//! Stablecoin example pallet
//!
//! This is a substrate pallet showcasing a simple implementation of a stablecoin based
//! on the [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf).
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;

use codec::{Decode, Encode};
use core::cmp::{max, min};
use frame_support::{
	debug::native,
	decl_error, decl_event, decl_module, decl_storage,
	dispatch::{DispatchError, DispatchResult},
	ensure,
	traits::Get,
};
use num_rational::Ratio;
use sp_runtime::{
	traits::{CheckedMul},
	Fixed64, PerThing, Perbill,
};
use sp_std::collections::vec_deque::VecDeque;
use sp_std::iter;
use static_assertions::const_assert;
use system::ensure_signed;

mod utils;

use utils::saturated_mul;

/// Trait for getting a price.
pub trait FetchPrice<Balance> {
	/// Fetch the current price.
	fn fetch_price() -> Balance;
}

/// The pallet's configuration trait.
pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The amount of coins necessary to buy the tracked value
	type CoinPrice: FetchPrice<Coins>;

	/// The expiration time of a bond
	type ExpirationPeriod: Get<<Self as system::Trait>::BlockNumber>;
	/// The maximum amount of bids allowed in the queue
	type MaximumBids: Get<usize>;
}

/// The type used to represent the account balance for the stablecoin.
pub type Coins = u64;

// 1000 units are supposed to represent $1 USD or whatever is being tracked.
const BASE_UNIT: Coins = 1000;
const COIN_SUPPLY: Coins = BASE_UNIT * 100;
const SHARE_SUPPLY: u64 = 100;

// The Basis whitepaper recommends 10% based on simulations.
const MINIMUM_BOND_PRICE: Perbill = Perbill::from_percent(10);
const MINIMUM_BOND_PAYOUT: i64 = 1;
const_assert!(MINIMUM_BOND_PAYOUT >= 1); // minimum bond amount should be at least 1

/// A bond representing (possible) future payout of coins.
/// 
/// Expires at block `expiration` so it will be discarded if payed out after that block.
#[derive(Encode, Decode, Default, Clone, PartialEq, PartialOrd, Eq, Ord)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Bond<AccountId, BlockNumber> {
	account: AccountId,
	payout: Coins,
	expiration: BlockNumber,
}

/// A bid for a bond of the stablecoin at a certain price.
/// 
/// `price_in_coins` is the amount of coins burned
/// `quantity` is the amount of coins gained on payout
#[derive(Encode, Decode, Default, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Bid<AccountId> {
	account: AccountId,
	price: Perbill,
	price_in_coins: Coins,
	quantity: Coins,
}

pub enum BidError {
	Overflow,
	Underflow,
}

impl<AccountId> Bid<AccountId> {
	fn new(account: AccountId, price: Perbill, quantity: Coins) -> Bid<AccountId> {
		// This is fine because Perbill has an implementation tuned for balance types.
		let price_in_coins = price * quantity;
		Bid {
			account,
			price,
			price_in_coins,
			quantity,
		}
	}

	/// Remove `coins` amount of coins from the bid, mirroring the changes in quantity
	/// according to the price attached to the bid.
	fn remove_coins(&mut self, coins: Coins) -> Result<Coins, BidError> {
		let inverse_price: Ratio<u64> = Ratio::new(Perbill::ACCURACY.into(), self.price.deconstruct().into());
		// Should never overflow, but better safe than sorry.
		let removed_quantity = inverse_price
			.checked_mul(&coins.into())
			.map(|r| r.to_integer())
			.ok_or(BidError::Overflow)?;
		self.price_in_coins = self
			.price_in_coins
			.checked_sub(coins)
			.ok_or(BidError::Underflow)?;
		self.quantity = self
			.quantity
			.checked_sub(removed_quantity)
			.ok_or(BidError::Underflow)?;
		Ok(removed_quantity)
	}
}

decl_event!(
	pub enum Event<T>
	where
		AccountId = <T as system::Trait>::AccountId,
		BlockNumber = <T as system::Trait>::BlockNumber,
	{
		Initialized(AccountId),
		Transfer(AccountId, AccountId, u64),
		NewBid(AccountId, Perbill, u64),
		RefundedBid(AccountId, u64),
		NewBond(AccountId, u64, BlockNumber),
		BondFulfilled(AccountId, u64),
		BondPartiallyFulfilled(AccountId, u64),
		BondExpired(AccountId, u64),
		CancelledBidsBelow(AccountId, Perbill),
		CancelledBids(AccountId),
		ExpandedSupply(u64),
		ContractedSupply(u64),
	}
);

decl_error! {
	pub enum Error for Module<T: Trait> {
		CoinOverflow,
		CoinUnderflow,
		InsufficientBalance,
		BalanceOverflow,
		ZeroPrice,
		GenericOverflow,
		GenericUnderflow,
		RoundingError,
	}
}

impl<T: Trait> From<BidError> for Error<T> {
	fn from(e: BidError) -> Self {
		match e {
			BidError::Overflow => Error::GenericOverflow,
			BidError::Underflow => Error::GenericUnderflow,
		}
	}
}

// This pallet's storage items.
decl_storage! {
	trait Store for Module<T: Trait> as Stablecoin {
		Init get(fn initialized): bool = false;

		ShareSupply get(fn share_supply): u64;
		Shares get(fn shares): Vec<(T::AccountId, u64)>;

		Balance get(fn get_balance): map hasher(blake2_256) T::AccountId => Coins;
		CoinSupply get(fn coin_supply): Coins;

		// TODO: limit the maximum bond size
		Bonds get(fn bonds): VecDeque<Bond<T::AccountId, T::BlockNumber>>;

		BondBids get(fn bond_bids): Vec<Bid<T::AccountId>>;
	}
}

// The pallet's dispatchable functions.
decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {

		fn deposit_event() = default;

		/// Initialize the stablecoin.
		///
		/// Sender of the transaction will be the founder.
		/// Initial coin supply will be allocated to the founder.
		pub fn init(origin) -> DispatchResult {
			let founder = ensure_signed(origin)?;

			ensure!(!Self::initialized(), "can only be initialized once");

			<Shares<T>>::put(vec![(founder.clone(), SHARE_SUPPLY)]);
			<ShareSupply>::put(SHARE_SUPPLY);

			<Balance<T>>::insert(&founder, COIN_SUPPLY);
			<CoinSupply>::put(COIN_SUPPLY);

			<Init>::put(true);

			Self::deposit_event(RawEvent::Initialized(founder));

			Ok(())
		}

		/// Initialize the coin with the given `shareholders`.
		///
		/// Sender of the transaction will be the founder.
		/// Initial coin supply will be distributed evenly to the shareholders.
		pub fn init_with_shareholders(origin, shareholders: Vec<T::AccountId>) -> DispatchResult {
			let founder = ensure_signed(origin)?;

			ensure!(!Self::initialized(), "can only be initialized once");

			let len = shareholders.len();
			// give one share to each shareholder
			let shares: Vec<(T::AccountId, u64)> = shareholders.into_iter().zip(iter::repeat(1).take(len)).collect();
			<Shares<T>>::put(shares);
			<ShareSupply>::put(len as u64);

			Self::hand_out_coins_to_shareholders(COIN_SUPPLY)?;

			<Init>::put(true);

			Self::deposit_event(RawEvent::Initialized(founder));

			Ok(())
		}

		/// Transfer `amount` coins from the sender to the account `to`.
		pub fn transfer(origin, to: T::AccountId, amount: u64) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let sender_balance = Self::get_balance(&sender);
			let updated_from_balance = sender_balance.checked_sub(amount).ok_or("not enough balance to transfer (underflow)")?;
			let receiver_balance = Self::get_balance(&to);
			let updated_to_balance = receiver_balance.checked_add(amount).ok_or("overflow for transfer target")?;

			// reduce sender's balance
			<Balance<T>>::insert(&sender, updated_from_balance);
			// increase receiver's balance
			<Balance<T>>::insert(&to, updated_to_balance);

			Self::deposit_event(RawEvent::Transfer(sender, to, amount));

			Ok(())
		}

		/// Bid for `amount * BASE_UNIT` coins at a price of `price`.
		///
		/// Example: `bid_for_bond(Perbill::from_percent(80), Fixed64::from_rational(125, 100))` will bid
		/// for a bond with a payout of `1.25 * BASE_UNIT` coins for a price of `1 * BASE_UNIT` coins.
		pub fn bid_for_bond(origin, price: Perbill, payout: Fixed64) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(price <= Perbill::from_percent(100), "price cannot be higher than 100%");
			ensure!(price > MINIMUM_BOND_PRICE, "offered price is lower than the minimum");
			ensure!(payout >= Fixed64::from_natural(MINIMUM_BOND_PAYOUT), "payout is lower than the minimum");

			let quantity = saturated_mul(payout, BASE_UNIT);

			// this is fine because `Perbill` is designed to be used with balance types and `price` is ensured
			// to be between `MINIMUM_BOND_PRICE` and 1
			let price_in_coins = price * quantity;
			Self::remove_balance(&who, price_in_coins)?;
			Self::add_bid(Bid::new(who.clone(), price, quantity))?;

			Self::deposit_event(RawEvent::NewBid(who, price, quantity));

			Ok(())
		}

		/// Cancel all bids at or below `price` of the sender.
		pub fn cancel_bids_at_or_below(origin, price: Perbill) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::cancel_bids(|bid| bid.account == who && bid.price <= price);

			Self::deposit_event(RawEvent::CancelledBidsBelow(who, price));

			Ok(())
		}

		/// Cancel all bids belonging to the sender.
		pub fn cancel_all_bids(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::cancel_bids(|bid| bid.account == who);

			Self::deposit_event(RawEvent::CancelledBids(who));

			Ok(())
		}

		/// Adjusts the amount of coins according to the price.
		fn on_initialize(_n: T::BlockNumber) {
			Self::_on_block().unwrap_or_else(|e| {
				native::error!("could not adjust supply: {:?}", e);
			});
		}
	}
}

impl<T: Trait> Module<T> {
	/// Add `amount` coins to the balance for `account`.
	fn add_balance(account: &T::AccountId, amount: Coins) -> DispatchResult {
		<Balance<T>>::try_mutate(account, |b: &mut u64| -> DispatchResult{
			*b = b.checked_add(amount).ok_or(Error::<T>::BalanceOverflow)?;
			Ok(())
		})?;
		Ok(())
	}

	/// Remove `amount` coins from the balance of `account`.
	fn remove_balance(account: &T::AccountId, amount: Coins) -> DispatchResult {
		<Balance<T>>::try_mutate(&account, |b: &mut u64| -> DispatchResult{
			*b = b.checked_sub(amount).ok_or(Error::<T>::InsufficientBalance)?;
			Ok(())
		})?;
		Ok(())
	}


	fn add_bid(bid: Bid<T::AccountId>) -> DispatchResult {
		let mut bids = Self::bond_bids();

		Self::_add_bid_to(bid, &mut bids)?;

		<BondBids<T>>::put(bids);
		Ok(())
	}

	/// Add a bid to the queue, making sure to sort it from highest to lowest price.
	///
	/// Truncates the bids to `MaximumBids` to keep the queue bounded.
	fn _add_bid_to(bid: Bid<T::AccountId>, bids: &mut Vec<Bid<T::AccountId>>) -> DispatchResult {
		let index: usize = bids
			// sort the bids from highest to lowest
			.binary_search_by(|&Bid { price, .. }| bid.price.cmp(&price))
			.unwrap_or_else(|i| i);
		bids.insert(index, bid);
		while bids.len() > T::MaximumBids::get() {
			if let Some(bid) = bids.pop() {
				Self::refund_bid(&bid)?;
			}
		}
		Ok(())
	}

	fn refund_bid(Bid {account, price_in_coins, ..}: &Bid<T::AccountId>) -> DispatchResult {
		Self::add_balance(account, *price_in_coins)?;
		Self::deposit_event(RawEvent::RefundedBid(account.clone(), *price_in_coins));
		Ok(())
	}

	fn cancel_bids<F>(cancel_for: F)
	where
		F: Fn(&Bid<T::AccountId>) -> bool,
	{
		let mut bids = Self::bond_bids();

		bids.retain(|b| {
			if cancel_for(b) {
				Self::refund_bid(b).unwrap_or_else(|e|{
					native::error!("{:?}", e);
					debug_assert!(false, "refund should not fail");
				});
				return false;
			}
			true
		});

		<BondBids<T>>::put(bids);
	}

	/// Expands (if the price is too high) or contracts (if the price is too low)
	/// the coin supply.
	fn expand_or_contract_on_price(price: Coins) -> DispatchResult {
		match price {
			0 => {
				native::error!("coin price is zero!");
				return Err(DispatchError::from(Error::<T>::ZeroPrice));
			},
			price if price > BASE_UNIT => {
				// safe from underflow because `price` is checked to be greater than `BASE_UNIT`
				let fraction = Fixed64::from_rational(price as i64, BASE_UNIT) - Fixed64::from_natural(1);
				let supply = Self::coin_supply();
				let contract_by = saturated_mul(fraction, supply);
				Self::contract_supply(contract_by)?;
			},
			price if price < BASE_UNIT => {
				// safe from underflow because `price` is checked to be less than `BASE_UNIT`
				let fraction = Fixed64::from_rational(BASE_UNIT as i64, price) - Fixed64::from_natural(1);
				let supply = Self::coin_supply();
				let expand_by = saturated_mul(fraction, supply);
				Self::expand_supply(expand_by)?;
			},
			_ => {
				native::info!("coin price is equal to base as is desired --> nothing to do");
			}
		}
		Ok(())
	}

	fn test_decrease_coin_supply(amount: Coins) -> DispatchResult {
		let coin_supply = Self::coin_supply();
		let remaining_supply = coin_supply.checked_sub(amount).ok_or(Error::<T>::CoinUnderflow)?;
		if remaining_supply < 1 {
			return Err(DispatchError::from(Error::<T>::CoinOverflow));
		}
		Ok(())
	}

	fn contract_supply(amount: Coins) -> DispatchResult {
		Self::test_decrease_coin_supply(amount)?;
		let mut bids = Self::bond_bids();
		let mut remaining = amount;
		let mut new_bonds = VecDeque::new();
		while remaining > 0 && !bids.is_empty() {
			let mut bid = bids.remove(0);
			if bid.price_in_coins >= remaining {
				let removed_quantity = bid.remove_coins(remaining).map_err(Error::<T>::from)?;
				new_bonds.push_back(Self::new_bond(bid.account.clone(), removed_quantity));
				// re-add bid with reduced amount
				if bid.price_in_coins > 0 && bid.quantity > 0 {
					// TODO: do we really want to return early on error here?
					Self::_add_bid_to(bid, &mut bids)?;
				} else if bid.price_in_coins != bid.quantity {
					// if one of them is zero, both should be
					return Err(DispatchError::from(Error::<T>::RoundingError));
				}
				remaining -= remaining;
			} else {
				let Bid {
					account,
					price_in_coins,
					quantity,
					..
				} = bid;
				new_bonds.push_back(Self::new_bond(account, quantity));
				remaining -= price_in_coins;
			}
		}
		let burned = amount
			.checked_sub(remaining)
			.ok_or(Error::<T>::GenericUnderflow)?;
		let new_supply = <CoinSupply>::get()
			.checked_sub(burned)
			.ok_or(Error::<T>::CoinUnderflow)?;
		for bond in new_bonds.iter() {
			Self::deposit_event(RawEvent::NewBond(bond.account.clone(), bond.payout, bond.expiration));
		}
		let mut bonds = Self::bonds();
		bonds.append(&mut new_bonds);
		<Bonds<T>>::put(bonds);
		<CoinSupply>::put(new_supply);
		<BondBids<T>>::put(bids);
		Self::deposit_event(RawEvent::ContractedSupply(burned));
		Ok(())
	}

	fn new_bond(account: T::AccountId, payout: Coins) -> Bond<T::AccountId, T::BlockNumber> {
		let expiration = <system::Module<T>>::block_number() + T::ExpirationPeriod::get();
		Bond {
			account,
			payout,
			expiration,
		}
	}

	fn _add_bond(bond: Bond<T::AccountId, T::BlockNumber>) {
		let mut bonds = Self::bonds();
		bonds.push_back(bond);
		<Bonds<T>>::put(bonds);
	}

	fn expand_supply(amount: Coins) -> DispatchResult {
		Self::test_increase_coin_supply(amount)?;
		let mut bonds = Self::bonds();
		let mut remaining = amount;
		while let Some(Bond {
			account,
			payout,
			expiration,
		}) = bonds.pop_front()
		{
			if remaining == 0 {
				break;
			}
			// bond has expired --> discard
			if <system::Module<T>>::block_number() >= expiration {
				Self::deposit_event(RawEvent::BondExpired(account, payout));
				continue;
			}
			// bond does not cover the remaining amount --> resolve and continue
			if payout <= remaining {
				remaining = remaining
					.checked_sub(payout)
					.ok_or(Error::<T>::GenericUnderflow)?;
				Self::add_balance(&account, payout)?;
				Self::deposit_event(RawEvent::BondFulfilled(account, payout));
			}
			// bond covers the remaining amount --> update and finish up
			else {
				let payout = payout
					.checked_sub(remaining)
					.ok_or(Error::<T>::GenericUnderflow)?;
				Self::add_balance(&account, remaining)?;
				Self::_add_bond(Bond {
					account: account.clone(),
					payout,
					expiration,
				});
				Self::deposit_event(RawEvent::BondPartiallyFulfilled(account, payout));
				break;
			}
		}
		// safe to do this late because of the test in the first line of the function
		Self::try_increase_coin_supply(amount - remaining)?;
		<Bonds<T>>::put(bonds);
		if remaining > 0 {
			Self::hand_out_coins_to_shareholders(remaining)?;
		}
		Self::deposit_event(RawEvent::ExpandedSupply(amount));
		Ok(())
	}

	fn test_increase_coin_supply(amount: Coins) -> DispatchResult {
		let coin_supply = Self::coin_supply();
		coin_supply.checked_add(amount).ok_or(Error::<T>::CoinOverflow)?;
		Ok(())
	}

	fn try_increase_coin_supply(amount: Coins) -> DispatchResult {
		let mut coin_supply = Self::coin_supply();
		coin_supply = coin_supply.checked_add(amount).ok_or(Error::<T>::CoinOverflow)?;
		<CoinSupply>::put(coin_supply);
		Ok(())
	}

	// will hand out coins to shareholders according to their number of shares
	// will hand out more coins to shareholders at the beginning of the list
	// if the handout cannot be equal
	fn hand_out_coins_to_shareholders(amount: Coins) -> DispatchResult {
		let supply = Self::share_supply();
		let shares = Self::shares();
		let len = shares.len() as u64;
		let coins_per_share = max(1, amount / supply);
		let pay_extra = coins_per_share * len < amount;
		let mut amount_payed = 0;
		Self::try_increase_coin_supply(amount)?;
		for (i, (acc, num_shares)) in shares.into_iter().enumerate() {
			if amount_payed >= amount {
				break;
			}
			let max_payout = amount - amount_payed;
			let is_in_first_mod_len = (i as u64) < amount % len;
			let extra_payout = if pay_extra && is_in_first_mod_len { 1 } else { 0 };
			let payout = min(max_payout, num_shares * coins_per_share + extra_payout);
			debug_assert!(
				amount_payed + payout <= amount,
				"amount payed out should be less or equal target amount"
			);
			let balance = Self::get_balance(&acc);
			<Balance<T>>::insert(&acc, balance + payout);
			amount_payed += payout;
		}
		debug_assert!(
			amount_payed == amount,
			"amount payed out should equal target amount"
		);
		Ok(())
	}

	fn _on_block() -> DispatchResult {
		let price = T::CoinPrice::fetch_price();
		Self::expand_or_contract_on_price(price)
	}
}

/// tests for this pallet
#[cfg(test)]
mod tests {
	use super::*;
	use itertools::Itertools;
	use log;
	use more_asserts::*;
	use quickcheck::{QuickCheck, TestResult};
	use rand::{thread_rng, Rng};
	use std::sync::atomic::{AtomicU64, Ordering};

	use frame_support::{assert_ok, impl_outer_origin, parameter_types, weights::Weight};
	use sp_core::H256;
	use sp_runtime::{
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup},
		Perbill,
	};
	use system;

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	static LAST_PRICE: AtomicU64 = AtomicU64::new(BASE_UNIT);
	pub struct RandomPrice;

	impl FetchPrice<Coins> for RandomPrice {
		fn fetch_price() -> Coins {
			let prev = LAST_PRICE.load(Ordering::SeqCst);
			let random = thread_rng().gen_range(500, 1500);
			let ratio: Ratio<u64> = Ratio::new(random, 1000);
			let next = ratio
				.checked_mul(&prev.into())
				.map(|r| r.to_integer())
				.unwrap_or(prev);
			LAST_PRICE.store(next + 1, Ordering::SeqCst);
			prev
		}
	}

	// For testing the pallet, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);

		// expire bonds quickly in tests
		pub const ExpirationPeriod: u64 = 100;
		// allow few bids
		pub const MaximumBids: usize = 10;
	}

	impl system::Trait for Test {
		type Origin = Origin;
		type Call = ();
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}

	impl Trait for Test {
		type Event = ();
		type ExpirationPeriod = ExpirationPeriod;
		type MaximumBids = MaximumBids;
		type CoinPrice = RandomPrice;
	}

	type System = system::Module<Test>;
	type Stablecoin = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
		system::GenesisConfig::default()
			.build_storage::<Test>()
			.unwrap()
			.into()
	}

	// ------------------------------------------------------------
	// init tests

	#[test]
	fn init_and_transfer() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));

			let amount = 42;
			assert_ok!(Stablecoin::transfer(Origin::signed(1), 2, amount));

			assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY - amount);
			assert_eq!(Stablecoin::get_balance(2), amount);
		});
	}

	#[test]
	fn init_with_shareholders_test() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init_with_shareholders(
				Origin::signed(1),
				vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
			));

			assert_eq!(
				Stablecoin::shares(),
				vec![
					(1, 1),
					(2, 1),
					(3, 1),
					(4, 1),
					(5, 1),
					(6, 1),
					(7, 1),
					(8, 1),
					(9, 1),
					(10, 1)
				]
			);
			assert_eq!(Stablecoin::share_supply(), 10);
		});
	}

	// ------------------------------------------------------------
	// bids and bonds
	#[test]
	fn bids_are_sorted_highest_to_lowest() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));

			assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), 5 * BASE_UNIT)));
			assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(33), 5 * BASE_UNIT)));
			assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(50), 5 * BASE_UNIT)));

			let bids = Stablecoin::bond_bids();
			let prices: Vec<_> = bids.into_iter().map(|Bid { price, .. }| price).collect();
			assert_eq!(
				prices,
				vec![
					Perbill::from_percent(50),
					Perbill::from_percent(33),
					Perbill::from_percent(25)
				]
			);
		});
	}

	#[test]
	fn amount_of_bids_is_limited() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));

			for _i in 0..(2 * MaximumBids::get()) {
				assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), 5 * BASE_UNIT)));
			}

			assert_eq!(Stablecoin::bond_bids().len(), MaximumBids::get());
		});
	}

	#[test]
	fn truncated_bids_are_refunded() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));

			let price = Perbill::from_percent(25);
			let payout = Fixed64::from_natural(MINIMUM_BOND_PAYOUT);
			for _i in 0..(MaximumBids::get() + 1) {
				assert_ok!(Stablecoin::bid_for_bond(Origin::signed(1), price, payout));
			}

			assert_eq!(Stablecoin::bond_bids().len(), MaximumBids::get());
			let expected = COIN_SUPPLY - price * saturated_mul(payout, BASE_UNIT) * (MaximumBids::get() as u64);
			assert_eq!(Stablecoin::get_balance(1), expected);
		});
	}

	#[test]
	fn cancel_all_bids_test() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));

			assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), 5 * BASE_UNIT)));
			assert_ok!(Stablecoin::add_bid(Bid::new(2, Perbill::from_percent(33), 5 * BASE_UNIT)));
			assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(50), 5 * BASE_UNIT)));
			assert_ok!(Stablecoin::add_bid(Bid::new(3, Perbill::from_percent(50), 5 * BASE_UNIT)));
			assert_eq!(Stablecoin::bond_bids().len(), 4);

			assert_ok!(Stablecoin::cancel_all_bids(Origin::signed(1)));

			let bids = Stablecoin::bond_bids();
			assert_eq!(bids.len(), 2);
			for bid in bids {
				assert!(bid.account != 1);
			}
		});
	}

	#[test]
	fn cancel_selected_bids_test() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));

			assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), 5 * BASE_UNIT)));
			assert_ok!(Stablecoin::add_bid(Bid::new(2, Perbill::from_percent(33), 5 * BASE_UNIT)));
			assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(45), 5 * BASE_UNIT)));
			assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(50), 5 * BASE_UNIT)));
			assert_ok!(Stablecoin::add_bid(Bid::new(3, Perbill::from_percent(55), 5 * BASE_UNIT)));
			assert_eq!(Stablecoin::bond_bids().len(), 5);

			assert_ok!(Stablecoin::cancel_bids_at_or_below(
				Origin::signed(1),
				Perbill::from_percent(45)
			));

			let bids = Stablecoin::bond_bids();
			assert_eq!(bids.len(), 3);
			let bids: Vec<(_, _)> = bids
				.into_iter()
				.map(|Bid { account, price, .. }| (account, price))
				.collect();
			assert_eq!(
				bids,
				vec![
					(3, Perbill::from_percent(55)),
					(1, Perbill::from_percent(50)),
					(2, Perbill::from_percent(33)),
				]
			);
		});
	}

	#[test]
	fn adding_bonds() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));

			Stablecoin::_add_bond(Stablecoin::new_bond(
				3,
				Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BASE_UNIT),
			));

			let bonds = Stablecoin::bonds();
			assert_eq!(bonds.len(), 1);
			let bond = &bonds[0];
			assert_eq!(bond.expiration, ExpirationPeriod::get() + 1);
		})
	}

	#[test]
	fn expire_bonds() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));
			Stablecoin::_add_bond(Stablecoin::new_bond(
				3,
				Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BASE_UNIT),
			));

			let bonds = Stablecoin::bonds();
			assert_eq!(bonds.len(), 1);
			let bond = &bonds[0];
			assert_eq!(bond.expiration, 101);

			let prev_supply = Stablecoin::coin_supply();
			// set blocknumber past expiration time
			System::set_block_number(ExpirationPeriod::get() + 20);
			assert_ok!(Stablecoin::contract_supply(42));
			assert_eq!(
				prev_supply,
				Stablecoin::coin_supply(),
				"coin supply should not change as the bond expired"
			);
		});
	}

	// ------------------------------------------------------------
	// handout tests

	#[test]
	fn simple_handout_test() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init_with_shareholders(
				Origin::signed(1),
				vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
			));
			assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY / 10);
			assert_eq!(Stablecoin::get_balance(10), COIN_SUPPLY / 10);

			let amount = 30 * BASE_UNIT;
			assert_ok!(Stablecoin::hand_out_coins_to_shareholders(amount));

			let amount_per_acc = 3 * BASE_UNIT;
			assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(2), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(3), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(7), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(10), COIN_SUPPLY / 10 + amount_per_acc);
		});
	}

	#[test]
	fn handout_less_than_shares_test() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init_with_shareholders(
				Origin::signed(1),
				vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
			));
			assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY / 10);
			assert_eq!(Stablecoin::get_balance(10), COIN_SUPPLY / 10);

			let amount = 8;
			assert_ok!(Stablecoin::hand_out_coins_to_shareholders(amount));

			let amount_per_acc = 1;
			assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(2), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(3), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(7), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(8), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(9), COIN_SUPPLY / 10);
			assert_eq!(Stablecoin::get_balance(10), COIN_SUPPLY / 10);
		});
	}

	#[test]
	fn handout_more_than_shares_test() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init_with_shareholders(
				Origin::signed(1),
				vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
			));
			assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY / 10);
			assert_eq!(Stablecoin::get_balance(10), COIN_SUPPLY / 10);

			let amount = 13;
			assert_ok!(Stablecoin::hand_out_coins_to_shareholders(amount));

			let amount_per_acc = 1;
			assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY / 10 + amount_per_acc + 1);
			assert_eq!(Stablecoin::get_balance(2), COIN_SUPPLY / 10 + amount_per_acc + 1);
			assert_eq!(Stablecoin::get_balance(3), COIN_SUPPLY / 10 + amount_per_acc + 1);
			assert_eq!(Stablecoin::get_balance(4), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(8), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(10), COIN_SUPPLY / 10 + amount_per_acc);
		});
	}

	#[test]
	fn handout_quickcheck() {
		fn property(shareholders: Vec<u64>, amount: Coins) -> TestResult {
			new_test_ext().execute_with(|| {
				if amount == 0 {
					return TestResult::discard();
				}

				// Expect less than 1000 shareholders
				let len = shareholders.len();
				if len < 1 || len > 999 {
					return TestResult::discard();
				}

				if shareholders.iter().any(|s| *s == 0) {
					return TestResult::discard();
				}

				if shareholders.iter().unique().count() != len {
					return TestResult::discard();
				}

				assert_ok!(Stablecoin::init_with_shareholders(
					Origin::signed(1),
					shareholders.clone()
				));

				let amount = amount;
				// this assert might actually produce a false positive
				// as there might be errors returned that are the correct
				// behavior for the given parameters
				assert_ok!(Stablecoin::hand_out_coins_to_shareholders(amount));

				let len = len as u64;
				let payout = amount;
				let balance = Stablecoin::get_balance(shareholders[0]);
				assert_ge!(balance, COIN_SUPPLY / len + payout / len);
				assert_le!(balance, COIN_SUPPLY / len + 1 + payout / len + 1);

				TestResult::passed()
			})
		}

		QuickCheck::new()
			.min_tests_passed(5)
			.tests(50)
			.max_tests(500)
			.quickcheck(property as fn(Vec<u64>, u64) -> TestResult)
	}

	// ------------------------------------------------------------
	// expand and contract tests
	#[test]
	fn expand_supply_test() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init_with_shareholders(
				Origin::signed(1),
				vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
			));

			// payout of 120% of BASE_UNIT
			let payout = Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BASE_UNIT);
			Stablecoin::_add_bond(Stablecoin::new_bond(2, payout));
			Stablecoin::_add_bond(Stablecoin::new_bond(3, payout));
			Stablecoin::_add_bond(Stablecoin::new_bond(4, payout));
			Stablecoin::_add_bond(Stablecoin::new_bond(5, 7 * payout));

			let prev_supply = Stablecoin::coin_supply();
			let amount = 13 * BASE_UNIT;
			assert_ok!(Stablecoin::expand_supply(amount));

			let amount_per_acc = COIN_SUPPLY / 10 + BASE_UNIT / 10;
			assert_eq!(Stablecoin::get_balance(1), amount_per_acc);
			assert_eq!(Stablecoin::get_balance(2), amount_per_acc + payout);
			assert_eq!(Stablecoin::get_balance(3), amount_per_acc + payout);
			assert_eq!(Stablecoin::get_balance(4), amount_per_acc + payout);
			assert_eq!(Stablecoin::get_balance(5), amount_per_acc + 7 * payout);
			assert_eq!(Stablecoin::get_balance(8), amount_per_acc);
			assert_eq!(Stablecoin::get_balance(10), amount_per_acc);

			assert_eq!(
				Stablecoin::coin_supply(),
				prev_supply + amount,
				"supply should be increased by amount"
			);
		});
	}

	#[test]
	fn contract_supply_test() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init_with_shareholders(
				Origin::signed(1),
				vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
			));

			let bond_amount = Ratio::new(125, 100)
				.checked_mul(&BASE_UNIT.into())
				.map(|r| r.to_integer())
				.unwrap();
			assert_ok!(Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(80), bond_amount)));
			assert_ok!(Stablecoin::add_bid(Bid::new(2, Perbill::from_percent(75), 2 * BASE_UNIT)));

			let prev_supply = Stablecoin::coin_supply();
			let amount = 2 * BASE_UNIT;
			assert_ok!(Stablecoin::contract_supply(amount));

			let bids = Stablecoin::bond_bids();
			let bonds = Stablecoin::bonds();
			assert_eq!(bids.len(), 1, "exactly one bid should have been removed");
			let remainging_bid_quantity = saturated_mul(Fixed64::from_rational(667, 1_000), BASE_UNIT);
			assert_eq!(
				bids[0],
				Bid::new(2, Perbill::from_percent(75), remainging_bid_quantity)
			);
			assert_eq!(bonds[0].payout, bond_amount);
			assert_eq!(
				bonds[1].payout,
				Fixed64::from_rational(333, 1_000).saturated_multiply_accumulate(BASE_UNIT)
			);

			assert_eq!(
				Stablecoin::coin_supply(),
				prev_supply - amount,
				"supply should be decreased by amount"
			);
		})
	}

	#[test]
	fn expand_or_contract_quickcheck() {
		fn property(bonds: Vec<(u64, u64)>, prices: Vec<Coins>) -> TestResult {
			new_test_ext().execute_with(|| {
				if prices.iter().any(|p| p == &0) {
					return TestResult::discard();
				}

				assert_ok!(Stablecoin::init_with_shareholders(
					Origin::signed(1),
					vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
				));

				for (account, payout) in bonds {
					if account > 0 && payout > 0 {
						Stablecoin::_add_bond(Stablecoin::new_bond(account, payout));
					}
				}

				for price in prices {
					// this assert might actually produce a false positive
					// as there might be errors returned that are the correct
					// behavior for the given parameters
					assert_ok!(Stablecoin::expand_or_contract_on_price(price));
				}

				TestResult::passed()
			})
		}

		QuickCheck::new()
			.min_tests_passed(5)
			.tests(50)
			.max_tests(500)
			.quickcheck(property as fn(Vec<(u64, u64)>, Vec<u64>) -> TestResult)
	}

	#[test]
	fn expand_or_contract_smoketest() {
		new_test_ext().execute_with(|| {
			let mut rng = rand::thread_rng();

			let bonds: Vec<(u64, u64)> = (0..100)
				.map(|_| (rng.gen_range(1, 200), rng.gen_range(1, 10 * BASE_UNIT)))
				.collect();

			assert_ok!(Stablecoin::init_with_shareholders(
				Origin::signed(1),
				vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
			));

			for (account, payout) in bonds {
				Stablecoin::_add_bond(Stablecoin::new_bond(account, payout));
			}

			for _ in 0..150 {
				Stablecoin::_on_block().unwrap_or_else(|e| {
					log::error!("could not adjust supply: {:?}", e);
				});
			}
		})
	}
}
