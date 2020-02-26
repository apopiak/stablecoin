#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;

use codec::{Decode, Encode};
use core::cmp::{max, min};
use frame_support::{
	debug::native,
	decl_error, decl_event, decl_module, decl_storage,
	dispatch::{DispatchError, DispatchResult},
	ensure,
	traits::{Currency, Get},
};
use num_rational::Ratio;
use sp_runtime::{traits::CheckedMul, Fixed64, PerThing, Perbill};
use sp_std::collections::vec_deque::VecDeque;
use sp_std::iter;
use system::ensure_signed;

/// Trait for getting a price.
pub trait FetchPrice<Balance> {
	/// Fetch the price.
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

pub type Coins = u64;

const BASE_UNIT: Coins = 1000; // 1000 units are supposed to represent $1 USD
const COIN_SUPPLY: Coins = BASE_UNIT * 100;
const SHARE_SUPPLY: u64 = 100;

const MINIMUM_BOND_PRICE: Perbill = Perbill::from_percent(10);
const MINIMUM_BOND_AMOUNT: i64 = 1;

#[derive(Encode, Decode, Default, Clone, PartialEq, PartialOrd, Eq, Ord)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Bond<AccountId, BlockNumber> {
	account: AccountId,
	payout: Coins,
	expiration: BlockNumber,
}

#[derive(Encode, Decode, Default, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Bid<AccountId> {
	account: AccountId,
	price: Perbill,
	price_in_coins: Coins,
	quantity: Coins,
}

impl<AccountId> Bid<AccountId> {
	fn new(account: AccountId, price: Perbill, quantity: Coins) -> Bid<AccountId> {
		let price_in_coins = price * quantity;
		Bid {
			account,
			price,
			price_in_coins,
			quantity,
		}
	}
}

#[derive(Encode, Decode, Default, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct CustomRatio<T>(T, T);

impl<T: Copy> From<Ratio<T>> for CustomRatio<T> {
	fn from(r: Ratio<T>) -> CustomRatio<T> {
		CustomRatio(*r.numer(), *r.denom())
	}
}

impl<T: Copy> Into<Ratio<T>> for CustomRatio<T> {
	fn into(self: CustomRatio<T>) -> Ratio<T> {
		Ratio::new_raw(self.0, self.1)
	}
}

decl_event!(
	pub enum Event<T>
	where
		AccountId = <T as system::Trait>::AccountId,
	{
		Initialized(AccountId),
		Transfer(AccountId, AccountId, u64),
		BondReleased(AccountId, u64),
	}
);

decl_error! {
	pub enum Error for Module<T: Trait> {
		InsufficientBalance,
		CoinOverflow,
		CoinUnderflow,
	}
}

// This pallet's storage items.bonds
decl_storage! {
	trait Store for Module<T: Trait> as Stablecoin {
		Init get(fn initialized): bool = false;

		ShareSupply get(fn share_supply): u64;
		Shares get(fn shares): Vec<(T::AccountId, u64)>;

		Balance get(fn get_balance): map hasher(blake2_256) T::AccountId => Coins;
		CoinSupply get(fn coin_supply): Coins;

		// TODO: limit the maximum bond size
		Bonds get(fn bonds): VecDeque<Bond<T::AccountId, T::BlockNumber>>;

		// TODO: how to implement continuous auction/priority queue
		BondBids get(fn bond_bids): Vec<Bid<T::AccountId>>;

		ExchangeRate get(fn exchange_rate): CustomRatio<u64>;
	}
}

// The pallet's dispatchable functions.
decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		// Initializing events
		// this is needed only if you are using events in your pallet
		fn deposit_event() = default;

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

		pub fn init_with_shareholders(origin, shareholders: Vec<T::AccountId>) -> DispatchResult {
			let founder = ensure_signed(origin)?;

			ensure!(!Self::initialized(), "can only be initialized once");

			let len = shareholders.len();
			let shares: Vec<(T::AccountId, u64)> = shareholders.into_iter().zip(iter::repeat(1).take(len)).collect();
			<Shares<T>>::put(shares);
			<ShareSupply>::put(len as u64);

			Self::hand_out_coins_to_shareholders(COIN_SUPPLY);

			<Init>::put(true);

			Self::deposit_event(RawEvent::Initialized(founder));

			Ok(())
		}

		pub fn transfer(origin, to: T::AccountId, amount: u64) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let sender_balance = Self::get_balance(&sender);
			ensure!(sender_balance >= amount, "Not enough balance.");

			let updated_from_balance = sender_balance.checked_sub(amount).ok_or("overflow in calculating balance")?;
			let receiver_balance = Self::get_balance(&to);
			let updated_to_balance = receiver_balance.checked_add(amount).ok_or("overflow in calculating balance")?;

			// reduce sender's balance
			<Balance<T>>::insert(&sender, updated_from_balance);
			// increase receiver's balance
			<Balance<T>>::insert(&to, updated_to_balance);

			Self::deposit_event(RawEvent::Transfer(sender, to, amount));

			Ok(())
		}

		pub fn bid_for_bond(origin, price: Perbill, amount: Fixed64) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(price > MINIMUM_BOND_PRICE, "offered price is lower than the minimum");
			ensure!(amount >= Fixed64::from_natural(MINIMUM_BOND_AMOUNT), "amount is lower than the minimum");

			// amount > 1 and we want to calculate the amount of coins
			// saturated_multiply_accumulate = int + self * int
			// --> subtract 1 from amount
			let amount = amount - Fixed64::from_natural(1);
			let quantity = amount.saturated_multiply_accumulate(BASE_UNIT);
			let price_in_coins = price * quantity;
			<Balance<T>>::try_mutate(&who, |b| -> DispatchResult { b.checked_sub(price_in_coins).ok_or(Error::<T>::InsufficientBalance)?; Ok(()) })?;
			Self::add_bid(Bid::new(who, price, quantity));

			Ok(())
		}

		// TODO: implement cancelling bids

		// TODO: actually implement or replace/remove
		pub fn update_exchange_rate(origin, c_ratio: CustomRatio<u64>) -> DispatchResult {
			let _who = ensure_signed(origin)?;

			let mut ratio: Ratio<u64> = c_ratio.into();
			ratio += Ratio::new(4, 5);
			let custom_ratio: CustomRatio<u64> = ratio.into();
			<ExchangeRate>::put(custom_ratio);

			Ok(())
		}

		fn on_initialize(_n: T::BlockNumber) {
			let price = T::CoinPrice::fetch_price();
			Self::expand_or_contract_on_price(price);
		}
	}
}

impl<T: Trait> Module<T> {
	fn add_bid(bid: Bid<T::AccountId>) {
		let mut bids = Self::bond_bids();

		Self::_add_bid_to(bid, &mut bids);

		<BondBids<T>>::put(bids);
	}

	fn _add_bid_to(bid: Bid<T::AccountId>, bids: &mut Vec<Bid<T::AccountId>>) {
		let index: usize = bids
			// sort the bids from greatest to lowest
			.binary_search_by(|&Bid { price, .. }| bid.price.cmp(&price))
			.unwrap_or_else(|i| i);
		bids.insert(index, bid);
		bids.truncate(T::MaximumBids::get());
	}

	fn expand_or_contract_on_price(price: Coins) {
		if price == 0 {
			native::error!("coin price is zero!");
			return;
		}
		if price > BASE_UNIT {
			let ratio = Ratio::new(price, BASE_UNIT);
			let supply = Self::coin_supply();
			let contract_by = (ratio * supply - supply).to_integer();
			Self::contract_supply(contract_by).unwrap_or_else(|e| {
				native::error!("could not expand supply: {:?}", e);
			});
		} else if price < BASE_UNIT {
			let ratio = Ratio::new(BASE_UNIT, price);
			let supply = Self::coin_supply();
			let expand_by = (ratio * supply - supply).to_integer();
			Self::expand_supply(expand_by).unwrap_or_else(|e| {
				native::error!("could not expand supply: {:?}", e);
			});
		} else {
			native::info!("coin price is equal to base as it should be");
		}
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
		let mut bids = Self::bond_bids();
		Self::test_decrease_coin_supply(amount)?;
		let mut remaining = amount;
		while remaining > 0 && bids.len() > 0 {
			let mut bid = bids.remove(0);
			if bid.quantity >= remaining {
				Self::add_bond(bid.account.clone(), remaining);
				bid.quantity -= remaining;
				bid.price_in_coins -= bid.price * remaining;
				// re-add bid with reduced amount
				if bid.quantity > 0 {
					Self::_add_bid_to(bid, &mut bids);
				}
				remaining -= remaining;
			} else {
				let Bid {
					account, quantity, ..
				} = bid;
				Self::add_bond(account, quantity);
				remaining -= quantity;
			}
		}
		Ok(())
	}

	fn add_bond(account: T::AccountId, payout: Coins) {
		let expiration = <system::Module<T>>::block_number() + T::ExpirationPeriod::get();
		let bond = Bond {
			account,
			payout,
			expiration,
		};

		let mut bonds = Self::bonds();
		bonds.push_back(bond);
		<Bonds<T>>::put(bonds);
	}

	fn expand_supply(amount: Coins) -> DispatchResult {
		let mut bonds = Self::bonds();
		Self::test_increase_coin_supply(amount)?;
		let mut remaining = amount;
		while remaining > 0 && bonds.len() > 0 {
			// bond has expired --> discard
			if let Some(Bond { expiration, .. }) = bonds.front() {
				if <system::Module<T>>::block_number() >= *expiration {
					bonds.pop_front();
					continue;
				}
			}
			// bond covers the remaining amount --> update and finish up
			if let Some(bond) = bonds.front_mut() {
				if bond.payout > remaining {
					bond.payout -= remaining;
					<Balance<T>>::mutate(&bond.account, |b| *b += remaining);
					remaining = 0;
				}
			// bond does not cover the remaining amount --> resolve and continue
			} else if let Some(bond) = bonds.pop_front() {
				assert!(
					bond.payout <= remaining,
					"payout should be less than the remaining amount"
				);
				<Balance<T>>::mutate(&bond.account, |b| *b += bond.payout);
				remaining -= bond.payout;
			}
		}
		Self::try_increase_coin_supply(amount - remaining)?;
		<Bonds<T>>::put(bonds);
		if remaining > 0 {
			Self::hand_out_coins_to_shareholders(remaining)?;
		}
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
			assert!(
				amount_payed + payout <= amount,
				"amount payed out should be less or equal target amount"
			);
			let balance = Self::get_balance(&acc);
			<Balance<T>>::insert(&acc, balance + payout);
			amount_payed += payout;
		}
		assert!(
			amount_payed == amount,
			"amount payed out should equal target amount"
		);
		Ok(())
	}
}

/// tests for this pallet
#[cfg(test)]
mod tests {
	use super::*;
	use itertools::Itertools;
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

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	static LAST_PRICE: AtomicU64 = AtomicU64::new(BASE_UNIT);
	struct RandomPrice;

	impl FetchPrice<Coins> for RandomPrice {
		fn fetch_price() -> Coins {
			let prev = LAST_PRICE.load(Ordering::SeqCst);
			let random = thread_rng().gen_range(500, 1500);
			let ratio: Ratio<u64> = Ratio::new(random, 1000);
			let next = ratio
				.checked_mul(&mut prev.into())
				.map(|r| r.to_integer())
				.unwrap_or(prev);
			LAST_PRICE.store(next, Ordering::SeqCst);
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
		type OnReapAccount = ();
	}

	impl Trait for Test {
		type Event = ();
		type ExpirationPeriod = ExpirationPeriod;
		type MaximumBids = MaximumBids;
		type CoinPrice = RandomPrice;
	}

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

			Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), 5 * BASE_UNIT));
			Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(33), 5 * BASE_UNIT));
			Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(50), 5 * BASE_UNIT));

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
				Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), 5 * BASE_UNIT));
			}

			assert_eq!(Stablecoin::bond_bids().len(), MaximumBids::get());
		});
	}

	#[test]
	fn adding_bonds() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));

			Stablecoin::add_bond(
				3,
				Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BASE_UNIT),
			);

			let bonds = Stablecoin::bonds();
			assert_eq!(bonds.len(), 1);
			let bond = bonds[0];
			assert_eq!(bond.expiration, 100);
		})
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
			Stablecoin::hand_out_coins_to_shareholders(amount);

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
			Stablecoin::hand_out_coins_to_shareholders(amount);

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
			Stablecoin::hand_out_coins_to_shareholders(amount);

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
				Stablecoin::hand_out_coins_to_shareholders(amount);

				let len = len as u64;
				let payout = amount;
				let balance = Stablecoin::get_balance(shareholders[0]);
				assert_ge!(balance, COIN_SUPPLY / len + payout / len);
				assert_le!(balance, COIN_SUPPLY / len + 1 + payout / len + 1);

				TestResult::passed()
			})
		}

		QuickCheck::new()
			.max_tests(10)
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
			assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY / 10);
			assert_eq!(Stablecoin::get_balance(10), COIN_SUPPLY / 10);

			let amount = 13;
			Stablecoin::expand_supply(amount);

			let amount_per_acc = 1;
			assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY / 10 + amount_per_acc + 1);
			assert_eq!(Stablecoin::get_balance(2), COIN_SUPPLY / 10 + amount_per_acc + 1);
			assert_eq!(Stablecoin::get_balance(3), COIN_SUPPLY / 10 + amount_per_acc + 1);
			assert_eq!(Stablecoin::get_balance(4), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(8), COIN_SUPPLY / 10 + amount_per_acc);
			assert_eq!(Stablecoin::get_balance(10), COIN_SUPPLY / 10 + amount_per_acc);
		});
	}
}
