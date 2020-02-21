#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;

use codec::{Decode, Encode};
use core::cmp::{max, min};
use frame_support::{
	debug::native, decl_error, decl_event, decl_module, decl_storage, dispatch::DispatchResult, ensure,
	traits::Get,
};
use num_rational::Ratio;
use sp_runtime::{PerThing, Perbill, Fixed64};
use sp_std::collections::vec_deque::VecDeque;
use sp_std::iter;
use system::ensure_signed;

/// The pallet's configuration trait.
pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	type ExpirationPeriod: Get<<Self as system::Trait>::BlockNumber>;
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
			account, price, price_in_coins, quantity,
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

decl_error!{
	pub enum Error for Module<T: Trait> {
		InsufficientBalance,
	}
}

// This pallet's storage items.bonds
decl_storage! {
	trait Store for Module<T: Trait> as Stablecoin {
		Init get(fn initialized): bool = false;

		ShareSupply get(fn share_supply): u64;
		Shares get(fn shares): Vec<(T::AccountId, u64)>;

		Balance get(fn get_balance): map hasher(blake2_256) T::AccountId => Coins;

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
			.binary_search_by(|&Bid { price, .. }| bid.price.cmp(&price)) // sort the bids from greatest to lowest
			.unwrap_or_else(|i| i);
		bids.insert(index, bid);
		bids.truncate(T::MaximumBids::get());
	}

	fn contract_supply(amount: Coins) {
		let mut bids = Self::bond_bids();
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
				let Bid {account, quantity, ..} = bid;
				Self::add_bond(account, quantity);
				remaining -= quantity;
			}
		}
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

	fn expand_supply(amount: u64) {
		let mut bonds = Self::bonds();
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
					<Balance<T>>::mutate(&bond.account, |b| *b += remaining * BASE_UNIT);
					remaining = 0;
				}
			// bond does not cover the remaining amount --> resolve and continue
			} else if let Some(bond) = bonds.pop_front() {
				assert!(
					bond.payout <= remaining,
					"payout should be less than the remaining amount"
				);
				<Balance<T>>::mutate(&bond.account, |b| *b += bond.payout * BASE_UNIT);
				remaining -= bond.payout;
			}
		}
		<Bonds<T>>::put(bonds);
		if remaining > 0 {
			Self::hand_out_coins_to_shareholders(remaining * BASE_UNIT);
		}
	}

	fn hand_out_coins_to_shareholders(amount: u64) {
		let supply = Self::share_supply();
		let shares = Self::shares();
		let len = shares.len() as u64;
		let coins_per_share = max(1, amount / supply);
		let pay_extra = coins_per_share * len < amount;
		let mut amount_payed = 0;
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
	}
}

/// tests for this pallet
#[cfg(test)]
mod tests {
	use super::*;
	use itertools::Itertools;
	use more_asserts::*;
	use quickcheck::{QuickCheck, TestResult};

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
	}
	type Stablecoin = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
		system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
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

			Stablecoin::add_bid(1, BASE_UNIT / 4, 5);
			Stablecoin::add_bid(1, BASE_UNIT / 3, 5);
			Stablecoin::add_bid(1, BASE_UNIT / 2, 5);

			let bids = Stablecoin::bond_bids();
			let prices: Vec<u64> = bids.into_iter().map(|Bid {price, ..}| price).collect();
			assert_eq!(prices, vec![BASE_UNIT / 2, BASE_UNIT / 3, BASE_UNIT / 4]);
		});
	}

	#[test]
	fn amount_of_bids_is_limited() {
		new_test_ext().execute_with(|| {
			assert_ok!(Stablecoin::init(Origin::signed(1)));

			for _i in 0..(2 * MaximumBids::get()) {
				Stablecoin::add_bid(1, BASE_UNIT / 4, 5);
			}
			
			assert_eq!(Stablecoin::bond_bids().len(),  MaximumBids::get());
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
			Stablecoin::hand_out_coins_to_shareholders(amount);

			let amount_per_acc = 3 * BASE_UNIT;
			assert_eq!(
				Stablecoin::get_balance(1),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(2),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(3),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(7),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(10),
				COIN_SUPPLY / 10 + amount_per_acc
			);
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

			let amount = 8 * BASE_UNIT;
			Stablecoin::hand_out_coins_to_shareholders(amount);

			let amount_per_acc = 1 * BASE_UNIT;
			assert_eq!(
				Stablecoin::get_balance(1),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(2),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(3),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(7),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(8),
				COIN_SUPPLY / 10 + amount_per_acc
			);
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

			let amount = 13 * BASE_UNIT;
			Stablecoin::hand_out_coins_to_shareholders(amount);

			let amount_per_acc = 1 * BASE_UNIT;
			assert_eq!(
				Stablecoin::get_balance(1),
				COIN_SUPPLY / 10 + amount_per_acc + 1 * BASE_UNIT
			);
			assert_eq!(
				Stablecoin::get_balance(2),
				COIN_SUPPLY / 10 + amount_per_acc + 1 * BASE_UNIT
			);
			assert_eq!(
				Stablecoin::get_balance(3),
				COIN_SUPPLY / 10 + amount_per_acc + 1 * BASE_UNIT
			);
			assert_eq!(
				Stablecoin::get_balance(4),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(8),
				COIN_SUPPLY / 10 + amount_per_acc
			);
			assert_eq!(
				Stablecoin::get_balance(10),
				COIN_SUPPLY / 10 + amount_per_acc
			);
		});
	}

	#[test]
	fn handout_quickcheck() {
		fn property(shareholders: Vec<u64>, amount: u64) -> TestResult {
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

				let amount = amount * BASE_UNIT;
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
}
