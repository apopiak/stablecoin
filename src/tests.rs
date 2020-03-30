/// tests for this pallet
#[cfg(test)]
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
use sp_std::iter;
use system;

impl_outer_origin! {
	pub enum Origin for Test {}
}

const BASE_UNIT: u64 = 1000;
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
	pub const MaximumBids: u64 = 10;
	// adjust supply every second block
	pub const AdjustmentFrequency: u64 = 2;
	pub const BaseUnit: u64 = BASE_UNIT;
	pub const InitialSupply: u64 = 100 * BaseUnit::get();
	pub const MinimumSupply: u64 = BaseUnit::get();
	pub const MinimumBondPrice: Perbill = Perbill::from_percent(10);
}

type AccountId = u64;
type BlockNumber = u64;

impl system::Trait for Test {
	type Origin = Origin;
	type Call = ();
	type Index = u64;
	type BlockNumber = BlockNumber;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
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
	type CoinPrice = RandomPrice;
	type ExpirationPeriod = ExpirationPeriod;
	type MaximumBids = MaximumBids;
	type AdjustmentFrequency = AdjustmentFrequency;
	type BaseUnit = BaseUnit;
	type InitialSupply = InitialSupply;
	type MinimumSupply = MinimumSupply;
	type MinimumBondPrice = MinimumBondPrice;
}

type System = system::Module<Test>;
type Stablecoin = Module<Test>;

// This function basically just builds a genesis storage key/value store according to
// our desired mockup.
fn new_test_ext() -> sp_io::TestExternalities {
	let mut storage = system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let shareholders: Vec<(AccountId, u64)> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
		.into_iter()
		.zip(iter::repeat(1))
		.collect();
	// make sure to run our storage build function to check config
	let _ = GenesisConfig::<Test> { shareholders }.assimilate_storage(&mut storage);
	storage.into()
}

fn new_test_ext_with(shareholders: Vec<AccountId>) -> sp_io::TestExternalities {
	let mut storage = system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let shareholders: Vec<(AccountId, u64)> = shareholders.into_iter().zip(iter::repeat(1)).collect();
	// make sure to run our storage build function to check config
	let _ = GenesisConfig::<Test> { shareholders }.assimilate_storage(&mut storage);
	storage.into()
}

// ------------------------------------------------------------
// utils
type BondT = Bond<AccountId, BlockNumber>;
// Trait object that we will be interacting with.
type RingBuffer = dyn RingBufferTrait<BondT>;
// Implementation that we will instantiate.
type Transient =
	RingBufferTransient<BondT, <Stablecoin as Store>::BondsRange, <Stablecoin as Store>::Bonds, BondIndex>;

fn add_bond(bond: BondT) {
	let mut bonds: Box<RingBuffer> = Box::new(Transient::new());
	bonds.push(bond);
	bonds.commit();
}

// ------------------------------------------------------------
// init tests
#[test]
fn init_test() {
	new_test_ext().execute_with(|| {
		let shares = Stablecoin::shares();
		assert_eq!(
			shares,
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
		let share_supply: u64 = shares.iter().map(|(_a, s)| s).sum();
		assert_eq!(share_supply, 10);
	});
}

// ------------------------------------------------------------
// balances
#[test]
fn transfer_test() {
	new_test_ext().execute_with(|| {
		let first_acc = 1;
		let second_acc = 2;
		let amount = BASE_UNIT;
		let from_balance_before = Stablecoin::get_balance(first_acc);
		let to_balance_before = Stablecoin::get_balance(second_acc);
		assert_ok!(Stablecoin::transfer_from_to(&first_acc, &second_acc, amount));
		assert_eq!(Stablecoin::get_balance(first_acc), from_balance_before - amount);
		assert_eq!(Stablecoin::get_balance(second_acc), to_balance_before + amount);
	});
}

// ------------------------------------------------------------
// currency trait
#[test]
fn slash_test() {
	new_test_ext().execute_with(|| {
		let acc = 1;
		let amount = BASE_UNIT;
		let balance_before = Stablecoin::get_balance(acc);
		assert_eq!(Stablecoin::slash(&acc, amount), 0);
		assert_eq!(Stablecoin::get_balance(acc), balance_before - amount);
	});
}

// ------------------------------------------------------------
// bids
#[test]
fn bids_are_sorted_highest_to_lowest() {
	new_test_ext().execute_with(|| {
		let bid_amount = 5 * BaseUnit::get();
		Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), bid_amount));
		Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(33), bid_amount));
		Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(50), bid_amount));

		let bids = Stablecoin::bond_bids();
		let prices: Vec<_> = bids.into_iter().map(|Bid { price, .. }| price).collect();
		// largest bid is stored last so we can pop
		assert_eq!(
			prices,
			vec![
				Perbill::from_percent(25),
				Perbill::from_percent(33),
				Perbill::from_percent(50),
			]
		);
	});
}

#[test]
fn amount_of_bids_is_limited() {
	new_test_ext().execute_with(|| {
		let bid_amount = 5 * BaseUnit::get();
		for _i in 0..(2 * MaximumBids::get()) {
			Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), bid_amount));
		}

		assert_eq!(Stablecoin::bond_bids().len() as u64, MaximumBids::get());
	});
}

#[test]
fn truncated_bids_are_refunded() {
	new_test_ext_with(vec![1]).execute_with(|| {
		let price = Perbill::from_percent(25);
		let quantity = BaseUnit::get();
		for _i in 0..(MaximumBids::get() + 1) {
			assert_ok!(Stablecoin::bid_for_bond(Origin::signed(1), price, quantity));
		}

		assert_eq!(Stablecoin::bond_bids().len() as u64, MaximumBids::get());
		let expected = InitialSupply::get() - price * quantity * (MaximumBids::get() as u64);
		assert_eq!(Stablecoin::get_balance(1), expected);
	});
}

#[test]
fn cancel_all_bids_test() {
	new_test_ext().execute_with(|| {
		let bid_amount = 5 * BaseUnit::get();
		Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), bid_amount));
		Stablecoin::add_bid(Bid::new(2, Perbill::from_percent(33), bid_amount));
		Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(50), bid_amount));
		Stablecoin::add_bid(Bid::new(3, Perbill::from_percent(50), bid_amount));
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
		let bid_amount = 5 * BaseUnit::get();
		Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(25), bid_amount));
		Stablecoin::add_bid(Bid::new(2, Perbill::from_percent(33), bid_amount));
		Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(45), bid_amount));
		Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(50), bid_amount));
		Stablecoin::add_bid(Bid::new(3, Perbill::from_percent(55), bid_amount));
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
		// highest bid is last so we can pop
		assert_eq!(
			bids,
			vec![
				(2, Perbill::from_percent(33)),
				(1, Perbill::from_percent(50)),
				(3, Perbill::from_percent(55)),
			]
		);
	});
}

// ------------------------------------------------------------
// bonds
#[test]
fn adding_bonds() {
	new_test_ext().execute_with(|| {
		let payout = Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BaseUnit::get());
		add_bond(Stablecoin::new_bond(3, payout));

		let (start, end) = Stablecoin::bonds_range();
		// computing the length this way is fine because there was no overflow
		assert_eq!(end - start, 1);
		let bond = &Stablecoin::get_bond(start);
		assert_eq!(bond.expiration, System::block_number() + ExpirationPeriod::get());
	})
}

#[test]
fn expire_bonds() {
	new_test_ext_with(vec![1]).execute_with(|| {
		let acc = 3;
		let prev_acc_balance = Stablecoin::get_balance(acc);
		let payout = Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BaseUnit::get());
		add_bond(Stablecoin::new_bond(acc, payout));

		let (start, end) = Stablecoin::bonds_range();
		// computing the length this way is fine because there was no overflow
		assert_eq!(end - start, 1);
		let bond = &Stablecoin::get_bond(start);
		assert_eq!(bond.expiration, System::block_number() + ExpirationPeriod::get());

		let prev_supply = Stablecoin::coin_supply();
		// set blocknumber past expiration time
		System::set_block_number(System::block_number() + ExpirationPeriod::get());
		assert_ok!(Stablecoin::expand_supply(prev_supply, 42));
		let acc_balance = Stablecoin::get_balance(acc);
		assert_eq!(
			prev_acc_balance, acc_balance,
			"account balance should not change as the bond expired"
		);
		assert_eq!(
			prev_supply + 42,
			Stablecoin::coin_supply(),
			"coin supply should have increased"
		);
	});
}

#[test]
fn expire_bonds_and_expand_supply() {
	new_test_ext_with(vec![1]).execute_with(|| {
		let first_acc = 3;
		let prev_first_acc_balance = Stablecoin::get_balance(first_acc);
		// 1.2 * BaseUnit
		let payout = Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BaseUnit::get());
		add_bond(Stablecoin::new_bond(first_acc, payout));

		let (start, end) = Stablecoin::bonds_range();
		// computing the length this way is fine because there was no overflow
		assert_eq!(end - start, 1);
		let bond = &Stablecoin::get_bond(start);
		assert_eq!(bond.expiration, System::block_number() + ExpirationPeriod::get());

		let prev_supply = Stablecoin::coin_supply();
		let second_acc = first_acc + 1;
		let prev_second_acc_balance = Stablecoin::get_balance(second_acc);
		// set blocknumber to the block number right before the first bond's expiration block
		System::set_block_number(System::block_number() + ExpirationPeriod::get() - 1);
		// Add a new bond
		add_bond(Stablecoin::new_bond(second_acc, payout));
		add_bond(Stablecoin::new_bond(second_acc, payout));
		add_bond(Stablecoin::new_bond(second_acc, payout));
		// Note: this one is from first_acc
		add_bond(Stablecoin::new_bond(first_acc, payout));

		// check bonds length
		let (start, end) = Stablecoin::bonds_range();
		// computing the length this way is fine because there was no overflow
		assert_eq!(end - start, 5);
		// Increase block number by one so that we reach the first bond's expiration block number.
		System::set_block_number(System::block_number() + 1);
		// expand the supply, only hitting the last bond that was added to the queue, but not fully filling it
		let new_coins = payout;
		assert_ok!(Stablecoin::expand_supply(Stablecoin::coin_supply(), new_coins));
		// make sure there are only three bonds left (the first one expired, the second one got consumed)
		let (start, end) = Stablecoin::bonds_range();
		// computing the length this way is fine because there was no overflow
		assert_eq!(end - start, 3);
		// make sure the first account's balance hasn't changed
		assert_eq!(prev_first_acc_balance, Stablecoin::get_balance(first_acc));
		// make sure the second account's balance has increased by `new_coins`
		let intermediate_second_acc_balance = prev_second_acc_balance + new_coins;
		assert_eq!(
			prev_second_acc_balance + new_coins,
			Stablecoin::get_balance(second_acc)
		);
		// make sure total supply increased by `new_coins`
		assert_eq!(prev_supply + new_coins, Stablecoin::coin_supply());

		let intermediate_supply = Stablecoin::coin_supply();
		// Set the block number to be *exactly equal* to the expiration date of all bonds that are left in the queue
		System::set_block_number(System::block_number() + ExpirationPeriod::get() - 1);

		// try to expand_supply, expected to do nothing because all bonds have expired
		let new_coins = 42;
		assert_ok!(Stablecoin::expand_supply(intermediate_supply, new_coins));

		// make sure there are no bonds left (they have all expired)
		let (start, end) = Stablecoin::bonds_range();
		// computing the length this way is fine because there was no overflow
		assert_eq!(end - start, 0);

		// make sure first and second's balances haven't changed
		assert_eq!(prev_first_acc_balance, Stablecoin::get_balance(first_acc));
		assert_eq!(
			intermediate_second_acc_balance,
			Stablecoin::get_balance(second_acc)
		);

		// Make sure coin supply has increased by `new_coins`
		assert_eq!(
			intermediate_supply + new_coins,
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
		let balance_per_acc = InitialSupply::get() / 10;
		assert_eq!(Stablecoin::get_balance(1), balance_per_acc);
		assert_eq!(Stablecoin::get_balance(10), balance_per_acc);

		let amount = 30 * BaseUnit::get();
		assert_ok!(Stablecoin::hand_out_coins(
			&Stablecoin::shares(),
			amount,
			Stablecoin::coin_supply()
		));

		let amount_per_acc = 3 * BaseUnit::get();
		assert_eq!(Stablecoin::get_balance(1), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(2), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(3), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(7), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(10), balance_per_acc + amount_per_acc);
	});
}

#[test]
fn handout_less_than_shares_test() {
	new_test_ext().execute_with(|| {
		let balance_per_acc = InitialSupply::get() / 10;
		assert_eq!(Stablecoin::get_balance(1), balance_per_acc);
		assert_eq!(Stablecoin::get_balance(10), balance_per_acc);

		let amount = 8;
		assert_ok!(Stablecoin::hand_out_coins(
			&Stablecoin::shares(),
			amount,
			Stablecoin::coin_supply()
		));

		let amount_per_acc = 1;
		assert_eq!(Stablecoin::get_balance(1), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(2), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(3), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(7), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(8), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(9), balance_per_acc);
		assert_eq!(Stablecoin::get_balance(10), balance_per_acc);
	});
}

#[test]
fn handout_more_than_shares_test() {
	new_test_ext().execute_with(|| {
		let balance_per_acc = InitialSupply::get() / 10;
		assert_eq!(Stablecoin::get_balance(1), balance_per_acc);
		assert_eq!(Stablecoin::get_balance(10), balance_per_acc);

		let amount = 13;
		assert_ok!(Stablecoin::hand_out_coins(
			&Stablecoin::shares(),
			amount,
			Stablecoin::coin_supply()
		));

		let amount_per_acc = 1;
		assert_eq!(Stablecoin::get_balance(1), balance_per_acc + amount_per_acc + 1);
		assert_eq!(Stablecoin::get_balance(2), balance_per_acc + amount_per_acc + 1);
		assert_eq!(Stablecoin::get_balance(3), balance_per_acc + amount_per_acc + 1);
		assert_eq!(Stablecoin::get_balance(4), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(8), balance_per_acc + amount_per_acc);
		assert_eq!(Stablecoin::get_balance(10), balance_per_acc + amount_per_acc);
	});
}

#[test]
fn handout_quickcheck() {
	fn property(shareholders: Vec<AccountId>, amount: Coins) -> TestResult {
		let len = shareholders.len();
		if amount == 0 {
			return TestResult::discard();
		}
		// Expects between 1 and 999 shareholders.
		if len < 1 || len > 999 {
			return TestResult::discard();
		}
		// 0 is not a valid AccountId
		if shareholders.iter().any(|s| *s == 0) {
			return TestResult::discard();
		}
		// make sure shareholders are distinct
		if shareholders.iter().unique().count() != len {
			return TestResult::discard();
		}

		let first = shareholders[0];

		new_test_ext_with(shareholders).execute_with(|| {
			let amount = amount;
			// this assert might actually produce a false positive
			// as there might be errors returned that are the correct
			// behavior for the given parameters
			assert_ok!(Stablecoin::hand_out_coins(
				&Stablecoin::shares(),
				amount,
				Stablecoin::coin_supply()
			));

			let len = len as u64;
			let payout = amount;
			let balance = Stablecoin::get_balance(first);
			assert_ge!(balance, InitialSupply::get() / len + payout / len);
			assert_le!(balance, InitialSupply::get() / len + 1 + payout / len + 1);

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
		// payout of 120% of BaseUnit
		let payout = Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BaseUnit::get());
		add_bond(Stablecoin::new_bond(2, payout));
		add_bond(Stablecoin::new_bond(3, payout));
		add_bond(Stablecoin::new_bond(4, payout));
		add_bond(Stablecoin::new_bond(5, 7 * payout));

		let prev_supply = Stablecoin::coin_supply();
		let amount = 13 * BaseUnit::get();
		assert_ok!(Stablecoin::expand_supply(prev_supply, amount));

		let amount_per_acc = InitialSupply::get() / 10 + BaseUnit::get() / 10;
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
		let bond_amount = Ratio::new(125, 100)
			.checked_mul(&BaseUnit::get().into())
			.map(|r| r.to_integer())
			.expect("bond_amount should not have overflowed");
		Stablecoin::add_bid(Bid::new(1, Perbill::from_percent(80), bond_amount));
		Stablecoin::add_bid(Bid::new(2, Perbill::from_percent(75), 2 * BaseUnit::get()));

		let prev_supply = Stablecoin::coin_supply();
		let amount = 2 * BaseUnit::get();
		assert_ok!(Stablecoin::contract_supply(prev_supply, amount));

		let bids = Stablecoin::bond_bids();
		assert_eq!(bids.len(), 1, "exactly one bid should have been removed");
		let remainging_bid_quantity = saturated_mul(Fixed64::from_rational(667, 1_000), BaseUnit::get());
		assert_eq!(
			bids[0],
			Bid::new(2, Perbill::from_percent(75), remainging_bid_quantity)
		);

		let (start, _) = Stablecoin::bonds_range();
		assert_eq!(Stablecoin::get_bond(start).payout, bond_amount);
		assert_eq!(
			Stablecoin::get_bond(start + 1).payout,
			Fixed64::from_rational(333, 1_000).saturated_multiply_accumulate(BaseUnit::get())
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

			for (account, payout) in bonds {
				if account > 0 && payout > 0 {
					add_bond(Stablecoin::new_bond(account, payout));
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
			.map(|_| (rng.gen_range(1, 200), rng.gen_range(1, 10 * BaseUnit::get())))
			.collect();

		for (account, payout) in bonds {
			add_bond(Stablecoin::new_bond(account, payout));
		}

		for _ in 0..150 {
			let price = RandomPrice::fetch_price();
			Stablecoin::on_block_with_price(0, price).unwrap_or_else(|e| {
				log::error!("could not adjust supply: {:?}", e);
			});
		}
	})
}
