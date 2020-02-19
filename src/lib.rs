#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::{decl_event, decl_module, decl_storage, dispatch::DispatchResult, ensure};
use num_rational::Ratio;
use sp_std::collections::vec_deque::VecDeque;
/// A pallet template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references

/// For more guidance on FRAME pallets, see the example.
/// https://github.com/paritytech/substrate/blob/master/frame/example/src/lib.rs
use sp_std::prelude::*;
use system::ensure_signed;

/// The pallet's configuration trait.
pub trait Trait: system::Trait {
    /// The overarching event type.
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

const BASE_UNIT: u64 = 1000; // 1000 units are supposed to represent $1 USD
const COIN_SUPPLY: u64 = BASE_UNIT * 100;
const SHARE_SUPPLY: u64 = 100;

#[derive(Encode, Decode, Default, Clone, PartialEq, PartialOrd, Eq, Ord)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Bond<AccountId, BlockNumber> {
    account: AccountId,
    payout: u64,
    expiration: BlockNumber,
}

#[derive(Encode, Decode, Default, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Bid<AccountId> {
    account: AccountId,
    quantity: u64,
    price: u64,
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

// This pallet's storage items.
decl_storage! {
    trait Store for Module<T: Trait> as Stablecoin {
        Init get(fn initialized): bool = false;

        Shares get(fn shares): map hasher(blake2_256) T::AccountId => u64;
        ShareOwners get(fn share_owners): Vec<T::AccountId>;

        Balance get(fn get_balance): map hasher(blake2_256) T::AccountId => u64;

        Bonds get(fn bonds): VecDeque<Bond<T::AccountId, T::BlockNumber>>;

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
            <Shares<T>>::insert(&founder, SHARE_SUPPLY);
            <ShareOwners<T>>::put(vec![&founder]);

            <Balance<T>>::insert(&founder, COIN_SUPPLY);

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

        // Just a dummy entry point.
        // function that can be called by the external world as an extrinsics call
        // takes a parameter of the type `AccountId`, stores it and emits an event
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

/// tests for this pallet
#[cfg(test)]
mod tests {
	use super::*;

	use sp_core::H256;
	use frame_support::{impl_outer_origin, assert_ok, parameter_types, weights::Weight};
	use sp_runtime::{
		traits::{BlakeTwo256, IdentityLookup}, testing::Header, Perbill,
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
    }
    type Stablecoin = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
		system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
	}

    #[test]
    fn init_and_transfer() {
        new_test_ext().execute_with(|| {
            // Just a dummy test for the dummy funtion `do_something`
            // calling the `do_something` function with a value 42
            assert_ok!(Stablecoin::init(Origin::signed(1)));

            let amount = 42;
            // asserting that the stored value is equal to what we stored
            assert_ok!(Stablecoin::transfer(Origin::signed(1), 2, amount));

            assert_eq!(Stablecoin::get_balance(1), COIN_SUPPLY - amount);
            assert_eq!(Stablecoin::get_balance(2), amount);
        });
    }
}
