//! # Stablecoin example pallet
//!
//! This is a substrate pallet showcasing a sample implementation of a non-collateralized
//! stablecoin based on the [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf).
//!
//! **Note: Example project for illustration, NOT audited and NOT production ready.**
//!
//! ## Dependencies
//!
//! This pallet depends on an external implementation of its `FetchPrice` trait - for example by an offchain worker - to act as a price oracle.
//!
//! ## Installation
//!
//! ### Runtime `Cargo.toml`
//!
//! To add this pallet to your runtime, simply include the following in your runtime's `Cargo.toml` file:
//!
//! ```TOML
//! [dependencies.pallet-stablecoin]
//! default_features = false
//! git = 'https://github.com/apopiak/pallet-stablecoin.git'
//! ```
//!
//! and update your runtime's `std` feature to include this pallet's `std` feature:
//!
//! ```TOML
//! std = [
//!     # --snip--
//!     'pallet_stablecoin/std',
//! ]
//! ```
//!
//! ### Runtime `lib.rs`
//!
//! Here is an example imlementation of its trait:
//!
//! ```rust,ignore
//! use pallet_stablecoin::Coins;
//!
//! parameter_types! {
//!     pub const ExpirationPeriod: BlockNumber = 5 * 365 * DAYS; // 5 years = 5 * 365 * DAYS
//!     pub const MaximumBids: usize = 1_000;
//!     pub const MinimumBondPrice: Perbill = Perbill::from_percent(10);
//!     pub const AdjustmentFrequency: BlockNumber = 1 * MINUTES; // 1 minute = 60000 / MILLISECS_PER_BLOCK
//!     pub const BaseUnit: Coins = 1_000_000;
//!     pub const InitialSupply: Coins = 1000 * BaseUnit::get();
//!     pub const MinimumSupply: Coins = BaseUnit::get();
//! }
//!
//! impl pallet_stablecoin::Trait for Runtime {
//!     type Event = Event;
//!     
//!     type CoinPrice = some_price_oracle::Module<Runtime>;
//!     type ExpirationPeriod = ExpirationPeriod;
//!     type MaximumBids = MaximumBids;
//!     type MinimumBondPrice = MinimumBondPrice;
//!     type AdjustmentFrequency = AdjustmentFrequency;
//!     type BaseUnit = BaseUnit;
//!     type InitialSupply = InitialSupply;
//!     type MinimumSupply = MinimumSupply;
//! }
//! ```
//!
//! and include it in your `construct_runtime!` macro:
//!
//! ```rust,ignore
//! Stablecoin: pallet_stablecoin::{Module, Call, Storage, Event<T>},
//! ```
//!
//! ### GenesisConfig `chain_spec.rs`
//!
//! Runtimes using the pallet need to add the `StablecoinConfig` to their genesis config.
//! The config expects a `Vec(AccountId, u64)` to initialize the shareholders.
//! See the following snippet for an example:
//!
//! ```rust,ignore
//! use node_template_runtime::{ // ... other imports
//!     StablecoinConfig
//! };
//! // ...
//!
//!     GenesisConfig {
//!         system: Some(SystemConfig { /* elided */ }),
//!         // ... other configs
//!         stablecoin: Some(StablecoinConfig {
//!             shareholders: endowed_accounts.iter().cloned().map(|acc| (acc, 1)).collect(),
//!         }),
//!     }
//! ```
//!
//! With this config the endowed accounts will be the shareholders of the stablecoin.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;

use adapters::{BoundedPriorityQueue, BoundedDeque};
use codec::{Decode, Encode};
use core::cmp::{max, min, Ord, Ordering};
use fixed::{types::extra::U64, FixedU128};
use frame_support::{
	debug::native,
	decl_error, decl_event, decl_module, decl_storage,
	dispatch::{DispatchError, DispatchResult},
	ensure,
	traits::Get,
};
use num_rational::Ratio;
use orml_traits::BasicCurrency;
use sp_runtime::{
	traits::{CheckedMul, Zero},
	PerThing, Perbill, RuntimeDebug,
};
use sp_std::collections::vec_deque::VecDeque;
use system::ensure_signed;

#[cfg(test)]
mod tests;

/// Expected price oracle interface. `fetch_price` must return the amount of Coins exchanged for the tracked value.
pub trait FetchPrice<Balance> {
	/// Fetch the current price.
	fn fetch_price() -> Balance;
}

/// The type used to represent the account balance for the stablecoin.
pub type Coins = u64;
/// The type used to index into the map storing the bonds queue.
pub type BondIndex = u16;

/// The pallet's configuration trait.
pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The amount of Coins necessary to buy the tracked value. (e.g., 1_100 for 1$)
	type CoinPrice: FetchPrice<Coins>;
	/// The expiration time of a bond.
	///
	/// The [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf) recommends an expiration
	/// period of 5 years.
	type ExpirationPeriod: Get<<Self as system::Trait>::BlockNumber>;
	/// The maximum amount of bids allowed in the queue. Used to prevent the queue from growing forever.
	type MaximumBids: Get<u64>;
	/// The minimum percentage to pay for a bond.
	///
	/// The [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf) recommends a minimum
	/// bond price of 10% based on simulations.
	type MinimumBondPrice: Get<Perbill>;
	/// The frequency of adjustments of the coin supply.
	type AdjustmentFrequency: Get<<Self as system::Trait>::BlockNumber>;
	/// The amount of Coins that are meant to track the value. Example: A value of 1_000 when tracking
	/// Dollars means that the Stablecoin will try to maintain a price of 1_000 Coins for 1$.
	type BaseUnit: Get<Coins>;
	/// The initial supply of Coins.
	type InitialSupply: Get<Coins>;
	/// The minimum amount of Coins in circulation.
	///
	/// Must be lower than `InitialSupply`.
	type MinimumSupply: Get<Coins>;
}

/// A bond representing (potential) future payout of Coins.
///
/// Expires at block `expiration` so it will be discarded if payed out after that block.
///
/// + `account` is the recipient of the bond payout.
/// + `payout` is the amount of Coins payed out.
#[derive(Encode, Decode, Default, Clone, PartialEq, PartialOrd, Eq, Ord, RuntimeDebug)]
pub struct Bond<AccountId, BlockNumber> {
	account: AccountId,
	payout: Coins,
	expiration: BlockNumber,
}

/// A bid for a bond of the stablecoin at a certain price.
///
/// + `account` is the bidder.
/// + `price` is a percentage of 1 coin.
/// + `quantity` is the amount of Coins gained on payout of the corresponding bond.
#[derive(Encode, Decode, Default, Clone, RuntimeDebug)]
pub struct Bid<AccountId> {
	account: AccountId,
	price: Perbill,
	quantity: Coins,
}

// Implement `Ord` for `Bid` to get the wanted sorting in the priority queue.
// TODO: Could this create issues in testing? How to address?
impl<AccountId> PartialEq for Bid<AccountId> {
	fn eq(&self, other: &Self) -> bool {
		self.price == other.price
	}
}
impl<AccountId> Eq for Bid<AccountId> {}

impl<AccountId> PartialOrd for Bid<AccountId> {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}
/// Sort `Bid`s by price.
impl<AccountId> Ord for Bid<AccountId> {
	fn cmp(&self, other: &Self) -> Ordering {
		self.price.cmp(&other.price)
	}
}

/// Error returned from `remove_coins` if there is an over- or underflow.
pub enum BidError {
	/// `remove_coins` overflowed.
	Overflow,
	/// `remove_coins` underflowed.
	Underflow,
}

impl<AccountId> Bid<AccountId> {
	/// Create a new bid.
	fn new(account: AccountId, price: Perbill, quantity: Coins) -> Bid<AccountId> {
		Bid {
			account,
			price,
			quantity,
		}
	}

	/// Return the amount of Coins to be payed for this bid.
	fn payment(&self) -> Coins {
		// This naive multiplication is fine because Perbill has an implementation tuned for balance types.
		self.price * self.quantity
	}

	/// Remove `coins` amount of Coins from the bid, mirroring the changes in quantity
	/// according to the price attached to the bid.
	fn remove_coins(&mut self, coins: Coins) -> Result<Coins, BidError> {
		// Inverse price is needed because `self.price` converts from amount of bond payout coins to payment coins,
		// but we need to convert the other way from payment coins to bond payout coins.
		// `self.price` equals the fraction of coins I'm willing to pay now in exchange for a bond.
		// But we need to calculate the amount of bond payouts corresponding to the coins I'm willing to pay now
		// which means we need to use the inverse of self.price!
		let inverse_price: Ratio<u64> = Ratio::new(Perbill::ACCURACY.into(), self.price.deconstruct().into());

		// Should never overflow, but better safe than sorry.
		let removed_quantity = inverse_price
			.checked_mul(&coins.into())
			.map(|r| r.to_integer())
			.ok_or(BidError::Overflow)?;
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
		/// Successful transfer from the first to the second account.
		Transfer(AccountId, AccountId, u64),
		/// New bid was registered for the account at given price and amount.
		NewBid(AccountId, Perbill, u64),
		/// A bid was refunded (repayed and removed from the queue).
		RefundedBid(AccountId, u64),
		/// A new bond was created for the account with payout and expiration.
		NewBond(AccountId, u64, BlockNumber),
		/// A bond was payed out to the account.
		BondFulfilled(AccountId, u64),
		/// A bond was partially payed out to the account.
		BondPartiallyFulfilled(AccountId, u64),
		/// A bond expired and was removed from the bond queue.
		BondExpired(AccountId, u64),
		/// All bids at and above the given price were cancelled for the account.
		CancelledBidsAbove(AccountId, Perbill),
		/// All bids at and below the given price were cancelled for the account.
		CancelledBidsBelow(AccountId, Perbill),
		/// All bids were cancelled for the account.
		CancelledBids(AccountId),
		/// The supply was expanded by the amount.
		ExpandedSupply(u64),
		/// The supply was contracted by the amount.
		ContractedSupply(u64),
	}
);

decl_error! {
	/// The possible errors returned by calls to this pallet's functions.
	pub enum Error for Module<T: Trait> {
		/// While trying to expand the supply, it overflowed.
		CoinSupplyOverflow,
		/// While trying to contract the supply, it underflowed.
		CoinSupplyUnderflow,
		/// The account trying to use funds (e.g., for bidding) does not have enough balance.
		InsufficientBalance,
		/// While trying to increase the balance for an account, it overflowed.
		BalanceOverflow,
		/// Something went very wrong and the price of the currency is zero.
		ZeroPrice,
		/// An arithmetic operation caused an overflow.
		GenericOverflow,
		/// An arithmetic operation caused an underflow.
		GenericUnderflow,
		/// The bidder tried to pay more than 100% for a bond.
		BondPriceOver100Percent,
		/// The bidding price is below `MinimumBondPrice`.
		BondPriceTooLow,
		/// The bond being bid for is not big enough (in amount of Coins).
		BondQuantityTooLow,
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
		/// The allocation of shares to accounts.
		///
		/// This is a `Vec` and thus should be limited to few shareholders (< 1_000).
		/// In principle it would be possible to make shares tradeable. In that case
		/// we would have to use a map similar to the `Balance` one.
		Shares get(fn shares): Vec<(T::AccountId, u64)>;

		/// The balance of stablecoin associated with each account.
		Balance get(fn get_balance): map hasher(blake2_128_concat) T::AccountId => Coins;

		/// The total amount of Coins in circulation.
		CoinSupply get(fn coin_supply): Coins = 0;

		/// The available bonds for contracting supply.
		Bonds get(fn get_bond): map hasher(twox_64_concat) BondIndex => Bond<T::AccountId, T::BlockNumber>;
		/// Start and end index pair used to implement a ringbuffer on top of the `Bonds` map.
		BondsRange get(fn bonds_range): (BondIndex, BondIndex) = (0, 0);

		/// The current bidding queue for bonds.
		BondBids get(fn bond_bids): Vec<Bid<T::AccountId>>;
	}
	add_extra_genesis {
		/// The shareholders to initialize the stablecoin with.
		config(shareholders):
			Vec<(T::AccountId, u64)>;
		build(|config: &GenesisConfig<T>| {
			assert!(
				T::MinimumSupply::get() < T::InitialSupply::get(),
				"initial coin supply needs to be greater than the minimum"
			);

			assert!(!config.shareholders.is_empty(), "need at least one shareholder");
			// TODO: make sure shareholders are unique?

			// Hand out the initial coin supply to the shareholders.
			<Module<T>>::hand_out_coins(&config.shareholders, T::InitialSupply::get(), <Module<T>>::coin_supply())
				.expect("initialization handout should not fail");

			// Store the shareholders with their shares.
			<Shares<T>>::put(&config.shareholders);
		});
	}
}

decl_module! {
	/// The pallet's dispatchable functions.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// The minimum percentage to pay for a bond.
		const MinimumBondPrice: Perbill = T::MinimumBondPrice::get();
		/// The expiration period for a bond.
		const ExpirationPeriod: T::BlockNumber = T::ExpirationPeriod::get();
		/// The amount of stablecoins that represent 1 external value (e.g., 1$).
		const BaseUnit: Coins = T::BaseUnit::get();
		/// The maximum amount of bids in the bidding queue.
		const MaximumBids: u64 = T::MaximumBids::get();
		/// How often the coin supply will be adjusted based on price.
		const AdjustmentFrequency: T::BlockNumber = T::AdjustmentFrequency::get();
		/// The minimum amount of Coins that will be in circulation.
		const MinimumSupply: Coins = T::MinimumSupply::get();

		fn deposit_event() = default;

		/// Transfer `amount` Coins from the sender to the account `to`.
		///
		/// **Weight:**
		/// - complexity: `O(1)`
		/// - DB access: 2 storage map reads + 2 storage map writes
		pub fn send_coins(origin, to: T::AccountId, amount: u64) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::transfer_from_to(&sender, &to, amount)?;
			Self::deposit_event(RawEvent::Transfer(sender, to, amount));
			Ok(())
		}

		/// Bid for `quantity` Coins at a `price`.
		///
		/// + `price` is a fraction of the desired payout quantity (e.g., 80%).
		/// + Expects a `quantity` of a least `BaseUnit`.
		///
		/// Example: `bid_for_bond(origin, Perbill::from_percent(80), 5 * BaseUnit)` will bid
		/// for a bond with a payout of `5 * BaseUnit` Coins for a price of
		/// `0.8 * 5 * BaseUnit = 4 * BaseUnit` Coins.
		///
		/// **Weight:**
		/// - complexity: `O(B)`
		///   - `B` being the number of bids in the bidding auction, limited to `MaximumBids`
		/// - DB access:
		///   - read and write bids from and to DB
		///   - 1 DB storage map write to pay the bid
		///   - 1 potential DB storage map write to refund evicted bid
		pub fn bid_for_bond(origin, price: Perbill, quantity: Coins) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(price <= Perbill::from_percent(100), Error::<T>::BondPriceOver100Percent);
			ensure!(price > T::MinimumBondPrice::get(), Error::<T>::BondPriceTooLow);
			ensure!(quantity >= T::BaseUnit::get(), Error::<T>::BondQuantityTooLow);

			let bid = Bid::new(who.clone(), price, quantity);

			// ↑ verify ↑
			Self::remove_balance(&who, bid.payment())?;
			// ↓ update ↓
			Self::add_bid(bid);
			Self::deposit_event(RawEvent::NewBid(who, price, quantity));

			Ok(())
		}

		/// Cancel all bids at or below `price` of the sender and refund the Coins.
		///
		/// **Weight:**
		/// - complexity: `O(B)`
		///   - `B` being the number of bids in the bidding auction, limited to `MaximumBids`
		/// - DB access: read and write bids from and to DB
		pub fn cancel_bids_at_or_below(origin, price: Perbill) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// ↑ verify ↑
			// ↓ update ↓
			Self::cancel_bids(|bid| bid.account == who && bid.price <= price);
			Self::deposit_event(RawEvent::CancelledBidsBelow(who, price));

			Ok(())
		}

		pub fn cancel_bids_at_or_above(origin, price: Perbill) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// ↑ verify ↑
			// ↓ update ↓
			Self::cancel_bids(|bid| bid.account == who && bid.price >= price);
			Self::deposit_event(RawEvent::CancelledBidsAbove(who, price));

			Ok(())
		}

		/// Cancel all bids belonging to the sender and refund the Coins.
		///
		/// **Weight:**
		/// - complexity: `O(B)`
		///   - `B` being the number of bids in the bidding auction, limited to `MaximumBids`
		/// - DB access: read and write bids from and to DB
		pub fn cancel_all_bids(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// ↑ verify ↑
			// ↓ update ↓
			Self::cancel_bids(|bid| bid.account == who);
			Self::deposit_event(RawEvent::CancelledBids(who));

			Ok(())
		}

		/// Adjust the amount of Coins according to the price.
		///
		/// **Weight:**
		/// - complexity: `O(F + P)`
		///   - `F` being the complexity of `CoinPrice::fetch_price()`
		///   - `P` being the complexity of `on_block_with_price`
		fn on_initialize(n: T::BlockNumber) {
			let price = T::CoinPrice::fetch_price();
			Self::on_block_with_price(n, price).unwrap_or_else(|e| {
				native::error!("could not adjust supply: {:?}", e);
			});
		}
	}
}

// Implement the BasicCurrency to allow other pallets to interact programmatically
// with the Stablecoin.
impl<T: Trait> BasicCurrency<T::AccountId> for Module<T> {
	type Balance = Coins;

	/// Return the amount of Coins in circulation.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 1 read
	fn total_issuance() -> Self::Balance {
		Self::coin_supply()
	}

	/// Return the balance of the given account.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 1 read from balance storage map
	fn total_balance(who: &T::AccountId) -> Self::Balance {
		Self::get_balance(who)
	}

	/// Return the free balance of the given account.
	///
	/// Equal to `total_balance` for this stablecoin.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 1 read from balance storage map
	fn free_balance(who: &T::AccountId) -> Self::Balance {
		Self::get_balance(who)
	}

	/// Cannot withdraw from stablecoin accounts. Returns `Ok(())` if `amount` is 0, otherwise returns an error.
	fn ensure_can_withdraw(_who: &T::AccountId, amount: Self::Balance) -> DispatchResult {
		if amount.is_zero() {
			return Ok(());
		}
		Err(DispatchError::Other("cannot change issuance for stablecoins"))
	}

	/// Transfer `amount` from one account to another.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 2 reads and write from and to balance storage map
	fn transfer(from: &T::AccountId, to: &T::AccountId, amount: Self::Balance) -> DispatchResult {
		Self::transfer_from_to(from, to, amount)
	}

	/// Noop that returns an error. Cannot change the issuance of a stablecoin.
	fn deposit(_who: &T::AccountId, _amount: Self::Balance) -> DispatchResult {
		Err(DispatchError::Other("cannot change issuance for stablecoins"))
	}

	/// Noop that returns an error. Cannot change the issuance of a stablecoin.
	fn withdraw(_who: &T::AccountId, _amount: Self::Balance) -> DispatchResult {
		Err(DispatchError::Other("cannot change issuance for stablecoins"))
	}

	/// Test whether the given account can be slashed with `value`.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 1 read from balance storage map
	fn can_slash(who: &T::AccountId, value: Self::Balance) -> bool {
		if value.is_zero() {
			return true;
		}
		Self::get_balance(who) >= value
	}

	/// Slash account `who` by `amount` returning the actual amount slashed.
	///
	/// If the account does not have `amount` Coins it will be slashed to 0
	/// and that amount returned.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 1 write to balance storage map
	fn slash(who: &T::AccountId, amount: Self::Balance) -> Self::Balance {
		let mut remaining: Coins = 0;
		<Balance<T>>::mutate(who, |b: &mut u64| {
			if *b < amount {
				remaining = amount - *b;
				*b = 0;
			} else {
				*b = b.saturating_sub(amount);
			}
		});
		remaining
	}
}

impl<T: Trait> Module<T> {
	// ------------------------------------------------------------
	// balances

	/// Transfer `amount` of Coins from one account to another.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 2 storage map reads + 2 storage map writes
	fn transfer_from_to(from: &T::AccountId, to: &T::AccountId, amount: Coins) -> DispatchResult {
		let from_balance = Self::get_balance(from);
		let updated_from_balance = from_balance
			.checked_sub(amount)
			.ok_or(Error::<T>::InsufficientBalance)?;
		let receiver_balance = Self::get_balance(&to);
		let updated_to_balance = receiver_balance
			.checked_add(amount)
			.ok_or(Error::<T>::BalanceOverflow)?;

		// ↑ verify ↑
		// ↓ update ↓

		// reduce from's balance
		<Balance<T>>::insert(&from, updated_from_balance);
		// increase receiver's balance
		<Balance<T>>::insert(&to, updated_to_balance);

		Ok(())
	}

	/// Add `amount` Coins to the balance for `account`.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 1 write to balance storage map
	fn add_balance(account: &T::AccountId, amount: Coins) {
		<Balance<T>>::mutate(account, |b: &mut u64| {
			*b = b.saturating_add(amount);
			*b
		});
	}

	/// Remove `amount` Coins from the balance of `account`.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 1 write to balance storage map
	fn remove_balance(account: &T::AccountId, amount: Coins) -> DispatchResult {
		<Balance<T>>::try_mutate(&account, |b: &mut u64| -> DispatchResult {
			*b = b.checked_sub(amount).ok_or(Error::<T>::InsufficientBalance)?;
			Ok(())
		})
	}

	// ------------------------------------------------------------
	// bids

	/// Construct a transient storage adapter for the bids priority queue.
	fn bids_transient() -> BoundedPriorityQueue<Bid<T::AccountId>, <Self as Store>::BondBids, T::MaximumBids>
	{
		BoundedPriorityQueue::<Bid<T::AccountId>, <Self as Store>::BondBids, T::MaximumBids>::new()
	}

	/// Add a bid to the queue.
	///
	/// **Weight:**
	/// - complexity: `O(B)` with `B` being the amount of bids
	/// - DB access:
	///   - read and write `B` bids
	///   - potentially call 1 `refund_bid`
	fn add_bid(bid: Bid<T::AccountId>) {
		Self::bids_transient()
			.push(bid)
			.map(|to_refund| Self::refund_bid(&to_refund));
	}

	/// Refund the Coins payed for `bid` to the account that bid.
	///
	/// **Weight:**
	/// - complexity: `O(1)`
	/// - DB access: 1 write
	fn refund_bid(bid: &Bid<T::AccountId>) {
		Self::add_balance(&bid.account, bid.payment());
		Self::deposit_event(RawEvent::RefundedBid(bid.account.clone(), bid.payment()));
	}

	/// Cancel all bids where `cancel_for` returns true and refund the bidders.
	///
	/// **Weight:**
	/// - complexity: `O(B)` with `B` being the amount of bids
	/// - DB access:
	///   - read and write `B` bids
	///   - call `refund_bid` up to `B` times
	fn cancel_bids<F>(cancel_for: F)
	where
		F: Fn(&Bid<T::AccountId>) -> bool,
	{
		let mut bids = Self::bond_bids();

		bids.retain(|b| {
			if cancel_for(b) {
				Self::refund_bid(b);
				return false;
			}
			true
		});

		<BondBids<T>>::put(bids);
	}

	/// Tries to contract the supply by `amount` by converting bids to bonds.
	///
	/// Note: Could contract the supply by less than `amount` if there are not enough bids.
	///
	/// **Weight:**
	/// - complexity: `O(BI + BO + C)`
	///   - `BI` being the number of bids in the bidding auction, limited to `MaximumBids`
	///   - `BO` being the number of newly created bonds, limited to `BI`
	///   - `C` being a constant amount of storage reads and writes for coin supply and bonds queue bounds bookkeeping
	/// - DB access:
	///   - 1 write for `coin_supply`
	///   - read and write bids
	///   - write `BO` newly created bonds + read and write bonds queue bounds
	///   - potentially refund up to `BI` bids
	fn contract_supply(coin_supply: Coins, amount: Coins) -> DispatchResult {
		// Checking whether coin supply would underflow.
		let remaining_supply = coin_supply
			.checked_sub(amount)
			.ok_or(Error::<T>::CoinSupplyUnderflow)?;
		if remaining_supply < T::MinimumSupply::get() {
			return Err(DispatchError::from(Error::<T>::CoinSupplyUnderflow));
		}
		// ↑ verify ↑
		let mut bids = Self::bids_transient();
		let mut remaining = amount;
		let mut new_bonds = VecDeque::new();
		// ↓ update ↓
		while remaining > 0 && !bids.is_empty() {
			let mut bid = bids
				.pop()
				.expect("checked whether queue is empty on previous line; qed");
			// the current bid can cover all the remaining contraction
			if bid.payment() >= remaining {
				match bid.remove_coins(remaining) {
					Err(_e) => {
						native::warn!("unable to remove coins from bid --> refunding bid: {:?}", bid);
						Self::refund_bid(&bid);
					}
					Ok(removed_quantity) => {
						new_bonds.push_back(Self::new_bond(bid.account.clone(), removed_quantity));
						// re-add bid with reduced amount
						if bid.quantity > 0 {
							bids.push(bid).map(|to_refund| Self::refund_bid(&to_refund));
						}
						remaining = 0;
					}
				}
			} else {
				let payment = bid.payment();
				let Bid {
					account, quantity, ..
				} = bid;
				new_bonds.push_back(Self::new_bond(account, quantity));
				remaining -= payment;
			}
		}
		debug_assert!(
			remaining <= amount,
			"remaining is never greater than the original amount"
		);
		let burned = amount.saturating_sub(remaining);
		debug_assert!(
			burned <= coin_supply,
			"burned <= amount < coin_supply is checked by coin underflow check in first lines"
		);
		let new_supply = coin_supply.saturating_sub(burned);
		for bond in new_bonds.iter() {
			Self::deposit_event(RawEvent::NewBond(
				bond.account.clone(),
				bond.payout,
				bond.expiration,
			));
		}
		let mut bonds = Self::bonds_transient();
		for bond in new_bonds {
			bonds.push_back(bond);
		}
		<CoinSupply>::put(new_supply);
		Self::deposit_event(RawEvent::ContractedSupply(burned));
		Ok(())
	}

	// ------------------------------------------------------------
	// bonds

	/// Create a new bond for the given `account` with the given `payout`.
	///
	/// Expiration is calculated based on the current `block_number` and the configured
	/// `ExpirationPeriod`.
	fn new_bond(account: T::AccountId, payout: Coins) -> Bond<T::AccountId, T::BlockNumber> {
		let expiration = <system::Module<T>>::block_number() + T::ExpirationPeriod::get();
		Bond {
			account,
			payout,
			expiration,
		}
	}

	/// Create a new transient storage adapter that manages the bonds.
	///
	/// Allows pushing and popping on a ringbuffer without managing the storage details.
	fn bonds_transient() -> BoundedDeque<
		Bond<T::AccountId, T::BlockNumber>,
		<Self as Store>::BondsRange,
		<Self as Store>::Bonds,
		BondIndex,
	> {
		BoundedDeque::<
			Bond<T::AccountId, T::BlockNumber>,
			<Self as Store>::BondsRange,
			<Self as Store>::Bonds,
			BondIndex,
		>::new()
	}

	// ------------------------------------------------------------
	// expand supply

	/// Expand the supply by `amount` by paying out bonds and shares.
	///
	/// Will first pay out bonds and only pay out shares if there are no remaining
	/// bonds.
	///
	/// **Weight:**
	/// - complexity: `O(B + C + H)`
	///   - `B` being the number of bonds, bounded by ringbuffer size, currently `u16::max_value()`
	///   - `C` being a constant amount of storage reads and writes for coin supply and bonds queue bounds bookkeeping
	///   - `H` being the complexity of `hand_out_coins`
	/// - DB access:
	///   - read bonds + read and write bonds queue bounds
	///   - potentially write back 1 bond
	///   - 1 write for `coin_supply` OR read shares and execute `hand_out_coins` which has DB accesses
	fn expand_supply(coin_supply: Coins, amount: Coins) -> DispatchResult {
		// Checking whether the supply will overflow.
		coin_supply
			.checked_add(amount)
			.ok_or(Error::<T>::CoinSupplyOverflow)?;
		// ↑ verify ↑
		let mut remaining = amount;
		let mut bonds = Self::bonds_transient();
		// ↓ update ↓
		while let Some(Bond {
			account,
			payout,
			expiration,
		}) = if remaining > 0 { bonds.pop_front() } else { None }
		{
			// bond has expired --> discard
			if <system::Module<T>>::block_number() >= expiration {
				Self::deposit_event(RawEvent::BondExpired(account, payout));
				continue;
			}
			// bond does not cover the remaining amount --> resolve and continue
			if payout <= remaining {
				// this is safe because we are in the branch where remaining >= payout
				remaining -= payout;
				Self::add_balance(&account, payout);
				Self::deposit_event(RawEvent::BondFulfilled(account, payout));
			}
			// bond covers the remaining amount --> update and finish up
			else {
				// this is safe because we are in the else branch where payout > remaining
				let payout = payout - remaining;
				Self::add_balance(&account, remaining);
				bonds.push_front(Bond {
					account: account.clone(),
					payout,
					expiration,
				});
				Self::deposit_event(RawEvent::BondPartiallyFulfilled(account, payout));
				break;
			}
		}
		// safe to do this late because of the test in the first line of the function
		// safe to substrate remaining because we initialize it with amount and never increase it
		let new_supply = coin_supply + amount - remaining;
		if remaining > 0 {
			// relies on supply being updated in `hand_out_coins`
			Self::hand_out_coins(&Self::shares(), remaining, new_supply)
				.expect("coin supply overflow was checked at the beginning of function; qed");
		} else {
			<CoinSupply>::put(new_supply);
		}
		Self::deposit_event(RawEvent::ExpandedSupply(amount));
		Ok(())
	}

	/// Hand out Coins to shareholders according to their number of shares.
	///
	/// Will hand out more Coins to shareholders at the beginning of the list
	/// if the handout cannot be equal.
	///
	/// **Weight:**
	/// - complexity: `O(S + C)`
	///   - `S` being `shares.len()` (the number of shareholders)
	///   - `C` being a constant amount of storage reads and writes for coin supply
	/// - DB access:
	///   - 1 write for `coin_supply`
	///   - `S` amount of writes
	fn hand_out_coins(shares: &[(T::AccountId, u64)], amount: Coins, coin_supply: Coins) -> DispatchResult {
		// Checking whether the supply will overflow.
		coin_supply
			.checked_add(amount)
			.ok_or(Error::<T>::CoinSupplyOverflow)?;
		// ↑ verify ↑
		let share_supply: u64 = shares.iter().map(|(_a, s)| s).sum();
		let len = shares.len() as u64;
		// No point in giving out less than 1 coin.
		let coins_per_share = max(1, amount / share_supply);
		let pay_extra = coins_per_share * len < amount;
		let mut amount_payed = 0;
		// ↓ update ↓
		for (i, (acc, num_shares)) in shares.iter().enumerate() {
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
			Self::add_balance(&acc, payout);
			amount_payed += payout;
		}
		debug_assert!(
			amount_payed == amount,
			"amount payed out should equal target amount"
		);

		// safe to do this late because of the test in the first line of the function
		let new_supply = coin_supply + amount;
		<CoinSupply>::put(new_supply);
		Ok(())
	}

	// ------------------------------------------------------------
	// on block

	/// Contracts or expands the supply based on conditions.
	///
	/// **Weight:**
	/// Calls `expand_or_contract_on_price` every `AdjustmentFrequency` blocks.
	/// - complexity: `O(P)` with `P` being the complexity of `expand_or_contract_on_price`
	fn on_block_with_price(block: T::BlockNumber, price: Coins) -> DispatchResult {
		// This can be changed to only correct for small or big price swings.
		if block % T::AdjustmentFrequency::get() == 0.into() {
			Self::expand_or_contract_on_price(price)
		} else {
			Ok(())
		}
	}

	/// Expands (if the price is too high) or contracts (if the price is too low) the coin supply.
	///
	/// **Weight:**
	/// - complexity: `O(S + C)`
	///   - `S` being the complexity of executing either `expand_supply` or `contract_supply`
	///   - `C` being a constant amount of storage reads for coin supply
	/// - DB access:
	///   - 1 read for coin_supply
	///   - execute `expand_supply` OR execute `contract_supply` which have DB accesses
	fn expand_or_contract_on_price(price: Coins) -> DispatchResult {
		match price {
			0 => {
				native::error!("coin price is zero!");
				return Err(DispatchError::from(Error::<T>::ZeroPrice));
			}
			price if price > T::BaseUnit::get() => {
				// safe from underflow because `price` is checked to be greater than `BaseUnit`
				let supply = Self::coin_supply();
				let contract_by = Self::calculate_supply_change(price, T::BaseUnit::get(), supply);
				Self::contract_supply(supply, contract_by)?;
			}
			price if price < T::BaseUnit::get() => {
				// safe from underflow because `price` is checked to be less than `BaseUnit`
				let supply = Self::coin_supply();
				let expand_by = Self::calculate_supply_change(T::BaseUnit::get(), price, supply);
				Self::expand_supply(supply, expand_by)?;
			}
			_ => {
				native::info!("coin price is equal to base as is desired --> nothing to do");
			}
		}
		Ok(())
	}

	/// Calculate the amount of supply change from a fraction given as `numerator` and `denominator`.
	fn calculate_supply_change(numerator: u64, denominator: u64, supply: u64) -> u64 {
		type Fix = FixedU128<U64>;
		let fraction = Fix::from_num(numerator) / Fix::from_num(denominator) - Fix::from_num(1);
		fraction.saturating_mul_int(supply as u128).to_num::<u64>()
	}
}
