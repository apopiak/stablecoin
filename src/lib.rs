//! # Stablecoin example pallet
//!
//! This is a substrate pallet showcasing a sample implementation of a non-collateralized
//! stablecoin based on the [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf).
//!
//! **Note: Example project for illustration, NOT audited and NOT production ready.**
//!
//! ## Dependecies
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

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;

use adapters::{BoundedPriorityQueueTrait, PriorityQueueTransient, RingBufferTrait, RingBufferTransient};
use codec::{Decode, Encode};
use core::cmp::{max, min, Ord, Ordering};
use frame_support::{
	debug::native,
	decl_error, decl_event, decl_module, decl_storage,
	dispatch::{DispatchError, DispatchResult},
	ensure,
	traits::Get,
};
use num_rational::Ratio;
use sp_runtime::{traits::CheckedMul, Fixed64, PerThing, Perbill};
use sp_std::collections::vec_deque::VecDeque;
use system::ensure_signed;

mod utils;
use utils::saturated_mul;

/// Expected price oracle interface. `fetch_price` must return the amount of coins exchanged for the tracked value.
pub trait FetchPrice<Balance> {
	/// Fetch the current price.
	fn fetch_price() -> Balance;
}

/// The type used to represent the account balance for the stablecoin.
pub type Coins = u64;
pub type BondIndex = u16;

/// The pallet's configuration trait.
pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The amount of coins necessary to buy the tracked value. (e.g., 1_100 for 1$)
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
	/// Must be higher than `InitialSupply`.
	type MinimumSupply: Get<Coins>;
}

/// A bond representing (potential) future payout of coins.
///
/// Expires at block `expiration` so it will be discarded if payed out after that block.
///
/// + `account` is the recipient of the bond payout.
/// + `payout` is the amount of Coins payed out.
#[derive(Encode, Decode, Default, Clone, PartialEq, PartialOrd, Eq, Ord)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Bond<AccountId, BlockNumber> {
	account: AccountId,
	payout: Coins,
	expiration: BlockNumber,
}

/// A bid for a bond of the stablecoin at a certain price.
///
/// + `account` is the bidder.
/// + `price` is a percentage of 1 coin.
/// + `quantity` is the amount of coins gained on payout of the corresponding bond.
#[derive(Encode, Decode, Default, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Bid<AccountId> {
	account: AccountId,
	price: Perbill,
	quantity: Coins,
}

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

/// Sort `Bid`s by price
impl<AccountId> Ord for Bid<AccountId> {
	fn cmp(&self, other: &Self) -> Ordering {
		self.price.cmp(&other.price)
	}
}

/// Error returned from `remove_coins` if there is an over- or underflow.
pub enum BidError {
	Overflow,
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

	/// Return the amount of coins to be payed for this bid.
	fn payment(&self) -> Coins {
		// This naive multiplication is fine because Perbill has an implementation tuned for balance types.
		self.price * self.quantity
	}

	/// Remove `coins` amount of coins from the bid, mirroring the changes in quantity
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
		/// All bids below the given price were cancelled for the account.
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
		GenericOverflow,
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

		/// The total amount of coins in circulation.
		CoinSupply get(fn coin_supply): Coins = 0;

		/// The available bonds for contracting supply.
		Bonds get(fn get_bond): map hasher(twox_64_concat) BondIndex => Bond<T::AccountId, T::BlockNumber>;
		/// Start and end index pair used to implement a ringbuffer on top of the `Bonds` map.
		BondsRange get(fn bonds_range): (BondIndex, BondIndex) = (0, 0);

		/// The current bidding queue for bonds.
		BondBids get(fn bond_bids): Vec<Bid<T::AccountId>>;
	}
	add_extra_genesis {
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

// The pallet's dispatchable functions.
decl_module! {
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

		/// Transfer `amount` coins from the sender to the account `to`.
		pub fn transfer(origin, to: T::AccountId, amount: u64) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let sender_balance = Self::get_balance(&sender);
			let updated_from_balance = sender_balance.checked_sub(amount).ok_or(Error::<T>::InsufficientBalance)?;
			let receiver_balance = Self::get_balance(&to);
			let updated_to_balance = receiver_balance.checked_add(amount).ok_or(Error::<T>::BalanceOverflow)?;

			// ↑ verify ↑
			// ↓ update ↓

			// reduce sender's balance
			<Balance<T>>::insert(&sender, updated_from_balance);
			// increase receiver's balance
			<Balance<T>>::insert(&to, updated_to_balance);

			Self::deposit_event(RawEvent::Transfer(sender, to, amount));

			Ok(())
		}

		/// Bid for `quantity` coins at a `price`.
		///
		/// + `price` is a fraction of the desired payout quantity (e.g., 80%).
		/// + Expects a `quantity` of a least `BaseUnit`.
		///
		/// Example: `bid_for_bond(origin, Perbill::from_percent(80), 5 * BaseUnit)` will bid
		/// for a bond with a payout of `5 * BaseUnit` coins for a price of
		/// `0.8 * 5 * BaseUnit = 4 * BaseUnit` coins.
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

		/// Cancel all bids at or below `price` of the sender and refund the coins.
		pub fn cancel_bids_at_or_below(origin, price: Perbill) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// ↑ verify ↑
			// ↓ update ↓
			Self::cancel_bids(|bid| bid.account == who && bid.price <= price);
			Self::deposit_event(RawEvent::CancelledBidsBelow(who, price));

			Ok(())
		}

		/// Cancel all bids belonging to the sender and refund the coins.
		pub fn cancel_all_bids(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// ↑ verify ↑
			// ↓ update ↓
			Self::cancel_bids(|bid| bid.account == who);
			Self::deposit_event(RawEvent::CancelledBids(who));

			Ok(())
		}

		/// Adjust the amount of coins according to the price.
		fn on_initialize(n: T::BlockNumber) {
			let price = T::CoinPrice::fetch_price();
			Self::on_block_with_price(n, price).unwrap_or_else(|e| {
				native::error!("could not adjust supply: {:?}", e);
			});
		}
	}
}

impl<T: Trait> Module<T> {
	// ------------------------------------------------------------
	// balances

	/// Add `amount` coins to the balance for `account`.
	fn add_balance(account: &T::AccountId, amount: Coins) {
		<Balance<T>>::mutate(account, |b: &mut u64| {
			*b = b.saturating_add(amount);
			*b
		});
	}

	/// Remove `amount` coins from the balance of `account`.
	fn remove_balance(account: &T::AccountId, amount: Coins) -> DispatchResult {
		<Balance<T>>::try_mutate(&account, |b: &mut u64| -> DispatchResult {
			*b = b.checked_sub(amount).ok_or(Error::<T>::InsufficientBalance)?;
			Ok(())
		})?;
		Ok(())
	}

	// ------------------------------------------------------------
	// bids

	fn bids_transient() -> Box<dyn BoundedPriorityQueueTrait<Bid<T::AccountId>, MaxLength = T::MaximumBids>> {
		Box::new(PriorityQueueTransient::<
			Bid<T::AccountId>,
			<Self as Store>::BondBids,
			T::MaximumBids,
		>::new())
	}

	/// Add a bid to the queue.
	fn add_bid(bid: Bid<T::AccountId>) {
		Self::bids_transient()
			.push(bid)
			.map(|to_refund| Self::refund_bid(&to_refund));
	}

	/// Refund the coins payed for `bid` to the account that bid.
	fn refund_bid(bid: &Bid<T::AccountId>) {
		Self::add_balance(&bid.account, bid.payment());
		Self::deposit_event(RawEvent::RefundedBid(bid.account.clone(), bid.payment()));
	}

	/// Cancel all bids where `cancel_for` returns true and refund the bidders.
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
			bonds.push(bond);
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
	fn bonds_transient() -> Box<dyn RingBufferTrait<Bond<T::AccountId, T::BlockNumber>>> {
		Box::new(RingBufferTransient::<
			Bond<T::AccountId, T::BlockNumber>,
			<Self as Store>::BondsRange,
			<Self as Store>::Bonds,
			BondIndex,
		>::new())
	}

	// ------------------------------------------------------------
	// expand supply

	/// Expand the supply by `amount` by paying out bonds and shares.
	///
	/// Will first pay out bonds and only pay out shares if there are no remaining
	/// bonds.
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
		}) = if remaining > 0 { bonds.pop() } else { None }
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

	// Will hand out coins to shareholders according to their number of shares.
	// Will hand out more coins to shareholders at the beginning of the list
	// if the handout cannot be equal.
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
	fn on_block_with_price(block: T::BlockNumber, price: Coins) -> DispatchResult {
		// This can be changed to only correct for small or big price swings.
		if block % T::AdjustmentFrequency::get() == 0.into() {
			Self::expand_or_contract_on_price(price)
		} else {
			Ok(())
		}
	}

	/// Expands (if the price is too high) or contracts (if the price is too low) the coin supply.
	fn expand_or_contract_on_price(price: Coins) -> DispatchResult {
		match price {
			0 => {
				native::error!("coin price is zero!");
				return Err(DispatchError::from(Error::<T>::ZeroPrice));
			}
			price if price > T::BaseUnit::get() => {
				// safe from underflow because `price` is checked to be greater than `BaseUnit`
				let fraction =
					Fixed64::from_rational(price as i64, T::BaseUnit::get()) - Fixed64::from_natural(1);
				let supply = Self::coin_supply();
				let contract_by = saturated_mul(fraction, supply);
				Self::contract_supply(supply, contract_by)?;
			}
			price if price < T::BaseUnit::get() => {
				// safe from underflow because `price` is checked to be less than `BaseUnit`
				let fraction =
					Fixed64::from_rational(T::BaseUnit::get() as i64, price) - Fixed64::from_natural(1);
				let supply = Self::coin_supply();
				let expand_by = saturated_mul(fraction, supply);
				Self::expand_supply(supply, expand_by)?;
			}
			_ => {
				native::info!("coin price is equal to base as is desired --> nothing to do");
			}
		}
		Ok(())
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
	type Transient = RingBufferTransient<
		BondT,
		<Stablecoin as Store>::BondsRange,
		<Stablecoin as Store>::Bonds,
		BondIndex,
	>;

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
}
