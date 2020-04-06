#![cfg_attr(not(feature = "std"), no_std)]

/// A price feed pallet

use frame_support::{decl_module, decl_storage, decl_event, decl_error, dispatch, debug::native};
use system::ensure_signed;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

use stablecoin::FetchPrice;
use price_fetch::FetchPriceFor;

impl<T: Trait> FetchPrice<u64> for Module<T> {
	fn fetch_price() -> u64 {
		Self::get_price()
	}
}

/// The pallet's configuration trait.
pub trait Trait: system::Trait {
	// Add other types and constants required to configure this pallet.

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	type OffchainPrice: FetchPriceFor;
}

// This pallet's storage items.
decl_storage! {
	trait Store for Module<T: Trait> as Price {
		Price get(fn get_price): u64 = 1_000_000;
	}
}

// The pallet's events
decl_event!(
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId {
		NewPrice(u64),

		DummyEvent(AccountId),
	}
);

// The pallet's errors
decl_error! {
	pub enum Error for Module<T: Trait> {
		NoOffchainPrice
	}
}

// The pallet's dispatchable functions.
decl_module! {
	/// The module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		pub fn set_price(origin, new_price: u64) -> dispatch::DispatchResult {
			let _who = ensure_signed(origin)?;
		
			Price::put(new_price);
		
			Self::deposit_event(RawEvent::NewPrice(new_price));
		
			Ok(())
		}

		pub fn get_offchain_price(origin) -> dispatch::DispatchResult {
			let _who = ensure_signed(origin)?;
			let price = T::OffchainPrice::get_price_for(b"ETH").ok_or(Error::<T>::NoOffchainPrice)?;

			native::info!("ETH offchain price: {}", price);
			Price::put(price);

			Self::deposit_event(RawEvent::NewPrice(price));

			Ok(())
		}
	}
}
