// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

/// A runtime module template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references

/// For more guidance on Substrate modules, see the example module
/// https://github.com/paritytech/substrate/blob/master/srml/example/src/lib.rs

#[cfg(test)]
mod tests;

// We have to import a few things
use rstd::{prelude::*};
use primitives::crypto::KeyTypeId;
use support::{decl_module, decl_storage, decl_event, dispatch,
  debug, storage::IterableStorageMap, traits::Get};
use system::offchain::{SubmitUnsignedTransaction};
use system::{ensure_none};
use simple_json::{self, json::JsonValue};
use runtime_io::{self, misc::print_utf8 as print_bytes};
#[cfg(not(feature = "std"))]
use num_traits::float::FloatCore;
use codec::Encode;
use sp_runtime::{
  offchain::http,
  transaction_validity::{
    TransactionValidity, TransactionLongevity, ValidTransaction, InvalidTransaction
  }
};

type Result<T> = core::result::Result<T, &'static str>;

/// Our local KeyType.
///
/// For security reasons the offchain worker doesn't have direct access to the keys
/// but only to app-specific subkeys, which are defined and grouped by their `KeyTypeId`.
pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"ofpf");

// REVIEW-CHECK: is it necessary to wrap-around storage vector at `MAX_VEC_LEN`?
pub const MAX_VEC_LEN: usize = 1000;

pub mod crypto {
  pub use super::KEY_TYPE;
  use sp_runtime::app_crypto::{app_crypto, sr25519};
  app_crypto!(sr25519, KEY_TYPE);
}

pub const FETCHED_CRYPTOS: [(&[u8], &[u8], &[u8]); 6] = [
  (b"BTC", b"coincap",
    b"https://api.coincap.io/v2/assets/bitcoin"),
  (b"BTC", b"cryptocompare",
    b"https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD"),
  (b"ETH", b"coincap",
   b"https://api.coincap.io/v2/assets/ethereum"),
  (b"ETH", b"cryptocompare",
    b"https://min-api.cryptocompare.com/data/price?fsym=ETH&tsyms=USD"),
  (b"DAI", b"coincap",
    b"https://api.coincap.io/v2/assets/dai"),
  (b"DAI", b"cryptocompare",
    b"https://min-api.cryptocompare.com/data/price?fsym=DAI&tsyms=USD"),
];

pub trait FetchPriceFor {
  fn get_price_for(symbol: &[u8]) -> Option<u64>;
}

impl<T: Trait> FetchPriceFor for Module<T> {
  fn get_price_for(symbol: &[u8]) -> Option<u64> {
    let (_, price) = <TokenAggPPMap<T>>::get(symbol);
    if price == Default::default() {
      return None;
    }
    price.into()
  }
}

/// The module's configuration trait.
pub trait Trait: timestamp::Trait + system::Trait {
  /// The overarching event type.
  type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
  type Call: From<Call<Self>>;
  type SubmitUnsignedTransaction: SubmitUnsignedTransaction<Self, <Self as Trait>::Call>;

  // Wait period between automated fetches. Set to 0 disable this feature.
  //   Then you need to manucally kickoff pricefetch
  type BlockFetchDur: Get<Self::BlockNumber>;
}

type StrVecBytes = Vec<u8>;
// Q: Is it possible to do:
// type PricePoint = (Moment, u64);
//
// So inside Event enum, I can do:
// ```
// pub enum Event<T> where Moment = <T as timestamp::Trait>::Moment {
//   FetchedPrice(StrVecBytes, StrVecBytes, PricePoint),
//   ...

decl_event!(
  pub enum Event<T> where Moment = <T as timestamp::Trait>::Moment {
    FetchedPrice(StrVecBytes, StrVecBytes, Moment, u64),
    AggregatedPrice(StrVecBytes, Moment, u64),
  }
);

// This module's storage items.
decl_storage! {
  trait Store for Module<T: Trait> as PriceFetch {
    // mapping of token sym -> (timestamp, price)
    //   price has been inflated by 10,000, and in USD.
    //   When used, it should be divided by 10,000.
    // Using linked map for easy traversal from offchain worker or UI
    TokenSrcPPMap: map hasher(blake2_128_concat) StrVecBytes => Vec<(T::Moment, u64)>;

    // storage about aggregated price points (calculated with our logic)
    TokenAggPPMap: map hasher(blake2_128_concat) StrVecBytes => (T::Moment, u64);
  }
}

// The module's dispatchable functions.
decl_module! {
  /// The module declaration.
  pub struct Module<T: Trait> for enum Call where origin: T::Origin {
    // Initializing events
    // this is needed only if you are using events in your module
    fn deposit_event() = default;

    pub fn record_price(
      origin,
      _block: T::BlockNumber,
      crypto_info: (StrVecBytes, StrVecBytes, StrVecBytes),
      price: u64
    ) -> dispatch::DispatchResult {
      // Ensuring this is an unsigned tx
      ensure_none(origin)?;

      let (sym, remote_src) = (crypto_info.0, crypto_info.1);
      let now = <timestamp::Module<T>>::get();

      // Debug printout
      debug::info!("record_price: {:?}, {:?}, {:?}",
        core::str::from_utf8(&sym).map_err(|_| "`sym` conversion error")?,
        core::str::from_utf8(&remote_src).map_err(|_| "`remote_src` conversion error")?,
        price
      );

      <TokenSrcPPMap<T>>::mutate(&sym, |pp_vec| pp_vec.push((now, price)));

      // Spit out an event and Add to storage
      Self::deposit_event(RawEvent::FetchedPrice(sym, remote_src, now, price));

      Ok(())
    }

    pub fn record_agg_pp(
      origin,
      _block: T::BlockNumber,
      sym: StrVecBytes,
      price: u64
    ) -> dispatch::DispatchResult {
      // Debug printout
      debug::info!("record_agg_pp: {}: {:?}",
        core::str::from_utf8(&sym).map_err(|_| "`sym` string conversion error")?,
        price
      );

      // Ensuring this is an unsigned tx
      ensure_none(origin)?;

      let now = <timestamp::Module<T>>::get();

      // Record in the storage
      let price_pt = (now.clone(), price.clone());
      <TokenAggPPMap<T>>::insert(&sym, price_pt);

      // Remove relevant storage items
      <TokenSrcPPMap<T>>::remove(&sym);

      // Spit the event
      Self::deposit_event(RawEvent::AggregatedPrice(
        sym.clone(), now.clone(), price.clone()));

      Ok(())
    }

    fn offchain_worker(block: T::BlockNumber) {
      let duration = T::BlockFetchDur::get();

      // Type I task: fetch price
      if duration > 0.into() && block % duration == 0.into() {
        for (sym, remote_src, remote_url) in FETCHED_CRYPTOS.iter() {
          if let Err(e) = Self::fetch_price(block, *sym, *remote_src, *remote_url) {
            debug::error!("Error fetching: {:?}, {:?}: {:?}",
              core::str::from_utf8(sym).unwrap(),
              core::str::from_utf8(remote_src).unwrap(),
              e);
          }
        }
      }

      // Type II task: aggregate price
      TokenSrcPPMap::<T>::iter()
        // filter those to be updated
        .filter(|(_, vec)| vec.len() > 0)
        .for_each(|(sym, _)| {
          if let Err(e) = Self::aggregate_pp(block, &sym) {
            debug::error!("Error aggregating price of {:?}: {:?}",
              core::str::from_utf8(&sym).unwrap(), e);
          }
        });
    } // end of `fn offchain_worker()`

  }
}

impl<T: Trait> Module<T> {
  fn fetch_json<'a>(remote_url: &'a [u8]) -> Result<JsonValue> {
    let remote_url_str = core::str::from_utf8(remote_url)
      .map_err(|_| "Error in converting remote_url to string")?;

    let pending = http::Request::get(remote_url_str).send()
      .map_err(|_| "Error in sending http GET request")?;

    let response = pending.wait()
      .map_err(|_| "Error in waiting http response back")?;

    if response.code != 200 {
      debug::warn!("Unexpected status code: {}", response.code);
      return Err("Non-200 status code returned from http request");
    }

    let json_result: Vec<u8> = response.body().collect::<Vec<u8>>();

    // Print out the whole JSON blob
    print_bytes(&json_result);

    let json_val: JsonValue = simple_json::parse_json(
      &core::str::from_utf8(&json_result).map_err(|_| "JSON result cannot convert to string")?)
      .map_err(|_| "JSON parsing error")?;

    Ok(json_val)
  }

  fn fetch_price<'a>(
    block: T::BlockNumber,
    sym: &'a [u8],
    remote_src: &'a [u8],
    remote_url: &'a [u8]
  ) -> Result<()> {
    debug::info!("fetch price: {:?}:{:?}",
      core::str::from_utf8(sym).unwrap(),
      core::str::from_utf8(remote_src).unwrap()
    );

    let json = Self::fetch_json(remote_url)?;

    let price = match remote_src {
      src if src == b"coincap" => Self::fetch_price_from_coincap(json)
        .map_err(|_| "fetch_price_from_coincap error"),
      src if src == b"cryptocompare" => Self::fetch_price_from_cryptocompare(json)
        .map_err(|_| "fetch_price_from_cryptocompare error"),
      _ => Err("Unknown remote source"),
    }?;

    let call = Call::record_price(
      block,
      (sym.to_vec(), remote_src.to_vec(), remote_url.to_vec()),
      price
    );

    // Unsigned tx
    T::SubmitUnsignedTransaction::submit_unsigned(call)
      .map_err(|_| "fetch_price: submit_unsigned(call) error")

    // Signed tx
    // let local_accts = T::SubmitTransaction::find_local_keys(None);
    // let (local_acct, local_key) = local_accts[0];
    // debug::info!("acct: {:?}", local_acct);
    // T::SignAndSubmitTransaction::sign_and_submit(call, local_key);

    // T::SubmitSignedTransaction::submit_signed(call);
  }

  fn vecchars_to_vecbytes<I: IntoIterator<Item = char> + Clone>(it: &I) -> Vec<u8> {
    it.clone().into_iter().map(|c| c as u8).collect::<_>()
  }

  fn fetch_price_from_cryptocompare(json_val: JsonValue) -> Result<u64> {
    // Expected JSON shape:
    //   r#"{"USD": 7064.16}"#;
    let val_f64: f64 = json_val.get_object()[0].1.get_number_f64();
    Ok((val_f64 * 10000.).round() as u64)
  }

  fn fetch_price_from_coincap(json_val: JsonValue) -> Result<u64> {
    // Expected JSON shape:
    //   r#"{"data":{"priceUsd":"8172.2628346190447316"}}"#;

    const PRICE_KEY: &[u8] = b"priceUsd";
    let data = json_val.get_object()[0].1.get_object();

    let (_, v) = data.iter()
      .filter(|(k, _)| PRICE_KEY.to_vec() == Self::vecchars_to_vecbytes(k))
      .nth(0)
      .ok_or("fetch_price_from_coincap: JSON does not conform to expectation")?;

    // `val` contains the price, such as "222.333" in bytes form
    let val_u8: Vec<u8> = v.get_bytes();

    // Convert to number
    let val_f64: f64 = core::str::from_utf8(&val_u8)
      .map_err(|_| "fetch_price_from_coincap: val_f64 convert to string error")?
      .parse::<f64>()
      .map_err(|_| "fetch_price_from_coincap: val_u8 parsing to f64 error")?;
    Ok((val_f64 * 10000.).round() as u64)
  }

  fn aggregate_pp<'a>(block: T::BlockNumber, sym: &'a [u8])
    -> Result<()> {
    let ts_pp_vec = <TokenSrcPPMap<T>>::get(sym);
    let price_sum: u64 = ts_pp_vec.iter().fold(0, |mem, pp| mem + pp.1);

    // Avoiding floating-point arithmetic & do integer division
    let price_avg: u64 = price_sum / (ts_pp_vec.len() as u64);

    // submit onchain call for aggregating the price
    let call = Call::record_agg_pp(block, sym.to_vec(), price_avg);

    // Unsigned tx
    T::SubmitUnsignedTransaction::submit_unsigned(call)
      .map_err(|_| "aggregate_pp: submit_signed(call) error")

    // Signed tx
    // T::SubmitSignedTransaction::submit_signed(call);
    // Ok(())
  }
}

#[allow(deprecated)]
impl<T: Trait> support::unsigned::ValidateUnsigned for Module<T> {
  type Call = Call<T>;

  #[allow(deprecated)]
  fn validate_unsigned(call: &Self::Call) -> TransactionValidity {

    match call {
      Call::record_price(block, (sym, remote_src, ..), price) => Ok(ValidTransaction {
        priority: 0,
        requires: vec![],
        provides: vec![(block, sym, remote_src, price).encode()],
        longevity: TransactionLongevity::max_value(),
        propagate: true,
      }),
      Call::record_agg_pp(block, sym, price) => Ok(ValidTransaction {
        priority: 0,
        requires: vec![],
        provides: vec![(block, sym, price).encode()],
        longevity: TransactionLongevity::max_value(),
        propagate: true,
      }),
      _ => InvalidTransaction::Call.into()
    }
  }
}
