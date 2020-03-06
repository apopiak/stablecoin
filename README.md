# Stablecoin example pallet

This is a substrate pallet showcasing a sample implementation of a non-collateralized stablecoin based on the [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf).

**Note: Example project for illustration, NOT audited and NOT production ready.**

## Purpose

This pallet is a sample showing how to implement an algorithmic (non-collateralized) stablecoin.

## Dependencies

### Traits

This pallet does not depend on any externally defined traits. It will probably be moved to an external definition of the `FetchPrice` trait soon.

### Pallets

This pallet depends on an external implementation of its `FetchPrice` trait - for example by an offchain worker - to act as a price oracle.

## Installation

### Runtime `Cargo.toml`

To add this pallet to your runtime, simply include the following in your runtime's `Cargo.toml` file:

```TOML
[dependencies.pallet-stablecoin]
default_features = false
git = 'https://github.com/apopiak/pallet-stablecoin.git'
```

and update your runtime's `std` feature to include this pallet's `std` feature:

```TOML
std = [
    # --snip--
    'pallet_stablecoin/std',
]
```

### Runtime `lib.rs`

Here is an example imlementation of its trait:

```rust
use pallet_stablecoin::Coins;

parameter_types! {
    pub const ExpirationPeriod: BlockNumber = 5 * 365 * DAYS; // 5 years = 5 * 365 * DAYS
    pub const MaximumBids: usize = 1_000;
    pub const AdjustmentFrequency: BlockNumber = 1 * MINUTES; // 1 minute = 60000 / MILLISECS_PER_BLOCK
    pub const BaseUnit: Coins = 1_000_000;
    pub const InitialSupply: Coins = 1000 * BaseUnit::get();
    pub const MinimumSupply: Coins = BaseUnit::get();
}

impl pallet_stablecoin::Trait for Runtime {
    type Event = Event;
    
    type CoinPrice = some_price_oracle::Module<Runtime>;
    type ExpirationPeriod = ExpirationPeriod;
    type MaximumBids = MaximumBids;
    type AdjustmentFrequency = AdjustmentFrequency;
    type BaseUnit = BaseUnit;
    type InitialSupply = InitialSupply;
    type MinimumSupply = MinimumSupply;
}
```

and include it in your `construct_runtime!` macro:

```rust
Stablecoin: pallet_stablecoin::{Module, Call, Storage, Event<T>},
```

### Genesis Configuration

This template pallet does not have any genesis configuration.

TODO: Allow initialization at genesis time.

## Implementation

The implementation follows the [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf). (It also takes some inspiration from [this unfinished Solidity implementation](https://github.com/alisyakainth/stablecoin).)

+ `Basis` tokens are called `Coins` and represent an ERC20-like token that will be stabilized by increasing and decreasing supply.
+ `Bond tokens` are called `Bonds` and allow in- and decreasing the supply. They represent a promise for n `Coins` in the future (under certain conditions).
+ `Share tokens` are called `Shares` and have a supply fixed at initialization time of the stablecoin. If there are not enough `Bonds` to increase coin supply, `Coins` are distributed to the accounts holding shares.

The `ExpirationPeriod` is configurable and measured in blocks (type `BlockNumber`).

The continuous bidding auction for bonds is implemented as a bounded priority queue to reduce storage costs. The paper does not specify whether it should or should not be bounded.

## Reference Docs

You can view the reference docs for this pallet by running:

```
cargo doc --open
```
