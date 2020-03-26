# {{crate}}
Current version: {{version}}

{{readme}}

### Implementation

The implementation follows the [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf). (It also takes some inspiration from [this unfinished Solidity implementation](https://github.com/alisyakainth/stablecoin).)

+ `Basis` tokens are called `Coins` and represent an ERC20-like token that will be stabilized by increasing and decreasing supply.
+ `Bond tokens` are called `Bonds` and allow in- and decreasing the supply. They represent a promise for n `Coins` in the future (under certain conditions).
+ `Share tokens` are called `Shares` and have a supply fixed at initialization time of the stablecoin. If there are not enough `Bonds` to increase coin supply, `Coins` are distributed to the accounts holding shares.

The `ExpirationPeriod` is configurable and measured in blocks (type `BlockNumber`).

The continuous bidding auction for bonds is implemented as a bounded priority queue to reduce storage costs. The paper does not specify whether it should or should not be bounded.

### Reference Docs

You can view the reference docs for this pallet by running:

```
cargo doc --open
```
