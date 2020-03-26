# How to Develop a Stablecoin with Substrate

This blogpost will cover how I built a non-collateralized stablecoin with [Substrate](https://substrate.dev/).

We will cover ... TODO: topics

## Introduction to Stablecoins
A stablecoin is a cryptocurrency aiming at price stability. They aim to address the problem where cryptocurrencies are not usable for day-to-day transactions because of their excessive volatility. Following the [CENTRE Whitepaper](https://www.centre.io/pdfs/centre-whitepaper.pdf) we can categorize stablecoins into 3+1 categories:

1. **Fiat-collateralized**: Fiat assets in reserves collateralize tokens and thus provide price stability by pegging token value to reserved fiat value. Examples for this is Tether (USDT), True USD (TUSD) and USD Coin (USDC) as well as many others.
2. **Crypto-collateralized**: Crypto assets in reserves collateralize tokens and provide price stability pegged to the value of those reserved crypto assets. Examples of this Dai (DAI) by MakerDAO and the Acala Network (aUSD).
3. **Algorithmic non-collateralized**: Software economic models aim to provide price stability without relying on underlying collateralized assets. An example of this is the now defunct Basis.
4. **Hybrid**: A blend of the three basic approaches above.

The stablecoin developed here is an algorithmic non-collateralized stablecoin mostly following the [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf). It will thus regulate its own supply based on its price provided by a price oracle. Two other assets called Bonds and Shares are used to achieve that supply adjustment.

TODO: write about contrast to collateralized stablecoins.

## Components of a Stablecoin Built with Substrate
In order to build a stablecoin with Substrate we will create a re-usable pallet that encapsulates the core logic. We will then instantiate it in the runtime of an example node and integrate it with other pallets that will provide the price oracle.

### Stablecoin Pallet
The pallet contains the implementation of the stablecoin according to the behavior outlined in the [Basis Whitepaper](https://www.basis.io/basis_whitepaper_en.pdf).

### Example Node
The example node combines the stablecoin pallet with the price oracles and allows testing and interaction.

### Price Oracle Pallets
The price oracle consists of a simple pallet storing the current price as well as an offchain worker pallet collecting prices from outside of the substrate chain.

## Summary