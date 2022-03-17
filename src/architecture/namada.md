# Namada Overview

Namada is a sovereign proof-of-stake blockchain, using Tendermint BFT consensus,
that enables multi-asset private transfers for any native or non-native asset
using a multi-asset shielded pool derived from the Sapling circuit. Namada features
full IBC protocol support, a natively integrated Ethereum bridge, and simple governance.
A multi-asset shielded transfer wallet is provided in order to facilitate
safe and private user interaction with the protocol.

Over time the set of supported features may be extended to include
features such as fully programmable validity predicates, distributed
key generation & threshold decryption for Ferveo, and more advanced
ZKP circuits. See [M2](./m2.md).

## Raison d'être

Safe and user-friendly multi-asset privacy doesn't yet exist in the blockchain ecosystem. Up until now you
had the choice to build a sovereign chain that reissues assets (e.g. Zcash) or to
build a privacy preserving solution on existing chains (e.g. Tornado Cash on
Ethereum). Both have large trade-offs: in the former case users don't have
assets that they actually want to use and in the latter case the restrictions
of existing platforms mean that users leak a ton of metadata
and the protocols are expensive and clunky to use.

Namada can support any asset on an IBC-compatible blockchain,
and assets sent over a custom Ethereum bridge that will
reduce transfer costs and streamline UX as much as possible.
Once assets are on Namada, shielded transfers will be cheap
and all assets contribute to the same anonymity set.

Namada is also a helpful stepping stone to finalise, test,
and launch a protocol version that is simpler than the full
Anoma protocol but still encapsulates a unified and useful
set of features. There are reasons to expect that it may
make sense for a fractal instance focused exclusively on
shielded transfers to exist in the long-term, as it can
provide throughput and user-friendliness guarantees which
are more difficult to provide with a more general platform.
Namada is designed so that it could evolve into such an instance.

# Features

## Base Ledger

- [Consensus](namada/consensus.md)
- [P2P layer](namada/p2p-layer.md)
- [Execution system](namada/execution-system.md)
- [Governance](namada/governance.md)
- [Proof-of-stake](namada/proof-of-stake.md)

## Cryptography

- [Multi-asset shielded pool circuit](namada/masp.md)

## Interoperability

- [IBC integration](namada/ibc.md)
- [Bidirectional Ethereum bridge](namada/ethereum-bridge.md)

## Economics

- [Shielded pool incentives](namada/masp/shielded-pool-incentives.md)
- [Proof-of-stake reward distribution](namada/proof-of-stake/reward-distribution.md)
- [Cubic slashing](namada/proof-of-stake/cubic-slashing.md)
- [Inflation system](namada/inflation-system.md)
- [Fee system](namada/fee-system.md)

## User interfaces

- [Web-based wallet](namada/web-wallet-interface.md)
- [Web-based block explorer](namada/web-explorer-interface.md)
