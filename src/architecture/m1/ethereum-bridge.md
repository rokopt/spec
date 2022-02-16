# Ethereum bridge

The M1 Ethereum bridge system consists of a few parts:

1. "IBC-adapter" code on the M1 side
  1. Ethereum state inclusion, which works as follows:
    1. All Anoma (m1) validators run Ethereum full nodes
    1. Every block, in their vote (we might need ABCI++ for this), validators include what they think the latest Ethereum block hash, header & height (or multiple, but ones they have not yet voted on)
    1. Once 2/3 of validators agree on a particular hash & height that the light client also thinks is valid (note that there can be multiple hashes for the same height, forks are allowed, but a 2/3 consensus is required), it is written to state in a way accessible to validity predicates. We could require the validators to commit-reveal as a bit of a Schelling point game.
  1. A particular validity predicate on M1 which roughly implements ICS20:
    1. Reads incoming messages from a particular contract (the bridge contract) on Ethereum for asset transfers
    1. Mints corresponding assets on M1, where the asset denom corresponds to `{token address on eth} || {min number of confirmations}`, with the minimum number of confirmations indicated in the outgoing ethereum message (maybe defaulting to 25 or 50 in the UI or sth), and where the minimum number of confirmations in block depth must be reached before the assets will be minted on M1.
1. A set of Ethereum contracts which perform the following functions:
  1. Verify Tendermint header updates from M1, and sub-state proofs
  1. Allow Ethereum contracts to send messages to M1 by outputting logs in a particular format
  1. Allow Ethereum contracts to receive messages from M1 by verifying message commitments in the M1 state Merkle tree
  1. Handle ICS20-style token transfer messages appropriately with escrow & unescrow on the Ethereum side
  1. Allow for message batching

This basic bridge architecture should provide for almost-M1 consensus security for the bridge and free Ethereum state reads on M1, plus bidirectional message passing with reasonably low gas costs on the Ethereum side.

Resources which may be helpful:
- [Gravity Bridge Solidity contracts](https://github.com/Gravity-Bridge/Gravity-Bridge/tree/main/solidity)
- [ICS20](https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer)
- [Rainbow Bridge contracts](https://github.com/aurora-is-near/rainbow-bridge/tree/master/contracts)
- [IBC in Solidity](https://github.com/hyperledger-labs/yui-ibc-solidity)

One caveat is that we should check the cost of Tendermint header verification on Ethereum; it can be amortised across packets but this still may be quite high. If it is too high we could try to use a threshold key with Ferveo instead.

Operational notes:
1. We should bundle the Ethereum full node with the `m1` daemon executable.
