# Ethereum bridge

The M1 Ethereum bridge system consists of a few parts:

- "IBC-adapter" code on the M1 side
  - Allow M1 validators to vote on the latest Ethereum state roots & log roots (check this) for blocks
  - Allow M1 validity predicates Ethereum state read access through these commitee-voted roots & Merkle proofs
  - Slash validators using commit-reveal, if they commit to a different root. Failing to reveal is considered a liveness fault.
- A set of Ethereum contracts which perform the following functions:
  - Verify Tendermint header updates from M1, and sub-state proofs
  - Allow Ethereum contracts to send messages to M1 by outputting logs in a particular format
  - Allow Ethereum contracts to receive messages from M1 by verifying message commitments in the M1 state Merkle tree
  - Handle ICS20-style token transfer messages appropriately with escrow & unescrow on the Ethereum side
  - Allow for message batching

This basic bridge architecture should provide for almost-M1 consensus security for the bridge and free Ethereum state reads on M1, plus bidirectional message passing with reasonably low gas costs on the Ethereum side.

Resources which may be helpful:
- [Gravity Bridge Solidity contracts](https://github.com/Gravity-Bridge/Gravity-Bridge/tree/main/solidity)
- [ICS20](https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer)
- [Rainbow Bridge contracts](https://github.com/aurora-is-near/rainbow-bridge/tree/master/contracts)

One caveat is that we should check the cost of Tendermint header verification on Ethereum; it can be amortised across packets but this still may be quite high. If it is too high we could try to use a threshold key with Ferveo instead.
