# Ethereum bridge

The M1 Ethereum bridge exists to mint wrapped ETH tokens on M1 which naturally
can be redeemed on Ethereum at a later time. It does not allow the minting
of XAN tokens (Anoma's native tokens) on Ethereum.

The M1 Ethereum bridge system consists of:
* Ethereum state inclusion onto M1.
* A set of validity predicates on M1 which roughly implements [ICS20](https://docs.cosmos.network/v0.42/modules/ibc/) fungible token transfers.
* A set of Ethereum smart contracts.

This basic bridge architecture should provide for almost-M1 consensus 
security for the bridge and free Ethereum state reads on M1, plus 
bidirectional message passing with reasonably low gas costs on the 
Ethereum side.

## Ethereum State Inclusion
We want to store data identifying which Ethereum blocks have been seen by
at least 2/3 of the staking validators in the blockchain storage. These will be Ethereum
block headers, along with messages from the Ethereum smart contracts relevant
to the bridge. We may also want to include Merkle proofs of inclusion of 
these messages in the relevant blocks. We might also implement policies to
prune old/irrelevant data or do checkpointing.

Each piece of block data should have a list of the validators that have seen
this block and the current amount of stake associated with it. This
will need to be appropriately adjusted across epoch boundaries. However, 
once a block has been seen by 2/3 of the staking validators, it is locked into a 
`seen` state. Thus, even if after an epoch that block has no longer been
reported as seen by 2/3 of the new staking validators set, it is still
considered as `seen`. 

To make this easy, we take the approach of always overwriting the state with
the new state rather than applying state diffs. The storage keys involved
are:
```
/eth_block/$block_hash/header : Vec<u8>
/eth_block/$block_hash/messages : Vec<Vec<u8>>
/eth_block/$block_hash/seen_by : Vec<Address>
/eth_block/$block_hash/voting_power: u64
/eth_block/$block_hash/seen: bool
/eth_block/$block_hash/? : [u8; 32]
# not yet decided
/eth_block/$block_hash/merkle_proofs : Vec<Vec<u8>>
```

For every M1 block proposal, the vote of a validator should include 
the headers, hash, & smart contract messages (possibly with Merkle proofs)
of the Ethereum blocks they have seen via their full node such that:

1. Has not been marked as `seen` by M1
2. The storage value `/eth_block/$block_hash/seen_by` does not include their
   address.
3. Is a descendant of a block marked `seen`

After an M1 block is committed, the next block proposer receives the 
aggregate of the vote extensions. From that, they should craft the proposed
state change of the above form. They subsequently include a tx to that end 
in their block proposal. This aggregated state change needs to be validated
by at least 2/3 of the staking validators as usual.

## M1 Validity Predicates

### Minting wrapped ETH tokens on M1
M1 requires a validity predicate with dedicated storage to mint wrapped
ETH. This validity predicate should be called on every inclusion of Ethereum
state above. Its storage contains a queue of messages from the Ethereum
bridge contracts. It also mints corresponding assets on M1, where the asset denomination corresponds to 
`{token address on ethereum} || {minimum number of confirmations}`.

The minimum number of confirmations indicated in the outgoing Ethereum message 
(maybe defaulting to 25 or 50 if unspecified) specifies the minimum number of 
confirmations in block depth that must be reached before the assets will be
minted on M1. This is the purpose of the message queue for this validity
predicate.

This queue contains instances of the following struct
```rust
struct MintEthToken {
    // token address on Ethereum
    ethereum_address: Address,
    // the address on M1 receiving the tokens
    receiver: Address,
    // the amount of ETH token to mint
    amount: Amount,
    // minimum number of confirmations needed for mints
    min_confirmations: u8,
    // height of the block at which the message appeared
    height: u64,
    // the hash & height of the last descendant block marked as `seen`
    latest_descendant: ([u8; 32], u64)
}

impl MintEthToken {
    /// Update the hash and height of the block `B` marked as `seen` in M1
    /// storage such that 
    ///   1. `B` is a descendant of the block containing the original message
    ///   2. `B` has the maximum height of all blocks satisfying 1.
    fn update_latest_descendant(&mut self, hash: [u8; 32], height: u64) {
        if height > self.latest_descendant.1 {
            self.latest_descendant = (hash, height);    
        }
    }
    
    /// Check if the number of confirmations for the block containing
    /// the original message exceeds the minimum number required to 
    /// consider the message confirmed.
    fn is_confirmed(&self) -> bool {
        self.latest_descendant.1 - self.height >= self.min_confirmations
    }
}
```
Every time this validity predicate is called, it must perform the following
actions:
 1. Add new messages from the input into the queue
 2. For each message in the queue, update its number of confirmations. This
    can be done by finding Ethereum block headers marked as `seen` in the new
    storage data (the input from finalizing the block, it isn't necessary to 
    access M1 storage) that are descendants of the `latest_descendant` field.
 3. For each message that is confirmed, transfer the appropriate tokens to 
    the address in the `receiver` field.

Note that this means that a transfer initiated on Ethereum will automatically
be seen and acted upon by M1. The appropriate protocol transactions to 
credit tokens to the given user will be included on chain free of charge
and requires no additional actions from the end user.

### Redeeming ETH by burning tokens on M1

For redeeming wrapped ETH, the M1 side will need another validity predicate
that is called only when the appropriate user tx lands on chain. This validity
predicate will simply burn the tokens.

Once, this transaction is approved, it is incumbent on the end user to 
request an appropriate light client proof of the transaction. This light
client proof must be submitted to the appropriate Ethereum smart contract
by the user to redeem their ETH. This also means all Ethereum gas costs
are the responsibility of the end user.

Producing light client proofs for transactions is available directly in
tendermint via the [`tx_search` rpc endpoint](https://docs.tendermint.com/master/rpc/#/Info/tx_search).
The M1 client should use this to provide a convenient means for end users
to request the proofs for their burned tokens.

## Ethereum Smart Contracts
The set of Ethereum contracts should perform the following functions:
 - Verify Tendermint light client proofs from M1 so that M1 messages can
   be submitted to the contract.
 - Emit log messages readable by M1
 - Handle ICS20-style token transfer messages appropriately with escrow & 
   unescrow on the Ethereum side
 - Allow for message batching

Furthermore, the Ethereum contracts will whitelist ETTH and tokens that
flow across the bridge as well as ensure limits on transfer volume per epoch.
 

## Resources which may be helpful:
- [Gravity Bridge Solidity contracts](https://github.com/Gravity-Bridge/Gravity-Bridge/tree/main/solidity)
- [ICS20](https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer)
- [Rainbow Bridge contracts](https://github.com/aurora-is-near/rainbow-bridge/tree/master/contracts)
- [IBC in Solidity](https://github.com/hyperledger-labs/yui-ibc-solidity)

One caveat is that we should check the cost of Tendermint header verification on Ethereum; it can be amortised across packets but this still may be quite high. If it is too high we could try to use a threshold key with Ferveo instead.

Operational notes:
1. We should bundle the Ethereum full node with the `m1` daemon executable.
