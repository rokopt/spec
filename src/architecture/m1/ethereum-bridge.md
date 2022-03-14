# Ethereum bridge

The M1 Ethereum bridge exists to mint wrapped ETH tokens on M1 which naturally
can be redeemed on Ethereum at a later time. Furthermore, it allows the
minting of wrapped tokens on Ethereum backed by escrowed assets on M1.

The M1 Ethereum bridge system consists of:
* Ethereum state inclusion onto M1.
* A set of validity predicates on M1 which roughly implements [ICS20](https://docs.cosmos.network/v0.42/modules/ibc/) fungible token transfers.
* A set of Ethereum smart contracts.
* An M1 bridge process

This basic bridge architecture should provide for almost-M1 consensus 
security for the bridge and free Ethereum state reads on M1, plus 
bidirectional message passing with reasonably low gas costs on the 
Ethereum side.

## Security
On M1, the validators are full nodes of Ethereum and their stake is also
accounting for security of the bridge. If they carry out a forking attack
on M1 to steal locked tokens of Ethereum their stake will be slashed on M1.
On the Ethereum side, we will add a limit to the amount of ETH that can be
locked to limit the damage a forking attack on M1 can do. To make an attack
more cumbersome we will also add a limit on how fast wrapped ETH can be
redeemed. This will not add more security, but rather make the attack more
inconvenient. 

## Ethereum State Inclusion 
We want to store data identifying which Ethereum blocks have been seen 
and validated by at least 2/3 of the staking validators in the blockchain storage. 
The data stored from each Ethereum block will be:
 * The block header
 * The block hash
 * Messages from the Ethereum smart contracts relevant
    to the bridge.
We may also we to include Merkle proofs of inclusion of 
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
3. Is a descendant of a block they have seen (even if it is not marked `seen`)

After an M1 block is committed, the next block proposer receives the 
aggregate of the vote extensions. From that, they should craft the proposed
state change of the above form. They subsequently include a tx to that end 
in their block proposal. This aggregated state change needs to be validated
by at least 2/3 of the staking validators as usual.

## M1 Validity Predicates

### Reacting to changes on Ethereum
M1 requires a validity predicates with dedicated storage to respond to changes on Ethereum that
have been confirmed by M1 validators. This includes 
 - minting wrapped ETH,
 - redeeming wrapped M1 tokens on Ethereum,
 - rewarding the Designated Relayer for submitting validator set changes to
   the appropriate Ethereum smart contract (more on this [here](#m1-bridge-relayers)).

This validity predicate should be called on every inclusion of Ethereum
state above. Its storage contains a queue of messages from the Ethereum
bridge contracts. It can mint corresponding assets on M1, where the asset denomination corresponds to 
`{token address on ethereum} || {minimum number of confirmations}` as well
as transfer tokens between accounts. 

The minimum number of confirmations indicated in the outgoing Ethereum message 
(maybe defaulting to 25 or 50 if unspecified) specifies the minimum number of 
confirmations in block depth that must be reached before the assets will be
minted on M1. This is the purpose of the message queue for this validity
predicate.

This queue contains instances of the `MintEthToken` struct below.
```rust
/// The token address for wrapped ETH tokens
const WRAPPED_ETH_ADDRESS: Address = ...;
const GOVERNANCE_TREASURY_ADDRESS: Address = ...;
pub struct WrappedETHAddress;
pub struct M1TokenAddress(Address);

pub trait MintingAddress {
    fn get_address(&self) -> &Address;
}

impl MintingAddress for WrappedETHAddress {
    fn get_address(&self) -> &Address {
        &WRAPPED_ETH_ADDRESS
    }
}

impl MintingAddress for M1TokenAddress {
    fn get_address(&self) -> &Address {
        &self.0
    }
}

/// Generic struct for transferring value from Ethereum
struct TransferFromEthereum<Token: MintingAddress> {
    /// token address on Ethereum
    ethereum_address: Address,
    /// the address on M1 receiving the tokens
    receiver: Address,
    /// The M1 token that will be minted
    token: Token, 
    /// the amount of ETH token to mint
    amount: Amount,
    /// minimum number of confirmations needed for mints
    min_confirmations: u8,
    /// height of the block at which the message appeared
    height: u64,
    /// the hash & height of the last descendant block marked as `seen`
    latest_descendant: ([u8; 32], u64)
}

impl TransferFromEthereum {
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
    pub fn is_confirmed(&self) -> bool {
        self.latest_descendant.1 - self.height >= self.min_confirmations
    }
}

/// Struct for minting wrapped ETH tokens on M1
pub type MintEthToken = TransferFromEthereum<WrappedETHAddress>;
/// Struct for redeeming wrapped M1 tokens from Ethereum
pub type RedeemM1Token = TransferFromEthereum<M1TokenAddress>;

pub struct RewardDesignateRelayer {
    /// the rewards address of the Designated Relayer
    rewards_address: Address,
    /// height of the block at which the message appeared
    height: u64,
    /// the hash & height of the last descendant block marked as `seen`
    latest_descendant: ([u8; 32], u64)
}

impl RewardDesignateRelayer {
    pub fn is_confirmed(&self) -> bool {
        // we use a protocol parameter for the minimum number of confirmations
        self.latest_descendant.1 - self.height >= MIN_CONFIRMATIONS
    }
}


/// The messages in the VP queue
pub enum BridgeMessage<T: MintingAddress> {
    /// Messages for transfering value over the bridge
    Token(TransferFromEthereum<T>),
    /// Message for rewarding the designated validator
    Reward(RewardDesignateRelayer),
}

impl BridgeMessage<T: MintingAddress> {
    /// Check if the message received enough confirmations
    pub fn is_confirmed(&self) -> bool {
        match self {
            BridgeMessage::Token(token) => token.is_confirmed(),
            BridgeMessage::Reward(reward) => reward.is_confirmed(),
        }
    }
    
    /// From whom to transfer value
    pub fn source_address(&self) -> Address {
        match self {
            BridgeMessage::Token(token) => token.get_address(),
            BridgeMessage::Reward(_) => GOVERNANCE_TREASURY_ADDRESS,
        }
    }

    /// To whom to transfer value
    pub fn target_address(&self) -> Address {
        match self {
            BridgeMessage::Token(token) => token.receiver,
            BridgeMessage::Reward(reward) => reward.rewards_address,
        }
    }
    
    /// Which token should be transferred
    pub fn token(&self) -> Address {
        match self {
            BridgeMessage::Token(token) => token.get_address(),
            BridgeMessage::Reward(_) => xan(),
        }
    }
    
    pub fn amount(&self) -> Amount {
        // the reward amount for the Designate Relayer is a protocol
        // parameter
        match self {
            BridgeMessage::Token(token) => token.amount,
            BridgeMessage::Reward(_) => REWARD_AMOUNT,
        }
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
 3. For each message that is confirmed, transfer the appropriate tokens.
    The message contains methods for getting the source address, target
    address, token address, and amount. 

Note that this means that a transfer initiated on Ethereum will automatically
be seen and acted upon by M1. The transfer of tokens to the correct user
will occur on chain free of charge and requires no additional actions
from the end user.

### Redeeming ETH by burning tokens on M1

For redeeming wrapped ETH, the M1 side will need another validity predicate
that is called only when the appropriate user tx lands on chain. This validity
predicate will simply burn the tokens.

Once this transaction is approved, it is incumbent on the end user to 
request an appropriate "proof" of the transaction. This proof must be 
submitted to the appropriate Ethereum smart contract by the user to 
redeem their ETH. This also means all Ethereum gas costs are the 
responsibility of the end user.

The proofs to be used will be custom bridge headers that are calculated
deterministically from the block contents, including messages snet by M1 and
possibly validator set updates. They will be designed for maximally
efficient Ethereum decoding and verification. 

For each block on M1, validators must submit the corresponding bridge
header signed with a special secp256k1 key as part of their vote extension.
Validators must reject votes which do not contain correctly signed bridge
headers. The finalized bridge header with aggregated signatures will appear in the
next block as a protocol transaction. Aggregation of signatures is the 
responsibility of the next block proposer. 

The bridge headers need only be produced when the proposed block contains
requests to transfer value over the bridge to Ethereum. The exception is 
when validator sets change.  Since the Ethereum smart contract should
accept any header signed by bridge header signed by 2 / 3 of the staking
validators, it needs up-to-date knowledge of:
 - The current validators' public keys
 - The current stake of each validator

This means the at the end of every M1 epoch, a special transaction must be
sent to the Ethereum contract detailing the new public keys and stake of the
new validator set. This message must also be signed by at least 2 / 3 of the
current validators as a "transfer of power". It is to be included in validators
vote extensions as part of the bridge header. Signing an invalid validator
transition set will be consider a slashable offense.

Due to asynchronicity concerns, this message should be submitted well in
advance of the actual epoch change, perhaps even at the beginning of each
new epoch. Bridge headers to ethereum should include the current M1 epoch
so that the smart contract knows how to verify the headers. In short, there
is a pipelining mechanism in the smart contract. 

Such a message is not prompted by any user transaction and thus will have
to be carried out by an _M1 bridge relayer_. Once the transfer of power 
message is on chain, any time afterwards an M1 bridge process may take it
to craft the appropriate message to the Ethereum smart contracts. 

The details on the M1 bridge relayers are below in the corresponding section.

Signing incorrect headers is considered a slashable offense. Anyone witnessing
an incorrect header that is signed may submit a complaint (a type of transaction)
to initiate slashing of the validator who made the signature.

### Minting wrapped M1 tokens on Ethereum

If a user wishes to mint a wrapped token on Ethereum backed by a token on 
M1, (including M1T, M1's native token), they first must submit a special transaction on M1. This transaction
should be an instance of the following:

```rust
struct MintWrappedM1Token {
    /// The M1 address owning the token
    source: Address,
    /// The address on Ethereum receiving the wrapped tokens
    ethereum_address: Address,
    /// The address of the token to be wrapped 
    token: Address,
    /// The number of tokens to mint
    amount: Amount,
}
```
A special M1 validity predicate will be called on this transaction. If the
transaction is valid, the corresponding amount of the M1 token will be transferred
from the `source` address and deposited in an escrow account by the
validity predicate. 

Just as in redeeming ETH above, it is incumbent on the end user to
request an appropriate proof of the transaction. This proof must be
submitted to the appropriate Ethereum smart contract by the user.
The corresponding amount of wrapped M1T tokens will be transferred to the
`ethereum_address` by the smart contract.

### Redeeming M1 tokens 

Redeeming wrapped M1 tokens from Ethereum works much the same way as sending
ETH over the bridge. In fact, it may be handled by the same validity
predicate.

Every time Ethereum state is included, this validity predicate is called .
It keeps a queue of messages from the Ethereum bridge contracts that 
indicate wrapped M1 tokens have been burned by said contract Ethereum side.

The messages should be instances of the `RedeemM1Token` struct defined in [the 
above section](#minting-wrapped-eth-tokens-on-m1). Once such a message
has reached the requisite number of confirmations, a free protocol 
transaction should be included by the next block proposer. This transaction
should transfer the appropriate amount of M1 tokens from the M1 escrow account
to the address of the recipient.

## M1 Bridge Relayers

Validator changes must be turned into a message that can be communicated to
smart contracts on Ethereum. These smart contracts need this information
to verify proofs of actions taken on M1.

Since this is protocol level information, it is not user prompted and thus
should not be the responsibility of any user to submit such a transaction. 
However, any user may choose to submit this transaction anyway.

This necessitates an M1 node whose job it is to submit these transactions on
Ethereum at the conclusion of each M1 epoch. This node is called the 
__Designated Relayer__. In theory, since this message is publicly available on the blockchain, 
anyone can submit this transaction, but only the Designated Relayer will be 
directly compensated by M1. 

All M1 full nodes will have an option to serve as bridge relayer and run the 
relayer program. M1 governance will vote on a single full node to act as 
Designated Relayer. The governance treasury will be used to compensate the
Designated Relayer for the gas fees incurred as well as extra fees as 
payment for their trouble.

Since all M1 validators are running Ethereum full nodes, they can monitor
the performance of the Designated Relayer. If the performance is deemed 
unsatisfactory, a governance vote can be used to replace them.

### Choosing the Designated Relayer
The Designated Relayer shall be chosen via governance and will require validation
by a native Designated Relayer VP. Candidates for the
position must submit a transaction that:
 - Transfers an AMOUNT amount of tokens from the candidate address to 
   the address associated with the Designate Relayer VP.
 - Makes a governance proposal that will allow voting on the candidate.

Here AMOUNT is a protocol parameter. These locked funds are for accountability
of the Designated Relayer.

The Designated Relayer VP has the following storage keys:
 - `{designated_relayer_addr}/current_relayer: (Address, Option<Address>)`
 - `{designated_relayer_addr}/next_relayer: (Address, Option<Address>)`
 - `{designated_relayer_addr}/funds/[address]: Amount`
 - `{designated_relayer_addr}/candidates/[address]/proposal: Vec<u8>`

The storage should satisfy the following properties:
 - The `current_relayer` and `next_relayer` fields include the address of the
   relayer and an optional address for receiving rewards.
 - The `/funds/[address]` field includes the amount of tokens belonging to
   `[address]` currently locked by the Designated Relayer VP.
 - The `/candidates/[address]/proposal` field contains a Borsh serialization
   of the governance proposal corresponding to the candidacy of `[address]`.
 - The `current_relayer` and `next_relayer` addresses must have locked funds
   in the corresponding substorage keys.


Voting for the Designated Relayer follows the standard governance voting mechanisms.
Ballots are cast of the form
  ```rust
  struct Ballot { relayer: Address, source: Address }
  ```

A Designated Relayer will be active for a fixed _term_. The _voting period_
for the next Designated Relayer will take place during the term of the
current Designated Relayer. The time between voting ending and term of the
newly elected Designated Relayer beginning is the _pipeline period_. Thus
`term = voting period + pipeline period`. All of these are measured in epochs.

Note that when proposing an address for the position of Designated Relayer,
certain funds are locked immediately. If the proposal does not win, its funds
will be refunded at the end of voting.

The locking of these funds will trigger the Designated Relayer VP which will
perform extra checks on the proposal other than those required by
governance. In particular, it should do the following:
 - check that the AMOUNT of funds sent was correct
 - The address in the proposal matches the address it received funds from
 - check the voting period is of correct length
 - that the proposal goes into effect at the correct epoch.
 - the code in the proposal is hash-checked (whitelisted).
 
The proposal is a standard governance proposal: 

 ```rust
  struct DesignatedRelayerProposal { relayer: Address, rewards: Option<Address> }
  
  struct OnChainProposal {
      id: u64,
      /// This can follow a standard template
      content: Vec<u8>,
      author: Address,
      /// This should conform to start of a term
      votingStartEpoch: Epoch,
      /// This should conform to the end of the designated voting period
      votingEndEpoch: Epoch,
      /// This should be the start of the term after `voteStartEpoch`
      graceEpoch: Epoch,
      /// This should be always be the same code. It will be hash-checked
      /// by the Designated Relayer VP
      proposalCode: Option<Vec<u8>>,
      /// The should be a Borsh serialization of a
      /// `DesignateRelayerProposal` instance
      parameters: Option<Vec<u8>>,
  }
```

The proposal code should read the `address` and `rewards` fields from the governance parameters
substorage key and write them into the `next_relayer` substorage key of the 
Designated Relayer VP. The proposal code is a pre-written whitelisted wasm
blob whose hash is known to the Designated Relayer VP. 

Once this proposal is accepted, the proposal code will attempt to write
to the Designated Relayer VP storage, triggering the VP. At this stage,
the Designated Relayer VP should check that the proposal is under the 
`/candidates/[address]/proposal` substorage key, where the `address` field
can be found in the `parameters` field of the proposal. If it is,
the VP accepts the changes.

Note that in the event of ties, several of these proposals will be enacted.
The last enacted will overwrite the `next_relayer` key, giving a tie-break
mechanism.

---
To handle the voting logic, M1 validators will keep a simple state machine in memory.
It should work as follows:

- At the end of voting period, release any funds not belonging to either
  the `next_relayer` or `current_relayer` address.
- At the end of the pipeline period, _copy_ the value of the `next_relayer`
  key to the `current_relayer` key.
- At the end of the pipeline period, release any funds in the Designated Relayer vault belonging to addresses
  other than the `current_relayer` key.

Note that this state machine is designed to automatically keep the current 
validator if no new address wins enough votes in the voting period. If an 
address wishes to stop being the designated relayer, they must submit the
following tx:
```rust
struct StopProposal { relayer: Address }
```
If this tx is approved, validators add this address and the current term
number to their state machine. This validator (unless replaced or removed due
to malfeasance) must serve the remainder of the current term as well as the 
entire next term before they will stop being automatically kept in the running.

If the current Designate relayer has requested to stop, an extra step appears in the
state machine after all the other steps. This step happens at the beginning
of the current Designated Relayers last term. Their address is removed 
from the `next_relayer` field in storage.

### Monitoring the relayer

At the end of each epoch, if there has been a change to M1 validator set,
a flag should be set on the M1 state machine (described above) that alerts
validators to watch for a confirmation log emitted from the Ethereum smart
contracts indicated that processed a validator set update.

There should be a timeout parameter in which this log must be seen or else
a fine is levied against the Designated Relayer from their locked funds. If
their locked funds reaches zero, their address is removed from the `current_relayer`
field and also from the `next_relayer` field if necessary. They are 
thus immediately removed from the position of Designated Relayer.

On, the other hand, if the requisite log is observed by 2/3 of the staking
validators, the next block proposer includes a tx giving a reward to the
Designated Relayer's rewards account, paid from the governance treasury.

### Additional protocol parameters

There are several protocol parameters involved with the Designate Relayer.
All of these can be changed by governance votes. These parameters are:
- term duration of the Designated Relayer in number of epochs
- voting duration (voting duration + pipeline = term)
- required funds to be locked in the Designate Relayer VP
- the number of Ethereum blocks in which to see the Designate Relayer submitted 
  a validator set change to Ethereum.
- The minimum number of confirmations needed to consider the message successfully
  relayed to Ethereum
- The amount to reward a Designated Relayer for relaying a validator set change
- The amount to punish a Designated Relayer for not relaying a validator set change
  quickly enough

## Ethereum Smart Contracts
The set of Ethereum contracts should perform the following functions:
- Verify bridge header proofs from M1 so that M1 messages can
  be submitted to the contract.
- Verify and maintain evolving validator sets with corresponding stake
  and public keys.
- Emit log messages readable by M1
- Handle ICS20-style token transfer messages appropriately with escrow &
  unescrow on the Ethereum side
- Allow for message batching

Furthermore, the Ethereum contracts will whitelist ETH and tokens that
flow across the bridge as well as ensure limits on transfer volume per epoch.

An Ethereum smart contract should perform the following steps to verify
a proof from M1:
1. Check the epoch included in the proof.
2. Look up the validator set corresponding to said epoch.
3. Verify that the signatures included amount to at least 2 / 3 of the
   total stake.
4. Check the validity of each signature.

If all the above verifications succeed, the contract may affect the
appropriate state change, emit logs, etc.


## Resources which may be helpful:
- [Gravity Bridge Solidity contracts](https://github.com/Gravity-Bridge/Gravity-Bridge/tree/main/solidity)
- [ICS20](https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer)
- [Rainbow Bridge contracts](https://github.com/aurora-is-near/rainbow-bridge/tree/master/contracts)
- [IBC in Solidity](https://github.com/hyperledger-labs/yui-ibc-solidity)

Operational notes:
1. We should bundle the Ethereum full node with the `m1` daemon executable.
