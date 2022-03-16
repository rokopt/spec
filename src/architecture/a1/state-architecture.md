# State architecture

## Validity Predicates
All state on [A1](../a1.md) is indexed by Validity Predicates (VPs).
State can be understood as a map from VP to per-VP state. 

### Keys
Each VP's state is further divided into states indexed by Keys.
State can therefore be further understood as a map from VP, Key to
 per-key State. 


#### Ordering
Keys are the core unit of ordering: 
- All writes to a key must be totally ordered.
- All reads to a key must be ordered with respect to writes.

#### Per-Key State
Per-Key state consists of:
- a reference to (hash of) the "most recent" _write_ transaction to
   this key
  - (Note that, as we order before evaluation, this reference may be
     to an invalid transaction, in which case the transaction
     referenced may not have written the current state.)
- an arbitrary blob of bits (storage)

### K0
Each VP's state includes a special key, for now called `K0`, with
 state representing the Validity Predicate's Program Text.
All transactions which _write_ to any key of the VP's state must
 _read_ from `K0`.

## Transactions
Transactions are the "things that must be ordered."
Each transaction consists of:
- _Parents_: a set of references to (hashes of) "previous" transactions.
- _Reads_: a set of Key, Reference pairs (representing
    "most recent write" for each key this transaction might read)
- _Writes_: a set of Key, Reference pairs (representing
    "most recent write" for each key this transaction might write)
- _Creates_: a set of Keys
- _Program_: some representation of a program to be executed over state

Note that _Parents_, even in an "invalid" transaction, _must include_
 all the references of in _Reads_ and _Writes_. 
For succinctness, in our marshaled format, we should probably not
 encode these twice, so when we unmarshal a block, we should
 understand that all references from _Reads_ and _Writes_ are appended
 to _Parents_.
_Parents_ can also contain other references.

Furthermore, all transactions (even "invalid" ones) _must read_ from
 `K0` of any VP to which they _Write_ or _Create_. 

### Validity 
First, we define state at the "start" of a transaction as, for each
 key in _Reads_ or _Writes_, the state from the "end" of the
 "most recent write" transaction referenced.

A transaction is _valid_ if, when executing _Program_:
- the state machine only reads from keys in _Reads_ or _Writes_,
- and only writes to keys in _Writes_ or _Creates_,
- and state after execution satisfies the VP programs (`K0`s) for all
   the VPs with keys in _Writes_ or _Creates_.
Note that we order transactions _before_ determining if they're valid. 

### Batching
A list of transactions can be batched together into a larger
 transaction (a _block_) by taking the union for each of their fields
 _Parents_, _Reads_, _Writes_, and _Creates_, and concatenating their
 programs (possibly with some notion of "roll-back and continue" for
 programs that turn out to be invalid).

## Consensus
The purpose of consensus is to decide on a sub-DAG of Transactions
 partially ordered by _Parents_ references.
Specifically, among decided transactions:
- All transactions which _Write_ or _Create_ the same key are totally
   ordered.
- All transactions which _Read_ a key are ordered with respect to
   transactions that _Write_ or _Create_ that key: they have one such
   transaction as a parent, and are an ancestor of the next such
   transaction.

### Key Creation
Consensus participants should take care not to allow multiple,
 unordered transactions which _Create_ the same key. 
For each possible Key that can be created, at any given time, the
 quorums of processes that can approve it must be well-defined.

### Ordering Shards
One way consensus participants can parallelize while ensuring key
 consensus properties is to divide into _ordering shards_: independent
 consensus instances, each featuring a copy of each participant. 
Theoretically, participants do not have to agree on the arrangement of
 these ordering shards, so long as they agree on which transactions
 are decided. 

An ordering shard could hold an exclusive but transferable write lock
 for keys, and distribute and collect read locks from other shards. 
Bookkeeping concerning these locks need not be done on-chain, so long
 as the consensus properties are maintained. 
However, in principle, we could do it on-chain, managed by some VP
 that is read in basically every block. 

### Epochs as VP
The set of quorums necessary to decide on a transaction change over time.
We want each transaction to encode the quorums necessary to decide it.
One way to do this is to encode a VP specifying necessary conditions
 for epoch updates, and a limited number of keys, each of which encodes
 a set of quorums. 
Each transaction must read from at least one of these keys.

Consensus can keep deciding on blocks using old quorums during quorum
 updates by continuing to use old quorums.
However, when a key is updated, an old quorum set is no longer
 usable. 

This naturally encodes how we can change the code that manages epoch
 updates (`K0` for the Epoch VP).

## Merkle Tree
Both VPs and Keys need only be referenced by collision-resistant hash. 
State is therefore a Hash Table, and can be kept as a Merkle Tree. 
This allows for compact update objects, and succinct roots. 





