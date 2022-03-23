# MASP integration spec

## Overview

The overall aim of this integration is to have the ability to provide a
multi-asset shielded pool following the MASP spec as an account on the
current Anoma blockchain implementation.

## Shielded pool VP

The shielded value pool can be an Anoma "established account" with a
validity predicate which handles the verification of shielded
transactions. Similarly to zcash, the asset balance of the shielded pool
itself is transparent - that is, from the transparent perspective, the
MASP is just an account holding assets. The shielded pool VP has the
following functions:

- Accept only valid transactions involving assets moving in or out of
  the pool.
- Accept valid shielded-to-shielded transactions, which don't move
  assets from the perspective of transparent Anoma.
- Publish the note commitment and nullifier reveal Merkle trees.

To make this possible, the host environment needs to provide
verification primitives to VPs. One possibility is to provide a single
high-level "verify transaction output descriptions and proofs"
operation, but another is to provide cryptographic functions in the host
environment and implement the verifier as part of the VP.

The shielded pool needs the ability to update the commitment and
nullifier Merkle trees as it receives transactions. This may possibly be
achievable via the temporary storage mechanism added for IBC, with the
trees finalized with each block.

The input to the VP is the following set of state changes:

- updates to the shielded pool's asset balances
- new encrypted notes
- updated note and nullifier tree states (partial, because we only have
  the last block's anchor?)

and the following data which is ancillary from the ledger's perspective:

- spend descriptions, which destroy old notes:
```
struct SpendDescription {
  // Value commitment to amount of the asset in the note being spent
  cv: jubjub::ExtendedPoint,
  // Last block's commitment tree root
  anchor: bls12_381::Scalar,
  // Nullifier for the note being nullified
  nullifier: [u8; 32],
  // Re-randomized version of the spend authorization key
  rk: PublicKey,
  // Spend authorization signature
  spend_auth_sig: Signature,
  // Zero-knowledge proof of the note and proof-authorizing key
  zkproof: Proof<Bls12>,
}
```
- output descriptions, which create new notes:
```
struct OutputDescription {
  // Value commitment to amount of the asset in the note being created
  cv: jubjub::ExtendedPoint,
  // Derived commitment tree location for the output note
  cmu: bls12_381::Scalar,
  // Note encryption public key
  epk: jubjub::ExtendedPoint,
  // Encrypted note ciphertext
  c_enc: [u8; ENC_CIPHERTEXT_SIZE],
  // Encrypted note key recovery ciphertext
  c_out: [u8; OUT_CIPHERTEXT_SIZE],
  // Zero-knowledge proof of the new encrypted note's location (?)
  zkproof: Proof<Bls12>,
}
```

Given these inputs:

The VP must verify the proofs for all spend and output descriptions
(`bellman::groth16`), as well as the signature for spend notes.

Encrypted notes from output descriptions must be published in the
storage so that holders of the viewing key can view them; however, the
VP does not concern itself with plaintext notes.

Nullifiers and commitments must be appended to their respective Merkle
trees in the VP's storage as well, which is a transaction-level rather
than a block-level state update.

Additionally to the individual spend and output description
verifications, the final transparent asset value change described in the
transaction must equal the pool asset value change, and as an additional
sanity check, the pool's balance of any asset may not end up negative
(this may already be impossible?). (needs more input)

NB: Shielded-to-shielded transactions in an asset do not, from the
ledger's perspective, transact in that asset; therefore, the asset's own
VP is not run as described above, and cannot be because the shielded
pool is asset-hiding.

## Client capabilities
The client should be able to:
* Make transactions with a shielded sender and/or receiver
* Scan the blockchain to determine shielded assets in one's possession
* Generate payment addresses from viewing keys from spending keys

To make shielded transactions, the client has to be capable of creating
and spending notes, and generating proofs which the pool VP verifies.

Unlike the VP, which must have the ability to do complex verifications,
the transaction code for shielded transactions can be comparatively
simple: it delivers the transparent value changes in or out of the pool,
if any, and proof data computed offline by the client.

The client and wallet must be extended to support the shielded pool and
the cryptographic operations needed to interact with it. From the
perspective of the transparent Anoma protocol, a shielded transaction is
just a data write to the MASP storage, unless it moves value in or out
of the pool. The client needs the capability to create notes,
transactions, and proofs of transactions, but it has the advantage of
simply being able to link against the MASP crates, unlike the VP.

### Making Shielded Transactions
#### Shielding Transactions
The client should be able to make shielding transactions by providing a
transparent source address and a shielded payment address. The
main transparent effect of such a transaction should be a deduction of
the specified amount from the source address, and a corresponding
increase in the balance of the MASP validity predicate's address. The
gas fee is charged to the source address. Once the transaction is
completed, the spending key that was used to generate the payment address
will have the authority to spend the amount that was send. Below is an
example of how a shielding transacion should be made:
```
anomac transfer --source Bertha --amount 50 --token BTC --payment-address 9cb63488b1d6ef25f069b6eb5bba2eee3dcf22bc10b2063a1fbcb91964341d75837bdce3e2fe3ec9c1e005
```
#### Unshielding Transactions
The client should be able to make unshielding transactions by providing
a shielded spending key and a transparent target address. The main
transparent effect of such a transaction should be a deduction of the
specified amount from the MASP validity predicate's address and a
corresponding increase in the transparent target address. The gas fee
is charged to the signer's address (which should default to the target
address). Once the transaction is complete, the spending key will no
longer be able to spend the transferred amount. Below is an example of
how an unshielding transaction should be made:
```
anomac transfer --target Bertha --amount 45 --token BTC --spending-key AA
```
#### Shielded Transactions
The client should be able to make shielded transactions by providing a
shielded spending key and a shielded payment address. There should be
no change in the transparent balance of the MASP validity predicate's
address. The gas fee is charged to the signer's address. Once the
transaction is complete, the spending key will no longer be able to
spend the transferred amount, but the spending key that was used to
(directly or indirectly) generate the payment address will. Below is
an example of how a shielded transaction should be made:
```
anomac transfer --spending-key AA --amount 5 --token BTC --payment-address 9cb63488b1d6ef25f069b6eb5bba2eee3dcf22bc10b2063a1fbcb91964341d75837bdce3e2fe3ec9c1e005
```
### Viewing Shielded Balances
The client should be able to view the balance at a shielded address.
This should be possible using only a viewing key, however supplying
a spending key is permissible. The output should be a list of pairs,
each denoting a token type and the unspent amount of that token
present at the shielded address. Note that it should be possible to
restrict the balance query to check only for a specific token type.
Below is are examples of how balance queries should be made:
```
anomac balance --spending-key AA
anomac balance --viewing-key 628a9956322f3f7d20b19801d9b4a8f3cb4b8b756a26ef2477feb5264be7b808c920996f37a79433d08e27fefcda0b6736c296b1073734a4ee35d11368f2b52ef14d7c1749cc8119ecc8a894f696992453f2dd78ef1e9d74172b2a5ef7cc8c50
```

### Shielded Address/Key Generation
#### Viewing Key Generation
The client should be able to derive a viewing key for any given
spending key. This key should be usable to determine the total
unspent notes that the spending key is authorized to spend. It should
also be able to generate payment addresses such that the originating
spending key has the authority to spend notes sent to them. It should
not be possible to directly or indirectly use the viewing key to spend
funds. Below is an example of how viewing keys should be generated:
```
anomaw -- masp derive-view-key --spending-key AA
```
#### Payment Address Generation
The client should be able to generate a payment address from a
spending key or viewing key. This payment address should be usable
to send notes to the originating spending key. It should not be
directly or indirectly usable to either spend notes or view shielded
balances. Below are examples of how payment addresses should be
generated:
```
anomaw masp gen-payment-addr --spending-key AA
anomaw masp gen-payment-addr --viewing-key 628a9956322f3f7d20b19801d9b4a8f3cb4b8b756a26ef2477feb5264be7b808c920996f37a79433d08e27fefcda0b6736c296b1073734a4ee35d11368f2b52ef14d7c1749cc8119ecc8a894f696992453f2dd78ef1e9d74172b2a5ef7cc8c50
```
## Protocol

### Note Format
The note structure encodes an asset's type, its quantity and its owner.
More precisely, it has the following format:
```
struct Note {
  // Diversifier for recipient address
  d: jubjub::SubgroupPoint,
  // Diversified public transmission key for recipient address
  pk_d: jubjub::SubgroupPoint,
  // Asset value in the note
  value: u64,
  // Pedersen commitment trapdoor
  rseed: Rseed,
  // Asset identifier for this note
  asset_type: AssetType,
  // Arbitrary data chosen by note sender
  memo: [u8; 512],
}
```
For cryptographic details and further information, see
[Note Plaintexts and Memo Fields](https://zips.z.cash/protocol/protocol.pdf#noteptconcept).
Note that this structure is required only by the client; the VP only
handles commitments to this data.

Diversifiers are selected (randomly?) by the client and used to
diversify addresses and their associated keys. `v` and `t` identify the
asset type and value. Asset identifiers are derived from asset names,
which are arbitrary strings (in this case, token/other asset VP
addresses). The derivation must deterministically result in an
identifier which hashes to a valid curve point.

### Transaction Format
The transaction data structure comprises a list of transparent inputs
and outputs as well as a list of shielded inputs and outputs. More
precisely:
```
struct Transaction {
    // Transaction version
    version: u32,
    // Transparent inputs
    tx_in: Vec<TxIn>,
    // Transparent outputs
    tx_out: Vec<TxOut>,
    // The net value of Sapling spends minus outputs
    value_balance_sapling: Vec<(u64, AssetType)>,
    // A sequence ofSpend descriptions
    spends_sapling: Vec<SpendDescription>,
    // A sequence ofOutput descriptions
    outputs_sapling: Vec<OutputDescription>,
    // A binding signature on the SIGHASH transaction hash,
    binding_sig_sapling: [u8; 64],
}
```
For the cryptographic constraints and further information, see
[Transaction Encoding and Consensus](https://zips.z.cash/protocol/protocol.pdf#txnencoding).
Note that this structure slightly deviates from Sapling due to
the fact that `value_balance_sapling` needs to be provided for
each asset type.

### Transparent Input Format
The input data structure decribes how much of each asset is
being deducted from certain accounts. More precisely, it is as follows:
```
struct TxIn {
    // Source address
    address: Address,
    // Asset identifier for this input
    token: AssetType,
    // Asset value in the input
    amount: u64,
    // A signature over the hash of the transaction
    sig: Signature,
    // Used to verify the owner's signature
    pk: PublicKey,
}
```
Note that the signature and public key are required to authenticate
the deductions.
### Transparent Output Format
The output data structure decribes how much is being added to
certain accounts. More precisely, it is as follows:
```
struct TxOut {
    // Destination address
    address: Address,
    // Asset identifier for this output
    token: AssetType,
    // Asset value in the output
    amount: u64,
}
```
Note that in contrast to Sapling's UTXO based approach, our
transparent inputs/outputs are based on the account model used
in the rest of Anoma.

# Shielded Transaction Specification
## Transaction Format
Shielded transactions are implemented as an optional extension to transparent transactions:
```
/// A simple bilateral token transfer
#[derive(..., BorshSerialize, BorshDeserialize, ...)]
pub struct Transfer {
    /// Source address will spend the tokens
    pub source: Address,
    /// Target address will receive the tokens
    pub target: Address,
    /// Token's address
    pub token: Address,
    /// The amount of tokens
    pub amount: Amount,
    /// Shielded transaction part
    pub shielded: Option<Transaction>,
}
```
## Conditions
* A shielded component equal to `None` indicates a transparent Anoma transaction
* Otherwise the shielded component must have the form `Some(x)` where `x` has the transaction encoding specified in the [Multi-Asset Shielded Pool Specication](https://raw.githubusercontent.com/anoma/masp/main/docs/multi-asset-shielded-pool.pdf)
* Hence for a shielded transaction to be valid:
  * the `Transfer` must satisfy the usual conditions for Anoma ledger transfers (i.e. sufficient funds, ...) as enforced by token and account validity predicates
  * the `Transaction` must satisfy the conditions specified in the [Multi-Asset Shielded Pool Specication](https://raw.githubusercontent.com/anoma/masp/main/docs/multi-asset-shielded-pool.pdf)
  * the `Transaction` and `Transfer` together must additionaly satisfy the below boundary conditions intended to ensure consistency between the MASP validity predicate ledger and Anoma ledger

### Boundary Conditions
* If the target address is the MASP validity predicate, then no transparent outputs are permitted in the shielded transaction
* If the target address is not the MASP validity predicate, then:
  * there must be exactly one transparent output in the shielded transaction and:
    * its public key must be the hash of the target address - this prevents replay attacks altering transfer destinations
    * its value must equal that of the containing transfer - this prevents replay attacks altering transfer amounts
* If the source address is the MASP validity predicate, then no transparent inputs are permitted in the shielded transaction
* If the source address is not the MASP validity predicate, then:
  * there must be exactly one transparent input in the shielded transaction and:
    * its value must equal that of amount in the containing transfer - this ensures that clients cannot steal funds from the pool

## Remarks
* The gas fees for shielded transactions are charged to the signer just like it is done for transparent transactions
  * As a consequence, an amount exceeding the gas fees must be available in a transparent account in order to execute an unshielding transaction - this prevents denial of service attacks

## Multi-Asset Shielded Pool Specification Differences from Zcash Protocol Specification
* [3.2 Notes](https://zips.z.cash/protocol/protocol.pdf#notes)
  * [3.2.1 Note Plaintexts and Memo Fields](https://zips.z.cash/protocol/protocol.pdf#noteptconcept)
* [4.1.8 Commitment](https://zips.z.cash/protocol/protocol.pdf#abstractcommit)
* [4.7 Sending Notes](https://zips.z.cash/protocol/protocol.pdf#send)
  * [4.7.2 Sending Notes (Sapling)](https://zips.z.cash/protocol/protocol.pdf#saplingsend)
* [4.8 Dummy Notes](https://zips.z.cash/protocol/protocol.pdf#dummynotes)
  * [4.8.2 Dummy Notes (Sapling)](https://zips.z.cash/protocol/protocol.pdf#saplingdummynotes)
* [4.13 Balance and Binding Signature (Sapling)](https://zips.z.cash/protocol/protocol.pdf#saplingbalance)
* [4.19.1 Encryption (Sapling and Orchard)](https://zips.z.cash/protocol/protocol.pdf#saplingandorchardencrypt)
* [4.19.2 Decryption using an Incoming Viewing Key (Sapling and Orchard)](https://zips.z.cash/protocol/protocol.pdf#decryptivk)
* [4.19.3 Decryption using a Full Viewing Key (Sapling and Orchard)](https://zips.z.cash/protocol/protocol.pdf#decryptovk)
* [5.4.8 Commitment Schemes](https://zips.z.cash/protocol/protocol.pdf#concretecommit)
  * [5.4.8.2 Windowed Pedersen commitments](https://zips.z.cash/protocol/protocol.pdf#concretewindowedcommit)
  * [5.4.8.3 Homomorphic Pedersen commitments (Sapling and Orchard)](https://zips.z.cash/protocol/protocol.pdf#concretehomomorphiccommit)
* [5.5 Encodings of Note Plaintexts and Memo Fields](https://zips.z.cash/protocol/protocol.pdf#notept)
* [7 Consensus Changes from Bitcoin](https://zips.z.cash/protocol/protocol.pdf#consensusfrombitcoin)
  * [7.1 Transaction Encoding and Consensus](https://zips.z.cash/protocol/protocol.pdf#txnencoding)
  * [7.4 Output Description Encoding and Consensus](https://zips.z.cash/protocol/protocol.pdf#outputencodingandconsensus)
