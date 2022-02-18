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
* Move assets between Anoma accounts and the shielded pool
* Move assets around within the shielded pool
* Scan the blockchain to determine shielded assets in one's possession

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

## Note Format
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

## Transaction Format
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

## Transparent Input Format
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
## Transparent Output Format
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
