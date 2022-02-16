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
SpendDescription {
  // Value commitment to amount of the asset in the note being spent
  cv: jubjub::ExtendedPoint,
  // Last block's commitment tree root
  anchor: bls12_381::Scalar,
  // Nullifier for the note being nullified
  nullifier: bytes,
  // Re-randomized version of the spend authorization key
  rk,
  // Spend authorization signature
  sighash_value, spend_auth_sig,
  // Zero-knowledge proof of the note and proof-authorizing key
  zkproof,
}
```
- output descriptions, which create new notes:
```
OutputDescription {
  // Value commitment to amount of the asset in the note being created
  cv: jubjub::ExtendedPoint,
  // Derived commitment tree location for the output note
  cmu: bls12_381::Scalar,
  // Note encryption public key
  epk: jubjub::ExtendedPoint,
  // Encrypted note ciphertext
  c_enc: bytes,
  // Encrypted note key recovery ciphertext
  c_out: bytes,
  // Zero-knowledge proof of the new encrypted note's location (?)
  zkproof,
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

The client, unlike the VP, needs a concept of a plaintext note:
```
Note {
  // Diversifier for recipient address
  d,
  // Diversified public transmission key for recipient address
  pkd,
  // Asset value in the note
  v,
  // Pedersen commitment trapdoor
  rcm,
  // Asset identifier for this note
  t,
}
```

Diversifiers are selected (randomly?) by the client and used to
diversify addresses and their associated keys. `v` and `t` identify the
asset type and value. Asset identifiers are derived from asset names,
which are arbitrary strings (in this case, token/other asset VP
addresses). The derivation must deterministically result in an
identifier which hashes to a valid curve point.
