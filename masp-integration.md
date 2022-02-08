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
