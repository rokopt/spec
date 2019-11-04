## Approaches

*Approach one*

"Diversifier" usage - [proposal](https://github.com/zcash/zcash/issues/2277#issuecomment-321106819).

Pros:
- Simple
- Provides shared anonymity set
- Maybe can reuse circuit from Zcash directly
- ZIP draft already: https://github.com/zcash/zips/pull/269/files
- Could add contract-controlled issuance pretty easily I think
- Could *maybe* re-use Zcash trusted setup if Zcash does another one (or collab somehow)
- Has all the nice features of Sapling, e.g. viewing keys

Cons:
- Shielded-only user issued assets (?)
- Asset identifiers must be known (as I understand it), no secret assets (although they could be e.g. a hash)
- Inflexible, relatively speaking, no varying rules for separate tokens.
- Seems likely Zcash will do this anyways

*Approach two*

"ZEXE" approach - [repo](https://github.com/scipr-lab/zexe) - "mint or conserve" predicate.

Questions:
- Can this be easily extended to non-fixed-supply assets (programmed by a contract) (presumably yes)?

Pros:
- More flexible
- Zcash is unlikely to do this, so more unique as a feature
- Larger anonymity set, in the sense that transactions may not be value transfers at all
- Setup does not depend on predicates
- Options for e.g. whitelisting / blacklisting (so convenient for some Tezos token use-cases)
- Can implement totally different use-cases, e.g. private decentralized exchange

Cons:
- More complex, lots of implementation to do, we'd need to add nice features like viewing keys
- Larger transactions, more expensive to verify
- Would definitely need a new trusted setup (and several if we don't use a universal SNARK)

Probably should use a universal SNARK. Will cost a bit in size / verification time.

In either case, we need a new trusted setup or a transparent SNARK. Options:
