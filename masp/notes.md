## Approaches

*Approach one*

"Diversifier" usage - [proposal](https://github.com/zcash/zcash/issues/2277#issuecomment-321106819).

Pros:
- Simple
- Provides shared anonymity set
- Maybe can reuse circuit from Zcash directly
- ZIP draft already: https://github.com/zcash/zips/pull/269/files
- Could add contract-controlled issuance pretty easily I think

Cons:
- Shielded-only user issued assets (?)
- Asset identifiers must be known (as I understand it), no secret assets (although they could be e.g. a hash)
- Inflexible, relatively speaking, no varying rules for separate tokens.

*Approach two*

"ZEXE" approach - [repo](https://github.com/scipr-lab/zexe).

Pros:
- More flexible

Cons:
- More complex
