# Validity Predicates

Short description

## List of Default VP for M1
native:
- Pos
- IBC: main IBC VP
- IbcToken: for IBC token escrow, burn and mint
- Protocol parameters: for now, it doesn’t allow any changes
- Default VPs: this is just being added. It’s a validity predicate for default WASM validity predicates :doge-fractal: , we’re adding the default implicit account’s VP to it, but there might be others later. For now, this also doesn’t allow any changes

WASM:
- fungible token VP: checks tx inputs == outputs and it’s used for the native token
- MASP: this could potentially be native too, it’s not difficult to change as they have the same API available
implicit account VP: allows cryptographic sigs authorization

we also have a reserved internal address for PosSlashPool  where slashed token would be sent to, but we don’t have any VP for it yet
