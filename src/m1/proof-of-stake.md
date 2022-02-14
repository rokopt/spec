# Proof of stake

This specification should cover
- Proof-of-stake bonding mechanism (already covered in ledger docs)
- Slashing mechanism & infractions
- Rewards & distribution

## Slashing

- Slashing should happen for all of the Tendermint-recognised faults.

## Rewards

Until we have programmable validity predicates, rewards can use the mechanism outlined in the [F1 paper](https://drops.dagstuhl.de/opus/volltexte/2020/11974/pdf/OASIcs-Tokenomics-2019-10.pdf), but it should use the exponential model, so that withdrawing rewards more frequently provides no additional benefit (this is a design constraint we should follow in general, we don't want to accidentally encourage transaction spam). This should be written in a way that allows for a natural upgrade to a validator-customisable rewards model (defaulting to this one) if possible.
