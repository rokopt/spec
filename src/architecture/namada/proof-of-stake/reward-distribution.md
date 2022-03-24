# Reward distribution

Namada uses the automatically-compounding variant of [F1 fee distribution](https://drops.dagstuhl.de/opus/volltexte/2020/11974/pdf/OASIcs-Tokenomics-2019-10.pdf).

Rewards are given to validators for voting on finalizing blocks: the fund for these rewards can come from **minting** (creating new tokens). The amount that is minted depends on how much is staked and our desired yearly inflation. When the total of the tokens staked is very low, the return rate per validator needs to increase, but as the total amount of stake rises, validators will receive less rewards. Once we have acquired the desired stake percentage, the amount minted will just be the desired yearly inflation. 

The validator and the delegator must have agreed on a commission rate between themselves. Delegators pay out rewards to validators based on a mutually-determined commission rate that both parties must have agreed upon beforehand. The minted rewards are auto-bonded and only transferred when the funds are unbonded. Once we have calculated the total that needs to be minted at the end of the epoch, we split the minted tokens according to the stake the relevant validators and delegators contributed and distribute them to validators and their delegators. This is similar to what Cosmos does. 
