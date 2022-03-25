# Reward distribution

Namada uses the automatically-compounding variant of [F1 fee distribution](https://drops.dagstuhl.de/opus/volltexte/2020/11974/pdf/OASIcs-Tokenomics-2019-10.pdf).

Rewards are given to validators for voting on finalizing blocks: the fund for these rewards can come from **minting** (creating new tokens). The amount that is minted depends on how much is staked and our desired yearly inflation. When the total of the tokens staked is very low, the return rate per validator needs to increase, but as the total amount of stake rises, validators will receive less rewards. Once we have acquired the desired stake percentage, the amount minted will just be the desired yearly inflation. 

The validator and the delegator must have agreed on a commission rate between themselves. Delegators pay out rewards to validators based on a mutually-determined commission rate that both parties must have agreed upon beforehand. The minted rewards are auto-bonded and only transferred when the funds are unbonded. Once we have calculated the total that needs to be minted at the end of the epoch, we split the minted tokens according to the stake the relevant validators and delegators contributed and distribute them to validators and their delegators. This is similar to what Cosmos does. 

## Basic algorithm

Take as a basis the following proof-of-stake system:

- A canonical singular staking unit of account.
- A set of validators `V_i`.
- A set of delegations `D_i`, each to a particular validator and in a particular (initial) amount.
- Epoched proof-of-stake, where changes to delegations, slashes, etc. are applied and inflation/rewards are paid out at the end of each epoch.
- Each epoch `e`, `R_e_i` is paid out to validator `V_i`.

We wish to approximate as exactly as possible the following ideal delegator reward distribution system:

- Each epoch, for each validator `V_i`, iterate over all of the delegations to that validator. For each delegation `D_j`, increase the delegation amount by `R_e_i * D_j.stake / V_i.stake` (or, equivalently, multiply it by `(V_i.stake + R_e_i) / V_i.stake`)
- Similarly, multiply the validator's voting power by `(V_i.stake + R_e_i) / V_i.stake`, which should now equal the sum of their revised-amount delegations.

In this system, rewards are automatically rebonded to delegations, increasing the delegation amounts and validator voting powers accordingly.

However, we wish to implement this without actually needing to iterate over all delegations each block, since this is too computationally expensive. We can exploit this constant multiplicative factor `V_i.stake + R_e_i / V_i.stake` which does not vary per delegation to perform this calculation lazily, storing only a constant amount of data per validator per epoch, and calculate revised amounts for each individual delegation only when a delegation changes.

Consider the accumulated changes to the stake amount of a particular delegation at epoch `m`, epoch `n`, and then from epoch `m` to `n`

$$
D_j.stake_m = D_j.stake_0 * \prod_{e = 0}^{m} \frac{V_i.stake_e + R_{i,e}}{V_i.stake_e}
$$

$$
D_j.stake_n = D_j.stake_0 * \prod_{e = 0}^{n} \frac{V_i.stake_e + R_{i,e}}{V_i.stake_e}
$$

$$
D_j.stake_n = D_j.stake_m * \prod_{e = m}^{n} \frac{V_i.stake_e + R_{i,e}}{V_i.stake_e}
$$

$$
D_j.stake_n = D_j.stake_0 * \prod_{e = 0}^{m} \frac{V_i.stake_e + R_{i,e}}{V_i.stake_e} * \prod_{e = m}^{n} \frac{V_i.stake_e + R_{i,e}}{V_i.stake_e}
$$

In order to calculate rewards for a delegation starting at an epoch `m` (after 0) at epoch `n`, we can simply divide out this difference:

$$
D_j.stake_n = D_j.stake_m * \prod_{e = m}^{n} \frac{V_i.stake_e + R_{i,e}}{V_i.stake_e}
$$

$$
D_j.stake_n = D_j.stake_m * \frac{\prod_{e = 0}^{n} \frac{V_i.stake_e + R_{i,e}}{V_i.stake_e}}{\prod_{e = 0}^{m} \frac{V_i.stake_e + R_{i,e}}{V_i.stake_e}}
$$

Let $entry_{v,l}$ be the entry for validator $v$ and epoch $l$, defined as:

$$
entry_l = \prod_{e = 0}^{l} \frac{V_i.stake_e + R_{i,e}}{V_i.stake_e}
$$

Then:

$$
D_j.stake_n = D_j.stake_m * \frac{entry_{v,n}}{entry_{v,m}}
$$

Thus, for each epoch and each validator, we need only store this accumulated product, with which updated amounts for all delegations can be calculated.

## Commission

Commission is implemented as a change to $R_{i,e}$. Validators can charge any commission they wish (in $[0, 1]$). The commission is paid directly to the account indicated by the validator.

## Slashes

Slashes should lead to punishment for delegators who were contributing voting power to the validator at the height of the infraction, _as if_ the delegations were iterated over and slashed individually.

This can be implemented as a negative inflation rate for a particular block.

Instant redelegation is not supported. Redelegations must wait the unbonding period.

## State management

Each $entry_{v,i}$ can be reference-counted by the number of delegations created during that epoch which might need to reference it. As soon as the number of delegations drops to zero, the entry can be deleted.
