

# Fee system

This specification should cover:
- Fee & gas system for M1

# Introduction

Tansaction fees im at incentivizing the operation of the blockchain. We want block producers to have incentive to add transactions to the blocks and publish blocks.

We will follow a [tipless version](https://arxiv.org/pdf/2106.01340.pdf) of the EIP 1559 scheme. In contrast with the original EIP 1559, the transaction fee of this tipless version consists solely of a base fee, with no tip. The base fee increases whenever blocks are fuller than the desired capacity and  decreases when the blocks haven't reached this capacity. Akin to Ethereum, our desired block fullness will also be 50%.   

To ensure incentivisation for validators we only burn (or transfer to treasury) 50% of the base fee rather than the 100% suggested by Ethereum. The remaining 20% is reserved for paying future block producers (6 blocks ahead). Validators are apportioned fees depending on the fullness of the blocks they produce. For example, if the block is 75% full, the validators received full fees whereas if the block they produce is only 25% full, they only receive a third of the full fees. Moreover, we need to make sure all the tx suggested by wallets are equal, hence the changes announced to the base fee will be carried out with a delay of 6 blocks or more. 

The change in base fees cannot be too fast or too frequent. We propose a minimum of 20 blocks between changes and a delay of 10 blocks before a base fee change is applied. 

TODO: To calculate base fees we need to define the gas fees for the following types of transactions.
1. Send governance proposals (every delegator/validator can propose a governance proposal: say "we want to increase gas fees")
2. Vote on governance proposals
3. Create accounts
4. Delete accounts
5. Stake funds
6. Unstake funds
7. Transfer funds
8. Propose blocks
9. Vote on blocks

TODO: We also need to determine the block capacity (engineering decision), which refers to the total gas a block can process. 

## Token flow

The protocol controls M1T (the native staking token) sourced from two locations:

1. Fees (80%) paid for transactions per the description above.
1. Inflation, as in tokens directly printed by the protocol (which we can do arbitrarily).

These tokens then flow to many different sinks:

1. Proof-of-stake rewards, which are paid into the reward distribution mechanism in order to distribute them to validators and delegators.
1. Shielded pool rewards, which are locked in a way such they can be eventually paid to users who kept tokens in the shielded pool.
1. A governance pool.
    - These tokens are slowly burned at a fixed fraction per epoch.
1. A set of configurable custom sinks, which can be addresses on M1, addresses on Ethereum (over the Ethereum bridge), or addresses on other chains connected over IBC.
    - These can be paid fixed amounts per epoch.
    - Initial receipients will be configured at genesis, and recipients can be added, removed, or altered by M1 governance.

## Token Economics and Inflation

Locked tokens help secure the system while liquidity supports its activity and liveness. We need to choose the ratio between locked and liquid token carefully. Liquid tokens make sure the price of the token is not increasing out of scarcity and user have access to tokens to pay transaction fees, while locked tokens are the guaranteeing attacking the system is expensive for an adversary. 

Here are some numbers from other projects

| Blockchain platform | Approximate locking %       | Remarks |
|--------------------------------------------------|------|-----|
| Cosmos                                           | 66.7 |
| Polkadot                                         | 50   |
| Ethereum                                         | 47   |
| Solana                                           | 77   |

Our desired percentage for M1 is 33%-66%: Locked for validating and the rest %33-%66 is liquid. When the price of the token is low we can aim for a higher % of locked tokens and reduce this as the price and demand for liquid tokens increases. For example, we can set a range, in the beginning have be 50 % and later aim for 1/3. I dont think we should go lower than that. The staking reward should be ideally set. 

The total inflation is impacted by of the tokens minted for PoS (paid to validators and their delegators), tokens that are burnt at treasury, tokens that are burnt from transction fees and tokens that are burnt for offences. 

TODO: inflation curve (_does this need to be plotted? I can do it with Inkscape_)Yes, please. Thanks!
