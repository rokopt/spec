

# Fee system

This specification should cover:
- Fee & gas system for M1

We will follow the EIP 1559 scheme, where the transaction fee consists of a base fee and a tip. The base fee increases whenever blocks are fuller than the desired capacity, which is defined to be 50% in Ethereum and decreases when the blocks are less than 50% full. Our desired block fullness will also be 50%. However, for privacy reasons, we adopt a [tipless version](https://arxiv.org/pdf/2106.01340.pdf) suggested by Tim Roughgarden.  

To make sure validators are incentivized we only burn (or transfer to treasury) 80% of the base fee rather than the 100% suggested by Ethereum. The remaining 20% is reserved for paying future (6 blocks ahead) block producers. Depending on how full the blocks are, validators get portions of these fees. For example, if the block is 75 % full, the validators get the full fees whereas if the block they produce is only 25% full, they get 1/3 of the full fees. Moreover, we need to make sure all the tx suggested by wallets are equal, hence the changes announced to the base fee will be carried out with a delay of 6 blocks or more. 

The change in base fees cannot be too fast or too frequent either. We propose a minimum of 20 blocks between changes and a delay of 10 blocks before a base fee change is applied. 

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

## Inflation and Validarors Rewards and Slashing
### Inflation
Locked tokens help secure the system while liquidity supports its activity and liveness.  

Desired 33%-66%: Locked for validating
Rest %: Liquid
_(desired for Anoma? or is this a more general practice while choosing locking %ages? If for Anoma, this should be included later, after the table.)_


| Blockchain platform | Approximate locking percentage       | Remarks |
|--------------------------------------------------|------|-----|
| Cosmos                                           | 66.7 |
| Polkadot                                         | 50   |
| Ethereum                                         | 47   |
| Solana                                           | 77   |

_the following paragraph can be done away with, by including relevant details in remarks_
In Cosmos the ideal locking is 2/3 in Polkadot it is 50%. In Ethereum the goal is to have 8,388,608 total ETH staked  by validators which would be 47%. On Solana its about 77 % of tokens. 

We can set a range, in the beginning have be 50 % and later aim for 1/3. I dont think we should go lower than that. The staking reward should be ideally set. 

TODO: inflation curve (_does this need to be plotted? I can do it with Inkscape_)

### Staking Rewards
Rewards are given to validators for voting on finalizing blocks: the fund for these rewards can come from **minting** _can we just say a word about what minting is?_. The amount that is minted depends on how much is staked and our desired yearly inflation. When the total of the tokens staked is very low, the return rate per validator needs to increase, but as the total amount of stake rises, validators will receive less rewards. Once we have acquired the desired stake percentage, the amount minted will just be the desired yearly inflation. 

Once we have calculated the total that needs to be minted at the end of the epoch, we split the minted tokens according to the stake they(_by "they" do you mean the relevant validators and delegators?_) contributed (i.e., Cosmos _what does this mean?_) and distribute them to validators and their delegators (_should this be "delegeators and their validators?"_). The validator and the delegator must have agreed on a commission rate between themselves. Delegators pay out rewards to validators based on a mutually-determined commission rate that both parties must have agreed upon beforehand. The minted rewards are auto-bonded and only transferred when the funds are unbonded. 

### Slashing for misbehavior 
An important part of the security model of M1 is based on making attacking the system very expensive. To this end, the validator who has bonded stake will be slashed once an offence has been detected. 

These are the types of offences: 
* Equivocation in consensus 
    * voting: meaning that a validator has submitted two votes that are confliciting 
    * block production: a block producer has created two different blocks for the same height
* Invalidity: 
    * block production: a block producer has produced invalid block
    * voting: validators have voted on invalid block
   
Unavailability is not considered an offense, but a validator who hasn't voted will not receive rewards. 

Once an offence has been reported: 
1. Kicking out
2. Slashing
  - individual: Once someone has reported an offence it is reviewed by validarors and if confirmed the offender is slashed. The funds that are taken from the offender are either burnt or sent to the treasury after a small cut (10%) of it goes to the person who reported the offence. 
  - collective (escalated slashing) : If more than a certain threshold of users commit an offence, then slashing will be escalated. We would like to implement quadratic slashing (_does this mean the growth of slashing is O(n^2)?_). If the offender is holding less than 1% of stake the slashing will be small and it will escalate to 100 % if the offenders hold up to 1/3 of the total stake.



OLDER VERSION BELOW 

# Fee system

This specification should cover:
- Fee & gas system for M1

We will follow the EIP 1559 scheme, where the transaction fee consists of a base fee and a tip. The base fee increases whenever blocks are fuller than the desired capacity, which is defined to be 50% in Ethereum and decreases when the blocks are less than 50% full. Our desired block fullness will also be 50%. However, for privacy reasons, we adopt a [tipless version](https://arxiv.org/pdf/2106.01340.pdf) suggested by Tim Roughgarden.  

To make sure validators are incentivized we only burn (or transfer to treasury) 80% of the base fee rather than the 100% suggested by Ethereum. The remaining 20% is reserved for paying future (6 blocks ahead) block producers. Depending on how full the blocks are, validators get portions of these fees. For example, if the block is 75 % full, the validators get the full fees whereas if the block they produce is only 25% full, they get 1/3 of the full fees. Moreover, we need to make sure all the tx suggested by wallets are equal, hence the changes announced to the base fee will be carried out with a delay of 6 blocks or more. 

The change in base fees cannot be too fast or too frequent either. We propose a minimum of 20 blocks between changes and a delay of 10 blocks before a base fee change is applied. 

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

## Inflation and Validarors Rewards and Slashing
### Inflation
Locked tokens serve as security of the system while liquidity supports activity and liveness of the system.  

Desired 33%-66%: Locked for validating
Rest %: Liquid

In Cosmos the ideal locking is 2/3 in Polkadot it is 50%. In Ethereum the goal is to have 8,388,608 total ETH staked  by validators which would be 47%. On Solana its about 77 % of tokens. We can set a range, in the beginning have be 50 % and later aim for 1/3. I dont think we should go lower than that. The staking reward should be ideally set. 

TODO: inflation curve







