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



