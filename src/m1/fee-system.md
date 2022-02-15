# Fee system

This specification should cover:
- Fee & gas system for M1

We will follow the EIP 1559 scheme, where the transaction fee consists of a base fee and a tip. The base fee increases whenever blocks are fuller than the desired capacity, which is defined to be 50 % in Ethereum and decreases when the blocks are less than 50% full . Our desired block fullness will also be 50 %. However, we adopt a [tipless version](https://arxiv.org/pdf/2106.01340.pdf)(suggested by Tim Roughgarden) for privacy reasons. 

To make sure validators are incentivized we only burn (or transfer to treasury) 80% of the base fee rather than the 100% suggested by Ethereum. The remaining 20% is reserved for paying future (6 blocks ahead) block producers. Depending on how full the blocks are, validators get portions of these fees. For example, if the block is 75 % full, the validators get the full fees whereas if the block they produce is only 25% full, they get 1/3 of the full fees. Moreover, we need to make sure all the tx suggested by wallets are equal, hence the changes announced to the base fee will be carried out with a delay of 6 blocks or more. 

The change in base fees cannot be too fast or too frequent either. We propose a minimum of 20 blocks between changes and a delay of 10 blocks before a base fee change is applied. 

TODO: To calculate base fees we need to define the gas fees for the following types of transactions.
1. Sending proposal for governance  (every delegator/validators can propose a governance proposal: say "we want to increase gas fees")
2. Voting for governance
3. Create accounts
4. Delete accounts
5. Stake funds
6. Unstake funds
7. Transfer funds
8. Propose blocks
9. Vote on blocks
TODO: We also need to determine the block capacity (engineering decision), which refers to the total gas a block can process. 

Test

