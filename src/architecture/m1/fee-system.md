# Fee system

This specification should cover:
- Fee & gas system for M1

## Transaction Fees 

Tansaction fees im at incentivizing the operation of the blockchain. We want block producers to have incentive to add transactions to the blocks and publish blocks.

We will follow a [tipless version](https://arxiv.org/pdf/2106.01340.pdf) of the EIP 1559 scheme. In contrast with the original EIP 1559, the transaction fee of this tipless version consists solely of a base fee, with no tip. The base fee increases whenever blocks are fuller than the desired capacity and  decreases when the blocks haven't reached this capacity. Akin to Ethereum, our desired block fullness will also be 50%.   

To ensure incentivisation for validators we only transfer to treasury (instead of burning) 50% of the base fee rather than the 100% suggested by Ethereum. The other 50 % is reserved for paying future block producers (6 blocks ahead). Validators are apportioned fees depending on the fullness of the blocks they produce. For example, if the block is 75% full, the validators received full fees whereas if the block they produce is only 25% full, they only receive a third of the full fees. Moreover, we need to make sure all the tx suggested by wallets are equal, hence the changes announced to the base fee will be carried out with a delay of 6 blocks or more. 

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

Hence, an increased inflation rate translates to greater rewards for users with staked assets (sometimes also called _staking yield_).

### Transaction fees in other projects

Similar to Solana, Ethereum 2.0, Near, Polkadot, and Cosmos we will be taking away block producers tokens from transactions fees. In Eth2.0, 100 % of tx fees are burned, in Solana 50%-100% are burned and in Near protocol also 70 % is burned and 30 % goes to smart contract authors. In our case, 50% is burned and the rest goes to future validators for block producution. 
