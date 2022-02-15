# Fee system

This specification should cover:
- Fee & gas system for M1

We will follow the EIP 1559 scheme, where te transaction fee constitutes of a base fee and a tip. the base fee increases whenver blocks are fuller than the desired capacity, which is defined to be 50 % in Ethereum and decreases when the blocks are less full than 50 %. Our desired block fullness will also be 50 %. However, we adopt a tipless version suugested by Tim Roughgarden (cite Roughgarden paper) for privacy reasons. 

To make sure validators are incentivized we only burn (or transfer to treasury) 80% of the base fee rather than the 100% suggested by Ethereum. The remaining 20% is reserved for paying future (6 blocks ahead) block producers. Depending on how full the blocks are the validators get portions of this fees. For example, if the block is 75 % full then the validators get all the fees. If the block they produce is only 25% full they get 1/3 of it. Moreoever, we need to make sure all the tx suggested by wallets are equal, hence the changes announced to the base fee will be carried out with a delay of 6 blocks or even more. 

The change in base fee cannot be too fast either or to frequent. We can go with a minimum of 20 blocks between changes and a delay of 10 before a base fee change is applied. 

TODO: To calculate base fee we need to define the gas fee for every type of transactions.
TODO: We also need to determine the block capacity, which refers to the total gas a block can process. 

