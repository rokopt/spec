

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

## Token Inflation
In general, inflation refers to the process of a currency losing its purchasing power over time. While this is a classical economic phenomenon, the way cryptocurrencies are produced permits great control over money supply, and doing so cleverly can have positive effects such as increasing incentives.

Locked tokens help secure the system while liquidity supports its activity and liveness. We need to choose the ratio between locked and liquid token carefully. Liquid tokens make sure the price of the token is not increasing out of scarcity and user have access to tokens to pay transaction fees, while locked tokens are the guaranteeing attacking the system is expensive for an adversary. 

Here are some numbers from other projects

| Blockchain platform | Approximate locking %       | Remarks |
|--------------------------------------------------|------|-----|
| Cosmos                                           | 66.7 |
| Polkadot                                         | 50   |
| Ethereum                                         | 47   |
| Solana                                           | 77   |

Our desired percentage for M1 is 33%-66%: Locked for validating and the rest %33-%66 is liquid. When the price of the token is low we can aim for a higher % of locked tokens and reduce this as the price and demand for liquid tokens increases. For example, we can set a range, in the beginning have be 50 % and later aim for 1/3. I dont think we should go lower than that. The staking reward should be ideally set. 

### Related work
Ethereum 2.0, Solana, and Near protocols inflation rate are independent of the how much tokens are staked. Near protocol and Ethereum 2.0 (Ajinkya, could you please double check this?)have a fixed inflation rates, while Solana start with a high inflation rate that decreases over time, as less transaction fees are burned. 
<!--## Inflation rates for popular platforms
_insert table here_
Solana has the following model where the inflation that is produced for rewards is independent of the staking ratio:
1. Define a starting inflation rate for year 1.
2. The inflation rate decreases thereon at a fixed pace until it reaches a desired rate.
3. Once this desired rate is attained, the inflation rate remains constant.-->

In Polkadot and Cosmos the total inflation rate that is paid as rewards to validators depends on the staking ratio. This is to incentivize validators and delegators to invest in the staking pool. We will follow the same idea and have inflarion vary depending on our target staking ratio. Here is how we achieve that. 

<!--### Inflation model

The total inflation consists of $I_{PoS}$, the inflation rate that is minted to be paid to validators, and the deflation rate, $D_T$.
$$I=I_{PoS} - D_T$$
Where $D_T$ are the funds that are burned from transaction fees. Instead of burning we also can send them to treasury. Same goes with funds that are taken away in form of slashing. We will ignore it and only focus on the calcualtion of $I_{PoS}$.

Let us assume $I_{target}$ is the target of total inflation rate. We want to limit our total inflation as follows. 
$$I_{target}<I_{PoS}<2*I_{target}$$

Moreover, let us assume the staked ratio, $R$, is calculated as 
$$ R = \frac{\textrm{total tokens staked}}{\textrm{total current supply of tokens}}.$$

$R_{target}$ is the target staking ratio that will be important for the PoS security. In Polkadot it is set to be 50% in Cosmos 66%. 


The desired rate is ideally reached after a large number of tokens is generated. Initially, we propose a high inflation rate to generate interest among potential token-holders. The inflation rate would depend on the staked ratio $R$ as follows.
 
$$ I_{PoS} =
  \begin{cases}
   I_{target} (1 + \frac{R}{R_{target} })      & \quad R<R_{target}\\
   \\
   2I_{target}  * 2 ^{-\frac{R-R_{target}}{1-R_{target}}} & \quad R>=R_{target}
  \end{cases}
$$





## Chris Feedback:
- bound the total inflation, but also let it vary a bit so that incentives for proof-of-stake, shielded pool, and governance can be reasonably predictable

- inputs: target staking ratio, target locked tokens for different assets in the shielded pool, target governance public goods funding (rate?), target total inflation rate

- outputs: staking rewards, locked token rewards for different assets, treasury pool

- there is a dependence between staking ratio, shielded pool incentives, governance PGF & the total inflation rate, but basically we should allow the total inflation rate to vary based on the individual P controllers for the first 3 things as long as it stays within bounds
-->

###  Model

Let us assume $T$ is the total token supply and $I$ is total inflation of M1. 

$$I=\frac{T_\textrm{end of year}-T_\textrm{beginning of year}}{T_\textrm{beginning of year}}$$

We assume further assume $I_{target}$ is our target total inflation that we want to achieve on the long term. 

The total inflation consists fo several components as follows. 

$I=I_{PoS}+I_L+I_T$

where $I_T$ is our inflation that goes to treasury, $I_{PoS}$ is inlation that is paid as PoS rewards, and $I_L$ is the inflation for locking that is pait to accounts in shielded pool. We can extend the $I_L$ be extended to be for many other types of $I_L1,...,I_Ln$. For simplicity we only assume to have one $I_L$. 

<!--$I_{target}-\alpha<I_t<I_{target}+\alpha$-->

These coponents are each varying depending on independent factors as follows. The $I_{PoS}$ depends on the staking ratio $R_t$. The locking inflation $I_L$ depends on 
the locking ratio $L_t$. Ideally we want the total token supply cocnsists of tokens locked for staking and shielded pool and the rest are liquid tokens $Y$. 

$T=T*R_t+T*L_t+Y$

where $R_t$ is the target staking ratio and $L_t$ is the target locking of asset in the shielded pool.
  
We define $I_{PoS}$ as follows. 

$$ I_{PoS} =
  \begin{cases}
   (max(I_{PoS})/2) (1 + \frac{R}{R_{target} })      & \quad R<R_{target}\\
   \\
   max(I_{PoS})  * 2 ^{-\frac{R-R_{target}}{1-R_{target}}} & \quad R>=R_{target}
  \end{cases}
$$

![](https://hackmd.io/_uploads/HJpRfOYl9.jpg)

We define $I_{L}$ as follows. 


$$ I_{L} =
  \begin{cases}
   max(I_L)(\frac{L_{target}-L_t}{L_{target}})      & \quad L<L_{target}\\
   \\
   0 & \quad L>=L_{target}
  \end{cases}
$$


![](https://hackmd.io/_uploads/BkR4Qdtg9.jpg)

The ratio between staking and locking in shielded pool is a trade off between security and privacy. A higher staking ratio means more security, a higher locking ratio means more privacy. It would be easier to consider these separatly, for example, setting the target staking ratio to 50 % and the target locking ratio to 25 %. 

Funds going to treasury can either be a % of the total infation (such as Near protocol where 5 % goes to treasury) or we can determine how much of total inflation goes to validator rewards and send the rest to treasury (such as Polkadot), in this case total inflation stays constant.

We need to define $max(I_{PoS})$, $max(I_L)$, and $I_T$ to bound total inflation. 

$max(I_{PoS})+max(I_L)+I_T=<max(I)$ 

The sum of $I_L$ and other $I_L1,...,I_Ln$ will also be limited. If their sum would exceed the limit, then we need to scale them down to stay within the limit. 

These bounds on $I_{PoS}$ and $I_L$ give us a min and max bound on the total inflation, where the total inflation depends on $L_t$ and $R_t$ independently. 

