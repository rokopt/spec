# Inflation system

## Token flow

The protocol controls M1T (the native staking token) sourced from two locations:

1. Fees (50%) paid for transactions per the description above.
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

| Blockchain platform | Approximate locking %       |
|--------------------------------------------------|------|
| Cosmos                                           | 66.7 |
| Polkadot                                         | 50   |
| Ethereum                                         | 47   |
| Solana                                           | 77   |

Our desired percentage for M1 is 33%-66%: Locked for validating and the rest %33-%66 is liquid. When the price of the token is low we can aim for a higher % of locked tokens and reduce this as the price and demand for liquid tokens increases. For example, we can set a range, in the beginning have be 50 % and later aim for 1/3. I dont think we should go lower than that. The staking reward should be ideally set. 

### Related work
Ethereum 2.0, Solana, and Near protocols inflation rate are independent of the how much tokens are staked. Ethereum 2.0, Solana, and Near protocols inflation rate are independent of the how much tokens are staked. Near protocol has an inflation rate of 5% while Ethereum 2.0 has an inflation rate of 1.4% (post EIP-1559). Solana starts with a high inflation rate that decreases over time, as less transaction fees are burnt.

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

The total inflation consists fo several components as follows. 

$I=I_{PoS}+I_L+I_T-D_T$

where $I_T$ is our inflation that goes to treasury, $I_{PoS}$ is inlation that is paid as PoS rewards, and $I_L$ is the inflation for locking that is pait to accounts in shielded pool. We can extend the $I_L$ be extended to be for many other types of $I_L1,...,I_Ln$. For simplicity we only assume to have one $I_L$. $D_T$ is the constant deflation of the treasury. This is applied to incentivize governance voter to spend treasury funds. 

<!--$I_{target}-\alpha<I_t<I_{target}+\alpha$-->

These coponents are each varying depending on independent factors as follows. The $I_{PoS}$ depends on the staking ratio $R_t$. The locking inflation $I_L$ depends on the locking ratio $L_t$. Ideally we want the total token supply cocnsists of tokens locked for staking and shielded pool and the rest are liquid tokens $Y$. 

$T=T*R_t+T*L_t+Y$

where $R_t$ is the target staking ratio and $L_t$ is the target locking of asset in the shielded pool.
  
We assume further assume $I_{target}$ is our target total inflation that we want to achieve on the long term. 

We define $I_{PoS}$ as follows. 

$$ I_{PoS} =
  \begin{cases}
   (max(I_{PoS})/2) (1 + \frac{R}{R_{target} })      & \quad R<R_{target}\\
   \\
   max(I_{PoS})  * 2 ^{-\frac{R-R_{target}}{1-R_{target}}} & \quad R>=R_{target}
  \end{cases}
$$

As an example, we plot the inflation of locked assets $I_L$ with respect to the locking ratio $R_t$ where we assume $R_{target} = 0.5$ and $max(I_{PoS}) = 12%$. 

<img src="https://hackmd.io/_uploads/Hk49PAvZc.png" height="200" />


We define $I_{L}$ as follows. 


$$ I_{L} =
  \begin{cases}
   max(I_L)(\frac{L_{target}-L_t}{L_{target}})      & \quad L<L_{target}\\
   \\
   0 & \quad L>=L_{target}
  \end{cases}
$$

As an example, we plot the inflation of locked assets $I_L$ with respect to the locking ratio $L_t$ with the assumed $L_{target} = 0.5$.

<img src="https://hackmd.io/_uploads/SJDN_0wbq.png" height="200" />

The ratio between staking and locking in shielded pool is a trade off between security and privacy. A higher staking ratio means more security, a higher locking ratio means more privacy. It would be easier to consider these separatly, for example, setting the target staking ratio to 50 % and the target locking ratio to 25 %. 

Funds going to treasury can either be a % of the total infation (such as Near protocol where 5 % goes to treasury) or we can determine how much of total inflation goes to validator rewards and send the rest to treasury (such as Polkadot), in this case total inflation stays constant.

We need to define $max(I_{PoS})$, $max(I_L)$, and $I_T$ to bound total inflation. 

$max(I_{PoS})+max(I_L)+I_T=<max(I)$ 

The sum of $I_L$ and other $I_L1,...,I_Ln$ will also be limited. If their sum would exceed the limit, then we need to scale them down to stay within the limit. 

These bounds on $I_{PoS}$ and $I_L$ give us a min and max bound on the total inflation, where the total inflation depends on $L_t$ and $R_t$ independently. 

