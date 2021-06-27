---
title: Anoma Token Economics
fontsize: 9pt
author: Christopher Goes, Awa Sun Yin, Adrian Brink
date: \textit{This paper describes possible approaches to incentive design. The contents of this document are subject to change as the project and industry evolve.}
abstract: |
  Anoma is a decentralised private financial settlement layer that provides different kinds of functionality to a broad variety of users. For the system to function as designed, actors such as validators, market makers, and orderbook operators must behave in certain ways, some of which can be defined by compliance to rigid protocols (voting in consensus) and others of which are more open-ended but equally essential (providing liquidity). In order to continuously align the incentives of these involved actors, Anoma has a native token, XAN, which is minted by the protocol and distributed to actors who behave in accordance with the desired functionality of the system as a whole. The native token is also used to shift some amount of network-effect-dependent expected future value to the present to encourage early adoption. This paper describes the actors involved, the roles which they must fill, and the basic mechanisms by which this incentive alignment is accomplished.
urlcolor: cyan
header-includes:
    - \usepackage{fancyhdr}
    - \usepackage{graphicx}
    - \pagestyle{fancy}
    - \fancyhead[RE,LO]{}
    - \fancyhead[LE,Ro]{}
    - \fancyhead[CO,CE]{}
    - \fancyfoot[CO,CE]{\textit{Confidential}}
    - \fancyfoot[LE,RO]{\thepage}
---

\pagebreak
  
# Introduction

The native token XAN is intended to align incentives of network participants of various kinds in order to further the Anoma protocol's aim of providing a decentralised private financial settlement layer. XAN is not a crypto-currency and is not intended to be used as a means of exchange, nor is it a utility token which users must purchase in order to utilise the system. The token has no artificial supply cap and the token base will expand over time as necessary. The mechanics of XAN are designed to provide both continuous alignment for network participants in the long-term and temporary incentives for early adopters to bootstrap Anoma with initial liquidity.

In general, XAN is not designed to be held by users who wish to use Anoma to send payments or barter with each other, but rather by operators such as stakers, validators, and market makers, who are variously required to hold, bond, lock, and transact with the native token in order to align incentives for particular purposes within the operational design of the system.

This paper enumerates permanent core protocol incentives, temporary bootstrapping incentives, incentive mechanics for upgrades, and finally covers miscellaneous state machine features involving the native token.

# Permanent core protocol incentive mechanics

The base protocol requires that actors in certain roles within the system perform particular functions continuously and indefinitely (although the identities of the actors may change). For this purpose, Anoma instantiates permanent mechanisms to align the incentives of these actors. An example of a permanent incentive in another system is the transaction fees paid to proof-of-work miners, which are intended to ensure that miners will converge on a single canonical chain.

## Transaction fees

Two kinds of transaction fees are charged by Anoma: execution fees, proportional to the compute, storage, and memory costs incurred by processing a transaction, and exchange fees, proportional to the value exchanged in a trade. This separation is necessary to ensure both that compute is correctly priced in order to prevent denial-of-service and that the protocol token captures value proportional to the value gained by the parties to the trade, required for long-term security and incentive alignment. Only certain kinds of transactions pay exchange fees — simple transfers do not. The execution fees are further split into a small initial fee, paid prior to threshold decryption and transaction execution, and a second fee to cover the gas required for transaction execution, paid after decryption during execution.

## Proof-of-stake security

Consensus security for Anoma is provided by a proof-of-stake system with a decentralised validator set. Validators must behave according to the rules of the consensus protocol — execute state transitions, commit blocks, etc. — and they can be held liable for Byzantine misbehaviour. In order to vote in consensus, validators must lock tokens in a bond which is held in escrow by the protocol, and released after a delay if and when the validator decides to unbond. Should the validator violate the rules of the protocol, part or all of this bond may be slashed. For their participation in the protocol and correct operation, validators are paid a portion of the execution and exchange fees.

## Distributed key generation & threshold decryption

Front-running protection for Anoma is provided by a distributed key generation and threshold decryption system, operated by a decentralised signer set. In principle, this signer set and the validator set in Anoma's proof-of-stake system may be different, but initially they will likely coincide. Signers must generate key shards according to the rules of the DKG protocol and decrypt transactions after encrypted transactions are submitted to the ledger. In order to participate in this protocol, signers must lock tokens in a bond which is held in escrow by the protocol (initially, this may coincide with the validator bond), and released after a delay if and when they decide to no longer participate. Should they violate the rules of the DKG or threshold decryption protocols, part or all of this bond may be slashed. For their participation in the DKG and threshold decryption protocols and correct operation, signers are paid a portion of the execution and exchange fees.

## Order gossip

Anoma implements an orderbook gossip protocol designed to allow peer-to-peer liquidity routing between nodes. Orderbook operators are responsible for sharing liquidity in the form of signed but not-yet-executed orders with each other and circulating it around the gossip network to whomever requires it. Orders are submitted by third parties such as users to a specific endpoint in the orderbook gossip layer. Without an explicit incentive mechanism, an endpoint receiving an order would have no incentive to share that order with other endpoints as it would not benefit from another party settling the order which it shared. In Anoma, every orderbook operator signs the orders which it shares. When an order is settled in a transaction, every involved orderbook relayer receives a small portion of the exchange fee in compensation for their services. This changes the incentives for rational orderbook operators such that liquidity gossip, not liquidity hoarding, is the optimal strategy.

Market makers, who sign and broadcast orders (and may or may not operate their own nodes in the orderbook gossip network), are expected to sign orders with a built-in spread, so they do not need to receive extra fees from the protocol.

## Order settlement

Once a set of matchable orders has been collected on the gossip network, some party must submit that set in a transaction to the ledger in order to settle the orders, and this party must pay the initial fee for transaction execution since the transaction is initially encrypted. Orders in Anoma reference this order settlement account in order to redirect part of the eventual exchange fee (determined after the transaction is decrypted and executed) to the party who submitted the orders in the transaction for settlement, compensating them for their initial fee payment plus a small bonus.

## Continuous external funding

The token holders, with a 2/3 threshold agreement, have the ability to continually adjust XAN inflation and to issue inflation in XAN to arbitrary accounts in order to fund off-ledger goods, such as protocol development, application development, communications, etc. XAN inflation can be minted once-off as a lump sum payment or continuously as a revocable contract between the protocol and the off-chain entity. This mechanism could also be used to conduct post-facto airdrops to early liquidity providers, market makers, marketplaces, traders, etc.

# Temporary bootstrapping incentive mechanics

Many use-cases of Anoma are valuable in proportion to the available liquidity of assets and orders. This liquidity is subject to network effects, meaning that existing liquidity will eventually provide a natural incentive for more liquidity to join but initial liquidity will have less of a reason to move to the protocol. In order to encourage initial early adoption, Anoma uses temporary bootstrapping incentives to shift some of the expected future value captured by holders of XAN into present value by minting XAN which is then paid to the early adopters. An example of a temporary incentive in another system is the block reward for new Bitcoin blocks, which pays early miners more and diminishes over time as transaction fees are expected to increase.

## Early inflationary block rewards

Early on, transfer and exchange volume in the network will likely be low, so additional inflationary block rewards will be minted by the protocol and paid to the validator set and DKG / threshold decryption signer set in order to cover their operational costs. An automatic inflation adjustment factor may be used to encourage a particular staking ratio and make it difficult for an adversary to rapidly acquire a large portion of the tokens in order to attack the network.

## Bridge incentivisation

Anoma connects to other systems, such as decentralised blockchains or centralised issuing services (i.e. central banks), in order to allow assets to be transferred from those platforms to Anoma, where they can be privately transferred or traded. Initially, transferring assets over these bridges may be perceived as risky since they are relatively novel and may also be illiquid at first. To bootstrap asset availability on Anoma, the protocol implements a temporary bridge transfer incentive. Users who move assets across the bridges and temporarily lock them will be rewarded with newly created XAN tokens. The rate at which these bonus XAN tokens are minted will decrease in proportion to the amount of the asset locked in the bridge, eventually reaching zero once enough assets are locked. Asset bridges so incentivised will be explicitly whitelisted by the stakeholder set.

For example, an Ethereum user can move ETH into Anoma over the ETH-Anoma bridge. The original ETH will be locked for a fixed amount of time (e.g. 6 months) and a derivative ETH token will be issued to the user on Anoma, immediately liquid, which can be redeemed by anyone after the locking period to reclaim the original ETH. At the same time, XAN tokens are minted in an amount correlated to the value of the ETH so locked. The temporary lock is necessary to ETH being recycled back and forth.

This bridge incentivisation scheme also functions as a token distribution mechanism to reward asset-holders that are early adopters of Anoma and provide them with a long-term incentive to support the network with liquidity.

## Early liquidity provision

In order to reward early users of the protocol and widen the token distribution, Anoma implements a temporary partial fee rebate incentive. Part of the execution and exchange fees are converted from whatever tokens they were originally paid in to XAN and returned to all parties who contributed liquidity to a trade. This fee rebate will diminish over time as the available liquidity on the protocol increases.

# Upgrade incentive mechanics

## Threshold commitment signalling

Token holders have the ability to signal their intent by publishing orders and committing to potential upgrades. In order to decide on a new protocol version, token holders must lock their tokens in order to signal their willingness to use the new version. The locked tokens will either become unlocked when the time-period expires or become liquid on the new version after it has been deployed.

# Miscellaneous token incentive mechanics

## Transaction fee conversion

Transaction fees can be paid in arbitrary fungible tokens so that users who simply want to trade between two assets or execute a private transfer don’t have to hold XAN in order to interact with the system. The validator set collectively determines transaction acceptance criteria and fee thresholds for various token denominations. Since validators receiving the transaction fees may not want to manage a large number of denominations, validators can opt to have the protocol automatically convert all of their transaction fees into XAN by market-buying XAN with whatever asset the fee is paid in.

## Dynamic incentive adjustment

The token holders also have the ability to control distribution of execution and exchange fees to actors fulfilling various roles in order to tweak the incentives described herein according to dynamic operational conditions. They can also elect to keep a portion of the execution and exchange fees in an escrow account controlled by the tokenholder set, just like XAN inflation, in order to fund off-chain activities in other tokens or keep a reserve for future incentive purposes.
