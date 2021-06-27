---
title: Anoma — Implementation Overview Paper
author: Christopher Goes, Awa Sun Yin, Adrian Brink, Anoma R&D Team
fontsize: 9pt
date: \textit{Prerelease, \today}
abstract: |
  Representative currency facilitates exchange by providing a common unit of account, so that parties need not find a counterparty with the exact opposite goods for purchase and sale in order to conduct a trade. Present large-scale financial systems offer this convenience, but restrict the means of exchange, which parties can use, locking economies in to fiat currencies and financial systems, whose governance systems can be captured and leveraged for private ends and bringing with them an intrusive surveillance state. In this paper, we outline how the proposed Anoma protocol can be instantiated with contemporary distributed ledger technology, peer-to-peer networking systems, and cryptographic primitives.
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

The following provides a brief overview of the mechanism by which Anoma instantiates the abstract model outlined in the whitepaper.

# Trade system

## Ledger instantiation

The aforementioned abstract trade system is instantiated using a validity predicate (VP) account model. Like a distributed virtual machine such as the EVM, the ledger contains many independent accounts with their own state subspace and code. Unlike a distributed virtual machine, execution does not proceed in a step-by-step flow where contracts initiate message calls to other contracts. Instead, transactions execute arbitrary code, read and write state as they please, and then all accounts whose state was altered in the course of the transaction decide whether to accept or reject it. The code associated with an account is referred to as a validity predicate, and the validity predicate can also be changed in a transaction (the change being validated by the old validity predicate before being enacted).

In order, a transaction is executed as follows:

1. Arbitrary code is executed in a virtual machine (LLVM/WASM) which can read/write all public state.
    1. The ledger tracks which accounts state was read or written.
    1. The ledger keeps writes in a temporary cache and does not yet commit them.
    1. Separate transactions are parallelized based on the read/write graph with a multi-version concurrency control approach similar to that used in PostgreSQL.
1. All accounts whose state was written during the code execution have the opportunity to accept or reject the transaction.
    1. The accounts validity predicate is called with access to all state changes which occurred and any extra data in the transaction (e.g. proofs).
    1. This validity predicate check is stateless and thus can happen in parallel for any number of involved accounts.
1. The state changes are committed if and only if all involved accounts accept the transaction.

For our purpose of multi-party exchange, this model has several advantages over step-based execution and contract-originating message calls:

- No coordinating contract is required to handle multi-party exchange, and accounts involved in multi-party exchange do not necessarily need to know about each other's existence. Generally speaking, accounts accept transactions as long as certain invariants (e.g. ownership and preservation of supply for a token) are preserved.
- Transaction execution can be much more efficient, since state changes can be directly specified (instead of computed) and only validated by the involved accounts, which can be done in parallel. The possibility of code execution during the first phase allows for limited computation in the case of possibly contentious shared resources (e.g. a counter being incremented).

## Front-running prevention

Adoption of distributed ledgers for use-cases of decentralized exchange is hindered by the ability of block proposers to "front-run" transactions due to their asymmetric game-theoretical advantage over transaction authors. Anoma instantiates a staged threshold decryption scheme to remove this asymmetric advantage and prevent front-running.

### Game-theoretic model

A ledger is executing some state machine, which for the purposes of reasoning about front-running we can completely abstract as an arbitrary transition function. Transactions are submitted to a mempool `M`, which is a gossiped (thus public) unordered set of transactions. At each consensus height `n`, the block proposer `P` selects a subset of transactions from `M` to include in the block `B_n`, and chooses an ordering. Assuming the block metadata is valid, `B_n` is confirmed by the consensus algorithm and the transactions are executed in the chosen order.

In temporal order, for a single transaction, the process of being included in a block is as follows:

1. Transaction `t` submitted by sender to mempool `M`.
	  1. Mempool is gossiped, so anyone can see the transaction data in the mempool.
1. Eventually some block proposer `P` elects to include `t` in a block `B_n`.
	  1. Proposer `P` chooses some ordering for the subset of transactions they include.
    1. Proposer `P` can also create their own transactions and choose to include those.
1. Block `B_n` is accepted and the transactions are executed in the order chosen by the proposer.

The salient feature here is that the mempool is public & the proposer controls the ordering, hence transactions submitted to the mempool leak information which may result in additional transactions being submitted with higher fees, the proposer choosing a different order, or proposer crafting their own transactions, etc. Suppose that all actors have preference functions over the state and the ability to view the current state, monitor the mempool, and submit transactions. Note that the block proposer `A_p` is a particular actor (we can simplify to the case of a single block without loss of generality).

Consider the case of actor `A_j`, who is not the proposer. In a single round, Actor `A_j`:

1. Inspects the current state, `S`.
1. Constructs the set of transactions `{t <- T | P_i (sm s t) s = GT}` such that the result of executing the transaction on the current state is a state which actor `A_j` prefers.
1. Chooses one of these transactions `t_j` to submit to the mempool.
	  1. We can assume that transactions can be chained, so one will be optimal.

Now the proposer `A_p` can do the following:

1. Inspect the current state, `S`.
1. Inspect the mempool `M`, which now contains `t_j`.
1. Construct two possible states, `S` and `S'`, where `S' = sm s t_j`.
1. Construct the set of possible states `s_i` as the union of:
	  1. The current state `S`
	  1. The current state `S` followed by executing `t_j`
	  1. The current state `S` followed by executing `t_p`, some transaction the proposer can submit
	  1. The current state `S` followed by executing `t_j` then `t_p`
	  1. The current state `S` followed by executing `t_p` then `t_j`
	  1. The current state `S` followed by executing `t_p0` then `t_j` then `t_p1`
1. Choose the preferred state according to the proposer's preference function `P_p`.
1. Include the appropriate transactions, in the appropriate order, in the block.

The proposer has a few distinct asymmetric advantages over `A_j` here:

1. The information from `t_j`, which is in the mempool.
	  1. `A_j` does not know about `t_p`, which the proposer might execute.
	  1. The proposer may be able to use this information to craft `t_p`.
	  1. e.g., if `t_j` performs some arbitrage to make profit, the proposer could craft `t_p` to do it themself.
2. The free "option" on whether or not to execute `t_j` and in what order relative to `t_p` to execute it.
	1. For example, `t_p0` could change the price of some asset which `t_j` then purchases, and `t_p1` then sells for a profit.

In order to prevent front-running, these asymmetric advantages need to be eliminated. The most straightforward way to do this is to ensure that the proposer makes ordering choices without any knowledge of the contents of `t_j`, and `t_j` is only executed (and the contents revealed) after an ordering has already been committed to. The proposer can still choose which transactions to include, but they have no information (other than fee amounts) on what data those transactions contain when they choose. This is what Anoma instantiates.

### Cryptographic mechanism

Periodically, validators run a Byzantine-fault tolerant distributed key generation protocol [@dkg-in-the-wild], generating a shared public key and private key shards split among the validators. Before submitting them to the peer-to-peer network, users encrypt transactions to this shared public key. The proposer then includes a set of encrypted transactions in a block, committing to a particular execution order. Once the block has been finalized, the validators run a threshold decryption protocol, each generating and gossiping their share of the decrypted transaction. Once the threshold (likely 2/3) is reached, the decrypted transaction can be submitted again for inclusion in a future block, where it will be executed as soon as all prior transactions (in the previously committed-to execution order) have been decrypted and executed. The block proposer only operates on encrypted transactions about which they have no information and thus possesses no game theoretic advantage over the users. This mechanism introduces a small amount of additional latency between transaction submission and execution, but as the threshold decryption protocol requires no interactions between nodes (only aggregation) this should not exceed an additional consensus round. Threshold decryption has the same fault-tolerance and fault accountability guarantees as BFT consensus.

# Orderbook system

Before any number of parties who might together be able to execute a mutually beneficial trade can do so, they must first be able to find each other. The orderbook system functions as a means of communicating intent to execute a particular trade, and is designed to allow parties to find each other based on the trade they wish to execute while also preserving efficiency and privacy in the case of local negotiation between known parties.

## Liquidity routing

The orderbook system consists of a peer-to-peer gossip network paired with a liquidity incentivisation system which routes a small portion of the surplus value from any executed trade to the peers who gossiped constituent components (signed orders) required to execute it, based on the incentive-compatible protocol described in *On Bitcoin and Red Balloons* [@on-bitcoin-and-red-balloons]. Participants in the gossip network continuously broadcast binding expressions of intent (signed orders, e.g. price quotes on a particular token pair, a bid for a non-fungible CryptoKitty, an acceptable carbon tax rate) and relay and store expressions of intent received from other peers in accordance with their operational costs and expected returns should those expressions result in order settlement on the ledger.

When two nodes first connect to each other, and periodically thereafter, they engage in a negotiation process to determine what sort of liquidity each node is interested in, which the counterparty node will subsequently filter forwarded expressions of intent in accordance with. Nodes which do not respect this filter will be disconnected from. Nodes are expected to update their intents quickly, likely by broadcasting binding intends with expiry dates (based on block height or timestamps) soon in the future and continuously rebroadcasting new intents. Most intents will never result in order settlement individually, but bandwidth and short-term storage are expected to be cheap.

## Privacy preservation

Privacy can be achieved in two ways, depending on the nature of the expressions of intent involved: nodes can construct expressions of intent which do not reveal certain involved parties but include a transfer authorization which can be settled against the ledger and can be verified to have certain contents (e.g. X tokens of Y denomination), and/or nodes can selectively connect to known peers and encrypt data in-transit in order to limit the visibility of their intents. This second method is particularly useful for negotiations which occur between logically proximate devices just prior to settlement, such as at a physical point-of-sale or in an online transaction between known parties, and in the case of physical colocation it is quite possible to use local point-to-point networking protocols (wireless LAN, bluetooth) to perform the negotiation without touching the internet.

# Fractal scaling

A single global orderbook and ledger will not scale to the order gossip and settlement throughputs which can be reasonably expected should the protocol become widely adopted, and even if the scaling problems could be solved such a ledger would present a difficult-to-govern and fragile single point of failure. The topology of order gossip and trade settlement should reflect the topology of the underlying commerce, both to facilitate scaling and to provide local sovereignty and antifragility, such that access to the local orderbook and local ledger is not dependent on globe-spanning internet networks and consensus algorithms. What constitutes "locality" may vary — locality may be geographical, topical, or cultural — geographical locality is most important for geographical fault-tolerance, but topical and cultural locality may also be important for self-sovereignty and memetic antifragility.

Trade settlement should generally happen at the most local layer possible. Separate instances of the protocol will be connected by a cross-chain message passing protocol [@ibc] in order to facilitate asset transfer to and from different global and local layers. Assets can also be locked and directly traded cross-chain without prior transfer. All of this should be cleanly abstracted away from end-user interfaces with automatic selection and cross-chain transfer (subject to appropriate security considerations).

# Upgrade system

The protocol utilizes a directed acyclic upgrade system which allows multiple new versions to be tested in parallel with a sliding scale of value-at-stake.

## Motivation

Initial versions of the ledger, trade settlement, and orderbook protocols will need to evolve and iterate over time in accordance with usage patterns, user feedback, technical developments enabling more performant, private, or secure constituent components, and any discovered bugs or vulnerabilities. Upgrades of distributed systems require both technical coordination, as operators such as validators, peer-to-peer gossip nodes, liquidity providers, and user frontends must agree on which version of the protocol they are using, and social coordination, as various parties wishing to make different changes to different parts of the protocol must coordinate in order to ensure that their changes are compatible and to combine them together in a subsequent version of the software. For certain upgrades, coordination may also be required on liquidity, which will often be tied to a particular version of the protocol.

Countervailing concerns when designing an upgrade system include the requirement not to compromise the security model of the ledger, the desire to avoid subjecting a minority of users to a protocol upgrade they do not wish to enact, and the desire to avoid imposing high operational costs on infrastructure providers.

## Prior efforts

Prior efforts to architect upgrade mechanisms [@tezos] [@cosmos] have focused primarily on voting mechanisms and automation of the processes responsible for delivery, compilation, and activation of new software versions. These efforts are helpful, but they do not address the social coordination problems. Both systems have a "binary switchover" where a new code version is either not yet activated, at best operating in a testnet with nothing at stake, or immediately activated and responsible for stewardship of all asset value from the previous version. This linear version progression and binary switchover prevents multiple new versions from being meaningfully tested at once (with real value at stake and real assets) and requires an extremely conservative software development process to mitigate the risk of bugs in a new software version which will immediately put at risk the entire network should there be a vulnerability.

## Mechanism

The protocol instantiates a directed acyclic upgrade system. Multiple versions can be run in parallel; they must only agree at the cross-chain interface boundary in order to exchange assets and conduct cross-chain trades. Anyone can launch a new version, changing the software as they wish ⁠—any validator can elect to validate, and anyone electing to use the new version can move assets over and start settling trades. Any number of new versions can be tested in parallel, and they can scale up from little value at stake to a reasonable fraction of the prior version of the protocol. The same mechanisms used for cross-chain liquidity sharing and trade settlement between fractal instances can be used between different versions, subject to agreement at the interface boundary.

At any point in logical time, there is one primary ledger, demarcated at the canonical controller of the protocol token and the canonical reporting location for protocol fault accountability remediation procedures. The primary ledger can be atomically switched by a two-thirds majority of the stakeholder set using the usual threshold commitment mechanism (so commitments to different versions can be made; as soon as a version reaches two-thirds the primary ledger switches). New versions may elect to alter the token supply (e.g. allocating themselves some payment for authoring the new software, or paying initial validators of the new chain), and if the primary ledger switch occurs, these alterations are realized. Until then, the usual supply guards apply, so no more tokens can be transferred out of a new version than were initially transferred to it from the primary ledger. The primary ledger may also elect to subsidize testing by minting additional proof-of-stake rewards for software authors and validators, again using the order-based threshold commitment mechanism. A cross-chain validation protocol allows the primary ledger to track the validator set and provide fault accountability for new versions in testing, as desired.

Old versions can remain running for awhile, during which period users can continue to use the old version or transfer assets as they wish, although certain aspects of security will now be dependent on the new primary ledger. After a certain period, validators may prefer to cease validating the old version, at which time state will be automatically migrated by cross-chain message passing before the old version shuts down.

\pagebreak

# References
