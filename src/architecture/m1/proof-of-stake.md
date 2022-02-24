# Proof of Stake (PoS)

This specification should cover
- Proof-of-stake bonding mechanism (already covered in ledger docs)
- Slashing mechanism & infractions for all of the Tendermint-recognised faults.
- Rewards & distribution

## Introduction
Blockchain system rely on economic security to prevent abuse and for actors to behave according to protocol. The aim is that economic incentive promote correct and long-term operation of the system and economic punishments would discourage diverting from correct protocol execution either by mistake or with the intent to carrying out attacks. Many PoS blockcains rely on the 1/3 Byzantine rule, where they make the assumption the adversary cannot control more 2/3 of the total stake or 2/3 of the actors. 

## Goals of Rewards and Slashing: Liveness and Security

* **Security: Delegation and Slashing**: we want to make sure  validators backed by enough funds to make misbehaviour very expensive. Security is achieved by punishing (slashing) if they do. *Slashing* locked funds (stake) intends to disintensivize diverting from correct execution of protocol, which is this case is voting to finalize valid blocks. 
* **Liveness: Paying Rewards**. For continued operation of M1 we want to incentivize participating in consensus and delegation, which helps security.


### Security 
In blockchain system we do not rely on altruistic behavior but rather economic security. We expect the validators to execute the protocol correctly. They get rewarded for doing so and punished otherwise. Each validator has some self-stake and some stake that is delegated to it by other token holders. The validator and delegators share the reward and risk of slashing impact with each other. 

The total stake behind consensus should be taken into account when value is transferred via a transaction. The total value transferred cannot exceed 2/3 of the total stake. For example, if we have 1 billion tokens, we aim that 300 Million of these tokens is backing validators. This means that users should not transfer more than 200 million of this token within a block. 


## Epoch

An epoch is a range of blocks or time that is defined by the base ledger and made available to the PoS system. This document assumes that epochs are identified by consecutive natural numbers. All the data relevant to PoS are [associated with epochs](#epoched-data).

### Epoched data

Epoched data are data associated with a specific epoch that are set in advance. The data relevant to the PoS system in the ledger's state are epoched. Each data can be uniquely identified. These are:
- [System parameters](#system-parameters). A single value for each epoch.
- [Active validator set](#active-validator-set). A single value for each epoch.
- Total voting power. A sum of all active and inactive validators' voting power. A single value for each epoch.
- [Validators' consensus key, state and total bonded tokens](#validator). Identified by the validator's address.
- [Bonds](#bonds) are created by self-bonding and delegations. They are identified by the pair of source address and the validator's address.

Changes to the epoched data do not take effect immediately. Instead, changes in epoch `n` are queued to take effect in the epoch `n + pipeline_length` for most cases and `n + unboding_length` for [unbonding](#unbond) actions. Should the same validator's data or same bonds (i.e. with the same identity) be updated more than once in the same epoch, the later update overrides the previously queued-up update. For bonds, the token amounts are added up. Once the epoch `n` has ended, the queued-up updates for epoch `n + pipeline_length` are final and the values become immutable.

## Entities

- [Validator](#validator): An account with a public consensus key, which may participate in producing blocks and governance activities. A validator may not also be a delegator.
- [Delegator](#delegator): An account that delegates some tokens to a validator. A delegator may not also be a validator.

Additionally, any account may submit evidence for [a slashable misbehaviour](#slashing).

### Validator

A validator must have a public consensus key. Additionally, it may also specify optional metadata fields (TBA).

A validator may be in one of the following states:
- *inactive*:
  A validator is not being considered for block creation and cannot receive any new delegations.
- *pending*:
  A validator has requested to become a *candidate*.
- *candidate*:
  A validator is considered for block creation and can receive delegations.

For each validator (in any state), the system also tracks total bonded tokens as a sum of the tokens in their self-bonds and delegated bonds, less any unbonded tokens. The total bonded tokens determine their voting voting power by multiplication by the `votes_per_token` [parameter](#system-parameters). The voting power is used for validator selection for block creation and is used in governance related activities.

#### Validator actions

- *become validator*:
  Any account that is not a validator already and that doesn't have any delegations may request to become a validator. It is required to provide a public consensus key and staking reward address. For the action applied in epoch `n`, the validator's state will be immediately set to *pending*, it will be set to *candidate* for epoch `n + pipeline_length` and the consensus key is set for epoch `n + pipeline_length`.
- *deactivate*:
  Only a *pending* or *candidate* validator account may *deactivate*. For this action applied in epoch `n`, the validator's account is set to become *inactive* in the epoch `n + pipeline_length`.
- *reactivate*:
  Only an *inactive* validator may *reactivate*. Similarly to *become validator* action, for this action applied in epoch `n`, the validator's state will be immediately set to *pending* and it will be set to *candidate* for epoch `n + pipeline_length`.
- *self-bond*:
  A validator may lock-up tokens into a [bond](#bonds) only for its own validator's address.
- *unbond*:
  Any self-bonded tokens may be partially or fully [unbonded](#unbond).
- *withdraw unbonds*:
  Unbonded tokens may be withdrawn in or after the [unbond's epoch](#unbond).
- *change consensus key*:
  Set the new consensus key. When applied in epoch `n`, the key is set for epoch `n + pipeline_length`.

#### Active validator set

From all the *candidate* validators, in each epoch the ones with the most voting power limited up to the `max_active_validators` [parameter](#system-parameters) are selected for the active validator set. The active validator set selected in epoch `n` is set for epoch `n + pipeline_length`.

### Delegator

A delegator may have any number of delegations to any number of validators. Delegations are stored in [bonds](#bonds).

#### Delegator actions

- *delegate*:
  An account which is not a validator may delegate tokens to any number of validators. This will lock-up tokens into a [bond](#bonds).
- *undelegate*:
  Any delegated tokens may be partially or fully [unbonded](#unbond).
- *withdraw unbonds*:
  Unbonded tokens may be withdrawn in or after the [unbond's epoch](#unbond).

## Bonds

A bond locks-up tokens from validators' self-bonding and delegators' delegations. For self-bonding, the source address is equal to the validator's address. Only validators can self-bond. For a bond created from a delegation, the bond's source is the delegator's account.

For each epoch, bonds are uniquely identified by the pair of source and validator's addresses. A bond created in epoch `n` is written into epoch `n + pipeline_length`. If there already is a bond in the epoch `n + pipeline_length` for this pair of source and validator's addresses, its tokens are incremented by the newly bonded amount.

Any bonds created in epoch `n` increment the bond's validator's total bonded tokens by the bond's token amount and update the voting power for epoch `n + pipeline_length`.

The tokens put into a bond are immediately deducted from the source account.

### Unbond

An unbonding action (validator *unbond* or delegator *undelegate*) requested by the bond's source account in epoch `n` creates an "unbond" with epoch set to `n + unbounding_length`. We also store the epoch of the bond(s) from which the unbond is created in order to determine if the unbond should be slashed if a fault occurred within the range of bond epoch (inclusive) and unbond epoch (exclusive).

Any unbonds created in epoch `n` decrements the bond's validator's total bonded tokens by the bond's token amount and update the voting power for epoch `n + unbonding_length`.

An "unbond" with epoch set to `n` may be withdrawn by the bond's source address in or any time after the epoch `n`. Once withdrawn, the unbond is deleted and the tokens are credited to the source account.

### Staking rewards
Rewards are given to validators for voting on finalizing blocks: the fund for these rewards can come from **minting** _can we just say a word about what minting is?_. The amount that is minted depends on how much is staked and our desired yearly inflation. When the total of the tokens staked is very low, the return rate per validator needs to increase, but as the total amount of stake rises, validators will receive less rewards. Once we have acquired the desired stake percentage, the amount minted will just be the desired yearly inflation. 

Once we have calculated the total that needs to be minted at the end of the epoch, we split the minted tokens according to the stake they(_by "they" do you mean the relevant validators and delegators?_) contributed (i.e., Cosmos _what does this mean?_) and distribute them to validators and their delegators (_should this be "delegeators and their validators?"_). The validator and the delegator must have agreed on a commission rate between themselves. Delegators pay out rewards to validators based on a mutually-determined commission rate that both parties must have agreed upon beforehand. The minted rewards are auto-bonded and only transferred when the funds are unbonded. 


Until we have programmable validity predicates, rewards can use the mechanism outlined in the [F1 paper](https://drops.dagstuhl.de/opus/volltexte/2020/11974/pdf/OASIcs-Tokenomics-2019-10.pdf), but it should use the exponential model, so that withdrawing rewards more frequently provides no additional benefit (this is a design constraint we should follow in general, we don't want to accidentally encourage transaction spam). This should be written in a way that allows for a natural upgrade to a validator-customisable rewards model (defaulting to this one) if possible.

To a validator who proposed a block, the system rewards tokens based on the `block_proposer_reward` [system parameter](#system-parameters) and each validator that voted on a block receives `block_vote_reward`.

### Slashing

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


Instead of absolute values, validators' total bonded token amounts and bonds' and unbonds' token amounts are stored as their deltas (i.e. the change of quantity from a previous epoch) to allow distinguishing changes for different epoch, which is essential for determining whether tokens should be slashed. However, because slashes for a fault that occurred in epoch `n` may only be applied before the beginning of epoch `n + unbonding_length`, in epoch `m` we can sum all the deltas of total bonded token amounts and bonds and unbond with the same source and validator for epoch equal or less than `m - unboding_length` into a single total bonded token amount, single bond and single unbond record. This is to keep the total number of total bonded token amounts for a unique validator and bonds and unbonds for a unique pair of source and validator bound to a maximum number (equal to `unbonding_length`).

To disincentivize validators misbehaviour in the PoS system a validator may be slashed for any fault that it has done. An evidence of misbehaviour may be submitted by any account for a fault that occurred in epoch `n` anytime before the beginning of epoch `n + unbonding_length`.

A valid evidence reduces the validator's total bonded token amount by the slash rate in and before the epoch in which the fault occurred. The validator's voting power must also be adjusted to the slashed total bonded token amount. Additionally, a slash is stored with the misbehaving validator's address and the relevant epoch in which the fault occurred. When an unbond is being withdrawn, we first look-up if any slash occurred within the range of epochs in which these were active and if so, reduce its token amount by the slash rate. Note that bonds and unbonds amounts are not slashed until their tokens are withdrawn.

The invariant is that the sum of amounts that may be withdrawn from a misbehaving validator must always add up to the total bonded token amount.


## System parameters

The default values that are relative to epoch duration assume that an epoch last about 24 hours.

- `max_validator_slots`: Maximum active validators, default `128`
- `pipeline_len`: Pipeline length in number of epochs, default `2`
- `unboding_len`: Unbonding duration in number of epochs, default `6`
- `votes_per_token`: Used in validators' voting power calculation, default 100‱ (1 voting power unit per 1000 tokens)
- `block_proposer_reward`: Amount of tokens rewarded to a validator for proposing a block
- `block_vote_reward`: Amount of tokens rewarded to each validator that voted on a block proposal
- `duplicate_vote_slash_rate`: Portion of validator's stake that should be slashed on a duplicate vote
- `light_client_attack_slash_rate`: Portion of validator's stake that should be slashed on a light client attack

## Storage

The [system parameters](#system-parameters) are written into the storage to allow for their changes. Additionally, each validator may record a new parameters value under their sub-key that they wish to change to, which would override the systems parameters when more than 2/3 voting power are in agreement on all the parameters values.

The validators' data are keyed by the their addresses, conceptually:

```rust,ignore
type Validators = HashMap<Address, Validator>;
```

Epoched data are stored in the following structure:
```rust,ignore
struct Epoched<Data> {
  /// The epoch in which this data was last updated
  last_update: Epoch,
  /// Dynamically sized vector in which the head is the data for epoch in which 
  /// the `last_update` was performed and every consecutive array element is the
  /// successor epoch of the predecessor array element. For system parameters, 
  /// validator's consensus key and state, `LENGTH = pipeline_length + 1`. 
  /// For all others, `LENGTH = unbonding_length + 1`.
  data: Vec<Option<Data>>
}
```

Note that not all epochs will have data set, only the ones in which some changes occurred.

To try to look-up a value for `Epoched` data with independent values in each epoch (such as the active validator set) in the current epoch `n`:

1. let `index = min(n - last_update, pipeline_length)`
1. read the `data` field at `index`:
   1. if there's a value at `index` return it
   1. else if `index == 0`, return `None`
   1. else decrement `index` and repeat this sub-step from 1.

To look-up a value for `Epoched` data with delta values in the current epoch `n`:

1. let `end = min(n - last_update, pipeline_length) + 1`
1. sum all the values that are not `None` in the `0 .. end` range bounded inclusively below and exclusively above

To update a value in `Epoched` data with independent values in epoch `n` with value `new` for epoch `m`:

1. let `shift = min(n - last_update, pipeline_length)`
1. if `shift == 0`:
   1. `data[m - n] = new`
1. else:
   1. for `i in 0 .. shift` range bounded inclusively below and exclusively above, set `data[i] = None`
   1. rotate `data` left by `shift`
   1. set `data[m - n] = new`
   1. set `last_update` to the current epoch

To update a value in `Epoched` data with delta values in epoch `n` with value `delta` for epoch `m`:

1. let `shift = min(n - last_update, pipeline_length)`
1. if `shift == 0`:
   1. set `data[m - n] = data[m - n].map_or_else(delta, |last_delta| last_delta + delta)` (add the `delta` to the previous value, if any, otherwise use the `delta` as the value)
1. else:
   1. let `sum` to be equal to the sum of all delta values in the `i in 0 .. shift` range bounded inclusively below and exclusively above and set `data[i] = None`
   1. rotate `data` left by `shift`
   1. set `data[0] = data[0].map_or_else(sum, |last_delta| last_delta + sum)`
   1. set `data[m - n] = delta`
   1. set `last_update` to the current epoch

The invariants for updates in both cases are that `m - n >= 0` and `m - n <= pipeline_length`.

For the active validator set, we store all the active and inactive validators separately with their respective voting power:
```rust,ignore
type VotingPower = u64;

/// Validator's address with its voting power.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct WeightedValidator {
  /// The `voting_power` field must be on top, because lexicographic ordering is
  /// based on the top-to-bottom declaration order and in the `ValidatorSet`
  /// the `WeighedValidator`s these need to be sorted by the `voting_power`.
  voting_power: VotingPower,
  address: Address,
}

struct ValidatorSet {
  /// Active validator set with maximum size equal to `max_active_validators`
  active: BTreeSet<WeightedValidator>,
  /// All the other validators that are not active
  inactive: BTreeSet<WeightedValidator>,
}

type ValidatorSets = Epoched<ValidatorSet>;

/// The sum of all active and inactive validators' voting power
type TotalVotingPower = Epoched<VotingPower>;
```

When any validator's voting power changes, we attempt to perform the following update on the `ActiveValidatorSet`:

1. let `validator` be the validator's address, `power_before` and `power_after` be the voting power before and after the change, respectively
1. let `power_delta = power_after - power_before`
1. let `min_active = active.first()` (active validator with lowest voting power)
1. let `max_inactive = inactive.last()` (inactive validator with greatest voting power)
1. find whether the validator is active, let `is_active = power_before >= max_inactive.voting_power`
   1. if `is_active`:
      1. if `power_delta > 0 && power_after > max_inactive.voting_power`, update the validator in `active` set with `voting_power = power_after`
      1. else, remove the validator from `active`, insert it into `inactive` and remove `max_inactive.address` from `inactive` and insert it into `active`
   1. else (`!is_active`):
      1. if `power_delta < 0 && power_after < min_active.voting_power`, update the validator in `inactive` set with `voting_power = power_after`
      1. else, remove the validator from `inactive`, insert it into `active` and remove `min_active.address` from `active` and insert it into `inactive`

Within each validator's address space, we store public consensus key, state, total bonded token amount and voting power calculated from the total bonded token amount (even though the voting power is stored in the `ValidatorSet`, we also need to have the `voting_power` here because we cannot look it up in the `ValidatorSet` without iterating the whole set):

```rust,ignore
struct Validator {
  consensus_key: Epoched<PublicKey>,
  state: Epoched<ValidatorState>,
  total_deltas: Epoched<token::Amount>,
  voting_power: Epoched<VotingPower>,
}

enum ValidatorState {
  Inactive,
  Pending,
  Candidate,
}
```

The bonds and unbonds are keyed by their identifier:

```rust,ignore
type Bonds = HashMap<BondId, Epoched<Bond>>;
type Unbonds = HashMap<BondId, Epoched<Unbond>>;

struct BondId {
  validator: Address,
  /// The delegator adddress for delegations, or the same as the `validator`
  /// address for self-bonds.
  source: Address,
}

struct Bond {
  /// A key is a the epoch set for the bond. This is used in unbonding, where
  // it's needed for slash epoch range check.
  deltas: HashMap<Epoch, token::Amount>,
}

struct Unbond {
  /// A key is a pair of the epoch of the bond from which a unbond was created
  /// the epoch of unboding. This is needed for slash epoch range check.
  deltas: HashMap<(Epoch, Epoch), token::Amount>
}
```

For slashes, we store the epoch and block height at which the fault occurred, slash rate and the slash type:

```rust,ignore
struct Slash {
  epoch: Epoch,
  block_height: u64,
  /// slash token amount ‱ (per ten thousand)
  rate: u8,
  r#type: SlashType,
}
```

## Initialization

An initial validator set with self-bonded token amounts must be given on system initialization.

This set is used to pre-compute epochs in the genesis block from epoch `0` to epoch `pipeline_length - 1`.

## Cubic slashing

"Collective (escalated slashing) : If more than a certain threshold of users commit an offence, then slashing will be escalated. We would like to implement quadratic slashing. If the offender is holding less than 1% of stake the slashing will be small and it will escalate to 100 % if the offenders hold up to 1/3 of the total stake."

Case to think of:
- Slash detected right before end of epoch 10
- Slash detected right after start of epoch 11
    - probably these should be counted as within the same period for the purpose of quadratic slashing

When a slash is detected:
1. Enqueue the slash for processing _at the end of the epoch after the current epoch_ (if slash is detected in epoch 10, processing is scheduled for the end of epoch 11)
2. Jail the validator in question (this will apply at the end of the current epoch, so 10 in this example)
3. Prevent the delegators to this validator from altering their delegations in any way until the enqueued slash is processed

At the end of each epoch, in order to process any slashes scheduled for processing at the end of that epoch:
1. Iterate over all slashes detected in the past 2 epochs.
2. Calculate the slash rate according to the following function:

_Note: the voting power of a slash is the voting power of the validator **when they violated the protocol**, not the voting power now. This does mean that these voting powers may not sum to 1, but this method should still be close to the incentives we want, and can't really be changed without making the system easier to game._

```typescript=
function calculateSlashRate(slashes) {
  votingPowerFraction = 0
  for slash in slashes:
    votingPowerFraction += slash.validator.votingPowerFraction
  return max(0.01, min(1, votingPowerFraction**2 * 9))
  // minimum slash rate is 1%
  // then exponential between 0 & 1/3 voting power
  // we can make this a more complex function later
}
```

3. Set the slash rate on the now "finalised" slash in storage
4. Update the validators' stored voting power appropriately
5. Delegations to the validator can now be redelegated / start unbonding / etc.

Validator can later submit a transaction to unjail themselves after a configurable period.

Where does the slash amount go? For now, governance treasury.

_In the future we could potentially reward the slash discoverer with part of the slash, we need commit-reveal._
