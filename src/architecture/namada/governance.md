# Namada Governance

Anoma introduce a governance mechanism to propose and apply protocol changes with and without the need for an hard fork. Anyone holding some `NamadaT` will be able to prosose some changes to which delegators and validator will cast their `yay` or `nay` votes. Governance on Anoma supports both `signaling` and `voting` mechanism. The difference between the the two, is that the former is needed when the changes require an hard fork. In cases where the chain is not able to produce blocks anymore, Anoma relies on `off chain` signaling to agree on a common move.

## On-chain protocol

### Governance Address
Governance adds 2 internal addresses:
- GovernanceAddress
- TreasuryAddress

The first address contains all the proposals under his address space.
The second address holds the funds of rejected proposals.

### Governance storage
Each proposal will be stored in a sub-key under the internal proposal address. The storage keys involved are:
```
/$GovernanceAddress/proposal/$id/content : Vec<u8>
/$GovernanceAddress/proposal/$id/author : Address
/$GovernanceAddress/proposal/$id/startEpoch: Epoch
/$GovernanceAddress/proposal/$id/endEpoch: Epoch
/$GovernanceAddress/proposal/$id/graceEpoch: Epoch
/$GovernanceAddress/proposal/$id/proposalCode: Option<Vec<u8>>
/$GovernanceAddress/proposal/$id/funds: u64
```

`Author` address field will be used to credit the locked funds if the proposal is approved.

The `content` value should follow a standard format. We leverage something similar to what is described in the [BIP2](https://github.com/bitcoin/bips/blob/master/bip-0002.mediawiki#bip-format-and-structure) document:

```json
{
    "title": "<text>",
    "authors": "<authors email addresses> ",
    "discussions-to": "<email address / link>",
    "created": "<date created on, in ISO 8601 (yyyy-mm-dd) format>",
    "license": "<abbreviation for approved license(s)>",
    "abstract": "<text>",
    "motivation": "<text>",
    "details": "<AIP number(s)> - optional field",
    "requires": "<AIP number(s)> - optional field",
}
```

`GovernanceAddress` parameters and global storage keys are:

```
/$GovernanceAddress/?: Vec<u8> 
/$GovernanceAddress/counter: u64
/$GovernanceAddress/min_proposal_fund: u64
/$GovernanceAddress/max_proposal_code_size: u64
/$GovernanceAddress/min_proposal_period: u64
/$GovernanceAddress/max_proposal_content: u64
/$GovernanceAddress/min_proposal_grace_epochs: u64
```

`counter` is used to assign a unique, incremental ID to each proposal.\
`min_proposal_fund` represents the minimum amount of locked tokens to submit a proposal.\
`max_proposal_code_size` is the maximum allowed size (in kilobytes) of the proposal wasm code.\
`min_proposal_period` sets the minimum voting time window (in `Epoch`).\
`max_proposal_content_size` tells the maximum number of characters allowed in the proposal content.\
`min_proposal_grace_epochs` is the minimum required number of `Epoch` between `start_epoch` and `end_epoch`.

The governance machinery also relies on a subkey stored under the `M1T` token address:

```
/$M1TAddress/balance/$GovernanceAddress: u64
```

This is to leverage the `M1T` VP to check that the funds were correctly locked.
The governance subkey, `/$GovernanceAddress/proposal/$id/funds` will be used after the tally step to know the exact amount of tokens to refund/slash.

### GovernanceAddress VP
Just like Pos, also governance has his own storage space. The `GovernanceAddress` validity predicate task is to check the integrity and correctness of new proposals. A proposal, to be correct, must satisfy the followings:
- Lock some funds >= `MIN_PROPOSAL_FUND`
- Contains a unique ID
- Contains a start, end and grace Epoch
- The difference between StartEpoch and EndEpoch should be >= `MIN_PROPOSAL_PERIOD` * constant.
- Should contain a text describing the proposal with length < `MAX_PROPOSAL_CONTENT_SIZE` characters.
- Vote can be done only by a delegator or validator
- Validator can vote only in the initial 2/3 of the whole proposal duration (`EndEpoch` - `StartEpoch`)
- Due to the previous requirement, the following must be true,`(EndEpoch - StartEpoch) % 3 == 0` 
- If defined `proposalCode`, should be the wasm bytecode rappresentation of the changes. This code is triggered in case the proposal has a position outcome.
- `GraceEpoch` should be greater than `EndEpoch` of at least `MIN_PROPOSAL_GRACE_EPOCHS`

`MIN_PROPOSAL_FUND`, `MAX_PROPOSAL_CODE_SIZE`, `MIN_PROPOSAL_GRACE_EPOCHS`, `MAX_PROPOSAL_CONTENT_SIZE` and `MIN_PROPOSAL_PERIOD` are parameters of the protocol.
Once a proposal has been created, nobody can modify any of its fields.
If `proposalCode`  is `Emtpy` or `None` , the proposal upgrade will need to be done via hard fork.

Here an example of such validity predicate.


```rust=
pub fn proposal_vp(tx_data: Vec<u8>, addr: Address, keys_changed: HashSet<Key>, verifiers: HashSet<Address>) {
    for key in keys_changed {
        if is_vote_key(key) {
             return (is_delegator(verifiers) || (is_validator(verifiers) && current_epoch_is_2_3(addr, id))) && is_valid_signature(tx_data);
        } else if is_content_key(key) {
            let post_content = read_post(key)
            return !has_pre(key) && post_content.len() < MAX_PROPOSAL_CONTENT_LENGTH;
        } else if is_author_key(key) {
            return !has_pre(key)  
        } else if is_proposa_code_key(key) {
            let proposal_code_size = get_proposal_code_size();
            return !has_pre(key) && proposal_code_size < MAX_PROPOSAL_CODE_SIZE;
        } else if is_grace_epoch_key(key) {
            let endEpoch = read_post_end_epoch(addr, id, END_EPOCH_KEY)
            let graceEpoch = read_post_grace_epoch(addr, id, GRACE_EPOCH_KEY)
            return !has_pre(key) && graceEpoch > endEpoch;
        } else if is_balance_key(key) {
            let pre_funds = read_funds_pre(key)
            let post_funds = read_funds_post(key)
            let minFunds = read_min_funds_parameter()
            return post_funds - pre_funds >= MIN_PROPOSAL_FUND;          
        } else if is_start_or_end_epoch_key(key) {
            let id = get_id_from_epoch_key(key);
            let currentEpoch = read_current_epoch();
            let minPeriod = read_min_period_parameter();
            let startEpoch = read_post_start_epoch(addr, id, START_EPOCH_KEY);
            let endEpoch = read_post_end_epoch(addr, id, END_EPOCH_KEY)
            return !has_pre(key) && startEpoch - currentEpoch >= MIN_PROPOSAL_PERIOD && (startEpoch - currentEpoch) % MIN_PROPOSAL_PERIOD == 0;
        } else if is_param_key(key) {
            let proposal_id = get_proposal_id();
            return is_tally_positive(proposal_id);
        }
        } else {
            return false;
        }
    }
}

fn is_delegator(verifiers: HashSet<Address>, tx_data: Vec<u8>) -> bool {
    // check if tx_data has been signed by a delegator
    return ...
}

fn is_validator(verifiers: HashSet<Address>, tx_data: Vec<u8>) -> bool {
    // check if tx_data has been signed by a validator
    return ...
}

fn current_epoch_is_2_3(addr: Address, id: u64) -> bool {
    let currentEpoch = read_current_epoch()
    let startEpoch = read_post_start_epoch(addr, id, START_EPOCH_KEY) 
    let endEpoch = read_post_end_epoch(addr, id, END_EPOCH_KEY)
    
    return ((endEpoch - startEpoch) * 2) / 3 <= (currentEpoch - startEpoch);
}

fn is_tally_positive() -> bool {
    // compute if 2/3 voting power voted yay
    return ...
}

```

Example of `proposalCode` could be:
- storage writes to change some protocol parameter
- storage writes to restore a slash

This means that corresponding VPs need to handle these cases.


### Proposal Transactions

The proposal transaction will have the following structure, where `author` address will be the refund address.

```rust=
struct OnChainProposal {
    id: u64
    content: Vec<u8>
    author: Address
    votingStartEpoch: Epoch
    votingEndEpoch: Epoch
    graceEpoch: Epoch
    proposalCode: Option<Vec<u8>>
}
```

### Vote transaction

Vote transactions have the following structure:

```rust=
struct OnChainVote {
    id: u64
    voter: Address
    yay: bool
}
```

Vote transaction creates or modify the following storage key:

```
/$GovernanceAddress/proposal/id/vote/$address: Enum(yay|nay)
```

The storage key will only be created if the transaction is signed either by a validator or a delagator. 
Validators will be able to vote only for 2/3 of the total voting period, meanwhile delegators can vote until the end of the voting period.
If a delegator votes opposite to its validator this will *overri*de the corresponding vote of this validator (e.g. if a delegator has a voting power of 200 and votes opposite to the delegator holding these tokens, than 200 will be subtracted from the votig power of the involved validator).

### Tally
At the beginning of each new epoch (and only then), in the `BeginBlock` event, talling will occur for all the proposals ending at this epoch (specified via the `endEpoch` field).
The proposal has a positive outcome if 2/3 of the staked `NamadaT` total is voting `yay`.
The tally can also be manually computed via CLI command. The tally method behavior will be the following:

```rust=
fn compute_tally(proposal_id: u64) {
    let end_epoch = get_proposal_end_epoch(proposal_id);
    let total_voting_power = get_total_voting_power();
    let vote_addresses = get_proposal_vote_iter(proposal_id).map(|addr| addr);
    let voting_validators = vote_addresses.filter(|addr| addr.is_validator());
    let voting_delegators = vote_addresses.filter(|addr| addr.is_delagator());

    let validators_power: HashMap<Address, VotingPower> = voting_validators.map(|addr| {
        (addr, get_voting_power(addr, end_epoch))
    });

    let yay_validators = voting_validators.filter(|addr| {
        return get_vote_for(addr) == "yay"
    })

    for delegator in voting_delegators {
        let validator: Address = get_validator_for(delegaor);
        let delagator_vote = get_vote_for(delagator);
        if delagator_vote == "yay" && !yay_validators.contains(validator) {
            validators_power[validator] -= get_delegator_voting_power(delegator);
        }
    }

    return sum(validators_power.iter_values()) / total_voting_power >= 0.66;
}
```

### Refund and Proposal Execution mechanism
Together with the talling, in the first block at the beginning of each epoch, in the `BeginBlock` event, the protocol will manage the execution of accepted proposals and refunding. For each ended proposal with positive outcome, it will refund the locked funds from `GovernanceAddress` to the proposal author address (specified in the proposal `author` field). For each proposal that has been rejected, instead, the locked funds will be moved to the `TreasuryAddress`. Moreover, if the proposal had a positive outcome and `proposalCode` was defined, these changes will be executed. Changes are executed in the first block of the `GraceEpoch` defined in the proposal.

If the proposal outcome is positive and current epoch is equal to the proposal `graceEpoch`, in the `BeginBlock` event:
- transfer the locked funds to the proposal author
- execute any changes to storage specified by `proposalCode`

In case the proposal was rejected, in the `BeginBlock` event:
- transfer the locked funds to `TreasuryAddress`

**NOTE**: we need a way to signal the fulfillment of an accepted proposal inside the block in which it is applied to the state. We could do that by using `Events` https://github.com/tendermint/tendermint/blob/ab0835463f1f89dcadf83f9492e98d85583b0e71/docs/spec/abci/abci.md#events (see https://github.com/anoma/anoma/issues/930).

## TreasuryAddress
Funds locked in `TreasuryAddress` address should be spendable only if a 2/3+ voting power accept a proposal which modifies its balance.

### TreasuryAddress storage
```
/$TreasuryAddress/max_spendable_sum: u64
/$TreasuryAddress/?: Vec<u8>
```

The funds will be stored under:
```
/$M1TAddress/balance/$TreasuryAddress: u64
```

### TreasuryAddress VP
```rust=
pub fn governance_fund_pool_vp(tx_data: Vec<u8>, addr: Address, keys_changed: HashSet<Key>, verifiers: HashSet<Address>) {
    for key in keys_changed {
        if is_parameter_key(key) {
            let proposal_id = get_proposal_id();
            let current_epoch = get_current_epoch();
            let proposal_grace_epoch = get_proposal_grace_epoch(proposal_id);
            return is_tally_positive(proposal_id) && current_epoch == proposal_grace_epoch;
        } else {
            return false;
        }
    }
}

fn is_tally_positive(proposal_id: u64) -> bool {
    // compute if 2/3 voting power voted yay
    return ...
}
```

`MAX_SPENDABLE_SUM` is a parameter in of the anoma protocol.

## ParameterAddress
Protocol parameter are described under the $ParameterAddress internal address. Proposals can modify them if 2/3+ voting power agree.

### ParameterAddress storage
```
/$ParamaterAddress/<param>: String
/$ParamaterAddress/?: Vec<u8>
```

### ParameterAddress VP
```rust=
pub fn parameter_vp(tx_data: Vec<u8>, addr: Address, keys_changed: HashSet<Key>, verifiers: HashSet<Address>) {
    for key in keys_changed {
        if is_param_key(key) {
            let proposal_id = get_proposal_id();
            let current_epoch = get_current_epoch();
            let proposal_grace_epoch = get_proposal_grace_epoch();
            return is_tally_positive(proposal_id) && current_epoch == proposal_grace_epoch;
        } else {
            return false;   
        }
    }
}

fn is_tally_positive(proposal_id: u64) -> bool {
    // compute if 2/3 voting power voted yay
    return ...
}
```

## Off-chain protocol

### Create proposal
A CLI command to create a signed JSON rappresentation of the proposal. The JSON will have the following structure:
```
{
  content: Base64<Vec<u8>>,
  author: Address,
  votingStart: TimeStamp,
  votingEnd: TimeStamp,
  signature: Base64<Vec<u8>>
}
```

The signature is produced over the hash of the concatenation of `content`, `author`, `votingStart` and `votingEnd`.

### Create vote

A CLI command to create a signed JSON rappresentation of a vote. The JSON will have the following structure:
```
{
  proposalHash: Base64<Vec<u8>>,
  voter: Address,
  signature: Base64<Self.proposalHash>,
  vote: Enum(yay|nay)
}
```

The proposalHash is produced over the concatenation of `content`, `author`, `votingStart`, `votingEnd`, `voter` and `vote`.

### Tally
Same mechanism as OnChain tally but instead of reading the data from storage it will require a list of serialized json votes.

## Interfaces

- Ledger CLI
- Wallet
