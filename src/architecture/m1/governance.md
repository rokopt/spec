# M1 Governance

Anoma introduce a governance mechanism to propose and apply protocol changes with and without the need for an hard fork. Anyone holding some `M1T` will be able to prosose some changes to which delegators and validator will cast their `yay` or `nay` votes. Governance on Anoma supports both `signaling` and `voting` mechanism. The difference between the the two, is that the former is needed when the changes require an hard fork. In cases where the chain is not able to produce blocks anymore, Anoma relies on `off chain` signaling to agree on a common move.

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
/$GovernanceAddress/proposal/$id: u64
/$GovernanceAddress/proposal/$id/content : Vec<u8>
/$GovernanceAddress/proposal/$id/author : Address
/$GovernanceAddress/proposal/$id/startEpoch: Epoch
/$GovernanceAddress/proposal/$id/endEpoch: Epoch
/$GovernanceAddress/proposal/$id/proposalCode: Option<Vec<u8>>
/$GovernanceAddress/proposal/$id/funds: u64
```

`Author` address field will be used to credit the locked funds if the proposal is approved.

`GovernanceAddress` global storage keys are:

```
/$GovernanceAddress/?: Vec<u8> 
/$GovernanceAddress/counter: u64
```

`Counter` is used to assign a unique, incremental ID to each proposal.

### GovernanceAddress VP
Just like Pos, also governance has his own storage space. The `GovernanceAddress` validity predicate task is to check the integrity and correctness of new proposals. A proposal, to be correct, must satisfy the followings:
- Lock some funds >= `MIN_PROPOSAL_FUND`
- Contains a unique ID
- Contains a start, end and grace Epoch
- The difference between StartEpoch and EndEpoch should be >= `MIN_PROPOSAL_PERIOD` * constant.
- Should contain a text describing the proposal with length < `MAX_PROPOSAL_CONTENT_LENGTH` characters.
- Vote can be done only by a delegator or validator
- Validator can vote only in the initial 2/3 of the whole proposal duration (`EndEpoch` - `StartEpoch`)
- Due to the previous requirement, the following must be true,`(EndEpoch - StartEpoch) % 3 == 0` 
- If defined `proposalCode`, should be the wasm bytecode rappresentation of the changes. This code is triggered in case the proposal has a position outcome.

`MIN_PROPOSAL_FUND`, `MAX_PROPOSAL_CODE_SIZE` and `MIN_PROPOSAL_PERIOD` are parameters of the protocol.
Once a proposal has been created, nobody can modify any of its fields.
If `proposalCode`  is `Emtpy` or `None` , the proposal upgrade will need to be done via hard fork.

Here an example of such validity predicate.


```rust=
pub fn proposal_vp(tx_data: Vec<u8>, addr: Address, keys_changed: HashSet<Key>, verifiers: HashSet<Address>) {
    for key in keys_changed {
        if is_proposal_key_id(key) {
            let current_id = read_counter();
            let proposal_id = get_current_proposal_id();
            let post_value_counter = read_post(COUNTER_STORAGE_KEY);
            return !has_pre(key) && current_id == proposal_id && post_value_counter == current_id++;
        } else if is_vote_key(key) {
             return (is_delegator(verifiers) || (is_validator(verifiers) && current_epoch_is_2_3(addr, id))) && is_valid_signature(tx_data);
        } else if is_content_key(key) {
            let post_content = read_post(key)
            return !has_pre(key) && post_content.len() < MAX_PROPOSAL_CONTENT_LENGTH;
        } else if is_author_key(key) {
            return !has_pre(key)  
        } else if is_proposa_code_key(key) {
            let proposal_code_size = get_proposal_code_size();
            return !has_pre(key) && proposal_code_size < MAX_PROPOSAL_CODE_SIZE;
        } else if is_grace_epoch(key) {
            let endEpoch = read_post_end_epoch(addr, id, END_EPOCH_KEY)
            let graceEpoch = read_post_grace_epoch(addr, id, GRACE_EPOCH_KEY)
            return !has_pre(key) && graceEpoch > endEpoch;
        } else if is_balance_key(key) {
            let has_pre_funds = has_pre_key(key)
            let pre_funds = read_funds_pre(key)
            let post_funds = read_funds_post(key)
            let minFunds = read_min_funds_parameter()
            // if new proposal
            if !has_pre_funds {
                return post_funds - pre_funds >= MIN_PROPOSAL_FUND;        
            } else {
                // return funds to owner or governance fund pool
                let currentEpoch = read_current_epoch()
                let endEpoch = read_post_end_epoch(addr, id, END_EPOCH_KEY)
                return currentEpoch >= endEpoch && is_allowed_transfer(verifiers);
            }   
        } else if is_start_or_end_epoch_key(key) {
            let id = get_id_from_epoch_key(key);
            let currentEpoch = read_current_epoch();
            let minPeriod = read_min_period_parameter();
            let startEpoch = read_post_start_epoch(addr, id, START_EPOCH_KEY);
            let endEpoch = read_post_end_epoch(addr, id, END_EPOCH_KEY)
            return !has_pre(key) && startEpoch - currentEpoch >= MIN_PROPOSAL_PERIOD && (startEpoch - currentEpoch) % MIN_PROPOSAL_PERIOD == 0;
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
    
fn is_allowed_transfer(verifiers: Vec<Address>) -> bool {
    // check if the transfer to towards a whitelisted address. 
    // Transfer can be towers TreasuryAddress if the proposal is rejected 
    // or author if proposal is accepted
    // this method must be called only if currentEpoch > proposal.endEpoch
    return ....
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
The proposal has a positive outcome if 2/3 of the staked `M1T` total is voting `yay`.
The tally can also be manually computed via CLI command. The tally method behavior will be the following:

```rust=
fn compute_tally(proposal_id: u64) {
    let vote_addresses = get_proposal_vote_iter(proposal_id).map(|addr| addr)
    let total_m1t: u64 = vote_addresses.reduce(|acc, addr| acc + get_addr_balance(addr), 0)
    
    let delegators =  vote_addresses.filter(|addr| addr.is_delegator())
    let yay_addresses = vote_addresses.filter(|addr| read_vote(proposal_id, addr) == 'yay')
    
    let yay_validators = yay_addresses.filter(|addr| addr.is_validator())
    let yay_validators_m1t = yay_validator.reduce(|acc, addr| acc + get_addr_balance(addr), 0)
    
    for delegator in delegators {
        if yay_validators.contains(delegator.get_correspoding_validator()) {
            if read_vote(proposal_id, delegator) == 'nay' {
                yay_validators_m1t -= get_addr_balance(delegator)
            }
        }
    }
    return yay_validators_m1t / total_m1t >= 0.66;
}
```

### Refund and Proposal Execution mechanism
Together with the talling, in the first block at the beginning of each epoch, in the `BeginBlock` event, the protocol will manage the execution of accepted proposals and refunding. For each ended proposal with positive outcome, it will refund the locked funds from `GovernanceAddress` to the proposal author address (specified in the proposal `author` field). For each proposal that has been rejected, instead, the locked funds will be moved to the `TreasuryAddress`. Moreover, if the proposal had a positive outcome and `proposalTxCode` was defined, these changes will be executed. Changes are execute in the first block of the `GraceEpoch` defined in the proposal.


If the proposal outcome is positive and current epoch is equal to the proposal `graceEpoch`, the `BeginBlock`
- transfer the locked funds to the proposal author (no tx, directly write keys to storage)
- execute any changes to storage specified by `proposalCode`

A `RejectProposal` transaction must:
- transfer the locked funds to the `TreasuryAddress`

**NOTE**: we need a way to signal the fulfillment of an accepted proposal inside the block in which it is applied to the state. We could do that by using `Events` https://github.com/tendermint/tendermint/blob/ab0835463f1f89dcadf83f9492e98d85583b0e71/docs/spec/abci/abci.md#events (see https://github.com/anoma/anoma/issues/930).

## TreasuryAddress
Funds locked in `TreasuryAddress` address should be spendable only if a 2/3+ voting power accept a proposal which modifies its balance.

### TreasuryAddress storage
```
/$TreasuryAddress/balance: u64
/$TreasuryAddress/?: Vec<u8>
```

### TreasuryAddress VP
```rust=
pub fn governance_fund_pool_vp(tx_data: Vec<u8>, addr: Address, keys_changed: HashSet<Key>, verifiers: HashSet<Address>) {
    for key in keys_changed {
        if is_balance_key(key) {
            let pre_balance = read_pre(key);
            let post_balance = read_post(key);
            let to_be_spent = post_balance - pre_balance;
            let proposal_min_lock_funds = read_min_proposal_fund();
            // if credit
            if to_be_spent >= proposal_min_lock_funds {
                return true
            }
            // if debit
            let proposal_id = get_proposal_id();
            let current_epoch = get_current_epoch();
            let proposal_grace_epoch = get_proposal_grace_epoch();
            return is_tally_positive(proposal_id) && current_epoch == proposal_grace_epoch && abs(to_be_spent) < MAX_SPENDABLE_SUM;
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
/$ParamaterAddress/$param: String
/$ParamaterAddress/?: Vec<u8>
```
We need to keep track of already executed proposals.

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
