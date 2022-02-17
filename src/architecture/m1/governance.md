# M1 Governance Spec Sketch

- "Governance signalling mechanism"
    - "polling mechanism"
- Protocol for voting on text
    - Ties the proof-of-stake system to a voting protocol

## Datatypes in the protocol

```rust
struct OnChainProposal {
  id: u64
  content: Vec<u8>
  author: Address
  votingStartEpoch: Epoch
  votingEndEpoch: Epoch
}
```

```rust
struct OffChainProposal {
  content: Vec<u8>
  author: Address
  votingStartTime: Timestamp 
  votingEndTime: Timestamp
}
```

```rust
struct VoteOnChain {
    proposalId: u64
    signature: Vec<u8>
    voter: Address
    yay: bool
}
```

```rust=
struct VoteOffChain {
    proposalHash: Vec<u8>
    signature: Vec<u8>
    voter: Address
    yay: bool
}
```

## On-chain protocol

### Governance Address/VP
Governance should have his own storage space as PoS. The validity predicate should behave in the following way:


```rust
pub fn proposal_vp(tx_data: Vec<u8>, addr: Address, keys_changed: HashSet<Key>, verifiers: HashSet<Address>) {
    for each key in modified_key:
        if is_proposal_key_id(key) {
            return !has_read_pre(key)
        } else if is_vote_key(key) {
             return (is_delegator(verifiers) || (is_validator(verifiers) && current_epoch_is_2_3(addr, id))) && is_valid_signature(tx_data);
        } else if is_content_key(key) {
            let post_content = read_post(key)
            return !has_read_pre(key) && post_content.len() < 500;
        } else if is_author_key(key) {
            return !has_read_pre(key) && true    
        } else if is_balance_key(key) {
            let pre_balance = read_balance_pre(key)
            let post_balance = read_balance_post(key)
            return post_balance - pre_balance <= 50;
        } else if is_start_or_end_epoch_key(key) {
            let id = get_id_from_epoch_key(key)
            let currentEpoch = read_current_epoch()
            let minPeriod = read_min_period()
            let startEpoch = read_post_start_epoch(addr, id, START_EPOCH_KEY) 
            let endEpoch = read_post_end_epoch(addr, id, END_EPOCH_KEY)
            
            return !has_read_pre(key) && startEpoch - currentEpoch >= minPeriod && (startEpoch - currentEpoch) % minPeriod == 0;
        } else {
            return false;
        }
    }
}

fn is_delegator(verifiers: HashSet<Address>, tx_data: Vec<u8>) -> bool {
    let delegator_addresses = get_all_delegetor_addresses()
    let current_verifiers = delegator_addresses.iter().filter(|address| verifiers.contains(address));
    return !current_verifiers.is_empty() && current_verifiers.iter().all(|addr| verify_tx_sign(tx_data, addr));
}

fn is_validator(verifiers: HashSet<Address>, tx_data: Vec<u8>) -> bool {
    let validator_addresses: Hashset<Address> = get_all_delegetor_addresses()
    let current_verifiers = validator_addresses.iter().filter(|address| verifiers.contains(address));
    return !current_verifiers.is_empty() && current_verifiers.iter().all(|addr| verify_tx_sign(tx_data, addr));
}

fn current_epoch_is_2_3(addr: Address, id: u64) {
    let currentEpoch = read_current_epoch()
    let startEpoch = read_post_start_epoch(addr, id, START_EPOCH_KEY) 
    let endEpoch = read_post_end_epoch(addr, id, END_EPOCH_KEY)
    
    return ((endEpoch - startEpoch) * 2) / 3 <= (currentEpoch - startEpoch);
}

```

### Governance storage
Each proposal will be stored in a sub-key under the internal proposal address. The storage keys involved are:
```
/$proposal_address/proposal/$id : u64
/$proposal_address/proposal/$id/content : Vec<u8>
/$proposal_address/proposal/$id/author : Address
/$proposal_address/proposal/$id/startEpoch: Epoch
/$proposal_address/proposal/$id/endEpoch: Epoch
/$proposal_address/? : Vec<u8> 

/$xan_token_address/balance/$proposal_address: u64
```

`Author` address field will be used to credit the locked funds if the proposal is approved.


### Proposal transaction

Proposal transaction will create the aforemontioned fields in the storage and lock the amount from the `author` address.

### Vote transaction

Vote transaction will create the following field in the storage:
```
/$proposal_address/proposal/id/vote/$address: Enum(yay|nay)
```

The storage key will only be created if the tx is signed either by a validator or a delagator. 
Validators will be able to vote only for 2/3 of the total voting period, meanwhile delegators can vote untill the end of the voting period.

### Tally
The proposal is has a positive outcome if:
- 2/3 of the staked xan total is voting `yay`
The tally can be computed via CLI command.

```rust
fn compute_tally(proposal_id: u64) {
    let vote_addresses = get_proposal_vote_iter(proposal_id).map(|addr| addr)
    let total_xan: u64 = vote_addresses.reduce(|acc, addr| acc + get_addr_balance(addr), 0)
    
    let delegators =  vote_addresses.filter(|addr| addr.is_delegator())
    let yay_addresses = vote_addresses.filter(|addr| read_vote(proposal_id, addr) == 'yay')
    
    let yay_validators = yay_addresses.filter(|addr| addr.is_validator())
    let yay_validators_xan = yay_validator.reduce(|acc, addr| acc + get_addr_balance(addr), 0)
    
    for delegator in delegators {
        if yay_validators.contains(delegator.get_correspoding_validator()) {
            if read_vote(proposal_id, delegator) == 'nay' {
                yay_validators_xan -= get_addr_balance(delegator)
            }
        }
    }
    return yay_validators_xan / total_xan >= 0.66;
}
```

### Refund mechanism
At the end of each epoch, the protocol will check, in the `BeginBlock` event, if any proposal has ended. For each ended proposal with positive outcome, it will refund the locked funds to the proposal author.

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
  yay: bool
}
```

The proposalHash is produced over the concatenation of `content`, `author`, `votingStart`, `votingEnd`, `voter` and `yay`.

### Tally
Same mechanism as OnChain tally but instead of reading the data from storage it will require a list of serialized json votes.

## Interfaces

- Ledger CLI
- Wallet
