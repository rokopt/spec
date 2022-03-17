# Cubic slashing

Namada implements cubic slashing, meaning that the amount of a slash is proportional to the cube of the voting power committing infractions discovered within a particular interval. This is designed to make it riskier to operate larger or similarly configured validators, and thus encourage network resilience.

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

At present, funds slashed are sent to the governance treasury. In the future we could potentially reward the slash discoverer with part of the slash, for which some sort of commit-reveal mechanism will be required to prevent front-running.
