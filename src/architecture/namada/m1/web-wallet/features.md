# Web Wallet

## Application Features

This application consists of a user interface that allows the user to perform the following actions in an intuitive way:

### Seed Phrase

[hifi Designs](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=4610%3A5890)

The user should be able to:

- Set up a new seed phrase and derive accounts from it [wireframe](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=6442%3A5866)
- Create a new seed phrase, export it to the clipboard, and be prompted to save the seed phrase [wireframe](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=6442%3A6015) [wireframe](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=6442%3A6104)
- Restore (Import) accounts from a seed phrase
- Retrieve a forgotten seed phrase by providing their password

### User accounts

[hifi Designs](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=5165%3A8862)

When entering the app, the user should be prompted for a password to decrypt the key pair (see [wireframe](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=6442%3A5801)). Following that, the user can:

- Create accounts derived from the master key pair
- Delete accounts
- Integrate the web wallet with the Ledger hardware wallet
  - Set up flow TBD
  - Managing TBD
- See an overview of the assets in the account and all derived accounts [wireframe](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=6442%3A5492)
- View the details of a single asset, containing the following information [wireframe](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=6442%3A5681)
  - Balance
  - All past transactions for the current account and asset
  - Button to initiate a new transfer using this asset

### Transfers

[TBD]()

- The user can create transparent transfers
- The user can create shielded transfers
- The wallet supports bi-directional transfer between Namada and ETH
  - Supports approving transactions with MetaMask
- The wallet supports bi-directional transfer between Namada and IBC supported chains
  - Supports approving transactions with Keplr

### Staking & Governance

[TBD]()

The user can:

- Bond funds to a list of validators
- Un-bond funds to a list of validators
- Submit proposals
- Vote on proposals
- Follow up with the current and past proposals and their vote results
