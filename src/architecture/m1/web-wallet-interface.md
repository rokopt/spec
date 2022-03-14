# Web wallet interface

## Application Features

The application consist of the an UI that allows the user to perform the following actions in an easy to use and consistent web application:

### Seed Phrase
[UI Designs](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=4610%3A5890)
* Can setup a new seed phrase and derive accounts on it
* When creating the seed phrase, the user can export it copied to the clipboard, user has to confirm the saving of the seed phrase
* Restore accounts from a seed phrase
* Can retrieve a forgotten seed phrase, this requires user to enter the main password

### User accounts
[UI Designs](https://www.figma.com/file/aiWZpaXjPLW6fDjE7dpFaU/Projects-2021?node-id=5165%3A8862)
* Can create accounts derived from the master key pair
* Can delete accounts
* Common to all transactions is that the user is being prompted for a password for encrypting the keys whenever a transactions is being performed
* User can integrated with Ledger hardware wallet

### Transfers
[TBD]()
* Can create transparent transfers
* Can create shielded transfers
* Bi-directional transfer between Namada and ETH
  * Supports approving transactions with MetaMask
* Bi-directional transfer between Namada and IBC supported chains
  *  Supports approving transactions with Keplr

### Staking & Governance
[TBD]()
* Can bond funds to a list of validators
* Can un-bond funds to a list of validators
* Can submit proposals
* Can vote on proposals
* Can follow up with the current and past proposals and their vote results

## Tech Stack
### Core Application
* Core application is built on React/TypeScript
* State management with Redux
* Application styling is accomplished with styled-components
* Extensive usage of WASM compiled Rust code from the common Anoma code base is encouraged where ever feasible.
