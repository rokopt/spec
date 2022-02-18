# IBC integration

* [IBC (Inter-blockchain communication protocol) spec](https://github.com/cosmos/ibc)

## IBC transaction
An IBC transaction `tx_ibc.wasm` is provided. We have to set an IBC message to the transaction data corresponding to execute an IBC operation. In Anoma, the transaction is executed according to the message. The message should be encoded with Protobuf (NOT with Borsh) as the following code.

```rust
use ibc::tx_msg::Msg;

pub fn make_ibc_data(message: impl Msg) -> Vec<u8> {
    let msg = message.to_any();
    let mut tx_data = vec![];
    prost::Message::encode(&msg, &mut tx_data).expect("encoding IBC message shouldn't fail");
    tx_data
}
```

The IBC messages are defined in `ibc-rs`.

* Client
  - [MsgCreateAnyClient](https://github.com/informalsystems/ibc-rs/blob/5ddec6d2571b1376de7d9ebe7e353b3cd726c2d3/modules/src/core/ics02_client/msgs/create_client.rs#L19-L23)
  - MsgSubmitAnyMisbehaviour (NOT supported yet)
  - [MsgUpdateAnyClient](https://github.com/informalsystems/ibc-rs/blob/5ddec6d2571b1376de7d9ebe7e353b3cd726c2d3/modules/src/core/ics02_client/msgs/update_client.rs#L20-L24)
  - [MsgUpgradeAnyClient](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics02_client/msgs/upgrade_client.rs#L24-L31)

* Connection
  - [MsgConnectionOpenInit](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics03_connection/msgs/conn_open_init.rs#L21-L27)
  - [MsgConnectionOpenTry](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics03_connection/msgs/conn_open_try.rs#L29-L38)
  - [MsgConnectionOpenAck](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics03_connection/msgs/conn_open_ack.rs#L20-L27)
  - [MsgConnectionOpenConfirm](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics03_connection/msgs/conn_open_confirm.rs#L19-L23)

* Channel
  - [MsgChannelOpenInit](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/chan_open_init.rs#L17-L21)
  - [MsgChannelOpenTry](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/chan_open_try.rs#L22-L29)
  - [MsgChannelOpenAck](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/chan_open_ack.rs#L18-L25)
  - [MsgChannelOpenConfirm](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/chan_open_confirm.rs#L18-L23)
  - [MsgRecvPacket](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/recv_packet.rs#L19-L23)
  - [MsgAcknowledgement](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/acknowledgement.rs#L19-L24)
  - [MsgChannelCloseInit](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/chan_close_init.rs#L18-L22)
  - [MsgChannelCloseConfirm](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/chan_close_confirm.rs#L20-L25)
  - [MsgTimeout](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/timeout.rs#L19-L24)
  - [MsgTimeoutOnClose](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/core/ics04_channel/msgs/timeout_on_close.rs#L18-L23)

* ICS20 FungibleTokenTransfer
  - [MsgTransfer](https://github.com/informalsystems/ibc-rs/blob/1448a2bbc817da10b183b8479548a12344ba0e9c/modules/src/applications/ics20_fungible_token_transfer/msgs/transfer.rs#L20-L37)

## IBC validity predicate
IBC validity predicate checks if an IBC-related transaction satisfies IBC protocol. When an IBC-related transaction is executed, IBC validity predicate (one of the native validity predicates) is executed. It is triggered by state change of the IBC-related data. For example, if an IBC connection end is created in the transaction, IBC validity predicate validates the creation. If the creation with `MsgConnectionOpenTry` is invalid, e.g. the state of the counterpart connection isn't `INIT`, the validity predicate makes the transaction fail.

## Fungible Token Transfer
The transfer of fungible tokens over an IBC channel on separate chains is defined in [ICS20](https://github.com/cosmos/ibc/blob/master/spec/app/ics-020-fungible-token-transfer/README.md).

In Anoma, the sending tokens is triggered by a transaction having [MsgTransfer](https://github.com/informalsystems/ibc-rs/blob/0a952b295dbcf67bcabb79ce57ce92c9c8d7e5c6/modules/src/applications/ics20_fungible_token_transfer/msgs/transfer.rs#L20-L37) as transaction data. The packet including `FungibleTokenPacketData` is made from the message in the transaction execution.

Anoma chain receives the tokens by a transaction having [MsgRecvPacket](https://github.com/informalsystems/ibc-rs/blob/0a952b295dbcf67bcabb79ce57ce92c9c8d7e5c6/modules/src/core/ics04_channel/msgs/recv_packet.rs#L19-L23) which has the packet including `FungibleTokenPacketData`.

The sending and receiving tokens in a transaction are validated by not only the IBC validity predicate but also IBC token validity predicate. IBC validity predicate is also one of the native validity predicates and validates if sending and receiving the packet is proper. IBC token validity predicate checks if the token transfer is valid.

A transaction escrowing/unescrowing a token changes the escrow account's balance of the token. The key is `{token_addr}/balance/{escrow_addr}`. A transaction burning a token changes the burn account's balance of the token. The key is `{token_addr}/balance/BURN_ADDR`. A transaction minting a token changes the mint account's balance of the token. The key is `{token_addr}/balance/MINT_ADDR`. `{escrow_addr}`, `{BURN_ADDR}`, and `{MINT~ADDR}` are addresses of `InternalAddress`. When these address are included of the change keys after transaction execution, IBC token validity predicate is executed.
