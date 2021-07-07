# Event dispatching / observer interface

The `stacks-node` supports a configurable event observer interface.
This is enabled by adding an entry to the node's `config.toml` file:

```toml
...
[[events_observer]]
endpoint = "listener:3700"
events_keys = [
  "*"
]
...
```

The `stacks-node` will then execute HTTP POSTs to the configured
endpoint in two events:

1. A new Stacks block is processed.
2. New mempool transactions have been received.

These events are sent to the configured endpoint at two URLs:


### `POST /new_block`

This payload includes data related to a newly processed block,
and any events emitted from Stacks transactions during the block.

If the transaction originally comes from the parent microblock stream 
preceding this block, the microblock related fields will be filled in.

Example:

```json
{
  "block_hash": "0x4eaabcd105865e471f697eff5dd5bd85d47ecb5a26a3379d74fae0ae87c40904",
  "block_height": 3,
  "burn_block_time": 1591301733,
  "events": [
    {
      "event_index": 1,
      "committed": true,
      "stx_transfer_event": {
        "amount": "1000",
        "recipient": "ST31DA6FTSJX2WGTZ69SFY11BH51NZMB0ZZ239N96",
        "sender": "ST3WM51TCWMJYGZS1QFMC28DH5YP86782YGR113C1"
      },
      "txid": "0x738e4d44636023efa08374033428e44eca490582bd39a6e61f3b6cf749b4214c",
      "type": "stx_transfer_event"
    }
  ],
  "index_block_hash": "0x329efcbcc6daf5ac3f264522e0df50eddb5be85df6ee8a9fc2384c54274d7afc",
  "parent_block_hash": "0xf5d4ce0efe1d42c963d615ce57f0d014f263a985175e4ece766eceff10e0a358",
  "parent_index_block_hash": "0x0c8b38d44d6af72703a4767ff4cea683ec965346d9e9a7ded2d773fb4f257c28",
  "parent_microblock": "0xedd15cf1e697c28df934e259f0f82970a7c9edc2d39bef04bdd0d422116235c6",
  "transactions": [
    {
      "contract_abi": null,
      "raw_result": "0x03",
      "raw_tx": "0x808000000004008bc5147525b8f477f0bc4522a88c8339b2494db50000000000000002000000000000000001015814daf929d8700af344987681f44e913890a12e38550abe8e40f149ef5269f40f4008083a0f2e0ddf65dcd05ecfc151c7ff8a5308ad04c77c0e87b5aeadad31010200000000040000000000000000000000000000000000000000000000000000000000000000",
      "status": "success",
      "tx_index": 0,
      "txid": "0x3e04ada5426332bfef446ba0a06d124aace4ade5c11840f541bf88e2e919faf6",
      "microblock_sequence": "None",
      "microblock_hash": "None",
      "microblock_parent_hash": "None"
    },
    {
      "contract_abi": null,
      "raw_result": "0x03",
      "raw_tx": "0x80800000000400f942874ce525e87f21bbe8c121b12fac831d02f4000000000000000000000000000003e800006ae29867aec4b0e4f776bebdcea7f6d9a24eeff370c8c739defadfcbb52659b30736ad4af021e8fb741520a6c65da419fdec01989fdf0032fc1838f427a9a36102010000000000051ac2d519faccba2e435f3272ff042b89435fd160ff00000000000003e800000000000000000000000000000000000000000000000000000000000000000000",
      "status": "success",
      "tx_index": 1,
      "txid": "0x738e4d44636023efa08374033428e44eca490582bd39a6e61f3b6cf749b4214c",
      "microblock_sequence": "3",
      "microblock_hash": "0x9304fcbcc6daf5ac3f264522e0df50eddb5be85df6ee8a9fc2384c54274daaac",
      "microblock_parent_hash": "0x4893ab44636023efa08374033428e44eca490582bd39a6e61f3b6cf749b474bd"
    }
   ],
   "matured_miner_rewards": [
    {
      "recipient": "ST31DA6FTSJX2WGTZ69SFY11BH51NZMB0ZZ239N96",
      "coinbase_amount": "1000",
      "tx_fees_anchored": "800",
      "tx_fees_streamed_confirmed": "0",
      "from_stacks_block_hash": "0xf5d4ce0efe1d42c963d615ce57f0d014f263a985175e4ece766eceff10e0a358",
      "from_index_block_hash": "0x329efcbcc6daf5ac3f264522e0df50eddb5be85df6ee8a9fc2384c54274d7afc",
    }
   ]
}
```

### `POST /new_burn_block`

This payload includes information about burn blocks as their sortitions are processed.
In the event of PoX forks, a `new_burn_block` event may be triggered for a burn block
previously processed.

Example:

```json
{
  "burn_block_hash": "0x4eaabcd105865e471f697eff5dd5bd85d47ecb5a26a3379d74fae0ae87c40904",
  "burn_block_height": 331,
  "reward_recipients": [
    {
      "recipient": "1C56LYirKa3PFXFsvhSESgDy2acEHVAEt6",
      "amt": 5000
    }
  ],
  "reward_slot_holders": [
    "1C56LYirKa3PFXFsvhSESgDy2acEHVAEt6",
    "1C56LYirKa3PFXFsvhSESgDy2acEHVAEt6"
  ],
  "burn_amount": 12000
}
```

* `reward_recipients` is an array of all the rewards received during this burn block. It may
  include recipients who did _not_ have reward slots during the block. This could happen if
  a miner's commitment was included a block or two later than intended. Such commitments would
  not be valid, but the reward recipient would still receive the burn `amt`.
* `reward_slot_holders` is an array of the Bitcoin addresses that would validly receive
  PoX commitments during this block. These addresses may not actually receive rewards during
  this block if the block is faster than miners have an opportunity to commit.

### `POST /new_microblocks`

This payload includes data related to one or more microblocks that are either emmitted by the 
node itself, or received through the network. 

Example:

```json
{
  "parent_index_block_hash": "0x999b38d44d6af72703a476dde4cea683ec965346d9e9a7ded2d773fb4f257a3b",
  "events": [
    {
      "event_index": 1,
      "committed": true,
      "stx_transfer_event": {
        "amount": "1000",
        "recipient": "ST31DA6FTSJX2WGTZ69SFY11BH51NZMB0ZZ239N96",
        "sender": "ST3WM51TCWMJYGZS1QFMC28DH5YP86782YGR113C1"
      },
      "txid": "0x738e4d44636023efa08374033428e44eca490582bd39a6e61f3b6cf749b4214c",
      "type": "stx_transfer_event"
    }
  ],
  "transactions": [
    {
      "contract_abi": null,
      "raw_result": "0x03",
      "raw_tx": "0x808000000004008bc5147525b8f477f0bc4522a88c8339b2494db50000000000000002000000000000000001015814daf929d8700af344987681f44e913890a12e38550abe8e40f149ef5269f40f4008083a0f2e0ddf65dcd05ecfc151c7ff8a5308ad04c77c0e87b5aeadad31010200000000040000000000000000000000000000000000000000000000000000000000000000",
      "status": "success",
      "tx_index": 0,
      "txid": "0x3e04ada5426332bfef446ba0a06d124aace4ade5c11840f541bf88e2e919faf6",
      "microblock_sequence": "3",
      "microblock_hash": "0x9304fcbcc6daf5ac3f264522e0df50eddb5be85df6ee8a9fc2384c54274daaac",
      "microblock_parent_hash": "0x4893ab44636023efa08374033428e44eca490582bd39a6e61f3b6cf749b474bd"
    },
    {
      "contract_abi": null,
      "raw_result": "0x03",
      "raw_tx": "0x80800000000400f942874ce525e87f21bbe8c121b12fac831d02f4000000000000000000000000000003e800006ae29867aec4b0e4f776bebdcea7f6d9a24eeff370c8c739defadfcbb52659b30736ad4af021e8fb741520a6c65da419fdec01989fdf0032fc1838f427a9a36102010000000000051ac2d519faccba2e435f3272ff042b89435fd160ff00000000000003e800000000000000000000000000000000000000000000000000000000000000000000",
      "status": "success",
      "tx_index": 1,
      "txid": "0x738e4d44636023efa08374033428e44eca490582bd39a6e61f3b6cf749b4214c",
      "microblock_sequence": "4",
      "microblock_hash": "0xfcd4fc34c6daf5ac3f264522e0df50eddb5be85df6ee8a9fc2384c5427459e43",
      "microblock_parent_hash": "0x9304fcbcc6daf5ac3f264522e0df50eddb5be85df6ee8a9fc2384c54274daaac"
    }
  ],
  "burn_block_hash": "0x4eaabcd105865e471f697eff5dd5bd85d47ecb5a26a3379d74fae0ae87c40904",
  "burn_block_height": 331,
  "burn_block_timestamp": 1651301734
}
```

* `burn_block_{}` are the stats related to the burn block that is associated with the stacks 
  block that precedes this microblock stream.
* Each transaction json object includes information about the microblock the transaction was packaged into. 

### `POST /new_mempool_tx`

This payload includes raw transactions newly received in the
node's mempool.

Example:

```json
[
  "0x80800000000400f942874ce525e87f21bbe8c121b12fac831d02f4000000000000000000000000000003e800006ae29867aec4b0e4f776bebdcea7f6d9a24eeff370c8c739defadfcbb52659b30736ad4af021e8fb741520a6c65da419fdec01989fdf0032fc1838f427a9a36102010000000000051ac2d519faccba2e435f3272ff042b89435fd160ff00000000000003e800000000000000000000000000000000000000000000000000000000000000000000"
]
```


### `POST /drop_mempool_tx`

This payload includes raw transactions newly received in the
node's mempool.

Example:

```json
{
  "dropped_txids": ["d7b667bb93898b1d3eba4fee86617b06b95772b192f3643256dd0821b476e36f"],
  "reason": "ReplaceByFee"
}
```

Reason can be one of:

* `ReplaceByFee` - replaced by a transaction with the same nonce, but a higher fee
* `ReplaceAcrossFork` - replaced by a transaction with the same nonce but in the canonical fork
* `TooExpensive` - the transaction is too expensive to include in a block
* `StaleGarbageCollect` - transaction was dropped because it became stale
