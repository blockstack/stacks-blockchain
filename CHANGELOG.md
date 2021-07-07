# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the versioning scheme outlined in the [README.md](README.md).

## [2.0.11.2.0]

### Added

- `clarity-cli` will now also print a serialized version of the resulting
  output from `eval` and `execute` commands. This serialization is in
  hexademical string format and supports integration with other tools. (#2684)
- `lcov`-compatible coverage reporting has been added to `clarity-cli` for
  Clarity contract testing. (#2592)
- The `README.md` file has new documentation about the release process. (#2726)

### Changed

- This change resets the testnet. (#2742)
- Caching has been added to speed up `/v2/info` responses. (#2746)

### Fixed

- PoX syncing will only look back to the reward cycle prior to divergence,
  instead of looking back over all history. This will speed up running a
  follower node. (#2746)
- The UTXO staleness check is re-ordered so that it occurs before the RBF-limit
  check. This way, if stale UTXOs reached the "RBF limit" a miner will recover
  by resetting the UTXO cache. (#2694)
- A bug is fixed in the mocknet/helium miner that would lead to a panic if a
  burn block occurred without a sortition in it. (#2711)
- Documentation is fixed in cases where string and buffer types are allowed
  but not covered in the documentation.  (#2676)

## [2.0.11.1.0]

This software update is our monthly release. It introduces fixes and features for both developers and miners. 
This release's chainstate directory is compatible with chainstate directories from 2.0.11.0.0.

## Added

- `/new_microblock` endpoint to notify event observers when a valid microblock
  has been received (#2571).
- Added new features to `clarity-cli` (#2597)
- Exposing new mining-related metrics in prometheus (#2664)
  - Miner's computed relative miner score as a percentage
  - Miner's computed commitment, the min of their previous commitment and their median commitment
  - Miner's current median commitment
- Add `key-for-seed` command to the `stacks-node` binary - outputs the associated secret key hex string
  and WIF formatted secret key for a given "seed" value (#2658).

## Changed

- Improved mempool walk order (#2514).
- Renamed database `tx_tracking.db` to `tx_tracking.sqlite` (#2666).
  
## Fixed 

- Alter the miner to prioritize spending the most recent UTXO when building a transaction, 
  instead of the largest UTXO. In the event of a tie, it uses the smallest UTXO first (#2661).
- Fix trait rpc lookups for implicitly implemented traits (#2602).
- Fix `v2/pox` endpoint, broken on Mocknet (#2634).
- Align cost limits on mocknet, testnet and mainnet (#2660). 
- Log peer addresses in the HTTP server (#2667)
- Mine microblocks if there are no recent unprocessed Stacks blocks

## [2.0.11.0.0]

The chainstate directory has been restructured in this release. It is not
compatible with prior chainstate directories.

## Added

- `/drop_mempool_tx` endpoint to notify event observers when a mempool
  transaction has been removed the mempool.
- `"reward_slot_holders"` field to the `new_burn_block` event
- CTRL-C handler for safe shutdown of `stacks-node`
- Log transactions in local db table via setting env `STACKS_TRANSACTION_LOG=1`
- New prometheus metrics for mempool transaction processing times and
  outstanding mempool transactions
- New RPC endpoint with path `/v2/traits/contractAddr/contractName/traitContractName
  /traitContractAddr/traitName` to determine whether a given trait is implemented 
  within the specified contract (either explicitly or implicitly).
- Re-activate the Atlas network for propagating and storing transaction
  attachments. This re-enables off-chain BNS name storage.
- Re-activate microblock mining.

## Changed

- Improved chainstate directory layout
- Improved node boot up time
- Better handling of flash blocks
- The `/v2/pox` RPC endpoint was updated to include more useful
  information about the current and next PoX cycles. For details, see
  `docs/rpc-endpoints.md`
  
## Fixed 

- Fixed faulty logic in the mempool that was still treating the transaction fee
  as a fee rate, which prevented replace-by-fee from working as expected.

## [2.0.10.0.1]

This is a low-priority hotfix release to address a bug in the deserialization logic. The
chainstate directory of 2.0.10.0.1 is compatible with 2.0.10. This release also begins the
usage of the versioning scheme outlined in the [README.md](README.md).

## [2.0.10]

This is a low-priority hotfix release to address two bugs in the block downloader. The
chainstate directory of 2.0.10 is compatible with 2.0.9. If booting up a node from genesis, or
an existing node has stalled in downloading blocks, this hotfix is necessary for your
node.

## Fixed

- Bug in microblocks inventory vector calculation that included invalidated microblocks
  as present bit. This bug will impact nodes booting up from genesis, but not affect nodes
  currently running at the chain tip (#2518).
- Bug in microblocks downloader logic that would cause the stacks-node to fail to wake-up
  to process newly arrived microblocks in certain instances (#2491).

## [2.0.9]

This is a hotfix release for improved handling of arriving Stacks blocks through
both the RPC interface and the P2P ineterface.  The chainstate directory of
2.0.9 is compatible with the 2.0.8 chainstate.

## Fixed

- TOCTTOU bug fixed in the chain processing logic that, which now ensures that
  an arriving Stacks block is processed at most once.

## [2.0.8] - 2021-03-02

This is a hotfix release for improved handling of static analysis storage and
improved `at-block` behavior. The chainstate directory of 2.0.8 is compatible with
the 2.0.7 chainstate.

## Fixed

- Improved static analysis storage
- `at-block` behavior in `clarity-cli` and unit tests (no changes in `stacks-node`
  behavior).

## [2.0.7] - 2021-02-26

This is an emergency hotfix that prevents the node from accidentally deleting
valid block data if its descendant microblock stream is invalid for some reason.

## Fixed

- Do not delete a valid parent Stacks block.


## [2.0.6] - 2021-02-15

The database schema has not changed since 2.0.5, so when spinning up a
2.0.6 node from a 2.0.5 chainstate, you do not need to use a fresh
working directory. Earlier versions' chainstate directories are
incompatible, however.

### Fixed

- Miner RBF logic has two "fallback" logic changes. First, if the RBF
  logic has increased fees by more than 50%, do not submit a new
  transaction. Second, fix the "same chainstate hash" fallback check.
- Winning block txid lookups in the SortitionDB have been corrected
  to use the txid during the lookup.
- The miner will no longer attempt to mine a new Stacks block if it receives a
  microblock in a discontinuous microblock stream.

## [2.0.5] - 2021-02-12

The database schema has changed since 2.0.4, so when spinning up a 2.0.5
node from an earlier chainstate, you must use a fresh working directory.

### Added

- Miner heuristic for handling relatively large or computationally
  expensive transactions: such transactions will be dropped from the
  mempool to prevent miners from re-attempting them once they fail.
  Miners can also now continue processing transactions that are
  behind those transactions in the mempool "queue".

### Fixed

- Miner block assembly now uses the correct block limit available via
  the node config
- `tx_fees_streamed_produced` fees are included in miner coinbase
  events for event observers
- SQLite indexes are now correctly created on database instantion

### Changed

- STX unlock events are now sent over the events endpoint bundled
  into an associated unlock transaction
- Atlas attachments networking endpoints are disabled for this
  release, while networking issues are addressed in the
  implementation

## [2.0.4] - 2021-02-07

### Changed

- Atlas attachments networking endpoints are disabled for this
  release, while networking issues are addressed in the
  implementation.

## [2.0.3] - 2021-02-04

### Added

- `stacks-node --mine-at-height` commandline option, which tells the
  `stacks-node` not to mine until it has synchronized to the given
  Stacks block height
- A new RPC endpoint `/v2/blocks/upload/{consensus_hash}` that accepts
  an uploaded a Stacks block for a given sortition

### Changed

- Enabled WAL mode for the chainstate databases. This allows much more
  concurrency in the `stacks-node`, and improves network performance
  across the board. **NOTE:** *This changed the database schema, any
  running node would need to re-initialize their nodes from a new chain
  state when upgrading*.
- Default value `wait_time_for_microblocks`: from 60s to 30s
- The mempool now performs more transfer semantics checks before admitting
  a transaction (e.g., reject if origin = recipient): see issue #2354
- Improved the performance of the code that handles `GetBlocksInv` p2p
  messages by an order of magnitude.
- Improved the performance of the block-downloader's block and
  microblock search code by a factor of 5x.

### Fixed

- Miner mempool querying now works across short-lived forks: see issue #2389
- JSON deserialization for high-depth JSON objects
- Atlas attachment serving: see PR #2390
- Address issues #2379, #2356, #2347, #2346. The tracking of the
  `LeaderBlockCommit` operations inflight is improved, drastically
  reducing the number of block commit rejections. When
  a`LeaderBlockCommit` is not included in the Bitcoin block it was
  targeting, it is condemned to be rejected, per the Stacks
  consensus. To avoid wasting BTC, the miner now tries to send its
  next `LeaderBlockCommit` operations using the UTXOs of the previous
  transaction with a replacement by fee. The fee increase increments
  can be configured with the setting `rbf_fee_increment`.
