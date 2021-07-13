# Stacks 2.0

Reference implementation of the [Stacks blockchain](https://github.com/blockstack/stacks) in Rust.

Stacks 2.0 is a layer-1 blockchain that connects to Bitcoin for security and enables decentralized apps and predictable smart contracts. Stacks 2.0 implements [Proof of Transfer (PoX)](https://blockstack.org/pox.pdf) mining that anchors to Bitcoin security. Leader election happens at the Bitcoin blockchain and Stacks (STX) miners write new blocks on the separate Stacks blockchain. With PoX there is no need to modify Bitcoin to enable smart contracts and apps around it. See [this page](https://github.com/blockstack/stacks) for more details and resources.

[![CircleCI](https://circleci.com/gh/blockstack/stacks-blockchain/tree/master.svg?style=svg)](https://circleci.com/gh/blockstack/stacks-blockchain/tree/master)

## Repository

| Blockstack Topic/Tech      | Where to learn more more                                                          |
| -------------------------- | --------------------------------------------------------------------------------- |
| Stacks 2.0                 | [master branch](https://github.com/blockstack/stacks-blockchain/tree/master)      |
| Stacks 1.0                 | [legacy branch](https://github.com/blockstack/stacks-blockchain/tree/stacks-1.0)  |
| Use the package            | [our core docs](https://docs.blockstack.org/core/naming/introduction.html)        |
| Develop a Blockstack App   | [our developer docs](https://docs.blockstack.org/browser/hello-blockstack.html)   |
| Use a Blockstack App       | [our browser docs](https://docs.blockstack.org/browser/browser-introduction.html) |
| Blockstack PBC the company | [our website](https://blockstack.org)                                             |

## Release Schedule and Hotfixes

Normal releases in this repository that add features such as improved RPC endpoints, improved boot-up time, new event
observer fields or event types, etc., are released on a monthly schedule. The currently staged changes for such releases
are in the [develop branch](https://github.com/blockstack/stacks-blockchain/tree/develop). It is generally safe to run
a `stacks-node` from that branch, though it has received less rigorous testing than release tags. If bugs are found in
the `develop` branch, please do report them as issues on this repository.

For fixes that impact the correct functioning or liveness of the network, _hotfixes_ may be issued. These are patches
to the main branch which are backported to the develop branch after merging. These hotfixes are categorized by priority
according to the following rubric:

- **High Priority**. Any fix for an issue that could deny service to the network as a whole, e.g., an issue where a particular kind of invalid transaction would cause nodes to stop processing requests or shut down unintentionally. Any fix for an issue that could cause honest miners to produce invalid blocks.
- **Medium Priority**. Any fix for an issue that could cause miners to waste funds
- **Low Priority**. Any fix for an issue that could deny service to individual nodes

## Versioning

This repository uses a 5 part version number.

```
X.Y.Z.A.n

X = 2 and does not change in practice unless there’s another Stacks 2.0 type event
Y increments on consensus-breaking changes
Z increments on non-consensus-breaking changes that require a fresh chainstate (akin to semantic MAJOR)
A increments on non-consensus-breaking changes that do not require a fresh chainstate, but introduce new features (akin to semantic MINOR)
n increments on patches and hot-fixes (akin to semantic PATCH)
```

For example, a node operator running version `2.0.10.0.0` would not need to wipe and refresh their chainstate
to upgrade to `2.0.10.1.0` or `2.0.10.0.1`. However, upgrading to `2.0.11.0.0` would require a new chainstate.

## Roadmap

- [x] [SIP 001: Burn Election](https://github.com/stacksgov/sips/blob/main/sips/sip-001/sip-001-burn-election.md)
- [x] [SIP 002: Clarity, a language for predictable smart contracts](https://github.com/stacksgov/sips/blob/main/sips/sip-002/sip-002-smart-contract-language.md)
- [x] [SIP 003: Peer Network](https://github.com/stacksgov/sips/blob/main/sips/sip-003/sip-003-peer-network.md)
- [x] [SIP 004: Cryptographic Committment to Materialized Views](https://github.com/stacksgov/sips/blob/main/sips/sip-004/sip-004-materialized-view.md)
- [x] [SIP 005: Blocks, Transactions, and Accounts](https://github.com/stacksgov/sips/blob/main/sips/sip-005/sip-005-blocks-and-transactions.md)
- [x] [SIP 006: Clarity Execution Cost Assessment](https://github.com/stacksgov/sips/blob/main/sips/sip-006/sip-006-runtime-cost-assessment.md)
- [x] [SIP 007: Stacking Consensus](https://github.com/stacksgov/sips/blob/main/sips/sip-007/sip-007-stacking-consensus.md)
- [x] [SIP 008: Clarity Parsing and Analysis Cost Assessment](https://github.com/stacksgov/sips/blob/main/sips/sip-008/sip-008-analysis-cost-assessment.md)

Stacks improvement proposals (SIPs) are aimed at describing the implementation of the Stacks blockchain, as well as proposing improvements. They should contain concise technical specifications of features or standards and the rationale behind it. SIPs are intended to be the primary medium for proposing new features, for collecting community input on a system-wide issue, and for documenting design decisions.

See [SIP 000](https://github.com/stacksgov/sips/blob/main/sips/sip-000/sip-000-stacks-improvement-proposal-process.md) for more details.

The SIPs are now located in the [stacksgov/sips](https://github.com/stacksgov/sips) repository as part of the [Stacks Community Governance organization](https://github.com/stacksgov).

### Testnet versions

- [x] **Helium** is a developer local setup, mono-node, assembling SIP 001, SIP 002, SIP 004 and SIP 005. With this version, developers can not only run Stacks 2.0 on their development machines, but also write, execute, and test smart contracts. See the instructions below for more details.

- [x] **Neon** is the first version of our public testnet, which shipped in Q2 2020. This testnet added SIP 003, and will be an open-membership public network, where participants will be able to validate and participate in mining testnet blocks.

- [x] **Argon** is the second version of our public testnet, which shipped in Q2 2020. This testnet improved on the stability of the Neon testnet.

- [x] **Krypton** is the third version of our public testnet, which incorporates a partial implementation of SIP 007. It allows developers to test a simple version of Stacking and PoX consensus.

- [x] **Xenon** is the upcoming version of our public testnet, which will run on the Bitcoin testnet. It will include SIP 006 and SIP 008, and will contain bugfixes and improvements to the implementation of SIP 007.

- [x] **Mainnet** is the fully functional version, that is estimated for Q4 2020.

See the [testnet website](https://testnet.blockstack.org) and ["when mainnet?" FAQ](https://github.com/blockstack/stacks/blob/master/whenmainnet.md) for details.

## Getting started

### Download and build stacks-blockchain

The first step is to ensure that you have Rust and the support software installed.

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

_For building on Windows, follow the rustup installer instructions at https://rustup.rs/_

From there, you can clone this repository:

```bash
git clone --depth=1 https://github.com/blockstack/stacks-blockchain.git

cd stacks-blockchain
```

Then build the project:

```bash
cargo build
```

Run the tests:

```bash
cargo test testnet  -- --test-threads=1
```

### Encode and sign transactions

Here, we have generated a keypair that will be used for signing the upcoming transactions:

```bash
cargo run --bin blockstack-cli generate-sk --testnet

# Output
# {
#  secretKey: "b8d99fd45da58038d630d9855d3ca2466e8e0f89d3894c4724f0efc9ff4b51f001",
#  publicKey: "02781d2d3a545afdb7f6013a8241b9e400475397516a0d0f76863c6742210539b5",
#  stacksAddress: "ST2ZRX0K27GW0SP3GJCEMHD95TQGJMKB7G9Y0X1MH"
# }
```

This keypair is already registered in the `testnet-follower-conf.toml` file, so it can be used as presented here.

We will interact with the following simple contract `kv-store`. In our examples, we will assume this contract is saved to `./kv-store.clar`:

```scheme
(define-map store { key: (string-ascii 32) } { value: (string-ascii 32) })

(define-public (get-value (key (string-ascii 32)))
    (match (map-get? store { key: key })
        entry (ok (get value entry))
        (err 0)))

(define-public (set-value (key (string-ascii 32)) (value (string-ascii 32)))
    (begin
        (map-set store { key: key } { value: value })
        (ok true)))
```

We want to publish this contract on chain, then issue some transactions that interact with it by setting some keys and getting some values, so we can observe read and writes.

Our first step is to generate and sign, using your private key, the transaction that will publish the contract `kv-store`.
To do that, we will use the subcommand:

```bash
cargo run --bin blockstack-cli publish --help
```

With the following arguments:

```bash
cargo run --bin blockstack-cli publish b8d99fd45da58038d630d9855d3ca2466e8e0f89d3894c4724f0efc9ff4b51f001 515 0 kv-store ./kv-store.clar --testnet
```

The `515` is the transaction fee, denominated in microSTX. Right now, the
testnet requires one microSTX per byte minimum, and this transaction should be
less than 515 bytes.
The third argument `0` is a nonce, that must be increased monotonically with each new transaction.

This command will output the **binary format** of the transaction. In our case, we want to pipe this output and dump it to a file that will be used later in this tutorial.

```bash
cargo run --bin blockstack-cli publish b8d99fd45da58038d630d9855d3ca2466e8e0f89d3894c4724f0efc9ff4b51f001 515 0 kv-store ./kv-store.clar --testnet | xxd -r -p > tx1.bin
```

### Run the testnet

You can observe the state machine in action locally by running:

```bash
cargo stacks-node start --config=./testnet/stacks-node/conf/testnet-follower-conf.toml
```

`testnet-follower-conf.toml` is a configuration file that you can use for setting genesis balances or configuring Event observers. You can grant an address an initial account balance by adding the following entries:

```
[[ustx_balance]]
address = "ST2VHM28V9E5QCRD6C73215KAPSBKQGPWTEE5CMQT"
amount = 100000000
```

The `address` field is the Stacks testnet address, and the `amount` field is the
number of microSTX to grant to it in the genesis block. The addresses of the
private keys used in the tutorial below are already added.

### Publish your contract

Assuming that the testnet is running, we can publish our `kv-store` contract.

In another terminal (or file explorer), you can move the `tx1.bin` generated earlier, to the mempool:

```bash
curl -X POST -H "Content-Type: application/octet-stream" --data-binary @./tx1.bin http://localhost:20443/v2/transactions
```

In the terminal window running the testnet, you can observe the state machine's reactions.

### Reading from / Writing to the contract

Now that our contract has been published on chain, let's try to submit some read / write transactions.
We will start by trying to read the value associated with the key `foo`.

To do that, we will use the subcommand:

```bash
cargo run --bin blockstack-cli contract-call --help
```

With the following arguments:

```bash
cargo run --bin blockstack-cli contract-call b8d99fd45da58038d630d9855d3ca2466e8e0f89d3894c4724f0efc9ff4b51f001 500 1 ST2ZRX0K27GW0SP3GJCEMHD95TQGJMKB7G9Y0X1MH kv-store get-value -e \"foo\" --testnet | xxd -r -p > tx2.bin
```

`contract-call` generates and signs a contract-call transaction.

We can submit the transaction by moving it to the mempool path:

```bash
curl -X POST -H "Content-Type: application/octet-stream" --data-binary @./tx2.bin http://localhost:20443/v2/transactions
```

Similarly, we can generate a transaction that would be setting the key `foo` to the value `bar`:

```bash
cargo run --bin blockstack-cli contract-call b8d99fd45da58038d630d9855d3ca2466e8e0f89d3894c4724f0efc9ff4b51f001 500 2 ST2ZRX0K27GW0SP3GJCEMHD95TQGJMKB7G9Y0X1MH kv-store set-value -e \"foo\" -e \"bar\" --testnet | xxd -r -p > tx3.bin
```

And submit it by moving it to the mempool path:

```bash
curl -X POST -H "Content-Type: application/octet-stream" --data-binary @./tx3.bin http://localhost:20443/v2/transactions
```

Finally, we can issue a third transaction, reading the key `foo` again, for ensuring that the previous transaction has successfully updated the state machine:

```bash
cargo run --bin blockstack-cli contract-call b8d99fd45da58038d630d9855d3ca2466e8e0f89d3894c4724f0efc9ff4b51f001 500 3 ST2ZRX0K27GW0SP3GJCEMHD95TQGJMKB7G9Y0X1MH kv-store get-value -e \"foo\" --testnet | xxd -r -p > tx4.bin
```

And submit this last transaction by moving it to the mempool path:

```bash
curl -X POST -H "Content-Type: application/octet-stream" --data-binary @./tx4.bin http://localhost:20443/v2/transactions
```

Congratulations, you can now [write your own smart contracts with Clarity](https://docs.blockstack.org/core/smart/overview.html).

## Platform support

Officially supported platforms: `Linux 64-bit`, `MacOS 64-bit`, `Windows 64-bit`.

Platforms with second-tier status _(builds are provided but not tested)_: `Linux ARMv7`, `Linux ARM64`.

## Community

Beyond this Github project,
Blockstack maintains a public [forum](https://forum.blockstack.org) and an
opened [Discord](https://discord.com/invite/XYdRyhf) channel. In addition, the project
maintains a [mailing list](https://blockstack.org/signup) which sends out
community announcements.

The greater Blockstack community regularly hosts in-person
[meetups](https://www.meetup.com/topics/blockstack/). The project's
[YouTube channel](https://www.youtube.com/channel/UC3J2iHnyt2JtOvtGVf_jpHQ) includes
videos from some of these meetups, as well as video tutorials to help new
users get started and help developers wrap their heads around the system's
design.

For help cross-compiling on memory-constrained devices, please see the community supported documentation here: [Cross Compiling](https://github.com/dantrevino/cross-compiling-stacks-blockchain/blob/master/README.md).

## Further Reading

You can learn more by visiting [the Blockstack Website](https://blockstack.org) and checking out the documentation:

- [Blockstack docs](https://docs.blockstack.org/)

You can also read the technical papers:

- ["PoX: Proof of Transfer Mining with Bitcoin"](https://blockstack.org/pox.pdf), May 2020
- ["The Blockstack Decentralized Computing Network"](https://blockstack.org/whitepaper.pdf), May 2019

If you have high-level questions about Blockstack, try [searching our forum](https://forum.blockstack.org) and start a new question if your question is not answered there.

## Contributing

### Tests and Coverage

PRs must include test coverage. However, if your PR includes large tests or tests which cannot run in parallel
(which is the default operation of the `cargo test` command), these tests should be decorated with `#[ignore]`.
If you add `#[ignore]` tests, you should add your branch to the filters for the `all_tests` job in our circle.yml
(or if you are working on net code or marf code, your branch should be named such that it matches the existing
filters there).

A test should be marked `#[ignore]` if:

1. It does not _always_ pass `cargo test` in a vanilla environment (i.e., it does not need to run with `--test-threads 1`).
2. Or, it runs for over a minute via a normal `cargo test` execution (the `cargo test` command will warn if this is not the case).

### Formatting

This repository uses the default rustfmt formatting style. PRs will be checked against `rustfmt` and will _fail_ if not
properly formatted.

You can check the formatting locally via:

```bash
cargo fmt --all -- --check
```

You can automatically reformat your commit via:

```bash
cargo fmt --all
```

## Non-Consensus Breaking Release Process

For non-consensus breaking releases, this project uses the following release process:

1. The release must be timed so that it does not interfere with a *prepare
phase*.  The timing of the next Stacking cycle can be found
[here](https://stacking.club/cycles/next). A release to `mainnet` should happen
at least 24 hours before the start of a new cycle, to avoid interfering
with the prepare phase. So, start by being aware of when the release can
happen.

1. Before creating the release, the release manager must determine the *version
number* for this release.  The factors that determine the version number are
discussed in [Versioning](#versioning).  We assume, in this section,
that the change is not consensus-breaking.  So, the release manager must first
determine whether there are any "non-consensus-breaking changes that require a
fresh chainstate". This means, in other words, that the database schema has
changed. Then, the release manager should determine whether this is a feature
release, as opposed to a hot fix or a patch. Given the answers to these
questions, the version number can be computed.

1. The release manager enumerates the PRs or issues that would _block_
   the release. A label should be applied to each such issue/PR as
   `2.0.x.y.z-blocker`. The release manager should ping these
   issue/PR owners for updates on whether or not those issues/PRs have
   any blockers or are waiting on feedback.

1. The release manager should open a `develop -> master` PR. This can be done before
   all the blocker PRs have merged, as it is helpful for the manager and others
   to see the staged changes.

1. The release manager must update the `CHANGELOG.md` file with summaries what
was `Added`, `Changed`, and `Fixed`. The pull requests merged into `develop`
can be found
[here](https://github.com/blockstack/stacks-blockchain/pulls?q=is%3Apr+is%3Aclosed+base%3Adevelop+sort%3Aupdated-desc). Note, however, that GitHub apparently does not allow sorting by
*merge time*, so, when sorting by some proxy criterion, some care should
be used to understand which PR's were *merged* after the last `develop ->
master` release PR.  This `CHANGELOG.md` should also be used as the description
of the `develop -> master` so that it acts as *release notes* when the branch
is tagged.

1. Once the blocker PRs have merged, the release manager will create a new tag
   by manually triggering the [`stacks-blockchain` Github Actions workflow](https://github.com/blockstack/stacks-blockchain/actions/workflows/stacks-blockchain.yml)
   against the `develop` branch, inputting the release candidate tag, `2.0.x.y.z-rc0`,
   in the Action's input textbox.

1. Once the release candidate has been built, and docker images, etc. are available,
   the release manager will notify various ecosystem participants to test the release
   candidate on various staging infrastructure:

   1. Stacks Foundation staging environments.
   1. Hiro PBC regtest network.
   1. Hiro PBC testnet network.
   1. Hiro PBC mainnet mock miner.

   The release candidate should be announced in the `#stacks-core-devs` channel in the
   Stacks Discord. For coordinating rollouts on specific infrastructure, the release
   manager should contact the above participants directly either through e-mail or
   Discord DM. The release manager should also confirm that the built release on the
   [Github releases](https://github.com/blockstack/stacks-blockchain/releases/)
   page is marked as `Pre-Release`.

1. The release manager will test that the release candidate successfully syncs with
   the current chain from genesis both in testnet and mainnet. This requires starting
   the release candidate with an empty chainstate and confirming that it synchronizes
   with the current chain tip.

1. If bugs or issues emerge from the rollout on staging infrastructure, the release
   will be delayed until those regressions are resolved. As regressions are resolved,
   additional release candidates should be tagged. The release manager is responsible
   for updating the `develop -> master` PR with information about the discovered issues,
   even if other community members and developers may be addressing the discovered
   issues.

1. Once the final release candidate has rolled out successfully without issue on the
   above staging infrastructure, the release manager tags 2 additional `stacks-blockchain`
   team members to review the `develop -> master` PR.

1. Once reviewed and approved, the release manager merges the PR, and tags the release
   via the [`stacks-blockchain` Github action]((https://github.com/blockstack/stacks-blockchain/actions/workflows/stacks-blockchain.yml))
   by clicking "Run workflow" and providing the release version as the tag (e.g.,
   `2.0.11.1.0`) This creates a release and release images. Once the release has been
   created, the release manager should update the Github release text with the
   `CHANGELOG.md` "top-matter" for the release.

## Copyright and License

The code and documentation copyright are attributed to blockstack.org for the year of 2020.

This code is released under [the GPL v3 license](https://www.gnu.org/licenses/quick-guide-gplv3.en.html), and the docs are released under [the Creative Commons license](https://creativecommons.org/).
