Use the following template to create your pull request

<!--
  IMPORTANT
  Pull requests are ideal for making small changes to this project. However, they are NOT an appropriate venue to introducing non-trivial or breaking changes to the codebase.

  For introducing non-trivial or breaking changes to the codebase, please follow the SIP (Stacks Improvement Proposal) process documented here:
  https://github.com/blockstack/stacks-blockchain/blob/master/sip/sip-000-stacks-improvement-proposal-process.md.
-->

## Description

Describe the changes that where made in this pull request. When possible start with a user story - short, simple descriptions of a feature told from the perspective of the person who desires the new capability. Be sure to also include the following information:

1. Motivation for change
2. What was changed
3. How does this impact application developers
4. Link to relevant issues and documentation
5. Provide examples of use cases with code samples and applicable acceptance criteria

Example:
As a Blockstack developer, I would like to encrypt files using the app private key. This is needed because storing unencrypted files is unacceptable. This pull request adds the `encryptContent` function which will take a string and encrypt it using the app private key.

```
encryptContent('my data')

// Running the above should result in the following encrypted data object
{"iv":"c91...","ephemeralPK":"031...","cipherText":"d61...","mac":"e73..."}
```

For details refer to issue #123

## Type of Change
- [ ] New feature
- [ ] Bug fix
- [ ] API reference/documentation update
- [ ] Other

## Does this introduce a breaking change?
The blockchain has low tolerance for most kinds of breaking changes, while upgrades require a high degree of coordination with the network participants.
Pull requests are NOT an appropriate venue for introducing _breaking_ changes and they will be rejected.
Instead, please follow [the SIP (Stacks Improvement Proposal) process documented here](https://github.com/blockstack/stacks-blockchain/blob/master/sip/sip-000-stacks-improvement-proposal-process.md).

## Are documentation updates required?
<!-- 
  DOCUMENTATION
  Consider if this PR makes changes that require SIP (Stacks Improvement Proposal) or documentation updates:
    - API changes
    - Renamed methods
    - Change in instructions inside tutorials/guides
    - etc...

   The best way to find these is by:
     - searching inside the SIPs at https://github.com/blockstack/stacks-blockchain/tree/master/sip
     - searching inside the docs at https://github.com/blockstack/docs
-->
- [ ] Link to documentation updates: 
- [ ] Link to SIP updates: 


## Testing information

Provide context on how tests should be performed.

1. Tests are required for all changes
1. If it’s a bug fix, list steps to reproduce the bug
1. Briefly mention affected code paths
1. List other affected projects if possible
1. Things to watch out for when testing
1. All PRs must have tests that explore all reasonably-reachable code paths. When possible, they must be unit tests (but integration tests may be accepted if the PR alters behaviors that are only observed when multiple nodes are running and communicating concurrently). Special attention must be paid to error paths on code that is reachable from the networking code.
1. Code that potentially leads to a denial of service (a node crash), such as the use of .unwrap(), unwrap_err(), or .expect(), is heavily discouraged.

## Checklist
- [ ] Code is commented where needed
- [ ] Formatter passes - `cargo fmt`
- [ ] Unit test coverage for new or modified code paths
- [ ] cargo tests pass - `cargo test`
- [ ] bitcoin integration tests pass - `docker build -f ./.github/actions/bitcoin-int-tests/Dockerfile.bitcoin-tests .`
- [ ] network integration tests pass - `./net-test/start.sh master`
- [ ] Changelog is updated
