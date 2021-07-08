// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2021 Stacks Open Internet Foundation
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use ed25519_dalek::Keypair as VRFKeypair;
use rand::rngs::ThreadRng;
use rand::thread_rng;
use serde::Serialize;
use sha2::Sha512;

use crate::types::chainstate::StacksAddress;
use crate::types::proof::TrieHash;
use address::AddressHashMode;
use burnchains::affirmation::*;
use burnchains::bitcoin::address::*;
use burnchains::bitcoin::keys::BitcoinPublicKey;
use burnchains::bitcoin::*;
use burnchains::*;
use burnchains::{BurnchainBlock, BurnchainBlockHeader, Txid};
use chainstate::burn::db::sortdb::{SortitionDB, SortitionHandleTx};
use chainstate::burn::distribution::BurnSamplePoint;
use chainstate::burn::operations::{
    leader_block_commit::BURN_BLOCK_MINED_AT_MODULUS, BlockstackOperationType, LeaderBlockCommitOp,
    LeaderKeyRegisterOp, UserBurnSupportOp,
};
use chainstate::burn::{BlockSnapshot, ConsensusHash, OpsHash, SortitionHash};
use chainstate::stacks::StacksPublicKey;
use util::db::Error as db_error;
use util::get_epoch_time_secs;
use util::hash::hex_bytes;
use util::hash::to_hex;
use util::hash::Hash160;
use util::log;
use util::secp256k1::Secp256k1PrivateKey;
use util::uint::BitArray;
use util::uint::Uint256;
use util::uint::Uint512;
use util::vrf::VRFPrivateKey;
use util::vrf::VRFPublicKey;

use crate::types::chainstate::{BlockHeaderHash, BurnchainHeaderHash, PoxId, SortitionId, VRFSeed};

#[test]
fn test_process_block_ops() {
    let first_burn_hash = BurnchainHeaderHash::from_hex(
        "0000000000000000000000000000000000000000000000000000000000000123",
    )
    .unwrap();
    let first_block_height = 120;

    let burnchain = Burnchain {
        pox_constants: PoxConstants::test_default(),
        peer_version: 0x012345678,
        network_id: 0x9abcdef0,
        chain_name: "bitcoin".to_string(),
        network_name: "testnet".to_string(),
        working_dir: "/nope".to_string(),
        consensus_hash_lifetime: 24,
        stable_confirmations: 7,
        first_block_height,
        initial_reward_start_block: first_block_height,
        first_block_timestamp: 0,
        first_block_hash: BurnchainHeaderHash::zero(),
    };
    let first_burn_hash = BurnchainHeaderHash::from_hex(
        "0000000000000000000000000000000000000000000000000000000000000123",
    )
    .unwrap();
    let block_121_hash = BurnchainHeaderHash::from_hex(
        "0000000000000000000000000000000000000000000000000000000000000012",
    )
    .unwrap();
    let block_122_hash = BurnchainHeaderHash::from_hex(
        "0000000000000000000000000000000000000000000000000000000000000002",
    )
    .unwrap();
    let block_123_hash = BurnchainHeaderHash::from_hex(
        "0000000000000000000000000000000000000000000000000000000000000001",
    )
    .unwrap();
    let block_124_hash_initial = BurnchainHeaderHash::from_hex(
        "0000000000000000000000000000000000000000000000000000000000000004",
    )
    .unwrap();

    let leader_key_1 = LeaderKeyRegisterOp {
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a").unwrap(),
        )
        .unwrap(),
        memo: vec![01, 02, 03, 04, 05],
        address: StacksAddress::from_bitcoin_address(
            &BitcoinAddress::from_scriptpubkey(
                BitcoinNetworkType::Testnet,
                &hex_bytes("76a914306231b2782b5f80d944bf69f9d46a1453a0a0eb88ac").unwrap(),
            )
            .unwrap(),
        ),

        txid: Txid::from_bytes(
            &hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562").unwrap(),
        )
        .unwrap(),
        vtxindex: 456,
        block_height: 123,
        burn_header_hash: block_123_hash.clone(),
    };

    let leader_key_2 = LeaderKeyRegisterOp {
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("bb519494643f79f1dea0350e6fb9a1da88dfdb6137117fc2523824a8aa44fe1c").unwrap(),
        )
        .unwrap(),
        memo: vec![01, 02, 03, 04, 05],
        address: StacksAddress::from_bitcoin_address(
            &BitcoinAddress::from_scriptpubkey(
                BitcoinNetworkType::Testnet,
                &hex_bytes("76a914306231b2782b5f80d944bf69f9d46a1453a0a0eb88ac").unwrap(),
            )
            .unwrap(),
        ),

        txid: Txid::from_bytes(
            &hex_bytes("9410df84e2b440055c33acb075a0687752df63fe8fe84aeec61abe469f0448c7").unwrap(),
        )
        .unwrap(),
        vtxindex: 457,
        block_height: 122,
        burn_header_hash: block_122_hash.clone(),
    };

    let leader_key_3 = LeaderKeyRegisterOp {
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("de8af7037e522e65d2fe2d63fb1b764bfea829df78b84444338379df13144a02").unwrap(),
        )
        .unwrap(),
        memo: vec![01, 02, 03, 04, 05],
        address: StacksAddress::from_bitcoin_address(
            &BitcoinAddress::from_scriptpubkey(
                BitcoinNetworkType::Testnet,
                &hex_bytes("76a914f464a593895cd58c74a7352dd4a65c491d0c0bf688ac").unwrap(),
            )
            .unwrap(),
        ),

        txid: Txid::from_bytes(
            &hex_bytes("eb54704f71d4a2d1128d60ffccced547054b52250ada6f3e7356165714f44d4c").unwrap(),
        )
        .unwrap(),
        vtxindex: 10,
        block_height: 121,
        burn_header_hash: block_121_hash.clone(),
    };

    let user_burn_1 = UserBurnSupportOp {
        address: StacksAddress::new(1, Hash160([1u8; 20])),
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a").unwrap(),
        )
        .unwrap(),
        block_header_hash_160: Hash160::from_bytes(
            &hex_bytes("7150f635054b87df566a970b21e07030d6444bf2").unwrap(),
        )
        .unwrap(), // 22222....2222
        key_block_ptr: 123,
        key_vtxindex: 456,
        burn_fee: 10000,

        txid: Txid::from_bytes(
            &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716b").unwrap(),
        )
        .unwrap(),
        vtxindex: 13,
        block_height: 124,
        burn_header_hash: block_124_hash_initial.clone(),
    };

    let user_burn_1_2 = UserBurnSupportOp {
        address: StacksAddress::new(2, Hash160([2u8; 20])),
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a").unwrap(),
        )
        .unwrap(),
        block_header_hash_160: Hash160::from_bytes(
            &hex_bytes("7150f635054b87df566a970b21e07030d6444bf2").unwrap(),
        )
        .unwrap(), // 22222....2222
        key_block_ptr: 123,
        key_vtxindex: 456,
        burn_fee: 30000,

        txid: Txid::from_bytes(
            &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716c").unwrap(),
        )
        .unwrap(),
        vtxindex: 14,
        block_height: 124,
        burn_header_hash: block_124_hash_initial.clone(),
    };

    let user_burn_2 = UserBurnSupportOp {
        address: StacksAddress::new(3, Hash160([3u8; 20])),
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("bb519494643f79f1dea0350e6fb9a1da88dfdb6137117fc2523824a8aa44fe1c").unwrap(),
        )
        .unwrap(),
        block_header_hash_160: Hash160::from_bytes(
            &hex_bytes("037a1e860899a4fa823c18b66f6264d20236ec58").unwrap(),
        )
        .unwrap(), // 22222....2223
        key_block_ptr: 122,
        key_vtxindex: 457,
        burn_fee: 20000,

        txid: Txid::from_bytes(
            &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716d").unwrap(),
        )
        .unwrap(),
        vtxindex: 15,
        block_height: 124,
        burn_header_hash: block_124_hash_initial.clone(),
    };

    let user_burn_2_2 = UserBurnSupportOp {
        address: StacksAddress::new(4, Hash160([4u8; 20])),
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("bb519494643f79f1dea0350e6fb9a1da88dfdb6137117fc2523824a8aa44fe1c").unwrap(),
        )
        .unwrap(),
        block_header_hash_160: Hash160::from_bytes(
            &hex_bytes("037a1e860899a4fa823c18b66f6264d20236ec58").unwrap(),
        )
        .unwrap(), // 22222....2223
        key_block_ptr: 122,
        key_vtxindex: 457,
        burn_fee: 40000,

        txid: Txid::from_bytes(
            &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716e").unwrap(),
        )
        .unwrap(),
        vtxindex: 16,
        block_height: 124,
        burn_header_hash: block_124_hash_initial.clone(),
    };

    // should be rejected
    let user_burn_noblock = UserBurnSupportOp {
        address: StacksAddress::new(5, Hash160([5u8; 20])),
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a").unwrap(),
        )
        .unwrap(),
        block_header_hash_160: Hash160::from_bytes(
            &hex_bytes("3333333333333333333333333333333333333333").unwrap(),
        )
        .unwrap(),
        key_block_ptr: 122,
        key_vtxindex: 772,
        burn_fee: 12345,

        txid: Txid::from_bytes(
            &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716f").unwrap(),
        )
        .unwrap(),
        vtxindex: 12,
        block_height: 123,
        burn_header_hash: block_123_hash.clone(),
    };

    // should be rejected
    let user_burn_nokey = UserBurnSupportOp {
        address: StacksAddress::new(6, Hash160([6u8; 20])),
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("3f3338db51f2b1f6ac0cf6177179a24ee130c04ef2f9849a64a216969ab60e70").unwrap(),
        )
        .unwrap(),
        block_header_hash_160: Hash160::from_bytes(
            &hex_bytes("037a1e860899a4fa823c18b66f6264d20236ec58").unwrap(),
        )
        .unwrap(),
        key_block_ptr: 122,
        key_vtxindex: 457,
        burn_fee: 12345,

        txid: Txid::from_bytes(
            &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c7170").unwrap(),
        )
        .unwrap(),
        vtxindex: 15,
        block_height: 123,
        burn_header_hash: block_123_hash.clone(),
    };

    let block_commit_1 = LeaderBlockCommitOp {
        sunset_burn: 0,
        commit_outs: vec![],
        block_header_hash: BlockHeaderHash::from_bytes(
            &hex_bytes("2222222222222222222222222222222222222222222222222222222222222222").unwrap(),
        )
        .unwrap(),
        new_seed: VRFSeed::from_bytes(
            &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333").unwrap(),
        )
        .unwrap(),
        parent_block_ptr: 0,
        parent_vtxindex: 0,
        key_block_ptr: 123,
        key_vtxindex: 456,
        memo: vec![0x80],

        burn_fee: 12345,
        input: (Txid([0; 32]), 0),
        apparent_sender: BurnchainSigner {
            public_keys: vec![StacksPublicKey::from_hex(
                "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
            )
            .unwrap()],
            num_sigs: 1,
            hash_mode: AddressHashMode::SerializeP2PKH,
        },

        txid: Txid::from_bytes(
            &hex_bytes("3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf").unwrap(),
        )
        .unwrap(),
        vtxindex: 444,
        block_height: 124,
        burn_parent_modulus: (123 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
        burn_header_hash: block_124_hash_initial.clone(),
    };

    let block_commit_2 = LeaderBlockCommitOp {
        sunset_burn: 0,
        commit_outs: vec![],
        block_header_hash: BlockHeaderHash::from_bytes(
            &hex_bytes("2222222222222222222222222222222222222222222222222222222222222223").unwrap(),
        )
        .unwrap(),
        new_seed: VRFSeed::from_bytes(
            &hex_bytes("3333333333333333333333333333333333333333333333333333333333333334").unwrap(),
        )
        .unwrap(),
        parent_block_ptr: 0,
        parent_vtxindex: 0,
        key_block_ptr: 122,
        key_vtxindex: 457,
        memo: vec![0x80],

        burn_fee: 12345,
        input: (Txid([0; 32]), 0),
        apparent_sender: BurnchainSigner {
            public_keys: vec![StacksPublicKey::from_hex(
                "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
            )
            .unwrap()],
            num_sigs: 1,
            hash_mode: AddressHashMode::SerializeP2PKH,
        },

        txid: Txid::from_bytes(
            &hex_bytes("3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27d0").unwrap(),
        )
        .unwrap(),
        vtxindex: 445,
        block_height: 124,
        burn_parent_modulus: (123 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
        burn_header_hash: block_124_hash_initial.clone(),
    };

    let block_commit_3 = LeaderBlockCommitOp {
        sunset_burn: 0,
        commit_outs: vec![],
        block_header_hash: BlockHeaderHash::from_bytes(
            &hex_bytes("2222222222222222222222222222222222222222222222222222222222222224").unwrap(),
        )
        .unwrap(),
        new_seed: VRFSeed::from_bytes(
            &hex_bytes("3333333333333333333333333333333333333333333333333333333333333335").unwrap(),
        )
        .unwrap(),
        parent_block_ptr: 0,
        parent_vtxindex: 0,
        key_block_ptr: 121,
        key_vtxindex: 10,
        memo: vec![0x80],

        burn_fee: 23456,
        input: (Txid([0; 32]), 0),
        apparent_sender: BurnchainSigner {
            public_keys: vec![StacksPublicKey::from_hex(
                "0283d603abdd2392646dbdd0dc80beb39c25bfab96a8a921ea5e7517ce533f8cd5",
            )
            .unwrap()],
            num_sigs: 1,
            hash_mode: AddressHashMode::SerializeP2PKH,
        },

        txid: Txid::from_bytes(
            &hex_bytes("301dc687a9f06a1ae87a013f27133e9cec0843c2983567be73e185827c7c13de").unwrap(),
        )
        .unwrap(),
        vtxindex: 446,
        block_height: 124,
        burn_parent_modulus: (123 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
        burn_header_hash: block_124_hash_initial.clone(),
    };

    let block_ops_121: Vec<BlockstackOperationType> =
        vec![BlockstackOperationType::LeaderKeyRegister(
            leader_key_3.clone(),
        )];
    let block_opshash_121 = OpsHash::from_txids(&vec![leader_key_3.txid.clone()]);
    let block_prev_chs_121 =
        vec![ConsensusHash::from_hex("0000000000000000000000000000000000000000").unwrap()];
    let mut block_121_snapshot = BlockSnapshot {
        accumulated_coinbase_ustx: 0,
        pox_valid: true,
        block_height: 121,
        burn_header_hash: block_121_hash.clone(),
        sortition_id: SortitionId(block_121_hash.0.clone()),
        parent_sortition_id: SortitionId(block_121_hash.0.clone()),
        burn_header_timestamp: 121,
        parent_burn_header_hash: first_burn_hash.clone(),
        ops_hash: block_opshash_121.clone(),
        consensus_hash: ConsensusHash::from_ops(
            &block_121_hash,
            &block_opshash_121,
            0,
            &block_prev_chs_121,
            &PoxId::stubbed(),
        ),
        total_burn: 0,
        sortition: false,
        sortition_hash: SortitionHash::initial().mix_burn_header(&block_121_hash),
        winning_block_txid: Txid::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap(),
        winning_stacks_block_hash: BlockHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap(),
        index_root: TrieHash::from_empty_data(), // TBD
        num_sortitions: 0,
        stacks_block_accepted: false,
        stacks_block_height: 0,
        arrival_index: 0,
        canonical_stacks_tip_height: 0,
        canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
        canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
        ..BlockSnapshot::initial(0, &first_burn_hash, 0)
    };

    let block_ops_122: Vec<BlockstackOperationType> =
        vec![BlockstackOperationType::LeaderKeyRegister(
            leader_key_2.clone(),
        )];
    let block_opshash_122 = OpsHash::from_txids(&vec![leader_key_2.txid.clone()]);
    let block_prev_chs_122 = vec![
        block_121_snapshot.consensus_hash.clone(),
        ConsensusHash::from_hex("0000000000000000000000000000000000000000").unwrap(),
    ];
    let mut block_122_snapshot = BlockSnapshot {
        accumulated_coinbase_ustx: 0,
        pox_valid: true,
        block_height: 122,
        burn_header_hash: block_122_hash.clone(),
        sortition_id: SortitionId(block_122_hash.0.clone()),
        parent_sortition_id: block_121_snapshot.sortition_id.clone(),
        burn_header_timestamp: 122,
        parent_burn_header_hash: block_121_hash.clone(),
        ops_hash: block_opshash_122.clone(),
        consensus_hash: ConsensusHash::from_ops(
            &block_122_hash,
            &block_opshash_122,
            0,
            &block_prev_chs_122,
            &PoxId::stubbed(),
        ),
        total_burn: 0,
        sortition: false,
        sortition_hash: SortitionHash::initial()
            .mix_burn_header(&block_121_hash)
            .mix_burn_header(&block_122_hash),
        winning_block_txid: Txid::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap(),
        winning_stacks_block_hash: BlockHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap(),
        index_root: TrieHash::from_empty_data(), // TBD
        num_sortitions: 0,
        stacks_block_accepted: false,
        stacks_block_height: 0,
        arrival_index: 0,
        canonical_stacks_tip_height: 0,
        canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
        canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
        ..BlockSnapshot::initial(0, &first_burn_hash, 0)
    };

    let block_ops_123: Vec<BlockstackOperationType> = vec![
        BlockstackOperationType::UserBurnSupport(user_burn_noblock.clone()),
        BlockstackOperationType::UserBurnSupport(user_burn_nokey.clone()),
        BlockstackOperationType::LeaderKeyRegister(leader_key_1.clone()),
    ];
    let block_opshash_123 = OpsHash::from_txids(&vec![
        // notably, the user burns here _wont_ be included in the consensus hash
        leader_key_1.txid.clone(),
    ]);
    let block_prev_chs_123 = vec![
        block_122_snapshot.consensus_hash.clone(),
        block_121_snapshot.consensus_hash.clone(),
    ];
    let mut block_123_snapshot = BlockSnapshot {
        accumulated_coinbase_ustx: 0,
        pox_valid: true,
        block_height: 123,
        burn_header_hash: block_123_hash.clone(),
        sortition_id: SortitionId(block_123_hash.0.clone()),
        parent_sortition_id: block_122_snapshot.sortition_id.clone(),
        burn_header_timestamp: 123,
        parent_burn_header_hash: block_122_hash.clone(),
        ops_hash: block_opshash_123.clone(),
        consensus_hash: ConsensusHash::from_ops(
            &block_123_hash,
            &block_opshash_123,
            0,
            &block_prev_chs_123,
            &PoxId::stubbed(),
        ), // user burns not included, so zero burns this block
        total_burn: 0,
        sortition: false,
        sortition_hash: SortitionHash::initial()
            .mix_burn_header(&block_121_hash)
            .mix_burn_header(&block_122_hash)
            .mix_burn_header(&block_123_hash),
        winning_block_txid: Txid::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap(),
        winning_stacks_block_hash: BlockHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap(),
        index_root: TrieHash::from_empty_data(), // TBD
        num_sortitions: 0,
        stacks_block_accepted: false,
        stacks_block_height: 0,
        arrival_index: 0,
        canonical_stacks_tip_height: 0,
        canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
        canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
        ..BlockSnapshot::initial(0, &first_burn_hash, 0)
    };

    // multiple possibilities for block 124 -- we'll reorg the chain each time back to 123 and
    // re-try block 124 to test them all.
    let block_ops_124_possibilities = vec![
        vec![BlockstackOperationType::LeaderBlockCommit(
            block_commit_1.clone(),
        )],
        vec![
            BlockstackOperationType::LeaderBlockCommit(block_commit_1.clone()),
            BlockstackOperationType::LeaderBlockCommit(block_commit_2.clone()),
            BlockstackOperationType::LeaderBlockCommit(block_commit_3.clone()),
        ],
        vec![
            BlockstackOperationType::LeaderBlockCommit(block_commit_1.clone()),
            BlockstackOperationType::LeaderBlockCommit(block_commit_2.clone()),
            BlockstackOperationType::LeaderBlockCommit(block_commit_3.clone()),
        ],
    ];

    let block_124_winners = vec![
        block_commit_1.clone(),
        block_commit_3.clone(),
        block_commit_1.clone(),
    ];

    let mut db = SortitionDB::connect_test(first_block_height, &first_burn_hash).unwrap();

    // NOTE: the .txs() method will NOT be called, so we can pass an empty vec![] here
    let block121 = BurnchainBlock::Bitcoin(BitcoinBlock::new(
        121,
        &block_121_hash,
        &first_burn_hash,
        &vec![],
        121,
    ));
    let block122 = BurnchainBlock::Bitcoin(BitcoinBlock::new(
        122,
        &block_122_hash,
        &block_121_hash,
        &vec![],
        122,
    ));
    let block123 = BurnchainBlock::Bitcoin(BitcoinBlock::new(
        123,
        &block_123_hash,
        &block_122_hash,
        &vec![],
        123,
    ));

    let initial_snapshot = BlockSnapshot::initial(
        first_block_height,
        &first_burn_hash,
        first_block_height as u64,
    );

    // process up to 124
    {
        let header = block121.header();
        let mut tx = SortitionHandleTx::begin(&mut db, &initial_snapshot.sortition_id).unwrap();

        let (sn121, _) = tx
            .process_block_ops(
                &burnchain,
                &initial_snapshot,
                &header,
                block_ops_121,
                None,
                PoxId::stubbed(),
                None,
                0,
            )
            .unwrap();
        tx.commit().unwrap();

        block_121_snapshot.index_root = sn121.index_root.clone();
        block_121_snapshot.parent_sortition_id = sn121.parent_sortition_id.clone();
        assert_eq!(sn121, block_121_snapshot);
    }
    {
        let header = block122.header();
        let mut tx = SortitionHandleTx::begin(&mut db, &block_121_snapshot.sortition_id).unwrap();

        let (sn122, _) = tx
            .process_block_ops(
                &burnchain,
                &block_121_snapshot,
                &header,
                block_ops_122,
                None,
                PoxId::stubbed(),
                None,
                0,
            )
            .unwrap();
        tx.commit().unwrap();

        block_122_snapshot.index_root = sn122.index_root.clone();
        block_122_snapshot.parent_sortition_id = sn122.parent_sortition_id.clone();
        assert_eq!(sn122, block_122_snapshot);
    }
    {
        let header = block123.header();
        let mut tx = SortitionHandleTx::begin(&mut db, &block_122_snapshot.sortition_id).unwrap();
        let (sn123, _) = tx
            .process_block_ops(
                &burnchain,
                &block_122_snapshot,
                &header,
                block_ops_123,
                None,
                PoxId::stubbed(),
                None,
                0,
            )
            .unwrap();
        tx.commit().unwrap();

        block_123_snapshot.index_root = sn123.index_root.clone();
        block_123_snapshot.parent_sortition_id = sn123.parent_sortition_id.clone();
        assert_eq!(sn123, block_123_snapshot);
    }

    for scenario_idx in 0..block_ops_124_possibilities.len() {
        let mut block_ops_124 = block_ops_124_possibilities[scenario_idx].clone();
        let mut block_124_hash_bytes = block_124_hash_initial.as_bytes().clone();
        block_124_hash_bytes[0] = (scenario_idx + 1) as u8;
        let block_124_hash = BurnchainHeaderHash(block_124_hash_bytes);

        for op in block_ops_124.iter_mut() {
            op.set_burn_header_hash(block_124_hash.clone());
        }

        // everything will be included
        let block_opshash_124 = OpsHash::from_txids(
            &block_ops_124
                .clone()
                .into_iter()
                .map(|bo| bo.txid())
                .collect(),
        );
        let block_prev_chs_124 = vec![
            block_123_snapshot.consensus_hash.clone(),
            block_122_snapshot.consensus_hash.clone(),
            ConsensusHash::from_hex("0000000000000000000000000000000000000000").unwrap(),
        ];

        let burn_total = block_ops_124.iter().fold(0u64, |mut acc, op| {
            let bf = match op {
                BlockstackOperationType::LeaderBlockCommit(ref op) => op.burn_fee,
                BlockstackOperationType::UserBurnSupport(ref op) => 0,
                _ => 0,
            };
            acc += bf;
            acc
        });

        let next_sortition = block_ops_124.len() > 0 && burn_total > 0;

        let mut block_124_snapshot = BlockSnapshot {
            accumulated_coinbase_ustx: 400_000_000,
            pox_valid: true,
            block_height: 124,
            burn_header_hash: block_124_hash.clone(),
            sortition_id: SortitionId(block_124_hash.0.clone()),
            parent_sortition_id: block_123_snapshot.sortition_id.clone(),
            burn_header_timestamp: 124,
            parent_burn_header_hash: block_123_snapshot.burn_header_hash.clone(),
            ops_hash: block_opshash_124.clone(),
            consensus_hash: ConsensusHash::from_ops(
                &block_124_hash,
                &block_opshash_124,
                burn_total,
                &block_prev_chs_124,
                &PoxId::stubbed(),
            ),
            total_burn: burn_total,
            sortition: next_sortition,
            sortition_hash: SortitionHash::initial()
                .mix_burn_header(&block_121_hash)
                .mix_burn_header(&block_122_hash)
                .mix_burn_header(&block_123_hash)
                .mix_burn_header(&block_124_hash),
            winning_block_txid: block_124_winners[scenario_idx].txid.clone(),
            winning_stacks_block_hash: block_124_winners[scenario_idx].block_header_hash.clone(),
            index_root: TrieHash::from_empty_data(), // TDB
            num_sortitions: if next_sortition { 1 } else { 0 },
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: 0,
            canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
            canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
            ..BlockSnapshot::initial(0, &first_burn_hash, 0)
        };

        if next_sortition {
            block_124_snapshot.sortition_hash = block_124_snapshot
                .sortition_hash
                .mix_VRF_seed(&block_124_winners[scenario_idx].new_seed);
        }

        let block124 = BurnchainBlock::Bitcoin(BitcoinBlock::new(
            124,
            &block_124_hash,
            &block_123_hash,
            &vec![],
            124,
        ));

        // process this scenario
        let sn124 = {
            let header = block124.header();
            let mut tx =
                SortitionHandleTx::begin(&mut db, &block_123_snapshot.sortition_id).unwrap();
            let (sn124, _) = tx
                .process_block_ops(
                    &burnchain,
                    &block_123_snapshot,
                    &header,
                    block_ops_124,
                    None,
                    PoxId::stubbed(),
                    None,
                    0,
                )
                .unwrap();
            tx.commit().unwrap();

            block_124_snapshot.index_root = sn124.index_root.clone();
            block_124_snapshot.parent_sortition_id = sn124.parent_sortition_id.clone();
            sn124
        };

        assert_eq!(sn124, block_124_snapshot);

        // get all winning block commit hashes.
        // There should only be two -- the winning block at height 124, and the genesis
        // sentinel block hash.  This is because epochs 121, 122, and 123 don't have any block
        // commits.
        let expected_winning_hashes = vec![
            BlockHeaderHash([0u8; 32]),
            block_124_winners[scenario_idx].block_header_hash.clone(),
        ];

        // TODO: pair up with stacks chain state?
        /*
        let winning_header_hashes = {
            let mut tx = db.tx_begin().unwrap();
            BurnDB::get_stacks_block_header_inventory(&mut tx, 124).unwrap()
                .iter()
                .map(|ref hinv| hinv.0.clone())
                .collect()
        };

        assert_eq!(expected_winning_hashes, winning_header_hashes);
        */
    }
}

#[test]
fn test_burn_snapshot_sequence() {
    let first_burn_hash = BurnchainHeaderHash::from_hex(
        "0000000000000000000000000000000000000000000000000000000000000123",
    )
    .unwrap();
    let first_block_height = 120;

    let burnchain = Burnchain {
        pox_constants: PoxConstants::test_default(),
        peer_version: 0x012345678,
        network_id: 0x9abcdef0,
        chain_name: "bitcoin".to_string(),
        network_name: "testnet".to_string(),
        working_dir: "/nope".to_string(),
        consensus_hash_lifetime: 24,
        stable_confirmations: 7,
        first_block_timestamp: 0,
        first_block_hash: first_burn_hash,
        first_block_height,
        initial_reward_start_block: first_block_height,
    };

    let mut leader_private_keys = vec![];
    let mut leader_public_keys = vec![];
    let mut leader_bitcoin_public_keys = vec![];
    let mut leader_bitcoin_addresses = vec![];

    for i in 0..32 {
        let mut csprng: ThreadRng = thread_rng();
        let keypair: VRFKeypair = VRFKeypair::generate(&mut csprng);

        let privkey_hex = to_hex(&keypair.secret.to_bytes());
        leader_private_keys.push(privkey_hex);

        let pubkey_hex = to_hex(&keypair.public.to_bytes());
        leader_public_keys.push(pubkey_hex);

        let bitcoin_privkey = Secp256k1PrivateKey::new();
        let bitcoin_publickey = BitcoinPublicKey::from_private(&bitcoin_privkey);

        leader_bitcoin_public_keys.push(to_hex(&bitcoin_publickey.to_bytes()));

        let btc_input = BitcoinTxInput {
            in_type: BitcoinInputType::Standard,
            keys: vec![bitcoin_publickey.clone()],
            num_required: 1,
            tx_ref: (Txid([0; 32]), 0),
        };

        leader_bitcoin_addresses.push(
            BitcoinAddress::from_bytes(
                BitcoinNetworkType::Testnet,
                BitcoinAddressType::PublicKeyHash,
                &btc_input.to_address_bits(),
            )
            .unwrap(),
        );
    }

    let mut expected_burn_total: u64 = 0;

    // insert all operations
    let mut db = SortitionDB::connect_test(first_block_height, &first_burn_hash).unwrap();
    let mut prev_snapshot = BlockSnapshot::initial(
        first_block_height,
        &first_burn_hash,
        first_block_height as u64,
    );
    let mut all_stacks_block_hashes = vec![];

    for i in 0..32 {
        let mut block_ops = vec![];
        let burn_block_hash = BurnchainHeaderHash::from_bytes(&vec![
            i + 1,
            i + 1,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            i + 1,
        ])
        .unwrap();
        let parent_burn_block_hash = prev_snapshot.burn_header_hash.clone();
        let parent_index_root = prev_snapshot.index_root.clone();

        // insert block commit paired to previous round's leader key, as well as a user burn
        if i > 0 {
            let next_block_commit = LeaderBlockCommitOp {
                sunset_burn: 0,
                commit_outs: vec![],
                block_header_hash: BlockHeaderHash::from_bytes(&vec![
                    i, i, i, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0,
                ])
                .unwrap(),
                new_seed: VRFSeed::from_bytes(&vec![
                    i, i, i, i, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0,
                ])
                .unwrap(),
                parent_block_ptr: (if i == 1 {
                    0
                } else {
                    first_block_height + (i as u64)
                }) as u32,
                parent_vtxindex: (if i == 1 { 0 } else { 2 * (i - 1) }) as u16,
                key_block_ptr: (first_block_height + (i as u64)) as u32,
                key_vtxindex: (2 * (i - 1) + 1) as u16,
                memo: vec![i],

                burn_fee: i as u64,
                input: (Txid([0; 32]), 0),
                apparent_sender: BurnchainSigner {
                    public_keys: vec![StacksPublicKey::from_hex(
                        &leader_bitcoin_public_keys[(i - 1) as usize].clone(),
                    )
                    .unwrap()],
                    num_sigs: 1,
                    hash_mode: AddressHashMode::SerializeP2PKH,
                },

                txid: Txid::from_bytes(&vec![
                    i, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, i,
                ])
                .unwrap(),
                vtxindex: (2 * i) as u32,
                block_height: first_block_height + ((i + 1) as u64),
                burn_parent_modulus: ((first_block_height + (i as u64))
                    % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                burn_header_hash: burn_block_hash.clone(),
            };

            all_stacks_block_hashes.push(next_block_commit.block_header_hash.clone());
            block_ops.push(BlockstackOperationType::LeaderBlockCommit(
                next_block_commit,
            ));
        }

        let ch = {
            let ic = db.index_handle(&prev_snapshot.sortition_id);
            ic.get_consensus_at((i as u64) + first_block_height)
                .unwrap()
                .unwrap_or(ConsensusHash::empty())
        };

        let next_leader_key = LeaderKeyRegisterOp {
            consensus_hash: ch.clone(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes(&leader_public_keys[i as usize]).unwrap(),
            )
            .unwrap(),
            memo: vec![0, 0, 0, 0, i],
            address: StacksAddress::from_bitcoin_address(
                &leader_bitcoin_addresses[i as usize].clone(),
            ),

            txid: Txid::from_bytes(&vec![
                i, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ])
            .unwrap(),
            vtxindex: (2 * i + 1) as u32,
            block_height: first_block_height + (i + 1) as u64,
            burn_header_hash: burn_block_hash.clone(),
        };

        block_ops.push(BlockstackOperationType::LeaderKeyRegister(next_leader_key));

        let block = BurnchainBlock::Bitcoin(BitcoinBlock::new(
            first_block_height + (i + 1) as u64,
            &burn_block_hash,
            &parent_burn_block_hash,
            &vec![],
            get_epoch_time_secs(),
        ));

        // process this block
        let snapshot = {
            let header = block.header();
            let mut tx = SortitionHandleTx::begin(&mut db, &prev_snapshot.sortition_id).unwrap();
            let (sn, _) = tx
                .process_block_ops(
                    &burnchain,
                    &prev_snapshot,
                    &header,
                    block_ops,
                    None,
                    PoxId::stubbed(),
                    None,
                    0,
                )
                .unwrap();
            tx.commit().unwrap();
            sn
        };

        if i > 0 {
            expected_burn_total += i as u64;

            assert_eq!(snapshot.total_burn, expected_burn_total);
            assert_eq!(
                snapshot.winning_block_txid,
                Txid::from_bytes(&vec![
                    i, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, i
                ])
                .unwrap()
            );
            assert_eq!(
                snapshot.winning_stacks_block_hash,
                BlockHeaderHash::from_bytes(&vec![
                    i, i, i, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0
                ])
                .unwrap()
            );
            assert_eq!(snapshot.burn_header_hash, burn_block_hash);
            assert_eq!(snapshot.parent_burn_header_hash, parent_burn_block_hash);
            assert_eq!(snapshot.block_height, (i as u64) + 1 + first_block_height);
            assert!(snapshot.sortition);
        } else {
            assert!(!snapshot.sortition);
            assert_eq!(snapshot.total_burn, 0);
        }

        prev_snapshot = snapshot;
    }
}
