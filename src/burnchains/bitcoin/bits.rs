// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020 Stacks Open Internet Foundation
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

use sha2::Digest;
use sha2::Sha256;

use address::public_keys_to_address_hash;
use address::AddressHashMode;
use burnchains::bitcoin::address::{BitcoinAddress, BitcoinAddressType};
use burnchains::bitcoin::keys::BitcoinPublicKey;
use burnchains::bitcoin::BitcoinNetworkType;
use burnchains::bitcoin::Error as btc_error;
use burnchains::bitcoin::{BitcoinInputType, BitcoinTxInput, BitcoinTxOutput};
use burnchains::PublicKey;
use burnchains::Txid;
use deps::bitcoin::blockdata::opcodes::All as btc_opcodes;
use deps::bitcoin::blockdata::opcodes::Class;
use deps::bitcoin::blockdata::script::{Builder, Instruction, Script};
use deps::bitcoin::blockdata::transaction::TxIn as BtcTxIn;
use deps::bitcoin::blockdata::transaction::TxOut as BtcTxOut;
use deps::bitcoin::util::hash::Sha256dHash;
use util::hash::Hash160;
use util::log;

use crate::types::chainstate::BurnchainHeaderHash;
use chainstate::stacks::{
    C32_ADDRESS_VERSION_MAINNET_MULTISIG, C32_ADDRESS_VERSION_MAINNET_SINGLESIG,
    C32_ADDRESS_VERSION_TESTNET_MULTISIG, C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
};

/// Parse a script into its structured constituant opcodes and data and collect them
pub fn parse_script<'a>(script: &'a Script) -> Vec<Instruction<'a>> {
    // we will have to accept non-minimial pushdata since there's at least one OP_RETURN
    // in the transaction stream that has this property already.
    script.iter(false).collect()
}

impl BitcoinTxInput {
    pub fn to_address_bits(&self) -> Vec<u8> {
        let hash_mode = match self.in_type {
            BitcoinInputType::Standard => {
                if self.keys.len() == 1 {
                    AddressHashMode::SerializeP2PKH
                } else {
                    AddressHashMode::SerializeP2SH
                }
            }
            BitcoinInputType::SegwitP2SH => {
                if self.keys.len() == 1 {
                    AddressHashMode::SerializeP2WPKH
                } else {
                    AddressHashMode::SerializeP2WSH
                }
            }
        };

        let h = public_keys_to_address_hash(&hash_mode, self.num_required, &self.keys);
        h.as_bytes().to_vec()
    }

    /// Parse a script instruction stream encoding a p2pkh scritpsig into a BitcoinTxInput
    pub fn from_bitcoin_p2pkh_script_sig(
        instructions: &Vec<Instruction>,
        input_txid: (Txid, u32),
    ) -> Option<BitcoinTxInput> {
        if instructions.len() != 2 {
            return None;
        }

        let i1 = &instructions[0];
        let i2 = &instructions[1];

        match (i1, i2) {
            (Instruction::PushBytes(ref _data1), Instruction::PushBytes(ref data2)) => {
                // data2 is a pubkey?
                match BitcoinPublicKey::from_slice(data2) {
                    Ok(pubkey) => {
                        // yup, one public key
                        Some(BitcoinTxInput {
                            tx_ref: input_txid,
                            keys: vec![pubkey],
                            num_required: 1,
                            in_type: BitcoinInputType::Standard,
                        })
                    }
                    Err(_e) => {
                        // not a p2pkh scriptsig
                        None
                    }
                }
            }
            (_, _) => {
                // anything else we don't recognize
                None
            }
        }
    }

    /// given the number of sigs required (m) and an array of pubkey pushbytes instructions, extract
    /// a burnchain tx input.  If segwit is True, then it means these pushbytes came from a witness
    /// program instead of a script-sig
    fn from_bitcoin_pubkey_pushbytes(
        num_sigs: usize,
        pubkey_pushbytes: &[Instruction],
        segwit: bool,
        input_txid: (Txid, u32),
    ) -> Option<BitcoinTxInput> {
        if num_sigs < 1 || pubkey_pushbytes.len() < 1 || pubkey_pushbytes.len() < num_sigs {
            test_debug!(
                "Not a multisig script: num_sigs = {}, num_pubkeys <= {}",
                num_sigs,
                pubkey_pushbytes.len()
            );
            return None;
        }

        // this script looks like a multisig script.  See if the
        // intermediate values are all pushdatas and that they are all
        // public keys.
        let mut keys: Vec<BitcoinPublicKey> = Vec::with_capacity(pubkey_pushbytes.len());

        for i in 0..pubkey_pushbytes.len() {
            let payload = match &pubkey_pushbytes[i] {
                Instruction::PushBytes(payload) => payload,
                _ => {
                    // not pushbytes, so this can't be a multisig script
                    test_debug!(
                        "Not a multisig script: Instruction {} is not a PushBytes",
                        i
                    );
                    return None;
                }
            };

            let pubk = BitcoinPublicKey::from_slice(payload);
            if pubk.is_err() {
                // not a public key
                test_debug!("Not a multisig script: pushbytes {} is not a public key", i);
                return None;
            }

            keys.push(pubk.unwrap());
        }

        Some(BitcoinTxInput {
            tx_ref: input_txid,
            keys: keys,
            num_required: num_sigs,
            in_type: if segwit {
                BitcoinInputType::SegwitP2SH
            } else {
                BitcoinInputType::Standard
            },
        })
    }

    /// Given the number of signatures required (m) and an array of Vec<u8>'s encoding public keys
    /// (both taken from a segwit program), extract a burnchain tx input.
    fn from_bitcoin_witness_pubkey_vecs(
        num_sigs: usize,
        pubkey_vecs: &[Vec<u8>],
        input_txid: (Txid, u32),
    ) -> Option<BitcoinTxInput> {
        if num_sigs < 1 || pubkey_vecs.len() < 1 || pubkey_vecs.len() < num_sigs {
            test_debug!(
                "Not a multisig script: num_sigs = {}, num_pubkeys <= {}",
                num_sigs,
                pubkey_vecs.len()
            );
            return None;
        }

        // this script looks like a multisig script.  See if the
        // intermediate values are all valid public keys.
        let mut keys: Vec<BitcoinPublicKey> = Vec::with_capacity(pubkey_vecs.len());

        for i in 0..pubkey_vecs.len() {
            let payload = &pubkey_vecs[i];
            let pubk = BitcoinPublicKey::from_slice(&payload[..]);
            if pubk.is_err() {
                // not a public key
                test_debug!("Not a multisig script: item {} is not a public key", i);
                return None;
            }

            keys.push(pubk.unwrap());
        }

        let tx_input = BitcoinTxInput {
            tx_ref: input_txid,
            keys: keys,
            num_required: num_sigs,
            in_type: BitcoinInputType::SegwitP2SH,
        };

        Some(tx_input)
    }

    /// parse the multisig scriptsig redeem script
    fn from_bitcoin_multisig_redeem_script(
        multisig_script: &Instruction,
        segwit: bool,
        input_txid: (Txid, u32),
    ) -> Option<BitcoinTxInput> {
        match multisig_script {
            Instruction::PushBytes(multisig_script_bytes) => {
                let multisig_script = Script::from(multisig_script_bytes.to_vec());
                let multisig_instructions = parse_script(&multisig_script);

                if multisig_instructions.len() < 4 {
                    // can't be a multisig script
                    test_debug!(
                        "Not a multisig script: keys pushdata has only {} instructions",
                        multisig_instructions.len()
                    );
                    return None;
                }

                match (
                    &multisig_instructions[0],
                    &multisig_instructions[multisig_instructions.len() - 2],
                    &multisig_instructions[multisig_instructions.len() - 1],
                ) {
                    (
                        Instruction::Op(op1),
                        Instruction::Op(op2),
                        Instruction::Op(btc_opcodes::OP_CHECKMULTISIG),
                    ) => {
                        // op1 and op2 must be integers
                        match (
                            btc_opcodes::from(*op1).classify(),
                            btc_opcodes::from(*op2).classify(),
                        ) {
                            (Class::PushNum(num_sigs), Class::PushNum(num_pubkeys)) => {
                                // the "#instructions - 3" comes from the OP_m, OP_n, and OP_CHECKMULTISIG
                                if num_sigs < 1
                                    || num_pubkeys < 1
                                    || num_pubkeys < num_sigs
                                    || num_pubkeys != (multisig_instructions.len() - 3) as i32
                                {
                                    test_debug!("Not a multisig script: num_sigs = {}, num_pubkeys = {}, num instructions = {}", num_sigs, num_pubkeys, multisig_instructions.len());
                                    return None;
                                }

                                let pubkey_pushbytes =
                                    &multisig_instructions[1..multisig_instructions.len() - 2];
                                if pubkey_pushbytes.len() as i32 != num_pubkeys {
                                    test_debug!("Not a multisig script: num_pubkeys = {}, num pushbytes = {}", num_sigs, num_pubkeys);
                                    return None;
                                }

                                BitcoinTxInput::from_bitcoin_pubkey_pushbytes(
                                    num_sigs as usize,
                                    pubkey_pushbytes,
                                    segwit,
                                    input_txid,
                                )
                            }
                            (_, _) => {
                                test_debug!(
                                    "Not a multisig script: missing num_sigs and/or num_pubkeys"
                                );
                                None
                            }
                        }
                    }
                    (_, _, _) => {
                        test_debug!(
                            "Not a multisig script: missing OP_m, OP_n, and/or OP_CHECKMULTISIG"
                        );
                        None
                    }
                }
            }
            _ => {
                test_debug!("Not a multisig script: not a PushBytes");
                None
            }
        }
    }

    /// parse a p2sh scriptsig
    fn from_bitcoin_p2sh_multisig_script_sig(
        instructions: &Vec<Instruction>,
        input_txid: (Txid, u32),
    ) -> Option<BitcoinTxInput> {
        // format: OP_0 <sig1> <sig2> ... <sig_m> OP_m <pubkey1> <pubkey2> ... <pubkey_n> OP_n OP_CHECKMULTISIG
        // the "OP_m <pubkey1> <pubkey2> ... <pubkey_n> OP_N OP_CHECKMULTISIG" is a single PushBytes
        if instructions.len() < 3 || instructions[0] != Instruction::PushBytes(&[]) {
            test_debug!(
                "Not a multisig script: {} instructions -- the first is {:?}",
                instructions.len(),
                instructions[0]
            );
            return None;
        }

        // verify that we got PUSHBYTES(<sig1>) PUSHBYTES(<sig2>) ... PUSHBYTES(<sigm>) PUSHBYTES(redeem script)
        for i in 1..instructions.len() {
            match instructions[i] {
                Instruction::PushBytes(_script) => {}
                _ => {
                    test_debug!(
                        "Not a multisig script: instruction {} is not a PushBytes: {:?}",
                        i,
                        instructions[i]
                    );
                    return None;
                }
            }
        }

        let redeem_script = &instructions[instructions.len() - 1];
        let tx_input_opt =
            BitcoinTxInput::from_bitcoin_multisig_redeem_script(redeem_script, false, input_txid);
        if tx_input_opt.is_none() {
            return None;
        }

        let tx_input = tx_input_opt.unwrap();

        // number of signatures must match number of required signatures (excluding OP_0 and PUSHDATA(redeem script))
        if instructions.len() - 2 != tx_input.num_required {
            test_debug!(
                "Not a multisig script: {} signatures, {} required",
                instructions.len() - 1,
                tx_input.num_required
            );
            return None;
        }

        Some(tx_input)
    }

    /// parse p2wpkh-over-p2sh public keys, given p2sh scriptsig as hash of witness
    fn from_bitcoin_p2wpkh_p2sh_script_sig(
        instructions: &Vec<Instruction>,
        witness: &Vec<Vec<u8>>,
        input_txid: (Txid, u32),
    ) -> Option<BitcoinTxInput> {
        // redeem script format: OP_PUSHDATA <20-byte witness hash>
        // witness format: <sig> <pubkey>
        if instructions.len() != 1 {
            test_debug!("Not a p2wpkh-over-p2sh script: invalid scriptsig");
            return None;
        }
        if witness.len() != 2 {
            test_debug!("Not a p2wpkh-over-p2sh script: invalid witness");
            return None;
        }

        match &instructions[0] {
            Instruction::PushBytes(witness_hash) => {
                // is this a viable witness hash?  00 <len> <hash>
                if witness_hash.len() != 22 {
                    test_debug!(
                        "Not a p2wpkh-over-p2sh script: invalid witness program hash length"
                    );
                    return None;
                }
                if witness_hash[0] != 0 {
                    test_debug!("Not a p2wpkh-over-p2sh script: not a version-0 witness program");
                    return None;
                }
                if witness_hash[1] != 20 {
                    test_debug!("Not a p2wpkh-over-p2sh script: not a 20-byte pushdata");
                    return None;
                }

                BitcoinTxInput::from_bitcoin_witness_pubkey_vecs(1, &witness[1..], input_txid)
            }
            _ => {
                test_debug!(
                    "Not a p2wpkh-over-p2sh script: scriptsig is not a witness program hash"
                );
                None
            }
        }
    }

    /// parse a p2wsh-over-p2sh multisig redeem script
    fn from_bitcoin_p2wsh_p2sh_multisig_script_sig(
        instructions: &Vec<Instruction>,
        witness: &Vec<Vec<u8>>,
        input_txid: (Txid, u32),
    ) -> Option<BitcoinTxInput> {
        // redeem script format: OP_PUSHDATA <32-byte witness hash>
        // witness format: OP_m <pubkey1> <pubkey2> ... <pubkey_n> OP_n OP_CHECKMULTISIG
        if instructions.len() != 1 {
            test_debug!("Not a p2wsh-over-p2sh script: invalid scriptsig");
            return None;
        }
        if witness.len() < 4 {
            test_debug!("Not a p2wsh-over-p2sh script: invalid witness");
            return None;
        }

        match &instructions[0] {
            Instruction::PushBytes(witness_hash) => {
                // is this a viable witness hash?
                // 00 32 <hash>
                if witness_hash.len() != 34 {
                    test_debug!(
                        "Not a p2wsh-over-p2sh script: invalid witness program hash length"
                    );
                    return None;
                }
                if witness_hash[0] != 0 {
                    test_debug!("Not a p2wsh-over-p2sh script: not a version-0 witness program");
                    return None;
                }
                if witness_hash[1] != 32 {
                    test_debug!("Not a p2wsh-over-p2sh script: not a 32-byte pushdata");
                    return None;
                }

                // witness program should be OP_0 <sig1> <sig2> ... <sig_n> MULTISIG_REDEEM_SCRIPT
                let num_expected_sigs = witness.len() - 2;
                let redeem_script = &witness[witness.len() - 1];

                let tx_input_opt = BitcoinTxInput::from_bitcoin_multisig_redeem_script(
                    &Instruction::PushBytes(&redeem_script[..]),
                    true,
                    input_txid,
                );
                if tx_input_opt.is_none() {
                    return None;
                }

                let tx_input = tx_input_opt.unwrap();

                // number of signatures must match number of required signatures (excluding OP_0 and PUSHDATA(redeem script))
                if num_expected_sigs != tx_input.num_required {
                    test_debug!(
                        "Not a witness multisig script: {} signatures, {} required",
                        num_expected_sigs,
                        tx_input.num_required
                    );
                    return None;
                }

                Some(tx_input)
            }
            _ => {
                test_debug!("Not a p2wsh multisig script: invalid witness hash script sig");
                None
            }
        }
    }

    /// parse a script-sig as either p2pkh scriptsig or p2sh multisig scriptsig
    /// does NOT work with segwit
    fn from_bitcoin_script_sig(
        script_sig: &Script,
        input_txid: (Txid, u32),
    ) -> Option<BitcoinTxInput> {
        let instructions = parse_script(script_sig);
        BitcoinTxInput::from_bitcoin_p2pkh_script_sig(&instructions, input_txid.clone()).or_else(
            || BitcoinTxInput::from_bitcoin_p2sh_multisig_script_sig(&instructions, input_txid),
        )
    }

    /// Parse a script-sig and a witness as either a p2wpkh-over-p2sh or p2wsh-over-p2sh multisig
    /// script.
    pub fn from_bitcoin_witness_script_sig(
        script_sig: &Script,
        witness: &Vec<Vec<u8>>,
        input_txid: (Txid, u32),
    ) -> Option<BitcoinTxInput> {
        let instructions = parse_script(script_sig);
        BitcoinTxInput::from_bitcoin_p2wpkh_p2sh_script_sig(
            &instructions,
            witness,
            input_txid.clone(),
        )
        .or_else(|| {
            BitcoinTxInput::from_bitcoin_p2wsh_p2sh_multisig_script_sig(
                &instructions,
                witness,
                input_txid,
            )
        })
    }

    /// parse a Bitcoin transaction input into a BitcoinTxInput
    pub fn from_bitcoin_txin(txin: &BtcTxIn) -> Option<BitcoinTxInput> {
        let input_txid = to_txid(txin);
        match txin.witness.len() {
            0 => {
                // not a segwit transaction
                BitcoinTxInput::from_bitcoin_script_sig(&txin.script_sig, input_txid)
            }
            _ => {
                // possibly a segwit p2wpkh-over-p2sh or multisig p2wsh-over-p2sh transaction
                BitcoinTxInput::from_bitcoin_witness_script_sig(
                    &txin.script_sig,
                    &txin.witness,
                    input_txid,
                )
            }
        }
    }
}

fn to_txid(txin: &BtcTxIn) -> (Txid, u32) {
    // bitcoin-rs library (which deps::bitcoin is based on)
    //   operates in a different endian-ness for txids than the rest of
    //   the codebase. so this method reverses the txid bits.
    let mut bits = txin.previous_output.txid.0.clone();
    bits.reverse();
    (Txid(bits), txin.previous_output.vout)
}

impl BitcoinTxOutput {
    /// Parse a BitcoinTxOutput from a Bitcoin scriptpubkey and its value in satoshis
    fn from_bitcoin_script_pubkey(
        network_id: BitcoinNetworkType,
        script_pubkey: &Script,
        amount: u64,
    ) -> Option<BitcoinTxOutput> {
        let script_bytes = script_pubkey.to_bytes();
        let address = if script_pubkey.is_p2pkh() {
            BitcoinAddress::from_bytes(
                network_id,
                BitcoinAddressType::PublicKeyHash,
                &script_bytes[3..23].to_vec(),
            )
        } else if script_pubkey.is_p2sh() {
            BitcoinAddress::from_bytes(
                network_id,
                BitcoinAddressType::ScriptHash,
                &script_bytes[2..22].to_vec(),
            )
        } else {
            Err(btc_error::InvalidByteSequence)
        };

        match address {
            Ok(addr) => Some(BitcoinTxOutput {
                address: addr,
                units: amount,
            }),
            Err(_e) => None,
        }
    }

    /// Parse a burnchain tx output from a bitcoin output
    pub fn from_bitcoin_txout(
        network_id: BitcoinNetworkType,
        txout: &BtcTxOut,
    ) -> Option<BitcoinTxOutput> {
        BitcoinTxOutput::from_bitcoin_script_pubkey(network_id, &txout.script_pubkey, txout.value)
    }
}

impl BurnchainHeaderHash {
    /// Instantiate a burnchain block hash from a Bitcoin block header
    pub fn from_bitcoin_hash(bitcoin_hash: &Sha256dHash) -> BurnchainHeaderHash {
        // NOTE: Sha256dhash is the same size as BurnchainHeaderHash, so this should never panic
        // Bitcoin stores its hashes in big-endian form, but our codebase stores them in
        // little-endian form (which is also how most libraries work).
        BurnchainHeaderHash::from_bytes_be(bitcoin_hash.as_bytes()).unwrap()
    }

    pub fn to_bitcoin_hash(&self) -> Sha256dHash {
        let mut bytes = self.0.to_vec();
        bytes.reverse();
        let mut buf = [0u8; 32];
        buf.copy_from_slice(&bytes[0..32]);
        Sha256dHash(buf)
    }

    pub fn zero() -> BurnchainHeaderHash {
        BurnchainHeaderHash([0x00; 32])
    }
}

#[cfg(test)]
mod tests {
    use burnchains::bitcoin::address::{BitcoinAddress, BitcoinAddressType};
    use burnchains::bitcoin::keys::BitcoinPublicKey;
    use burnchains::bitcoin::BitcoinInputType;
    use burnchains::bitcoin::BitcoinNetworkType;
    use burnchains::Txid;
    use deps::bitcoin::blockdata::script::{Builder, Script};
    use util::hash::hex_bytes;
    use util::log;

    use super::parse_script;
    use super::BitcoinTxInput;
    use super::BitcoinTxOutput;

    struct ScriptFixture<T> {
        script: Script,
        result: T,
    }

    struct ScriptWitnessFixture<T> {
        script: Script,
        witness: Vec<Vec<u8>>,
        result: T,
    }

    #[test]
    fn tx_input_singlesig() {
        let tx_input_singlesig_fixtures = vec![
            ScriptFixture {
                // one compressed key
                script: Builder::from(hex_bytes("483045022100f24ac462a80b285584f93bf930e8c548fa63edcb0d790d480202a1e305c1657e02203c7bb3e396c00d3ec7f6a80946449dc6b855a9e7140adf183c26724e59af922a0121032cb957290adc734c56dbc29b63f94f1c493cd895aaa628766861b3d195dd1043").unwrap()).into_script(),
                result: BitcoinTxInput {
                    num_required: 1,
                    keys: vec![
                        BitcoinPublicKey::from_hex("032cb957290adc734c56dbc29b63f94f1c493cd895aaa628766861b3d195dd1043").unwrap()
                    ],
                    in_type: BitcoinInputType::Standard,
                    tx_ref: (Txid([0; 32]), 0),
                }
            },
            ScriptFixture {
                // one uncompressed key
                script: Builder::from(hex_bytes("483045022100be57031bf2c095945ba2876e97b3f86ee051643a29b908f22ed45ccf58620103022061e056e5f48c5a51c66604a1ca28e4bfaabab1478424c9bbb396cc6afe5c222e0141040fadbbcea0ff3b05f03195b41cd991d7a0af8bd38559943aec99cbdaf0b22cc806b9a4f07579934774cc0c155e781d45c989f94336765e88a66d91cfb9f060b0").unwrap()).into_script(),
                result: BitcoinTxInput {
                    num_required: 1,
                    keys: vec![
                        BitcoinPublicKey::from_hex("040fadbbcea0ff3b05f03195b41cd991d7a0af8bd38559943aec99cbdaf0b22cc806b9a4f07579934774cc0c155e781d45c989f94336765e88a66d91cfb9f060b0").unwrap()
                    ],
                    in_type: BitcoinInputType::Standard,
                    tx_ref: (Txid([0; 32]), 0),
                }
            }
        ];

        for script_fixture in tx_input_singlesig_fixtures {
            let tx_input_opt =
                BitcoinTxInput::from_bitcoin_script_sig(&script_fixture.script, (Txid([0; 32]), 0));
            assert!(tx_input_opt.is_some());
            assert_eq!(tx_input_opt.unwrap(), script_fixture.result);

            let tx_input_singlesig_opt = BitcoinTxInput::from_bitcoin_p2pkh_script_sig(
                &parse_script(&script_fixture.script),
                (Txid([0; 32]), 0),
            );
            assert!(tx_input_singlesig_opt.is_some());
            assert_eq!(tx_input_singlesig_opt.unwrap(), script_fixture.result);

            let tx_input_multisig_opt = BitcoinTxInput::from_bitcoin_p2sh_multisig_script_sig(
                &parse_script(&script_fixture.script),
                (Txid([0; 32]), 0),
            );
            assert!(tx_input_multisig_opt.is_none());

            let txin_str = serde_json::to_string(&script_fixture.result).unwrap();
            let txin: BitcoinTxInput = serde_json::from_str(&txin_str).unwrap();
            assert_eq!(txin, script_fixture.result);
        }
    }

    #[test]
    fn tx_input_multisig() {
        let tx_input_multisig_fixtures = vec![
            ScriptFixture {
                // 2-of-3 multisig, uncompressed keys 
                script: Builder::from(hex_bytes("00483045022100acb79a21e7e6cea47a598254e02639f87b5fa9a08c0ec8455503da0a479c19560220724014c241ac64ffc108d4457302644d5d057fbc4f2edbf33a86f24cf0b10447014730440220338862b4a13d67415fdaac35d408bd2a6d86e4c3be03b7abc92ee769b254dbe1022043ba94f304aff774fdb957af078c9b302425976370cc66f42ae05382c84ea5ea014cc9524104a97b658c114d77dc5f71736ab78fbe408ce632ed1478d7eaa106eef67c55d58a91c6449de4858faf11721e85fe09ec850c6578432eb4be9a69c76232ac593c3b4104019ef04a316792f0ecbe5ab1718c833c3964dee3626cfabe19d97745dbcaa5198919081b456e8eeea5898afa0e36d5c17ab693a80d728721128ed8c5f38cdba04104a04f29f308160e6f945b33d943304b1b471ed8f9eaceeb5412c04e60a0fab0376871d9d1108948b67cafbc703e565a18f8351fb8558fd7c7482d7027eecd687c53ae").unwrap()).into_script(),
                result: BitcoinTxInput {
                    num_required: 2,
                    keys: vec![
                        BitcoinPublicKey::from_hex("04a97b658c114d77dc5f71736ab78fbe408ce632ed1478d7eaa106eef67c55d58a91c6449de4858faf11721e85fe09ec850c6578432eb4be9a69c76232ac593c3b").unwrap(),
                        BitcoinPublicKey::from_hex("04019ef04a316792f0ecbe5ab1718c833c3964dee3626cfabe19d97745dbcaa5198919081b456e8eeea5898afa0e36d5c17ab693a80d728721128ed8c5f38cdba0").unwrap(),
                        BitcoinPublicKey::from_hex("04a04f29f308160e6f945b33d943304b1b471ed8f9eaceeb5412c04e60a0fab0376871d9d1108948b67cafbc703e565a18f8351fb8558fd7c7482d7027eecd687c").unwrap()
                    ],
                    in_type: BitcoinInputType::Standard,
                    tx_ref: (Txid([0; 32]), 0),
                }
            },
            ScriptFixture {
                // 15-of-15 multisig, compressed keys
                script: Builder::from(hex_bytes("00483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a1960542136850014d01025f210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c715fae").unwrap()).into_script(),
                result: BitcoinTxInput {
                    num_required: 15,
                    keys: vec![
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap(),
                        BitcoinPublicKey::from_hex("0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71").unwrap()
                    ],
                    in_type: BitcoinInputType::Standard,
                    tx_ref: (Txid([0; 32]), 0),
                }
            },
            ScriptFixture {
                // 2-of-3 multisig, compressed keys 
                script: Builder::from(hex_bytes("004830450221008d5ec57d362ff6ef6602e4e756ef1bdeee12bd5c5c72697ef1455b379c90531002202ef3ea04dfbeda043395e5bc701e4878c15baab9c6ba5808eb3d04c91f641a0c0147304402200bd8c62b938e02094021e481b149fd5e366a212cb823187149799a68cfa7652002203b52120c5cf25ceab5f0a6b5cdb8eca0fd2f386316c9721177b75ddca82a4ae8014c69522103310188e911026cf18c3ce274e0ebb5f95b007f230d8cb7d09879d96dbeab1aff210243930746e6ed6552e03359db521b088134652905bd2d1541fa9124303a41e95621029e03a901b85534ff1e92c43c74431f7ce72046060fcf7a95c37e148f78c7725553ae").unwrap()).into_script(),
                result: BitcoinTxInput {
                    num_required: 2,
                    keys: vec![
                        BitcoinPublicKey::from_hex("03310188e911026cf18c3ce274e0ebb5f95b007f230d8cb7d09879d96dbeab1aff").unwrap(),
                        BitcoinPublicKey::from_hex("0243930746e6ed6552e03359db521b088134652905bd2d1541fa9124303a41e956").unwrap(),
                        BitcoinPublicKey::from_hex("029e03a901b85534ff1e92c43c74431f7ce72046060fcf7a95c37e148f78c77255").unwrap()
                    ],
                    in_type: BitcoinInputType::Standard,
                    tx_ref: (Txid([0; 32]), 0),
                }
            }
        ];

        for script_fixture in tx_input_multisig_fixtures {
            let tx_input_opt =
                BitcoinTxInput::from_bitcoin_script_sig(&script_fixture.script, (Txid([0; 32]), 0));
            assert!(tx_input_opt.is_some());
            assert_eq!(tx_input_opt.unwrap(), script_fixture.result);

            let tx_input_singlesig_opt = BitcoinTxInput::from_bitcoin_p2sh_multisig_script_sig(
                &parse_script(&script_fixture.script),
                (Txid([0; 32]), 0),
            );
            assert!(tx_input_singlesig_opt.is_some());
            assert_eq!(tx_input_singlesig_opt.unwrap(), script_fixture.result);

            let tx_input_multisig_opt = BitcoinTxInput::from_bitcoin_p2pkh_script_sig(
                &parse_script(&script_fixture.script),
                (Txid([0; 32]), 0),
            );
            assert!(tx_input_multisig_opt.is_none());

            let txin_str = serde_json::to_string(&script_fixture.result).unwrap();
            let txin: BitcoinTxInput = serde_json::from_str(&txin_str).unwrap();
            assert_eq!(txin, script_fixture.result);
        }
    }

    #[test]
    fn tx_input_segwit_p2wpkh_p2sh() {
        // should extract keys from segwit p2wpkh-over-p2sh witness script
        let tx_fixtures_p2wpkh_p2sh = vec![
            ScriptWitnessFixture {
                // p2wpkh-over-p2sh
                script: Builder::from(hex_bytes("160014393ffec4f09b38895b8502377693f23c6ae00f19").unwrap()).into_script(),
                witness: vec![
                    hex_bytes("304402204686573485d6a7cc7e40d9a95f5e87eafbf4eabfc38863498fd022b18a4da4fc0220036d715f2bc7b16b3a264500d1944ca3cad3c3e9d87a01cf917ecf06e436952401").unwrap(),
                    hex_bytes("02d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e81").unwrap()
                ],
                result: Some(BitcoinTxInput {
                    num_required: 1,
                    keys: vec![
                        BitcoinPublicKey::from_hex("02d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e81").unwrap()
                    ],
                    in_type: BitcoinInputType::SegwitP2SH,
                    tx_ref: (Txid([0; 32]), 0),
                })
            },
            ScriptWitnessFixture {
                // invalid p2wpkh-over-p2sh
                script: Builder::from(hex_bytes("160114393ffec4f09b38895b8502377693f23c6ae00f19").unwrap()).into_script(),      // wrong version
                witness: vec![
                    hex_bytes("304402204686573485d6a7cc7e40d9a95f5e87eafbf4eabfc38863498fd022b18a4da4fc0220036d715f2bc7b16b3a264500d1944ca3cad3c3e9d87a01cf917ecf06e436952401").unwrap(),
                    hex_bytes("02d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e81").unwrap()
                ],
                result: None
            },
            ScriptWitnessFixture {
                // invalid p2wpkh-over-p2sh
                script: Builder::from(hex_bytes("160014393ffec4f09b38895b8502377693f23c6ae00f19").unwrap()).into_script(),
                witness: vec![                          // too many entries
                    hex_bytes("304402204686573485d6a7cc7e40d9a95f5e87eafbf4eabfc38863498fd022b18a4da4fc0220036d715f2bc7b16b3a264500d1944ca3cad3c3e9d87a01cf917ecf06e436952401").unwrap(),
                    hex_bytes("304402204686573485d6a7cc7e40d9a95f5e87eafbf4eabfc38863498fd022b18a4da4fc0220036d715f2bc7b16b3a264500d1944ca3cad3c3e9d87a01cf917ecf06e436952401").unwrap(),
                    hex_bytes("02d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e81").unwrap()
                ],
                result: None
            },
            ScriptWitnessFixture {
                // invalid p2wpkh-over-p2sh
                script: Builder::from(hex_bytes("160014393ffec4f09b38895b8502377693f23c6ae00f19").unwrap()).into_script(),
                witness: vec![
                    // last witness entry isn't a public key
                    hex_bytes("02d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e81").unwrap(),
                    hex_bytes("304402204686573485d6a7cc7e40d9a95f5e87eafbf4eabfc38863498fd022b18a4da4fc0220036d715f2bc7b16b3a264500d1944ca3cad3c3e9d87a01cf917ecf06e436952401").unwrap(),
                ],
                result: None
            }
        ];

        for fixture in tx_fixtures_p2wpkh_p2sh {
            let tx_opt = BitcoinTxInput::from_bitcoin_witness_script_sig(
                &fixture.script,
                &fixture.witness,
                (Txid([0; 32]), 0),
            );
            match (tx_opt, fixture.result) {
                (Some(tx_input), Some(fixture_input)) => {
                    assert_eq!(tx_input, fixture_input);

                    let txin_str = serde_json::to_string(&fixture_input).unwrap();
                    let txin: BitcoinTxInput = serde_json::from_str(&txin_str).unwrap();
                    assert_eq!(txin, fixture_input);
                }
                (None, None) => {}
                (Some(_t), None) => {
                    test_debug!("Decoded a p2wpkh-over-p2sh when we should not have done so");
                    assert!(false);
                }
                (None, Some(_f)) => {
                    test_debug!("Failed to decode p2wpkh-over-p2sh when we should have done so");
                    assert!(false);
                }
            }
        }
    }

    #[test]
    fn tx_input_segwit_p2wsh_multisig_p2sh() {
        // should extract keys from segwit p2wsh-multisig-over-p2sh witness script
        let tx_fixtures_p2wpkh_p2sh = vec![
            ScriptWitnessFixture {
                // p2wsh-multisig-over-p2sh
                script: Builder::from(hex_bytes("22002067091a41e9871c5ae20b0c69a786f02df5d3c7aa632689b608069181b43a28a2").unwrap()).into_script(),
                witness: vec![
                    hex_bytes("").unwrap(),
                    hex_bytes("3044022064c5b5f61baad8bb8ecad98666b99e09f1777ef805df41a1c7926f8468b6b6df02205eac177c77f274acb670cd24d504f01b27de767e0241c818c91e479cb0ddcf1801").unwrap(),
                    hex_bytes("30440220053ce777bc7bb842d8eef83769a027797567624ab9eed5722889ed3192f431b30220256e8aaef8de2a571198acde708fcbca02fb18780ac470c0d7f811734af729af01").unwrap(),
                    hex_bytes("522102d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e812102f21b29694df4c2188bee97103d10d017d1865fb40528f25589af9db6e0786b6521028791dc45c049107fb99e673265a38a096536aacdf78aa90710a32fff7750f9f953ae").unwrap()
                ],
                result: Some(BitcoinTxInput {
                    num_required: 2,
                    keys: vec![
                        BitcoinPublicKey::from_hex("02d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e81").unwrap(),
                        BitcoinPublicKey::from_hex("02f21b29694df4c2188bee97103d10d017d1865fb40528f25589af9db6e0786b65").unwrap(),
                        BitcoinPublicKey::from_hex("028791dc45c049107fb99e673265a38a096536aacdf78aa90710a32fff7750f9f9").unwrap()
                    ],
                    in_type: BitcoinInputType::SegwitP2SH,
                    tx_ref: (Txid([0; 32]), 0),
                })
            },
            ScriptWitnessFixture {
                // invalid p2wsh-multisig-over-p2sh: bad witness hash len
                script: Builder::from(hex_bytes("23002067091a41e9871c5ae20b0c69a786f02df5d3c7aa632689b608069181b43a28a200").unwrap()).into_script(),
                witness: vec![
                    hex_bytes("").unwrap(),
                    hex_bytes("3044022064c5b5f61baad8bb8ecad98666b99e09f1777ef805df41a1c7926f8468b6b6df02205eac177c77f274acb670cd24d504f01b27de767e0241c818c91e479cb0ddcf1801").unwrap(),
                    hex_bytes("30440220053ce777bc7bb842d8eef83769a027797567624ab9eed5722889ed3192f431b30220256e8aaef8de2a571198acde708fcbca02fb18780ac470c0d7f811734af729af01").unwrap(),
                    hex_bytes("522102d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e812102f21b29694df4c2188bee97103d10d017d1865fb40528f25589af9db6e0786b6521028791dc45c049107fb99e673265a38a096536aacdf78aa90710a32fff7750f9f953ae").unwrap()
                ],
                result: None
            },
            ScriptWitnessFixture {
                // invalid p2wsh-multisig-over-p2sh: bad witness hash version
                script: Builder::from(hex_bytes("22012067091a41e9871c5ae20b0c69a786f02df5d3c7aa632689b608069181b43a28a2").unwrap()).into_script(),
                witness: vec![
                    hex_bytes("").unwrap(),
                    hex_bytes("3044022064c5b5f61baad8bb8ecad98666b99e09f1777ef805df41a1c7926f8468b6b6df02205eac177c77f274acb670cd24d504f01b27de767e0241c818c91e479cb0ddcf1801").unwrap(),
                    hex_bytes("30440220053ce777bc7bb842d8eef83769a027797567624ab9eed5722889ed3192f431b30220256e8aaef8de2a571198acde708fcbca02fb18780ac470c0d7f811734af729af01").unwrap(),
                    hex_bytes("522102d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e812102f21b29694df4c2188bee97103d10d017d1865fb40528f25589af9db6e0786b6521028791dc45c049107fb99e673265a38a096536aacdf78aa90710a32fff7750f9f953ae").unwrap()
                ],
                result: None
            },
            ScriptWitnessFixture {
                // invalid p2wsh-multisig-over-p2sh: wrong number of signatures
                script: Builder::from(hex_bytes("22002067091a41e9871c5ae20b0c69a786f02df5d3c7aa632689b608069181b43a28a2").unwrap()).into_script(),
                witness: vec![
                    hex_bytes("").unwrap(),
                    hex_bytes("3044022064c5b5f61baad8bb8ecad98666b99e09f1777ef805df41a1c7926f8468b6b6df02205eac177c77f274acb670cd24d504f01b27de767e0241c818c91e479cb0ddcf1801").unwrap(),
                    hex_bytes("3044022064c5b5f61baad8bb8ecad98666b99e09f1777ef805df41a1c7926f8468b6b6df02205eac177c77f274acb670cd24d504f01b27de767e0241c818c91e479cb0ddcf1801").unwrap(),
                    hex_bytes("30440220053ce777bc7bb842d8eef83769a027797567624ab9eed5722889ed3192f431b30220256e8aaef8de2a571198acde708fcbca02fb18780ac470c0d7f811734af729af01").unwrap(),
                    hex_bytes("522102d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e812102f21b29694df4c2188bee97103d10d017d1865fb40528f25589af9db6e0786b6521028791dc45c049107fb99e673265a38a096536aacdf78aa90710a32fff7750f9f953ae").unwrap()
                ],
                result: None
            },
            ScriptWitnessFixture {
                // invalid p2wsh-multisig-over-p2sh: not a valid multisig script
                script: Builder::from(hex_bytes("22002067091a41e9871c5ae20b0c69a786f02df5d3c7aa632689b608069181b43a28a2").unwrap()).into_script(),
                witness: vec![
                    hex_bytes("").unwrap(),
                    hex_bytes("3044022064c5b5f61baad8bb8ecad98666b99e09f1777ef805df41a1c7926f8468b6b6df02205eac177c77f274acb670cd24d504f01b27de767e0241c818c91e479cb0ddcf1801").unwrap(),
                    hex_bytes("522102d341f728783eb93e6fb5921a1ebe9d149e941de31e403cd69afa2f0f1e698e812102f21b29694df4c2188bee97103d10d017d1865fb40528f25589af9db6e0786b6521028791dc45c049107fb99e673265a38a096536aacdf78aa90710a32fff7750f9f953ae").unwrap(),
                    hex_bytes("30440220053ce777bc7bb842d8eef83769a027797567624ab9eed5722889ed3192f431b30220256e8aaef8de2a571198acde708fcbca02fb18780ac470c0d7f811734af729af01").unwrap(),
                ],
                result: None,
            },
            ScriptWitnessFixture {
                // invalid p2wsh-multisig-over-p2sh: incompatible (but well-formed!) multisig script
                script: Builder::from(hex_bytes("22002067091a41e9871c5ae20b0c69a786f02df5d3c7aa632689b608069181b43a28a2").unwrap()).into_script(),
                witness: vec![
                    hex_bytes("").unwrap(),
                    hex_bytes("3044022064c5b5f61baad8bb8ecad98666b99e09f1777ef805df41a1c7926f8468b6b6df02205eac177c77f274acb670cd24d504f01b27de767e0241c818c91e479cb0ddcf1801").unwrap(),
                    hex_bytes("30440220053ce777bc7bb842d8eef83769a027797567624ab9eed5722889ed3192f431b30220256e8aaef8de2a571198acde708fcbca02fb18780ac470c0d7f811734af729af01").unwrap(),
                    hex_bytes("00483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a196054213685001483045022100db90a0a5841d3cc6e7e981b6317013fa2787674ae9be88f1c9ec762627d419c3022028cf94eac4641629c1a0d3f9519e9cc2d5e48e221f48c882c3a1960542136850014d01025f210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c715fae").unwrap()
                ],
                result: None
            }
        ];

        for fixture in tx_fixtures_p2wpkh_p2sh {
            let tx_opt = BitcoinTxInput::from_bitcoin_witness_script_sig(
                &fixture.script,
                &fixture.witness,
                (Txid([0; 32]), 0),
            );
            match (tx_opt, fixture.result) {
                (Some(tx_input), Some(fixture_input)) => {
                    assert_eq!(tx_input, fixture_input);

                    let txin_str = serde_json::to_string(&fixture_input).unwrap();
                    let txin: BitcoinTxInput = serde_json::from_str(&txin_str).unwrap();
                    assert_eq!(txin, fixture_input);
                }
                (None, None) => {}
                (Some(_t), None) => {
                    test_debug!("Decoded a p2wsh-over-p2sh when we should not have done so");
                    assert!(false);
                }
                (None, Some(_f)) => {
                    test_debug!("Failed to decode p2wsh-over-p2sh when we should have done so");
                    assert!(false);
                }
            }
        }
    }

    #[test]
    fn tx_input_strange() {
        // none of these should parse
        let tx_fixtures_strange_scriptsig : Vec<ScriptFixture<Option<BitcoinTxInput>>> = vec![
            ScriptFixture {
                // 0-of-0 multisig
                // taken from 970b435253b69cde8207b3245d7723bb24861fd7ab3cfe361f45ae8de085ac52
                script: Builder::from(hex_bytes("00000001ae").unwrap()).into_script(),
                result: None
            },
            ScriptFixture {
                // segwit p2sh p2wsh redeem script by itself
                script: Builder::from(hex_bytes("2200200db5e96eaf886fab2f1a20f00528f293e9fc9fb202d2c68c2f57a41eba47b5bf").unwrap()).into_script(),
                result: None
            },
            ScriptFixture {
                // segwit p2sh p2wpkh redeem script by itself
                script: Builder::from(hex_bytes("160014751e76e8199196d454941c45d1b3a323f1433bd6").unwrap()).into_script(),
                result: None
            },
            ScriptFixture {
                // nonsensical 4-of-3 multisig, wth 2 signatures
                script: Builder::from(hex_bytes("004730440220338862b4a13d67415fdaac35d408bd2a6d86e4c3be03b7abc92ee769b254dbe1022043ba94f304aff774fdb957af078c9b302425976370cc66f42ae05382c84ea5ea014730440220338862b4a13d67415fdaac35d408bd2a6d86e4c3be03b7abc92ee769b254dbe1022043ba94f304aff774fdb957af078c9b302425976370cc66f42ae05382c84ea5ea014c69542103310188e911026cf18c3ce274e0ebb5f95b007f230d8cb7d09879d96dbeab1aff210243930746e6ed6552e03359db521b088134652905bd2d1541fa9124303a41e95621029e03a901b85534ff1e92c43c74431f7ce72046060fcf7a95c37e148f78c7725553ae").unwrap()).into_script(),
                result: None
            },
            ScriptFixture {
                // nonsensical 4-of-3 multisig, with 3 signatures 
                script: Builder::from(hex_bytes("004730440220338862b4a13d67415fdaac35d408bd2a6d86e4c3be03b7abc92ee769b254dbe1022043ba94f304aff774fdb957af078c9b302425976370cc66f42ae05382c84ea5ea014730440220338862b4a13d67415fdaac35d408bd2a6d86e4c3be03b7abc92ee769b254dbe1022043ba94f304aff774fdb957af078c9b302425976370cc66f42ae05382c84ea5ea01483045022100be57031bf2c095945ba2876e97b3f86ee051643a29b908f22ed45ccf58620103022061e056e5f48c5a51c66604a1ca28e4bfaabab1478424c9bbb396cc6afe5c222e014c69542103310188e911026cf18c3ce274e0ebb5f95b007f230d8cb7d09879d96dbeab1aff210243930746e6ed6552e03359db521b088134652905bd2d1541fa9124303a41e95621029e03a901b85534ff1e92c43c74431f7ce72046060fcf7a95c37e148f78c7725553ae").unwrap()).into_script(),
                result: None,
            },
            ScriptFixture {
                // nonsensical 4-of-3 multisig, with 4 signatures 
                script: Builder::from(hex_bytes("004730440220338862b4a13d67415fdaac35d408bd2a6d86e4c3be03b7abc92ee769b254dbe1022043ba94f304aff774fdb957af078c9b302425976370cc66f42ae05382c84ea5ea014730440220338862b4a13d67415fdaac35d408bd2a6d86e4c3be03b7abc92ee769b254dbe1022043ba94f304aff774fdb957af078c9b302425976370cc66f42ae05382c84ea5ea01483045022100be57031bf2c095945ba2876e97b3f86ee051643a29b908f22ed45ccf58620103022061e056e5f48c5a51c66604a1ca28e4bfaabab1478424c9bbb396cc6afe5c222e01483045022100fd9c04b330810694cb4bfef793b193f9cbfaa07325700f217b9cb03e5207005302202f07e7c9c6774c5619a043752444f6da6fd81b9d9d008ec965796d87271598de014c69542103310188e911026cf18c3ce274e0ebb5f95b007f230d8cb7d09879d96dbeab1aff210243930746e6ed6552e03359db521b088134652905bd2d1541fa9124303a41e95621029e03a901b85534ff1e92c43c74431f7ce72046060fcf7a95c37e148f78c7725553ae").unwrap()).into_script(),
                result: None
            },
            ScriptFixture {
                // pushdata 64-byte 0's
                script: Builder::from(hex_bytes("4e404000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000").unwrap()).into_script(),
                result: None
            },
            ScriptFixture {
                // scriptsig from mainnet transaction 09f691b2263260e71f363d1db51ff3100d285956a40cc0e4f8c8c2c4a80559b1
                script: Builder::from(hex_bytes("4c500100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c").unwrap()).into_script(),
                result: None
            },
            ScriptFixture {
                // scriptsig from mainnet transaction 8d31992805518fd62daa3bdd2a5c4fd2cd3054c9b3dca1d78055e9528cff6adc
                script: Builder::from(hex_bytes("4d4001255044462d312e330a25e2e3cfd30a0a0a312030206f626a0a3c3c2f57696474682032203020522f4865696768742033203020522f547970652034203020522f537562747970652035203020522f46696c7465722036203020522f436f6c6f7253706163652037203020522f4c656e6774682038203020522f42697473506572436f6d706f6e656e7420383e3e0a73747265616d0affd8fffe00245348412d3120697320646561642121212121852fec092339759c39b1a1c63c4c97e1fffe017f46dc93a6b67e013b029aaa1db2560b45ca67d688c7f84b8c4c791fe02b3df614f86db1690901c56b45c1530afedfb76038e972722fe7ad728f0e4904e046c230570fe9d41398abe12ef5bc942be33542a4802d98b5d70f2a332ec37fac3514e74ddc0f2cc1a874cd0c78305a21566461309789606bd0bf3f98cda8044629a14d4001255044462d312e330a25e2e3cfd30a0a0a312030206f626a0a3c3c2f57696474682032203020522f4865696768742033203020522f547970652034203020522f537562747970652035203020522f46696c7465722036203020522f436f6c6f7253706163652037203020522f4c656e6774682038203020522f42697473506572436f6d706f6e656e7420383e3e0a73747265616d0affd8fffe00245348412d3120697320646561642121212121852fec092339759c39b1a1c63c4c97e1fffe017346dc9166b67e118f029ab621b2560ff9ca67cca8c7f85ba84c79030c2b3de218f86db3a90901d5df45c14f26fedfb3dc38e96ac22fe7bd728f0e45bce046d23c570feb141398bb552ef5a0a82be331fea48037b8b5d71f0e332edf93ac3500eb4ddc0decc1a864790c782c76215660dd309791d06bd0af3f98cda4bc4629b1086e879169a77ca787").unwrap()).into_script(),
                result: None
            }
        ];

        for script_fixture in tx_fixtures_strange_scriptsig {
            let tx_input_opt =
                BitcoinTxInput::from_bitcoin_script_sig(&script_fixture.script, (Txid([0; 32]), 0));
            assert!(tx_input_opt.is_none());
        }
    }

    #[test]
    fn tx_output_p2pkh() {
        let amount = 123;
        let tx_fixtures_p2pkh = vec![
            ScriptFixture {
                script: Builder::from(
                    hex_bytes("76a914395f3643cea07ec4eec73b4d9a973dcce56b9bf188ac").unwrap(),
                )
                .into_script(),
                result: BitcoinTxOutput {
                    units: amount,
                    address: BitcoinAddress::from_bytes(
                        BitcoinNetworkType::Mainnet,
                        BitcoinAddressType::PublicKeyHash,
                        &hex_bytes("395f3643cea07ec4eec73b4d9a973dcce56b9bf1").unwrap(),
                    )
                    .unwrap(),
                },
            },
            ScriptFixture {
                script: Builder::from(
                    hex_bytes("76a914000000000000000000000000000000000000000088ac").unwrap(),
                )
                .into_script(),
                result: BitcoinTxOutput {
                    units: amount,
                    address: BitcoinAddress::from_bytes(
                        BitcoinNetworkType::Mainnet,
                        BitcoinAddressType::PublicKeyHash,
                        &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
                    )
                    .unwrap(),
                },
            },
        ];

        for script_fixture in tx_fixtures_p2pkh {
            let tx_output_opt = BitcoinTxOutput::from_bitcoin_script_pubkey(
                BitcoinNetworkType::Mainnet,
                &script_fixture.script,
                amount,
            );
            assert!(tx_output_opt.is_some());
            assert_eq!(tx_output_opt.unwrap(), script_fixture.result);
        }
    }

    #[test]
    fn tx_output_p2sh() {
        let amount = 123;
        let tx_fixtures_p2sh = vec![
            ScriptFixture {
                script: Builder::from(
                    hex_bytes("a914eb1881fb0682c2eb37e478bf918525a2c61bc40487").unwrap(),
                )
                .into_script(),
                result: BitcoinTxOutput {
                    units: amount,
                    address: BitcoinAddress::from_bytes(
                        BitcoinNetworkType::Mainnet,
                        BitcoinAddressType::ScriptHash,
                        &hex_bytes("eb1881fb0682c2eb37e478bf918525a2c61bc404").unwrap(),
                    )
                    .unwrap(),
                },
            },
            ScriptFixture {
                script: Builder::from(
                    hex_bytes("a914000000000000000000000000000000000000000087").unwrap(),
                )
                .into_script(),
                result: BitcoinTxOutput {
                    units: amount,
                    address: BitcoinAddress::from_bytes(
                        BitcoinNetworkType::Mainnet,
                        BitcoinAddressType::ScriptHash,
                        &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
                    )
                    .unwrap(),
                },
            },
        ];

        for script_fixture in tx_fixtures_p2sh {
            let tx_output_opt = BitcoinTxOutput::from_bitcoin_script_pubkey(
                BitcoinNetworkType::Mainnet,
                &script_fixture.script,
                amount,
            );
            assert!(tx_output_opt.is_some());
            assert_eq!(tx_output_opt.unwrap(), script_fixture.result);
        }
    }

    #[test]
    fn tx_output_strange() {
        let tx_fixtures_strange: Vec<ScriptFixture<Option<BitcoinTxOutput>>> = vec![
            ScriptFixture {
                // script pubkey for segwit p2wpkh
                script: Builder::from(
                    hex_bytes("0014751e76e8199196d454941c45d1b3a323f1433bd6").unwrap(),
                )
                .into_script(),
                result: None,
            },
            ScriptFixture {
                // script pubkey for a segwit p2wsh
                script: Builder::from(
                    hex_bytes(
                        "00201863143c14c5166804bd19203356da136c985678cd4d27a1b8c6329604903262",
                    )
                    .unwrap(),
                )
                .into_script(),
                result: None,
            },
        ];

        for script_fixture in tx_fixtures_strange {
            let tx_output_opt = BitcoinTxOutput::from_bitcoin_script_pubkey(
                BitcoinNetworkType::Mainnet,
                &script_fixture.script,
                123,
            );
            assert!(tx_output_opt.is_none());
        }
    }
}
