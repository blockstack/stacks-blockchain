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

use crate::types::chainstate::StacksAddress;
use crate::{codec::StacksMessageCodec, types::chainstate::StacksMicroblockHeader};
use burnchains::Txid;
use chainstate::stacks::StacksTransaction;
use vm::analysis::ContractAnalysis;
use vm::costs::ExecutionCost;
use vm::types::{
    AssetIdentifier, PrincipalData, QualifiedContractIdentifier, StandardPrincipalData, Value,
};

#[derive(Debug, Clone, PartialEq)]
pub enum TransactionOrigin {
    Stacks(StacksTransaction),
    Burn(Txid),
}

impl From<StacksTransaction> for TransactionOrigin {
    fn from(o: StacksTransaction) -> TransactionOrigin {
        TransactionOrigin::Stacks(o)
    }
}

impl TransactionOrigin {
    pub fn txid(&self) -> Txid {
        match self {
            TransactionOrigin::Burn(txid) => txid.clone(),
            TransactionOrigin::Stacks(tx) => tx.txid(),
        }
    }
    pub fn serialize_to_vec(&self) -> Vec<u8> {
        match self {
            TransactionOrigin::Burn(txid) => txid.as_bytes().to_vec(),
            TransactionOrigin::Stacks(tx) => tx.txid().as_bytes().to_vec(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct StacksTransactionReceipt {
    pub transaction: TransactionOrigin,
    pub events: Vec<StacksTransactionEvent>,
    pub post_condition_aborted: bool,
    pub result: Value,
    pub stx_burned: u128,
    pub contract_analysis: Option<ContractAnalysis>,
    pub execution_cost: ExecutionCost,
    pub microblock_header: Option<StacksMicroblockHeader>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StacksTransactionEvent {
    SmartContractEvent(SmartContractEventData),
    STXEvent(STXEventType),
    NFTEvent(NFTEventType),
    FTEvent(FTEventType),
}

impl StacksTransactionEvent {
    pub fn json_serialize(
        &self,
        event_index: usize,
        txid: &Txid,
        committed: bool,
    ) -> serde_json::Value {
        match self {
            StacksTransactionEvent::SmartContractEvent(event_data) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "contract_event",
                "contract_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::STXEvent(STXEventType::STXTransferEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "stx_transfer_event",
                "stx_transfer_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::STXEvent(STXEventType::STXMintEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "stx_mint_event",
                "stx_mint_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::STXEvent(STXEventType::STXBurnEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "stx_burn_event",
                "stx_burn_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::STXEvent(STXEventType::STXLockEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "stx_lock_event",
                "stx_lock_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::NFTEvent(NFTEventType::NFTTransferEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "nft_transfer_event",
                "nft_transfer_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::NFTEvent(NFTEventType::NFTMintEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "nft_mint_event",
                "nft_mint_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::NFTEvent(NFTEventType::NFTBurnEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "nft_burn_event",
                "nft_burn_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::FTEvent(FTEventType::FTTransferEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "ft_transfer_event",
                "ft_transfer_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::FTEvent(FTEventType::FTMintEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "ft_mint_event",
                "ft_mint_event": event_data.json_serialize()
            }),
            StacksTransactionEvent::FTEvent(FTEventType::FTBurnEvent(event_data)) => json!({
                "txid": format!("0x{:?}", txid),
                "event_index": event_index,
                "committed": committed,
                "type": "ft_burn_event",
                "ft_burn_event": event_data.json_serialize()
            }),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum STXEventType {
    STXTransferEvent(STXTransferEventData),
    STXMintEvent(STXMintEventData),
    STXBurnEvent(STXBurnEventData),
    STXLockEvent(STXLockEventData),
}

#[derive(Debug, Clone, PartialEq)]
pub enum NFTEventType {
    NFTTransferEvent(NFTTransferEventData),
    NFTMintEvent(NFTMintEventData),
    NFTBurnEvent(NFTBurnEventData),
}

#[derive(Debug, Clone, PartialEq)]
pub enum FTEventType {
    FTTransferEvent(FTTransferEventData),
    FTMintEvent(FTMintEventData),
    FTBurnEvent(FTBurnEventData),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct STXTransferEventData {
    pub sender: PrincipalData,
    pub recipient: PrincipalData,
    pub amount: u128,
}

impl STXTransferEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        json!({
            "sender": format!("{}",self.sender),
            "recipient": format!("{}",self.recipient),
            "amount": format!("{}", self.amount),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct STXMintEventData {
    pub recipient: PrincipalData,
    pub amount: u128,
}

impl STXMintEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        json!({
            "recipient": format!("{}",self.recipient),
            "amount": format!("{}", self.amount),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct STXLockEventData {
    pub locked_amount: u128,
    pub unlock_height: u64,
    pub locked_address: PrincipalData,
}

impl STXLockEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        json!({
            "locked_amount": format!("{}",self.locked_amount),
            "unlock_height": format!("{}", self.unlock_height),
            "locked_address": format!("{}", self.locked_address),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct STXBurnEventData {
    pub sender: PrincipalData,
    pub amount: u128,
}

impl STXBurnEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        json!({
            "sender": format!("{}", self.sender),
            "amount": format!("{}", self.amount),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct NFTTransferEventData {
    pub asset_identifier: AssetIdentifier,
    pub sender: PrincipalData,
    pub recipient: PrincipalData,
    pub value: Value,
}

impl NFTTransferEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        let raw_value = {
            let mut bytes = vec![];
            self.value.consensus_serialize(&mut bytes).unwrap();
            let formatted_bytes: Vec<String> = bytes.iter().map(|b| format!("{:02x}", b)).collect();
            formatted_bytes
        };
        json!({
            "asset_identifier": format!("{}", self.asset_identifier),
            "sender": format!("{}",self.sender),
            "recipient": format!("{}",self.recipient),
            "value": self.value,
            "raw_value": format!("0x{}", raw_value.join("")),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct NFTMintEventData {
    pub asset_identifier: AssetIdentifier,
    pub recipient: PrincipalData,
    pub value: Value,
}

impl NFTMintEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        let raw_value = {
            let mut bytes = vec![];
            self.value.consensus_serialize(&mut bytes).unwrap();
            let formatted_bytes: Vec<String> = bytes.iter().map(|b| format!("{:02x}", b)).collect();
            formatted_bytes
        };
        json!({
            "asset_identifier": format!("{}", self.asset_identifier),
            "recipient": format!("{}",self.recipient),
            "value": self.value,
            "raw_value": format!("0x{}", raw_value.join("")),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct NFTBurnEventData {
    pub asset_identifier: AssetIdentifier,
    pub sender: PrincipalData,
    pub value: Value,
}

impl NFTBurnEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        let raw_value = {
            let mut bytes = vec![];
            self.value.consensus_serialize(&mut bytes).unwrap();
            let formatted_bytes: Vec<String> = bytes.iter().map(|b| format!("{:02x}", b)).collect();
            formatted_bytes
        };
        json!({
            "asset_identifier": format!("{}", self.asset_identifier),
            "sender": format!("{}",self.sender),
            "value": self.value,
            "raw_value": format!("0x{}", raw_value.join("")),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FTTransferEventData {
    pub asset_identifier: AssetIdentifier,
    pub sender: PrincipalData,
    pub recipient: PrincipalData,
    pub amount: u128,
}

impl FTTransferEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        json!({
            "asset_identifier": format!("{}", self.asset_identifier),
            "sender": format!("{}",self.sender),
            "recipient": format!("{}",self.recipient),
            "amount": format!("{}", self.amount),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FTMintEventData {
    pub asset_identifier: AssetIdentifier,
    pub recipient: PrincipalData,
    pub amount: u128,
}

impl FTMintEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        json!({
            "asset_identifier": format!("{}", self.asset_identifier),
            "recipient": format!("{}",self.recipient),
            "amount": format!("{}", self.amount),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FTBurnEventData {
    pub asset_identifier: AssetIdentifier,
    pub sender: PrincipalData,
    pub amount: u128,
}

impl FTBurnEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        json!({
            "asset_identifier": format!("{}", self.asset_identifier),
            "sender": format!("{}",self.sender),
            "amount": format!("{}", self.amount),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SmartContractEventData {
    pub key: (QualifiedContractIdentifier, String),
    pub value: Value,
}

impl SmartContractEventData {
    pub fn json_serialize(&self) -> serde_json::Value {
        let raw_value = {
            let mut bytes = vec![];
            self.value.consensus_serialize(&mut bytes).unwrap();
            let formatted_bytes: Vec<String> = bytes.iter().map(|b| format!("{:02x}", b)).collect();
            formatted_bytes
        };
        json!({
            "contract_identifier": self.key.0.to_string(),
            "topic": self.key.1,
            "value": self.value,
            "raw_value": format!("0x{}", raw_value.join("")),
        })
    }
}
