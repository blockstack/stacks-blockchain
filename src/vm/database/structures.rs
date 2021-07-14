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

use serde::Deserialize;
use std::convert::TryInto;
use std::io::Write;
use util::hash::{hex_bytes, to_hex};
use vm::analysis::ContractAnalysis;
use vm::contracts::Contract;
use vm::database::ClarityDatabase;
use vm::errors::{Error, IncomparableError, InterpreterError, InterpreterResult, RuntimeErrorType};
use vm::types::{OptionalData, PrincipalData, TupleTypeSignature, TypeSignature, Value, NONE};

pub trait ClaritySerializable {
    fn serialize(&self) -> String;
}

pub trait ClarityDeserializable<T> {
    fn deserialize(json: &str) -> T;
}

impl ClaritySerializable for String {
    fn serialize(&self) -> String {
        self.into()
    }
}

impl ClarityDeserializable<String> for String {
    fn deserialize(serialized: &str) -> String {
        serialized.into()
    }
}

macro_rules! clarity_serializable {
    ($Name:ident) => {
        impl ClaritySerializable for $Name {
            fn serialize(&self) -> String {
                serde_json::to_string(self).expect("Failed to serialize vm.Value")
            }
        }
        impl ClarityDeserializable<$Name> for $Name {
            fn deserialize(json: &str) -> Self {
                let mut deserializer = serde_json::Deserializer::from_str(&json);
                // serde's default 128 depth limit can be exhausted
                //  by a 64-stack-depth AST, so disable the recursion limit
                deserializer.disable_recursion_limit();
                // use stacker to prevent the deserializer from overflowing.
                //  this will instead spill to the heap
                let deserializer = serde_stacker::Deserializer::new(&mut deserializer);
                Deserialize::deserialize(deserializer).expect("Failed to deserialize vm.Value")
            }
        }
    };
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FungibleTokenMetadata {
    pub total_supply: Option<u128>,
}

clarity_serializable!(FungibleTokenMetadata);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonFungibleTokenMetadata {
    pub key_type: TypeSignature,
}

clarity_serializable!(NonFungibleTokenMetadata);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataMapMetadata {
    pub key_type: TypeSignature,
    pub value_type: TypeSignature,
}

clarity_serializable!(DataMapMetadata);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataVariableMetadata {
    pub value_type: TypeSignature,
}

clarity_serializable!(DataVariableMetadata);

#[derive(Serialize, Deserialize)]
pub struct ContractMetadata {
    pub contract: Contract,
}

clarity_serializable!(ContractMetadata);

#[derive(Serialize, Deserialize)]
pub struct SimmedBlock {
    pub block_height: u64,
    pub block_time: u64,
    pub block_header_hash: [u8; 32],
    pub burn_chain_header_hash: [u8; 32],
    pub vrf_seed: [u8; 32],
}

clarity_serializable!(SimmedBlock);

clarity_serializable!(PrincipalData);
clarity_serializable!(i128);
clarity_serializable!(u128);
clarity_serializable!(u64);
clarity_serializable!(u32);
clarity_serializable!(Contract);
clarity_serializable!(ContractAnalysis);

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum STXBalance {
    Unlocked {
        amount: u128,
    },
    LockedPoxOne {
        amount_unlocked: u128,
        amount_locked: u128,
        unlock_height: u64,
    },
    LockedPoxTwo {
        amount_unlocked: u128,
        amount_locked: u128,
        unlock_height: u64,
    },
}

/// Lifetime-limited handle to an uncommitted balance structure.
/// All balance mutations (debits, credits, locks, unlocks) must go through this structure.
pub struct STXBalanceSnapshot<'db, 'conn> {
    principal: PrincipalData,
    balance: STXBalance,
    burn_block_height: u64,
    db_ref: &'conn mut ClarityDatabase<'db>,
}

type Result<T> = std::result::Result<T, Error>;

impl ClaritySerializable for STXBalance {
    fn serialize(&self) -> String {
        let mut buffer = Vec::new();
        match self {
            STXBalance::Unlocked { amount } => {
                buffer
                    .write_all(&amount.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_unlocked.");
                buffer
                    .write_all(&0u128.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_locked.");
                buffer
                    .write_all(&0u64.to_be_bytes())
                    .expect("STXBalance serialization: failed writing unlock_height.");
            }
            STXBalance::LockedPoxOne {
                amount_unlocked,
                amount_locked,
                unlock_height,
            } => {
                buffer
                    .write_all(&amount_unlocked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_unlocked.");
                buffer
                    .write_all(&amount_locked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_locked.");
                buffer
                    .write_all(&unlock_height.to_be_bytes())
                    .expect("STXBalance serialization: failed writing unlock_height.");
            }
            STXBalance::LockedPoxTwo {
                amount_unlocked,
                amount_locked,
                unlock_height,
            } => {
                buffer
                    .write_all(&[STXBalance::pox_2_version])
                    .expect("STXBalance serialization: failed to write PoX version byte");
                buffer
                    .write_all(&amount_unlocked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_unlocked.");
                buffer
                    .write_all(&amount_locked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_locked.");
                buffer
                    .write_all(&unlock_height.to_be_bytes())
                    .expect("STXBalance serialization: failed writing unlock_height.");
            }
        }
        to_hex(buffer.as_slice())
    }
}

impl ClarityDeserializable<STXBalance> for STXBalance {
    fn deserialize(input: &str) -> Self {
        let bytes = hex_bytes(&input).expect("STXBalance deserialization: failed decoding bytes.");
        if bytes.len() == STXBalance::unlocked_and_v1_size {
            let amount_unlocked = u128::from_be_bytes(
                bytes[0..16]
                    .try_into()
                    .expect("STXBalance deserialization: failed reading amount_unlocked."),
            );
            let amount_locked = u128::from_be_bytes(
                bytes[16..32]
                    .try_into()
                    .expect("STXBalance deserialization: failed reading amount_locked."),
            );
            let unlock_height = u64::from_be_bytes(
                bytes[32..40]
                    .try_into()
                    .expect("STXBalance deserialization: failed reading unlock_height."),
            );

            if amount_locked == 0 {
                STXBalance::Unlocked {
                    amount: amount_unlocked,
                }
            } else {
                STXBalance::LockedPoxOne {
                    amount_unlocked,
                    amount_locked,
                    unlock_height,
                }
            }
        } else if bytes.len() == STXBalance::v2_size {
            let version = &bytes[0];
            if version != &STXBalance::pox_2_version {
                panic!(
                    "Bad version byte in STX Balance serialization = {}",
                    version
                );
            }
            let amount_unlocked = u128::from_be_bytes(
                bytes[1..17]
                    .try_into()
                    .expect("STXBalance deserialization: failed reading amount_unlocked."),
            );
            let amount_locked = u128::from_be_bytes(
                bytes[17..33]
                    .try_into()
                    .expect("STXBalance deserialization: failed reading amount_locked."),
            );
            let unlock_height = u64::from_be_bytes(
                bytes[33..41]
                    .try_into()
                    .expect("STXBalance deserialization: failed reading unlock_height."),
            );

            if amount_locked == 0 {
                STXBalance::Unlocked {
                    amount: amount_unlocked,
                }
            } else {
                STXBalance::LockedPoxTwo {
                    amount_unlocked,
                    amount_locked,
                    unlock_height,
                }
            }
        } else {
            panic!("Bad STX Balance serialization size = {}", bytes.len());
        }
    }
}

impl<'db, 'conn> STXBalanceSnapshot<'db, 'conn> {
    pub fn new(
        principal: &PrincipalData,
        balance: STXBalance,
        burn_height: u64,
        db_ref: &'conn mut ClarityDatabase<'db>,
    ) -> STXBalanceSnapshot<'db, 'conn> {
        STXBalanceSnapshot {
            principal: principal.clone(),
            balance,
            burn_block_height: burn_height,
            db_ref,
        }
    }

    pub fn balance(&self) -> &STXBalance {
        &self.balance
    }

    pub fn save(self) -> () {
        let key = ClarityDatabase::make_key_for_account_balance(&self.principal);
        self.db_ref.put(&key, &self.balance)
    }

    pub fn transfer_to(mut self, recipient: &PrincipalData, amount: u128) -> Result<()> {
        if !self.can_transfer(amount) {
            return Err(InterpreterError::InsufficientBalance.into());
        }

        let recipient_key = ClarityDatabase::make_key_for_account_balance(recipient);
        let mut recipient_balance = self
            .db_ref
            .get(&recipient_key)
            .unwrap_or(STXBalance::zero());

        recipient_balance
            .checked_add_unlocked_amount(amount)
            .ok_or(Error::Runtime(RuntimeErrorType::ArithmeticOverflow, None))?;

        self.debit(amount);
        self.db_ref.put(&recipient_key, &recipient_balance);
        self.save();
        Ok(())
    }

    pub fn get_available_balance(&self) -> u128 {
        let v1_unlock_height = self.db_ref.get_v1_unlock_height();
        self.balance
            .get_available_balance_at_burn_block(self.burn_block_height, v1_unlock_height)
    }

    pub fn canonical_balance_repr(&self) -> STXBalance {
        let v1_unlock_height = self.db_ref.get_v1_unlock_height();
        self.balance
            .canonical_repr_at_block(self.burn_block_height, v1_unlock_height)
            .0
    }

    pub fn has_locked_tokens(&self) -> bool {
        let v1_unlock_height = self.db_ref.get_v1_unlock_height();
        self.balance
            .has_locked_tokens_at_burn_block(self.burn_block_height, v1_unlock_height)
    }

    pub fn has_unlockable_tokens(&self) -> bool {
        let v1_unlock_height = self.db_ref.get_v1_unlock_height();
        self.balance
            .has_unlockable_tokens_at_burn_block(self.burn_block_height, v1_unlock_height)
    }

    pub fn can_transfer(&self, amount: u128) -> bool {
        self.get_available_balance() >= amount
    }

    pub fn debit(&mut self, amount: u128) {
        let unlocked = self.unlock_available_tokens_if_any();
        if unlocked > 0 {
            debug!("Consolidated after account-debit");
        }

        self.balance.debit_unlocked_amount(amount)
    }

    pub fn credit(&mut self, amount: u128) {
        let unlocked = self.unlock_available_tokens_if_any();
        if unlocked > 0 {
            debug!("Consolidated after account-credit");
        }

        self.balance
            .checked_add_unlocked_amount(amount)
            .expect("STX balance overflow");
    }

    pub fn set_balance(&mut self, balance: STXBalance) {
        self.balance = balance;
    }

    pub fn lock_tokens_v1(&mut self, amount_to_lock: u128, unlock_burn_height: u64) {
        let unlocked = self.unlock_available_tokens_if_any();
        if unlocked > 0 {
            debug!("Consolidated after account-token-lock");
        }

        // caller needs to have checked this
        assert!(amount_to_lock > 0, "BUG: cannot lock 0 tokens");

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            panic!("FATAL: cannot set a lock with expired unlock burn height");
        }

        if self.has_locked_tokens() {
            // caller needs to have checked this
            panic!("FATAL: account already has locked tokens");
        }

        // from `unlock_available_tokens_if_any` call above, `self.balance` should
        //  be canonicalized already

        let new_amount_unlocked = self
            .balance
            .get_total_balance()
            .checked_sub(amount_to_lock)
            .expect("STX underflow");

        self.balance = STXBalance::LockedPoxOne {
            amount_unlocked: new_amount_unlocked,
            amount_locked: amount_to_lock,
            unlock_height: unlock_burn_height,
        };
    }

    pub fn extend_lock_v2(&mut self, unlock_burn_height: u64) {
        let unlocked = self.unlock_available_tokens_if_any();
        if unlocked > 0 {
            debug!("Consolidated after extend-token-lock");
        }

        if !self.has_locked_tokens() {
            // caller needs to have checked this
            panic!("FATAL: account does not have locked tokens");
        }

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            panic!("FATAL: cannot set a lock with expired unlock burn height");
        }

        self.balance = STXBalance::LockedPoxTwo {
            amount_unlocked: self.balance.amount_unlocked(),
            amount_locked: self.balance.amount_locked(),
            unlock_height: unlock_burn_height,
        };
    }

    pub fn lock_tokens_v2(&mut self, amount_to_lock: u128, unlock_burn_height: u64) {
        let unlocked = self.unlock_available_tokens_if_any();
        if unlocked > 0 {
            debug!("Consolidated after account-token-lock");
        }

        // caller needs to have checked this
        assert!(amount_to_lock > 0, "BUG: cannot lock 0 tokens");

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            panic!("FATAL: cannot set a lock with expired unlock burn height");
        }

        if self.has_locked_tokens() {
            // caller needs to have checked this
            panic!("FATAL: account already has locked tokens");
        }

        // from `unlock_available_tokens_if_any` call above, `self.balance` should
        //  be canonicalized already

        let new_amount_unlocked = self
            .balance
            .get_total_balance()
            .checked_sub(amount_to_lock)
            .expect("STX underflow");

        self.balance = STXBalance::LockedPoxTwo {
            amount_unlocked: new_amount_unlocked,
            amount_locked: amount_to_lock,
            unlock_height: unlock_burn_height,
        };
    }

    /// Unlock any tokens that are unlockable at the current
    ///  burn block height, and return the amount newly unlocked
    fn unlock_available_tokens_if_any(&mut self) -> u128 {
        let (new_balance, unlocked) = self
            .balance
            .canonical_repr_at_block(self.burn_block_height, self.db_ref.get_v1_unlock_height());
        self.balance = new_balance;
        unlocked
    }
}

// NOTE: do _not_ add mutation methods to this struct. Put them in STXBalanceSnapshot!
impl STXBalance {
    pub const unlocked_and_v1_size: usize = 40;
    pub const v2_size: usize = 41;
    pub const pox_2_version: u8 = 0;

    pub fn zero() -> STXBalance {
        STXBalance::Unlocked { amount: 0 }
    }

    pub fn initial(amount: u128) -> STXBalance {
        STXBalance::Unlocked { amount }
    }

    /// This method returns the datastructure's lazy view of the unlock_height:
    ///  this *may* be updated by a canonicalized view of the account
    pub fn unlock_height(&self) -> u64 {
        match self {
            STXBalance::Unlocked { .. } => 0,
            STXBalance::LockedPoxOne { unlock_height, .. }
            | STXBalance::LockedPoxTwo { unlock_height, .. } => *unlock_height,
        }
    }

    /// This method returns the datastructure's lazy view of the unlock_height
    ///  *while* factoring in the PoX 2 early unlock for PoX 1.
    /// This value is still lazy: this unlock height may be less than the current
    ///  burn block height, if so it will be updated in a canonicalized view.
    pub fn effective_unlock_height(&self, v1_unlock_height: u32) -> u64 {
        match self {
            STXBalance::Unlocked { .. } => 0,
            STXBalance::LockedPoxOne { unlock_height, .. } => {
                if *unlock_height >= (v1_unlock_height as u64) {
                    v1_unlock_height as u64
                } else {
                    *unlock_height
                }
            }
            STXBalance::LockedPoxTwo { unlock_height, .. } => *unlock_height,
        }
    }

    /// This method returns the datastructure's lazy view of the amount locked:
    ///  this *may* be updated by a canonicalized view of the account
    pub fn amount_locked(&self) -> u128 {
        match self {
            STXBalance::Unlocked { .. } => 0,
            STXBalance::LockedPoxOne { amount_locked, .. }
            | STXBalance::LockedPoxTwo { amount_locked, .. } => *amount_locked,
        }
    }

    /// This method returns the datastructure's lazy view of the amount unlocked:
    ///  this *may* be updated by a canonicalized view of the account
    pub fn amount_unlocked(&self) -> u128 {
        match self {
            STXBalance::Unlocked {
                amount: amount_unlocked,
            }
            | STXBalance::LockedPoxOne {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxTwo {
                amount_unlocked, ..
            } => *amount_unlocked,
        }
    }

    fn debit_unlocked_amount(&mut self, delta: u128) {
        match self {
            STXBalance::Unlocked {
                amount: amount_unlocked,
            }
            | STXBalance::LockedPoxOne {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxTwo {
                amount_unlocked, ..
            } => {
                *amount_unlocked = amount_unlocked.checked_sub(delta).expect("STX underflow");
            }
        }
    }

    fn checked_add_unlocked_amount(&mut self, delta: u128) -> Option<u128> {
        match self {
            STXBalance::Unlocked {
                amount: amount_unlocked,
            }
            | STXBalance::LockedPoxOne {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxTwo {
                amount_unlocked, ..
            } => {
                if let Some(new_amount) = amount_unlocked.checked_add(delta) {
                    *amount_unlocked = new_amount;
                    Some(new_amount)
                } else {
                    None
                }
            }
        }
    }

    fn set_locked(&mut self) {
        match self {
            STXBalance::Unlocked { .. } => {}
            STXBalance::LockedPoxOne {
                unlock_height,
                amount_locked,
                ..
            } => {
                *unlock_height = 0;
                *amount_locked = 0;
            }
            STXBalance::LockedPoxTwo {
                unlock_height,
                amount_locked,
                ..
            } => {
                *unlock_height = 0;
                *amount_locked = 0;
            }
        }
    }

    /// Returns a canonicalized STXBalance at a given burn_block_height
    /// (i.e., if burn_block_height >= unlock_height, then return struct where
    ///   amount_unlocked = 0, unlock_height = 0), and the amount of tokens which
    ///   are "unlocked" by the canonicalization
    pub fn canonical_repr_at_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
    ) -> (STXBalance, u128) {
        if self.has_unlockable_tokens_at_burn_block(burn_block_height, v1_unlock_height) {
            (
                STXBalance::Unlocked {
                    amount: self.get_total_balance(),
                },
                self.amount_locked(),
            )
        } else {
            (self.clone(), 0)
        }
    }

    pub fn get_available_balance_at_burn_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
    ) -> u128 {
        if self.has_unlockable_tokens_at_burn_block(burn_block_height, v1_unlock_height) {
            self.get_total_balance()
        } else {
            match self {
                STXBalance::Unlocked { amount } => *amount,
                STXBalance::LockedPoxOne {
                    amount_unlocked, ..
                } => *amount_unlocked,
                STXBalance::LockedPoxTwo {
                    amount_unlocked, ..
                } => *amount_unlocked,
            }
        }
    }

    pub fn get_locked_balance_at_burn_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
    ) -> (u128, u64) {
        if self.has_unlockable_tokens_at_burn_block(burn_block_height, v1_unlock_height) {
            (0, 0)
        } else {
            match self {
                STXBalance::Unlocked { .. } => (0, 0),
                STXBalance::LockedPoxOne {
                    amount_locked,
                    unlock_height,
                    ..
                } => (*amount_locked, *unlock_height),
                STXBalance::LockedPoxTwo {
                    amount_locked,
                    unlock_height,
                    ..
                } => (*amount_locked, *unlock_height),
            }
        }
    }

    pub fn get_total_balance(&self) -> u128 {
        let (unlocked, locked) = match self {
            STXBalance::Unlocked { amount } => (*amount, 0),
            STXBalance::LockedPoxOne {
                amount_unlocked,
                amount_locked,
                ..
            } => (*amount_unlocked, *amount_locked),
            STXBalance::LockedPoxTwo {
                amount_unlocked,
                amount_locked,
                ..
            } => (*amount_unlocked, *amount_locked),
        };
        unlocked.checked_add(locked).expect("STX overflow")
    }

    pub fn was_locked_by_v2(&self) -> bool {
        if let STXBalance::LockedPoxTwo { .. } = self {
            true
        } else {
            false
        }
    }

    pub fn has_locked_tokens_at_burn_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
    ) -> bool {
        match self {
            STXBalance::Unlocked { .. } => false,
            STXBalance::LockedPoxOne {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                // if normally unlockable, return false
                if *unlock_height <= burn_block_height {
                    return false;
                }
                // if unlockable due to Stacks 2.1 early unlock
                if v1_unlock_height as u64 <= burn_block_height {
                    return false;
                }
                true
            }
            STXBalance::LockedPoxTwo {
                amount_locked,
                unlock_height,
                ..
            } => *amount_locked > 0 && *unlock_height > burn_block_height,
        }
    }

    pub fn has_unlockable_tokens_at_burn_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
    ) -> bool {
        match self {
            STXBalance::Unlocked { .. } => false,
            STXBalance::LockedPoxOne {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                // if normally unlockable, return true
                if *unlock_height <= burn_block_height {
                    return true;
                }
                // if unlockable due to Stacks 2.1 early unlock
                if v1_unlock_height as u64 <= burn_block_height {
                    return true;
                }
                false
            }
            STXBalance::LockedPoxTwo {
                amount_locked,
                unlock_height,
                ..
            } => *amount_locked > 0 && *unlock_height <= burn_block_height,
        }
    }

    pub fn can_transfer_at_burn_block(
        &self,
        amount: u128,
        burn_block_height: u64,
        v1_unlock_height: u32,
    ) -> bool {
        self.get_available_balance_at_burn_block(burn_block_height, v1_unlock_height) >= amount
    }
}
