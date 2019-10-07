// Copyright 2015-2019 Parity Technologies (UK) Ltd.
// This file is part of Parity Ethereum.

// Parity Ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity Ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity Ethereum.  If not, see <http://www.gnu.org/licenses/>.

//! Receipt

use ethereum_types::{H160, H256, U256, Address, Bloom};
use parity_util_mem::MallocSizeOf;
use rlp::{Rlp, RlpStream, Encodable, Decodable, DecoderError};

use BlockNumber;
use log_entry::{LogEntry, LocalizedLogEntry};

/// Transaction outcome store in the receipt.
#[derive(Debug, Clone, PartialEq, Eq, MallocSizeOf)]
pub enum TransactionOutcome {
	/// Status and state root are unknown under EIP-98 rules.
	Unknown,
	/// State root is known. Pre EIP-98 and EIP-658 rules.
	StateRoot(H256),
	/// Status code is known. EIP-658 rules.
	StatusCode(u8),
}

/// Information describing execution of a transaction.
#[derive(Debug, Clone, PartialEq, Eq, MallocSizeOf)]
pub struct Receipt {
	/// The gas used in the execution of the transaction. Note the difference of meaning to `Receipt::gas_used`.
	pub gas_used: U256,
	/// Logs bloom
	pub log_bloom: Bloom,
	/// Logs
	pub logs: Vec<LogEntry>,
	/// Transaction outcome.
	pub outcome: TransactionOutcome,
	/// Transaction hash.
	pub transaction_hash: H256,
	/// Transaction index.
	pub transaction_index: usize,
	/// The total gas used in the block following execution of the transaction.
	pub cumulative_gas_used: U256,
	/// Contract address.
	pub contract_address: Option<Address>,
}

impl Receipt {
	/// Create an empty Receipt for tests?!
	pub fn empty() -> Self {
		Self {
			gas_used: U256::zero(),
			log_bloom: Bloom::default(),
			logs: Vec::new(),
			outcome: TransactionOutcome::Unknown,
			transaction_hash: H256::zero(),
			transaction_index: 0,
			cumulative_gas_used: U256::zero(),
			contract_address: None,
		}
	}
}

impl Encodable for Receipt {
	fn rlp_append(&self, s: &mut RlpStream) {
		match self.outcome {
			TransactionOutcome::Unknown => {
				s.begin_list(7);
			},
			TransactionOutcome::StateRoot(ref root) => {
				s.begin_list(8);
				s.append(root);
			},
			TransactionOutcome::StatusCode(ref status_code) => {
				s.begin_list(8);
				s.append(status_code);
			},
		}
		s.append(&self.gas_used);
		s.append(&self.log_bloom);
		s.append_list(&self.logs);
		s.append(&self.transaction_hash);
		s.append(&self.transaction_index);
		s.append(&self.cumulative_gas_used);
		s.append(&self.contract_address);
	}
}

impl Decodable for Receipt {
	fn decode(rlp: &Rlp) -> Result<Self, DecoderError> {
		if rlp.item_count()? == 7 {
			Ok(Receipt {
				outcome: TransactionOutcome::Unknown,
				gas_used: rlp.val_at(0)?,
				log_bloom: rlp.val_at(1)?,
				logs: rlp.list_at(2)?,
				transaction_hash: rlp.val_at(3)?,
				transaction_index: rlp.val_at(4)?,
				cumulative_gas_used: rlp.val_at(5)?,
				contract_address: rlp.val_at(6)?,
			})
		} else {
			Ok(Receipt {
				outcome: {
					let first = rlp.at(0)?;
					if first.is_data() && first.data()?.len() <= 1 {
						TransactionOutcome::StatusCode(first.as_val()?)
					} else {
						TransactionOutcome::StateRoot(first.as_val()?)
					}
				},
				gas_used: rlp.val_at(1)?,
				log_bloom: rlp.val_at(2)?,
				logs: rlp.list_at(3)?,
				transaction_hash: rlp.val_at(4)?,
				transaction_index: rlp.val_at(5)?,
				cumulative_gas_used: rlp.val_at(6)?,
				contract_address: rlp.val_at(7)?,
			})
		}
	}
}

/// Receipt with additional info.
#[derive(Debug, Clone, PartialEq)]
pub struct LocalizedReceipt {
	/// Transaction hash.
	pub transaction_hash: H256,
	/// Transaction index.
	pub transaction_index: usize,
	/// Block hash.
	pub block_hash: H256,
	/// Block number.
	pub block_number: BlockNumber,
	/// The total gas used in the block following execution of the transaction.
	pub cumulative_gas_used: U256,
	/// The gas used in the execution of the transaction. Note the difference of meaning to `Receipt::gas_used`.
	pub gas_used: U256,
	/// Contract address.
	pub contract_address: Option<Address>,
	/// Logs
	pub logs: Vec<LocalizedLogEntry>,
	/// Logs bloom
	pub log_bloom: Bloom,
	/// Transaction outcome.
	pub outcome: TransactionOutcome,
	/// Receiver address
	pub to: Option<H160>,
	/// Sender
	pub from: H160
}

#[cfg(test)]
mod tests {
	use super::{Receipt, TransactionOutcome, Address, H256};
	use log_entry::LogEntry;
	use std::str::FromStr;

	#[test]
	fn test_no_state_root() {
		let expected = ::rustc_hex::FromHex::from_hex("f9014183040caeb9010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000f838f794dcf421d093428b096ca501a7cd1a740855a7976fc0a00000000000000000000000000000000000000000000000000000000000000000").unwrap();
		let r = Receipt::new(
			TransactionOutcome::Unknown,
			0x40cae.into(),
			vec![LogEntry {
				address: Address::from_str("dcf421d093428b096ca501a7cd1a740855a7976f").unwrap(),
				topics: vec![],
				data: vec![0u8; 32]
			}]
		);
		assert_eq!(&::rlp::encode(&r)[..], &expected[..]);
	}

	#[test]
	fn test_basic() {
		let expected = ::rustc_hex::FromHex::from_hex("f90162a02f697d671e9ae4ee24a43c4b0d7e15f1cb4ba6de1561120d43b9a4e8c4a8a6ee83040caeb9010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000f838f794dcf421d093428b096ca501a7cd1a740855a7976fc0a00000000000000000000000000000000000000000000000000000000000000000").unwrap();
		let r = Receipt::new(
			TransactionOutcome::StateRoot(H256::from_str("2f697d671e9ae4ee24a43c4b0d7e15f1cb4ba6de1561120d43b9a4e8c4a8a6ee").unwrap()),
			0x40cae.into(),
			vec![LogEntry {
				address: Address::from_str("dcf421d093428b096ca501a7cd1a740855a7976f").unwrap(),
				topics: vec![],
				data: vec![0u8; 32]
			}]
		);
		let encoded = ::rlp::encode(&r);
		assert_eq!(&encoded[..], &expected[..]);
		let decoded: Receipt = ::rlp::decode(&encoded).expect("decoding receipt failed");
		assert_eq!(decoded, r);
	}

	#[test]
	fn test_status_code() {
		let expected = ::rustc_hex::FromHex::from_hex("f901428083040caeb9010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000f838f794dcf421d093428b096ca501a7cd1a740855a7976fc0a00000000000000000000000000000000000000000000000000000000000000000").unwrap();
		let r = Receipt::new(
			TransactionOutcome::StatusCode(0),
			0x40cae.into(),
			vec![LogEntry {
				address: Address::from_str("dcf421d093428b096ca501a7cd1a740855a7976f").unwrap(),
				topics: vec![],
				data: vec![0u8; 32]
			}]
		);
		let encoded = ::rlp::encode(&r);
		assert_eq!(&encoded[..], &expected[..]);
		let decoded: Receipt = ::rlp::decode(&encoded).expect("decoding receipt failed");
		assert_eq!(decoded, r);
	}
}
