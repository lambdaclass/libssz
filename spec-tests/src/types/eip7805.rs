use ssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use ssz_types::SszList;

use super::bellatrix::MAX_BYTES_PER_TRANSACTION;
use super::bellatrix::MAX_TRANSACTIONS_PER_PAYLOAD;

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct InclusionList {
    pub slot: u64,
    pub validator_index: u64,
    pub inclusion_list_committee_root: [u8; 32],
    pub transactions: SszList<SszList<u8, MAX_BYTES_PER_TRANSACTION>, MAX_TRANSACTIONS_PER_PAYLOAD>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedInclusionList {
    pub message: InclusionList,
    pub signature: [u8; 96],
}
