use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_types::{SszList, SszVector};

use super::deneb::MAX_BLOB_COMMITMENTS_PER_BLOCK;
use super::phase0::SignedBeaconBlockHeader;

pub const FIELD_ELEMENTS_PER_CELL: usize = 64;
pub const BYTES_PER_FIELD_ELEMENT: usize = 32;
pub const BYTES_PER_CELL: usize = FIELD_ELEMENTS_PER_CELL * BYTES_PER_FIELD_ELEMENT;
pub const NUMBER_OF_COLUMNS: usize = 128;
pub const KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH: usize = 4;

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DataColumnSidecar {
    pub index: u64,
    pub column: SszList<SszVector<u8, BYTES_PER_CELL>, MAX_BLOB_COMMITMENTS_PER_BLOCK>,
    pub kzg_commitments: SszList<[u8; 48], MAX_BLOB_COMMITMENTS_PER_BLOCK>,
    pub kzg_proofs: SszList<[u8; 48], MAX_BLOB_COMMITMENTS_PER_BLOCK>,
    pub signed_block_header: SignedBeaconBlockHeader,
    pub kzg_commitments_inclusion_proof: SszVector<[u8; 32], KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct MatrixEntry {
    pub cell: SszVector<u8, BYTES_PER_CELL>,
    pub kzg_proof: [u8; 48],
    pub column_index: u64,
    pub row_index: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DataColumnsByRootIdentifier {
    pub block_root: [u8; 32],
    pub columns: SszList<u64, NUMBER_OF_COLUMNS>,
}
