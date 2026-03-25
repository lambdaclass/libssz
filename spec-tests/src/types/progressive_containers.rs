use libssz_derive::{SszDecode, SszEncode};
use libssz_merkle::{
    merkleize_progressive, mix_in_active_fields, HashTreeRoot, Node, Sha256Hasher,
};
use libssz_types::{ProgressiveBitlist, ProgressiveList, SszBitlist, SszBitvector, SszList};

use super::containers::SmallTestStruct;

// Helper: build chunks for progressive container merkleization.
// Places field roots at positions corresponding to `1` entries in active_fields,
// fills `0` positions with zero nodes.
fn progressive_container_chunks(field_roots: &[Node], active_fields: &[bool]) -> Vec<Node> {
    let mut chunks = Vec::with_capacity(active_fields.len());
    let mut field_idx = 0;
    for &active in active_fields {
        if active {
            chunks.push(field_roots[field_idx]);
            field_idx += 1;
        } else {
            chunks.push([0u8; 32]);
        }
    }
    assert_eq!(field_idx, field_roots.len());
    chunks
}

// ── ProgressiveSingleFieldContainerTestStruct ──
// active_fields = [1]

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode)]
pub struct ProgressiveSingleFieldContainerTestStruct {
    pub a: u8,
}

impl HashTreeRoot for ProgressiveSingleFieldContainerTestStruct {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        let active_fields = &[true];
        let field_roots = [self.a.hash_tree_root(hasher)];
        let chunks = progressive_container_chunks(&field_roots, active_fields);
        let root = merkleize_progressive(hasher, &chunks);
        mix_in_active_fields(hasher, &root, active_fields)
    }
}

// ── ProgressiveSingleListContainerTestStruct ──
// active_fields = [0, 0, 0, 0, 1]

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode)]
pub struct ProgressiveSingleListContainerTestStruct {
    pub c: ProgressiveBitlist,
}

impl HashTreeRoot for ProgressiveSingleListContainerTestStruct {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        let active_fields = &[false, false, false, false, true];
        let field_roots = [self.c.hash_tree_root(hasher)];
        let chunks = progressive_container_chunks(&field_roots, active_fields);
        let root = merkleize_progressive(hasher, &chunks);
        mix_in_active_fields(hasher, &root, active_fields)
    }
}

// ── ProgressiveVarTestStruct ──
// active_fields = [1, 0, 1, 0, 1]

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode)]
pub struct ProgressiveVarTestStruct {
    pub a: u8,
    pub b: SszList<u16, 123>,
    pub c: ProgressiveBitlist,
}

impl HashTreeRoot for ProgressiveVarTestStruct {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        let active_fields = &[true, false, true, false, true];
        let field_roots = [
            self.a.hash_tree_root(hasher),
            self.b.hash_tree_root(hasher),
            self.c.hash_tree_root(hasher),
        ];
        let chunks = progressive_container_chunks(&field_roots, active_fields);
        let root = merkleize_progressive(hasher, &chunks);
        mix_in_active_fields(hasher, &root, active_fields)
    }
}

// ── ProgressiveComplexTestStruct ──
// active_fields = [1,0,1,0,1,0,0,0,1,0,0,0,1,1,0,0,0,0,0,0,1,1]

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode)]
pub struct ProgressiveComplexTestStruct {
    pub a: u8,
    pub b: SszList<u16, 123>,
    pub c: ProgressiveBitlist,
    pub d: ProgressiveList<u64>,
    pub e: ProgressiveList<SmallTestStruct>,
    pub f: ProgressiveList<ProgressiveList<VarTestStruct>>,
    pub g: SszList<ProgressiveSingleFieldContainerTestStruct, 10>,
    pub h: ProgressiveList<ProgressiveVarTestStruct>,
}

impl HashTreeRoot for ProgressiveComplexTestStruct {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        let active_fields = &[
            true, false, true, false, true, false, false, false, true, false, false, false, true,
            true, false, false, false, false, false, false, true, true,
        ];
        let field_roots = [
            self.a.hash_tree_root(hasher),
            self.b.hash_tree_root(hasher),
            self.c.hash_tree_root(hasher),
            self.d.hash_tree_root(hasher),
            self.e.hash_tree_root(hasher),
            self.f.hash_tree_root(hasher),
            self.g.hash_tree_root(hasher),
            self.h.hash_tree_root(hasher),
        ];
        let chunks = progressive_container_chunks(&field_roots, active_fields);
        let root = merkleize_progressive(hasher, &chunks);
        mix_in_active_fields(hasher, &root, active_fields)
    }
}

// ── ProgressiveTestStruct ──
// From the containers handler (not progressive_containers)
// active_fields implied from test spec:
// class ProgressiveTestStruct(Container):
//     A: ProgressiveList[byte]
//     B: ProgressiveList[uint64]
//     C: ProgressiveList[SmallTestStruct]
//     D: ProgressiveList[ProgressiveList[VarTestStruct]]
//
// Wait - ProgressiveTestStruct in the containers handler is actually a regular Container
// with progressive fields, NOT a ProgressiveContainer.

// Let me check what the spec says...
// From the spec README:
// class ProgressiveTestStruct(Container):
//     A: ProgressiveList[byte]
//     B: ProgressiveList[uint64]
//     C: ProgressiveList[SmallTestStruct]
//     D: ProgressiveList[ProgressiveList[VarTestStruct]]
//
// This is a REGULAR container (not ProgressiveContainer) whose fields happen
// to be progressive types. So it uses normal container merkleization.

use super::containers::VarTestStruct;

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode)]
pub struct ProgressiveTestStruct {
    pub a: ProgressiveList<u8>,
    pub b: ProgressiveList<u64>,
    pub c: ProgressiveList<SmallTestStruct>,
    pub d: ProgressiveList<ProgressiveList<VarTestStruct>>,
}

impl HashTreeRoot for ProgressiveTestStruct {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        // Regular container merkleization (not progressive)
        let field_roots: [Node; 4] = [
            self.a.hash_tree_root(hasher),
            self.b.hash_tree_root(hasher),
            self.c.hash_tree_root(hasher),
            self.d.hash_tree_root(hasher),
        ];
        libssz_merkle::merkleize(hasher, &field_roots, None)
    }
}

// ── ProgressiveBitsStruct ──
// From the containers handler:
// class ProgressiveBitsStruct(Container):
//     A: Bitvector[256]
//     B: Bitlist[256]
//     C: ProgressiveBitlist
//     D: Bitvector[257]
//     E: Bitlist[257]
//     F: ProgressiveBitlist
//     G: Bitvector[1280]
//     H: Bitlist[1280]
//     I: ProgressiveBitlist
//     J: Bitvector[1281]
//     K: Bitlist[1281]
//     L: ProgressiveBitlist
//
// Also a regular Container.

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode)]
pub struct ProgressiveBitsStruct {
    pub a: SszBitvector<256>,
    pub b: SszBitlist<256>,
    pub c: ProgressiveBitlist,
    pub d: SszBitvector<257>,
    pub e: SszBitlist<257>,
    pub f: ProgressiveBitlist,
    pub g: SszBitvector<1280>,
    pub h: SszBitlist<1280>,
    pub i: ProgressiveBitlist,
    pub j: SszBitvector<1281>,
    pub k: SszBitlist<1281>,
    pub l: ProgressiveBitlist,
}

impl HashTreeRoot for ProgressiveBitsStruct {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        let field_roots: [Node; 12] = [
            self.a.hash_tree_root(hasher),
            self.b.hash_tree_root(hasher),
            self.c.hash_tree_root(hasher),
            self.d.hash_tree_root(hasher),
            self.e.hash_tree_root(hasher),
            self.f.hash_tree_root(hasher),
            self.g.hash_tree_root(hasher),
            self.h.hash_tree_root(hasher),
            self.i.hash_tree_root(hasher),
            self.j.hash_tree_root(hasher),
            self.k.hash_tree_root(hasher),
            self.l.hash_tree_root(hasher),
        ];
        libssz_merkle::merkleize(hasher, &field_roots, None)
    }
}
