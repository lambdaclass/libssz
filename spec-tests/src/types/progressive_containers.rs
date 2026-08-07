use libssz_derive::{HashTreeRoot as HashTreeRootDerive, SszDecode, SszEncode};
use libssz_merkle::{HashTreeRoot, Node, Sha256Hasher};
use libssz_types::{ProgressiveBitlist, ProgressiveList, SszBitlist, SszBitvector, SszList};

use super::containers::{SmallTestStruct, VarTestStruct};

// The `ProgressiveContainer` types below carry their `active_fields` in the
// derive attribute; the two plain `Container` types at the bottom of the file
// merkleize normally and keep hand-written impls.

// ── ProgressiveSingleFieldContainerTestStruct ──
// active_fields = [1]

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container)]
pub struct ProgressiveSingleFieldContainerTestStruct {
    pub a: u8,
}

// ── ProgressiveSingleListContainerTestStruct ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [0, 0, 0, 0, 1])]
pub struct ProgressiveSingleListContainerTestStruct {
    pub c: ProgressiveBitlist,
}

// ── ProgressiveVarTestStruct ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [1, 0, 1, 0, 1])]
pub struct ProgressiveVarTestStruct {
    pub a: u8,
    pub b: SszList<u16, 123>,
    pub c: ProgressiveBitlist,
}

// ── ProgressiveComplexTestStruct ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(
    progressive_container,
    active_fields = [1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1]
)]
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

// ── ProgressiveTestStruct ──
//
// From the `containers` handler, not `progressive_containers`: a regular
// `Container` whose fields happen to be progressive types, so it merkleizes as
// an ordinary container.

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
//
// Also a regular `Container`, pairing each bounded bit type with a
// `ProgressiveBitlist` across the 256/257 and 1280/1281 chunk boundaries.

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
