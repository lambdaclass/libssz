use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_types::{SszBitlist, SszBitvector, SszList, SszVector};

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SingleFieldTestStruct {
    pub a: u8,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SmallTestStruct {
    pub a: u16,
    pub b: u16,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct FixedTestStruct {
    pub a: u8,
    pub b: u64,
    pub c: u32,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct VarTestStruct {
    pub a: u16,
    pub b: SszList<u16, 1024>,
    pub c: u8,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ComplexTestStruct {
    pub a: u16,
    pub b: SszList<u16, 128>,
    pub c: u8,
    pub d: SszList<u8, 256>,
    pub e: VarTestStruct,
    pub f: SszVector<FixedTestStruct, 4>,
    pub g: SszVector<VarTestStruct, 2>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BitsStruct {
    pub a: SszBitlist<5>,
    pub b: SszBitvector<2>,
    pub c: SszBitvector<1>,
    pub d: SszBitlist<6>,
    pub e: SszBitvector<8>,
}
