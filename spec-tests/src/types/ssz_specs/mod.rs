//! Types from the `ethereum/ssz-specs` test vector fillers.
//!
//! Split by fixture group, mirroring `tests/fillers/ssz/` in that repo, since
//! the same type name can mean different things in different groups:
//! `SampleShapeContainer` is a container around a union in one group and a
//! container around a progressive container in another.

pub mod compatible_unions;
pub mod progressive_containers;
pub mod progressive_types;
