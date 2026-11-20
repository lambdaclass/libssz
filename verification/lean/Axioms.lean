import Libssz

/-! The main theorems depend only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`): no `sorry` and no `axiom` from
`FunsExternal.lean` (in libssz it only defines `Vec::reserve`, and none of these
theorems uses it). -/

open Libssz.Proofs Libssz.Proofs

#print axioms Bool.ssz_append.spec
#print axioms Bool.from_ssz_bytes.spec
#print axioms U8.ssz_append.spec
#print axioms U8.from_ssz_bytes.spec
#print axioms U16.ssz_append.spec
#print axioms U16.from_ssz_bytes.spec
#print axioms U32.ssz_append.spec
#print axioms U32.from_ssz_bytes.spec
#print axioms U64.ssz_append.spec
#print axioms U64.from_ssz_bytes.spec
#print axioms U128.ssz_append.spec
#print axioms U128.from_ssz_bytes.spec

/-! Lists of integers and `[u8; N]`. -/

#print axioms U8.decode_loop.spec
#print axioms U8.encode_loop.spec
#print axioms U8.decode_list.spec
#print axioms U8.vec_from_ssz_bytes.spec
#print axioms U8.encode_list.spec
#print axioms U16.decode_loop.spec
#print axioms U16.encode_loop.spec
#print axioms U16.decode_list.spec
#print axioms U16.vec_from_ssz_bytes.spec
#print axioms U16.encode_list.spec
#print axioms U32.decode_loop.spec
#print axioms U32.encode_loop.spec
#print axioms U32.decode_list.spec
#print axioms U32.vec_from_ssz_bytes.spec
#print axioms U32.encode_list.spec
#print axioms U64.decode_loop.spec
#print axioms U64.encode_loop.spec
#print axioms U64.decode_list.spec
#print axioms U64.vec_from_ssz_bytes.spec
#print axioms U64.encode_list.spec
#print axioms U128.decode_loop.spec
#print axioms U128.encode_loop.spec
#print axioms U128.decode_list.spec
#print axioms U128.vec_from_ssz_bytes.spec
#print axioms U128.encode_list.spec
#print axioms ArrayU8N.from_ssz_bytes.spec
#print axioms ArrayU8N.ssz_append.spec
#print axioms U64.decode_list_diverges
#print axioms decode_byte_array_vec_loop.spec
#print axioms decode_byte_array_vec.spec
#print axioms ArrayU8N.encode_loop.spec
#print axioms ArrayU8N.decode_list.spec
#print axioms ArrayU8N.vec_from_ssz_bytes.spec
#print axioms ArrayU8N.encode_list.spec
#print axioms Bool.decode_loop.spec
#print axioms Bool.decode_list.spec
#print axioms Bool.vec_from_ssz_bytes.spec
#print axioms Bool.ssz_append.bytes_spec
#print axioms Bool.encode_loop.spec
#print axioms Bool.encode_list.spec

/-! Lists of variable-size items. -/

#print axioms read_offset.spec
#print axioms read_item_offsets_loop.spec
#print axioms decode_items_loop.spec
#print axioms decode_var_items.spec
#print axioms decode_var_list.spec
#print axioms VecU8.vec_from_ssz_bytes.spec
#print axioms VecVecU8.vec_from_ssz_bytes.spec
#print axioms offsetSpansFrom_ok
#print axioms offsetSpansFrom_err
#print axioms chainOK_iff
#print axioms slices_eq

/-! Encoding lists of variable-size items. -/

#print axioms encode_var_loop.spec
#print axioms encode_var_items.spec
#print axioms vec_var_ssz_append.spec
#print axioms encode_var_list.spec
#print axioms encode_var_list.agrees
#print axioms encode_var_list.diverges
#print axioms VecVecU8.encode.agrees
#print axioms VecVecU8.encode.diverges
#print axioms serialize_list_var
#print axioms uintBytes_mod32

/-! Containers (`ContainerEncoder`, `ContainerDecoder`) and the example container. -/

#print axioms copy_within.spec
#print axioms with_capacity.spec
#print axioms append_fixed.spec
#print axioms append_variable.spec
#print axioms finalize.spec
#print axioms new.spec
#print axioms decode_fixed.spec
#print axioms read_first_offset.spec
#print axioms read_next_offset.spec
#print axioms decode_variable.spec
#print axioms eth_decode
#print axioms eth_encode
#print axioms Example.ssz_append.bytes_spec
#print axioms Example.encode.agrees
#print axioms Example.encode.diverges
#print axioms Example.from_ssz_bytes.spec

/-! The per-field steps of `ssz-derive`. -/

#print axioms decode_fixed_part.fixed_spec
#print axioms decode_fixed_part.first_spec
#print axioms decode_fixed_part.next_spec
#print axioms decode_variable_part.fixed_spec
#print axioms decode_variable_part.var_spec

/-! Fixed-size containers of the consensus layer (phase0). -/

#print axioms eth_decode_fixed
#print axioms eth_encode_fixed
#print axioms Checkpoint.from_ssz_bytes.spec
#print axioms Checkpoint.encode.agrees
#print axioms Fork.from_ssz_bytes.spec
#print axioms Fork.encode.agrees
#print axioms BeaconBlockHeader.from_ssz_bytes.spec
#print axioms BeaconBlockHeader.encode.agrees
#print axioms Validator.from_ssz_bytes.spec
#print axioms Validator.encode.agrees
#print axioms AttestationData.from_ssz_bytes.spec
#print axioms AttestationData.encode.agrees

/-! The whole libssz model uses no axioms either: for example, the `Vec<T>` instances
(which pull in lists of fixed- and variable-size items, offsets and `decode_list_with_max`)
and the container helpers. In the Aeneas translation of libssz before the verification
rewrite, the same items are `axiom`s. -/

open libssz in
#print axioms alloc.vec.Vec.Insts.LibsszDecodeSszDecode
open libssz in
#print axioms alloc.vec.Vec.Insts.LibsszEncodeSszEncode
open libssz in
#print axioms decode.ContainerDecoder.read_variable_offset
open libssz in
#print axioms encode.ContainerEncoder.append_fixed
