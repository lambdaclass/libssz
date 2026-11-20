import Libssz

/-! The main theorems of libssz depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`): no `sorry` and no `axiom`.

`FunsExternal.lean` has seven handwritten definitions, and none of them is an `axiom`:
`Vec::reserve` (the identity) and the six models in `Libssz/StdModel.lean` (`as_chunks`,
`as_flattened`, `into_flattened`, `into_boxed_slice`, `Iterator::map` and the `next` of
`Map`). That is why they do not show up in this list. Still, one has to trust that they say
what `core` and `alloc` do: they are part of the trusted base.

The SHA-NI core of `ssz-merkle` (`Libssz/Merkle/`) adds ten more handwritten definitions, also
not `axiom`s: the type `__m128i`, eight intrinsics from `core::arch::x86_64` (the models in
`Libssz/Merkle/Intrinsics.lean`) and `black_box` (the identity). They are also part of the
trusted base: one has to trust that each model says what the processor instruction does.

The AArch64 core (`Libssz/MerkleNeon/`) adds nine more, also not `axiom`s: the type
`uint32x4_t` and eight intrinsics from `core::arch::aarch64` (the models in
`Libssz/MerkleNeon/Intrinsics.lean`). `black_box` is the same as in the x86 extraction. -/

open Libssz.Proofs

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

/-! `ssz_write_fixed`: the in-place write that containers use. -/

#print axioms Bool.ssz_write_fixed.spec
#print axioms U8.ssz_write_fixed.spec
#print axioms U16.ssz_write_fixed.spec
#print axioms U32.ssz_write_fixed.spec
#print axioms U64.ssz_write_fixed.spec
#print axioms U128.ssz_write_fixed.spec
#print axioms ArrayU8N.ssz_write_fixed.spec

/-! Lists of integers and `[u8; N]`. -/

#print axioms U8.decode_list.spec
#print axioms U8.vec_from_ssz_bytes.spec
#print axioms U8.encode_list.spec
#print axioms vec_to_ssz_default
#print axioms U8.vec_to_ssz.spec
#print axioms U16.from_le_chunks.spec
#print axioms U16.append_le_short.spec
#print axioms U16.append_le_blocks.spec
#print axioms U16.append_fixed_slice.spec
#print axioms U16.fixed_slice_to_vec.spec
#print axioms U16.vec_to_ssz.spec
#print axioms U16.decode_list.spec
#print axioms U16.vec_from_ssz_bytes.spec
#print axioms U16.encode_list.spec
#print axioms U32.from_le_chunks.spec
#print axioms U32.append_le_short.spec
#print axioms U32.append_le_blocks.spec
#print axioms U32.append_fixed_slice.spec
#print axioms U32.fixed_slice_to_vec.spec
#print axioms U32.vec_to_ssz.spec
#print axioms U32.decode_list.spec
#print axioms U32.vec_from_ssz_bytes.spec
#print axioms U32.encode_list.spec
#print axioms U64.from_le_chunks.spec
#print axioms U64.append_le_short.spec
#print axioms U64.append_le_blocks.spec
#print axioms U64.append_fixed_slice.spec
#print axioms U64.fixed_slice_to_vec.spec
#print axioms U64.vec_to_ssz.spec
#print axioms U64.decode_list.spec
#print axioms U64.vec_from_ssz_bytes.spec
#print axioms U64.encode_list.spec
#print axioms U128.from_le_chunks.spec
#print axioms U128.append_le_short.spec
#print axioms U128.append_le_blocks.spec
#print axioms U128.append_fixed_slice.spec
#print axioms U128.fixed_slice_to_vec.spec
#print axioms U128.vec_to_ssz.spec
#print axioms U128.decode_list.spec
#print axioms U128.vec_from_ssz_bytes.spec
#print axioms U128.encode_list.spec
#print axioms ArrayU8N.from_ssz_bytes.spec
#print axioms ArrayU8N.ssz_append.spec
#print axioms U64.decode_list_diverges
#print axioms as_chunks_spec
#print axioms as_flattened_spec
#print axioms into_flattened_spec
#print axioms collect_map_slice
#print axioms decode_byte_array_vec.spec
#print axioms ArrayU8N.decode_list.spec
#print axioms ArrayU8N.vec_from_ssz_bytes.spec
#print axioms ArrayU8N.encode_list.spec
#print axioms ArrayU8N.vec_to_ssz.spec
#print axioms Bool.decode_loop.spec
#print axioms Bool.decode_list.spec
#print axioms Bool.vec_from_ssz_bytes.spec
#print axioms Bool.ssz_append.bytes_spec
#print axioms Bool.encode_loop.spec
#print axioms Bool.encode_list.spec
#print axioms Bool.vec_to_ssz.spec

/-! Decoding lists of variable-size items. -/

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
#print axioms append_fixed.spec_append
#print axioms append_fixed.spec_write
#print axioms append_variable.spec
#print axioms finalize.spec
#print axioms new.spec
#print axioms offset_at.spec
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

/-! Fixed-size consensus-layer containers (phase0). -/

#print axioms eth_decode_fixed
#print axioms eth_encode_fixed
#print axioms append_via_write_fixed
#print axioms Checkpoint.from_ssz_bytes.spec
#print axioms Checkpoint.ssz_write_fixed.bytes_spec
#print axioms Checkpoint.encode.agrees
#print axioms Fork.from_ssz_bytes.spec
#print axioms Fork.ssz_write_fixed.bytes_spec
#print axioms Fork.encode.agrees
#print axioms BeaconBlockHeader.from_ssz_bytes.spec
#print axioms BeaconBlockHeader.ssz_write_fixed.bytes_spec
#print axioms BeaconBlockHeader.encode.agrees
#print axioms Validator.from_ssz_bytes.spec
#print axioms Validator.ssz_write_fixed.bytes_spec
#print axioms Validator.encode.agrees
#print axioms AttestationData.from_ssz_bytes.spec
#print axioms AttestationData.ssz_write_fixed.bytes_spec
#print axioms AttestationData.encode.agrees

/-! The whole libssz model uses no axioms either: for example, the `Vec<T>` instances (which
pull in lists of fixed-size and variable-size items, offsets and `decode_list_with_max`) and
the container helpers. In the model of libssz before the verification rewrite, the same items
were `axiom`s. -/

open libssz_codec in
#print axioms alloc.vec.Vec.Insts.LibsszDecodeSszDecode
open libssz_codec in
#print axioms alloc.vec.Vec.Insts.LibsszEncodeSszEncode
open libssz_codec in
#print axioms decode.ContainerDecoder.read_variable_offset
open libssz_codec in
#print axioms encode.ContainerEncoder.append_fixed
open libssz_codec in
#print axioms decode.ContainerDecoder.offset_at

/-! The SHA-NI core of merkleization (`ssz-merkle/src/shani.rs`): hashing a pair of nodes,
two interleaved pairs and a whole tree layer gives the same as EthLib's `combine` (SHA-256 of
the 64 bytes). -/

open Libssz.Merkle in
#print axioms hash_block
open Libssz.Merkle in
#print axioms hash_pair.spec
open Libssz.Merkle in
#print axioms hash_pairs_x2.spec
open Libssz.Merkle in
#print axioms hash_pairs_x4_loop0.spec
open Libssz.Merkle in
#print axioms hash_pairs_x4_loop1.spec
open Libssz.Merkle in
#print axioms hash_pairs_x4.spec
open Libssz.Merkle in
#print axioms set4_getElem?
open Libssz.Merkle in
#print axioms src_node
open Libssz.Merkle in
#print axioms hash_layer_loop.spec
open Libssz.Merkle in
#print axioms hash_layer.spec
open libssz_merkle in
#print axioms shani.hash_layer

/-! The merkleization tree (`ssz-merkle/src/lib.rs`), for any hasher that satisfies `Lawful`:
the SHA-NI core satisfies it (`shani_lawful`), and so do the trait's default methods if
`hash_pair` computes `combine` (`Lawful.of_hash_pair`). The `ZERO_HASHES` table is computed by
Lean's kernel (`zeroRow_eq`). `pack` uses `as_chunks`, with the same model as the codec. -/

open Libssz.Merkle in
#print axioms shani_lawful
open Libssz.Merkle in
#print axioms Lawful.of_hash_pair
open Libssz.Merkle in
#print axioms layer.spec
open Libssz.Merkle in
#print axioms layer_in_place.spec
open Libssz.Merkle in
#print axioms zeroRow_eq
open Libssz.Merkle in
#print axioms ceil_log2.spec
open Libssz.Merkle in
#print axioms tree_depth.spec
open Libssz.Merkle in
#print axioms parentOf_subtreeAt
open Libssz.Merkle in
#print axioms real_root_loop.spec
open Libssz.Merkle in
#print axioms real_root.spec
open Libssz.Merkle in
#print axioms virtual_root.spec
open Libssz.Merkle in
#print axioms real_root_on_stack.spec
open Libssz.Merkle in
#print axioms merkleize.spec
open Libssz.Merkle in
#print axioms merkleize_in_place.spec
open Libssz.Merkle in
#print axioms mix_in_length.spec
open Libssz.Merkle in
#print axioms mix_in_selector.spec
open Libssz.Merkle in
#print axioms pack.spec
open Libssz.Merkle in
#print axioms pack_bits.spec
open Libssz.Merkle in
#print axioms merkleize_progressive_inner.spec
open Libssz.Merkle in
#print axioms merkleize_progressive.spec

/-! The `hash_tree_root` of each type: `bool`, `u8`…`u128`, `[u8; N]` and the containers in
`ssz-merkle/src/verif_example.rs`, with the code that `#[derive(HashTreeRoot)]` generates.
All of them are EthLib's `hashTreeRoot` with the same type descriptor used for the codec. -/

open Libssz.Merkle in
#print axioms hashTreeRoot_leaf
open Libssz.Merkle in
#print axioms hashTreeRoot_byteVector
open Libssz.Merkle in
#print axioms hashTreeRoot_container
open Libssz.Merkle in
#print axioms Bool.hash_tree_root.spec
open Libssz.Merkle in
#print axioms U8.hash_tree_root.spec
open Libssz.Merkle in
#print axioms U16.hash_tree_root.spec
open Libssz.Merkle in
#print axioms U32.hash_tree_root.spec
open Libssz.Merkle in
#print axioms U64.hash_tree_root.spec
open Libssz.Merkle in
#print axioms U128.hash_tree_root.spec
open Libssz.Merkle in
#print axioms ArrayU8N.hash_tree_root.spec
open Libssz.Merkle in
#print axioms Checkpoint.hash_tree_root.spec
open Libssz.Merkle in
#print axioms Fork.hash_tree_root.spec
open Libssz.Merkle in
#print axioms BeaconBlockHeader.hash_tree_root.spec
open Libssz.Merkle in
#print axioms Validator.hash_tree_root.spec
open Libssz.Merkle in
#print axioms AttestationData.hash_tree_root.spec
open Libssz.Merkle in
#print axioms Uints.hash_tree_root.spec

/-! `Vec<T>`: `Vec<u64>` is EthLib's `List[uint64, len]`, through the link with the codec
(`<u64 as SszEncode>::ssz_fixed_slice_to_vec`). And the difference from the specification for
`Vec<[u8; 4]>` (`VecU8x4.diverges`; see the divergences in `README.md`). -/

open Libssz.Merkle in
#print axioms hashTreeRoot_list_basic
open Libssz.Merkle in
#print axioms hashTreeRoot_list_composite
open Libssz.Merkle in
#print axioms basic_items_bytes_u64.spec
open Libssz.Merkle in
#print axioms VecU64.hash_tree_root.spec
open Libssz.Merkle in
#print axioms basic_items_bytes_u8n.spec
open Libssz.Merkle in
#print axioms vec_basic_root
open Libssz.Merkle in
#print axioms VecU8x4.diverges

/-! Lists of composite items: the item roots in batches (`merkleize_groups`,
`hash_tree_roots` and the rows, `Rows`), and `Vec<T>` with composite items (for example
`Vec<[u8; 48]>`). -/

open Libssz.Merkle in
#print axioms subtreeAt_chunks_congr
open Libssz.Merkle in
#print axioms subtreeAt_append_zeros
open Libssz.Merkle in
#print axioms parentOf_subtreeAt_pair
open Libssz.Merkle in
#print axioms copy_from_slice_eq
open Libssz.Merkle in
#print axioms forall₂_of_getElem?
open Libssz.Merkle in
#print axioms mapM_of_forall₂
open Libssz.Merkle in
#print axioms merkleize_groups_loop.spec
open Libssz.Merkle in
#print axioms merkleize_groups.spec
open Libssz.Merkle in
#print axioms Rows.of_default
open Libssz.Merkle in
#print axioms bytes_zeroNode
open Libssz.Merkle in
#print axioms chunksOf_append_zeros
open Libssz.Merkle in
#print axioms container_row_root
open Libssz.Merkle in
#print axioms list_len2
open Libssz.Merkle in
#print axioms list_len4
open Libssz.Merkle in
#print axioms list_len8
open Libssz.Merkle in
#print axioms hash_tree_roots_loop0_loop0.spec
open Libssz.Merkle in
#print axioms hash_tree_roots_loop0.spec
open Libssz.Merkle in
#print axioms hash_tree_roots.spec
open Libssz.Merkle in
#print axioms ArrayU8N.rows
open Libssz.Merkle in
#print axioms Validator.rows
open Libssz.Merkle in
#print axioms vec_composite_root
open Libssz.Merkle in
#print axioms VecU8N.hash_tree_root.spec
open Libssz.Merkle in
#print axioms VecValidator.hash_tree_root.spec

/-! `SszList` and `SszVector` (crate `ssz-types`, linked with the tree and the codec), and the
containers in `ssz-types/src/verif_example.rs`. -/

open Libssz.SszTypes in
#print axioms hashTreeRoot_vector_basic
open Libssz.SszTypes in
#print axioms hashTreeRoot_vector_composite
open Libssz.SszTypes in
#print axioms concatParts_size32
open Libssz.SszTypes in
#print axioms packBytes_concat32
open Libssz.SszTypes in
#print axioms hashTreeRoot_bytes32
open Libssz.SszTypes in
#print axioms mapM_bytes32
open Libssz.SszTypes in
#print axioms basic_items_bytes_eq
open Libssz.SszTypes in
#print axioms roots_forall₂
open Libssz.SszTypes in
#print axioms SszList.composite_root
open Libssz.SszTypes in
#print axioms SszVector.composite_root
open Libssz.SszTypes in
#print axioms pack_le_cap
open Libssz.SszTypes in
#print axioms SszList.basic_rust
open Libssz.SszTypes in
#print axioms SszVector.basic_rust
open Libssz.SszTypes in
#print axioms serializeEach_u64
open Libssz.SszTypes in
#print axioms bytes_size32
open Libssz.SszTypes in
#print axioms SszListU64.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SszVectorU64.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms bytes_map_size32
open Libssz.SszTypes in
#print axioms SszListBytes32.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SszVectorBytes32.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms u8n_not_basic
open Libssz.SszTypes in
#print axioms SszListU8N.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SszVectorU8N.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SszListValidator.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SszVectorU8x4.diverges
open Libssz.SszTypes in
#print axioms IndexedAttestation.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms HistoricalBatch.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms DepositData.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms Deposit.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms Deposit.rows
open Libssz.SszTypes in
#print axioms SyncCommittee.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms StateLists.hash_tree_root.spec

/-! `ExecutionPayload` (capella): `SszList<u8>` and `SszVector<u8>` as `ByteList` and
`ByteVector`, the list of lists `transactions` and the list of containers `withdrawals`. -/

open Libssz.SszTypes in
#print axioms basic_items_bytes_u8.spec
open Libssz.SszTypes in
#print axioms hashTreeRoot_byteList
open Libssz.SszTypes in
#print axioms SszListU8.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SszVectorU8.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SszListU8.rows
open Libssz.SszTypes in
#print axioms SszListByteList.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms leValue_lt
open Libssz.SszTypes in
#print axioms uintBytes_leValue
open Libssz.SszTypes in
#print axioms hashTreeRoot_uint256
open Libssz.SszTypes in
#print axioms Withdrawal.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms Withdrawal.rows
open Libssz.SszTypes in
#print axioms ExecutionPayload.hash_tree_root.spec

/-! Bitfields (`SszBitvector`, `SszBitlist`): `hash_tree_root`, encode and decode, with the
`SmallVec` model (`Libssz/SszTypes/SmallVecModel.lean`, definitions, not axioms), and the
containers with bitfields. -/

open Libssz.SszTypes in
#print axioms Canon.size
open Libssz.SszTypes in
#print axioms hashTreeRoot_bitVector
open Libssz.SszTypes in
#print axioms hashTreeRoot_bitList
open Libssz.SszTypes in
#print axioms pack_bits_canon
open Libssz.SszTypes in
#print axioms chunks_bits_le
open Libssz.SszTypes in
#print axioms SszBitvector.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SszBitlist.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms mask_nat
open Libssz.SszTypes in
#print axioms SszBitvector.ssz_append.spec
open Libssz.SszTypes in
#print axioms last_byte
open Libssz.SszTypes in
#print axioms shift_ne_zero
open Libssz.SszTypes in
#print axioms validate_excess_bits.spec
open Libssz.SszTypes in
#print axioms canon_of_bitVector
open Libssz.SszTypes in
#print axioms SszBitvector.from_ssz_bytes.spec
open Libssz.SszTypes in
#print axioms bit_testBit
open Libssz.SszTypes in
#print axioms testBit_byte_high
open Libssz.SszTypes in
#print axioms byte_eq_of_testBit
open Libssz.SszTypes in
#print axioms unpackBits_get
open Libssz.SszTypes in
#print axioms packBits_testBit
open Libssz.SszTypes in
#print axioms Canon.high
open Libssz.SszTypes in
#print axioms packBitsDelimited_eq
open Libssz.SszTypes in
#print axioms one_shl_u8
open Libssz.SszTypes in
#print axioms getElem_eq_of
open Libssz.SszTypes in
#print axioms bytes_getElem
open Libssz.SszTypes in
#print axioms pad_get
open Libssz.SszTypes in
#print axioms SszBitlist.ssz_append.spec
open Libssz.SszTypes in
#print axioms testBit_log
open Libssz.SszTypes in
#print axioms testBit_above_log
open Libssz.SszTypes in
#print axioms log_lt_8
open Libssz.SszTypes in
#print axioms highestBit_log
open Libssz.SszTypes in
#print axioms mask_above_zero
open Libssz.SszTypes in
#print axioms clear_bit_testBit
open Libssz.SszTypes in
#print axioms unpackBits_congr
open Libssz.SszTypes in
#print axioms bytes_getD
open Libssz.SszTypes in
#print axioms deserialize_bitList
open Libssz.SszTypes in
#print axioms SszBitlist.from_ssz_bytes.spec
open Libssz.SszTypes in
#print axioms Attestation.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms Attestation.rows
open Libssz.SszTypes in
#print axioms PendingAttestation.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms PendingAttestation.rows
open Libssz.SszTypes in
#print axioms SyncAggregate.hash_tree_root.spec

/-! `BeaconBlockBody`, `BeaconBlock` and `BeaconState` (phase0). -/

open Libssz.SszTypes in
#print axioms Eth1Data.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms Eth1Data.rows
open Libssz.SszTypes in
#print axioms SignedBeaconBlockHeader.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms ProposerSlashing.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms ProposerSlashing.rows
open Libssz.SszTypes in
#print axioms AttesterSlashing.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms AttesterSlashing.rows
open Libssz.SszTypes in
#print axioms VoluntaryExit.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SignedVoluntaryExit.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms SignedVoluntaryExit.rows
open Libssz.SszTypes in
#print axioms BeaconBlockBody.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms BeaconBlock.hash_tree_root.spec
open Libssz.SszTypes in
#print axioms BeaconState.hash_tree_root.spec

/-! The AArch64 core (`ssz-merkle/src/neon.rs`): the Arm instructions are EthLib's rounds and
schedule (`MerkleNeon/Proofs/Rounds.lean`); one pair, two, four and a whole layer give the same
as EthLib's `combine`; the hasher satisfies `Lawful`, so the tree and the type roots hold
(two examples: `merkleize_neon` and `beacon_state_neon`). -/

open Libssz.MerkleNeon in
#print axioms hashRound_laneRound
open Libssz.MerkleNeon in
#print axioms sha256h_quadStep
open Libssz.MerkleNeon in
#print axioms sha256h2_quadStep
open Libssz.MerkleNeon in
#print axioms su_next4
open Libssz.MerkleNeon in
#print axioms words_eq
open Libssz.MerkleNeon in
#print axioms K_row
open Libssz.MerkleNeon in
#print axioms PAD_WK_row
open Libssz.MerkleNeon in
#print axioms scheduled_quad.spec
open Libssz.MerkleNeon in
#print axioms finish_block.spec
open Libssz.MerkleNeon in
#print axioms digest.spec
open Libssz.MerkleNeon in
#print axioms hash_pair.spec
open Libssz.MerkleNeon in
#print axioms hash_pairs_x2.spec
open Libssz.MerkleNeon in
#print axioms hash_pairs_x4.spec
open Libssz.MerkleNeon in
#print axioms hash_layer_loop.spec
open Libssz.MerkleNeon in
#print axioms hash_layer.spec
open Libssz.MerkleNeon in
#print axioms neon_lawful
open Libssz.MerkleNeon in
#print axioms merkleize_neon
open Libssz.MerkleNeon in
#print axioms beacon_state_neon
