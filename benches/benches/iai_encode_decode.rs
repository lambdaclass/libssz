use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use libssz::{SszDecode, SszEncode};
use ssz_bench::fixtures::{make_validator, Validator};

#[library_benchmark]
fn iai_encode_validator() -> Vec<u8> {
    let v = make_validator(42);
    v.to_ssz()
}

#[library_benchmark]
fn iai_decode_validator() -> Validator {
    let v = make_validator(42);
    let encoded = v.to_ssz();
    Validator::from_ssz_bytes(&encoded).unwrap()
}

library_benchmark_group!(
    name = encode_decode_group;
    benchmarks = iai_encode_validator, iai_decode_validator
);

main!(library_benchmark_groups = encode_decode_group);
