# libssz (Rust) ≡ EthLib (Lean), via Charon + Aeneas: the codec of the `ssz` crate.
#
#   make extract   regenerates lean/Libssz/Code/ from ../crates/ssz
#   make proofs    builds the proofs and prints the axioms of the main theorems
#   make difftest  differential tests: libssz before the rewrite vs libssz now, and the Lean
#                  model and EthLib against the Rust code
#
# Tools: Charon and Aeneas at the commits in README.md, and Lean through elan.

CHARON ?= charon
AENEAS ?= aeneas

CRATE  := ../crates/ssz
DERIVE := $(wildcard ../crates/ssz-derive/src/*.rs)
LLBC   := $(abspath libssz.llbc)
CODE   := lean/Libssz/Code

.PHONY: extract proofs difftest clean

$(LLBC): $(wildcard $(CRATE)/src/*.rs) $(CRATE)/Cargo.toml $(DERIVE) Makefile
	cd $(CRATE) && $(CHARON) cargo --preset=aeneas --dest-file=$(LLBC) \
	  -- --features verif-example --target x86_64-unknown-linux-gnu

extract: $(LLBC)
	$(AENEAS) -backend lean $(LLBC) -dest lean -subdir /Libssz/Code -split-files \
	  -namespace libssz -loops-to-rec -all-computable -filter-trait-methods
	python3 -I scripts/complete_externals_codec.py \
	  $(CODE)/FunsExternal_Template.lean $(CODE)/FunsExternal.lean
	rm -f $(CODE)/FunsExternal_Template.lean

proofs:
	cd lean && lake build && lake env lean Axioms.lean

difftest:
	cd lean && lake build difftest
	cd difftest && cargo test --release -- --nocapture --test-threads 1

clean:
	rm -f $(LLBC)
