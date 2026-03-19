.PHONY: ci fmt clippy build test test-alloc doc no-std-check coverage audit bench bench-baseline bench-compare fuzz fuzz-quick download-spec-tests spec-tests

ci: fmt clippy build test test-alloc doc no-std-check coverage audit spec-tests ## Run the full CI pipeline locally

fmt: ## Check formatting
	cargo fmt --all -- --check

clippy: ## Run clippy with warnings as errors
	cargo clippy --workspace --all-targets --exclude spec-tests -- -D warnings

build: ## Build all workspace targets
	cargo build --workspace --all-targets --exclude spec-tests

test: ## Run tests with default features
	cargo test --workspace --exclude spec-tests

test-alloc: ## Run tests with alloc-only (no-std) features
	cargo test --workspace --exclude spec-tests --no-default-features --features alloc

doc: ## Check documentation builds without warnings
	RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps --exclude spec-tests

no-std-check: ## Verify no_std compilation on thumbv7m-none-eabi
	cargo check -p libssz -p libssz-types -p libssz-merkle --target thumbv7m-none-eabi --no-default-features --features alloc

coverage: ## Generate code coverage report (requires cargo-llvm-cov)
	cargo llvm-cov --workspace --exclude spec-tests --lcov --output-path lcov.info --fail-under-lines 70

download-spec-tests: ## Download consensus spec test vectors (~1.25GB)
	./spec-tests/download-vectors.sh

spec-tests: download-spec-tests ## Run consensus spec tests (downloads vectors if needed)
	cargo test -p spec-tests

audit: ## Audit dependencies for known vulnerabilities (requires cargo-audit)
	cargo audit

bench: ## Run criterion benchmarks
	cargo bench --workspace --bench encode --bench decode --bench hash_tree_root --bench merkle --bench differential

bench-baseline: ## Save benchmark baseline (usage: make bench-baseline BASELINE=main)
	cargo bench --workspace --bench encode --bench decode --bench hash_tree_root --bench merkle --bench differential -- --save-baseline $(BASELINE)

bench-compare: ## Compare against saved baseline (usage: make bench-compare BASELINE=main)
	cargo bench --workspace --bench encode --bench decode --bench hash_tree_root --bench merkle --bench differential -- --baseline $(BASELINE)

fuzz: ## Run all fuzz targets for 60s each (requires cargo-fuzz + nightly)
	cd fuzz && cargo +nightly fuzz run decode_arbitrary -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run roundtrip -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run diff_encode -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run diff_hash_tree_root -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run hash_tree_root_fuzz -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run merkle_primitives -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run union_decode -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run diff_decode -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run variable_container -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run nested_types -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run diff_htr_container -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run union_htr -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run transparent -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run all_variable -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run wide_union -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run deep_nesting -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run many_fields -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run offset_adversarial -- -max_total_time=60
	cd fuzz && cargo +nightly fuzz run construction_api -- -max_total_time=60

fuzz-quick: ## Quick fuzz smoke test (10s each)
	@for target in $$(cd fuzz && cargo +nightly fuzz list 2>/dev/null); do \
		echo "Fuzzing $$target for 10s..."; \
		(cd fuzz && cargo +nightly fuzz run $$target -- -max_total_time=10) || exit 1; \
	done

help: ## Show this help
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-16s\033[0m %s\n", $$1, $$2}'
