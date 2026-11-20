import Lake
open Lake DSL

-- Aeneas' Lean library: the model of Rust (`Result`, `U64`, `Slice`, `Vec`, the `step` tactics).
-- Pinned to the Aeneas commit that generated the model in `Libssz/**/Code/`.
require aeneas from git "https://github.com/AeneasVerif/aeneas.git" @
  "5a392f4b80a4d0d05abc240eb2a7fa70622a9a35" / "backends/lean"

-- The specification: EthLib's SSZ serialization and Merkleization.
require EthLib from git "https://github.com/ethereum/EthLib.git" @
  "cdd16763847e2a6cf52f01128cc1ce618a8c516c"

package «libssz-verification» where
  leanOptions := #[⟨`maxHeartbeats, (1000000 : Nat)⟩]

@[default_target]
lean_lib «Libssz» where
  roots := #[`Libssz]
  requiresModuleSystem := true


/-- Runs the Lean model of libssz and EthLib's specification on given inputs; used by the
differential test in `../difftest`. -/
lean_exe «difftest» where
  root := `DiffTest
