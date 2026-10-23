use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

const VERSION: &str = "v1.7.0-alpha.13";

/// The three test archives published by the consensus-specs repo.
#[derive(Debug, Clone, Copy)]
pub enum Archive {
    General,
    Mainnet,
    Minimal,
}

impl Archive {
    pub fn dir_name(self) -> &'static str {
        match self {
            Archive::General => "general",
            Archive::Mainnet => "mainnet",
            Archive::Minimal => "minimal",
        }
    }
}

/// Return the root cache directory for spec test vectors.
///
/// Priority:
/// 1. `SPEC_TESTS_DIR` environment variable
/// 2. `<workspace>/target/spec-tests/<version>/`
pub fn cache_dir() -> PathBuf {
    if let Ok(dir) = std::env::var("SPEC_TESTS_DIR") {
        return PathBuf::from(dir);
    }
    workspace_target().join("spec-tests").join(VERSION)
}

/// Path to the workspace `target/` directory.
fn workspace_target() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("spec-tests has a parent dir")
        .join("target")
}

/// Return the path to an extracted archive directory, panicking if not found.
///
/// Run `spec-tests/download-vectors.sh` before running the tests.
pub fn archive_dir(archive: Archive) -> PathBuf {
    let root = cache_dir().join(archive.dir_name());
    let sentinel = root.join(".extracted");
    if !sentinel.exists() {
        panic!(
            "Spec test vectors not found at {}. Run:\n  ./spec-tests/download-vectors.sh",
            root.display()
        );
    }
    root
}

// ── ssz_generic helpers ──

/// Path to an ssz_generic handler directory.
pub fn ssz_generic_handler_path(handler: &str) -> PathBuf {
    archive_dir(Archive::General)
        .join("tests")
        .join("general")
        .join("phase0")
        .join("ssz_generic")
        .join(handler)
}

/// Iterate valid test cases for an ssz_generic handler.
pub fn ssz_generic_valid_cases(handler: &str) -> Vec<(PathBuf, String)> {
    collect_cases(&ssz_generic_handler_path(handler).join("valid"))
}

/// Iterate invalid test cases for an ssz_generic handler.
pub fn ssz_generic_invalid_cases(handler: &str) -> Vec<(PathBuf, String)> {
    collect_cases(&ssz_generic_handler_path(handler).join("invalid"))
}

// ── ssz_static helpers ──

/// Path to an ssz_static type directory for a given network and fork.
pub fn ssz_static_type_path(archive: Archive, fork: &str, type_name: &str) -> PathBuf {
    archive_dir(archive)
        .join("tests")
        .join(archive.dir_name())
        .join(fork)
        .join("ssz_static")
        .join(type_name)
}

/// Iterate test cases for an ssz_static type.
pub fn ssz_static_cases(archive: Archive, fork: &str, type_name: &str) -> Vec<(PathBuf, String)> {
    let type_dir = ssz_static_type_path(archive, fork, type_name);
    let mut cases = Vec::new();
    if !type_dir.exists() {
        return cases;
    }
    if let Ok(suites) = fs::read_dir(&type_dir) {
        for suite in suites.flatten() {
            if suite.file_type().is_ok_and(|t| t.is_dir()) {
                cases.extend(collect_cases(&suite.path()));
            }
        }
    }
    cases
}

// ── ssz-specs fixtures ──

const SSZ_SPECS_VERSION: &str = "v0.1.0";

/// A single case from an `ethereum/ssz-specs` JSON fixture.
///
/// Each fixture file holds a map of test id to case body. `value` and `_info`
/// are ignored: `serialized` and `root` already pin down the behaviour under
/// test, matching how the consensus-specs runners work.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SszSpecsCase {
    /// Test id, filled in from the fixture map key rather than the body.
    #[serde(skip)]
    pub name: String,
    /// Name of the type under test, as spelled in the ssz-specs fillers.
    pub type_name: String,
    /// Hex-encoded canonical encoding of the value.
    pub serialized: String,
    /// Hex-encoded hash tree root, empty for decode-failure cases.
    pub root: String,
    /// Set on decode-failure cases, naming why the input must be rejected.
    #[serde(default)]
    pub rejection_reason: Option<String>,
    /// The bytes to feed the decoder on a decode-failure case.
    #[serde(default)]
    pub raw_bytes: Option<String>,
}

impl SszSpecsCase {
    /// Whether this case expects decoding to fail.
    pub fn is_rejection(&self) -> bool {
        self.rejection_reason.is_some()
    }

    /// The bytes to decode: `rawBytes` when present, else `serialized`.
    pub fn input_bytes(&self) -> Vec<u8> {
        let hex_str = self.raw_bytes.as_deref().unwrap_or(&self.serialized);
        decode_hex(hex_str, &self.name)
    }

    /// The canonical encoding a decoded value must re-encode to.
    pub fn serialized_bytes(&self) -> Vec<u8> {
        decode_hex(&self.serialized, &self.name)
    }

    /// The expected hash tree root. Panics on a decode-failure case, which has
    /// no root to check.
    pub fn expected_root(&self) -> [u8; 32] {
        let bytes = decode_hex(&self.root, &self.name);
        let mut root = [0u8; 32];
        assert_eq!(bytes.len(), 32, "{}: root is not 32 bytes", self.name);
        root.copy_from_slice(&bytes);
        root
    }
}

/// Return the root directory holding the extracted ssz-specs fixtures.
///
/// Priority:
/// 1. `SSZ_SPECS_DIR` environment variable
/// 2. `<workspace>/target/spec-tests/ssz-specs/<version>/`
pub fn ssz_specs_dir() -> PathBuf {
    if let Ok(dir) = std::env::var("SSZ_SPECS_DIR") {
        return PathBuf::from(dir);
    }
    workspace_target()
        .join("spec-tests")
        .join("ssz-specs")
        .join(SSZ_SPECS_VERSION)
}

/// Load every case from an ssz-specs fixture group, sorted by test id.
///
/// `group` is a fixture subdirectory such as `test_basic_types`. Panics if the
/// group is missing or empty, since a silently skipped group would look like a
/// passing test.
pub fn ssz_specs_cases(group: &str) -> Vec<SszSpecsCase> {
    let root = ssz_specs_dir();
    let sentinel = root.join(".extracted");
    if !sentinel.exists() {
        panic!(
            "ssz-specs test vectors not found at {}. Run:\n  ./spec-tests/download-vectors.sh",
            root.display()
        );
    }
    let group_dir = root.join("fixtures").join("ssz").join("ssz").join(group);

    let mut files: Vec<PathBuf> = fs::read_dir(&group_dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {}", group_dir.display(), e))
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "json"))
        .collect();
    files.sort();

    let mut cases = Vec::new();
    for file in &files {
        let content =
            fs::read_to_string(file).unwrap_or_else(|e| panic!("read {}: {}", file.display(), e));
        let fixture: BTreeMap<String, SszSpecsCase> = serde_json::from_str(&content)
            .unwrap_or_else(|e| panic!("parse {}: {}", file.display(), e));
        for (name, mut case) in fixture {
            case.name = name;
            cases.push(case);
        }
    }
    assert!(
        !cases.is_empty(),
        "{}: no fixtures found",
        group_dir.display()
    );
    cases
}

// ── File reading ──

/// Read and snappy-decompress a `.ssz_snappy` file.
pub fn read_ssz_snappy(path: &Path) -> Vec<u8> {
    let compressed = fs::read(path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    let mut decoder = snap::raw::Decoder::new();
    decoder
        .decompress_vec(&compressed)
        .unwrap_or_else(|e| panic!("snappy decompress {}: {}", path.display(), e))
}

/// Parse the `root` field from a `meta.yaml` or `roots.yaml` file.
pub fn parse_root(path: &Path) -> [u8; 32] {
    #[derive(Deserialize)]
    struct Meta {
        root: String,
    }
    let content =
        fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    let meta: Meta = serde_yaml::from_str(&content)
        .unwrap_or_else(|e| panic!("parse {}: {}", path.display(), e));
    let bytes = decode_hex(&meta.root, &path.display().to_string());
    let mut root = [0u8; 32];
    root.copy_from_slice(&bytes);
    root
}

/// Decode a hex string, with or without a `0x` prefix.
fn decode_hex(hex_str: &str, context: &str) -> Vec<u8> {
    let stripped = hex_str.strip_prefix("0x").unwrap_or(hex_str);
    hex::decode(stripped).unwrap_or_else(|e| panic!("hex decode in {context}: {e}"))
}

/// Read a scalar YAML value (for boolean/uint test cases).
pub fn read_yaml_value(path: &Path) -> serde_yaml::Value {
    let content =
        fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    serde_yaml::from_str(&content).unwrap_or_else(|e| panic!("parse {}: {}", path.display(), e))
}

// ── Internal ──

fn collect_cases(dir: &Path) -> Vec<(PathBuf, String)> {
    let mut cases = Vec::new();
    if !dir.exists() {
        return cases;
    }
    let mut entries: Vec<_> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {}", dir.display(), e))
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_ok_and(|t| t.is_dir()))
        .collect();
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let name = entry.file_name().to_string_lossy().into_owned();
        cases.push((entry.path(), name));
    }
    cases
}
