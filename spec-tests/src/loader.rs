use serde::Deserialize;
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
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .expect("spec-tests has a parent dir")
        .join("target")
        .join("spec-tests")
        .join(VERSION)
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
            if suite.file_type().map_or(false, |t| t.is_dir()) {
                cases.extend(collect_cases(&suite.path()));
            }
        }
    }
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
    let hex_str = meta.root.strip_prefix("0x").unwrap_or(&meta.root);
    let bytes = hex::decode(hex_str)
        .unwrap_or_else(|e| panic!("hex decode root in {}: {}", path.display(), e));
    let mut root = [0u8; 32];
    root.copy_from_slice(&bytes);
    root
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
        .filter(|e| e.file_type().map_or(false, |t| t.is_dir()))
        .collect();
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let name = entry.file_name().to_string_lossy().into_owned();
        cases.push((entry.path(), name));
    }
    cases
}
