use flate2::read::GzDecoder;
use serde::Deserialize;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

const RELEASE_URL: &str = "https://github.com/ethereum/consensus-specs/releases/download/v1.6.1";
const VERSION: &str = "v1.6.1";

/// The three test archives published by the consensus-specs repo.
#[derive(Debug, Clone, Copy)]
pub enum Archive {
    General,
    Mainnet,
    Minimal,
}

impl Archive {
    pub fn filename(self) -> &'static str {
        match self {
            Archive::General => "general.tar.gz",
            Archive::Mainnet => "mainnet.tar.gz",
            Archive::Minimal => "minimal.tar.gz",
        }
    }

    /// e.g. "general", "mainnet", "minimal" — matches the top-level dir inside the tarball.
    pub fn dir_name(self) -> &'static str {
        match self {
            Archive::General => "general",
            Archive::Mainnet => "mainnet",
            Archive::Minimal => "minimal",
        }
    }

    pub fn url(self) -> String {
        format!("{}/{}", RELEASE_URL, self.filename())
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
    // Walk up from the manifest dir to find workspace target/
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .expect("spec-tests has a parent dir")
        .join("target")
        .join("spec-tests")
        .join(VERSION)
}

/// Ensure that the given archive has been downloaded and extracted.
/// Returns the path to the extracted `tests/` directory.
///
/// e.g. for `Archive::General` → `<cache>/general/tests/general/`
pub fn ensure_archive(archive: Archive) -> PathBuf {
    let root = cache_dir().join(archive.dir_name());
    let sentinel = root.join(".extracted");

    if sentinel.exists() {
        return root;
    }

    eprintln!("Downloading {} ({})...", archive.filename(), archive.url());

    // Download
    let resp = ureq::get(&archive.url())
        .call()
        .unwrap_or_else(|e| panic!("Failed to download {}: {}", archive.url(), e));

    let mut compressed = Vec::new();
    resp.into_body()
        .as_reader()
        .read_to_end(&mut compressed)
        .expect("read response body");

    // Decompress + extract
    let gz = GzDecoder::new(compressed.as_slice());
    let mut archive_tar = tar::Archive::new(gz);

    fs::create_dir_all(&root).expect("create cache dir");
    archive_tar.unpack(&root).expect("extract tar.gz");

    // Write sentinel
    fs::write(&sentinel, "").expect("write sentinel");

    eprintln!("Extracted to {}", root.display());
    root
}

// ── ssz_generic helpers ──

/// Path to an ssz_generic handler directory.
///
/// e.g. `<cache>/general/tests/general/phase0/ssz_generic/boolean`
pub fn ssz_generic_handler_path(handler: &str) -> PathBuf {
    let root = ensure_archive(Archive::General);
    root.join("tests")
        .join("general")
        .join("phase0")
        .join("ssz_generic")
        .join(handler)
}

/// Iterate valid test cases for an ssz_generic handler.
/// Returns `(case_path, case_name)` pairs.
pub fn ssz_generic_valid_cases(handler: &str) -> Vec<(PathBuf, String)> {
    collect_cases(&ssz_generic_handler_path(handler).join("valid"))
}

/// Iterate invalid test cases for an ssz_generic handler.
pub fn ssz_generic_invalid_cases(handler: &str) -> Vec<(PathBuf, String)> {
    collect_cases(&ssz_generic_handler_path(handler).join("invalid"))
}

// ── ssz_static helpers ──

/// Path to an ssz_static type directory for a given network and fork.
///
/// e.g. `<cache>/mainnet/tests/mainnet/phase0/ssz_static/Validator`
pub fn ssz_static_type_path(archive: Archive, fork: &str, type_name: &str) -> PathBuf {
    let root = ensure_archive(archive);
    root.join("tests")
        .join(archive.dir_name())
        .join(fork)
        .join("ssz_static")
        .join(type_name)
}

/// Iterate test cases for an ssz_static type. Cases are nested under suite
/// directories (e.g. `ssz_random/case_0/`).
pub fn ssz_static_cases(archive: Archive, fork: &str, type_name: &str) -> Vec<(PathBuf, String)> {
    let type_dir = ssz_static_type_path(archive, fork, type_name);
    let mut cases = Vec::new();
    if !type_dir.exists() {
        return cases;
    }
    // Each suite (ssz_random, etc.) contains case directories
    if let Ok(suites) = fs::read_dir(&type_dir) {
        for suite in suites.flatten() {
            if suite.file_type().map_or(false, |t| t.is_dir()) {
                let suite_cases = collect_cases(&suite.path());
                cases.extend(suite_cases);
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
/// Returns the 32-byte hash tree root.
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

/// Read a scalar YAML value as a string (for boolean/uint test cases).
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
