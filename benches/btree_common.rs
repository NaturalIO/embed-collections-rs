//! Common utilities for BTreeMap benchmarks
//!
//! This module provides shared test data generation for comparing
//! embed_collections::BTreeMap with std::collections::BTreeMap.

use fastrand::Rng;

/// Data sizes for benchmarks
pub const SIZES: [usize; 3] = [1_000, 10_000, 1_000_000];

/// Generate random u32 keys for testing
///
/// Returns a Vec of random u32 values. The values may contain duplicates,
/// which is intentional to test realistic scenarios.
pub fn generate_random_keys(count: usize) -> Vec<u32> {
    let mut rng = Rng::new();
    (0..count).map(|_| rng.u32(..)).collect()
}

/// Generate sequential u32 keys for testing
///
/// Returns a Vec of sequential u32 values from 0 to count-1.
pub fn generate_sequential_keys(count: usize) -> Vec<u32> {
    (0..count as u32).collect()
}

/// Test data container for benchmarks
pub struct TestData {
    pub keys: Vec<u32>,
}

impl TestData {
    /// Create test data with random u32 keys (value equals key)
    pub fn new_random(count: usize) -> Self {
        let keys = generate_random_keys(count);
        Self { keys }
    }

    /// Create test data with sequential keys (value equals key)
    pub fn new_sequential(count: usize) -> Self {
        let keys = generate_sequential_keys(count);
        Self { keys }
    }
}

/// Get size description for benchmark naming
pub fn size_desc(size: usize) -> &'static str {
    match size {
        1_000 => "1k",
        10_000 => "10k",
        1_000_000 => "1m",
        _ => "unknown",
    }
}
