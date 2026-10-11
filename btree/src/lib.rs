#![allow(rustdoc::redundant_explicit_links)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![cfg_attr(not(feature = "std"), no_std)]

//! # embed-btree
//!
//! We provide a `BTreeMap` for single-threaded in-memory storage.
//! It's b+tree designed
//!
//! - cache-aware principles,
//!   - All page is aligned in 4*CACHE_LINE (256 bytes on x86_64).
//!   - Use Layout API to determine the capacity, offset and alignment for the keys and values.
//!   - Keys is a tight array to enable efficient forward search for CPU pipeline.
//!   - No parent pointer in the page, saving the space.
//!     - we fill reused PathBuffer during descending, and pop when working upward.
//!     - PathBuffer only used during ops that require mutation of the map, so it's safe for
//!       concurrent reads.
//!   - Avoid memory fragmentation for the allocator.
//!
//! There tree variants:
//! - [various_map]:
//!   - Delay page allocation by inlining K, V with option.
//!   - Fallback to std BTreeMap after inserting the 2nd element
//! - [compact]
//!   - For short-lived, small size tree.
//!   - Avoid allocation of PathBuffer on heap, until the tree height grows pass threshold.
//!     (>4 for insert/remove, >2 for entry ops)
//!   - PathBuffer allocation is reused.
//! - [large]
//!   - For long-lived, large size tree.
//!   - after tree height grows beyond 1, allocate a small heap for PathBuffer, and page statistic (inter and
//!     leavse).
//!
//! Struct size:
//!
//! ```text
//! std: BTreeMap<u32, u32>: 24
//! std: Option<BTreeMap<u32, u32>>: 32
//! std: VacantEntry<u32, u32>: 40
//! std: OccupiedEntry<u32, u32>: 32
//!
//! compact: BTreeMap<u32, u32>: 24
//! compact: Option<BTreeMap<u32, u32>>: 24
//! compact: Entry<u32,u32>:  32
//! compact: Option<Entry<u32, u32>>:  40
//! compact: VacantEntry<u32, u32>: 32
//! compact: OccupiedEntry<u32, u32>: 24
//!
//! large: BTreeMap 24
//! large: Option<BTreeMap> 24
//! large: Entry size: 24
//! large: Option<Entry>: 32
//! large: VacantEntry<u32, u32>: 24
//! large: OccupiedEntry<u32, u32>: 16
//!
//! ```
//!
//! ## Supported K, V types
//!
//! **Optimised for numeric key**
//!   - Respecting numeric space, more compact tree when doing sequential insertion
//!   - Reduce latency for sequential get and insertion.
//!
//! Optimised for unbalanced size K / V, and specially 0-size V, for most capacity.
//!
//! Bytes keys on the heap are supported, but we will not do prefix compress.
//!   (You may look for other structures with prefix compression: Art, Masstree)
//!
//! Limits:
//!   - K should have `Clone` (for propagate into the InterNode during split)
//!   - K + V should < 2 * CACHE_LINE_SIZE
//!     - It make sure InterNode can hold at least two children.
//!     - If K & V is large you should put into `Box`, for room saving, and for the speed to move value
//!
//! ## Compared to std btree_map
//!
//! (Analyse based on source of rust 1.94)
//!
//! std:
//! - pure btree (without horizontal links).
//! - Each key store only once at either leaf and inter nodes, don't require key to be `Clone`.
//! - good for point lookup (value may be at top level)
//! - has fixed Cap=11, node size varies according to T. (For T=U64, size is 288B for InterNode and 192B for LeafNode)
//! - the size of page varies for different type of K / V, might not perfectly aligned for the cache and allocator.
//! - each page has keys, values, pointers. the section of pointers may be wasted for leaves.
//! - cursor API is still unstable, need nightly.
//!
//! crate::bptree:
//! - faster sequential get & insert
//! - faster iteration
//! - faster teardown
//! - higher fan-out, reduction in height
//!
//! ## Special API and Scenario
//!
//! statistic (node count and memory usage) in [large] variant
//!
//! Entries:
//! - Adjacent `Entry` (for iter and modification).
//!   - [bptree::Entry::peek_forward()]
//!   - [bptree::Entry::peek_backward()]
//!   - [bptree::Entry::move_forward()]
//!   - [bptree::Entry::move_backward()]
//!   - [bptree::VacantEntry::peek_forward()]
//!   - [bptree::VacantEntry::peek_backward()]
//!   - [bptree::VacantEntry::move_forward()]
//!   - [bptree::VacantEntry::move_backward()]
//!   - [bptree::OccupiedEntry::peek_forward()]
//!   - [bptree::OccupiedEntry::peek_backward()]
//!   - [bptree::OccupiedEntry::move_forward()]
//!   - [bptree::OccupiedEntry::move_backward()]
//! - Alter key of an OccupiedEntry.
//!   - [bptree::OccupiedEntry::alter_key()]
//!
//! Batch removal:
//! - [bptree::BTree::remove_range()](btree::BTree::remove_range)
//! - [bptree::BTree::remove_range_with()](btree::BTree::remove_range_with)
//!
//! Readonly [Cursor](btree::Cursor):
//! - [bptree::BTree::cursor()](btree::BTree::cursor)
//! - [bptree::BTree::first_cursor()](btree::BTree::first_cursor)
//! - [bptree::BTree::last_cursor()](btree::BTree::last_cursor)
//!
//! Use case:
//! - [range-tree-rs](https://docs.rs/range-tree-rs)
//!
//! ## benchmark
//!
//! platform: intel i7-8550U, key: u32, value: u32, rust 1.97.
//!
//! Measured in million ops for different size of dataset:
//!
//! insert_seq |compact|large|std
//! -|-|-|-
//! 1k|84.777|**91.140**|20.001
//! 10k|72.022|**79.060**|16.04
//! 1m|44.863|**46.200**|11.207
//!
//! insert_rand|compact|large|std|avl(box)|avl(arc)
//! -|-|-|-|-|-
//! 1k|21.459|**22.284**|17.792|11.172|9.5397
//! 10k|13.931|**14.319**|11.587|6.3669|5.651
//! 1M|5.8124|**5.9710**|3.0691|0.78|0.732
//!
//! get_seq|compact|large|std
//! -|-|-|-
//! 1k|59.214|**62.891**|34.248
//! 10k|40.652|**41.823**|27.571
//! 1M|30.640|**32.597**|19.907
//!
//! get_rand|compact|large|std|avl(box)|avl(arc)
//! -|-|-|-|-|-
//! 1k|**52.213**|51.230|27.651|24.254|23.466
//! 10k|**22.117**|20.894|16.868|11.771|10.806
//! 1M|6.1369|**6.2403**|3.2569|1.4423|1.2712
//!
//! remove_rand|compact|large|std
//! -|-|-|-
//! 1k|18.336|**19.963**|15.968
//! 10k|14.094|**15.462**|11.701
//! 1M|5.2262|**5.4713**|3.0724
//!
//! iter|compact|large|std
//! -|-|-|-
//! 1k|1423,3|1443.2|346.8
//! 10k|1226.3|1286.9|303.83
//! 1M|**217.10**|**215.95**|51.147
//!
//! into_iter|compact|large|std
//! -|-|-|-
//! 1k|364.14|**396.07**|143.81
//! 10k|356.85|**410.32**|81.389
//! 1M|327.87|**360.18**|56.742

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

#[allow(private_interfaces)]
pub mod various_map;
pub use various_map::VariousMap;
/// generic interface of b+tree
pub mod bptree;
/// BtreeMap with no stats (for many short-live dataset)
pub mod compact;
/// BtreeMap with stats (for large love-live dataset)
pub mod large;
pub use bptree::{Key, Value};

pub type BTreeMap<K, V> = compact::BTreeMap<K, V>;

pub use embed_collections::CACHE_LINE_SIZE;

/// logging macro for development
#[macro_export(local_inner_macros)]
macro_rules! trace_log {
    ($($arg:tt)+)=>{
        #[cfg(feature="trace_log")]
        {
            log::debug!($($arg)+);
        }
    };
}

/// logging macro for development
#[macro_export(local_inner_macros)]
macro_rules! print_log {
    ($($arg:tt)+)=>{
        #[cfg(feature="trace_log")]
        {
            log::debug!($($arg)+);
        }
        #[cfg(not(feature="trace_log"))]
        {
            std::println!($($arg)+);
        }
    };
}
