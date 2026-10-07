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
//!   - Use Layout API to determine the capacity, offset and alignement for the keys and values.
//!   - Keys is a tight array to enable efficient forward search for CPU pipeline.
//!   - No parent pointer in the page, we fill PathBuffer during descending, and pop when working upward.
//!   - Avoid memory fragmentation for the allocator.
//!
//! There tree variants:
//! - [various_map]:
//!   - Delay page allocation by inlining K, V with option.
//!   - Fallback to [compact] after inserting the 2nd element
//! - [compact]
//!   - For short-lived small size tree.
//!   - Avoid allocation of PathBuffer on heap, until the tree-height grows > 2.
//!   - PathBuffer allocation is reused.
//! - [large]
//!   - For long-lived large size tree.
//!   - Maintain a small statistic of page counts (inter and leaves), and PathBuffer, on the heap if tree-hight grows > 1
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
//! embed-btree:
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
//!   - `Entry::peek_forward()`
//!   - `Entry::peek_backward()`
//!   - `Entry::move_forward()`
//!   - `Entry::move_backward()`
//!   - `VacantEntry::peek_forward()`
//!   - `VacantEntry::peek_backward()`
//!   - `VacantEntry::move_forward()`
//!   - `VacantEntry::move_backward()`
//!   - `OccupiedEntry::peek_forward()`
//!   - `OccupiedEntry::peek_backward()`
//!   - `OccupiedEntry::move_forward()`
//!   - `OccupiedEntry::move_backward()`
//! - Alter key of an OccupiedEntry.
//!   - `OccupiedEntry::alter_key()`
//!
//! Batch removal:
//! - `BTree::remove_range()`
//! - `BTree::remove_range_with()`
//!
//! Readonly [Cursor]:
//! - [BTree::cursor()]
//! - [BTree::first_cursor()]
//! - [BTree::last_cursor()]
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
//! insert_seq |btree|std
//! -|-|-
//! 1k|**104.68**|20.001
//! 10k|**90.206**|16.04
//! 1m|**50.454**|11.207
//!
//! insert_rand|btree|std|avl(box)|avl(arc)
//! -|-|-|-|-
//! 1k|**23.325**|17.792|11.172|9.5397
//! 10k|**14.949**|11.587|6.3669|5.651
//! 1M|**6.1205**|3.0691|0.78|0.732
//!
//! get_seq|btree|std
//! -|-|-
//! 1k|**56.462**|34.248
//! 10k|**40.265**|27.571
//! 1M|**31.384**|19.907
//!
//! get_rand|btree|std|avl(box)|avl(arc)
//! -|-|-|-|-
//! 1k|**49.961**|27.651|24.254|23.466
//! 10k|**20.223**|16.868|11.771|10.806
//! 1M|**6.0508**|3.2569|1.4423|1.2712
//!
//! remove_rand |btree|std
//! -|-|-
//! 1k|**19.963**|15.968
//! 10k|**15.462**|11.701
//! 1M|**5.4713**|3.0724
//!
//! iter|btree|std
//! -|-|-
//! 1k|1443.2|346.8
//! 10k|1286.9|303.83
//! 1M|**215.95**|51.147
//!
//! into_iter|btree|std
//! -|-|-
//! 1k|396.07|143.81
//! 10k|410.32|81.389
//! 1M|**360.18**|56.742

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

#[allow(private_interfaces)]
pub mod various_map;
pub use various_map::VariousMap;
mod btree;
pub mod large;
pub use btree::{Key, Value};

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
