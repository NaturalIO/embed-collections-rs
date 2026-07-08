#![allow(rustdoc::redundant_explicit_links)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![cfg_attr(not(feature = "std"), no_std)]
//! ### embed-btree
//!
//! We provide a `BTreeMap` for single-threaded long-term in-memory storage.
//! It's a cache aware b+tree:
//!
//! - Nodes are filled up in 4 cache lines (256 bytes on x86_64).
//!   - Capacity in compile-time determined according to the size of Key, Value.
//!   - Reduce memory fragmentation by alignment.
//! - **Optimised for numeric key**
//!   - Respecting numeric space for sequential insertion.
//!   - Reduce latency for sequential insertion.
//! - Faster iteration and teardown
//! - **Limitation**:
//!   - K should have clone (for propagate into the InterNode during split)
//!   - K & V should <= CACHE_LINE_SIZE - 16
//!     - It make sure InterNode can hold  at least two children.
//!     - If K & V is large you should put into `Box`, for room saving, and for the speed to move value
//! - **Special API**:
//!   - Peak and move to previous/next `Entry` (for modification).
//!   - Alter key of an OccupiedEntry.
//!   - Batch remove with range.
//!   - Movable `Cursor` (for readonly)
//!
//! Compared to std::collections::btree (as of rust 1.94):
//! - The std impl is pure btree (not b+tree) without horizontal links. Each key store only once at either leaf and inter nodes.
//! - The std impl is optimised for point lookup.
//! - The std impl has fixed Cap=11, node size varies according to T. (For T=U64, size is 288B for InterNode and 192B for LeafNode)
//! - The std cursor API is still unstable (as of 1.94) and relatively complex to use.
//!
//! **benchmark**
//!
//! platform: intel i7-8550U, key: u32, value: u32, rust 1.92.
//!
//! Measured in million ops for different size of dataset:
//!
//! insert_seq |btree|std
//! -|-|-
//! 1k|**88.956**|20.001
//! 10k|**75.291**|16.04
//! 100k|**45.959**|11.207
//!
//! insert_rand|btree|std|avl(box)|avl(arc)
//! -|-|-|-|-
//! 1k|**21.311**|17.792|11.172|9.5397
//! 10k|**14.268**|11.587|6.3669|5.651
//! 100k|**5.4814**|3.0691|0.78|0.732
//!
//! get_seq|btree|std
//! -|-|-
//! 1k|**59.448**|34.248
//! 10k|**37.225**|27.571
//! 100k|**30.77**|19.907
//!
//! get_rand|btree|std|avl(box)|avl(arc)
//! -|-|-|-|-
//! 1k|**47.33**|27.651|24.254|23.466
//! 10k|**19.358**|16.868|11.771|10.806
//! 100k|**5.2584**|3.2569|1.4423|1.2712
//!
//! remove_rand |btree|std
//! -|-|-
//! 1k|**20.965**|15.968
//! 10k|**16.073**|11.701
//! 100k|**5.0214**|3.0724
//!
//! iter|btree|std
//! -|-|-
//! 1k|1342.8|346.8
//! 10k|1209.4|303.83
//! 100k|**152.57**|51.147
//!
//! into_iter|btree|std
//! -|-|-
//! 1k|396.07|143.81
//! 10k|397.05|81.389
//! 100k|**360.18**|56.742

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

#[allow(private_interfaces)]
pub mod various_map;
pub use various_map::VariousMap;
pub mod btree;
pub use btree::BTreeMap;
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
