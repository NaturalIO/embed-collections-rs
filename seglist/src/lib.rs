#![allow(rustdoc::redundant_explicit_links)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]

//! # SegList
//!
//! [SegList](crate::seglist) is a replacement for linked list, and Vec (when you don't need random
//! access)
//!
//! [Various](crate::various) is designed for parameter passing, which wraps `Option` & `SegList`, when the optimal condition is empty or one.
//!
//! More CPU-cache friendly compared to `LinkedList`. And because it does not re-allocate, it's faster than `Vec::push()` when the number of elements is small.
//! It's nice to the memory allocator (always allocate with fixed size segment).
//!
//! Benchmark: append + drain (x86_64, cache line 128 bytes):
//!
//! (platform: intel i7-8550U)
//!
//! | Elements | SegList | Vec | SegList vs Vec |
//! |----------|---------|-----|----------------|
//! | 10 | 40.5 ns | 147.0 ns | **3.6x faster** |
//! | 32 | 99.1 ns | 237.8 ns | **2.4x faster** |
//! | 100 | 471.1 ns | 464.0 ns | ~1.0x |
//! | 500 | 2.77 µs | 895.5 ns | 3.1x slower |

extern crate alloc;

pub mod various;
pub use various::Various;
pub mod seglist;
pub use seglist::SegList;
