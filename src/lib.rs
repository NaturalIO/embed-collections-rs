#![allow(rustdoc::redundant_explicit_links)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
//!
//! # embed-collections
//!
//! A collection of memory efficient data structures, for embedding environment and server applications that need tight memory management.
//!
//! This repo consists some small crates.
//!
//! **NOTE: There nothing in the main crate, all modules have moved to sub crates**.
//!
//! ## Cache efficient collections
//!
//! - [embed-constvec](https://docs.rs/embed-constvec): Fixed capacity inline vec
//! - [embed-seglist](https://docs.rs/embed-seglist):  A cache aware (short-live) list to store elements with adaptive size segments
//! - [embed-btree](https://docs.rs/embed-btree): A cache aware B+tree for lone-live and large dataset, optimized for numeric types, with special entry API allows peeking adjacent values.
//!
//! ## Intrusive collections:
//!
//! We support all-types from the [pointers](https://docs.rs/pointers) crate,
//! with `Pointer` trait for intrusive collections:
//! - raw pointers (`NonNull<T>`, `*const T`, `*mut T`)
//! - std `Box` (owned),
//! - std `Arc`, `Rc` (multiple ownership)
//! - `Irc`: Highly customizable Intrusive Reference Counter.
//! - [WaitGroupZeroGuard](https://docs.rs/crossfire/latest/crossfire/waitgroup/struct.WaitGroupZeroGuard.html):  see the doc in `crossfire` crate
//!
//! Sub crates:
//! - [embed-dlist](https://docs.rs/embed-dlist): Intrusive Doubly Linked List (Queue / Stack).
//! - [embed-slist](https://docs.rs/embed-slist): Intrusive Singly Linked List ( Queue / stack).
//! - [embed-avl](https://docs.rs/embed-avl): Intrusive AVL Tree (Balanced Binary Search Tree), port to rust from ZFS
//!
//! **Disclaimer**
//!
//! Intrusive code is not recommended unless you are full aware of what you are doing.
//! Most traits are mark with `unsafe`. While we try to give you freedom, not letting the rules probibit
//! you build highly customized logic, this library still has regular scheduled Miri test routine.
//! But the disadvantages includes:
//!
//! - Complex to write (This crate seal most boilderplates)
//!
//! - Linking heap object to another is bad for cache hit (Use structure like `SegList` is preferable)
//!
//! There're three usage scenarios:
//!
//! 1. Push smart pointer to the list, so that the list hold 1 ref count when the type is `Arc` /
//!    `Rc`, but you have to use UnsafeCell for internal mutation.
//!
//! 2. Push `Box` to the list, the list own the items until they are popped, it's better than std
//!    LinkedList because no additional allocation is needed.  It will not move the item
//!    in-and-out of hidden `Box` on every push / pop.
//!
//! 3. Push raw pointer (better use NonNull instead of *const T for smaller footprint) to the list,
//!    for temporary usage. You must ensure the list item not dropped be other refcount
//!    (for example, the item is holding by Arc in other structure).
//!
//!
//! ### Difference to `intrusive-collections` crate
//!
//! This crate choose to use trait instead of c like `offset_of!`, mainly because:
//!
//! - Mangling with offset conversion makes the code hard to read (for people not used to c style coding).
//!
//! - You don't have to understand some complex macro style.
//!
//! - It's dangerous to use pointer offset conversion when the embedded Node not perfectly aligned,
//!   and using memtion to return the node ref is more safer approach.
//!   For example, the default `repr(Rust)` might reorder the field, or you mistakenly use `repr(packed)`.
//!

/// Cache line size in bytes
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm64ec",
    target_arch = "powerpc64",
))]
pub const CACHE_LINE_SIZE: usize = 64;
#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm64ec",
    target_arch = "powerpc64",
)))]
pub const CACHE_LINE_SIZE: usize = 32;
