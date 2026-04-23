# Embed Collections

docs.rs: <https://docs.rs/embed-collections/latest/embed_collections/>

`embed-collections` provides memory efficient data structures for Rust.
For embedding environment and server applications that need tight memory management.

This crate provides two categories:

- Cache efficient collections:
    - [`ConstVec`]: Fixed capacity inline vec
    - [`SegList`](https://docs.rs/embed-collections/latest/embed_collections/seg_list/index.html):  A cache aware list to store elements with adaptive size segments
    - [`Various`](https://docs.rs/embed-collections/latest/embed_collections/various/index.html): For various elements passing between functions, zero or one condition will use Option, otherwise will using `SegList`
    - [`BTreeMap`](https://docs.rs/embed-collections/latest/embed_collections/btree/index.html): A cache aware B+tree implementation, optimized for numeric types, with special entry API allows peaking adjacent values.

- Intrusive collection
    - Supports various smart pointer types: owned (Box), multiple ownership (Arc, Rc), raw pointers (`NonNull<T>`, `*const T`, `*mut T`)
    - [`dlist`](https://docs.rs/embed-collections/latest/embed_collections/dlist/index.html): Intrusive Doubly Linked List (Queue / Stack).
    - [`slist`](https://docs.rs/embed-collections/latest/embed_collections/slist/index.html): Intrusive Singly Linked List ( Queue / stack).
    - [`slist_owned`](https://docs.rs/embed-collections/latest/embed_collections/slist_owned/index.html): An intrusive slist but with safe and more compact interface
    - [`avl`](https://docs.rs/embed-collections/latest/embed_collections/avl/index.html): Intrusive AVL Tree (Balanced Binary Search Tree), port to rust from ZFS

## SegList & Various

`SegList` and `Various` is designed for parameter passing.

More CPU-cache friendly compared to `LinkedList`. And because it does not re-allocate, it's faster than `Vec::push()` when the number of elements is small.
It's nice to the memory allocator (always allocate with fixed size segment).

Benchmark: append + drain (x86_64, cache line 128 bytes):

(platform: intel i7-8550U)

| Elements | SegList | Vec | SegList vs Vec |
|----------|---------|-----|----------------|
| 10 | 40.5 ns | 147.0 ns | **3.6x faster** |
| 32 | 99.1 ns | 237.8 ns | **2.4x faster** |
| 100 | 471.1 ns | 464.0 ns | ~1.0x |
| 500 | 2.77 µs | 895.5 ns | 3.1x slower |

## B+tree

We provide a [BTreeMap](https://docs.rs/embed-collections/latest/embed_collections/btree/index.html) for single-threaded long-term in-memory storage.
It's a cache aware b+tree:

- Nodes are filled up in 4 cache lines (256 bytes on x86_64).
- Optimized for numeric type, and tight arrangement sequential inserting.
- Capacity in compile-time determined according to the size of Key, Value.
- Smart optimization for sequential insert
- Faster iteration and teardown
- Key type needs `Clone`
- Specially API:
  - peak and move to previous/next entry.
  - alter key of an OccupiedEntry.
  - Batch remove with range.

Comparing to std::collections::btree (as of rust 1.94):
- The std impl is pure btree (not b+tree) without horizontal links. Each key store only once at either leaf and inter nodes.
- The std impl is optimised for point lookup,
- The std impl has fixed Cap=11, size is 288B for InterNode and 192B for LeafNode.
- The std cursor API is still unstable (as of 1.94) and provides more complex features

**benchmark**:

(platform: intel i7-8550U, key: u32, value: u32, rust 1.92)

insert_seq (me/s)|btree|std
-|-|-
1k|88.956|20.001
10k|75.291|16.04
100k|45.959|11.207

insert_rand (me/s)|btree|std|avl(box)|avl(arc)
-|-|-|-|-
1k|21.311|17.792|11.172|9.5397
10k|14.268|11.587|6.3669|5.651
100k|5.4814|3.0691|0.78|0.732

get_seq (me/s)|btree|std
-|-|-
1k|59.448|34.248
10k|37.225|27.571
100k|30.77|19.907

get_rand (me/s)|btree|std|avl(box)|avl(arc)
-|-|-|-|-
1k|47.33|27.651|24.254|23.466
10k|19.358|16.868|11.771|10.806
100k|5.2584|3.2569|1.4423|1.2712

remove_rand (me/s)|btree|std
-|-|-
1k|20.965|15.968
10k|16.073|11.701
100k|5.0214|3.0724

iter (me/s)|btree|std
-|-|-
1k|1342.8|346.8
10k|1209.4|303.83
100k|152.57|51.147

into_iter (me/s)|btree|std
-|-|-
1k|396.07|143.81
10k|397.05|81.389
100k|360.18|56.742


## Intrusive Collections

intrusive collection is often used in c/c++ code, they does not need extra allocation.
But the disadvantages includes: complexity to write, bad for cache hit when the node is too small

There're three usage scenarios:

1. Push smart pointer to the list, so that the list hold 1 ref count when the type is `Arc` /
   `Rc`, but you have to use UnsafeCell for internal mutation.

2. Push `Box` to the list, the list own the items until they are popped, it's better than std
   LinkedList because no additional allocation is needed.

3. Push raw pointer (better use NonNull instead of *const T for smaller footprint) to the list,
   for temporary usage. You must ensure the list item not dropped be other refcount
   (for example, the item is holding by Arc in other structure).


### Difference to `intrusive-collections` crate

This crate choose to use trait instead of c like `offset_of!`, mainly because:

- Mangling with offset conversion makes the code hard to read (for people not used to c style coding).

- You don't have to understand some complex macro style.

- It's dangerous to use pointer offset conversion when the embedded Node not perfectly aligned,
  and using memtion to return the node ref is more safer approach.
  For example, the default `repr(Rust)` might reorder the field, or you mistakenly use `repr(packed)`.

### instrusive link list example

```rust
use embed_collections::{dlist::{DLinkedList, DListItem, DListNode}, Pointer};
use std::cell::UnsafeCell;
use std::sync::Arc;

// The tag structure only for labeling, distinguish two lists
struct CacheTag;
struct IOTag;

struct MyItem {
    val: i32,
    cache_link: UnsafeCell<DListNode<MyItem, CacheTag>>,
    io_link: UnsafeCell<DListNode<MyItem, IOTag>>,
}

impl MyItem {
    fn new(val: i32) -> Self {
        Self {
            val,
            cache_link: UnsafeCell::new(DListNode::default()),
            io_link: UnsafeCell::new(DListNode::default()),
        }
    }
}

unsafe impl DListItem<CacheTag> for MyItem {
    fn get_node(&self) -> &mut DListNode<Self, CacheTag> {
        unsafe { &mut *self.cache_link.get() }
    }
}

unsafe impl DListItem<IOTag> for MyItem {
    fn get_node(&self) -> &mut DListNode<Self, IOTag> {
        unsafe { &mut *self.io_link.get() }
    }
}

let mut cache_list = DLinkedList::<Arc<MyItem>, CacheTag>::new();
let mut io_list = DLinkedList::<Arc<MyItem>, IOTag>::new();

let item1 = Arc::new(MyItem::new(10));
let item2 = Arc::new(MyItem::new(20));

// Push the same item to both lists
cache_list.push_back(item1.clone());
io_list.push_back(item1.clone());

cache_list.push_back(item2.clone());
io_list.push_back(item2.clone());

assert_eq!(cache_list.pop_front().unwrap().val, 10);
assert_eq!(io_list.pop_front().unwrap().val, 10);
assert_eq!(cache_list.pop_front().unwrap().val, 20);
assert_eq!(io_list.pop_front().unwrap().val, 20);
```

## Feature Flags

*   **`default`**: Enabled by default. Includes the `std` features.
*   **`std`**: Enables integration with the Rust standard library, including the `println!` macro for debugging. Disabling this feature enables `no_std` compilation.
*   **`slist`**: Enables the singly linked list (`slist`) and owned singly linked list (`slist_owned`) modules.
*   **`dlist`**: Enables the doubly linked list (`dlist`) module.
*   **`avl`**: Enables the `avl` module.
*   **`btree`**: Enable the btree module.
*   **`full`**: Enabled by default. Includes `slist`, `dlist`, and `avl`.

To compile with `no_std` and only the `slist` module, you would use:
`cargo build --no-default-features --features slist`
