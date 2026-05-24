# Embed Collections

docs.rs: <https://docs.rs/embed-collections/latest/embed_collections/>

<!-- cargo-rdme start -->


## embed-collections

A collection of memory efficient data structures, for embedding environment and server applications that need tight memory management.

This crate provides two categories of modules:

- Cache efficient collections:
    - [const_vec](https://docs.rs/embed-collections/latest/embed_collections/const_vec/): Fixed capacity inline vec
    - [seg_list](#seglist--various):  A cache aware (short-live) list to store elements with adaptive size segments
    - [various](#seglist--various): A short-live list wrapping `SegList` with `Option<T>` to delay allocation.
    - [btree](#btree): A cache aware B+tree for lone-live and large dataset, optimized for numeric types, with special entry API allows peeking adjacent values.
    - [various_map](https://docs.rs/embed-collections/latest/embed_collections/various_map/): A short-live map wrapping BTreeMap (std) with `Option<(K, V)>` to delay allocation.

- [Intrusive collections](#intrusive-collections):
    - All container types support by [Pointer] [SmartPointer] trait:
      - std `Box` (owned),
      - std `Arc`, `Rc` (multiple ownership)
      - [Irc](https://docs.rs/embed-collections/latest/embed_collections/irc/): Highly customized Intrusive Reference Counter. See the detail in
        module doc.
      - [WaitGroupZeroGuard](https://docs.rs/crossfire/latest/crossfire/waitgroup/struct.WaitGroupZeroGuard.html):  see the doc in `crossfire` crate
      - raw pointers (`NonNull<T>`, `*const T`, `*mut T`)
    - Structs:
      - [dlist](https://docs.rs/embed-collections/latest/embed_collections/dlist/): Intrusive Doubly Linked List (Queue / Stack).
      - [slist](https://docs.rs/embed-collections/latest/embed_collections/slist/): Intrusive Singly Linked List ( Queue / stack).
      - [slist_owned](https://docs.rs/embed-collections/latest/embed_collections/slist_owned/): An intrusive slist but with safe and more compact interface
      - [avl](https://docs.rs/embed-collections/latest/embed_collections/avl/): Intrusive AVL Tree (Balanced Binary Search Tree), port to rust from ZFS

**Disclaimer**

Intrusive code is not recommended unless you are full aware of what you are doing.
Most traits are mark with `unsafe`. While we try to give you freedom, not letting the rules probibit
you build highly customized logic, this library still has regular scheduled Miri test routine.

### SegList & Various

[SegList](https://docs.rs/embed-collections/latest/embed_collections/seg_list/) and [Various](https://docs.rs/embed-collections/latest/embed_collections/various/) is designed for parameter passing.

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

### B+tree

We provide a [BTreeMap](https://docs.rs/embed-collections/latest/embed_collections/btree/) for single-threaded long-term in-memory storage.
It's a cache aware b+tree:

- Nodes are filled up in 4 cache lines (256 bytes on x86_64).
  - Capacity in compile-time determined according to the size of Key, Value.
  - Reduce memory fragmentation by alignment.
- **Optimised for numeric key**
  - Respecting numeric space for sequential insertion.
  - Reduce latency for sequential insertion.
- Faster iteration and teardown
- **Limitation**:
  - K should have clone (for propagate into the InterNode during split)
  - K & V should <= CACHE_LINE_SIZE - 16
    - It make sure InterNode can hold  at least two children.
    - If K & V is large you should put into `Box`, for room saving, and for the speed to move value
- **Special API**:
  - Peak and move to previous/next `Entry` (for modification).
  - Alter key of an OccupiedEntry.
  - Batch remove with range.
  - Movable `Cursor` (for readonly)

Compared to std::collections::btree (as of rust 1.94):
- The std impl is pure btree (not b+tree) without horizontal links. Each key store only once at either leaf and inter nodes.
- The std impl is optimised for point lookup.
- The std impl has fixed Cap=11, node size varies according to T. (For T=U64, size is 288B for InterNode and 192B for LeafNode)
- The std cursor API is still unstable (as of 1.94) and relatively complex to use.

**benchmark**

platform: intel i7-8550U, key: u32, value: u32, rust 1.92.

Measured in million ops for different size of dataset:

insert_seq |btree|std
-|-|-
1k|**88.956**|20.001
10k|**75.291**|16.04
100k|**45.959**|11.207

insert_rand|btree|std|avl(box)|avl(arc)
-|-|-|-|-
1k|**21.311**|17.792|11.172|9.5397
10k|**14.268**|11.587|6.3669|5.651
100k|**5.4814**|3.0691|0.78|0.732

get_seq|btree|std
-|-|-
1k|**59.448**|34.248
10k|**37.225**|27.571
100k|**30.77**|19.907

get_rand|btree|std|avl(box)|avl(arc)
-|-|-|-|-
1k|**47.33**|27.651|24.254|23.466
10k|**19.358**|16.868|11.771|10.806
100k|**5.2584**|3.2569|1.4423|1.2712

remove_rand |btree|std
-|-|-
1k|**20.965**|15.968
10k|**16.073**|11.701
100k|**5.0214**|3.0724

iter|btree|std
-|-|-
1k|1342.8|346.8
10k|1209.4|303.83
100k|**152.57**|51.147

into_iter|btree|std
-|-|-
1k|396.07|143.81
10k|397.05|81.389
100k|**360.18**|56.742


### Intrusive Collections

intrusive collection is often used in c/c++ code, they does not need extra allocation.
But the disadvantages includes:

- Complex to write (This crate seal most boilderplates)

- Linking heap object to another is bad for cache hit (Use structure like [SegList] is preferable)

There're three usage scenarios:

1. Push smart pointer to the list, so that the list hold 1 ref count when the type is `Arc` /
   `Rc`, but you have to use UnsafeCell for internal mutation.

2. Push `Box` to the list, the list own the items until they are popped, it's better than std
   LinkedList because no additional allocation is needed.  It will not move the item
   in-and-out of hidden `Box` on every push / pop.

3. Push raw pointer (better use NonNull instead of *const T for smaller footprint) to the list,
   for temporary usage. You must ensure the list item not dropped be other refcount
   (for example, the item is holding by Arc in other structure).


#### Difference to `intrusive-collections` crate

This crate choose to use trait instead of c like `offset_of!`, mainly because:

- Mangling with offset conversion makes the code hard to read (for people not used to c style coding).

- You don't have to understand some complex macro style.

- It's dangerous to use pointer offset conversion when the embedded Node not perfectly aligned,
  and using memtion to return the node ref is more safer approach.
  For example, the default `repr(Rust)` might reorder the field, or you mistakenly use `repr(packed)`.

#### instrusive link list example

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

### Feature Flags

*   **`default`**: Enabled by default. Includes the `std`, `various`, `seglist` features.
*   **`full`**: Includes everything but std
*   **`std`**: Enables integration with the Rust standard library, including the `println!` macro for debugging. Disabling this feature enables `no_std` compilation.
*   **`avl`**: Enables the `avl` module.
*   **`btree`**: Enable the btree module.
*   **`dlist`**: Enables the doubly linked list (`dlist`) module.
*   **`irc`**: Enables the `irc` (intrusive ref count) module.
*   **`various`**: Enable various_map module
*   **`various` + `seglist`**: Enable various module
*   **`seglist`**: Enable seg_list module
*   **`slist`**: Enables the singly linked list (`slist`) and owned singly linked list (`slist_owned`) modules.

To compile with `no_std` and only the `slist` module, you would use:
`cargo build --no-default-features --features slist`

<!-- cargo-rdme end -->
