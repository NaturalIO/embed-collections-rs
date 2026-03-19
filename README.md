# Embed Collections

docs.rs: <https://docs.rs/embed-collections/latest/embed_collections/>

`embed-collections` provides memory efficient data structures for Rust.
For embedding environment and server applications that need tight memory management.

This crate provide two categories:

- Cache efficient collections:
    - [`ConstVec`]: Fixed capacity inline vec
    - [`SegList`]:  A list to store elements with adaptive size segments (the capacity of segment is calculated to fit a CPU cacheline). More efficient when vec when the number of items is small (< 100).
    - [`Various`]: For various count of elements passing between functions, zero or one condition will use Option, otherwise will using `SegList`

- intrusiave collection
    - Supports various smart pointer types: owned (Box), multiple ownership (Arc, Rc), unsafe (raw pointer)
    - [`dlist`]: Intrusive Doubly Linked List (Queue / Stack).
    - [`slist`]: Intrusive Singly Linked List ( Queue / stack).
    - [`slist_owned`]: An intrusive slist but with safe and more compact interface
    - [`avl`]: Intrusive AVL Tree (Balanced Binary Search Tree), port to rust from ZFS

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

This crate uses [feature flags](https://doc.rust-lang.org/cargo/reference/features.html) to control
the compilation of certain functionalities:

*   **`default`**: Enabled by default. Includes the `std` and `full` features.
*   **`std`**: Enables integration with the Rust standard library, including the `println!` macro for debugging. Disabling this feature enables `no_std` compilation.
*   **`slist`**: Enables the singly linked list (`slist`) and owned singly linked list (`slist_owned`) modules.
*   **`dlist`**: Enables the doubly linked list (`dlist`) module.
*   **`avl`**: Enables the `avl` and `range_tree` module.
*   **`full`**: Enabled by default. Includes `slist`, `dlist`, and `avl`.

To compile with `no_std` and only the `slist` module, you would use:
`cargo build --no-default-features --features slist`
