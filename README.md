# Embed Collections

docs.rs: <https://docs.rs/embed-collections/latest/embed_collections/>

`embed-collections` provides intrusive data structures for Rust. Unlike standard collections,
intrusive collections require the elements to store the node data (links) themselves.
This allows for:

- **Memory Efficiency**: No extra allocation for nodes.
- **Deterministic Memory Management**: You control where the node lives.
- **Flexibility**: Works with various pointer types (`Box`, `Arc`, `Rc`, `NonNull`, raw pointers).
- **Multiple ownership**: The trait and collection come with Tag to distinguish from each other,
  allow compiler checks.

Difference to crate `intrusive-collections`:

This crate choose to use DListItem::get_node() instead of c like `offset_of!`, mainly because:

- Mangling with offset conversion makes the code hard to read (for people not used to c style coding).

- You don't have to understand some complex macro style.

- It's dangerous to use pointer offset conversion when the embedded Node not perfectly aligned,
and using memtion to return the node ref is more safer approach.
 For example, the default `repr(Rust)` might reorder the field, or you mistakenly use `repr(packed)`.

There're three usage scenarios:

1. Push smart pointer to the list, so that the list hold 1 ref count when the type is `Arc` /
   `Rc`, but you have to use UnsafeCell for internal mutation.

2. Push `Box` to the list, the list own the items until they are popped, it's better than std
   LinkedList because no additional allocation is needed.

3. Push raw pointer (better use NonNull instead of *const T for smaller footprint) to the list,
for temporary usage. You must ensure the list item not dropped be other refcount
(for example, the item is holding by Arc in other structure).

## Modules

- [`dlist`]: Intrusive Doubly Linked List.
- [`slist`]: Intrusive Singly Linked List (FIFO Queue).
- [`avl`]: Intrusive AVL Tree (Balanced Binary Search Tree), and RangeTree based on AVL tree, port to rust from ZFS

## Feature Flags

This crate uses [feature flags](https://doc.rust-lang.org/cargo/reference/features.html) to control
the compilation of certain functionalities:

*   **`default`**: Enabled by default. Includes the `std` and `full` features.
*   **`std`**: Enables integration with the Rust standard library, including the `println!` macro for debugging. Disabling this feature enables `no_std` compilation.
*   **`slist`**: Enables the singly linked list (`slist`) module.
*   **`dlist`**: Enables the doubly linked list (`dlist`) module.
*   **`avl`**: Enables the `avl` and `range_tree` module.
*   **`full`**: Enabled by default. Includes `slist`, `dlist`, and `avl`.

To compile with `no_std` and only the `slist` module, you would use:
`cargo build --no-default-features --features slist`

## Example

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
