# Embed Collections

`embed-collections` provides intrusive data structures for Rust. Unlike standard collections,
intrusive collections require the elements to store the node data (links) themselves.
This allows for:

- **Memory Efficiency**: No extra allocation for nodes.
- **Deterministic Memory Management**: You control where the node lives.
- **Flexibility**: Works with various pointer types (`Box`, `Arc`, `Rc`, `NonNull`, raw pointers).

Difference to crate `intrusive-collections`:

This crate choose to use DListItem::get_node() instead of c like `offset_of!`, mainly because:

- Mangling with offset conversion makes the code hard to read (for people not used to c style coding).

- You don't have to understand some complex macro style.

- It's dangerous to use pointer offset conversion when the embedded Node not perfectly aligned,
and using memtion to return the node ref is more safer approach.
(For example, the default `repr(Rust) might reorder the field`, or you mistakenly use `repr(packed)`)

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

## Example

```rust
use embed_collections::{dlist::{DLinkedList, DListItem, DListNode}, Pointer};
use std::cell::UnsafeCell;

struct MyItem {
    val: i32,
    link: UnsafeCell<DListNode<MyItem, ()>>,
}

impl MyItem {
    fn new(val: i32) -> Self {
        Self {
            val,
            link: UnsafeCell::new(DListNode::default()),
        }
    }
}

unsafe impl DListItem<()> for MyItem {
    fn get_node(&self) -> &mut DListNode<Self, ()> {
        unsafe { &mut *self.link.get() }
    }
}

let mut list = DLinkedList::<Box<MyItem>, ()>::new();
list.push_back(Box::new(MyItem::new(10)));
list.push_back(Box::new(MyItem::new(20)));

assert_eq!(list.pop_front().unwrap().val, 10);
assert_eq!(list.pop_front().unwrap().val, 20);
```
