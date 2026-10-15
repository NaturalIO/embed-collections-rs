use super::*;
use core::fmt::Debug;
use core::ops::Deref;
use pointers::{CloneablePointer, Pointer};

/// Result of a search operation in an [`AvlTree`].
pub enum Entry<'a, P, Tag, K>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    Vacant(VacantEntry<'a, P, Tag, K>),
    Occupied(OccupiedEntry<'a, P, Tag>),
}

impl<'a, P, Tag, K> Entry<'a, P, Tag, K>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    #[inline]
    pub fn unwrap_occupied(self) -> OccupiedEntry<'a, P, Tag>
    where
        K: Debug,
    {
        match self {
            Self::Occupied(ent) => ent,
            Self::Vacant(ent) => {
                panic!("called unwrap_occupied on vacent entry {:?}", ent.key);
            }
        }
    }

    #[inline]
    pub fn unwrap_vacant(self) -> VacantEntry<'a, P, Tag, K>
    where
        P::Target: Debug,
    {
        match self {
            Self::Vacant(ent) => ent,
            Self::Occupied(ent) => {
                panic!("called unwrap_occupied on vacent entry {:?}", ent.as_ref());
            }
        }
    }
}

pub struct OccupiedEntry<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    /// The matching node or the parent for insertion.
    pub(crate) node: NonNull<P::Target>,
    pub(crate) tree: &'a mut AvlTree<P, Tag>,
}

impl<'a, P, Tag> OccupiedEntry<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    #[inline]
    pub fn get(&self) -> &'a P::Target {
        unsafe { self.node.as_ref() }
    }

    #[inline]
    pub fn clone_ref(&self) -> P
    where
        P: CloneablePointer,
    {
        unsafe { CloneablePointer::from_raw_and_clone(self.node.as_ptr()) }
    }

    /// Remove the node from the tree
    #[inline]
    pub fn remove(self) -> P {
        let p = self.node.as_ptr();
        unsafe {
            self.tree._remove(p);
            P::from_raw(p)
        }
    }

    /// Remove the next node if it exists and return the reference, without changing the current position.
    #[inline]
    pub fn remove_prev(&mut self) -> Option<P> {
        if let Some(prev) = self.tree._walk_dir(self.node, DIR_LEFT) {
            unsafe {
                self.tree._remove(prev.as_ptr());
                return Some(P::from_raw(prev.as_ptr()));
            }
        }
        None
    }

    /// Remove the next node if it exists and return the reference, without changing the current position.
    #[inline]
    pub fn remove_next(&mut self) -> Option<P> {
        if let Some(next) = self.tree._walk_dir(self.node, DIR_RIGHT) {
            unsafe {
                self.tree._remove(next.as_ptr());
                return Some(P::from_raw(next.as_ptr()));
            }
        }
        None
    }

    #[inline]
    pub fn peek_prev(&self) -> Option<&'a P::Target> {
        if let Some(p) = self.tree._walk_dir(self.node, DIR_LEFT) {
            Some(unsafe { p.as_ref() })
        } else {
            None
        }
    }

    #[inline]
    pub fn peek_next(&self) -> Option<&'a P::Target> {
        if let Some(p) = self.tree._walk_dir(self.node, DIR_RIGHT) {
            Some(unsafe { p.as_ref() })
        } else {
            None
        }
    }

    #[inline]
    pub fn move_prev(mut self) -> Option<Self> {
        if let Some(p) = self.tree._walk_dir(self.node, DIR_LEFT) {
            self.node = p;
            Some(self)
        } else {
            None
        }
    }

    #[inline]
    pub fn move_next(mut self) -> Option<Self> {
        if let Some(p) = self.tree._walk_dir(self.node, DIR_RIGHT) {
            self.node = p;
            Some(self)
        } else {
            None
        }
    }

    /// Insert before the current node.
    /// The entry position is unchanged.
    ///
    /// # Safety
    ///
    /// Caller should make sure the new_node is exactly before the current node.
    ///
    /// otherwise the new_node is way smaller than its ancestor
    /// (with value not adjacent to current node) will break the tree total ordering.
    #[inline]
    pub unsafe fn insert_prev_unchecked(&mut self, new_node: P) {
        unsafe {
            let new_ptr = new_node.into_raw() as *mut P::Target;
            self.tree._insert_here(new_ptr, self.node, DIR_LEFT);
        }
    }

    /// Insert before the current node,
    /// with entry position is changed to newly inserted node.
    ///
    /// # Safety
    ///
    /// Caller should make sure the new_node is exactly before the current node.
    ///
    /// otherwise the new_node is way smaller than its ancestor
    /// (with value not adjacent to current node) will break the tree total ordering.
    #[inline]
    pub unsafe fn insert_move_prev_unchecked(self, new_node: P) -> Self {
        unsafe {
            let new_ptr = new_node.into_raw() as *mut P::Target;
            self.tree._insert_here(new_ptr, self.node, DIR_LEFT);
            Self { node: NonNull::new_unchecked(new_ptr), tree: self.tree }
        }
    }

    /// Insert after the current node.
    /// The entry position is unchanged.
    ///
    /// # Safety
    ///
    /// Caller should make sure the new_node is exactly after the current node.
    ///
    /// Otherwise the new_node is way smaller than its ancestor
    /// (with value not adjacent to current node) will break the tree total ordering.
    #[inline]
    pub unsafe fn insert_next_unchecked(&mut self, new_node: P) {
        unsafe {
            let new_ptr = new_node.into_raw() as *mut P::Target;
            self.tree._insert_here(new_ptr, self.node, DIR_RIGHT);
        }
    }

    /// Insert after the current node,
    /// with entry position is changed to newly inserted node.
    ///
    /// # Safety
    ///
    /// Caller should make sure the new_node is exactly after the current node.
    ///
    /// Otherwise the new_node is way smaller than its ancestor
    /// (with value not adjacent to current node) will break the tree total ordering.
    #[inline]
    pub unsafe fn insert_move_next_unchecked(self, new_node: P) -> Self {
        unsafe {
            let new_ptr = new_node.into_raw() as *mut P::Target;
            self.tree._insert_here(new_ptr, self.node, DIR_RIGHT);
            Self { node: NonNull::new_unchecked(new_ptr), tree: self.tree }
        }
    }
}

impl<'a, P, Tag> Deref for OccupiedEntry<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    type Target = P::Target;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a, P, Tag> AsRef<P::Target> for OccupiedEntry<'a, P, Tag>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    #[inline]
    fn as_ref(&self) -> &P::Target {
        Self::get(self)
    }
}

/// # Examples
///
/// ```rust
/// use embed_avl::{AvlTree, AvlItem, AvlNode, Entry};
/// use core::cell::UnsafeCell;
/// use core::borrow::Borrow;
/// extern crate alloc;
/// use alloc::sync::Arc;
///
/// struct MyNode {
///     value: i32,
///     avl_node: UnsafeCell<AvlNode<MyNode, ()>>,
/// }
///
/// unsafe impl AvlItem<()> for MyNode {
///
///     fn get_node(&self) -> &mut AvlNode<MyNode, ()> {
///         unsafe { &mut *self.avl_node.get() }
///     }
/// }
/// impl Borrow<i32> for MyNode {
///     fn borrow(&self) -> &i32 {
///         &self.value
///     }
/// }
///
/// let mut tree = AvlTree::<Arc<MyNode>, ()>::new();
/// let key = 42;
/// if let Entry::Vacant(ent) = tree.entry(key) {
///     ent.insert_node(Arc::new(MyNode {
///         value: key,
///         avl_node: UnsafeCell::new(Default::default()),
///     }));
/// }
/// ```
pub struct VacantEntry<'a, P, Tag, K>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    pub(crate) node: *mut P::Target,
    pub(crate) direction: Dir,
    pub(crate) tree: &'a mut AvlTree<P, Tag>,
    pub(crate) key: K,
}

impl<'a, P, Tag, K> VacantEntry<'a, P, Tag, K>
where
    P: Pointer,
    P::Target: AvlItem<Tag>,
{
    /// Return the nearest node in the search result
    #[inline(always)]
    pub fn nearest(&self) -> Option<&P::Target> {
        if !self.node.is_null() { unsafe { self.node.as_ref() } } else { None }
    }

    #[inline]
    pub fn peek_prev(&self) -> Option<&P::Target> {
        if !self.node.is_null() {
            unsafe {
                if self.direction == DIR_RIGHT {
                    return Some(&*self.node);
                } else if let Some(node) =
                    self.tree._walk_dir(NonNull::new_unchecked(self.node), DIR_LEFT)
                {
                    return Some(node.as_ref());
                }
            }
        }
        None
    }

    #[inline]
    pub fn key(&self) -> &K {
        &self.key
    }

    #[inline]
    pub fn peek_next(&self) -> Option<&P::Target> {
        if !self.node.is_null() {
            unsafe {
                if self.direction == DIR_LEFT {
                    return Some(&*self.node);
                } else if let Some(node) =
                    self.tree._walk_dir(NonNull::new_unchecked(self.node), DIR_RIGHT)
                {
                    return Some(node.as_ref());
                }
            }
        }
        None
    }

    #[inline]
    pub fn move_prev(self) -> Option<OccupiedEntry<'a, P, Tag>> {
        if !self.node.is_null() {
            unsafe {
                let p = NonNull::new_unchecked(self.node);
                if self.direction == DIR_RIGHT {
                    return Some(OccupiedEntry { node: p, tree: self.tree });
                } else if let Some(node) = self.tree._walk_dir(p, DIR_LEFT) {
                    return Some(OccupiedEntry { node, tree: self.tree });
                }
            }
        }
        None
    }

    #[inline]
    pub fn move_next(self) -> Option<OccupiedEntry<'a, P, Tag>> {
        if !self.node.is_null() {
            unsafe {
                let p = NonNull::new_unchecked(self.node);
                if self.direction == DIR_LEFT {
                    return Some(OccupiedEntry { node: p, tree: self.tree });
                } else if let Some(node) = self.tree._walk_dir(p, DIR_RIGHT) {
                    return Some(OccupiedEntry { node, tree: self.tree });
                }
            }
        }
        None
    }

    /// # Safety
    ///
    /// Caller should make sure `new_node` have the same value to the search key to `entry()`,
    ///
    /// ignoring `K` captured in VacantEntry
    #[inline]
    pub unsafe fn insert_node_unchecked(self, new_node: P) -> OccupiedEntry<'a, P, Tag> {
        let new_ptr = new_node.into_raw() as *mut P::Target;
        self.tree._insert(new_ptr, self.node, self.direction);
        OccupiedEntry { node: unsafe { NonNull::new_unchecked(new_ptr) }, tree: self.tree }
    }
}

impl<'a, P, Tag, K> VacantEntry<'a, P, Tag, K>
where
    P: Pointer,
    P::Target: AvlItem<Tag> + Borrow<K>,
    K: PartialEq,
{
    /// insert new_node at the position, for entry search by borrowed key
    ///
    /// # Safety
    ///
    /// We have debug_assert_eq the key an the node
    #[inline]
    pub fn insert_node(self, new_node: P) -> OccupiedEntry<'a, P, Tag> {
        debug_assert!(&self.key == new_node.as_ref().borrow());
        let new_ptr = new_node.into_raw() as *mut P::Target;
        self.tree._insert(new_ptr, self.node, self.direction);
        OccupiedEntry { node: unsafe { NonNull::new_unchecked(new_ptr) }, tree: self.tree }
    }
}
