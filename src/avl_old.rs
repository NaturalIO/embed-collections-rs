use std::{
    cell::UnsafeCell,
    cmp::{Ordering, PartialEq},
    fmt,
    sync::{Arc, Weak},
};

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum AvlDirection {
    Left = 0,
    Right = 1,
}

impl AvlDirection {
    #[inline(always)]
    fn reverse(self) -> AvlDirection {
        match self {
            AvlDirection::Left => AvlDirection::Right,
            AvlDirection::Right => AvlDirection::Left,
        }
    }
}

pub struct AvlNodeRef<T>(pub Arc<UnsafeCell<T>>);

unsafe impl<T> Send for AvlNodeRef<T> {}
unsafe impl<T> Sync for AvlNodeRef<T> {}

pub struct AvlNodeRefWeak<T>(pub Weak<UnsafeCell<T>>);

unsafe impl<T> Send for AvlNodeRefWeak<T> {}
unsafe impl<T> Sync for AvlNodeRefWeak<T> {}

impl<T> AvlNodeRefWeak<T> {
    #[inline(always)]
    pub fn upgrade(&self) -> AvlNodeRef<T> {
        AvlNodeRef(self.0.upgrade().unwrap())
    }

    #[inline(always)]
    fn as_raw(&self) -> *const T {
        unsafe { std::mem::transmute(self.0.as_ptr()) } // require nightly feature(weak_into_raw)
    }
}

macro_rules! try_weak_option {
    ( $expr: expr ) => {
        match $expr.as_ref() {
            Some(item) => Some(item.upgrade()),
            None => None,
        }
    };
}

macro_rules! avlchild_to_balance {
    ( $dir: expr ) => {
        match $dir {
            AvlDirection::Left => -1,
            AvlDirection::Right => 1,
        }
    };
}

// Cloning a `NodeRef` only increments a reference count. It does not copy the data.
impl<T> Clone for AvlNodeRef<T> {
    #[inline(always)]
    fn clone(&self) -> AvlNodeRef<T> {
        AvlNodeRef(self.0.clone())
    }
}

impl<T> std::ops::Deref for AvlNodeRef<T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        self.borrow()
    }
}

impl<T: fmt::Debug> fmt::Debug for AvlNodeRef<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.borrow(), f)
    }
}

impl<T> PartialEq for AvlNodeRef<T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        return Arc::ptr_eq(&self.0, &other.0);
    }
}

impl<T> AvlNodeRef<T> {
    #[inline(always)]
    pub fn downgrade(&self) -> AvlNodeRefWeak<T> {
        AvlNodeRefWeak(Arc::downgrade(&self.0))
    }

    #[inline(always)]
    pub fn borrow_mut<'a>(&'a self) -> &'a mut T {
        unsafe { std::mem::transmute(self.0.get() as *const T) }
    }

    #[inline(always)]
    pub fn borrow<'a>(&'a self) -> &'a T {
        unsafe { std::mem::transmute::<*mut T, &'a T>(self.0.get()) }
    }

    #[inline(always)]
    pub fn as_raw(&self) -> *const T {
        self.0.get() as *const T
    }
}

pub struct AvlNode<T> {
    pub left: Option<AvlNodeRef<T>>,
    pub right: Option<AvlNodeRef<T>>,
    pub parent: Option<AvlNodeRefWeak<T>>,
    pub balance: i8,
}

impl<T> Default for AvlNode<T> {
    fn default() -> Self {
        Self { left: None, right: None, parent: None, balance: 0 }
    }
}

impl<T> AvlNode<T> {
    #[inline(always)]
    pub fn detach(&mut self) {
        self.left = None;
        self.right = None;
        self.parent = None;
        self.balance = 0;
    }

    #[inline(always)]
    fn get_child(&self, dir: AvlDirection) -> Option<AvlNodeRef<T>> {
        match dir {
            AvlDirection::Left => match self.left {
                Some(ref left) => return Some(left.clone()),
                None => return None,
            },
            AvlDirection::Right => match self.right {
                Some(ref right) => return Some(right.clone()),
                None => return None,
            },
        }
    }

    #[inline(always)]
    fn take_child(&mut self, dir: AvlDirection) -> Option<AvlNodeRef<T>> {
        match dir {
            AvlDirection::Left => self.left.take(),
            AvlDirection::Right => self.right.take(),
        }
    }

    #[inline(always)]
    fn get_child_ref(&self, dir: AvlDirection) -> Option<&AvlNodeRef<T>> {
        match dir {
            AvlDirection::Left => self.left.as_ref(),
            AvlDirection::Right => self.right.as_ref(),
        }
    }

    #[inline(always)]
    fn set_child(&mut self, dir: AvlDirection, child: Option<AvlNodeRef<T>>) {
        match dir {
            AvlDirection::Left => self.left = child,
            AvlDirection::Right => self.right = child,
        }
    }

    #[inline(always)]
    fn get_parent(&self) -> Option<AvlNodeRef<T>> {
        return try_weak_option!(self.parent);
    }

    // Swap two node but not there value
    #[inline(always)]
    pub fn swap(&mut self, other: &mut AvlNode<T>) {
        std::mem::swap(&mut self.left, &mut other.left);
        std::mem::swap(&mut self.right, &mut other.right);
        std::mem::swap(&mut self.parent, &mut other.parent);
        std::mem::swap(&mut self.balance, &mut other.balance);
    }
}

#[allow(unused_must_use)]
impl<T: fmt::Debug + fmt::Display> fmt::Debug for AvlNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(");

        if let Some(ref left) = self.left {
            write!(f, "left: {:p} [{}]", left, left);
        } else {
            write!(f, "left: none ");
        }

        if let Some(ref right) = self.right {
            write!(f, "right: {:p} [{}]", right, right);
        } else {
            write!(f, "right: none ");
        }
        write!(f, ")")
    }
}

#[allow(unused_must_use)]
impl<T: fmt::Display> fmt::Display for AvlNodeRef<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let t = self.borrow();
        fmt::Display::fmt(&t, f)
    }
}

pub type AvlCmpNodeFunc<T> = fn(&T, &AvlNodeRef<T>) -> Ordering;
pub type AvlCmpFunc<K, T> = fn(&K, &AvlNodeRef<T>) -> Ordering;
pub type AvlSubFunc<K, T> = fn(&K, &AvlNodeRef<T>) -> i64;

pub struct AvlTree<T> {
    pub root: Option<AvlNodeRef<T>>,
    count: i64,
    node_offset: usize,
}

#[derive(Debug)]
pub struct AvlSearchResult<T> {
    node: Option<AvlNodeRef<T>>,
    pub direction: Option<AvlDirection>,
}

impl<T> Default for AvlSearchResult<T> {
    fn default() -> AvlSearchResult<T> {
        AvlSearchResult { node: None, direction: Some(AvlDirection::Left) }
    }
}

impl<T> AvlSearchResult<T> {
    #[inline(always)]
    pub fn get_exact(&self) -> Option<AvlNodeRef<T>> {
        if self.direction.is_none() {
            if self.node.is_none() {
                return None;
            } else {
                return self.node.clone();
            }
        }
        None
    }

    #[inline(always)]
    pub fn into_exact(mut self) -> Option<AvlNodeRef<T>> {
        if self.direction.is_none() {
            if self.node.is_none() {
                return None;
            } else {
                return self.node.take();
            }
        }
        None
    }

    #[inline(always)]
    pub fn get_node_ref(&self) -> Option<&AvlNodeRef<T>> {
        return self.node.as_ref();
    }
}

macro_rules! return_end {
    ($tree: expr, $dir: expr) => {{
        match $tree.root {
            None => return None,
            Some(ref data) => return Some($tree.bottom_child_ref(data, $dir).clone()),
        }
    }};
}

macro_rules! balance_to_child {
    ($balance: expr) => {
        match $balance {
            0 | 1 => AvlDirection::Left,
            _ => AvlDirection::Right,
        }
    };
}

impl<T: std::fmt::Debug> AvlTree<T> {
    pub fn new(node_offset: usize) -> AvlTree<T> {
        AvlTree { count: 0, root: None, node_offset }
    }

    //    #[inline(always)]
    //    fn node_to_data<'a>(&self, node: &'a AvlNode<T>) -> &'a T {
    //        unsafe {
    //            let off = node as *const AvlNode<T> as usize + self.node_offset;
    //            std::mem::transmute::<usize, &'a T>(off)
    //        }
    //    }

    #[inline(always)]
    fn to_node<'a>(&self, data: &'a AvlNodeRef<T>) -> &'a AvlNode<T> {
        // Avoid borrow as much as possible
        let off = data.0.get() as *const T as usize + self.node_offset;
        unsafe { std::mem::transmute::<usize, &'a AvlNode<T>>(off) }
    }

    #[inline(always)]
    unsafe fn to_node_raw(&self, data: &AvlNodeRef<T>) -> *mut AvlNode<T> {
        let off = data.0.get() as *const T as usize + self.node_offset;
        return off as *mut AvlNode<T>;
    }

    #[inline(always)]
    unsafe fn to_node_from_raw(&self, data: *const T) -> *mut AvlNode<T> {
        let off = data as usize + self.node_offset;
        return off as *mut AvlNode<T>;
    }

    //    #[inline(always)]
    //    fn node_to_data_mut<'a>(&self, node: &'a mut AvlNode<T>) -> &'a mut T {
    //        unsafe {
    //            let off = node as *mut AvlNode<T> as usize + self.node_offset;
    //            std::mem::transmute::<usize, &'a mut T>(off)
    //        }
    //    }

    #[inline(always)]
    fn to_node_mut<'a>(&self, data: &'a AvlNodeRef<T>) -> &'a mut AvlNode<T> {
        let off = data.0.get() as *const T as usize + self.node_offset;
        unsafe { std::mem::transmute::<usize, &'a mut AvlNode<T>>(off) }
    }

    pub fn get_count(&self) -> i64 {
        return self.count;
    }

    pub fn first(&self) -> Option<AvlNodeRef<T>> {
        return_end!(self, AvlDirection::Left)
    }

    #[inline]
    pub fn last(&self) -> Option<AvlNodeRef<T>> {
        return_end!(self, AvlDirection::Right)
    }

    #[inline]
    pub fn insert(&mut self, new_data: AvlNodeRef<T>, w: AvlSearchResult<T>) {
        debug_assert!(w.direction.is_some());
        self._insert(new_data, w.node.as_ref(), w.direction.unwrap());
    }

    pub fn _insert(
        &mut self, new_data: AvlNodeRef<T>, here: Option<&AvlNodeRef<T>>,
        mut which_child: AvlDirection,
    ) {
        let mut new_balance: i8;

        match here {
            None => {
                if self.count > 0 {
                    panic!("insert into a tree size {} with empty where.node", self.count);
                }
                self.root = Some(new_data);
                self.count += 1;
                return;
            }
            Some(parent) => {
                let node: &mut AvlNode<T> = self.to_node_mut(&new_data);
                let parent_node = self.to_node_mut(parent);
                //debug_assert!(None == parent_node.get_child(which_child));
                node.parent = Some(parent.downgrade());
                let _ = node; // prevent borrowing new_data
                parent_node.set_child(which_child, Some(new_data));
                self.count += 1;

                /*
                ┆* Now, back up the tree modifying the balance of all nodes above the
                ┆* insertion point. If we get to a highly unbalanced ancestor, we
                ┆* need to do a rotation.  If we back out of the tree we are done.
                ┆* If we brought any subtree into perfect balance (0), we are also done.
                ┆*/
                let mut data: AvlNodeRef<T> = parent.clone();
                loop {
                    let node = self.to_node_mut(&data);
                    let old_balance = node.balance;
                    new_balance = old_balance + avlchild_to_balance!(which_child);
                    if new_balance == 0 {
                        node.balance = 0;
                        return;
                    }
                    if old_balance != 0 {
                        self.rotate(data, new_balance);
                        return;
                    }
                    node.balance = new_balance;
                    match node.get_parent() {
                        None => return,
                        Some(_parent) => {
                            which_child = self.parent_direction(&data, Some(&_parent));
                            data = _parent;
                        }
                    }
                }
            }
        }
    }

    pub fn insert_here(
        &mut self, new_data: AvlNodeRef<T>, here: &AvlNodeRef<T>, direction: AvlDirection,
    ) {
        let mut dir_child = direction;
        /*
        let _cmp = self.cmp_func;
        { // XXX debug_assert ?
            let data_ref = new_data.borrow();
            let diff = _cmp(data_ref, &here);
            debug_assert!(diff != Ordering::Equal);
            if diff == Ordering::Less {
                debug_assert!(dir_child == AvlDirection::Left);
            } else {
                debug_assert!(dir_child == AvlDirection::Right);
            }
        }
        */
        let child = self.to_node(here).get_child_ref(dir_child);
        if let Some(_data_exists) = child {
            dir_child = dir_child.reverse();
            let node = self.bottom_child_ref(&_data_exists, dir_child);
            /*
            loop {
                { // XXX debug_assert
                    let diff = _cmp(data_ref, &node);
                    if diff == Ordering::Greater {
                        assert!(dir_child == AvlDirection::Right);
                    } else {
                        assert!(dir_child == AvlDirection::Left);
                    }
                }
                let temp = self.to_node_mut(&node).get_child_ref(dir_child);
                if let Some(__node) = temp {
                    node = __node;
                    continue
                }
                break
            }
            */
            self._insert(new_data, Some(node), dir_child);
        } else {
            self._insert(new_data, Some(here), dir_child);
        }
    }

    // set child and both child's parent
    #[inline(always)]
    fn set_child2(
        &mut self, node: &mut AvlNode<T>, dir: AvlDirection, child: Option<AvlNodeRef<T>>,
        parent: &AvlNodeRef<T>,
    ) {
        if let Some(ref _child) = child {
            self.to_node_mut(&_child).parent = Some(parent.downgrade());
        }
        node.set_child(dir, child);
    }

    #[inline(always)]
    fn parent_direction(
        &self, data: &AvlNodeRef<T>, parent: Option<&AvlNodeRef<T>>,
    ) -> AvlDirection {
        if let Some(_parent) = parent {
            unsafe {
                let (_, dir) = self._parent_direction_raw(data.as_raw(), _parent.as_raw());
                return dir;
            }
        }
        // this just follow zfs
        AvlDirection::Left
    }

    #[inline(always)]
    unsafe fn _parent_direction_raw(
        &self, data_raw: *const T, parent_raw: *const T,
    ) -> (*const AvlNode<T>, AvlDirection) {
        unsafe {
            let parent_node = self.to_node_from_raw(parent_raw);
            if let Some(ref left) = (*parent_node).left {
                if left.as_raw() == data_raw {
                    return (parent_node, AvlDirection::Left);
                }
            }
            if let Some(ref right) = (*parent_node).right {
                if right.as_raw() == data_raw {
                    return (parent_node, AvlDirection::Right);
                }
            }
            panic!("invalid avl tree, node {:#?}, parent {:#?}", (*data_raw), (*parent_raw));
        }
    }

    #[inline(always)]
    fn parent_direction2(&self, data: &AvlNodeRef<T>) -> AvlDirection {
        let node = self.to_node(data);
        if let Some(ref _parent) = node.parent {
            unsafe {
                let (_, dir) = self._parent_direction_raw(data.as_raw(), _parent.as_raw());
                return dir;
            }
        }
        // this just follow zfs
        AvlDirection::Left
    }

    #[inline]
    fn rotate(&mut self, data: AvlNodeRef<T>, balance: i8) -> bool {
        let dir: AvlDirection;
        if balance < 0 {
            dir = AvlDirection::Left;
        } else {
            dir = AvlDirection::Right;
        }
        let node: &mut AvlNode<T> = self.to_node_mut(&data);

        let parent = node.get_parent();
        let dir_inverse = dir.reverse();
        let left_heavy = balance >> 1;
        let right_heavy = -left_heavy;
        let child = node.take_child(dir);
        let _child = child.unwrap();
        let child_node: &mut AvlNode<T> = self.to_node_mut(&_child);
        let mut child_balance = child_node.balance;

        let which_child = self.parent_direction(&data, parent.as_ref());

        // node is overly left heavy, the left child is balanced or also left heavy.
        if child_balance != right_heavy {
            child_balance += right_heavy;

            let c_right = child_node.take_child(dir_inverse);
            self.set_child2(node, dir, c_right, &data);
            // move node to be child's right child
            node.balance = -child_balance;

            node.parent = Some(_child.downgrade());
            let _ = node;
            child_node.set_child(dir_inverse, Some(data));
            // update the pointer into this subtree

            child_node.balance = child_balance;
            if let Some(ref _parent) = parent {
                child_node.parent = Some(_parent.downgrade());
                self.to_node_mut(&_parent).set_child(which_child, Some(_child));
            } else {
                child_node.parent = None;
                self.root = Some(_child);
            }
            return child_balance == 0;
        }
        // When node is left heavy, but child is right heavy we use
        // a different rotation.

        let g_child = child_node.take_child(dir_inverse);
        let _g_child = g_child.unwrap();
        let g_child_node = self.to_node_mut(&_g_child);
        let g_left = g_child_node.take_child(dir);
        let g_right = g_child_node.take_child(dir_inverse);

        self.set_child2(node, dir, g_right, &data);
        self.set_child2(child_node, dir_inverse, g_left, &_child);

        /*
         * move child to left child of gchild and
         * move node to right child of gchild and
         * fixup parent of all this to point to gchild
         */

        let g_child_balance = g_child_node.balance;
        if g_child_balance == right_heavy {
            child_node.balance = left_heavy;
        } else {
            child_node.balance = 0;
        }
        child_node.parent = Some(_g_child.downgrade());
        g_child_node.set_child(dir, Some(_child));

        if g_child_balance == left_heavy {
            node.balance = right_heavy;
        } else {
            node.balance = 0;
        }
        g_child_node.balance = 0;

        node.parent = Some(_g_child.downgrade());
        g_child_node.set_child(dir_inverse, Some(data));

        if let Some(mut _parent) = parent {
            g_child_node.parent = Some(_parent.downgrade());
            self.to_node_mut(&_parent).set_child(which_child, Some(_g_child));
        } else {
            g_child_node.parent = None;
            self.root = Some(_g_child);
        }
        return true;
    }

    pub fn replace(&mut self, old: &AvlNodeRef<T>, node: AvlNodeRef<T>) {
        let old_node = self.to_node_mut(old);
        let new_node = self.to_node_mut(&node);
        if let Some(left) = old_node.take_child(AvlDirection::Left) {
            self.set_child2(new_node, AvlDirection::Left, Some(left), &node);
        }
        if let Some(right) = old_node.take_child(AvlDirection::Right) {
            self.set_child2(new_node, AvlDirection::Right, Some(right), &node);
        }
        new_node.balance = old_node.balance;
        old_node.balance = 0;
        if let Some(parent) = old_node.get_parent() {
            let dir = self.parent_direction(old, Some(&parent));
            self.set_child2(self.to_node_mut(&parent), dir, Some(node), &parent);
            old_node.parent = None;
        } else {
            debug_assert_eq!(self.root.as_ref(), Some(old));
            self.root = Some(node);
        }
    }

    pub fn remove(&mut self, del: &AvlNodeRef<T>) {
        /*
        ┆* Deletion is easiest with a node that has at most 1 child.
        ┆* We swap a node with 2 children with a sequentially valued
        ┆* neighbor node. That node will have at most 1 child. Note this
        ┆* has no effect on the ordering of the remaining nodes.
        ┆*
        ┆* As an optimization, we choose the greater neighbor if the tree
        ┆* is right heavy, otherwise the left neighbor. This reduces the
        ┆* number of rotations needed.
        ┆*/
        if self.count == 0 {
            return;
        } else if self.count == 1 && self.root.as_ref().unwrap() == del {
            self.root = None;
            self.count = 0;
            self.to_node_mut(del).detach();
            return;
        }
        let mut which_child: AvlDirection;
        let imm_data: Option<AvlNodeRef<T>>;
        let parent: Option<AvlNodeRef<T>>;
        let del_node = self.to_node_mut(del);

        let node_swap_flag: bool;
        node_swap_flag = del_node.left.is_some() && del_node.right.is_some();

        if node_swap_flag {
            let dir: AvlDirection;
            let dir_child_temp: AvlDirection;
            let dir_child_del: AvlDirection;
            let dir_inverse: AvlDirection;
            dir = balance_to_child!(del_node.balance + 1);
            let child: AvlNodeRef<T>;
            {
                let child_temp = &del_node.get_child_ref(dir).unwrap();

                dir_inverse = dir.reverse();
                let _child = self.bottom_child_ref(child_temp, dir_inverse);
                dir_child_temp = self.parent_direction2(&_child);
                dir_child_del = self.parent_direction2(del);
                child = _child.clone();
                self.to_node_mut(&child).swap(del_node);

                // move 'node' to delete's spot in the tree
            }
            let child_node = self.to_node_mut(&child);
            if child_node.get_child_ref(dir).unwrap() == &child {
                // if node(d) left child is node(c)
                child_node.set_child(dir, Some(del.clone()));
            }

            self.to_node_mut(child_node.get_child_ref(dir).unwrap()).parent =
                Some(child.downgrade());
            self.to_node_mut(child_node.get_child_ref(dir_inverse).unwrap()).parent =
                Some(child.downgrade());

            let parent = child_node.get_parent();
            if let Some(_parent) = parent {
                self.to_node_mut(&_parent).set_child(dir_child_del, Some(child));
            } else {
                self.root = Some(child);
            }

            // Put tmp where node used to be (just temporary).
            // It always has a parent and at most 1 child.

            let mut _parent = del_node.get_parent().unwrap();
            self.to_node_mut(&_parent).set_child(dir_child_temp, Some(del.clone()));
            if del_node.right.is_some() {
                which_child = AvlDirection::Right;
            } else {
                which_child = AvlDirection::Left;
            }
            if let Some(_child) = del_node.get_child_ref(which_child) {
                self.to_node_mut(_child).parent = Some(del.downgrade());
            }
            which_child = dir_child_temp;
        } else {
            which_child = self.parent_direction2(del);
        }

        // Here we know "delete" is at least partially a leaf node. It can
        // be easily removed from the tree.

        parent = del_node.get_parent();

        if del_node.left.is_some() {
            imm_data = del_node.take_child(AvlDirection::Left);
        } else {
            imm_data = del_node.take_child(AvlDirection::Right);
        }

        // Connect parent directly to node (leaving out delete).

        if let Some(ref _imm_data) = imm_data {
            let imm_node = self.to_node_mut(&_imm_data);
            // TODO optimise parent
            if let Some(_parent) = parent.as_ref() {
                imm_node.parent = Some(_parent.downgrade());
            } else {
                imm_node.parent = None;
            }
        }
        if let Some(_parent) = parent {
            assert!(self.count > 0);
            self.count -= 1;

            let parent_node = self.to_node_mut(&_parent);
            parent_node.set_child(which_child, imm_data);

            //Since the subtree is now shorter, begin adjusting parent balances
            //and performing any needed rotations.

            let mut _node_data: AvlNodeRef<T> = _parent;
            let mut old_balance: i8;
            let mut new_balance: i8;
            loop {
                // Move up the tree and adjust the balance.
                // Capture the parent and which_child values for the next
                // iteration before any rotations occur.

                let _node = self.to_node_mut(&_node_data);
                old_balance = _node.balance;
                new_balance = old_balance - avlchild_to_balance!(which_child);

                //If a node was in perfect balance but isn't anymore then
                //we can stop, since the height didn't change above this point
                //due to a deletion.

                if old_balance == 0 {
                    _node.balance = new_balance;
                    break;
                }

                let __parent = _node.get_parent();
                which_child = self.parent_direction(&_node_data, __parent.as_ref());

                //If the new balance is zero, we don't need to rotate
                //else
                //need a rotation to fix the balance.
                //If the rotation doesn't change the height
                //of the sub-tree we have finished adjusting.

                if new_balance == 0 {
                    _node.balance = new_balance;
                } else if !self.rotate(_node_data, new_balance) {
                    break;
                }
                if __parent.is_some() {
                    _node_data = __parent.unwrap();
                    continue;
                }
                break;
            }
        } else {
            if imm_data.is_some() {
                assert!(self.count > 0);
                self.count -= 1;
                self.root = imm_data;
            }
        }
        if self.root.is_none() {
            if self.count > 0 {
                panic!("AvlTree {} nodes left after remove but tree.root == nil", self.count);
            }
        }
        del_node.detach();
    }

    // When found node equal to value, return (Some(node), None);
    // otherwise return (Some(node), direction) to indicate where to insert
    pub fn find<'a, K>(&'a self, val: &'a K, cmp_func: AvlCmpFunc<K, T>) -> AvlSearchResult<T> {
        if self.root.is_none() {
            return AvlSearchResult::default();
        }
        let mut node_data = self.root.as_ref().unwrap();
        loop {
            let diff = cmp_func(val, node_data);
            match diff {
                Ordering::Equal => {
                    return AvlSearchResult { node: Some(node_data.clone()), direction: None };
                }
                Ordering::Less => {
                    let node = self.to_node(&node_data);
                    let left = node.get_child_ref(AvlDirection::Left);
                    if left.is_none() {
                        return AvlSearchResult {
                            node: Some(node_data.clone()),
                            direction: Some(AvlDirection::Left),
                        };
                    }
                    node_data = left.unwrap();
                }
                Ordering::Greater => {
                    let node = self.to_node(&node_data);
                    let right = node.get_child_ref(AvlDirection::Right);
                    if right.is_none() {
                        return AvlSearchResult {
                            node: Some(node_data.clone()),
                            direction: Some(AvlDirection::Right),
                        };
                    }
                    node_data = right.unwrap();
                }
            }
        }
    }

    // for range tree, val may overlap multiple range(node), ensure return the smallest
    pub(crate) fn find_contained<'a, K>(
        &'a self, val: &'a K, cmp_func: AvlCmpFunc<K, T>,
    ) -> Option<AvlNodeRef<T>> {
        if self.root.is_none() {
            return None;
        }
        let mut node_data = self.root.as_ref().unwrap();
        let mut result_node: Option<&AvlNodeRef<T>> = None;
        loop {
            let diff = cmp_func(val, node_data);
            match diff {
                Ordering::Equal => {
                    let node = self.to_node(&node_data);
                    let left = node.get_child_ref(AvlDirection::Left);
                    result_node = Some(node_data);
                    if left.is_none() {
                        break;
                    } else {
                        node_data = left.unwrap();
                    }
                }
                Ordering::Less => {
                    let node = self.to_node(&node_data);
                    let left = node.get_child_ref(AvlDirection::Left);
                    if left.is_none() {
                        break;
                    }
                    node_data = left.unwrap();
                }
                Ordering::Greater => {
                    let node = self.to_node(&node_data);
                    let right = node.get_child_ref(AvlDirection::Right);
                    if right.is_none() {
                        break;
                    }
                    node_data = right.unwrap();
                }
            }
        }

        result_node.cloned()
    }

    // for slab, return any block larger or equal than search param
    pub fn find_larger_eq<'a, K>(
        &'a self, val: &'a K, cmp_func: AvlCmpFunc<K, T>,
    ) -> AvlSearchResult<T> {
        if self.root.is_none() {
            return AvlSearchResult::default();
        }
        let mut node_data = self.root.as_ref().unwrap();
        loop {
            let diff = cmp_func(val, &node_data);
            match diff {
                Ordering::Equal => {
                    return AvlSearchResult { node: Some(node_data.clone()), direction: None };
                }
                Ordering::Less => {
                    return AvlSearchResult { node: Some(node_data.clone()), direction: None };
                }
                Ordering::Greater => {
                    let right = self.to_node(node_data).get_child_ref(AvlDirection::Right);
                    if right.is_none() {
                        return AvlSearchResult { node: None, direction: None };
                    }
                    node_data = right.unwrap();
                }
            }
        }
    }

    pub fn find_nearest<'a, K>(
        &'a self, val: &'a K, cmp_func: AvlCmpFunc<K, T>,
    ) -> AvlSearchResult<T> {
        if self.root.is_none() {
            return AvlSearchResult::default();
        }

        let mut node_data = self.root.as_ref().unwrap();
        let mut nearest_node = None;
        loop {
            let diff = cmp_func(val, &node_data);
            match diff {
                Ordering::Equal => {
                    return AvlSearchResult { node: Some(node_data.clone()), direction: None };
                }
                Ordering::Less => {
                    nearest_node = Some(node_data.clone());
                    let left = self.to_node(node_data).get_child_ref(AvlDirection::Left);
                    if left.is_none() {
                        break;
                    }
                    node_data = left.unwrap();
                }
                Ordering::Greater => {
                    let right = self.to_node(node_data).get_child_ref(AvlDirection::Right);
                    if right.is_none() {
                        break;
                    }
                    node_data = right.unwrap();
                }
            }
        }
        return AvlSearchResult { node: nearest_node, direction: None };
    }

    #[inline(always)]
    fn bottom_child_ref<'a>(
        &self, mut data: &'a AvlNodeRef<T>, dir: AvlDirection,
    ) -> &'a AvlNodeRef<T> {
        unsafe {
            loop {
                let child = {
                    let node = self.to_node_raw(data);
                    match dir {
                        AvlDirection::Left => (*node).left.as_ref(),
                        AvlDirection::Right => (*node).right.as_ref(),
                    }
                };
                if let Some(child) = child {
                    data = child;
                } else {
                    return data;
                }
            }
        }
    }

    pub fn walk_cb<F: Fn(&AvlNodeRef<T>)>(&self, cb: F) {
        if let Some(mut node) = self.first() {
            loop {
                cb(&node);
                let next = self.walk(&node, AvlDirection::Right);
                if let Some(_node) = next {
                    node = _node;
                } else {
                    break;
                }
            }
        }
    }

    pub fn walk(&self, data: &AvlNodeRef<T>, dir: AvlDirection) -> Option<AvlNodeRef<T>> {
        let dir_inverse = dir.reverse();
        let node = self.to_node(data);
        if let Some(temp) = node.get_child_ref(dir) {
            return Some(self.bottom_child_ref(temp, dir_inverse).clone());
        } else {
            if node.parent.is_none() {
                return None;
            }
            let mut new_parent: &AvlNodeRefWeak<T> = node.parent.as_ref().unwrap();
            unsafe {
                let mut data_raw: *const T = data.as_raw();
                let mut parent_raw: *const T;
                loop {
                    parent_raw = new_parent.as_raw();
                    let (parent_node, dir) = self._parent_direction_raw(data_raw, parent_raw);
                    if dir == dir_inverse {
                        return Some(new_parent.upgrade());
                    }
                    data_raw = parent_raw;
                    let _parent = (*parent_node).parent.as_ref();
                    if _parent.is_none() {
                        return None;
                    }
                    new_parent = _parent.unwrap();
                }
            }
        }
    }

    fn validate_node(&self, data: &AvlNodeRef<T>, cmp_func: AvlCmpNodeFunc<T>) {
        let node = self.to_node(data);
        if let Some(left) = node.left.as_ref() {
            assert!(cmp_func(left.borrow(), data) != Ordering::Greater);
            assert_eq!(self.to_node(left).get_parent().unwrap(), *data);
        }
        if let Some(right) = node.right.as_ref() {
            assert!(cmp_func(right.borrow(), data) != Ordering::Less);
            assert_eq!(self.to_node(right).get_parent().unwrap(), *data);
        }
    }

    #[inline]
    pub fn nearest(
        &self, current: &AvlSearchResult<T>, direction: AvlDirection,
    ) -> Option<AvlNodeRef<T>> {
        if let Some(ref node) = current.node {
            if current.direction != None && current.direction != Some(direction) {
                return Some(node.clone());
            }
            return self.walk(node, direction);
        } else {
            return None;
        }
    }

    pub fn validate(&self, cmp_func: AvlCmpNodeFunc<T>) {
        let mut stack: Vec<AvlNodeRef<T>> =
            Vec::with_capacity(((self.get_count() + 10) as f32).log2() as usize);
        if self.root.is_none() {
            assert_eq!(self.count, 0);
            return;
        }
        let mut data = self.root.clone();
        let mut visited = 0;
        loop {
            if let Some(_data) = data {
                let node = self.to_node(&_data);
                let left = node.get_child(AvlDirection::Left);
                if left.is_some() {
                    stack.push(_data.clone());
                    data = left;
                    continue;
                }
                visited += 1;
                self.validate_node(&_data, cmp_func);
                data = node.get_child(AvlDirection::Right);
            } else if stack.len() > 0 {
                let _data = stack.pop().unwrap();
                self.validate_node(&_data, cmp_func);
                visited += 1;
                let node = self.to_node(&_data);
                data = node.get_child(AvlDirection::Right);
            } else {
                break;
            }
        }
        assert_eq!(visited, self.count);
    }

    // return added: bool
    pub fn add(&mut self, node: AvlNodeRef<T>, cmp_func: AvlCmpNodeFunc<T>) -> bool {
        if self.count == 0 && self.root.is_none() {
            self.root.replace(node);
            self.count = 1;
            return true;
        }
        let w: AvlSearchResult<T> = self.find(node.borrow(), cmp_func);
        if w.direction.is_none() {
            return false;
        }
        self.insert(node, w);
        return true;
    }

    /*
    pub fn add_dup(&mut self, node: &AvlNodeRef<T>) -> bool {
        let w: AvlSearchResult<T> = self.find_indentical(node);
        if w.direction.is_none() {
            return false
        }
        self.insert(node, w);
        true
    }
    */
}

#[cfg(test)]
mod tests {

    extern crate rand;
    //extern crate cpuprofiler;
    //use self::cpuprofiler::PROFILER;
    use std::mem::offset_of;
    use std::time::Instant;

    use super::*;

    struct IntAvlNode {
        pub value: i64,
        pub node: AvlNode<Self>,
    }

    impl fmt::Debug for IntAvlNode {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{} {:#?}", self.value, self.node)
        }
    }

    impl fmt::Display for IntAvlNode {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.value)
        }
    }

    type IntAvlTree = AvlTree<IntAvlNode>;

    fn new_intnode(i: i64) -> AvlNodeRef<IntAvlNode> {
        AvlNodeRef(Arc::new(UnsafeCell::new(IntAvlNode { node: AvlNode::default(), value: i })))
    }

    fn new_intnode_raw(i: i64) -> IntAvlNode {
        IntAvlNode { value: i, node: AvlNode::default() }
    }

    fn new_inttree() -> IntAvlTree {
        let off = offset_of!(IntAvlNode, node);
        AvlTree::<IntAvlNode>::new(off)
    }

    fn cmp_int_node(a: &IntAvlNode, b: &AvlNodeRef<IntAvlNode>) -> Ordering {
        let _a: i64 = a.value;
        let _b: i64 = b.borrow().value;
        if _a < _b {
            Ordering::Less
        } else if _a > _b {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }

    fn cmp_int(a: &i64, b: &AvlNodeRef<IntAvlNode>) -> Ordering {
        let _a: i64 = *a;
        let _b: i64 = b.borrow().value;
        if _a < _b {
            Ordering::Less
        } else if _a > _b {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }

    impl AvlTree<IntAvlNode> {
        fn remove_int(&mut self, i: i64) -> bool {
            let result = self.find_node(&new_intnode_raw(i));
            let node = result.get_exact();
            if node.is_none() {
                println!("not found {}", i);
                return false;
            }
            self.remove(&node.unwrap());
            true
        }

        fn add_int_node(&mut self, node: AvlNodeRef<IntAvlNode>) -> bool {
            self.add(node, cmp_int_node)
        }

        fn validate_tree(&self) {
            self.validate(cmp_int_node);
        }

        fn find_int(&self, i: i64) -> AvlSearchResult<IntAvlNode> {
            self.find(&i, cmp_int)
        }

        fn find_node(&self, node: &IntAvlNode) -> AvlSearchResult<IntAvlNode> {
            self.find(node, cmp_int_node)
        }
    }

    #[test]
    fn int_avl_node() {
        let mut tree = new_inttree();

        assert_eq!(tree.get_count(), 0);
        assert_eq!(tree.first(), None);
        assert_eq!(tree.last(), None);

        let node1 = new_intnode(1);
        let node2 = new_intnode(2);
        let node3 = new_intnode(3);
        tree.set_child2(tree.to_node_mut(&node1), AvlDirection::Left, Some(node2.clone()), &node1);
        tree.set_child2(tree.to_node_mut(&node2), AvlDirection::Right, Some(node3.clone()), &node2);
        assert_eq!(tree.parent_direction2(&node2), AvlDirection::Left);
        assert_eq!(tree.parent_direction2(&node1), AvlDirection::Left);
        assert_eq!(tree.parent_direction2(&node3), AvlDirection::Right);
    }

    /*
    fn int_avl_tree_exists(tree: &AvlTree<IntAvlNode>, i: i64) -> bool {
        let result = tree.find_int(i);
        result.get_exact().is_some()
    }
    */

    /*
    #[test]
    fn int_avl_tree_dup() {
        let mut result: AvlSearchResult<i64>;
        let mut tree = new_inttree();
        let node1 = new_intnode(1);
        assert!(tree.add_dup(node1.clone()));
        assert!(! tree.add_dup(node1.clone()));
        let node2 = new_intnode(2);
        assert!(tree.add_dup(node2.clone()));
        let node3 = new_intnode(3);
        assert!(tree.add_dup(node3.clone()));
        let node1_1 = new_intnode(1);
        assert!(tree.add_dup(node1_1.clone()));
        {
            assert!(! tree.add_int_node(new_intnode(2)));
        }
        assert!(! tree.add_dup(node1.clone()));
        assert_eq!(tree.get_count(), 4);
        tree.validate_tree();

        {
            result = tree.find_indentical(&node1.borrow().value);
            assert_eq!(result.get_exact(), Some(node1.clone()));
            assert!(result.get_exact() != Some(node1_1.clone()));
        }

        tree.remove(node1.clone());
        assert_eq!(tree.get_count(), 3);

        {
            result = tree.find_indentical(&node1.borrow().value);
            assert!(result.get_exact().is_none());
        }
        {
            result = tree.find_indentical(&node1_1.borrow().value);
            assert_eq!(result.get_exact(), Some(node1_1.clone()));
            assert!(result.get_exact() != Some(node1.clone()));
        }
        assert!(int_avl_tree_exists(&tree, 1));
        assert!(int_avl_tree_exists(&tree, 2));
        assert!(int_avl_tree_exists(&tree, 3));

        tree.remove(node1_1.clone());
        assert!(! int_avl_tree_exists(&tree, 1));
        assert!(int_avl_tree_exists(&tree, 2));
        assert!(int_avl_tree_exists(&tree, 3));
        tree.remove(node2.clone());
        assert!(! int_avl_tree_exists(&tree, 2));
        assert!(int_avl_tree_exists(&tree, 3));
        tree.remove(node3.clone());
        assert!(! int_avl_tree_exists(&tree, 3));
        assert_eq!(tree.get_count(), 0);
    }
    */

    #[test]
    fn int_avl_tree_basic() {
        let mut tree = new_inttree();
        let node = new_intnode(0);
        assert_eq!(tree.find_node(&node.borrow()).into_exact(), None);
        assert_eq!(tree.nearest(&tree.find_node(&node.borrow()), AvlDirection::Left), None);
        assert_eq!(tree.nearest(&tree.find_node(&node.borrow()), AvlDirection::Right), None);
        tree.add_int_node(node.clone());
        let result = tree.find_node(&node.borrow());
        assert!(result.get_node_ref().is_some());
        assert_eq!(tree.nearest(&result, AvlDirection::Left), None);
        assert_eq!(tree.nearest(&result, AvlDirection::Right), None);

        let rs = tree.find_larger_eq(&new_intnode_raw(0), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        assert_eq!(found_value, 0);
        let rs = tree.find_larger_eq(&new_intnode_raw(2), cmp_int_node).into_exact();
        assert!(rs.is_none());

        let result = tree.find_int(1);
        let left = tree.nearest(&result, AvlDirection::Left);
        assert!(left.is_some());
        assert_eq!(left.unwrap().borrow().value, 0);
        assert_eq!(tree.nearest(&result, AvlDirection::Right), None);

        tree.add_int_node(new_intnode(2));
        let rs = tree.find_larger_eq(&new_intnode_raw(1), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        assert_eq!(found_value, 2);
    }

    #[test]
    fn int_avl_tree_order() {
        let max = 20000;
        let mut tree = new_inttree();
        assert!(tree.first().is_none());
        //PROFILER.lock().unwrap().start("./my-prof.profile").unwrap();
        let start_ts = Instant::now();
        for i in 0..max {
            tree.add_int_node(new_intnode(i));
        }
        tree.validate_tree();
        assert_eq!(tree.get_count(), max as i64);
        {
            let mut count = 0;
            let mut node: Option<AvlNodeRef<IntAvlNode>> = tree.first();
            loop {
                if node.is_none() {
                    break;
                }
                let _node = node.clone().unwrap();
                assert_eq!(_node.borrow().value, count);
                let next = tree.walk(&_node, AvlDirection::Right);
                count += 1;
                if next.is_some() {
                    node = next;
                } else {
                    break;
                }
            }
            assert_eq!(tree.last(), node);
            assert_eq!(count, max);
        }
        {
            let rs = tree.find_larger_eq(&new_intnode_raw(5), cmp_int_node).into_exact();
            let found_value = rs.unwrap().borrow().value;
            println!("found larger_eq {}", found_value);
            assert!(found_value >= 5);
            tree.remove_int(5);
            let rs = tree.find_larger_eq(&new_intnode_raw(5), cmp_int_node).into_exact();
            assert!(rs.unwrap().borrow().value >= 6);
            tree.add_int_node(new_intnode(5));
        }
        {
            for i in 0..max {
                //println!("removing {}", i);
                assert!(tree.remove_int(i));
                //tree.validate_tree();
            }
            assert_eq!(tree.get_count(), 0);
        }
        let end_ts = Instant::now();
        //PROFILER.lock().unwrap().stop().unwrap();
        println!("duration {}", end_ts.duration_since(start_ts).as_secs_f64());
    }

    #[test]
    fn int_avl_tree_fixed1() {
        let mut tree = new_inttree();
        let arr = [4719789032060327248, 7936680652950253153, 5197008094511783121];
        for i in arr.iter() {
            let rc = new_intnode(*i);
            tree.add_int_node(rc.clone());
            let rs = tree.find_node(rc.borrow());
            assert_eq!(rs.get_exact(), Some(rc), "add error {}", i);
        }
        assert_eq!(tree.get_count(), arr.len() as i64);
        for i in arr.iter() {
            assert!(tree.remove_int(*i));
        }
        assert_eq!(tree.get_count(), 0);
    }

    #[test]
    fn int_avl_tree_fixed2() {
        let mut tree = new_inttree();
        tree.validate_tree();
        let node1 = new_intnode(536872960);
        {
            tree.add_int_node(node1.clone());
            tree.validate_tree();
            tree.remove(&node1);
            tree.validate_tree();
            tree.add_int_node(node1.clone());
            tree.validate_tree();
        }
        assert_eq!(Arc::strong_count(&node1.0), 2);
        assert!(tree.find_node(&node1.borrow()).get_exact().is_some());
        let node2 = new_intnode(12288);
        tree.add_int_node(node2.clone());
        tree.validate_tree();
        tree.remove(&node1);
        tree.validate_tree();
        tree.add_int_node(node1);
        tree.validate_tree();
        let node3 = new_intnode(22528);
        tree.add_int_node(node3.clone());
        tree.validate_tree();
        tree.remove(&node2);
        assert_eq!(tree.find_node(&node2.borrow()).get_exact(), None);
        tree.validate_tree();
        tree.remove(&node3);
        assert_eq!(tree.find_node(&node3.borrow()).get_exact(), None);
        tree.validate_tree();
        tree.add_int_node(node3);
        tree.validate_tree();
    }

    #[test]
    fn int_avl_tree_fixed3() {
        let mut tree = new_inttree();
        {
            tree.add_int_node(new_intnode(2));
            tree.add_int_node(new_intnode(14));
            tree.add_int_node(new_intnode(12));
            tree.add_int_node(new_intnode(15));
            tree.add_int_node(new_intnode(5));
            tree.add_int_node(new_intnode(3));
            tree.add_int_node(new_intnode(9));
            tree.add_int_node(new_intnode(16));
            tree.add_int_node(new_intnode(11));
            tree.add_int_node(new_intnode(6));
            tree.add_int_node(new_intnode(18));
            tree.add_int_node(new_intnode(8));
            tree.add_int_node(new_intnode(13));
            tree.add_int_node(new_intnode(17));
            tree.add_int_node(new_intnode(4));
            tree.add_int_node(new_intnode(1));
            tree.add_int_node(new_intnode(20));
            tree.add_int_node(new_intnode(10));
            tree.add_int_node(new_intnode(7));
            tree.add_int_node(new_intnode(19));
        }
        assert_eq!(tree.remove_int(1), true);
        assert_eq!(tree.remove_int(2), true);
        assert_eq!(tree.remove_int(3), true);
        assert_eq!(tree.remove_int(4), true);
        assert_eq!(tree.remove_int(5), true);
        assert_eq!(tree.remove_int(6), true);
        assert_eq!(tree.remove_int(7), true);
        assert_eq!(tree.remove_int(8), true);
        assert_eq!(tree.get_count(), 12);
    }

    #[test]
    fn int_avl_tree_fixed4() {
        let mut test_list: Vec<i64> = Vec::new();
        let mut tree = new_inttree();
        tree.validate_tree();
        test_list.push(3);
        tree.add_int_node(new_intnode(3));
        test_list.push(1);
        tree.add_int_node(new_intnode(1));
        test_list.push(6);
        tree.add_int_node(new_intnode(6));
        test_list.push(4);
        tree.add_int_node(new_intnode(4));
        test_list.push(5);
        tree.add_int_node(new_intnode(5));
        for node_value in test_list.clone() {
            tree.remove_int(node_value);
            tree.validate_tree();
        }
    }

    #[test]
    fn int_avl_tree_fixed5() {
        let mut tree = new_inttree();
        tree.add_int_node(new_intnode(25));
        tree.add_int_node(new_intnode(20));
        tree.add_int_node(new_intnode(15));
        tree.add_int_node(new_intnode(10));
        tree.add_int_node(new_intnode(8));
        tree.add_int_node(new_intnode(12));
        tree.add_int_node(new_intnode(4));
        tree.add_int_node(new_intnode(6));
        tree.add_int_node(new_intnode(18));
        tree.add_int_node(new_intnode(28));
        tree.add_int_node(new_intnode(26));
        tree.add_int_node(new_intnode(29));
        tree.add_int_node(new_intnode(30));
        tree.add_int_node(new_intnode(32));
        assert!(tree.remove_int(8));
        tree.validate_tree();
        assert!(tree.remove_int(10));
        tree.validate_tree();
        assert!(tree.remove_int(26));
        assert!(tree.remove_int(15));
        assert!(tree.remove_int(29));
        assert!(tree.remove_int(6));
        assert!(tree.remove_int(20));
        assert!(tree.remove_int(28));
        assert!(tree.remove_int(4));
        assert!(tree.remove_int(12));
        assert!(tree.remove_int(18));
        assert!(tree.remove_int(30));
        assert!(tree.remove_int(32));
        assert!(tree.remove_int(25));
        tree.validate_tree();
    }

    /*
    #[test]
    fn int_avl_tree_random() {
        let count = 1000;
        let mut test_list: Vec<i64> = Vec::with_capacity(count);
        let mut rng = rand::thread_rng();
        let mut tree = new_inttree();
        tree.validate_tree();
        for _ in 0..count {
            let node_value: i64 = rng.gen();
            if !test_list.contains(&node_value) {
                test_list.push(node_value);
                assert!(tree.add_int_node(new_intnode(node_value)))
            }
        }
        tree.validate_tree();
        test_list.sort();
        for index in 0..test_list.len() {
            let node = tree.find_int(test_list[index]).get_exact();
            assert!(!node.is_none());
            let _node = node.as_ref().unwrap();
            let prev = tree.walk(_node, AvlDirection::Left);
            let next = tree.walk(_node, AvlDirection::Right);
            if index == 0 {
                // first node
                assert!(prev.is_none());
                assert!(!next.is_none());
                assert_eq!(next.unwrap().borrow().value, test_list[index + 1]);
            } else if index == test_list.len() - 1 {
                // last node
                assert!(!prev.is_none());
                assert_eq!(prev.unwrap().borrow().value, test_list[index - 1]);
                assert!(next.is_none());
            } else {
                // middle node
                assert!(!prev.is_none());
                assert_eq!(prev.unwrap().borrow().value, test_list[index - 1]);
                assert!(!next.is_none());
                assert_eq!(next.unwrap().borrow().value, test_list[index + 1]);
            }
        }
        for index in 0..test_list.len() {
            assert!(tree.remove_int(test_list[index]));
        }
        tree.validate_tree();
        assert_eq!(0, tree.get_count());
    }

    #[test]
    fn int_avl_tree_random_remove() {
        let count = 10000;
        let mut test_list: Vec<i64> = Vec::new();
        let mut rng = rand::thread_rng();
        let mut tree = new_inttree();
        tree.validate_tree();
        for _ in 0..count {
            let node_value: i64 = rng.gen_range(1, 20000);
            if !test_list.contains(&node_value) {
                test_list.push(node_value);
                assert!(tree.add_int_node(new_intnode(node_value)))
            }
        }
        assert_eq!(test_list.len() as i64, tree.get_count());
        tree.validate_tree();

        let mut change_list: Vec<i64> = Vec::new();
        for _ in 0..count {
            let remove_node_value: i64 = rng.gen_range(1, 20000);
            if test_list.contains(&remove_node_value) && !change_list.contains(&remove_node_value) {
                change_list.push(remove_node_value);
                assert!(tree.remove_int(remove_node_value));
            }
        }
        assert_eq!(test_list.len() as i64, tree.get_count() + change_list.len() as i64);
    }
    */

    #[test]
    fn int_avl_tree_remove_again() {
        let mut tree = new_inttree();
        tree.validate_tree();
        let node1 = new_intnode(536872960);
        tree.add_int_node(node1.clone());
        assert_eq!(tree.get_count(), 1);
        tree.remove(&node1);
        assert_eq!(tree.get_count(), 0);
        tree.remove(&node1);
        assert_eq!(tree.get_count(), 0);
    }

    // TODO TestAVLTreeLargeDup

    #[test]
    fn int_avl_tree_find_nearest() {
        let mut tree = new_inttree();
        {
            tree.add_int_node(new_intnode(1));
            tree.add_int_node(new_intnode(5));
            tree.add_int_node(new_intnode(10));
            tree.add_int_node(new_intnode(15));
            tree.add_int_node(new_intnode(20));
            tree.add_int_node(new_intnode(25));
            tree.add_int_node(new_intnode(30));
            tree.add_int_node(new_intnode(35));
            tree.add_int_node(new_intnode(40));
            tree.add_int_node(new_intnode(45));
        }

        let rs = tree.find_nearest(&new_intnode_raw(1), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 1);

        let rs = tree.find_nearest(&new_intnode_raw(5), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 5);

        let rs = tree.find_nearest(&new_intnode_raw(10), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 10);

        let rs = tree.find_nearest(&new_intnode_raw(15), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 15);

        let rs = tree.find_nearest(&new_intnode_raw(20), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 20);

        let rs = tree.find_nearest(&new_intnode_raw(25), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 25);

        let rs = tree.find_nearest(&new_intnode_raw(30), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 30);

        let rs = tree.find_nearest(&new_intnode_raw(35), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 35);

        let rs = tree.find_nearest(&new_intnode_raw(40), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 40);

        let rs = tree.find_nearest(&new_intnode_raw(45), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 45);

        let rs = tree.find_nearest(&new_intnode_raw(4), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 5);

        let rs = tree.find_nearest(&new_intnode_raw(2), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 5);

        let rs = tree.find_nearest(&new_intnode_raw(1), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 1);

        let rs = tree.find_nearest(&new_intnode_raw(41), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 45);

        let rs = tree.find_nearest(&new_intnode_raw(44), cmp_int_node).into_exact();
        let found_value = rs.unwrap().borrow().value;
        println!("found nearest {}", found_value);
        assert!(found_value == 45);
    }
}
