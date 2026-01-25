// Dummy logger
macro_rules! log_debug_assert {
    ($($arg:tt)*) => { debug_assert!($($arg)*) };
}

#[allow(unused_macros)]
macro_rules! log_info {
    ($($arg:tt)*) => {};
}
#[allow(unused_macros)]
macro_rules! log_error {
    ($($arg:tt)*) => {};
}
#[allow(unused_macros)]
macro_rules! log_debug {
    ($($arg:tt)*) => {};
}

// offset_of! macro
macro_rules! offset_of {
    ($ty:ty, $field:ident) => {
        unsafe { &(*(0 as *const $ty)).$field as *const _ as usize }
    };
}

mod avl_old {
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

        #[inline(always)]
        fn to_node<'a>(&self, data: &'a AvlNodeRef<T>) -> &'a AvlNode<T> {
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
            log_debug_assert!(w.direction.is_some());
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
                    node.parent = Some(parent.downgrade());
                    let _ = node; // prevent borrowing new_data
                    parent_node.set_child(which_child, Some(new_data));
                    self.count += 1;

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
            let child = self.to_node(here).get_child_ref(dir_child);
            if let Some(_data_exists) = child {
                dir_child = dir_child.reverse();
                let node = self.bottom_child_ref(&_data_exists, dir_child);
                self._insert(new_data, Some(node), dir_child);
            } else {
                self._insert(new_data, Some(here), dir_child);
            }
        }

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

            if child_balance != right_heavy {
                child_balance += right_heavy;

                let c_right = child_node.take_child(dir_inverse);
                self.set_child2(node, dir, c_right, &data);
                node.balance = -child_balance;

                node.parent = Some(_child.downgrade());
                let _ = node;
                child_node.set_child(dir_inverse, Some(data));

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

            let g_child = child_node.take_child(dir_inverse);
            let _g_child = g_child.unwrap();
            let g_child_node = self.to_node_mut(&_g_child);
            let g_left = g_child_node.take_child(dir);
            let g_right = g_child_node.take_child(dir_inverse);

            self.set_child2(node, dir, g_right, &data);
            self.set_child2(child_node, dir_inverse, g_left, &_child);

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
                }
                let child_node = self.to_node_mut(&child);
                if child_node.get_child_ref(dir).unwrap() == &child {
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

            parent = del_node.get_parent();

            if del_node.left.is_some() {
                imm_data = del_node.take_child(AvlDirection::Left);
            } else {
                imm_data = del_node.take_child(AvlDirection::Right);
            }

            if let Some(ref _imm_data) = imm_data {
                let imm_node = self.to_node_mut(&_imm_data);
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
                let mut _node_data: AvlNodeRef<T> = _parent;
                let mut old_balance: i8;
                let mut new_balance: i8;
                loop {
                    let _node = self.to_node_mut(&_node_data);
                    old_balance = _node.balance;
                    new_balance = old_balance - avlchild_to_balance!(which_child);

                    if old_balance == 0 {
                        _node.balance = new_balance;
                        break;
                    }

                    let __parent = _node.get_parent();
                    which_child = self.parent_direction(&_node_data, __parent.as_ref());

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

        pub fn validate(&self, _cmp_func: AvlCmpNodeFunc<T>) {
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
                    data = node.get_child(AvlDirection::Right);
                } else if stack.len() > 0 {
                    let _data = stack.pop().unwrap();
                    visited += 1;
                    let node = self.to_node(&_data);
                    data = node.get_child(AvlDirection::Right);
                } else {
                    break;
                }
            }
            assert_eq!(visited, self.count);
        }

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
    }
}

use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use rand::seq::SliceRandom;
use rand::{Rng, thread_rng};
use std::cell::UnsafeCell;
use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;

use avl_old::{AvlNodeRef, AvlTree};

// Setup from avl_old.rs's tests
struct IntAvlNode {
    pub value: i64,
    pub node: avl_old::AvlNode<Self>,
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

fn new_intnode_old(i: i64) -> AvlNodeRef<IntAvlNode> {
    AvlNodeRef(Arc::new(UnsafeCell::new(IntAvlNode {
        node: avl_old::AvlNode::default(),
        value: i,
    })))
}

fn new_inttree_old() -> AvlTree<IntAvlNode> {
    let off = offset_of!(IntAvlNode, node);
    AvlTree::<IntAvlNode>::new(off)
}

fn cmp_int_node_old<'a>(a: &'a IntAvlNode, b: &'a AvlNodeRef<IntAvlNode>) -> Ordering {
    a.value.cmp(&b.borrow().value)
}

fn cmp_int_old(a: &i64, b: &AvlNodeRef<IntAvlNode>) -> Ordering {
    a.cmp(&b.borrow().value)
}

// bench_avl_insert_old
fn bench_avl_insert_old(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<i64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut group = c.benchmark_group("avl_insert_old");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("insert_10000", |b| {
        b.iter(|| {
            let mut tree = new_inttree_old();
            for &value in &values {
                tree.add(black_box(new_intnode_old(value)), cmp_int_node_old);
            }
        })
    });
    group.finish();
}

// bench_avl_search_old
fn bench_avl_search_old(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<i64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut tree = new_inttree_old();
    for &value in &values {
        tree.add(new_intnode_old(value), cmp_int_node_old);
    }

    values.shuffle(&mut rng);

    let mut group = c.benchmark_group("avl_search_old");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("search_10000", |b| {
        b.iter(|| {
            for &value in &values {
                black_box(tree.find(&value, cmp_int_old));
            }
        })
    });
    group.finish();
}

fn bench_avl_drop_old(c: &mut Criterion) {
    let count = 10000;
    let mut rng = thread_rng();
    let mut values: Vec<i64> = (0..count).map(|_| rng.r#gen()).collect();
    values.sort_unstable();
    values.dedup();

    let mut group = c.benchmark_group("avl_drop_old");
    group.throughput(Throughput::Elements(values.len() as u64));
    group.bench_function("drop_10000", |b| {
        b.iter_with_setup(
            || {
                let mut tree = new_inttree_old();
                for &value in &values {
                    tree.add(new_intnode_old(value), cmp_int_node_old);
                }
                tree
            },
            |tree| {
                black_box(tree);
            },
        )
    });
    group.finish();
}

criterion_group!(benches, bench_avl_insert_old, bench_avl_search_old, bench_avl_drop_old);
criterion_main!(benches);
