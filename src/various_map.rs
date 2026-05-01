use alloc::collections::BTreeMap;
use alloc::collections::btree_map;
use core::borrow::Borrow;
use core::fmt::Debug;
use core::iter;
use core::option;

pub enum VariousMap<K, V> {
    One(Option<(K, V)>),
    Multi(BTreeMap<K, V>),
}

impl<K: Ord, V> VariousMap<K, V> {
    #[inline]
    pub fn new() -> Self {
        Self::One(None)
    }

    #[inline]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord, // K needs Ord for BTreeMap and overall comparison
        Q: Ord + ?Sized,    // Q also needs Ord for BTreeMap.
    {
        match self {
            Self::One(Some(item)) => {
                if item.0.borrow() == key {
                    Some(&item.1)
                } else {
                    None
                }
            }
            Self::Multi(map) => map.get(key),
            _ => None,
        }
    }

    #[inline]
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Ord, // K needs Ord for BTreeMap and overall comparison
        Q: Ord + ?Sized,    // Q also needs Ord for BTreeMap.
    {
        match self {
            Self::One(Some(item)) => {
                if item.0.borrow() == key {
                    Some(&mut item.1)
                } else {
                    None
                }
            }
            Self::Multi(map) => map.get_mut(key),
            _ => None,
        }
    }

    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        let (old_k, old_v) = match self {
            Self::One(ref mut item) => {
                if item.is_none() {
                    item.replace((key, value));
                    return None;
                }
                let (old_k, old_v) = item.take().unwrap();
                if old_k == key {
                    item.replace((key, value));
                    return Some(old_v);
                }
                (old_k, old_v)
            }
            Self::Multi(ref mut map) => {
                return map.insert(key, value);
            }
        };
        let mut map = BTreeMap::new();
        map.insert(key, value);
        map.insert(old_k, old_v);
        *self = Self::Multi(map);
        None
    }

    //    pub fn entry(&mut self, key: K) -> Entry<'_, K, V>
    //    where
    //        K: PartialEq + Eq + Ord + Clone + Debug,
    //        V: PartialEq + Debug + Default,
    //    {
    //        let old_self_state = std::mem::replace(self, Self::Empty);
    //
    //        match old_self_state {
    //            Self::Empty => {
    //                Entry::EmptyVacant {
    //                    key,
    //                    parent_map_ref: self as *mut VariousMap<K, V>, // Raw pointer
    //                }
    //            }
    //            Self::One(item) => {
    //                if key == k_val {
    //                    item.1 =
    //                    let k_ref;
    //                    let v_ref;
    //                    unsafe {
    //                        let map_ptr = self as *mut VariousMap<K, V>;
    //                        if let VariousMap::One((k_inner, v_inner)) = &mut *map_ptr {
    //                            k_ref = &*k_inner;
    //                            v_ref = &mut *v_inner;
    //                        } else {
    //                            unreachable!(
    //                                "Map state changed unexpectedly to non-One after put back One variant"
    //                            );
    //                        }
    //                    }
    //
    //                    Entry::OneOccupied {
    //                        k_ref,
    //                        v_ref,
    //                        parent_map_ref: self as *mut VariousMap<K, V>,
    //                    }
    //                } else {
    //                    Entry::OneToMultiVacant {
    //                        key,
    //                        old_k: k_val,
    //                        old_v: v_val,
    //                        parent_map_ref: self as *mut VariousMap<K, V>,
    //                    }
    //                }
    //            }
    //            Self::Multi(map) => {
    //                *self = Self::Multi(map);
    //                match self {
    //                    Self::Multi(map_ref) => Entry::Multi(map_ref.entry(key)),
    //                    _ => unreachable!(),
    //                }
    //            }
    //        }
    //    }

    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        match self {
            Self::One(o) => Iter::One(o.iter()),
            Self::Multi(map) => Iter::Multi(map.iter()),
        }
    }
}

impl<K, V> IntoIterator for VariousMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        match self {
            Self::One(o) => IntoIter::One(o),
            Self::Multi(map) => IntoIter::Multi(map.into_iter()),
        }
    }
}

/// An iterator over the entries of a `VariousMap`.
pub enum Iter<'a, K, V> {
    One(option::Iter<'a, (K, V)>),
    Multi(btree_map::Iter<'a, K, V>),
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Iter::One(iter) => {
                if let Some(item) = iter.next() {
                    return Some((&item.0, &item.1));
                } else {
                    None
                }
            }
            Iter::Multi(iter) => iter.next(),
        }
    }
}

/// An owning iterator over the entries of a `VariousMap`.
pub enum IntoIter<K, V> {
    One(Option<(K, V)>),
    Multi(btree_map::IntoIter<K, V>),
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => iter.take(),
            Self::Multi(iter) => iter.next(),
        }
    }
}

/*
pub enum Entry<'a, K: 'a, V: 'a> {
    /// An entry that exists in the `One` variant of `VariousMap`.
    Occupied {
        k_ref: &'a K,
        v_ref: &'a mut V,
        parent_map_ref: *mut VariousMap<K, V>, // Changed to raw pointer
    },
    /// A vacant entry where `VariousMap` is `Empty`.
    Vacant {
        key: K,
        parent_map_ref: *mut VariousMap<K, V>, // Changed to raw pointer
    },
    /// A vacant entry where `VariousMap` is `One`, but the key doesn't match.
    OneToMultiVacant {
        key: K,                                // The new key to insert
        old_k: K,                              // The key from the existing `One` variant
        old_v: V,                              // The value from the existing `One` variant
        parent_map_ref: *mut VariousMap<K, V>, // Changed to raw pointer
    },
    /// Delegates to `BTreeMap`'s entry.
    Multi(btree_map::Entry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: PartialEq + Eq + Ord + Clone + Debug,
    V: PartialEq + Debug + Default,
{
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::OneOccupied { v_ref, .. } => v_ref,
            Entry::EmptyVacant { key, parent_map_ref } => unsafe {
                let map = &mut *parent_map_ref;
                *map = VariousMap::One(key, default);
                if let VariousMap::One(_, v_ref) = map { v_ref } else { unreachable!() }
            },
            Entry::OneToMultiVacant { key, old_k, old_v, parent_map_ref } => unsafe {
                let map = &mut *parent_map_ref;
                let mut btree = BTreeMap::new();
                btree.insert(old_k, old_v);
                let inserted_key = key.clone();
                btree.insert(key, default);
                *map = VariousMap::Multi(btree);
                if let VariousMap::Multi(map_inner) = map {
                    map_inner.get_mut(&inserted_key).unwrap()
                } else {
                    unreachable!()
                }
            },
            Entry::Multi(btree_entry) => btree_entry.or_insert(default),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> V>(self, default_fn: F) -> &'a mut V {
        match self {
            Entry::OneOccupied { v_ref, .. } => v_ref,
            Entry::EmptyVacant { key, parent_map_ref } => unsafe {
                let map = &mut *parent_map_ref;
                *map = VariousMap::One(key, default_fn());
                if let VariousMap::One(_, v_ref) = map { v_ref } else { unreachable!() }
            },
            Entry::OneToMultiVacant { key, old_k, old_v, parent_map_ref } => unsafe {
                let map = &mut *parent_map_ref;
                let mut btree = BTreeMap::new();
                btree.insert(old_k, old_v);
                let inserted_key = key.clone();
                btree.insert(key, default_fn());
                *map = VariousMap::Multi(btree);
                if let VariousMap::Multi(map_inner) = map {
                    map_inner.get_mut(&inserted_key).unwrap()
                } else {
                    unreachable!()
                }
            },
            Entry::Multi(btree_entry) => btree_entry.or_insert_with(default_fn),
        }
    }

    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::OneOccupied { v_ref, k_ref, parent_map_ref } => {
                f(v_ref);
                Entry::OneOccupied { v_ref, k_ref, parent_map_ref }
            }
            Entry::Multi(btree_entry) => Entry::Multi(btree_entry.and_modify(f)),
            _ => self, // Vacant entries don't get modified.
        }
    }

    pub fn remove(self) -> V {
        match self {
            Entry::OneOccupied { v_ref, parent_map_ref, .. } => unsafe {
                let map = &mut *parent_map_ref;
                let old_map_state = std::mem::replace(map, VariousMap::Empty);
                if let VariousMap::One(_, v) = old_map_state {
                    v
                } else {
                    unreachable!(
                        "Map state changed unexpectedly during Entry::OneOccupied::remove"
                    );
                }
            },
            Entry::Multi(btree_entry) => match btree_entry {
                btree_map::Entry::Occupied(occupied_entry) => occupied_entry.remove(),
                btree_map::Entry::Vacant(_) => panic!("Called remove on a vacant entry"),
            },
            _ => panic!("Called remove on a vacant entry"),
        }
    }
}
*/
