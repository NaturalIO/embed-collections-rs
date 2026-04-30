use alloc::collections::btree_map;
use alloc::collections::BTreeMap;
use core::borrow::Borrow;
use core::iter;
use core::option; // Added for option::IntoIter

pub enum VariousMap<K, V> {
    Empty,
    One(K, V),
    Multi(BTreeMap<K, V>),
}

/// An iterator over the entries of a `VariousMap`.
pub enum Iter<'a, K, V> {
    Empty(iter::Empty<(&'a K, &'a V)>),
    One(option::IntoIter<(&'a K, &'a V)>),
    Multi(btree_map::Iter<'a, K, V>),
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Iter::Empty(iter) => iter.next(),
            Iter::One(iter) => iter.next(),
            Iter::Multi(iter) => iter.next(),
        }
    }
}

/// An owning iterator over the entries of a `VariousMap`.
pub enum IntoIter<K, V> {
    Empty(iter::Empty<(K, V)>),
    One(option::IntoIter<(K, V)>),
    Multi(btree_map::IntoIter<K, V>),
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IntoIter::Empty(iter) => iter.next(),
            IntoIter::One(iter) => iter.next(),
            IntoIter::Multi(iter) => iter.next(),
        }
    }
}

pub enum Entry<'a, K: 'a, V: 'a> {
    /// An entry that already existed in the map.
    Occupied(OccupiedEntry<'a, K, V>),

    /// A vacant entry that can be inserted into.
    Vacant(VacantEntry<'a, K, V>),
}

/// A view into an occupied entry in a `VariousMap`.
pub enum OccupiedEntry<'a, K: 'a, V: 'a> {
    One {
        map: &'a mut VariousMap<K, V>, // Reference to the parent map to allow removal
        key_ref: &'a K, // Reference to the key in the One variant
        value_ref: &'a mut V, // Mutable reference to the value in the One variant
    },
    Multi(btree_map::OccupiedEntry<'a, K, V>),
}

/// A view into a vacant entry in a `VariousMap`.
pub struct VacantEntry<'a, K: 'a, V: 'a> {
    map: &'a mut VariousMap<K, V>,
    key: K, // Owned key to be inserted
}

impl<'a, K, V> OccupiedEntry<'a, K, V>
where
    K: PartialEq + Eq + Ord + Debug,
{
    pub fn get_mut(&mut self) -> &mut V {
        match self {
            OccupiedEntry::One { value_ref, .. } => value_ref,
            OccupiedEntry::Multi(entry) => entry.get_mut(),
        }
    }

    pub fn remove(self) -> V {
        match self {
            OccupiedEntry::One { map, key_ref, value_ref } => {
                let old_map_state = std::mem::replace(map, VariousMap::Empty);
                if let VariousMap::One(k, v) = old_map_state {
                    // Check if k matches key_ref, this should always be true.
                    assert_eq!(&k, key_ref, "Key mismatch during OccupiedEntry::One::remove");
                    v
                } else {
                    unreachable!("Map state changed unexpectedly during OccupiedEntry::One::remove");
                }
            }
            OccupiedEntry::Multi(entry) => entry.remove(),
        }
    }
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: PartialEq + Eq + Ord + Clone, // K needs to be Clone for the One to Multi transition
{
    pub fn insert(self, value: V) -> &'a mut V {
        match std::mem::replace(self.map, VariousMap::Empty) {
            VariousMap::Empty => {
                *self.map = VariousMap::One(self.key, value);
                if let VariousMap::One(_, v_ref) = self.map {
                    v_ref
                } else {
                    unreachable!()
                }
            }
            VariousMap::One(k, v) => {
                let mut btree = BTreeMap::new();
                btree.insert(k, v);
                btree.insert(self.key, value);
                *self.map = VariousMap::Multi(btree);
                if let VariousMap::Multi(map_inner) = self.map {
                    // We just inserted self.key, so it must be present
                    map_inner.get_mut(&self.key).unwrap()
                } else {
                    unreachable!()
                }
            }
            VariousMap::Multi(mut btree) => {
                // This case should be handled by Entry::Multi(btree_map::VacantEntry)
                // This implies an error in the Entry::entry logic if we reach here
                unreachable!("VacantEntry::insert should not be called on a Multi map that was already Multi");
            }
        }
    }
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: PartialEq + Eq + Ord + Clone, // K needs to be Clone for VacantEntry
    V: Default, // Default is not strictly needed for or_insert, but helpful for some use cases.
{
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.get_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> V>(self, default_fn: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.get_mut(),
            Entry::Vacant(entry) => entry.insert(default_fn()),
        }
    }

    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        if let Entry::Occupied(mut entry) = self {
            f(entry.get_mut());
            Entry::Occupied(entry)
        } else {
            self
        }
    }
}

impl<K, V> VariousMap<K, V> {
    pub fn new() -> Self {
        Self::Empty
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + PartialEq + Eq + Ord,
        Q: PartialEq + Eq + Ord + ?Sized,
    {
        match self {
            Self::Empty => None,
            Self::One(k, v) => {
                if key.eq(k.borrow()) {
                    Some(v)
                } else {
                    None
                }
            }
            Self::Multi(map) => map.get(key),
        }
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + PartialEq + Eq + Ord,
        Q: PartialEq + Eq + Ord + ?Sized,
    {
        match self {
            Self::Empty => None,
            Self::One(k, v) => {
                if key.eq(k.borrow()) {
                    Some(v)
                } else {
                    None
                }
            }
            Self::Multi(map) => map.get_mut(key),
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: PartialEq + Eq + Ord,
    {
        match std::mem::replace(self, Self::Empty) {
            Self::Empty => {
                *self = Self::One(key, value);
                None
            }
            Self::One(k, v) => {
                if key == k {
                    *self = Self::One(key, value);
                    Some(v)
                } else {
                    let mut map = BTreeMap::new();
                    map.insert(k, v);
                    map.insert(key, value);
                    *self = Self::Multi(map);
                    None
                }
            }
            Self::Multi(mut map) => {
                let old_value = map.insert(key, value);
                *self = Self::Multi(map);
                old_value
            }
        }
    }

    pub fn entry(&mut self, key: K) -> Entry<'_, K, V>
    where
        K: PartialEq + Eq + Ord + Clone,
        V: Default, // V: Default is only needed for or_insert with Default value. Not directly by entry.
    {
        match self {
            Self::Empty => Entry::Vacant(VacantEntry { map: self, key }),
            Self::One(k_ref, v_ref) => {
                if key == *k_ref {
                    Entry::Occupied(OccupiedEntry::One { map: self, key_ref: k_ref, value_ref: v_ref })
                } else {
                    Entry::Vacant(VacantEntry { map: self, key })
                }
            }
            Self::Multi(map) => {
                match map.entry(key) {
                    btree_map::Entry::Occupied(entry) => Entry::Occupied(OccupiedEntry::Multi(entry)),
                    btree_map::Entry::Vacant(entry) => Entry::Vacant(VacantEntry { map: self, key: entry.into_key() }),
                }
            }
        }
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        match self {
            Self::Empty => Iter::Empty(iter::empty()),
            Self::One(k, v) => Iter::One(Some((k, v)).into_iter()),
            Self::Multi(map) => Iter::Multi(map.iter()),
        }
    }
}

impl<K, V> IntoIterator for VariousMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            VariousMap::Empty => IntoIter::Empty(iter::empty()),
            VariousMap::One(k, v) => IntoIter::One(Some((k, v)).into_iter()),
            VariousMap::Multi(map) => IntoIter::Multi(map.into_iter()),
        }
    }
}