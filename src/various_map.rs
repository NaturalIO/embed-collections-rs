//! VariousMap: Provide a tempoary map optimise for empty or one condition,
//! to delay allocation.
//!
//! Initial to be Option<(K, V)>.
//! If multi item inserted, transit from Option to std::collections::BTreeMap.

use alloc::collections::BTreeMap;
use alloc::collections::btree_map;
use core::borrow::Borrow;
use core::mem::MaybeUninit;
use core::option;

/// A tempoary map optimise for empty or one condition,
/// to delay allocation.
///
/// Initial to be Option<(K, V)>.
/// If multi item inserted, transit from Option to std::collections::BTreeMap.
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
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
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
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
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
            Self::One(item) => {
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
            Self::Multi(map) => {
                return map.insert(key, value);
            }
        };
        let mut map = BTreeMap::new();
        map.insert(key, value);
        map.insert(old_k, old_v);
        *self = Self::Multi(map);
        None
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        match self {
            Self::One(o) => Iter::One(o.iter()),
            Self::Multi(map) => Iter::Multi(map.iter()),
        }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        match self {
            Self::One(o) => IterMut::One(o.iter_mut()),
            Self::Multi(map) => IterMut::Multi(map.iter_mut()),
        }
    }

    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V> {
        match self {
            Self::One(o) => Keys::One(o.iter()),
            Self::Multi(map) => Keys::Multi(map.keys()),
        }
    }

    #[inline]
    pub fn values(&self) -> Values<'_, K, V> {
        match self {
            Self::One(o) => Values::One(o.iter()),
            Self::Multi(map) => Values::Multi(map.values()),
        }
    }

    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        match self {
            Self::One(o) => ValuesMut::One(o.iter_mut()),
            Self::Multi(map) => ValuesMut::Multi(map.values_mut()),
        }
    }

    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        let mut exists = false;
        match self {
            Self::One(Some(item)) => {
                if item.0 == key {
                    exists = true;
                }
            }
            Self::Multi(map) => match map.entry(key) {
                btree_map::Entry::Occupied(ent) => {
                    return Entry::Occupied(OccupiedEntry::Multi(ent));
                }
                btree_map::Entry::Vacant(ent) => return Entry::Vacant(VacantEntry::Multi(ent)),
            },
            _ => {}
        }
        if !exists {
            return Entry::Vacant(VacantEntry::One(VacantEntryOne { key, map: self }));
        }
        // in order to resolve borrow issue,
        // return field ref only after returning self ref.
        if let Self::One(item) = self {
            return Entry::Occupied(OccupiedEntry::One(item));
        }
        unreachable!();
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::One(Some(_item)) => 1,
            Self::Multi(map) => map.len(),
            _ => 0,
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        match self {
            Self::One(item) => item.is_none(),
            Self::Multi(map) => map.is_empty(),
        }
    }

    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match self {
            Self::One(Some(item)) => item.0.borrow() == key,
            Self::Multi(map) => map.contains_key(key),
            _ => false,
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

pub enum Iter<'a, K, V> {
    One(option::Iter<'a, (K, V)>),
    Multi(btree_map::Iter<'a, K, V>),
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => {
                if let Some(item) = iter.next() {
                    Some((&item.0, &item.1))
                } else {
                    None
                }
            }
            Self::Multi(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::One(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
            Self::Multi(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
        }
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::One(iter) => iter.len(),
            Self::Multi(iter) => iter.len(),
        }
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => {
                if let Some(item) = iter.next_back() {
                    Some((&item.0, &item.1))
                } else {
                    None
                }
            }
            Self::Multi(iter) => iter.next_back(),
        }
    }
}

pub enum IterMut<'a, K, V> {
    One(option::IterMut<'a, (K, V)>),
    Multi(btree_map::IterMut<'a, K, V>),
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => {
                if let Some(item) = iter.next() {
                    Some((&item.0, &mut item.1))
                } else {
                    None
                }
            }
            Self::Multi(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::One(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
            Self::Multi(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
        }
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::One(iter) => iter.len(),
            Self::Multi(iter) => iter.len(),
        }
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => {
                if let Some(item) = iter.next_back() {
                    Some((&item.0, &mut item.1))
                } else {
                    None
                }
            }
            Self::Multi(iter) => iter.next_back(),
        }
    }
}

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

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::One(iter) => {
                if iter.is_some() {
                    1
                } else {
                    0
                }
            }
            Self::Multi(iter) => iter.len(),
        }
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => iter.take(),
            Self::Multi(iter) => iter.next_back(),
        }
    }
}

pub enum Keys<'a, K, V> {
    One(option::Iter<'a, (K, V)>),
    Multi(btree_map::Keys<'a, K, V>),
}

impl<'a, K, V> Clone for Keys<'a, K, V> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Self::One(iter) => Self::One(iter.clone()),
            Self::Multi(iter) => Self::Multi(iter.clone()),
        }
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => iter.next().map(|item| &item.0),
            Self::Multi(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::One(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
            Self::Multi(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
        }
    }
}

impl<'a, K, V> ExactSizeIterator for Keys<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::One(iter) => iter.len(),
            Self::Multi(iter) => iter.len(),
        }
    }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => iter.next_back().map(|item| &item.0),
            Self::Multi(iter) => iter.next_back(),
        }
    }
}

pub enum Values<'a, K, V> {
    One(option::Iter<'a, (K, V)>),
    Multi(btree_map::Values<'a, K, V>),
}

impl<'a, K, V> Clone for Values<'a, K, V> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Self::One(iter) => Self::One(iter.clone()),
            Self::Multi(iter) => Self::Multi(iter.clone()),
        }
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => iter.next().map(|item| &item.1),
            Self::Multi(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::One(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
            Self::Multi(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
        }
    }
}

impl<'a, K, V> ExactSizeIterator for Values<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::One(iter) => iter.len(),
            Self::Multi(iter) => iter.len(),
        }
    }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => iter.next_back().map(|item| &item.1),
            Self::Multi(iter) => iter.next_back(),
        }
    }
}

pub enum ValuesMut<'a, K, V> {
    One(option::IterMut<'a, (K, V)>),
    Multi(btree_map::ValuesMut<'a, K, V>),
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => iter.next().map(|item| &mut item.1),
            Self::Multi(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::One(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
            Self::Multi(iter) => {
                let l = iter.len();
                (l, Some(l))
            }
        }
    }
}

impl<'a, K, V> ExactSizeIterator for ValuesMut<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::One(iter) => iter.len(),
            Self::Multi(iter) => iter.len(),
        }
    }
}

impl<'a, K, V> DoubleEndedIterator for ValuesMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::One(iter) => iter.next_back().map(|item| &mut item.1),
            Self::Multi(iter) => iter.next_back(),
        }
    }
}

pub enum Entry<'a, K: 'a, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

pub enum OccupiedEntry<'a, K: 'a, V: 'a> {
    One(&'a mut Option<(K, V)>),
    Multi(btree_map::OccupiedEntry<'a, K, V>),
}

impl<'a, K, V> OccupiedEntry<'a, K, V>
where
    K: Ord,
{
    #[inline]
    pub fn get(&self) -> &V {
        match self {
            Self::One(o) => &o.as_ref().unwrap().1,
            Self::Multi(ent) => ent.get(),
        }
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        match self {
            Self::One(o) => &mut o.as_mut().unwrap().1,
            Self::Multi(ent) => ent.get_mut(),
        }
    }

    #[inline]
    pub fn key(&self) -> &K {
        match self {
            Self::One(o) => &o.as_ref().unwrap().0,
            Self::Multi(ent) => ent.key(),
        }
    }

    #[inline]
    pub fn remove(self) -> V {
        match self {
            Self::One(o) => {
                let (_k, v) = o.take().unwrap();
                v
            }
            Self::Multi(ent) => ent.remove(),
        }
    }

    #[inline]
    pub fn remove_entry(self) -> (K, V) {
        match self {
            Self::One(o) => o.take().unwrap(),
            Self::Multi(ent) => ent.remove_entry(),
        }
    }

    #[inline]
    pub fn insert(self, value: V) -> V {
        match self {
            Self::One(o) => {
                let (k, old_v) = o.take().unwrap();
                o.replace((k, value));
                old_v
            }
            Self::Multi(mut ent) => ent.insert(value),
        }
    }

    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        match self {
            Self::One(o) => &mut o.as_mut().unwrap().1,
            Self::Multi(ent) => ent.into_mut(),
        }
    }
}

pub enum VacantEntry<'a, K, V> {
    One(VacantEntryOne<'a, K, V>),
    Multi(btree_map::VacantEntry<'a, K, V>),
}

struct VacantEntryOne<'a, K: 'a, V: 'a> {
    pub(crate) key: K,                        // Owned key to insert
    pub(crate) map: &'a mut VariousMap<K, V>, // Reference to the VariousMap
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: Ord,
{
    #[inline]
    pub fn key(&self) -> &K {
        match self {
            Self::One(ent) => &ent.key,
            Self::Multi(ent) => ent.key(),
        }
    }

    #[inline]
    pub fn into_key(self) -> K {
        match self {
            Self::One(ent) => ent.key,
            Self::Multi(ent) => ent.into_key(),
        }
    }

    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        match self {
            Self::One(ent) => {
                let mut _value = MaybeUninit::new(value);
                let mut _key = MaybeUninit::new(ent.key);
                let map = ent.map;
                if let VariousMap::One(item) = map {
                    if item.is_none() {
                        unsafe {
                            // we should have return here, but don't because of the borrow checker
                            item.replace((_key.assume_init_read(), _value.assume_init_read()));
                        }
                    } else {
                        let (old_k, old_v) = item.take().unwrap();
                        unsafe {
                            if &old_k == _key.assume_init_ref() {
                                // we should have return here, but don't because of the borrow checker
                                item.replace((_key.assume_init_read(), _value.assume_init_read()));
                            } else {
                                let _ = item;
                                let mut _map = BTreeMap::new();
                                _map.insert(old_k, old_v);
                                *map = VariousMap::Multi(_map);
                            }
                        }
                    }
                }
                match map {
                    VariousMap::One(Some(item)) => &mut item.1,
                    VariousMap::Multi(map) => unsafe {
                        map.entry(_key.assume_init_read()).or_insert(_value.assume_init_read())
                    },
                    _ => unreachable!(),
                }
            }
            Self::Multi(ent) => ent.insert(value),
        }
    }
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: Ord,
{
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default_fn: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default_fn()),
        }
    }

    #[inline]
    pub fn and_modify<F>(mut self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        if let Entry::Occupied(ref mut entry) = self {
            f(entry.get_mut());
        }
        self
    }

    #[inline]
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    #[inline]
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        match self {
            Entry::Occupied(mut ent) => {
                match ent {
                    OccupiedEntry::One(ref mut o) => {
                        let (k, _old_v) = o.take().unwrap();
                        o.replace((k, value));
                    }
                    OccupiedEntry::Multi(ref mut ent) => {
                        ent.insert(value);
                    }
                }
                ent
            }
            Entry::Vacant(VacantEntry::One(entry)) => {
                let mut _value = MaybeUninit::new(value);
                let mut _key = MaybeUninit::new(entry.key);
                let map = entry.map;
                if let VariousMap::One(item) = map {
                    if item.is_none() {
                        unsafe {
                            item.replace((_key.assume_init_read(), _value.assume_init_read()));
                        }
                    } else {
                        let (old_k, old_v) = item.take().unwrap();
                        unsafe {
                            if &old_k == _key.assume_init_ref() {
                                item.replace((_key.assume_init_read(), _value.assume_init_read()));
                            } else {
                                let _ = item;
                                let mut _map = BTreeMap::new();
                                _map.insert(old_k, old_v);
                                *map = VariousMap::Multi(_map);
                            }
                        }
                    }
                }
                match map {
                    VariousMap::One(o) => OccupiedEntry::One(o),
                    VariousMap::Multi(map) => {
                        let ent = unsafe {
                            map.entry(_key.assume_init_read())
                                .insert_entry(_value.assume_init_read())
                        };
                        OccupiedEntry::Multi(ent)
                    }
                }
            }
            Entry::Vacant(VacantEntry::Multi(ent)) => OccupiedEntry::Multi(ent.insert_entry(value)),
        }
    }

    #[inline]
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(Default::default)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let map: VariousMap<i32, String> = VariousMap::new();
        assert!(matches!(map, VariousMap::One(None)));
    }

    #[test]
    fn test_insert_and_get_one() {
        let mut map = VariousMap::<usize, usize>::new();
        assert_eq!(map.insert(1, 1), None);
        assert!(matches!(map, VariousMap::One(Some((ref k, ref v))) if *k == 1 && *v == 1));
        assert_eq!(map.get(&1), Some(&1));
        assert_eq!(map.get(&2), None);
        **(map.get_mut(&1).as_mut().unwrap()) = 2;
        assert_eq!(map.get(&1), Some(&2));
        assert_eq!(map.insert(1, 3), Some(2));
        assert_eq!(map.get(&1), Some(&3));
    }

    #[test]
    fn test_insert_transition_to_multi() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());
        assert_eq!(map.insert(2, "two".to_string()), None);

        // After inserting a second element, it should transition to BTreeMap
        match map {
            VariousMap::Multi(ref btree_map) => {
                assert_eq!(btree_map.len(), 2);
                assert_eq!(btree_map.get(&1), Some(&"one".to_string()));
                assert_eq!(btree_map.get(&2), Some(&"two".to_string()));
            }
            _ => panic!("Expected Multi variant after inserting two elements"),
        }

        assert_eq!(map.get(&1), Some(&"one".to_string()));
        assert_eq!(map.get(&2), Some(&"two".to_string()));
        assert_eq!(map.get(&3), None);

        **map.get_mut(&2).as_mut().unwrap() = "two_update".to_string();
        assert_eq!(map.get(&2), Some(&"two_update".to_string()));
    }

    #[test]
    fn test_iter_one() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());
        let mut collected: Vec<_> = map.iter().collect();
        collected.sort_by_key(|(k, _)| *k);
        assert_eq!(collected, vec![(&1, &"one".to_string())]);
    }

    #[test]
    fn test_iter_multi() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());
        map.insert(2, "two".to_string()); // Transition to Multi
        map.insert(3, "three".to_string());

        let mut collected: Vec<_> = map.iter().collect();
        collected.sort_by_key(|(k, _)| *k);
        assert_eq!(
            collected,
            vec![(&1, &"one".to_string()), (&2, &"two".to_string()), (&3, &"three".to_string())]
        );
    }

    #[test]
    fn test_into_iter_one() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());
        let mut collected: Vec<_> = map.into_iter().collect();
        collected.sort_by_key(|(k, _)| *k);
        assert_eq!(collected, vec![(1, "one".to_string())]);
    }

    #[test]
    fn test_contains_key() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());
        assert!(map.contains_key(&1));
        assert!(!map.contains_key(&2));

        map.insert(2, "two".to_string()); // Transition to Multi
        assert!(map.contains_key(&1));
        assert!(map.contains_key(&2));
        assert!(!map.contains_key(&3));
    }

    #[test]
    fn test_entry_api_one() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());

        // Occupied
        match map.entry(1) {
            Entry::Occupied(ent) => {
                assert_eq!(ent.get(), &"one".to_string());
                ent.insert("one_updated".to_string());
            }
            Entry::Vacant(_) => panic!("Should be occupied"),
        }
        assert_eq!(map.get(&1), Some(&"one_updated".to_string()));

        // Vacant
        match map.entry(2) {
            Entry::Occupied(_) => panic!("Should be vacant"),
            Entry::Vacant(ent) => {
                ent.insert("two".to_string());
            }
        }
        assert!(map.contains_key(&2));
    }

    #[test]
    fn test_entry_api_or_insert() {
        let mut map = VariousMap::new();
        map.entry(1).or_insert("one".to_string());

        // Occupied
        let v = map
            .entry(1)
            .and_modify(|v| {
                *v = "one_3".to_string();
            })
            .or_insert("one_2".to_string());
        assert_eq!(v, &"one_3".to_string());

        // Vacant
        map.entry(2).or_insert("two".to_string());
        assert_eq!(map.get(&2), Some(&"two".to_string()));
    }

    #[test]
    fn test_entry_api_insert_entry() {
        let mut map = VariousMap::new();

        // Vacant -> insert_entry
        let occupied = map.entry(1).insert_entry("one".to_string());
        assert_eq!(occupied.get(), &"one".to_string());

        // Occupied -> insert_entry
        let occupied = map.entry(1).insert_entry("one_updated".to_string());
        assert_eq!(occupied.get(), &"one_updated".to_string());
        assert_eq!(map.get(&1), Some(&"one_updated".to_string()));
    }

    #[test]
    fn test_keys() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());
        assert_eq!(map.keys().collect::<Vec<_>>(), vec![&1]);

        map.insert(2, "two".to_string());
        let mut keys = map.keys().collect::<Vec<_>>();
        keys.sort();
        assert_eq!(keys, vec![&1, &2]);
    }

    #[test]
    fn test_values() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());
        assert_eq!(map.values().collect::<Vec<_>>(), vec![&"one".to_string()]);

        map.insert(2, "two".to_string());
        let mut values = map.values().collect::<Vec<_>>();
        values.sort();
        assert_eq!(values, vec![&"one".to_string(), &"two".to_string()]);
    }

    #[test]
    fn test_values_mut() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());
        for v in map.values_mut() {
            *v = "one_updated".to_string();
        }
        assert_eq!(map.get(&1), Some(&"one_updated".to_string()));

        map.insert(2, "two".to_string());
        for v in map.values_mut() {
            v.push_str("_mut");
        }
        assert_eq!(map.get(&1), Some(&"one_updated_mut".to_string()));
        assert_eq!(map.get(&2), Some(&"two_mut".to_string()));
    }

    #[test]
    fn test_iter_mut() {
        let mut map = VariousMap::new();
        map.insert(1, "one".to_string());
        for (k, v) in map.iter_mut() {
            assert_eq!(k, &1);
            *v = "one_updated".to_string();
        }
        assert_eq!(map.get(&1), Some(&"one_updated".to_string()));

        map.insert(2, "two".to_string());
        for (k, v) in map.iter_mut() {
            if *k == 1 {
                *v = "one_final".to_string();
            } else if *k == 2 {
                *v = "two_final".to_string();
            }
        }
        assert_eq!(map.get(&1), Some(&"one_final".to_string()));
        assert_eq!(map.get(&2), Some(&"two_final".to_string()));
    }
}
