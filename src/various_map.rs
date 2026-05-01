use alloc::collections::BTreeMap;
use alloc::collections::btree_map;
use core::borrow::Borrow;
use core::mem::MaybeUninit;
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

// New Entry API Definitions (Revised)
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
                return v;
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

pub struct VacantEntry<'a, K: 'a, V: 'a> {
    pub(crate) key: K,                        // Owned key to insert
    pub(crate) map: &'a mut VariousMap<K, V>, // Reference to the VariousMap
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: Ord,
{
    #[inline]
    pub fn key(&self) -> &K {
        &self.key
    }

    #[inline]
    pub fn into_key(self) -> K {
        self.key
    }

    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        let mut _value = MaybeUninit::new(value);
        let mut _key = MaybeUninit::new(self.key);
        let map = self.map;
        if let VariousMap::One(item) = map {
            if item.is_none() {
                unsafe {
                    item.replace((_key.assume_init_read(), _value.assume_init_read()));
                }
                // we should have return here, but don't because of the borrow checker
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
            VariousMap::One(Some(item)) => &mut item.1,
            VariousMap::Multi(map) => unsafe {
                map.entry(_key.assume_init_read()).or_insert(_value.assume_init_read())
            },
            _ => unreachable!(),
        }
    }
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: Ord,
    V: Default,
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
            Entry::Vacant(entry) => {
                let mut _value = MaybeUninit::new(value);
                let mut _key = MaybeUninit::new(entry.key);
                let map = entry.map;
                if let VariousMap::One(item) = map {
                    if item.is_none() {
                        unsafe {
                            item.replace((_key.assume_init_read(), _value.assume_init_read()));
                        }
                        // we should have return here, but don't because of the borrow checker
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
