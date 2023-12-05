//! A map type implemented as a sorted list of key/value pairs.
//! 
//! For a small numbers of smallish elements, this is faster than other associative structures like `BTreeMap` and `HashMap`.
//! Because of this, it is used as the collection type for symbol tables in the vm.
//! 
//! As a general benchmark, it was found that the break even point for a worst case scenario with
//! `String` keys and `16`-byte values (as the vm uses) was over 80 elements, vastly more than we expect to have in practice.
//! Additionally, that was only for insertion; actual lookup time was around 2x faster (compared to `BTreeMap` as was used previously).

use alloc::vec::Vec;
use alloc::borrow::Borrow;

#[cfg(feature = "serde")]
use serde::{Serialize, Deserialize};

use crate::gc::*;

#[derive(Collect, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[collect(no_drop, bound = "where V: Collect")]
pub struct Entry<K: Ord + 'static, V> {
    #[collect(require_static)] pub key: K,
                               pub value: V,
}
/// A map type implemented as a list of key/value pairs.
/// 
/// If the const generic `SORTED` is set to `true`, keys will be sorted in ascending order, lookups are `O(log(n))`, and insertions are `O(n)`.
/// If `SORTED` is set to `false`, keys will be sorted in insertion order, lookups are `O(n)`, and insertions are `O(1)`.
#[derive(Collect, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[collect(no_drop, bound = "where V: Collect")]
pub struct VecMap<K: Ord + 'static, V, const SORTED: bool> {
    values: Vec<Entry<K, V>>,
}
impl<K: Ord + 'static, V, const SORTED: bool> VecMap<K, V, SORTED> {
    /// Creates a new, empty map.
    pub fn new() -> Self {
        Self { values: vec![] }
    }
    /// Creates a new, empty map with the specified capacity.
    pub fn with_capacity(cap: usize) -> Self {
        Self { values: Vec::with_capacity(cap) }
    }
    /// Gets an immutable reference to a stored value, if it exists.
    pub fn get<Q: ?Sized + Ord>(&self, key: &Q) -> Option<&V> where K: Borrow<Q> {
        match SORTED {
            true => self.values.binary_search_by(|x| x.key.borrow().cmp(key)).ok().map(|i| &self.values[i].value),
            false => self.values.iter().find(|x| x.key.borrow() == key).map(|x| &x.value),
        }
    }
    /// Gets a mutable reference to a stored value, if it exists.
    pub fn get_mut<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<&mut V> where K: Borrow<Q> {
        match SORTED {
            true => self.values.binary_search_by(|x| x.key.borrow().cmp(key)).ok().map(|i| &mut self.values[i].value),
            false => self.values.iter_mut().find(|x| x.key.borrow() == key).map(|x| &mut x.value),
        }
    }
    /// Inserts a new value into the map.
    /// If an entry with the same key already exists, the previous value is returned.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match SORTED {
            true => match self.values.binary_search_by(|x| x.key.cmp(&key)) {
                Ok(i) => Some(core::mem::replace(&mut self.values[i].value, value)),
                Err(i) => {
                    self.values.insert(i, Entry { key, value });
                    None
                }
            }
            false => match self.get_mut(&key) {
                Some(x) => Some(core::mem::replace(x, value)),
                None => {
                    self.values.push(Entry { key, value });
                    None
                }
            }
        }
    }
    /// Gets the number of values stored in the map.
    pub fn len(&self) -> usize {
        self.values.len()
    }
    /// Checks if the map is currently empty (no values).
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
    /// Iterates through the map.
    pub fn iter(&self) -> Iter<K, V> {
        Iter(self.values.iter())
    }
    /// Iterates through the map.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut(self.values.iter_mut())
    }
    /// Gets a raw slice of the entries stored in the map.
    pub fn as_slice(&self) -> &[Entry<K, V>] {
        self.values.as_slice()
    }
}

impl<K: Ord + 'static, V, const SORTED: bool> Default for VecMap<K, V, SORTED> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + 'static, V, const SORTED: bool> IntoIterator for VecMap<K, V, SORTED> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.values.into_iter())
    }
}

pub struct IntoIter<K: Ord + 'static, V>(alloc::vec::IntoIter<Entry<K, V>>);
impl<K: Ord + 'static, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|x| (x.key, x.value))
    }
}

pub struct Iter<'a, K: Ord + 'static, V>(core::slice::Iter<'a, Entry<K, V>>);
impl<'a, K: Ord + 'static, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|x| (&x.key, &x.value))
    }
}

pub struct IterMut<'a, K: Ord + 'static, V>(core::slice::IterMut<'a, Entry<K, V>>);
impl<'a, K: Ord + 'static, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|x| (&x.key, &mut x.value))
    }
}

impl<K: Ord + 'static, V, const SORTED: bool> FromIterator<(K, V)> for VecMap<K, V, SORTED> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut res = VecMap::<K, V, SORTED>::new();
        for (k, v) in iter {
            res.insert(k, v);
        }
        res
    }
}

#[test]
fn test_vecmap_sorted() {
    let mut v = VecMap::<usize, usize, true>::new();
    assert_eq!(v.len(), 0);
    assert_eq!(v.as_slice().len(), 0);
    assert_eq!(v.is_empty(), true);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), []);

    assert_eq!(v.insert(45, 12), None);
    assert_eq!(v.len(), 1);
    assert_eq!(v.as_slice().len(), 1);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 12)]);

    assert_eq!(v.insert(56, 6), None);
    assert_eq!(v.len(), 2);
    assert_eq!(v.as_slice().len(), 2);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 12), (56, 6)]);

    assert_eq!(v.insert(80, 3), None);
    assert_eq!(v.len(), 3);
    assert_eq!(v.as_slice().len(), 3);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 12), (56, 6), (80, 3)]);

    assert_eq!(v.insert(2, 654), None);
    assert_eq!(v.len(), 4);
    assert_eq!(v.as_slice().len(), 4);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(2, 654), (45, 12), (56, 6), (80, 3)]);

    assert_eq!(v.insert(56, 98), Some(6));
    assert_eq!(v.len(), 4);
    assert_eq!(v.as_slice().len(), 4);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(2, 654), (45, 12), (56, 98), (80, 3)]);

    *v.get_mut(&80).unwrap() = 13;
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(2, 654), (45, 12), (56, 98), (80, 13)]);
    *v.get_mut(&45).unwrap() = 444;
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(2, 654), (45, 444), (56, 98), (80, 13)]);

    assert_eq!(v.get_mut(&2).map(|x| *x), Some(654));
    assert_eq!(v.get_mut(&45).map(|x| *x), Some(444));
    assert_eq!(v.get_mut(&56).map(|x| *x), Some(98));
    assert_eq!(v.get_mut(&80).map(|x| *x), Some(13));
    assert_eq!(v.get_mut(&81).map(|x| *x), None);
    assert_eq!(v.get_mut(&69).map(|x| *x), None);
    assert_eq!(v.get_mut(&0).map(|x| *x), None);
    assert_eq!(v.get_mut(&21).map(|x| *x), None);
    assert_eq!(v.get_mut(&50).map(|x| *x), None);

    assert_eq!(v.get(&2).map(|x| *x), Some(654));
    assert_eq!(v.get(&45).map(|x| *x), Some(444));
    assert_eq!(v.get(&56).map(|x| *x), Some(98));
    assert_eq!(v.get(&80).map(|x| *x), Some(13));
    assert_eq!(v.get(&81).map(|x| *x), None);
    assert_eq!(v.get(&69).map(|x| *x), None);
    assert_eq!(v.get(&0).map(|x| *x), None);
    assert_eq!(v.get(&21).map(|x| *x), None);
    assert_eq!(v.get(&50).map(|x| *x), None);

    assert_eq!(v.insert(50, 3), None);
    assert_eq!(v.len(), 5);
    assert_eq!(v.as_slice().len(), 5);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(2, 654), (45, 444), (50, 3), (56, 98), (80, 13)]);
}

#[test]
fn test_vecmap_unsorted() {
    let mut v = VecMap::<usize, usize, false>::new();
    assert_eq!(v.len(), 0);
    assert_eq!(v.as_slice().len(), 0);
    assert_eq!(v.is_empty(), true);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), []);

    assert_eq!(v.insert(45, 12), None);
    assert_eq!(v.len(), 1);
    assert_eq!(v.as_slice().len(), 1);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 12)]);

    assert_eq!(v.insert(56, 6), None);
    assert_eq!(v.len(), 2);
    assert_eq!(v.as_slice().len(), 2);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 12), (56, 6)]);

    assert_eq!(v.insert(80, 3), None);
    assert_eq!(v.len(), 3);
    assert_eq!(v.as_slice().len(), 3);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 12), (56, 6), (80, 3)]);

    assert_eq!(v.insert(2, 654), None);
    assert_eq!(v.len(), 4);
    assert_eq!(v.as_slice().len(), 4);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 12), (56, 6), (80, 3), (2, 654)]);

    assert_eq!(v.insert(56, 98), Some(6));
    assert_eq!(v.len(), 4);
    assert_eq!(v.as_slice().len(), 4);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 12), (56, 98), (80, 3), (2, 654)]);

    *v.get_mut(&80).unwrap() = 13;
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 12), (56, 98), (80, 13), (2, 654)]);
    *v.get_mut(&45).unwrap() = 444;
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 444), (56, 98), (80, 13), (2, 654)]);

    assert_eq!(v.get_mut(&2).map(|x| *x), Some(654));
    assert_eq!(v.get_mut(&45).map(|x| *x), Some(444));
    assert_eq!(v.get_mut(&56).map(|x| *x), Some(98));
    assert_eq!(v.get_mut(&80).map(|x| *x), Some(13));
    assert_eq!(v.get_mut(&81).map(|x| *x), None);
    assert_eq!(v.get_mut(&69).map(|x| *x), None);
    assert_eq!(v.get_mut(&0).map(|x| *x), None);
    assert_eq!(v.get_mut(&21).map(|x| *x), None);
    assert_eq!(v.get_mut(&50).map(|x| *x), None);

    assert_eq!(v.get(&2).map(|x| *x), Some(654));
    assert_eq!(v.get(&45).map(|x| *x), Some(444));
    assert_eq!(v.get(&56).map(|x| *x), Some(98));
    assert_eq!(v.get(&80).map(|x| *x), Some(13));
    assert_eq!(v.get(&81).map(|x| *x), None);
    assert_eq!(v.get(&69).map(|x| *x), None);
    assert_eq!(v.get(&0).map(|x| *x), None);
    assert_eq!(v.get(&21).map(|x| *x), None);
    assert_eq!(v.get(&50).map(|x| *x), None);

    assert_eq!(v.insert(50, 3), None);
    assert_eq!(v.len(), 5);
    assert_eq!(v.as_slice().len(), 5);
    assert_eq!(v.is_empty(), false);
    assert_eq!(v.iter().map(|x| (*x.0, *x.1)).collect::<Vec<_>>(), [(45, 444), (56, 98), (80, 13), (2, 654), (50, 3)]);
}
