//! A vector that allows for generational indexing.
//! 
//! This is essentially a rewrite of a subset of the `slotmap` crate since we can't implement [`Collect`] on foreign types.

use alloc::vec::{self, Vec};
use core::marker::PhantomData;
use core::{slice, iter};

use crate::gc::*;

/// A key that can be used with a [`SlotMap`].
/// 
/// Instead of implementing this trait manually, it is recommended to use the [`new_key`](crate::new_key) macro.
pub trait Key: Copy + Eq + Ord + 'static {
    fn new(slot: usize, generation: usize) -> Self;
    fn get_slot(&self) -> usize;
    fn get_generation(&self) -> usize;
}

/// Defines a new key type for use in [`SlotMap`].
#[macro_export]
macro_rules! new_key {
    ($($(#[doc = $doc:expr])? $vis:vis struct $name:ident;)*) => {$(
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        $(#[doc = $doc])?
        $vis struct $name(usize, usize);
        impl $crate::slotmap::Key for $name {
            fn new(slot: usize, generation: usize) -> Self { Self(slot, generation) }
            fn get_slot(&self) -> usize { self.0 }
            fn get_generation(&self) -> usize { self.1 }
        }
    )*}
}

#[derive(Clone, Collect)]
#[collect(no_drop)]
struct Slot<T> {
                               value: Option<T>,
    #[collect(require_static)] generation: usize,
}

/// A dense, resizable array that supports generational indexing.
/// 
/// You can use the [`new_key`](crate::new_key) macro to create a new key type to use.
/// It is recommended to use different key types for different collections to avoid accidentally using a key from a different map.
#[derive(Clone, Collect)]
#[collect(no_drop)]
pub struct SlotMap<K: Key, T> {
                               slots: Vec<Slot<T>>,
    #[collect(require_static)] empty_slots: Vec<usize>,
    #[collect(require_static)] num_values: usize,
    #[collect(require_static)] _key: PhantomData<K>
}
impl<K: Key, T> Default for SlotMap<K, T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<K: Key, T> SlotMap<K, T> {
    /// Creates a new empty container.
    pub fn new() -> Self {
        SlotMap {
            slots: vec![],
            empty_slots: vec![],
            num_values: 0,
            _key: PhantomData,
        }
    }
    #[cfg(test)]
    fn invariant(&self) -> bool {
        self.num_values == self.slots.iter().filter(|x| x.value.is_some()).count()
        &&
        self.num_values + self.empty_slots.len() == self.slots.len()
    }
    /// Adds a new value to the map and returns a new key that references it.
    pub fn insert(&mut self, value: T) -> K {
        #[cfg(test)] assert!(self.invariant());

        self.num_values += 1;
        let key = match self.empty_slots.pop() {
            Some(slot) => {
                debug_assert!(self.slots[slot].value.is_none());
                self.slots[slot].value = Some(value);
                K::new(slot, self.slots[slot].generation)
            }
            None => {
                debug_assert!(self.slots.iter().all(|x| x.value.is_some()));
                let slot = self.slots.len();
                self.slots.push(Slot { value: Some(value), generation: 0 });
                K::new(slot, 0)
            }
        };

        #[cfg(test)] assert!(self.invariant());
        #[allow(clippy::let_and_return)] key
    }
    /// Removes a value from the map and returns it (if it existed).
    /// It is guaranteed that all future accesses with the removed key will return [`None`].
    pub fn remove(&mut self, key: K) -> Option<T> {
        #[cfg(test)] assert!(self.invariant());

        let slot = self.slots.get_mut(key.get_slot())?;
        let res = if slot.generation == key.get_generation() { slot.value.take() } else { None };
        if res.is_some() {
            slot.generation += 1;
            self.num_values -= 1;
            self.empty_slots.push(key.get_slot());
        }

        #[cfg(test)] assert!(self.invariant());
        res
    }
    /// Removes all values from the slotmap.
    pub fn clear(&mut self) {
        #[cfg(test)] assert!(self.invariant());

        for (i, slot) in self.slots.iter_mut().enumerate() {
            if slot.value.take().is_some() {
                slot.generation += 1;
                self.empty_slots.push(i);
            }
        }
        self.num_values = 0;

        #[cfg(test)] assert!(self.invariant());
    }
    /// Retains only the values for which the predicate returns true.
    /// For all retained values, any existing keys are still valid after this operation.
    pub fn retain_mut<F: FnMut(K, &mut T) -> bool>(&mut self, mut f: F) {
        #[cfg(test)] assert!(self.invariant());

        for (i, slot) in self.slots.iter_mut().enumerate() {
            if let Some(value) = &mut slot.value {
                if !f(K::new(i, slot.generation), value) {
                    slot.value = None;
                    slot.generation += 1;
                    self.num_values -= 1;
                    self.empty_slots.push(i);
                }
            }
        }

        #[cfg(test)] assert!(self.invariant());
    }
    /// Get a reference to a value in the map.
    pub fn get(&self, key: K) -> Option<&T> {
        let slot = self.slots.get(key.get_slot())?;
        if slot.generation == key.get_generation() { slot.value.as_ref() } else { None }
    }
    /// Get a mutable reference to a value in the map.
    pub fn get_mut(&mut self, key: K) -> Option<&mut T> {
        let slot = self.slots.get_mut(key.get_slot())?;
        if slot.generation == key.get_generation() { slot.value.as_mut() } else { None }
    }
    /// Get the number of values stored in the map.
    pub fn len(&self) -> usize {
        self.num_values
    }
    /// Checks if the map is currently empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Iterates over the keys and values currently stored in the map.
    pub fn iter(&self) -> Iter<K, T> {
        Iter(self.slots.iter().enumerate(), PhantomData)
    }
    /// Mutably iterates over the keys and values currently stored in the map.
    pub fn iter_mut(&mut self) -> IterMut<K, T> {
        IterMut(self.slots.iter_mut().enumerate(), PhantomData)
    }
}
impl<K: Key, T> IntoIterator for SlotMap<K, T> {
    type IntoIter = IntoIter<K, T>;
    type Item = (K, T);
    fn into_iter(self) -> IntoIter<K, T> {
        IntoIter(self.slots.into_iter().enumerate(), PhantomData)
    }
}

pub struct IntoIter<K: Key, T>(iter::Enumerate<vec::IntoIter<Slot<T>>>, PhantomData<K>);
pub struct Iter<'a, K: Key, T>(iter::Enumerate<slice::Iter<'a, Slot<T>>>, PhantomData<K>);
pub struct IterMut<'a, K: Key, T>(iter::Enumerate<slice::IterMut<'a, Slot<T>>>, PhantomData<K>);

impl<K: Key, T> Iterator for IntoIter<K, T> {
    type Item = (K, T);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (i, slot) = self.0.next()?;
            if let Some(x) = slot.value { return Some((K::new(i, slot.generation), x)) }
        }
    }
}
impl<'a, K: Key, T> Iterator for Iter<'a, K, T> {
    type Item = (K, &'a T);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (i, slot) = self.0.next()?;
            if let Some(x) = slot.value.as_ref() { return Some((K::new(i, slot.generation), x)) }
        }
    }
}
impl<'a, K: Key, T> Iterator for IterMut<'a, K, T> {
    type Item = (K, &'a mut T);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (i, slot) = self.0.next()?;
            if let Some(x) = slot.value.as_mut() { return Some((K::new(i, slot.generation), x)) }
        }
    }
}

#[test]
fn test_slotmap() {
    use alloc::collections::BTreeSet;
    new_key! {
        struct TestKey;
    }
    let mut map: SlotMap<TestKey, i32> = SlotMap::new();
    assert_eq!(map.len(), 0);
    assert_eq!(map.slots.len(), 0);

    let key = map.insert(56);
    assert_eq!(*map.get(key).unwrap(), 56);
    *map.get_mut(key).unwrap() = 23;
    assert_eq!(*map.get(key).unwrap(), 23);
    assert_eq!(map.slots.len(), 1);

    let key2 = map.insert(11);
    assert_eq!(*map.get(key).unwrap(), 23);
    assert_eq!(*map.get(key2).unwrap(), 11);
    assert_eq!(map.slots.len(), 2);

    assert_eq!(map.remove(key), Some(23));
    assert!(map.get(key).is_none());
    assert_eq!(*map.get(key2).unwrap(), 11);
    assert_eq!(map.slots.len(), 2);

    assert_eq!(map.remove(key), None);
    assert!(map.get(key).is_none());
    assert_eq!(*map.get(key2).unwrap(), 11);
    assert_eq!(map.slots.len(), 2);

    for (_, v) in map.iter_mut() { *v += 1; }
    assert!(map.get(key).is_none());
    assert_eq!(*map.get(key2).unwrap(), 12);
    assert_eq!(map.slots.len(), 2);

    assert_eq!(map.remove(key2), Some(12));
    assert!(map.get(key).is_none());
    assert!(map.get(key2).is_none());
    assert_eq!(map.slots.len(), 2);

    assert_eq!(map.remove(key2), None);
    assert!(map.get(key).is_none());
    assert!(map.get(key2).is_none());
    assert_eq!(map.slots.len(), 2);

    for _ in 0..4 {
        let mut keys = vec![];
        for i in 0..128 {
            keys.push((map.insert(i), i));
        }
        assert_eq!(map.slots.len(), 128);
        keys[20..].reverse();
        keys[..100].reverse();
        keys[40..70].reverse();

        for i in 0..keys.len() {
            assert_eq!(map.len(), 128 - i);
            for j in 0..i {
                assert!(map.get(keys[j].0).is_none());
                assert!(map.get_mut(keys[j].0).is_none());
                assert!(map.remove(keys[j].0).is_none());
            }
            assert_eq!(*map.get(keys[i].0).unwrap(), keys[i].1);
            assert_eq!(*map.get_mut(keys[i].0).unwrap(), keys[i].1);
            assert_eq!(map.remove(keys[i].0), Some(keys[i].1));
            assert_eq!(map.remove(keys[i].0), None);
            assert_eq!(map.remove(keys[i].0), None);
            assert!(map.get(keys[i].0).is_none());
            assert!(map.get_mut(keys[i].0).is_none());
            for j in i+1..keys.len() {
                assert_eq!(*map.get(keys[j].0).unwrap(), keys[j].1);
                assert_eq!(*map.get_mut(keys[j].0).unwrap(), keys[j].1);
            }
            assert_eq!(map.len(), 128 - i - 1);

            let mut cache = BTreeSet::default();
            let cpy = map.clone();

            cache.clear();
            for (key, val) in map.iter() {
                assert!(cache.insert(*val));
                assert_eq!(map.get(key).unwrap(), val);
                assert_eq!(cpy.get(key).unwrap(), val);
            }
            cache.clear();
            for (key, val) in map.iter_mut() {
                assert!(cache.insert(*val));
                assert_eq!(cpy.get(key).unwrap(), val);
            }
            cache.clear();
            for (key, val) in map.clone() {
                assert!(cache.insert(val));
                assert_eq!(*map.get(key).unwrap(), val);
                assert_eq!(*cpy.get(key).unwrap(), val);
            }
        }
    }

    assert_eq!(map.slots.len(), 128);
    assert_eq!(map.len(), 0);
    assert!(map.is_empty());

    let mut keys = vec![];
    for i in 0..32 {
        keys.push((i, map.insert(i)));
    }
    keys[..25].reverse();
    keys[7..].reverse();
    keys[11..19].reverse();

    assert_eq!(map.slots.len(), 128);
    assert_eq!(map.len(), 32);
    assert!(!map.is_empty());
    for (i, key) in keys.iter().copied() {
        assert_eq!(*map.get(key).unwrap(), i);
        assert_eq!(*map.get_mut(key).unwrap(), i);
    }

    map.clear();
    assert_eq!(map.slots.len(), 128);
    assert_eq!(map.len(), 0);
    assert!(map.is_empty());
    for (_, key) in keys.iter().copied() {
        assert_eq!(map.get(key).copied(), None);
        assert_eq!(map.get_mut(key).copied(), None);
    }

    map.clear();
    let k1 = map.insert(12);
    assert_eq!(map.remove(k1), Some(12));
    assert_eq!(map.remove(k1), None);
    assert_eq!(map.remove(k1), None);
    let k2 = map.insert(13);
    assert_eq!(k1.0, k2.0);
    assert_eq!(k1.1 + 1, k2.1);
    assert_eq!(map.remove(k1), None);
    assert_eq!(map.remove(k1), None);
    assert_eq!(map.remove(k2), Some(13));
    assert_eq!(map.remove(k2), None);
    assert_eq!(map.remove(k2), None);

    map.clear();
    let kv1 = map.insert(54);
    let kv2 = map.insert(-4);
    let kv3 = map.insert(51);
    let kv4 = map.insert(-53);
    let kv5 = map.insert(52);
    let kv6 = map.insert(12);
    let kv7 = map.insert(2);
    assert_eq!(map.get(kv1).copied(), Some(54));
    assert_eq!(map.get(kv2).copied(), Some(-4));
    assert_eq!(map.get(kv3).copied(), Some(51));
    assert_eq!(map.get(kv4).copied(), Some(-53));
    assert_eq!(map.get(kv5).copied(), Some(52));
    assert_eq!(map.get(kv6).copied(), Some(12));
    assert_eq!(map.get(kv7).copied(), Some(2));
    map.retain_mut(|k, v| k == kv6 || *v % 2 != 0);
    assert_eq!(map.get(kv1).copied(), None);
    assert_eq!(map.get(kv2).copied(), None);
    assert_eq!(map.get(kv3).copied(), Some(51));
    assert_eq!(map.get(kv4).copied(), Some(-53));
    assert_eq!(map.get(kv5).copied(), None);
    assert_eq!(map.get(kv6).copied(), Some(12));
    assert_eq!(map.get(kv7).copied(), None);
}
