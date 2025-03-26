// SPDX-License-Identifier: LGPL-3.0-or-later
//
// Copyright © 2025 Jaxydog
//
// This file is part of Recomposition.
//
// Recomposition is free software: you can redistribute it and/or modify it under the terms of the GNU Lesser General
// Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// Recomposition is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied
// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
// details.
//
// You should have received a copy of the GNU Lesser General Public License along with Recomposition. If not, see
// <https://www.gnu.org/licenses/>.

//! Implements composable filters.

use core::marker::PhantomData;

/// A value that acts as a filter for a given type.
pub trait Filter<T: ?Sized>: Sized {
    /// Returns `true` if the given value passes this [`Filter`] implementation.
    ///
    /// This function's output should ideally be deterministic, however this is left up to the type's implementation.
    fn test(&self, value: &T) -> bool;

    /// Returns a new [`Filter`] implementation that inverts the result of this implementation.
    #[inline]
    fn not(self) -> Not<T, Self> {
        Not { filter: self, marker: PhantomData }
    }

    /// Returns a new [`Filter`] implementation that combines the results of both implementations using a logical AND.
    #[inline]
    fn and<F>(self, other: F) -> And<T, Self, F>
    where
        F: Filter<T>,
    {
        And { filter_a: self, filter_b: other, marker: PhantomData }
    }

    /// Returns a new [`Filter`] implementation that combines the results of both implementations using a logical OR.
    #[inline]
    fn or<F>(self, other: F) -> Or<T, Self, F>
    where
        F: Filter<T>,
    {
        Or { filter_a: self, filter_b: other, marker: PhantomData }
    }

    /// Returns a new [`Filter`] implementation that combines the results of both implementations using a logical XOR.
    #[inline]
    fn xor<F>(self, other: F) -> Xor<T, Self, F>
    where
        F: Filter<T>,
    {
        Xor { filter_a: self, filter_b: other, marker: PhantomData }
    }
}

impl<T, F> Filter<T> for &F
where
    T: ?Sized,
    F: Filter<T>,
{
    #[inline]
    fn test(&self, value: &T) -> bool {
        <F as Filter<T>>::test(self, value)
    }
}

impl<T, F> Filter<T> for &mut F
where
    T: ?Sized,
    F: Filter<T>,
{
    #[inline]
    fn test(&self, value: &T) -> bool {
        <F as Filter<T>>::test(self, value)
    }
}

#[cfg(feature = "std")]
impl<T, F> Filter<T> for Box<F>
where
    T: ?Sized,
    F: Filter<T>,
{
    #[inline]
    fn test(&self, value: &T) -> bool {
        <F as Filter<T>>::test(self, value)
    }
}

/// A [`Filter`] implementation that always returns `true`.
#[derive(Clone, Debug)]
pub struct Always<T>(PhantomData<fn(&T)>)
where
    T: ?Sized;

impl<T> Filter<T> for Always<T>
where
    T: ?Sized,
{
    #[inline]
    fn test(&self, _: &T) -> bool {
        true
    }
}

/// A [`Filter`] implementation that always returns `false`.
#[derive(Clone, Debug)]
pub struct Never<T>(PhantomData<fn(&T)>)
where
    T: ?Sized;

impl<T> Filter<T> for Never<T>
where
    T: ?Sized,
{
    #[inline]
    fn test(&self, _: &T) -> bool {
        false
    }
}

/// Inverts the stored [`Filter`] implementation.
#[derive(Clone, Debug)]
pub struct Not<T, F>
where
    T: ?Sized,
{
    /// The inner filter.
    filter: F,
    /// Retains the type being sorted.
    marker: PhantomData<fn(&T)>,
}

impl<T, F> Filter<T> for Not<T, F>
where
    T: ?Sized,
    F: Filter<T>,
{
    #[inline]
    fn test(&self, value: &T) -> bool {
        !self.filter.test(value)
    }
}

/// Combines two filters using a logical AND.
#[derive(Clone, Debug)]
pub struct And<T, A, B>
where
    T: ?Sized,
{
    /// The first inner filter.
    filter_a: A,
    /// The second inner filter.
    filter_b: B,
    /// Retains the type being sorted.
    marker: PhantomData<fn(&T)>,
}

impl<T, A, B> Filter<T> for And<T, A, B>
where
    T: ?Sized,
    A: Filter<T>,
    B: Filter<T>,
{
    #[inline]
    fn test(&self, value: &T) -> bool {
        self.filter_a.test(value) && self.filter_b.test(value)
    }
}

/// Combines two filters using a logical OR.
#[derive(Clone, Debug)]
pub struct Or<T, A, B>
where
    T: ?Sized,
{
    /// The first inner filter.
    filter_a: A,
    /// The second inner filter.
    filter_b: B,
    /// Retains the type being sorted.
    marker: PhantomData<fn(&T)>,
}

impl<T, A, B> Filter<T> for Or<T, A, B>
where
    T: ?Sized,
    A: Filter<T>,
    B: Filter<T>,
{
    #[inline]
    fn test(&self, value: &T) -> bool {
        self.filter_a.test(value) || self.filter_b.test(value)
    }
}

/// Combines two filters using a logical XOR.
#[derive(Clone, Debug)]
pub struct Xor<T, A, B>
where
    T: ?Sized,
{
    /// The first inner filter.
    filter_a: A,
    /// The second inner filter.
    filter_b: B,
    /// Retains the type being sorted.
    marker: PhantomData<fn(&T)>,
}

impl<T, A, B> Filter<T> for Xor<T, A, B>
where
    T: ?Sized,
    A: Filter<T>,
    B: Filter<T>,
{
    #[inline]
    fn test(&self, value: &T) -> bool {
        self.filter_a.test(value) ^ self.filter_b.test(value)
    }
}

/// Uses the given function as a [`Filter`] implementation.
#[derive(Clone, Debug)]
pub struct FromFn<T, F>
where
    T: ?Sized,
{
    /// The predicate function.
    function: F,
    /// Retains the type being sorted.
    marker: PhantomData<fn(&T)>,
}

impl<T, F> Filter<T> for FromFn<T, F>
where
    T: ?Sized,
    F: Fn(&T) -> bool,
{
    #[inline]
    fn test(&self, value: &T) -> bool {
        (self.function)(value)
    }
}

/// Returns a [`Filter`] implementation that always returns `true`.
#[inline]
#[must_use]
pub const fn always<T>() -> Always<T>
where
    T: ?Sized,
{
    Always(PhantomData)
}

/// Returns a [`Filter`] implementation that always returns `true`.
#[inline]
#[must_use]
pub const fn never<T>() -> Never<T>
where
    T: ?Sized,
{
    Never(PhantomData)
}

/// Creates a [`Filter`] implementation using the given function.
///
/// The given function's output should ideally be deterministic.
#[inline]
pub const fn from_fn<T, F>(f: F) -> FromFn<T, F>
where
    T: ?Sized,
    F: Fn(&T) -> bool,
{
    FromFn { function: f, marker: PhantomData }
}

/// Extends a type so that it may be filtered.
pub trait ListFilterExt<T> {
    /// Filters elements out of this value that do not match the given [`Filter`] implementation.
    fn filter<F>(&mut self, filter: F)
    where
        F: Filter<T>;
}

/// Extends a type so that it may be filtered.
pub trait MapFilterExt<K, V> {
    /// Filters keys out of this map that do not match the given [`Filter`] implementation.
    fn filter_keys<F>(&mut self, filter: F)
    where
        F: Filter<K>;

    /// Filters values out of this map that do not match the given [`Filter`] implementation.
    fn filter_values<F>(&mut self, filter: F)
    where
        F: Filter<V>;
}

#[cfg(feature = "std")]
impl<T> ListFilterExt<T> for ::std::vec::Vec<T> {
    #[inline]
    fn filter<F>(&mut self, filter: F)
    where
        F: Filter<T>,
    {
        self.retain(
            #[inline]
            |value| filter.test(value),
        );
    }
}

#[cfg(feature = "std")]
impl<T> ListFilterExt<T> for ::std::collections::VecDeque<T> {
    #[inline]
    fn filter<F>(&mut self, filter: F)
    where
        F: Filter<T>,
    {
        self.retain(
            #[inline]
            |value| filter.test(value),
        );
    }
}

#[cfg(feature = "std")]
impl<T, S> ListFilterExt<T> for ::std::collections::HashSet<T, S>
where
    S: ::std::hash::BuildHasher,
{
    #[inline]
    fn filter<F>(&mut self, filter: F)
    where
        F: Filter<T>,
    {
        self.retain(
            #[inline]
            |value| filter.test(value),
        );
    }
}

#[cfg(feature = "std")]
impl<T> ListFilterExt<T> for ::std::collections::BTreeSet<T>
where
    T: Ord,
{
    #[inline]
    fn filter<F>(&mut self, filter: F)
    where
        F: Filter<T>,
    {
        self.retain(
            #[inline]
            |value| filter.test(value),
        );
    }
}

#[cfg(feature = "std")]
impl<T> ListFilterExt<T> for ::std::collections::BinaryHeap<T>
where
    T: Ord,
{
    #[inline]
    fn filter<F>(&mut self, filter: F)
    where
        F: Filter<T>,
    {
        self.retain(
            #[inline]
            |value| filter.test(value),
        );
    }
}

#[cfg(feature = "std")]
impl<K, V, S> MapFilterExt<K, V> for ::std::collections::HashMap<K, V, S>
where
    S: ::std::hash::BuildHasher,
{
    #[inline]
    fn filter_keys<F>(&mut self, filter: F)
    where
        F: Filter<K>,
    {
        self.retain(
            #[inline]
            |key, _| filter.test(key),
        );
    }

    #[inline]
    fn filter_values<F>(&mut self, filter: F)
    where
        F: Filter<V>,
    {
        self.retain(
            #[inline]
            |_, value| filter.test(value),
        );
    }
}

#[cfg(feature = "std")]
impl<K, V> MapFilterExt<K, V> for ::std::collections::BTreeMap<K, V>
where
    K: Ord,
{
    #[inline]
    fn filter_keys<F>(&mut self, filter: F)
    where
        F: Filter<K>,
    {
        self.retain(
            #[inline]
            |key, _| filter.test(key),
        );
    }

    #[inline]
    fn filter_values<F>(&mut self, filter: F)
    where
        F: Filter<V>,
    {
        self.retain(
            #[inline]
            |_, value| filter.test(value),
        );
    }
}
