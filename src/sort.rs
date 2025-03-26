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

//! Implements composable sorters.

use core::cmp::Ordering;

/// A value that acts as a sorter for a given type.
pub trait Sort<T: ?Sized>: Sized {
    /// Compares the given values, returning the relative ordering of the left-most value as compared to the right-most
    /// value.
    ///
    /// The output of this function must be deterministic to allow for proper collection sorting.
    fn compare(&self, lhs: &T, rhs: &T) -> Ordering;

    /// Returns a new [`Sort`] implementation that reverses the result of this implementation.
    #[inline]
    fn reverse(self) -> Reverse<Self> {
        Reverse { sorter: self }
    }

    /// Sorts using this [`Sort`] implementation, then applies the second if the values are equal.
    #[inline]
    fn then<S>(self, other: S) -> Then<Self, S> {
        Then { sorter_a: self, sorter_b: other }
    }

    /// Applies a mapping function to each value before sorting.
    #[inline]
    fn map_owned<U, F>(self, f: F) -> MapOwned<Self, F>
    where
        F: Fn(&T) -> U,
    {
        MapOwned { function: f, sorter: self }
    }

    /// Applies a mapping function to each value before sorting.
    ///
    /// The mapped values are expected to be borrowed from the input value.
    #[inline]
    fn map_borrowed<U, F>(self, f: F) -> MapBorrowed<Self, F>
    where
        U: ?Sized,
        F: for<'a> Fn(&'a T) -> &'a U,
    {
        MapBorrowed { function: f, sorter: self }
    }
}

/// Sorts values based on their [`Ord`] implementation.
#[derive(Clone, Debug)]
pub struct Order;

impl<T> Sort<T> for Order
where
    T: ?Sized + Ord,
{
    #[inline]
    fn compare(&self, lhs: &T, rhs: &T) -> Ordering {
        lhs.cmp(rhs)
    }
}

/// Reverses the stored [`Sort`] implementation.
#[derive(Clone, Debug)]
pub struct Reverse<S> {
    /// The inner sorter.
    sorter: S,
}

impl<T, S> Sort<T> for Reverse<S>
where
    T: ?Sized,
    S: Sort<T>,
{
    #[inline]
    fn compare(&self, lhs: &T, rhs: &T) -> Ordering {
        self.sorter.compare(lhs, rhs).reverse()
    }
}

/// Sorts using the first [`Sort`] implementation, then applies the second if the values are equal.
#[derive(Clone, Debug)]
pub struct Then<A, B> {
    /// The first inner sorter.
    sorter_a: A,
    /// The second inner sorter.
    sorter_b: B,
}

impl<T, A, B> Sort<T> for Then<A, B>
where
    T: ?Sized,
    A: Sort<T>,
    B: Sort<T>,
{
    #[inline]
    fn compare(&self, lhs: &T, rhs: &T) -> Ordering {
        self.sorter_a.compare(lhs, rhs).then_with(
            #[inline]
            || self.sorter_b.compare(lhs, rhs),
        )
    }
}

/// Applies the inner mapping function to each value before sorting.
#[derive(Clone, Debug)]
pub struct MapOwned<S, F> {
    /// The inner mapping function.
    function: F,
    /// The inner sorter.
    sorter: S,
}

impl<T, U, S, F> Sort<T> for MapOwned<S, F>
where
    T: ?Sized,
    S: Sort<U>,
    F: Fn(&T) -> U,
{
    #[inline]
    fn compare(&self, lhs: &T, rhs: &T) -> Ordering {
        self.sorter.compare(&(self.function)(lhs), &(self.function)(rhs))
    }
}

/// Applies the inner mapping function to each value before sorting.
///
/// The mapped values are expected to be borrowed from the input value.
#[derive(Clone, Debug)]
pub struct MapBorrowed<S, F> {
    /// The inner mapping function.
    function: F,
    /// The inner sorter.
    sorter: S,
}

impl<T, U, S, F> Sort<T> for MapBorrowed<S, F>
where
    T: ?Sized,
    U: ?Sized,
    S: Sort<U>,
    F: for<'a> Fn(&'a T) -> &'a U,
{
    #[inline]
    fn compare(&self, lhs: &T, rhs: &T) -> Ordering {
        self.sorter.compare((self.function)(lhs), (self.function)(rhs))
    }
}

/// Uses the given function as a [`Sort`] implementation.
#[derive(Clone, Debug)]
pub struct FromFn<F> {
    /// The sorting function.
    function: F,
}

impl<T, F> Sort<T> for FromFn<F>
where
    T: ?Sized,
    F: Fn(&T, &T) -> Ordering,
{
    fn compare(&self, lhs: &T, rhs: &T) -> Ordering {
        (self.function)(lhs, rhs)
    }
}

/// Creates a [`Sort`] implementation using the given function.
///
/// The output of this function must be deterministic to allow for proper collection sorting.
#[inline]
pub const fn from_fn<T, F>(f: F) -> FromFn<F>
where
    T: ?Sized,
    F: Fn(&T, &T) -> Ordering,
{
    FromFn { function: f }
}

/// Extends a list so that it may be sorted easily.
pub trait ListSortExt<T> {
    /// Returns `true` if this slice is sorted according to the given [`Sort`] implementation.
    fn is_sorted_with<S>(&self, sorter: S) -> bool
    where
        S: Sort<T>;

    /// Sorts this slice using the given [`Sort`] implementation.
    #[cfg(feature = "std")]
    fn sort_with<S>(&mut self, sorter: S)
    where
        S: Sort<T>;

    /// Sorts this slice using the given [`Sort`] implementation without preserving the order of equal elements.
    fn sort_unstable_with<S>(&mut self, sorter: S)
    where
        S: Sort<T>;
}

impl<T> ListSortExt<T> for [T] {
    #[inline]
    fn is_sorted_with<S>(&self, sorter: S) -> bool
    where
        S: Sort<T>,
    {
        self.is_sorted_by(
            #[inline]
            |lhs, rhs| sorter.compare(lhs, rhs).is_le(),
        )
    }

    #[cfg(feature = "std")]
    #[inline]
    fn sort_with<S>(&mut self, sorter: S)
    where
        S: Sort<T>,
    {
        self.sort_by(
            #[inline]
            |lhs, rhs| sorter.compare(lhs, rhs),
        );
    }

    #[inline]
    fn sort_unstable_with<S>(&mut self, sorter: S)
    where
        S: Sort<T>,
    {
        self.sort_unstable_by(
            #[inline]
            |lhs, rhs| sorter.compare(lhs, rhs),
        );
    }
}
