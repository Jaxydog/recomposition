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

//! A small library that adds additional chain-able iterator-like types.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "filtering")]
pub mod filter;
#[cfg(feature = "sorting")]
pub mod sort;
