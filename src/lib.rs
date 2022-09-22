// This file is part of the laron-primitives.
//
// Copyright (C) 2022 Ade M Ramdani
//
// SPDX-License-Identifier: GPL-3.0-or-later
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.
//!
//! unprim contains primitive types from 8 into 256 bit.
//! it is unstable and not intended for production use.
//!
//! ```rust
//! use laron_primitives::*;
//!
//! let a = U256::from(100);
//! let b = U256::from(2);
//!
//! assert_eq!(a * b, 200u64.into());
//! ```
//! Or you can use `.into()` method to init the types.
//!
//! ```rust
//! use laron_primitives::*;
//!
//! let a: U24 = 100u64.into();
//! let b: U24 = 2u64.into();
//! let c: u32 = (a * b).into();
//!
//! assert_eq!(c, 200);
//! ```
//!
//! You can use macro to define new types. In example if you want to
//! define a type with 512 bit, you can use the macro.
//! ```rust
//!
//! use laron_primitives::*;
//!
//! define!(U512, 64, "512 bit");
//!
//! let a = U512::from(100);
//! let b = U512::from(2);
//! let c = a * b;
//! assert_eq!(c, 200u64.into());
pub use std::{
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    str::FromStr,
};

pub use serde::{Deserialize, Serialize};

#[macro_use]
pub mod macros;

pub fn mul8(x: u8, y: u8) -> (u8, u8) {
    let z = x as u16 * y as u16;
    ((z >> 8) as u8, z as u8)
}

pub fn mul_r(z: u8, x: u8, y: u8) -> (u8, u8) {
    let (hi, lo) = mul8(x, y);
    let (lo, c) = lo.overflowing_add(z);
    let (hi, _) = hi.overflowing_add(c as u8);
    (hi, lo)
}

pub fn mul_carry(z: u8, x: u8, y: u8, carry: u8) -> (u8, u8) {
    let (hi, lo) = mul8(x, y);
    let (lo, c) = lo.overflowing_add(carry);
    let (hi, _) = hi.overflowing_add(c as u8);
    let (lo, c) = lo.overflowing_add(z);
    let (hi, _) = hi.overflowing_add(c as u8);
    (hi, lo)
}

/// Computes 16-bit division of two 8-bit numbers and return the quotient and remainder.
pub fn div8(hi: u8, lo: u8, y: u8) -> (u8, u8) {
    if y != 0 && y <= hi {
        panic!("forbidden");
    }

    let z = (hi as u16) << 8 | lo as u16;
    ((z / y as u16) as u8, (z % y as u16) as u8)
}

/// Computes <!d, !0> / d.
pub fn reciprocal_2by1(d: u8) -> u8 {
    let (reciprocal, _) = div8(!d, !0u8, d);
    reciprocal
}

/// Devides <uh, ul> / d, returns the quotient and remainder.
/// It use provided d's reciprocal.
/// Implementation is ported from https://github.com/holiman/uint250.
pub fn div_rem_2by1(uh: u8, ul: u8, d: u8, reciprocal: u8) -> (u8, u8) {
    let (qh, ql) = mul8(reciprocal, uh);
    let (ql, carry) = ql.overflowing_add(ul);
    let (mut qh, _) = qh.overflowing_add(uh);
    qh = qh.overflowing_add(carry as u8 + 1).0;

    let (mut r, _) = ul.overflowing_sub((qh as u16 * d as u16) as u8);

    if r > ql {
        qh = qh.overflowing_sub(1).0;
        r = r.overflowing_add(d).0;
    }

    if r >= d {
        qh = qh.overflowing_add(1).0;
        r = r.overflowing_sub(d).0;
    }

    (qh, r)
}

/// Computes x -= y * multiplier.
/// requires: len(x) >= len(y).
pub fn sub_mul(nx: &[u8], y: &[u8], multiplier: u8) -> (Vec<u8>, u8) {
    let mut x = vec![0u8; nx.len()];
    x.copy_from_slice(nx);
    let mut borrow = 0u8;

    for i in 0..y.len() {
        let (s, carry1) = x[i].overflowing_sub(borrow);
        let (ph, pl) = mul8(y[i], multiplier);
        let (t, carry2) = s.overflowing_sub(pl);
        x[i] = t;
        borrow = ph + carry1 as u8 + carry2 as u8;
    }

    (x, borrow)
}

/// Computes x += y where x and y is a slice.
/// requires: len(x) >= len(y).
pub fn add_slice(x: &[u8], y: &[u8]) -> (Vec<u8>, u8) {
    let mut x = vec![0u8; x.len()];
    let mut carry = false;
    for i in 0..y.len() {
        (x[i], carry) = x[i].overflowing_add(y[i] + carry as u8);
    }
    (x, carry as u8)
}

define!(
    U24,
    3,
    "24-bit unsigned integer represented as little-endian byte order."
);

define!(
    U40,
    5,
    "40-bit unsigned integer represented as little-endian byte order."
);

define!(
    U48,
    6,
    "48-bit unsigned integer represented as little-endian byte order."
);

define!(
    U56,
    7,
    "56-bit unsigned integer represented as little-endian byte order."
);

define!(
    U72,
    9,
    "72-bit unsigned integer represented as little-endian byte order."
);

define!(
    U80,
    10,
    "80-bit unsigned integer represented as little-endian byte order."
);

define!(
    U88,
    11,
    "88-bit unsigned integer represented as little-endian byte order."
);

define!(
    U96,
    12,
    "96-bit unsigned integer represented as little-endian byte order."
);

define!(
    U104,
    13,
    "104-bit unsigned integer represented as little-endian byte order."
);

define!(
    U112,
    14,
    "112-bit unsigned integer represented as little-endian byte order."
);

define!(
    U120,
    15,
    "120-bit unsigned integer represented as little-endian byte order."
);

define!(
    U136,
    17,
    "136-bit unsigned integer represented as little-endian byte order."
);

define!(
    U144,
    18,
    "144-bit unsigned integer represented as little-endian byte order."
);

define!(
    U152,
    19,
    "152-bit unsigned integer represented as little-endian byte order."
);

define!(
    U160,
    20,
    "160-bit unsigned integer represented as little-endian byte order."
);

define!(
    U168,
    21,
    "168-bit unsigned integer represented as little-endian byte order."
);

define!(
    U176,
    22,
    "176-bit unsigned integer represented as little-endian byte order."
);

define!(
    U184,
    23,
    "184-bit unsigned integer represented as little-endian byte order."
);

define!(
    U192,
    24,
    "192-bit unsigned integer represented as little-endian byte order."
);

define!(
    U200,
    25,
    "200-bit unsigned integer represented as little-endian byte order."
);

define!(
    U208,
    26,
    "208-bit unsigned integer represented as little-endian byte order."
);

define!(
    U216,
    27,
    "216-bit unsigned integer represented as little-endian byte order."
);

define!(
    U224,
    28,
    "224-bit unsigned integer represented as little-endian byte order."
);

define!(
    U232,
    29,
    "232-bit unsigned integer represented as little-endian byte order."
);

define!(
    U240,
    30,
    "240-bit unsigned integer represented as little-endian byte order."
);

define!(
    U248,
    31,
    "248-bit unsigned integer represented as little-endian byte order."
);

define!(
    U256,
    32,
    "256-bit unsigned integer represented as little-endian byte order."
);

#[cfg(test)]
mod test_primitives {
    use super::*;

    #[test]
    fn test_macro() {
        define!(
            U8,
            1,
            "8-bit unsigned integer represented as little-endian byte order."
        );

        let x: U8 = 200u8.into();
        assert_eq!(200u8, x.into());
    }
}
