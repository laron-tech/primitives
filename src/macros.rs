// This file is part of the primitives.
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

#[macro_export]
macro_rules! bit_size {
    ($t:ty) => {{
        use std::mem::size_of;
        (size_of::<$t>() * 8) as u32
    }};
}

#[macro_export]
macro_rules! doc {
    ($x:expr, $s:expr, $($t:tt)*) => {
        #[doc = $x]
        #[doc = concat!("```", "\nuse primitives::*;\n\n", "let x: ", stringify!($s), " = 100u8.into();", "\n", "assert_eq!(100u8, x.into());\n\n", "```")]
        #[derive(Clone, Copy)]
        $($t)*
    };
}

#[macro_export]
macro_rules! byte_size {
    ($t:ty) => {{
        use std::mem::size_of;
        size_of::<$t>() as usize
    }};
}

#[macro_export]
macro_rules! impl_serde {
    ($S:ident) => {
        impl Serialize for $S {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                let s = self.to_str_radix(16);
                serializer.serialize_str(&format!("0x{}", &s))
            }
        }
        impl<'de> Deserialize<'de> for $S {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                let s = String::deserialize(deserializer)?;
                <$S>::from_str(&s).map_err(serde::de::Error::custom)
            }
        }
    };
}

#[macro_export]
macro_rules! impl_stringr {
    ($S:ident) => {
        impl $S {
            fn to_radix_digits_le(v: &$S, radix: u32) -> Vec<u8> {
                assert!((2..=36).contains(&radix));

                let mut res = Vec::new();
                let mut digits = v.clone();

                while digits > Self::zero() {
                    let q = digits / Self::from(radix);
                    let r = digits % Self::from(radix);
                    res.push(r.into());
                    digits = q;
                }
                res
            }

            fn from_radix_digits_be(digits: &[u8], radix: u32) -> $S {
                assert!((2..=36).contains(&radix));

                let mut res = <$S>::zero();
                let mut power = <$S>::one();
                for digit in digits.iter().rev() {
                    let digit = *digit as u8;
                    if digit >= radix as u8 {
                        return <$S>::zero();
                    }
                    res += power * digit.into();
                    power *= radix.into();
                }
                res
            }

            /// convert this type into radix string.
            pub fn to_str_radix(&self, radix: u32) -> String {
                assert!((2..=36).contains(&radix));

                if self.is_zero() {
                    return "0".to_string();
                }

                let mut res = Self::to_radix_digits_le(self, radix);

                for r in &mut res {
                    if *r < 10 {
                        *r += b'0';
                    } else {
                        *r += b'a' - 10;
                    }
                }

                res.reverse();

                unsafe { String::from_utf8_unchecked(res) }
            }

            /// Convert string into this type by given radix.
            pub fn from_str_radix(s: &str, radix: u32) -> Result<Self, String> {
                let mut s = s;

                if s.starts_with('+') {
                    let tail = &s[1..];
                    if tail.starts_with('+') {
                        s = tail;
                    }
                }

                if s.is_empty() {
                    return Err("empty string".to_string());
                }

                if s.starts_with('_') {
                    return Err("leading underscore".to_string());
                }

                let mut v = Vec::with_capacity(s.len());

                for b in s.bytes() {
                    let d = match b {
                        b'0'..=b'9' => b - b'0',
                        b'a'..=b'z' => b - b'a' + 10,
                        b'A'..=b'Z' => b - b'A' + 10,
                        b'_' => continue,
                        _ => return Err("invalid character".to_string()),
                    };

                    if d < radix as u8 {
                        v.push(d);
                    } else {
                        return Err("invalid digit".to_string());
                    }
                }

                Ok(Self::from_radix_digits_be(&v, radix))
            }
        }
    };
}

#[macro_export]
macro_rules! impl_def_trait {
    ($S:ident) => {
        impl Eq for $S {}

        impl PartialEq for $S {
            fn eq(&self, other: &Self) -> bool {
                self.data == other.data
            }
        }

        impl Ord for $S {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                let x = self.clone();
                let y = other.clone();
                let (z, c) = x.overflowing_sub(y);

                if c {
                    std::cmp::Ordering::Less
                } else if z.is_zero() {
                    std::cmp::Ordering::Equal
                } else {
                    std::cmp::Ordering::Greater
                }
            }

            fn clamp(self, min: Self, max: Self) -> Self
            where
                Self: Sized,
            {
                if self < min {
                    min
                } else if self > max {
                    max
                } else {
                    self
                }
            }
        }

        impl PartialOrd for $S {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Default for $S {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl std::fmt::Display for $S {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.pad_integral(true, "", &self.to_str_radix(10))
            }
        }

        impl std::fmt::Debug for $S {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(self, f)
            }
        }

        impl std::fmt::Binary for $S {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.pad_integral(true, "", &self.to_str_radix(2))
            }
        }

        impl std::fmt::Octal for $S {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.pad_integral(true, "", &self.to_str_radix(8))
            }
        }

        impl FromStr for $S {
            type Err = String;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                if s.is_empty() {
                    return Err("Empty string".to_string());
                }

                #[allow(unused_mut)]
                let mut res: Result<Self, String>;

                // check if the string has a leading 0x
                if s.starts_with("0x") {
                    res = Self::from_str_radix(s.strip_prefix("0x").unwrap(), 16);
                } else if s.starts_with("0b") {
                    res = Self::from_str_radix(s.strip_prefix("0b").unwrap(), 2);
                } else if s.starts_with("0o") {
                    res = Self::from_str_radix(s.strip_prefix("0o").unwrap(), 8);
                } else {
                    res = Self::from_str_radix(s, 10);
                }

                match res {
                    Ok(v) => Ok(v),
                    Err(e) => Err(e),
                }
            }
        }
    };
}

#[macro_export]
macro_rules! define {
    ($S:ident, $size:expr, $doc:expr) => {
        doc!(
            $doc,
            $S,
            pub struct $S {
                data: [u8; $size],
            }
        );

        from_prim!($S, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

        impl_def_trait!($S);

        impl_stringr!($S);

        impl_serde!($S);

        impl $S {
            /// Bytes size of this type.
            pub const SIZE: usize = $size;

            /// Bit size of this type.
            pub const BITS: u32 = bit_size!($S);

            /// Minimum value of this type.
            pub const MIN: $S = $S { data: [0; $size] };

            /// Maximum value of this type.
            pub const MAX: $S = $S { data: [255; $size] };

            /// Return zero representation of this types.
            pub fn zero() -> Self {
                let data = [0; Self::SIZE];
                Self { data }
            }

            /// Return one representation of this types.
            pub fn one() -> Self {
                let mut data = [0; Self::SIZE];
                data[0] = 1;
                Self { data }
            }

            /// Return true if this is zero.
            pub fn is_zero(&self) -> bool {
                self.data.iter().all(|&x| x == 0)
            }

            /// Return true if this is one.
            pub fn is_one(&self) -> bool {
                self.data[0] == 1 && self.data.iter().all(|&x| x == 0)
            }

            /// Create this type from little endian bytes.
            pub fn from_le_bytes(bytes: [u8; $size]) -> Self {
                let mut data = [0; Self::SIZE];
                for i in 0..data.len() {
                    if i < bytes.len() {
                        data[i] = bytes[i];
                    } else {
                        data[i] = 0;
                    }
                }
                Self { data }
            }

            /// Create this type from big endian bytes.
            pub fn from_be_bytes(bytes: [u8; $size]) -> Self {
                let mut data = [0; Self::SIZE];
                for i in 0..data.len() {
                    if i < bytes.len() {
                        data[i] = bytes[i];
                    } else {
                        data[i] = 0;
                    }
                }
                data.reverse();
                Self { data }
            }

            /// Return the little endian representation of this type.
            pub fn to_le_bytes(&self) -> [u8; $size] {
                self.data
            }

            /// Return the big endian representation of this type.
            pub fn to_be_bytes(&self) -> [u8; $size] {
                let mut data = self.data;
                data.reverse();
                data
            }

            /// Convert this type to little endian.
            pub fn to_le(&self) -> Self {
                self.clone()
            }

            /// Convert this type to big endian.
            pub fn to_be(&self) -> Self {
                Self {
                    data: self.to_be_bytes(),
                }
            }

            /// Return count of leading zeros.
            pub fn leading_zeros(&self) -> u32 {
                let mut data = self.data;
                data.reverse();
                let mut zeros = 0;
                for i in 0..Self::SIZE {
                    let z = data[i].leading_zeros();
                    zeros += z;
                    if z != 8 {
                        break;
                    }
                }
                zeros
            }

            /// Return count of trailing zeros.
            pub fn trailing_zeros(&self) -> u32 {
                let data = self.data;
                let mut zeros = 0;
                for i in 0..Self::SIZE {
                    let z = data[i].trailing_zeros();
                    zeros += z;
                    if z != 8 {
                        break;
                    }
                }
                zeros
            }

            /// Return count of leading ones.
            pub fn leading_ones(&self) -> u32 {
                let mut data = self.data;
                data.reverse();
                let mut ones = 0;
                for i in 0..Self::SIZE {
                    let o = data[i].leading_ones();
                    ones += o;
                    if o != 8 {
                        break;
                    }
                }
                ones
            }

            /// Return count of trailing ones.
            pub fn trailing_ones(&self) -> u32 {
                let data = self.data;
                let mut ones = 0;
                for i in 0..Self::SIZE {
                    let o = data[i].trailing_ones();
                    ones += o;
                    if o != 8 {
                        break;
                    }
                }
                ones
            }

            impl_maths!($size);

            impl_shift!();
        }

        impl_math_ops!($S);
        impl_bit_ops!($S);
    };
}

#[macro_export]
macro_rules! from_prim {
    ($S:ident, $( $T:ty ),*) => {
        $(
            impl From<$T> for $S {
                fn from(x: $T) -> Self {
                    let mut data = [0; Self::SIZE];
                    let bytes = x.to_le_bytes();
                    for i in 0..data.len() {
                        if i < bytes.len() {
                            data[i] = bytes[i];
                        } else {
                            break;
                        }
                    }
                    Self { data }
                }
            }

            impl From<$S> for $T {
                fn from(x: $S) -> Self {
                    let mut bytes = [0; byte_size!($T)];
                    let data = x.data;
                    for i in 0..bytes.len() {
                        if i < data.len() {
                            bytes[i] = data[i];
                        } else {
                            break;
                        }
                    }
                    <$T>::from_le_bytes(bytes)
                }
            }
        )*
    };
}

#[macro_export]
macro_rules! impl_maths {
    ($size:expr) => {
        /// Add two number and return the sum along with the carry.
        pub fn overflowing_add(&self, other: Self) -> (Self, bool) {
            let x = self.data;
            let y = other.data;

            let mut carry = 0;
            let mut sum = [0; Self::SIZE];

            for i in 0..x.len() {
                let (s, c) = x[i].overflowing_add(y[i]);
                let (s, c2) = s.overflowing_add(carry);
                sum[i] = s;
                carry = c as u8 + c2 as u8;
            }

            (Self { data: sum }, carry != 0)
        }

        /// Subtract two number and return the sum along with the borrow.
        pub fn overflowing_sub(&self, other: Self) -> (Self, bool) {
            let x = self.data;
            let y = other.data;

            let mut br = 0;
            let mut sum = [0; Self::SIZE];

            for i in 0..x.len() {
                let (s, b) = x[i].overflowing_sub(y[i]);
                let (s, b2) = s.overflowing_sub(br);
                sum[i] = s;
                br = b as u8 + b2 as u8;
            }

            (Self { data: sum }, br != 0)
        }

        /// Return product of two number after multiplication and bool indicating overflow.
        pub fn overflowing_mul(&self, other: Self) -> (Self, bool) {
            let x = self.data;
            let y = other.data;

            let mut res = [0; Self::SIZE * 2];
            let mut resid = 0;
            let mut temp: Vec<u8> = Vec::new();
            let mut tempid = 0;
            let mut carry = 0;
            let mut c: Vec<u8> = Vec::new();

            if y.len() == 1 && x.len() == 1 {
                let (c, r) = mul8(x[0], y[0]);
                let mut data = [0; Self::SIZE];
                data[0] = r;
                return (Self { data }, c != 0);
            }

            for i in 0..y.len() {
                for j in 0..x.len() {
                    if i == 0 && j == 0 {
                        let (cr, r) = mul8(x[j], y[i]);
                        res[resid] = r;
                        resid += 1;
                        carry = cr;
                        continue;
                    }

                    if i == 0 {
                        if j == (x.len() - 1) {
                            let (cc, rr) = mul_r(carry, x[j], y[i]);
                            c.push(cc);
                            temp.push(rr);
                            carry = 0;
                            continue;
                        }

                        let (cr, rr) = mul_r(carry, x[j], y[i]);
                        carry = cr;
                        temp.push(rr);
                        continue;
                    }

                    if i != y.len() - 1 {
                        if j == 0 {
                            let (cr, r) = mul_r(temp[0], x[j], y[i]);
                            res[resid] = r;
                            resid += 1;
                            carry = cr;
                            temp.remove(0);
                            continue;
                        } else if j == x.len() - 1 {
                            let (cc, rr) = mul_carry(c[0], x[j], y[i], carry);
                            c[0] = cc;
                            temp.push(rr);
                            tempid = 0;
                            carry = 0;
                            continue;
                        } else {
                            let (cr, rr) = mul_carry(temp[tempid], x[j], y[i], carry);
                            temp[tempid] = rr;
                            carry = cr;
                            tempid += 1;
                            continue;
                        }
                    }

                    if j == 0 {
                        let (cr, r) = mul_r(temp[0], x[j], y[i]);
                        res[resid] = r;
                        carry = cr;
                        resid += 1;
                        temp.remove(0);
                        continue;
                    } else if j != x.len() - 1 {
                        let (cr, r) = mul_carry(temp[0], x[j], y[i], carry);
                        res[resid] = r;
                        carry = cr;
                        resid += 1;
                        temp.remove(0);
                        continue;
                    } else {
                        let (a, b) = mul_carry(c[0], x[j], y[i], carry);
                        res[resid] = a;
                        resid += 1;
                        res[resid] = b;
                        carry = 0;
                        continue;
                    }
                }
            }

            let mut data = [0; Self::SIZE];
            data.copy_from_slice(&res[..Self::SIZE]);
            let mut ov = [0; Self::SIZE];
            ov.copy_from_slice(&res[Self::SIZE..]);

            let prod2 = Self { data: ov };

            (Self { data }, !prod2.is_zero())
        }

        /// Devides u by single normalized word d and produces both quotient and remainder.
        fn div_rem_by1(u: &[u8], d: u8) -> ([u8; $size], u8) {
            let reciprocal = reciprocal_2by1(d);
            let mut q = [0u8; Self::SIZE];
            let mut r = u[u.len() - 1];

            for i in (0..u.len() - 1).rev() {
                (q[i], r) = div_rem_2by1(r, u[i], d, reciprocal);
            }

            (q, r)
        }

        /// Implement division of u by multiple normalized words d from the Knuth's algorithm.
        fn div_rem_knuth(u: &[u8], d: &[u8]) -> ([u8; $size], [u8; $size]) {
            let mut q = [0u8; Self::SIZE];
            let dh = d[d.len() - 1];
            let dl = d[d.len() - 2];
            let reciprocal = reciprocal_2by1(dh);
            let mut u = u.to_vec();

            for j in (0..u.len() - d.len()).rev() {
                let u2 = u[j + d.len()];
                let u1 = u[j + d.len() - 1];
                let u0 = u[j + d.len() - 2];

                #[allow(unused_mut)]
                let (mut qhat, mut rhat);

                if u2 >= dh {
                    qhat = !0u8;
                } else {
                    (qhat, rhat) = div_rem_2by1(u2, u1, dh, reciprocal);
                    let (ph, pl) = mul8(qhat, dl);
                    if ph > rhat || (ph == rhat && pl > u0) {
                        qhat -= 1;
                    }
                }

                let (nu, borrow) = sub_mul(&u[j..], d, qhat);
                u[j..].copy_from_slice(&nu);
                u[j + d.len()] = u2.overflowing_sub(borrow).0;

                if u2 < borrow {
                    qhat -= 1;
                    let (nu, carry) = add_slice(&u[j..], d);
                    u[j..].copy_from_slice(&nu);
                    u[j + d.len()] = carry;
                }

                q[j] = qhat;
            }

            let mut rem = [0u8; Self::SIZE];
            for i in 0..d.len() {
                rem[i] = u[i];
            }
            (q, rem)
        }

        /// Divide two numbers and return tuple of the quotient and remainder.
        pub fn div_rem(&self, rhs: Self) -> (Self, Self) {
            let mut q = [0u8; Self::SIZE];
            let mut r = [0u8; Self::SIZE];

            // If the divisor is zero, return the dividend.
            if rhs.is_zero() {
                return (self.clone(), Self::zero());
            }

            let (u, d) = (self.data, rhs.data);

            let mut dlen = 0usize;

            for i in (0..d.len()).rev() {
                if d[i] != 0 {
                    dlen = i + 1;
                    break;
                }
            }

            let shift = d[dlen - 1].leading_zeros();

            let dnstorage = [0u8; Self::SIZE];
            let mut dn = dnstorage[..dlen].to_vec();

            for i in (1..dlen).rev() {
                dn[i] = ((d[i] as u16) << shift) as u8 | ((d[i - 1] as u16) >> (8 - shift)) as u8;
            }
            dn[0] = ((d[0] as u16) << shift) as u8;

            let mut ulen = 0usize;

            for i in (0..u.len()).rev() {
                if u[i] != 0 {
                    ulen = i + 1;
                    break;
                }
            }

            if ulen < dlen {
                r.copy_from_slice(&u);
                return (Self { data: q }, Self { data: r });
            }

            let unstorage = [0u8; Self::SIZE + 1];
            let mut un = unstorage[..ulen + 1].to_vec();
            un[ulen] = ((u[ulen - 1] as u16) >> (8 - shift)) as u8;

            for i in (1..ulen).rev() {
                un[i] = ((u[i] as u16) << shift) as u8 | ((u[i - 1] as u16) >> (8 - shift)) as u8;
            }
            un[0] = ((u[0] as u16) << shift) as u8;

            if dlen == 1 {
                let (qt, rt) = Self::div_rem_by1(&un, dn[0]);
                r[0] = ((rt as u16) >> shift) as u8;
                q = qt;

                return (Self { data: q }, Self { data: r });
            }

            let (un, q) = Self::div_rem_knuth(&un, &dn);

            for i in 0..d.len() - 1 {
                r[i] = ((un[i] as u16) >> shift) as u8
                    | ((un[i + 1] as u16) << (8 - shift) as u8) as u8;
            }

            r[dlen - 1] = ((un[dlen - 1] as u16) >> shift) as u8;

            return (Self { data: q }, Self { data: r });
        }
    };
}

#[macro_export]
macro_rules! impl_shift {
    () => {
        /// Shift left and return the result along with boolean indicating overflow.
        pub fn overflowing_shl(&self, n: u32) -> (Self, bool) {
            if n == 0 {
                return (self.clone(), false);
            }

            if n >= Self::BITS {
                let mut shift = n;
                while shift >= Self::BITS {
                    shift -= Self::BITS;
                }
                return (self.overflowing_shl(shift).0, true);
            }

            let mut x = self.data;
            x.reverse();

            let mut data = [0u8; Self::SIZE];

            for i in 0..x.len() {
                if n == 8 {
                    if i != x.len() - 1 {
                        data[i] = x[i + 1];
                    }
                    continue;
                }

                if n % 8 == 0 {
                    let q = (n / 8) as usize;
                    if i + q <= x.len() - 1 {
                        data[i] = x[i + q];
                        continue;
                    }
                }

                if n < 8 {
                    data[i] = x[i] << n;
                    if i < x.len() - 1 {
                        data[i] |= x[i + 1] >> (8 - n);
                    }
                    continue;
                }

                if n > 8 {
                    let q = (n / 8) as usize;
                    if i + q <= x.len() - 1 {
                        data[i] = x[i + q] << (n % 8);
                        if i + 1 + q <= x.len() - 1 {
                            data[i] |= x[i + 1 + q] >> (8 - (n % 8));
                        }
                        continue;
                    }
                }
            }

            data.reverse();

            (Self { data }, false)
        }

        /// Shift right and return the result along with boolean indicating overflow.
        pub fn overflowing_shr(&self, n: u32) -> (Self, bool) {
            if n == 0 {
                return (self.clone(), false);
            }

            if n >= Self::BITS {
                let mut shift = n;
                while shift >= Self::BITS {
                    shift -= Self::BITS;
                }
                return (self.overflowing_shl(shift).0, true);
            }

            let x = self.data;
            let mut data = [0u8; Self::SIZE];

            for i in 0..x.len() {
                if n == 8 {
                    if i != x.len() - 1 {
                        data[i] = x[i + 1];
                    }
                    continue;
                }

                if n % 8 == 0 {
                    let q = (n / 8) as usize;
                    if i + q <= x.len() - 1 {
                        data[i] = x[i + q];
                        continue;
                    }
                }

                if n < 8 {
                    data[i] = x[i] >> n;
                    if i < x.len() - 1 {
                        data[i] |= x[i + 1] << (8 - n);
                    }
                    continue;
                }

                if n > 8 {
                    let q = (n / 8) as usize;
                    if i + q <= x.len() - 1 {
                        data[i] = x[i + q] >> (n % 8);
                        if i + 1 + q <= x.len() - 1 {
                            data[i] |= x[i + 1 + q] << (8 - (n % 8));
                        }
                        continue;
                    }
                }
            }

            (Self { data }, false)
        }
    };
}

#[macro_export]
macro_rules! impl_math_ops {
    ($( $S:ident ),*) => {
        $(
            impl Add for $S {
                type Output = $S;

                fn add(self, other: $S) -> $S {
                    let (sum, carry) = self.overflowing_add(other);
                    if carry {
                        panic!("attempt to add with overflow");
                    }
                    sum
                }
            }

            impl AddAssign for $S {
                fn add_assign(&mut self, other: $S) {
                    *self = *self + other;
                }
            }

            impl Sub for $S {
                type Output = $S;

                fn sub(self, other: $S) -> $S {
                    let (sum, borrow) = self.overflowing_sub(other);
                    if borrow {
                        panic!("attempt to subtract with underflow");
                    }
                    sum
                }
            }

            impl SubAssign for $S {
                fn sub_assign(&mut self, other: $S) {
                    *self = *self - other;
                }
            }

            impl Mul for $S {
                type Output = $S;

                fn mul(self, other: $S) -> $S {
                    let (prod, carry) = self.overflowing_mul(other);

                    if carry {
                        panic!("attempt to multiply with upperflow");
                    }
                    prod
                }
            }

            impl MulAssign for $S {
                fn mul_assign(&mut self, other: $S) {
                    *self = *self * other;
                }
            }

            impl Div for $S {
                type Output = $S;

                fn div(self, other: $S) -> $S {
                    self.div_rem(other).0
                }
            }

            impl DivAssign for $S {
                fn div_assign(&mut self, other: $S) {
                    *self = *self / other;
                }
            }

            impl Rem for $S {
                type Output = $S;

                fn rem(self, other: $S) -> Self {
                    self.div_rem(other).1
                }
            }

            impl RemAssign for $S {
                fn rem_assign(&mut self, other: $S) {
                    *self = *self % other;
                }
            }
        )*
    };
}

#[macro_export]
macro_rules! impl_bit_ops {
    ($($S:ident),*) => {
        $(
            impl BitAnd for $S {
                type Output = $S;

                fn bitand(self, rhs: Self) -> Self::Output {
                    let x = self.data;
                    let y = rhs.data;
                    let mut data = [0; Self::SIZE];

                    for i in 0..x.len() {
                        data[i] = x[i] & y[i];
                    }

                    Self { data }
                }
            }

            impl BitAndAssign for $S {
                fn bitand_assign(&mut self, rhs: Self) {
                    *self = *self & rhs;
                }
            }

            impl BitOr for $S {
                type Output = $S;

                fn bitor(self, rhs: Self) -> Self::Output {
                    let x = self.data;
                    let y = rhs.data;
                    let mut data = [0; Self::SIZE];

                    for i in 0..x.len() {
                        data[i] = x[i] | y[i];
                    }

                    Self { data }
                }
            }

            impl BitOrAssign for $S {
                fn bitor_assign(&mut self, rhs: Self) {
                    *self = *self | rhs;
                }
            }

            impl BitXor for $S {
                type Output = $S;

                fn bitxor(self, rhs: Self) -> Self::Output {
                    let x = self.data;
                    let y = rhs.data;
                    let mut data = [0; Self::SIZE];

                    for i in 0..x.len() {
                        data[i] = x[i] ^ y[i];
                    }

                    Self { data }
                }
            }

            impl BitXorAssign for $S {
                fn bitxor_assign(&mut self, rhs: Self) {
                    *self = *self ^ rhs;
                }
            }

            impl Not for $S {
                type Output = $S;

                fn not(self) -> Self::Output {
                    let mut data = self.data;
                    for i in 0..data.len() {
                        data[i] = !data[i];
                    }
                    Self { data }
                }
            }

            impl Shl<u32> for $S {
                type Output = $S;

                fn shl(self, n: u32) -> Self::Output {
                    let (x, ov) = self.overflowing_shl(n);
                    if ov {
                        panic!("attemp to shift left with overflow.")
                    }
                    x
                }
            }

            impl ShlAssign<u32> for $S {
                fn shl_assign(&mut self, n: u32) {
                    *self = *self << n;
                }
            }

            impl Shr<u32> for $S {
                type Output = $S;

                fn shr(self, n: u32) -> Self::Output {
                    let (x, ov) = self.overflowing_shr(n);
                    if ov {
                        panic!("attemp to shift right with overflow.")
                    }
                    x
                }
            }

            impl ShrAssign<u32> for $S {
                fn shr_assign(&mut self, n: u32) {
                    *self = *self >> n;
                }
            }
        )*
    };
}
