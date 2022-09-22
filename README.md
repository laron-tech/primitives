# PRIMITIVES
![build](https://github.com/laron-tech/primitives/actions/workflows/rust.yml/badge.svg)
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
![crates.io](https://img.shields.io/crates/v/laron-primitives.svg)

Ethereum primitives type for rust.

This crate was **unstable** and maybe lot's of bugs and I suggest not to use this.

## Usage
```toml
[dependencies]
laron_primitives = "0.1"
```

```rust
use laron_primitives::*;

let x: U256 = 100u128.into();
let y: U256 = 2u128.into();
let z = x * y;

assert_eq!(200u64, z.into());
```

## Macro
To create new type, you can use macro `define!`.
```rust
use laron_primitives::*;

define!(U512, 64, "512-bits custom type.");

let x: U512 = 100u8.into();

assert_eq!(x * 2u8.into(), 200u8.into());

```

## TODO
- Add Pow/Exp method for each types.
- Add SQRT method for each types.
