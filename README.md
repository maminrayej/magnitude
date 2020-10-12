
![](assets/Magnitude.png)
<a href="https://www.freepik.com/vectors/logo">Logo by www.freepik.com</a>

Magnitude - To infinity and beyond!
==========================================================
[![Crate](https://img.shields.io/crates/v/magnitude.svg)](https://crates.io/crates/magnitude)
[![API](https://docs.rs/magnitude/badge.svg)](https://docs.rs/magnitude) \
This crate is useful when you need to work with algorithms like
[Dijkstra's Shortest Path](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm#Pseudocode) or
[Floyd–Warshall algorithm](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm#Algorithm)
that require infinite values in order to be written elegantly.

 One simple example can be finding the max value in a vector:
 ```rust
 use magnitude::Magnitude;

 fn find_max(vec: &Vec<Magnitude<i32>>) -> Magnitude<i32> {
     let mut max = Magnitude::NegInfinite;
     for val in vec {
         if *val > max {
             max = *val;
         }
     }

     max
 }

 let vec: Vec<Magnitude<i32>> = vec![2.into(), 3.into(), 6.into(), (-10).into()];
 assert_eq!(find_max(&vec), 6.into());
 ````
 You can do all **valid** comparison(==, !=, >, <, >=, <=) and arithmetic(+,-, *, /, +=, -=, *=, /=) operations on magnitudes. \
 Invalid operations are listed below which means any other operation is valid.

 # Invalid operations
 * Comparison:
    - two `PosInfinite`
    - two `NegInfinite`
 * Arithmetic:
     - Add:
         - `PosInfinite` + `NegInfinite`
     - Sub:
         - `PosInfinite` - `PosInfinite`
         - `NegInfinite` - `NegInfinite`
     - Mul:
         - zero * `PosInfinite`
         - zero * `NegInfinite`
     - Div:
         - non-zero / `PosInfinite`
         - non-zero / `NegInfinite`
         - `PosInfinite` / zero
         - `NegInfinite` / zero
         - `PosInfinite` / `PosInfinite`
         - `PosInfinite` / `NegInfinite`
         - `NegInfinite` / `PosInfinite`
         - `NegInfinite` / `NegInfinite`

# Relationship of Magnitude with `f64` and `f32` infinities
Magnitude as of 0.2.0 treat `f64::INFINITY`, `f64::NEG_INFINITY`, `f32::INFINITY`, `f32::NEG_INFINITY` as infinites:
```rust
use magnitude::Magnitude;

let pos_inf: Magnitude<f64> = f64::INFINITY.into();
let neg_inf: Magnitude<f64> = f64::NEG_INFINITY.into();
assert!(pos_inf.is_pos_infinite());
assert!(neg_inf.is_neg_infinite());

let pos_inf: Magnitude<f32> = f32::INFINITY.into();
let neg_inf: Magnitude<f32> = f32::NEG_INFINITY.into();
assert!(pos_inf.is_pos_infinite());
assert!(neg_inf.is_neg_infinite());
```

# Release
* 0.2.0: handle `f64::INFINITY`, `f64::NEG_INFINITY`, `f32::INFINITY`, `f32::NEG_INFINITY` properly \
special thanks to [@niklasmohrin](https://github.com/niklasmohrin) and [@smarnach](https://github.com/smarnach)