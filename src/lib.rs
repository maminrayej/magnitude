#[derive(Debug, Copy, Clone)]
pub enum Magnitude<T> {
    Finite(T),
    PosInfinit,
    NegInfinit,
}

// implement comparison operators for Beyond
use std::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};

impl<T: PartialEq> PartialEq for Magnitude<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Magnitude::Finite(value1), Magnitude::Finite(value2)) => value1.eq(value2),

            (Magnitude::Finite(_), Magnitude::PosInfinit)
            | (Magnitude::Finite(_), Magnitude::NegInfinit)
            | (Magnitude::PosInfinit, Magnitude::Finite(_))
            | (Magnitude::PosInfinit, Magnitude::NegInfinit)
            | (Magnitude::NegInfinit, Magnitude::Finite(_))
            | (Magnitude::NegInfinit, Magnitude::PosInfinit) => false,

            (Magnitude::PosInfinit, Magnitude::PosInfinit) => {
                panic!("Can not compare two positive infinities")
            }

            (Magnitude::NegInfinit, Magnitude::NegInfinit) => {
                panic!("Can not compare two negative infinities")
            }
        }
    }
}

impl<T: PartialEq> Eq for Magnitude<T> {}

impl<T: PartialOrd> PartialOrd for Magnitude<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Magnitude::Finite(value1), Magnitude::Finite(value2)) => value1.partial_cmp(value2),

            (Magnitude::Finite(_), Magnitude::NegInfinit) => Some(Ordering::Greater),
            (Magnitude::PosInfinit, Magnitude::Finite(_)) => Some(Ordering::Greater),
            (Magnitude::PosInfinit, Magnitude::NegInfinit) => Some(Ordering::Greater),

            (Magnitude::Finite(_), Magnitude::PosInfinit) => Some(Ordering::Less),
            (Magnitude::NegInfinit, Magnitude::Finite(_)) => Some(Ordering::Less),
            (Magnitude::NegInfinit, Magnitude::PosInfinit) => Some(Ordering::Less),

            (Magnitude::PosInfinit, Magnitude::PosInfinit) => {
                panic!("Can not compare two positive infinities")
            }
            (Magnitude::NegInfinit, Magnitude::NegInfinit) => {
                panic!("Can not compare two negative infinities")
            }
        }
    }
}

impl<T: Ord> Ord for Magnitude<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

// implement arithmetic operators for Beyond
use std::ops::{Add, Div, Mul, Neg, Sub};

impl<T: Add<Output = T>> Add for Magnitude<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Magnitude::Finite(value1), Magnitude::Finite(value2)) => {
                Magnitude::Finite(value1 + value2)
            }

            (Magnitude::Finite(_), Magnitude::PosInfinit) => Magnitude::PosInfinit,
            (Magnitude::PosInfinit, Magnitude::Finite(_)) => Magnitude::PosInfinit,
            (Magnitude::PosInfinit, Magnitude::PosInfinit) => Magnitude::PosInfinit,

            (Magnitude::Finite(_), Magnitude::NegInfinit) => Magnitude::NegInfinit,
            (Magnitude::NegInfinit, Magnitude::Finite(_)) => Magnitude::NegInfinit,
            (Magnitude::NegInfinit, Magnitude::NegInfinit) => Magnitude::NegInfinit,

            (Magnitude::PosInfinit, Magnitude::NegInfinit)
            | (Magnitude::NegInfinit, Magnitude::PosInfinit) => {
                panic!("Can not add PosInfinit and NegInfinit")
            }
        }
    }
}

impl<T: Sub<Output = T>> Sub for Magnitude<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Magnitude::Finite(value1), Magnitude::Finite(value2)) => {
                Magnitude::Finite(value1 - value2)
            }

            (Magnitude::Finite(_), Magnitude::NegInfinit) => Magnitude::PosInfinit,
            (Magnitude::PosInfinit, Magnitude::Finite(_)) => Magnitude::PosInfinit,
            (Magnitude::PosInfinit, Magnitude::NegInfinit) => Magnitude::PosInfinit,

            (Magnitude::Finite(_), Magnitude::PosInfinit) => Magnitude::NegInfinit,
            (Magnitude::NegInfinit, Magnitude::Finite(_)) => Magnitude::NegInfinit,
            (Magnitude::NegInfinit, Magnitude::PosInfinit) => Magnitude::NegInfinit,

            (Magnitude::PosInfinit, Magnitude::PosInfinit) => {
                panic!("Can not subtract two PosInfinities")
            }
            (Magnitude::NegInfinit, Magnitude::NegInfinit) => {
                panic!("Can not subtract two NegInfinities")
            }
        }
    }
}

use num_traits::identities::Zero;
impl<T: Mul<Output = T> + PartialOrd + Zero> Mul for Magnitude<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Magnitude::Finite(value1), Magnitude::Finite(value2)) => {
                Magnitude::Finite(value1 * value2)
            }

            (Magnitude::PosInfinit, Magnitude::Finite(value))
            | (Magnitude::Finite(value), Magnitude::PosInfinit) => {
                if value < T::zero() {
                    Magnitude::NegInfinit
                } else if value > T::zero() {
                    Magnitude::PosInfinit
                } else {
                    panic!("Can not multiply zero by Infinity");
                }
            }

            (Magnitude::NegInfinit, Magnitude::Finite(value))
            | (Magnitude::Finite(value), Magnitude::NegInfinit) => {
                if value < T::zero() {
                    Magnitude::PosInfinit
                } else if value > T::zero() {
                    Magnitude::NegInfinit
                } else {
                    panic!("Can not multiply zero by Infinity");
                }
            }

            (Magnitude::PosInfinit, Magnitude::PosInfinit) => Magnitude::PosInfinit,
            (Magnitude::PosInfinit, Magnitude::NegInfinit) => Magnitude::NegInfinit,
            (Magnitude::NegInfinit, Magnitude::PosInfinit) => Magnitude::NegInfinit,
            (Magnitude::NegInfinit, Magnitude::NegInfinit) => Magnitude::PosInfinit,
        }
    }
}

impl<T: Div<Output = T> + PartialOrd + Zero> Div for Magnitude<T> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Magnitude::Finite(value1), Magnitude::Finite(value2)) => {
                Magnitude::Finite(value1 / value2)
            }

            (Magnitude::Finite(value), Magnitude::PosInfinit) => {
                if value < T::zero() {
                    Magnitude::NegInfinit
                } else if value > T::zero() {
                    Magnitude::PosInfinit
                } else {
                    Magnitude::Finite(T::zero())
                }
            }

            (Magnitude::PosInfinit, Magnitude::Finite(value)) => {
                if value < T::zero() {
                    Magnitude::NegInfinit
                } else if value > T::zero() {
                    Magnitude::PosInfinit
                } else {
                    panic!("Division by zero");
                }
            }

            (Magnitude::Finite(value), Magnitude::NegInfinit) => {
                if value < T::zero() {
                    Magnitude::PosInfinit
                } else if value > T::zero() {
                    Magnitude::NegInfinit
                } else {
                    Magnitude::Finite(T::zero())
                }
            }

            (Magnitude::NegInfinit, Magnitude::Finite(value)) => {
                if value < T::zero() {
                    Magnitude::PosInfinit
                } else if value > T::zero() {
                    Magnitude::NegInfinit
                } else {
                    panic!("Division by zero");
                }
            }

            (Magnitude::PosInfinit, Magnitude::PosInfinit)
            | (Magnitude::PosInfinit, Magnitude::NegInfinit)
            | (Magnitude::NegInfinit, Magnitude::PosInfinit)
            | (Magnitude::NegInfinit, Magnitude::NegInfinit) => {
                panic!("Can not divide two infinities")
            }
        }
    }
}

impl<T: Neg<Output = T>> Neg for Magnitude<T> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Magnitude::Finite(value) => Magnitude::Finite(-value),
            Magnitude::PosInfinit => Magnitude::NegInfinit,
            Magnitude::NegInfinit => Magnitude::PosInfinit,
        }
    }
}

// implement auxilary operators
use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

impl<T: Add<Output = T> + Clone> AddAssign for Magnitude<T> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<T: Sub<Output = T> + Clone> SubAssign for Magnitude<T> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<T: Mul<Output = T> + Clone + PartialOrd + Zero> MulAssign for Magnitude<T> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<T: Div<Output = T> + Clone + PartialOrd + Zero> DivAssign for Magnitude<T> {
    fn div_assign(&mut self, rhs: Self) {
        *self = self.clone() / rhs;
    }
}
