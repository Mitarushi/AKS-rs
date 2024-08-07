use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};

use rug::Integer;

use crate::modint::DivError;

pub trait Ops<Rhs = Self, Output = Self>:
    Sized
    + Add<Rhs, Output = Output>
    + Sub<Rhs, Output = Output>
    + Mul<Rhs, Output = Output>
    + Neg<Output = Output>
{
}

impl<T, Rhs, Output> Ops<Rhs, Output> for T where
    T: Sized
        + Add<Rhs, Output = Output>
        + Sub<Rhs, Output = Output>
        + Mul<Rhs, Output = Output>
        + Neg<Output = Output>
{
}

pub trait RefOps<Rhs = Self, Output = Self> = Ops<Rhs, Output> + for<'a> Ops<&'a Rhs, Output>
where
    for<'a> &'a Self: Ops<Rhs, Output> + Ops<&'a Rhs, Output>;

pub trait PolyElemRing<'a>: Debug + Clone {
    type Elem: PolyElem<'a, Ring = Self>;
    fn zero(&'a self) -> Self::Elem;

    fn one(&'a self) -> Self::Elem;

    fn from_i64(&'a self, x: i64) -> Self::Elem;

    fn from_integer(&'a self, x: Integer) -> Self::Elem;

    fn poly_mul_required_words(&self, len: usize) -> usize;
}

pub trait PolyElem<'a>: RefOps + RefOps<i64> + Debug + Clone + PartialEq {
    type Ring: PolyElemRing<'a, Elem = Self>;

    fn is_zero(&self) -> bool;

    fn write_digits(&self, digits: &mut [u64], min_len: usize);

    fn from_digits(ring: &'a Self::Ring, digits: &[u64], min_len: usize) -> Self;

    fn inv(&self) -> Result<Self, DivError>;
}
