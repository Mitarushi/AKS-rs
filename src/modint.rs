use std::cell::RefCell;
use std::fmt::{Debug, Display};
use std::ops::{Add, Mul, Neg, Sub};

use rug::{Assign, Integer};
use rug::integer::Order;

use overload_macros::{overload, overload_eq, overload_unary};

use crate::poly_elem_trait::{PolyElem, PolyElemRing};

#[derive(Debug, Clone)]
struct FastDiv {
    b_log: u32,
    m_len: u32,
    inv: Integer,
    modulo: Integer,
}

impl FastDiv {
    pub fn new(modulo: Integer) -> Self {
        let m_len = modulo.significant_bits();
        let b_log = m_len + 1;
        let b = Integer::from(1) << b_log;
        let inv = b / &modulo;
        FastDiv {
            b_log,
            m_len,
            inv,
            modulo,
        }
    }

    fn double_inv(&mut self) {
        let b = Integer::from(1) << self.b_log;
        let inv = &self.inv * (2 * b - &self.inv * &self.modulo);
        let mut inv = inv >> self.m_len;

        let b_log_next = self.b_log * 2 - self.m_len;
        let b_next = Integer::from(1) << b_log_next;
        let r = b_next - &inv * &self.modulo;
        if r >= self.modulo {
            inv += 1;
        }

        self.inv = inv;
        self.b_log = b_log_next;
    }

    fn double_until(&mut self, n: u32) {
        while self.b_log < n {
            self.double_inv();
        }
    }

    fn approx_div(&mut self, x: &Integer) -> Integer {
        let x_len = x.significant_bits();
        self.double_until(x_len);
        let inv = Integer::from(&self.inv >> (self.b_log - x_len));
        let q = inv * x >> x_len;
        q
    }

    pub fn rem(&mut self, x: &Integer) -> Integer {
        let q = self.approx_div(x);
        let r = x - q * &self.modulo;
        if r >= self.modulo {
            r - &self.modulo
        } else {
            r
        }
    }
}

#[derive(Clone, Debug)]
pub struct ModRing {
    pub modulo: Integer,
    fast_div: RefCell<FastDiv>,
}

#[derive(Clone)]
pub struct ModInt<'a> {
    pub value: Integer,
    pub ring: &'a ModRing,
}

pub enum DivState<T> {
    Error,
    Result(T),
    DivisorFound(Integer),
}

impl<T> DivState<T> {
    pub fn unwrap(self) -> T {
        match self {
            DivState::Result(x) => x,
            _ => panic!("DivState::unwrap()"),
        }
    }
}

impl ModRing {
    pub fn new(modulo: Integer) -> Self {
        let fast_div = FastDiv::new(modulo.clone());
        ModRing {
            modulo,
            fast_div: RefCell::new(fast_div),
        }
    }

    pub fn from(&self, value: Integer) -> ModInt {
        self.from_bounded(self.fast_div.borrow_mut().rem(&value))
    }

    pub fn from_bounded(&self, value: Integer) -> ModInt {
        ModInt {
            value,
            ring: self,
        }
    }

    pub fn from_i64(&self, value: i64) -> ModInt {
        self.from(Integer::from(value))
    }

    pub fn add(&self, a: &ModInt, b: &ModInt) -> ModInt {
        let r = Integer::from(&a.value + &b.value);
        let value = if r >= self.modulo { r - &self.modulo } else { r };
        self.from_bounded(value)
    }

    pub fn sub(&self, a: &ModInt, b: &ModInt) -> ModInt {
        let r = Integer::from(&a.value - &b.value);
        let value = if r < 0 { r + &self.modulo } else { r };
        self.from_bounded(value)
    }

    pub fn mul(&self, a: &ModInt, b: &ModInt) -> ModInt {
        let r = Integer::from(&a.value * &b.value);
        let r = self.fast_div.borrow_mut().rem(&r);
        self.from_bounded(r)
    }

    pub fn neg(&self, a: &ModInt) -> ModInt {
        let value = if a.value.is_zero() {
            Integer::from(0)
        } else {
            Integer::from(&self.modulo - &a.value)
        };
        self.from_bounded(value)
    }

    pub fn zero(&self) -> ModInt {
        self.from_bounded(Integer::from(0))
    }

    pub fn one(&self) -> ModInt {
        self.from_bounded(Integer::from(1))
    }
}

fn significant_bits(x: u64) -> u32 {
    64 - x.leading_zeros()
}

impl<'a> PolyElemRing<'a> for ModRing {
    type Elem = ModInt<'a>;

    fn zero(&'a self) -> Self::Elem {
        self.zero()
    }

    fn one(&'a self) -> Self::Elem {
        self.one()
    }

    fn from_i64(&'a self, x: i64) -> Self::Elem {
        self.from_i64(x)
    }

    fn mul_required_bits(&self, len: usize) -> u32 {
        self.modulo.significant_bits() * 2 + significant_bits(len as u64)
    }
}


impl<'a> ModInt<'a> {
    fn add_(&self, other: &ModInt<'a>) -> ModInt<'a> {
        self.ring.add(self, other)
    }

    fn add_i64(&self, other: &i64) -> ModInt<'a> {
        self.add_(&self.ring.from_i64(*other))
    }

    fn sub_(&self, other: &ModInt<'a>) -> ModInt<'a> {
        self.ring.sub(self, other)
    }

    fn sub_i64(&self, other: &i64) -> ModInt<'a> {
        self.sub_(&self.ring.from_i64(*other))
    }

    fn mul_(&self, other: &ModInt<'a>) -> ModInt<'a> {
        self.ring.mul(self, other)
    }

    fn mul_i64(&self, other: &i64) -> ModInt<'a> {
        self.mul_(&self.ring.from_i64(*other))
    }

    fn neg_(&self) -> ModInt<'a> {
        self.ring.neg(self)
    }

    fn eq_(&self, other: &ModInt<'a>) -> bool {
        self.value == other.value
    }

    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    pub fn inv(&self) -> DivState<ModInt<'a>> {
        let a = &self.value;
        let b = &self.ring.modulo;
        let mut g = Integer::new();
        let mut x = Integer::new();
        (&mut g, &mut x).assign(a.extended_gcd_ref(b));

        if &g == b {
            DivState::Error
        } else if g == 1 {
            DivState::Result(self.ring.from_bounded(x))
        } else {
            DivState::DivisorFound(g)
        }
    }
}

impl<'a> PolyElem<'a> for ModInt<'a> {
    type Ring = ModRing;

    fn is_zero(&self) -> bool {
        self.is_zero()
    }

    fn write_digits(&self, digits: &mut [u64]) {
        self.value.write_digits(digits, Order::LsfLe);
    }

    fn from_digits(ring: &'a Self::Ring, digits: &[u64]) -> ModInt<'a> {
        let mut value = Integer::new();
        value.assign_digits(digits, Order::LsfLe);
        ring.from(value)
    }

    fn inv(&self) -> DivState<ModInt<'a>> {
        self.inv()
    }
}

overload!(<'a>, Add, ModInt<'a>, add, add_);
overload!(<'a>, Add, ModInt<'a>, i64, add, add_i64);
overload!(<'a>, Sub, ModInt<'a>, sub, sub_);
overload!(<'a>, Sub, ModInt<'a>, i64, sub, sub_i64);
overload!(<'a>, Mul, ModInt<'a>, mul, mul_);
overload!(<'a>, Mul, ModInt<'a>, i64, mul, mul_i64);
overload_unary!(<'a>, Neg, ModInt<'a>, neg, neg_);
overload_eq!(<'a>, PartialEq, ModInt<'a>, eq, eq_);

impl<'a> Display for ModInt<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl<'a> Debug for ModInt<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[cfg(test)]
mod tests {
    use rug::{Complete, rand};

    use super::*;

    #[test]
    fn test_modint() {
        let mut rng = rand::RandState::new();
        let mut gen_random = || -> Integer {
            Integer::from(Integer::random_bits(128, &mut rng))
        };

        for _ in 0..100 {
            let modulo = gen_random();
            let a = gen_random();
            let b = gen_random();

            let ring = ModRing::new(modulo.clone());
            let a_mod = ring.from(a.clone());
            let b_mod = ring.from(b.clone());

            let c = &a_mod + &b_mod;
            assert_eq!(c.value, (&a + &b).complete() % &modulo);

            let c = &a_mod - &b_mod;
            assert_eq!(c.value, ((&a - &b).complete() % &modulo + &modulo) % &modulo);

            let c = &a_mod * &b_mod;
            assert_eq!(c.value, (&a * &b).complete() % &modulo);
        }
    }
}
