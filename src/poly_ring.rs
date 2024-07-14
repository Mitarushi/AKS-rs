use std::cell::RefCell;
use std::cmp::{max, min};
use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};

use rug::integer::Order;
use rug::Integer;

use overload_macros::{overload, overload_eq, overload_unary};

use crate::modint::DivError;
use crate::poly::Poly;
use crate::poly_elem_trait::{PolyElem, PolyElemRing};

pub trait FastPolyDivTrait<'a, T: PolyElem<'a>>: Debug + Clone {
    fn rem(&mut self, x: &Poly<'a, T>) -> Poly<'a, T>;
}

#[derive(Clone, Debug)]
pub struct NormalPolyDiv<'a, T: PolyElem<'a>> {
    b_deg: usize,
    m_len: usize,
    inv: Poly<'a, T>,
    modulo: Poly<'a, T>,
}

impl<'a, T: PolyElem<'a>> NormalPolyDiv<'a, T> {
    pub fn new(modulo: Poly<'a, T>) -> Self {
        let m_len = modulo.deg() as usize;
        let b_deg = m_len + 1;
        let b = Poly::x_power_of(modulo.ring, b_deg);
        let inv = (&b / &modulo).unwrap();
        NormalPolyDiv {
            b_deg,
            m_len,
            inv,
            modulo,
        }
    }

    fn double_inv(&mut self) {
        let b: Poly<T> = Poly::x_power_of(self.modulo.ring, self.b_deg);
        let inv = &self.inv * (&b * 2 - (&self.inv * &self.modulo));
        let inv = inv >> self.m_len;
        let b_deg_next = self.b_deg * 2 - self.m_len;
        self.inv = inv;
        self.b_deg = b_deg_next;
    }

    fn double_until(&mut self, n: usize) {
        while self.b_deg < n {
            self.double_inv();
        }
    }

    pub fn div(&mut self, x: &Poly<'a, T>) -> Poly<'a, T> {
        let x_deg = max(x.deg(), 0) as usize;
        self.double_until(x_deg);
        let inv = &self.inv >> (self.b_deg - x_deg);

        let pre_shift = min(x_deg, self.m_len - 1);
        let post_shift = x_deg - pre_shift;
        (&inv * (x >> pre_shift)) >> post_shift
    }

    pub fn rem_(&mut self, x: &Poly<'a, T>) -> Poly<'a, T> {
        let q = self.div(x);
        x - &q * &self.modulo
    }
}

impl<'a, T: PolyElem<'a>> FastPolyDivTrait<'a, T> for NormalPolyDiv<'a, T> {
    fn rem(&mut self, x: &Poly<'a, T>) -> Poly<'a, T> {
        self.rem_(x)
    }
}

// Poly for x^n - a
#[derive(Clone, Debug)]
pub struct NearMonomialDiv<T> {
    pub n: usize,
    pub a: T,
}

impl<'a, T: PolyElem<'a>> NearMonomialDiv<T> {
    pub fn new(n: usize, a: T) -> Self {
        NearMonomialDiv { n, a }
    }

    pub fn rem_(&self, x: &Poly<'a, T>) -> Poly<'a, T> {
        let mut r_coef = x.coef.clone();
        for i in (self.n..r_coef.len()).rev() {
            let j = i - self.n;
            r_coef[j] = &r_coef[j] + &r_coef[i] * &self.a;
        }
        r_coef.truncate(self.n);
        Poly::reduce(&mut r_coef);
        Poly::new(r_coef, x.ring)
    }
}

impl<'a, T: PolyElem<'a>> FastPolyDivTrait<'a, T> for NearMonomialDiv<T> {
    fn rem(&mut self, x: &Poly<'a, T>) -> Poly<'a, T> {
        self.rem_(x)
    }
}

#[derive(Clone, Debug)]
pub struct NaivePolyDiv<'a, T: PolyElem<'a>> {
    modulo: Poly<'a, T>,
}

impl<'a, T: PolyElem<'a>> NaivePolyDiv<'a, T> {
    pub fn new(modulo: Poly<'a, T>) -> Self {
        NaivePolyDiv { modulo }
    }
}

impl<'a, T: PolyElem<'a>> FastPolyDivTrait<'a, T> for NaivePolyDiv<'a, T> {
    fn rem(&mut self, x: &Poly<'a, T>) -> Poly<'a, T> {
        (x % &self.modulo).unwrap()
    }
}

#[derive(Clone, Debug)]
pub struct ModPolyRing<'a, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>> {
    pub modulo: Poly<'a, T>,
    fast_div: RefCell<U>,
}

#[derive(Clone, Debug)]
pub struct ModPoly<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>> {
    pub value: Poly<'a, T>,
    pub ring: &'b ModPolyRing<'a, T, U>,
}

impl<'a, T: PolyElem<'a>> ModPolyRing<'a, T, NormalPolyDiv<'a, T>> {
    pub fn new(modulo: Poly<'a, T>) -> Self {
        let fast_div = NormalPolyDiv::new(modulo.clone());
        ModPolyRing {
            modulo,
            fast_div: RefCell::new(fast_div),
        }
    }
}

impl<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>> ModPolyRing<'a, T, U> {
    pub fn from_fast_div(modulo: Poly<'a, T>, fast_div: U) -> ModPolyRing<'a, T, U> {
        ModPolyRing {
            modulo,
            fast_div: RefCell::new(fast_div),
        }
    }

    pub fn from(&'b self, value: Poly<'a, T>) -> ModPoly<'a, 'b, T, U> {
        self.from_bounded(self.fast_div.borrow_mut().rem(&value))
    }

    pub fn from_bounded(&'b self, value: Poly<'a, T>) -> ModPoly<'a, 'b, T, U> {
        ModPoly { value, ring: self }
    }

    pub fn add(
        &'b self,
        a: &ModPoly<'a, 'b, T, U>,
        b: &ModPoly<'a, 'b, T, U>,
    ) -> ModPoly<'a, 'b, T, U> {
        self.from_bounded(&a.value + &b.value)
    }

    pub fn sub(
        &'b self,
        a: &ModPoly<'a, 'b, T, U>,
        b: &ModPoly<'a, 'b, T, U>,
    ) -> ModPoly<'a, 'b, T, U> {
        self.from_bounded(&a.value - &b.value)
    }

    pub fn mul(
        &'b self,
        a: &ModPoly<'a, 'b, T, U>,
        b: &ModPoly<'a, 'b, T, U>,
    ) -> ModPoly<'a, 'b, T, U> {
        let r = &a.value * &b.value;
        let r = self.fast_div.borrow_mut().rem(&r);
        self.from_bounded(r)
    }

    pub fn neg(&'b self, a: &ModPoly<'a, 'b, T, U>) -> ModPoly<'a, 'b, T, U> {
        self.from_bounded(-&a.value)
    }
}

impl<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>> ModPoly<'a, 'b, T, U> {
    fn add_(&self, other: &ModPoly<'a, 'b, T, U>) -> ModPoly<'a, 'b, T, U> {
        self.ring.add(self, other)
    }

    fn add_i64(&self, other: &i64) -> ModPoly<'a, 'b, T, U> {
        ModPoly {
            value: &self.value + other,
            ring: self.ring,
        }
    }

    fn sub_(&self, other: &ModPoly<'a, 'b, T, U>) -> ModPoly<'a, 'b, T, U> {
        self.ring.sub(self, other)
    }

    fn sub_i64(&self, other: &i64) -> ModPoly<'a, 'b, T, U> {
        ModPoly {
            value: &self.value - other,
            ring: self.ring,
        }
    }

    fn mul_(&self, other: &ModPoly<'a, 'b, T, U>) -> ModPoly<'a, 'b, T, U> {
        self.ring.mul(self, other)
    }

    fn mul_i64(&self, other: &i64) -> ModPoly<'a, 'b, T, U> {
        ModPoly {
            value: &self.value * other,
            ring: self.ring,
        }
    }

    fn neg_(&self) -> ModPoly<'a, 'b, T, U> {
        self.ring.neg(self)
    }

    fn eq_(&self, other: &ModPoly<'a, 'b, T, U>) -> bool {
        self.value == other.value
    }

    pub fn pow(&self, n: &Integer) -> ModPoly<'a, 'b, T, U> {
        let mut y = self.ring.from_bounded(Poly::one(self.value.ring));
        let n_bits = n.to_digits::<bool>(Order::Lsf);

        for i in n_bits.into_iter().rev() {
            y = &y * &y;
            if i {
                y = &y * self;
            }
        }
        y
    }
}

overload!(<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>>, Add, ModPoly<'a, 'b, T, U>, add, add_);
overload!(<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>>, Add, ModPoly<'a, 'b, T, U>, i64, add, add_i64);
overload!(<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>>, Sub, ModPoly<'a, 'b, T, U>, sub, sub_);
overload!(<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>>, Sub, ModPoly<'a, 'b, T, U>, i64, sub, sub_i64);
overload!(<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>>, Mul, ModPoly<'a, 'b, T, U>, mul, mul_);
overload!(<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>>, Mul, ModPoly<'a, 'b, T, U>, i64, mul, mul_i64);
overload_unary!(<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>>, Neg, ModPoly<'a, 'b, T, U>, neg, neg_);
overload_eq!(<'a, 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>>, PartialEq, ModPoly<'a, 'b, T, U>, eq, eq_);

impl<'b, 'a: 'b, T: PolyElem<'a> + 'b, U: FastPolyDivTrait<'a, T> + 'b> PolyElemRing<'b>
    for ModPolyRing<'a, T, U>
{
    type Elem = ModPoly<'a, 'b, T, U>;

    fn zero(&'b self) -> Self::Elem {
        self.from_bounded(Poly::zero(self.modulo.ring))
    }

    fn one(&'b self) -> Self::Elem {
        self.from_bounded(Poly::one(self.modulo.ring))
    }

    fn from_i64(&'b self, x: i64) -> Self::Elem {
        self.from_bounded(Poly::from_int_vec(vec![Integer::from(x)], self.modulo.ring))
    }

    fn from_integer(&'b self, x: Integer) -> Self::Elem {
        self.from_bounded(Poly::from_int_vec(vec![x], self.modulo.ring))
    }

    fn poly_mul_required_words(&self, len: usize) -> usize {
        let self_len = self.modulo.len() * 2 - 1;
        let elem_len = len * self_len;
        self.modulo.ring.poly_mul_required_words(elem_len) * self_len
    }
}

impl<'b, 'a: 'b, T: PolyElem<'a>, U: FastPolyDivTrait<'a, T>> PolyElem<'b>
    for ModPoly<'a, 'b, T, U>
{
    type Ring = ModPolyRing<'a, T, U>;

    fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    fn write_digits(&self, digits: &mut [u64], min_len: usize) {
        let self_len = self.ring.modulo.len() * 2 - 1;
        let elem_min_len = min_len * self_len;
        let elem_size = self.ring.poly_mul_required_words(elem_min_len);

        for (i, x) in self.value.coef.iter().enumerate() {
            let from_pos = elem_size * i;
            let to_pos = elem_size * (i + 1);
            x.write_digits(&mut digits[from_pos..to_pos], elem_min_len);
        }
    }

    fn from_digits(ring: &'b Self::Ring, digits: &[u64], min_len: usize) -> Self {
        let self_len = ring.modulo.len() * 2 - 1;
        let elem_min_len = min_len * self_len;
        let elem_size = ring.poly_mul_required_words(elem_min_len);

        let value_coef = (0..self_len)
            .map(|i| {
                let from_pos = elem_size * i;
                let to_pos = elem_size * (i + 1);
                T::from_digits(ring.modulo.ring, &digits[from_pos..to_pos], elem_min_len)
            })
            .collect();
        let value = Poly::new(value_coef, ring.modulo.ring);

        ring.from(value)
    }

    fn inv(&self) -> Result<Self, DivError> {
        if self == &self.ring.one() {
            Ok(self.ring.one())
        } else {
            Err(DivError::Error)
        }
    }
}

#[cfg(test)]
mod tests {
    use rug::Integer;

    use crate::modint::{ModInt, ModRing};

    use super::*;

    #[test]
    fn test_mod_poly() {
        let mut rng = rug::rand::RandState::new();
        let mut random_int = || Integer::from(Integer::random_bits(128, &mut rng));

        for _ in 0..10 {
            let n = random_int();
            let n = n.next_prime();
            let n_ring = ModRing::new(n.clone());

            let mut modulo_coef = (0..128).map(|_| random_int()).collect::<Vec<_>>();
            modulo_coef.push(Integer::from(1));
            let modulo = Poly::<ModInt>::from_int_vec(modulo_coef, &n_ring);
            let ring = ModPolyRing::new(modulo.clone());

            let a = random_int();
            let x_a = Poly::from_int_vec(vec![a.clone(), Integer::from(1)], &n_ring);
            let x_a = ring.from(x_a);
            let x_a_pow = x_a.pow(&n);

            let x = Poly::one(&n_ring) << 1;
            let x = ring.from(x);
            let x_pow = x.pow(&n);
            let x_pow_a = &x_pow + &ring.from_bounded(Poly::from_int_vec(vec![a.clone()], &n_ring));

            assert_eq!(x_a_pow.value, x_pow_a.value);
        }
    }
}
