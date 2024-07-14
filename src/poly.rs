use std::cmp::{max, min};
use std::ops::{Add, Div, Index, IndexMut, Mul, Neg, Rem, Shl, Shr, Sub};

use rug::Integer;

use overload_macros::{overload, overload_eq, overload_unary};

use crate::modint::DivError;
use crate::poly_elem_trait::{PolyElem, PolyElemRing};

#[derive(Clone, Debug)]
pub struct Poly<'a, T: PolyElem<'a>> {
    pub coef: Vec<T>,
    pub ring: &'a T::Ring,
}

impl<'a, T: PolyElem<'a>> Poly<'a, T> {
    pub fn new(coef: Vec<T>, ring: &'a T::Ring) -> Poly<'a, T> {
        Poly { coef, ring }
    }

    pub fn len(&self) -> usize {
        self.coef.len()
    }

    pub fn deg(&self) -> isize {
        self.coef.len() as isize - 1
    }

    pub fn reduce(coef: &mut Vec<T>) {
        while !coef.is_empty() && coef.last().unwrap().is_zero() {
            coef.pop();
        }
    }

    fn add_(&self, other: &Poly<'a, T>) -> Poly<'a, T> {
        let length = max(self.len(), other.len());
        let mut coef = vec![self.ring.zero(); length];
        for (i, x) in self.coef.iter().enumerate() {
            coef[i] = x.clone();
        }
        for (i, x) in other.coef.iter().enumerate() {
            coef[i] = &coef[i] + x;
        }
        Poly::reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    fn add_i64(&self, other: &i64) -> Poly<'a, T> {
        let mut coef = self.coef.clone();
        if coef.is_empty() {
            coef.push(self.ring.from_i64(*other));
        } else {
            coef[0] = &coef[0] + other;
        }
        Poly::reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    fn sub_(&self, other: &Poly<'a, T>) -> Poly<'a, T> {
        let length = max(self.len(), other.len());
        let mut coef = vec![self.ring.zero(); length];
        for (i, x) in self.coef.iter().enumerate() {
            coef[i] = x.clone();
        }
        for (i, x) in other.coef.iter().enumerate() {
            coef[i] = &coef[i] - x;
        }
        Poly::reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    fn sub_i64(&self, other: &i64) -> Poly<'a, T> {
        let mut coef = self.coef.clone();
        if coef.is_empty() {
            coef.push(self.ring.from_i64(-*other));
        } else {
            coef[0] = &coef[0] - other;
        }
        Poly::reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    fn to_single_integer(&self, step: usize, min_len: usize) -> Integer {
        let len = self.len();
        let mut bit = vec![0; step * len];
        for (i, x) in self.coef.iter().enumerate() {
            let idx_from = i * step;
            let idx_to = idx_from + step;
            x.write_digits(&mut bit[idx_from..idx_to], min_len);
        }
        Integer::from_digits(&bit, rug::integer::Order::LsfLe)
    }

    fn from_single_integer(
        value: Integer,
        ring: &'a T::Ring,
        step: usize,
        min_len: usize,
    ) -> Poly<'a, T> {
        let bit = value.to_digits::<u64>(rug::integer::Order::LsfLe);
        let mut coef = Vec::with_capacity((bit.len() + step - 1) / step);
        for from_idx in (0..bit.len()).step_by(step) {
            let to_idx = min(from_idx + step, bit.len());
            coef.push(T::from_digits(ring, &bit[from_idx..to_idx], min_len));
        }
        Poly::new(coef, ring)
    }

    fn mul_(&self, other: &Poly<'a, T>) -> Poly<'a, T> {
        let min_len = min(self.len(), other.len());
        let required_word = self.ring.poly_mul_required_words(min_len);
        let a = self.to_single_integer(required_word, min_len);
        let b = other.to_single_integer(required_word, min_len);
        let c = a * b;
        Poly::from_single_integer(c, self.ring, required_word, min_len)
    }

    fn mul_i64(&self, other: &i64) -> Poly<'a, T> {
        let mut coef = self.coef.iter().map(|x| x * other).collect();
        Poly::reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    fn neg_(&self) -> Poly<'a, T> {
        let coef = self.coef.iter().map(|x| -x).collect();
        Poly {
            coef,
            ring: self.ring,
        }
    }

    fn shl_(&self, shift: &usize) -> Poly<'a, T> {
        let mut coef = vec![self.ring.zero(); *shift];
        coef.extend(self.coef.iter().cloned());
        Poly::new(coef, self.ring)
    }

    fn shr_(&self, shift: &usize) -> Poly<'a, T> {
        let coef = self.coef[min(*shift, self.len())..].to_vec();
        Poly::new(coef, self.ring)
    }

    pub fn lc(&self) -> T {
        if self.coef.is_empty() {
            self.ring.zero()
        } else {
            self.coef.last().unwrap().clone()
        }
    }

    pub fn divmod_with_lc_inv(
        &self,
        other: &Poly<'a, T>,
        lc_inv: &T,
    ) -> (Poly<'a, T>, Poly<'a, T>) {
        if self.len() < other.len() {
            return (Poly::zero(self.ring), self.clone());
        }

        let n = self.deg() as usize;
        let m = other.deg() as usize;

        let mut r_coef = self.coef.clone();
        let mut q_coef = vec![self.ring.zero(); n - m + 1];

        for i in (0..=n - m).rev() {
            let q = &r_coef[i + m] * lc_inv;
            q_coef[i] = q.clone();
            for j in 0..=m {
                r_coef[i + j] = &r_coef[i + j] - &(&q * &other.coef[j]);
            }
        }

        let q = Poly::new(q_coef, self.ring);
        Poly::reduce(&mut r_coef);
        let r = Poly::new(r_coef, self.ring);
        (q, r)
    }

    pub fn divmod(&self, other: &Poly<'a, T>) -> Result<(Poly<'a, T>, Poly<'a, T>), DivError> {
        let lc_inv = other.lc().inv()?;
        Ok(self.divmod_with_lc_inv(other, &lc_inv))
    }

    fn div_(&self, other: &Poly<'a, T>) -> Result<Poly<'a, T>, DivError> {
        let (q, _) = self.divmod(other)?;
        Ok(q)
    }

    fn rem_(&self, other: &Poly<'a, T>) -> Result<Poly<'a, T>, DivError> {
        let (_, r) = self.divmod(other)?;
        Ok(r)
    }

    fn eq_(&self, other: &Poly<'a, T>) -> bool {
        self.coef == other.coef
    }

    pub fn x_power_of(ring: &'a T::Ring, n: usize) -> Poly<'a, T> {
        let mut coef = vec![ring.zero(); n + 1];
        coef[n] = ring.one();
        Poly::new(coef, ring)
    }

    pub fn one(ring: &'a T::Ring) -> Poly<'a, T> {
        Poly::new(vec![ring.one()], ring)
    }

    pub fn zero(ring: &'a T::Ring) -> Poly<'a, T> {
        Poly::new(vec![], ring)
    }

    pub fn from_int_vec(coef: Vec<Integer>, ring: &'a T::Ring) -> Poly<'a, T> {
        let mut coef = coef.into_iter().map(|x| ring.from_integer(x)).collect();
        Poly::reduce(&mut coef);
        Poly::new(coef, ring)
    }

    pub fn is_zero(&self) -> bool {
        self.coef.is_empty()
    }

    pub fn gcd(&self, other: &Poly<'a, T>) -> Result<Poly<'a, T>, DivError> {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let r = a.rem(&b)?;
            a = b;
            b = r;
        }
        Ok(a)
    }
}

overload!(<'a, T: PolyElem<'a>>, Add, Poly<'a, T>, add, add_);
overload!(<'a, T: PolyElem<'a>>, Add, Poly<'a, T>, i64, add, add_i64);
overload!(<'a, T: PolyElem<'a>>, Sub, Poly<'a, T>, sub, sub_);
overload!(<'a, T: PolyElem<'a>>, Sub, Poly<'a, T>, i64, sub, sub_i64);
overload!(<'a, T: PolyElem<'a>>, Mul, Poly<'a, T>, mul, mul_);
overload!(<'a, T: PolyElem<'a>>, Mul, Poly<'a, T>, i64, mul, mul_i64);
overload_unary!(<'a, T: PolyElem<'a>>, Neg, Poly<'a, T>, neg, neg_);
overload!(<'a, T: PolyElem<'a>>, Shl, Poly<'a, T>, usize, shl, shl_);
overload!(<'a, T: PolyElem<'a>>, Shr, Poly<'a, T>, usize, shr, shr_);
overload!(<'a, T: PolyElem<'a>>, Div, Poly<'a, T>, Poly<'a, T>, Result<Poly<'a, T>, DivError>, div, div_);
overload!(<'a, T: PolyElem<'a>>, Rem, Poly<'a, T>, Poly<'a, T>, Result<Poly<'a, T>, DivError>, rem, rem_);
overload_eq!(<'a, T: PolyElem<'a>>, PartialEq, Poly<'a, T>, eq, eq_);

impl<'a, T: PolyElem<'a>> Index<usize> for Poly<'a, T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        &self.coef[index]
    }
}

impl<'a, T: PolyElem<'a>> IndexMut<usize> for Poly<'a, T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        if index >= self.coef.len() {
            self.coef.resize(index + 1, self.ring.zero());
        }
        &mut self.coef[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modint::ModRing;
    use rug::{rand, Integer};

    #[test]
    fn test_poly() {
        let mut rng = rand::RandState::new();
        let mut gen_random = || -> Integer { Integer::from(Integer::random_bits(128, &mut rng)) };

        for _ in 0..10 {
            let modulo = gen_random();
            let ring = ModRing::new(modulo.clone());
            let n = 1000;

            let a = (0..n).map(|_| ring.from(gen_random())).collect::<Vec<_>>();
            let b = (0..n).map(|_| ring.from(gen_random())).collect::<Vec<_>>();
            let c = (0..n).map(|_| ring.from(gen_random())).collect::<Vec<_>>();

            let mut res_naive = vec![ring.from_i64(0); n * 2 - 1];
            for (i, x) in a.iter().enumerate() {
                for (j, y) in b.iter().enumerate() {
                    res_naive[i + j] = &res_naive[i + j] + &(x * y);
                }
            }
            for (i, x) in c.iter().enumerate() {
                res_naive[i] = &res_naive[i] - x;
            }

            let a_poly = Poly::new(a, &ring);
            let b_poly = Poly::new(b, &ring);
            let c_poly = Poly::new(c, &ring);
            let res_poly = a_poly * b_poly - c_poly;

            assert_eq!(res_naive, res_poly.coef);
        }
    }
}
