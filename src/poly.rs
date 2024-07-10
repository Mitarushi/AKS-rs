use std::cmp::{max, min};
use std::ops::{Add, Div, Index, IndexMut, Mul, Neg, Rem, Shl, Shr, Sub};
use rug::Integer;
use crate::modint::{DivState, ModInt, ModRing};

#[derive(Clone, Debug)]
pub struct Poly<'a> {
    pub coef: Vec<ModInt<'a>>,
    pub ring: &'a ModRing,
}

fn significant_bits(x: u64) -> u32 {
    64 - x.leading_zeros()
}

impl<'a> Poly<'a> {
    pub fn new(coef: Vec<ModInt<'a>>, ring: &'a ModRing) -> Poly<'a> {
        Poly { coef, ring }
    }

    pub fn len(&self) -> usize {
        self.coef.len()
    }

    pub fn deg(&self) -> isize {
        self.coef.len() as isize - 1
    }

    fn reduce(coef: &mut Vec<ModInt<'a>>) {
        while coef.len() > 0 && coef.last().unwrap().is_zero() {
            coef.pop();
        }
    }

    fn add_(&self, other: &Poly<'a>) -> Poly<'a> {
        let length = max(self.len(), other.len());
        let mut coef = vec![self.ring.from_i64(0); length];
        for (i, x) in self.coef.iter().enumerate() {
            coef[i] = x.clone();
        }
        for (i, x) in other.coef.iter().enumerate() {
            coef[i] = &coef[i] + x;
        }
        Poly::reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    fn sub_(&self, other: &Poly<'a>) -> Poly<'a> {
        let length = max(self.len(), other.len());
        let mut coef = vec![self.ring.from_i64(0); length];
        for (i, x) in self.coef.iter().enumerate() {
            coef[i] = x.clone();
        }
        for (i, x) in other.coef.iter().enumerate() {
            coef[i] = &coef[i] - x;
        }
        Poly::reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    fn to_single_integer(&self, step: u32) -> Integer {
        let mut bit = vec![0; step as usize * self.coef.len()];
        for (i, x) in self.coef.iter().enumerate() {
            let idx_from = i * step as usize;
            let idx_to = idx_from + step as usize;
            x.value.write_digits::<u64>(&mut bit[idx_from..idx_to], rug::integer::Order::LsfLe);
        }
        Integer::from_digits(&bit, rug::integer::Order::LsfLe)
    }

    fn from_single_integer(value: Integer, ring: &'a ModRing, step: u32) -> Poly<'a> {
        let bit = value.to_digits::<u64>(rug::integer::Order::LsfLe);
        let mut coef = Vec::new();
        coef.reserve(bit.len() / step as usize + 1);
        for from_idx in (0..bit.len()).step_by(step as usize) {
            let to_idx = min(from_idx + step as usize, bit.len());
            let x = Integer::from_digits(&bit[from_idx..to_idx], rug::integer::Order::LsfLe);
            coef.push(ring.from(x));
        }
        Poly::new(coef, ring)
    }

    fn mul_(&self, other: &Poly) -> Poly<'a> {
        let min_len = min(self.len(), other.len());
        let required_bits = self.ring.modulo.significant_bits() * 2 + significant_bits(min_len as u64);
        let step = (required_bits + 63) / 64;
        let a = self.to_single_integer(step);
        let b = other.to_single_integer(step);
        let c = a * b;
        Poly::from_single_integer(c, self.ring, step)
    }

    fn mul_modint(&self, other: &ModInt<'a>) -> Poly<'a> {
        let mut coef = self.coef.iter().map(|x| x * other).collect();
        Poly::reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    fn neg_(&self) -> Poly<'a> {
        let coef = self.coef.iter().map(|x| -x).collect();
        Poly {
            coef,
            ring: self.ring,
        }
    }

    fn shl_(&self, shift: usize) -> Poly<'a> {
        let mut coef = vec![self.ring.from_i64(0); shift];
        coef.extend(self.coef.iter().cloned());
        Poly::new(coef, self.ring)
    }

    fn shr_(&self, shift: usize) -> Poly<'a> {
        let mut coef = self.coef.clone();
        coef.drain(0..min(shift, coef.len()));
        Poly::new(coef, self.ring)
    }

    pub fn lc(&self) -> ModInt<'a> {
        if self.coef.len() == 0 {
            self.ring.from_i64(0)
        } else {
            self.coef.last().unwrap().clone()
        }
    }

    pub fn divmod(&self, other: &Poly<'a>) -> DivState<(Poly<'a>, Poly<'a>)> {
        if self.len() == 0 {
            return DivState::Result((Poly::zero(self.ring), Poly::zero(self.ring)));
        }

        let n = self.deg() as usize;
        let m = other.deg() as usize;

        let mut r_coef = self.coef.clone();
        let mut q_coef = vec![self.ring.from_i64(0); n - m + 1];

        let lc_r_inv = other.lc().inv();
        match lc_r_inv {
            DivState::Error => return DivState::Error,
            DivState::DivisorFound(x) => return DivState::DivisorFound(x),
            _ => {}
        }
        let lc_r_inv = lc_r_inv.unwrap();

        for i in (0..=n - m).rev() {
            let q = &r_coef[i + m] * &lc_r_inv;
            q_coef[i] = q.clone();
            for j in 0..=m {
                r_coef[i + j] = &r_coef[i + j] - &(&q * &other.coef[j]);
            }
        }

        let q = Poly::new(q_coef, self.ring);
        Poly::reduce(&mut r_coef);
        let r = Poly::new(r_coef, self.ring);
        DivState::Result((q, r))
    }

    fn div_(&self, other: &Poly<'a>) -> DivState<Poly<'a>> {
        match self.divmod(other) {
            DivState::Error => DivState::Error,
            DivState::DivisorFound(x) => DivState::DivisorFound(x),
            DivState::Result((q, _)) => DivState::Result(q),
        }
    }

    fn rem_(&self, other: &Poly<'a>) -> DivState<Poly<'a>> {
        match self.divmod(other) {
            DivState::Error => DivState::Error,
            DivState::DivisorFound(x) => DivState::DivisorFound(x),
            DivState::Result((_, r)) => DivState::Result(r),
        }
    }

    pub fn x_power_of(ring: &'a ModRing, n: usize) -> Poly<'a> {
        let mut coef = vec![ring.from_i64(0); n + 1];
        coef[n] = ring.from_i64(1);
        Poly::new(coef, ring)
    }

    pub fn one(ring: &'a ModRing) -> Poly<'a> {
        Poly::new(vec![ring.from_i64(1)], ring)
    }

    pub fn zero(ring: &'a ModRing) -> Poly<'a> {
        Poly::new(vec![], ring)
    }
}

impl<'a> Add for Poly<'a> {
    type Output = Poly<'a>;

    fn add(self, other: Poly<'a>) -> Poly<'a> {
        self.add_(&other)
    }
}

impl<'a> Add for &Poly<'a> {
    type Output = Poly<'a>;

    fn add(self, other: &Poly<'a>) -> Poly<'a> {
        self.add_(other)
    }
}

impl<'a> Sub for Poly<'a> {
    type Output = Poly<'a>;

    fn sub(self, other: Poly<'a>) -> Poly<'a> {
        self.sub_(&other)
    }
}

impl<'a> Sub for &Poly<'a> {
    type Output = Poly<'a>;

    fn sub(self, other: &Poly<'a>) -> Poly<'a> {
        self.sub_(other)
    }
}

impl<'a> Mul for Poly<'a> {
    type Output = Poly<'a>;

    fn mul(self, other: Poly<'a>) -> Poly<'a> {
        self.mul_(&other)
    }
}

impl<'a> Mul<ModInt<'a>> for Poly<'a> {
    type Output = Poly<'a>;

    fn mul(self, other: ModInt<'a>) -> Poly<'a> {
        self.mul_modint(&other)
    }
}

impl<'a> Mul for &Poly<'a> {
    type Output = Poly<'a>;

    fn mul(self, other: &Poly<'a>) -> Poly<'a> {
        self.mul_(other)
    }
}

impl<'a> Mul<&ModInt<'a>> for &Poly<'a> {
    type Output = Poly<'a>;

    fn mul(self, other: &ModInt<'a>) -> Poly<'a> {
        self.mul_modint(&other)
    }
}

impl<'a> Mul<i64> for &Poly<'a> {
    type Output = Poly<'a>;

    fn mul(self, other: i64) -> Poly<'a> {
        self.mul(&self.ring.from_bounded(Integer::from(other)))
    }
}

impl<'a> Neg for Poly<'a> {
    type Output = Poly<'a>;

    fn neg(self) -> Poly<'a> {
        self.neg_()
    }
}

impl<'a> Neg for &Poly<'a> {
    type Output = Poly<'a>;

    fn neg(self) -> Poly<'a> {
        self.neg_()
    }
}

impl<'a> Index<usize> for Poly<'a> {
    type Output = ModInt<'a>;

    fn index(&self, index: usize) -> &ModInt<'a> {
        &self.coef[index]
    }
}

impl<'a> IndexMut<usize> for Poly<'a> {
    fn index_mut(&mut self, index: usize) -> &mut ModInt<'a> {
        if index >= self.coef.len() {
            self.coef.resize(index + 1, self.ring.from_i64(0));
        }
        &mut self.coef[index]
    }
}

impl<'a> Shl<usize> for Poly<'a> {
    type Output = Poly<'a>;

    fn shl(self, shift: usize) -> Poly<'a> {
        self.shl_(shift)
    }
}

impl<'a> Shl<usize> for &Poly<'a> {
    type Output = Poly<'a>;

    fn shl(self, shift: usize) -> Poly<'a> {
        self.shl_(shift)
    }
}

impl<'a> Shr<usize> for Poly<'a> {
    type Output = Poly<'a>;

    fn shr(self, shift: usize) -> Poly<'a> {
        self.shr_(shift)
    }
}

impl<'a> Shr<usize> for &Poly<'a> {
    type Output = Poly<'a>;

    fn shr(self, shift: usize) -> Poly<'a> {
        self.shr_(shift)
    }
}

impl<'a> Div for Poly<'a> {
    type Output = DivState<Poly<'a>>;

    fn div(self, other: Poly<'a>) -> DivState<Poly<'a>> {
        self.div_(&other)
    }
}

impl<'a> Div for &Poly<'a> {
    type Output = DivState<Poly<'a>>;

    fn div(self, other: &Poly<'a>) -> DivState<Poly<'a>> {
        self.div_(other)
    }
}

impl<'a> Rem for Poly<'a> {
    type Output = DivState<Poly<'a>>;

    fn rem(self, other: Poly<'a>) -> DivState<Poly<'a>> {
        self.rem_(&other)
    }
}

impl<'a> Rem for &Poly<'a> {
    type Output = DivState<Poly<'a>>;

    fn rem(self, other: &Poly<'a>) -> DivState<Poly<'a>> {
        self.rem_(other)
    }
}

impl<'a> PartialEq for Poly<'a> {
    fn eq(&self, other: &Poly<'a>) -> bool {
        self.coef == other.coef
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rug::{Integer, rand};

    #[test]
    fn test_poly() {
        let mut rng = rand::RandState::new();
        let mut gen_random = || -> Integer {
            Integer::from(Integer::random_bits(128, &mut rng))
        };

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