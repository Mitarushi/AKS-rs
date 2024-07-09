use std::cmp::{max, min};
use std::ops::{Add, Mul, Neg, Sub};
use rug::Integer;
use crate::modint::{ModInt, ModRing};

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

    pub fn deg(&self) -> usize {
        self.coef.len() - 1
    }

    fn reduce(coef: &mut Vec<ModInt<'a>>) {
        while coef.len() > 0 && coef.last().unwrap().is_zero() {
            coef.pop();
        }
    }

    fn add_(&self, other: &Poly<'a>) -> Poly<'a> {
        let length = max(self.deg(), other.deg()) + 1;
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
        let length = max(self.deg(), other.deg()) + 1;
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
        let min_len = min(self.deg(), other.deg()) + 1;
        let required_bits = self.ring.modulo.significant_bits() * 2 + significant_bits(min_len as u64);
        let step = (required_bits + 63) / 64;
        let a = self.to_single_integer(step);
        let b = other.to_single_integer(step);
        let c = a * b;
        Poly::from_single_integer(c, self.ring, step)
    }

    fn neg_(&self) -> Poly<'a> {
        let coef = self.coef.iter().map(|x| -x).collect();
        Poly {
            coef,
            ring: self.ring,
        }
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

impl<'a> Mul for &Poly<'a> {
    type Output = Poly<'a>;

    fn mul(self, other: &Poly<'a>) -> Poly<'a> {
        self.mul_(other)
    }
}

impl<'a> Neg for Poly<'a> {
    type Output = Poly<'a>;

    fn neg(self) -> Poly<'a> {
        self.neg_()
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

        for _ in 0..100 {
            let modulo = gen_random();
            let ring = ModRing::new(modulo.clone());
            let n = 1000;

            let a = (0..n).map(|_| gen_random()).collect::<Vec<_>>();
            let b = (0..n).map(|_| gen_random()).collect::<Vec<_>>();
            let c = (0..n).map(|_| gen_random()).collect::<Vec<_>>();

            let mut res_naive = vec![Integer::from(0); 2 * n - 1];
            for (i, x) in a.iter().enumerate() {
                for (j, y) in b.iter().enumerate() {
                    res_naive[i + j] += x * y;
                }
            }
            for (i, x) in c.iter().enumerate() {
                res_naive[i] -= x;
            }
            res_naive.iter_mut().for_each(|x| *x %= &modulo);

            let a_poly = Poly::new(a.iter().map(|x| ring.from(x.clone())).collect(), &ring);
            let b_poly = Poly::new(b.iter().map(|x| ring.from(x.clone())).collect(), &ring);
            let c_poly = Poly::new(c.iter().map(|x| ring.from(x.clone())).collect(), &ring);
            let res_poly = a_poly * b_poly - c_poly;

            let res_poly = res_poly.coef.iter().map(|x| x.value.clone()).collect::<Vec<_>>();

            assert_eq!(res_naive, res_poly);
        }
    }
}