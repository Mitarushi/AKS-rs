use std::cmp::{max, min};
use std::ops::{Add, Mul, Sub};
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

    pub fn add(&self, other: &Poly) -> Poly<'a> {
        let length = max(self.deg(), other.deg()) + 1;
        let mut coef = vec![self.ring.from_i64(0); length];
        for (i, x) in self.coef.iter().enumerate() {
            coef[i] = x.clone();
        }
        for (i, x) in other.coef.iter().enumerate() {
            coef[i] = self.ring.add(&coef[i], x);
        }
        Poly::reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    pub fn sub(&self, other: &Poly) -> Poly<'a> {
        let length = max(self.deg(), other.deg()) + 1;
        let mut coef = vec![self.ring.from_i64(0); length];
        for (i, x) in self.coef.iter().enumerate() {
            coef[i] = x.clone();
        }
        for (i, x) in other.coef.iter().enumerate() {
            coef[i] = self.ring.sub(&coef[i], x);
        }
        self.reduce(&mut coef);
        Poly::new(coef, self.ring)
    }

    fn to_single_integer(&self, step: u32) -> Integer {
        let mut bit = vec![0; step as usize * self.coef.len()];
        for (i, x) in self.coef.iter().enumerate() {
            let idx_from = i * step as usize;
            let idx_to = idx_from + step as usize;
            x.value.write_digits::<u64>(&mut bit[idx_from..idx_to], rug::integer::Order::Lsf);
        }
        Integer::from_digits(&bit, rug::integer::Order::Lsf)
    }

    fn from_single_integer(value: Integer, ring: &'a ModRing, step: u32) -> Poly<'a> {
        let bit = value.to_digits::<u64>(rug::integer::Order::Lsf);
        let mut coef = Vec::new();
        for from_idx in (0..bit.len()).step_by(step as usize) {
            let to_idx = min(from_idx + step as usize, bit.len());
            let x = Integer::from_digits(&bit[from_idx..to_idx], rug::integer::Order::Lsf);
            coef.push(ring.from_bounded(x));
        }
        Poly::new(coef, ring)
    }

    pub fn mul(&self, other: &Poly) -> Poly<'a> {
        let min_len = min(self.deg(), other.deg()) + 1;
        let required_bits = self.ring.modulo.significant_bits() + significant_bits(min_len as u64);
        let step = (required_bits + 63) / 64;
        let a = self.to_single_integer(step);
        let b = other.to_single_integer(step);
        let c = a * b;
        Poly::from_single_integer(c, self.ring, step)
    }

    pub fn neg(&self) -> Poly<'a> {
        let mut coef = self.coef.iter().map(|x| self.ring.neg(x)).collect();
        Poly {
            coef,
            ring: self.ring,
        }
    }
}

impl<'a> Add for Poly<'a> {
    type Output = Poly<'a>;

    fn add(self, other: Poly<'a>) -> Poly<'a> {
        self.add(other)
    }
}

impl<'a> Add for &Poly<'a> {
    type Output = Poly<'a>;

    fn add(self, other: &Poly<'a>) -> Poly<'a> {
        self.add(other)
    }
}

impl<'a> Sub for Poly<'a> {
    type Output = Poly<'a>;

    fn sub(self, other: Poly<'a>) -> Poly<'a> {
        self.sub(other)
    }
}

impl<'a> Sub for &Poly<'a> {
    type Output = Poly<'a>;

    fn sub(self, other: &Poly<'a>) -> Poly<'a> {
        self.sub(other)
    }
}

impl<'a> Mul for Poly<'a> {
    type Output = Poly<'a>;

    fn mul(self, other: Poly<'a>) -> Poly<'a> {
        self.mul(other)
    }
}

impl<'a> Mul for &Poly<'a> {
    type Output = Poly<'a>;

    fn mul(self, other: &Poly<'a>) -> Poly<'a> {
        self.mul(other)
    }
}
