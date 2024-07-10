use std::cell::RefCell;
use std::cmp::{max, min};
use std::ops::{Add, Neg, Mul, Sub};
use rug::Integer;
use rug::integer::Order;
use crate::{overload, overload_eq, overload_unary};
use crate::poly::Poly;

#[derive(Clone, Debug)]
struct FastPolyDiv<'a> {
    b_deg: usize,
    m_len: usize,
    inv: Poly<'a>,
    modulo: Poly<'a>,
}

impl<'a> FastPolyDiv<'a> {
    pub fn new(modulo: Poly<'a>) -> Self {
        let m_len = modulo.deg() as usize;
        let b_deg = m_len + 1;
        let b = Poly::x_power_of(modulo.ring, b_deg);
        let inv = (&b / &modulo).unwrap();
        FastPolyDiv {
            b_deg,
            m_len,
            inv,
            modulo,
        }
    }

    fn double_inv(&mut self) {
        let b = Poly::x_power_of(self.modulo.ring, self.b_deg);
        let inv = &self.inv * &(&b * 2 - (&self.inv * &self.modulo));
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

    pub fn div(&mut self, x: &Poly<'a>) -> Poly<'a> {
        let x_deg = max(x.deg(), 0) as usize;
        self.double_until(x_deg);
        let inv = &self.inv >> (self.b_deg - x_deg);

        let pre_shift = min(x_deg, self.m_len - 1);
        let post_shift = x_deg - pre_shift;
        let q = &inv * (x >> pre_shift) >> post_shift;
        q
    }

    pub fn rem(&mut self, x: &Poly<'a>) -> Poly<'a> {
        let q = self.div(x);
        let r = x - &(&q * &self.modulo);
        r
    }
}

#[derive(Clone, Debug)]
pub struct ModPolyRing<'a> {
    pub modulo: Poly<'a>,
    fast_div: RefCell<FastPolyDiv<'a>>,
}

#[derive(Clone, Debug)]
pub struct ModPoly<'a, 'b> {
    pub value: Poly<'a>,
    pub ring: &'b ModPolyRing<'a>,
}

impl<'a, 'b> ModPolyRing<'a> {
    pub fn new(modulo: Poly<'a>) -> Self {
        let fast_div = FastPolyDiv::new(modulo.clone());
        ModPolyRing {
            modulo,
            fast_div: RefCell::new(fast_div),
        }
    }

    pub fn from(&'b self, value: Poly<'a>) -> ModPoly<'a, 'b> {
        self.from_bounded(self.fast_div.borrow_mut().rem(&value))
    }

    pub fn from_bounded(&'b self, value: Poly<'a>) -> ModPoly<'a, 'b> {
        ModPoly {
            value,
            ring: self,
        }
    }

    pub fn add(&'b self, a: &ModPoly<'a, 'b>, b: &ModPoly<'a, 'b>) -> ModPoly<'a, 'b> {
        self.from_bounded(&a.value + &b.value)
    }

    pub fn sub(&'b self, a: &ModPoly<'a, 'b>, b: &ModPoly<'a, 'b>) -> ModPoly<'a, 'b> {
        self.from_bounded(&a.value - &b.value)
    }

    pub fn mul(&'b self, a: &ModPoly<'a, 'b>, b: &ModPoly<'a, 'b>) -> ModPoly<'a, 'b> {
        let r = &a.value * &b.value;
        let r = self.fast_div.borrow_mut().rem(&r);
        self.from_bounded(r)
    }

    pub fn neg(&'b self, a: &ModPoly<'a, 'b>) -> ModPoly<'a, 'b> {
        self.from_bounded(-&a.value)
    }
}

impl<'a, 'b> ModPoly<'a, 'b> {
    fn add_(&self, other: &ModPoly<'a, 'b>) -> ModPoly<'a, 'b> {
        self.ring.add(self, other)
    }

    fn sub_(&self, other: &ModPoly<'a, 'b>) -> ModPoly<'a, 'b> {
        self.ring.sub(self, other)
    }

    fn mul_(&self, other: &ModPoly<'a, 'b>) -> ModPoly<'a, 'b> {
        self.ring.mul(self, other)
    }

    fn neg_(&self) -> ModPoly<'a, 'b> {
        self.ring.neg(self)
    }

    fn eq_(&self, other: &ModPoly<'a, 'b>) -> bool {
        self.value == other.value
    }

    pub fn pow(&self, n: &Integer) -> ModPoly<'a, 'b> {
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

overload!('a, 'b, Add, ModPoly<'a, 'b>, add, add_);
overload!('a, 'b, Sub, ModPoly<'a, 'b>, sub, sub_);
overload!('a, 'b, Mul, ModPoly<'a, 'b>, mul, mul_);
overload_unary!('a, 'b, Neg, ModPoly<'a, 'b>, neg, neg_);
overload_eq!('a, 'b, PartialEq, ModPoly<'a, 'b>, eq, eq_);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modint::ModRing;
    use rug::Integer;

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
            let modulo = Poly::from_int_vec(modulo_coef, &n_ring);
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