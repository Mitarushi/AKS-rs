use std::cell::RefCell;
use rug::{Assign, Integer};
use std::fmt::{Debug, Display};
use std::ops::{Add, Neg, Mul, Sub};


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

#[derive(Clone)]
pub struct ModRing {
    pub modulo: Integer,
    fast_div: RefCell<FastDiv>,
}

#[derive(Clone)]
pub struct ModInt<'a> {
    pub value: Integer,
    pub ring: &'a ModRing,
}

pub enum InvState<'a> {
    Zero,
    Exists(ModInt<'a>),
    DivisorFound(Integer),
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
}

impl<'a> ModInt<'a> {
    fn add_(&self, other: &ModInt<'a>) -> ModInt<'a> {
        self.ring.add(self, other)
    }

    fn sub_(&self, other: &ModInt<'a>) -> ModInt<'a> {
        self.ring.sub(self, other)
    }

    fn mul_(&self, other: &ModInt<'a>) -> ModInt<'a> {
        self.ring.mul(self, other)
    }

    fn neg_(&self) -> ModInt<'a> {
        self.ring.neg(self)
    }

    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    pub fn inv(&self) -> InvState {
        let a = &self.value;
        let b = &self.ring.modulo;
        let mut g = Integer::new();
        let mut x = Integer::new();
        (&mut g, &mut x).assign(a.extended_gcd_ref(b));

        if &g == b {
            InvState::Zero
        } else if g == 1 {
            InvState::Exists(self.ring.from_bounded(x))
        } else {
            InvState::DivisorFound(g)
        }
    }
}

impl<'a> Add for ModInt<'a> {
    type Output = ModInt<'a>;

    fn add(self, other: ModInt<'a>) -> ModInt<'a> {
        self.add_(&other)
    }
}

impl<'a> Add for &ModInt<'a> {
    type Output = ModInt<'a>;

    fn add(self, other: &ModInt<'a>) -> ModInt<'a> {
        self.add_(other)
    }
}

impl<'a> Sub for ModInt<'a> {
    type Output = ModInt<'a>;

    fn sub(self, other: ModInt<'a>) -> ModInt<'a> {
        self.sub_(&other)
    }
}

impl<'a> Sub for &ModInt<'a> {
    type Output = ModInt<'a>;

    fn sub(self, other: &ModInt<'a>) -> ModInt<'a> {
        self.sub_(other)
    }
}

impl<'a> Mul for ModInt<'a> {
    type Output = ModInt<'a>;

    fn mul(self, other: ModInt<'a>) -> ModInt<'a> {
        self.mul_(&other)
    }
}

impl<'a> Mul for &ModInt<'a> {
    type Output = ModInt<'a>;

    fn mul(self, other: &ModInt<'a>) -> ModInt<'a> {
        self.mul_(other)
    }
}

impl<'a> Neg for ModInt<'a> {
    type Output = ModInt<'a>;

    fn neg(self) -> ModInt<'a> {
        self.neg_()
    }
}

impl<'a> Neg for &ModInt<'a> {
    type Output = ModInt<'a>;

    fn neg(self) -> ModInt<'a> {
        self.neg_()
    }
}

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
