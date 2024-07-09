use std::cell::RefCell;
use rug::{Assign, Integer};
use std::fmt::{Debug, Display};
use std::ops::{Add, AddAssign, Neg, Mul, MulAssign, Sub, SubAssign};


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
        let inv = inv >> self.m_len;

        self.inv = inv;
        self.b_log = self.b_log * 2 - self.m_len;
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

#[derive(Debug, Clone)]
pub struct ModRing {
    pub modulo: Integer,
    fast_div: RefCell<FastDiv>,
}

#[derive(Debug, Clone)]
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
        ModInt {
            value: self.fast_div.borrow_mut().rem(&value),
            ring: self,
        }
    }

    pub fn from_i64(&self, value: i64) -> ModInt {
        self.from(Integer::from(value))
    }

    pub fn add(&self, a: &ModInt, b: &ModInt) -> ModInt {
        let r = Integer::from(&a.value + &b.value);
        let value = if r >= self.modulo { r - &self.modulo } else { r };
        ModInt {
            value,
            ring: self,
        }
    }

    pub fn sub(&self, a: &ModInt, b: &ModInt) -> ModInt {
        let r = Integer::from(&a.value - &b.value);
        let value = if r < 0 { r + &self.modulo } else { r };
        ModInt {
            value,
            ring: self,
        }
    }

    pub fn mul(&self, a: &ModInt, b: &ModInt) -> ModInt {
        let r = Integer::from(&a.value * &b.value);
        ModInt {
            value: self.fast_div.borrow_mut().rem(&r),
            ring: self,
        }
    }

    pub fn neg(&self, a: &ModInt) -> ModInt {
        let value = if a.value.is_zero() {
            Integer::from(0)
        } else {
            Integer::from(&self.modulo - &a.value)
        };
        ModInt {
            value,
            ring: self,
        }
    }
}

impl ModInt<'_> {
    pub fn add(&self, other: &ModInt) -> ModInt {
        self.ring.add(self, other)
    }

    pub fn sub(&self, other: &ModInt) -> ModInt {
        self.ring.sub(self, other)
    }

    pub fn mul(&self, other: &ModInt) -> ModInt {
        self.ring.mul(self, other)
    }

    pub fn neg(&self) -> ModInt {
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
            InvState::Exists(
                ModInt {
                    value: x,
                    ring: self.ring,
                }
            )
        } else {
            InvState::DivisorFound(g)
        }
    }
}

impl<'a> Add for ModInt<'a> {
    type Output = ModInt<'a>;

    fn add(self, other: ModInt) -> ModInt<'a> {
        self.ring.add(&self, &other)
    }
}

impl<'a> Add for &ModInt<'a> {
    type Output = ModInt<'a>;

    fn add(self, other: &ModInt) -> ModInt<'a> {
        self.ring.add(self, other)
    }
}

impl<'a> AddAssign for ModInt<'a> {
    fn add_assign(&mut self, other: ModInt) {
        *self = self.ring.add(self, &other);
    }
}

impl<'a> Sub for ModInt<'a> {
    type Output = ModInt<'a>;

    fn sub(self, other: ModInt) -> ModInt<'a> {
        self.ring.sub(&self, &other)
    }
}

impl<'a> Sub for &ModInt<'a> {
    type Output = ModInt<'a>;

    fn sub(self, other: &ModInt) -> ModInt<'a> {
        self.ring.sub(self, other)
    }
}

impl<'a> SubAssign for ModInt<'a> {
    fn sub_assign(&mut self, other: ModInt) {
        *self = self.ring.sub(self, &other);
    }
}

impl<'a> Mul for ModInt<'a> {
    type Output = ModInt<'a>;

    fn mul(self, other: ModInt) -> ModInt<'a> {
        self.ring.mul(&self, &other)
    }
}

impl<'a> Mul for &ModInt<'a> {
    type Output = ModInt<'a>;

    fn mul(self, other: &ModInt) -> ModInt<'a> {
        self.ring.mul(self, other)
    }
}

impl<'a> MulAssign for ModInt<'a> {
    fn mul_assign(&mut self, other: ModInt) {
        *self = self.ring.mul(self, &other);
    }
}

impl<'a> Neg for ModInt<'a> {
    type Output = ModInt<'a>;

    fn neg(self) -> ModInt<'a> {
        self.ring.neg(&self)
    }
}

impl<'a> Neg for &ModInt<'a> {
    type Output = ModInt<'a>;

    fn neg(self) -> ModInt<'a> {
        self.ring.neg(self)
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
    use super::*;

    #[test]
    fn test_modint() {
        let mod_int = 1000000007i128;
        let a_int = 1414213562373i128;
        let b_int = 3141592653589i128;

        let ring = ModRing::new(Integer::from(mod_int));
        let a = ring.from(Integer::from(a_int));
        let b = ring.from(Integer::from(b_int));

        let c = &a + &b;
        assert_eq!(c.value, (a_int + b_int) % mod_int);

        let c = &a - &b;
        assert_eq!(c.value, (a_int - b_int) % mod_int + mod_int);

        let c = &a * &b;
        assert_eq!(c.value, (a_int * b_int) % mod_int);
    }
}
