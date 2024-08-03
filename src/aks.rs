use std::cmp::Reverse;
use std::collections::BinaryHeap;

use rug::integer::IsPrime;
use rug::ops::Pow;
use rug::rand::RandState;
use rug::{Complete, Float, Integer};

use crate::modint::{ModInt, ModRing};
use crate::poly::Poly;
use crate::poly_elem_trait::PolyElemRing;
use crate::poly_ring::{ModPolyRing, NaivePolyDiv, NearMonomialDiv};

fn factor(n: i64) -> Vec<i64> {
    let mut n = n;
    let mut factors = Vec::new();
    for i in 2.. {
        if i * i > n {
            break;
        }
        if n % i == 0 {
            factors.push(i);
            while n % i == 0 {
                n /= i;
            }
        }
    }
    if n > 1 {
        factors.push(n);
    }
    factors
}

fn phi(n: i64) -> i64 {
    let factors = factor(n);
    let mut phi = n;
    for &p in factors.iter() {
        phi = phi / p * (p - 1);
    }
    phi
}

pub fn aks(n: &Integer) -> bool {
    if n.is_perfect_power() {
        return false;
    }
    let lgn = n.significant_bits() as i64;
    let n_float = Float::with_val(lgn as u32 * 3, n);
    let lgn2 = n_float
        .log2()
        .square()
        .floor()
        .to_integer()
        .unwrap()
        .to_i64()
        .unwrap();

    for a in 2..=lgn2 {
        if n == &a {
            return true;
        }
        if n.is_divisible_u(a as u32) {
            return false;
        }
    }

    let n_ring = ModRing::new(n.clone());

    let r = (2..)
        .find(|r| {
            let mut i = 1;
            let x = n.mod_u(*r);
            for _ in 0..lgn2 {
                i = i * x % *r;
                if i == 1 {
                    return false;
                }
            }
            true
        })
        .unwrap();

    let phi_r = phi(r as i64);
    let a_limit = ((phi_r as f64).sqrt() * lgn as f64).floor() as i64;

    let poly = Poly::x_power_of(&n_ring, r as usize) - Poly::new(vec![n_ring.one()], &n_ring);
    let fast_div = NearMonomialDiv::new(r as usize, n_ring.one());
    let poly_ring = ModPolyRing::from_fast_div(poly, fast_div);

    (1..=a_limit).all(|a| {
        let x_a = Poly::new(vec![n_ring.from_i64(a), n_ring.from_i64(1)], &n_ring);
        let x_a = poly_ring.from(x_a);
        let x_a_n = x_a.pow(n);

        let x = Poly::x_power_of(&n_ring, 1);
        let x = poly_ring.from(x);
        let x_n_a =
            &x.pow(n) + &poly_ring.from_bounded(Poly::new(vec![n_ring.from_i64(a)], &n_ring));

        x_a_n == x_n_a
    })
}

fn find_min_rd(n: &Integer) -> (i64, u32) {
    let cost = |r: i64, d: u32| -> i64 {
        let d = d as i64;
        r * d * d
    };

    let min_r = |n: &Integer, d: u32| -> i64 {
        let approx_lgn = n.significant_bits();
        let n_float = Float::with_val(approx_lgn * 3, n);
        let lgn = n_float.log2();
        let r_float = (lgn * d).square().ceil();
        r_float.to_integer().unwrap().to_i64().unwrap()
    };

    let max_r = |n: &Integer, d: u32| -> i64 {
        let approx_lgn = n.significant_bits();
        let n_float = Float::with_val(approx_lgn * 3, n);
        let lgn = n_float.log2();
        let r_float = ((lgn * d).square() * (d + 1)).floor();
        r_float.to_integer().unwrap().to_i64().unwrap()
    };

    let mut heap = BinaryHeap::new();

    let push = |heap: &mut BinaryHeap<_>, r: i64, d: u32, is_first: bool| {
        let c = cost(r, d);
        heap.push(Reverse((c, r, d, is_first)));
    };

    push(&mut heap, min_r(n, 1), 1, true);

    let mut nd_vec = vec![Integer::ZERO, n.clone() - Integer::ONE];
    // let mut max_r_vec = vec![0, max_r(n, 1)];

    const R_STEP: i64 = 100000;

    loop {
        let Reverse((_, r_from, d, is_first)) = heap.pop().unwrap();
        for r in r_from..r_from + R_STEP {
            if nd_vec[d as usize].is_divisible_u(r as u32) {
                return (r, d);
            }
        }

        if is_first {
            push(&mut heap, min_r(n, d + 1), d + 1, true);
            nd_vec.push(n.pow(d + 1).complete() - Integer::ONE);
            // max_r_vec.push(max_r(n, d + 1));
        }

        // if r_from + R_STEP <= max_r_vec[d as usize] {
        //     push(&mut heap, r_from + R_STEP, d, false);
        // }
        push(&mut heap, r_from + R_STEP, d, false);
    }
}

fn gen_random_poly<'a>(
    rng: &mut RandState,
    ring: &'a ModRing,
    d: u32,
    is_monic: bool,
) -> Poly<'a, ModInt<'a>> {
    let coef = if is_monic {
        (0..d)
            .map(|_| ring.random_from(rng))
            .chain(std::iter::once(ring.one()))
            .collect()
    } else {
        (0..=d).map(|_| ring.random_from(rng)).collect()
    };
    Poly::new(coef, ring)
}

pub fn quartic_aks(n: &Integer) -> bool {
    if n.is_perfect_power() {
        return false;
    }

    let (r, d) = find_min_rd(n);
    let n_ring = ModRing::new(n.clone());
    let nd = n.pow(d).complete();
    let d_factor = factor(d as i64);
    let r_factor = factor(r);

    let mut rng = RandState::new();

    let f = loop {
        if n.is_probably_prime(1) == IsPrime::No {
            return false;
        }

        let f = gen_random_poly(&mut rng, &n_ring, d, true);
        let f_ring = ModPolyRing::from_fast_div(f.clone(), NaivePolyDiv::new(f.clone()));

        let t = f_ring.from(Poly::x_power_of(&n_ring, 1));
        let t_pow = t.pow(&nd);

        if t_pow != t {
            continue;
        }

        if d_factor.iter().all(|q| {
            let nd_q = n.pow(d / *q as u32).complete();
            let t_pow_q = t.pow(&nd_q);
            match f.gcd(&t_pow_q.value) {
                Ok(gcd) => gcd.deg() == 0,
                Err(_) => false,
            }
        }) {
            break f;
        }
    };
    let f_ring = ModPolyRing::from_fast_div(f.clone(), NaivePolyDiv::new(f.clone()));

    let b = loop {
        if n.is_probably_prime(1) == IsPrime::No {
            return false;
        }

        let b = gen_random_poly(&mut rng, &n_ring, d - 1, false);
        let b = f_ring.from(b);

        if b.pow(&(&nd - Integer::ONE).complete()) != f_ring.one() {
            continue;
        }

        if r_factor.iter().all(|q| {
            let b_pow = b.pow(&((&nd - Integer::ONE).complete() / q));
            match f.gcd(&b_pow.value) {
                Ok(gcd) => gcd.deg() == 0,
                Err(_) => false,
            }
        }) {
            break b;
        }
    };

    let xr_b = Poly::x_power_of(&f_ring, r as usize) - Poly::new(vec![b.clone()], &f_ring);
    let xr_b_ring =
        ModPolyRing::from_fast_div(xr_b.clone(), NearMonomialDiv::new(r as usize, b.clone()));

    let x = xr_b_ring.from_bounded(Poly::x_power_of(&f_ring, 1));
    let x_1_nd = (&x - xr_b_ring.one()).pow(&nd);
    let x_nd_1 = x.pow(&nd) - xr_b_ring.one();

    x_1_nd == x_nd_1
}

#[cfg(test)]
mod tests {
    use rug::integer::IsPrime;

    use super::*;

    #[test]
    fn test_aks_small() {
        assert!(aks(&Integer::from(998244353)));
        assert!(!aks(&Integer::from(998244353i64 * 1000000007)));
    }

    #[test]
    fn test_aks_large() {
        let mut rng = rug::rand::RandState::new();
        let mut random_int = || Integer::from(Integer::random_bits(20, &mut rng));

        for i in 0..10 {
            let is_prime = i % 2 == 0;
            let mut n = random_int();
            if is_prime {
                n = n.next_prime();
            }
            let is_prime = n.is_probably_prime(10) != IsPrime::No;
            let is_prime_aks = aks(&n);
            println!("{}: {} {}", i, n, is_prime_aks);
            assert_eq!(is_prime, is_prime_aks, "Failed on test case {}", i);
        }
    }

    #[test]
    fn test_small_quartic_aks() {
        for i in 2..10000 {
            let n = Integer::from(i);
            let is_prime = n.is_probably_prime(10) != IsPrime::No;
            let is_prime_aks = quartic_aks(&n);
            assert_eq!(is_prime, is_prime_aks, "Failed on test case {}", i);
        }
    }

    #[test]
    fn test_large_prime_quartic_aks() {
        let mut rng = RandState::new();
        let mut random_int = || Integer::from(Integer::random_bits(70, &mut rng));

        for _ in 0..5 {
            let n = random_int().next_prime();
            let res = quartic_aks(&n);
            println!("{}: {}", n, res);
            assert!(res, "Failed on test case {}", n);
        }
    }

    #[test]
    fn test_large_composite_quartic_aks() {
        let mut rng = rug::rand::RandState::new();
        let mut random_int = || Integer::from(Integer::random_bits(500, &mut rng));

        for _ in 0..10 {
            let n = random_int();
            let res = quartic_aks(&n);
            let ans = n.is_probably_prime(10) != IsPrime::No;
            assert_eq!(ans, res, "Failed on test case {}", n);
        }
    }
}
