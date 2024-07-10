use rug::Integer;
use crate::modint::ModRing;
use crate::poly::Poly;
use crate::poly_ring::{FastDivEnum, ModPolyRing, NearMonomialDiv};

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
    let lgn2 = lgn * lgn;

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
        .filter(|r| {
            let mut x = n_ring.from_i64(1);
            let r = n_ring.from_i64(*r);
            for _ in 0..lgn2 {
                x = x * &r;
                if x.value == 1 {
                    return false;
                }
            }
            true
        }).next().unwrap();

    let phi_r = phi(r);
    let a_limit = ((phi_r as f64).sqrt() * lgn as f64).floor() as i64;

    let poly = Poly::x_power_of(&n_ring, r as usize) - Poly::new(vec![n_ring.from_i64(1)], &n_ring);
    let fast_div = FastDivEnum::NearMonomial(NearMonomialDiv::new(r as usize, n_ring.from_i64(1)));
    let poly_ring = ModPolyRing::from_fast_div(poly, fast_div);

    (1..=a_limit).
        all(
            |a| {
                let x_a = Poly::new(vec![n_ring.from_i64(a), n_ring.from_i64(1)], &n_ring);
                let x_a = poly_ring.from(x_a);
                let x_a_n = x_a.pow(n);

                let x = Poly::x_power_of(&n_ring, 1);
                let x = poly_ring.from(x);
                let x_n_a = &x.pow(n) + &poly_ring.from_bounded(Poly::new(vec![n_ring.from_i64(a)], &n_ring));

                x_a_n == x_n_a
            }
        )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_aks_small() {
        assert!(aks(&Integer::from(998244353)));
        assert!(!aks(&Integer::from(998244353i64 * 1000000007)));
    }

    #[test]
    fn test_aks_large() {
        let mut rng = rug::rand::RandState::new();
        let mut random_int = || Integer::from(Integer::random_bits(512, &mut rng));

        for i in 0..20 {
            let is_prime = i % 2 == 0;
            let mut n = random_int();
            if is_prime {
                n = n.next_prime();
            }
            let is_prime_aks = aks(&n);
            println!("{}: {} {}", i, n, is_prime_aks);
            assert_eq!(is_prime, is_prime_aks, "Failed on test case {}", i);
        }
    }
}