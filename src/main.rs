use rug::Integer;
use crate::modint::ModRing;
use crate::poly::Poly;
use crate::poly_ring::ModPolyRing;

mod modint;
mod poly;
mod poly_ring;
mod overload_macro;

fn main() {
    let mut rng = rug::rand::RandState::new();
    let mut random_int = || Integer::from(Integer::random_bits(1024, &mut rng));

    let start = std::time::Instant::now();
    for _ in 0..1 {
        let n = random_int();
        let n = n.next_prime();
        let n_ring = ModRing::new(n.clone());

        let mut modulo_coef = (0..1024).map(|_| random_int()).collect::<Vec<_>>();
        modulo_coef.push(Integer::from(1));
        let modulo_coef = modulo_coef.into_iter().map(|x| n_ring.from(x)).collect::<Vec<_>>();
        let modulo = Poly::new(modulo_coef, &n_ring);
        let ring = ModPolyRing::new(modulo.clone());

        let a = n_ring.from(random_int());
        let x_a = Poly::new(vec![a.clone(), n_ring.from_i64(1)], &n_ring);
        let x_a = ring.from(x_a);
        let x_a_pow = x_a.pow(&n);

        let x = Poly::one(&n_ring) << 1;
        let x = ring.from(x);
        let x_pow = x.pow(&n);
        let x_pow_a = &x_pow + &ring.from_bounded(Poly::new(vec![a.clone()], &n_ring));

        assert_eq!(x_a_pow.value, x_pow_a.value);
    }
    println!("{:?}", start.elapsed());
}