use rug::Integer;
use crate::modint::ModRing;
use crate::poly::Poly;
use crate::poly_ring::{FastDivEnum, ModPolyRing, NearMonomialDiv};
use crate::prime::aks;

mod modint;
mod poly;
mod poly_ring;
mod overload_macro;
mod prime;

fn main() {
    let mut rng = rug::rand::RandState::new();
    let mut random_int = || Integer::from(Integer::random_bits(100, &mut rng));

    for _ in 0..10 {
        let n = random_int();
        let n = n.next_prime();

        let start = std::time::Instant::now();
        println!("{} is prime: {}", n, aks(&n));
        println!("time: {:?}", start.elapsed());
    }
}
