#![feature(trait_alias)]

use rug::Integer;

use crate::aks::aks;

mod aks;
mod modint;
mod poly;
mod poly_elem_trait;
mod poly_ring;

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
