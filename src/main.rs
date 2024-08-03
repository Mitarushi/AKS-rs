#![feature(trait_alias)]

use clap::{Parser, ValueEnum};
use rug::Integer;

use crate::aks::{aks, quartic_aks};

mod aks;
mod modint;
mod poly;
mod poly_elem_trait;
mod poly_ring;

#[derive(Debug, Clone, ValueEnum)]
enum Algorithm {
    Aks,
    QuarticAks,
}
#[derive(Parser)]
struct Cli {
    #[arg(short, long, required = true)]
    n: Integer,
    #[arg(short, long, default_value = "quartic-aks")]
    algorithm: Algorithm
}

fn main() {
    let args = Cli::parse();
    let n = args.n;

    let start = std::time::Instant::now();
    let is_prime = match args.algorithm {
        Algorithm::Aks => aks(&n),
        Algorithm::QuarticAks => quartic_aks(&n),
    };
    let elapsed = start.elapsed();

    println!("{} is proven to be {}.", n, if is_prime { "prime" } else { "composite" });
    println!("Elapsed: {}.{:03} sec", elapsed.as_secs(), elapsed.subsec_millis());
}
