//! Prints one line per graph of a planar_code stream (stdin): index, face size multiset, degree
//! multiset, canonical code (hex). Used to identify survivors with known contact graphs.

use std::io::BufReader;
use tammes15::graph::{canon, Faces};
use tammes15::pcode::{Reader, Rot};

fn main() {
    let stdin = std::io::stdin();
    let mut rd = Reader::new(BufReader::new(stdin.lock()));
    let mut g = Rot::default();
    let mut fc = Faces::default();
    let mut k = 0;
    while rd.next_into(&mut g).unwrap() {
        Faces::compute(&g, &mut fc);
        let mut fs = [0usize; 8];
        for c in &fc.cyc {
            fs[c.len().min(7)] += 1;
        }
        let mut ds = [0usize; 8];
        for a in &g.adj {
            ds[a.len().min(7)] += 1;
        }
        let c = canon(&g);
        println!(
            "{k} n={} e={} faces3456={:?} deg345={:?} {}",
            g.n,
            fc.ne,
            &fs[3..7],
            &ds[3..6],
            c.iter().map(|b| format!("{:02x}", b)).collect::<String>()
        );
        k += 1;
    }
}
