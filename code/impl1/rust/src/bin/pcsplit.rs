//! Splits a planar_code stream (stdin) by graph index: graph i goes to part i mod M.
//! Usage: pcsplit M PREFIX   writes PREFIX_0.pc .. PREFIX_{M-1}.pc
//! Part r keeps the original order; graph j of part r is graph r + j M of the input.

use std::io::{BufReader, BufWriter, Write};
use tammes15::pcode::{write_graph, write_header, Reader, Rot};

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let m: usize = a[1].parse().expect("usage: pcsplit M PREFIX");
    let mut outs: Vec<BufWriter<std::fs::File>> = (0..m)
        .map(|r| {
            let mut w = BufWriter::new(std::fs::File::create(format!("{}_{r}.pc", a[2])).unwrap());
            write_header(&mut w).unwrap();
            w
        })
        .collect();
    let stdin = std::io::stdin();
    let mut rd = Reader::new(BufReader::with_capacity(1 << 20, stdin.lock()));
    let mut g = Rot::default();
    let mut i = 0usize;
    while rd.next_into(&mut g).unwrap() {
        write_graph(&mut outs[i % m], &g).unwrap();
        i += 1;
    }
    for w in outs.iter_mut() {
        w.flush().unwrap();
    }
    eprintln!("{i} graphs split into {m} parts");
}
