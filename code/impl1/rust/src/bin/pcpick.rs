//! Copies the graphs with the given indices (0-based, one per line in IDXFILE, first field) from a
//! planar_code stream (stdin) to OUT, in input order.
//! Usage: pcpick IDXFILE OUT.pc < in.pc

use std::collections::HashSet;
use std::io::{BufReader, BufWriter, Write};
use tammes15::pcode::{write_graph, write_header, Reader, Rot};

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let want: HashSet<u64> = std::fs::read_to_string(&a[1])
        .expect("usage: pcpick IDXFILE OUT.pc")
        .lines()
        .filter_map(|l| l.split_whitespace().next().and_then(|t| t.parse().ok()))
        .collect();
    let mut w = BufWriter::new(std::fs::File::create(&a[2]).unwrap());
    write_header(&mut w).unwrap();
    let stdin = std::io::stdin();
    let mut rd = Reader::new(BufReader::with_capacity(1 << 20, stdin.lock()));
    let mut g = Rot::default();
    let (mut i, mut n) = (0u64, 0usize);
    while rd.next_into(&mut g).unwrap() {
        if want.contains(&i) {
            write_graph(&mut w, &g).unwrap();
            n += 1;
        }
        i += 1;
    }
    w.flush().unwrap();
    eprintln!("{n} of {} requested graphs written ({i} read)", want.len());
}
