//! Helper of the coverage join (code/impl1/coverage_join.sh).
//!
//!   pcrec FILE.pc ...         one line per graph of each file: file name, index, n, number of
//!                             edges, faces of size 3, 4, 5, 6, faces of any other size, maximum
//!                             degree, the record as stored (hex bytes), canonical code (hex,
//!                             graph.rs canon)
//!   pcrec --cut COUNTS DIR < FILE.pc
//!                             cuts FILE.pc into consecutive parts of the sizes listed in COUNTS
//!                             (one per line), written to DIR/<line>.pc with the planar_code header;
//!                             fails unless the sizes add up to the number of graphs of FILE.pc
//!   pcrec --drange PARAMS     the d range tdeep reads from PARAMS (deep.rs read_drange), radians,
//!                             printed as in the summary line of tdeep

use std::io::{BufReader, BufWriter, Write};
use tammes15::graph::{canon, Faces};
use tammes15::pcode::{write_graph, write_header, Reader, Rot};

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("--drange") => {
            let (lo, hi) = tammes15::deep::read_drange(&a[2]);
            println!("d in [{lo:.17e}, {hi:.17e}] rad = [{:.10}, {:.10}] deg", lo.to_degrees(), hi.to_degrees());
        }
        Some("--cut") => {
            let counts: Vec<usize> = std::fs::read_to_string(&a[2])
                .unwrap()
                .lines()
                .map(|l| l.trim().parse().expect("COUNTS: one integer per line"))
                .collect();
            let stdin = std::io::stdin();
            let mut rd = Reader::new(BufReader::with_capacity(1 << 20, stdin.lock()));
            let mut g = Rot::default();
            for (j, &c) in counts.iter().enumerate() {
                let mut w = BufWriter::new(std::fs::File::create(format!("{}/{j}.pc", a[3])).unwrap());
                write_header(&mut w).unwrap();
                for _ in 0..c {
                    assert!(rd.next_into(&mut g).unwrap(), "input ends inside part {j}");
                    write_graph(&mut w, &g).unwrap();
                }
                w.flush().unwrap();
            }
            assert!(!rd.next_into(&mut g).unwrap(), "graphs left after the last part");
        }
        Some(_) => {
            let mut g = Rot::default();
            let mut fc = Faces::default();
            let so = std::io::stdout();
            let mut so = BufWriter::new(so.lock());
            for path in &a[1..] {
                let name = std::path::Path::new(path).file_name().unwrap().to_string_lossy().to_string();
                let f = std::fs::File::open(path).unwrap_or_else(|e| panic!("{path}: {e}"));
                let mut rd = Reader::new(BufReader::with_capacity(1 << 20, f));
                let mut i = 0u64;
                let mut buf = Vec::new();
                while rd.next_into(&mut g).unwrap() {
                    Faces::compute(&g, &mut fc);
                    let mut fs = [0usize; 5];
                    for c in &fc.cyc {
                        fs[if (3..=6).contains(&c.len()) { c.len() - 3 } else { 4 }] += 1;
                    }
                    let maxdeg = g.adj.iter().map(|x| x.len()).max().unwrap_or(0);
                    buf.clear();
                    write_graph(&mut buf, &g).unwrap();
                    writeln!(
                        so,
                        "{name} {i} {} {} {} {} {} {} {} {maxdeg} {} {}",
                        g.n,
                        fc.ne,
                        fs[0],
                        fs[1],
                        fs[2],
                        fs[3],
                        fs[4],
                        hex(&buf),
                        hex(&canon(&g))
                    )
                    .unwrap();
                    i += 1;
                }
            }
        }
        None => {
            eprintln!("usage: pcrec FILE.pc ... | pcrec --cut COUNTS DIR < FILE.pc | pcrec --drange PARAMS");
            std::process::exit(2);
        }
    }
}
