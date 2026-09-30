//! vmap: check that graph a of file A and graph b of file B are the same planar code.
//! usage: vmap A B < pairs   (stdin lines "a b"); prints "a b SAME" or "a b DIFFERENT";
//! a line with a single index a prints every index of B holding graph a of A.

use std::io::BufRead;
use tverify::graph::read_planar_code;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let ga = read_planar_code(&std::fs::read(&args[1]).expect("file A"));
    let gb = read_planar_code(&std::fs::read(&args[2]).expect("file B"));
    let codes_b: Vec<Vec<u8>> = gb.iter().map(|g| g.to_code()).collect();
    let mut bad = 0;
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let t: Vec<usize> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        if t.len() == 1 {
            let c = ga[t[0]].to_code();
            let hits: Vec<String> = (0..gb.len()).filter(|&j| codes_b[j] == c).map(|j| j.to_string()).collect();
            println!("{} FOUND {}", t[0], hits.join(","));
            continue;
        }
        let same = ga[t[0]].to_code() == codes_b[t[1]];
        if !same {
            bad += 1;
        }
        println!("{} {} {}", t[0], t[1], if same { "SAME" } else { "DIFFERENT" });
    }
    eprintln!("different: {bad}");
}
