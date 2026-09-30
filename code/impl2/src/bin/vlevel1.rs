//! vlevel1: level-1 filter (linear rows only, src/level1.rs) on a planar_code stream.
//! usage: plantri ... | vlevel1 [--noarea] [--relsys] [--out FILE] [--iso K] [--dlo DEG] [--dhi DEG] ; survivors are written to FILE
//! (planar code with header), counts on stderr.
//! --relsys (the same as --noarea): only rows implied by `RelSys` (Lean hypothesis D3), without the
//! Girard rows; the summary line then ends with "rows relsys".

use std::io::{Read, Write};
use std::time::Instant;
use tverify::consts;
use tverify::graph::Graph;
use tverify::level1::L1;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut area = true;
    let mut out: Option<String> = None;
    let mut iso = 0usize;
    let mut dlo = consts::DLO_DEG.to_string();
    let mut dhi = consts::DHI_DEG.to_string();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--noarea" | "--relsys" => area = false,
            "--out" => {
                i += 1;
                out = Some(args[i].clone())
            }
            "--iso" => {
                i += 1;
                iso = args[i].parse().unwrap()
            }
            "--dlo" => {
                i += 1;
                dlo = args[i].clone()
            }
            "--dhi" => {
                i += 1;
                dhi = args[i].clone()
            }
            a => panic!("unknown option {a}"),
        }
        i += 1;
    }
    tverify::mp::selftest();
    let p = consts::params(&dlo, &dhi);
    let mut l1 = L1::new(&p);
    l1.area_rows = area;
    let mut w = out.map(|f| {
        let mut w = std::io::BufWriter::new(std::fs::File::create(f).unwrap());
        w.write_all(b">>planar_code<<").unwrap();
        w
    });
    let mut data = Vec::new();
    std::io::stdin().lock().read_to_end(&mut data).unwrap();
    let t0 = Instant::now();
    let mut p0 = 0;
    let hdr = b">>planar_code<<";
    if data.len() >= hdr.len() && &data[..hdr.len()] == hdr {
        p0 = hdr.len();
    }
    let (mut n, mut surv, mut nohex) = (0u64, 0u64, 0u64);
    let mut pos = p0;
    while pos < data.len() {
        let start = pos;
        let nv = data[pos] as usize;
        pos += 1;
        let mut adj = vec![Vec::with_capacity(5); nv];
        for v in 0..nv {
            loop {
                let x = data[pos] as usize;
                pos += 1;
                if x == 0 {
                    break;
                }
                adj[v].push(x - 1);
            }
        }
        let g = Graph::from_adj(adj);
        n += 1;
        // k free points lie alone in k distinct hexagons
        if g.faces.iter().filter(|f| f.len() == 6).count() < iso {
            nohex += 1;
            continue;
        }
        if !l1.kill(&g) {
            surv += 1;
            if let Some(w) = w.as_mut() {
                w.write_all(&data[start..pos]).unwrap();
            }
        }
    }
    let dt = t0.elapsed().as_secs_f64();
    eprintln!(
        "graphs {n} fewer than {iso} hexagons {nohex} survivors {surv} time {dt:.3} s ({:.2} us per graph), passes per graph {:.2}{}",
        dt / n.max(1) as f64 * 1e6,
        l1.passes as f64 / n.max(1) as f64,
        if area { "" } else { " rows relsys" }
    );
}
