//! Contact graph of a numerical spherical code (Sloane's pack.3.N.txt format: 3N coordinates).
//!
//! Usage: contact FILE [TOL_DEG] [-o graph.pc]
//! Prints psi in degrees, the smallest distances (to see the gap between contacts and non-contacts),
//! degrees, face sizes, isolated vertices, and the canonical code of the contact graph without its
//! isolated vertices. Numerical only (floating point), used to identify graphs.

use std::io::Write;
use tammes15::graph::{canon, Faces};
use tammes15::pcode::{write_graph, write_header, Rot};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let txt = std::fs::read_to_string(&args[1]).unwrap();
    let tol_deg: f64 = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(1e-6);
    let out = args.iter().position(|a| a == "-o").map(|i| args[i + 1].clone());
    let v: Vec<f64> = txt.split_whitespace().map(|s| s.parse().unwrap()).collect();
    let n = v.len() / 3;
    let mut p: Vec<[f64; 3]> = (0..n).map(|i| [v[3 * i], v[3 * i + 1], v[3 * i + 2]]).collect();
    for x in p.iter_mut() {
        let r = (x[0] * x[0] + x[1] * x[1] + x[2] * x[2]).sqrt();
        for c in x.iter_mut() {
            *c /= r;
        }
    }
    let dot = |a: &[f64; 3], b: &[f64; 3]| a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
    let mut d = vec![vec![0.0; n]; n];
    let mut all = Vec::new();
    for i in 0..n {
        for j in i + 1..n {
            let t = dot(&p[i], &p[j]).clamp(-1.0, 1.0).acos().to_degrees();
            d[i][j] = t;
            d[j][i] = t;
            all.push(t);
        }
    }
    all.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let psi = all[0];
    println!("n {n} psi_deg {psi:.10}");
    print!("smallest distances (deg):");
    for t in all.iter().take(45) {
        print!(" {:.7}", t);
    }
    println!();
    // contacts
    let mut nb: Vec<Vec<usize>> = vec![Vec::new(); n];
    for i in 0..n {
        for j in 0..n {
            if i != j && d[i][j] <= psi + tol_deg {
                nb[i].push(j);
            }
        }
    }
    let iso: Vec<usize> = (0..n).filter(|&i| nb[i].is_empty()).collect();
    println!("degrees {:?}", nb.iter().map(|x| x.len()).collect::<Vec<_>>());
    println!("isolated {:?}", iso);
    // rotation (counterclockwise seen from outside)
    let keep: Vec<usize> = (0..n).filter(|&i| !nb[i].is_empty()).collect();
    let idx = |i: usize| keep.iter().position(|&k| k == i).unwrap() as u8;
    let mut adj = Vec::new();
    for &i in &keep {
        let a = p[i];
        let e1 = {
            let q = p[nb[i][0]];
            let t = [q[0] - dot(&a, &q) * a[0], q[1] - dot(&a, &q) * a[1], q[2] - dot(&a, &q) * a[2]];
            let r = dot(&t, &t).sqrt();
            [t[0] / r, t[1] / r, t[2] / r]
        };
        let e2 = [a[1] * e1[2] - a[2] * e1[1], a[2] * e1[0] - a[0] * e1[2], a[0] * e1[1] - a[1] * e1[0]];
        let mut l: Vec<(f64, usize)> = nb[i]
            .iter()
            .map(|&j| {
                let q = p[j];
                (dot(&q, &e2).atan2(dot(&q, &e1)), j)
            })
            .collect();
        l.sort_by(|x, y| x.0.partial_cmp(&y.0).unwrap());
        adj.push(l.iter().map(|&(_, j)| idx(j)).collect::<Vec<u8>>());
    }
    let g = Rot { n: keep.len(), adj };
    let mut fc = Faces::default();
    Faces::compute(&g, &mut fc);
    let mut fs: Vec<usize> = fc.cyc.iter().map(|c| c.len()).collect();
    fs.sort();
    println!("edges {} faces {} face sizes {:?}", fc.ne, fc.nf(), fs);
    let c = canon(&g);
    println!("canon {}", c.iter().map(|b| format!("{:02x}", b)).collect::<String>());
    if let Some(o) = out {
        let mut w = std::io::BufWriter::new(std::fs::File::create(o).unwrap());
        write_header(&mut w).unwrap();
        write_graph(&mut w, &g).unwrap();
        w.flush().unwrap();
    }
}
