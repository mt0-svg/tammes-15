//! Level-1 filter: reads plantri planar_code on stdin, writes the graphs that survive to a
//! planar_code file, prints statistics on stderr.
//!
//! Usage: plantri -p -f6 13 | tfilter PARAMS [--iso K] [--lp] [--no-cuts] [--no-face] [-o out.pc]
//! With --iso K the input graphs carry K isolated vertices: every choice of K hexagons marked
//! "full" (one isolated vertex each) is tried; the graph survives if one choice survives.
//! A case is killed only by a rigorous argument: degree > 5, face size > 6, FBBT emptiness
//! (outward rounding), or a verified Farkas certificate of the phase-1 LP. Face inequalities
//! read from the parameter file may be numerical (uncertified); the run says so on stderr.

use std::io::{BufReader, BufWriter, Write};
use std::time::Instant;
use tammes15::graph::Faces;
use tammes15::lp::{lp_feasibility, LpResult};
use tammes15::params::Params;
use tammes15::pcode::{write_graph, write_header, Reader, Rot};
use tammes15::system::{fbbt, Fbbt, Opts, Sys};

#[derive(Default)]
struct Stats {
    total: u64,
    rej_deg: u64,
    rej_face: u64,
    rej_nohex: u64,
    k_a: u64,
    k_b: u64,
    k_lp: u64,
    lp_unknown: u64,
    surv: u64,
    cases: u64,
    uncertified: bool,
}

#[derive(PartialEq)]
enum Verdict {
    RejFace,
    KillA,
    KillB,
    KillLp,
    Survive,
}

fn level1(fc: &Faces, p: &Params, opts: Opts, iso: Option<&[bool]>, use_lp: bool, sys: &mut Sys, st: &mut Stats) -> Verdict {
    let maxf = fc.cyc.iter().map(|c| c.len()).max().unwrap();
    let opt_a = Opts { use_face_ineq: false, ..opts };
    if sys.build(fc, p, opt_a, iso).is_err() {
        return Verdict::RejFace;
    }
    if fbbt(sys, 60, 1e-9) == Fbbt::Infeasible {
        return Verdict::KillA;
    }
    if opts.use_face_ineq && maxf >= 5 && (!p.pent.is_empty() || !p.hex.is_empty() || !p.hexf.is_empty()) {
        let (slo, shi) = (sys.lo.clone(), sys.hi.clone());
        sys.build(fc, p, opts, iso).unwrap();
        st.uncertified |= sys.uses_uncertified;
        sys.lo.copy_from_slice(&slo);
        sys.hi.copy_from_slice(&shi);
        if fbbt(sys, 60, 1e-9) == Fbbt::Infeasible {
            return Verdict::KillB;
        }
    }
    if use_lp {
        match lp_feasibility(sys) {
            LpResult::Infeasible(_) => return Verdict::KillLp,
            LpResult::Unknown => st.lp_unknown += 1,
            LpResult::Feasible => {}
        }
    }
    Verdict::Survive
}

/// all k-subsets of 0..n, as index vectors
fn subsets(n: usize, k: usize) -> Vec<Vec<usize>> {
    fn rec(s: usize, n: usize, k: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if cur.len() == k {
            out.push(cur.clone());
            return;
        }
        for i in s..n {
            cur.push(i);
            rec(i + 1, n, k, cur, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    rec(0, n, k, &mut Vec::new(), &mut out);
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: tfilter PARAMS [--iso K] [--lp] [--no-cuts] [--no-face] [-o out.pc]");
        std::process::exit(2);
    }
    let p = Params::load(&args[1]);
    let mut use_lp = false;
    let mut iso_k = 0usize;
    let mut opts = Opts::default();
    let mut out: Option<BufWriter<std::fs::File>> = None;
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--lp" => use_lp = true,
            "--no-cuts" => opts.use_cuts = false,
            "--no-face" => opts.use_face_ineq = false,
            "--iso" => {
                i += 1;
                iso_k = args[i].parse().unwrap();
            }
            "-o" => {
                i += 1;
                let mut w = BufWriter::new(std::fs::File::create(&args[i]).unwrap());
                write_header(&mut w).unwrap();
                out = Some(w);
            }
            a => panic!("unknown argument {a}"),
        }
        i += 1;
    }
    let stdin = std::io::stdin();
    let mut rd = Reader::new(BufReader::with_capacity(1 << 20, stdin.lock()));
    let mut g = Rot::default();
    let mut fc = Faces::default();
    let mut sys = Sys::default();
    let t0 = Instant::now();
    let mut st = Stats::default();
    let mut total_cls = [0u64; 3];
    let mut surv_cls = [0u64; 3];
    while rd.next_into(&mut g).unwrap() {
        st.total += 1;
        if g.adj.iter().any(|a| a.len() > 5) {
            st.rej_deg += 1;
            continue;
        }
        Faces::compute(&g, &mut fc);
        let maxf = fc.cyc.iter().map(|c| c.len()).max().unwrap();
        let cls = if maxf <= 4 { 0 } else if maxf == 5 { 1 } else { 2 };
        total_cls[cls] += 1;
        let tally = |v: &Verdict, st: &mut Stats| match v {
            Verdict::RejFace => st.rej_face += 1,
            Verdict::KillA => st.k_a += 1,
            Verdict::KillB => st.k_b += 1,
            Verdict::KillLp => st.k_lp += 1,
            Verdict::Survive => {}
        };
        let survived = if iso_k == 0 {
            st.cases += 1;
            let v = level1(&fc, &p, opts, None, use_lp, &mut sys, &mut st);
            tally(&v, &mut st);
            v == Verdict::Survive
        } else {
            let hexes: Vec<usize> = (0..fc.nf()).filter(|&f| fc.cyc[f].len() == 6).collect();
            if hexes.len() < iso_k {
                st.rej_nohex += 1;
                false
            } else {
                let mut any = false;
                let mut last = Verdict::KillA;
                for sub in subsets(hexes.len(), iso_k) {
                    let mut mask = vec![false; fc.nf()];
                    for &j in &sub {
                        mask[hexes[j]] = true;
                    }
                    st.cases += 1;
                    let v = level1(&fc, &p, opts, Some(&mask), use_lp, &mut sys, &mut st);
                    if v == Verdict::Survive {
                        any = true;
                        break;
                    }
                    last = v;
                }
                if !any {
                    tally(&last, &mut st);
                }
                any
            }
        };
        if survived {
            st.surv += 1;
            surv_cls[cls] += 1;
            if let Some(w) = out.as_mut() {
                write_graph(w, &g).unwrap();
            }
        }
    }
    if let Some(mut w) = out {
        w.flush().unwrap();
    }
    let dt = t0.elapsed().as_secs_f64();
    eprintln!(
        "total {} rej_deg {} rej_face {} rej_nohex {} killed_a {} killed_b {} killed_lp {} survivors {} (cases {}, lp_unknown {}) time {:.2}s ({:.2} us/graph){}",
        st.total,
        st.rej_deg,
        st.rej_face,
        st.rej_nohex,
        st.k_a,
        st.k_b,
        st.k_lp,
        st.surv,
        st.cases,
        st.lp_unknown,
        dt,
        1e6 * dt / st.total.max(1) as f64,
        if st.uncertified { " [UNCERTIFIED face inequalities used]" } else { "" }
    );
    eprintln!("classes total [triquad, pent, hex] = {:?}  survivors = {:?}", total_cls, surv_cls);
    let _ = std::io::stderr().flush();
}
