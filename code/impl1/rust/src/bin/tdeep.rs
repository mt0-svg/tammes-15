//! Level 2 driver: interval branch-and-prune (deep.rs) on every graph of a planar_code stream.
//!
//! Usage: tdeep PARAMS [options] < graphs.pc
//!   --iso K            K isolated vertices (every choice of K full hexagons is tried)
//!   --no-face          no face inequalities from PARAMS (rigorous mode); also --no-cuts
//!   --no-wheel         no wheel variables for full hexagons
//!   --nobranchr        never split the wheel variables (they are only contracted)
//!   --rweight W        multiply the scaled width of the wheel variables by W in the split
//!                      choice (W = 1e-3: corners first, free point last)
//!   --shave K          3B shaving: refute and drop slices of 1/K of every variable at both ends
//!   --pisplit E        split a corner reaching within E/2 of pi at pi - E (rad)
//!   --dsplit DEG       split d first while its width exceeds DEG (d slicing inside the search)
//!   --xstar            inter-face kill test: vertex pairs around a common vertex, sharing no
//!                      face, must be at distance >= d (xstar.rs)
//!   --xlp              LP kill test on the mean-value linear relaxation (xlin.rs) at every node
//!                      of depth >= --xlpdepth D (default 0); --xobbt 1: also LP bounds on d,
//!                      --xobbt 2: LP bounds on every variable (weak-duality certified)
//!   --dlo DEG, --dhi DEG  replace the ends of the d range
//!   --nodes N          node budget per case; --stopunres N: stop a case after N unresolved boxes
//!   --tol X            width below which a box is reported unresolved (rad)
//!   --absscale, --dweight W, --shrink F, --rounds R   search and propagation tuning
//!   --replay           re-check every killed case by replaying its tree
//!   --trig B           transcendental backend: rig (default, rigorous, rtrig.rs), libm (glibc
//!                      plus TR_ULPS ulps, assumption), mpfr (correctly rounded, slow)
//!   --local FILE       tie-window discard "Local" (local.rs, Theorem 4.1 of Section 4): FILE =
//!                      data/tie_targets.txt; tried on boxes with d_lo <= --localmax DEG (default:
//!                      all boxes; sound for every d); --localr R (default and maximum 1.04e-3, the radius of Theorem 4.1)
//!   --pair             refutation "Pair" (local.rs): two points of the glued configuration, not
//!                      joined by an edge, provably closer than d
//!   --close            refutation "Close" (local.rs): an edge of the glued configuration (or a
//!                      wheel radius) provably of the wrong length (loop closure of the gluing)
//!   --cert DIR         write the tree of every killed case to DIR/g<idx>_c<choice>.cert
//!   --certfile FILE    append the trees of all killed cases to FILE ("G idx choice", tokens, "E")
//!   --replayfile FILE  no search: replay the trees of FILE (same options as the recording run;
//!                      any --trig); verdict VERIFIED, REPLAY_FAILED or NO_CERTIFICATE per graph
//!   --dump FILE        append the unresolved (U) and open (O) boxes of surviving cases to FILE,
//!                      one line per box: graph index, choice, U/O, then lo hi of every variable
//!   --every M          only the graphs whose index is a multiple of M (sampling)
//!   --skip FILE        skip the graphs whose indices (first field of each line) are in FILE
//!   --only IDX, --from IDX (skip the graphs before index IDX), --verbose, -o unresolved.pc
//! With --iso K the graphs carry K isolated vertices: every choice of K hexagons marked full is
//! tried; the graph is killed only if every choice is killed.
//! stdout, one line per graph: index, canonical code (hex), faces [f3 f4 f5 f6], verdict
//! (KILLED / UNRESOLVED / BUDGET), nodes, seconds, and for unresolved graphs the hull of d over the
//! unresolved boxes (degrees, and offset from d_lo in radians), and when the search stopped early
//! (node budget, or --stopunres unresolved boxes) the number and d-hull of the open boxes.
//! A graph is killed only by interval contractors (outward rounding; libm assumption of ivt.rs).
//! Face inequalities from the parameter file are numerical (uncertified) unless --no-face.

use std::io::{BufReader, BufWriter, Write};
use std::time::Instant;
use tammes15::deep::{read_drange, Cfg, Outcome, Prob, Reason};
use tammes15::iv;
use tammes15::ivt::Iv;
use tammes15::graph::{canon, Faces};
use tammes15::params::Params;
use tammes15::pcode::{write_graph, write_header, Reader, Rot};

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
        eprintln!("usage: tdeep PARAMS [--iso K] [--no-face] [--no-cuts] [--no-wheel] [--tol X] [--nodes N] [--dweight W] [--replay] [--only IDX] [--stopunres N] [--dlo DEG] [--dhi DEG] [--verbose] [-o out.pc]");
        std::process::exit(2);
    }
    let p = Params::load(&args[1]);
    let (dlo, dhi) = read_drange(&args[1]);
    let mut cfg = Cfg::default();
    let mut iso_k = 0usize;
    let mut replay = false;
    let mut cert_dir: Option<String> = None;
    let mut cert_file: Option<BufWriter<std::fs::File>> = None;
    let mut replay_map: Option<std::collections::HashMap<(u64, usize), Vec<tammes15::deep::Tok>>> = None;
    let mut verbose = false;
    let mut dump: Option<String> = None;
    let mut only: Option<u64> = None;
    let mut from = 0u64;
    let mut skip: std::collections::HashSet<u64> = std::collections::HashSet::new();
    let mut every = 1u64;
    let mut dlo_override: Option<f64> = None;
    let mut dhi_override: Option<f64> = None;
    let mut out: Option<BufWriter<std::fs::File>> = None;
    let mut local_file: Option<String> = None;
    let mut local_r = 1.04e-3f64;
    let mut local_dmax = f64::INFINITY;
    let mut pair = false;
    let mut close = false;
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--no-face" => cfg.use_face_ineq = false,
            "--no-cuts" => cfg.use_cuts = false,
            "--no-wheel" => cfg.use_wheel = false,
            "--nobranchr" => cfg.branch_wheel = false,
            "--rweight" => {
                i += 1;
                cfg.rweight = args[i].parse().unwrap()
            }
            "--xlp" => cfg.xlp = true,
            "--xstar" => cfg.xstar = true,
            "--dsplit" => {
                i += 1;
                cfg.dsplit = args[i].parse::<f64>().unwrap().to_radians();
            }
            "--xobbt" => {
                i += 1;
                cfg.xobbt = args[i].parse().unwrap();
            }
            "--xlpdepth" => {
                i += 1;
                cfg.xlp_depth = args[i].parse().unwrap();
            }
            "--replay" => replay = true,
            "--local" => {
                i += 1;
                local_file = Some(args[i].clone());
            }
            "--localr" => {
                i += 1;
                local_r = args[i].parse().unwrap();
                assert!(local_r <= 1.04e-3, "the radius of Theorem 4.1 is 1.04e-3");
            }
            "--localmax" => {
                i += 1;
                local_dmax = iv::parse_up(&args[i]).to_radians().next_up();
            }
            "--pair" => pair = true,
            "--shave" => {
                i += 1;
                cfg.shave = args[i].parse().unwrap();
            }
            "--pisplit" => {
                i += 1;
                cfg.pisplit = args[i].parse().unwrap();
            }
            "--close" => close = true,
            "--trig" => {
                i += 1;
                tammes15::ivt::set_trig(match args[i].as_str() {
                    "libm" => tammes15::ivt::Trig::Libm,
                    "rig" => tammes15::ivt::Trig::Rig,
                    "mpfr" => tammes15::ivt::Trig::Mpfr,
                    s => panic!("--trig libm|rig|mpfr, got {s}"),
                });
            }
            "--cert" => {
                i += 1;
                cert_dir = Some(args[i].clone());
                std::fs::create_dir_all(&args[i]).unwrap();
            }
            "--certfile" => {
                i += 1;
                let f = std::fs::OpenOptions::new().create(true).append(true).open(&args[i]).unwrap();
                cert_file = Some(BufWriter::new(f));
            }
            "--replayfile" => {
                i += 1;
                let s = std::fs::read_to_string(&args[i]).unwrap();
                let mut map = std::collections::HashMap::new();
                let mut cur: Option<((u64, usize), String)> = None;
                for l in s.lines() {
                    if let Some(h) = l.strip_prefix("G ") {
                        let w: Vec<&str> = h.split_whitespace().collect();
                        cur = Some(((w[0].parse().unwrap(), w[1].parse().unwrap()), String::new()));
                    } else if l == "E" {
                        let (k, t) = cur.take().expect("E without G");
                        let toks = tammes15::deep::parse_cert(&t).unwrap_or_else(|e| panic!("graph {k:?}: {e}"));
                        // a graph interrupted after some of its choices and redone on resume has
                        // two certificates for those choices: both are valid, the last one is kept
                        map.insert(k, toks);
                    } else {
                        let c = cur.as_mut().expect("token outside G ... E");
                        c.1.push_str(l);
                        c.1.push('\n');
                    }
                }
                replay_map = Some(map);
            }
            "--absscale" => cfg.rel_scale = false,
            "--shrink" => {
                i += 1;
                cfg.shrink = args[i].parse().unwrap();
            }
            "--rounds" => {
                i += 1;
                cfg.max_rounds = args[i].parse().unwrap();
            }
            "--verbose" => verbose = true,
            "--dump" => {
                i += 1;
                dump = Some(args[i].clone());
            }
            "--every" => {
                i += 1;
                every = args[i].parse().unwrap();
            }
            "--skip" => {
                i += 1;
                let s = std::fs::read_to_string(&args[i]).unwrap();
                skip = s.lines().filter_map(|l| l.split_whitespace().next()).map(|w| w.parse::<u64>().unwrap()).collect();
            }
            "--from" => {
                i += 1;
                from = args[i].parse::<u64>().unwrap();
            }
            "--only" => {
                i += 1;
                only = Some(args[i].parse::<u64>().unwrap());
            }
            "--dlo" => {
                i += 1;
                dlo_override = Some(iv::parse_dn(&args[i]).to_radians().next_down());
            }
            "--dhi" => {
                i += 1;
                dhi_override = Some(iv::parse_up(&args[i]).to_radians().next_up());
            }
            "--stopunres" => {
                i += 1;
                cfg.stop_unres = args[i].parse().unwrap();
            }
            "--iso" => {
                i += 1;
                iso_k = args[i].parse().unwrap();
            }
            "--tol" => {
                i += 1;
                cfg.tol = args[i].parse().unwrap();
            }
            "--nodes" => {
                i += 1;
                cfg.max_nodes = args[i].parse().unwrap();
            }
            "--dweight" => {
                i += 1;
                cfg.dweight = args[i].parse().unwrap();
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
    cfg.record = replay || cert_dir.is_some() || cert_file.is_some();
    let (mut verified, mut ver_fail, mut ver_missing) = (0u64, 0u64, 0u64);
    cfg.dref = Some(dhi - dlo);
    let dlo = dlo_override.unwrap_or(dlo);
    let dhi = dhi_override.unwrap_or(dhi);
    let targets = local_file.as_ref().map(|f| std::sync::Arc::new(tammes15::local::Targets::load(f)));
    let stdin = std::io::stdin();
    let mut rd = Reader::new(BufReader::new(stdin.lock()));
    let mut g = Rot::default();
    let mut fc = Faces::default();
    let t0 = Instant::now();
    let (mut total, mut killed, mut unres, mut budget) = (0u64, 0u64, 0u64, 0u64);
    let mut kills = [0u64; tammes15::deep::NKINDS];
    let mut nodes_all = 0u64;
    let mut uncert = false;
    let mut replay_fail = 0u64;
    let stdout = std::io::stdout();
    let mut so = stdout.lock();
    while rd.next_into(&mut g).unwrap() {
        let idx = total;
        total += 1;
        if only.map_or(false, |k| k != idx) || idx < from || skip.contains(&idx) || idx % every != 0 {
            continue;
        }
        let tg = Instant::now();
        Faces::compute(&g, &mut fc);
        let mut fs = [0usize; 8];
        for c in &fc.cyc {
            fs[c.len().min(7)] += 1;
        }
        let code: String = canon(&g).iter().map(|b| format!("{:02x}", b)).collect();
        let hexes: Vec<usize> = (0..fc.nf()).filter(|&f| fc.cyc[f].len() == 6).collect();
        let choices: Vec<Option<Vec<bool>>> = if iso_k == 0 {
            vec![None]
        } else {
            subsets(hexes.len(), iso_k)
                .into_iter()
                .map(|s| {
                    let mut m = vec![false; fc.nf()];
                    for j in s {
                        m[hexes[j]] = true;
                    }
                    Some(m)
                })
                .collect()
        };
        let mut all_killed = true;
        let mut any_unres = false;
        let mut nodes = 0u64;
        let mut done_min = 1.0f64;
        let mut dh: Option<Iv> = None;
        let mut dop: Option<Iv> = None;
        let (mut nun, mut nop) = (0u64, 0u64);
        let mut detail = String::new();
        let hull = |h: &mut Option<Iv>, x: Option<Iv>| {
            if let Some(x) = x {
                *h = Some(h.map_or(x, |y| y.hull(x)));
            }
        };
        for (ci, ch) in choices.iter().enumerate() {
            let mut prob = match Prob::new(&fc, &p, dlo, dhi, cfg, ch.as_deref()) {
                Ok(pr) => pr,
                Err(_) => continue, // degree > 5 or face > 6: rejected at level 0
            };
            if targets.is_some() || pair || close {
                prob.set_local(&fc, targets.clone(), local_r, local_dmax, pair);
                prob.local.as_mut().unwrap().close = close;
            }
            uncert |= prob.uses_uncertified;
            if let Some(map) = replay_map.as_ref() {
                // replay mode: re-check the recorded tree of this choice instead of searching
                match map.get(&(idx, ci)) {
                    None => {
                        all_killed = false;
                        detail.push_str(&format!(" choice{ci}=nocert"));
                    }
                    Some(c) => match prob.replay(c) {
                        Ok(leaves) => nodes += leaves as u64,
                        Err(pos) => {
                            all_killed = false;
                            any_unres = true;
                            detail.push_str(&format!(" choice{ci}=failed_at_token_{pos}"));
                        }
                    },
                }
                continue;
            }
            let o: Outcome = prob.solve();
            nodes += o.nodes;
            if !(o.killed && !o.stopped) {
                done_min = done_min.min(o.done);
            }
            for k in 0..tammes15::deep::NKINDS {
                kills[k] += o.kills[k];
            }
            if o.killed && !o.stopped {
                if let Some(dir) = cert_dir.as_ref() {
                    std::fs::write(format!("{dir}/g{idx}_c{ci}.cert"), tammes15::deep::cert_text(&o.cert)).unwrap();
                }
                if let Some(w) = cert_file.as_mut() {
                    write!(w, "G {idx} {ci}\n{}E\n", tammes15::deep::cert_text(&o.cert)).unwrap();
                    w.flush().unwrap(); // a killed run keeps every certificate it reported
                }
                if replay {
                    match prob.replay(&o.cert) {
                        Ok(_) => {}
                        Err(pos) => {
                            replay_fail += 1;
                            eprintln!("graph {idx} choice {ci}: replay failed at token {pos}");
                        }
                    }
                }
            } else {
                all_killed = false;
                any_unres |= o.n_unres > 0;
                nun += o.n_unres;
                nop += o.n_open;
                hull(&mut dh, o.dhull);
                hull(&mut dop, o.dopen);
                if ch.is_some() {
                    let full: Vec<usize> = ch.as_ref().unwrap().iter().enumerate().filter(|(_, &b)| b).map(|(f, _)| f).collect();
                    detail.push_str(&format!(" choice{}={:?}", ci, full));
                }
                if let Some(path) = dump.as_ref() {
                    use std::io::Write as _;
                    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
                    for (k, bx) in o.unres.iter().map(|x| ("U", x)).chain(o.open_boxes.iter().map(|x| ("O", x))) {
                        let s: Vec<String> = bx.iter().map(|x| format!("{:.17e} {:.17e}", x.lo, x.hi)).collect();
                        writeln!(f, "{idx} {ci} {k} {}", s.join(" ")).unwrap();
                    }
                }
                if verbose {
                    for bx in o.unres.iter().take(5) {
                        let wmax = bx.iter().map(|x| x.w()).fold(0.0, f64::max);
                        eprintln!("  graph {idx} choice {ci} unresolved box: d = [{:.12}, {:.12}] deg, max width {wmax:.2e}", bx[prob.di].lo.to_degrees(), bx[prob.di].hi.to_degrees());
                    }
                }
            }
        }
        nodes_all += nodes;
        let dt = tg.elapsed().as_secs_f64();
        let verdict = if replay_map.is_some() {
            if all_killed {
                verified += 1;
                "VERIFIED"
            } else if any_unres {
                ver_fail += 1;
                "REPLAY_FAILED"
            } else {
                ver_missing += 1;
                "NO_CERTIFICATE"
            }
        } else if all_killed {
            killed += 1;
            "KILLED"
        } else if any_unres {
            unres += 1;
            "UNRESOLVED"
        } else {
            budget += 1;
            "BUDGET"
        };
        let mut line = format!("{idx} {code} faces={:?} {verdict} nodes={nodes} t={dt:.3}", &fs[3..7]);
        if let Some(h) = dh {
            line.push_str(&format!(" unres={nun} d=[{:.9},{:.9}]deg (dlo+{:.2e} rad)", h.lo.to_degrees(), h.hi.to_degrees(), h.lo - dlo));
        }
        if let Some(h) = dop {
            line.push_str(&format!(" open={nop} d=[{:.9},{:.9}]deg done={:.3e}", h.lo.to_degrees(), h.hi.to_degrees(), done_min));
        }
        line.push_str(&detail);
        writeln!(so, "{line}").unwrap();
        so.flush().unwrap();
        if !all_killed {
            if let Some(w) = out.as_mut() {
                write_graph(w, &g).unwrap();
            }
        }
    }
    if let Some(mut w) = out {
        w.flush().unwrap();
    }
    if let Some(mut w) = cert_file {
        w.flush().unwrap();
    }
    if replay_map.is_some() {
        eprintln!("replay: verified {verified} failed {ver_fail} missing certificates {ver_missing} (trig {})", tammes15::ivt::trig_name());
    }
    if verbose {
        eprintln!("contractor passes: {}", tammes15::deep::PASSES.load(std::sync::atomic::Ordering::Relaxed));
    }
    let dt = t0.elapsed().as_secs_f64();
    let ks: Vec<String> = (0..tammes15::deep::NKINDS).filter(|&k| kills[k] > 0).map(|k| format!("{}:{}", Reason::KINDS[k], kills[k])).collect();
    eprintln!(
        "d in [{dlo:.17e}, {dhi:.17e}] rad = [{:.10}, {:.10}] deg; total {total} killed {killed} unresolved {unres} budget {budget} nodes {nodes_all} time {dt:.2}s ({:.3} s/graph) leaf kills [{}] trig {}{}{}",
        dlo.to_degrees(),
        dhi.to_degrees(),
        dt / total.max(1) as f64,
        ks.join(" "),
        tammes15::ivt::trig_name(),
        if replay { format!(" replay_failures {replay_fail}") } else { String::new() },
        if uncert { " [UNCERTIFIED face inequalities used]" } else { "" }
    );
}
