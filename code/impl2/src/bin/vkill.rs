//! vkill: independent kill test for plane graphs of the N = 15 class.
//!
//! usage: vkill FILE.pc [--iso K] [--first N] [--skip S] [--only i,j,..] [--nodes N]
//!        [--local] [--pair] [--edge] [--targets data/tie_targets.txt] [--rlocal R]
//!        [--dlo DEG] [--dhi DEG] [--tol T] [--dweight W] [--nomono] [--nonewton]
//!        [--ratio Q] [--quiet] [--allcases] [--shave K] [--maxsec S] [--parambranch] [--incr] [--shaverounds R] [--deadline EPOCH] [--lp 0-3] [--dropfam F1,F2] [--part I/N/DEPTH] [--relsys]
//! (by default the cases of a graph stop at the first case that is not killed)
//! --relsys: only relations of `RelSys` (Lean hypothesis D3): the families PentSplit, HexChain5
//! and HexC4Iso are dropped, and --edge is refused (Edge is not a test of D3).
//!
//! For each graph, every choice of K distinct hexagons holding the free points is a case; the
//! graph is KILLED iff every case is killed. Output: one line per graph
//! "idx verdict ncases nodes seconds faces=[..] cases=..." on stdout, summary on stderr.

use std::io::Write;
use std::time::Instant;
use tverify::consts;
use tverify::glue::{load_targets, GlueOpts};
use tverify::graph::read_planar_code;
use tverify::model::Model;
use tverify::prop::Opts;
use tverify::search::{solve, SearchOpts, Verdict};

fn combos(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut cur = Vec::new();
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
    rec(0, n, k, &mut cur, &mut out);
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut file = String::new();
    let mut iso = 0usize;
    let mut first = usize::MAX;
    let mut skip = 0usize;
    let mut only: Option<Vec<usize>> = None;
    let mut nodes = 30000u64;
    let mut local = false;
    let mut pair = false;
    let mut edge = false;
    let mut targets_path = String::from("../../data/tie_targets.txt");
    let mut rlocal = 1.04e-3;
    let mut dlo = consts::DLO_DEG.to_string();
    let mut dhi = consts::DHI_DEG.to_string();
    let mut tol = 1e-9;
    let mut dweight = 1.0;
    let mut po = Opts::default();
    let mut quiet = false;
    let mut rho_pair = 0.5;
    let mut shave = 0usize;
    let mut maxsec = 0.0f64;
    let mut allcases = false;
    let mut param_branch = false;
    let mut incr = false;
    let mut shave_rounds = 3usize;
    let mut deadline = 0u64;
    let mut lp = 0usize;
    let mut dropfam: Vec<String> = Vec::new();
    let mut part: Option<(usize, usize, usize)> = None;
    let mut relsys = false;
    let mut i = 1;
    while i < args.len() {
        let a = args[i].as_str();
        let mut val = || {
            i += 1;
            args[i].clone()
        };
        match a {
            "--iso" => iso = val().parse().unwrap(),
            "--first" => first = val().parse().unwrap(),
            "--skip" => skip = val().parse().unwrap(),
            "--only" => only = Some(val().split(',').map(|s| s.parse().unwrap()).collect()),
            "--nodes" => nodes = val().parse().unwrap(),
            "--local" => local = true,
            "--pair" => pair = true,
            "--edge" => edge = true,
            "--targets" => targets_path = val(),
            "--rlocal" => rlocal = val().parse().unwrap(),
            "--dlo" => dlo = val(),
            "--dhi" => dhi = val(),
            "--tol" => tol = val().parse().unwrap(),
            "--dweight" => dweight = val().parse().unwrap(),
            "--nomono" => po.mono = false,
            "--nonewton" => po.newton = false,
            "--ratio" => po.ratio = val().parse().unwrap(),
            "--rhopair" => rho_pair = val().parse().unwrap(),
            "--quiet" => quiet = true,
            "--shave" => shave = val().parse().unwrap(),
            "--maxsec" => maxsec = val().parse().unwrap(),
            "--allcases" => allcases = true,
            "--parambranch" => param_branch = true,
            "--incr" => incr = true,
            "--shaverounds" => shave_rounds = val().parse().unwrap(),
            "--deadline" => deadline = val().parse().unwrap(),
            "--lp" => lp = val().parse().unwrap(),
            "--dropfam" => dropfam = val().split(',').map(|s| s.to_string()).collect(),
            "--part" => {
                let t: Vec<usize> = val().split('/').map(|s| s.parse().unwrap()).collect();
                assert!(t.len() == 3 && t[0] < t[1], "--part I/N/DEPTH with I < N");
                part = Some((t[0], t[1], t[2]));
            }
            "--relsys" => relsys = true,
            _ => {
                if a.starts_with("--") {
                    panic!("unknown option {a}");
                }
                file = a.to_string();
            }
        }
        i += 1;
    }
    tverify::mp::selftest();
    if std::env::var("VK_PROF").is_ok() {
        tverify::prop::PROF_ON.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    let p = consts::params(&dlo, &dhi);
    eprintln!("range d in [{:.17e}, {:.17e}] rad, alpha in [{:.17e}, {:.17e}]", p.dlo, p.dhi, p.alo, p.ahi);
    if relsys {
        assert!(!edge, "--edge is not a test of D3 and is refused with --relsys");
        eprintln!("relsys: families {:?} dropped, Edge off", tverify::model::OUTSIDE_RELSYS);
    }
    let glue = if local || pair || edge {
        let targets = if local {
            let t = std::fs::read_to_string(&targets_path).expect("targets file");
            load_targets(&t)
        } else {
            Vec::new()
        };
        Some(GlueOpts { local, pair, edge, r_local: rlocal, targets, rho_pair })
    } else {
        None
    };
    let so = SearchOpts { nodes, tol, dweight, prop: po, glue, shave, maxsec, incr, shave_rounds, lp, part };
    let bytes = std::fs::read(&file).expect("input file");
    let graphs = read_planar_code(&bytes);
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let (mut nk, mut nb, mut nu, mut ng) = (0, 0, 0, 0);
    let mut tot_nodes = 0u64;
    let t_all = Instant::now();
    for (gi, g) in graphs.iter().enumerate() {
        if gi < skip {
            continue;
        }
        if let Some(o) = &only {
            if !o.contains(&gi) {
                continue;
            }
        } else if gi - skip >= first {
            break;
        }
        if deadline > 0 {
            let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs();
            if now >= deadline {
                eprintln!("deadline reached before graph {gi}");
                break;
            }
        }
        if let Err(e) = g.check_class() {
            panic!("graph {gi} is outside the class: {e}");
        }
        let hex: Vec<usize> = (0..g.faces.len()).filter(|&f| g.faces[f].len() == 6).collect();
        let cs = combos(hex.len(), iso);
        let t0 = Instant::now();
        let mut verdict = Verdict::Killed;
        let mut gnodes = 0u64;
        let mut desc = String::new();
        for c in &cs {
            let full: Vec<usize> = c.iter().map(|&k| hex[k]).collect();
            let mut m = Model::new(g, &full, &p);
            if param_branch {
                m.branch_on_parameters();
            }
            if !dropfam.is_empty() {
                m.drop_families(&dropfam);
            }
            if relsys {
                m.restrict_to_relsys();
            }
            let (v, rep) = solve(&m, &so);
            gnodes += rep.nodes;
            if !quiet {
                desc.push_str(&format!(
                    " [{:?} {:?} n={} e={} L={} P={} E={} LP={} done={:.4}]",
                    full, v, rep.nodes, rep.empty, rep.local, rep.pair, rep.edge, rep.lpkill, rep.done
                ));
                if let Some((pi, pn, pd)) = part {
                    // the part runs of a case agree on `seen` when they are all KILLED
                    desc.push_str(&format!(
                        " [part {pi}/{pn} depth {pd} seen={} kept={} skipped={:.4}]",
                        rep.part_seen, rep.part_kept, rep.skipped
                    ));
                }
            }
            match v {
                Verdict::Killed => {}
                Verdict::Budget => {
                    if verdict == Verdict::Killed {
                        verdict = Verdict::Budget
                    }
                }
                Verdict::Unresolved => verdict = Verdict::Unresolved,
            }
            // the graph survives as soon as one case does
            if verdict != Verdict::Killed && !allcases {
                break;
            }
        }
        let dt = t0.elapsed().as_secs_f64();
        ng += 1;
        tot_nodes += gnodes;
        match verdict {
            Verdict::Killed => nk += 1,
            Verdict::Budget => nb += 1,
            Verdict::Unresolved => nu += 1,
        }
        let vs = match verdict {
            Verdict::Killed => "KILLED",
            Verdict::Budget => "BUDGET",
            Verdict::Unresolved => "UNRESOLVED",
        };
        writeln!(out, "{gi} {vs} {} {gnodes} {dt:.4} faces={:?}{desc}", cs.len(), g.face_counts()).unwrap();
        out.flush().unwrap();
    }
    tverify::prop::prof_report();
    eprintln!(
        "graphs {ng} killed {nk} budget {nb} unresolved {nu} nodes {tot_nodes} time {:.2} s",
        t_all.elapsed().as_secs_f64()
    );
}
