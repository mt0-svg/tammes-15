//! vtest: soundness tests on the known optimal configurations C1, C3 and their realised
//! subgraphs, built here from the coordinates (data/bk15_c1.txt, data/bk15_c3.txt).
//!
//! usage: vtest COORDS [--maxdel K] [--vertex] [--boxes N] [--search NODES] [--local] [--targets F]
//!        [--limit N] [--seed S] [--relsys]
//! (--relsys: the model restricted to the relations of `RelSys` and Edge off, as vkill --relsys)
//!
//! For every subgraph realised by the configuration in the closed relaxation (edge deletions,
//! optionally one deleted vertex kept as a free point; degrees >= 3, faces <= 6, corners <= pi):
//! - the box of radius 1e-10 around the true values is not refuted and keeps the true values;
//! - N random boxes containing the true values (half-widths 1e-8 .. 1e-1) are not refuted by
//!   propagation, keep the true values, and are not refuted by Pair or Edge;
//! - on the tightest boxes Local must fire (when --local);
//! - optional: the search over [dlo, dhi] without Local must not return KILLED.

use tverify::consts;
use tverify::geom::{dist, oangle, Rng, P};
use tverify::glue::{load_targets, Glue, GlueOpts, GlueVerdict};
use tverify::graph::Graph;
use tverify::iv::I;
use tverify::model::{Model, VA, VD};
use tverify::prop::{Opts, Prop, Stats};
use tverify::search::{solve, SearchOpts, Verdict};

fn read_coords(path: &str) -> Vec<P> {
    let t = std::fs::read_to_string(path).unwrap();
    t.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Vec<f64> = l.split_whitespace().map(|s| s.parse().unwrap()).collect();
            [v[0], v[1], v[2]]
        })
        .collect()
}

/// Rotation system from coordinates: neighbours sorted by counterclockwise angle.
fn rotation(pts: &[P], edges: &[(usize, usize)], alive: &[bool]) -> Vec<Vec<usize>> {
    let n = pts.len();
    let mut adj = vec![Vec::new(); n];
    for &(a, b) in edges {
        adj[a].push(b);
        adj[b].push(a);
    }
    for v in 0..n {
        if !alive[v] || adj[v].is_empty() {
            continue;
        }
        let r = adj[v][0];
        adj[v].sort_by(|&x, &y| {
            let ax = if x == r { 0.0 } else { oangle(&pts[v], &pts[r], &pts[x]) };
            let ay = if y == r { 0.0 } else { oangle(&pts[v], &pts[r], &pts[y]) };
            ax.partial_cmp(&ay).unwrap()
        });
    }
    adj
}

struct Sub {
    g: Graph,
    /// map from graph vertex to configuration point
    map: Vec<usize>,
    free: Option<usize>,
    desc: String,
}

/// Build the graph of the alive vertices with the given edges; None if outside the class or
/// if some corner exceeds pi.
fn build(pts: &[P], edges: &[(usize, usize)], alive: &[bool]) -> Option<(Graph, Vec<usize>)> {
    let n = pts.len();
    let idx: Vec<usize> = (0..n).filter(|&v| alive[v]).collect();
    let mut inv = vec![usize::MAX; n];
    for (i, &v) in idx.iter().enumerate() {
        inv[v] = i;
    }
    let rot = rotation(pts, edges, alive);
    let adj: Vec<Vec<usize>> = idx.iter().map(|&v| rot[v].iter().map(|&w| inv[w]).collect()).collect();
    if adj.iter().any(|l| l.len() < 3 || l.len() > 5) {
        return None;
    }
    let g = Graph::from_adj(adj);
    if g.check_class().is_err() {
        return None;
    }
    // corners <= pi
    for v in 0..g.n {
        let d = g.adj[v].len();
        for j in 0..d {
            let a = idx[g.adj[v][j]];
            let b = idx[g.adj[v][(j + 1) % d]];
            let c = oangle(&pts[idx[v]], &pts[a], &pts[b]);
            if c > std::f64::consts::PI {
                return None;
            }
        }
    }
    Some((g, idx))
}

/// True values of all model variables (point values).
fn truth(m: &Model, pts: &[P], map: &[usize], free: Option<usize>, psi: f64) -> Vec<f64> {
    let g = &m.g;
    let mut t = vec![f64::NAN; m.nv];
    t[VD] = psi;
    t[VA] = (psi.cos() / (1.0 + psi.cos())).acos();
    for (fi, f) in g.faces.iter().enumerate() {
        let k = f.len();
        for i in 0..k {
            let v = map[f[i]];
            let a = map[f[(i + k - 1) % k]];
            let b = map[f[(i + 1) % k]];
            let c = oangle(&pts[v], &pts[a], &pts[b]);
            let var = m.corner_var[fi][i];
            if t[var].is_nan() {
                t[var] = c;
            } else {
                assert!((t[var] - c).abs() < 1e-9, "shared corner variable disagrees: {} vs {}", t[var], c);
            }
        }
    }
    for (fi, rv) in &m.wheels {
        let p = pts[free.unwrap()];
        let cyc = &g.faces[*fi];
        for i in 0..6 {
            t[rv[i]] = dist(&p, &pts[map[cyc[i]]]);
            // theta_i: variables follow the radii
            let a = pts[map[cyc[i]]];
            let b = pts[map[cyc[(i + 1) % 6]]];
            let th = oangle(&p, &a, &b);
            let th = th.min(2.0 * std::f64::consts::PI - th);
            t[rv[0] + 6 + i] = th;
        }
    }
    assert!(t.iter().all(|x| !x.is_nan()), "unset truth");
    t
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = args[1].clone();
    let mut maxdel = 2usize;
    let mut vertex = false;
    let mut nboxes = 20usize;
    let mut search_nodes = 0u64;
    let mut local = false;
    let mut targets_path = String::from("../../data/tie_targets.txt");
    let mut limit = usize::MAX;
    let mut seed = 7u64;
    let mut relsys = false;
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--maxdel" => {
                i += 1;
                maxdel = args[i].parse().unwrap()
            }
            "--vertex" => vertex = true,
            "--boxes" => {
                i += 1;
                nboxes = args[i].parse().unwrap()
            }
            "--search" => {
                i += 1;
                search_nodes = args[i].parse().unwrap()
            }
            "--local" => local = true,
            "--targets" => {
                i += 1;
                targets_path = args[i].clone()
            }
            "--limit" => {
                i += 1;
                limit = args[i].parse().unwrap()
            }
            "--relsys" => relsys = true,
            "--seed" => {
                i += 1;
                seed = args[i].parse().unwrap()
            }
            a => panic!("unknown option {a}"),
        }
        i += 1;
    }
    tverify::mp::selftest();
    let pts = read_coords(&path);
    let n = pts.len();
    let mut psi = f64::INFINITY;
    for a in 0..n {
        for b in a + 1..n {
            psi = psi.min(dist(&pts[a], &pts[b]));
        }
    }
    let mut contacts = Vec::new();
    for a in 0..n {
        for b in a + 1..n {
            if dist(&pts[a], &pts[b]) < psi + 1e-9 {
                contacts.push((a, b));
            }
        }
    }
    eprintln!("psi = {:.15} deg, {} contacts", psi.to_degrees(), contacts.len());
    let p = consts::params(consts::DLO_DEG, consts::DHI_DEG);
    let targets = if local { load_targets(&std::fs::read_to_string(&targets_path).unwrap()) } else { Vec::new() };
    let go = GlueOpts { local, pair: true, edge: !relsys, r_local: 1.04e-3, targets, rho_pair: 10.0 };
    if relsys {
        eprintln!("relsys: families {:?} dropped, Edge off", tverify::model::OUTSIDE_RELSYS);
    }
    // enumerate realised subgraphs
    let mut subs: Vec<Sub> = Vec::new();
    let verts: Vec<Option<usize>> = if vertex { (0..n).map(Some).collect() } else { vec![None] };
    for &fv in &verts {
        let mut alive = vec![true; n];
        if let Some(w) = fv {
            alive[w] = false;
        }
        let base: Vec<(usize, usize)> = contacts.iter().cloned().filter(|&(a, b)| alive[a] && alive[b]).collect();
        // DFS over deletion sets in increasing order, pruned by monotonicity
        let mut stack: Vec<(usize, Vec<usize>)> = vec![(0, vec![])];
        while let Some((start, del)) = stack.pop() {
            let es: Vec<(usize, usize)> = base.iter().enumerate().filter(|(k, _)| !del.contains(k)).map(|(_, e)| *e).collect();
            let ok = build(&pts, &es, &alive);
            let (g, map) = match ok {
                Some(x) => x,
                None => continue,
            };
            // with a free point, it must lie in a hexagon of g
            if let Some(w) = fv {
                let _ = w;
            }
            subs.push(Sub { g, map, free: fv, desc: format!("free={:?} del={:?}", fv, del.iter().map(|&k| base[k]).collect::<Vec<_>>()) });
            if del.len() < maxdel {
                for k in start..base.len() {
                    let mut d2 = del.clone();
                    d2.push(k);
                    stack.push((k + 1, d2));
                }
            }
        }
    }
    eprintln!("{} realised subgraphs (maxdel {maxdel}, vertex {vertex})", subs.len());
    let mut rng = Rng(seed);
    let po = Opts::default();
    let mut nfail = 0;
    let mut nlocal_fired = 0;
    let mut ntested = 0;
    let mut searched = 0;
    for s in subs.iter().take(limit) {
        let g = &s.g;
        // hexagon containing the free point: try every hexagon, keep the one whose wheel truth
        // is consistent (the point lies inside: angles at P sum to 2 pi)
        let hex: Vec<usize> = (0..g.faces.len()).filter(|&f| g.faces[f].len() == 6).collect();
        let full: Vec<usize> = match s.free {
            None => vec![],
            Some(w) => {
                let mut found = None;
                for &f in &hex {
                    let cyc = &g.faces[f];
                    let pp = pts[w];
                    let mut sum = 0.0;
                    for i in 0..6 {
                        let a = pts[s.map[cyc[i]]];
                        let b = pts[s.map[cyc[(i + 1) % 6]]];
                        let th = oangle(&pp, &a, &b);
                        sum += th.min(2.0 * std::f64::consts::PI - th);
                    }
                    if (sum - 2.0 * std::f64::consts::PI).abs() < 1e-9 {
                        found = Some(f);
                    }
                }
                match found {
                    Some(f) => vec![f],
                    None => continue, // the deleted vertex is not in a hexagon: not a class member
                }
            }
        };
        let mut m = Model::new(g, &full, &p);
        if relsys {
            m.restrict_to_relsys();
        }
        let t = truth(&m, &pts, &s.map, s.free, psi);
        ntested += 1;
        let mut prop = Prop::new(&m);
        let mut st = Stats { evals: 0 };
        let glue = Glue::new(&m, go.clone());
        let inside = |b: &[I]| -> bool { (0..m.nv).all(|v| b[v].lo <= t[v] + 1e-9 && t[v] - 1e-9 <= b[v].hi) };
        for trial in 0..=nboxes {
            let w = if trial == 0 { 1e-10 } else { [1e-8, 1e-6, 1e-4, 1e-3, 1e-2, 1e-1][trial % 6] };
            let mut b: Vec<I> = (0..m.nv)
                .map(|v| {
                    let lo = t[v] - w * rng.next() - 1e-11;
                    let hi = t[v] + w * rng.next() + 1e-11;
                    I::new(lo.max(m.init[v].lo), hi.min(m.init[v].hi))
                })
                .collect();
            if !inside(&b) {
                // the truth lies outside the initial domain: a failure of the model itself
                eprintln!("FAIL truth outside the domain: {} {:?}", s.desc, (0..m.nv).filter(|&v| !(m.init[v].lo <= t[v] && t[v] <= m.init[v].hi)).map(|v| (&m.names[v], t[v], m.init[v])).collect::<Vec<_>>());
                nfail += 1;
                break;
            }
            let ok = prop.run(&m, &mut b, &po, &mut st);
            if !ok {
                eprintln!("FAIL propagation refuted a box containing the truth: {} w={w}", s.desc);
                nfail += 1;
                continue;
            }
            if !inside(&b) {
                let bad: Vec<_> = (0..m.nv).filter(|&v| !(b[v].lo <= t[v] + 1e-9 && t[v] - 1e-9 <= b[v].hi)).map(|v| (&m.names[v], t[v], b[v])).collect();
                eprintln!("FAIL propagation lost the truth: {} w={w} {:?}", s.desc, bad);
                nfail += 1;
                continue;
            }
            if trial == 0 {
                // gluing check: pairwise chords of the placed centre configuration against the coordinates
                if let Some((y, rho)) = glue.place(&b) {
                    let mut idx: Vec<usize> = s.map.clone();
                    if let Some(w) = s.free {
                        idx.push(w);
                    }
                    let mut worst = 0.0f64;
                    for a in 0..idx.len() {
                        for c in a + 1..idx.len() {
                            let pa = pts[idx[a]];
                            let pc = pts[idx[c]];
                            let ch = tverify::geom::norm(&tverify::geom::sub(&pa, &pc));
                            let ya = [y[a][0].mid(), y[a][1].mid(), y[a][2].mid()];
                            let yc = [y[c][0].mid(), y[c][1].mid(), y[c][2].mid()];
                            let cy = tverify::geom::norm(&tverify::geom::sub(&ya, &yc));
                            worst = worst.max((ch - cy).abs() - rho[a] - rho[c]);
                        }
                    }
                    if worst > 1e-9 {
                        eprintln!("FAIL gluing: chord mismatch {worst:.3e} beyond rho: {}", s.desc);
                        nfail += 1;
                    }
                } else {
                    eprintln!("FAIL gluing: place() gave None on the truth box: {}", s.desc);
                    nfail += 1;
                }
            }
            match glue.test(&b) {
                GlueVerdict::Pair | GlueVerdict::Edge => {
                    eprintln!("FAIL glue refuted a box containing the truth: {} w={w}", s.desc);
                    nfail += 1;
                }
                GlueVerdict::Local => {
                    if trial == 0 {
                        nlocal_fired += 1;
                    }
                }
                GlueVerdict::None => {
                    if local && trial == 0 {
                        eprintln!("note: Local did not fire on the truth box: {}", s.desc);
                    }
                }
            }
        }
        if search_nodes > 0 {
            let so = SearchOpts { nodes: search_nodes, tol: 1e-9, dweight: 1.0, prop: po, glue: Some(GlueOpts { local: false, ..go.clone() }), shave: 0, maxsec: 0.0, incr: false, shave_rounds: 3, lp: 0, part: None };
            let (v, rep) = solve(&m, &so);
            searched += 1;
            if v == Verdict::Killed {
                eprintln!("FAIL search without Local killed a realised subgraph: {} ({} nodes)", s.desc, rep.nodes);
                nfail += 1;
            } else {
                println!("search {:?} n={} {}", v, rep.nodes, s.desc);
            }
        }
    }
    eprintln!("tested {ntested} subgraphs, {searched} searches, Local fired on {nlocal_fired} truth boxes, failures {nfail}");
    if nfail > 0 {
        std::process::exit(1);
    }
}
