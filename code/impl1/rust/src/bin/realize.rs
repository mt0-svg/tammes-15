//! Which subgraphs of the contact graph of a numerical configuration are realised by the same
//! configuration in the closed relaxation (all face corners <= pi)? Floating point, used to
//! check that level 2 never kills a graph that has a known solution (soundness test).
//!
//! Usage: realize PACKFILE K [--vertex] [-o realised.pc] [--params FILE] [--check PARAMS [--local TARGETS]]
//! With --check and --local, also checks the gluing of local.rs (check_place).
//! With --check, every realised subgraph is tested with level 2 (all optional tests on: star,
//! LP bounds on all variables): the box of half-width max(1e-9, 1000 x contact spread) around its
//! true corner angles, d and
//! wheel radii must not be refuted (prints "true point kept" or "TRUE POINT REFUTED").
//! With --params, every row of the level-1 system of each realised graph is evaluated at the
//! configuration and violated rows are printed (checks the numerical face inequalities).
//! Builds the contact graph as `contact` does (same vertex numbering when there is no isolated
//! vertex), deletes every set of at most K edges (after deleting one vertex with --vertex; the
//! vertex stays in the configuration as an isolated point inside the merged face), keeps the
//! connected graphs with minimum degree >= 3 and faces <= 6, and prints: canonical code, faces,
//! deleted vertex and edges, largest face corner (deg), smallest corner (deg), `realised` when
//! the largest corner is < 180 deg.

use std::collections::HashSet;
use std::io::Write;
use tammes15::graph::{canon, Faces};
use tammes15::pcode::{write_graph, write_header, Rot};
use tammes15::params::Params;
use tammes15::poly::{angle_at, V3};
use tammes15::deep::{read_drange, Cfg, FaceK, Prob};
use tammes15::ivt::Iv;
use tammes15::system::{Opts, Sys};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let txt = std::fs::read_to_string(&args[1]).unwrap();
    let k: usize = args[2].parse().unwrap();
    let with_vertex = args.iter().any(|a| a == "--vertex");
    let out = args.iter().position(|a| a == "-o").map(|i| args[i + 1].clone());
    let params = args.iter().position(|a| a == "--params").map(|i| Params::load(&args[i + 1]));
    let check = args.iter().position(|a| a == "--check").map(|i| {
        let (lo, hi) = read_drange(&args[i + 1]);
        (Params::load(&args[i + 1]), lo, hi)
    });
    let targets = args.iter().position(|a| a == "--local").map(|i| tammes15::local::Targets::load(&args[i + 1]));
    let v: Vec<f64> = txt.split_whitespace().map(|s| s.parse().unwrap()).collect();
    let n = v.len() / 3;
    let mut p: Vec<V3> = (0..n).map(|i| [v[3 * i], v[3 * i + 1], v[3 * i + 2]]).collect();
    for x in p.iter_mut() {
        let r = (x[0] * x[0] + x[1] * x[1] + x[2] * x[2]).sqrt();
        for c in x.iter_mut() {
            *c /= r;
        }
    }
    let dot = |a: &V3, b: &V3| a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
    let mut dm = vec![vec![0.0; n]; n];
    let mut psi = f64::INFINITY;
    for i in 0..n {
        for j in i + 1..n {
            let t = dot(&p[i], &p[j]).clamp(-1.0, 1.0).acos();
            dm[i][j] = t;
            dm[j][i] = t;
            psi = psi.min(t);
        }
    }
    let tol = 1e-8;
    let mut nb: Vec<Vec<usize>> = vec![Vec::new(); n];
    for i in 0..n {
        for j in 0..n {
            if i != j && dm[i][j] <= psi + tol {
                nb[i].push(j);
            }
        }
    }
    assert!(nb.iter().all(|x| !x.is_empty()), "isolated vertices not supported");
    // spread of the contact distances (precision of the input configuration)
    let mut spread = 0.0f64;
    for i in 0..n {
        for &j in &nb[i] {
            spread = spread.max(dm[i][j] - psi);
        }
    }
    if check.is_some() {
        println!("contact distance spread {spread:.3e} rad; true-point box half-width {:.3e}", (1e3 * spread).max(1e-9));
    }
    // rotation as in contact.rs (counterclockwise seen from outside)
    let mut adj = Vec::new();
    for i in 0..n {
        let a = p[i];
        let q = p[nb[i][0]];
        let t = [q[0] - dot(&a, &q) * a[0], q[1] - dot(&a, &q) * a[1], q[2] - dot(&a, &q) * a[2]];
        let r = dot(&t, &t).sqrt();
        let e1 = [t[0] / r, t[1] / r, t[2] / r];
        let e2 = [a[1] * e1[2] - a[2] * e1[1], a[2] * e1[0] - a[0] * e1[2], a[0] * e1[1] - a[1] * e1[0]];
        let mut l: Vec<(f64, usize)> = nb[i].iter().map(|&j| (dot(&p[j], &e2).atan2(dot(&p[j], &e1)), j)).collect();
        l.sort_by(|x, y| x.0.partial_cmp(&y.0).unwrap());
        adj.push(l.iter().map(|&(_, j)| j as u8).collect::<Vec<u8>>());
    }
    let g = Rot { n, adj };
    let mut wout = out.map(|o| {
        let mut w = std::io::BufWriter::new(std::fs::File::create(o).unwrap());
        write_header(&mut w).unwrap();
        w
    });
    let mut seen: HashSet<Vec<u8>> = HashSet::new();
    let mut fc = Faces::default();
    let bases: Vec<Option<usize>> = if with_vertex { (0..n).map(Some).collect() } else { vec![None] };
    for dv in bases {
        // graph on the original numbering with the vertex's edges removed
        let mut base = g.clone();
        if let Some(x) = dv {
            base.adj[x].clear();
            for u in 0..n {
                base.adj[u].retain(|&w| w as usize != x);
            }
        }
        let mut edges = Vec::new();
        for u in 0..n {
            for &w in &base.adj[u] {
                if (u as u8) < w {
                    edges.push((u as u8, w));
                }
            }
        }
        let m = edges.len();
        let mut idx: Vec<usize> = Vec::new();
        loop {
            let mut h = base.clone();
            for &i in &idx {
                let (a, b) = edges[i];
                h.adj[a as usize].retain(|&x| x != b);
                h.adj[b as usize].retain(|&x| x != a);
            }
            // compact numbering without the deleted vertex
            let keep: Vec<usize> = (0..n).filter(|&u| Some(u) != dv).collect();
            let pos = |u: usize| keep.iter().position(|&x| x == u).unwrap() as u8;
            let hc = Rot { n: keep.len(), adj: keep.iter().map(|&u| h.adj[u].iter().map(|&w| pos(w as usize)).collect()).collect() };
            let ok_deg = hc.adj.iter().all(|a| a.len() >= 3);
            let conn = {
                let mut s = vec![false; hc.n];
                let mut st = vec![0usize];
                s[0] = true;
                let mut c = 1;
                while let Some(u) = st.pop() {
                    for &w in &hc.adj[u] {
                        if !s[w as usize] {
                            s[w as usize] = true;
                            c += 1;
                            st.push(w as usize);
                        }
                    }
                }
                c == hc.n
            };
            if ok_deg && conn {
                Faces::compute(&hc, &mut fc);
                if fc.cyc.iter().all(|c| c.len() <= 6) {
                    let code = canon(&hc);
                    if seen.insert(code.clone()) {
                        let (mut amax, mut amin) = (0.0f64, 10.0f64);
                        let mut angs: Vec<Vec<f64>> = Vec::new();
                        for cyc in &fc.cyc {
                            let l = cyc.len();
                            angs.push(Vec::with_capacity(l));
                            for t in 0..l {
                                let (a, b, c) = (keep[cyc[(t + l - 1) % l] as usize], keep[cyc[t] as usize], keep[cyc[(t + 1) % l] as usize]);
                                // corner at b between the incoming neighbour a and the next c:
                                // c follows a in the rotation of b (face tracing rule)
                                let mut ang = angle_at(&p[b], &p[a], &p[c]);
                                if ang < 0.0 {
                                    ang += 2.0 * std::f64::consts::PI;
                                }
                                amax = amax.max(ang);
                                angs.last_mut().unwrap().push(ang);
                                amin = amin.min(ang);
                            }
                        }
                        let mut fs = [0usize; 8];
                        for c in &fc.cyc {
                            fs[c.len().min(7)] += 1;
                        }
                        let de: Vec<(u8, u8)> = idx.iter().map(|&i| edges[i]).collect();
                        let real = amax < std::f64::consts::PI;
                        println!(
                            "{} faces={:?} vertex={} edges={:?} maxcorner={:.6} mincorner={:.6}{}",
                            code.iter().map(|b| format!("{:02x}", b)).collect::<String>(),
                            &fs[3..7],
                            dv.map_or("-".to_string(), |v| v.to_string()),
                            de,
                            amax.to_degrees(),
                            amin.to_degrees(),
                            if real { " realised" } else { "" }
                        );
                        if real {
                            if let Some(w) = wout.as_mut() {
                                write_graph(w, &hc).unwrap();
                            }
                            if let Some((cp, cdlo, cdhi)) = check.as_ref() {
                                check_true_point(cp, *cdlo, *cdhi, &fc, &g, dv, &keep, &p, &angs, psi, (1e3 * spread).max(1e-9), targets.as_ref());
                            }
                            if let Some(pp) = params.as_ref() {
                                // full hexagon: the size-6 face with most former neighbours of dv
                                let iso: Option<Vec<bool>> = dv.map(|x| {
                                    let nbx: Vec<u8> = g.adj[x].iter().map(|&w| pos(w as usize)).collect();
                                    let score = |c: &Vec<u8>| if c.len() == 6 { c.iter().filter(|w| nbx.contains(w)).count() } else { 0 };
                                    let best = (0..fc.nf()).max_by_key(|&f| score(&fc.cyc[f])).unwrap();
                                    (0..fc.nf()).map(|f| f == best).collect()
                                });
                                let mut sys = Sys::default();
                                sys.build(&fc, pp, Opts::default(), iso.as_deref()).unwrap();
                                let mut val = vec![f64::NAN; sys.nvar];
                                val[0] = tammes15::poly::alpha(psi);
                                for (f, cv) in sys.cvar.iter().enumerate() {
                                    for (t, &vv) in cv.iter().enumerate() {
                                        if vv != 0 {
                                            val[vv as usize] = angs[f][t];
                                        }
                                    }
                                }
                                let mut bad = 0;
                                for r in 0..sys.nrows() {
                                    let s: f64 = (sys.rs[r]..sys.rs[r + 1]).map(|k| sys.tc[k as usize] * val[sys.tv[k as usize] as usize]).sum();
                                    if s < sys.rlo[r] - 1e-9 || s > sys.rhi[r] + 1e-9 {
                                        bad += 1;
                                        if bad <= 5 {
                                            let terms: Vec<String> = (sys.rs[r]..sys.rs[r + 1]).map(|k| format!("{}*v{}", sys.tc[k as usize], sys.tv[k as usize])).collect();
                                            println!("  violated row {r}: {} = {s:.6} not in [{:.6}, {:.6}]", terms.join(" + "), sys.rlo[r], sys.rhi[r]);
                                        }
                                    }
                                }
                                for (f, a) in angs.iter().enumerate() {
                                    if a.len() >= 5 {
                                        let s: f64 = a.iter().sum();
                                        let dg: Vec<String> = a.iter().map(|x| format!("{:.6}", x)).collect();
                                        println!("  face {f} corners (rad) [{}] sum {s:.6}", dg.join(", "));
                                    }
                                }
                                println!("  rows {} violated {bad} (at psi = {:.10} deg)", sys.nrows(), psi.to_degrees());
                            }
                        }
                    }
                }
            }
            let mut advanced = false;
            let mut j = idx.len();
            while j > 0 {
                j -= 1;
                let limit = m - (idx.len() - j);
                if idx[j] < limit {
                    idx[j] += 1;
                    for t in j + 1..idx.len() {
                        idx[t] = idx[t - 1] + 1;
                    }
                    advanced = true;
                    break;
                }
            }
            if !advanced {
                if idx.len() == k || idx.len() == m {
                    break;
                }
                idx = (0..idx.len() + 1).collect();
            }
        }
    }
    if let Some(mut w) = wout {
        w.flush().unwrap();
    }
}

/// Soundness check of level 2 with every optional test on (star, LP bounds on all variables):
/// the box of half-width 1e-9 around the true corner angles (and d = psi, wheel radii) of a
/// realised subgraph must not be refuted.
#[allow(clippy::too_many_arguments)]
fn check_true_point(cp: &Params, dlo: f64, dhi: f64, fc: &Faces, g: &Rot, dv: Option<usize>, keep: &[usize], p: &[V3], angs: &[Vec<f64>], psi: f64, eps: f64, targets: Option<&tammes15::local::Targets>) {
    let pos = |u: usize| keep.iter().position(|&x| x == u).unwrap() as u8;
    let iso: Option<Vec<bool>> = dv.map(|x| {
        let nbx: Vec<u8> = g.adj[x].iter().map(|&w| pos(w as usize)).collect();
        let score = |c: &Vec<u8>| if c.len() == 6 { c.iter().filter(|w| nbx.contains(w)).count() } else { 0 };
        let best = (0..fc.nf()).max_by_key(|&f| score(&fc.cyc[f])).unwrap();
        (0..fc.nf()).map(|f| f == best).collect()
    });
    let mut cfg = Cfg::default();
    cfg.use_face_ineq = false;
    cfg.use_cuts = false;
    cfg.xstar = true;
    cfg.xlp = true;
    cfg.xobbt = 2;
    let prob = match Prob::new(fc, cp, dlo, dhi, cfg, iso.as_deref()) {
        Ok(pr) => pr,
        Err(e) => {
            println!("  check: rejected at level 0 ({e:?})");
            return;
        }
    };
    let mut b = prob.root.clone();
    for (f, cv) in prob.sys.cvar.iter().enumerate() {
        for (t, &vv) in cv.iter().enumerate() {
            if vv != 0 {
                let x = angs[f][t];
                b[vv as usize] = b[vv as usize].meet(Iv::new(x - eps, x + eps));
            }
        }
    }
    b[prob.di] = b[prob.di].meet(Iv::new(psi - eps, psi + eps));
    for (f, fk) in prob.faces.iter().enumerate() {
        if let (FaceK::Hex { r: Some(r0), .. }, Some(x)) = (fk, dv) {
            for i in 0..6 {
                let r = tammes15::poly::dist(&p[x], &p[keep[fc.cyc[f][i] as usize]]);
                b[r0 + i] = b[r0 + i].meet(Iv::new(r - eps, r + eps));
            }
        }
    }
    if b.iter().any(|x| !(x.lo <= x.hi)) {
        println!("  check: true point outside the root box");
        return;
    }
    let mut sys = prob.sys.clone();
    match prob.check(&mut sys, &mut b, 0) {
        Ok(()) => println!("  check: true point kept (star pairs {})", prob.stars.as_ref().map_or(0, |s| s.npairs)),
        Err(r) => println!("  check: TRUE POINT REFUTED by {r:?}"),
    }
    if let Some(tg) = targets {
        check_place(cp, dlo, dhi, fc, iso.as_deref(), dv, keep, p, &b, tg);
    }
}

/// Gluing check (local.rs): the placed enclosure of the box around the true point must contain
/// the true configuration, normalised as in local.rs (root at (0, 0, 1), its reference neighbour
/// in the half plane y = 0, x > 0), up to the mirror y -> -y; and the Local test must fire (the
/// configuration is a copy of C1 or C3 up to 1e-15).
fn check_place(cp: &Params, dlo: f64, dhi: f64, fc: &Faces, iso: Option<&[bool]>, dv: Option<usize>, keep: &[usize], p: &[V3], b: &[Iv], tg: &tammes15::local::Targets) {
    let mut cfg = Cfg::default();
    cfg.use_face_ineq = false;
    cfg.use_cuts = false;
    let mut prob = Prob::new(fc, cp, dlo, dhi, cfg, iso).unwrap();
    prob.set_local(fc, None, 1.04e-3, f64::INFINITY, false);
    let geo = &prob.local.as_ref().unwrap().geo;
    let Some((pos, rho)) = geo.place(b) else {
        println!("  place: NO ENCLOSURE");
        return;
    };
    // true points in the numbering of local.rs: graph vertices, then the isolated vertex
    let mut tp: Vec<V3> = keep.iter().map(|&u| p[u]).collect();
    if let Some(x) = dv {
        tp.push(p[x]);
    }
    let (r0, w0) = geo.root_ref();
    let dot = |a: &V3, b: &V3| a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
    let e3 = tp[r0];
    let c = dot(&tp[w0], &e3);
    let mut e1 = [tp[w0][0] - c * e3[0], tp[w0][1] - c * e3[1], tp[w0][2] - c * e3[2]];
    let nn = dot(&e1, &e1).sqrt();
    for x in e1.iter_mut() {
        *x /= nn;
    }
    let e2 = [e3[1] * e1[2] - e3[2] * e1[1], e3[2] * e1[0] - e3[0] * e1[2], e3[0] * e1[1] - e3[1] * e1[0]];
    let mut worst = [0.0f64; 2];
    for (m, mirror) in [false, true].iter().enumerate() {
        for v in 0..tp.len() {
            let y = [dot(&tp[v], &e1), if *mirror { -dot(&tp[v], &e2) } else { dot(&tp[v], &e2) }, dot(&tp[v], &e3)];
            let mut s = 0.0;
            for k in 0..3 {
                let g = (pos[v][k].lo - y[k]).max(y[k] - pos[v][k].hi).max(0.0);
                s += g * g;
            }
            // excess of the distance to the enclosure box over rho (should be <= 0)
            worst[m] = worst[m].max(s.sqrt() - rho[v]);
        }
    }
    let rmax = rho.iter().cloned().fold(0.0, f64::max);
    let ok = worst[0].min(worst[1]) <= 1e-12;
    let loc = geo.local(b, tg, 1.04e-3);
    println!(
        "  place: {} (excess {:.2e} / mirror {:.2e}, max rho {:.2e}), local {}",
        if ok { "true configuration enclosed" } else { "TRUE CONFIGURATION NOT ENCLOSED" },
        worst[0],
        worst[1],
        rmax,
        if loc { "fires" } else { "DOES NOT FIRE" }
    );
}
