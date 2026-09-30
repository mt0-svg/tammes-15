//! Independent consistency test of the gluing of local.rs (Geo::place, local_at, pair_at,
//! close_at) on the 8 frame configurations of data/tie_targets.txt.
//! Usage: localtest ROOT (the root of this repository).
//!
//! For each configuration, after a random orthogonal map (rotation, or rotation times a
//! reflection), the contact graph is built with its rotation system in BOTH orientations
//! (counterclockwise seen from outside, and the reversed lists), for the full graph, every
//! single-vertex deletion whose merged face is a hexagon (the vertex becomes the free point),
//! every single-edge deletion and every vertex-plus-edge deletion. The true corners, d and wheel
//! radii are measured on the configuration (corner at b from a to c in the sense of the
//! rotation), and a box of half-width w is placed around them OFF CENTRE (random split of the
//! width), for several w. The test then checks:
//!   - place() gives an enclosure containing the true configuration normalised as local.rs says
//!     (root at (0, 0, 1), reference neighbour in the half plane y = 0, x > 0), unmirrored for the
//!     counterclockwise orientation and mirrored for the other one (excess <= 1e-13);
//!   - the other mirror is NOT enclosed (the orientation claim is not vacuous);
//!   - pair_at and close_at never fire (genuine configuration);
//!   - local_at fires whenever max rho < 1.04e-3 minus the enclosure width.
//! Negative controls of Local, on the placement of the full graph (first width, counterclockwise):
//!   - one point moved along a great circle by 0.9 r fires, by 1.1 r or by 0.1 rad does not, for
//!     every point (r = 1.04e-3); the largest move that fires, found by bisection, lies within
//!     1e-8 below 2 asin(r / 2), the geodesic length of a chord r;
//!   - the whole placement turned about the root axis so that its farthest point moves by 0.9 r
//!     fires, by 1.1 r does not;
//!   - the placement tested against the targets of the other type only (C1 against C3) does not
//!     fire: a genuine configuration far from every target is not taken for one.
use std::sync::Arc;
use tammes15::deep::{read_drange, Cfg, Prob};
use tammes15::graph::Faces;
use tammes15::ivt::Iv;
use tammes15::local::Targets;
use tammes15::params::Params;
use tammes15::pcode::Rot;

type V = [f64; 3];
fn dot(a: &V, b: &V) -> f64 {
    a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
}
fn cross(a: &V, b: &V) -> V {
    [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
}
fn unit(a: &V) -> V {
    let r = dot(a, a).sqrt();
    [a[0] / r, a[1] / r, a[2] / r]
}
fn angdist(a: &V, b: &V) -> f64 {
    let c = cross(a, b);
    dot(&c, &c).sqrt().atan2(dot(a, b))
}
fn tangent(p: &V, q: &V) -> V {
    let c = dot(p, q);
    unit(&[q[0] - c * p[0], q[1] - c * p[1], q[2] - c * p[2]])
}
/// counterclockwise angle (seen from outside) at p from direction q to direction r, in [0, 2 pi)
fn ccw(p: &V, q: &V, r: &V) -> f64 {
    let tq = tangent(p, q);
    let tr = tangent(p, r);
    let a = dot(p, &cross(&tq, &tr)).atan2(dot(&tq, &tr));
    if a < 0.0 {
        a + 2.0 * std::f64::consts::PI
    } else {
        a
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> f64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 >> 11) as f64 / (1u64 << 53) as f64
    }
}

fn load_confs(path: &str) -> Vec<(String, Vec<V>)> {
    let s = std::fs::read_to_string(path).unwrap();
    let mut lines = s.lines().filter(|l| !l.starts_with('#') && !l.trim().is_empty());
    let mut out = Vec::new();
    while let Some(h) = lines.next() {
        let name = h[5..].to_string();
        let mut p = Vec::new();
        for _ in 0..15 {
            let w: Vec<f64> = lines.next().unwrap().split_whitespace().map(|x| x.parse().unwrap()).collect();
            p.push(unit(&[w[0], w[2], w[4]]));
        }
        lines.next();
        out.push((name, p));
    }
    out
}

#[derive(Default)]
struct Stat {
    cases: u64,
    free: u64,
    noenc: u64,
    rejected: u64,
    worst: f64,
    other_min: f64,
    maxrho: f64,
    pair: u64,
    close: u64,
    local_expected: u64,
    local_fired: u64,
}

fn main() {
    let root = std::env::args().nth(1).expect("usage: localtest ROOT");
    let pfile = format!("{root}/data/params15ft.txt");
    let params = Params::load(&pfile);
    let (dlo, dhi) = read_drange(&pfile);
    let tg = Arc::new(Targets::load(&format!("{root}/data/tie_targets.txt")));
    let confs = load_confs(&format!("{root}/data/tie_targets.txt"));
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let widths = [1e-10, 1e-7, 1e-6, 1e-5, 3e-5];
    let mut neg: Vec<(String, bool)> = Vec::new();
    for (ci, (name, p0)) in confs.iter().enumerate() {
        for refl in [false, true] {
            // random orthogonal map: rotation from a random unit quaternion, then optional reflection
            let (a, b, c, d) = loop {
                let q: Vec<f64> = (0..4).map(|_| 2.0 * rng.next() - 1.0).collect();
                let n = q.iter().map(|x| x * x).sum::<f64>();
                if n > 0.1 && n < 1.0 {
                    let s = n.sqrt();
                    break (q[0] / s, q[1] / s, q[2] / s, q[3] / s);
                }
            };
            let m = [
                [a * a + b * b - c * c - d * d, 2.0 * (b * c - a * d), 2.0 * (b * d + a * c)],
                [2.0 * (b * c + a * d), a * a - b * b + c * c - d * d, 2.0 * (c * d - a * b)],
                [2.0 * (b * d - a * c), 2.0 * (c * d + a * b), a * a - b * b - c * c + d * d],
            ];
            let p: Vec<V> = p0
                .iter()
                .map(|x| {
                    let mut y = [0.0; 3];
                    for i in 0..3 {
                        y[i] = m[i][0] * x[0] + m[i][1] * x[1] + m[i][2] * x[2];
                    }
                    if refl {
                        y[2] = -y[2];
                    }
                    unit(&y)
                })
                .collect();
            let n = 15;
            let mut psi = f64::INFINITY;
            for i in 0..n {
                for j in i + 1..n {
                    psi = psi.min(angdist(&p[i], &p[j]));
                }
            }
            let mut nb: Vec<Vec<usize>> = vec![Vec::new(); n];
            for i in 0..n {
                for j in 0..n {
                    if i != j && angdist(&p[i], &p[j]) <= psi + 1e-9 {
                        nb[i].push(j);
                    }
                }
            }
            let edges: Vec<(usize, usize)> = (0..n).flat_map(|i| nb[i].iter().filter(move |&&j| j > i).map(move |&j| (i, j))).collect();
            assert_eq!(edges.len(), 30);
            // deletion patterns: (vertex, edge)
            let mut pats: Vec<(Option<usize>, Vec<usize>)> = vec![(None, vec![])];
            for x in 0..n {
                pats.push((Some(x), vec![]));
            }
            for e in 0..30 {
                pats.push((None, vec![e]));
                for e2 in e + 1..30 {
                    pats.push((None, vec![e, e2]));
                }
            }
            for x in 0..n {
                for e in 0..30 {
                    if edges[e].0 != x && edges[e].1 != x {
                        pats.push((Some(x), vec![e]));
                    }
                }
            }
            for orient_ccw in [true, false] {
                let mut st: Vec<Stat> = (0..widths.len()).map(|_| Stat { other_min: f64::INFINITY, ..Default::default() }).collect();
                for (dv, de) in &pats {
                    let dv = *dv;
                    let keep: Vec<usize> = (0..n).filter(|&u| Some(u) != dv).collect();
                    let posn = |u: usize| keep.iter().position(|&x| x == u).unwrap();
                    let alive = |i: usize, j: usize| {
                        Some(i) != dv && Some(j) != dv && de.iter().all(|&e| edges[e] != (i.min(j), i.max(j)))
                    };
                    let mut adj: Vec<Vec<u8>> = Vec::new();
                    for &i in &keep {
                        let l: Vec<usize> = nb[i].iter().cloned().filter(|&j| alive(i, j)).collect();
                        if l.len() < 3 {
                            break;
                        }
                        let e0 = l[0];
                        let mut s: Vec<(f64, usize)> = l.iter().map(|&j| (if j == e0 { 0.0 } else { ccw(&p[i], &p[e0], &p[j]) }, j)).collect();
                        s.sort_by(|x, y| x.0.partial_cmp(&y.0).unwrap());
                        let mut v: Vec<u8> = s.iter().map(|&(_, j)| posn(j) as u8).collect();
                        if !orient_ccw {
                            v.reverse();
                        }
                        adj.push(v);
                    }
                    if adj.len() != keep.len() {
                        continue;
                    }
                    let g = Rot { n: keep.len(), adj };
                    let mut fc = Faces::default();
                    Faces::compute(&g, &mut fc);
                    if fc.cyc.iter().any(|c| c.len() > 6) {
                        continue;
                    }
                    // Euler check (connected plane graph)
                    if keep.len() as i64 - fc.ne as i64 + fc.nf() as i64 != 2 {
                        continue;
                    }
                    // true corners in the sense of the rotation; skip non-convex (not realised)
                    let mut angs: Vec<Vec<f64>> = Vec::new();
                    let mut convex = true;
                    for cyc in &fc.cyc {
                        let l = cyc.len();
                        let mut v = Vec::new();
                        for t in 0..l {
                            let (a, b, c) = (keep[cyc[(t + l - 1) % l] as usize], keep[cyc[t] as usize], keep[cyc[(t + 1) % l] as usize]);
                            let ang = if orient_ccw { ccw(&p[b], &p[a], &p[c]) } else { ccw(&p[b], &p[c], &p[a]) };
                            if !(ang < std::f64::consts::PI) {
                                convex = false;
                            }
                            v.push(ang);
                        }
                        angs.push(v);
                    }
                    if !convex {
                        continue;
                    }
                    // corner sums at every vertex = 2 pi
                    for v in 0..keep.len() {
                        let s: f64 = fc.at[v].iter().map(|&(f, t)| angs[f as usize][t as usize]).sum();
                        assert!((s - 2.0 * std::f64::consts::PI).abs() < 1e-9, "corner sum {s}");
                    }
                    // full hexagon: the face containing all former neighbours of dv
                    let iso: Option<Vec<bool>> = match dv {
                        None => None,
                        Some(x) => {
                            let nx: Vec<u8> = nb[x].iter().map(|&w| posn(w) as u8).collect();
                            let f = (0..fc.nf()).find(|&f| nx.iter().all(|w| fc.cyc[f].contains(w)));
                            match f {
                                Some(f) if fc.cyc[f].len() == 6 => Some((0..fc.nf()).map(|h| h == f).collect()),
                                _ => continue,
                            }
                        }
                    };
                    let mut cfg = Cfg::default();
                    cfg.use_face_ineq = false;
                    cfg.use_cuts = false;
                    let mut prob = match Prob::new(&fc, &params, dlo, dhi, cfg, iso.as_deref()) {
                        Ok(pr) => pr,
                        Err(_) => {
                            st[0].rejected += 1;
                            continue;
                        }
                    };
                    // true values of the variables
                    let nv = prob.root.len();
                    let mut val = vec![f64::NAN; nv];
                    val[0] = tammes15::poly::alpha(psi);
                    val[prob.di] = psi;
                    for (f, cv) in prob.sys.cvar.iter().enumerate() {
                        for (t, &vv) in cv.iter().enumerate() {
                            let x = angs[f][t];
                            let j = vv as usize;
                            if val[j].is_nan() {
                                val[j] = x;
                            } else {
                                assert!((val[j] - x).abs() < 1e-9, "shared variable {j}: {} vs {x}", val[j]);
                            }
                        }
                    }
                    if let Some(x) = dv {
                        let f = iso.as_ref().unwrap().iter().position(|&b| b).unwrap();
                        if let tammes15::deep::FaceK::Hex { r: Some(r0), .. } = prob.faces[f] {
                            for i in 0..6 {
                                val[r0 + i] = angdist(&p[x], &p[keep[fc.cyc[f][i] as usize]]);
                            }
                        }
                    }
                    assert!(val.iter().all(|x| !x.is_nan()));
                    prob.set_local(&fc, Some(tg.clone()), 1.04e-3, f64::INFINITY, true);
                    let geo = &prob.local.as_ref().unwrap().geo;
                    let (r0, w0) = geo.root_ref();
                    // true configuration in local.rs numbering, normalised
                    let mut tp: Vec<V> = keep.iter().map(|&u| p[u]).collect();
                    if let Some(x) = dv {
                        tp.push(p[x]);
                    }
                    let e3 = tp[r0];
                    let e1 = tangent(&e3, &tp[w0]);
                    let e2 = cross(&e3, &e1);
                    for (wi, &w) in widths.iter().enumerate() {
                        let mut b = prob.root.clone();
                        for j in 0..nv {
                            let al = rng.next();
                            b[j] = b[j].meet(Iv::new(val[j] - w * al, val[j] + w * (1.0 - al)));
                        }
                        if b.iter().any(|x| !(x.lo <= x.hi)) {
                            st[wi].rejected += 1;
                            continue;
                        }
                        let s = &mut st[wi];
                        s.cases += 1;
                        if dv.is_some() {
                            s.free += 1;
                        }
                        let Some((pos, rho)) = geo.place(&b) else {
                            s.noenc += 1;
                            continue;
                        };
                        let mut exc = [0.0f64; 2];
                        for (mi, mirror) in [false, true].iter().enumerate() {
                            for v in 0..tp.len() {
                                let y2 = dot(&tp[v], &e2);
                                let y = [dot(&tp[v], &e1), if *mirror { -y2 } else { y2 }, dot(&tp[v], &e3)];
                                let mut q = 0.0;
                                for k in 0..3 {
                                    let gk = (pos[v][k].lo - y[k]).max(y[k] - pos[v][k].hi).max(0.0);
                                    q += gk * gk;
                                }
                                exc[mi] = exc[mi].max(q.sqrt() - rho[v]);
                            }
                        }
                        let (mine, other) = if orient_ccw { (exc[0], exc[1]) } else { (exc[1], exc[0]) };
                        s.worst = s.worst.max(mine);
                        s.other_min = s.other_min.min(other);
                        if wi == 0 && dv.is_none() && de.is_empty() && orient_ccw {
                            neg.push(negative_controls(ci, name, refl, geo, &pos, &rho, &tg));
                        }
                        let mr = rho.iter().cloned().fold(0.0, f64::max);
                        s.maxrho = s.maxrho.max(mr);
                        if geo.pair_at(&pos, &rho, &b) {
                            s.pair += 1;
                        }
                        if geo.close_at(&pos, &rho, &b) {
                            s.close += 1;
                        }
                        let encw = pos.iter().map(|q| q.iter().map(|x| x.hi - x.lo).fold(0.0, f64::max)).fold(0.0, f64::max);
                        if mr + 2.0 * encw < 1.0e-3 && tp.len() == 15 {
                            s.local_expected += 1;
                            if geo.local_at(&pos, &rho, &tg, 1.04e-3) {
                                s.local_fired += 1;
                            }
                        }
                    }
                }
                for (wi, s) in st.iter().enumerate() {
                    println!(
                        "conf {ci} {name} refl={refl} orient={} w={:.0e}: cases {} (with free point {}, rejected {}), no enclosure {}, worst excess {:.2e}, other mirror min excess {:.2e}, max rho {:.2e}, pair fired {}, close fired {}, local fired {}/{}",
                        if orient_ccw { "ccw" } else { "cw" },
                        widths[wi],
                        s.cases,
                        s.free,
                        s.rejected,
                        s.noenc,
                        s.worst,
                        s.other_min,
                        s.maxrho,
                        s.pair,
                        s.close,
                        s.local_fired,
                        s.local_expected
                    );
                }
            }
        }
    }
    // Negative controls of Local (local_at), on the placement of each frame configuration (full
    // contact graph, box half-width 1e-10, counterclockwise rotation lists)
    let mut all = true;
    for (line, ok) in &neg {
        println!("{line}");
        all &= ok;
    }
    println!("local negative controls: {} placements, {}", neg.len(), if all { "PASS" } else { "FAIL" });
    if !all {
        std::process::exit(1);
    }
}

/// The placement (pos, rho) moved: point v turned on the sphere by the angle s, in a fixed tangent
/// direction at its midpoint (every coordinate interval translated by the same amount).
fn moved(pos: &[[Iv; 3]], v: usize, s: f64) -> Vec<[Iv; 3]> {
    let m = unit(&[pos[v][0].mid(), pos[v][1].mid(), pos[v][2].mid()]);
    let k = (0..3).min_by(|&a, &b| m[a].abs().partial_cmp(&m[b].abs()).unwrap()).unwrap();
    let mut e = [0.0; 3];
    e[k] = 1.0;
    let t = tangent(&m, &e);
    let mut q = pos.to_vec();
    for i in 0..3 {
        let d = (s.cos() - 1.0) * m[i] + s.sin() * t[i];
        q[v][i] = Iv::new((pos[v][i].lo + d).next_down(), (pos[v][i].hi + d).next_up());
    }
    q
}

/// The whole placement turned about the axis of the root, (0, 0, 1), by the angle th.
fn turned(pos: &[[Iv; 3]], th: f64) -> Vec<[Iv; 3]> {
    pos.iter()
        .map(|p| {
            let (x, y) = (p[0].mid(), p[1].mid());
            let (dx, dy) = (x * th.cos() - y * th.sin() - x, x * th.sin() + y * th.cos() - y);
            [
                Iv::new((p[0].lo + dx).next_down(), (p[0].hi + dx).next_up()),
                Iv::new((p[1].lo + dy).next_down(), (p[1].hi + dy).next_up()),
                p[2],
            ]
        })
        .collect()
}

/// Local (radius r = 1.04e-3) must fire on the placement of a frame configuration and on it with one
/// point moved by 0.9 r, and must not fire with one point moved by 1.1 r or by 0.1 rad, nor on the
/// placement turned about the root axis so that some point moves by 1.1 r (it fires at 0.9 r), nor
/// against the targets of the other type only (a genuine optimal configuration far from every
/// target of that list). For each point, the largest move that still fires (bisection) must lie
/// between r - 1e-8 and r.
fn negative_controls(ci: usize, name: &str, refl: bool, geo: &tammes15::local::Geo, pos: &[[Iv; 3]], rho: &[f64], tg: &Targets) -> (String, bool) {
    let r: f64 = 1.04e-3;
    // Local compares chord lengths with r: a point moved along a great circle by s is at chord 2 sin(s / 2),
    // so the largest geodesic move that can still fire is 2 asin(r / 2)
    let sr = 2.0 * (r / 2.0).asin();
    let fires = |q: &[[Iv; 3]], t: &Targets| geo.local_at(q, rho, t, r);
    let n = pos.len();
    let base = fires(pos, tg);
    let count = |s: f64| (0..n).filter(|&v| fires(&moved(pos, v, s), tg)).count();
    let (f09, f11, ffar) = (count(0.9 * r), count(1.1 * r), count(0.1));
    let (mut gmin, mut gmax) = (f64::INFINITY, 0.0f64);
    for v in 0..n {
        let (mut a, mut b) = (0.9 * r, 1.1 * r);
        for _ in 0..60 {
            let c = 0.5 * (a + b);
            if fires(&moved(pos, v, c), tg) {
                a = c
            } else {
                b = c
            }
        }
        gmin = gmin.min(sr - a);
        gmax = gmax.max(sr - a);
    }
    // the largest distance of a point from the root axis, and the turn that moves that point by s
    let mxy = pos.iter().map(|p| (p[0].mid().powi(2) + p[1].mid().powi(2)).sqrt()).fold(0.0, f64::max);
    let th = |s: f64| 2.0 * (s / (2.0 * mxy)).asin();
    let (t09, t11) = (fires(&turned(pos, th(0.9 * r)), tg), fires(&turned(pos, th(1.1 * r)), tg));
    // target names are "POINTS TYPE a->b [mirror]", the placement name "POINTS TYPE"
    let ty = name.split_whitespace().nth(1).unwrap_or("");
    let keep: Vec<usize> = (0..tg.names.len()).filter(|&i| tg.names[i].split_whitespace().nth(1) != Some(ty)).collect();
    let other = Targets {
        t: keep.iter().map(|&i| tg.t[i]).collect(),
        tm: keep.iter().map(|&i| tg.tm[i]).collect(),
        names: keep.iter().map(|&i| tg.names[i].clone()).collect(),
    };
    let fo = fires(pos, &other);
    let ok = base && f09 == n && f11 == 0 && ffar == 0 && gmin > 0.0 && gmax < 1e-8 && t09 && !t11 && !fo && !other.t.is_empty();
    (
        format!(
            "local negative control conf {ci} {name} refl={refl}: placement fires {base}; one point moved by 0.9 r: fires for {f09} of {n} points, by 1.1 r: {f11}, by 0.1 rad: {ffar}; 2 asin(r/2) minus the largest move that fires: {gmin:.3e} to {gmax:.3e}; turned about the root axis, largest move 0.9 r: fires {t09}, 1.1 r: fires {t11}; against the {} targets of the other type only: fires {fo}; {}",
            other.t.len(),
            if ok { "as expected" } else { "NOT AS EXPECTED" }
        ),
        ok,
    )
}
