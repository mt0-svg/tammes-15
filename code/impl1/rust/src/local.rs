//! Gluing of a box into an enclosure of the whole configuration, and the tie-window discard
//! "Local" (Sections 4 and 5.4 of the paper).
//!
//! Positions. Let G be the plane graph of the case (rotation system from the traced faces), d the
//! edge length, and at every vertex v the corners of the faces around v (box variables). Fix a
//! root vertex v0 and its reference neighbour w0. Every genuine configuration realising the box is
//! isometric to the configuration Y built as follows: Y(v0) = (0, 0, 1), frame F(v0) = I; a vertex
//! v with frame F(v) = (e1, e2, p) (orthonormal, right handed, p = Y(v), e1 the unit tangent at p
//! towards the reference neighbour ref(v), e2 = p x e1) gives its neighbour n, reached from ref(v)
//! by turning through the corners of the faces between them (angle phi, rotation sense of the
//! embedding), the frame
//!     F(n) = F(v) Rz(phi) Ry(d) Z,     Z = diag(-1, -1, 1),
//! whose third column is Y(n) = cos d p + sin d (cos phi e1 + sin phi e2) and whose first column
//! is the unit tangent at Y(n) towards p (so ref(n) = v). The isolated vertex P of a full hexagon
//! A_0..A_5 (wheel variables r_i = |P A_i|) is Y(P) = F(A_i) Rz(psi) Ry(r_i) e3, psi = (angle from
//! ref(A_i) to A_{i-1}) + beta_i, beta_i = angle(A_{i-1} A_i P) = tri_angle(r_{i-1}, r_i, d).
//! If the embedding's rotation sense is the opposite one, Y is the mirror image of the genuine
//! configuration: still isometric, which is all that is used.
//!
//! Centered enclosure. Each angle enters through an interval enclosure over the box (sums of
//! corner intervals, intersected with 2 pi minus the complementary corners since the corners
//! around a vertex sum to 2 pi; d; r_i; beta_i). Take its midpoint c and radius rho (upward).
//! Every factor is a rotation and |Rz(a) - Rz(b)| = |Ry(a) - Ry(b)| = 2|sin((a - b)/2)| <= |a - b|
//! (operator norm), so |A_1 ... A_m - B_1 ... B_m| <= sum |A_i - B_i| for rotations gives
//!     |Y(v) - Y_c(v)| <= rho(v) = sum over the steps of the path from v0 of the radii,
//! Y_c(v) the position computed at the midpoints (itself enclosed in interval arithmetic).
//!
//! Local. Targets: the 8 frame configurations of data/tie_targets.txt (types C1, C3), each
//! normalised in every possible way (root image a, reference image b for each of the 60 directed
//! contacts ab: a -> (0, 0, 1), b -> half plane y = 0, x > 0) and with its mirror image (y -> -y).
//! The box is discarded when, for some normalised target T, every point v of Y (vertices and
//! isolated vertices) has sup |Y_c(v) - T_j| + rho(v) <= r for a target point T_j, the map v -> j
//! being injective (hence a bijection of the 15 points). Then every genuine configuration X
//! realising the box satisfies |x_v - R T_j(v)| <= r for a rotation R, and Theorem 4.1
//! (Section 4, r = 1.04e-3) gives psi(X) <= psi*: the box holds no configuration
//! with minimal distance > psi*. So a box discarded by Local is not "empty": it is empty of
//! configurations better than the known optimum, which is what the tie window needs.
//!
//! Pair (optional, a refutation): two points u, v not joined by an edge with
//! sup |Y(u) - Y(v)| < 2 sin(d_lo / 2) cannot both belong to a configuration of minimal distance
//! >= d_lo (all pairs of a configuration are at angular distance >= d).

use crate::graph::Faces;
use crate::iv::{parse_dn, parse_up, TWO_PI_HI, TWO_PI_LO};
use crate::ivt::Iv;

pub type V3 = [Iv; 3];
type M3 = [[Iv; 3]; 3];

const ZERO: Iv = Iv { lo: 0.0, hi: 0.0 };
const ONE: Iv = Iv { lo: 1.0, hi: 1.0 };

fn mmul(a: &M3, b: &M3) -> M3 {
    let mut c = [[ZERO; 3]; 3];
    for i in 0..3 {
        for j in 0..3 {
            let mut s = a[i][0].mul(b[0][j]);
            s = s.add(a[i][1].mul(b[1][j]));
            s = s.add(a[i][2].mul(b[2][j]));
            c[i][j] = s;
        }
    }
    c
}

/// Rz(phi) Ry(d) Z at point arguments (enclosures of the exact matrix).
fn step(phi: f64, d: f64) -> M3 {
    let (cp, sp) = (Iv::pt(phi).cos(), Iv::pt(phi).sin());
    let (cd, sd) = (Iv::pt(d).cos(), Iv::pt(d).sin());
    // Rz = [[cp, -sp, 0], [sp, cp, 0], [0, 0, 1]], Ry = [[cd, 0, sd], [0, 1, 0], [-sd, 0, cd]]
    // Rz Ry = [[cp cd, -sp, cp sd], [sp cd, cp, sp sd], [-sd, 0, cd]]; times Z negates columns 0, 1
    [
        [cp.mul(cd).neg(), sp, cp.mul(sd)],
        [sp.mul(cd).neg(), cp.neg(), sp.mul(sd)],
        [sd, ZERO, cd],
    ]
}

/// Midpoint of an enclosure and an upper bound of the distance from it to any point of the
/// enclosure.
fn center(x: Iv) -> Option<(f64, f64)> {
    if !(x.lo <= x.hi) || !x.lo.is_finite() || !x.hi.is_finite() {
        return None;
    }
    let c = x.mid().max(x.lo).min(x.hi);
    let r = Iv::pt(c).sub(Iv::pt(x.lo)).hi.max(Iv::pt(x.hi).sub(Iv::pt(c)).hi);
    Some((c, r))
}

fn up_add(a: f64, b: f64) -> f64 {
    (a + b).next_up()
}

/// One BFS step: the frame of `v` is computed from the frame of `from` by turning from ref(from)
/// through the corners `fwd` (the complementary corners around `from` are `bwd`).
#[derive(Clone, Debug)]
struct Step {
    v: usize,
    from: usize,
    fwd: Vec<usize>,
    bwd: Vec<usize>,
}

/// Isolated vertex of a full hexagon, placed from corner A_i = cyc[i].
#[derive(Clone, Debug)]
struct Free {
    /// for each i: (A_i, corners from ref(A_i) to A_{i-1}, complementary corners, var r_{i-1}, var r_i)
    from: Vec<(usize, Vec<usize>, Vec<usize>, usize, usize)>,
}

/// Geometry of one case (graph, variables).
#[derive(Clone, Debug)]
pub struct Geo {
    n: usize,
    root: usize,
    root_ref: usize,
    steps: Vec<Step>,
    free: Vec<Free>,
    /// pairs of points joined by an edge (for Pair), points numbered vertices then free points
    edge: Vec<Vec<bool>>,
    di: usize,
}

/// Normalised targets: 15 points each, enclosures and midpoints.
pub struct Targets {
    pub t: Vec<[V3; 15]>,
    pub tm: Vec<[[f64; 3]; 15]>,
    pub names: Vec<String>,
}

fn dot(a: &V3, b: &V3) -> Iv {
    a[0].mul(b[0]).add(a[1].mul(b[1])).add(a[2].mul(b[2]))
}

impl Targets {
    /// Reads data/tie_targets.txt: "conf NAME TYPE", 15 lines of "x_mid x_rad y_mid y_rad z_mid
    /// z_rad", "contacts i j i j ..." (0-based).
    pub fn load(path: &str) -> Targets {
        let s = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let mut lines = s.lines().filter(|l| !l.starts_with('#') && !l.trim().is_empty());
        let mut out = Targets { t: Vec::new(), tm: Vec::new(), names: Vec::new() };
        while let Some(h) = lines.next() {
            assert!(h.starts_with("conf "), "expected conf line, got {h}");
            let name = h[5..].trim().to_string();
            let mut p = [[ZERO; 3]; 15];
            for i in 0..15 {
                let w: Vec<&str> = lines.next().unwrap().split_whitespace().collect();
                assert_eq!(w.len(), 6);
                for k in 0..3 {
                    let rad = parse_up(w[2 * k + 1]);
                    let lo = Iv::pt(parse_dn(w[2 * k])).sub(Iv::pt(rad)).lo;
                    let hi = Iv::pt(parse_up(w[2 * k])).add(Iv::pt(rad)).hi;
                    p[i][k] = Iv::new(lo, hi);
                }
            }
            let c: Vec<usize> = lines.next().unwrap().split_whitespace().skip(1).map(|x| x.parse().unwrap()).collect();
            assert_eq!(c.len(), 60, "30 contacts expected");
            for e in 0..30 {
                for (a, b) in [(c[2 * e], c[2 * e + 1]), (c[2 * e + 1], c[2 * e])] {
                    // frame: e3 = p_a, e1 = unit(p_b - <p_a, p_b> p_a), e2 = e3 x e1
                    let e3 = p[a];
                    let ab = dot(&p[a], &p[b]);
                    let mut t1 = [ZERO; 3];
                    for k in 0..3 {
                        t1[k] = p[b][k].sub(ab.mul(p[a][k]));
                    }
                    let nn = dot(&t1, &t1).sqrt();
                    let e1 = [t1[0].div(nn), t1[1].div(nn), t1[2].div(nn)];
                    let e2 = [
                        e3[1].mul(e1[2]).sub(e3[2].mul(e1[1])),
                        e3[2].mul(e1[0]).sub(e3[0].mul(e1[2])),
                        e3[0].mul(e1[1]).sub(e3[1].mul(e1[0])),
                    ];
                    for mirror in [false, true] {
                        let mut q = [[ZERO; 3]; 15];
                        let mut qm = [[0.0; 3]; 15];
                        for j in 0..15 {
                            let y = dot(&p[j], &e2);
                            q[j] = [dot(&p[j], &e1), if mirror { y.neg() } else { y }, dot(&p[j], &e3)];
                            for k in 0..3 {
                                qm[j][k] = q[j][k].mid();
                            }
                        }
                        out.t.push(q);
                        out.tm.push(qm);
                        out.names.push(format!("{name} {a}->{b}{}", if mirror { " mirror" } else { "" }));
                    }
                }
            }
        }
        out
    }
}

impl Geo {
    /// `cvar[f][pos]`: corner variable of face f at position pos; `wheel[f]`: first wheel
    /// variable of face f when it is a full hexagon; `di`: index of d.
    pub fn new(fc: &Faces, cvar: &[Vec<u32>], wheel: &[Option<usize>], di: usize) -> Geo {
        let n = fc.at.len();
        // rotation at v: entries (prev, next, corner var) with next = successor of prev
        let mut rot: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut cor: Vec<Vec<usize>> = vec![Vec::new(); n];
        for v in 0..n {
            let ent: Vec<(usize, usize, usize)> = fc.at[v]
                .iter()
                .map(|&(f, pos)| {
                    let c = &fc.cyc[f as usize];
                    let m = c.len();
                    let p = pos as usize;
                    (c[(p + m - 1) % m] as usize, c[(p + 1) % m] as usize, cvar[f as usize][p] as usize)
                })
                .collect();
            let deg = ent.len();
            let mut cur = ent[0].0;
            for _ in 0..deg {
                let e = ent.iter().find(|e| e.0 == cur).expect("rotation");
                rot[v].push(cur);
                cor[v].push(e.2); // corner from rot[v][k] to rot[v][k + 1]
                cur = e.1;
            }
            assert_eq!(cur, rot[v][0], "rotation does not close");
        }
        // root: minimal eccentricity
        let bfs = |r: usize| -> (Vec<usize>, Vec<usize>, usize) {
            let mut dist = vec![usize::MAX; n];
            let mut par = vec![usize::MAX; n];
            let mut order = vec![r];
            dist[r] = 0;
            let mut h = 0;
            while h < order.len() {
                let v = order[h];
                h += 1;
                for &w in &rot[v] {
                    if dist[w] == usize::MAX {
                        dist[w] = dist[v] + 1;
                        par[w] = v;
                        order.push(w);
                    }
                }
            }
            let ecc = *dist.iter().max().unwrap();
            (order, par, ecc)
        };
        let root = (0..n).min_by_key(|&r| bfs(r).2).unwrap();
        let (order, par, _) = bfs(root);
        // an unreached vertex would stay at the pole with no deviation bound: refuse such graphs
        assert_eq!(order.len(), n, "graph not connected");
        // ref(v): rot[root][0] for the root, the BFS parent otherwise
        let refv = |v: usize| if v == root { rot[root][0] } else { par[v] };
        // corners at v from ref(v) to w, and the complementary ones
        let arc = |v: usize, w: usize| -> (Vec<usize>, Vec<usize>) {
            let deg = rot[v].len();
            let k0 = rot[v].iter().position(|&x| x == refv(v)).unwrap();
            let k1 = rot[v].iter().position(|&x| x == w).unwrap();
            let s = (k1 + deg - k0) % deg;
            let fwd: Vec<usize> = (0..s).map(|t| cor[v][(k0 + t) % deg]).collect();
            let bwd: Vec<usize> = (s..deg).map(|t| cor[v][(k0 + t) % deg]).collect();
            (fwd, bwd)
        };
        let mut steps = Vec::new();
        for &v in order.iter().skip(1) {
            let (fwd, bwd) = arc(par[v], v);
            steps.push(Step { v, from: par[v], fwd, bwd });
        }
        let mut free = Vec::new();
        for (f, w) in wheel.iter().enumerate() {
            if let Some(r0) = *w {
                let c = &fc.cyc[f];
                assert_eq!(c.len(), 6);
                let mut from = Vec::new();
                for i in 0..6 {
                    let a = c[i] as usize;
                    let am = c[(i + 5) % 6] as usize;
                    let (fwd, bwd) = arc(a, am);
                    from.push((a, fwd, bwd, r0 + (i + 5) % 6, r0 + i));
                }
                free.push(Free { from });
            }
        }
        let np = n + free.len();
        let mut edge = vec![vec![false; np]; np];
        for v in 0..n {
            for &w in &rot[v] {
                edge[v][w] = true;
            }
        }
        let root_ref = rot[root][0];
        Geo { n, root, root_ref, steps, free, edge, di }
    }

    /// Number of points (vertices and isolated vertices).
    pub fn np(&self) -> usize {
        self.n + self.free.len()
    }

    /// Enclosure of an angle given by corners (forward sum, intersected with 2 pi minus the
    /// complementary sum).
    fn angle(b: &[Iv], fwd: &[usize], bwd: &[usize]) -> Iv {
        let mut s = ZERO;
        for &j in fwd {
            s = s.add(b[j]);
        }
        let mut t = ZERO;
        for &j in bwd {
            t = t.add(b[j]);
        }
        let c = Iv::new(TWO_PI_LO, TWO_PI_HI).sub(t);
        s.meet(c)
    }

    /// Centered enclosures of all points: (Y_c enclosure, rho). None if some enclosure is not
    /// usable (empty or infinite).
    pub fn place(&self, b: &[Iv]) -> Option<(Vec<V3>, Vec<f64>)> {
        let (dc, dr) = center(b[self.di])?;
        let id: M3 = [[ONE, ZERO, ZERO], [ZERO, ONE, ZERO], [ZERO, ZERO, ONE]];
        let mut fr: Vec<M3> = vec![id; self.n];
        let mut rho = vec![0.0f64; self.np()];
        for s in &self.steps {
            let (pc, pr) = center(Self::angle(b, &s.fwd, &s.bwd))?;
            fr[s.v] = mmul(&fr[s.from], &step(pc, dc));
            rho[s.v] = up_add(up_add(rho[s.from], pr), dr);
        }
        let mut pos: Vec<V3> = fr.iter().map(|f| [f[0][2], f[1][2], f[2][2]]).collect();
        for fp in &self.free {
            let mut best: Option<(V3, f64)> = None;
            for (a, fwd, bwd, rm, ri) in &fp.from {
                let beta = match crate::deep::tri_angle(b[*rm], b[*ri], b[self.di]) {
                    Ok(x) => x,
                    Err(_) => return None,
                };
                let (pc, pr) = center(Self::angle(b, fwd, bwd).add(beta))?;
                let (rc, rr) = center(b[*ri])?;
                // F(a) Rz(psi) Ry(r) e3 = F(a) (sin r cos psi, sin r sin psi, cos r)
                let (cp, sp) = (Iv::pt(pc).cos(), Iv::pt(pc).sin());
                let (cr, sr) = (Iv::pt(rc).cos(), Iv::pt(rc).sin());
                let loc = [sr.mul(cp), sr.mul(sp), cr];
                let f = &fr[*a];
                let mut y = [ZERO; 3];
                for k in 0..3 {
                    y[k] = f[k][0].mul(loc[0]).add(f[k][1].mul(loc[1])).add(f[k][2].mul(loc[2]));
                }
                let r = up_add(up_add(rho[*a], pr), rr);
                if best.as_ref().map_or(true, |bb| r < bb.1) {
                    best = Some((y, r));
                }
            }
            let (y, r) = best?;
            rho[pos.len()] = r;
            pos.push(y);
        }
        Some((pos, rho))
    }

    /// Local discard: true when some normalised target matches every point within `r`.
    pub fn local(&self, b: &[Iv], tg: &Targets, r: f64) -> bool {
        match self.place(b) {
            Some((pos, rho)) => self.local_at(&pos, &rho, tg, r),
            None => false,
        }
    }

    /// Local discard on placed points (see `place`).
    pub fn local_at(&self, pos: &[V3], rho: &[f64], tg: &Targets, r: f64) -> bool {
        if rho.iter().any(|&x| !(x < r)) {
            return false;
        }
        let np = self.np();
        if np != 15 {
            return false;
        }
        let pm: Vec<[f64; 3]> = pos.iter().map(|p| [p[0].mid(), p[1].mid(), p[2].mid()]).collect();
        'targets: for (t, tm) in tg.t.iter().zip(tg.tm.iter()) {
            let mut used = [false; 15];
            for v in 0..np {
                // nearest target point by midpoints
                let mut bj = 0;
                let mut bd = f64::INFINITY;
                for j in 0..15 {
                    let dd = (pm[v][0] - tm[j][0]).powi(2) + (pm[v][1] - tm[j][1]).powi(2) + (pm[v][2] - tm[j][2]).powi(2);
                    if dd < bd {
                        bd = dd;
                        bj = j;
                    }
                }
                if used[bj] {
                    continue 'targets;
                }
                let mut s = ZERO;
                for k in 0..3 {
                    s = s.add(pos[v][k].sub(t[bj][k]).sqr());
                }
                if !(up_add(s.sqrt().hi, rho[v]) <= r) {
                    continue 'targets;
                }
                used[bj] = true;
            }
            return true;
        }
        false
    }

    /// Closure refutation: true when some edge uv of G has a length provably different from
    /// d (|Y(u) - Y(v)| = 2 sin(d/2) for every realisation), or some isolated vertex P of a full
    /// hexagon has |Y(P) - Y(A_i)| provably different from 2 sin(r_i/2). Edges of the BFS tree
    /// hold by construction; the others are the loop closures of the gluing.
    pub fn close_at(&self, pos: &[V3], rho: &[f64], b: &[Iv]) -> bool {
        let chord = |x: Iv| -> Iv {
            // 2 sin(x/2), increasing on [0, pi]
            if !(x.lo >= 0.0 && x.hi <= 3.0) {
                return Iv::new(f64::NEG_INFINITY, f64::INFINITY);
            }
            Iv::new(Iv::pt(x.lo).scale(0.5).sin().scale(2.0).lo, Iv::pt(x.hi).scale(0.5).sin().scale(2.0).hi)
        };
        let dist = |u: usize, v: usize| -> Iv {
            let mut s = ZERO;
            for k in 0..3 {
                s = s.add(pos[u][k].sub(pos[v][k]).sqr());
            }
            let r = up_add(rho[u], rho[v]);
            let q = s.sqrt();
            Iv::new(Iv::pt(q.lo).sub(Iv::pt(r)).lo, up_add(q.hi, r))
        };
        let cd = chord(b[self.di]);
        for u in 0..self.n {
            for v in u + 1..self.n {
                if self.edge[u][v] {
                    let e = dist(u, v);
                    if e.hi < cd.lo || e.lo > cd.hi {
                        return true;
                    }
                }
            }
        }
        for (k, fp) in self.free.iter().enumerate() {
            let p = self.n + k;
            for (a, _, _, _, ri) in &fp.from {
                let cr = chord(b[*ri]);
                let e = dist(p, *a);
                if e.hi < cr.lo || e.lo > cr.hi {
                    return true;
                }
            }
        }
        false
    }

    /// Pair refutation: true when two points not joined by an edge are provably closer than
    /// the chord 2 sin(d_lo / 2).
    pub fn pair(&self, b: &[Iv]) -> bool {
        match self.place(b) {
            Some((pos, rho)) => self.pair_at(&pos, &rho, b),
            None => false,
        }
    }

    /// Pair refutation on placed points.
    pub fn pair_at(&self, pos: &[V3], rho: &[f64], b: &[Iv]) -> bool {
        let chord = Iv::pt(b[self.di].lo).scale(0.5).sin().scale(2.0).lo;
        let np = self.np();
        for u in 0..np {
            for v in u + 1..np {
                if self.edge[u][v] {
                    continue;
                }
                let mut s = ZERO;
                for k in 0..3 {
                    s = s.add(pos[u][k].sub(pos[v][k]).sqr());
                }
                if up_add(up_add(s.sqrt().hi, rho[u]), rho[v]) < chord {
                    return true;
                }
            }
        }
        false
    }

    /// The root vertex (placed at (0, 0, 1)) and its reference neighbour (placed at
    /// (sin d, 0, cos d)).
    pub fn root_ref(&self) -> (usize, usize) {
        (self.root, self.root_ref)
    }
}
