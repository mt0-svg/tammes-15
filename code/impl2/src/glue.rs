//! Gluing a box into point enclosures, and the discards that use them.
//!
//! Gluing (derivation in Section 6.5 of the paper). BFS tree from a root v0 of minimal
//! eccentricity; ref(v0) = adj[v0][0], ref(v) = BFS parent otherwise. Frames are rotations
//! F(v) with F(v) e3 = Y(v) and F(v) e1 = unit tangent at Y(v) toward Y(ref(v)); F(v0) = I. For a
//! child n of v, with phi = angle at v from ref(v) to n (sum of the corners in rotation order),
//! F(n) = F(v) Rz(phi) Ry(d) Z, Z = diag(-1, -1, 1). A free point P of a full hexagon, anchored at
//! its vertex A_i, is F(A_i) Rz(psi) Ry(r_i) e3 with psi = (angle from ref(A_i) to A_{i-1}) +
//! angle(A_{i-1} A_i P). Every genuine configuration realising the box, rotated so that v0 -> e3
//! and ref(v0) -> half plane y = 0, x > 0, is Y or its mirror image (y -> -y), depending on
//! the orientation of its embedding.
//!
//! Centered enclosure: with centres c (midpoints) of the angle enclosures and radii rad,
//! |Y(v) - Y_c(v)| <= rho(v) = sum over the tree path of (rad(phi) + rad(d)) (+ rad(psi) +
//! rad(r_i) for a free point), because every factor is a rotation and |R(t) - R(s)| <= |t - s| in
//! operator norm, and prod A_i - prod B_i telescopes into terms of norm |A_k - B_k|. Y_c is
//! computed in interval arithmetic from the exact centre values.
//!
//! Local: discard the box if for some target configuration (data/tie_targets.txt, normalised on a
//! directed contact, mirrored or not) there is an injective map of the 15 points to the target
//! points with sup |Y_c(v) - T_j| + rho(v) <= r_local (Theorem 4.1, Section 4).
//! Pair: refute if two points not joined by an edge have sup |Y(u) - Y(v)| < 2 sin(d_lo / 2).
//! Edge: refute if an edge (or a wheel radius) has an enclosure of |Y(u) - Y(v)| disjoint from
//! 2 sin(d / 2) (resp. 2 sin(r_i / 2)).

use crate::elem;
use crate::iv::{dn, up, I};
use crate::model::{Model, VD};

pub type V3 = [I; 3];
pub type M3 = [[I; 3]; 3];

#[derive(Clone, Debug)]
pub struct Target {
    pub pts: Vec<V3>,
}

#[derive(Clone, Debug)]
pub struct GlueOpts {
    pub local: bool,
    pub pair: bool,
    pub edge: bool,
    pub r_local: f64,
    pub targets: Vec<Target>,
    /// Pair and Edge are only tried when max rho is below this
    pub rho_pair: f64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GlueVerdict {
    None,
    Local,
    Pair,
    Edge,
}

#[derive(Clone, Debug)]
enum Step {
    /// child n of vertex v: angle from ref(v) to n given by corner lists
    Vertex { v: usize, n: usize, fwd: Vec<usize>, bwd: Vec<usize> },
    /// free point of wheel w anchored at vertex v; prev = A_{i-1}; radii vars ri (r_i), rp (r_{i-1})
    Free { v: usize, fwd: Vec<usize>, bwd: Vec<usize>, ri: usize, rp: usize },
}

pub struct Glue {
    npts: usize,
    root: usize,
    steps: Vec<Step>,
    /// pairs (p, q) of points that are joined by an edge of G
    edges: Vec<(usize, usize)>,
    /// (free point index, vertex, radius variable)
    spokes: Vec<(usize, usize, usize)>,
    nonedges: Vec<(usize, usize)>,
    o: GlueOpts,
}

fn mat_mul(a: &M3, b: &M3) -> M3 {
    let mut c = [[I::pt(0.0); 3]; 3];
    for i in 0..3 {
        for j in 0..3 {
            c[i][j] = a[i][0] * b[0][j] + a[i][1] * b[1][j] + a[i][2] * b[2][j];
        }
    }
    c
}

/// Rz(phi) Ry(t) Z for point angles (as intervals of the exact centre values).
fn step_mat(phi: f64, t: f64) -> M3 {
    let (sp, cp) = elem::sincos_pt(phi);
    let (st, ct) = elem::sincos_pt(t);
    let z = I::pt(0.0);
    // Rz(phi) = [[c, -s, 0], [s, c, 0], [0, 0, 1]], Ry(t) = [[ct, 0, st], [0, 1, 0], [-st, 0, ct]]
    let rz = [[cp, -sp, z], [sp, cp, z], [z, z, I::pt(1.0)]];
    let ry = [[ct, z, st], [z, I::pt(1.0), z], [-st, z, ct]];
    let mut m = mat_mul(&rz, &ry);
    for row in m.iter_mut() {
        row[0] = -row[0];
        row[1] = -row[1];
    }
    m
}

/// F Rz(phi) Ry(t) e3 = F (st cp, st sp, ct).
fn point_of(f: &M3, phi: f64, t: f64) -> V3 {
    let (sp, cp) = elem::sincos_pt(phi);
    let (st, ct) = elem::sincos_pt(t);
    let w = [st * cp, st * sp, ct];
    let mut y = [I::pt(0.0); 3];
    for i in 0..3 {
        y[i] = f[i][0] * w[0] + f[i][1] * w[1] + f[i][2] * w[2];
    }
    y
}

fn dist_hi(a: &V3, b: &V3) -> f64 {
    let dx = a[0] - b[0];
    let dy = a[1] - b[1];
    let dz = a[2] - b[2];
    (dx.sqr() + dy.sqr() + dz.sqr()).sqrt().unwrap().hi
}

fn dist(a: &V3, b: &V3) -> I {
    let dx = a[0] - b[0];
    let dy = a[1] - b[1];
    let dz = a[2] - b[2];
    (dx.sqr() + dy.sqr() + dz.sqr()).sqrt().unwrap()
}

impl Glue {
    pub fn new(m: &Model, o: GlueOpts) -> Glue {
        let g = &m.g;
        let n = g.n;
        // root of minimal eccentricity
        let bfs = |s: usize| -> (Vec<usize>, Vec<usize>, Vec<usize>) {
            let mut par = vec![usize::MAX; n];
            let mut dep = vec![usize::MAX; n];
            let mut order = vec![s];
            dep[s] = 0;
            let mut h = 0;
            while h < order.len() {
                let v = order[h];
                h += 1;
                for &w in &g.adj[v] {
                    if dep[w] == usize::MAX {
                        dep[w] = dep[v] + 1;
                        par[w] = v;
                        order.push(w);
                    }
                }
            }
            assert_eq!(order.len(), n, "graph is not connected");
            (par, dep, order)
        };
        let mut root = 0;
        let mut bestecc = usize::MAX;
        for s in 0..n {
            let (_, dep, _) = bfs(s);
            let e = *dep.iter().max().unwrap();
            if e < bestecc {
                bestecc = e;
                root = s;
            }
        }
        let (par, dep, order) = bfs(root);
        let refn = |v: usize| -> usize {
            if v == root {
                g.adj[v][0]
            } else {
                par[v]
            }
        };
        let cvar = |v: usize, t: usize| -> usize {
            let (f, i) = g.corner_face[v][t];
            m.corner_var[f][i]
        };
        // corner lists from ref(v) to neighbour at index j (forward) and the complement
        let lists = |v: usize, j: usize| -> (Vec<usize>, Vec<usize>) {
            let deg = g.adj[v].len();
            let jr = g.adj[v].iter().position(|&x| x == refn(v)).unwrap();
            let mut fwd = Vec::new();
            let mut t = jr;
            while t != j {
                fwd.push(cvar(v, t));
                t = (t + 1) % deg;
            }
            // the complementary corners (all of them when j = jr: a full turn)
            let bwd: Vec<usize> = (0..deg - fwd.len()).map(|k| cvar(v, (j + k) % deg)).collect();
            (fwd, bwd)
        };
        let mut steps = Vec::new();
        for &v in &order {
            for (j, &w) in g.adj[v].iter().enumerate() {
                if w != root && par[w] == v {
                    let (fwd, bwd) = lists(v, j);
                    steps.push(Step::Vertex { v, n: w, fwd, bwd });
                }
            }
        }
        // free points, points n.. in the order of m.wheels
        let mut spokes = Vec::new();
        for (wi, (f, rv)) in m.wheels.iter().enumerate() {
            let cyc = &g.faces[*f];
            // anchor: vertex of minimal depth
            let i = (0..6).min_by_key(|&i| dep[cyc[i]]).unwrap();
            let v = cyc[i];
            let prev = cyc[(i + 5) % 6];
            let j = g.adj[v].iter().position(|&x| x == prev).unwrap();
            debug_assert_eq!(g.corner_face[v][j], (*f, i));
            let (fwd, bwd) = lists(v, j);
            steps.push(Step::Free { v, fwd, bwd, ri: rv[i], rp: rv[(i + 5) % 6] });
            for k in 0..6 {
                spokes.push((n + wi, cyc[k], rv[k]));
            }
        }
        let npts = n + m.wheels.len();
        let mut edges = Vec::new();
        let mut nonedges = Vec::new();
        for p in 0..npts {
            for q in p + 1..npts {
                if p < n && q < n && g.is_edge(p, q) {
                    edges.push((p, q));
                } else {
                    nonedges.push((p, q));
                }
            }
        }
        Glue { npts, root, steps, edges, spokes, nonedges, o }
    }

    /// Centre points Y_c (enclosures) and radii rho for the box b; None if some angle
    /// enclosure is empty or unbounded.
    pub fn place(&self, b: &[I]) -> Option<(Vec<V3>, Vec<f64>)> {
        let n = self.npts;
        let mut y = vec![[I::pt(0.0); 3]; n];
        let mut rho = vec![0.0f64; n];
        let mut fr: Vec<Option<M3>> = vec![None; n];
        let id = [[I::pt(1.0), I::pt(0.0), I::pt(0.0)], [I::pt(0.0), I::pt(1.0), I::pt(0.0)], [I::pt(0.0), I::pt(0.0), I::pt(1.0)]];
        fr[self.root] = Some(id);
        y[self.root] = [I::pt(0.0), I::pt(0.0), I::pt(1.0)];
        let d = b[VD];
        let cd = d.mid();
        let rd = d.rad_about(cd);
        let tp = I::two_pi();
        let angle = |fwd: &Vec<usize>, bwd: &Vec<usize>| -> Option<I> {
            let mut s = I::pt(0.0);
            for &c in fwd {
                s = s + b[c];
            }
            let mut t = I::pt(0.0);
            for &c in bwd {
                t = t + b[c];
            }
            let a = s.meet(tp - t)?;
            if !a.lo.is_finite() || !a.hi.is_finite() {
                return None;
            }
            Some(a)
        };
        let mut nfree = self.npts - self.spokes.len() / 6;
        for st in &self.steps {
            match st {
                Step::Vertex { v, n: w, fwd, bwd } => {
                    let a = angle(fwd, bwd)?;
                    let ca = a.mid();
                    let ra = a.rad_about(ca);
                    let f = fr[*v].as_ref().unwrap();
                    y[*w] = point_of(f, ca, cd);
                    fr[*w] = Some(mat_mul(f, &step_mat(ca, cd)));
                    rho[*w] = up(up(rho[*v] + ra) + rd);
                }
                Step::Free { v, fwd, bwd, ri, rp } => {
                    let a = angle(fwd, bwd)?;
                    // angle at A_i in the triangle (P, A_{i-1}, A_i), opposite r_{i-1}
                    let (sd, cdd) = elem::sincos(d);
                    let (sb, cb) = elem::sincos(b[*ri]);
                    let (_, ca_) = elem::sincos(b[*rp]);
                    let nu = elem::acos((ca_ - cb * cdd) / (sb * sd))?;
                    let psi = a + nu;
                    let cpsi = psi.mid();
                    let rpsi = psi.rad_about(cpsi);
                    let r = b[*ri];
                    let cr = r.mid();
                    let rr = r.rad_about(cr);
                    let f = fr[*v].as_ref().unwrap();
                    y[nfree] = point_of(f, cpsi, cr);
                    rho[nfree] = up(up(rho[*v] + rpsi) + rr);
                    nfree += 1;
                }
            }
        }
        Some((y, rho))
    }

    pub fn test(&self, b: &[I]) -> GlueVerdict {
        if !(self.o.local || self.o.pair || self.o.edge) {
            return GlueVerdict::None;
        }
        let (y, rho) = match self.place(b) {
            Some(x) => x,
            None => return GlueVerdict::None,
        };
        let maxrho = rho.iter().cloned().fold(0.0, f64::max);
        if maxrho <= self.o.rho_pair {
            if self.o.pair {
                let dl = b[VD].lo;
                let chord = (elem::sin(I::pt(dl * 0.5)) * 2.0).lo; // 2 sin(d_lo/2), rounded down
                for &(p, q) in &self.nonedges {
                    let s = up(up(dist_hi(&y[p], &y[q]) + rho[p]) + rho[q]);
                    if s < chord {
                        return GlueVerdict::Pair;
                    }
                }
            }
            if self.o.edge {
                let ch = elem::sin(b[VD] * 0.5) * 2.0;
                for &(p, q) in &self.edges {
                    let dd = dist(&y[p], &y[q]);
                    let e = rho[p] + rho[q];
                    let enc = I::new(dn(dd.lo - e), up(dd.hi + e));
                    if enc.meet(ch).is_none() {
                        return GlueVerdict::Edge;
                    }
                }
                for &(p, v, rv) in &self.spokes {
                    let ch = elem::sin(b[rv] * 0.5) * 2.0;
                    let dd = dist(&y[p], &y[v]);
                    let e = rho[p] + rho[v];
                    let enc = I::new(dn(dd.lo - e), up(dd.hi + e));
                    if enc.meet(ch).is_none() {
                        return GlueVerdict::Edge;
                    }
                }
            }
        }
        if self.o.local && maxrho < self.o.r_local && self.npts == 15 {
            if self.local(&y, &rho) {
                return GlueVerdict::Local;
            }
        }
        GlueVerdict::None
    }

    fn local(&self, y: &[V3], rho: &[f64]) -> bool {
        let r = self.o.r_local;
        'targets: for t in &self.o.targets {
            let mut used = [false; 15];
            let mut map = [usize::MAX; 15];
            for p in 0..15 {
                let mut found = usize::MAX;
                for j in 0..15 {
                    if used[j] {
                        continue;
                    }
                    let s = up(dist_hi(&y[p], &t.pts[j]) + rho[p]);
                    if s <= r {
                        found = j;
                        break;
                    }
                }
                if found == usize::MAX {
                    continue 'targets;
                }
                used[found] = true;
                map[p] = found;
            }
            return true;
        }
        false
    }
}

/// Parse data/tie_targets.txt and build the normalised targets: for each configuration, each
/// directed contact (a, b) and each orientation, the rotation M with M p_a = e3 and M p_b in the
/// half plane y = 0, x > 0 (rows: e1' = unit tangent at p_a toward p_b, e2' = p_a x e1',
/// e3' = p_a), followed by the reflection y -> -y for the mirrored targets.
pub fn load_targets(text: &str) -> Vec<Target> {
    let mut confs: Vec<(Vec<V3>, Vec<(usize, usize)>)> = Vec::new();
    let mut cur: Vec<V3> = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with("conf") {
            cur.clear();
            continue;
        }
        if let Some(rest) = line.strip_prefix("contacts") {
            let nums: Vec<usize> = rest.split_whitespace().map(|s| s.parse().unwrap()).collect();
            let pairs: Vec<(usize, usize)> = nums.chunks(2).map(|c| (c[0], c[1])).collect();
            assert_eq!(cur.len(), 15);
            assert_eq!(pairs.len(), 30);
            confs.push((cur.clone(), pairs));
            continue;
        }
        let tok: Vec<&str> = line.split_whitespace().collect();
        assert_eq!(tok.len(), 6, "bad target line {line}");
        let mut p = [I::pt(0.0); 3];
        for k in 0..3 {
            let mid = crate::mp::dec(tok[2 * k]);
            let rad = crate::mp::dec(tok[2 * k + 1]);
            p[k] = I::new(dn(mid.lo - rad.hi), up(mid.hi + rad.hi));
        }
        cur.push(p);
    }
    assert_eq!(confs.len(), 8);
    let dot = |a: &V3, b: &V3| a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
    let mut out = Vec::new();
    for (pts, pairs) in &confs {
        for &(i, j) in pairs {
            for &(a, bb) in &[(i, j), (j, i)] {
                let pa = pts[a];
                let pb = pts[bb];
                let c = dot(&pa, &pb);
                let t = [pb[0] - c * pa[0], pb[1] - c * pa[1], pb[2] - c * pa[2]];
                let nt = dot(&t, &t).sqrt().unwrap();
                let e1 = [t[0] / nt, t[1] / nt, t[2] / nt];
                let e2 = [pa[1] * e1[2] - pa[2] * e1[1], pa[2] * e1[0] - pa[0] * e1[2], pa[0] * e1[1] - pa[1] * e1[0]];
                let e3 = pa;
                for mirror in [false, true] {
                    let mut q = Vec::with_capacity(15);
                    for p in pts {
                        let y = dot(&e2, p);
                        q.push([dot(&e1, p), if mirror { -y } else { y }, dot(&e3, p)]);
                    }
                    // the image of p_a is e3 and p_b is in the half plane y = 0, x > 0; the map is
                    // reordered so that target point 0 is p_a and target point 1 is p_b
                    let mut ord = vec![a, bb];
                    ord.extend((0..15).filter(|&k| k != a && k != bb));
                    out.push(Target { pts: ord.iter().map(|&k| q[k]).collect() });
                }
            }
        }
    }
    out
}
