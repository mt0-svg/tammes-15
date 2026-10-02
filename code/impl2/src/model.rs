//! The per-case constraint system: variables, domains, explicit face relations, linear rows.
//!
//! Variables: 0 = d, 1 = a = alpha(d) (the corner of every triangle), then per face: rhombus x
//! (positions 0, 2) and y (positions 1, 3) (opposite corners of a rhombus are equal, Section 3 of
//! the paper), pentagon and hexagon corners one each; then per full hexagon (a hexagon holding a
//! free point P) six radii r_i = |P A_i| and six auxiliary angles theta_i = angle A_i P A_{i+1}.

use crate::faces::Fam;
use crate::graph::Graph;
use crate::iv::{I, PI_HI};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Eq,
    Ge,
}

#[derive(Clone, Debug)]
pub struct Rel {
    pub fam: Fam,
    pub ins: [usize; 4],
    pub outs: [usize; 3],
    pub kinds: [Kind; 3],
}

/// lo <= sum coef_j x_j <= hi
#[derive(Clone, Debug)]
pub struct Lin {
    pub terms: Vec<(usize, f64)>,
    pub lo: f64,
    pub hi: f64,
}

#[derive(Clone, Debug)]
pub enum Con {
    Rel(Rel),
    Lin(Lin),
}

#[derive(Clone, Debug)]
pub struct Params {
    pub dlo: f64,
    pub dhi: f64,
    pub alo: f64,
    pub ahi: f64,
}

#[derive(Clone, Debug)]
pub struct Model {
    pub g: Graph,
    pub full: Vec<usize>,
    pub nv: usize,
    pub init: Vec<I>,
    pub branch: Vec<bool>,
    pub cons: Vec<Con>,
    /// corner_var[f][i]: variable of the corner of face f at position i
    pub corner_var: Vec<Vec<usize>>,
    /// per full hexagon: (face, radius variables in face order)
    pub wheels: Vec<(usize, [usize; 6])>,
    pub names: Vec<String>,
}

pub const VD: usize = 0;
pub const VA: usize = 1;

impl Model {
    /// Build the system of graph g with free points in the hexagons `full` (face indices).
    pub fn new(g: &Graph, full: &[usize], p: &Params) -> Model {
        let mut init = vec![I::new(p.dlo, p.dhi), I::new(p.alo, p.ahi)];
        let mut branch = vec![true, false];
        let mut names = vec!["d".to_string(), "a".to_string()];
        let mut corner_var = Vec::new();
        let mut cons = Vec::new();
        let corner_dom = I::new(p.alo, PI_HI);
        let s_hi = {
            let c = crate::elem::cos(I::pt(p.dhi));
            let t = I::pt(1.0) / c.sqrt().unwrap();
            (crate::elem::atan(t) * 4.0).hi
        };
        for (fi, f) in g.faces.iter().enumerate() {
            let m = f.len();
            let mut cv = vec![0usize; m];
            match m {
                3 => {
                    for c in cv.iter_mut() {
                        *c = VA;
                    }
                }
                4 => {
                    let x = init.len();
                    let rho_dom = I::new(p.alo, (I::pt(p.ahi) * 2.0).hi.min(PI_HI));
                    init.push(rho_dom);
                    init.push(rho_dom);
                    branch.push(true);
                    branch.push(true);
                    names.push(format!("f{fi}x"));
                    names.push(format!("f{fi}y"));
                    cv = vec![x, x + 1, x, x + 1];
                }
                5 | 6 => {
                    for (i, c) in cv.iter_mut().enumerate() {
                        *c = init.len();
                        init.push(corner_dom);
                        branch.push(true);
                        names.push(format!("f{fi}u{i}"));
                    }
                }
                _ => panic!("face size {m}"),
            }
            corner_var.push(cv);
        }
        // alpha relation (both directions)
        cons.push(Con::Rel(Rel { fam: Fam::Alpha, ins: [VD, 0, 0, 0], outs: [VA, 0, 0], kinds: [Kind::Eq; 3] }));
        cons.push(Con::Rel(Rel { fam: Fam::AlphaInv, ins: [VA, 0, 0, 0], outs: [VD, 0, 0], kinds: [Kind::Eq; 3] }));
        // vertex sums
        for v in 0..g.n {
            let mut terms: Vec<(usize, f64)> = Vec::new();
            for j in 0..g.adj[v].len() {
                let (f, i) = g.corner_face[v][j];
                let var = corner_var[f][i];
                if let Some(t) = terms.iter_mut().find(|t| t.0 == var) {
                    t.1 += 1.0;
                } else {
                    terms.push((var, 1.0));
                }
            }
            let tp = I::two_pi();
            cons.push(Con::Lin(Lin { terms, lo: tp.lo, hi: tp.hi }));
        }
        for (fi, f) in g.faces.iter().enumerate() {
            let m = f.len();
            let cv = &corner_var[fi];
            let u = |k: i64| cv[(k.rem_euclid(m as i64)) as usize];
            match m {
                4 => {
                    let (x, y) = (cv[0], cv[1]);
                    cons.push(Con::Rel(Rel { fam: Fam::RhoY, ins: [VD, x, 0, 0], outs: [y, 0, 0], kinds: [Kind::Eq; 3] }));
                    cons.push(Con::Rel(Rel { fam: Fam::RhoY, ins: [VD, y, 0, 0], outs: [x, 0, 0], kinds: [Kind::Eq; 3] }));
                    cons.push(Con::Rel(Rel { fam: Fam::RhoD, ins: [x, y, 0, 0], outs: [VD, 0, 0], kinds: [Kind::Eq; 3] }));
                    // x, y in [a, 2a], x + y >= 3a (Section 5.2)
                    for &w in &[x, y] {
                        cons.push(Con::Lin(Lin { terms: vec![(w, 1.0), (VA, -1.0)], lo: 0.0, hi: f64::INFINITY }));
                        cons.push(Con::Lin(Lin { terms: vec![(w, 1.0), (VA, -2.0)], lo: f64::NEG_INFINITY, hi: 0.0 }));
                    }
                    cons.push(Con::Lin(Lin { terms: vec![(x, 1.0), (y, 1.0), (VA, -3.0)], lo: 0.0, hi: f64::INFINITY }));
                    // x + y <= S(dhi) = 4 atan(1/sqrt(cos dhi)) (max of x + rho(x, d), increasing in d)
                    cons.push(Con::Lin(Lin { terms: vec![(x, 1.0), (y, 1.0)], lo: f64::NEG_INFINITY, hi: s_hi }));
                }
                5 => {
                    for w in cv.iter() {
                        cons.push(Con::Lin(Lin { terms: vec![(*w, 1.0), (VA, -1.0)], lo: 0.0, hi: f64::INFINITY }));
                    }
                    for i in 0..5i64 {
                        cons.push(Con::Rel(Rel {
                            fam: Fam::PentSplit,
                            ins: [VD, u(i + 2), u(i + 3), 0],
                            outs: [u(i), u(i + 1), u(i - 1)],
                            kinds: [Kind::Eq; 3],
                        }));
                        cons.push(Con::Rel(Rel {
                            fam: Fam::PentFan,
                            ins: [VD, u(i + 1), u(i - 1), 0],
                            outs: [u(i), u(i + 2), u(i - 2)],
                            kinds: [Kind::Eq; 3],
                        }));
                    }
                }
                6 => {
                    for w in cv.iter() {
                        cons.push(Con::Lin(Lin { terms: vec![(*w, 1.0), (VA, -1.0)], lo: 0.0, hi: f64::INFINITY }));
                    }
                    for p0 in 0..2i64 {
                        cons.push(Con::Rel(Rel {
                            fam: Fam::HexAlt,
                            ins: [VD, u(p0 + 1), u(p0 + 3), u(p0 + 5)],
                            outs: [u(p0), u(p0 + 2), u(p0 + 4)],
                            kinds: [Kind::Eq; 3],
                        }));
                    }
                    for i in 0..6i64 {
                        cons.push(Con::Rel(Rel {
                            fam: Fam::HexChain5,
                            ins: [VD, u(i + 1), u(i + 2), u(i + 3)],
                            outs: [u(i), u(i + 4), u(i + 5)],
                            kinds: [Kind::Eq; 3],
                        }));
                        for s in [1i64, -1] {
                            cons.push(Con::Rel(Rel {
                                fam: Fam::HexC4Iso,
                                ins: [VD, u(i + s), u(i + 2 * s), u(i + 4 * s)],
                                outs: [u(i), u(i + 3 * s), u(i + 5 * s)],
                                kinds: [Kind::Eq; 3],
                            }));
                            // |A_i A_{i+3s}| >= d: u_{i+2s} >= L(u_{i+s})
                            cons.push(Con::Rel(Rel {
                                fam: Fam::HexLong,
                                ins: [VD, u(i + s), 0, 0],
                                outs: [u(i + 2 * s), 0, 0],
                                kinds: [Kind::Ge; 3],
                            }));
                        }
                    }
                }
                _ => {}
            }
        }
        // wheels
        let mut wheels = Vec::new();
        for &fi in full {
            assert_eq!(g.faces[fi].len(), 6, "a free point must lie in a hexagon");
            let cv = corner_var[fi].clone();
            let r0 = init.len();
            let rdom = I::new(p.dlo, (I::pt(p.dhi) * 3.0).hi.min(PI_HI));
            for i in 0..6 {
                init.push(rdom);
                branch.push(true);
                names.push(format!("f{fi}r{i}"));
            }
            let t0 = init.len();
            for i in 0..6 {
                init.push(I::new(0.0, PI_HI));
                branch.push(false);
                names.push(format!("f{fi}t{i}"));
            }
            let r = |k: i64| r0 + (k.rem_euclid(6)) as usize;
            for i in 0..6i64 {
                let ui = cv[i as usize];
                // r_i >= d, r_i <= 3d
                cons.push(Con::Lin(Lin { terms: vec![(r(i), 1.0), (VD, -1.0)], lo: 0.0, hi: f64::INFINITY }));
                cons.push(Con::Lin(Lin { terms: vec![(r(i), 1.0), (VD, -3.0)], lo: f64::NEG_INFINITY, hi: 0.0 }));
                cons.push(Con::Rel(Rel { fam: Fam::WCorner, ins: [VD, r(i - 1), r(i), r(i + 1)], outs: [ui, 0, 0], kinds: [Kind::Eq; 3] }));
                cons.push(Con::Rel(Rel { fam: Fam::WTheta, ins: [VD, r(i), r(i + 1), 0], outs: [t0 + i as usize, 0, 0], kinds: [Kind::Eq; 3] }));
                cons.push(Con::Rel(Rel { fam: Fam::WBack, ins: [VD, r(i - 1), r(i), ui], outs: [r(i + 1), 0, 0], kinds: [Kind::Eq; 3] }));
                cons.push(Con::Rel(Rel { fam: Fam::WBack, ins: [VD, r(i + 1), r(i), ui], outs: [r(i - 1), 0, 0], kinds: [Kind::Eq; 3] }));
            }
            let tp = I::two_pi();
            cons.push(Con::Lin(Lin { terms: (0..6).map(|i| (t0 + i, 1.0)).collect(), lo: tp.lo, hi: tp.hi }));
            let mut rv = [0usize; 6];
            for i in 0..6 {
                rv[i] = r0 + i;
            }
            wheels.push((fi, rv));
        }
        Model { g: g.clone(), full: full.to_vec(), nv: init.len(), init, branch, cons, corner_var, wheels, names }
    }

    /// Drop the explicit relations of the given families (names as in the Fam enum, e.g.
    /// "HexC4Iso"). Fewer constraints can only weaken the contraction: soundness is unchanged.
    pub fn drop_families(&mut self, names: &[String]) {
        self.cons.retain(|c| match c {
            Con::Rel(r) => !names.iter().any(|n| *n == format!("{:?}", r.fam)),
            Con::Lin(_) => true,
        });
    }

    /// The model restricted to the relation system `RelSys` of the Lean hypothesis D3
    /// (lean/Tammes15/Hyps/Case.lean): drops the families of OUTSIDE_RELSYS.
    pub fn restrict_to_relsys(&mut self) {
        let names: Vec<String> = OUTSIDE_RELSYS.iter().map(|f| format!("{f:?}")).collect();
        self.drop_families(&names);
        assert!(!self.has_family(&OUTSIDE_RELSYS), "a family outside RelSys is left in the model");
    }

    /// true if some explicit relation of the model belongs to one of the families.
    pub fn has_family(&self, fams: &[Fam]) -> bool {
        self.cons.iter().any(|c| matches!(c, Con::Rel(r) if fams.contains(&r.fam)))
    }
}

/// Face families of the model that are not relations of `RelSys`: each holds for a convex
/// equilateral polygon, but follows from the pentagon fans (T5), hexagon triangles (T6) and long
/// diagonals (T7) of `RelSys` only through a realisability lemma of the face that is not stated.
/// Every other relation of the model is a field of `RelSys` or an identity derived from one
/// (code/impl2/README.md).
pub const OUTSIDE_RELSYS: [Fam; 3] = [Fam::PentSplit, Fam::HexChain5, Fam::HexC4Iso];

impl Model {
    /// Branch only on a set of variables that determines the configuration of every face
    /// given d: d, the rhombus x, pentagon corners 0 and 1 (PentSplit), hexagon corners 0, 1, 2
    /// (HexChain5), radii r_0, r_1 of each wheel. Only the search order changes: a box whose
    /// branchable variables are all narrow is still reported UNRESOLVED, never discarded.
    pub fn branch_on_parameters(&mut self) {
        let mut br = vec![false; self.nv];
        br[VD] = true;
        for (fi, f) in self.g.faces.iter().enumerate() {
            let cv = &self.corner_var[fi];
            match f.len() {
                4 => br[cv[0]] = true,
                5 => {
                    br[cv[0]] = true;
                    br[cv[1]] = true;
                }
                6 => {
                    for k in 0..3 {
                        br[cv[k]] = true;
                    }
                }
                _ => {}
            }
        }
        for (_, rv) in &self.wheels {
            br[rv[0]] = true;
            br[rv[1]] = true;
        }
        self.branch = br;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Prism over an m-gon: vertices 0..m on top, m..2m below; faces two m-gons and m squares.
    fn prism(m: usize) -> Graph {
        let mut adj = vec![Vec::new(); 2 * m];
        for i in 0..m {
            adj[i] = vec![(i + 1) % m, i + m, (i + m - 1) % m];
            adj[m + i] = vec![m + (i + m - 1) % m, i, m + (i + 1) % m];
        }
        Graph::from_adj(adj)
    }

    fn count(m: &Model) -> std::collections::BTreeMap<String, usize> {
        let mut c = std::collections::BTreeMap::new();
        for k in &m.cons {
            let name = match k {
                Con::Rel(r) => format!("{:?}", r.fam),
                Con::Lin(_) => "Lin".to_string(),
            };
            *c.entry(name).or_insert(0) += 1;
        }
        c
    }

    #[test]
    fn relsys_drops_exactly_the_three_families() {
        let p = crate::consts::params(crate::consts::DLO_DEG, crate::consts::DHI_DEG);
        for (sides, full) in [(5usize, false), (6, false), (6, true)] {
            let g = prism(sides);
            assert!(g.n + g.faces.len() == g.nedges() + 2);
            let hexes: Vec<usize> = (0..g.faces.len()).filter(|&f| g.faces[f].len() == 6).collect();
            let fl: Vec<usize> = if full { vec![hexes[0]] } else { vec![] };
            let m0 = Model::new(&g, &fl, &p);
            let mut m1 = m0.clone();
            m1.restrict_to_relsys();
            let (c0, c1) = (count(&m0), count(&m1));
            let get = |c: &std::collections::BTreeMap<String, usize>, k: &str| *c.get(k).unwrap_or(&0);
            if sides == 5 {
                assert_eq!(get(&c0, "PentSplit"), 10);
                assert_eq!(get(&c0, "PentFan"), 10);
            } else {
                assert_eq!(get(&c0, "HexChain5"), 12);
                assert_eq!(get(&c0, "HexC4Iso"), 24);
                assert_eq!(get(&c0, "HexAlt"), 4);
                assert_eq!(get(&c0, "HexLong"), 24);
            }
            for f in OUTSIDE_RELSYS {
                assert_eq!(get(&c1, &format!("{f:?}")), 0);
            }
            for (k, v) in &c0 {
                if !OUTSIDE_RELSYS.iter().any(|f| format!("{f:?}") == *k) {
                    assert_eq!(get(&c1, k), *v, "family {k} changed");
                }
            }
            if full {
                assert_eq!(get(&c1, "WCorner"), 6);
                assert_eq!(get(&c1, "WBack"), 12);
            }
            assert!(m0.has_family(&OUTSIDE_RELSYS) && !m1.has_family(&OUTSIDE_RELSYS));
            eprintln!("prism {sides} full {full}: before {c0:?} after {c1:?}");
        }
    }
}
