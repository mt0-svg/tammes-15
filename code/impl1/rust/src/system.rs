//! Linear system attached to a candidate contact graph (level 1 of the Musin-Tarasov scheme).
//!
//! Variables: v0 = a (the angle alpha(d) of the equilateral triangle of side d), and the face
//! angles. Triangle angles are identified with a. A rhombus (quadrilateral face) has two
//! variables x (corners 0, 2) and y (corners 1, 3). Pentagon and hexagon corners have one
//! variable each. Every row is lo <= sum c_j v_j <= hi; every variable has a finite box.
//! All constants are outward-rounded enclosures, so each row is a valid consequence of the
//! geometry of an irreducible contact graph with psi(X) = d in [dlo, dhi]:
//!   vertex rows      sum of the angles at a vertex = 2 pi
//!   rhombus rows     x + y >= 3a (chord), x + y <= shi, a <= x <= 2a, tangent cuts y - c x <= c0
//!   pentagon/hexagon a <= u <= pi, optional face inequalities from the parameter file.

use crate::graph::Faces;
use crate::iv::*;
use crate::params::Params;

#[derive(Clone, Debug, Default)]
pub struct Sys {
    pub nvar: usize,
    pub lo: Vec<f64>,
    pub hi: Vec<f64>,
    pub rs: Vec<u32>, // row starts into terms, len = nrows + 1
    pub tv: Vec<u32>,
    pub tc: Vec<f64>,
    pub rlo: Vec<f64>,
    pub rhi: Vec<f64>,
    /// variable of each corner: cvar[f][p]
    pub cvar: Vec<Vec<u32>>,
    pub uses_uncertified: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reject {
    Degree,
    FaceSize,
}

#[derive(Clone, Copy, Debug)]
pub struct Opts {
    pub use_cuts: bool,
    pub use_face_ineq: bool,
}

impl Default for Opts {
    fn default() -> Self {
        Opts { use_cuts: true, use_face_ineq: true }
    }
}

impl Sys {
    pub fn nrows(&self) -> usize {
        self.rlo.len()
    }

    fn clear(&mut self) {
        self.nvar = 0;
        self.lo.clear();
        self.hi.clear();
        self.rs.clear();
        self.rs.push(0);
        self.tv.clear();
        self.tc.clear();
        self.rlo.clear();
        self.rhi.clear();
        self.cvar.clear();
        self.uses_uncertified = false;
    }

    fn var(&mut self, lo: f64, hi: f64) -> u32 {
        self.lo.push(lo);
        self.hi.push(hi);
        self.nvar += 1;
        (self.nvar - 1) as u32
    }

    fn row(&mut self, terms: &[(u32, f64)], lo: f64, hi: f64) {
        for &(v, c) in terms {
            // merge repeated variables
            let s = *self.rs.last().unwrap() as usize;
            if let Some(k) = (s..self.tv.len()).find(|&k| self.tv[k] == v) {
                self.tc[k] += c;
            } else {
                self.tv.push(v);
                self.tc.push(c);
            }
        }
        self.rs.push(self.tv.len() as u32);
        self.rlo.push(lo);
        self.rhi.push(hi);
    }

    /// Builds the level-1 system. `iso_hex[f]` marks hexagons containing an isolated vertex.
    pub fn build(&mut self, fc: &Faces, p: &Params, o: Opts, iso_hex: Option<&[bool]>) -> Result<(), Reject> {
        self.clear();
        for at in &fc.at {
            if at.len() > 5 {
                return Err(Reject::Degree);
            }
        }
        let a = self.var(p.alo, p.ahi);
        let two_ahi = mul_up(2.0, p.ahi);
        let inf = f64::INFINITY;
        let ninf = f64::NEG_INFINITY;
        for (f, cyc) in fc.cyc.iter().enumerate() {
            let m = cyc.len();
            let mut cv = Vec::with_capacity(m);
            match m {
                3 => cv.extend([a, a, a]),
                4 => {
                    let x = self.var(p.alo, two_ahi);
                    let y = self.var(p.alo, two_ahi);
                    cv.extend([x, y, x, y]);
                    self.row(&[(x, 1.0), (y, 1.0), (a, -3.0)], 0.0, inf);
                    self.row(&[(x, 1.0), (y, 1.0)], ninf, p.shi);
                    for &z in &[x, y] {
                        self.row(&[(z, 1.0), (a, -1.0)], 0.0, inf);
                        self.row(&[(z, 1.0), (a, -2.0)], ninf, 0.0);
                    }
                    if o.use_cuts {
                        for k in 0..p.cuts.len() {
                            let (c, _) = p.cuts[k];
                            let c0 = p.cut_c0(k);
                            self.row(&[(y, 1.0), (x, -c)], ninf, c0);
                            self.row(&[(x, 1.0), (y, -c)], ninf, c0);
                        }
                    }
                }
                5 | 6 => {
                    for _ in 0..m {
                        let u = self.var(p.alo, PI_HI);
                        cv.push(u);
                        self.row(&[(u, 1.0), (a, -1.0)], 0.0, inf);
                    }
                    let full = m == 6 && iso_hex.map_or(false, |h| h[f]);
                    let ineqs = if m == 5 { &p.pent } else if full { &p.hexf } else { &p.hex };
                    if full {
                        if let Some(s) = p.fullhex_sum_lo {
                            let t: Vec<(u32, f64)> = cv.iter().map(|&u| (u, 1.0)).collect();
                            self.row(&t, s, inf);
                        }
                    }
                    if o.use_face_ineq {
                        for q in ineqs {
                            if !q.certified {
                                self.uses_uncertified = true;
                            }
                            for s in 0..m {
                                for dir in [1isize, -1] {
                                    let t: Vec<(u32, f64)> = (0..m)
                                        .map(|i| {
                                            let idx = ((s as isize + dir * i as isize).rem_euclid(m as isize)) as usize;
                                            (cv[idx], q.w[i])
                                        })
                                        .collect();
                                    self.row(&t, q.lo, q.hi);
                                }
                            }
                        }
                    }
                }
                _ => return Err(Reject::FaceSize),
            }
            self.cvar.push(cv);
        }
        // vertex rows
        for v in 0..fc.at.len() {
            let t: Vec<(u32, f64)> = fc.at[v].iter().map(|&(f, pos)| (self.cvar[f as usize][pos as usize], 1.0)).collect();
            self.row(&t, TWO_PI_LO, TWO_PI_HI);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fbbt {
    Infeasible,
    Open,
}

/// Feasibility-based bound tightening with outward rounding. Returns Infeasible only when the
/// system has no real solution (rigorous). Tightens `lo`/`hi` in place.
///
/// For a row with terms c_j v_j, m_j = cmin(c_j, lo_j, hi_j) and M_j = cmax(...) are f64 bounds
/// of the terms. smin (sum of the m_j with downward rounding) is <= the real sum of the m_j, so
/// sub_dn(smin, m_k) is a valid lower bound of the sum of the other terms; same for the upper
/// side. The bounds of the row's variables are read once per row (updates made while
/// processing a row are used from the next row on); this only weakens a step, never its
/// validity.
pub fn fbbt(s: &mut Sys, max_sweeps: usize, tol: f64) -> Fbbt {
    let nr = s.nrows();
    let mut mn: Vec<f64> = Vec::with_capacity(8);
    let mut mx: Vec<f64> = Vec::with_capacity(8);
    for _ in 0..max_sweeps {
        let mut changed = 0.0f64;
        for r in 0..nr {
            let (b, e) = (s.rs[r] as usize, s.rs[r + 1] as usize);
            let (rlo, rhi) = (s.rlo[r], s.rhi[r]);
            mn.clear();
            mx.clear();
            let mut smin = 0.0;
            let mut smax = 0.0;
            for k in b..e {
                let (v, c) = (s.tv[k] as usize, s.tc[k]);
                let (a, z) = (cmin(c, s.lo[v], s.hi[v]), cmax(c, s.lo[v], s.hi[v]));
                mn.push(a);
                mx.push(z);
                smin = add_dn(smin, a);
                smax = add_up(smax, z);
            }
            if smin > rhi || smax < rlo {
                return Fbbt::Infeasible;
            }
            for k in b..e {
                let (v, c) = (s.tv[k] as usize, s.tc[k]);
                if c == 0.0 {
                    continue;
                }
                // bounds on the sum of the other terms
                let omin = sub_dn(smin, mn[k - b]);
                let omax = sub_up(smax, mx[k - b]);
                // rlo - omax <= c v <= rhi - omin
                let cup = if rhi.is_finite() { sub_up(rhi, omin) } else { f64::INFINITY };
                let cdn = if rlo.is_finite() { sub_dn(rlo, omax) } else { f64::NEG_INFINITY };
                let (nlo, nhi) = if c > 0.0 {
                    (
                        if cdn.is_finite() { div_dn(cdn, c) } else { f64::NEG_INFINITY },
                        if cup.is_finite() { div_up(cup, c) } else { f64::INFINITY },
                    )
                } else {
                    (
                        if cup.is_finite() { div_dn(cup, c) } else { f64::NEG_INFINITY },
                        if cdn.is_finite() { div_up(cdn, c) } else { f64::INFINITY },
                    )
                };
                if nlo > s.lo[v] {
                    changed = changed.max(nlo - s.lo[v]);
                    s.lo[v] = nlo;
                }
                if nhi < s.hi[v] {
                    changed = changed.max(s.hi[v] - nhi);
                    s.hi[v] = nhi;
                }
                if s.lo[v] > s.hi[v] {
                    return Fbbt::Infeasible;
                }
            }
        }
        if changed < tol {
            break;
        }
    }
    Fbbt::Open
}
