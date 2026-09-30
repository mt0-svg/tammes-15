//! Level 1: bound propagation on the linear rows only (for an independent stage A).
//!
//! Variables: a = alpha(d) in [alpha(dlo), alpha(dhi)] (every triangle corner), rhombus corner
//! pairs x, y, pentagon and hexagon corners. Rows (all valid for every configuration of the
//! class, Section 6.5):
//! - vertex sums: sum of the corners at v = 2 pi;
//! - rhombus: a <= x, y <= 2a, x + y >= 3a, x + y <= S(dhi);
//! - pentagon, hexagon corners in [a, pi];
//! - face angle sums (Girard): the corners of an m-gon sum to (m - 2) pi + area > (m - 2) pi.
//! A graph is killed when propagation empties a variable. No allocation per graph beyond the
//! face tracing of Graph.

use crate::graph::Graph;
use crate::iv::{dn, up, I, PI_HI};
use crate::model::Params;

pub struct L1 {
    alo: f64,
    ahi: f64,
    s_hi: f64,
    pub area_rows: bool,
    pub passes: usize,
}

/// A row lo <= sum c_j x_j <= hi with small integer coefficients.
struct Row {
    t: [(u16, f64); 8],
    n: usize,
    lo: f64,
    hi: f64,
}

impl L1 {
    pub fn new(p: &Params) -> L1 {
        let c = crate::elem::cos(I::pt(p.dhi));
        let t = I::pt(1.0) / c.sqrt().unwrap();
        let s_hi = (crate::elem::atan(t) * 4.0).hi;
        L1 { alo: p.alo, ahi: p.ahi, s_hi, area_rows: true, passes: 0 }
    }

    /// true = killed (no solution of the rows)
    pub fn kill(&mut self, g: &Graph) -> bool {
        // variables
        let mut b: Vec<I> = vec![I::new(self.alo, self.ahi)];
        let mut cv: Vec<[u16; 6]> = Vec::with_capacity(g.faces.len());
        let mut rows: Vec<Row> = Vec::with_capacity(g.n + 4 * g.faces.len());
        let two_pi = I::two_pi();
        let pi = I::PI;
        let mk = |t: &[(u16, f64)], lo: f64, hi: f64| -> Row {
            let mut a = [(0u16, 0.0); 8];
            a[..t.len()].copy_from_slice(t);
            Row { t: a, n: t.len(), lo, hi }
        };
        for f in &g.faces {
            let m = f.len();
            let mut c = [0u16; 6];
            match m {
                3 => {}
                4 => {
                    let x = b.len() as u16;
                    b.push(I::new(self.alo, (I::pt(self.ahi) * 2.0).hi.min(PI_HI)));
                    b.push(I::new(self.alo, (I::pt(self.ahi) * 2.0).hi.min(PI_HI)));
                    c[0] = x;
                    c[1] = x + 1;
                    c[2] = x;
                    c[3] = x + 1;
                    for w in [x, x + 1] {
                        rows.push(mk(&[(w, 1.0), (0, -1.0)], 0.0, f64::INFINITY));
                        rows.push(mk(&[(w, 1.0), (0, -2.0)], f64::NEG_INFINITY, 0.0));
                    }
                    rows.push(mk(&[(x, 1.0), (x + 1, 1.0), (0, -3.0)], 0.0, f64::INFINITY));
                    rows.push(mk(&[(x, 1.0), (x + 1, 1.0)], f64::NEG_INFINITY, self.s_hi));
                }
                5 | 6 => {
                    let mut t = Vec::with_capacity(6);
                    for k in 0..m {
                        let w = b.len() as u16;
                        b.push(I::new(self.alo, PI_HI));
                        c[k] = w;
                        rows.push(mk(&[(w, 1.0), (0, -1.0)], 0.0, f64::INFINITY));
                        t.push((w, 1.0));
                    }
                    if self.area_rows {
                        let lo = (pi * (m as f64 - 2.0)).lo;
                        rows.push(mk(&t, lo, f64::INFINITY));
                    }
                }
                _ => return true, // outside the class (faces > 6 cannot occur)
            }
            cv.push(c);
        }
        for v in 0..g.n {
            let mut t: Vec<(u16, f64)> = Vec::with_capacity(5);
            for j in 0..g.adj[v].len() {
                let (f, i) = g.corner_face[v][j];
                let var = if g.faces[f].len() == 3 { 0 } else { cv[f][i] };
                if let Some(e) = t.iter_mut().find(|e| e.0 == var) {
                    e.1 += 1.0;
                } else {
                    t.push((var, 1.0));
                }
            }
            if t.len() > 8 {
                return false;
            }
            rows.push(mk(&t, two_pi.lo, two_pi.hi));
        }
        // propagate
        for pass in 0..60 {
            let mut change = 0.0f64;
            for r in &rows {
                for j in 0..r.n {
                    let (vj, cj) = r.t[j];
                    let mut rlo = 0.0f64;
                    let mut rhi = 0.0f64;
                    for (i, &(vi, ci)) in r.t[..r.n].iter().enumerate() {
                        if i != j {
                            let x = b[vi as usize];
                            let (p, q) = if ci >= 0.0 { (x.lo * ci, x.hi * ci) } else { (x.hi * ci, x.lo * ci) };
                            rlo = dn(rlo + dn(p));
                            rhi = up(rhi + up(q));
                        }
                    }
                    // c_j x_j in [lo - rhi, hi - rlo]
                    let nlo = if r.lo.is_finite() { dn(r.lo - rhi) } else { f64::NEG_INFINITY };
                    let nhi = if r.hi.is_finite() { up(r.hi - rlo) } else { f64::INFINITY };
                    let (xlo, xhi) = if cj > 0.0 {
                        (if nlo.is_finite() { dn(nlo / cj) } else { f64::NEG_INFINITY }, if nhi.is_finite() { up(nhi / cj) } else { f64::INFINITY })
                    } else {
                        (if nhi.is_finite() { dn(nhi / cj) } else { f64::NEG_INFINITY }, if nlo.is_finite() { up(nlo / cj) } else { f64::INFINITY })
                    };
                    let x = &mut b[vj as usize];
                    let w0 = x.width();
                    let lo = x.lo.max(xlo);
                    let hi = x.hi.min(xhi);
                    if lo > hi {
                        self.passes += pass + 1;
                        return true;
                    }
                    x.lo = lo;
                    x.hi = hi;
                    if w0 > 0.0 {
                        change = change.max((w0 - (hi - lo)) / w0);
                    }
                }
            }
            if change < 1e-6 {
                self.passes += pass + 1;
                return false;
            }
        }
        self.passes += 60;
        false
    }
}
