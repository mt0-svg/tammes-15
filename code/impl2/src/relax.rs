//! Linear relaxation of a box and rigorous LP tests (optional contractor, --lp).
//!
//! Rows, each valid for every genuine point of the box B:
//! - the linear rows of the model, as they are;
//! - for an explicit relation out_k = F_k(in) with the D<4> evaluation ok on B (F_k is C^1 on
//!   the convex box, gradient enclosure [gl, gh]): with xl, xh the lower and upper corners of the
//!   input box, F_k(x) - F_k(xl) = J (x - xl) with J in [gl, gh] and x - xl >= 0, so
//!   F_k(xl) + gl.(x - xl) <= F_k(x) <= F_k(xl) + gh.(x - xl); at the upper corner x - xh <= 0
//!   gives F_k(xh) + gh.(x - xh) <= F_k(x) <= F_k(xh) + gl.(x - xh). Hence the two ranged rows
//!   out - gl.x in [F(xl) - gl.xl, F(xh) - gl.xh] and out - gh.x in [F(xh) - gh.xh, F(xl) - gh.xl]
//!   (right-hand sides by interval arithmetic, rounded outward; coefficients are the exact
//!   doubles gl, gh). For out >= F (Ge) only the lower ends are kept.
//! The simplex (simplex.rs) proposes row multipliers y; they are trusted only after a check in
//! outward rounded interval arithmetic:
//! - Farkas: for every x in B and s = A x, sum_j (A^T y)_j x_j - sum_i y_i s_i = 0 exactly; if the
//!   interval of this expression over x in B and s_i in [rl_i, ru_i] excludes 0, no genuine point
//!   lies in B;
//! - bound (Neumaier and Shcherbina 2004): c.x = (c - A^T y).x + sum_i y_i s_i, so c.x >= min over B
//!   of the first term + sum_i min over [rl_i, ru_i] of y_i s_i.

use crate::ad::{Num, D};
use crate::faces::eval;
use crate::iv::I;
use crate::model::{Con, Kind, Model, VD};
use crate::simplex::{feasibility, minimize, Lp, Outcome};

pub struct Relax {
    pub lp: Lp,
}

fn push_row(lp: &mut Lp, row: &[f64], lo: f64, hi: f64) {
    lp.a.extend_from_slice(row);
    lp.rl.push(lo);
    lp.ru.push(hi);
    lp.m += 1;
}

/// Build the relaxation of box b. Returns None if a bound is not finite.
pub fn build(m: &Model, b: &[I]) -> Option<Relax> {
    let n = m.nv;
    let mut lp = Lp { n, m: 0, a: Vec::new(), rl: Vec::new(), ru: Vec::new(), xl: Vec::with_capacity(n), xu: Vec::with_capacity(n) };
    for v in 0..n {
        if !b[v].lo.is_finite() || !b[v].hi.is_finite() {
            return None;
        }
        lp.xl.push(b[v].lo);
        lp.xu.push(b[v].hi);
    }
    let mut row = vec![0.0f64; n];
    for c in &m.cons {
        match c {
            Con::Lin(l) => {
                for x in row.iter_mut() {
                    *x = 0.0;
                }
                for &(v, cf) in &l.terms {
                    row[v] += cf;
                }
                push_row(&mut lp, &row, l.lo, l.hi);
            }
            Con::Rel(r) => {
                let nin = r.fam.nin();
                let nout = r.fam.nout();
                let mut xd = [D::<4>::c(I::pt(0.0)); 4];
                let mut xl = [I::pt(0.0); 4];
                let mut xh = [I::pt(0.0); 4];
                for j in 0..nin {
                    let x = b[r.ins[j]];
                    xd[j] = D::var(x, j);
                    xl[j] = I::pt(x.lo);
                    xh[j] = I::pt(x.hi);
                }
                let out = match eval(r.fam, &xd) {
                    Some(o) => o,
                    None => continue,
                };
                if !(0..nout).any(|k| out[k].ok) {
                    continue;
                }
                let (fl, fh) = match (eval(r.fam, &xl), eval(r.fam, &xh)) {
                    (Some(a), Some(bb)) => (a, bb),
                    _ => continue,
                };
                for k in 0..nout {
                    if !out[k].ok {
                        continue;
                    }
                    let g = out[k].g;
                    if (0..nin).any(|j| !g[j].lo.is_finite() || !g[j].hi.is_finite()) {
                        continue;
                    }
                    let ov = r.outs[k];
                    // rows out - gsel . x with gsel = lower ends, then upper ends
                    for sel in 0..2 {
                        for x in row.iter_mut() {
                            *x = 0.0;
                        }
                        row[ov] += 1.0;
                        let mut sl = I::pt(0.0);
                        let mut sh = I::pt(0.0);
                        for j in 0..nin {
                            let cf = if sel == 0 { g[j].lo } else { g[j].hi };
                            row[r.ins[j]] -= cf;
                            sl = sl + I::pt(cf) * xl[j];
                            sh = sh + I::pt(cf) * xh[j];
                        }
                        let (lo, hi) = if sel == 0 {
                            // out - gl.x in [F(xl) - gl.xl, F(xh) - gl.xh]
                            ((fl[k] - sl).lo, (fh[k] - sh).hi)
                        } else {
                            // out - gh.x in [F(xh) - gh.xh, F(xl) - gh.xl]
                            ((fh[k] - sh).lo, (fl[k] - sl).hi)
                        };
                        let hi = if r.kinds[k] == Kind::Ge { f64::INFINITY } else { hi };
                        if lo.is_finite() || hi.is_finite() {
                            push_row(&mut lp, &row, lo, hi);
                        }
                    }
                }
            }
        }
    }
    Some(Relax { lp })
}

impl Relax {
    /// interval of sum_j (A^T y)_j x_j over the box, minus sum_i y_i [rl_i, ru_i]
    fn identity_range(&self, y: &[f64]) -> I {
        let lp = &self.lp;
        let mut aty = vec![I::pt(0.0); lp.n];
        let mut s = I::pt(0.0);
        for i in 0..lp.m {
            if y[i] == 0.0 {
                continue;
            }
            let yi = I::pt(y[i]);
            for j in 0..lp.n {
                let a = lp.a[i * lp.n + j];
                if a != 0.0 {
                    aty[j] = aty[j] + yi * I::pt(a);
                }
            }
            s = s + yi * I::new(lp.rl[i], lp.ru[i]);
        }
        let mut t = I::pt(0.0);
        for j in 0..lp.n {
            t = t + aty[j] * I::new(lp.xl[j], lp.xu[j]);
        }
        t - s
    }

    /// true if the multipliers y prove that no genuine point lies in the box
    pub fn farkas(&self, y: &[f64]) -> bool {
        let r = self.identity_range(y);
        r.lo > 0.0 || r.hi < 0.0
    }

    /// rigorous lower bound of c.x over the relaxation, from multipliers y
    pub fn lower_bound(&self, c: &[f64], y: &[f64]) -> f64 {
        let lp = &self.lp;
        let mut g: Vec<I> = c.iter().map(|&x| I::pt(x)).collect();
        let mut s = I::pt(0.0);
        for i in 0..lp.m {
            if y[i] == 0.0 {
                continue;
            }
            let yi = I::pt(y[i]);
            for j in 0..lp.n {
                let a = lp.a[i * lp.n + j];
                if a != 0.0 {
                    g[j] = g[j] - yi * I::pt(a);
                }
            }
            s = s + yi * I::new(lp.rl[i], lp.ru[i]);
        }
        let mut t = s;
        for j in 0..lp.n {
            t = t + g[j] * I::new(lp.xl[j], lp.xu[j]);
        }
        if t.lo.is_nan() {
            f64::NEG_INFINITY
        } else {
            t.lo
        }
    }
}

/// LP test of a box: Some(false) if proved empty, Some(true) after contracting the variables
/// in `vars` (their bounds in b are narrowed), None if nothing was learnt.
pub fn lp_test(m: &Model, b: &mut [I], vars: &[usize], maxit: usize) -> Option<bool> {
    let rx = build(m, b)?;
    match feasibility(&rx.lp, maxit) {
        Outcome::Infeasible(y) => {
            let neg: Vec<f64> = y.iter().map(|x| -x).collect();
            if rx.farkas(&y) || rx.farkas(&neg) {
                return Some(false);
            }
            return None;
        }
        Outcome::Failed => return None,
        _ => {}
    }
    let mut changed = false;
    for &v in vars {
        for dir in [1.0, -1.0] {
            let mut c = vec![0.0; m.nv];
            c[v] = dir;
            if let Outcome::Optimal(_, y) = minimize(&rx.lp, &c, maxit) {
                let lb = rx.lower_bound(&c, &y);
                if !lb.is_finite() {
                    continue;
                }
                if dir > 0.0 {
                    // x_v >= lb
                    if lb > b[v].hi {
                        return Some(false);
                    }
                    if lb > b[v].lo {
                        b[v].lo = lb;
                        changed = true;
                    }
                } else {
                    // -x_v >= lb
                    let ub = -lb;
                    if ub < b[v].lo {
                        return Some(false);
                    }
                    if ub < b[v].hi {
                        b[v].hi = ub;
                        changed = true;
                    }
                }
            }
        }
    }
    let _ = VD;
    if changed {
        Some(true)
    } else {
        None
    }
}
