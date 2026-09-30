//! Bounded dense simplex with a phase 2 (f64, heuristic) and a rigorous weak-duality bound.
//!
//! Problem: rows lo_k <= a_k . x <= hi_k, x in a finite box (a `Sys`). The simplex only proposes
//! row multipliers y. For any y, since s = A x lies in [lo, hi]:
//!   c . x = (c - y A) . x + y . s  >=  min over the box of (c - y A) . x + sum_k min(y_k lo_k, y_k hi_k),
//! which `safe_lower` evaluates in outward-rounded arithmetic (a multiplier that would need an
//! infinite row bound is set to 0). So the bound is valid whatever the quality of y.
//! Tableau layout as in lp.rs: columns x (n), s (m), artificials (m); row k of the original
//! matrix is a_k . x - s_k + sigma_k w_k = 0, stored multiplied by rho_k = +-1 so that the
//! initial basic column is +e_k; then y_k = rho_k (c_B^T T[:, init_col_k]).

use crate::iv::*;
use crate::system::Sys;

pub struct Lp {
    m: usize,
    n: usize,
    ncol: usize,
    t: Vec<f64>,
    lb: Vec<f64>,
    ub: Vec<f64>,
    cost: Vec<f64>,
    basis: Vec<usize>,
    at_upper: Vec<bool>,
    is_basic: Vec<bool>,
    beta: Vec<f64>,
    init_col: Vec<usize>,
    rho: Vec<f64>,
    pub iters: usize,
}

const EPS: f64 = 1e-9;

impl Lp {
    pub fn new(s: &Sys) -> Lp {
        let n = s.nvar;
        let m = s.nrows();
        let ncol = n + 2 * m;
        let mut t = vec![0.0; m * ncol];
        let mut lb = vec![0.0; ncol];
        let mut ub = vec![f64::INFINITY; ncol];
        let mut cost = vec![0.0; ncol];
        for j in 0..n {
            lb[j] = s.lo[j];
            ub[j] = s.hi[j];
        }
        let mut at_upper = vec![false; ncol];
        let mut is_basic = vec![false; ncol];
        let mut basis = vec![0; m];
        let mut beta = vec![0.0; m];
        let mut init_col = vec![0; m];
        let mut rho = vec![0.0; m];
        for k in 0..m {
            let row = &mut t[k * ncol..(k + 1) * ncol];
            let mut act = 0.0;
            for q in s.rs[k] as usize..s.rs[k + 1] as usize {
                let j = s.tv[q] as usize;
                row[j] += s.tc[q];
                act += s.tc[q] * lb[j];
            }
            let sc = n + k;
            let ac = n + m + k;
            row[sc] = -1.0;
            lb[sc] = s.rlo[k];
            ub[sc] = s.rhi[k];
            cost[ac] = 1.0;
            if act >= s.rlo[k] && act <= s.rhi[k] {
                basis[k] = sc;
                is_basic[sc] = true;
                beta[k] = act;
                init_col[k] = sc;
                rho[k] = -1.0;
                row[ac] = 1.0;
                for v in row.iter_mut() {
                    *v = -*v;
                }
                // artificial never needed for this row
                lb[ac] = 0.0;
                ub[ac] = 0.0;
            } else {
                let (bound, upper) = if act < s.rlo[k] { (s.rlo[k], false) } else { (s.rhi[k], true) };
                at_upper[sc] = upper;
                let r = act - bound;
                let sigma = if r > 0.0 { -1.0 } else { 1.0 };
                row[ac] = sigma;
                basis[k] = ac;
                is_basic[ac] = true;
                beta[k] = r.abs();
                init_col[k] = ac;
                rho[k] = sigma;
                if sigma < 0.0 {
                    for v in row.iter_mut() {
                        *v = -*v;
                    }
                }
            }
        }
        Lp { m, n, ncol, t, lb, ub, cost, basis, at_upper, is_basic, beta, init_col, rho, iters: 0 }
    }

    fn obj(&self) -> f64 {
        let mut v: f64 = (0..self.m).map(|i| self.cost[self.basis[i]] * self.beta[i]).sum();
        for j in 0..self.ncol {
            if !self.is_basic[j] && self.cost[j] != 0.0 {
                v += self.cost[j] * if self.at_upper[j] { self.ub[j] } else { self.lb[j] };
            }
        }
        v
    }

    /// Primal simplex on the current cost; false on iteration limit or numerical failure.
    fn run(&mut self, max_iter: usize) -> bool {
        let (m, nc) = (self.m, self.ncol);
        let mut d = vec![0.0; nc];
        for it in 0..max_iter {
            self.iters += 1;
            d.copy_from_slice(&self.cost);
            for i in 0..m {
                let cb = self.cost[self.basis[i]];
                if cb != 0.0 {
                    let row = &self.t[i * nc..(i + 1) * nc];
                    for j in 0..nc {
                        d[j] -= cb * row[j];
                    }
                }
            }
            let bland = it > 300;
            let mut enter = usize::MAX;
            let mut best = 0.0;
            for j in 0..nc {
                if self.is_basic[j] || self.lb[j] == self.ub[j] {
                    continue;
                }
                let cand = if self.at_upper[j] { d[j] > EPS } else { d[j] < -EPS };
                if cand {
                    if bland {
                        enter = j;
                        break;
                    }
                    if d[j].abs() > best {
                        best = d[j].abs();
                        enter = j;
                    }
                }
            }
            if enter == usize::MAX {
                return true;
            }
            let j = enter;
            let dir = if self.at_upper[j] { -1.0 } else { 1.0 };
            let mut tmax = self.ub[j] - self.lb[j];
            let mut leave = usize::MAX;
            let mut leave_to_upper = false;
            for i in 0..m {
                let a = self.t[i * nc + j] * dir;
                let bi = self.basis[i];
                if a > EPS {
                    if self.lb[bi].is_finite() {
                        let r = (self.beta[i] - self.lb[bi]) / a;
                        if r < tmax - 1e-12 || (leave == usize::MAX && r <= tmax) {
                            tmax = r.max(0.0);
                            leave = i;
                            leave_to_upper = false;
                        }
                    }
                } else if a < -EPS {
                    if self.ub[bi].is_finite() {
                        let r = (self.ub[bi] - self.beta[i]) / (-a);
                        if r < tmax - 1e-12 || (leave == usize::MAX && r <= tmax) {
                            tmax = r.max(0.0);
                            leave = i;
                            leave_to_upper = true;
                        }
                    }
                }
            }
            if !tmax.is_finite() {
                return false;
            }
            for i in 0..m {
                self.beta[i] -= dir * tmax * self.t[i * nc + j];
            }
            if leave == usize::MAX {
                self.at_upper[j] = !self.at_upper[j];
                continue;
            }
            let old = self.basis[leave];
            let newval = if dir > 0.0 { self.lb[j] + tmax } else { self.ub[j] - tmax };
            let piv = self.t[leave * nc + j];
            {
                let row = &mut self.t[leave * nc..(leave + 1) * nc];
                for v in row.iter_mut() {
                    *v /= piv;
                }
            }
            let prow: Vec<f64> = self.t[leave * nc..(leave + 1) * nc].to_vec();
            for i in 0..m {
                if i == leave {
                    continue;
                }
                let f = self.t[i * nc + j];
                if f != 0.0 {
                    let row = &mut self.t[i * nc..(i + 1) * nc];
                    for (v, p) in row.iter_mut().zip(prow.iter()) {
                        *v -= f * p;
                    }
                }
            }
            self.is_basic[old] = false;
            self.at_upper[old] = leave_to_upper;
            self.is_basic[j] = true;
            self.basis[leave] = j;
            self.beta[leave] = newval;
        }
        false
    }

    /// Phase 1; returns the remaining infeasibility (sum of artificials), None on failure.
    pub fn phase1(&mut self, max_iter: usize) -> Option<f64> {
        if self.run(max_iter) {
            Some(self.obj())
        } else {
            None
        }
    }

    /// Phase 2 on the structural objective c (minimised), artificials fixed at 0. Call after a
    /// phase 1 that reached (numerically) zero infeasibility.
    pub fn phase2(&mut self, c: &[f64], max_iter: usize) -> bool {
        for j in 0..self.ncol {
            self.cost[j] = if j < self.n { c[j] } else { 0.0 };
        }
        for k in 0..self.m {
            let ac = self.n + self.m + k;
            self.lb[ac] = 0.0;
            self.ub[ac] = 0.0;
            if !self.is_basic[ac] {
                self.at_upper[ac] = false;
            }
        }
        self.run(max_iter)
    }

    /// Row multipliers of the current basis for the current cost.
    pub fn duals(&self) -> Vec<f64> {
        let (m, nc) = (self.m, self.ncol);
        (0..m)
            .map(|k| {
                let col = self.init_col[k];
                let v: f64 = (0..m).map(|i| self.cost[self.basis[i]] * self.t[i * nc + col]).sum();
                v * self.rho[k]
            })
            .collect()
    }
}

/// Rigorous lower bound of c . x over {x in [s.lo, s.hi] : s.rlo <= A x <= s.rhi} from any
/// multipliers y (weak duality, outward rounding); -inf when no finite bound results.
pub fn safe_lower(s: &Sys, c: &[f64], y: &[f64]) -> f64 {
    let n = s.nvar;
    // r = c - y A as intervals
    let mut rlo: Vec<f64> = c.to_vec();
    let mut rhi: Vec<f64> = c.to_vec();
    let mut acc = 0.0f64; // lower bound of sum_k y_k s_k
    for k in 0..s.nrows() {
        let mut yk = y[k];
        if !yk.is_finite() || yk.abs() < 1e-300 {
            continue;
        }
        if (yk > 0.0 && !s.rlo[k].is_finite()) || (yk < 0.0 && !s.rhi[k].is_finite()) {
            yk = 0.0;
        }
        if yk == 0.0 {
            continue;
        }
        acc = add_dn(acc, if yk > 0.0 { mul_dn(yk, s.rlo[k]) } else { mul_dn(yk, s.rhi[k]) });
        for q in s.rs[k] as usize..s.rs[k + 1] as usize {
            let j = s.tv[q] as usize;
            let a = s.tc[q];
            rlo[j] = sub_dn(rlo[j], mul_up(yk, a));
            rhi[j] = sub_up(rhi[j], mul_dn(yk, a));
        }
    }
    let mut v = acc;
    for j in 0..n {
        let (l, u) = (s.lo[j], s.hi[j]);
        let t = mul_dn(rlo[j], l).min(mul_dn(rlo[j], u)).min(mul_dn(rhi[j], l)).min(mul_dn(rhi[j], u));
        v = add_dn(v, t);
    }
    if v.is_nan() {
        f64::NEG_INFINITY
    } else {
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// max x0 + x1 s.t. x0 + 2 x1 <= 4, 3 x0 + x1 <= 6, x in [0, 10]^2: optimum 2.8 at (1.6, 1.2).
    #[test]
    fn small_lp_and_safe_bound() {
        let mut s = Sys::default();
        s.rs.push(0);
        s.nvar = 2;
        s.lo = vec![0.0, 0.0];
        s.hi = vec![10.0, 10.0];
        for (terms, hi) in [(vec![(0u32, 1.0), (1u32, 2.0)], 4.0), (vec![(0u32, 3.0), (1u32, 1.0)], 6.0)] {
            for (v, c) in terms {
                s.tv.push(v);
                s.tc.push(c);
            }
            s.rs.push(s.tv.len() as u32);
            s.rlo.push(f64::NEG_INFINITY);
            s.rhi.push(hi);
        }
        let mut lp = Lp::new(&s);
        assert!(lp.phase1(100).unwrap() < 1e-12);
        let c = [-1.0, -1.0];
        assert!(lp.phase2(&c, 100));
        let y = lp.duals();
        let lb = safe_lower(&s, &c, &y);
        assert!(lb <= -2.8 && lb > -2.8 - 1e-9, "{lb}");
        // any multipliers give a valid (weaker) bound
        let lb0 = safe_lower(&s, &c, &[0.0, 0.0]);
        assert!(lb0 <= -2.8);
    }
}
