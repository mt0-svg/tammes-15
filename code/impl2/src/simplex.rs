//! Dense bounded-variable primal simplex in floating point, without any guarantee.
//!
//! Its only use is to propose row multipliers that relax.rs then checks in outward rounded
//! interval arithmetic (a Farkas test or a Neumaier-Shcherbina bound), so a wrong, inaccurate or
//! failed answer can only cost strength, never soundness.
//!
//! Problem: variables x_j in [xl_j, xu_j] (finite), rows r_i = a_i . x in [rl_i, ru_i] (either end
//! may be infinite). The row values are extra variables s_i, and the system is A x - s = 0. The
//! tableau T = B^{-1} [A | -I] is kept dense (m x (n + m)); z_B = -sum over nonbasic k of
//! T[., k] z_k. Phase 1 minimises the sum of the bound violations of the basic variables, phase 2
//! a linear objective; Dantzig pricing, first breakpoint ratio test, iteration limit.

pub struct Lp {
    pub n: usize,
    pub m: usize,
    /// m x n, row major
    pub a: Vec<f64>,
    pub rl: Vec<f64>,
    pub ru: Vec<f64>,
    pub xl: Vec<f64>,
    pub xu: Vec<f64>,
}

pub enum Outcome {
    /// phase 1 ended with positive infeasibility; candidate Farkas multipliers of the rows
    Infeasible(Vec<f64>),
    /// feasible point found (phase 1 only)
    Feasible,
    /// phase 2 optimum: primal x and row multipliers
    Optimal(Vec<f64>, Vec<f64>),
    Failed,
}

struct Tab {
    n: usize,
    m: usize,
    w: usize,
    t: Vec<f64>,
    lo: Vec<f64>,
    hi: Vec<f64>,
    val: Vec<f64>,
    basis: Vec<usize>,
    /// row of a basic variable, usize::MAX if nonbasic
    row_of: Vec<usize>,
}

const FEAS_TOL: f64 = 1e-9;
const PIV_TOL: f64 = 1e-9;
const COST_TOL: f64 = 1e-10;

impl Tab {
    fn new(lp: &Lp) -> Tab {
        let (n, m) = (lp.n, lp.m);
        let w = n + m;
        let mut t = vec![0.0; m * w];
        for i in 0..m {
            for j in 0..n {
                t[i * w + j] = -lp.a[i * n + j];
            }
            t[i * w + n + i] = 1.0;
        }
        let mut lo = lp.xl.clone();
        lo.extend_from_slice(&lp.rl);
        let mut hi = lp.xu.clone();
        hi.extend_from_slice(&lp.ru);
        let mut val = vec![0.0; w];
        for j in 0..n {
            val[j] = lp.xl[j];
        }
        let basis: Vec<usize> = (n..w).collect();
        let mut row_of = vec![usize::MAX; w];
        for i in 0..m {
            row_of[n + i] = i;
        }
        let mut tb = Tab { n, m, w, t, lo, hi, val, basis, row_of };
        tb.recompute();
        tb
    }

    fn recompute(&mut self) {
        for i in 0..self.m {
            let mut s = 0.0;
            let row = &self.t[i * self.w..(i + 1) * self.w];
            for k in 0..self.w {
                if self.row_of[k] == usize::MAX && row[k] != 0.0 {
                    s -= row[k] * self.val[k];
                }
            }
            self.val[self.basis[i]] = s;
        }
    }

    fn pivot(&mut self, p: usize, k: usize) {
        let w = self.w;
        let piv = self.t[p * w + k];
        for x in self.t[p * w..(p + 1) * w].iter_mut() {
            *x /= piv;
        }
        let prow: Vec<f64> = self.t[p * w..(p + 1) * w].to_vec();
        for i in 0..self.m {
            if i == p {
                continue;
            }
            let f = self.t[i * w + k];
            if f != 0.0 {
                let row = &mut self.t[i * w..(i + 1) * w];
                for (x, &y) in row.iter_mut().zip(prow.iter()) {
                    *x -= f * y;
                }
                row[k] = 0.0;
            }
        }
        let leaving = self.basis[p];
        self.row_of[leaving] = usize::MAX;
        self.basis[p] = k;
        self.row_of[k] = p;
    }

    /// One step with entering nonbasic k moving in direction dir (+1 or -1); `phase1` selects
    /// the breakpoint rule. Returns false if no finite step exists.
    fn step(&mut self, k: usize, dir: f64, phase1: bool) -> bool {
        let w = self.w;
        let mut tmax = self.hi[k] - self.lo[k];
        let mut leave: Option<(usize, f64)> = None;
        let mut best_r = 0.0f64;
        for i in 0..self.m {
            let r = -self.t[i * w + k] * dir;
            if r.abs() <= PIV_TOL {
                continue;
            }
            let bv = self.basis[i];
            let (v, l, h) = (self.val[bv], self.lo[bv], self.hi[bv]);
            let cand: Option<(f64, f64)> = if r > 0.0 {
                if phase1 && v < l - FEAS_TOL {
                    Some(((l - v) / r, l))
                } else if v <= h + FEAS_TOL && h.is_finite() {
                    Some((((h - v) / r).max(0.0), h))
                } else {
                    None
                }
            } else if phase1 && v > h + FEAS_TOL {
                Some(((h - v) / r, h))
            } else if v >= l - FEAS_TOL && l.is_finite() {
                Some((((l - v) / r).max(0.0), l))
            } else {
                None
            };
            if let Some((ti, bound)) = cand {
                if ti < tmax - 1e-12 || (ti <= tmax + 1e-12 && leave.is_some() && r.abs() > best_r) {
                    tmax = ti;
                    leave = Some((i, bound));
                    best_r = r.abs();
                }
            }
        }
        if !tmax.is_finite() {
            return false;
        }
        // move
        for i in 0..self.m {
            let r = -self.t[i * w + k] * dir;
            if r != 0.0 {
                let bv = self.basis[i];
                self.val[bv] += r * tmax;
            }
        }
        self.val[k] += dir * tmax;
        match leave {
            None => {
                // bound flip of the entering variable
                self.val[k] = if dir > 0.0 { self.hi[k] } else { self.lo[k] };
            }
            Some((p, bound)) => {
                let leaving = self.basis[p];
                self.pivot(p, k);
                self.val[leaving] = bound;
            }
        }
        true
    }

    fn at_lower(&self, k: usize) -> bool {
        (self.val[k] - self.lo[k]).abs() <= (self.val[k] - self.hi[k]).abs()
    }

    /// multipliers pi_i' = sum_i c_i (B^{-1})_{i i'} with B^{-1} = -T[., n..n+m]
    fn multipliers(&self, cb: &[f64]) -> Vec<f64> {
        let mut pi = vec![0.0; self.m];
        for i in 0..self.m {
            if cb[i] == 0.0 {
                continue;
            }
            let row = &self.t[i * self.w + self.n..(i + 1) * self.w];
            for (ip, &x) in row.iter().enumerate() {
                pi[ip] -= cb[i] * x;
            }
        }
        pi
    }

    fn phase1(&mut self, maxit: usize) -> Option<Option<Vec<f64>>> {
        let w = self.w;
        let mut cb = vec![0.0; self.m];
        for it in 0..maxit {
            if it % 50 == 49 {
                self.recompute();
            }
            let mut infeas = false;
            for i in 0..self.m {
                let bv = self.basis[i];
                cb[i] = if self.val[bv] < self.lo[bv] - FEAS_TOL {
                    infeas = true;
                    -1.0
                } else if self.val[bv] > self.hi[bv] + FEAS_TOL {
                    infeas = true;
                    1.0
                } else {
                    0.0
                };
            }
            if !infeas {
                return Some(None);
            }
            // pricing: g_k = -sum_i cb_i T_ik
            let mut best = usize::MAX;
            let mut bestg = 0.0f64;
            let mut bestdir = 0.0;
            for k in 0..w {
                if self.row_of[k] != usize::MAX || self.hi[k] - self.lo[k] <= 0.0 {
                    continue;
                }
                let mut g = 0.0;
                for i in 0..self.m {
                    if cb[i] != 0.0 {
                        g -= cb[i] * self.t[i * w + k];
                    }
                }
                let lower = self.at_lower(k);
                let (ok, dir) = if lower { (g < -COST_TOL, 1.0) } else { (g > COST_TOL, -1.0) };
                if ok && g.abs() > bestg {
                    bestg = g.abs();
                    best = k;
                    bestdir = dir;
                }
            }
            if best == usize::MAX {
                return Some(Some(self.multipliers(&cb)));
            }
            if !self.step(best, bestdir, true) {
                return None;
            }
        }
        None
    }

    fn phase2(&mut self, c: &[f64], maxit: usize) -> Option<Vec<f64>> {
        let w = self.w;
        let cost = |k: usize| if k < c.len() { c[k] } else { 0.0 };
        for it in 0..maxit {
            if it % 50 == 49 {
                self.recompute();
            }
            let cb: Vec<f64> = self.basis.iter().map(|&b| cost(b)).collect();
            let mut best = usize::MAX;
            let mut bestg = 0.0f64;
            let mut bestdir = 0.0;
            for k in 0..w {
                if self.row_of[k] != usize::MAX || self.hi[k] - self.lo[k] <= 0.0 {
                    continue;
                }
                let mut dk = cost(k);
                for i in 0..self.m {
                    if cb[i] != 0.0 {
                        dk -= cb[i] * self.t[i * w + k];
                    }
                }
                let lower = self.at_lower(k);
                let (ok, dir) = if lower { (dk < -COST_TOL, 1.0) } else { (dk > COST_TOL, -1.0) };
                if ok && dk.abs() > bestg {
                    bestg = dk.abs();
                    best = k;
                    bestdir = dir;
                }
            }
            if best == usize::MAX {
                return Some(self.multipliers(&cb));
            }
            if !self.step(best, bestdir, false) {
                return None;
            }
        }
        None
    }
}

/// Phase 1 only.
pub fn feasibility(lp: &Lp, maxit: usize) -> Outcome {
    let mut tb = Tab::new(lp);
    match tb.phase1(maxit) {
        None => Outcome::Failed,
        Some(None) => Outcome::Feasible,
        Some(Some(y)) => Outcome::Infeasible(y),
    }
}

/// Minimise c . x (phase 1 then phase 2).
pub fn minimize(lp: &Lp, c: &[f64], maxit: usize) -> Outcome {
    let mut tb = Tab::new(lp);
    match tb.phase1(maxit) {
        None => Outcome::Failed,
        Some(Some(y)) => Outcome::Infeasible(y),
        Some(None) => match tb.phase2(c, maxit) {
            None => Outcome::Failed,
            Some(y) => Outcome::Optimal(tb.val[..lp.n].to_vec(), y),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_lps() {
        // x + y >= 3, x - y <= 1, x, y in [0, 2]: min x + 2y at (2, 1) -> 4
        let lp = Lp {
            n: 2,
            m: 2,
            a: vec![1.0, 1.0, 1.0, -1.0],
            rl: vec![3.0, f64::NEG_INFINITY],
            ru: vec![f64::INFINITY, 1.0],
            xl: vec![0.0, 0.0],
            xu: vec![2.0, 2.0],
        };
        match minimize(&lp, &[1.0, 2.0], 100) {
            Outcome::Optimal(x, y) => {
                assert!((x[0] - 2.0).abs() < 1e-9 && (x[1] - 1.0).abs() < 1e-9, "{x:?}");
                // Neumaier-Shcherbina bound with the returned multipliers: sum_j min (c - A^T y)_j x_j
                // + sum_i min y_i r_i over the row ranges; must equal the optimum 4
                let g = [1.0 - y[0] - y[1], 2.0 - y[0] + y[1]];
                let mut lb = 0.0;
                for j in 0..2 {
                    lb += (g[j] * lp.xl[j]).min(g[j] * lp.xu[j]);
                }
                for i in 0..2 {
                    if y[i] > 0.0 {
                        lb += y[i] * lp.rl[i];
                    } else if y[i] < 0.0 {
                        lb += y[i] * lp.ru[i];
                    }
                }
                assert!((lb - 4.0).abs() < 1e-9, "y {y:?} lb {lb}");
            }
            _ => panic!("not optimal"),
        }
        // infeasible: x + y >= 5 with x, y in [0, 2]
        let lp2 = Lp { n: 2, m: 1, a: vec![1.0, 1.0], rl: vec![5.0], ru: vec![f64::INFINITY], xl: vec![0.0, 0.0], xu: vec![2.0, 2.0] };
        match feasibility(&lp2, 100) {
            Outcome::Infeasible(y) => assert!(y[0].abs() > 0.0),
            _ => panic!("not infeasible"),
        }
    }
}
