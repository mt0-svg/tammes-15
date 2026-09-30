//! Phase-1 bounded primal simplex (dense tableau, f64) and rigorous Farkas certificate check.
//!
//! The simplex is only a heuristic that proposes row multipliers lambda. Infeasibility is
//! asserted only after `check_farkas` verifies, in outward-rounded arithmetic, that
//!   min over the variable box of (sum_k lambda_k a_k)^T x  >  sum_k h_k(lambda_k),
//! where h_k(l) = l*hi_k for l > 0 and l*lo_k for l < 0. Any feasible x would satisfy
//! (sum lambda_k a_k)^T x <= sum h_k(lambda_k), so the check proves infeasibility.

use crate::iv::*;
use crate::system::Sys;

pub struct Simplex {
    m: usize,
    ncol: usize,
    t: Vec<f64>, // m x ncol, row-major
    lb: Vec<f64>,
    ub: Vec<f64>,
    cost: Vec<f64>,
    basis: Vec<usize>,   // column basic in row i
    at_upper: Vec<bool>, // for nonbasic columns
    is_basic: Vec<bool>,
    beta: Vec<f64>, // values of basic variables
    init_col: Vec<usize>,
    init_sign: Vec<f64>,
    pub iters: usize,
}

pub enum LpResult {
    /// verified infeasible, with the multipliers
    Infeasible(Vec<f64>),
    /// phase 1 reached (numerically) zero infeasibility
    Feasible,
    /// numerical trouble or certificate check failed
    Unknown,
}

const EPS: f64 = 1e-9;

impl Simplex {
    /// Builds the phase-1 problem for rows lo <= A x <= hi, x in box.
    pub fn new(s: &Sys) -> Simplex {
        let n = s.nvar;
        let m = s.nrows();
        let ncol = n + 2 * m; // x, s (row activities), artificials
        let mut t = vec![0.0; m * ncol];
        let mut lb = vec![0.0; ncol];
        let mut ub = vec![f64::INFINITY; ncol];
        let mut cost = vec![0.0; ncol];
        for j in 0..n {
            lb[j] = s.lo[j];
            ub[j] = s.hi[j];
        }
        // x nonbasic at lower bound (all boxes are finite)
        let mut at_upper = vec![false; ncol];
        let mut is_basic = vec![false; ncol];
        let mut basis = vec![0; m];
        let mut beta = vec![0.0; m];
        let mut init_col = vec![0; m];
        let mut init_sign = vec![0.0; m];
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
                // s basic with value act; artificial nonbasic at 0 (column irrelevant)
                basis[k] = sc;
                is_basic[sc] = true;
                beta[k] = act;
                init_col[k] = sc;
                init_sign[k] = -1.0;
                row[ac] = 1.0;
                // make the basic column the unit column: divide row by -1
                for v in row.iter_mut() {
                    *v = -*v;
                }
            } else {
                // s nonbasic at the violated bound, artificial basic = |act - bound|
                let (bound, upper) = if act < s.rlo[k] { (s.rlo[k], false) } else { (s.rhi[k], true) };
                at_upper[sc] = upper;
                let r = act - bound; // row: a x - s + sigma w = 0 -> sigma w = -(a x - s) = -r
                let sigma = if r > 0.0 { -1.0 } else { 1.0 };
                row[ac] = sigma;
                basis[k] = ac;
                is_basic[ac] = true;
                beta[k] = r.abs();
                init_col[k] = ac;
                init_sign[k] = sigma;
                if sigma < 0.0 {
                    for v in row.iter_mut() {
                        *v = -*v;
                    }
                }
            }
        }
        Simplex { m, ncol, t, lb, ub, cost, basis, at_upper, is_basic, beta, init_col, init_sign, iters: 0 }
    }

    fn obj(&self) -> f64 {
        (0..self.m).map(|i| self.cost[self.basis[i]] * self.beta[i]).sum()
    }

    /// Runs phase 1. Returns the final infeasibility.
    pub fn solve(&mut self, max_iter: usize) -> Option<f64> {
        let (m, nc) = (self.m, self.ncol);
        let mut d = vec![0.0; nc];
        for it in 0..max_iter {
            self.iters = it;
            // reduced costs d_j = c_j - c_B^T T_j
            for j in 0..nc {
                d[j] = self.cost[j];
            }
            for i in 0..m {
                let cb = self.cost[self.basis[i]];
                if cb != 0.0 {
                    let row = &self.t[i * nc..(i + 1) * nc];
                    for j in 0..nc {
                        d[j] -= cb * row[j];
                    }
                }
            }
            // entering column: Dantzig, Bland after many iterations
            let bland = it > 200;
            let mut enter = usize::MAX;
            let mut best = 0.0;
            for j in 0..nc {
                if self.is_basic[j] || self.lb[j] == self.ub[j] {
                    continue;
                }
                let cand = if self.at_upper[j] { d[j] > EPS } else { d[j] < -EPS };
                let score = if cand { d[j].abs() } else { 0.0 };
                if score > 0.0 {
                    if bland {
                        enter = j;
                        break;
                    }
                    if score > best {
                        best = score;
                        enter = j;
                    }
                }
            }
            if enter == usize::MAX {
                return Some(self.obj());
            }
            let j = enter;
            let dir = if self.at_upper[j] { -1.0 } else { 1.0 };
            // ratio test: x_j moves by dir*t, basic i moves by -dir*t*T_ij
            let mut tmax = self.ub[j] - self.lb[j]; // bound flip
            let mut leave = usize::MAX;
            let mut leave_to_upper = false;
            for i in 0..m {
                let a = self.t[i * nc + j] * dir;
                let bi = self.basis[i];
                if a > EPS {
                    // basic decreases
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
                return None; // unbounded direction cannot happen in phase 1 with finite x box
            }
            // update basic values
            for i in 0..m {
                self.beta[i] -= dir * tmax * self.t[i * nc + j];
            }
            if leave == usize::MAX {
                // bound flip
                self.at_upper[j] = !self.at_upper[j];
                continue;
            }
            // pivot: j enters at row leave
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
        None
    }

    /// Row multipliers y = c_B^T B^{-1} recovered from the columns of the initial basis.
    pub fn duals(&self) -> Vec<f64> {
        let (m, nc) = (self.m, self.ncol);
        let mut y = vec![0.0; m];
        for k in 0..m {
            let col = self.init_col[k];
            let mut v = 0.0;
            for i in 0..m {
                v += self.cost[self.basis[i]] * self.t[i * nc + col];
            }
            // T[:, col] = B^{-1} * (init_sign_k e_k) up to the row sign flips applied at start,
            // which are exactly init_sign_k, so B^{-1} e_k = T[:, col] * init_sign_k^{-1}... the
            // sign is fixed by trying both signs in check_farkas.
            y[k] = v * self.init_sign[k];
        }
        y
    }
}

/// Rigorous check of a Farkas certificate for lo <= A x <= hi, x in [s.lo, s.hi].
pub fn check_farkas(s: &Sys, lam_in: &[f64]) -> bool {
    let n = s.nvar;
    for sign in [1.0, -1.0] {
        let lam: Vec<f64> = (0..s.nrows())
            .map(|k| {
                let l = sign * lam_in[k];
                if (l > 0.0 && !s.rhi[k].is_finite()) || (l < 0.0 && !s.rlo[k].is_finite()) || l.abs() < 1e-14 {
                    0.0
                } else {
                    l
                }
            })
            .collect();
        // c = sum lam_k a_k as intervals
        let mut clo = vec![0.0; n];
        let mut chi = vec![0.0; n];
        let mut rhs = 0.0;
        for k in 0..s.nrows() {
            let l = lam[k];
            if l == 0.0 {
                continue;
            }
            for q in s.rs[k] as usize..s.rs[k + 1] as usize {
                let j = s.tv[q] as usize;
                let c = s.tc[q];
                clo[j] = add_dn(clo[j], mul_dn(l, c));
                chi[j] = add_up(chi[j], mul_up(l, c));
            }
            rhs = add_up(rhs, if l > 0.0 { mul_up(l, s.rhi[k]) } else { mul_up(l, s.rlo[k]) });
        }
        let mut lb = 0.0;
        for j in 0..n {
            let (l, u) = (s.lo[j], s.hi[j]);
            let v = mul_dn(clo[j], l).min(mul_dn(clo[j], u)).min(mul_dn(chi[j], l)).min(mul_dn(chi[j], u));
            lb = add_dn(lb, v);
        }
        if lb > rhs {
            return true;
        }
    }
    false
}

/// Phase-1 LP on the current box; certified infeasibility or not.
pub fn lp_feasibility(s: &Sys) -> LpResult {
    let mut sp = Simplex::new(s);
    match sp.solve(5000) {
        None => LpResult::Unknown,
        Some(obj) => {
            if obj <= 1e-9 {
                LpResult::Feasible
            } else {
                let y = sp.duals();
                if check_farkas(s, &y) {
                    LpResult::Infeasible(y)
                } else {
                    LpResult::Unknown
                }
            }
        }
    }
}
