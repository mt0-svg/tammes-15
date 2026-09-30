//! Contractors and the propagation loop.
//!
//! Explicit relation out_k = F_k(in) (or out_k >= F_k(in)), F given by faces::eval. On a box B:
//! 1. natural enclosure V_k of F_k(B) (with the D<4> evaluation, which also gives an enclosure
//!    J_k of grad F_k over B and the flag ok = "F is C^1 on B");
//! 2. if ok: mean value form F_k(c) + J_k . (B - c) (c the midpoint, F_k(c) by a point
//!    evaluation); monotonicity: when J_kj has a sign, the minimum (maximum) of F_k over B is
//!    attained on the face x_j = lower (upper) end, so the lower (upper) bound is taken from an
//!    evaluation on that face; V_k is intersected with both;
//! 3. the output is intersected with V_k (Eq) or with [V_k.lo, inf) (Ge);
//! 4. Newton step on the inputs (if ok): for every genuine point y of B, F_k(y) lies in the
//!    target T (the output interval for Eq, (-inf, out.hi] for Ge) and in
//!    F_k(c) + sum_l J_kl (y_l - c_l), so J_kj (y_j - c_j) lies in T - F_k(c) - sum_{l != j} J_kl
//!    (B_l - c_l); when 0 is not in J_kj this bounds y_j.
//! An empty intersection anywhere means that no genuine point lies in B.

use crate::ad::{Num, D};
use crate::faces::{eval, Fam};
use crate::iv::{dn, up, I};
use crate::model::{Con, Kind, Lin, Model, Rel};

#[derive(Clone, Copy, Debug)]
pub struct Opts {
    pub mono: bool,
    pub newton: bool,
    pub ratio: f64,
    pub maxrounds: usize,
}

impl Default for Opts {
    fn default() -> Self {
        Opts { mono: true, newton: true, ratio: 0.02, maxrounds: 200 }
    }
}

pub struct Stats {
    pub evals: u64,
}

/// Optional profile (environment variable VK_PROF set): applications and nanoseconds per family.
pub static PROF_ON: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
pub static mut PROF: [(u64, u64); 16] = [(0, 0); 16];

fn fam_index(f: Fam) -> usize {
    f as usize
}

pub fn prof_report() {
    if !PROF_ON.load(std::sync::atomic::Ordering::Relaxed) {
        return;
    }
    let names = ["PentSplit", "PentFan", "HexAlt", "HexChain5", "HexC4Iso", "HexLong", "RhoY", "RhoD", "Alpha", "AlphaInv", "WCorner", "WTheta", "WBack", "Lin", "", ""];
    #[allow(static_mut_refs)]
    unsafe {
        for (i, (n, t)) in PROF.iter().enumerate() {
            if *n > 0 {
                eprintln!("prof {:10} applies {:10} total {:8.3} s  per apply {:7.2} us", names[i], n, *t as f64 * 1e-9, *t as f64 / *n as f64 * 1e-3);
            }
        }
    }
}

/// Division of a (possibly half-infinite) interval by an interval g with 0 not in g.
fn div_ext(num: I, g: I) -> I {
    debug_assert!(!g.contains0());
    // candidate quotients; infinite numerator ends give infinite results in the right direction
    let q = |a: f64, b: f64| -> f64 {
        if a.is_infinite() {
            if (a > 0.0) == (b > 0.0) {
                f64::INFINITY
            } else {
                f64::NEG_INFINITY
            }
        } else {
            a / b
        }
    };
    let p = [q(num.lo, g.lo), q(num.lo, g.hi), q(num.hi, g.lo), q(num.hi, g.hi)];
    let mut lo = f64::INFINITY;
    let mut hi = f64::NEG_INFINITY;
    for &x in &p {
        if x.is_nan() {
            return I::ENTIRE;
        }
        lo = lo.min(x);
        hi = hi.max(x);
    }
    I::new(dn(lo), up(hi))
}

/// eval on the input box x, remembered within one application of a relation (the key is the
/// input box itself, so a box changed by a Newton step is evaluated again).
fn cached_eval(fam: Fam, x: &[I; 4], nin: usize, cache: &mut Vec<([I; 4], Option<[I; 3]>)>, st: &mut Stats) -> Option<[I; 3]> {
    let same = |a: &[I; 4]| (0..nin).all(|j| a[j].lo.to_bits() == x[j].lo.to_bits() && a[j].hi.to_bits() == x[j].hi.to_bits());
    if let Some((_, v)) = cache.iter().find(|(a, _)| same(a)) {
        return *v;
    }
    st.evals += 1;
    let v = eval(fam, x);
    cache.push((*x, v));
    v
}

/// Apply an explicit relation. Returns false if the box is proved empty. Sets changed[v].
fn apply_rel(r: &Rel, b: &mut [I], o: &Opts, st: &mut Stats) -> bool {
    let fam = r.fam;
    let nin = fam.nin();
    let nout = fam.nout();
    let mut xd = [D::<4>::c(I::pt(0.0)); 4];
    for j in 0..nin {
        xd[j] = D::var(b[r.ins[j]], j);
    }
    st.evals += 1;
    let out = match eval(fam, &xd) {
        Some(v) => v,
        None => return false,
    };
    let mut xc = [I::pt(0.0); 4];
    let mut cen = [0.0f64; 4];
    for j in 0..nin {
        cen[j] = b[r.ins[j]].mid();
        xc[j] = I::pt(cen[j]);
    }
    let any_ok = (0..nout).any(|k| out[k].ok);
    let fc: Option<[I; 3]> = if any_ok && (o.newton || true) {
        st.evals += 1;
        eval(fam, &xc)
    } else {
        None
    };
    let mut cache: Vec<([I; 4], Option<[I; 3]>)> = Vec::with_capacity(6);
    for k in 0..nout {
        let mut v = out[k].v;
        let g = out[k].g;
        let ok = out[k].ok;
        if ok {
            if let Some(fc) = fc {
                // mean value form
                let mut m = fc[k];
                for j in 0..nin {
                    m = m + g[j] * (b[r.ins[j]] - xc[j]);
                }
                v = match v.meet(m) {
                    Some(x) => x,
                    None => return false,
                };
            }
            if o.mono {
                let mut mono_any = false;
                let mut lo_box = [I::pt(0.0); 4];
                let mut hi_box = [I::pt(0.0); 4];
                for j in 0..nin {
                    let x = b[r.ins[j]];
                    if g[j].lo >= 0.0 {
                        lo_box[j] = I::pt(x.lo);
                        hi_box[j] = I::pt(x.hi);
                        mono_any = true;
                    } else if g[j].hi <= 0.0 {
                        lo_box[j] = I::pt(x.hi);
                        hi_box[j] = I::pt(x.lo);
                        mono_any = true;
                    } else {
                        lo_box[j] = x;
                        hi_box[j] = x;
                    }
                }
                if mono_any {
                    // None cannot occur on a sub-box when F is C^1 on B; treat as no information
                    let lo = cached_eval(fam, &lo_box, nin, &mut cache, st).map(|w| w[k].lo).unwrap_or(f64::NEG_INFINITY);
                    let hi = cached_eval(fam, &hi_box, nin, &mut cache, st).map(|w| w[k].hi).unwrap_or(f64::INFINITY);
                    v = match v.meet(I::new(lo, hi)) {
                        Some(x) => x,
                        None => return false,
                    };
                }
            }
        }
        let ov = r.outs[k];
        let target = match r.kinds[k] {
            Kind::Eq => v,
            Kind::Ge => I::new(v.lo, f64::INFINITY),
        };
        b[ov] = match b[ov].meet(target) {
            Some(x) => x,
            None => return false,
        };
        // Newton step on the inputs
        if o.newton && ok {
            if let Some(fc) = fc {
                let t = match r.kinds[k] {
                    Kind::Eq => b[ov],
                    Kind::Ge => I::new(f64::NEG_INFINITY, b[ov].hi),
                };
                for j in 0..nin {
                    if g[j].contains0() {
                        continue;
                    }
                    let mut s = I::pt(0.0);
                    for l in 0..nin {
                        if l != j {
                            s = s + g[l] * (b[r.ins[l]] - xc[l]);
                        }
                    }
                    let rest = fc[k] + s;
                    if rest.is_bad() || !rest.lo.is_finite() || !rest.hi.is_finite() {
                        continue;
                    }
                    let num = I::new(
                        if t.lo.is_finite() { dn(t.lo - rest.hi) } else { f64::NEG_INFINITY },
                        if t.hi.is_finite() { up(t.hi - rest.lo) } else { f64::INFINITY },
                    );
                    let dx = div_ext(num, g[j]);
                    let nx = I::new(
                        if dx.lo.is_finite() { dn(cen[j] + dx.lo) } else { f64::NEG_INFINITY },
                        if dx.hi.is_finite() { up(cen[j] + dx.hi) } else { f64::INFINITY },
                    );
                    let iv = r.ins[j];
                    b[iv] = match b[iv].meet(nx) {
                        Some(x) => x,
                        None => return false,
                    };
                }
            }
        }
    }
    true
}

/// Linear row lo <= sum c_j x_j <= hi: contract every variable.
fn apply_lin(l: &Lin, b: &mut [I]) -> bool {
    let n = l.terms.len();
    for j in 0..n {
        let (vj, cj) = l.terms[j];
        // rest = sum over l != j of c_l x_l (outward)
        let mut rest = I::pt(0.0);
        for (i, &(vi, ci)) in l.terms.iter().enumerate() {
            if i != j {
                rest = rest + b[vi] * ci;
            }
        }
        if rest.is_bad() || !rest.lo.is_finite() || !rest.hi.is_finite() {
            continue;
        }
        // c_j x_j in [lo - rest.hi, hi - rest.lo]
        let num = I::new(
            if l.lo.is_finite() { dn(l.lo - rest.hi) } else { f64::NEG_INFINITY },
            if l.hi.is_finite() { up(l.hi - rest.lo) } else { f64::INFINITY },
        );
        let nx = div_ext(num, I::pt(cj));
        b[vj] = match b[vj].meet(nx) {
            Some(x) => x,
            None => return false,
        };
    }
    true
}

pub struct Prop {
    /// for each variable, the constraints that read or write it
    pub deps: Vec<Vec<usize>>,
    queue: Vec<usize>,
    inq: Vec<bool>,
}

fn con_vars(c: &Con) -> Vec<usize> {
    match c {
        Con::Rel(r) => {
            let mut v: Vec<usize> = r.ins[..r.fam.nin()].to_vec();
            v.extend_from_slice(&r.outs[..r.fam.nout()]);
            v
        }
        Con::Lin(l) => l.terms.iter().map(|t| t.0).collect(),
    }
}

impl Prop {
    pub fn new(m: &Model) -> Prop {
        let mut deps = vec![Vec::new(); m.nv];
        for (ci, c) in m.cons.iter().enumerate() {
            let mut vs = con_vars(c);
            vs.sort();
            vs.dedup();
            for v in vs {
                deps[v].push(ci);
            }
        }
        Prop { deps, queue: Vec::new(), inq: vec![false; m.cons.len()] }
    }

    /// Propagate to a (loose) fixed point. Returns false if the box is proved empty.
    pub fn run(&mut self, m: &Model, b: &mut [I], o: &Opts, st: &mut Stats) -> bool {
        self.run_seeded(m, b, o, st, None)
    }

    /// Same, starting from the constraints that contain one of the variables `seeds` (all
    /// constraints when None). Used when b is a propagated box in which only these variables
    /// were narrowed (a child after a split, a shaving slice). The start queue only affects how
    /// much is contracted, never soundness: every step is one of the sound contractions.
    pub fn run_seeded(&mut self, m: &Model, b: &mut [I], o: &Opts, st: &mut Stats, seeds: Option<&[usize]>) -> bool {
        self.queue.clear();
        match seeds {
            None => {
                for i in 0..m.cons.len() {
                    self.queue.push(i);
                    self.inq[i] = true;
                }
            }
            Some(vs) => {
                for &v in vs {
                    for &ci in &self.deps[v] {
                        if !self.inq[ci] {
                            self.inq[ci] = true;
                            self.queue.push(ci);
                        }
                    }
                }
            }
        }
        let mut head = 0usize;
        let limit = o.maxrounds * m.cons.len();
        let mut count = 0usize;
        let mut old = vec![I::pt(0.0); m.nv];
        let mut ok = true;
        while head < self.queue.len() {
            let ci = self.queue[head];
            head += 1;
            self.inq[ci] = false;
            count += 1;
            if count > limit {
                break;
            }
            let c = &m.cons[ci];
            let vars = con_vars(c);
            for &v in &vars {
                old[v] = b[v];
            }
            let prof = PROF_ON.load(std::sync::atomic::Ordering::Relaxed);
            let t0 = if prof { Some(std::time::Instant::now()) } else { None };
            let res = match c {
                Con::Rel(r) => apply_rel(r, b, o, st),
                Con::Lin(l) => apply_lin(l, b),
            };
            if let Some(t0) = t0 {
                let k = match c {
                    Con::Rel(r) => fam_index(r.fam),
                    Con::Lin(_) => 13,
                };
                #[allow(static_mut_refs)]
                unsafe {
                    PROF[k].0 += 1;
                    PROF[k].1 += t0.elapsed().as_nanos() as u64;
                }
            }
            if !res {
                ok = false;
                break;
            }
            for &v in &vars {
                let w0 = old[v].width();
                let w1 = b[v].width();
                if w1 < w0 && (w0 - w1 > o.ratio * w0 || (w1 == 0.0 && w0 > 0.0)) {
                    for &cj in &self.deps[v] {
                        if !self.inq[cj] && cj != ci {
                            self.inq[cj] = true;
                            self.queue.push(cj);
                        }
                    }
                }
            }
            if head > 4096 && head * 2 > self.queue.len() {
                self.queue.drain(..head);
                head = 0;
            }
        }
        for x in self.inq.iter_mut() {
            *x = false;
        }
        ok
    }
}

pub fn fam_of(c: &Con) -> Option<Fam> {
    match c {
        Con::Rel(r) => Some(r.fam),
        Con::Lin(_) => None,
    }
}
