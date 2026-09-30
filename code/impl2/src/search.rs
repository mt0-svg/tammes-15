//! Depth-first branch and prune.
//!
//! A node is a box. It is discarded when propagation proves it empty, or (optional) when the
//! Local discard or the Pair refutation fires (glue.rs). Otherwise the branchable variable with
//! the largest width relative to its width in the propagated root box is bisected at its midpoint
//! (the two closed halves cover the box). A box whose branchable variables are all narrower than
//! `tol` is reported UNRESOLVED and never discarded.

use crate::glue::{Glue, GlueOpts, GlueVerdict};
use crate::iv::I;
use crate::model::Model;
use crate::prop::{Opts, Prop, Stats};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Killed,
    Budget,
    Unresolved,
}

#[derive(Clone, Debug)]
pub struct SearchOpts {
    pub nodes: u64,
    pub tol: f64,
    pub dweight: f64,
    pub prop: Opts,
    pub glue: Option<GlueOpts>,
    /// 3B shaving: slices of 1/shave of every branchable variable at both ends are tested by
    /// propagation and removed when refuted (0 = off)
    pub shave: usize,
    /// wall-clock limit per case in seconds (BUDGET when exceeded; 0 = none)
    pub maxsec: f64,
    /// incremental propagation: a child box is propagated from the constraints of its split
    /// variable, a shaving slice from those of the shaved variable
    pub incr: bool,
    /// maximal number of shaving sweeps per node
    pub shave_rounds: usize,
    /// LP relaxation test (relax.rs): 0 off, 1 feasibility, 2 also contract d, 3 also contract
    /// every branchable variable
    pub lp: usize,
    /// share of the tree (parallel runs): Some((i, n, depth)) keeps only the nodes of the given
    /// depth whose rank in the depth-first order is i mod n; the part runs 0..n of one case, with
    /// the same binary and options, cover the whole tree (the part above that depth is the same
    /// in every run: the search is deterministic)
    pub part: Option<(usize, usize, usize)>,
}

#[derive(Clone, Debug, Default)]
pub struct Report {
    pub nodes: u64,
    pub empty: u64,
    pub local: u64,
    pub pair: u64,
    pub edge: u64,
    pub lpkill: u64,
    pub evals: u64,
    pub maxdepth: usize,
    /// fraction of the root volume (in the split measure) that was refuted
    pub done: f64,
    pub unresolved_box: Option<Vec<I>>,
    /// with a part: nodes met at the part depth, the ones kept, and the weight left to the others
    pub part_seen: u64,
    pub part_kept: u64,
    pub skipped: f64,
}

pub fn solve(m: &Model, so: &SearchOpts) -> (Verdict, Report) {
    let mut prop = Prop::new(m);
    let mut st = Stats { evals: 0 };
    let mut rep = Report::default();
    let mut root = m.init.clone();
    let glue = so.glue.as_ref().map(|go| Glue::new(m, go.clone()));
    if !prop.run(m, &mut root, &so.prop, &mut st) {
        rep.nodes = 1;
        rep.empty = 1;
        rep.evals = st.evals;
        rep.done = 1.0;
        return (Verdict::Killed, rep);
    }
    let refw: Vec<f64> = (0..m.nv)
        .map(|v| {
            let w = root[v].width();
            let w = if w > 0.0 { w } else { 1.0 };
            if v == crate::model::VD {
                w / so.dweight
            } else {
                w
            }
        })
        .collect();
    // stack of (box, depth, weight)
    let mut stack: Vec<(Vec<I>, usize, f64, usize)> = vec![(root, 0, 1.0, usize::MAX)];
    let mut first = true;
    let t_start = std::time::Instant::now();
    let diag = std::env::var("VK_DIAG").is_ok();
    let mut splits = vec![0u64; m.nv];
    while let Some((mut b, depth, wt, split)) = stack.pop() {
        if rep.nodes >= so.nodes || (so.maxsec > 0.0 && t_start.elapsed().as_secs_f64() > so.maxsec) {
            if std::env::var("VK_DUMP").is_ok() {
                dump_open(m, &b, &stack);
            }
            if diag {
                print_splits(m, &splits);
            }
            return (Verdict::Budget, rep);
        }
        if let Some((pi, pn, pd)) = so.part {
            if depth == pd {
                let rank = rep.part_seen;
                rep.part_seen += 1;
                if rank % pn as u64 != pi as u64 {
                    rep.skipped += wt;
                    continue;
                }
                rep.part_kept += 1;
            }
        }
        rep.nodes += 1;
        rep.maxdepth = rep.maxdepth.max(depth);
        if !first {
            let seeds = [split];
            let ok = if so.incr && split != usize::MAX { prop.run_seeded(m, &mut b, &so.prop, &mut st, Some(&seeds)) } else { prop.run(m, &mut b, &so.prop, &mut st) };
            if !ok {
                rep.empty += 1;
                rep.done += wt;
                rep.evals = st.evals;
                continue;
            }
        }
        first = false;
        if so.shave > 0 {
            match shave(m, &mut b, &mut prop, &so.prop, &mut st, so.shave, so.tol, so.incr, so.shave_rounds) {
                true => {}
                false => {
                    rep.empty += 1;
                    rep.done += wt;
                    rep.evals = st.evals;
                    continue;
                }
            }
        }
        if let Some(gl) = &glue {
            match gl.test(&b) {
                GlueVerdict::Local => {
                    if diag {
                        let mr = gl.place(&b).map(|(_, r)| r.iter().cloned().fold(0.0, f64::max)).unwrap_or(f64::NAN);
                        let mw = (0..m.nv).filter(|&v| m.branch[v]).map(|v| b[v].width()).fold(0.0, f64::max);
                        eprintln!("LOCAL depth {depth} maxrho {mr:.3e} maxw {mw:.3e} d [{:.12}, {:.12}]", b[crate::model::VD].lo.to_degrees(), b[crate::model::VD].hi.to_degrees());
                    }
                    rep.local += 1;
                    rep.done += wt;
                    continue;
                }
                GlueVerdict::Pair => {
                    rep.pair += 1;
                    rep.done += wt;
                    continue;
                }
                GlueVerdict::Edge => {
                    rep.edge += 1;
                    rep.done += wt;
                    continue;
                }
                GlueVerdict::None => {}
            }
        }
        if so.lp > 0 {
            let vars: Vec<usize> = match so.lp {
                1 => vec![],
                2 => vec![crate::model::VD],
                _ => (0..m.nv).filter(|&v| m.branch[v]).collect(),
            };
            match crate::relax::lp_test(m, &mut b, &vars, 400) {
                Some(false) => {
                    rep.lpkill += 1;
                    rep.done += wt;
                    continue;
                }
                Some(true) => {
                    if !prop.run_seeded(m, &mut b, &so.prop, &mut st, Some(&vars)) {
                        rep.lpkill += 1;
                        rep.done += wt;
                        continue;
                    }
                }
                None => {}
            }
        }
        // choose the split variable
        let mut best = usize::MAX;
        let mut bw = 0.0;
        let mut maxabs = 0.0f64;
        for v in 0..m.nv {
            if !m.branch[v] {
                continue;
            }
            let w = b[v].width();
            maxabs = maxabs.max(w);
            let rw = w / refw[v];
            if rw > bw {
                bw = rw;
                best = v;
            }
        }
        if best == usize::MAX || maxabs < so.tol {
            rep.evals = st.evals;
            rep.unresolved_box = Some(b);
            return (Verdict::Unresolved, rep);
        }
        splits[best] += 1;
        let x = b[best];
        let mid = x.mid();
        if !(mid > x.lo && mid < x.hi) {
            rep.evals = st.evals;
            rep.unresolved_box = Some(b);
            return (Verdict::Unresolved, rep);
        }
        let mut b1 = b.clone();
        b1[best] = I::new(x.lo, mid);
        b[best] = I::new(mid, x.hi);
        stack.push((b, depth + 1, wt * 0.5, best));
        stack.push((b1, depth + 1, wt * 0.5, best));
    }
    if diag {
        print_splits(m, &splits);
    }
    rep.evals = st.evals;
    (Verdict::Killed, rep)
}

/// Diagnostics (env VK_DIAG): how often each variable was split.
fn print_splits(m: &Model, splits: &[u64]) {
    let mut v: Vec<(u64, usize)> = splits.iter().enumerate().filter(|x| *x.1 > 0).map(|(i, &c)| (c, i)).collect();
    v.sort_by(|a, b| b.cmp(a));
    let s: Vec<String> = v.iter().take(25).map(|(c, i)| format!("{}:{}", m.names[*i], c)).collect();
    eprintln!("SPLITS {}", s.join(" "));
}

/// Diagnostics at BUDGET (env VK_DUMP): the open boxes (current and stack), their d ranges and
/// weights, and the hull of every variable over them.
fn dump_open(m: &Model, cur: &[I], stack: &[(Vec<I>, usize, f64, usize)]) {
    let mut hull: Vec<I> = cur.to_vec();
    eprintln!("open boxes: {} on the stack + current", stack.len());
    eprintln!("  current d [{:.9}, {:.9}] deg", cur[crate::model::VD].lo.to_degrees(), cur[crate::model::VD].hi.to_degrees());
    for (b, depth, wt, _) in stack {
        let d = b[crate::model::VD];
        eprintln!("  depth {depth} weight {wt:.3e} d [{:.9}, {:.9}] deg", d.lo.to_degrees(), d.hi.to_degrees());
        for v in 0..m.nv {
            hull[v] = hull[v].hull(b[v]);
        }
    }
    for v in 0..m.nv {
        eprintln!("  hull {} [{:.9}, {:.9}]", m.names[v], hull[v].lo, hull[v].hi);
    }
}

/// 3B shaving (Lhomme 1993). For each branchable variable and each end, the slice of width
/// w/k at that end is propagated alone; if propagation proves it empty, the slice holds no
/// genuine point and the variable is restricted to the rest (the cut point belongs to both
/// closed pieces, so nothing is lost). Returns false if the whole box is proved empty.
fn shave(m: &Model, b: &mut Vec<I>, prop: &mut Prop, po: &Opts, st: &mut Stats, k: usize, tol: f64, incr: bool, max_rounds: usize) -> bool {
    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < max_rounds {
        changed = false;
        rounds += 1;
        for v in 0..m.nv {
            if !m.branch[v] {
                continue;
            }
            for end in 0..2 {
                let x = b[v];
                let w = x.width();
                if !(w > tol) {
                    continue;
                }
                let cut = if end == 0 { x.lo + w / k as f64 } else { x.hi - w / k as f64 };
                if !(cut > x.lo && cut < x.hi) {
                    continue;
                }
                let mut t = b.clone();
                t[v] = if end == 0 { I::new(x.lo, cut) } else { I::new(cut, x.hi) };
                let seeds = [v];
                let sd = if incr { Some(&seeds[..]) } else { None };
                if !prop.run_seeded(m, &mut t, po, st, sd) {
                    b[v] = if end == 0 { I::new(cut, x.hi) } else { I::new(x.lo, cut) };
                    if !prop.run_seeded(m, b, po, st, sd) {
                        return false;
                    }
                    changed = true;
                }
            }
        }
    }
    true
}
