//! Best-first interval branch and bound for a lower bound of a minimum over a box.

use crate::iv::Iv;
use std::cmp::Ordering;
use std::collections::BinaryHeap;

#[derive(Clone, Copy)]
struct Node {
    lb: f64,
    x: [Iv; 4],
}
impl PartialEq for Node {
    fn eq(&self, o: &Self) -> bool {
        self.lb == o.lb
    }
}
impl Eq for Node {}
impl PartialOrd for Node {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Node {
    fn cmp(&self, o: &Self) -> Ordering {
        // min-heap on lb
        o.lb.partial_cmp(&self.lb).unwrap_or(Ordering::Equal)
    }
}

pub struct Result {
    /// rigorous lower bound of the minimum over the feasible part of the root box
    /// (+inf if the whole box was refuted)
    pub lb: f64,
    /// value at a point that the evaluation did not refute (not rigorous; stopping only)
    pub ub: f64,
    pub nodes: u64,
    /// true if the gap closed below tol; false if stopped by the node budget or the width floor
    pub converged: bool,
}

/// `eval(box)` returns None if the box holds no feasible point, else a lower bound of the
/// objective over its feasible points. `dims` coordinates of the box are split.
pub fn minimize<F: Fn(&[Iv; 4]) -> Option<f64>>(root: [Iv; 4], dims: usize, eval: F, tol: f64, min_w: f64, max_nodes: u64) -> Result {
    let mut heap = BinaryHeap::new();
    let mut ub = f64::INFINITY;
    let mut nodes = 1u64;
    if let Some(lb) = eval(&root) {
        heap.push(Node { lb, x: root });
    }
    let point_ub = |x: &[Iv; 4]| -> f64 {
        let mut p = *x;
        for c in p.iter_mut().take(dims) {
            *c = Iv::pt(c.mid());
        }
        eval(&p).unwrap_or(f64::INFINITY)
    };
    loop {
        let Some(nd) = heap.pop() else {
            return Result { lb: f64::INFINITY, ub, nodes, converged: true };
        };
        if ub - nd.lb <= tol {
            return Result { lb: nd.lb, ub, nodes, converged: true };
        }
        // widest coordinate
        let mut k = 0;
        for i in 1..dims {
            if nd.x[i].w() > nd.x[k].w() {
                k = i;
            }
        }
        if nd.x[k].w() < min_w || nodes >= max_nodes {
            return Result { lb: nd.lb, ub, nodes, converged: false };
        }
        let m = nd.x[k].mid();
        for half in 0..2 {
            let mut c = nd.x;
            c[k] = if half == 0 { Iv::new(nd.x[k].lo, m) } else { Iv::new(m, nd.x[k].hi) };
            nodes += 1;
            if let Some(lb) = eval(&c) {
                let lb = lb.max(nd.lb);
                ub = ub.min(point_ub(&c));
                heap.push(Node { lb, x: c });
            }
        }
    }
}
