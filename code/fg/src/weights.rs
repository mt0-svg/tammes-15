//! Constants of the test T and the weight tables (README.md, sections "The test T").

use crate::graph::all_types;
use crate::iv::{Iv, PI_IV};

/// d as an interval from a value in degrees given as an exact rational num / den.
pub fn deg(num: f64, den: f64) -> Iv {
    Iv::pt(num).div(Iv::pt(den)).mul(PI_IV).div(Iv::pt(180.0))
}
pub fn dlo() -> Iv {
    deg(5365785.0, 100000.0)
}
pub fn dhi() -> Iv {
    deg(566716.0, 10000.0)
}
pub fn two_pi() -> Iv {
    PI_IV.scale(2.0)
}
/// alpha at the two ends of the range, as enclosures.
pub fn alpha_lo() -> Iv {
    let d = dlo();
    let a = crate::geom::alpha(d);
    a
}
pub fn alpha_hi() -> Iv {
    crate::geom::alpha(dhi())
}
/// Triangle area 3 alpha(dlo) - pi, the least area of a triangle for d in [dlo, dhi].
pub fn tri_area_lo() -> Iv {
    alpha_lo().scale(3.0).sub(PI_IV)
}

/// W1: the vertex rows at v alone. Type (t, q, p5, p6) is feasible iff some a in
/// [alpha(dlo), alpha(dhi)] has m a <= 2 pi <= (t + 2 q) a + (p5 + p6) pi. Decided with outward
/// enclosures (the margins are at least 1.07 degrees, constants.out).
pub fn w1_feasible(t: [u8; 4]) -> bool {
    let m = (t[0] + t[1] + t[2] + t[3]) as f64;
    let p = (t[2] + t[3]) as f64;
    let tq = (t[0] + 2 * t[1]) as f64;
    let al = alpha_lo();
    let ah = alpha_hi();
    let tp = two_pi();
    // feasible a: [max(al, (2pi - p pi)/(t + 2q)), min(ah, 2 pi / m)]
    let upper = ah.hi.min(tp.div(Iv::pt(m)).hi);
    let lower = if p >= 2.0 {
        al.lo
    } else if tq == 0.0 {
        f64::INFINITY
    } else {
        al.lo.max(tp.sub(PI_IV.scale(p)).div(Iv::pt(tq)).lo)
    };
    // decisive only with a margin: assert the decision does not depend on rounding
    let upper_in = ah.lo.min(tp.div(Iv::pt(m)).lo);
    let lower_in = if p >= 2.0 {
        al.hi
    } else if tq == 0.0 {
        f64::INFINITY
    } else {
        al.hi.max(tp.sub(PI_IV.scale(p)).div(Iv::pt(tq)).hi)
    };
    let a = lower <= upper;
    let b = lower_in <= upper_in;
    assert_eq!(a, b, "W1 decision too close to the boundary for type {:?}", t);
    a
}

/// Mask (over the type indices of `all_types`) of the types that W1 forbids.
pub fn w1_forbidden_mask() -> u128 {
    let mut m = 0u128;
    for (i, t) in all_types().iter().enumerate() {
        if !w1_feasible(*t) {
            m |= 1u128 << i;
        }
    }
    m
}

/// The W3 tables read from weights.txt (written by `amin table`).
pub struct W3 {
    /// lower bound of e(f) = area(f) - (|f| - 2) T(dlo) for faces of size 3..6 (index |f| - 3)
    pub eps: [f64; 4],
    /// lower bound of the sum of e(f) over the faces at a vertex, by type index (inf if the type
    /// admits no corners)
    pub beta: Vec<f64>,
    /// upper bound of 4 pi - (2n - 4) T(dlo), by n (index n)
    pub slack: [f64; 32],
    /// lower bound of e(f) for a hexagon that holds a rattler (cap of radius h(dlo))
    pub eps6r: f64,
}

impl W3 {
    pub fn read(path: &str) -> W3 {
        let s = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("reading {path}: {e}"));
        let nt = all_types().len();
        let mut w = W3 { eps: [f64::NAN; 4], beta: vec![f64::NAN; nt], slack: [f64::NAN; 32], eps6r: f64::NAN };
        let mut done = false;
        for line in s.lines() {
            let f: Vec<&str> = line.split_whitespace().collect();
            if f.is_empty() || f[0].starts_with('#') {
                continue;
            }
            let num = |x: &str| -> f64 {
                if x == "inf" {
                    f64::INFINITY
                } else {
                    x.parse().unwrap()
                }
            };
            match f[0] {
                "eps" => w.eps[f[1].parse::<usize>().unwrap() - 3] = num(f[2]),
                "beta" => w.beta[f[1].parse::<usize>().unwrap()] = num(f[6]),
                "epsr" => w.eps6r = num(f[2]),
                "slack" => w.slack[f[1].parse::<usize>().unwrap()] = num(f[2]),
                "end" => done = true,
                _ => {}
            }
        }
        assert!(done, "weights file {path} has no end line");
        assert!(w.eps.iter().all(|x| !x.is_nan()), "missing eps");
        assert!(w.beta.iter().all(|x| !x.is_nan()), "missing beta");
        assert!(!w.eps6r.is_nan(), "missing epsr");
        w
    }
}
