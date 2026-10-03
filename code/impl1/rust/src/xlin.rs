//! Rigorous linear relaxation of the level-2 face relations on a box, and an LP kill test with a
//! verified Farkas certificate (lp::check_farkas). Exploratory option, not used by the proof.
//!
//! For a relation o = F(x_1, ..., x_K) satisfied by every solution in the box B, with F smooth on
//! B (every asin/acos argument strictly inside (-1, 1) and no division by an interval containing
//! 0, checked on the whole box by the interval evaluation): for x in B, the mean value theorem on
//! the segment [c, x] (inside B, which is convex) gives F(x) = F(c) + grad F(xi) . (x - c), and
//! grad F(xi) lies in the interval enclosure J of the gradient over B (forward-mode automatic
//! differentiation in interval arithmetic). With g_j = mid(J_j) (an f64 used as an exact
//! coefficient), r_j >= |J_j - g_j| and h_j >= |x_j - c_j| on B:
//!   F(c) - g.c - sum_j r_j h_j  <=  o - g.x  <=  F(c) - g.c + sum_j r_j h_j,
//! with F(c) and g.c enclosed in outward-rounded arithmetic. The error term is O(width^2), so
//! on small boxes the rows are much tighter than the interval (hull) bounds, and the LP couples
//! all faces through the vertex rows at once.
//! Relations: a = alpha(d); rhombus y = rho(x, d), x = rho(y, d); pentagon fan from each corner
//! (u_{i+1}, u_{i-1}, d) -> (u_i, u_{i+2}, u_{i-2}); hexagon (u_1, u_3, u_5, d) -> (u_0, u_2, u_4)
//! for both parities (T1-T6 of Section 6.2). Wheel variables do not enter the LP.

use crate::deep::{FaceK, Prob};
use crate::iv::{add_up, mul_up, sub_dn};
use crate::ivt::Iv;
use crate::lp::{check_farkas, lp_feasibility, LpResult};
use crate::lpopt::{safe_lower, Lp};
use crate::system::Sys;

/// Value and gradient (with respect to K inputs) enclosed on a box; `ok` is false as soon as an
/// operation leaves its smooth domain somewhere on the box.
#[derive(Clone, Copy, Debug)]
pub struct Ad<const K: usize> {
    pub v: Iv,
    pub g: [Iv; K],
    pub ok: bool,
}

const Z: Iv = Iv { lo: 0.0, hi: 0.0 };

impl<const K: usize> Ad<K> {
    pub fn var(x: Iv, j: usize) -> Self {
        let mut g = [Z; K];
        g[j] = Iv::pt(1.0);
        Ad { v: x, g, ok: true }
    }
    pub fn cst(x: Iv) -> Self {
        Ad { v: x, g: [Z; K], ok: true }
    }
    fn map(self, v: Iv, dv: Iv, ok: bool) -> Self {
        let mut g = [Z; K];
        for j in 0..K {
            g[j] = dv.mul(self.g[j]);
        }
        Ad { v, g, ok: self.ok && ok && v.lo <= v.hi && dv.lo <= dv.hi }
    }
    pub fn add(self, o: Self) -> Self {
        let mut g = [Z; K];
        for j in 0..K {
            g[j] = self.g[j].add(o.g[j]);
        }
        Ad { v: self.v.add(o.v), g, ok: self.ok && o.ok }
    }
    pub fn sub(self, o: Self) -> Self {
        let mut g = [Z; K];
        for j in 0..K {
            g[j] = self.g[j].sub(o.g[j]);
        }
        Ad { v: self.v.sub(o.v), g, ok: self.ok && o.ok }
    }
    pub fn mul(self, o: Self) -> Self {
        let mut g = [Z; K];
        for j in 0..K {
            g[j] = self.g[j].mul(o.v).add(self.v.mul(o.g[j]));
        }
        Ad { v: self.v.mul(o.v), g, ok: self.ok && o.ok }
    }
    pub fn div(self, o: Self) -> Self {
        let ok = !(o.v.lo <= 0.0 && o.v.hi >= 0.0) && o.v.lo <= o.v.hi;
        let q = self.v.div(o.v);
        let o2 = o.v.sqr();
        let mut g = [Z; K];
        for j in 0..K {
            g[j] = self.g[j].mul(o.v).sub(self.v.mul(o.g[j])).div(o2);
        }
        Ad { v: q, g, ok: self.ok && o.ok && ok }
    }
    pub fn scale(self, c: f64) -> Self {
        let mut g = [Z; K];
        for j in 0..K {
            g[j] = self.g[j].scale(c);
        }
        Ad { v: self.v.scale(c), g, ok: self.ok }
    }
    pub fn sin(self) -> Self {
        self.map(self.v.sin(), self.v.cos(), true)
    }
    pub fn cos(self) -> Self {
        self.map(self.v.cos(), self.v.sin().neg(), true)
    }
    pub fn atan(self) -> Self {
        let den = Iv::pt(1.0).add(self.v.sqr());
        self.map(self.v.atan(), Iv::pt(1.0).div(den), true)
    }
    /// sqrt(1 - x^2) with a positive lower bound, or None
    fn cofactor(x: Iv) -> Option<Iv> {
        if !(x.lo > -1.0 && x.hi < 1.0) {
            return None;
        }
        let s = Iv::pt(1.0).sub(x.sqr()).sqrt();
        if s.lo > 0.0 {
            Some(s)
        } else {
            None
        }
    }
    pub fn asin(self) -> Self {
        match Self::cofactor(self.v) {
            Some(s) => self.map(self.v.asin(), Iv::pt(1.0).div(s), true),
            None => Ad { v: self.v.asin(), g: self.g, ok: false },
        }
    }
    pub fn acos(self) -> Self {
        match Self::cofactor(self.v) {
            Some(s) => self.map(self.v.acos(), Iv::pt(-1.0).div(s), true),
            None => Ad { v: self.v.acos(), g: self.g, ok: false },
        }
    }
}

/// Base of the isosceles triangle with legs d and apex angle u (T1).
pub fn ad_iso_base<const K: usize>(u: Ad<K>, d: Ad<K>) -> Ad<K> {
    d.sin().mul(u.scale(0.5).sin()).asin().scale(2.0)
}
/// Base angle of the isosceles triangle with legs d and apex angle u (T1).
pub fn ad_iso_angle<const K: usize>(u: Ad<K>, d: Ad<K>) -> Ad<K> {
    let h = u.scale(0.5);
    h.cos().div(d.cos().mul(h.sin())).atan()
}
/// Angle opposite g in the triangle with sides g, e, f: acos((cos g - cos e cos f)/(sin e sin f)) (T2).
pub fn ad_tri_angle<const K: usize>(g: Ad<K>, e: Ad<K>, f: Ad<K>) -> Ad<K> {
    g.cos().sub(e.cos().mul(f.cos())).div(e.sin().mul(f.sin())).acos()
}

fn push_row(sys: &mut Sys, terms: &[(u32, f64)], lo: f64, hi: f64) {
    for &(v, c) in terms {
        sys.tv.push(v);
        sys.tc.push(c);
    }
    sys.rs.push(sys.tv.len() as u32);
    sys.rlo.push(lo);
    sys.rhi.push(hi);
}

/// Adds the mean-value rows of o_m = F_m(x) (m < M) on the box; returns the number of rows.
fn lin_rows<const K: usize, const M: usize>(sys: &mut Sys, b: &[Iv], inp: [usize; K], out: [usize; M], f: &dyn Fn(&[Ad<K>; K]) -> [Ad<K>; M]) -> usize {
    let mut c = [0.0f64; K];
    let mut h = [0.0f64; K];
    for j in 0..K {
        let x = b[inp[j]];
        c[j] = x.mid();
        h[j] = (c[j] - x.lo).next_up().max((x.hi - c[j]).next_up());
    }
    let xp: [Ad<K>; K] = std::array::from_fn(|j| Ad::var(Iv::pt(c[j]), j));
    let xb: [Ad<K>; K] = std::array::from_fn(|j| Ad::var(b[inp[j]], j));
    let fp = f(&xp);
    let fb = f(&xb);
    let mut n = 0;
    for m in 0..M {
        if !fp[m].ok || !fb[m].ok || !(fp[m].v.lo <= fp[m].v.hi) {
            continue;
        }
        if fb[m].g.iter().any(|x| !(x.lo.is_finite() && x.hi.is_finite())) {
            continue;
        }
        let mut terms: Vec<(u32, f64)> = Vec::with_capacity(K + 1);
        terms.push((out[m] as u32, 1.0));
        let mut acc = fp[m].v;
        let mut r = 0.0f64;
        for j in 0..K {
            let jj = fb[m].g[j];
            let g = jj.mid();
            let rj = (jj.hi - g).next_up().max((g - jj.lo).next_up());
            r = add_up(r, mul_up(rj, h[j]));
            acc = acc.sub(Iv::pt(g).mul(Iv::pt(c[j])));
            terms.push((inp[j] as u32, -g));
        }
        push_row(sys, &terms, sub_dn(acc.lo, r), add_up(acc.hi, r));
        n += 1;
    }
    n
}

/// Linear relaxation of the case on box `b` (level-1 rows of `p.sys` plus mean-value rows), as
/// a Sys whose variables are those of p.sys followed by d.
pub fn relaxation(p: &Prob, b: &[Iv]) -> Sys {
    let mut s = p.sys.clone();
    for j in 0..p.nvar {
        s.lo[j] = b[j].lo;
        s.hi[j] = b[j].hi;
    }
    let di = p.di;
    debug_assert_eq!(di, p.nvar);
    s.lo.push(b[di].lo);
    s.hi.push(b[di].hi);
    s.nvar += 1;
    lin_rows::<1, 1>(&mut s, b, [di], [0], &|x| {
        let c = x[0].cos();
        [c.div(c.add(Ad::cst(Iv::pt(1.0)))).acos()]
    });
    for fk in &p.faces {
        match fk {
            FaceK::Tri => {}
            FaceK::Rhombus { x, y } => {
                let rho = |x: &[Ad<2>; 2]| [ad_iso_angle(x[0], x[1]).scale(2.0)];
                lin_rows::<2, 1>(&mut s, b, [*x, di], [*y], &rho);
                lin_rows::<2, 1>(&mut s, b, [*y, di], [*x], &rho);
            }
            FaceK::Pent { u } => {
                let fan = |x: &[Ad<3>; 3]| {
                    let (up, um, d) = (x[0], x[1], x[2]);
                    let (e, b1) = (ad_iso_base(up, d), ad_iso_angle(up, d));
                    let (f, b3) = (ad_iso_base(um, d), ad_iso_angle(um, d));
                    [b1.add(ad_tri_angle(d, e, f)).add(b3), b1.add(ad_tri_angle(f, e, d)), b3.add(ad_tri_angle(e, f, d))]
                };
                for i in 0..5 {
                    lin_rows::<3, 3>(&mut s, b, [u[(i + 1) % 5], u[(i + 4) % 5], di], [u[i], u[(i + 2) % 5], u[(i + 3) % 5]], &fan);
                }
            }
            FaceK::Hex { u, .. } => {
                let hexf = |x: &[Ad<4>; 4]| {
                    let d = x[3];
                    let (e1, b1) = (ad_iso_base(x[0], d), ad_iso_angle(x[0], d));
                    let (e3, b3) = (ad_iso_base(x[1], d), ad_iso_angle(x[1], d));
                    let (e5, b5) = (ad_iso_base(x[2], d), ad_iso_angle(x[2], d));
                    [
                        b5.add(ad_tri_angle(e3, e1, e5)).add(b1),
                        b1.add(ad_tri_angle(e5, e1, e3)).add(b3),
                        b3.add(ad_tri_angle(e1, e3, e5)).add(b5),
                    ]
                };
                for par in 0..2 {
                    let k = |j: usize| u[(j + par) % 6];
                    lin_rows::<4, 3>(&mut s, b, [k(1), k(3), k(5), di], [k(0), k(2), k(4)], &hexf);
                }
            }
        }
    }
    s
}

/// True when the linear relaxation on `b` is infeasible with a verified Farkas certificate.
pub fn lp_kill(p: &Prob, b: &[Iv]) -> bool {
    let s = relaxation(p, b);
    matches!(lp_feasibility(&s), LpResult::Infeasible(_))
}

/// LP contraction on the relaxation of box `b`: Err when it is infeasible (verified Farkas
/// certificate); otherwise the bounds of `vars` (box indices <= d) are tightened by LP
/// minimisation and maximisation, each bound certified by `lpopt::safe_lower` (weak duality in
/// outward-rounded arithmetic), so the contraction is valid whatever the simplex accuracy.
pub fn lp_contract(p: &Prob, b: &mut [Iv], vars: &[usize]) -> Result<(), ()> {
    let s = relaxation(p, b);
    let mut lp = Lp::new(&s);
    match lp.phase1(5000) {
        None => return Ok(()),
        Some(inf) if inf > 1e-9 => {
            let y = lp.duals();
            return if check_farkas(&s, &y) { Err(()) } else { Ok(()) };
        }
        _ => {}
    }
    let mut c = vec![0.0; s.nvar];
    for &j in vars {
        for sgn in [1.0f64, -1.0] {
            c[j] = sgn;
            if lp.phase2(&c, 3000) {
                let y = lp.duals();
                let lbv = safe_lower(&s, &c, &y);
                if sgn > 0.0 {
                    if lbv > b[j].lo {
                        b[j].lo = lbv;
                    }
                } else if -lbv < b[j].hi {
                    b[j].hi = -lbv;
                }
                if !(b[j].lo <= b[j].hi) {
                    return Err(());
                }
            }
            c[j] = 0.0;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poly;

    fn sys0(nv: usize, b: &[Iv]) -> Sys {
        let mut s = Sys::default();
        s.rs.push(0);
        s.nvar = nv;
        s.lo = b.iter().map(|x| x.lo).collect();
        s.hi = b.iter().map(|x| x.hi).collect();
        s
    }

    /// Every row must hold at the true configuration (rows valid on the whole box).
    fn rows_hold(s: &Sys, x: &[f64]) {
        for r in 0..s.nrows() {
            let v: f64 = (s.rs[r] as usize..s.rs[r + 1] as usize).map(|k| s.tc[k] * x[s.tv[k] as usize]).sum();
            let tol = 1e-12 * (1.0 + (s.rs[r] as usize..s.rs[r + 1] as usize).map(|k| (s.tc[k] * x[s.tv[k] as usize]).abs()).sum::<f64>());
            assert!(s.rlo[r] - tol <= v && v <= s.rhi[r] + tol, "row {r}: {} <= {v} <= {}", s.rlo[r], s.rhi[r]);
        }
    }

    /// Mean-value rows of the face relations contain random true faces, on boxes of random
    /// widths (up to 0.4 rad, possibly reaching past pi) around them.
    #[test]
    fn rows_contain_true_faces() {
        let mut seed = 987654321u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((seed >> 11) as f64) / ((1u64 << 53) as f64)
        };
        let mut rows = 0usize;
        let mut faces = [0usize; 3];
        for _ in 0..30000 {
            let d = 0.9 + 0.13 * rnd();
            let m = [4, 5, 6][(rnd() * 3.0) as usize % 3];
            let params: Vec<f64> = (0..m - 3).map(|_| 1.2 + 1.9 * rnd()).collect();
            let Some((vs, ang)) = poly::build(m, d, &params) else { continue };
            if !poly::valid_face(d, &vs, &ang, 0.0) {
                continue;
            }
            faces[m - 4] += 1;
            // variables: corners 0..m, d at m, a = alpha(d) at m + 1
            let a = (d.cos() / (1.0 + d.cos())).acos();
            let mut x: Vec<f64> = ang.clone();
            x.push(d);
            x.push(a);
            let wmax = [1e-6, 1e-3, 0.05, 0.4][(rnd() * 4.0) as usize % 4];
            let b: Vec<Iv> = x
                .iter()
                .enumerate()
                .map(|(j, &t)| {
                    let w = if j == m { wmax * 0.2 } else { wmax };
                    Iv::new(t - w * rnd(), t + w * rnd())
                })
                .collect();
            let di = m;
            let mut s = sys0(m + 2, &b);
            lin_rows::<1, 1>(&mut s, &b, [di], [m + 1], &|x| {
                let c = x[0].cos();
                [c.div(c.add(Ad::cst(Iv::pt(1.0)))).acos()]
            });
            match m {
                4 => {
                    let rho = |x: &[Ad<2>; 2]| [ad_iso_angle(x[0], x[1]).scale(2.0)];
                    lin_rows::<2, 1>(&mut s, &b, [0, di], [1], &rho);
                    lin_rows::<2, 1>(&mut s, &b, [1, di], [0], &rho);
                    lin_rows::<2, 1>(&mut s, &b, [2, di], [3], &rho);
                }
                5 => {
                    let fan = |x: &[Ad<3>; 3]| {
                        let (up, um, d) = (x[0], x[1], x[2]);
                        let (e, b1) = (ad_iso_base(up, d), ad_iso_angle(up, d));
                        let (f, b3) = (ad_iso_base(um, d), ad_iso_angle(um, d));
                        [b1.add(ad_tri_angle(d, e, f)).add(b3), b1.add(ad_tri_angle(f, e, d)), b3.add(ad_tri_angle(e, f, d))]
                    };
                    for i in 0..5 {
                        lin_rows::<3, 3>(&mut s, &b, [(i + 1) % 5, (i + 4) % 5, di], [i, (i + 2) % 5, (i + 3) % 5], &fan);
                    }
                }
                _ => {
                    let hexf = |x: &[Ad<4>; 4]| {
                        let d = x[3];
                        let (e1, b1) = (ad_iso_base(x[0], d), ad_iso_angle(x[0], d));
                        let (e3, b3) = (ad_iso_base(x[1], d), ad_iso_angle(x[1], d));
                        let (e5, b5) = (ad_iso_base(x[2], d), ad_iso_angle(x[2], d));
                        [
                            b5.add(ad_tri_angle(e3, e1, e5)).add(b1),
                            b1.add(ad_tri_angle(e5, e1, e3)).add(b3),
                            b3.add(ad_tri_angle(e1, e3, e5)).add(b5),
                        ]
                    };
                    for par in 0..2 {
                        let k = |j: usize| (j + par) % 6;
                        lin_rows::<4, 3>(&mut s, &b, [k(1), k(3), k(5), di], [k(0), k(2), k(4)], &hexf);
                    }
                }
            }
            rows += s.nrows();
            rows_hold(&s, &x);
        }
        assert!(faces.iter().all(|&f| f > 300) && rows > 50000, "{faces:?} {rows}");
    }

    /// On small boxes the rows are tight: the width of each row interval is O(width^2).
    #[test]
    fn rows_are_second_order() {
        let d = 0.95;
        let (_, ang) = poly::build(5, d, &[1.9, 2.1]).unwrap();
        for &w in &[1e-2, 1e-3] {
            let mut b: Vec<Iv> = ang.iter().map(|&t| Iv::new(t - w, t + w)).collect();
            b.push(Iv::new(d - w, d + w));
            let mut s = sys0(6, &b);
            let fan = |x: &[Ad<3>; 3]| {
                let (up, um, d) = (x[0], x[1], x[2]);
                let (e, b1) = (ad_iso_base(up, d), ad_iso_angle(up, d));
                let (f, b3) = (ad_iso_base(um, d), ad_iso_angle(um, d));
                [b1.add(ad_tri_angle(d, e, f)).add(b3), b1.add(ad_tri_angle(f, e, d)), b3.add(ad_tri_angle(e, f, d))]
            };
            lin_rows::<3, 3>(&mut s, &b, [1, 4, 5], [0, 2, 3], &fan);
            assert_eq!(s.nrows(), 3);
            for r in 0..3 {
                assert!(s.rhi[r] - s.rlo[r] < 200.0 * w * w, "w = {w}: row width {}", s.rhi[r] - s.rlo[r]);
            }
        }
    }
}
