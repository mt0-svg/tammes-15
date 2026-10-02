//! Spherical trigonometry of the faces (paper, Sections 5.2 and 5.3), on intervals.
//!
//! Every function is evaluated through its monotonicity, proved in the paper (T1 to T4, T7):
//! the value at the ends of the argument box, each computed in outward rounded arithmetic.

use crate::iv::{Iv, PI_IV};

/// Point versions (degenerate intervals) of the elementary relations.
fn ebase_pt(d: f64, u: f64) -> Iv {
    // 2 asin(sin d sin(u/2)), (T1)
    Iv::pt(d).sin().mul(Iv::pt(u).scale(0.5).sin()).meet(Iv::new(-1.0, 1.0)).unwrap().asin().scale(2.0)
}
fn bangle_pt(d: f64, u: f64) -> Iv {
    // atan(cos(u/2) / (cos d sin(u/2))), (T1)
    let h = Iv::pt(u).scale(0.5);
    h.cos().div(Iv::pt(d).cos().mul(h.sin())).atan()
}

/// alpha(d) = acos(cos d / (1 + cos d)), increasing in d (T3).
pub fn alpha(d: Iv) -> Iv {
    let f = |x: f64| {
        let c = Iv::pt(x).cos();
        c.div(c.add(Iv::pt(1.0))).acos()
    };
    Iv::new(f(d.lo).lo, f(d.hi).hi)
}

/// Base of the isosceles triangle with legs d and apex u: increasing in d in (0, pi/2) and in
/// u in [0, pi] (T1).
pub fn ebase(d: Iv, u: Iv) -> Iv {
    // at u = pi the base is 2 asin(sin d) = 2 d, since d < pi/2
    let hi = if u.hi >= PI_IV.lo { Iv::pt(d.hi).scale(2.0).hi } else { ebase_pt(d.hi, u.hi).hi };
    Iv::new(ebase_pt(d.lo, u.lo).lo, hi)
}

/// Base angle of the isosceles triangle with legs d and apex u: decreasing in u in (0, pi],
/// increasing in d in (0, pi/2) (T1: bangle = atan(cot(u/2) / cos d)).
pub fn bangle(d: Iv, u: Iv) -> Iv {
    // at u = pi the base angle is 0
    let lo = if u.hi >= PI_IV.lo { 0.0 } else { bangle_pt(d.lo, u.hi).lo };
    Iv::new(lo, bangle_pt(d.hi, u.lo).hi)
}

fn eta_nat(g: Iv, e: Iv, f: Iv) -> Iv {
    g.cos().sub(e.cos().mul(f.cos())).div(e.sin().mul(f.sin()))
}

/// eta(g; e, f) = (cos g - cos e cos f) / (sin e sin f) for sides in (0, pi): decreasing in g,
/// its derivative in e has the sign of cos f - cos e cos g and in f that of cos e - cos f cos g
/// (T2). Where both signs are fixed on the box, the range is read at two corners; otherwise the
/// natural interval extension is used.
pub fn eta(g: Iv, e: Iv, f: Iv) -> Iv {
    assert!(e.lo > 0.0 && f.lo > 0.0 && e.hi < PI_IV.lo && f.hi < PI_IV.lo);
    let se = f.cos().sub(e.cos().mul(g.cos()));
    let sf = e.cos().sub(f.cos().mul(g.cos()));
    let dir = |s: Iv| -> i32 {
        if s.lo > 0.0 {
            1
        } else if s.hi < 0.0 {
            -1
        } else {
            0
        }
    };
    let (de, df) = (dir(se), dir(sf));
    if de != 0 && df != 0 {
        let pick = |x: Iv, s: i32, want_hi: bool| -> f64 {
            // the end of x where eta is largest (want_hi) or smallest
            if (s > 0) == want_hi {
                x.hi
            } else {
                x.lo
            }
        };
        let lo = eta_nat(Iv::pt(g.hi), Iv::pt(pick(e, de, false)), Iv::pt(pick(f, df, false))).lo;
        let hi = eta_nat(Iv::pt(g.lo), Iv::pt(pick(e, de, true)), Iv::pt(pick(f, df, true))).hi;
        Iv::new(lo, hi)
    } else {
        eta_nat(g, e, f)
    }
}

/// The angle opposite the side g in a triangle with sides g, e, f: acos(eta), on the part of the
/// box where eta lies in [-1, 1]; None where no triangle exists (T2).
pub fn gam(g: Iv, e: Iv, f: Iv) -> Option<Iv> {
    let x = eta(g, e, f).meet(Iv::new(-1.0, 1.0))?;
    Some(x.acos())
}

/// (T7) L(d, u) = bangle(d, u) + acos(min(1, cot d tan(ebase(d, u) / 2))): non-increasing in u;
/// the returned value is a lower bound of L over d in the box and u <= uhi.
pub fn long_diag_lo(d: Iv, uhi: f64) -> f64 {
    let ul = uhi.min(PI_IV.lo);
    let u = Iv::new(ul, if uhi >= PI_IV.lo { PI_IV.hi } else { ul });
    let b = bangle(d, u);
    let e = ebase(d, u);
    let cot = Iv::new(
        Iv::pt(d.hi).cos().div(Iv::pt(d.hi).sin()).lo,
        Iv::pt(d.lo).cos().div(Iv::pt(d.lo).sin()).hi,
    );
    let t = cot.mul(e.scale(0.5).tan());
    let m = Iv::new(t.lo.min(1.0), t.hi.min(1.0));
    b.add(m.meet(Iv::new(-1.0, 1.0)).unwrap().acos()).lo
}

/// Rhombus: y = rho_d(x) = 2 bangle(d, x) (T4: cot(x/2) cot(y/2) = cos d).
pub fn rho(d: Iv, x: Iv) -> Iv {
    bangle(d, x).scale(2.0)
}

/// Closed interval [alpha(d), pi] of the corners, for the box of d.
pub fn corner_range(d: Iv) -> Iv {
    Iv::new(alpha(d).lo, PI_IV.hi)
}

/// Pentagon A0..A4 by the fan from A0 (T5), parameters d, u1, u4. Returns the enclosures of the
/// five corners [u0, u1, u2, u3, u4] intersected with [alpha(d), pi], or None if the box holds
/// no pentagon (a corner out of range or no middle triangle).
pub fn pentagon(d: Iv, u1: Iv, u4: Iv) -> Option<[Iv; 5]> {
    let cr = corner_range(d);
    let u1 = u1.meet(cr)?;
    let u4 = u4.meet(cr)?;
    let e = ebase(d, u1);
    let f = ebase(d, u4);
    let b1 = bangle(d, u1);
    let b4 = bangle(d, u4);
    let g0 = gam(d, e, f)?;
    let g2 = gam(f, e, d)?;
    let g3 = gam(e, f, d)?;
    let u0 = b1.add(g0).add(b4).meet(cr)?;
    let u2 = b1.add(g2).meet(cr)?;
    let u3 = b4.add(g3).meet(cr)?;
    Some([u0, u1, u2, u3, u4])
}

/// Hexagon A0..A5 (T6), parameters d, u1, u3, u5, with the long diagonal relations (T7) for the
/// six pairs of adjacent corners in both directions. Returns the six corners intersected with
/// [alpha(d), pi], or None if the box holds no hexagon.
pub fn hexagon(d: Iv, u1: Iv, u3: Iv, u5: Iv) -> Option<[Iv; 6]> {
    let cr = corner_range(d);
    let u1 = u1.meet(cr)?;
    let u3 = u3.meet(cr)?;
    let u5 = u5.meet(cr)?;
    let (e1, e3, e5) = (ebase(d, u1), ebase(d, u3), ebase(d, u5));
    let (b1, b3, b5) = (bangle(d, u1), bangle(d, u3), bangle(d, u5));
    let g0 = gam(e3, e1, e5)?;
    let g2 = gam(e5, e1, e3)?;
    let g4 = gam(e1, e3, e5)?;
    let u0 = b5.add(g0).add(b1).meet(cr)?;
    let u2 = b1.add(g2).add(b3).meet(cr)?;
    let u4 = b3.add(g4).add(b5).meet(cr)?;
    let u = [u0, u1, u2, u3, u4, u5];
    for i in 0..6 {
        let j = (i + 1) % 6;
        if long_diag_lo(d, u[i].hi) > u[j].hi || long_diag_lo(d, u[j].hi) > u[i].hi {
            return None;
        }
    }
    Some(u)
}

/// Lower bound of the area (angle excess) from enclosures of the corners.
pub fn area_lo(u: &[Iv]) -> f64 {
    let k = u.len() as f64;
    let mut s = Iv::pt(0.0);
    for x in u {
        s = s.add(*x);
    }
    s.sub(PI_IV.scale(k - 2.0)).lo
}
pub fn area_hi(u: &[Iv]) -> f64 {
    let k = u.len() as f64;
    let mut s = Iv::pt(0.0);
    for x in u {
        s = s.add(*x);
    }
    s.sub(PI_IV.scale(k - 2.0)).hi
}
