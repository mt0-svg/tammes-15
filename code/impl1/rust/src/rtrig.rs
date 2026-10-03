//! Rigorous enclosures of cos, sin, tan, atan, asin, acos at f64 points, from IEEE 754 basic
//! operations only (+, -, *, /, sqrt, each correctly rounded to nearest and then moved one ulp
//! outward by `Iv`), with Taylor series and explicit remainder bounds. No libm function is called.
//! Constants: code/gp/rtrig_consts.gp (PARI/GP, 200 digits), output
//! code/gp/rtrig_consts.out.
//!
//! Derivations.
//! - Reduction for cos, sin, tan: k = nearest integer to x 2/pi (any integer is correct; this one
//!   gives |r| <= pi/4 + tiny), r = x - k pi/2 with pi/2 = P1 + P2 + P3, P1 and P2 dyadic with at
//!   most 32 significant bits, so k P1 and k P2 are exact doubles for |k| < 2^21 and only the
//!   subtractions and k P3 (an interval) are rounded. Then cos x = cos r, -sin r, -cos r, sin r for
//!   k = 0, 1, 2, 3 mod 4. If |r| > 0.8 on the enclosure (never for |k| < 2^21 in practice) the
//!   trivial enclosure is returned.
//! - Kernels on |r| <= 0.8, N = 10: cos r = sum_{j <= N} (-1)^j r^{2j}/(2j)! + R, |R| <=
//!   |r|^{2N+2}/(2N+2)! <= 0.8^22/22! < 6.6e-24 (Lagrange, |cos^{(m)}| <= 1); sin r = sum_{j <= N}
//!   (-1)^j r^{2j+1}/(2j+1)! + R, |R| <= |r|^{2N+3}/(2N+3)! < 2.3e-25 |r|/0.8 (Lagrange; the
//!   bound is taken as |r|^{23}/23! computed from |r|). Coefficients are interval quotients.
//! - atan: odd, atan x = pi/2 - atan(1/x) for x > 1, and for t in [0, 1] with c = j/8 the nearest
//!   eighth, atan t = atan c + atan u, u = (t - c)/(1 + t c) (valid since t c > -1), |u| <= 1/16
//!   up to rounding; atan u = sum_{i <= 6} (-1)^i u^{2i+1}/(2i+1) + R with |R| <= |u|^15/15
//!   (alternating series with terms decreasing to 0 for |u| <= 1). A_j = atan(j/8) enclosures from
//!   PARI. If the enclosure of |u| exceeds 0.07 the kernel falls back to [0, pi/4] bounds.
//! - acos x = 2 atan(sqrt((1 - x)/(1 + x))) for x in (-1, 1] (x = cos theta, theta in [0, pi):
//!   the root is tan(theta/2) >= 0), acos(-1) = pi.
//! - asin x = 2 atan(x / (1 + sqrt((1 - x)(1 + x)))) for x in [-1, 1] (x = sin theta, theta in
//!   [-pi/2, pi/2]: the quotient is tan(theta/2)).
//! - tan x = sin x / cos x from the same reduced r (interval division; the whole line when the
//!   cosine enclosure contains 0).
//! atan of an interval is taken endpoint-wise (atan is increasing).

use crate::ivt::Iv;
use std::sync::OnceLock;

const P1: f64 = f64::from_bits(0x3ff921fb54400000);
const P2: f64 = f64::from_bits(0x3dd0b4611a000000);
const P3_LO: f64 = f64::from_bits(0x3bf898cc51701b83);
const P3_HI: f64 = f64::from_bits(0x3bf898cc51701b84);
/// Tight enclosure of pi (PARI).
pub const PI_T_LO: f64 = f64::from_bits(0x400921fb54442d18);
pub const PI_T_HI: f64 = f64::from_bits(0x400921fb54442d19);
const A_LO: [u64; 9] = [
    0,
    0x3fbfd5ba9aac2f6d,
    0x3fcf5b75f92c80dd,
    0x3fd6f61941e4def0,
    0x3fddac670561bb4f,
    0x3fe1e00babdefeb3,
    0x3fe4978fa3269ee1,
    0x3fe700a7c5784633,
    0x3fe921fb54442d18,
];
const A_HI: [u64; 9] = [
    0,
    0x3fbfd5ba9aac2f6e,
    0x3fcf5b75f92c80de,
    0x3fd6f61941e4def1,
    0x3fddac670561bb50,
    0x3fe1e00babdefeb4,
    0x3fe4978fa3269ee2,
    0x3fe700a7c5784634,
    0x3fe921fb54442d19,
];

const NC: usize = 10;
const NA: usize = 6;

struct Coef {
    /// (-1)^j / (2j)!
    c: [Iv; NC + 1],
    /// (-1)^j / (2j+1)!
    s: [Iv; NC + 1],
    /// (-1)^i / (2i+1)
    a: [Iv; NA + 1],
    /// 1/22!, 1/23!
    rc: Iv,
    rs: Iv,
}

fn coef() -> &'static Coef {
    static C: OnceLock<Coef> = OnceLock::new();
    C.get_or_init(|| {
        let one = Iv::pt(1.0);
        let mut c = [one; NC + 1];
        let mut s = [one; NC + 1];
        // f = 1/m! as an interval, built by exact integer divisors
        let mut f = one;
        for m in 1..=2 * NC + 3 {
            f = f.div(Iv::pt(m as f64));
            if m % 2 == 0 && m / 2 <= NC {
                c[m / 2] = if (m / 2) % 2 == 0 { f } else { f.neg() };
            }
            if m % 2 == 1 && (m - 1) / 2 <= NC {
                let j = (m - 1) / 2;
                s[j] = if j % 2 == 0 { f } else { f.neg() };
            }
        }
        let mut f22 = one;
        for m in 1..=2 * NC + 2 {
            f22 = f22.div(Iv::pt(m as f64));
        }
        let f23 = f22.div(Iv::pt((2 * NC + 3) as f64));
        let mut a = [one; NA + 1];
        for i in 0..=NA {
            let q = one.div(Iv::pt((2 * i + 1) as f64));
            a[i] = if i % 2 == 0 { q } else { q.neg() };
        }
        Coef { c, s, a, rc: f22, rs: f23 }
    })
}

#[inline]
fn absmax(x: Iv) -> f64 {
    x.lo.abs().max(x.hi.abs())
}

/// cos r and sin r for an enclosure r with |r| <= 0.8.
fn kern(r: Iv) -> (Iv, Iv) {
    let k = coef();
    let s = r.sqr();
    let m = absmax(r);
    // remainder bounds |r|^22/22!, |r|^23/23! (upper bounds by outward rounding)
    let m2 = Iv::pt(m).sqr();
    let m4 = m2.sqr();
    let m8 = m4.sqr();
    let m16 = m8.sqr();
    let m22 = m16.mul(m4).mul(m2);
    let bc = m22.mul(k.rc).hi;
    let bs = m22.mul(Iv::pt(m)).mul(k.rs).hi;
    let mut pc = k.c[NC];
    let mut ps = k.s[NC];
    for j in (0..NC).rev() {
        pc = pc.mul(s).add(k.c[j]);
        ps = ps.mul(s).add(k.s[j]);
    }
    let cr = pc.add(Iv::new(-bc, bc));
    let sr = ps.mul(r).add(Iv::new(-bs, bs));
    (cr, sr)
}

/// (cos x, sin x) enclosures, or None when the reduction is out of range.
fn cos_sin(x: f64) -> Option<(Iv, Iv)> {
    if !x.is_finite() {
        return None;
    }
    let kf = (x * std::f64::consts::FRAC_2_PI).round();
    if !(kf.abs() < 1048576.0) {
        return None;
    }
    // k P1 and k P2 are exact (<= 32 + 21 significant bits)
    let r = Iv::pt(x)
        .sub(Iv::pt(kf * P1))
        .sub(Iv::pt(kf * P2))
        .sub(Iv::pt(kf).mul(Iv::new(P3_LO, P3_HI)));
    if absmax(r) > 0.8 {
        return None;
    }
    let (c, s) = kern(r);
    let q = (kf as i64).rem_euclid(4);
    let (cx, sx) = match q {
        0 => (c, s),
        1 => (s.neg(), c),
        2 => (c.neg(), s.neg()),
        _ => (s, c.neg()),
    };
    let cl = |v: Iv| Iv::new(v.lo.max(-1.0), v.hi.min(1.0));
    Some((cl(cx), cl(sx)))
}

/// Enclosure of cos x.
pub fn cos_enc(x: f64) -> Iv {
    if x.is_nan() {
        return Iv::new(f64::NAN, f64::NAN);
    }
    cos_sin(x).map_or(Iv::new(-1.0, 1.0), |v| v.0)
}

/// Enclosure of sin x.
pub fn sin_enc(x: f64) -> Iv {
    if x.is_nan() {
        return Iv::new(f64::NAN, f64::NAN);
    }
    cos_sin(x).map_or(Iv::new(-1.0, 1.0), |v| v.1)
}

/// Enclosure of tan x (the whole line when the cosine enclosure contains 0 or x is far out).
pub fn tan_enc(x: f64) -> Iv {
    if x.is_nan() {
        return Iv::new(f64::NAN, f64::NAN);
    }
    match cos_sin(x) {
        Some((c, s)) => s.div(c),
        None => Iv::new(f64::NEG_INFINITY, f64::INFINITY),
    }
}

/// atan u for an enclosure u with |u| <= 0.07.
fn atan_small(u: Iv) -> Iv {
    let k = coef();
    let s = u.sqr();
    let m = absmax(u);
    // |u|^15/15
    let m2 = Iv::pt(m).sqr();
    let m4 = m2.sqr();
    let m8 = m4.sqr();
    let m15 = m8.mul(m4).mul(m2).mul(Iv::pt(m));
    let b = m15.div(Iv::pt(15.0)).hi;
    let mut p = k.a[NA];
    for i in (0..NA).rev() {
        p = p.mul(s).add(k.a[i]);
    }
    p.mul(u).add(Iv::new(-b, b))
}

/// atan t for a point t in [0, 1].
fn atan01(t: f64) -> Iv {
    let j = (t * 8.0).round() as usize;
    let j = j.min(8);
    if j == 0 {
        return atan_small(Iv::pt(t));
    }
    let c = j as f64 / 8.0; // exact
    let u = Iv::pt(t).sub(Iv::pt(c)).div(Iv::pt(1.0).add(Iv::pt(t).mul(Iv::pt(c))));
    let aj = Iv::new(f64::from_bits(A_LO[j]), f64::from_bits(A_HI[j]));
    if absmax(u) > 0.07 {
        // not reached for t in [0, 1]; safe fallback
        return Iv::new(0.0, f64::from_bits(A_HI[8]));
    }
    aj.add(atan_small(u))
}

/// Enclosure of atan x at a point (x = +-inf gives +-pi/2).
pub fn atan_enc(x: f64) -> Iv {
    if x.is_nan() {
        return Iv::new(f64::NAN, f64::NAN);
    }
    if x < 0.0 {
        return atan_enc(-x).neg();
    }
    let half_pi = Iv::new(PI_T_LO * 0.5, PI_T_HI * 0.5);
    if x == f64::INFINITY {
        return half_pi;
    }
    if x <= 1.0 {
        return atan01(x);
    }
    // x > 1: atan x = pi/2 - atan(1/x), 1/x in (0, 1)
    let y = Iv::pt(1.0).div(Iv::pt(x));
    let lo = y.lo.max(0.0);
    let hi = y.hi.min(1.0);
    let ay = Iv::new(atan01(lo).lo, atan01(hi).hi);
    half_pi.sub(ay)
}

/// atan of an interval (increasing).
pub fn atan_iv(y: Iv) -> Iv {
    Iv::new(atan_enc(y.lo).lo, atan_enc(y.hi).hi)
}

/// Enclosure of acos x at a point x in [-1, 1] (NaN outside).
pub fn acos_enc(x: f64) -> Iv {
    if !(x >= -1.0 && x <= 1.0) {
        return Iv::new(f64::NAN, f64::NAN);
    }
    if x == -1.0 {
        return Iv::new(PI_T_LO, PI_T_HI);
    }
    let one = Iv::pt(1.0);
    let q = one.sub(Iv::pt(x)).div(one.add(Iv::pt(x)));
    let q = Iv::new(q.lo.max(0.0), q.hi);
    let r = q.sqrt();
    let a = atan_iv(r).scale(2.0);
    Iv::new(a.lo.max(0.0), a.hi.min(PI_T_HI))
}

/// Enclosure of asin x at a point x in [-1, 1] (NaN outside).
pub fn asin_enc(x: f64) -> Iv {
    if !(x >= -1.0 && x <= 1.0) {
        return Iv::new(f64::NAN, f64::NAN);
    }
    let one = Iv::pt(1.0);
    let w = one.sub(Iv::pt(x)).mul(one.add(Iv::pt(x)));
    let w = Iv::new(w.lo.max(0.0), w.hi);
    let q = Iv::pt(x).div(one.add(w.sqrt()));
    let a = atan_iv(q).scale(2.0);
    Iv::new(a.lo.max(-PI_T_HI * 0.5), a.hi.min(PI_T_HI * 0.5))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn against_libm_loose() {
        // loose sanity check against libm
        let mut x = -7.0f64;
        while x < 7.0 {
            for (e, v) in [(cos_enc(x), x.cos()), (sin_enc(x), x.sin()), (atan_enc(x), x.atan())] {
                assert!(e.lo <= v + 1e-15 && v - 1e-15 <= e.hi && e.hi - e.lo < 1e-14, "{x} {e:?} {v}");
            }
            if x.abs() < 1.5 {
                let e = tan_enc(x);
                let v = x.tan();
                assert!(e.lo <= v + 1e-13 * v.abs().max(1.0) && v - 1e-13 * v.abs().max(1.0) <= e.hi, "{x} {e:?} {v}");
            }
            if x.abs() <= 1.0 {
                for (e, v) in [(acos_enc(x), x.acos()), (asin_enc(x), x.asin())] {
                    assert!(e.lo <= v + 1e-15 && v - 1e-15 <= e.hi && e.hi - e.lo < 1e-14, "{x} {e:?} {v}");
                }
            }
            x += 0.001237;
        }
        for x in [-1.0, 1.0, 0.0, -0.0, 1e-300, 0.5, -0.5] {
            let e = acos_enc(x);
            assert!(e.lo <= x.acos() && x.acos() <= e.hi + 1e-15);
            let e = asin_enc(x);
            assert!(e.lo <= x.asin() + 1e-15 && x.asin() <= e.hi + 1e-15);
        }
    }
}
