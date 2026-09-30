//! Fast rigorous elementary functions (own implementation; MPFR is used only to build the tables
//! and in the tests).
//!
//! Rigor argument (details in Section 6.5 of the paper):
//! - every operation is an outward-rounded interval operation of iv.rs;
//! - table entries cos(k/64), sin(k/64) (0 <= k <= KMAX) and atan(k/64) (0 <= k <= 64) are
//!   enclosed by MPFR with directed rounding (correctly rounded, so the enclosures are rigorous);
//! - sin/cos at a double x: k = round(64 x), t = x - k/64 (enclosed as an interval, |t| <= 1/128
//!   up to one ulp), cos x = cos(k/64) cos t - sin(k/64) sin t, sin x = sin(k/64) cos t + cos(k/64) sin t;
//!   sin t, cos t by their Taylor polynomials of degree 7 and 8 plus the Lagrange remainder
//!   |t|^9/9! and |t|^10/10! (all derivatives of sin, cos are bounded by 1);
//! - atan at y in [0, 1]: c = k/64 nearest to y, atan y = atan c + atan z, z = (y - c)/(1 + y c),
//!   |z| <= 1/128 (up to rounding); atan z by its Taylor polynomial of degree 7 plus the bound
//!   |z|^9/9 of the alternating series (terms decreasing for |z| < 1); for y > 1,
//!   atan y = pi/2 - atan(1/y); atan is odd;
//! - acos x = 2 atan(sqrt((1 - x)/(1 + x))) on (-1, 1] (tan(theta/2) = sqrt((1 - cos)/(1 + cos))
//!   for theta in [0, pi)), acos(-1) = pi; asin x = atan(x / sqrt((1 - x)(1 + x))) on (-1, 1),
//!   asin(+-1) = +-pi/2;
//! - interval extensions: acos decreasing, asin and atan increasing (endpoint values); cos, sin
//!   through their extrema as in mp.rs (an extremum is included unless the pi enclosure excludes it).

use crate::iv::{dn, up, I, PI_HI, PI_LO};
use crate::mp;
use std::sync::OnceLock;

const KMAX: usize = 1024; // table covers |x| <= 16

struct Tab {
    cs: Vec<(I, I)>,
    at: Vec<I>,
    // Taylor coefficients as enclosures
    s3: I,
    s5: I,
    s7: I,
    c2: I,
    c4: I,
    c6: I,
    c8: I,
    f9: I,
    f10: I,
    a3: I,
    a5: I,
    a7: I,
    a9: I,
    half_pi: I,
}

static TAB: OnceLock<Tab> = OnceLock::new();

fn inv(n: f64) -> I {
    I::pt(1.0) / I::pt(n)
}

fn build() -> Tab {
    let mut cs = Vec::with_capacity(KMAX + 1);
    for k in 0..=KMAX {
        let x = k as f64 / 64.0; // exact
        cs.push((mp::cos_pt(x), mp::sin_pt(x)));
    }
    let mut at = Vec::with_capacity(65);
    for k in 0..=64 {
        let x = k as f64 / 64.0;
        at.push(mp::atan(I::pt(x)));
    }
    Tab {
        cs,
        at,
        s3: inv(6.0),
        s5: inv(120.0),
        s7: inv(5040.0),
        c2: inv(2.0),
        c4: inv(24.0),
        c6: inv(720.0),
        c8: inv(40320.0),
        f9: inv(362880.0),
        f10: inv(3628800.0),
        a3: inv(3.0),
        a5: inv(5.0),
        a7: inv(7.0),
        a9: inv(9.0),
        half_pi: I::half_pi(),
    }
}

#[inline(always)]
fn tab() -> &'static Tab {
    TAB.get_or_init(build)
}

/// Enclosures of (sin x, cos x) at a double x.
#[inline]
pub fn sincos_pt(x: f64) -> (I, I) {
    if !x.is_finite() {
        return (I::new(-1.0, 1.0), I::new(-1.0, 1.0));
    }
    let ax = x.abs();
    if ax > (KMAX as f64 - 1.0) / 64.0 {
        return (mp::sin_pt(x), mp::cos_pt(x));
    }
    let tb = tab();
    let kf = (ax * 64.0).round();
    let k = kf as usize;
    let t = I::pt(ax) - I::pt(kf / 64.0);
    let m = t.mag();
    let t2 = t.sqr();
    let m2 = up(m * m);
    let m4 = up(m2 * m2);
    let m8 = up(m4 * m4);
    // sin t = t (1 - t^2/6 + t^4/120 - t^6/5040) + R, |R| <= |t|^9/9!
    let ps = I::pt(1.0) - t2 * (tb.s3 - t2 * (tb.s5 - t2 * tb.s7));
    let r9 = (I::pt(m8) * I::pt(m) * tb.f9).hi;
    let st = t * ps + I::new(-r9, r9);
    // cos t = 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 + R, |R| <= |t|^10/10!
    let pc = I::pt(1.0) - t2 * (tb.c2 - t2 * (tb.c4 - t2 * (tb.c6 - t2 * tb.c8)));
    let r10 = (I::pt(m8) * I::pt(m2) * tb.f10).hi;
    let ct = pc + I::new(-r10, r10);
    let (ck, sk) = tb.cs[k];
    let c = ck * ct - sk * st;
    let s = sk * ct + ck * st;
    let c = I::new(c.lo.max(-1.0), c.hi.min(1.0));
    let s = I::new(s.lo.max(-1.0), s.hi.min(1.0));
    if x < 0.0 {
        (-s, c)
    } else {
        (s, c)
    }
}

/// Extremum test: may k pi + (half ? pi/2 : 0) lie in [a, b]?
#[inline]
fn may_contain(a: f64, b: f64, k: i64, half: bool) -> bool {
    let kk = k as f64 + if half { 0.5 } else { 0.0 };
    let p1 = kk * PI_LO;
    let p2 = kk * PI_HI;
    let lo = dn(p1.min(p2));
    let hi = up(p1.max(p2));
    !(hi < a || lo > b)
}

/// Enclosures of (sin x, cos x) over an interval x.
#[inline]
pub fn sincos(x: I) -> (I, I) {
    let full = I::new(-1.0, 1.0);
    if x.is_bad() || !x.lo.is_finite() || !x.hi.is_finite() || x.hi - x.lo >= 6.0 {
        return (full, full);
    }
    if x.lo == x.hi {
        return sincos_pt(x.lo);
    }
    let (sa, ca) = sincos_pt(x.lo);
    let (sb, cb) = sincos_pt(x.hi);
    let mut s = sa.hull(sb);
    let mut c = ca.hull(cb);
    let qa = if x.lo >= 0.0 { x.lo / PI_HI } else { x.lo / PI_LO };
    let qb = if x.hi >= 0.0 { x.hi / PI_LO } else { x.hi / PI_HI };
    let k0 = qa.floor() as i64 - 1;
    let k1 = qb.ceil() as i64 + 1;
    for k in k0..=k1 {
        let even = k.rem_euclid(2) == 0;
        if may_contain(x.lo, x.hi, k, false) {
            if even {
                c.hi = 1.0
            } else {
                c.lo = -1.0
            }
        }
        if may_contain(x.lo, x.hi, k, true) {
            if even {
                s.hi = 1.0
            } else {
                s.lo = -1.0
            }
        }
    }
    (s, c)
}

#[inline]
pub fn sin(x: I) -> I {
    sincos(x).0
}
#[inline]
pub fn cos(x: I) -> I {
    sincos(x).1
}

/// atan at a double y in [0, 1].
#[inline]
fn atan01(y: f64) -> I {
    let tb = tab();
    let kf = (y * 64.0).round();
    let k = kf as usize;
    let c = kf / 64.0;
    let z = (I::pt(y) - I::pt(c)) / (I::pt(1.0) + I::pt(y) * I::pt(c));
    let m = z.mag();
    let z2 = z.sqr();
    let p = I::pt(1.0) - z2 * (tb.a3 - z2 * (tb.a5 - z2 * tb.a7));
    let m2 = up(m * m);
    let m4 = up(m2 * m2);
    let m8 = up(m4 * m4);
    let r = (I::pt(m8) * I::pt(m) * tb.a9).hi;
    tb.at[k] + z * p + I::new(-r, r)
}

/// atan at a double y.
#[inline]
pub fn atan_pt(y: f64) -> I {
    if y.is_nan() {
        return I::new(-PI_HI * 0.5, PI_HI * 0.5);
    }
    let ay = y.abs();
    let r = if ay <= 1.0 {
        atan01(ay)
    } else if ay == f64::INFINITY {
        tab().half_pi
    } else {
        // atan(y) = pi/2 - atan(1/y), 1/y in (0, 1)
        let w = I::pt(1.0) / I::pt(ay);
        let w = I::new(w.lo.max(0.0), w.hi.min(1.0));
        let aw = I::new(atan01(w.lo).lo, atan01(w.hi).hi);
        tab().half_pi - aw
    };
    if y < 0.0 {
        -r
    } else {
        r
    }
}

#[inline]
pub fn atan(x: I) -> I {
    if x.is_bad() {
        return I::new(-PI_HI * 0.5, PI_HI * 0.5);
    }
    if x.lo == x.hi {
        return atan_pt(x.lo);
    }
    // narrow interval inside [0, 1] with a common table point: one Taylor evaluation over the
    // whole interval (the polynomial enclosure and the remainder bound hold for every z in it)
    if x.lo >= 0.0 && x.hi <= 1.0 {
        let k0 = (x.lo * 64.0).round();
        if k0 == (x.hi * 64.0).round() {
            return atan01_iv(x, k0);
        }
    } else if x.lo > 1.0 && x.hi.is_finite() {
        // atan y = pi/2 - atan(1/y), 1/y in (0, 1)
        let w = I::pt(1.0) / x;
        let w = I::new(w.lo.max(0.0), w.hi.min(1.0));
        return tab().half_pi - atan(w);
    } else if x.hi < 0.0 {
        return -atan(-x);
    }
    I::new(atan_pt(x.lo).lo, atan_pt(x.hi).hi)
}

/// atan over an interval y in [0, 1] whose ends round to the same table point k0/64.
#[inline]
fn atan01_iv(y: I, k0: f64) -> I {
    let tb = tab();
    let c = k0 / 64.0;
    let z = (y - I::pt(c)) / (I::pt(1.0) + y * I::pt(c));
    let m = z.mag();
    if !(m <= 0.5) {
        return I::new(atan01(y.lo).lo, atan01(y.hi).hi);
    }
    let z2 = z.sqr();
    let p = I::pt(1.0) - z2 * (tb.a3 - z2 * (tb.a5 - z2 * tb.a7));
    let m2 = up(m * m);
    let m4 = up(m2 * m2);
    let m8 = up(m4 * m4);
    let r = (I::pt(m8) * I::pt(m) * tb.a9).hi;
    tb.at[k0 as usize] + z * p + I::new(-r, r)
}

/// acos at a double x in [-1, 1].
#[inline]
fn acos_pt(x: f64) -> I {
    if x >= 1.0 {
        return I::pt(0.0);
    }
    if x <= -1.0 {
        return I::PI;
    }
    let q = (I::pt(1.0) - I::pt(x)) / (I::pt(1.0) + I::pt(x));
    let s = q.sqrt().unwrap();
    let a = atan(s);
    let r = a * 2.0;
    I::new(r.lo.max(0.0), r.hi.min(PI_HI))
}

/// asin at a double x in [-1, 1].
#[inline]
fn asin_pt(x: f64) -> I {
    let hp = tab().half_pi;
    if x >= 1.0 {
        return hp;
    }
    if x <= -1.0 {
        return -hp;
    }
    let den = ((I::pt(1.0) - I::pt(x)) * (I::pt(1.0) + I::pt(x))).sqrt().unwrap();
    let a = atan(I::pt(x) / den);
    I::new(a.lo.max(-hp.hi), a.hi.min(hp.hi))
}

/// acos over x meet [-1, 1]; None if x misses [-1, 1].
#[inline]
pub fn acos(x: I) -> Option<I> {
    let c = x.clamp_to(-1.0, 1.0)?;
    if c.lo == c.hi {
        return Some(acos_pt(c.lo));
    }
    Some(I::new(acos_pt(c.hi).lo, acos_pt(c.lo).hi))
}

/// asin over x meet [-1, 1]; None if x misses [-1, 1].
#[inline]
pub fn asin(x: I) -> Option<I> {
    let c = x.clamp_to(-1.0, 1.0)?;
    if c.lo == c.hi {
        return Some(asin_pt(c.lo));
    }
    Some(I::new(asin_pt(c.lo).lo, asin_pt(c.hi).hi))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn against_mpfr() {
        let mut seed = 12345u64;
        let mut rnd = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed >> 11) as f64 / (1u64 << 53) as f64
        };
        let mut maxw = 0.0f64;
        for _ in 0..200000 {
            let x = (rnd() - 0.5) * 20.0;
            let (s, c) = sincos_pt(x);
            let ms = mp::sin_pt(x);
            let mc = mp::cos_pt(x);
            assert!(s.lo <= ms.lo && ms.hi <= s.hi, "sin {x} {s:?} {ms:?}");
            assert!(c.lo <= mc.lo && mc.hi <= c.hi, "cos {x} {c:?} {mc:?}");
            maxw = maxw.max(s.width()).max(c.width());
            let y = (rnd() - 0.5) * 2.0;
            let a = acos(I::pt(y)).unwrap();
            let ma = mp::acos(I::pt(y)).unwrap();
            assert!(a.lo <= ma.lo && ma.hi <= a.hi, "acos {y} {a:?} {ma:?}");
            let a = asin(I::pt(y)).unwrap();
            let ma = mp::asin(I::pt(y)).unwrap();
            assert!(a.lo <= ma.lo && ma.hi <= a.hi, "asin {y} {a:?} {ma:?}");
            let z = (rnd() - 0.5) * 100.0;
            let a = atan(I::pt(z));
            let ma = mp::atan(I::pt(z));
            assert!(a.lo <= ma.lo && ma.hi <= a.hi, "atan {z} {a:?} {ma:?}");
        }
        assert!(maxw < 1e-14, "{maxw}");
    }
}

#[cfg(test)]
mod interval_tests {
    use super::*;
    #[test]
    fn intervals_against_mpfr() {
        let mut seed = 99u64;
        let mut rnd = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed >> 11) as f64 / (1u64 << 53) as f64
        };
        let widths = [0.0, 1e-15, 1e-12, 1e-9, 1e-6, 1e-3, 0.1, 1.0];
        for it in 0..200000 {
            let w = widths[it % widths.len()] * rnd();
            // sin, cos on [x, x + w], sampled at 5 points
            let x = (rnd() - 0.5) * 16.0;
            let iv = I::new(x, x + w);
            let (s, c) = sincos(iv);
            for t in 0..5 {
                let p = x + w * t as f64 / 4.0;
                let p = p.min(iv.hi);
                let ms = mp::sin_pt(p);
                let mc = mp::cos_pt(p);
                assert!(s.lo <= ms.lo && ms.hi <= s.hi, "sin {iv:?} at {p}: {s:?} {ms:?}");
                assert!(c.lo <= mc.lo && mc.hi <= c.hi, "cos {iv:?} at {p}: {c:?} {mc:?}");
            }
            // atan on [y, y + w] (monotone: endpoints)
            let y = (rnd() - 0.5) * 8.0;
            let iv = I::new(y, y + w);
            let a = atan(iv);
            for &p in &[iv.lo, iv.hi] {
                let ma = mp::atan(I::pt(p));
                assert!(a.lo <= ma.lo && ma.hi <= a.hi, "atan {iv:?} at {p}: {a:?} {ma:?}");
            }
            // acos, asin on [z, z + w] inside [-1, 1]
            let z = (rnd() * 2.0 - 1.0).min(1.0 - w);
            let iv = I::new(z, (z + w).min(1.0));
            let a = acos(iv).unwrap();
            let b = asin(iv).unwrap();
            for &p in &[iv.lo, iv.hi] {
                let ma = mp::acos(I::pt(p)).unwrap();
                let mb = mp::asin(I::pt(p)).unwrap();
                assert!(a.lo <= ma.lo && ma.hi <= a.hi, "acos {iv:?} at {p}: {a:?} {ma:?}");
                assert!(b.lo <= mb.lo && mb.hi <= b.hi, "asin {iv:?} at {p}: {b:?} {mb:?}");
            }
        }
    }
}
