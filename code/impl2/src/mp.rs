//! Rigorous elementary functions through MPFR (libmpfr.so.6, called directly by FFI).
//!
//! Rigor: MPFR returns the correctly rounded value of cos, sin, tan, acos, asin, atan in the
//! requested direction at the requested precision (MPFR documentation, section "Nomenclature and
//! types": every function is correctly rounded). We work at precision 53 with the default (huge)
//! exponent range, so the MPFR result rounded toward -inf (RNDD) is a double not above the exact
//! value, and mpfr_get_d with the same direction keeps it below (it is exact when the value is a
//! normal double; for subnormal magnitudes the second rounding goes the same way). Symmetrically
//! for RNDU. The input double is copied exactly (set_d at precision 53 is exact).
//!
//! Interval extensions: acos is decreasing, asin and atan increasing, so their ranges over a
//! closed interval are given by the endpoint values. cos and sin are handled by their extrema:
//! on [a, b] with b - a < 2 pi, the range is the hull of the endpoint values and of the extreme
//! values (+1 or -1) at every point k pi (cos) or pi/2 + k pi (sin) that may lie in [a, b]; the
//! test "may lie" uses the enclosure [PI_LO, PI_HI] of pi, so an extremum is included whenever
//! it cannot be excluded.

use crate::iv::{dn, up, I, PI_HI, PI_LO};
use std::cell::RefCell;
use std::os::raw::{c_int, c_long};

#[repr(C)]
struct Mpfr {
    prec: c_long,
    sign: c_int,
    exp: c_long,
    d: *mut u64,
}

const RNDN: c_int = 0;
const RNDU: c_int = 2;
const RNDD: c_int = 3;

extern "C" {
    fn mpfr_init2(x: *mut Mpfr, prec: c_long);
    fn mpfr_set_d(x: *mut Mpfr, d: f64, rnd: c_int) -> c_int;
    fn mpfr_get_d(x: *const Mpfr, rnd: c_int) -> f64;
    fn mpfr_cos(r: *mut Mpfr, x: *const Mpfr, rnd: c_int) -> c_int;
    fn mpfr_sin(r: *mut Mpfr, x: *const Mpfr, rnd: c_int) -> c_int;
    fn mpfr_tan(r: *mut Mpfr, x: *const Mpfr, rnd: c_int) -> c_int;
    fn mpfr_acos(r: *mut Mpfr, x: *const Mpfr, rnd: c_int) -> c_int;
    fn mpfr_asin(r: *mut Mpfr, x: *const Mpfr, rnd: c_int) -> c_int;
    fn mpfr_atan(r: *mut Mpfr, x: *const Mpfr, rnd: c_int) -> c_int;
    fn mpfr_const_pi(r: *mut Mpfr, rnd: c_int) -> c_int;
    fn mpfr_set_str(r: *mut Mpfr, s: *const u8, base: c_int, rnd: c_int) -> c_int;
}

struct Pair {
    x: Mpfr,
    r: Mpfr,
}

thread_local! {
    static MP: RefCell<Pair> = RefCell::new(unsafe {
        let mut p = Pair {
            x: Mpfr { prec: 0, sign: 0, exp: 0, d: std::ptr::null_mut() },
            r: Mpfr { prec: 0, sign: 0, exp: 0, d: std::ptr::null_mut() },
        };
        mpfr_init2(&mut p.x, 53);
        mpfr_init2(&mut p.r, 53);
        p
    });
}

type F = unsafe extern "C" fn(*mut Mpfr, *const Mpfr, c_int) -> c_int;

#[inline]
fn call(f: F, x: f64, rnd: c_int) -> f64 {
    MP.with(|m| {
        let mut m = m.borrow_mut();
        let p = &mut *m;
        unsafe {
            mpfr_set_d(&mut p.x, x, RNDN);
            f(&mut p.r, &p.x, rnd);
            mpfr_get_d(&p.r, rnd)
        }
    })
}

#[inline]
fn both(f: F, x: f64) -> I {
    I::new(call(f, x, RNDD), call(f, x, RNDU))
}

pub fn cos_pt(x: f64) -> I {
    both(mpfr_cos, x)
}
pub fn sin_pt(x: f64) -> I {
    both(mpfr_sin, x)
}

/// Enclosure of the set {k : k pi in [a, b]} is contained in the returned range of k
/// (extremum candidates are then tested with the pi enclosure).
fn k_range(a: f64, b: f64) -> (i64, i64) {
    // a / pi >= a / PI_HI for a >= 0 and >= a / PI_LO for a < 0; widen by one to be safe.
    let qa = if a >= 0.0 { a / PI_HI } else { a / PI_LO };
    let qb = if b >= 0.0 { b / PI_LO } else { b / PI_HI };
    ((qa.floor() as i64) - 1, (qb.ceil() as i64) + 1)
}

/// May the point k pi + off (off = 0 or pi/2) lie in [a, b]?
fn may_contain(a: f64, b: f64, k: i64, half: bool) -> bool {
    let kk = k as f64 + if half { 0.5 } else { 0.0 };
    // enclosure of kk * pi (kk is exactly representable, |kk| < 2^52)
    let p1 = kk * PI_LO;
    let p2 = kk * PI_HI;
    let lo = dn(p1.min(p2));
    let hi = up(p1.max(p2));
    !(hi < a || lo > b)
}

pub fn cos(x: I) -> I {
    if x.is_bad() || !x.lo.is_finite() || !x.hi.is_finite() || x.hi - x.lo >= 6.0 {
        return I::new(-1.0, 1.0);
    }
    let ca = cos_pt(x.lo);
    let cb = cos_pt(x.hi);
    let mut r = ca.hull(cb);
    let (k0, k1) = k_range(x.lo, x.hi);
    for k in k0..=k1 {
        if may_contain(x.lo, x.hi, k, false) {
            if k.rem_euclid(2) == 0 {
                r.hi = 1.0;
            } else {
                r.lo = -1.0;
            }
        }
    }
    I::new(r.lo.max(-1.0), r.hi.min(1.0))
}

pub fn sin(x: I) -> I {
    if x.is_bad() || !x.lo.is_finite() || !x.hi.is_finite() || x.hi - x.lo >= 6.0 {
        return I::new(-1.0, 1.0);
    }
    let sa = sin_pt(x.lo);
    let sb = sin_pt(x.hi);
    let mut r = sa.hull(sb);
    let (k0, k1) = k_range(x.lo, x.hi);
    for k in k0..=k1 {
        if may_contain(x.lo, x.hi, k, true) {
            // sin(pi/2 + k pi) = (-1)^k
            if k.rem_euclid(2) == 0 {
                r.hi = 1.0;
            } else {
                r.lo = -1.0;
            }
        }
    }
    I::new(r.lo.max(-1.0), r.hi.min(1.0))
}

/// tan on an interval that provably lies inside (-pi/2, pi/2); otherwise ENTIRE.
pub fn tan(x: I) -> I {
    if x.is_bad() || !(x.lo > -0.5 * PI_LO && x.hi < 0.5 * PI_LO) {
        return I::ENTIRE;
    }
    I::new(call(mpfr_tan, x.lo, RNDD), call(mpfr_tan, x.hi, RNDU))
}

/// acos on x meet [-1, 1] (decreasing); None if x misses [-1, 1].
pub fn acos(x: I) -> Option<I> {
    let c = x.clamp_to(-1.0, 1.0)?;
    Some(I::new(call(mpfr_acos, c.hi, RNDD), call(mpfr_acos, c.lo, RNDU)))
}

/// asin on x meet [-1, 1] (increasing); None if x misses [-1, 1].
pub fn asin(x: I) -> Option<I> {
    let c = x.clamp_to(-1.0, 1.0)?;
    Some(I::new(call(mpfr_asin, c.lo, RNDD), call(mpfr_asin, c.hi, RNDU)))
}

pub fn atan(x: I) -> I {
    if x.is_bad() {
        return I::new(-0.5 * PI_HI, 0.5 * PI_HI);
    }
    let lo = if x.lo == f64::NEG_INFINITY { -0.5 * PI_HI } else { call(mpfr_atan, x.lo, RNDD) };
    let hi = if x.hi == f64::INFINITY { 0.5 * PI_HI } else { call(mpfr_atan, x.hi, RNDU) };
    I::new(lo, hi)
}

/// Enclosure of the decimal number s (MPFR parses exactly and rounds in the given direction).
pub fn dec(s: &str) -> I {
    let mut z = s.as_bytes().to_vec();
    z.push(0);
    MP.with(|m| {
        let mut m = m.borrow_mut();
        let p = &mut *m;
        unsafe {
            let rc = mpfr_set_str(&mut p.r, z.as_ptr(), 10, RNDD);
            assert_eq!(rc, 0, "bad decimal {s}");
            let lo = mpfr_get_d(&p.r, RNDD);
            mpfr_set_str(&mut p.r, z.as_ptr(), 10, RNDU);
            let hi = mpfr_get_d(&p.r, RNDU);
            I::new(lo, hi)
        }
    })
}

/// Enclosure of (decimal degrees) * pi / 180 (outward interval arithmetic on exact enclosures).
pub fn deg2rad(s: &str) -> I {
    dec(s) * I::PI / I::pt(180.0)
}

/// Check the hard-coded pi enclosure against MPFR.
pub fn selftest() {
    MP.with(|m| {
        let mut m = m.borrow_mut();
        let p = &mut *m;
        unsafe {
            mpfr_const_pi(&mut p.r, RNDD);
            let lo = mpfr_get_d(&p.r, RNDD);
            mpfr_const_pi(&mut p.r, RNDU);
            let hi = mpfr_get_d(&p.r, RNDU);
            assert_eq!(lo, PI_LO);
            assert_eq!(hi, PI_HI);
        }
    });
    let c = cos(I::new(3.0, 3.3));
    assert!(c.lo == -1.0);
    let s = sin(I::new(1.5, 1.6));
    assert!(s.hi == 1.0);
    let _ = up(0.0);
}
