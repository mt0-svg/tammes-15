//! Correctly rounded enclosures through MPFR (system libmpfr.so.6, MPFR 4): for f64 x, the value
//! f(x) is rounded down and up to 53-bit precision (MPFR_RNDD, MPFR_RNDU), which are exact doubles.
//! Used as the reference backend (ivt::Trig::Mpfr) and by the rtrigcheck binary.
use std::cell::RefCell;
use std::os::raw::{c_int, c_long};

#[repr(C)]
struct Mpfr {
    prec: c_long,
    sign: c_int,
    exp: c_long,
    d: *mut u64,
}

#[link(name = ":libmpfr.so.6")]
extern "C" {
    fn mpfr_init2(x: *mut Mpfr, p: c_long);
    fn mpfr_set_d(x: *mut Mpfr, v: f64, r: c_int) -> c_int;
    fn mpfr_cos(y: *mut Mpfr, x: *const Mpfr, r: c_int) -> c_int;
    fn mpfr_sin(y: *mut Mpfr, x: *const Mpfr, r: c_int) -> c_int;
    fn mpfr_acos(y: *mut Mpfr, x: *const Mpfr, r: c_int) -> c_int;
    fn mpfr_asin(y: *mut Mpfr, x: *const Mpfr, r: c_int) -> c_int;
    fn mpfr_atan(y: *mut Mpfr, x: *const Mpfr, r: c_int) -> c_int;
    fn mpfr_tan(y: *mut Mpfr, x: *const Mpfr, r: c_int) -> c_int;
    fn mpfr_const_pi(y: *mut Mpfr, r: c_int) -> c_int;
    fn mpfr_get_d(x: *const Mpfr, r: c_int) -> f64;
}

const RNDN: c_int = 0;
const RNDU: c_int = 2;
const RNDD: c_int = 3;

struct St {
    x: Mpfr,
    y: Mpfr,
}

thread_local! {
    static ST: RefCell<St> = RefCell::new(unsafe {
        let mut x: Mpfr = std::mem::zeroed();
        let mut y: Mpfr = std::mem::zeroed();
        mpfr_init2(&mut x, 53);
        mpfr_init2(&mut y, 53);
        St { x, y }
    });
}

type F = unsafe extern "C" fn(*mut Mpfr, *const Mpfr, c_int) -> c_int;

/// (RD(f(x)), RU(f(x))) for f = 0 cos, 1 acos, 2 asin, 3 atan, 4 tan, 5 sin. NaN outside the domain.
pub fn enc(f: usize, v: f64) -> (f64, f64) {
    let g: F = match f {
        0 => mpfr_cos,
        1 => mpfr_acos,
        2 => mpfr_asin,
        3 => mpfr_atan,
        4 => mpfr_tan,
        _ => mpfr_sin,
    };
    ST.with(|s| {
        let mut s = s.borrow_mut();
        let St { x, y } = &mut *s;
        unsafe {
            mpfr_set_d(x, v, RNDN); // exact: 53-bit precision holds every double
            g(y, x, RNDD);
            let lo = mpfr_get_d(y, RNDD);
            g(y, x, RNDU);
            let hi = mpfr_get_d(y, RNDU);
            (lo, hi)
        }
    })
}

/// (RD(pi), RU(pi)) at 53 bits.
pub fn pi_enc() -> (f64, f64) {
    ST.with(|s| {
        let mut s = s.borrow_mut();
        let St { y, .. } = &mut *s;
        unsafe {
            mpfr_const_pi(y, RNDD);
            let lo = mpfr_get_d(y, RNDD);
            mpfr_const_pi(y, RNDU);
            let hi = mpfr_get_d(y, RNDU);
            (lo, hi)
        }
    })
}
