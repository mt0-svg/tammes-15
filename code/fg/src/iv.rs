//! Closed intervals of f64 with outward rounding.
//!
//! The four operations and sqrt are rounded to nearest by IEEE 754 and widened by one ulp on each
//! side. The elementary functions (sin, cos, tan, asin, acos, atan) call the platform libm, whose
//! error is below 1 ulp for these functions in glibc; their results are widened by `LIBM_ULPS`
//! ulps on each side. Every function is evaluated through its monotonicity on the argument range,
//! so an enclosure of the range follows from enclosures of the values at the ends.

use std::f64::consts::{FRAC_PI_2, PI};

pub const LIBM_ULPS: u32 = 4;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Iv {
    pub lo: f64,
    pub hi: f64,
}

#[inline]
fn dn(x: f64, k: u32) -> f64 {
    let mut y = x;
    for _ in 0..k {
        y = y.next_down();
    }
    y
}
#[inline]
fn up(x: f64, k: u32) -> f64 {
    let mut y = x;
    for _ in 0..k {
        y = y.next_up();
    }
    y
}

/// Enclosure of pi.
pub const PI_IV: Iv = Iv { lo: 3.141592653589793, hi: 3.1415926535897936 };

impl Iv {
    #[inline]
    pub fn new(lo: f64, hi: f64) -> Iv {
        debug_assert!(lo <= hi, "bad interval {lo} {hi}");
        Iv { lo, hi }
    }
    #[inline]
    pub fn pt(x: f64) -> Iv {
        Iv { lo: x, hi: x }
    }
    #[inline]
    pub fn w(&self) -> f64 {
        self.hi - self.lo
    }
    #[inline]
    pub fn mid(&self) -> f64 {
        0.5 * (self.lo + self.hi)
    }
    #[inline]
    pub fn add(self, o: Iv) -> Iv {
        Iv { lo: dn(self.lo + o.lo, 1), hi: up(self.hi + o.hi, 1) }
    }
    #[inline]
    pub fn sub(self, o: Iv) -> Iv {
        Iv { lo: dn(self.lo - o.hi, 1), hi: up(self.hi - o.lo, 1) }
    }
    #[inline]
    pub fn neg(self) -> Iv {
        Iv { lo: -self.hi, hi: -self.lo }
    }
    pub fn mul(self, o: Iv) -> Iv {
        let p = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi];
        let mut lo = p[0];
        let mut hi = p[0];
        for &x in &p[1..] {
            lo = lo.min(x);
            hi = hi.max(x);
        }
        Iv { lo: dn(lo, 1), hi: up(hi, 1) }
    }
    pub fn div(self, o: Iv) -> Iv {
        assert!(o.lo > 0.0 || o.hi < 0.0, "division by an interval containing 0");
        let p = [self.lo / o.lo, self.lo / o.hi, self.hi / o.lo, self.hi / o.hi];
        let mut lo = p[0];
        let mut hi = p[0];
        for &x in &p[1..] {
            lo = lo.min(x);
            hi = hi.max(x);
        }
        Iv { lo: dn(lo, 1), hi: up(hi, 1) }
    }
    /// Multiplication by an exact small scalar (a power of two or a small integer).
    pub fn scale(self, c: f64) -> Iv {
        self.mul(Iv::pt(c))
    }
    pub fn sqrt(self) -> Iv {
        assert!(self.lo >= 0.0);
        Iv { lo: dn(self.lo.sqrt(), 1).max(0.0), hi: up(self.hi.sqrt(), 1) }
    }
    pub fn hull(self, o: Iv) -> Iv {
        Iv { lo: self.lo.min(o.lo), hi: self.hi.max(o.hi) }
    }
    pub fn meet(self, o: Iv) -> Option<Iv> {
        let lo = self.lo.max(o.lo);
        let hi = self.hi.min(o.hi);
        if lo <= hi {
            Some(Iv { lo, hi })
        } else {
            None
        }
    }
    /// cos on an interval inside [-pi/2 - 1, pi + 1]: decreasing on [0, pi], increasing on
    /// [-pi, 0], with the maximum 1 at 0 and the minimum -1 at pi.
    pub fn cos(self) -> Iv {
        assert!(self.lo >= -FRAC_PI_2 - 1.0 && self.hi <= PI + 1.0, "cos range {:?}", self);
        let a = self.lo.cos();
        let b = self.hi.cos();
        let mut lo = dn(a.min(b), LIBM_ULPS);
        let mut hi = up(a.max(b), LIBM_ULPS);
        if self.lo <= 0.0 && self.hi >= 0.0 {
            hi = 1.0;
        }
        if self.lo <= PI_IV.hi && self.hi >= PI_IV.lo {
            lo = -1.0;
        }
        Iv { lo: lo.max(-1.0), hi: hi.min(1.0) }
    }
    /// sin on an interval inside [-pi/2, 3 pi / 2]: maximum 1 at pi/2.
    pub fn sin(self) -> Iv {
        assert!(self.lo >= -FRAC_PI_2 && self.hi <= 1.5 * PI, "sin range {:?}", self);
        let a = self.lo.sin();
        let b = self.hi.sin();
        let mut lo = dn(a.min(b), LIBM_ULPS);
        let mut hi = up(a.max(b), LIBM_ULPS);
        // pi/2 is not a double; FRAC_PI_2 is within 1 ulp of it
        if self.lo <= up(FRAC_PI_2, 1) && self.hi >= dn(FRAC_PI_2, 1) {
            hi = 1.0;
        }
        if self.lo <= dn(-FRAC_PI_2, 0) {
            lo = -1.0;
        }
        Iv { lo: lo.max(-1.0), hi: hi.min(1.0) }
    }
    /// tan on an interval inside (-pi/2, pi/2): increasing.
    pub fn tan(self) -> Iv {
        assert!(self.lo > -FRAC_PI_2 + 1e-9 && self.hi < FRAC_PI_2 - 1e-9, "tan range {:?}", self);
        Iv { lo: dn(self.lo.tan(), LIBM_ULPS), hi: up(self.hi.tan(), LIBM_ULPS) }
    }
    /// atan: increasing.
    pub fn atan(self) -> Iv {
        Iv { lo: dn(self.lo.atan(), LIBM_ULPS), hi: up(self.hi.atan(), LIBM_ULPS) }
    }
    /// asin on an interval inside [-1, 1]: increasing.
    pub fn asin(self) -> Iv {
        assert!(self.lo >= -1.0 && self.hi <= 1.0, "asin range {:?}", self);
        Iv { lo: dn(self.lo.asin(), LIBM_ULPS), hi: up(self.hi.asin(), LIBM_ULPS) }
    }
    /// acos on an interval inside [-1, 1]: decreasing.
    pub fn acos(self) -> Iv {
        assert!(self.lo >= -1.0 && self.hi <= 1.0, "acos range {:?}", self);
        Iv { lo: dn(self.hi.acos(), LIBM_ULPS).max(0.0), hi: up(self.lo.acos(), LIBM_ULPS) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn contains_known_values() {
        let x = Iv::new(0.3, 0.7);
        let c = x.cos();
        assert!(c.lo <= 0.7f64.cos() && 0.3f64.cos() <= c.hi);
        let s = Iv::new(1.0, 2.0).sin();
        assert!(s.hi == 1.0 && s.lo <= 1.0f64.sin().min(2.0f64.sin()));
        let a = Iv::new(-0.5, 0.25).acos();
        assert!(a.lo <= 0.25f64.acos() && (-0.5f64).acos() <= a.hi);
        let p = Iv::pt(-1.0).acos();
        assert!(p.lo <= PI && PI <= p.hi);
        assert!(PI_IV.lo < PI_IV.hi && PI_IV.lo == PI);
        let q = Iv::new(1.0, 2.0).mul(Iv::new(-3.0, 0.5));
        assert!(q.lo <= -6.0 && q.hi >= 1.0);
    }
}
