//! Closed intervals of f64 with outward rounding.
//!
//! Rigor: IEEE 754 binary64 addition, subtraction, multiplication, division and square root
//! return the correctly rounded (round to nearest) value RN(x) of the exact result x. RN(x) is
//! one of the two doubles adjacent to x (or x itself), so next_down(RN(x)) <= x <= next_up(RN(x))
//! for every finite x, and also on overflow (RN(x) = +inf gives next_down = MAX <= x). Every
//! endpoint below is widened by one step in the safe direction, so the result contains the exact
//! set of values. Products 0 * inf (possible only with unbounded intervals) are taken as 0, the
//! standard convention of interval arithmetic for extended endpoints.

use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct I {
    pub lo: f64,
    pub hi: f64,
}

#[inline(always)]
pub fn dn(x: f64) -> f64 {
    x.next_down()
}
#[inline(always)]
pub fn up(x: f64) -> f64 {
    x.next_up()
}

pub const PI_LO: f64 = std::f64::consts::PI; // RN(pi) < pi
pub const PI_HI: f64 = 3.1415926535897936; // next_up(RN(pi)) > pi (checked against MPFR in mp::selftest)

impl I {
    #[inline(always)]
    pub const fn new(lo: f64, hi: f64) -> I {
        I { lo, hi }
    }
    #[inline(always)]
    pub const fn pt(x: f64) -> I {
        I { lo: x, hi: x }
    }
    pub const ENTIRE: I = I { lo: f64::NEG_INFINITY, hi: f64::INFINITY };
    pub const PI: I = I { lo: PI_LO, hi: PI_HI };
    #[inline(always)]
    pub fn two_pi() -> I {
        I::new(2.0 * PI_LO, 2.0 * PI_HI) // exact doubling
    }
    #[inline(always)]
    pub fn half_pi() -> I {
        I::new(0.5 * PI_LO, 0.5 * PI_HI)
    }
    #[inline(always)]
    pub fn width(&self) -> f64 {
        self.hi - self.lo
    }
    /// A double inside the interval (the rounded midpoint, clamped).
    #[inline(always)]
    pub fn mid(&self) -> f64 {
        if !self.lo.is_finite() || !self.hi.is_finite() {
            if self.lo.is_finite() {
                return self.lo;
            }
            if self.hi.is_finite() {
                return self.hi;
            }
            return 0.0;
        }
        let m = 0.5 * self.lo + 0.5 * self.hi;
        m.max(self.lo).min(self.hi)
    }
    /// Upper bound of the radius around mid().
    #[inline(always)]
    pub fn rad_about(&self, c: f64) -> f64 {
        up((c - self.lo).max(self.hi - c))
    }
    #[inline(always)]
    pub fn contains(&self, x: f64) -> bool {
        self.lo <= x && x <= self.hi
    }
    #[inline(always)]
    pub fn contains0(&self) -> bool {
        self.lo <= 0.0 && 0.0 <= self.hi
    }
    #[inline(always)]
    pub fn is_bad(&self) -> bool {
        self.lo.is_nan() || self.hi.is_nan()
    }
    /// Intersection; None if empty.
    #[inline(always)]
    pub fn meet(&self, o: I) -> Option<I> {
        let lo = self.lo.max(o.lo);
        let hi = self.hi.min(o.hi);
        if lo <= hi {
            Some(I::new(lo, hi))
        } else {
            None
        }
    }
    #[inline(always)]
    pub fn hull(&self, o: I) -> I {
        I::new(self.lo.min(o.lo), self.hi.max(o.hi))
    }
    #[inline(always)]
    pub fn abs(&self) -> I {
        if self.lo >= 0.0 {
            *self
        } else if self.hi <= 0.0 {
            I::new(-self.hi, -self.lo)
        } else {
            I::new(0.0, (-self.lo).max(self.hi))
        }
    }
    #[inline(always)]
    pub fn mag(&self) -> f64 {
        self.lo.abs().max(self.hi.abs())
    }
    #[inline(always)]
    pub fn sqr(&self) -> I {
        let a = self.abs();
        let lo = if a.lo == 0.0 { 0.0 } else { dn(a.lo * a.lo).max(0.0) };
        I::new(lo, up(a.hi * a.hi))
    }
    /// Square root; None if the interval lies in (-inf, 0).
    #[inline(always)]
    pub fn sqrt(&self) -> Option<I> {
        if self.hi < 0.0 {
            return None;
        }
        let lo = if self.lo <= 0.0 { 0.0 } else { dn(self.lo.sqrt()).max(0.0) };
        Some(I::new(lo, up(self.hi.sqrt())))
    }
    /// Multiply by a double constant.
    #[inline(always)]
    pub fn scale(&self, c: f64) -> I {
        *self * I::pt(c)
    }
    /// Clamp into [lo, hi] (used for the domain of acos, asin); None if disjoint.
    #[inline(always)]
    pub fn clamp_to(&self, lo: f64, hi: f64) -> Option<I> {
        self.meet(I::new(lo, hi))
    }
}

#[inline(always)]
fn fix0(p: f64) -> f64 {
    if p.is_nan() {
        0.0
    } else {
        p
    }
}

impl Add for I {
    type Output = I;
    #[inline(always)]
    fn add(self, o: I) -> I {
        let lo = self.lo + o.lo;
        let hi = self.hi + o.hi;
        if lo.is_nan() || hi.is_nan() {
            return I::ENTIRE;
        }
        I::new(dn(lo), up(hi))
    }
}
impl Sub for I {
    type Output = I;
    #[inline(always)]
    fn sub(self, o: I) -> I {
        let lo = self.lo - o.hi;
        let hi = self.hi - o.lo;
        if lo.is_nan() || hi.is_nan() {
            return I::ENTIRE;
        }
        I::new(dn(lo), up(hi))
    }
}
impl Neg for I {
    type Output = I;
    #[inline(always)]
    fn neg(self) -> I {
        I::new(-self.hi, -self.lo)
    }
}
impl Mul for I {
    type Output = I;
    #[inline(always)]
    fn mul(self, o: I) -> I {
        let (a, b, c, d) = (self.lo, self.hi, o.lo, o.hi);
        if a >= 0.0 && c >= 0.0 {
            // common case: both nonnegative
            let lo = fix0(a * c);
            let hi = fix0(b * d);
            return I::new(if lo == 0.0 { 0.0 } else { dn(lo) }, up(hi));
        }
        let p1 = fix0(a * c);
        let p2 = fix0(a * d);
        let p3 = fix0(b * c);
        let p4 = fix0(b * d);
        let lo = p1.min(p2).min(p3).min(p4);
        let hi = p1.max(p2).max(p3).max(p4);
        I::new(dn(lo), up(hi))
    }
}
impl Div for I {
    type Output = I;
    #[inline(always)]
    fn div(self, o: I) -> I {
        if o.contains0() || !o.lo.is_finite() || !o.hi.is_finite() || !self.lo.is_finite() || !self.hi.is_finite() {
            return I::ENTIRE;
        }
        let (a, b, c, d) = (self.lo, self.hi, o.lo, o.hi);
        let p1 = a / c;
        let p2 = a / d;
        let p3 = b / c;
        let p4 = b / d;
        let lo = p1.min(p2).min(p3).min(p4);
        let hi = p1.max(p2).max(p3).max(p4);
        I::new(dn(lo), up(hi))
    }
}
impl Add<f64> for I {
    type Output = I;
    #[inline(always)]
    fn add(self, o: f64) -> I {
        self + I::pt(o)
    }
}
impl Sub<f64> for I {
    type Output = I;
    #[inline(always)]
    fn sub(self, o: f64) -> I {
        self - I::pt(o)
    }
}
impl Mul<f64> for I {
    type Output = I;
    #[inline(always)]
    fn mul(self, o: f64) -> I {
        self * I::pt(o)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn pi_bounds() {
        assert!(PI_LO < PI_HI);
        assert_eq!(PI_HI, PI_LO.next_up());
    }
    #[test]
    fn basic() {
        let x = I::new(0.1, 0.2);
        let y = I::new(-0.3, 0.4);
        let z = x * y;
        assert!(z.lo <= -0.06 && z.hi >= 0.08);
        let w = x / I::new(3.0, 3.0);
        assert!(w.lo < 0.1 / 3.0 && w.hi > 0.2 / 3.0);
    }
}
