//! Generic numbers for the face formulas: plain intervals (I) and first-order interval
//! automatic differentiation (D<K>: value enclosure plus enclosures of the K partial derivatives).
//!
//! Soundness of D: every operation propagates value enclosures exactly as I does; the gradient
//! enclosures follow the chain rule with interval evaluation of the derivative over the whole
//! value enclosure. The flag `ok` records that every operation was C^1 on the whole input box
//! (acos/asin arguments strictly inside (-1, 1), sqrt arguments > 0, divisors without 0, no
//! clamping). Only when ok is true may the gradient be used (mean value form, monotonicity,
//! Newton step): then F is C^1 on the convex box and F(y) - F(x) = int_0^1 grad F(x + t(y - x)) dt
//! . (y - x) lies in [grad F] . (y - x).

use crate::elem;
use crate::iv::I;
use std::ops::{Add, Div, Mul, Neg, Sub};

pub trait Num: Copy + Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Div<Output = Self> + Neg<Output = Self> {
    fn c(x: I) -> Self;
    fn v(&self) -> I;
    fn sincos(self) -> (Self, Self);
    /// asin on the clamp to [-1, 1]; None if the value misses [-1, 1].
    fn asin(self) -> Option<Self>;
    /// acos on the clamp to [-1, 1]; None if the value misses [-1, 1].
    fn acos(self) -> Option<Self>;
    fn atan(self) -> Self;
    /// sqrt on the clamp to [0, inf); None if the value is negative.
    fn sqrt(self) -> Option<Self>;
    /// Intersect the value with a range known to contain every true value; None if empty.
    fn meet(self, r: I) -> Option<Self>;
    /// min(self, 1).
    fn min1(self) -> Self;
    fn half(self) -> Self {
        self * Self::c(I::pt(0.5))
    }
    fn twice(self) -> Self {
        self * Self::c(I::pt(2.0))
    }
}

impl Num for I {
    #[inline(always)]
    fn c(x: I) -> I {
        x
    }
    #[inline(always)]
    fn v(&self) -> I {
        *self
    }
    #[inline(always)]
    fn sincos(self) -> (I, I) {
        elem::sincos(self)
    }
    #[inline(always)]
    fn asin(self) -> Option<I> {
        elem::asin(self)
    }
    #[inline(always)]
    fn acos(self) -> Option<I> {
        elem::acos(self)
    }
    #[inline(always)]
    fn atan(self) -> I {
        elem::atan(self)
    }
    #[inline(always)]
    fn sqrt(self) -> Option<I> {
        I::sqrt(&self)
    }
    #[inline(always)]
    fn meet(self, r: I) -> Option<I> {
        I::meet(&self, r)
    }
    #[inline(always)]
    fn min1(self) -> I {
        I::new(self.lo.min(1.0), self.hi.min(1.0))
    }
    #[inline(always)]
    fn half(self) -> I {
        I::new(self.lo * 0.5, self.hi * 0.5) // exact scaling by a power of two (no underflow here)
    }
    #[inline(always)]
    fn twice(self) -> I {
        I::new(self.lo * 2.0, self.hi * 2.0)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct D<const K: usize> {
    pub v: I,
    pub g: [I; K],
    pub ok: bool,
}

impl<const K: usize> D<K> {
    #[inline(always)]
    pub fn var(x: I, j: usize) -> Self {
        let mut g = [I::pt(0.0); K];
        g[j] = I::pt(1.0);
        D { v: x, g, ok: true }
    }
    #[inline(always)]
    fn chain(&self, v: I, fp: I) -> Self {
        let mut g = [I::pt(0.0); K];
        for i in 0..K {
            g[i] = fp * self.g[i];
        }
        D { v, g, ok: self.ok }
    }
    #[inline(always)]
    fn bad(v: I) -> Self {
        D { v, g: [I::ENTIRE; K], ok: false }
    }
}

impl<const K: usize> Add for D<K> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut g = [I::pt(0.0); K];
        for i in 0..K {
            g[i] = self.g[i] + o.g[i];
        }
        D { v: self.v + o.v, g, ok: self.ok && o.ok }
    }
}
impl<const K: usize> Sub for D<K> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        let mut g = [I::pt(0.0); K];
        for i in 0..K {
            g[i] = self.g[i] - o.g[i];
        }
        D { v: self.v - o.v, g, ok: self.ok && o.ok }
    }
}
impl<const K: usize> Neg for D<K> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        let mut g = [I::pt(0.0); K];
        for i in 0..K {
            g[i] = -self.g[i];
        }
        D { v: -self.v, g, ok: self.ok }
    }
}
impl<const K: usize> Mul for D<K> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let mut g = [I::pt(0.0); K];
        for i in 0..K {
            g[i] = self.g[i] * o.v + o.g[i] * self.v;
        }
        D { v: self.v * o.v, g, ok: self.ok && o.ok }
    }
}
impl<const K: usize> Div for D<K> {
    type Output = Self;
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        let v = self.v / o.v;
        if o.v.contains0() || !v.lo.is_finite() || !v.hi.is_finite() {
            return D::bad(v);
        }
        let mut g = [I::pt(0.0); K];
        for i in 0..K {
            g[i] = (self.g[i] - v * o.g[i]) / o.v;
        }
        D { v, g, ok: self.ok && o.ok }
    }
}

impl<const K: usize> Num for D<K> {
    #[inline(always)]
    fn c(x: I) -> Self {
        D { v: x, g: [I::pt(0.0); K], ok: true }
    }
    #[inline(always)]
    fn v(&self) -> I {
        self.v
    }
    #[inline(always)]
    fn sincos(self) -> (Self, Self) {
        let (s, c) = elem::sincos(self.v);
        (self.chain(s, c), self.chain(c, -s))
    }
    #[inline(always)]
    fn asin(self) -> Option<Self> {
        let v = elem::asin(self.v)?;
        if !(self.v.lo > -1.0 && self.v.hi < 1.0) {
            return Some(D::bad(v));
        }
        let w = ((I::pt(1.0) - self.v) * (I::pt(1.0) + self.v)).sqrt().unwrap();
        if w.lo <= 0.0 {
            return Some(D::bad(v));
        }
        Some(self.chain(v, I::pt(1.0) / w))
    }
    #[inline(always)]
    fn acos(self) -> Option<Self> {
        let v = elem::acos(self.v)?;
        if !(self.v.lo > -1.0 && self.v.hi < 1.0) {
            return Some(D::bad(v));
        }
        let w = ((I::pt(1.0) - self.v) * (I::pt(1.0) + self.v)).sqrt().unwrap();
        if w.lo <= 0.0 {
            return Some(D::bad(v));
        }
        Some(self.chain(v, -(I::pt(1.0) / w)))
    }
    #[inline(always)]
    fn atan(self) -> Self {
        let v = elem::atan(self.v);
        if !self.v.lo.is_finite() || !self.v.hi.is_finite() {
            return D::bad(v);
        }
        self.chain(v, I::pt(1.0) / (I::pt(1.0) + self.v.sqr()))
    }
    #[inline(always)]
    fn sqrt(self) -> Option<Self> {
        let v = I::sqrt(&self.v)?;
        if self.v.lo <= 0.0 || v.lo <= 0.0 {
            return Some(D::bad(v));
        }
        Some(self.chain(v, I::pt(1.0) / v.twice()))
    }
    #[inline(always)]
    fn meet(self, r: I) -> Option<Self> {
        let v = I::meet(&self.v, r)?;
        if v == self.v {
            Some(self)
        } else {
            // a true clamp: the formula is no longer the smooth one on the whole box
            Some(D::bad(v))
        }
    }
    #[inline(always)]
    fn min1(self) -> Self {
        if self.v.hi < 1.0 {
            self
        } else if self.v.lo >= 1.0 {
            D::c(I::pt(1.0))
        } else {
            D::bad(self.v.min1())
        }
    }
}
