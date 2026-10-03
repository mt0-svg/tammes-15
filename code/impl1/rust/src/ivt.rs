//! Interval arithmetic on f64 with outward rounding, including the transcendental functions
//! needed for spherical trigonometry.
//!
//! Basic operations: IEEE round-to-nearest result moved one ulp outward (rigorous).
//! Transcendental functions at the interval endpoints: rtrig.rs, rigorous enclosures from IEEE
//! basic operations and Taylor series with remainder bounds; no libm call, no assumption. The
//! results are memoised per thread in a direct-mapped cache keyed by the argument bits (the
//! functions are deterministic, so a hit returns the same enclosure).

use crate::iv::{PI_HI, PI_LO};

/// Name of the backend of the transcendental functions, printed in the replay logs.
pub fn trig_name() -> &'static str {
    "rig"
}

const CBITS: u32 = 16;
struct Cache {
    keys: Vec<u64>,
    vals: Vec<(f64, f64)>,
}
thread_local! {
    static CACHE: std::cell::RefCell<Cache> = std::cell::RefCell::new(Cache {
        keys: vec![u64::MAX; 5 << CBITS],
        vals: vec![(0.0, 0.0); 5 << CBITS],
    });
}

/// Enclosure (lo, hi) of function f (0 cos, 1 acos, 2 asin, 3 atan, 4 tan) at the point x.
#[inline]
fn enc(f: usize, x: f64) -> (f64, f64) {
    CACHE.with(|c| {
        let mut c = c.borrow_mut();
        let b = x.to_bits();
        let h = ((b.wrapping_mul(0x9E3779B97F4A7C15) >> (64 - CBITS)) as usize) + (f << CBITS);
        if c.keys[h] == b {
            return c.vals[h];
        }
        let e = match f {
            0 => crate::rtrig::cos_enc(x),
            1 => crate::rtrig::acos_enc(x),
            2 => crate::rtrig::asin_enc(x),
            3 => crate::rtrig::atan_enc(x),
            _ => crate::rtrig::tan_enc(x),
        };
        let r = (e.lo, e.hi);
        c.keys[h] = b;
        c.vals[h] = r;
        r
    })
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Iv {
    pub lo: f64,
    pub hi: f64,
}

impl Iv {
    #[inline]
    pub fn new(lo: f64, hi: f64) -> Iv {
        Iv { lo, hi }
    }
    #[inline]
    pub fn pt(x: f64) -> Iv {
        Iv { lo: x, hi: x }
    }
    pub fn pi() -> Iv {
        Iv { lo: PI_LO, hi: PI_HI }
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        !(self.lo <= self.hi)
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
    pub fn meet(&self, o: Iv) -> Iv {
        Iv { lo: self.lo.max(o.lo), hi: self.hi.min(o.hi) }
    }
    #[inline]
    pub fn hull(&self, o: Iv) -> Iv {
        Iv { lo: self.lo.min(o.lo), hi: self.hi.max(o.hi) }
    }
    #[inline]
    pub fn contains(&self, x: f64) -> bool {
        self.lo <= x && x <= self.hi
    }
    pub fn add(self, o: Iv) -> Iv {
        Iv { lo: (self.lo + o.lo).next_down(), hi: (self.hi + o.hi).next_up() }
    }
    pub fn sub(self, o: Iv) -> Iv {
        Iv { lo: (self.lo - o.hi).next_down(), hi: (self.hi - o.lo).next_up() }
    }
    pub fn neg(self) -> Iv {
        Iv { lo: -self.hi, hi: -self.lo }
    }
    pub fn mul(self, o: Iv) -> Iv {
        let p = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi];
        if p.iter().any(|v| v.is_nan()) {
            // 0 times an infinite end: no information (never read as emptiness)
            return Iv { lo: f64::NEG_INFINITY, hi: f64::INFINITY };
        }
        let mut lo = f64::INFINITY;
        let mut hi = f64::NEG_INFINITY;
        for v in p {
            lo = lo.min(v);
            hi = hi.max(v);
        }
        Iv { lo: lo.next_down(), hi: hi.next_up() }
    }
    pub fn scale(self, c: f64) -> Iv {
        self.mul(Iv::pt(c))
    }
    /// division; the divisor must not contain 0 (returns the whole line otherwise)
    pub fn div(self, o: Iv) -> Iv {
        if o.lo <= 0.0 && o.hi >= 0.0 {
            return Iv { lo: f64::NEG_INFINITY, hi: f64::INFINITY };
        }
        let p = [self.lo / o.lo, self.lo / o.hi, self.hi / o.lo, self.hi / o.hi];
        if p.iter().any(|v| v.is_nan()) {
            return Iv { lo: f64::NEG_INFINITY, hi: f64::INFINITY };
        }
        let mut lo = f64::INFINITY;
        let mut hi = f64::NEG_INFINITY;
        for v in p {
            lo = lo.min(v);
            hi = hi.max(v);
        }
        Iv { lo: lo.next_down(), hi: hi.next_up() }
    }
    pub fn sqr(self) -> Iv {
        if self.lo >= 0.0 {
            Iv { lo: (self.lo * self.lo).next_down(), hi: (self.hi * self.hi).next_up() }
        } else if self.hi <= 0.0 {
            Iv { lo: (self.hi * self.hi).next_down(), hi: (self.lo * self.lo).next_up() }
        } else {
            Iv { lo: 0.0, hi: (self.lo * self.lo).max(self.hi * self.hi).next_up() }
        }
    }
    /// sqrt of the nonnegative part (sqrt is correctly rounded in IEEE 754)
    pub fn sqrt(self) -> Iv {
        let lo = self.lo.max(0.0);
        Iv { lo: lo.sqrt().next_down().max(0.0), hi: self.hi.max(0.0).sqrt().next_up() }
    }
    pub fn cos(self) -> Iv {
        if self.w() >= 6.0 {
            return Iv::new(-1.0, 1.0);
        }
        // cos is decreasing on [2k pi, (2k+1) pi]
        let (a, a2) = enc(0, self.lo);
        let (b, b2) = enc(0, self.hi);
        let (a, a2, b, b2) = (a.max(-1.0), a2.min(1.0), b.max(-1.0), b2.min(1.0));
        let mut lo = a.min(b);
        let mut hi = a2.max(b2);
        // extrema at multiples of pi inside the interval (checked with pi enclosures)
        let kmin = (self.lo / PI_HI).floor() as i64 - 1;
        let kmax = (self.hi / PI_LO).ceil() as i64 + 1;
        for k in kmin..=kmax {
            let (klo, khi) = if k >= 0 { (k as f64 * PI_LO, k as f64 * PI_HI) } else { (k as f64 * PI_HI, k as f64 * PI_LO) };
            if khi >= self.lo && klo <= self.hi {
                if k % 2 == 0 {
                    hi = 1.0;
                } else {
                    lo = -1.0;
                }
            }
        }
        Iv { lo, hi }
    }
    pub fn sin(self) -> Iv {
        // sin x = cos(x - pi/2)
        let half_pi = Iv::new(PI_LO * 0.5, PI_HI * 0.5);
        self.sub(half_pi).cos()
    }
    /// acos on the part inside [-1, 1] (decreasing)
    pub fn acos(self) -> Iv {
        let lo = self.lo.max(-1.0);
        let hi = self.hi.min(1.0);
        if lo > hi {
            return Iv { lo: f64::NAN, hi: f64::NAN };
        }
        Iv { lo: enc(1, hi).0.max(0.0), hi: enc(1, lo).1 }
    }
    /// asin on the part inside [-1, 1] (increasing)
    pub fn asin(self) -> Iv {
        let lo = self.lo.max(-1.0);
        let hi = self.hi.min(1.0);
        if lo > hi {
            return Iv { lo: f64::NAN, hi: f64::NAN };
        }
        Iv { lo: enc(2, lo).0, hi: enc(2, hi).1 }
    }
    pub fn atan(self) -> Iv {
        Iv { lo: enc(3, self.lo).0, hi: enc(3, self.hi).1 }
    }
    /// tan on an interval inside (-pi/2, pi/2) (increasing); whole line otherwise
    pub fn tan(self) -> Iv {
        if !(self.lo > -PI_LO * 0.5 && self.hi < PI_LO * 0.5) {
            return Iv { lo: f64::NEG_INFINITY, hi: f64::INFINITY };
        }
        Iv { lo: enc(4, self.lo).0, hi: enc(4, self.hi).1 }
    }
}

/// Side opposite to angle `ang` in a spherical triangle with sides b, c around it.
pub fn side_from_angle(b: Iv, c: Iv, ang: Iv) -> Iv {
    b.cos().mul(c.cos()).add(b.sin().mul(c.sin()).mul(ang.cos())).acos()
}
/// Angle opposite to side a in a spherical triangle with sides a, b, c.
pub fn angle_from_sides(a: Iv, b: Iv, c: Iv) -> Iv {
    a.cos().sub(b.cos().mul(c.cos())).div(b.sin().mul(c.sin())).acos()
}
/// Angle of the equilateral triangle of side d.
pub fn alpha(d: Iv) -> Iv {
    let c = d.cos();
    c.div(c.add(Iv::pt(1.0))).acos()
}
/// Other angle of a rhombus with side d and angle x: 2 acot(cos d tan(x/2)), decreasing in x,
/// increasing in d; evaluated by monotonicity (x in (0, pi), d in (0, pi/2)).
pub fn rho(x: Iv, d: Iv) -> Iv {
    let f = |xx: f64, dd: f64| -> Iv {
        let t = Iv::pt(xx).scale(0.5).tan();
        let k = Iv::pt(dd).cos();
        let z = t.mul(k);
        Iv::pt(1.0).div(z).atan().scale(2.0)
    };
    let lo = f(x.hi, d.lo);
    let hi = f(x.lo, d.hi);
    Iv { lo: lo.lo, hi: hi.hi }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn enclosures() {
        let x = Iv::new(0.3, 0.31);
        let c = x.cos();
        assert!(c.contains(0.3f64.cos()) && c.contains(0.31f64.cos()));
        let y = Iv::new(3.0, 3.3);
        assert_eq!(y.cos().lo, -1.0);
        let s = Iv::new(1.5, 1.6).sin();
        assert_eq!(s.hi, 1.0);
        let d = Iv::pt(1.0);
        let a = alpha(d);
        let e = (1.0f64.cos() / (1.0 + 1.0f64.cos())).acos();
        assert!(a.contains(e));
        // rhombus with angle alpha has other angle 2 alpha
        let r = rho(Iv::pt(e), d);
        assert!(r.lo <= 2.0 * e + 1e-12 && r.hi >= 2.0 * e - 1e-12, "{r:?} {}", 2.0 * e);
        // equilateral triangle: side from angle
        let s = side_from_angle(d, d, Iv::pt(e));
        assert!(s.lo <= 1.0 + 1e-12 && s.hi >= 1.0 - 1e-12);
    }
}
