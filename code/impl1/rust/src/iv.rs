//! Outward-rounded arithmetic on f64 for rigorous bounds.
//!
//! IEEE 754 round-to-nearest gives the exact result of +, -, *, / up to half an ulp, so moving the
//! computed value one ulp down (up) yields a valid lower (upper) bound of the exact result. Only the
//! four basic operations are used here; transcendental constants enter through decimal enclosures
//! computed in PARI/GP (code/gp/consts.gp) and nudged outward once more when parsed.

#[inline(always)]
pub fn dn(x: f64) -> f64 {
    x.next_down()
}
#[inline(always)]
pub fn up(x: f64) -> f64 {
    x.next_up()
}
#[inline(always)]
pub fn add_dn(a: f64, b: f64) -> f64 {
    dn(a + b)
}
#[inline(always)]
pub fn add_up(a: f64, b: f64) -> f64 {
    up(a + b)
}
#[inline(always)]
pub fn sub_dn(a: f64, b: f64) -> f64 {
    dn(a - b)
}
#[inline(always)]
pub fn sub_up(a: f64, b: f64) -> f64 {
    up(a - b)
}
#[inline(always)]
pub fn mul_dn(a: f64, b: f64) -> f64 {
    dn(a * b)
}
#[inline(always)]
pub fn mul_up(a: f64, b: f64) -> f64 {
    up(a * b)
}
#[inline(always)]
pub fn div_dn(a: f64, b: f64) -> f64 {
    dn(a / b)
}
#[inline(always)]
pub fn div_up(a: f64, b: f64) -> f64 {
    up(a / b)
}

/// Lower bound of min over x in [l, u] of c*x.
#[inline(always)]
pub fn cmin(c: f64, l: f64, u: f64) -> f64 {
    if c >= 0.0 {
        mul_dn(c, l)
    } else {
        mul_dn(c, u)
    }
}
/// Upper bound of max over x in [l, u] of c*x.
#[inline(always)]
pub fn cmax(c: f64, l: f64, u: f64) -> f64 {
    if c >= 0.0 {
        mul_up(c, u)
    } else {
        mul_up(c, l)
    }
}

/// Parse a decimal lower bound: nearest f64, then one ulp down.
pub fn parse_dn(s: &str) -> f64 {
    dn(s.parse::<f64>().expect("bad float"))
}
/// Parse a decimal upper bound: nearest f64, then one ulp up.
pub fn parse_up(s: &str) -> f64 {
    up(s.parse::<f64>().expect("bad float"))
}

pub const PI_LO: f64 = 3.141592653589793 - 1e-15;
pub const PI_HI: f64 = 3.141592653589793 + 1e-15;
pub const TWO_PI_LO: f64 = 6.283185307179586 - 2e-15;
pub const TWO_PI_HI: f64 = 6.283185307179586 + 2e-15;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn pi_enclosures() {
        // pi = 3.14159265358979323846..., 2 pi = 6.28318530717958647692...
        assert!(PI_LO < std::f64::consts::PI && std::f64::consts::PI < PI_HI);
        assert!(PI_LO < 3.141592653589793 && PI_HI > 3.1415926535897936);
        assert!(TWO_PI_LO < 6.283185307179586 && TWO_PI_HI > 6.283185307179587);
    }
    #[test]
    fn rounding() {
        assert!(add_dn(0.1, 0.2) < 0.30000000000000004);
        assert!(add_up(0.1, 0.2) > 0.3);
        assert!(cmin(-2.0, 1.0, 3.0) <= -6.0);
        assert!(cmax(-2.0, 1.0, 3.0) >= -2.0);
    }
}
