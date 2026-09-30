//! Face relations as explicit formulas, generic over I and D<K>.
//!
//! Notation (derivations in Section 6.5 of the paper): a face is a convex
//! equilateral spherical polygon A_0 .. A_{m-1} of side d, corners u_i in [alpha(d), pi]. In a
//! convex polygon the rays from a vertex to the other vertices appear in their cyclic order inside
//! the corner, so a corner is the sum of the angles of the triangles of any fan of diagonals.
//!
//! Spherical trigonometry used (sides in (0, pi)):
//! - law of cosines: cos a = cos b cos c + sin b sin c cos A; the angle opposite g in a triangle
//!   with sides g, e, f: acos((cos g - cos e cos f) / (sin e sin f));
//! - isosceles triangle, legs d, apex angle u: sin(e/2) = sin d sin(u/2) (e the base) and base
//!   angle beta = atan(cos(u/2) / (cos d sin(u/2))) (Napier: cos d = cot(u/2) cot beta);
//! - isosceles triangle, legs d, base D: apex 2 asin(sin(D/2) / sin d), base angle gamma with
//!   cos gamma = tan(D/2) cot d (Napier on the half triangle).

use crate::ad::Num;
use crate::iv::{I, PI_HI};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fam {
    /// in: d, u_{i+2}, u_{i+3}; out: u_i, u_{i+1}, u_{i-1} (pentagon split by A_{i-1} A_{i+1})
    PentSplit,
    /// in: d, u_{i+1}, u_{i-1}; out: u_i, u_{i+2}, u_{i-2} (pentagon fan from A_i)
    PentFan,
    /// in: d, u_{p+1}, u_{p+3}, u_{p+5}; out: u_p, u_{p+2}, u_{p+4}
    HexAlt,
    /// in: d, u_{i+1}, u_{i+2}, u_{i+3}; out: u_i, u_{i+4}, u_{i+5}
    HexChain5,
    /// in: d, u_{i+s}, u_{i+2s}, u_{i+4s}; out: u_i, u_{i+3s}, u_{i+5s}
    HexC4Iso,
    /// in: d, u_{i+1}; out: lower bound of u_{i+2} (|A_i A_{i+3}| >= d)
    HexLong,
    /// in: d, x; out: y (rhombus, opposite corner pair)
    RhoY,
    /// in: x, y; out: d (rhombus)
    RhoD,
    /// in: d; out: alpha(d)
    Alpha,
    /// in: a; out: alpha^{-1}(a)
    AlphaInv,
    /// in: d, r_{i-1}, r_i, r_{i+1}; out: u_i (wheel of a full hexagon)
    WCorner,
    /// in: d, r_i, r_{i+1}; out: theta_i (angle at the free point)
    WTheta,
    /// in: d, r_{i-1}, r_i, u_i; out: r_{i+1}
    WBack,
}

impl Fam {
    pub fn nin(self) -> usize {
        match self {
            Fam::PentSplit | Fam::PentFan | Fam::WTheta => 3,
            Fam::HexAlt | Fam::HexChain5 | Fam::HexC4Iso | Fam::WCorner | Fam::WBack => 4,
            Fam::HexLong | Fam::RhoY | Fam::RhoD => 2,
            Fam::Alpha | Fam::AlphaInv => 1,
        }
    }
    pub fn nout(self) -> usize {
        match self {
            Fam::PentSplit | Fam::PentFan | Fam::HexAlt | Fam::HexChain5 | Fam::HexC4Iso => 3,
            _ => 1,
        }
    }
}

#[inline(always)]
fn one<T: Num>() -> T {
    T::c(I::pt(1.0))
}

#[inline(always)]
fn ang_range() -> I {
    I::new(0.0, PI_HI)
}

#[inline(always)]
fn unit() -> I {
    I::new(-1.0, 1.0)
}

/// sqrt(1 - c^2) computed as sqrt((1 - c)(1 + c)).
#[inline(always)]
fn sin_from_cos<T: Num>(c: T) -> Option<T> {
    ((one::<T>() - c) * (one::<T>() + c)).sqrt()
}

struct Iso<T> {
    se2: T,
    ce2: T,
    ce: T,
    se: T,
    beta: T,
}

#[inline(always)]
fn iso<T: Num>(sd: T, cd: T, u: T) -> Option<Iso<T>> {
    let (s2, c2) = u.half().sincos();
    let se2 = sd * s2;
    let ce2 = sin_from_cos(se2)?;
    let sq = se2 * se2;
    let ce = one::<T>() - sq.twice();
    let se = (se2 * ce2).twice();
    let beta = (c2 / (cd * s2)).atan();
    Some(Iso { se2, ce2, ce, se, beta })
}

/// Angle opposite side g (cos g = cg) in a triangle with the other sides e, f.
#[inline(always)]
fn ang<T: Num>(cg: T, ce: T, se: T, cf: T, sf: T) -> Option<T> {
    ((cg - ce * cf) / (se * sf)).acos()
}

/// Closing isosceles triangle (legs d) on a base D given by cos D: (apex angle, base angle).
#[inline(always)]
fn closing<T: Num>(sd: T, cd: T, c_base: T) -> Option<(T, T)> {
    let s2 = (one::<T>() - c_base).half().meet(I::new(0.0, 1.0))?.sqrt()?; // sin(D/2)
    let c2 = (one::<T>() + c_base).half().meet(I::new(0.0, 1.0))?.sqrt()?; // cos(D/2)
    let apex = (s2 / sd).asin()?.twice();
    let gam = ((s2 * cd) / (c2 * sd)).acos()?;
    Some((apex, gam))
}

/// Evaluate a family. Returns None when the box provably contains no solution (a triangle
/// that cannot exist, an angle that must be negative, ...).
#[inline(always)]
pub fn eval<T: Num>(fam: Fam, x: &[T; 4]) -> Option<[T; 3]> {
    let z = T::c(I::pt(0.0));
    match fam {
        Fam::Alpha => {
            let (_, cd) = x[0].sincos();
            let a = (cd / (one::<T>() + cd)).acos()?;
            Some([a, z, z])
        }
        Fam::AlphaInv => {
            let (_, ca) = x[0].sincos();
            let d = (ca / (one::<T>() - ca)).acos()?;
            Some([d, z, z])
        }
        Fam::RhoY => {
            let (_, cd) = x[0].sincos();
            let (s2, c2) = x[1].half().sincos();
            let y = (c2 / (cd * s2)).atan().twice();
            Some([y, z, z])
        }
        Fam::RhoD => {
            let (sx, cx) = x[0].half().sincos();
            let (sy, cy) = x[1].half().sincos();
            let d = ((cx * cy) / (sx * sy)).acos()?;
            Some([d, z, z])
        }
        Fam::PentSplit => {
            let (sd, cd) = x[0].sincos();
            let p = iso(sd, cd, x[1])?;
            let th = (x[2] - p.beta).meet(ang_range())?;
            let (_, cth) = th.sincos();
            let c_d = (p.ce * cd + p.se * sd * cth).meet(unit())?;
            let s_d = sin_from_cos(c_d)?;
            let phi1 = p.beta + ang(cd, p.ce, p.se, c_d, s_d)?;
            let phim = ang(p.ce, cd, sd, c_d, s_d)?;
            let (apex, gam) = closing(sd, cd, c_d)?;
            Some([apex, phi1 + gam, phim + gam])
        }
        Fam::PentFan => {
            let (sd, cd) = x[0].sincos();
            let a = iso(sd, cd, x[1])?;
            let b = iso(sd, cd, x[2])?;
            let mi = ang(cd, a.ce, a.se, b.ce, b.se)?;
            let m2 = ang(b.ce, a.ce, a.se, cd, sd)?;
            let mm2 = ang(a.ce, b.ce, b.se, cd, sd)?;
            Some([a.beta + b.beta + mi, a.beta + m2, b.beta + mm2])
        }
        Fam::HexAlt => {
            let (sd, cd) = x[0].sincos();
            let p1 = iso(sd, cd, x[1])?;
            let p3 = iso(sd, cd, x[2])?;
            let p5 = iso(sd, cd, x[3])?;
            let g0 = ang(p3.ce, p1.ce, p1.se, p5.ce, p5.se)?;
            let g2 = ang(p5.ce, p1.ce, p1.se, p3.ce, p3.se)?;
            let g4 = ang(p1.ce, p3.ce, p3.se, p5.ce, p5.se)?;
            Some([p1.beta + p5.beta + g0, p1.beta + p3.beta + g2, p3.beta + p5.beta + g4])
        }
        Fam::HexChain5 => {
            let (sd, cd) = x[0].sincos();
            let a = iso(sd, cd, x[1])?;
            let b = iso(sd, cd, x[3])?;
            let th = (x[2] - a.beta - b.beta).meet(ang_range())?;
            let (_, cth) = th.sincos();
            let c_d = (a.ce * b.ce + a.se * b.se * cth).meet(unit())?;
            let s_d = sin_from_cos(c_d)?;
            let phi0 = a.beta + ang(b.ce, a.ce, a.se, c_d, s_d)?;
            let phi4 = b.beta + ang(a.ce, b.ce, b.se, c_d, s_d)?;
            let (apex, gam) = closing(sd, cd, c_d)?;
            Some([phi0 + gam, phi4 + gam, apex])
        }
        Fam::HexC4Iso => {
            let (sd, cd) = x[0].sincos();
            let a = iso(sd, cd, x[1])?;
            let th = (x[2] - a.beta).meet(ang_range())?;
            let (_, cth) = th.sincos();
            let c_d = (a.ce * cd + a.se * sd * cth).meet(unit())?;
            let s_d = sin_from_cos(c_d)?;
            let phi0 = a.beta + ang(cd, a.ce, a.se, c_d, s_d)?;
            let phi3 = ang(a.ce, cd, sd, c_d, s_d)?;
            let b = iso(sd, cd, x[3])?;
            let psi0 = ang(b.ce, cd, sd, c_d, s_d)?;
            let psi3 = ang(cd, b.ce, b.se, c_d, s_d)?;
            let psi5 = ang(c_d, b.ce, b.se, cd, sd)?;
            Some([phi0 + psi0, phi3 + b.beta + psi3, b.beta + psi5])
        }
        Fam::HexLong => {
            let (sd, cd) = x[0].sincos();
            let a = iso(sd, cd, x[1])?;
            let k = ((a.se2 / a.ce2) * (cd / sd)).min1();
            let l = a.beta + k.acos()?;
            Some([l, z, z])
        }
        Fam::WCorner => {
            let (sd, cd) = x[0].sincos();
            let (_, ca) = x[1].sincos();
            let (sb, cb) = x[2].sincos();
            let (_, cc) = x[3].sincos();
            let mu = ang(cc, cb, sb, cd, sd)?;
            let nu = ang(ca, cb, sb, cd, sd)?;
            Some([mu + nu, z, z])
        }
        Fam::WTheta => {
            let (_, cd) = x[0].sincos();
            let (sa, ca) = x[1].sincos();
            let (sb, cb) = x[2].sincos();
            let th = ang(cd, ca, sa, cb, sb)?;
            Some([th, z, z])
        }
        Fam::WBack => {
            let (sd, cd) = x[0].sincos();
            let (_, ca) = x[1].sincos();
            let (sb, cb) = x[2].sincos();
            let nu = ang(ca, cb, sb, cd, sd)?;
            let mu = (x[3] - nu).meet(ang_range())?;
            let (_, cmu) = mu.sincos();
            let r = (cb * cd + sb * sd * cmu).acos()?;
            Some([r, z, z])
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ad::D;
    use crate::geom::{random_polygon, Rng};

    fn widen(x: f64, e: f64) -> I {
        I::new(x - e, x + e)
    }

    /// Check a family on one true polygon: inputs as tiny intervals, outputs must contain the
    /// true corners (up to the construction error).
    fn check(fam: Fam, d: f64, ins: &[f64], outs: &[(f64, Kind)]) {
        let e = 1e-12;
        let mut x = [I::pt(0.0); 4];
        x[0] = widen(d, e);
        for (k, &v) in ins.iter().enumerate() {
            x[k + 1] = widen(v, e);
        }
        let r = eval::<I>(fam, &x).unwrap_or_else(|| panic!("{fam:?} refuted a true polygon"));
        let mut xd = [D::<4>::c(I::pt(0.0)); 4];
        for j in 0..=ins.len() {
            xd[j] = D::var(x[j], j);
        }
        let rd = eval::<D<4>>(fam, &xd).unwrap_or_else(|| panic!("{fam:?} (AD) refuted a true polygon"));
        for (k, &(t, kind)) in outs.iter().enumerate() {
            for v in [r[k], rd[k].v] {
                let ok = match kind {
                    Kind::Eq => v.lo <= t + 1e-8 && t - 1e-8 <= v.hi,
                    Kind::Ge => v.lo <= t + 1e-8,
                };
                assert!(ok, "{fam:?} output {k}: true {t} enclosure {v:?}");
                if let Kind::Eq = kind {
                    assert!(v.width() < 1e-6, "{fam:?} output {k}: wide enclosure {v:?}");
                }
            }
        }
    }

    #[derive(Clone, Copy)]
    enum Kind {
        Eq,
        Ge,
    }

    #[test]
    fn random_polygons() {
        let mut rng = Rng(987654321);
        let (dlo, dhi) = (0.9365, 0.9892);
        let mut counts = [0usize; 2];
        let mut tries = 0;
        while counts[0] < 3000 || counts[1] < 3000 {
            tries += 1;
            assert!(tries < 5_000_000);
            let m = if counts[0] < 3000 { 5 } else { 6 };
            let d = dlo + (dhi - dlo) * rng.next();
            let amin = (d.cos() / (1.0 + d.cos())).acos();
            let (_pts, u) = match random_polygon(m, d, amin, &mut rng) {
                Some(x) => x,
                None => continue,
            };
            counts[m - 5] += 1;
            let mi = m as i64;
            let uu = |k: i64| u[k.rem_euclid(mi) as usize];
            if m == 5 {
                for i in 0..5i64 {
                    check(Fam::PentSplit, d, &[uu(i + 2), uu(i + 3)], &[(uu(i), Kind::Eq), (uu(i + 1), Kind::Eq), (uu(i - 1), Kind::Eq)]);
                    check(Fam::PentFan, d, &[uu(i + 1), uu(i - 1)], &[(uu(i), Kind::Eq), (uu(i + 2), Kind::Eq), (uu(i - 2), Kind::Eq)]);
                }
            } else {
                for p0 in 0..2i64 {
                    check(Fam::HexAlt, d, &[uu(p0 + 1), uu(p0 + 3), uu(p0 + 5)], &[(uu(p0), Kind::Eq), (uu(p0 + 2), Kind::Eq), (uu(p0 + 4), Kind::Eq)]);
                }
                for i in 0..6i64 {
                    check(Fam::HexChain5, d, &[uu(i + 1), uu(i + 2), uu(i + 3)], &[(uu(i), Kind::Eq), (uu(i + 4), Kind::Eq), (uu(i + 5), Kind::Eq)]);
                    for s in [1i64, -1] {
                        check(Fam::HexC4Iso, d, &[uu(i + s), uu(i + 2 * s), uu(i + 4 * s)], &[(uu(i), Kind::Eq), (uu(i + 3 * s), Kind::Eq), (uu(i + 5 * s), Kind::Eq)]);
                        check(Fam::HexLong, d, &[uu(i + s)], &[(uu(i + 2 * s), Kind::Ge)]);
                    }
                }
            }
        }
        eprintln!("pentagons {} hexagons {} tries {}", counts[0], counts[1], tries);
    }

    #[test]
    fn rhombus_and_alpha() {
        let mut rng = Rng(42);
        for _ in 0..10000 {
            let d: f64 = 0.9365 + 0.0527 * rng.next();
            let a = (d.cos() / (1.0 + d.cos())).acos();
            let x = a + a * rng.next();
            let y = 2.0 * ((x / 2.0).cos() / (d.cos() * (x / 2.0).sin())).atan();
            // an independent check of the rhombus: cos d = cot(x/2) cot(y/2)
            assert!(((x / 2.0).tan().recip() * (y / 2.0).tan().recip() - d.cos()).abs() < 1e-12);
            let z = I::pt(0.0);
            let r = eval::<I>(Fam::RhoY, &[widen(d, 1e-13), widen(x, 1e-13), z, z]).unwrap()[0];
            assert!(r.lo <= y + 1e-10 && y - 1e-10 <= r.hi);
            let r = eval::<I>(Fam::RhoD, &[widen(x, 1e-13), widen(y, 1e-13), z, z]).unwrap()[0];
            assert!(r.lo <= d + 1e-9 && d - 1e-9 <= r.hi);
            let r = eval::<I>(Fam::Alpha, &[widen(d, 1e-13), z, z, z]).unwrap()[0];
            assert!(r.lo <= a + 1e-10 && a - 1e-10 <= r.hi);
            let r = eval::<I>(Fam::AlphaInv, &[widen(a, 1e-13), z, z, z]).unwrap()[0];
            assert!(r.lo <= d + 1e-9 && d - 1e-9 <= r.hi);
        }
    }
}

#[cfg(test)]
mod wheel_tests {
    use super::*;
    use crate::geom::{dist, random_polygon_in, unit, Rng};

    #[test]
    fn random_wheels() {
        let mut rng = Rng(1357);
        let (dlo, dhi) = (0.9365, 0.9892);
        let mut done = 0;
        let mut tries = 0;
        while done < 3000 {
            tries += 1;
            assert!(tries < 2_000_000);
            let d = dlo + (dhi - dlo) * rng.next();
            let amin = (d.cos() / (1.0 + d.cos())).acos();
            let reg = 2.2 + 0.2 * rng.next();
            let (pts, u) = match random_polygon_in(6, d, amin, reg - 0.35, (reg + 0.35).min(std::f64::consts::PI), &mut rng) {
                Some(x) => x,
                None => continue,
            };
            // random interior point: centroid plus a random positive combination of small weight
            let mut p = [0.0; 3];
            let spread = 0.6 * rng.next();
            for q in &pts {
                let w = 1.0 + spread * (rng.next() - 0.5);
                for k in 0..3 {
                    p[k] += w * q[k];
                }
            }
            let p = unit(&p);
            let r: Vec<f64> = pts.iter().map(|q| dist(&p, q)).collect();
            if r.iter().any(|&x| x < d) {
                continue;
            }
            done += 1;
            let e = 1e-12;
            let w = |x: f64| I::new(x - e, x + e);
            let rr = |k: i64| r[k.rem_euclid(6) as usize];
            let z = I::pt(0.0);
            let mut tsum = 0.0;
            for i in 0..6i64 {
                let ui = u[i as usize];
                let c = eval::<I>(Fam::WCorner, &[w(d), w(rr(i - 1)), w(rr(i)), w(rr(i + 1))]).unwrap()[0];
                assert!(c.lo <= ui + 1e-8 && ui - 1e-8 <= c.hi && c.width() < 1e-6, "WCorner {c:?} {ui}");
                let t = eval::<I>(Fam::WTheta, &[w(d), w(rr(i)), w(rr(i + 1)), z]).unwrap()[0];
                let tt = crate::geom::oangle(&p, &pts[i as usize], &pts[((i + 1) % 6) as usize]);
                let tt = tt.min(2.0 * std::f64::consts::PI - tt);
                assert!(t.lo <= tt + 1e-8 && tt - 1e-8 <= t.hi, "WTheta {t:?} {tt}");
                tsum += tt;
                let b = eval::<I>(Fam::WBack, &[w(d), w(rr(i - 1)), w(rr(i)), w(ui)]).unwrap()[0];
                assert!(b.lo <= rr(i + 1) + 1e-8 && rr(i + 1) - 1e-8 <= b.hi && b.width() < 1e-6, "WBack+ {b:?}");
                let b = eval::<I>(Fam::WBack, &[w(d), w(rr(i + 1)), w(rr(i)), w(ui)]).unwrap()[0];
                assert!(b.lo <= rr(i - 1) + 1e-8 && rr(i - 1) - 1e-8 <= b.hi && b.width() < 1e-6, "WBack- {b:?}");
                assert!(rr(i) <= 3.0 * d);
            }
            assert!((tsum - 2.0 * std::f64::consts::PI).abs() < 1e-9);
        }
        eprintln!("wheels {done} tries {tries}");
    }
}
