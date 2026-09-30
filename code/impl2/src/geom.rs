//! Plain floating-point geometry for the soundness tests (not used by any discard).

pub type P = [f64; 3];

pub fn dot(a: &P, b: &P) -> f64 {
    a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
}
pub fn cross(a: &P, b: &P) -> P {
    [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
}
pub fn norm(a: &P) -> f64 {
    dot(a, a).sqrt()
}
pub fn unit(a: &P) -> P {
    let n = norm(a);
    [a[0] / n, a[1] / n, a[2] / n]
}
pub fn sub(a: &P, b: &P) -> P {
    [a[0] - b[0], a[1] - b[1], a[2] - b[2]]
}
/// Angular distance.
pub fn dist(a: &P, b: &P) -> f64 {
    let c = cross(a, b);
    norm(&c).atan2(dot(a, b))
}
/// Unit tangent at p toward q.
pub fn tangent(p: &P, q: &P) -> P {
    let c = dot(p, q);
    unit(&[q[0] - c * p[0], q[1] - c * p[1], q[2] - c * p[2]])
}
/// Oriented angle at p from direction toward a to direction toward b, counterclockwise about
/// the outward normal p, in [0, 2 pi).
pub fn oangle(p: &P, a: &P, b: &P) -> f64 {
    let ta = tangent(p, a);
    let tb = tangent(p, b);
    let s = dot(p, &cross(&ta, &tb));
    let c = dot(&ta, &tb);
    let t = s.atan2(c);
    if t < 0.0 {
        t + 2.0 * std::f64::consts::PI
    } else {
        t
    }
}
/// Point at distance t from p in the direction at oriented angle phi from the tangent toward a.
pub fn walk(p: &P, a: &P, phi: f64, t: f64) -> P {
    let e1 = tangent(p, a);
    let e2 = cross(p, &e1);
    let dir = [
        phi.cos() * e1[0] + phi.sin() * e2[0],
        phi.cos() * e1[1] + phi.sin() * e2[1],
        phi.cos() * e1[2] + phi.sin() * e2[2],
    ];
    [
        t.cos() * p[0] + t.sin() * dir[0],
        t.cos() * p[1] + t.sin() * dir[1],
        t.cos() * p[2] + t.sin() * dir[2],
    ]
}

pub struct Rng(pub u64);
impl Rng {
    pub fn next(&mut self) -> f64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 >> 11) as f64 / (1u64 << 53) as f64
    }
}

/// A random convex equilateral spherical m-gon of side d (m = 5 or 6): the chain A_0 .. A_{m-1}
/// with corners u_1 .. u_{m-3} random and u_{m-2} solved by bisection so that |A_{m-1} A_0| = d.
/// Returns (vertices, corners) with the corners measured from the coordinates, or None if the
/// polygon is not convex with corners in [amin, pi].
pub fn random_polygon(m: usize, d: f64, amin: f64, rng: &mut Rng) -> Option<(Vec<P>, Vec<f64>)> {
    random_polygon_in(m, d, amin, amin, std::f64::consts::PI, rng)
}

/// Same, with the free corners sampled in [slo, shi].
pub fn random_polygon_in(m: usize, d: f64, amin: f64, slo: f64, shi: f64, rng: &mut Rng) -> Option<(Vec<P>, Vec<f64>)> {
    let pi = std::f64::consts::PI;
    let mut u = vec![0.0; m];
    for k in 1..m - 2 {
        u[k] = slo + (shi - slo) * rng.next();
    }
    let build = |last: f64, u: &Vec<f64>| -> Vec<P> {
        let a0 = [0.0, 0.0, 1.0];
        let a1 = [d.sin(), 0.0, d.cos()];
        let mut pts = vec![a0, a1];
        for k in 1..m - 1 {
            let corner = if k == m - 2 { last } else { u[k] };
            // at A_k, the corner is swept from A_{k-1} to A_{k+1}; turn so the polygon is on the left
            let p = pts[k];
            let prev = pts[k - 1];
            let q = walk(&p, &prev, 2.0 * pi - corner, d);
            pts.push(q);
        }
        pts
    };
    let f = |last: f64| -> f64 {
        let pts = build(last, &u);
        dist(&pts[m - 1], &pts[0]) - d
    };
    // scan for a sign change
    let n = 200;
    let mut prev_x = amin;
    let mut prev_f = f(amin);
    let mut roots = Vec::new();
    for s in 1..=n {
        let x = amin + (pi - amin) * s as f64 / n as f64;
        let fx = f(x);
        if prev_f.signum() != fx.signum() {
            let (mut lo, mut hi) = (prev_x, x);
            let flo = prev_f;
            for _ in 0..200 {
                let mid = 0.5 * (lo + hi);
                if (f(mid) > 0.0) == (flo > 0.0) {
                    lo = mid;
                } else {
                    hi = mid;
                }
            }
            roots.push(0.5 * (lo + hi));
        }
        prev_x = x;
        prev_f = fx;
    }
    for last in roots {
        if let Some(r) = check_polygon(build(last, &u), m, d, amin) {
            return Some(r);
        }
    }
    None
}

fn check_polygon(pts: Vec<P>, m: usize, d: f64, amin: f64) -> Option<(Vec<P>, Vec<f64>)> {
    let pi = std::f64::consts::PI;
    // measured corners: at A_k from A_{k-1} to A_{k+1}, clockwise sweep = 2 pi - oangle
    let mut cs = vec![0.0; m];
    for k in 0..m {
        let p = pts[k];
        let a = pts[(k + m - 1) % m];
        let b = pts[(k + 1) % m];
        cs[k] = 2.0 * pi - oangle(&p, &a, &b);
        if cs[k] >= 2.0 * pi {
            cs[k] -= 2.0 * pi;
        }
    }
    for k in 0..m {
        if !(cs[k] >= amin && cs[k] <= pi) {
            return None;
        }
    }
    // equal sides and non-adjacent pairs >= d
    for i in 0..m {
        for j in i + 1..m {
            let dd = dist(&pts[i], &pts[j]);
            let adj = j == i + 1 || (i == 0 && j == m - 1);
            if adj && (dd - d).abs() > 1e-9 {
                return None;
            }
            if !adj && dd < d {
                return None;
            }
        }
    }
    // angle sum must exceed (m - 2) pi (positive area) and the polygon must be simple: check the
    // polygon lies on the left of every side great circle (convexity)
    let (mut npos, mut nneg) = (0, 0);
    for i in 0..m {
        let a = pts[i];
        let b = pts[(i + 1) % m];
        let nrm = cross(&a, &b);
        for k in 0..m {
            if k != i && k != (i + 1) % m {
                let s = dot(&nrm, &pts[k]);
                if s > 1e-12 {
                    npos += 1;
                }
                if s < -1e-12 {
                    nneg += 1;
                }
            }
        }
    }
    if npos > 0 && nneg > 0 {
        return None;
    }
    Some((pts, cs))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn debug_hex() {
        let mut rng = Rng(5);
        let d: f64 = 0.95;
        let amin = (d.cos() / (1.0 + d.cos())).acos();
        let mut ok = 0;
        for _ in 0..200 {
            if let Some((pts, u)) = random_polygon_in(6, d, amin, 1.95, 2.65, &mut rng) {
                ok += 1;
                if ok < 3 {
                    let mut p = [0.0; 3];
                    for q in &pts { for k in 0..3 { p[k] += q[k]; } }
                    let p = unit(&p);
                    let r: Vec<f64> = pts.iter().map(|q| dist(&p, q)).collect();
                    eprintln!("u {:?} r {:?}", u, r);
                }
            }
        }
        eprintln!("ok {ok} of 200");
    }
}
