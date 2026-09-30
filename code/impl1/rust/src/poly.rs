//! Equilateral spherical polygons (floating point): construction from d and m-3 angles.
//!
//! Vertices A_0..A_{m-1} counterclockwise seen from outside the sphere, interior on the left;
//! see `build` for the parametrisation. Floating point only: numerical exploration and candidate
//! face inequalities, never a proof.

pub type V3 = [f64; 3];

#[inline]
pub fn dot(a: &V3, b: &V3) -> f64 {
    a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
}
#[inline]
pub fn cross(a: &V3, b: &V3) -> V3 {
    [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
}
#[inline]
pub fn scale(a: &V3, s: f64) -> V3 {
    [a[0] * s, a[1] * s, a[2] * s]
}
#[inline]
pub fn add(a: &V3, b: &V3) -> V3 {
    [a[0] + b[0], a[1] + b[1], a[2] + b[2]]
}
#[inline]
pub fn sub(a: &V3, b: &V3) -> V3 {
    [a[0] - b[0], a[1] - b[1], a[2] - b[2]]
}
#[inline]
pub fn norm(a: &V3) -> V3 {
    let r = dot(a, a).sqrt();
    scale(a, 1.0 / r)
}
pub fn dist(a: &V3, b: &V3) -> f64 {
    // atan2 form, accurate for all distances
    let c = cross(a, b);
    dot(&c, &c).sqrt().atan2(dot(a, b))
}
/// unit tangent at p pointing to q
pub fn tangent(p: &V3, q: &V3) -> V3 {
    norm(&sub(q, &scale(p, dot(p, q))))
}
/// point at distance d from p in tangent direction t
pub fn walk(p: &V3, t: &V3, d: f64) -> V3 {
    add(&scale(p, d.cos()), &scale(t, d.sin()))
}
/// rotate tangent vector t at p by angle th counterclockwise (seen from outside)
pub fn rot(p: &V3, t: &V3, th: f64) -> V3 {
    let n = cross(p, t);
    add(&scale(t, th.cos()), &scale(&n, th.sin()))
}
/// signed angle at p from direction of q to direction of r, counterclockwise, in (-pi, pi]
pub fn angle_at(p: &V3, q: &V3, r: &V3) -> f64 {
    let tq = tangent(p, q);
    let tr = tangent(p, r);
    dot(p, &cross(&tq, &tr)).atan2(dot(&tq, &tr))
}

/// alpha(d): angle of the equilateral spherical triangle with side d
pub fn alpha(d: f64) -> f64 {
    (d.cos() / (1.0 + d.cos())).acos()
}

/// Builds an equilateral polygon with m vertices, side d, from the m-3 angles
/// u_1, ..., u_{m-3} at A_1, ..., A_{m-3}, starting with A_0, A_1 fixed.
/// Walk: A_{k+1} = walk from A_k turning by the interior angle u_k (interior on the left).
/// The last two vertices: A_{m-1} is at distance d from A_0 and from A_{m-2} (two candidates,
/// the one making the polygon counterclockwise is chosen). Returns vertices and all m interior
/// angles, or None if no such point exists.
pub fn build(m: usize, d: f64, u: &[f64]) -> Option<(Vec<V3>, Vec<f64>)> {
    assert_eq!(u.len(), m - 3);
    let a0: V3 = [0.0, 0.0, 1.0];
    let a1: V3 = [d.sin(), 0.0, d.cos()];
    let mut v = vec![a0, a1];
    for k in 1..=m - 3 {
        let p = v[k];
        let back = tangent(&p, &v[k - 1]);
        // interior on the left when walking A_{k-1} -> A_k -> A_{k+1}: the direction to A_{k+1}
        // is the direction back to A_{k-1} rotated clockwise by u_k
        let t = rot(&p, &back, -u[k - 1]);
        v.push(walk(&p, &t, d));
    }
    // A_{m-1}: at distance d from A_{m-2} and A_0
    let p = v[m - 2];
    let q = a0;
    let c = d.cos();
    // x = alpha p + beta q + gamma (p x q), x.p = c, x.q = c, |x| = 1
    let pq = dot(&p, &q);
    let den = 1.0 - pq * pq;
    if den < 1e-14 {
        return None;
    }
    let al = c * (1.0 - pq) / den;
    let be = al;
    let n = cross(&p, &q);
    let base = add(&scale(&p, al), &scale(&q, be));
    let rem = 1.0 - dot(&base, &base);
    if rem < 0.0 {
        return None;
    }
    let g = (rem / den).sqrt(); // |n|^2 = den
    let cand = [add(&base, &scale(&n, g)), add(&base, &scale(&n, -g))];
    let mut best: Option<(Vec<V3>, Vec<f64>)> = None;
    for x in cand.iter() {
        let mut w = v.clone();
        w.push(*x);
        let ang: Vec<f64> = (0..m).map(|i| angle_at(&w[i], &w[(i + 1) % m], &w[(i + m - 1) % m])).collect();
        // interior angle at A_i measured counterclockwise from next to previous
        if ang.iter().all(|&t| t > 0.0) {
            let s: f64 = ang.iter().sum();
            if s > (m as f64 - 2.0) * std::f64::consts::PI {
                best = Some((w, ang));
            }
        }
    }
    best
}

/// Validity for a face of an irreducible contact graph: every angle in [alpha(d), pi), all
/// non-adjacent vertex distances >= d.
pub fn valid_face(d: f64, vs: &[V3], ang: &[f64], slack: f64) -> bool {
    let m = vs.len();
    let al = alpha(d);
    if ang.iter().any(|&t| t < al - slack || t >= std::f64::consts::PI) {
        return false;
    }
    for i in 0..m {
        for j in i + 2..m {
            if i == 0 && j == m - 1 {
                continue;
            }
            if dist(&vs[i], &vs[j]) < d - slack {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn regular_pentagon() {
        // regular spherical pentagon with side d: angle u with cos(d) from the triangle formula
        let d = 0.95f64;
        // find u by bisection such that build closes symmetrically: u_1 = u_2 = u
        let mut lo = 1.5;
        let mut hi = 3.1;
        for _ in 0..100 {
            let mid = 0.5 * (lo + hi);
            let (_, ang) = build(5, d, &[mid, mid]).unwrap();
            if ang[3] > mid {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        let (vs, ang) = build(5, d, &[lo, lo]).unwrap();
        for t in &ang {
            assert!((t - lo).abs() < 1e-9, "{ang:?}");
        }
        for i in 0..5 {
            assert!((dist(&vs[i], &vs[(i + 1) % 5]) - d).abs() < 1e-12);
        }
    }
}
