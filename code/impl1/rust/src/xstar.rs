//! Inter-face kill test ("star" constraints); exploratory option, not used by the proof.
//!
//! Around a vertex v with faces F_0, ..., F_{k-1} in rotation order and corners c_0, ..., c_{k-1}
//! (sum 2 pi), every vertex a of a face around v has a known direction and distance from v:
//!   a neighbour w_t (first vertex of the corner of F_t): angle P_t = c_0 + ... + c_{t-1}, distance d;
//!   the vertex two steps away in F_t through w_t: angle P_t + beta(u), distance e(u), where u is
//!   the corner of F_t at w_t and (e, beta) the base and base angle of the isosceles triangle with
//!   legs d and apex u (T1; the diagonal lies inside the corner at v since F_t is convex);
//!   the vertex two steps away through w_{t+1}: angle P_t + c_t - beta(u'), distance e(u').
//! For two such vertices a, b lying on faces F_i, F_j (i < j) and sharing no face (so a, b are
//! not adjacent and |ab| >= d), the angle at v between the geodesics va and vb is
//! min(theta, 2 pi - theta) with theta = (angle of b) - (angle of a), and |ab| is the side opposite
//! it (T10). The box is discarded when the upper bound of |ab| is < d. Only a kill test; three-step
//! vertices of hexagons are not used.

use crate::deep::{iso_angle, iso_base, side, Prob};
use crate::graph::Faces;
use crate::iv::{PI_HI, TWO_PI_HI, TWO_PI_LO};
use crate::ivt::Iv;

#[derive(Clone, Debug)]
struct Entry {
    vert: usize,
    face: usize, // index in the rotation order around v
    /// 0: neighbour at the start of the corner; 1: two steps via the start neighbour;
    /// 2: two steps via the end neighbour
    kind: u8,
    mid: usize, // corner variable of the middle vertex (kinds 1, 2)
}

#[derive(Clone, Debug)]
struct Star {
    corners: Vec<usize>, // corner variables around v, rotation order
    pairs: Vec<(Entry, Entry)>,
}

#[derive(Clone, Debug, Default)]
pub struct Stars {
    stars: Vec<Star>,
    pub npairs: usize,
}

impl Stars {
    /// `cvar[f][p]`: variable of the corner of face f at position p (Sys::cvar).
    pub fn new(fc: &Faces, cvar: &[Vec<u32>]) -> Stars {
        let n = fc.at.len();
        let mut on_face = vec![vec![false; fc.nf()]; n];
        for (f, c) in fc.cyc.iter().enumerate() {
            for &x in c {
                on_face[x as usize][f] = true;
            }
        }
        let share = |a: usize, b: usize| (0..fc.nf()).any(|f| on_face[a][f] && on_face[b][f]);
        let mut stars = Vec::with_capacity(n);
        let mut npairs = 0;
        for v in 0..n {
            // corners (f, p) at v chained in rotation order: the corner after (f, p) is the one
            // whose previous vertex is the next vertex of (f, p)
            let at = &fc.at[v];
            if at.is_empty() {
                stars.push(Star { corners: vec![], pairs: vec![] });
                continue;
            }
            let prevnext = |&(f, p): &(u16, u8)| {
                let c = &fc.cyc[f as usize];
                let l = c.len();
                (c[(p as usize + l - 1) % l] as usize, c[(p as usize + 1) % l] as usize)
            };
            let mut order = vec![at[0]];
            while order.len() < at.len() {
                let (_, nx) = prevnext(order.last().unwrap());
                let nxt = *at.iter().find(|c| prevnext(c).0 == nx).expect("rotation chain");
                order.push(nxt);
            }
            let corners: Vec<usize> = order.iter().map(|&(f, p)| cvar[f as usize][p as usize] as usize).collect();
            let mut entries = Vec::new();
            for (t, &(f, p)) in order.iter().enumerate() {
                let c = &fc.cyc[f as usize];
                let l = c.len();
                let p = p as usize;
                let (pv, nx) = (c[(p + l - 1) % l] as usize, c[(p + 1) % l] as usize);
                entries.push(Entry { vert: pv, face: t, kind: 0, mid: 0 });
                if l >= 4 {
                    let pp = c[(p + l - 2) % l] as usize;
                    let nn = c[(p + 2) % l] as usize;
                    let fu = f as usize;
                    entries.push(Entry { vert: pp, face: t, kind: 1, mid: cvar[fu][(p + l - 1) % l] as usize });
                    if nn != pp {
                        entries.push(Entry { vert: nn, face: t, kind: 2, mid: cvar[fu][(p + 1) % l] as usize });
                    } else {
                        // rhombus: the opposite vertex, reachable through either neighbour
                        entries.push(Entry { vert: nn, face: t, kind: 2, mid: cvar[fu][(p + 1) % l] as usize });
                    }
                    let _ = nx;
                }
            }
            let mut pairs = Vec::new();
            for i in 0..entries.len() {
                for j in i + 1..entries.len() {
                    let (a, b) = (&entries[i], &entries[j]);
                    if a.face == b.face || a.vert == b.vert || a.vert == v || b.vert == v || share(a.vert, b.vert) {
                        continue;
                    }
                    pairs.push((a.clone(), b.clone()));
                }
            }
            npairs += pairs.len();
            stars.push(Star { corners, pairs });
        }
        Stars { stars, npairs }
    }

    /// Err when some pair at some vertex is proven closer than d on the box.
    pub fn kill(&self, p: &Prob, b: &[Iv]) -> Result<(), ()> {
        let d = b[p.di];
        let dpt = d;
        for st in &self.stars {
            if st.pairs.is_empty() {
                continue;
            }
            for (a, bb) in &st.pairs {
                // (distance from v, part of the corner of its face after the entry, part before)
                let geo = |e: &Entry| -> (Iv, Iv, Iv) {
                    let c = b[st.corners[e.face]];
                    match e.kind {
                        0 => (dpt, c, Iv::pt(0.0)),
                        1 => {
                            let u = b[e.mid];
                            let be = iso_angle(u, d);
                            (iso_base(u, d), c.sub(be), be)
                        }
                        _ => {
                            let u = b[e.mid];
                            let be = iso_angle(u, d);
                            (iso_base(u, d), be, c.sub(be))
                        }
                    }
                };
                let (ra, rem_a, _) = geo(a);
                let (rb, _, off_b) = geo(bb);
                let mut th = rem_a.add(off_b);
                for t in a.face + 1..bb.face {
                    th = th.add(b[st.corners[t]]);
                }
                // A = min(theta, 2 pi - theta) <= min(theta_hi, 2 pi - theta_lo, pi); true theta lies
                // in [0, 2 pi]. Only the upper bound of A matters for the upper bound of |ab| (side
                // is increasing in A); the lower end is any value below it.
                let (lo, hi) = (th.lo.max(0.0), th.hi.min(TWO_PI_HI));
                if !(lo <= hi) || !(ra.lo <= ra.hi) || !(rb.lo <= rb.hi) {
                    continue;
                }
                let amax = hi.min((TWO_PI_HI - lo).next_up()).min(PI_HI);
                let amin = lo.min(TWO_PI_LO - hi).clamp(0.0, amax);
                let ang = Iv::new(amin, amax);
                if let Ok(s) = side(ra, rb, ang) {
                    if s.hi < d.lo {
                        return Err(());
                    }
                }
            }
        }
        Ok(())
    }
}
