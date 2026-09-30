//! Faces and corners of a plane graph given by rotation lists.
//!
//! Face tracing: the directed edge u->v is followed by v->w where w is the successor of u in the
//! rotation of v. Every directed edge lies on exactly one face. A corner is a pair (vertex, face)
//! where the face boundary passes through the vertex; in a 3-connected plane graph each face
//! passes at most once through a vertex, so corners of v correspond to the faces around v.

use crate::pcode::Rot;

#[derive(Clone, Debug, Default)]
pub struct Faces {
    /// Vertex cycles of the faces, in tracing order.
    pub cyc: Vec<Vec<u8>>,
    /// For each vertex, the list of (face, position of the vertex in that face's cycle).
    pub at: Vec<Vec<(u16, u8)>>,
    pub ne: usize,
}

impl Faces {
    pub fn compute(g: &Rot, out: &mut Faces) {
        let n = g.n;
        out.cyc.clear();
        out.at.clear();
        out.at.resize(n, Vec::new());
        // edge id: (u, i) -> offset[u] + i
        let mut off = [0usize; 257];
        for v in 0..n {
            off[v + 1] = off[v] + g.adj[v].len();
        }
        let m2 = off[n];
        out.ne = m2 / 2;
        let mut seen = vec![false; m2];
        for u0 in 0..n {
            for i0 in 0..g.adj[u0].len() {
                if seen[off[u0] + i0] {
                    continue;
                }
                let f = out.cyc.len() as u16;
                let mut cyc = Vec::with_capacity(6);
                let (mut u, mut i) = (u0, i0);
                loop {
                    seen[off[u] + i] = true;
                    let pos = cyc.len() as u8;
                    cyc.push(u as u8);
                    out.at[u].push((f, pos));
                    let v = g.adj[u][i] as usize;
                    let av = &g.adj[v];
                    let j = av.iter().position(|&x| x as usize == u).expect("asymmetric adjacency");
                    let j2 = (j + 1) % av.len();
                    u = v;
                    i = j2;
                    if u == u0 && i == i0 {
                        break;
                    }
                }
                out.cyc.push(cyc);
            }
        }
    }

    pub fn nf(&self) -> usize {
        self.cyc.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cube_faces() {
        // cube: vertices 0..8, rotation lists from a planar drawing
        // outer square 0-1-2-3, inner square 4-5-6-7, i joined to i+4
        let adj: Vec<Vec<u8>> = vec![
            vec![1, 4, 3],
            vec![2, 5, 0],
            vec![3, 6, 1],
            vec![0, 7, 2],
            vec![0, 5, 7],
            vec![1, 6, 4],
            vec![2, 7, 5],
            vec![3, 4, 6],
        ];
        let g = Rot { n: 8, adj };
        let mut f = Faces::default();
        Faces::compute(&g, &mut f);
        assert_eq!(f.ne, 12);
        assert_eq!(f.nf(), 6);
        assert!(f.cyc.iter().all(|c| c.len() == 4));
        assert!(f.at.iter().all(|a| a.len() == 3));
    }
}

/// Canonical code of a connected plane graph up to orientation-preserving and reversing
/// isomorphism: lexicographic minimum over all start darts and both orientations of the BFS code
/// (neighbours listed in rotation order starting from the discovering edge, 0 as separator).
/// For 3-connected planar graphs (unique embedding up to reflection, Whitney) equal codes mean
/// isomorphic graphs.
pub fn canon(g: &Rot) -> Vec<u8> {
    let n = g.n;
    let mut best: Option<Vec<u8>> = None;
    let mut num = vec![0u8; n];
    let mut refn = vec![0usize; n]; // reference neighbour position
    let mut order = Vec::with_capacity(n);
    for u0 in 0..n {
        for i0 in 0..g.adj[u0].len() {
            for &dir in &[1isize, -1] {
                num.iter_mut().for_each(|x| *x = 0);
                order.clear();
                num[u0] = 1;
                refn[u0] = i0;
                order.push(u0);
                let mut next = 2u8;
                let mut code = Vec::with_capacity(2 * n + 4 * n);
                let mut qi = 0;
                let mut worse = false;
                while qi < order.len() {
                    let v = order[qi];
                    qi += 1;
                    let d = g.adj[v].len() as isize;
                    for s in 0..d {
                        let idx = (refn[v] as isize + dir * s).rem_euclid(d) as usize;
                        let w = g.adj[v][idx] as usize;
                        if num[w] == 0 {
                            num[w] = next;
                            next += 1;
                            refn[w] = g.adj[w].iter().position(|&x| x as usize == v).unwrap();
                            order.push(w);
                        }
                        code.push(num[w]);
                    }
                    code.push(0);
                    if let Some(b) = &best {
                        let l = code.len();
                        if code[..] > b[..l.min(b.len())] {
                            worse = true;
                            break;
                        }
                    }
                }
                if worse {
                    continue;
                }
                if best.as_ref().map_or(true, |b| code < *b) {
                    best = Some(code);
                }
            }
        }
    }
    let mut out = vec![n as u8];
    out.extend(best.unwrap_or_default());
    out
}
