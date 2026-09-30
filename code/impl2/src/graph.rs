//! Plane graphs from plantri's planar_code (plantri guide, Appendix A: a byte n, then for each
//! vertex 1..n its neighbours in clockwise order followed by 0; an optional 15-byte header
//! ">>planar_code<<"). Faces are traced from the rotation system.
//!
//! Conventions. adj[v] is the rotation at v. Corner (v, j) is the angular sector at v from
//! adj[v][j] to adj[v][j+1] (indices mod deg v), swept in the rotation sense. The face containing
//! corner (v, j) is traced by the rule: after the directed edge u -> v comes v -> w where
//! w = adj[v][pos_v(u) + 1]. A face is stored as its vertex cycle [v_0, .., v_{m-1}] with the
//! directed edges v_i -> v_{i+1}; its corner at v_i is corner (v_i, pos_{v_i}(v_{i-1})).

#[derive(Clone, Debug)]
pub struct Graph {
    pub n: usize,
    pub adj: Vec<Vec<usize>>,
    pub faces: Vec<Vec<usize>>,
    /// corner_face[v][j] = (face index, position of v in the face cycle) of corner (v, j)
    pub corner_face: Vec<Vec<(usize, usize)>>,
}

impl Graph {
    pub fn from_adj(adj: Vec<Vec<usize>>) -> Graph {
        let n = adj.len();
        let pos = |v: usize, u: usize, adj: &Vec<Vec<usize>>| -> usize {
            adj[v].iter().position(|&x| x == u).expect("asymmetric adjacency")
        };
        // directed edge (u, j) = u -> adj[u][j]
        let mut seen: Vec<Vec<bool>> = adj.iter().map(|l| vec![false; l.len()]).collect();
        let mut faces = Vec::new();
        let mut corner_face: Vec<Vec<(usize, usize)>> = adj.iter().map(|l| vec![(usize::MAX, 0); l.len()]).collect();
        for u0 in 0..n {
            for j0 in 0..adj[u0].len() {
                if seen[u0][j0] {
                    continue;
                }
                let mut cyc = Vec::new();
                let (mut u, mut j) = (u0, j0);
                loop {
                    seen[u][j] = true;
                    cyc.push(u);
                    let v = adj[u][j];
                    let pu = pos(v, u, &adj);
                    let jn = (pu + 1) % adj[v].len();
                    u = v;
                    j = jn;
                    if u == u0 && j == j0 {
                        break;
                    }
                    assert!(cyc.len() <= 4 * n, "face tracing does not close");
                }
                let f = faces.len();
                let m = cyc.len();
                for i in 0..m {
                    let v = cyc[i];
                    let prev = cyc[(i + m - 1) % m];
                    let jv = pos(v, prev, &adj);
                    corner_face[v][jv] = (f, i);
                }
                faces.push(cyc);
            }
        }
        for v in 0..n {
            for j in 0..adj[v].len() {
                assert!(corner_face[v][j].0 != usize::MAX);
            }
        }
        Graph { n, adj, faces, corner_face }
    }

    pub fn is_edge(&self, u: usize, v: usize) -> bool {
        self.adj[u].contains(&v)
    }

    pub fn nedges(&self) -> usize {
        self.adj.iter().map(|l| l.len()).sum::<usize>() / 2
    }

    /// Face size counts [triangles, quadrilaterals, pentagons, hexagons].
    pub fn face_counts(&self) -> [usize; 4] {
        let mut c = [0; 4];
        for f in &self.faces {
            if (3..=6).contains(&f.len()) {
                c[f.len() - 3] += 1;
            }
        }
        c
    }

    /// Check the class: degrees 3..5, faces 3..6, Euler characteristic 2, faces are simple cycles.
    pub fn check_class(&self) -> Result<(), String> {
        for v in 0..self.n {
            let d = self.adj[v].len();
            if !(3..=5).contains(&d) {
                return Err(format!("vertex {v} has degree {d}"));
            }
        }
        for (i, f) in self.faces.iter().enumerate() {
            if !(3..=6).contains(&f.len()) {
                return Err(format!("face {i} has size {}", f.len()));
            }
            let mut s = f.clone();
            s.sort();
            s.dedup();
            if s.len() != f.len() {
                return Err(format!("face {i} is not a simple cycle"));
            }
        }
        let e = self.nedges();
        if self.n + self.faces.len() != e + 2 {
            return Err("Euler characteristic is not 2".into());
        }
        Ok(())
    }

    pub fn to_code(&self) -> Vec<u8> {
        let mut out = vec![self.n as u8];
        for v in 0..self.n {
            for &w in &self.adj[v] {
                out.push((w + 1) as u8);
            }
            out.push(0);
        }
        out
    }
}

/// Read all graphs of a planar_code file (one-byte format).
pub fn read_planar_code(bytes: &[u8]) -> Vec<Graph> {
    let mut p = 0;
    let hdr = b">>planar_code<<";
    if bytes.len() >= hdr.len() && &bytes[..hdr.len()] == hdr {
        p = hdr.len();
    }
    let mut out = Vec::new();
    while p < bytes.len() {
        let n = bytes[p] as usize;
        assert!(n > 0, "two-byte planar code not supported");
        p += 1;
        let mut adj = vec![Vec::new(); n];
        for v in 0..n {
            loop {
                let b = bytes[p] as usize;
                p += 1;
                if b == 0 {
                    break;
                }
                assert!(b <= n);
                adj[v].push(b - 1);
            }
        }
        out.push(Graph::from_adj(adj));
    }
    out
}

/// Parse a planar code given in hexadecimal (as printed by tdeep and vkill), without header.
pub fn from_hex(s: &str) -> Graph {
    let b: Vec<u8> = (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect();
    let g = read_planar_code(&b);
    assert_eq!(g.len(), 1);
    g.into_iter().next().unwrap()
}
