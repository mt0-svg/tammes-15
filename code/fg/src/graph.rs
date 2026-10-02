//! Plane graphs in planar code (the output format of plantri): reading, faces, the class test and
//! the vertex types.
//!
//! Planar code: the header ">>planar_code<<" once, then for each graph the number n of vertices
//! (one byte, n < 256) and, for each vertex 1..n, its neighbours in cyclic order followed by 0.

use std::io::{self, Read};

pub const MAXN: usize = 32;
pub const MAXD: usize = 16;

#[derive(Clone)]
pub struct Graph {
    pub n: usize,
    pub deg: [u8; MAXN],
    /// neighbours in cyclic order, 0-based
    pub adj: [[u8; MAXD]; MAXN],
}

impl Graph {
    pub fn empty() -> Graph {
        Graph { n: 0, deg: [0; MAXN], adj: [[0; MAXD]; MAXN] }
    }
    pub fn edges(&self) -> usize {
        (0..self.n).map(|v| self.deg[v] as usize).sum::<usize>() / 2
    }
}

/// Buffered reader of a planar code stream.
pub struct PcReader<R: Read> {
    inner: R,
    buf: Vec<u8>,
    pos: usize,
    len: usize,
    eof: bool,
}

impl<R: Read> PcReader<R> {
    pub fn new(inner: R) -> io::Result<PcReader<R>> {
        let mut r = PcReader { inner, buf: vec![0; 1 << 22], pos: 0, len: 0, eof: false };
        let mut hdr = [0u8; 15];
        for b in hdr.iter_mut() {
            match r.byte()? {
                Some(x) => *b = x,
                None => {
                    if r.len == 0 {
                        return Ok(r); // empty stream: no graphs
                    }
                    return Err(io::Error::new(io::ErrorKind::InvalidData, "short header"));
                }
            }
        }
        if &hdr != b">>planar_code<<" {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "not planar code"));
        }
        Ok(r)
    }
    #[inline]
    fn byte(&mut self) -> io::Result<Option<u8>> {
        if self.pos == self.len {
            if self.eof {
                return Ok(None);
            }
            self.len = 0;
            self.pos = 0;
            while self.len < self.buf.len() {
                let k = self.inner.read(&mut self.buf[self.len..])?;
                if k == 0 {
                    self.eof = true;
                    break;
                }
                self.len += k;
                if self.len >= 1 << 16 {
                    break;
                }
            }
            if self.len == 0 {
                return Ok(None);
            }
        }
        let b = self.buf[self.pos];
        self.pos += 1;
        Ok(Some(b))
    }
    /// Reads the next graph into g; false at the end of the stream.
    pub fn next(&mut self, g: &mut Graph) -> io::Result<bool> {
        let n = match self.byte()? {
            None => return Ok(false),
            Some(0) => return Err(io::Error::new(io::ErrorKind::InvalidData, "n = 0 (two-byte codes unsupported)")),
            Some(n) => n as usize,
        };
        if n > MAXN {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "n too large"));
        }
        g.n = n;
        for v in 0..n {
            let mut k = 0;
            loop {
                let b = self.byte()?.ok_or_else(|| io::Error::new(io::ErrorKind::UnexpectedEof, "truncated graph"))?;
                if b == 0 {
                    break;
                }
                if k >= MAXD || b as usize > n {
                    return Err(io::Error::new(io::ErrorKind::InvalidData, "bad neighbour or degree"));
                }
                g.adj[v][k] = b - 1;
                k += 1;
            }
            g.deg[v] = k as u8;
        }
        Ok(true)
    }
}

/// Faces of a graph with its rotation system: face of each dart and face sizes.
/// Dart (v, j) is v -> adj[v][j]. The face walk is (u -> v) followed by (v -> w), w the neighbour
/// after u in the cyclic order at v. The corner at v between adj[v][j - 1] and adj[v][j] belongs to
/// the face of the dart (v, j).
pub struct Faces {
    pub nf: usize,
    pub face: [[u8; MAXD]; MAXN],
    pub size: [u8; 2 * MAXN * 3],
    /// vertex set of each face as a bit mask
    pub verts: [u32; 2 * MAXN * 3],
    pub ok: bool,
}

impl Faces {
    pub fn new() -> Faces {
        Faces { nf: 0, face: [[0; MAXD]; MAXN], size: [0; 2 * MAXN * 3], verts: [0; 2 * MAXN * 3], ok: false }
    }
}

/// Computes the faces. Returns false if the rotation system is inconsistent (a neighbour list
/// that is not symmetric) or some face repeats a vertex.
pub fn faces(g: &Graph, fc: &mut Faces) -> bool {
    let n = g.n;
    // pos[v][j] = index of v in adj[w], w = adj[v][j]
    let mut pos = [[0u8; MAXD]; MAXN];
    for v in 0..n {
        for j in 0..g.deg[v] as usize {
            let w = g.adj[v][j] as usize;
            let mut found = false;
            for i in 0..g.deg[w] as usize {
                if g.adj[w][i] as usize == v {
                    pos[v][j] = i as u8;
                    found = true;
                    break;
                }
            }
            if !found {
                fc.ok = false;
                return false;
            }
        }
    }
    const UNSET: u8 = 255;
    for v in 0..n {
        for j in 0..g.deg[v] as usize {
            fc.face[v][j] = UNSET;
        }
    }
    let mut nf = 0usize;
    for v0 in 0..n {
        for j0 in 0..g.deg[v0] as usize {
            if fc.face[v0][j0] != UNSET {
                continue;
            }
            // walk the face starting with dart (v0, j0)
            let (mut v, mut j) = (v0, j0);
            let mut sz = 0u8;
            let mut vm = 0u32;
            let mut repeat = false;
            loop {
                fc.face[v][j] = nf as u8;
                if vm & (1 << v) != 0 {
                    repeat = true;
                }
                vm |= 1 << v;
                sz += 1;
                let w = g.adj[v][j] as usize;
                let i = pos[v][j] as usize; // index of v in adj[w]
                let jn = (i + 1) % g.deg[w] as usize;
                v = w;
                j = jn;
                if v == v0 && j == j0 {
                    break;
                }
                if sz as usize > 2 * MAXN * 3 {
                    fc.ok = false;
                    return false;
                }
            }
            fc.size[nf] = sz;
            fc.verts[nf] = vm;
            nf += 1;
            if repeat {
                fc.nf = nf;
                fc.ok = false;
                return false;
            }
        }
    }
    fc.nf = nf;
    fc.ok = true;
    true
}

/// The class of Section 5.1 up to 3-connectivity (which plantri -p guarantees; checked separately
/// by `three_connected` where stated): degrees 3 to 5, faces bounded by cycles of 3 to 6 edges,
/// Euler's relation n - E + F = 2.
pub fn in_class_local(g: &Graph, fc: &Faces) -> bool {
    if !fc.ok {
        return false;
    }
    for v in 0..g.n {
        if g.deg[v] < 3 || g.deg[v] > 5 {
            return false;
        }
    }
    for f in 0..fc.nf {
        if fc.size[f] < 3 || fc.size[f] > 6 {
            return false;
        }
    }
    g.n + fc.nf == g.edges() + 2
}

/// 3-connectivity by deleting every pair of vertices (for small checks only).
pub fn three_connected(g: &Graph) -> bool {
    let n = g.n;
    if n < 4 {
        return false;
    }
    for a in 0..n {
        for b in a + 1..n {
            let removed = (1u32 << a) | (1u32 << b);
            let start = (0..n).find(|&v| removed & (1 << v) == 0).unwrap();
            let mut seen = removed | (1 << start);
            let mut stack = vec![start];
            while let Some(v) = stack.pop() {
                for j in 0..g.deg[v] as usize {
                    let w = g.adj[v][j] as usize;
                    if seen & (1 << w) == 0 {
                        seen |= 1 << w;
                        stack.push(w);
                    }
                }
            }
            if seen != (if n == 32 { u32::MAX } else { (1u32 << n) - 1 }) {
                return false;
            }
        }
    }
    true
}

/// Vertex type: the numbers of incident faces of sizes 3, 4, 5, 6.
#[inline]
pub fn vertex_type(g: &Graph, fc: &Faces, v: usize) -> [u8; 4] {
    let mut t = [0u8; 4];
    for j in 0..g.deg[v] as usize {
        let s = fc.size[fc.face[v][j] as usize];
        t[(s - 3) as usize] += 1;
    }
    t
}

/// Index of a vertex type (t, q, p5, p6) with t + q + p5 + p6 = m in {3, 4, 5}: 0..111.
pub fn type_index(t: [u8; 4]) -> usize {
    let mut idx = 0;
    for (i, c) in all_types().iter().enumerate() {
        if *c == t {
            idx = i;
            return idx;
        }
    }
    panic!("vertex type out of range {:?} {}", t, idx);
}

/// All vertex types of degree 3, 4, 5, in a fixed order.
pub fn all_types() -> Vec<[u8; 4]> {
    let mut v = Vec::new();
    for m in 3u8..=5 {
        for a in 0..=m {
            for b in 0..=m - a {
                for c in 0..=m - a - b {
                    v.push([a, b, c, m - a - b - c]);
                }
            }
        }
    }
    v
}

/// Lookup table from a packed type (t | q << 3 | p5 << 6 | p6 << 9) to its index.
pub fn type_table() -> Vec<u8> {
    let mut tab = vec![255u8; 1 << 12];
    for (i, t) in all_types().iter().enumerate() {
        tab[pack(*t)] = i as u8;
    }
    tab
}
#[inline]
pub fn pack(t: [u8; 4]) -> usize {
    t[0] as usize | (t[1] as usize) << 3 | (t[2] as usize) << 6 | (t[3] as usize) << 9
}

/// Writes a graph in planar code (without the header).
pub fn write_pc(g: &Graph, out: &mut Vec<u8>) {
    out.push(g.n as u8);
    for v in 0..g.n {
        for j in 0..g.deg[v] as usize {
            out.push(g.adj[v][j] + 1);
        }
        out.push(0);
    }
}

/// Canonical code of an embedded graph up to isomorphism and reflection: the least, over every
/// starting dart and both orientations, of the BFS code (vertices numbered in order of discovery,
/// each vertex listing its neighbours' numbers in rotation order from the dart it was reached by).
pub fn canon(g: &Graph) -> Vec<u8> {
    let n = g.n;
    let mut pos = [[0u8; MAXD]; MAXN];
    for v in 0..n {
        for j in 0..g.deg[v] as usize {
            let w = g.adj[v][j] as usize;
            for i in 0..g.deg[w] as usize {
                if g.adj[w][i] as usize == v {
                    pos[v][j] = i as u8;
                }
            }
        }
    }
    let mut best: Option<Vec<u8>> = None;
    for v0 in 0..n {
        for j0 in 0..g.deg[v0] as usize {
            for dir in [1i32, -1] {
                let mut num = [255u8; MAXN];
                let mut first = [0u8; MAXN]; // index of the entering dart at each vertex
                let mut order = Vec::with_capacity(n);
                num[v0] = 0;
                first[v0] = j0 as u8;
                order.push(v0);
                let mut code = Vec::with_capacity(3 * n * 2);
                let mut head = 0;
                while head < order.len() {
                    let v = order[head];
                    head += 1;
                    let d = g.deg[v] as i32;
                    for s in 0..d {
                        let j = ((first[v] as i32 + dir * s).rem_euclid(d)) as usize;
                        let w = g.adj[v][j] as usize;
                        if num[w] == 255 {
                            num[w] = order.len() as u8;
                            first[w] = pos[v][j];
                            order.push(w);
                        }
                        code.push(num[w]);
                    }
                    code.push(254);
                }
                if best.as_ref().map_or(true, |b| code < *b) {
                    best = Some(code);
                }
            }
        }
    }
    best.unwrap_or_default()
}
