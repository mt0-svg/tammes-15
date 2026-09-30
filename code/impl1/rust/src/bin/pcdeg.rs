//! Sanity check of the max-degree-5 plantri filter (code/impl1/enum/plantri_md5.c).
//! usage: plantri -p -f6 N | pcdeg
//! Reads planar_code (one-byte format, with or without header) from stdin as a stream and prints
//! the number of graphs, the number with maximum degree <= 5, and the number with every vertex
//! degree in 3..5 and every face of size 3..6 (faces traced from the rotation system).
//! Standalone reader, it shares no code with tfilter or with code/impl2.
use std::io::Read;

/// Reads stdin in large blocks and hands out single bytes.
struct Input {
    buf: Vec<u8>,
    pos: usize,
    len: usize,
    stdin: std::io::Stdin,
}

impl Input {
    fn next(&mut self) -> Option<u8> {
        if self.pos == self.len {
            self.len = self.stdin.lock().read(&mut self.buf).expect("read stdin");
            self.pos = 0;
            if self.len == 0 {
                return None;
            }
        }
        self.pos += 1;
        Some(self.buf[self.pos - 1])
    }
}

fn main() {
    let mut inp = Input { buf: vec![0; 1 << 22], pos: 0, len: 0, stdin: std::io::stdin() };
    let hdr = b">>planar_code<<";
    let mut first = inp.next();
    if first == Some(b'>') {
        for &h in &hdr[1..] {
            assert_eq!(inp.next(), Some(h), "bad header");
        }
        first = inp.next();
    }
    let (mut total, mut md5, mut class) = (0u64, 0u64, 0u64);
    let mut adj: Vec<Vec<usize>> = Vec::new();
    let mut seen: Vec<Vec<bool>> = Vec::new();
    let mut nb = first;
    while let Some(b) = nb {
        let n = b as usize;
        if adj.len() < n {
            adj.resize(n, Vec::new());
            seen.resize(n, Vec::new());
        }
        for a in adj.iter_mut().take(n) {
            a.clear();
            loop {
                let w = inp.next().expect("truncated graph") as usize;
                if w == 0 {
                    break;
                }
                a.push(w - 1);
            }
        }
        nb = inp.next();
        let adj = &adj[..n];
        total += 1;
        let maxdeg = adj.iter().map(|a| a.len()).max().unwrap_or(0);
        if maxdeg <= 5 {
            md5 += 1;
        }
        // The class needs every degree in 3..5, so the faces are traced only then.
        if !adj.iter().all(|a| (3..=5).contains(&a.len())) {
            continue;
        }
        // Faces: the directed edge (v, w) is followed by (w, x) where x is the successor of v
        // in the cyclic order at w. Every directed edge lies in exactly one face.
        for (s, a) in seen.iter_mut().zip(adj) {
            s.clear();
            s.resize(a.len(), false);
        }
        let mut ok = true;
        let mut nfaces = 0usize;
        let nedges: usize = adj.iter().map(|a| a.len()).sum::<usize>() / 2;
        for v0 in 0..n {
            for j0 in 0..adj[v0].len() {
                if seen[v0][j0] {
                    continue;
                }
                nfaces += 1;
                let (mut v, mut j, mut len) = (v0, j0, 0usize);
                while !seen[v][j] {
                    seen[v][j] = true;
                    len += 1;
                    let w = adj[v][j];
                    let i = adj[w].iter().position(|&x| x == v).expect("symmetric adjacency");
                    let jn = (i + 1) % adj[w].len();
                    v = w;
                    j = jn;
                }
                if !(3..=6).contains(&len) {
                    ok = false;
                }
            }
        }
        if n + nfaces != nedges + 2 {
            ok = false;
        }
        if ok {
            class += 1;
        }
    }
    println!("graphs {total} maxdeg<=5 {md5} class(deg 3..5, faces 3..6, Euler 2) {class}");
}
