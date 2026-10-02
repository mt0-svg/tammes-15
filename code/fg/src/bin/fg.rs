//! fg: a face-growth generator of the class graphs (3-connected plane graphs with n vertices,
//! degrees 3 to 5, faces of 3 to 6 edges), in the style of the Flyspeck-Tame generator, with
//! hereditary prunes. A prototype, not a verified generator: its output is checked against the
//! plantri route (known-answer tests of README.md), nothing about it is proved.
//!
//! fg ref N OUT [--all] [--sabotage]
//!     reads planar code on stdin (plantri_md5 -p -f6 N), writes the sorted canonical codes of the
//!     class graphs passing W1 (every class graph with --all) to OUT, and prints per largest face
//!     size s the number of classes and the expected number of generator leaves, the sum over the
//!     classes of 2 s f_s / |Aut| (rootings of a largest face modulo automorphisms).
//! fg gen N OUT [--all] [--sabotage] [--ring] [--ring2] [--caps] [--tight] [--hash] [--hist] [--rule R] [--smin A] [--smax B]
//!     runs the generator for the seed sizes s = A..B (default 3..6), writes the sorted canonical
//!     codes of the leaves to OUT and prints the node counts.
//!
//! The generator. A state is a plane graph on the sphere whose faces are either final (faces of
//! the output) or open regions (unions of output faces not yet placed), every face a simple cycle,
//! oriented with its interior on the left of its directed edges. The seed for size s is the final
//! face [0, 1, ..., s-1] and the region [s-1, ..., 1, 0]; all later final faces have at most s
//! edges, so the seed is a largest face of the output. A step picks a region f and a directed edge
//! u -> v of f (the rule below) and branches over every face F of at most s edges that could lie
//! on the left of u -> v inside f: with f rotated to f_0 = v, ..., f_{L-1} = u, the cycle F runs
//! f_0 = f_{i_0}, new vertices, f_{i_1}, new vertices, ..., f_{i_k} = f_{L-1} with
//! 0 = i_0 < i_1 < ... < i_k = L - 1, and closes by u -> v. The rest of f splits into the regions
//! [f_{i_j}, f_{i_j + 1}, ..., f_{i_{j+1}}, new vertices of gap j reversed], dropped when they are a
//! single edge. A chord f_{i_j} f_{i_{j+1}} (no new vertex, i_{j+1} > i_j + 1) must not be an edge
//! already. Completeness (sketch, not proved here): for an output graph G and a rooting of the seed
//! on a largest face of G, the states along the path map into G, each region onto a disc of G
//! bounded by the image cycle; the face of G on the left of the image of u -> v lies in that disc
//! and meets its boundary in the cyclic order of the boundary, so it is one of the branches, and a
//! chord of it is not an edge elsewhere since G is simple. So every rooting gives exactly one leaf.
//!
//! Prunes (each keeps every state that has a completion in the class passing W1):
//! - more than n vertices (vertices are never removed);
//! - a new final face that meets an older final face in two vertices that are not an edge of both,
//!   or in three or more vertices (the face boundaries of a 3-connected plane graph meet in nothing,
//!   a vertex or an edge; final faces never change);
//! - a vertex whose reachable types all fail: its final faces stay, each open corner (a region at
//!   the vertex) becomes at least one face of 3 to s edges, and the degree only grows; so the final
//!   degree m lies in [max(3, d), 5] and the type is the final faces plus m - (d - c) faces of sizes
//!   3..s, with d the degree and c the open corners. Doomed if no such type passes W1 (with --all,
//!   if no such m exists). For c = 0 this is: the vertex is complete and fails W1 or its degree is
//!   outside 3..5.
//! - with --caps, the same test with per-corner bounds (Caps): a face in the corner of x inside a
//!   region of L boundary vertices has at most min(s, L + R) edges, R = n - nv the vertices still to
//!   come, and the region holds at most L - 2 + 2R faces; applied to every open vertex at each node.
//! Not used: a squander bound from the Amin table (README.md, W2g): W2g passes on every class graph
//! with n <= 15, so the bound cannot cut a state that has a completion in the class.
//!
//! Rules for the step: 0 (default) the open vertex with the most final faces (least label on ties),
//! its first region, the edge entering it; 1 the region of least length, then its vertex as in 0.
//! Isomorph rejection: none in the tree by default (as Flyspeck-Tame), one canonical code per leaf;
//! --ring and --ring2 reject, inside the tree, the rootings of the seed that are not of greatest
//! flag sequence (ring_ok, ring2_ok).
//! --sabotage (negative control) also forbids the W1-feasible type (2,2,0,0).
//! --tight does not build the candidates with more than n - nv new vertices (same nodes, fewer
//! candidates).
//! --hash keeps 128-bit hashes of the canonical codes (for n = 15) and writes no code file; the
//! classes of different seed sizes differ (the largest face size is an invariant), so they add.
//! --hist prints, per (remaining vertices, final faces), the nodes with and without a good leaf below.

use std::collections::BTreeSet;
use std::io::{self, BufWriter, Write};
use std::time::Instant;
use tammes_weight_test::graph::{faces, in_class_local, three_connected, vertex_type, Faces, Graph, PcReader, MAXD, MAXN};
use tammes_weight_test::weights::w1_feasible;

const MAXV: usize = 24;
const RMAX: usize = 24;
const MAXF: usize = 40;
const MAXR: usize = 28;

#[derive(Clone)]
struct St {
    nv: usize,
    nfin: usize,
    fin: [[u8; 6]; MAXF],
    finlen: [u8; MAXF],
    finmask: [u32; MAXF],
    nreg: usize,
    reg: [[u8; RMAX]; MAXR],
    reglen: [u8; MAXR],
    adj: [u32; MAXV],
    /// final faces at each vertex by size 3..6
    ft: [[u8; 4]; MAXV],
    /// open corners (regions) at each vertex
    oc: [u8; MAXV],
    /// --ring: the corona of the seed is complete and its sequence is seed_seq
    seed_done: bool,
    seed_seq: [u8; 6],
}

/// Sequence of a flag (start j, direction dir) of a face a of s edges: for k = 0..s-1, the vertex
/// x_k = a[j + dir k] and the edge x_k x_{k+1}, the entry 8 deg(x_k) + size of the other face on
/// that edge. `other(x, y)` gives that size.
fn flag_seq(a: &[u8], j: usize, dir: bool, deg: &dyn Fn(u8) -> u8, other: &dyn Fn(u8, u8) -> u8) -> [u8; 6] {
    let s = a.len();
    let mut q = [0u8; 6];
    for (k, e) in q.iter_mut().enumerate().take(s) {
        let (x, y) = if dir { (a[(j + k) % s], a[(j + k + 1) % s]) } else { (a[(j + s * 2 - k) % s], a[(j + s * 2 - k - 1) % s]) };
        *e = 8 * deg(x) + other(x, y);
    }
    q
}

/// The greatest flag sequence of a face and the number of flags that reach it.
fn max_flag_seq(a: &[u8], deg: &dyn Fn(u8) -> u8, other: &dyn Fn(u8, u8) -> u8) -> ([u8; 6], usize) {
    let mut best = [0u8; 6];
    let mut cnt = 0;
    for j in 0..a.len() {
        for dir in [true, false] {
            let q = flag_seq(a, j, dir, deg, other);
            if q > best {
                best = q;
                cnt = 1;
            } else if q == best {
                cnt += 1;
            }
        }
    }
    (best, cnt)
}

struct Tab {
    /// doomed[s - 3][ft packed base 6][oc]
    doomed: Vec<bool>,
    w1: Vec<bool>,
}

fn pack6(t: [u8; 4]) -> usize {
    ((t[0] as usize * 6 + t[1] as usize) * 6 + t[2] as usize) * 6 + t[3] as usize
}

impl Tab {
    fn new(all: bool, sabotage: bool) -> Tab {
        let mut w1 = vec![false; 1296];
        for a in 0..6u8 {
            for b in 0..6u8 {
                for c in 0..6u8 {
                    for d in 0..6u8 {
                        let m = a + b + c + d;
                        if (3..=5).contains(&m) {
                            let t = [a, b, c, d];
                            let mut ok = all || w1_feasible(t);
                            if sabotage && t == [2, 2, 0, 0] {
                                ok = false;
                            }
                            w1[pack6(t)] = ok;
                        }
                    }
                }
            }
        }
        let mut doomed = vec![true; 4 * 1296 * 6];
        for s in 3..=6usize {
            for a in 0..6u8 {
                for b in 0..6u8 {
                    for c in 0..6u8 {
                        for d in 0..6u8 {
                            let t = [a, b, c, d];
                            let k = (a + b + c + d) as usize;
                            for oc in 0..6usize {
                                let deg = k + oc;
                                let mut ok = false;
                                if oc == 0 {
                                    ok = (3..=5).contains(&deg) && w1[pack6(t)];
                                } else {
                                    for m in deg.max(3)..=5 {
                                        let e = m - k;
                                        // e extra faces of sizes 3..s
                                        for x3 in 0..=e {
                                            for x4 in 0..=e - x3 {
                                                for x5 in 0..=e - x3 - x4 {
                                                    let x6 = e - x3 - x4 - x5;
                                                    if (s < 4 && x4 > 0) || (s < 5 && x5 > 0) || (s < 6 && x6 > 0) {
                                                        continue;
                                                    }
                                                    let u = [a + x3 as u8, b + x4 as u8, c + x5 as u8, d + x6 as u8];
                                                    if u.iter().all(|&z| z < 6) && w1[pack6(u)] {
                                                        ok = true;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                doomed[((s - 3) * 1296 + pack6(t)) * 6 + oc] = !ok;
                            }
                        }
                    }
                }
            }
        }
        Tab { doomed, w1 }
    }
    #[inline]
    fn doomed(&self, s: usize, t: [u8; 4], oc: u8) -> bool {
        if oc >= 6 || t.iter().any(|&z| z >= 6) {
            return true;
        }
        self.doomed[((s - 3) * 1296 + pack6(t)) * 6 + oc as usize]
    }
}

/// --caps: the reachable-type test with per-corner bounds. A face that will fill part of the open
/// corner of x in a region of L boundary vertices uses at most L boundary vertices and at most
/// R = n - nv new ones, so it has at most min(s, L + R) edges; the region holds at most
/// L - 2 + 2R faces (Euler for a disc with R interior vertices, all faces triangles), so the corner
/// gets between 1 and that many faces. Doomed if no multiset of extra faces reachable this way,
/// added to the final faces at x, gives a type with 3 to 5 faces that passes W1.
struct Caps {
    /// multisets (x3, x4, x5, x6) of at most 5 faces, indexed 0..126
    idx: Vec<[u8; 4]>,
    /// ok[ft packed base 6]: the extra multisets x with W1(ft + x) and 3 <= |ft| + |x| <= 5
    ok: Vec<u128>,
    /// single corner (cap K, at most k faces): the reachable multisets
    one: [[u128; 6]; 7],
    memo: std::collections::HashMap<u32, u128>,
}

impl Caps {
    fn new(tab: &Tab) -> Caps {
        let mut idx = Vec::new();
        for a in 0..=5u8 {
            for b in 0..=5 - a {
                for c in 0..=5 - a - b {
                    for d in 0..=5 - a - b - c {
                        idx.push([a, b, c, d]);
                    }
                }
            }
        }
        assert_eq!(idx.len(), 126);
        let mut ok = vec![0u128; 1296];
        for a in 0..6u8 {
            for b in 0..6u8 {
                for c in 0..6u8 {
                    for d in 0..6u8 {
                        let t = [a, b, c, d];
                        let k: u8 = t.iter().sum();
                        let mut m = 0u128;
                        for (i, x) in idx.iter().enumerate() {
                            let u = [a + x[0], b + x[1], c + x[2], d + x[3]];
                            let tot = k + x.iter().sum::<u8>();
                            if (3..=5).contains(&tot) && tab.w1[pack6(u)] {
                                m |= 1 << i;
                            }
                        }
                        ok[pack6(t)] = m;
                    }
                }
            }
        }
        let mut one = [[0u128; 6]; 7];
        for cap in 3..=6usize {
            for kmax in 1..=5usize {
                let mut m = 0u128;
                for (i, x) in idx.iter().enumerate() {
                    let tot: usize = x.iter().map(|&z| z as usize).sum();
                    let fits = (0..4).all(|z| x[z] == 0 || z + 3 <= cap);
                    if tot >= 1 && tot <= kmax && fits {
                        m |= 1 << i;
                    }
                }
                one[cap][kmax] = m;
            }
        }
        Caps { idx, ok, one, memo: std::collections::HashMap::new() }
    }

    fn add(&self, a: u128, b: u128) -> u128 {
        let mut r = 0u128;
        for i in 0..126 {
            if a >> i & 1 == 0 {
                continue;
            }
            for j in 0..126 {
                if b >> j & 1 == 0 {
                    continue;
                }
                let (x, y) = (self.idx[i], self.idx[j]);
                let z = [x[0] + y[0], x[1] + y[1], x[2] + y[2], x[3] + y[3]];
                if z.iter().sum::<u8>() <= 5 {
                    let k = self.idx.iter().position(|w| *w == z).unwrap();
                    r |= 1 << k;
                }
            }
        }
        r
    }

    /// corners: (cap, kmax) per open corner
    fn doomed(&mut self, ft: [u8; 4], corners: &mut [(u8, u8)]) -> bool {
        if corners.len() > 5 || ft.iter().any(|&z| z >= 6) {
            return true;
        }
        if corners.is_empty() {
            return self.ok[pack6(ft)] & 1 == 0; // index 0 is the empty multiset
        }
        corners.sort_unstable();
        let mut key = corners.len() as u32;
        for &(c, k) in corners.iter() {
            key = key * 32 + (c as u32 - 3) * 8 + k as u32;
        }
        let reach = if let Some(&r) = self.memo.get(&key) {
            r
        } else {
            let mut r = self.one[corners[0].0 as usize][corners[0].1 as usize];
            for &(c, k) in &corners[1..] {
                r = self.add(r, self.one[c as usize][k as usize]);
            }
            self.memo.insert(key, r);
            r
        };
        reach & self.ok[pack6(ft)] == 0
    }
}

#[derive(Default, Clone)]
struct Stats {
    nodes: u64,
    cands: u64,
    rej_nv: u64,
    rej_meet: u64,
    rej_doom: u64,
    rej_ring: u64,
    rej_caps: u64,
    /// --hist: (remaining vertices, final faces) -> [dead nodes, useful nodes]
    hist: Vec<[u64; 2]>,
    /// nodes with an ok leaf in their subtree (or ok leaves themselves)
    useful: u64,
    leaves: u64,
    leaves_short: u64,
    leaves_not3c: u64,
    leaves_ok: u64,
    w1_recheck_fail: u64,
    max_reg_len: usize,
    max_nreg: usize,
}

struct Gen<'a> {
    n: usize,
    s: usize,
    rule: u8,
    ring: bool,
    ring2: bool,
    caps: Option<Caps>,
    hist: bool,
    tight: bool,
    tab: &'a Tab,
    st: Stats,
    codes: BTreeSet<Vec<u8>>,
    /// --hash: 128-bit hashes of the canonical codes instead of the codes (large n, no code file)
    hash_only: bool,
    hashes: std::collections::HashSet<u128>,
}

fn popc(x: u32) -> u32 {
    x.count_ones()
}

impl<'a> Gen<'a> {
    fn seed(&self) -> St {
        let s = self.s;
        let mut st = St {
            nv: s,
            nfin: 1,
            fin: [[0; 6]; MAXF],
            finlen: [0; MAXF],
            finmask: [0; MAXF],
            nreg: 1,
            reg: [[0; RMAX]; MAXR],
            reglen: [0; MAXR],
            adj: [0; MAXV],
            ft: [[0; 4]; MAXV],
            oc: [0; MAXV],
            seed_done: false,
            seed_seq: [0; 6],
        };
        for i in 0..s {
            st.fin[0][i] = i as u8;
            st.reg[0][i] = (s - 1 - i) as u8;
            st.finmask[0] |= 1 << i;
            let j = (i + 1) % s;
            st.adj[i] |= 1 << j;
            st.adj[j] |= 1 << i;
            st.ft[i][s - 3] = 1;
            st.oc[i] = 1;
        }
        st.finlen[0] = s as u8;
        st.reglen[0] = s as u8;
        st
    }

    /// (region, position of v in it)
    fn pick(&self, st: &St) -> (usize, usize) {
        let score = |v: usize| -> i32 { st.ft[v].iter().map(|&z| z as i32).sum() };
        match self.rule {
            0 => {
                let mut best = usize::MAX;
                let mut bs = -1;
                for v in 0..st.nv {
                    if st.oc[v] > 0 && score(v) > bs {
                        bs = score(v);
                        best = v;
                    }
                }
                for r in 0..st.nreg {
                    for p in 0..st.reglen[r] as usize {
                        if st.reg[r][p] as usize == best {
                            return (r, p);
                        }
                    }
                }
                unreachable!()
            }
            _ => {
                let mut rbest = 0;
                for r in 1..st.nreg {
                    if st.reglen[r] < st.reglen[rbest] {
                        rbest = r;
                    }
                }
                let mut pbest = 0;
                let mut bs = -1;
                for p in 0..st.reglen[rbest] as usize {
                    let v = st.reg[rbest][p] as usize;
                    if score(v) > bs || (score(v) == bs && v < st.reg[rbest][pbest] as usize) {
                        bs = score(v);
                        pbest = p;
                    }
                }
                (rbest, pbest)
            }
        }
    }

    fn run(&mut self) {
        let st = self.seed();
        self.st.nodes += 1;
        if self.expand(&st) {
            self.st.useful += 1;
        }
    }

    fn expand(&mut self, st: &St) -> bool {
        let (ri, p0) = self.pick(st);
        let l = st.reglen[ri] as usize;
        let mut f = [0u8; RMAX];
        for i in 0..l {
            f[i] = st.reg[ri][(p0 + i) % l];
        }
        let mut b = [0usize; 8];
        let mut r = [0usize; 8];
        b[0] = 0;
        self.gen_face(st, ri, &f, l, &mut b, &mut r, 1, 1)
    }

    /// b[0..nb] boundary indices so far, r[j] new vertices after b[j]; size = F vertices so far
    #[allow(clippy::too_many_arguments)]
    fn gen_face(&mut self, st: &St, ri: usize, f: &[u8; RMAX], l: usize, b: &mut [usize; 8], r: &mut [usize; 8], nb: usize, size: usize) -> bool {
        let s = self.s;
        let p = b[nb - 1];
        let mut any = false;
        // room: the next gap takes nr new vertices and one boundary vertex
        if size + 1 > s {
            return false;
        }
        // --tight: no more new vertices than n - nv (the candidates rejected for that are not built)
        let top = if self.tight { (s - size - 1).min(self.n - st.nv - (size - nb)) } else { s - size - 1 };
        for nr in 0..=top {
            for q in p + 1..l {
                if nr == 0 && q > p + 1 && st.adj[f[p] as usize] & (1 << f[q]) != 0 {
                    continue;
                }
                let nsize = size + nr + 1;
                r[nb - 1] = nr;
                b[nb] = q;
                if q == l - 1 {
                    if nsize >= 3 {
                        any |= self.child(st, ri, f, l, b, r, nb + 1);
                    }
                } else if nsize < s {
                    any |= self.gen_face(st, ri, f, l, b, r, nb + 1, nsize);
                }
            }
        }
        any
    }

    #[allow(clippy::too_many_arguments)]
    fn child(&mut self, st: &St, ri: usize, f: &[u8; RMAX], l: usize, b: &[usize; 8], r: &[usize; 8], nb: usize) -> bool {
        self.st.cands += 1;
        let newv: usize = r[..nb - 1].iter().sum();
        if st.nv + newv > self.n {
            self.st.rej_nv += 1;
            return false;
        }
        // the face F
        let mut face = [0u8; 6];
        let mut fl = 0;
        let mut next = st.nv as u8;
        for j in 0..nb {
            face[fl] = f[b[j]];
            fl += 1;
            if j + 1 < nb {
                for _ in 0..r[j] {
                    face[fl] = next;
                    next += 1;
                    fl += 1;
                }
            }
        }
        let mut fmask = 0u32;
        for &x in &face[..fl] {
            fmask |= 1 << x;
        }
        // meeting rule with the older final faces
        for g in 0..st.nfin {
            let c = fmask & st.finmask[g];
            let k = popc(c);
            if k >= 3 {
                self.st.rej_meet += 1;
                return false;
            }
            if k == 2 {
                let x = c.trailing_zeros() as u8;
                let y = (c & (c - 1)).trailing_zeros() as u8;
                let cons = |a: &[u8]| -> bool {
                    let m = a.len();
                    (0..m).any(|i| {
                        let (u, w) = (a[i], a[(i + 1) % m]);
                        (u == x && w == y) || (u == y && w == x)
                    })
                };
                if !(cons(&face[..fl]) && cons(&st.fin[g][..st.finlen[g] as usize])) {
                    self.st.rej_meet += 1;
                    return false;
                }
            }
        }
        let mut c = st.clone();
        c.nv = st.nv + newv;
        // remove region ri
        for i in 0..l {
            c.oc[f[i] as usize] -= 1;
        }
        let last = c.nreg - 1;
        if ri != last {
            c.reg[ri] = c.reg[last];
            c.reglen[ri] = c.reglen[last];
        }
        c.nreg -= 1;
        // add F
        let gi = c.nfin;
        assert!(gi < MAXF);
        c.fin[gi] = face;
        c.finlen[gi] = fl as u8;
        c.finmask[gi] = fmask;
        c.nfin += 1;
        for i in 0..fl {
            let x = face[i] as usize;
            let y = face[(i + 1) % fl] as usize;
            c.adj[x] |= 1 << y;
            c.adj[y] |= 1 << x;
            c.ft[x][fl - 3] += 1;
        }
        // pieces
        let mut pos = 0; // position in face of f[b[j]]
        for j in 0..nb - 1 {
            let (a, z) = (b[j], b[j + 1]);
            let nr = r[j];
            if !(z == a + 1 && nr == 0) {
                let plen = z - a + 1 + nr;
                assert!(plen <= RMAX && c.nreg < MAXR, "region too long or too many regions");
                let ri2 = c.nreg;
                let mut k = 0;
                for i in a..=z {
                    c.reg[ri2][k] = f[i];
                    k += 1;
                }
                for t in (0..nr).rev() {
                    c.reg[ri2][k] = face[pos + 1 + t];
                    k += 1;
                }
                c.reglen[ri2] = plen as u8;
                for i in 0..plen {
                    c.oc[c.reg[ri2][i] as usize] += 1;
                }
                c.nreg += 1;
                self.st.max_reg_len = self.st.max_reg_len.max(plen);
            }
            pos += 1 + nr;
        }
        self.st.max_nreg = self.st.max_nreg.max(c.nreg);
        for &x in &face[..fl] {
            let x = x as usize;
            debug_assert_eq!(popc(c.adj[x]) as u8, c.ft[x].iter().sum::<u8>() + c.oc[x]);
            if self.tab.doomed(self.s, c.ft[x], c.oc[x]) {
                self.st.rej_doom += 1;
                return false;
            }
        }
        if self.caps.is_some() && !self.caps_ok(&c) {
            self.st.rej_caps += 1;
            return false;
        }
        if self.ring2 && !self.ring2_ok(&c, fmask) {
            self.st.rej_ring += 1;
            return false;
        }
        if self.ring && !self.ring_ok(&mut c, fmask) {
            self.st.rej_ring += 1;
            return false;
        }
        self.st.nodes += 1;
        let u = if c.nreg == 0 { self.leaf(&c) } else { self.expand(&c) };
        if self.hist {
            if self.st.hist.is_empty() {
                self.st.hist = vec![[0; 2]; 32 * MAXF];
            }
            self.st.hist[(self.n - c.nv) * MAXF + c.nfin][u as usize] += 1;
        }
        if u {
            self.st.useful += 1;
        }
        u
    }

    /// --caps on every open vertex (the complete ones are decided by `doomed`).
    fn caps_ok(&mut self, c: &St) -> bool {
        let r = self.n - c.nv;
        let mut cor = [[(0u8, 0u8); 6]; MAXV];
        let mut nc = [0usize; MAXV];
        for g in 0..c.nreg {
            let l = c.reglen[g] as usize;
            let cap = (l + r).min(self.s) as u8;
            let kmax = (l + 2 * r - 2).min(5) as u8;
            for i in 0..l {
                let x = c.reg[g][i] as usize;
                if nc[x] >= 6 {
                    return false;
                }
                cor[x][nc[x]] = (cap, kmax);
                nc[x] += 1;
            }
        }
        let caps = self.caps.as_mut().unwrap();
        for x in 0..c.nv {
            if nc[x] > 0 && caps.doomed(c.ft[x], &mut cor[x][..nc[x]]) {
                return false;
            }
        }
        true
    }

    /// --ring, a partial isomorph rejection. A face is complete when all its vertices are (no open
    /// corner), and then its flag sequences (flag_seq) are final. The rooting of the seed must give
    /// the greatest flag sequence among all flags of all faces of s edges (ties allowed): checked
    /// for the seed's own flags when its corona completes, then against every other face of s
    /// edges when both are complete. Sound: the rooting on a face and flag of greatest sequence
    /// survives every check, so each class keeps a leaf; at a leaf every face is complete, so
    /// exactly the rootings of greatest sequence survive (the expected_ring count of fg ref).
    fn ring_ok(&self, c: &mut St, fmask: u32) -> bool {
        let s = self.s;
        let mut open = 0u32;
        for v in 0..c.nv {
            if c.oc[v] > 0 {
                open |= 1 << v;
            }
        }
        let cc: &St = c;
        let deg = |x: u8| popc(cc.adj[x as usize]) as u8;
        let other_of = |g: usize| {
            move |x: u8, y: u8| -> u8 {
                for h in 0..cc.nfin {
                    if h == g || cc.finmask[h] & (1 << x) == 0 || cc.finmask[h] & (1 << y) == 0 {
                        continue;
                    }
                    let a = &cc.fin[h][..cc.finlen[h] as usize];
                    let m = a.len();
                    if (0..m).any(|i| (a[i] == x && a[(i + 1) % m] == y) || (a[i] == y && a[(i + 1) % m] == x)) {
                        return m as u8;
                    }
                }
                panic!("no face across a complete edge")
            }
        };
        let newly = fmask & !open;
        let (done, seq0) = if !cc.seed_done {
            if cc.finmask[0] & open != 0 {
                return true;
            }
            let a = &cc.fin[0][..s];
            let q0 = flag_seq(a, 0, true, &deg, &other_of(0));
            if max_flag_seq(a, &deg, &other_of(0)).0 > q0 {
                return false;
            }
            (false, q0)
        } else {
            (true, cc.seed_seq)
        };
        for g in 1..cc.nfin {
            if cc.finlen[g] as usize != s || cc.finmask[g] & open != 0 {
                continue;
            }
            if done && cc.finmask[g] & newly == 0 {
                continue;
            }
            let a = &cc.fin[g][..s];
            if max_flag_seq(a, &deg, &other_of(g)).0 > seq0 {
                return false;
            }
        }
        if !done {
            c.seed_done = true;
            c.seed_seq = seq0;
        }
        true
    }

    /// --ring2, the same rejection decided earlier. The k-th entry of a flag sequence is final as
    /// soon as its vertex x_k is complete (its degree and the faces around it are final). Each time
    /// a vertex completes, every flag of every final face of s edges is compared with the seed flag
    /// (0, +) entry by entry while both entries are final: a first difference in favour of the other
    /// flag prunes. The flag of greatest sequence never loses such a comparison, and at a leaf all
    /// entries are final, so the surviving leaves are those of --ring.
    fn ring2_ok(&self, c: &St, fmask: u32) -> bool {
        let s = self.s;
        let mut open = 0u32;
        for v in 0..c.nv {
            if c.oc[v] > 0 {
                open |= 1 << v;
            }
        }
        if fmask & !open == 0 {
            return true;
        }
        let other = |g: usize, x: u8, y: u8| -> u8 {
            for h in 0..c.nfin {
                if h == g || c.finmask[h] & (1 << x) == 0 || c.finmask[h] & (1 << y) == 0 {
                    continue;
                }
                let a = &c.fin[h][..c.finlen[h] as usize];
                let m = a.len();
                if (0..m).any(|i| (a[i] == x && a[(i + 1) % m] == y) || (a[i] == y && a[(i + 1) % m] == x)) {
                    return m as u8;
                }
            }
            panic!("no face across an edge at a complete vertex")
        };
        let entry = |g: usize, x: u8, y: u8| -> u8 { 8 * popc(c.adj[x as usize]) as u8 + other(g, x, y) };
        // seed entries, 255 while unknown
        let mut e0 = [255u8; 6];
        for (k, e) in e0.iter_mut().enumerate().take(s) {
            if open & (1 << k) == 0 {
                *e = entry(0, k as u8, ((k + 1) % s) as u8);
            }
        }
        for g in 0..c.nfin {
            if c.finlen[g] as usize != s {
                continue;
            }
            let a = &c.fin[g][..s];
            for j in 0..s {
                for dir in [true, false] {
                    if g == 0 && j == 0 && dir {
                        continue;
                    }
                    for k in 0..s {
                        let (x, y) = if dir { (a[(j + k) % s], a[(j + k + 1) % s]) } else { (a[(j + 2 * s - k) % s], a[(j + 2 * s - k - 1) % s]) };
                        if open & (1 << x) != 0 || e0[k] == 255 {
                            break;
                        }
                        let ea = entry(g, x, y);
                        if ea > e0[k] {
                            return false;
                        }
                        if ea < e0[k] {
                            break;
                        }
                    }
                }
            }
        }
        true
    }

    fn leaf(&mut self, c: &St) -> bool {
        self.st.leaves += 1;
        if c.nv != self.n {
            self.st.leaves_short += 1;
            return false;
        }
        let g = to_graph(c);
        if !three_connected(&g) {
            self.st.leaves_not3c += 1;
            return false;
        }
        let mut fc = Faces::new();
        assert!(faces(&g, &mut fc) && in_class_local(&g, &fc), "leaf outside the class");
        for v in 0..g.n {
            let t = vertex_type(&g, &fc, v);
            if !self.tab.w1[pack6(t)] {
                self.st.w1_recheck_fail += 1;
            }
        }
        self.st.leaves_ok += 1;
        let code = canon_aut(&g).0;
        if self.hash_only {
            self.hashes.insert(hash128(&code));
        } else {
            self.codes.insert(code);
        }
        true
    }
}

/// The rotation system of a leaf (every face final).
fn to_graph(c: &St) -> Graph {
    let n = c.nv;
    let mut nxt = [[255u8; MAXV]; MAXV];
    for g in 0..c.nfin {
        let m = c.finlen[g] as usize;
        let a = &c.fin[g];
        for i in 0..m {
            let (u, x, w) = (a[(i + m - 1) % m], a[i], a[(i + 1) % m]);
            assert_eq!(nxt[x as usize][u as usize], 255, "corner twice");
            nxt[x as usize][u as usize] = w;
        }
    }
    let mut g = Graph::empty();
    g.n = n;
    for x in 0..n {
        let d = popc(c.adj[x]) as usize;
        assert!(d <= MAXD && n <= MAXN);
        let w0 = c.adj[x].trailing_zeros() as u8;
        let mut w = w0;
        let mut k = 0;
        loop {
            g.adj[x][k] = w;
            k += 1;
            w = nxt[x][w as usize];
            assert!(w != 255 && k <= d, "rotation broken");
            if w == w0 {
                break;
            }
        }
        assert_eq!(k, d, "rotation is not one cycle");
        g.deg[x] = d as u8;
    }
    g
}

/// Canonical code up to isomorphism and reflection (the construction of graph::canon) and the
/// number of flags (dart, orientation) that reach it, which is |Aut| with reflections.
fn canon_aut(g: &Graph) -> (Vec<u8>, usize) {
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
    let mut ties = 0;
    let mut code = Vec::with_capacity(8 * n);
    for v0 in 0..n {
        for j0 in 0..g.deg[v0] as usize {
            for dir in [1i32, -1] {
                let mut num = [255u8; MAXN];
                let mut first = [0u8; MAXN];
                let mut order = [0usize; MAXN];
                let mut len = 1;
                num[v0] = 0;
                first[v0] = j0 as u8;
                order[0] = v0;
                code.clear();
                let mut head = 0;
                while head < len {
                    let v = order[head];
                    head += 1;
                    let d = g.deg[v] as i32;
                    for s in 0..d {
                        let j = ((first[v] as i32 + dir * s).rem_euclid(d)) as usize;
                        let w = g.adj[v][j] as usize;
                        if num[w] == 255 {
                            num[w] = len as u8;
                            first[w] = pos[v][j];
                            order[len] = w;
                            len += 1;
                        }
                        code.push(num[w]);
                    }
                    code.push(254);
                }
                match &best {
                    Some(b) if code > *b => {}
                    Some(b) if code == *b => ties += 1,
                    _ => {
                        best = Some(code.clone());
                        ties = 1;
                    }
                }
            }
        }
    }
    (best.unwrap_or_default(), ties)
}

/// Faces of a rotation system as vertex cycles, all traced with the same orientation, and the
/// face of each dart.
fn face_lists(g: &Graph) -> (Vec<Vec<u8>>, [[u8; MAXN]; MAXN]) {
    let n = g.n;
    let mut dface = [[255u8; MAXN]; MAXN];
    let mut fl = Vec::new();
    for v in 0..n {
        for j in 0..g.deg[v] as usize {
            let w = g.adj[v][j] as usize;
            if dface[v][w] != 255 {
                continue;
            }
            let id = fl.len() as u8;
            let mut cyc = Vec::new();
            let (mut a, mut b) = (v, w);
            while dface[a][b] == 255 {
                dface[a][b] = id;
                cyc.push(a as u8);
                let i = (0..g.deg[b] as usize).find(|&i| g.adj[b][i] as usize == a).unwrap();
                let c = g.adj[b][(i + 1) % g.deg[b] as usize] as usize;
                a = b;
                b = c;
            }
            fl.push(cyc);
        }
    }
    (fl, dface)
}

/// Number of rootings of a largest face (face, start, direction) whose flag sequence is the
/// greatest over all faces of s edges: the rootings that survive --ring.
fn ring_rootings(g: &Graph, s: usize) -> usize {
    let (fl, dface) = face_lists(g);
    let deg = |x: u8| g.deg[x as usize];
    let mut best = [0u8; 6];
    let mut cnt = 0;
    for (id, a) in fl.iter().enumerate() {
        if a.len() != s {
            continue;
        }
        let other = |x: u8, y: u8| -> u8 {
            let (x, y) = (x as usize, y as usize);
            let h = if dface[x][y] as usize == id { dface[y][x] } else { dface[x][y] };
            fl[h as usize].len() as u8
        };
        let (q, c) = max_flag_seq(a, &deg, &other);
        if q > best {
            best = q;
            cnt = c;
        } else if q == best {
            cnt += c;
        }
    }
    cnt
}

/// Two multiplicative (FNV-style) byte hashes with different offsets and multipliers, as one
/// 128-bit value.
fn hash128(c: &[u8]) -> u128 {
    let (mut a, mut b) = (0xcbf29ce484222325u64, 0x84222325cbf29ce4u64);
    for &x in c {
        a = (a ^ x as u64).wrapping_mul(0x100000001b3);
        b = (b ^ x as u64).wrapping_mul(0x1000193_00000001);
    }
    (a as u128) << 64 | b as u128
}

fn hex(c: &[u8]) -> String {
    c.iter().map(|b| format!("{b:02x}")).collect()
}

fn write_codes(path: &str, codes: &BTreeSet<Vec<u8>>) -> io::Result<()> {
    let mut w = BufWriter::new(std::fs::File::create(path)?);
    for c in codes {
        writeln!(w, "{}", hex(c))?;
    }
    w.flush()
}

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: fg ref N OUT [--all] [--sabotage] | fg gen N OUT [--all] [--sabotage] [--ring] [--ring2] [--caps] [--tight] [--hash] [--hist] [--rule R] [--smin A] [--smax B]");
        std::process::exit(2);
    }
    let n: usize = args[2].parse().unwrap();
    let out = &args[3];
    let mut all = false;
    let mut sabotage = false;
    let mut rule = 0u8;
    let mut ring = false;
    let mut ring2 = false;
    let mut use_caps = false;
    let mut hist = false;
    let mut tight = false;
    let mut hash_only = false;
    let mut smin = 3;
    let mut smax = 6;
    let mut i = 4;
    while i < args.len() {
        match args[i].as_str() {
            "--all" => all = true,
            "--sabotage" => sabotage = true,
            "--ring" => ring = true,
            "--ring2" => ring2 = true,
            "--caps" => use_caps = true,
            "--hist" => hist = true,
            "--tight" => tight = true,
            "--hash" => hash_only = true,
            "--rule" => {
                rule = args[i + 1].parse().unwrap();
                i += 1;
            }
            "--smin" => {
                smin = args[i + 1].parse().unwrap();
                i += 1;
            }
            "--smax" => {
                smax = args[i + 1].parse().unwrap();
                i += 1;
            }
            a => panic!("unknown option {a}"),
        }
        i += 1;
    }
    let tab = Tab::new(all, sabotage);
    let so = io::stdout();
    let mut o = so.lock();
    let t0 = Instant::now();
    match args[1].as_str() {
        "ref" => {
            let stdin = io::stdin();
            let mut rd = PcReader::new(stdin.lock())?;
            let mut g = Graph::empty();
            let mut fc = Faces::new();
            let mut codes = BTreeSet::new();
            let (mut read, mut class) = (0u64, 0u64);
            let mut per_s = [0u64; 7];
            let mut expect = [0u64; 7];
            let mut expect_ring = [0u64; 7];
            while rd.next(&mut g)? {
                read += 1;
                if g.n != n || !faces(&g, &mut fc) || !in_class_local(&g, &fc) {
                    continue;
                }
                class += 1;
                if !(0..g.n).all(|v| tab.w1[pack6(vertex_type(&g, &fc, v))]) {
                    continue;
                }
                let (code, aut) = canon_aut(&g);
                let s = (0..fc.nf).map(|f| fc.size[f] as usize).max().unwrap();
                let fs = (0..fc.nf).filter(|&f| fc.size[f] as usize == s).count();
                assert_eq!((2 * s * fs) % aut, 0, "rootings not a multiple of |Aut|");
                per_s[s] += 1;
                expect[s] += (2 * s * fs / aut) as u64;
                let rr = ring_rootings(&g, s);
                assert_eq!(rr % aut, 0, "ring rootings not a multiple of |Aut|");
                expect_ring[s] += (rr / aut) as u64;
                assert!(codes.insert(code), "two isomorphic graphs in the input");
            }
            write_codes(out, &codes)?;
            for s in 3..=6 {
                writeln!(o, "fg ref n {n} s {s} classes {} expected_leaves {} expected_ring {}", per_s[s], expect[s], expect_ring[s])?;
            }
            writeln!(
                o,
                "fg ref n {n} all {} sabotage {} read {read} class {class} kept {} expected_leaves {} expected_ring {} secs {:.2}",
                all as u8,
                sabotage as u8,
                codes.len(),
                expect.iter().sum::<u64>(),
                expect_ring.iter().sum::<u64>(),
                t0.elapsed().as_secs_f64()
            )?;
        }
        "gen" => {
            let mut codes = BTreeSet::new();
            let mut tot = Stats::default();
            let mut nhash = 0usize;
            for s in smin..=smax {
                let t1 = Instant::now();
                let caps = if use_caps { Some(Caps::new(&tab)) } else { None };
                let mut gen = Gen { n, s, rule, ring, ring2, caps, hist, tight, tab: &tab, st: Stats::default(), codes: BTreeSet::new(), hash_only, hashes: std::collections::HashSet::new() };
                gen.run();
                let st = &gen.st;
                writeln!(
                    o,
                    "fg gen n {n} s {s} rule {rule} ring {}{}{}{} nodes {} cands {} rej_nv {} rej_meet {} rej_doom {} rej_caps {} rej_ring {} useful {} leaves {} short {} not3c {} ok {} classes {} w1_recheck_fail {} max_reg_len {} max_nreg {} secs {:.2}",
                    ring as u8, if ring2 { " ring2" } else { "" }, if use_caps { " caps" } else { "" }, if tight { " tight" } else { "" }, st.nodes, st.cands, st.rej_nv, st.rej_meet, st.rej_doom, st.rej_caps, st.rej_ring, st.useful, st.leaves, st.leaves_short, st.leaves_not3c, st.leaves_ok,
                    gen.codes.len() + gen.hashes.len(), st.w1_recheck_fail, st.max_reg_len, st.max_nreg, t1.elapsed().as_secs_f64()
                )?;
                for (i, h) in st.hist.iter().enumerate() {
                    if h[0] + h[1] > 0 {
                        writeln!(o, "fg hist n {n} s {s} remaining_vertices {} final_faces {} dead {} useful {}", i / MAXF, i % MAXF, h[0], h[1])?;
                    }
                }
                o.flush()?;
                tot.nodes += st.nodes;
                tot.cands += st.cands;
                tot.useful += st.useful;
                tot.leaves += st.leaves;
                tot.leaves_ok += st.leaves_ok;
                tot.w1_recheck_fail += st.w1_recheck_fail;
                for c in gen.codes {
                    codes.insert(c);
                }
                nhash += gen.hashes.len();
            }
            if !hash_only {
                write_codes(out, &codes)?;
            }
            writeln!(
                o,
                "fg gen n {n} all {} sabotage {} rule {rule} ring {}{}{}{} s {smin}..{smax} nodes {} cands {} useful {} leaves {} ok {} classes {} w1_recheck_fail {} secs {:.2}",
                all as u8,
                sabotage as u8,
                ring as u8,
                if ring2 { " ring2" } else { "" },
                if use_caps { " caps" } else { "" },
                if tight { " tight" } else { "" },
                tot.nodes,
                tot.cands,
                tot.useful,
                tot.leaves,
                tot.leaves_ok,
                codes.len() + nhash,
                tot.w1_recheck_fail,
                t0.elapsed().as_secs_f64()
            )?;
        }
        _ => {
            eprintln!("unknown command");
            std::process::exit(2);
        }
    }
    Ok(())
}
