//! Streaming reader and writer for plantri's planar_code format (one-byte version, n <= 255).
//!
//! Format: header ">>planar_code<<" (15 bytes, optionally followed by "le<<"/"be<<" only for the
//! two-byte variant, which is not supported), then per graph: n, and for each vertex 1..n the
//! 1-based neighbours in clockwise order terminated by 0.

use std::io::{self, BufRead, Write};

pub const HEADER: &[u8] = b">>planar_code<<";

pub struct Reader<R: BufRead> {
    r: R,
    started: bool,
}

/// A plane graph given by rotation lists (clockwise), 0-based vertices.
#[derive(Clone, Debug, Default)]
pub struct Rot {
    pub n: usize,
    pub adj: Vec<Vec<u8>>,
}

impl<R: BufRead> Reader<R> {
    pub fn new(r: R) -> Self {
        Reader { r, started: false }
    }

    fn byte(&mut self) -> io::Result<Option<u8>> {
        let mut b = [0u8; 1];
        match self.r.read(&mut b)? {
            0 => Ok(None),
            _ => Ok(Some(b[0])),
        }
    }

    /// Reads the next graph into `g`; returns false at end of input.
    pub fn next_into(&mut self, g: &mut Rot) -> io::Result<bool> {
        if !self.started {
            let mut h = [0u8; 15];
            match self.r.read_exact(&mut h) {
                Ok(()) => {}
                Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(false),
                Err(e) => return Err(e),
            }
            if &h[..] != HEADER {
                return Err(io::Error::new(io::ErrorKind::InvalidData, "not planar_code"));
            }
            self.started = true;
        }
        let n = match self.byte()? {
            None => return Ok(false),
            Some(0) => {
                return Err(io::Error::new(io::ErrorKind::InvalidData, "two-byte planar_code unsupported"))
            }
            Some(n) => n as usize,
        };
        g.n = n;
        if g.adj.len() < n {
            g.adj.resize(n, Vec::new());
        }
        g.adj.truncate(n);
        for v in 0..n {
            let list = &mut g.adj[v];
            list.clear();
            loop {
                let mut b = [0u8; 1];
                self.r.read_exact(&mut b)?;
                if b[0] == 0 {
                    break;
                }
                list.push(b[0] - 1);
            }
        }
        Ok(true)
    }
}

pub fn write_header<W: Write>(w: &mut W) -> io::Result<()> {
    w.write_all(HEADER)
}

pub fn write_graph<W: Write>(w: &mut W, g: &Rot) -> io::Result<()> {
    let mut buf = Vec::with_capacity(1 + g.n + g.adj.iter().map(|a| a.len()).sum::<usize>());
    buf.push(g.n as u8);
    for v in 0..g.n {
        for &u in &g.adj[v] {
            buf.push(u + 1);
        }
        buf.push(0);
    }
    w.write_all(&buf)
}
