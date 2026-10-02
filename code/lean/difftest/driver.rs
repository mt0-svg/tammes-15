//! Driver of the differential test of Prims.lean against the program.
//! A child module of deep.rs (setup.sh appends it), so that it calls the private functions of
//! deep.rs themselves.
//!
//! Usage: difftest N [PRIM...]   N cases per primitive (all primitives when none is named).
//!
//! For each case it writes, on stdout, the inputs, the log of the arithmetic the program performed
//! (one line per distinct call), and the program's result:
//!
//!   P piLo piHi twoPiLo twoPiHi        once, the constants of iv.rs
//!   C prim id                           a case
//!   I tokens                            its inputs
//!   O op a0 a1 a2 a3 r0 r1              a call of operation op (dtlog::OP_NAMES) and its result
//!   R tag tokens                        the result
//!   E
//!   S prim cases conflicts flips tag:count ...    at the end, per primitive
//!
//! A float is written as the 16 hex digits of its bits, made canonical (-0 as 0, every NaN as
//! 7ff8000000000000): the Lean model identifies the two zeros and has one NaN. A call of an
//! operation is logged once per case; a second call with the same canonical arguments and another
//! canonical result is a conflict (the operation would not be a function on the values the Lean
//! model reads). Each logged call with a zero or NaN argument is evaluated again with the signs of
//! its zeros flipped and its NaNs replaced by other NaNs; a different canonical result is a flip.

use super::*;
use crate::dtlog::{self, Entry};
use crate::iv::{cmax, cmin, PI_HI, PI_LO, TWO_PI_HI, TWO_PI_LO};
use crate::ivt::Iv;
use crate::system::{fbbt, Fbbt, Sys};
use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::{BufWriter, Write};

const NAN_BITS: u64 = 0x7ff8_0000_0000_0000;

fn canon(x: f64) -> u64 {
    if x.is_nan() {
        NAN_BITS
    } else if x == 0.0 {
        0
    } else {
        x.to_bits()
    }
}

fn hx(s: &mut String, x: f64) {
    write!(s, " {:016x}", canon(x)).unwrap();
}

fn hiv(s: &mut String, v: Iv) {
    hx(s, v.lo);
    hx(s, v.hi);
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn unif(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn range(&mut self, a: f64, b: f64) -> f64 {
        a + (b - a) * self.unif()
    }
}

/// The ranges of the realistic values of an argument.
#[derive(Clone, Copy)]
enum Kind {
    /// a corner or an angle, (0, pi]
    Angle,
    /// the distance d
    D,
    /// a side or a distance r
    Side,
    /// anything
    Gen,
}

impl Kind {
    fn range(self) -> (f64, f64) {
        match self {
            Kind::Angle => (0.05, 3.3),
            Kind::D => (0.85, 1.0),
            Kind::Side => (0.4, 3.0),
            Kind::Gen => (-3.0, 7.0),
        }
    }
}

struct Gen {
    rng: Rng,
    special: Vec<f64>,
    special_fin: Vec<f64>,
}

impl Gen {
    fn new(seed: u64) -> Gen {
        let base = [
            0.0,
            -0.0,
            1.0,
            -1.0,
            0.5,
            2.0,
            3.0,
            PI_LO,
            PI_HI,
            std::f64::consts::PI,
            std::f64::consts::FRAC_PI_2,
            PI_LO * 0.5,
            PI_HI * 0.5,
            TWO_PI_LO,
            TWO_PI_HI,
            2.0 * PI_LO,
            std::f64::consts::FRAC_PI_3,
            0.936_495_6,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
            f64::MAX,
            -f64::MAX,
            f64::MIN_POSITIVE,
            5e-324,
            -5e-324,
            1e-300,
            1e300,
        ];
        let mut special = Vec::new();
        for x in base {
            special.push(x);
            if x.is_finite() {
                special.push(x.next_up());
                special.push(x.next_down());
            }
        }
        let special_fin = special.iter().copied().filter(|x| x.is_finite()).collect();
        Gen {
            rng: Rng(seed),
            special,
            special_fin,
        }
    }

    fn real(&mut self, k: Kind) -> f64 {
        let (a, b) = k.range();
        self.rng.range(a, b)
    }

    fn spec(&mut self, fin: bool) -> f64 {
        let v = if fin { &self.special_fin } else { &self.special };
        v[self.rng.below(v.len() as u64) as usize]
    }

    fn width(&mut self) -> f64 {
        if self.rng.below(10) == 0 {
            0.0
        } else {
            10f64.powf(self.rng.range(-16.0, -0.5))
        }
    }

    fn end(&mut self, k: Kind, fin: bool) -> f64 {
        if self.rng.below(2) == 0 {
            self.spec(fin)
        } else {
            self.real(k)
        }
    }

    /// An interval: realistic narrow or wide, empty, with special ends, a point, an end of random
    /// bits, or wide. With `fin`, finite ends only.
    fn iv(&mut self, k: Kind, fin: bool) -> Iv {
        match self.rng.below(100) {
            0..=34 => {
                let lo = self.real(k);
                let hi = lo + self.width();
                Iv::new(lo, hi)
            }
            35..=49 => {
                let (x, y) = (self.real(k), self.real(k));
                Iv::new(x.min(y), x.max(y))
            }
            50..=57 => {
                let (x, y) = (self.real(k), self.real(k));
                Iv::new(x.max(y), x.min(y))
            }
            58..=74 => {
                let (x, y) = (self.end(k, fin), self.end(k, fin));
                if self.rng.below(10) < 7 && x <= y {
                    Iv::new(x, y)
                } else if self.rng.below(10) < 7 && y <= x {
                    Iv::new(y, x)
                } else {
                    Iv::new(x, y)
                }
            }
            75..=84 => {
                let x = self.end(k, fin);
                Iv::new(x, x)
            }
            85..=94 => {
                let mut z = f64::from_bits(self.rng.next());
                if fin && !z.is_finite() {
                    z = self.real(k);
                }
                let x = self.real(k);
                if self.rng.below(2) == 0 {
                    Iv::new(z.min(x), z.max(x))
                } else {
                    Iv::new(z, x)
                }
            }
            _ => {
                let (x, y) = (self.real(Kind::Gen), self.real(Kind::Gen));
                Iv::new(x.min(y), x.max(y))
            }
        }
    }

    fn ivs<const K: usize>(&mut self, k: Kind) -> [Iv; K] {
        let mut v = [Iv::pt(0.0); K];
        for x in v.iter_mut() {
            *x = self.iv(k, false);
        }
        v
    }

    /// A box of 14 variables with finite ends: 0 the variable a, 1 the variable d, 2 to 7
    /// corners, 8 to 13 distances r.
    fn bx(&mut self) -> Vec<Iv> {
        (0..14)
            .map(|i| {
                let k = match i {
                    0 => Kind::Angle,
                    1 => Kind::D,
                    2..=7 => Kind::Angle,
                    _ => Kind::Side,
                };
                self.iv(k, true)
            })
            .collect()
    }

    /// `m` indices in `lo..hi`, distinct with probability 0.9, else any in `0..14`.
    fn idx(&mut self, m: usize, lo: usize, hi: usize) -> Vec<usize> {
        if self.rng.below(10) == 0 {
            return (0..m).map(|_| self.rng.below(14) as usize).collect();
        }
        let mut pool: Vec<usize> = (lo..hi).collect();
        let mut out = Vec::new();
        for _ in 0..m {
            let k = self.rng.below(pool.len() as u64) as usize;
            out.push(pool.swap_remove(k));
        }
        out
    }

    fn di(&mut self) -> usize {
        if self.rng.below(10) == 0 {
            self.rng.below(14) as usize
        } else {
            1
        }
    }

    fn coef(&mut self) -> f64 {
        match self.rng.below(20) {
            0 => 0.0,
            1 => -0.0,
            2 => 1e-300,
            3 => -1e300,
            4 => 1e308,
            5..=9 => self.rng.range(-3.0, 3.0),
            _ => [1.0, -1.0, 2.0, -2.0, 0.5, -0.5, 3.0, -3.0, 1.5, 4.0][self.rng.below(10) as usize],
        }
    }

    fn dir(&mut self) -> i8 {
        self.rng.below(3) as i8 - 1
    }
}

fn bx_tokens(s: &mut String, b: &[Iv]) {
    write!(s, " {}", b.len()).unwrap();
    for v in b {
        hiv(s, *v);
    }
}

fn res_box(r: Result<(), ()>, b: &[Iv]) -> String {
    let mut s = String::new();
    match r {
        Err(()) => s.push('0'),
        Ok(()) => {
            s.push('1');
            for v in b {
                hiv(&mut s, *v);
            }
        }
    }
    s
}

fn res_iv(v: Iv) -> String {
    let mut s = String::from("0");
    hiv(&mut s, v);
    s
}

fn res_opt(r: Result<Iv, ()>) -> String {
    match r {
        Err(()) => "0".into(),
        Ok(v) => {
            let mut s = String::from("1");
            hiv(&mut s, v);
            s
        }
    }
}

fn res_ivs(v: &[Iv]) -> String {
    let mut s = String::from("0");
    for x in v {
        hiv(&mut s, *x);
    }
    s
}

fn res_fl(x: f64) -> String {
    let mut s = String::from("0");
    hx(&mut s, x);
    s
}

// The pass-inline steps: the lines of deep.rs `pass` (rows "a <-> d", "Rhombus", "Hex" diagonals),
// copied as they stand there.
fn alpha_step(b: &mut [Iv], di: usize) -> Result<(), ()> {
    let na = alpha_iv(b[di]);
    nar(b, 0, na)
}
fn alpha_inv_step(b: &mut [Iv], di: usize) -> Result<(), ()> {
    let nd = alpha_inv_iv(b[0]);
    nar(b, di, nd)
}
fn rho_step(b: &mut [Iv], x: usize, y: usize, di: usize) -> Result<(), ()> {
    let d = b[di];
    let ny = crate::ivt::rho(b[x], d);
    nar(b, y, ny)
}
fn rho_d_step(b: &mut [Iv], x: usize, y: usize, di: usize) -> Result<(), ()> {
    let nd = rhombus_d(b[x], b[y])?;
    nar(b, di, nd)
}
fn diag_fwd_step(b: &mut [Iv], p: usize, q: usize, di: usize) -> Result<(), ()> {
    let lq = longdiag_lb(b[p], b[di]);
    nar(b, q, Iv::new(lq, f64::INFINITY))
}
fn diag_bwd_step(b: &mut [Iv], p: usize, q: usize, di: usize) -> Result<(), ()> {
    let lp = longdiag_lb(b[q], b[di]);
    nar(b, p, Iv::new(lp, f64::INFINITY))
}

const PRIMS: [&str; 30] = [
    "nar",
    "isoBase",
    "isoAngle",
    "triAngleSt",
    "triAngle",
    "triAngleC",
    "alphaIv",
    "alphaInvIv",
    "rhoIv",
    "rhombusD",
    "side",
    "longdiagLb",
    "cornerEnds",
    "decDir",
    "monoBounds2",
    "monoBounds3",
    "pentEvalC",
    "hexEvalC",
    "cmin",
    "cmax",
    "alphaStep",
    "alphaInvStep",
    "rhoStep",
    "rhoDStep",
    "diagFwdStep",
    "diagBwdStep",
    "pentStep",
    "hexStep",
    "wheelStep",
    "rowStep",
];

/// One case of `prim`: its input tokens and the program's result, computed with the log on.
fn run_case(prim: &str, g: &mut Gen) -> (String, String) {
    let mut i = String::new();
    let r: String;
    match prim {
        "nar" => {
            let mut b: Vec<Iv> = (0..3).map(|_| g.iv(Kind::Angle, true)).collect();
            let j = g.rng.below(3) as usize;
            let n = g.iv(Kind::Angle, false);
            bx_tokens(&mut i, &b);
            write!(i, " {}", j).unwrap();
            hiv(&mut i, n);
            dtlog::start();
            let res = nar(&mut b, j, n);
            r = res_box(res, &b);
        }
        "isoBase" | "isoAngle" | "longdiagLb" => {
            let (u, d) = (g.iv(Kind::Angle, false), g.iv(Kind::D, false));
            hiv(&mut i, u);
            hiv(&mut i, d);
            dtlog::start();
            r = match prim {
                "isoBase" => res_iv(iso_base(u, d)),
                "isoAngle" => res_iv(iso_angle(u, d)),
                _ => res_fl(longdiag_lb(u, d)),
            };
        }
        "triAngleSt" | "triAngle" | "triAngleC" => {
            let [a, b, c] = g.ivs::<3>(Kind::Side);
            hiv(&mut i, a);
            hiv(&mut i, b);
            hiv(&mut i, c);
            dtlog::start();
            r = match prim {
                "triAngleSt" => match tri_angle_st(a, b, c) {
                    Ok(v) => res_iv(v),
                    Err(v) => {
                        let mut s = String::from("1");
                        hiv(&mut s, v);
                        s
                    }
                },
                "triAngle" => res_opt(tri_angle(a, b, c)),
                _ => res_iv(tri_angle_c(a, b, c)),
            };
        }
        "alphaIv" => {
            let d = g.iv(Kind::D, false);
            hiv(&mut i, d);
            dtlog::start();
            r = res_iv(alpha_iv(d));
        }
        "alphaInvIv" => {
            let a = g.iv(Kind::Angle, false);
            hiv(&mut i, a);
            dtlog::start();
            r = res_iv(alpha_inv_iv(a));
        }
        "rhoIv" => {
            let (x, d) = (g.iv(Kind::Angle, false), g.iv(Kind::D, false));
            hiv(&mut i, x);
            hiv(&mut i, d);
            dtlog::start();
            r = res_iv(crate::ivt::rho(x, d));
        }
        "rhombusD" => {
            let [x, y] = g.ivs::<2>(Kind::Angle);
            hiv(&mut i, x);
            hiv(&mut i, y);
            dtlog::start();
            r = res_opt(rhombus_d(x, y));
        }
        "side" => {
            let (b, c, a) = (
                g.iv(Kind::Side, false),
                g.iv(Kind::D, false),
                g.iv(Kind::Angle, false),
            );
            hiv(&mut i, b);
            hiv(&mut i, c);
            hiv(&mut i, a);
            dtlog::start();
            r = res_opt(side(b, c, a));
        }
        "cornerEnds" => {
            let u = g.iv(Kind::Angle, false);
            hiv(&mut i, u);
            dtlog::start();
            let (a, b) = corner_ends(u);
            r = res_ivs(&[a, b]);
        }
        "decDir" => {
            let [u, bx, x] = g.ivs::<3>(Kind::Angle);
            let d = g.iv(Kind::D, false);
            for v in [u, bx, x, d] {
                hiv(&mut i, v);
            }
            dtlog::start();
            r = format!("{}", dec_dir(u, bx, x, d));
        }
        "monoBounds2" => {
            let d = g.iv(Kind::D, false);
            let inp = g.ivs::<2>(Kind::Angle);
            let mut ends = [(Iv::pt(0.0), Iv::pt(0.0)); 2];
            for (j, e) in ends.iter_mut().enumerate() {
                *e = if g.rng.below(2) == 0 {
                    corner_ends(inp[j])
                } else {
                    (g.iv(Kind::Angle, false), g.iv(Kind::Angle, false))
                };
            }
            let mut dirs = [[0i8; 2]; 3];
            for row in dirs.iter_mut() {
                for x in row.iter_mut() {
                    *x = g.dir();
                }
            }
            hiv(&mut i, d);
            for j in 0..2 {
                hiv(&mut i, inp[j]);
                hiv(&mut i, ends[j].0);
                hiv(&mut i, ends[j].1);
            }
            for row in dirs {
                for x in row {
                    write!(i, " {}", x).unwrap();
                }
            }
            dtlog::start();
            r = res_ivs(&mono_bounds(&inp, &ends, &dirs, &|x| pent_eval_c(x, d)));
        }
        "monoBounds3" => {
            let d = g.iv(Kind::D, false);
            let inp = g.ivs::<3>(Kind::Angle);
            let mut ends = [(Iv::pt(0.0), Iv::pt(0.0)); 3];
            for (j, e) in ends.iter_mut().enumerate() {
                *e = if g.rng.below(2) == 0 {
                    corner_ends(inp[j])
                } else {
                    (g.iv(Kind::Angle, false), g.iv(Kind::Angle, false))
                };
            }
            let mut dirs = [[0i8; 3]; 3];
            for row in dirs.iter_mut() {
                for x in row.iter_mut() {
                    *x = g.dir();
                }
            }
            hiv(&mut i, d);
            for j in 0..3 {
                hiv(&mut i, inp[j]);
                hiv(&mut i, ends[j].0);
                hiv(&mut i, ends[j].1);
            }
            for row in dirs {
                for x in row {
                    write!(i, " {}", x).unwrap();
                }
            }
            dtlog::start();
            r = res_ivs(&mono_bounds(&inp, &ends, &dirs, &|x| hex_eval_c(x, d)));
        }
        "pentEvalC" => {
            let d = g.iv(Kind::D, false);
            let x = g.ivs::<2>(Kind::Angle);
            hiv(&mut i, d);
            for v in x {
                hiv(&mut i, v);
            }
            dtlog::start();
            r = res_ivs(&pent_eval_c(&x, d));
        }
        "hexEvalC" => {
            let d = g.iv(Kind::D, false);
            let x = g.ivs::<3>(Kind::Angle);
            hiv(&mut i, d);
            for v in x {
                hiv(&mut i, v);
            }
            dtlog::start();
            r = res_ivs(&hex_eval_c(&x, d));
        }
        "cmin" | "cmax" => {
            let c = g.coef();
            let lu = g.iv(Kind::Gen, true);
            hx(&mut i, c);
            hx(&mut i, lu.lo);
            hx(&mut i, lu.hi);
            dtlog::start();
            r = res_fl(if prim == "cmin" {
                cmin(c, lu.lo, lu.hi)
            } else {
                cmax(c, lu.lo, lu.hi)
            });
        }
        "alphaStep" | "alphaInvStep" => {
            let mut b = g.bx();
            let di = g.di();
            bx_tokens(&mut i, &b);
            write!(i, " {}", di).unwrap();
            dtlog::start();
            let res = if prim == "alphaStep" {
                alpha_step(&mut b, di)
            } else {
                alpha_inv_step(&mut b, di)
            };
            r = res_box(res, &b);
        }
        "rhoStep" | "rhoDStep" | "diagFwdStep" | "diagBwdStep" => {
            let mut b = g.bx();
            let u = g.idx(2, 2, 8);
            let di = g.di();
            bx_tokens(&mut i, &b);
            write!(i, " {} {} {}", u[0], u[1], di).unwrap();
            dtlog::start();
            let res = match prim {
                "rhoStep" => rho_step(&mut b, u[0], u[1], di),
                "rhoDStep" => rho_d_step(&mut b, u[0], u[1], di),
                "diagFwdStep" => diag_fwd_step(&mut b, u[0], u[1], di),
                _ => diag_bwd_step(&mut b, u[0], u[1], di),
            };
            r = res_box(res, &b);
        }
        "pentStep" => {
            let mut b = g.bx();
            let u = g.idx(5, 2, 8);
            let rot = g.rng.below(5) as usize;
            let di = g.di();
            bx_tokens(&mut i, &b);
            for x in &u {
                write!(i, " {}", x).unwrap();
            }
            write!(i, " {} {}", rot, di).unwrap();
            let ua: [usize; 5] = [u[0], u[1], u[2], u[3], u[4]];
            dtlog::start();
            let res = pent_rot(&mut b, &ua, rot, di);
            r = res_box(res, &b);
        }
        "hexStep" => {
            let mut b = g.bx();
            let u = g.idx(6, 2, 8);
            let par = g.rng.below(2) as usize;
            let di = g.di();
            bx_tokens(&mut i, &b);
            for x in &u {
                write!(i, " {}", x).unwrap();
            }
            write!(i, " {} {}", par, di).unwrap();
            let ua: [usize; 6] = [u[0], u[1], u[2], u[3], u[4], u[5]];
            dtlog::start();
            let res = hex_par(&mut b, &ua, par, di);
            r = res_box(res, &b);
        }
        "wheelStep" => {
            let mut b = g.bx();
            let u = g.idx(6, 2, 8);
            let r0 = if g.rng.below(10) == 0 {
                g.rng.below(9) as usize
            } else {
                8
            };
            let di = g.di();
            if g.rng.below(10) < 7 {
                // near the regular spherical wheel: sin r = 2 sin(d / 2) makes the six angles at P
                // equal to pi / 3, and the corners are twice the base angle of the isosceles
                // triangle (r, r, d); so the angle sum test passes and the narrowings run
                let d0 = g.rng.range(0.85, 1.0);
                b[di] = Iv::new(d0, d0 + g.width() * 0.01);
                let rs = (2.0 * (0.5 * d0).sin()).asin();
                let beta = (rs.cos() * (1.0 - d0.cos()) / (rs.sin() * d0.sin())).acos();
                for k in 0..6 {
                    let (w1, w2) = (
                        10f64.powf(g.rng.range(-9.0, -1.3)),
                        10f64.powf(g.rng.range(-9.0, -1.3)),
                    );
                    b[r0 + k] = Iv::new(rs * (1.0 - w1), rs * (1.0 + w2));
                }
                for k in 0..6 {
                    let (w1, w2) = (
                        10f64.powf(g.rng.range(-6.0, -0.4)),
                        10f64.powf(g.rng.range(-6.0, -0.4)),
                    );
                    b[u[k]] = Iv::new(2.0 * beta - w1, 2.0 * beta + w2);
                }
            }
            bx_tokens(&mut i, &b);
            for x in &u {
                write!(i, " {}", x).unwrap();
            }
            write!(i, " {} {}", r0, di).unwrap();
            let ua: [usize; 6] = [u[0], u[1], u[2], u[3], u[4], u[5]];
            dtlog::start();
            let res = wheel(&mut b, &ua, r0, di);
            r = res_box(res, &b);
        }
        "rowStep" => {
            let n = 6;
            let b: Vec<Iv> = (0..n).map(|_| g.iv(Kind::Gen, true)).collect();
            let k = 1 + g.rng.below(6) as usize;
            let tv: Vec<u32> = (0..k).map(|_| g.rng.below(n as u64) as u32).collect();
            let tc: Vec<f64> = (0..k).map(|_| g.coef()).collect();
            let rr = g.iv(Kind::Gen, false);
            let (rlo, rhi) = match g.rng.below(6) {
                0 => (f64::NEG_INFINITY, rr.hi),
                1 => (rr.lo, f64::INFINITY),
                _ => (rr.lo, rr.hi),
            };
            bx_tokens(&mut i, &b);
            write!(i, " {}", k).unwrap();
            for j in 0..k {
                write!(i, " {}", tv[j]).unwrap();
                hx(&mut i, tc[j]);
            }
            hx(&mut i, rlo);
            hx(&mut i, rhi);
            let mut s = Sys {
                nvar: n,
                lo: b.iter().map(|v| v.lo).collect(),
                hi: b.iter().map(|v| v.hi).collect(),
                rs: vec![0, k as u32],
                tv,
                tc,
                rlo: vec![rlo],
                rhi: vec![rhi],
                cvar: Vec::new(),
                uses_uncertified: false,
            };
            dtlog::start();
            let res = fbbt(&mut s, 1, 1e-13);
            let nb: Vec<Iv> = (0..n).map(|j| Iv::new(s.lo[j], s.hi[j])).collect();
            r = res_box(if res == Fbbt::Infeasible { Err(()) } else { Ok(()) }, &nb);
        }
        _ => panic!("unknown primitive {prim}"),
    }
    (i, r)
}

/// The variants of the arguments of a logged call: zeros with both signs, NaNs with two payloads.
fn variants(e: &Entry) -> Vec<[f64; 4]> {
    let n = dtlog::arity(e.op);
    let mut out = vec![e.a];
    for k in 0..n {
        let x = e.a[k];
        if x == 0.0 || x.is_nan() {
            let alts: Vec<f64> = if x == 0.0 {
                vec![-x]
            } else {
                vec![
                    f64::from_bits(0x7ff8_0000_0000_0001),
                    f64::from_bits(0xfff8_0000_0000_0000),
                ]
            };
            let mut more = Vec::new();
            for a in &out {
                for &y in &alts {
                    let mut b = *a;
                    b[k] = y;
                    more.push(b);
                }
            }
            out.extend(more);
        }
    }
    out
}

#[derive(Default)]
struct Stats {
    cases: u64,
    conflicts: u64,
    flips: u64,
    entries: u64,
    tags: std::collections::BTreeMap<String, u64>,
}

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: u64 = args
        .get(1)
        .and_then(|s| s.parse().ok())
        .expect("usage: difftest N [PRIM...]");
    let prims: Vec<&str> = if args.len() > 2 {
        args[2..].iter().map(|s| s.as_str()).collect()
    } else {
        PRIMS.to_vec()
    };
    let out = std::io::stdout();
    let mut w = BufWriter::with_capacity(1 << 20, out.lock());
    let mut line = String::new();
    hx(&mut line, PI_LO);
    hx(&mut line, PI_HI);
    hx(&mut line, TWO_PI_LO);
    hx(&mut line, TWO_PI_HI);
    writeln!(w, "P{line}").unwrap();
    let mut all = Vec::new();
    for prim in prims {
        let pidx = PRIMS.iter().position(|p| *p == prim).expect("unknown primitive") as u64;
        let mut g = Gen::new(20_261_001 + 1_000_003 * pidx);
        let mut st = Stats::default();
        for id in 0..n {
            let (inp, res) = run_case(prim, &mut g);
            let log = dtlog::stop();
            let mut seen: HashMap<(u8, [u64; 4]), [u64; 2]> = HashMap::new();
            let mut body = String::new();
            for e in &log {
                let key = (e.op, [canon(e.a[0]), canon(e.a[1]), canon(e.a[2]), canon(e.a[3])]);
                let val = [canon(e.r[0]), canon(e.r[1])];
                match seen.get(&key) {
                    Some(v) => {
                        if *v != val {
                            st.conflicts += 1;
                            eprintln!(
                                "CONFLICT {prim} {id} op {} {:x?} {:x?} {:x?}",
                                dtlog::OP_NAMES[e.op as usize],
                                key.1,
                                v,
                                val
                            );
                        }
                        continue;
                    }
                    None => {
                        seen.insert(key, val);
                    }
                }
                for a in variants(e).into_iter().skip(1) {
                    let rr = dtlog::eval(e.op, a);
                    if [canon(rr[0]), canon(rr[1])] != val {
                        st.flips += 1;
                        eprintln!(
                            "FLIP {prim} {id} op {} {:x?} {:x?} {:x?}",
                            dtlog::OP_NAMES[e.op as usize],
                            a.map(f64::to_bits),
                            val,
                            rr.map(canon)
                        );
                    }
                }
                write!(body, "O {}", e.op).unwrap();
                for x in e.a {
                    write!(body, " {:016x}", canon(x)).unwrap();
                }
                writeln!(body, " {:016x} {:016x}", val[0], val[1]).unwrap();
            }
            st.entries += seen.len() as u64;
            st.cases += 1;
            let mut tag = res.split(' ').next().unwrap_or("").to_string();
            // a box result: "1=" when the box is unchanged, "1*" when it narrowed
            if tag == "1" && (prim == "nar" || prim.ends_with("Step")) {
                let it: Vec<&str> = inp.split_whitespace().collect();
                let rt: Vec<&str> = res.split_whitespace().collect();
                tag = if it[1..rt.len()] == rt[1..] {
                    "1=".into()
                } else {
                    "1*".into()
                };
            }
            *st.tags.entry(tag).or_default() += 1;
            writeln!(w, "C {prim} {id}").unwrap();
            writeln!(w, "I{inp}").unwrap();
            w.write_all(body.as_bytes()).unwrap();
            writeln!(w, "R {res}").unwrap();
            writeln!(w, "E").unwrap();
        }
        all.push((prim, st));
    }
    for (prim, st) in &all {
        let mut s = format!(
            "S {prim} {} {} {} {}",
            st.cases, st.conflicts, st.flips, st.entries
        );
        for (t, c) in &st.tags {
            write!(s, " {t}:{c}").unwrap();
        }
        writeln!(w, "{s}").unwrap();
        eprintln!("{s}");
    }
    w.flush().unwrap();
}
