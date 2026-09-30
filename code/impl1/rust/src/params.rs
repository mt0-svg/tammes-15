//! Parameters of the level-1 linear system, read from a text file produced by code/gp/params.sh.
//!
//! Lines: `alo x`, `ahi x` (enclosure of alpha(d) = angle of the equilateral triangle of side d, over
//! the admissible range of d), `shi x` (upper bound of the angle sum u1 + u2 of a rhombus),
//! `cut c c0` (y - c x <= c0 for every rhombus angle pair, both orders), and optional face
//! inequalities `pent w0 w1 w2 w3 w4 lo hi` / `hex w0 .. w5 lo hi` meaning
//! lo <= sum_i w_i u_{s+i} <= hi for every rotation s and both orientations of the face.
//! Face inequalities marked `pent!`/`hex!` are certified; plain ones are numerical (uncertified).

use crate::iv::{parse_dn, parse_up};

#[derive(Clone, Debug, Default)]
pub struct FaceIneq {
    pub w: Vec<f64>,
    pub lo: f64,
    pub hi: f64,
    pub certified: bool,
}

#[derive(Clone, Debug, Default)]
pub struct Params {
    pub alo: f64,
    pub ahi: f64,
    pub shi: f64,
    pub cuts: Vec<(f64, f64)>,
    pub pent: Vec<FaceIneq>,
    pub hex: Vec<FaceIneq>,
    /// inequalities for hexagons containing an isolated vertex (`hexf`, `hexf!`)
    pub hexf: Vec<FaceIneq>,
    /// hexagon with an isolated vertex inside: lower bound of the angle sum
    pub fullhex_sum_lo: Option<f64>,
}

fn parse_face(t: &[&str], size: usize, certified: bool) -> FaceIneq {
    assert_eq!(t.len(), size + 3, "face inequality arity");
    let w = (0..size).map(|i| t[1 + i].parse::<f64>().unwrap()).collect();
    let lo = if t[size + 1] == "-inf" { f64::NEG_INFINITY } else { parse_dn(t[size + 1]) };
    let hi = if t[size + 2] == "inf" { f64::INFINITY } else { parse_up(t[size + 2]) };
    FaceIneq { w, lo, hi, certified }
}

impl Params {
    pub fn from_str(s: &str) -> Params {
        let mut p = Params::default();
        for line in s.lines() {
            let t: Vec<&str> = line.split_whitespace().collect();
            if t.is_empty() || t[0].starts_with('#') {
                continue;
            }
            match t[0] {
                "alo" => p.alo = parse_dn(t[1]),
                "ahi" => p.ahi = parse_up(t[1]),
                "shi" => p.shi = parse_up(t[1]),
                "cut" => p.cuts.push((t[1].parse::<f64>().unwrap(), parse_up(t[2]))),
                "pent" => p.pent.push(parse_face(&t, 5, false)),
                "pent!" => p.pent.push(parse_face(&t, 5, true)),
                "hex" => p.hex.push(parse_face(&t, 6, false)),
                "hex!" => p.hex.push(parse_face(&t, 6, true)),
                "hexf" => p.hexf.push(parse_face(&t, 6, false)),
                "hexf!" => p.hexf.push(parse_face(&t, 6, true)),
                "fullhex_sum_lo" => p.fullhex_sum_lo = Some(parse_dn(t[1])),
                "dlo" | "dhi" => {}
                k => panic!("unknown parameter key {k}"),
            }
        }
        assert!(p.alo > 1.0 && p.ahi >= p.alo && p.shi > 3.0, "incomplete parameters");
        p
    }

    pub fn load(path: &str) -> Params {
        Params::from_str(&std::fs::read_to_string(path).expect("cannot read params"))
    }

    /// Note: the cut constant c0 is valid for the decimal slope c; the f64 slope differs from the
    /// decimal by at most 1e-16 relative, and x <= 2.5, so c0 is widened by 1e-15 here.
    pub fn cut_c0(&self, k: usize) -> f64 {
        self.cuts[k].1 + 1e-15
    }
}
