//! Level 2 of the Musin-Tarasov scheme: interval branch-and-prune on the exact angle relations of
//! one case (plane graph faces + optional mask of hexagons holding an isolated vertex).
//!
//! Box variables: the level-1 variables of `system::Sys` (v0 = a = alpha(d), rhombus x/y,
//! pentagon and hexagon corners), then d, then for each full hexagon the six distances
//! r_i = |P A_i| from the isolated vertex P to the corners (wheel variables, optional).
//!
//! Contractors, each sound in outward-rounded interval arithmetic (ivt::Iv; transcendental
//! functions by rtrig.rs, rigorous). Derivations: Section 6.2 of the paper.
//!   lin    FBBT on the rows of Sys (vertex sums, rhombus rows, face inequalities if enabled)
//!   alpha  a = alpha(d) and d = alpha^{-1}(a), both increasing
//!   rho    rhombus: y = rho(x, d), x = rho(y, d), d = acos(cot(x/2) cot(y/2))
//!   pent   fan from each corner A_i: (u_{i-1}, u_{i+1}, d) give u_i, u_{i+2}, u_{i-2}
//!   hex    alternate corners and d give the other three (both parities); long diagonals >= d
//!   wheel  full hexagon: triangles P A_i A_{i+1}, angles at P sum to 2 pi, d <= r_i <= 3d
//! A box is discarded only when a contractor proves that it holds no solution. The search is
//! deterministic; `Cert` records the tree (split variable and split point, reason of each
//! discard) so that a checker with a correctly rounded library can replay it (`replay`).

use crate::graph::Faces;
use crate::iv::{PI_HI, PI_LO, TWO_PI_HI, TWO_PI_LO};
use crate::ivt::Iv;
use crate::params::Params;
use crate::system::{fbbt, Fbbt, Opts, Reject, Sys};

/// Diagnostics: number of contractor passes (all cases of the process).
pub static PASSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Number of discard kinds (Reason::KINDS).
pub const NKINDS: usize = 13;

#[inline]
fn pt(x: f64) -> Iv {
    Iv::pt(x)
}

/// Usable enclosure (NaN-free, lo <= hi). Anything else carries no information.
#[inline]
fn usable(x: Iv) -> bool {
    x.lo <= x.hi
}

/// The interval lies inside (0, PI_LO) (NaN-free). Guard of `tri_angle_st`.
#[inline]
fn in_open(x: Iv) -> bool {
    0.0 < x.lo && x.hi < PI_LO
}

// ---------------------------------------------------------------------------------------------
// Spherical trigonometry on intervals

/// Base of the isosceles triangle with legs d and apex angle u: e = 2 asin(sin d sin(u/2)).
/// Valid for d in (0, pi/2], u in [0, 2 pi]; each variable occurs once (natural extension exact
/// up to rounding).
pub fn iso_base(u: Iv, d: Iv) -> Iv {
    d.sin().mul(u.scale(0.5).sin()).asin().scale(2.0)
}

/// Base angle of the isosceles triangle with legs d and apex angle u:
/// beta = atan(cos(u/2) / (cos d sin(u/2))) (Napier: cos d = cot(u/2) cot(beta)).
/// Decreasing in u for u in (0, 2 pi); d occurs once.
pub fn iso_angle(u: Iv, d: Iv) -> Iv {
    let cd = d.cos();
    let f = |x: f64| {
        let h = pt(x).scale(0.5);
        h.cos().div(cd.mul(h.sin())).atan()
    };
    Iv::new(f(u.hi).lo, f(u.lo).hi)
}

/// Angle opposite side g in the spherical triangle with sides g, e, f (all in (0, pi)).
/// cos G = h(g, e, f) = (cos g - cos e cos f) / (sin e sin f). h is decreasing in g; dh/de has
/// the sign of cos F (F opposite f), dh/df the sign of cos E; the signs are tested on the box and
/// the bounds taken at the corresponding corners (whole interval when the sign is unknown).
/// G = acos(h) is decreasing in h, so G is increasing in g (Section 6.2, T2).
/// Err(()) when no triangle with sides in the box exists (h > 1 or h < -1 on the whole box).
pub fn tri_angle(g: Iv, e: Iv, f: Iv) -> Result<Iv, ()> {
    tri_angle_st(g, e, f).map_err(|_| ())
}

/// Same as `tri_angle` for the clamped formula acos(clamp(h, -1, 1)), which is defined on the
/// whole box: where no triangle exists it returns the constant value (0 or pi) of the clamp.
/// Used at corners of a box in monotonicity arguments, where non-existence proves nothing.
pub fn tri_angle_c(g: Iv, e: Iv, f: Iv) -> Iv {
    tri_angle_st(g, e, f).unwrap_or_else(|v| v)
}

/// Err(v): no triangle on the whole box, v = constant value of the clamped formula there.
fn tri_angle_st(g: Iv, e: Iv, f: Iv) -> Result<Iv, Iv> {
    // The monotonicity below needs sin > 0 on the three sides: no information unless the three
    // intervals lie inside (0, PI_LO) (computed enclosures are passed here).
    if !(in_open(g) && in_open(e) && in_open(f)) {
        return Ok(Iv::new(0.0, PI_HI));
    }
    let h = |g: Iv, e: Iv, f: Iv| g.cos().sub(e.cos().mul(f.cos())).div(e.sin().mul(f.sin()));
    let gc = g.cos();
    // numerators of cos F and cos E (denominators are > 0)
    let nf = f.cos().sub(gc.mul(e.cos()));
    let ne = e.cos().sub(gc.mul(f.cos()));
    // h increasing in e iff cos F > 0; G = acos(h) is then decreasing in e.
    // (e at the corner where h is maximal, e at the corner where h is minimal)
    let (e_hmax, e_hmin) = if nf.lo > 0.0 {
        (pt(e.hi), pt(e.lo))
    } else if nf.hi < 0.0 {
        (pt(e.lo), pt(e.hi))
    } else {
        (e, e)
    };
    let (f_hmax, f_hmin) = if ne.lo > 0.0 {
        (pt(f.hi), pt(f.lo))
    } else if ne.hi < 0.0 {
        (pt(f.lo), pt(f.hi))
    } else {
        (f, f)
    };
    let hmax = h(pt(g.lo), e_hmax, f_hmax); // upper bound of h: .hi
    let hmin = h(pt(g.hi), e_hmin, f_hmin); // lower bound of h: .lo
    if !(hmax.hi <= f64::INFINITY) || !(hmin.lo >= f64::NEG_INFINITY) {
        return Ok(Iv::new(0.0, PI_HI)); // NaN: no information
    }
    if hmax.hi < -1.0 {
        return Err(Iv::pi());
    }
    if hmin.lo > 1.0 {
        return Err(Iv::pt(0.0));
    }
    let lo = pt(hmax.hi.min(1.0)).acos().lo;
    let hi = pt(hmin.lo.max(-1.0)).acos().hi;
    Ok(Iv::new(lo.max(0.0), hi))
}

/// alpha(d) = acos(cos d / (1 + cos d)), increasing; evaluated at the endpoints.
pub fn alpha_iv(d: Iv) -> Iv {
    let f = |x: f64| {
        let c = pt(x).cos();
        c.div(c.add(pt(1.0))).acos()
    };
    Iv::new(f(d.lo).lo, f(d.hi).hi)
}

/// alpha^{-1}(a) = acos(cos a / (1 - cos a)), increasing on (pi/3, pi/2 + ...).
pub fn alpha_inv_iv(a: Iv) -> Iv {
    let f = |x: f64| {
        let c = pt(x).cos();
        c.div(pt(1.0).sub(c)).acos()
    };
    Iv::new(f(a.lo).lo, f(a.hi).hi)
}

/// Side of a rhombus from its angles: d = acos(cot(x/2) cot(y/2)), increasing in x and y
/// (x, y in (0, pi)). Err if cot(x/2) cot(y/2) > 1 on the whole box.
fn rhombus_d(x: Iv, y: Iv) -> Result<Iv, ()> {
    let cot = |t: f64| {
        let h = pt(t).scale(0.5);
        h.cos().div(h.sin())
    };
    let pmax = cot(x.lo).mul(cot(y.lo)); // largest product: smallest d
    let pmin = cot(x.hi).mul(cot(y.hi));
    if !usable(pmax) || !usable(pmin) {
        return Ok(Iv::new(0.0, PI_HI));
    }
    if pmin.lo > 1.0 {
        return Err(());
    }
    let lo = pt(pmax.hi.min(1.0)).acos().lo;
    let hi = pt(pmin.lo.max(-1.0)).acos().hi;
    Ok(Iv::new(lo, hi))
}

/// Side opposite the angle `ang` in the triangle with sides b, c around it:
/// cos a = cos b cos c + sin b sin c cos A. The angle is first clamped to [0, pi] (Err if the
/// clamp is empty). a is increasing in A; d(cos a)/db = -(sin b cos c - cos b sin c cos A) and
/// symmetrically in c (identities valid for all arguments), so the signs are tested on the box
/// and the bounds taken at the corresponding corners.
pub fn side(b: Iv, c: Iv, ang: Iv) -> Result<Iv, ()> {
    let a = Iv::new(ang.lo.max(0.0), ang.hi.min(PI_HI));
    if !(a.lo <= a.hi) {
        return Err(());
    }
    let q = |b: Iv, c: Iv, ca: Iv| b.cos().mul(c.cos()).add(b.sin().mul(c.sin()).mul(ca));
    let ca = a.cos();
    let sb = b.sin().mul(c.cos()).sub(b.cos().mul(c.sin()).mul(ca));
    let sc = c.sin().mul(b.cos()).sub(c.cos().mul(b.sin()).mul(ca));
    // a increasing in b iff sb > 0: (b where a is minimal, b where a is maximal)
    let (b_amin, b_amax) = if sb.lo > 0.0 {
        (pt(b.lo), pt(b.hi))
    } else if sb.hi < 0.0 {
        (pt(b.hi), pt(b.lo))
    } else {
        (b, b)
    };
    let (c_amin, c_amax) = if sc.lo > 0.0 {
        (pt(c.lo), pt(c.hi))
    } else if sc.hi < 0.0 {
        (pt(c.hi), pt(c.lo))
    } else {
        (c, c)
    };
    let qmax = q(b_amin, c_amin, pt(a.lo).cos());
    // cos is decreasing in the angle on [0, pi] only: at an upper end of at least PI_LO (it may be
    // PI_HI > pi) the cosine is bounded below by -1 instead.
    let ca_hi = if PI_LO <= a.hi { pt(-1.0) } else { pt(a.hi).cos() };
    let qmin = q(b_amax, c_amax, ca_hi);
    if !usable(qmax) || !usable(qmin) {
        return Ok(Iv::new(0.0, PI_HI));
    }
    let lo = pt(qmax.hi.min(1.0)).acos().lo;
    let hi = pt(qmin.lo.max(-1.0)).acos().hi;
    Ok(Iv::new(lo.max(0.0), hi))
}

/// Lower bound of the angle at A_2 of a convex equilateral chain A_0 A_1 A_2 A_3 (sides d, angle
/// u at A_1) needed for |A_0 A_3| >= d: L(u, d) = beta(u, d) + acos(cot d tan(e/2)), e = base of
/// the isosceles triangle (legs d, apex u). L is decreasing in u; returns inf over the box.
fn longdiag_lb(u: Iv, d: Iv) -> f64 {
    let up = pt(u.hi);
    let e = iso_base(up, d);
    let b = iso_angle(up, d);
    let arg = d.cos().div(d.sin()).mul(e.scale(0.5).tan());
    if !usable(arg) || !usable(b) {
        return f64::NEG_INFINITY;
    }
    let phi_lo = pt(arg.hi.min(1.0)).acos().lo;
    b.add(pt(phi_lo)).lo
}

// ---------------------------------------------------------------------------------------------
// Problem description

#[derive(Clone, Debug)]
pub enum FaceK {
    Tri,
    Rhombus { x: usize, y: usize },
    Pent { u: [usize; 5] },
    /// `r`: index of the first wheel variable when the hexagon holds an isolated vertex
    Hex { u: [usize; 6], r: Option<usize> },
}

/// Reason of a discard: contractor kind and face (for a checker and for statistics).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Reason {
    Lin,
    Alpha,
    Rho(u16),
    Pent(u16, u8),
    Hex(u16, u8),
    HexDiag(u16, u8),
    Wheel(u16),
    Bound,
    /// linear relaxation infeasible, verified Farkas certificate (xlin.rs)
    Lp,
    /// two vertices around a common vertex, sharing no face, closer than d (xstar.rs)
    Star,
    /// tie window: the glued configuration lies within the radius of Theorem C of a copy of C1 or
    /// C3 (local.rs); the box holds no configuration with minimal distance > psi*
    Local,
    /// two points of the glued configuration, not joined by an edge, closer than d (local.rs)
    Pair,
    /// an edge (or a wheel radius) of the glued configuration has the wrong length (local.rs)
    Close,
}

impl Reason {
    pub fn kind(&self) -> usize {
        match self {
            Reason::Lin => 0,
            Reason::Alpha => 1,
            Reason::Rho(_) => 2,
            Reason::Pent(..) => 3,
            Reason::Hex(..) => 4,
            Reason::HexDiag(..) => 5,
            Reason::Wheel(_) => 6,
            Reason::Bound => 7,
            Reason::Lp => 8,
            Reason::Star => 9,
            Reason::Local => 10,
            Reason::Pair => 11,
            Reason::Close => 12,
        }
    }
    pub const KINDS: [&'static str; NKINDS] = ["lin", "alpha", "rho", "pent", "hex", "hexdiag", "wheel", "bound", "lp", "star", "local", "pair", "close"];
}

#[derive(Clone, Copy, Debug)]
pub struct Cfg {
    /// linear rows: use face inequalities of the parameter file (numerical, uncertified)
    pub use_face_ineq: bool,
    pub use_cuts: bool,
    /// wheel variables for hexagons holding an isolated vertex
    pub use_wheel: bool,
    pub lin_sweeps: usize,
    pub max_rounds: usize,
    /// stop propagation when no variable shrinks by more than this fraction of its width
    pub shrink: f64,
    /// boxes whose branchable variables are all narrower than `tol` are reported unresolved
    pub tol: f64,
    pub max_nodes: u64,
    pub max_unres: usize,
    /// stop the search after this many unresolved boxes (the case survives anyway)
    pub stop_unres: u64,
    /// weight of d in the split choice (relative widths are multiplied by it)
    pub dweight: f64,
    /// split choice on widths relative to the propagated root box (else absolute widths)
    pub rel_scale: bool,
    /// with rel_scale: reference width for d (instead of its root width), so that a narrow
    /// d range is not split first
    pub dref: Option<f64>,
    pub record: bool,
    /// LP kill test on the linear relaxation (xlin.rs) at every node of depth >= xlp_depth
    pub xlp: bool,
    pub xlp_depth: usize,
    /// with xlp: 0 = kill test only, 1 = also LP bounds on d, 2 = LP bounds on every variable
    pub xobbt: u8,
    /// inter-face "star" kill test (xstar.rs)
    pub xstar: bool,
    /// split d first while its width exceeds this (rad): the face contractors are much weaker
    /// on wide d ranges
    pub dsplit: f64,
    /// branch on the wheel variables r_i (else they are only contracted)
    pub branch_wheel: bool,
    /// weight of the wheel variables in the split choice (their scaled width is multiplied by it;
    /// small values split the corners first and the free point last)
    pub rweight: f64,
    /// split a corner whose interval reaches within pisplit/2 of pi at pi - pisplit (isolates the
    /// nearly straight corners; 0 = always bisect)
    pub pisplit: f64,
    /// 3B shaving after propagation: slices of 1/shave of the width at both ends of every
    /// branchable variable are refuted by propagation and removed (0 = off)
    pub shave: usize,
}

impl Default for Cfg {
    fn default() -> Self {
        Cfg {
            use_face_ineq: true,
            use_cuts: true,
            use_wheel: true,
            lin_sweeps: 8,
            max_rounds: 40,
            shrink: 0.02,
            tol: 1e-9,
            max_nodes: 2_000_000,
            max_unres: 200,
            stop_unres: 50,
            dweight: 1.0,
            rel_scale: true,
            dref: None,
            record: false,
            xlp: false,
            xlp_depth: 0,
            xobbt: 0,
            xstar: false,
            dsplit: f64::INFINITY,
            branch_wheel: true,
            rweight: 1.0,
            pisplit: 0.0,
            shave: 0,
        }
    }
}

pub struct Prob {
    pub sys: Sys,
    pub faces: Vec<FaceK>,
    pub nvar: usize,
    pub di: usize,
    pub nv: usize,
    pub root: Vec<Iv>,
    pub branch: Vec<bool>,
    /// variables of each face contractor (without d)
    pub fvars: Vec<Vec<usize>>,
    pub uses_uncertified: bool,
    pub cfg: Cfg,
    pub stars: Option<crate::xstar::Stars>,
    /// gluing tests (local.rs): Local and Pair
    pub local: Option<LocalCfg>,
}

/// Configuration of the gluing tests.
pub struct LocalCfg {
    pub geo: crate::local::Geo,
    /// targets and radius of Theorem C (None: no Local test)
    pub targets: Option<std::sync::Arc<crate::local::Targets>>,
    pub r: f64,
    /// Local is tried only on boxes with d.lo <= dmax (rad)
    pub dmax: f64,
    /// Pair test
    pub pair: bool,
    /// Close test
    pub close: bool,
}

/// Search tree token, depth-first preorder: Split(v, x) is followed by the subtree of
/// [lo, x] then the subtree of [x, hi] for variable v of the propagated box.
#[derive(Clone, Copy, Debug)]
pub enum Tok {
    Kill(Reason),
    Split(u16, f64),
    Unres,
    Budget,
}

#[derive(Clone, Debug, Default)]
pub struct Outcome {
    pub killed: bool,
    pub budget_hit: bool,
    /// search stopped early (node budget or `stop_unres` unresolved boxes)
    pub stopped: bool,
    pub nodes: u64,
    pub n_unres: u64,
    pub unres: Vec<Vec<Iv>>,
    /// hull of d over the unresolved (small) boxes
    pub dhull: Option<Iv>,
    /// hull of d over the boxes left open when the search stopped early, and their number
    pub dopen: Option<Iv>,
    pub n_open: u64,
    /// the boxes left open when the search stopped early (at most max_unres)
    pub open_boxes: Vec<Vec<Iv>>,
    /// sum of 2^-depth over the discarded leaves (fraction of the root tree done; diagnostics)
    pub done: f64,
    pub kills: [u64; NKINDS],
    pub cert: Vec<Tok>,
    pub max_depth: usize,
}

impl Prob {
    /// `dlo`, `dhi`: enclosure of the admissible range of d (radians). `iso`: full hexagons.
    pub fn new(fc: &Faces, p: &Params, dlo: f64, dhi: f64, cfg: Cfg, iso: Option<&[bool]>) -> Result<Prob, Reject> {
        let mut sys = Sys::default();
        let o = Opts { use_cuts: cfg.use_cuts, use_face_ineq: cfg.use_face_ineq };
        sys.build(fc, p, o, iso)?;
        let nvar = sys.nvar;
        let di = nvar;
        let mut nv = nvar + 1;
        let mut faces = Vec::with_capacity(fc.nf());
        for (f, cv) in sys.cvar.iter().enumerate() {
            let c: Vec<usize> = cv.iter().map(|&v| v as usize).collect();
            faces.push(match c.len() {
                3 => FaceK::Tri,
                4 => FaceK::Rhombus { x: c[0], y: c[1] },
                5 => FaceK::Pent { u: [c[0], c[1], c[2], c[3], c[4]] },
                6 => {
                    let full = iso.map_or(false, |h| h[f]);
                    let r = if full && cfg.use_wheel {
                        nv += 6;
                        Some(nv - 6)
                    } else {
                        None
                    };
                    FaceK::Hex { u: [c[0], c[1], c[2], c[3], c[4], c[5]], r }
                }
                _ => unreachable!(),
            });
        }
        let mut root = Vec::with_capacity(nv);
        for j in 0..nvar {
            root.push(Iv::new(sys.lo[j], sys.hi[j]));
        }
        root.push(Iv::new(dlo, dhi));
        while root.len() < nv {
            // r_i in [d, 3d] (Section 6.2)
            root.push(Iv::new(dlo, (3.0 * dhi).next_up()));
        }
        let mut branch = vec![true; nv];
        branch[0] = false; // a is a function of d
        if !cfg.branch_wheel {
            for j in di + 1..nv {
                branch[j] = false;
            }
        }
        let fvars: Vec<Vec<usize>> = faces
            .iter()
            .map(|fk| match fk {
                FaceK::Tri => vec![],
                FaceK::Rhombus { x, y } => vec![*x, *y],
                FaceK::Pent { u } => u.to_vec(),
                FaceK::Hex { u, r } => {
                    let mut v = u.to_vec();
                    if let Some(r0) = r {
                        v.extend(*r0..*r0 + 6);
                    }
                    v
                }
            })
            .collect();
        let uses_uncertified = sys.uses_uncertified;
        let stars = if cfg.xstar { Some(crate::xstar::Stars::new(fc, &sys.cvar)) } else { None };
        Ok(Prob { sys, faces, nvar, di, nv, root, branch, fvars, uses_uncertified, cfg, stars, local: None })
    }

    /// One pass of all contractors; Err on proven emptiness.
    /// `act`: variables that shrank significantly in the previous pass (None: first pass); a face
    /// contractor is skipped when none of its variables (nor d) is active, since it is a
    /// function of them and was already applied (skipping never affects soundness).
    fn pass(&self, sys: &mut Sys, b: &mut [Iv], act: Option<&[bool]>) -> Result<(), Reason> {
        PASSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        // linear rows
        for j in 0..self.nvar {
            sys.lo[j] = b[j].lo;
            sys.hi[j] = b[j].hi;
        }
        if fbbt(sys, self.cfg.lin_sweeps, 1e-13) == Fbbt::Infeasible {
            return Err(Reason::Lin);
        }
        for j in 0..self.nvar {
            b[j] = Iv::new(sys.lo[j], sys.hi[j]);
        }
        let di = self.di;
        // a <-> d
        let na = alpha_iv(b[di]);
        nar(b, 0, na).map_err(|_| Reason::Alpha)?;
        let nd = alpha_inv_iv(b[0]);
        nar(b, di, nd).map_err(|_| Reason::Alpha)?;
        for (f, fk) in self.faces.iter().enumerate() {
            let f16 = f as u16;
            if let Some(a) = act {
                if !a[di] && !self.fvars[f].iter().any(|&j| a[j]) {
                    continue;
                }
            }
            match fk {
                FaceK::Tri => {}
                FaceK::Rhombus { x, y } => {
                    let (x, y) = (*x, *y);
                    let e = Reason::Rho(f16);
                    let d = b[di];
                    let ny = crate::ivt::rho(b[x], d);
                    nar(b, y, ny).map_err(|_| e)?;
                    let nx = crate::ivt::rho(b[y], d);
                    nar(b, x, nx).map_err(|_| e)?;
                    let nd = rhombus_d(b[x], b[y]).map_err(|_| e)?;
                    nar(b, di, nd).map_err(|_| e)?;
                }
                FaceK::Pent { u } => {
                    for i in 0..5 {
                        let e = Reason::Pent(f16, i as u8);
                        pent_rot(b, u, i, di).map_err(|_| e)?;
                    }
                }
                FaceK::Hex { u, r } => {
                    for par in 0..2 {
                        let e = Reason::Hex(f16, par as u8);
                        hex_par(b, u, par, di).map_err(|_| e)?;
                    }
                    for j in 0..6 {
                        let e = Reason::HexDiag(f16, j as u8);
                        let (p, q) = (u[j], u[(j + 1) % 6]);
                        let lq = longdiag_lb(b[p], b[di]);
                        nar(b, q, Iv::new(lq, f64::INFINITY)).map_err(|_| e)?;
                        let lp = longdiag_lb(b[q], b[di]);
                        nar(b, p, Iv::new(lp, f64::INFINITY)).map_err(|_| e)?;
                    }
                    if let Some(r0) = r {
                        wheel(b, u, *r0, di).map_err(|_| Reason::Wheel(f16))?;
                    }
                }
            }
        }
        Ok(())
    }

    /// 3B shaving: for every branchable variable, a slice of 1/cfg.shave of its width at each end
    /// is propagated alone; a slice refuted by the contractors holds no solution and is removed
    /// (repeated while it succeeds, at most 4 times per end), then the box is propagated again.
    /// Err when a whole variable range is refuted.
    fn shave(&self, sys: &mut Sys, b: &mut [Iv]) -> Result<(), Reason> {
        let k = self.cfg.shave as f64;
        let mut changed = false;
        for j in 0..self.nv {
            if !self.branch[j] {
                continue;
            }
            for side in 0..2 {
                for _ in 0..4 {
                    let w = b[j].w();
                    if !(w > 1e-12) {
                        break;
                    }
                    let cut = if side == 0 { b[j].lo + w / k } else { b[j].hi - w / k };
                    let mut s = b.to_vec();
                    if side == 0 {
                        s[j].hi = cut;
                    } else {
                        s[j].lo = cut;
                    }
                    if self.propagate(sys, &mut s).is_ok() {
                        break;
                    }
                    if side == 0 {
                        b[j].lo = cut;
                    } else {
                        b[j].hi = cut;
                    }
                    changed = true;
                }
            }
        }
        if changed {
            self.propagate(sys, b)?;
        }
        Ok(())
    }

    /// Enables the gluing tests (local.rs). Needs the wheel variables of the full hexagons.
    pub fn set_local(&mut self, fc: &Faces, targets: Option<std::sync::Arc<crate::local::Targets>>, r: f64, dmax: f64, pair: bool) {
        let wheel: Vec<Option<usize>> = self.faces.iter().map(|fk| if let FaceK::Hex { r, .. } = fk { *r } else { None }).collect();
        let geo = crate::local::Geo::new(fc, &self.sys.cvar, &wheel, self.di);
        self.local = Some(LocalCfg { geo, targets, r, dmax, pair, close: false });
    }

    /// Propagation, then (with cfg.xlp, at depth >= cfg.xlp_depth) the LP kill test.
    pub fn check(&self, sys: &mut Sys, b: &mut [Iv], depth: usize) -> Result<(), Reason> {
        self.propagate(sys, b)?;
        if self.cfg.shave > 0 {
            self.shave(sys, b)?;
        }
        if let Some(st) = self.stars.as_ref() {
            st.kill(self, b).map_err(|_| Reason::Star)?;
        }
        if let Some(l) = self.local.as_ref() {
            let want_local = l.targets.is_some() && b[self.di].lo <= l.dmax;
            if want_local || l.pair || l.close {
                if let Some((pos, rho)) = l.geo.place(b) {
                    if l.pair && l.geo.pair_at(&pos, &rho, b) {
                        return Err(Reason::Pair);
                    }
                    if l.close && l.geo.close_at(&pos, &rho, b) {
                        return Err(Reason::Close);
                    }
                    if want_local && l.geo.local_at(&pos, &rho, l.targets.as_ref().unwrap(), l.r) {
                        return Err(Reason::Local);
                    }
                }
            }
        }
        if !(self.cfg.xlp && depth >= self.cfg.xlp_depth) {
            return Ok(());
        }
        if self.cfg.xobbt == 0 {
            return if crate::xlin::lp_kill(self, b) { Err(Reason::Lp) } else { Ok(()) };
        }
        let di = self.di;
        let vars: Vec<usize> = if self.cfg.xobbt == 1 { vec![di] } else { (1..=di).collect() };
        for _ in 0..3 {
            let w0: Vec<f64> = b.iter().map(|x| x.w()).collect();
            crate::xlin::lp_contract(self, b, &vars).map_err(|_| Reason::Lp)?;
            if !(0..=di).any(|j| b[j].w() < 0.7 * w0[j]) {
                break;
            }
            self.propagate(sys, b)?;
        }
        Ok(())
    }

    /// Propagate to a (loose) fixpoint.
    pub fn propagate(&self, sys: &mut Sys, b: &mut [Iv]) -> Result<(), Reason> {
        let mut w0: Vec<f64> = b.iter().map(|x| x.w()).collect();
        let mut act = vec![false; self.nv];
        for round in 0..self.cfg.max_rounds {
            self.pass(sys, b, if round == 0 { None } else { Some(&act) })?;
            let mut big = false;
            for j in 0..self.nv {
                let w = b[j].w();
                act[j] = w0[j] - w > self.cfg.shrink * w0[j] && w0[j] - w > 1e-14;
                big |= act[j];
                w0[j] = w;
            }
            if !big {
                break;
            }
        }
        Ok(())
    }

    fn pick(&self, b: &[Iv], scale: &[f64]) -> Option<usize> {
        if b[self.di].w() > self.cfg.dsplit {
            return Some(self.di);
        }
        let mut best = None;
        let mut bw = 0.0;
        let mut maxw = 0.0f64;
        for j in 0..self.nv {
            if !self.branch[j] {
                continue;
            }
            let w = b[j].w();
            maxw = maxw.max(w);
            let s = if j > self.di { w * scale[j] * self.cfg.rweight } else { w * scale[j] };
            if s > bw {
                bw = s;
                best = Some(j);
            }
        }
        if maxw < self.cfg.tol {
            None
        } else {
            best
        }
    }

    /// Branch-and-prune from the root box.
    pub fn solve(&self) -> Outcome {
        let mut out = Outcome::default();
        let mut sys = self.sys.clone();
        let mut rootb = self.root.clone();
        // scales: inverse widths of the propagated root box
        let mut scale = vec![1.0; self.nv];
        if let Err(r) = self.check(&mut sys, &mut rootb, 0) {
            out.killed = true;
            out.nodes = 1;
            out.kills[r.kind()] += 1;
            if self.cfg.record {
                out.cert.push(Tok::Kill(r));
            }
            return out;
        }
        for j in 0..self.nv {
            let w = rootb[j].w();
            scale[j] = if !self.cfg.rel_scale { 1.0 } else if w > 1e-12 { 1.0 / w } else { 1.0 };
        }
        if let (true, Some(r)) = (self.cfg.rel_scale, self.cfg.dref) {
            scale[self.di] = 1.0 / r;
        }
        scale[self.di] *= self.cfg.dweight;
        let hull = |h: &mut Option<Iv>, d: Iv| *h = Some(h.map_or(d, |x| x.hull(d)));
        // explicit stack: (box, depth, already propagated)
        let mut stack: Vec<(Vec<Iv>, usize, bool)> = vec![(rootb, 0, true)];
        while let Some((mut b, depth, done)) = stack.pop() {
            out.nodes += 1;
            out.max_depth = out.max_depth.max(depth);
            if !done {
                if let Err(r) = self.check(&mut sys, &mut b, depth) {
                    out.kills[r.kind()] += 1;
                    out.done += 0.5f64.powi(depth as i32);
                    if self.cfg.record {
                        out.cert.push(Tok::Kill(r));
                    }
                    continue;
                }
            }
            if out.nodes >= self.cfg.max_nodes || out.n_unres >= self.cfg.stop_unres {
                out.budget_hit = out.nodes >= self.cfg.max_nodes;
                out.stopped = true;
                hull(&mut out.dopen, b[self.di]);
                for (bb, _, _) in stack.iter() {
                    hull(&mut out.dopen, bb[self.di]);
                }
                out.n_open = 1 + stack.len() as u64;
                out.open_boxes.push(b.clone());
                for (bb, _, _) in stack.iter().rev().take(self.cfg.max_unres) {
                    out.open_boxes.push(bb.clone());
                }
                if self.cfg.record {
                    out.cert.push(Tok::Budget);
                }
                return out;
            }
            match self.pick(&b, &scale) {
                None => {
                    out.n_unres += 1;
                    hull(&mut out.dhull, b[self.di]);
                    if out.unres.len() < self.cfg.max_unres {
                        out.unres.push(b);
                    }
                    if self.cfg.record {
                        out.cert.push(Tok::Unres);
                    }
                }
                Some(j) => {
                    let mut x = b[j].mid();
                    let ps = self.cfg.pisplit;
                    if ps > 0.0 && j >= 1 && j < self.di && b[j].hi > PI_LO - 0.5 * ps && b[j].lo < PI_LO - 2.0 * ps {
                        x = PI_LO - ps;
                    }
                    if self.cfg.record {
                        out.cert.push(Tok::Split(j as u16, x));
                    }
                    let mut lo = b.clone();
                    lo[j].hi = x;
                    b[j].lo = x;
                    stack.push((b, depth + 1, false));
                    stack.push((lo, depth + 1, false));
                }
            }
        }
        out.killed = out.n_unres == 0;
        out
    }

    /// Replays a recorded tree: every Kill leaf must be refuted again by propagation from the box
    /// defined by the recorded splits. Returns the number of leaves checked, or the position of
    /// the first token that fails. The tree only has to partition the root box: a split point
    /// outside the current box (possible when the replay contracts differently, e.g. with another
    /// transcendental backend) sends the whole box to one side, the other side being empty.
    pub fn replay(&self, cert: &[Tok]) -> Result<usize, usize> {
        let mut sys = self.sys.clone();
        let mut pos = 0usize;
        let mut leaves = 0usize;
        // None: marker "skip the next recorded subtree" (child box empty, see below)
        let mut stack: Vec<Option<(Vec<Iv>, usize)>> = vec![Some((self.root.clone(), 0))];
        while let Some(top) = stack.pop() {
            let Some((mut b, depth)) = top else {
                pos = skip_subtree(cert, pos).ok_or(pos)?;
                continue;
            };
            let t = *cert.get(pos).ok_or(pos)?;
            let res = self.check(&mut sys, &mut b, depth);
            match t {
                Tok::Kill(_) => {
                    if res.is_ok() {
                        return Err(pos);
                    }
                    leaves += 1;
                }
                Tok::Split(j, x) => {
                    if res.is_err() {
                        // killed earlier than recorded: still a valid refutation of the subtree;
                        // skip the recorded subtree
                        pos = skip_subtree(cert, pos).ok_or(pos)?;
                        leaves += 1;
                        continue;
                    }
                    let j = j as usize;
                    if !(j < b.len()) || x.is_nan() {
                        return Err(pos);
                    }
                    if x < b[j].lo {
                        // [lo, x] is empty: skip its recorded subtree, the box goes to [x, hi]
                        pos = skip_subtree(cert, pos + 1).ok_or(pos)?;
                        stack.push(Some((b, depth + 1)));
                        continue;
                    }
                    if x > b[j].hi {
                        // [x, hi] is empty: the box goes to [lo, x], then its subtree is skipped
                        stack.push(None);
                        stack.push(Some((b, depth + 1)));
                        pos += 1;
                        continue;
                    }
                    let mut lo = b.clone();
                    lo[j].hi = x;
                    b[j].lo = x;
                    stack.push(Some((b, depth + 1)));
                    stack.push(Some((lo, depth + 1)));
                }
                Tok::Unres | Tok::Budget => return Err(pos),
            }
            pos += 1;
        }
        if pos != cert.len() {
            return Err(pos);
        }
        Ok(leaves)
    }
}

/// Text form of a search tree, one token per line, preorder: `S var xbits` (split of variable
/// `var` at the f64 whose IEEE bits are the hex `xbits`), `K kind face sub` (discard; kind as in
/// Reason::KINDS), `U` (unresolved), `B` (stopped).
pub fn cert_text(cert: &[Tok]) -> String {
    let mut s = String::with_capacity(16 * cert.len());
    for t in cert {
        match t {
            Tok::Split(v, x) => s.push_str(&format!("S {v} {:016x}\n", x.to_bits())),
            Tok::Kill(r) => {
                let (f, sub) = match *r {
                    Reason::Rho(f) | Reason::Wheel(f) => (f as i32, 0),
                    Reason::Pent(f, i) | Reason::Hex(f, i) | Reason::HexDiag(f, i) => (f as i32, i as i32),
                    _ => (-1, 0),
                };
                s.push_str(&format!("K {} {f} {sub}\n", Reason::KINDS[r.kind()]));
            }
            Tok::Unres => s.push_str("U\n"),
            Tok::Budget => s.push_str("B\n"),
        }
    }
    s
}

/// Inverse of `cert_text` (the face and sub-index of a discard are not needed by `replay` and are
/// kept only for the kinds that carry them).
pub fn parse_cert(s: &str) -> Result<Vec<Tok>, String> {
    let mut out = Vec::new();
    for l in s.lines() {
        let w: Vec<&str> = l.split_whitespace().collect();
        match w.first().copied() {
            Some("S") if w.len() == 3 => {
                let v: u16 = w[1].parse().map_err(|_| format!("bad split: {l}"))?;
                let x = f64::from_bits(u64::from_str_radix(w[2], 16).map_err(|_| format!("bad split: {l}"))?);
                out.push(Tok::Split(v, x));
            }
            Some("K") if w.len() == 4 => {
                let f: i32 = w[2].parse().map_err(|_| format!("bad kill: {l}"))?;
                let sub: i32 = w[3].parse().map_err(|_| format!("bad kill: {l}"))?;
                let (f, sub) = (f.max(0) as u16, sub.max(0) as u8);
                let r = match w[1] {
                    "lin" => Reason::Lin,
                    "alpha" => Reason::Alpha,
                    "rho" => Reason::Rho(f),
                    "pent" => Reason::Pent(f, sub),
                    "hex" => Reason::Hex(f, sub),
                    "hexdiag" => Reason::HexDiag(f, sub),
                    "wheel" => Reason::Wheel(f),
                    "bound" => Reason::Bound,
                    "lp" => Reason::Lp,
                    "star" => Reason::Star,
                    "local" => Reason::Local,
                    "pair" => Reason::Pair,
                    "close" => Reason::Close,
                    k => return Err(format!("unknown kind {k}")),
                };
                out.push(Tok::Kill(r));
            }
            Some("U") => out.push(Tok::Unres),
            Some("B") => out.push(Tok::Budget),
            _ => return Err(format!("bad token line: {l}")),
        }
    }
    Ok(out)
}

/// Position after the subtree starting at `pos` (preorder).
fn skip_subtree(cert: &[Tok], mut pos: usize) -> Option<usize> {
    // `open` counts the subtrees still to be skipped; a Split replaces itself by its two children.
    // A tree is read in preorder: each Split is followed by the subtree of its lower half and
    // then that of its upper half.
    let mut open = 1usize;
    while open > 0 {
        match cert.get(pos)? {
            Tok::Split(..) => open += 2,
            _ => {}
        }
        open -= 1;
        pos += 1;
    }
    Some(pos)
}

/// Intersect b[j] with n; Err on empty intersection; unusable n (NaN) ignored.
#[inline]
fn nar(b: &mut [Iv], j: usize, n: Iv) -> Result<(), ()> {
    if !usable(n) {
        return Ok(());
    }
    let lo = b[j].lo.max(n.lo);
    let hi = b[j].hi.min(n.hi);
    if lo > hi {
        return Err(());
    }
    b[j] = Iv::new(lo, hi);
    Ok(())
}

/// Corner evaluation with monotonicity. `dirs[k][j]` is +1 (-1) when output k is non-decreasing
/// (non-increasing) in input j on the whole box, 0 when unknown. `ends[j]` = (lo end, hi end)
/// of input j: sub-intervals that contain the points where a monotone output reaches its extreme
/// values over the input interval (points, except near pi, see `corner_ends`). For each output
/// the lower bound is read at the corner where every monotone input sits at its minimising end
/// (unknown inputs keep their interval), the upper bound at the opposite corner. `eval` must be
/// an enclosure of the (clamped) formula on any sub-box. Results are cached per corner.
fn mono_bounds<const K: usize>(inp: &[Iv; K], ends: &[(Iv, Iv); K], dirs: &[[i8; K]; 3], eval: &dyn Fn(&[Iv; K]) -> [Iv; 3]) -> [Iv; 3] {
    let mut cache: [Option<[Iv; 3]>; 27] = [None; 27];
    let mut get = |sel: [u8; K]| -> [Iv; 3] {
        let mut code = 0usize;
        for j in 0..K {
            code = 3 * code + sel[j] as usize;
        }
        if let Some(v) = cache[code] {
            return v;
        }
        let mut x = *inp;
        for j in 0..K {
            x[j] = match sel[j] {
                0 => ends[j].0,
                1 => ends[j].1,
                _ => inp[j],
            };
        }
        let v = eval(&x);
        cache[code] = Some(v);
        v
    };
    let mut out = [Iv::pt(0.0); 3];
    for k in 0..3 {
        let mut slo = [2u8; K];
        let mut shi = [2u8; K];
        for j in 0..K {
            match dirs[k][j] {
                1 => {
                    slo[j] = 0;
                    shi[j] = 1;
                }
                -1 => {
                    slo[j] = 1;
                    shi[j] = 0;
                }
                _ => {}
            }
        }
        out[k] = Iv::new(get(slo)[k].lo, get(shi)[k].hi);
    }
    out
}

/// Ends of a corner-angle input u (0 < u <= PI_HI). The base e(u) = 2 asin(sin d sin(u/2)) of the
/// isosceles triangle is increasing on (0, pi] and symmetric about pi. The hi end is the point hi
/// when hi <= PI_LO, else the interval [max(lo, PI_LO), hi], which contains min(hi, pi), where e is
/// largest. The lo end is the point lo when lo + hi <= 2 pi (then e(hi) = e(2 pi - hi) >= e(lo), so
/// e is smallest at lo), else the whole interval (only when u lies within rounding of pi).
fn corner_ends(u: Iv) -> (Iv, Iv) {
    let hi_end = if u.hi <= PI_LO { pt(u.hi) } else { Iv::new(u.lo.max(PI_LO), u.hi) };
    let lo_end = if (u.lo + u.hi).next_up() <= 2.0 * PI_LO { pt(u.lo) } else { u };
    (lo_end, hi_end)
}

/// Direction of C(u) = beta(u, d) + G(e(u, d), ...) in the corner angle u, where
/// dG/de = -cot(X)/sin(e) (X = angle of the middle triangle opposite the side held fixed):
/// dC/du = -sin d (cos d sin(u/2) + cot X cos(u/2)) / (2 sin(e/2) cos^2(e/2)) for u in (0, 2 pi)
/// (Appendix B.1, T5 and T6). Returns -1 when dC/du <= 0 on the box: either u <= PI_LO and
/// beta + X <= pi (then cos d sin(u/2) + cot X cos(u/2) = cos(u/2) sin(beta + X)/(sin beta sin X)
/// >= 0), or the bracket is positive by direct interval evaluation (valid past pi). Else 0.
fn dec_dir(u: Iv, beta_plus_x: Iv, x: Iv, d: Iv) -> i8 {
    if u.hi <= PI_LO && beta_plus_x.hi <= PI_LO {
        return -1;
    }
    let h = u.scale(0.5);
    let s = d.cos().mul(h.sin()).add(x.cos().div(x.sin()).mul(h.cos()));
    if usable(s) && s.lo > 0.0 {
        -1
    } else {
        0
    }
}

/// Pentagon fan from A_i as a function of (u_{i+1}, u_{i-1}) with d fixed to its interval:
/// outputs (u_i, u_{i+2}, u_{i-2}), clamped formula (never fails).
fn pent_eval_c(x: &[Iv; 2], d: Iv) -> [Iv; 3] {
    let (e, b1) = (iso_base(x[0], d), iso_angle(x[0], d));
    let (f, b3) = (iso_base(x[1], d), iso_angle(x[1], d));
    [b1.add(tri_angle_c(d, e, f)).add(b3), b1.add(tri_angle_c(f, e, d)), b3.add(tri_angle_c(e, f, d))]
}

/// Pentagon, fan from A_i: triangles A_i A_{i+1} A_{i+2} (apex u_{i+1}), A_i A_{i-1} A_{i-2}
/// (apex u_{i-1}), middle triangle A_i A_{i+2} A_{i-2} with sides e, f, d.
/// Monotonicity (Appendix B.1, T5 and T6): u_i is non-increasing in u_{i+1} when b1 + F <= pi on the
/// box (F = middle angle at A_{i+2}, so b1 + F is the formula for u_{i+2}), and in u_{i-1} when
/// b3 + E <= pi; u_{i+2} is non-decreasing in u_{i-1} and non-increasing in u_{i+1} when
/// b1 + G_i <= pi; symmetrically for u_{i-2}.
fn pent_rot(b: &mut [Iv], u: &[usize; 5], i: usize, di: usize) -> Result<(), ()> {
    let d = b[di];
    let (ip, im, ipp, imm) = (u[(i + 1) % 5], u[(i + 4) % 5], u[(i + 2) % 5], u[(i + 3) % 5]);
    let (up, um) = (b[ip], b[im]);
    let e = iso_base(up, d);
    let b1 = iso_angle(up, d);
    let f = iso_base(um, d);
    let b3 = iso_angle(um, d);
    let gi = tri_angle(d, e, f)?;
    let gp = tri_angle(f, e, d)?;
    let gm = tri_angle(e, f, d)?;
    let nat = [b1.add(gi).add(b3), b1.add(gp), b3.add(gm)];
    let dirs = [
        [dec_dir(up, nat[1], gp, d), dec_dir(um, nat[2], gm, d)],
        [dec_dir(up, b1.add(gi), gi, d), 1],
        [1, dec_dir(um, b3.add(gi), gi, d)],
    ];
    let ends = [corner_ends(up), corner_ends(um)];
    let mo = mono_bounds(&[up, um], &ends, &dirs, &|x| pent_eval_c(x, d));
    nar(b, u[i], nat[0].meet(mo[0]))?;
    nar(b, ipp, nat[1].meet(mo[1]))?;
    nar(b, imm, nat[2].meet(mo[2]))?;
    Ok(())
}

/// Hexagon, inputs (u_1, u_3, u_5) (relabelled), outputs (u_0, u_2, u_4), clamped formula.
fn hex_eval_c(x: &[Iv; 3], d: Iv) -> [Iv; 3] {
    let (e1, b1) = (iso_base(x[0], d), iso_angle(x[0], d));
    let (e3, b3) = (iso_base(x[1], d), iso_angle(x[1], d));
    let (e5, b5) = (iso_base(x[2], d), iso_angle(x[2], d));
    [
        b5.add(tri_angle_c(e3, e1, e5)).add(b1),
        b1.add(tri_angle_c(e5, e1, e3)).add(b3),
        b3.add(tri_angle_c(e1, e3, e5)).add(b5),
    ]
}

/// Hexagon: corners k(1), k(3), k(5) with k(j) = u[(j + par) % 6] give the diagonals of the
/// middle triangle A_0 A_2 A_4 (relabelled) and hence the corners k(0), k(2), k(4).
/// Monotonicity (T9): u_0 is non-decreasing in u_3, non-increasing in u_1 when b1 + g2 <= pi and
/// in u_5 when b5 + g4 <= pi (g_j = middle angle at A_j); cyclically for u_2, u_4.
fn hex_par(b: &mut [Iv], u: &[usize; 6], par: usize, di: usize) -> Result<(), ()> {
    let d = b[di];
    let k = |j: usize| u[(j + par) % 6];
    let (u1, u3, u5) = (b[k(1)], b[k(3)], b[k(5)]);
    let (e1, b1) = (iso_base(u1, d), iso_angle(u1, d));
    let (e3, b3) = (iso_base(u3, d), iso_angle(u3, d));
    let (e5, b5) = (iso_base(u5, d), iso_angle(u5, d));
    let g0 = tri_angle(e3, e1, e5)?;
    let g2 = tri_angle(e5, e1, e3)?;
    let g4 = tri_angle(e1, e3, e5)?;
    let nat = [b5.add(g0).add(b1), b1.add(g2).add(b3), b3.add(g4).add(b5)];
    let dirs = [
        [dec_dir(u1, b1.add(g2), g2, d), 1, dec_dir(u5, b5.add(g4), g4, d)],
        [dec_dir(u1, b1.add(g0), g0, d), dec_dir(u3, b3.add(g4), g4, d), 1],
        [1, dec_dir(u3, b3.add(g2), g2, d), dec_dir(u5, b5.add(g0), g0, d)],
    ];
    let ends = [corner_ends(u1), corner_ends(u3), corner_ends(u5)];
    let mo = mono_bounds(&[u1, u3, u5], &ends, &dirs, &|x| hex_eval_c(x, d));
    nar(b, k(0), nat[0].meet(mo[0]))?;
    nar(b, k(2), nat[1].meet(mo[1]))?;
    nar(b, k(4), nat[2].meet(mo[2]))?;
    Ok(())
}

/// Wheel around the isolated vertex P of a full hexagon: r_i = |P A_i| in [d, 3d],
/// theta_i = angle A_i P A_{i+1} (opposite side d), sum theta_i = 2 pi,
/// u_i = angle(P A_i A_{i-1}) + angle(P A_i A_{i+1}).
fn wheel(b: &mut [Iv], u: &[usize; 6], r0: usize, di: usize) -> Result<(), ()> {
    let d = b[di];
    for i in 0..6 {
        nar(b, r0 + i, Iv::new(d.lo, d.scale(3.0).hi))?;
    }
    let mut th = [Iv::pt(0.0); 6];
    for i in 0..6 {
        th[i] = tri_angle(d, b[r0 + i], b[r0 + (i + 1) % 6])?;
    }
    let mut s = Iv::pt(0.0);
    for t in th.iter() {
        s = s.add(*t);
    }
    if s.hi < TWO_PI_LO || s.lo > TWO_PI_HI {
        return Err(());
    }
    for i in 0..6 {
        let (ip, im) = (r0 + (i + 1) % 6, r0 + (i + 5) % 6);
        let ri = b[r0 + i];
        let a1 = tri_angle(b[ip], ri, d)?; // angle P A_i A_{i+1}
        let a2 = tri_angle(b[im], ri, d)?; // angle P A_i A_{i-1}
        nar(b, u[i], a1.add(a2))?;
        // backward: angle P A_i A_{i+1} = u_i - angle P A_i A_{i-1}, then r_{i+1} is the side
        // opposite it in the triangle with sides r_i, d
        let rp = side(ri, d, b[u[i]].sub(a2))?;
        nar(b, ip, rp)?;
        let rm = side(ri, d, b[u[i]].sub(a1))?;
        nar(b, im, rm)?;
    }
    Ok(())
}

/// Reads `dlo` and `dhi` (radians, decimal enclosures) from a parameter file.
pub fn read_drange(path: &str) -> (f64, f64) {
    let s = std::fs::read_to_string(path).expect("cannot read params");
    let mut lo = None;
    let mut hi = None;
    for line in s.lines() {
        let t: Vec<&str> = line.split_whitespace().collect();
        if t.len() >= 2 && t[0] == "dlo" {
            lo = Some(crate::iv::parse_dn(t[1]));
        }
        if t.len() >= 2 && t[0] == "dhi" {
            hi = Some(crate::iv::parse_up(t[1]));
        }
    }
    (lo.expect("no dlo"), hi.expect("no dhi"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poly;

    #[test]
    fn skip_subtree_counts_both_children() {
        let k = || Tok::Kill(Reason::Lin);
        let s = || Tok::Split(1, 0.5);
        assert_eq!(skip_subtree(&[k()], 0), Some(1));
        assert_eq!(skip_subtree(&[s(), k(), k()], 0), Some(3));
        assert_eq!(skip_subtree(&[s(), s(), k(), k(), k()], 0), Some(5));
        assert_eq!(skip_subtree(&[s(), k(), s(), k(), k(), k()], 0), Some(5));
        assert_eq!(skip_subtree(&[s(), k(), k(), k()], 1), Some(2));
        assert_eq!(skip_subtree(&[s(), k()], 0), None);
    }

    #[test]
    fn isosceles_and_triangle() {
        let d = 1.0f64;
        let a = poly::alpha(d);
        // equilateral: apex alpha gives base d and base angle alpha
        let e = iso_base(pt(a), pt(d));
        assert!(e.lo <= d + 1e-12 && e.hi >= d - 1e-12, "{e:?}");
        let be = iso_angle(pt(a), pt(d));
        assert!(be.lo <= a + 1e-12 && be.hi >= a - 1e-12, "{be:?}");
        let g = tri_angle(pt(d), pt(d), pt(d)).unwrap();
        assert!(g.contains(a) || (g.lo - a).abs() < 1e-12, "{g:?} {a}");
        // triangle inequality violated
        assert!(tri_angle(pt(2.5), pt(1.0), pt(1.0)).is_err());
        assert!(tri_angle(pt(0.1), pt(1.0), pt(1.5)).is_err());
        let ai = alpha_inv_iv(pt(a));
        assert!(ai.lo <= d && d <= ai.hi, "{ai:?}");
    }

    /// Random convex equilateral pentagons and hexagons (floating construction): every true
    /// configuration must survive the contractors (soundness smoke test).
    #[test]
    fn faces_contain_true_configurations() {
        let mut seed = 12345u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((seed >> 11) as f64) / ((1u64 << 53) as f64)
        };
        let mut tested = [0usize; 2];
        for _ in 0..20000 {
            let d = 0.93 + 0.1 * rnd();
            let m = if rnd() < 0.5 { 5 } else { 6 };
            let params: Vec<f64> = (0..m - 3).map(|_| 1.2 + 1.9 * rnd()).collect();
            let Some((vs, ang)) = poly::build(m, d, &params) else { continue };
            if !poly::valid_face(d, &vs, &ang, 0.0) {
                continue;
            }
            tested[m - 5] += 1;
            let mut b: Vec<Iv> = ang.iter().map(|&x| Iv::new(x - 1e-9, x + 1e-9)).collect();
            b.push(Iv::new(d - 1e-12, d + 1e-12));
            let di = m;
            if m == 5 {
                let u = [0, 1, 2, 3, 4];
                for i in 0..5 {
                    pent_rot(&mut b, &u, i, di).expect("pentagon refuted a true configuration");
                }
            } else {
                let u = [0, 1, 2, 3, 4, 5];
                for par in 0..2 {
                    hex_par(&mut b, &u, par, di).expect("hexagon refuted a true configuration");
                }
                for j in 0..6 {
                    let lq = longdiag_lb(b[u[j]], b[di]);
                    assert!(lq <= b[u[(j + 1) % 6]].hi, "long diagonal bound");
                    let lp = longdiag_lb(b[u[(j + 1) % 6]], b[di]);
                    assert!(lp <= b[u[j]].hi, "long diagonal bound");
                }
            }
            for (j, &x) in ang.iter().enumerate() {
                assert!(b[j].lo <= x + 1e-9 && x - 1e-9 <= b[j].hi);
            }
            // contraction is effective: a corner released to [1, pi] is recovered
            let k = (rnd() * m as f64) as usize % m;
            b[k] = Iv::new(1.0, 3.2);
            for _ in 0..2 {
                if m == 5 {
                    for i in 0..5 {
                        pent_rot(&mut b, &[0, 1, 2, 3, 4], i, m).unwrap();
                    }
                } else {
                    for par in 0..2 {
                        hex_par(&mut b, &[0, 1, 2, 3, 4, 5], par, m).unwrap();
                    }
                }
            }
            assert!(b[k].w() < 1e-6 && b[k].contains(ang[k]), "{m} {k} {:?} {}", b[k], ang[k]);
        }
        assert!(tested[0] > 100 && tested[1] > 100, "{tested:?}");
    }

    /// Face contractors on random wide boxes around true configurations (tests the monotonicity
    /// arguments of pent_rot / hex_par, including boxes that reach past pi).
    #[test]
    fn faces_wide_boxes() {
        let mut seed = 4242u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((seed >> 11) as f64) / ((1u64 << 53) as f64)
        };
        let mut tested = [0usize; 2];
        for _ in 0..40000 {
            let d = 0.93 + 0.1 * rnd();
            let m = if rnd() < 0.5 { 5 } else { 6 };
            let params: Vec<f64> = (0..m - 3).map(|_| 1.2 + 1.9 * rnd()).collect();
            let Some((vs, ang)) = poly::build(m, d, &params) else { continue };
            if !poly::valid_face(d, &vs, &ang, 0.0) {
                continue;
            }
            tested[m - 5] += 1;
            let scale = [0.001, 0.01, 0.1, 0.4][(rnd() * 4.0) as usize % 4];
            let mut b: Vec<Iv> = ang
                .iter()
                .map(|&x| {
                    let (l, h) = (scale * rnd(), scale * rnd());
                    Iv::new(x - l, x + h)
                })
                .collect();
            let (l, h) = (0.02 * scale * rnd(), 0.02 * scale * rnd());
            b.push(Iv::new(d - l, d + h));
            for _ in 0..3 {
                if m == 5 {
                    for i in 0..5 {
                        pent_rot(&mut b, &[0, 1, 2, 3, 4], i, m).expect("pentagon refuted a true configuration (wide box)");
                    }
                } else {
                    for par in 0..2 {
                        hex_par(&mut b, &[0, 1, 2, 3, 4, 5], par, m).expect("hexagon refuted a true configuration (wide box)");
                    }
                }
            }
            for (j, &x) in ang.iter().enumerate() {
                assert!(b[j].contains(x), "m {m} corner {j}: {:?} lost {x}", b[j]);
            }
        }
        assert!(tested[0] > 1000 && tested[1] > 500, "{tested:?}");
    }

    /// Monotonicity signs of the pentagon fan, checked by finite differences at random points.
    #[test]
    fn pentagon_monotonicity_fd() {
        let mut seed = 31337u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((seed >> 11) as f64) / ((1u64 << 53) as f64)
        };
        let f = |up: f64, um: f64, d: f64| {
            let r = pent_eval_c(&[pt(up), pt(um)], pt(d));
            [r[0].mid(), r[1].mid(), r[2].mid()]
        };
        let mut n = 0;
        for _ in 0..20000 {
            let d = 0.93 + 0.1 * rnd();
            let (up, um) = (1.2 + 1.9 * rnd(), 1.2 + 1.9 * rnd());
            let v = f(up, um, d);
            if v.iter().any(|&x| x >= std::f64::consts::PI - 1e-3) {
                continue;
            }
            let h = 1e-6;
            let dp = f(up + h, um, d);
            let dm = f(up, um + h, d);
            // u_i decreasing in both; u_{i+2} decreasing in u_{i+1}, increasing in u_{i-1};
            // u_{i-2} increasing in u_{i+1}, decreasing in u_{i-1} (all angles < pi here)
            assert!(dp[0] <= v[0] + 1e-12 && dm[0] <= v[0] + 1e-12, "u_i");
            assert!(dp[1] <= v[1] + 1e-12 && dm[1] >= v[1] - 1e-12, "u_i+2");
            assert!(dp[2] >= v[2] - 1e-12 && dm[2] <= v[2] + 1e-12, "u_i-2");
            n += 1;
        }
        assert!(n > 1000, "{n}");
    }

    /// tri_angle and side on random boxes: values at random points of the box are enclosed.
    #[test]
    fn box_enclosures() {
        let mut seed = 99u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((seed >> 11) as f64) / ((1u64 << 53) as f64)
        };
        let mut n_ok = 0;
        for _ in 0..20000 {
            let mut bx = [Iv::pt(0.0); 3];
            for k in 0..3 {
                let c = 0.3 + 2.5 * rnd();
                let w = 0.3 * rnd() * rnd();
                bx[k] = Iv::new(c, c + w);
            }
            let ta = tri_angle(bx[0], bx[1], bx[2]);
            let sd = side(bx[0], bx[1], bx[2]);
            for _ in 0..20 {
                let x: Vec<f64> = (0..3).map(|k| bx[k].lo + (bx[k].hi - bx[k].lo) * rnd()).collect();
                let h = (x[0].cos() - x[1].cos() * x[2].cos()) / (x[1].sin() * x[2].sin());
                if h.abs() <= 1.0 {
                    let g = h.acos();
                    let t = ta.expect("tri_angle refuted a realisable triangle");
                    assert!(t.lo <= g + 1e-13 && g <= t.hi + 1e-13, "{bx:?} {x:?} {g} {t:?}");
                    n_ok += 1;
                }
                if x[2] <= std::f64::consts::PI {
                    let a = (x[0].cos() * x[1].cos() + x[0].sin() * x[1].sin() * x[2].cos()).clamp(-1.0, 1.0).acos();
                    let s = sd.expect("side refuted a valid angle");
                    assert!(s.lo <= a + 1e-13 && a <= s.hi + 1e-13, "{bx:?} {x:?} {a} {s:?}");
                }
            }
        }
        assert!(n_ok > 10000, "{n_ok}");
    }

    /// Wheel: a hexagon with a point P inside at distance >= d from all corners.
    #[test]
    fn wheel_contains_true_configurations() {
        let mut seed = 777u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((seed >> 11) as f64) / ((1u64 << 53) as f64)
        };
        let mut tested = 0;
        for _ in 0..200000 {
            let d = 0.93 + 0.1 * rnd();
            let params: Vec<f64> = (0..3).map(|_| 1.8 + 1.3 * rnd()).collect();
            let Some((vs, ang)) = poly::build(6, d, &params) else { continue };
            if !poly::valid_face(d, &vs, &ang, 0.0) {
                continue;
            }
            // random interior point: normalized convex combination
            let w: Vec<f64> = (0..6).map(|_| rnd()).collect();
            let mut p = [0.0; 3];
            for i in 0..6 {
                p = poly::add(&p, &poly::scale(&vs[i], w[i]));
            }
            let p = poly::norm(&p);
            let r: Vec<f64> = vs.iter().map(|v| poly::dist(&p, v)).collect();
            if r.iter().any(|&x| x < d) {
                continue;
            }
            tested += 1;
            let mut b: Vec<Iv> = ang.iter().map(|&x| Iv::new(x - 1e-9, x + 1e-9)).collect();
            b.push(Iv::new(d - 1e-12, d + 1e-12));
            for &x in &r {
                b.push(Iv::new(x - 1e-9, x + 1e-9));
            }
            wheel(&mut b, &[0, 1, 2, 3, 4, 5], 7, 6).expect("wheel refuted a true configuration");
            // wide boxes
            let sc = [0.001, 0.01, 0.1, 0.3][(rnd() * 4.0) as usize % 4];
            let mut truth: Vec<f64> = ang.clone();
            truth.push(d);
            truth.extend(r.iter().copied());
            let mut w: Vec<Iv> = truth.iter().enumerate().map(|(j, &x)| { let s = if j == 6 { 0.02 * sc } else { sc }; Iv::new(x - s * rnd(), x + s * rnd()) }).collect();
            for _ in 0..3 {
                wheel(&mut w, &[0, 1, 2, 3, 4, 5], 7, 6).expect("wheel refuted a true configuration (wide box)");
            }
            for (j, &x) in truth.iter().enumerate() {
                assert!(w[j].contains(x), "wheel var {j}: {:?} lost {x}", w[j]);
            }
        }
        assert!(tested > 50, "{tested}");
    }
}

#[cfg(test)]
mod bench {
    use super::*;
    /// cargo test --release -p tammes15 --lib bench -- --ignored --nocapture
    #[test]
    #[ignore]
    fn contractor_costs() {
        let d = Iv::new(1.0, 1.0001);
        let mut b: Vec<Iv> = vec![Iv::new(1.9, 2.0), Iv::new(2.2, 2.3), Iv::new(2.0, 2.2), Iv::new(2.1, 2.2), Iv::new(2.3, 2.4), d];
        let n = 100000;
        let t = std::time::Instant::now();
        let mut s = 0.0;
        for k in 0..n {
            let x = pt(1.0 + 1e-9 * k as f64);
            s += tri_angle(x, Iv::new(1.6, 1.7), Iv::new(1.5, 1.6)).unwrap().lo;
        }
        eprintln!("tri_angle: {:.3} us", t.elapsed().as_secs_f64() * 1e6 / n as f64);
        let t = std::time::Instant::now();
        for k in 0..n {
            s += iso_base(Iv::new(2.0, 2.0 + 1e-9 * k as f64), d).lo + iso_angle(Iv::new(2.0, 2.1), d).lo;
        }
        eprintln!("iso pair: {:.3} us", t.elapsed().as_secs_f64() * 1e6 / n as f64);
        let t = std::time::Instant::now();
        for k in 0..n {
            s += Iv::new(1.0, 1.0 + 1e-9 * k as f64).cos().lo;
        }
        eprintln!("Iv::cos: {:.3} us", t.elapsed().as_secs_f64() * 1e6 / n as f64);
        let t = std::time::Instant::now();
        for _ in 0..n / 10 {
            let mut bb = b.clone();
            let _ = pent_rot(&mut bb, &[0, 1, 2, 3, 4], 0, 5);
            s += bb[0].lo;
        }
        eprintln!("pent_rot: {:.3} us", t.elapsed().as_secs_f64() * 1e6 / (n / 10) as f64);
        b[0] = Iv::new(1.9, 2.0);
        eprintln!("{s}");
    }
}
