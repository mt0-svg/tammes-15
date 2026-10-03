import Tammes15.Contractors.Arith
import Tammes15.PaperSteps.SearchDefs

/-!
# The contractors of the program, written over its arithmetic (Definition B.1(2) of the paper)

Each definition transcribes one function of code/impl1/rust/src (deep.rs, ivt.rs, system.rs),
line for line, over an arbitrary arithmetic `R : Rnd`: every interval operation of the Rust code is
the corresponding field of `R`, every comparison of floats is `Fl.le` or `Fl.lt`, every `max` and
`min` of floats is `Fl.max` or `Fl.min`, and an early `Err` is `none`. The memo cache of
`mono_bounds` is left out (it returns what it stored).

Two places differ from the Rust code that wrote the certificates, by a guard (Appendix B.1 of the
paper; the program of this repository carries both, code/impl1/deep-guards.patch):

* `triAngleSt` returns the no-information interval `[0, PI_HI]` when one of its three input
  intervals is not inside `(0, PI_LO)` (the monotonicity it uses needs sines of the sides positive
  on the whole box; the program passes computed enclosures of diagonals there). This leaves the
  result unchanged whenever the enclosures are tight;
* `side` reads the cosine of the upper end of the angle as `-1` when that end is at least `PI_LO`
  (the side is increasing in the angle on `[0, π]` only; the program evaluates it at `PI_HI`). This
  leaves the result unchanged when the enclosures are tight and the enclosure of `sin b sin c` is
  positive. When that enclosure is not positive, the exact `-1` can raise the lower end of `qmin`
  above the unguarded value and so narrow the result. This narrowing is sound: the soundness proved
  here is about the guarded code, in either case.

Boxes are the boxes of `PaperSteps.Search` over the variables `PVar P k`; a box variable is read as
the interval of its two real ends (`ivOf`), and `nar` writes the real values of finite float ends
back.
-/

namespace Tammes15.Contractors

open Real
open scoped Classical
open Tammes15 Tammes15.PaperSteps Tammes15.PaperSteps.Search

variable (R : Rnd)

/-! ## Helpers -/

/-- `x.scale(c)`, which is `x.mul(Iv::pt(c))`. -/
noncomputable def Rnd.scale (I : Iv) (c : ℝ) : Iv := R.mul I (Iv.pt (.ofReal c))

/-- The interval of a box variable. -/
noncomputable def ivOf {ι : Type} (B : Box ι) (j : ι) : Iv := Iv.ofReal (B.lo j) (B.hi j)

/-- deep.rs `nar`: intersect variable `j` with `n` (ignored when `n` is not usable); `none` on an
empty intersection. -/
noncomputable def nar {ι : Type} (B : Box ι) (j : ι) (n : Iv) : Option (Box ι) :=
  if ¬ n.Usable then some B
  else
    if Fl.lt (Fl.min (.ofReal (B.hi j)) n.hi) (Fl.max (.ofReal (B.lo j)) n.lo) then none
    else some ⟨Function.update B.lo j (Fl.max (.ofReal (B.lo j)) n.lo).toReal,
      Function.update B.hi j (Fl.min (.ofReal (B.hi j)) n.hi).toReal⟩

/-! ## Spherical trigonometry on intervals (deep.rs) -/

/-- deep.rs `iso_base`: `2 asin(sin d sin(u/2))`. -/
noncomputable def isoBase (u d : Iv) : Iv :=
  R.scale (R.asin (R.mul (R.sin d) (R.sin (R.scale u 0.5)))) 2

/-- deep.rs `iso_angle`: `atan(cos(x/2) / (cos d sin(x/2)))` at the two ends of `u`. -/
noncomputable def isoAngle (u d : Iv) : Iv :=
  let cd := R.cos d
  let f := fun x : Fl =>
    let h := R.scale (Iv.pt x) 0.5
    R.atan (R.div (R.cos h) (R.mul cd (R.sin h)))
  ⟨(f u.hi).lo, (f u.lo).hi⟩

/-- The guard of `triAngleSt`: the interval lies inside `(0, PI_LO)`. -/
def InOpen (I : Iv) : Prop := Fl.lt (.ofReal 0) I.lo ∧ Fl.lt I.hi (.ofReal R.piLo)

/-- deep.rs `tri_angle_st` (with the guard `InOpen` on the three inputs): `ok` an enclosure of the
angle opposite `g`, or `error v` when no triangle with sides in the box exists, `v` the value of
the clamped formula there. -/
noncomputable def triAngleSt (g e f : Iv) : Except Iv Iv :=
  if ¬ (InOpen R g ∧ InOpen R e ∧ InOpen R f) then .ok ⟨.ofReal 0, .ofReal R.piHi⟩
  else
    let h := fun g e f : Iv =>
      R.div (R.sub (R.cos g) (R.mul (R.cos e) (R.cos f))) (R.mul (R.sin e) (R.sin f))
    let gc := R.cos g
    let nf := R.sub (R.cos f) (R.mul gc (R.cos e))
    let ne := R.sub (R.cos e) (R.mul gc (R.cos f))
    let ee : Iv × Iv :=
      if Fl.lt (.ofReal 0) nf.lo then (Iv.pt e.hi, Iv.pt e.lo)
      else if Fl.lt nf.hi (.ofReal 0) then (Iv.pt e.lo, Iv.pt e.hi) else (e, e)
    let ff : Iv × Iv :=
      if Fl.lt (.ofReal 0) ne.lo then (Iv.pt f.hi, Iv.pt f.lo)
      else if Fl.lt ne.hi (.ofReal 0) then (Iv.pt f.lo, Iv.pt f.hi) else (f, f)
    let hmax := h (Iv.pt g.lo) ee.1 ff.1
    let hmin := h (Iv.pt g.hi) ee.2 ff.2
    if ¬ Fl.le hmax.hi Fl.inf ∨ ¬ Fl.le Fl.ninf hmin.lo then .ok ⟨.ofReal 0, .ofReal R.piHi⟩
    else if Fl.lt hmax.hi (.ofReal (-1)) then .error ⟨.ofReal R.piLo, .ofReal R.piHi⟩
    else if Fl.lt (.ofReal 1) hmin.lo then .error (Iv.pt (.ofReal 0))
    else .ok ⟨Fl.max (R.acos (Iv.pt (Fl.min hmax.hi (.ofReal 1)))).lo (.ofReal 0),
      (R.acos (Iv.pt (Fl.max hmin.lo (.ofReal (-1))))).hi⟩

/-- deep.rs `tri_angle`: `none` when no triangle with sides in the box exists. -/
noncomputable def triAngle (g e f : Iv) : Option Iv := (triAngleSt R g e f).toOption

/-- deep.rs `tri_angle_c`: the clamped formula, defined on the whole box. -/
noncomputable def triAngleC (g e f : Iv) : Iv :=
  match triAngleSt R g e f with
  | .ok v => v
  | .error v => v

/-- deep.rs `alpha_iv`: `α` at the two ends of `d`. -/
noncomputable def alphaIv (d : Iv) : Iv :=
  let f := fun x : Fl =>
    let c := R.cos (Iv.pt x)
    R.acos (R.div c (R.add c (Iv.pt (.ofReal 1))))
  ⟨(f d.lo).lo, (f d.hi).hi⟩

/-- deep.rs `alpha_inv_iv`: `α⁻¹(a) = acos(cos a / (1 - cos a))` at the two ends of `a`. -/
noncomputable def alphaInvIv (a : Iv) : Iv :=
  let f := fun x : Fl =>
    let c := R.cos (Iv.pt x)
    R.acos (R.div c (R.sub (Iv.pt (.ofReal 1)) c))
  ⟨(f a.lo).lo, (f a.hi).hi⟩

/-- ivt.rs `rho`: the other angle `2 atan(1 / (tan(x/2) cos d))` of a rhombus, at the corners
`(x.hi, d.lo)` and `(x.lo, d.hi)`. -/
noncomputable def rhoIv (x d : Iv) : Iv :=
  let f := fun xx dd : Fl =>
    let t := R.tan (R.scale (Iv.pt xx) 0.5)
    let kk := R.cos (Iv.pt dd)
    let z := R.mul t kk
    R.scale (R.atan (R.div (Iv.pt (.ofReal 1)) z)) 2
  ⟨(f x.hi d.lo).lo, (f x.lo d.hi).hi⟩

/-- deep.rs `rhombus_d`: the side `acos(cot(x/2) cot(y/2))` of a rhombus from its angles; `none`
when `cot(x/2) cot(y/2) > 1` on the whole box. -/
noncomputable def rhombusD (x y : Iv) : Option Iv :=
  let cot := fun t : Fl =>
    let h := R.scale (Iv.pt t) 0.5
    R.div (R.cos h) (R.sin h)
  let pmax := R.mul (cot x.lo) (cot y.lo)
  let pmin := R.mul (cot x.hi) (cot y.hi)
  if ¬ pmax.Usable ∨ ¬ pmin.Usable then some ⟨.ofReal 0, .ofReal R.piHi⟩
  else if Fl.lt (.ofReal 1) pmin.lo then none
  else some ⟨(R.acos (Iv.pt (Fl.min pmax.hi (.ofReal 1)))).lo,
    (R.acos (Iv.pt (Fl.max pmin.lo (.ofReal (-1))))).hi⟩

/-- deep.rs `side` (with the guard at `PI_LO`): the side opposite the angle `ang` in the triangle
with sides `b`, `c` around it; `none` when the angle clamped to `[0, PI_HI]` is empty. -/
noncomputable def side (b c ang : Iv) : Option Iv :=
  let a : Iv := ⟨Fl.max ang.lo (.ofReal 0), Fl.min ang.hi (.ofReal R.piHi)⟩
  if ¬ Fl.le a.lo a.hi then none
  else
    let qc := fun (b c ca : Iv) =>
      R.add (R.mul (R.cos b) (R.cos c)) (R.mul (R.mul (R.sin b) (R.sin c)) ca)
    let ca := R.cos a
    let sb := R.sub (R.mul (R.sin b) (R.cos c)) (R.mul (R.mul (R.cos b) (R.sin c)) ca)
    let sc := R.sub (R.mul (R.sin c) (R.cos b)) (R.mul (R.mul (R.cos c) (R.sin b)) ca)
    let bb : Iv × Iv :=
      if Fl.lt (.ofReal 0) sb.lo then (Iv.pt b.lo, Iv.pt b.hi)
      else if Fl.lt sb.hi (.ofReal 0) then (Iv.pt b.hi, Iv.pt b.lo) else (b, b)
    let cc : Iv × Iv :=
      if Fl.lt (.ofReal 0) sc.lo then (Iv.pt c.lo, Iv.pt c.hi)
      else if Fl.lt sc.hi (.ofReal 0) then (Iv.pt c.hi, Iv.pt c.lo) else (c, c)
    let qmax := qc bb.1 cc.1 (R.cos (Iv.pt a.lo))
    let qmin := qc bb.2 cc.2
      (if Fl.le (.ofReal R.piLo) a.hi then Iv.pt (.ofReal (-1)) else R.cos (Iv.pt a.hi))
    if ¬ qmax.Usable ∨ ¬ qmin.Usable then some ⟨.ofReal 0, .ofReal R.piHi⟩
    else some ⟨Fl.max (R.acos (Iv.pt (Fl.min qmax.hi (.ofReal 1)))).lo (.ofReal 0),
      (R.acos (Iv.pt (Fl.max qmin.lo (.ofReal (-1))))).hi⟩

/-- deep.rs `longdiag_lb`: `L(u.hi, d) = β(u.hi, d) + acos(cot d tan(e/2))`, a lower bound of
the corner next to `u` (`-∞` when an enclosure is not usable). -/
noncomputable def longdiagLb (u d : Iv) : Fl :=
  let up := Iv.pt u.hi
  let e := isoBase R up d
  let b := isoAngle R up d
  let arg := R.mul (R.div (R.cos d) (R.sin d)) (R.tan (R.scale e 0.5))
  if ¬ arg.Usable ∨ ¬ b.Usable then Fl.ninf
  else (R.add b (Iv.pt (R.acos (Iv.pt (Fl.min arg.hi (.ofReal 1)))).lo)).lo

/-! ## Corner evaluation by monotonicity (deep.rs) -/

/-- deep.rs `corner_ends`: the lower and the upper end of a corner input. -/
noncomputable def cornerEnds (u : Iv) : Iv × Iv :=
  (if Fl.le (R.addUp u.lo u.hi) (.ofReal (2 * R.piLo)) then Iv.pt u.lo else u,
    if Fl.le u.hi (.ofReal R.piLo) then Iv.pt u.hi else ⟨Fl.max u.lo (.ofReal R.piLo), u.hi⟩)

/-- deep.rs `dec_dir`: `-1` when `C(u) = β(u, d) + G(e(u, d), ...)` is non-increasing in `u` on
the box, `0` otherwise. -/
noncomputable def decDir (u bx x d : Iv) : ℤ :=
  if Fl.le u.hi (.ofReal R.piLo) ∧ Fl.le bx.hi (.ofReal R.piLo) then -1
  else
    let h := R.scale u 0.5
    let s := R.add (R.mul (R.cos d) (R.sin h)) (R.mul (R.div (R.cos x) (R.sin x)) (R.cos h))
    if s.Usable ∧ Fl.lt (.ofReal 0) s.lo then -1 else 0

/-- deep.rs `mono_bounds`: for each output `k`, the lower end of the evaluation at the corner where
every input of known direction sits at its minimising end (the others keep their interval), and the
upper end of the evaluation at the opposite corner. -/
noncomputable def monoBounds {K : ℕ} (inp : Fin K → Iv) (ends : Fin K → Iv × Iv)
    (dirs : Fin 3 → Fin K → ℤ) (eval : (Fin K → Iv) → Fin 3 → Iv) : Fin 3 → Iv :=
  fun k =>
    let sel := fun (low : Bool) (j : Fin K) =>
      if dirs k j = 1 then (if low then (ends j).1 else (ends j).2)
      else if dirs k j = -1 then (if low then (ends j).2 else (ends j).1)
      else inp j
    ⟨(eval (sel true) k).lo, (eval (sel false) k).hi⟩

/-- deep.rs `pent_eval_c`: the pentagon fan as a function of `(u_{i+1}, u_{i-1})`, clamped. -/
noncomputable def pentEvalC (d : Iv) (x : Fin 2 → Iv) : Fin 3 → Iv :=
  let e := isoBase R (x 0) d
  let b1 := isoAngle R (x 0) d
  let f := isoBase R (x 1) d
  let b3 := isoAngle R (x 1) d
  ![R.add (R.add b1 (triAngleC R d e f)) b3, R.add b1 (triAngleC R f e d),
    R.add b3 (triAngleC R e f d)]

/-- deep.rs `hex_eval_c`: the hexagon as a function of `(u_1, u_3, u_5)`, clamped. -/
noncomputable def hexEvalC (d : Iv) (x : Fin 3 → Iv) : Fin 3 → Iv :=
  let e1 := isoBase R (x 0) d
  let b1 := isoAngle R (x 0) d
  let e3 := isoBase R (x 1) d
  let b3 := isoAngle R (x 1) d
  let e5 := isoBase R (x 2) d
  let b5 := isoAngle R (x 2) d
  ![R.add (R.add b5 (triAngleC R e3 e1 e5)) b1, R.add (R.add b1 (triAngleC R e5 e1 e3)) b3,
    R.add (R.add b3 (triAngleC R e1 e3 e5)) b5]

/-! ## The contractors on a box of a case -/

variable {P : PlaneGraph} {k : ℕ}

/-- The variable of the corner `j` steps along the face of `e`. -/
noncomputable def fv (e : P.G.Dart) (j : ℕ) : PVar P k := cvar ((P.R.face ^ j) e)

/-- deep.rs `pass`, `a ↔ d`, first half: `a := α(d)`. -/
noncomputable def alphaStep (B : Box (PVar P k)) : Option (Box (PVar P k)) :=
  nar B .a (alphaIv R (ivOf B .d))

/-- deep.rs `pass`, `a ↔ d`, second half: `d := α⁻¹(a)`. -/
noncomputable def alphaInvStep (B : Box (PVar P k)) : Option (Box (PVar P k)) :=
  nar B .d (alphaInvIv R (ivOf B .a))

/-- deep.rs `pass`, rhombus, `y = ρ(x, d)` and `x = ρ(y, d)`: the corner after `e` from the corner
of `e`. -/
noncomputable def rhoStep (B : Box (PVar P k)) (e : P.G.Dart) : Option (Box (PVar P k)) :=
  nar B (fv e 1) (rhoIv R (ivOf B (fv e 0)) (ivOf B .d))

/-- deep.rs `pass`, rhombus, `d = acos(cot(x/2) cot(y/2))`. -/
noncomputable def rhoDStep (B : Box (PVar P k)) (e : P.G.Dart) : Option (Box (PVar P k)) :=
  (rhombusD R (ivOf B (fv e 0)) (ivOf B (fv e 1))).bind (nar B .d)

/-- deep.rs `pent_rot`: the fan of a pentagon from the corner of `e` (`u_i`), from
`u_{i+1}`, `u_{i-1}` and `d`, narrowing `u_i`, `u_{i+2}`, `u_{i-2}`. -/
noncomputable def pentStep (B : Box (PVar P k)) (e : P.G.Dart) : Option (Box (PVar P k)) :=
  let d := ivOf B .d
  let up := ivOf B (fv e 1)
  let um := ivOf B (fv e 4)
  let ee := isoBase R up d
  let b1 := isoAngle R up d
  let ff := isoBase R um d
  let b3 := isoAngle R um d
  match triAngle R d ee ff, triAngle R ff ee d, triAngle R ee ff d with
  | some gi, some gp, some gm =>
    let nat := ![R.add (R.add b1 gi) b3, R.add b1 gp, R.add b3 gm]
    let dirs : Fin 3 → Fin 2 → ℤ :=
      ![![decDir R up (nat 1) gp d, decDir R um (nat 2) gm d],
        ![decDir R up (R.add b1 gi) gi d, 1],
        ![1, decDir R um (R.add b3 gi) gi d]]
    let mo := monoBounds ![up, um] ![cornerEnds R up, cornerEnds R um] dirs (pentEvalC R d)
    (nar B (fv e 0) ((nat 0).meet (mo 0))).bind fun B₁ =>
      (nar B₁ (fv e 2) ((nat 1).meet (mo 1))).bind fun B₂ =>
        nar B₂ (fv e 3) ((nat 2).meet (mo 2))
  | _, _, _ => none

/-- deep.rs `hex_par`: the corners `k(1), k(3), k(5)` of the hexagon of `e` (`k(j)` the corner
`j` steps after `e`) give the triangle `A₀A₂A₄` and the corners `k(0), k(2), k(4)`. -/
noncomputable def hexStep (B : Box (PVar P k)) (e : P.G.Dart) : Option (Box (PVar P k)) :=
  let d := ivOf B .d
  let u1 := ivOf B (fv e 1)
  let u3 := ivOf B (fv e 3)
  let u5 := ivOf B (fv e 5)
  let e1 := isoBase R u1 d
  let b1 := isoAngle R u1 d
  let e3 := isoBase R u3 d
  let b3 := isoAngle R u3 d
  let e5 := isoBase R u5 d
  let b5 := isoAngle R u5 d
  match triAngle R e3 e1 e5, triAngle R e5 e1 e3, triAngle R e1 e3 e5 with
  | some g0, some g2, some g4 =>
    let nat := ![R.add (R.add b5 g0) b1, R.add (R.add b1 g2) b3, R.add (R.add b3 g4) b5]
    let dirs : Fin 3 → Fin 3 → ℤ :=
      ![![decDir R u1 (R.add b1 g2) g2 d, 1, decDir R u5 (R.add b5 g4) g4 d],
        ![decDir R u1 (R.add b1 g0) g0 d, decDir R u3 (R.add b3 g4) g4 d, 1],
        ![1, decDir R u3 (R.add b3 g2) g2 d, decDir R u5 (R.add b5 g0) g0 d]]
    let mo := monoBounds ![u1, u3, u5] ![cornerEnds R u1, cornerEnds R u3, cornerEnds R u5] dirs
      (hexEvalC R d)
    (nar B (fv e 0) ((nat 0).meet (mo 0))).bind fun B₁ =>
      (nar B₁ (fv e 2) ((nat 1).meet (mo 1))).bind fun B₂ =>
        nar B₂ (fv e 4) ((nat 2).meet (mo 2))
  | _, _, _ => none

/-- deep.rs `pass`, long diagonals of a hexagon, forward: the corner after `e` is at least
`L(u, d)`, `u` the corner of `e`. -/
noncomputable def diagFwdStep (B : Box (PVar P k)) (e : P.G.Dart) : Option (Box (PVar P k)) :=
  nar B (fv e 1) ⟨longdiagLb R (ivOf B (fv e 0)) (ivOf B .d), Fl.inf⟩

/-- deep.rs `pass`, long diagonals of a hexagon, backward: the corner of `e` is at least `L(u, d)`,
`u` the corner after `e`. -/
noncomputable def diagBwdStep (B : Box (PVar P k)) (e : P.G.Dart) : Option (Box (PVar P k)) :=
  nar B (fv e 0) ⟨longdiagLb R (ivOf B (fv e 1)) (ivOf B .d), Fl.inf⟩

/-- One turn of the last loop of deep.rs `wheel`, at the corner `i` of the hexagon of the free point
`m`: the corner from the two wheel angles at it, then `r_{i+1}` and `r_{i-1}` back from the corner
by `side`. -/
noncomputable def wheelTurn (H : HexChoice P k) (m : Fin k) (d : Iv) (B : Box (PVar P k))
    (i : Fin 6) : Option (Box (PVar P k)) :=
  let u : PVar P k := fv (H.base m) i
  let ri := ivOf B (.r m i)
  (triAngle R (ivOf B (.r m (i + 1))) ri d).bind fun a1 =>
  (triAngle R (ivOf B (.r m (i - 1))) ri d).bind fun a2 =>
  (nar B u (R.add a1 a2)).bind fun B₂ =>
  (side R ri d (R.sub (ivOf B₂ u) a2)).bind fun rp =>
  (nar B₂ (.r m (i + 1)) rp).bind fun B₃ =>
  (side R ri d (R.sub (ivOf B₃ u) a1)).bind fun rm =>
  nar B₃ (.r m (i - 1)) rm

/-- deep.rs `wheel` for the free point `m` (the hexagon of `H.base m`): `d ≤ r_i ≤ 3d`, the six
angles at the free point sum to `2π`, each corner is the sum of the two wheel angles at it, and the
distances back from the corners. -/
noncomputable def wheelStep (H : HexChoice P k) (m : Fin k) (B : Box (PVar P k)) :
    Option (Box (PVar P k)) :=
  let d := ivOf B .d
  ((List.finRange 6).foldlM (fun B' i => nar B' (.r m i) ⟨d.lo, (R.scale d 3).hi⟩) B).bind
    fun B₁ =>
  ((List.finRange 6).mapM fun i => triAngle R d (ivOf B₁ (.r m i)) (ivOf B₁ (.r m (i + 1)))).bind
    fun th =>
  let s := th.foldl R.add (Iv.pt (.ofReal 0))
  if Fl.lt s.hi (.ofReal R.twoPiLo) ∨ Fl.lt (.ofReal R.twoPiHi) s.lo then none
  else (List.finRange 6).foldlM (wheelTurn R H m d) B₁

/-! ## The linear rows (system.rs) -/

/-- A row `lo ≤ Σ c_j v_j ≤ hi` of system.rs `Sys`, its terms in the program's order. -/
structure Row (ι : Type) where
  terms : List (ι × ℝ)
  lo : Fl
  hi : Fl

/-- The linear form of a row at the values `x`. -/
def Row.form {ι : Type} (r : Row ι) (x : ι → ℝ) : ℝ := (r.terms.map fun t => t.2 * x t.1).sum

/-- iv.rs `cmin`: a lower bound of `c x` over `[l, u]`. -/
noncomputable def cmin (c l u : ℝ) : Fl :=
  if 0 ≤ c then R.mulDn (.ofReal c) (.ofReal l) else R.mulDn (.ofReal c) (.ofReal u)

/-- iv.rs `cmax`: an upper bound of `c x` over `[l, u]`. -/
noncomputable def cmax (c l u : ℝ) : Fl :=
  if 0 ≤ c then R.mulUp (.ofReal c) (.ofReal u) else R.mulUp (.ofReal c) (.ofReal l)

/-- The second loop of system.rs `fbbt` over a row: each term `(v, c)` with its bounds `mn`, `mx`
read at the start of the row, against the sums `smin`, `smax` of all of them. -/
noncomputable def rowUpd {ι : Type} (r : Row ι) (smin smax : Fl) :
    List ((ι × ℝ) × Fl × Fl) → Box ι → Option (Box ι)
  | [], B => some B
  | ((v, c), mn, mx) :: l, B =>
    if c = 0 then rowUpd r smin smax l B
    else
      let omin := R.subDn smin mn
      let omax := R.subUp smax mx
      let cup := if r.hi.IsFinite then R.subUp r.hi omin else Fl.inf
      let cdn := if r.lo.IsFinite then R.subDn r.lo omax else Fl.ninf
      let nlo := if 0 < c then (if cdn.IsFinite then R.divDn cdn (.ofReal c) else Fl.ninf)
        else (if cup.IsFinite then R.divDn cup (.ofReal c) else Fl.ninf)
      let nhi := if 0 < c then (if cup.IsFinite then R.divUp cup (.ofReal c) else Fl.inf)
        else (if cdn.IsFinite then R.divUp cdn (.ofReal c) else Fl.inf)
      let lo' := if Fl.lt (.ofReal (B.lo v)) nlo then nlo.toReal else B.lo v
      let hi' := if Fl.lt nhi (.ofReal (B.hi v)) then nhi.toReal else B.hi v
      if hi' < lo' then none
      else rowUpd r smin smax l ⟨Function.update B.lo v lo', Function.update B.hi v hi'⟩

/-- system.rs `fbbt`, one row: the bounds of the terms and their sums with downward and upward
rounding, the infeasibility test, then the update of every variable of the row. -/
noncomputable def rowStep {ι : Type} (r : Row ι) (B : Box ι) : Option (Box ι) :=
  let mn := r.terms.map fun t => cmin R t.2 (B.lo t.1) (B.hi t.1)
  let mx := r.terms.map fun t => cmax R t.2 (B.lo t.1) (B.hi t.1)
  let smin := mn.foldl R.addDn (.ofReal 0)
  let smax := mx.foldl R.addUp (.ofReal 0)
  if Fl.lt r.hi smin ∨ Fl.lt smax r.lo then none
  else rowUpd R r smin smax (r.terms.zip (mn.zip mx)) B

end Tammes15.Contractors
