/-!
# A computable copy of Prims.lean over exact rationals (the differential test, Section 10.4 of the paper)

`Tammes15.Contractors.Prims` is noncomputable: its floats are extended reals, its box ends are
reals and its tests are classical. This module copies every definition of Prims.lean, line for
line, over types that Lean can run:

* `FlQ`: a float as an exact rational (`fin`), `top` (`∞`), `bot` (`-∞`) or `nan`;
* `IvQ`, `BoxQ`, `RowQ`: intervals, boxes with rational ends, rows with rational coefficients;
* `RndQ`: the arithmetic, a record of functions as `Rnd` (in the differential test, a table of the
  values the Rust program computed).

Commute.lean embeds these types into `Fl`, `Iv`, `Box` and `Row` and proves that each definition
here commutes with the embedding: running a definition of this module runs the definition of the
same name in Prims.lean at the arithmetic `lift R`. The steps on a box take the indices of their
variables as arguments (`v j` for the corner `j` steps along the face, `jd` for `d`) in place of
the variables `fv e j` and `.d` of a plane graph; Commute.lean states the steps of Prims.lean through
these.

This module imports only the Lean core, so that the test driver compiles without Mathlib.
-/

namespace Tammes15.Contractors.Q

/-- A float of the program read exactly: a finite value as a rational, `∞`, `-∞` or NaN. The two
zeros are one value, as in `Fl`. -/
inductive FlQ
  | fin (q : Rat)
  | top
  | bot
  | nan
  deriving DecidableEq, Inhabited, Repr

namespace FlQ

/-- IEEE `a ≤ b`, false when either side is NaN. -/
def ble : FlQ → FlQ → Bool
  | fin p, fin q => decide (p ≤ q)
  | bot, fin _ => true
  | bot, top => true
  | bot, bot => true
  | fin _, top => true
  | top, top => true
  | _, _ => false

/-- IEEE `a < b`, false when either side is NaN. -/
def blt : FlQ → FlQ → Bool
  | fin p, fin q => decide (p < q)
  | bot, fin _ => true
  | bot, top => true
  | fin _, top => true
  | _, _ => false

/-- `Fl.le`. -/
abbrev le (a b : FlQ) : Prop := ble a b = true

/-- `Fl.lt`. -/
abbrev lt (a b : FlQ) : Prop := blt a b = true

/-- `Fl.max` (`f64::max`: the other argument when one is NaN). -/
def max : FlQ → FlQ → FlQ
  | nan, b => b
  | a, nan => a
  | a, b => if ble a b then b else a

/-- `Fl.min` (`f64::min`: the other argument when one is NaN). -/
def min : FlQ → FlQ → FlQ
  | nan, b => b
  | a, nan => a
  | a, b => if ble a b then a else b

/-- `f64::is_finite`, as a boolean. -/
def isFin : FlQ → Bool
  | fin _ => true
  | _ => false

/-- `Fl.IsFinite`. -/
abbrev IsFinite (x : FlQ) : Prop := x.isFin = true

/-- `Fl.toReal`: the value of a finite float, `0` for the others. -/
def toQ : FlQ → Rat
  | fin q => q
  | _ => 0

/-- `Fl.inf`. -/
abbrev inf : FlQ := top

/-- `Fl.ninf`. -/
abbrev ninf : FlQ := bot

end FlQ

/-- `Iv`: two float ends. -/
structure IvQ where
  lo : FlQ
  hi : FlQ
  deriving DecidableEq, Inhabited, Repr

namespace IvQ

/-- `Iv.pt`. -/
def pt (x : FlQ) : IvQ := ⟨x, x⟩

/-- `Iv.ofReal`. -/
def ofQ (lo hi : Rat) : IvQ := ⟨.fin lo, .fin hi⟩

/-- `Iv.Usable`. -/
abbrev Usable (I : IvQ) : Prop := FlQ.le I.lo I.hi

/-- `Iv.meet`. -/
def meet (I J : IvQ) : IvQ := ⟨FlQ.max I.lo J.lo, FlQ.min I.hi J.hi⟩

end IvQ

/-- `Rnd`: the operations of the program as functions. -/
structure RndQ where
  add : IvQ → IvQ → IvQ
  sub : IvQ → IvQ → IvQ
  mul : IvQ → IvQ → IvQ
  div : IvQ → IvQ → IvQ
  cos : IvQ → IvQ
  sin : IvQ → IvQ
  acos : IvQ → IvQ
  asin : IvQ → IvQ
  atan : IvQ → IvQ
  tan : IvQ → IvQ
  addDn : FlQ → FlQ → FlQ
  addUp : FlQ → FlQ → FlQ
  subDn : FlQ → FlQ → FlQ
  subUp : FlQ → FlQ → FlQ
  mulDn : FlQ → FlQ → FlQ
  mulUp : FlQ → FlQ → FlQ
  divDn : FlQ → FlQ → FlQ
  divUp : FlQ → FlQ → FlQ
  piLo : Rat
  piHi : Rat
  twoPiLo : Rat
  twoPiHi : Rat

/-- `Box`: rational ends. -/
structure BoxQ (ι : Type) where
  lo : ι → Rat
  hi : ι → Rat

/-- `Function.update` on rational ends. -/
def updQ {ι : Type} [DecidableEq ι] (f : ι → Rat) (j : ι) (v : Rat) : ι → Rat :=
  fun i => if i = j then v else f i

/-- `![a, b]`. -/
def vec2 {α : Type} (a b : α) : Fin 2 → α
  | ⟨0, _⟩ => a
  | _ => b

/-- `![a, b, c]`. -/
def vec3 {α : Type} (a b c : α) : Fin 3 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | _ => c

variable (R : RndQ)

/-- `Rnd.scale`. -/
def RndQ.scale (I : IvQ) (c : Rat) : IvQ := R.mul I (IvQ.pt (.fin c))

/-- `ivOf`. -/
def ivOf {ι : Type} (B : BoxQ ι) (j : ι) : IvQ := IvQ.ofQ (B.lo j) (B.hi j)

/-- `nar`. -/
def nar {ι : Type} [DecidableEq ι] (B : BoxQ ι) (j : ι) (n : IvQ) : Option (BoxQ ι) :=
  if ¬ n.Usable then some B
  else
    if FlQ.lt (FlQ.min (.fin (B.hi j)) n.hi) (FlQ.max (.fin (B.lo j)) n.lo) then none
    else some ⟨updQ B.lo j (FlQ.max (.fin (B.lo j)) n.lo).toQ,
      updQ B.hi j (FlQ.min (.fin (B.hi j)) n.hi).toQ⟩

/-- `isoBase`. -/
def isoBase (u d : IvQ) : IvQ :=
  R.scale (R.asin (R.mul (R.sin d) (R.sin (R.scale u (1 / 2))))) 2

/-- `isoAngle`. -/
def isoAngle (u d : IvQ) : IvQ :=
  let cd := R.cos d
  let f := fun x : FlQ =>
    let h := R.scale (IvQ.pt x) (1 / 2)
    R.atan (R.div (R.cos h) (R.mul cd (R.sin h)))
  ⟨(f u.hi).lo, (f u.lo).hi⟩

/-- `InOpen`. -/
abbrev InOpen (I : IvQ) : Prop := FlQ.lt (.fin 0) I.lo ∧ FlQ.lt I.hi (.fin R.piLo)

/-- `triAngleSt`. -/
def triAngleSt (g e f : IvQ) : Except IvQ IvQ :=
  if ¬ (InOpen R g ∧ InOpen R e ∧ InOpen R f) then .ok ⟨.fin 0, .fin R.piHi⟩
  else
    let h := fun g e f : IvQ =>
      R.div (R.sub (R.cos g) (R.mul (R.cos e) (R.cos f))) (R.mul (R.sin e) (R.sin f))
    let gc := R.cos g
    let nf := R.sub (R.cos f) (R.mul gc (R.cos e))
    let ne := R.sub (R.cos e) (R.mul gc (R.cos f))
    let ee : IvQ × IvQ :=
      if FlQ.lt (.fin 0) nf.lo then (IvQ.pt e.hi, IvQ.pt e.lo)
      else if FlQ.lt nf.hi (.fin 0) then (IvQ.pt e.lo, IvQ.pt e.hi) else (e, e)
    let ff : IvQ × IvQ :=
      if FlQ.lt (.fin 0) ne.lo then (IvQ.pt f.hi, IvQ.pt f.lo)
      else if FlQ.lt ne.hi (.fin 0) then (IvQ.pt f.lo, IvQ.pt f.hi) else (f, f)
    let hmax := h (IvQ.pt g.lo) ee.1 ff.1
    let hmin := h (IvQ.pt g.hi) ee.2 ff.2
    if ¬ FlQ.le hmax.hi FlQ.inf ∨ ¬ FlQ.le FlQ.ninf hmin.lo then .ok ⟨.fin 0, .fin R.piHi⟩
    else if FlQ.lt hmax.hi (.fin (-1)) then .error ⟨.fin R.piLo, .fin R.piHi⟩
    else if FlQ.lt (.fin 1) hmin.lo then .error (IvQ.pt (.fin 0))
    else .ok ⟨FlQ.max (R.acos (IvQ.pt (FlQ.min hmax.hi (.fin 1)))).lo (.fin 0),
      (R.acos (IvQ.pt (FlQ.max hmin.lo (.fin (-1))))).hi⟩

/-- `triAngle`. -/
def triAngle (g e f : IvQ) : Option IvQ := (triAngleSt R g e f).toOption

/-- `triAngleC`. -/
def triAngleC (g e f : IvQ) : IvQ :=
  match triAngleSt R g e f with
  | .ok v => v
  | .error v => v

/-- `alphaIv`. -/
def alphaIv (d : IvQ) : IvQ :=
  let f := fun x : FlQ =>
    let c := R.cos (IvQ.pt x)
    R.acos (R.div c (R.add c (IvQ.pt (.fin 1))))
  ⟨(f d.lo).lo, (f d.hi).hi⟩

/-- `alphaInvIv`. -/
def alphaInvIv (a : IvQ) : IvQ :=
  let f := fun x : FlQ =>
    let c := R.cos (IvQ.pt x)
    R.acos (R.div c (R.sub (IvQ.pt (.fin 1)) c))
  ⟨(f a.lo).lo, (f a.hi).hi⟩

/-- `rhoIv`. -/
def rhoIv (x d : IvQ) : IvQ :=
  let f := fun xx dd : FlQ =>
    let t := R.tan (R.scale (IvQ.pt xx) (1 / 2))
    let kk := R.cos (IvQ.pt dd)
    let z := R.mul t kk
    R.scale (R.atan (R.div (IvQ.pt (.fin 1)) z)) 2
  ⟨(f x.hi d.lo).lo, (f x.lo d.hi).hi⟩

/-- `rhombusD`. -/
def rhombusD (x y : IvQ) : Option IvQ :=
  let cot := fun t : FlQ =>
    let h := R.scale (IvQ.pt t) (1 / 2)
    R.div (R.cos h) (R.sin h)
  let pmax := R.mul (cot x.lo) (cot y.lo)
  let pmin := R.mul (cot x.hi) (cot y.hi)
  if ¬ pmax.Usable ∨ ¬ pmin.Usable then some ⟨.fin 0, .fin R.piHi⟩
  else if FlQ.lt (.fin 1) pmin.lo then none
  else some ⟨(R.acos (IvQ.pt (FlQ.min pmax.hi (.fin 1)))).lo,
    (R.acos (IvQ.pt (FlQ.max pmin.lo (.fin (-1))))).hi⟩

/-- `side`. -/
def side (b c ang : IvQ) : Option IvQ :=
  let a : IvQ := ⟨FlQ.max ang.lo (.fin 0), FlQ.min ang.hi (.fin R.piHi)⟩
  if ¬ FlQ.le a.lo a.hi then none
  else
    let qc := fun (b c ca : IvQ) =>
      R.add (R.mul (R.cos b) (R.cos c)) (R.mul (R.mul (R.sin b) (R.sin c)) ca)
    let ca := R.cos a
    let sb := R.sub (R.mul (R.sin b) (R.cos c)) (R.mul (R.mul (R.cos b) (R.sin c)) ca)
    let sc := R.sub (R.mul (R.sin c) (R.cos b)) (R.mul (R.mul (R.cos c) (R.sin b)) ca)
    let bb : IvQ × IvQ :=
      if FlQ.lt (.fin 0) sb.lo then (IvQ.pt b.lo, IvQ.pt b.hi)
      else if FlQ.lt sb.hi (.fin 0) then (IvQ.pt b.hi, IvQ.pt b.lo) else (b, b)
    let cc : IvQ × IvQ :=
      if FlQ.lt (.fin 0) sc.lo then (IvQ.pt c.lo, IvQ.pt c.hi)
      else if FlQ.lt sc.hi (.fin 0) then (IvQ.pt c.hi, IvQ.pt c.lo) else (c, c)
    let qmax := qc bb.1 cc.1 (R.cos (IvQ.pt a.lo))
    let qmin := qc bb.2 cc.2
      (if FlQ.le (.fin R.piLo) a.hi then IvQ.pt (.fin (-1)) else R.cos (IvQ.pt a.hi))
    if ¬ qmax.Usable ∨ ¬ qmin.Usable then some ⟨.fin 0, .fin R.piHi⟩
    else some ⟨FlQ.max (R.acos (IvQ.pt (FlQ.min qmax.hi (.fin 1)))).lo (.fin 0),
      (R.acos (IvQ.pt (FlQ.max qmin.lo (.fin (-1))))).hi⟩

/-- `longdiagLb`. -/
def longdiagLb (u d : IvQ) : FlQ :=
  let up := IvQ.pt u.hi
  let e := isoBase R up d
  let b := isoAngle R up d
  let arg := R.mul (R.div (R.cos d) (R.sin d)) (R.tan (R.scale e (1 / 2)))
  if ¬ arg.Usable ∨ ¬ b.Usable then FlQ.ninf
  else (R.add b (IvQ.pt (R.acos (IvQ.pt (FlQ.min arg.hi (.fin 1)))).lo)).lo

/-- `cornerEnds`. -/
def cornerEnds (u : IvQ) : IvQ × IvQ :=
  (if FlQ.le (R.addUp u.lo u.hi) (.fin (2 * R.piLo)) then IvQ.pt u.lo else u,
    if FlQ.le u.hi (.fin R.piLo) then IvQ.pt u.hi else ⟨FlQ.max u.lo (.fin R.piLo), u.hi⟩)

/-- `decDir`. -/
def decDir (u bx x d : IvQ) : Int :=
  if FlQ.le u.hi (.fin R.piLo) ∧ FlQ.le bx.hi (.fin R.piLo) then -1
  else
    let h := R.scale u (1 / 2)
    let s := R.add (R.mul (R.cos d) (R.sin h)) (R.mul (R.div (R.cos x) (R.sin x)) (R.cos h))
    if s.Usable ∧ FlQ.lt (.fin 0) s.lo then -1 else 0

/-- `monoBounds`. -/
def monoBounds {K : Nat} (inp : Fin K → IvQ) (ends : Fin K → IvQ × IvQ)
    (dirs : Fin 3 → Fin K → Int) (eval : (Fin K → IvQ) → Fin 3 → IvQ) : Fin 3 → IvQ :=
  fun k =>
    let sel := fun (low : Bool) (j : Fin K) =>
      if dirs k j = 1 then (if low then (ends j).1 else (ends j).2)
      else if dirs k j = -1 then (if low then (ends j).2 else (ends j).1)
      else inp j
    ⟨(eval (sel true) k).lo, (eval (sel false) k).hi⟩

/-- `pentEvalC`. -/
def pentEvalC (d : IvQ) (x : Fin 2 → IvQ) : Fin 3 → IvQ :=
  let e := isoBase R (x 0) d
  let b1 := isoAngle R (x 0) d
  let f := isoBase R (x 1) d
  let b3 := isoAngle R (x 1) d
  vec3 (R.add (R.add b1 (triAngleC R d e f)) b3) (R.add b1 (triAngleC R f e d))
    (R.add b3 (triAngleC R e f d))

/-- `hexEvalC`. -/
def hexEvalC (d : IvQ) (x : Fin 3 → IvQ) : Fin 3 → IvQ :=
  let e1 := isoBase R (x 0) d
  let b1 := isoAngle R (x 0) d
  let e3 := isoBase R (x 1) d
  let b3 := isoAngle R (x 1) d
  let e5 := isoBase R (x 2) d
  let b5 := isoAngle R (x 2) d
  vec3 (R.add (R.add b5 (triAngleC R e3 e1 e5)) b1) (R.add (R.add b1 (triAngleC R e5 e1 e3)) b3)
    (R.add (R.add b3 (triAngleC R e1 e3 e5)) b5)

/-! ## The steps on a box, over the indices of their variables -/

section Steps

variable {ι : Type} [DecidableEq ι]

/-- `alphaStep` (`ja` the variable `a`, `jd` the variable `d`). -/
def alphaStep (B : BoxQ ι) (ja jd : ι) : Option (BoxQ ι) :=
  nar B ja (alphaIv R (ivOf B jd))

/-- `alphaInvStep`. -/
def alphaInvStep (B : BoxQ ι) (ja jd : ι) : Option (BoxQ ι) :=
  nar B jd (alphaInvIv R (ivOf B ja))

/-- `rhoStep` (`v j` the variable of the corner `j` steps along the face). -/
def rhoStep (B : BoxQ ι) (v : Nat → ι) (jd : ι) : Option (BoxQ ι) :=
  nar B (v 1) (rhoIv R (ivOf B (v 0)) (ivOf B jd))

/-- `rhoDStep`. -/
def rhoDStep (B : BoxQ ι) (v : Nat → ι) (jd : ι) : Option (BoxQ ι) :=
  (rhombusD R (ivOf B (v 0)) (ivOf B (v 1))).bind (nar B jd)

/-- `pentStep`. -/
def pentStep (B : BoxQ ι) (v : Nat → ι) (jd : ι) : Option (BoxQ ι) :=
  let d := ivOf B jd
  let up := ivOf B (v 1)
  let um := ivOf B (v 4)
  let ee := isoBase R up d
  let b1 := isoAngle R up d
  let ff := isoBase R um d
  let b3 := isoAngle R um d
  match triAngle R d ee ff, triAngle R ff ee d, triAngle R ee ff d with
  | some gi, some gp, some gm =>
    let nat := vec3 (R.add (R.add b1 gi) b3) (R.add b1 gp) (R.add b3 gm)
    let dirs : Fin 3 → Fin 2 → Int :=
      vec3 (vec2 (decDir R up (nat 1) gp d) (decDir R um (nat 2) gm d))
        (vec2 (decDir R up (R.add b1 gi) gi d) 1)
        (vec2 1 (decDir R um (R.add b3 gi) gi d))
    let mo := monoBounds (vec2 up um) (vec2 (cornerEnds R up) (cornerEnds R um)) dirs
      (pentEvalC R d)
    (nar B (v 0) ((nat 0).meet (mo 0))).bind fun B₁ =>
      (nar B₁ (v 2) ((nat 1).meet (mo 1))).bind fun B₂ =>
        nar B₂ (v 3) ((nat 2).meet (mo 2))
  | _, _, _ => none

/-- `hexStep`. -/
def hexStep (B : BoxQ ι) (v : Nat → ι) (jd : ι) : Option (BoxQ ι) :=
  let d := ivOf B jd
  let u1 := ivOf B (v 1)
  let u3 := ivOf B (v 3)
  let u5 := ivOf B (v 5)
  let e1 := isoBase R u1 d
  let b1 := isoAngle R u1 d
  let e3 := isoBase R u3 d
  let b3 := isoAngle R u3 d
  let e5 := isoBase R u5 d
  let b5 := isoAngle R u5 d
  match triAngle R e3 e1 e5, triAngle R e5 e1 e3, triAngle R e1 e3 e5 with
  | some g0, some g2, some g4 =>
    let nat := vec3 (R.add (R.add b5 g0) b1) (R.add (R.add b1 g2) b3) (R.add (R.add b3 g4) b5)
    let dirs : Fin 3 → Fin 3 → Int :=
      vec3 (vec3 (decDir R u1 (R.add b1 g2) g2 d) 1 (decDir R u5 (R.add b5 g4) g4 d))
        (vec3 (decDir R u1 (R.add b1 g0) g0 d) (decDir R u3 (R.add b3 g4) g4 d) 1)
        (vec3 1 (decDir R u3 (R.add b3 g2) g2 d) (decDir R u5 (R.add b5 g0) g0 d))
    let mo := monoBounds (vec3 u1 u3 u5) (vec3 (cornerEnds R u1) (cornerEnds R u3)
      (cornerEnds R u5)) dirs (hexEvalC R d)
    (nar B (v 0) ((nat 0).meet (mo 0))).bind fun B₁ =>
      (nar B₁ (v 2) ((nat 1).meet (mo 1))).bind fun B₂ =>
        nar B₂ (v 4) ((nat 2).meet (mo 2))
  | _, _, _ => none

/-- `diagFwdStep`. -/
def diagFwdStep (B : BoxQ ι) (v : Nat → ι) (jd : ι) : Option (BoxQ ι) :=
  nar B (v 1) ⟨longdiagLb R (ivOf B (v 0)) (ivOf B jd), FlQ.inf⟩

/-- `diagBwdStep`. -/
def diagBwdStep (B : BoxQ ι) (v : Nat → ι) (jd : ι) : Option (BoxQ ι) :=
  nar B (v 0) ⟨longdiagLb R (ivOf B (v 1)) (ivOf B jd), FlQ.inf⟩

/-- `wheelTurn` (`v j` the corner `j` steps along the hexagon, `r i` the variable `r m i`). -/
def wheelTurn (v : Nat → ι) (r : Fin 6 → ι) (d : IvQ) (B : BoxQ ι) (i : Fin 6) :
    Option (BoxQ ι) :=
  let u : ι := v i
  let ri := ivOf B (r i)
  (triAngle R (ivOf B (r (i + 1))) ri d).bind fun a1 =>
  (triAngle R (ivOf B (r (i - 1))) ri d).bind fun a2 =>
  (nar B u (R.add a1 a2)).bind fun B₂ =>
  (side R ri d (R.sub (ivOf B₂ u) a2)).bind fun rp =>
  (nar B₂ (r (i + 1)) rp).bind fun B₃ =>
  (side R ri d (R.sub (ivOf B₃ u) a1)).bind fun rm =>
  nar B₃ (r (i - 1)) rm

/-- `wheelStep`. -/
def wheelStep (v : Nat → ι) (r : Fin 6 → ι) (jd : ι) (B : BoxQ ι) : Option (BoxQ ι) :=
  let d := ivOf B jd
  ((List.finRange 6).foldlM (fun B' i => nar B' (r i) ⟨d.lo, (R.scale d 3).hi⟩) B).bind
    fun B₁ =>
  ((List.finRange 6).mapM fun i => triAngle R d (ivOf B₁ (r i)) (ivOf B₁ (r (i + 1)))).bind
    fun th =>
  let s := th.foldl R.add (IvQ.pt (.fin 0))
  if FlQ.lt s.hi (.fin R.twoPiLo) ∨ FlQ.lt (.fin R.twoPiHi) s.lo then none
  else (List.finRange 6).foldlM (wheelTurn R v r d) B₁

end Steps

/-! ## The linear rows -/

/-- `Row`. -/
structure RowQ (ι : Type) where
  terms : List (ι × Rat)
  lo : FlQ
  hi : FlQ

/-- `cmin`. -/
def cmin (c l u : Rat) : FlQ :=
  if 0 ≤ c then R.mulDn (.fin c) (.fin l) else R.mulDn (.fin c) (.fin u)

/-- `cmax`. -/
def cmax (c l u : Rat) : FlQ :=
  if 0 ≤ c then R.mulUp (.fin c) (.fin u) else R.mulUp (.fin c) (.fin l)

/-- `rowUpd`. -/
def rowUpd {ι : Type} [DecidableEq ι] (r : RowQ ι) (smin smax : FlQ) :
    List ((ι × Rat) × FlQ × FlQ) → BoxQ ι → Option (BoxQ ι)
  | [], B => some B
  | ((v, c), mn, mx) :: l, B =>
    if c = 0 then rowUpd r smin smax l B
    else
      let omin := R.subDn smin mn
      let omax := R.subUp smax mx
      let cup := if r.hi.IsFinite then R.subUp r.hi omin else FlQ.inf
      let cdn := if r.lo.IsFinite then R.subDn r.lo omax else FlQ.ninf
      let nlo := if 0 < c then (if cdn.IsFinite then R.divDn cdn (.fin c) else FlQ.ninf)
        else (if cup.IsFinite then R.divDn cup (.fin c) else FlQ.ninf)
      let nhi := if 0 < c then (if cup.IsFinite then R.divUp cup (.fin c) else FlQ.inf)
        else (if cdn.IsFinite then R.divUp cdn (.fin c) else FlQ.inf)
      let lo' := if FlQ.lt (.fin (B.lo v)) nlo then nlo.toQ else B.lo v
      let hi' := if FlQ.lt nhi (.fin (B.hi v)) then nhi.toQ else B.hi v
      if hi' < lo' then none
      else rowUpd r smin smax l ⟨updQ B.lo v lo', updQ B.hi v hi'⟩

/-- `rowStep`. -/
def rowStep {ι : Type} [DecidableEq ι] (r : RowQ ι) (B : BoxQ ι) : Option (BoxQ ι) :=
  let mn := r.terms.map fun t => cmin R t.2 (B.lo t.1) (B.hi t.1)
  let mx := r.terms.map fun t => cmax R t.2 (B.lo t.1) (B.hi t.1)
  let smin := mn.foldl R.addDn (.fin 0)
  let smax := mx.foldl R.addUp (.fin 0)
  if FlQ.lt r.hi smin ∨ FlQ.lt smax r.lo then none
  else rowUpd R r smin smax (r.terms.zip (mn.zip mx)) B

end Tammes15.Contractors.Q
