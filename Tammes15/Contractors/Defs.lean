import Tammes15.Contractors.Prims

/-!
# Soundness of the contractors: the definitions (Definition B.1 of the paper)

The objects that the statements of Statement.lean reach, moved there verbatim (same names, same
bodies), in a module of definitions only, so that the challenge of Comparator can copy it whole.

* `RowKind`, `SysRow`: the rows of system.rs `Sys::build` under `--no-face --no-cuts`, each by its
  linear form (any order of terms) and bounds that contain the range of the form at the solutions.
* `Prim`, `Prim.Allowed`, `primStep`: one application of one contractor of deep.rs `Prob::pass`
  (`Contractors.Prims`), or one row of system.rs `fbbt`.
* `DomOK`: every variable of the box within its range in the program's root box.
* `Run H B o`: `o` is reached from `B` by a finite sequence of primitive steps on boxes of the
  domain, each computed with some arithmetic `R` with `R.Sound`, and of 3B cuts.
* `WheelOut`, `Impl N`: how the procedures `N` compute on boxes of the domain.
* `ProgTreesDom`: `ProgTrees` with root boxes in the domain; `onDom N`: the procedures of `N` on
  the domain.
-/

namespace Tammes15.Contractors

open Real
open scoped Classical
open Tammes15 Tammes15.PaperSteps Tammes15.PaperSteps.Search

variable {P : PlaneGraph} {k : ℕ}

/-! ## The rows of system.rs -/

/-- The rows of system.rs `Sys::build` with `--no-face --no-cuts`: the vertex sums, the four rows
of a rhombus (`x + y ≥ 3a`, `x + y ≤ shi`, `z ≥ a`, `z ≤ 2a` for each of its two variables `z`),
and `u ≥ a` for a pentagon or hexagon corner. -/
inductive RowKind (P : PlaneGraph) (k : ℕ) : Type
  | vertex (v : Fin P.n)
  | rhSum (e : P.G.Dart)
  | rhSumHi (e : P.G.Dart)
  | rhLo (e : P.G.Dart)
  | rhHi (e : P.G.Dart)
  | corner (e : P.G.Dart)

/-- The face condition of a row kind. -/
def RowKind.Allowed : RowKind P k → Prop
  | .vertex _ => True
  | .rhSum e => fsize P e = 4
  | .rhSumHi e => fsize P e = 4
  | .rhLo e => fsize P e = 4
  | .rhHi e => fsize P e = 4
  | .corner e => fsize P e = 5 ∨ fsize P e = 6

/-- The linear form of a row kind. -/
noncomputable def RowKind.form : RowKind P k → (PVar P k → ℝ) → ℝ
  | .vertex v, x => ∑ e ∈ Finset.univ.filter (fun e : P.G.Dart => e.fst = v), x (cvar e)
  | .rhSum e, x => x (fv e 0) + x (fv e 1) - 3 * x .a
  | .rhSumHi e, x => x (fv e 0) + x (fv e 1)
  | .rhLo e, x => x (fv e 0) - x .a
  | .rhHi e, x => x (fv e 0) - 2 * x .a
  | .corner e, x => x (fv e 0) - x .a

/-- The lower end of the range of the form at the solutions. -/
noncomputable def RowKind.lo : RowKind P k → EReal
  | .vertex _ => ((2 * π : ℝ) : EReal)
  | .rhSum _ => 0
  | .rhSumHi _ => ⊥
  | .rhLo _ => 0
  | .rhHi _ => ⊥
  | .corner _ => 0

/-- The upper end of the range of the form at the solutions (`3.73170040409990243346`, the `shi`
of data/params15ft.txt, bounds `S(d)` on `[dlo, dhi]`). -/
noncomputable def RowKind.hi : RowKind P k → EReal
  | .vertex _ => ((2 * π : ℝ) : EReal)
  | .rhSum _ => ⊤
  | .rhSumHi _ => ((3.73170040409990243346 : ℝ) : EReal)
  | .rhLo _ => ⊤
  | .rhHi _ => 0
  | .corner _ => ⊤

/-- A row of the program: the linear form of a kind (in any order of the terms, repeated variables
merged or not) with bounds that contain the kind's range. -/
def SysRow (r : Row (PVar P k)) : Prop :=
  ∃ κ : RowKind P k, κ.Allowed ∧ (∀ x, r.form x = κ.form x) ∧ Fl.le r.lo (.num κ.lo) ∧
    Fl.le (.num κ.hi) r.hi

/-! ## Primitive steps -/

/-- One application of one contractor of deep.rs `Prob::pass`, or one row of system.rs `fbbt`. -/
inductive Prim (P : PlaneGraph) (k : ℕ) : Type
  | row (r : Row (PVar P k))
  | alpha
  | alphaInv
  | rho (e : P.G.Dart)
  | rhoD (e : P.G.Dart)
  | pent (e : P.G.Dart)
  | hex (e : P.G.Dart)
  | diagFwd (e : P.G.Dart)
  | diagBwd (e : P.G.Dart)
  | wheel (m : Fin k)

/-- The steps the program applies: rows of `Sys::build`, and each contractor on a face of its size. -/
def Prim.Allowed : Prim P k → Prop
  | .row r => SysRow r
  | .alpha => True
  | .alphaInv => True
  | .rho e => fsize P e = 4
  | .rhoD e => fsize P e = 4
  | .pent e => fsize P e = 5
  | .hex e => fsize P e = 6
  | .diagFwd e => fsize P e = 6
  | .diagBwd e => fsize P e = 6
  | .wheel _ => True

/-- A primitive step computed with the arithmetic `R`. -/
noncomputable def primStep (R : Rnd) (H : HexChoice P k) :
    Prim P k → Box (PVar P k) → Option (Box (PVar P k))
  | .row r, B => rowStep R r B
  | .alpha, B => alphaStep R B
  | .alphaInv, B => alphaInvStep R B
  | .rho e, B => rhoStep R B e
  | .rhoD e, B => rhoDStep R B e
  | .pent e, B => pentStep R B e
  | .hex e, B => hexStep R B e
  | .diagFwd e, B => diagFwdStep R B e
  | .diagBwd e, B => diagBwdStep R B e
  | .wheel m, B => wheelStep R H m B

/-! ## The domain and the runs -/

/-- Every variable of the box within its range in the program's root box. -/
def DomOK (B : Box (PVar P k)) : Prop :=
  (1.1 ≤ B.lo .a ∧ B.hi .a ≤ 1.3) ∧ (0.9 ≤ B.lo .d ∧ B.hi .d ≤ 1) ∧
    (∀ e, 1.1 ≤ B.lo (.c e) ∧ B.hi (.c e) ≤ 3.2 ∧ (fsize P e = 4 → B.hi (.c e) ≤ 2.5)) ∧
    ∀ m j, 0.9 ≤ B.lo (.r m j) ∧ B.hi (.r m j) ≤ 3

/-- `o` is reached from `B` by primitive steps on boxes of the domain (each with an arithmetic `R`
with `R.Sound`), and 3B cuts: at a cut point `t` of a variable `v`, the slice below (above) `t` is
removed when a run empties it. -/
inductive Run (H : HexChoice P k) : Box (PVar P k) → Option (Box (PVar P k)) → Prop
  | stop (B : Box (PVar P k)) : Run H B (some B)
  | step (R : Rnd) (hR : R.Sound) (s : Prim P k) (hs : s.Allowed) {B B' : Box (PVar P k)}
      {o : Option (Box (PVar P k))} (hB : DomOK B) (h : primStep R H s B = some B')
      (hrest : Run H B' o) : Run H B o
  | kill (R : Rnd) (hR : R.Sound) (s : Prim P k) (hs : s.Allowed) {B : Box (PVar P k)}
      (hB : DomOK B) (h : primStep R H s B = none) : Run H B none
  | cutLo (v : PVar P k) (t : ℝ) {B : Box (PVar P k)} {o : Option (Box (PVar P k))}
      (ht : B.lo v ≤ t ∧ t ≤ B.hi v) (h₁ : Run H (B.lower v t) none)
      (h₂ : Run H (B.upper v t) o) : Run H B o
  | cutHi (v : PVar P k) (t : ℝ) {B : Box (PVar P k)} {o : Option (Box (PVar P k))}
      (ht : B.lo v ≤ t ∧ t ≤ B.hi v) (h₁ : Run H (B.upper v t) none)
      (h₂ : Run H (B.lower v t) o) : Run H B o

/-- The wheel enclosure is deep.rs `tri_angle(b[r_{i-1}], b[r_i], b[d])` computed with some
arithmetic `R` with `R.Sound`, read in real ends `β` at least as wide. -/
def WheelOut (B : Box (PVar P k)) (m : Fin k) (i : Fin 6) (β : ℝ × ℝ) : Prop :=
  ∃ R : Rnd, R.Sound ∧ ∃ I : Iv,
    triAngle R (ivOf B (.r m (i - 1))) (ivOf B (.r m i)) (ivOf B .d) = some I ∧
      Fl.le (.ofReal β.1) I.lo ∧ Fl.le I.hi (.ofReal β.2)

/-- How the procedures of the program compute, on boxes of the domain: the narrowing in every mode
is the outcome of a run, and the wheel enclosure is `tri_angle`. -/
def Impl (N : Procs) : Prop :=
  (∀ (P : PlaneGraph) (k : ℕ) (H : HexChoice P k) (m : Mode) (B : Box (PVar P k)), DomOK B →
    Run H B (N.narrow P k H m B)) ∧
  ∀ (P : PlaneGraph) (k : ℕ) (B : Box (PVar P k)) (m : Fin k) (i : Fin 6) (β : ℝ × ℝ), DomOK B →
    N.wheel P k B m i = some β → WheelOut B m i β

/-- `ProgTrees` with root boxes in the domain. -/
def ProgTreesDom (L : Set PlaneGraph) (N : Procs) : Prop :=
  ∀ P ∈ L, ∀ k : ℕ, P.n + k = 15 → ∀ H : HexChoice P k, ∃ H₀ : HexChoice P k, SameHexSet H H₀ ∧
    ∀ d, dlo ≤ d → d ≤ dhi → ∃ lo hi : ℝ, lo ≤ d ∧ d ≤ hi ∧
      ∃ (m : Mode) (B₀ : Box (PVar P k)) (t : Search.Tree (PVar P k)),
        RootOK lo hi B₀ ∧ DomOK B₀ ∧ t.OK (N.narrow P k H₀ m) (LeafKill N P H₀) B₀

/-- The procedures of `N` on the domain, the identity (no enclosure) off it. -/
noncomputable def onDom (N : Procs) : Procs where
  narrow P k H m B := if DomOK B then N.narrow P k H m B else some B
  wheel P k B m i := if DomOK B then N.wheel P k B m i else none

end Tammes15.Contractors
