import Tammes15.PaperSteps.Defs
import Tammes15.PaperSteps.SearchTree

/-!
# The objects of the level-2 search

The definitions of Definition 5.4 of the paper, with the narrowings of the program as
parameters, that the statements of `progKilled_of_progTrees` (Search.lean) and
`conjecture_of_enum_progTrees` (MainSearch.lean) reach. The module holds definitions only, so that
the challenge of Comparator can copy it whole.

* `PVar P k`: the variables of the program for a case (system.rs `Sys::build`, deep.rs `Prob::new`):
  `a = α(d)`, which every corner of a triangle uses; a corner per dart (`cvar e` is the variable the
  program uses for the corner of `e`: `a` in a triangle, one of the two opposite darts in a rhombus,
  its own otherwise); `d`; the distances `r m j` of the free points. `PVar.val A` gives their values
  at an assignment.
* `Procs`: the interval procedures of the program, as functions of a box: the narrowing in each
  mode of the runs (`Mode`), and the enclosure of the angle `γ(r_{i-1}; r_i, d)` of a wheel
  triangle (deep.rs `tri_angle`). `Procs.Sound` is their soundness on the solutions of the
  relation system with `d ∈ [dlo, dhi]` (`Sol`); it is a hypothesis of `progKilled_of_progTrees`.
* The leaf test `LeafKill` (local.rs `Geo::place`, `Geo::pair_at`, `Geo::local_at`): centres and
  radii of the angles of the gluing over the narrowed box (`Encl.Covers`), the configuration glued
  from the centres (`glueC`) with the radii summed along the tree paths (`radC`), and Pair (`PairC`)
  or Local against the targets (`TieC`) on that enclosure.
* `ProgTrees L N`: for every entry, every set of hexagons (the program's choice `H₀`) and every
  `d ∈ [dlo, dhi]`, a run on a range of `d` containing it, with a root box that holds the
  solutions (`RootOK`) and a tree that the replay accepts (`Search.Tree.OK`).
-/

open Real Matrix
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15 Search

open scoped Classical

variable {P : PlaneGraph} {k : ℕ}

/-! ## The variables of the program -/

/-- The variables of the search for a case with `k` free points: `a = α(d)`, a corner per dart, `d`,
and the distance `r m j` from the `m`-th free point to the corner `A_j` of its hexagon. -/
inductive PVar (P : PlaneGraph) (k : ℕ) : Type
  | a : PVar P k
  | c : P.G.Dart → PVar P k
  | d : PVar P k
  | r : Fin k → Fin 6 → PVar P k

/-- The value of a variable at an assignment. -/
noncomputable def PVar.val (A : Assign P k) : PVar P k → ℝ
  | .a => alpha A.d
  | .c e => A.corner e
  | .d => A.d
  | .r m j => A.r m j

/-- A key ordering the darts by their ends. -/
def dartKey (e : P.G.Dart) : ℕ := e.fst.val * P.n + e.snd.val

/-- The variable of the program for the corner of the dart `e`: `a` in a triangle; in a rhombus,
the variable of the one of the two opposite darts `e`, `face² e` with the smaller key (the program
has one variable for both); the dart's own variable otherwise. -/
noncomputable def cvar (e : P.G.Dart) : PVar P k :=
  if fsize P e = 3 then .a
  else if fsize P e = 4 then
    (if dartKey e ≤ dartKey ((P.R.face ^ 2) e) then .c e else .c ((P.R.face ^ 2) e))
  else .c e

/-! ## The procedures of the program and their soundness -/

/-- The modes of propagation of the runs: the first level (tfilter.rs: the rows), and the second
level (deep.rs `Prob::check` before the gluing tests: the relations, then 3B shaving with slices of
`1/s` of the widths when `s > 0`). -/
inductive Mode
  | level1
  | level2 (shave : ℕ)

/-- The interval procedures of the program, as functions of a box of a case: the narrowing in each
mode (`none` when it proves the box empty), and the enclosure of `γ(r_{i-1}; r_i, d)` for the `m`-th
free point placed from the corner `i` (deep.rs `tri_angle`, `none` when it finds no triangle). -/
structure Procs where
  narrow : (P : PlaneGraph) → (k : ℕ) → HexChoice P k → Mode → Box (PVar P k) →
    Option (Box (PVar P k))
  wheel : (P : PlaneGraph) → (k : ℕ) → Box (PVar P k) → Fin k → Fin 6 → Option (ℝ × ℝ)

/-- The solutions of a case: the assignments that satisfy the relation system with `d ∈ [dlo, dhi]`. -/
def Sol (P : PlaneGraph) {k : ℕ} (H : HexChoice P k) : Set (Assign P k) :=
  {A | dlo ≤ A.d ∧ A.d ≤ dhi ∧ RelSys P H A}

/-- The procedures keep the solutions: every narrowing is sound, and the enclosure of the wheel
angle over a box holds the angle of every solution in the box. -/
def Procs.Sound (N : Procs) : Prop :=
  ∀ (P : PlaneGraph) (k : ℕ) (H : HexChoice P k),
    (∀ m, NarrowSound (Sol P H) PVar.val (N.narrow P k H m)) ∧
    ∀ A ∈ Sol P H, ∀ B : Box (PVar P k), B.Mem (PVar.val A) →
      ∀ (m : Fin k) (i : Fin 6) (β : ℝ × ℝ), N.wheel P k B m i = some β →
        β.1 ≤ gam (A.r m (i - 1)) (A.r m i) A.d ∧ gam (A.r m (i - 1)) (A.r m i) A.d ≤ β.2

/-! ## The root box -/

/-- The root box of a run on `[lo, hi]` contains the box of deep.rs `Prob::new`: `a` from `α(dlo)`
to `α(dhi)`; every corner from `α(dlo)`, up to `α(dhi)` in a triangle, `2 α(dhi)` in a rhombus and
`π` otherwise; `d ∈ [lo, hi]`; `r ∈ [lo, 3 hi]`. -/
def RootOK (lo hi : ℝ) (B : Box (PVar P k)) : Prop :=
  (B.lo .a ≤ alpha dlo ∧ alpha dhi ≤ B.hi .a) ∧
  (∀ e, B.lo (.c e) ≤ alpha dlo ∧
    (fsize P e = 3 → alpha dhi ≤ B.hi (.c e)) ∧ (fsize P e = 4 → 2 * alpha dhi ≤ B.hi (.c e)) ∧
    (fsize P e ≠ 3 → fsize P e ≠ 4 → π ≤ B.hi (.c e))) ∧
  (B.lo .d ≤ lo ∧ hi ≤ B.hi .d) ∧
  ∀ m j, B.lo (.r m j) ≤ lo ∧ 3 * hi ≤ B.hi (.r m j)

/-! ## Enclosure of the turns -/

/-- The number of darts at the vertex of `a`. -/
noncomputable def rotDeg (a : P.G.Dart) : ℕ := Function.minimalPeriod P.R.rot.symm a

/-- Lower end of the enclosure of the program's turn from `a` to `b` over a box (local.rs
`Geo::angle`): the sum of the corners passed, intersected with `2π` minus the sum of the other
corners at the vertex. -/
noncomputable def turnLo (B : Box (PVar P k)) (a b : P.G.Dart) : ℝ :=
  max (∑ t ∈ Finset.range (turnStepsR P.R a b), B.lo (cvar ((P.R.rot.symm ^ (t + 1)) a)))
    (2 * π - ∑ t ∈ Finset.Ico (turnStepsR P.R a b) (rotDeg a),
      B.hi (cvar ((P.R.rot.symm ^ (t + 1)) a)))

/-- Upper end of the enclosure of the program's turn from `a` to `b`. -/
noncomputable def turnHi (B : Box (PVar P k)) (a b : P.G.Dart) : ℝ :=
  min (∑ t ∈ Finset.range (turnStepsR P.R a b), B.hi (cvar ((P.R.rot.symm ^ (t + 1)) a)))
    (2 * π - ∑ t ∈ Finset.Ico (turnStepsR P.R a b) (rotDeg a),
      B.lo (cvar ((P.R.rot.symm ^ (t + 1)) a)))

/-! ## The gluing from centres and radii -/

/-- Centres and radii of the angles of the gluing over a box (local.rs `Geo::place`, `center`):
`d`; the turn into each vertex from its parent; for each free point, the angle that places it and
its distance to the corner it is placed from. -/
structure Encl (P : PlaneGraph) (k : ℕ) where
  dc : ℝ
  dr : ℝ
  pc : Fin P.n → ℝ
  pr : Fin P.n → ℝ
  qc : Fin k → ℝ
  qr : Fin k → ℝ
  rc : Fin k → ℝ
  rr : Fin k → ℝ

/-- The dart `A_i → A_{i+1}` of the hexagon of the `m`-th free point, `i = freeCorner m`; its first
end is the corner `A_i` the point is placed from. -/
noncomputable def freeDart (H : HexChoice P k) (g : GlueData P k) (m : Fin k) : P.G.Dart :=
  (P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)

/-- The dart `A_i → A_{i-1}` towards which the program turns at `A_i`. -/
noncomputable def freeBack (H : HexChoice P k) (g : GlueData P k) (m : Fin k) : P.G.Dart :=
  ((P.R.face ^ ((g.freeCorner m - 1 : Fin 6) : ℕ)) (H.base m)).symm

/-- The frames of the program's gluing with the turn `φ v` into each vertex and the step `δ`. -/
noncomputable def frameAng (g : GlueData P k) (φ : Fin P.n → ℝ) (δ : ℝ) :
    ℕ → Fin P.n → Matrix (Fin 3) (Fin 3) ℝ
  | 0, _ => 1
  | n + 1, v => if v = g.root then 1 else frameAng g φ δ n (g.par v).fst * stepM (φ v) δ

/-- The radius of a frame: the sum of the radii of the turns and of the steps along the path. -/
noncomputable def radN (g : GlueData P k) (pr : Fin P.n → ℝ) (dr : ℝ) : ℕ → Fin P.n → ℝ
  | 0, _ => 0
  | n + 1, v => if v = g.root then 0 else radN g pr dr n (g.par v).fst + pr v + dr

/-- The configuration glued from the centres (`Y_c`). -/
noncomputable def glueC (H : HexChoice P k) (g : GlueData P k) (E : Encl P k) : Pts P k → E3
  | .inl v => toEuclideanLin (frameAng g E.pc E.dc (g.depth v) v) e3
  | .inr m =>
    toEuclideanLin (frameAng g E.pc E.dc (g.depth (freeDart H g m).fst) (freeDart H g m).fst *
      rotZ (E.qc m) * rotY (E.rc m)) e3

/-- The radius of each point (`ϱ`): the radius of its frame, plus for a free point the radii of
the angle and of the distance that place it. -/
noncomputable def radC (H : HexChoice P k) (g : GlueData P k) (E : Encl P k) : Pts P k → ℝ
  | .inl v => radN g E.pr E.dr (g.depth v) v
  | .inr m => radN g E.pr E.dr (g.depth (freeDart H g m).fst) (freeDart H g m).fst + E.qr m + E.rr m

/-- The centres and radii cover the box: each angle of the gluing, enclosed over the box as the
program encloses it, lies within its radius of its centre. -/
def Encl.Covers (W : Box (PVar P k) → Fin k → Fin 6 → Option (ℝ × ℝ)) (H : HexChoice P k)
    (g : GlueData P k) (B : Box (PVar P k)) (E : Encl P k) : Prop :=
  (E.dc - E.dr ≤ B.lo .d ∧ B.hi .d ≤ E.dc + E.dr) ∧
  (∀ v, v ≠ g.root → E.pc v - E.pr v ≤ turnLo B (g.refD (g.par v).fst) (g.par v) ∧
      turnHi B (g.refD (g.par v).fst) (g.par v) ≤ E.pc v + E.pr v) ∧
  (∀ m, ∃ β : ℝ × ℝ, W B m (g.freeCorner m) = some β ∧
      E.qc m - E.qr m ≤ turnLo B (g.refD (freeDart H g m).fst) (freeBack H g m) + β.1 ∧
      turnHi B (g.refD (freeDart H g m).fst) (freeBack H g m) + β.2 ≤ E.qc m + E.qr m) ∧
  ∀ m, E.rc m - E.rr m ≤ B.lo (.r m (g.freeCorner m)) ∧
    B.hi (.r m (g.freeCorner m)) ≤ E.rc m + E.rr m

/-- Pair on the enclosure (local.rs `Geo::pair_at`): two points not joined by an edge whose centres
and radii put them closer than `2 sin (d₋ / 2)`, `d₋ ≥ 0` the lower end of `d`. The program does
not test `d₋ ≥ 0`: it holds on every box of a replay, which lies in the root box (`nar` intersects,
splits and shaving cut inside the interval), whose lower end of `d` is at least `0.9365`. -/
def PairC (H : HexChoice P k) (g : GlueData P k) (E : Encl P k) (B : Box (PVar P k)) : Prop :=
  0 ≤ B.lo .d ∧ ∃ a b : Pts P k, a ≠ b ∧ ¬ PAdj P a b ∧
    ‖glueC H g E a - glueC H g E b‖ + radC H g E a + radC H g E b < 2 * sin (B.lo .d / 2)

/-- Local on the enclosure (local.rs `Geo::local_at`): a normalised target and a bijection of the
points with its points such that, for every choice of the target points in their boxes, each
centre plus its radius is within `rLocal` of its normalised target point. -/
def TieC (H : HexChoice P k) (g : GlueData P k) (E : Encl P k) : Prop :=
  ∃ c : Fin 8, ∃ e ∈ tieContacts c, ∃ ab : Fin 15 × Fin 15, (ab = e ∨ ab = e.swap) ∧
    ∃ mirror : Bool, ∃ j : Pts P k ≃ Fin 15, ∀ z : Fin 15 → E3, InTieBoxes c z →
      ∀ v, ‖glueC H g E v - tieNormalize (z ab.1) (z ab.2) mirror (z (j v))‖ + radC H g E v ≤
        rLocal

/-- The leaf test of the program on a narrowed box: a valid gluing, centres and radii that cover
the box, and Pair or Local on the enclosure. These are exact real statements; the program checks
them in outward-rounded binary64 arithmetic with the `rig` backend (the centres, `up_add`,
`Iv::sqrt`, `Iv::sin` and `Iv::cos` in `step`, the normalisation of `Targets::load`). `Procs.Sound`
covers the narrowings and `tri_angle` only, so reading a leaf the program kills as `LeafKill` also
trusts that arithmetic. -/
def LeafKill (N : Procs) (P : PlaneGraph) {k : ℕ} (H : HexChoice P k) (B : Box (PVar P k)) :
    Prop :=
  ∃ g : GlueData P k, g.Valid ∧ ∃ E : Encl P k, E.Covers (N.wheel P k) H g B ∧
    (PairC H g E B ∨ TieC H g E)

/-! ## The replayed trees -/

/-- What the replays and their join with the survivors check, for the procedures `N`: for every
entry, every set of hexagons (the program's choice `H₀`) and every `d ∈ [dlo, dhi]`, a run on a
range of `d` that contains it, with a root box that holds the solutions of that range, and a tree
that its replay accepts (for an entry rejected by the first level, the tree is a leaf of the first
level). `RootOK` and `LeafKill` are exact real statements that the program checks in
outward-rounded binary64 arithmetic (`rig` backend), which a VERIFIED line asks to trust besides
`Procs.Sound`. `P` is read from its plantri record with `P.R.rot` the previous neighbour in the
clockwise order of the planar code (the paper, Section 7.3); under the other reading
`ProgTrees` would state the mirror image of what the program checks. -/
def ProgTrees (L : Set PlaneGraph) (N : Procs) : Prop :=
  ∀ P ∈ L, ∀ k : ℕ, P.n + k = 15 → ∀ H : HexChoice P k, ∃ H₀ : HexChoice P k, SameHexSet H H₀ ∧
    ∀ d, dlo ≤ d → d ≤ dhi → ∃ lo hi : ℝ, lo ≤ d ∧ d ≤ hi ∧
      ∃ (m : Mode) (B₀ : Box (PVar P k)) (t : Search.Tree (PVar P k)),
        RootOK lo hi B₀ ∧ t.OK (N.narrow P k H₀ m) (LeafKill N P H₀) B₀

end Tammes15.PaperSteps
