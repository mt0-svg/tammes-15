import Tammes15.Hyps.Computations
import Tammes15.PaperSteps.TieData

/-!
# The verdicts of the program, in its own conventions

`Killed L F` (D3) speaks of every choice of hexagons, of the gluing of Definition 7.2 and of `F`. The
program checks something narrower, which this file states as `ProgKilled L`:

* one choice of hexagons per set of hexagons, with base darts of its own (`SameHexSet`);
* its gluing (code/impl1/rust/src/local.rs, `Geo::new` and `Geo::place`), which turns at a vertex in
  the order opposite to `P.R.rot` (`Assign.turnR`) and places a free point from a corner `A_i` through
  `A_{i-1}` (`progGlueY`). The plane graph `P` is read from its plantri record as in the paper
  (Appendix B.2): `P.R.rot` takes a dart at a vertex to the next one counterclockwise, the
  previous neighbour in the clockwise order of the planar code. Under the other reading (`rot` the
  next neighbour of the code) the program would turn by `rot`, and `ProgKilled` would state the
  mirror image of what it checks;
* Pair (`Geo::pair_at`) as `PairFires` on that configuration;
* Local (`Targets::load`, `Geo::local_at`) against the targets of `TieData`, normalised by the program
  from two points of a listed contact (`tieNormalize`), as `TieFires`.

`ProgKilled` is the pointwise form of the verdicts: for every assignment that satisfies the relation
system with its `d` in `[dlo, dhi]`, some gluing of the program fires Pair or Local. That the boxes
and the interval arithmetic of the program give this form is the soundness of the search
(Proposition 6.4 of the paper).
`killed_of_progKilled` (PaperSteps/Main.lean) proves `Killed L {frameC1, frameC3}` from it.
-/

open Real Matrix
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15

open scoped Classical

variable {P : PlaneGraph} {k : ℕ}

/-! ## Choices of hexagons -/

/-- Two choices of hexagons for the same set of faces: a bijection of the free points that sends
each hexagon of `H` to the hexagon (the same face) of `H₀`. -/
def SameHexSet (H H₀ : HexChoice P k) : Prop :=
  ∃ σ : Fin k ≃ Fin k, ∀ m, P.R.face.SameCycle (H.base m) (H₀.base (σ m))

/-! ## The gluing of the program -/

/-- The number of steps of `rot⁻¹` from the dart `a` to the dart `b` at the same vertex. -/
noncomputable def turnStepsR {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (a b : G.Dart) : ℕ :=
  if h : ∃ s, (R.rot.symm ^ s) a = b then Nat.find h else 0

/-- The angle the program turns from the dart `a` to the dart `b` at their vertex: the sum of the
corners passed going by `rot⁻¹` (the program's rotation order; the corner between `e` and `rot⁻¹ e`
is the corner of the dart `rot⁻¹ e`). -/
noncomputable def turnR (A : Assign P k) (a b : P.G.Dart) : ℝ :=
  ∑ t ∈ Finset.range (turnStepsR P.R a b), A.corner ((P.R.rot.symm ^ (t + 1)) a)

/-- The frames of the program's gluing (`Geo::place`): `F'(v₀) = I` and `F'(w) = F'(v) R_z(φ') R_y(d) Z`
with `φ'` the program's turn at the parent `v` from its reference dart to the dart towards `w`. -/
noncomputable def progFrameN (g : GlueData P k) (A : Assign P k) :
    ℕ → Fin P.n → Matrix (Fin 3) (Fin 3) ℝ
  | 0, _ => 1
  | n + 1, v =>
    if v = g.root then 1
    else progFrameN g A n (g.par v).fst * stepM (turnR A (g.refD (g.par v).fst) (g.par v)) A.d

/-- The frame `F'(v)` of a vertex in the program's gluing. -/
noncomputable def progFrame (g : GlueData P k) (A : Assign P k) (v : Fin P.n) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  progFrameN g A (g.depth v) v

/-- The configuration glued by the program: `Y'(v) = F'(v) e₃`; the `m`-th free point is placed from
the corner `A_i`, `i = freeCorner m`, turning from the reference dart of `A_i` to the dart
`A_i → A_{i-1}` and then by the angle `γ(r_{i-1}; r_i, d)` of the wheel triangle `A_{i-1} A_i P` at
`A_i`, at distance `r_i` (`Geo::place`, the loop over `fp.from`). -/
noncomputable def progGlueY (H : HexChoice P k) (A : Assign P k) (g : GlueData P k) :
    Pts P k → E3
  | .inl v => toEuclideanLin (progFrame g A v) e3
  | .inr m =>
    toEuclideanLin
      (progFrame g A ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst *
        rotZ (turnR A (g.refD ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst)
            ((P.R.face ^ ((g.freeCorner m - 1 : Fin 6) : ℕ)) (H.base m)).symm +
          gam (A.r m (g.freeCorner m - 1)) (A.r m (g.freeCorner m)) A.d) *
        rotY (A.r m (g.freeCorner m))) e3

/-! ## Local as the program checks it -/

/-- The program's normalisation of a target (`Targets::load`): with `e₃ = z_a`,
`e₁ = (z_b - ⟪z_a, z_b⟫ z_a) / ‖z_b - ⟪z_a, z_b⟫ z_a‖` and `e₂ = e₃ × e₁`, a point `z` goes to
`(⟪z, e₁⟫, ±⟪z, e₂⟫, ⟪z, e₃⟫)`, the sign `-` for the mirror image. -/
noncomputable def tieNormalize (za zb : E3) (mirror : Bool) (z : E3) : E3 :=
  !₂[⟪z, ‖zb - ⟪za, zb⟫ • za‖⁻¹ • (zb - ⟪za, zb⟫ • za)⟫,
    (if mirror then -1 else 1) * ⟪z, cross za (‖zb - ⟪za, zb⟫ • za‖⁻¹ • (zb - ⟪za, zb⟫ • za))⟫,
    ⟪z, za⟫]

/-- `z` lies in the target boxes of configuration `c`: every coordinate within its radius of its
midpoint. -/
def InTieBoxes (c : Fin 8) (z : Fin 15 → E3) : Prop :=
  ∀ i l, |(z i).ofLp l - tieMid c i l| ≤ tieRad c i l

/-- Local of the program (`Geo::local_at`), pointwise: for some configuration `c` of the targets,
some directed contact `(a, b)` of it, normalised directly or mirrored, and some bijection `j` of the
points with the target points, every choice `z` of the target points in their boxes, normalised by
`tieNormalize (z a) (z b)`, lies within `rLocal` of the configuration, point by point. -/
def TieFires {α : Type} (Y : α → E3) : Prop :=
  ∃ c : Fin 8, ∃ e ∈ tieContacts c, ∃ ab : Fin 15 × Fin 15, (ab = e ∨ ab = e.swap) ∧
    ∃ mirror : Bool, ∃ j : α ≃ Fin 15, ∀ z : Fin 15 → E3, InTieBoxes c z →
      ∀ v, ‖Y v - tieNormalize (z ab.1) (z ab.2) mirror (z (j v))‖ ≤ rLocal

/-! ## The verdicts -/

/-- The verdicts of the program on the list `L`, pointwise: for every entry with `n` vertices
and every set of `k = 15 - n` hexagons (given by a choice `H`), the program's own choice `H₀` of the
same set is refuted: every assignment satisfying the relation system of `H₀` with `d ∈ [dlo, dhi]`
has a valid gluing of the program that fires Pair, or fires Local against the targets. `P` is read
from its plantri record with `P.R.rot` the previous neighbour in the clockwise order of the planar
code (the paper, Appendix B.2), the reading under which these are the program's gluings. -/
def ProgKilled (L : Set PlaneGraph) : Prop :=
  ∀ P ∈ L, ∀ k : ℕ, P.n + k = 15 → ∀ H : HexChoice P k, ∃ H₀ : HexChoice P k, SameHexSet H H₀ ∧
    ∀ A : Assign P k, dlo ≤ A.d → A.d ≤ dhi → RelSys P H₀ A →
      ∃ g : GlueData P k, g.Valid ∧
        (PairFires P A (progGlueY H₀ A g) ∨ TieFires (progGlueY H₀ A g))

end Tammes15.PaperSteps
