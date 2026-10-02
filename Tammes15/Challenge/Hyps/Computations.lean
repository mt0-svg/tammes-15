import Tammes15.Challenge.Hyps.Case
import Tammes15.Challenge.Local41.Defs
import Tammes15.Challenge.D2Regions.Defs

/-!
# The four statements D1 to D4, stated exactly

The theorem `Tammes15.reduction` (module `Tammes15.Hyps.Reduction`) proves `Tammes15.Conjecture`
from four hypotheses on a list `L` of plane graphs and a set `F` of labelled frame configurations.
D1 and D4 are proved for the frames C1 and C3 (`Tammes15.Kappa.kappaHyp`,
`Tammes15.Attained.attained`), so `Tammes15.conjecture_of_enum_killed` needs D2 and D3 only; Section 7.3
of the paper derives D2 and D3 from the outputs of the programs.

* `KappaHyp F` (D1): the first-order rigidity constant of every frame is at least `kappa0`.
* `EnumComplete L` (D2, Definition 7.1 of the paper): every rotation system with 12 to 15 vertices of a 3-connected graph with
  degrees 3 to 5 that is in the input class of `plantri -p -f6` read on a drawing
  (`D2Regions.PlaneClass`: an arc drawing on the sphere without crossings, with these clockwise
  orders, every region bounded by at most 6 edges) is isomorphic to an entry of `L`, possibly with
  the orientation reversed.
* `Killed L F` (D3): for every entry with `n` vertices, every choice of `15 - n` hexagons and every
  assignment with `d ∈ [dlo, dhi]` that satisfies the relation system, some gluing of it fires
  Pair, or fires Local with a frame of `F`.
* `AttainedHyp F` (D4): `F` is not empty, and every frame is a configuration of 15 unit vectors
  whose listed pairs have inner product exactly `u` (the root of the quintic) and whose other pairs
  have inner product at most `u`.
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15

/-- The first-order rigidity constant claimed for the frames, `κ₀ = 6.4980·10⁻³` (the C1 type;
the C3 type has `6.8142·10⁻³`). -/
noncomputable def kappa0 : ℝ := 6.4980e-3

/-- D1 (KappaBound): every frame of `F` has first-order rigidity constant at least `kappa0` with
respect to its contacts. -/
def KappaHyp (F : Set Frame) : Prop :=
  ∀ q ∈ F, KappaBound q.p q.S kappa0

/-- A contact drawing of `G` at distance `d`: unit vectors at pairwise spherical distance at least
`d`, the edges exactly the pairs at distance `d`. -/
def IsContactDrawing {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) (x : Fin n → E3) : Prop :=
  0 < d ∧ d < π / 2 ∧ (∀ a, ‖x a‖ = 1) ∧ (∀ a b, a ≠ b → d ≤ sdist (x a) (x b)) ∧
    ∀ a b, G.Adj a b ↔ a ≠ b ∧ sdist (x a) (x b) = d

/-- `R` is the rotation system of a contact drawing of `G`: at each vertex, the counterclockwise
order of the edges seen from outside (`IsAngular`). -/
def ContactDrawn {n : ℕ} (G : SimpleGraph (Fin n)) (R : RotSys G) : Prop :=
  ∃ (d : ℝ) (x : Fin n → E3), IsContactDrawing G d x ∧ IsAngular R x

open scoped Classical in
/-- D2 (EnumComplete): every rotation system with `12 ≤ n ≤ 15` vertices of a 3-connected graph with
degrees 3 to 5 in the input class of `plantri -p -f6` read on a drawing (`D2Regions.PlaneClass`)
is isomorphic, possibly reversing the orientation, to an entry of `L` with the same number of
vertices. The body of `D2Regions.EnumCompletePlane`. -/
def EnumComplete (L : Set PlaneGraph) : Prop :=
  ∀ n : ℕ, 12 ≤ n → n ≤ 15 → ∀ (G : SimpleGraph (Fin n)) (R : RotSys G),
    KConnected G 3 → (∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5) → D2Regions.PlaneClass G R →
      ∃ P ∈ L, P.n = n ∧ R.IsoRefl P.R

/-- D3 (Killed): every case of `L` is refuted on `[dlo, dhi]`: for every entry `P`, with
`k = 15 - P.n` free points in any `k` distinct hexagons, every assignment satisfying the relation
system has a valid gluing whose configuration fires Pair or Local (with a frame of `F`). -/
def Killed (L : Set PlaneGraph) (F : Set Frame) : Prop :=
  ∀ P ∈ L, ∀ k : ℕ, P.n + k = 15 → ∀ (H : HexChoice P k) (A : Assign P k),
    dlo ≤ A.d → A.d ≤ dhi → RelSys P H A →
      ∃ g : GlueData P k, g.Valid ∧ (PairFires P A (glueY H A g) ∨ LocalFires F (glueY H A g))

/-- D4 (Attained): `F` is not empty; for the root `u ∈ (1/2, 7/10)` of the quintic, every frame
consists of unit vectors, its listed pairs are pairs of distinct indices with inner product `u`,
and any two distinct points have inner product at most `u`. -/
def AttainedHyp (F : Set Frame) : Prop :=
  F.Nonempty ∧ ∃ u : ℝ, 1 / 2 < u ∧ u < 7 / 10 ∧ quintic u = 0 ∧
    ∀ q ∈ F, (∀ i, ‖q.p i‖ = 1) ∧ (∀ ij ∈ q.S, ij.1 ≠ ij.2 ∧ ⟪q.p ij.1, q.p ij.2⟫ = u) ∧
      ∀ i j, i ≠ j → ⟪q.p i, q.p j⟫ ≤ u

/-! ## The Fejes Tóth bound -/

/-- The Fejes Tóth bound for 15 points in the form the capstone uses: every configuration of 15
points with minimal distance `d` has `d ≤ dhi = 56.6716°`. L. Fejes Tóth (1943) gives
`d₁₅ ≤ arccos ((cot² ω - 1) / 2)`, `ω = 15π / 78`, which is `56.67…°`. Proved in Lean as
`fejesToth_bound` (module `Tammes15.FejesToth.Bound`), which `reduction` uses; not a hypothesis. -/
def FejesTothBound : Prop :=
  ∀ d : ℝ, Nonempty (Config 15 d) → d ≤ dhi

end Tammes15
