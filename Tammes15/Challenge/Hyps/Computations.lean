import Tammes15.Challenge.Hyps.Case
import Tammes15.Challenge.Local41.Defs

/-!
# The four computations D1 to D4, stated exactly

The hybrid theorem `Tammes15.reduction` (module `Tammes15.Hyps.Reduction`) proves
`Tammes15.Conjecture` from four hypotheses on a list `L` of plane graphs and a set `F` of labelled
frame configurations. Each hypothesis is a statement that a recorded computation checks; Section 8
of the paper names, for each one, the program, its output and the step of the proof it gives.

* `KappaHyp F` (D1): the first-order rigidity constant of every frame is at least `kappa0`.
* `EnumComplete L` (D2): every plane graph of the class of Section 5.1 with 12 to 15 vertices is
  isomorphic to an entry of `L`, possibly with the orientation reversed.
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

/-- D2 (EnumComplete): every plane graph of the class with `12 ≤ n ≤ 15` vertices is isomorphic,
possibly reversing the orientation, to an entry of `L` with the same number of vertices. -/
def EnumComplete (L : Set PlaneGraph) : Prop :=
  ∀ n : ℕ, 12 ≤ n → n ≤ 15 → ∀ (G : SimpleGraph (Fin n)) (R : RotSys G),
    InClass ⟨n, G, R⟩ → ∃ P ∈ L, P.n = n ∧ R.IsoRefl P.R

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
