import Tammes15.Draw.Defs

/-!
# Exposed pairs, the hull graph and oriented arguments

Definitions for the proof of Corollary A.6 by the convex hull of the points (paper,
Lemma A.5 and Corollary A.6). `ExposedPair x a b`: some linear functional takes its
maximum over the point set `x` exactly at `x a` and `x b` (an edge of the hull polytope, since no
three points of a sphere are collinear). `hullGraph x` is the graph of exposed pairs. `oarg z p q`
is the oriented angle at `z` from the arc `z p` to the arc `z q`, the argument inside
`ocorner z p q` before its reduction to `[0, 2π)`; its sums along closed walks are winding
numbers about `z`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

/-- `{a, b}` is an exposed pair of the point set `x`: some linear functional takes its maximum
over `x` exactly at `x a` and `x b`. -/
def ExposedPair {V : Type*} (x : V → E3) (a b : V) : Prop :=
  a ≠ b ∧ ∃ N : E3, ⟪x a, N⟫ = ⟪x b, N⟫ ∧ ∀ z, z ≠ a → z ≠ b → ⟪x z, N⟫ < ⟪x a, N⟫

/-- The oriented angle at `z` from the arc `z p` to the arc `z q`, in `(-π, π]`: the argument
inside `ocorner z p q`, before its reduction to `[0, 2π)`. -/
noncomputable def oarg (z p q : E3) : ℝ :=
  Complex.arg ⟨⟪tdir z p, tdir z q⟫, ⟪z, cross (tdir z p) (tdir z q)⟫⟩

theorem ExposedPair.symm {V : Type*} {x : V → E3} {a b : V} (h : ExposedPair x a b) :
    ExposedPair x b a := by
  obtain ⟨hab, N, hN, hlt⟩ := h
  exact ⟨hab.symm, N, hN.symm, fun z hzb hza => hN ▸ hlt z hza hzb⟩

/-- The hull graph: the exposed pairs of the point set `x`. -/
def hullGraph {V : Type*} (x : V → E3) : SimpleGraph V where
  Adj a b := ExposedPair x a b
  symm := ⟨fun _ _ h => ExposedPair.symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem hullGraph_adj {V : Type*} (x : V → E3) (a b : V) :
    (hullGraph x).Adj a b ↔ ExposedPair x a b := Iff.rfl

end Tammes15
