import Tammes15.Statement

/-!
# Theorem C: objects

The first order change `Lmap` of the contact inner products, the tangent fields `TPerp`
orthogonal to the infinitesimal rotations, and the named computational hypothesis `KappaBound`
(Lemma 5.1, hypothesis D1); `tpart p x` is the tangent part
of the displacement `x - p` of a unit vector `p` (the `t_i` of the proof of Theorem C).
-/

open Real Matrix WithLp
open scoped RealInnerProductSpace

namespace Tammes15

/-- Cross product on `E3`. -/
noncomputable def cross (a b : E3) : E3 := toLp 2 (ofLp a ⨯₃ ofLp b)

/-- The first order change of the contact inner products, `L(t)_{ij}`. -/
noncomputable def Lmap {n : ℕ} (p t : Fin n → E3) (ij : Fin n × Fin n) : ℝ :=
  ⟪p ij.1, t ij.2⟫ + ⟪p ij.2, t ij.1⟫

/-- Tangent fields orthogonal to the infinitesimal rotations. -/
def TPerp {n : ℕ} (p t : Fin n → E3) : Prop :=
  (∀ i, ⟪p i, t i⟫ = 0) ∧ ∑ i, cross (p i) (t i) = 0

/-- The named computational hypothesis of Lemma 5.1: `κ ≥ κ0`. -/
def KappaBound {n : ℕ} (p : Fin n → E3) (S : Finset (Fin n × Fin n)) (κ0 : ℝ) : Prop :=
  ∀ t : Fin n → E3, TPerp p t → ∃ ij ∈ S, κ0 * Real.sqrt (∑ i, ‖t i‖ ^ 2) ≤ Lmap p t ij

/-- The tangent part `t = (x - p) + (|x - p|² / 2) p` of the displacement of `p` to `x`. -/
noncomputable def tpart (p x : E3) : E3 := (x - p) + (‖x - p‖ ^ 2 / 2) • p

end Tammes15
