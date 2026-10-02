import Tammes15.Attained.Data

/-!
# Definitions of the statements on the frame configurations

The group `D` (`rhoL`, `tauL`, `dWord`), the frame configurations as sets of indices (`frameIdx`,
`IsFrameKeep`) and as sets of points (`frameSet`, `tC1`), and the least angular distance of fifteen
points (`minAngle`): the definitions that the statements of `local_optimality_frame` (LocalEq.lean)
and `optima_four` (Optima.lean) reach beyond `Tammes15.Attained.Data`. The module holds definitions
only, so that the challenge of Comparator can copy it whole.
-/

open Real Matrix InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15 Attained

/-! ## The group `D` -/

/-- `ρ(x, y, z) = (z, x, y)`. -/
noncomputable def rhoL : E3 ≃ₗᵢ[ℝ] E3 := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate 3)

/-- `τ(x, y, z) = (-z, -y, -x)`. -/
noncomputable def tauL : E3 ≃ₗᵢ[ℝ] E3 :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 2)).trans
    (LinearIsometryEquiv.neg ℝ)

/-- The six elements of `D`: `1, ρ, ρ², τ, ρτ, ρ²τ` (in `ρτ`, `τ` acts first). -/
noncomputable def dWord : Fin 6 → (E3 ≃ₗᵢ[ℝ] E3) :=
  ![LinearIsometryEquiv.refl ℝ E3, rhoL, rhoL.trans rhoL, tauL, tauL.trans rhoL,
    tauL.trans (rhoL.trans rhoL)]

/-! ## The frame configurations -/

/-- The indices of the frame points kept by the choice `t` in the three toggle pairs. -/
def frameIdx (t : Fin 3 → Bool) : Finset (Fin 18) :=
  Finset.univ.filter (fun k => k.val < 6 ∨ 12 ≤ k.val) ∪
    {if t 0 then 6 else 11, if t 1 then 7 else 9, if t 2 then 8 else 10}

/-- `keep` labels a frame configuration: it is injective with image the indices kept by some choice
in the toggle pairs. -/
def IsFrameKeep (keep : Fin 15 → Fin 18) : Prop :=
  Function.Injective keep ∧ ∃ t : Fin 3 → Bool, Finset.univ.image keep = frameIdx t

/-- The least angular distance of two of fifteen points, `min_{i<j} dist(x_i, x_j)`. -/
noncomputable def minAngle (x : Fin 15 → E3) : ℝ :=
  (Finset.univ.filter (fun ij : Fin 15 × Fin 15 => ij.1 < ij.2)).inf'
    ⟨((0 : Fin 15), (1 : Fin 15)), by simp⟩ (fun ij => angle (x ij.1) (x ij.2))

/-- The frame configuration keeping `t` in the toggle pairs, as a set of points. -/
noncomputable def frameSet (t : Fin 3 → Bool) : Set E3 :=
  (fun k => pt bR uR k) '' (frameIdx t : Set (Fin 18))

/-- The choice of `C1` in the toggle pairs: the points `6`, `7` and `10`. -/
def tC1 : Fin 3 → Bool := ![true, true, false]

end Tammes15.PaperSteps
