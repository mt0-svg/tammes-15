import Tammes15.Vendor.EM8.PolygonExcess
import Tammes15.Draw.Defs

/-!
# Common definitions of the face chain

* `AvoidReach G u v`: reachability in `G` with the vertices `u` and `v` deleted.
* `cross_eq_crossVec`: the cross product of the package is the one of the eight-point code.
* `face_fst`, `face_rot_symm`: the face permutation starts at the end of a dart, and the face
  step into the corner of a dart `e` comes from the reversed dart `R.rot e`.
-/

open Real Matrix WithLp InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15.FaceChain

open Tammes15.Vendor.EM8.SquareAntiprismVerification

/-- Reachability in `G` with the vertices `u` and `v` deleted (every step joins two vertices other
than `u` and `v`; a vertex reaches itself). -/
def AvoidReach {V : Type} (G : SimpleGraph V) (u v : V) : V → V → Prop :=
  Relation.ReflTransGen (fun i j => G.Adj i j ∧ i ≠ u ∧ i ≠ v ∧ j ≠ u ∧ j ≠ v)

theorem cross_eq_crossVec (a b : E3) : cross a b = crossVec a b := by
  ext i
  fin_cases i <;> simp [cross, crossVec, crossProduct]

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem face_fst (R : RotSys G) (e : G.Dart) : (R.face e).fst = e.snd := by
  have h := R.rot_fst (R.rot.symm e.symm)
  rw [Equiv.apply_symm_apply] at h
  simpa [RotSys.face] using h.symm

theorem face_rot_symm {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (e : G.Dart) :
    R.face (R.rot e).symm = e := by
  unfold RotSys.face; simp

end Tammes15.FaceChain
