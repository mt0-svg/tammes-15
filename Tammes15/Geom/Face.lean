import Tammes15.Geom.Basic
import Tammes15.Draw.Defs

/-!
# Faces of a rotation system as polygons in cone form

The face of a dart `e` of a rotation system `R` on a drawing `x` is read as the periodic sequence
`faceSeq R x e n = x ((R.face ^ n) e).fst` of its vertices, of period the minimal period of `e`
under `R.face`. Consecutive vertices are the ends of the darts of the face walk
(`faceSeq_succ`), so `StrictSupportFace` with faces of at least three darts makes it an `IsCPoly`
(`faceSeq_isCPoly`), and a point on the inner side of every side of the walk is `Inside` it
(`inside_faceSeq_iff`).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Geom

/-- The vertex sequence of the face of `e`. -/
def faceSeq {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (R : RotSys G)
    (x : V → E3) (e : G.Dart) : ℕ → E3 :=
  fun n => x ((R.face ^ n) e).fst

theorem face_fst {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (R : RotSys G)
    (f : G.Dart) : (R.face f).fst = f.snd := by
  have h := R.rot_fst (R.rot.symm f.symm)
  rw [Equiv.apply_symm_apply] at h
  show (R.rot.symm f.symm).fst = f.snd
  rw [← h]
  rfl

theorem face_pow_add_apply {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (e : G.Dart) (i j : ℕ) :
    (R.face ^ (i + j)) e = (R.face ^ i) ((R.face ^ j) e) := by
  rw [pow_add, Equiv.Perm.mul_apply]

theorem faceSeq_succ {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (R : RotSys G)
    (x : V → E3) (e : G.Dart) (n : ℕ) : faceSeq R x e (n + 1) = x ((R.face ^ n) e).snd := by
  simp only [faceSeq]
  rw [pow_succ', Equiv.Perm.mul_apply, face_fst]

theorem face_pow_minimalPeriod {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (e : G.Dart) : (R.face ^ Function.minimalPeriod R.face e) e = e := by
  rw [Equiv.Perm.coe_pow]
  exact Function.isPeriodicPt_minimalPeriod R.face e

theorem faceSeq_periodic {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (x : V → E3) (e : G.Dart) (n : ℕ) :
    faceSeq R x e (n + Function.minimalPeriod R.face e) = faceSeq R x e n := by
  simp only [faceSeq]
  rw [face_pow_add_apply R e n, face_pow_minimalPeriod]

/-- A positive power of the face permutation below the minimal period moves the dart. -/
theorem face_pow_ne {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (R : RotSys G)
    (e : G.Dart) (k : ℕ) (hk0 : 0 < k) (hk : k < Function.minimalPeriod R.face e) :
    (R.face ^ k) e ≠ e := by
  intro h
  have hp : Function.IsPeriodicPt R.face k e := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow]
    exact h
  have := Function.IsPeriodicPt.minimalPeriod_le hk0 hp
  omega

theorem minimalPeriod_face_pow {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (e : G.Dart) (j : ℕ) :
    Function.minimalPeriod R.face ((R.face ^ j) e) = Function.minimalPeriod R.face e := by
  classical
  have hper : e ∈ Function.periodicPts R.face := by
    refine ⟨orderOf R.face, orderOf_pos _, ?_⟩
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  rw [Equiv.Perm.coe_pow]
  exact Function.minimalPeriod_apply_iterate hper j

theorem faceSeq_face_pow {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (x : V → E3) (e : G.Dart) (j n : ℕ) :
    faceSeq R x ((R.face ^ j) e) n = faceSeq R x e (j + n) := by
  simp only [faceSeq]
  rw [add_comm j n, face_pow_add_apply]

/-- The face of a dart of a strictly supported drawing is a polygon in cone form. -/
theorem faceSeq_isCPoly {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hconv : StrictSupportFace R x)
    (e : G.Dart) (h3 : 3 ≤ Function.minimalPeriod R.face e) :
    IsCPoly (Function.minimalPeriod R.face e) (faceSeq R x e) := by
  refine ⟨h3, fun i => hx _, faceSeq_periodic R x e, fun i k hk2 hkP => ?_⟩
  set f := (R.face ^ i) e with hf
  have hPf : Function.minimalPeriod R.face f = Function.minimalPeriod R.face e :=
    minimalPeriod_face_pow R e i
  have h1 : (R.face ^ k) f ≠ f := face_pow_ne R f k (by omega) (by rw [hPf]; exact hkP)
  have h2 : (R.face ^ k) f ≠ R.face f := by
    intro h
    have h' : R.face ((R.face ^ (k - 1)) f) = R.face f := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
      exact h
    exact face_pow_ne R f (k - 1) (by omega) (by rw [hPf]; omega) (R.face.injective h')
  have e1 : faceSeq R x e i = x f.fst := rfl
  have e2 : faceSeq R x e (i + 1) = x f.snd := faceSeq_succ R x e i
  have e3 : faceSeq R x e (i + k) = x ((R.face ^ k) f).fst := (faceSeq_face_pow R x e i k).symm
  rw [e1, e2, e3]
  exact hconv f k h1 h2

theorem inside_faceSeq_iff {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (x : V → E3) (e : G.Dart) (p : E3) :
    Inside (faceSeq R x e) p ↔
      ∀ n : ℕ, 0 < ⟪cross (x ((R.face ^ n) e).fst) (x ((R.face ^ n) e).snd), p⟫ := by
  unfold Inside
  refine forall_congr' fun n => ?_
  rw [faceSeq_succ]
  rfl

/-- Every side of a face is an edge of the graph. -/
theorem faceSeq_adj {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (R : RotSys G)
    (x : V → E3) (e : G.Dart) (n : ℕ) :
    ∃ f : G.Dart, faceSeq R x e n = x f.fst ∧ faceSeq R x e (n + 1) = x f.snd := by
  exact ⟨(R.face ^ n) e, rfl, faceSeq_succ R x e n⟩

end Tammes15.Geom
