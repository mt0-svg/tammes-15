import Tammes15.D2Regions.Faces
import Tammes15.FaceChain.Interfaces
import Tammes15.Vendor.EM8.ContactSectorCover

/-!
# The cover (Lemma 3.20 of the paper: every point lies in the closed polygon of a face walk)

Every unit vector lies in the closed polygon of some face of a contact drawing with an angular
rotation system, corners in `(0, π)` and strictly supported faces of at least three darts. A vertex
`a` nearest to `z` (largest `⟪x a, z⟫`) has a corner sector holding `z`
(`contactRotateAt_sectors_cover` of the eight-point code, through `FaceChain.Setup`); the face of
the first dart of that corner is a polygon in cone form with contact sides, and `fan_inClosed` puts
`z` in its closed polygon. No Euler relation and no area are used.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.D2Regions

open Tammes15.Geom Tammes15.FaceChain Tammes15.Vendor.EM8.SquareAntiprismVerification

theorem cover {n : ℕ} (S : FaceChain.Setup n) (hconv : StrictSupportFace S.R S.x)
    (h3 : ∀ e : S.G.Dart, 3 ≤ Function.minimalPeriod S.R.face e) (hdeg : ∀ a, ∃ b, S.G.Adj a b)
    (hn : 0 < n) (z : E3) : ∃ e : S.G.Dart, InClosed (faceSeq S.R S.x e) z := by
  classical
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => ⟪S.x i, z⟫) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨b, hab⟩ := hdeg a
  have hne : ∃ j, j ≠ a ∧ inner ℝ (S.x a) (S.x j) = cos S.d := by
    obtain ⟨h1, h2⟩ := (S.contactAdj_iff a b).mpr hab
    exact ⟨b, h1.symm, h2⟩
  obtain ⟨j, hleft, hright⟩ :=
    contactRotateAt_sectors_cover S.x (cos S.d) S.hY S.hc S.irreducible a hne z
  set e : S.G.Dart := S.dartEquiv ⟨a, j⟩ with he
  have hrot : (S.R.rot e).snd = (contactRotateAt S.x (cos S.d) S.hY S.hc a j).val := by
    rw [he, ← S.dartEquiv_rotate]
    rfl
  have hA := faceSeq_isCPoly S.R S.x S.unit hconv e (h3 e)
  have h0 : faceSeq S.R S.x e 0 = S.x a := by
    simp only [faceSeq, pow_zero, Equiv.Perm.one_apply]
    rfl
  have h1 : faceSeq S.R S.x e 1 = S.x j.val := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, faceSeq_succ, pow_zero, Equiv.Perm.one_apply]
    rfl
  have hlast : faceSeq S.R S.x e (Function.minimalPeriod S.R.face e - 1) =
      S.x (contactRotateAt S.x (cos S.d) S.hY S.hc a j).val := by
    have h := rot_symm_face_pow S.R e 0 (by have := h3 e; omega)
    rw [zero_add] at h
    simp only [faceSeq]
    rw [← h, dart_symm_fst, pow_zero, Equiv.Perm.one_apply, hrot]
  refine ⟨e, fan_inClosed hA (cos S.d) ?_ ?_ z ?_ ?_ ?_⟩
  · intro i
    rw [faceSeq_succ]
    exact ((S.contactAdj_iff _ _).mpr ((S.R.face ^ i) e).adj).2
  · intro i hi
    rw [h0]
    refine S.bound a _ ?_
    intro h
    apply hi
    rw [h0, h]
    rfl
  · intro i
    rw [h0]
    exact hmax _ (Finset.mem_univ _)
  · rw [h0, h1, cross_eq_crossVec]
    exact hleft
  · rw [h0, hlast, cross_eq_crossVec]
    exact hright

end Tammes15.D2Regions
