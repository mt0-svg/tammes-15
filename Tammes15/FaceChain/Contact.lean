import Tammes15.FaceChain.Interfaces
import Tammes15.FaceChain.ThreeConn
import Tammes15.FaceChain.Sizes
import Tammes15.Hyps.Transport
import Tammes15.Trigrows.Rows

/-!
# Lemmas A.7, 4.3 and 4.4 for a contact graph

`faceconvex_contact` proves the statement of the same name in `Tammes15.Draw.Iface`: strict
support of every face (Lemma A.7 in cone form) through the generalized eight-point chain on
`Fin n` (`Setup.strictSupportFace`), carried to the vertex type `V` along `Fintype.equivFin V`
(`RotSys.map`, and the transport lemmas of `Tammes15.Hyps.Transport`); face sizes 3 to 6
(`faceSizes_of`, `face_perimeter_lt`); and 3-connectivity (`threeconn`).
-/

open Real Matrix WithLp InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15.FaceChain

open Tammes15.Vendor.EM8.SquareAntiprismVerification

section
variable {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  {G : SimpleGraph V} {G' : SimpleGraph V'}

/-- The bijection of darts of a graph isomorphism. -/
def dartIso (φ : G ≃g G') : G.Dart ≃ G'.Dart where
  toFun := dmap φ
  invFun := dmap φ.symm
  left_inv e := by
    ext <;> simp [dmap]
  right_inv := dmap_dmap_symm φ

/-- The rotation system carried along a graph isomorphism. -/
def RotSys.map (φ : G ≃g G') (R : RotSys G) : RotSys G' where
  rot := (dartIso φ).permCongr R.rot
  rot_fst e := by
    simp [Equiv.permCongr_apply, dartIso, dmap, R.rot_fst]
  rot_cycle a b h := by
    obtain ⟨i, hi⟩ := R.rot_cycle ((dartIso φ).symm a) ((dartIso φ).symm b)
      (by simp [dartIso, dmap, h])
    refine ⟨i, ?_⟩
    have hz : ((dartIso φ).permCongr R.rot) ^ i = (dartIso φ).permCongr (R.rot ^ i) :=
      (map_zpow (dartIso φ).permCongrHom R.rot i).symm
    rw [hz, Equiv.permCongr_apply, hi, Equiv.apply_symm_apply]

theorem RotSys.map_rot (φ : G ≃g G') (R : RotSys G) (e : G.Dart) :
    dmap φ (R.rot e) = (RotSys.map φ R).rot (dmap φ e) := by
  show dmap φ (R.rot e) = dartIso φ (R.rot ((dartIso φ).symm (dartIso φ e)))
  rw [Equiv.symm_apply_apply]
  rfl

theorem RotSys.map_rot_symm (φ : G ≃g G') (R : RotSys G) (e' : G'.Dart) :
    dmap φ.symm ((RotSys.map φ R).rot e') = R.rot (dmap φ.symm e') := by
  show (dartIso φ).symm (dartIso φ (R.rot ((dartIso φ).symm e'))) = R.rot ((dartIso φ).symm e')
  rw [Equiv.symm_apply_apply]

end

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Lemmas A.7 (cone form), 4.3 (sizes) and 4.4. -/
theorem faceconvex_contact [DecidableRel G.Adj] (dlo d : ℝ) (h7 : 7 * dlo > 2 * π)
    (hlo : dlo ≤ d) (hd : 0 < d ∧ d < π / 2) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hsep : ∀ a b, a ≠ b → d ≤ sdist (x a) (x b))
    (hG : ∀ a b, G.Adj a b ↔ a ≠ b ∧ sdist (x a) (x b) = d)
    (R : RotSys G) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, alpha d ≤ ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (hdeg : ∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5)
    (_hconn : G.Connected) (h2 : KConnected G 2) (_hsph : R.Spherical)
    (hface3 : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e)
    (hwalk : ∀ e : G.Dart, ∀ m n : ℕ, m < n → n < Function.minimalPeriod R.face e →
      ((R.face ^ m) e).fst ≠ ((R.face ^ n) e).fst) :
    StrictSupportFace R x ∧ FaceSizes R 3 6 ∧ KConnected G 3 := by
  have hcpos : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π := fun e =>
    ⟨lt_of_lt_of_le (by linarith [(alpha_bounds d hd).1, pi_pos]) (hcorner e).1, (hcorner e).2⟩
  have hinj : Function.Injective x := by
    intro a b hab
    by_contra hne
    have h := hsep a b hne
    rw [hab, sdist_self _ (hx b)] at h
    linarith [hd.1]
  have hGd : ∀ a b, G.Adj a b → sdist (x a) (x b) = d := fun a b h => ((hG a b).mp h).2
  have htd : ∀ e : G.Dart, tdir (x e.fst) (x e.snd) ≠ 0 := by
    intro e h
    have hn := tdir_norm _ _ (hx e.fst) (hx e.snd)
    rw [h, norm_zero, hGd _ _ e.adj] at hn
    exact (Real.sin_pos_of_pos_of_lt_pi hd.1 (by linarith [hd.2, pi_pos])).ne' hn.symm
  have hS : StrictSupportFace R x := by
    let φ : G ≃g G.map (Fintype.equivFin V).toEmbedding :=
      SimpleGraph.Iso.map (Fintype.equivFin V) G
    let R' := RotSys.map φ R
    let x' : Fin (Fintype.card V) → E3 := fun v' => x (φ.symm v')
    let S : Setup (Fintype.card V) :=
      { d := d, x := x', G := G.map (Fintype.equivFin V).toEmbedding, R := R', hd := hd
        unit := fun v => hx _
        sep := fun a b hab => hsep _ _ (φ.symm.injective.ne hab)
        adj := fun a b => by
          rw [← φ.symm.map_adj_iff, hG, φ.symm.injective.ne_iff]
        angular := isAngular_iso R R' φ (RotSys.map_rot φ R) x hR
        corner := fun e' => by
          have h := hcpos (dmap φ.symm e')
          have hr := RotSys.map_rot_symm φ R e'
          rw [← hr] at h
          simpa [dmap, x'] using h }
    have h' := S.strictSupportFace (iso_kConnected φ 2 h2)
    have hb := strictSupportFace_iso R' R φ.symm (RotSys.map_rot_symm φ R) x' h'
    have hxx : (fun v => x' (φ.symm.symm v)) = x := by
      funext v
      simp [x']
    rwa [hxx] at hb
  refine ⟨hS, ?_, ?_⟩
  · exact faceSizes_of R dlo d h7 hlo hface3 fun e => face_perimeter_lt R x hx d hGd hS hface3 e
  · exact threeconn R x hx hinj d hGd htd hR hcpos hS (fun a => (hdeg a).1) h2 hwalk

end Tammes15.FaceChain
