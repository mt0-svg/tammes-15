import Tammes15.Attained.Frames
import Tammes15.Draw.Frame
import Tammes15.PaperSteps.Defs
import Tammes15.PaperSteps.FrameDefs
import Tammes15.PaperSteps.Roots2

/-!
# The group `D` on the frame points, and the targets as images of `C1` and `C3`

`ρ(x, y, z) = (z, x, y)` and `τ(x, y, z) = (-z, -y, -x)` permute the eighteen frame points
(`pt_rho`, `pt_tau`), so each element of `D` acts on their indices (`dIdx`, `pt_dWord`). Each
target configuration `c` of `TieData` lists, in its own order, the images under the element
`tieG c` of `D` of the points of `C1` or `C3` (`tieX c`) relabelled by `tieSigma c` (`tie_idx`),
and the exact frame points lie in its boxes (`inTieBoxes_pt`). The coordinates of the frame points
are signed copies of nine values (`ptPat`), each within `1e-39` of a decimal (`sym_close`, from
Roots2). The normalisation of the program is an orthogonal map when the two points are unit vectors
at inner product of absolute value below one (`normalize_isometry`).
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15 Attained

/-! ## The group `D` -/

theorem rhoL_apply (v : E3) : rhoL v = !₂[v.ofLp 2, v.ofLp 0, v.ofLp 1] := by
  ext i
  fin_cases i
  all_goals
    dsimp
    simp [rhoL, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
    try rfl

theorem tauL_apply (v : E3) : tauL v = !₂[-v.ofLp 2, -v.ofLp 1, -v.ofLp 0] := by
  ext i
  fin_cases i <;> simp [tauL, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.swap_apply_of_ne_of_ne]

/-- `ρ` on the indices of the frame points (the order of `Attained.ptN`). -/
def rhoIdx : Fin 18 → Fin 18 := ![1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9, 14, 12, 13, 17, 15, 16]

/-- `τ` on the indices of the frame points. -/
def tauIdx : Fin 18 → Fin 18 := ![15, 16, 17, 12, 13, 14, 9, 11, 10, 6, 8, 7, 3, 4, 5, 0, 1, 2]

theorem pt_rho (b u : ℝ) (k : Fin 18) : rhoL (pt b u k) = pt b u (rhoIdx k) := by
  ext i
  fin_cases i <;>
    simp [rhoL, pt, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, ptN, rhoIdx,
      show (finRotate 3 : Equiv.Perm (Fin 3)).symm 0 = 2 by decide,
      show (finRotate 3 : Equiv.Perm (Fin 3)).symm 1 = 0 by decide,
      show (finRotate 3 : Equiv.Perm (Fin 3)).symm 2 = 1 by decide] <;>
    fin_cases k <;> simp

theorem pt_tau (b u : ℝ) (k : Fin 18) : tauL (pt b u k) = pt b u (tauIdx k) := by
  have htauL (v : E3) : tauL v = !₂[-v.ofLp 2, -v.ofLp 1, -v.ofLp 0] := by
    ext i
    fin_cases i <;>
      simp [tauL, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
        show (Equiv.swap (0 : Fin 3) 2) 0 = 2 by decide,
        show (Equiv.swap (0 : Fin 3) 2) 1 = 1 by decide,
        show (Equiv.swap (0 : Fin 3) 2) 2 = 0 by decide]
  rw [htauL]
  ext i
  fin_cases i <;>
    fin_cases k <;>
    simp [pt, ptN, tauIdx] <;>
    ring

/-- The six elements of `D` on the indices of the frame points. -/
def dIdx : Fin 6 → Fin 18 → Fin 18 :=
  ![id, rhoIdx, fun k => rhoIdx (rhoIdx k), tauIdx, fun k => rhoIdx (tauIdx k),
    fun k => rhoIdx (rhoIdx (tauIdx k))]

theorem pt_dWord (b u : ℝ) (w : Fin 6) (k : Fin 18) : dWord w (pt b u k) = pt b u (dIdx w k) := by
  fin_cases w <;> simp [dWord, dIdx, LinearIsometryEquiv.trans_apply, pt_rho, pt_tau]

/-! ## `C1` and `C3` -/

/-- The indices kept by `C3` (`true`) or `C1` (`false`). -/
def keepX : Bool → Fin 15 → Fin 18
  | true => keepC3
  | false => keepC1

/-- `C3` (`true`) or `C1` (`false`). -/
noncomputable def frameX : Bool → Frame
  | true => frameC3
  | false => frameC1

theorem frameX_p (X : Bool) (m : Fin 15) : (frameX X).p m = pt bR uR (keepX X m) := by
  cases X <;> rfl

theorem frameX_mem (X : Bool) : frameX X ∈ ({frameC1, frameC3} : Set Frame) := by
  cases X <;> simp [frameX]

theorem frameX_unit (X : Bool) (m : Fin 15) : ‖(frameX X).p m‖ = 1 := by
  cases X
  · exact frameC1_unit m
  · exact frameC3_unit m

theorem frameX_contact (X : Bool) : ∀ ij ∈ (frameX X).S,
    ij.1 ≠ ij.2 ∧ ⟪(frameX X).p ij.1, (frameX X).p ij.2⟫ = uR := by
  cases X
  · exact frameC1_contact
  · exact frameC3_contact

/-! ## The target configurations as images of `C1` and `C3` -/

theorem tie_idx : ∀ c i, tieIdx c i = dIdx (tieG c) (keepX (tieX c) (tieSigma c i)) := by
  decide

theorem tieSigma_bijective (c : Fin 8) : Function.Bijective (tieSigma c) := by
  revert c
  decide

/-- `tieSigma c` as a permutation. -/
noncomputable def tieSigmaEquiv (c : Fin 8) : Fin 15 ≃ Fin 15 :=
  Equiv.ofBijective (tieSigma c) (tieSigma_bijective c)

/-- The contacts listed for a target configuration are contacts of the frame it comes from. -/
theorem tie_contacts : ∀ c, ∀ e ∈ tieContacts c,
    (tieSigma c e.1, tieSigma c e.2) ∈ (frameX (tieX c)).S ∨
      (tieSigma c e.2, tieSigma c e.1) ∈ (frameX (tieX c)).S := by
  decide +kernel

/-- The point `i` of the target configuration `c`, exactly. -/
theorem pt_tieIdx (c : Fin 8) (i : Fin 15) :
    pt bR uR (tieIdx c i) = dWord (tieG c) ((frameX (tieX c)).p (tieSigma c i)) := by
  rw [tie_idx, ← pt_dWord, frameX_p]

/-! ## The coordinates of the frame points against the target boxes -/

/-- The layout of the coordinates of the eighteen frame points (`Attained.ptN`) on nine values
`v 0, …, v 8`, standing for `a, b, c, d, e, f, r, s, t`. -/
def ptPat (v : Fin 9 → ℝ) : Fin 18 → Fin 3 → ℝ :=
  ![![v 0, v 1, v 2], ![v 2, v 0, v 1], ![v 1, v 2, v 0],
    ![v 3, v 4, v 5], ![v 5, v 3, v 4], ![v 4, v 5, v 3],
    ![v 6, v 7, v 8], ![v 8, v 6, v 7], ![v 7, v 8, v 6],
    ![-v 8, -v 7, -v 6], ![-v 6, -v 8, -v 7], ![-v 7, -v 6, -v 8],
    ![-v 5, -v 4, -v 3], ![-v 4, -v 3, -v 5], ![-v 3, -v 5, -v 4],
    ![-v 2, -v 1, -v 0], ![-v 1, -v 0, -v 2], ![-v 0, -v 2, -v 1]]

/-- The nine numerators. -/
def symN (b u : ℝ) : Fin 9 → ℝ :=
  ![aN b u, bN b u, cN b u, dN b u, eN b u, fN b u, rN b u, sN b u, tN b u]

/-- The nine decimals of the targets (rows 0, 3 and 6 of `ptMid`). -/
def symMid : Fin 9 → ℝ :=
  ![0.8950239687385675817752053027300069363982, 0.1714903098093749755411220556254286252362, 0.4117319140228847855850930801629745052897, 0.8009928994820256966989893094450395527570, 0.3819643241495056538159414100761232449542, -0.4609920064994498908133393714792726773162, 0.7788399620322553112220048616995050840131, -0.6271780756254064502195746100187979488791, 0.007481643964200167173391057544491047266499]

theorem pt_ofLp (b u : ℝ) (k : Fin 18) (l : Fin 3) :
    (pt b u k).ofLp l = ptPat (fun s => symN b u s / 225008) k l := by
  fin_cases k <;> fin_cases l <;> simp [pt, ptN, ptPat, symN, neg_div]

theorem ptPat_close {v w : Fin 9 → ℝ} {ε : ℝ} (h : ∀ s, |v s - w s| ≤ ε) (k : Fin 18) (l : Fin 3) :
    |ptPat v k l - ptPat w k l| ≤ ε := by
  fin_cases k <;> fin_cases l <;> simp [ptPat] <;>
    first
    | apply h
    | rw [show -v _ + w _ = -(v _ - w _) by ring, abs_neg]
      apply h

theorem sym_close (s : Fin 9) : |symN bR uR s / 225008 - symMid s| ≤ 1e-39 := by
  have hu := uR_mem2
  have hb := bR_mem2
  have key : ∀ x m : ℝ, (225008 : ℝ) * (m - 1e-39) ≤ x ∧ x ≤ (225008 : ℝ) * (m + 1e-39) →
      |x / 225008 - m| ≤ 1e-39 := by
    intro x m h
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
      linarith [h.1]
    · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num)]
      linarith [h.2]
  fin_cases s
  · exact key _ _ (close_aN bR uR hu hb)
  · exact key _ _ (close_bN bR uR hu hb)
  · exact key _ _ (close_cN bR uR hu hb)
  · exact key _ _ (close_dN bR uR hu hb)
  · exact key _ _ (close_eN bR uR hu hb)
  · exact key _ _ (close_fN bR uR hu hb)
  · exact key _ _ (close_rN bR uR hu hb)
  · exact key _ _ (close_sN bR uR hu hb)
  · exact key _ _ (close_tN bR uR hu hb)

/-! The decimals of the targets against those of the frame, one configuration at a time. -/

theorem tie_mid_0 (i : Fin 15) (l : Fin 3) :
    |ptPat symMid (tieIdx 0 i) l - tieMid 0 i l| ≤ 1e-39 := by
  fin_cases i <;> fin_cases l <;> norm_num [ptPat, symMid, tieIdx, tieMid, abs_le]

theorem tie_mid_1 (i : Fin 15) (l : Fin 3) :
    |ptPat symMid (tieIdx 1 i) l - tieMid 1 i l| ≤ 1e-39 := by
  fin_cases i <;> fin_cases l <;> norm_num [ptPat, symMid, tieIdx, tieMid, abs_le]

theorem tie_mid_2 (i : Fin 15) (l : Fin 3) :
    |ptPat symMid (tieIdx 2 i) l - tieMid 2 i l| ≤ 1e-39 := by
  fin_cases i <;> fin_cases l <;> norm_num [ptPat, symMid, tieIdx, tieMid, abs_le]

theorem tie_mid_3 (i : Fin 15) (l : Fin 3) :
    |ptPat symMid (tieIdx 3 i) l - tieMid 3 i l| ≤ 1e-39 := by
  fin_cases i <;> fin_cases l <;> norm_num [ptPat, symMid, tieIdx, tieMid, abs_le]

theorem tie_mid_4 (i : Fin 15) (l : Fin 3) :
    |ptPat symMid (tieIdx 4 i) l - tieMid 4 i l| ≤ 1e-39 := by
  fin_cases i <;> fin_cases l <;> norm_num [ptPat, symMid, tieIdx, tieMid, abs_le]

theorem tie_mid_5 (i : Fin 15) (l : Fin 3) :
    |ptPat symMid (tieIdx 5 i) l - tieMid 5 i l| ≤ 1e-39 := by
  fin_cases i <;> fin_cases l <;> norm_num [ptPat, symMid, tieIdx, tieMid, abs_le]

theorem tie_mid_6 (i : Fin 15) (l : Fin 3) :
    |ptPat symMid (tieIdx 6 i) l - tieMid 6 i l| ≤ 1e-39 := by
  fin_cases i <;> fin_cases l <;> norm_num [ptPat, symMid, tieIdx, tieMid, abs_le]

theorem tie_mid_7 (i : Fin 15) (l : Fin 3) :
    |ptPat symMid (tieIdx 7 i) l - tieMid 7 i l| ≤ 1e-39 := by
  fin_cases i <;> fin_cases l <;> norm_num [ptPat, symMid, tieIdx, tieMid, abs_le]

theorem tie_mid (c : Fin 8) (i : Fin 15) (l : Fin 3) :
    |ptPat symMid (tieIdx c i) l - tieMid c i l| ≤ 1e-39 := by
  fin_cases c
  exacts [tie_mid_0 i l, tie_mid_1 i l, tie_mid_2 i l, tie_mid_3 i l, tie_mid_4 i l, tie_mid_5 i l,
    tie_mid_6 i l, tie_mid_7 i l]

theorem inTieBoxes_pt (c : Fin 8) : InTieBoxes c (fun i => pt bR uR (tieIdx c i)) := by
  intro i l
  dsimp [InTieBoxes]
  have hpt := pt_ofLp bR uR (tieIdx c i) l
  rw [hpt]
  have h_sym_close : ∀ s : Fin 9, |(fun s' => symN bR uR s' / 225008) s - symMid s| ≤ 1e-39 := by
    intro s
    simpa using sym_close s
  have h_ppc := ptPat_close h_sym_close (tieIdx c i) l
  have h_tm := tie_mid c i l
  have h_total : |ptPat (fun s => symN bR uR s / 225008) (tieIdx c i) l - tieMid c i l| ≤ 2e-39 := by
    calc
      |ptPat (fun s => symN bR uR s / 225008) (tieIdx c i) l - tieMid c i l|
          = |(ptPat (fun s => symN bR uR s / 225008) (tieIdx c i) l - ptPat symMid (tieIdx c i) l) +
              (ptPat symMid (tieIdx c i) l - tieMid c i l)| := by ring_nf
      _ ≤ |ptPat (fun s => symN bR uR s / 225008) (tieIdx c i) l - ptPat symMid (tieIdx c i) l|
          + |ptPat symMid (tieIdx c i) l - tieMid c i l| := abs_add_le _ _
      _ ≤ 1e-39 + 1e-39 := by
        nlinarith
      _ = 2e-39 := by ring
  have h_tieRad : tieRad c i l = 1e-38 := by
    fin_cases c <;> fin_cases i <;> fin_cases l <;> norm_num [tieRad]
  rw [h_tieRad]
  have h_2e39_le_1e38 : (2 : ℝ) * 1e-39 ≤ 1e-38 := by norm_num
  nlinarith

/-! ## The normalisation of the program -/

/-- The normalisation `tieNormalize za zb` is an orthogonal map for unit vectors `za`, `zb` with
`|⟪za, zb⟫| < 1`. -/
theorem normalize_isometry (za zb : E3) (ha : ‖za‖ = 1) (hb : ‖zb‖ = 1) (hab : |⟪za, zb⟫| < 1)
    (mirror : Bool) : ∃ O : E3 ≃ₗᵢ[ℝ] E3, ∀ z, tieNormalize za zb mirror z = O z := by
  set c := ⟪za, zb⟫ with hc
  set w := zb - c • za with hw
  have hwa : ⟪za, w⟫ = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ha, ← hc]
    ring
  have hw2 : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    rw [hw, norm_sub_sq_real, real_inner_smul_right, norm_smul, real_inner_comm, ← hc, ha, hb,
      Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hc2 : c ^ 2 < 1 := by
    have h1 := abs_lt.mp hab
    nlinarith [h1.1, h1.2]
  have hwpos : 0 < ‖w‖ := by
    have h : 0 < ‖w‖ ^ 2 := by rw [hw2]; linarith
    exact lt_of_le_of_ne (norm_nonneg _) (fun h0 => by rw [← h0] at h; simp at h)
  set e1 := ‖w‖⁻¹ • w with he1d
  have he1 : ‖e1‖ = 1 := by
    rw [he1d, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
  have hae1 : ⟪za, e1⟫ = 0 := by rw [he1d, real_inner_smul_right, hwa, mul_zero]
  set e2 := cross za e1 with he2d
  have he2 : ‖e2‖ = 1 := norm_cross_frame za e1 ha he1 hae1
  have hae2 : ⟪za, e2⟫ = 0 := inner_cross_self za e1
  have he12 : ⟪e1, e2⟫ = 0 := by
    rw [he2d, inner_cross_perm, cross_self_eq_zero, inner_zero_right]
  set s : ℝ := if mirror then -1 else 1 with hsd
  have hs : s * s = 1 := by by_cases hm : mirror <;> simp [hsd, hm]
  have hse2 : ‖s • e2‖ = 1 := by
    rw [norm_smul, he2, mul_one]
    by_cases hm : mirror <;> simp [hsd, hm]
  set v : Fin 3 → E3 := ![e1, s • e2, za] with hv
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hv, real_inner_self_eq_norm_sq, he1, he2, ha, real_inner_smul_left,
        real_inner_smul_right, hae1, hae2, he12, real_inner_comm za, real_inner_comm e1, hs, hse2]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    intro z _
    rw [frame_expand za e1 z ha he1 hae1]
    have h0 : za ∈ Submodule.span ℝ (Set.range v) := Submodule.subset_span ⟨2, rfl⟩
    have h1 : e1 ∈ Submodule.span ℝ (Set.range v) := Submodule.subset_span ⟨0, rfl⟩
    have h2 : s • e2 ∈ Submodule.span ℝ (Set.range v) := Submodule.subset_span ⟨1, rfl⟩
    have h2' : e2 ∈ Submodule.span ℝ (Set.range v) := by
      have := Submodule.smul_mem _ s h2
      rwa [smul_smul, hs, one_smul] at this
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ h0)
      (Submodule.smul_mem _ _ h1)) (Submodule.smul_mem _ _ h2')
  refine ⟨(OrthonormalBasis.mk hon hsp).repr, fun z => ?_⟩
  ext l
  fin_cases l <;> by_cases hm : mirror <;>
    simp [tieNormalize, OrthonormalBasis.repr_apply_apply, hv, real_inner_comm z,
      real_inner_smul_left, hsd, he1d, he2d, hw, hc, hm]

end Tammes15.PaperSteps
