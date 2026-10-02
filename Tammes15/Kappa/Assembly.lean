import Tammes15.Kappa.Spec
import Tammes15.Kappa.Close
import Tammes15.Attained.Frames

/-!
# D1 `KappaHyp {frameC1, frameC3}`

`kappa_frame`: `KappaBound` for a frame `p` from a certificate checked in the kernel at a frame `q`
within `δ` of `p`: `kappa_of_cert` with the inequality of `cert_of_check`, whose matrix bound is
`nMat_spec` bounded by the kernel check. For C1 and C3 the kernel checks are those of
Tammes15.Kappa.C1 and C3, rewritten by `checkV` and `checkW`, `δ = 2·10⁻²⁰` (`close_C1`,
`close_C3`), and the margins are about `2.2·10⁻⁵` (C1) and `9.1·10⁻²` (C3) at `kappa0 = 6.4980·10⁻³`.
-/

set_option maxHeartbeats 0

open scoped RealInnerProductSpace

namespace Tammes15.Kappa

open Attained

/-- The error term of a certificate: the matrix bound, the perturbation to the frame, and the
TPerp forms at the rounded frame. -/
noncomputable def etaOf (B : ℕ) (δ L M K : ℝ) : ℝ := (B : ℝ) / 2 ^ 265 + Cpert δ L M + 8 * δ * K

theorem kappa_frame (p : Fin 15 → E3) (S : Finset (Fin 15 × Fin 15)) (P : List (List ℤ))
    (Sn : List (ℕ × ℕ)) (Lam : List ℕ) (Mu : List (List ℕ)) (Mk : List (List ℤ)) (RC B : ℕ)
    (δ L M K : ℝ) (hs : Shape P Sn Lam Mu Mk)
    (hN : absSum (symm (nMat (RC : ℤ) (nL Lam) (mkV P Sn) (mkW (Mu.map nL) (mkV P Sn)) Mk
      (tr (mkV P Sn)) (mkGt P))) ≤ B)
    (hL : ∑ e, lamOf Lam e ≤ L) (hM : ∑ e, ∑ f, muOf Mu e f ≤ M)
    (hK : ∑ k, ∑ b, |mkOf Mk k b| ≤ K) (hδ : 0 ≤ δ) (hclose : ∀ i m, |p i m - qOf P i m| ≤ δ)
    (hp : ∀ i, ‖p i‖ = 1) (hSl : ∀ e, SlOf Sn e ∈ S)
    (hmargin : ((RC : ℝ) / 2 ^ 64 + etaOf B δ L M K) * kappa0 ^ 2 + etaOf B δ L M K < 1) :
    KappaBound p S kappa0 := by
  let q := qOf P
  let Sl := SlOf Sn
  let lam := lamOf Lam
  let mu := muOf Mu
  let mk := mkOf Mk
  let Rc2 := (RC : ℝ) / 2 ^ 64
  let η0 := (B : ℝ) / 2 ^ 265
  let η := etaOf B δ L M K
  have hlam_nonneg : ∀ e, 0 ≤ lam e := lamOf_nonneg Lam
  have hmu_nonneg : ∀ e f, 0 ≤ mu e f := muOf_nonneg Mu
  have hκ0_pos : 0 < kappa0 := by
    unfold kappa0
    norm_num
  have hNmat_eq := nMat_spec P Sn Lam Mu Mk RC hs
  have hN_real : ((absSum (symm (nMat (RC : ℤ) (nL Lam) (mkV P Sn) (mkW (Mu.map nL) (mkV P Sn)) Mk
    (tr (mkV P Sn)) (mkGt P)))) : ℝ) ≤ (B : ℝ) := by
    exact mod_cast hN
  have htemp : (2 : ℝ) ^ 264 * (∑ a, ∑ b,
      |Nr q Sl lam mu Rc2 mk a b + Nr q Sl lam mu Rc2 mk b a|) ≤ (B : ℝ) := by
    rw [← hNmat_eq]
    exact hN_real
  have hsum_bound : (∑ a, ∑ b,
      |Nr q Sl lam mu Rc2 mk a b + Nr q Sl lam mu Rc2 mk b a|) ≤ (B : ℝ) / (2 : ℝ) ^ 264 := by
    have hpos : 0 < (2 : ℝ) ^ 264 := by norm_num
    rw [le_div_iff₀ hpos]
    nlinarith
  have hNcert : (∑ a, ∑ b,
      |Nr q Sl lam mu Rc2 mk a b + Nr q Sl lam mu Rc2 mk b a|) / 2 ≤ η0 := by
    unfold η0
    calc
      (∑ a, ∑ b, |Nr q Sl lam mu Rc2 mk a b + Nr q Sl lam mu Rc2 mk b a|) / 2 ≤
          ((B : ℝ) / (2 : ℝ) ^ 264) / 2 :=
        div_le_div_of_nonneg_right hsum_bound (by norm_num : 0 ≤ (2 : ℝ))
      _ = (B : ℝ) / ((2 : ℝ) ^ 264 * 2) := by ring
      _ = (B : ℝ) / (2 : ℝ) ^ 265 := by
        rw [pow_succ (2 : ℝ) 264]
  have hCpert_le : Cpert δ (∑ e, lam e) (∑ e, ∑ f, mu e f) ≤ Cpert δ L M :=
    Cpert_mono δ (∑ e, lam e) (∑ e, ∑ f, mu e f) L M hδ hL hM
  have hsum_mk_bound : 8 * δ * (∑ k, ∑ b, |mk k b|) ≤ 8 * δ * K := by
    have hpos : 0 ≤ 8 * δ := by nlinarith
    apply mul_le_mul_of_nonneg_left hK hpos
  have hS_le_η : η0 + Cpert δ (∑ e, lam e) (∑ e, ∑ f, mu e f) + 8 * δ * (∑ k, ∑ b, |mk k b|) ≤ η := by
    unfold η etaOf
    nlinarith
  have hcert := cert_of_check p q Sl lam mu Rc2 δ η0 mk hlam_nonneg hmu_nonneg hδ hclose hp hNcert
  have hcert' : ∀ w t, TPerp p t → -(η * (w ^ 2 + ∑ i, ‖t i‖ ^ 2)) ≤ Fform p Sl lam mu Rc2 w t := by
    intro w t ht
    have h := hcert w t ht
    have hZ : 0 ≤ w ^ 2 + ∑ i, ‖t i‖ ^ 2 := by
      have hw : 0 ≤ w ^ 2 := pow_two_nonneg w
      have ht_sum : 0 ≤ ∑ i, ‖t i‖ ^ 2 := Finset.sum_nonneg (fun i _ => pow_two_nonneg _)
      nlinarith
    have h_mul : (η0 + Cpert δ (∑ e, lam e) (∑ e, ∑ f, mu e f) + 8 * δ * ∑ k, ∑ b, |mk k b|) *
        (w ^ 2 + ∑ i, ‖t i‖ ^ 2) ≤ η * (w ^ 2 + ∑ i, ‖t i‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hS_le_η hZ
    have h_neg : -(η * (w ^ 2 + ∑ i, ‖t i‖ ^ 2)) ≤
        -((η0 + Cpert δ (∑ e, lam e) (∑ e, ∑ f, mu e f) + 8 * δ * ∑ k, ∑ b, |mk k b|) *
          (w ^ 2 + ∑ i, ‖t i‖ ^ 2)) :=
      neg_le_neg h_mul
    exact le_trans h_neg h
  exact kappa_of_cert p S Sl hSl lam mu Rc2 η kappa0 hlam_nonneg hmu_nonneg hκ0_pos hmargin hcert'

theorem Sl_mem_C1 : ∀ e, SlOf C1.Sn e ∈ frameC1.S := by
  intro e; fin_cases e <;> unfold SlOf C1.Sn frameC1 <;> decide

theorem Sl_mem_C3 : ∀ e, SlOf C3.Sn e ∈ frameC3.S := by
  intro e
  fin_cases e <;> decide

theorem margin_C1 :
    ((C1.RCn : ℝ) / 2 ^ 64 + etaOf C1.Bn (2 / 10 ^ 20) 1230 22456 104279) * kappa0 ^ 2 +
      etaOf C1.Bn (2 / 10 ^ 20) 1230 22456 104279 < 1 := by
  unfold etaOf Cpert kappa0 C1.RCn C1.Bn; set_option exponentiation.threshold 300 in norm_num

theorem margin_C3 :
    ((C3.RCn : ℝ) / 2 ^ 64 + etaOf C3.Bn (2 / 10 ^ 20) 1043 20496 95078) * kappa0 ^ 2 +
      etaOf C3.Bn (2 / 10 ^ 20) 1043 20496 95078 < 1 := by
  unfold etaOf Cpert kappa0 C3.RCn C3.Bn; set_option exponentiation.threshold 300 in norm_num

theorem checkN_C1 : absSum (symm (nMat (C1.RCn : ℤ) (nL C1.Lamn) (mkV (dLL oP C1.Pn) C1.Sn)
    (mkW (C1.Mun.map nL) (mkV (dLL oP C1.Pn) C1.Sn)) (dLL oM C1.Mkn)
    (tr (mkV (dLL oP C1.Pn) C1.Sn)) (mkGt (dLL oP C1.Pn)))) ≤ C1.Bn := by
  have h := C1.checkN
  rw [← C1.checkW, ← C1.checkV] at h
  exact h

theorem checkN_C3 : absSum (symm (nMat (C3.RCn : ℤ) (nL C3.Lamn) (mkV (dLL oP C3.Pn) C3.Sn)
    (mkW (C3.Mun.map nL) (mkV (dLL oP C3.Pn) C3.Sn)) (dLL oM C3.Mkn)
    (tr (mkV (dLL oP C3.Pn) C3.Sn)) (mkGt (dLL oP C3.Pn)))) ≤ C3.Bn := by
  have h := C3.checkN
  rw [← C3.checkW, ← C3.checkV] at h
  exact h

theorem kappa_C1 : KappaBound frameC1.p frameC1.S kappa0 :=
  kappa_frame frameC1.p frameC1.S (dLL oP C1.Pn) C1.Sn C1.Lamn C1.Mun (dLL oM C1.Mkn) C1.RCn C1.Bn
    (2 / 10 ^ 20) 1230 22456 104279 C1.shape checkN_C1 C1.sums.1 C1.sums.2.1 C1.sums.2.2
    (by positivity) close_C1 frameC1_unit Sl_mem_C1 margin_C1

theorem kappa_C3 : KappaBound frameC3.p frameC3.S kappa0 :=
  kappa_frame frameC3.p frameC3.S (dLL oP C3.Pn) C3.Sn C3.Lamn C3.Mun (dLL oM C3.Mkn) C3.RCn C3.Bn
    (2 / 10 ^ 20) 1043 20496 95078 C3.shape checkN_C3 C3.sums.1 C3.sums.2.1 C3.sums.2.2
    (by positivity) close_C3 frameC3_unit Sl_mem_C3 margin_C3

/-- D1 for the two frames of D4. -/
theorem kappaHyp : KappaHyp {Attained.frameC1, Attained.frameC3} := by
  intro q hq
  rcases hq with rfl | rfl
  · exact kappa_C1
  · exact kappa_C3

end Tammes15.Kappa
