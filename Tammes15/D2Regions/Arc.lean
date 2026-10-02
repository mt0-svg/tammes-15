import Tammes15.D2Regions.Defs
import Tammes15.Geom.Basic
import Tammes15.Vendor.EM8.ContactGeometryGlobal

/-!
# Minor arcs (Lemma 3.20 of the paper)

`minorArc p q` for unit `p, q` with `q ≠ -p`: symmetric in its ends, contains them, its points
other than the ends lie on the open arc `OpenContactArc p q` of the eight-point code, it is
preconnected (the image of the segment `[p, q]` under normalisation), and its midpoint is none of
its ends when `p ≠ q`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.D2Regions

open Tammes15.Vendor.EM8.SquareAntiprismVerification (OpenContactArc)

theorem minorArc_comm (p q : E3) : minorArc p q = minorArc q p := by
  ext z
  constructor
  · intro h
    rcases h with ⟨hnorm, s, t, hs, ht, hz⟩
    refine ⟨hnorm, t, s, ht, hs, ?_⟩
    rw [hz, add_comm]
  · intro h
    rcases h with ⟨hnorm, s, t, hs, ht, hz⟩
    refine ⟨hnorm, t, s, ht, hs, ?_⟩
    rw [hz, add_comm]

theorem left_mem_minorArc (p q : E3) (hp : ‖p‖ = 1) : p ∈ minorArc p q := by
  unfold minorArc
  refine ⟨hp, 1, 0, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · simp

theorem right_mem_minorArc (p q : E3) (hq : ‖q‖ = 1) : q ∈ minorArc p q := by
  unfold minorArc
  exact ⟨hq, 0, 1, le_rfl, by norm_num, by simp⟩

/-- A point of the closed arc other than its ends lies on the open arc. -/
theorem mem_openContactArc_of_mem_minorArc (p q z : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hz : z ∈ minorArc p q) (hzp : z ≠ p) (hzq : z ≠ q) : z ∈ OpenContactArc p q := by
  rcases hz with ⟨hnorm, s, t, hs, ht, hz_eq⟩
  have hs_pos : 0 < s := by
    by_contra! h
    have hs_zero : s = 0 := by linarith
    rw [hs_zero, zero_smul, zero_add] at hz_eq
    have ht_one : t = 1 := by
      have hnorm' : ‖t • q‖ = 1 := by rw [← hz_eq, hnorm]
      rw [norm_smul, Real.norm_of_nonneg ht, hq, mul_one] at hnorm'
      exact hnorm'
    rw [ht_one, one_smul] at hz_eq
    exact hzq hz_eq
  have ht_pos : 0 < t := by
    by_contra! h
    have ht_zero : t = 0 := by linarith
    rw [ht_zero, zero_smul, add_zero] at hz_eq
    have hs_one : s = 1 := by
      have hnorm' : ‖s • p‖ = 1 := by rw [← hz_eq, hnorm]
      rw [norm_smul, Real.norm_of_nonneg hs, hp, mul_one] at hnorm'
      exact hnorm'
    rw [hs_one, one_smul] at hz_eq
    exact hzp hz_eq
  have hsum_pos : 0 < s + t := by linarith
  have hsum_ne_zero : s + t ≠ 0 := by linarith
  set τ := t / (s + t) with hτ_def
  have hτ_pos : 0 < τ := by
    rw [hτ_def]
    exact div_pos ht_pos hsum_pos
  have hτ_lt_one : τ < 1 := by
    rw [hτ_def]
    exact (div_lt_one hsum_pos).mpr (by linarith)
  have h_comb_eq : (1 - τ) • p + τ • q = ((s + t)⁻¹ : ℝ) • z := by
    dsimp [τ]
    have hcoeff1 : (s + t)⁻¹ * s = s / (s + t) := by
      field_simp [hsum_ne_zero]
    have hcoeff2 : (s + t)⁻¹ * t = t / (s + t) := by
      field_simp [hsum_ne_zero]
    have hcoeff : (1 - t / (s + t)) = s / (s + t) := by
      field_simp [hsum_ne_zero]
      ring
    calc
      (1 - t / (s + t)) • p + (t / (s + t)) • q
          = (s / (s + t)) • p + (t / (s + t)) • q := by rw [hcoeff]
      _ = ((s + t)⁻¹ * s) • p + ((s + t)⁻¹ * t) • q := by rw [hcoeff1, hcoeff2]
      _ = (s + t)⁻¹ • (s • p) + (s + t)⁻¹ • (t • q) := by simp [smul_smul]
      _ = (s + t)⁻¹ • (s • p + t • q) := by rw [smul_add]
      _ = (s + t)⁻¹ • z := by rw [hz_eq]
  have h_norm_comb : ‖(1 - τ) • p + τ • q‖ = (s + t)⁻¹ := by
    rw [h_comb_eq]
    rw [norm_smul]
    have hpos : 0 ≤ (s + t)⁻¹ := by
      rw [inv_nonneg]
      linarith
    rw [Real.norm_of_nonneg hpos, hnorm, mul_one]
  refine ⟨τ, hτ_pos, hτ_lt_one, ?_⟩
  calc
    z = 1 • z := by simp
    _ = ((s + t) * (s + t)⁻¹) • z := by
      field_simp [hsum_ne_zero]
      simp
    _ = (s + t) • ((s + t)⁻¹ • z) := by simp [smul_smul]
    _ = (s + t) • ((1 - τ) • p + τ • q) := by rw [h_comb_eq]
    _ = ((s + t)⁻¹)⁻¹ • ((1 - τ) • p + τ • q) := by simp
    _ = ‖(1 - τ) • p + τ • q‖⁻¹ • ((1 - τ) • p + τ • q) := by rw [h_norm_comb]

/-- The closed minor arc is preconnected. -/
theorem isPreconnected_minorArc (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : q ≠ -p) :
    IsPreconnected (minorArc p q) := by
  have hy0 : ∀ θ : ℝ, (1 - θ) • p + θ • q ≠ 0 := by
    intro θ h0
    have h1 := congrArg (fun w => ⟪w, p⟫) h0
    have h2 := congrArg (fun w => ⟪w, q⟫) h0
    simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hp, hq,
      inner_zero_left] at h1 h2
    rw [real_inner_comm] at h1
    have hc : ⟪p, q⟫ = -1 := by linear_combination h1 + h2
    apply hpq
    have hsq : ‖p + q‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, hp, hq, hc]
      norm_num
    have hpq0 : p + q = 0 := norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq)
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hpq0
  set g : ℝ → E3 := fun θ => ‖(1 - θ) • p + θ • q‖⁻¹ • ((1 - θ) • p + θ • q) with hg
  have hl : Continuous (fun θ : ℝ => (1 - θ) • p + θ • q) := by fun_prop
  have hcont : Continuous g :=
    (hl.norm.inv₀ (fun θ => norm_ne_zero_iff.mpr (hy0 θ))).smul hl
  have heq : minorArc p q = g '' Set.Icc 0 1 := by
    ext z
    constructor
    · rintro ⟨hz, s, t, hs, ht, rfl⟩
      have hst : 0 < s + t := by
        rcases (add_nonneg hs ht).lt_or_eq with h | h
        · exact h
        · exfalso
          have hs0 : s = 0 := by linarith
          have ht0 : t = 0 := by linarith
          rw [hs0, ht0, zero_smul, zero_smul, add_zero, norm_zero] at hz
          exact zero_ne_one hz
      refine ⟨t / (s + t), ⟨div_nonneg ht hst.le, (div_le_one hst).mpr (by linarith)⟩, ?_⟩
      have hy : (1 - t / (s + t)) • p + (t / (s + t)) • q = (s + t)⁻¹ • (s • p + t • q) := by
        rw [one_sub_div hst.ne', add_sub_cancel_right, div_eq_inv_mul, div_eq_inv_mul, smul_add,
          smul_smul, smul_smul]
      simp only [hg]
      rw [hy, norm_smul, hz, mul_one, norm_inv, Real.norm_of_nonneg hst.le, inv_inv, smul_smul,
        mul_inv_cancel₀ hst.ne', one_smul]
    · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
      refine ⟨norm_smul_inv_norm (hy0 θ), ‖(1 - θ) • p + θ • q‖⁻¹ * (1 - θ),
        ‖(1 - θ) • p + θ • q‖⁻¹ * θ, mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (by linarith),
        mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) h0, ?_⟩
      simp only [hg]
      rw [smul_add, smul_smul, smul_smul]
  rw [heq]
  exact isPreconnected_Icc.image g hcont.continuousOn

/-- The normalised midpoint lies on the arc. -/
theorem midpoint_mem_minorArc (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : q ≠ -p) :
    ‖p + q‖⁻¹ • (p + q) ∈ minorArc p q := by
  have h_add_ne_zero : p + q ≠ 0 := by
    intro hzero
    apply hpq
    have := add_eq_zero_iff_eq_neg.mp hzero
    calc
      q = -(-q) := by simp
      _ = -p := by rw [← this]
  have h_norm_pos : 0 < ‖p + q‖ := by
    have h_nonneg := norm_nonneg (p + q)
    by_contra! hle
    have hzero : ‖p + q‖ = 0 := by linarith
    have h_add_zero : p + q = 0 := norm_eq_zero.mp hzero
    exact h_add_ne_zero h_add_zero
  have h_coeff_nonneg : 0 ≤ ‖p + q‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have h_norm_smul : ‖‖p + q‖⁻¹ • (p + q)‖ = 1 := by
    calc
      ‖‖p + q‖⁻¹ • (p + q)‖ = ‖‖p + q‖⁻¹‖ * ‖p + q‖ := norm_smul _ _
      _ = |‖p + q‖⁻¹| * ‖p + q‖ := by rw [Real.norm_eq_abs]
      _ = ‖p + q‖⁻¹ * ‖p + q‖ := by rw [abs_of_pos (inv_pos.mpr h_norm_pos)]
      _ = 1 := by field_simp [ne_of_gt h_norm_pos]
  refine ⟨h_norm_smul, ‖p + q‖⁻¹, ‖p + q‖⁻¹, h_coeff_nonneg, h_coeff_nonneg, ?_⟩
  rw [smul_add]

/-- The normalised midpoint of two distinct, non-antipodal unit vectors is neither of them. -/
theorem midpoint_ne_left (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hne : p ≠ q)
    (hpq : q ≠ -p) : ‖p + q‖⁻¹ • (p + q) ≠ p := by
  intro h
  have hpq0 : p + q ≠ 0 := fun h0 => hpq (by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h0)
  have hr : 0 < ‖p + q‖ := norm_pos_iff.mpr hpq0
  have h2 : p + q = ‖p + q‖ • p := by
    calc p + q = ‖p + q‖ • (‖p + q‖⁻¹ • (p + q)) := by
          rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      _ = ‖p + q‖ • p := by rw [h]
  have h3 : q = (‖p + q‖ - 1) • p := by
    rw [sub_smul, one_smul, ← h2]
    abel
  have h4 : |‖p + q‖ - 1| = 1 := by
    have := congrArg norm h3
    rw [norm_smul, hp, hq, mul_one, Real.norm_eq_abs] at this
    exact this.symm
  rcases (abs_eq zero_le_one).mp h4 with h5 | h5
  · apply hne
    rw [h3, h5, one_smul]
  · apply hpq
    rw [h3, h5, neg_one_smul]

end Tammes15.D2Regions
