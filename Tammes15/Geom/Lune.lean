import Tammes15.Geom.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The volume of a lune in coordinates

`csect θ` is the part of the open unit ball of `E3` over the planar sector `0 < y₀`,
`y₀ cos θ + y₁ sin θ ≤ 0` of angle `θ`; its volume is `2/3 · θ` for `0 ≤ θ ≤ π`
(`volume_csect`). Slicing along the last coordinate, the slice at height `t` with `|t| < 1` is the
planar sector of radius `√(1 - t²)` and angle `θ`, of area `θ (1 - t²) / 2` (`area_sector`, in
polar coordinates through `polar_sector_iff`), and `∫_{-1}^{1} θ (1 - t²) / 2 dt = 2θ/3`.
-/

open Real MeasureTheory
open scoped ENNReal

namespace Tammes15.Geom

/-- The lune of angle `θ` in coordinates. -/
def csect (θ : ℝ) : Set E3 := {y | ‖y‖ < 1 ∧ 0 < y 0 ∧ y 0 * cos θ + y 1 * sin θ ≤ 0}

theorem measurableSet_csect (θ : ℝ) : MeasurableSet (csect θ) := by
  unfold csect
  measurability

/-- The sector condition in polar coordinates. -/
theorem polar_sector_iff (r φ θ : ℝ) (hr : 0 < r) (hφ1 : -π < φ) (hφ2 : φ < π) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ π) :
    (0 < r * cos φ ∧ r * cos φ * cos θ + r * sin φ * sin θ ≤ 0) ↔
      -(π / 2) < φ ∧ φ < π / 2 ∧ φ ≤ θ - π / 2 := by
  constructor
  · intro ⟨hcosφ, hcosφθ⟩
    have hcosφ_pos : 0 < cos φ :=
      (mul_pos_iff_of_pos_left hr).mp hcosφ
    have hcos_sub_nonpos : cos (φ - θ) ≤ 0 := by
      have h_eq : r * cos φ * cos θ + r * sin φ * sin θ = r * cos (φ - θ) := by
        calc
          r * cos φ * cos θ + r * sin φ * sin θ = r * (cos φ * cos θ + sin φ * sin θ) := by ring
          _ = r * cos (φ - θ) := by rw [Real.cos_sub φ θ]
      have h_nonpos' : r * cos (φ - θ) ≤ 0 := by
        rw [← h_eq]
        exact hcosφθ
      nlinarith
    have hφ_range : -(π / 2) < φ ∧ φ < π / 2 := by
      by_cases hle : φ ≤ -(π / 2)
      · have hcos_le : cos φ ≤ 0 := by
          have hx₁ : π / 2 ≤ -(φ) := by linarith
          have hx₂ : -(φ) ≤ π + π / 2 := by
            linarith [hφ1]
          have h := Real.cos_nonpos_of_pi_div_two_le_of_le hx₁ hx₂
          rw [Real.cos_neg] at h
          exact h
        linarith
      · have hlow : -(π / 2) < φ := by linarith
        by_cases hle2 : π / 2 ≤ φ
        · have hcos_le : cos φ ≤ 0 :=
            Real.cos_nonpos_of_pi_div_two_le_of_le hle2 (by linarith [hφ2])
          linarith
        · have hhigh : φ < π / 2 := by linarith
          exact ⟨hlow, hhigh⟩
    have hφ_θ : φ ≤ θ - π / 2 := by
      by_contra! hlt
      -- Then φ - θ > -π/2, i.e., -(φ - θ) < π/2
      -- Also φ < π/2 and θ ≥ 0, so φ - θ < π/2
      -- So φ - θ ∈ (-π/2, π/2), hence cos(φ - θ) > 0, contradiction
      have hpos : 0 < cos (φ - θ) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> linarith
      linarith [hcos_sub_nonpos, hpos]
    exact ⟨hφ_range.1, hφ_range.2, hφ_θ⟩
  · intro ⟨hφ_low, hφ_high, hφ_θ⟩
    have hcosφ_pos : 0 < cos φ :=
      Real.cos_pos_of_mem_Ioo ⟨hφ_low, hφ_high⟩
    have hcos_sub_nonpos : cos (φ - θ) ≤ 0 := by
      have hθ_sub_φ_ge : π / 2 ≤ θ - φ := by linarith
      have hθ_sub_φ_le : θ - φ ≤ π + π / 2 := by
        linarith
      have hcos_θ_sub_φ_nonpos : cos (θ - φ) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hθ_sub_φ_ge hθ_sub_φ_le
      have h_eq_cos : cos (θ - φ) = cos (φ - θ) := by
        have : θ - φ = -(φ - θ) := by ring
        rw [this, Real.cos_neg]
      rw [h_eq_cos] at hcos_θ_sub_φ_nonpos
      exact hcos_θ_sub_φ_nonpos
    have h_first : 0 < r * cos φ := mul_pos hr hcosφ_pos
    have h_second : r * cos φ * cos θ + r * sin φ * sin θ ≤ 0 := by
      have h_eq : r * cos φ * cos θ + r * sin φ * sin θ = r * cos (φ - θ) := by
        calc
          r * cos φ * cos θ + r * sin φ * sin θ = r * (cos φ * cos θ + sin φ * sin θ) := by ring
          _ = r * cos (φ - θ) := by rw [Real.cos_sub φ θ]
      rw [h_eq]
      nlinarith
    exact ⟨h_first, h_second⟩

/-- `∫⁻ r in (0, ρ), r = ρ² / 2`. -/
theorem lintegral_Ioo_ofReal_id (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∫⁻ r in Set.Ioo 0 ρ, ENNReal.ofReal r = ENNReal.ofReal (ρ ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ, integral_id]
    ring_nf
  · exact (continuous_id.integrableOn_Icc (a := 0) (b := ρ)).mono_set Set.Ioo_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun r hr => hr.1.le)

/-- The weight `r` of polar coordinates on a rectangle `A × B`. -/
theorem setLIntegral_prod_ofReal_fst (A B : Set ℝ) :
    ∫⁻ p in A ×ˢ B, ENNReal.ofReal p.1 =
      (∫⁻ r in A, ENNReal.ofReal r) * volume B := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have h := lintegral_prod_mul (μ := volume.restrict A) (ν := volume.restrict B)
    (f := fun r => ENNReal.ofReal r) (g := fun _ => 1)
    measurable_id.ennreal_ofReal.aemeasurable aemeasurable_const
  simp only [mul_one, lintegral_one, Measure.restrict_apply_univ] at h
  exact h

/-- Area of a planar sector of radius `ρ` and angle `θ`. -/
theorem area_sector (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < ρ ^ 2 ∧ 0 < p.1 ∧ p.1 * cos θ + p.2 * sin θ ≤ 0} =
      ENNReal.ofReal (θ * ρ ^ 2 / 2) := by
  set S := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < ρ ^ 2 ∧ 0 < p.1 ∧ p.1 * cos θ + p.2 * sin θ ≤ 0}
    with hS_def
  set T := {p : ℝ × ℝ | p.1 < ρ ∧ -(π / 2) < p.2 ∧ p.2 < π / 2 ∧ p.2 ≤ θ - π / 2} with hT_def
  have hSm : MeasurableSet S := by
    rw [hS_def]
    measurability
  have hTm : MeasurableSet T := by
    rw [hT_def]
    measurability
  have hmem : ∀ p ∈ polarCoord.target, polarCoord.symm p ∈ S ↔ p ∈ T := by
    rintro ⟨r, φ⟩ ⟨hr, hφ1, hφ2⟩
    have hr : 0 < r := hr
    rw [polarCoord_symm_apply]
    simp only [hS_def, hT_def, Set.mem_ofPred_eq]
    have hsq : (r * cos φ) ^ 2 + (r * sin φ) ^ 2 = r ^ 2 := by
      have := cos_sq_add_sin_sq φ
      linear_combination r ^ 2 * this
    rw [hsq, polar_sector_iff r φ θ hr hφ1 hφ2 hθ0 hθ]
    have hrr : r ^ 2 < ρ ^ 2 ↔ r < ρ := pow_lt_pow_iff_left₀ hr.le hρ two_ne_zero
    rw [hrr]
  have heq : Set.EqOn (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • S.indicator 1 (polarCoord.symm p))
      (T.indicator fun p => ENNReal.ofReal p.1) polarCoord.target := by
    intro p hp
    show ENNReal.ofReal p.1 • S.indicator 1 (polarCoord.symm p) =
      T.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) p
    by_cases hpT : p ∈ T
    · rw [Set.indicator_of_mem ((hmem p hp).mpr hpT), Set.indicator_of_mem hpT, Pi.one_apply,
        smul_eq_mul, mul_one]
    · rw [Set.indicator_of_notMem (mt (hmem p hp).mp hpT), Set.indicator_of_notMem hpT,
        smul_zero]
  rw [← lintegral_indicator_one hSm, ← lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet heq,
    setLIntegral_indicator hTm]
  have hθ' : θ - π / 2 < π := by linarith [pi_pos]
  have hlo : Set.Ioo 0 ρ ×ˢ Set.Ioo (-(π / 2)) (θ - π / 2) ⊆ T ∩ polarCoord.target := by
    rintro ⟨r, φ⟩ ⟨⟨hr0, hrρ⟩, hφ1, hφ2⟩
    refine ⟨⟨hrρ, hφ1, by linarith, hφ2.le⟩, hr0, by linarith [pi_pos], by linarith⟩
  have hhi : T ∩ polarCoord.target ⊆ Set.Ioo 0 ρ ×ˢ Set.Icc (-(π / 2)) (θ - π / 2) := by
    rintro ⟨r, φ⟩ ⟨⟨hrρ, hφ1, -, hφ2⟩, hr0, -, -⟩
    exact ⟨⟨hr0, hrρ⟩, hφ1.le, hφ2⟩
  have hval : ∀ B : Set ℝ, volume B = ENNReal.ofReal θ →
      ∫⁻ p in Set.Ioo 0 ρ ×ˢ B, ENNReal.ofReal p.1 = ENNReal.ofReal (θ * ρ ^ 2 / 2) := by
    intro B hB
    rw [setLIntegral_prod_ofReal_fst, lintegral_Ioo_ofReal_id ρ hρ, hB,
      ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  apply le_antisymm
  · calc ∫⁻ p in T ∩ polarCoord.target, ENNReal.ofReal p.1
        ≤ ∫⁻ p in Set.Ioo 0 ρ ×ˢ Set.Icc (-(π / 2)) (θ - π / 2), ENNReal.ofReal p.1 :=
          lintegral_mono_set hhi
      _ = _ := hval _ (by rw [Real.volume_Icc]; ring_nf)
  · calc ENNReal.ofReal (θ * ρ ^ 2 / 2)
        = ∫⁻ p in Set.Ioo 0 ρ ×ˢ Set.Ioo (-(π / 2)) (θ - π / 2), ENNReal.ofReal p.1 :=
          (hval _ (by rw [Real.volume_Ioo]; ring_nf)).symm
      _ ≤ _ := lintegral_mono_set hlo

/-- `csect θ` in the coordinates `(y₂, (y₀, y₁))`. -/
def csectCoords (θ : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {z | z.2.1 ^ 2 + z.2.2 ^ 2 < 1 - z.1 ^ 2 ∧ 0 < z.2.1 ∧ z.2.1 * cos θ + z.2.2 * sin θ ≤ 0}

theorem measurableSet_csectCoords (θ : ℝ) : MeasurableSet (csectCoords θ) := by
  unfold csectCoords
  measurability

/-- The slice of `csectCoords θ` at height `t` is the sector of radius `√(1 - t²)`, empty for
`1 ≤ t²`. -/
theorem volume_csectCoords_slice (θ t : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π) :
    volume (Prod.mk t ⁻¹' csectCoords θ) =
      (Set.Ioo (-1) 1).indicator (fun t : ℝ => ENNReal.ofReal (θ * (1 - t ^ 2) / 2)) t := by
  by_cases ht : t ∈ Set.Ioo (-1 : ℝ) 1
  · have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hsq : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := sq_sqrt h1
    have hs : Prod.mk t ⁻¹' csectCoords θ = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < √(1 - t ^ 2) ^ 2 ∧
        0 < p.1 ∧ p.1 * cos θ + p.2 * sin θ ≤ 0} := by
      rw [hsq]
      rfl
    rw [Set.indicator_of_mem ht, hs, area_sector _ θ (sqrt_nonneg _) hθ0 hθ, hsq]
  · rw [Set.indicator_of_notMem ht]
    have h1 : 1 ≤ t ^ 2 := by
      by_contra h
      exact ht ⟨by nlinarith, by nlinarith⟩
    have he : Prod.mk t ⁻¹' csectCoords θ = ∅ := by
      ext p
      simp only [Set.mem_preimage, csectCoords, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h
      nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    rw [he, measure_empty]

theorem volume_csectCoords (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π) :
    volume (csectCoords θ) = ENNReal.ofReal (2 / 3 * θ) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_csectCoords θ)]
  simp_rw [volume_csectCoords_slice θ _ hθ0 hθ]
  rw [lintegral_indicator measurableSet_Ioo, ← ofReal_integral_eq_lintegral_ofReal,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  · congr 1
    have h1 : IntervalIntegrable (fun t : ℝ => (1 : ℝ)) volume (-1) 1 := intervalIntegrable_const
    have h2 : IntervalIntegrable (fun t : ℝ => t ^ 2) volume (-1) 1 :=
      intervalIntegral.intervalIntegrable_pow 2
    simp_rw [mul_div_assoc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_sub h1 h2, integral_pow]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
    ring
  · exact (Continuous.integrableOn_Icc (by fun_prop) (a := -1) (b := 1)).mono_set
      Set.Ioo_subset_Icc_self
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht => ?_)
    have : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    positivity

/-- `‖y‖ < 1` in coordinates. -/
theorem norm_lt_one_iff_coords (y : E3) : ‖y‖ < 1 ↔ y 0 ^ 2 + y 1 ^ 2 < 1 - y 2 ^ 2 := by
  have h : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [← sq_lt_one_iff₀ (norm_nonneg y), h]
  constructor <;> intro h' <;> linarith

theorem volume_csect (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π) :
    volume (csect θ) = ENNReal.ofReal (2 / 3 * θ) := by
  let T : E3 → ℝ × (ℝ × ℝ) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ))) ∘
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)) ∘ WithLp.ofLp
  have hT : MeasurePreserving T volume volume := by
    have h1 : MeasurePreserving (WithLp.ofLp : E3 → Fin 3 → ℝ) volume volume :=
      PiLp.volume_preserving_ofLp (Fin 3)
    have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
    have h3 : MeasurePreserving
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ)))
        volume volume := by
      rw [Measure.volume_eq_prod ℝ (Fin 2 → ℝ), Measure.volume_eq_prod ℝ (ℝ × ℝ)]
      exact (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
    exact h3.comp (h2.comp h1)
  have hpre : csect θ = T ⁻¹' csectCoords θ := by
    ext y
    simp only [csect, csectCoords, Set.mem_ofPred_eq, Set.mem_preimage, norm_lt_one_iff_coords]
    rfl
  rw [hpre, hT.measure_preimage (measurableSet_csectCoords θ).nullMeasurableSet,
    volume_csectCoords θ hθ0 hθ]

end Tammes15.Geom
