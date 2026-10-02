import Tammes15.FejesToth.Facets
import Tammes15.FejesToth.Saturate
import Tammes15.FejesToth.Numerics
import Tammes15.Hyps.Computations

/-!
# The Fejes Tóth bound for 15 points

`fejesToth_bound : FejesTothBound` (Proposition 8.3; definition in `Tammes15.Hyps.Computations`),
by the route of the paper, Section 8: a configuration at `d > dhi` is
`c₀`-separated (N1), extends to a saturated `c₀`-separated set `S` (step (2)) with no closed
hemisphere; its hull (Lemma 3.7) has facets bounded by the triangle lemma (steps (4), (5)); the count
of fan triangles (step (6)) gives `(2|S| - 4) 2θ₀ ≤ 4π` with `|S| ≥ 15`, against `θ₀ > π / 13` (N2).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

namespace FejesToth

/-- Saturation at a level `c ≥ 0` leaves no closed hemisphere (the hypothesis of Lemma hull). -/
theorem hB_of_sat {V : Type} (x : V → E3) (c : ℝ) (hc : 0 ≤ c)
    (hsat : ∀ u : E3, ‖u‖ = 1 → ∃ a, c < ⟪u, x a⟫) :
    ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫ := by
  intro e he
  have hnorm_pos : 0 < ‖e‖ := (norm_pos_iff.mpr he)
  have hinv_pos : 0 < (‖e‖⁻¹ : ℝ) := inv_pos.mpr hnorm_pos
  set u := (‖e‖⁻¹ : ℝ) • e with hu_def
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv_pos]
    field_simp [hnorm_pos.ne.symm]
  rcases hsat u hu_norm with ⟨a, ha⟩
  have hinner_eq : ⟪u, x a⟫ = (‖e‖⁻¹ : ℝ) * ⟪e, x a⟫ := by
    dsimp [u]
    rw [real_inner_smul_left]
  have hpos_mul : 0 < (‖e‖⁻¹ : ℝ) * ⟪e, x a⟫ := by
    linarith
  have hpos_inner : 0 < ⟪e, x a⟫ :=
    pos_of_mul_pos_right hpos_mul (le_of_lt hinv_pos)
  refine ⟨a, ?_⟩
  rw [real_inner_comm]
  exact hpos_inner

theorem inner_lt_cos_of_lt_arccos (t s : ℝ) (ht0 : 0 ≤ t) (ht : t < Real.arccos s)
    (hs1 : -1 ≤ s) (hs2 : s ≤ 1) : s < Real.cos t := by
  have harccos_le_pi : Real.arccos s ≤ π := Real.arccos_le_pi s
  have hcos_lt : Real.cos (Real.arccos s) < Real.cos t :=
    Real.cos_lt_cos_of_nonneg_of_le_pi ht0 harccos_le_pi ht
  have hcos_eq : Real.cos (Real.arccos s) = s := Real.cos_arccos hs1 hs2
  linarith

end FejesToth

open scoped Classical
open FejesToth

/-- Proposition 8.3: the Fejes Tóth bound, `FejesTothBound`. -/
theorem fejesToth_bound : FejesTothBound := by
  intro d ⟨X⟩
  by_contra hd
  push Not at hd
  -- step 1: the points are `c₀`-separated, `c₀ = 0.5494377`
  have hdhi0 : 0 ≤ dhi := by unfold dhi; positivity
  have hN1 : Real.cos dhi ≤ 5494377 / 10 ^ 7 := by
    have h := N1
    rwa [show π * (566716 / 1800000) = dhi by unfold dhi; ring] at h
  have hsep15 : ∀ i j, i ≠ j → ⟪X.pt i, X.pt j⟫ < 5494377 / 10 ^ 7 := by
    intro i j hij
    have h1 := X.sep i j hij
    unfold sdist at h1
    have hb := abs_le.mp ((abs_real_inner_le_norm (X.pt i) (X.pt j)).trans
      (by rw [X.unit i, X.unit j, one_mul]))
    have h2 := inner_lt_cos_of_lt_arccos dhi _ hdhi0 (hd.trans_le h1) hb.1 hb.2
    linarith
  have hinjX : Function.Injective X.pt := by
    intro i j h
    by_contra hij
    have h1 := hsep15 i j hij
    rw [h, real_inner_self_eq_norm_sq, X.unit j] at h1
    norm_num at h1
  -- step 2: a saturated `c₀`-separated superset `S`
  obtain ⟨S, hXS, hSu, hSsep, hSsat⟩ := exists_saturated (5494377 / 10 ^ 7) (by norm_num)
    (Finset.univ.image X.pt)
    (fun y hy => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact X.unit i)
    (fun y hy z hz hyz => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
      exact (hsep15 i j fun h => hyz (congrArg X.pt h)).le)
  -- step 3: the hull of `S`
  let x : S → E3 := fun s => s.1
  have hx : ∀ v, ‖x v‖ = 1 := fun v => hSu v.1 v.2
  have hinj : Function.Injective x := Subtype.val_injective
  have hsat : ∀ u : E3, ‖u‖ = 1 → ∃ a, (5494377 / 10 ^ 7 : ℝ) < ⟪u, x a⟫ := fun u hu => by
    obtain ⟨s, hs, h⟩ := hSsat u hu
    exact ⟨⟨s, hs⟩, h⟩
  have hsepx : ∀ a b, a ≠ b → ⟪x a, x b⟫ ≤ 5494377 / 10 ^ 7 := fun a b hab =>
    hSsep a.1 a.2 b.1 b.2 fun h => hab (Subtype.ext h)
  have hB := hB_of_sat x _ (by norm_num) hsat
  obtain ⟨rho, hrho⟩ := exists_angular x hx (hull_distinctDirs x hx hinj hB)
  have : Nonempty S := ⟨⟨X.pt 0, hXS (Finset.mem_image_of_mem _ (Finset.mem_univ 0))⟩⟩
  -- steps 4 to 6: every facet, then the count
  have hcount := hull_fan_count x hx hinj hB rho hrho _
    (fun C => facet_fan_bound x hx hinj hB rho hrho (5494377 / 10 ^ 7) (by norm_num) (by norm_num)
      hsepx hsat C)
  -- `|S| ≥ 15`
  have hcard : (15 : ℝ) ≤ Fintype.card S := by
    have h1 : (Finset.univ.image X.pt).card = 15 := by
      rw [Finset.card_image_of_injective _ hinjX, Finset.card_univ, Fintype.card_fin]
    have h2 : (Finset.univ.image X.pt).card ≤ S.card := Finset.card_le_card hXS
    have h3 : Fintype.card S = S.card := Fintype.card_coe S
    have : 15 ≤ Fintype.card S := by omega
    exact_mod_cast this
  -- step 7: `θ₀ > π / 13` contradicts `(2|S| - 4) 2θ₀ ≤ 4π`
  have hN2 := N2
  have hθ : 0 < Complex.arg ⟨1 + 3 * (5494377 / 10 ^ 7 : ℝ),
      (1 - 5494377 / 10 ^ 7) * √(1 + 2 * (5494377 / 10 ^ 7 : ℝ))⟩ :=
    lt_trans (by positivity) hN2
  have h26 : (26 : ℝ) * (2 * Complex.arg ⟨1 + 3 * (5494377 / 10 ^ 7 : ℝ),
      (1 - 5494377 / 10 ^ 7) * √(1 + 2 * (5494377 / 10 ^ 7 : ℝ))⟩) ≤
      (2 * (Fintype.card S : ℝ) - 4) * (2 * Complex.arg ⟨1 + 3 * (5494377 / 10 ^ 7 : ℝ),
      (1 - 5494377 / 10 ^ 7) * √(1 + 2 * (5494377 / 10 ^ 7 : ℝ))⟩) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith [Real.pi_pos]

end Tammes15
