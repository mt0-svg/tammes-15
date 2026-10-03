import Tammes15.Geom.Wheel
import Tammes15.Trigrows.Margins
import Tammes15.Trigrows.Mono
import Tammes15.Rattlers.Hex

/-!
# Lemma A.10 and Proposition 4.5 on faces in cone form

Lemma A.10 of the paper: a point `r` strictly inside a face with all sides `d`, at distance
at least `d` from every vertex, is at distance at least `h(d)` from the great circle of every side,
in the form `sin d * sin (hrad d) ≤ ⟪cross (A i) (A (i + 1)), r⟫` (`disc_side`); hence the disc
`D(r, h(d))` lies in the closed face (`disc_closed`).

Proposition 4.5 of the paper: no face with at most five vertices contains such a point. The
formal proof uses no perimeter: a side whose great circle is at distance at least `h(d)` from `r`
subtends at `r` an angle at most `α(d)` (`subtend_le_alpha`: with `u = ⟪r, A⟫`, `v = ⟪r, B⟫`,
`c = cos d`, the Gram identity gives `uv ≤ c²`, and `cos β = (c - uv)/√((1-u²)(1-v²)) ≥
(c - uv)/(1 - uv) ≥ c/(1 + c)`), and the angles at `r` add up to `2π` (`wheel_sum`), while
`5 α(d) < 2π`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Geom

/-- Gram identity for the triple product. -/
theorem triple_sq (a b c : E3) :
    ⟪cross a b, c⟫ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 * ‖c‖ ^ 2 + 2 * ⟪a, b⟫ * ⟪b, c⟫ * ⟪a, c⟫ -
      ‖a‖ ^ 2 * ⟪b, c⟫ ^ 2 - ‖b‖ ^ 2 * ⟪a, c⟫ ^ 2 - ‖c‖ ^ 2 * ⟪a, b⟫ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_coords, cross_coords]; simp; ring

theorem norm_cross_unit (a b : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖cross a b‖ = sin (sdist a b) := by
  have hsq : ‖cross a b‖ ^ 2 = 1 - ⟪a, b⟫ ^ 2 := by
    rw [norm_cross_sq a b, ha, hb]
    norm_num
  have h_nonneg : 0 ≤ ‖cross a b‖ := norm_nonneg _
  calc
    ‖cross a b‖ = Real.sqrt (‖cross a b‖ ^ 2) := by
      rw [Real.sqrt_sq h_nonneg]
    _ = Real.sqrt (1 - ⟪a, b⟫ ^ 2) := by rw [hsq]
    _ = Real.sin (Real.arccos ⟪a, b⟫) := by rw [Real.sin_arccos]
    _ = sin (sdist a b) := rfl

/-- Decomposition in the basis `a, b, cross a b`. -/
theorem smul_decomp (a b p : E3) :
    ‖cross a b‖ ^ 2 • p = ⟪cross p b, cross a b⟫ • a + ⟪cross a p, cross a b⟫ • b +
      ⟪p, cross a b⟫ • cross a b := by
  rw [← real_inner_self_eq_norm_sq]
  ext i
  simp only [inner_coords, cross_coords]
  fin_cases i <;> simp <;> ring

theorem cos_hrad (d : ℝ) (hd : 0 < d ∧ d < π / 2) : cos (hrad d) = cos d / cos (d / 2) := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  have hd_cos_pos : 0 < cos d := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, hd_lt⟩
  have hd2_cos_pos : 0 < cos (d / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    have hpi_pos : 0 < π := by exact Real.pi_pos
    constructor
    · linarith
    · linarith
  have h_nonneg : -1 ≤ cos d / cos (d / 2) := by
    have hpos : 0 < cos d / cos (d / 2) := div_pos hd_cos_pos hd2_cos_pos
    linarith
  have h_le_one : cos d / cos (d / 2) ≤ 1 := by
    apply (div_le_one hd2_cos_pos).mpr
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  unfold hrad
  rw [Real.cos_arccos h_nonneg h_le_one]

theorem sin_mul_sin_hrad_sq (d : ℝ) (hd : 0 < d ∧ d < π / 2) :
    (sin d * sin (hrad d)) ^ 2 = 1 - cos d ^ 2 - 2 * cos d ^ 2 * (1 - cos d) := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hmem_d : d ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> nlinarith
  have hmem_dhalf : d / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> nlinarith
  have hcos_d_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo hmem_d
  have hcos_half_pos : 0 < cos (d / 2) := Real.cos_pos_of_mem_Ioo hmem_dhalf
  have hcos_half_ne_zero : cos (d / 2) ≠ 0 := by linarith
  have hone_plus_cos_ne_zero : 1 + cos d ≠ 0 := by linarith
  have hcos_sq_half : cos (d / 2) ^ 2 = (1 + cos d) / 2 := by
    rw [Real.cos_sq (d / 2)]
    have h : 2 * (d / 2) = d := by ring
    rw [h]
    ring
  have hcos_hrad : cos (hrad d) = cos d / cos (d / 2) := cos_hrad d ⟨hdpos, hdlt⟩
  calc
    (sin d * sin (hrad d)) ^ 2 = sin d ^ 2 * sin (hrad d) ^ 2 := by ring
    _ = (1 - cos d ^ 2) * sin (hrad d) ^ 2 := by rw [Real.sin_sq]
    _ = (1 - cos d ^ 2) * (1 - cos (hrad d) ^ 2) := by rw [Real.sin_sq]
    _ = (1 - cos d ^ 2) * (1 - (cos d / cos (d / 2)) ^ 2) := by rw [hcos_hrad]
    _ = (1 - cos d ^ 2) * (1 - cos d ^ 2 / cos (d / 2) ^ 2) := by ring
    _ = (1 - cos d ^ 2) * ((cos (d / 2) ^ 2 - cos d ^ 2) / cos (d / 2) ^ 2) := by
      field_simp [hcos_half_ne_zero]
    _ = (1 - cos d ^ 2) * (((1 + cos d) / 2 - cos d ^ 2) / ((1 + cos d) / 2)) := by rw [hcos_sq_half]
    _ = (1 - cos d ^ 2) * (1 - 2 * cos d ^ 2 / (1 + cos d)) := by
      field_simp [hone_plus_cos_ne_zero]
    _ = 1 - cos d ^ 2 - 2 * cos d ^ 2 * (1 - cos d) := by
      field_simp [hone_plus_cos_ne_zero]
      ring

/-- A nonnegative combination of the ends of an arc of length `d`, seen from a point at distance
at least `d` from both ends. -/
theorem edge_comb_bound (d : ℝ) (hd : 0 < d ∧ d < π / 2) (a b r : E3) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ = cos d) (l μ : ℝ) (hl : 0 ≤ l) (hμ : 0 ≤ μ)
    (hra : ⟪r, a⟫ ≤ cos d) (hrb : ⟪r, b⟫ ≤ cos d) :
    ⟪r, l • a + μ • b⟫ * cos (d / 2) ≤ cos d * ‖l • a + μ • b‖ := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hcosd_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, hdlt⟩
  have hcos_half_pos : 0 < cos (d / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcosd_nonneg : 0 ≤ cos d := le_of_lt hcosd_pos
  have hcos_half_nonneg : 0 ≤ cos (d / 2) := le_of_lt hcos_half_pos
  have hcos_sq_half : cos (d / 2) ^ 2 = (1 + cos d) / 2 := by
    have h := Real.cos_sq (d / 2)
    rw [h]
    have hcos2 : cos (2 * (d / 2)) = cos d := by ring
    rw [hcos2]
    ring
  have hinner : ⟪r, l • a + μ • b⟫ = l * ⟪r, a⟫ + μ * ⟪r, b⟫ := by
    simp [inner_add_right, real_inner_smul_right]
  have hinner_bound : ⟪r, l • a + μ • b⟫ ≤ (l + μ) * cos d := by
    rw [hinner]
    have h1 : l * ⟪r, a⟫ ≤ l * cos d := mul_le_mul_of_nonneg_left hra hl
    have h2 : μ * ⟪r, b⟫ ≤ μ * cos d := mul_le_mul_of_nonneg_left hrb hμ
    linarith
  have hnorm_sq : ‖l • a + μ • b‖ ^ 2 = l ^ 2 + μ ^ 2 + 2 * l * μ * cos d := by
    rw [norm_add_sq_real]
    simp [norm_smul, real_inner_smul_right, real_inner_smul_left, ha, hb, hab, abs_of_nonneg hl,
      abs_of_nonneg hμ]
    ring
  have hnorm_sq_lower : ((l + μ) * cos (d / 2)) ^ 2 ≤ ‖l • a + μ • b‖ ^ 2 := by
    rw [hnorm_sq]
    calc
      ((l + μ) * cos (d / 2)) ^ 2 = (l + μ) ^ 2 * cos (d / 2) ^ 2 := by ring
      _ = (l + μ) ^ 2 * ((1 + cos d) / 2) := by rw [hcos_sq_half]
      _ = (l ^ 2 + μ ^ 2 + 2 * l * μ) * (1 + cos d) / 2 := by ring
      _ ≤ l ^ 2 + μ ^ 2 + 2 * l * μ * cos d := by
        have h_nonneg_sq : 0 ≤ (l - μ) ^ 2 := by positivity
        have h_cosd_le_one : cos d ≤ 1 := cos_le_one d
        nlinarith
  have hnorm_bound : (l + μ) * cos (d / 2) ≤ ‖l • a + μ • b‖ := by
    have h_sq_le : ((l + μ) * cos (d / 2)) ^ 2 ≤ (‖l • a + μ • b‖) ^ 2 := by
      simpa [sq] using hnorm_sq_lower
    have h := Real.le_sqrt_of_sq_le h_sq_le
    rw [Real.sqrt_sq (norm_nonneg _)] at h
    exact h
  calc
    ⟪r, l • a + μ • b⟫ * cos (d / 2) ≤ ((l + μ) * cos d) * cos (d / 2) := by
      nlinarith [hcos_half_nonneg, hinner_bound]
    _ = (l + μ) * cos d * cos (d / 2) := by ring
    _ = cos d * ((l + μ) * cos (d / 2)) := by ring
    _ ≤ cos d * ‖l • a + μ • b‖ := by
      nlinarith

/-- Lemma A.10, distance form. -/
theorem disc_side (d : ℝ) (hd : 0 < d ∧ d < π / 2) {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A)
    (hside : ∀ i, sdist (A i) (A (i + 1)) = d) (r : E3) (hr : ‖r‖ = 1) (hin : Inside A r)
    (hfar : ∀ i, d ≤ sdist r (A i)) (i : ℕ) :
    sin d * sin (hrad d) ≤ ⟪cross (A i) (A (i + 1)), r⟫ := by
  have hm3 := hA.three
  have hsd : 0 < sin d := sin_pos_of_pos_of_lt_pi hd.1 (by linarith [pi_pos])
  have hcd : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hd.2⟩
  have hc2 : 0 < cos (d / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hnorm : ∀ k, ‖cross (A k) (A (k + 1))‖ = sin d := fun k => by
    rw [norm_cross_unit _ _ (hA.unit k) (hA.unit (k + 1)), hside k]
  have hab : ∀ k, ⟪A k, A (k + 1)⟫ = cos d := fun k => by
    rw [← cos_sdist _ _ (hA.unit k) (hA.unit _), hside k]
  have hra : ∀ k, ⟪r, A k⟫ ≤ cos d := fun k => by
    rw [← cos_sdist r (A k) hr (hA.unit k)]
    exact cos_le_cos_of_nonneg_of_le_pi hd.1.le (sdist_mem_Icc _ _).2 (hfar k)
  -- the side minimising `⟪cross (A k) (A (k + 1)), r⟫`
  have hne : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨i0, -, hmin⟩ :=
    Finset.exists_min_image (Finset.range m) (fun k => ⟪cross (A k) (A (k + 1)), r⟫) hne
  have hge : ∀ k, ⟪cross (A i0) (A (i0 + 1)), r⟫ ≤ ⟪cross (A k) (A (k + 1)), r⟫ := by
    intro k
    have hk := hmin (k % m) (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
    have e1 : A k = A (k % m) := hA.mod k
    have e2 : A (k + 1) = A (k % m + 1) := by
      rw [hA.mod (k + 1), hA.mod (k % m + 1)]
      congr 1
      simp [Nat.add_mod]
    rw [e1, e2]
    exact hk
  refine le_trans ?_ (hge i)
  set a := A i0 with ha_def
  set b := A (i0 + 1) with hb_def
  set N := cross a b with hN_def
  set s := ⟪N, r⟫ with hs_def
  have hs0 : 0 < s := hin i0
  have hN2 : ‖N‖ ^ 2 = sin d ^ 2 := by rw [hN_def, hnorm i0]
  have hsd2 : sin d ^ 2 ≠ 0 := by positivity
  set t := s / sin d ^ 2 with ht_def
  have ht0 : 0 ≤ t := div_nonneg hs0.le (sq_nonneg _)
  have hts : t * sin d ^ 2 = s := by rw [ht_def]; field_simp
  set p := r - t • N with hp_def
  have hNp : ⟪p, N⟫ = 0 := by
    rw [hp_def, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hN2,
      real_inner_comm, ← hs_def, hts, sub_self]
  -- `p` lies in the closed face
  have hpc : ∀ k, 0 ≤ ⟪cross (A k) (A (k + 1)), p⟫ := by
    intro k
    have hcs : ⟪cross (A k) (A (k + 1)), N⟫ ≤ sin d ^ 2 := by
      calc _ ≤ ‖cross (A k) (A (k + 1))‖ * ‖N‖ := real_inner_le_norm _ _
        _ = sin d ^ 2 := by rw [hnorm, hN_def, hnorm]; ring
    have hexp : ⟪cross (A k) (A (k + 1)), p⟫ =
        ⟪cross (A k) (A (k + 1)), r⟫ - t * ⟪cross (A k) (A (k + 1)), N⟫ := by
      rw [hp_def, inner_sub_right, real_inner_smul_right]
    rw [hexp]
    have := mul_le_mul_of_nonneg_left hcs ht0
    linarith [hge k]
  -- `p = l a + μ b`
  have hdec := smul_decomp a b p
  rw [← hN_def, hNp, zero_smul, add_zero, hN2] at hdec
  set l := ⟪cross p b, N⟫ / sin d ^ 2 with hl_def
  set μ := ⟪cross a p, N⟫ / sin d ^ 2 with hμ_def
  have hp : p = l • a + μ • b := by
    have : p = (sin d ^ 2)⁻¹ • (sin d ^ 2 • p) := by rw [smul_smul, inv_mul_cancel₀ hsd2, one_smul]
    rw [this, hdec, smul_add, smul_smul, smul_smul, hl_def, hμ_def, div_eq_inv_mul, div_eq_inv_mul]
  have hl : 0 ≤ l := by
    have h1 := hpc (i0 + 1)
    have hpos : 0 < ⟪cross (A (i0 + 1)) (A (i0 + 1 + 1)), a⟫ := by
      rw [← triple_cycle]
      simpa [add_assoc] using hA.support i0 2 le_rfl (by omega)
    have hbb : ⟪cross (A (i0 + 1)) (A (i0 + 1 + 1)), b⟫ = 0 := by
      rw [hb_def, real_inner_comm]; exact inner_cross_self _ _
    rw [hp, inner_add_right, real_inner_smul_right, real_inner_smul_right, hbb, mul_zero,
      add_zero] at h1
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hpos]
  have hμ : 0 ≤ μ := by
    have h1 := hpc (i0 + (m - 1))
    have hidx : i0 + (m - 1) + 1 = i0 + m := by omega
    rw [hidx, hA.periodic i0, ← ha_def] at h1
    have hpos : 0 < ⟪cross (A (i0 + (m - 1))) a, b⟫ := by
      rw [triple_cycle]
      exact hA.support i0 (m - 1) (by omega) (by omega)
    have haa : ⟪cross (A (i0 + (m - 1))) a, a⟫ = 0 := inner_cross_right_zero _ _
    rw [hp, inner_add_right, real_inner_smul_right, real_inner_smul_right, haa, mul_zero,
      zero_add] at h1
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hpos]
  -- the bound: `‖p‖² = ⟪r, p⟫ = 1 - s²/sin² d` and `⟪r, p⟫ cos (d/2) ≤ cos d ‖p‖`
  have hecb := edge_comb_bound d hd a b r (hA.unit i0) (hA.unit (i0 + 1)) (hab i0) l μ hl hμ
    (hra i0) (hra (i0 + 1))
  rw [← hp] at hecb
  have hrr : ⟪r, r⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hr]; norm_num
  have hrp : ⟪r, p⟫ = 1 - t * s := by
    rw [hp_def, inner_sub_right, real_inner_smul_right, hrr, real_inner_comm, ← hs_def]
  have hpp : ‖p‖ ^ 2 = 1 - t * s := by
    rw [← real_inner_self_eq_norm_sq, hp_def, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      hrr, real_inner_self_eq_norm_sq N, hN2, real_inner_comm N r, ← hs_def]
    nlinarith [hts]
  set P := ‖p‖ with hP_def
  have hP0 : 0 ≤ P := norm_nonneg _
  rw [hrp, ← hpp] at hecb
  -- `P ≤ cos (hrad d)` in every case
  have hch : cos (hrad d) = cos d / cos (d / 2) := cos_hrad d hd
  have hPh : P ^ 2 ≤ cos (hrad d) ^ 2 := by
    rcases hP0.eq_or_lt with h0 | hpos
    · rw [← h0]; nlinarith [sq_nonneg (cos (hrad d))]
    · have h1 : P * cos (d / 2) ≤ cos d := by nlinarith
      have h2 : P ≤ cos (hrad d) := by rw [hch, le_div_iff₀ hc2]; exact h1
      exact pow_le_pow_left₀ hP0 h2 2
  have hsin : sin (hrad d) ^ 2 = 1 - cos (hrad d) ^ 2 := sin_sq _
  have hsh0 : 0 ≤ sin (hrad d) :=
    sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg _) (arccos_le_pi _)
  -- `s² = sin² d (1 - P²) ≥ sin² d sin² (hrad d)`
  have hs2 : s ^ 2 = sin d ^ 2 * (1 - P ^ 2) := by
    rw [hpp]
    have : s = t * sin d ^ 2 := hts.symm
    rw [this]; ring
  have hsq : (sin d * sin (hrad d)) ^ 2 ≤ s ^ 2 := by
    rw [hs2, mul_pow, hsin]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  exact le_of_pow_le_pow_left₀ two_ne_zero hs0.le hsq

/-- Lemma A.10: the disc `D(r, h(d))` lies in the closed face. -/
theorem disc_closed (d : ℝ) (hd : 0 < d ∧ d < π / 2) {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A)
    (hside : ∀ i, sdist (A i) (A (i + 1)) = d) (r : E3) (hr : ‖r‖ = 1) (hin : Inside A r)
    (hfar : ∀ i, d ≤ sdist r (A i)) (y : E3) (hy : ‖y‖ = 1) (hry : sdist r y ≤ hrad d) :
    InClosed A y := by
  intro i
  have hsd : 0 < sin d := sin_pos_of_pos_of_lt_pi hd.1 (by linarith [pi_pos])
  have hn : ‖cross (A i) (A (i + 1))‖ = sin d := by
    rw [norm_cross_unit _ _ (hA.unit i) (hA.unit (i + 1)), hside i]
  set n := (sin d)⁻¹ • cross (A i) (A (i + 1)) with hn_def
  have hn1 : ‖n‖ = 1 := by
    rw [hn_def, norm_smul, hn, norm_inv, Real.norm_of_nonneg hsd.le, inv_mul_cancel₀ hsd.ne']
  have hrn : sin (hrad d) ≤ ⟪r, n⟫ := by
    have h := disc_side d hd hA hside r hr hin hfar i
    rw [hn_def, real_inner_smul_right, real_inner_comm, le_inv_mul_iff₀ hsd]
    exact h
  have hb := hrad_bounds d hd
  have h := cap_in_hemisphere (hrad d) ⟨by linarith, by linarith⟩ r n y hr hn1 hy hrn hry
  rw [hn_def, real_inner_smul_right] at h
  rw [real_inner_comm]
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hsd)).mp h

/-- The algebra of `subtend_le_alpha`, with `u = ⟪r, a⟫`, `v = ⟪r, b⟫`, `c = cos d` and the
Gram determinant bounded below by the disc inequality: `uv ≤ c²`, then
`(1 - u²)(1 - v²) ≤ (1 - uv)²` and `(c - uv)/(1 - uv) ≥ c/(1 + c)`. -/
theorem subtend_alg (c u v : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hG : 1 - c ^ 2 - 2 * c ^ 2 * (1 - c) ≤ 1 + 2 * c * v * u - v ^ 2 - u ^ 2 - c ^ 2) :
    0 < (1 - u ^ 2) * (1 - v ^ 2) ∧
      c / (1 + c) ≤ (c - u * v) / √((1 - u ^ 2) * (1 - v ^ 2)) := by
  have hs : u * v ≤ c ^ 2 := by
    by_contra h
    rw [not_le] at h
    have : 0 < (u * v - c ^ 2) * (2 * (1 - c)) := mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg (u - v)]
  have hGid : 1 + 2 * c * v * u - v ^ 2 - u ^ 2 - c ^ 2 =
      (1 - u ^ 2) * (1 - v ^ 2) - (c - u * v) ^ 2 := by ring
  have hK : 0 < 1 - c ^ 2 - 2 * c ^ 2 * (1 - c) := by
    have : 1 - c ^ 2 - 2 * c ^ 2 * (1 - c) = (1 - c) ^ 2 * (1 + 2 * c) := by ring
    rw [this]; exact mul_pos (pow_pos (by linarith) 2) (by linarith)
  have hD : 0 < (1 - u ^ 2) * (1 - v ^ 2) := by nlinarith [sq_nonneg (c - u * v)]
  refine ⟨hD, ?_⟩
  have hs1 : 0 < 1 - u * v := by nlinarith
  have hsq : √((1 - u ^ 2) * (1 - v ^ 2)) ≤ 1 - u * v :=
    Real.sqrt_le_iff.mpr ⟨hs1.le, by nlinarith [sq_nonneg (u - v)]⟩
  have hcs : 0 ≤ c - u * v := by nlinarith
  calc c / (1 + c) ≤ (c - u * v) / (1 - u * v) := by
        rw [div_le_div_iff₀ (by linarith) hs1]; nlinarith
    _ ≤ (c - u * v) / √((1 - u ^ 2) * (1 - v ^ 2)) :=
        div_le_div_of_nonneg_left hcs (Real.sqrt_pos.mpr hD) hsq

/-- A side whose great circle is at distance at least `h(d)` from `r` subtends at most `α(d)`. -/
theorem subtend_le_alpha (d : ℝ) (hd : 0 < d ∧ d < π / 2) (a b r : E3) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hr : ‖r‖ = 1) (hab : sdist a b = d)
    (hdisc : sin d * sin (hrad d) ≤ ⟪cross a b, r⟫) :
    angle (tdir r a) (tdir r b) ≤ alpha d := by
  have hc0 : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hd.2⟩
  have hc1 : cos d < 1 := by
    have := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [pi_pos]) hd.1
    rwa [cos_zero] at this
  have hab' : ⟪a, b⟫ = cos d := by rw [← hab, cos_sdist a b ha hb]
  have hsh : 0 ≤ sin (hrad d) := sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg _) (arccos_le_pi _)
  have hsd : 0 ≤ sin d := sin_nonneg_of_nonneg_of_le_pi hd.1.le (by linarith [pi_pos])
  have hsq := pow_le_pow_left₀ (mul_nonneg hsd hsh) hdisc 2
  rw [sin_mul_sin_hrad_sq d hd, triple_sq, ha, hb, hr, hab', real_inner_comm r b,
    real_inner_comm r a] at hsq
  simp only [one_pow, one_mul, mul_one] at hsq
  obtain ⟨hD, hineq⟩ := subtend_alg (cos d) ⟪r, a⟫ ⟪r, b⟫ hc0 hc1 hsq
  have hta : ‖tdir r a‖ ^ 2 = 1 - ⟪r, a⟫ ^ 2 := by rw [norm_tdir_sq r a hr, ha, one_pow]
  have htb : ‖tdir r b‖ ^ 2 = 1 - ⟪r, b⟫ ^ 2 := by rw [norm_tdir_sq r b hr, hb, one_pow]
  have hnorm : ‖tdir r a‖ * ‖tdir r b‖ = √((1 - ⟪r, a⟫ ^ 2) * (1 - ⟪r, b⟫ ^ 2)) := by
    rw [← hta, ← htb, ← mul_pow, Real.sqrt_sq (by positivity)]
  unfold angle alpha
  rw [inner_tdir r a b hr, hab', hnorm]
  exact arccos_le_arccos hineq

/-- No face with at most five vertices holds a point at distance at least `h(d)` from all its
sides. -/
theorem no_small_face (d : ℝ) (hd : 0 < d ∧ d < π / 2) (hα : alpha d < 2 * π / 5) {m : ℕ}
    {A : ℕ → E3} (hA : IsCPoly m A) (hm : m ≤ 5) (hside : ∀ i, sdist (A i) (A (i + 1)) = d)
    (r : E3) (hr : ‖r‖ = 1) (hin : Inside A r)
    (hdisc : ∀ i, sin d * sin (hrad d) ≤ ⟪cross (A i) (A (i + 1)), r⟫) : False := by
  have hw := wheel_sum hA r hr hin
  have hle : ∑ i ∈ Finset.range m, angle (tdir r (A i)) (tdir r (A (i + 1))) ≤
      ∑ _i ∈ Finset.range m, alpha d :=
    Finset.sum_le_sum fun i _ =>
      subtend_le_alpha d hd _ _ r (hA.unit i) (hA.unit (i + 1)) hr (hside i) (hdisc i)
  rw [hw, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  have ha0 : 0 ≤ alpha d := arccos_nonneg _
  have hm' : (m : ℝ) ≤ 5 := by exact_mod_cast hm
  nlinarith [pi_pos]

/-- Proposition 4.5, in cone form. -/
theorem nor (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A)
    (hm : m ≤ 5) (hside : ∀ i, sdist (A i) (A (i + 1)) = d) (r : E3) (hr : ‖r‖ = 1)
    (hin : Inside A r) (hfar : ∀ i, d ≤ sdist r (A i)) : False := by
  have h1 := pi_div_four_lt_dlo
  have h2 := dhi_lt_pi_div_three
  have hd : 0 < d ∧ d < π / 2 := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hα : alpha d < 2 * π / 5 := by
    have hmono : alpha d ≤ alpha dhi := alpha_strictMonoOn.monotoneOn ⟨hd.1, hd.2⟩
      ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ hhi
    exact lt_of_le_of_lt hmono alpha_dhi_lt
  exact no_small_face d hd hα hA hm hside r hr hin (disc_side d hd hA hside r hr hin hfar)

end Tammes15.Geom
