import Tammes15.Geom.Face
import Tammes15.TwoConn.Farm

/-!
# A point far from the drawing lies strictly inside a face

`exists_face_inside`: for a drawing of a graph with edges of length `d`, an angular rotation
system with corners in `(0, π)` and faces in cone form (`StrictSupportFace`, faces of at least
three darts), every unit point at distance more than `d` from all vertices lies strictly on the
inner side of every side of some face.

Route (nearest point of the drawing, paper Section 3). The drawn edge of a dart `a → b` is the cone
`{l • a + μ • b | 0 ≤ l, 0 ≤ μ}`; some unit point `z` of the drawing maximises `⟪y, ·⟫ / ‖·‖`
(`cover_exists_cone_max`, compactness of the chords). `z` is not a vertex: at a vertex `v`,
`exists_pos_of_corner_lt_pi` gives a neighbour `w` on the positive side of the tangent direction of
`y`, and a short step along the chord to `w` gains (`cover_chord_gain`, `cover_vertex_not_max`).
So `z` lies inside the drawn edge of a dart `a → b`; the first order conditions
(`cover_first_order`) put `y - ⟪y, z⟫ z` along `cross a b`, nonzero since `y` is on no drawn edge
(`cover_arc_inner_ge`). Orient the dart so that `y` is on the positive side and take its face. If
some side of the face had `y` on its nonpositive side, the chord from `z` to `y` would leave the
closed face (`cover_first_exit`) at a point of a side (`IsCPoly.comb_of_side`), a point of the
drawing strictly nearer to `y` than `z` (`cover_geodesic_gain`, `cover_face_of_interior`).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Geom

/-! ## Self-contained steps -/

theorem cover_inner_eq_cos (a b : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (d : ℝ)
    (h : sdist a b = d) : ⟪a, b⟫ = cos d := by
  dsimp [sdist] at h
  rw [← h]
  have h_abs := abs_real_inner_le_norm a b
  have h_norm : ‖a‖ * ‖b‖ = 1 := by rw [ha, hb]; norm_num
  have h_abs' : |⟪a, b⟫| ≤ 1 := by linarith
  have h_bound := abs_le.mp h_abs'
  exact (Real.cos_arccos h_bound.1 h_bound.2).symm

theorem cover_inner_lt_cos (a b : E3) (d : ℝ) (hd0 : 0 ≤ d) (hdπ : d ≤ π) (h : d < sdist a b) :
    ⟪a, b⟫ < cos d := by
  by_contra! hle
  -- hle : cos d ≤ ⟪a, b⟫
  have hle_arccos : Real.arccos ⟪a, b⟫ ≤ Real.arccos (cos d) :=
    Real.arccos_le_arccos hle
  have harccos_cos_d : Real.arccos (cos d) = d :=
    Real.arccos_cos hd0 hdπ
  have hle_d : Real.arccos ⟪a, b⟫ ≤ d := by
    calc
      Real.arccos ⟪a, b⟫ ≤ Real.arccos (cos d) := hle_arccos
      _ = d := harccos_cos_d
  dsimp [sdist] at h
  linarith

/-- A short step along the chord from `a` towards `b` increases `⟪y, ·⟫ / ‖·‖` when `y` has a
positive component along the tangent direction of `b` at `a`. -/
theorem cover_chord_gain (a b y : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : 0 < ⟪a, b⟫)
    (hq : 0 < ⟪y, b⟫ - ⟪y, a⟫ * ⟪a, b⟫) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ⟪y, a⟫ * ‖(1 - t) • a + t • b‖ < ⟪y, (1 - t) • a + t • b⟫ := by
  set c := ⟪y, a⟫ with hc
  set k := ⟪a, b⟫ with hk
  set q := ⟪y, b⟫ - c * k with hqdef
  have hk1 : k ≤ 1 := by
    have := real_inner_le_norm a b
    rw [ha, hb, mul_one] at this
    exact this
  have hinner : ∀ t : ℝ, ⟪y, (1 - t) • a + t • b⟫ = c * (1 - t + t * k) + t * q := by
    intro t
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hqdef, ← hc]
    ring
  have hnorm : ∀ t : ℝ, ‖(1 - t) • a + t • b‖ ^ 2 = (1 - t + t * k) ^ 2 + t ^ 2 * (1 - k ^ 2) := by
    intro t
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ha, hb,
      real_inner_comm a b, ← hk]
    ring
  rcases le_or_gt c 0 with hc0 | hc0
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    rw [hinner]
    simp only [sub_self, zero_smul, zero_add, one_smul, hb, mul_one, one_mul]
    nlinarith
  · set t := min 1 (k * q / c) with ht
    have ht0 : 0 < t := lt_min one_pos (div_pos (mul_pos hab hq) hc0)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htc : c * t ≤ k * q := by
      have h := min_le_right 1 (k * q / c)
      rw [← ht] at h
      rw [le_div_iff₀ hc0] at h
      linarith
    refine ⟨t, ht0, ht1, ?_⟩
    set α := 1 - t + t * k with hα
    have hαk : k ≤ α := by nlinarith
    have hpos : 0 < c * α + t * q := by
      have : 0 < c * α := mul_pos hc0 (lt_of_lt_of_le hab hαk)
      nlinarith [mul_pos ht0 hq]
    rw [hinner]
    have hsq : (c * ‖(1 - t) • a + t • b‖) ^ 2 < (c * α + t * q) ^ 2 := by
      rw [mul_pow, hnorm]
      have hk2 : 0 ≤ 1 - k ^ 2 := by nlinarith
      have h1 : c * t * (1 - k ^ 2) ≤ c * t := by
        have : 0 ≤ c * t := (mul_pos hc0 ht0).le
        nlinarith
      have h2 : c * (c * t * (1 - k ^ 2)) < 2 * c * α * q := by
        have h3 : c * (c * t * (1 - k ^ 2)) ≤ c * (k * q) := by
          apply mul_le_mul_of_nonneg_left _ hc0.le
          linarith
        have h4 : c * (k * q) < 2 * c * α * q := by
          have : 0 < c * q := mul_pos hc0 hq
          nlinarith
        linarith
      nlinarith [mul_pos ht0 ht0, mul_pos ht0 hq, sq_nonneg (t * q)]
    exact lt_of_pow_lt_pow_left₀ 2 hpos.le hsq

/-- A unit point of the drawn edge `a b` is as near to one of its ends as the two ends are to each
other. -/
theorem cover_arc_inner_ge (a b : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (l μ : ℝ) (hl : 0 ≤ l)
    (hμ : 0 ≤ μ) (hp : ‖l • a + μ • b‖ = 1) :
    ⟪a, b⟫ ≤ ⟪l • a + μ • b, a⟫ ∨ ⟪a, b⟫ ≤ ⟪l • a + μ • b, b⟫ := by
  set p := l • a + μ • b with hp_def
  set k := ⟪a, b⟫ with hk_def
  have hk_sq_le_one : k ^ 2 ≤ 1 := by
    have h_abs : |k| ≤ 1 := by
      calc
        |k| = |⟪a, b⟫| := rfl
        _ ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
        _ = 1 * 1 := by simp [ha, hb]
        _ = 1 := by simp
    have h := abs_le.mp h_abs
    nlinarith
  have hk_le_one : k ≤ 1 := by nlinarith
  have h_sum : ⟪p, a⟫ + ⟪p, b⟫ = (l + μ) * (1 + k) := by
    calc
      ⟪p, a⟫ + ⟪p, b⟫ = ⟪l • a + μ • b, a⟫ + ⟪l • a + μ • b, b⟫ := rfl
      _ = (⟪l • a, a⟫ + ⟪μ • b, a⟫) + (⟪l • a, b⟫ + ⟪μ • b, b⟫) := by simp [inner_add_left]
      _ = (l * ⟪a, a⟫ + μ * ⟪b, a⟫) + (l * ⟪a, b⟫ + μ * ⟪b, b⟫) := by simp [real_inner_smul_left]
      _ = (l * ‖a‖^2 + μ * k) + (l * k + μ * ‖b‖^2) := by
        simp [hk_def, real_inner_comm a b]
      _ = (l * 1 + μ * k) + (l * k + μ * 1) := by simp [ha, hb]
      _ = (l + μ) * (1 + k) := by ring
  have h_norm_sq : ‖p‖^2 = 1 := by rw [hp, one_pow]
  have h_norm_sq_expand : ‖p‖^2 = l^2 + μ^2 + 2 * l * μ * k := by
    calc
      ‖p‖^2 = ‖l • a + μ • b‖^2 := rfl
      _ = ⟪l • a + μ • b, l • a + μ • b⟫ := by rw [real_inner_self_eq_norm_sq]
      _ = ⟪l • a, l • a + μ • b⟫ + ⟪μ • b, l • a + μ • b⟫ := by rw [inner_add_left]
      _ = (⟪l • a, l • a⟫ + ⟪l • a, μ • b⟫) + (⟪μ • b, l • a⟫ + ⟪μ • b, μ • b⟫) := by
        rw [inner_add_right, inner_add_right]
      _ = (l * ⟪a, l • a⟫ + l * ⟪a, μ • b⟫) + (μ * ⟪b, l • a⟫ + μ * ⟪b, μ • b⟫) := by
        rw [real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
      _ = (l * (l * ⟪a, a⟫) + l * (μ * ⟪a, b⟫)) + (μ * (l * ⟪b, a⟫) + μ * (μ * ⟪b, b⟫)) := by
        rw [real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right]
      _ = (l^2 * ⟪a, a⟫ + (l * μ) * ⟪a, b⟫) + ((μ * l) * ⟪b, a⟫ + μ^2 * ⟪b, b⟫) := by ring
      _ = (l^2 * ‖a‖^2 + (l * μ) * k) + ((μ * l) * k + μ^2 * ‖b‖^2) := by
        rw [hk_def, real_inner_self_eq_norm_sq, real_inner_comm a b, real_inner_self_eq_norm_sq]
      _ = l^2 + μ^2 + 2 * l * μ * k := by
        simp [ha, hb]
        ring
  have h_lm_ge_one : 1 ≤ l + μ := by
    have h_sq_bound : l^2 + μ^2 + 2 * l * μ * k ≤ (l + μ)^2 := by
      have : 0 ≤ l * μ := mul_nonneg hl hμ
      nlinarith
    have h_one_le_sq : 1 ≤ (l + μ)^2 := by
      linarith
    have h_nonneg_sum : 0 ≤ l + μ := add_nonneg hl hμ
    nlinarith
  have h_sum_ge_one_plus_k : 1 + k ≤ ⟪p, a⟫ + ⟪p, b⟫ := by
    calc
      1 + k = 1 * (1 + k) := by simp
      _ ≤ (l + μ) * (1 + k) := by
        have : 0 ≤ 1 + k := by
          have : -1 ≤ k := by
            -- from k^2 ≤ 1 we get -1 ≤ k
            nlinarith
          nlinarith
        nlinarith
      _ = ⟪p, a⟫ + ⟪p, b⟫ := by rw [h_sum]
  have h_two_k_le_sum : 2 * k ≤ ⟪p, a⟫ + ⟪p, b⟫ := by
    nlinarith
  by_contra! h_not
  rcases h_not with ⟨h_lt_a, h_lt_b⟩
  -- h_lt_a : ⟪p, a⟫ < k,  h_lt_b : ⟪p, b⟫ < k
  have h_sum_lt_two_k : ⟪p, a⟫ + ⟪p, b⟫ < 2 * k := by nlinarith
  nlinarith

/-- First exit of a segment from a finite intersection of half spaces, in the parameters: `u i`,
`v i` are the values at the two ends of the `i`-th affine function. -/
theorem cover_first_exit {ι : Type} (S : Finset ι) (u v : ι → ℝ) (hu : ∀ i ∈ S, 0 ≤ u i)
    (huv : ∀ i ∈ S, u i = 0 → 0 < v i) (hex : ∃ j ∈ S, v j ≤ 0) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ (∀ i ∈ S, 0 ≤ (1 - s) * u i + s * v i) ∧
      ∃ j ∈ S, (1 - s) * u j + s * v j = 0 := by
  -- T = {i ∈ S | v i ≤ 0}, nonempty by hex
  set T := S.filter (fun i => v i ≤ 0) with hT
  have hT_nonempty : T.Nonempty := by
    rcases hex with ⟨j, hjS, hjv⟩
    refine ⟨j, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hjS, hjv⟩
  -- For i ∈ T, u i > 0 (else huv contradicts v i ≤ 0)
  have hu_pos : ∀ i ∈ T, 0 < u i := by
    intro i hi
    rcases Finset.mem_filter.1 hi with ⟨hiS, hiv⟩
    by_contra! hle
    have hueq0 : u i = 0 := by linarith [hu i hiS, hle]
    have hvpos : 0 < v i := huv i hiS hueq0
    linarith
  -- For i ∈ T, u i - v i > 0
  have h_denom_pos : ∀ i ∈ T, 0 < u i - v i := by
    intro i hi
    have hui_pos := hu_pos i hi
    have hvi_le0 : v i ≤ 0 := (Finset.mem_filter.1 hi).2
    linarith
  -- Take j ∈ T minimizing r i = u i / (u i - v i)
  obtain ⟨j, hjT, hjmin⟩ := Finset.exists_min_image T (fun i => u i / (u i - v i)) hT_nonempty
  have hjS : j ∈ S := (Finset.mem_filter.1 hjT).1
  have hjv : v j ≤ 0 := (Finset.mem_filter.1 hjT).2
  have huj_pos : 0 < u j := hu_pos j hjT
  set s := u j / (u j - v j) with hs_def
  have hs_pos : 0 < s := by
    rw [hs_def]
    exact div_pos (hu_pos j hjT) (h_denom_pos j hjT)
  have hs_le_one : s ≤ 1 := by
    rw [hs_def]
    have hnum_le_denom : u j ≤ u j - v j := by linarith
    exact ((div_le_one (h_denom_pos j hjT)).mpr hnum_le_denom)
  -- Nonnegativity for all i ∈ S
  have h_nonneg : ∀ i ∈ S, 0 ≤ (1 - s) * u i + s * v i := by
    intro i hiS
    by_cases hiT : i ∈ T
    · -- i ∈ T: s ≤ u i / (u i - v i) gives s * (u i - v i) ≤ u i
      have hineq : s ≤ u i / (u i - v i) := hjmin i hiT
      have h_mul : s * (u i - v i) ≤ u i := ((le_div_iff₀ (h_denom_pos i hiT)).mp hineq)
      have hcalc : (1 - s) * u i + s * v i = u i - s * (u i - v i) := by ring
      rw [hcalc]
      linarith
    · -- i ∉ T: v i > 0, u i ≥ 0, 0 < s ≤ 1
      have hvi_pos : 0 < v i := by
        by_contra! hle
        have hiT' : i ∈ T := by
          rw [Finset.mem_filter]
          exact ⟨hiS, hle⟩
        exact hiT hiT'
      have hui_nonneg : 0 ≤ u i := hu i hiS
      have hs_nonneg : 0 ≤ s := by linarith
      nlinarith
  -- At j, the expression equals 0
  have h_at_j : (1 - s) * u j + s * v j = 0 := by
    have hcalc : (1 - s) * u j + s * v j = u j - s * (u j - v j) := by ring
    rw [hcalc]
    rw [hs_def]
    field_simp [ne_of_gt (h_denom_pos j hjT)]
    ring
  exact ⟨s, hs_pos, hs_le_one, h_nonneg, j, hjS, h_at_j⟩

/-- A point of the closed polygon on the great circle of a side is a nonnegative combination of
the two ends of the side. -/
theorem IsCPoly.comb_of_side {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (p : E3) (hp : InClosed A p)
    (i : ℕ) (hi : ⟪cross (A i) (A (i + 1)), p⟫ = 0) :
    ∃ l μ : ℝ, 0 ≤ l ∧ 0 ≤ μ ∧ p = l • A i + μ • A (i + 1) := by
  have key : ∀ a b q : E3, ‖cross a b‖ ^ 2 • q = ⟪cross q b, cross a b⟫ • a +
      ⟪cross a q, cross a b⟫ • b + ⟪q, cross a b⟫ • cross a b := by
    intro a b q
    rw [← real_inner_self_eq_norm_sq]
    ext j
    simp only [inner_coords, cross_coords]
    fin_cases j <;> simp <;> ring
  have hm3 := hA.three
  have hc2 : 0 < ⟪cross (A i) (A (i + 1)), A (i + 2)⟫ := hA.support i 2 le_rfl (by omega)
  have hn0 : 0 < ‖cross (A i) (A (i + 1))‖ ^ 2 := by
    rcases (sq_nonneg ‖cross (A i) (A (i + 1))‖).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : cross (A i) (A (i + 1)) = 0 := by
        rw [← norm_eq_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h.symm
      rw [h0, inner_zero_left] at hc2
      exact lt_irrefl _ hc2
  set a := A i with ha
  set b := A (i + 1) with hb
  set n := cross a b with hn
  set N := ‖n‖ ^ 2 with hN
  have hpn : ⟪p, n⟫ = 0 := by rw [real_inner_comm]; exact hi
  have hpeq : p = (⟪cross p b, n⟫ / N) • a + (⟪cross a p, n⟫ / N) • b := by
    have hd := key a b p
    rw [← hn, ← hN, hpn, zero_smul, add_zero] at hd
    calc p = N⁻¹ • (N • p) := by rw [smul_smul, inv_mul_cancel₀ hn0.ne', one_smul]
      _ = _ := by rw [hd, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  set l := ⟪cross p b, n⟫ / N with hl
  set μ := ⟪cross a p, n⟫ / N with hμ
  refine ⟨l, μ, ?_, ?_, hpeq⟩
  · have h1 := hp (i + 1)
    have e2 : A (i + 1 + 1) = A (i + 2) := rfl
    rw [e2, ← hb, hpeq, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      triple_cycle b (A (i + 2)) b, inner_cross_right_zero, ← triple_cycle a b (A (i + 2))] at h1
    rw [mul_zero, add_zero] at h1
    exact (mul_nonneg_iff_of_pos_right hc2).mp h1
  · have hw : 0 < ⟪cross a b, A (i + (m - 1))⟫ := hA.support i (m - 1) (by omega) (by omega)
    have h2 := hp (i + (m - 1))
    have e1 : A (i + (m - 1) + 1) = a := by
      rw [ha, show i + (m - 1) + 1 = i + m by omega, hA.periodic i]
    rw [e1, hpeq, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_cross_right_zero, triple_cycle (A (i + (m - 1))) a b] at h2
    rw [mul_zero, zero_add] at h2
    exact (mul_nonneg_iff_of_pos_right hw).mp h2

/-- A point inside the side `A 0 A 1` is strictly on the inner side of every other side. -/
theorem IsCPoly.pos_of_open_side {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (l μ : ℝ) (hl : 0 < l)
    (hμ : 0 < μ) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j < m) :
    0 < ⟪cross (A j) (A (j + 1)), l • A 0 + μ • A 1⟫ := by
  have hinner : ⟪cross (A j) (A (j + 1)), l • A 0 + μ • A 1⟫ = l * ⟪cross (A j) (A (j + 1)), A 0⟫ + μ * ⟪cross (A j) (A (j + 1)), A 1⟫ := by
    simp [inner_add_right, inner_smul_right]
  rw [hinner]
  by_cases h : j + 1 < m
  · -- Case j + 1 < m
    by_cases hj1_eq : j = 1
    · -- Subcase j = 1
      subst hj1_eq
      have hpos0 : 0 < ⟪cross (A 1) (A 2), A 0⟫ := by
        apply hA.support_of_ne 1 0
        · rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < m)]; omega
        · rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 2 < m)]; omega
      have hzero1 : ⟪cross (A 1) (A 2), A 1⟫ = 0 := by
        calc
          ⟪cross (A 1) (A 2), A 1⟫ = ⟪cross (A 2) (A 1), A 1⟫ := by rw [triple_cycle]
          _ = 0 := inner_cross_right_zero (A 2) (A 1)
      nlinarith
    · -- Subcase j ≠ 1, so j ≥ 2
      have hj2 : 2 ≤ j := by omega
      have hpos0 : 0 < ⟪cross (A j) (A (j + 1)), A 0⟫ := by
        apply hA.support_of_ne j 0
        · rw [Nat.zero_mod, Nat.mod_eq_of_lt hjm]; omega
        · rw [Nat.zero_mod, Nat.mod_eq_of_lt h]; omega
      have hm_gt_1 : 1 < m := by omega
      have hpos1 : 0 < ⟪cross (A j) (A (j + 1)), A 1⟫ := by
        apply hA.support_of_ne j 1
        · rw [Nat.mod_eq_of_lt hjm, Nat.mod_eq_of_lt hm_gt_1]; omega
        · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hm_gt_1]; omega
      nlinarith
  · -- Case j + 1 ≥ m, but j < m, so j + 1 = m
    have heq : j + 1 = m := by omega
    have hm_pos : 0 < m := by omega
    have hA0 : A (j + 1) = A 0 := by
      calc
        A (j + 1) = A m := by rw [heq]
        _ = A (0 + m) := by simp
        _ = A 0 := hA.periodic 0
    have hzero0 : ⟪cross (A j) (A (j + 1)), A 0⟫ = 0 := by
      rw [hA0]
      exact inner_cross_right_zero (A j) (A 0)
    have hm3 : 3 ≤ m := hA.three
    have hj2 : 2 ≤ j := by omega
    have hm_gt_1 : 1 < m := by omega
    have hpos1 : 0 < ⟪cross (A j) (A (j + 1)), A 1⟫ := by
      apply hA.support_of_ne j 1
      · rw [Nat.mod_eq_of_lt hjm, Nat.mod_eq_of_lt hm_gt_1]; omega
      · rw [heq, Nat.mod_self _, Nat.mod_eq_of_lt hm_gt_1]; omega
    nlinarith

/-- Moving from `z` along the chord to `y` brings the direction nearer to `y`. -/
theorem cover_geodesic_gain (z y : E3) (hz : ‖z‖ = 1) (hy : ‖y‖ = 1) (h0 : 0 ≤ ⟪y, z⟫)
    (h1 : ⟪y, z⟫ < 1) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ⟪y, z⟫ * ‖(1 - s) • z + s • y‖ < ⟪y, (1 - s) • z + s • y⟫ := by
  set c := ⟪y, z⟫ with hc
  set p := (1 - s) • z + s • y with hp
  have hyy : ⟪y, y⟫ = 1 := by
    have := calc
      ⟪y, y⟫ = RCLike.re (⟪y, y⟫) := by simp
      _ = ‖y‖ ^ 2 := inner_self_eq_norm_sq y
      _ = 1 := by rw [hy]; norm_num
    exact this
  have hzz : ⟪z, z⟫ = 1 := by
    have := calc
      ⟪z, z⟫ = RCLike.re (⟪z, z⟫) := by simp
      _ = ‖z‖ ^ 2 := inner_self_eq_norm_sq z
      _ = 1 := by rw [hz]; norm_num
    exact this
  have hs_nonneg : 0 ≤ s := by linarith
  have h_one_minus_s_nonneg : 0 ≤ 1 - s := by linarith
  have h_one_minus_c_pos : 0 < 1 - c := by linarith
  have h_one_minus_c_nonneg : 0 ≤ 1 - c := by linarith
  -- compute ⟪y, p⟫
  have h_inner_yp : ⟪y, p⟫ = c + s * (1 - c) := by
    dsimp [p]
    calc
      ⟪y, (1 - s) • z + s • y⟫ = ⟪y, (1 - s) • z⟫ + ⟪y, s • y⟫ := by rw [inner_add_right]
      _ = (1 - s) * ⟪y, z⟫ + s * ⟪y, y⟫ := by rw [inner_smul_right, inner_smul_right]
      _ = (1 - s) * c + s * 1 := by rw [hc, hyy]
      _ = (1 - s) * c + s := by ring
      _ = c + s * (1 - c) := by ring
  -- compute ‖p‖²
  have h_norm_p_sq : ‖p‖ ^ 2 = 1 - 2 * s * (1 - s) * (1 - c) := by
    dsimp [p]
    have h_inner_p_p : ⟪(1 - s) • z + s • y, (1 - s) • z + s • y⟫ = 1 - 2 * s * (1 - s) * (1 - c) := by
      calc
        ⟪(1 - s) • z + s • y, (1 - s) • z + s • y⟫ =
            ⟪(1 - s) • z, (1 - s) • z⟫ + ⟪(1 - s) • z, s • y⟫ + ⟪s • y, (1 - s) • z⟫ + ⟪s • y, s • y⟫ := by
          rw [inner_add_add_self]
        _ = ((1 - s) * ((1 - s) * ⟪z, z⟫)) + ((1 - s) * (s * ⟪z, y⟫)) + (s * ((1 - s) * ⟪y, z⟫)) + (s * (s * ⟪y, y⟫)) := by
          rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
            inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
          simp
        _ = ((1 - s) ^ 2) * ⟪z, z⟫ + ((1 - s) * s) * ⟪z, y⟫ + (s * (1 - s)) * ⟪y, z⟫ + (s ^ 2) * ⟪y, y⟫ := by ring
        _ = ((1 - s) ^ 2) * 1 + ((1 - s) * s) * ⟪z, y⟫ + (s * (1 - s)) * ⟪y, z⟫ + (s ^ 2) * 1 := by rw [hzz, hyy]
        _ = ((1 - s) ^ 2) * 1 + ((1 - s) * s) * c + (s * (1 - s)) * c + (s ^ 2) * 1 := by
          rw [← real_inner_comm z y, hc]
        _ = 1 - 2 * s * (1 - s) * (1 - c) := by ring
    have h_norm_sq_eq : ‖(1 - s) • z + s • y‖ ^ 2 = RCLike.re (⟪(1 - s) • z + s • y, (1 - s) • z + s • y⟫) := by
      rw [inner_self_eq_norm_sq]
    -- For ℝ, RCLike.re is identity on real inner products
    have h_re_eq : RCLike.re (⟪(1 - s) • z + s • y, (1 - s) • z + s • y⟫) = ⟪(1 - s) • z + s • y, (1 - s) • z + s • y⟫ := by
      simp
    rw [h_norm_sq_eq, h_re_eq, h_inner_p_p]
  have h_norm_p_sq_le_one : ‖p‖ ^ 2 ≤ 1 := by
    rw [h_norm_p_sq]
    have : 0 ≤ 2 * s * (1 - s) * (1 - c) := by
      have h1 : 0 ≤ 2 := by norm_num
      have h2 : 0 ≤ s := hs_nonneg
      have h3 : 0 ≤ 1 - s := h_one_minus_s_nonneg
      have h4 : 0 ≤ 1 - c := h_one_minus_c_nonneg
      positivity
    nlinarith
  have h_norm_p_le_one : ‖p‖ ≤ 1 := by
    nlinarith
  have hc_mul_norm_p_le_c : c * ‖p‖ ≤ c := by
    nlinarith
  have hc_lt_inner_yp : c < ⟪y, p⟫ := by
    rw [h_inner_yp]
    have : 0 < s * (1 - c) := by nlinarith
    nlinarith
  calc
    ⟪y, z⟫ * ‖(1 - s) • z + s • y‖ = c * ‖p‖ := by rw [hc, hp]
    _ ≤ c := hc_mul_norm_p_le_c
    _ < ⟪y, p⟫ := hc_lt_inner_yp
    _ = ⟪y, (1 - s) • z + s • y⟫ := by rw [hp]

/-- Some unit point of finitely many drawn edges maximises `⟪y, ·⟫ / ‖·‖` over all of them. -/
theorem cover_exists_cone_max {ι : Type} [Finite ι] [Nonempty ι] (a b : ι → E3)
    (ha : ∀ i, ‖a i‖ = 1) (hb : ∀ i, ‖b i‖ = 1) (hab : ∀ i, 0 < ⟪a i, b i⟫) (y : E3) :
    ∃ i₀ : ι, ∃ l₀ μ₀ : ℝ, 0 ≤ l₀ ∧ 0 ≤ μ₀ ∧ ‖l₀ • a i₀ + μ₀ • b i₀‖ = 1 ∧
      ∀ i : ι, ∀ l μ : ℝ, 0 ≤ l → 0 ≤ μ →
        ⟪y, l • a i + μ • b i⟫ ≤ ⟪y, l₀ • a i₀ + μ₀ • b i₀⟫ * ‖l • a i + μ • b i‖ := by
  set P : ι → ℝ → E3 := fun i t => (1 - t) • a i + t • b i with hP
  have hPpos : ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 → 0 < ‖P i t‖ := by
    intro i t ht
    have hPa : ⟪a i, P i t⟫ = (1 - t) + t * ⟪a i, b i⟫ := by
      simp only [hP, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ha,
        one_pow, mul_one]
    have h1 : 0 < ⟪a i, P i t⟫ := by
      have hk1 : ⟪a i, b i⟫ ≤ 1 := by
        have := real_inner_le_norm (a i) (b i)
        rw [ha, hb, mul_one] at this
        exact this
      rw [hPa]; nlinarith [mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 hk1), hab i]
    have h2 := real_inner_le_norm (a i) (P i t)
    rw [ha, one_mul] at h2
    linarith
  set f : ι → ℝ → ℝ := fun i t => ⟪y, P i t⟫ / ‖P i t‖ with hf
  have hcont : ∀ i, ContinuousOn (f i) (Set.Icc 0 1) := by
    intro i
    have hPc : Continuous (P i) := by
      simp only [hP]; fun_prop
    apply ContinuousOn.div
    · exact (continuous_const.inner hPc).continuousOn
    · exact (continuous_norm.comp hPc).continuousOn
    · intro t ht; exact (hPpos i t ht).ne'
  have hmax_i : ∀ i, ∃ t ∈ Set.Icc (0 : ℝ) 1, IsMaxOn (f i) (Set.Icc 0 1) t := fun i =>
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one) (hcont i)
  choose T hT hTmax using hmax_i
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => f i (T i))
  set t₀ := T i₀ with ht₀
  set N := ‖P i₀ t₀‖ with hNdef
  have hN : 0 < N := hPpos i₀ t₀ (hT i₀)
  have hz : ((1 - t₀) / N) • a i₀ + (t₀ / N) • b i₀ = N⁻¹ • P i₀ t₀ := by
    simp only [hP, smul_add, smul_smul, div_eq_inv_mul]
  refine ⟨i₀, (1 - t₀) / N, t₀ / N, div_nonneg (by linarith [(hT i₀).2]) hN.le,
    div_nonneg (hT i₀).1 hN.le, ?_, ?_⟩
  · rw [hz, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hN, inv_mul_cancel₀ hN.ne']
  · intro i l μ hl hμ
    rw [hz, real_inner_smul_right]
    have hf0 : f i₀ t₀ = N⁻¹ * ⟪y, P i₀ t₀⟫ := by
      simp only [hf]; rw [div_eq_inv_mul]
    rw [← hf0]
    rcases (add_nonneg hl hμ).eq_or_lt with h0 | hpos
    · have hl0 : l = 0 := by linarith
      have hμ0 : μ = 0 := by linarith
      subst hl0 hμ0
      simp
    · set s := μ / (l + μ) with hs
      have hsI : s ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hμ hpos.le, div_le_one_of_le₀ (by linarith) hpos.le⟩
      have hlm : l • a i + μ • b i = (l + μ) • P i s := by
        simp only [hP, smul_add, smul_smul]
        have e1 : (l + μ) * (1 - s) = l := by rw [hs]; field_simp; ring
        have e2 : (l + μ) * s = μ := by rw [hs]; field_simp
        rw [e1, e2]
      have hfi : f i s ≤ f i₀ t₀ := le_trans (hTmax i hsI) (hi₀ i)
      have hPs := hPpos i s hsI
      have hle : ⟪y, P i s⟫ ≤ f i₀ t₀ * ‖P i s‖ := by
        have h := hfi
        simp only [hf] at h
        rw [div_le_iff₀ hPs] at h
        exact h
      rw [hlm, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
      nlinarith

theorem cover_inner_cross_sq (a b t : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hta : ⟪t, a⟫ = 0)
    (htb : ⟪t, b⟫ = 0) : ⟪cross a b, t⟫ ^ 2 = ‖t‖ ^ 2 * (1 - ⟪a, b⟫ ^ 2) := by
  have h : ⟪cross a b, t⟫ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 * ‖t‖ ^ 2 + 2 * ⟪a, b⟫ * ⟪b, t⟫ * ⟪a, t⟫ -
      ‖a‖ ^ 2 * ⟪b, t⟫ ^ 2 - ‖b‖ ^ 2 * ⟪a, t⟫ ^ 2 - ‖t‖ ^ 2 * ⟪a, b⟫ ^ 2 := by
    simp only [← real_inner_self_eq_norm_sq, inner_coords, cross_coords]; simp; ring
  rw [ha, hb] at h
  have hta' : ⟪a, t⟫ = 0 := by rw [real_inner_comm]; exact hta
  have htb' : ⟪b, t⟫ = 0 := by rw [real_inner_comm]; exact htb
  rw [hta', htb'] at h
  simp at h
  rw [h]
  ring

/-- First order conditions at a maximiser inside a drawn edge: `y - ⟪y, z⟫ z` is orthogonal to
both ends. -/
theorem cover_first_order (a b y : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : 0 < ⟪a, b⟫)
    (l μ : ℝ) (hl : 0 < l) (hμ : 0 < μ) (hz : ‖l • a + μ • b‖ = 1)
    (hmax : ∀ l' μ' : ℝ, 0 ≤ l' → 0 ≤ μ' →
      ⟪y, l' • a + μ' • b⟫ ≤ ⟪y, l • a + μ • b⟫ * ‖l' • a + μ' • b‖) :
    ⟪y, a⟫ = ⟪y, l • a + μ • b⟫ * ⟪l • a + μ • b, a⟫ ∧
      ⟪y, b⟫ = ⟪y, l • a + μ • b⟫ * ⟪l • a + μ • b, b⟫ := by
  set z := l • a + μ • b with hz_def
  set M := ⟪y, z⟫ with hM_def
  have hz_norm : ‖z‖ = 1 := hz
  have hza : ⟪z, a⟫ = l + μ * ⟪a, b⟫ := by
    dsimp [z]
    calc
      ⟪l • a + μ • b, a⟫ = ⟪l • a, a⟫ + ⟪μ • b, a⟫ := by rw [inner_add_left]
      _ = l * ⟪a, a⟫ + μ * ⟪b, a⟫ := by simp [inner_smul_left]
      _ = l * (‖a‖ ^ 2) + μ * ⟪a, b⟫ := by rw [real_inner_self_eq_norm_sq, real_inner_comm b a]
      _ = l * 1 + μ * ⟪a, b⟫ := by rw [ha, one_pow]
      _ = l + μ * ⟪a, b⟫ := by ring
  have hzb : ⟪z, b⟫ = l * ⟪a, b⟫ + μ := by
    dsimp [z]
    calc
      ⟪l • a + μ • b, b⟫ = ⟪l • a, b⟫ + ⟪μ • b, b⟫ := by rw [inner_add_left]
      _ = l * ⟪a, b⟫ + μ * ⟪b, b⟫ := by simp [inner_smul_left]
      _ = l * ⟪a, b⟫ + μ * (‖b‖ ^ 2) := by rw [real_inner_self_eq_norm_sq]
      _ = l * ⟪a, b⟫ + μ * 1 := by rw [hb, one_pow]
      _ = l * ⟪a, b⟫ + μ := by ring
  have hza_pos : 0 < ⟪z, a⟫ := by
    rw [hza]
    nlinarith
  have hzb_pos : 0 < ⟪z, b⟫ := by
    rw [hzb]
    nlinarith
  have hza_le : ⟪y, a⟫ ≤ M * ⟪z, a⟫ := by
    by_contra! h
    have hq : 0 < ⟪y, a⟫ - M * ⟪z, a⟫ := by nlinarith
    have hgain := cover_chord_gain z a y hz_norm ha hza_pos hq
    rcases hgain with ⟨t, ht_pos, ht_le_one, h_ineq⟩
    have h_nonneg_l' : 0 ≤ (1 - t) * l + t := by nlinarith
    have h_nonneg_μ' : 0 ≤ (1 - t) * μ := by nlinarith
    have h_eq : (1 - t) • z + t • a = ((1 - t) * l + t) • a + ((1 - t) * μ) • b := by
      dsimp [z]
      calc
        (1 - t) • (l • a + μ • b) + t • a
            = ((1 - t) • (l • a) + (1 - t) • (μ • b)) + t • a := by rw [smul_add]
        _ = (((1 - t) * l) • a + ((1 - t) * μ) • b) + t • a := by simp [smul_smul]
        _ = ((1 - t) * l + t) • a + ((1 - t) * μ) • b := by
          simp [add_smul, add_comm, add_assoc]
    have h_contra := hmax ((1 - t) * l + t) ((1 - t) * μ) h_nonneg_l' h_nonneg_μ'
    rw [← hM_def] at h_ineq
    rw [h_eq] at h_ineq
    nlinarith
  have hzb_le : ⟪y, b⟫ ≤ M * ⟪z, b⟫ := by
    by_contra! h
    have hq : 0 < ⟪y, b⟫ - M * ⟪z, b⟫ := by nlinarith
    have hgain := cover_chord_gain z b y hz_norm hb hzb_pos hq
    rcases hgain with ⟨t, ht_pos, ht_le_one, h_ineq⟩
    have h_nonneg_l' : 0 ≤ (1 - t) * l := by nlinarith
    have h_nonneg_μ' : 0 ≤ (1 - t) * μ + t := by nlinarith
    have h_eq : (1 - t) • z + t • b = ((1 - t) * l) • a + ((1 - t) * μ + t) • b := by
      dsimp [z]
      calc
        (1 - t) • (l • a + μ • b) + t • b
            = ((1 - t) • (l • a) + (1 - t) • (μ • b)) + t • b := by rw [smul_add]
        _ = (((1 - t) * l) • a + ((1 - t) * μ) • b) + t • b := by simp [smul_smul]
        _ = ((1 - t) * l) • a + (((1 - t) * μ) • b + t • b) := by rw [add_assoc]
        _ = ((1 - t) * l) • a + ((1 - t) * μ + t) • b := by rw [add_smul]
    have h_contra := hmax ((1 - t) * l) ((1 - t) * μ + t) h_nonneg_l' h_nonneg_μ'
    rw [← hM_def] at h_ineq
    rw [h_eq] at h_ineq
    nlinarith
  have h_sum_eq_zero : l * (⟪y, a⟫ - M * ⟪z, a⟫) + μ * (⟪y, b⟫ - M * ⟪z, b⟫) = 0 := by
    calc
      l * (⟪y, a⟫ - M * ⟪z, a⟫) + μ * (⟪y, b⟫ - M * ⟪z, b⟫)
          = (l * ⟪y, a⟫ + μ * ⟪y, b⟫) - M * (l * ⟪z, a⟫ + μ * ⟪z, b⟫) := by ring
      _ = ⟪y, l • a + μ • b⟫ - M * ⟪z, l • a + μ • b⟫ := by
        simp [inner_add_right, inner_smul_right]
      _ = ⟪y, z⟫ - M * ⟪z, z⟫ := by rw [hz_def]
      _ = M - M * (‖z‖ ^ 2) := by rw [hM_def, real_inner_self_eq_norm_sq]
      _ = M - M * (1 ^ 2) := by rw [hz_norm]
      _ = M - M * (1 : ℝ) := by norm_num
      _ = 0 := by ring
  have h_diff1 : ⟪y, a⟫ - M * ⟪z, a⟫ = 0 := by
    have h_nonpos1 : ⟪y, a⟫ - M * ⟪z, a⟫ ≤ 0 := by nlinarith
    have h_nonpos2 : ⟪y, b⟫ - M * ⟪z, b⟫ ≤ 0 := by nlinarith
    have : l * (⟪y, a⟫ - M * ⟪z, a⟫) = 0 := by nlinarith
    nlinarith [hl, this]
  have h_diff2 : ⟪y, b⟫ - M * ⟪z, b⟫ = 0 := by
    have h_nonpos1 : ⟪y, a⟫ - M * ⟪z, a⟫ ≤ 0 := by nlinarith
    have h_nonpos2 : ⟪y, b⟫ - M * ⟪z, b⟫ ≤ 0 := by nlinarith
    have : μ * (⟪y, b⟫ - M * ⟪z, b⟫) = 0 := by nlinarith
    nlinarith [hμ, this]
  constructor
  · rw [hM_def, hz_def]
    linarith
  · rw [hM_def, hz_def]
    linarith

/-! ## The two cases of the maximiser -/

/-- The maximiser is not a vertex. -/
theorem cover_vertex_not_max {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (d : ℝ) (hd : 0 < d ∧ d < π / 2)
    (hG : ∀ a b, G.Adj a b → sdist (x a) (x b) = d) (hne : ∀ v, ∃ w, G.Adj v w)
    (R : RotSys G) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (y : E3) (hy : ‖y‖ = 1) (hfar : ∀ v, d < sdist y (x v)) (v : V)
    (hmax : ∀ e : G.Dart, ∀ l μ : ℝ, 0 ≤ l → 0 ≤ μ →
      ⟪y, l • x e.fst + μ • x e.snd⟫ ≤ ⟪y, x v⟫ * ‖l • x e.fst + μ • x e.snd‖) : False := by
  have hc0 : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hc1 : cos d < 1 := by
    rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [pi_pos]) hd.1
  have hyv : ⟪y, x v⟫ < cos d :=
    cover_inner_lt_cos y (x v) d hd.1.le (by linarith [pi_pos]) (hfar v)
  have hk : ∀ w, G.Adj v w → ⟪x v, x w⟫ = cos d := fun w h =>
    cover_inner_eq_cos (x v) (x w) (hx v) (hx w) d (hG v w h)
  obtain ⟨w₀, hw₀⟩ := hne v
  set c := ⟪y, x v⟫ with hc
  set t : E3 := y - c • x v with ht
  have hvv : ⟪x v, x v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx v]; norm_num
  have htv : ⟪x v, t⟫ = 0 := by
    rw [ht, inner_sub_right, real_inner_smul_right, hvv, real_inner_comm, ← hc]; ring
  by_cases ht0 : t = 0
  · -- `y = c • x v`, so `c = -1`, and a neighbour is nearer to `y` than `x v`
    have hy' : y = c • x v := by rw [← sub_eq_zero]; exact ht0
    have hc2 : c ^ 2 = 1 := by
      have h := congrArg (fun p : E3 => ‖p‖ ^ 2) hy'
      simp only [hy, norm_smul, hx v, Real.norm_eq_abs, mul_one, sq_abs] at h
      linarith
    have hcm : c = -1 := by nlinarith
    have hm := hmax ⟨(v, w₀), hw₀⟩ 0 1 le_rfl zero_le_one
    simp only [zero_smul, one_smul, zero_add, hx w₀, mul_one] at hm
    have hyw : ⟪y, x w₀⟫ = c * cos d := by
      rw [hy', real_inner_smul_left, hk w₀ hw₀]
    rw [hyw, hcm] at hm
    linarith
  · obtain ⟨w, hw, hpos⟩ :=
      exists_pos_of_corner_lt_pi R x hx hR hcorner v ⟨w₀, hw₀⟩ t htv ht0
    have hq : 0 < ⟪y, x w⟫ - ⟪y, x v⟫ * ⟪x v, x w⟫ := by
      have : ⟪t, x w⟫ = ⟪y, x w⟫ - c * ⟪x v, x w⟫ := by
        rw [ht, inner_sub_left, real_inner_smul_left]
      rw [← hc]; linarith
    obtain ⟨s, hs0, hs1, hgain⟩ :=
      cover_chord_gain (x v) (x w) y (hx v) (hx w) (by rw [hk w hw]; exact hc0) hq
    have hm := hmax ⟨(v, w), hw⟩ (1 - s) s (by linarith) hs0.le
    exact absurd hm (not_le.mpr hgain)

/-- Inside a drawn edge with `y` on its positive side, the face of the dart holds `y`. -/
theorem cover_face_of_interior {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (R : RotSys G) (hconv : StrictSupportFace R x)
    (hface3 : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e) (y : E3) (hy : ‖y‖ = 1)
    (e : G.Dart) (l μ : ℝ) (hl : 0 < l) (hμ : 0 < μ) (hz : ‖l • x e.fst + μ • x e.snd‖ = 1)
    (hM0 : 0 ≤ ⟪y, l • x e.fst + μ • x e.snd⟫) (hM1 : ⟪y, l • x e.fst + μ • x e.snd⟫ < 1)
    (hmax : ∀ f : G.Dart, ∀ l' μ' : ℝ, 0 ≤ l' → 0 ≤ μ' →
      ⟪y, l' • x f.fst + μ' • x f.snd⟫ ≤
        ⟪y, l • x e.fst + μ • x e.snd⟫ * ‖l' • x f.fst + μ' • x f.snd‖)
    (hside : 0 < ⟪cross (x e.fst) (x e.snd), y⟫) :
    ∀ n : ℕ, 0 < ⟪cross (x ((R.face ^ n) e).fst) (x ((R.face ^ n) e).snd), y⟫ := by
  set m := Function.minimalPeriod R.face e with hm
  set A := faceSeq R x e with hAdef
  have hA : IsCPoly m A := faceSeq_isCPoly R x hx hconv e (hface3 e)
  have hA0 : A 0 = x e.fst := rfl
  have hA1 : A 1 = x e.snd := by rw [hAdef, faceSeq_succ]; rfl
  set z := l • x e.fst + μ • x e.snd with hzdef
  have hzA : z = l • A 0 + μ • A 1 := by rw [hA0, hA1]
  have hN : ∀ n, cross (x ((R.face ^ n) e).fst) (x ((R.face ^ n) e).snd) =
      cross (A n) (A (n + 1)) := by
    intro n; rw [hAdef, faceSeq_succ]; rfl
  have hz0 : ⟪cross (A 0) (A (0 + 1)), z⟫ = 0 := by
    rw [zero_add, hzA, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      triple_cycle (A 0) (A 1) (A 0), inner_cross_right_zero, inner_cross_right_zero]
    ring
  have hy0 : 0 < ⟪cross (A 0) (A (0 + 1)), y⟫ := by
    rw [zero_add, hA0, hA1]; exact hside
  suffices hins : Inside A y by
    intro n; rw [hN]; exact hins n
  rw [inside_iff hA]
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hjm, hj⟩ := hcon
  obtain ⟨s, hs0, hs1, hcl, i, -, hi0⟩ := cover_first_exit (Finset.range m)
    (fun i => ⟪cross (A i) (A (i + 1)), z⟫) (fun i => ⟪cross (A i) (A (i + 1)), y⟫)
    (by
      intro i hi
      rw [Finset.mem_range] at hi
      rcases Nat.eq_zero_or_pos i with rfl | hi1
      · exact hz0.ge
      · rw [hzA]; exact (hA.pos_of_open_side l μ hl hμ i hi1 hi).le)
    (by
      intro i hi hi0
      rw [Finset.mem_range] at hi
      rcases Nat.eq_zero_or_pos i with rfl | hi1
      · exact hy0
      · rw [hzA] at hi0; exact absurd hi0 (hA.pos_of_open_side l μ hl hμ i hi1 hi).ne')
    ⟨j, Finset.mem_range.mpr hjm, hj⟩
  set p : E3 := (1 - s) • z + s • y with hp
  have hpN : ∀ k, ⟪cross (A k) (A (k + 1)), p⟫ =
      (1 - s) * ⟪cross (A k) (A (k + 1)), z⟫ + s * ⟪cross (A k) (A (k + 1)), y⟫ := by
    intro k; rw [hp, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hpcl : InClosed A p := by
    rw [inClosed_iff hA]
    intro k hk
    rw [hpN]; exact hcl k (Finset.mem_range.mpr hk)
  obtain ⟨l', μ', hl', hμ', hpc⟩ := hA.comb_of_side p hpcl i (by rw [hpN]; exact hi0)
  obtain ⟨f, hf1, hf2⟩ := faceSeq_adj R x e i
  have hle := hmax f l' μ' hl' hμ'
  rw [← hf1, ← hf2, ← hpc] at hle
  have hgain := cover_geodesic_gain z y hz hy hM0 hM1 s hs0 hs1
  rw [← hp] at hgain
  linarith

/-! ## The theorem -/

/-- Every unit point at distance more than `d` from every vertex is strictly inside some face (the
vertex type is nonempty: with no vertex there is no dart). -/
theorem exists_face_inside {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V}
    (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (d : ℝ) (hd : 0 < d ∧ d < π / 2)
    (hG : ∀ a b, G.Adj a b → sdist (x a) (x b) = d) (hne : ∀ v, ∃ w, G.Adj v w)
    (R : RotSys G) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (hconv : StrictSupportFace R x) (hface3 : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e)
    (y : E3) (hy : ‖y‖ = 1) (hfar : ∀ v, d < sdist y (x v)) :
    ∃ e : G.Dart, ∀ n : ℕ, 0 < ⟪cross (x ((R.face ^ n) e).fst) (x ((R.face ^ n) e).snd), y⟫ := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hc0 : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hk : ∀ e : G.Dart, ⟪x e.fst, x e.snd⟫ = cos d := fun e =>
    cover_inner_eq_cos _ _ (hx _) (hx _) d (hG _ _ e.adj)
  have hfar' : ∀ v, ⟪y, x v⟫ < cos d := fun v =>
    cover_inner_lt_cos y (x v) d hd.1.le (by linarith [pi_pos]) (hfar v)
  have : Nonempty G.Dart := ⟨⟨(v₀, (hne v₀).choose), (hne v₀).choose_spec⟩⟩
  obtain ⟨e₀, l₀, μ₀, hl₀, hμ₀, hz1, hmax⟩ := cover_exists_cone_max (fun e : G.Dart => x e.fst)
    (fun e => x e.snd) (fun e => hx _) (fun e => hx _) (fun e => by rw [hk]; exact hc0) y
  set a := x e₀.fst with ha
  set b := x e₀.snd with hb
  set z := l₀ • a + μ₀ • b with hz
  have hna : ‖a‖ = 1 := hx _
  have hnb : ‖b‖ = 1 := hx _
  have hab : ⟪a, b⟫ = cos d := hk e₀
  -- the maximiser is not a vertex
  have hvert : ∀ v, z = x v → False := fun v hzv =>
    cover_vertex_not_max x hx d hd hG hne R hR hcorner y hy hfar v
      (fun f l μ hl hμ => by have h := hmax f l μ hl hμ; rwa [hzv] at h)
  rcases hμ₀.eq_or_lt with hμ0 | hμpos
  · refine (hvert e₀.fst ?_).elim
    have hza : z = l₀ • a := by rw [hz, ← hμ0, zero_smul, add_zero]
    have hl1 : l₀ = 1 := by
      rw [hza, norm_smul, hna, mul_one, Real.norm_eq_abs, abs_of_nonneg hl₀] at hz1
      exact hz1
    rw [hza, hl1, one_smul]
  rcases hl₀.eq_or_lt with hl0 | hlpos
  · refine (hvert e₀.snd ?_).elim
    have hzb : z = μ₀ • b := by rw [hz, ← hl0, zero_smul, zero_add]
    have hμ1 : μ₀ = 1 := by
      rw [hzb, norm_smul, hnb, mul_one, Real.norm_eq_abs, abs_of_nonneg hμ₀] at hz1
      exact hz1
    rw [hzb, hμ1, one_smul]
  -- inside the drawn edge of `e₀`
  obtain ⟨hya, hyb⟩ := cover_first_order a b y hna hnb (by rw [hab]; exact hc0) l₀ μ₀ hlpos hμpos
    hz1 (fun l μ hl hμ => hmax e₀ l μ hl hμ)
  rw [← hz] at hya hyb
  set M := ⟪y, z⟫ with hM
  have hza1 : ⟪z, a⟫ < 1 := by
    have hc1 : cos d < 1 := by
      rw [← cos_zero]
      exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [pi_pos]) hd.1
    have hzz : ‖z‖ ^ 2 = l₀ ^ 2 + μ₀ ^ 2 + 2 * l₀ * μ₀ * cos d := by
      rw [← real_inner_self_eq_norm_sq, hz, inner_add_left, inner_add_right, inner_add_right,
        real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hna, hnb,
        real_inner_comm a b, hab]
      ring
    have hzav : ⟪z, a⟫ = l₀ + μ₀ * cos d := by
      rw [hz, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hna, real_inner_comm a b, hab]
      ring
    rw [hz1] at hzz
    rw [hzav]
    nlinarith [mul_pos hμpos hμpos, mul_pos (mul_pos hμpos hμpos) (sub_pos.mpr hc1)]
  have hM0 : 0 ≤ M := by
    by_contra hneg
    rw [not_le] at hneg
    have h := hmax e₀ 1 0 zero_le_one le_rfl
    simp only [one_smul, zero_smul, add_zero] at h
    rw [hna, mul_one, hya] at h
    nlinarith
  have hM1 : M < 1 := by
    have hle : M ≤ 1 := by
      have := real_inner_le_norm y z
      rw [hy, hz1, mul_one] at this
      exact this
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h, one_mul] at hya hyb
      rcases cover_arc_inner_ge a b hna hnb l₀ μ₀ hl₀ hμ₀ hz1 with h' | h'
      · rw [← hz, ← hya, hab] at h'
        exact absurd h' (not_le.mpr (hfar' e₀.fst))
      · rw [← hz, ← hyb, hab] at h'
        exact absurd h' (not_le.mpr (hfar' e₀.snd))
  -- `y` is off the great circle of `e₀`
  set τ : E3 := y - M • z with hτ
  have hτa : ⟪τ, a⟫ = 0 := by rw [hτ, inner_sub_left, real_inner_smul_left, hya]; ring
  have hτb : ⟪τ, b⟫ = 0 := by rw [hτ, inner_sub_left, real_inner_smul_left, hyb]; ring
  have hτn : ⟪cross a b, τ⟫ = ⟪cross a b, y⟫ := by
    rw [hτ, inner_sub_right, real_inner_smul_right, hz, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, triple_cycle a b a, inner_cross_right_zero, inner_cross_right_zero]
    ring
  have hτnorm : ‖τ‖ ^ 2 = 1 - M ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hτ, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hy, hz1, real_inner_comm y z, ← hM]
    ring
  have hsq := cover_inner_cross_sq a b τ hna hnb hτa hτb
  rw [hτn, hτnorm, hab] at hsq
  have hc1 : cos d < 1 := by
    rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [pi_pos]) hd.1
  have hsq_pos : 0 < ⟪cross a b, y⟫ ^ 2 := by
    rw [hsq]
    apply mul_pos <;> nlinarith
  have hne0 : ⟪cross a b, y⟫ ≠ 0 := by
    intro h; rw [h] at hsq_pos; simp at hsq_pos
  rcases hne0.lt_or_gt with hneg | hpos
  · -- orient by the reversed dart
    have hs1 : x e₀.symm.fst = b := rfl
    have hs2 : x e₀.symm.snd = a := rfl
    have hzs : μ₀ • x e₀.symm.fst + l₀ • x e₀.symm.snd = z := by rw [hs1, hs2, hz, add_comm]
    refine ⟨e₀.symm, cover_face_of_interior x hx R hconv hface3 y hy e₀.symm μ₀ l₀ hμpos hlpos
      (by rw [hzs]; exact hz1) (by rw [hzs]; exact hM0) (by rw [hzs]; exact hM1)
      (fun f l μ hl hμ => by rw [hzs]; exact hmax f l μ hl hμ) ?_⟩
    rw [hs1, hs2, cross_swap, inner_neg_left]
    linarith
  · exact ⟨e₀, cover_face_of_interior x hx R hconv hface3 y hy e₀ l₀ μ₀ hlpos hμpos hz1 hM0 hM1
      (fun f l μ hl hμ => hmax f l μ hl hμ) hpos⟩

end Tammes15.Geom
