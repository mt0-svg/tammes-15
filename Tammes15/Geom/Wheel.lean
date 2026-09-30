import Tammes15.Geom.Basic
import Tammes15.Draw.Frame

/-!
# The wheel at an inside point

At a point `x` strictly inside a convex polygon in cone form, the tangent directions towards the
vertices turn monotonically, each step an angle in `(0, π)`, and the steps add up to `2π`
(paper Section 3, proofs of Proposition nor and of (T8)). Proof in tangent coordinates `tz`:
`Im (conj (tz a) * tz b) = ⟪cross a b, x⟫`, the partial sums of the arguments stay below `2π` up
to the last vertex because the sign of `⟪cross (A 0) (A j), x⟫` switches once (`switch_of_inside`,
from `cramer4`), and the total is a positive multiple of `2π` below `3π` (`phase_sum`).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace ComplexConjugate

namespace Tammes15.Geom

/-- Tangent coordinate of `p` at `x` in the frame `(e, cross x e)`. -/
noncomputable def tz (x e p : E3) : ℂ := ⟨⟪p, e⟫, ⟪p, cross x e⟫⟩

theorem exists_unit_orth (x : E3) (hx : ‖x‖ = 1) : ∃ e : E3, ‖e‖ = 1 ∧ ⟪x, e⟫ = 0 := by
  simpa [hx] using exists_unit_orthogonal x

theorem tz_eq_tcoord (x e p : E3) : tz x e p = tcoord x e p := rfl

theorem im_conj_mul_tz (x e a b : E3) (hx : ‖x‖ = 1) (he : ‖e‖ = 1) (hxe : ⟪x, e⟫ = 0) :
    (conj (tz x e a) * tz x e b).im = ⟪cross a b, x⟫ := by
  have h := det_tdir_frame x e a b hx he hxe
  have h2 : ⟪x, cross (tdir x a) (tdir x b)⟫ = ⟪cross a b, x⟫ := by
    simp only [tdir, inner_coords, cross_coords]; simp; ring
  rw [← h2, h]
  simp [tz, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem tdir_eq_tz (x e a : E3) (hx : ‖x‖ = 1) (he : ‖e‖ = 1) (hxe : ⟪x, e⟫ = 0) :
    tdir x a = (tz x e a).re • e + (tz x e a).im • cross x e := by
  simpa [tz] using tdir_frame x e a hx he hxe

theorem re_conj_mul_tz (x e a b : E3) (hx : ‖x‖ = 1) (he : ‖e‖ = 1) (hxe : ⟪x, e⟫ = 0) :
    (conj (tz x e a) * tz x e b).re = ⟪tdir x a, tdir x b⟫ := by
  rw [inner_tdir_frame x e a b hx he hxe]
  simp [tz, Complex.mul_re, Complex.conj_re, Complex.conj_im]

theorem norm_tz (x e a : E3) (hx : ‖x‖ = 1) (he : ‖e‖ = 1) (hxe : ⟪x, e⟫ = 0) :
    ‖tz x e a‖ = ‖tdir x a‖ :=
  (norm_tdir_eq_norm_tcoord x e a hx he hxe).symm

/-- The angle between two tangent directions is the argument of their quotient, when positive. -/
theorem angle_tdir_eq_arg (x e a b : E3) (hx : ‖x‖ = 1) (he : ‖e‖ = 1) (hxe : ⟪x, e⟫ = 0)
    (hpos : 0 < ⟪cross a b, x⟫) :
    angle (tdir x a) (tdir x b) = Complex.arg (conj (tz x e a) * tz x e b) := by
  set u := tdir x a
  set v := tdir x b
  set z := conj (tz x e a) * tz x e b
  have hz_im_pos : 0 < z.im := by
    rw [Tammes15.Geom.im_conj_mul_tz x e a b hx he hxe]
    exact hpos
  have hz_re : z.re = ⟪u, v⟫ := by
    rw [Tammes15.Geom.re_conj_mul_tz x e a b hx he hxe]
  have hnorm_z : ‖z‖ = ‖u‖ * ‖v‖ := by
    calc
      ‖z‖ = ‖conj (tz x e a) * tz x e b‖ := rfl
      _ = ‖conj (tz x e a)‖ * ‖tz x e b‖ := by rw [Complex.norm_mul]
      _ = ‖tz x e a‖ * ‖tz x e b‖ := by rw [Complex.norm_conj]
      _ = ‖tdir x a‖ * ‖tdir x b‖ := by
        rw [Tammes15.Geom.norm_tz x e a hx he hxe, Tammes15.Geom.norm_tz x e b hx he hxe]
      _ = ‖u‖ * ‖v‖ := rfl
  have hz_arg : z.arg = Real.arccos (z.re / ‖z‖) := by
    rw [Complex.arg_of_im_pos hz_im_pos]
  have h_angle_cos : Real.cos (angle u v) = ⟪u, v⟫ / (‖u‖ * ‖v‖) := by
    rw [InnerProductGeometry.cos_angle]
  have h_arccos_cos : Real.arccos (Real.cos (angle u v)) = angle u v :=
    Real.arccos_cos (InnerProductGeometry.angle_nonneg u v) (InnerProductGeometry.angle_le_pi u v)
  calc
    angle u v = Real.arccos (Real.cos (angle u v)) := by rw [h_arccos_cos]
    _ = Real.arccos (⟪u, v⟫ / (‖u‖ * ‖v‖)) := by rw [h_angle_cos]
    _ = Real.arccos (z.re / ‖z‖) := by rw [hz_re, hnorm_z]
    _ = z.arg := by rw [hz_arg]
    _ = Complex.arg (conj (tz x e a) * tz x e b) := rfl

/-- Telescoping of arguments. -/
theorem conj_mul_eq_exp_sum (z : ℕ → ℂ) (hz : ∀ i, z i ≠ 0) (n : ℕ) :
    conj (z 0) * z n = ((‖z 0‖ * ‖z n‖ : ℝ) : ℂ) *
      Complex.exp (((∑ i ∈ Finset.range n, Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℂ) *
        Complex.I) := by
  induction' n with n ih
  · -- n = 0
    have h0 : conj (z 0) * z 0 = ((‖z 0‖ * ‖z 0‖ : ℝ) : ℂ) := by
      calc
        conj (z 0) * z 0 = (Complex.normSq (z 0) : ℂ) := by
          rw [← Complex.normSq_eq_conj_mul_self]
        _ = ((‖z 0‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.normSq_eq_norm_sq]
        _ = ((‖z 0‖ * ‖z 0‖ : ℝ) : ℂ) := by ring
    simp [h0, Finset.sum_range_zero, Complex.exp_zero]
  · -- n → n+1
    have hzn : conj (z n) * z n = ((‖z n‖ ^ 2 : ℝ) : ℂ) := by
      calc
        conj (z n) * z n = (Complex.normSq (z n) : ℂ) := by
          rw [← Complex.normSq_eq_conj_mul_self]
        _ = ((‖z n‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.normSq_eq_norm_sq]
    have hzn_ne_zero : ((‖z n‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      intro hzero
      have hzero' : ‖z n‖ ^ 2 = (0 : ℝ) := by exact_mod_cast hzero
      have hnorm : ‖z n‖ = 0 := by
        nlinarith
      have hz' : z n ≠ 0 := hz n
      rw [norm_eq_zero] at hnorm
      exact hz' hnorm
    have h_polar_raw : conj (z n) * z (n + 1) =
        ((‖conj (z n) * z (n + 1)‖ : ℝ) : ℂ) *
        Complex.exp (((Complex.arg (conj (z n) * z (n + 1)) : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    have h_norm_w : ‖conj (z n) * z (n + 1)‖ = ‖z n‖ * ‖z (n + 1)‖ := by
      simp
    have h_polar : conj (z n) * z (n + 1) =
        ((‖z n‖ * ‖z (n + 1)‖ : ℝ) : ℂ) *
        Complex.exp (((Complex.arg (conj (z n) * z (n + 1)) : ℝ) : ℂ) * Complex.I) := by
      nth_rw 1 [h_polar_raw]
      have hcoeff : ((‖conj (z n) * z (n + 1)‖ : ℝ) : ℂ) = ((‖z n‖ * ‖z (n + 1)‖ : ℝ) : ℂ) := by
        push_cast
        simp [h_norm_w]
      rw [hcoeff]
    have h_key : (conj (z 0) * z (n + 1)) * ((‖z n‖ ^ 2 : ℝ) : ℂ) =
        ((‖z 0‖ * ‖z (n + 1)‖ : ℝ) : ℂ) *
        Complex.exp (((∑ i ∈ Finset.range (n + 1), Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℂ) * Complex.I) *
        ((‖z n‖ ^ 2 : ℝ) : ℂ) := by
      calc
        (conj (z 0) * z (n + 1)) * ((‖z n‖ ^ 2 : ℝ) : ℂ)
            = (conj (z 0) * z (n + 1)) * (conj (z n) * z n) := by rw [hzn]
        _ = (conj (z 0) * z n) * (conj (z n) * z (n + 1)) := by ring
        _ = (((‖z 0‖ * ‖z n‖ : ℝ) : ℂ) *
              Complex.exp (((∑ i ∈ Finset.range n, Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℂ) * Complex.I) *
              (conj (z n) * z (n + 1))) := by rw [ih]
        _ = (((‖z 0‖ * ‖z n‖ : ℝ) : ℂ) *
              Complex.exp (((∑ i ∈ Finset.range n, Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℂ) * Complex.I) *
              (((‖z n‖ * ‖z (n + 1)‖ : ℝ) : ℂ) *
              Complex.exp (((Complex.arg (conj (z n) * z (n + 1)) : ℝ) : ℂ) * Complex.I))) := by
          nth_rw 1 [h_polar]
        _ = ((‖z 0‖ * ‖z n‖ : ℝ) : ℂ) * (‖z n‖ * ‖z (n + 1)‖ : ℝ) *
              (Complex.exp (((∑ i ∈ Finset.range n, Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((Complex.arg (conj (z n) * z (n + 1)) : ℝ) : ℂ) * Complex.I)) := by ring
        _ = ((‖z 0‖ * ‖z n‖ : ℝ) : ℂ) * (‖z n‖ * ‖z (n + 1)‖ : ℝ) *
              Complex.exp ((((∑ i ∈ Finset.range n, Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℂ) * Complex.I) +
                (((Complex.arg (conj (z n) * z (n + 1)) : ℝ) : ℂ) * Complex.I)) := by
          rw [Complex.exp_add]
        _ = ((‖z 0‖ * ‖z n‖ : ℝ) : ℂ) * (‖z n‖ * ‖z (n + 1)‖ : ℝ) *
              Complex.exp ((((∑ i ∈ Finset.range n, Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℂ) +
                ((Complex.arg (conj (z n) * z (n + 1)) : ℝ) : ℂ)) * Complex.I) := by ring
        _ = ((‖z 0‖ * ‖z n‖ : ℝ) : ℂ) * (‖z n‖ * ‖z (n + 1)‖ : ℝ) *
              Complex.exp ((((∑ i ∈ Finset.range n, Complex.arg (conj (z i) * z (i + 1)) : ℝ) +
                Complex.arg (conj (z n) * z (n + 1)) : ℝ) : ℂ) * Complex.I) := by push_cast; ring
        _ = ((‖z 0‖ * ‖z n‖ : ℝ) : ℂ) * (‖z n‖ * ‖z (n + 1)‖ : ℝ) *
              Complex.exp ((((∑ i ∈ Finset.range (n + 1), Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℝ) : ℂ) * Complex.I) := by
          rw [Finset.sum_range_succ]
        _ = ((‖z 0‖ * ‖z n‖ * ‖z n‖ * ‖z (n + 1)‖ : ℝ) : ℂ) *
              Complex.exp ((((∑ i ∈ Finset.range (n + 1), Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℝ) : ℂ) * Complex.I) := by
          push_cast; ring
        _ = (((‖z 0‖ * ‖z (n + 1)‖ : ℝ) * (‖z n‖ ^ 2 : ℝ) : ℝ) : ℂ) *
              Complex.exp ((((∑ i ∈ Finset.range (n + 1), Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℝ) : ℂ) * Complex.I) := by ring
        _ = ((‖z 0‖ * ‖z (n + 1)‖ : ℝ) : ℂ) *
              Complex.exp ((((∑ i ∈ Finset.range (n + 1), Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℝ) : ℂ) * Complex.I) *
              ((‖z n‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    -- Cancel ((‖z n‖ ^ 2 : ℝ) : ℂ) from both sides
    apply mul_right_cancel₀ hzn_ne_zero
    calc
      (conj (z 0) * z (n + 1)) * ((‖z n‖ ^ 2 : ℝ) : ℂ)
          = ((‖z 0‖ * ‖z (n + 1)‖ : ℝ) : ℂ) *
            Complex.exp (((∑ i ∈ Finset.range (n + 1), Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℂ) * Complex.I) *
            ((‖z n‖ ^ 2 : ℝ) : ℂ) := by rw [h_key]
      _ = (((‖z 0‖ * ‖z (n + 1)‖ : ℝ) : ℂ) *
            Complex.exp (((∑ i ∈ Finset.range (n + 1), Complex.arg (conj (z i) * z (i + 1)) : ℝ) : ℂ) * Complex.I)) *
            ((‖z n‖ ^ 2 : ℝ) : ℂ) := by ring

/-- Real phase lemma: increasing partial sums with steps in `(0, π)`, closing up modulo `2π`,
whose sine changes sign once, end at `2π`. -/
theorem phase_sum (m : ℕ) (hm : 2 ≤ m) (S : ℕ → ℝ) (h0 : S 0 = 0)
    (hstep : ∀ i < m, 0 < S (i + 1) - S i ∧ S (i + 1) - S i < π) (hclose : cos (S m) = 1)
    (hswitch : ∀ j, 1 ≤ j → j + 1 < m → 0 ≤ sin (S (j + 1)) → 0 < sin (S j)) :
    S m = 2 * π := by
  -- Extract the two parts of hstep
  have hpos : ∀ i < m, 0 < S (i + 1) - S i := fun i hi => (hstep i hi).1
  have hlt : ∀ i < m, S (i + 1) - S i < π := fun i hi => (hstep i hi).2
  -- S is strictly increasing on i < m
  have hinc : ∀ i < m, S i < S (i + 1) := by
    intro i hi
    have h := hpos i hi
    linarith
  -- S i > 0 for 0 < i ≤ m
  have hpos_S : ∀ i, 0 < i → i ≤ m → 0 < S i := by
    intro i hi_pos hi_le
    induction' i with k ih
    · exact (Nat.not_lt_zero _ hi_pos).elim
    · by_cases hk0 : k = 0
      · subst hk0
        have h := hpos 0 (by omega)
        rw [h0] at h
        linarith
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have hk_le_m : k ≤ m := by omega
        have hSk_pos := ih hk_pos hk_le_m
        have hSk_lt_Sk1 : S k < S (k + 1) := hinc k (by omega)
        linarith
  -- S m > 0
  have hSm_pos : 0 < S m := hpos_S m (by omega) (le_refl m)
  -- From cos (S m) = 1, get S m = 2π * n for some integer n
  rcases (Real.cos_eq_one_iff (S m)).mp hclose with ⟨n, hn⟩
  -- hn: (n : ℝ) * (2 * π) = S m
  have hn_pos : 0 < (n : ℝ) := by
    have h2pi_pos : 0 < 2 * π := by positivity
    have hpos_prod : 0 < (n : ℝ) * (2 * π) := by
      rw [hn]
      exact hSm_pos
    exact pos_of_mul_pos_left hpos_prod (by linarith)
  -- Now we need to show S m < 4π
  have hSm_lt_4pi : S m < 4 * π := by
    by_cases h_last_lt_pi : S (m - 1) < π
    · -- Case A: S (m-1) < π, then S m < 2π < 4π
      have hm1_lt_m : m - 1 < m := by omega
      rcases hstep (m - 1) hm1_lt_m with ⟨_, hlt_step⟩
      have hstep_m : S m - S (m - 1) < π := by
        have : (m - 1) + 1 = m := by omega
        rw [← this]
        exact hlt_step
      have hSm_lt_2pi : S m < 2 * π := by
        linarith
      linarith
    · -- Case B: S (m-1) ≥ π
      have h_exists : ∃ j, j < m ∧ π ≤ S j := by
        refine ⟨m - 1, by omega, by linarith⟩
      let j0 := Nat.find h_exists
      have hj0_spec : j0 < m ∧ π ≤ S j0 := Nat.find_spec h_exists
      rcases hj0_spec with ⟨hj0_lt_m, hj0_ge_pi⟩
      have hj0_min : ∀ j, j < j0 → S j < π := by
        intro j hj_lt_j0
        have hj_lt_m : j < m := lt_of_lt_of_le hj_lt_j0 (le_of_lt hj0_lt_m)
        by_contra! hge
        have h_not : ¬ (j < m ∧ π ≤ S j) := Nat.find_min h_exists hj_lt_j0
        exact h_not ⟨hj_lt_m, hge⟩
      -- j0 ≥ 2
      have hj0_ge_2 : 2 ≤ j0 := by
        by_contra! h_lt_2
        have hj0_lt_2 : j0 < 2 := by omega
        have h_cases : j0 = 0 ∨ j0 = 1 := by omega
        rcases h_cases with (h_j0_eq_0 | h_j0_eq_1)
        · rw [h_j0_eq_0, h0] at hj0_ge_pi
          have hpi_pos : 0 < π := Real.pi_pos
          linarith
        · rw [h_j0_eq_1] at hj0_ge_pi
          -- Need S 1 < π. From hstep 0: S 1 - S 0 < π, and S 0 = 0
          have hS1_lt_pi : S 1 < π := by
            have hstep0 := hstep 0 (by omega)
            rcases hstep0 with ⟨_, hlt0⟩
            rw [h0] at hlt0
            -- hlt0: S (0+1) - S 0 < π → S 1 - 0 < π → S 1 < π
            simp at hlt0
            exact hlt0
          linarith
      -- S j0 < 2π
      have hj0_lt_2pi : S j0 < 2 * π := by
        have h_prev_lt_j0 : j0 - 1 < j0 := by omega
        have h_prev_lt_m : j0 - 1 < m := lt_of_lt_of_le h_prev_lt_j0 (le_of_lt hj0_lt_m)
        have hS_prev_lt_pi : S (j0 - 1) < π := hj0_min (j0 - 1) h_prev_lt_j0
        have hstep_j0 : S (j0 - 1 + 1) - S (j0 - 1) < π := hlt (j0 - 1) h_prev_lt_m
        have h_eq : j0 - 1 + 1 = j0 := by omega
        rw [h_eq] at hstep_j0
        linarith
      -- sin(S j0) ≤ 0
      have hSj0_sin_nonpos : sin (S j0) ≤ 0 := by
        rw [← Real.sin_sub_two_pi]
        apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
        · linarith
        · linarith
      -- Now we prove by induction that for all j with j0 ≤ j < m, π ≤ S j < 2π
      have h_interval : ∀ j, j0 ≤ j → j < m → (π ≤ S j ∧ S j < 2 * π) := by
        have h_base : (j0 < m → (π ≤ S j0 ∧ S j0 < 2 * π)) := fun _ => ⟨hj0_ge_pi, hj0_lt_2pi⟩
        have h_step : ∀ k, j0 ≤ k → (k < m → (π ≤ S k ∧ S k < 2 * π)) → (k + 1 < m → (π ≤ S (k + 1) ∧ S (k + 1) < 2 * π)) := by
          intro k hk_le_j0 hk_ih hk1_lt_m
          rcases hk_ih (by omega) with ⟨hSk_ge_pi, hSk_lt_2pi⟩
          have hk_lt_m : k < m := by omega
          -- Show S (k+1) > π
          have hSk1_gt_pi : π < S (k + 1) := by
            have hSk_lt_Sk1 : S k < S (k + 1) := hinc k hk_lt_m
            linarith
          -- sin(S k) ≤ 0 (from S k ∈ [π, 2π))
          have hSk_sin_nonpos : sin (S k) ≤ 0 := by
            rw [← Real.sin_sub_two_pi]
            apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
            · linarith
            · linarith
          -- Need 1 ≤ k to apply hswitch contrapositive
          have hk_ge_1 : 1 ≤ k := by omega
          have hSk1_sin_neg : sin (S (k + 1)) < 0 := by
            -- contrapositive of hswitch: sin(S k) ≤ 0 → sin(S (k+1)) < 0
            by_contra! h_not_neg
            -- h_not_neg: sin(S (k+1)) ≥ 0
            have hpos_sin_k : 0 < sin (S k) := hswitch k hk_ge_1 hk1_lt_m h_not_neg
            linarith
          -- Now sin(S (k+1)) < 0, so S (k+1) cannot be in [2π, 3π)
          by_cases hSk1_ge_2pi : 2 * π ≤ S (k + 1)
          · -- If S (k+1) ≥ 2π, then sin(S (k+1) - 2π) ≥ 0
            -- But sin(S (k+1)) = sin(S (k+1) - 2π) < 0, contradiction
            have h_sin_ge : sin (S (k + 1) - 2 * π) ≥ 0 := by
              have hx : 0 ≤ S (k + 1) - 2 * π := by linarith
              have hx_le_pi : S (k + 1) - 2 * π ≤ π := by
                -- S (k+1) < S k + π < 2π + π = 3π
                have hSk1_lt_3pi : S (k + 1) < 3 * π := by
                  have hstep_k_lt : S (k + 1) - S k < π := hlt k hk_lt_m
                  linarith
                linarith
              exact Real.sin_nonneg_of_nonneg_of_le_pi hx hx_le_pi
            -- sin(S (k+1)) = sin(S (k+1) - 2π) by periodicity
            rw [Real.sin_sub_two_pi] at h_sin_ge
            linarith
          · -- S (k+1) < 2π
            have hSk1_lt_2pi : S (k + 1) < 2 * π := by linarith
            exact ⟨by linarith, hSk1_lt_2pi⟩
        intro j hj0_le_j hj_lt_m
        -- Use Nat.le_induction with P := λ k _ => (k < m → (π ≤ S k ∧ S k < 2 * π))
        have h_all : j < m → (π ≤ S j ∧ S j < 2 * π) :=
          Nat.le_induction (m := j0) (P := λ k _ => (k < m → (π ≤ S k ∧ S k < 2 * π)))
            h_base (fun k hk_le_j0 ih => fun hk1_lt_m => h_step k hk_le_j0 ih hk1_lt_m) j hj0_le_j
        exact h_all hj_lt_m
      -- Apply the interval lemma to m-1
      have hm1_lt_m : m - 1 < m := by omega
      have hS_last : π ≤ S (m - 1) ∧ S (m - 1) < 2 * π := by
        by_cases hm1_ge_j0 : j0 ≤ m - 1
        · exact h_interval (m - 1) hm1_ge_j0 hm1_lt_m
        · -- m-1 < j0, but j0 is minimal with S j0 ≥ π
          -- This means S (m-1) < π, contradicting h_last_lt_pi
          have h_lt_j0 : m - 1 < j0 := by omega
          have hS_lt_pi : S (m - 1) < π := hj0_min (m - 1) h_lt_j0
          linarith
      rcases hS_last with ⟨_, hS_last_lt_2pi⟩
      -- Now S m = S (m-1) + (S m - S (m-1)) < 2π + π = 3π < 4π
      have hstep_last : S m - S (m - 1) < π := by
        have : (m - 1) + 1 = m := by omega
        rw [← this]
        exact hlt (m - 1) hm1_lt_m
      have hSm_lt_3pi : S m < 3 * π := by
        have hpos_last : 0 < S ((m - 1) + 1) - S (m - 1) := hpos (m - 1) hm1_lt_m
        have h_eq : (m - 1) + 1 = m := by omega
        rw [h_eq] at hpos_last
        linarith
      linarith
  -- Now we have S m = 2π * n and 0 < S m < 4π, so n = 1
  have hn_lt_two : (n : ℝ) < 2 := by
    rw [← hn] at hSm_lt_4pi
    have h2pi_pos : 0 < 2 * π := by positivity
    nlinarith
  have hn_eq_one : n = 1 := by
    have hn_int_ge_one : (1 : ℤ) ≤ n := by
      by_contra! h_lt
      have : (n : ℤ) ≤ 0 := by omega
      have hn_nonpos : (n : ℝ) ≤ 0 := by exact_mod_cast this
      linarith [hn_pos, hn_nonpos]
    have hn_int_lt_two : (n : ℤ) < 2 := by
      by_contra! h_ge
      have : (2 : ℤ) ≤ n := h_ge
      have hn_ge_two : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    omega
  -- Finally, substitute n = 1 into hn
  rw [hn_eq_one] at hn
  simp at hn
  linarith

/-- Complex form of the wheel. -/
theorem arg_sum_eq_two_pi (m : ℕ) (hm : 2 ≤ m) (z : ℕ → ℂ) (hz : ∀ i, z i ≠ 0)
    (hper : z m = z 0) (hpos : ∀ i < m, 0 < (conj (z i) * z (i + 1)).im)
    (hswitch : ∀ j, 1 ≤ j → j + 1 < m → 0 ≤ (conj (z 0) * z (j + 1)).im →
      0 < (conj (z 0) * z j).im) :
    ∑ i ∈ Finset.range m, Complex.arg (conj (z i) * z (i + 1)) = 2 * π := by
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, Complex.arg (conj (z i) * z (i + 1)) with hS
  have hpolar := conj_mul_eq_exp_sum z hz
  have hr : ∀ n, 0 < ‖z 0‖ * ‖z n‖ := fun n =>
    mul_pos (norm_pos_iff.mpr (hz 0)) (norm_pos_iff.mpr (hz n))
  -- `Im (conj (z 0) * z n) = ‖z 0‖ ‖z n‖ sin (S n)`
  have him : ∀ n, (conj (z 0) * z n).im = (‖z 0‖ * ‖z n‖) * sin (S n) := by
    intro n
    rw [hpolar n, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hsin : ∀ n, 0 < sin (S n) ↔ 0 < (conj (z 0) * z n).im := fun n => by
    rw [him n]; exact (mul_pos_iff_of_pos_left (hr n)).symm
  have hsin' : ∀ n, 0 ≤ sin (S n) ↔ 0 ≤ (conj (z 0) * z n).im := fun n => by
    rw [him n]; exact (mul_nonneg_iff_of_pos_left (hr n)).symm
  show S m = 2 * π
  apply phase_sum m hm S (by simp [hS])
  · intro i hi
    have hsucc : S (i + 1) - S i = Complex.arg (conj (z i) * z (i + 1)) := by
      simp [hS, Finset.sum_range_succ]
    rw [hsucc]
    have h := hpos i hi
    refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr h.le) ?_,
      Complex.arg_lt_pi_iff.mpr (Or.inr h.ne')⟩
    intro h0
    exact h.ne' (Complex.arg_eq_zero_iff.mp h0.symm).2
  · have h := hpolar m
    rw [hper] at h
    have hre := congrArg Complex.re h
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at hre
    have hlhs : (conj (z 0) * z 0).re = ‖z 0‖ * ‖z 0‖ := by
      rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]; ring
    rw [hlhs] at hre
    have hp2 : 0 < ‖z 0‖ ^ 2 := pow_pos (norm_pos_iff.mpr (hz 0)) 2
    field_simp at hre
    exact mul_left_cancel₀ hp2.ne' (by rw [mul_one]; exact hre.symm)
  · intro j hj hjm h
    exact (hsin j).mpr (hswitch j hj hjm ((hsin' (j + 1)).mp h))

/-- The sign of `⟪cross (A 0) (A j), x⟫` switches once along the polygon. -/
theorem switch_of_inside {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (x : E3) (hin : Inside A x)
    (j : ℕ) (hj : 1 ≤ j) (hjm : j + 1 < m) (h : 0 ≤ ⟪cross (A 0) (A (j + 1)), x⟫) :
    0 < ⟪cross (A 0) (A j), x⟫ := by
  -- `[0, j, x] [0, 1, j+1] = [0, j+1, x] [0, 1, j] + [0, j, j+1] [0, 1, x]` (`cramer4`)
  have key : ⟪cross (A 0) (A j), x⟫ * ⟪cross (A 0) (A 1), A (j + 1)⟫ =
      ⟪cross (A 0) (A (j + 1)), x⟫ * ⟪cross (A 0) (A 1), A j⟫ +
        ⟪cross (A 0) (A j), A (j + 1)⟫ * ⟪cross (A 0) (A 1), x⟫ := by
    simp only [inner_coords, cross_coords]; simp; ring
  have h1 : 0 < ⟪cross (A 0) (A 1), A (j + 1)⟫ := by
    simpa using hA.support 0 (j + 1) (by omega) hjm
  have h2 : 0 ≤ ⟪cross (A 0) (A 1), A j⟫ := by
    rcases Nat.eq_or_lt_of_le hj with rfl | hj2
    · rw [inner_cross_right_zero]
    · simpa using (hA.support 0 j hj2 (by omega)).le
  have h3 : 0 < ⟪cross (A 0) (A j), A (j + 1)⟫ := by
    simpa using hA.triple_pos 0 j (j + 1) (by omega) (by omega) hjm
  have h4 : 0 < ⟪cross (A 0) (A 1), x⟫ := by simpa using hin 0
  by_contra hneg
  rw [not_lt] at hneg
  have := mul_nonpos_of_nonpos_of_nonneg hneg h1.le
  nlinarith [mul_pos h3 h4, mul_nonneg h h2]

theorem tdir_ne_zero_of_inside {A : ℕ → E3} (hunit : ∀ i, ‖A i‖ = 1) (x : E3) (hx : ‖x‖ = 1)
    (hin : Inside A x) (i : ℕ) : tdir x (A i) ≠ 0 := by
  intro hzero
  have h_tdir_def : tdir x (A i) = A i - ⟪x, A i⟫ • x := rfl
  rw [h_tdir_def] at hzero
  have h_eq : A i = ⟪x, A i⟫ • x := sub_eq_zero.mp hzero
  have h_cross : cross (A i) (A (i + 1)) = ⟪x, A i⟫ • cross x (A (i + 1)) := by
    have htemp : cross (A i) (A (i + 1)) = cross (⟪x, A i⟫ • x) (A (i + 1)) :=
      congrArg (fun a => cross a (A (i + 1))) h_eq
    rw [htemp]
    exact cross_smul_left x (A (i + 1)) (⟪x, A i⟫)
  have h_inner : ⟪cross (A i) (A (i + 1)), x⟫ = 0 := by
    rw [h_cross, inner_smul_left]
    have h : ⟪cross x (A (i + 1)), x⟫ = 0 := by
      rw [real_inner_comm]
      exact inner_cross_self x (A (i + 1))
    rw [h]
    simp
  have h_pos : 0 < ⟪cross (A i) (A (i + 1)), x⟫ := hin i
  linarith

/-- The tangent coordinate of a vertex at an inside point is not zero. -/
theorem tz_ne_zero_of_inside {A : ℕ → E3} (hunit : ∀ i, ‖A i‖ = 1) (x e : E3) (hx : ‖x‖ = 1)
    (he : ‖e‖ = 1) (hxe : ⟪x, e⟫ = 0) (hin : Inside A x) (i : ℕ) : tz x e (A i) ≠ 0 := by
  intro h
  apply tdir_ne_zero_of_inside hunit x hx hin i
  rw [← norm_eq_zero, ← norm_tz x e _ hx he hxe, h, norm_zero]

theorem arg_mem_Ioo_of_im_pos (w : ℂ) (h : 0 < w.im) : 0 < Complex.arg w ∧ Complex.arg w < π := by
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr h.le) ?_,
    Complex.arg_lt_pi_iff.mpr (Or.inr h.ne')⟩
  intro h0
  exact h.ne' (Complex.arg_eq_zero_iff.mp h0.symm).2

/-- The angles at an inside point between consecutive vertices add up to `2π`. -/
theorem wheel_sum {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (x : E3) (hx : ‖x‖ = 1)
    (hin : Inside A x) :
    ∑ i ∈ Finset.range m, angle (tdir x (A i)) (tdir x (A (i + 1))) = 2 * π := by
  obtain ⟨e, he, hxe⟩ := exists_unit_orth x hx
  have hz := tz_ne_zero_of_inside hA.unit x e hx he hxe hin
  have hsum := arg_sum_eq_two_pi m (by have := hA.three; omega) (fun i => tz x e (A i)) hz
    (by simpa using congrArg (tz x e) (hA.periodic 0))
    (fun i _ => by rw [im_conj_mul_tz x e _ _ hx he hxe]; exact hin i)
    (fun j hj hjm h => by
      rw [im_conj_mul_tz x e _ _ hx he hxe] at h ⊢
      exact switch_of_inside hA x hin j hj hjm h)
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ => angle_tdir_eq_arg x e _ _ hx he hxe (hin i)

/-- Polar form of `z` from the polar form of `conj z₀ * z`. -/
theorem eq_polar_of_conj_mul (z₀ z : ℂ) (h₀ : z₀ ≠ 0) (S r : ℝ)
    (h : conj z₀ * z = ((‖z₀‖ * r : ℝ) : ℂ) * Complex.exp ((S : ℂ) * Complex.I)) :
    z = (r : ℂ) * Complex.exp (((Complex.arg z₀ + S : ℝ) : ℂ) * Complex.I) := by
  have hpol : z₀ = (‖z₀‖ : ℂ) * Complex.exp ((Complex.arg z₀ : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I z₀).symm
  have hn : z₀ * conj z₀ = ((‖z₀‖ : ℂ)) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hne : ((‖z₀‖ : ℂ)) ^ 2 ≠ 0 := by
    have : (‖z₀‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h₀)
    exact pow_ne_zero 2 this
  apply mul_left_cancel₀ hne
  have hexp : Complex.exp (((Complex.arg z₀ + S : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((Complex.arg z₀ : ℂ) * Complex.I) * Complex.exp ((S : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [hexp]
  push_cast at h ⊢
  linear_combination (-z) * hn + z₀ * h +
    ((‖z₀‖ : ℂ) * (r : ℂ) * Complex.exp ((S : ℂ) * Complex.I)) * hpol

/-- Lifted angles of the tangent directions at an inside point. -/
theorem wheel_lift {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (x : E3) (hx : ‖x‖ = 1)
    (hin : Inside A x) (e : E3) (he : ‖e‖ = 1) (hxe : ⟪x, e⟫ = 0) :
    ∃ θ : ℕ → ℝ, (∀ i, 0 < θ (i + 1) - θ i ∧ θ (i + 1) - θ i < π) ∧
      (∀ i, θ (i + m) = θ i + 2 * π) ∧
      (∀ i, θ (i + 1) - θ i = angle (tdir x (A i)) (tdir x (A (i + 1)))) ∧
      ∀ i, tdir x (A i) = ‖tdir x (A i)‖ • (cos (θ i) • e + sin (θ i) • cross x e) := by
  set z : ℕ → ℂ := fun i => tz x e (A i) with hzdef
  have hz : ∀ i, z i ≠ 0 := tz_ne_zero_of_inside hA.unit x e hx he hxe hin
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, Complex.arg (conj (z i) * z (i + 1)) with hS
  have hstep : ∀ i, (fun n => Complex.arg (z 0) + S n) (i + 1) -
      (fun n => Complex.arg (z 0) + S n) i = Complex.arg (conj (z i) * z (i + 1)) := by
    intro i; simp [hS, Finset.sum_range_succ]
  have hang : ∀ i, Complex.arg (conj (z i) * z (i + 1)) =
      angle (tdir x (A i)) (tdir x (A (i + 1))) := fun i =>
    (angle_tdir_eq_arg x e _ _ hx he hxe (hin i)).symm
  refine ⟨fun n => Complex.arg (z 0) + S n, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hstep]
    apply arg_mem_Ioo_of_im_pos
    simp only [hzdef]
    rw [im_conj_mul_tz x e _ _ hx he hxe]
    exact hin i
  · intro i
    have hw := wheel_sum (hA.shift i) x hx (hin.shift i)
    simp only [hS, Finset.sum_range_add]
    have : ∑ k ∈ Finset.range m, Complex.arg (conj (z (i + k)) * z (i + k + 1)) = 2 * π := by
      rw [← hw]
      exact Finset.sum_congr rfl fun k _ => hang (i + k)
    rw [this]; ring
  · intro i; rw [hstep, hang]
  · intro i
    have hpolar := conj_mul_eq_exp_sum z hz i
    have hzi := eq_polar_of_conj_mul (z 0) (z i) (hz 0) (S i) ‖z i‖ hpolar
    have hre : (z i).re = ‖z i‖ * cos (Complex.arg (z 0) + S i) := by
      rw [hzi, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      rw [← hzi]
    have him : (z i).im = ‖z i‖ * sin (Complex.arg (z 0) + S i) := by
      rw [hzi, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      rw [← hzi]
    have hnorm : ‖z i‖ = ‖tdir x (A i)‖ := norm_tz x e _ hx he hxe
    calc tdir x (A i) = (z i).re • e + (z i).im • cross x e := tdir_eq_tz x e (A i) hx he hxe
      _ = ‖tdir x (A i)‖ • (cos (Complex.arg (z 0) + S i) • e +
          sin (Complex.arg (z 0) + S i) • cross x e) := by
        rw [hre, him, hnorm, smul_add, smul_smul, smul_smul]

end Tammes15.Geom
