import Mathlib
import Tammes15.Numerics.Taylor

open Real Finset Tammes15.Numerics

namespace D3Q2A0

def fm (a b : ℕ) : ℕ := a * b / 2 ^ 24

def cosFix (z : ℕ) : ℕ :=
  16777216 - fm (fm z z) (8388608 - fm (fm z z) (699051 - fm (fm z z) (23302 - fm (fm z z) 416)))

def sinFix (z : ℕ) : ℕ :=
  fm z (16777216 - fm (fm z z) (2796203 - fm (fm z z) (139810 - fm (fm z z) (3329 - fm (fm z z) 46))))

def sincos24o (x0 : ℕ) : ℕ × ℕ × ℕ :=
  if 26353589 < x0 then
    (if 13176794 < 52707179 - x0 then
      (cosFix (26353589 - (52707179 - x0)), sinFix (26353589 - (52707179 - x0)), 1)
    else (sinFix (52707179 - x0), cosFix (52707179 - x0), 1))
  else
    (if 13176794 < x0 then (cosFix (26353589 - x0), sinFix (26353589 - x0), 0)
    else (sinFix x0, cosFix x0, 0))
end D3Q2A0

open D3Q2A0

theorem D3Q2A0.fm_approx (a b : ℕ) (α β ea eb αm βm : ℝ) (hα : |α| ≤ αm) (hβ : |β| ≤ βm)
    (ha : |(a : ℝ) - 2 ^ 24 * α| ≤ ea) (hb : |(b : ℝ) - 2 ^ 24 * β| ≤ eb) :
    |(fm a b : ℝ) - 2 ^ 24 * (α * β)| ≤ αm * eb + βm * ea + ea * eb / 2 ^ 24 + 1 := by
  set A := (2 ^ 24 : ℝ) with hA
  have hApos : 0 < A := by
    norm_num [hA]
  have hA_nonneg : 0 ≤ A := by linarith
  have ea_nonneg : 0 ≤ ea := by
    have h := abs_nonneg ((a : ℝ) - 2 ^ 24 * α)
    linarith
  have eb_nonneg : 0 ≤ eb := by
    have h := abs_nonneg ((b : ℝ) - 2 ^ 24 * β)
    linarith
  have αm_nonneg : 0 ≤ αm := by
    have h := abs_nonneg α
    linarith
  have βm_nonneg : 0 ≤ βm := by
    have h := abs_nonneg β
    linarith
  have h_floor_low : (fm a b : ℝ) * A ≤ (a : ℝ) * (b : ℝ) := by
    have h := Nat.div_mul_le_self (a * b) (2 ^ 24)
    simpa [fm, hA] using mod_cast h
  have h_floor_high : (a : ℝ) * (b : ℝ) < ((fm a b : ℝ) + 1) * A := by
    have h_mod := Nat.mod_add_div (a * b) (2 ^ 24)
    have h_mod_lt : (a * b) % (2 ^ 24) < 2 ^ 24 := Nat.mod_lt _ (by norm_num)
    have h_mod_lt' : (Nat.cast ((a * b) % (2 ^ 24)) : ℝ) < A := by

      rw [hA]
      exact mod_cast h_mod_lt
    have h_eq : (a : ℝ) * (b : ℝ) = ((fm a b : ℝ) * A) + (Nat.cast ((a * b) % (2 ^ 24)) : ℝ) := by
      have h := congrArg (fun x : ℕ => (x : ℝ)) h_mod

      have h' : (Nat.cast ((a * b) % (2 ^ 24)) : ℝ) + (Nat.cast (2 ^ 24) : ℝ) * (Nat.cast ((a * b) / (2 ^ 24)) : ℝ) = (a : ℝ) * (b : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_mul] using h

      rw [h'.symm]

      dsimp [fm, A]

      ring
    nlinarith
  have h_floor_diff : |(fm a b : ℝ) - ((a : ℝ) * (b : ℝ)) / A| ≤ 1 := by
    have h1 : -1 ≤ (fm a b : ℝ) - ((a : ℝ) * (b : ℝ)) / A := by
      have hpos' : 0 < A := hApos
      have htemp : (fm a b : ℝ) * A ≤ (a : ℝ) * (b : ℝ) := h_floor_low

      nlinarith
    have h2 : (fm a b : ℝ) - ((a : ℝ) * (b : ℝ)) / A ≤ 1 := by
      have htemp : (a : ℝ) * (b : ℝ) < ((fm a b : ℝ) + 1) * A := h_floor_high
      nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  have h_algebra : ((a : ℝ) * (b : ℝ)) / A - A * (α * β) =
      ((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A + α * ((b : ℝ) - A * β) + β * ((a : ℝ) - A * α) := by
    field_simp [show A ≠ 0 from by linarith]
    ring_nf
  have h_bound1 : |((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A| ≤ ea * eb / A := by
    have h_num : |((a : ℝ) - A * α) * ((b : ℝ) - A * β)| ≤ ea * eb := by
      calc
        |((a : ℝ) - A * α) * ((b : ℝ) - A * β)| = |(a : ℝ) - A * α| * |(b : ℝ) - A * β| := abs_mul _ _
        _ ≤ ea * |(b : ℝ) - A * β| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        _ ≤ ea * eb := mul_le_mul_of_nonneg_left hb ea_nonneg
    rw [abs_div]
    have hA_abs : |A| = A := abs_of_pos hApos
    rw [hA_abs]
    exact (div_le_div_of_nonneg_right h_num hA_nonneg)
  have h_bound2 : |α * ((b : ℝ) - A * β)| ≤ αm * eb := by
    rw [abs_mul]
    exact mul_le_mul hα hb (abs_nonneg _) αm_nonneg
  have h_bound3 : |β * ((a : ℝ) - A * α)| ≤ βm * ea := by
    rw [abs_mul]
    exact mul_le_mul hβ ha (abs_nonneg _) βm_nonneg
  calc
    |(fm a b : ℝ) - A * (α * β)| = |((fm a b : ℝ) - ((a : ℝ) * (b : ℝ)) / A) +
        (((a : ℝ) * (b : ℝ)) / A - A * (α * β))| := by ring
    _ ≤ |(fm a b : ℝ) - ((a : ℝ) * (b : ℝ)) / A| + |((a : ℝ) * (b : ℝ)) / A - A * (α * β)| := abs_add_le _ _
    _ ≤ 1 + |((a : ℝ) * (b : ℝ)) / A - A * (α * β)| := by nlinarith
    _ = 1 + |(((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A + α * ((b : ℝ) - A * β) + β * ((a : ℝ) - A * α))| := by rw [h_algebra]
    _ ≤ 1 + (|((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A| + |α * ((b : ℝ) - A * β)| + |β * ((a : ℝ) - A * α)|) := by
      have h_triple : |((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A + α * ((b : ℝ) - A * β) + β * ((a : ℝ) - A * α)| ≤
          |((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A| + |α * ((b : ℝ) - A * β)| + |β * ((a : ℝ) - A * α)| := by
        calc
          |((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A + α * ((b : ℝ) - A * β) + β * ((a : ℝ) - A * α)|
              ≤ |((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A + α * ((b : ℝ) - A * β)| + |β * ((a : ℝ) - A * α)| := abs_add_le _ _
          _ ≤ (|((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A| + |α * ((b : ℝ) - A * β)|) + |β * ((a : ℝ) - A * α)| := by
            nlinarith [abs_add_le (((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A) (α * ((b : ℝ) - A * β))]
          _ = |((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A| + |α * ((b : ℝ) - A * β)| + |β * ((a : ℝ) - A * α)| := by ring
      nlinarith
    _ ≤ 1 + (ea * eb / A + αm * eb + βm * ea) := by
      have h_sum : |((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A| + |α * ((b : ℝ) - A * β)| + |β * ((a : ℝ) - A * α)| ≤
          ea * eb / A + αm * eb + βm * ea := by
        have h12 := add_le_add h_bound1 h_bound2
        have h123 := add_le_add h12 h_bound3
        linarith
      have h_add := add_le_add_right h_sum 1

      simpa [add_comm, add_left_comm, add_assoc] using h_add
    _ = αm * eb + βm * ea + ea * eb / A + 1 := by ring

theorem D3Q2A0.sub_approx (a b : ℕ) (α β ea eb : ℝ) (hab : b ≤ a)
    (ha : |(a : ℝ) - 2 ^ 24 * α| ≤ ea) (hb : |(b : ℝ) - 2 ^ 24 * β| ≤ eb) :
    |((a - b : ℕ) : ℝ) - 2 ^ 24 * (α - β)| ≤ ea + eb := by
  have hcast : ((a - b : ℕ) : ℝ) = (a : ℝ) - (b : ℝ) :=
    Nat.cast_sub hab
  rw [hcast]
  have h_eq : (a : ℝ) - (b : ℝ) - 2 ^ 24 * (α - β) = ((a : ℝ) - 2 ^ 24 * α) - ((b : ℝ) - 2 ^ 24 * β) := by
    ring
  rw [h_eq]
  calc
    |((a : ℝ) - 2 ^ 24 * α) - ((b : ℝ) - 2 ^ 24 * β)| ≤ |(a : ℝ) - 2 ^ 24 * α| + |(b : ℝ) - 2 ^ 24 * β| :=
      abs_sub _ _
    _ ≤ ea + eb := add_le_add ha hb

theorem D3Q2A0.fm_margin (a b : ℕ) (α β ea eb : ℝ) (hα : |α| ≤ 1) (hβ : |β| ≤ 1)
    (ha : |(a : ℝ) - 2 ^ 24 * α| ≤ ea) (hb : |(b : ℝ) - 2 ^ 24 * β| ≤ eb) (he : ea * eb ≤ 2 ^ 24) :
    |(fm a b : ℝ) - 2 ^ 24 * (α * β)| ≤ ea + eb + 2 := by
  set A := (2 ^ 24 : ℝ) with hA
  have hApos : 0 < A := by norm_num
  have hA_nonneg : 0 ≤ A := by norm_num
  have hea_nonneg : 0 ≤ ea := by
    have h := abs_nonneg ((a : ℝ) - A * α)
    linarith
  have heb_nonneg : 0 ≤ eb := by
    have h := abs_nonneg ((b : ℝ) - A * β)
    linarith

  have h_identity : (a : ℝ) * (b : ℝ) / A - A * (α * β) =
      ((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A + α * ((b : ℝ) - A * β) + β * ((a : ℝ) - A * α) := by
    field_simp [hApos.ne']
    ring

  have h_floor : |(fm a b : ℝ) - (a : ℝ) * (b : ℝ) / A| ≤ 1 := by
    have h_low : (fm a b : ℝ) * A ≤ (a : ℝ) * (b : ℝ) := by
      have h := Nat.div_mul_le_self (a * b) (2 ^ 24)
      simpa [fm, hA] using mod_cast h
    have h_high : (a : ℝ) * (b : ℝ) < ((fm a b : ℝ) + 1) * A := by
      have h_mod := Nat.mod_lt (a * b) (by norm_num : 0 < 2 ^ 24)
      have h_div_add_mod := Nat.div_add_mod (a * b) (2 ^ 24)

      have h_eq : ((a : ℝ) * (b : ℝ)) = ((fm a b : ℝ)) * A + ((a * b % 2 ^ 24 : ℕ) : ℝ) := by
        calc
          (a : ℝ) * (b : ℝ) = ((a * b : ℕ) : ℝ) := by simp
          _ = (((2 ^ 24 : ℕ) * ((a * b) / (2 ^ 24) : ℕ) + (a * b) % (2 ^ 24) : ℕ) : ℝ) := by

            have h := congrArg (fun x : ℕ => (x : ℝ)) h_div_add_mod.symm
            simpa using h
          _ = ((2 ^ 24 : ℕ) : ℝ) * (((a * b) / (2 ^ 24) : ℕ) : ℝ) + (((a * b) % (2 ^ 24) : ℕ) : ℝ) := by simp
          _ = A * ((fm a b : ℝ)) + ((a * b % 2 ^ 24 : ℕ) : ℝ) := by
            rw [hA, show ((a * b / 2 ^ 24 : ℕ) : ℝ) = (fm a b : ℝ) by simp [fm],
              show ((2 ^ 24 : ℕ) : ℝ) = (2 ^ 24 : ℝ) by norm_num]
          _ = ((fm a b : ℝ)) * A + ((a * b % 2 ^ 24 : ℕ) : ℝ) := by ring
      have h_mod_lt : ((a * b % 2 ^ 24 : ℕ) : ℝ) < A := by
        simpa [hA] using mod_cast h_mod
      have h_sum_lt : ((fm a b : ℝ)) * A + ((a * b % 2 ^ 24 : ℕ) : ℝ) < ((fm a b : ℝ)) * A + A := by
        linarith
      linarith
    have h_div_low : (fm a b : ℝ) ≤ (a : ℝ) * (b : ℝ) / A := by
      calc
        (fm a b : ℝ) = ((fm a b : ℝ) * A) / A := by field_simp [hApos.ne']
        _ ≤ ((a : ℝ) * (b : ℝ)) / A := div_le_div_of_nonneg_right h_low hA_nonneg
    have h_div_high : (a : ℝ) * (b : ℝ) / A < (fm a b : ℝ) + 1 := by
      calc
        (a : ℝ) * (b : ℝ) / A < (((fm a b : ℝ) + 1) * A) / A :=
          div_lt_div_of_pos_right h_high hApos
        _ = (fm a b : ℝ) + 1 := by field_simp [hApos.ne']
    have h_sub_nonpos : (fm a b : ℝ) - (a : ℝ) * (b : ℝ) / A ≤ 0 := by linarith
    have h_sub_gt_neg_one : -1 < (fm a b : ℝ) - (a : ℝ) * (b : ℝ) / A := by linarith
    rw [abs_of_nonpos h_sub_nonpos]
    linarith

  have h_main : |(a : ℝ) * (b : ℝ) / A - A * (α * β)| ≤ ea + eb + 1 := by
    rw [h_identity]
    calc
      |((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A + α * ((b : ℝ) - A * β) + β * ((a : ℝ) - A * α)|
          ≤ |((a : ℝ) - A * α) * ((b : ℝ) - A * β) / A| + |α * ((b : ℝ) - A * β)| + |β * ((a : ℝ) - A * α)| := by
        apply abs_add_three
      _ = |((a : ℝ) - A * α) * ((b : ℝ) - A * β)| / |A| + |α| * |(b : ℝ) - A * β| + |β| * |(a : ℝ) - A * α| := by
        simp [abs_div, abs_mul]
      _ = |(a : ℝ) - A * α| * |(b : ℝ) - A * β| / A + |α| * |(b : ℝ) - A * β| + |β| * |(a : ℝ) - A * α| := by
        simp [abs_mul, abs_of_nonneg hA_nonneg]
      _ ≤ ea * eb / A + 1 * eb + 1 * ea := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        ·
          refine div_le_div_of_nonneg_right (mul_le_mul ha hb (abs_nonneg _) hea_nonneg) hA_nonneg
        ·
          exact mul_le_mul hα hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        ·
          exact mul_le_mul hβ ha (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ = ea * eb / A + ea + eb := by ring
      _ ≤ 1 + ea + eb := by
        have hdiv : ea * eb / A ≤ 1 := (div_le_one hApos).mpr he
        linarith
      _ = ea + eb + 1 := by ring

  have h_final : |(fm a b : ℝ) - A * (α * β)| ≤ |(fm a b : ℝ) - (a : ℝ) * (b : ℝ) / A| + |(a : ℝ) * (b : ℝ) / A - A * (α * β)| := by
    calc
      |(fm a b : ℝ) - A * (α * β)| = |((fm a b : ℝ) - (a : ℝ) * (b : ℝ) / A) + ((a : ℝ) * (b : ℝ) / A - A * (α * β))| := by
        simp [sub_add_sub_cancel]
      _ ≤ |(fm a b : ℝ) - (a : ℝ) * (b : ℝ) / A| + |(a : ℝ) * (b : ℝ) / A - A * (α * β)| := abs_add_le _ _

  apply le_trans h_final
  have h_sum := add_le_add h_floor h_main
  linarith

theorem D3Q2A0.flag_sound (Lt Rt m : ℕ) (L R eL eR : ℝ) (hL : |(Lt : ℝ) - 2 ^ 24 * L| ≤ eL)
    (hR : |(Rt : ℝ) - 2 ^ 24 * R| ≤ eR) (hm : eL + eR ≤ m) (h : Lt + m < Rt) : L < R := by
  have hL_abs := (abs_le.mp hL)
  have hR_abs := (abs_le.mp hR)
  rcases hL_abs with ⟨hL_left, hL_right⟩
  rcases hR_abs with ⟨hR_left, hR_right⟩

  have h1 : (2 : ℝ) ^ 24 * L ≤ (Lt : ℝ) + eL := by linarith

  have h2 : (Rt : ℝ) - eR ≤ (2 : ℝ) ^ 24 * R := by linarith

  have hm_real : eL + eR ≤ (m : ℝ) := by exact_mod_cast hm
  have h_real : (Lt : ℝ) + (m : ℝ) < (Rt : ℝ) := by exact_mod_cast h

  have h_chain : (2 : ℝ) ^ 24 * L < (2 : ℝ) ^ 24 * R := by
    have h_eL_le : eL ≤ (m : ℝ) - eR := by linarith
    have h3 : (Lt : ℝ) + eL ≤ (Lt : ℝ) + (m : ℝ) - eR := by linarith
    have h4 : (Lt : ℝ) + (m : ℝ) - eR < (Rt : ℝ) - eR := by linarith
    linarith

  exact lt_of_mul_lt_mul_left h_chain (by positivity)

theorem D3Q2A0.pi24_bounds : (52707178.53 : ℝ) < π * 2 ^ 24 ∧ π * 2 ^ 24 < 52707178.54 := by
  have h2 : (2 ^ 24 : ℝ) = 16777216 := by norm_num
  constructor
  · nlinarith [Real.pi_gt_d20, h2]
  · nlinarith [Real.pi_lt_d20, h2]

theorem D3Q2A0.half_sin (a s : ℕ) (e : ℝ)
    (h : |(s : ℝ) - 2 ^ 24 * Real.sin (((a / 2 : ℕ) : ℝ) / 2 ^ 24)| ≤ e) :
    |(s : ℝ) - 2 ^ 24 * Real.sin ((a : ℝ) / 2 ^ 25)| ≤ e + 1 / 2 := by
  set A := (2 ^ 24 : ℝ) with hA
  set k := a / 2 with hk
  have hposA : 0 < A := by
    norm_num [hA]
  have hA_ne_zero : A ≠ 0 := by linarith

  have hk_le_a_nat : (2 * k : ℕ) ≤ a := by
    simpa [hk] using Nat.mul_div_le a 2
  have ha_mod_two : a % 2 ≤ 1 := by
    rcases Nat.mod_two_eq_zero_or_one a with (h | h)
    · rw [h]; exact Nat.zero_le _
    · rw [h]
  have ha_eq_real : (a : ℝ) = (2 * k : ℝ) + ((a % 2 : ℕ) : ℝ) := by
    have h_nat := Nat.div_add_mod a 2

    rw [← hk] at h_nat

    have h_nat' := h_nat.symm
    exact_mod_cast h_nat'
  have ha_le : (a : ℝ) ≤ (2 * k : ℝ) + 1 := by
    have hmod_le' : ((a % 2 : ℕ) : ℝ) ≤ (1 : ℝ) := by exact_mod_cast ha_mod_two
    linarith
  have hk_le_a_real : (2 * k : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast hk_le_a_nat

  have h_diff : |(k : ℝ) / A - (a : ℝ) / (2 * A)| ≤ 1 / (2 * A) := by
    have h_sub_eq : (a : ℝ) / (2 * A) - (k : ℝ) / A = ((a : ℝ) - (2 * k : ℝ)) / (2 * A) := by
      field_simp [hA_ne_zero]
    have h_abs : |(a : ℝ) / (2 * A) - (k : ℝ) / A| ≤ 1 / (2 * A) := by
      rw [h_sub_eq]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2 * A)]
      have h_num : |(a : ℝ) - (2 * k : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have h_den_nonneg : 0 ≤ 2 * A := by linarith
      exact div_le_div_of_nonneg_right h_num h_den_nonneg
    rw [abs_sub_comm]
    exact h_abs

  have h_main : |(s : ℝ) - A * Real.sin ((a : ℝ) / (2 * A))| ≤
      |(s : ℝ) - A * Real.sin ((k : ℝ) / A)| + A * |Real.sin ((k : ℝ) / A) - Real.sin ((a : ℝ) / (2 * A))| := by
    calc
      |(s : ℝ) - A * Real.sin ((a : ℝ) / (2 * A))|
          = |((s : ℝ) - A * Real.sin ((k : ℝ) / A)) + (A * Real.sin ((k : ℝ) / A) - A * Real.sin ((a : ℝ) / (2 * A)))| := by ring
      _ ≤ |(s : ℝ) - A * Real.sin ((k : ℝ) / A)| + |A * Real.sin ((k : ℝ) / A) - A * Real.sin ((a : ℝ) / (2 * A))| :=
        abs_add_le _ _
      _ = |(s : ℝ) - A * Real.sin ((k : ℝ) / A)| + |A * (Real.sin ((k : ℝ) / A) - Real.sin ((a : ℝ) / (2 * A)))| := by ring
      _ = |(s : ℝ) - A * Real.sin ((k : ℝ) / A)| + |A| * |Real.sin ((k : ℝ) / A) - Real.sin ((a : ℝ) / (2 * A))| := by rw [abs_mul]
      _ = |(s : ℝ) - A * Real.sin ((k : ℝ) / A)| + A * |Real.sin ((k : ℝ) / A) - Real.sin ((a : ℝ) / (2 * A))| := by rw [abs_of_pos hposA]

  have h_target_eq : (2 ^ 25 : ℝ) = 2 * A := by
    norm_num [hA]

  calc
    |(s : ℝ) - (2 ^ 24 : ℝ) * Real.sin ((a : ℝ) / (2 ^ 25 : ℝ))|
        = |(s : ℝ) - A * Real.sin ((a : ℝ) / (2 * A))| := by
      norm_num [hA, h_target_eq]
    _ ≤ |(s : ℝ) - A * Real.sin ((k : ℝ) / A)| + A * |Real.sin ((k : ℝ) / A) - Real.sin ((a : ℝ) / (2 * A))| :=
      h_main
    _ ≤ e + A * |Real.sin ((k : ℝ) / A) - Real.sin ((a : ℝ) / (2 * A))| := by
      have h' : |(s : ℝ) - A * Real.sin ((k : ℝ) / A)| ≤ e := by
        simpa [hA, hk, div_div] using h
      nlinarith
    _ ≤ e + A * |(k : ℝ) / A - (a : ℝ) / (2 * A)| := by
      have h_sin := Real.abs_sin_sub_sin_le ((k : ℝ) / A) ((a : ℝ) / (2 * A))
      nlinarith
    _ ≤ e + A * (1 / (2 * A)) := by
      nlinarith
    _ = e + 1 / 2 := by
      field_simp [hA_ne_zero]

theorem D3Q2A0.half_cos (a c : ℕ) (e : ℝ)
    (h : |(c : ℝ) - 2 ^ 24 * abs (Real.cos (((a / 2 : ℕ) : ℝ) / 2 ^ 24))| ≤ e) :
    |(c : ℝ) - 2 ^ 24 * abs (Real.cos ((a : ℝ) / 2 ^ 25))| ≤ e + 1 / 2 := by
  set A := (2 : ℝ) ^ 24 with hA
  set k := a / 2 with hk
  set x := (a : ℝ) / (2 : ℝ) ^ 25 with hx
  set y := (k : ℝ) / (2 : ℝ) ^ 24 with hy
  have hApos : 0 < A := by
    dsimp [A]
    norm_num

  have h_y : abs ((c : ℝ) - A * abs (Real.cos y)) ≤ e := by
    simpa [hk, hy, hA] using h

  have h_triangle : abs ((c : ℝ) - A * abs (Real.cos x)) ≤
      abs ((c : ℝ) - A * abs (Real.cos y)) + abs (A * abs (Real.cos y) - A * abs (Real.cos x)) := by
    calc
      abs ((c : ℝ) - A * abs (Real.cos x)) =
          abs (((c : ℝ) - A * abs (Real.cos y)) + (A * abs (Real.cos y) - A * abs (Real.cos x))) := by ring_nf
      _ ≤ abs ((c : ℝ) - A * abs (Real.cos y)) + abs (A * abs (Real.cos y) - A * abs (Real.cos x)) :=
        abs_add_le _ _

  have h_inner : abs (A * abs (Real.cos y) - A * abs (Real.cos x)) ≤ (1 : ℝ) / 2 := by
    have h_nat_low : k * 2 ≤ a := by
      simpa [hk, mul_comm] using Nat.div_mul_le_self a 2
    have h_nat_high : a ≤ k * 2 + 1 := by
      have h_mod_div := Nat.mod_add_div a 2
      rw [← hk] at h_mod_div
      omega
    have h_low : (k : ℝ) * 2 ≤ (a : ℝ) := by exact_mod_cast h_nat_low
    have h_high : (a : ℝ) ≤ (k : ℝ) * 2 + 1 := by exact_mod_cast h_nat_high
    have h_num_bound : abs ((k : ℝ) * 2 - (a : ℝ)) ≤ 1 := by
      have h_nonpos : (k : ℝ) * 2 - (a : ℝ) ≤ 0 := by linarith
      have h_nonneg : -1 ≤ (k : ℝ) * 2 - (a : ℝ) := by linarith
      rw [abs_le]
      constructor <;> linarith
    have h_diff : y - x = ((k : ℝ) * 2 - (a : ℝ)) / (2 : ℝ) ^ 25 := by
      dsimp [y, x]
      ring_nf
    have h_two_pow_pos : 0 < (2 : ℝ) ^ 25 := by norm_num
    calc
      abs (A * abs (Real.cos y) - A * abs (Real.cos x)) = abs (A * (abs (Real.cos y) - abs (Real.cos x))) := by ring_nf
      _ = abs A * abs (abs (Real.cos y) - abs (Real.cos x)) := by rw [abs_mul]
      _ = A * abs (abs (Real.cos y) - abs (Real.cos x)) := by rw [abs_of_pos hApos]
      _ ≤ A * abs (Real.cos y - Real.cos x) :=
        mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _) (by linarith)
      _ ≤ A * abs (y - x) :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (by linarith)
      _ = A * abs (((k : ℝ) * 2 - (a : ℝ)) / (2 : ℝ) ^ 25) := by rw [h_diff]
      _ = A * (abs ((k : ℝ) * 2 - (a : ℝ)) / abs ((2 : ℝ) ^ 25)) := by rw [abs_div]
      _ = A * (abs ((k : ℝ) * 2 - (a : ℝ)) / ((2 : ℝ) ^ 25)) := by
        rw [abs_of_pos h_two_pow_pos]
      _ ≤ A * (1 / (2 : ℝ) ^ 25) := by
        have h_div : abs ((k : ℝ) * 2 - (a : ℝ)) / ((2 : ℝ) ^ 25) ≤ 1 / ((2 : ℝ) ^ 25) :=
          div_le_div_of_nonneg_right h_num_bound (by linarith)
        exact mul_le_mul_of_nonneg_left h_div (by linarith)
      _ = (1 : ℝ) / 2 := by
        dsimp [A]
        ring_nf

  calc
    abs ((c : ℝ) - A * abs (Real.cos x)) ≤
        abs ((c : ℝ) - A * abs (Real.cos y)) + abs (A * abs (Real.cos y) - A * abs (Real.cos x)) := h_triangle
    _ ≤ e + (1 : ℝ) / 2 :=
      add_le_add h_y h_inner
    _ = e + 1 / 2 := by ring

theorem D3Q2A0.lip_sin (v : ℕ) (θ φ e d : ℝ) (h : |(v : ℝ) - 2 ^ 24 * Real.sin θ| ≤ e) (hd : 2 ^ 24 * |θ - φ| ≤ d) :
    |(v : ℝ) - 2 ^ 24 * Real.sin φ| ≤ e + d := by
  set A := (2 : ℝ) ^ 24 with hA
  have hApos : 0 ≤ A := by
    rw [hA]
    positivity
  calc
    |(v : ℝ) - A * Real.sin φ|
        = |((v : ℝ) - A * Real.sin θ) + (A * Real.sin θ - A * Real.sin φ)| := by ring_nf
    _ ≤ |(v : ℝ) - A * Real.sin θ| + |A * Real.sin θ - A * Real.sin φ| := abs_add_le _ _
    _ = |(v : ℝ) - A * Real.sin θ| + |A * (Real.sin θ - Real.sin φ)| := by ring_nf
    _ = |(v : ℝ) - A * Real.sin θ| + |A| * |Real.sin θ - Real.sin φ| := by rw [abs_mul]
    _ = |(v : ℝ) - A * Real.sin θ| + A * |Real.sin θ - Real.sin φ| := by rw [abs_of_nonneg hApos]
    _ ≤ e + A * |Real.sin θ - Real.sin φ| := by
      nlinarith
    _ ≤ e + A * |θ - φ| := by
      nlinarith [Real.abs_sin_sub_sin_le θ φ]
    _ ≤ e + d := by nlinarith

theorem D3Q2A0.lip_cos (v : ℕ) (θ φ e d : ℝ) (h : |(v : ℝ) - 2 ^ 24 * abs (Real.cos θ)| ≤ e)
    (hd : 2 ^ 24 * |θ - φ| ≤ d) : |(v : ℝ) - 2 ^ 24 * abs (Real.cos φ)| ≤ e + d := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 24 := by norm_num
  set A := (2 : ℝ) ^ 24 with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    positivity
  have h_tri : |(v : ℝ) - A * abs (Real.cos φ)| ≤ |(v : ℝ) - A * abs (Real.cos θ)| + |A * abs (Real.cos θ) - A * abs (Real.cos φ)| := by
    calc
      |(v : ℝ) - A * abs (Real.cos φ)|
          = |((v : ℝ) - A * abs (Real.cos θ)) + (A * abs (Real.cos θ) - A * abs (Real.cos φ))| := by ring
      _ ≤ |(v : ℝ) - A * abs (Real.cos θ)| + |A * abs (Real.cos θ) - A * abs (Real.cos φ)| :=
        abs_add_le _ _
  have h_bound : |A * abs (Real.cos θ) - A * abs (Real.cos φ)| ≤ d := by
    calc
      |A * abs (Real.cos θ) - A * abs (Real.cos φ)|
          = |A * (abs (Real.cos θ) - abs (Real.cos φ))| := by ring
      _ = |A| * |abs (Real.cos θ) - abs (Real.cos φ)| := by rw [abs_mul]
      _ = A * |abs (Real.cos θ) - abs (Real.cos φ)| := by
        rw [abs_of_nonneg hA_nonneg]
      _ ≤ A * |Real.cos θ - Real.cos φ| :=
        mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _) hA_nonneg
      _ ≤ A * |θ - φ| :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) hA_nonneg
      _ ≤ d := hd
  linarith

theorem D3Q2A0.round26 (v : ℕ) : |((((v + 2 ^ 25) / 2 ^ 26 : ℕ)) : ℝ) - (v : ℝ) / 2 ^ 26| ≤ 1 / 2 := by
  set q := ((v + 2 ^ 25) / 2 ^ 26 : ℕ) with hq
  set r := (v + 2 ^ 25) % 2 ^ 26 with hr
  have hdivmod := Nat.div_add_mod (v + 2 ^ 25) (2 ^ 26)
  have hr_lt : r < 2 ^ 26 := Nat.mod_lt (v + 2 ^ 25) (by norm_num : 0 < 2 ^ 26)
  have h_eq : (q : ℝ) - (v : ℝ) / (2 ^ 26 : ℝ) = ((2 ^ 25 : ℝ) - (r : ℝ)) / (2 ^ 26 : ℝ) := by
    have h_v_eq : (v : ℝ) = (2 ^ 26 : ℝ) * (q : ℝ) + (r : ℝ) - (2 ^ 25 : ℝ) := by
      have h := hdivmod
      rw [← hq, ← hr] at h
      have h' : ((2 ^ 26 : ℕ) * q + r : ℝ) = (v + 2 ^ 25 : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    rw [h_v_eq]
    field_simp [show (2 ^ 26 : ℝ) ≠ 0 by norm_num]
    ring
  rw [hq, h_eq]
  have h_num : |(2 ^ 25 : ℝ) - (r : ℝ)| ≤ (2 ^ 25 : ℝ) := by
    have h_low : -(2 ^ 25 : ℝ) ≤ (2 ^ 25 : ℝ) - (r : ℝ) := by
      have : (r : ℝ) ≤ 2 ^ 26 := by exact_mod_cast hr_lt.le
      linarith
    have h_high : (2 ^ 25 : ℝ) - (r : ℝ) ≤ (2 ^ 25 : ℝ) := by
      have : 0 ≤ (r : ℝ) := by exact_mod_cast Nat.zero_le _
      linarith
    exact abs_le.mpr ⟨h_low, h_high⟩
  have h_den_pos : 0 < (2 ^ 26 : ℝ) := by norm_num
  calc
    |((2 ^ 25 : ℝ) - (r : ℝ)) / (2 ^ 26 : ℝ)| = |(2 ^ 25 : ℝ) - (r : ℝ)| / |(2 ^ 26 : ℝ)| := by rw [abs_div]
    _ = |(2 ^ 25 : ℝ) - (r : ℝ)| / (2 ^ 26 : ℝ) := by rw [abs_of_pos h_den_pos]
    _ ≤ (2 ^ 25 : ℝ) / (2 ^ 26 : ℝ) := div_le_div_of_nonneg_right h_num (by norm_num : 0 ≤ (2 ^ 26 : ℝ))
    _ = 1 / 2 := by norm_num

set_option maxHeartbeats 400000 in
theorem D3Q2A0.cosFix_poly (z : ℕ) (hz : z ≤ 13176795) :
    |(cosFix z : ℝ) - 2 ^ 24 * cosT 5 ((z : ℝ) / 2 ^ 24)| ≤ 13 / 4 := by
  have hApos : 0 < (2 : ℝ) ^ 24 := by norm_num
  set t := (z : ℝ) / (2 : ℝ) ^ 24 with ht
  set s := t ^ 2 with hs
  have hz_nonneg : 0 ≤ (z : ℝ) := by exact_mod_cast Nat.zero_le z
  have ht_nonneg : 0 ≤ t := div_nonneg hz_nonneg (by positivity)
  have ht_bound : t ≤ 0.7854 := by
    rw [ht]
    have hz' : (z : ℝ) ≤ 13176795 := by exact_mod_cast hz
    have hineq : (13176795 : ℝ) ≤ 0.7854 * (2 : ℝ) ^ 24 := by norm_num
    have h1 : (z : ℝ) / (2 : ℝ) ^ 24 ≤ 13176795 / (2 : ℝ) ^ 24 := by
      have hpos : 0 ≤ ((2 : ℝ) ^ 24)⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hz' hpos
    have h2 : 13176795 / (2 : ℝ) ^ 24 ≤ 0.7854 := by
      calc
        13176795 / (2 : ℝ) ^ 24 = (13176795 : ℝ) * (((2 : ℝ) ^ 24)⁻¹) := by ring
        _ ≤ (0.7854 * (2 : ℝ) ^ 24) * (((2 : ℝ) ^ 24)⁻¹) := by
          have hpos : 0 ≤ ((2 : ℝ) ^ 24)⁻¹ := by positivity
          nlinarith
        _ = 0.7854 := by field_simp [hApos.ne']
    exact h1.trans h2
  have hs_bound : s ≤ 0.617 := by
    dsimp [s]
    have hsq : t ^ 2 ≤ (0.7854 : ℝ) ^ 2 := by nlinarith
    have hcalc : (0.7854 : ℝ) ^ 2 ≤ 0.617 := by norm_num
    linarith
  have hs_abs_bound : |s| ≤ 0.617 := by
    rw [abs_of_nonneg (pow_two_nonneg t)]
    exact hs_bound

  have hz_approx : |(z : ℝ) - (2 : ℝ) ^ 24 * t| ≤ 0 := by
    rw [ht]
    field_simp [hApos.ne']
    simp

  set w := fm z z with hw_def
  have hw_bound : |(w : ℝ) - (2 : ℝ) ^ 24 * s| ≤ 1 := by
    rw [hw_def]
    have := D3Q2A0.fm_approx z z t t 0 0 (0.7854 : ℝ) (0.7854 : ℝ)
      (by rw [abs_of_nonneg ht_nonneg]; exact ht_bound)
      (by rw [abs_of_nonneg ht_nonneg]; exact ht_bound)
      hz_approx hz_approx
    simpa [hs, sq] using this
  have hw_nat_le : w ≤ 10349197 := by
    rw [hw_def]
    unfold fm
    have hsq : z * z ≤ 13176795 * 13176795 := Nat.mul_le_mul hz hz
    have hcalc : (13176795 * 13176795) / (2 ^ 24) ≤ 10349197 := by norm_num
    have hdiv : (z * z) / (2 ^ 24) ≤ (13176795 * 13176795) / (2 ^ 24) :=
      Nat.div_le_div_right hsq
    exact Nat.le_trans hdiv hcalc

  have h416_bound : |(416 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 40320)| ≤ 0.11 := by
    have hcalc : -0.11 ≤ (416 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 40320) ∧
        (416 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 40320) ≤ 0.11 := by norm_num
    rcases hcalc with ⟨h1, h2⟩
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  set q4 := fm w 416 with hq4_def
  have hq4_bound : |(q4 : ℝ) - (2 : ℝ) ^ 24 * (s / 40320)| ≤ 1.07 := by
    rw [hq4_def]
    have hβm : |(1 : ℝ) / 40320| ≤ (1 : ℝ) / 40320 := by
      rw [abs_of_pos (by norm_num : 0 < (1 : ℝ) / 40320)]
    have htmp := D3Q2A0.fm_approx w 416 s ((1 : ℝ) / 40320) 1 (0.11 : ℝ) (0.617 : ℝ) ((1 : ℝ) / 40320)
      hs_abs_bound (by
        rw [abs_of_pos (by norm_num : 0 < (1 : ℝ) / 40320)])
      hw_bound h416_bound
    have hcalc : (0.617 : ℝ) * (0.11 : ℝ) + ((1 : ℝ) / 40320) * (1 : ℝ) +
        (1 : ℝ) * (0.11 : ℝ) / (2 : ℝ) ^ 24 + 1 ≤ 1.07 := by norm_num
    have htmp' : |(fm w 416 : ℝ) - (2 : ℝ) ^ 24 * (s / 40320)| ≤
        (0.617 : ℝ) * (0.11 : ℝ) + ((1 : ℝ) / 40320) * (1 : ℝ) +
        (1 : ℝ) * (0.11 : ℝ) / (2 : ℝ) ^ 24 + 1 := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htmp
    linarith [htmp', hcalc]
  have hq4_nat_le : q4 ≤ 23302 := by
    rw [hq4_def]
    unfold fm
    have hwq : w * 416 ≤ 10349197 * 416 := Nat.mul_le_mul hw_nat_le (by rfl)
    have hcalc : (10349197 * 416) / (2 ^ 24) ≤ 23302 := by norm_num
    have hdiv : (w * 416) / (2 ^ 24) ≤ (10349197 * 416) / (2 ^ 24) :=
      Nat.div_le_div_right hwq
    exact Nat.le_trans hdiv hcalc

  have h23302_bound : |(23302 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 720)| ≤ 0.32 := by
    have hcalc : -0.32 ≤ (23302 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 720) ∧
        (23302 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 720) ≤ 0.32 := by norm_num
    rcases hcalc with ⟨h1, h2⟩
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  set h3 := 23302 - q4 with hh3_def
  have hh3_bound : |(h3 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 720 - s / 40320)| ≤ 1.39 := by
    rw [hh3_def]
    have := D3Q2A0.sub_approx 23302 q4 ((1 : ℝ) / 720) (s / 40320) (0.32 : ℝ) (1.07 : ℝ) hq4_nat_le
      h23302_bound hq4_bound
    have hsum : (0.32 : ℝ) + 1.07 = 1.39 := by norm_num
    rw [hsum] at this
    simpa [sub_sub] using this

  set w2 := fm w h3 with hw2_def
  have hw2_bound : |(w2 : ℝ) - (2 : ℝ) ^ 24 * (s / 720 - s ^ 2 / 40320)| ≤ 1.86 := by
    rw [hw2_def]
    have hβ_bound : |(1 : ℝ) / 720 - s / 40320| ≤ (1 : ℝ) / 720 := by
      have hdiff : (1 : ℝ) / 720 - s / 40320 ≤ (1 : ℝ) / 720 := by
        have : 0 ≤ s / 40320 := div_nonneg (pow_two_nonneg t) (by norm_num)
        linarith
      have hlower : -(1 / 720 : ℝ) ≤ (1 : ℝ) / 720 - s / 40320 := by
        have : s / 40320 ≤ (0.617 : ℝ) / 40320 := by linarith
        nlinarith
      rw [abs_le]
      exact ⟨hlower, hdiff⟩
    have htmp := D3Q2A0.fm_approx w h3 s ((1 : ℝ) / 720 - s / 40320) 1 (1.39 : ℝ) (0.617 : ℝ) ((1 : ℝ) / 720)
      hs_abs_bound hβ_bound hw_bound hh3_bound
    have hcalc : (0.617 : ℝ) * (1.39 : ℝ) + ((1 : ℝ) / 720) * (1 : ℝ) +
        (1 : ℝ) * (1.39 : ℝ) / (2 : ℝ) ^ 24 + 1 ≤ 1.86 := by norm_num
    have htmp' : |(fm w h3 : ℝ) - (2 : ℝ) ^ 24 * (s / 720 - s ^ 2 / 40320)| ≤
        (0.617 : ℝ) * (1.39 : ℝ) + ((1 : ℝ) / 720) * (1 : ℝ) +
        (1 : ℝ) * (1.39 : ℝ) / (2 : ℝ) ^ 24 + 1 := by
      have htmp_lhs : |(fm w h3 : ℝ) - (2 : ℝ) ^ 24 * (s * ((1 : ℝ) / 720 - s / 40320))| =
          |(fm w h3 : ℝ) - (2 : ℝ) ^ 24 * (s / 720 - s ^ 2 / 40320)| := by
        congr 1
        ring
      rw [htmp_lhs] at htmp
      exact htmp
    linarith [htmp', hcalc]

  have h699051_bound : |(699051 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 24)| ≤ 0.34 := by
    have hcalc : -0.34 ≤ (699051 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 24) ∧
        (699051 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 24) ≤ 0.34 := by norm_num
    rcases hcalc with ⟨h1, h2⟩
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hw2_nat_le : w2 ≤ 699051 := by
    rw [hw2_def]
    unfold fm
    have hwh : w * h3 ≤ 10349197 * 699051 := by
      apply Nat.mul_le_mul hw_nat_le
      have : h3 ≤ 23302 := by rw [hh3_def]; exact Nat.sub_le _ _
      exact le_trans this (by norm_num)
    have hcalc : (10349197 * 699051) / (2 ^ 24) ≤ 699051 := by norm_num
    have hdiv : (w * h3) / (2 ^ 24) ≤ (10349197 * 699051) / (2 ^ 24) :=
      Nat.div_le_div_right hwh
    exact Nat.le_trans hdiv hcalc

  set h2 := 699051 - w2 with hh2_def
  have hh2_bound : |(h2 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 24 - (s / 720 - s ^ 2 / 40320))| ≤ 2.2 := by
    rw [hh2_def]
    have := D3Q2A0.sub_approx 699051 w2 ((1 : ℝ) / 24) (s / 720 - s ^ 2 / 40320) (0.34 : ℝ) (1.86 : ℝ) hw2_nat_le
      h699051_bound hw2_bound
    have hsum : (0.34 : ℝ) + 1.86 = 2.2 := by norm_num
    rw [hsum] at this
    simpa [sub_sub] using this

  set w3 := fm w h2 with hw3_def
  have hw3_bound : |(w3 : ℝ) - (2 : ℝ) ^ 24 * (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))| ≤ 2.41 := by
    rw [hw3_def]
    have hβ_bound : |(1 : ℝ) / 24 - (s / 720 - s ^ 2 / 40320)| ≤ (1 : ℝ) / 24 := by
      have hpos : 0 ≤ s / 720 - s ^ 2 / 40320 := by
        have : s / 40320 ≤ (1 : ℝ) / 720 := by nlinarith
        nlinarith
      have hdiff : (1 : ℝ) / 24 - (s / 720 - s ^ 2 / 40320) ≤ (1 : ℝ) / 24 := by linarith
      have hlower : -(1 / 24 : ℝ) ≤ (1 : ℝ) / 24 - (s / 720 - s ^ 2 / 40320) := by
        have hpos' : s / 720 - s ^ 2 / 40320 ≤ (1 : ℝ) / 24 := by nlinarith
        linarith
      rw [abs_le]
      exact ⟨hlower, hdiff⟩
    have htmp := D3Q2A0.fm_approx w h2 s ((1 : ℝ) / 24 - (s / 720 - s ^ 2 / 40320)) 1 (2.2 : ℝ) (0.617 : ℝ) ((1 : ℝ) / 24)
      hs_abs_bound hβ_bound hw_bound hh2_bound
    have hcalc : (0.617 : ℝ) * (2.2 : ℝ) + ((1 : ℝ) / 24) * (1 : ℝ) +
        (1 : ℝ) * (2.2 : ℝ) / (2 : ℝ) ^ 24 + 1 ≤ 2.41 := by norm_num
    have htmp' : |(fm w h2 : ℝ) - (2 : ℝ) ^ 24 * (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))| ≤
        (0.617 : ℝ) * (2.2 : ℝ) + ((1 : ℝ) / 24) * (1 : ℝ) +
        (1 : ℝ) * (2.2 : ℝ) / (2 : ℝ) ^ 24 + 1 := by
      have htmp_lhs : |(fm w h2 : ℝ) - (2 : ℝ) ^ 24 * (s * ((1 : ℝ) / 24 - (s / 720 - s ^ 2 / 40320)))| =
          |(fm w h2 : ℝ) - (2 : ℝ) ^ 24 * (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))| := by
        congr 1
        ring
      rw [htmp_lhs] at htmp
      exact htmp
    linarith [htmp', hcalc]

  have h8388608_bound : |(8388608 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 2)| ≤ 0 := by
    have : (8388608 : ℝ) = (2 : ℝ) ^ 24 * ((1 : ℝ) / 2) := by norm_num
    rw [this, sub_self, abs_zero]
  have hw3_nat_le : w3 ≤ 8388608 := by
    rw [hw3_def]
    unfold fm
    have hwh : w * h2 ≤ 10349197 * 8388608 := by
      apply Nat.mul_le_mul hw_nat_le
      have : h2 ≤ 699051 := by rw [hh2_def]; exact Nat.sub_le _ _
      exact le_trans this (by norm_num)
    have hcalc : (10349197 * 8388608) / (2 ^ 24) ≤ 8388608 := by norm_num
    have hdiv : (w * h2) / (2 ^ 24) ≤ (10349197 * 8388608) / (2 ^ 24) :=
      Nat.div_le_div_right hwh
    exact Nat.le_trans hdiv hcalc

  set h1 := 8388608 - w3 with hh1_def
  have hh1_bound : |(h1 : ℝ) - (2 : ℝ) ^ 24 * ((1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320)))| ≤ 2.41 := by
    rw [hh1_def]
    have := D3Q2A0.sub_approx 8388608 w3 ((1 : ℝ) / 2) (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320)) (0 : ℝ) (2.41 : ℝ) hw3_nat_le
      h8388608_bound hw3_bound
    have hsum : (0 : ℝ) + 2.41 = 2.41 := by norm_num
    rw [hsum] at this
    simpa [sub_sub] using this

  set w4 := fm w h1 with hw4_def
  have hβ_bound : |(1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))| ≤ (1 : ℝ) / 2 := by
    have hnonneg : 0 ≤ s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320) := by
      have : s / 40320 ≤ (1 : ℝ) / 720 := by nlinarith
      nlinarith
    have hle : s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320) ≤ (1 : ℝ) / 2 := by
      have h1 : s / 24 ≤ (0.617 : ℝ) / 24 := by linarith
      have h2 : (0.617 : ℝ) / 24 ≤ (1 : ℝ) / 2 := by norm_num
      have h3 : -(s ^ 2 / 720 - s ^ 3 / 40320) ≤ 0 := by
        have : s / 40320 ≤ (1 : ℝ) / 720 := by nlinarith
        nlinarith
      linarith
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hw4_bound : |(w4 : ℝ) - (2 : ℝ) ^ 24 * (s * ((1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))))| ≤ 2.99 := by
    rw [hw4_def]
    have htmp := D3Q2A0.fm_approx w h1 s ((1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))) 1 (2.41 : ℝ) (0.617 : ℝ) ((1 : ℝ) / 2)
      hs_abs_bound hβ_bound hw_bound hh1_bound
    have hcalc : (0.617 : ℝ) * (2.41 : ℝ) + ((1 : ℝ) / 2) * (1 : ℝ) +
        (1 : ℝ) * (2.41 : ℝ) / (2 : ℝ) ^ 24 + 1 ≤ 2.99 := by norm_num
    have htmp' : |(fm w h1 : ℝ) - (2 : ℝ) ^ 24 * (s * ((1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))))| ≤
        (0.617 : ℝ) * (2.41 : ℝ) + ((1 : ℝ) / 2) * (1 : ℝ) +
        (1 : ℝ) * (2.41 : ℝ) / (2 : ℝ) ^ 24 + 1 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
    linarith [htmp', hcalc]

  have hcosFix_eq_nat : cosFix z = (16777216 : ℕ) - w4 := by
    simp [cosFix, w4, w, q4, h3, h2, h1, w3, w2]
  have hw4_le : w4 ≤ 16777216 := by

    have : w4 ≤ 8388608 := by
      rw [hw4_def]
      unfold fm
      have hwh : w * h1 ≤ 10349197 * 8388608 := by
        apply Nat.mul_le_mul hw_nat_le
        have : h1 ≤ 8388608 := by rw [hh1_def]; exact Nat.sub_le _ _
        exact le_trans this (by norm_num)
      have hcalc : (10349197 * 8388608) / (2 ^ 24) ≤ 8388608 := by norm_num
      have hdiv : (w * h1) / (2 ^ 24) ≤ (10349197 * 8388608) / (2 ^ 24) :=
        Nat.div_le_div_right hwh
      exact Nat.le_trans hdiv hcalc
    exact le_trans this (by norm_num)
  have hcosFix_eq : (cosFix z : ℝ) = (2 : ℝ) ^ 24 - (w4 : ℝ) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) hcosFix_eq_nat
    rw [Nat.cast_sub hw4_le] at h
    simpa [show (16777216 : ℝ) = (2 : ℝ) ^ 24 by norm_num] using h
  rw [hcosFix_eq]
  have hcosT_expand : cosT 5 t = 1 - s * ((1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))) := by
    unfold cosT
    simp [Finset.sum_range_succ, Nat.factorial, hs]
    ring
  rw [hcosT_expand]
  have hgoal : |((2 : ℝ) ^ 24 - (w4 : ℝ)) - (2 : ℝ) ^ 24 * (1 - s * ((1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))))| =
      |(w4 : ℝ) - (2 : ℝ) ^ 24 * (s * ((1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))))| := by
    have h : ((2 : ℝ) ^ 24 - (w4 : ℝ)) - (2 : ℝ) ^ 24 * (1 - s * ((1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320)))) =
        -((w4 : ℝ) - (2 : ℝ) ^ 24 * (s * ((1 : ℝ) / 2 - (s / 24 - (s ^ 2 / 720 - s ^ 3 / 40320))))) := by
      ring
    rw [h, abs_neg]
  rw [hgoal]
  have hfinal : (2.99 : ℝ) ≤ 13 / 4 := by norm_num
  linarith [hw4_bound, hfinal]

theorem D3Q2A0.sinFix_poly (z : ℕ) (hz : z ≤ 13176795) :
    |(sinFix z : ℝ) - 2 ^ 24 * sinT 5 ((z : ℝ) / 2 ^ 24)| ≤ 7 / 2 := by
  have hApos : (0 : ℝ) < 2 ^ 24 := by norm_num
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (z : ℝ) / 2 ^ 24 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t ≤ 0.7854 := by
    rw [ht, div_le_iff₀ hApos]
    have h1 : (z : ℝ) ≤ 13176795 := by exact_mod_cast hz
    have h2 : (13176795 : ℝ) ≤ 0.7854 * 2 ^ 24 := by norm_num
    linarith
  have hta : |t| ≤ 0.7854 := by rw [abs_of_nonneg ht0]; exact ht1
  have hz0 : |(z : ℝ) - 2 ^ 24 * t| ≤ 0 := by
    rw [ht, mul_div_cancel₀ _ hApos.ne', sub_self, abs_zero]

  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = fm z z := ⟨_, rfl⟩
  obtain ⟨r4, hr4⟩ : ∃ r : ℕ, r = fm w 46 := ⟨_, rfl⟩
  obtain ⟨g3, hg3⟩ : ∃ g : ℕ, g = 3329 - r4 := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ q : ℕ, q = fm w g3 := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g : ℕ, g = 139810 - q3 := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q : ℕ, q = fm w g2 := ⟨_, rfl⟩
  obtain ⟨g1, hg1⟩ : ∃ g : ℕ, g = 2796203 - q2 := ⟨_, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ q : ℕ, q = fm w g1 := ⟨_, rfl⟩
  obtain ⟨g0, hg0⟩ : ∃ g : ℕ, g = 16777216 - q1 := ⟨_, rfl⟩
  have hsf : sinFix z = fm z g0 := by
    rw [hg0, hq1, hg1, hq2, hg2, hq3, hg3, hr4, hw]; rfl

  have hfmle : ∀ a b A B : ℕ, a ≤ A → b ≤ B → fm a b ≤ A * B / 2 ^ 24 :=
    fun a b A B ha hb => Nat.div_le_div_right (Nat.mul_le_mul ha hb)
  have hwle : w ≤ 10349197 := by
    rw [hw]; exact (hfmle _ _ _ _ hz hz).trans (by norm_num)
  have hr4le : r4 ≤ 3329 := by
    rw [hr4]; exact (hfmle _ _ _ _ hwle (le_refl 46)).trans (by norm_num)
  have hg3le : g3 ≤ 3329 := by rw [hg3]; exact Nat.sub_le _ _
  have hq3le : q3 ≤ 139810 := by
    rw [hq3]; exact (hfmle _ _ _ _ hwle hg3le).trans (by norm_num)
  have hg2le : g2 ≤ 139810 := by rw [hg2]; exact Nat.sub_le _ _
  have hq2le : q2 ≤ 2796203 := by
    rw [hq2]; exact (hfmle _ _ _ _ hwle hg2le).trans (by norm_num)
  have hg1le : g1 ≤ 2796203 := by rw [hg1]; exact Nat.sub_le _ _
  have hq1le : q1 ≤ 16777216 := by
    rw [hq1]; exact (hfmle _ _ _ _ hwle hg1le).trans (by norm_num)

  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = t * t := ⟨_, rfl⟩
  obtain ⟨p4, hp4⟩ : ∃ p : ℝ, p = 1 / 5040 - s * (1 / 362880) := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ p : ℝ, p = 1 / 120 - s * p4 := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ p : ℝ, p = 1 / 6 - s * p3 := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ p : ℝ, p = 1 - s * p2 := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact mul_self_nonneg t
  have hs1 : s ≤ 0.617 := by
    have h := mul_le_mul ht1 ht1 ht0 (by norm_num : (0 : ℝ) ≤ 0.7854)
    rw [hs]; linarith
  have hsa : |s| ≤ 0.617 := by rw [abs_of_nonneg hs0]; exact hs1
  have hp4l : 0 ≤ p4 := by rw [hp4]; linarith
  have hp4u : p4 ≤ 1 / 5040 := by rw [hp4]; linarith
  have hsp4 : s * p4 ≤ 0.617 * (1 / 5040) := mul_le_mul hs1 hp4u hp4l (by norm_num)
  have hsp4' : 0 ≤ s * p4 := mul_nonneg hs0 hp4l
  have hp3l : 0 ≤ p3 := by rw [hp3]; linarith
  have hp3u : p3 ≤ 1 / 120 := by rw [hp3]; linarith
  have hsp3 : s * p3 ≤ 0.617 * (1 / 120) := mul_le_mul hs1 hp3u hp3l (by norm_num)
  have hsp3' : 0 ≤ s * p3 := mul_nonneg hs0 hp3l
  have hp2l : 0 ≤ p2 := by rw [hp2]; linarith
  have hp2u : p2 ≤ 1 / 6 := by rw [hp2]; linarith
  have hsp2 : s * p2 ≤ 0.617 * (1 / 6) := mul_le_mul hs1 hp2u hp2l (by norm_num)
  have hsp2' : 0 ≤ s * p2 := mul_nonneg hs0 hp2l
  have hp1l : 0 ≤ p1 := by rw [hp1]; linarith
  have hp1u : p1 ≤ 1 := by rw [hp1]; linarith
  have hb4 : |(1 : ℝ) / 362880| ≤ 1 / 362880 := by rw [abs_of_pos (by norm_num)]
  have hp4a : |p4| ≤ 1 / 5040 := abs_le.mpr ⟨by linarith, hp4u⟩
  have hp3a : |p3| ≤ 1 / 120 := abs_le.mpr ⟨by linarith, hp3u⟩
  have hp2a : |p2| ≤ 1 / 6 := abs_le.mpr ⟨by linarith, hp2u⟩
  have hp1a : |p1| ≤ 1 := abs_le.mpr ⟨by linarith, hp1u⟩

  have hc46 : |((46 : ℕ) : ℝ) - 2 ^ 24 * (1 / 362880)| ≤ 0.24 := by
    rw [abs_le]; constructor <;> norm_num
  have hc3 : |((3329 : ℕ) : ℝ) - 2 ^ 24 * (1 / 5040)| ≤ 0.19 := by
    rw [abs_le]; constructor <;> norm_num
  have hc2 : |((139810 : ℕ) : ℝ) - 2 ^ 24 * (1 / 120)| ≤ 0.14 := by
    rw [abs_le]; constructor <;> norm_num
  have hc1 : |((2796203 : ℕ) : ℝ) - 2 ^ 24 * (1 / 6)| ≤ 0.34 := by
    rw [abs_le]; constructor <;> norm_num
  have hc0 : |((16777216 : ℕ) : ℝ) - 2 ^ 24 * 1| ≤ 0 := by norm_num

  have ew : |(w : ℝ) - 2 ^ 24 * s| ≤ 1 := by
    rw [hw, hs]
    exact le_trans (fm_approx z z t t 0 0 0.7854 0.7854 hta hta hz0 hz0) (by norm_num)
  have e4 : |(r4 : ℝ) - 2 ^ 24 * (s * (1 / 362880))| ≤ 1.15 := by
    rw [hr4]
    exact le_trans (fm_approx w 46 s (1 / 362880) 1 0.24 0.617 (1 / 362880) hsa hb4 ew hc46)
      (by norm_num)
  have e3 : |(g3 : ℝ) - 2 ^ 24 * p4| ≤ 1.34 := by
    rw [hg3, hp4]
    exact le_trans (sub_approx 3329 r4 (1 / 5040) (s * (1 / 362880)) 0.19 1.15 hr4le hc3 e4)
      (by norm_num)
  have f3 : |(q3 : ℝ) - 2 ^ 24 * (s * p4)| ≤ 1.83 := by
    rw [hq3]
    exact le_trans (fm_approx w g3 s p4 1 1.34 0.617 (1 / 5040) hsa hp4a ew e3) (by norm_num)
  have e2 : |(g2 : ℝ) - 2 ^ 24 * p3| ≤ 1.97 := by
    rw [hg2, hp3]
    exact le_trans (sub_approx 139810 q3 (1 / 120) (s * p4) 0.14 1.83 hq3le hc2 f3) (by norm_num)
  have f2 : |(q2 : ℝ) - 2 ^ 24 * (s * p3)| ≤ 2.23 := by
    rw [hq2]
    exact le_trans (fm_approx w g2 s p3 1 1.97 0.617 (1 / 120) hsa hp3a ew e2) (by norm_num)
  have e1 : |(g1 : ℝ) - 2 ^ 24 * p2| ≤ 2.57 := by
    rw [hg1, hp2]
    exact le_trans (sub_approx 2796203 q2 (1 / 6) (s * p3) 0.34 2.23 hq2le hc1 f2) (by norm_num)
  have f1 : |(q1 : ℝ) - 2 ^ 24 * (s * p2)| ≤ 2.76 := by
    rw [hq1]
    exact le_trans (fm_approx w g1 s p2 1 2.57 0.617 (1 / 6) hsa hp2a ew e1) (by norm_num)
  have e0 : |(g0 : ℝ) - 2 ^ 24 * p1| ≤ 2.76 := by
    rw [hg0, hp1]
    exact le_trans (sub_approx 16777216 q1 1 (s * p2) 0 2.76 hq1le hc0 f1) (by norm_num)
  have ef : |(fm z g0 : ℝ) - 2 ^ 24 * (t * p1)| ≤ 7 / 2 :=
    le_trans (fm_approx z g0 t p1 0 2.76 0.7854 1 hta hp1a hz0 e0) (by norm_num)

  have hsinT : sinT 5 t = t * p1 := by
    rw [hp1, hp2, hp3, hp4, hs]
    simp only [sinT, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
    ring
  rw [← ht, hsf, hsinT]
  exact ef

theorem D3Q2A0.cosFix_err (z : ℕ) (hz : z ≤ 13176795) :
    |(cosFix z : ℝ) - 2 ^ 24 * Real.cos ((z : ℝ) / 2 ^ 24)| ≤ 37 / 10 := by
  set A := (2 ^ 24 : ℝ) with hA
  set t := (z : ℝ) / A with ht
  have hApos : 0 < A := by norm_num [hA]
  have ht_nonneg : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hz' : (z : ℝ) ≤ 13176795 := by exact_mod_cast hz
  have ht_bound : t ≤ (13176795 : ℝ) / A := by
    rw [ht]
    exact div_le_div_of_nonneg_right hz' (by positivity)
  have h_cosFix_poly : |(cosFix z : ℝ) - A * cosT 5 t| ≤ 13/4 := by
    simpa [hA, ht] using D3Q2A0.cosFix_poly z hz
  have h_cos_sub : |Real.cos t - cosT 5 t| ≤ |t| ^ 10 / ((10 : ℕ).factorial : ℝ) := by
    simpa using abs_cos_sub_cosT_le 5 t
  have h_abs_t : |t| = t := abs_of_nonneg ht_nonneg
  have h_rem : A * (t ^ 10 / ((10 : ℕ).factorial : ℝ)) ≤ 42/100 := by
    have h_pow : t ^ 10 ≤ ((13176795 : ℝ) / A) ^ 10 :=
      pow_le_pow_left₀ ht_nonneg ht_bound 10
    have h_div : t ^ 10 / ((10 : ℕ).factorial : ℝ) ≤ ((13176795 : ℝ) / A) ^ 10 / ((10 : ℕ).factorial : ℝ) :=
      div_le_div_of_nonneg_right h_pow (by positivity)
    calc
      A * (t ^ 10 / ((10 : ℕ).factorial : ℝ)) ≤ A * (((13176795 : ℝ) / A) ^ 10 / ((10 : ℕ).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h_div (by positivity)
      _ ≤ 42/100 := by norm_num [hA]
  calc
    |(cosFix z : ℝ) - 2 ^ 24 * Real.cos ((z : ℝ) / 2 ^ 24)|
        = |(cosFix z : ℝ) - A * Real.cos t| := by
      simp [hA, ht]
    _ = |((cosFix z : ℝ) - A * cosT 5 t) + A * (cosT 5 t - Real.cos t)| := by ring
    _ ≤ |(cosFix z : ℝ) - A * cosT 5 t| + |A * (cosT 5 t - Real.cos t)| := abs_add_le _ _
    _ = |(cosFix z : ℝ) - A * cosT 5 t| + |A| * |cosT 5 t - Real.cos t| := by rw [abs_mul]
    _ = |(cosFix z : ℝ) - A * cosT 5 t| + A * |cosT 5 t - Real.cos t| := by rw [abs_of_pos hApos]
    _ = |(cosFix z : ℝ) - A * cosT 5 t| + A * |Real.cos t - cosT 5 t| := by
      rw [abs_sub_comm (cosT 5 t) (Real.cos t)]
    _ ≤ 13/4 + A * (|t| ^ 10 / ((10 : ℕ).factorial : ℝ)) := by
      have hsum := add_le_add h_cosFix_poly (mul_le_mul_of_nonneg_left h_cos_sub (by positivity))
      exact hsum
    _ = 13/4 + A * (t ^ 10 / ((10 : ℕ).factorial : ℝ)) := by rw [h_abs_t]
    _ ≤ 13/4 + 42/100 := by nlinarith
    _ ≤ 37/10 := by norm_num

theorem D3Q2A0.sinFix_err (z : ℕ) (hz : z ≤ 13176795) :
    |(sinFix z : ℝ) - 2 ^ 24 * Real.sin ((z : ℝ) / 2 ^ 24)| ≤ 37 / 10 := by
  set A := (2 ^ 24 : ℝ) with hA
  set t := (z : ℝ) / A with ht
  have hApos : 0 < A := by norm_num
  have hA_nonneg : 0 ≤ A := by norm_num
  have ht_nonneg : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hA_nonneg
  have htz : t ≤ 13176795 / A :=
    div_le_div_of_nonneg_right (by exact_mod_cast hz) hA_nonneg
  have ht_bound : t ≤ 0.786 := by
    have h : (13176795 : ℝ) / A ≤ 0.786 := by norm_num
    exact le_trans htz h
  have h_sinFix_poly : |(sinFix z : ℝ) - A * sinT 5 t| ≤ 7/2 := by
    simpa [hA, ht] using sinFix_poly z hz
  have h_sinT_bound : |Real.sin t - sinT 5 t| ≤ |t| ^ 11 / ((11 : ℕ).factorial : ℝ) := by
    have := abs_sin_sub_sinT_le 5 t
    simpa [show (2*5+1 : ℕ) = 11 by norm_num] using this
  have h_t_bound_pow : |t| ^ 11 ≤ (0.786 : ℝ) ^ 11 := by
    rw [abs_of_nonneg ht_nonneg]
    gcongr
  have h_main_bound : A * |Real.sin t - sinT 5 t| ≤ 1/10 := by
    calc
      A * |Real.sin t - sinT 5 t| ≤ A * (|t| ^ 11 / ((11 : ℕ).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h_sinT_bound hA_nonneg
      _ = (A / ((11 : ℕ).factorial : ℝ)) * |t| ^ 11 := by ring
      _ ≤ (A / ((11 : ℕ).factorial : ℝ)) * (0.786 : ℝ) ^ 11 :=
        mul_le_mul_of_nonneg_left h_t_bound_pow (by positivity)
      _ ≤ 1/10 := by norm_num
  calc
    |(sinFix z : ℝ) - 2 ^ 24 * Real.sin ((z : ℝ) / 2 ^ 24)|
        = |(sinFix z : ℝ) - A * Real.sin t| := by simp [hA, ht]
    _ = |((sinFix z : ℝ) - A * sinT 5 t) + (A * sinT 5 t - A * Real.sin t)| := by ring
    _ ≤ |(sinFix z : ℝ) - A * sinT 5 t| + |A * sinT 5 t - A * Real.sin t| := abs_add_le _ _
    _ = |(sinFix z : ℝ) - A * sinT 5 t| + |A * (sinT 5 t - Real.sin t)| := by ring
    _ = |(sinFix z : ℝ) - A * sinT 5 t| + |A| * |sinT 5 t - Real.sin t| := by rw [abs_mul]
    _ = |(sinFix z : ℝ) - A * sinT 5 t| + A * |sinT 5 t - Real.sin t| := by
      rw [abs_of_nonneg hA_nonneg]
    _ = |(sinFix z : ℝ) - A * sinT 5 t| + A * |Real.sin t - sinT 5 t| := by
      rw [abs_sub_comm (sinT 5 t) (Real.sin t)]
    _ ≤ 7/2 + A * |Real.sin t - sinT 5 t| := add_le_add_left h_sinFix_poly _
    _ ≤ 7/2 + 1/10 := by
      have h := add_le_add_right h_main_bound (7/2)
      simpa [add_comm] using h
    _ ≤ 37 / 10 := by norm_num

set_option maxHeartbeats 400000 in
theorem D3Q2A0.sincos24o_err (x0 : ℕ) (h : x0 ≤ 52707179) :
    |((sincos24o x0).1 : ℝ) - 2 ^ 24 * Real.sin ((x0 : ℝ) / 2 ^ 24)| ≤ 9 / 2 ∧
    |((sincos24o x0).2.1 : ℝ) - 2 ^ 24 * abs (Real.cos ((x0 : ℝ) / 2 ^ 24))| ≤ 9 / 2 := by
  have hpi24 := D3Q2A0.pi24_bounds
  rcases hpi24 with ⟨hpi24l, hpi24u⟩
  set A := (2 ^ 24 : ℝ) with hAdef
  have hApos : 0 < A := by norm_num [hAdef]
  have hx0_le : (x0 : ℝ) ≤ 52707179 := by exact_mod_cast h

  have h_lip_cos (a b : ℝ) : |cos a - cos b| ≤ |a - b| := abs_cos_sub_cos_le a b
  have h_lip_sin (a b : ℝ) : |sin a - sin b| ≤ |a - b| := abs_sin_sub_sin_le a b

  have ho1_abs : |(52707179 : ℝ) - π * A| < 0.47 := by
    have hlow : -(0.47 : ℝ) < (52707179 : ℝ) - π * A := by linarith
    have hhigh : (52707179 : ℝ) - π * A < 0.47 := by linarith
    exact abs_lt.mpr ⟨hlow, hhigh⟩
  have ho2_abs : |(26353589 : ℝ) - (π * A) / 2| < 0.27 := by
    have hlow : -(0.27 : ℝ) < (26353589 : ℝ) - (π * A) / 2 := by linarith
    have hhigh : (26353589 : ℝ) - (π * A) / 2 < 0.27 := by linarith
    exact abs_lt.mpr ⟨hlow, hhigh⟩
  have h37_10_lt_9_2 : (37/10 : ℝ) ≤ 9/2 := by norm_num

  by_cases hH : (26353589 : ℕ) < x0
  ·
    by_cases hQ : (13176794 : ℕ) < 52707179 - x0
    ·
      have hx0_lt : x0 < 39530385 := by omega
      have hz_le : 26353589 - (52707179 - x0) ≤ 13176795 := by omega
      unfold sincos24o
      simp [hH, hQ]

      set z := 26353589 - (52707179 - x0) with hz_def
      have hx0_le_52707179 : x0 ≤ 52707179 := h
      have hx0_le_39530384 : x0 ≤ 39530384 := by omega
      have hz_cast : (z : ℝ) = (26353589 : ℝ) - ((52707179 : ℝ) - (x0 : ℝ)) := by
        rw [hz_def]
        have h_sub1 : 52707179 - x0 ≤ 52707179 := Nat.sub_le _ _
        have h_sub2 : 52707179 - x0 ≤ 26353589 := by omega
        simp [Nat.cast_sub hx0_le_52707179, Nat.cast_sub h_sub2]
      have h_cos_err := D3Q2A0.cosFix_err z hz_le
      have h_sin_err := D3Q2A0.sinFix_err z hz_le

      have hz_div_A_eq : (z : ℝ) / A = ((x0 : ℝ) / A - π / 2) + (((26353589 : ℝ) - (π * A) / 2) - ((52707179 : ℝ) - π * A)) / A := by
        rw [hz_cast]
        field_simp [ne_of_gt hApos]
        ring
      have h_diff_bound : A * |(z : ℝ) / A - ((x0 : ℝ) / A - π / 2)| < 0.74 := by
        rw [hz_div_A_eq]
        have : (((x0 : ℝ) / A - π / 2) + (((26353589 : ℝ) - (π * A) / 2) - ((52707179 : ℝ) - π * A)) / A) - ((x0 : ℝ) / A - π / 2) =
            (((26353589 : ℝ) - (π * A) / 2) - ((52707179 : ℝ) - π * A)) / A := by ring
        rw [this]
        rw [abs_div, abs_of_pos hApos]
        have : A * (|((26353589 : ℝ) - (π * A) / 2) - ((52707179 : ℝ) - π * A)| / A) = |((26353589 : ℝ) - (π * A) / 2) - ((52707179 : ℝ) - π * A)| := by
          field_simp [ne_of_gt hApos]
        rw [this]

        have h_o1 : |(52707179 : ℝ) - π * A| < 0.47 := ho1_abs
        have h_o2 : |(26353589 : ℝ) - (π * A) / 2| < 0.27 := ho2_abs
        have h_diff : |((26353589 : ℝ) - (π * A) / 2) - ((52707179 : ℝ) - π * A)| ≤
            |(26353589 : ℝ) - (π * A) / 2| + |(52707179 : ℝ) - π * A| := abs_sub _ _
        linarith
      have h_triangle_cos (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
        calc
          |a - c| = |(a - b) + (b - c)| := by ring
          _ ≤ |a - b| + |b - c| := abs_add_le _ _
      have h_triangle_sin (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
        calc
          |a - c| = |(a - b) + (b - c)| := by ring
          _ ≤ |a - b| + |b - c| := abs_add_le _ _

      have h_cos_neg : cos ((x0 : ℝ) / A) < 0 := by
        have hx0_gt_H : (26353589 : ℝ) < (x0 : ℝ) := by exact_mod_cast hH

        have h_lower : π / 2 < (x0 : ℝ) / A := by
          have hx0_ge_nat : 26353590 ≤ x0 := by

            omega
          have hx0_ge : (26353590 : ℝ) ≤ (x0 : ℝ) := by exact_mod_cast hx0_ge_nat
          calc
            π / 2 = (π * A) / (2 * A) := by field_simp [ne_of_gt hApos]
            _ < (26353590 : ℝ) * 2 / (2 * A) := by
              have hpos : 0 < 2 * A := by positivity
              field_simp [ne_of_gt hpos]
              linarith
            _ = (26353590 : ℝ) / A := by ring
            _ ≤ (x0 : ℝ) / A := by gcongr

        have h_upper : (x0 : ℝ) / A < π + π / 2 := by
          calc
            (x0 : ℝ) / A < 39530385 / A := by
              gcongr
              exact_mod_cast hx0_lt
            _ = π + ((39530385 : ℝ) - π * A) / A := by
              field_simp [ne_of_gt hApos]
              ring
            _ < π + 0.47 / A := by
              gcongr

              have : (39530385 : ℝ) - π * A < (52707179 : ℝ) - π * A := by linarith
              have h_o1_lt : (52707179 : ℝ) - π * A < 0.47 := by
                rcases abs_lt.mp ho1_abs with ⟨_, hr⟩
                exact hr
              linarith
            _ < π + π / 2 := by
              have hpi_pos : 0 < π := pi_pos
              have hApos' : 0 < A := hApos
              nlinarith

        exact Real.cos_neg_of_pi_div_two_lt_of_lt h_lower h_upper
      constructor
      ·
        have h_sin_eq : Real.sin ((x0 : ℝ) / A) = cos ((x0 : ℝ) / A - π / 2) := by

          calc
            Real.sin ((x0 : ℝ) / A) = cos (π / 2 - (x0 : ℝ) / A) := (Real.cos_pi_div_two_sub _).symm
            _ = cos (-((x0 : ℝ) / A - π / 2)) := by ring
            _ = cos ((x0 : ℝ) / A - π / 2) := by rw [Real.cos_neg]
        rw [h_sin_eq]
        have h_main : |(cosFix z : ℝ) - A * cos ((x0 : ℝ) / A - π / 2)| ≤ 37/10 + 0.74 := by
          calc
            |(cosFix z : ℝ) - A * cos ((x0 : ℝ) / A - π / 2)|
                ≤ |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| + |A * cos ((z : ℝ) / A) - A * cos ((x0 : ℝ) / A - π / 2)| :=
              h_triangle_cos _ _ _
            _ = |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| + |A| * |cos ((z : ℝ) / A) - cos ((x0 : ℝ) / A - π / 2)| := by
              rw [← abs_mul, mul_sub]
            _ = |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| + A * |cos ((z : ℝ) / A) - cos ((x0 : ℝ) / A - π / 2)| := by
              rw [abs_of_pos hApos]
            _ ≤ 37/10 + A * |cos ((z : ℝ) / A) - cos ((x0 : ℝ) / A - π / 2)| := by
              have htemp : |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| ≤ 37/10 := by
                simpa [hAdef] using h_cos_err
              nlinarith
            _ ≤ 37/10 + A * |(z : ℝ) / A - ((x0 : ℝ) / A - π / 2)| := by
              have htemp : |cos ((z : ℝ) / A) - cos ((x0 : ℝ) / A - π / 2)| ≤ |(z : ℝ) / A - ((x0 : ℝ) / A - π / 2)| :=
                h_lip_cos _ _
              nlinarith
            _ ≤ 37/10 + 0.74 := by linarith
        have h_bound : (37/10 + 0.74 : ℝ) ≤ 9/2 := by norm_num
        linarith
      ·
        have h_abs_cos : |cos ((x0 : ℝ) / A)| = -cos ((x0 : ℝ) / A) := abs_of_neg h_cos_neg
        rw [h_abs_cos]
        have h_cos_eq : -cos ((x0 : ℝ) / A) = sin ((x0 : ℝ) / A - π / 2) := by

          rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
          ring
        rw [h_cos_eq]
        have h_main : |(sinFix z : ℝ) - A * sin ((x0 : ℝ) / A - π / 2)| ≤ 37/10 + 0.74 := by
          calc
            |(sinFix z : ℝ) - A * sin ((x0 : ℝ) / A - π / 2)|
                ≤ |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| + |A * sin ((z : ℝ) / A) - A * sin ((x0 : ℝ) / A - π / 2)| :=
              h_triangle_sin _ _ _
            _ = |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| + |A| * |sin ((z : ℝ) / A) - sin ((x0 : ℝ) / A - π / 2)| := by
              rw [← abs_mul, mul_sub]
            _ = |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| + A * |sin ((z : ℝ) / A) - sin ((x0 : ℝ) / A - π / 2)| := by
              rw [abs_of_pos hApos]
            _ ≤ 37/10 + A * |sin ((z : ℝ) / A) - sin ((x0 : ℝ) / A - π / 2)| := by
              have htemp : |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| ≤ 37/10 := by
                simpa [hAdef] using h_sin_err
              nlinarith
            _ ≤ 37/10 + A * |(z : ℝ) / A - ((x0 : ℝ) / A - π / 2)| := by
              have htemp : |sin ((z : ℝ) / A) - sin ((x0 : ℝ) / A - π / 2)| ≤ |(z : ℝ) / A - ((x0 : ℝ) / A - π / 2)| :=
                h_lip_sin _ _
              nlinarith
            _ ≤ 37/10 + 0.74 := by linarith
        have h_bound : (37/10 + 0.74 : ℝ) ≤ 9/2 := by norm_num
        linarith
    ·
      have hz_le : 52707179 - x0 ≤ 13176795 := by omega
      unfold sincos24o
      simp [hH, hQ]
      set z := 52707179 - x0 with hz_def
      have hz_cast : (z : ℝ) = (52707179 : ℝ) - (x0 : ℝ) := by
        rw [hz_def]
        simpa using Nat.cast_sub h
      have h_cos_err := D3Q2A0.cosFix_err z hz_le
      have h_sin_err := D3Q2A0.sinFix_err z hz_le

      have hz_div_A_eq : (z : ℝ) / A = (π - (x0 : ℝ) / A) + ((52707179 : ℝ) - π * A) / A := by
        rw [hz_cast]
        field_simp [ne_of_gt hApos]
        ring
      have h_diff_bound : A * |(z : ℝ) / A - (π - (x0 : ℝ) / A)| < 0.47 := by
        rw [hz_div_A_eq]
        have : ((π - (x0 : ℝ) / A) + ((52707179 : ℝ) - π * A) / A) - (π - (x0 : ℝ) / A) =
            ((52707179 : ℝ) - π * A) / A := by ring
        rw [this]
        rw [abs_div, abs_of_pos hApos]
        have : A * (|(52707179 : ℝ) - π * A| / A) = |(52707179 : ℝ) - π * A| := by
          field_simp [ne_of_gt hApos]
        rw [this]
        exact ho1_abs
      have h_triangle_cos (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
        calc
          |a - c| = |(a - b) + (b - c)| := by ring
          _ ≤ |a - b| + |b - c| := abs_add_le _ _
      have h_triangle_sin (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
        calc
          |a - c| = |(a - b) + (b - c)| := by ring
          _ ≤ |a - b| + |b - c| := abs_add_le _ _

      have h_cos_neg : cos ((x0 : ℝ) / A) < 0 := by
        have hx0_gt_H : (26353589 : ℝ) < (x0 : ℝ) := by exact_mod_cast hH

        have h_lower : π / 2 < (x0 : ℝ) / A := by

          have hx0_ge_nat : 39530385 ≤ x0 := by
            have hz_le' : z ≤ 13176794 := by

              have : z ≤ 13176794 := Nat.le_of_not_lt hQ
              exact this

            omega
          have hx0_ge : (39530385 : ℝ) ≤ (x0 : ℝ) := by exact_mod_cast hx0_ge_nat

          calc
            π / 2 = (π * A) / (2 * A) := by field_simp [ne_of_gt hApos]
            _ < (39530385 : ℝ) * 2 / (2 * A) := by
              have hpos : 0 < 2 * A := by positivity
              field_simp [ne_of_gt hpos]
              linarith
            _ = (39530385 : ℝ) / A := by ring
            _ ≤ (x0 : ℝ) / A := by gcongr

        have h_upper : (x0 : ℝ) / A < π + π / 2 := by
          calc
            (x0 : ℝ) / A ≤ 52707179 / A := by gcongr
            _ = π + ((52707179 : ℝ) - π * A) / A := by
              field_simp [ne_of_gt hApos]
              ring
            _ < π + 0.47 / A := by
              gcongr
              rcases abs_lt.mp ho1_abs with ⟨_, hr⟩
              exact hr
            _ < π + π / 2 := by
              have hpi_pos : 0 < π := pi_pos
              have hApos' : 0 < A := hApos
              nlinarith

        exact Real.cos_neg_of_pi_div_two_lt_of_lt h_lower h_upper
      constructor
      ·
        have h_sin_eq : Real.sin ((x0 : ℝ) / A) = sin (π - (x0 : ℝ) / A) :=
          (Real.sin_pi_sub ((x0 : ℝ) / A)).symm
        rw [h_sin_eq]
        have h_main : |(sinFix z : ℝ) - A * sin (π - (x0 : ℝ) / A)| ≤ 37/10 + 0.47 := by
          calc
            |(sinFix z : ℝ) - A * sin (π - (x0 : ℝ) / A)|
                ≤ |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| + |A * sin ((z : ℝ) / A) - A * sin (π - (x0 : ℝ) / A)| :=
              h_triangle_sin _ _ _
            _ = |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| + |A| * |sin ((z : ℝ) / A) - sin (π - (x0 : ℝ) / A)| := by
              rw [← abs_mul, mul_sub]
            _ = |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| + A * |sin ((z : ℝ) / A) - sin (π - (x0 : ℝ) / A)| := by
              rw [abs_of_pos hApos]
            _ ≤ 37/10 + A * |sin ((z : ℝ) / A) - sin (π - (x0 : ℝ) / A)| := by
              have htemp : |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| ≤ 37/10 := by
                simpa [hAdef] using h_sin_err
              nlinarith
            _ ≤ 37/10 + A * |(z : ℝ) / A - (π - (x0 : ℝ) / A)| := by
              have htemp : |sin ((z : ℝ) / A) - sin (π - (x0 : ℝ) / A)| ≤ |(z : ℝ) / A - (π - (x0 : ℝ) / A)| :=
                h_lip_sin _ _
              nlinarith
            _ ≤ 37/10 + 0.47 := by linarith
        have h_bound : (37/10 + 0.47 : ℝ) ≤ 9/2 := by norm_num
        linarith
      ·
        have h_abs_cos : |cos ((x0 : ℝ) / A)| = -cos ((x0 : ℝ) / A) := abs_of_neg h_cos_neg
        rw [h_abs_cos]
        have h_cos_eq : -cos ((x0 : ℝ) / A) = cos (π - (x0 : ℝ) / A) :=
          (Real.cos_pi_sub ((x0 : ℝ) / A)).symm
        rw [h_cos_eq]
        have h_main : |(cosFix z : ℝ) - A * cos (π - (x0 : ℝ) / A)| ≤ 37/10 + 0.47 := by
          calc
            |(cosFix z : ℝ) - A * cos (π - (x0 : ℝ) / A)|
                ≤ |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| + |A * cos ((z : ℝ) / A) - A * cos (π - (x0 : ℝ) / A)| :=
              h_triangle_cos _ _ _
            _ = |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| + |A| * |cos ((z : ℝ) / A) - cos (π - (x0 : ℝ) / A)| := by
              rw [← abs_mul, mul_sub]
            _ = |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| + A * |cos ((z : ℝ) / A) - cos (π - (x0 : ℝ) / A)| := by
              rw [abs_of_pos hApos]
            _ ≤ 37/10 + A * |cos ((z : ℝ) / A) - cos (π - (x0 : ℝ) / A)| := by
              have htemp : |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| ≤ 37/10 := by
                simpa [hAdef] using h_cos_err
              nlinarith
            _ ≤ 37/10 + A * |(z : ℝ) / A - (π - (x0 : ℝ) / A)| := by
              have htemp : |cos ((z : ℝ) / A) - cos (π - (x0 : ℝ) / A)| ≤ |(z : ℝ) / A - (π - (x0 : ℝ) / A)| :=
                h_lip_cos _ _
              nlinarith
            _ ≤ 37/10 + 0.47 := by linarith
        have h_bound : (37/10 + 0.47 : ℝ) ≤ 9/2 := by norm_num
        linarith
  ·
    by_cases hQ : (13176794 : ℕ) < x0
    ·
      have hz_le : 26353589 - x0 ≤ 13176795 := by omega
      unfold sincos24o
      simp [hH, hQ]
      set z := 26353589 - x0 with hz_def
      have hx0_le_H : x0 ≤ 26353589 := by omega
      have hz_cast : (z : ℝ) = (26353589 : ℝ) - (x0 : ℝ) := by
        rw [hz_def]
        simpa using Nat.cast_sub hx0_le_H
      have h_cos_err := D3Q2A0.cosFix_err z hz_le
      have h_sin_err := D3Q2A0.sinFix_err z hz_le

      have hz_div_A_eq : (z : ℝ) / A = (π / 2 - (x0 : ℝ) / A) + ((26353589 : ℝ) - (π * A) / 2) / A := by
        rw [hz_cast]
        field_simp [ne_of_gt hApos]
        ring
      have h_diff_bound : A * |(z : ℝ) / A - (π / 2 - (x0 : ℝ) / A)| < 0.27 := by
        rw [hz_div_A_eq]
        have : ((π / 2 - (x0 : ℝ) / A) + ((26353589 : ℝ) - (π * A) / 2) / A) - (π / 2 - (x0 : ℝ) / A) =
            ((26353589 : ℝ) - (π * A) / 2) / A := by ring
        rw [this]
        rw [abs_div, abs_of_pos hApos]

        have : A * (|(26353589 : ℝ) - (π * A) / 2| / A) = |(26353589 : ℝ) - (π * A) / 2| := by
          field_simp [ne_of_gt hApos]
        rw [this]
        exact ho2_abs
      have h_triangle_cos (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
        calc
          |a - c| = |(a - b) + (b - c)| := by ring
          _ ≤ |a - b| + |b - c| := abs_add_le _ _
      have h_triangle_sin (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
        calc
          |a - c| = |(a - b) + (b - c)| := by ring
          _ ≤ |a - b| + |b - c| := abs_add_le _ _
      constructor
      ·
        have h_sin_eq : Real.sin ((x0 : ℝ) / A) = cos (π / 2 - (x0 : ℝ) / A) :=
          (Real.cos_pi_div_two_sub ((x0 : ℝ) / A)).symm
        rw [h_sin_eq]
        have h_main : |(cosFix z : ℝ) - A * cos (π / 2 - (x0 : ℝ) / A)| ≤ 37/10 + 0.27 := by
          calc
            |(cosFix z : ℝ) - A * cos (π / 2 - (x0 : ℝ) / A)|
                ≤ |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| + |A * cos ((z : ℝ) / A) - A * cos (π / 2 - (x0 : ℝ) / A)| :=
              h_triangle_cos _ _ _
            _ = |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| + |A| * |cos ((z : ℝ) / A) - cos (π / 2 - (x0 : ℝ) / A)| := by
              rw [← abs_mul, mul_sub]
            _ = |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| + A * |cos ((z : ℝ) / A) - cos (π / 2 - (x0 : ℝ) / A)| := by
              rw [abs_of_pos hApos]
            _ ≤ 37/10 + A * |cos ((z : ℝ) / A) - cos (π / 2 - (x0 : ℝ) / A)| := by
              have htemp : |(cosFix z : ℝ) - A * cos ((z : ℝ) / A)| ≤ 37/10 := by
                simpa [hAdef] using h_cos_err
              nlinarith
            _ ≤ 37/10 + A * |(z : ℝ) / A - (π / 2 - (x0 : ℝ) / A)| := by
              have htemp : |cos ((z : ℝ) / A) - cos (π / 2 - (x0 : ℝ) / A)| ≤ |(z : ℝ) / A - (π / 2 - (x0 : ℝ) / A)| :=
                h_lip_cos _ _
              nlinarith
            _ ≤ 37/10 + 0.27 := by
              linarith
        have h_397_le_45 : (37/10 + 0.27 : ℝ) ≤ 9/2 := by norm_num
        linarith
      ·
        have h_cos_nonneg : 0 ≤ cos ((x0 : ℝ) / A) := by
          have hx0_le_H' : (x0 : ℝ) ≤ 26353589 := by exact_mod_cast hx0_le_H
          have h_lt_pi_div_2 : (x0 : ℝ) / A < π / 2 := by
            calc
              (x0 : ℝ) / A ≤ 26353589 / A := by gcongr
              _ = (52707178 : ℝ) / (2 * A) := by ring
              _ < (π * A) / (2 * A) := by
                gcongr
                linarith
              _ = π / 2 := by field_simp [ne_of_gt hApos]
          have h_neg_pi_div_2_le : -(π / 2) ≤ (x0 : ℝ) / A := by
            have h_nonneg : 0 ≤ (x0 : ℝ) / A := div_nonneg (Nat.cast_nonneg _) (by norm_num [hAdef])
            linarith [pi_pos, h_nonneg]
          exact Real.cos_nonneg_of_mem_Icc ⟨h_neg_pi_div_2_le, le_of_lt h_lt_pi_div_2⟩
        have h_abs_cos : |cos ((x0 : ℝ) / A)| = cos ((x0 : ℝ) / A) := abs_of_nonneg h_cos_nonneg
        rw [h_abs_cos]
        have h_cos_eq : cos ((x0 : ℝ) / A) = sin (π / 2 - (x0 : ℝ) / A) :=
          (Real.sin_pi_div_two_sub ((x0 : ℝ) / A)).symm
        rw [h_cos_eq]
        have h_main : |(sinFix z : ℝ) - A * sin (π / 2 - (x0 : ℝ) / A)| ≤ 37/10 + 0.27 := by
          calc
            |(sinFix z : ℝ) - A * sin (π / 2 - (x0 : ℝ) / A)|
                ≤ |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| + |A * sin ((z : ℝ) / A) - A * sin (π / 2 - (x0 : ℝ) / A)| :=
              h_triangle_sin _ _ _
            _ = |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| + |A| * |sin ((z : ℝ) / A) - sin (π / 2 - (x0 : ℝ) / A)| := by
              rw [← abs_mul, mul_sub]
            _ = |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| + A * |sin ((z : ℝ) / A) - sin (π / 2 - (x0 : ℝ) / A)| := by
              rw [abs_of_pos hApos]
            _ ≤ 37/10 + A * |sin ((z : ℝ) / A) - sin (π / 2 - (x0 : ℝ) / A)| := by
              have htemp : |(sinFix z : ℝ) - A * sin ((z : ℝ) / A)| ≤ 37/10 := by
                simpa [hAdef] using h_sin_err
              nlinarith
            _ ≤ 37/10 + A * |(z : ℝ) / A - (π / 2 - (x0 : ℝ) / A)| := by
              have htemp : |sin ((z : ℝ) / A) - sin (π / 2 - (x0 : ℝ) / A)| ≤ |(z : ℝ) / A - (π / 2 - (x0 : ℝ) / A)| :=
                h_lip_sin _ _
              nlinarith
            _ ≤ 37/10 + 0.27 := by
              linarith
        have h_397_le_45 : (37/10 + 0.27 : ℝ) ≤ 9/2 := by norm_num
        linarith
    ·
      have hQ' : x0 ≤ 13176794 := by omega
      have hz_le : x0 ≤ 13176795 := by omega
      unfold sincos24o
      simp [hH, hQ]

      have h_sin_err := D3Q2A0.sinFix_err x0 hz_le
      have h_cos_err := D3Q2A0.cosFix_err x0 hz_le
      have h_cos_nonneg : 0 ≤ cos ((x0 : ℝ) / A) := by
        have hx0_le_Q : (x0 : ℝ) ≤ 13176794 := by exact_mod_cast hQ'
        have h_nonneg : 0 ≤ (x0 : ℝ) / A := div_nonneg (Nat.cast_nonneg _) (by norm_num [hAdef])
        have h_le_pi_div_2 : (x0 : ℝ) / A ≤ π / 2 := by

          have h_lt : (x0 : ℝ) / A < π / 2 := by
            calc
              (x0 : ℝ) / A ≤ 13176794 / A := by gcongr
              _ = (52707176 : ℝ) / (4 * A) := by ring
              _ < (π * A) / (4 * A) := by
                gcongr
                linarith
              _ = π / 4 := by field_simp [ne_of_gt hApos]
              _ < π / 2 := by linarith [pi_pos]
          exact le_of_lt h_lt
        have h_neg_pi_div_2_le : -(π / 2) ≤ (x0 : ℝ) / A := by
          linarith [pi_pos]
        exact Real.cos_nonneg_of_mem_Icc ⟨h_neg_pi_div_2_le, h_le_pi_div_2⟩
      constructor
      ·
        have : |(sinFix x0 : ℝ) - A * sin ((x0 : ℝ) / A)| ≤ 37/10 := by

          simpa [hAdef] using h_sin_err
        linarith
      ·
        have h_abs_cos : |cos ((x0 : ℝ) / A)| = cos ((x0 : ℝ) / A) := abs_of_nonneg h_cos_nonneg
        have : |(cosFix x0 : ℝ) - A * cos ((x0 : ℝ) / A)| ≤ 37/10 := by
          simpa [hAdef] using h_cos_err
        rw [h_abs_cos]
        linarith

theorem D3Q2A0.sincos24o_sign (x0 : ℕ) (h : x0 ≤ 52707179) :
    (sincos24o x0).2.2 = 1 ↔ Real.cos ((x0 : ℝ) / 2 ^ 24) < 0 := by
  have hsign : (sincos24o x0).2.2 = 1 ↔ 26353589 < x0 := by
    unfold sincos24o
    split_ifs with h1 h2 h3
    · simp [h1]
    · simp [h1]
    · simp [h1]
    · simp [h1]
  rw [hsign]
  constructor
  · intro hx0
    have hx0' : 26353589 < x0 := hx0
    have hx0_nat : 26353590 ≤ x0 := by omega
    have hlower : Real.pi / 2 < (x0 : ℝ) / (2 ^ 24 : ℝ) := by
      have hpi_lt : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
      have hmid : Real.pi / 2 < (26353590 : ℝ) / (2 ^ 24 : ℝ) := by
        nlinarith
      have hx0val : (26353590 : ℝ) ≤ (x0 : ℝ) := by exact_mod_cast hx0_nat
      have hpos : 0 ≤ (2 ^ 24 : ℝ) := by norm_num
      have hright : (26353590 : ℝ) / (2 ^ 24 : ℝ) ≤ (x0 : ℝ) / (2 ^ 24 : ℝ) :=
        div_le_div_of_nonneg_right hx0val hpos
      linarith
    have hupper : (x0 : ℝ) / (2 ^ 24 : ℝ) < Real.pi + Real.pi / 2 := by
      have hx0val : (x0 : ℝ) ≤ 52707179 := by exact_mod_cast h
      have hpi_gt : 3.14159265358979323846 < Real.pi := Real.pi_gt_d20
      have hpi_lt : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
      nlinarith
    exact Real.cos_neg_of_pi_div_two_lt_of_lt hlower hupper
  · intro hcos
    by_contra! hx0
    have hx0val : (x0 : ℝ) ≤ 26353589 := by exact_mod_cast hx0
    have hupper : (x0 : ℝ) / (2 ^ 24 : ℝ) < Real.pi / 2 := by
      have : (26353589 : ℝ) / (2 ^ 24 : ℝ) < Real.pi / 2 := by
        have hpi_gt : 3.14159265358979323846 < Real.pi := Real.pi_gt_d20
        nlinarith
      have hdiv : (x0 : ℝ) / (2 ^ 24 : ℝ) ≤ (26353589 : ℝ) / (2 ^ 24 : ℝ) := by
        apply div_le_div_of_nonneg_right hx0val (by norm_num)
      linarith
    have hpos : -(Real.pi / 2) < (x0 : ℝ) / (2 ^ 24 : ℝ) := by
      have : 0 ≤ (x0 : ℝ) := by exact_mod_cast Nat.zero_le x0
      have hpi_pos : 0 < Real.pi := by exact Real.pi_pos
      nlinarith
    have hcos_pos : 0 < Real.cos ((x0 : ℝ) / (2 ^ 24 : ℝ)) :=
      Real.cos_pos_of_mem_Ioo ⟨hpos, hupper⟩
    linarith

theorem D3Q2A0.flag_lin2 (p q r E : ℕ) (P Q R : ℝ) (hE : E ≤ 64) (hQ : |Q| ≤ 1) (hR : |R| ≤ 1)
    (hp : |(p : ℝ) - 2 ^ 24 * P| ≤ (E : ℝ) + 1) (hq : |(q : ℝ) - 2 ^ 24 * Q| ≤ (E : ℝ))
    (hr : |(r : ℝ) - 2 ^ 24 * R| ≤ (E : ℝ) + 1) (h : p + (3 * E + 4) < fm q r) : P < Q * R := by
  have hE_bound : (E : ℝ) * ((E : ℝ) + 1) ≤ (2 ^ 24 : ℝ) := by
    have hE64 : (E : ℝ) ≤ 64 := by exact_mod_cast hE
    nlinarith
  have h_fm_margin := D3Q2A0.fm_margin q r Q R (E : ℝ) ((E : ℝ) + 1) hQ hR hq hr hE_bound
  have h_fm_simp : |(fm q r : ℝ) - 2 ^ 24 * (Q * R)| ≤ 2 * (E : ℝ) + 3 := by
    linarith
  have h_flag_sound := D3Q2A0.flag_sound p (fm q r) (3 * E + 4) P (Q * R) ((E : ℝ) + 1) (2 * (E : ℝ) + 3)
    hp h_fm_simp (by
      push_cast
      ring_nf
      rfl
    ) h
  exact h_flag_sound

theorem D3Q2A0.flag_prod3 (p q r u v E : ℕ) (P Q R U V : ℝ) (hE : E ≤ 64) (hP : |P| ≤ 1) (hQ : |Q| ≤ 1)
    (hR : |R| ≤ 1) (hU : |U| ≤ 1) (hV : |V| ≤ 1)
    (hp : |(p : ℝ) - 2 ^ 24 * P| ≤ (E : ℝ)) (hq : |(q : ℝ) - 2 ^ 24 * Q| ≤ (E : ℝ))
    (hr : |(r : ℝ) - 2 ^ 24 * R| ≤ (E : ℝ) + 1)
    (hu : |(u : ℝ) - 2 ^ 24 * U| ≤ (E : ℝ)) (hv : |(v : ℝ) - 2 ^ 24 * V| ≤ (E : ℝ) + 1)
    (h : fm (fm p q) r + (5 * E + 8) < fm u v) : P * Q * R < U * V := by
  have hE64 : (E : ℝ) ≤ 64 := by exact_mod_cast hE
  have hE_nonneg : 0 ≤ (E : ℝ) := by exact_mod_cast Nat.zero_le E

  have hEE : (E : ℝ) * (E : ℝ) ≤ (2 : ℝ) ^ 24 := by
    have hsq : (E : ℝ) * (E : ℝ) ≤ (64 : ℝ) * (64 : ℝ) := by
      nlinarith
    have h64sq : (64 : ℝ) * (64 : ℝ) = 4096 := by norm_num
    have h4096 : (4096 : ℝ) ≤ (2 : ℝ) ^ 24 := by norm_num
    linarith
  have h1 : |(fm p q : ℝ) - (2 : ℝ) ^ 24 * (P * Q)| ≤ (E : ℝ) + (E : ℝ) + 2 :=
    fm_margin p q P Q (E : ℝ) (E : ℝ) hP hQ hp hq hEE

  have hPQ_abs : |P * Q| ≤ 1 := by
    calc
      |P * Q| = |P| * |Q| := abs_mul P Q
      _ ≤ 1 * 1 := mul_le_mul hP hQ (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hPQ_R_abs : |P * Q * R| ≤ 1 := by
    calc
      |P * Q * R| = |P * Q| * |R| := abs_mul (P * Q) R
      _ ≤ 1 * 1 := mul_le_mul hPQ_abs hR (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have h2E2_E1 : ((E : ℝ) + (E : ℝ) + 2) * ((E : ℝ) + 1) ≤ (2 : ℝ) ^ 24 := by
    have hE1 : (E : ℝ) + 1 ≤ 65 := by linarith
    have hsq : ((E : ℝ) + 1) * ((E : ℝ) + 1) ≤ (65 : ℝ) * (65 : ℝ) := by
      nlinarith
    have hcalc : ((E : ℝ) + (E : ℝ) + 2) * ((E : ℝ) + 1) = 2 * (((E : ℝ) + 1) * ((E : ℝ) + 1)) := by ring
    rw [hcalc]
    have h65sq : (65 : ℝ) * (65 : ℝ) = 4225 := by norm_num
    have h4225 : (4225 : ℝ) ≤ (2 : ℝ) ^ 24 := by norm_num
    nlinarith
  have h2 : |(fm (fm p q) r : ℝ) - (2 : ℝ) ^ 24 * (P * Q * R)| ≤
      ((E : ℝ) + (E : ℝ) + 2) + ((E : ℝ) + 1) + 2 :=
    fm_margin (fm p q) r (P * Q) R ((E : ℝ) + (E : ℝ) + 2) ((E : ℝ) + 1) hPQ_abs hR h1 hr h2E2_E1
  have h2_final : |(fm (fm p q) r : ℝ) - (2 : ℝ) ^ 24 * (P * Q * R)| ≤ 3 * (E : ℝ) + 5 := by
    linarith

  have hUV_abs : |U * V| ≤ 1 := by
    calc
      |U * V| = |U| * |V| := abs_mul U V
      _ ≤ 1 * 1 := mul_le_mul hU hV (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hE_E1 : (E : ℝ) * ((E : ℝ) + 1) ≤ (2 : ℝ) ^ 24 := by
    have hE1 : (E : ℝ) + 1 ≤ 65 := by linarith
    have hprod : (E : ℝ) * ((E : ℝ) + 1) ≤ (64 : ℝ) * (65 : ℝ) := by
      nlinarith
    have h64_65 : (64 : ℝ) * (65 : ℝ) = 4160 := by norm_num
    have h4160 : (4160 : ℝ) ≤ (2 : ℝ) ^ 24 := by norm_num
    linarith
  have h3 : |(fm u v : ℝ) - (2 : ℝ) ^ 24 * (U * V)| ≤ (E : ℝ) + ((E : ℝ) + 1) + 2 :=
    fm_margin u v U V (E : ℝ) ((E : ℝ) + 1) hU hV hu hv hE_E1
  have h3_final : |(fm u v : ℝ) - (2 : ℝ) ^ 24 * (U * V)| ≤ 2 * (E : ℝ) + 3 := by
    linarith

  have hm : (3 * (E : ℝ) + 5) + (2 * (E : ℝ) + 3) ≤ ((5 * E + 8 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact flag_sound (fm (fm p q) r) (fm u v) (5 * E + 8) (P * Q * R) (U * V) (3 * (E : ℝ) + 5) (2 * (E : ℝ) + 3)
    h2_final h3_final hm h

theorem D3Q2A0.flag_sum (x g e f c1 c2 s k E : ℕ) (X G Se Sf C1 C2 : ℝ) (hE : E ≤ 64) (hk : k ≤ 2) (hs : s ≤ k)
    (hG : |G| ≤ 1) (hSe : |Se| ≤ 1) (hSf : |Sf| ≤ 1) (hC1 : |C1| ≤ 1) (hC2 : |C2| ≤ 1)
    (hx : |(x : ℝ) - 2 ^ 24 * X| ≤ (E : ℝ)) (hg : |(g : ℝ) - 2 ^ 24 * G| ≤ (E : ℝ))
    (he : |(e : ℝ) - 2 ^ 24 * Se| ≤ (E : ℝ)) (hf : |(f : ℝ) - 2 ^ 24 * Sf| ≤ (E : ℝ))
    (hc1 : |(c1 : ℝ) - 2 ^ 24 * C1| ≤ (E : ℝ)) (hc2 : |(c2 : ℝ) - 2 ^ 24 * C2| ≤ (E : ℝ))
    (h : x + s * fm c1 c2 + (2 * k + 6) * (E + 1) < fm g (fm e f) + fm c1 c2) :
    X + s * (C1 * C2) < G * (Se * Sf) + C1 * C2 := by
  set p := fm c1 c2 with hp
  set q := fm e f with hq
  have hE' : (E : ℝ) ≤ 64 := by exact_mod_cast hE
  have hE_sq : (E : ℝ) * (E : ℝ) ≤ (2 ^ 24 : ℝ) := by
    have hE64 : (E : ℝ) ≤ 64 := by exact_mod_cast hE
    have h2pow24 : (2 ^ 24 : ℝ) = 16777216 := by norm_num
    nlinarith
  have hE_2E2 : (E : ℝ) * (2 * (E : ℝ) + 2) ≤ (2 ^ 24 : ℝ) := by
    have hE64 : (E : ℝ) ≤ 64 := by exact_mod_cast hE
    have h2pow24 : (2 ^ 24 : ℝ) = 16777216 := by norm_num
    nlinarith
  have hSeSf : |Se * Sf| ≤ 1 := by
    calc
      |Se * Sf| = |Se| * |Sf| := abs_mul Se Sf
      _ ≤ 1 * 1 := mul_le_mul hSe hSf (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ = 1 := by norm_num
  have hp_bound : |(p : ℝ) - 2 ^ 24 * (C1 * C2)| ≤ (E : ℝ) + (E : ℝ) + 2 := by
    apply D3Q2A0.fm_margin c1 c2 C1 C2 (E : ℝ) (E : ℝ) hC1 hC2 hc1 hc2
    exact hE_sq
  have hq_bound : |(q : ℝ) - 2 ^ 24 * (Se * Sf)| ≤ (E : ℝ) + (E : ℝ) + 2 := by
    apply D3Q2A0.fm_margin e f Se Sf (E : ℝ) (E : ℝ) hSe hSf he hf
    exact hE_sq
  have hgq_bound : |(fm g q : ℝ) - 2 ^ 24 * (G * (Se * Sf))| ≤ (E : ℝ) + ((E : ℝ) + (E : ℝ) + 2) + 2 := by
    refine D3Q2A0.fm_margin g q G (Se * Sf) (E : ℝ) ((E : ℝ) + (E : ℝ) + 2) hG hSeSf hg ?_ ?_
    · exact hq_bound
    · have h_eq : (E : ℝ) * ((E : ℝ) + (E : ℝ) + 2) = (E : ℝ) * (2 * (E : ℝ) + 2) := by ring
      rw [h_eq]
      exact hE_2E2
  have hgq_bound_simp : |(fm g q : ℝ) - 2 ^ 24 * (G * (Se * Sf))| ≤ 3 * (E : ℝ) + 4 := by
    have : (E : ℝ) + ((E : ℝ) + (E : ℝ) + 2) + 2 = 3 * (E : ℝ) + 4 := by ring
    rw [this] at hgq_bound
    exact hgq_bound
  have h_left : |((x + s * p : ℕ) : ℝ) - 2 ^ 24 * (X + (s : ℝ) * (C1 * C2))| ≤ (E : ℝ) + (k : ℝ) * (2 * (E : ℝ) + 2) := by
    push_cast
    have h_eq : (x : ℝ) + (s : ℝ) * (p : ℝ) - 2 ^ 24 * (X + (s : ℝ) * (C1 * C2)) =
        ((x : ℝ) - 2 ^ 24 * X) + (s : ℝ) * ((p : ℝ) - 2 ^ 24 * (C1 * C2)) := by
      ring
    rw [h_eq]
    calc
      |((x : ℝ) - 2 ^ 24 * X) + (s : ℝ) * ((p : ℝ) - 2 ^ 24 * (C1 * C2))| ≤
          |(x : ℝ) - 2 ^ 24 * X| + |(s : ℝ) * ((p : ℝ) - 2 ^ 24 * (C1 * C2))| := abs_add_le _ _
      _ ≤ (E : ℝ) + |(s : ℝ) * ((p : ℝ) - 2 ^ 24 * (C1 * C2))| :=
        add_le_add hx (le_refl _)
      _ = (E : ℝ) + |(s : ℝ)| * |(p : ℝ) - 2 ^ 24 * (C1 * C2)| := by rw [abs_mul]
      _ = (E : ℝ) + (s : ℝ) * |(p : ℝ) - 2 ^ 24 * (C1 * C2)| := by
        rw [abs_of_nonneg (by exact_mod_cast Nat.zero_le s)]
      _ ≤ (E : ℝ) + (s : ℝ) * ((E : ℝ) + (E : ℝ) + 2) := by
        have h_mul : (s : ℝ) * |(p : ℝ) - 2 ^ 24 * (C1 * C2)| ≤ (s : ℝ) * ((E : ℝ) + (E : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hp_bound (by exact_mod_cast Nat.zero_le s)
        exact add_le_add_right h_mul (E : ℝ)
      _ = (E : ℝ) + (s : ℝ) * (2 * (E : ℝ) + 2) := by ring
      _ ≤ (E : ℝ) + (k : ℝ) * (2 * (E : ℝ) + 2) := by
        have h_mul : (s : ℝ) * (2 * (E : ℝ) + 2) ≤ (k : ℝ) * (2 * (E : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (by nlinarith)
        exact add_le_add_right h_mul (E : ℝ)
  have h_right : |((fm g q + p : ℕ) : ℝ) - 2 ^ 24 * (G * (Se * Sf) + C1 * C2)| ≤ 5 * (E : ℝ) + 6 := by
    push_cast
    have h_eq : (fm g q : ℝ) + (p : ℝ) - 2 ^ 24 * (G * (Se * Sf) + C1 * C2) =
        ((fm g q : ℝ) - 2 ^ 24 * (G * (Se * Sf))) + ((p : ℝ) - 2 ^ 24 * (C1 * C2)) := by
      ring
    rw [h_eq]
    calc
      |((fm g q : ℝ) - 2 ^ 24 * (G * (Se * Sf))) + ((p : ℝ) - 2 ^ 24 * (C1 * C2))| ≤
          |(fm g q : ℝ) - 2 ^ 24 * (G * (Se * Sf))| + |(p : ℝ) - 2 ^ 24 * (C1 * C2)| :=
        abs_add_le _ _
      _ ≤ (3 * (E : ℝ) + 4) + ((E : ℝ) + (E : ℝ) + 2) := by
        refine add_le_add hgq_bound_simp hp_bound
      _ = 5 * (E : ℝ) + 6 := by ring
  set eL := (E : ℝ) + (k : ℝ) * (2 * (E : ℝ) + 2) with heL
  set eR := 5 * (E : ℝ) + 6 with heR
  set m := (2 * k + 6) * (E + 1) with hm
  have h_sum : eL + eR = (m : ℝ) := by
    dsimp [eL, eR, m]
    push_cast
    ring
  have h_lt : (x + s * p : ℕ) + m < (fm g q + p : ℕ) := by
    dsimp [p, q, m]
    omega
  apply D3Q2A0.flag_sound (x + s * p) (fm g q + p) m (X + (s : ℝ) * (C1 * C2)) (G * (Se * Sf) + C1 * C2) eL eR
    ?_ ?_ ?_ ?_
  · simpa [heL] using h_left
  · simpa [heR] using h_right
  ·

    simpa [hm] using h_sum.le
  ·

    simpa [p, q, m] using h_lt

theorem D3Q2A0.flag_sum_rev (x g e f c1 c2 s k E : ℕ) (X G Se Sf C1 C2 : ℝ) (hE : E ≤ 64) (hk : k ≤ 2) (hs : s ≤ k)
    (hG : |G| ≤ 1) (hSe : |Se| ≤ 1) (hSf : |Sf| ≤ 1) (hC1 : |C1| ≤ 1) (hC2 : |C2| ≤ 1)
    (hx : |(x : ℝ) - 2 ^ 24 * X| ≤ (E : ℝ)) (hg : |(g : ℝ) - 2 ^ 24 * G| ≤ (E : ℝ))
    (he : |(e : ℝ) - 2 ^ 24 * Se| ≤ (E : ℝ)) (hf : |(f : ℝ) - 2 ^ 24 * Sf| ≤ (E : ℝ))
    (hc1 : |(c1 : ℝ) - 2 ^ 24 * C1| ≤ (E : ℝ)) (hc2 : |(c2 : ℝ) - 2 ^ 24 * C2| ≤ (E : ℝ))
    (h : fm g (fm e f) + fm c1 c2 + (2 * k + 6) * (E + 1) < x + s * fm c1 c2) :
    G * (Se * Sf) + C1 * C2 < X + s * (C1 * C2) := by
  set p := fm c1 c2 with hp
  set q := fm e f with hq
  have hE_sq : (E : ℝ) * (E : ℝ) ≤ (2 ^ 24 : ℝ) := by
    have h_nonneg : 0 ≤ (E : ℝ) := by exact_mod_cast Nat.zero_le E
    have hE' : (E : ℝ) ≤ 64 := by exact_mod_cast hE
    have h64sq : (64 : ℝ) * (64 : ℝ) ≤ (2 ^ 24 : ℝ) := by norm_num
    have hsq : (E : ℝ) * (E : ℝ) ≤ (64 : ℝ) * (64 : ℝ) :=
      mul_le_mul hE' hE' h_nonneg (by linarith)
    linarith
  have hE_mul_2E2 : (E : ℝ) * ((E : ℝ) + (E : ℝ) + 2) ≤ (2 ^ 24 : ℝ) := by
    have h_nonneg : 0 ≤ (E : ℝ) := by exact_mod_cast Nat.zero_le E
    have hE' : (E : ℝ) ≤ 64 := by exact_mod_cast hE
    have hmax : (E : ℝ) * ((E : ℝ) + (E : ℝ) + 2) ≤ (64 : ℝ) * ((64 : ℝ) + (64 : ℝ) + 2) := by
      nlinarith
    have h64 : (64 : ℝ) * ((64 : ℝ) + (64 : ℝ) + 2) ≤ (2 ^ 24 : ℝ) := by norm_num
    nlinarith
  have hSe_mul_Sf : |Se * Sf| ≤ 1 := by
    calc
      |Se * Sf| = |Se| * |Sf| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul hSe hSf (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hp_bound : |(p : ℝ) - 2 ^ 24 * (C1 * C2)| ≤ (E : ℝ) + (E : ℝ) + 2 :=
    D3Q2A0.fm_margin c1 c2 C1 C2 (E : ℝ) (E : ℝ) hC1 hC2 hc1 hc2 hE_sq
  have hq_bound : |(q : ℝ) - 2 ^ 24 * (Se * Sf)| ≤ (E : ℝ) + (E : ℝ) + 2 :=
    D3Q2A0.fm_margin e f Se Sf (E : ℝ) (E : ℝ) hSe hSf he hf hE_sq
  have hpq_bound : |(fm g q : ℝ) - 2 ^ 24 * (G * (Se * Sf))| ≤ (E : ℝ) + ((E : ℝ) + (E : ℝ) + 2) + 2 :=
    D3Q2A0.fm_margin g q G (Se * Sf) (E : ℝ) ((E : ℝ) + (E : ℝ) + 2) hG hSe_mul_Sf hg hq_bound hE_mul_2E2
  have hLt : |((fm g q + p : ℕ) : ℝ) - 2 ^ 24 * (G * (Se * Sf) + C1 * C2)| ≤ (5 : ℝ) * (E : ℝ) + 6 := by
    push_cast
    have hsum : (fm g q : ℝ) + (p : ℝ) - 2 ^ 24 * (G * (Se * Sf) + C1 * C2) =
        ((fm g q : ℝ) - 2 ^ 24 * (G * (Se * Sf))) + ((p : ℝ) - 2 ^ 24 * (C1 * C2)) := by ring
    rw [hsum]
    calc
      |((fm g q : ℝ) - 2 ^ 24 * (G * (Se * Sf))) + ((p : ℝ) - 2 ^ 24 * (C1 * C2))|
          ≤ |(fm g q : ℝ) - 2 ^ 24 * (G * (Se * Sf))| + |(p : ℝ) - 2 ^ 24 * (C1 * C2)| := abs_add_le _ _
      _ ≤ ((E : ℝ) + ((E : ℝ) + (E : ℝ) + 2) + 2) + ((E : ℝ) + (E : ℝ) + 2) := by
        nlinarith
      _ = (5 : ℝ) * (E : ℝ) + 6 := by ring
  have hRt : |((x + s * p : ℕ) : ℝ) - 2 ^ 24 * (X + (s : ℝ) * (C1 * C2))| ≤ (E : ℝ) + (s : ℝ) * ((2 : ℝ) * (E : ℝ) + 2) := by
    push_cast
    have hsum : (x : ℝ) + (s : ℝ) * (p : ℝ) - 2 ^ 24 * (X + (s : ℝ) * (C1 * C2)) =
        ((x : ℝ) - 2 ^ 24 * X) + (s : ℝ) * ((p : ℝ) - 2 ^ 24 * (C1 * C2)) := by ring
    rw [hsum]
    calc
      |((x : ℝ) - 2 ^ 24 * X) + (s : ℝ) * ((p : ℝ) - 2 ^ 24 * (C1 * C2))|
          ≤ |(x : ℝ) - 2 ^ 24 * X| + |(s : ℝ) * ((p : ℝ) - 2 ^ 24 * (C1 * C2))| := abs_add_le _ _
      _ = |(x : ℝ) - 2 ^ 24 * X| + |(s : ℝ)| * |(p : ℝ) - 2 ^ 24 * (C1 * C2)| := by rw [abs_mul]
      _ = |(x : ℝ) - 2 ^ 24 * X| + (s : ℝ) * |(p : ℝ) - 2 ^ 24 * (C1 * C2)| := by
        rw [abs_of_nonneg (show 0 ≤ (s : ℝ) from Nat.cast_nonneg _)]
      _ ≤ (E : ℝ) + (s : ℝ) * ((2 : ℝ) * (E : ℝ) + 2) := by
        nlinarith
  have hm : ((5 : ℝ) * (E : ℝ) + 6) + ((E : ℝ) + (s : ℝ) * ((2 : ℝ) * (E : ℝ) + 2)) ≤
      ((2 * k + 6) * (E + 1) : ℕ) := by
    push_cast
    have hs' : (s : ℝ) ≤ (k : ℝ) := by exact_mod_cast hs
    have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    nlinarith
  have h_lt : (fm g q + p : ℕ) + ((2 * k + 6) * (E + 1) : ℕ) < (x + s * p : ℕ) := by
    calc
      (fm g q + p : ℕ) + ((2 * k + 6) * (E + 1) : ℕ) = fm g q + fm c1 c2 + (2 * k + 6) * (E + 1) := by
        simp [hp, hq]
      _ < x + s * fm c1 c2 := h
      _ = x + s * p := by simp [hp]
      _ = (x + s * p : ℕ) := by simp
  exact D3Q2A0.flag_sound (fm g q + p) (x + s * p) ((2 * k + 6) * (E + 1))
    (G * (Se * Sf) + C1 * C2) (X + (s : ℝ) * (C1 * C2))
    ((5 : ℝ) * (E : ℝ) + 6) ((E : ℝ) + (s : ℝ) * ((2 : ℝ) * (E : ℝ) + 2)) hLt hRt hm h_lt

theorem D3Q2A0.flag15 (x a E : ℕ) (X Al : ℝ) (hE : E ≤ 64) (hX : |X| ≤ 1) (hAl : |Al| ≤ 1)
    (hx : |(x : ℝ) - 2 ^ 24 * X| ≤ (E : ℝ)) (ha : |(a : ℝ) - 2 ^ 24 * Al| ≤ (E : ℝ))
    (h : x + (4 * E + 3) < fm a (16777216 + x)) : X < Al * (1 + X) := by
  have h_one_plus_X : |(1 : ℝ) + X| ≤ 2 := by
    have hX_lower : -1 ≤ X := (abs_le.mp hX).1
    have hX_upper : X ≤ 1 := (abs_le.mp hX).2
    apply abs_le.mpr
    constructor
    · linarith
    · linarith
  have hb : |((16777216 + x : ℕ) : ℝ) - 2 ^ 24 * ((1 : ℝ) + X)| ≤ (E : ℝ) := by
    push_cast
    have h16777216 : (16777216 : ℝ) = 2 ^ 24 := by norm_num
    rw [h16777216]
    have h_eq : ((2 ^ 24 : ℝ) + (x : ℝ)) - 2 ^ 24 * ((1 : ℝ) + X) = (x : ℝ) - 2 ^ 24 * X := by ring
    rw [h_eq]
    exact hx
  have h_fm_bound : |(fm a (16777216 + x) : ℝ) - 2 ^ 24 * (Al * ((1 : ℝ) + X))| ≤ 3 * (E : ℝ) + 2 := by
    have h_fm := D3Q2A0.fm_approx a (16777216 + x) Al ((1 : ℝ) + X) (E : ℝ) (E : ℝ) 1 2
      hAl h_one_plus_X ha hb
    have h_rhs : (1 : ℝ) * (E : ℝ) + (2 : ℝ) * (E : ℝ) + (E : ℝ) * (E : ℝ) / (2 ^ 24 : ℝ) + 1 ≤ 3 * (E : ℝ) + 2 := by
      have hE_sq_div : (E : ℝ) * (E : ℝ) / (2 ^ 24 : ℝ) ≤ 1 := by
        have hEsq : (E : ℝ) * (E : ℝ) ≤ 4096 := by
          have hE' : (E : ℝ) ≤ 64 := by exact_mod_cast hE
          nlinarith
        have hpos : (0 : ℝ) ≤ 2 ^ 24 := by norm_num
        have h_div : (E : ℝ) * (E : ℝ) / (2 ^ 24 : ℝ) ≤ 4096 / (2 ^ 24 : ℝ) :=
          div_le_div_of_nonneg_right hEsq hpos
        have h_4096_div : 4096 / (2 ^ 24 : ℝ) ≤ 1 := by norm_num
        linarith
      nlinarith
    exact le_trans h_fm h_rhs
  have hm : (E : ℝ) + (3 * (E : ℝ) + 2) ≤ ((4 * E + 3 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact D3Q2A0.flag_sound x (fm a (16777216 + x)) (4 * E + 3) X (Al * ((1 : ℝ) + X))
    (E : ℝ) (3 * (E : ℝ) + 2)
    hx h_fm_bound hm h
