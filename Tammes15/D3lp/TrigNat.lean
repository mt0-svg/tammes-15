import Tammes15.Numerics.Taylor

open Real

namespace Tammes15.D3lp.TrigNat

def sinTerm (b n x k : ℕ) : ℕ :=
  (2 * n + 1).descFactorial (2 * n - 2 * k) * 2 ^ (b * (2 * n - 2 * k)) * x ^ (2 * k + 1)

def sinSum (b n x par : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => sinSum b n x par m + if m % 2 = par then sinTerm b n x m else 0

def cosTerm (b n x k : ℕ) : ℕ :=
  (2 * n).descFactorial (2 * n - 2 * k) * 2 ^ (b * (2 * n + 1 - 2 * k)) * x ^ (2 * k)

def cosSum (b n x par : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => cosSum b n x par m + if m % 2 = par then cosTerm b n x m else 0

def sinGe (b n x c : ℕ) : Bool :=
  Nat.ble (sinSum b n x 1 n + x ^ (2 * n + 1) + c * (2 * n + 1).factorial * 2 ^ (b * (2 * n)))
    (sinSum b n x 0 n)

def sinLe (b n x c : ℕ) : Bool :=
  Nat.ble (sinSum b n x 0 n + x ^ (2 * n + 1))
    (sinSum b n x 1 n + c * (2 * n + 1).factorial * 2 ^ (b * (2 * n)))

def cosGe (b n x c : ℕ) : Bool :=
  Nat.ble (cosSum b n x 1 n + x ^ (2 * n) * 2 ^ b + c * (2 * n).factorial * 2 ^ (b * (2 * n)))
    (cosSum b n x 0 n)

def cosLe (b n x c : ℕ) : Bool :=
  Nat.ble (cosSum b n x 0 n + x ^ (2 * n) * 2 ^ b)
    (cosSum b n x 1 n + c * (2 * n).factorial * 2 ^ (b * (2 * n)))

def cosGeNeg (b n x c : ℕ) : Bool :=
  Nat.ble (cosSum b n x 1 n + x ^ (2 * n) * 2 ^ b)
    (cosSum b n x 0 n + c * (2 * n).factorial * 2 ^ (b * (2 * n)))

def cosLeNeg (b n x c : ℕ) : Bool :=
  Nat.ble (cosSum b n x 0 n + x ^ (2 * n) * 2 ^ b + c * (2 * n).factorial * 2 ^ (b * (2 * n)))
    (cosSum b n x 1 n)

theorem sinTerm_real (b n x k : ℕ) (hk : k ≤ n) :
    (sinTerm b n x k : ℝ) = ((2 * n + 1).factorial : ℝ) * 2 ^ (b * (2 * n + 1)) *
      (((x : ℝ) / 2 ^ b) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) := by
  have hd := Nat.factorial_mul_descFactorial (show 2 * n - 2 * k ≤ 2 * n + 1 by omega)
  have he : 2 * n + 1 - (2 * n - 2 * k) = 2 * k + 1 := by omega
  rw [he] at hd
  have hdR : ((2 * k + 1).factorial : ℝ) * ((2 * n + 1).descFactorial (2 * n - 2 * k) : ℝ) =
      ((2 * n + 1).factorial : ℝ) := by exact_mod_cast hd
  have hpow : (2 : ℝ) ^ (b * (2 * n + 1)) = 2 ^ (b * (2 * n - 2 * k)) * (2 ^ b) ^ (2 * k + 1) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    have : 2 * n + 1 = (2 * n - 2 * k) + (2 * k + 1) := by omega
    rw [this, Nat.mul_add]
  have hf : ((2 * k + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (2 : ℝ) ^ b ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold sinTerm
  push_cast
  rw [← hdR, hpow, div_pow]
  field_simp

theorem cosTerm_real (b n x k : ℕ) (hk : k ≤ n) :
    (cosTerm b n x k : ℝ) = ((2 * n).factorial : ℝ) * 2 ^ (b * (2 * n + 1)) *
      (((x : ℝ) / 2 ^ b) ^ (2 * k) / ((2 * k).factorial : ℝ)) := by
  have hd := Nat.factorial_mul_descFactorial (show 2 * n - 2 * k ≤ 2 * n by omega)
  have he : 2 * n - (2 * n - 2 * k) = 2 * k := by omega
  rw [he] at hd
  have hdR : ((2 * k).factorial : ℝ) * ((2 * n).descFactorial (2 * n - 2 * k) : ℝ) =
      ((2 * n).factorial : ℝ) := by exact_mod_cast hd
  have hpow : (2 : ℝ) ^ (b * (2 * n + 1)) = 2 ^ (b * (2 * n + 1 - 2 * k)) * (2 ^ b) ^ (2 * k) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    have : 2 * n + 1 = (2 * n + 1 - 2 * k) + 2 * k := by omega
    rw [this, Nat.mul_add]
    congr 2
    omega
  have hf : ((2 * k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (2 : ℝ) ^ b ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold cosTerm
  push_cast
  rw [← hdR, hpow, div_pow]
  field_simp

theorem sinSum_sub (b n x m : ℕ) (hm : m ≤ n) :
    (sinSum b n x 0 m : ℝ) - sinSum b n x 1 m =
      ((2 * n + 1).factorial : ℝ) * 2 ^ (b * (2 * n + 1)) *
        ∑ k ∈ Finset.range m, (-1) ^ k * ((x : ℝ) / 2 ^ b) ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ) := by
  induction m with
  | zero => simp [sinSum]
  | succ m ih =>
    have ih' := ih (by omega)
    have ht := sinTerm_real b n x m (by omega)
    simp only [sinSum, Finset.sum_range_succ]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have hp : ((-1 : ℝ)) ^ m = 1 := by
        rw [← Nat.mod_add_div m 2, h, pow_add, pow_mul]; norm_num
      simp only [h, ite_true, show ¬ (0 = 1) from by omega, ite_false, Nat.cast_add,
        add_zero, hp, one_mul]
      rw [mul_add, ← ih', ht]
      ring
    · have hp : ((-1 : ℝ)) ^ m = -1 := by
        rw [← Nat.mod_add_div m 2, h, pow_add, pow_mul]; norm_num
      simp only [h, ite_true, show ¬ (1 = 0) from by omega, ite_false, Nat.cast_add,
        add_zero, hp, neg_one_mul]
      rw [mul_add, ← ih', ht]
      ring

theorem cosSum_sub (b n x m : ℕ) (hm : m ≤ n) :
    (cosSum b n x 0 m : ℝ) - cosSum b n x 1 m =
      ((2 * n).factorial : ℝ) * 2 ^ (b * (2 * n + 1)) *
        ∑ k ∈ Finset.range m, (-1) ^ k * ((x : ℝ) / 2 ^ b) ^ (2 * k) /
          ((2 * k).factorial : ℝ) := by
  induction m with
  | zero => simp [cosSum]
  | succ m ih =>
    have ih' := ih (by omega)
    have ht := cosTerm_real b n x m (by omega)
    simp only [cosSum, Finset.sum_range_succ]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have hp : ((-1 : ℝ)) ^ m = 1 := by
        rw [← Nat.mod_add_div m 2, h, pow_add, pow_mul]; norm_num
      simp only [h, ite_true, show ¬ (0 = 1) from by omega, ite_false, Nat.cast_add, add_zero, hp,
        one_mul]
      rw [mul_add, ← ih', ht]
      ring
    · have hp : ((-1 : ℝ)) ^ m = -1 := by
        rw [← Nat.mod_add_div m 2, h, pow_add, pow_mul]; norm_num
      simp only [h, ite_true, show ¬ (1 = 0) from by omega, ite_false, Nat.cast_add, add_zero, hp,
        neg_one_mul]
      rw [mul_add, ← ih', ht]
      ring

theorem sin_rem_scaled (b n x : ℕ) :
    ((2 * n + 1).factorial : ℝ) * 2 ^ (b * (2 * n + 1)) *
        (((x : ℝ) / 2 ^ b) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) = (x : ℝ) ^ (2 * n + 1) := by
  have hfact : ((2 * n + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2exp : (2 : ℝ) ^ (b * (2 * n + 1)) ≠ 0 :=
    pow_ne_zero (b * (2 * n + 1)) (by norm_num : (2 : ℝ) ≠ 0)
  field_simp [hfact]
  rw [div_pow]
  rw [pow_mul]
  field_simp [h2exp]

theorem cos_rem_scaled (b n x : ℕ) :
    ((2 * n).factorial : ℝ) * 2 ^ (b * (2 * n + 1)) *
        (((x : ℝ) / 2 ^ b) ^ (2 * n) / ((2 * n).factorial : ℝ)) = (x : ℝ) ^ (2 * n) * 2 ^ b := by
  have hfact : ((2 * n).factorial : ℝ) ≠ 0 := by
    exact mod_cast Nat.factorial_ne_zero (2 * n)
  field_simp [hfact]
  rw [div_pow, ← pow_mul]
  have h_exp : (2 : ℝ) ^ (b * (2 * n + 1)) = (2 : ℝ) ^ (b * (2 * n)) * (2 : ℝ) ^ b := by
    calc
      (2 : ℝ) ^ (b * (2 * n + 1)) = (2 : ℝ) ^ (b * (2 * n) + b) := by ring
      _ = (2 : ℝ) ^ (b * (2 * n)) * (2 : ℝ) ^ b := by rw [pow_add]
  rw [h_exp]
  field_simp [pow_ne_zero (b * (2 * n)) (by norm_num : (2 : ℕ) ≠ 0)]

theorem sin_bound_scaled (b n c : ℕ) :
    ((2 * n + 1).factorial : ℝ) * 2 ^ (b * (2 * n + 1)) * ((c : ℝ) / 2 ^ b) =
      (c : ℝ) * ((2 * n + 1).factorial : ℝ) * 2 ^ (b * (2 * n)) := by
  have h_exp : (2 : ℝ) ^ (b * (2 * n + 1)) = (2 : ℝ) ^ (b * (2 * n)) * (2 : ℝ) ^ b := by
    calc
      (2 : ℝ) ^ (b * (2 * n + 1)) = (2 : ℝ) ^ (b * (2 * n) + b) := by ring
      _ = (2 : ℝ) ^ (b * (2 * n)) * (2 : ℝ) ^ b := by rw [pow_add]
  calc
    ((2 * n + 1).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n + 1)) * ((c : ℝ) / (2 : ℝ) ^ b)
        = ((2 * n + 1).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n)) * (2 : ℝ) ^ b) * ((c : ℝ) / (2 : ℝ) ^ b) := by
      rw [h_exp]
    _ = ((2 * n + 1).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) * ((2 : ℝ) ^ b * ((c : ℝ) / (2 : ℝ) ^ b)) := by ring
    _ = ((2 * n + 1).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) * (c : ℝ) := by
      field_simp [ne_of_gt (by positivity : 0 < (2 : ℝ) ^ b)]
    _ = (c : ℝ) * ((2 * n + 1).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) := by ring

theorem cos_bound_scaled (b n c : ℕ) :
    ((2 * n).factorial : ℝ) * 2 ^ (b * (2 * n + 1)) * ((c : ℝ) / 2 ^ b) =
      (c : ℝ) * ((2 * n).factorial : ℝ) * 2 ^ (b * (2 * n)) := by
  have h_exp : b * (2 * n + 1) = b * (2 * n) + b := by
    rw [Nat.mul_add, Nat.mul_one]
  have h_pow : (2 : ℝ) ^ (b * (2 * n + 1)) = (2 : ℝ) ^ (b * (2 * n)) * (2 : ℝ) ^ b := by
    rw [h_exp, pow_add]
  have h2b : (2 : ℝ) ^ b ≠ 0 := pow_ne_zero b (by norm_num : (2 : ℝ) ≠ 0)
  calc
    ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n + 1)) * (((c : ℝ) / (2 : ℝ) ^ b))
        = ((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n)) * (2 : ℝ) ^ b) * (((c : ℝ) / (2 : ℝ) ^ b)) := by
      rw [h_pow]
    _ = ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) * (2 : ℝ) ^ b * (((c : ℝ) / (2 : ℝ) ^ b)) := by ring
    _ = ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) * ((2 : ℝ) ^ b * (((c : ℝ) / (2 : ℝ) ^ b))) := by ring
    _ = ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) * (c : ℝ) := by
      field_simp [h2b]
    _ = (c : ℝ) * ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) := by ring

theorem sinGe_sound {b n x c : ℕ} (h : sinGe b n x c = true) :
    (c : ℝ) / 2 ^ b ≤ sin ((x : ℝ) / 2 ^ b) := by
  set v := (x : ℝ) / 2 ^ b with hv
  have hv_nonneg : 0 ≤ v := by
    rw [hv]
    refine div_nonneg (Nat.cast_nonneg _) ?_
    positivity
  refine Tammes15.Numerics.le_sin_of_sinT n hv_nonneg ?_
  set M := ((2 * n + 1).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n + 1))) with hM
  have hMpos : 0 < M := by
    rw [hM]
    refine mul_pos (by exact_mod_cast Nat.factorial_pos _) ?_
    positivity
  have hnat : sinSum b n x 1 n + x ^ (2 * n + 1) + c * (2 * n + 1).factorial * 2 ^ (b * (2 * n)) ≤
      sinSum b n x 0 n := by
    simpa [sinGe, Nat.ble_eq] using h
  have hsum := sinSum_sub b n x n (le_rfl)
  have hrem := sin_rem_scaled b n x
  have hineq : (c : ℝ) / 2 ^ b ≤ Tammes15.Numerics.sinT n v - v ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
    apply le_of_mul_le_mul_left ?_ hMpos
    calc
      M * ((c : ℝ) / 2 ^ b) = (c : ℝ) * ((2 * n + 1).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n))) := by
        rw [sin_bound_scaled b n c]
      _ ≤ ((sinSum b n x 0 n : ℝ) - (sinSum b n x 1 n : ℝ)) - (x : ℝ) ^ (2 * n + 1) := by
        have h' : (sinSum b n x 1 n : ℝ) + (x : ℝ) ^ (2 * n + 1) + (c : ℝ) * ((2 * n + 1).factorial : ℝ) *
            ((2 : ℝ) ^ (b * (2 * n))) ≤ (sinSum b n x 0 n : ℝ) := by
          exact_mod_cast hnat
        linarith
      _ = M * Tammes15.Numerics.sinT n ((x : ℝ) / 2 ^ b) - (x : ℝ) ^ (2 * n + 1) := by
        simpa [hM, Tammes15.Numerics.sinT] using
          congrArg (· - (x : ℝ) ^ (2 * n + 1)) hsum
      _ = M * Tammes15.Numerics.sinT n ((x : ℝ) / 2 ^ b) -
          (((2 * n + 1).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n + 1))) *
            (((x : ℝ) / 2 ^ b) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))) := by rw [hM, hrem]
      _ = M * (Tammes15.Numerics.sinT n ((x : ℝ) / 2 ^ b) -
          (((x : ℝ) / 2 ^ b) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))) := by rw [mul_sub]
      _ = M * (Tammes15.Numerics.sinT n v - v ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
        rw [hv]
  exact hineq

theorem sinLe_sound {b n x c : ℕ} (h : sinLe b n x c = true) :
    sin ((x : ℝ) / 2 ^ b) ≤ (c : ℝ) / 2 ^ b := by
  have hx : 0 ≤ (x : ℝ) / ((2 : ℝ) ^ b) := by
    have hx' : 0 ≤ (x : ℝ) := Nat.cast_nonneg _
    have hp : 0 ≤ ((2 : ℝ) ^ b) := pow_nonneg (by norm_num) _
    exact div_nonneg hx' hp
  set v := (x : ℝ) / ((2 : ℝ) ^ b) with hv
  set M := ((2 * n + 1).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n + 1))) with hM
  have hMpos : 0 < M := by
    have hfact : 0 < ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpow : 0 < (2 : ℝ) ^ (b * (2 * n + 1)) := pow_pos (by norm_num) _
    exact mul_pos hfact hpow

  have hM_mul_sinT : M * (Tammes15.Numerics.sinT n v) = ((sinSum b n x 0 n : ℕ) : ℝ) - ((sinSum b n x 1 n : ℕ) : ℝ) := by
    have hsub := sinSum_sub b n x n (le_refl n)
    dsimp [v, M, Tammes15.Numerics.sinT]
    rw [← hsub]
  have hM_mul_rem : M * (v ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) = (x : ℝ) ^ (2 * n + 1) := by
    have hrem := sin_rem_scaled b n x
    dsimp [v, M]
    rw [← hrem]
  have hM_mul_bound : M * ((c : ℝ) / ((2 : ℝ) ^ b)) = (c : ℝ) * ((2 * n + 1).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n))) := by
    have hbound := sin_bound_scaled b n c
    dsimp [M]
    rw [← hbound]

  have h_nat_ineq : (sinSum b n x 0 n : ℕ) + x ^ (2 * n + 1) ≤
      (sinSum b n x 1 n : ℕ) + c * (2 * n + 1).factorial * 2 ^ (b * (2 * n)) := by
    unfold sinLe at h
    exact Nat.le_of_ble_eq_true h

  have h_ineq : ((sinSum b n x 0 n : ℕ) : ℝ) + ((x : ℝ) ^ (2 * n + 1)) ≤
      ((sinSum b n x 1 n : ℕ) : ℝ) + (c : ℝ) * ((2 * n + 1).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n))) := by
    exact_mod_cast h_nat_ineq

  have hM_ineq : M * (Tammes15.Numerics.sinT n v + v ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) ≤
      M * ((c : ℝ) / ((2 : ℝ) ^ b)) := by
    calc
      M * (Tammes15.Numerics.sinT n v + v ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) =
          M * (Tammes15.Numerics.sinT n v) + M * (v ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by ring
      _ = (((sinSum b n x 0 n : ℕ) : ℝ) - ((sinSum b n x 1 n : ℕ) : ℝ)) + (x : ℝ) ^ (2 * n + 1) := by rw [hM_mul_sinT, hM_mul_rem]
      _ ≤ (c : ℝ) * ((2 * n + 1).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n))) := by
        linarith
      _ = M * ((c : ℝ) / ((2 : ℝ) ^ b)) := by rw [hM_mul_bound]

  have h_main : Tammes15.Numerics.sinT n v + v ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) ≤ (c : ℝ) / 2 ^ b :=
    le_of_mul_le_mul_left hM_ineq hMpos
  exact Tammes15.Numerics.sin_le_of_sinT n (c := (c : ℝ) / ((2 : ℝ) ^ b)) hx h_main

theorem cosGe_sound {b n x c : ℕ} (h : cosGe b n x c = true) :
    (c : ℝ) / 2 ^ b ≤ cos ((x : ℝ) / 2 ^ b) := by
  set v := (x : ℝ) / 2 ^ b with hv
  have hx : 0 ≤ v := by
    rw [hv]
    refine div_nonneg (Nat.cast_nonneg _) ?_
    positivity
  have hineq_nat : cosSum b n x 1 n + x ^ (2 * n) * 2 ^ b + c * (2 * n).factorial * 2 ^ (b * (2 * n)) ≤
      cosSum b n x 0 n := by
    simpa [cosGe, Nat.ble_eq] using h
  have hineq_real : (cosSum b n x 1 n : ℝ) + (x : ℝ) ^ (2 * n) * (2 : ℝ) ^ b + (c : ℝ) * ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) ≤
      (cosSum b n x 0 n : ℝ) := by
    exact_mod_cast hineq_nat
  set M := ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n + 1)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    positivity
  have hM_cosT : M * Tammes15.Numerics.cosT n v = (cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ) := by
    calc
      M * Tammes15.Numerics.cosT n v = ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n + 1)) * Tammes15.Numerics.cosT n v := by rw [hM]
      _ = ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n + 1)) *
          (∑ k ∈ Finset.range n, (-1) ^ k * ((x : ℝ) / 2 ^ b) ^ (2 * k) / ((2 * k).factorial : ℝ)) := rfl
      _ = (cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ) := by
        rw [← cosSum_sub b n x n le_rfl]
  have hcosT : (c : ℝ) / 2 ^ b ≤ Tammes15.Numerics.cosT n v - v ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    have htemp : M * ((c : ℝ) / 2 ^ b) ≤ M * (Tammes15.Numerics.cosT n v - v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
      calc
        M * ((c : ℝ) / 2 ^ b) = (c : ℝ) * ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) := by
          rw [hM]
          exact cos_bound_scaled b n c
        _ ≤ ((cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ)) - (x : ℝ) ^ (2 * n) * (2 : ℝ) ^ b := by
          linarith
        _ = M * Tammes15.Numerics.cosT n v - M * (v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
          rw [hM_cosT]
          have h_eq : (x : ℝ) ^ (2 * n) * (2 : ℝ) ^ b = M * (v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
            rw [hM, hv]
            exact (cos_rem_scaled b n x).symm
          rw [h_eq]
        _ = M * (Tammes15.Numerics.cosT n v - v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by ring
    exact le_of_mul_le_mul_left htemp hMpos
  exact Tammes15.Numerics.le_cos_of_cosT n hx hcosT

theorem cosLe_sound {b n x c : ℕ} (h : cosLe b n x c = true) :
    cos ((x : ℝ) / 2 ^ b) ≤ (c : ℝ) / 2 ^ b := by
  set v := (x : ℝ) / (2 : ℝ) ^ b with hv
  have hv_nonneg : 0 ≤ v := by
    rw [hv]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hgoal : Tammes15.Numerics.cosT n v + v ^ (2 * n) / ((2 * n).factorial : ℝ) ≤ (c : ℝ) / (2 : ℝ) ^ b := by
    set M := ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n + 1)) with hM
    have hM_pos : 0 < M := by
      rw [hM]
      positivity
    have hineq_nat : cosSum b n x 0 n + x ^ (2 * n) * 2 ^ b ≤
        cosSum b n x 1 n + c * (2 * n).factorial * 2 ^ (b * (2 * n)) := by
      unfold cosLe at h
      exact Nat.le_of_ble_eq_true h
    have hineq_real : (cosSum b n x 0 n : ℝ) + (x : ℝ) ^ (2 * n) * (2 : ℝ) ^ b ≤
        (cosSum b n x 1 n : ℝ) + (c : ℝ) * ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) := by
      exact_mod_cast hineq_nat
    have h_sub : M * Tammes15.Numerics.cosT n v = (cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ) := by
      rw [hM, Tammes15.Numerics.cosT]
      rw [← (cosSum_sub b n x n (le_refl n))]
    have h_rem : M * (v ^ (2 * n) / ((2 * n).factorial : ℝ)) = (x : ℝ) ^ (2 * n) * (2 : ℝ) ^ b := by
      rw [hM, hv]
      exact cos_rem_scaled b n x
    have h_bound : M * ((c : ℝ) / (2 : ℝ) ^ b) = (c : ℝ) * ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) := by
      rw [hM]
      exact cos_bound_scaled b n c
    apply le_of_mul_le_mul_left ?_ hM_pos
    calc
      M * (Tammes15.Numerics.cosT n v + v ^ (2 * n) / ((2 * n).factorial : ℝ)) =
          M * Tammes15.Numerics.cosT n v + M * (v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by ring
      _ = ((cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ)) + ((x : ℝ) ^ (2 * n) * (2 : ℝ) ^ b) := by
        rw [h_sub, h_rem]
      _ ≤ (c : ℝ) * ((2 * n).factorial : ℝ) * (2 : ℝ) ^ (b * (2 * n)) := by
        linarith
      _ = M * ((c : ℝ) / (2 : ℝ) ^ b) := by rw [h_bound]
  exact Tammes15.Numerics.cos_le_of_cosT n hv_nonneg hgoal

theorem cosGeNeg_sound {b n x c : ℕ} (h : cosGeNeg b n x c = true) :
    -((c : ℝ) / 2 ^ b) ≤ cos ((x : ℝ) / 2 ^ b) := by
  set v := (x : ℝ) / ((2 : ℝ) ^ b) with hv
  set M := ((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n + 1))) with hM
  have hx : 0 ≤ v := by
    rw [hv]
    have hx' : 0 ≤ (x : ℝ) := Nat.cast_nonneg _
    have hp : 0 ≤ (2 : ℝ) ^ b := pow_nonneg (by norm_num) _
    exact div_nonneg hx' hp
  have hMpos : 0 < M := by
    rw [hM]
    have hfact : 0 < ((2 * n).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hpow : 0 < (2 : ℝ) ^ (b * (2 * n + 1)) := pow_pos (by norm_num) _
    exact mul_pos hfact hpow
  apply Tammes15.Numerics.le_cos_of_cosT n hx

  have hineq : M * (-(c : ℝ) / ((2 : ℝ) ^ b)) ≤ M * (Tammes15.Numerics.cosT n v - v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
    have hL : M * (-(c : ℝ) / ((2 : ℝ) ^ b)) = -((c : ℝ) * ((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n)))) := by
      calc
        M * (-(c : ℝ) / ((2 : ℝ) ^ b)) = -(M * ((c : ℝ) / ((2 : ℝ) ^ b))) := by ring
        _ = -((c : ℝ) * ((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n)))) := by
          rw [hM, cos_bound_scaled]
    have hcosSum := cosSum_sub b n x n (le_refl n)
    have hcosSum' : M * Tammes15.Numerics.cosT n v = (cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ) := by
      rw [hM, hv, Tammes15.Numerics.cosT]
      simpa using hcosSum.symm
    have hR : M * (Tammes15.Numerics.cosT n v - v ^ (2 * n) / ((2 * n).factorial : ℝ)) =
        ((cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ)) - (x : ℝ) ^ (2 * n) * ((2 : ℝ) ^ b) := by
      calc
        M * (Tammes15.Numerics.cosT n v - v ^ (2 * n) / ((2 * n).factorial : ℝ)) =
            M * Tammes15.Numerics.cosT n v - M * (v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by ring
        _ = ((cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ)) - M * (v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
          rw [hcosSum']
        _ = ((cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ)) - (x : ℝ) ^ (2 * n) * ((2 : ℝ) ^ b) := by
          rw [hM, cos_rem_scaled]
    rw [hL, hR]

    have hnat : cosSum b n x 1 n + x ^ (2 * n) * 2 ^ b ≤
        cosSum b n x 0 n + c * (2 * n).factorial * 2 ^ (b * (2 * n)) :=
      Nat.le_of_ble_eq_true h
    have hnat' : (cosSum b n x 1 n : ℝ) + (x : ℝ) ^ (2 * n) * ((2 : ℝ) ^ b) ≤
        (cosSum b n x 0 n : ℝ) + (c : ℝ) * ((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n))) := by
      exact_mod_cast hnat
    linarith

  have hgoal : M * (-(↑c / ((2 : ℝ) ^ b))) ≤ M * (Tammes15.Numerics.cosT n v - v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by

    simpa [neg_div] using hineq
  exact le_of_mul_le_mul_left hgoal hMpos

theorem cosLeNeg_sound {b n x c : ℕ} (h : cosLeNeg b n x c = true) :
    cos ((x : ℝ) / 2 ^ b) ≤ -((c : ℝ) / 2 ^ b) := by
  set v := (x : ℝ) / (2 ^ b : ℝ) with hv
  have hv_nonneg : 0 ≤ v := by
    rw [hv]
    refine div_nonneg (Nat.cast_nonneg _) (by positivity)
  have h_cosT : Tammes15.Numerics.cosT n v + v ^ (2 * n) / ((2 * n).factorial : ℝ) ≤ -((c : ℝ) / (2 ^ b : ℝ)) := by
    set M := ((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n + 1))) with hM
    have hMpos : 0 < M := by
      rw [hM]
      refine mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (by norm_num) _)
    have h_nat : cosSum b n x 0 n + x ^ (2 * n) * 2 ^ b + c * (2 * n).factorial * 2 ^ (b * (2 * n)) ≤
        cosSum b n x 1 n := by
      exact Nat.le_of_ble_eq_true h
    have h_nat' : (cosSum b n x 0 n + x ^ (2 * n) * 2 ^ b + c * (2 * n).factorial * 2 ^ (b * (2 * n)) : ℝ) ≤
        (cosSum b n x 1 n : ℝ) := by exact_mod_cast h_nat
    have h_eq : M * (Tammes15.Numerics.cosT n v + v ^ (2 * n) / ((2 * n).factorial : ℝ)) ≤
        M * (-((c : ℝ) / (2 ^ b : ℝ))) := by
      calc
        M * (Tammes15.Numerics.cosT n v + v ^ (2 * n) / ((2 * n).factorial : ℝ))
            = M * Tammes15.Numerics.cosT n v + M * (v ^ (2 * n) / ((2 * n).factorial : ℝ)) := by ring
        _ = ((cosSum b n x 0 n : ℝ) - (cosSum b n x 1 n : ℝ)) +
            ((x : ℝ) ^ (2 * n) * (2 : ℝ) ^ b) := by
          rw [hM]
          have h_cosSum_sub := cosSum_sub b n x n (le_refl n)
          have h_cos_rem := cos_rem_scaled b n x
          rw [h_cosSum_sub, h_cos_rem]
          simp [hv, Tammes15.Numerics.cosT]
        _ = ((cosSum b n x 0 n : ℝ) + (x : ℝ) ^ (2 * n) * (2 : ℝ) ^ b) -
            (cosSum b n x 1 n : ℝ) := by ring
        _ ≤ -((c : ℝ) * ((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n)))) := by
          linarith
        _ = M * (-((c : ℝ) / (2 ^ b : ℝ))) := by
          rw [hM]
          calc
            -((c : ℝ) * ((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n))))
                = -(((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n + 1))) * ((c : ℝ) / (2 ^ b : ℝ))) := by
              rw [cos_bound_scaled b n c]
            _ = ((2 * n).factorial : ℝ) * ((2 : ℝ) ^ (b * (2 * n + 1))) * (-((c : ℝ) / (2 ^ b : ℝ))) := by ring
    exact le_of_mul_le_mul_left h_eq hMpos
  exact Tammes15.Numerics.cos_le_of_cosT n hv_nonneg h_cosT

theorem le_arcsin_of_sin_le {y c : ℝ} (hc1 : -(π / 2) ≤ c) (hc2 : c ≤ π / 2) (hy : y ≤ 1)
    (h : sin c ≤ y) : c ≤ arcsin y := by
  rw [← Real.arcsin_sin hc1 hc2]
  exact Real.arcsin_le_arcsin h

theorem arcsin_le_of_le_sin {y c : ℝ} (hc1 : -(π / 2) ≤ c) (hc2 : c ≤ π / 2) (hy : -1 ≤ y)
    (h : y ≤ sin c) : arcsin y ≤ c := by
  have hy1 : y ≤ 1 := le_trans h (Real.sin_le_one c)
  have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 := ⟨hy, hy1⟩
  have hc_mem : c ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨hc1, hc2⟩
  rw [Real.arcsin_le_iff_le_sin hy_mem hc_mem]
  exact h

theorem le_arctan_of_sin_le {y c : ℝ} (hc1 : -(π / 2) < c) (hc2 : c < π / 2)
    (h : sin c ≤ y * cos c) : c ≤ arctan y := by
  have hcos_pos : 0 < cos c :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have htan_le_y : tan c ≤ y := by
    calc
      tan c = sin c / cos c := Real.tan_eq_sin_div_cos c
      _ ≤ y := (div_le_iff₀ hcos_pos).2 h
  calc
    c = arctan (tan c) := (Real.arctan_tan hc1 hc2).symm
    _ ≤ arctan y := Real.arctan_mono htan_le_y

theorem arctan_le_of_le_sin {y c : ℝ} (hc1 : -(π / 2) < c) (hc2 : c < π / 2)
    (h : y * cos c ≤ sin c) : arctan y ≤ c := by
  have hcos_pos : 0 < cos c :=
    Real.cos_pos_of_mem_Ioo (Set.mem_Ioo.mpr ⟨hc1, hc2⟩)
  have hy_le_tan_c : y ≤ tan c :=
    calc
      y ≤ sin c / cos c := (le_div_iff₀ hcos_pos).mpr h
      _ = tan c := by rw [Real.tan_eq_sin_div_cos]
  calc
    arctan y ≤ arctan (tan c) := Real.arctan_mono hy_le_tan_c
    _ = c := Real.arctan_tan hc1 hc2

end Tammes15.D3lp.TrigNat
