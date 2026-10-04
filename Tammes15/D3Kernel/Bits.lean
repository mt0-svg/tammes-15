import Tammes15.D3Kernel.Iface

namespace Tammes15.D3Kernel

theorem land_shiftRight (x o w : ℕ) : Nat.land (Nat.shiftRight x o) (2 ^ w - 1) = bits x o w := by
  unfold bits
  rw [Nat.land_eq, Nat.shiftRight_eq]
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  rw [Bool.and_comm]

theorem land_mask_shiftLeft (x s : ℕ) :
    Nat.land x (Nat.shiftLeft 18446744073709551615 s) = x / 2 ^ s % 2 ^ 64 * 2 ^ s := by
  have h18446744073709551615 : 18446744073709551615 = 2^64 - 1 := by norm_num
  rw [h18446744073709551615]
  rw [Nat.land_eq]
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq_mul_pow]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_land, Nat.testBit_mul_two_pow]
  rw [Nat.testBit_mul_two_pow]
  rw [Nat.testBit_mod_two_pow]
  rw [Nat.testBit_div_two_pow]
  by_cases hsk : s ≤ k
  ·
    have h_add : (k - s) + s = k := Nat.sub_add_cancel hsk
    rw [h_add]
    rw [Nat.testBit_two_pow_sub_one]
    by_cases h_lt : k - s < 64
    · simp [hsk, h_lt]
    · simp [hsk, h_lt]
  ·
    have hk_lt_s : k < s := Nat.lt_of_not_ge hsk
    have h_sub : k - s = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hk_lt_s)
    rw [h_sub]
    simp [hsk]

theorem bnd_setBnd_self (box t w : ℕ) (hw : w < 2 ^ 64) : bnd (setBnd box t w) t = w := by
  dsimp [bnd, setBnd, bits]
  set s := 2 ^ (64 * t) with hs
  set m := 2 ^ 64 with hm
  have hs_pos : s ≠ 0 := by positivity
  have hm_pos : m ≠ 0 := by positivity
  set r := box / s % m with hr
  set q := box / s / m with hq

  have h_div_eq : box / s = q * m + r := by
    have h := Nat.div_add_mod (box / s) m
    rw [← hq, ← hr] at h
    rw [mul_comm] at h
    rw [← h]

  have h_box_eq : box = (box / s) * s + box % s := by
    have h := Nat.div_add_mod box s
    rw [mul_comm] at h
    exact h.symm

  have h_box_eq2 : box = q * m * s + r * s + box % s := by
    calc
      box = (box / s) * s + box % s := h_box_eq
      _ = (q * m + r) * s + box % s := by rw [h_div_eq]
      _ = q * m * s + r * s + box % s := by rw [add_mul]

  have h_sub_add : (q * m * s + r * s + box % s) - r * s + w * s = q * m * s + box % s + w * s := by
    have hle : r * s ≤ r * s + box % s := Nat.le_add_right _ _

    rw [add_assoc]

    rw [Nat.add_sub_assoc hle (q * m * s)]

    rw [Nat.add_sub_cancel_left]

  have hgoal : (box - box / s % m * s + w * s) / s % m = w := by

    rw [← hr]

    rw [h_box_eq2]

    rw [h_sub_add]

    have h_div_split : (q * m * s + box % s + w * s) / s = q * m + (box % s + w * s) / s := by
      have hpos : 0 < s := Nat.pos_of_ne_zero hs_pos
      calc
        (q * m * s + box % s + w * s) / s = ((box % s + w * s) + q * m * s) / s := by
          simp [add_comm, add_left_comm, add_assoc]
        _ = ((box % s + w * s) + (q * m) * s) / s := by rw [mul_assoc]
        _ = (box % s + w * s) / s + q * m := by rw [Nat.add_mul_div_right (box % s + w * s) (q * m) hpos]
        _ = q * m + (box % s + w * s) / s := by rw [add_comm]
    rw [h_div_split]

    have h_mod_lt : box % s < s := Nat.mod_lt box (Nat.pos_of_ne_zero hs_pos)
    have h_div_inner : (box % s + w * s) / s = w := by
      apply Nat.div_eq_of_lt_le
      ·
        exact Nat.le_add_left (w * s) (box % s)
      ·
        rw [Nat.add_one w, Nat.succ_mul]
        have h : box % s + w * s < s + w * s := Nat.add_lt_add_right h_mod_lt (w * s)
        rw [add_comm s (w * s)] at h
        exact h
    rw [h_div_inner]

    rw [Nat.add_mod]
    have h_mul_mod : (q * m) % m = 0 := by
      calc
        (q * m) % m = ((q % m) * (m % m)) % m := by rw [Nat.mul_mod]
        _ = ((q % m) * 0) % m := by rw [Nat.mod_self]
        _ = 0 % m := by simp
        _ = 0 := by rw [Nat.zero_mod]
    rw [h_mul_mod]
    simp [Nat.mod_eq_of_lt hw]

  simpa [hm] using hgoal

theorem bnd_indep (H L t t' v : ℕ) (hv : v < 2 ^ 64) (hL : L < 2 ^ (64 * t)) (h : t' ≠ t) :
    bnd ((H * 2 ^ 64 + v) * 2 ^ (64 * t) + L) t' =
      if t' < t then L / 2 ^ (64 * t') % 2 ^ 64 else H / 2 ^ (64 * (t' - t - 1)) % 2 ^ 64 := by
  unfold bnd bits
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · rw [ite_eq_left hlt]
    obtain ⟨d, rfl⟩ : ∃ d, t = t' + (d + 1) := ⟨t - t' - 1, by omega⟩
    have e1 : (H * 2 ^ 64 + v) * 2 ^ (64 * (t' + (d + 1))) + L =
        L + (H * 2 ^ 64 + v) * 2 ^ (64 * d) * 2 ^ 64 * 2 ^ (64 * t') := by
      rw [show 64 * (t' + (d + 1)) = 64 * d + 64 + 64 * t' by ring, pow_add, pow_add]
      ring
    rw [e1, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
  · rw [ite_eq_right (by omega)]
    obtain ⟨d, rfl⟩ : ∃ d, t' = t + (d + 1) := ⟨t' - t - 1, by omega⟩
    rw [show t + (d + 1) - t - 1 = d by omega]
    have e2 : 2 ^ (64 * (t + (d + 1))) = 2 ^ (64 * t) * (2 ^ 64 * 2 ^ (64 * d)) := by
      rw [← pow_add, ← pow_add]
      ring_nf
    rw [e2, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    rw [add_comm ((H * 2 ^ 64 + v) * 2 ^ (64 * t)) L, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hL, zero_add]
    rw [add_comm (H * 2 ^ 64) v, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]

theorem bnd_setBnd_ne (box t t' w : ℕ) (hw : w < 2 ^ 64) (h : t' ≠ t) :
    bnd (setBnd box t w) t' = bnd box t' := by
  have hs : 0 < 2 ^ (64 * t) := by positivity
  have hbox : box = (box / 2 ^ (64 * t) / 2 ^ 64 * 2 ^ 64 + box / 2 ^ (64 * t) % 2 ^ 64) * 2 ^ (64 * t) +
      box % 2 ^ (64 * t) := by
    rw [Nat.div_add_mod', Nat.div_add_mod']
  have hset : setBnd box t w = (box / 2 ^ (64 * t) / 2 ^ 64 * 2 ^ 64 + w) * 2 ^ (64 * t) + box % 2 ^ (64 * t) := by
    have e : setBnd box t w = box - box / 2 ^ (64 * t) % 2 ^ 64 * 2 ^ (64 * t) + w * 2 ^ (64 * t) := rfl
    rw [e]
    have hb := hbox
    generalize box / 2 ^ (64 * t) / 2 ^ 64 = H at hb ⊢
    generalize box / 2 ^ (64 * t) % 2 ^ 64 = M at hb ⊢
    generalize box % 2 ^ (64 * t) = L at hb ⊢
    rw [hb, add_mul, add_right_comm, Nat.add_sub_cancel]
    ring
  rw [hset]
  conv_rhs => rw [hbox]
  rw [bnd_indep _ _ _ _ _ hw (Nat.mod_lt _ hs) h,
    bnd_indep _ _ _ _ _ (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ hs) h]

theorem active_setBnd (box t w : ℕ) (ht : t < 128) (_hw : w < 2 ^ 64) (hb : Active box) :
    Active (setBnd box t w) := by
  unfold Active at hb ⊢

  have h_bound : 64 * t + 64 ≤ 8192 := by
    have ht' : t ≤ 127 := by omega
    omega
  have h_pow_pos : 0 < 2 ^ (64 * t + 64) := by positivity
  set H := box / 2 ^ (64 * t + 64) with hH_def
  set M := bnd box t with hM_def
  set L := box % 2 ^ (64 * t) with hL_def

  have h_box_eq : box = H * 2 ^ (64 * t + 64) + M * 2 ^ (64 * t) + L := by
    have h_divmod1 : box = (box / 2 ^ (64 * t)) * 2 ^ (64 * t) + box % 2 ^ (64 * t) := by
      have h := (Nat.div_add_mod box (2 ^ (64 * t))).symm

      simpa [mul_comm] using h
    have h_divmod2 : (box / 2 ^ (64 * t)) = ((box / 2 ^ (64 * t)) / 2 ^ 64) * 2 ^ 64 + (box / 2 ^ (64 * t)) % 2 ^ 64 := by
      have h := (Nat.div_add_mod (box / 2 ^ (64 * t)) (2 ^ 64)).symm

      simpa [mul_comm] using h
    calc
      box = (box / 2 ^ (64 * t)) * 2 ^ (64 * t) + box % 2 ^ (64 * t) := h_divmod1
      _ = (((box / 2 ^ (64 * t)) / 2 ^ 64) * 2 ^ 64 + (box / 2 ^ (64 * t)) % 2 ^ 64) * 2 ^ (64 * t) + box % 2 ^ (64 * t) := by

        nth_rw 1 [h_divmod2]
      _ = ((box / (2 ^ (64 * t) * 2 ^ 64)) * 2 ^ 64 + M) * 2 ^ (64 * t) + L := by
        rw [Nat.div_div_eq_div_mul, hM_def, hL_def, bnd, bits]
      _ = ((box / 2 ^ (64 * t + 64)) * 2 ^ 64 + M) * 2 ^ (64 * t) + L := by
        rw [show (2 : ℕ) ^ (64 * t) * 2 ^ 64 = 2 ^ (64 * t + 64) by ring]
      _ = (box / 2 ^ (64 * t + 64)) * (2 ^ 64 * 2 ^ (64 * t)) + M * 2 ^ (64 * t) + L := by ring
      _ = H * 2 ^ (64 * t + 64) + M * 2 ^ (64 * t) + L := by
        rw [hH_def, show (2 : ℕ) ^ 64 * 2 ^ (64 * t) = 2 ^ (64 * t + 64) by ring]

  have h_mod_lt : M * 2 ^ (64 * t) + L < 2 ^ (64 * t + 64) := by
    have hM_lt : M < 2 ^ 64 := by
      rw [hM_def, bnd, bits]
      exact Nat.mod_lt _ (by norm_num)
    have hL_lt : L < 2 ^ (64 * t) := by rw [hL_def]; exact Nat.mod_lt _ (by norm_num)
    have hM_le : M ≤ 2 ^ 64 - 1 := by omega
    have hL_le : L ≤ 2 ^ (64 * t) - 1 := by omega
    have h_sum_le : M * 2 ^ (64 * t) + L ≤ (2 ^ 64 - 1) * 2 ^ (64 * t) + (2 ^ (64 * t) - 1) := by
      have h1 : M * 2 ^ (64 * t) ≤ (2 ^ 64 - 1) * 2 ^ (64 * t) := Nat.mul_le_mul_right _ hM_le
      exact Nat.add_le_add h1 hL_le
    have h_target : (2 ^ 64 - 1) * 2 ^ (64 * t) + (2 ^ (64 * t) - 1) < 2 ^ (64 * t + 64) := by
      have h_eq : (2 ^ 64 - 1) * 2 ^ (64 * t) + (2 ^ (64 * t) - 1) + 1 = 2 ^ (64 * t + 64) := by
        calc
          (2 ^ 64 - 1) * 2 ^ (64 * t) + (2 ^ (64 * t) - 1) + 1 = (2 ^ 64 - 1) * 2 ^ (64 * t) + 2 ^ (64 * t) := by omega
          _ = ((2 ^ 64 - 1) + 1) * 2 ^ (64 * t) := by ring
          _ = 2 ^ 64 * 2 ^ (64 * t) := by
            rw [Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 64)]
          _ = 2 ^ (64 * t + 64) := by rw [← Nat.pow_add, add_comm, Nat.pow_add]
      omega
    omega

  have hH_ineq : 2 ^ (8192 - (64 * t + 64)) ≤ H := by

    have h_lt : H * 2 ^ (64 * t + 64) + (M * 2 ^ (64 * t) + L) < (H + 1) * 2 ^ (64 * t + 64) := by
      calc
        H * 2 ^ (64 * t + 64) + (M * 2 ^ (64 * t) + L) < H * 2 ^ (64 * t + 64) + 2 ^ (64 * t + 64) :=
          Nat.add_lt_add_left h_mod_lt _
        _ = (H + 1) * 2 ^ (64 * t + 64) := by ring
    have h_le' : 2 ^ 8192 ≤ H * 2 ^ (64 * t + 64) + M * 2 ^ (64 * t) + L := by
      rw [← h_box_eq]
      exact hb
    have h_pow_eq : 2 ^ 8192 = 2 ^ (64 * t + 64) * 2 ^ (8192 - (64 * t + 64)) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' h_bound]
    rw [h_pow_eq] at h_le'

    have h_le : 2 ^ (64 * t + 64) * 2 ^ (8192 - (64 * t + 64)) ≤ H * 2 ^ (64 * t + 64) + (M * 2 ^ (64 * t) + L) := by
      simpa [add_assoc] using h_le'
    have h_combined : 2 ^ (64 * t + 64) * 2 ^ (8192 - (64 * t + 64)) < (H + 1) * 2 ^ (64 * t + 64) :=
      lt_of_le_of_lt h_le h_lt

    have h_pow_ineq : 2 ^ (8192 - (64 * t + 64)) * 2 ^ (64 * t + 64) < (H + 1) * 2 ^ (64 * t + 64) := by
      rw [Nat.mul_comm (2 ^ (8192 - (64 * t + 64))) (2 ^ (64 * t + 64))]
      exact h_combined

    have h_cancel : 2 ^ (8192 - (64 * t + 64)) < H + 1 :=
      Nat.lt_of_mul_lt_mul_right h_pow_ineq
    omega

  have h_sub_nonneg : M * 2 ^ (64 * t) ≤ box := by
    have hM_le_div : M ≤ box / 2 ^ (64 * t) := by
      rw [hM_def, bnd, bits]
      exact Nat.mod_le _ _
    calc
      M * 2 ^ (64 * t) ≤ (box / 2 ^ (64 * t)) * 2 ^ (64 * t) := Nat.mul_le_mul_right _ hM_le_div
      _ ≤ box := Nat.div_mul_le_self _ _
  have h_sub_eq : box - M * 2 ^ (64 * t) = H * 2 ^ (64 * t + 64) + L := by
    rw [h_box_eq]
    calc
      (H * 2 ^ (64 * t + 64) + M * 2 ^ (64 * t) + L) - M * 2 ^ (64 * t) =
          ((H * 2 ^ (64 * t + 64) + L) + M * 2 ^ (64 * t)) - M * 2 ^ (64 * t) := by ring_nf
      _ = H * 2 ^ (64 * t + 64) + L := by rw [Nat.add_sub_cancel_right]
  calc
    2 ^ 8192 = 2 ^ (64 * t + 64) * 2 ^ (8192 - (64 * t + 64)) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' h_bound]
    _ ≤ 2 ^ (64 * t + 64) * H := Nat.mul_le_mul_left _ hH_ineq
    _ = H * 2 ^ (64 * t + 64) := by ring
    _ ≤ H * 2 ^ (64 * t + 64) + L + w * 2 ^ (64 * t) := by omega
    _ = (H * 2 ^ (64 * t + 64) + L) + w * 2 ^ (64 * t) := by ring
    _ = (box - M * 2 ^ (64 * t)) + w * 2 ^ (64 * t) := by rw [h_sub_eq]
    _ = box - M * 2 ^ (64 * t) + w * 2 ^ (64 * t) := rfl
    _ = setBnd box t w := by rw [setBnd, hM_def]

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem setBnd_kernel (box t x : ℕ) :
    Nat.add (Nat.sub box (Nat.land box (Nat.shiftLeft 18446744073709551615 (64 * t))))
      (Nat.shiftLeft x (64 * t)) = setBnd box t x := by
  rw [land_mask_shiftLeft, shl_eq]
  rfl

theorem bits_lt (x o w : ℕ) : bits x o w < 2 ^ w := Nat.mod_lt _ (by positivity)

end Tammes15.D3Kernel
