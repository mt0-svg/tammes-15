import Tammes15.D3Kernel.KForm

namespace Tammes15.D3Kernel.KForm

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel

def allBelowK (p : ℕ → Bool) (n : ℕ) : Bool :=
  @Nat.rec (fun _ => Bool) true (fun i ih => @Bool.rec (fun _ => Bool) false (p i) ih) n

def anyBelowK (p : ℕ → Bool) (n : ℕ) : Bool :=
  @Nat.rec (fun _ => Bool) false (fun i ih => @Bool.rec (fun _ => Bool) (p i) true ih) n

def countBelowK (p : ℕ → Bool) (n : ℕ) : ℕ :=
  @Nat.rec (fun _ => ℕ) 0 (fun i ih => Nat.add ih (@Bool.rec (fun _ => ℕ) 0 1 (p i))) n

def maxK (a b : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) a b (Nat.ble a b)

def minK (a b : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) b a (Nat.ble a b)

def faceK (g : ℕ) : ℕ := Nat.shiftRight g 64

def fstK (g : ℕ) : ℕ := Nat.shiftRight g 2112

theorem allBelowK_eq (p : ℕ → Bool) (n : ℕ) : allBelowK p n = (List.range n).all p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show @Bool.rec (fun _ => Bool) false (p n) (allBelowK p n) = _
    rw [List.range_succ, List.all_append, ← ih]
    cases allBelowK p n <;> simp

theorem anyBelowK_eq (p : ℕ → Bool) (n : ℕ) : anyBelowK p n = (List.range n).any p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show @Bool.rec (fun _ => Bool) (p n) true (anyBelowK p n) = _
    rw [List.range_succ, List.any_append, ← ih]
    cases anyBelowK p n <;> simp

theorem countBelowK_eq (p : ℕ → Bool) (n : ℕ) : countBelowK p n = (List.range n).countP p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.add (countBelowK p n) (@Bool.rec (fun _ => ℕ) 0 1 (p n)) = _
    rw [List.range_succ, List.countP_append, ← ih]
    cases h : p n <;> simp [h]

theorem ble_false {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) h

theorem maxK_eq (a b : ℕ) : maxK a b = max a b := by
  unfold maxK
  by_cases hab : a ≤ b
  · rw [Nat.ble_eq_true_of_le hab]
    exact (max_eq_right hab).symm
  · rw [ble_false hab]
    exact (max_eq_left (Nat.le_of_lt (Nat.lt_of_not_le hab))).symm

theorem minK_eq (a b : ℕ) : minK a b = min a b := by
  unfold minK
  by_cases hab : a ≤ b
  · rw [Nat.ble_eq_true_of_le hab]
    exact (min_eq_left hab).symm
  · rw [ble_false hab]
    exact (min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hab))).symm

theorem laneK_fst (g i : ℕ) (hi : i < 256) : laneK (fstK g) i = (Ctx.code g).fstAt i := by
  rw [laneK_eq]
  show ((g >>> 2112) >>> (8 * i)) % 256 = ((g / 2 ^ 2112 % 2 ^ 2048) >>> (8 * i)) % 256
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · have h : 8 * i + j < 2048 := by omega
    simp only [hj, h, decide_true, Bool.true_and]
    rw [Nat.add_comm 2112]
  · simp [hj]

theorem laneK_faceK (g i : ℕ) (hi : i < 256) : laneK (faceK g) i = (Ctx.code g).faceAt i :=
  laneK_face g i hi

end Tammes15.D3Kernel.KForm
