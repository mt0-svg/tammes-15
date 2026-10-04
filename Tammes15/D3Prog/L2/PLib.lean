import Tammes15.D3Prog.Sem
import Tammes15.D3Prog.L2.Defs

namespace D3Prog.L2

open D3Ck2Spec

theorem scArg_eq (x : ℕ) : scArg x = scI (sv x) := by
  unfold scArg scI sv
  split_ifs with h1 h2 h2 <;> push_cast at * <;> omega

theorem p_sin {x : ℕ} {V : ℤ} (h : V = (sc28pS (scArg x)).1) : V = sinI (sv x) := by
  rw [h, scArg_eq]; rfl

theorem p_cos {x : ℕ} {V : ℤ} (h : V = (sc28pS (scArg x)).2) : V = cosI (sv x) := by
  rw [h, scArg_eq]; rfl

theorem p_sel {v m a b : ℕ} (h : v = if m = 1 then a else b) : sv v = if m = 1 then sv a else sv b := by
  rw [h]; split_ifs <;> rfl

theorem p_hint {v H s : ℕ} (h : sv v = ((H / 2 ^ s % 2 ^ 30 : ℕ) : ℤ)) : 0 ≤ sv v := by
  rw [h]; positivity

theorem p_sqrt {v w : ℕ} (h : sv v = ((Nat.sqrt (w - 4611686018427387904) : ℕ) : ℤ)) :
    sv v = ((Int.toNat (sv w)).sqrt : ℤ) := by
  have e : Int.toNat (sv w) = w - 4611686018427387904 := by unfold sv; omega
  rw [h, e]

theorem p_add_comm {V A B : ℤ} (h : V = B + A) : V = A + B := by rw [h, add_comm]

theorem p_mul_comm {V A B : ℤ} (h : V = B * A) : V = A * B := by rw [h, mul_comm]

theorem p_and_comm {v a b : ℕ} (h : v = 1 ↔ b = 1 ∧ a = 1) : v = 1 ↔ a = 1 ∧ b = 1 := by rw [h, and_comm]

theorem p_or_comm {v a b : ℕ} (h : v = 1 ↔ b = 1 ∨ a = 1) : v = 1 ↔ a = 1 ∨ b = 1 := by rw [h, or_comm]

theorem p_addc {V A C : ℤ} (k : ℤ) (h : V = A + C) (hc : C = k) : V = A + k := by rw [h, hc]

theorem p_neg {V Z A : ℤ} (hz : Z = 0) (h : V = Z - A) : V = -A := by rw [h, hz, zero_sub]

theorem p_le {o l : ℕ} {A B : ℤ} (hl : l = 1 ↔ B < A) (ho : o = 1 ↔ ¬l = 1) : o = 1 ↔ A ≤ B := by
  rw [ho, hl, not_lt]

theorem p_ltc {o : ℕ} {A C : ℤ} (k : ℤ) (hc : C = k) (h : o = 1 ↔ A < C) : o = 1 ↔ A < k := hc ▸ h

theorem p_clt {o : ℕ} {A C : ℤ} (k : ℤ) (hc : C = k) (h : o = 1 ↔ C < A) : o = 1 ↔ k < A := hc ▸ h

theorem p_max {l : ℕ} {V A B : ℤ} (hl : l = 1 ↔ A < B) (hv : V = if l = 1 then B else A) : V = max A B := by
  rw [hv]; split_ifs with h
  · rw [max_eq_right (hl.1 h).le]
  · rw [max_eq_left (not_lt.1 (fun h' => h (hl.2 h')))]

theorem p_min {l : ℕ} {V A B : ℤ} (hl : l = 1 ↔ A < B) (hv : V = if l = 1 then A else B) : V = min A B := by
  rw [hv]; split_ifs with h
  · rw [min_eq_left (hl.1 h).le]
  · rw [min_eq_right (not_lt.1 (fun h' => h (hl.2 h')))]

theorem p_mul {P V A B : ℤ} (hp : P = A * B) (hv : V = P / 2 ^ 28) : V = A * B / 2 ^ 28 := by rw [hv, hp]

theorem p_mulc {P V A B : ℤ} (hp : P = A * B) (hv : V = -((-P) / 2 ^ 28)) : V = -(-(A * B) / 2 ^ 28) := by
  rw [hv, hp]

theorem p_add_cc {V A B : ℤ} (k a b : ℤ) (hv : V = k) (ha : A = a) (hb : B = b) (h : k = a + b) : V = A + B := by
  rw [hv, ha, hb, h]

theorem p_sub_cc {V A B : ℤ} (k a b : ℤ) (hv : V = k) (ha : A = a) (hb : B = b) (h : k = a - b) : V = A - B := by
  rw [hv, ha, hb, h]

theorem p_add_0l {A B : ℤ} (ha : A = 0) : B = A + B := by rw [ha, zero_add]

theorem p_add_0r {A B : ℤ} (hb : B = 0) : A = A + B := by rw [hb, add_zero]

theorem p_sub_0r {A B : ℤ} (hb : B = 0) : A = A - B := by rw [hb, sub_zero]

theorem p_half_cc {V A : ℤ} (k a : ℤ) (hv : V = k) (ha : A = a) (h : k = a / 2) : V = A / 2 := by rw [hv, ha, h]

theorem p_halfc_cc {V A : ℤ} (k a : ℤ) (hv : V = k) (ha : A = a) (h : k = (a + 1) / 2) : V = (A + 1) / 2 := by
  rw [hv, ha, h]

theorem p_sin_cc {V X : ℤ} (k x : ℤ) (hv : V = k) (hx : X = x) (h : sinI x = k) : V = sinI X := by
  rw [hv, hx, h]

theorem p_cos_cc {V X : ℤ} (k x : ℤ) (hv : V = k) (hx : X = x) (h : cosI x = k) : V = cosI X := by
  rw [hv, hx, h]

theorem p_lt_cc {v : ℕ} {A B : ℤ} (a b : ℤ) (ha : A = a) (hb : B = b) (h : v = 1 ↔ a < b) : v = 1 ↔ A < B := by
  rw [ha, hb]; exact h

theorem p_lt_self (A : ℤ) : (0 : ℕ) = 1 ↔ A < A := by simp

theorem p_not_not {a x : ℕ} (ha : a = 1 ↔ ¬x = 1) : x = 1 ↔ ¬a = 1 := by rw [ha, not_not]

theorem p_and_f1 (b : ℕ) : (0 : ℕ) = 1 ↔ (0 : ℕ) = 1 ∧ b = 1 := by simp

theorem p_and_f2 (a : ℕ) : (0 : ℕ) = 1 ↔ a = 1 ∧ (0 : ℕ) = 1 := by simp

theorem p_and_t1 (b : ℕ) : b = 1 ↔ (1 : ℕ) = 1 ∧ b = 1 := by simp

theorem p_and_t2 (a : ℕ) : a = 1 ↔ a = 1 ∧ (1 : ℕ) = 1 := by simp

theorem p_and_self (a : ℕ) : a = 1 ↔ a = 1 ∧ a = 1 := by simp

theorem p_or_t1 (b : ℕ) : (1 : ℕ) = 1 ↔ (1 : ℕ) = 1 ∨ b = 1 := by simp

theorem p_or_t2 (a : ℕ) : (1 : ℕ) = 1 ↔ a = 1 ∨ (1 : ℕ) = 1 := by simp

theorem p_or_f1 (b : ℕ) : b = 1 ↔ (0 : ℕ) = 1 ∨ b = 1 := by simp

theorem p_or_f2 (a : ℕ) : a = 1 ↔ a = 1 ∨ (0 : ℕ) = 1 := by simp

theorem p_or_self (a : ℕ) : a = 1 ↔ a = 1 ∨ a = 1 := by simp

theorem p_ult (A B : ℤ) : ((if A < B then 1 else 0 : ℕ) = 1 ↔ A < B) := by split_ifs with h <;> simp [h]

theorem p_uand (a b : ℕ) : ((if a = 1 ∧ b = 1 then 1 else 0 : ℕ) = 1 ↔ a = 1 ∧ b = 1) := by
  split_ifs with h <;> simp [h]

theorem p_uor (a b : ℕ) : ((if a = 1 ∨ b = 1 then 1 else 0 : ℕ) = 1 ↔ a = 1 ∨ b = 1) := by
  split_ifs with h <;> simp [h]

theorem p_unot (a : ℕ) : ((if a = 1 then 0 else 1 : ℕ) = 1 ↔ ¬a = 1) := by split_ifs with h <;> simp [h]

theorem p_sel_same {α : Type} (m : ℕ) (a : α) : a = if m = 1 then a else a := (ite_self a).symm

theorem p_sel_t {α : Type} (a b : α) : a = if (1 : ℕ) = 1 then a else b := by simp

theorem p_sel_f {α : Type} (a b : α) : b = if (0 : ℕ) = 1 then a else b := by simp

end D3Prog.L2
