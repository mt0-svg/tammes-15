import Tammes15.D3Kernel.Assembly

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3Kernel Pent

def kgood (k : ℕ) : Bool :=
  Nat.ble (nat_lit 13785518459381088256) k && Nat.blt k (nat_lit 18442240474082181120)

def kfix (k : ℕ) : ℕ := Nat.shiftLeft (kman k) (Nat.sub (kexp k) (nat_lit 1013))

def nvK (g : ℕ) : ℕ := Nat.land (Nat.shiftRight g (nat_lit 16)) (nat_lit 255)

theorem kgood_spec {k : ℕ} (h : kgood k = true) :
    2 ^ 63 ≤ k ∧ 1013 ≤ kexp k ∧ kexp k < 2047 := by
  unfold kgood at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨hle, hlt⟩
  have hle' : 13785518459381088256 ≤ k := by
    simpa using hle
  have hlt' : k < 18442240474082181120 := by
    simpa using hlt
  have hp63 : 2 ^ 63 ≤ k := by
    have : 2 ^ 63 ≤ 13785518459381088256 := by norm_num
    exact Nat.le_trans this hle'
  have hexp_eq : kexp k = (k - 2 ^ 63) / 2 ^ 52 % 2 ^ 11 :=
    kexp_eq hp63
  have hb_lower : 1013 * 2 ^ 52 ≤ k - 2 ^ 63 := by
    have : 13785518459381088256 = 2 ^ 63 + 1013 * 2 ^ 52 := by norm_num
    rw [this] at hle'
    omega
  have hb_upper : k - 2 ^ 63 < 2047 * 2 ^ 52 := by
    have : 18442240474082181120 = 2 ^ 63 + 2047 * 2 ^ 52 := by norm_num
    rw [this] at hlt'
    omega
  have hdiv_lt : (k - 2 ^ 63) / 2 ^ 52 < 2047 :=
    (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ 52)).mpr hb_upper
  have hdiv_ge : 1013 ≤ (k - 2 ^ 63) / 2 ^ 52 :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ 52)).mpr hb_lower
  have hmod : (k - 2 ^ 63) / 2 ^ 52 % 2 ^ 11 = (k - 2 ^ 63) / 2 ^ 52 :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le hdiv_lt (by norm_num : 2047 ≤ 2 ^ 11))
  rw [hexp_eq, hmod]
  exact And.intro hp63 (And.intro hdiv_ge hdiv_lt)

theorem keyVal_kgood {k : ℕ} (h : kgood k = true) : keyVal k = (kfix k : ℝ) / 2 ^ 62 := by
  obtain ⟨h1, h2, h3⟩ := kgood_spec h
  have he := kexp_eq h1
  have hm := kman_eq h1
  unfold keyVal
  simp only [ite_eq_left h1]
  rw [← he, ite_eq_right (by omega), ite_eq_right (by omega), ← hm]
  have hz : ((kexp k : ℤ) - 1075) = ((kexp k - 1013 : ℕ) : ℤ) - 62 := by omega
  have hf : kfix k = kman k * 2 ^ (kexp k - 1013) := shl_eq _ _
  rw [hz, zpow_sub₀ (by norm_num), zpow_natCast, hf]
  push_cast
  ring

theorem nvK_eq (g : ℕ) : nvK g = Ctx.nv g := land_shiftRight g 16 8

end Tammes15.D3Kernel.Kinds
