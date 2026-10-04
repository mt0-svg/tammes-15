import Tammes15.D3Kernel.Sound
import Tammes15.D3Kernel.PentLink
import Tammes15.D3Kernel.KForm

namespace Tammes15.D3Kernel.Pent

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Tammes15.D3Kernel.KForm

def kexp (k : ℕ) : ℕ := Nat.land (Nat.shiftRight k (nat_lit 52)) (nat_lit 2047)

def kman (k : ℕ) : ℕ := Nat.add (Nat.land k (nat_lit 4503599627370495)) (nat_lit 4503599627370496)

def kfl (k : ℕ) : ℕ := Nat.shiftRight (kman k) (Nat.sub (nat_lit 1051) (kexp k))

def kce (k : ℕ) : ℕ :=
  Nat.shiftRight (Nat.add (kman k) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 1051) (kexp k))) (nat_lit 1)))
    (Nat.sub (nat_lit 1051) (kexp k))

def kok (k : ℕ) : Bool :=
  Nat.ble (nat_lit 9223372036854775808) k && Nat.blt k (nat_lit 18446744073709551616) &&
    Nat.ble (nat_lit 1022) (kexp k) && Nat.ble (kexp k) (nat_lit 1024)

def kokK (k : ℕ) : Bool :=
  Nat.ble (nat_lit 3070) (Nat.shiftRight k (nat_lit 52)) && Nat.ble (Nat.shiftRight k (nat_lit 52)) (nat_lit 3072)

def fk (it o m : ℕ) : ℕ := Nat.land (Nat.shiftRight it o) m

def bk (box t : ℕ) : ℕ := Nat.land (Nat.shiftRight box (Nat.shiftLeft t (nat_lit 6))) (nat_lit 18446744073709551615)

def lf (box v : ℕ) : ℕ :=
  Nat.add (kfl (bk box (Nat.shiftLeft v 1)))
    (Nat.shiftLeft (kce (bk box (Nat.add (Nat.shiftLeft v 1) 1))) (nat_lit 32))

def claim (it : ℕ) : ℕ :=
  @Bool.rec (fun _ => ℕ) (kce (Nat.land it (nat_lit 18446744073709551615)))
    (kfl (Nat.land it (nat_lit 18446744073709551615))) (Nat.beq (fk it 64 1) 1)

def inDomB (F0 F1 F2 F3 : ℕ) : Bool :=
  Nat.blt F0 18446744073709551616 && Nat.blt F1 18446744073709551616 && Nat.blt F2 18446744073709551616 &&
  Nat.blt F3 4294967296 &&
  Nat.ble 15099495 (F0 % 4294967296) && Nat.ble (F0 / 4294967296 % 4294967296) 16777216 &&
  Nat.ble 18454938 (F1 % 4294967296) && Nat.ble (F1 / 4294967296 % 4294967296) 53687091 &&
  Nat.ble 18454938 (F2 % 4294967296) && Nat.ble (F2 / 4294967296 % 4294967296) 53687091

def jx (s : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 1 4 (Nat.beq s 2)
def jy (s : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 4 1 (Nat.beq s 2)
def jo (s : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) (@Bool.rec (fun _ => ℕ) 0 2 (Nat.beq s 1)) 3 (Nat.beq s 2)

def okP (k : Fin 2) (hi : Bool) (g box it : ℕ) : Bool :=
  let c := Ctx.code g
  let e := fk it 75 127
  let s := fk it 82 7
  let t := fk it 64 127
  let o := Nat.shiftRight t 1
  let xv := fk it 85 63
  let yv := fk it 91 63
  let dv := fk it 97 63
  let nv := Ctx.nv g
  Nat.blt e c.D && Nat.beq (c.period e) 5 && Nat.ble s 2 &&
  Nat.beq (k : ℕ) (@Bool.rec (fun _ => ℕ) 1 0 (Nat.beq s 0)) &&
  Nat.beq (Nat.land t 1) (@Bool.rec (fun _ => ℕ) 0 1 hi) &&
  Nat.blt dv nv && Nat.blt xv nv && Nat.blt yv nv && Nat.blt o nv &&
  Nat.beq (Ctx.mean g dv) 1 &&
  Nat.beq (Ctx.mean g xv) (2 + c.faceIter e (jx s)) &&
  Nat.beq (Ctx.mean g yv) (2 + c.faceIter e (jy s)) &&
  Nat.beq (Ctx.mean g o) (2 + c.faceIter e (jo s)) &&
  kok (bk box (2 * dv)) && kok (bk box (2 * dv + 1)) && kok (bk box (2 * xv)) && kok (bk box (2 * xv + 1)) &&
  kok (bk box (2 * yv)) && kok (bk box (2 * yv + 1)) && kok (Nat.land it 18446744073709551615) &&
  inDomB (lf box dv) (lf box xv) (lf box yv) (claim it)

def inDomBK (F0 F1 F2 F3 : ℕ) : Bool :=
  Nat.blt F0 18446744073709551616 && Nat.blt F1 18446744073709551616 && Nat.blt F2 18446744073709551616 &&
  Nat.blt F3 4294967296 &&
  Nat.ble 15099495 (Nat.land F0 4294967295) && Nat.ble (Nat.land (Nat.shiftRight F0 32) 4294967295) 16777216 &&
  Nat.ble 18454938 (Nat.land F1 4294967295) && Nat.ble (Nat.land (Nat.shiftRight F1 32) 4294967295) 53687091 &&
  Nat.ble 18454938 (Nat.land F2 4294967295) && Nat.ble (Nat.land (Nat.shiftRight F2 32) 4294967295) 53687091

def okPK (k : Fin 2) (hi : Bool) (g box it : ℕ) : Bool :=
  let face := Nat.shiftRight g 64
  let e := fk it 75 127
  let s := fk it 82 7
  let t := fk it 64 127
  let o := Nat.shiftRight t 1
  let xv := fk it 85 63
  let yv := fk it 91 63
  let dv := fk it 97 63
  let nv := nvCK g
  Nat.blt e (DK g) && Nat.beq (periodK face e) 5 && Nat.ble s 2 &&
  Nat.beq (k : ℕ) (@Bool.rec (fun _ => ℕ) 1 0 (Nat.beq s 0)) &&
  Nat.beq (Nat.land t 1) (@Bool.rec (fun _ => ℕ) 0 1 hi) &&
  Nat.blt dv nv && Nat.blt xv nv && Nat.blt yv nv && Nat.blt o nv &&
  Nat.beq (meanK g dv) 1 &&
  Nat.beq (meanK g xv) (Nat.add 2 (iterK face e (jx s))) &&
  Nat.beq (meanK g yv) (Nat.add 2 (iterK face e (jy s))) &&
  Nat.beq (meanK g o) (Nat.add 2 (iterK face e (jo s))) &&
  kokK (bk box (Nat.shiftLeft dv 1)) && kokK (bk box (Nat.add (Nat.shiftLeft dv 1) 1)) &&
  kokK (bk box (Nat.shiftLeft xv 1)) && kokK (bk box (Nat.add (Nat.shiftLeft xv 1) 1)) &&
  kokK (bk box (Nat.shiftLeft yv 1)) && kokK (bk box (Nat.add (Nat.shiftLeft yv 1) 1)) &&
  kokK (Nat.land it 18446744073709551615) &&
  inDomBK (lf box dv) (lf box xv) (lf box yv) (claim it)

abbrev Prog := ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → ℕ

def ProgOK (k : Fin 2) (hi : Bool) (prog : Prog) : Prop :=
  ∀ (n F0 F1 F2 F3 : ℕ) (hs : List ℕ) (v : ℕ),
    (∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) →
      Nat.beq (prog (oN n) F0 F1 F2 F3 hs) v = true → ∀ l < n, lane v l = 1 →
        LaneClaim k hi (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)

def progChecker (k : Fin 2) (hi : Bool) (prog : Prog) : Checker where
  σ := ℕ × ℕ × ℕ × ℕ × ℕ × Bool
  H := List ℕ
  init := (0, 0, 0, 0, 0, true)
  onRec g box it s :=
    let sh := Nat.shiftLeft s.1 (nat_lit 6)
    (Nat.add s.1 1,
      Nat.add s.2.1 (Nat.shiftLeft (lf box (fk it 97 63)) sh),
      Nat.add s.2.2.1 (Nat.shiftLeft (lf box (fk it 85 63)) sh),
      Nat.add s.2.2.2.1 (Nat.shiftLeft (lf box (fk it 91 63)) sh),
      Nat.add s.2.2.2.2.1 (Nat.shiftLeft (claim it) sh),
      s.2.2.2.2.2 && okPK k hi g box it)
  onKill _ _ _ s := (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, false)
  fin s hs := s.2.2.2.2.2 && Nat.beq (prog (oN s.1) s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 hs) (oN s.1)
  frc s k := @Bool.rec (fun _ => List ℕ) (k s) (k s)
    (Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0)
  frc_eq s k := by
    cases Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0 <;> rfl

def pIdx (it : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.shiftLeft (fk it 121 3) 2)
    (Nat.shiftLeft (@Bool.rec (fun _ => ℕ) 1 0 (Nat.beq (fk it 82 7) 0)) 1)) (fk it 64 1)

def kOf (i : ℕ) : Fin 2 := if i / 2 % 2 = 0 then 0 else 1

def hiOf (i : ℕ) : Bool := i % 2 == 1

def btree (f : ℕ → Checker) (key : ℕ → ℕ) : ℕ → ℕ → Checker
  | 0, i => f i
  | d + 1, i => Checker.pair (fun it => Nat.beq (Nat.land (Nat.shiftRight (key it) d) 1) 0)
      (btree f key d i) (btree f key d (i + 2 ^ d))

def pentChecker (progs : ℕ → Prog) : Checker :=
  btree (fun i => if i < 12 then progChecker (kOf i) (hiOf i) (progs i) else Checker.none) pIdx 4 0

theorem kok_spec {k : ℕ} (h : kok k = true) :
    2 ^ 63 ≤ k ∧ k < 2 ^ 64 ∧ 1022 ≤ kexp k ∧ kexp k ≤ 1024 := by
  have h_all : ((Nat.ble 9223372036854775808 k = true ∧ Nat.blt k 18446744073709551616 = true) ∧
    Nat.ble 1022 (kexp k) = true) ∧ Nat.ble (kexp k) 1024 = true := by
    simpa [kok] using h
  refine ⟨?_, ?_, (Nat.ble_eq (x := 1022) (y := kexp k)).mp h_all.1.2,
    (Nat.ble_eq (x := kexp k) (y := 1024)).mp h_all.2⟩
  · have := (Nat.ble_eq (x := 9223372036854775808) (y := k)).mp h_all.1.1.1
    norm_num
    exact this
  · have := (Nat.blt_eq (x := k) (y := 18446744073709551616)).mp h_all.1.1.2
    norm_num
    exact this

private theorem p63 : (2 : ℕ) ^ 11 * 2 ^ 52 = 2 ^ 63 := by norm_num

theorem kexp_eq {k : ℕ} (h : 2 ^ 63 ≤ k) : kexp k = (k - 2 ^ 63) / 2 ^ 52 % 2 ^ 11 := by
  have e : kexp k = bits k 52 11 := land_shiftRight k 52 11
  rw [e]
  unfold bits
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 2 ^ 11 * 2 ^ 52 :=
    ⟨k - 2 ^ 63, by rw [p63]; exact (Nat.sub_add_cancel h).symm⟩
  rw [p63, Nat.add_sub_cancel, ← p63, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mod_right]

theorem kman_eq {k : ℕ} (h : 2 ^ 63 ≤ k) : kman k = 2 ^ 52 + (k - 2 ^ 63) % 2 ^ 52 := by
  have e : Nat.land k 4503599627370495 = bits k 0 52 := land_shiftRight k 0 52
  unfold kman
  show Nat.land k 4503599627370495 + 4503599627370496 = _
  rw [e]
  unfold bits
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 2 ^ 11 * 2 ^ 52 :=
    ⟨k - 2 ^ 63, by rw [p63]; exact (Nat.sub_add_cancel h).symm⟩
  rw [p63, Nat.add_sub_cancel, ← p63, pow_zero, Nat.div_one, Nat.add_mul_mod_self_right, add_comm]
  norm_num

theorem kfl_eq (k : ℕ) : kfl k = kman k / 2 ^ (1051 - kexp k) := by
  unfold kfl
  exact Nat.shiftRight_eq_div_pow _ _

theorem kce_eq (k : ℕ) : kce k = (kman k + 2 ^ (1051 - kexp k) - 1) / 2 ^ (1051 - kexp k) := by
  unfold kce
  show (kman k + (1 <<< (1051 - kexp k) - 1)) >>> (1051 - kexp k) = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow,
    ← Nat.add_sub_assoc (Nat.one_le_two_pow)]

theorem keyVal_kok {k : ℕ} (h : kok k = true) :
    keyVal k = (kman k : ℝ) / 2 ^ (1051 - kexp k) / 2 ^ 24 := by
  obtain ⟨h1, -, h3, h4⟩ := kok_spec h
  have he := kexp_eq h1
  have hm := kman_eq h1
  unfold keyVal
  simp only [ite_eq_left h1]
  rw [← he, ite_eq_right (by omega), ite_eq_right (by omega), ← hm]
  have hz : ((kexp k : ℤ) - 1075) = -((1051 - kexp k + 24 : ℕ) : ℤ) := by omega
  rw [hz, zpow_neg, zpow_natCast, pow_add, div_div, div_eq_mul_inv]

theorem kfl_le {k : ℕ} (h : kok k = true) : (kfl k : ℝ) / 2 ^ 24 ≤ keyVal k := by
  rw [keyVal_kok h, kfl_eq]
  gcongr
  have := Nat.cast_div_le (α := ℝ) (m := kman k) (n := 2 ^ (1051 - kexp k))
  push_cast at this
  exact this

theorem le_kce {k : ℕ} (h : kok k = true) : keyVal k ≤ (kce k : ℝ) / 2 ^ 24 := by
  rw [keyVal_kok h, kce_eq]
  gcongr
  generalize 1051 - kexp k = s
  generalize kman k = M
  have hP : 0 < 2 ^ s := by positivity
  have hle : M ≤ (M + 2 ^ s - 1) / 2 ^ s * 2 ^ s := by
    have hd := Nat.div_add_mod (M + 2 ^ s - 1) (2 ^ s)
    have hr := Nat.mod_lt (M + 2 ^ s - 1) hP
    generalize (M + 2 ^ s - 1) / 2 ^ s = q at hd ⊢
    generalize (M + 2 ^ s - 1) % 2 ^ s = r at hd hr
    rw [mul_comm] at hd
    generalize 2 ^ s = P at hP hd hr ⊢
    generalize q * P = X at hd ⊢
    omega
  rw [div_le_iff₀ (by positivity)]
  exact_mod_cast hle

theorem kce_lt {k : ℕ} (h : kok k = true) : kce k < 2 ^ 27 ∧ kfl k < 2 ^ 27 := by

  have h_all : ((Nat.ble 9223372036854775808 k = true ∧ Nat.blt k 18446744073709551616 = true) ∧
    Nat.ble 1022 (kexp k) = true) ∧ Nat.ble (kexp k) 1024 = true := by
    simpa [kok] using h
  have hk_ge : 9223372036854775808 ≤ k :=
    (Nat.ble_eq (x := 9223372036854775808) (y := k)).mp (h_all.1.1.1)
  have hk_lt : k < 18446744073709551616 :=
    (Nat.blt_eq (x := k) (y := 18446744073709551616)).mp (h_all.1.1.2)
  have h_exp_lo : 1022 ≤ kexp k :=
    (Nat.ble_eq (x := 1022) (y := kexp k)).mp (h_all.1.2)
  have h_exp_hi : kexp k ≤ 1024 :=
    (Nat.ble_eq (x := kexp k) (y := 1024)).mp (h_all.2)

  have h_man_lt : kman k < 2 ^ 53 := by
    rw [kman]
    have h_land : Nat.land k 4503599627370495 ≤ 4503599627370495 := by
      rw [Nat.land_eq]
      exact Nat.and_le_right
    have h_sum : (Nat.land k 4503599627370495) + 4503599627370496 ≤
        4503599627370495 + 4503599627370496 := Nat.add_le_add_right h_land _
    have h_eq : 4503599627370495 + 4503599627370496 = 2 ^ 53 - 1 := by norm_num
    rw [h_eq] at h_sum
    have : 2 ^ 53 - 1 < 2 ^ 53 := Nat.sub_lt (by norm_num) (by norm_num)
    exact lt_of_le_of_lt h_sum this

  have h_shift_ge : 27 ≤ 1051 - kexp k := by
    have h_le : kexp k ≤ 1051 := by

      exact Nat.le_trans h_exp_hi (by norm_num)
    apply ((Nat.le_sub_iff_add_le h_le).mpr ?_)

    omega
  have h_pow_sub_ge : 2 ^ 27 ≤ 2 ^ (1051 - kexp k) :=
    Nat.pow_le_pow_right (by norm_num) h_shift_ge
  have h_div_lt : kman k / 2 ^ (1051 - kexp k) < 2 ^ 26 := by
    apply (Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) _)).mpr
    have : 2 ^ 26 * 2 ^ 27 ≤ 2 ^ 26 * 2 ^ (1051 - kexp k) :=
      Nat.mul_le_mul_left _ h_pow_sub_ge
    have h_pow_mul : 2 ^ 26 * 2 ^ 27 = 2 ^ 53 := by ring
    rw [h_pow_mul] at this
    exact lt_of_lt_of_le h_man_lt this
  have h_fl_lt : kfl k < 2 ^ 27 := by
    rw [kfl]

    have := Nat.shiftRight_eq_div_pow (kman k) (1051 - kexp k)

    have h_pow_le : 2 ^ 26 ≤ 2 ^ 27 :=
      Nat.pow_le_pow_right (by norm_num) (show 26 ≤ 27 from by norm_num)
    simpa [Nat.shiftRight_eq_div_pow] using
      lt_of_lt_of_le h_div_lt h_pow_le
  have h_ce_lt : kce k < 2 ^ 27 := by

    set t := 1051 - kexp k with ht
    have h_shiftLeft_pow : Nat.shiftLeft 1 t = 2 ^ t := by
      induction' t with t ih
      · rfl
      · have h := congrArg (fun x => 2 * x) ih
        simpa [Nat.shiftLeft_succ, pow_succ, mul_comm, add_comm] using h
    have h_target : kce k = (kman k + 2 ^ t - 1) / 2 ^ t := by
      rw [kce]
      calc
        (Nat.add (kman k) (Nat.sub (Nat.shiftLeft 1 (Nat.sub 1051 (kexp k))) 1)).shiftRight
            (Nat.sub 1051 (kexp k))
            = ((kman k + (Nat.shiftLeft 1 (1051 - kexp k) - 1)) >>> (1051 - kexp k)) := by simp
        _ = ((kman k + (Nat.shiftLeft 1 t - 1)) >>> t) := by simp [ht]
        _ = ((kman k + (2 ^ t - 1)) >>> t) := by
          simp [Nat.shiftLeft_eq]
        _ = (kman k + 2 ^ t - 1) / 2 ^ t := by
          have h : 1 ≤ 2 ^ t := by
            apply Nat.one_le_two_pow
          simp [Nat.add_sub_assoc h, Nat.shiftRight_eq_div_pow]
    rw [h_target]
    have ht_pos : 0 < 2 ^ t := pow_pos (by norm_num) t
    have h_sub_le : kman k + 2 ^ t - 1 ≤ kman k + 2 ^ t := by omega
    have h_div_le : (kman k + 2 ^ t - 1) / 2 ^ t ≤ (kman k + 2 ^ t) / 2 ^ t :=
      Nat.div_le_div_right h_sub_le
    have h_add_div : (kman k + 2 ^ t) / 2 ^ t = kman k / 2 ^ t + 1 :=
      Nat.add_div_right _ ht_pos
    rw [h_add_div] at h_div_le
    have h_div_lt_t : kman k / 2 ^ t < 2 ^ 26 := by
      apply (Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) _)).mpr
      have h_pow_t : 2 ^ 27 ≤ 2 ^ t := by
        rw [ht]
        exact h_pow_sub_ge
      have : 2 ^ 26 * 2 ^ 27 ≤ 2 ^ 26 * 2 ^ t :=
        Nat.mul_le_mul_left _ h_pow_t
      have h_pow_mul : 2 ^ 26 * 2 ^ 27 = 2 ^ 53 := by ring
      rw [h_pow_mul] at this
      exact lt_of_lt_of_le h_man_lt this
    have h_lt : kman k / 2 ^ t + 1 < 2 ^ 27 := by
      have h_pow_lt : 2 ^ 26 < 2 ^ 27 :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h_sum : kman k / 2 ^ t + 1 < 2 ^ 26 + 1 :=
        Nat.add_lt_add_right h_div_lt_t 1
      have : 2 ^ 26 + 1 ≤ 2 ^ 27 := by omega
      exact lt_of_lt_of_le h_sum this
    exact lt_of_le_of_lt h_div_le h_lt
  exact And.intro h_ce_lt h_fl_lt

theorem inDomB_sound {F0 F1 F2 F3 : ℕ} (h : inDomB F0 F1 F2 F3 = true) : InDom F0 F1 F2 F3 := by

  have h_all : ((((((((F0 < 18446744073709551616 ∧ F1 < 18446744073709551616) ∧
    F2 < 18446744073709551616) ∧ F3 < 4294967296) ∧
    15099495 ≤ F0 % 4294967296) ∧ F0 / 4294967296 % 4294967296 ≤ 16777216) ∧
    18454938 ≤ F1 % 4294967296) ∧ F1 / 4294967296 % 4294967296 ≤ 53687091) ∧
    18454938 ≤ F2 % 4294967296) ∧ F2 / 4294967296 % 4294967296 ≤ 53687091 := by
    simpa [inDomB] using h
  rcases h_all with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hF0_lt, hF1_lt⟩, hF2_lt⟩, hF3_lt⟩, hF0_mod_lo⟩, hF0_div_hi⟩, hF1_mod_lo⟩, hF1_div_hi⟩, hF2_mod_lo⟩, hF2_div_hi⟩

  unfold InDom
  have h2pow64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have h2pow32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ 24 := by norm_num
  refine ⟨by simpa [h2pow64] using hF0_lt, by simpa [h2pow64] using hF1_lt, by simpa [h2pow64] using hF2_lt,
    by simpa [h2pow32] using hF3_lt,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    unfold fld
    have h_base : (0.9 : ℝ) ≤ (15099495 : ℝ) / ((2 : ℝ) ^ 24) := by norm_num
    have h_cast : (15099495 : ℝ) ≤ ((F0 % 4294967296 : ℕ) : ℝ) := by exact_mod_cast hF0_mod_lo
    have h_div : (15099495 : ℝ) / ((2 : ℝ) ^ 24) ≤ ((F0 % 4294967296 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) :=
      div_le_div_of_nonneg_right h_cast hpos
    simpa [show (2 : ℕ) ^ 0 = 1 by norm_num, h2pow32] using le_trans h_base h_div
  ·
    unfold fld
    have h_cast : ((F0 / 4294967296 % 4294967296 : ℕ) : ℝ) ≤ (16777216 : ℝ) := by exact_mod_cast hF0_div_hi
    have h_div : (16777216 : ℝ) / ((2 : ℝ) ^ 24) = (1 : ℝ) := by norm_num
    have h_le : ((F0 / 4294967296 % 4294967296 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) ≤ (16777216 : ℝ) / ((2 : ℝ) ^ 24) :=
      div_le_div_of_nonneg_right h_cast hpos
    simpa [h2pow32] using le_trans h_le (by rw [h_div])
  ·
    unfold fld
    have h_base : (1.1 : ℝ) ≤ (18454938 : ℝ) / ((2 : ℝ) ^ 24) := by norm_num
    have h_cast : (18454938 : ℝ) ≤ ((F1 % 4294967296 : ℕ) : ℝ) := by exact_mod_cast hF1_mod_lo
    have h_div : (18454938 : ℝ) / ((2 : ℝ) ^ 24) ≤ ((F1 % 4294967296 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) :=
      div_le_div_of_nonneg_right h_cast hpos
    simpa [show (2 : ℕ) ^ 0 = 1 by norm_num, h2pow32] using le_trans h_base h_div
  ·
    unfold fld
    have h_cast : ((F1 / 4294967296 % 4294967296 : ℕ) : ℝ) ≤ (53687091 : ℝ) := by exact_mod_cast hF1_div_hi
    have h_div : (53687091 : ℝ) / ((2 : ℝ) ^ 24) ≤ (3.2 : ℝ) := by norm_num
    have h_le : ((F1 / 4294967296 % 4294967296 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) ≤ (53687091 : ℝ) / ((2 : ℝ) ^ 24) :=
      div_le_div_of_nonneg_right h_cast hpos
    simpa [h2pow32] using le_trans h_le h_div
  ·
    unfold fld
    have h_base : (1.1 : ℝ) ≤ (18454938 : ℝ) / ((2 : ℝ) ^ 24) := by norm_num
    have h_cast : (18454938 : ℝ) ≤ ((F2 % 4294967296 : ℕ) : ℝ) := by exact_mod_cast hF2_mod_lo
    have h_div : (18454938 : ℝ) / ((2 : ℝ) ^ 24) ≤ ((F2 % 4294967296 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) :=
      div_le_div_of_nonneg_right h_cast hpos
    simpa [show (2 : ℕ) ^ 0 = 1 by norm_num, h2pow32] using le_trans h_base h_div
  ·
    unfold fld
    have h_cast : ((F2 / 4294967296 % 4294967296 : ℕ) : ℝ) ≤ (53687091 : ℝ) := by exact_mod_cast hF2_div_hi
    have h_div : (53687091 : ℝ) / ((2 : ℝ) ^ 24) ≤ (3.2 : ℝ) := by norm_num
    have h_le : ((F2 / 4294967296 % 4294967296 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) ≤ (53687091 : ℝ) / ((2 : ℝ) ^ 24) :=
      div_le_div_of_nonneg_right h_cast hpos
    simpa [h2pow32] using le_trans h_le h_div

theorem lane_append (F f n i : ℕ) (hF : F < 2 ^ (64 * n)) (hf : f < 2 ^ 64) :
    lane (F + f * 2 ^ (64 * n)) i = if i < n then lane F i else if i = n then f else 0 := by
  unfold lane
  by_cases hi : i < n
  ·
    have h_le : 64 * i ≤ 64 * n := Nat.mul_le_mul_left 64 (Nat.le_of_lt hi)
    have h_pow_dvd : 2 ^ (64 * i) ∣ 2 ^ (64 * n) := Nat.pow_dvd_pow 2 h_le
    have h_dvd : 2 ^ (64 * i) ∣ f * 2 ^ (64 * n) :=
      Nat.dvd_trans h_pow_dvd (Nat.dvd_mul_left (2 ^ (64 * n)) f)
    rw [Nat.add_div_of_dvd_left h_dvd]
    have h_div : (f * 2 ^ (64 * n)) / 2 ^ (64 * i) = f * 2 ^ (64 * (n - i)) := by
      rw [Nat.mul_div_assoc f h_pow_dvd]
      rw [Nat.pow_div h_le (by norm_num : 0 < 2)]
      have h_sub : (64 * n) - (64 * i) = 64 * (n - i) := by
        rw [← Nat.mul_sub_left_distrib]
      rw [h_sub]
    rw [h_div]
    have h_mod : (f * 2 ^ (64 * (n - i))) % 2 ^ 64 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      have h_ge : 64 ≤ 64 * (n - i) := by
        have h_one : 1 ≤ n - i := by
          have h_succ : i + 1 ≤ n := Nat.succ_le_of_lt hi
          simpa [add_comm] using Nat.le_sub_of_add_le (by simpa [add_comm] using h_succ)
        nlinarith
      have h_pow_dvd2 : 2 ^ 64 ∣ 2 ^ (64 * (n - i)) := Nat.pow_dvd_pow 2 h_ge
      exact Nat.dvd_trans h_pow_dvd2 (Nat.dvd_mul_left (2 ^ (64 * (n - i))) f)
    rw [Nat.add_mod, h_mod, add_zero, Nat.mod_mod]
    simp [hi]
  ·
    by_cases heq : i = n
    ·
      rw [heq]
      have h_dvd : 2 ^ (64 * n) ∣ f * 2 ^ (64 * n) := Nat.dvd_mul_left (2 ^ (64 * n)) f
      rw [Nat.add_div_of_dvd_left h_dvd]
      have hFdiv : F / 2 ^ (64 * n) = 0 := Nat.div_eq_of_lt hF
      rw [hFdiv]
      have h_mul_div : (f * 2 ^ (64 * n)) / 2 ^ (64 * n) = f := by
        rw [Nat.mul_div_cancel f (by norm_num : 0 < 2 ^ (64 * n))]
      rw [h_mul_div]
      rw [Nat.zero_add]
      simpa [heq] using Nat.mod_eq_of_lt hf
    ·
      have hn_lt_i : n < i := by
        by_contra! h
        have hle : i ≤ n := h
        rcases Nat.lt_or_eq_of_le hle with (hlt | heq')
        · exact hi hlt
        · exact heq heq'
      have h_sum_lt : F + f * 2 ^ (64 * n) < 2 ^ (64 * i) :=
      calc
        F + f * 2 ^ (64 * n) < 2 ^ (64 * n) + f * 2 ^ (64 * n) :=
          Nat.add_lt_add_right hF (f * 2 ^ (64 * n))
        _ = (f + 1) * 2 ^ (64 * n) := by
          rw [add_comm, Nat.succ_mul f (2 ^ (64 * n))]
        _ ≤ 2 ^ 64 * 2 ^ (64 * n) :=
          Nat.mul_le_mul (Nat.succ_le_of_lt hf) (le_refl _)
        _ = 2 ^ (64 * (n + 1)) := by
          rw [← Nat.pow_add, Nat.mul_add, add_comm]
        _ ≤ 2 ^ (64 * i) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_left 64 (Nat.succ_le_of_lt hn_lt_i))
      have h_div : (F + f * 2 ^ (64 * n)) / 2 ^ (64 * i) = 0 := Nat.div_eq_of_lt h_sum_lt
      rw [h_div, Nat.zero_mod]
      simp [hi, heq]

private lemma oN_mul_sub_one_eq (a b : ℕ) (ha : 0 < a) (hb : 1 < b) : a * (b - 1) + (a - 1) = a * b - 1 := by
  have h1 : a * (b - 1) = a * b - a := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  have h2 : a * b - a + (a - 1) = a * b - 1 := by
    have hle : a ≤ a * b := by
      calc
        a = a * 1 := by simp
        _ ≤ a * b := Nat.mul_le_mul_left a (by omega)
    omega
  calc
    a * (b - 1) + (a - 1) = (a * b - a) + (a - 1) := by rw [h1]
    _ = a * b - 1 := by rw [h2]

private lemma oN_succ (n : ℕ) : oN (n+1) = 2^(64*n) + oN n := by
  unfold oN
  simp only [Nat.shiftLeft_eq']
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have h64 : (2^6 : ℕ) = 64 := by norm_num
  rw [h64]
  rw [add_mul, one_mul, mul_comm n 64]
  rw [pow_add]
  have hM : (18446744073709551615 : ℕ) = 2^64 - 1 := by norm_num
  rw [hM]
  simp only [Nat.sub_eq]
  have hpos : 0 < 2^64 - 1 := by norm_num
  have ha : 0 < 2^(64*n) := pow_pos (by norm_num) _
  have hb : 1 < 2^64 := by norm_num
  have h_eq : 2 ^ (64 * n) * 2 ^ 64 - 1 = (2 ^ (64 * n) - 1) + 2 ^ (64 * n) * (2 ^ 64 - 1) := by
    rw [← oN_mul_sub_one_eq (2^(64*n)) (2^64) ha hb, add_comm]
  rw [h_eq]
  change ((2 ^ (64 * n) - 1 + 2 ^ (64 * n) * (2 ^ 64 - 1)) / (2 ^ 64 - 1)) = 2 ^ (64 * n) + ((2 ^ (64 * n) - 1) / (2 ^ 64 - 1))
  rw [Nat.add_mul_div_right _ _ hpos]
  rw [add_comm]

private lemma oN_lt_pow (n : ℕ) (hn : 0 < n) : oN n < 2^(64*n) := by
  induction' n with k ih
  · exact (lt_irrefl _ hn).elim
  · rw [oN_succ]
    have hbound : oN k < 2^(64*k) := by
      by_cases hk0 : k = 0
      · subst hk0; unfold oN; decide
      · exact ih (Nat.pos_of_ne_zero hk0)
    have hsum : 2^(64*k) + oN k < 2^(64*k) + 2^(64*k) := by omega
    have hdouble : 2^(64*k) + 2^(64*k) = 2^(64*k + 1) := by
      rw [← mul_two, ← pow_succ]
    have hpow : 2^(64*k + 1) ≤ 2^(64*(k+1)) := by
      apply Nat.pow_le_pow_right (by norm_num) ?_
      omega
    calc
      2^(64*k) + oN k < 2^(64*k) + 2^(64*k) := hsum
      _ = 2^(64*k + 1) := hdouble
      _ ≤ 2^(64*(k+1)) := hpow

private lemma oN_pow_64_mod (n : ℕ) (hn : 0 < n) : (2^(64*n)) % 2^64 = 0 := by
  have h : 2^64 ∣ 2^(64*n) := by
    have hle : 64 ≤ 64*n := by omega
    exact Nat.pow_dvd_pow 2 hle
  rcases h with ⟨k, hk⟩
  rw [hk]
  simp

private lemma oN_mod_64 (n : ℕ) (hn : 0 < n) : oN n % 2^64 = 1 := by
  induction' n with k ih
  · exact (lt_irrefl _ hn).elim
  · rw [oN_succ]
    by_cases hk0 : k = 0
    · subst hk0; decide
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hmod_pow : (2^(64*k)) % 2^64 = 0 := oN_pow_64_mod k hkpos
      have hmod_dws : oN k % 2^64 = 1 := ih hkpos
      rw [Nat.add_mod]
      rw [hmod_pow, hmod_dws]
      simp

theorem lane_oN (n l : ℕ) (hl : l < n) : lane (oN n) l = 1 := by
  dsimp [lane]
  induction' n with k ih generalizing l
  · exact absurd hl (Nat.not_lt_zero _)
  · have h_cases := Nat.lt_succ_iff_lt_or_eq.mp hl
    rcases h_cases with (hl' | heq)
    ·
      have hpos : 0 < 2^(64*l) := pow_pos (by norm_num) _

      have h_pow_eq : 2^(64*k) = 2^(64*l) * 2^(64*(k-l)) := by
        rw [← pow_add]
        have hsum : 64*l + 64*(k-l) = 64*k := by omega
        rw [hsum]
      rw [oN_succ]
      rw [h_pow_eq]

      rw [add_comm, mul_comm (2^(64*l)) (2^(64*(k-l)))]

      rw [Nat.add_mul_div_right _ _ hpos]

      by_cases hkl : k - l = 0
      ·
        have : k = l := by omega
        subst this
        omega
      · have hpos_kl : 0 < k - l := Nat.pos_of_ne_zero hkl
        have hmod_pow : (2^(64*(k-l))) % 2^64 = 0 := oN_pow_64_mod (k-l) hpos_kl

        have hM : (2^64 : ℕ) = 18446744073709551616 := by norm_num
        rw [hM] at hmod_pow
        rw [Nat.add_mod, hmod_pow]
        simp

        rw [← hM]
        exact ih l hl'
    ·
      rw [heq]
      rw [oN_succ]
      have hpos : 0 < 2^(64*k) := pow_pos (by norm_num) _
      rw [add_comm, Nat.add_div_right _ hpos]

      by_cases hk0 : k = 0
      · subst hk0; decide
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have h_lt : oN k < 2^(64*k) := oN_lt_pow k hkpos
        have h_div : oN k / 2^(64*k) = 0 := Nat.div_eq_of_lt h_lt
        rw [h_div]

theorem append_lt (F f n : ℕ) (hF : F < 2 ^ (64 * n)) (hf : f < 2 ^ 64) :
    F + f * 2 ^ (64 * n) < 2 ^ (64 * (n + 1)) := by
  have hF' : F + 1 ≤ 2 ^ (64 * n) := Nat.succ_le_of_lt hF
  have hf' : f + 1 ≤ 2 ^ 64 := Nat.succ_le_of_lt hf
  have h_mul : (f + 1) * 2 ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) :=
    Nat.mul_le_mul hf' (by rfl)
  have h_pow : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
    calc
      2 ^ (64 * (n + 1)) = 2 ^ (64 * n + 64) := by ring
      _ = 2 ^ (64 * n) * 2 ^ 64 := by rw [Nat.pow_add]
  rw [h_pow]
  have h_total : (F + f * 2 ^ (64 * n)) + 1 ≤ 2 ^ (64 * n) * 2 ^ 64 := by
    calc
      (F + f * 2 ^ (64 * n)) + 1 = F + 1 + f * 2 ^ (64 * n) := by ring
      _ ≤ 2 ^ (64 * n) + f * 2 ^ (64 * n) := Nat.add_le_add_right hF' _
      _ = (f + 1) * 2 ^ (64 * n) := by ring
      _ ≤ 2 ^ 64 * 2 ^ (64 * n) := h_mul
      _ = 2 ^ (64 * n) * 2 ^ 64 := Nat.mul_comm _ _
  exact Nat.lt_of_succ_le h_total

theorem fld_pair (a b : ℕ) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    fld (a + Nat.shiftLeft b 32) 0 = (a : ℝ) / 2 ^ 24 ∧ fld (a + Nat.shiftLeft b 32) 32 = (b : ℝ) / 2 ^ 24 := by
  have hshift_eq : Nat.shiftLeft b 32 = b <<< 32 := by simp [Nat.shiftLeft_eq']
  have hsum_mod32 : (a + Nat.shiftLeft b 32) % 2 ^ 32 = a := by
    rw [hshift_eq]
    omega
  have hsum_div32 : (a + Nat.shiftLeft b 32) / 2 ^ 32 = b := by
    rw [hshift_eq]
    omega
  have hsum_mod32' : ((a + Nat.shiftLeft b 32) / 2 ^ 32) % 2 ^ 32 = b := by
    rw [hsum_div32]
    exact Nat.mod_eq_of_lt hb
  constructor
  · dsimp [fld]
    have hinner : ((a + b <<< 32) / 1 % 4294967296 : ℕ) = a := by
      calc
        ((a + b <<< 32) / 1 % 4294967296 : ℕ) = (a + b <<< 32) % 4294967296 := by simp
        _ = (a + b <<< 32) % (2 ^ 32) := by norm_num
        _ = (a + b.shiftLeft 32) % (2 ^ 32) := by rw [hshift_eq]
        _ = a := hsum_mod32
    rw [hinner]
  · dsimp [fld]
    have hinner : ((a + b <<< 32) / 4294967296 % 4294967296 : ℕ) = b := by
      calc
        ((a + b <<< 32) / 4294967296 % 4294967296 : ℕ) = (a + b <<< 32) / (2 ^ 32) % (2 ^ 32) := by norm_num
        _ = (a + b.shiftLeft 32) / (2 ^ 32) % (2 ^ 32) := by rw [hshift_eq]
        _ = ((a + b.shiftLeft 32) / 2 ^ 32) % 2 ^ 32 := rfl
        _ = b := hsum_mod32'
    rw [hinner]

theorem fld0_of_lt {F : ℕ} (h : F < 2 ^ 32) : fld F 0 = (F : ℝ) / 2 ^ 24 := by
  unfold fld
  rw [pow_zero, Nat.div_one, Nat.mod_eq_of_lt h]

theorem fk_bits7 (it o : ℕ) : fk it o 127 = bits it o 7 := land_shiftRight it o 7
theorem fk_bits6 (it o : ℕ) : fk it o 63 = bits it o 6 := land_shiftRight it o 6
theorem fk_bits3 (it o : ℕ) : fk it o 7 = bits it o 3 := land_shiftRight it o 3
theorem fk_bits1 (it o : ℕ) : fk it o 1 = bits it o 1 := land_shiftRight it o 1

theorem bk_eq (box t : ℕ) : bk box t = bnd box t := by
  show Nat.land (Nat.shiftRight box (Nat.shiftLeft t 6)) 18446744073709551615 = bnd box t
  rw [Walk.shl6]
  exact land_shiftRight box (64 * t) 64

theorem lf_eq (box v : ℕ) : lf box v = kfl (bnd box (2 * v)) + Nat.shiftLeft (kce (bnd box (2 * v + 1))) 32 := by
  have h2 : Nat.shiftLeft v 1 = 2 * v := by rw [shl_eq]; ring
  show Nat.add (kfl (bk box (Nat.shiftLeft v 1))) (Nat.shiftLeft (kce (bk box (Nat.add (Nat.shiftLeft v 1) 1))) 32) = _
  rw [h2, bk_eq, bk_eq]
  rfl

theorem claim_lo {it : ℕ} (h : bits it 64 1 = 0) : claim it = kce (itNew it) := by
  unfold claim
  rw [fk_bits1, h]
  exact congrArg kce (Walk.kf_new it)

theorem claim_hi {it : ℕ} (h : bits it 64 1 = 1) : claim it = kfl (itNew it) := by
  unfold claim
  rw [fk_bits1, h]
  exact congrArg kfl (Walk.kf_new it)

theorem lf_bounds {box v : ℕ} {y : ℝ} (h1 : kok (bnd box (2 * v)) = true) (h2 : kok (bnd box (2 * v + 1)) = true)
    (hy : keyVal (bnd box (2 * v)) ≤ y ∧ y ≤ keyVal (bnd box (2 * v + 1))) :
    fld (lf box v) 0 ≤ y ∧ y ≤ fld (lf box v) 32 := by
  rw [lf_eq]
  obtain ⟨ha, hb⟩ := fld_pair _ _ (lt_trans (kce_lt h1).2 (by norm_num)) (lt_trans (kce_lt h2).1 (by norm_num))
  rw [ha, hb]
  exact ⟨(kfl_le h1).trans hy.1, hy.2.trans (le_kce h2)⟩

theorem val_d {g : ℕ} {P : PlaneGraph} {kk : ℕ} (lab : P.G.Dart ≃ Fin (Ctx.D g)) (A : Assign P kk) {v : ℕ}
    (h : Ctx.mean g v = 1) : Ctx.val g lab A v = A.d := by
  simp [Ctx.val, h]

theorem val_corner {g : ℕ} {P : PlaneGraph} {kk : ℕ} (lab : P.G.Dart ≃ Fin (Ctx.D g)) (A : Assign P kk) {v : ℕ}
    (d : P.G.Dart) (h : Ctx.mean g v = 2 + (lab d : ℕ)) : Ctx.val g lab A v = A.corner d := by
  have hD : Ctx.D g < 256 := bits_lt g 0 8
  have hd : (lab d : ℕ) < Ctx.D g := (lab d).isLt
  unfold Ctx.val
  rw [ite_eq_right (show ¬ Ctx.mean g v = 0 by omega), ite_eq_right (show ¬ Ctx.mean g v = 1 by omega),
    dite_eq_left (show Ctx.mean g v < 258 ∧ Ctx.mean g v - 2 < Ctx.D g by omega)]
  congr 1
  rw [Equiv.symm_apply_eq]
  ext
  show Ctx.mean g v - 2 = (lab d : ℕ)
  omega

theorem boxMem_set {nv box t w : ℕ} {y : ℕ → ℝ} (hw : w < 2 ^ 64) (hy : BoxMem nv box y)
    (hlo : t % 2 = 0 → keyVal w ≤ y (t / 2)) (hhi : t % 2 = 1 → y (t / 2) ≤ keyVal w) :
    BoxMem nv (setBnd box t w) y := by
  intro v hv
  by_cases h0 : 2 * v = t
  · subst h0
    rw [bnd_setBnd_self _ _ _ hw, bnd_setBnd_ne _ _ _ _ hw (by omega)]
    have := hlo (by omega)
    rw [show 2 * v / 2 = v by omega] at this
    exact ⟨this, (hy v hv).2⟩
  · by_cases h1 : 2 * v + 1 = t
    · subst h1
      rw [bnd_setBnd_self _ _ _ hw, bnd_setBnd_ne _ _ _ _ hw (by omega)]
      have := hhi (by omega)
      rw [show (2 * v + 1) / 2 = v by omega] at this
      exact ⟨(hy v hv).1, this⟩
    · rw [bnd_setBnd_ne _ _ _ _ hw (Ne.symm (Ne.symm h0)), bnd_setBnd_ne _ _ _ _ hw h1]
      exact hy v hv

theorem recOK_of_pent {k : Fin 2} {hi : Bool} {g box it : ℕ} (hok : okP k hi g box it = true)
    (hc : LaneClaim k hi (lf box (fk it 97 63)) (lf box (fk it 85 63)) (lf box (fk it 91 63)) (claim it)) :
    RecOK g box it := by
  have hok' := hok
  simp only [okP, fk_bits7, fk_bits6, fk_bits3, bk_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq,
    and_assoc] at hok'
  obtain ⟨he, hper, hs2, hk, hside, hdv, hxv, hyv, ho, mdv, mxv, myv, mo, k1, k2, k3, k4, k5, k6, knew, -⟩ := hok'
  rw [fk_bits6, fk_bits6, fk_bits6] at hc
  have hoe : Nat.shiftRight (bits it 64 7) 1 = bits it 64 7 / 2 := Nat.shiftRight_eq_div_pow _ _
  rw [hoe] at ho mo
  intro S hS

  set e' : S.P.G.Dart := S.lab.symm ⟨bits it 75 7, he⟩ with he'
  have hlab : (S.lab e' : ℕ) = bits it 75 7 := by simp [he']
  have hfs : fsize S.P e' = 5 :=
    fsize_of_period S.hm e' ((congrArg (Ctx.code g).period hlab).trans hper) (by norm_num)
  have hiter : ∀ j, (Ctx.code g).faceIter (bits it 75 7) j = S.lab ((S.P.R.face ^ j) e') := by
    intro j; rw [← hlab]; exact faceIter_lab S.hm e' j
  have hxd : S.x (bits it 97 6) = S.A.d := val_d S.lab S.A mdv
  have hcorner : ∀ v j, Ctx.mean g v = 2 + (Ctx.code g).faceIter (bits it 75 7) j → S.x v = S.A.fc e' j := by
    intro v j hm
    rw [hiter] at hm
    exact val_corner S.lab S.A _ hm
  have hd : fld (lf box (bits it 97 6)) 0 ≤ S.A.d ∧ S.A.d ≤ fld (lf box (bits it 97 6)) 32 := by
    rw [← hxd]; exact lf_bounds k1 k2 (hS _ hdv)
  have hX : fld (lf box (bits it 85 6)) 0 ≤ S.x (bits it 85 6) ∧ S.x (bits it 85 6) ≤ fld (lf box (bits it 85 6)) 32 :=
    lf_bounds k3 k4 (hS _ hxv)
  have hY : fld (lf box (bits it 91 6)) 0 ≤ S.x (bits it 91 6) ∧ S.x (bits it 91 6) ≤ fld (lf box (bits it 91 6)) 32 :=
    lf_bounds k5 k6 (hS _ hyv)
  have hL := laneClaim_relSys S.hR hfs hd (hi := hi) (F1 := lf box (bits it 85 6)) (F2 := lf box (bits it 91 6))
    (F3 := claim it)

  have hcl : Claim hi (fld (claim it) 0) (S.x (bits it 64 7 / 2)) := by
    obtain h | h | h : bits it 82 3 = 0 ∨ bits it 82 3 = 1 ∨ bits it 82 3 = 2 := by omega
    · rw [h] at hk mxv myv mo
      have hk0 : k = 0 := Fin.ext hk
      subst hk0
      rw [hcorner _ 1 mxv] at hX
      rw [hcorner _ 4 myv] at hY
      rw [hcorner _ 0 mo]
      exact (hL.1 hX hY).1 hc
    · rw [h] at hk mxv myv mo
      have hk1 : k = 1 := Fin.ext hk
      subst hk1
      rw [hcorner _ 1 mxv] at hX
      rw [hcorner _ 4 myv] at hY
      rw [hcorner _ 2 mo]
      exact (hL.1 hX hY).2 hc
    · rw [h] at hk mxv myv mo
      have hk1 : k = 1 := Fin.ext hk
      subst hk1
      rw [hcorner _ 4 mxv] at hX
      rw [hcorner _ 1 myv] at hY
      rw [hcorner _ 3 mo]
      exact hL.2 hX hY hc

  have hb1 : bits it 64 1 = bits it 64 7 % 2 := by
    unfold bits; rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 7)]; rfl
  have hside' : bits it 64 7 % 2 = @Bool.rec (fun _ => ℕ) 0 1 hi := by
    rw [← hside]; exact (Nat.and_one_is_mod _).symm
  rw [Walk.kf_new] at knew
  refine boxMem_set (bits_lt it 0 64) hS (fun h0 => ?_) (fun h1 => ?_)
  · have h0' : bits it 64 7 % 2 = 0 := h0
    cases hi
    · have hlt : claim it < 2 ^ 32 := by
        rw [claim_lo (hb1.trans h0')]; exact lt_trans (kce_lt knew).1 (by norm_num)
      have hcl' : (claim it : ℝ) / 2 ^ 24 ≤ S.x (bits it 64 7 / 2) := by
        rw [← fld0_of_lt hlt]; exact hcl
      rw [claim_lo (hb1.trans h0')] at hcl'
      exact (le_kce knew).trans hcl'
    · have h1' : bits it 64 7 % 2 = 1 := hside'
      omega
  · have h1' : bits it 64 7 % 2 = 1 := h1
    cases hi
    · have h0' : bits it 64 7 % 2 = 0 := hside'
      omega
    · have hlt : claim it < 2 ^ 32 := by
        rw [claim_hi (hb1.trans h1')]; exact lt_trans (kce_lt knew).2 (by norm_num)
      have hcl' : S.x (bits it 64 7 / 2) ≤ (claim it : ℝ) / 2 ^ 24 := by
        rw [← fld0_of_lt hlt]; exact hcl
      rw [claim_hi (hb1.trans h1')] at hcl'
      exact hcl'.trans (kfl_le knew)

def PInv (k : Fin 2) (hi : Bool) (s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool) (tr : List Ev) : Prop :=
  s.2.2.2.2.2 = true →
    s.2.1 < 2 ^ (64 * s.1) ∧ s.2.2.1 < 2 ^ (64 * s.1) ∧ s.2.2.2.1 < 2 ^ (64 * s.1) ∧
      s.2.2.2.2.1 < 2 ^ (64 * s.1) ∧
      (∀ l < s.1, InDom (lane s.2.1 l) (lane s.2.2.1 l) (lane s.2.2.2.1 l) (lane s.2.2.2.2.1 l)) ∧
      ∀ e ∈ tr, ∃ g box it, e = .record g box it ∧ okP k hi g box it = true ∧
        ∃ l < s.1, lane s.2.1 l = lf box (fk it 97 63) ∧ lane s.2.2.1 l = lf box (fk it 85 63) ∧
          lane s.2.2.2.1 l = lf box (fk it 91 63) ∧ lane s.2.2.2.2.1 l = claim it

theorem okP_inDomB {k : Fin 2} {hi : Bool} {g box it : ℕ} (h : okP k hi g box it = true) :
    inDomB (lf box (fk it 97 63)) (lf box (fk it 85 63)) (lf box (fk it 91 63)) (claim it) = true := by
  unfold okP at h
  exact ((Bool.and_eq_true _ _).mp h).2

theorem kokK_eq (k : ℕ) : kokK k = kok k := by
  have hs : Nat.shiftRight k 52 = k / 4503599627370496 := by
    have h := Nat.shiftRight_eq_div_pow k 52
    norm_num at h
    exact h
  have he : kexp k = k / 4503599627370496 % 2048 := by
    have h : kexp k = bits k 52 11 := land_shiftRight k 52 11
    rw [h]
    unfold bits
    norm_num
  unfold kokK kok
  rw [he, hs]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
  omega

theorem inDomBK_eq (F0 F1 F2 F3 : ℕ) : inDomBK F0 F1 F2 F3 = inDomB F0 F1 F2 F3 := by
  have hland : ∀ (F : ℕ), F &&& 4294967295 = F % 4294967296 := by
    intro F
    calc
      F &&& 4294967295 = F &&& (2^32 - 1) := by norm_num
      _ = F % (2^32) := Nat.and_two_pow_sub_one_eq_mod F 32
      _ = F % 4294967296 := by norm_num
  have hshift : ∀ (F : ℕ), (F >>> 32) &&& 4294967295 = (F / 4294967296) % 4294967296 := by
    intro F
    calc
      (F >>> 32) &&& 4294967295 = (F >>> 32) &&& (2^32 - 1) := by norm_num
      _ = (F >>> 32) % (2^32) := Nat.and_two_pow_sub_one_eq_mod (F >>> 32) 32
      _ = (F / 2^32) % (2^32) := by rw [Nat.shiftRight_eq_div_pow]
      _ = (F / 4294967296) % 4294967296 := by norm_num
  rw [inDomBK, inDomB]
  simp [hland F0, hland F1, hland F2, hshift F0, hshift F1, hshift F2]

theorem okPK_eq (k : Fin 2) (hi : Bool) (g box it : ℕ) : okPK k hi g box it = okP k hi g box it := by
  have he : fk it 75 127 < 256 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hs : ∀ v, Nat.shiftLeft v 1 = 2 * v := fun v => by
    show v <<< 1 = 2 * v
    rw [Nat.shiftLeft_eq]; ring
  have hD : (Ctx.code g).D = Ctx.D g := rfl
  unfold okPK okP
  simp only [nvCK_eq, DK_eq, meanK_eq, periodK_eq g _ he, iterK_eq g _ _ he, inDomBK_eq, kokK_eq, hs, hD,
    Nat.add_eq]

theorem prog_step_rec (k : Fin 2) (hi : Bool) (prog : Prog) (n F0 F1 F2 F3 : ℕ) (ok : Bool) (g box it : ℕ) :
    (progChecker k hi prog).step (.record g box it) (n, F0, F1, F2, F3, ok) =
      (n + 1, F0 + lf box (fk it 97 63) * 2 ^ (64 * n), F1 + lf box (fk it 85 63) * 2 ^ (64 * n),
        F2 + lf box (fk it 91 63) * 2 ^ (64 * n), F3 + claim it * 2 ^ (64 * n), ok && okP k hi g box it) := by
  show (Nat.add n 1, Nat.add F0 (Nat.shiftLeft (lf box (fk it 97 63)) (Nat.shiftLeft n 6)),
    Nat.add F1 (Nat.shiftLeft (lf box (fk it 85 63)) (Nat.shiftLeft n 6)),
    Nat.add F2 (Nat.shiftLeft (lf box (fk it 91 63)) (Nat.shiftLeft n 6)),
    Nat.add F3 (Nat.shiftLeft (claim it) (Nat.shiftLeft n 6)), ok && okPK k hi g box it) = _
  rw [Walk.shl6, okPK_eq]
  simp only [shl_eq]
  rfl

theorem pinv_record {k : Fin 2} {hi : Bool} {n F0 F1 F2 F3 : ℕ} {tr : List Ev} {g box it : ℕ}
    (h : PInv k hi (n, F0, F1, F2, F3, true) tr) (hok : okP k hi g box it = true) :
    PInv k hi (n + 1, F0 + lf box (fk it 97 63) * 2 ^ (64 * n), F1 + lf box (fk it 85 63) * 2 ^ (64 * n),
      F2 + lf box (fk it 91 63) * 2 ^ (64 * n), F3 + claim it * 2 ^ (64 * n), true) (tr ++ [.record g box it]) := by
  unfold PInv at h ⊢
  dsimp only at h ⊢
  intro _
  obtain ⟨b0, b1, b2, b3, hdom, hev⟩ := h rfl
  have hD := inDomB_sound (okP_inDomB hok)
  have f0 := hD.1
  have f1 := hD.2.1
  have f2 := hD.2.2.1
  have f3 : claim it < 2 ^ 64 := lt_trans hD.2.2.2.1 (by norm_num)
  refine ⟨append_lt _ _ _ b0 f0, append_lt _ _ _ b1 f1, append_lt _ _ _ b2 f2, append_lt _ _ _ b3 f3, ?_, ?_⟩
  · intro l hl
    rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2, lane_append _ _ _ _ b3 f3]
    by_cases hln : l < n
    · simp only [hln, ite_true]
      exact hdom l hln
    · have hle : l = n := by omega
      simp [hle]
      exact hD
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨g', box', it', rfl, hok', l, hl, h0, h1, h2, h3⟩ := hev e he
      refine ⟨g', box', it', rfl, hok', l, by omega, ?_⟩
      rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2,
        lane_append _ _ _ _ b3 f3]
      simp only [hl, ite_true]
      exact ⟨h0, h1, h2, h3⟩
    · rw [List.mem_singleton] at he
      subst he
      refine ⟨g, box, it, rfl, hok, n, by omega, ?_⟩
      rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2,
        lane_append _ _ _ _ b3 f3]
      simp

theorem pinv_step {k : Fin 2} {hi : Bool} {prog : Prog} {s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool} {tr : List Ev}
    (h : PInv k hi s tr) (e : Ev) : PInv k hi ((progChecker k hi prog).step e s) (tr ++ [e]) := by
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := s
  cases e with
  | kill g box it =>
    intro hf
    have h' : false = true := hf
    cases h'
  | record g box it =>
    rw [prog_step_rec]
    unfold PInv
    dsimp only
    intro hf
    rw [Bool.and_eq_true] at hf
    obtain ⟨rfl, hok⟩ := hf
    have := pinv_record h hok
    unfold PInv at this
    dsimp only at this
    exact this rfl

theorem pinv_fold {k : Fin 2} {hi : Bool} {prog : Prog} (tr : List Ev) :
    ∀ (s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool) (tr0 : List Ev), PInv k hi s tr0 →
      PInv k hi (tr.foldl (fun s e => (progChecker k hi prog).step e s) s) (tr0 ++ tr) := by
  induction tr with
  | nil => intro s tr0 h; rw [List.append_nil]; exact h
  | cons e tr ih =>
    intro s tr0 h
    have := ih _ _ (pinv_step (prog := prog) h e)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

theorem progChecker_sound {k : Fin 2} {hi : Bool} {prog : Prog} (hp : ProgOK k hi prog) :
    (progChecker k hi prog).Sound fun _ => True := by
  intro tr hs _ hfin e he
  have hinv : PInv k hi ((progChecker k hi prog).run tr) tr := by
    have h0 : PInv k hi (0, 0, 0, 0, 0, true) [] := by
      intro _
      refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun l hl => absurd hl (Nat.not_lt_zero _),
        fun e he => absurd he (by simp)⟩
    have := pinv_fold (prog := prog) tr _ _ h0
    rw [List.nil_append] at this
    exact this
  generalize (progChecker k hi prog).run tr = S at hinv hfin
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := S
  have hf : (ok && Nat.beq (prog (oN n) F0 F1 F2 F3 hs) (oN n)) = true := hfin
  rw [Bool.and_eq_true] at hf
  obtain ⟨rfl, hv⟩ := hf
  unfold PInv at hinv
  dsimp only at hinv
  obtain ⟨-, -, -, -, hdom, hev⟩ := hinv rfl
  obtain ⟨g, box, it, rfl, hok, l, hl, h0, h1, h2, h3⟩ := hev e he
  have hc := hp n F0 F1 F2 F3 hs (oN n) hdom hv l hl (lane_oN n l hl)
  rw [h0, h1, h2, h3] at hc
  exact recOK_of_pent hok hc

theorem btree_sound (f : ℕ → Checker) (key : ℕ → ℕ) (hf : ∀ i, (f i).Sound fun _ => True) :
    ∀ (d i : ℕ) (adm : ℕ → Prop), (btree f key d i).Sound adm := by
  intro d
  induction d with
  | zero => intro i adm; exact (hf i).mono fun _ _ => trivial
  | succ d ih => intro i adm; exact Checker.pair_sound (ih i _) (ih (i + 2 ^ d) _)

theorem pentChecker_sound (progs : ℕ → Prog) (hp : ∀ i < 12, ProgOK (kOf i) (hiOf i) (progs i)) :
    (pentChecker progs).Sound (kindIs 3) := by
  refine btree_sound _ pIdx (fun i => ?_) 4 0 _
  split_ifs with h
  · exact progChecker_sound (hp i h)
  · exact Checker.none_sound _

end Tammes15.D3Kernel.Pent
