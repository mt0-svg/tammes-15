import Mathlib
import Tammes15.D3Pack.Lanes
import Tammes15.D3Pack.Fixed24

open D3Dec

namespace D3Q2A0

noncomputable def cnd {α : Type} (b : Bool) (x y : α) : α :=
  @Bool.rec (fun _ => α) y x b

noncomputable def frc2 {α : Type} (a b : ℕ) (k : ℕ → ℕ → α) : α :=
  cnd (Nat.beq a 0) (cnd (Nat.beq b 0) (k 0 0) (k 0 b)) (cnd (Nat.beq b 0) (k a 0) (k a b))

def mulTerm (O A B k : ℕ) : ℕ :=
  Nat.land (Nat.shiftLeft A k) (Nat.mul (Nat.land B (Nat.shiftLeft O k)) (Nat.sub (Nat.shiftLeft 1 (Nat.sub 64 k)) 1))

noncomputable def mulBitF (O A B k P : ℕ) (ih : ℕ → ℕ) : ℕ :=
  frc2 (Nat.add P (Nat.land (Nat.shiftLeft A k)
    (Nat.mul (Nat.land B (Nat.shiftLeft O k)) (Nat.sub (Nat.shiftLeft 1 (Nat.sub 64 k)) 1)))) 1 (fun P _ => ih P)

noncomputable def mulF (K : ℕ) (O A B : ℕ) : ℕ :=
  @Nat.rec (fun _ => ℕ → ℕ) (fun P => P) (fun k ih P => mulBitF O A B k P ih) K 0

def mH (O : ℕ) : ℕ := Nat.mul O 9223372036854775808

def pmask (b : ℕ) : ℕ := Nat.mul b 9223372036854775807

def psub (O x y : ℕ) : ℕ :=
  Nat.land (Nat.sub (Nat.add x (mH O)) y)
    (pmask (Nat.shiftRight (Nat.land (Nat.sub (Nat.add x (mH O)) y) (mH O)) 63))

def plt (O x y : ℕ) : ℕ :=
  Nat.shiftRight (Nat.land (Nat.sub (Nat.add y (mH O)) (Nat.add x O)) (mH O)) 63

def psel (M A B : ℕ) : ℕ := Nat.xor B (Nat.land (Nat.xor A B) M)

def rep (O v : ℕ) : ℕ := Nat.mul O v

def pfm (mul : ℕ → ℕ → ℕ → ℕ → ℕ) (K O A B : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (mul K O A B) 24) (Nat.mul O 1099511627775)

def pfmc (O A k : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (Nat.mul A k) 24) (Nat.mul O 1099511627775)

def cosP (mul : ℕ → ℕ → ℕ → ℕ → ℕ) (O z2 : ℕ) : ℕ :=
  Nat.sub (rep O 16777216) (pfm mul 24 O (Nat.sub (rep O 8388608) (pfm mul 24 O (Nat.sub (rep O 699051)
    (pfm mul 24 O (Nat.sub (rep O 23302) (pfmc O z2 416)) z2)) z2)) z2)

def sinP (mul : ℕ → ℕ → ℕ → ℕ → ℕ) (O z z2 : ℕ) : ℕ :=
  pfm mul 24 O (Nat.sub (rep O 16777216) (pfm mul 24 O (Nat.sub (rep O 2796203) (pfm mul 24 O (Nat.sub (rep O 139810)
    (pfm mul 24 O (Nat.sub (rep O 3329) (pfmc O z2 46)) z2)) z2)) z2)) z

def sincosP24o (mul : ℕ → ℕ → ℕ → ℕ → ℕ) (O x0 : ℕ) : ℕ × ℕ × ℕ :=
  let negb := plt O (rep O 26353589) x0
  let nm := pmask negb
  let x := psel nm (psub O (rep O 52707179) x0) x0
  let swb := plt O (rep O 13176794) x
  let sm := pmask swb
  let z := psel sm (Nat.sub (rep O 26353589) x) x
  let z2 := pfm mul 24 O z z
  (psel sm (cosP mul O z2) (sinP mul O z z2), psel sm (sinP mul O z z2) (cosP mul O z2), negb)
end D3Q2A0

open D3Dec D3Q2A0

theorem D3Q2A0.frc2_eq {α : Type} (a b : ℕ) (k : ℕ → ℕ → α) : frc2 a b k = k a b := by
  simp [frc2, cnd]
  cases ha : Nat.beq a 0
  ·
    cases hb : Nat.beq b 0
    ·
      rfl
    ·
      have hb0 : b = 0 := Nat.eq_of_beq_eq_true hb
      subst hb0; rfl
  ·
    have ha0 : a = 0 := Nat.eq_of_beq_eq_true ha
    subst ha0
    cases hb : Nat.beq b 0
    ·
      rfl
    ·
      have hb0 : b = 0 := Nat.eq_of_beq_eq_true hb
      subst hb0; rfl

theorem D3Q2A0.mulF_eq_sum (K O A B : ℕ) : mulF K O A B = ∑ k ∈ Finset.range K, mulTerm O A B k := by

  have hfrc2_one : ∀ (a : ℕ) (f : ℕ → ℕ → ℕ), frc2 a 1 f = f a 1 := by
    intro a f
    unfold frc2 cnd
    have h1 : Nat.beq (1 : ℕ) 0 = false := by decide
    by_cases ha : Nat.beq a 0
    ·
      have ha_eq : a = 0 := Nat.eq_of_beq_eq_true ha
      subst ha_eq
      simp [h1]
    ·
      simp [ha, h1]

  set R := fun (K : ℕ) (P : ℕ) =>
    @Nat.rec (fun _ => ℕ → ℕ) (fun P => P) (fun k ih P => mulBitF O A B k P ih) K P
  with hR_def
  have h_mulF_eq_R : mulF K O A B = R K 0 := rfl
  rw [h_mulF_eq_R]
  have hR_succ : ∀ K P, R (K + 1) P = mulBitF O A B K P (R K) := by
    intro K P; rfl
  have h_mulBitF_eq : ∀ K P, mulBitF O A B K P (R K) = R K (P + mulTerm O A B K) := by
    intro K P
    unfold mulBitF mulTerm
    simpa using hfrc2_one (P + (Nat.land (Nat.shiftLeft A K)
      (Nat.mul (Nat.land B (Nat.shiftLeft O K)) (Nat.sub (Nat.shiftLeft 1 (Nat.sub 64 K)) 1))))
      (fun P' _ => R K P')
  have hR_eq : ∀ K P, R K P = P + ∑ k ∈ Finset.range K, mulTerm O A B k := by
    intro K
    induction K with
    | zero =>
      intro P
      unfold R
      simp
    | succ K ih =>
      intro P
      rw [hR_succ K P, h_mulBitF_eq K P, ih (P + mulTerm O A B K)]
      rw [Finset.sum_range_succ]
      omega
  rw [hR_eq K 0, zero_add]

theorem D3Q2A0.sum_testBit (K b : ℕ) (hb : b < 2 ^ K) :
    ∑ k ∈ Finset.range K, (if b.testBit k then 2 ^ k else 0) = b := by
  induction K generalizing b with
  | zero =>
    have hb0 : b = 0 := by omega
    subst hb0
    simp
  | succ K ih =>
    rw [Finset.sum_range_succ']
    have hdiv : b / 2 < 2 ^ K := by
      apply Nat.div_lt_of_lt_mul
      rw [pow_succ'] at hb
      exact hb
    have h0 : (if b.testBit 0 then 2 ^ 0 else 0) = b % 2 := by
      rw [pow_zero]
      rcases Nat.mod_two_eq_zero_or_one b with (h | h)
      · have hbit : b.testBit 0 = false := by
          rw [Nat.testBit_zero, h]
          decide
        simp [h, hbit]
      · have hbit : b.testBit 0 = true := by
          rw [Nat.testBit_zero, h]
          decide
        simp [h, hbit]
    have hsum : ∑ k ∈ Finset.range K, (if b.testBit (k + 1) then 2 ^ (k + 1) else 0) =
        2 * ∑ k ∈ Finset.range K, (if (b / 2).testBit k then 2 ^ k else 0) := by
      simp_rw [Nat.testBit_succ, pow_succ]
      calc
        ∑ k ∈ Finset.range K, (if (b / 2).testBit k then 2 ^ k * 2 else 0)
            = ∑ k ∈ Finset.range K, (2 * if (b / 2).testBit k then 2 ^ k else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases h : (b / 2).testBit k
          · simp [h, mul_comm]
          · simp [h]
        _ = 2 * ∑ k ∈ Finset.range K, (if (b / 2).testBit k then 2 ^ k else 0) := by
          rw [Finset.mul_sum]
    rw [hsum, ih (b / 2) hdiv, h0]
    omega

theorem D3Q2A0.pack_sum (W L K : ℕ) (f : ℕ → ℕ → ℕ) :
    ∑ k ∈ Finset.range K, pack W L (f k) = pack W L (fun l => ∑ k ∈ Finset.range K, f k l) := by
  unfold pack
  rw [Finset.sum_comm]
  simp [Finset.sum_mul]

theorem D3Q2A0.mulTerm_pack (L k : ℕ) (a b : ℕ → ℕ) (hk : k < 64) (ha : ∀ l < L, a l * 2 ^ k < 2 ^ 64)
    (hb : ∀ l < L, b l < 2 ^ 64) :
    mulTerm (pack 64 L fun _ => 1) (pack 64 L a) (pack 64 L b) k =
      pack 64 L (fun l => if (b l).testBit k then a l * 2 ^ k else 0) := by
  have hWpos : 0 < 64 := by norm_num
  have h_two_pow_k_lt : (2 ^ k : ℕ) < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by norm_num) hk
  have h_sub_one_lt : (2 ^ (64 - k) - 1 : ℕ) < 2 ^ 64 := by
    have : 2 ^ (64 - k) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    omega
  have h_ones_lt : ∀ l < L, (1 : ℕ) < 2 ^ 64 := by
    intro l hl; norm_num

  have h_and_sub (x : ℕ) (hx : x * 2 ^ k < 2 ^ 64) : (x * 2 ^ k) &&& (2 ^ 64 - 2 ^ k) = x * 2 ^ k := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi64 : i < 64
    ·
      by_cases hi : i < k
      ·
        have hA : (x * 2 ^ k).testBit i = false := by
          rw [Nat.testBit_mul_two_pow]
          simp [hi]
        have hB : (2 ^ 64 - 2 ^ k).testBit i = false := by

          rw [show (2 ^ 64 - 2 ^ k : ℕ) = (2 ^ (64 - k) - 1) * 2 ^ k from
            calc
              2 ^ 64 - 2 ^ k = (2 ^ k * 2 ^ (64 - k)) - 2 ^ k := by
                rw [← pow_add, Nat.add_sub_cancel' (by omega : k ≤ 64)]
              _ = (2 ^ k * 2 ^ (64 - k)) - (2 ^ k * 1) := by simp
              _ = 2 ^ k * (2 ^ (64 - k) - 1) := by rw [Nat.mul_sub_left_distrib]
              _ = (2 ^ (64 - k) - 1) * 2 ^ k := by ring
          , Nat.testBit_mul_two_pow]
          simp [hi]
        rw [hA, hB]; simp
      ·
        have hA : (x * 2 ^ k).testBit i = x.testBit (i - k) := by
          rw [Nat.testBit_mul_two_pow]
          simp [show k ≤ i from by omega]
        have hB : (2 ^ 64 - 2 ^ k).testBit i = true := by
          rw [show (2 ^ 64 - 2 ^ k : ℕ) = (2 ^ (64 - k) - 1) * 2 ^ k from
            calc
              2 ^ 64 - 2 ^ k = (2 ^ k * 2 ^ (64 - k)) - 2 ^ k := by
                rw [← pow_add, Nat.add_sub_cancel' (by omega : k ≤ 64)]
              _ = (2 ^ k * 2 ^ (64 - k)) - (2 ^ k * 1) := by simp
              _ = 2 ^ k * (2 ^ (64 - k) - 1) := by rw [Nat.mul_sub_left_distrib]
              _ = (2 ^ (64 - k) - 1) * 2 ^ k := by ring
          , Nat.testBit_mul_two_pow]
          have hk_le_i : k ≤ i := by omega
          have h_lt : i - k < 64 - k := by omega
          simp [hk_le_i, h_lt]
        rw [hA, hB]; simp
    ·
      have hA : (x * 2 ^ k).testBit i = false :=
        Nat.testBit_eq_false_of_lt (by
          have : 2 ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega)
      have hB : (2 ^ 64 - 2 ^ k).testBit i = false :=
        Nat.testBit_eq_false_of_lt (by
          have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
          have : 2 ^ 64 - 2 ^ k < 2 ^ 64 := by omega
          have hpow : 2 ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega)
      simp [hA]

  have hAshift : Nat.shiftLeft (pack 64 L a) k = pack 64 L (fun l => a l * 2 ^ k) := by
    calc
      Nat.shiftLeft (pack 64 L a) k = (pack 64 L a) * 2 ^ k := by
        simpa using Nat.shiftLeft_eq (pack 64 L a) k
      _ = 2 ^ k * pack 64 L a := by ring
      _ = pack 64 L (fun l => 2 ^ k * a l) := by rw [pack_const_mul 64 L (2 ^ k) a]
      _ = pack 64 L (fun l => a l * 2 ^ k) := by simp [mul_comm]

  have hOshift : Nat.shiftLeft (pack 64 L fun _ => (1 : ℕ)) k = pack 64 L fun _ => 2 ^ k := by
    calc
      Nat.shiftLeft (pack 64 L fun _ => (1 : ℕ)) k = (pack 64 L fun _ => (1 : ℕ)) * 2 ^ k := by
        simpa using Nat.shiftLeft_eq (pack 64 L fun _ => (1 : ℕ)) k
      _ = 2 ^ k * pack 64 L fun _ => (1 : ℕ) := by ring
      _ = pack 64 L (fun l => 2 ^ k * (1 : ℕ)) := by rw [pack_const_mul 64 L (2 ^ k) (fun _ => (1 : ℕ))]
      _ = pack 64 L fun _ => 2 ^ k := by simp

  have hland1 : Nat.land (pack 64 L b) (Nat.shiftLeft (pack 64 L fun _ => (1 : ℕ)) k) =
      pack 64 L (fun l => b l &&& 2 ^ k) := by
    rw [hOshift]
    exact land_pack 64 L b (fun _ => 2 ^ k) hWpos hb (fun l _ => h_two_pow_k_lt)

  have hmul : Nat.mul (Nat.land (pack 64 L b) (Nat.shiftLeft (pack 64 L fun _ => (1 : ℕ)) k))
      (Nat.sub (Nat.shiftLeft 1 (Nat.sub 64 k)) 1) =
      pack 64 L (fun l => if (b l).testBit k then 2 ^ 64 - 2 ^ k else 0) := by
    rw [hland1]
    have hsub : Nat.sub (Nat.shiftLeft 1 (Nat.sub 64 k)) 1 = 2 ^ (64 - k) - 1 := by
      have h := Nat.shiftLeft_eq 1 (Nat.sub 64 k)
      simpa [one_mul] using congrArg (· - 1) h
    rw [hsub]

    have h := pack_const_mul 64 L (2 ^ (64 - k) - 1) (fun l => b l &&& 2 ^ k)

    calc
      (pack 64 L fun l => b l &&& 2 ^ k).mul (2 ^ (64 - k) - 1) = (pack 64 L fun l => b l &&& 2 ^ k) * (2 ^ (64 - k) - 1) := rfl
      _ = (2 ^ (64 - k) - 1) * pack 64 L fun l => b l &&& 2 ^ k := by ring
      _ = pack 64 L (fun l => (2 ^ (64 - k) - 1) * (b l &&& 2 ^ k)) := by rw [h]
      _ = pack 64 L (fun l => if (b l).testBit k then 2 ^ 64 - 2 ^ k else 0) := by
        refine pack_congr 64 L _ _ fun l hl => ?_
        rw [Nat.and_two_pow]
        by_cases hbit : (b l).testBit k
        · have htoNat : ((b l).testBit k).toNat = 1 := by simp [hbit]
          rw [htoNat, one_mul]
          have h_eq : 2 ^ k * (2 ^ (64 - k) - 1) = 2 ^ 64 - 2 ^ k := by
            have hk_le : k ≤ 64 := by omega
            have h64 : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k) := by
              rw [← pow_add, Nat.add_sub_cancel' hk_le]
            have h_one_le : 1 ≤ 2 ^ (64 - k) := Nat.one_le_two_pow
            calc
              2 ^ k * (2 ^ (64 - k) - 1) = 2 ^ k * 2 ^ (64 - k) - 2 ^ k * 1 := by
                rw [Nat.mul_sub_left_distrib]
              _ = 2 ^ k * 2 ^ (64 - k) - 2 ^ k := by simp
              _ = 2 ^ 64 - 2 ^ k := by rw [h64]
          rw [mul_comm, h_eq]
          simp [hbit]
        · have htoNat : ((b l).testBit k).toNat = 0 := by simp [hbit]
          rw [htoNat, zero_mul]
          simp [hbit]

  rw [D3Q2A0.mulTerm, hAshift, hmul]
  have h_final_and : Nat.land (pack 64 L (fun l => a l * 2 ^ k))
      (pack 64 L (fun l => if (b l).testBit k then 2 ^ 64 - 2 ^ k else 0)) =
      pack 64 L (fun l => if (b l).testBit k then a l * 2 ^ k else 0) := by
    have h_lt1 : ∀ l < L, a l * 2 ^ k < 2 ^ 64 := ha
    have h_lt2 : ∀ l < L, (if (b l).testBit k then 2 ^ 64 - 2 ^ k else 0) < 2 ^ 64 := by
      intro l hl
      split_ifs with hbit
      · have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
        have : 2 ^ 64 - 2 ^ k < 2 ^ 64 := by omega
        exact this
      · exact pow_pos (by norm_num) 64
    have hland := land_pack 64 L (fun l => a l * 2 ^ k) (fun l => if (b l).testBit k then 2 ^ 64 - 2 ^ k else 0)
      hWpos h_lt1 h_lt2

    calc
      (pack 64 L fun l => a l * 2 ^ k).land (pack 64 L fun l => if (b l).testBit k then 2 ^ 64 - 2 ^ k else 0)
          = (pack 64 L fun l => a l * 2 ^ k) &&& (pack 64 L fun l => if (b l).testBit k then 2 ^ 64 - 2 ^ k else 0) := rfl
      _ = pack 64 L (fun l => (a l * 2 ^ k) &&& (if (b l).testBit k then 2 ^ 64 - 2 ^ k else 0)) := by rw [hland]
      _ = pack 64 L (fun l => if (b l).testBit k then a l * 2 ^ k else 0) := by
        refine pack_congr 64 L _ _ fun l hl => ?_
        by_cases hbit : (b l).testBit k
        · simp [hbit]
          apply h_and_sub (a l) (ha l hl)
        · simp [hbit]
  rw [h_final_and]

theorem D3Q2A0.mulF_pack (K L : ℕ) (a b : ℕ → ℕ) (hK : K ≤ 64) (ha : ∀ l < L, a l < 2 ^ (64 - K))
    (hb : ∀ l < L, b l < 2 ^ K) :
    mulF K (pack 64 L fun _ => 1) (pack 64 L a) (pack 64 L b) = pack 64 L (fun l => a l * b l) := by
  rw [D3Q2A0.mulF_eq_sum]
  have hsum : (∑ k ∈ Finset.range K, mulTerm (pack 64 L fun _ => 1) (pack 64 L a) (pack 64 L b) k) =
      ∑ k ∈ Finset.range K, pack 64 L (fun l => if (b l).testBit k then a l * 2 ^ k else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk64 : k < 64 := by
      have hk_lt_K : k < K := Finset.mem_range.1 hk
      omega
    have ha' : ∀ l < L, a l * 2 ^ k < 2 ^ 64 := by
      intro l hl
      have ha_l := ha l hl
      have hpow : 2 ^ k ≤ 2 ^ K :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt (Finset.mem_range.1 hk))
      calc
        a l * 2 ^ k < 2 ^ (64 - K) * 2 ^ k := Nat.mul_lt_mul_of_pos_right ha_l (by positivity)
        _ ≤ 2 ^ (64 - K) * 2 ^ K := Nat.mul_le_mul_left _ hpow
        _ = 2 ^ 64 := by rw [← pow_add, Nat.sub_add_cancel hK]
    have hb' : ∀ l < L, b l < 2 ^ 64 := by
      intro l hl
      have hb_l := hb l hl
      have hpow : 2 ^ K ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hK
      exact lt_of_lt_of_le hb_l hpow
    rw [D3Q2A0.mulTerm_pack L k a b hk64 ha' hb']
  rw [hsum]
  rw [D3Q2A0.pack_sum 64 L K (fun k l => if (b l).testBit k then a l * 2 ^ k else 0)]
  refine D3Dec.pack_congr 64 L (fun l => ∑ k ∈ Finset.range K, (if (b l).testBit k then a l * 2 ^ k else 0))
    (fun l => a l * b l) fun l hl => ?_
  calc
    ∑ k ∈ Finset.range K, (if (b l).testBit k then a l * 2 ^ k else 0)
        = a l * (∑ k ∈ Finset.range K, (if (b l).testBit k then 2 ^ k else 0)) := by
      simp [Finset.mul_sum, mul_ite, mul_zero]
    _ = a l * b l := by rw [D3Q2A0.sum_testBit K (b l) (hb l hl)]

theorem D3Q2A0.plt_pack (L : ℕ) (x y : ℕ → ℕ) (hx : ∀ l < L, x l < 2 ^ 63) (hy : ∀ l < L, y l < 2 ^ 63) :
    plt (pack 64 L fun _ => 1) (pack 64 L x) (pack 64 L y) = pack 64 L (fun l => if x l < y l then 1 else 0) := by
  set O := pack 64 L fun _ => 1 with hO
  have h2_63_val : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  have hmH : mH O = pack 64 L (fun _ => 2 ^ 63) := by
    rw [hO, mH, h2_63_val]
    calc
      pack 64 L (fun _ => 1) * 2 ^ 63 = 2 ^ 63 * pack 64 L (fun _ => 1) := by rw [mul_comm]
      _ = pack 64 L (fun l => 2 ^ 63 * 1) := by rw [pack_const_mul]
      _ = pack 64 L (fun _ => 2 ^ 63) := by simp
  have h_add_y : pack 64 L y + mH O = pack 64 L (fun l => y l + 2 ^ 63) := by
    rw [hmH, pack_add]
  have h_add_x : pack 64 L x + O = pack 64 L (fun l => x l + 1) := by
    rw [hO, pack_add]
  have h_le : ∀ l < L, x l + 1 ≤ y l + 2 ^ 63 := by
    intro l hl
    have hx' := hx l hl
    have hy' := hy l hl
    omega
  have h_sub : pack 64 L (fun l => y l + 2 ^ 63) - pack 64 L (fun l => x l + 1) = pack 64 L (fun l => (y l + 2 ^ 63) - (x l + 1)) := by
    rw [pack_sub 64 L (fun l => x l + 1) (fun l => y l + 2 ^ 63) h_le]
  have h_sub_lt : ∀ l < L, (y l + 2 ^ 63) - (x l + 1) < 2 ^ 64 := by
    intro l hl
    have hx' := hx l hl
    have hy' := hy l hl
    omega
  have h_land : Nat.land (Nat.sub (Nat.add (pack 64 L y) (mH O)) (Nat.add (pack 64 L x) O)) (mH O) =
      pack 64 L (fun l => if x l < y l then 2 ^ 63 else 0) := by
    rw [hmH, hO]
    change Nat.land (Nat.sub ((pack 64 L y) + (pack 64 L fun _ => 2 ^ 63)) ((pack 64 L x) + (pack 64 L fun _ => 1))) ((pack 64 L fun _ => 2 ^ 63))
      = pack 64 L (fun l => if x l < y l then 2 ^ 63 else 0)
    rw [pack_add, pack_add]

    have h_sub' : Nat.sub (pack 64 L (fun l => y l + 2 ^ 63)) (pack 64 L (fun l => x l + 1)) = pack 64 L (fun l => (y l + 2 ^ 63) - (x l + 1)) := by
      simpa using h_sub
    rw [h_sub']
    have h_lt1 : ∀ l < L, (y l + 2 ^ 63) - (x l + 1) < 2 ^ 64 := h_sub_lt
    have h_lt2 : ∀ l < L, (2 ^ 63 : ℕ) < 2 ^ 64 := by
      intro l hl; norm_num
    have h_land_eq := land_pack 64 L (fun l => (y l + 2 ^ 63) - (x l + 1)) (fun _ => 2 ^ 63) (by norm_num) h_lt1 h_lt2
    have h_temp : Nat.land (pack 64 L (fun l => (y l + 2 ^ 63) - (x l + 1))) (pack 64 L (fun _ => 2 ^ 63)) =
        pack 64 L (fun l => ((y l + 2 ^ 63) - (x l + 1)) &&& 2 ^ 63) := by
      simpa using h_land_eq
    rw [h_temp]
    apply pack_congr 64 L
    intro l hl
    have hz : (y l + 2 ^ 63) - (x l + 1) < 2 ^ 64 := h_sub_lt l hl
    rw [land_two_pow 64 ((y l + 2 ^ 63) - (x l + 1)) (by norm_num) hz]
    by_cases hxy : x l < y l
    · have hineq' : 9223372036854775808 ≤ y l + 9223372036854775807 - x l := by omega
      simp [hxy, hineq']
    · have hineq' : ¬ (9223372036854775808 ≤ y l + 9223372036854775807 - x l) := by omega
      simp [hxy, hineq']
  have h_shift : Nat.shiftRight (Nat.land (Nat.sub (Nat.add (pack 64 L y) (mH O)) (Nat.add (pack 64 L x) O)) (mH O)) 63 =
      pack 64 L (fun l => if x l < y l then 1 else 0) := by
    rw [h_land]
    have h_temp : pack 64 L (fun l => if x l < y l then 2 ^ 63 else 0) = 2 ^ 63 * pack 64 L (fun l => if x l < y l then 1 else 0) := by
      calc
        pack 64 L (fun l => if x l < y l then 2 ^ 63 else 0) = pack 64 L (fun l => 2 ^ 63 * (if x l < y l then 1 else 0)) := by
          apply pack_congr 64 L
          intro l hl
          by_cases hxy : x l < y l
          · simp [hxy]
          · simp [hxy]
        _ = 2 ^ 63 * pack 64 L (fun l => if x l < y l then 1 else 0) := by rw [pack_const_mul]
    rw [h_temp]
    have hpos : 0 < 2 ^ 63 := by norm_num
    have hcalc : (2 ^ 63 * pack 64 L (fun l => if x l < y l then 1 else 0)) >>> 63 = pack 64 L (fun l => if x l < y l then 1 else 0) := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.mul_div_cancel_left _ hpos
    simpa using hcalc
  unfold plt
  rw [h_shift]

theorem D3Q2A0.psub_pack (L : ℕ) (x y : ℕ → ℕ) (hx : ∀ l < L, x l < 2 ^ 63) (hy : ∀ l < L, y l < 2 ^ 63) :
    psub (pack 64 L fun _ => 1) (pack 64 L x) (pack 64 L y) = pack 64 L (fun l => x l - y l) := by
  set O := pack 64 L (fun _ => 1) with hO
  have hmH : D3Q2A0.mH O = pack 64 L (fun _ => 2 ^ 63) := by
    rw [D3Q2A0.mH, hO]
    calc
      (pack 64 L (fun _ => 1)) * 9223372036854775808 = (pack 64 L (fun _ => 1)) * (2 ^ 63) := by norm_num
      _ = 2 ^ 63 * pack 64 L (fun _ => 1) := by ring
      _ = pack 64 L (fun _ => 2 ^ 63) := by
        rw [D3Dec.pack_const_mul]
        simp
  have hpsub_unfold : psub O (pack 64 L x) (pack 64 L y) =
      Nat.land (Nat.sub ((pack 64 L x).add (D3Q2A0.mH O)) (pack 64 L y))
        (D3Q2A0.pmask (Nat.shiftRight
          (Nat.land (Nat.sub ((pack 64 L x).add (D3Q2A0.mH O)) (pack 64 L y)) (D3Q2A0.mH O)) 63)) := rfl
  rw [hpsub_unfold, hmH]

  have h_add : (pack 64 L x).add (pack 64 L (fun _ => 2 ^ 63)) = pack 64 L (fun l => x l + 2 ^ 63) :=
    D3Dec.pack_add 64 L x (fun _ => 2 ^ 63)
  rw [h_add]

  have h_sub : (pack 64 L (fun l => x l + 2 ^ 63)).sub (pack 64 L y) = pack 64 L (fun l => x l + 2 ^ 63 - y l) :=
    D3Dec.pack_sub 64 L y (fun l => x l + 2 ^ 63) (by
      intro l hl; have hx := hx l hl; have hy := hy l hl; omega)
  rw [h_sub]

  have hWpos : 0 < 64 := by norm_num
  have h_lane_lt : ∀ l < L, x l + 2 ^ 63 - y l < 2 ^ 64 := by
    intro l hl; have hx := hx l hl; have hy := hy l hl; omega
  have h_land_guard : Nat.land (pack 64 L (fun l => x l + 2 ^ 63 - y l)) (pack 64 L (fun _ => 2 ^ 63)) =
      pack 64 L (fun l => (x l + 2 ^ 63 - y l) &&& (2 ^ 63)) :=
    D3Dec.land_pack 64 L (fun l => x l + 2 ^ 63 - y l) (fun _ => 2 ^ 63) hWpos h_lane_lt
      (fun l hl => Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [h_land_guard]

  have h92 : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  have h_and_guard : ∀ l < L, (x l + 2 ^ 63 - y l) &&& (2 ^ 63) = if y l ≤ x l then 2 ^ 63 else 0 := by
    intro l hl
    have hbound : x l + 2 ^ 63 - y l < 2 ^ 64 := h_lane_lt l hl
    have h := D3Dec.land_two_pow 64 (x l + 2 ^ 63 - y l) hWpos hbound
    have h_simp : (2 : ℕ) ^ (64 - 1) = 2 ^ 63 := by norm_num
    rw [h_simp] at h
    rw [h_simp] at h
    by_cases hle : y l ≤ x l
    · have hle' : 2 ^ 63 ≤ x l + 2 ^ 63 - y l := by omega
      rw [ite_eq_left hle'] at h
      simpa [h92, hle] using h
    · have hnot : ¬ 2 ^ 63 ≤ x l + 2 ^ 63 - y l := by omega
      rw [ite_eq_right hnot] at h
      simpa [h92, hle] using h
  have h_guard_pack : pack 64 L (fun l => (x l + 2 ^ 63 - y l) &&& (2 ^ 63)) =
      pack 64 L (fun l => if y l ≤ x l then 2 ^ 63 else 0) := by
    apply D3Dec.pack_congr 64 L _ _ h_and_guard
  rw [h_guard_pack]

  have h_shift_guard : Nat.shiftRight (pack 64 L (fun l => if y l ≤ x l then 2 ^ 63 else 0)) 63 =
      pack 64 L (fun l => if y l ≤ x l then 1 else 0) := by
    have h_eq : pack 64 L (fun l => if y l ≤ x l then 2 ^ 63 else 0) =
        2 ^ 63 * pack 64 L (fun l => if y l ≤ x l then 1 else 0) := by
      calc
        pack 64 L (fun l => if y l ≤ x l then 2 ^ 63 else 0) =
            pack 64 L (fun l => 2 ^ 63 * (if y l ≤ x l then 1 else 0)) := by
          apply D3Dec.pack_congr 64 L _ _
          intro l hl
          by_cases hle : y l ≤ x l
          · simp [hle]
          · simp [hle]
        _ = 2 ^ 63 * pack 64 L (fun l => if y l ≤ x l then 1 else 0) := by
          rw [D3Dec.pack_const_mul]
    have hpos : 0 < 2 ^ 63 := by norm_num
    rw [h_eq]
    simpa [Nat.shiftRight_eq_div_pow] using (Nat.mul_div_cancel_left (pack 64 L (fun l => if y l ≤ x l then 1 else 0)) hpos)
  rw [h_shift_guard]

  have h_pmask_pack : D3Q2A0.pmask (pack 64 L (fun l => if y l ≤ x l then 1 else 0)) =
      pack 64 L (fun l => if y l ≤ x l then 2 ^ 63 - 1 else 0) := by
    rw [D3Q2A0.pmask]
    have h92' : (9223372036854775807 : ℕ) = 2 ^ 63 - 1 := by norm_num
    rw [h92']
    calc
      (pack 64 L (fun l => if y l ≤ x l then 1 else 0)) * (2 ^ 63 - 1) =
          (2 ^ 63 - 1) * pack 64 L (fun l => if y l ≤ x l then 1 else 0) := by ring
      _ = pack 64 L (fun l => (2 ^ 63 - 1) * (if y l ≤ x l then 1 else 0)) := by
        rw [D3Dec.pack_const_mul]
      _ = pack 64 L (fun l => if y l ≤ x l then 2 ^ 63 - 1 else 0) := by
        apply D3Dec.pack_congr 64 L _ _
        intro l hl
        by_cases hle : y l ≤ x l
        · simp [hle]
        · simp [hle]
  rw [h_pmask_pack]

  have h_lane2_lt : ∀ l < L, (if y l ≤ x l then 2 ^ 63 - 1 else 0) < 2 ^ 64 := by
    intro l hl
    by_cases hle : y l ≤ x l
    · rw [if_pos hle]; omega
    · rw [if_neg hle]; omega
  have h_final_land : Nat.land (pack 64 L (fun l => x l + 2 ^ 63 - y l))
      (pack 64 L (fun l => if y l ≤ x l then 2 ^ 63 - 1 else 0)) =
      pack 64 L (fun l => (x l + 2 ^ 63 - y l) &&& (if y l ≤ x l then 2 ^ 63 - 1 else 0)) :=
    D3Dec.land_pack 64 L (fun l => x l + 2 ^ 63 - y l) (fun l => if y l ≤ x l then 2 ^ 63 - 1 else 0)
      hWpos h_lane_lt h_lane2_lt
  rw [h_final_land]

  apply D3Dec.pack_congr 64 L _ _
  intro l hl
  have hx := hx l hl
  have hy := hy l hl
  by_cases hle : y l ≤ x l
  · rw [if_pos hle]
    have hd : x l - y l < 2 ^ 63 := by omega
    have h_eq : x l + 2 ^ 63 - y l = (x l - y l) + 2 ^ 63 := by omega
    rw [h_eq]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    rw [Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt hd]
  · rw [if_neg hle]
    simp
    rw [Nat.sub_eq_zero_of_le (by omega : x l ≤ y l)]

theorem D3Q2A0.pshr_pack (L s : ℕ) (x : ℕ → ℕ) (hs : s ≤ 64) (hx : ∀ l < L, x l < 2 ^ 64) :
    Nat.land (Nat.shiftRight (pack 64 L x) s) (Nat.mul (pack 64 L fun _ => 1) (2 ^ (64 - s) - 1)) =
      pack 64 L (fun l => x l >>> s) := by
  have hW : 0 < 64 := by norm_num
  have hx_shift : ∀ l < L, x l >>> s < 2 ^ 64 := by
    intro l hl
    have h := hx l hl
    have hle : x l >>> s ≤ x l := Nat.shiftRight_le _ _
    exact Nat.lt_of_le_of_lt hle h
  have hmask : Nat.mul (pack 64 L fun _ => 1) (2 ^ (64 - s) - 1) = pack 64 L (fun _ => 2 ^ (64 - s) - 1) := by
    simpa [mul_comm, mul_one] using pack_const_mul 64 L (2 ^ (64 - s) - 1) (fun _ => 1)
  rw [hmask]
  apply Nat.eq_of_testBit_eq
  intro n
  dsimp [Nat.land]
  rw [Nat.testBit_land, Nat.testBit_shiftRight]
  rw [add_comm s n]
  have hmask_lt : ∀ l < L, (fun _ : ℕ => 2 ^ (64 - s) - 1) l < 2 ^ 64 := by
    intro l hl
    by_cases hz : 64 - s = 0
    · rw [hz]; norm_num
    · have hpos : 0 < 2 ^ (64 - s) := pow_pos (by norm_num) _
      have hlt : 2 ^ (64 - s) - 1 < 2 ^ (64 - s) := Nat.sub_lt hpos (by norm_num)
      have hle : 2 ^ (64 - s) ≤ 2 ^ 64 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact Nat.lt_of_lt_of_le hlt hle
  rw [testBit_pack 64 L x hW (hx) (n + s),
    testBit_pack 64 L (fun l => x l >>> s) hW hx_shift n,
    testBit_pack 64 L (fun _ => 2 ^ (64 - s) - 1) hW hmask_lt n]
  simp only [Nat.testBit_two_pow_sub_one]
  by_cases hq : n / 64 < L
  · rw [if_pos hq]
    rw [Nat.testBit_shiftRight]
    by_cases hr : n % 64 < 64 - s
    ·
      have hrs : n % 64 + s < 64 := by omega
      have hs_lt_64 : s < 64 := by omega
      have hs_mod : s % 64 = s := Nat.mod_eq_of_lt hs_lt_64
      have hsum_mod' : (n + s) % 64 = n % 64 + s % 64 :=
        Nat.add_mod_of_add_mod_lt (by rw [hs_mod]; exact hrs)
      have hsum_mod : (n + s) % 64 = n % 64 + s := by rwa [hs_mod] at hsum_mod'
      have hsum_div' : (n + s) / 64 = n / 64 + s / 64 :=
        Nat.add_div_eq_of_add_mod_lt (by rw [hs_mod]; exact hrs)
      have hs_div : s / 64 = 0 := Nat.div_eq_of_lt hs_lt_64
      have hsum_div : (n + s) / 64 = n / 64 := by rwa [hs_div, add_zero] at hsum_div'
      have hsum_div_lt : (n + s) / 64 < L := by rwa [hsum_div]
      rw [if_pos hsum_div_lt, hsum_mod]
      rw [show (n % 64 + s) = s + n % 64 by omega]
      rw [hsum_div]
      simp [hr, hq]
    ·
      have hge : 64 ≤ s + n % 64 := by omega
      have hxq : x (n / 64) < 2 ^ 64 := hx (n / 64) hq
      have hpow : 2 ^ 64 ≤ 2 ^ (s + n % 64) := Nat.pow_le_pow_right (by norm_num) hge
      have hbit : (x (n / 64)).testBit (s + n % 64) = false :=
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hxq hpow)
      simp [hr, hbit]
  ·
    simp [hq]

private lemma D3Q2A0.testBit_two_pow_sub_one (n i : ℕ) (hi : i < n) : (2 ^ n - 1).testBit i = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true]
  have hpos : 0 < 2 ^ i := pow_pos (by norm_num) i
  have hdiv : (2 ^ n - 1) / 2 ^ i = 2 ^ (n - i) - 1 := by
    apply Nat.div_eq_of_lt_le
    · have ha : 1 ≤ 2 ^ (n - i) := Nat.one_le_two_pow
      have h_pow : 2 ^ (n - i) * 2 ^ i = 2 ^ n := by
        rw [← pow_add, Nat.sub_add_cancel (by omega : i ≤ n)]
      have h_eq : (2 ^ (n - i) - 1) * 2 ^ i + 2 ^ i = 2 ^ n := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel ha, h_pow]
      have h_lt : (2 ^ (n - i) - 1) * 2 ^ i < (2 ^ (n - i) - 1) * 2 ^ i + 2 ^ i := by
        apply Nat.lt_add_of_pos_right
        exact hpos
      rw [h_eq] at h_lt
      have h_le : (2 ^ (n - i) - 1) * 2 ^ i ≤ (2 ^ n).pred :=
        Nat.le_pred_of_lt h_lt
      rw [Nat.pred_eq_sub_one] at h_le
      exact h_le
    · have ha : 1 ≤ 2 ^ (n - i) := Nat.one_le_two_pow
      rw [Nat.sub_add_cancel ha]
      have h_pow : 2 ^ (n - i) * 2 ^ i = 2 ^ n := by
        rw [← pow_add, Nat.sub_add_cancel (by omega : i ≤ n)]
      rw [h_pow]
      have hpos' : 0 < 2 ^ n := pow_pos (by norm_num) n
      exact Nat.sub_lt hpos' (by omega)
  rw [hdiv]
  have hpos' : 0 < n - i := by omega
  rcases Nat.exists_eq_succ_of_ne_zero hpos'.ne' with ⟨k, hk⟩
  rw [hk, pow_succ]
  rw [mul_comm]
  have h : 2 * 2 ^ k - 1 = 2 * (2 ^ k - 1) + 1 := by
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  rw [h]
  simp [Nat.add_mod]

lemma D3Q2A0.land_two_pow_sub_one_of_lt (x : ℕ) (hx : x < 2 ^ 63) : x &&& (2 ^ 63 - 1) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 63
  · have hmask : (2 ^ 63 - 1).testBit i = true := testBit_two_pow_sub_one 63 i hi
    rw [hmask]
    simp
  · by_cases hi63 : i = 63
    · subst hi63
      have hmask : (2 ^ 63 - 1).testBit 63 = false := by
        apply Nat.testBit_eq_false_of_lt
        omega
      have hx63 : x.testBit 63 = false :=
        Nat.testBit_eq_false_of_lt hx
      rw [hmask, hx63]
      simp
    · have hmask : (2 ^ 63 - 1).testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have : 2 ^ 63 - 1 < 2 ^ i := by
          refine lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by norm_num) (by omega : 63 ≤ i))
          omega
        exact this
      have hx_i : x.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have : 2 ^ 63 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega : 63 ≤ i)
        omega
      rw [hmask, hx_i]
      simp

theorem D3Q2A0.psel_pack (L : ℕ) (c : ℕ → Bool) (a b : ℕ → ℕ) (ha : ∀ l < L, a l < 2 ^ 63) (hb : ∀ l < L, b l < 2 ^ 63) :
    psel (pack 64 L fun l => if c l then 2 ^ 63 - 1 else 0) (pack 64 L a) (pack 64 L b) =
      pack 64 L (fun l => if c l then a l else b l) := by
  set M := pack 64 L fun l => if c l then 2 ^ 63 - 1 else 0 with hM
  set A := pack 64 L a with hA
  set B := pack 64 L b with hB
  have hM_lt : ∀ l < L, (fun l => if c l then 2 ^ 63 - 1 else 0) l < 2 ^ 64 := by
    intro l hl
    dsimp
    split_ifs
    · have : 2 ^ 63 - 1 < 2 ^ 64 := by
        have h : 2 ^ 63 < 2 ^ 64 := by norm_num
        omega
      exact this
    · omega
  have hA_lt : ∀ l < L, a l < 2 ^ 64 := fun l hl => by
    have h := ha l hl
    have : 2 ^ 63 < 2 ^ 64 := by norm_num
    omega
  have hB_lt : ∀ l < L, b l < 2 ^ 64 := fun l hl => by
    have h := hb l hl
    have : 2 ^ 63 < 2 ^ 64 := by norm_num
    omega
  have hRHS_lt : ∀ l < L, (fun l => if c l then a l else b l) l < 2 ^ 64 := by
    intro l hl
    dsimp
    split_ifs
    · exact hA_lt l hl
    · exact hB_lt l hl
  have hxor : ∀ (x y : Bool), y.xor (x.xor y) = x := by
    intro x y; cases x <;> cases y <;> simp
  apply Nat.eq_of_testBit_eq
  intro n

  simpa [psel, Nat.testBit_xor, Nat.testBit_land, hM, hA, hB] using
    (by

      rw [testBit_pack 64 L (fun l => if c l then a l else b l) (by norm_num) hRHS_lt]

      have h92 : (9223372036854775807 : ℕ) = 2 ^ 63 - 1 := by norm_num
      rw [h92]
      rw [testBit_pack 64 L a (by norm_num) hA_lt,
        testBit_pack 64 L b (by norm_num) hB_lt,
        testBit_pack 64 L (fun l => if c l then 2 ^ 63 - 1 else 0) (by norm_num) hM_lt]

      by_cases hn : n / 64 < L
      ·
        have hn' : n / 64 < L := hn

        simp [hn']
        set l := n / 64 with hl
        set r := n % 64 with hr
        have hr_lt : r < 64 := Nat.mod_lt n (by norm_num)
        by_cases hc : c l
        ·
          simp [hc]
          by_cases hr63 : r < 63
          · have hmask : (2 ^ 63 - 1).testBit r = true :=
              testBit_two_pow_sub_one 63 r hr63

            have h92 : (9223372036854775807 : ℕ) = 2 ^ 63 - 1 := by norm_num

            have hmask' : (9223372036854775807 : ℕ).testBit r = true := by
              rw [h92]
              exact hmask
            simp [hmask', hxor]
          · have hr63' : r = 63 := by omega
            rw [hr63']
            have ha63 : (a l).testBit 63 = false :=
              Nat.testBit_eq_false_of_lt (ha l hn)
            have hb63 : (b l).testBit 63 = false :=
              Nat.testBit_eq_false_of_lt (hb l hn)
            have hmask : (2 ^ 63 - 1).testBit 63 = false := by
              apply Nat.testBit_eq_false_of_lt
              omega
            have hmask' : (9223372036854775807 : ℕ).testBit 63 = false := by
              rw [h92]
              exact hmask
            simp [hmask', ha63, hb63]
        ·
          simp [hc]
      ·
        simp [hn])

theorem D3Q2A0.rep_pack (L v : ℕ) : rep (pack 64 L fun _ => 1) v = pack 64 L (fun _ => v) := by
  simpa [rep, mul_comm] using D3Dec.pack_const_mul 64 L v (fun _ => 1)

theorem D3Q2A0.pmask_pack (L : ℕ) (b : ℕ → ℕ) : pmask (pack 64 L b) = pack 64 L (fun l => b l * 9223372036854775807) := by
  unfold pmask
  simpa [mul_comm] using D3Dec.pack_const_mul 64 L 9223372036854775807 b

theorem D3Q2A0.pfm_pack (K L : ℕ) (a b : ℕ → ℕ) (hK : K ≤ 64) (ha : ∀ l < L, a l < 2 ^ (64 - K))
    (hb : ∀ l < L, b l < 2 ^ K) :
    pfm mulF K (pack 64 L fun _ => 1) (pack 64 L a) (pack 64 L b) = pack 64 L (fun l => fm (a l) (b l)) := by
  unfold pfm
  rw [mulF_pack K L a b hK ha hb]
  have hmask : (1099511627775 : ℕ) = 2 ^ (64 - 24) - 1 := by norm_num
  have hs24 : 24 ≤ 64 := by norm_num
  have hprod : ∀ l < L, a l * b l < 2 ^ 64 := by
    intro l hl
    have ha' := ha l hl
    have hb' := hb l hl
    have hpow : 2 ^ (64 - K) * 2 ^ K = 2 ^ 64 := by
      rw [← pow_add, Nat.sub_add_cancel hK]
    calc
      a l * b l < 2 ^ (64 - K) * 2 ^ K := Nat.mul_lt_mul_of_lt_of_lt ha' hb'
      _ = 2 ^ 64 := hpow
  rw [hmask]
  rw [pshr_pack L 24 (fun l => a l * b l) hs24 hprod]
  refine D3Dec.pack_congr 64 L (fun l => (a l * b l) >>> 24) (fun l => fm (a l) (b l)) ?_
  intro l hl
  unfold fm
  rw [Nat.shiftRight_eq_div_pow]

theorem D3Q2A0.pfmc_pack (L k : ℕ) (a : ℕ → ℕ) (ha : ∀ l < L, a l * k < 2 ^ 64) :
    pfmc (pack 64 L fun _ => 1) (pack 64 L a) k = pack 64 L (fun l => fm (a l) k) := by
  unfold pfmc fm
  have hmul : (pack 64 L a).mul k = pack 64 L (fun l => a l * k) := by
    simpa [mul_comm] using pack_const_mul 64 L k a
  have hmask_val : 1099511627775 = 2 ^ (64 - 24) - 1 := by norm_num
  have hmask_pack : (pack 64 L fun _ => 1).mul (2 ^ (64 - 24) - 1) = pack 64 L (fun _ => 2 ^ (64 - 24) - 1) := by
    calc
      (pack 64 L fun _ => 1).mul (2 ^ (64 - 24) - 1) = (2 ^ (64 - 24) - 1) * (pack 64 L fun _ => 1) := by
        simp [mul_comm]
      _ = pack 64 L (fun l => (2 ^ (64 - 24) - 1) * 1) := by rw [pack_const_mul]
      _ = pack 64 L (fun _ => 2 ^ (64 - 24) - 1) := by simp
  rw [hmul, hmask_val, hmask_pack]
  have h24le64 : 24 ≤ 64 := by norm_num
  have ha_mul : ∀ l < L, (a l * k) < 2 ^ 64 := ha
  rw [← hmask_pack]
  rw [pshr_pack L 24 (fun l => a l * k) h24le64 ha_mul]
  refine pack_congr 64 L (fun l => (a l * k) >>> 24) (fun l => (a l * k) / 2 ^ 24) ?_
  intro l hl
  rw [Nat.shiftRight_eq_div_pow]

theorem D3Q2A0.cosP_pack (L : ℕ) (z : ℕ → ℕ) (hz : ∀ l < L, z l ≤ 13176795) :
    cosP mulF (pack 64 L fun _ => 1) (pfm mulF 24 (pack 64 L fun _ => 1) (pack 64 L z) (pack 64 L z)) =
      pack 64 L (fun l => cosFix (z l)) := by
  set O := pack 64 L fun _ => 1 with hO
  set z2 := pfm mulF 24 O (pack 64 L z) (pack 64 L z) with hz2

  have hz_lt_2_24 : ∀ l < L, z l < 2 ^ 24 := by
    intro l hl
    have h := hz l hl
    have h13176795_lt : 13176795 < 2 ^ 24 := by norm_num
    exact lt_of_le_of_lt h h13176795_lt
  have hz_lt_2_40 : ∀ l < L, z l < 2 ^ 40 := by
    intro l hl
    have h := hz l hl
    have h13176795_lt : 13176795 < 2 ^ 40 := by norm_num
    exact lt_of_le_of_lt h h13176795_lt

  have hfmz_bound : ∀ l < L, fm (z l) (z l) < 2 ^ 24 := by
    intro l hl
    have hz_lt : z l < 2 ^ 24 := hz_lt_2_24 l hl
    unfold fm
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).2

    have hz_le : z l ≤ 2 ^ 24 := Nat.le_of_lt hz_lt
    exact Nat.mul_lt_mul_of_le_of_lt hz_le hz_lt (by norm_num : 0 < 2 ^ 24)
  have hfmz_lt_2_40 : ∀ l < L, fm (z l) (z l) < 2 ^ 40 := by
    intro l hl
    have h := hfmz_bound l hl
    have h24_lt_40 : 2 ^ 24 < 2 ^ 40 := by norm_num

    apply lt_of_lt_of_le h
    exact le_of_lt h24_lt_40
  have hfmz_mul_416_lt_2_64 : ∀ l < L, fm (z l) (z l) * 416 < 2 ^ 64 := by
    intro l hl
    have h := hfmz_bound l hl

    have hlt : fm (z l) (z l) * 416 < 2 ^ 24 * 416 := by
      apply Nat.mul_lt_mul_of_pos_right h
      norm_num
    have h24_mul_416_lt_2_64 : 2 ^ 24 * 416 < 2 ^ 64 := by norm_num
    apply lt_of_lt_of_le hlt
    exact le_of_lt h24_mul_416_lt_2_64

  have hfm2_bound : ∀ l < L, fm (fm (z l) (z l)) 416 < 2 ^ 24 := by
    intro l hl
    have h := hfmz_bound l hl

    have h_mul_lt : fm (z l) (z l) * 416 < 2 ^ 24 * 416 := by
      apply Nat.mul_lt_mul_of_pos_right h
      norm_num
    have h_div_lt : fm (z l) (z l) * 416 / 2 ^ 24 < 416 := by

      have h_eq : 2 ^ 24 * 416 = 416 * 2 ^ 24 := by ring
      rw [h_eq] at h_mul_lt
      exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).2 h_mul_lt
    have h416_lt : 416 < 2 ^ 24 := by norm_num
    unfold fm
    apply lt_of_lt_of_le h_div_lt
    exact le_of_lt h416_lt
  have hfm2_lt_416 : ∀ l < L, fm (fm (z l) (z l)) 416 < 416 := by
    intro l hl
    have h := hfmz_bound l hl
    have h_mul_lt : fm (z l) (z l) * 416 < 416 * 2 ^ 24 := by
      apply Nat.mul_lt_mul_of_pos_right h
      norm_num
    unfold fm
    exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).2 h_mul_lt
  have hfm2_le_23302 : ∀ l < L, fm (fm (z l) (z l)) 416 ≤ 23302 := by
    intro l hl; have h := hfm2_lt_416 l hl; omega

  have h_level2_sub_le : ∀ l < L, fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l)) ≤ 699051 := by
    intro l hl
    have ha : 23302 - fm (fm (z l) (z l)) 416 ≤ 23302 := by
      have h := hfm2_bound l hl; omega
    have hb : fm (z l) (z l) < 2 ^ 24 := hfmz_bound l hl
    unfold fm
    have hprod : (23302 - fm (fm (z l) (z l)) 416) * fm (z l) (z l) < 23302 * 2 ^ 24 :=
      Nat.mul_lt_mul_of_le_of_lt ha hb (by norm_num : 0 < 23302)
    have hdiv : (23302 - fm (fm (z l) (z l)) 416) * fm (z l) (z l) / 2 ^ 24 < 23302 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).2 hprod
    have hle : (23302 - fm (fm (z l) (z l)) 416) * fm (z l) (z l) / 2 ^ 24 ≤ 23302 := Nat.le_of_lt hdiv
    have : 23302 ≤ 699051 := by norm_num
    exact Nat.le_trans hle this

  have h_level3_sub_le : ∀ l < L, fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l)) ≤ 8388608 := by
    intro l hl
    have ha : 699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l)) ≤ 699051 := by
      have h := h_level2_sub_le l hl; omega
    have hb : fm (z l) (z l) < 2 ^ 24 := hfmz_bound l hl
    unfold fm
    have hprod : (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) * fm (z l) (z l) < 699051 * 2 ^ 24 :=
      Nat.mul_lt_mul_of_le_of_lt ha hb (by norm_num : 0 < 699051)
    have hdiv : (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) * fm (z l) (z l) / 2 ^ 24 < 699051 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).2 hprod
    have hle : (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) * fm (z l) (z l) / 2 ^ 24 ≤ 699051 := Nat.le_of_lt hdiv
    have : 699051 ≤ 8388608 := by norm_num
    exact Nat.le_trans hle this

  have h_level4_sub_le : ∀ l < L, fm (8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) (fm (z l) (z l)) ≤ 16777216 := by
    intro l hl
    have ha : 8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l)) ≤ 8388608 := by
      have h := h_level3_sub_le l hl; omega
    have hb : fm (z l) (z l) < 2 ^ 24 := hfmz_bound l hl
    unfold fm
    have hprod : (8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) * fm (z l) (z l) < 8388608 * 2 ^ 24 :=
      Nat.mul_lt_mul_of_le_of_lt ha hb (by norm_num : 0 < 8388608)
    have hdiv : (8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) * fm (z l) (z l) / 2 ^ 24 < 8388608 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).2 hprod
    have hle : (8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) * fm (z l) (z l) / 2 ^ 24 ≤ 8388608 := Nat.le_of_lt hdiv
    have : 8388608 ≤ 16777216 := by norm_num
    exact Nat.le_trans hle this

  have h_level2_arg_lt : ∀ l < L, 23302 - fm (fm (z l) (z l)) 416 < 2 ^ 40 := by
    intro l hl
    have h := hfm2_bound l hl
    have hsub_le : 23302 - fm (fm (z l) (z l)) 416 ≤ 23302 := Nat.sub_le _ _
    have h23302_lt : 23302 < 2 ^ 40 := by norm_num
    omega

  have h_level3_arg_lt : ∀ l < L, 699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l)) < 2 ^ 40 := by
    intro l hl
    have h := h_level2_sub_le l hl
    have hsub_le : 699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l)) ≤ 699051 :=
      Nat.sub_le _ _
    have h699051_lt : 699051 < 2 ^ 40 := by norm_num
    omega

  have h_level4_arg_lt : ∀ l < L, 8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l)) < 2 ^ 40 := by
    intro l hl
    have h := h_level3_sub_le l hl
    have hsub_le : 8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l)) ≤ 8388608 :=
      Nat.sub_le _ _
    have h8388608_lt : 8388608 < 2 ^ 40 := by norm_num
    omega

  unfold cosP

  have hz2_eq : z2 = pack 64 L (fun l => fm (z l) (z l)) := by
    rw [hz2, pfm_pack 24 L z z (by norm_num) hz_lt_2_40 hz_lt_2_24]
  rw [hz2_eq]

  have h_level1_inner : Nat.sub (rep O 23302) (pfmc O (pack 64 L (fun l => fm (z l) (z l))) 416) =
      pack 64 L (fun l => 23302 - fm (fm (z l) (z l)) 416) := by
    rw [rep_pack L 23302]
    have hpfmc : pfmc O (pack 64 L (fun l => fm (z l) (z l))) 416 =
        pack 64 L (fun l => fm (fm (z l) (z l)) 416) :=
      pfmc_pack L 416 (fun l => fm (z l) (z l)) hfmz_mul_416_lt_2_64
    rw [hpfmc]
    simpa using pack_sub 64 L (fun l => fm (fm (z l) (z l)) 416) (fun _ => 23302) hfm2_le_23302
  rw [h_level1_inner]

  have h_level2_pfm : pfm mulF 24 O (pack 64 L (fun l => 23302 - fm (fm (z l) (z l)) 416))
      (pack 64 L (fun l => fm (z l) (z l))) =
      pack 64 L (fun l => fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) := by
    rw [pfm_pack 24 L (fun l => 23302 - fm (fm (z l) (z l)) 416) (fun l => fm (z l) (z l))
      (by norm_num) h_level2_arg_lt hfmz_bound]
  rw [h_level2_pfm]

  have h_level3_inner : Nat.sub (rep O 699051)
      (pack 64 L (fun l => fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l)))) =
      pack 64 L (fun l => 699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) := by
    rw [rep_pack L 699051]
    simpa using pack_sub 64 L (fun l => fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l)))
      (fun _ => 699051) h_level2_sub_le
  rw [h_level3_inner]

  have h_level4_pfm : pfm mulF 24 O (pack 64 L (fun l => 699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))))
      (pack 64 L (fun l => fm (z l) (z l))) =
      pack 64 L (fun l => fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) := by
    rw [pfm_pack 24 L (fun l => 699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l)))
      (fun l => fm (z l) (z l)) (by norm_num) h_level3_arg_lt hfmz_bound]
  rw [h_level4_pfm]

  have h_level5_inner : Nat.sub (rep O 8388608)
      (pack 64 L (fun l => fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l)))) =
      pack 64 L (fun l => 8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) := by
    rw [rep_pack L 8388608]
    simpa using pack_sub 64 L (fun l => fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l)))
      (fun _ => 8388608) h_level3_sub_le
  rw [h_level5_inner]

  have h_level6_pfm : pfm mulF 24 O (pack 64 L (fun l => 8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))))
      (pack 64 L (fun l => fm (z l) (z l))) =
      pack 64 L (fun l => fm (8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) (fm (z l) (z l))) := by
    rw [pfm_pack 24 L (fun l => 8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l)))
      (fun l => fm (z l) (z l)) (by norm_num) h_level4_arg_lt hfmz_bound]
  rw [h_level6_pfm]

  have h_final_inner : Nat.sub (rep O 16777216)
      (pack 64 L (fun l => fm (8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) (fm (z l) (z l)))) =
      pack 64 L (fun l => 16777216 - fm (8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) (fm (z l) (z l))) := by
    rw [rep_pack L 16777216]
    simpa using pack_sub 64 L (fun l => fm (8388608 - fm (699051 - fm (23302 - fm (fm (z l) (z l)) 416) (fm (z l) (z l))) (fm (z l) (z l))) (fm (z l) (z l)))
      (fun _ => 16777216) h_level4_sub_le
  rw [h_final_inner]

  apply congrArg (pack 64 L)
  ext l
  unfold cosFix
  simp [fm, mul_comm]

theorem D3Q2A0.sinP_pack (L : ℕ) (z : ℕ → ℕ) (hz : ∀ l < L, z l ≤ 13176795) :
    sinP mulF (pack 64 L fun _ => 1) (pack 64 L z)
        (pfm mulF 24 (pack 64 L fun _ => 1) (pack 64 L z) (pack 64 L z)) =
      pack 64 L (fun l => sinFix (z l)) := by
  set O := pack 64 L fun _ => 1 with hO
  set A := pack 64 L z with hA
  set w := fun l => fm (z l) (z l) with hw_def

  have hz24 : ∀ l < L, z l < 2 ^ 24 := by
    intro l hl; have h := hz l hl; omega
  have hz40 : ∀ l < L, z l < 2 ^ 40 := by
    intro l hl; have h := hz l hl; omega
  have hw24 : ∀ l < L, w l < 2 ^ 24 := by
    intro l hl
    unfold w fm
    have hzl := hz l hl
    have hsq : z l * z l ≤ 13176795 * 13176795 := Nat.mul_le_mul hzl hzl
    have hmax : 13176795 * 13176795 < 2 ^ 48 := by norm_num
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).mpr
    calc
      z l * z l ≤ 13176795 * 13176795 := hsq
      _ < 2 ^ 48 := hmax
      _ = 2 ^ 24 * 2 ^ 24 := by ring
  have hw_mul_46_lt : ∀ l < L, w l * 46 < 2 ^ 64 := by
    intro l hl
    have hw := hw24 l hl
    have hprod : w l * 46 < 2 ^ 24 * 46 := Nat.mul_lt_mul_of_pos_right hw (by norm_num)
    have hmax : 2 ^ 24 * 46 < 2 ^ 64 := by norm_num
    omega

  have h_div_le : ∀ (a b : ℕ), b < 2 ^ 24 → a * b / 2 ^ 24 ≤ a := by
    intro a b hb
    by_cases ha : a = 0
    · subst a; simp
    · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
      have h_lt : a * b / 2 ^ 24 < a := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).mpr
        exact Nat.mul_lt_mul_of_pos_left hb ha_pos
      omega

  have h_fm46_le_3329 : ∀ l < L, fm (w l) 46 ≤ 3329 := by
    intro l hl
    unfold fm
    have h := h_div_le (w l) 46 (by norm_num : 46 < 2 ^ 24)
    have hw := hw24 l hl
    have hprod : w l * 46 < 2 ^ 24 * 3329 := by
      have h1 : w l * 46 < 2 ^ 24 * 46 := Nat.mul_lt_mul_of_pos_right hw (by norm_num)
      have h2 : 2 ^ 24 * 46 ≤ 2 ^ 24 * 3329 := Nat.mul_le_mul_left _ (by norm_num)
      omega
    have hdiv : w l * 46 / 2 ^ 24 < 3329 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).mpr hprod
    omega

  have h_fm3329_le_139810 : ∀ l < L, fm (3329 - fm (w l) 46) (w l) ≤ 139810 := by
    intro l hl
    unfold fm
    have hsub : 3329 - fm (w l) 46 ≤ 3329 := Nat.sub_le _ _
    have hw := hw24 l hl
    have hprod : (3329 - fm (w l) 46) * w l < 2 ^ 24 * 139810 := by
      have h1 : (3329 - fm (w l) 46) * w l ≤ 3329 * w l := Nat.mul_le_mul_right _ hsub
      have h2 : 3329 * w l < 3329 * 2 ^ 24 := Nat.mul_lt_mul_of_pos_left hw (by norm_num)
      have h3 : 3329 * 2 ^ 24 ≤ 2 ^ 24 * 139810 := by

        nlinarith
      omega
    have hdiv : (3329 - fm (w l) 46) * w l / 2 ^ 24 < 139810 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).mpr hprod
    exact Nat.le_of_lt hdiv

  have h_fm139810_le_2796203 : ∀ l < L, fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l) ≤ 2796203 := by
    intro l hl
    unfold fm
    have hsub : 139810 - fm (3329 - fm (w l) 46) (w l) ≤ 139810 := Nat.sub_le _ _
    have hw := hw24 l hl
    have hprod : (139810 - fm (3329 - fm (w l) 46) (w l)) * w l < 2 ^ 24 * 2796203 := by
      have h1 : (139810 - fm (3329 - fm (w l) 46) (w l)) * w l ≤ 139810 * w l := Nat.mul_le_mul_right _ hsub
      have h2 : 139810 * w l < 139810 * 2 ^ 24 := Nat.mul_lt_mul_of_pos_left hw (by norm_num)
      have h3 : 139810 * 2 ^ 24 ≤ 2 ^ 24 * 2796203 := by nlinarith
      omega
    have hdiv : (139810 - fm (3329 - fm (w l) 46) (w l)) * w l / 2 ^ 24 < 2796203 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).mpr hprod
    exact Nat.le_of_lt hdiv

  have h_fm2796203_le_16777216 : ∀ l < L, fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l) ≤ 16777216 := by
    intro l hl
    unfold fm
    have hsub : 2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l) ≤ 2796203 := Nat.sub_le _ _
    have hw := hw24 l hl
    have hprod : (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) * w l < 2 ^ 24 * 16777216 := by
      have h1 : (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) * w l ≤ 2796203 * w l := Nat.mul_le_mul_right _ hsub
      have h2 : 2796203 * w l < 2796203 * 2 ^ 24 := Nat.mul_lt_mul_of_pos_left hw (by norm_num)
      have h3 : 2796203 * 2 ^ 24 ≤ 2 ^ 24 * 16777216 := by nlinarith
      omega
    have hdiv : (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) * w l / 2 ^ 24 < 16777216 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 24)).mpr hprod
    exact Nat.le_of_lt hdiv

  have hB : pfm mulF 24 O A A = pack 64 L w :=
    pfm_pack 24 L z z (by omega) hz40 hz24
  have h_pfmc : pfmc O (pack 64 L w) 46 = pack 64 L (fun l => fm (w l) 46) :=
    pfmc_pack L 46 w hw_mul_46_lt
  have h_rep16777216 : rep O 16777216 = pack 64 L (fun _ => 16777216) := rep_pack L 16777216
  have h_rep2796203 : rep O 2796203 = pack 64 L (fun _ => 2796203) := rep_pack L 2796203
  have h_rep139810 : rep O 139810 = pack 64 L (fun _ => 139810) := rep_pack L 139810
  have h_rep3329 : rep O 3329 = pack 64 L (fun _ => 3329) := rep_pack L 3329

  unfold sinP

  rw [h_rep16777216, h_rep2796203, h_rep139810, h_rep3329]

  rw [hB]

  rw [h_pfmc]

  have h_sub1 : (pack 64 L fun _ : ℕ => 3329) - pack 64 L (fun l => fm (w l) 46) =
      pack 64 L (fun l => 3329 - fm (w l) 46) :=
    pack_sub 64 L (fun l => fm (w l) 46) (fun _ => 3329) (fun l hl => h_fm46_le_3329 l hl)
  have h_sub1' : (pack 64 L fun _ : ℕ => 3329).sub (pack 64 L fun l => fm (w l) 46) =
      pack 64 L (fun l => 3329 - fm (w l) 46) := by
    simpa using h_sub1
  rw [h_sub1']

  have h_pfm1 : pfm mulF 24 O (pack 64 L (fun l => 3329 - fm (w l) 46)) (pack 64 L w) =
      pack 64 L (fun l => fm (3329 - fm (w l) 46) (w l)) := by

    have ha : ∀ l < L, (fun l => 3329 - fm (w l) 46) l < 2 ^ (64 - 24) := by
      intro l hl
      have hle : 3329 - fm (w l) 46 ≤ 3329 := Nat.sub_le _ _
      have h_lt : 3329 < 2 ^ (64 - 24) := by norm_num
      exact Nat.lt_of_le_of_lt hle h_lt
    exact pfm_pack 24 L (fun l => 3329 - fm (w l) 46) w (by omega) ha hw24
  rw [h_pfm1]

  have h_sub2 : pack 64 L (fun _ : ℕ => 139810) - pack 64 L (fun l => fm (3329 - fm (w l) 46) (w l)) =
      pack 64 L (fun l => 139810 - fm (3329 - fm (w l) 46) (w l)) :=
    pack_sub 64 L (fun l => fm (3329 - fm (w l) 46) (w l)) (fun _ => 139810) (fun l hl => h_fm3329_le_139810 l hl)
  have h_sub2' : (pack 64 L fun _ : ℕ => 139810).sub (pack 64 L fun l => fm (3329 - fm (w l) 46) (w l)) =
      pack 64 L (fun l => 139810 - fm (3329 - fm (w l) 46) (w l)) := by
    simpa using h_sub2
  rw [h_sub2']

  have h_pfm2 : pfm mulF 24 O (pack 64 L (fun l => 139810 - fm (3329 - fm (w l) 46) (w l))) (pack 64 L w) =
      pack 64 L (fun l => fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) := by
    have ha : ∀ l < L, (fun l => 139810 - fm (3329 - fm (w l) 46) (w l)) l < 2 ^ (64 - 24) := by
      intro l hl
      have hle : 139810 - fm (3329 - fm (w l) 46) (w l) ≤ 139810 := Nat.sub_le _ _
      have h_lt : 139810 < 2 ^ (64 - 24) := by norm_num
      exact Nat.lt_of_le_of_lt hle h_lt
    exact pfm_pack 24 L (fun l => 139810 - fm (3329 - fm (w l) 46) (w l)) w (by omega) ha hw24
  rw [h_pfm2]

  have h_sub3 : pack 64 L (fun _ : ℕ => 2796203) - pack 64 L (fun l => fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) =
      pack 64 L (fun l => 2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) :=
    pack_sub 64 L (fun l => fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (fun _ => 2796203) (fun l hl => h_fm139810_le_2796203 l hl)
  have h_sub3' : (pack 64 L fun _ : ℕ => 2796203).sub (pack 64 L fun l => fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) =
      pack 64 L (fun l => 2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) := by
    simpa using h_sub3
  rw [h_sub3']

  have h_pfm3 : pfm mulF 24 O (pack 64 L (fun l => 2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l))) (pack 64 L w) =
      pack 64 L (fun l => fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) := by
    have ha : ∀ l < L, (fun l => 2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) l < 2 ^ (64 - 24) := by
      intro l hl
      have hle : 2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l) ≤ 2796203 := Nat.sub_le _ _
      have h_lt : 2796203 < 2 ^ (64 - 24) := by norm_num
      exact Nat.lt_of_le_of_lt hle h_lt
    exact pfm_pack 24 L (fun l => 2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) w (by omega) ha hw24
  rw [h_pfm3]

  have h_sub4 : pack 64 L (fun _ : ℕ => 16777216) - pack 64 L (fun l => fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) =
      pack 64 L (fun l => 16777216 - fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) :=
    pack_sub 64 L (fun l => fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) (fun _ => 16777216) (fun l hl => h_fm2796203_le_16777216 l hl)
  have h_sub4' : (pack 64 L fun _ : ℕ => 16777216).sub (pack 64 L fun l => fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) =
      pack 64 L (fun l => 16777216 - fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) := by
    simpa using h_sub4
  rw [h_sub4']

  have h_pfm4 : pfm mulF 24 O (pack 64 L (fun l => 16777216 - fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l))) A =
      pack 64 L (fun l => fm (16777216 - fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) (z l)) := by
    have ha : ∀ l < L, (fun l => 16777216 - fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) l < 2 ^ (64 - 24) := by
      intro l hl
      have hle : 16777216 - fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l) ≤ 16777216 := Nat.sub_le _ _
      have h_lt : 16777216 < 2 ^ (64 - 24) := by norm_num
      exact Nat.lt_of_le_of_lt hle h_lt
    exact pfm_pack 24 L (fun l => 16777216 - fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) z (by omega) ha hz24
  rw [h_pfm4]

  apply pack_congr 64 L
  intro l hl
  have h_comm : ∀ (a b : ℕ), fm a b = fm b a := by
    intro a b; unfold fm; rw [Nat.mul_comm]
  calc
    fm (16777216 - fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) (z l)
        = fm (z l) (16777216 - fm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)) := by rw [h_comm]
    _ = fm (z l) (16777216 - fm (w l) (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l))) := by rw [h_comm (2796203 - fm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)) (w l)]
    _ = fm (z l) (16777216 - fm (w l) (2796203 - fm (w l) (139810 - fm (3329 - fm (w l) 46) (w l)))) := by rw [h_comm (139810 - fm (3329 - fm (w l) 46) (w l)) (w l)]
    _ = fm (z l) (16777216 - fm (w l) (2796203 - fm (w l) (139810 - fm (w l) (3329 - fm (w l) 46)))) := by rw [h_comm (3329 - fm (w l) 46) (w l)]
    _ = sinFix (z l) := by
      unfold sinFix fm w
      rfl

theorem D3Q2A0.sincosP24o_pack (L : ℕ) (x0 : ℕ → ℕ) (hx : ∀ l < L, x0 l ≤ 52707179) :
    sincosP24o mulF (pack 64 L fun _ => 1) (pack 64 L x0) =
      (pack 64 L (fun l => (sincos24o (x0 l)).1), pack 64 L (fun l => (sincos24o (x0 l)).2.1),
        pack 64 L (fun l => (sincos24o (x0 l)).2.2)) := by
  set O := pack 64 L fun _ => 1 with hO
  have hx63 : ∀ l < L, x0 l < 2 ^ 63 := by
    intro l hl
    have h := hx l hl
    have hpos : 52707179 < 2 ^ 63 := by norm_num
    omega
  have hx26353589_lt : ∀ l < L, (26353589 : ℕ) < 2 ^ 63 := by
    intro l hl; norm_num
  have hx13176794_lt : ∀ l < L, (13176794 : ℕ) < 2 ^ 63 := by
    intro l hl; norm_num

  set x' := fun l => if 26353589 < x0 l then 52707179 - x0 l else x0 l with hx'
  have hx'_bound : ∀ l < L, x' l ≤ 26353589 := by
    intro l hl
    unfold x'
    split_ifs with hlt
    · have hx0 : 26353590 ≤ x0 l := by omega
      omega
    · exact Nat.le_of_not_gt hlt
  have hx'_lt_2_63 : ∀ l < L, x' l < 2 ^ 63 := by
    intro l hl
    have h := hx'_bound l hl
    have hpos : 26353589 < 2 ^ 63 := by norm_num
    omega

  set z := fun l => if 13176794 < x' l then 26353589 - x' l else x' l with hz
  have hz_le_13176794 : ∀ l < L, z l ≤ 13176794 := by
    intro l hl
    unfold z
    split_ifs with hlt
    · have hx' := hx'_bound l hl
      omega
    · exact Nat.le_of_not_gt hlt
  have hz_lt_2_24 : ∀ l < L, z l < 2 ^ 24 := by
    intro l hl
    have h := hz_le_13176794 l hl
    have hpos : 13176794 < 2 ^ 24 := by norm_num
    omega
  have hz_lt_2_40 : ∀ l < L, z l < 2 ^ 40 := by
    intro l hl
    have h := hz_lt_2_24 l hl
    have hpos : 2 ^ 24 < 2 ^ 40 := by norm_num
    omega

  set c1 := fun l => decide (26353589 < x0 l) with hc1
  set c2 := fun l => decide (13176794 < x' l) with hc2
  have h2_63_minus_1 : (2 ^ 63 - 1 : ℕ) = 9223372036854775807 := by norm_num

  have h_negb : plt O (rep O 26353589) (pack 64 L x0) =
      pack 64 L (fun l => if c1 l then 1 else 0) := by
    rw [hc1]
    rw [D3Q2A0.rep_pack]
    rw [D3Q2A0.plt_pack L (fun _ => 26353589) x0 hx26353589_lt hx63]
    refine D3Dec.pack_congr 64 L _ _ fun l hl => ?_
    simp

  have h_nm' : pmask (plt O (rep O 26353589) (pack 64 L x0)) =
      pack 64 L (fun l => if c1 l then 2 ^ 63 - 1 else 0) := by
    rw [h_negb, D3Q2A0.pmask_pack]
    rw [h2_63_minus_1]
    refine D3Dec.pack_congr 64 L _ _ fun l hl => ?_
    simp [hc1]

  have h_psub : psub O (rep O 52707179) (pack 64 L x0) =
      pack 64 L (fun l => 52707179 - x0 l) := by
    rw [D3Q2A0.rep_pack]
    have h52707179_lt : ∀ l < L, (52707179 : ℕ) < 2 ^ 63 := by
      intro l hl; norm_num
    rw [D3Q2A0.psub_pack L (fun _ => 52707179) x0 h52707179_lt hx63]
  have h_x : psel (pmask (plt O (rep O 26353589) (pack 64 L x0)))
      (psub O (rep O 52707179) (pack 64 L x0)) (pack 64 L x0) =
      pack 64 L x' := by
    rw [h_nm', h_psub]
    have h52707179_sub_lt : ∀ l < L, (52707179 : ℕ) - x0 l < 2 ^ 63 := by
      intro l hl
      have hpos : 52707179 < 2 ^ 63 := by norm_num
      omega
    rw [D3Q2A0.psel_pack L c1 (fun l => 52707179 - x0 l) x0 h52707179_sub_lt hx63]
    refine D3Dec.pack_congr 64 L _ _ fun l hl => ?_
    unfold x' c1
    simp

  have h_swb : plt O (rep O 13176794) (pack 64 L x') =
      pack 64 L (fun l => if c2 l then 1 else 0) := by
    rw [hc2]
    rw [D3Q2A0.rep_pack]
    rw [D3Q2A0.plt_pack L (fun _ => 13176794) x' hx13176794_lt hx'_lt_2_63]
    refine D3Dec.pack_congr 64 L _ _ fun l hl => ?_
    simp
  have h_sm' : pmask (plt O (rep O 13176794) (pack 64 L x')) =
      pack 64 L (fun l => if c2 l then 2 ^ 63 - 1 else 0) := by
    rw [h_swb, D3Q2A0.pmask_pack]
    rw [h2_63_minus_1]
    refine D3Dec.pack_congr 64 L _ _ fun l hl => ?_
    simp [hc2]

  have h_sub : (rep O 26353589) - (pack 64 L x') =
      pack 64 L (fun l => 26353589 - x' l) := by
    rw [D3Q2A0.rep_pack]
    rw [D3Dec.pack_sub 64 L x' (fun _ => 26353589) (fun l hl => hx'_bound l hl)]
  have h_z : psel (pmask (plt O (rep O 13176794) (pack 64 L x')))
      ((rep O 26353589) - (pack 64 L x')) (pack 64 L x') =
      pack 64 L z := by
    rw [h_sm', h_sub]
    have h26353589_sub_lt : ∀ l < L, (26353589 : ℕ) - x' l < 2 ^ 63 := by
      intro l hl
      have hpos : 26353589 < 2 ^ 63 := by norm_num
      omega
    rw [D3Q2A0.psel_pack L c2 (fun l => 26353589 - x' l) x' h26353589_sub_lt hx'_lt_2_63]
    refine D3Dec.pack_congr 64 L _ _ fun l hl => ?_
    unfold z c2
    simp

  have h_z2 : pfm mulF 24 O (pack 64 L z) (pack 64 L z) =
      pack 64 L (fun l => fm (z l) (z l)) := by
    rw [D3Q2A0.pfm_pack 24 L z z (by omega) hz_lt_2_40 hz_lt_2_24]

  have h_cosP : cosP mulF O (pfm mulF 24 O (pack 64 L z) (pack 64 L z)) =
      pack 64 L (fun l => cosFix (z l)) := by
    rw [D3Q2A0.cosP_pack L z (fun l hl => by
      have h := hz_le_13176794 l hl
      omega)]
  have h_sinP : sinP mulF O (pack 64 L z) (pfm mulF 24 O (pack 64 L z) (pack 64 L z)) =
      pack 64 L (fun l => sinFix (z l)) := by
    rw [D3Q2A0.sinP_pack L z (fun l hl => by
      have h := hz_le_13176794 l hl
      omega)]

  have h_cosFix_lt : ∀ l < L, cosFix (z l) < 2 ^ 63 := by
    intro l hl
    have hzl := hz_le_13176794 l hl
    have : cosFix (z l) ≤ 16777216 := by
      unfold cosFix
      omega
    have hpos : 16777216 < 2 ^ 63 := by norm_num
    omega
  have h_sinFix_lt : ∀ l < L, sinFix (z l) < 2 ^ 63 := by
    intro l hl
    have hzl := hz_le_13176794 l hl
    have h_sinFix_le : sinFix (z l) ≤ z l := by
      have hg : 16777216 - (fm (fm (z l) (z l)) (2796203 - fm (fm (z l) (z l)) (139810 - fm (fm (z l) (z l)) (3329 - fm (fm (z l) (z l)) 46)))) ≤ 16777216 := by omega
      have hcalc : sinFix (z l) = (z l) * (16777216 - fm (fm (z l) (z l)) (2796203 - fm (fm (z l) (z l)) (139810 - fm (fm (z l) (z l)) (3329 - fm (fm (z l) (z l)) 46)))) / 2 ^ 24 := by
        simp [sinFix, fm]
      rw [hcalc]
      have hdiv : (z l) * (16777216 - fm (fm (z l) (z l)) (2796203 - fm (fm (z l) (z l)) (139810 - fm (fm (z l) (z l)) (3329 - fm (fm (z l) (z l)) 46)))) / 2 ^ 24 ≤ (z l) * 16777216 / 2 ^ 24 :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ hg)
      have h_eq : (z l) * 16777216 / 2 ^ 24 = z l := by
        have : 16777216 = 2 ^ 24 := by norm_num
        rw [this]
        simp
      exact le_trans hdiv (by rw [h_eq])
    have hpos : 13176794 < 2 ^ 63 := by norm_num
    exact lt_of_le_of_lt (le_trans h_sinFix_le hzl) hpos

  calc
    sincosP24o mulF O (pack 64 L x0) =
      let negb := plt O (rep O 26353589) (pack 64 L x0)
      let nm := pmask negb
      let x := psel nm (psub O (rep O 52707179) (pack 64 L x0)) (pack 64 L x0)
      let swb := plt O (rep O 13176794) x
      let sm := pmask swb
      let z := psel sm (Nat.sub (rep O 26353589) x) x
      let z2 := pfm mulF 24 O z z
      (psel sm (cosP mulF O z2) (sinP mulF O z z2), psel sm (sinP mulF O z z2) (cosP mulF O z2), negb) := rfl
    _ = (psel (pmask (plt O (rep O 13176794) (pack 64 L x')))
          (cosP mulF O (pfm mulF 24 O (pack 64 L z) (pack 64 L z)))
          (sinP mulF O (pack 64 L z) (pfm mulF 24 O (pack 64 L z) (pack 64 L z))),
        psel (pmask (plt O (rep O 13176794) (pack 64 L x')))
          (sinP mulF O (pack 64 L z) (pfm mulF 24 O (pack 64 L z) (pack 64 L z)))
          (cosP mulF O (pfm mulF 24 O (pack 64 L z) (pack 64 L z))),
        plt O (rep O 26353589) (pack 64 L x0)) := by
      simp [h_x, h_z]
    _ = (psel (pack 64 L (fun l => if c2 l then 2 ^ 63 - 1 else 0))
          (pack 64 L (fun l => cosFix (z l)))
          (pack 64 L (fun l => sinFix (z l))),
        psel (pack 64 L (fun l => if c2 l then 2 ^ 63 - 1 else 0))
          (pack 64 L (fun l => sinFix (z l)))
          (pack 64 L (fun l => cosFix (z l))),
        pack 64 L (fun l => if c1 l then 1 else 0)) := by
      rw [h_sm', h_cosP, h_sinP, h_negb]
    _ = (pack 64 L (fun l => if 13176794 < x' l then cosFix (z l) else sinFix (z l)),
        pack 64 L (fun l => if 13176794 < x' l then sinFix (z l) else cosFix (z l)),
        pack 64 L (fun l => if 26353589 < x0 l then 1 else 0)) := by
      rw [D3Q2A0.psel_pack L c2 (fun l => cosFix (z l)) (fun l => sinFix (z l)) h_cosFix_lt h_sinFix_lt]
      rw [D3Q2A0.psel_pack L c2 (fun l => sinFix (z l)) (fun l => cosFix (z l)) h_sinFix_lt h_cosFix_lt]
      simp [hc1, hc2]
    _ = (pack 64 L (fun l => (sincos24o (x0 l)).1),
        pack 64 L (fun l => (sincos24o (x0 l)).2.1),
        pack 64 L (fun l => (sincos24o (x0 l)).2.2)) := by
      refine Prod.ext ?_ ?_
      ·
        refine D3Dec.pack_congr 64 L _ _ fun l hl => ?_
        dsimp [x', z]
        have hx0 := hx l hl
        by_cases h1 : 26353589 < x0 l
        · have hx'_eq : x' l = 52707179 - x0 l := by
            unfold x'; simp [h1]
          have hz_cases : z l = if 13176794 < 52707179 - x0 l then 26353589 - (52707179 - x0 l) else 52707179 - x0 l := by
            unfold z; simp [h1, hx'_eq]
          by_cases h2 : 13176794 < 52707179 - x0 l
          · have hz_eq : z l = 26353589 - (52707179 - x0 l) := by rw [hz_cases]; simp [h2]
            simp [h1, h2, hz_eq, sincos24o]
          · have hz_eq : z l = 52707179 - x0 l := by rw [hz_cases]; simp [h2]
            simp [h1, h2, hz_eq, sincos24o]
        · have hx'_eq : x' l = x0 l := by unfold x'; simp [h1]
          have hz_cases : z l = if 13176794 < x0 l then 26353589 - x0 l else x0 l := by
            unfold z; simp [h1, hx'_eq]
          by_cases h2 : 13176794 < x0 l
          · have hz_eq : z l = 26353589 - x0 l := by rw [hz_cases]; simp [h2]
            simp [h1, h2, hz_eq, sincos24o]
          · have hz_eq : z l = x0 l := by rw [hz_cases]; simp [h2]
            simp [h1, h2, hz_eq, sincos24o]
      ·
        refine Prod.ext ?_ ?_
        ·
          refine D3Dec.pack_congr 64 L _ _ fun l hl => ?_
          dsimp [x', z]
          have hx0 := hx l hl
          by_cases h1 : 26353589 < x0 l
          · have hx'_eq : x' l = 52707179 - x0 l := by unfold x'; simp [h1]
            have hz_cases : z l = if 13176794 < 52707179 - x0 l then 26353589 - (52707179 - x0 l) else 52707179 - x0 l := by
              unfold z; simp [h1, hx'_eq]
            by_cases h2 : 13176794 < 52707179 - x0 l
            · have hz_eq : z l = 26353589 - (52707179 - x0 l) := by rw [hz_cases]; simp [h2]
              simp [h1, h2, hz_eq, sincos24o]
            · have hz_eq : z l = 52707179 - x0 l := by rw [hz_cases]; simp [h2]
              simp [h1, h2, hz_eq, sincos24o]
          · have hx'_eq : x' l = x0 l := by unfold x'; simp [h1]
            have hz_cases : z l = if 13176794 < x0 l then 26353589 - x0 l else x0 l := by
              unfold z; simp [h1, hx'_eq]
            by_cases h2 : 13176794 < x0 l
            · have hz_eq : z l = 26353589 - x0 l := by rw [hz_cases]; simp [h2]
              simp [h1, h2, hz_eq, sincos24o]
            · have hz_eq : z l = x0 l := by rw [hz_cases]; simp [h2]
              simp [h1, h2, hz_eq, sincos24o]
        ·
          refine D3Dec.pack_congr 64 L _ _ fun l hl => ?_
          have hx0 := hx l hl
          by_cases h1 : 26353589 < x0 l
          · have hx'_eq : x' l = 52707179 - x0 l := by unfold x'; simp [h1]
            have hz_cases : z l = if 13176794 < 52707179 - x0 l then 26353589 - (52707179 - x0 l) else 52707179 - x0 l := by
              unfold z; simp [h1, hx'_eq]
            by_cases h2 : 13176794 < 52707179 - x0 l
            · have hz_eq : z l = 26353589 - (52707179 - x0 l) := by rw [hz_cases]; simp [h2]
              simp [h1, h2, hz_eq, sincos24o]
            · have hz_eq : z l = 52707179 - x0 l := by rw [hz_cases]; simp [h2]
              simp [h1, h2, hz_eq, sincos24o]
          · have hx'_eq : x' l = x0 l := by unfold x'; simp [h1]
            have hz_cases : z l = if 13176794 < x0 l then 26353589 - x0 l else x0 l := by
              unfold z; simp [h1, hx'_eq]
            by_cases h2 : 13176794 < x0 l
            · have hz_eq : z l = 26353589 - x0 l := by rw [hz_cases]; simp [h2]
              simp [h1, h2, hz_eq, sincos24o]
            · have hz_eq : z l = x0 l := by rw [hz_cases]; simp [h2]
              simp [h1, h2, hz_eq, sincos24o]
