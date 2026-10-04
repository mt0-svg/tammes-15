import Tammes15.D3Ck2.Unr
import Tammes15.D3Ck2.Spec.Scalar
import Tammes15.D3Pack.Lanes24

namespace D3Ck2Spec

def lane (A l : ℕ) : ℕ := A / 2 ^ (64 * l) % 2 ^ 64

def Fits (n b A : ℕ) : Prop := A < 2 ^ (64 * n) ∧ ∀ i < n, lane A i < b

def sv (x : ℕ) : ℤ := (x : ℤ) - 2 ^ 62

theorem lane_lt (A l : ℕ) : lane A l < 2 ^ 64 := Nat.mod_lt _ (by positivity)

theorem lane_zero (A : ℕ) (hA : A < 2 ^ 64) : lane A 0 = A := by
  simpa [lane] using Nat.mod_eq_of_lt hA

open Finset in

theorem oN_eq (n : ℕ) : D3Ck2.oN n = ∑ k ∈ range n, (2 ^ 64) ^ k := by
  rw [Nat.geomSum_eq (by norm_num) n]
  unfold D3Ck2.oN
  show (1 <<< (n <<< 6) - 1) / 18446744073709551615 = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, ← pow_mul, show n * 2 ^ 6 = 64 * n by ring]
  norm_num

open Finset in
theorem geom64_lt (n : ℕ) : ∑ k ∈ range n, (2 ^ 64) ^ k < 2 ^ (64 * n) := by
  rw [Nat.geomSum_eq (by norm_num) n, ← pow_mul]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt (by positivity) (by norm_num))

theorem lane_oN (n l : ℕ) (hl : l < n) : lane (D3Ck2.oN n) l = 1 := by
  rw [oN_eq]
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ, ← pow_mul]
    have hS := geom64_lt n
    unfold lane
    rcases Nat.lt_or_ge l n with h | h
    · have hd : 2 ^ (64 * l) ∣ 2 ^ (64 * n) := pow_dvd_pow 2 (by omega)
      rw [Nat.add_div_of_dvd_left hd, Nat.pow_div (by omega) (by norm_num),
        show 64 * n - 64 * l = 64 + 64 * (n - l - 1) by omega, pow_add, Nat.add_mul_mod_self_left]
      exact ih h
    · obtain rfl : l = n := by omega
      rw [Nat.add_div_of_dvd_left (dvd_refl _), Nat.div_self (by positivity), Nat.div_eq_of_lt hS]
      norm_num

theorem oN_lt (n : ℕ) : D3Ck2.oN n < 2 ^ (64 * n) := by
  rw [oN_eq]; exact geom64_lt n

theorem oN_pack (n : ℕ) : D3Ck2.oN n = D3Dec.pack 64 n (fun _ => 1) := by
  rw [oN_eq]; unfold D3Dec.pack
  exact Finset.sum_congr rfl fun k _ => by rw [one_mul, pow_mul]

theorem pack_lane_mod (n A : ℕ) : D3Dec.pack 64 n (lane A) = A % 2 ^ (64 * n) := by
  induction n with
  | zero => simp only [D3Dec.pack, Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [D3Dec.pack_succ, ih, show 64 * (n + 1) = 64 * n + 64 by ring, pow_add, Nat.mod_mul, lane]; ring

theorem pack_lane (n A : ℕ) (hA : A < 2 ^ (64 * n)) : D3Dec.pack 64 n (lane A) = A := by
  rw [pack_lane_mod, Nat.mod_eq_of_lt hA]

theorem lane_pack (n : ℕ) (f : ℕ → ℕ) (hf : ∀ l < n, f l < 2 ^ 64) (l : ℕ) (hl : l < n) :
    lane (D3Dec.pack 64 n f) l = f l :=
  D3Dec.pack_div_mod 64 n f hf l hl

theorem fits_pack (n b : ℕ) (f : ℕ → ℕ) (hb : b ≤ 2 ^ 64) (hf : ∀ l < n, f l < b) :
    Fits n b (D3Dec.pack 64 n f) := by
  have hf' : ∀ l < n, f l < 2 ^ 64 := fun l hl => lt_of_lt_of_le (hf l hl) hb
  exact ⟨D3Dec.pack_lt 64 n f hf', fun i hi => by rw [lane_pack n f hf' i hi]; exact hf i hi⟩

theorem mulF_eq (K O A B : ℕ) : Lanes24.mulF K O A B = D3Q2A0.mulF K O A B := rfl
theorem plt_eq (O x y : ℕ) : Lanes24.plt O x y = D3Q2A0.plt O x y := rfl
theorem psub_eq (O x y : ℕ) : Lanes24.psub O x y = D3Q2A0.psub O x y := rfl

theorem lane_land (A B l : ℕ) : lane (Nat.land A B) l = Nat.land (lane A l) (lane B l) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h_and_distrib : ∀ (d a b : Bool), (d && (a && b)) = ((d && a) && (d && b)) := by
    intro d a b
    match d with
    | true => simp
    | false => simp
  calc
    (lane (Nat.land A B) l).testBit i
        = ((Nat.land A B) / 2 ^ (64 * l) % 2 ^ 64).testBit i := rfl
    _ = (decide (i < 64) && ((Nat.land A B) / 2 ^ (64 * l)).testBit i) := by
      rw [Nat.testBit_mod_two_pow]
    _ = (decide (i < 64) && (Nat.land A B).testBit (i + 64 * l)) := by
      rw [Nat.testBit_div_two_pow]
    _ = (decide (i < 64) && ((A.testBit (i + 64 * l) && B.testBit (i + 64 * l)))) := by
      rw [Nat.land_eq, Nat.testBit_land]
    _ = ((decide (i < 64) && A.testBit (i + 64 * l)) && (decide (i < 64) && B.testBit (i + 64 * l))) := by
      rw [h_and_distrib]
    _ = ((A / 2 ^ (64 * l) % 2 ^ 64).testBit i && (B / 2 ^ (64 * l) % 2 ^ 64).testBit i) := by
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    _ = ((lane A l).testBit i && (lane B l).testBit i) := rfl
    _ = (Nat.land (lane A l) (lane B l)).testBit i := by
      rw [Nat.land_eq, Nat.testBit_land]

theorem lane_lor (A B l : ℕ) : lane (Nat.lor A B) l = Nat.lor (lane A l) (lane B l) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lane]
  have hright : ((A / 2 ^ (64 * l) % 2 ^ 64).lor (B / 2 ^ (64 * l) % 2 ^ 64)).testBit i =
      ((A / 2 ^ (64 * l) % 2 ^ 64).testBit i || (B / 2 ^ (64 * l) % 2 ^ 64).testBit i) := by
    simp
  rw [hright]
  rw [Nat.testBit_mod_two_pow]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  have hleft : (A.lor B).testBit (i + 64 * l) = (A.testBit (i + 64 * l) || B.testBit (i + 64 * l)) := by
    simp
  rw [hleft]
  rw [Bool.and_or_distrib_left]

theorem lane_xor (A B l : ℕ) : lane (Nat.xor A B) l = Nat.xor (lane A l) (lane B l) := by
  show lane (A ^^^ B) l = lane A l ^^^ lane B l
  apply Nat.eq_of_testBit_eq; intro i
  simp only [lane, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  by_cases h : i < 64 <;> simp [h]

theorem lane_add (n A B : ℕ) (hA : A < 2 ^ (64 * n)) (hB : B < 2 ^ (64 * n))
    (hs : ∀ i < n, lane A i + lane B i < 2 ^ 64) :
    Nat.add A B < 2 ^ (64 * n) ∧ ∀ l < n, lane (Nat.add A B) l = lane A l + lane B l := by
  have h64pos : 0 < 2 ^ 64 := by norm_num
  induction n generalizing A B with
  | zero =>
    have hA0 : A = 0 := by
      simpa [Nat.pow_zero] using hA
    have hB0 : B = 0 := by
      simpa [Nat.pow_zero] using hB
    simp [hA0, hB0]
  | succ n ih =>
    set a0 := A % 2 ^ 64 with ha0
    set A1 := A / 2 ^ 64 with hA1
    set b0 := B % 2 ^ 64 with hb0
    set B1 := B / 2 ^ 64 with hB1

    have hlane0_A : lane A 0 = a0 := by
      simp [lane, ha0]
    have hlane0_B : lane B 0 = b0 := by
      simp [lane, hb0]
    have ha0_add_b0_lt : a0 + b0 < 2 ^ 64 := by
      have h0 := hs 0 (by omega)
      rw [hlane0_A, hlane0_B] at h0
      exact h0

    have hA1_lt : A1 < 2 ^ (64 * n) := by
      rw [hA1]
      apply (Nat.div_lt_iff_lt_mul h64pos).mpr
      calc
        A < 2 ^ (64 * (n + 1)) := hA
        _ = 2 ^ (64 * n + 64) := by rw [Nat.mul_succ]
        _ = 2 ^ (64 * n) * 2 ^ 64 := by rw [Nat.pow_add]
    have hB1_lt : B1 < 2 ^ (64 * n) := by
      rw [hB1]
      apply (Nat.div_lt_iff_lt_mul h64pos).mpr
      calc
        B < 2 ^ (64 * (n + 1)) := hB
        _ = 2 ^ (64 * n + 64) := by rw [Nat.mul_succ]
        _ = 2 ^ (64 * n) * 2 ^ 64 := by rw [Nat.pow_add]

    have hs1 : ∀ i < n, lane A1 i + lane B1 i < 2 ^ 64 := by
      intro i hi
      have hi' : i + 1 < n + 1 := by omega
      have hcarry := hs (i + 1) hi'
      have hlane_A_succ : lane A (i + 1) = lane A1 i := by
        rw [lane, lane, hA1]
        calc
          A / 2 ^ (64 * (i + 1)) % 2 ^ 64
              = A / 2 ^ (64 + 64 * i) % 2 ^ 64 := by rw [show 64 * (i + 1) = 64 + 64 * i by ring]
          _ = A / (2 ^ 64 * 2 ^ (64 * i)) % 2 ^ 64 := by rw [Nat.pow_add]
          _ = (A / 2 ^ 64) / 2 ^ (64 * i) % 2 ^ 64 := by rw [Nat.div_div_eq_div_mul]
      have hlane_B_succ : lane B (i + 1) = lane B1 i := by
        rw [lane, lane, hB1]
        calc
          B / 2 ^ (64 * (i + 1)) % 2 ^ 64
              = B / 2 ^ (64 + 64 * i) % 2 ^ 64 := by rw [show 64 * (i + 1) = 64 + 64 * i by ring]
          _ = B / (2 ^ 64 * 2 ^ (64 * i)) % 2 ^ 64 := by rw [Nat.pow_add]
          _ = (B / 2 ^ 64) / 2 ^ (64 * i) % 2 ^ 64 := by rw [Nat.div_div_eq_div_mul]
      rw [hlane_A_succ, hlane_B_succ] at hcarry
      exact hcarry

    rcases ih A1 B1 hA1_lt hB1_lt hs1 with ⟨hsum1, hlane1⟩

    have hsum : A + B < 2 ^ (64 * (n + 1)) := by
      have hA_eq : A = a0 + 2 ^ 64 * A1 := by
        rw [ha0, hA1, Nat.mod_add_div A (2 ^ 64)]
      have hB_eq : B = b0 + 2 ^ 64 * B1 := by
        rw [hb0, hB1, Nat.mod_add_div B (2 ^ 64)]
      rw [hA_eq, hB_eq]
      have hsum_eq : (a0 + 2 ^ 64 * A1) + (b0 + 2 ^ 64 * B1) = (a0 + b0) + 2 ^ 64 * (A1 + B1) := by ring
      rw [hsum_eq]
      have h1 : (a0 + b0) + 2 ^ 64 * (A1 + B1) < 2 ^ 64 + 2 ^ 64 * (A1 + B1) := by
        apply Nat.add_lt_add_right ha0_add_b0_lt
      have hsum1_succ_le : A1 + B1 + 1 ≤ 2 ^ (64 * n) :=
        Nat.succ_le_of_lt hsum1
      have h2 : 2 ^ 64 + 2 ^ 64 * (A1 + B1) = 2 ^ 64 * (A1 + B1 + 1) := by ring
      have h3 : 2 ^ 64 * (A1 + B1 + 1) ≤ 2 ^ 64 * 2 ^ (64 * n) :=
        Nat.mul_le_mul_left (2 ^ 64) hsum1_succ_le
      have h4 : 2 ^ 64 * 2 ^ (64 * n) = 2 ^ (64 * (n + 1)) := by
        calc
          2 ^ 64 * 2 ^ (64 * n) = 2 ^ (64 + 64 * n) := by rw [Nat.pow_add]
          _ = 2 ^ (64 * n + 64) := by rw [add_comm]
          _ = 2 ^ (64 * (n + 1)) := by rw [Nat.mul_succ]
      have h5 : 2 ^ 64 * (A1 + B1 + 1) ≤ 2 ^ (64 * (n + 1)) := by
        calc
          2 ^ 64 * (A1 + B1 + 1) ≤ 2 ^ 64 * 2 ^ (64 * n) := h3
          _ = 2 ^ (64 * (n + 1)) := h4
      exact (h1.trans_eq h2).trans_le h5

    have h_lane_succ_eq : ∀ (X : ℕ) (l : ℕ), lane X (l + 1) = lane (X / 2 ^ 64) l := by
      intro X l
      rw [lane, lane]
      have h_denom : 2 ^ (64 * (l + 1)) = 2 ^ 64 * 2 ^ (64 * l) := by
        rw [Nat.mul_succ, Nat.pow_add, mul_comm]
      rw [h_denom, Nat.div_div_eq_div_mul]

    have h_div_no_carry : (A + B) / 2 ^ 64 = A / 2 ^ 64 + B / 2 ^ 64 := by
      rw [Nat.add_div (h := h64pos) (a := A) (b := B) (c := 2 ^ 64)]
      have hmod : A % 2 ^ 64 + B % 2 ^ 64 < 2 ^ 64 := by
        have h0 := hs 0 (by omega)
        have h_lane0_A : lane A 0 = A % 2 ^ 64 := by
          simp [lane, show 64 * 0 = 0 by ring]
        have h_lane0_B : lane B 0 = B % 2 ^ 64 := by
          simp [lane, show 64 * 0 = 0 by ring]
        rw [h_lane0_A, h_lane0_B] at h0
        exact h0

      have h_cond : ¬ (2 ^ 64 ≤ A % 2 ^ 64 + B % 2 ^ 64) := by omega
      rw [ite_eq_right h_cond]
      simp
    have hlane : ∀ l < n + 1, lane (A + B) l = lane A l + lane B l := by
      intro l hl
      rcases Nat.eq_zero_or_pos l with (rfl | hpos)
      ·
        have ha0_lt : a0 < 2 ^ 64 := by
          rw [ha0]
          exact Nat.mod_lt _ h64pos
        have hb0_lt : b0 < 2 ^ 64 := by
          rw [hb0]
          exact Nat.mod_lt _ h64pos
        have hA_eq : A = a0 + 2 ^ 64 * A1 := by
          rw [ha0, hA1, Nat.mod_add_div A (2 ^ 64)]
        have hB_eq : B = b0 + 2 ^ 64 * B1 := by
          rw [hb0, hB1, Nat.mod_add_div B (2 ^ 64)]
        rw [hA_eq, hB_eq]

        have h1 : (a0 + 2 ^ 64 * A1) % 2 ^ 64 = a0 := by
          rw [Nat.add_mod, show (2 ^ 64 * A1) % 2 ^ 64 = 0 by simp, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt ha0_lt]
        have h2 : (b0 + 2 ^ 64 * B1) % 2 ^ 64 = b0 := by
          rw [Nat.add_mod, show (2 ^ 64 * B1) % 2 ^ 64 = 0 by simp, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hb0_lt]
        have h3 : ((a0 + 2 ^ 64 * A1) + (b0 + 2 ^ 64 * B1)) % 2 ^ 64 = a0 + b0 := by
          calc
            ((a0 + 2 ^ 64 * A1) + (b0 + 2 ^ 64 * B1)) % 2 ^ 64 = ((a0 + b0) + 2 ^ 64 * (A1 + B1)) % 2 ^ 64 := by ring_nf
            _ = (a0 + b0) % 2 ^ 64 := by
              rw [Nat.add_mod, show (2 ^ 64 * (A1 + B1)) % 2 ^ 64 = 0 by simp, add_zero, Nat.mod_mod]
            _ = a0 + b0 := Nat.mod_eq_of_lt ha0_add_b0_lt

        have hgoal : ((a0 + 2 ^ 64 * A1) + (b0 + 2 ^ 64 * B1)) % 2 ^ 64 = (a0 + 2 ^ 64 * A1) % 2 ^ 64 + (b0 + 2 ^ 64 * B1) % 2 ^ 64 := by
          rw [h1, h2, h3]
        simpa [lane, show 64 * 0 = 0 by ring, show (2 : ℕ) ^ 0 = 1 by simp] using hgoal
      ·
        rcases Nat.exists_eq_succ_of_ne_zero hpos.ne' with ⟨m, rfl⟩
        have hm : m < n := by omega
        rw [h_lane_succ_eq (A + B) m, h_div_no_carry]

        rw [h_lane_succ_eq A m, h_lane_succ_eq B m]

        simpa [hA1, hB1] using hlane1 m hm
    exact And.intro hsum hlane

theorem lane_sub (n A B : ℕ) (hA : A < 2 ^ (64 * n)) (hB : B < 2 ^ (64 * n))
    (hs : ∀ i < n, lane B i ≤ lane A i) :
    Nat.sub A B < 2 ^ (64 * n) ∧ ∀ l < n, lane (Nat.sub A B) l = lane A l - lane B l := by
  have e : Nat.sub A B = D3Dec.pack 64 n (fun l => lane A l - lane B l) := by
    show A - B = _
    conv_lhs => rw [← pack_lane n A hA, ← pack_lane n B hB]
    exact D3Dec.pack_sub 64 n (lane B) (lane A) hs
  have hf : ∀ l < n, lane A l - lane B l < 2 ^ 64 := fun l _ => lt_of_le_of_lt (Nat.sub_le _ _) (lane_lt A l)
  rw [e]; exact ⟨D3Dec.pack_lt 64 n _ hf, fun l hl => lane_pack n _ hf l hl⟩

theorem lane_mul (n A c : ℕ) (hA : A < 2 ^ (64 * n)) (hs : ∀ i < n, lane A i * c < 2 ^ 64) :
    Nat.mul A c < 2 ^ (64 * n) ∧ ∀ l < n, lane (Nat.mul A c) l = lane A l * c := by
  induction n generalizing A c with
  | zero =>
    have hA0 : A = 0 := by
      have h : A < 1 := by simpa using hA
      exact Nat.lt_one_iff.mp h
    subst hA0
    simp
  | succ n ih =>
    have hA' : A < 2 ^ (64 * n) * 2 ^ 64 := by
      have : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by ring
      rw [this] at hA
      exact hA
    have ha0_lt : A % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
    have hA1_lt : A / 2 ^ 64 < 2 ^ (64 * n) := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 64)).mpr
      exact hA'
    set a0 := A % 2 ^ 64 with ha0
    set A1 := A / 2 ^ 64 with hA1
    have hA_eq : A = a0 + 2 ^ 64 * A1 := by
      rw [ha0, hA1]
      calc
        A = 2 ^ 64 * (A / 2 ^ 64) + A % 2 ^ 64 := (Nat.div_add_mod A (2 ^ 64)).symm
        _ = A % 2 ^ 64 + 2 ^ 64 * (A / 2 ^ 64) := by rw [add_comm]
    have h_a0c_lt : a0 * c < 2 ^ 64 := by
      have h_bound0 := hs 0 (by omega)
      have h_lane0 : lane A 0 = a0 := by
        dsimp [lane, a0]
        simp
      rw [h_lane0] at h_bound0
      exact h_bound0
    have h_lane_A1 : ∀ i < n, lane A1 i * c < 2 ^ 64 := by
      intro i hi
      have h_lane_succ : lane A (i + 1) = lane A1 i := by
        dsimp [lane, A1]
        calc
          A / 2 ^ (64 * (i + 1)) % 2 ^ 64 = A / (2 ^ 64 * 2 ^ (64 * i)) % 2 ^ 64 := by ring
          _ = (A / 2 ^ 64) / 2 ^ (64 * i) % 2 ^ 64 := by rw [Nat.div_div_eq_div_mul]
          _ = A1 / 2 ^ (64 * i) % 2 ^ 64 := rfl
      have h_bound := hs (i + 1) (by omega)
      rw [h_lane_succ] at h_bound
      exact h_bound
    have h_A1c_lt : A1 * c < 2 ^ (64 * n) :=
      (ih A1 c hA1_lt h_lane_A1).1
    have h_bound : A * c < 2 ^ (64 * (n + 1)) := by
      rw [hA_eq]
      rw [Nat.add_mul, mul_assoc]
      have hsum : a0 * c + 2 ^ 64 * (A1 * c) < 2 ^ 64 + 2 ^ 64 * (2 ^ (64 * n) - 1) := by
        apply Nat.add_lt_add_of_lt_of_le h_a0c_lt
        have : A1 * c ≤ 2 ^ (64 * n) - 1 := by omega
        nlinarith
      have hgoal : 2 ^ 64 + 2 ^ 64 * (2 ^ (64 * n) - 1) = 2 ^ (64 * (n + 1)) := by
        have hpos : 1 ≤ 2 ^ (64 * n) := Nat.one_le_two_pow
        calc
          2 ^ 64 + 2 ^ 64 * (2 ^ (64 * n) - 1) = 2 ^ 64 * 1 + 2 ^ 64 * (2 ^ (64 * n) - 1) := by ring
          _ = 2 ^ 64 * (1 + (2 ^ (64 * n) - 1)) := by ring
          _ = 2 ^ 64 * 2 ^ (64 * n) := by rw [Nat.add_comm, Nat.sub_add_cancel hpos]
          _ = 2 ^ (64 * (n + 1)) := by ring
      rw [hgoal] at hsum
      exact hsum
    have h_lanes : ∀ l < n + 1, lane (A * c) l = lane A l * c := by
      intro l hl
      rcases em (l = 0) with (rfl | hl_pos)
      ·
        dsimp [lane, a0]
        simp
        rw [hA_eq]
        rw [Nat.add_mul, mul_assoc]

        have hleft : (a0 * c + 2 ^ 64 * (A1 * c)) % 2 ^ 64 = a0 * c := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_a0c_lt]
        have hright : (a0 + 2 ^ 64 * A1) % 2 ^ 64 * c = a0 * c := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha0_lt]
        have hgoal : (a0 * c + 2 ^ 64 * (A1 * c)) % 2 ^ 64 = (a0 + 2 ^ 64 * A1) % 2 ^ 64 * c := by
          rw [hleft, hright]
        simpa [show (2:ℕ)^64 = 18446744073709551616 by norm_num] using hgoal
      ·
        have h_l_sub_one_lt_n : l - 1 < n := by omega
        have h_lane_A1c : ∀ i < n, lane (A1 * c) i = lane A1 i * c := (ih A1 c hA1_lt h_lane_A1).2
        have h_lane_eq : lane (A * c) l = lane (A1 * c) (l - 1) := by
          dsimp [lane]
          rw [hA_eq]
          rw [Nat.add_mul, mul_assoc]

          set d := 2 ^ (64 * l) with hd
          set d' := 2 ^ (64 * (l - 1)) with hd'
          have hd_pos : 0 < d := by
            dsimp [d]
            positivity
          have h_relation : d = 2 ^ 64 * d' := by
            rw [hd, hd']
            rw [show 64 * l = 64 + 64 * (l - 1) by omega, pow_add]
          set X := A1 * c with hX
          set q := X / d' with hq
          set r := X % d' with hr
          have hX_eq : X = q * d' + r := by
            rw [hq, hr, mul_comm]
            exact (Nat.div_add_mod X d').symm
          have hr_lt : r < d' := Nat.mod_lt _ (by positivity : 0 < d')
          have h_rem_lt : a0 * c + r * 2 ^ 64 < d := by
            have ha0_max : a0 * c ≤ 2 ^ 64 - 1 := by omega
            have hr_max : r ≤ d' - 1 := by omega
            have hcalc : (2 ^ 64 - 1) + (d' - 1) * 2 ^ 64 = d - 1 := by
              rw [hd, hd']
              rw [show 64 * l = 64 + 64 * (l - 1) by omega, pow_add]
              have hpos64 : 1 ≤ 2 ^ 64 := by norm_num
              have hposd' : 1 ≤ 2 ^ (64 * (l - 1)) := Nat.one_le_two_pow
              omega
            have hle : a0 * c + r * 2 ^ 64 ≤ (2 ^ 64 - 1) + (d' - 1) * 2 ^ 64 := by
              nlinarith
            have : (2 ^ 64 - 1) + (d' - 1) * 2 ^ 64 = d - 1 := hcalc
            rw [this] at hle
            omega
          have h_eq : a0 * c + 2 ^ 64 * X = q * d + (a0 * c + r * 2 ^ 64) := by
            rw [hX_eq, h_relation]
            ring
          rw [h_eq]
          have h_div : (q * d + (a0 * c + r * 2 ^ 64)) / d = q :=
            Nat.div_eq_of_lt_le (by omega) (by
              have : (q + 1) * d = q * d + d := by ring
              rw [this]
              exact Nat.add_lt_add_left h_rem_lt (q * d))
          rw [h_div]
        rw [h_lane_eq]
        rw [h_lane_A1c (l - 1) h_l_sub_one_lt_n]
        have h_lane_A_succ : lane A l = lane A1 (l - 1) := by
          dsimp [lane, A1]
          calc
            A / 2 ^ (64 * l) % 2 ^ 64 = A / (2 ^ 64 * 2 ^ (64 * (l - 1))) % 2 ^ 64 := by
              rw [show 64 * l = 64 + 64 * (l - 1) by omega, pow_add]
            _ = (A / 2 ^ 64) / 2 ^ (64 * (l - 1)) % 2 ^ 64 := by rw [Nat.div_div_eq_div_mul]
            _ = A1 / 2 ^ (64 * (l - 1)) % 2 ^ 64 := rfl
        rw [h_lane_A_succ]
    exact And.intro h_bound h_lanes

theorem lane_shl (n A s : ℕ) (hA : A < 2 ^ (64 * n)) (hs : ∀ i < n, lane A i < 2 ^ (64 - s)) :
    Nat.shiftLeft A s < 2 ^ (64 * n) ∧ ∀ l < n, lane (Nat.shiftLeft A s) l = lane A l * 2 ^ s := by
  have hf : ∀ l < n, lane A l * 2 ^ s < 2 ^ 64 := fun l hl => by
    rcases Nat.lt_or_ge 64 s with h | h
    · have h0 : lane A l = 0 := by have := hs l hl; rw [show 64 - s = 0 by omega] at this; omega
      rw [h0, zero_mul]; positivity
    · calc lane A l * 2 ^ s < 2 ^ (64 - s) * 2 ^ s := Nat.mul_lt_mul_of_pos_right (hs l hl) (by positivity)
        _ = 2 ^ 64 := by rw [← pow_add, Nat.sub_add_cancel h]
  have e : Nat.shiftLeft A s = D3Dec.pack 64 n (fun l => lane A l * 2 ^ s) := by
    rw [show Nat.shiftLeft A s = A * 2 ^ s from Nat.shiftLeft_eq A s]
    conv_lhs => rw [← pack_lane n A hA]
    rw [mul_comm, D3Dec.pack_const_mul]
    exact D3Dec.pack_congr _ _ _ _ fun l _ => mul_comm _ _
  rw [e]; exact ⟨D3Dec.pack_lt 64 n _ hf, fun l hl => lane_pack n _ hf l hl⟩

theorem lane_shr (n A s : ℕ) (hs : s ≤ 64) :
    Nat.land (Nat.shiftRight A s) (Nat.mul (D3Ck2.oN n) (2 ^ (64 - s) - 1)) < 2 ^ (64 * n) ∧
      ∀ l < n, lane (Nat.land (Nat.shiftRight A s) (Nat.mul (D3Ck2.oN n) (2 ^ (64 - s) - 1))) l = lane A l / 2 ^ s := by
  have hm : ∀ l < n, 2 ^ (64 - s) - 1 < 2 ^ 64 := fun _ _ => by
    have : 2 ^ (64 - s) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hM : Nat.mul (D3Ck2.oN n) (2 ^ (64 - s) - 1) = D3Dec.pack 64 n (fun _ => 2 ^ (64 - s) - 1) := by
    show D3Ck2.oN n * (2 ^ (64 - s) - 1) = _
    rw [oN_pack, mul_comm, D3Dec.pack_const_mul]
    exact D3Dec.pack_congr _ _ _ _ fun l _ => mul_one _
  have hf : ∀ l < n, lane A l / 2 ^ s < 2 ^ 64 := fun l _ => lt_of_le_of_lt (Nat.div_le_self _ _) (lane_lt A l)
  have e : Nat.land (Nat.shiftRight A s) (Nat.mul (D3Ck2.oN n) (2 ^ (64 - s) - 1)) =
      D3Dec.pack 64 n (fun l => lane A l / 2 ^ s) := by
    rw [hM]
    apply Nat.eq_of_testBit_eq; intro i
    show (A >>> s &&& _).testBit i = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, D3Dec.testBit_pack 64 n _ (by norm_num) hm,
      D3Dec.testBit_pack 64 n _ (by norm_num) hf]
    split_ifs with h
    · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow, lane, Nat.testBit_mod_two_pow,
        Nat.testBit_div_two_pow]
      by_cases hj : i % 64 + s < 64
      · have h1 : i % 64 < 64 - s := by omega
        simp only [hj, h1, decide_true, Bool.true_and, Bool.and_true]
        congr 1; have := Nat.mod_add_div i 64; omega
      · have h1 : ¬ i % 64 < 64 - s := by omega
        simp [hj, h1]
    · simp
  rw [e]; exact ⟨D3Dec.pack_lt 64 n _ hf, fun l hl => lane_pack n _ hf l hl⟩

theorem lane_mulc (n c : ℕ) (hc : c < 2 ^ 64) :
    Nat.mul (D3Ck2.oN n) c < 2 ^ (64 * n) ∧ ∀ l < n, lane (Nat.mul (D3Ck2.oN n) c) l = c := by
  have h_pos : 0 < 2 ^ 64 - 1 := by
    norm_num

  have h_geom : ∀ n : ℕ, D3Ck2.oN n * (2 ^ 64 - 1) = 2 ^ (64 * n) - 1 := by
    intro n
    induction n with
    | zero =>
        unfold D3Ck2.oN
        simp [Nat.shiftLeft_eq]
        exact Nat.zero_div _
    | succ n ih =>

        have h_oN_succ_formula : D3Ck2.oN (n + 1) = (2 ^ (64 * (n + 1)) - 1) / (2 ^ 64 - 1) := by
          unfold D3Ck2.oN
          have h_shift : Nat.shiftLeft 1 (Nat.shiftLeft (n+1) 6) = 2 ^ (64 * (n+1)) := by
            simp [Nat.shiftLeft_eq, mul_comm]
          rw [h_shift]
          rfl
        rw [h_oN_succ_formula]

        have h_id : 2 ^ (64 * (n + 1)) - 1 = (2 ^ 64 - 1) * 2 ^ (64 * n) + (2 ^ (64 * n) - 1) := by
          have h_pow : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
            rw [show 64 * (n + 1) = 64 * n + 64 by ring, pow_add, mul_comm]
          omega
        have h_dvd : 2 ^ 64 - 1 ∣ 2 ^ (64 * (n + 1)) - 1 := by
          rw [h_id]
          apply Nat.dvd_add
          · exact ⟨2^(64*n), by ring⟩
          · rw [← ih]
            exact ⟨D3Ck2.oN n, mul_comm _ _⟩
        rw [Nat.div_mul_cancel h_dvd]

  have h_oN_succ : ∀ n : ℕ, D3Ck2.oN (n + 1) = 1 + 2 ^ 64 * D3Ck2.oN n := by
    intro n
    have h_eq_mul : (2 ^ 64 - 1) * D3Ck2.oN (n + 1) = (2 ^ 64 - 1) * (1 + 2 ^ 64 * D3Ck2.oN n) := by
      calc
        (2 ^ 64 - 1) * D3Ck2.oN (n + 1) = D3Ck2.oN (n + 1) * (2 ^ 64 - 1) := mul_comm _ _
        _ = 2 ^ (64 * (n + 1)) - 1 := h_geom (n + 1)
        _ = (2 ^ 64 - 1) * 2 ^ (64 * n) + (2 ^ (64 * n) - 1) := by
          have h_pow : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
            rw [show 64 * (n + 1) = 64 * n + 64 by ring, pow_add, mul_comm]
          omega
        _ = (2 ^ 64 - 1) * 2 ^ (64 * n) + D3Ck2.oN n * (2 ^ 64 - 1) := by rw [h_geom n]
        _ = (2 ^ 64 - 1) * 2 ^ (64 * n) + (2 ^ 64 - 1) * D3Ck2.oN n := by rw [mul_comm (D3Ck2.oN n)]
        _ = (2 ^ 64 - 1) * (2 ^ (64 * n) + D3Ck2.oN n) := by ring
        _ = (2 ^ 64 - 1) * (1 + 2 ^ 64 * D3Ck2.oN n) := by
          have h_eq : 2 ^ (64 * n) = D3Ck2.oN n * (2 ^ 64 - 1) + 1 := by
            have h := h_geom n
            have hpos : 1 ≤ 2 ^ (64 * n) := by
              apply Nat.one_le_two_pow
            calc
              2 ^ (64 * n) = ((2 ^ (64 * n) - 1) + 1) := by rw [Nat.sub_add_cancel hpos]
              _ = D3Ck2.oN n * (2 ^ 64 - 1) + 1 := by rw [← h]
          rw [h_eq]
          ring
    exact Nat.eq_of_mul_eq_mul_left h_pos h_eq_mul

  induction n with
  | zero =>
      have h_oN0 : D3Ck2.oN 0 = 0 := by
        unfold D3Ck2.oN
        simp [Nat.shiftLeft_eq]
        exact Nat.zero_div _
      constructor
      · rw [h_oN0]
        simp
      · intro l hl
        exfalso; exact Nat.not_lt_zero _ hl
  | succ n ih =>
      rcases ih with ⟨h_bound, h_lane⟩
      rw [h_oN_succ n]

      have h_mul_eq : (1 + 2 ^ 64 * D3Ck2.oN n) * c = c + 2 ^ 64 * (D3Ck2.oN n * c) := by
        rw [Nat.add_mul, Nat.one_mul]
        ring

      have h_goal_left : (Nat.mul (1 + 2 ^ 64 * D3Ck2.oN n) c) = c + 2 ^ 64 * (D3Ck2.oN n * c) :=
        h_mul_eq
      rw [h_goal_left]
      have hA : D3Ck2.oN n * c < 2 ^ (64 * n) := by
        simpa [Nat.mul_comm] using h_bound
      constructor
      ·
        have h_pow : 2 ^ (64 * n) * 2 ^ 64 = 2 ^ (64 * (n + 1)) := by
          rw [show 64 * (n + 1) = 64 * n + 64 by ring, pow_add, mul_comm]
        omega
      ·
        intro l hl
        rcases Nat.eq_zero_or_pos l with (rfl | hpos)
        ·
          rw [lane]
          simpa [hc] using Nat.mod_eq_of_lt hc
        ·
          obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
          have hl'_lt_n : l' < n := by omega

          have h_lane_succ : lane (c + 2 ^ 64 * (D3Ck2.oN n * c)) (l' + 1) =
                             lane ((c + 2 ^ 64 * (D3Ck2.oN n * c)) / 2 ^ 64) l' := by
            simp [lane, show 2 ^ (64 * (l' + 1)) = 2 ^ 64 * 2 ^ (64 * l') by
              rw [show 64 * (l' + 1) = 64 * l' + 64 by ring, pow_add, mul_comm],
              Nat.div_div_eq_div_mul]
          rw [h_lane_succ]

          have h_div : (c + 2 ^ 64 * (D3Ck2.oN n * c)) / 2 ^ 64 = D3Ck2.oN n * c := by
            apply Nat.div_eq_of_lt_le
            · omega
            · have h_upper : c + 2 ^ 64 * (D3Ck2.oN n * c) < (D3Ck2.oN n * c + 1) * 2 ^ 64 := by
                nlinarith
              exact h_upper
          rw [h_div]
          have h_lane' : lane (D3Ck2.oN n * c) l' = c := by
            simpa [Nat.mul_comm] using h_lane l' hl'_lt_n
          simpa [lane] using h_lane'

theorem lane_plt (n x y : ℕ) (hx : Fits n (2 ^ 63) x) (hy : Fits n (2 ^ 63) y) :
    Fits n 2 (Lanes24.plt (D3Ck2.oN n) x y) ∧
      ∀ l < n, lane (Lanes24.plt (D3Ck2.oN n) x y) l = if lane x l < lane y l then 1 else 0 := by
  have e : Lanes24.plt (D3Ck2.oN n) x y = D3Dec.pack 64 n (fun l => if lane x l < lane y l then 1 else 0) := by
    rw [plt_eq, oN_pack]
    conv_lhs => rw [← pack_lane n x hx.1, ← pack_lane n y hy.1]
    exact D3Q2A0.plt_pack n (lane x) (lane y) hx.2 hy.2
  have hb : ∀ l < n, (if lane x l < lane y l then 1 else 0) < 2 := fun l _ => by split_ifs <;> norm_num
  rw [e]
  exact ⟨fits_pack n 2 _ (by norm_num) hb, fun l hl => lane_pack n _ (fun i hi => by
    have := hb i hi; omega) l hl⟩

theorem lane_pmask (n b : ℕ) (hb : Fits n 2 b) :
    Fits n (2 ^ 63) (Lanes24.pmask b) ∧ ∀ l < n, lane (Lanes24.pmask b) l = lane b l * (2 ^ 63 - 1) := by
  have e : Lanes24.pmask b = D3Dec.pack 64 n (fun l => lane b l * (2 ^ 63 - 1)) := by
    show D3Q2A0.pmask b = _
    conv_lhs => rw [← pack_lane n b hb.1]
    exact D3Q2A0.pmask_pack n (lane b)
  have h : ∀ l < n, lane b l * (2 ^ 63 - 1) < 2 ^ 63 := fun l hl => by
    have := hb.2 l hl; interval_cases (lane b l) <;> norm_num
  rw [e]
  exact ⟨fits_pack n (2 ^ 63) _ (by norm_num) h, fun l hl => lane_pack n _ (fun i hi => by
    have := h i hi; omega) l hl⟩

theorem lane_psel (M A B l : ℕ) :
    lane (Lanes24.psel M A B) l = Lanes24.psel (lane M l) (lane A l) (lane B l) := by
  rw [Lanes24.psel, lane_xor, lane_land, lane_xor, Lanes24.psel]

theorem lane_psub (n x y : ℕ) (hx : Fits n (2 ^ 63) x) (hy : Fits n (2 ^ 63) y) :
    Fits n (2 ^ 63) (Lanes24.psub (D3Ck2.oN n) x y) ∧
      ∀ l < n, lane (Lanes24.psub (D3Ck2.oN n) x y) l = lane x l - lane y l := by
  have e : Lanes24.psub (D3Ck2.oN n) x y = D3Dec.pack 64 n (fun l => lane x l - lane y l) := by
    rw [psub_eq, oN_pack]
    conv_lhs => rw [← pack_lane n x hx.1, ← pack_lane n y hy.1]
    exact D3Q2A0.psub_pack n (lane x) (lane y) hx.2 hy.2
  have hb : ∀ l < n, lane x l - lane y l < 2 ^ 63 := fun l hl => by have := hx.2 l hl; omega
  rw [e]
  exact ⟨fits_pack n (2 ^ 63) _ (by norm_num) hb, fun l hl => lane_pack n _ (fun i hi => by
    have := hb i hi; omega) l hl⟩

theorem lane_pshr1 (n x : ℕ) (hx : x < 2 ^ (64 * n)) :
    Fits n (2 ^ 63) (Lanes24.pshr1 (D3Ck2.oN n) x) ∧
      ∀ l < n, lane (Lanes24.pshr1 (D3Ck2.oN n) x) l = lane x l / 2 := by
  have e : Lanes24.pshr1 (D3Ck2.oN n) x = D3Dec.pack 64 n (fun l => lane x l >>> 1) := by
    have := D3Q2A0.pshr_pack n 1 (lane x) (by norm_num) (fun l _ => lane_lt x l)
    rw [pack_lane n x hx, ← oN_pack] at this
    rw [← this]; rfl
  have h : ∀ l < n, lane x l >>> 1 < 2 ^ 63 := fun l _ => by
    have := lane_lt x l; rw [Nat.shiftRight_eq_div_pow]; omega
  rw [e]
  refine ⟨fits_pack n (2 ^ 63) _ (by norm_num) h, fun l hl => ?_⟩
  rw [lane_pack n _ (fun i hi => by have := h i hi; omega) l hl, Nat.shiftRight_eq_div_pow, pow_one]

theorem lane_rsh (n P sh : ℕ) (hsh : 1 ≤ sh ∧ sh ≤ 63) (hP : Fits n (2 ^ 63) P) :
    D3Ck2.rsh (D3Ck2.oN n) P sh < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.rsh (D3Ck2.oN n) P sh) l = rshN (lane P l) sh := by
  have hf : ∀ l < n, lane P l + 2 ^ (sh - 1) < 2 ^ 64 := fun l hl => by
    have := hP.2 l hl
    have : 2 ^ (sh - 1) ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have eQ : Nat.add P (Nat.mul (D3Ck2.oN n) (Nat.shiftLeft 1 (Nat.sub sh 1))) =
      D3Dec.pack 64 n (fun l => lane P l + 2 ^ (sh - 1)) := by
    show P + D3Ck2.oN n * (1 <<< (sh - 1)) = _
    rw [Nat.shiftLeft_eq, one_mul, oN_pack, mul_comm, D3Dec.pack_const_mul]
    conv_lhs => rw [← pack_lane n P hP.1]
    rw [D3Dec.pack_add]; exact D3Dec.pack_congr _ _ _ _ fun l _ => by ring
  have e : D3Ck2.rsh (D3Ck2.oN n) P sh = D3Dec.pack 64 n (fun l => rshN (lane P l) sh) := by
    unfold D3Ck2.rsh
    rw [eQ]
    have h2 : Nat.sub (Nat.shiftLeft 1 (Nat.sub 64 sh)) 1 = 2 ^ (64 - sh) - 1 := by
      show 1 <<< (64 - sh) - 1 = _; rw [Nat.shiftLeft_eq, one_mul]
    rw [h2, oN_pack, D3Q2A0.pshr_pack n sh _ (by omega) hf]
    exact D3Dec.pack_congr _ _ _ _ fun l _ => by rw [Nat.shiftRight_eq_div_pow]; rfl
  have hb : ∀ l < n, rshN (lane P l) sh < 2 ^ 64 := fun l hl => by
    unfold rshN; exact lt_of_le_of_lt (Nat.div_le_self _ _) (hf l hl)
  rw [e]; exact ⟨D3Dec.pack_lt 64 n _ hb, fun l hl => lane_pack n _ hb l hl⟩

theorem lane_kc (n A c : ℕ) (hA : A < 2 ^ (64 * n)) (hs : ∀ i < n, lane A i * c < 2 ^ 64) :
    D3Ck2.kc (D3Ck2.oN n) A c < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.kc (D3Ck2.oN n) A c) l = kcN (lane A l) c := by
  have hmul := lane_mul n A c hA hs
  rcases hmul with ⟨hmul_lt, hmul_lane⟩
  have hs28 : 28 ≤ 64 := by omega
  have hshr := lane_shr n (Nat.mul A c) 28 hs28
  rcases hshr with ⟨hshr_lt, hshr_lane⟩
  have h_mask : (68719476735 : ℕ) = 2 ^ (64 - 28) - 1 := by norm_num
  have h_shr_eq : D3Ck2.kc (D3Ck2.oN n) A c =
      Nat.land (Nat.shiftRight (Nat.mul A c) 28) (Nat.mul (D3Ck2.oN n) (2 ^ (64 - 28) - 1)) := by
    unfold D3Ck2.kc
    rw [h_mask]
  have h_bound : D3Ck2.kc (D3Ck2.oN n) A c < 2 ^ (64 * n) := by
    rw [h_shr_eq]
    exact hshr_lt
  have h_lane : ∀ l < n, lane (D3Ck2.kc (D3Ck2.oN n) A c) l = kcN (lane A l) c := by
    intro l hl
    rw [h_shr_eq]
    rw [hshr_lane l hl]
    rw [hmul_lane l hl]
    unfold kcN
    rfl
  exact And.intro h_bound h_lane

theorem lane_mulF (K n A B : ℕ) (hK : K ≤ 64) (hA : Fits n (2 ^ (64 - K)) A) (hB : Fits n (2 ^ K) B) :
    Lanes24.mulF K (D3Ck2.oN n) A B < 2 ^ (64 * n) ∧
      ∀ l < n, lane (Lanes24.mulF K (D3Ck2.oN n) A B) l = lane A l * lane B l := by
  have hm : ∀ l < n, lane A l * lane B l < 2 ^ 64 := fun l hl => by
    calc lane A l * lane B l < 2 ^ (64 - K) * 2 ^ K := Nat.mul_lt_mul'' (hA.2 l hl) (hB.2 l hl)
      _ = 2 ^ 64 := by rw [← pow_add, Nat.sub_add_cancel hK]
  have e : Lanes24.mulF K (D3Ck2.oN n) A B = D3Dec.pack 64 n (fun l => lane A l * lane B l) := by
    rw [mulF_eq, oN_pack, ← pack_lane n A hA.1, ← pack_lane n B hB.1]
    rw [D3Q2A0.mulF_pack K n (lane A) (lane B) hK hA.2 hB.2]
    exact D3Dec.pack_congr _ _ _ _ fun l hl => by
      rw [lane_pack n _ (fun i _ => lane_lt A i) l hl, lane_pack n _ (fun i _ => lane_lt B i) l hl]
  rw [e]; exact (fits_pack n (2 ^ 64) _ le_rfl hm).1 |> fun h => ⟨h, fun l hl => lane_pack n _ hm l hl⟩

theorem frc2_one (a : ℕ) (g : ℕ → ℕ) : Lanes24.frc2 a 1 (fun P _ => g P) = g a := by
  cases a <;> rfl

theorem mulU6_eq (O A B : ℕ) : D3Ck2.mulU6 O A B = Lanes24.mulF 6 O A B := by
  unfold D3Ck2.mulU6 Lanes24.mulF
  rw [show (6 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  simp only [Nat.rec_zero, Lanes24.mulBitF, frc2_one, Nat.add_eq, Nat.zero_add]
  rfl

theorem mulU13_eq (O A B : ℕ) : D3Ck2.mulU13 O A B = Lanes24.mulF 13 O A B := by
  unfold D3Ck2.mulU13 Lanes24.mulF
  rw [show (13 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  simp only [Nat.rec_zero, Lanes24.mulBitF, frc2_one, Nat.add_eq, Nat.zero_add]
  rfl

theorem mulU20_eq (O A B : ℕ) : D3Ck2.mulU20 O A B = Lanes24.mulF 20 O A B := by
  unfold D3Ck2.mulU20 Lanes24.mulF
  rw [show (20 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  simp only [Nat.rec_zero, Lanes24.mulBitF, frc2_one, Nat.add_eq, Nat.zero_add]
  rfl

theorem mulU26_eq (O A B : ℕ) : D3Ck2.mulU26 O A B = Lanes24.mulF 26 O A B := by
  unfold D3Ck2.mulU26 Lanes24.mulF
  rw [show (26 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  simp only [Nat.rec_zero, Lanes24.mulBitF, frc2_one, Nat.add_eq, Nat.zero_add]
  rfl

theorem mulU28_eq (O A B : ℕ) : D3Ck2.mulU28 O A B = Lanes24.mulF 28 O A B := by
  unfold D3Ck2.mulU28 Lanes24.mulF
  rw [show (28 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  simp only [Nat.rec_zero, Lanes24.mulBitF, frc2_one, Nat.add_eq, Nat.zero_add]
  rfl

theorem lane_shr_mod (F s w l : ℕ) (hw : s + w ≤ 64) :
    lane (Nat.shiftRight F s) l % 2 ^ w = lane F l / 2 ^ s % 2 ^ w := by
  unfold lane
  have e : Nat.shiftRight F s = F / 2 ^ s := Nat.shiftRight_eq_div_pow F s
  rw [e, Nat.div_div_eq_div_mul, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : w ≤ 64))]
  have h64 : (2 : ℕ) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← pow_add]; congr 1; omega
  rw [h64, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : w ≤ 64 - s)), Nat.mul_comm (2 ^ s) (2 ^ (64 * l))]

theorem lane_ix (n F s : ℕ) (hs : s = 0 ∨ s = 32) :
    Fits n (2 ^ 63) (D3Ck2.ix (D3Ck2.oN n) F s) ∧
      ∀ l < n, lane (D3Ck2.ix (D3Ck2.oN n) F s) l = lane F l / 2 ^ s % 2 ^ 32 * 16 + 2 ^ 62 := by
  have hs' : s + 32 ≤ 64 := by omega
  have hM := lane_mulc n 4294967295 (by norm_num)
  have hL0 : Nat.land (Nat.shiftRight F s) (Nat.mul (D3Ck2.oN n) 4294967295) < 2 ^ (64 * n) :=
    lt_of_le_of_lt Nat.and_le_right hM.1
  have hLl : ∀ l < n, lane (Nat.land (Nat.shiftRight F s) (Nat.mul (D3Ck2.oN n) 4294967295)) l =
      lane F l / 2 ^ s % 2 ^ 32 := by
    intro l hl
    rw [lane_land, hM.2 l hl, show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num]
    rw [show Nat.land (lane (Nat.shiftRight F s) l) (2 ^ 32 - 1) = lane (Nat.shiftRight F s) l % 2 ^ 32 from
      Nat.and_two_pow_sub_one_eq_mod _ _]
    exact lane_shr_mod F s 32 l hs'
  have hb : ∀ l, lane F l / 2 ^ s % 2 ^ 32 < 2 ^ 32 := fun l => Nat.mod_lt _ (by positivity)
  obtain ⟨hS0, hSl⟩ := lane_shl n _ 4 hL0 (fun i hi => by
    rw [hLl i hi]; exact lt_of_lt_of_le (hb i) (by norm_num))
  obtain ⟨hC0, hCl⟩ := lane_mulc n 4611686018427387904 (by norm_num)
  obtain ⟨hA0, hAl⟩ := lane_add n _ _ hS0 hC0 (fun i hi => by
    rw [hSl i hi, hLl i hi, hCl i hi]; have := hb i; omega)
  unfold D3Ck2.ix
  refine ⟨⟨hA0, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hAl l hl, hSl l hl, hLl l hl, hCl l hl]; have := hb l; omega
  · rw [hAl l hl, hSl l hl, hLl l hl, hCl l hl]; norm_num

theorem lane_hxa (n H s : ℕ) (hs : s = 0 ∨ s = 32) :
    Fits n (2 ^ 63) (D3Ck2.hxa (D3Ck2.oN n) H s) ∧
      ∀ l < n, lane (D3Ck2.hxa (D3Ck2.oN n) H s) l = lane H l / 2 ^ s % 2 ^ 30 + 2 ^ 62 := by
  have hs' : s + 30 ≤ 64 := by omega
  have hM := lane_mulc n 1073741823 (by norm_num)
  have hL0 : Nat.land (Nat.shiftRight H s) (Nat.mul (D3Ck2.oN n) 1073741823) < 2 ^ (64 * n) :=
    lt_of_le_of_lt Nat.and_le_right hM.1
  have hLl : ∀ l < n, lane (Nat.land (Nat.shiftRight H s) (Nat.mul (D3Ck2.oN n) 1073741823)) l =
      lane H l / 2 ^ s % 2 ^ 30 := by
    intro l hl
    rw [lane_land, hM.2 l hl, show (1073741823 : ℕ) = 2 ^ 30 - 1 by norm_num]
    rw [show Nat.land (lane (Nat.shiftRight H s) l) (2 ^ 30 - 1) = lane (Nat.shiftRight H s) l % 2 ^ 30 from
      Nat.and_two_pow_sub_one_eq_mod _ _]
    exact lane_shr_mod H s 30 l hs'
  have hb : ∀ l, lane H l / 2 ^ s % 2 ^ 30 < 2 ^ 30 := fun l => Nat.mod_lt _ (by positivity)
  obtain ⟨hC0, hCl⟩ := lane_mulc n 4611686018427387904 (by norm_num)
  obtain ⟨hA0, hAl⟩ := lane_add n _ _ hL0 hC0 (fun i hi => by
    rw [hLl i hi, hCl i hi]; have := hb i; omega)
  unfold D3Ck2.hxa
  refine ⟨⟨hA0, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hAl l hl, hLl l hl, hCl l hl]; have := hb l; omega
  · rw [hAl l hl, hLl l hl, hCl l hl]; norm_num

theorem land_pow63_shr (v : ℕ) (hv : v < 2 ^ 64) : (v &&& 2 ^ 63) >>> 63 = v / 2 ^ 63 := by
  rw [Nat.land_comm, Nat.two_pow_and, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  have h : v / 2 ^ 63 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc v < 2 ^ 64 := hv
      _ = 2 * 2 ^ 63 := by norm_num
  rcases (by omega : v / 2 ^ 63 = 0 ∨ v / 2 ^ 63 = 1) with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

theorem plt_one (x y : ℕ) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    Lanes24.plt 1 x y = if x < y then 1 else 0 := by
  unfold Lanes24.plt Lanes24.mH
  have e : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  simp only [Nat.mul_eq, one_mul, Nat.add_eq, Nat.sub_eq, Nat.land_eq, Nat.shiftRight_eq, e]
  rw [land_pow63_shr _ (by omega)]
  split_ifs with h
  · rw [Nat.div_eq_iff (by positivity)]; constructor <;> omega
  · rw [Nat.div_eq_iff (by positivity)]; constructor <;> omega

theorem psel_full (A B : ℕ) (hA : A < 2 ^ 63) (hB : B < 2 ^ 63) :
    Lanes24.psel (2 ^ 63 - 1) A B = A := by
  unfold Lanes24.psel
  simp only [Nat.xor_eq, Nat.land_eq]
  rw [Nat.and_two_pow_sub_one_of_lt_two_pow (Nat.xor_lt_two_pow hA hB), ← Nat.xor_assoc, Nat.xor_comm B A,
    Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem psel_zero (A B : ℕ) : Lanes24.psel 0 A B = B := by
  unfold Lanes24.psel
  simp

theorem psub_one (x y : ℕ) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) : Lanes24.psub 1 x y = x - y := by
  unfold Lanes24.psub Lanes24.mH Lanes24.pmask
  have e : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  have e' : (9223372036854775807 : ℕ) = 2 ^ 63 - 1 := by norm_num
  simp only [Nat.mul_eq, one_mul, Nat.add_eq, Nat.sub_eq, Nat.land_eq, Nat.shiftRight_eq, e, e']
  rw [land_pow63_shr _ (by omega)]
  by_cases h : y ≤ x
  · have h1 : (x + 2 ^ 63 - y) / 2 ^ 63 = 1 := by rw [Nat.div_eq_iff (by positivity)]; constructor <;> omega
    rw [h1, one_mul, Nat.and_two_pow_sub_one_eq_mod]
    rw [show x + 2 ^ 63 - y = (x - y) + 2 ^ 63 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · have h1 : (x + 2 ^ 63 - y) / 2 ^ 63 = 0 := by rw [Nat.div_eq_iff (by positivity)]; constructor <;> omega
    rw [h1, zero_mul, Nat.and_zero]
    omega

theorem pshr1_one (x : ℕ) (hx : x < 2 ^ 64) : Lanes24.pshr1 1 x = x / 2 := by
  unfold Lanes24.pshr1 Lanes24.m63
  have e' : (9223372036854775807 : ℕ) = 2 ^ 63 - 1 := by norm_num
  simp only [Nat.mul_eq, one_mul, Nat.land_eq, Nat.shiftRight_eq, e']
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_one]
  exact Nat.mod_eq_of_lt (by omega)

theorem pmask_plt_one (a b : ℕ) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Lanes24.pmask (Lanes24.plt 1 a b) = if a < b then 2 ^ 63 - 1 else 0 := by
  rw [plt_one a b ha hb]
  unfold Lanes24.pmask
  split_ifs <;> norm_num

theorem psel_cond (c : Prop) [Decidable c] (A B : ℕ) (hA : A < 2 ^ 63) (hB : B < 2 ^ 63) :
    Lanes24.psel (if c then 2 ^ 63 - 1 else 0) A B = if c then A else B := by
  split_ifs
  · exact psel_full A B hA hB
  · exact psel_zero A B

theorem psel_pmask (b A B : ℕ) (hb : b < 2) (hA : A < 2 ^ 63) (hB : B < 2 ^ 63) :
    Lanes24.psel (Lanes24.pmask b) A B = if b = 1 then A else B := by
  interval_cases b
  · rw [show Lanes24.pmask 0 = 0 from rfl, psel_zero]; simp
  · rw [show Lanes24.pmask 1 = 2 ^ 63 - 1 by unfold Lanes24.pmask; norm_num, psel_full _ _ hA hB]; simp

theorem x0_eq (X : ℕ) (hX : X < 2 ^ 63) :
    Nat.land (Nat.sub (Nat.add X (Lanes24.mH 1)) (Nat.mul 1 4611686018427387904)) (Lanes24.m63 1) =
      if X < 2 ^ 62 then X + 2 ^ 62 else X - 2 ^ 62 := by
  unfold Lanes24.mH Lanes24.m63
  have e : (4611686018427387904 : ℕ) = 2 ^ 62 := by norm_num
  have e1 : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  have e2 : (9223372036854775807 : ℕ) = 2 ^ 63 - 1 := by norm_num
  simp only [Nat.mul_eq, one_mul, Nat.add_eq, Nat.sub_eq, Nat.land_eq, e, e1, e2, Nat.and_two_pow_sub_one_eq_mod]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show X + 2 ^ 63 - 2 ^ 62 = (X - 2 ^ 62) + 2 ^ 63 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem sqStep_one (q r s : ℕ) (hq : q < 2 ^ 62) (hr : r < 2 ^ 62) (hs : s < 2 ^ 62) :
    D3Ck2.sqStep 1 q (r, s) = sqStepS q (r, s) := by
  unfold D3Ck2.sqStep sqStepS
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.land_eq, one_mul]
  rw [plt_one r (s + q) (by omega) (by omega), pshr1_one s (by omega)]
  by_cases h : r < s + q
  · simp only [h, ite_true, Nat.sub_self, Lanes24.pmask, Nat.mul_eq, zero_mul, Nat.and_zero, Nat.sub_zero,
      add_zero, show ¬(s + q ≤ r) by omega, ite_false]
  · have e' : (9223372036854775807 : ℕ) = 2 ^ 63 - 1 := by norm_num
    simp only [h, ite_false, Nat.sub_zero, Lanes24.pmask, Nat.mul_eq, one_mul, e',
      Nat.and_two_pow_sub_one_of_lt_two_pow (show s + q < 2 ^ 63 by omega), show s + q ≤ r by omega, ite_true]

theorem sqLoop_one_gen (K : ℕ) (hK : K ≤ 29) :
    ∀ r s, r < 2 ^ 62 → s < 2 ^ 61 → D3Ck2.sqLoop 1 K (r, s) = sqLoopS K (r, s) := by
  induction K with
  | zero => intro r s _ _; rfl
  | succ K ih =>
    intro r s hr hs
    have hq : 4 ^ K ≤ 2 ^ 56 := by
      calc 4 ^ K ≤ 4 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 56 := by norm_num
    have h1 : D3Ck2.sqLoop 1 (K + 1) (r, s) = D3Ck2.sqLoop 1 K (D3Ck2.sqStep 1 (Nat.shiftLeft 1 (Nat.add K K)) (r, s)) :=
      rfl
    have h2 : sqLoopS (K + 1) (r, s) = sqLoopS K (sqStepS (4 ^ K) (r, s)) := rfl
    have h3 : Nat.shiftLeft 1 (Nat.add K K) = 4 ^ K := by
      show 1 <<< (K + K) = 4 ^ K
      rw [Nat.shiftLeft_eq, one_mul, ← two_mul, pow_mul]; norm_num
    rw [h1, h2, h3, sqStep_one _ _ _ (by omega) hr (by omega)]
    unfold sqStepS
    split_ifs with h
    · exact ih (by omega) _ _ (by omega) (by omega)
    · exact ih (by omega) _ _ hr (by omega)

theorem sqLoop_one (K x : ℕ) (hK : K ≤ 29) (hx : x < 4 ^ K) :
    D3Ck2.sqLoop 1 K (x, 0) = sqLoopS K (x, 0) := by
  have : 4 ^ K ≤ 4 ^ 29 := Nat.pow_le_pow_right (by norm_num) hK
  exact sqLoop_one_gen K hK x 0 (by norm_num at this ⊢; omega) (by norm_num)

theorem psqrt_one (W : ℕ) (hW : W ≤ 2 ^ 62 + 2 ^ 56) :
    D3Ck2.psqrt 1 W = Nat.sqrt (W - 2 ^ 62) + 2 ^ 62 := by
  unfold D3Ck2.psqrt
  have e : (4611686018427387904 : ℕ) = 2 ^ 62 := by norm_num
  simp only [Nat.mul_eq, one_mul, Nat.add_eq, e]
  rw [psub_one W (2 ^ 62) (by omega) (by norm_num), sqLoop_one 29 _ le_rfl (by omega),
    sqLoopS_sqrt 29 _ (by omega)]

theorem lane_zero_pack (i : ℕ) : lane 0 i = 0 := by simp [lane]

theorem fits_zero (n b : ℕ) (hb : 0 < b) : Fits n b 0 :=
  ⟨by positivity, fun i _ => by rw [lane_zero_pack i]; exact hb⟩

theorem sqStep_lanes (n q R S : ℕ) (hq : q ≤ 2 ^ 56) (hR : Fits n (2 ^ 62) R) (hS : Fits n (2 ^ 61) S) :
    Fits n (2 ^ 62) (D3Ck2.sqStep (D3Ck2.oN n) q (R, S)).1 ∧ Fits n (2 ^ 61) (D3Ck2.sqStep (D3Ck2.oN n) q (R, S)).2 ∧
      ∀ l < n, (lane (D3Ck2.sqStep (D3Ck2.oN n) q (R, S)).1 l, lane (D3Ck2.sqStep (D3Ck2.oN n) q (R, S)).2 l) =
        sqStepS q (lane R l, lane S l) := by
  have hO := lane_mulc n q (by omega)
  set t := Nat.add S (Nat.mul (D3Ck2.oN n) q) with htdef
  have ht := lane_add n S (Nat.mul (D3Ck2.oN n) q) hS.1 hO.1 (fun i hi => by
    rw [hO.2 i hi]; have := hS.2 i hi; omega)
  have htF : Fits n (2 ^ 63) t := ⟨ht.1, fun i hi => by rw [ht.2 i hi, hO.2 i hi]; have := hS.2 i hi; omega⟩
  have hRF : Fits n (2 ^ 63) R := ⟨hR.1, fun i hi => by have := hR.2 i hi; omega⟩
  have hp := lane_plt n R t hRF htF
  set ge := Nat.sub (D3Ck2.oN n) (Lanes24.plt (D3Ck2.oN n) R t) with hgedef
  have hge := lane_sub n (D3Ck2.oN n) (Lanes24.plt (D3Ck2.oN n) R t) (oN_lt n) hp.1.1 (fun i hi => by
    rw [hp.2 i hi, lane_oN n i hi]; split_ifs <;> omega)
  have hgeF : Fits n 2 ge := ⟨hge.1, fun i hi => by rw [hge.2 i hi, lane_oN n i hi]; omega⟩
  have hm := lane_pmask n ge hgeF
  have hgel : ∀ i < n, lane ge i = if lane S i + q ≤ lane R i then 1 else 0 := fun i hi => by
    rw [hge.2 i hi, hp.2 i hi, lane_oN n i hi, ht.2 i hi, hO.2 i hi]; split_ifs <;> omega
  set la := Nat.land t (Lanes24.pmask ge) with hladef
  have hla_lt : la < 2 ^ (64 * n) := Nat.and_lt_two_pow _ hm.1.1
  have hla : ∀ i < n, lane la i = if lane S i + q ≤ lane R i then lane S i + q else 0 := fun i hi => by
    rw [hladef, lane_land, hm.2 i hi, hgel i hi, ht.2 i hi, hO.2 i hi]
    have := hS.2 i hi
    split_ifs
    · rw [one_mul]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
    · rw [zero_mul]; exact Nat.and_zero _
  have hd := lane_sub n R la hR.1 hla_lt (fun i hi => by rw [hla i hi]; split_ifs <;> omega)
  have hsh := lane_pshr1 n S hS.1
  have hgq := lane_mul n ge q hge.1 (fun i hi => by rw [hgel i hi]; split_ifs <;> omega)
  have hs2 := lane_add n (Lanes24.pshr1 (D3Ck2.oN n) S) (Nat.mul ge q) hsh.1.1 hgq.1 (fun i hi => by
    rw [hsh.2 i hi, hgq.2 i hi, hgel i hi]; have := hS.2 i hi; split_ifs <;> omega)
  have e1 : (D3Ck2.sqStep (D3Ck2.oN n) q (R, S)).1 = Nat.sub R la := rfl
  have e2 : (D3Ck2.sqStep (D3Ck2.oN n) q (R, S)).2 = Nat.add (Lanes24.pshr1 (D3Ck2.oN n) S) (Nat.mul ge q) := rfl
  rw [e1, e2]
  refine ⟨⟨hd.1, fun i hi => ?_⟩, ⟨hs2.1, fun i hi => ?_⟩, fun l hl => ?_⟩
  · rw [hd.2 i hi]; have := hR.2 i hi; omega
  · rw [hs2.2 i hi, hsh.2 i hi, hgq.2 i hi, hgel i hi]; have := hS.2 i hi; split_ifs <;> omega
  · rw [hd.2 l hl, hla l hl, hs2.2 l hl, hsh.2 l hl, hgq.2 l hl, hgel l hl]
    unfold sqStepS
    split_ifs <;> simp

theorem sqLoop_lanes (n K : ℕ) (hK : K ≤ 29) : ∀ R S, Fits n (2 ^ 62) R → Fits n (2 ^ 61) S →
    Fits n (2 ^ 62) (D3Ck2.sqLoop (D3Ck2.oN n) K (R, S)).1 ∧ Fits n (2 ^ 61) (D3Ck2.sqLoop (D3Ck2.oN n) K (R, S)).2 ∧
      ∀ l < n, (lane (D3Ck2.sqLoop (D3Ck2.oN n) K (R, S)).1 l, lane (D3Ck2.sqLoop (D3Ck2.oN n) K (R, S)).2 l) =
        sqLoopS K (lane R l, lane S l) := by
  induction K with
  | zero => intro R S hR hS; exact ⟨hR, hS, fun l _ => rfl⟩
  | succ K ih =>
    intro R S hR hS
    have hq : 4 ^ K ≤ 2 ^ 56 := by
      calc 4 ^ K ≤ 4 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 56 := by norm_num
    have h3 : Nat.shiftLeft 1 (Nat.add K K) = 4 ^ K := by
      show 1 <<< (K + K) = 4 ^ K
      rw [Nat.shiftLeft_eq, one_mul, ← two_mul, pow_mul]; norm_num
    have h1 : D3Ck2.sqLoop (D3Ck2.oN n) (K + 1) (R, S) =
        D3Ck2.sqLoop (D3Ck2.oN n) K (D3Ck2.sqStep (D3Ck2.oN n) (Nat.shiftLeft 1 (Nat.add K K)) (R, S)) := rfl
    have h2 : ∀ s, sqLoopS (K + 1) s = sqLoopS K (sqStepS (4 ^ K) s) := fun _ => rfl
    rw [h1, h3]
    obtain ⟨f1, f2, hst⟩ := sqStep_lanes n (4 ^ K) R S hq hR hS
    obtain ⟨g1, g2, hl⟩ := ih (by omega) _ _ f1 f2
    refine ⟨g1, g2, fun l hlt => ?_⟩
    rw [h2, ← hst l hlt]
    exact hl l hlt

theorem lane_psqrt (n W : ℕ) (hW : Fits n (2 ^ 62 + 2 ^ 56 + 1) W) :
    D3Ck2.psqrt (D3Ck2.oN n) W < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.psqrt (D3Ck2.oN n) W) l = D3Ck2.psqrt 1 (lane W l) := by
  have hc := lane_mulc n 4611686018427387904 (by norm_num)
  have hWF : Fits n (2 ^ 63) W := ⟨hW.1, fun i hi => by have := hW.2 i hi; omega⟩
  have hcF : Fits n (2 ^ 63) (Nat.mul (D3Ck2.oN n) 4611686018427387904) :=
    ⟨hc.1, fun i hi => by rw [hc.2 i hi]; norm_num⟩
  have hps := lane_psub n W _ hWF hcF
  have hR : Fits n (2 ^ 62) (Lanes24.psub (D3Ck2.oN n) W (Nat.mul (D3Ck2.oN n) 4611686018427387904)) :=
    ⟨hps.1.1, fun i hi => by rw [hps.2 i hi, hc.2 i hi]; have := hW.2 i hi; omega⟩
  obtain ⟨_, g2, hl⟩ := sqLoop_lanes n 29 le_rfl _ 0 hR (fits_zero n _ (by positivity))
  have ha := lane_add n _ (Nat.mul (D3Ck2.oN n) 4611686018427387904) g2.1 hc.1 (fun i hi => by
    rw [hc.2 i hi]; have := g2.2 i hi; omega)
  have e : D3Ck2.psqrt (D3Ck2.oN n) W = Nat.add (D3Ck2.sqLoop (D3Ck2.oN n) 29
      (Lanes24.psub (D3Ck2.oN n) W (Nat.mul (D3Ck2.oN n) 4611686018427387904), 0)).2
      (Nat.mul (D3Ck2.oN n) 4611686018427387904) := rfl
  rw [e]
  refine ⟨ha.1, fun l hlt => ?_⟩
  have hw := hW.2 l hlt
  rw [ha.2 l hlt, hc.2 l hlt, psqrt_one _ (by omega)]
  have h2 := congrArg Prod.snd (hl l hlt)
  simp only at h2
  rw [h2, hps.2 l hlt, hc.2 l hlt, lane_zero_pack l, sqLoopS_sqrt 29 _ (by norm_num; omega)]
  norm_num

def scArg (X : ℕ) : ℕ := if X < 2 ^ 62 then PI_LO + 1 else X - 2 ^ 62

theorem red28_one (X : ℕ) (hX : X < 2 ^ 63) :
    D3Ck2.red28 1 X =
      (let x := min (scArg X) (PI_LO + 1)
       let x1 := if HPI_LO < x then PI_LO - x else x
       (if QPI < x1 then HPI_LO - x1 else x1, if QPI < x1 then 2 ^ 63 - 1 else 0,
         if HPI_LO < x then 2 ^ 63 - 1 else 0)) := by
  unfold D3Ck2.red28
  simp only [x0_eq X hX]
  simp only [Lanes24.rep, Nat.mul_eq, one_mul, Nat.sub_eq]
  have hpi : PI_LO = 843314856 := rfl
  have hhpi : HPI_LO = 421657428 := rfl
  have hqpi : QPI = 210828714 := rfl
  have hx : Lanes24.psel (Lanes24.pmask (Lanes24.plt 1 843314857 (if X < 2 ^ 62 then X + 2 ^ 62 else X - 2 ^ 62)))
      843314857 (if X < 2 ^ 62 then X + 2 ^ 62 else X - 2 ^ 62) = min (scArg X) (PI_LO + 1) := by
    have h0 : (if X < 2 ^ 62 then X + 2 ^ 62 else X - 2 ^ 62) < 2 ^ 63 := by split_ifs <;> omega
    rw [pmask_plt_one _ _ (by norm_num) h0, psel_cond _ _ _ (by norm_num) h0]
    unfold scArg
    rw [hpi]
    split_ifs <;> omega
  rw [hx]
  have hxb : min (scArg X) (PI_LO + 1) ≤ 843314857 := by rw [hpi]; omega
  generalize min (scArg X) (PI_LO + 1) = x at hxb ⊢
  have hnm : Lanes24.pmask (Lanes24.plt 1 421657428 x) = if HPI_LO < x then 2 ^ 63 - 1 else 0 := by
    rw [pmask_plt_one _ _ (by norm_num) (by omega), hhpi]
  have hx1 : Lanes24.psel (if HPI_LO < x then 2 ^ 63 - 1 else 0) (Lanes24.psub 1 843314856 x) x =
      if HPI_LO < x then PI_LO - x else x := by
    rw [psub_one _ _ (by norm_num) (by omega), psel_cond _ _ _ (by omega) (by omega), hpi]
  rw [hnm, hx1]
  have hx1b : (if HPI_LO < x then PI_LO - x else x) ≤ 421657428 := by rw [hhpi, hpi]; split_ifs <;> omega
  generalize (if HPI_LO < x then PI_LO - x else x) = x1 at hx1b ⊢
  have hsm : Lanes24.pmask (Lanes24.plt 1 210828714 x1) = if QPI < x1 then 2 ^ 63 - 1 else 0 := by
    rw [pmask_plt_one _ _ (by norm_num) (by omega), hqpi]
  rw [hsm, psel_cond _ _ _ (by omega) (by omega), hhpi]

theorem out28_one (sm nm s c : ℕ) (hsm : sm = 0 ∨ sm = 2 ^ 63 - 1) (hnm : nm = 0 ∨ nm = 2 ^ 63 - 1)
    (hs : s < 2 ^ 62) (hc : c < 2 ^ 62) :
    D3Ck2.out28 1 sm nm s c =
      (2 ^ 62 + (if sm = 0 then s else c),
        if nm = 0 then 2 ^ 62 + (if sm = 0 then c else s) else 2 ^ 62 - (if sm = 0 then c else s)) := by
  unfold D3Ck2.out28
  have e : (4611686018427387904 : ℕ) = 2 ^ 62 := by norm_num
  simp only [Nat.mul_eq, one_mul, Nat.add_eq, Nat.sub_eq, e]
  have hne : (2 ^ 63 - 1 : ℕ) ≠ 0 := by norm_num
  rcases hsm with rfl | rfl <;> rcases hnm with rfl | rfl
  · simp [psel_zero]
  · simp only [psel_zero, ite_true, hne, ite_false]
    rw [psel_full _ _ (by omega) (by omega)]
  · simp only [psel_zero, psel_full c s (by omega) (by omega), psel_full s c (by omega) (by omega), hne, ite_true,
      ite_false]
  · simp only [psel_full c s (by omega) (by omega), psel_full s c (by omega) (by omega), hne, ite_false]
    rw [psel_full _ _ (by omega) (by omega)]

theorem psel_lt (k M A B : ℕ) (hA : A < 2 ^ k) (hB : B < 2 ^ k) : Lanes24.psel M A B < 2 ^ k :=
  Nat.xor_lt_two_pow hB (lt_of_le_of_lt Nat.and_le_left (Nat.xor_lt_two_pow hA hB))

theorem lane_out28 (n sm nm s c : ℕ) (hsm : sm < 2 ^ (64 * n)) (hnm : nm < 2 ^ (64 * n))
    (hm : ∀ i < n, (lane sm i = 0 ∨ lane sm i = 2 ^ 63 - 1) ∧ (lane nm i = 0 ∨ lane nm i = 2 ^ 63 - 1))
    (hs : Fits n (2 ^ 62) s) (hc : Fits n (2 ^ 62) c) :
    Fits n (2 ^ 63) (D3Ck2.out28 (D3Ck2.oN n) sm nm s c).1 ∧ Fits n (2 ^ 63) (D3Ck2.out28 (D3Ck2.oN n) sm nm s c).2 ∧
      ∀ l < n, lane (D3Ck2.out28 (D3Ck2.oN n) sm nm s c).1 l =
          (D3Ck2.out28 1 (lane sm l) (lane nm l) (lane s l) (lane c l)).1 ∧
        lane (D3Ck2.out28 (D3Ck2.oN n) sm nm s c).2 l =
          (D3Ck2.out28 1 (lane sm l) (lane nm l) (lane s l) (lane c l)).2 := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hc0, hc1⟩ := hc

  have hsel : ∀ l < n, ∀ A B : ℕ, A < 2 ^ 62 → B < 2 ^ 62 → Lanes24.psel (lane sm l) A B < 2 ^ 62 := by
    intro l hl A B hA hB
    rcases (hm l hl).1 with h | h <;> rw [h]
    · rw [psel_zero]; exact hB
    · rw [psel_full A B (by omega) (by omega)]; exact hA
  have hsv0 : Lanes24.psel sm c s < 2 ^ (64 * n) := psel_lt _ _ _ _ hc0 hs0
  have hcv0 : Lanes24.psel sm s c < 2 ^ (64 * n) := psel_lt _ _ _ _ hs0 hc0
  have hsvb : ∀ l < n, lane (Lanes24.psel sm c s) l < 2 ^ 62 := fun l hl => by
    rw [lane_psel]; exact hsel l hl _ _ (hc1 l hl) (hs1 l hl)
  have hcvb : ∀ l < n, lane (Lanes24.psel sm s c) l < 2 ^ 62 := fun l hl => by
    rw [lane_psel]; exact hsel l hl _ _ (hs1 l hl) (hc1 l hl)
  obtain ⟨hK0, hKl⟩ := lane_mulc n 4611686018427387904 (by norm_num)
  obtain ⟨hA0, hAl⟩ := lane_add n _ _ hK0 hsv0 (fun i hi => by
    rw [hKl i hi]; have := hsvb i hi; omega)
  obtain ⟨hS0, hSl⟩ := lane_sub n _ _ hK0 hcv0 (fun i hi => by
    rw [hKl i hi]; have := hcvb i hi; omega)
  obtain ⟨hB0, hBl⟩ := lane_add n _ _ hK0 hcv0 (fun i hi => by
    rw [hKl i hi]; have := hcvb i hi; omega)
  unfold D3Ck2.out28
  simp only []
  refine ⟨⟨hA0, fun l hl => ?_⟩, ⟨psel_lt _ _ _ _ hS0 hB0, fun l hl => ?_⟩, fun l hl => ⟨?_, ?_⟩⟩
  · rw [hAl l hl, hKl l hl]; have := hsvb l hl; omega
  · have h1 := hcvb l hl
    rw [lane_psel, hSl l hl, hBl l hl, hKl l hl]
    rcases (hm l hl).2 with h | h <;> rw [h]
    · rw [psel_zero]; omega
    · rw [psel_full _ _ (by omega) (by omega)]; omega
  · rw [hAl l hl, hKl l hl, lane_psel]
    rfl
  · rw [lane_psel, hSl l hl, hBl l hl, hKl l hl, lane_psel]
    rfl

theorem oN_one : D3Ck2.oN 1 = 1 := by
  unfold D3Ck2.oN
  rfl

theorem fits_one {b A : ℕ} (hA : A < b) (hb : b ≤ 2 ^ 64) : Fits 1 b A := by
  refine ⟨by simpa using lt_of_lt_of_le hA hb, fun i hi => ?_⟩
  obtain rfl : i = 0 := by omega
  rw [lane_zero A (lt_of_lt_of_le hA hb)]
  exact hA

theorem rsh_one (P sh : ℕ) (hsh : 1 ≤ sh ∧ sh ≤ 63) (hP : P < 2 ^ 63) : D3Ck2.rsh 1 P sh = rshN P sh := by
  have h := lane_rsh 1 P sh hsh (fits_one hP (by norm_num))
  rw [oN_one] at h
  have h0 := h.2 0 (by norm_num)
  rwa [lane_zero _ (by simpa using h.1), lane_zero _ (lt_trans hP (by norm_num))] at h0

theorem kc_one (A c : ℕ) (hA : A < 2 ^ 64) (hs : A * c < 2 ^ 64) : D3Ck2.kc 1 A c = kcN A c := by
  have h := lane_kc 1 A c (by simpa using hA) (fun i hi => by
    obtain rfl : i = 0 := by omega
    rw [lane_zero A hA]; exact hs)
  rw [oN_one] at h
  have h0 := h.2 0 (by norm_num)
  rwa [lane_zero _ (by simpa using h.1), lane_zero _ hA] at h0

theorem mulF_one (K A B : ℕ) (hK : K ≤ 64) (hA : A < 2 ^ (64 - K)) (hB : B < 2 ^ K) :
    Lanes24.mulF K 1 A B = A * B := by
  have h := lane_mulF K 1 A B hK (fits_one hA (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (fits_one hB (Nat.pow_le_pow_right (by norm_num) hK))
  rw [oN_one] at h
  have h0 := h.2 0 (by norm_num)
  have hA' : A < 2 ^ 64 := lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hB' : B < 2 ^ 64 := lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) hK)
  rwa [lane_zero _ (by simpa using h.1), lane_zero _ hA', lane_zero _ hB'] at h0

theorem rshN_mono {x y : ℕ} (s : ℕ) (h : x ≤ y) : rshN x s ≤ rshN y s :=
  Nat.div_le_div_right (by omega)

theorem rep_one (v : ℕ) : Lanes24.rep 1 v = v := Nat.one_mul v

theorem p2_mono {a b : ℕ} (h : a ≤ b) : p2 a ≤ p2 b := rshN_mono 28 (Nat.mul_le_mul h h)
theorem p4_mono {a b : ℕ} (h : a ≤ b) : p4 a ≤ p4 b := rshN_mono 26 (Nat.mul_le_mul h (rshN_mono 2 h))
theorem p6_mono {a b c d : ℕ} (h1 : a ≤ b) (h2 : c ≤ d) : p6 a c ≤ p6 b d :=
  rshN_mono 20 (Nat.mul_le_mul h2 (rshN_mono 8 h1))
theorem p8_mono {a b : ℕ} (h : a ≤ b) : p8 a ≤ p8 b := rshN_mono 14 (Nat.mul_le_mul h (rshN_mono 14 h))
theorem p10_mono {a b c d : ℕ} (h1 : a ≤ b) (h2 : c ≤ d) : p10 a c ≤ p10 b d :=
  rshN_mono 6 (Nat.mul_le_mul h2 (rshN_mono 22 h1))
theorem kcN_mono {a b : ℕ} (c : ℕ) (h : a ≤ b) : kcN a c ≤ kcN b c :=
  Nat.div_le_div_right (Nat.mul_le_mul_right c h)

theorem p2_le {z : ℕ} (hz : z ≤ QPI) : p2 z ≤ 165584485 := le_trans (p2_mono hz) (by decide)
theorem p4_le {a : ℕ} (h : a ≤ 165584485) : p4 a ≤ 102140835 := le_trans (p4_mono h) (by decide)
theorem p6_le {a b : ℕ} (ha : a ≤ 165584485) (hb : b ≤ 102140835) : p6 a b ≤ 63005564 :=
  le_trans (p6_mono ha hb) (by decide)
theorem p8_le {a : ℕ} (h : a ≤ 102140835) : p8 a ≤ 38863889 := le_trans (p8_mono h) (by decide)
theorem p10_le {a b : ℕ} (ha : a ≤ 165584485) (hb : b ≤ 38863889) : p10 a b ≤ 23682682 :=
  le_trans (p10_mono ha hb) (by decide)

theorem n2_one (z : ℕ) (hz : z ≤ QPI) : D3Ck2.rsh 1 (D3Ck2.mulU28 1 z z) 28 = p2 z := by
  have hq : QPI = 210828714 := rfl
  have h0 : z < 2 ^ 28 := by omega
  rw [mulU28_eq, mulF_one 28 z z (by norm_num) (lt_of_lt_of_le h0 (by norm_num)) h0]
  exact rsh_one _ _ ⟨by norm_num, by norm_num⟩ (lt_of_le_of_lt (Nat.mul_le_mul hz hz) (by rw [hq]; norm_num))

theorem n4_one (z2 : ℕ) (h : z2 ≤ 165584485) :
    D3Ck2.rsh 1 (D3Ck2.mulU26 1 z2 (D3Ck2.rsh 1 z2 2)) 26 = p4 z2 := by
  rw [rsh_one z2 2 ⟨by norm_num, by norm_num⟩ (by omega)]
  have hr : rshN z2 2 ≤ 41396121 := le_trans (rshN_mono 2 h) (by decide)
  rw [mulU26_eq, mulF_one 26 _ _ (by norm_num) (lt_of_le_of_lt h (by norm_num)) (lt_of_le_of_lt hr (by norm_num))]
  exact rsh_one _ _ ⟨by norm_num, by norm_num⟩ (lt_of_le_of_lt (Nat.mul_le_mul h hr) (by norm_num))

theorem n6_one (z2 z4 : ℕ) (h2 : z2 ≤ 165584485) (h4 : z4 ≤ 102140835) :
    D3Ck2.rsh 1 (D3Ck2.mulU20 1 z4 (D3Ck2.rsh 1 z2 8)) 20 = p6 z2 z4 := by
  rw [rsh_one z2 8 ⟨by norm_num, by norm_num⟩ (by omega)]
  have hr : rshN z2 8 ≤ 646814 := le_trans (rshN_mono 8 h2) (by decide)
  rw [mulU20_eq, mulF_one 20 _ _ (by norm_num) (lt_of_le_of_lt h4 (by norm_num)) (lt_of_le_of_lt hr (by norm_num))]
  exact rsh_one _ _ ⟨by norm_num, by norm_num⟩ (lt_of_le_of_lt (Nat.mul_le_mul h4 hr) (by norm_num))

theorem n8_one (z4 : ℕ) (h4 : z4 ≤ 102140835) :
    D3Ck2.rsh 1 (D3Ck2.mulU13 1 z4 (D3Ck2.rsh 1 z4 14)) 14 = p8 z4 := by
  rw [rsh_one z4 14 ⟨by norm_num, by norm_num⟩ (by omega)]
  have hr : rshN z4 14 ≤ 6234 := le_trans (rshN_mono 14 h4) (by decide)
  rw [mulU13_eq, mulF_one 13 _ _ (by norm_num) (lt_of_le_of_lt h4 (by norm_num)) (lt_of_le_of_lt hr (by norm_num))]
  exact rsh_one _ _ ⟨by norm_num, by norm_num⟩ (lt_of_le_of_lt (Nat.mul_le_mul h4 hr) (by norm_num))

theorem n10_one (z2 z8 : ℕ) (h2 : z2 ≤ 165584485) (h8 : z8 ≤ 38863889) :
    D3Ck2.rsh 1 (D3Ck2.mulU6 1 z8 (D3Ck2.rsh 1 z2 22)) 6 = p10 z2 z8 := by
  rw [rsh_one z2 22 ⟨by norm_num, by norm_num⟩ (by omega)]
  have hr : rshN z2 22 ≤ 39 := le_trans (rshN_mono 22 h2) (by decide)
  rw [mulU6_eq, mulF_one 6 _ _ (by norm_num) (lt_of_le_of_lt h8 (by norm_num)) (lt_of_le_of_lt hr (by norm_num))]
  exact rsh_one _ _ ⟨by norm_num, by norm_num⟩ (lt_of_le_of_lt (Nat.mul_le_mul h8 hr) (by norm_num))

theorem ncos_one (z2 z4 z6 z8 z10 : ℕ) (_h2 : z2 ≤ 165584485) (h4 : z4 ≤ 102140835) (h6 : z6 ≤ 63005564)
    (h8 : z8 ≤ 38863889) (h10 : z10 ≤ 23682682) :
    D3Ck2.rsh 1 (Nat.sub (Nat.add (Nat.add (Lanes24.rep 1 68719476736) (D3Ck2.kc 1 z4 2863311531))
      (D3Ck2.kc 1 z8 1704352)) (Nat.add (Nat.add (Nat.shiftLeft z2 7) (D3Ck2.kc 1 z6 95443718))
        (D3Ck2.kc 1 z10 18937))) 8 = cosP z2 z4 z6 z8 z10 := by
  rw [rep_one, kc_one z4 _ (by omega) (by omega), kc_one z8 _ (by omega) (by omega),
    kc_one z6 _ (by omega) (by omega), kc_one z10 _ (by omega) (by omega),
    show Nat.shiftLeft z2 7 = z2 * 2 ^ 7 from Nat.shiftLeft_eq z2 7]
  simp only [Nat.add_eq, Nat.sub_eq]
  have hb : 68719476736 + kcN z4 2863311531 + kcN z8 1704352 ≤
      68719476736 + kcN 102140835 2863311531 + kcN 38863889 1704352 :=
    Nat.add_le_add (Nat.add_le_add_left (kcN_mono _ h4) _) (kcN_mono _ h8)
  rw [rsh_one _ 8 ⟨by norm_num, by norm_num⟩ (lt_of_le_of_lt (le_trans (Nat.sub_le _ _) hb) (by decide))]
  rfl

theorem nsin_one (z z2 z4 z6 z8 : ℕ) (hz : z ≤ QPI) (h2 : z2 ≤ 165584485) (h4 : z4 ≤ 102140835)
    (h6 : z6 ≤ 63005564) (h8 : z8 ≤ 38863889) :
    D3Ck2.rsh 1 (D3Ck2.mulU28 1 (D3Ck2.rsh 1 (Nat.sub (Nat.add (Nat.add (Lanes24.rep 1 68719476736)
      (D3Ck2.kc 1 z4 572662306)) (D3Ck2.kc 1 z8 189372)) (Nat.add (D3Ck2.kc 1 z2 11453246123)
        (D3Ck2.kc 1 z6 13634817))) 6) z) 30 = sinP z z2 z4 z6 z8 := by
  have hq : QPI = 210828714 := rfl
  rw [rep_one, kc_one z4 _ (by omega) (by omega), kc_one z8 _ (by omega) (by omega),
    kc_one z2 _ (by omega) (by omega), kc_one z6 _ (by omega) (by omega)]
  have hb : Nat.sub (Nat.add (Nat.add 68719476736 (kcN z4 572662306)) (kcN z8 189372))
      (Nat.add (kcN z2 11453246123) (kcN z6 13634817)) ≤
      68719476736 + kcN 102140835 572662306 + kcN 38863889 189372 :=
    le_trans (Nat.sub_le _ _) (Nat.add_le_add (Nat.add_le_add_left (kcN_mono _ h4) _) (kcN_mono _ h8))
  rw [rsh_one _ 6 ⟨by norm_num, by norm_num⟩ (lt_of_le_of_lt hb (by decide))]
  have hb30 := le_trans (rshN_mono 6 hb) (show rshN (68719476736 + kcN 102140835 572662306 + kcN 38863889 189372) 6
    ≤ 1077146947 by decide)
  have h0 : z < 2 ^ 28 := by omega
  rw [mulU28_eq, mulF_one 28 _ _ (by norm_num) (lt_of_le_of_lt hb30 (by norm_num)) h0]
  rw [rsh_one _ 30 ⟨by norm_num, by norm_num⟩
    (lt_of_le_of_lt (Nat.mul_le_mul hb30 hz) (by rw [hq]; norm_num))]
  rfl

theorem out_eq (x x1 s c : ℕ) (hs : s < 2 ^ 62) (hc : c < 2 ^ 62) :
    D3Ck2.out28 1 (if QPI < x1 then 2 ^ 63 - 1 else 0) (if HPI_LO < x then 2 ^ 63 - 1 else 0) s c =
      ((((if QPI < x1 then c else s : ℕ) : ℤ) + 2 ^ 62).toNat,
        ((if HPI_LO < x then -((if QPI < x1 then s else c : ℕ) : ℤ) else ((if QPI < x1 then s else c : ℕ) : ℤ)) +
          2 ^ 62).toNat) := by
  rw [out28_one _ _ _ _ (by split_ifs <;> simp) (by split_ifs <;> simp) hs hc]
  have hne : (2 ^ 63 - 1 : ℕ) ≠ 0 := by norm_num
  by_cases h1 : QPI < x1 <;> by_cases h2 : HPI_LO < x <;> simp only [h1, h2, hne, if_true, if_false] <;>
    ext <;> simp <;> omega

def r28x0 (a : ℕ) : ℕ := if a < 2 ^ 62 then a + 2 ^ 62 else a - 2 ^ 62
def r28x (a : ℕ) : ℕ := if 843314857 < r28x0 a then 843314857 else r28x0 a
def r28x1 (a : ℕ) : ℕ := if 421657428 < r28x a then 843314856 - r28x a else r28x a
def r28v (a : ℕ) : ℕ × ℕ × ℕ :=
  (if 210828714 < r28x1 a then 421657428 - r28x1 a else r28x1 a,
    if 210828714 < r28x1 a then 2 ^ 63 - 1 else 0, if 421657428 < r28x a then 2 ^ 63 - 1 else 0)

theorem r28x_le (a : ℕ) : r28x a ≤ 843314857 := by unfold r28x; split_ifs <;> omega
theorem r28x1_le (a : ℕ) : r28x1 a ≤ 421657428 := by
  have := r28x_le a; unfold r28x1; split_ifs <;> omega

theorem red28_lanes (n X : ℕ) (hX : Fits n (2 ^ 63) X) :
    Fits n (2 ^ 63) (D3Ck2.red28 (D3Ck2.oN n) X).1 ∧ Fits n (2 ^ 63) (D3Ck2.red28 (D3Ck2.oN n) X).2.1 ∧
      Fits n (2 ^ 63) (D3Ck2.red28 (D3Ck2.oN n) X).2.2 ∧
      ∀ l < n, lane (D3Ck2.red28 (D3Ck2.oN n) X).1 l = (r28v (lane X l)).1 ∧
        lane (D3Ck2.red28 (D3Ck2.oN n) X).2.1 l = (r28v (lane X l)).2.1 ∧
        lane (D3Ck2.red28 (D3Ck2.oN n) X).2.2 l = (r28v (lane X l)).2.2 := by
  obtain ⟨hX0, hX1⟩ := hX
  have cf : ∀ c : ℕ, c < 2 ^ 63 → Fits n (2 ^ 63) (Nat.mul (D3Ck2.oN n) c) := fun c hc =>
    ⟨(lane_mulc n c (by omega)).1, fun i hi => by rw [(lane_mulc n c (by omega)).2 i hi]; exact hc⟩
  have cl : ∀ c : ℕ, c < 2 ^ 64 → ∀ l < n, lane (Nat.mul (D3Ck2.oN n) c) l = c := fun c hc =>
    (lane_mulc n c hc).2
  have c0 : ∀ c : ℕ, c < 2 ^ 64 → Nat.mul (D3Ck2.oN n) c < 2 ^ (64 * n) := fun c hc => (lane_mulc n c hc).1
  unfold D3Ck2.red28 Lanes24.mH Lanes24.m63 Lanes24.rep
  simp only []

  obtain ⟨hA0, hAl⟩ := lane_add n X _ hX0 (c0 9223372036854775808 (by norm_num)) (fun i hi => by
    rw [cl _ (by norm_num) i hi]; have := hX1 i hi; omega)
  obtain ⟨hS0, hSl⟩ := lane_sub n _ _ hA0 (c0 4611686018427387904 (by norm_num)) (fun i hi => by
    rw [cl _ (by norm_num) i hi, hAl i hi, cl _ (by norm_num) i hi]; omega)
  set x0 := Nat.land (Nat.sub (Nat.add X (Nat.mul (D3Ck2.oN n) 9223372036854775808))
    (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (Nat.mul (D3Ck2.oN n) 9223372036854775807) with hx0
  have hx0l : ∀ l < n, lane x0 l = r28x0 (lane X l) := by
    intro l hl
    have ha := hX1 l hl
    rw [hx0, lane_land, hSl l hl, hAl l hl, cl _ (by norm_num) l hl, cl _ (by norm_num) l hl,
      cl _ (by norm_num) l hl]
    have e : (4611686018427387904 : ℕ) = 2 ^ 62 := by norm_num
    have e1 : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
    have e2 : (9223372036854775807 : ℕ) = 2 ^ 63 - 1 := by norm_num
    simp only [Nat.land_eq, e, e1, e2, Nat.and_two_pow_sub_one_eq_mod, r28x0]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show lane X l + 2 ^ 63 - 2 ^ 62 = (lane X l - 2 ^ 62) + 2 ^ 63 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
  have hx0f : Fits n (2 ^ 63) x0 := ⟨lt_of_le_of_lt Nat.and_le_left hS0, fun l hl => by
    rw [hx0l l hl, r28x0]; have := hX1 l hl; split_ifs <;> omega⟩

  obtain ⟨hP, hPl⟩ := lane_plt n _ _ (cf 843314857 (by norm_num)) hx0f
  obtain ⟨hK, hKl⟩ := lane_pmask n _ hP
  set xx := Lanes24.psel (Lanes24.pmask (Lanes24.plt (D3Ck2.oN n) (Nat.mul (D3Ck2.oN n) 843314857) x0))
    (Nat.mul (D3Ck2.oN n) 843314857) x0 with hxx
  have hxxl : ∀ l < n, lane xx l = r28x (lane X l) := by
    intro l hl
    have hb := hx0f.2 l hl
    rw [hx0l l hl] at hb
    rw [hxx, lane_psel, hKl l hl, hPl l hl, cl _ (by norm_num) l hl, hx0l l hl, r28x]
    split_ifs with h
    · rw [one_mul, psel_full _ _ (by norm_num) hb]
    · rw [zero_mul, psel_zero]
  have hxxf : Fits n (2 ^ 63) xx := ⟨psel_lt _ _ _ _ (c0 _ (by norm_num)) hx0f.1, fun l hl => by
    rw [hxxl l hl]; have := r28x_le (lane X l); omega⟩

  obtain ⟨hP2, hP2l⟩ := lane_plt n _ _ (cf 421657428 (by norm_num)) hxxf
  obtain ⟨hK2, hK2l⟩ := lane_pmask n _ hP2
  set nmm := Lanes24.pmask (Lanes24.plt (D3Ck2.oN n) (Nat.mul (D3Ck2.oN n) 421657428) xx) with hnmm
  have hnml : ∀ l < n, lane nmm l = if 421657428 < r28x (lane X l) then 2 ^ 63 - 1 else 0 := by
    intro l hl
    rw [hnmm, hK2l l hl, hP2l l hl, cl _ (by norm_num) l hl, hxxl l hl]
    split_ifs <;> simp

  obtain ⟨hU, hUl⟩ := lane_psub n _ _ (cf 843314856 (by norm_num)) hxxf
  set x1 := Lanes24.psel nmm (Lanes24.psub (D3Ck2.oN n) (Nat.mul (D3Ck2.oN n) 843314856) xx) xx with hx1
  have hx1l : ∀ l < n, lane x1 l = r28x1 (lane X l) := by
    intro l hl
    have hb := r28x_le (lane X l)
    rw [hx1, lane_psel, hnml l hl, hUl l hl, cl _ (by norm_num) l hl, hxxl l hl, r28x1]
    split_ifs with h
    · rw [psel_full _ _ (by omega) (by omega)]
    · rw [psel_zero]
  have hx10 : x1 < 2 ^ (64 * n) := psel_lt _ _ _ _ hU.1 hxxf.1
  have hx1f : Fits n (2 ^ 63) x1 := ⟨hx10, fun l hl => by
    rw [hx1l l hl]; have := r28x1_le (lane X l); omega⟩

  obtain ⟨hP4, hP4l⟩ := lane_plt n _ _ (cf 210828714 (by norm_num)) hx1f
  obtain ⟨hK4, hK4l⟩ := lane_pmask n _ hP4
  set smm := Lanes24.pmask (Lanes24.plt (D3Ck2.oN n) (Nat.mul (D3Ck2.oN n) 210828714) x1) with hsmm
  have hsml : ∀ l < n, lane smm l = if 210828714 < r28x1 (lane X l) then 2 ^ 63 - 1 else 0 := by
    intro l hl
    rw [hsmm, hK4l l hl, hP4l l hl, cl _ (by norm_num) l hl, hx1l l hl]
    split_ifs <;> simp

  obtain ⟨hZ0, hZl⟩ := lane_sub n _ _ (c0 421657428 (by norm_num)) hx10 (fun i hi => by
    rw [cl _ (by norm_num) i hi, hx1l i hi]; exact r28x1_le _)
  have hzl : ∀ l < n, lane (Lanes24.psel smm (Nat.sub (Nat.mul (D3Ck2.oN n) 421657428) x1) x1) l =
      (r28v (lane X l)).1 := by
    intro l hl
    have hb := r28x1_le (lane X l)
    rw [lane_psel, hsml l hl, hZl l hl, cl _ (by norm_num) l hl, hx1l l hl]
    simp only [r28v]
    split_ifs with h
    · exact psel_full _ _ (by omega) (by omega)
    · exact psel_zero _ _
  refine ⟨⟨psel_lt _ _ _ _ hZ0 hx10, fun l hl => ?_⟩, hK4, hK2, fun l hl => ⟨hzl l hl, ?_, ?_⟩⟩
  · rw [hzl l hl]; simp only [r28v]; have := r28x1_le (lane X l); split_ifs <;> omega
  · rw [hsml l hl]; simp only [r28v]
  · rw [hnml l hl]; simp only [r28v]

theorem lane_red28 (n X : ℕ) (hX : Fits n (2 ^ 63) X) :
    Fits n (2 ^ 63) (D3Ck2.red28 (D3Ck2.oN n) X).1 ∧ Fits n (2 ^ 63) (D3Ck2.red28 (D3Ck2.oN n) X).2.1 ∧
      Fits n (2 ^ 63) (D3Ck2.red28 (D3Ck2.oN n) X).2.2 ∧
      ∀ l < n, lane (D3Ck2.red28 (D3Ck2.oN n) X).1 l = (D3Ck2.red28 1 (lane X l)).1 ∧
        lane (D3Ck2.red28 (D3Ck2.oN n) X).2.1 l = (D3Ck2.red28 1 (lane X l)).2.1 ∧
        lane (D3Ck2.red28 (D3Ck2.oN n) X).2.2 l = (D3Ck2.red28 1 (lane X l)).2.2 := by
  obtain ⟨f1, f2, f3, hl⟩ := red28_lanes n X hX
  refine ⟨f1, f2, f3, fun l hl' => ?_⟩
  have ha : lane X l < 2 ^ 63 := hX.2 l hl'
  obtain ⟨g1, g2, g3, gl⟩ := red28_lanes 1 (lane X l) (fits_one ha (by norm_num))
  rw [oN_one] at g1 g2 g3 gl
  obtain ⟨e1, e2, e3⟩ := gl 0 (by norm_num)
  have ha' : lane (lane X l) 0 = lane X l := lane_zero _ (lt_trans ha (by norm_num))
  rw [ha', lane_zero _ (by simpa using g1.1)] at e1
  rw [ha', lane_zero _ (by simpa using g2.1)] at e2
  rw [ha', lane_zero _ (by simpa using g3.1)] at e3
  obtain ⟨d1, d2, d3⟩ := hl l hl'
  exact ⟨d1.trans e1.symm, d2.trans e2.symm, d3.trans e3.symm⟩

theorem sc28u_one (X : ℕ) (hX : X < 2 ^ 63) :
    D3Ck2.sc28u 1 X = (((sc28pS (scArg X)).1 + 2 ^ 62).toNat, ((sc28pS (scArg X)).2 + 2 ^ 62).toNat) := by
  have eQ : QPI = 210828714 := rfl
  have eH : HPI_LO = 421657428 := rfl
  have eP : PI_LO = 843314856 := rfl
  have hr := red28_one X hX
  unfold D3Ck2.sc28u sc28pS sc28pZ
  simp only [hr]
  generalize hx : min (scArg X) (PI_LO + 1) = x
  have hxle : x ≤ PI_LO + 1 := hx ▸ min_le_right _ _
  generalize hx1 : (if HPI_LO < x then PI_LO - x else x) = x1
  have hx1le : x1 ≤ HPI_LO := by rw [← hx1]; split_ifs <;> omega
  generalize hz : (if QPI < x1 then HPI_LO - x1 else x1) = z
  have hzle : z ≤ QPI := by rw [← hz]; split_ifs <;> omega
  have b2 := p2_le hzle
  have b4 := p4_le b2
  have b6 := p6_le b2 b4
  have b8 := p8_le b4
  have b10 := p10_le b2 b8
  rw [n2_one z hzle, n4_one _ b2, n6_one _ _ b2 b4, n8_one _ b4, n10_one _ _ b2 b8,
    ncos_one _ _ _ _ _ b2 b4 b6 b8 b10, nsin_one _ _ _ _ _ hzle b2 b4 b6 b8]

  obtain ⟨es, ec⟩ := sc28pZ_err z hzle
  have hs : (sc28pZ z).1 < 2 ^ 62 := by
    have h := (abs_le.mp es).2
    have h1 := Real.sin_le_one ((z : ℝ) / 2 ^ 28)
    have : ((sc28pZ z).1 : ℝ) < 2 ^ 62 := by linarith
    exact_mod_cast this
  have hc : (sc28pZ z).2 < 2 ^ 62 := by
    have h := (abs_le.mp ec).2
    have h1 := Real.cos_le_one ((z : ℝ) / 2 ^ 28)
    have : ((sc28pZ z).2 : ℝ) < 2 ^ 62 := by linarith
    exact_mod_cast this
  exact out_eq x x1 _ _ hs hc

noncomputable def pz2 (O Z : ℕ) : ℕ := D3Ck2.rsh O (D3Ck2.mulU28 O Z Z) 28
noncomputable def pz4 (O Z2 : ℕ) : ℕ := D3Ck2.rsh O (D3Ck2.mulU26 O Z2 (D3Ck2.rsh O Z2 2)) 26
noncomputable def pz6 (O Z2 Z4 : ℕ) : ℕ := D3Ck2.rsh O (D3Ck2.mulU20 O Z4 (D3Ck2.rsh O Z2 8)) 20
noncomputable def pz8 (O Z4 : ℕ) : ℕ := D3Ck2.rsh O (D3Ck2.mulU13 O Z4 (D3Ck2.rsh O Z4 14)) 14
noncomputable def pz10 (O Z2 Z8 : ℕ) : ℕ := D3Ck2.rsh O (D3Ck2.mulU6 O Z8 (D3Ck2.rsh O Z2 22)) 6

noncomputable def pcos (O Z2 Z4 Z6 Z8 Z10 : ℕ) : ℕ :=
  D3Ck2.rsh O (Nat.sub (Nat.add (Nat.add (Lanes24.rep O 68719476736) (D3Ck2.kc O Z4 2863311531))
    (D3Ck2.kc O Z8 1704352)) (Nat.add (Nat.add (Nat.shiftLeft Z2 7) (D3Ck2.kc O Z6 95443718))
      (D3Ck2.kc O Z10 18937))) 8

noncomputable def psin (O Z Z2 Z4 Z6 Z8 : ℕ) : ℕ :=
  D3Ck2.rsh O (D3Ck2.mulU28 O (D3Ck2.rsh O (Nat.sub (Nat.add (Nat.add (Lanes24.rep O 68719476736)
    (D3Ck2.kc O Z4 572662306)) (D3Ck2.kc O Z8 189372)) (Nat.add (D3Ck2.kc O Z2 11453246123)
      (D3Ck2.kc O Z6 13634817))) 6) Z) 30

noncomputable def pS (O Z : ℕ) : ℕ :=
  psin O Z (pz2 O Z) (pz4 O (pz2 O Z)) (pz6 O (pz2 O Z) (pz4 O (pz2 O Z))) (pz8 O (pz4 O (pz2 O Z)))

noncomputable def pC (O Z : ℕ) : ℕ :=
  pcos O (pz2 O Z) (pz4 O (pz2 O Z)) (pz6 O (pz2 O Z) (pz4 O (pz2 O Z))) (pz8 O (pz4 O (pz2 O Z)))
    (pz10 O (pz2 O Z) (pz8 O (pz4 O (pz2 O Z))))

theorem sc28u_split (O X : ℕ) : D3Ck2.sc28u O X =
    D3Ck2.out28 O (D3Ck2.red28 O X).2.1 (D3Ck2.red28 O X).2.2 (pS O (D3Ck2.red28 O X).1) (pC O (D3Ck2.red28 O X).1) :=
  rfl

theorem fits_le {n b c Z : ℕ} (hZ : Z < 2 ^ (64 * n)) (h : ∀ i < n, lane Z i ≤ c) (hc : c < b) : Fits n b Z :=
  ⟨hZ, fun i hi => lt_of_le_of_lt (h i hi) hc⟩

theorem rshmul_lanes (K sh n A B : ℕ) (hK : K ≤ 64) (hsh : 1 ≤ sh ∧ sh ≤ 63)
    (hA : Fits n (2 ^ (64 - K)) A) (hB : Fits n (2 ^ K) B) (hp : ∀ i < n, lane A i * lane B i < 2 ^ 63) :
    D3Ck2.rsh (D3Ck2.oN n) (Lanes24.mulF K (D3Ck2.oN n) A B) sh < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.rsh (D3Ck2.oN n) (Lanes24.mulF K (D3Ck2.oN n) A B) sh) l =
        rshN (lane A l * lane B l) sh := by
  have hm := lane_mulF K n A B hK hA hB
  have hr := lane_rsh n _ sh hsh ⟨hm.1, fun i hi => by rw [hm.2 i hi]; exact hp i hi⟩
  exact ⟨hr.1, fun l hl => by rw [hr.2 l hl, hm.2 l hl]⟩

theorem rsh_lanes_le (n P sh c : ℕ) (hsh : 1 ≤ sh ∧ sh ≤ 63) (hP : P < 2 ^ (64 * n))
    (hb : ∀ i < n, lane P i ≤ c) (hc : c < 2 ^ 63) :
    D3Ck2.rsh (D3Ck2.oN n) P sh < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.rsh (D3Ck2.oN n) P sh) l = rshN (lane P l) sh ∧ rshN (lane P l) sh ≤ rshN c sh := by
  have hr := lane_rsh n P sh hsh (fits_le hP hb hc)
  exact ⟨hr.1, fun l hl => ⟨hr.2 l hl, rshN_mono sh (hb l hl)⟩⟩

theorem kc_lanes (n A c B : ℕ) (hA : A < 2 ^ (64 * n)) (hb : ∀ i < n, lane A i ≤ B) (hc : B * c < 2 ^ 64) :
    D3Ck2.kc (D3Ck2.oN n) A c < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.kc (D3Ck2.oN n) A c) l = kcN (lane A l) c ∧ kcN (lane A l) c ≤ kcN B c := by
  have h := lane_kc n A c hA (fun i hi => lt_of_le_of_lt (Nat.mul_le_mul_right c (hb i hi)) hc)
  exact ⟨h.1, fun l hl => ⟨h.2 l hl, kcN_mono c (hb l hl)⟩⟩

theorem pz2_lanes (n Z : ℕ) (hZ : Z < 2 ^ (64 * n)) (hz : ∀ i < n, lane Z i ≤ QPI) :
    pz2 (D3Ck2.oN n) Z < 2 ^ (64 * n) ∧ ∀ l < n, lane (pz2 (D3Ck2.oN n) Z) l = p2 (lane Z l) := by
  have hq : QPI = 210828714 := rfl
  unfold pz2; rw [mulU28_eq]
  have r := rshmul_lanes 28 28 n Z Z (by norm_num) ⟨by norm_num, by norm_num⟩
    (fits_le hZ hz (by rw [hq]; norm_num)) (fits_le hZ hz (by rw [hq]; norm_num))
    (fun i hi => lt_of_le_of_lt (Nat.mul_le_mul (hz i hi) (hz i hi)) (by rw [hq]; norm_num))
  exact ⟨r.1, fun l hl => r.2 l hl⟩

theorem pz4_lanes (n Z2 : ℕ) (h : Z2 < 2 ^ (64 * n)) (hb : ∀ i < n, lane Z2 i ≤ 165584485) :
    pz4 (D3Ck2.oN n) Z2 < 2 ^ (64 * n) ∧ ∀ l < n, lane (pz4 (D3Ck2.oN n) Z2) l = p4 (lane Z2 l) := by
  unfold pz4; rw [mulU26_eq]
  obtain ⟨r1, r2⟩ := rsh_lanes_le n Z2 2 _ ⟨by norm_num, by norm_num⟩ h hb (by norm_num)
  have hr : rshN 165584485 2 ≤ 41396121 := by decide
  have r := rshmul_lanes 26 26 n Z2 (D3Ck2.rsh (D3Ck2.oN n) Z2 2) (by norm_num) ⟨by norm_num, by norm_num⟩
    (fits_le h hb (by norm_num))
    (fits_le r1 (fun i hi => by rw [(r2 i hi).1]; exact le_trans (r2 i hi).2 hr) (by norm_num))
    (fun i hi => by
      rw [(r2 i hi).1]; exact lt_of_le_of_lt (Nat.mul_le_mul (hb i hi) (le_trans (r2 i hi).2 hr)) (by norm_num))
  exact ⟨r.1, fun l hl => by rw [r.2 l hl, (r2 l hl).1]; rfl⟩

theorem pz6_lanes (n Z2 Z4 : ℕ) (h2 : Z2 < 2 ^ (64 * n)) (h4 : Z4 < 2 ^ (64 * n))
    (b2 : ∀ i < n, lane Z2 i ≤ 165584485) (b4 : ∀ i < n, lane Z4 i ≤ 102140835) :
    pz6 (D3Ck2.oN n) Z2 Z4 < 2 ^ (64 * n) ∧
      ∀ l < n, lane (pz6 (D3Ck2.oN n) Z2 Z4) l = p6 (lane Z2 l) (lane Z4 l) := by
  unfold pz6; rw [mulU20_eq]
  obtain ⟨r1, r2⟩ := rsh_lanes_le n Z2 8 _ ⟨by norm_num, by norm_num⟩ h2 b2 (by norm_num)
  have hr : rshN 165584485 8 ≤ 646814 := by decide
  have r := rshmul_lanes 20 20 n Z4 (D3Ck2.rsh (D3Ck2.oN n) Z2 8) (by norm_num) ⟨by norm_num, by norm_num⟩
    (fits_le h4 b4 (by norm_num))
    (fits_le r1 (fun i hi => by rw [(r2 i hi).1]; exact le_trans (r2 i hi).2 hr) (by norm_num))
    (fun i hi => by
      rw [(r2 i hi).1]; exact lt_of_le_of_lt (Nat.mul_le_mul (b4 i hi) (le_trans (r2 i hi).2 hr)) (by norm_num))
  exact ⟨r.1, fun l hl => by rw [r.2 l hl, (r2 l hl).1]; rfl⟩

theorem pz8_lanes (n Z4 : ℕ) (h4 : Z4 < 2 ^ (64 * n)) (b4 : ∀ i < n, lane Z4 i ≤ 102140835) :
    pz8 (D3Ck2.oN n) Z4 < 2 ^ (64 * n) ∧ ∀ l < n, lane (pz8 (D3Ck2.oN n) Z4) l = p8 (lane Z4 l) := by
  unfold pz8; rw [mulU13_eq]
  obtain ⟨r1, r2⟩ := rsh_lanes_le n Z4 14 _ ⟨by norm_num, by norm_num⟩ h4 b4 (by norm_num)
  have hr : rshN 102140835 14 ≤ 6234 := by decide
  have r := rshmul_lanes 13 14 n Z4 (D3Ck2.rsh (D3Ck2.oN n) Z4 14) (by norm_num) ⟨by norm_num, by norm_num⟩
    (fits_le h4 b4 (by norm_num))
    (fits_le r1 (fun i hi => by rw [(r2 i hi).1]; exact le_trans (r2 i hi).2 hr) (by norm_num))
    (fun i hi => by
      rw [(r2 i hi).1]; exact lt_of_le_of_lt (Nat.mul_le_mul (b4 i hi) (le_trans (r2 i hi).2 hr)) (by norm_num))
  exact ⟨r.1, fun l hl => by rw [r.2 l hl, (r2 l hl).1]; rfl⟩

theorem pz10_lanes (n Z2 Z8 : ℕ) (h2 : Z2 < 2 ^ (64 * n)) (h8 : Z8 < 2 ^ (64 * n))
    (b2 : ∀ i < n, lane Z2 i ≤ 165584485) (b8 : ∀ i < n, lane Z8 i ≤ 38863889) :
    pz10 (D3Ck2.oN n) Z2 Z8 < 2 ^ (64 * n) ∧
      ∀ l < n, lane (pz10 (D3Ck2.oN n) Z2 Z8) l = p10 (lane Z2 l) (lane Z8 l) := by
  unfold pz10; rw [mulU6_eq]
  obtain ⟨r1, r2⟩ := rsh_lanes_le n Z2 22 _ ⟨by norm_num, by norm_num⟩ h2 b2 (by norm_num)
  have hr : rshN 165584485 22 ≤ 39 := by decide
  have r := rshmul_lanes 6 6 n Z8 (D3Ck2.rsh (D3Ck2.oN n) Z2 22) (by norm_num) ⟨by norm_num, by norm_num⟩
    (fits_le h8 b8 (by norm_num))
    (fits_le r1 (fun i hi => by rw [(r2 i hi).1]; exact le_trans (r2 i hi).2 hr) (by norm_num))
    (fun i hi => by
      rw [(r2 i hi).1]; exact lt_of_le_of_lt (Nat.mul_le_mul (b8 i hi) (le_trans (r2 i hi).2 hr)) (by norm_num))
  exact ⟨r.1, fun l hl => by rw [r.2 l hl, (r2 l hl).1]; rfl⟩

theorem pcos_lanes (n Z2 Z4 Z6 Z8 Z10 : ℕ) (h2 : Z2 < 2 ^ (64 * n)) (h4 : Z4 < 2 ^ (64 * n))
    (h6 : Z6 < 2 ^ (64 * n)) (h8 : Z8 < 2 ^ (64 * n)) (h10 : Z10 < 2 ^ (64 * n))
    (b2 : ∀ i < n, lane Z2 i ≤ 165584485) (b4 : ∀ i < n, lane Z4 i ≤ 102140835)
    (b6 : ∀ i < n, lane Z6 i ≤ 63005564) (b8 : ∀ i < n, lane Z8 i ≤ 38863889)
    (b10 : ∀ i < n, lane Z10 i ≤ 23682682) :
    pcos (D3Ck2.oN n) Z2 Z4 Z6 Z8 Z10 < 2 ^ (64 * n) ∧ ∀ l < n,
      lane (pcos (D3Ck2.oN n) Z2 Z4 Z6 Z8 Z10) l = cosP (lane Z2 l) (lane Z4 l) (lane Z6 l) (lane Z8 l) (lane Z10 l) := by
  unfold pcos Lanes24.rep
  have a1 := lane_mulc n 68719476736 (by norm_num)
  obtain ⟨k4, k4l⟩ := kc_lanes n Z4 2863311531 102140835 h4 b4 (by norm_num)
  obtain ⟨k8, k8l⟩ := kc_lanes n Z8 1704352 38863889 h8 b8 (by norm_num)
  obtain ⟨k6, k6l⟩ := kc_lanes n Z6 95443718 63005564 h6 b6 (by norm_num)
  obtain ⟨k10, k10l⟩ := kc_lanes n Z10 18937 23682682 h10 b10 (by norm_num)
  have v4 : kcN 102140835 2863311531 = 1089502240 := by decide
  have v8 : kcN 38863889 1704352 = 246754 := by decide
  have v6 : kcN 63005564 95443718 = 22401978 := by decide
  have v10 : kcN 23682682 18937 = 1670 := by decide
  have a2 := lane_add n _ _ a1.1 k4 (fun i hi => by
    rw [a1.2 i hi, (k4l i hi).1]; have := (k4l i hi).2; omega)
  have a3 := lane_add n _ _ a2.1 k8 (fun i hi => by
    rw [a2.2 i hi, a1.2 i hi, (k4l i hi).1, (k8l i hi).1]; have := (k4l i hi).2; have := (k8l i hi).2; omega)
  have s1 := lane_shl n Z2 7 h2 (fun i hi => by have := b2 i hi; norm_num; omega)
  have c2 := lane_add n _ _ s1.1 k6 (fun i hi => by
    rw [s1.2 i hi, (k6l i hi).1]; have := b2 i hi; have := (k6l i hi).2; omega)
  have c3 := lane_add n _ _ c2.1 k10 (fun i hi => by
    rw [c2.2 i hi, s1.2 i hi, (k6l i hi).1, (k10l i hi).1]; have := b2 i hi; have := (k6l i hi).2
    have := (k10l i hi).2; omega)
  have d := lane_sub n _ _ a3.1 c3.1 (fun i hi => by
    rw [a3.2 i hi, a2.2 i hi, a1.2 i hi, (k4l i hi).1, (k8l i hi).1, c3.2 i hi, c2.2 i hi, s1.2 i hi,
      (k6l i hi).1, (k10l i hi).1]
    have := b2 i hi; have := (k6l i hi).2; have := (k10l i hi).2; omega)
  have r := lane_rsh n _ 8 ⟨by norm_num, by norm_num⟩ ⟨d.1, fun i hi => by
    rw [d.2 i hi, a3.2 i hi, a2.2 i hi, a1.2 i hi, (k4l i hi).1, (k8l i hi).1]
    have := (k4l i hi).2; have := (k8l i hi).2; omega⟩
  refine ⟨r.1, fun l hl => ?_⟩
  rw [r.2 l hl, d.2 l hl, a3.2 l hl, a2.2 l hl, a1.2 l hl, (k4l l hl).1, (k8l l hl).1, c3.2 l hl, c2.2 l hl,
    s1.2 l hl, (k6l l hl).1, (k10l l hl).1]
  rfl

theorem psin_lanes (n Z Z2 Z4 Z6 Z8 : ℕ) (hZ : Z < 2 ^ (64 * n)) (h2 : Z2 < 2 ^ (64 * n))
    (h4 : Z4 < 2 ^ (64 * n)) (h6 : Z6 < 2 ^ (64 * n)) (h8 : Z8 < 2 ^ (64 * n)) (bz : ∀ i < n, lane Z i ≤ QPI)
    (b2 : ∀ i < n, lane Z2 i ≤ 165584485) (b4 : ∀ i < n, lane Z4 i ≤ 102140835)
    (b6 : ∀ i < n, lane Z6 i ≤ 63005564) (b8 : ∀ i < n, lane Z8 i ≤ 38863889) :
    psin (D3Ck2.oN n) Z Z2 Z4 Z6 Z8 < 2 ^ (64 * n) ∧ ∀ l < n,
      lane (psin (D3Ck2.oN n) Z Z2 Z4 Z6 Z8) l = sinP (lane Z l) (lane Z2 l) (lane Z4 l) (lane Z6 l) (lane Z8 l) := by
  have hQ : QPI = 210828714 := rfl
  unfold psin Lanes24.rep
  rw [mulU28_eq]
  have a1 := lane_mulc n 68719476736 (by norm_num)
  obtain ⟨k4, k4l⟩ := kc_lanes n Z4 572662306 102140835 h4 b4 (by norm_num)
  obtain ⟨k8, k8l⟩ := kc_lanes n Z8 189372 38863889 h8 b8 (by norm_num)
  obtain ⟨k2, k2l⟩ := kc_lanes n Z2 11453246123 165584485 h2 b2 (by norm_num)
  obtain ⟨k6, k6l⟩ := kc_lanes n Z6 13634817 63005564 h6 b6 (by norm_num)
  have v4 : kcN 102140835 572662306 = 217900447 := by decide
  have v8 : kcN 38863889 189372 = 27417 := by decide
  have v2 : kcN 165584485 11453246123 = 7064938026 := by decide
  have v6 : kcN 63005564 13634817 = 3200282 := by decide
  have a2 := lane_add n _ _ a1.1 k4 (fun i hi => by
    rw [a1.2 i hi, (k4l i hi).1]; have := (k4l i hi).2; omega)
  have a3 := lane_add n _ _ a2.1 k8 (fun i hi => by
    rw [a2.2 i hi, a1.2 i hi, (k4l i hi).1, (k8l i hi).1]; have := (k4l i hi).2; have := (k8l i hi).2; omega)
  have c2 := lane_add n _ _ k2 k6 (fun i hi => by
    rw [(k2l i hi).1, (k6l i hi).1]; have := (k2l i hi).2; have := (k6l i hi).2; omega)
  have d := lane_sub n _ _ a3.1 c2.1 (fun i hi => by
    rw [a3.2 i hi, a2.2 i hi, a1.2 i hi, (k4l i hi).1, (k8l i hi).1, c2.2 i hi, (k2l i hi).1, (k6l i hi).1]
    have := (k2l i hi).2; have := (k6l i hi).2; omega)
  obtain ⟨q1, q2⟩ := rsh_lanes_le n _ 6 68937404600 ⟨by norm_num, by norm_num⟩ d.1 (fun i hi => by
    rw [d.2 i hi, a3.2 i hi, a2.2 i hi, a1.2 i hi, (k4l i hi).1, (k8l i hi).1]
    have := (k4l i hi).2; have := (k8l i hi).2; omega) (by norm_num)
  have hq : rshN 68937404600 6 ≤ 1077146947 := by decide
  have r := rshmul_lanes 28 30 n _ Z (by norm_num) ⟨by norm_num, by norm_num⟩
    (fits_le q1 (fun i hi => by rw [(q2 i hi).1]; exact le_trans (q2 i hi).2 hq) (by norm_num))
    (fits_le hZ bz (by rw [hQ]; norm_num))
    (fun i hi => by
      rw [(q2 i hi).1]
      exact lt_of_le_of_lt (Nat.mul_le_mul (le_trans (q2 i hi).2 hq) (bz i hi)) (by rw [hQ]; norm_num))
  refine ⟨r.1, fun l hl => ?_⟩
  rw [r.2 l hl, (q2 l hl).1, d.2 l hl, a3.2 l hl, a2.2 l hl, a1.2 l hl, (k4l l hl).1, (k8l l hl).1, c2.2 l hl,
    (k2l l hl).1, (k6l l hl).1]
  rfl

theorem sc28pZ_lt (z : ℕ) (hz : z ≤ QPI) : (sc28pZ z).1 < 2 ^ 62 ∧ (sc28pZ z).2 < 2 ^ 62 := by
  obtain ⟨es, ec⟩ := sc28pZ_err z hz
  constructor
  · have h := (abs_le.mp es).2
    have h1 := Real.sin_le_one ((z : ℝ) / 2 ^ 28)
    have : ((sc28pZ z).1 : ℝ) < 2 ^ 62 := by linarith
    exact_mod_cast this
  · have h := (abs_le.mp ec).2
    have h1 := Real.cos_le_one ((z : ℝ) / 2 ^ 28)
    have : ((sc28pZ z).2 : ℝ) < 2 ^ 62 := by linarith
    exact_mod_cast this

theorem sc_lanes (n Z : ℕ) (hZ : Z < 2 ^ (64 * n)) (hz : ∀ i < n, lane Z i ≤ QPI) :
    Fits n (2 ^ 62) (pS (D3Ck2.oN n) Z) ∧ Fits n (2 ^ 62) (pC (D3Ck2.oN n) Z) ∧
      ∀ l < n, lane (pS (D3Ck2.oN n) Z) l = (sc28pZ (lane Z l)).1 ∧
        lane (pC (D3Ck2.oN n) Z) l = (sc28pZ (lane Z l)).2 := by
  unfold pS pC
  obtain ⟨c2, l2⟩ := pz2_lanes n Z hZ hz
  have b2 : ∀ i < n, lane (pz2 (D3Ck2.oN n) Z) i ≤ 165584485 := fun i hi => by rw [l2 i hi]; exact p2_le (hz i hi)
  obtain ⟨c4, l4⟩ := pz4_lanes n _ c2 b2
  have b4 : ∀ i < n, lane (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z)) i ≤ 102140835 := fun i hi => by
    rw [l4 i hi]; exact p4_le (b2 i hi)
  obtain ⟨c6, l6⟩ := pz6_lanes n _ _ c2 c4 b2 b4
  have b6 : ∀ i < n, lane (pz6 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z))) i ≤
      63005564 := fun i hi => by rw [l6 i hi]; exact p6_le (b2 i hi) (b4 i hi)
  obtain ⟨c8, l8⟩ := pz8_lanes n _ c4 b4
  have b8 : ∀ i < n, lane (pz8 (D3Ck2.oN n) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z))) i ≤ 38863889 := fun i hi => by
    rw [l8 i hi]; exact p8_le (b4 i hi)
  obtain ⟨c10, l10⟩ := pz10_lanes n _ _ c2 c8 b2 b8
  have b10 : ∀ i < n, lane (pz10 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z)
      (pz8 (D3Ck2.oN n) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z)))) i ≤ 23682682 := fun i hi => by
    rw [l10 i hi]; exact p10_le (b2 i hi) (b8 i hi)
  obtain ⟨cs, ls⟩ := psin_lanes n _ _ _ _ _ hZ c2 c4 c6 c8 hz b2 b4 b6 b8
  obtain ⟨cc, lc⟩ := pcos_lanes n _ _ _ _ _ c2 c4 c6 c8 c10 b2 b4 b6 b8 b10
  have hv : ∀ l < n, lane (psin (D3Ck2.oN n) Z (pz2 (D3Ck2.oN n) Z) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z))
      (pz6 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z)))
      (pz8 (D3Ck2.oN n) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z)))) l = (sc28pZ (lane Z l)).1 ∧
      lane (pcos (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z))
        (pz6 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z)))
        (pz8 (D3Ck2.oN n) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z)))
        (pz10 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z) (pz8 (D3Ck2.oN n) (pz4 (D3Ck2.oN n) (pz2 (D3Ck2.oN n) Z))))) l =
        (sc28pZ (lane Z l)).2 := fun l hl => by
    rw [ls l hl, lc l hl, l10 l hl, l8 l hl, l6 l hl, l4 l hl, l2 l hl]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨cs, fun i hi => ?_⟩, ⟨cc, fun i hi => ?_⟩, hv⟩
  · rw [(hv i hi).1]; exact (sc28pZ_lt _ (hz i hi)).1
  · rw [(hv i hi).2]; exact (sc28pZ_lt _ (hz i hi)).2

theorem sc_one (z : ℕ) (hz : z ≤ QPI) : pS 1 z = (sc28pZ z).1 ∧ pC 1 z = (sc28pZ z).2 := by
  have hq : QPI = 210828714 := rfl
  have hz64 : z < 2 ^ 64 := by rw [hq] at hz; omega
  have h := sc_lanes 1 z (by simpa using hz64) (fun i hi => by
    obtain rfl : i = 0 := by omega
    rw [lane_zero z hz64]; exact hz)
  rw [oN_one] at h
  obtain ⟨fs, fc, hl⟩ := h
  obtain ⟨e1, e2⟩ := hl 0 one_pos
  rw [lane_zero _ (by simpa using fs.1), lane_zero z hz64] at e1
  rw [lane_zero _ (by simpa using fc.1), lane_zero z hz64] at e2
  exact ⟨e1, e2⟩

theorem red28_one_props (X : ℕ) (hX : X < 2 ^ 63) :
    (D3Ck2.red28 1 X).1 ≤ QPI ∧ ((D3Ck2.red28 1 X).2.1 = 0 ∨ (D3Ck2.red28 1 X).2.1 = 2 ^ 63 - 1) ∧
      ((D3Ck2.red28 1 X).2.2 = 0 ∨ (D3Ck2.red28 1 X).2.2 = 2 ^ 63 - 1) := by
  rw [red28_one X hX]
  dsimp only
  have eQ : QPI = 210828714 := rfl
  have eH : HPI_LO = 421657428 := rfl
  generalize (if HPI_LO < min (scArg X) (PI_LO + 1) then PI_LO - min (scArg X) (PI_LO + 1)
    else min (scArg X) (PI_LO + 1)) = x1
  refine ⟨?_, by split_ifs <;> simp, by split_ifs <;> simp⟩
  split_ifs <;> omega

theorem lane_sc28u (n X : ℕ) (hX : Fits n (2 ^ 63) X) :
    Fits n (2 ^ 63) (D3Ck2.sc28u (D3Ck2.oN n) X).1 ∧ Fits n (2 ^ 63) (D3Ck2.sc28u (D3Ck2.oN n) X).2 ∧
      ∀ l < n, lane (D3Ck2.sc28u (D3Ck2.oN n) X).1 l = (D3Ck2.sc28u 1 (lane X l)).1 ∧
        lane (D3Ck2.sc28u (D3Ck2.oN n) X).2 l = (D3Ck2.sc28u 1 (lane X l)).2 := by
  obtain ⟨zF, f1F, f2F, hr⟩ := lane_red28 n X hX
  have hzq : ∀ i < n, lane (D3Ck2.red28 (D3Ck2.oN n) X).1 i ≤ QPI := fun i hi => by
    rw [(hr i hi).1]; exact (red28_one_props _ (hX.2 i hi)).1
  obtain ⟨sF, cF, hsc⟩ := sc_lanes n _ zF.1 hzq
  have hm : ∀ i < n, (lane (D3Ck2.red28 (D3Ck2.oN n) X).2.1 i = 0 ∨
      lane (D3Ck2.red28 (D3Ck2.oN n) X).2.1 i = 2 ^ 63 - 1) ∧
      (lane (D3Ck2.red28 (D3Ck2.oN n) X).2.2 i = 0 ∨ lane (D3Ck2.red28 (D3Ck2.oN n) X).2.2 i = 2 ^ 63 - 1) :=
    fun i hi => by rw [(hr i hi).2.1, (hr i hi).2.2]; exact (red28_one_props _ (hX.2 i hi)).2
  have ho := lane_out28 n _ _ _ _ f1F.1 f2F.1 hm sF cF
  rw [sc28u_split]
  refine ⟨ho.1, ho.2.1, fun l hl => ?_⟩
  have hzl := (red28_one_props _ (hX.2 l hl)).1
  rw [(ho.2.2 l hl).1, (ho.2.2 l hl).2, sc28u_split 1 (lane X l), (hsc l hl).1, (hsc l hl).2, (hr l hl).1,
    (hr l hl).2.1, (hr l hl).2.2, (sc_one _ hzl).1, (sc_one _ hzl).2]
  exact ⟨rfl, rfl⟩

theorem land_m63_lanes (n A : ℕ) (_hA : A < 2 ^ (64 * n)) :
    Nat.land A (Nat.mul (D3Ck2.oN n) 9223372036854775807) < 2 ^ (64 * n) ∧
      ∀ l < n, lane (Nat.land A (Nat.mul (D3Ck2.oN n) 9223372036854775807)) l = lane A l % 2 ^ 63 := by
  have m := lane_mulc n 9223372036854775807 (by norm_num)
  refine ⟨Nat.and_lt_two_pow _ m.1, fun l hl => ?_⟩
  rw [lane_land, m.2 l hl, show (9223372036854775807 : ℕ) = 2 ^ 63 - 1 by norm_num]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem sv_cases (x : ℕ) : sv x = if x < 2 ^ 62 then -((2 ^ 62 - x : ℕ) : ℤ) else ((x - 2 ^ 62 : ℕ) : ℤ) := by
  unfold sv; split_ifs with h
  · rw [Nat.cast_sub (by omega)]; push_cast; ring
  · rw [Nat.cast_sub (by omega)]; push_cast; ring

theorem sabs_lanes (n X : ℕ) (hX : Fits n (2 ^ 63) X) :
    Fits n 2 (D3Ck2.sabs (D3Ck2.oN n) X).1 ∧ Fits n (2 ^ 63) (D3Ck2.sabs (D3Ck2.oN n) X).2 ∧
      ∀ l < n, lane (D3Ck2.sabs (D3Ck2.oN n) X).1 l = (if lane X l < 2 ^ 62 then 1 else 0) ∧
        lane (D3Ck2.sabs (D3Ck2.oN n) X).2 l =
          (if lane X l < 2 ^ 62 then 2 ^ 62 - lane X l else lane X l - 2 ^ 62) := by
  have c62 := lane_mulc n 4611686018427387904 (by norm_num)
  have c63 := lane_mulc n 9223372036854775808 (by norm_num)
  have c3 := lane_mulc n 13835058055282163712 (by norm_num)
  have hsg := lane_plt n X _ hX ⟨c62.1, fun i hi => by rw [c62.2 i hi]; norm_num⟩
  have a1 := lane_add n X _ hX.1 c63.1 (fun i hi => by rw [c63.2 i hi]; have := hX.2 i hi; omega)
  have a2 := lane_sub n _ _ a1.1 c62.1 (fun i hi => by rw [a1.2 i hi, c63.2 i hi, c62.2 i hi]; omega)
  have a3 := land_m63_lanes n _ a2.1
  have b1 := lane_sub n _ X c3.1 hX.1 (fun i hi => by rw [c3.2 i hi]; have := hX.2 i hi; omega)
  have b2 := land_m63_lanes n _ b1.1
  have hAl : ∀ i < n, lane (Nat.land (Nat.sub (Nat.add X (Nat.mul (D3Ck2.oN n) 9223372036854775808))
      (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (Nat.mul (D3Ck2.oN n) 9223372036854775807)) i =
      if lane X i < 2 ^ 62 then lane X i + 2 ^ 62 else lane X i - 2 ^ 62 := fun i hi => by
    rw [a3.2 i hi, a2.2 i hi, a1.2 i hi, c63.2 i hi, c62.2 i hi]
    have := hX.2 i hi
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show lane X i + 9223372036854775808 - 4611686018427387904 = (lane X i - 2 ^ 62) + 2 ^ 63 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hBl : ∀ i < n, lane X i < 2 ^ 62 → lane (Nat.land (Nat.sub (Nat.mul (D3Ck2.oN n) 13835058055282163712) X)
      (Nat.mul (D3Ck2.oN n) 9223372036854775807)) i = 2 ^ 62 - lane X i := fun i hi h => by
    rw [b2.2 i hi, b1.2 i hi, c3.2 i hi,
      show 13835058055282163712 - lane X i = (2 ^ 62 - lane X i) + 2 ^ 63 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have hsgF : Fits n 2 (Lanes24.plt (D3Ck2.oN n) X (Nat.mul (D3Ck2.oN n) 4611686018427387904)) := hsg.1
  have hsgl : ∀ l < n, lane (Lanes24.plt (D3Ck2.oN n) X (Nat.mul (D3Ck2.oN n) 4611686018427387904)) l =
      if lane X l < 2 ^ 62 then 1 else 0 := fun l hl => by
    rw [hsg.2 l hl, c62.2 l hl, show (4611686018427387904 : ℕ) = 2 ^ 62 by norm_num]
  have pm := lane_pmask n _ hsgF
  have e2 : (D3Ck2.sabs (D3Ck2.oN n) X).2 =
      Lanes24.psel (Lanes24.pmask (Lanes24.plt (D3Ck2.oN n) X (Nat.mul (D3Ck2.oN n) 4611686018427387904)))
        (Nat.land (Nat.sub (Nat.mul (D3Ck2.oN n) 13835058055282163712) X) (Nat.mul (D3Ck2.oN n) 9223372036854775807))
        (Nat.land (Nat.sub (Nat.add X (Nat.mul (D3Ck2.oN n) 9223372036854775808))
          (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (Nat.mul (D3Ck2.oN n) 9223372036854775807)) := rfl
  have hv : ∀ l < n, lane (D3Ck2.sabs (D3Ck2.oN n) X).2 l =
      (if lane X l < 2 ^ 62 then 2 ^ 62 - lane X l else lane X l - 2 ^ 62) := fun l hl => by
    have hx := hX.2 l hl
    rw [e2, lane_psel, pm.2 l hl, hsgl l hl]
    by_cases h : lane X l < 2 ^ 62
    · rw [if_pos h, if_pos h, one_mul, psel_full _ _ (by rw [b2.2 l hl]; exact Nat.mod_lt _ (by norm_num))
        (by rw [a3.2 l hl]; exact Nat.mod_lt _ (by norm_num)), hBl l hl h]
    · rw [if_neg h, if_neg h, zero_mul, psel_zero, hAl l hl, if_neg h]
  refine ⟨hsgF, ⟨?_, fun i hi => ?_⟩, fun l hl => ⟨hsgl l hl, hv l hl⟩⟩
  · rw [e2]; exact psel_lt _ _ _ _ b2.1 a3.1
  · rw [hv i hi]; have := hX.2 i hi; split_ifs <;> omega

theorem sout_lanes (n F G : ℕ) (hF : Fits n 2 F) (hG : Fits n (2 ^ 62) G) :
    Lanes24.psel (Lanes24.pmask F) (Nat.sub (Nat.mul (D3Ck2.oN n) 4611686018427387904) G)
      (Nat.add (Nat.mul (D3Ck2.oN n) 4611686018427387904) G) < 2 ^ (64 * n) ∧
      ∀ l < n, lane (Lanes24.psel (Lanes24.pmask F) (Nat.sub (Nat.mul (D3Ck2.oN n) 4611686018427387904) G)
        (Nat.add (Nat.mul (D3Ck2.oN n) 4611686018427387904) G)) l =
          if lane F l = 1 then 2 ^ 62 - lane G l else 2 ^ 62 + lane G l := by
  have c62 := lane_mulc n 4611686018427387904 (by norm_num)
  have s := lane_sub n _ G c62.1 hG.1 (fun i hi => by rw [c62.2 i hi]; have := hG.2 i hi; omega)
  have a := lane_add n _ G c62.1 hG.1 (fun i hi => by rw [c62.2 i hi]; have := hG.2 i hi; omega)
  have pm := lane_pmask n F hF
  refine ⟨psel_lt _ _ _ _ s.1 a.1, fun l hl => ?_⟩
  have hg := hG.2 l hl
  rw [lane_psel, pm.2 l hl, s.2 l hl, a.2 l hl, c62.2 l hl,
    show lane F l * (2 ^ 63 - 1) = Lanes24.pmask (lane F l) by unfold Lanes24.pmask; norm_num,
    psel_pmask _ _ _ (hF.2 l hl) (by omega) (by omega), show (4611686018427387904 : ℕ) = 2 ^ 62 by norm_num]

theorem fits_of_sv (n X b : ℕ) (hX : X < 2 ^ (64 * n)) (hb : b ≤ 62) (h : ∀ i < n, |sv (lane X i)| < 2 ^ b) :
    Fits n (2 ^ 63) X := by
  refine ⟨hX, fun i hi => ?_⟩
  have h1 := (abs_lt.mp (h i hi)).2
  have h2 : (2 : ℤ) ^ b ≤ 2 ^ 62 := pow_le_pow_right₀ (by norm_num) hb
  unfold sv at h1
  have : (lane X i : ℤ) < 2 ^ 63 := by linarith
  exact_mod_cast this

theorem mag_eq (x : ℕ) : (((if x < 2 ^ 62 then 2 ^ 62 - x else x - 2 ^ 62 : ℕ)) : ℤ) = |sv x| := by
  rw [sv_cases]; split_ifs with h
  · rw [abs_neg, abs_of_nonneg (by positivity)]
  · rw [abs_of_nonneg (by positivity)]

theorem toNat_pos (q : ℕ) : ((q : ℤ) + 2 ^ 62).toNat = 2 ^ 62 + q := by omega

theorem toNat_neg (q : ℕ) : (-(q : ℤ) + 2 ^ 62).toNat = 2 ^ 62 - q := by omega

theorem lane_smx (K n X Y : ℕ) (hK : 1 ≤ K ∧ K ≤ 63) (hX : Fits n (2 ^ 63) X) (hY : Fits n (2 ^ 63) Y)
    (hb : ∀ i < n, |sv (lane X i)| < 2 ^ (64 - K) ∧ |sv (lane Y i)| < 2 ^ K ∧
      |sv (lane X i) * sv (lane Y i)| < 2 ^ 61) :
    D3Ck2.smx K (D3Ck2.oN n) X Y < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.smx K (D3Ck2.oN n) X Y) l = (sv (lane X l) * sv (lane Y l) + 2 ^ 62).toNat := by
  obtain ⟨sx, mx, hxl⟩ := sabs_lanes n X hX
  obtain ⟨sy, my, hyl⟩ := sabs_lanes n Y hY
  have hmx : ∀ i < n, ((lane (D3Ck2.sabs (D3Ck2.oN n) X).2 i : ℕ) : ℤ) = |sv (lane X i)| := fun i hi => by
    rw [(hxl i hi).2]; exact mag_eq _
  have hmy : ∀ i < n, ((lane (D3Ck2.sabs (D3Ck2.oN n) Y).2 i : ℕ) : ℤ) = |sv (lane Y i)| := fun i hi => by
    rw [(hyl i hi).2]; exact mag_eq _
  have p := lane_mulF K n (D3Ck2.sabs (D3Ck2.oN n) X).2 (D3Ck2.sabs (D3Ck2.oN n) Y).2 (by omega)
    ⟨mx.1, fun i hi => by
      have : ((lane (D3Ck2.sabs (D3Ck2.oN n) X).2 i : ℕ) : ℤ) < 2 ^ (64 - K) := by rw [hmx i hi]; exact (hb i hi).1
      exact_mod_cast this⟩
    ⟨my.1, fun i hi => by
      have : ((lane (D3Ck2.sabs (D3Ck2.oN n) Y).2 i : ℕ) : ℤ) < 2 ^ K := by rw [hmy i hi]; exact (hb i hi).2.1
      exact_mod_cast this⟩
  have hp : ∀ i < n, ((lane (Lanes24.mulF K (D3Ck2.oN n) (D3Ck2.sabs (D3Ck2.oN n) X).2
      (D3Ck2.sabs (D3Ck2.oN n) Y).2) i : ℕ) : ℤ) = |sv (lane X i) * sv (lane Y i)| := fun i hi => by
    rw [p.2 i hi]; push_cast; rw [hmx i hi, hmy i hi, abs_mul]
  have hF : Fits n 2 (Nat.xor (D3Ck2.sabs (D3Ck2.oN n) X).1 (D3Ck2.sabs (D3Ck2.oN n) Y).1) :=
    ⟨Nat.xor_lt_two_pow sx.1 sy.1, fun i hi => by
      rw [lane_xor, (hxl i hi).1, (hyl i hi).1]; split_ifs <;> decide⟩
  have hG : Fits n (2 ^ 62) (Lanes24.mulF K (D3Ck2.oN n) (D3Ck2.sabs (D3Ck2.oN n) X).2
      (D3Ck2.sabs (D3Ck2.oN n) Y).2) := ⟨p.1, fun i hi => by
    have : ((lane (Lanes24.mulF K (D3Ck2.oN n) (D3Ck2.sabs (D3Ck2.oN n) X).2
        (D3Ck2.sabs (D3Ck2.oN n) Y).2) i : ℕ) : ℤ) < 2 ^ 62 := by
      rw [hp i hi]; linarith [(hb i hi).2.2]
    exact_mod_cast this⟩
  have o := sout_lanes n _ _ hF hG
  refine ⟨o.1, fun l hl => ?_⟩
  show lane (Lanes24.psel _ _ _) l = _
  rw [o.2 l hl, lane_xor, (hxl l hl).1, (hyl l hl).1]
  have e := hp l hl
  generalize lane (Lanes24.mulF K (D3Ck2.oN n) (D3Ck2.sabs (D3Ck2.oN n) X).2
    (D3Ck2.sabs (D3Ck2.oN n) Y).2) l = q at e ⊢
  have sxe : sv (lane X l) < 0 ↔ lane X l < 2 ^ 62 := by unfold sv; omega
  have sye : sv (lane Y l) < 0 ↔ lane Y l < 2 ^ 62 := by unfold sv; omega
  by_cases h1 : lane X l < 2 ^ 62 <;> by_cases h2 : lane Y l < 2 ^ 62
  · have hs : 0 ≤ sv (lane X l) * sv (lane Y l) :=
      mul_nonneg_of_nonpos_of_nonpos (le_of_lt (sxe.2 h1)) (le_of_lt (sye.2 h2))
    rw [abs_of_nonneg hs] at e
    rw [if_pos h1, if_pos h2, show Nat.xor 1 1 = 0 by decide, if_neg (by decide), ← e, toNat_pos]
  · have hs : sv (lane X l) * sv (lane Y l) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt (sxe.2 h1)) (not_lt.mp (mt sye.1 h2))
    rw [abs_of_nonpos hs] at e
    rw [if_pos h1, if_neg h2, show Nat.xor 1 0 = 1 by decide, if_pos rfl,
      show sv (lane X l) * sv (lane Y l) = -(q : ℤ) by rw [e]; ring, toNat_neg]
  · have hs : sv (lane X l) * sv (lane Y l) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (not_lt.mp (mt sxe.1 h1)) (le_of_lt (sye.2 h2))
    rw [abs_of_nonpos hs] at e
    rw [if_neg h1, if_pos h2, show Nat.xor 0 1 = 1 by decide, if_pos rfl,
      show sv (lane X l) * sv (lane Y l) = -(q : ℤ) by rw [e]; ring, toNat_neg]
  · have hs : 0 ≤ sv (lane X l) * sv (lane Y l) :=
      mul_nonneg (not_lt.mp (mt sxe.1 h1)) (not_lt.mp (mt sye.1 h2))
    rw [abs_of_nonneg hs] at e
    rw [if_neg h1, if_neg h2, show Nat.xor 0 0 = 0 by decide, if_neg (by decide), ← e, toNat_pos]

theorem srdF_val (x : ℕ) (h3 : |sv x| < 2 ^ 61) :
    (if (if x < 2 ^ 62 then 1 else 0) = 1 then
      2 ^ 62 - ((if x < 2 ^ 62 then 2 ^ 62 - x else x - 2 ^ 62) + (if x < 2 ^ 62 then 1 else 0) * 268435455) / 2 ^ 28
    else
      2 ^ 62 + ((if x < 2 ^ 62 then 2 ^ 62 - x else x - 2 ^ 62) + (if x < 2 ^ 62 then 1 else 0) * 268435455) / 2 ^ 28) =
      (sv x / 2 ^ 28 + 2 ^ 62).toNat := by
  rw [sv_cases] at h3 ⊢
  by_cases h1 : x < 2 ^ 62
  · simp only [h1, if_true, abs_neg, Nat.abs_cast] at h3 ⊢
    generalize 2 ^ 62 - x = m at h3 ⊢
    omega
  · simp only [h1, if_false, Nat.abs_cast] at h3 ⊢
    rw [if_neg (show ¬ (0 : ℕ) = 1 by decide)]
    generalize x - 2 ^ 62 = m at h3 ⊢
    omega

theorem srdC_val (x : ℕ) (h3 : |sv x| < 2 ^ 61) :
    (if (if x < 2 ^ 62 then 1 else 0) = 1 then
      2 ^ 62 - ((if x < 2 ^ 62 then 2 ^ 62 - x else x - 2 ^ 62) + (1 - if x < 2 ^ 62 then 1 else 0) * 268435455) / 2 ^ 28
    else
      2 ^ 62 + ((if x < 2 ^ 62 then 2 ^ 62 - x else x - 2 ^ 62) + (1 - if x < 2 ^ 62 then 1 else 0) * 268435455) / 2 ^ 28) =
      (-((-sv x) / 2 ^ 28) + 2 ^ 62).toNat := by
  rw [sv_cases] at h3 ⊢
  by_cases h1 : x < 2 ^ 62
  · simp only [h1, if_true, abs_neg, Nat.abs_cast] at h3 ⊢
    generalize 2 ^ 62 - x = m at h3 ⊢
    omega
  · simp only [h1, if_false, Nat.abs_cast] at h3 ⊢
    rw [if_neg (show ¬ (0 : ℕ) = 1 by decide)]
    generalize x - 2 ^ 62 = m at h3 ⊢
    omega

theorem sshl_val (x : ℕ) (h3 : |sv x| < 2 ^ 33) :
    (if (if x < 2 ^ 62 then 1 else 0) = 1 then
      2 ^ 62 - (if x < 2 ^ 62 then 2 ^ 62 - x else x - 2 ^ 62) * 2 ^ 28
    else
      2 ^ 62 + (if x < 2 ^ 62 then 2 ^ 62 - x else x - 2 ^ 62) * 2 ^ 28) =
      (sv x * 2 ^ 28 + 2 ^ 62).toNat := by
  rw [sv_cases] at h3 ⊢
  by_cases h1 : x < 2 ^ 62
  · simp only [h1, if_true, abs_neg, Nat.abs_cast] at h3 ⊢
    generalize 2 ^ 62 - x = m at h3 ⊢
    omega
  · simp only [h1, if_false, Nat.abs_cast] at h3 ⊢
    rw [if_neg (show ¬ (0 : ℕ) = 1 by decide)]
    generalize x - 2 ^ 62 = m at h3 ⊢
    omega

theorem lane_srdF (n X : ℕ) (hX : X < 2 ^ (64 * n)) (hb : ∀ i < n, |sv (lane X i)| < 2 ^ 61) :
    D3Ck2.srdF (D3Ck2.oN n) X < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.srdF (D3Ck2.oN n) X) l = (sv (lane X l) / 2 ^ 28 + 2 ^ 62).toNat := by
  have hXF := fits_of_sv n X 61 hX (by norm_num) hb
  obtain ⟨sx, mx, hxl⟩ := sabs_lanes n X hXF
  have t1 := lane_mul n _ 268435455 sx.1 (fun i hi => by have := sx.2 i hi; omega)
  have t2 := lane_add n _ _ mx.1 t1.1 (fun i hi => by
    rw [t1.2 i hi]; have := mx.2 i hi; have := sx.2 i hi; omega)
  have hmg := lane_shr n (Nat.add (D3Ck2.sabs (D3Ck2.oN n) X).2
    (Nat.mul (D3Ck2.sabs (D3Ck2.oN n) X).1 268435455)) 28 (by norm_num)
  rw [show (2 : ℕ) ^ (64 - 28) - 1 = 68719476735 by norm_num] at hmg
  have hG : Fits n (2 ^ 62) (Nat.land (Nat.shiftRight (Nat.add (D3Ck2.sabs (D3Ck2.oN n) X).2
      (Nat.mul (D3Ck2.sabs (D3Ck2.oN n) X).1 268435455)) 28) (Nat.mul (D3Ck2.oN n) 68719476735)) :=
    ⟨hmg.1, fun i hi => by
      rw [hmg.2 i hi, t2.2 i hi, t1.2 i hi]; have := mx.2 i hi; have := sx.2 i hi; omega⟩
  have o := sout_lanes n _ _ sx hG
  refine ⟨o.1, fun l hl => ?_⟩
  show lane (Lanes24.psel _ _ _) l = _
  rw [o.2 l hl, hmg.2 l hl, t2.2 l hl, t1.2 l hl, (hxl l hl).1, (hxl l hl).2]
  exact srdF_val _ (hb l hl)

theorem lane_srdC (n X : ℕ) (hX : X < 2 ^ (64 * n)) (hb : ∀ i < n, |sv (lane X i)| < 2 ^ 61) :
    D3Ck2.srdC (D3Ck2.oN n) X < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.srdC (D3Ck2.oN n) X) l = (-((-sv (lane X l)) / 2 ^ 28) + 2 ^ 62).toNat := by
  have hXF := fits_of_sv n X 61 hX (by norm_num) hb
  obtain ⟨sx, mx, hxl⟩ := sabs_lanes n X hXF
  have t0 := lane_sub n _ _ (oN_lt n) sx.1 (fun i hi => by rw [lane_oN n i hi]; have := sx.2 i hi; omega)
  have t1 := lane_mul n _ 268435455 t0.1 (fun i hi => by
    rw [t0.2 i hi, lane_oN n i hi]; have := sx.2 i hi; omega)
  have t2 := lane_add n _ _ mx.1 t1.1 (fun i hi => by
    rw [t1.2 i hi, t0.2 i hi, lane_oN n i hi]; have := mx.2 i hi; have := sx.2 i hi; omega)
  have hmg := lane_shr n (Nat.add (D3Ck2.sabs (D3Ck2.oN n) X).2
    (Nat.mul (Nat.sub (D3Ck2.oN n) (D3Ck2.sabs (D3Ck2.oN n) X).1) 268435455)) 28 (by norm_num)
  rw [show (2 : ℕ) ^ (64 - 28) - 1 = 68719476735 by norm_num] at hmg
  have hG : Fits n (2 ^ 62) (Nat.land (Nat.shiftRight (Nat.add (D3Ck2.sabs (D3Ck2.oN n) X).2
      (Nat.mul (Nat.sub (D3Ck2.oN n) (D3Ck2.sabs (D3Ck2.oN n) X).1) 268435455)) 28)
      (Nat.mul (D3Ck2.oN n) 68719476735)) :=
    ⟨hmg.1, fun i hi => by
      rw [hmg.2 i hi, t2.2 i hi, t1.2 i hi, t0.2 i hi, lane_oN n i hi]; have := mx.2 i hi; have := sx.2 i hi
      omega⟩
  have o := sout_lanes n _ _ sx hG
  refine ⟨o.1, fun l hl => ?_⟩
  show lane (Lanes24.psel _ _ _) l = _
  rw [o.2 l hl, hmg.2 l hl, t2.2 l hl, t1.2 l hl, t0.2 l hl, lane_oN n l hl, (hxl l hl).1, (hxl l hl).2]
  exact srdC_val _ (hb l hl)

theorem lane_sshl (n X : ℕ) (hX : X < 2 ^ (64 * n)) (hb : ∀ i < n, |sv (lane X i)| < 2 ^ 33) :
    D3Ck2.sshl (D3Ck2.oN n) X < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.sshl (D3Ck2.oN n) X) l = (sv (lane X l) * 2 ^ 28 + 2 ^ 62).toNat := by
  have hXF := fits_of_sv n X 33 hX (by norm_num) hb
  obtain ⟨sx, mx, hxl⟩ := sabs_lanes n X hXF
  have hm : ∀ i < n, lane (D3Ck2.sabs (D3Ck2.oN n) X).2 i < 2 ^ 33 := fun i hi => by
    have : ((lane (D3Ck2.sabs (D3Ck2.oN n) X).2 i : ℕ) : ℤ) < 2 ^ 33 := by
      rw [(hxl i hi).2, mag_eq]; exact hb i hi
    exact_mod_cast this
  have t := lane_shl n _ 28 mx.1 (fun i hi => by have := hm i hi; norm_num; omega)
  have hG : Fits n (2 ^ 62) (Nat.shiftLeft (D3Ck2.sabs (D3Ck2.oN n) X).2 28) :=
    ⟨t.1, fun i hi => by rw [t.2 i hi]; have := hm i hi; omega⟩
  have o := sout_lanes n _ _ sx hG
  refine ⟨o.1, fun l hl => ?_⟩
  show lane (Lanes24.psel _ _ _) l = _
  rw [o.2 l hl, t.2 l hl, (hxl l hl).1, (hxl l hl).2]
  exact sshl_val _ (hb l hl)

end D3Ck2Spec
