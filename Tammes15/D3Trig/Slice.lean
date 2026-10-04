import Tammes15.D3Kernel.Pent

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel Tammes15.D3Kernel.Pent

structure Batch where
  N : ℕ
  G0 : ℕ
  G1 : ℕ
  G2 : ℕ
  G3 : ℕ

def BatchClaims (C : ℕ → ℕ → ℕ → ℕ → Prop) (B : Batch) : Prop :=
  ∀ i < B.N, C (lane B.G0 i) (lane B.G1 i) (lane B.G2 i) (lane B.G3 i)

def ProgOKG (Dom C : ℕ → ℕ → ℕ → ℕ → Prop) (prog : Prog) : Prop :=
  ∀ (n F0 F1 F2 F3 : ℕ) (hs : List ℕ) (v : ℕ),
    (∀ i < n, Dom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) →
      Nat.beq (prog (oN n) F0 F1 F2 F3 hs) v = true → ∀ l < n, lane v l = 1 →
        C (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)

def domAll (dom : ℕ → ℕ → ℕ → ℕ → Bool) (D : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  @Nat.rec (fun _ => ℕ → ℕ → ℕ → ℕ → Bool)
    (fun F0 F1 F2 F3 => dom (Nat.land F0 18446744073709551615) (Nat.land F1 18446744073709551615)
      (Nat.land F2 18446744073709551615) (Nat.land F3 18446744073709551615))
    (fun d ih F0 F1 F2 F3 =>
      @Bool.rec (fun _ => Bool) false
        (ih (Nat.shiftRight F0 (Nat.shiftLeft 1 (Nat.add d 6))) (Nat.shiftRight F1 (Nat.shiftLeft 1 (Nat.add d 6)))
          (Nat.shiftRight F2 (Nat.shiftLeft 1 (Nat.add d 6))) (Nat.shiftRight F3 (Nat.shiftLeft 1 (Nat.add d 6))))
        (ih (Nat.land F0 (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add d 6))) 1))
          (Nat.land F1 (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add d 6))) 1))
          (Nat.land F2 (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add d 6))) 1))
          (Nat.land F3 (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add d 6))) 1))))
    D

def batchOK (prog : Prog) (dom : ℕ → ℕ → ℕ → ℕ → Bool) (D : ℕ) (B : Batch) (hs : List ℕ) : Bool :=
  Nat.beq B.N (Nat.shiftLeft 1 D) && domAll dom D B.G0 B.G1 B.G2 B.G3 &&
    Nat.beq (prog (oN B.N) B.G0 B.G1 B.G2 B.G3 hs) (oN B.N)

inductive BT where
  | leaf (B : Batch)
  | node (l r : BT)

noncomputable def BT.get (t : BT) : ℕ → ℕ → Batch :=
  @BT.rec (fun _ => ℕ → ℕ → Batch) (fun B _ _ => B)
    (fun _ _ gl gr d b => @Nat.rec (fun _ => Batch) (gl 0 b)
      (fun d' _ => @Bool.rec (fun _ => Batch) (gr d' b) (gl d' b) (Nat.beq (Nat.land (Nat.shiftRight b d') 1) 0)) d)
    t

noncomputable def BT.All (P : Batch → Prop) (t : BT) : Prop :=
  @BT.rec (fun _ => Prop) (fun B => P B) (fun _ _ pl pr => pl ∧ pr) t

def hint0 (hs : List ℕ) : ℕ := @List.rec ℕ (fun _ => ℕ) 0 (fun a _ _ => a) hs
def hint1 (hs : List ℕ) : ℕ := @List.rec ℕ (fun _ => ℕ) 0 (fun _ t _ => hint0 t) hs

def sliceAt (B : Batch) (s M O F0 F1 F2 F3 : ℕ) : ℕ :=
  @Bool.rec (fun _ => ℕ) 0 O
    (Nat.ble (Nat.shiftLeft (Nat.add M 1) s) (Nat.shiftLeft 1 (Nat.shiftLeft B.N 6)) &&
      Nat.beq (Nat.land (Nat.shiftRight B.G0 s) M) F0 && Nat.beq (Nat.land (Nat.shiftRight B.G1 s) M) F1 &&
      Nat.beq (Nat.land (Nat.shiftRight B.G2 s) M) F2 && Nat.beq (Nat.land (Nat.shiftRight B.G3 s) M) F3)

noncomputable def sliceProg (t : BT) (Dt : ℕ) : Prog :=
  fun O F0 F1 F2 F3 hs =>
    @Bool.rec (fun _ => ℕ)
      (sliceAt (t.get Dt (hint0 hs)) (Nat.shiftLeft (hint1 hs) 6) (Nat.mul O 18446744073709551615) O F0 F1 F2 F3)
      0 (Nat.beq O 0)

theorem sl_eq_mul (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem sr_eq_div (a b : ℕ) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b

theorem land_pow_sub_one (a k : ℕ) : Nat.land a (Nat.sub (2 ^ k) 1) = a % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod a k

theorem sl_half (d : ℕ) : Nat.shiftLeft 1 (Nat.add d 6) = 64 * 2 ^ d := by
  rw [sl_eq_mul, one_mul, show Nat.add d 6 = d + 6 from rfl, pow_add]
  ring

theorem lane_mod (x m i : ℕ) (hi : i < m) : lane (x % 2 ^ (64 * m)) i = lane x i := by
  unfold lane
  obtain ⟨j, rfl⟩ : ∃ j, m = i + (j + 1) := ⟨m - i - 1, by omega⟩
  rw [show 64 * (i + (j + 1)) = 64 * i + 64 * (j + 1) by ring, pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : 64 ≤ 64 * (j + 1)))]

theorem lane_div (x o i : ℕ) : lane (x / 2 ^ (64 * o)) i = lane x (o + i) := by
  unfold lane
  rw [Nat.div_div_eq_div_mul, ← pow_add, show 64 * o + 64 * i = 64 * (o + i) by ring]

theorem lane_land_half (F d i : ℕ) (hi : i < 2 ^ d) :
    lane (Nat.land F (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add d 6))) 1)) i = lane F i := by
  rw [sl_half, sl_eq_mul, one_mul, land_pow_sub_one]
  exact lane_mod F (2 ^ d) i hi

theorem lane_shiftRight_half (F d i : ℕ) :
    lane (Nat.shiftRight F (Nat.shiftLeft 1 (Nat.add d 6))) i = lane F (i + 2 ^ d) := by
  rw [sl_half, sr_eq_div, lane_div, add_comm]

theorem land64_eq_lane0 (F : ℕ) : Nat.land F 18446744073709551615 = lane F 0 := by
  have h : Nat.land F 18446744073709551615 = F % 2 ^ 64 := land_pow_sub_one F 64
  rw [h]
  simp [lane]

theorem oN_mul (n : ℕ) : oN n * 18446744073709551615 = 2 ^ (64 * n) - 1 := by
  have hs : Nat.shiftLeft 1 (Nat.shiftLeft n 6) = 2 ^ (64 * n) := by
    rw [sl_eq_mul n, sl_eq_mul, one_mul]
    congr 1
    ring
  have hd : 18446744073709551615 ∣ 2 ^ (64 * n) - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ 64) 1 n
    rw [one_pow, ← pow_mul, show (2 : ℕ) ^ 64 - 1 = 18446744073709551615 by norm_num] at h
    exact h
  unfold oN
  rw [hs]
  exact Nat.div_mul_cancel hd

theorem lane_slice (G o n l : ℕ) (hl : l < n) :
    lane (Nat.land (Nat.shiftRight G (Nat.shiftLeft o 6)) (2 ^ (64 * n) - 1)) l = lane G (o + l) := by
  rw [show Nat.shiftLeft o 6 = 64 * o by rw [sl_eq_mul]; ring, sr_eq_div]
  rw [show Nat.land (G / 2 ^ (64 * o)) (2 ^ (64 * n) - 1) = G / 2 ^ (64 * o) % 2 ^ (64 * n) from
    land_pow_sub_one _ _]
  rw [lane_mod _ _ _ hl, lane_div]

theorem ble_bound (n o N : ℕ)
    (h : Nat.ble (Nat.shiftLeft (2 ^ (64 * n)) (Nat.shiftLeft o 6)) (Nat.shiftLeft 1 (Nat.shiftLeft N 6)) = true) :
    n + o ≤ N := by
  have h' := Nat.le_of_ble_eq_true h
  rw [sl_eq_mul o, sl_eq_mul N, sl_eq_mul, sl_eq_mul, one_mul, ← pow_add] at h'
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h'
  rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at h2
  omega

theorem oN_beq_zero (n : ℕ) (hn : 0 < n) : Nat.beq (oN n) 0 = false := by
  have h := oN_mul n
  have h2 : 2 ≤ 2 ^ (64 * n) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : oN n ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    omega
  cases hb : Nat.beq (oN n) 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) hne

theorem sliceAt_cases (B : Batch) (s M O F0 F1 F2 F3 v : ℕ) (hv : sliceAt B s M O F0 F1 F2 F3 = v)
    (hv0 : v ≠ 0) :
    v = O ∧ Nat.shiftLeft (M + 1) s ≤ Nat.shiftLeft 1 (Nat.shiftLeft B.N 6) ∧
      Nat.land (Nat.shiftRight B.G0 s) M = F0 ∧ Nat.land (Nat.shiftRight B.G1 s) M = F1 ∧
      Nat.land (Nat.shiftRight B.G2 s) M = F2 ∧ Nat.land (Nat.shiftRight B.G3 s) M = F3 := by
  have key : ∀ c : Bool, @Bool.rec (fun _ => ℕ) 0 O c = v → c = true ∧ O = v := by
    intro c h1
    cases c
    · exact absurd h1.symm hv0
    · exact ⟨rfl, h1⟩
  unfold sliceAt at hv
  obtain ⟨hc, hO⟩ := key _ hv
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  exact ⟨hO.symm, h1, h2, h3, h4, h5⟩

theorem domAll_sound {dom : ℕ → ℕ → ℕ → ℕ → Bool} (D : ℕ) {F0 F1 F2 F3 : ℕ}
    (h : domAll dom D F0 F1 F2 F3 = true) :
    ∀ i < 2 ^ D, dom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i) = true := by
  induction D generalizing F0 F1 F2 F3 with
  | zero =>
    intro i hi
    have hi0 : i = 0 := by
      have : i < 1 := by simpa using hi
      omega
    subst hi0
    rw [← land64_eq_lane0, ← land64_eq_lane0, ← land64_eq_lane0, ← land64_eq_lane0]
    exact h
  | succ d ih =>
    intro i hi
    have key : ∀ b1 b2 : Bool, @Bool.rec (fun _ => Bool) false b1 b2 = true → b1 = true ∧ b2 = true := by
      intro b1 b2
      cases b1 <;> cases b2 <;> decide
    have h' : @Bool.rec (fun _ => Bool) false
        (domAll dom d (Nat.shiftRight F0 (Nat.shiftLeft 1 (Nat.add d 6)))
          (Nat.shiftRight F1 (Nat.shiftLeft 1 (Nat.add d 6))) (Nat.shiftRight F2 (Nat.shiftLeft 1 (Nat.add d 6)))
          (Nat.shiftRight F3 (Nat.shiftLeft 1 (Nat.add d 6))))
        (domAll dom d (Nat.land F0 (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add d 6))) 1))
          (Nat.land F1 (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add d 6))) 1))
          (Nat.land F2 (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add d 6))) 1))
          (Nat.land F3 (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add d 6))) 1))) = true := h
    obtain ⟨hH, hL⟩ := key _ _ h'
    by_cases hlt : i < 2 ^ d
    · have h2 := ih hL i hlt
      rwa [lane_land_half F0 d i hlt, lane_land_half F1 d i hlt, lane_land_half F2 d i hlt,
        lane_land_half F3 d i hlt] at h2
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 ^ d := ⟨i - 2 ^ d, by omega⟩
      have hj : j < 2 ^ d := by
        rw [pow_succ] at hi
        omega
      have h2 := ih hH j hj
      rwa [lane_shiftRight_half, lane_shiftRight_half, lane_shiftRight_half, lane_shiftRight_half] at h2

theorem batchClaims_of_ok {Dom C : ℕ → ℕ → ℕ → ℕ → Prop} {dom : ℕ → ℕ → ℕ → ℕ → Bool}
    (hdom : ∀ {a b c e : ℕ}, dom a b c e = true → Dom a b c e) {prog : Prog} (hp : ProgOKG Dom C prog)
    {D : ℕ} {B : Batch} {hs : List ℕ} (h : batchOK prog dom D B hs = true) : BatchClaims C B := by
  unfold batchOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hN, hd⟩, hv⟩ := h
  have hN' : B.N = 2 ^ D := by
    rw [Nat.eq_of_beq_eq_true hN, sl_eq_mul, one_mul]
  intro i hi
  have hdom' : ∀ j < B.N, Dom (lane B.G0 j) (lane B.G1 j) (lane B.G2 j) (lane B.G3 j) :=
    fun j hj => hdom (domAll_sound D hd j (by rw [← hN']; exact hj))
  exact hp B.N B.G0 B.G1 B.G2 B.G3 hs (oN B.N) hdom' hv i hi (lane_oN B.N i hi)

theorem batchClaims_nil (C : ℕ → ℕ → ℕ → ℕ → Prop) : BatchClaims C ⟨0, 0, 0, 0, 0⟩ :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem BT.all_get {P : Batch → Prop} {t : BT} (h : t.All P) (d b : ℕ) : P (t.get d b) := by
  have key : ∀ t : BT, t.All P → ∀ d, P (t.get d b) := by
    intro t
    induction t with
    | leaf B =>
      intro h _
      exact h
    | node l r ihl ihr =>
      intro h d
      have h' : l.All P ∧ r.All P := h
      cases d with
      | zero => exact ihl h'.1 0
      | succ d' =>
        show P (@Bool.rec (fun _ => Batch) (r.get d' b) (l.get d' b)
          (Nat.beq (Nat.land (Nat.shiftRight b d') 1) 0))
        cases Nat.beq (Nat.land (Nat.shiftRight b d') 1) 0
        · exact ihr h'.2 d'
        · exact ihl h'.1 d'
  exact key t h d

theorem sliceProg_ok {Dom C : ℕ → ℕ → ℕ → ℕ → Prop} {t : BT} (Dt : ℕ) (ht : t.All (BatchClaims C)) :
    ProgOKG Dom C (sliceProg t Dt) := by
  intro n F0 F1 F2 F3 hs v _ hv l hl h1
  have hn : 0 < n := by omega
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [lane] at h1
  have hz : Nat.beq (oN n) 0 = false := oN_beq_zero n hn
  have hs' : sliceAt (t.get Dt (hint0 hs)) (Nat.shiftLeft (hint1 hs) 6) (Nat.mul (oN n) 18446744073709551615)
      (oN n) F0 F1 F2 F3 = v := by
    have hv' : sliceProg t Dt (oN n) F0 F1 F2 F3 hs = v := Nat.eq_of_beq_eq_true hv
    simp only [sliceProg, hz] at hv'
    exact hv'
  obtain ⟨-, hb, h0, h1', h2, h3⟩ := sliceAt_cases _ _ _ _ _ _ _ _ _ hs' hv0
  have hM : Nat.mul (oN n) 18446744073709551615 = 2 ^ (64 * n) - 1 := oN_mul n
  have hM1 : Nat.mul (oN n) 18446744073709551615 + 1 = 2 ^ (64 * n) := by
    rw [hM]
    exact Nat.sub_add_cancel Nat.one_le_two_pow
  rw [hM1] at hb
  have hbd := ble_bound n (hint1 hs) (t.get Dt (hint0 hs)).N (by rw [Nat.ble_eq]; exact hb)
  have hC := BT.all_get ht Dt (hint0 hs) (hint1 hs + l) (by omega)
  rw [hM] at h0 h1' h2 h3
  rw [← h0, ← h1', ← h2, ← h3, lane_slice _ _ _ _ hl, lane_slice _ _ _ _ hl, lane_slice _ _ _ _ hl,
    lane_slice _ _ _ _ hl]
  exact hC

end Tammes15.D3Trig
