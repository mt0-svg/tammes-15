import Tammes15.D3Prog.LaneSim

namespace D3Prog

open D3Ck2Spec

theorem R.one {L U w : ℕ} (h : R 1 0 L U w w) : L ≤ w ∧ w ≤ U := h.wle Nat.one_pos

theorem R.lt64 {L U w : ℕ} (h : R 1 0 L U w w) : w < 2 ^ 64 := by
  have := h.1; simpa using this

theorem r1_ix {F : ℕ} (hF : F < 2 ^ 64) (s : ℕ) (hs : s = 0 ∨ s = 32) :
    R 1 0 4611686018427387904 4611686087146864624 (D3Ck2.ix 1 F s) (D3Ck2.ix 1 F s) := by
  have h := r_ix (n := 1) (l := 0) Nat.one_pos F s hs
  rw [oN_one, lane_zero F hF] at h
  exact h

theorem r1_hxa {H : ℕ} (hH : H < 2 ^ 64) (s : ℕ) (hs : s = 0 ∨ s = 32) :
    R 1 0 4611686018427387904 4611686019501129727 (D3Ck2.hxa 1 H s) (D3Ck2.hxa 1 H s) := by
  have h := r_hxa (n := 1) (l := 0) Nat.one_pos H s hs
  rw [oN_one, lane_zero H hH] at h
  exact h

theorem e_c (c : ℕ) (k : ℤ) (h : (c : ℤ) - 4611686018427387904 = k) : sv (Nat.mul 1 c) = k := by
  simp only [sv, Nat.mul_eq, one_mul]; omega

theorem e_ix {F : ℕ} (hF : F < 2 ^ 64) (s : ℕ) (hs : s = 0 ∨ s = 32) :
    sv (D3Ck2.ix 1 F s) = ((F / 2 ^ s % 2 ^ 32 * 16 : ℕ) : ℤ) := by
  rw [ix_one F s hF hs]; simp only [sv]; push_cast; ring

theorem e_hxa {H : ℕ} (hH : H < 2 ^ 64) (s : ℕ) (hs : s = 0 ∨ s = 32) :
    sv (D3Ck2.hxa 1 H s) = ((H / 2 ^ s % 2 ^ 30 : ℕ) : ℤ) := by
  rw [hxa_one H s hH hs]; simp only [sv]; push_cast; ring

theorem e_add {La Ua Lb Ub a b : ℕ} (ha : R 1 0 La Ua a a) (hb : R 1 0 Lb Ub b b)
    (h : 4611686018427387904 ≤ La + Lb) :
    sv (Nat.sub (Nat.add a b) (Nat.mul 1 4611686018427387904)) = sv a + sv b := by
  have := ha.one; have := hb.one
  simp only [sv, Nat.sub_eq, Nat.add_eq, Nat.mul_eq, one_mul]; omega

theorem e_sub {La Ua Lb Ub a b : ℕ} (ha : R 1 0 La Ua a a) (hb : R 1 0 Lb Ub b b)
    (h : Ub ≤ La + 4611686018427387904) :
    sv (Nat.sub (Nat.add a (Nat.mul 1 4611686018427387904)) b) = sv a - sv b := by
  have := ha.one; have := hb.one
  simp only [sv, Nat.sub_eq, Nat.add_eq, Nat.mul_eq, one_mul]; omega

theorem e_neg {La Ua a : ℕ} (ha : R 1 0 La Ua a a) (h : Ua ≤ 9223372036854775808) :
    sv (Nat.sub (Nat.add (Nat.mul 1 4611686018427387904) (Nat.mul 1 4611686018427387904)) a) = -sv a := by
  have := ha.one
  simp only [sv, Nat.sub_eq, Nat.add_eq, Nat.mul_eq, one_mul]; omega

theorem e_halfF {La Ua a : ℕ} (ha : R 1 0 La Ua a a) :
    sv (Nat.add (Lanes24.pshr1 1 a) (Nat.mul 1 2305843009213693952)) = sv a / 2 := by
  rw [pshr1_one a ha.lt64]
  simp only [sv, Nat.add_eq, Nat.mul_eq, one_mul]; omega

theorem e_halfC {La Ua a : ℕ} (ha : R 1 0 La Ua a a) (h : Ua < 18446744073709551615) :
    sv (Nat.add (Lanes24.pshr1 1 (Nat.add a 1)) (Nat.mul 1 2305843009213693952)) = (sv a + 1) / 2 := by
  have := ha.one
  rw [pshr1_one _ (by simp only [Nat.add_eq]; omega)]
  simp only [sv, Nat.add_eq, Nat.mul_eq, one_mul]; omega

theorem e_smx_gen (K : ℕ) {La Ua Lb Ub a b : ℕ} (ha : R 1 0 La Ua a a) (hb : R 1 0 Lb Ub b b) (B : ℕ)
    (hp : PB 1 a b B) (L U : ℕ) (h : smxOk K La Ua Lb Ub B L U = true) :
    sv (D3Ck2.smx K 1 a b) = sv a * sv b := by
  have hr := r_smx_gen (n := 1) (l := 0) Nat.one_pos K ha hb B hp L U h
  simp only [smxOk, decide_eq_true_eq] at h
  obtain ⟨hK1, hK2, hUa, hUb, ha1, ha2, hb1, hb2, hlo, hhi, -, -⟩ := h
  have hA := ha.sv_mem 0 Nat.one_pos
  have hB := hb.sv_mem 0 Nat.one_pos
  rw [lane_zero a ha.lt64] at hA
  rw [lane_zero b hb.lt64] at hB
  have hc := mul_corners hA hB
  have hpb := abs_le.1 (hp 0 Nat.one_pos)
  rw [lane_zero a ha.lt64, lane_zero b hb.lt64] at hpb
  have hwa : a < 2 ^ 63 := by have := ha.one; omega
  have hwb : b < 2 ^ 63 := by have := hb.one; omega
  rw [smx_one K a b ⟨hK1, hK2⟩ hwa hwb ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩,
    abs_lt.2 ⟨by norm_num; linarith [le_min hc.2 hpb.2, max_le hc.1 hpb.1],
      by norm_num; linarith [le_min hc.2 hpb.2, max_le hc.1 hpb.1]⟩⟩]
  have : 0 ≤ sv a * sv b + 2 ^ 62 := by norm_num; linarith [max_le hc.1 hpb.1]
  simp only [sv] at this ⊢
  rw [Int.toNat_of_nonneg this]; ring

theorem e_smx (K : ℕ) {La Ua Lb Ub a b : ℕ} (ha : R 1 0 La Ua a a) (hb : R 1 0 Lb Ub b b) (L U : ℕ)
    (h : smxOk K La Ua Lb Ub 340282366920938463463374607431768211456 L U = true) :
    sv (D3Ck2.smx K 1 a b) = sv a * sv b :=
  e_smx_gen K ha hb _ (by have := pb_big (n := 1) a b; norm_num at this ⊢; exact this) L U h

theorem e_smx_pb (K : ℕ) {La Ua Lb Ub a b B : ℕ} (ha : R 1 0 La Ua a a) (hb : R 1 0 Lb Ub b b)
    (hp : PB 1 a b B) (L U : ℕ) (h : smxOk K La Ua Lb Ub B L U = true) :
    sv (D3Ck2.smx K 1 a b) = sv a * sv b :=
  e_smx_gen K ha hb B hp L U h

theorem e_smx_sq (K : ℕ) {La Ua a : ℕ} (ha : R 1 0 La Ua a a) (L U : ℕ) (h : sqOk K La Ua L U = true) :
    sv (D3Ck2.smx K 1 a a) = sv a * sv a := by
  simp only [sqOk, decide_eq_true_eq] at h
  obtain ⟨hK1, hK2, hUa, ha1, ha2, ha3, ha4, hhi, -, -⟩ := h
  have hA := ha.sv_mem 0 Nat.one_pos
  rw [lane_zero a ha.lt64] at hA
  have hm := (sq_mem hA).2
  have hwa : a < 2 ^ 63 := by have := ha.one; omega
  rw [smx_one K a a ⟨hK1, hK2⟩ hwa hwa ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩,
    by rw [abs_of_nonneg (mul_self_nonneg _)]; norm_num; linarith [le_max_left ((((La : ℤ) - 4611686018427387904)) *
      ((La : ℤ) - 4611686018427387904)) (((Ua : ℤ) - 4611686018427387904) * ((Ua : ℤ) - 4611686018427387904))]⟩]
  have : 0 ≤ sv a * sv a + 2 ^ 62 := by nlinarith [mul_self_nonneg (sv a)]
  simp only [sv] at this ⊢
  rw [Int.toNat_of_nonneg this]; ring

theorem rnd_one {k : ℕ} (op : ℕ → ℕ → ℕ) (f : ℤ → ℤ) (hf : Monotone f) (hk : k ≤ 61)
    (hop : ∀ X, X < 2 ^ (64 * 1) → (∀ i < 1, |sv (lane X i)| < 2 ^ k) →
      op (D3Ck2.oN 1) X < 2 ^ (64 * 1) ∧ ∀ l < 1, lane (op (D3Ck2.oN 1) X) l = (f (sv (lane X l)) + 2 ^ 62).toNat)
    {La Ua a : ℕ} (ha : R 1 0 La Ua a a) (L U : ℕ) (h : rndOk k f La Ua L U = true) :
    sv (op 1 a) = f (sv a) := by
  simp only [rndOk, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, -, -⟩ := h
  have hA := ha.sv_mem 0 Nat.one_pos
  rw [lane_zero a ha.lt64] at hA
  have hb : |sv a| < 2 ^ k := abs_lt.2 ⟨by linarith, by linarith⟩
  rw [one_form op f hk hop a ha.lt64 hb]
  have : 0 ≤ f (sv a) + 2 ^ 62 := le_trans h3 (by have := hf hA.1; norm_num at this ⊢; linarith)
  simp only [sv] at this ⊢
  rw [Int.toNat_of_nonneg this]; ring

theorem e_srdF {La Ua a : ℕ} (ha : R 1 0 La Ua a a) (L U : ℕ)
    (h : rndOk 61 (fun v : ℤ => v / 2 ^ 28) La Ua L U = true) : sv (D3Ck2.srdF 1 a) = sv a / 2 ^ 28 :=
  rnd_one D3Ck2.srdF (fun v : ℤ => v / 2 ^ 28) mono_srdF le_rfl (srdF_lanes 1) ha L U h

theorem e_srdC {La Ua a : ℕ} (ha : R 1 0 La Ua a a) (L U : ℕ)
    (h : rndOk 61 (fun v : ℤ => -((-v) / 2 ^ 28)) La Ua L U = true) :
    sv (D3Ck2.srdC 1 a) = -((-sv a) / 2 ^ 28) :=
  rnd_one D3Ck2.srdC (fun v : ℤ => -((-v) / 2 ^ 28)) mono_srdC le_rfl (srdC_lanes 1) ha L U h

theorem e_sshl {La Ua a : ℕ} (ha : R 1 0 La Ua a a) (L U : ℕ)
    (h : rndOk 33 (fun v : ℤ => v * 2 ^ 28) La Ua L U = true) : sv (D3Ck2.sshl 1 a) = sv a * 2 ^ 28 :=
  rnd_one D3Ck2.sshl (fun v : ℤ => v * 2 ^ 28) mono_sshl (by norm_num) (sshl_lanes 1) ha L U h

theorem e_sc1 {Lx Ux x : ℕ} (hx : R 1 0 Lx Ux x x) (h : Ux < 9223372036854775808) :
    sv (D3Ck2.sc28u 1 x).1 = (sc28pS (scArg x)).1 := by
  have := hx.one
  rw [sc28u_one x (by omega)]
  obtain ⟨h1, -, -, -⟩ := sc28pS_bound (scArg x)
  simp only [sv]
  rw [Int.toNat_of_nonneg (by linarith)]; ring

theorem e_sc2 {Lx Ux x : ℕ} (hx : R 1 0 Lx Ux x x) (h : Ux < 9223372036854775808) :
    sv (D3Ck2.sc28u 1 x).2 = (sc28pS (scArg x)).2 := by
  have := hx.one
  rw [sc28u_one x (by omega)]
  obtain ⟨-, -, h3, -⟩ := sc28pS_bound (scArg x)
  simp only [sv]
  rw [Int.toNat_of_nonneg (by linarith)]; ring

theorem e_psqrt {Lw Uw w : ℕ} (hw : R 1 0 Lw Uw w w) (h : Uw ≤ 4683743612465315840) :
    sv (D3Ck2.psqrt 1 w) = ((Nat.sqrt (w - 4611686018427387904) : ℕ) : ℤ) := by
  have := hw.one
  rw [psqrt_one w (le_trans this.2 (le_trans h (by norm_num)))]
  have e : (4611686018427387904 : ℕ) = 2 ^ 62 := by norm_num
  rw [e]; simp only [sv]; push_cast; ring

theorem e_plt {La Ua Lb Ub a b : ℕ} (ha : R 1 0 La Ua a a) (hb : R 1 0 Lb Ub b b)
    (h : Ua < 9223372036854775808 ∧ Ub < 9223372036854775808) :
    (Lanes24.plt 1 a b = 1 ↔ sv a < sv b) := by
  have := ha.one; have := hb.one
  rw [plt_one a b (by omega) (by omega)]
  simp only [sv]
  split_ifs with hab <;> simp <;> omega

theorem e_land {La Ua Lb Ub a b : ℕ} (ha : R 1 0 La Ua a a) (hb : R 1 0 Lb Ub b b) (h : Ua ≤ 1 ∧ Ub ≤ 1) :
    (Nat.land a b = 1 ↔ a = 1 ∧ b = 1) := by
  have := ha.one; have := hb.one
  have h1 : a ≤ 1 := by omega
  have h2 : b ≤ 1 := by omega
  interval_cases a <;> interval_cases b <;> decide

theorem e_lor {La Ua Lb Ub a b : ℕ} (ha : R 1 0 La Ua a a) (hb : R 1 0 Lb Ub b b) (h : Ua ≤ 1 ∧ Ub ≤ 1) :
    (Nat.lor a b = 1 ↔ a = 1 ∨ b = 1) := by
  have := ha.one; have := hb.one
  have h1 : a ≤ 1 := by omega
  have h2 : b ≤ 1 := by omega
  interval_cases a <;> interval_cases b <;> decide

theorem e_not {La Ua a : ℕ} (ha : R 1 0 La Ua a a) (h : Ua ≤ 1) : (Nat.sub 1 a = 1 ↔ ¬a = 1) := by
  have := ha.one
  have h1 : a ≤ 1 := by omega
  interval_cases a <;> decide

theorem e_psel {Lm Um La Ua Lb Ub m a b : ℕ} (hm : R 1 0 Lm Um m m) (ha : R 1 0 La Ua a a)
    (hb : R 1 0 Lb Ub b b) (h : Um ≤ 1 ∧ Ua < 9223372036854775808 ∧ Ub < 9223372036854775808) :
    Lanes24.psel (Lanes24.pmask m) a b = if m = 1 then a else b := by
  have := hm.one; have := ha.one; have := hb.one
  exact psel_pmask m a b (by omega) (by omega) (by omega)

end D3Prog
