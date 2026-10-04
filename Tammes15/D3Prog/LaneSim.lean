import Tammes15.D3Ck2.Spec.Lanes

namespace D3Prog

open D3Ck2Spec

def R (n l L U v w : ℕ) : Prop :=
  v < 2 ^ (64 * n) ∧ (∀ i < n, L ≤ lane v i ∧ lane v i ≤ U) ∧ lane v l = w

def PB (n a b B : ℕ) : Prop := ∀ i < n, |sv (lane a i) * sv (lane b i)| ≤ B

variable {n l : ℕ}

theorem R.fits {L U v w b : ℕ} (h : R n l L U v w) (hU : U < b) : Fits n b v :=
  ⟨h.1, fun i hi => lt_of_le_of_lt (h.2.1 i hi).2 hU⟩

theorem R.wle {L U v w : ℕ} (hl : l < n) (h : R n l L U v w) : L ≤ w ∧ w ≤ U := by
  rw [← h.2.2]; exact h.2.1 l hl

theorem R.sv_mem {L U v w : ℕ} (h : R n l L U v w) (i : ℕ) (hi : i < n) :
    (L : ℤ) - 4611686018427387904 ≤ sv (lane v i) ∧ sv (lane v i) ≤ (U : ℤ) - 4611686018427387904 := by
  have := h.2.1 i hi
  simp only [sv]
  constructor <;> push_cast <;> omega

theorem r_zero : R n l 0 0 0 0 :=
  ⟨by positivity, fun i _ => by simp [lane_zero_pack], lane_zero_pack l⟩

theorem r_O (hl : l < n) : R n l 1 1 (D3Ck2.oN n) 1 :=
  ⟨oN_lt n, fun i hi => by rw [lane_oN n i hi]; exact ⟨le_rfl, le_rfl⟩, lane_oN n l hl⟩

theorem r_c (hl : l < n) (c : ℕ) (hc : c < 18446744073709551616) :
    R n l c c (Nat.mul (D3Ck2.oN n) c) (Nat.mul 1 c) := by
  obtain ⟨h1, h2⟩ := lane_mulc n c (by simpa using hc)
  exact ⟨h1, fun i hi => by rw [h2 i hi]; exact ⟨le_rfl, le_rfl⟩, by rw [h2 l hl]; exact (Nat.one_mul c).symm⟩

theorem ix_one (x s : ℕ) (hx : x < 2 ^ 64) (hs : s = 0 ∨ s = 32) :
    D3Ck2.ix 1 x s = x / 2 ^ s % 2 ^ 32 * 16 + 2 ^ 62 := by
  have h := lane_ix 1 x s hs
  rw [oN_one] at h
  have h1 := h.2 0 Nat.one_pos
  rwa [lane_zero _ (by simpa using h.1.1), lane_zero _ hx] at h1

theorem r_ix (hl : l < n) (F s : ℕ) (hs : s = 0 ∨ s = 32) :
    R n l 4611686018427387904 4611686087146864624 (D3Ck2.ix (D3Ck2.oN n) F s) (D3Ck2.ix 1 (lane F l) s) := by
  obtain ⟨h1, h2⟩ := lane_ix n F s hs
  refine ⟨h1.1, fun i hi => ?_, ?_⟩
  · rw [h2 i hi]
    have := Nat.mod_lt (lane F i / 2 ^ s) (show 0 < 2 ^ 32 by norm_num)
    exact ⟨by norm_num, by norm_num; omega⟩
  · rw [h2 l hl, ix_one _ s (lane_lt F l) hs]

theorem hxa_one (x s : ℕ) (hx : x < 2 ^ 64) (hs : s = 0 ∨ s = 32) :
    D3Ck2.hxa 1 x s = x / 2 ^ s % 2 ^ 30 + 2 ^ 62 := by
  have h := lane_hxa 1 x s hs
  rw [oN_one] at h
  have h1 := h.2 0 Nat.one_pos
  rwa [lane_zero _ (by simpa using h.1.1), lane_zero _ hx] at h1

theorem r_hxa (hl : l < n) (H s : ℕ) (hs : s = 0 ∨ s = 32) :
    R n l 4611686018427387904 4611686019501129727 (D3Ck2.hxa (D3Ck2.oN n) H s) (D3Ck2.hxa 1 (lane H l) s) := by
  obtain ⟨h1, h2⟩ := lane_hxa n H s hs
  refine ⟨h1.1, fun i hi => ?_, ?_⟩
  · rw [h2 i hi]
    have := Nat.mod_lt (lane H i / 2 ^ s) (show 0 < 2 ^ 30 by norm_num)
    exact ⟨by norm_num, by norm_num; omega⟩
  · rw [h2 l hl, hxa_one _ s (lane_lt H l) hs]

theorem r_add (hl : l < n) {La Ua Lb Ub a b wa wb : ℕ} (ha : R n l La Ua a wa) (hb : R n l Lb Ub b wb)
    (h : Ua + Ub < 18446744073709551616) : R n l (La + Lb) (Ua + Ub) (Nat.add a b) (Nat.add wa wb) := by
  obtain ⟨h1, h2⟩ := lane_add n a b ha.1 hb.1 (fun i hi => by
    have := (ha.2.1 i hi).2; have := (hb.2.1 i hi).2; norm_num; omega)
  refine ⟨h1, fun i hi => ?_, ?_⟩
  · rw [h2 i hi]; have := ha.2.1 i hi; have := hb.2.1 i hi; omega
  · rw [h2 l hl, ha.2.2, hb.2.2]; rfl

theorem r_sub (hl : l < n) {La Ua Lb Ub a b wa wb : ℕ} (ha : R n l La Ua a wa) (hb : R n l Lb Ub b wb)
    (h : Ub ≤ La) : R n l (La - Ub) (Ua - Lb) (Nat.sub a b) (Nat.sub wa wb) := by
  obtain ⟨h1, h2⟩ := lane_sub n a b ha.1 hb.1 (fun i hi => by
    have := (ha.2.1 i hi).1; have := (hb.2.1 i hi).2; omega)
  refine ⟨h1, fun i hi => ?_, ?_⟩
  · rw [h2 i hi]; have := ha.2.1 i hi; have := hb.2.1 i hi; omega
  · rw [h2 l hl, ha.2.2, hb.2.2]; rfl

theorem r_pshr1 (hl : l < n) {La Ua a wa : ℕ} (ha : R n l La Ua a wa) :
    R n l (La / 2) (Ua / 2) (Lanes24.pshr1 (D3Ck2.oN n) a) (Lanes24.pshr1 1 wa) := by
  obtain ⟨h1, h2⟩ := lane_pshr1 n a ha.1
  refine ⟨h1.1, fun i hi => ?_, ?_⟩
  · rw [h2 i hi]; have := ha.2.1 i hi
    exact ⟨Nat.div_le_div_right this.1, Nat.div_le_div_right this.2⟩
  · rw [h2 l hl, ha.2.2, pshr1_one wa (by rw [← ha.2.2]; exact lane_lt _ _)]

theorem r_plt (hl : l < n) {La Ua Lb Ub a b wa wb : ℕ} (ha : R n l La Ua a wa) (hb : R n l Lb Ub b wb)
    (h : Ua < 9223372036854775808 ∧ Ub < 9223372036854775808) :
    R n l 0 1 (Lanes24.plt (D3Ck2.oN n) a b) (Lanes24.plt 1 wa wb) := by
  have e : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  rw [e] at h
  obtain ⟨h1, h2⟩ := lane_plt n a b (ha.fits h.1) (hb.fits h.2)
  refine ⟨h1.1, fun i hi => ?_, ?_⟩
  · rw [h2 i hi]; split_ifs <;> simp
  · rw [h2 l hl, ha.2.2, hb.2.2, plt_one wa wb (lt_of_le_of_lt (ha.wle hl).2 h.1)
      (lt_of_le_of_lt (hb.wle hl).2 h.2)]

theorem r_land (_hl : l < n) {La Ua Lb Ub a b wa wb : ℕ} (ha : R n l La Ua a wa) (hb : R n l Lb Ub b wb)
    (h : Ua ≤ 1 ∧ Ub ≤ 1) : R n l 0 1 (Nat.land a b) (Nat.land wa wb) := by
  refine ⟨lt_of_le_of_lt (Nat.and_le_left (n := a) (m := b)) ha.1, fun i hi => ?_, ?_⟩
  · rw [lane_land]
    exact ⟨Nat.zero_le _, ((Nat.and_le_left (n := lane a i) (m := lane b i)).trans (ha.2.1 i hi).2).trans h.1⟩
  · rw [lane_land, ha.2.2, hb.2.2]

theorem r_lor (_hl : l < n) {La Ua Lb Ub a b wa wb : ℕ} (ha : R n l La Ua a wa) (hb : R n l Lb Ub b wb)
    (h : Ua ≤ 1 ∧ Ub ≤ 1) : R n l 0 1 (Nat.lor a b) (Nat.lor wa wb) := by
  refine ⟨Nat.or_lt_two_pow ha.1 hb.1, fun i hi => ?_, ?_⟩
  · rw [lane_lor]
    have h2 : lane a i ||| lane b i < 2 ^ 1 :=
      Nat.or_lt_two_pow (by have := (ha.2.1 i hi).2; omega) (by have := (hb.2.1 i hi).2; omega)
    exact ⟨Nat.zero_le _, by change lane a i ||| lane b i ≤ 1; omega⟩
  · rw [lane_lor, ha.2.2, hb.2.2]

theorem psel_lt' {k M A B : ℕ} (hA : A < 2 ^ k) (hB : B < 2 ^ k) : Lanes24.psel M A B < 2 ^ k := by
  unfold Lanes24.psel
  exact Nat.xor_lt_two_pow hB (lt_of_le_of_lt Nat.and_le_left (Nat.xor_lt_two_pow hA hB))

theorem r_psel (hl : l < n) {Lm Um La Ua Lb Ub m a b wm wa wb : ℕ} (hm : R n l Lm Um m wm)
    (ha : R n l La Ua a wa) (hb : R n l Lb Ub b wb)
    (h : Um ≤ 1 ∧ Ua < 9223372036854775808 ∧ Ub < 9223372036854775808) :
    R n l (min La Lb) (max Ua Ub) (Lanes24.psel (Lanes24.pmask m) a b) (Lanes24.psel (Lanes24.pmask wm) wa wb) := by
  have e : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  rw [e] at h
  obtain ⟨-, hm2⟩ := lane_pmask n m (hm.fits (by omega))
  have key : ∀ i < n, lane (Lanes24.psel (Lanes24.pmask m) a b) i = if lane m i = 1 then lane a i else lane b i := by
    intro i hi
    rw [lane_psel, hm2 i hi]
    have hpm : lane m i * (2 ^ 63 - 1) = Lanes24.pmask (lane m i) := by
      simp only [Lanes24.pmask]; norm_num
    rw [hpm, psel_pmask _ _ _ (by have := (hm.2.1 i hi).2; omega) (lt_of_le_of_lt (ha.2.1 i hi).2 h.2.1)
      (lt_of_le_of_lt (hb.2.1 i hi).2 h.2.2)]
  refine ⟨psel_lt' ha.1 hb.1, fun i hi => ?_, ?_⟩
  · rw [key i hi]; have := ha.2.1 i hi; have := hb.2.1 i hi
    split_ifs <;> constructor <;> omega
  · rw [key l hl, ha.2.2, hb.2.2, hm.2.2, psel_pmask _ _ _ (by have := (hm.wle hl).2; omega)
      (lt_of_le_of_lt (ha.wle hl).2 h.2.1) (lt_of_le_of_lt (hb.wle hl).2 h.2.2)]

theorem mul_corners {a1 a2 b1 b2 x y : ℤ} (hx : a1 ≤ x ∧ x ≤ a2) (hy : b1 ≤ y ∧ y ≤ b2) :
    min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2)) ≤ x * y ∧
      x * y ≤ max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
  have hl : ∀ c : ℤ, min (c * b1) (c * b2) ≤ c * y := fun c => by
    rcases le_total 0 c with hc | hc
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 hc)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 hc)
  have hu : ∀ c : ℤ, c * y ≤ max (c * b1) (c * b2) := fun c => by
    rcases le_total 0 c with hc | hc
    · exact (mul_le_mul_of_nonneg_left hy.2 hc).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hy.1 hc).trans (le_max_left _ _)
  constructor
  · rcases le_total 0 y with hy0 | hy0
    · exact (min_le_left _ _).trans ((hl a1).trans (mul_le_mul_of_nonneg_right hx.1 hy0))
    · exact (min_le_right _ _).trans ((hl a2).trans (mul_le_mul_of_nonpos_right hx.2 hy0))
  · rcases le_total 0 y with hy0 | hy0
    · exact (mul_le_mul_of_nonneg_right hx.2 hy0).trans ((hu a2).trans (le_max_right _ _))
    · exact (mul_le_mul_of_nonpos_right hx.1 hy0).trans ((hu a1).trans (le_max_left _ _))

theorem toNat_mem {p lo hi : ℤ} {L U : ℕ} (hp : lo ≤ p ∧ p ≤ hi) (h0 : 0 ≤ lo + 2 ^ 62)
    (hL : (L : ℤ) ≤ lo + 2 ^ 62) (hU : hi + 2 ^ 62 ≤ U) : L ≤ (p + 2 ^ 62).toNat ∧ (p + 2 ^ 62).toNat ≤ U := by
  omega

theorem smx_one (K x y : ℕ) (hK : 1 ≤ K ∧ K ≤ 63) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63)
    (hb : |sv x| < 2 ^ (64 - K) ∧ |sv y| < 2 ^ K ∧ |sv x * sv y| < 2 ^ 61) :
    D3Ck2.smx K 1 x y = (sv x * sv y + 2 ^ 62).toNat := by
  have hx' : x < 2 ^ 64 := by omega
  have hy' : y < 2 ^ 64 := by omega
  have h := lane_smx K 1 x y hK (fits_one hx (by norm_num)) (fits_one hy (by norm_num))
    (fun i hi => by obtain rfl : i = 0 := by omega
                    rw [lane_zero _ hx', lane_zero _ hy']; exact hb)
  rw [oN_one] at h
  have h1 := h.2 0 Nat.one_pos
  rwa [lane_zero _ (by simpa using h.1), lane_zero _ hx', lane_zero _ hy'] at h1

def smxOk (K La Ua Lb Ub B L U : ℕ) : Bool :=
  let a1 : ℤ := (La : ℤ) - 4611686018427387904
  let a2 : ℤ := (Ua : ℤ) - 4611686018427387904
  let b1 : ℤ := (Lb : ℤ) - 4611686018427387904
  let b2 : ℤ := (Ub : ℤ) - 4611686018427387904
  let lo := max (min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2))) (-(B : ℤ))
  let hi := min (max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2))) (B : ℤ)
  decide (1 ≤ K ∧ K ≤ 63 ∧ Ua < 9223372036854775808 ∧ Ub < 9223372036854775808 ∧
    -((2 : ℤ) ^ (64 - K)) < a1 ∧ a2 < (2 : ℤ) ^ (64 - K) ∧ -((2 : ℤ) ^ K) < b1 ∧ b2 < (2 : ℤ) ^ K ∧
    -2305843009213693952 < lo ∧ hi < 2305843009213693952 ∧
    (L : ℤ) ≤ lo + 4611686018427387904 ∧ hi + 4611686018427387904 ≤ (U : ℤ))

theorem r_smx_gen (hl : l < n) (K : ℕ) {La Ua Lb Ub a b wa wb : ℕ} (ha : R n l La Ua a wa)
    (hb : R n l Lb Ub b wb) (B : ℕ) (hp : PB n a b B) (L U : ℕ) (h : smxOk K La Ua Lb Ub B L U = true) :
    R n l L U (D3Ck2.smx K (D3Ck2.oN n) a b) (D3Ck2.smx K 1 wa wb) := by
  simp only [smxOk, decide_eq_true_eq] at h
  obtain ⟨hK1, hK2, hUa, hUb, ha1, ha2, hb1, hb2, hlo, hhi, hL, hU⟩ := h
  have e63 : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  rw [e63] at hUa hUb
  have hval : ∀ i < n, (max (min (min (((La : ℤ) - 4611686018427387904) * ((Lb : ℤ) - 4611686018427387904))
      (((La : ℤ) - 4611686018427387904) * ((Ub : ℤ) - 4611686018427387904)))
      (min (((Ua : ℤ) - 4611686018427387904) * ((Lb : ℤ) - 4611686018427387904))
        (((Ua : ℤ) - 4611686018427387904) * ((Ub : ℤ) - 4611686018427387904)))) (-(B : ℤ)) ≤
        sv (lane a i) * sv (lane b i) ∧
      sv (lane a i) * sv (lane b i) ≤ min (max (max (((La : ℤ) - 4611686018427387904) *
        ((Lb : ℤ) - 4611686018427387904)) (((La : ℤ) - 4611686018427387904) * ((Ub : ℤ) - 4611686018427387904)))
        (max (((Ua : ℤ) - 4611686018427387904) * ((Lb : ℤ) - 4611686018427387904))
          (((Ua : ℤ) - 4611686018427387904) * ((Ub : ℤ) - 4611686018427387904)))) (B : ℤ)) ∧
      |sv (lane a i)| < 2 ^ (64 - K) ∧ |sv (lane b i)| < 2 ^ K := by
    intro i hi
    have hA := ha.sv_mem i hi
    have hB := hb.sv_mem i hi
    have hc := mul_corners hA hB
    have hpb := abs_le.1 (hp i hi)
    refine ⟨⟨max_le hc.1 hpb.1, le_min hc.2 hpb.2⟩, abs_lt.2 ⟨lt_of_lt_of_le ha1 hA.1, lt_of_le_of_lt hA.2 ha2⟩,
      abs_lt.2 ⟨lt_of_lt_of_le hb1 hB.1, lt_of_le_of_lt hB.2 hb2⟩⟩
  have hb' : ∀ i < n, |sv (lane a i)| < 2 ^ (64 - K) ∧ |sv (lane b i)| < 2 ^ K ∧
      |sv (lane a i) * sv (lane b i)| < 2 ^ 61 := by
    intro i hi
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hval i hi
    exact ⟨h3, h4, abs_lt.2 ⟨by norm_num; linarith, by norm_num; linarith⟩⟩
  obtain ⟨h1, h2⟩ := lane_smx K n a b ⟨hK1, hK2⟩ (ha.fits hUa) (hb.fits hUb) hb'
  refine ⟨h1, fun i hi => ?_, ?_⟩
  · rw [h2 i hi]
    obtain ⟨⟨hv1, hv2⟩, -, -⟩ := hval i hi
    exact toNat_mem ⟨hv1, hv2⟩ (by linarith) hL hU
  · rw [h2 l hl, ha.2.2, hb.2.2]
    have hwa : lane a l < 2 ^ 63 := lt_of_le_of_lt (ha.2.1 l hl).2 hUa
    have hwb : lane b l < 2 ^ 63 := lt_of_le_of_lt (hb.2.1 l hl).2 hUb
    rw [ha.2.2] at hwa; rw [hb.2.2] at hwb
    have := hb' l hl
    rw [ha.2.2, hb.2.2] at this
    exact (smx_one K wa wb ⟨hK1, hK2⟩ hwa hwb this).symm

theorem pb_big (a b : ℕ) : PB n a b (2 ^ 128) := by
  intro i _
  have h1 : |sv (lane a i)| ≤ 2 ^ 64 := by
    have := lane_lt a i; simp only [sv]; rw [abs_le]; constructor <;> push_cast <;> omega
  have h2 : |sv (lane b i)| ≤ 2 ^ 64 := by
    have := lane_lt b i; simp only [sv]; rw [abs_le]; constructor <;> push_cast <;> omega
  rw [abs_mul]; push_cast
  calc |sv (lane a i)| * |sv (lane b i)| ≤ 2 ^ 64 * 2 ^ 64 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 2 ^ 128 := by norm_num

theorem r_smx (hl : l < n) (K : ℕ) {La Ua Lb Ub a b wa wb : ℕ} (ha : R n l La Ua a wa)
    (hb : R n l Lb Ub b wb) (L U : ℕ)
    (h : smxOk K La Ua Lb Ub 340282366920938463463374607431768211456 L U = true) :
    R n l L U (D3Ck2.smx K (D3Ck2.oN n) a b) (D3Ck2.smx K 1 wa wb) :=
  r_smx_gen hl K ha hb _ (by have := pb_big (n := n) a b; norm_num at this ⊢; exact this) L U h

theorem r_smx_pb (hl : l < n) (K : ℕ) {La Ua Lb Ub a b wa wb B : ℕ} (ha : R n l La Ua a wa)
    (hb : R n l Lb Ub b wb) (hp : PB n a b B) (L U : ℕ) (h : smxOk K La Ua Lb Ub B L U = true) :
    R n l L U (D3Ck2.smx K (D3Ck2.oN n) a b) (D3Ck2.smx K 1 wa wb) :=
  r_smx_gen hl K ha hb B hp L U h

def sqOk (K La Ua L U : ℕ) : Bool :=
  let a1 : ℤ := (La : ℤ) - 4611686018427387904
  let a2 : ℤ := (Ua : ℤ) - 4611686018427387904
  let lo : ℤ := if 0 < a1 then a1 * a1 else if a2 < 0 then a2 * a2 else 0
  let hi := max (a1 * a1) (a2 * a2)
  decide (1 ≤ K ∧ K ≤ 63 ∧ Ua < 9223372036854775808 ∧
    -((2 : ℤ) ^ (64 - K)) < a1 ∧ a2 < (2 : ℤ) ^ (64 - K) ∧ -((2 : ℤ) ^ K) < a1 ∧ a2 < (2 : ℤ) ^ K ∧
    hi < 2305843009213693952 ∧ (L : ℤ) ≤ lo + 4611686018427387904 ∧ hi + 4611686018427387904 ≤ (U : ℤ))

theorem sq_mem {a1 a2 x : ℤ} (hx : a1 ≤ x ∧ x ≤ a2) :
    (if 0 < a1 then a1 * a1 else if a2 < 0 then a2 * a2 else 0) ≤ x * x ∧ x * x ≤ max (a1 * a1) (a2 * a2) := by
  constructor
  · split_ifs with h1 h2
    · nlinarith
    · nlinarith
    · nlinarith
  · rcases le_total 0 x with h | h
    · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)

theorem r_smx_sq (hl : l < n) (K : ℕ) {La Ua a wa : ℕ} (ha : R n l La Ua a wa) (L U : ℕ)
    (h : sqOk K La Ua L U = true) : R n l L U (D3Ck2.smx K (D3Ck2.oN n) a a) (D3Ck2.smx K 1 wa wa) := by
  simp only [sqOk, decide_eq_true_eq] at h
  obtain ⟨hK1, hK2, hUa, ha1, ha2, ha3, ha4, hhi, hL, hU⟩ := h
  have e63 : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  rw [e63] at hUa
  have hval : ∀ i < n, _ ∧ _ := fun i hi => sq_mem (ha.sv_mem i hi)
  have hb' : ∀ i < n, |sv (lane a i)| < 2 ^ (64 - K) ∧ |sv (lane a i)| < 2 ^ K ∧
      |sv (lane a i) * sv (lane a i)| < 2 ^ 61 := by
    intro i hi
    have hA := ha.sv_mem i hi
    obtain ⟨h1, h2⟩ := hval i hi
    refine ⟨abs_lt.2 ⟨lt_of_lt_of_le ha1 hA.1, lt_of_le_of_lt hA.2 ha2⟩,
      abs_lt.2 ⟨lt_of_lt_of_le ha3 hA.1, lt_of_le_of_lt hA.2 ha4⟩, ?_⟩
    rw [abs_of_nonneg (mul_self_nonneg _)]; norm_num; linarith
  obtain ⟨h1, h2⟩ := lane_smx K n a a ⟨hK1, hK2⟩ (ha.fits hUa) (ha.fits hUa) hb'
  refine ⟨h1, fun i hi => ?_, ?_⟩
  · rw [h2 i hi]
    obtain ⟨hv1, hv2⟩ := hval i hi
    refine toNat_mem ⟨hv1, hv2⟩ ?_ hL hU
    split_ifs <;> nlinarith
  · rw [h2 l hl, ha.2.2]
    have hwa : lane a l < 2 ^ 63 := lt_of_le_of_lt (ha.2.1 l hl).2 hUa
    rw [ha.2.2] at hwa
    have := hb' l hl
    rw [ha.2.2] at this
    exact (smx_one K wa wa ⟨hK1, hK2⟩ hwa hwa this).symm

def rndOk (k : ℕ) (f : ℤ → ℤ) (La Ua L U : ℕ) : Bool :=
  let a1 : ℤ := (La : ℤ) - 4611686018427387904
  let a2 : ℤ := (Ua : ℤ) - 4611686018427387904
  decide (-((2 : ℤ) ^ k) < a1 ∧ a2 < (2 : ℤ) ^ k ∧ 0 ≤ f a1 + 4611686018427387904 ∧
    (L : ℤ) ≤ f a1 + 4611686018427387904 ∧ f a2 + 4611686018427387904 ≤ (U : ℤ))

theorem r_rnd (hl : l < n) (k : ℕ) (f : ℤ → ℤ) (hf : Monotone f) (op : ℕ → ℕ → ℕ)
    (hop : ∀ X, X < 2 ^ (64 * n) → (∀ i < n, |sv (lane X i)| < 2 ^ k) →
      op (D3Ck2.oN n) X < 2 ^ (64 * n) ∧ ∀ l < n, lane (op (D3Ck2.oN n) X) l = (f (sv (lane X l)) + 2 ^ 62).toNat)
    (hop1 : ∀ x, x < 2 ^ 64 → |sv x| < 2 ^ k → op 1 x = (f (sv x) + 2 ^ 62).toNat)
    {La Ua a wa : ℕ} (ha : R n l La Ua a wa) (L U : ℕ) (h : rndOk k f La Ua L U = true) :
    R n l L U (op (D3Ck2.oN n) a) (op 1 wa) := by
  simp only [rndOk, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h0, hL, hU⟩ := h
  have hb : ∀ i < n, |sv (lane a i)| < 2 ^ k := fun i hi => by
    have := ha.sv_mem i hi; exact abs_lt.2 ⟨lt_of_lt_of_le h1 this.1, lt_of_le_of_lt this.2 h2⟩
  obtain ⟨g1, g2⟩ := hop a ha.1 hb
  refine ⟨g1, fun i hi => ?_, ?_⟩
  · rw [g2 i hi]
    have := ha.sv_mem i hi
    exact toNat_mem ⟨hf this.1, hf this.2⟩ h0 hL hU
  · rw [g2 l hl, ha.2.2]
    have := hb l hl
    rw [ha.2.2] at this
    exact (hop1 wa (by rw [← ha.2.2]; exact lane_lt _ _) this).symm

theorem one_form {k : ℕ} (op : ℕ → ℕ → ℕ) (f : ℤ → ℤ) (_hk : k ≤ 61)
    (hop : ∀ X, X < 2 ^ (64 * 1) → (∀ i < 1, |sv (lane X i)| < 2 ^ k) →
      op (D3Ck2.oN 1) X < 2 ^ (64 * 1) ∧ ∀ l < 1, lane (op (D3Ck2.oN 1) X) l = (f (sv (lane X l)) + 2 ^ 62).toNat)
    (x : ℕ) (hx : x < 2 ^ 64) (hb : |sv x| < 2 ^ k) : op 1 x = (f (sv x) + 2 ^ 62).toNat := by
  have h := hop x (by simpa using hx) (fun i hi => by obtain rfl : i = 0 := by omega
                                                      rw [lane_zero _ hx]; exact hb)
  rw [oN_one] at h
  have h1 := h.2 0 Nat.one_pos
  rwa [lane_zero _ (by simpa using h.1), lane_zero _ hx] at h1

theorem srdF_lanes (n X : ℕ) (hX : X < 2 ^ (64 * n)) (hb : ∀ i < n, |sv (lane X i)| < 2 ^ 61) :
    D3Ck2.srdF (D3Ck2.oN n) X < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.srdF (D3Ck2.oN n) X) l = ((fun v : ℤ => v / 2 ^ 28) (sv (lane X l)) + 2 ^ 62).toNat :=
  lane_srdF n X hX hb

theorem srdC_lanes (n X : ℕ) (hX : X < 2 ^ (64 * n)) (hb : ∀ i < n, |sv (lane X i)| < 2 ^ 61) :
    D3Ck2.srdC (D3Ck2.oN n) X < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.srdC (D3Ck2.oN n) X) l = ((fun v : ℤ => -((-v) / 2 ^ 28)) (sv (lane X l)) + 2 ^ 62).toNat :=
  lane_srdC n X hX hb

theorem sshl_lanes (n X : ℕ) (hX : X < 2 ^ (64 * n)) (hb : ∀ i < n, |sv (lane X i)| < 2 ^ 33) :
    D3Ck2.sshl (D3Ck2.oN n) X < 2 ^ (64 * n) ∧
      ∀ l < n, lane (D3Ck2.sshl (D3Ck2.oN n) X) l = ((fun v : ℤ => v * 2 ^ 28) (sv (lane X l)) + 2 ^ 62).toNat :=
  lane_sshl n X hX hb

theorem mono_srdF : Monotone (fun v : ℤ => v / 2 ^ 28) := fun _ _ h => Int.ediv_le_ediv (by norm_num) h
theorem mono_srdC : Monotone (fun v : ℤ => -((-v) / 2 ^ 28)) := fun _ _ h =>
  neg_le_neg (Int.ediv_le_ediv (by norm_num) (neg_le_neg h))
theorem mono_sshl : Monotone (fun v : ℤ => v * 2 ^ 28) := fun _ _ h => by
  simp only; exact mul_le_mul_of_nonneg_right h (by norm_num)

theorem r_srdF (hl : l < n) {La Ua a wa : ℕ} (ha : R n l La Ua a wa) (L U : ℕ)
    (h : rndOk 61 (fun v : ℤ => v / 2 ^ 28) La Ua L U = true) :
    R n l L U (D3Ck2.srdF (D3Ck2.oN n) a) (D3Ck2.srdF 1 wa) :=
  r_rnd hl 61 _ mono_srdF D3Ck2.srdF (srdF_lanes n) (one_form (k := 61) D3Ck2.srdF (fun v : ℤ => v / 2 ^ 28) le_rfl (srdF_lanes 1)) ha L U h

theorem r_srdC (hl : l < n) {La Ua a wa : ℕ} (ha : R n l La Ua a wa) (L U : ℕ)
    (h : rndOk 61 (fun v : ℤ => -((-v) / 2 ^ 28)) La Ua L U = true) :
    R n l L U (D3Ck2.srdC (D3Ck2.oN n) a) (D3Ck2.srdC 1 wa) :=
  r_rnd hl 61 _ mono_srdC D3Ck2.srdC (srdC_lanes n) (one_form (k := 61) D3Ck2.srdC (fun v : ℤ => -((-v) / 2 ^ 28)) le_rfl (srdC_lanes 1)) ha L U h

theorem r_sshl (hl : l < n) {La Ua a wa : ℕ} (ha : R n l La Ua a wa) (L U : ℕ)
    (h : rndOk 33 (fun v : ℤ => v * 2 ^ 28) La Ua L U = true) :
    R n l L U (D3Ck2.sshl (D3Ck2.oN n) a) (D3Ck2.sshl 1 wa) :=
  r_rnd hl 33 _ mono_sshl D3Ck2.sshl (sshl_lanes n) (one_form (k := 33) D3Ck2.sshl (fun v : ℤ => v * 2 ^ 28) (by norm_num) (sshl_lanes 1)) ha L U h

theorem sc28pS_min (x : ℕ) : sc28pS (min x (PI_LO + 1)) = sc28pS x := by
  unfold sc28pS; simp only [min_assoc, min_self]

theorem sc28pS_bound (x : ℕ) : 0 ≤ (sc28pS x).1 ∧ (sc28pS x).1 ≤ 268435459 ∧
    -268435459 ≤ (sc28pS x).2 ∧ (sc28pS x).2 ≤ 268435459 := by
  rw [← sc28pS_min x]
  have h := sc28pS_err (min x (PI_LO + 1)) (min_le_right _ _)
  set y := ((min x (PI_LO + 1) : ℕ) : ℝ) / 2 ^ 28
  have hs := Real.sin_le_one y
  have hs' := Real.neg_one_le_sin y
  have hc := Real.cos_le_one y
  have hc' := Real.neg_one_le_cos y
  obtain ⟨h1, h2⟩ := h
  rw [abs_le] at h1 h2
  have e1 : (0 : ℤ) ≤ (sc28pS (min x (PI_LO + 1))).1 := by
    unfold sc28pS; simp only; split_ifs <;> positivity
  refine ⟨e1, ?_, ?_, ?_⟩
  · have : ((sc28pS (min x (PI_LO + 1))).1 : ℝ) ≤ 268435459 := by nlinarith
    exact_mod_cast this
  · have : (-268435459 : ℝ) ≤ ((sc28pS (min x (PI_LO + 1))).2 : ℝ) := by nlinarith
    exact_mod_cast this
  · have : ((sc28pS (min x (PI_LO + 1))).2 : ℝ) ≤ 268435459 := by nlinarith
    exact_mod_cast this

theorem sc_one_bound (y : ℕ) (hy : y < 2 ^ 63) :
    4611686018427387904 ≤ (D3Ck2.sc28u 1 y).1 ∧ (D3Ck2.sc28u 1 y).1 ≤ 4611686018695823363 ∧
      4611686018158952445 ≤ (D3Ck2.sc28u 1 y).2 ∧ (D3Ck2.sc28u 1 y).2 ≤ 4611686018695823363 := by
  rw [sc28u_one y hy]
  obtain ⟨h1, h2, h3, h4⟩ := sc28pS_bound (scArg y)
  simp only
  omega

theorem r_sc1 (hl : l < n) {Lx Ux x wx : ℕ} (hx : R n l Lx Ux x wx) (h : Ux < 9223372036854775808) :
    R n l 4611686018427387904 4611686018695823363 (D3Ck2.sc28u (D3Ck2.oN n) x).1 (D3Ck2.sc28u 1 wx).1 := by
  have e : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  rw [e] at h
  obtain ⟨g1, -, g3⟩ := lane_sc28u n x (hx.fits h)
  refine ⟨g1.1, fun i hi => ?_, ?_⟩
  · rw [(g3 i hi).1]
    have := sc_one_bound (lane x i) (lt_of_le_of_lt (hx.2.1 i hi).2 h)
    exact ⟨this.1, this.2.1⟩
  · rw [(g3 l hl).1, hx.2.2]

theorem r_sc2 (hl : l < n) {Lx Ux x wx : ℕ} (hx : R n l Lx Ux x wx) (h : Ux < 9223372036854775808) :
    R n l 4611686018158952445 4611686018695823363 (D3Ck2.sc28u (D3Ck2.oN n) x).2 (D3Ck2.sc28u 1 wx).2 := by
  have e : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  rw [e] at h
  obtain ⟨-, g2, g3⟩ := lane_sc28u n x (hx.fits h)
  refine ⟨g2.1, fun i hi => ?_, ?_⟩
  · rw [(g3 i hi).2]
    have := sc_one_bound (lane x i) (lt_of_le_of_lt (hx.2.1 i hi).2 h)
    exact ⟨this.2.2.1, this.2.2.2⟩
  · rw [(g3 l hl).2, hx.2.2]

theorem sqrt_le_pow28 (x : ℕ) (hx : x ≤ 2 ^ 56) : Nat.sqrt x ≤ 2 ^ 28 := by
  have := Nat.sqrt_le_sqrt hx
  rwa [show (2 : ℕ) ^ 56 = (2 ^ 28) ^ 2 by norm_num, Nat.sqrt_eq'] at this

theorem r_psqrt (hl : l < n) {Lw Uw w ww : ℕ} (hw : R n l Lw Uw w ww) (h : Uw ≤ 4683743612465315840) :
    R n l 4611686018427387904 4611686018695823360 (D3Ck2.psqrt (D3Ck2.oN n) w) (D3Ck2.psqrt 1 ww) := by
  have e : (4683743612465315840 : ℕ) = 2 ^ 62 + 2 ^ 56 := by norm_num
  rw [e] at h
  obtain ⟨g1, g2⟩ := lane_psqrt n w (hw.fits (by omega))
  refine ⟨g1, fun i hi => ?_, ?_⟩
  · rw [g2 i hi, psqrt_one _ (le_trans (hw.2.1 i hi).2 h)]
    have := sqrt_le_pow28 (lane w i - 2 ^ 62) (by have := (hw.2.1 i hi).2; omega)
    exact ⟨by norm_num, by norm_num at this ⊢; exact this⟩
  · rw [g2 l hl, hw.2.2]

def pbOk (plus : Bool) (K Lq Uq B : ℕ) : Bool :=
  let a1 : ℤ := (Lq : ℤ) - 4611686018427387904
  let a2 : ℤ := (Uq : ℤ) - 4611686018427387904
  decide (1 ≤ K ∧ K ≤ 63 ∧ Uq < 9223372036854775808 ∧
    -((2 : ℤ) ^ (64 - K)) < a1 ∧ a2 < (2 : ℤ) ^ (64 - K) ∧ -((2 : ℤ) ^ K) < a1 ∧ a2 < (2 : ℤ) ^ K ∧
    a1 * a1 < 2305843009213693952 ∧ a2 * a2 < 2305843009213693952 ∧
    36028797018963968 + (if plus then max (-a1) a2 else 0) ≤ (B : ℤ))

theorem sqrt_mul_le (x : ℤ) :
    ((Nat.sqrt (2 ^ 56 - (x * x).toNat) : ℕ) : ℤ) * |x| ≤ 36028797018963968 := by
  set m := (x * x).toNat with hm
  have hm' : (m : ℤ) = x * x := Int.toNat_of_nonneg (mul_self_nonneg x)
  set s := Nat.sqrt (2 ^ 56 - m)
  have hs : s * s ≤ 2 ^ 56 - m := Nat.sqrt_le (2 ^ 56 - m)
  rcases le_or_gt m (2 ^ 56) with h | h
  · have hs' : (s : ℤ) * s + m ≤ 2 ^ 56 := by
      have : s * s + m ≤ 2 ^ 56 := by omega
      exact_mod_cast this
    rw [hm'] at hs'
    have hx : |x| * |x| = x * x := abs_mul_abs_self x
    nlinarith [sq_nonneg ((s : ℤ) - |x|), abs_nonneg x]
  · have h0 : s = 0 := by
      show Nat.sqrt (2 ^ 56 - m) = 0
      rw [show 2 ^ 56 - m = 0 by omega, Nat.sqrt_zero]
    rw [h0]; simp

theorem send_lanes (_hl : l < n) (K : ℕ) {Lq Uq q wq : ℕ} (hq : R n l Lq Uq q wq) (plus : Bool) (B : ℕ)
    (h : pbOk plus K Lq Uq B = true) :
    D3Ck2.psqrt (D3Ck2.oN n) (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
      (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q)) < 2 ^ (64 * n) ∧
    ∀ i < n, lane (D3Ck2.psqrt (D3Ck2.oN n) (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
      (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q))) i < 2 ^ 63 ∧
      0 ≤ sv (lane (D3Ck2.psqrt (D3Ck2.oN n) (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
        (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q))) i) ∧
      sv (lane (D3Ck2.psqrt (D3Ck2.oN n) (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
        (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q))) i) * |sv (lane q i)| ≤
          36028797018963968 ∧
      |sv (lane q i)| ≤ max (-((Lq : ℤ) - 4611686018427387904)) ((Uq : ℤ) - 4611686018427387904) := by
  simp only [pbOk, decide_eq_true_eq] at h
  obtain ⟨hK1, hK2, hUq, ha1, ha2, ha3, ha4, hs1, hs2, hB⟩ := h
  have e63 : (9223372036854775808 : ℕ) = 2 ^ 63 := by norm_num
  rw [e63] at hUq

  have hsq : ∀ i < n, |sv (lane q i)| < 2 ^ (64 - K) ∧ |sv (lane q i)| < 2 ^ K ∧
      |sv (lane q i) * sv (lane q i)| < 2 ^ 61 := by
    intro i hi
    have hA := hq.sv_mem i hi
    have hm := (sq_mem hA).2
    refine ⟨abs_lt.2 ⟨lt_of_lt_of_le ha1 hA.1, lt_of_le_of_lt hA.2 ha2⟩,
      abs_lt.2 ⟨lt_of_lt_of_le ha3 hA.1, lt_of_le_of_lt hA.2 ha4⟩, ?_⟩
    rw [abs_of_nonneg (mul_self_nonneg _)]
    exact lt_of_le_of_lt hm (max_lt (by norm_num; exact hs1) (by norm_num; exact hs2))
  obtain ⟨q1, q2⟩ := lane_smx K n q q ⟨hK1, hK2⟩ (hq.fits hUq) (hq.fits hUq) hsq
  obtain ⟨c1, c2⟩ := lane_mulc n 4683743612465315840 (by norm_num)
  obtain ⟨o1, o2⟩ := lane_mulc n 4611686018427387904 (by norm_num)
  obtain ⟨d1, d2⟩ := lane_add n _ _ c1 o1 (fun i hi => by rw [c2 i hi, o2 i hi]; norm_num)
  have hq2 : ∀ i < n, (lane (D3Ck2.smx K (D3Ck2.oN n) q q) i : ℤ) = sv (lane q i) * sv (lane q i) + 2 ^ 62 := by
    intro i hi
    rw [q2 i hi]
    exact Int.toNat_of_nonneg (by nlinarith [mul_self_nonneg (sv (lane q i))])
  have hq2b : ∀ i < n, lane (D3Ck2.smx K (D3Ck2.oN n) q q) i < 2 ^ 62 + 2 ^ 61 := by
    intro i hi
    have := hq2 i hi
    have h3 := (hsq i hi).2.2
    rw [abs_of_nonneg (mul_self_nonneg _)] at h3
    omega
  obtain ⟨w1, w2⟩ := lane_sub n _ _ d1 q1 (fun i hi => by
    rw [d2 i hi, c2 i hi, o2 i hi]; have := hq2b i hi; norm_num at this ⊢; omega)
  have hW : ∀ i < n, lane (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
      (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q)) i =
        2 ^ 62 + 2 ^ 56 + 2 ^ 62 - lane (D3Ck2.smx K (D3Ck2.oN n) q q) i := by
    intro i hi
    rw [w2 i hi, d2 i hi, c2 i hi, o2 i hi]; norm_num
  obtain ⟨r1, r2⟩ := lane_psqrt n _ ⟨w1, fun i hi => by
    rw [hW i hi]; have := hq2 i hi; have := mul_self_nonneg (sv (lane q i)); omega⟩
  refine ⟨r1, fun i hi => ?_⟩
  have hWi : lane (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
      (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q)) i ≤ 2 ^ 62 + 2 ^ 56 := by
    rw [hW i hi]; have := hq2 i hi; have := mul_self_nonneg (sv (lane q i)); omega
  rw [r2 i hi, psqrt_one _ hWi]
  have hsub : lane (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
      (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q)) i - 2 ^ 62 =
        2 ^ 56 - (sv (lane q i) * sv (lane q i)).toNat := by
    rw [hW i hi, q2 i hi]
    have := mul_self_nonneg (sv (lane q i))
    omega
  rw [hsub]
  have hroot := sqrt_mul_le (sv (lane q i))
  have hr28 := sqrt_le_pow28 (2 ^ 56 - (sv (lane q i) * sv (lane q i)).toNat) (Nat.sub_le _ _)
  have hsv : sv (Nat.sqrt (2 ^ 56 - (sv (lane q i) * sv (lane q i)).toNat) + 2 ^ 62) =
      ((Nat.sqrt (2 ^ 56 - (sv (lane q i) * sv (lane q i)).toNat) : ℕ) : ℤ) := by
    simp only [sv]; push_cast; ring
  rw [hsv]
  have hA := hq.sv_mem i hi
  refine ⟨by norm_num at hr28 ⊢; omega, Nat.cast_nonneg _, hroot, ?_⟩
  exact abs_le.2 ⟨by have := le_max_left (-((Lq : ℤ) - 4611686018427387904)) ((Uq : ℤ) - 4611686018427387904)
                     linarith [hA.1],
                  le_trans hA.2 (le_max_right _ _)⟩

theorem pbOk_B {plus : Bool} {K Lq Uq B : ℕ} (h : pbOk plus K Lq Uq B = true) :
    36028797018963968 + (if plus then max (-((Lq : ℤ) - 4611686018427387904)) ((Uq : ℤ) - 4611686018427387904)
      else 0) ≤ (B : ℤ) := by
  simp only [pbOk, decide_eq_true_eq] at h
  exact h.2.2.2.2.2.2.2.2.2

theorem pb_sqrt (hl : l < n) {Lq Uq q wq : ℕ} (hq : R n l Lq Uq q wq) (K B : ℕ)
    (h : pbOk false K Lq Uq B = true) :
    PB n (D3Ck2.psqrt (D3Ck2.oN n) (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
      (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q))) q B := by
  intro i hi
  obtain ⟨-, h0, h1, -⟩ := (send_lanes hl K hq false B h).2 i hi
  have hB := pbOk_B h
  simp only [Bool.false_eq_true, ite_false, add_zero] at hB
  rw [abs_mul, abs_of_nonneg h0]
  linarith

theorem pb_sqrt1 (hl : l < n) {Lq Uq q wq : ℕ} (hq : R n l Lq Uq q wq) (K B : ℕ)
    (h : pbOk true K Lq Uq B = true) :
    PB n (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4611686018427387905)
      (D3Ck2.psqrt (D3Ck2.oN n) (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
        (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q))))
      (Nat.mul (D3Ck2.oN n) 4611686018427387904)) q B := by
  obtain ⟨r1, r2⟩ := send_lanes hl K hq true B h
  obtain ⟨c1, c2⟩ := lane_mulc n 4611686018427387905 (by norm_num)
  obtain ⟨o1, o2⟩ := lane_mulc n 4611686018427387904 (by norm_num)
  obtain ⟨d1, d2⟩ := lane_add n _ _ c1 r1 (fun i hi => by
    rw [c2 i hi]; have := (r2 i hi).1; norm_num at this ⊢; omega)
  obtain ⟨-, e2⟩ := lane_sub n _ _ d1 o1 (fun i hi => by rw [d2 i hi, c2 i hi, o2 i hi]; omega)
  intro i hi
  obtain ⟨-, h0, h1, h2⟩ := r2 i hi
  have hB := pbOk_B h
  simp only [ite_true] at hB
  rw [e2 i hi, d2 i hi, c2 i hi, o2 i hi]
  have hsv : sv (4611686018427387905 + lane (D3Ck2.psqrt (D3Ck2.oN n) (Nat.sub (Nat.add
      (Nat.mul (D3Ck2.oN n) 4683743612465315840) (Nat.mul (D3Ck2.oN n) 4611686018427387904))
      (D3Ck2.smx K (D3Ck2.oN n) q q))) i - 4611686018427387904) =
      sv (lane (D3Ck2.psqrt (D3Ck2.oN n) (Nat.sub (Nat.add (Nat.mul (D3Ck2.oN n) 4683743612465315840)
        (Nat.mul (D3Ck2.oN n) 4611686018427387904)) (D3Ck2.smx K (D3Ck2.oN n) q q))) i) + 1 := by
    simp only [sv]; push_cast [Nat.add_sub_cancel_left] ; omega
  rw [hsv, abs_mul, abs_of_nonneg (by linarith)]
  nlinarith [abs_nonneg (sv (lane q i))]

end D3Prog
