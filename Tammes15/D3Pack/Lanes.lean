import Mathlib

namespace D3Dec

def pack (W L : ℕ) (f : ℕ → ℕ) : ℕ := ∑ l ∈ Finset.range L, f l * 2 ^ (W * l)

def guard (W L : ℕ) : ℕ := pack W L fun _ => 2 ^ (W - 1)

def swarLin (c1 c2 c3 X1 X2 X3 Y H : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.mul c1 X1) (Nat.mul c2 X2)) (Nat.mul c3 X3)) H) Y) H) H

def packCert (c : List (ℕ × ℕ)) : ℕ := c.foldr (fun e a => a * 2 ^ 100 + e.1 + e.2 * 2 ^ 20) 0

def walkP {σ : Type} (f : ℕ → ℕ → σ → σ) (z : σ) (c m : ℕ) : σ :=
  Nat.rec (motive := fun _ => σ) z (fun j s => f (c >>> (100 * j) % 2 ^ 20) (c >>> (100 * j + 20) % 2 ^ 80) s) m

def packTerms (B : ℕ) : List (ℕ × ℤ) → ℤ
  | [] => 0
  | (j, c) :: t => c * ((1 <<< (B * j) : ℕ) : ℤ) + packTerms B t

def posVec (B : ℕ) (l : List (ℕ × ℤ)) : ℕ := (l.map fun e => e.2.toNat * 2 ^ (B * e.1)).sum

def negVec (B : ℕ) (l : List (ℕ × ℤ)) : ℕ := (l.map fun e => (-e.2).toNat * 2 ^ (B * e.1)).sum

theorem pack_succ (W L : ℕ) (f : ℕ → ℕ) : pack W (L + 1) f = pack W L f + f L * 2 ^ (W * L) := by
  unfold pack
  rw [Finset.sum_range_succ]

theorem pack_congr (W L : ℕ) (f g : ℕ → ℕ) (h : ∀ l < L, f l = g l) : pack W L f = pack W L g := by
  unfold pack
  refine Finset.sum_congr rfl ?_
  intro l hl
  rw [h l (Finset.mem_range.1 hl)]

theorem pack_add (W L : ℕ) (f g : ℕ → ℕ) : pack W L f + pack W L g = pack W L (fun l => f l + g l) := by
  unfold pack
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← add_mul]

theorem pack_sub (W L : ℕ) (f g : ℕ → ℕ) (h : ∀ l < L, f l ≤ g l) :
    pack W L g - pack W L f = pack W L (fun l => g l - f l) := by
  apply Nat.sub_eq_of_eq_add
  calc pack W L g = pack W L (fun l => (g l - f l) + f l) := by
        apply pack_congr W L g (fun l => (g l - f l) + f l)
        intro l hl
        rw [Nat.sub_add_cancel (h l hl)]
    _ = pack W L (fun l => g l - f l) + pack W L f := by rw [← pack_add]

theorem pack_const_mul (W L k : ℕ) (f : ℕ → ℕ) : k * pack W L f = pack W L (fun l => k * f l) := by
  simp [pack, Finset.mul_sum, mul_assoc]

theorem pack_lt (W L : ℕ) (f : ℕ → ℕ) (h : ∀ l < L, f l < 2 ^ W) : pack W L f < 2 ^ (W * L) := by
  induction L with
  | zero => simp [pack]
  | succ L ih =>
    rw [pack_succ]
    have h1 := ih (fun l hl => h l (Nat.lt_succ_of_lt hl))
    have h2 : f L + 1 ≤ 2 ^ W := h L (Nat.lt_succ_self L)
    have h3 : 2 ^ (W * (L + 1)) = 2 ^ W * 2 ^ (W * L) := by
      rw [mul_add, mul_one, pow_add, mul_comm]
    rw [h3]
    calc pack W L f + f L * 2 ^ (W * L) < 2 ^ (W * L) + f L * 2 ^ (W * L) := by omega
      _ = (f L + 1) * 2 ^ (W * L) := by ring
      _ ≤ 2 ^ W * 2 ^ (W * L) := Nat.mul_le_mul_right _ h2

theorem pack_div_mod (W L : ℕ) (f : ℕ → ℕ) (h : ∀ l < L, f l < 2 ^ W) (l : ℕ) (hl : l < L) :
    pack W L f / 2 ^ (W * l) % 2 ^ W = f l := by
  induction L with
  | zero => omega
  | succ L ih =>
    rw [pack_succ]
    have hpos : 0 < 2 ^ (W * l) := Nat.pos_of_ne_zero (by positivity)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hlt | heq
    · have hih := ih (fun m hm => h m (Nat.lt_succ_of_lt hm)) hlt
      have hsplit : 2 ^ (W * L) = 2 ^ (W * l) * (2 ^ W * 2 ^ (W * (L - l - 1))) := by
        rw [← pow_add, ← pow_add]
        congr 1
        have : L = l + 1 + (L - l - 1) := by omega
        conv_lhs => rw [this]
        ring
      rw [hsplit, show f L * (2 ^ (W * l) * (2 ^ W * 2 ^ (W * (L - l - 1)))) =
          f L * (2 ^ W * 2 ^ (W * (L - l - 1))) * 2 ^ (W * l) by ring, Nat.add_mul_div_right _ _ hpos,
        show f L * (2 ^ W * 2 ^ (W * (L - l - 1))) = 2 ^ W * (f L * 2 ^ (W * (L - l - 1))) by ring,
        Nat.add_mul_mod_self_left, hih]
    · subst heq
      have hA := pack_lt W l f (fun m hm => h m (Nat.lt_succ_of_lt hm))
      rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hA, zero_add]
      exact Nat.mod_eq_of_lt (h l (Nat.lt_succ_self l))

theorem testBit_pack (W L : ℕ) (f : ℕ → ℕ) (hW : 0 < W) (h : ∀ l < L, f l < 2 ^ W) (n : ℕ) :
    (pack W L f).testBit n = if n / W < L then (f (n / W)).testBit (n % W) else false := by
  split_ifs with hn
  · have hmod : n % W < W := Nat.mod_lt _ hW
    have e : n = n % W + W * (n / W) := by rw [Nat.add_comm, Nat.div_add_mod]
    rw [← pack_div_mod W L f h (n / W) hn, Nat.testBit_mod_two_pow, decide_eq_true hmod, Bool.true_and,
      Nat.testBit_div_two_pow, ← e]
  · have hle : W * L ≤ n := by
      have := (Nat.le_div_iff_mul_le hW).1 (not_lt.1 hn)
      linarith [mul_comm L W]
    exact Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le (pack_lt W L f h) (Nat.pow_le_pow_right (by norm_num) hle))

theorem land_pack (W L : ℕ) (f g : ℕ → ℕ) (hW : 0 < W) (hf : ∀ l < L, f l < 2 ^ W)
    (hg : ∀ l < L, g l < 2 ^ W) : pack W L f &&& pack W L g = pack W L (fun l => f l &&& g l) := by
  have hfg : ∀ l < L, (f l &&& g l) < 2 ^ W := fun l hl => Nat.and_lt_two_pow _ (hg l hl)
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_land, testBit_pack W L f hW hf, testBit_pack W L g hW hg, testBit_pack W L _ hW hfg]
  split_ifs <;> simp

theorem xor_pack (W L : ℕ) (f g : ℕ → ℕ) (hW : 0 < W) (hf : ∀ l < L, f l < 2 ^ W)
    (hg : ∀ l < L, g l < 2 ^ W) : pack W L f ^^^ pack W L g = pack W L (fun l => f l ^^^ g l) := by
  have hfg : ∀ l < L, (f l ^^^ g l) < 2 ^ W := fun l hl => Nat.xor_lt_two_pow (hf l hl) (hg l hl)
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_xor, testBit_pack W L f hW hf, testBit_pack W L g hW hg, testBit_pack W L _ hW hfg]
  split_ifs <;> simp [Nat.testBit_xor]

theorem land_two_pow (W z : ℕ) (hW : 0 < W) (hz : z < 2 ^ W) :
    z &&& 2 ^ (W - 1) = if 2 ^ (W - 1) ≤ z then 2 ^ (W - 1) else 0 := by
  have hp : 2 ^ W = 2 ^ (W - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hW]
  have hbit : z.testBit (W - 1) = decide (2 ^ (W - 1) ≤ z) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have h2 : z / 2 ^ (W - 1) < 2 := (Nat.div_lt_iff_lt_mul (by positivity)).2 (by rw [mul_comm, ← hp]; exact hz)
    by_cases hc : 2 ^ (W - 1) ≤ z
    · have : 1 ≤ z / 2 ^ (W - 1) := (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa using hc)
      simp [hc, Nat.mod_eq_of_lt h2]; omega
    · have : z / 2 ^ (W - 1) = 0 := Nat.div_eq_of_lt (not_le.1 hc)
      simp [hc, this]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_two_pow]
  by_cases hi : W - 1 = i
  · subst hi
    split_ifs with hc <;> simp [hbit, hc]
  · split_ifs <;> simp [hi]

theorem land_guard (W L : ℕ) (f : ℕ → ℕ) (hW : 0 < W) (h : ∀ l < L, f l < 2 ^ W) :
    pack W L f &&& guard W L = pack W L (fun l => if 2 ^ (W - 1) ≤ f l then 2 ^ (W - 1) else 0) := by
  have hg : ∀ l < L, (fun _ => 2 ^ (W - 1)) l < 2 ^ W := fun _ _ =>
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [guard, land_pack W L f _ hW h hg]
  exact pack_congr W L _ _ fun l hl => land_two_pow W (f l) hW (h l hl)

theorem pack_inj (W L : ℕ) (f g : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ W) (hg : ∀ l < L, g l < 2 ^ W) :
    pack W L f = pack W L g ↔ ∀ l < L, f l = g l := by
  constructor
  · intro e l hl
    rw [← pack_div_mod W L f hf l hl, ← pack_div_mod W L g hg l hl, e]
  · exact pack_congr W L f g

theorem land_guard_eq_iff (W L : ℕ) (f : ℕ → ℕ) (hW : 0 < W) (h : ∀ l < L, f l < 2 ^ W) :
    pack W L f &&& guard W L = guard W L ↔ ∀ l < L, 2 ^ (W - 1) ≤ f l := by
  have hlt : 2 ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hne : 2 ^ (W - 1) ≠ 0 := by positivity
  rw [land_guard W L f hW h, guard, pack_inj W L _ _ (fun l _ => by split_ifs <;> omega) (fun _ _ => hlt)]
  refine forall_congr' fun l => imp_congr_right fun _ => ?_
  split_ifs with hc
  · simp [hc]
  · simp only [hc, iff_false]
    exact fun e => hne e.symm

theorem swarLin_iff (N c1 c2 c3 : ℕ) (x1 x2 x3 y : ℕ → ℕ)
    (hs : ∀ i < N, c1 * x1 i + c2 * x2 i + c3 * x3 i < 2 ^ 63) (hy : ∀ i < N, y i < 2 ^ 63) :
    swarLin c1 c2 c3 (pack 64 N x1) (pack 64 N x2) (pack 64 N x3) (pack 64 N y) (guard 64 N) = true ↔
      ∀ i < N, y i ≤ c1 * x1 i + c2 * x2 i + c3 * x3 i := by
  set s : ℕ → ℕ := fun i => c1 * x1 i + c2 * x2 i + c3 * x3 i with hs_def
  have hS : c1 * pack 64 N x1 + c2 * pack 64 N x2 + c3 * pack 64 N x3 = pack 64 N s := by
    rw [pack_const_mul, pack_const_mul, pack_const_mul, pack_add, pack_add]
  have hG : pack 64 N s + guard 64 N = pack 64 N (fun i => s i + 2 ^ 63) := by
    rw [guard, pack_add]
  have hsub : pack 64 N (fun i => s i + 2 ^ 63) - pack 64 N y = pack 64 N (fun i => s i + 2 ^ 63 - y i) :=
    pack_sub 64 N y _ fun i hi => by have := hy i hi; show y i ≤ s i + 2 ^ 63; omega
  have hb : ∀ i < N, s i + 2 ^ 63 - y i < 2 ^ 64 := fun i hi => by
    have := hs i hi; simp only [hs_def] at this ⊢; omega
  show (Nat.beq ((c1 * pack 64 N x1 + c2 * pack 64 N x2 + c3 * pack 64 N x3 + guard 64 N - pack 64 N y) &&&
    guard 64 N) (guard 64 N) = true) ↔ _
  rw [Nat.beq_eq, hS, hG, hsub, land_guard_eq_iff 64 N _ (by norm_num) hb]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  have := hy i hi
  simp only [hs_def]
  constructor <;> intro hc <;> omega

theorem halves (K a b : ℕ) (ha : a < 2 ^ K) : (a + b * 2 ^ K) % 2 ^ K = a ∧ (a + b * 2 ^ K) >>> K = b := by
  have hp : 0 < 2 ^ K := by positivity
  refine ⟨by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha], ?_⟩
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ha, zero_add]

theorem fields3 (H a b c : ℕ) (ha : a < 2 ^ H) (hb : b < 2 ^ H) :
    (a + b * 2 ^ H + c * 2 ^ (2 * H)) % 2 ^ H = a ∧ (a + b * 2 ^ H + c * 2 ^ (2 * H)) >>> H % 2 ^ H = b ∧
      (a + b * 2 ^ H + c * 2 ^ (2 * H)) >>> (2 * H) = c := by
  have hp : 0 < 2 ^ H := by positivity
  have e : a + b * 2 ^ H + c * 2 ^ (2 * H) = a + (b + c * 2 ^ H) * 2 ^ H := by rw [two_mul, pow_add]; ring
  have e2 : (a + (b + c * 2 ^ H) * 2 ^ H) / 2 ^ H = b + c * 2 ^ H := by
    rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ha, zero_add]
  rw [e]
  refine ⟨by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha], ?_, ?_⟩
  · rw [Nat.shiftRight_eq_div_pow, e2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  · rw [Nat.shiftRight_eq_div_pow, two_mul, pow_add, ← Nat.div_div_eq_div_mul, e2,
      Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hb, zero_add]

theorem walkP_eq_foldl {σ : Type} (f : ℕ → ℕ → σ → σ) (z : σ) (c m : ℕ) :
    walkP f z c m = (List.range m).foldl (fun s j => f (c >>> (100 * j) % 2 ^ 20) (c >>> (100 * j + 20) % 2 ^ 80) s) z := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ← ih]
    rfl

theorem pack_mul_pow (W L s : ℕ) (f : ℕ → ℕ) :
    pack W L f * 2 ^ (W * s) = pack W (L + s) (fun l => if s ≤ l then f (l - s) else 0) := by
  unfold pack
  rw [add_comm L s, Finset.sum_range_add, Finset.sum_mul]
  beta_reduce
  have h0 : ∑ x ∈ Finset.range s, (if s ≤ x then f (x - s) else 0) * 2 ^ (W * x) = 0 :=
    Finset.sum_eq_zero fun l hl => by
      have : ¬ s ≤ l := by simp at hl; omega
      simp [this]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [le_add_iff_nonneg_right, zero_le, ite_true, Nat.add_sub_cancel_left]
  rw [mul_assoc, ← pow_add, mul_add, add_comm (W * l)]

theorem ones_div (W L : ℕ) (hW : 0 < W) : (2 ^ (W * L) - 1) / (2 ^ W - 1) = pack W L (fun _ => 1) := by
  have h2 : 2 ≤ 2 ^ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hg : pack W L (fun _ => 1) = ∑ l ∈ Finset.range L, (2 ^ W) ^ l := by
    unfold pack
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [one_mul, pow_mul]
  rw [hg, Nat.geomSum_eq h2, pow_mul]

theorem packTerms_eq (B : ℕ) (l : List (ℕ × ℤ)) : packTerms B l = (posVec B l : ℤ) - negVec B l := by
  induction l with
  | nil => simp [packTerms, posVec, negVec]
  | cons e t ih =>
    obtain ⟨j, c⟩ := e
    simp only [packTerms, posVec, negVec, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.shiftLeft_eq, one_mul]
    push_cast
    have hc : c = (c.toNat : ℤ) - ((-c).toNat : ℤ) := (Int.toNat_sub_toNat_neg c).symm
    conv_lhs => rw [hc]
    ring

theorem zero_mask (W L : ℕ) (t : ℕ → ℕ) (hW : 2 ≤ W) (ht : ∀ l < L, t l < 2 ^ (W - 1)) :
    (pack W L t + (guard W L - pack W L (fun _ => 1))) &&& guard W L =
      pack W L (fun l => if t l = 0 then 0 else 2 ^ (W - 1)) := by
  have h1 : 1 ≤ 2 ^ (W - 1) := Nat.one_le_two_pow
  have hp : 2 ^ W = 2 ^ (W - 1) + 2 ^ (W - 1) := by
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ W)]
  have hsub : guard W L - pack W L (fun _ => 1) = pack W L (fun _ => 2 ^ (W - 1) - 1) :=
    pack_sub W L (fun _ => 1) (fun _ => 2 ^ (W - 1)) fun _ _ => h1
  rw [hsub, pack_add, land_guard W L _ (by omega) fun l hl => by
    have := ht l hl
    show t l + (2 ^ (W - 1) - 1) < 2 ^ W
    omega]
  refine pack_congr W L _ _ fun l hl => ?_
  have := ht l hl
  split_ifs <;> omega

theorem packCert_cons (e : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    packCert (e :: l) = e.1 + e.2 * 2 ^ 20 + packCert l * 2 ^ 100 := by
  have h : packCert (e :: l) = packCert l * 2 ^ 100 + e.1 + e.2 * 2 ^ 20 := by
    rw [packCert, packCert, List.foldr_cons]
  rw [h, Nat.add_assoc, Nat.add_comm]

theorem packCert_field (l : List (ℕ × ℕ)) (hl : ∀ e ∈ l, e.1 < 2 ^ 20 ∧ e.2 < 2 ^ 80) (j : ℕ)
    (hj : j < l.length) :
    packCert l >>> (100 * j) % 2 ^ 20 = l[j].1 ∧ packCert l >>> (100 * j + 20) % 2 ^ 80 = l[j].2 := by
  induction l generalizing j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons e t ih =>
    have he := hl e (List.mem_cons_self ..)
    have hent : e.1 + e.2 * 2 ^ 20 < 2 ^ 100 := by
      calc e.1 + e.2 * 2 ^ 20 < 2 ^ 20 + e.2 * 2 ^ 20 := Nat.add_lt_add_right he.1 _
        _ = (e.2 + 1) * 2 ^ 20 := by rw [Nat.add_mul, one_mul, Nat.add_comm]
        _ ≤ 2 ^ 80 * 2 ^ 20 := Nat.mul_le_mul_right _ he.2
        _ = 2 ^ 100 := by rw [← pow_add]
    have hp20 : 0 < 2 ^ 20 := by positivity
    have hp100 : 0 < 2 ^ 100 := by positivity
    have hdiv : packCert (e :: t) / 2 ^ 100 = packCert t := by
      rw [packCert_cons, Nat.add_mul_div_right _ _ hp100, Nat.div_eq_of_lt hent, Nat.zero_add]
    have e100 : (2 : ℕ) ^ 100 = 2 ^ 80 * 2 ^ 20 := by rw [← pow_add]
    have hsplit : packCert (e :: t) = e.1 + (e.2 + packCert t * 2 ^ 80) * 2 ^ 20 := by
      rw [packCert_cons, e100, Nat.add_mul, ← Nat.mul_assoc, Nat.add_assoc]
    cases j with
    | zero =>
      rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.zero_add, List.getElem_cons_zero, hsplit,
        Nat.shiftRight_eq_div_pow, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he.1,
        Nat.add_mul_div_right _ _ hp20, Nat.div_eq_of_lt he.1, Nat.zero_add, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt he.2]
      exact ⟨rfl, rfl⟩
    | succ j =>
      have hj' : j < t.length := Nat.lt_of_succ_lt_succ hj
      have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) j hj'
      have s1 : packCert (e :: t) >>> (100 * (j + 1)) = packCert t >>> (100 * j) := by
        rw [show 100 * (j + 1) = 100 + 100 * j by omega, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow _ 100, hdiv]
      have s2 : packCert (e :: t) >>> (100 * (j + 1) + 20) = packCert t >>> (100 * j + 20) := by
        rw [show 100 * (j + 1) + 20 = 100 + (100 * j + 20) by omega, Nat.shiftRight_add,
          Nat.shiftRight_eq_div_pow _ 100, hdiv]
      rw [s1, s2]
      exact ih'

end D3Dec

#print axioms D3Dec.pack_succ
#print axioms D3Dec.pack_congr
#print axioms D3Dec.pack_add
#print axioms D3Dec.pack_sub
#print axioms D3Dec.pack_const_mul
#print axioms D3Dec.pack_lt
#print axioms D3Dec.pack_div_mod
#print axioms D3Dec.testBit_pack
#print axioms D3Dec.land_pack
#print axioms D3Dec.xor_pack
#print axioms D3Dec.land_two_pow
#print axioms D3Dec.land_guard
#print axioms D3Dec.pack_inj
#print axioms D3Dec.land_guard_eq_iff
#print axioms D3Dec.swarLin_iff
#print axioms D3Dec.halves
#print axioms D3Dec.fields3
#print axioms D3Dec.walkP_eq_foldl
#print axioms D3Dec.pack_mul_pow
#print axioms D3Dec.ones_div
#print axioms D3Dec.packTerms_eq
#print axioms D3Dec.zero_mask
#print axioms D3Dec.packCert_cons
#print axioms D3Dec.packCert_field
