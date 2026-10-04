import Tammes15.D3Kernel.Kinds.LinDefs

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3Kernel Pent

theorem allBelow_iff (p : ℕ → Bool) (n : ℕ) :
    allBelow p n = true ↔ ∀ j < n, p j = true := by
  induction n with
  | zero =>
      simp [allBelow]
  | succ n ih =>
      simp [allBelow, ih]
      refine ⟨?_, ?_⟩
      · rintro ⟨h, hn⟩ j hj
        rcases Nat.eq_or_lt_of_le hj with (rfl | hj')
        · exact hn
        · exact h j hj'
      · intro h
        exact ⟨fun j hj => h j (Nat.le_of_lt hj), h n (le_refl n)⟩

theorem countBelow_eq (p : ℕ → Bool) (n : ℕ) :
    countBelow p n = ((Finset.range n).filter (fun j => p j = true)).card := by
  induction' n with n ih
  · rfl
  · rw [countBelow, ih]
    have h_range_succ : Finset.range (n + 1) = Finset.cons n (Finset.range n) (by
      intro h; have := (Finset.mem_range.mp h); omega) := by
      ext i; simp [Finset.mem_range]; omega
    rw [h_range_succ, Finset.filter_cons]
    split
    · rw [Finset.card_cons]
    · rfl

lemma countBelow_eq_card_filter (p : ℕ → Bool) (m : ℕ) :
    countBelow p m = ((Finset.range m).filter (fun i => p i)).card := by
  induction' m with m ih
  · rfl
  · have h_range : Finset.range (m + 1) = insert m (Finset.range m) := by
      ext i; simp; omega
    rw [h_range]
    rw [Finset.filter_insert (fun i => p i) m (Finset.range m)]
    by_cases h : p m
    · rw [if_pos h]
      have h_dk1 : countBelow p (m + 1) = countBelow p m + 1 := by
        simp [countBelow, h]
      rw [h_dk1, ih]
      have hm : m ∉ ((Finset.range m).filter (fun i => p i)) := by
        intro hmem
        have hm_mem := (Finset.mem_filter.mp hmem).1
        rw [Finset.mem_range] at hm_mem
        omega
      rw [Finset.card_insert_of_notMem hm]
    · rw [if_neg h]
      have h_dk1 : countBelow p (m + 1) = countBelow p m := by
        simp [countBelow, h]
      rw [h_dk1, ih]

theorem sum_regroup (n m : ℕ) (τ : ℕ → ℕ) (y : ℕ → ℝ) (hτ : ∀ i < m, τ i < n) :
    ∑ q ∈ Finset.range n, (countBelow (fun i => Nat.beq (τ i) q) m : ℝ) * y q =
      ∑ i ∈ Finset.range m, y (τ i) := by
  have h_maps : ∀ i ∈ Finset.range m, τ i ∈ Finset.range n := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    exact hτ i hi
  have h_fiber := Finset.sum_fiberwise_of_maps_to h_maps (fun i => y (τ i))
  rw [← h_fiber]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have h_filter_eq : ((Finset.range m).filter (fun i => τ i = q)) = ((Finset.range m).filter (fun i => Nat.beq (τ i) q)) := by
    ext i; simp
  calc
    (countBelow (fun i => Nat.beq (τ i) q) m : ℝ) * y q
        = (((Finset.range m).filter (fun i => Nat.beq (τ i) q)).card : ℝ) * y q := by
      rw [countBelow_eq_card_filter (fun i => Nat.beq (τ i) q) m]
    _ = (((Finset.range m).filter (fun i => Nat.beq (τ i) q)).card : ℝ) • y q := by
      rw [smul_eq_mul]
    _ = (((Finset.range m).filter (fun i => Nat.beq (τ i) q)).card : ℕ) • y q := by
      simp
    _ = (∑ i ∈ ((Finset.range m).filter (fun i => Nat.beq (τ i) q)), y q) := by
      rw [← Finset.sum_const]
    _ = (∑ i ∈ ((Finset.range m).filter (fun i => τ i = q)), y q) := by rw [h_filter_eq]
    _ = (∑ i ∈ ((Finset.range m).filter (fun i => τ i = q)), y (τ i)) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_filter] at hi
      rw [hi.2]
    _ = ∑ i ∈ Finset.range m with τ i = q, y (τ i) := by rfl

theorem sorted_block (f : ℕ → ℕ) (D o e v : ℕ) (hs : ∀ i, i + 1 < D → f i ≤ f (i + 1))
    (hoe : o < e) (heD : e ≤ D) (ho : o = 0 ∨ f (o - 1) < v) (he : e = D ∨ v < f e)
    (hv : ∀ i < e - o, f (o + i) = v) :
    ∀ i < D, f i = v ↔ o ≤ i ∧ i < e := by
  have hmono : ∀ a b, a ≤ b → b < D → f a ≤ f b := by
    intro a b hle hb
    have hP : ∀ m, a ≤ m → (m < D → f a ≤ f m) := by
      refine Nat.le_induction (fun _ => le_refl (f a)) (fun m hm hPm hm1_lt_D => ?_)
      have hm_lt_D : m < D := lt_trans (Nat.lt_succ_self m) hm1_lt_D
      have hfa_fm : f a ≤ f m := hPm hm_lt_D
      have hfm_fm1 : f m ≤ f (m + 1) := hs m hm1_lt_D
      exact le_trans hfa_fm hfm_fm1
    exact hP b hle hb
  intro i hi
  constructor
  · intro hfi_eq_v
    have ho_le_D : o < D := lt_of_lt_of_le hoe heD
    constructor
    · by_contra! h_not
      rcases ho with (ho0 | h_lt)
      · have : i < 0 := by simpa [ho0] using h_not
        exact Nat.not_lt_zero _ this
      · have h_o_sub_one_lt_D : o - 1 < D := by
          have h_o_sub_one_lt_o : o - 1 < o := by
            by_cases ho0' : o = 0
            · exfalso
              have hi_lt_0 : i < 0 := by simpa [ho0'] using h_not
              exact Nat.not_lt_zero _ hi_lt_0
            · exact Nat.sub_lt (Nat.pos_of_ne_zero ho0') (by omega)
          exact lt_trans h_o_sub_one_lt_o ho_le_D
        have h_le : i ≤ o - 1 := by omega
        have h_fi_le_f_o_sub_one : f i ≤ f (o - 1) := hmono i (o - 1) h_le h_o_sub_one_lt_D
        rw [hfi_eq_v] at h_fi_le_f_o_sub_one
        linarith
    · by_contra! h_not
      rcases he with (heD' | h_lt_v_fe)
      · rw [heD'] at h_not
        omega
      · have he_lt_D : e < D := by
          by_contra! h_eq
          have heq : e = D := by omega
          have : i ≥ D := by omega
          omega
        have h_fe_le_fi : f e ≤ f i := hmono e i h_not hi
        rw [hfi_eq_v] at h_fe_le_fi
        linarith
  · intro ⟨h_le, h_lt⟩
    have h_sub_lt : i - o < e - o := by omega
    calc
      f i = f (o + (i - o)) := by
        rw [add_comm, Nat.sub_add_cancel h_le]
      _ = v := hv (i - o) h_sub_lt

theorem recFin_sound (side nf cc cp cn P Q : ℕ) (xv S : ℝ)
    (hlo : ((cp : ℝ) - cn) * xv + ((P : ℝ) - Q) / 2 ^ 62 ≤ S)
    (hhi : S ≤ ((bP cc : ℝ) - bN cc) / 2 ^ 62)
    (h : recFin side nf cc cp cn P Q = true) :
    (side = 1 → xv ≤ (nf : ℝ) / 2 ^ 62) ∧ (side ≠ 1 → (nf : ℝ) / 2 ^ 62 ≤ xv) := by
  have h2pos : 0 < (2:ℝ) ^ 62 := by positivity
  constructor
  ·
    intro hside

    unfold recFin at h
    simp [hside] at h
    rcases h with ⟨⟨hcn0, hcp_pos⟩, hineq⟩

    subst hcn0

    have h_combined : ((cp : ℝ)) * xv * ((2:ℝ) ^ 62) + ((P : ℝ) - (Q : ℝ)) ≤ (((bP cc : ℕ) : ℝ) - ((bN cc : ℕ) : ℝ)) := by
      have h := le_trans hlo hhi
      linarith

    have hineq' : (Q : ℝ) + ((bP cc : ℕ) : ℝ) ≤ (cp : ℝ) * (nf : ℝ) + (P : ℝ) + ((bN cc : ℕ) : ℝ) := by
      exact_mod_cast hineq

    have h_final : ((cp : ℝ)) * xv * ((2:ℝ) ^ 62) ≤ ((cp : ℝ)) * (nf : ℝ) := by
      have h_mid : ((Q : ℝ) + ((bP cc : ℕ) : ℝ) - (P : ℝ) - ((bN cc : ℕ) : ℝ)) ≤ ((cp : ℝ)) * (nf : ℝ) := by
        linarith
      have h_left : ((cp : ℝ)) * xv * ((2:ℝ) ^ 62) ≤ ((Q : ℝ) + ((bP cc : ℕ) : ℝ) - (P : ℝ) - ((bN cc : ℕ) : ℝ)) := by
        linarith
      linarith

    have hcp_pos' : 0 < (cp : ℝ) := by exact_mod_cast hcp_pos
    have h_div : xv * ((2:ℝ) ^ 62) ≤ (nf : ℝ) := by
      rw [mul_assoc] at h_final
      exact le_of_mul_le_mul_left h_final hcp_pos'

    field_simp
    exact h_div
  ·
    intro hside_ne

    unfold recFin at h

    have hbeq : Nat.beq side 1 = false := by
      by_contra hnot
      have hbeq_true : Nat.beq side 1 = true := by
        cases hb : Nat.beq side 1
        · exfalso; exact hnot hb
        · rfl
      have hside_eq : side = 1 := (Nat.beq_eq.mp hbeq_true)
      exact hside_ne hside_eq
    simp [hbeq] at h
    rcases h with ⟨⟨hcp0, hcn_pos⟩, hineq⟩

    subst hcp0

    have h_combined : (-((cn : ℝ))) * xv * ((2:ℝ) ^ 62) + ((P : ℝ) - (Q : ℝ)) ≤ (((bP cc : ℕ) : ℝ) - ((bN cc : ℕ) : ℝ)) := by
      have h := le_trans hlo hhi
      linarith

    have hineq' : (cn : ℝ) * (nf : ℝ) + (Q : ℝ) + ((bP cc : ℕ) : ℝ) ≤ (P : ℝ) + ((bN cc : ℕ) : ℝ) := by
      exact_mod_cast hineq

    have h_final : ((cn : ℝ)) * (nf : ℝ) ≤ ((cn : ℝ)) * xv * ((2:ℝ) ^ 62) := by
      have h_mid : ((cn : ℝ)) * (nf : ℝ) ≤ ((P : ℝ) + ((bN cc : ℕ) : ℝ) - (Q : ℝ) - ((bP cc : ℕ) : ℝ)) := by
        linarith
      have h_right : ((P : ℝ) + ((bN cc : ℕ) : ℝ) - (Q : ℝ) - ((bP cc : ℕ) : ℝ)) ≤ ((cn : ℝ)) * xv * ((2:ℝ) ^ 62) := by
        linarith
      linarith

    have hcn_pos' : 0 < (cn : ℝ) := by exact_mod_cast hcn_pos
    have h_div : (nf : ℝ) ≤ xv * ((2:ℝ) ^ 62) := by
      rw [mul_assoc] at h_final
      exact le_of_mul_le_mul_left h_final hcn_pos'

    field_simp
    rw [mul_comm]
    exact h_div

theorem emptyFin_sound (cc cp cn P Q : ℕ) (S : ℝ)
    (hlo : ((P : ℝ) - Q) / 2 ^ 62 ≤ S)
    (hhi : S ≤ ((bP cc : ℝ) - bN cc) / 2 ^ 62)
    (h : emptyFin cc cp cn P Q = true) : False := by
  have h_empty : emptyFin cc cp cn P Q = true := h
  unfold emptyFin at h_empty
  have h_lt_nat : Q + bP cc < P + bN cc := by
    simpa [Nat.blt, decide_eq_true] using h_empty
  have h_lt_real : (Q : ℝ) + (bP cc : ℝ) < (P : ℝ) + (bN cc : ℝ) := by
    exact_mod_cast h_lt_nat
  have h_div : ((P : ℝ) - Q) / ((2 : ℝ) ^ 62) ≤ ((bP cc : ℝ) - bN cc) / ((2 : ℝ) ^ 62) :=
    le_trans hlo hhi
  have h_pos : (0 : ℝ) < (2 : ℝ) ^ 62 := by norm_num
  have h_mul : (P : ℝ) - Q ≤ (bP cc : ℝ) - bN cc := by
    nlinarith
  have h_le : (P : ℝ) + (bN cc : ℝ) ≤ (Q : ℝ) + (bP cc : ℝ) := by
    nlinarith
  nlinarith

theorem beq_false_of_ne' {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

def stepB (ih : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (w ng mg Ts' key v cp cn P Q : ℕ) : Bool :=
  if w = v then (if ng = 0 then ih Ts' (cp + mg) cn P Q else ih Ts' cp (cn + mg) P Q)
  else if kgood key = true then
    (if ng = 0 then ih Ts' cp cn (P + mg * kfix key) Q else ih Ts' cp cn P (Q + mg * kfix key))
  else false

theorem linAcc_succ (box v : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool) (n Ts cp cn P Q : ℕ) :
    linAcc box v k (n + 1) Ts cp cn P Q =
      stepB (linAcc box v k n) (tVar Ts 0) (tNeg Ts 0) (tMag Ts 0) (Ts / 2 ^ 10)
        (bk box (2 * tVar Ts 0 + tNeg Ts 0)) v cp cn P Q := by
  have hs : linAcc box v k (n + 1) Ts cp cn P Q =
      (let w := Nat.land Ts (nat_lit 63)
       let ng := Nat.land (Nat.shiftRight Ts (nat_lit 6)) (nat_lit 1)
       let mg := Nat.land (Nat.shiftRight Ts (nat_lit 7)) (nat_lit 7)
       let Ts' := Nat.shiftRight Ts (nat_lit 10)
       let key := bk box (Nat.add (Nat.shiftLeft w (nat_lit 1)) ng)
       @Bool.rec (fun _ => Bool)
         (@Bool.rec (fun _ => Bool) false
             (@Bool.rec (fun _ => Bool) (linAcc box v k n Ts' cp cn P (Nat.add Q (Nat.mul mg (kfix key))))
               (linAcc box v k n Ts' cp cn (Nat.add P (Nat.mul mg (kfix key))) Q) (Nat.beq ng (nat_lit 0)))
             (kgood key))
         (@Bool.rec (fun _ => Bool) (linAcc box v k n Ts' cp (Nat.add cn mg) P Q)
           (linAcc box v k n Ts' (Nat.add cp mg) cn P Q) (Nat.beq ng (nat_lit 0)))
         (Nat.beq w v)) := rfl
  have e1 : Nat.land Ts (nat_lit 63) = tVar Ts 0 := land_shiftRight Ts 0 6
  have e2 : Nat.land (Nat.shiftRight Ts (nat_lit 6)) (nat_lit 1) = tNeg Ts 0 := land_shiftRight Ts 6 1
  have e3 : Nat.land (Nat.shiftRight Ts (nat_lit 7)) (nat_lit 7) = tMag Ts 0 := land_shiftRight Ts 7 3
  have e4 : Nat.shiftRight Ts (nat_lit 10) = Ts / 2 ^ 10 := Nat.shiftRight_eq_div_pow Ts 10
  have e5 : Nat.add (Nat.shiftLeft (tVar Ts 0) (nat_lit 1)) (tNeg Ts 0) = 2 * tVar Ts 0 + tNeg Ts 0 := by
    rw [shl_eq]
    show tVar Ts 0 * 2 ^ 1 + tNeg Ts 0 = 2 * tVar Ts 0 + tNeg Ts 0
    ring
  rw [hs]
  dsimp only
  rw [e1, e2, e3, e4, e5]
  unfold stepB
  by_cases hw : tVar Ts 0 = v
  · have hb : Nat.beq (tVar Ts 0) v = true := by rw [hw]; exact Nat.beq_refl v
    rw [hb, if_pos hw]
    by_cases hn : tNeg Ts 0 = 0
    · have hb' : Nat.beq (tNeg Ts 0) (nat_lit 0) = true := by rw [hn]; rfl
      rw [hb', if_pos hn]
      rfl
    · have hb' : Nat.beq (tNeg Ts 0) (nat_lit 0) = false := by
        exact beq_false_of_ne' hn
      rw [hb', if_neg hn]
      rfl
  · have hb : Nat.beq (tVar Ts 0) v = false := beq_false_of_ne' hw
    rw [hb, if_neg hw]
    cases hg : kgood (bk box (2 * tVar Ts 0 + tNeg Ts 0))
    · rfl
    · by_cases hn : tNeg Ts 0 = 0
      · have hb' : Nat.beq (tNeg Ts 0) (nat_lit 0) = true := by rw [hn]; rfl
        rw [hb', if_pos rfl, if_pos hn]
        rfl
      · have hb' : Nat.beq (tNeg Ts 0) (nat_lit 0) = false := beq_false_of_ne' hn
        rw [hb', if_pos rfl, if_neg hn]
        rfl

theorem tVar_div (Ts q : ℕ) : tVar (Ts / 2 ^ 10) q = tVar Ts (q + 1) := by
  unfold tVar bits
  rw [Nat.div_div_eq_div_mul, ← pow_add, show 10 * (q + 1) = 10 + 10 * q by ring]

theorem tNeg_div (Ts q : ℕ) : tNeg (Ts / 2 ^ 10) q = tNeg Ts (q + 1) := by
  unfold tNeg bits
  rw [Nat.div_div_eq_div_mul, ← pow_add, show 10 * (q + 1) + 6 = 10 + (10 * q + 6) by ring]

theorem tMag_div (Ts q : ℕ) : tMag (Ts / 2 ^ 10) q = tMag Ts (q + 1) := by
  unfold tMag bits
  rw [Nat.div_div_eq_div_mul, ← pow_add, show 10 * (q + 1) + 7 = 10 + (10 * q + 7) by ring]

theorem tCoef_div (Ts q : ℕ) : tCoef (Ts / 2 ^ 10) q = tCoef Ts (q + 1) := by
  unfold tCoef
  rw [tNeg_div, tMag_div]

theorem linAcc_spec (box v : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool) (x : ℕ → ℝ) :
    ∀ (n Ts cp cn P Q : ℕ),
      (∀ q < n, tVar Ts q ≠ v →
        (kgood (bk box (2 * tVar Ts q)) = true →
          (kfix (bk box (2 * tVar Ts q)) : ℝ) / 2 ^ 62 ≤ x (tVar Ts q)) ∧
        (kgood (bk box (2 * tVar Ts q + 1)) = true →
          x (tVar Ts q) ≤ (kfix (bk box (2 * tVar Ts q + 1)) : ℝ) / 2 ^ 62)) →
      linAcc box v k n Ts cp cn P Q = true →
      ∃ cp' cn' P' Q', k cp' cn' P' Q' = true ∧
        ((cp' : ℝ) - cn') * x v + ((P' : ℝ) - Q') / 2 ^ 62 ≤
          ∑ q ∈ Finset.range n, tCoef Ts q * x (tVar Ts q) + ((cp : ℝ) - cn) * x v +
            ((P : ℝ) - Q) / 2 ^ 62 := by
  intro n
  induction n with
  | zero =>
    intro Ts cp cn P Q _ h
    exact ⟨cp, cn, P, Q, h, by simp⟩
  | succ n ih =>
    intro Ts cp cn P Q hx h
    rw [linAcc_succ] at h
    unfold stepB at h
    have hx' : ∀ q < n, tVar (Ts / 2 ^ 10) q ≠ v →
        (kgood (bk box (2 * tVar (Ts / 2 ^ 10) q)) = true →
          (kfix (bk box (2 * tVar (Ts / 2 ^ 10) q)) : ℝ) / 2 ^ 62 ≤ x (tVar (Ts / 2 ^ 10) q)) ∧
        (kgood (bk box (2 * tVar (Ts / 2 ^ 10) q + 1)) = true →
          x (tVar (Ts / 2 ^ 10) q) ≤ (kfix (bk box (2 * tVar (Ts / 2 ^ 10) q + 1)) : ℝ) / 2 ^ 62) := by
      intro q hq hqv
      rw [tVar_div] at hqv ⊢
      exact hx (q + 1) (by omega) hqv
    have hsum : ∑ q ∈ Finset.range (n + 1), tCoef Ts q * x (tVar Ts q) =
        ∑ q ∈ Finset.range n, tCoef (Ts / 2 ^ 10) q * x (tVar (Ts / 2 ^ 10) q) + tCoef Ts 0 * x (tVar Ts 0) := by
      rw [Finset.sum_range_succ']
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      rw [tCoef_div, tVar_div]
    rw [hsum]
    have hmag : (0 : ℝ) ≤ tMag Ts 0 := Nat.cast_nonneg _
    have hng : tNeg Ts 0 < 2 := bits_lt Ts _ 1
    have hpos : tNeg Ts 0 = 0 → tCoef Ts 0 = tMag Ts 0 := fun h0 => by
      unfold tCoef; rw [if_neg (by omega)]
    have hneg : tNeg Ts 0 ≠ 0 → tCoef Ts 0 = -(tMag Ts 0 : ℝ) := fun h0 => by
      unfold tCoef; rw [if_pos (by omega)]
    split_ifs at h with hw hn hg hn'
    · obtain ⟨a, b, c, d, hk, hle⟩ := ih _ _ _ _ _ hx' h
      refine ⟨a, b, c, d, hk, ?_⟩
      rw [hpos hn, hw]
      push_cast at hle ⊢
      linarith
    · obtain ⟨a, b, c, d, hk, hle⟩ := ih _ _ _ _ _ hx' h
      refine ⟨a, b, c, d, hk, ?_⟩
      rw [hneg hn, hw]
      push_cast at hle ⊢
      linarith
    · rw [hn', add_zero] at hg h
      have hb := (hx 0 (by omega) hw).1 hg
      obtain ⟨a, b, c, d, hk, hle⟩ := ih _ _ _ _ _ hx' h
      refine ⟨a, b, c, d, hk, ?_⟩
      have hm := mul_le_mul_of_nonneg_left hb hmag
      rw [hpos hn']
      push_cast at hle ⊢
      have e : (tMag Ts 0 : ℝ) * ((kfix (bk box (2 * tVar Ts 0)) : ℝ) / 2 ^ 62) =
          (tMag Ts 0 : ℝ) * (kfix (bk box (2 * tVar Ts 0)) : ℝ) / 2 ^ 62 := by ring
      linarith
    · have h1 : tNeg Ts 0 = 1 := by omega
      rw [h1] at hg h
      have hb := (hx 0 (by omega) hw).2 hg
      obtain ⟨a, b, c, d, hk, hle⟩ := ih _ _ _ _ _ hx' h
      refine ⟨a, b, c, d, hk, ?_⟩
      have hm := mul_le_mul_of_nonneg_left hb hmag
      rw [hneg hn']
      push_cast at hle ⊢
      have e : (tMag Ts 0 : ℝ) * ((kfix (bk box (2 * tVar Ts 0 + 1)) : ℝ) / 2 ^ 62) =
          (tMag Ts 0 : ℝ) * (kfix (bk box (2 * tVar Ts 0 + 1)) : ℝ) / 2 ^ 62 := by ring
      linarith

theorem two_pi_le_cTPH : 2 * Real.pi ≤ (cTPH : ℝ) / 2 ^ 62 := by
  have h : (6.28318530717958647694 : ℝ) ≤ ((28976077832308491370 : ℕ) : ℝ) / (2 ^ 62 : ℝ) := by
    norm_num
  have := Real.pi_lt_d20
  unfold cTPH
  linarith

theorem cTPL_le_two_pi : (cTPL : ℝ) / 2 ^ 62 ≤ 2 * Real.pi := by
  have h : ((28976077832308491369 : ℕ) : ℝ) / 2 ^ 62 ≤ 2 * (3.14159265358979323846 : ℝ) := by
    norm_num
  have := Real.pi_gt_d20
  unfold cTPL
  linarith

theorem shi_le_cSHI :
    ((373170040409990243346 : ℕ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) ≤ (cSHI : ℝ) / 2 ^ 62 := by
  unfold cSHI
  norm_num

end Tammes15.D3Kernel.Kinds
