import Tammes15.W1Filter.Defs

set_option maxHeartbeats 400000

namespace Tammes15.W1Filter

open Tammes15 Tammes15.D3lp
open scoped Classical

def periodGo (f : Nat → Nat) (i : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, cur, t => if f cur = i then t else periodGo f i fuel (f cur) (t + 1)

def period (f : Nat → Nat) (i : Nat) : Nat := periodGo f i 6 i 1

theorem packBytes_lane (a : Array ℕ) (ha : ∀ x ∈ a, x < 256) (i : ℕ) :
    (packBytes a >>> (8 * i)) % 256 = a.getD i 0 := by
  cases a with | mk l =>
  induction l generalizing i with
  | nil =>
      simp [packBytes]
  | cons x xs ih =>
      have hx : x < 256 := ha x (by simp)
      have hmem : ∀ y, y ∈ ({ toList := xs } : Array ℕ) → y ∈ ({ toList := x :: xs } : Array ℕ) := by
        intro y hy
        have hy' : y ∈ xs := by simpa [Array.mem_def] using hy
        simpa [Array.mem_def] using Or.inr hy'
      have ih_xs := ih i (by
        intro y hy
        exact ha y (hmem y hy))
      simp [packBytes, Array.foldr, Array.getD] at ih_xs ⊢
      set y := List.foldr (fun x_1 x_2 => x_2 * 256 + x_1 % 256) 0 xs with hy_def
      rcases i with (i | i)
      ·
        simp [hx, hy_def]
      · have h8 : (8 : ℕ) * (i + 1) = 8 + 8 * i := by ring
        rw [h8, Nat.shiftRight_add]
        have hshift : (y * 256 + x % 256) >>> 8 = y := by omega
        rw [hshift]
        have ih_i := ih i (by
          intro y' hy'
          have hy'' : y' ∈ xs := by simpa [Array.mem_def] using hy'
          exact ha y' (by simpa [Array.mem_def] using Or.inr hy''))
        simp [packBytes, Array.foldr, Array.getD] at ih_i
        rw [ih_i]
        simp

theorem allFrom_iff (P : ℕ → Bool) (len i : ℕ) :
    allFrom P len i = true ↔ ∀ k, i ≤ k → k < i + len → P k = true := by
  induction' len with len ih generalizing i
  ·
    constructor
    · intro _ k _ hik
      have : i + 0 = i := by omega
      omega
    · intro _
      rfl
  ·
    simp [allFrom]
    constructor
    · intro ⟨hPi, hallFrom⟩ k hik hkk
      by_cases hki : k = i
      · subst hki; exact hPi
      · have hik1 : i + 1 ≤ k := by omega
        have hkbound : k < (i + 1) + len := by omega
        exact (ih (i + 1)).mp hallFrom k hik1 hkbound
    · intro h
      constructor
      · apply h i (by omega) (by omega)
      · apply (ih (i + 1)).mpr
        intro k hik1 hkk
        apply h k (by omega) (by omega)

theorem periodGoA_eq (fa : Array ℕ) (i fuel cur t : ℕ) :
    periodGoA fa i fuel cur t = periodGo (fun k => fa.getD k 0) i fuel cur t := by
  induction fuel generalizing cur t with
  | zero => simp [periodGoA, periodGo]
  | succ fuel ih => simp [periodGoA, periodGo, ih]

theorem countBlock_eq (fa : Array ℕ) (len k t q p : ℕ) :
    countBlock fa len k t q p =
      (t + ((Finset.Ico k (k + len)).filter (fun j => periodGoA fa j 6 j 1 = 3)).card,
       q + ((Finset.Ico k (k + len)).filter (fun j => periodGoA fa j 6 j 1 = 4)).card,
       p + ((Finset.Ico k (k + len)).filter
          (fun j => periodGoA fa j 6 j 1 ≠ 3 ∧ periodGoA fa j 6 j 1 ≠ 4)).card) := by
  induction' len with len ih generalizing k t q p
  ·
    simp [countBlock]
  ·
    have hIco : Finset.Ico k (k + (len + 1)) =
        insert k (Finset.Ico (k + 1) (k + (len + 1))) := by
      ext x; constructor <;> intro h
      · rcases Finset.mem_Ico.1 h with ⟨hx1, hx2⟩
        by_cases hxk : x = k
        · apply Finset.mem_insert.mpr; left; exact hxk
        · apply Finset.mem_insert.mpr; right
          apply Finset.mem_Ico.mpr
          constructor
          · omega
          · omega
      · rcases Finset.mem_insert.1 h with (hx | hx)
        · subst hx; apply Finset.mem_Ico.mpr; constructor <;> omega
        · rcases Finset.mem_Ico.1 hx with ⟨hx1, hx2⟩
          apply Finset.mem_Ico.mpr; constructor <;> omega
    have hk_not_mem : k ∉ Finset.Ico (k + 1) (k + (len + 1)) := by
      intro h; rcases Finset.mem_Ico.1 h with ⟨h1, h2⟩; omega
    rw [hIco]
    have hk_not_mem_filter_3 : k ∉ ((Finset.Ico (k + 1) (k + (len + 1))).filter (fun j => periodGoA fa j 6 j 1 = 3)) := by
      simp [hk_not_mem]
    have hk_not_mem_filter_4 : k ∉ ((Finset.Ico (k + 1) (k + (len + 1))).filter (fun j => periodGoA fa j 6 j 1 = 4)) := by
      simp [hk_not_mem]
    have hk_not_mem_filter_other : k ∉ ((Finset.Ico (k + 1) (k + (len + 1))).filter (fun j => periodGoA fa j 6 j 1 ≠ 3 ∧ periodGoA fa j 6 j 1 ≠ 4)) := by
      simp [hk_not_mem]
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert]
    simp [Finset.card_insert_of_notMem hk_not_mem_filter_3,
          Finset.card_insert_of_notMem hk_not_mem_filter_4,
          Finset.card_insert_of_notMem hk_not_mem_filter_other]
    by_cases hs3 : periodGoA fa k 6 k 1 = 3
    · simp [countBlock, hs3]
      rw [ih (k + 1) (t + 1) q p]
      have hIcoEq : Finset.Ico (k + 1) (k + 1 + len) = Finset.Ico (k + 1) (k + (len + 1)) := by
        rw [add_assoc, add_comm 1 len]
      rw [hIcoEq]
      ext <;> simp [add_comm, add_left_comm, add_assoc]
    · by_cases hs4 : periodGoA fa k 6 k 1 = 4
      · simp [countBlock, hs4]
        rw [ih (k + 1) t (q + 1) p]
        have hIcoEq : Finset.Ico (k + 1) (k + 1 + len) = Finset.Ico (k + 1) (k + (len + 1)) := by
          rw [add_assoc, add_comm 1 len]
        rw [hIcoEq]
        ext <;> simp [add_comm, add_left_comm, add_assoc]
      · simp [countBlock, hs3, hs4]
        rw [ih (k + 1) t q (p + 1)]
        have hIcoEq : Finset.Ico (k + 1) (k + 1 + len) = Finset.Ico (k + 1) (k + (len + 1)) := by
          rw [add_assoc, add_comm 1 len]
        rw [hIcoEq]
        ext <;> simp [add_comm, add_left_comm, add_assoc]

theorem w1Type_iff (t q p : ℕ) : w1Type t q p = true ↔ W1Type t q p := by
  simp [w1Type, W1Type]; omega

lemma periodGo_spec (f : ℕ → ℕ) (i : ℕ) (fuel cur t m : ℕ)
    (hcur : cur = f^[t-1] i) (ht : 1 ≤ t)
    (hnor : ∀ s, 0 < s → s < t → f^[s] i ≠ i)
    (hperiod : periodGo f i fuel cur t = m) (hm : 0 < m) :
    f^[m] i = i ∧ ∀ s, 0 < s → s < m → f^[s] i ≠ i := by
  induction fuel generalizing cur t m with
  | zero =>

    unfold periodGo at hperiod

    have hm0 : m = 0 := by simpa [eq_comm] using hperiod
    rw [hm0] at hm
    exact (Nat.lt_irrefl 0 hm).elim
  | succ fuel ih =>

    unfold periodGo at hperiod
    by_cases heq : f cur = i
    ·

      have hperiod' : t = m := by simpa [heq] using hperiod
      subst hperiod'

      have h_eq : f^[t] i = i := by
        calc
          f^[t] i = f^[(t-1)+1] i := by
            rw [Nat.sub_add_cancel ht]
          _ = f (f^[t-1] i) := by rw [Function.iterate_succ_apply']
          _ = f cur := by rw [hcur]
          _ = i := heq
      exact And.intro h_eq hnor
    ·

      have hperiod' : periodGo f i fuel (f cur) (t + 1) = m := by
        simpa [heq] using hperiod
      have hcur' : f cur = f^[((t + 1) - 1)] i := by
        calc
          f cur = f (f^[t-1] i) := by rw [hcur]
          _ = f^[(t-1).succ] i := by rw [Function.iterate_succ_apply']
          _ = f^[t] i := by
            rw [Nat.succ_eq_add_one, Nat.sub_add_cancel ht]
          _ = f^[((t + 1) - 1)] i := by simp
      have ht' : 1 ≤ t + 1 := by
        exact Nat.le_add_left 1 t
      have hnor' : ∀ s, 0 < s → s < t + 1 → f^[s] i ≠ i := by
        intro s hs_pos hs_lt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs_lt with (hs_lt_t | hs_eq_t)
        · exact hnor s hs_pos hs_lt_t
        ·
          rw [hs_eq_t]

          have hiter : f^[t] i = f cur := by
            calc
              f^[t] i = f^[(t-1)+1] i := by rw [Nat.sub_add_cancel ht]
              _ = f (f^[t-1] i) := by rw [Function.iterate_succ_apply']
              _ = f cur := by rw [hcur]
          rw [hiter]
          exact heq
      have hrec := ih (f cur) (t + 1) m hcur' ht' hnor' hperiod' hm
      exact hrec

theorem period_spec (f : ℕ → ℕ) (i m : ℕ) (h : period f i = m) (hm : 0 < m) :
    f^[m] i = i ∧ ∀ t, 0 < t → t < m → f^[t] i ≠ i := by
  unfold period at h

  apply periodGo_spec f i 6 i 1 m
  ·
    simp
  ·
    exact le_rfl
  ·
    intro s hs_pos hs_lt
    rcases (Nat.lt_one_iff.mp hs_lt) with rfl
    exact (Nat.lt_irrefl 0 hs_pos).elim
  ·
    exact h
  ·
    exact hm

theorem period_eq_zero (f : ℕ → ℕ) (i : ℕ) (h : period f i = 0) :
    ∀ t, 0 < t → t ≤ 6 → f^[t] i ≠ i := by
  have h0 : periodGo f i 6 i 1 = 0 := h
  have hmain : ∀ (fuel t : ℕ) (cur : ℕ), periodGo f i fuel cur t = 0 → (cur = f^[t-1] i) → 1 ≤ t →
      ∀ s, t ≤ s → s < t + fuel → f^[s] i ≠ i := by
    intro fuel
    induction' fuel with fuel ih
    · intro t cur hperiod hcur ht s hts hstf
      have : s < t := by simpa using hstf
      exact (Nat.not_lt.mpr hts this).elim
    · intro t cur hperiod hcur ht s hts hstf
      unfold periodGo at hperiod
      by_cases h_eq : f cur = i
      · rw [if_pos h_eq] at hperiod
        have : 1 ≤ 0 := by simpa [hperiod] using ht
        linarith
      · rw [if_neg h_eq] at hperiod
        have hcur' : f cur = f^[t] i := by
          rw [hcur]
          rw [(Function.iterate_succ_apply' f (t-1) i).symm]
          have : (t - 1).succ = t := by
            rw [Nat.succ_eq_add_one, Nat.sub_add_cancel ht]
          rw [this]
        have h1 : 1 ≤ t + 1 := by omega
        have h_s_base : f^[t] i ≠ i := by
          rw [← hcur']
          exact h_eq
        have h_s_rest : ∀ s, t + 1 ≤ s → s < (t + 1) + fuel → f^[s] i ≠ i :=
          ih (t+1) (f cur) hperiod hcur' h1
        rcases Nat.eq_or_lt_of_le hts with (rfl | h_gt)
        · exact h_s_base
        · apply h_s_rest s (Nat.succ_le_of_lt h_gt)
          simpa [add_comm, add_assoc, add_left_comm] using hstf
  have hcur0 : i = f^[1-1] i := by simp
  have h1le : 1 ≤ 1 := by omega
  have h_s := hmain 6 1 i h0 hcur0 h1le
  intro t htpos hle
  apply h_s t htpos
  omega

theorem period_eq_of_first_return (f : ℕ → ℕ) (i m : ℕ) (hm0 : 0 < m)
    (hm : m ≤ 6) (hret : f^[m] i = i) (hfirst : ∀ t, 0 < t → t < m → f^[t] i ≠ i) :
    period f i = m := by
  unfold period periodGo

  have h_inv : ∀ (fuel cur t : ℕ), cur = f^[t-1] i → 1 ≤ t → t ≤ m → m < t + fuel →
      periodGo f i fuel cur t = m := by
    intro fuel
    induction' fuel with fuel ih
    ·
      intro cur t hcur ht1 htm hfuel
      have h_lt : m < t := by simpa using hfuel
      have : t ≤ m := htm
      omega
    ·
      intro cur t hcur ht1 htm hfuel
      unfold periodGo
      by_cases h_eq : f cur = i
      ·
        rw [if_pos h_eq]
        by_contra h_ne
        have h_lt : t < m := Nat.lt_of_le_of_ne htm h_ne
        have h_iter : f^[t] i = i := by
          calc
            f^[t] i = f^[(t-1)+1] i := by rw [Nat.sub_add_cancel ht1]
            _ = f (f^[t-1] i) := by
              simpa using (congrFun (Function.iterate_succ' f (t-1)) i)
            _ = f cur := by rw [hcur]
            _ = i := h_eq
        exact hfirst t ht1 h_lt h_iter
      ·
        rw [if_neg h_eq]
        have hcur' : f cur = f^[t] i := by
          calc
            f cur = f (f^[t-1] i) := by rw [hcur]
            _ = f^[(t-1)+1] i := by
              simpa using (congrFun (Function.iterate_succ' f (t-1)) i).symm
            _ = f^[t] i := by rw [Nat.sub_add_cancel ht1]
        have h_eq_t : f cur = f^[((t+1)-1)] i := by
          rw [Nat.add_sub_cancel]
          exact hcur'
        have ht1' : 1 ≤ t+1 := by omega
        have htm' : t+1 ≤ m := by
          by_contra h_gt
          have : m ≤ t := by omega
          have h_eq_m : t = m := by omega
          have h_eq_i : f cur = i := by
            rw [hcur', h_eq_m, hret]
          exact h_eq h_eq_i
        have hfuel' : m < (t+1) + fuel := by
          omega
        exact ih (f cur) (t+1) h_eq_t ht1' htm' hfuel'

  have hcur0 : i = f^[0] i := by simp
  have h_1sub1 : (1 : ℕ) - 1 = 0 := by omega
  have hcur0' : i = f^[(1 : ℕ)-1] i := by
    rw [h_1sub1]
    simp
  have hfuel_cond : m < (1 : ℕ) + 6 := by
    omega
  exact h_inv 6 i 1 hcur0' (by omega) (by omega) hfuel_cond

theorem scan_segment (b : ByteArray) (n fuel i v : ℕ) (fst snd off : Array ℕ)
    (l : List ℕ) (hv : v < n) (hl : ∀ x ∈ l, 0 < x ∧ x < 256)
    (hb : ∀ j (hj : j < l.length), b.data[i + j]? = some (l[j]'hj).toUInt8)
    (h0 : b.data[i + l.length]? = some 0) :
    scan b n (fuel + l.length + 1) i v fst snd off =
      scan b n fuel (i + l.length + 1) (v + 1) (fst ++ (List.replicate l.length v).toArray)
        (snd ++ (l.map (· - 1)).toArray) (off.push (fst.size + l.length)) := by
  induction l generalizing fuel i fst snd with
  | nil =>
    have hv' : ¬ n ≤ v := by omega
    have h0i : b.data[i]? = some (0 : UInt8) := by simpa using h0
    have htemp := Array.getElem?_eq_some_iff (xs := b.data) (i := i) (b := (0 : UInt8))
    rcases htemp.mp h0i with ⟨hi_data, hbi⟩
    have hi_size : i < b.size := by
      rw [← ByteArray.size_data]
      exact hi_data
    have hbi_val : (b[i]'hi_size).toNat = 0 := by
      rw [ByteArray.getElem_eq_getElem_data]
      rw [hbi]
      rfl
    simp [scan, hv', hi_size, hbi_val]
  | cons x l ih =>
    have hx_pos : 0 < x := (hl x (by simp)).1
    have hx_lt : x < 256 := (hl x (by simp)).2
    have hv' : ¬ n ≤ v := by omega
    have hbi_data : b.data[i]? = some (x.toUInt8) := by
      have h0len : 0 < (x :: l).length := by simp
      simpa using hb 0 h0len
    have htemp2 := Array.getElem?_eq_some_iff (xs := b.data) (i := i) (b := (x.toUInt8))
    rcases htemp2.mp hbi_data with ⟨hi_data2, hbi2⟩
    have hi_size : i < b.size := by
      rw [← ByteArray.size_data]
      exact hi_data2
    have hx_toNat : ((b[i]'hi_size).toNat : Nat) = x := by
      calc
        ((b[i]'hi_size).toNat : Nat) = ((b.data[i]).toNat : Nat) := rfl
        _ = ((x.toUInt8).toNat : Nat) := by rw [hbi2]
        _ = x := by
          rw [Nat.toUInt8_eq]
          exact UInt8.toNat_ofNat_of_lt hx_lt
    have hx_ne_zero : x ≠ 0 := by omega
    have h_first_step : scan b n (fuel + (x :: l).length + 1) i v fst snd off =
        scan b n (fuel + l.length + 1) (i + 1) v (fst.push v) (snd.push (x - 1)) off := by
      simp [scan, hv', hi_size, hx_toNat, hx_ne_zero, add_comm, add_left_comm, add_assoc]
    have hl_tail : ∀ x' ∈ l, 0 < x' ∧ x' < 256 := by
      intro x' hx'
      exact hl x' (by simp [hx'])
    have hb_tail : ∀ j (hj : j < l.length), b.data[(i + 1) + j]? = some (l[j]'hj).toUInt8 := by
      intro j hj
      have hj' : j + 1 < (x :: l).length := by
        simp [hj]
      have htemp := hb (j + 1) hj'
      simpa [add_comm, add_left_comm, add_assoc] using htemp
    have h0_tail : b.data[(i + 1) + l.length]? = some 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using h0
    have h_ih := ih fuel (i + 1) (fst.push v) (snd.push (x - 1)) hl_tail hb_tail h0_tail
    have h_temp := h_first_step.trans h_ih

    refine h_temp.trans ?_

    have e1 : i + 1 + l.length + 1 = i + (x :: l).length + 1 := by simp; omega
    have e2 : fst.push v ++ (List.replicate l.length v).toArray =
        fst ++ (List.replicate (x :: l).length v).toArray := by
      apply Array.toList_inj.mp; simp [List.replicate_succ]
    have e3 : snd.push (x - 1) ++ (l.map (· - 1)).toArray =
        snd ++ ((x :: l).map (· - 1)).toArray := by
      apply Array.toList_inj.mp; simp
    have e4 : (fst.push v).size + l.length = fst.size + (x :: l).length := by
      simp [Array.size_push]; omega
    rw [e1, e2, e3, e4]

end Tammes15.W1Filter
