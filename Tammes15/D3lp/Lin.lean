import Mathlib

namespace Tammes15.D3lp

structure Row where
  terms : List (ℕ × ℤ)
  rhs : ℤ
  deriving Repr, DecidableEq

noncomputable def evalTerms (t : List (ℕ × ℤ)) (x : ℕ → ℝ) : ℝ :=
  (t.map fun q => (q.2 : ℝ) * x q.1).sum

def Row.Holds (r : Row) (x : ℕ → ℝ) : Prop :=
  evalTerms r.terms x ≤ r.rhs

def rhsSum (rows : List (ℕ × Row)) : ℤ :=
  (rows.map fun q => (q.1 : ℤ) * q.2.rhs).sum

def insertAdd (j : ℕ) (c : ℤ) : List (ℕ × ℤ) → List (ℕ × ℤ)
  | [] => [(j, c)]
  | (i, a) :: s =>
    if j < i then (j, c) :: (i, a) :: s
    else if j = i then (i, a + c) :: s
    else (i, a) :: insertAdd j c s

def addScaled (y : ℤ) : List (ℕ × ℤ) → List (ℕ × ℤ) → List (ℕ × ℤ)
  | [], acc => acc
  | (j, c) :: t, acc => addScaled y t (insertAdd j (y * c) acc)

def combine : List (ℕ × Row) → List (ℕ × ℤ) → List (ℕ × ℤ)
  | [], acc => acc
  | (y, r) :: rows, acc => combine rows (addScaled y r.terms acc)

def farkasCheck (rows : List (ℕ × Row)) : Bool :=
  (combine rows []).all (fun q => q.2 == 0) && decide (rhsSum rows < 0)

noncomputable def combSum (rows : List (ℕ × Row)) (x : ℕ → ℝ) : ℝ :=
  (rows.map fun q => (q.1 : ℝ) * evalTerms q.2.terms x).sum

theorem evalTerms_nil (x : ℕ → ℝ) : evalTerms [] x = 0 := by
  simp [evalTerms]

theorem evalTerms_cons (j : ℕ) (c : ℤ) (t : List (ℕ × ℤ)) (x : ℕ → ℝ) :
    evalTerms ((j, c) :: t) x = c * x j + evalTerms t x := by
  simp [evalTerms]

theorem insertAdd_eval (j : ℕ) (c : ℤ) (acc : List (ℕ × ℤ)) (x : ℕ → ℝ) :
    evalTerms (insertAdd j c acc) x = c * x j + evalTerms acc x := by
  induction acc with
  | nil =>
    simp [insertAdd, evalTerms]
  | cons p s ih =>
    rcases p with ⟨i, a⟩
    simp [insertAdd]
    split
    ·
      simp [evalTerms, List.map_cons, List.sum_cons]
    · split
      ·
        subst i
        simp [evalTerms, List.map_cons, List.sum_cons]
        ring
      ·
        simp [evalTerms, List.map_cons, List.sum_cons]
        unfold evalTerms at ih
        rw [ih]
        ring

theorem addScaled_eval (y : ℤ) (t acc : List (ℕ × ℤ)) (x : ℕ → ℝ) :
    evalTerms (addScaled y t acc) x = y * evalTerms t x + evalTerms acc x := by
  induction t generalizing acc with
  | nil =>
    simp [addScaled, evalTerms]
  | cons hd tl ih =>
    rcases hd with ⟨j, c⟩
    simp only [addScaled]
    rw [ih, insertAdd_eval]
    simp [evalTerms, List.map_cons, List.sum_cons]
    ring

theorem combine_eval (rows : List (ℕ × Row)) (acc : List (ℕ × ℤ)) (x : ℕ → ℝ) :
    evalTerms (combine rows acc) x = combSum rows x + evalTerms acc x := by
  induction rows generalizing acc
  case nil => simp [combine, combSum]
  case cons yhr rows ih =>
    rcases yhr with ⟨y, r⟩
    simp [combine]
    rw [ih (addScaled y r.terms acc)]
    rw [addScaled_eval (y : ℤ) r.terms acc x]
    push_cast
    unfold combSum
    simp [List.map_cons, List.sum_cons]
    abel

theorem evalTerms_eq_zero_of_all (t : List (ℕ × ℤ)) (h : t.all (fun q => q.2 == 0) = true)
    (x : ℕ → ℝ) : evalTerms t x = 0 := by
  rw [evalTerms]
  apply List.sum_eq_zero
  intro y hy
  rcases List.mem_map.mp hy with ⟨q, hq, rfl⟩
  have hq2 : q.2 = 0 := by
    have := (List.all_eq_true.mp h) q hq
    simpa using this
  simp [hq2]

theorem combSum_le_rhsSum (rows : List (ℕ × Row)) (x : ℕ → ℝ) (hx : ∀ q ∈ rows, q.2.Holds x) :
    combSum rows x ≤ rhsSum rows := by
  induction' rows with q rows ih
  · simp [combSum, rhsSum]
  · rcases q with ⟨y, r⟩
    have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg _
    have hx_tail : ∀ q ∈ rows, q.2.Holds x := by
      intro q' hq'
      exact hx q' (by simp [hq'])
    have hr := hx (y, r) (by simp)
    have h_mul : (y : ℝ) * evalTerms r.terms x ≤ (y : ℝ) * (r.rhs : ℝ) :=
      mul_le_mul_of_nonneg_left hr hy
    have ih' : combSum rows x ≤ (rhsSum rows : ℝ) := ih hx_tail
    simpa [combSum, rhsSum, evalTerms] using add_le_add h_mul ih'

theorem farkasCheck_sound (rows : List (ℕ × Row)) (h : farkasCheck rows = true)
    (x : ℕ → ℝ) (hx : ∀ q ∈ rows, q.2.Holds x) : False := by
  simp only [farkasCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have h0 := combine_eval rows [] x
  rw [evalTerms_eq_zero_of_all _ h.1 x, evalTerms_nil, add_zero] at h0
  have h1 := combSum_le_rhsSum rows x hx
  have h2 : (rhsSum rows : ℝ) < 0 := by exact_mod_cast h.2
  linarith

def packTerms (B : ℕ) : List (ℕ × ℤ) → ℤ
  | [] => 0
  | (j, c) :: t => c * ((1 <<< (B * j) : ℕ) : ℤ) + packTerms B t

def l1Terms : List (ℕ × ℤ) → ℕ
  | [] => 0
  | (_, c) :: t => c.natAbs + l1Terms t

def packSum (B : ℕ) : List (ℕ × Row) → ℤ
  | [] => 0
  | (y, r) :: rows => (y : ℤ) * packTerms B r.terms + packSum B rows

def l1Sum : List (ℕ × Row) → ℕ
  | [] => 0
  | (y, r) :: rows => y * l1Terms r.terms + l1Sum rows

def farkasPacked (B : ℕ) (rows : List (ℕ × Row)) : Bool :=
  packSum B rows == 0 && Nat.blt (l1Sum rows) (1 <<< B) && decide (rhsSum rows < 0)

def flat (rows : List (ℕ × Row)) : List (ℕ × ℤ) :=
  rows.flatMap fun q => q.2.terms.map fun t => (t.1, (q.1 : ℤ) * t.2)

def coefOf (t : List (ℕ × ℤ)) (j : ℕ) : ℤ :=
  ((t.filter fun q => q.1 = j).map (·.2)).sum

open Tammes15 Tammes15.D3lp
open scoped Classical

lemma packTerms_append (B : ℕ) (s t : List (ℕ × ℤ)) : packTerms B (s ++ t) = packTerms B s + packTerms B t := by
  induction' s with p s ih
  · simp [packTerms]
  · rcases p with ⟨j, c⟩
    simp [packTerms, ih]
    ring

lemma packTerms_map_mul (B : ℕ) (y : ℤ) (t : List (ℕ × ℤ)) :
    packTerms B (t.map fun q => (q.1, y * q.2)) = y * packTerms B t := by
  induction' t with p t ih
  · simp [packTerms]
  · rcases p with ⟨j, c⟩
    simp [packTerms, ih]
    ring

theorem packSum_eq_packTerms_flat (B : ℕ) (rows : List (ℕ × Row)) :
    packSum B rows = packTerms B (flat rows) := by
  induction' rows with yr rows ih
  · rfl
  · rcases yr with ⟨y, r⟩
    simp [packSum, flat, List.flatMap_cons, ih]
    calc
      (y : ℤ) * packTerms B r.terms + packTerms B (flat rows) =
          (y : ℤ) * packTerms B r.terms + packTerms B (flat rows) := rfl
      _ = packTerms B (r.terms.map fun q => (q.1, (y : ℤ) * q.2)) + packTerms B (flat rows) := by
        rw [packTerms_map_mul B (y : ℤ) r.terms]
      _ = packTerms B ((r.terms.map fun q => (q.1, (y : ℤ) * q.2)) ++ flat rows) := by
        rw [packTerms_append B _ _]
      _ = packTerms B (flat ((y, r) :: rows)) := by
        simp [flat, List.flatMap_cons]

open Tammes15 Tammes15.D3lp
open scoped Classical

private lemma l1Terms_append (l1 l2 : List (ℕ × ℤ)) : l1Terms (l1 ++ l2) = l1Terms l1 + l1Terms l2 := by
  induction' l1 with a l1 ih generalizing l2
  · simp [l1Terms]
  · simp [l1Terms, List.cons_append, ih, add_assoc]

private lemma l1Sum_append (rows1 rows2 : List (ℕ × Row)) : l1Sum (rows1 ++ rows2) = l1Sum rows1 + l1Sum rows2 := by
  induction' rows1 with p rows1 ih generalizing rows2
  · simp [l1Sum]
  · simp [l1Sum, List.cons_append, ih, add_assoc]

private lemma flat_append (rows1 rows2 : List (ℕ × Row)) : flat (rows1 ++ rows2) = flat rows1 ++ flat rows2 := by
  simp [flat, List.flatMap_append]

private lemma l1Terms_flat_single (y : ℕ) (r : Row) : l1Terms (flat [(y, r)]) = y * l1Terms r.terms := by
  simp [flat]
  induction' r.terms with t ts ih
  · simp [l1Terms]
  · rw [List.map_cons, l1Terms, l1Terms]
    rw [ih]
    simp [Int.natAbs_mul, mul_comm, Nat.mul_add]

theorem l1Terms_flat (rows : List (ℕ × Row)) : l1Terms (flat rows) ≤ l1Sum rows := by
  induction' rows with p rows ih
  · rfl
  · rcases p with ⟨y, r⟩
    have hflat : flat ((y, r) :: rows) = flat [(y, r)] ++ flat rows := by
      simp [flat, List.flatMap_cons]
    rw [hflat, l1Terms_append]

    rw [l1Terms_flat_single y r]

    simpa [l1Sum] using add_le_add_right ih (y * l1Terms r.terms)

theorem evalTerms_flat (rows : List (ℕ × Row)) (x : ℕ → ℝ) :
    evalTerms (flat rows) x = combSum rows x := by
  induction rows with
  | nil =>
      simp [evalTerms, combSum, flat]
  | cons q rows ih =>

      simp only [evalTerms, combSum, flat, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]

      rw [List.map_map (g := fun (q' : ℕ × ℤ) => (q'.2 : ℝ) * x q'.1) (f := fun (t : ℕ × ℤ) => (t.1, (q.1 : ℤ) * t.2))]

      have h_comp : ((fun (q' : ℕ × ℤ) => (q'.2 : ℝ) * x q'.1) ∘ fun (t : ℕ × ℤ) => (t.1, (q.1 : ℤ) * t.2)) =
          (fun (t : ℕ × ℤ) => ((q.1 : ℝ) * (t.2 : ℝ)) * x t.1) := by
        ext t; simp
      rw [h_comp]
      have h_map_mul : (List.map (fun (t : ℕ × ℤ) => ((q.1 : ℝ) * (t.2 : ℝ)) * x t.1) q.2.terms).sum =
          (q.1 : ℝ) * (List.map (fun (t : ℕ × ℤ) => (t.2 : ℝ) * x t.1) q.2.terms).sum := by
        calc
          (List.map (fun (t : ℕ × ℤ) => ((q.1 : ℝ) * (t.2 : ℝ)) * x t.1) q.2.terms).sum
              = (List.map (fun (t : ℕ × ℤ) => (q.1 : ℝ) * ((t.2 : ℝ) * x t.1)) q.2.terms).sum := by
            congr; ext t; ring
          _ = (q.1 : ℝ) * (List.map (fun (t : ℕ × ℤ) => (t.2 : ℝ) * x t.1) q.2.terms).sum := by
            rw [List.sum_map_mul_left]
      rw [h_map_mul]

      have h_eq := ih

      simpa [evalTerms, combSum, flat] using congrArg (fun t => (q.1 : ℝ) * (List.map (fun (t : ℕ × ℤ) => (t.2 : ℝ) * x t.1) q.2.terms).sum + t) h_eq

theorem natAbs_coefOf_le (t : List (ℕ × ℤ)) (j : ℕ) : (coefOf t j).natAbs ≤ l1Terms t := by
  induction t with
  | nil =>
      simp [coefOf, l1Terms]
  | cons p t ih =>
      rcases p with ⟨i, c⟩
      unfold coefOf l1Terms
      simp only [List.filter_cons]
      by_cases h : i = j
      ·
        simp [h]
        have h_abs := Int.natAbs_add_le c (coefOf t j)
        have hcoef : (coefOf t j).natAbs ≤ l1Terms t := ih
        have h_sum : c.natAbs + (coefOf t j).natAbs ≤ c.natAbs + l1Terms t :=
          Nat.add_le_add_left hcoef c.natAbs
        exact Nat.le_trans h_abs h_sum
      ·
        simp [h]
        simpa [coefOf, add_comm] using Nat.le_trans ih (Nat.le_add_right (l1Terms t) c.natAbs)

open Tammes15 Tammes15.D3lp
open scoped Classical

lemma packTerms_eq_sum_of_superset (B : ℕ) (t : List (ℕ × ℤ)) (s : Finset ℕ)
    (hs : (t.map Prod.fst).toFinset ⊆ s) :
    packTerms B t = ∑ j ∈ s, coefOf t j * (2 ^ (B * j) : ℤ) := by
  induction' t with p t ih generalizing s
  · simp [packTerms, coefOf]
  · rcases p with ⟨i, c⟩
    have hs_tail : (t.map Prod.fst).toFinset ⊆ s :=
      Finset.Subset.trans (by simp) hs
    have hi : i ∈ s := by
      have hmem : i ∈ ((i, c) :: t).map Prod.fst := by simp
      have hmem' : i ∈ (((i, c) :: t).map Prod.fst).toFinset := by
        simpa [List.mem_toFinset] using hmem
      exact hs hmem'
    have h_pow : ((1 <<< (B * i) : ℕ) : ℤ) = (2 : ℤ) ^ (B * i) := by
      simp [Nat.one_shiftLeft, Nat.cast_pow]
    rw [packTerms, ih s hs_tail, h_pow]
    calc
      c * ((2 : ℤ) ^ (B * i)) + ∑ j ∈ s, coefOf t j * (2 ^ (B * j) : ℤ)
          = (if i ∈ s then c * ((2 : ℤ) ^ (B * i)) else 0) +
            ∑ j ∈ s, coefOf t j * (2 ^ (B * j) : ℤ) := by simp [hi]
      _ = (∑ j ∈ s, (if i = j then c * ((2 : ℤ) ^ (B * j)) else 0)) +
          ∑ j ∈ s, coefOf t j * (2 ^ (B * j) : ℤ) := by
        rw [Finset.sum_ite_eq s i (fun j => c * ((2 : ℤ) ^ (B * j)))]
      _ = ∑ j ∈ s, ((if i = j then c * ((2 : ℤ) ^ (B * j)) else 0) +
          coefOf t j * (2 ^ (B * j) : ℤ)) := by rw [Finset.sum_add_distrib]
      _ = ∑ j ∈ s, ((if i = j then c else 0) * (2 ^ (B * j) : ℤ) +
          coefOf t j * (2 ^ (B * j) : ℤ)) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        by_cases h : i = j
        · simp [h]
        · simp [h]
      _ = ∑ j ∈ s, ((if i = j then c else 0) + coefOf t j) * (2 ^ (B * j) : ℤ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [add_mul]
      _ = ∑ j ∈ s, coefOf ((i, c) :: t) j * (2 ^ (B * j) : ℤ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hcoef : coefOf ((i, c) :: t) j = (if i = j then c else 0) + coefOf t j := by
          simp [coefOf, List.filter_cons]
          by_cases h : i = j
          · simp [h]
          · simp [h]
        rw [hcoef]

theorem packTerms_eq_sum (B : ℕ) (t : List (ℕ × ℤ)) :
    packTerms B t = ∑ j ∈ (t.map Prod.fst).toFinset, coefOf t j * 2 ^ (B * j) := by
  apply packTerms_eq_sum_of_superset B t ((t.map Prod.fst).toFinset)
  simp

theorem evalTerms_eq_sum (t : List (ℕ × ℤ)) (x : ℕ → ℝ) :
    evalTerms t x = ∑ j ∈ (t.map Prod.fst).toFinset, (coefOf t j : ℝ) * x j := by

  have h_aux : ∀ (t : List (ℕ × ℤ)) (s : Finset ℕ), (t.map Prod.fst).toFinset ⊆ s →
      evalTerms t x = ∑ j ∈ s, (coefOf t j : ℝ) * x j := by
    intro t s hs
    induction' t with p t ih generalizing s
    · simp [evalTerms, coefOf]
    · rcases p with ⟨i, c⟩
      simp [evalTerms]

      have hcoef : ∀ j, (coefOf ((i, c) :: t) j : ℝ) = (if i = j then (c : ℝ) else 0) + (coefOf t j : ℝ) := by
        intro j
        simp [coefOf, List.filter_cons]
        split_ifs <;> simp
      have hsum_eq : (∑ j ∈ s, (coefOf ((i, c) :: t) j : ℝ) * x j) =
          (∑ j ∈ s, ((if i = j then (c : ℝ) else 0) + (coefOf t j : ℝ)) * x j) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [hcoef j]
      rw [hsum_eq]

      rw [Finset.sum_congr rfl (fun j hj => by rw [add_mul])]
      rw [Finset.sum_add_distrib]
      have h_insert : (((i, c) :: t).map Prod.fst).toFinset = insert i (t.map Prod.fst).toFinset := by simp
      have hs_insert : insert i (t.map Prod.fst).toFinset ⊆ s := by
        rwa [← h_insert]
      have hs_t : (t.map Prod.fst).toFinset ⊆ s :=
        Finset.Subset.trans (Finset.subset_insert i _) hs_insert
      rw [← evalTerms, ih s hs_t]

      have hsum : (∑ j ∈ s, ((if i = j then (c : ℝ) else 0)) * x j) = (c : ℝ) * x i := by
        calc
          (∑ j ∈ s, ((if i = j then (c : ℝ) else 0)) * x j) = (∑ j ∈ s, (if i = j then (c : ℝ) * x j else 0)) := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            split_ifs <;> simp
          _ = (c : ℝ) * x i := by
            simp [Finset.sum_ite_eq, hs_insert (Finset.mem_insert_self i _)]
      rw [hsum]

  exact h_aux t ((t.map Prod.fst).toFinset) (Finset.Subset.refl _)

theorem digits_eq_zero (B : ℕ) (s : Finset ℕ) (a : ℕ → ℤ) (hb : ∀ j ∈ s, |a j| < 2 ^ B)
    (h : ∑ j ∈ s, a j * 2 ^ (B * j) = 0) : ∀ j ∈ s, a j = 0 := by
  induction' s using Finset.induction_on_min with m s hm ih
  · intro j hj; exfalso; exact Finset.notMem_empty j hj
  · have hm_not_mem : m ∉ s := by
      intro hm'; exact Nat.lt_irrefl m (hm m hm')
    have hsum_split : a m * (2 : ℤ) ^ (B * m) + ∑ j ∈ s, a j * (2 : ℤ) ^ (B * j) = 0 := by
      simpa [Finset.sum_insert hm_not_mem] using h
    have h_pow_ne_zero : (2 : ℤ) ^ (B * m) ≠ 0 := by
      apply pow_ne_zero
      norm_num
    have h_factor : ∀ j ∈ s, a j * (2 : ℤ) ^ (B * j) =
        (2 : ℤ) ^ (B * m) * (2 : ℤ) ^ B * (a j * (2 : ℤ) ^ (B * (j - m - 1))) := by
      intro j hj
      have hmj : m < j := hm j hj
      rcases Nat.exists_eq_add_of_lt hmj with ⟨k, hk⟩
      have hk_eq : j = m + k + 1 := hk
      rw [hk_eq]
      calc
        a (m + k + 1) * (2 : ℤ) ^ (B * (m + k + 1)) = a (m + k + 1) * ((2 : ℤ) ^ (B * m + B * k + B)) := by ring
        _ = a (m + k + 1) * ((2 : ℤ) ^ (B * m + B * k) * (2 : ℤ) ^ B) := by rw [pow_add]
        _ = a (m + k + 1) * (((2 : ℤ) ^ (B * m) * (2 : ℤ) ^ (B * k)) * (2 : ℤ) ^ B) := by rw [pow_add]
        _ = a (m + k + 1) * ((2 : ℤ) ^ (B * m) * (2 : ℤ) ^ B * (2 : ℤ) ^ (B * k)) := by ring
        _ = (2 : ℤ) ^ (B * m) * (2 : ℤ) ^ B * (a (m + k + 1) * (2 : ℤ) ^ (B * k)) := by ring
        _ = (2 : ℤ) ^ (B * m) * (2 : ℤ) ^ B * (a (m + k + 1) * (2 : ℤ) ^ (B * ((m + k + 1) - m - 1))) := by
          have : (m + k + 1 : ℕ) - m - 1 = k := by omega
          simp [this]
    have hsum_eq : (2 : ℤ) ^ (B * m) * (a m + (2 : ℤ) ^ B * (∑ j ∈ s, a j * (2 : ℤ) ^ (B * (j - m - 1)))) = 0 := by
      calc
        (2 : ℤ) ^ (B * m) * (a m + (2 : ℤ) ^ B * (∑ j ∈ s, a j * (2 : ℤ) ^ (B * (j - m - 1))))
            = (2 : ℤ) ^ (B * m) * a m + (2 : ℤ) ^ (B * m) * ((2 : ℤ) ^ B * (∑ j ∈ s, a j * (2 : ℤ) ^ (B * (j - m - 1)))) := by ring
        _ = a m * (2 : ℤ) ^ (B * m) + ((2 : ℤ) ^ (B * m) * (2 : ℤ) ^ B) * (∑ j ∈ s, a j * (2 : ℤ) ^ (B * (j - m - 1))) := by ring
        _ = a m * (2 : ℤ) ^ (B * m) + (∑ j ∈ s, (2 : ℤ) ^ (B * m) * (2 : ℤ) ^ B * (a j * (2 : ℤ) ^ (B * (j - m - 1)))) := by
          simp [Finset.mul_sum, mul_assoc]
        _ = a m * (2 : ℤ) ^ (B * m) + (∑ j ∈ s, a j * (2 : ℤ) ^ (B * j)) := by
          refine congrArg (fun t => a m * (2 : ℤ) ^ (B * m) + t) (Finset.sum_congr rfl fun j hj => ?_)
          rw [h_factor j hj]
        _ = 0 := hsum_split
    have h_inner_eq_zero : a m + (2 : ℤ) ^ B * (∑ j ∈ s, a j * (2 : ℤ) ^ (B * (j - m - 1))) = 0 := by
      have hzero := eq_zero_or_eq_zero_of_mul_eq_zero hsum_eq
      rcases hzero with (hpow | hinner)
      · exfalso; exact h_pow_ne_zero hpow
      · exact hinner
    have h_dvd : (2 : ℤ) ^ B ∣ a m := by
      have : a m = -((2 : ℤ) ^ B * (∑ j ∈ s, a j * (2 : ℤ) ^ (B * (j - m - 1)))) := by
        linarith
      rw [this]
      exact ⟨-(∑ j ∈ s, a j * (2 : ℤ) ^ (B * (j - m - 1))), by ring⟩
    have h_abs_lt : |a m| < (2 : ℤ) ^ B := hb m (Finset.mem_insert_self m s)
    have h_am_zero : a m = 0 := Int.eq_zero_of_abs_lt_dvd h_dvd h_abs_lt
    have hsum_s : ∑ j ∈ s, a j * (2 : ℤ) ^ (B * j) = 0 := by
      simpa [h_am_zero] using hsum_split
    have h_rest : ∀ j ∈ s, a j = 0 := ih (fun j hj => hb j (Finset.mem_insert_of_mem hj)) hsum_s
    intro j hj
    rcases Finset.mem_insert.mp hj with (rfl | hj')
    · exact h_am_zero
    · exact h_rest j hj'

theorem packTerms_eq_zero (B : ℕ) (t : List (ℕ × ℤ)) (h0 : packTerms B t = 0)
    (hb : l1Terms t < 2 ^ B) (x : ℕ → ℝ) : evalTerms t x = 0 := by
  have hz := digits_eq_zero B _ (coefOf t) (fun j _ => by
    have h1 := natAbs_coefOf_le t j
    rw [Int.abs_eq_natAbs]
    exact_mod_cast lt_of_le_of_lt h1 hb) (by rw [← packTerms_eq_sum]; exact h0)
  rw [evalTerms_eq_sum]
  exact Finset.sum_eq_zero fun j hj => by rw [hz j hj]; simp

theorem farkasPacked_sound (B : ℕ) (rows : List (ℕ × Row)) (h : farkasPacked B rows = true)
    (x : ℕ → ℝ) (hx : ∀ q ∈ rows, q.2.Holds x) : False := by
  simp only [farkasPacked, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, hb⟩, hr⟩ := h
  rw [packSum_eq_packTerms_flat] at h0
  have hb' : l1Terms (flat rows) < 2 ^ B := by
    rw [Nat.one_shiftLeft] at hb
    exact lt_of_le_of_lt (l1Terms_flat rows) hb
  have hz := packTerms_eq_zero B _ h0 hb' x
  rw [evalTerms_flat] at hz
  have h1 := combSum_le_rhsSum rows x hx
  have h2 : (rhsSum rows : ℝ) < 0 := by exact_mod_cast hr
  linarith

end Tammes15.D3lp
