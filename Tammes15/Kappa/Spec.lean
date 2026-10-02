import Tammes15.Kappa.Generic

/-!
# D1: specification of the kernel checker

`nMat_spec`: under `Shape`, the natural number `absSum (symm (nMat ...))` that the kernel bounds in
`checkN` is `2^264 ∑ |Nr + Nrᵀ|` of the real matrix `Nr` of the certificate at the rounded frame.

Route: every list of the checker is written as `List.ofFn` of its entries (`mkV_eq`, `mkGt_eq`,
`mkW_eq`, `tr_ofFn`, `nMat_eq`, `symm_ofFn`), `absSum` of such a list is a double sum of `natAbs`
(`absSum_ofFn`), and each integer entry is `2^264` times the real one (`vEntry_cast`,
`gEntry_cast`, `nEntry_cast`).
-/

open scoped RealInnerProductSpace

namespace Tammes15.Kappa

/-! ## 1. Lists as `List.ofFn` -/

theorem ofFn_getD {α : Type*} (l : List α) (d : α) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i d) = l := by
  subst h
  have hget : (fun (i : Fin l.length) => l.getD i d) = (fun (i : Fin l.length) => l[i.val]) := by
    ext i
    rw [List.getD_eq_getElem l d i.isLt]
  rw [hget]
  exact List.ofFn_getElem

theorem ofFn_getD_getD {α : Type*} (M : List (List α)) (d : α) (n m : ℕ) (h : M.length = n)
    (h' : ∀ r ∈ M, r.length = m) :
    List.ofFn (fun i : Fin n => List.ofFn fun j : Fin m => (M.getD i []).getD j d) = M := by
  apply List.ext_getElem
  · simp [List.length_ofFn, h]
  · intro i hi hMi
    have hi_lt_n : i < n := by
      simpa [List.length_ofFn, h] using hi
    have hi_mem : (M.get ⟨i, hMi⟩) ∈ M :=
      List.get_mem M ⟨i, hMi⟩
    have hrow_len : (M.get ⟨i, hMi⟩).length = m := h' _ hi_mem
    have hgetD_outer : M.getD (i : ℕ) [] = M.get ⟨i, hMi⟩ := by
      simpa [List.get_eq_getElem] using List.getD_eq_getElem (l := M) (d := ([] : List α)) hMi
    calc
      (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => (M.getD i []).getD j d)[i]
          = (fun i : Fin n => List.ofFn fun j : Fin m => (M.getD i []).getD j d) ⟨i, hi_lt_n⟩ := by
        rw [List.getElem_ofFn (by simpa [List.length_ofFn, h] using hi)]
      _ = List.ofFn fun j : Fin m => (M.getD (⟨i, hi_lt_n⟩ : Fin n) []).getD j d := rfl
      _ = List.ofFn fun j : Fin m => (M.getD (i : ℕ) []).getD j d := by simp
      _ = List.ofFn fun j : Fin m => (M.get ⟨i, hMi⟩).getD j d := by rw [hgetD_outer]
      _ = List.ofFn fun j : Fin m => ((M.get ⟨i, hMi⟩)[j]) := by
        refine congrArg (fun f => List.ofFn f) (funext fun j => ?_)
        simpa using List.getD_eq_getElem (l := M.get ⟨i, hMi⟩) (d := d) (by
          rw [hrow_len]
          exact j.isLt)
      _ = (M.get ⟨i, hMi⟩) := by
        subst hrow_len
        exact List.ofFn_getElem (xs := M.get ⟨i, hMi⟩)
      _ = M[i] := by rw [List.get_eq_getElem]

theorem smulAdd_ofFn {m : ℕ} (c : ℤ) (v acc : Fin m → ℤ) :
    smulAdd c (List.ofFn v) (List.ofFn acc) = List.ofFn fun b => c * v b + acc b := by
  apply List.ext_getElem
  · simp [smulAdd, List.length_zipWith, List.length_ofFn]
  · intro i hi1 hi2
    simp [smulAdd, List.getElem_zipWith, List.getElem_ofFn]

theorem lin_ofFn {n m : ℕ} (c : Fin n → ℤ) (r : Fin n → Fin m → ℤ) (acc : Fin m → ℤ) :
    lin (List.ofFn c) (List.ofFn fun i => List.ofFn (r i)) (List.ofFn acc) =
      List.ofFn fun b => acc b + ∑ i, c i * r i b := by
  induction n generalizing acc with
  | zero =>
    simp [lin]
  | succ n ih =>
    simp only [List.ofFn_succ, lin, smulAdd_ofFn]
    have h := ih (fun i => c i.succ) (fun i => r i.succ) (fun b => c 0 * r 0 b + acc b)
    simp only [h]
    refine congrArg (fun f : Fin m → ℤ => List.ofFn f) ?_
    ext b
    simp only [Fin.sum_univ_succ]
    ring

theorem tr_ofFn {n : ℕ} (M : Fin n → Fin 46 → ℤ) :
    tr (List.ofFn fun i => List.ofFn (M i)) = List.ofFn fun j => List.ofFn fun i => M i j := by
  induction n with
  | zero =>
      simp [tr, List.ofFn]
      decide
  | succ n ih =>
      rw [List.ofFn_succ]
      have h_tr_cons (a : List ℤ) (as : List (List ℤ)) : tr (a :: as) = List.zipWith List.cons a (tr as) := by
        simp [tr]
      rw [h_tr_cons]
      rw [ih (fun i j => M i.succ j)]
      ext j
      simp [List.ofFn_succ]

theorem symm_ofFn (M : Fin 46 → Fin 46 → ℤ) :
    symm (List.ofFn fun a => List.ofFn (M a)) =
      List.ofFn fun a => List.ofFn fun b => M a b + M b a := by
  unfold symm
  rw [tr_ofFn]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_zipWith, List.getElem_ofFn]
  apply List.ext_getElem (by simp)
  intro k h3 h4
  simp

theorem foldl_add_map_sum {α : Type} (f : α → ℕ) (s0 : ℕ) (l : List α) :
    l.foldl (fun s x => s + f x) s0 = s0 + (l.map f).sum := by
  induction' l with x xs ih generalizing s0
  · simp
  · simp [ih, add_assoc]

theorem foldl_add_map_sum' {β : Type} (f : β → ℕ) (a : ℕ) (l : List β) :
    l.foldl (fun s r => s + f r) a = a + (l.map f).sum := by
  induction' l with x xs ih generalizing a
  · simp
  · simp [ih, add_assoc]

theorem absSum_ofFn {n m : ℕ} (M : Fin n → Fin m → ℤ) :
    absSum (List.ofFn fun a => List.ofFn (M a)) = ∑ a, ∑ b, (M a b).natAbs := by
  have h_inner : ∀ (s0 : ℕ) (r : List ℤ),
      r.foldl (fun s x => s + x.natAbs) s0 = s0 + (r.map Int.natAbs).sum := by
    intro s0 r
    exact foldl_add_map_sum Int.natAbs s0 r
  have h_outer_eq : (fun (s : ℕ) (r : List ℤ) => r.foldl (fun s x => s + x.natAbs) s) =
      (fun (s : ℕ) (r : List ℤ) => s + (r.map Int.natAbs).sum) := by
    ext s r; rw [h_inner s r]
  calc
    absSum (List.ofFn fun a => List.ofFn (M a))
        = (List.ofFn fun a => List.ofFn (M a)).foldl
            (fun s r => r.foldl (fun s x => s + x.natAbs) s) 0 := rfl
    _ = (List.ofFn fun a => List.ofFn (M a)).foldl
            (fun s r => s + (r.map Int.natAbs).sum) 0 := by rw [h_outer_eq]
    _ = 0 + ((List.ofFn fun a => List.ofFn (M a)).map
            (fun r => (r.map Int.natAbs).sum)).sum := by
      rw [foldl_add_map_sum']
    _ = ((List.ofFn fun a => List.ofFn (M a)).map
            (fun r => (r.map Int.natAbs).sum)).sum := by simp
    _ = (List.ofFn ((fun r => (r.map Int.natAbs).sum) ∘ (fun a => List.ofFn (M a)))).sum := by
      rw [List.map_ofFn]
    _ = (List.ofFn fun a => ((List.ofFn (M a)).map Int.natAbs).sum).sum := rfl
    _ = (List.ofFn fun a => (List.ofFn (Int.natAbs ∘ M a)).sum).sum := by
      simp [List.map_ofFn]
    _ = (List.ofFn fun a => (List.ofFn fun b => (M a b).natAbs).sum).sum := rfl
    _ = (List.ofFn fun a => ∑ b : Fin m, (M a b).natAbs).sum := by
      simp [Fin.sum_ofFn]
    _ = ∑ a : Fin n, ∑ b : Fin m, (M a b).natAbs := by
      simp [Fin.sum_ofFn]

theorem mkV_eq (P : List (List ℤ)) (S : List (ℕ × ℕ)) (hS : S.length = 30) :
    mkV P S = List.ofFn fun e : Fin 30 => List.ofFn fun a : Fin 46 => vEntry P (S.getD e (0, 0)) a := by
  rw [mkV]
  have hS_eq : S = List.ofFn fun e : Fin 30 => S.getD e (0, 0) := by
    apply List.ext_getElem
    · simp [hS]
    · intro i hi hi'
      have hiS : i < S.length := by simpa using hi
      rw [List.getElem_ofFn hi', List.getD_eq_getElem S (0, 0) hiS]
  have h_map_eq : S.map (fun e => (List.range 46).map fun a => vEntry P e a) =
      (List.ofFn fun e : Fin 30 => S.getD e (0, 0)).map (fun e => (List.range 46).map fun a => vEntry P e a) :=
    congrArg (fun L => L.map (fun e => (List.range 46).map fun a => vEntry P e a)) hS_eq
  rw [h_map_eq]
  rw [List.map_ofFn]
  -- Goal: List.ofFn (fun e => (List.range 46).map fun a => vEntry P (S.getD e (0, 0)) a) =
  --       List.ofFn fun e => List.ofFn fun a => vEntry P (S.getD e (0, 0)) a
  refine congrArg List.ofFn (funext ?_)
  intro e
  -- Goal: ((fun e => ...) ∘ (fun e => S.getD e (0,0))) e = List.ofFn (fun a => vEntry P (S.getD e (0,0)) a)
  -- Simplify LHS: (f ∘ g) e = f (g e)
  rw [Function.comp_apply]
  -- Goal: (List.range 46).map (fun a => vEntry P (S.getD e (0, 0)) a) = List.ofFn (fun a => vEntry P (S.getD e (0, 0)) a)
  rw [← List.ofFn_getElem_eq_map (l := List.range 46) (f := fun a => vEntry P (S.getD e (0, 0)) a)]
  simp [List.getElem_range]

theorem mkGt_eq (P : List (List ℤ)) :
    mkGt P = List.ofFn fun a : Fin 46 => List.ofFn fun k : Fin 18 => gEntry P k a := by
  unfold mkGt
  have h1 : (List.range 46).map (fun a => (List.range 18).map (fun k => gEntry P k a)) =
      List.ofFn (fun a : Fin 46 => (List.range 18).map (fun k => gEntry P k a)) := by
    apply List.ext_getElem
    · simp [List.length_map, List.length_range]
    · intro i hi1 hi2
      have hL : ((List.range 46).map (fun a => (List.range 18).map (fun k => gEntry P k a)))[i] =
          (List.range 18).map (fun k => gEntry P k i) := by
        have := List.getElem_map (f := fun a => (List.range 18).map (fun k => gEntry P k a))
          (l := List.range 46) (i := i) (h := hi1)
        rw [List.getElem_range] at this
        exact this
      have hR : (List.ofFn (fun a : Fin 46 => (List.range 18).map (fun k => gEntry P k a)))[i] =
          (List.range 18).map (fun k => gEntry P k i) := by
        have := List.getElem_ofFn (f := fun a : Fin 46 => (List.range 18).map (fun k => gEntry P k a))
          (i := i) (h := hi2)
        simpa using this
      exact hL.trans hR.symm
  have h2 : List.ofFn (fun a : Fin 46 => (List.range 18).map (fun k => gEntry P k a)) =
      List.ofFn (fun a : Fin 46 => List.ofFn (fun k : Fin 18 => gEntry P k a)) := by
    refine congrArg List.ofFn (funext fun a => ?_)
    apply List.ext_getElem
    · simp [List.length_map, List.length_range]
    · intro j hj1 hj2
      have hL : ((List.range 18).map (fun k => gEntry P k a))[j] = gEntry P j a := by
        have := List.getElem_map (f := fun k => gEntry P k a) (l := List.range 18) (i := j) (h := hj1)
        rw [List.getElem_range] at this
        exact this
      have hR : (List.ofFn (fun k : Fin 18 => gEntry P k a))[j] = gEntry P j a := by
        have := List.getElem_ofFn (f := fun k : Fin 18 => gEntry P k a) (i := j) (h := hj2)
        simpa using this
      exact hL.trans hR.symm
  exact h1.trans h2

theorem mkW_eq {m n : ℕ} (mu : Fin m → Fin n → ℤ) (V : Fin n → Fin 46 → ℤ) :
    mkW (List.ofFn fun e => List.ofFn (mu e)) (List.ofFn fun f => List.ofFn (V f)) =
      List.ofFn fun e => List.ofFn fun b => ∑ f, mu e f * V f b := by
  simp only [mkW, List.map_ofFn, zeros]
  refine (List.ofFn_inj.2 ?_)
  funext i
  simpa [List.ofFn_const, zero_add] using lin_ofFn (mu i) V (fun _ => 0)

theorem range_map_eq_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn fun i : Fin n => f i := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hi_range : i < (List.range n).length := by
      simpa [List.length_map] using hi
    simp [List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem zip_range_ofFn {α β : Type*} (f : Fin 46 → α) (g : Fin 46 → β) :
    (List.range 46).zip ((List.ofFn f).zip (List.ofFn g)) =
      List.ofFn fun a : Fin 46 => ((a : ℕ), f a, g a) := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_zip, List.getElem_range, List.getElem_ofFn]

theorem nRow_eq (RC : ℤ) (lam : Fin 30 → ℤ) (V W : Fin 30 → Fin 46 → ℤ) (Mk : Fin 18 → Fin 46 → ℤ)
    (a : ℕ) (vt : Fin 30 → ℤ) (gt : Fin 18 → ℤ) :
    nRow RC (List.ofFn lam) (List.ofFn fun e => List.ofFn (V e)) (List.ofFn fun e => List.ofFn (W e))
        (List.ofFn fun k => List.ofFn (Mk k)) a (List.ofFn vt) (List.ofFn gt) =
      List.ofFn fun b : Fin 46 =>
        (((if a = 0 ∧ (b : ℕ) = 0 then RC * 2 ^ 200 else if a = (b : ℕ) then -(2 ^ 264) else 0) +
          (if a = 0 then ∑ e, -(lam e * 2 ^ 100) * V e b else 0)) +
          ∑ e, -(vt e) * W e b) + ∑ k, -(gt k * 2 ^ 100) * Mk k b := by
  have hbase := range_map_eq_ofFn 46 (fun b : ℕ =>
      if a = 0 ∧ b = 0 then RC * 2 ^ 200 else if a = b then -(2 ^ 264 : ℤ) else 0)
  unfold nRow
  simp only [hbase, List.map_ofFn]
  by_cases ha : a = 0
  · subst ha
    simp only [↓reduceIte]
    rw [lin_ofFn, lin_ofFn, lin_ofFn]
    simp only [Function.comp_apply]
  · simp only [ha, ↓reduceIte, add_zero]
    rw [lin_ofFn, lin_ofFn]
    simp only [Function.comp_apply]

theorem nMat_eq (RC : ℤ) (lam : Fin 30 → ℤ) (V W : Fin 30 → Fin 46 → ℤ) (Mk : Fin 18 → Fin 46 → ℤ)
    (Vt : Fin 46 → Fin 30 → ℤ) (Gt : Fin 46 → Fin 18 → ℤ) :
    nMat RC (List.ofFn lam) (List.ofFn fun e => List.ofFn (V e)) (List.ofFn fun e => List.ofFn (W e))
        (List.ofFn fun k => List.ofFn (Mk k)) (List.ofFn fun a => List.ofFn (Vt a))
        (List.ofFn fun a => List.ofFn (Gt a)) =
      List.ofFn fun a : Fin 46 => List.ofFn fun b : Fin 46 =>
        (((if (a : ℕ) = 0 ∧ (b : ℕ) = 0 then RC * 2 ^ 200 else
            if (a : ℕ) = (b : ℕ) then -(2 ^ 264) else 0) +
          (if (a : ℕ) = 0 then ∑ e, -(lam e * 2 ^ 100) * V e b else 0)) +
          ∑ e, -(Vt a e) * W e b) + ∑ k, -(Gt a k * 2 ^ 100) * Mk k b := by
  unfold nMat
  rw [zip_range_ofFn, List.map_ofFn]
  refine congrArg List.ofFn (funext fun a => ?_)
  simp only [Function.comp_apply]
  rw [nRow_eq RC lam V W Mk (a : ℕ) (Vt a) (Gt a)]

/-! ## 2. The integer entries are `2^100` and `2^264` times the real ones -/

theorem getP_cast (P : List (List ℤ)) (i : ℕ) (hi : i < 15) (m : Fin 3) :
    ((getP P i m : ℤ) : ℝ) = 2 ^ 100 * qOf P ⟨i, hi⟩ m := by
  rw [qOf_apply]
  unfold getP
  push_cast
  field_simp [show (2 : ℝ) ^ 100 ≠ 0 from by norm_num]

theorem fin46_cases (a : Fin 46) : a = 0 ∨ ∃ i m, a = ix i m := by
  by_cases h : a.val = 0
  · left; exact Fin.ext h
  · right
    have ha_pos : 1 ≤ a.val := by omega
    have ha_lt : a.val < 46 := a.isLt
    set i_val := (a.val - 1) / 3 with hi_val
    set m_val := (a.val - 1) % 3 with hm_val
    have hi_lt : i_val < 15 := by omega
    have hm_lt : m_val < 3 := by omega
    have h_eq : a.val = 1 + 3 * i_val + m_val := by
      dsimp [i_val, m_val]
      have h := Nat.div_add_mod (a.val - 1) 3
      omega
    exact ⟨⟨i_val, hi_lt⟩, ⟨m_val, hm_lt⟩, Fin.ext h_eq⟩

theorem fin18_cases (k : Fin 18) :
    (∃ k' : Fin 15, k = ⟨k'.val, by omega⟩) ∨ ∃ c : Fin 3, k = ⟨15 + c.val, by omega⟩ := by
  by_cases h : k.val < 15
  · left
    refine ⟨⟨k.val, h⟩, ?_⟩
    ext
    simp
  · right
    have h15 : 15 ≤ k.val := by omega
    have hlt : k.val - 15 < 3 := by omega
    refine ⟨⟨k.val - 15, hlt⟩, ?_⟩
    ext
    simp
    omega

theorem vEntry_zero (P : List (List ℤ)) (x : ℕ × ℕ) : vEntry P x 0 = 2 ^ 100 := by
  simp [vEntry]

theorem vEntry_ix (P : List (List ℤ)) (x : ℕ × ℕ) (i : Fin 15) (m : Fin 3) :
    vEntry P x (ix i m) =
      (if (i : ℕ) = x.2 then -getP P x.1 m else 0) + (if (i : ℕ) = x.1 then -getP P x.2 m else 0) := by
  have hm : (m : ℕ) < 3 := m.2
  have hval : (ix i m : ℕ) = 1 + 3 * (i : ℕ) + (m : ℕ) := by
    simp [ix]
  have h0 : (ix i m : ℕ) ≠ 0 := by
    rw [hval]
    omega
  have hdiv : ((ix i m : ℕ) - 1) / 3 = (i : ℕ) := by
    rw [hval]
    omega
  have hmod : ((ix i m : ℕ) - 1) % 3 = (m : ℕ) := by
    rw [hval]
    omega
  unfold vEntry
  rw [if_neg h0, hdiv, hmod]

theorem gEntry_zero (P : List (List ℤ)) (k : ℕ) : gEntry P k 0 = 0 := by
  simp [gEntry]

theorem gEntry_ix_pt (P : List (List ℤ)) (k i : Fin 15) (m : Fin 3) :
    gEntry P k (ix i m) = if i = k then getP P i m else 0 := by
  have hpos : (ix i m).val ≠ 0 := by
    simp [ix]
  have hsub : (ix i m).val - 1 = 3 * i.val + m.val := by
    simp [ix]; omega
  have hdiv : ((ix i m).val - 1) / 3 = i.val := by
    rw [hsub]
    have hm : m.val < 3 := m.is_lt
    omega
  have hmod : ((ix i m).val - 1) % 3 = m.val := by
    rw [hsub]
    have hm : m.val < 3 := m.is_lt
    omega
  have hlt : (k : ℕ) < 15 := by
    have := k.is_lt
    omega
  unfold gEntry
  simp [hpos, hdiv, hmod, hlt]
  by_cases h : (i : ℕ) = (k : ℕ)
  · have heq : i = k := Fin.ext h
    subst heq
    simp
  · have hne : i ≠ k := by
      intro heq
      apply h
      rw [heq]
    simp [h, hne]

theorem gEntry_ix_rot (P : List (List ℤ)) (c : Fin 3) (i : Fin 15) (m : Fin 3) :
    gEntry P (15 + c) (ix i m) =
      if m = c + 2 then getP P i (c + 1 : Fin 3) else if m = c + 1 then -getP P i (c + 2 : Fin 3) else 0 := by
  fin_cases c <;> fin_cases m <;>
    dsimp [gEntry, ix, getP] <;>
    simp [show (1 + 3 * (i : ℕ) - 1) = 3 * (i : ℕ) by omega,
          show (1 + 3 * (i : ℕ)) % 3 = 1 by omega,
          show (1 + 3 * (i : ℕ)) / 3 = (i : ℕ) by omega,
          show (1 + 3 * (i : ℕ) + 1) % 3 = 2 by omega,
          show (1 + 3 * (i : ℕ) + 1) / 3 = (i : ℕ) by omega]

theorem SlOf_eq (S : List (ℕ × ℕ)) (e : Fin 30) (h1 : (S.getD e (0, 0)).1 < 15)
    (h2 : (S.getD e (0, 0)).2 < 15) : SlOf S e = (⟨(S.getD e (0, 0)).1, h1⟩, ⟨(S.getD e (0, 0)).2, h2⟩) := by
  apply Prod.ext
  · apply Fin.ext; exact Nat.mod_eq_of_lt h1
  · apply Fin.ext; exact Nat.mod_eq_of_lt h2

theorem vEntry_pair_cast (P : List (List ℤ)) (x : ℕ × ℕ) (h1 : x.1 < 15) (h2 : x.2 < 15) (a : Fin 46) :
    ((vEntry P x a : ℤ) : ℝ) = 2 ^ 100 * vr (qOf P) (⟨x.1, h1⟩, ⟨x.2, h2⟩) a := by
  have hgetP_cast (i : ℕ) (hi : i < 15) (m : Fin 3) : ((getP P i m : ℤ) : ℝ) = 2 ^ 100 * qOf P ⟨i, hi⟩ m := by
    simp [getP, qOf]
    fin_cases m <;> simp <;> ring
  by_cases ha0 : a.val = 0
  · have ha : a = 0 := Fin.ext ha0
    subst ha
    simp [vEntry, vr]
    norm_num
  · have ha_val_pos : 0 < a.val := Nat.pos_of_ne_zero ha0
    have hdiv : (a.val - 1) / 3 < 15 := by
      have ha_le : a.val ≤ 45 := by
        have := a.isLt
        omega
      omega
    have hmod : (a.val - 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    let m3 : Fin 3 := ⟨(a.val - 1) % 3, hmod⟩
    have ha_eq : a = ix ⟨(a.val - 1) / 3, hdiv⟩ m3 := by
      refine Fin.ext ?_
      dsimp [ix, m3]
      omega
    rw [ha_eq]
    simp [vEntry, vr, ix]
    have hdiv_eq : ((1 + 3 * ((a.val - 1) / 3) + (m3 : ℕ)) - 1) / 3 = ((a.val - 1) / 3 : ℕ) := by
      dsimp [m3]
      omega
    have hmod_eq : ((1 + 3 * ((a.val - 1) / 3) + (m3 : ℕ)) - 1) % 3 = (m3 : ℕ) := by
      dsimp [m3]
      omega
    simp [hdiv_eq, hmod_eq]
    by_cases hi2 : ((a.val - 1) / 3 : ℕ) = x.2
    · simp [hi2]
      rw [hgetP_cast x.1 h1 m3, hgetP_cast x.2 h2 m3]
      by_cases heq : x.2 = x.1
      · simp [heq]
        ring
      · simp [heq]
    · simp [hi2]
      by_cases hi1 : ((a.val - 1) / 3 : ℕ) = x.1
      · simp [hi1]
        rw [hgetP_cast x.2 h2 m3]
      · simp [hi1]

theorem vEntry_cast (P : List (List ℤ)) (S : List (ℕ × ℕ)) (e : Fin 30)
    (hS : (S.getD e (0, 0)).1 < 15 ∧ (S.getD e (0, 0)).2 < 15) (a : Fin 46) :
    ((vEntry P (S.getD e (0, 0)) a : ℤ) : ℝ) = 2 ^ 100 * vr (qOf P) (SlOf S e) a := by
  rw [SlOf_eq S e hS.1 hS.2]
  exact vEntry_pair_cast P _ hS.1 hS.2 a

theorem gEntry_cast (P : List (List ℤ)) (k : Fin 18) (a : Fin 46) :
    ((gEntry P k a : ℤ) : ℝ) = 2 ^ 100 * gr (qOf P) k a := by
  simp only [gEntry, gr, getP]
  simp [qOf_apply]
  by_cases ha : (a : ℕ) = 0
  · have ha' : a = 0 := by
      apply Fin.ext
      simpa using ha
    simp [ha']
  · have ha' : a ≠ 0 := by
      intro h; apply ha; simpa using congrArg (·.val) h
    simp [ha']
    by_cases hk : (k : ℕ) < 15
    · simp [hk, Nat.mod_eq_of_lt hk]
      by_cases h_eq : ((a : ℕ) - 1) / 3 = (k : ℕ)
      · simp [h_eq]
        field_simp
      · simp [h_eq]
    · simp [hk]
      by_cases h1 : ((a : ℕ) - 1) % 3 = ((k : ℕ) - 15 + 2) % 3
      · simp [h1]
        field_simp
      · simp [h1]
        by_cases h2 : ((a : ℕ) - 1) % 3 = ((k : ℕ) - 15 + 1) % 3
        · simp [h2]
          field_simp
        · simp [h2]

theorem nE_base (RC : ℕ) (a b : Fin 46) :
    ((if (a : ℕ) = 0 ∧ (b : ℕ) = 0 then (RC : ℤ) * 2 ^ 200 else
        if (a : ℕ) = (b : ℕ) then -(2 ^ 264) else 0 : ℤ) : ℝ) =
      2 ^ 264 * (if a.val = 0 ∧ b.val = 0 then (RC : ℝ) / 2 ^ 64 else if a = b then -1 else 0) := by
  by_cases hzero : (a : ℕ) = 0 ∧ (b : ℕ) = 0
  · -- both zero case
    rcases hzero with ⟨ha, hb⟩
    have h_eq : a = b := Fin.ext (ha.trans hb.symm)
    simp [hb, h_eq]
    field_simp [show (2 : ℝ) ^ 64 ≠ 0 from by norm_num]
    have h_2pow200 : (1606938044258990275541962092341162602522202993782792835301376 : ℝ) = (2 : ℝ) ^ 200 := by
      norm_num
    rw [h_2pow200]
  · -- not both zero
    by_cases heq_nat : (a : ℕ) = (b : ℕ)
    · -- a = b (as ℕ), not both zero
      have h_eq_fin : a = b := Fin.ext heq_nat
      have ha_ne_zero_nat : (a : ℕ) ≠ 0 := by
        intro h
        apply hzero
        have hb0 : (b : ℕ) = 0 := by simpa [heq_nat] using h
        exact ⟨h, hb0⟩
      have hb_ne_zero_fin : b ≠ 0 := by
        intro hb0
        apply ha_ne_zero_nat
        simpa [h_eq_fin] using congrArg (fun x : Fin 46 => (x : ℕ)) hb0
      simp [h_eq_fin, hb_ne_zero_fin]
    · -- a ≠ b (as ℕ), not both zero
      have h_ne_fin : a ≠ b := by
        intro h_eq; apply heq_nat; simpa using congrArg (fun x : Fin 46 => (x : ℕ)) h_eq
      have hzero_fin : ¬ (a = 0 ∧ b = 0) := by
        intro h
        rcases h with ⟨ha0, hb0⟩
        apply hzero
        have ha_nat : (a : ℕ) = 0 := by simpa using congrArg (fun x : Fin 46 => (x : ℕ)) ha0
        have hb_nat : (b : ℕ) = 0 := by simpa using congrArg (fun x : Fin 46 => (x : ℕ)) hb0
        exact ⟨ha_nat, hb_nat⟩
      simp [hzero_fin, heq_nat, h_ne_fin]

theorem nE_lam (P : List (List ℤ)) (S : List (ℕ × ℕ)) (Lam : List ℕ)
    (hS : ∀ e ∈ S, e.1 < 15 ∧ e.2 < 15) (hSl : S.length = 30) (a b : Fin 46) :
    ((if (a : ℕ) = 0 then
        ∑ e : Fin 30, -((Lam.getD e 0 : ℤ) * 2 ^ 100) * vEntry P (S.getD e (0, 0)) b else 0 : ℤ) : ℝ) =
      -(2 ^ 264 * (if a.val = 0 then ∑ e, lamOf Lam e * vr (qOf P) (SlOf S e) b else 0)) := by
  have hS' (e : Fin 30) : (S.getD e (0, 0)).1 < 15 ∧ (S.getD e (0, 0)).2 < 15 := by
    have hmem : S.getD e (0, 0) ∈ S := by
      rw [List.getD_eq_getElem]
      exact List.getElem_mem (by rw [hSl]; exact e.2)
    exact hS _ hmem
  split_ifs with ha
  · push_cast
    simp_rw [vEntry_cast P S _ (hS' _) b]
    have hl (e : Fin 30) : ((Lam.getD e 0 : ℕ) : ℝ) = lamOf Lam e * 2 ^ 64 := by
      rw [lamOf]; field_simp
    simp_rw [hl, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h_pow : (2 : ℝ) ^ 264 = 2 ^ 64 * 2 ^ 100 * 2 ^ 100 := by
      rw [← pow_add, ← pow_add]
    rw [h_pow]
    ring
  · simp

theorem nE_mu (P : List (List ℤ)) (S : List (ℕ × ℕ)) (Mu : List (List ℕ))
    (hS : ∀ e ∈ S, e.1 < 15 ∧ e.2 < 15) (hSl : S.length = 30) (a b : Fin 46) :
    ((∑ e : Fin 30, -(vEntry P (S.getD e (0, 0)) a) *
        ∑ f : Fin 30, ((Mu.getD e []).getD f 0 : ℤ) * vEntry P (S.getD f (0, 0)) b : ℤ) : ℝ) =
      -(2 ^ 264 * ∑ e, ∑ f, muOf Mu e f * vr (qOf P) (SlOf S e) a * vr (qOf P) (SlOf S f) b) := by
  push_cast
  have hS' (e : Fin 30) : (S.getD e (0, 0)).1 < 15 ∧ (S.getD e (0, 0)).2 < 15 := by
    have hmem : S.getD e (0, 0) ∈ S := by
      rw [List.getD_eq_getElem]
      exact List.getElem_mem (by
        rw [hSl]
        exact e.2)
    exact hS _ hmem
  simp_rw [vEntry_cast P S _ (hS' _) a, vEntry_cast P S _ (hS' _) b]
  simp_rw [Finset.mul_sum]
  have hmu (e f : Fin 30) : ((Mu.getD e []).getD f 0 : ℝ) = muOf Mu e f * (2 ^ 64 : ℝ) := by
    rw [muOf]
    field_simp
  simp_rw [hmu]
  have h_pow : (2 : ℝ) ^ 100 * (2 : ℝ) ^ 64 * (2 : ℝ) ^ 100 = (2 : ℝ) ^ 264 := by
    calc
      (2 : ℝ) ^ 100 * (2 : ℝ) ^ 64 * (2 : ℝ) ^ 100 = ((2 : ℝ) ^ 100 * (2 : ℝ) ^ 100) * (2 : ℝ) ^ 64 := by ring
      _ = (2 : ℝ) ^ (100 + 100) * (2 : ℝ) ^ 64 := by rw [pow_add]
      _ = (2 : ℝ) ^ 200 * (2 : ℝ) ^ 64 := by norm_num
      _ = (2 : ℝ) ^ (200 + 64) := by rw [pow_add]
      _ = (2 : ℝ) ^ 264 := by norm_num
  have h_inner (e f : Fin 30) : -(2 ^ 100 * vr (qOf P) (SlOf S e) a) * ((muOf Mu e f * (2 ^ 64 : ℝ)) * (2 ^ 100 * vr (qOf P) (SlOf S f) b)) =
      -(2 ^ 264 * (muOf Mu e f * vr (qOf P) (SlOf S e) a * vr (qOf P) (SlOf S f) b)) := by
    calc
      -(2 ^ 100 * vr (qOf P) (SlOf S e) a) * ((muOf Mu e f * (2 ^ 64 : ℝ)) * (2 ^ 100 * vr (qOf P) (SlOf S f) b))
      = -((2 : ℝ) ^ 100 * (2 : ℝ) ^ 64 * (2 : ℝ) ^ 100) * (vr (qOf P) (SlOf S e) a * muOf Mu e f * vr (qOf P) (SlOf S f) b) := by ring
      _ = -((2 : ℝ) ^ 264) * (vr (qOf P) (SlOf S e) a * muOf Mu e f * vr (qOf P) (SlOf S f) b) := by rw [h_pow]
      _ = -(2 ^ 264 * (muOf Mu e f * vr (qOf P) (SlOf S e) a * vr (qOf P) (SlOf S f) b)) := by ring
  simp_rw [h_inner]
  simp [Finset.sum_neg_distrib]

theorem nE_gr (P : List (List ℤ)) (Mk : List (List ℤ)) (a b : Fin 46) :
    ((∑ k : Fin 18, -(gEntry P k a * 2 ^ 100) * (Mk.getD k []).getD b 0 : ℤ) : ℝ) =
      -(2 ^ 264 * ∑ k, gr (qOf P) k a * mkOf Mk k b) := by
  push_cast
  simp_rw [gEntry_cast P]
  simp_rw [mkOf]
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  ring

/-- The entry `(a, b)` of `nMat` for the data of the certificate, as an integer formula. -/
def nEntry (P : List (List ℤ)) (S : List (ℕ × ℕ)) (Lam : List ℕ) (Mu : List (List ℕ))
    (Mk : List (List ℤ)) (RC : ℕ) (a b : Fin 46) : ℤ :=
  (((if (a : ℕ) = 0 ∧ (b : ℕ) = 0 then (RC : ℤ) * 2 ^ 200 else
      if (a : ℕ) = (b : ℕ) then -(2 ^ 264) else 0) +
    (if (a : ℕ) = 0 then
      ∑ e : Fin 30, -((Lam.getD e 0 : ℤ) * 2 ^ 100) * vEntry P (S.getD e (0, 0)) b else 0)) +
    ∑ e : Fin 30, -(vEntry P (S.getD e (0, 0)) a) *
      ∑ f : Fin 30, ((Mu.getD e []).getD f 0 : ℤ) * vEntry P (S.getD f (0, 0)) b) +
    ∑ k : Fin 18, -(gEntry P k a * 2 ^ 100) * (Mk.getD k []).getD b 0

theorem nEntry_cast (P : List (List ℤ)) (S : List (ℕ × ℕ)) (Lam : List ℕ) (Mu : List (List ℕ))
    (Mk : List (List ℤ)) (RC : ℕ) (hS : ∀ e ∈ S, e.1 < 15 ∧ e.2 < 15) (hSl : S.length = 30)
    (a b : Fin 46) :
    ((nEntry P S Lam Mu Mk RC a b : ℤ) : ℝ) =
      2 ^ 264 * Nr (qOf P) (SlOf S) (lamOf Lam) (muOf Mu) ((RC : ℝ) / 2 ^ 64) (mkOf Mk) a b := by
  unfold nEntry Nr
  rw [Int.cast_add, Int.cast_add, Int.cast_add, nE_base, nE_lam P S Lam hS hSl, nE_mu P S Mu hS hSl,
    nE_gr]
  ring

/-! ## 3. The specification -/

/-- Specification of the checker: the integer computation is `2^264` times the real matrix. -/
theorem nMat_spec (P : List (List ℤ)) (S : List (ℕ × ℕ)) (Lam : List ℕ)
    (Mu : List (List ℕ)) (Mk : List (List ℤ)) (RC : ℕ) (hs : Shape P S Lam Mu Mk) :
    ((absSum (symm (nMat (RC : ℤ) (nL Lam) (mkV P S) (mkW (Mu.map nL) (mkV P S)) Mk
        (tr (mkV P S)) (mkGt P))) : ℕ) : ℝ) =
      2 ^ 264 * ∑ a, ∑ b,
        |Nr (qOf P) (SlOf S) (lamOf Lam) (muOf Mu) ((RC : ℝ) / 2 ^ 64) (mkOf Mk) a b +
          Nr (qOf P) (SlOf S) (lamOf Lam) (muOf Mu) ((RC : ℝ) / 2 ^ 64) (mkOf Mk) b a| := by
  obtain ⟨-, -, hSl, hS, hL, hM, hM', hK, hK'⟩ := hs
  have hLam : nL Lam = List.ofFn fun e : Fin 30 => ((Lam.getD e 0 : ℕ) : ℤ) := by
    unfold nL
    conv_lhs => rw [← ofFn_getD Lam 0 30 hL]
    rw [List.map_ofFn]
    rfl
  have hMu : Mu.map nL =
      List.ofFn fun e : Fin 30 => List.ofFn fun f : Fin 30 => (((Mu.getD e []).getD f 0 : ℕ) : ℤ) := by
    conv_lhs => rw [← ofFn_getD_getD Mu 0 30 30 hM hM']
    rw [List.map_ofFn]
    congr 1
  have hMk : Mk = List.ofFn fun k : Fin 18 => List.ofFn fun b : Fin 46 => (Mk.getD k []).getD b 0 :=
    (ofFn_getD_getD Mk 0 18 46 hK hK').symm
  have key : nMat (RC : ℤ) (nL Lam) (mkV P S) (mkW (Mu.map nL) (mkV P S)) Mk (tr (mkV P S))
      (mkGt P) = List.ofFn fun a => List.ofFn fun b => nEntry P S Lam Mu Mk RC a b := by
    calc nMat (RC : ℤ) (nL Lam) (mkV P S) (mkW (Mu.map nL) (mkV P S)) Mk (tr (mkV P S)) (mkGt P)
        = nMat (RC : ℤ) (nL Lam) (mkV P S) (mkW (Mu.map nL) (mkV P S))
            (List.ofFn fun k : Fin 18 => List.ofFn fun b : Fin 46 => (Mk.getD k []).getD b 0)
            (tr (mkV P S)) (mkGt P) := by rw [← hMk]
      _ = _ := by
        rw [hLam, hMu, mkV_eq P S hSl, mkW_eq, tr_ofFn, mkGt_eq, nMat_eq]
        rfl
  rw [key, symm_ofFn, absSum_ofFn]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_add, nEntry_cast P S Lam Mu Mk RC hS hSl,
    nEntry_cast P S Lam Mu Mk RC hS hSl, ← mul_add, abs_mul, abs_of_pos (by positivity)]

end Tammes15.Kappa
