import Tammes15.D3Kernel.Kinds.CoverDefs

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp

def cvIter (F : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => i
  | j + 1 => F (cvIter F i j)

def cvCanon (F : ℕ → ℕ) (D i : ℕ) : Bool :=
  decide (i < D) && cvIter F i 6 == i && (List.range 5).all (fun j => decide (i < cvIter F i (j + 1)))

def cvCanonList (F : ℕ → ℕ) (D : ℕ) : List ℕ := (List.range D).filter (cvCanon F D)

def cvHrep (F : ℕ → ℕ) (i : ℕ) : ℕ :=
  min i (min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3)
    (min (cvIter F i 4) (cvIter F i 5)))))

theorem cv_iter_lab {α : Type} {D : ℕ} (f : Equiv.Perm α) (lab : α ≃ Fin D) (F : ℕ → ℕ)
    (hF : ∀ e, F (lab e) = lab (f e)) (e : α) (j : ℕ) : cvIter F (lab e) j = lab ((f ^ j) e) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [cvIter, ih, hF, pow_succ']

theorem faceIter_eq_cvIter (c : GCode) (i j : ℕ) : c.faceIter i j = cvIter c.faceAt i j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [GCode.faceIter, cvIter, ih]

theorem canon_eq (c : GCode) (i : ℕ) : canon c i = cvCanon c.faceAt c.D i := by
  simp only [canon, cvCanon, faceIter_eq_cvIter]

theorem hrep_eq (c : GCode) (i : ℕ) : hrep c i = cvHrep c.faceAt i := by
  simp only [hrep, cvHrep, faceIter_eq_cvIter]

theorem canonList_eq (c : GCode) : canonList c = cvCanonList c.faceAt c.D := by
  rw [canonList, cvCanonList, show canon c = cvCanon c.faceAt c.D from funext (canon_eq c)]

theorem cv_min_six (a b c d e f : ℕ) :
    min a (min b (min c (min d (min e f)))) = a ∨
    min a (min b (min c (min d (min e f)))) = b ∨
    min a (min b (min c (min d (min e f)))) = c ∨
    min a (min b (min c (min d (min e f)))) = d ∨
    min a (min b (min c (min d (min e f)))) = e ∨
    min a (min b (min c (min d (min e f)))) = f := by
  have h := Nat.le_total a (min b (min c (min d (min e f))))
  rcases h with (h | h)
  · left; exact Nat.min_eq_left h
  · have hmin : min a (min b (min c (min d (min e f)))) = min b (min c (min d (min e f))) :=
      Nat.min_eq_right h
    rw [hmin]
    have hb := Nat.le_total b (min c (min d (min e f)))
    rcases hb with (hb | hb)
    · right; left; exact Nat.min_eq_left hb
    · have hmin' : min b (min c (min d (min e f))) = min c (min d (min e f)) :=
        Nat.min_eq_right hb
      rw [hmin']
      have hc := Nat.le_total c (min d (min e f))
      rcases hc with (hc | hc)
      · right; right; left; exact Nat.min_eq_left hc
      · have hmin'' : min c (min d (min e f)) = min d (min e f) :=
          Nat.min_eq_right hc
        rw [hmin'']
        have hd := Nat.le_total d (min e f)
        rcases hd with (hd | hd)
        · right; right; right; left; exact Nat.min_eq_left hd
        · have hmin''' : min d (min e f) = min e f :=
            Nat.min_eq_right hd
          rw [hmin''']
          have he := Nat.le_total e f
          rcases he with (he | he)
          · right; right; right; right; left; exact Nat.min_eq_left he
          · right; right; right; right; right; exact Nat.min_eq_right he

theorem cv_hrep_spec (F : ℕ → ℕ) (i : ℕ) :
    (∃ j < 6, cvHrep F i = cvIter F i j) ∧ ∀ j < 6, cvHrep F i ≤ cvIter F i j := by
  constructor
  ·
    unfold cvHrep
    have h := cv_min_six i (cvIter F i 1) (cvIter F i 2) (cvIter F i 3) (cvIter F i 4) (cvIter F i 5)
    rcases h with (h | h | h | h | h | h)
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨3, by decide, h⟩
    · exact ⟨4, by decide, h⟩
    · exact ⟨5, by decide, h⟩
  ·
    intro j hj
    interval_cases j
    ·
      unfold cvHrep
      apply Nat.min_le_left
    ·
      unfold cvHrep
      calc
        min i (min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))))) ≤ min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)))) := Nat.min_le_right _ _
        _ ≤ cvIter F i 1 := Nat.min_le_left _ _
    ·
      unfold cvHrep
      calc
        min i (min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))))) ≤ min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)))) := Nat.min_le_right _ _
        _ ≤ min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))) := Nat.min_le_right _ _
        _ ≤ cvIter F i 2 := Nat.min_le_left _ _
    ·
      unfold cvHrep
      calc
        min i (min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))))) ≤ min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)))) := Nat.min_le_right _ _
        _ ≤ min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))) := Nat.min_le_right _ _
        _ ≤ min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)) := Nat.min_le_right _ _
        _ ≤ cvIter F i 3 := Nat.min_le_left _ _
    ·
      unfold cvHrep
      calc
        min i (min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))))) ≤ min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)))) := Nat.min_le_right _ _
        _ ≤ min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))) := Nat.min_le_right _ _
        _ ≤ min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)) := Nat.min_le_right _ _
        _ ≤ min (cvIter F i 4) (cvIter F i 5) := Nat.min_le_right _ _
        _ ≤ cvIter F i 4 := Nat.min_le_left _ _
    ·
      unfold cvHrep
      calc
        min i (min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))))) ≤ min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)))) := Nat.min_le_right _ _
        _ ≤ min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))) := Nat.min_le_right _ _
        _ ≤ min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)) := Nat.min_le_right _ _
        _ ≤ min (cvIter F i 4) (cvIter F i 5) := Nat.min_le_right _ _
        _ ≤ cvIter F i 5 := Nat.min_le_right _ _

theorem cv_canon_spec (F : ℕ → ℕ) (D i : ℕ) :
    cvCanon F D i = true ↔ (i < D ∧ cvIter F i 6 = i ∧ ∀ j, 0 < j → j < 6 → i < cvIter F i j) := by
  unfold cvCanon
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨hlt, heq⟩, hall⟩
    have heq' : cvIter F i 6 = i := by
      simpa [beq_iff_eq] using heq
    refine ⟨hlt, heq', ?_⟩
    rw [List.all_iff_forall_prop] at hall
    intro j hjpos hjlt
    have := hall (j - 1) (by
      apply List.mem_range.mpr
      omega)
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using this
  · rintro ⟨hlt, heq, hall⟩
    refine ⟨⟨hlt, ?_⟩, ?_⟩
    · simpa [beq_iff_eq] using heq
    · rw [List.all_iff_forall_prop]
      intro j hj
      rw [List.mem_range] at hj
      apply hall (j + 1)
      · omega
      · omega

theorem cv_canon_hrep {α : Type} {D : ℕ} (f : Equiv.Perm α) (lab : α ≃ Fin D) (F : ℕ → ℕ)
    (hF : ∀ e, F (lab e) = lab (f e)) (e : α) (he : Function.minimalPeriod f e = 6) :
    cvCanon F D (cvHrep F (lab e)) = true := by
  have hit := cv_iter_lab f lab F hF
  have hpow : ∀ n : ℕ, (f ^ n) e = f^[n] e := fun n => by rw [Equiv.Perm.coe_pow]
  have hmod : ∀ n : ℕ, (f ^ n) e = (f ^ (n % 6)) e := fun n => by
    rw [hpow, hpow, ← he, Function.iterate_mod_minimalPeriod_eq]
  have hinj : ∀ a b : ℕ, a < 6 → b < 6 → (f ^ a) e = (f ^ b) e → a = b := by
    intro a b ha hb h
    rw [hpow, hpow] at h
    exact Function.iterate_injOn_Iio_minimalPeriod (by rw [he]; exact ha) (by rw [he]; exact hb) h
  obtain ⟨⟨j0, hj0, hr⟩, hmin⟩ := cv_hrep_spec F (lab e)
  rw [hit] at hr
  have hr' : cvHrep F (lab e) = ((lab ((f ^ j0) e) : Fin D) : ℕ) := hr
  rw [cv_canon_spec, hr']
  refine ⟨(lab _).isLt, ?_, fun j hj1 hj6 => ?_⟩
  · rw [hit, ← Equiv.Perm.mul_apply, ← pow_add, hmod (6 + j0)]
    rw [show (6 + j0) % 6 = j0 by omega]
  · rw [hit, ← Equiv.Perm.mul_apply, ← pow_add, hmod (j + j0)]
    have hle := hmin ((j + j0) % 6) (Nat.mod_lt _ (by norm_num))
    rw [hr', hit] at hle
    refine lt_of_le_of_ne hle fun heq => ?_
    have h2 := hinj _ _ (Nat.mod_lt _ (by norm_num)) hj0 (lab.injective (Fin.val_injective heq.symm))
    omega

theorem cv_minimalPeriod_of_canon {α : Type} {D : ℕ} (f : Equiv.Perm α) (lab : α ≃ Fin D)
    (F : ℕ → ℕ) (hF : ∀ e, F (lab e) = lab (f e)) (e : α) (h : cvCanon F D (lab e) = true) :
    Function.minimalPeriod f e = 6 := by

  have h_and : (decide (lab e < D) && cvIter F (lab e) 6 == lab e) = true ∧
      (List.range 5).all (fun j => decide (lab e < cvIter F (lab e) (j + 1))) = true := by
    simpa [cvCanon] using h
  rcases h_and with ⟨h_and1, h_all⟩
  have h_lt : lab e < D := by
    have := ((Bool.and_eq_true _ _).mp h_and1).1
    exact of_decide_eq_true this
  have h_eq6 : cvIter F (lab e) 6 = lab e := by
    have := ((Bool.and_eq_true _ _).mp h_and1).2
    simpa [beq_iff_eq] using this
  have h_lt5 : ∀ j, j < 5 → lab e < cvIter F (lab e) (j + 1) := by
    have := List.all_eq_true.mp h_all
    intro j hj
    have hj' : j ∈ List.range 5 := by
      rw [List.mem_range]
      exact hj
    exact of_decide_eq_true (this j hj')

  have h_eq6_iter : cvIter F (lab e) 6 = (lab ((f ^ 6) e) : ℕ) := by
    simpa using cv_iter_lab f lab F hF e 6
  have h_eq6_val : (lab ((f ^ 6) e) : ℕ) = (lab e : ℕ) := by
    rw [← h_eq6_iter, h_eq6]
  have h_eq6_lab : lab ((f ^ 6) e) = lab e := by
    exact Fin.ext h_eq6_val
  have h_eq6_e : (f ^ 6) e = e := by
    apply lab.injective
    exact h_eq6_lab
  have h_iter_eq6 : f^[6] e = e := by
    rw [Equiv.Perm.iterate_eq_pow, h_eq6_e]
  have h_periodic : Function.IsPeriodicPt f 6 e := by
    rw [Function.IsPeriodicPt]
    exact h_iter_eq6
  have hpos6 : 0 < 6 := by norm_num
  have hpos_min : 0 < Function.minimalPeriod f e :=
    Function.IsPeriodicPt.minimalPeriod_pos hpos6 h_periodic
  have hle_min : Function.minimalPeriod f e ≤ 6 :=
    Function.IsPeriodicPt.minimalPeriod_le hpos6 h_periodic
  have hiter_min : f^[Function.minimalPeriod f e] e = e :=
    Function.iterate_minimalPeriod
  by_cases hlt : Function.minimalPeriod f e < 6
  ·
    have h_lt5_val : Function.minimalPeriod f e - 1 < 5 := by
      omega

    set j := Function.minimalPeriod f e - 1 with hj_def
    have hj_lt5 : j < 5 := by
      omega
    have h_lt_val : lab e < cvIter F (lab e) (j + 1) := h_lt5 j hj_lt5
    have hj_succ : j + 1 = Function.minimalPeriod f e := by
      omega
    rw [hj_succ, cv_iter_lab f lab F hF e (Function.minimalPeriod f e)] at h_lt_val

    have h_eq_e : (f ^ Function.minimalPeriod f e) e = e := by
      rw [← Equiv.Perm.iterate_eq_pow, hiter_min]
    rw [h_eq_e] at h_lt_val

    exact absurd h_lt_val (lt_irrefl _)
  ·
    exact le_antisymm hle_min (Nat.le_of_not_lt hlt)

theorem cv_eq_of_canon_sameCycle {α : Type} [Fintype α] [DecidableEq α] {D : ℕ}
    (f : Equiv.Perm α) (lab : α ≃ Fin D) (F : ℕ → ℕ) (hF : ∀ e, F (lab e) = lab (f e)) (e e' : α)
    (h : cvCanon F D (lab e) = true) (h' : cvCanon F D (lab e') = true) (hs : f.SameCycle e e') :
    e = e' := by

  have h_unfold_e : decide ((lab e).val < D) = true ∧ (cvIter F (lab e) 6 = (lab e).val) ∧
      ((List.range 5).all (fun j => decide ((lab e).val < cvIter F (lab e) (j + 1)))) = true := by
    simpa [cvCanon, Bool.and_eq_true_iff] using h
  have h_unfold_e' : decide ((lab e').val < D) = true ∧ (cvIter F (lab e') 6 = (lab e').val) ∧
      ((List.range 5).all (fun j => decide ((lab e').val < cvIter F (lab e') (j + 1)))) = true := by
    simpa [cvCanon, Bool.and_eq_true_iff] using h'
  rcases h_unfold_e with ⟨h_lt_e, h_eq6_e, h_all_e⟩
  rcases h_unfold_e' with ⟨h_lt_e', h_eq6_e', h_all_e'⟩

  have h_lt_succ_e : ∀ j, j < 5 → (lab e).val < cvIter F (lab e) (j + 1) := by
    intro j hj
    have hmem : j ∈ List.range 5 := List.mem_range.mpr hj
    have h_decide := (List.all_eq_true.mp h_all_e) j hmem
    simpa [decide_eq_true_eq] using h_decide
  have h_lt_succ_e' : ∀ j, j < 5 → (lab e').val < cvIter F (lab e') (j + 1) := by
    intro j hj
    have hmem : j ∈ List.range 5 := List.mem_range.mpr hj
    have h_decide := (List.all_eq_true.mp h_all_e') j hmem
    simpa [decide_eq_true_eq] using h_decide

  have h_fix_e : (f ^ 6) e = e := by
    have h_eq6_val : cvIter F (lab e) 6 = (lab e).val := h_eq6_e
    rw [cv_iter_lab f lab F hF e 6] at h_eq6_val
    have h_eq_fin : lab ((f ^ 6) e) = lab e := by
      apply Fin.ext
      simpa using h_eq6_val
    exact lab.injective h_eq_fin
  have h_lt_succ_pow_e : ∀ j, j < 5 → (lab e).val < (lab ((f ^ (j + 1)) e)).val := by
    intro j hj
    have h_lt := h_lt_succ_e j hj
    rw [cv_iter_lab f lab F hF e (j + 1)] at h_lt
    exact h_lt
  have h_fix_e' : (f ^ 6) e' = e' := by
    have h_eq6_val' : cvIter F (lab e') 6 = (lab e').val := h_eq6_e'
    rw [cv_iter_lab f lab F hF e' 6] at h_eq6_val'
    have h_eq_fin' : lab ((f ^ 6) e') = lab e' := by
      apply Fin.ext
      simpa using h_eq6_val'
    exact lab.injective h_eq_fin'
  have h_lt_succ_pow_e' : ∀ j, j < 5 → (lab e').val < (lab ((f ^ (j + 1)) e')).val := by
    intro j hj
    have h_lt := h_lt_succ_e' j hj
    rw [cv_iter_lab f lab F hF e' (j + 1)] at h_lt
    exact h_lt

  obtain ⟨n, hn_lt, hn_eq⟩ := hs.exists_pow_eq'

  let q := n / 6
  let r := n % 6
  have h_n_eq : n = 6 * q + r := by
    dsimp [q, r]
    exact (Nat.div_add_mod n 6).symm
  have hr_lt_6 : r < 6 := Nat.mod_lt n (by norm_num)

  have h_pow_reduce : (f ^ n) e = (f ^ r) e := by
    rw [h_n_eq]
    have h_fix_pow : ∀ k : ℕ, ((f ^ 6) ^ k) e = e := by
      intro k
      induction' k with k ih
      · rfl
      · rw [pow_succ']
        simp [ih, h_fix_e]
    have h_comm : ((f ^ 6) ^ q) * (f ^ r) = (f ^ r) * ((f ^ 6) ^ q) := by
      calc
        ((f ^ 6) ^ q) * (f ^ r) = (f ^ (6 * q)) * (f ^ r) := by rw [pow_mul]
        _ = (f ^ r) * (f ^ (6 * q)) := by rw [pow_mul_comm f (6 * q) r]
        _ = (f ^ r) * ((f ^ 6) ^ q) := by rw [pow_mul]
    calc
      (f ^ (6 * q + r)) e = ((f ^ (6 * q)) * (f ^ r)) e := by rw [pow_add]
      _ = (f ^ (6 * q)) ((f ^ r) e) := rfl
      _ = ((f ^ 6) ^ q) ((f ^ r) e) := by rw [pow_mul]
      _ = ((f ^ 6) ^ q * f ^ r) e := rfl
      _ = (f ^ r * (f ^ 6) ^ q) e := by rw [h_comm]
      _ = (f ^ r) (((f ^ 6) ^ q) e) := rfl
      _ = (f ^ r) e := by rw [h_fix_pow q]

  have h_e'_eq : e' = (f ^ r) e := by
    rw [← hn_eq, h_pow_reduce]

  rcases Nat.eq_zero_or_pos r with (hr_zero | hr_pos)
  ·
    rw [hr_zero, pow_zero] at h_e'_eq
    exact h_e'_eq.symm
  ·
    have hr_lt_6' : r < 6 := hr_lt_6
    by_cases hr_lt_5 : r < 5
    ·
      have h_lt_val : (lab e).val < (lab ((f ^ r) e)).val := by
        have hj : r - 1 < 5 := by omega
        have h := h_lt_succ_pow_e (r - 1) hj
        have h_pow_eq : (f ^ ((r - 1) + 1)) e = (f ^ r) e := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
        simpa [h_pow_eq] using h
      have h_lt_val' : (lab e').val < (lab e).val := by
        have h := h_lt_succ_pow_e' ((6 - r) - 1) (by omega)
        have h_pow_eq : (f ^ (((6 - r) - 1) + 1)) e' = (f ^ (6 - r)) e' := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ 6 - r)]
        have h_comp : (f ^ (6 - r)) e' = e := by
          rw [h_e'_eq]
          calc
            (f ^ (6 - r)) ((f ^ r) e) = ((f ^ (6 - r)) * (f ^ r)) e := rfl
            _ = (f ^ ((6 - r) + r)) e := by rw [pow_add]
            _ = (f ^ 6) e := by rw [Nat.sub_add_cancel (by omega : r ≤ 6)]
            _ = e := h_fix_e
        simpa [h_pow_eq, h_comp] using h
      have h_lt1 : (lab e).val < (lab e').val := by
        simpa [h_e'_eq] using h_lt_val
      exact absurd h_lt_val' (lt_asymm h_lt1)
    ·
      have hr_eq_5 : r = 5 := by omega
      dsimp [r] at *
      have hr_eq_5' : n % 6 = 5 := hr_eq_5

      have h_lt_val : (lab e).val < (lab ((f ^ (n % 6)) e)).val := by
        have h := h_lt_succ_pow_e 4 (by decide : 4 < 5)
        have h_pow_eq : (f ^ (4 + 1)) e = (f ^ (n % 6)) e := by

          rw [show (4 : ℕ) + 1 = 5 by decide, hr_eq_5']
        simpa [h_pow_eq] using h
      have h_lt_val' : (lab e').val < (lab e).val := by
        have h := h_lt_succ_pow_e' 0 (by decide : 0 < 5)
        have h_f1 : f e' = e := by
          calc
            f e' = (f ^ 1) e' := by simp
            _ = (f ^ 1) ((f ^ (n % 6)) e) := by rw [h_e'_eq]
            _ = ((f ^ 1) * (f ^ (n % 6))) e := rfl
            _ = (f ^ (1 + n % 6)) e := by rw [pow_add]
            _ = (f ^ 6) e := by rw [hr_eq_5']
            _ = e := h_fix_e
        simpa [h_f1] using h
      have h_lt1 : (lab e).val < (lab e').val := by
        simpa [h_e'_eq] using h_lt_val
      exact absurd h_lt_val' (lt_asymm h_lt1)

theorem cv_hrep_mem {α : Type} {D : ℕ} (f : Equiv.Perm α) (lab : α ≃ Fin D) (F : ℕ → ℕ)
    (hF : ∀ e, F (lab e) = lab (f e)) (e : α) :
    ∃ j < 6, cvHrep F (lab e) = ((lab ((f ^ j) e) : Fin D) : ℕ) := by
  let i : ℕ := lab e
  have h_iter (j : ℕ) : cvIter F i j = lab ((f ^ j) e) := cv_iter_lab f lab F hF e j
  unfold cvHrep
  have h0 := min_choice i (min (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)))))
  rcases h0 with (h0 | hrest)
  ·
    refine ⟨0, by decide, ?_⟩
    rw [h0]
    simp [i]
  ·
    have h1 := min_choice (cvIter F i 1) (min (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))))
    rcases h1 with (h1a | h1b)
    ·
      refine ⟨1, by decide, ?_⟩
      rw [hrest, h1a]
      simpa using h_iter 1
    ·
      have h2 := min_choice (cvIter F i 2) (min (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5)))
      rcases h2 with (h2a | h2b)
      ·
        refine ⟨2, by decide, ?_⟩
        rw [hrest, h1b, h2a]
        simpa using h_iter 2
      ·
        have h3 := min_choice (cvIter F i 3) (min (cvIter F i 4) (cvIter F i 5))
        rcases h3 with (h3a | h3b)
        ·
          refine ⟨3, by decide, ?_⟩
          rw [hrest, h1b, h2b, h3a]
          simpa using h_iter 3
        ·
          have h4 := min_choice (cvIter F i 4) (cvIter F i 5)
          rcases h4 with (h4a | h4b)
          ·
            refine ⟨4, by decide, ?_⟩
            rw [hrest, h1b, h2b, h3b, h4a]
            simpa using h_iter 4
          ·
            refine ⟨5, by decide, ?_⟩
            rw [hrest, h1b, h2b, h3b, h4b]
            simpa using h_iter 5

theorem cv_sort_mem_sublistsLen (L : List ℕ) (hL : L.Pairwise (· < ·)) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x ∈ L) : S.sort (· ≤ ·) ∈ List.sublistsLen S.card L := by
  rw [List.mem_sublistsLen]
  constructor
  ·
    refine List.sublist_of_subperm_of_pairwise (r := (· ≤ ·)) ?_ ?_ ?_
    ·
      apply (Finset.sort_nodup S (· ≤ ·)).subperm
      intro x hx
      have hxS : x ∈ S := by
        rwa [Finset.mem_sort] at hx
      exact hS x hxS
    ·
      exact Finset.pairwise_sort S (· ≤ ·)
    ·
      exact hL.imp le_of_lt
  ·
    exact Finset.length_sort (· ≤ ·)

theorem cv_canonList_spec (F : ℕ → ℕ) (D : ℕ) :
    (cvCanonList F D).Pairwise (· < ·) ∧ ∀ i, i ∈ cvCanonList F D ↔ cvCanon F D i = true := by
  have h_range_pairwise : (List.range D).Pairwise (· < ·) := List.pairwise_lt_range
  have h_filter_pairwise : (cvCanonList F D).Pairwise (· < ·) := by
    dsimp [cvCanonList]
    exact List.Pairwise.filter (cvCanon F D) h_range_pairwise
  have h_mem : ∀ i, i ∈ cvCanonList F D ↔ cvCanon F D i = true := by
    intro i
    dsimp [cvCanonList]
    simp only [List.mem_filter, List.mem_range, cvCanon]
    constructor
    · rintro ⟨hlt, h⟩
      exact h
    · intro h
      have hlt : i < D := by
        have hdecide : decide (i < D) = true := Bool.and_elim_left (Bool.and_elim_left h)
        exact Bool.of_decide_true hdecide
      exact ⟨hlt, h⟩
  exact And.intro h_filter_pairwise h_mem

theorem cv_perm_of_mem {k : ℕ} (r : Fin k → ℕ) (hr : Function.Injective r) (q : Fin k → ℕ)
    (h : ∀ m, ∃ m', q m' = r m) : ∃ σ : Fin k ≃ Fin k, ∀ m, q (σ m) = r m := by
  choose σ₀ hσ₀ using h
  have h_inj : Function.Injective σ₀ := by
    intro a b h_eq
    apply hr
    calc
      r a = q (σ₀ a) := (hσ₀ a).symm
      _ = q (σ₀ b) := by rw [h_eq]
      _ = r b := hσ₀ b
  have h_bij : Function.Bijective σ₀ :=
    (Finite.injective_iff_bijective.mp h_inj)
  exact ⟨Equiv.ofBijective σ₀ h_bij, hσ₀⟩

theorem cv_inj_of_nodup (k : ℕ) (q : ℕ → ℕ) (h : ((List.range k).map q).Nodup) (m m' : ℕ)
    (hm : m < k) (hm' : m' < k) (he : q m = q m') : m = m' := by
  have hinj := List.inj_on_of_nodup_map h
  have hm_mem : m ∈ List.range k := by
    rw [List.mem_range]
    exact hm
  have hm'_mem : m' ∈ List.range k := by
    rw [List.mem_range]
    exact hm'
  exact hinj hm_mem hm'_mem he

theorem cv_consts_pFull :
    (5485728400226463897 : ℝ) / 2 ^ 62 ≤ (118952772983819258225 : ℝ) / 100000000000000000000 ∧
      (120830549335659207180 : ℝ) / 100000000000000000000 ≤ (5572325549701602698 : ℝ) / 2 ^ 62 ∧
      2 * ((120830549335659207180 : ℝ) / 100000000000000000000) ≤ (11144651099403205396 : ℝ) / 2 ^ 62 ∧
      (314159265358979323847 : ℝ) / 100000000000000000000 ≤ (14488038916154245685 : ℝ) / 2 ^ 62 := by
  norm_num

theorem cv_consts_d :
    (4318872327539817176 : ℝ) / 2 ^ 62 ≤ 5365785 / 100000 * (Real.pi / 180) ∧
      566716 / 10000 * (Real.pi / 180) ≤ (4561446368004038610 : ℝ) / 2 ^ 62 ∧
      3 * (566716 / 10000 * (Real.pi / 180)) ≤ (13684339104012115830 : ℝ) / 2 ^ 62 := by
  have hpos_2pow62 : (0 : ℝ) < 2 ^ 62 := by norm_num
  have hpos_100000 : (0 : ℝ) < 100000 := by norm_num
  have hpos_10000 : (0 : ℝ) < 10000 := by norm_num
  have hpos_180 : (0 : ℝ) < 180 := by norm_num
  have h1 : (4318872327539817176 : ℝ) / 2 ^ 62 ≤ 5365785 / 100000 * (Real.pi / 180) := by
    field_simp [hpos_2pow62.ne', hpos_100000.ne', hpos_180.ne']
    have hL : (4318872327539817176 : ℝ) * 100000 * 180 ≤ (5365785 : ℝ) * (3.14159265358979323846 : ℝ) * (2 : ℝ) ^ 62 := by
      norm_num
    have hpi := Real.pi_gt_d20
    nlinarith
  have h2 : 566716 / 10000 * (Real.pi / 180) ≤ (4561446368004038610 : ℝ) / 2 ^ 62 := by
    field_simp [hpos_2pow62.ne', hpos_10000.ne', hpos_180.ne']
    have hL : (566716 : ℝ) * (3.14159265358979323847 : ℝ) * (2 : ℝ) ^ 62 ≤ (4561446368004038610 : ℝ) * 10000 * 180 := by
      norm_num
    have hpi := Real.pi_lt_d20
    nlinarith
  have h3 : 3 * (566716 / 10000 * (Real.pi / 180)) ≤ (13684339104012115830 : ℝ) / 2 ^ 62 := by
    field_simp [hpos_2pow62.ne', hpos_10000.ne', hpos_180.ne']
    have hL : (3 : ℝ) * (566716 : ℝ) * (3.14159265358979323847 : ℝ) * (2 : ℝ) ^ 62 ≤ (13684339104012115830 : ℝ) * 10000 * 180 := by
      norm_num
    have hpi := Real.pi_lt_d20
    nlinarith
  exact And.intro h1 (And.intro h2 h3)

end Tammes15.D3Kernel.Kinds
