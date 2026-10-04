import Tammes15.D3lp.Cuts

open Real

namespace Tammes15.D3lp

open Tammes15
open scoped Classical

theorem PentRel.rev {d u₀ u₁ u₂ u₃ u₄ : ℝ} (h : PentRel d u₀ u₁ u₂ u₃ u₄) :
    PentRel d u₀ u₄ u₃ u₂ u₁ := by
  unfold PentRel at h ⊢
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  have eta_symm (g e f : ℝ) : eta g e f = eta g f e := by
    unfold eta
    simp [mul_comm]
  have gam_symm (g e f : ℝ) : gam g e f = gam g f e := by
    unfold gam
    rw [eta_symm g e f]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← eta_symm d (ebase d u₁) (ebase d u₄)]; exact h1
  · exact h3
  · exact h2
  · rw [gam_symm d (ebase d u₄) (ebase d u₁)]; linarith
  · exact h6
  · exact h5

theorem HexRel.rev {d u₀ u₁ u₂ u₃ u₄ u₅ : ℝ} (h : HexRel d u₀ u₁ u₂ u₃ u₄ u₅) :
    HexRel d u₀ u₅ u₄ u₃ u₂ u₁ := by
  unfold HexRel
  rcases h with ⟨hη1, hη2, hη3, hcorner0, hcorner2, hcorner4⟩
  have h_symm_eta : ∀ g e f : ℝ, eta g e f = eta g f e := by
    intro g e f
    unfold eta
    ring
  have h_symm_gam : ∀ g e f : ℝ, gam g e f = gam g f e := by
    intro g e f
    unfold gam
    rw [h_symm_eta g e f]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_symm_eta (ebase d u₃) (ebase d u₅) (ebase d u₁)]
    exact hη1
  · rw [h_symm_eta (ebase d u₁) (ebase d u₅) (ebase d u₃)]
    exact hη3
  · rw [h_symm_eta (ebase d u₅) (ebase d u₃) (ebase d u₁)]
    exact hη2
  · rw [← h_symm_gam (ebase d u₃) (ebase d u₁) (ebase d u₅)]
    rw [hcorner0]
    ring
  · rw [← h_symm_gam (ebase d u₁) (ebase d u₃) (ebase d u₅)]
    rw [hcorner4]
    ring
  · rw [← h_symm_gam (ebase d u₅) (ebase d u₁) (ebase d u₃)]
    rw [hcorner2]
    ring

theorem HexDiagRel.symm {d a b : ℝ} (h : HexDiagRel d a b) : HexDiagRel d b a :=
  ⟨h.2, h.1⟩

section Code

variable {P : PlaneGraph} {c : GCode} {lab : P.G.Dart ≃ Fin c.D}

theorem vars_dv {k : ℕ} (A : Assign P k) (e : P.G.Dart) : vars lab A (dv (lab e)) = A.corner e := by
  simp [vars, dv, Equiv.symm_apply_apply, Fin.eta]

theorem faceIter_lab (hm : Matches P c lab) (e : P.G.Dart) (j : ℕ) :
    c.faceIter (lab e) j = lab ((P.R.face ^ j) e) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp [GCode.faceIter, hm.face, ih, pow_succ']

open Tammes15 Tammes15.D3lp
open scoped Classical

private lemma faceIter_succ (c : GCode) (i t : ℕ) (ht : 0 < t) :
    c.faceIter i t = c.faceAt (c.faceIter i (t - 1)) := by
  have h := Nat.sub_add_cancel ht
  calc
    c.faceIter i t = c.faceIter i ((t - 1) + 1) := by rw [h]
    _ = c.faceAt (c.faceIter i (t - 1)) := by rw [GCode.faceIter]

private lemma period_spec_aux (c : GCode) (i : ℕ) (fuel cur t m : ℕ)
    (hcur : cur = c.faceIter i (t - 1))
    (ht : 1 ≤ t)
    (hne : ∀ s, 0 < s → s < t → c.faceIter i s ≠ i)
    (hperiod : c.periodGo i fuel cur t = m)
    (hm : 0 < m) :
    c.faceIter i m = i ∧ ∀ s, 0 < s → s < m → c.faceIter i s ≠ i := by
  induction' fuel with fuel ih generalizing cur t m
  ·
    simp [GCode.periodGo] at hperiod

    rw [← hperiod] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  ·
    simp [GCode.periodGo] at hperiod
    by_cases hface : c.faceAt cur = i
    ·
      simp [hface] at hperiod

      subst hperiod
      have hface_iter_m : c.faceIter i t = i := by
        rw [faceIter_succ c i t (by omega), ← hcur, hface]
      exact ⟨hface_iter_m, hne⟩
    ·
      simp [hface] at hperiod

      have hcur' : c.faceAt cur = c.faceIter i ((t + 1) - 1) := by
        have hsub : (t + 1 : ℕ) - 1 = t := by omega
        rw [hsub, hcur, ← faceIter_succ c i t (by omega)]
      have ht' : 1 ≤ t + 1 := by omega
      have hne' : ∀ s, 0 < s → s < t + 1 → c.faceIter i s ≠ i := by
        intro s hs_pos hs_lt
        by_cases hs_eq_t : s = t
        · rw [hs_eq_t, faceIter_succ c i t (by omega), ← hcur]
          exact hface
        · apply hne s hs_pos
          omega
      exact ih (c.faceAt cur) (t + 1) m hcur' ht' hne' hperiod hm

theorem period_spec (c : GCode) (i m : ℕ) (h : c.period i = m) (hm : 0 < m) :
    c.faceIter i m = i ∧ ∀ t, 0 < t → t < m → c.faceIter i t ≠ i := by
  have hperiod_def : c.period i = c.periodGo i 6 i 1 := rfl
  rw [hperiod_def] at h
  have ht : 1 ≤ 1 := le_refl 1
  have hne : ∀ s, 0 < s → s < 1 → c.faceIter i s ≠ i := by
    intro s hs_pos hs_lt
    omega
  have hcur : i = c.faceIter i (1 - 1) := by
    simp [GCode.faceIter]
  exact period_spec_aux c i 6 i 1 m hcur ht hne h hm

theorem minimalPeriod_eq_of_first_return {α : Type} (f : α → α) (x : α) (m : ℕ)
    (hm : 0 < m) (hx : f^[m] x = x) (hfirst : ∀ t, 0 < t → t < m → f^[t] x ≠ x) :
    Function.minimalPeriod f x = m := by
  have hx' : Function.IsPeriodicPt f m x := hx
  have hpos : 0 < Function.minimalPeriod f x :=
    Function.IsPeriodicPt.minimalPeriod_pos hm hx'
  have hle : Function.minimalPeriod f x ≤ m :=
    Function.IsPeriodicPt.minimalPeriod_le hm hx'
  have hiter : f^[Function.minimalPeriod f x] x = x :=
    Function.iterate_minimalPeriod
  by_cases h : Function.minimalPeriod f x < m
  · exact absurd hiter (hfirst (Function.minimalPeriod f x) hpos h)
  · exact le_antisymm hle (Nat.le_of_not_lt h)

theorem fsize_of_period (hm : Matches P c lab) (e : P.G.Dart) {m : ℕ}
    (h : c.period (lab e) = m) (hpos : 0 < m) : fsize P e = m := by
  rw [fsize]
  apply minimalPeriod_eq_of_first_return (P.R.face) e m hpos
  ·
    have hspec := (period_spec c (lab e) m h hpos).left
    have h_iter := faceIter_lab hm e m
    have h_eq : (P.R.face ^ m) e = e := by
      apply lab.injective
      apply Fin.val_injective
      simpa using h_iter.symm.trans hspec
    calc
      (P.R.face)^[m] e = ((P.R.face : Equiv.Perm P.G.Dart) ^ m) e := by
        simp [Equiv.Perm.coe_pow]
      _ = e := h_eq
  ·
    intro t ht_pos ht_lt
    have hspec := (period_spec c (lab e) m h hpos).right t ht_pos ht_lt
    have h_iter := faceIter_lab hm e t
    have h_ne : (P.R.face ^ t) e ≠ e := by
      intro h_eq
      apply hspec
      calc
        c.faceIter (lab e) t = lab ((P.R.face ^ t) e) := h_iter
        _ = lab e := by rw [h_eq]
    intro h_iterate
    apply h_ne
    calc
      (P.R.face ^ t) e = ((P.R.face : Equiv.Perm P.G.Dart) ^ t) e := rfl
      _ = (P.R.face)^[t] e := by symm; simp [Equiv.Perm.coe_pow]
      _ = e := h_iterate

theorem vertex_lt (hm : Matches P c lab) (v : ℕ)
    (h : ((List.range c.D).filter fun i => c.fstAt i == v).isEmpty = false) : v < P.n := by
  have h_nonempty : ((List.range c.D).filter fun i => c.fstAt i == v).isEmpty = false := h
  rcases (List.isEmpty_eq_false_iff_exists_mem.mp h_nonempty) with ⟨i, hi⟩
  rcases (List.mem_filter.mp hi) with ⟨hi_range, hi_eq⟩
  have hi_lt : i < c.D := by
    simpa [List.mem_range] using hi_range
  have h_fst_eq : c.fstAt i = v := by
    simpa using hi_eq
  set e := lab.symm ⟨i, hi_lt⟩ with he
  have h_lab : lab e = ⟨i, hi_lt⟩ := by
    rw [he]
    exact Equiv.apply_symm_apply lab ⟨i, hi_lt⟩
  have h_fst' : c.fstAt i = (e.fst : ℕ) := by
    calc
      c.fstAt i = c.fstAt (lab e) := by rw [h_lab]
      _ = (e.fst : ℕ) := hm.fst e
  have h_v_eq : v = (e.fst : ℕ) := by
    rw [← h_fst_eq, h_fst']
  rw [h_v_eq]
  exact Fin.isLt e.fst

theorem eval_vertexTerms (hm : Matches P c lab) {k : ℕ} (A : Assign P k) (v : Fin P.n) (s : ℤ) :
    evalTerms (vertexTerms c v s) (vars lab A) =
      s * ∑ e ∈ Finset.univ.filter (fun e : P.G.Dart => e.fst = v), A.corner e := by
  have h_nodup : (List.range c.D).Nodup := List.nodup_range
  have h_nodup_filter : ((List.range c.D).filter fun i => c.fstAt i == (v : ℕ)).Nodup :=
    h_nodup.filter _

  delta vertexTerms evalTerms dv

  rw [List.map_map]

  have h_comp : ((fun q : ℕ × ℤ => (q.2 : ℝ) * vars lab A q.1) ∘ fun i : ℕ => (i+1, s)) = (fun i : ℕ => (s : ℝ) * vars lab A (i+1)) := by
    rfl
  rw [h_comp]

  rw [List.sum_map_mul_left]

  have h_sum_eq : (List.map (fun i => vars lab A (i+1)) ((List.range c.D).filter fun i => c.fstAt i == (v : ℕ))).sum =
      ((List.range c.D).filter fun i => c.fstAt i == (v : ℕ)).toFinset.sum (fun i => vars lab A (i+1)) := by
    rw [List.sum_toFinset (fun i => vars lab A (i+1)) h_nodup_filter]
  rw [h_sum_eq]

  have h_toFinset_eq : ((List.range c.D).filter fun i => c.fstAt i == (v : ℕ)).toFinset =
      (Finset.range c.D).filter fun i => c.fstAt i = (v : ℕ) := by
    ext i; simp [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, List.mem_range]
  rw [h_toFinset_eq]

  refine congrArg (fun x => (s : ℝ) * x) ?_

  have h_vars_eq (i : ℕ) (hi : i ∈ Finset.range c.D) : vars lab A (i+1) = A.corner (lab.symm ⟨i, Finset.mem_range.mp hi⟩) := by
    have hi_lt : i < c.D := Finset.mem_range.mp hi
    simp [vars, hi_lt]
  apply Finset.sum_bij (fun i hi => lab.symm ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩)
  ·
    intro i hi
    have hi_mem := Finset.mem_filter.mp hi
    have hi_range : i ∈ Finset.range c.D := hi_mem.1
    have hi_fst : c.fstAt i = (v : ℕ) := hi_mem.2
    have hi_lt : i < c.D := Finset.mem_range.mp hi_range
    let e := lab.symm ⟨i, hi_lt⟩
    have he_fst : e.fst = v := by
      have h := hm.fst e
      have hlab : lab e = (⟨i, hi_lt⟩ : Fin c.D) := by
        simp [e]
      rw [hlab] at h
      have h' : (e.fst : ℕ) = (v : ℕ) := by
        calc
          (e.fst : ℕ) = c.fstAt (⟨i, hi_lt⟩ : Fin c.D) := by simpa using h.symm
          _ = c.fstAt i := rfl
          _ = (v : ℕ) := hi_fst
      exact Fin.ext h'
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_fst⟩
  ·
    intro i₁ hi₁ i₂ hi₂ h_eq
    have hi₁_lt : i₁ < c.D := Finset.mem_range.mp (Finset.mem_filter.mp hi₁).1
    have hi₂_lt : i₂ < c.D := Finset.mem_range.mp (Finset.mem_filter.mp hi₂).1
    have h_eq' : lab (lab.symm ⟨i₁, hi₁_lt⟩) = lab (lab.symm ⟨i₂, hi₂_lt⟩) := by rw [h_eq]
    simpa [hi₁_lt, hi₂_lt] using h_eq'
  ·
    intro e he
    have he_mem := Finset.mem_filter.mp he
    have he_fst : e.fst = v := he_mem.2
    let i := (lab e).val
    have hi_lt : i < c.D := (lab e).is_lt
    have hi_range : i ∈ Finset.range c.D := by
      simpa [Finset.mem_range] using hi_lt
    have hi_fst : c.fstAt i = (v : ℕ) := by
      have h := hm.fst e
      simpa [i, he_fst] using h
    have hi_mem : i ∈ (Finset.range c.D).filter fun i => c.fstAt i = (v : ℕ) := by
      refine Finset.mem_filter.mpr ⟨hi_range, hi_fst⟩
    refine ⟨i, hi_mem, ?_⟩
    simp [i]
  ·
    intro i hi
    have hi_range : i ∈ Finset.range c.D := (Finset.mem_filter.mp hi).1
    rw [h_vars_eq i hi_range]

theorem eval_cutTerms (hm : Matches P c lab) {k : ℕ} (A : Assign P k) (e : P.G.Dart) (m : ℕ)
    (rev : Bool) (sgn : ℤ) (w : List ℤ) :
    evalTerms (cutTerms c m (lab e) rev sgn 0 w) (vars lab A) =
      sgn * ∑ j ∈ Finset.range w.length,
        (w.getD j 0 : ℝ) * A.fc e (if rev then (m - j) % m else j) := by

  have hgen : ∀ (j0 : ℕ),
      evalTerms (cutTerms c m (lab e) rev sgn j0 w) (vars lab A) =
        sgn * ∑ j ∈ Finset.range w.length,
          (w.getD j 0 : ℝ) * A.fc e (if rev then (m - (j0 + j)) % m else j0 + j) := by
    intro j0
    induction' w with w ws ih generalizing j0
    ·
      simp [cutTerms, evalTerms]
    ·
      simp only [cutTerms, evalTerms, List.map_cons, List.sum_cons]

      have hface : c.faceIter (lab e) (if rev then (m - j0) % m else j0) =
          lab ((P.R.face ^ (if rev then (m - j0) % m else j0)) e) :=
        faceIter_lab hm e (if rev then (m - j0) % m else j0)
      have hvars : vars lab A (dv (c.faceIter (lab e) (if rev then (m - j0) % m else j0))) =
          A.fc e (if rev then (m - j0) % m else j0) := by
        rw [hface, vars_dv A ((P.R.face ^ (if rev then (m - j0) % m else j0)) e)]
        rfl
      rw [hvars]

      have hlen : (w :: ws).length = ws.length + 1 := rfl
      rw [hlen, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]

      have ih' := ih (j0 + 1)
      have hsum : (List.map (fun q => ↑q.2 * vars lab A q.1) (cutTerms c m (↑(lab e)) rev sgn (j0 + 1) ws)).sum =
          sgn * ∑ j ∈ Finset.range ws.length, (ws.getD j 0 : ℝ) * A.fc e (if rev then (m - ((j0 + 1) + j)) % m else (j0 + 1) + j) := by
        simpa [evalTerms] using ih'
      rw [hsum]

      have hsum' : (∑ j ∈ Finset.range ws.length, (ws.getD j 0 : ℝ) * A.fc e (if rev then (m - ((j0 + 1) + j)) % m else (j0 + 1) + j)) =
                  (∑ j ∈ Finset.range ws.length, (ws.getD j 0 : ℝ) * A.fc e (if rev then (m - (j0 + (j + 1))) % m else j0 + (j + 1))) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp [Nat.add_comm, Nat.add_left_comm]
      rw [hsum']
      simp only [Int.cast_mul]
      ring

  simpa [zero_add] using hgen 0

end Code

section Face

variable {P : PlaneGraph} {k : ℕ}

theorem fc_face_pow (A : Assign P k) (e : P.G.Dart) (s j : ℕ) :
    A.fc ((P.R.face ^ s) e) j = A.fc e (s + j) := by
  simp [Assign.fc, ← Equiv.Perm.mul_apply, ← pow_add, add_comm]

theorem fsize_face_pow (e : P.G.Dart) (s : ℕ) : fsize P ((P.R.face ^ s) e) = fsize P e := by
  unfold fsize
  have h_per : e ∈ Function.periodicPts (P.R.face : P.G.Dart → P.G.Dart) := by
    apply Function.Injective.mem_periodicPts
    exact P.R.face.injective
  calc
    Function.minimalPeriod (P.R.face : P.G.Dart → P.G.Dart) ((P.R.face ^ s) e)
        = Function.minimalPeriod (P.R.face : P.G.Dart → P.G.Dart) ((⇑P.R.face)^[s] e) := by
      simp [Equiv.Perm.iterate_eq_pow]
    _ = Function.minimalPeriod (P.R.face : P.G.Dart → P.G.Dart) e :=
      Function.minimalPeriod_apply_iterate h_per s

theorem fc_mod (A : Assign P k) (e : P.G.Dart) (j : ℕ) : A.fc e j = A.fc e (j % fsize P e) := by
  dsimp [Assign.fc, fsize]
  rw [← Equiv.Perm.iterate_eq_pow (f := P.R.face) (n := j),
    ← Equiv.Perm.iterate_eq_pow (f := P.R.face) (n := j % Function.minimalPeriod P.R.face e),
    Function.iterate_mod_minimalPeriod_eq]

end Face

section Rows

variable {P : PlaneGraph} {c : GCode} {lab : P.G.Dart ≃ Fin c.D} {lo hi : ℝ} {p : Params}
  {k : ℕ} {H : HexChoice P k} {A : Assign P k}

theorem pent_rots (hR : RelSys P H A) (e : P.G.Dart) (he : fsize P e = 5) (rev : Bool) :
    ∀ s : Fin 5,
      PentRel A.d (A.fc e (if rev then (5 - (s : ℕ)) % 5 else s))
        (A.fc e (if rev then (5 - ((s + 1 : Fin 5) : ℕ)) % 5 else (s + 1 : Fin 5)))
        (A.fc e (if rev then (5 - ((s + 2 : Fin 5) : ℕ)) % 5 else (s + 2 : Fin 5)))
        (A.fc e (if rev then (5 - ((s + 3 : Fin 5) : ℕ)) % 5 else (s + 3 : Fin 5)))
        (A.fc e (if rev then (5 - ((s + 4 : Fin 5) : ℕ)) % 5 else (s + 4 : Fin 5))) := by
  intro s
  have hface_size : ∀ (s' : Fin 5), fsize P ((P.R.face ^ (s'.val : ℕ)) e) = 5 := by
    intro s'
    rw [fsize_face_pow, he]
  have hforward : ∀ (s' : Fin 5), PentRel A.d (A.fc e (s' : ℕ)) (A.fc e ((s' + 1 : Fin 5) : ℕ))
      (A.fc e ((s' + 2 : Fin 5) : ℕ)) (A.fc e ((s' + 3 : Fin 5) : ℕ)) (A.fc e ((s' + 4 : Fin 5) : ℕ)) := by
    intro s'
    have hp := hR.pent ((P.R.face ^ (s'.val : ℕ)) e) (hface_size s')
    simpa [fc_face_pow, fc_mod A e, he, Fin.val_add] using hp
  fin_cases s
  ·
    cases rev
    ·
      simpa using hforward 0
    ·
      simpa [show ((0 : Fin 5) : ℕ) = 0 by decide] using PentRel.rev (hforward 0)
  ·
    cases rev
    ·
      simpa using hforward 1
    ·
      simpa [show ((1 : Fin 5) : ℕ) = 1 by decide] using PentRel.rev (hforward 4)
  ·
    cases rev
    ·
      simpa using hforward 2
    ·
      simpa [show ((2 : Fin 5) : ℕ) = 2 by decide] using PentRel.rev (hforward 3)
  ·
    cases rev
    ·
      simpa using hforward 3
    ·
      simpa [show ((3 : Fin 5) : ℕ) = 3 by decide] using PentRel.rev (hforward 2)
  ·
    cases rev
    ·
      simpa using hforward 4
    ·
      simpa [show ((4 : Fin 5) : ℕ) = 4 by decide] using PentRel.rev (hforward 1)

lemma fin_add_nat_val_eq_nat_add_mod (s : Fin 6) (j : ℕ) : ((s + Fin.ofNat 6 j : Fin 6) : ℕ) = ((s : ℕ) + j) % 6 := by
  calc
    ((s + Fin.ofNat 6 j : Fin 6) : ℕ) = (s + Fin.ofNat 6 j).val := rfl
    _ = (s.val + (Fin.ofNat 6 j).val) % 6 := by rw [Fin.val_add]
    _ = (s.val + j % 6) % 6 := by rw [Fin.val_ofNat]
    _ = (s.val + j) % 6 := by omega
    _ = ((s : ℕ) + j) % 6 := rfl

theorem hex_rots (hR : RelSys P H A) (e : P.G.Dart) (he : fsize P e = 6) (rev : Bool) :
    ∀ s : Fin 6,
      HexRel A.d (A.fc e (if rev then (6 - (s : ℕ)) % 6 else s))
        (A.fc e (if rev then (6 - ((s + 1 : Fin 6) : ℕ)) % 6 else (s + 1 : Fin 6)))
        (A.fc e (if rev then (6 - ((s + 2 : Fin 6) : ℕ)) % 6 else (s + 2 : Fin 6)))
        (A.fc e (if rev then (6 - ((s + 3 : Fin 6) : ℕ)) % 6 else (s + 3 : Fin 6)))
        (A.fc e (if rev then (6 - ((s + 4 : Fin 6) : ℕ)) % 6 else (s + 4 : Fin 6)))
        (A.fc e (if rev then (6 - ((s + 5 : Fin 6) : ℕ)) % 6 else (s + 5 : Fin 6))) := by
  intro s
  have hface : ∀ t : ℕ, fsize P ((P.R.face ^ t) e) = 6 := by
    intro t; rw [Tammes15.D3lp.fsize_face_pow, he]
  have fc_shift_nat (k : ℕ) (j : ℕ) : A.fc ((P.R.face ^ k) e) j = A.fc e ((k + j) % 6) := by
    calc
      A.fc ((P.R.face ^ k) e) j = A.fc e (k + j) := Tammes15.D3lp.fc_face_pow A e k j
      _ = A.fc e ((k + j) % fsize P e) := Tammes15.D3lp.fc_mod A e (k + j)
      _ = A.fc e ((k + j) % 6) := by rw [he]
  by_cases hrev : rev
  ·
    fin_cases s <;> simp [hrev] <;> norm_num <;>
      first
        | exact HexRel.rev (hR.hex e (hface 0))
        | (have h := hR.hex ((P.R.face ^ 5) e) (hface 5)
           rw [fc_shift_nat 5 0, fc_shift_nat 5 1, fc_shift_nat 5 2, fc_shift_nat 5 3, fc_shift_nat 5 4, fc_shift_nat 5 5] at h
           have h' := HexRel.rev h
           norm_num at h'
           exact h')
        | (have h := hR.hex ((P.R.face ^ 4) e) (hface 4)
           rw [fc_shift_nat 4 0, fc_shift_nat 4 1, fc_shift_nat 4 2, fc_shift_nat 4 3, fc_shift_nat 4 4, fc_shift_nat 4 5] at h
           have h' := HexRel.rev h
           norm_num at h'
           exact h')
        | (have h := hR.hex ((P.R.face ^ 3) e) (hface 3)
           rw [fc_shift_nat 3 0, fc_shift_nat 3 1, fc_shift_nat 3 2, fc_shift_nat 3 3, fc_shift_nat 3 4, fc_shift_nat 3 5] at h
           have h' := HexRel.rev h
           norm_num at h'
           exact h')
        | (have h := hR.hex ((P.R.face ^ 2) e) (hface 2)
           rw [fc_shift_nat 2 0, fc_shift_nat 2 1, fc_shift_nat 2 2, fc_shift_nat 2 3, fc_shift_nat 2 4, fc_shift_nat 2 5] at h
           have h' := HexRel.rev h
           norm_num at h'
           exact h')
        | (have h := hR.hex ((P.R.face ^ 1) e) (hface 1)
           rw [fc_shift_nat 1 0, fc_shift_nat 1 1, fc_shift_nat 1 2, fc_shift_nat 1 3, fc_shift_nat 1 4, fc_shift_nat 1 5] at h
           have h' := HexRel.rev h
           norm_num at h'
           exact h')
  ·
    fin_cases s <;> simp [hrev] <;> norm_num <;>
      first
        | exact hR.hex e (hface 0)
        | (have h := hR.hex ((P.R.face ^ 1) e) (hface 1)
           rw [fc_shift_nat 1 0, fc_shift_nat 1 1, fc_shift_nat 1 2, fc_shift_nat 1 3, fc_shift_nat 1 4, fc_shift_nat 1 5] at h
           norm_num at h
           exact h)
        | (have h := hR.hex ((P.R.face ^ 2) e) (hface 2)
           rw [fc_shift_nat 2 0, fc_shift_nat 2 1, fc_shift_nat 2 2, fc_shift_nat 2 3, fc_shift_nat 2 4, fc_shift_nat 2 5] at h
           norm_num at h
           exact h)
        | (have h := hR.hex ((P.R.face ^ 3) e) (hface 3)
           rw [fc_shift_nat 3 0, fc_shift_nat 3 1, fc_shift_nat 3 2, fc_shift_nat 3 3, fc_shift_nat 3 4, fc_shift_nat 3 5] at h
           norm_num at h
           exact h)
        | (have h := hR.hex ((P.R.face ^ 4) e) (hface 4)
           rw [fc_shift_nat 4 0, fc_shift_nat 4 1, fc_shift_nat 4 2, fc_shift_nat 4 3, fc_shift_nat 4 4, fc_shift_nat 4 5] at h
           norm_num at h
           exact h)
        | (have h := hR.hex ((P.R.face ^ 5) e) (hface 5)
           rw [fc_shift_nat 5 0, fc_shift_nat 5 1, fc_shift_nat 5 2, fc_shift_nat 5 3, fc_shift_nat 5 4, fc_shift_nat 5 5] at h
           norm_num at h
           exact h)

theorem hexDiag_rots (hR : RelSys P H A) (e : P.G.Dart) (he : fsize P e = 6) (rev : Bool) :
    ∀ s : Fin 6,
      HexDiagRel A.d (A.fc e (if rev then (6 - (s : ℕ)) % 6 else s))
        (A.fc e (if rev then (6 - ((s + 1 : Fin 6) : ℕ)) % 6 else (s + 1 : Fin 6))) := by
  intro s
  by_cases hrev : rev
  ·
    let b := ((5 : Fin 6) - s).val
    have hsize : fsize P ((P.R.face ^ b) e) = 6 := by
      rw [fsize_face_pow e b, he]
    have h := hR.hexDiag ((P.R.face ^ b) e) hsize
    rw [fc_face_pow A e b 0, fc_face_pow A e b 1] at h
    simp at h

    have h_swapped : HexDiagRel A.d (A.fc e (b + 1)) (A.fc e b) := by
      rcases h with ⟨h1, h2⟩
      exact ⟨h2, h1⟩

    have hmod := fc_mod A e (b + 1)
    rw [he] at hmod
    rw [hmod] at h_swapped

    fin_cases s <;> simp [b, hrev] at h_swapped ⊢ <;> exact h_swapped
  ·
    have hsize : fsize P ((P.R.face ^ (s : ℕ)) e) = 6 := by
      rw [fsize_face_pow e (s : ℕ), he]
    have h := hR.hexDiag ((P.R.face ^ (s : ℕ)) e) hsize
    rw [fc_face_pow A e (s : ℕ) 0, fc_face_pow A e (s : ℕ) 1] at h
    simp at h

    have hmod := fc_mod A e ((s : ℕ) + 1)
    rw [he] at hmod
    rw [hmod] at h

    fin_cases s <;> simp [hrev] at h ⊢ <;> exact h

theorem holds_alpha (hp : ParamsValid lo hi p) (hd : lo ≤ A.d ∧ A.d ≤ hi) (up : Bool) {r : Row}
    (hr : rowOf c p (.alpha up) = some r) : r.Holds (vars lab A) := by
  cases up with
  | false =>
    simp [rowOf] at hr
    subst hr
    have hlo := hp.alpha_lo A.d hd.1 hd.2
    have hS := hp.S_pos
    have hpos : 0 < (p.S : ℝ) := by exact_mod_cast hS
    have hineq : (p.alo : ℝ) ≤ (p.S : ℝ) * alpha A.d := by
      have := hlo
      rw [div_le_iff₀ hpos] at this
      linarith
    simp [Row.Holds, evalTerms, vars]
    linarith
  | true =>
    simp [rowOf] at hr
    subst hr
    have hhi := hp.alpha_hi A.d hd.1 hd.2
    have hS := hp.S_pos
    have hpos : 0 < (p.S : ℝ) := by exact_mod_cast hS
    have hineq : (p.S : ℝ) * alpha A.d ≤ (p.ahi : ℝ) := by
      have := hhi
      rw [le_div_iff₀ hpos] at this
      linarith
    simp [Row.Holds, evalTerms, vars]
    exact hineq

theorem holds_corner (hp : ParamsValid lo hi p) (hR : RelSys P H A) (i : ℕ) (up : Bool)
    {r : Row} (hr : rowOf c p (.corner i up) = some r) : r.Holds (vars lab A) := by
  cases up with
  | false =>
    simp [rowOf] at hr
    rcases hr with ⟨hD, hr⟩
    rcases hr with rfl
    simp [Row.Holds, evalTerms, vars, dv, hD]
    have hmem := hR.corner_mem (lab.symm ⟨i, hD⟩)
    linarith
  | true =>
    simp [rowOf] at hr
    rcases hr with ⟨hD, hr⟩
    rcases hr with rfl
    simp [Row.Holds, evalTerms, vars, dv, hD]
    have hS_pos' : 0 < (p.S : ℝ) := by exact_mod_cast hp.S_pos
    have hpi_hi' : (p.S : ℝ) * π ≤ (p.pihi : ℝ) := by
      calc
        (p.S : ℝ) * π ≤ (p.S : ℝ) * ((p.pihi : ℝ) / (p.S : ℝ)) := by
          nlinarith [hp.pi_hi]
        _ = (p.pihi : ℝ) := by field_simp [ne_of_gt hS_pos']
    have hcorner_lt_pi : A.corner (lab.symm ⟨i, hD⟩) < π :=
      (hR.corner_mem (lab.symm ⟨i, hD⟩)).2
    nlinarith

theorem holds_vertex (hm : Matches P c lab) (hp : ParamsValid lo hi p) (hR : RelSys P H A)
    (v : ℕ) (up : Bool) {r : Row} (hr : rowOf c p (.vertex v up) = some r) :
    r.Holds (vars lab A) := by
  dsimp [rowOf] at hr
  by_cases hne : ((List.range c.D).filter fun i => c.fstAt i == v).isEmpty
  ·
    simp [hne] at hr
  ·
    have hne_empty : ((List.range c.D).filter fun i => c.fstAt i == v).isEmpty = false := by
      simpa using hne
    have hv_lt : v < P.n := vertex_lt hm v hne_empty
    let V : Fin P.n := ⟨v, hv_lt⟩
    have hS_pos' : 0 < (p.S : ℝ) := by exact_mod_cast hp.S_pos
    simp [hne] at hr

    by_cases hup : up
    ·
      simp [hup] at hr

      rw [← hr]
      unfold Row.Holds
      rw [eval_vertexTerms hm A V ((p.S : ℤ))]
      rw [hR.vertex_sum V]
      push_cast
      have h := hp.twopi_hi
      have h' := (le_div_iff₀ hS_pos').mp h
      nlinarith
    ·
      simp [hup] at hr

      rw [← hr]
      unfold Row.Holds
      rw [eval_vertexTerms hm A V (-(p.S : ℤ))]
      rw [hR.vertex_sum V]
      push_cast
      have h := hp.twopi_lo
      have h' := (div_le_iff₀ hS_pos').mp h
      nlinarith

theorem holds_tri (hm : Matches P c lab) (hR : RelSys P H A) (i : ℕ) (up : Bool) {r : Row}
    (hr : rowOf c p (.tri i up) = some r) : r.Holds (vars lab A) := by
  by_cases hi : i < c.D
  · by_cases hper : c.period i = 3
    · unfold rowOf at hr
      simp [hi, hper] at hr

      rw [← hr]
      set e := lab.symm ⟨i, hi⟩ with he
      have hlab_fin : lab e = ⟨i, hi⟩ := by
        simpa [he] using Equiv.apply_symm_apply lab ⟨i, hi⟩
      have hfsize : fsize P e = 3 :=
        fsize_of_period hm e (by simpa [hlab_fin] using hper) (by norm_num)
      have hcorner : A.corner e = alpha A.d := hR.tri e hfsize
      have hvars_dv : vars lab A (dv i) = A.corner e := by
        have h_dv_eq : dv (lab e) = dv i := by
          simpa [hlab_fin, dv] using rfl
        rw [← h_dv_eq]
        exact vars_dv A e
      dsimp [Row.Holds, evalTerms, vars]
      split
      · simp [dv, hi]
        calc
          A.corner (lab.symm ⟨i, hi⟩) = A.corner e := by rw [← he]
          _ = alpha A.d := hcorner
          _ ≤ alpha A.d := le_rfl
      · simp [dv, hi]
        calc
          alpha A.d = A.corner e := by rw [hcorner]
          _ = A.corner (lab.symm ⟨i, hi⟩) := by rw [he]
          _ ≤ A.corner (lab.symm ⟨i, hi⟩) := le_rfl
    · unfold rowOf at hr
      simp [hi, hper] at hr
  · unfold rowOf at hr
    simp [hi] at hr

theorem holds_rhOpp (hm : Matches P c lab) (hR : RelSys P H A) (i : ℕ) (up : Bool) {r : Row}
    (hr : rowOf c p (.rhOpp i up) = some r) : r.Holds (vars lab A) := by

  by_cases hcond : i < c.D ∧ c.period i = 4
  · rcases hcond with ⟨hi, hper⟩

    have hcond' : i < c.D ∧ c.period i = 4 := ⟨hi, hper⟩

    dsimp [rowOf] at hr
    simp [hcond'] at hr

    have hr_eq : (if up then ⟨[(dv i, -1), (dv (c.faceIter i 2), 1)], 0⟩
      else ⟨[(dv i, 1), (dv (c.faceIter i 2), -1)], 0⟩) = r := by
      simpa using hr

    set e := lab.symm ⟨i, hi⟩ with he
    have h_lab_e : (lab e : ℕ) = i := by
      simp [e]

    have hper_lab : c.period (lab e : ℕ) = 4 := by
      rw [h_lab_e, hper]
    have hfsize : fsize P e = 4 := by
      apply fsize_of_period hm e hper_lab
      omega

    have h_rhombus : A.corner ((P.R.face ^ 2) e) = A.corner e := by
      have h := (hR.rhombus e hfsize).1
      simpa [Assign.fc, pow_zero] using h

    have h_faceIter : c.faceIter i 2 = (lab ((P.R.face ^ 2) e) : ℕ) := by
      calc
        c.faceIter i 2 = c.faceIter (lab e : ℕ) 2 := by rw [h_lab_e]
        _ = (lab ((P.R.face ^ 2) e) : ℕ) := by rw [faceIter_lab hm e 2]

    subst hr_eq

    cases up with
    | true =>

      unfold Row.Holds
      simp [evalTerms]

      rw [h_faceIter]

      rw [← h_lab_e]

      rw [vars_dv A ((P.R.face ^ 2) e), vars_dv A e]

      rw [h_rhombus]
    | false =>

      unfold Row.Holds
      simp [evalTerms]

      rw [h_faceIter]

      rw [← h_lab_e]

      rw [vars_dv A e, vars_dv A ((P.R.face ^ 2) e)]

      rw [h_rhombus]
  ·
    dsimp [rowOf] at hr
    simp [hcond] at hr

theorem holds_rhLe (hm : Matches P c lab) (hp : ParamsValid lo hi p) (hd : lo ≤ A.d ∧ A.d ≤ hi)
    (hR : RelSys P H A) (i : ℕ) {r : Row} (hr : rowOf c p (.rhLe i) = some r) :
    r.Holds (vars lab A) := by

  unfold rowOf at hr
  simp at hr
  rcases hr with ⟨⟨hi_lt, h_period⟩, hr_eq⟩

  let e : P.G.Dart := lab.symm ⟨i, hi_lt⟩

  have h_fsize : fsize P e = 4 := by
    apply fsize_of_period hm e
    · simpa [e] using h_period
    · norm_num

  have h_rhombus := hR.rhombus e h_fsize
  rcases h_rhombus with ⟨h_fc2, h_fc1⟩

  have h_corner_e := hR.corner_mem e
  have h_corner_f1 := hR.corner_mem ((P.R.face ^ 1) e)
  rcases h_corner_e with ⟨h_alpha_le_fc0, h_fc0_lt_pi⟩
  rcases h_corner_f1 with ⟨h_alpha_le_fc1, h_fc1_lt_pi⟩

  have h_fc0_eq : A.fc e 0 = A.corner e := by
    simp [Assign.fc]
  have h_fc1_eq : A.fc e 1 = A.corner ((P.R.face ^ 1) e) := by
    simp [Assign.fc]

  have hd_pos : 0 < A.d := by
    linarith [hp.lo_pos, hd.1]
  have hd_lt_pi_div_2 : A.d < π / 2 := by
    linarith [hp.hi_lt, hd.2]
  have hd_range : 0 < A.d ∧ A.d < π / 2 := ⟨hd_pos, hd_lt_pi_div_2⟩
  have h_alpha_fc0 : alpha A.d ≤ A.fc e 0 ∧ A.fc e 0 < π := by
    rw [h_fc0_eq]
    exact ⟨h_alpha_le_fc0, h_fc0_lt_pi⟩
  have h_alpha_fc1 : alpha A.d ≤ A.fc e 1 := by
    rw [h_fc1_eq]
    exact h_alpha_le_fc1

  have h_rhombus_rows := Tammes15.rhombus_rows A.d (A.fc e 0) (A.fc e 1) hd_range h_fc1 h_alpha_fc0 h_alpha_fc1
  rcases h_rhombus_rows with ⟨h_fc0_le_2alpha, _, _, _⟩

  have h_vars_dv : vars lab A (dv i) = A.corner e := by
    simpa [e] using vars_dv (lab := lab) A e

  subst hr_eq

  unfold Row.Holds
  have h_eval : evalTerms [(0, -2), (dv i, 1)] (vars lab A) = (-2 : ℝ) * vars lab A 0 + (1 : ℝ) * vars lab A (dv i) := by
    simp [evalTerms]
  rw [h_eval]
  have h_vars_0 : vars lab A 0 = alpha A.d := rfl
  rw [h_vars_0, h_vars_dv]
  rw [h_fc0_eq] at h_fc0_le_2alpha
  simp
  linarith

theorem holds_rhSum (hm : Matches P c lab) (hp : ParamsValid lo hi p)
    (hd : lo ≤ A.d ∧ A.d ≤ hi) (hR : RelSys P H A) (i : ℕ) (up : Bool) {r : Row}
    (hr : rowOf c p (.rhSum i up) = some r) : r.Holds (vars lab A) := by
  simp only [rowOf] at hr
  by_cases hcond : i < c.D ∧ c.period i = 4
  · rw [if_pos hcond] at hr
    obtain ⟨hi_lt, h_period⟩ := hcond
    set e : P.G.Dart := lab.symm ⟨i, hi_lt⟩ with he
    have hle : ((lab e : Fin c.D) : ℕ) = i := by simp [e]
    have h_fsize : fsize P e = 4 := fsize_of_period hm e (by rw [hle]; exact h_period) (by norm_num)
    obtain ⟨_, h_fc1⟩ := hR.rhombus e h_fsize
    obtain ⟨h_a0, h_p0⟩ := hR.corner_mem e
    obtain ⟨h_a1, _⟩ := hR.corner_mem ((P.R.face ^ 1) e)
    have h_fc0_eq : A.fc e 0 = A.corner e := by simp [Assign.fc]
    have h_fc1_eq : A.fc e 1 = A.corner ((P.R.face ^ 1) e) := rfl
    have hd_pos : 0 < A.d := by linarith [hp.lo_pos, hd.1]
    have hd_lt : A.d < π / 2 := by linarith [hp.hi_lt, hd.2]
    obtain ⟨_, _, h3, hS⟩ := Tammes15.rhombus_rows A.d (A.fc e 0) (A.fc e 1) ⟨hd_pos, hd_lt⟩ h_fc1
      ⟨by rw [h_fc0_eq]; exact h_a0, by rw [h_fc0_eq]; exact h_p0⟩ (by rw [h_fc1_eq]; exact h_a1)
    have hv0 : vars lab A (dv i) = A.fc e 0 := by
      rw [h_fc0_eq, ← hle]; exact vars_dv A e
    have hv1 : vars lab A (dv (c.faceIter i 1)) = A.fc e 1 := by
      rw [← hle, faceIter_lab hm e 1, h_fc1_eq]; exact vars_dv A _
    have hv00 : vars lab A 0 = alpha A.d := rfl
    have hSpos : (0 : ℝ) < p.S := by exact_mod_cast hp.S_pos
    have hSs := hp.ssum_hi A.d hd.1 hd.2
    cases up with
    | true =>
      simp only [if_true, Option.some.injEq] at hr
      subst hr
      simp only [Row.Holds, evalTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hv0, hv1]
      push_cast
      have : (p.S : ℝ) * (A.fc e 0 + A.fc e 1) ≤ p.shi := by
        have h1 : Ssum A.d * p.S ≤ p.shi := (le_div_iff₀ hSpos).mp hSs
        nlinarith
      linarith
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hr
      subst hr
      simp only [Row.Holds, evalTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hv0, hv1, hv00]
      push_cast
      linarith
  · rw [if_neg hcond] at hr
    exact absurd hr (by simp)

lemma listGet_mem {α : Type} (l : List α) (k : ℕ) (a : α) (h : listGet l k = some a) : a ∈ l := by
  induction l generalizing k with
  | nil => simp [listGet] at h
  | cons hd tl ih =>
    cases k with
    | zero =>
      simp [listGet] at h
      subst h
      exact List.mem_cons_self
    | succ k =>
      simp [listGet] at h
      apply List.mem_cons_of_mem
      apply ih
      exact h

theorem holds_pent (hm : Matches P c lab) (hp : ParamsValid lo hi p) (hd : lo ≤ A.d ∧ A.d ≤ hi)
    (hR : RelSys P H A) (kk i : ℕ) (rev up : Bool) {r : Row}
    (hr : rowOf c p (.pent kk i rev up) = some r) : r.Holds (vars lab A) := by
  simp [rowOf] at hr
  rcases hr with ⟨⟨h_cD, h_per⟩, hr⟩
  unfold cutRow at hr
  cases h_list : listGet p.pent kk with
  | none => simp [h_list] at hr
  | some cr =>
    simp [h_list] at hr
    by_cases h_wlen : cr.w.length = 5
    · simp [h_wlen] at hr
      set e := lab.symm ⟨i, h_cD⟩ with he_def
      have h_fsize : fsize P e = 5 := by
        apply fsize_of_period hm e
        · calc
            c.period (lab e) = c.period i := by simp [e]
            _ = 5 := h_per
        · norm_num
      have h_mem : cr ∈ p.pent := listGet_mem p.pent kk cr h_list
      have h_pent_cut := (hp.pent cr h_mem).2
      set u : Fin 5 → ℝ := fun j => A.fc e (if rev then (5 - (j : ℕ)) % 5 else (j : ℕ)) with hu_def
      have h_corner_u : ∀ j : Fin 5, alpha A.d ≤ u j ∧ u j < π := by
        intro j
        dsimp [u]
        by_cases hrev : rev
        · simp [hrev]
          have := hR.corner_mem ((P.R.face ^ ((5 - (j : ℕ)) % 5)) e)
          simpa [Assign.fc] using this
        · simp [hrev]
          have := hR.corner_mem ((P.R.face ^ (j : ℕ)) e)
          simpa [Assign.fc] using this
      have h_pent_rel : ∀ s : Fin 5, PentRel A.d
        (u s) (u (s + 1)) (u (s + 2)) (u (s + 3)) (u (s + 4)) := by
        intro s
        dsimp [u]
        simpa using pent_rots hR e h_fsize rev s
      have h_bound := h_pent_cut A.d (hd.1) (hd.2) u h_corner_u h_pent_rel
      rcases h_bound with ⟨h_lo, h_hi⟩
      have h_lab_val : (lab e : ℕ) = i := by simp [e]
      have hS_pos : 0 < (p.S : ℝ) := by exact_mod_cast hp.S_pos
      have h_sum_eq : (∑ j ∈ Finset.range cr.w.length, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (5 - j) % 5 else j)) =
          (p.S : ℝ) * (∑ j : Fin 5, wOf p.S 5 cr.w j * u j) := by
        calc
          (∑ j ∈ Finset.range cr.w.length, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (5 - j) % 5 else j))
              = (∑ j ∈ Finset.range 5, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (5 - j) % 5 else j)) := by
            simp [h_wlen]
          _ = (∑ j : Fin 5, (cr.w.getD (j : ℕ) 0 : ℝ) * A.fc e (if rev then (5 - (j : ℕ)) % 5 else (j : ℕ))) := by
            simp [Finset.sum_range]
          _ = (∑ j : Fin 5, ((cr.w.getD (j : ℕ) 0 : ℝ) / (p.S : ℝ)) * (p.S : ℝ) * A.fc e (if rev then (5 - (j : ℕ)) % 5 else (j : ℕ))) := by
            field_simp [ne_of_gt hS_pos]
          _ = (∑ j : Fin 5, (wOf p.S 5 cr.w j * (p.S : ℝ)) * A.fc e (if rev then (5 - (j : ℕ)) % 5 else (j : ℕ))) := by
            simp [wOf]
          _ = (p.S : ℝ) * (∑ j : Fin 5, wOf p.S 5 cr.w j * u j) := by
            simp [u, Finset.mul_sum, mul_assoc, mul_comm]
      have h_eval_neg := eval_cutTerms hm A e 5 rev (-1) cr.w
      have h_eval_neg' : evalTerms (cutTerms c 5 i rev (-1) 0 cr.w) (vars lab A) =
          (-1 : ℝ) * ∑ j ∈ Finset.range cr.w.length, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (5 - j) % 5 else j) := by
        simpa [h_lab_val] using h_eval_neg
      have h_eval_neg'' : evalTerms (cutTerms c 5 i rev (-1) 0 cr.w) (vars lab A) =
          (-1 : ℝ) * ((p.S : ℝ) * (∑ j : Fin 5, wOf p.S 5 cr.w j * u j)) := by
        rw [h_eval_neg', h_sum_eq]
      have h_eval_pos := eval_cutTerms hm A e 5 rev 1 cr.w
      have h_eval_pos' : evalTerms (cutTerms c 5 i rev 1 0 cr.w) (vars lab A) =
          (1 : ℝ) * ∑ j ∈ Finset.range cr.w.length, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (5 - j) % 5 else j) := by
        simpa [h_lab_val] using h_eval_pos
      have h_eval_pos'' : evalTerms (cutTerms c 5 i rev 1 0 cr.w) (vars lab A) =
          (1 : ℝ) * ((p.S : ℝ) * (∑ j : Fin 5, wOf p.S 5 cr.w j * u j)) := by
        rw [h_eval_pos', h_sum_eq]
      rw [← hr]
      cases up with
      | false =>
        simp
        unfold Row.Holds
        rw [h_eval_neg'']
        simp

        have h_mul : (cr.lo : ℝ) ≤ (p.S : ℝ) * (∑ j : Fin 5, wOf p.S 5 cr.w j * u j) := by
          calc
            (cr.lo : ℝ) = ((cr.lo : ℝ) / (p.S : ℝ)) * (p.S : ℝ) := by field_simp [ne_of_gt hS_pos]
            _ ≤ (∑ j : Fin 5, wOf p.S 5 cr.w j * u j) * (p.S : ℝ) := by
              nlinarith
            _ = (p.S : ℝ) * (∑ j : Fin 5, wOf p.S 5 cr.w j * u j) := by ring
        nlinarith
      | true =>
        simp
        unfold Row.Holds
        rw [h_eval_pos'']
        simp

        have h_mul : (p.S : ℝ) * (∑ j : Fin 5, wOf p.S 5 cr.w j * u j) ≤ (cr.hi : ℝ) := by
          calc
            (p.S : ℝ) * (∑ j : Fin 5, wOf p.S 5 cr.w j * u j) ≤ (p.S : ℝ) * ((cr.hi : ℝ) / (p.S : ℝ)) := by
              nlinarith
            _ = (cr.hi : ℝ) := by field_simp [ne_of_gt hS_pos]
        nlinarith
    · simp [h_wlen] at hr

theorem holds_hex (hm : Matches P c lab) (hp : ParamsValid lo hi p) (hd : lo ≤ A.d ∧ A.d ≤ hi)
    (hR : RelSys P H A) (kk i : ℕ) (rev up : Bool) {r : Row}
    (hr : rowOf c p (.hex kk i rev up) = some r) : r.Holds (vars lab A) := by
  simp [rowOf] at hr
  rcases hr with ⟨⟨h_cD, h_per⟩, hr⟩
  unfold cutRow at hr
  cases h_list : listGet p.hex kk with
  | none => simp [h_list] at hr
  | some cr =>
    simp [h_list] at hr
    by_cases h_wlen : cr.w.length = 6
    · simp [h_wlen] at hr
      set e := lab.symm ⟨i, h_cD⟩ with he_def
      have h_fsize : fsize P e = 6 := by
        apply fsize_of_period hm e
        · calc
            c.period (lab e) = c.period i := by simp [e]
            _ = 6 := h_per
        · norm_num
      have h_mem : cr ∈ p.hex := listGet_mem p.hex kk cr h_list
      have h_hex_cut := (hp.hex cr h_mem).2
      set u : Fin 6 → ℝ := fun j => A.fc e (if rev then (6 - (j : ℕ)) % 6 else (j : ℕ)) with hu_def
      have h_corner_u : ∀ j : Fin 6, alpha A.d ≤ u j ∧ u j < π := by
        intro j
        dsimp [u]
        by_cases hrev : rev
        · simp [hrev]
          have := hR.corner_mem ((P.R.face ^ ((6 - (j : ℕ)) % 6)) e)
          simpa [Assign.fc] using this
        · simp [hrev]
          have := hR.corner_mem ((P.R.face ^ (j : ℕ)) e)
          simpa [Assign.fc] using this
      have h_hex_rel : ∀ s : Fin 6, HexRel A.d
        (u s) (u (s + 1)) (u (s + 2)) (u (s + 3)) (u (s + 4)) (u (s + 5)) := by
        intro s
        dsimp [u]
        simpa using hex_rots hR e h_fsize rev s
      have h_diag : ∀ s : Fin 6, HexDiagRel A.d (u s) (u (s + 1)) := by
        intro s
        dsimp [u]
        simpa using hexDiag_rots hR e h_fsize rev s
      have h_bound := h_hex_cut A.d (hd.1) (hd.2) u h_corner_u h_hex_rel h_diag
      rcases h_bound with ⟨h_lo, h_hi⟩
      have h_lab_val : (lab e : ℕ) = i := by simp [e]
      have hS_pos : 0 < (p.S : ℝ) := by exact_mod_cast hp.S_pos
      have h_sum_eq : (∑ j ∈ Finset.range cr.w.length, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (6 - j) % 6 else j)) =
          (p.S : ℝ) * (∑ j : Fin 6, wOf p.S 6 cr.w j * u j) := by
        calc
          (∑ j ∈ Finset.range cr.w.length, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (6 - j) % 6 else j))
              = (∑ j ∈ Finset.range 6, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (6 - j) % 6 else j)) := by
            simp [h_wlen]
          _ = (∑ j : Fin 6, (cr.w.getD (j : ℕ) 0 : ℝ) * A.fc e (if rev then (6 - (j : ℕ)) % 6 else (j : ℕ))) := by
            simp [Finset.sum_range]
          _ = (∑ j : Fin 6, ((cr.w.getD (j : ℕ) 0 : ℝ) / (p.S : ℝ)) * (p.S : ℝ) * A.fc e (if rev then (6 - (j : ℕ)) % 6 else (j : ℕ))) := by
            field_simp [ne_of_gt hS_pos]
          _ = (∑ j : Fin 6, (wOf p.S 6 cr.w j * (p.S : ℝ)) * A.fc e (if rev then (6 - (j : ℕ)) % 6 else (j : ℕ))) := by
            simp [wOf]
          _ = (p.S : ℝ) * (∑ j : Fin 6, wOf p.S 6 cr.w j * u j) := by
            simp [u, Finset.mul_sum, mul_assoc, mul_comm]
      have h_eval_neg := eval_cutTerms hm A e 6 rev (-1) cr.w
      have h_eval_neg' : evalTerms (cutTerms c 6 i rev (-1) 0 cr.w) (vars lab A) =
          (-1 : ℝ) * ∑ j ∈ Finset.range cr.w.length, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (6 - j) % 6 else j) := by
        simpa [h_lab_val] using h_eval_neg
      have h_eval_neg'' : evalTerms (cutTerms c 6 i rev (-1) 0 cr.w) (vars lab A) =
          (-1 : ℝ) * ((p.S : ℝ) * (∑ j : Fin 6, wOf p.S 6 cr.w j * u j)) := by
        rw [h_eval_neg', h_sum_eq]
      have h_eval_pos := eval_cutTerms hm A e 6 rev 1 cr.w
      have h_eval_pos' : evalTerms (cutTerms c 6 i rev 1 0 cr.w) (vars lab A) =
          (1 : ℝ) * ∑ j ∈ Finset.range cr.w.length, (cr.w.getD j 0 : ℝ) * A.fc e (if rev then (6 - j) % 6 else j) := by
        simpa [h_lab_val] using h_eval_pos
      have h_eval_pos'' : evalTerms (cutTerms c 6 i rev 1 0 cr.w) (vars lab A) =
          (1 : ℝ) * ((p.S : ℝ) * (∑ j : Fin 6, wOf p.S 6 cr.w j * u j)) := by
        rw [h_eval_pos', h_sum_eq]
      rw [← hr]
      cases up with
      | false =>
        simp
        unfold Row.Holds
        rw [h_eval_neg'']
        simp

        have h_mul : (cr.lo : ℝ) ≤ (p.S : ℝ) * (∑ j : Fin 6, wOf p.S 6 cr.w j * u j) := by
          calc
            (cr.lo : ℝ) = ((cr.lo : ℝ) / (p.S : ℝ)) * (p.S : ℝ) := by field_simp [ne_of_gt hS_pos]
            _ ≤ (∑ j : Fin 6, wOf p.S 6 cr.w j * u j) * (p.S : ℝ) := by
              nlinarith
            _ = (p.S : ℝ) * (∑ j : Fin 6, wOf p.S 6 cr.w j * u j) := by ring
        nlinarith
      | true =>
        simp
        unfold Row.Holds
        rw [h_eval_pos'']
        simp

        have h_mul : (p.S : ℝ) * (∑ j : Fin 6, wOf p.S 6 cr.w j * u j) ≤ (cr.hi : ℝ) := by
          calc
            (p.S : ℝ) * (∑ j : Fin 6, wOf p.S 6 cr.w j * u j) ≤ (p.S : ℝ) * ((cr.hi : ℝ) / (p.S : ℝ)) := by
              nlinarith
            _ = (cr.hi : ℝ) := by field_simp [ne_of_gt hS_pos]
        nlinarith
    · simp [h_wlen] at hr

theorem rows_of_relsys (hm : Matches P c lab) (hp : ParamsValid lo hi p)
    (hd : lo ≤ A.d ∧ A.d ≤ hi) (hR : RelSys P H A) (id : RowId) {r : Row}
    (hr : rowOf c p id = some r) : r.Holds (vars lab A) := by
  cases id with
  | alpha up => exact holds_alpha hp hd up hr
  | corner i up => exact holds_corner hp hR i up hr
  | vertex v up => exact holds_vertex hm hp hR v up hr
  | tri i up => exact holds_tri hm hR i up hr
  | rhOpp i up => exact holds_rhOpp hm hR i up hr
  | rhLe i => exact holds_rhLe hm hp hd hR i hr
  | rhSum i up => exact holds_rhSum hm hp hd hR i up hr
  | pent kk i rev up => exact holds_pent hm hp hd hR kk i rev up hr
  | hex kk i rev up => exact holds_hex hm hp hd hR kk i rev up hr

end Rows

end Tammes15.D3lp
