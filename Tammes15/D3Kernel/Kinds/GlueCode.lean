import Tammes15.D3Kernel.Kinds.Leaf

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Tammes15.PaperSteps
open scoped Classical

def firstGo (p : ℕ → Bool) : ℕ → ℕ → ℕ
  | j, 0 => j
  | j, fuel + 1 => if p j then j else firstGo p (j + 1) fuel

def firstLt (p : ℕ → Bool) (n : ℕ) : ℕ := firstGo p 0 n

theorem firstGo_spec (p : ℕ → Bool) : ∀ (fuel j : ℕ),
    j ≤ firstGo p j fuel ∧ firstGo p j fuel ≤ j + fuel ∧
      (∀ i, j ≤ i → i < firstGo p j fuel → p i = false) ∧
      (firstGo p j fuel < j + fuel → p (firstGo p j fuel) = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j
    simp only [firstGo]
    exact ⟨le_refl _, by omega, fun i h1 h2 => by omega, fun h => by omega⟩
  | succ fuel ih =>
    intro j
    by_cases hp : p j = true
    · have e : firstGo p j (fuel + 1) = j := by simp [firstGo, hp]
      rw [e]
      exact ⟨le_refl _, by omega, fun i h1 h2 => by omega, fun _ => hp⟩
    · have hp' : p j = false := by simpa using hp
      obtain ⟨h1, h2, h3, h4⟩ := ih (j + 1)
      have e : firstGo p j (fuel + 1) = firstGo p (j + 1) fuel := by simp [firstGo, hp']
      rw [e]
      refine ⟨by omega, by omega, fun i hi1 hi2 => ?_, fun h => h4 (by omega)⟩
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hi1
      · exact hp'
      · exact h3 i hi1 hi2

theorem firstLt_eq {p : ℕ → Bool} {n j : ℕ} (hj : j < n) (hp : p j = true) (hmin : ∀ i < j, p i = false) :
    firstLt p n = j := by
  obtain ⟨-, h2, h3, h4⟩ := firstGo_spec p n 0
  unfold firstLt
  rcases lt_trichotomy (firstGo p 0 n) j with h | h | h
  · have := h4 (by omega)
    rw [hmin _ h] at this
    exact absurd this (by simp)
  · exact h
  · have := h3 j (Nat.zero_le _) h
    rw [hp] at this
    exact absurd this (by simp)

theorem firstLt_none {p : ℕ → Bool} {n : ℕ} (h : ∀ i < n, p i = false) : firstLt p n = n := by
  obtain ⟨-, h2, -, h4⟩ := firstGo_spec p n 0
  unfold firstLt
  by_contra hne
  have := h4 (by omega)
  rw [h _ (by omega)] at this
  exact absurd this (by simp)

def revC (c : GCode) (i : ℕ) : ℕ :=
  firstLt (fun j => c.fstAt j == c.fstAt (c.faceAt i) && c.fstAt (c.faceAt j) == c.fstAt i) c.D

def rsymC (c : GCode) (i : ℕ) : ℕ := c.faceAt (revC c i)

def stepsC (c : GCode) (i j : ℕ) : ℕ :=
  if firstLt (fun s => (rsymC c)^[s] i == j) c.D < c.D then firstLt (fun s => (rsymC c)^[s] i == j) c.D else 0

def degC (c : GCode) (i : ℕ) : ℕ := firstLt (fun s => (rsymC c)^[s + 1] i == i) c.D + 1

section Graph

variable {P : PlaneGraph} {c : GCode} {lab : P.G.Dart ≃ Fin c.D}

theorem face_fst' (P : PlaneGraph) (e : P.G.Dart) : (P.R.face e).fst = e.snd := by
  have h := P.R.rot_fst (P.R.rot.symm e.symm)
  rw [Equiv.apply_symm_apply] at h
  show (P.R.rot.symm e.symm).fst = e.snd
  rw [← h]
  rfl

theorem rot_symm_eq_face (P : PlaneGraph) (a : P.G.Dart) : P.R.rot.symm a = P.R.face a.symm := by
  show P.R.rot.symm a = P.R.rot.symm a.symm.symm
  rw [SimpleGraph.Dart.symm_symm]

theorem card_dart (lab : P.G.Dart ≃ Fin c.D) : Fintype.card P.G.Dart = c.D := by
  rw [Fintype.card_congr lab, Fintype.card_fin]

theorem revC_lab (hm : Matches P c lab) (a : P.G.Dart) : revC c (lab a) = lab a.symm := by
  have huniq : ∀ e : P.G.Dart, (c.fstAt (lab e) == c.fstAt (c.faceAt (lab a)) &&
      c.fstAt (c.faceAt (lab e)) == c.fstAt (lab a)) = true → e = a.symm := by
    intro e he
    simp only [Bool.and_eq_true, beq_iff_eq, hm.face, hm.fst, face_fst'] at he
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact Fin.ext he.1
    · exact Fin.ext he.2
  have hp : (c.fstAt (lab a.symm) == c.fstAt (c.faceAt (lab a)) &&
      c.fstAt (c.faceAt (lab a.symm)) == c.fstAt (lab a)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, hm.face, hm.fst, face_fst']
    exact ⟨rfl, rfl⟩
  unfold revC
  apply firstLt_eq (lab a.symm).isLt hp
  intro i hi
  by_contra hne
  have hpi : (c.fstAt i == c.fstAt (c.faceAt (lab a)) && c.fstAt (c.faceAt i) == c.fstAt (lab a)) = true := by
    simpa using hne
  have hiD : i < c.D := lt_trans hi (lab a.symm).isLt
  have hq := huniq (lab.symm ⟨i, hiD⟩) (by rw [Equiv.apply_symm_apply]; exact hpi)
  have h2 : ((lab (lab.symm ⟨i, hiD⟩) : Fin c.D) : ℕ) = lab a.symm := by rw [hq]
  rw [Equiv.apply_symm_apply] at h2
  simp only at h2
  omega

theorem rsymC_lab (hm : Matches P c lab) (a : P.G.Dart) : rsymC c (lab a) = lab (P.R.rot.symm a) := by
  rw [rsymC, revC_lab hm, hm.face, rot_symm_eq_face]

theorem rsymC_iter (hm : Matches P c lab) (a : P.G.Dart) (s : ℕ) :
    (rsymC c)^[s] (lab a) = lab ((P.R.rot.symm ^ s) a) := by
  induction s with
  | zero => rfl
  | succ s ih => rw [Function.iterate_succ_apply', ih, rsymC_lab hm, pow_succ', Equiv.Perm.mul_apply]

theorem rsymC_iter_eq_iff (hm : Matches P c lab) (a b : P.G.Dart) (s : ℕ) :
    ((rsymC c)^[s] (lab a) == (lab b : ℕ)) = true ↔ (P.R.rot.symm ^ s) a = b := by
  rw [beq_iff_eq, rsymC_iter hm]
  constructor
  · intro h
    exact lab.injective (Fin.ext h)
  · intro h
    rw [h]

theorem exists_lt_card (lab : P.G.Dart ≃ Fin c.D) (f : Equiv.Perm P.G.Dart) (a b : P.G.Dart) (s : ℕ)
    (h : (f ^ s) a = b) : ∃ s' < c.D, (f ^ s') a = b := by
  have hper : a ∈ Function.periodicPts f := Function.Injective.mem_periodicPts f.injective a
  have hpos : 0 < Function.minimalPeriod f a := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hle : Function.minimalPeriod f a ≤ c.D := by
    rw [← card_dart lab]
    exact Function.minimalPeriod_le_card
  refine ⟨s % Function.minimalPeriod f a, lt_of_lt_of_le (Nat.mod_lt _ hpos) hle, ?_⟩
  rw [Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq, ← Equiv.Perm.coe_pow, h]

theorem stepsC_eq (hm : Matches P c lab) (a b : P.G.Dart) :
    turnStepsR P.R a b = stepsC c (lab a) (lab b) := by
  classical
  unfold turnStepsR stepsC
  by_cases h : ∃ s, (P.R.rot.symm ^ s) a = b
  · rw [dite_eq_left h]
    obtain ⟨s', hs'D, hs'⟩ := exists_lt_card lab _ a b (Nat.find h) (Nat.find_spec h)
    have hfind : Nat.find h < c.D := lt_of_le_of_lt (Nat.find_min' h hs') hs'D
    have hfl : firstLt (fun t => (rsymC c)^[t] (lab a : ℕ) == (lab b : ℕ)) c.D = Nat.find h := by
      apply firstLt_eq hfind
      · exact (rsymC_iter_eq_iff hm a b _).2 (Nat.find_spec h)
      · intro i hi
        by_contra hne
        have hi' : ((rsymC c)^[i] (lab a : ℕ) == (lab b : ℕ)) = true := by simpa using hne
        exact Nat.find_min h hi ((rsymC_iter_eq_iff hm a b i).1 hi')
    rw [hfl, ite_eq_left hfind]
  · rw [dite_eq_right h]
    have hfl : firstLt (fun t => (rsymC c)^[t] (lab a : ℕ) == (lab b : ℕ)) c.D = c.D := by
      apply firstLt_none
      intro i _
      by_contra hne
      have hi' : ((rsymC c)^[i] (lab a : ℕ) == (lab b : ℕ)) = true := by simpa using hne
      exact h ⟨i, (rsymC_iter_eq_iff hm a b i).1 hi'⟩
    rw [hfl, ite_eq_right (lt_irrefl _)]

theorem degC_eq (hm : Matches P c lab) (a : P.G.Dart) : rotDeg a = degC c (lab a) := by
  classical
  set f := P.R.rot.symm
  have hper : a ∈ Function.periodicPts f := Function.Injective.mem_periodicPts f.injective a
  have hpos : 0 < Function.minimalPeriod f a := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hle : Function.minimalPeriod f a ≤ c.D := by
    rw [← card_dart lab]
    exact Function.minimalPeriod_le_card
  have hiter : ∀ t, (f ^ t) a = (⇑f)^[t] a := fun t => by rw [Equiv.Perm.coe_pow]
  have hfl : firstLt (fun s => (rsymC c)^[s + 1] (lab a : ℕ) == (lab a : ℕ)) c.D =
      Function.minimalPeriod f a - 1 := by
    apply firstLt_eq (by omega)
    · rw [rsymC_iter_eq_iff hm a a, hiter, Nat.sub_add_cancel hpos]
      exact Function.iterate_minimalPeriod
    · intro i hi
      by_contra hne
      have hi' : ((rsymC c)^[i + 1] (lab a : ℕ) == (lab a : ℕ)) = true := by simpa using hne
      rw [rsymC_iter_eq_iff hm a a, hiter] at hi'
      exact absurd (Function.IsPeriodicPt.minimalPeriod_le (Nat.succ_pos i) hi') (by omega)
  show Function.minimalPeriod f a = degC c (lab a)
  unfold degC
  rw [hfl]
  omega

end Graph

end Tammes15.D3Kernel.Kinds
