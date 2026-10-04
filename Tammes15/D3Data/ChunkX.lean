import Tammes15.D3Data.QX
import Tammes15.D3Kernel.Kinds.CoverK

namespace Tammes15.D3Data

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Tammes15.D3Kernel.Kinds Tammes15.D3Kernel.Pent
  Tammes15.D3Kernel.Walk

def rootsAt (R : List ℕ) (i n : ℕ) : List ℕ := (R.drop (2 * i)).take (2 * n)

theorem rootPairs_drop (R : List ℕ) (i : ℕ) : rootPairs (R.drop (2 * i)) = (rootPairs R).drop i := by
  induction i generalizing R with
  | zero =>
      simp
  | succ i ih =>
      cases R with
      | nil =>
        have hpos : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
        simp [rootPairs, hpos]
      | cons g rs =>
        cases rs with
        | nil =>
          have hpos : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
          simp [rootPairs, hpos]
        | cons b rs' =>
          have hpos : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
          have hdrop : (g :: b :: rs').drop (2 * (i + 1)) = rs'.drop (2 * i) := by
            rw [hpos]
            simp [List.drop_succ_cons]
          calc
            rootPairs ((g :: b :: rs').drop (2 * (i + 1))) = rootPairs (rs'.drop (2 * i)) := by rw [hdrop]
            _ = (rootPairs rs').drop i := ih rs'
            _ = ((g, b) :: rootPairs rs').drop (i + 1) := by simp
            _ = (rootPairs (g :: b :: rs')).drop (i + 1) := by simp [rootPairs]

theorem rootPairs_take (R : List ℕ) (n : ℕ) : rootPairs (R.take (2 * n)) = (rootPairs R).take n := by
  induction n generalizing R with
  | zero =>
      simp [rootPairs]
  | succ n ih =>
      cases R with
      | nil => simp [rootPairs]
      | cons g tail =>
          cases tail with
          | nil =>
              have hpos : 2 * (n + 1) = (2 * n) + 2 := by omega
              simp [rootPairs, List.take_succ_cons, hpos]
          | cons b rs =>
              have h : 2 * (n + 1) = (2 * n) + 2 := by omega
              simp [rootPairs, List.take_succ_cons, h, ih]

theorem rootPairs_rootsAt (R : List ℕ) (i n : ℕ) : rootPairs (rootsAt R i n) = ((rootPairs R).drop i).take n := by
  unfold rootsAt
  rw [rootPairs_take, rootPairs_drop]

theorem mem_rootPairs_rootsAt {R : List ℕ} {i n : ℕ} {p : ℕ × ℕ} (h : p ∈ rootPairs (rootsAt R i n)) :
    p ∈ rootPairs R := by
  rw [rootPairs_rootsAt] at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

def coverAt (i n : ℕ) (c : GCode) (R : List ℕ) : Bool := cover c (rootsAt R i n)

theorem coverAt_sound (i n : ℕ) : CoverSound (coverAt i n) := by
  intro c R hc hR
  exact cover_sound c (rootsAt R i n) hc fun p hp => hR p (mem_rootPairs_rootsAt hp)

theorem cover_of_coverK {c : GCode} {R : List ℕ} (h : coverK c R = true) : cover c R = true := by
  rw [← coverK_eq]
  exact h

theorem killedCode_of_QX_at {R s t : List ℕ} (h : Reach QX R s t) (ht : Done t) {c : GCode} {i n : ℕ}
    (hc : cover c (rootsAt R i n) = true) : KilledCode c :=
  killedCode_of_kinds progsZ progsZ_ok QXs QXs_sound (coverAt_sound i n) h ht hc

def ChunkQX (job : List (List ℕ)) : Prop :=
  ∀ l ∈ job, ∀ c ∈ codesOfLits l, ∃ (R s t : List ℕ) (i n : ℕ),
    Reach QX R s t ∧ Done t ∧ cover c (rootsAt R i n) = true

theorem jobFact_of_chunkQX {job : List (List ℕ)} (h : ChunkQX job) : JobFact job := by
  intro l hl c hc
  obtain ⟨R, s, t, i, n, hr, hd, hcov⟩ := h l hl c hc
  exact killedCode_of_QX_at hr hd hcov

theorem chunkQX_nil : ChunkQX [] := by
  intro l hl
  simp at hl

theorem chunkQX_cons {l : List ℕ} {job : List (List ℕ)}
    (hl : ∀ c ∈ codesOfLits l, ∃ (R s t : List ℕ) (i n : ℕ),
      Reach QX R s t ∧ Done t ∧ cover c (rootsAt R i n) = true)
    (h : ChunkQX job) : ChunkQX (l :: job) := by
  intro l' hl' c hc
  rcases List.mem_cons.1 hl' with rfl | hl'
  · exact hl c hc
  · exact h l' hl' c hc

theorem chunkQX_append {a b : List (List ℕ)} (ha : ChunkQX a) (hb : ChunkQX b) : ChunkQX (a ++ b) := by
  intro l hl c hc
  rcases List.mem_append.1 hl with hl | hl
  · exact ha l hl c hc
  · exact hb l hl c hc

theorem chunkQX_lits_cons {D f s : ℕ} {t : List ℕ} (h1 : ChunkQX [[D, f, s]]) (h2 : ChunkQX [t]) :
    ChunkQX [D :: f :: s :: t] := by
  intro l hl c hc
  rw [List.mem_singleton] at hl
  subst hl
  simp only [codesOfLits, List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact h1 [D, f, s] (List.mem_singleton_self _) ⟨D, f, s⟩ (by simp [codesOfLits])
  · exact h2 t (List.mem_singleton_self _) c hc

theorem chunkQX_lits_nil : ChunkQX [[]] := by
  intro l hl c hc
  rw [List.mem_singleton] at hl
  subst hl
  simp [codesOfLits] at hc

def ChunkG (Q : Checker) (job : List (List ℕ)) : Prop :=
  ∀ l ∈ job, ∀ c ∈ codesOfLits l, ∃ (R s t : List ℕ) (i n : ℕ),
    Reach Q R s t ∧ Done t ∧ cover c (rootsAt R i n) = true

theorem chunkQX_eq_chunkG : ChunkQX = ChunkG QX := rfl

theorem jobFact_of_chunkG {Q : Checker} (hQ : Q.Sound fun _ => True) {job : List (List ℕ)} (h : ChunkG Q job) :
    JobFact job := by
  intro l hl c hc
  obtain ⟨R, s, t, i, n, hr, hd, hcov⟩ := h l hl c hc
  exact killedCode_of_walk hQ (coverAt_sound i n) hr hd hcov

theorem chunkG_nil (Q : Checker) : ChunkG Q [] := by
  intro l hl
  simp at hl

theorem chunkG_cons {Q : Checker} {l : List ℕ} {job : List (List ℕ)}
    (hl : ∀ c ∈ codesOfLits l, ∃ (R s t : List ℕ) (i n : ℕ),
      Reach Q R s t ∧ Done t ∧ cover c (rootsAt R i n) = true)
    (h : ChunkG Q job) : ChunkG Q (l :: job) := by
  intro l' hl' c hc
  rcases List.mem_cons.1 hl' with rfl | hl'
  · exact hl c hc
  · exact h l' hl' c hc

theorem chunkG_append {Q : Checker} {a b : List (List ℕ)} (ha : ChunkG Q a) (hb : ChunkG Q b) :
    ChunkG Q (a ++ b) := by
  intro l hl c hc
  rcases List.mem_append.1 hl with hl | hl
  · exact ha l hl c hc
  · exact hb l hl c hc

theorem chunkG_lits_cons {Q : Checker} {D f s : ℕ} {t : List ℕ} (h1 : ChunkG Q [[D, f, s]])
    (h2 : ChunkG Q [t]) : ChunkG Q [D :: f :: s :: t] := by
  intro l hl c hc
  rw [List.mem_singleton] at hl
  subst hl
  simp only [codesOfLits, List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact h1 [D, f, s] (List.mem_singleton_self _) ⟨D, f, s⟩ (by simp [codesOfLits])
  · exact h2 t (List.mem_singleton_self _) c hc

theorem chunkG_lits_nil (Q : Checker) : ChunkG Q [[]] := by
  intro l hl c hc
  rw [List.mem_singleton] at hl
  subst hl
  simp [codesOfLits] at hc

theorem forall_codes_eq {P : GCode → Prop} {l : List ℕ} {c : GCode} (he : codesOfLits l = [c]) (hc : P c) :
    ∀ c' ∈ codesOfLits l, P c' := by
  intro c' hc'
  rw [he] at hc'
  have h_eq : c' = c := (List.mem_singleton.mp hc')
  rw [h_eq]
  exact hc

theorem jobFact_nil : JobFact [] := by
  intro l hl
  exfalso
  exact (List.not_mem_nil (a := l)) hl

theorem jobFact_cons {l : List ℕ} {job : List (List ℕ)} (hl : ∀ c ∈ codesOfLits l, KilledCode c)
    (h : JobFact job) : JobFact (l :: job) := by
  unfold JobFact
  intro l' hl'
  rcases ((List.mem_cons (a := l') (b := l) (l := job)).mp hl') with (hl' | hl')
  · subst hl'
    exact hl
  · exact h l' hl'

end Tammes15.D3Data
