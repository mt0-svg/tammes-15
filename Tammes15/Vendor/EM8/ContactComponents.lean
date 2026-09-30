-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/ContactComponents.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8, hand changes marked below, `Fin 8` generalized to `Fin nPts` (auto-bound); see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.ContactSeparation

open Real
noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def ContactAdj (Y : Fin nPts → ℝ³) (c : ℝ) (i j : Fin nPts) : Prop :=
  i ≠ j ∧ inner ℝ (Y i) (Y j) = c

lemma ContactAdj.symm {Y : Fin nPts → ℝ³} {c : ℝ} {i j : Fin nPts} (h : ContactAdj Y c i j) :
    ContactAdj Y c j i := ⟨h.1.symm, (real_inner_comm (Y i) (Y j)).trans h.2⟩

abbrev ContactReachable (Y : Fin nPts → ℝ³) (c : ℝ) := Relation.ReflTransGen (ContactAdj Y c)

lemma contactReachable_symm {Y : Fin nPts → ℝ³} {c : ℝ} {i j : Fin nPts}
    (h : ContactReachable Y c i j) : ContactReachable Y c j i := by
  induction h with
  | refl => exact .refl
  | tail hpath hstep ih => exact (Relation.ReflTransGen.single hstep.symm).trans ih

def contactComponent (Y : Fin nPts → ℝ³) (c : ℝ) (i : Fin nPts) : Finset (Fin nPts) := by
  classical
  exact Finset.univ.filter (ContactReachable Y c i)

@[simp] lemma mem_contactComponent (Y : Fin nPts → ℝ³) (c : ℝ) (i j : Fin nPts) :
    j ∈ contactComponent Y c i ↔ ContactReachable Y c i j := by
  classical
  simp [contactComponent]

lemma contactComponent_root (Y : Fin nPts → ℝ³) (c : ℝ) (i : Fin nPts) : i ∈ contactComponent Y c i :=
  (mem_contactComponent Y c i i).mpr .refl

lemma contactComponent_closed (Y : Fin nPts → ℝ³) (c : ℝ) (root i j : Fin nPts)
    (hi : i ∈ contactComponent Y c root) (hij : ContactAdj Y c i j) : j ∈ contactComponent Y c root :=
  (mem_contactComponent Y c root j).mpr (((mem_contactComponent Y c root i).mp hi).tail hij)

lemma reachable_nonisolated {Y : Fin nPts → ℝ³} {c : ℝ} {i j : Fin nPts}
    (h : ContactReachable Y c i j) (hi : ∃ k, ContactAdj Y c i k) : ∃ k, ContactAdj Y c j k := by
  induction h with
  | refl => exact hi
  | tail hpath hstep ih => exact ⟨_, hstep.symm⟩

lemma irreducible_degree_in_closed_set (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (V : Finset (Fin nPts)) (i : Fin nPts) (hneigh : ∃ j, ContactAdj Y c i j)
    (hclosed : ∀ j, ContactAdj Y c i j → j ∈ V) :
    3 ≤ (contactNeighborsWithin Y c V i).card := by
  obtain ⟨n, hn⟩ := hneigh
  obtain ⟨j, k, l, hji, hki, hli, hjk, hjl, hkl, hij, hik, hil⟩ :=
    irreducible_three_neighbors Y c hY hc hirr i ⟨n, hn.1.symm, hn.2⟩
  have hj : j ∈ contactNeighborsWithin Y c V i := (mem_contactNeighborsWithin Y c V i j).mpr
    ⟨hclosed j ⟨hji.symm, hij⟩, hji, hij⟩
  have hk : k ∈ contactNeighborsWithin Y c V i := (mem_contactNeighborsWithin Y c V i k).mpr
    ⟨hclosed k ⟨hki.symm, hik⟩, hki, hik⟩
  have hl : l ∈ contactNeighborsWithin Y c V i := (mem_contactNeighborsWithin Y c V i l).mpr
    ⟨hclosed l ⟨hli.symm, hil⟩, hli, hil⟩
  have hsub : ({j, k, l} : Finset (Fin nPts)) ⊆ contactNeighborsWithin Y c V i := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hj
    · exact hk
    · exact hl
  have hc3 : ({j, k, l} : Finset (Fin nPts)).card = 3 := by simp [hjk, hjl, hkl]
  rw [← hc3]
  exact Finset.card_le_card hsub

theorem irreducible_component_size (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 < c) (hcupper : c ≤ aInf)
    (hirr : PackingIrreducible c Y) (i : Fin nPts) (hneigh : ∃ j, ContactAdj Y c i j) :
    5 ≤ (contactComponent Y c i).card := by
  apply three_neighbor_component_size Y c hY hc.le (hcupper.trans_lt aInf_lt_one_third)
    (contactComponent Y c i) ⟨i, contactComponent_root Y c i⟩
  intro j hj
  apply irreducible_degree_in_closed_set Y c hY ⟨hc, hcupper.trans_lt aInf_mem_Ioo.2⟩ hirr _ j
    (reachable_nonisolated ((mem_contactComponent Y c i j).mp hj) hneigh)
  intro k hcontact
  exact contactComponent_closed Y c i j k hj hcontact

lemma contactComponent_eq_of_reachable (Y : Fin nPts → ℝ³) (c : ℝ) (i j : Fin nPts)
    (hij : ContactReachable Y c i j) : contactComponent Y c i = contactComponent Y c j := by
  ext k
  simp only [mem_contactComponent]
  exact ⟨fun hik => (contactReachable_symm hij).trans hik, fun hjk => hij.trans hjk⟩

theorem unique_nontrivial_contact_component (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 < c) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
    (i j : Fin 8) (hi : ∃ k, ContactAdj Y c i k) (hj : ∃ k, ContactAdj Y c j k) :
    contactComponent Y c i = contactComponent Y c j := by
  have hci := irreducible_component_size Y c hY hc hcupper hirr i hi
  have hcj := irreducible_component_size Y c hY hc hcupper hirr j hj
  have hinter : ((contactComponent Y c i) ∩ (contactComponent Y c j)).Nonempty := by
    by_contra h
    have hdis : Disjoint (contactComponent Y c i) (contactComponent Y c j) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    have hcard := Finset.card_le_univ ((contactComponent Y c i) ∪ (contactComponent Y c j))
    rw [Finset.card_union_of_disjoint hdis] at hcard
    norm_num at hcard
    omega
  obtain ⟨k, hk⟩ := hinter
  obtain ⟨hik, hjk⟩ := Finset.mem_inter.mp hk
  apply contactComponent_eq_of_reachable
  exact ((mem_contactComponent Y c i k).mp hik).trans
    (contactReachable_symm ((mem_contactComponent Y c j k).mp hjk))

abbrev ContactReachableWithout (Y : Fin nPts → ℝ³) (c : ℝ) (v : Fin nPts) :=
  Relation.ReflTransGen (fun i j => ContactAdj Y c i j ∧ i ≠ v ∧ j ≠ v)

/-- Deleting any one vertex leaves the remaining vertices of a nontrivial
irreducible contact component connected. The proof is the paper's finite
cut-partition argument, without a block-cut-tree assumption. -/
theorem irreducible_component_two_connected (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 < c) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
    (root : Fin 8) (hroot : ∃ k, ContactAdj Y c root k) (v i j : Fin 8)
    (hi : i ∈ contactComponent Y c root) (hj : j ∈ contactComponent Y c root)
    (hiv : i ≠ v) (hjv : j ≠ v) : ContactReachableWithout Y c v i j := by
  classical
  by_contra hnot
  let A : Finset (Fin 8) := Finset.univ.filter (fun x =>
    x ∈ contactComponent Y c root ∧ x ≠ v ∧ ContactReachableWithout Y c v i x)
  let B : Finset (Fin 8) := Finset.univ.filter (fun x =>
    x ∈ contactComponent Y c root ∧ x ≠ v ∧ ¬ ContactReachableWithout Y c v i x)
  have hA : A.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hiv, .refl⟩⟩
  have hB : B.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hjv, hnot⟩⟩
  have hvA : v ∉ A := by simp [A]
  have hvB : v ∉ B := by simp [B]
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    have ha : x ∈ contactComponent Y c root ∧ x ≠ v ∧ ContactReachableWithout Y c v i x := by simpa [A] using hxA
    have hb : x ∈ contactComponent Y c root ∧ x ≠ v ∧ ¬ ContactReachableWithout Y c v i x := by simpa [B] using hxB
    exact hb.2.2 ha.2.2
  apply contact_cut_partition_impossible Y c hY hc.le (hcupper.trans_lt aInf_lt_one_third)
    A B v hA hB hdis hvA hvB
  · intro x hx
    have hxA : x ∈ contactComponent Y c root ∧ x ≠ v ∧ ContactReachableWithout Y c v i x := by simpa [A] using hx
    apply irreducible_degree_in_closed_set Y c hY ⟨hc, hcupper.trans_lt aInf_mem_Ioo.2⟩ hirr (insert v A) x
      (reachable_nonisolated ((mem_contactComponent Y c root x).mp hxA.1) hroot)
    intro y hxy
    by_cases hyv : y = v
    · exact Finset.mem_insert.mpr (Or.inl hyv)
    · apply Finset.mem_insert_of_mem
      have hyC := contactComponent_closed Y c root x y hxA.1 hxy
      have hyReach : ContactReachableWithout Y c v i y := hxA.2.2.tail ⟨hxy, hxA.2.1, hyv⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyC, hyv, hyReach⟩
  · intro x hx
    have hxB : x ∈ contactComponent Y c root ∧ x ≠ v ∧ ¬ ContactReachableWithout Y c v i x := by simpa [B] using hx
    apply irreducible_degree_in_closed_set Y c hY ⟨hc, hcupper.trans_lt aInf_mem_Ioo.2⟩ hirr (insert v B) x
      (reachable_nonisolated ((mem_contactComponent Y c root x).mp hxB.1) hroot)
    intro y hxy
    by_cases hyv : y = v
    · exact Finset.mem_insert.mpr (Or.inl hyv)
    · apply Finset.mem_insert_of_mem
      have hyC := contactComponent_closed Y c root x y hxB.1 hxy
      have hyNot : ¬ ContactReachableWithout Y c v i y := by
        intro hyReach
        exact hxB.2.2 (hyReach.tail ⟨hxy.symm, hyv, hxB.2.1⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyC, hyv, hyNot⟩
-- tammes-15 port change: ContactTwoConnected, the hypothesis the face chain takes instead of c ≤ aInf, and its proof for eight points.

/-- The conclusion of `irreducible_component_two_connected` as a property of `Y` and `c`: deleting
any one vertex leaves every nontrivial contact component connected. The face chain below uses
only this of the bound `c ≤ aInf`, so that it holds for every number of points. -/
def ContactTwoConnected (Y : Fin nPts → ℝ³) (c : ℝ) : Prop :=
  ∀ root : Fin nPts, (∃ k, ContactAdj Y c root k) → ∀ v i j : Fin nPts,
    i ∈ contactComponent Y c root → j ∈ contactComponent Y c root → i ≠ v → j ≠ v →
    ContactReachableWithout Y c v i j

theorem contactTwoConnected_of_aInf (Y : Fin 8 → ℝ³) (c : ℝ) (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 < c)
    (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y) : ContactTwoConnected Y c :=
  fun root hroot v i j hi hj hiv hjv =>
    irreducible_component_two_connected Y c hY hc hcupper hirr root hroot v i j hi hj hiv hjv

end Tammes15.Vendor.EM8.SquareAntiprismVerification
