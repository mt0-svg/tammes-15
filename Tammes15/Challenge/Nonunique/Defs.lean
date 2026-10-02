import Mathlib

/-!
# Contact graphs and the two lists of contacts

`contactGraph X c`: on the indices of the points `X i`, `i ~ j` when `i ≠ j` and `⟪X i, X j⟫ = c`.
For unit vectors and `c = cos d` this is the contact graph at angular distance `d`.

`S1`, `S3`: the 30 contacts of the frames C1 and C3 (`Tammes15.Attained.frameC1.S`,
`frameC3.S`, copied; equal by `rfl` in `Tammes15.Nonunique.Corollary`), and `listGraph S` the
graph with these edges. `Deg5Clique G`: any two distinct vertices of degree 5 are adjacent. It holds
for C3 (degree-5 vertices 0, 1, 2, pairwise adjacent) and fails for C1 (degree-5 vertices 0, 1, 14;
0 and 14 are not adjacent), and it is invariant under isomorphism, so the two graphs are not
isomorphic (paper, proof of Corollary 1.2; code/gp/contact_graphs.gp).
-/

open scoped RealInnerProductSpace

namespace Tammes15.Nonunique

/-- Euclidean 3-space (as `Tammes15.E3`). -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The contact graph of `X` at inner product `c`. -/
def contactGraph {N : ℕ} (X : Fin N → E3) (c : ℝ) : SimpleGraph (Fin N) where
  Adj i j := i ≠ j ∧ ⟪X i, X j⟫ = c
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [real_inner_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The graph on `Fin 15` whose edges are the pairs of `S`, either way round. -/
def listGraph (S : Finset (Fin 15 × Fin 15)) : SimpleGraph (Fin 15) :=
  SimpleGraph.fromRel fun i j => (i, j) ∈ S

instance (S : Finset (Fin 15 × Fin 15)) : DecidableRel (listGraph S).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ((i, j) ∈ S ∨ (j, i) ∈ S)))

/-- The contacts of C1. -/
def S1 : Finset (Fin 15 × Fin 15) := {(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 7), (2, 4), (2, 5), (3, 7), (3, 9), (4, 8), (4, 11), (5, 6), (5, 10), (6, 9), (7, 11), (8, 10), (8, 14), (9, 12), (9, 13), (10, 13), (10, 14), (11, 12), (11, 14), (12, 13), (12, 14), (13, 14)}

/-- The contacts of C3. -/
def S3 : Finset (Fin 15 × Fin 15) := {(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 7), (2, 4), (2, 5), (2, 8), (3, 7), (3, 9), (4, 8), (4, 11), (5, 6), (5, 10), (6, 9), (7, 11), (8, 10), (9, 12), (9, 13), (10, 13), (10, 14), (11, 12), (11, 14), (12, 13), (12, 14), (13, 14)}

/-- Any two distinct vertices of degree 5 are adjacent. -/
def Deg5Clique (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj] : Prop :=
  ∀ v w, v ≠ w → G.degree v = 5 → G.degree w = 5 → G.Adj v w

/-- `contactGraph X c` is `listGraph S` when the pairs of `S` are increasing and at inner product
`c`, and every other increasing pair is below `c`. -/
theorem contactGraph_eq_listGraph (X : Fin 15 → E3) (c : ℝ) (S : Finset (Fin 15 × Fin 15))
    (hlt : ∀ ij ∈ S, ij.1 < ij.2) (hS : ∀ ij ∈ S, ⟪X ij.1, X ij.2⟫ = c)
    (hsep : ∀ i j, i < j → (i, j) ∉ S → ⟪X i, X j⟫ < c) :
    contactGraph X c = listGraph S := by
  ext i j
  constructor
  · intro h
    rcases h with ⟨hne, heq⟩
    have hlt_or := lt_or_gt_of_ne hne
    rcases hlt_or with (hlt_ij | hlt_ji)
    · by_cases hmem : (i, j) ∈ S
      · exact ⟨hne, Or.inl hmem⟩
      · exfalso
        have hlt' := hsep i j hlt_ij hmem
        linarith
    · by_cases hmem : (j, i) ∈ S
      · exact ⟨hne, Or.inr hmem⟩
      · exfalso
        have hlt' := hsep j i hlt_ji hmem
        rw [real_inner_comm (X j) (X i)] at heq
        linarith
  · intro h
    rcases h with ⟨hne, hmem⟩
    rcases hmem with (hmem | hmem)
    · have hlt' := hlt (i, j) hmem
      have hne' : i ≠ j := by
        intro heq
        rw [heq] at hlt'
        exact lt_irrefl _ hlt'
      have heq' := hS (i, j) hmem
      exact ⟨hne', heq'⟩
    · have hlt' := hlt (j, i) hmem
      have hne' : i ≠ j := by
        intro heq
        rw [heq] at hlt'
        exact lt_irrefl _ hlt'
      have heq' := hS (j, i) hmem
      have heq'' : ⟪X i, X j⟫ = c := by
        calc
          ⟪X i, X j⟫ = ⟪X j, X i⟫ := by rw [real_inner_comm]
          _ = c := by simpa using heq'
      exact ⟨hne', heq''⟩

/-- The pairs of `S1` are increasing. -/
theorem S1_lt : ∀ ij ∈ S1, ij.1 < ij.2 := by
  set_option maxRecDepth 1000000 in
  decide

/-- The pairs of `S3` are increasing. -/
theorem S3_lt : ∀ ij ∈ S3, ij.1 < ij.2 := by
  set_option maxRecDepth 1000000 in
  decide

/-- `Deg5Clique` is invariant under isomorphism. -/
theorem deg5Clique_of_iso {G G' : SimpleGraph (Fin 15)} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : G ≃g G') (h : Deg5Clique G') : Deg5Clique G := by
  intro v w h_ne h_deg_v h_deg_w
  have h_deg_v' : G'.degree (φ v) = 5 := by
    rw [SimpleGraph.Iso.degree_eq φ v, h_deg_v]
  have h_deg_w' : G'.degree (φ w) = 5 := by
    rw [SimpleGraph.Iso.degree_eq φ w, h_deg_w]
  have h_ne' : φ v ≠ φ w := by
    intro h_eq
    apply h_ne
    exact φ.injective h_eq
  have h_adj' : G'.Adj (φ v) (φ w) := h (φ v) (φ w) h_ne' h_deg_v' h_deg_w'
  rwa [SimpleGraph.Iso.map_adj_iff φ] at h_adj'

/-- The degree-5 vertices of C3 are pairwise adjacent. -/
theorem deg5Clique_S3 : Deg5Clique (listGraph S3) := by
  unfold Deg5Clique; decide

/-- Two degree-5 vertices of C1 (0 and 14) are not adjacent. -/
theorem not_deg5Clique_S1 : ¬ Deg5Clique (listGraph S1) := by
  intro h
  have h0 : (listGraph S1).degree 0 = 5 := by decide
  have h14 : (listGraph S1).degree 14 = 5 := by decide
  have h014 : ¬ (listGraph S1).Adj 0 14 := by decide
  exact absurd (h 0 14 (by decide) h0 h14) h014

/-- The contact graphs of C1 and C3 are not isomorphic. -/
theorem listGraph_S1_not_iso : IsEmpty (listGraph S1 ≃g listGraph S3) := by
  exact ⟨fun φ => not_deg5Clique_S1 (deg5Clique_of_iso φ deg5Clique_S3)⟩

/-- Isomorphic graphs stay isomorphic after rewriting both sides. -/
theorem isEmpty_iso_congr {G G' H H' : SimpleGraph (Fin 15)} (hG : G = G') (hH : H = H')
    (h : IsEmpty (G' ≃g H')) : IsEmpty (G ≃g H) := by
  subst hG; subst hH; exact h

end Tammes15.Nonunique
