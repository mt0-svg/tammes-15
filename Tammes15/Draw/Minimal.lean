import Tammes15.Draw.Shift

/-!
# Lemma 4.2

For a configuration `X` at separation `d < π/2` with fewest contacts, and the graph `G` of its
non-rattlers with an angular rotation system: every corner lies in `[α(d), π)` and every vertex
has degree 3, 4 or 5. A corner `≥ π`, or a vertex of degree one, would give a push direction
(`exists_push_dir`) and a configuration with fewer contacts (`shift_config`,
`contactCount_lt_of_shift`); the lower bound is Lemma A.1 (`alpha_le_angle`,
`angle_le_ocorner`); the degree bounds come from the angle sum `corner_sum`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Lemma A.1 for the corner after a dart that the rotation moves. -/
theorem alpha_le_corner {N : ℕ} {d : ℝ} (hd : 0 < d ∧ d < π / 2) (X : Config N d)
    (emb : V ↪ Fin N) (hG : ∀ a b, G.Adj a b → (contactGraph X).Adj (emb a) (emb b))
    (R : RotSys G) (e : G.Dart) (hne : R.rot e ≠ e) :
    alpha d ≤ ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) := by
  have hdpi : 0 < d ∧ d < π := ⟨hd.1, by linarith [Real.pi_pos, hd.2]⟩
  have hD := distinctDirs_contact hdpi X emb hG
  have h1 := (contactGraph_adj_iff X _ _).mp (hG _ _ e.adj)
  have hfst : (R.rot e).fst = e.fst := R.rot_fst e
  have h2adj : G.Adj e.fst (R.rot e).snd := hfst ▸ (R.rot e).adj
  have h2 := (contactGraph_adj_iff X _ _).mp (hG _ _ h2adj)
  have hsnd : e.snd ≠ (R.rot e).snd := by
    intro h
    exact hne (SimpleGraph.Dart.ext _ _ (Prod.ext hfst h.symm))
  have h12 : d ≤ sdist (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) :=
    X.sep _ _ (fun h => hsnd (emb.injective h))
  calc alpha d ≤ angle (tdir (X.pt (emb e.fst)) (X.pt (emb e.snd)))
        (tdir (X.pt (emb e.fst)) (X.pt (emb (R.rot e).snd))) :=
        alpha_le_angle d hd _ _ _ (X.unit _) (X.unit _) (X.unit _) h1.2 h2.2 h12
    _ ≤ _ := angle_le_ocorner _ _ _ (X.unit _) (hD.1 _ _ e.adj) (hD.1 _ _ h2adj)

/-- Lemma 4.2. -/
theorem lemma_minimal {d : ℝ} (hd : 0 < d ∧ d < π / 2) (X : Config 15 d)
    (hmin : ∀ Y : Config 15 d, contactCount X ≤ contactCount Y) [DecidableRel G.Adj]
    (emb : V ↪ Fin 15) (hG : ∀ a b, G.Adj a b ↔ (contactGraph X).Adj (emb a) (emb b))
    (hcov : ∀ a j, (contactGraph X).Adj (emb a) j → ∃ b, emb b = j)
    (hnr : ∀ a, ∃ b, G.Adj a b) (R : RotSys G) (hR : IsAngular R (X.pt ∘ emb)) :
    (∀ e : G.Dart,
      alpha d ≤ ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) ∧
        ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) < π) ∧
      ∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5 := by
  have hdpi : 0 < d ∧ d < π := ⟨hd.1, by linarith [Real.pi_pos, hd.2]⟩
  have hD := distinctDirs_contact hdpi X emb (fun a b h => (hG a b).mp h)
  have hno : ∀ e : G.Dart,
      ¬ (π ≤ ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) ∨
        R.rot e = e) := by
    intro e he
    obtain ⟨t, ht, hvt, htw⟩ := exists_push_dir (X.pt ∘ emb) (fun v => X.unit _) hD R hR e he
    obtain ⟨X', hsame, hfar⟩ := shift_config hd X (emb e.fst) t ht hvt (by
      intro j hj hdj
      have hc : (contactGraph X).Adj (emb e.fst) j :=
        (contactGraph_adj_iff X _ _).mpr ⟨fun h => hj h.symm, hdj⟩
      obtain ⟨b, rfl⟩ := hcov e.fst j hc
      exact htw b ((hG _ _).mpr hc))
    have hlt := contactCount_lt_of_shift X X' (emb e.fst) hsame hfar
      ⟨emb e.snd, (hG _ _).mp e.adj⟩
    exact absurd (hmin X') (not_le.mpr hlt)
  have hcorner : ∀ e : G.Dart,
      alpha d ≤ ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) ∧
        ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) < π := by
    intro e
    have h := not_or.mp (hno e)
    exact ⟨alpha_le_corner hd X emb (fun a b h => (hG a b).mp h) R e h.2, not_le.mp h.1⟩
  refine ⟨hcorner, fun a => ?_⟩
  obtain ⟨b, hab⟩ := hnr a
  let e0 : G.Dart := ⟨(a, b), hab⟩
  have hne : R.rot e0 ≠ e0 := (not_or.mp (hno e0)).2
  have hfst : (R.rot e0).fst = a := R.rot_fst e0
  have hac : G.Adj a (R.rot e0).snd := hfst ▸ (R.rot e0).adj
  have hbc : b ≠ (R.rot e0).snd := by
    intro h
    exact hne (SimpleGraph.Dart.ext _ _ (Prod.ext hfst h.symm))
  have hsum := corner_sum (X.pt ∘ emb) (fun v => X.unit _) hD R hR a
    ⟨b, (R.rot e0).snd, hbc, hab, hac⟩
  have hcard : (Finset.univ.filter (fun e : G.Dart => e.fst = a)).card = G.degree a :=
    G.dart_fst_fiber_card_eq_degree a
  set S := Finset.univ.filter (fun e : G.Dart => e.fst = a) with hS
  have hmem : ∀ e ∈ S, e.fst = a := fun e he => (Finset.mem_filter.mp he).2
  have hterm : ∀ e ∈ S,
      alpha d ≤ ocorner ((X.pt ∘ emb) a) ((X.pt ∘ emb) e.snd) ((X.pt ∘ emb) (R.rot e).snd) ∧
        ocorner ((X.pt ∘ emb) a) ((X.pt ∘ emb) e.snd) ((X.pt ∘ emb) (R.rot e).snd) < π := by
    intro e he
    have h := hcorner e
    rw [hmem e he] at h
    exact h
  have hα := alpha_bounds d hd
  have hlow : (S.card : ℝ) * alpha d ≤ 2 * π := by
    rw [← hsum]
    have h := Finset.sum_le_sum (fun e he => (hterm e he).1)
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have hne' : S.Nonempty := ⟨e0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hhigh : 2 * π < (S.card : ℝ) * π := by
    rw [← hsum]
    have h := Finset.sum_lt_sum_of_nonempty hne' (fun e he => (hterm e he).2)
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have h6 : (S.card : ℝ) < 6 := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith [mul_le_mul_of_nonneg_right h (le_of_lt (lt_trans (by positivity) hα.1))]
  have h2 : (2 : ℝ) < S.card := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith [Real.pi_pos]
  rw [← hcard]
  have h6' : S.card < 6 := by exact_mod_cast h6
  have h2' : 2 < S.card := by exact_mod_cast h2
  omega

end Tammes15
