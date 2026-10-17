/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
import Tammes15.Attained.Final
import Tammes15.PaperSteps.LocalEq
import Tammes15.Draw.Structure
import Tammes15.Hyps.Reduction
import Tammes15.Contractors.Main

/-!
# The maximal configurations

`classification_of_enum_killed`: from D2 (`EnumComplete L`) and D3 (`Killed L {frameC1, frameC3}`),
every fifteen points of the sphere at pairwise distance at least `ψ* = arccos u` are an orthogonal
image of `C1` or of `C3`, up to labelling; `classification_of_enum_progTreesDom` gives the same from
the hypotheses of `conjecture_of_enum_progTreesDom`.

The structure theorem (`structured_of_min`) is proved for a configuration with the fewest contacts,
and that minimality enters only to exclude a corner `≥ π` (`lemma_minimal`). Here it is replaced by
`Unshiftable`: no point with a contact can be moved off all its contacts while the others stay.
Starting from any configuration `X` at separation `ψ*`, shifting such points one at a time never
creates a contact, so the least contact count among the configurations that keep the points of `X`
that still have contacts (`Descends`) is attained by an unshiftable `Y` (`exists_unshiftable`). The
structure theorem, D2, D3 and the equality case of local optimality
(`PaperSteps.local_optimality_frame`) make `Y` an image of `C1` or `C3`, whose points all have
contacts; so no point was shifted, and `X = Y`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

/-- No point of `X` that has a contact can be moved to a point at distance more than `d` from all
the others while the others stay. -/
def Unshiftable {d : ℝ} (X : Config 15 d) : Prop :=
  ∀ (i : Fin 15) (X' : Config 15 d), (∀ j, j ≠ i → X'.pt j = X.pt j) →
    (∀ j, j ≠ i → d < sdist (X'.pt i) (X'.pt j)) → ¬ ∃ j, (contactGraph X).Adj i j

/-- `Y` keeps every point of `X` that has a contact in `Y`. -/
def Descends {d : ℝ} (X Y : Config 15 d) : Prop :=
  ∀ i, (∃ j, (contactGraph Y).Adj i j) → Y.pt i = X.pt i

section Unshift

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- `lemma_minimal` for an unshiftable configuration: the same proof, whose minimality
serves only to exclude a corner `≥ π` by a shift. -/
theorem lemma_unshiftable {d : ℝ} (hd : 0 < d ∧ d < π / 2) (X : Config 15 d)
    (hns : Unshiftable X) [DecidableRel G.Adj]
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
    exact hns (emb e.fst) X' hsame hfar ⟨emb e.snd, (hG _ _).mp e.adj⟩
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


end Unshift

open scoped Classical

/-- A configuration at separation `d` descends to an unshiftable one: take the least contact
count among the configurations that keep the points of `X` with contacts; a shift of such a
configuration keeps that property and lowers the count. -/
theorem exists_unshiftable {d : ℝ} (X : Config 15 d) :
    ∃ Y : Config 15 d, Descends X Y ∧ Unshiftable Y := by
  have hex : ∃ n, ∃ Y : Config 15 d, Descends X Y ∧ contactCount Y = n :=
    ⟨_, X, fun _ _ => rfl, rfl⟩
  obtain ⟨Y, hY, hYn⟩ := Nat.find_spec hex
  refine ⟨Y, hY, fun i X' hsame hfar hc => ?_⟩
  have hlt := contactCount_lt_of_shift Y X' i hsame hfar hc
  have hnoti : ∀ a b, (contactGraph X').Adj a b → a ≠ i := by
    rintro a b hab rfl
    obtain ⟨hne, hsd⟩ := (contactGraph_adj_iff X' a b).mp hab
    have h := hfar b (Ne.symm hne)
    rw [hsd] at h
    exact lt_irrefl d h
  have hD : Descends X X' := by
    rintro a ⟨b, hab⟩
    have hai := hnoti a b hab
    have hbi := hnoti b a hab.symm
    obtain ⟨hne, hsd⟩ := (contactGraph_adj_iff X' a b).mp hab
    have hY' : (contactGraph Y).Adj a b := by
      rw [contactGraph_adj_iff]
      refine ⟨hne, ?_⟩
      rw [← hsame a hai, ← hsame b hbi]
      exact hsd
    rw [hsame a hai]
    exact hY a ⟨b, hY'⟩
  have := Nat.find_min' hex ⟨X', hD, rfl⟩
  omega

section

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The conclusions of `structured_of_min` for an unshiftable configuration: the proof of
`structured_of_min` with `lemma_unshiftable` for `lemma_minimal`, and item (4) from
`Geom.rattlers_core`, which needs neither minimality nor maximality. -/
theorem structured_of_unshiftable (dlo dhi d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi)
    (hmarg : 7 * dlo > 2 * π ∧ alpha dhi < 2 * π / 5 ∧ Tammes15.dlo ≤ dlo ∧ dhi ≤ Tammes15.dhi)
    (hd : 0 < d ∧ d < π / 2)
    (X : Config 15 d) (hns : Unshiftable X)
    (emb : V ↪ Fin 15) (hG : ∀ a b, G.Adj a b ↔ (contactGraph X).Adj (emb a) (emb b))
    (hS : ∀ i, (∃ a, emb a = i) ↔ ∃ j, (contactGraph X).Adj i j)
    (k : ℕ) (hcard : Fintype.card V + k = 15) (hV : Nonempty V) :
    Nonempty (Structured (V := V) (G := G) X k) := by
  have hdpi : 0 < d ∧ d < π := ⟨hd.1, by linarith [Real.pi_pos, hd.2]⟩
  have hrat : ∀ i, (∀ a, emb a ≠ i) → ∀ j, j ≠ i → d < sdist (X.pt i) (X.pt j) := by
    intro i hi j hj
    have hij : i ≠ j := fun h => hj h.symm
    refine lt_of_le_of_ne (X.sep i j hij) (fun heq => ?_)
    obtain ⟨a, ha⟩ := (hS i).mpr ⟨j, (contactGraph_adj_iff X i j).mpr ⟨hij, heq.symm⟩⟩
    exact hi a ha
  have hcov : ∀ a j, (contactGraph X).Adj (emb a) j → ∃ b, emb b = j :=
    fun a j h => (hS j).mpr ⟨emb a, h.symm⟩
  have hnr : ∀ a, ∃ b, G.Adj a b := by
    intro a
    obtain ⟨j, hj⟩ := (hS (emb a)).mp ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := hcov a j hj
    exact ⟨b, (hG a b).mpr hj⟩
  have hD := distinctDirs_contact hdpi X emb (fun a b h => (hG a b).mp h)
  obtain ⟨R, hR⟩ := exists_angular (X.pt ∘ emb) (fun v => X.unit _) hD
  obtain ⟨hcorner, hdeg⟩ := lemma_unshiftable hd X hns emb hG hcov hnr R hR
  have hsep' : ∀ a b, a ≠ b → d ≤ sdist ((X.pt ∘ emb) a) ((X.pt ∘ emb) b) :=
    fun a b hab => X.sep _ _ (emb.injective.ne hab)
  have hGd : ∀ a b, G.Adj a b → sdist ((X.pt ∘ emb) a) ((X.pt ∘ emb) b) = d :=
    fun a b h => ((contactGraph_adj_iff X _ _).mp ((hG a b).mp h)).2
  have hGiff : ∀ a b, G.Adj a b ↔ a ≠ b ∧ sdist ((X.pt ∘ emb) a) ((X.pt ∘ emb) b) = d :=
    fun a b => by
      rw [hG a b, contactGraph_adj_iff, emb.injective.ne_iff]
      exact Iff.rfl
  have hc : cos d < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hdpi.2.le hd.1
    rwa [Real.cos_zero] at h
  have hsepc : ∀ a b, a ≠ b → ⟪(X.pt ∘ emb) a, (X.pt ∘ emb) b⟫ ≤ cos d := fun a b hab =>
    (le_sdist_iff _ _ (X.unit _) (X.unit _) d ⟨hd.1.le, hdpi.2.le⟩).mp (hsep' a b hab)
  have hGc : ∀ a b, G.Adj a b → ⟪(X.pt ∘ emb) a, (X.pt ∘ emb) b⟫ = cos d := fun a b h => by
    rw [← cos_sdist ((X.pt ∘ emb) a) ((X.pt ∘ emb) b) (X.unit _) (X.unit _), hGd a b h]
  have hα := alpha_bounds d hd
  have hcorner0 : ∀ e : G.Dart,
      0 < ocorner ((X.pt ∘ emb) e.fst) ((X.pt ∘ emb) e.snd) ((X.pt ∘ emb) (R.rot e).snd) ∧
        ocorner ((X.pt ∘ emb) e.fst) ((X.pt ∘ emb) e.snd) ((X.pt ∘ emb) (R.rot e).snd) < π :=
    fun e => ⟨lt_of_lt_of_le (by linarith [Real.pi_pos]) (hcorner e).1, (hcorner e).2⟩
  have := hV
  obtain ⟨hconn, h2, hsph, hf3, hwalk⟩ :=
    twoconn_contact (X.pt ∘ emb) (fun v => X.unit _) (cos d) hc hsepc hGc hnr R hR hcorner0
  obtain ⟨hconv, hfaces, h3⟩ :=
    faceconvex_contact dlo d hmarg.1 hlo hd (X.pt ∘ emb) (fun v => X.unit _) hsep' hGiff R hR
      hcorner hdeg hconn h2 hsph hf3 hwalk
  obtain ⟨hexOf, h6, hin, hdist⟩ :=
    Geom.rattlers_core d (le_trans hmarg.2.2.1 hlo) (le_trans hhi hmarg.2.2.2) hd X emb hG hrat R hR
      hcorner hdeg hfaces hconv
  have hrk : Fintype.card {i : Fin 15 // ∀ a, emb a ≠ i} = k := by
    have := card_compl_range_add emb
    omega
  have hk3 : k ≤ 3 :=
    k_le_three_of_hex k hcard R (fun a => (hdeg a).1) hsph (fun e => (hfaces e).1) hrk hexOf h6
      hdist
  exact ⟨⟨emb, by omega, hG, hrat, R, hR, hcorner, hdeg, h3, hsph, hfaces, hconv, hexOf, h6, hin,
    hdist, hk3⟩⟩


end

/-- `realisation_of_structured`, with the points of the realisation those of the configuration
under a bijection. -/
theorem realisation_of_structured_pts {d : ℝ} (hd : dlo ≤ d ∧ d ≤ dhi) (X : Config 15 d) (k : ℕ)
    (G : SimpleGraph (Fin (15 - k))) (S : Structured (V := Fin (15 - k)) (G := G) X k) :
    InClass ⟨15 - k, G, S.R⟩ ∧ ∃ (H : HexChoice ⟨15 - k, G, S.R⟩ k)
      (x : Pts ⟨15 - k, G, S.R⟩ k → E3), Realisation ⟨15 - k, G, S.R⟩ H d x ∧
        ∃ ι : Pts ⟨15 - k, G, S.R⟩ k ≃ Fin 15, ∀ a, x a = X.pt (ι a) := by
  refine ⟨⟨S.threeConn, S.degrees, S.faces, S.spherical⟩, ?_⟩
  have hk := S.k_le
  -- the rattlers, indexed by `Fin k`
  have hcard : Fintype.card {i : Fin 15 // ∀ a, S.emb a ≠ i} = k := by
    have h1 : Fintype.card {i : Fin 15 // i ∈ Set.range S.emb} = 15 - k := by
      have := Set.card_range_of_injective S.emb.injective
      rw [Fintype.card_fin] at this
      exact (Fintype.card_congr (Equiv.refl _)).trans this
    have h2 : Fintype.card {i : Fin 15 // ∀ a, S.emb a ≠ i} =
        Fintype.card {i : Fin 15 // i ∉ Set.range S.emb} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by simp [Set.mem_range]))
    rw [h2, Fintype.card_subtype_compl, h1, Fintype.card_fin]
    omega
  let e : Fin k ≃ {i : Fin 15 // ∀ a, S.emb a ≠ i} := (Fintype.equivFinOfCardEq hcard).symm
  let H : HexChoice ⟨15 - k, G, S.R⟩ k :=
    { base := fun m => S.hexOf (e m)
      hex := fun m => S.hexOf_six (e m)
      distinct := fun m m' h => by
        by_contra hne
        exact S.hexOf_distinct (e m) (e m') (fun h' => hne (e.injective h')) h }
  let ι : Pts ⟨15 - k, G, S.R⟩ k → Fin 15 := Sum.elim S.emb (fun m => (e m).1)
  have hι : Function.Injective ι :=
    Function.Injective.sumElim S.emb.injective (fun m m' h => e.injective (Subtype.ext h))
      (fun a m h => (e m).2 a h)
  have hdpos : 0 < d := lt_of_lt_of_le (lt_trans (by positivity) pi_div_four_lt_dlo) hd.1
  have hdlt : d < π / 2 := by
    have := dhi_lt_pi_div_three
    have := Real.pi_pos
    linarith [hd.2]
  have hbij : Function.Bijective ι := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hι, ?_⟩
    simp only [Pts, Fintype.card_sum, Fintype.card_fin]
    omega
  refine ⟨H, fun a => X.pt (ι a), ?_, Equiv.ofBijective ι hbij, fun a => rfl⟩
  exact
    { d_mem := ⟨hdpos, hdlt⟩
      unit := fun a => X.unit _
      edge := fun v w h => ((contactGraph_adj_iff X _ _).mp ((S.G_eq v w).mp h)).2
      angular := S.angular
      convex := S.convex
      corners := S.corners
      sep := fun a b hab => X.sep _ _ (hι.ne hab)
      inside := fun m j => S.hexOf_inside (e m) j }

/-- `realisation_transport`, with the points of the new realisation those of the old one under a
bijection, up to the antipodal map. -/
theorem realisation_transport_pts {P P' : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ}
    {x : Pts P k → E3} (hP : InClass P) (hiso : P.R.IsoRefl P'.R) (hx : Realisation P H d x) :
    InClass P' ∧ ∃ (H' : HexChoice P' k) (x' : Pts P' k → E3), Realisation P' H' d x' ∧
      ∃ σ : Pts P' k ≃ Pts P k, (∀ a, x' a = x (σ a)) ∨ (∀ a, x' a = -x (σ a)) := by
  obtain ⟨φ, hA | hB⟩ := hiso
  · exact ⟨inClass_iso φ hA hP, H.map φ hA, _, realisation_iso φ hA hx,
      Equiv.sumCongr φ.symm.toEquiv (Equiv.refl _), Or.inl fun a => rfl⟩
  · have hA' : ∀ e, dmap φ (P.reverse.R.rot e) = P'.R.rot (dmap φ e) := by
      intro e
      have h := hB (P.R.rot.symm e)
      rw [Equiv.apply_symm_apply] at h
      rw [h, Equiv.apply_symm_apply]
      rfl
    exact ⟨inClass_iso (P := P.reverse) φ hA' (inClass_reverse hP), H.reverse.map φ hA', _,
      realisation_iso (P := P.reverse) φ hA' (realisation_reverse hx),
      Equiv.sumCongr φ.symm.toEquiv (Equiv.refl _), Or.inr fun a => rfl⟩

/-! ## The classification -/

/-- `keep ∘ e` labels the same frame configuration as `keep`. -/
theorem isFrameKeep_comp {keep : Fin 15 → Fin 18} (hk : PaperSteps.IsFrameKeep keep)
    (e : Fin 15 ≃ Fin 15) : PaperSteps.IsFrameKeep (keep ∘ e) := by
  obtain ⟨hinj, t, ht⟩ := hk
  refine ⟨hinj.comp e.injective, t, ?_⟩
  rw [← ht, ← Finset.image_image, Finset.image_univ_equiv]

theorem isFrameKeep_C1 : PaperSteps.IsFrameKeep Attained.keepC1 :=
  ⟨by decide, PaperSteps.tC1, by decide⟩

theorem isFrameKeep_C3 : PaperSteps.IsFrameKeep Attained.keepC3 :=
  ⟨by decide, fun _ => true, by decide⟩

/-- `C1` and `C3` are frame configurations: their points are those of a frame labelling. -/
theorem frame_keep_of_mem {q : Frame} (hq : q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame)) :
    ∃ keep, PaperSteps.IsFrameKeep keep ∧ ∀ m, q.p m = Attained.pt Attained.bR Attained.uR (keep m) := by
  rcases hq with rfl | hq
  · exact ⟨Attained.keepC1, isFrameKeep_C1, fun _ => rfl⟩
  · rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨Attained.keepC3, isFrameKeep_C3, fun _ => rfl⟩

/-- Every point of `C1` and of `C3` lies in one of its thirty contact pairs. -/
theorem frame_contact {q : Frame} (hq : q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame))
    (m : Fin 15) : ∃ ij ∈ q.S, ij.1 = m ∨ ij.2 = m := by
  rcases hq with rfl | hq
  · revert m; decide
  · rw [Set.mem_singleton_iff] at hq
    subst hq
    revert m; decide

/-- The classification of the maximal configurations, from D2 and D3: fifteen points of the sphere
at pairwise distance at least `arccos u` are, after relabelling, an orthogonal image of `C1` or of
`C3`. -/
theorem classification_of_enum_killed (L : Set PlaneGraph) (h2 : EnumComplete L)
    (h3 : Killed L {Attained.frameC1, Attained.frameC3}) (u : ℝ) (hu1 : 1 / 2 < u)
    (hu2 : u < 7 / 10) (hu0 : quintic u = 0) (x : Fin 15 → E3) (hx : ∀ i, ‖x i‖ = 1)
    (hsep : ∀ i j, i ≠ j → arccos u ≤ angle (x i) (x j)) :
    ∃ q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame), ∃ σ : Fin 15 ≃ Fin 15,
      ∃ R : E3 ≃ₗᵢ[ℝ] E3, ∀ i, x i = R (q.p (σ i)) := by
  -- the contact cosine of the frames is `u`
  obtain ⟨-, u', hu1', hu2', hu0', hF⟩ := Attained.attained
  have huu : u' = u := existsUnique_root.unique ⟨hu1', hu2', hu0'⟩ ⟨hu1, hu2, hu0⟩
  subst huu
  have huR : Attained.uR = u' := by
    obtain ⟨⟨hl, hh⟩, h0⟩ := Attained.uR_spec
    refine existsUnique_root.unique ⟨?_, ?_, h0⟩ ⟨hu1, hu2, hu0⟩
    · exact lt_of_lt_of_le (by norm_num [Attained.ul]) hl
    · exact lt_of_le_of_lt hh (by norm_num [Attained.uh])
  obtain ⟨-, hub⟩ := conjecture_iff.mp (conjecture_of_enum_killed L h2 h3)
  -- the configuration `X` at separation `d = arccos u`
  set d := arccos u' with hd_def
  let X : Config 15 d := ⟨x, hx, fun i j hij => by
    rw [sdist_eq_angle _ _ (hx i) (hx j)]; exact hsep i j hij⟩
  have hdlo : dlo < d := dlo_lt_arccos_root u' hu1 hu2 hu0
  have hdhi : d ≤ dhi := fejesToth_bound d ⟨X⟩
  have hd : dlo ≤ d ∧ d ≤ dhi := ⟨hdlo.le, hdhi⟩
  have hdpi : 0 < d ∧ d < π / 2 := by
    have := pi_div_four_lt_dlo
    have := dhi_lt_pi_div_three
    have := Real.pi_pos
    constructor <;> linarith
  have hd15 : 0 ≤ d ∧ d ≤ π := ⟨hdpi.1.le, by linarith [Real.pi_pos, hdpi.2]⟩
  -- an unshiftable descendant `Y`, which has a contact by the upper bound
  obtain ⟨Y, hYX, hns⟩ := exists_unshiftable X
  have hcontact : ∀ i j, i ≠ j → ⟪Y.pt i, Y.pt j⟫ = u' → (contactGraph Y).Adj i j := by
    intro i j hij hin
    refine (contactGraph_adj_iff Y i j).mpr ⟨hij, ?_⟩
    rw [sdist_eq_angle _ _ (Y.unit i) (Y.unit j), InnerProductGeometry.angle, Y.unit i, Y.unit j,
      mul_one, div_one, hin]
  obtain ⟨i0, j0, hij0, hle0⟩ := hub u' hu1 hu2 hu0 Y.pt Y.unit
  have hc0 : (contactGraph Y).Adj i0 j0 := by
    refine (contactGraph_adj_iff Y i0 j0).mpr ⟨hij0, le_antisymm ?_ (Y.sep i0 j0 hij0)⟩
    rw [sdist_eq_angle _ _ (Y.unit i0) (Y.unit j0)]
    exact hle0
  -- its non-rattlers, as in `structure_theorem`
  set S : Finset (Fin 15) := Finset.univ.filter (fun i => ∃ j, (contactGraph Y).Adj i j)
    with hSdef
  have hS15 : S.card ≤ 15 := by simpa using Finset.card_le_univ S
  obtain ⟨e0, he0⟩ := exists_emb_fin_card S
  obtain ⟨k, hk_def⟩ : ∃ k, k = 15 - S.card := ⟨_, rfl⟩
  have hn : 15 - k = S.card := by omega
  let emb : Fin (15 - k) ↪ Fin 15 := (finCongr hn).toEmbedding.trans e0
  have hmemS : ∀ i, i ∈ S ↔ ∃ j, (contactGraph Y).Adj i j := fun i => by simp [hSdef]
  have hS : ∀ i, (∃ a, emb a = i) ↔ ∃ j, (contactGraph Y).Adj i j := by
    intro i
    rw [← hmemS i, ← he0 i]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨finCongr hn a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(finCongr hn).symm a, by simp [emb]⟩
  have hV : Nonempty (Fin (15 - k)) := by
    obtain ⟨a, _⟩ := (hS i0).mpr ⟨j0, hc0⟩
    exact ⟨a⟩
  set G := (contactGraph Y).comap emb
  obtain ⟨St⟩ := structured_of_unshiftable (G := G) dlo dhi d hd.1 hd.2
    ⟨two_pi_lt_seven_dlo, alpha_dhi_lt, le_rfl, le_rfl⟩ hdpi Y hns emb (fun a b => Iff.rfl) hS k
    (by simp only [Fintype.card_fin]; omega) hV
  -- a realisation, D2, D3 and the gluing, as in `upperBound_of_hyps`
  obtain ⟨hP, H, xr, hxr, ι, hι⟩ := realisation_of_structured_pts hd Y k G St
  have hk := St.k_le
  obtain ⟨P', hP'L, hn', hiso⟩ :=
    h2 (15 - k) (by omega) (by omega) G St.R St.threeConn St.degrees
      (D2Regions.planeClass_of_structured hdpi St)
  obtain ⟨hP', H', x', hx', σ, hσ⟩ := realisation_transport_pts hP hiso hxr
  have hrel := relSys_of_realisation hP' hd hx'
  obtain ⟨g, hg, hfire⟩ := h3 P' hP'L k (by omega) H' _ hdlo.le hdhi hrel
  obtain ⟨O, hO⟩ := glue_congruent hP' hd hx' g hg
  rcases hfire with ⟨a, b, hab, -, hlt⟩ | ⟨q, hq, O2, j, hj⟩
  · -- Pair contradicts the separation
    exfalso
    rw [hO a, hO b, ← map_sub, LinearIsometryEquiv.norm_map] at hlt
    have := pair_core (x' a) (x' b) (x' a) (x' b) (hx'.unit a) (hx'.unit b) d 0 0 hd15
      (hx'.sep a b hab) (by simp) (by simp)
    change ‖x' a - x' b‖ < 2 * sin (d / 2) at hlt
    linarith
  · -- Local: `Y` is within `rLocal` of an image of `q`, point by point
    let τ : Fin 15 ≃ Pts P' k := ι.symm.trans σ.symm
    have hτ : ∀ i, xr (σ (τ i)) = Y.pt i := fun i => by simp [τ, hι]
    have hclose0 : ∀ a, ‖x' a - O.symm (O2 (q.p (j a)))‖ ≤ rLocal := fun a => by
      have h := hj a
      rw [hO a] at h
      rw [← LinearIsometryEquiv.norm_map O, map_sub, LinearIsometryEquiv.apply_symm_apply]
      exact h
    obtain ⟨Rc, hRc⟩ : ∃ Rc : E3 ≃ₗᵢ[ℝ] E3, ∀ i, ‖Y.pt i - Rc (q.p (j (τ i)))‖ ≤ rLocal := by
      rcases hσ with hσ | hσ
      · refine ⟨O2.trans O.symm, fun i => ?_⟩
        have h := hclose0 (τ i)
        rw [hσ, hτ] at h
        exact h
      · refine ⟨(O2.trans O.symm).trans (LinearIsometryEquiv.neg ℝ), fun i => ?_⟩
        have h := hclose0 (τ i)
        rw [hσ, hτ] at h
        rw [← norm_neg]
        simpa [sub_eq_add_neg, add_comm] using h
    -- local optimality with its equality case
    obtain ⟨keepQ, hkeepQ, hqp⟩ := frame_keep_of_mem hq
    let σ' : Fin 15 ≃ Fin 15 := τ.trans j
    have hkeep := isFrameKeep_comp hkeepQ σ'
    have hclose : ∀ i, ‖Y.pt i - Rc (Attained.pt Attained.bR Attained.uR ((keepQ ∘ σ') i))‖ ≤
        rLocal := fun i => by
      rw [Function.comp_apply, ← hqp]
      exact hRc i
    obtain ⟨hmin_le, heq⟩ := PaperSteps.local_optimality_frame _ hkeep Y.pt Y.unit Rc hclose
    have hge : arccos Attained.uR ≤ PaperSteps.minAngle Y.pt := by
      unfold PaperSteps.minAngle
      refine Finset.le_inf' _ _ (fun ij hij => ?_)
      have hlt' : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
      have h := Y.sep ij.1 ij.2 (ne_of_lt hlt')
      rw [sdist_eq_angle _ _ (Y.unit _) (Y.unit _)] at h
      rw [huR]
      exact h
    obtain ⟨R', hR'⟩ := heq (le_antisymm hmin_le hge)
    have hYq : ∀ i, Y.pt i = R' (q.p (σ' i)) := fun i => by
      rw [hR' i, hqp]
      rfl
    -- every point of `Y` has a contact, so `Y = X`
    have hall : ∀ i, ∃ i', (contactGraph Y).Adj i i' := by
      intro i
      obtain ⟨ij, hijS, hm⟩ := frame_contact hq (σ' i)
      obtain ⟨-, hSu, -⟩ := hF q hq
      obtain ⟨hne, hin⟩ := hSu ij hijS
      have hin' : ⟪Y.pt (σ'.symm ij.1), Y.pt (σ'.symm ij.2)⟫ = u' := by
        rw [hYq, hYq, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
          LinearIsometryEquiv.inner_map_map]
        exact hin
      have hne' : σ'.symm ij.1 ≠ σ'.symm ij.2 := fun h => hne (σ'.symm.injective h)
      have hadj := hcontact _ _ hne' hin'
      rcases hm with hm | hm
      · rw [hm, Equiv.symm_apply_apply] at hadj
        exact ⟨_, hadj⟩
      · rw [hm, Equiv.symm_apply_apply] at hadj
        exact ⟨_, hadj.symm⟩
    refine ⟨q, hq, σ', R', fun i => ?_⟩
    rw [← hYq i]
    exact (hYX i (hall i)).symm

/-- `classification_of_enum_killed` from the hypotheses of `conjecture_of_enum_progTreesDom`: D2,
the accepted trees and procedures computed by the program. -/
theorem classification_of_enum_progTreesDom (L : Set PlaneGraph) (N : PaperSteps.Procs)
    (h2 : EnumComplete L) (h3 : Contractors.ProgTreesDom L N) (hN : Contractors.Impl N) (u : ℝ)
    (hu1 : 1 / 2 < u) (hu2 : u < 7 / 10) (hu0 : quintic u = 0) (x : Fin 15 → E3)
    (hx : ∀ i, ‖x i‖ = 1) (hsep : ∀ i j, i ≠ j → arccos u ≤ angle (x i) (x j)) :
    ∃ q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame), ∃ σ : Fin 15 ≃ Fin 15,
      ∃ R : E3 ≃ₗᵢ[ℝ] E3, ∀ i, x i = R (q.p (σ i)) :=
  classification_of_enum_killed L h2 (Contractors.killed_of_progTreesDom h3 hN) u hu1 hu2 hu0 x hx
    hsep

end Tammes15
