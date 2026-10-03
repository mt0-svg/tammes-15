import Tammes15.Draw.Minimal
import Tammes15.Draw.Iface
import Tammes15.Draw.Count

/-!
# Theorem 4.1

`structure_theorem`: some maximal configuration of 15 points is structured. The proof takes a
maximal configuration with fewest contacts (`exists_min_contacts`), indexes its non-rattlers by
`Fin n`, and assembles the fields of `Structured`: the angular rotation system
(`exists_angular`), Lemma 4.2 (`lemma_minimal`), Corollary A.6 (`twoconn_contact`),
Lemmas A.7, 4.3 and 4.4 (`faceconvex_contact`), item (4) (`rattlers_in_hexagons`) and
Corollary 4.7 (`k_le_three_of_hex`).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

/-- A finset of `Fin N` is the range of an embedding of `Fin` of its size. -/
theorem exists_emb_fin_card {N : ℕ} (S : Finset (Fin N)) :
    ∃ emb : Fin S.card ↪ Fin N, ∀ i, (∃ a, emb a = i) ↔ i ∈ S := by
  refine ⟨(S.orderEmbOfFin rfl).toEmbedding, λ i => ?_⟩
  have h := Finset.range_orderEmbOfFin S rfl
  -- h : Set.range ⇑(S.orderEmbOfFin rfl) = ↑S
  rw [← Finset.mem_coe, ← h, Set.mem_range]
  -- Goal: (∃ a, ((S.orderEmbOfFin rfl).toEmbedding) a = i) ↔ (∃ a, ⇑(S.orderEmbOfFin rfl) a = i)
  simp

section

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Theorem 4.1 for a maximal configuration with fewest contacts and an indexing `emb` of its
non-rattlers. `hmarg` keeps `[dlo, dhi]` inside the paper's range
`[Tammes15.dlo, Tammes15.dhi]`, as `rattlers_in_hexagons` needs. -/
theorem structured_of_min (dlo dhi d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi)
    (hmax : IsGreatest {d | Nonempty (Config 15 d)} d)
    (hmarg : 7 * dlo > 2 * π ∧ alpha dhi < 2 * π / 5 ∧ Tammes15.dlo ≤ dlo ∧ dhi ≤ Tammes15.dhi)
    (hd : 0 < d ∧ d < π / 2)
    (X : Config 15 d) (hmin : ∀ Y : Config 15 d, contactCount X ≤ contactCount Y)
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
  obtain ⟨hcorner, hdeg⟩ := lemma_minimal hd X hmin emb hG hcov hnr R hR
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
  haveI := hV
  obtain ⟨hconn, h2, hsph, hf3, hwalk⟩ :=
    twoconn_contact (X.pt ∘ emb) (fun v => X.unit _) (cos d) hc hsepc hGc hnr R hR hcorner0
  obtain ⟨hconv, hfaces, h3⟩ :=
    faceconvex_contact dlo d hmarg.1 hlo hd (X.pt ∘ emb) (fun v => X.unit _) hsep' hGiff R hR
      hcorner hdeg hconn h2 hsph hf3 hwalk
  obtain ⟨hexOf, h6, hin, hdist⟩ :=
    rattlers_in_hexagons dlo dhi d hmarg hlo hhi hd hmax X hmin emb hG hrat R hR hcorner hdeg h3
      hsph hfaces hconv
  have hrk : Fintype.card {i : Fin 15 // ∀ a, emb a ≠ i} = k := by
    have := card_compl_range_add emb
    omega
  have hk3 : k ≤ 3 :=
    k_le_three_of_hex k hcard R (fun a => (hdeg a).1) hsph (fun e => (hfaces e).1) hrk hexOf h6
      hdist
  exact ⟨⟨emb, by omega, hG, hrat, R, hR, hcorner, hdeg, h3, hsph, hfaces, hconv, hexOf, h6, hin,
    hdist, hk3⟩⟩

end

/-- Theorem 4.1: some maximal configuration is structured. `dlo, dhi` are the
parameters of the range of `d15`, with the two margins the proof uses and inside the paper's range
`[Tammes15.dlo, Tammes15.dhi]`: the margins of the hexagon argument (`nor`, the one hexagon
margin) hold only there, and without the last two conjuncts the parameters do not keep `d15`
in that range. -/
theorem structure_theorem (dlo dhi d15 : ℝ) (hlo : dlo ≤ d15) (hhi : d15 ≤ dhi)
    (hmax : IsGreatest {d | Nonempty (Config 15 d)} d15)
    (hmarg : 7 * dlo > 2 * π ∧ alpha dhi < 2 * π / 5 ∧ Tammes15.dlo ≤ dlo ∧
      dhi ≤ Tammes15.dhi) :
    ∃ X : Config 15 d15, ∃ k : ℕ, ∃ G : SimpleGraph (Fin (15 - k)),
      Nonempty (Structured (V := Fin (15 - k)) (G := G) X k) := by
  have hdlo : 0 < dlo := by nlinarith [Real.pi_pos, hmarg.1]
  obtain ⟨X0⟩ := hmax.1
  have hd : 0 < d15 ∧ d15 < π / 2 := ⟨lt_of_lt_of_le hdlo hlo, lt_pi_div_two_of_config15 X0⟩
  obtain ⟨X, hmin⟩ := exists_min_contacts hmax.1
  set S : Finset (Fin 15) := Finset.univ.filter (fun i => ∃ j, (contactGraph X).Adj i j)
    with hSdef
  have hS15 : S.card ≤ 15 := by simpa using Finset.card_le_univ S
  obtain ⟨e0, he0⟩ := exists_emb_fin_card S
  have hn : 15 - (15 - S.card) = S.card := by omega
  let emb : Fin (15 - (15 - S.card)) ↪ Fin 15 := (finCongr hn).toEmbedding.trans e0
  have hmemS : ∀ i, i ∈ S ↔ ∃ j, (contactGraph X).Adj i j := fun i => by simp [hSdef]
  have hS : ∀ i, (∃ a, emb a = i) ↔ ∃ j, (contactGraph X).Adj i j := by
    intro i
    rw [← hmemS i, ← he0 i]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨finCongr hn a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(finCongr hn).symm a, by simp [emb]⟩
  obtain ⟨i, j, hij, hsd⟩ := exists_contact_of_isGreatest (by norm_num) hmax X
  have hV : Nonempty (Fin (15 - (15 - S.card))) := by
    obtain ⟨a, _⟩ := (hS i).mpr ⟨j, (contactGraph_adj_iff X i j).mpr ⟨hij, hsd⟩⟩
    exact ⟨a⟩
  refine ⟨X, 15 - S.card, (contactGraph X).comap emb, ?_⟩
  exact structured_of_min dlo dhi d15 hlo hhi hmax hmarg hd X hmin emb (fun a b => Iff.rfl) hS
    (15 - S.card) (by simp only [Fintype.card_fin]; omega) hV

end Tammes15
