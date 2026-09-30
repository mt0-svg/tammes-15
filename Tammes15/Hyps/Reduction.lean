import Tammes15.Hyps.Interfaces
import Tammes15.Hyps.Transport
import Tammes15.Local41.Chain
import Tammes15.Glue.Pair
import Tammes15.Trigrows.Sdist

/-!
# The capstone: `Tammes15.Conjecture` from D1 to D4

`reduction L F : FejesTothBound → KappaHyp F → EnumComplete L → Killed L F → AttainedHyp F →
Conjecture`.

The proof is the written reduction. Attainment is D4. For the upper bound, a configuration with
all angles above `ψ* = arccos u` gives a maximal configuration at `d₁₅ ∈ (ψ*, dhi]`
(`exists_isGreatest_config`, `FejesTothBound`), hence (Theorem 3.1, `structure_theorem`) a
structured one, hence a realisation of a case of a plane graph of the class
(`realisation_of_structured`); D2 and `realisation_transport` move it to a case of an entry of the
list, whose assignment satisfies the relation system (`relSys_of_realisation`). D3 then gives a
gluing firing Pair or Local; the gluing is the realisation up to isometry (`glue_congruent`), so
Pair contradicts the separation `d₁₅`, and Local with Theorem 4.1 (`local_optimality`, with D1 and
D4) gives two points at inner product at least `u`, while all inner products are below
`cos d₁₅ < u`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

/-! ## Numeric facts -/

/-- The root `u = 0.5926059…` of the quintic lies below `0.5927`. -/
theorem root_lt (u : ℝ) (h1 : 1 / 2 < u) (h2 : u < 7 / 10) (h0 : quintic u = 0) :
    u < 0.5927 := by
  by_contra h
  push Not at h
  have hle : quintic 0.5927 ≤ quintic u :=
    (quintic_strictMonoOn.le_iff_le ⟨by norm_num, by norm_num⟩ ⟨h1.le, h2.le⟩).mpr h
  have hpos : 0 < quintic 0.5927 := by unfold quintic; norm_num
  linarith

/-- The radius condition of Theorem 4.1 for `r = 1.04·10⁻³`, `κ₀ = 6.4980·10⁻³`, `n = 15`. -/
theorem radius_ok (u : ℝ) (h0 : 0 < u) (hu : u < 0.5927) :
    Real.sqrt ((15 : ℕ) : ℝ) * rLocal * (1.01 * (1 + u)) ≤ kappa0 := by
  have hs : Real.sqrt ((15 : ℕ) : ℝ) < 3.873 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt ((15 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have h1 : Real.sqrt ((15 : ℕ) : ℝ) * rLocal * (1.01 * (1 + u)) ≤
      3.873 * rLocal * (1.01 * (1 + 0.5927)) := by
    unfold rLocal
    have ha : Real.sqrt ((15 : ℕ) : ℝ) * 1.04e-3 ≤ 3.873 * 1.04e-3 := by nlinarith
    have hb : 1.01 * (1 + u) ≤ 1.01 * (1 + 0.5927) := by nlinarith
    exact mul_le_mul ha hb (by positivity) (by positivity)
  refine h1.trans ?_
  unfold rLocal kappa0; norm_num

/-- The small-displacement condition of Theorem 4.1. -/
theorem radius_sq_ok : ((15 : ℕ) : ℝ) * rLocal ^ 2 < 0.02 := by
  unfold rLocal; norm_num

/-! ## From Theorem 3.1 to a realisation -/

/-- A structured configuration (Theorem 3.1) gives a plane graph of the class and a realisation
of one of its cases, with the rattlers as free points. -/
theorem realisation_of_structured {d : ℝ} (hd : dlo ≤ d ∧ d ≤ dhi) (X : Config 15 d) (k : ℕ)
    (G : SimpleGraph (Fin (15 - k))) (S : Structured (V := Fin (15 - k)) (G := G) X k) :
    InClass ⟨15 - k, G, S.R⟩ ∧ ∃ (H : HexChoice ⟨15 - k, G, S.R⟩ k)
      (x : Pts ⟨15 - k, G, S.R⟩ k → E3), Realisation ⟨15 - k, G, S.R⟩ H d x := by
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
  refine ⟨H, fun a => X.pt (ι a), ?_⟩
  exact
    { d_mem := ⟨hdpos, hdlt⟩
      unit := fun a => X.unit _
      edge := fun v w h => ((contactGraph_adj_iff X _ _).mp ((S.G_eq v w).mp h)).2
      angular := S.angular
      convex := S.convex
      corners := S.corners
      sep := fun a b hab => X.sep _ _ (hι.ne hab)
      inside := fun m j => S.hexOf_inside (e m) j }

/-! ## The relation system of a realisation -/

/-- The assignment of a realisation satisfies the relation system (assembled from the
interfaces). -/
theorem relSys_of_realisation {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ}
    {x : Pts P k → E3} (hP : InClass P) (hd : dlo ≤ d ∧ d ≤ dhi) (hx : Realisation P H d x) :
    RelSys P H (assignOf P H d x) where
  corner_mem e := hx.corners e
  vertex_sum v := vertexSum_of_realisation hP hd hx v
  tri e he := tri_of_realisation hP hd hx e he
  rhombus e he := rhombus_of_realisation hP hd hx e he
  pent e he := pent_of_realisation hP hd hx e he
  hex e he := hex_of_realisation hP hd hx e he
  hexDiag e he := hexDiag_of_realisation hP hd hx e he
  wheel m := wheel_of_realisation hP hd hx m

/-! ## Attainment and the upper bound -/

/-- D4 gives attainment. -/
theorem attained_of_hyp (F : Set Frame) (h4 : AttainedHyp F) : Attained := by
  obtain ⟨⟨q, hq⟩, u, hu1, hu2, hu0, hF⟩ := h4
  intro u' h1 h2 h0
  have huu : u' = u := existsUnique_root.unique ⟨h1, h2, h0⟩ ⟨hu1, hu2, hu0⟩
  subst huu
  obtain ⟨hp, -, hle⟩ := hF q hq
  refine ⟨q.p, hp, fun i j hij => ?_⟩
  rw [← sdist_eq_angle _ _ (hp i) (hp j),
    le_sdist_iff _ _ (hp i) (hp j) _ ⟨arccos_nonneg _, arccos_le_pi _⟩,
    cos_arccos (by linarith) (by linarith)]
  exact hle i j hij

/-- D1 to D4 give the upper bound. -/
theorem upperBound_of_hyps (L : Set PlaneGraph) (F : Set Frame) (h0 : FejesTothBound)
    (h1 : KappaHyp F)
    (h2 : EnumComplete L) (h3 : Killed L F) (h4 : AttainedHyp F) : UpperBound := by
  intro u hu1 hu2 hu0 X hX
  by_contra hne
  push Not at hne
  -- the minimal angle `m` of `X` exceeds `ψ* = arccos u`
  obtain ⟨p, hp, hmin⟩ : ∃ p : Fin 15 × Fin 15, p.1 ≠ p.2 ∧
      ∀ q : Fin 15 × Fin 15, q.1 ≠ q.2 → angle (X p.1) (X p.2) ≤ angle (X q.1) (X q.2) := by
    obtain ⟨p, hp, hmin⟩ := Set.Finite.exists_minimalFor
      (fun q : Fin 15 × Fin 15 => angle (X q.1) (X q.2)) {q | q.1 ≠ q.2} (Set.toFinite _)
      ⟨(0, 1), by decide⟩
    exact ⟨p, hp, fun q hq => by
      by_contra h
      push Not at h
      exact absurd (hmin hq h.le) (not_le.mpr h)⟩
  have hm : arccos u < angle (X p.1) (X p.2) := hne _ _ hp
  have hC : Nonempty (Config 15 (angle (X p.1) (X p.2))) :=
    ⟨⟨X, hX, fun i j hij => by
      rw [sdist_eq_angle _ _ (hX i) (hX j)]; exact hmin (i, j) hij⟩⟩
  -- the maximal separation `d₁₅`
  obtain ⟨d15, hmax⟩ := exists_isGreatest_config 15 (by norm_num)
  have hmd : angle (X p.1) (X p.2) ≤ d15 := hmax.2 hC
  obtain ⟨X15⟩ := hmax.1
  have hdhi : d15 ≤ dhi := h0 d15 ⟨X15⟩
  have hψ : arccos u < d15 := hm.trans_le hmd
  have hdlo : dlo < d15 := (dlo_lt_arccos_root u hu1 hu2 hu0).trans hψ
  have hd : dlo ≤ d15 ∧ d15 ≤ dhi := ⟨hdlo.le, hdhi⟩
  have hd15 : 0 ≤ d15 ∧ d15 ≤ π := by
    have := pi_div_four_lt_dlo
    have := dhi_lt_pi_div_three
    have := Real.pi_pos
    constructor <;> linarith
  -- Theorem 3.1, a case of the list, its relation system
  obtain ⟨Y, k, G, ⟨S⟩⟩ :=
    structure_theorem dlo dhi d15 hdlo.le hdhi hmax
      ⟨two_pi_lt_seven_dlo, alpha_dhi_lt, le_rfl, le_rfl⟩
  obtain ⟨hP, H, x, hx⟩ := realisation_of_structured hd Y k G S
  have hk := S.k_le
  obtain ⟨P', hP'L, hn, hiso⟩ := h2 (15 - k) (by omega) (by omega) G S.R hP
  obtain ⟨hP', H', x', hx'⟩ := realisation_transport hP hiso hx
  have hrel := relSys_of_realisation hP' hd hx'
  obtain ⟨g, hg, hfire⟩ := h3 P' hP'L k (by omega) H' _ hdlo.le hdhi hrel
  obtain ⟨O, hO⟩ := glue_congruent hP' hd hx' g hg
  -- distinct points of the realisation have inner product below `u`
  have hcos : cos d15 < u := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (arccos_nonneg u) hd15.2 hψ
    rwa [cos_arccos (by linarith) (by linarith)] at h
  have hsmall : ∀ a b, a ≠ b → ⟪x' a, x' b⟫ < u := fun a b hab =>
    lt_of_le_of_lt ((le_sdist_iff _ _ (hx'.unit a) (hx'.unit b) d15 hd15).mp (hx'.sep a b hab))
      hcos
  rcases hfire with ⟨a, b, hab, -, hlt⟩ | ⟨q, hq, O2, j, hj⟩
  · -- Pair contradicts the separation
    rw [hO a, hO b, ← map_sub, LinearIsometryEquiv.norm_map] at hlt
    have := pair_core (x' a) (x' b) (x' a) (x' b) (hx'.unit a) (hx'.unit b) d15 0 0 hd15
      (hx'.sep a b hab) (by simp) (by simp)
    change ‖x' a - x' b‖ < 2 * sin (d15 / 2) at hlt
    linarith
  · -- Local and Theorem 4.1
    obtain ⟨-, u', hu1', hu2', hu0', hF⟩ := h4
    have huu : u' = u := existsUnique_root.unique ⟨hu1', hu2', hu0'⟩ ⟨hu1, hu2, hu0⟩
    subst huu
    obtain ⟨hpu, hSu, -⟩ := hF q hq
    obtain ⟨ij, hij, hle⟩ := local_optimality q.p q.S u' kappa0 rLocal hpu
      (fun ij hij => ⟨(hSu ij hij).2, (hSu ij hij).1⟩) (by linarith) (h1 q hq)
      (radius_ok u' (by linarith) (root_lt u' hu1 hu2 hu0)) radius_sq_ok
      (fun i => glueY H' (assignOf P' H' d15 x') g (j.symm i))
      (fun i => by rw [hO, LinearIsometryEquiv.norm_map]; exact hx'.unit _) O2
      (fun i => by simpa using hj (j.symm i))
    rw [hO, hO, LinearIsometryEquiv.inner_map_map] at hle
    have hne' : j.symm ij.1 ≠ j.symm ij.2 := fun h => (hSu ij hij).1 (j.symm.injective h)
    linarith [hsmall _ _ hne']

/-- The capstone: the Fejes Tóth bound (`FejesTothBound`, a literature input) and the four
computations D1 (`KappaHyp`), D2 (`EnumComplete`), D3 (`Killed`) and D4 (`AttainedHyp`) imply the
Tammes conjecture for 15 points, `Tammes15.Conjecture` of `lean/Tammes15/Statement.lean`. -/
theorem reduction (L : Set PlaneGraph) (F : Set Frame) (h0 : FejesTothBound) (h1 : KappaHyp F)
    (h2 : EnumComplete L) (h3 : Killed L F) (h4 : AttainedHyp F) : Conjecture :=
  conjecture_iff.mpr ⟨attained_of_hyp F h4, upperBound_of_hyps L F h0 h1 h2 h3 h4⟩

end Tammes15
