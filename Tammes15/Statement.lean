import Mathlib

/-!
# The statement: the Tammes problem for 15 points

The problem:

  Place 15 points on the unit sphere S^2 so that the minimum angular distance between two of them
  is as large as possible. Determine the maximum d_15 and prove that the conjectured optimal
  arrangements attain it.

and, for the conjectured value, Buddenhagen and Kottwitz, "Multiplicity and Symmetry Breaking in
(Conjectured) Densest Packings of Congruent Circles on a Sphere", Section 4 and Table 1
(reference [BK] of the paper): the cosine `u` of the minimal separation angle of the
best known 15-point packings is `0.59260590292507377810...`, with minimal polynomial
`13u^5 - u^4 + 6u^3 + 2u^2 - 3u - 1`. The quintic has exactly one root in `(1/2, 7/10)`
(`existsUnique_root`), so `arccos u` below is the conjectured `d_15 = 53.6578501299...°`.

`Tammes15.Conjecture`: `arccos u` is the greatest `d` such that some 15 points of the unit sphere
have pairwise angles `≥ d`, i.e. it is the maximum `d_15`. It splits (`conjecture_iff`) into
* `Attained`: some configuration has minimal angle `≥ arccos u`. Buddenhagen and Kottwitz give
  exact coordinates for two such configurations, in a number field of degree 20;
  `Tammes15.Attained.attained` proves it for them (D4).
* `UpperBound`: every 15 points of the unit sphere have two of them at angle `≤ arccos u`, proved
  from D2 and D3 (`Tammes15.conjecture_of_enum_killed`).

The statement below asks for attainment by some configuration, not by the two named ones;
`Tammes15.nonunique_of_enum_killed` adds that two configurations whose contact graphs are not
isomorphic attain the maximum.
-/

open Real InnerProductGeometry

namespace Tammes15

/-- Euclidean 3-space; the unit sphere `S^2` is `{p | ‖p‖ = 1}`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The minimal polynomial of `u = cos d_15` (Buddenhagen and Kottwitz, Table 1, `n = 15`). -/
def quintic (u : ℝ) : ℝ := 13 * u ^ 5 - u ^ 4 + 6 * u ^ 3 + 2 * u ^ 2 - 3 * u - 1

/-- `d` is achievable by `N` points: there are `N` points of the unit sphere, pairwise at angular
distance at least `d`. The angular distance of unit vectors `p, q` is `angle p q = arccos ⟪p, q⟫`
in `[0, π]`. For `d > 0` the points are automatically distinct. -/
def Achievable (N : ℕ) (d : ℝ) : Prop :=
  ∃ X : Fin N → E3, (∀ i, ‖X i‖ = 1) ∧ ∀ i j, i ≠ j → d ≤ angle (X i) (X j)

/-- The Tammes conjecture for `N = 15`: for the root `u ∈ (1/2, 7/10)` of the quintic,
`arccos u` is the maximum of the achievable `d`. -/
def Conjecture : Prop :=
  ∃ u : ℝ, 1 / 2 < u ∧ u < 7 / 10 ∧ quintic u = 0 ∧
    IsGreatest {d | Achievable 15 d} (arccos u)

/-- Attainment, proved by the frames C1 and C3 of Buddenhagen and Kottwitz (`Tammes15.Attained.attained`). -/
def Attained : Prop :=
  ∀ u : ℝ, 1 / 2 < u → u < 7 / 10 → quintic u = 0 → Achievable 15 (arccos u)

/-- The upper bound: any 15 points of the unit sphere have two distinct indices at angular distance
at most `arccos u`. -/
def UpperBound : Prop :=
  ∀ u : ℝ, 1 / 2 < u → u < 7 / 10 → quintic u = 0 →
    ∀ X : Fin 15 → E3, (∀ i, ‖X i‖ = 1) → ∃ i j, i ≠ j ∧ angle (X i) (X j) ≤ arccos u

theorem quintic_strictMonoOn : StrictMonoOn quintic (Set.Icc (1 / 2) (7 / 10)) := by
  intro a ha b hb hab
  simp only [Set.mem_Icc] at ha hb
  unfold quintic
  have h : 0 < b - a := by linarith
  have key : 0 < 13 * (b ^ 4 + b ^ 3 * a + b ^ 2 * a ^ 2 + b * a ^ 3 + a ^ 4)
      - (b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3) + 6 * (b ^ 2 + b * a + a ^ 2) + 2 * (b + a) - 3 := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < a) (by linarith : (0 : ℝ) < b),
      pow_pos (by linarith : (0 : ℝ) < a) 3, pow_pos (by linarith : (0 : ℝ) < b) 3]
  nlinarith [mul_pos h key]

theorem existsUnique_root : ∃! u : ℝ, 1 / 2 < u ∧ u < 7 / 10 ∧ quintic u = 0 := by
  have hc : ContinuousOn quintic (Set.Icc (1 / 2) (7 / 10)) := by
    unfold quintic; fun_prop
  obtain ⟨u, hu, hu0⟩ := intermediate_value_Ioo (by norm_num) hc
    (show (0 : ℝ) ∈ Set.Ioo (quintic (1 / 2)) (quintic (7 / 10)) by
      simp only [quintic, Set.mem_Ioo]; norm_num)
  refine ⟨u, ⟨hu.1, hu.2, hu0⟩, fun v ⟨hv1, hv2, hv0⟩ => ?_⟩
  exact quintic_strictMonoOn.injOn ⟨hv1.le, hv2.le⟩ ⟨hu.1.le, hu.2.le⟩ (hv0.trans hu0.symm)

theorem conjecture_iff : Conjecture ↔ Attained ∧ UpperBound := by
  obtain ⟨u₀, ⟨h1, h2, h0⟩, huniq⟩ := existsUnique_root
  constructor
  · rintro ⟨u, hu1, hu2, hu0, hmem, hub⟩
    have hu : u = u₀ := huniq u ⟨hu1, hu2, hu0⟩
    subst hu
    refine ⟨fun v hv1 hv2 hv0 => ?_, fun v hv1 hv2 hv0 X hX => ?_⟩
    · rw [huniq v ⟨hv1, hv2, hv0⟩]; exact hmem
    · rw [huniq v ⟨hv1, hv2, hv0⟩]
      by_contra hne
      push Not at hne
      -- the minimum pairwise angle of X exceeds arccos u, contradicting maximality
      obtain ⟨p, hp⟩ : ∃ p : Fin 15 × Fin 15, p.1 ≠ p.2 ∧
          ∀ q : Fin 15 × Fin 15, q.1 ≠ q.2 → angle (X p.1) (X p.2) ≤ angle (X q.1) (X q.2) := by
        obtain ⟨p, hp, hmin⟩ := Set.Finite.exists_minimalFor
          (fun q : Fin 15 × Fin 15 => angle (X q.1) (X q.2)) {q | q.1 ≠ q.2} (Set.toFinite _)
          ⟨(0, 1), by decide⟩
        exact ⟨p, hp, fun q hq => by
          by_contra h
          push Not at h
          exact absurd (hmin hq h.le) (not_le.mpr h)⟩
      have hach : Achievable 15 (angle (X p.1) (X p.2)) :=
        ⟨X, hX, fun i j hij => hp.2 (i, j) hij⟩
      have := hub hach
      exact absurd (hne p.1 p.2 hp.1) (not_lt.mpr this)
  · rintro ⟨hatt, hup⟩
    refine ⟨u₀, h1, h2, h0, hatt u₀ h1 h2 h0, ?_⟩
    rintro d ⟨X, hX, hd⟩
    obtain ⟨i, j, hij, hle⟩ := hup u₀ h1 h2 h0 X hX
    exact (hd i j hij).trans hle

end Tammes15
