import Tammes15.Draw.Defs
import Tammes15.Trigrows.Sdist
import Tammes15.Vendor.EM8.RankinBound

/-!
# Setup of Section 3: `d_N` is attained, `d_15 < π/2`, and a maximal configuration with fewest
contacts

`contactCount X` is `E(X)`, the number of edges of the contact graph. The supremum of the
achievable separations is a maximum by compactness of `(S²)^N` (`exists_isGreatest_config`); a
maximal configuration has a contact (`exists_contact_of_isGreatest`); fifteen points always have
two at distance below `π/2` (`lt_pi_div_two_of_config15`, from Rankin's bound `rankin_six`:
at most six unit vectors of `ℝ³` have pairwise nonpositive inner products).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

/-- `E(X)`, the number of contacts of `X`. -/
noncomputable def contactCount {N : ℕ} {d : ℝ} (X : Config N d) : ℕ :=
  (contactGraph X).edgeSet.ncard

theorem contactGraph_adj_iff {N : ℕ} {d : ℝ} (X : Config N d) (i j : Fin N) :
    (contactGraph X).Adj i j ↔ i ≠ j ∧ sdist (X.pt i) (X.pt j) = d := by
  rw [contactGraph, SimpleGraph.fromRel_adj]
  simp [sdist_comm]

theorem achievable_iff_nonempty_config (N : ℕ) (d : ℝ) :
    Achievable N d ↔ Nonempty (Config N d) := by
  constructor
  · intro h
    rcases h with ⟨X, hX, hsep⟩
    refine ⟨{ pt := X, unit := hX, sep := ?_ }⟩
    intro i j hne
    have h := hsep i j hne
    have h_eq : sdist (X i) (X j) = angle (X i) (X j) := sdist_eq_angle (X i) (X j) (hX i) (hX j)
    linarith
  · intro h
    rcases h with ⟨Y⟩
    refine ⟨Y.pt, Y.unit, ?_⟩
    intro i j hne
    have h := Y.sep i j hne
    have h_eq : sdist (Y.pt i) (Y.pt j) = angle (Y.pt i) (Y.pt j) := sdist_eq_angle (Y.pt i) (Y.pt j) (Y.unit i) (Y.unit j)
    linarith

theorem config_le_pi {N : ℕ} (hN : 2 ≤ N) {d : ℝ} (X : Config N d) : d ≤ π := by
  have h0N : (0 : ℕ) < N := by omega
  have h1N : (1 : ℕ) < N := by omega
  let i₀ : Fin N := ⟨0, h0N⟩
  let i₁ : Fin N := ⟨1, h1N⟩
  have hne : i₀ ≠ i₁ := by
    intro h
    have hval : (0 : ℕ) = (1 : ℕ) := by simpa [i₀, i₁] using congrArg Fin.val h
    omega
  have hsep := X.sep i₀ i₁ hne
  have hsdist := sdist_mem_Icc (X.pt i₀) (X.pt i₁)
  rcases hsdist with ⟨_, hle⟩
  exact le_trans hsep hle

/-- `d_N` is attained (compactness of `(S²)^N`). -/
theorem exists_isGreatest_config (N : ℕ) (hN : 2 ≤ N) :
    ∃ dN : ℝ, IsGreatest {d | Nonempty (Config N d)} dN := by
  -- The set of distinct pairs of indices
  let P : Finset (Fin N × Fin N) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  have hP : P.Nonempty := by
    let i : Fin N := ⟨0, by omega⟩
    let j : Fin N := ⟨1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have hval := congrArg Fin.val h
      simp [i, j] at hval
    refine ⟨(i, j), ?_⟩
    simp [P, hij]
  -- The set of all N-tuples of unit vectors
  let K : Set (Fin N → E3) := Set.pi Set.univ (fun _ => Metric.sphere (0 : E3) 1)
  have hK : IsCompact K := by
    refine isCompact_univ_pi (fun i => ?_)
    exact isCompact_sphere (0 : E3) 1
  have hne : K.Nonempty := by
    refine ⟨fun _ => EuclideanSpace.single 0 1, ?_⟩
    intro i
    simp
  -- The function measuring the minimum pairwise distance
  let f : (Fin N → E3) → ℝ := fun Z => P.inf' hP (fun p => sdist (Z p.1) (Z p.2))
  have hf : ContinuousOn f K := by
    refine ContinuousOn.finset_inf'_apply hP (fun p hp => ?_)
    have h_cont : Continuous (fun (Z : Fin N → E3) => sdist (Z p.1) (Z p.2)) := by
      dsimp [sdist]
      have h_inner : Continuous (fun (Z : Fin N → E3) => ⟪Z p.1, Z p.2⟫) :=
        Continuous.inner (continuous_apply p.1) (continuous_apply p.2)
      exact Continuous.arccos h_inner
    exact h_cont.continuousOn
  -- Get the maximum of f on K
  obtain ⟨Z₀, hZ₀K, hZ₀max⟩ := IsCompact.exists_isMaxOn hK hne hf
  refine ⟨f Z₀, ?_⟩
  constructor
  · -- f Z₀ ∈ {d | Nonempty (Config N d)}
    refine ⟨Z₀, ?_, ?_⟩
    · -- unit: ∀ i, ‖Z₀ i‖ = 1
      intro i
      have hmem := hZ₀K i (Set.mem_univ i)
      rw [Metric.mem_sphere] at hmem
      simpa [dist_eq_norm] using hmem
    · -- sep: ∀ i j, i ≠ j → f Z₀ ≤ sdist (Z₀ i) (Z₀ j)
      intro i j hij
      have hmem : (i, j) ∈ P := by
        simp [P, hij]
      exact Finset.inf'_le (fun (p : Fin N × Fin N) => sdist (Z₀ p.1) (Z₀ p.2)) hmem
  · -- ∀ d ∈ {d | Nonempty (Config N d)}, d ≤ f Z₀
    intro d hd
    rcases hd with ⟨Y⟩
    -- Y : Config N d
    have hd_le_fY : d ≤ f Y.pt := by
      refine Finset.le_inf' hP (fun p => sdist (Y.pt p.1) (Y.pt p.2)) ?_
      intro p hp
      rcases p with ⟨i, j⟩
      simp [P] at hp
      exact Y.sep i j hp
    have hYptK : Y.pt ∈ K := by
      intro i hi
      have hnorm := Y.unit i
      rw [Metric.mem_sphere, dist_eq_norm]
      simpa using hnorm
    have hfY_le_fZ₀ : f Y.pt ≤ f Z₀ := hZ₀max hYptK
    exact le_trans hd_le_fY hfY_le_fZ₀

/-- A maximal configuration has a contact. -/
theorem exists_contact_of_isGreatest {N : ℕ} (hN : 2 ≤ N) {d : ℝ}
    (hmax : IsGreatest {d | Nonempty (Config N d)} d) (X : Config N d) :
    ∃ i j, i ≠ j ∧ sdist (X.pt i) (X.pt j) = d := by
  by_contra h
  push Not at h
  have hlt : ∀ i j, i ≠ j → d < sdist (X.pt i) (X.pt j) := by
    intro i j hij
    have hle := X.sep i j hij
    have hne := h i j hij
    exact lt_of_le_of_ne hle (Ne.symm hne)
  have h_one_lt_N : 1 < N := by omega
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have hi_ne : i0 ≠ i1 := by
    intro heq
    have : (0 : ℕ) = 1 := by simpa using congr_arg Fin.val heq
    omega
  let P := Finset.univ.filter (fun (p : Fin N × Fin N) => p.1 ≠ p.2)
  have hP : P.Nonempty := by
    refine ⟨(i0, i1), ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hi_ne⟩
  let d' := P.inf' hP (fun p => sdist (X.pt p.1) (X.pt p.2))
  have hd_lt_d' : d < d' := by
    rw [Finset.lt_inf'_iff hP]
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hp_ne⟩
    exact hlt p.1 p.2 hp_ne
  have hX_config : Config N d' :=
    ⟨X.pt, X.unit, fun i j hij => by
      have hmem : (i, j) ∈ P := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hij⟩
      have hle := Finset.inf'_le (fun p => sdist (X.pt p.1) (X.pt p.2)) hmem
      dsimp [d']
      exact hle⟩
  have hd'_le_d : d' ≤ d := hmax.2 ⟨hX_config⟩
  linarith

/-- Rankin's bound in dimension three (the eight-point repository proves it as
`Tammes15.Vendor.EM8.SquareAntiprismVerification.rankin_nonacute_bound`, RankinBound.lean). -/
theorem rankin_six {ι : Type*} [Fintype ι] (Y : ι → E3) (hY : ∀ i, ‖Y i‖ = 1)
    (hsep : ∀ i j, i ≠ j → ⟪Y i, Y j⟫ ≤ 0) : Fintype.card ι ≤ 6 := by
  exact Tammes15.Vendor.EM8.SquareAntiprismVerification.rankin_nonacute_bound Y hY hsep

theorem lt_pi_div_two_of_config15 {d : ℝ} (X : Config 15 d) : d < π / 2 := by
  by_contra! h
  have hd_nonneg : 0 ≤ d := by
    have hπpos : 0 < π := Real.pi_pos
    linarith
  have hd_le_pi : d ≤ π := config_le_pi (by norm_num) X
  have hcos_nonpos : cos d ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
  have h_inner : ∀ i j : Fin 15, i ≠ j → ⟪X.pt i, X.pt j⟫ ≤ 0 := by
    intro i j hne
    have hsep := X.sep i j hne
    have hle := (le_sdist_iff (X.pt i) (X.pt j) (X.unit i) (X.unit j) d ⟨hd_nonneg, hd_le_pi⟩).mp hsep
    linarith
  have hcard := rankin_six (X.pt) (X.unit) h_inner
  have hcard15 : Fintype.card (Fin 15) = 15 := Fintype.card_fin 15
  rw [hcard15] at hcard
  norm_num at hcard

/-- A configuration with fewest contacts among those at separation `d`. -/
theorem exists_min_contacts {N : ℕ} {d : ℝ} (h : Nonempty (Config N d)) :
    ∃ X : Config N d, ∀ Y : Config N d, contactCount X ≤ contactCount Y := by
  classical
    have h_nonempty : ∃ n : ℕ, ∃ X : Config N d, contactCount X = n := by
      rcases h with ⟨X⟩
      exact ⟨contactCount X, X, rfl⟩
    let n := Nat.find h_nonempty
    have hn : ∃ X : Config N d, contactCount X = n := Nat.find_spec h_nonempty
    rcases hn with ⟨X, hX⟩
    refine ⟨X, ?_⟩
    intro Y
    have hY : contactCount Y ∈ {m | ∃ X : Config N d, contactCount X = m} := ⟨Y, rfl⟩
    have hle : n ≤ contactCount Y := Nat.find_min' h_nonempty hY
    rw [hX]
    exact hle

end Tammes15
