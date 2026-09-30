import Tammes15.Draw.Frame
import Tammes15.Draw.Cyclic
import Tammes15.Draw.Exist

/-!
# The angular rotation system of a drawing and the angle sum at a vertex

For a graph drawn with unit vectors whose neighbour directions at each vertex are nonzero and
pairwise distinct (`DistinctDirs`), the counterclockwise successor at each vertex is a rotation
system (`exists_angular`), and for every angular rotation
system the corners at a vertex of degree at least two sum to `2π` (`corner_sum`). A
contact graph has distinct directions (`distinctDirs_contact`). The construction follows the
eight-point drawing layer (`contactRotate`, `contactRotateAt_angle_sum` of
github.com/lukasliehr/Energy-Minimization-8-Points at 50d14bc, LeanCode/LargeS/Lean_Code/
RotationSystem.lean), rewritten for a general graph in the frame coordinates of
`Tammes15.Draw.Frame`.
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Neighbour directions at every vertex are nonzero and pairwise distinct. -/
def DistinctDirs (G : SimpleGraph V) (x : V → E3) : Prop :=
  (∀ v w, G.Adj v w → tdir (x v) (x w) ≠ 0) ∧
    ∀ v a b, G.Adj v a → G.Adj v b → a ≠ b → ocorner (x v) (x a) (x b) ≠ 0

/-- Iterates of a vertex-preserving permutation of darts stay at the vertex. -/
theorem rot_pow_fst (R : RotSys G) (e : G.Dart) (n : ℕ) : ((R.rot ^ n) e).fst = e.fst := by
  induction' n with k ih
  · simp
  · rw [pow_succ', Equiv.Perm.mul_apply, R.rot_fst, ih]

/-- At a vertex with two distinct neighbours no dart is fixed by the rotation. -/
theorem rot_ne_self (R : RotSys G) (e : G.Dart) (a b : V) (hab : a ≠ b) (ha : G.Adj e.fst a)
    (hb : G.Adj e.fst b) : R.rot e ≠ e := by
  intro h
  have hzpow : ∀ k : ℤ, (R.rot ^ k) e = e :=
    Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h
  set fa : G.Dart := ⟨(e.fst, a), ha⟩ with hfa
  set fb : G.Dart := ⟨(e.fst, b), hb⟩ with hfb
  have hcycle_fa : R.rot.SameCycle e fa := R.rot_cycle e fa rfl
  have hcycle_fb : R.rot.SameCycle e fb := R.rot_cycle e fb rfl
  rcases hcycle_fa with ⟨kfa, hkfa⟩
  rcases hcycle_fb with ⟨kfb, hkfb⟩
  have heq_fa : e = fa := by
    rw [hzpow kfa] at hkfa
    exact hkfa
  have heq_fb : e = fb := by
    rw [hzpow kfb] at hkfb
    exact hkfb
  have h_ab : a = b := by
    calc
      a = fa.snd := by rfl
      _ = e.snd := by rw [heq_fa]
      _ = fb.snd := by rw [heq_fb]
      _ = b := by rfl
  exact hab h_ab

/-- A dart fixed by the rotation is the only dart at its vertex. -/
theorem eq_of_rot_eq_self (R : RotSys G) (e f : G.Dart) (hf : f.fst = e.fst) (he : R.rot e = e) :
    f = e := by
  have h_cycle : R.rot.SameCycle e f := R.rot_cycle (G := G) e f hf.symm
  rcases h_cycle with ⟨k, hk⟩
  have hk' : (R.rot ^ k) e = e := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self he k
  rw [hk'] at hk
  exact hk.symm

/-- A rotation system from a permutation of the neighbours of each vertex whose every two
elements are in one cycle. -/
theorem exists_rotSys_of_local (σ : ∀ v, Equiv.Perm {w // G.Adj v w})
    (hσ : ∀ v a b, (σ v).SameCycle a b) :
    ∃ R : RotSys G, ∀ e : G.Dart, (R.rot e).snd = (σ e.fst ⟨e.snd, e.adj⟩).1 := by
  -- Equivalence between darts and Σ v, {w // G.Adj v w}
  let E : G.Dart ≃ Σ v, {w // G.Adj v w} :=
    { toFun := λ e => ⟨e.fst, ⟨e.snd, e.adj⟩⟩
      invFun := λ p => ⟨(p.1, p.2.1), p.2.2⟩
      left_inv := by
        intro e
        ext <;> rfl
      right_inv := by
        intro p
        rfl }
  -- Build the rotation system
  let f : Equiv.Perm (Σ v, {w // G.Adj v w}) := Equiv.sigmaCongrRight σ
  let rot : Equiv.Perm G.Dart := (E.trans f).trans E.symm
  have h_rot_fst : ∀ x : G.Dart, (rot x).fst = x.fst := by
    intro x
    simp [rot, E, f]
  have h_snd_eq : ∀ e : G.Dart, (rot e).snd = (σ e.fst ⟨e.snd, e.adj⟩).1 := by
    intro e
    simp [rot, E, f]
  have h_rot_apply : ∀ y, E (rot y) = f (E y) := by
    intro y
    simp [rot, E, f]
  have h_pow_eq : ∀ (n : ℕ) (x : G.Dart), (rot ^ n) x = E.symm ((f ^ n) (E x)) := by
    intro n
    induction' n with k ih
    · intro x; rfl
    · intro x
      rw [pow_succ, pow_succ]
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      rw [ih (rot x)]
      rw [h_rot_apply x]
  -- Lemma: f ^ n applied to E x
  have h_f_pow : ∀ (n : ℕ) (x : G.Dart), (f ^ n) (E x) = ⟨x.fst, ((σ x.fst) ^ n) ⟨x.snd, x.adj⟩⟩ := by
    intro n
    induction' n with k ih
    · intro x; rfl
    · intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      rw [ih x]
      simp [f, E, Equiv.sigmaCongrRight_apply]
      rw [pow_succ', Equiv.Perm.mul_apply]
  have h_rot_cycle : ∀ x y : G.Dart, x.fst = y.fst → rot.SameCycle x y := by
    intro x y hxy
    -- Transport the adjacency proof across the equality
    have hadj : G.Adj x.fst y.snd := hxy ▸ y.adj
    -- hσ gives that σ x.fst is in the same cycle
    have h_cycle_sigma : (σ x.fst).SameCycle ⟨x.snd, x.adj⟩ ⟨y.snd, hadj⟩ :=
      hσ x.fst ⟨x.snd, x.adj⟩ ⟨y.snd, hadj⟩
    -- On a finite type, SameCycle gives a finite power
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h_cycle_sigma
    -- (rot ^ n) x = y
    have h_pow : (rot ^ n) x = y := by
      rw [h_pow_eq n x]
      rw [h_f_pow n x]
      -- Now we have E.symm ⟨x.fst, ((σ x.fst) ^ n) ⟨x.snd, x.adj⟩⟩
      -- and hn : ((σ x.fst) ^ n) ⟨x.snd, x.adj⟩ = ⟨y.snd, hadj⟩
      rw [hn]
      -- E.symm ⟨x.fst, ⟨y.snd, hadj⟩⟩ = y
      dsimp [E]
      ext
      · simp [hxy]
      · simp
    -- Convert to SameCycle with ℤ exponent
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    exact h_pow
  refine ⟨{ rot := rot, rot_fst := h_rot_fst, rot_cycle := h_rot_cycle }, h_snd_eq⟩

/-- The angular rotation system exists. -/
theorem exists_angular [DecidableRel G.Adj] (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hD : DistinctDirs G x) : ∃ R : RotSys G, IsAngular R x := by
  -- For each v, choose a unit vector ev v orthogonal to x v
  have hev : ∀ v, ∃ e : E3, ‖e‖ = 1 ∧ ⟪x v, e⟫ = 0 := by
    intro v
    exact exists_unit_orthogonal (x v)
  let ev : V → E3 := fun v => Classical.choose (hev v)
  have hev_spec : ∀ v, ‖ev v‖ = 1 ∧ ⟪x v, ev v⟫ = 0 := by
    intro v
    exact Classical.choose_spec (hev v)
  -- Define φ v w = fangle (x v) (ev v) (x w.1) for w : {w // G.Adj v w}
  let φ := fun (v : V) (w : {w // G.Adj v w}) => fangle (x v) (ev v) (x w.1)
  -- φ values lie in [0, 2π)
  have hφ_range : ∀ v w, 0 ≤ φ v w ∧ φ v w < 2 * π := by
    intro v w
    dsimp [φ, fangle]
    have hmem := toIcoMod_mem_Ico Real.two_pi_pos 0 (Complex.arg (tcoord (x v) (ev v) (x w.1)))
    rcases hmem with ⟨hleft, hright⟩
    exact ⟨hleft, by simpa [add_zero] using hright⟩
  -- φ is injective at each vertex
  have hφ_inj : ∀ v, Function.Injective (φ v) := by
    intro v a b h
    by_contra hne
    have hne' : a.1 ≠ b.1 := by
      intro h
      apply hne
      exact Subtype.ext h
    apply hD.2 v a.1 b.1 a.2 b.2 hne'
    -- Show: occurs (x v) (x a.1) (x b.1) = 0
    have h_ocorner : ocorner (x v) (x a.1) (x b.1) =
        toIcoMod Real.two_pi_pos 0 (fangle (x v) (ev v) (x b.1) - fangle (x v) (ev v) (x a.1)) := by
      apply ocorner_eq_fangle_sub (x v) (ev v) (x a.1) (x b.1) (hx v) (hev_spec v).1 (hev_spec v).2
      · exact hD.1 v a.1 a.2
      · exact hD.1 v b.1 b.2
    rw [h_ocorner]
    dsimp [φ] at h
    rw [h, sub_self]
    -- toIcoMod two_pi_pos 0 0 = 0
    simpa using toIcoMod_apply_left Real.two_pi_pos (0 : ℝ)
  -- For each v, get a cyclic ordering σ v using exists_cyclic_succ
  have h_exists_σ : ∀ v, ∃ σ : Equiv.Perm {w // G.Adj v w}, (∀ a b, σ.SameCycle a b) ∧
      ∀ a b, b ≠ a → toIcoMod Real.two_pi_pos 0 (φ v (σ a) - φ v a) ≤
        toIcoMod Real.two_pi_pos 0 (φ v b - φ v a) := by
    intro v
    apply exists_cyclic_succ (φ v) (hφ_inj v) (hφ_range v)
  choose σ hσ_cycle hσ_min using h_exists_σ
  -- Get rotation system R using exists_rotSys_of_local
  have h_exists_R : ∃ R : RotSys G, ∀ e : G.Dart, (R.rot e).snd = (σ e.fst ⟨e.snd, e.adj⟩).1 := by
    apply exists_rotSys_of_local σ (fun v a b => hσ_cycle v a b)
  rcases h_exists_R with ⟨R, hR⟩
  -- Show IsAngular R x
  refine ⟨R, ?_⟩
  intro e f hf_eq hf_ne
  -- From hR: (R.rot e).snd = (σ e.fst ⟨e.snd, e.adj⟩).1
  have hR_e : (R.rot e).snd = (σ e.fst ⟨e.snd, e.adj⟩).1 := hR e
  -- f.snd is adjacent to e.fst (since f.adj : G.Adj f.fst f.snd and f.fst = e.fst)
  have hf_adj' : G.Adj e.fst f.snd := by
    rw [← hf_eq]
    exact f.adj
  let a : {w // G.Adj e.fst w} := ⟨e.snd, e.adj⟩
  let b : {w // G.Adj e.fst w} := ⟨f.snd, hf_adj'⟩
  have hb_ne_a : b ≠ a := by
    intro h_eq
    apply hf_ne
    -- need to show f = e
    have h_snd : f.snd = e.snd := by
      have := congr_arg Subtype.val h_eq
      exact this
    apply SimpleGraph.Dart.ext f e
    ext <;> assumption
  -- The minimality clause for σ
  have h_min := hσ_min e.fst a b hb_ne_a
  -- Compute ocorner (x e.fst) (x e.snd) (x (R.rot e).snd)
  have h_occur_R : ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) =
      toIcoMod Real.two_pi_pos 0 (fangle (x e.fst) (ev e.fst) (x (R.rot e).snd) -
        fangle (x e.fst) (ev e.fst) (x e.snd)) := by
    apply ocorner_eq_fangle_sub (x e.fst) (ev e.fst) (x e.snd) (x (R.rot e).snd)
      (hx e.fst) (hev_spec e.fst).1 (hev_spec e.fst).2
    · exact hD.1 e.fst e.snd e.adj
    · have h_adj : G.Adj (R.rot e).fst (R.rot e).snd := (R.rot e).adj
      rw [R.rot_fst e] at h_adj
      exact hD.1 e.fst (R.rot e).snd h_adj
  -- Compute occurs (x e.fst) (x e.snd) (x f.snd)
  have h_occur_f : ocorner (x e.fst) (x e.snd) (x f.snd) =
      toIcoMod Real.two_pi_pos 0 (fangle (x e.fst) (ev e.fst) (x f.snd) -
        fangle (x e.fst) (ev e.fst) (x e.snd)) := by
    refine ocorner_eq_fangle_sub (x e.fst) (ev e.fst) (x e.snd) (x f.snd)
      (hx e.fst) (hev_spec e.fst).1 (hev_spec e.fst).2 ?_ ?_
    · exact hD.1 e.fst e.snd e.adj
    · rw [← hf_eq]
      exact hD.1 f.fst f.snd f.adj
  -- Rewrite the goal using these equalities
  rw [h_occur_R, h_occur_f]
  -- Compute the φ expressions
  have h_φσ : φ e.fst (σ e.fst a) = fangle (x e.fst) (ev e.fst) (x (R.rot e).snd) := by
    dsimp [φ]
    rw [← hR_e]
  have h_φa : φ e.fst a = fangle (x e.fst) (ev e.fst) (x e.snd) := rfl
  have h_φb : φ e.fst b = fangle (x e.fst) (ev e.fst) (x f.snd) := rfl
  -- Now the goal is exactly h_min
  simpa [h_φσ, h_φa, h_φb] using h_min

/-- The corners at a vertex with two distinct neighbours sum to `2π`. -/
theorem corner_sum [DecidableRel G.Adj] (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hD : DistinctDirs G x) (R : RotSys G) (hR : IsAngular R x) (v : V)
    (hv : ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b) :
    ∑ e ∈ Finset.univ.filter (fun e : G.Dart => e.fst = v),
      ocorner (x v) (x e.snd) (x (R.rot e).snd) = 2 * π := by
  obtain ⟨e₀, he₀_norm, he₀_orth⟩ := exists_unit_orthogonal (x v)
  have hx_v_norm : ‖x v‖ = 1 := hx v
  have hD1 : ∀ v' w, G.Adj v' w → tdir (x v') (x w) ≠ 0 := hD.1
  have hD2 : ∀ v' a b, G.Adj v' a → G.Adj v' b → a ≠ b → ocorner (x v') (x a) (x b) ≠ 0 := hD.2
  let α := {e : G.Dart // e.fst = v}
  have hα_nonempty : Nonempty α := by
    obtain ⟨a, b, hne, ha, hb⟩ := hv
    refine ⟨⟨⟨(v, a), ha⟩, rfl⟩⟩
  let σ : Equiv.Perm α := Equiv.Perm.subtypePerm R.rot (fun e => by
    have := R.rot_fst e
    simp [this])
  let φ : α → ℝ := fun f => fangle (x v) e₀ (x f.1.snd)
  have hφ_inj : Function.Injective φ := by
    intro f g h
    dsimp [φ] at h
    by_contra hne
    have hne' : f.1 ≠ g.1 := by
      intro heq
      apply hne
      exact Subtype.ext heq
    have hsnd_ne : f.1.snd ≠ g.1.snd := by
      intro heq
      apply hne'
      apply SimpleGraph.Dart.ext f.1 g.1
      apply Prod.ext
      · simpa [f.2, g.2]
      · exact heq
    have h_adj_f' : G.Adj f.1.fst f.1.snd := f.1.adj
    have h_adj_g' : G.Adj g.1.fst g.1.snd := g.1.adj
    have h_adj_f : G.Adj v f.1.snd := by simpa [f.2] using h_adj_f'
    have h_adj_g : G.Adj v g.1.snd := by simpa [g.2] using h_adj_g'
    have h_occ_eq_zero : ocorner (x v) (x f.1.snd) (x g.1.snd) = 0 := by
      have hpos_f : tdir (x v) (x f.1.snd) ≠ 0 := hD1 v f.1.snd h_adj_f
      have hpos_g : tdir (x v) (x g.1.snd) ≠ 0 := hD1 v g.1.snd h_adj_g
      have h_eq := ocorner_eq_fangle_sub (x v) e₀ (x f.1.snd) (x g.1.snd) hx_v_norm he₀_norm he₀_orth hpos_f hpos_g
      rw [h] at h_eq
      simpa [toIcoMod_apply_left two_pi_pos (0 : ℝ)] using h_eq
    have h_occ_ne_zero : ocorner (x v) (x f.1.snd) (x g.1.snd) ≠ 0 :=
      hD2 v f.1.snd g.1.snd h_adj_f h_adj_g hsnd_ne
    exact h_occ_ne_zero h_occ_eq_zero
  have hφ_range : ∀ f : α, 0 ≤ φ f ∧ φ f < 2 * π := by
    intro f
    dsimp [φ, fangle]
    have hmem := toIcoMod_mem_Ico two_pi_pos (0 : ℝ) (Complex.arg (tcoord (x v) e₀ (x f.1.snd)))
    rcases hmem with ⟨hle, hlt⟩
    have hlt' : toIcoMod two_pi_pos (0 : ℝ) (Complex.arg (tcoord (x v) e₀ (x f.1.snd))) < 2 * π := by
      simpa [zero_add] using hlt
    exact ⟨hle, hlt'⟩
  have hσ_fix : ∀ f : α, σ f ≠ f := by
    intro f
    obtain ⟨a, b, hne, ha, hb⟩ := hv
    have h_adj_f' : G.Adj f.1.fst f.1.snd := f.1.adj
    have h_rot_ne : R.rot f.1 ≠ f.1 :=
      rot_ne_self R f.1 a b hne (by simpa [f.2] using ha) (by simpa [f.2] using hb)
    intro heq
    apply h_rot_ne
    have : (σ f).1 = f.1 := by
      simpa [σ, Equiv.Perm.subtypePerm] using congr_arg Subtype.val heq
    exact this
  have hmin : ∀ a b : α, b ≠ a → toIcoMod two_pi_pos (0 : ℝ) (φ (σ a) - φ a) ≤ toIcoMod two_pi_pos (0 : ℝ) (φ b - φ a) := by
    intro a b hne
    have ha_fst : a.1.fst = v := a.2
    have hb_fst : b.1.fst = v := b.2
    have h_adj_a' : G.Adj a.1.fst a.1.snd := a.1.adj
    have h_adj_b' : G.Adj b.1.fst b.1.snd := b.1.adj
    have hR' := hR a.1 b.1 (by simpa [ha_fst, hb_fst] using rfl) (by
      intro heq
      apply hne
      exact Subtype.ext heq)
    have hpos_a : tdir (x v) (x a.1.snd) ≠ 0 := by
      apply hD1 v a.1.snd
      simpa [ha_fst] using h_adj_a'
    have hpos_b : tdir (x v) (x b.1.snd) ≠ 0 := by
      apply hD1 v b.1.snd
      simpa [hb_fst] using h_adj_b'
    have hpos_rot : tdir (x v) (x (R.rot a.1).snd) ≠ 0 := by
      have h_adj_rot' : G.Adj (R.rot a.1).fst (R.rot a.1).snd := (R.rot a.1).adj
      have h_adj_rot : G.Adj v (R.rot a.1).snd := by
        simpa [R.rot_fst a.1, a.2] using h_adj_rot'
      exact hD1 v (R.rot a.1).snd h_adj_rot
    have h_eq_a := ocorner_eq_fangle_sub (x v) e₀ (x a.1.snd) (x (R.rot a.1).snd) hx_v_norm he₀_norm he₀_orth hpos_a hpos_rot
    have h_eq_b := ocorner_eq_fangle_sub (x v) e₀ (x a.1.snd) (x b.1.snd) hx_v_norm he₀_norm he₀_orth hpos_a hpos_b
    have hR'' : ocorner (x v) (x a.1.snd) (x (R.rot a.1).snd) ≤ ocorner (x v) (x a.1.snd) (x b.1.snd) := by
      simpa [ha_fst] using hR'
    rw [h_eq_a, h_eq_b] at hR''
    simpa [σ, Equiv.Perm.subtypePerm, φ] using hR''
  have hsum := sum_cyclic_succ φ hφ_inj hφ_range σ hσ_fix hmin
  have hterm : ∀ f : α, toIcoMod two_pi_pos (0 : ℝ) (φ (σ f) - φ f) = ocorner (x v) (x f.1.snd) (x (R.rot f.1).snd) := by
    intro f
    have h_adj_f' : G.Adj f.1.fst f.1.snd := f.1.adj
    have h_adj_rot' : G.Adj (R.rot f.1).fst (R.rot f.1).snd := (R.rot f.1).adj
    have h_adj_rot : G.Adj v (R.rot f.1).snd := by
      simpa [R.rot_fst f.1, f.2] using h_adj_rot'
    have hpos_f : tdir (x v) (x f.1.snd) ≠ 0 := hD1 v f.1.snd (by simpa [f.2] using h_adj_f')
    have hpos_rot : tdir (x v) (x (R.rot f.1).snd) ≠ 0 := hD1 v (R.rot f.1).snd h_adj_rot
    have h_eq := ocorner_eq_fangle_sub (x v) e₀ (x f.1.snd) (x (R.rot f.1).snd) hx_v_norm he₀_norm he₀_orth hpos_f hpos_rot
    dsimp [φ, σ, Equiv.Perm.subtypePerm] at h_eq ⊢
    simpa using h_eq.symm
  have hsum' : ∑ f : α, ocorner (x v) (x f.1.snd) (x (R.rot f.1).snd) = 2 * π := by
    simpa [hterm] using hsum
  let s := Finset.univ.filter (fun e : G.Dart => e.fst = v)
  have hs : ∀ e : G.Dart, e ∈ s ↔ e.fst = v := by
    intro e
    simp [s]
  calc
    ∑ e ∈ Finset.univ.filter (fun e : G.Dart => e.fst = v), ocorner (x v) (x e.snd) (x (R.rot e).snd)
        = ∑ e ∈ s, ocorner (x v) (x e.snd) (x (R.rot e).snd) := by rfl
    _ = ∑ f : α, ocorner (x v) (x f.1.snd) (x (R.rot f.1).snd) := by
      rw [Finset.sum_subtype s hs (fun e => ocorner (x v) (x e.snd) (x (R.rot e).snd))]
    _ = 2 * π := hsum'

/-- Distinct neighbour directions from the separation of a drawing with edges of length `d`. -/
theorem distinctDirs_of_sep {d : ℝ} (hd : 0 < d ∧ d < π) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hsep : ∀ a b, a ≠ b → d ≤ sdist (x a) (x b))
    (hG : ∀ a b, G.Adj a b → sdist (x a) (x b) = d) : DistinctDirs G x := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hsin : 0 < sin d := Real.sin_pos_of_pos_of_lt_pi hdpos hdlt
  have htd : ∀ v w, G.Adj v w → tdir (x v) (x w) ≠ 0 := by
    intro v w h h0
    have hn := tdir_norm (x v) (x w) (hx v) (hx w)
    rw [hG v w h, h0, norm_zero] at hn
    linarith
  refine ⟨htd, fun v a b ha hb hne h0 => ?_⟩
  have hcos : ⟪x v, x a⟫ = ⟪x v, x b⟫ := by
    rw [← cos_sdist _ _ (hx v) (hx a), ← cos_sdist _ _ (hx v) (hx b), hG v a ha, hG v b hb]
  have heq := eq_of_ocorner_eq_zero (x v) (x a) (x b) (hx v) (hx a) (hx b) hcos (htd v a ha) h0
  have h := hsep a b hne
  rw [heq, sdist_self _ (hx b)] at h
  linarith

/-- A contact graph, and any graph mapped into it, has distinct neighbour directions. -/
theorem distinctDirs_contact {N : ℕ} {d : ℝ} (hd : 0 < d ∧ d < π) (X : Config N d)
    (emb : V ↪ Fin N) (hG : ∀ a b, G.Adj a b → (contactGraph X).Adj (emb a) (emb b)) :
    DistinctDirs G (X.pt ∘ emb) :=
  distinctDirs_of_sep hd (X.pt ∘ emb) (fun _ => X.unit _)
    (fun _ _ h => X.sep _ _ (emb.injective.ne h))
    (fun a b h => ((contactGraph_adj_iff X _ _).mp (hG a b h)).2)

/-- The angle sum at a vertex in the form that TwoConn uses: every corner of
the angular rotation system is positive. -/
theorem angular_corner_sum [DecidableRel G.Adj] (R : RotSys G) (x : V → E3)
    (hx : ∀ v, ‖x v‖ = 1) (hR : IsAngular R x)
    (hpos : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd))
    (v : V) (hv : ∃ w, G.Adj v w) :
    ∑ e ∈ Finset.univ.filter (fun e : G.Dart => e.fst = v),
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) = 2 * π := by
  have htd : ∀ u w, G.Adj u w → tdir (x u) (x w) ≠ 0 := by
    intro u w h h0
    have h1 : 0 < ocorner (x u) (x w) _ := hpos ⟨(u, w), h⟩
    rw [ocorner_of_tdir_eq_zero _ _ _ h0] at h1
    exact lt_irrefl _ h1
  have hD : DistinctDirs G x := by
    refine ⟨htd, fun u a b ha hb hab h0 => ?_⟩
    have h1 : ocorner (x u) (x a) _ ≤ ocorner (x u) (x a) (x b) :=
      hR ⟨(u, a), ha⟩ ⟨(u, b), hb⟩ rfl
        (fun h => hab (congrArg (fun e : G.Dart => e.snd) h).symm)
    have h2 : 0 < ocorner (x u) (x a) _ := hpos ⟨(u, a), ha⟩
    linarith
  obtain ⟨w, hw⟩ := hv
  let e0 : G.Dart := ⟨(v, w), hw⟩
  have hfst : (R.rot e0).fst = v := R.rot_fst e0
  have hne : (R.rot e0).snd ≠ w := by
    intro h
    have h1 := hpos e0
    have hr : R.rot e0 = e0 := SimpleGraph.Dart.ext _ _ (Prod.ext hfst h)
    rw [hr, ocorner_self] at h1
    exact lt_irrefl _ h1
  have hadj : G.Adj v (R.rot e0).snd := hfst ▸ (R.rot e0).adj
  rw [← corner_sum x hx hD R hR v ⟨w, (R.rot e0).snd, hne.symm, hw, hadj⟩]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [(Finset.mem_filter.mp he).2]

end Tammes15
