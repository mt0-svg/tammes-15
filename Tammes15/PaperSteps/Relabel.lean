import Tammes15.PaperSteps.Defs

/-!
# Step (i) of the proof of Lemma B.7: another choice of hexagons for the same set

Two choices `H`, `H₀` of the same set of hexagons differ by a bijection `σ` of the free points and,
for each hexagon, a cyclic shift `s m` of its corners: `H.base m = face^(s m) (H₀.base (σ m))`
(`exists_shift_data`). An assignment satisfying the relation system for `H` gives one for `H₀`
(`relSys_relabel`), the wheel relations being invariant under a shift of the indices
(`wheelRel_shift`); a gluing for `H₀` gives a gluing for `H` with the same points, up to the
relabelling (`glueY_relabel`), and Pair and Local do not see the labels (`pairFires_of_equiv`,
`localFires_of_equiv`).
-/

open Real Matrix
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15

open scoped Classical

variable {P : PlaneGraph} {k : ℕ}

/-- A dart in the face cycle of a dart `y` of a hexagon is `face^s y` for some `s < 6`. -/
theorem exists_shift {x y : P.G.Dart} (hy : Function.minimalPeriod P.R.face y = 6)
    (h : P.R.face.SameCycle x y) : ∃ s : Fin 6, x = (P.R.face ^ (s : ℕ)) y := by
  have h_symm : P.R.face.SameCycle y x := (Equiv.Perm.sameCycle_comm.mp h)
  obtain ⟨i, hi⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h_symm
  have h_period : (P.R.face : P.G.Dart → P.G.Dart)^[i % 6] y = (P.R.face : P.G.Dart → P.G.Dart)^[i] y := by
    calc
      (P.R.face : P.G.Dart → P.G.Dart)^[i % 6] y = (P.R.face : P.G.Dart → P.G.Dart)^[i % Function.minimalPeriod P.R.face y] y := by rw [hy]
      _ = (P.R.face : P.G.Dart → P.G.Dart)^[i] y := Function.iterate_mod_minimalPeriod_eq
  have h_eq : (P.R.face ^ (i % 6)) y = x := by
    calc
      (P.R.face ^ (i % 6)) y = ((P.R.face : P.G.Dart → P.G.Dart)^[i % 6]) y := by simp [Equiv.Perm.coe_pow]
      _ = ((P.R.face : P.G.Dart → P.G.Dart)^[i]) y := h_period
      _ = (P.R.face ^ i) y := by simp [Equiv.Perm.coe_pow]
      _ = x := hi
  refine ⟨⟨i % 6, Nat.mod_lt i (by norm_num)⟩, ?_⟩
  simpa using h_eq.symm

/-- The powers of the face permutation on a hexagon add modulo 6. -/
theorem face_pow_add_fin {y : P.G.Dart} (hy : Function.minimalPeriod P.R.face y = 6)
    (i s : Fin 6) :
    (P.R.face ^ ((i + s : Fin 6) : ℕ)) y = (P.R.face ^ (i : ℕ)) ((P.R.face ^ (s : ℕ)) y) := by
  -- (f ^ i) ((f ^ s) y) = (f ^ i * f ^ s) y = (f ^ (i + s)) y
  have hRHS : (P.R.face ^ (i : ℕ)) ((P.R.face ^ (s : ℕ)) y) = (P.R.face ^ ((i : ℕ) + (s : ℕ))) y := by
    calc
      (P.R.face ^ (i : ℕ)) ((P.R.face ^ (s : ℕ)) y) = ((P.R.face ^ (i : ℕ)) * (P.R.face ^ (s : ℕ))) y := by
        rw [Equiv.Perm.mul_apply]
      _ = (P.R.face ^ ((i : ℕ) + (s : ℕ))) y := by rw [pow_add]
  rw [hRHS]
  -- ((i + s : Fin 6) : ℕ) = ((i : ℕ) + (s : ℕ)) % 6
  have h_fin_add : ((i + s : Fin 6) : ℕ) = ((i : ℕ) + (s : ℕ)) % 6 := by
    simpa using Fin.val_add i s
  rw [h_fin_add]
  -- Convert permutation powers to function iterates and apply the period lemma
  simp_rw [Equiv.Perm.coe_pow]
  have h_iter := Function.iterate_mod_minimalPeriod_eq (f := P.R.face) (x := y) (n := (i : ℕ) + (s : ℕ))
  rw [hy] at h_iter
  simpa using h_iter

/-- The relabelling data of two choices of the same set of hexagons. -/
theorem exists_shift_data {H H₀ : HexChoice P k} (h : SameHexSet H H₀) :
    ∃ σ : Fin k ≃ Fin k, ∃ s : Fin k → Fin 6,
      ∀ m, H.base m = (P.R.face ^ (s m : ℕ)) (H₀.base (σ m)) := by
  rcases h with ⟨σ, h_cycle⟩
  have h_exists : ∀ m, ∃ s : Fin 6, H.base m = (P.R.face ^ (s : ℕ)) (H₀.base (σ m)) := by
    intro m
    exact exists_shift (H₀.hex (σ m)) (h_cycle m)
  choose s h_s using h_exists
  exact ⟨σ, s, h_s⟩

/-- (T8) is invariant under a cyclic shift of the indices of the hexagon. -/
theorem wheelRel_shift {d : ℝ} {u r : Fin 6 → ℝ} (s : Fin 6) (h : WheelRel d u r) :
    WheelRel d (fun j => u (j + s)) (fun j => r (j + s)) := by
  rcases h with ⟨hr, heta1, hsum, heta2, hu⟩
  have h_add : ∀ (j s : Fin 6), (j + 1) + s = (j + s) + 1 := by
    intro j s; abel
  have h_sub : ∀ (j s : Fin 6), (j - 1) + s = (j + s) - 1 := by
    intro j s; abel
  have hsum' : ∑ j : Fin 6, gam d (r (j + s)) (r ((j + s) + 1)) = 2 * π := by
    calc
      ∑ j : Fin 6, gam d (r (j + s)) (r ((j + s) + 1)) = ∑ j : Fin 6, gam d (r j) (r (j + 1)) :=
        Fintype.sum_equiv (Equiv.addRight s)
          (fun k => gam d (r (k + s)) (r ((k + s) + 1)))
          (fun k => gam d (r k) (r (k + 1)))
          (fun _ => rfl)
      _ = 2 * π := hsum
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j; simp; exact hr (j + s)
  · intro j; simp; simpa [h_add] using heta1 (j + s)
  · simpa [h_add] using hsum'
  · intro j; simp; simpa [h_add, h_sub] using heta2 (j + s)
  · intro j; simp; simpa [h_add, h_sub] using hu (j + s)

/-- The assignment for `H₀` read from an assignment for `H`: the same `d` and corners, and the
distances of the free point `m₀ = σ m` to the corners `A_j` of `H₀`, which are the corners
`A_{j - s m}` of `H`. -/
def relabelAssign (A : Assign P k) (σ : Fin k ≃ Fin k) (s : Fin k → Fin 6) : Assign P k where
  d := A.d
  corner := A.corner
  r m₀ j := A.r (σ.symm m₀) (j - s (σ.symm m₀))

/-- An assignment satisfying the relation system for `H` gives one for `H₀`. -/
theorem relSys_relabel {H H₀ : HexChoice P k} {A : Assign P k} (σ : Fin k ≃ Fin k)
    (s : Fin k → Fin 6) (hs : ∀ m, H.base m = (P.R.face ^ (s m : ℕ)) (H₀.base (σ m)))
    (hR : RelSys P H A) : RelSys P H₀ (relabelAssign A σ s) := by
  refine {
    corner_mem := hR.corner_mem
    vertex_sum := hR.vertex_sum
    tri := hR.tri
    rhombus := hR.rhombus
    pent := hR.pent
    hex := hR.hex
    hexDiag := hR.hexDiag
    wheel := by
      intro m₀
      set m := σ.symm m₀ with hm
      have hbase : H.base m = (P.R.face ^ (s m : ℕ)) (H₀.base m₀) := by
        calc
          H.base m = H.base (σ.symm m₀) := by rw [hm]
          _ = (P.R.face ^ (s (σ.symm m₀) : ℕ)) (H₀.base (σ (σ.symm m₀))) := by rw [hs]
          _ = (P.R.face ^ (s m : ℕ)) (H₀.base m₀) := by rw [hm, Equiv.apply_symm_apply]
      have hw := hR.wheel m
      have hw_shift := wheelRel_shift ((-(s m) : Fin 6)) hw
      -- hw_shift : WheelRel A.d (fun j => A.fc (H.base m) ↑(j + -(s m))) (fun j => A.r m (j + -(s m)))
      have h_fc_eq (j : Fin 6) : A.fc (H.base m) ↑(j + -(s m)) = A.corner ((P.R.face ^ (j : ℕ)) (H₀.base m₀)) := by
        dsimp [Assign.fc]
        rw [hbase]
        rw [← face_pow_add_fin (H₀.hex m₀) (j + (-(s m))) (s m)]
        have h_add : (j + (-(s m))) + s m = j := by simp
        rw [h_add]
      have hw_final : WheelRel A.d (fun (j : Fin 6) => A.corner ((P.R.face ^ (j : ℕ)) (H₀.base m₀))) (fun j => A.r m (j + -(s m))) := by
        have h_funext : (fun (j : Fin 6) => A.fc (H.base m) ↑(j + -(s m))) = (fun (j : Fin 6) => A.corner ((P.R.face ^ (j : ℕ)) (H₀.base m₀))) := by
          refine funext ?_
          intro j
          exact h_fc_eq j
        rw [h_funext] at hw_shift
        exact hw_shift
      -- Now rewrite the second component: j + -(s m) = j - s m in Fin 6
      have h_r_eq : (fun (j : Fin 6) => A.r m (j + -(s m))) = (fun (j : Fin 6) => A.r m (j - s m)) := by
        refine funext ?_
        intro j
        rw [sub_eq_add_neg]
      rw [h_r_eq] at hw_final
      -- The goal is definitionally equal to hw_final
      exact hw_final
  }

/-- The gluing for `H` read from a gluing for `H₀`: the same tree, and the free point `m` placed from
the corner of `H` that is the corner `freeCorner (σ m)` of `H₀`. -/
def relabelGlue (g : GlueData P k) (σ : Fin k ≃ Fin k) (s : Fin k → Fin 6) : GlueData P k where
  root := g.root
  rootDart := g.rootDart
  par := g.par
  depth := g.depth
  freeCorner m := g.freeCorner (σ m) - s m

theorem relabelGlue_valid {g : GlueData P k} (hg : g.Valid) (σ : Fin k ≃ Fin k)
    (s : Fin k → Fin 6) : (relabelGlue g σ s).Valid := by
  rcases hg with ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

/-- The glued configurations have the same points, up to the relabelling of the free points. -/
theorem glueY_relabel {H H₀ : HexChoice P k} (A : Assign P k) (σ : Fin k ≃ Fin k)
    (s : Fin k → Fin 6) (hs : ∀ m, H.base m = (P.R.face ^ (s m : ℕ)) (H₀.base (σ m)))
    (g : GlueData P k) :
    ∀ a, glueY H A (relabelGlue g σ s) a = glueY H₀ (relabelAssign A σ s) g (Sum.map id σ a) := by
  -- First prove a lemma about frameN equality that works for all vertices
  have h_frameN : ∀ n, ∀ v', (relabelGlue g σ s).frameN A n v' = g.frameN (relabelAssign A σ s) n v' := by
    intro n
    induction n with
    | zero => intro v'; rfl
    | succ n ih =>
      intro v'
      dsimp [GlueData.frameN, relabelGlue, relabelAssign, Assign.turn, GlueData.refD]
      by_cases h : v' = g.root
      · simp [h]
      · rw [if_neg h, if_neg h]
        dsimp [relabelGlue, relabelAssign] at ih
        rw [ih (g.par v').fst]
  intro a
  cases a with
  | inl v =>
      have h_frame : (relabelGlue g σ s).frame A v = g.frame (relabelAssign A σ s) v := by
        unfold GlueData.frame
        simpa [relabelGlue] using h_frameN (g.depth v) v
      simp [glueY, Sum.map, h_frame]
  | inr m =>
      let i : Fin 6 := g.freeCorner (σ m) - s m
      let j : Fin 6 := g.freeCorner (σ m)
      have hi_add_s : i + s m = j := sub_add_cancel _ _
      -- Use the given lemma face_pow_add_fin
      have h_face_pow_add : (P.R.face ^ ((i + s m : Fin 6) : ℕ)) (H₀.base (σ m)) =
          (P.R.face ^ (i : ℕ)) ((P.R.face ^ (s m : ℕ)) (H₀.base (σ m))) :=
        face_pow_add_fin (P := P) (y := H₀.base (σ m)) (hy := H₀.hex (σ m)) (i := i) (s := s m)
      -- (face ^ j) y = (face ^ i) ((face ^ s) y)
      have h_face_eq : (P.R.face ^ (j : ℕ)) (H₀.base (σ m)) =
          (P.R.face ^ (i : ℕ)) ((P.R.face ^ (s m : ℕ)) (H₀.base (σ m))) := by
        rw [← hi_add_s]
        rw [← h_face_pow_add]
      -- Expand both sides
      dsimp [glueY, Sum.map, relabelGlue, relabelAssign, GlueData.frame, GlueData.frameN,
        GlueData.refD, Assign.turn]
      rw [hs m]
      -- Now the goal is an equality of toEuclideanLin applications
      -- Use h_face_eq to relate the face powers, and h_frameN for the frames
      -- Also simplify the distance terms using hi_add_s
      have h_dist1 : A.r (σ.symm (σ m)) (g.freeCorner (σ m) - s (σ.symm (σ m))) = A.r m i := by
        dsimp [i]
        simp [Equiv.symm_apply_apply]
      have h_dist2 : A.r (σ.symm (σ m)) (g.freeCorner (σ m) + 1 - s (σ.symm (σ m))) = A.r m (i + 1) := by
        dsimp [i]
        simp [Equiv.symm_apply_apply]
        abel
      -- The face powers give equal vertices
      have h_face_vertex : ((P.R.face ^ (i : ℕ)) ((P.R.face ^ (s m : ℕ)) (H₀.base (σ m)))).toProd.1 =
          ((P.R.face ^ (j : ℕ)) (H₀.base (σ m))).toProd.1 := by
        rw [h_face_eq]
      -- Now apply h_frameN to the specific vertices
      have h_frame_eq := h_frameN
        (g.depth ((P.R.face ^ (i : ℕ)) ((P.R.face ^ (s m : ℕ)) (H₀.base (σ m)))).toProd.1)
        ((P.R.face ^ (i : ℕ)) ((P.R.face ^ (s m : ℕ)) (H₀.base (σ m)))).toProd.1
      dsimp [relabelGlue, relabelAssign] at h_frame_eq
      -- Now the goal: expand i, j and use the equalities
      dsimp [i, j] at *
      -- Now the goal has explicit expressions; use the equalities
      rw [h_face_eq]  -- relates the face powers
      rw [h_frame_eq]  -- relates the frames
      rw [h_dist1]  -- relates the first distance
      rw [h_dist2]  -- relates the second distance

/-- Pair does not see the labels, nor an isometry: it passes along a bijection of the points that
keeps the adjacency. -/
theorem pairFires_of_equiv {A A' : Assign P k} (hd : A'.d = A.d) (e : Pts P k ≃ Pts P k)
    (he : ∀ a b, PAdj P (e a) (e b) ↔ PAdj P a b) (O : E3 ≃ₗᵢ[ℝ] E3) {Y Y' : Pts P k → E3}
    (hY : ∀ a, Y a = O (Y' (e a))) (h : PairFires P A' Y') : PairFires P A Y := by
  rcases h with ⟨a', b', hne', hpadj', hdist'⟩
  refine ⟨e.symm a', e.symm b', ?_, ?_, ?_⟩
  · intro h_eq
    apply hne'
    calc
      a' = e (e.symm a') := by simp
      _ = e (e.symm b') := by rw [h_eq]
      _ = b' := by simp
  · -- ¬ PAdj P (e.symm a') (e.symm b')
    intro h
    apply hpadj'
    simpa using (he (e.symm a') (e.symm b')).mpr h
  · -- ‖Y (e.symm a') - Y (e.symm b')‖ < 2 * sin (A.d / 2)
    rw [hY (e.symm a'), hY (e.symm b')]
    simp
    -- Now we need: ‖O (Y' a') - O (Y' b')‖ < 2 * sin (A.d / 2)
    have hnorm : ‖O (Y' a') - O (Y' b')‖ = ‖Y' a' - Y' b'‖ := by
      calc
        ‖O (Y' a') - O (Y' b')‖ = ‖O (Y' a' - Y' b')‖ := by rw [O.map_sub]
        _ = ‖Y' a' - Y' b'‖ := by rw [O.norm_map]
    rw [hnorm, ← hd]
    exact hdist'

/-- Local does not see the labels, nor an isometry. -/
theorem localFires_of_equiv {F : Set Frame} {α β : Type} (e : α ≃ β) (O : E3 ≃ₗᵢ[ℝ] E3)
    {Y : α → E3} {Y' : β → E3} (hY : ∀ a, Y a = O (Y' (e a))) (h : LocalFires F Y') :
    LocalFires F Y := by
  rcases h with ⟨q, hqF, O', j, hj⟩
  refine ⟨q, hqF, O'.trans O, e.trans j, ?_⟩
  intro a
  rw [hY a]
  have : (e.trans j) a = j (e a) := rfl
  have : (O'.trans O) (q.p (j (e a))) = O (O' (q.p (j (e a)))) := rfl
  calc
    ‖O (Y' (e a)) - (O'.trans O) (q.p ((e.trans j) a))‖ = ‖O (Y' (e a)) - O (O' (q.p (j (e a))))‖ := by
      simp
    _ = ‖O (Y' (e a) - O' (q.p (j (e a))))‖ := by rw [map_sub]
    _ = ‖Y' (e a) - O' (q.p (j (e a)))‖ := by rw [O.norm_map]
    _ ≤ rLocal := hj (e a)

/-- The relabelling of the free points keeps the adjacency of points. -/
theorem pAdj_sumMap (σ : Fin k ≃ Fin k) (a b : Pts P k) :
    PAdj P (Equiv.sumCongr (Equiv.refl _) σ a) (Equiv.sumCongr (Equiv.refl _) σ b) ↔ PAdj P a b := by
  cases a with
  | inl va =>
    cases b with
    | inl vb =>
      simp [PAdj]
    | inr vb =>
      simp [PAdj]
  | inr va =>
    cases b with
    | inl vb =>
      simp [PAdj]
    | inr vb =>
      simp [PAdj]

end Tammes15.PaperSteps
