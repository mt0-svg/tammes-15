import Tammes15.FaceChain.Basic

/-!
# Face sizes

Lemma 4.3 of the paper: a face orbit of period `m` with strict support is a strict
spherical polygon of the eight-point code with perimeter `m d`, less than `2π`
(`StrictSphericalPolygon.perimeter_lt_two_pi`), so `m ≤ 6` when `7 dlo > 2π` and `d ≥ dlo`.
-/

open Real Matrix WithLp InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15.FaceChain

open Tammes15.Vendor.EM8.SquareAntiprismVerification

theorem face_support_fin {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (x : V → E3) (hS : StrictSupportFace R x)
    (e : G.Dart) (n : ℕ) (hn : Function.minimalPeriod R.face e = n + 3)
    (i j : Fin (n + 3)) (hji : j ≠ i) (hji1 : j ≠ i + 1) :
    0 < ⟪cross (x ((R.face ^ i.val) e).fst) (x ((R.face ^ (i + 1).val) e).fst),
      x ((R.face ^ j.val) e).fst⟫ := by
  set F := R.face with hF
  set f := (F ^ i.val) e with hf
  have hi := i.isLt
  have hj := j.isLt
  have hi1 := (i + 1 : Fin (n + 3)).isLt
  -- the value of `i + 1`
  have hv : ((i + 1 : Fin (n + 3)).val = i.val + 1) ∨
      ((i + 1 : Fin (n + 3)).val = 0 ∧ i.val + 1 = n + 3) := by
    have h1 : ((i + 1 : Fin (n + 3)).val) = (i.val + 1) % (n + 3) := by
      simpa using Fin.val_add i 1
    rcases Nat.lt_or_ge (i.val + 1) (n + 3) with h | h
    · left; rw [h1, Nat.mod_eq_of_lt h]
    · right
      have h2 : i.val + 1 = n + 3 := by omega
      exact ⟨by rw [h1, h2, Nat.mod_self], h2⟩
  have hper : (F ^ (n + 3)) e = e := by
    have h := Function.isPeriodicPt_minimalPeriod (⇑F) e
    rw [hn] at h
    rw [Equiv.Perm.coe_pow]
    exact h
  -- the next vertex
  have hnext : (F ^ (i + 1 : Fin (n + 3)).val) e = F f := by
    rcases hv with h | ⟨h, h2⟩
    · rw [h, pow_succ', Equiv.Perm.mul_apply]
    · rw [h, pow_zero, Equiv.Perm.one_apply, hf, ← Equiv.Perm.mul_apply, ← pow_succ', h2, hper]
  -- the period of `f`
  have hpf : Function.minimalPeriod F f = n + 3 := by
    rw [hf, Equiv.Perm.coe_pow, Function.minimalPeriod_apply_iterate
      (Function.minimalPeriod_pos_iff_mem_periodicPts.mp (by rw [hn]; omega)), hn]
  have hnp : ∀ k, 0 < k → k < n + 3 → (F ^ k) f ≠ f := by
    intro k hk0 hk1 h
    have := Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (f := ⇑F) (x := f) hk0.ne'
      (by rw [hpf]; exact hk1)
    apply this
    show (⇑F)^[k] f = f
    rw [← Equiv.Perm.coe_pow]
    exact h
  -- the step from `f` to the vertex `j`
  obtain ⟨t, ht_lt, ht0, ht1, hte⟩ : ∃ t, t < n + 3 ∧ t ≠ 0 ∧ t ≠ 1 ∧
      (F ^ t) f = (F ^ j.val) e := by
    have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hne1 : j.val ≠ (i + 1 : Fin (n + 3)).val := fun h => hji1 (Fin.ext h)
    rcases Nat.lt_or_ge j.val i.val with hlt | hge
    · refine ⟨j.val + (n + 3) - i.val, by omega, by omega, by rcases hv with h | ⟨h, h2⟩ <;> omega, ?_⟩
      rw [hf, ← Equiv.Perm.mul_apply, ← pow_add, show j.val + (n + 3) - i.val + i.val =
        j.val + (n + 3) by omega, pow_add, Equiv.Perm.mul_apply, hper]
    · refine ⟨j.val - i.val, by omega, by omega, by rcases hv with h | ⟨h, h2⟩ <;> omega, ?_⟩
      rw [hf, ← Equiv.Perm.mul_apply, ← pow_add, show j.val - i.val + i.val = j.val by omega]
  have h1 : (F ^ t) f ≠ f := hnp t (by omega) ht_lt
  have h2 : (F ^ t) f ≠ F f := by
    intro h
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [pow_succ', Equiv.Perm.mul_apply] at h
    exact hnp s (by omega) (by omega) (F.injective h)
  have key := hS f t h1 h2
  rw [hnext, face_fst, ← hte]
  exact key

theorem face_side_length {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (x : V → E3) (d : ℝ)
    (hG : ∀ a b, G.Adj a b → sdist (x a) (x b) = d) (e : G.Dart) (n : ℕ)
    (hn : Function.minimalPeriod R.face e = n + 3) (i : Fin (n + 3)) :
    sdist (x ((R.face ^ i.val) e).fst) (x ((R.face ^ (i + 1).val) e).fst) = d := by
  have h_val_add : ((i + 1 : Fin (n + 3)).val : ℕ) = ((i.val : ℕ) + 1) % (n + 3) := by
    simpa using Fin.val_add i 1
  have h_iterate_eq : (R.face ^ (i + 1 : Fin (n + 3)).val) e = R.face ((R.face ^ i.val) e) := by
    calc
      (R.face ^ (i + 1 : Fin (n + 3)).val) e = (R.face ^ (((i.val : ℕ) + 1) % (n + 3))) e := by
        simp [h_val_add]
      _ = (R.face ^ (i.val + 1)) e := by
        have h := Function.iterate_mod_minimalPeriod_eq (f := R.face) (x := e) (n := i.val + 1)
        rw [hn] at h
        simpa [Equiv.Perm.coe_pow] using h
      _ = R.face ((R.face ^ i.val) e) := by simp [pow_succ']
  have h_face_fst_eq_snd (f : G.Dart) : (R.face f).fst = f.snd := by
    have h_rot_symm_fst : ∀ (x : G.Dart), (R.rot.symm x).fst = x.fst := by
      intro x
      have := R.rot_fst (R.rot.symm x)
      simpa [Equiv.apply_symm_apply] using this.symm
    calc
      (R.face f).fst = (R.rot.symm (SimpleGraph.Dart.symm f)).fst := rfl
      _ = (SimpleGraph.Dart.symm f).fst := by rw [h_rot_symm_fst]
      _ = f.snd := by simp [SimpleGraph.Dart.symm]
  calc
    sdist (x ((R.face ^ i.val) e).fst) (x ((R.face ^ (i + 1 : Fin (n + 3)).val) e).fst) =
      sdist (x ((R.face ^ i.val) e).fst) (x (R.face ((R.face ^ i.val) e)).fst) := by
      simp [h_iterate_eq]
    _ = sdist (x ((R.face ^ i.val) e).fst) (x ((R.face ^ i.val) e).snd) := by
      rw [h_face_fst_eq_snd]
    _ = d := hG _ _ ((R.face ^ i.val) e).adj

theorem face_perimeter_lt {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (d : ℝ)
    (hG : ∀ a b, G.Adj a b → sdist (x a) (x b) = d) (hS : StrictSupportFace R x)
    (hface3 : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e) (e : G.Dart) :
    (Function.minimalPeriod R.face e : ℝ) * d < 2 * π := by
  set m := Function.minimalPeriod R.face e with hm_def
  have hm3 : 3 ≤ m := hface3 e
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hm3
  -- hn : m = 3 + n
  have hn' : Function.minimalPeriod R.face e = n + 3 := by
    rw [← hm_def, hn, add_comm]
  let vertex : Fin (n + 3) → E3 := λ i => x ((R.face ^ (i.val : ℕ)) e).fst
  have hunits : ∀ i, ‖vertex i‖ = 1 := λ i => hx _
  have hsupport : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < inner ℝ (crossVec (vertex i) (vertex (i + 1))) (vertex j) := by
    intro i j hji hji1
    have h := Tammes15.FaceChain.face_support_fin R x hS e n hn' i j hji hji1
    simpa [vertex, Tammes15.FaceChain.cross_eq_crossVec] using h
  let Q : StrictSphericalPolygon n :=
    { vertex := vertex
      unit := hunits
      support := hsupport }
  have hperim_lt : Q.perimeter < 2 * Real.pi :=
    StrictSphericalPolygon.perimeter_lt_two_pi Q
  have hperim_eq : Q.perimeter = (m : ℝ) * d := by
    calc
      Q.perimeter = ∑ i : Fin (n + 3), sphereAngle (Q.vertex i) (Q.vertex (i + 1)) := rfl
      _ = ∑ i : Fin (n + 3), sdist (Q.vertex i) (Q.vertex (i + 1)) := by
        simp [sphereAngle, sdist]
      _ = ∑ i : Fin (n + 3), d := by
        refine Finset.sum_congr rfl (λ i hi => ?_)
        dsimp [Q, vertex]
        rw [Tammes15.FaceChain.face_side_length R x d hG e n hn' i]
      _ = ((Finset.univ : Finset (Fin (n + 3))).card : ℝ) * d := by
        simp [Finset.sum_const]
      _ = ((n + 3 : ℕ) : ℝ) * d := by simp
      _ = (m : ℝ) * d := by
        have hm_eq : m = n + 3 := hm_def.trans hn'
        rw [hm_eq]
  linarith

theorem faceSizes_of {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (dlo d : ℝ) (h7 : 7 * dlo > 2 * π) (hlo : dlo ≤ d)
    (hface3 : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e)
    (hper : ∀ e : G.Dart, (Function.minimalPeriod R.face e : ℝ) * d < 2 * π) :
    FaceSizes R 3 6 := by
  intro e
  have hlower : 3 ≤ Function.minimalPeriod R.face e := hface3 e
  have hupper : Function.minimalPeriod R.face e ≤ 6 := by
    by_contra! h
    -- h : 6 < Function.minimalPeriod R.face e
    have hm : (7 : ℕ) ≤ Function.minimalPeriod R.face e := Nat.succ_le_of_lt h
    have hm' : (7 : ℝ) ≤ (Function.minimalPeriod R.face e : ℝ) := by exact_mod_cast hm
    have h2π_pos : 0 < 2 * π := mul_pos (by norm_num) pi_pos
    have hdlo_pos : 0 < dlo := by linarith
    have hdpos : 0 < d := by linarith
    have h1 : (7 : ℝ) * dlo ≤ (7 : ℝ) * d := by gcongr
    have h2 : (7 : ℝ) * d ≤ (Function.minimalPeriod R.face e : ℝ) * d := by gcongr
    have h3 : (Function.minimalPeriod R.face e : ℝ) * d < 2 * π := hper e
    have h4 : 2 * π < (7 : ℝ) * dlo := h7
    linarith
  exact And.intro hlower hupper

end Tammes15.FaceChain
