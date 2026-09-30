import Tammes15.Hyps.Case
import Tammes15.Draw.Angular
import Tammes15.Draw.Frame
import Tammes15.Trigrows.Points
import Tammes15.Trigrows.Sdist

/-!
# Transport of a realisation along an isomorphism of rotation systems

The enumeration (D2) gives an entry `P'` of the list isomorphic to the plane graph `P` of a
configuration, possibly with the orientation reversed. A realisation of a case of `P` gives one of
the corresponding case of `P'`: the same points relabelled when the isomorphism keeps the
rotation (`realisation_iso`), and first the antipodal image `-x` with the reversed rotation
system when it reverses it (`realisation_reverse`).
-/

open Real Matrix WithLp InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

section Graph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The reversed rotation system (the rotation of the mirror image). -/
def RotSys.reverse (R : RotSys G) : RotSys G where
  rot := R.rot.symm
  rot_fst x := by simpa using (R.rot_fst (R.rot.symm x)).symm
  rot_cycle x y h := Equiv.Perm.sameCycle_inv.mpr (R.rot_cycle x y h)

theorem RotSys.reverse_face_apply (R : RotSys G) (e : G.Dart) :
    R.reverse.face e = (R.face.symm e.symm).symm := by
  simp [RotSys.face, RotSys.reverse, Equiv.trans_apply, Equiv.symm_trans, Function.Involutive.coe_toPerm, Function.Involutive.toPerm_symm]

theorem RotSys.reverse_face_pow (R : RotSys G) (e : G.Dart) (j : ℕ) :
    (R.reverse.face ^ j) e = ((R.face ^ j).symm e.symm).symm := by
  induction' j with j ih
  · rw [pow_zero, pow_zero]
    have h : ((Equiv.symm (1 : Equiv.Perm G.Dart)) e.symm) = e.symm := by
      simpa using (Equiv.symm_apply_apply (1 : Equiv.Perm G.Dart) e.symm)
    simp [h, SimpleGraph.Dart.symm_symm]
  · rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, ih]
    have hbase : ∀ e' : G.Dart, R.reverse.face e' = (R.face.symm e'.symm).symm := by
      intro e'
      simp [RotSys.face, RotSys.reverse, Function.Involutive.toPerm]
    rw [hbase]
    have hinv : (R.face ^ (j + 1)).symm = R.face.symm * (R.face ^ j).symm := by
      calc
        (R.face ^ (j + 1)).symm = (R.face ^ (j + 1))⁻¹ := by rw [Equiv.Perm.inv_def]
        _ = (R.face ^ j * R.face)⁻¹ := by rw [pow_succ]
        _ = R.face⁻¹ * (R.face ^ j)⁻¹ := by rw [_root_.mul_inv_rev]
        _ = R.face.symm * (R.face ^ j).symm := by simp [Equiv.Perm.inv_def]
    calc
      (R.face.symm (((R.face ^ j).symm e.symm).symm.symm)).symm
          = (R.face.symm ((R.face ^ j).symm e.symm)).symm := by simp
      _ = ((R.face.symm * (R.face ^ j).symm) e.symm).symm := by rw [Equiv.Perm.mul_apply]
      _ = ((R.face ^ (j + 1)).symm e.symm).symm := by rw [hinv]

theorem RotSys.reverse_minimalPeriod (R : RotSys G) (e : G.Dart) :
    Function.minimalPeriod R.reverse.face e = Function.minimalPeriod R.face e.symm := by
  -- Let s be the dart symmetry as a permutation, and f = R.face
  let s : Equiv.Perm G.Dart := Function.Involutive.toPerm (SimpleGraph.Dart.symm : G.Dart → G.Dart) SimpleGraph.Dart.symm_involutive
  let f : Equiv.Perm G.Dart := R.face
  have hs_inv : Function.Involutive (s : G.Dart → G.Dart) := by
    intro x
    simp [s]
  have hs_symm : ∀ x, s x = x.symm := by
    intro x; rfl
  -- Key identity: R.reverse.face = s ∘ f⁻¹ ∘ s as functions
  have h_rev_face_eq_fun : (R.reverse.face : G.Dart → G.Dart) = (s : G.Dart → G.Dart) ∘ ((f⁻¹ : Equiv.Perm G.Dart) : G.Dart → G.Dart) ∘ (s : G.Dart → G.Dart) := by
    apply funext; intro x
    dsimp [s, f, RotSys.reverse, RotSys.face]
    simp
  -- Use the characterization of minimal period
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro n
  -- Expand IsPeriodicPt
  rw [Function.IsPeriodicPt, Function.IsPeriodicPt]
  -- Now we need: (R.reverse.face)^[n] e = e ↔ (R.face)^[n] (e.symm) = e.symm
  rw [h_rev_face_eq_fun]
  -- Now we need: (s ∘ f⁻¹ ∘ s)^[n] e = e ↔ f^[n] (e.symm) = e.symm
  -- Lemma: for an involution s, (s ∘ g ∘ s)^[n] = s ∘ g^[n] ∘ s
  have h_iter_conj : ∀ (g : G.Dart → G.Dart), (s ∘ g ∘ s)^[n] = s ∘ (g^[n]) ∘ s := by
    intro g
    induction' n with k ih
    · rfl
    · rw [Function.iterate_succ', Function.iterate_succ', ih]
      ext x
      · dsimp; rw [hs_inv]
      · dsimp; rw [hs_inv]
  rw [h_iter_conj ((f⁻¹ : Equiv.Perm G.Dart) : G.Dart → G.Dart)]
  -- Now we need: s ((f⁻¹)^[n] (s e)) = e ↔ f^[n] (e.symm) = e.symm
  -- Expand IsFixedPt
  rw [Function.IsFixedPt, Function.IsFixedPt]
  -- Now we need: (s ∘ (f⁻¹)^[n] ∘ s) e = e ↔ f^[n] (e.symm) = e.symm
  -- Simplify the left side
  rw [Function.comp_apply, Function.comp_apply]
  -- Now we need: s ((f⁻¹)^[n] (s e)) = e ↔ f^[n] (e.symm) = e.symm
  rw [hs_symm e]
  -- Now we need: s ((f⁻¹)^[n] (e.symm)) = e ↔ f^[n] (e.symm) = e.symm
  -- Apply s to both sides of the left equality
  constructor
  · intro h
    -- h: s ((f⁻¹)^[n] (e.symm)) = e
    -- Apply s to both sides: s (s ((f⁻¹)^[n] (e.symm))) = s e
    -- Using hs_inv: s (s x) = x, and hs_symm: s e = e.symm
    -- This gives: (f⁻¹)^[n] (e.symm) = e.symm
    have h' := congrArg s h
    rw [hs_inv, hs_symm] at h'
    -- h': (f⁻¹)^[n] (e.symm) = e.symm
    -- Now relate (f⁻¹)^[n] to f^[n]
    -- (f⁻¹)^[n] = (f⁻¹ ^ n) = (f ^ n)⁻¹
    rw [Equiv.Perm.iterate_eq_pow] at h'
    -- h': (f⁻¹ ^ n) (e.symm) = e.symm
    rw [inv_pow] at h'
    -- h': (f ^ n)⁻¹ (e.symm) = e.symm
    -- Apply (f ^ n) to both sides
    have h'' := congrArg (fun y => (f ^ n) y) h'
    -- h'': (f ^ n) ((f ^ n)⁻¹ (e.symm)) = (f ^ n) (e.symm)
    -- But (f ^ n) ((f ^ n)⁻¹ x) = x
    -- So h'' simplifies to: e.symm = (f ^ n) (e.symm)
    -- i.e., (f ^ n) (e.symm) = e.symm
    -- We need: f^[n] (e.symm) = e.symm
    -- Since f = R.face, f^[n] = (f ^ n) as functions
    simpa [f, Equiv.Perm.iterate_eq_pow, Equiv.apply_symm_apply] using h''.symm
  · intro h
    -- h: f^[n] (e.symm) = e.symm
    -- We need: s ((f⁻¹)^[n] (e.symm)) = e
    -- From h, we have (f⁻¹)^[n] (e.symm) = e.symm (since f is a permutation)
    have h_inv : ((f⁻¹ : Equiv.Perm G.Dart) : G.Dart → G.Dart)^[n] (e.symm) = e.symm := by
      rw [Equiv.Perm.iterate_eq_pow] at h ⊢
      -- h: (f ^ n) (e.symm) = e.symm
      -- Goal: (f⁻¹ ^ n) (e.symm) = e.symm
      -- From h, apply (f ^ n)⁻¹ to both sides
      have h' := congrArg (fun y => (f ^ n)⁻¹ y) h
      -- h': (f ^ n)⁻¹ ((f ^ n) (e.symm)) = (f ^ n)⁻¹ (e.symm)
      -- i.e., e.symm = (f ^ n)⁻¹ (e.symm)
      -- Now (f ^ n)⁻¹ = f⁻¹ ^ n by inv_pow
      simpa [f, inv_pow] using h'.symm
    rw [h_inv]
    simp [hs_symm]

theorem RotSys.reverse_sameCycle (R : RotSys G) (a b : G.Dart) :
    R.reverse.face.SameCycle a b ↔ R.face.SameCycle a.symm b.symm := by
  let s : Equiv.Perm G.Dart := Function.Involutive.toPerm SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
  have hs_inv : s⁻¹ = s := by
    rw [Equiv.Perm.inv_def]
    exact Function.Involutive.toPerm_symm SimpleGraph.Dart.symm_involutive
  have h_rev_face_eq : R.reverse.face = s * R.face⁻¹ * s⁻¹ := by
    apply Equiv.ext
    intro x
    dsimp [s, RotSys.face, RotSys.reverse]
    simp [SimpleGraph.Dart.symm_symm]
  rw [h_rev_face_eq]
  rw [Equiv.Perm.sameCycle_conj]
  rw [hs_inv]
  simp [s, Function.Involutive.coe_toPerm]

theorem RotSys.reverse_faceCount (R : RotSys G) : R.reverse.faceCount = R.faceCount := by
  let s : Equiv.Perm G.Dart := Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive
  have hs_inv : s⁻¹ = s := by
    ext x
    · simp [s]
    · simp [s, Function.Involutive.coe_toPerm]
  have h_face_eq : R.reverse.face = s * R.face⁻¹ * s := by
    ext x
    · simp [RotSys.face, RotSys.reverse, s]
    · simp [RotSys.face, RotSys.reverse, s]
  have h_sameCycle_iff (a b : G.Dart) : R.reverse.face.SameCycle a b ↔ R.face.SameCycle (s a) (s b) := by
    rw [h_face_eq]
    have h_conj := Equiv.Perm.sameCycle_conj (f := R.face⁻¹) (g := s) (x := a) (y := b)
    have h_temp : s * R.face⁻¹ * s = s * R.face⁻¹ * s⁻¹ := by rw [hs_inv]
    rw [h_temp, h_conj]
    simp [hs_inv, Equiv.Perm.sameCycle_inv]
  have h_equiv : Quotient (Equiv.Perm.SameCycle.setoid R.reverse.face) ≃
                Quotient (Equiv.Perm.SameCycle.setoid R.face) :=
    Quotient.congr (e := s) (eq := h_sameCycle_iff)
  unfold RotSys.faceCount
  exact Nat.card_congr h_equiv

end Graph

section Iso

variable {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  {G : SimpleGraph V} {G' : SimpleGraph V'}

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] in
theorem dmap_dmap_symm (φ : G ≃g G') (e' : G'.Dart) : dmap φ (dmap φ.symm e') = e' := by
  ext <;> simp [dmap]

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] in
theorem dmap_injective (φ : G ≃g G') : Function.Injective (dmap φ) := by
  intro a b h
  have h1 := congrArg (fun e => φ.symm e.fst) h
  have h2 := congrArg (fun e => φ.symm e.snd) h
  simp only [dmap, RelIso.symm_apply_apply] at h1 h2
  exact SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)

theorem dmap_face (R : RotSys G) (R' : RotSys G') (φ : G ≃g G')
    (hφ : ∀ e, dmap φ (R.rot e) = R'.rot (dmap φ e)) (e : G.Dart) :
    dmap φ (R.face e) = R'.face (dmap φ e) := by
  have hface_eq : ∀ {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (R : RotSys G) (e : G.Dart),
    R.face e = R.rot.symm (e.symm) := by
    intro V _ _ G R e
    calc
      R.face e = ((SimpleGraph.Dart.symm_involutive.toPerm).trans R.rot.symm) e := rfl
      _ = R.rot.symm ((SimpleGraph.Dart.symm_involutive.toPerm) e) := by rw [Equiv.trans_apply]
      _ = R.rot.symm (e.symm) := by rw [Function.Involutive.coe_toPerm]
  have hφ_symm : ∀ f, dmap φ (R.rot.symm f) = R'.rot.symm (dmap φ f) := by
    intro f
    have h := hφ (R.rot.symm f)
    rw [Equiv.apply_symm_apply] at h
    calc
      dmap φ (R.rot.symm f) = R'.rot.symm (R'.rot (dmap φ (R.rot.symm f))) := by
        rw [Equiv.symm_apply_apply]
      _ = R'.rot.symm (dmap φ f) := by rw [← h]
  have hsymm_dmap : dmap φ (e.symm) = (dmap φ e).symm := by
    apply SimpleGraph.Dart.ext
    dsimp [dmap]
    simp
  calc
    dmap φ (R.face e) = dmap φ (R.rot.symm (e.symm)) := by rw [hface_eq R e]
    _ = R'.rot.symm (dmap φ (e.symm)) := by rw [hφ_symm (e.symm)]
    _ = R'.rot.symm ((dmap φ e).symm) := by rw [hsymm_dmap]
    _ = R'.face (dmap φ e) := by rw [hface_eq R' (dmap φ e)]

theorem dmap_face_pow (R : RotSys G) (R' : RotSys G') (φ : G ≃g G')
    (hφ : ∀ e, dmap φ (R.rot e) = R'.rot (dmap φ e)) (e : G.Dart) (j : ℕ) :
    dmap φ ((R.face ^ j) e) = (R'.face ^ j) (dmap φ e) := by
  have hface_step : ∀ e, dmap φ (R.face e) = R'.face (dmap φ e) := by
    intro e
    calc
      dmap φ (R.face e) = dmap φ (R.rot.symm (e.symm)) := rfl
      _ = R'.rot.symm (dmap φ (e.symm)) := by
        have h := hφ (R.rot.symm (e.symm))
        simpa [Equiv.apply_symm_apply] using congrArg R'.rot.symm h.symm
      _ = R'.rot.symm ((dmap φ e).symm) := by
        ext <;> simp [dmap]
      _ = R'.face (dmap φ e) := rfl
  induction j generalizing e with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [hface_step ((R.face ^ j) e), ih e]

theorem dmap_minimalPeriod (R : RotSys G) (R' : RotSys G') (φ : G ≃g G')
    (hφ : ∀ e, dmap φ (R.rot e) = R'.rot (dmap φ e)) (e : G.Dart) :
    Function.minimalPeriod R'.face (dmap φ e) = Function.minimalPeriod R.face e := by
  apply (Function.minimalPeriod_eq_minimalPeriod_iff).mpr
  intro n
  have hinj : Function.Injective (dmap φ) := by
    intro a b h
    apply SimpleGraph.Dart.ext
    have h_prod : (dmap φ a).toProd = (dmap φ b).toProd := by
      rw [h]
    have h_fst : (dmap φ a).fst = (dmap φ b).fst := by
      have := congrArg Prod.fst h_prod
      simpa [dmap] using this
    have h_snd : (dmap φ a).snd = (dmap φ b).snd := by
      have := congrArg Prod.snd h_prod
      simpa [dmap] using this
    have hφ_inj : Function.Injective (φ : V → V') := by
      -- φ is an order isomorphism of adjacency relations, hence a bijection on vertices
      exact φ.injective
    apply Prod.ext
    · apply hφ_inj
      simpa [dmap] using h_fst
    · apply hφ_inj
      simpa [dmap] using h_snd
  have h_face_eq : ∀ e, dmap φ (R.face e) = R'.face (dmap φ e) := by
    intro e
    dsimp [RotSys.face]
    have h_symm : dmap φ (e.symm) = (dmap φ e).symm := by
      ext <;> simp [dmap]
    have htemp := hφ (R.rot.symm (e.symm))
    -- htemp : dmap φ (R.rot (R.rot.symm (e.symm))) = R'.rot (dmap φ (R.rot.symm (e.symm)))
    have htemp' : dmap φ (e.symm) = R'.rot (dmap φ (R.rot.symm (e.symm))) := by
      simpa [Equiv.apply_symm_apply] using htemp
    calc
      dmap φ (R.rot.symm (e.symm)) = R'.rot.symm (R'.rot (dmap φ (R.rot.symm (e.symm)))) := by
        simp
      _ = R'.rot.symm (dmap φ (e.symm)) := by rw [htemp']
      _ = R'.rot.symm ((dmap φ e).symm) := by rw [h_symm]
  have h_conj : ∀ (k : ℕ) (e : G.Dart), dmap φ ((R.face ^ k) e) = (R'.face ^ k) (dmap φ e) := by
    intro k e
    induction' k with k ih
    · rfl
    · calc
        dmap φ ((R.face ^ (k + 1)) e) = dmap φ (((R.face : G.Dart → G.Dart)^[k+1]) e) := by
          simp [Equiv.Perm.coe_pow]
        _ = dmap φ (R.face ((R.face : G.Dart → G.Dart)^[k] e)) := by
          rw [Function.iterate_succ_apply']
        _ = dmap φ (R.face ((R.face ^ k) e)) := by
          simp [Equiv.Perm.coe_pow]
        _ = R'.face (dmap φ ((R.face ^ k) e)) := by rw [h_face_eq]
        _ = R'.face ((R'.face ^ k) (dmap φ e)) := by rw [ih]
        _ = ((R'.face : G'.Dart → G'.Dart)^[k+1]) (dmap φ e) := by
          simp [Equiv.Perm.coe_pow, Function.iterate_succ_apply']
        _ = (R'.face ^ (k + 1)) (dmap φ e) := by simp [Equiv.Perm.coe_pow]
  constructor
  · intro h
    -- h : IsPeriodicPt R'.face n (dmap φ e), i.e., (R'.face ^ n) (dmap φ e) = dmap φ e
    have h_iter : (R'.face ^ n) (dmap φ e) = dmap φ e := h
    rw [← h_conj n e] at h_iter
    -- h_iter : dmap φ ((R.face ^ n) e) = dmap φ e
    -- dmap φ is injective because φ is injective on vertices
    -- So (R.face ^ n) e = e, i.e., IsPeriodicPt R.face n e
    apply hinj
    exact h_iter
  · intro h
    -- h : IsPeriodicPt R.face n e, i.e., (R.face ^ n) e = e
    have h_iter : (R.face ^ n) e = e := h
    have h_iter' : dmap φ ((R.face ^ n) e) = dmap φ e := by rw [h_iter]
    rw [h_conj n e] at h_iter'
    -- h_iter' : (R'.face ^ n) (dmap φ e) = dmap φ e, i.e., IsPeriodicPt R'.face n (dmap φ e)
    exact h_iter'

theorem dmap_sameCycle (R : RotSys G) (R' : RotSys G') (φ : G ≃g G')
    (hφ : ∀ e, dmap φ (R.rot e) = R'.rot (dmap φ e)) (a b : G.Dart) :
    R'.face.SameCycle (dmap φ a) (dmap φ b) ↔ R.face.SameCycle a b := by
  -- Key lemma: dmap φ commutes with face
  have h_face : ∀ e, dmap φ (R.face e) = R'.face (dmap φ e) := by
    intro e
    have h_symm : ∀ e', dmap φ (R.rot.symm e') = R'.rot.symm (dmap φ e') := by
      intro e'
      have h := hφ (R.rot.symm e')
      simpa [Equiv.apply_symm_apply] using congrArg R'.rot.symm h.symm
    calc
      dmap φ (R.face e) = dmap φ (R.rot.symm (e.symm)) := rfl
      _ = R'.rot.symm (dmap φ (e.symm)) := by rw [h_symm]
      _ = R'.rot.symm ((dmap φ e).symm) := rfl
      _ = R'.face (dmap φ e) := rfl
  -- dmap φ is injective (since φ is a graph isomorphism)
  have hinj : Function.Injective (dmap φ) := by
    intro x y h
    have hxy : x = y := by
      -- From h : dmap φ x = dmap φ y, we can apply dmap φ.symm to both sides
      calc
        x = dmap φ.symm (dmap φ x) := by simp [dmap]
        _ = dmap φ.symm (dmap φ y) := by rw [h]
        _ = y := by simp [dmap]
    exact hxy
  -- Helper lemma: h_face for inverse
  have h_face_inv : ∀ e, dmap φ (R.face⁻¹ e) = R'.face⁻¹ (dmap φ e) := by
    intro e
    have h := h_face (R.face⁻¹ e)
    simpa [Equiv.apply_symm_apply] using congrArg (R'.face⁻¹ : Equiv.Perm G'.Dart) h.symm
  -- Helper lemma: zpow identities
  have h_zpow_succ {α : Type} {f : Equiv.Perm α} {x : α} {n : ℤ} : (f ^ (n + 1)) x = f ((f ^ n) x) := by
    rw [add_comm n 1, zpow_add f 1 n, zpow_one f]
    rfl
  have h_zpow_pred {α : Type} {f : Equiv.Perm α} {x : α} {n : ℤ} : (f ^ (-n - 1)) x = f⁻¹ ((f ^ (-n)) x) := by
    have : -n - 1 = -1 + -n := by ring
    rw [this, zpow_add f (-1) (-n), zpow_neg f 1]
    simp
  -- Lemma: dmap φ commutes with face powers
  have h_pow : ∀ (i : ℤ) (e : G.Dart), dmap φ ((R.face ^ i) e) = (R'.face ^ i) (dmap φ e) := by
    intro i e
    induction' i using Int.induction_on with n ih n ih
    · simp
    · rw [h_zpow_succ (f := R.face) (x := e) (n := (n : ℤ)), h_face, ih,
        h_zpow_succ (f := R'.face) (x := dmap φ e) (n := (n : ℤ))]
    · rw [h_zpow_pred (f := R.face) (x := e) (n := (n : ℤ)), h_face_inv, ih,
        h_zpow_pred (f := R'.face) (x := dmap φ e) (n := (n : ℤ))]
  -- Main proof
  constructor
  · intro h
    rcases h with ⟨i, hi⟩
    -- hi : (R'.face ^ i) (dmap φ a) = dmap φ b
    have h_pow_i := h_pow i a
    -- h_pow_i : dmap φ ((R.face ^ i) a) = (R'.face ^ i) (dmap φ a)
    rw [← h_pow_i] at hi
    -- hi : dmap φ ((R.face ^ i) a) = dmap φ b
    have h_eq : (R.face ^ i) a = b := hinj hi
    exact ⟨i, h_eq⟩
  · intro h
    rcases h with ⟨i, hi⟩
    -- hi : (R.face ^ i) a = b
    have h_pow_i := h_pow i a
    -- h_pow_i : dmap φ ((R.face ^ i) a) = (R'.face ^ i) (dmap φ a)
    rw [hi] at h_pow_i
    -- h_pow_i : dmap φ b = (R'.face ^ i) (dmap φ a)
    exact ⟨i, h_pow_i.symm⟩

theorem iso_faceCount (R : RotSys G) (R' : RotSys G') (φ : G ≃g G')
    (hφ : ∀ e, dmap φ (R.rot e) = R'.rot (dmap φ e)) : R'.faceCount = R.faceCount := by
  let D : G.Dart ≃ G'.Dart :=
    { toFun := dmap φ
      invFun := dmap φ.symm
      left_inv := fun e => by ext <;> simp [dmap]
      right_inv := fun e' => dmap_dmap_symm φ e' }
  have h : ∀ a b, R.face.SameCycle a b ↔ R'.face.SameCycle (D a) (D b) :=
    fun a b => (dmap_sameCycle R R' φ hφ a b).symm
  unfold RotSys.faceCount
  exact (Nat.card_congr (Quotient.congr D h)).symm

theorem iso_spherical (R : RotSys G) (R' : RotSys G') (φ : G ≃g G')
    (hφ : ∀ e, dmap φ (R.rot e) = R'.rot (dmap φ e)) (h : R.Spherical) : R'.Spherical := by
  classical
  unfold RotSys.Spherical at h ⊢
  have hV : Fintype.card V' = Fintype.card V := (Fintype.card_congr φ.toEquiv).symm
  have hE : G'.edgeFinset.card = G.edgeFinset.card := φ.card_edgeFinset_eq.symm
  rw [iso_faceCount R R' φ hφ]
  convert h using 3
  · exact congrArg _ hV
  · convert congrArg (fun k : ℕ => (k : ℤ)) hE using 2

theorem iso_degree (φ : G ≃g G') (v : V) : G'.degree (φ v) = G.degree v := by
  exact SimpleGraph.Iso.degree_eq φ v

theorem iso_kConnected (φ : G ≃g G') (k : ℕ) (h : KConnected G k) : KConnected G' k := by
  rcases h with ⟨hcard, hconn⟩
  refine ⟨?_, ?_⟩
  · -- k < Fintype.card V'
    have hcard_eq : Fintype.card V = Fintype.card V' := Fintype.card_congr φ.toEquiv
    rw [← hcard_eq]
    exact hcard
  · -- ∀ S' : Finset V', S'.card < k → (G'.induce (↑S')ᶜ).Connected
    intro S' hS'
    let S : Finset V := S'.map (φ.symm.toEquiv : V' ≃ V).toEmbedding
    have hcard_S : S.card = S'.card := Finset.card_map _
    have hcard_S_lt_k : S.card < k := by
      rw [hcard_S]
      exact hS'
    have h_conn_S : (G.induce ((S : Set V)ᶜ)).Connected := hconn S hcard_S_lt_k
    -- Key: v ∈ S ↔ φ v ∈ S'
    have h_mem : ∀ v, v ∈ (S : Set V) ↔ (φ v) ∈ (S' : Set V') := by
      intro v
      constructor
      · intro hv
        rw [Finset.mem_coe, Finset.mem_map] at hv
        rcases hv with ⟨v', hv', rfl⟩
        simp [hv']
      · intro hv
        have : v = (φ.symm.toEquiv : V' ≃ V) (φ v) := by simp
        rw [this]
        apply Finset.mem_coe.mpr
        apply Finset.mem_map.mpr
        exact ⟨φ v, hv, rfl⟩
    -- Build Set.BijOn φ (Sᶜ) (S'ᶜ)
    have hbij : Set.BijOn (φ : V → V') ((S : Set V)ᶜ) ((S' : Set V')ᶜ) := by
      refine ⟨?_, ?_, ?_⟩
      · -- MapsTo: v ∈ Sᶜ → φ v ∈ S'ᶜ
        intro v hv
        rw [Set.mem_compl_iff] at hv ⊢
        intro hvs'
        apply hv
        rw [h_mem v]
        exact hvs'
      · -- InjOn
        exact (RelIso.injective φ).injOn (s := ((S : Set V)ᶜ))
      · -- SurjOn: v' ∈ S'ᶜ → ∃ v ∈ Sᶜ, φ v = v'
        intro v' hv'
        rw [Set.mem_compl_iff] at hv'
        have hv_symm_not_S : (φ.symm v') ∉ (S : Set V) := by
          intro hS
          apply hv'
          have := (h_mem (φ.symm v')).mp hS
          simpa using this
        refine ⟨φ.symm v', hv_symm_not_S, ?_⟩
        simp
    -- Then use SimpleGraph.Iso.induce
    let iso : (G.induce ((S : Set V)ᶜ)) ≃g (G'.induce ((S' : Set V')ᶜ)) :=
      SimpleGraph.Iso.induce φ hbij
    -- Connectedness transfers
    exact ((SimpleGraph.Iso.connected_iff iso).mp h_conn_S)

theorem isAngular_iso (R : RotSys G) (R' : RotSys G') (φ : G ≃g G')
    (hφ : ∀ e, dmap φ (R.rot e) = R'.rot (dmap φ e)) (x : V → E3) (hR : IsAngular R x) :
    IsAngular R' (fun v' => x (φ.symm v')) := by
  intro e' f' hfst hne
  have h_dmap_symm (d : G'.Dart) : dmap φ (dmap φ.symm d) = d := by
    apply SimpleGraph.Dart.ext
    simp [dmap]
  have h_rot_eq : R'.rot e' = dmap φ (R.rot (dmap φ.symm e')) := by
    calc
      R'.rot e' = R'.rot (dmap φ (dmap φ.symm e')) := by rw [h_dmap_symm]
      _ = dmap φ (R.rot (dmap φ.symm e')) := by rw [hφ]
  have hfst' : (dmap φ.symm f').fst = (dmap φ.symm e').fst := by
    simpa [dmap] using congrArg φ.symm hfst
  have hne' : dmap φ.symm f' ≠ dmap φ.symm e' := by
    intro h_eq
    apply hne
    have : dmap φ (dmap φ.symm f') = dmap φ (dmap φ.symm e') := by rw [h_eq]
    simpa [h_dmap_symm] using this
  have hR_ef := hR (dmap φ.symm e') (dmap φ.symm f') hfst' hne'
  have h_rot_snd : (R.rot (dmap φ.symm e')).snd = φ.symm (R'.rot e').snd := by
    calc
      (R.rot (dmap φ.symm e')).snd = φ.symm (φ ((R.rot (dmap φ.symm e')).snd)) := by simp
      _ = φ.symm ((dmap φ (R.rot (dmap φ.symm e'))).snd) := rfl
      _ = φ.symm ((R'.rot e').snd) := by rw [← h_rot_eq]
  rw [h_rot_snd] at hR_ef
  simpa [dmap] using hR_ef

theorem strictSupportFace_iso (R : RotSys G) (R' : RotSys G') (φ : G ≃g G')
    (hφ : ∀ e, dmap φ (R.rot e) = R'.rot (dmap φ e)) (x : V → E3) (hS : StrictSupportFace R x) :
    StrictSupportFace R' (fun v' => x (φ.symm v')) := by
  intro e' n hne1 hne2
  set e := dmap φ.symm e' with he
  have hde : dmap φ e = e' := by
    dsimp [e]
    ext <;> simp [dmap]
  have hface_eq : dmap φ ((R.face ^ n) e) = (R'.face ^ n) e' := by
    rw [dmap_face_pow R R' φ hφ e n, hde]
  have hRface_ne_e : (R.face ^ n) e ≠ e := by
    intro h
    apply hne1
    calc
      (R'.face ^ n) e' = dmap φ ((R.face ^ n) e) := by symm; exact hface_eq
      _ = dmap φ e := by rw [h]
      _ = e' := hde
  have hφ_symm (d : G.Dart) : dmap φ (R.rot.symm d) = R'.rot.symm (dmap φ d) := by
    have h := hφ (R.rot.symm d)
    -- h: dmap φ (R.rot (R.rot.symm d)) = R'.rot (dmap φ (R.rot.symm d))
    -- simplify LHS using Equiv.apply_symm_apply
    have h' := congrArg R'.rot.symm h
    -- h': R'.rot.symm (dmap φ (R.rot (R.rot.symm d))) = dmap φ (R.rot.symm d)
    simpa [Equiv.apply_symm_apply] using h'.symm
  have hsymm_dmap (d : G.Dart) : (dmap φ d).symm = dmap φ (d.symm) := by
    ext <;> simp [dmap]
  have hface_dmap (d : G.Dart) : dmap φ (R.face d) = R'.face (dmap φ d) := by
    calc
      dmap φ (R.face d) = dmap φ (R.rot.symm (d.symm)) := rfl
      _ = R'.rot.symm (dmap φ (d.symm)) := hφ_symm (d.symm)
      _ = R'.rot.symm ((dmap φ d).symm) := by rw [hsymm_dmap]
      _ = R'.face (dmap φ d) := rfl
  have hRface_ne_Rface_e : (R.face ^ n) e ≠ R.face e := by
    intro h
    apply hne2
    calc
      (R'.face ^ n) e' = dmap φ ((R.face ^ n) e) := by symm; exact hface_eq
      _ = dmap φ (R.face e) := by rw [h]
      _ = R'.face (dmap φ e) := by rw [hface_dmap]
      _ = R'.face e' := by rw [hde]
  have hinner : ⟪cross ((fun v' => x (φ.symm v')) e'.fst) ((fun v' => x (φ.symm v')) e'.snd),
      (fun v' => x (φ.symm v')) ((R'.face ^ n) e').fst⟫ =
      ⟪cross (x e.fst) (x e.snd), x ((R.face ^ n) e).fst⟫ := by
    have hfst : ((R'.face ^ n) e').fst = φ (((R.face ^ n) e).fst) := by
      calc
        ((R'.face ^ n) e').fst = (dmap φ ((R.face ^ n) e)).fst := by rw [← hface_eq]
        _ = φ (((R.face ^ n) e).fst) := by simp [dmap]
    calc
      ⟪cross (x (φ.symm e'.fst)) (x (φ.symm e'.snd)), x (φ.symm ((R'.face ^ n) e').fst)⟫
          = ⟪cross (x e.fst) (x e.snd), x (φ.symm ((R'.face ^ n) e').fst)⟫ := by
        simp [e, dmap]
      _ = ⟪cross (x e.fst) (x e.snd), x (φ.symm (φ (((R.face ^ n) e).fst)))⟫ := by rw [hfst]
      _ = ⟪cross (x e.fst) (x e.snd), x ((R.face ^ n) e).fst⟫ := by simp
  rw [hinner]
  exact hS e n hRface_ne_e hRface_ne_Rface_e

end Iso

section Mirror

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem cross_neg_neg (a b : E3) : cross (-a) (-b) = cross a b := by
  simp [cross]

theorem ocorner_neg (v a b : E3) : ocorner (-v) (-a) (-b) = ocorner v b a := by
  unfold ocorner
  have h_tdir_neg : ∀ (x y : E3), tdir (-x) (-y) = -tdir x y := by
    intro x y
    unfold tdir
    simp
    abel
  have h_tdir_a : tdir (-v) (-a) = -tdir v a := h_tdir_neg v a
  have h_tdir_b : tdir (-v) (-b) = -tdir v b := h_tdir_neg v b
  have h_cross_neg : ∀ (x y : E3), cross (-x) (-y) = cross x y := by
    intro x y
    unfold cross
    simp [map_neg]
  have h_inner1 : ⟪tdir (-v) (-a), tdir (-v) (-b)⟫ = ⟪tdir v a, tdir v b⟫ := by
    rw [h_tdir_a, h_tdir_b]
    simp
  have h_inner2 : ⟪-v, cross (tdir (-v) (-a)) (tdir (-v) (-b))⟫ = -⟪v, cross (tdir v a) (tdir v b)⟫ := by
    rw [h_tdir_a, h_tdir_b, h_cross_neg (tdir v a) (tdir v b)]
    simp
  have h_cross_swap : cross (tdir v b) (tdir v a) = -cross (tdir v a) (tdir v b) := by
    unfold cross
    have h := cross_anticomm' (tdir v a) (tdir v b)
    -- h: crossProduct (tdir v a) (tdir v b) + crossProduct (tdir v b) (tdir v a) = 0
    -- So crossProduct (tdir v b) (tdir v a) = -(crossProduct (tdir v a) (tdir v b))
    have h' : ofLp (tdir v b) ⨯₃ ofLp (tdir v a) = -(ofLp (tdir v a) ⨯₃ ofLp (tdir v b)) := by
      exact eq_neg_of_add_eq_zero_right h
    rw [h']
    set f := crossProduct (tdir v a).ofLp with hf
    set x := (tdir v b).ofLp with hx
    have h_neg : (-f) x = -(f x) := by rfl
    calc
      toLp 2 (-f x) = toLp 2 ((-f) x) := by rfl
      _ = toLp 2 (-(f x)) := by rw [h_neg]
      _ = -(toLp 2 (f x)) := by simp
  have h_complex : (⟨⟪tdir (-v) (-a), tdir (-v) (-b)⟫, ⟪-v, cross (tdir (-v) (-a)) (tdir (-v) (-b))⟫⟩ : ℂ) =
                   (⟨⟪tdir v b, tdir v a⟫, ⟪v, cross (tdir v b) (tdir v a)⟫⟩ : ℂ) := by
    rw [h_inner1, h_inner2]
    rw [real_inner_comm (tdir v b) (tdir v a)]
    rw [h_cross_swap]
    simp
  have h_arg_eq : Complex.arg (⟨⟪tdir (-v) (-a), tdir (-v) (-b)⟫, ⟪-v, cross (tdir (-v) (-a)) (tdir (-v) (-b))⟫⟩ : ℂ) =
                  Complex.arg (⟨⟪tdir v b, tdir v a⟫, ⟪v, cross (tdir v b) (tdir v a)⟫⟩ : ℂ) := by
    rw [h_complex]
  rw [h_arg_eq]

theorem sdist_neg_neg (a b : E3) : sdist (-a) (-b) = sdist a b := by
  unfold sdist; rw [inner_neg_neg]

theorem isAngular_reverse (R : RotSys G) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hD : DistinctDirs G x) (hR : IsAngular R x) : IsAngular R.reverse (fun v => -x v) := by
  intro e f hfst hne
  rw [show (R.reverse.rot) = R.rot.symm from rfl]
  simp [ocorner_neg]
  set v := e.fst with hvdef
  set g := R.rot.symm e with hgdef
  have hgfst : g.fst = v := by
    simpa [g, hvdef] using (R.rot_fst (R.rot.symm e)).symm
  have hfg_fst : f.fst = g.fst := by rw [hfst, hgfst]
  by_cases hfg : f = g
  · subst hfg; rfl
  · have hv_norm : ‖x v‖ = 1 := hx v
    have hg_adj : G.Adj v g.snd := by
      simpa [hgfst] using g.adj
    have hf_adj : G.Adj v f.snd := by
      simpa [hfst] using f.adj
    obtain ⟨t, ht_norm, ht_orth⟩ := exists_unit_orthogonal (x v)
    have h_ocorner_eq : ∀ (a b : G.Dart), a.fst = v → b.fst = v →
        ocorner (x v) (x a.snd) (x b.snd) = toIcoMod Real.two_pi_pos 0 (fangle (x v) t (x b.snd) - fangle (x v) t (x a.snd)) := by
      intro a b ha hb
      apply ocorner_eq_fangle_sub (x v) t (x a.snd) (x b.snd) hv_norm ht_norm ht_orth
      · have ha_adj : G.Adj v a.snd := by simpa [ha] using a.adj
        exact hD.1 v a.snd ha_adj
      · have hb_adj : G.Adj v b.snd := by simpa [hb] using b.adj
        exact hD.1 v b.snd hb_adj
    set θ := fun (h : G.Dart) => fangle (x v) t (x h.snd) with hθdef
    have h_ocorner_g_e : ocorner (x v) (x g.snd) (x e.snd) = toIcoMod Real.two_pi_pos 0 (θ e - θ g) := by
      rw [h_ocorner_eq g e hgfst (by simp [hvdef])]
    have h_ocorner_f_e : ocorner (x v) (x f.snd) (x e.snd) = toIcoMod Real.two_pi_pos 0 (θ e - θ f) := by
      rw [h_ocorner_eq f e hfst (by simp [hvdef])]
    rw [h_ocorner_g_e, h_ocorner_f_e]
    set α := fun h => toIcoMod Real.two_pi_pos 0 (θ e - θ h) with hαdef
    have hRgf : α g ≤ toIcoMod Real.two_pi_pos 0 (θ f - θ g) := by
      have h := hR g f hfg_fst hfg
      have hL := h_ocorner_g_e
      have hR' : ocorner (x v) (x g.snd) (x f.snd) = toIcoMod Real.two_pi_pos 0 (θ f - θ g) := by
        rw [h_ocorner_eq g f hgfst hfst]
      simpa [g, hgfst, hgdef, hL, hR'] using h
    have hαf_nonneg : 0 ≤ α f := by
      have hmem := toIcoMod_mem_Ico Real.two_pi_pos 0 (θ e - θ f)
      rcases Set.mem_Ico.mp hmem with ⟨hlo, _⟩
      exact hlo
    have hαg_lt_2pi : α g < 2 * π := by
      have hmem := toIcoMod_mem_Ico Real.two_pi_pos 0 (θ e - θ g)
      rcases Set.mem_Ico.mp hmem with ⟨_, hhi⟩
      simpa [add_zero] using hhi
    by_cases h_lt : α f < α g
    · have h_eq : toIcoMod Real.two_pi_pos 0 (θ f - θ g) = α g - α f := by
        have hXsubY : θ f - θ g = (θ e - θ g) - (θ e - θ f) := by ring
        rw [hXsubY]
        rw [toIcoMod_eq_iff Real.two_pi_pos]
        constructor
        · rw [Set.mem_Ico]
          constructor
          · linarith
          · linarith
        · have hαg_val : α g = toIcoMod Real.two_pi_pos 0 (θ e - θ g) := rfl
          have hαf_val : α f = toIcoMod Real.two_pi_pos 0 (θ e - θ f) := rfl
          rcases (toIcoMod_eq_iff Real.two_pi_pos).mp hαg_val with ⟨_, ⟨z, hz⟩⟩
          rcases (toIcoMod_eq_iff Real.two_pi_pos).mp hαf_val with ⟨_, ⟨z', hz'⟩⟩
          use z - z'
          calc
            (θ e - θ g) - (θ e - θ f) = (α g + z • (2 * π)) - (α f + z' • (2 * π)) := by rw [hz, hz']
            _ = (α g - α f) + (z - z') • (2 * π) := by ring
      rw [h_eq] at hRgf
      have hαf_pos : 0 < α f := by
        by_contra! hle
        have hαf_zero : α f = 0 := by linarith
        have hzero : toIcoMod Real.two_pi_pos 0 (θ e - θ f) = 0 := by
          dsimp [α] at hαf_zero
          simpa using hαf_zero
        rcases (toIcoMod_eq_iff Real.two_pi_pos).mp hzero with ⟨_, ⟨z, hz⟩⟩
        have hθ_eq : θ f - θ e = (-z) • (2 * π) := by
          calc
            θ f - θ e = -(θ e - θ f) := by ring
            _ = -(0 + z • (2 * π)) := by rw [hz]
            _ = (-z) • (2 * π) := by ring
        have h_ocorner_ef : ocorner (x v) (x e.snd) (x f.snd) = toIcoMod Real.two_pi_pos 0 (θ f - θ e) := by
          rw [h_ocorner_eq e f (by simp [hvdef]) hfst]
        have hzero_ef : toIcoMod Real.two_pi_pos 0 (θ f - θ e) = 0 := by
          rw [hθ_eq]
          apply (toIcoMod_eq_iff Real.two_pi_pos).mpr
          constructor
          · constructor <;> linarith
          · use -z; ring
        have hD2 := hD.2 v e.snd f.snd (by simpa [hvdef] using e.adj) (by simpa [hfst] using f.adj)
          (by
            intro h
            apply hne
            ext <;> simp [h, hfst, hvdef])
        rw [h_ocorner_ef, hzero_ef] at hD2
        exact hD2 rfl
      linarith
    · linarith

theorem strictSupportFace_reverse (R : RotSys G) (x : V → E3)
    (hS : StrictSupportFace R x) : StrictSupportFace R.reverse (fun v => -x v) := by
  classical
  intro e n h1 h2
  have hface_fst : ∀ d : G.Dart, (R.face d).fst = d.snd := by
    intro d
    have h := R.rot_fst (R.rot.symm d.symm)
    rw [Equiv.apply_symm_apply] at h
    simpa [RotSys.face] using h.symm
  set f := e.symm with hf
  set g := (R.face ^ n).symm f with hg
  have hpow : (R.reverse.face ^ n) e = g.symm := RotSys.reverse_face_pow R e n
  have hface : R.reverse.face e = (R.face.symm f).symm := by
    have := RotSys.reverse_face_pow R e 1
    simpa [pow_one] using this
  rw [hpow] at h1 h2 ⊢
  rw [hface] at h2
  have hgf : g ≠ f := fun h => h1 (by rw [h, hf, SimpleGraph.Dart.symm_symm])
  have hgf' : g ≠ R.face.symm f := fun h => h2 (by rw [h])
  have ho := orderOf_pos R.face
  have hopow : R.face ^ orderOf R.face = 1 := pow_orderOf_eq_one R.face
  set o := orderOf R.face
  have hmn : (R.face ^ (o * n - n)) f = g := by
    rw [hg]
    apply (R.face ^ n).injective
    rw [Equiv.apply_symm_apply, ← Equiv.Perm.mul_apply, ← pow_add,
      Nat.add_sub_cancel' (Nat.le_mul_of_pos_left n ho), pow_mul, hopow, one_pow,
      Equiv.Perm.one_apply]
  have hk : (R.face ^ (o * n - n + 1)) f = R.face g := by
    rw [pow_succ', Equiv.Perm.mul_apply, hmn]
  have hS' := hS f (o * n - n + 1)
    (by
      rw [hk]
      intro h
      apply hgf'
      rw [← h, Equiv.symm_apply_apply])
    (by
      rw [hk]
      intro h
      exact hgf (R.face.injective h))
  rw [hk, hface_fst] at hS'
  have hfst : f.fst = e.snd := rfl
  have hsnd : f.snd = e.fst := rfl
  rw [hfst, hsnd] at hS'
  have hanti : cross (x e.snd) (x e.fst) = -cross (x e.fst) (x e.snd) := by
    unfold cross
    rw [← _root_.cross_anticomm]
    rfl
  rw [hanti, inner_neg_left] at hS'
  have hgs : g.symm.fst = g.snd := rfl
  simp only [cross, hgs, inner_neg_right] at hS' ⊢
  have hneg : ∀ a b : EuclideanSpace ℝ (Fin 3),
      WithLp.toLp 2 ((-a).ofLp ⨯₃ (-b).ofLp) = WithLp.toLp 2 (a.ofLp ⨯₃ b.ofLp) := by
    intro a b
    simp
  rw [hneg]
  linarith

theorem inside_reverse (R : RotSys G) (x : V → E3) (b : G.Dart) (p : E3)
    (h : ∀ j : ℕ, 0 < ⟪cross (x ((R.face ^ j) b).fst) (x ((R.face ^ j) b).snd), p⟫) (j : ℕ) :
    0 < ⟪cross (-x ((R.reverse.face ^ j) b.symm).fst) (-x ((R.reverse.face ^ j) b.symm).snd),
      -p⟫ := by
  classical
    -- Using R.reverse_face_pow to rewrite the goal
    have hface_pow := R.reverse_face_pow b.symm j
    -- hface_pow : (R.reverse.face ^ j) b.symm = ((R.face ^ j).symm (b.symm).symm).symm
    -- Simplify: (b.symm).symm = b
    have hface_pow' : (R.reverse.face ^ j) b.symm = ((R.face ^ j).symm b).symm := by
      simpa using hface_pow
    rw [hface_pow']
    -- Goal: 0 < ⟪cross (-x (((R.face ^ j).symm b).symm).fst) (-x (((R.face ^ j).symm b).symm).snd), -p⟫
    set c := (R.face ^ j).symm b with hc_def
    -- Dart.symm swaps fst and snd
    have h_symm_fst : (c.symm).fst = c.snd := rfl
    have h_symm_snd : (c.symm).snd = c.fst := rfl
    rw [h_symm_fst, h_symm_snd]
    -- Goal: 0 < ⟪cross (-x c.snd) (-x c.fst), -p⟫
    rw [cross_neg_neg (x c.snd) (x c.fst)]
    -- Goal: 0 < ⟪cross (x c.snd) (x c.fst), -p⟫
    -- Antisymmetry of cross: cross a b = -cross b a
    have h_cross_anti : cross (x c.snd) (x c.fst) = -cross (x c.fst) (x c.snd) := by
      unfold cross
      have h := _root_.cross_anticomm (ofLp (x c.snd)) (ofLp (x c.fst))
      -- h : -(crossProduct (ofLp (x c.snd))) (ofLp (x c.fst)) = (crossProduct (ofLp (x c.fst))) (ofLp (x c.snd))
      -- So (crossProduct (ofLp (x c.snd))) (ofLp (x c.fst)) = -((crossProduct (ofLp (x c.fst))) (ofLp (x c.snd)))
      have h' : (crossProduct (ofLp (x c.snd))) (ofLp (x c.fst)) = -((crossProduct (ofLp (x c.fst))) (ofLp (x c.snd))) := by
        have := congrArg (fun f : Fin 3 → ℝ => -f) h
        simpa [neg_neg] using this
      calc
        toLp 2 ((crossProduct (ofLp (x c.snd))) (ofLp (x c.fst)))
            = toLp 2 (-((crossProduct (ofLp (x c.fst))) (ofLp (x c.snd)))) := by rw [h']
        _ = -toLp 2 ((crossProduct (ofLp (x c.fst))) (ofLp (x c.snd))) := by rw [toLp_neg]
    rw [h_cross_anti]
    -- Goal: 0 < ⟪-cross (x c.fst) (x c.snd), -p⟫
    rw [inner_neg_left, inner_neg_right]
    -- Goal: 0 < -(-⟪cross (x c.fst) (x c.snd), p⟫)
    simp
    -- Goal: 0 < ⟪cross (x c.fst) (x c.snd), p⟫
    -- Now we need to relate c.fst, c.snd to (R.face ^ m) b for some m
    -- c = (R.face ^ j).symm b, and R.face has finite order
    -- Prove SameCycle by induction on j (as a separate lemma to avoid capturing hypotheses)
    have h_same_cycle : (R.face : Equiv.Perm G.Dart).SameCycle b c := by
      rw [hc_def]
      -- Use a separate induction that doesn't capture the outer context
      refine Nat.rec ?_ (fun k ih => ?_) j
      · -- j = 0: (R.face ^ 0).symm b = b
        simp
        exact Equiv.Perm.SameCycle.refl (R.face : Equiv.Perm G.Dart) b
      · -- j = k+1: (R.face ^ (k+1)).symm = (R.face ^ k * R.face).symm = R.face.symm * (R.face ^ k).symm
        rw [pow_succ]
        -- Goal: SameCycle b ((R.face ^ k * R.face).symm b)
        -- ((R.face ^ k * R.face).symm) b = (R.face.symm * (R.face ^ k).symm) b = R.face.symm ((R.face ^ k).symm b)
        have h_symm_mul : ((R.face : Equiv.Perm G.Dart) ^ k * R.face).symm = R.face.symm * ((R.face : Equiv.Perm G.Dart) ^ k).symm := by
          rfl
        rw [h_symm_mul]
        -- Goal: SameCycle b (R.face.symm ((R.face ^ k).symm b))
        -- By SameCycle.symm_apply_right applied to ih
        exact ih.symm_apply_right
    -- Now use SameCycle.exists_nat_pow_eq to get m
    obtain ⟨m, hm_eq⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h_same_cycle
    -- hm_eq : (R.face ^ m) b = c
    rw [← hm_eq]
    -- Goal: 0 < ⟪cross (x ((R.face ^ m) b).fst) (x ((R.face ^ m) b).snd), p⟫
    exact h m

end Mirror

/-! ## Plane graphs, cases and realisations -/

/-- The plane graph with the reversed rotation system. -/
abbrev PlaneGraph.reverse (P : PlaneGraph) : PlaneGraph := ⟨P.n, P.G, P.R.reverse⟩

/-- The hexagons of a case, for the reversed rotation system: the reversed base darts. -/
def HexChoice.reverse {P : PlaneGraph} {k : ℕ} (H : HexChoice P k) : HexChoice P.reverse k where
  base m := (H.base m).symm
  hex m := by
    show Function.minimalPeriod P.R.reverse.face (H.base m).symm = 6
    rw [RotSys.reverse_minimalPeriod, SimpleGraph.Dart.symm_symm]
    exact H.hex m
  distinct m m' h := H.distinct m m' (by
    have h' := (RotSys.reverse_sameCycle P.R _ _).mp h
    simpa only [SimpleGraph.Dart.symm_symm] using h')

/-- The hexagons of a case, carried along an isomorphism of rotation systems. -/
def HexChoice.map {P P' : PlaneGraph} {k : ℕ} (H : HexChoice P k) (φ : P.G ≃g P'.G)
    (hφ : ∀ e, dmap φ (P.R.rot e) = P'.R.rot (dmap φ e)) : HexChoice P' k where
  base m := dmap φ (H.base m)
  hex m := by rw [dmap_minimalPeriod P.R P'.R φ hφ]; exact H.hex m
  distinct m m' h := H.distinct m m' ((dmap_sameCycle P.R P'.R φ hφ _ _).mp h)

theorem inClass_reverse {P : PlaneGraph} (hP : InClass P) : InClass P.reverse := by
  obtain ⟨h3, hdeg, hfs, hsph⟩ := hP
  refine ⟨h3, hdeg, fun e => ?_, ?_⟩
  · show 3 ≤ Function.minimalPeriod P.R.reverse.face e ∧
      Function.minimalPeriod P.R.reverse.face e ≤ 6
    rw [RotSys.reverse_minimalPeriod]
    exact hfs e.symm
  · show P.R.reverse.Spherical
    unfold RotSys.Spherical at hsph ⊢
    rw [RotSys.reverse_faceCount]
    exact hsph

theorem inClass_iso {P P' : PlaneGraph} (φ : P.G ≃g P'.G)
    (hφ : ∀ e, dmap φ (P.R.rot e) = P'.R.rot (dmap φ e)) (hP : InClass P) : InClass P' := by
  obtain ⟨h3, hdeg, hfs, hsph⟩ := hP
  refine ⟨iso_kConnected φ 3 h3, fun a => ?_, fun e => ?_, iso_spherical P.R P'.R φ hφ hsph⟩
  · have h := iso_degree φ (φ.symm a)
    rw [RelIso.apply_symm_apply] at h
    rw [h]; exact hdeg _
  · rw [← dmap_dmap_symm φ e, dmap_minimalPeriod P.R P'.R φ hφ]
    exact hfs _

theorem realisation_reverse {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ}
    {x : Pts P k → E3} (hx : Realisation P H d x) :
    Realisation P.reverse H.reverse d (fun a => -x a) where
  d_mem := hx.d_mem
  unit a := by rw [norm_neg]; exact hx.unit a
  edge v w h := by rw [sdist_neg_neg]; exact hx.edge v w h
  angular := by
    have hD : DistinctDirs P.G (fun v => x (.inl v)) :=
      distinctDirs_of_sep ⟨hx.d_mem.1, by linarith [hx.d_mem.2, Real.pi_pos]⟩ (fun v => x (.inl v))
        (fun v => hx.unit _) (fun v w h => hx.sep (.inl v) (.inl w) (by simpa using h))
        (fun v w h => hx.edge v w h)
    exact isAngular_reverse P.R (fun v => x (.inl v)) (fun v => hx.unit _) hD hx.angular
  convex := strictSupportFace_reverse P.R (fun v => x (.inl v)) hx.convex
  corners e := by
    have h := hx.corners (P.R.rot.symm e)
    have hf : (P.R.rot.symm e).fst = e.fst := P.R.reverse.rot_fst e
    rw [Equiv.apply_symm_apply, hf] at h
    show alpha d ≤ ocorner (-x (.inl e.fst)) (-x (.inl e.snd)) (-x (.inl (P.R.rot.symm e).snd)) ∧
      ocorner (-x (.inl e.fst)) (-x (.inl e.snd)) (-x (.inl (P.R.rot.symm e).snd)) < π
    rw [ocorner_neg]
    exact h
  sep a b hab := by rw [sdist_neg_neg]; exact hx.sep a b hab
  inside m j :=
    inside_reverse P.R (fun v => x (.inl v)) (H.base m) (x (.inr m)) (fun j => hx.inside m j) j

theorem realisation_iso {P P' : PlaneGraph} (φ : P.G ≃g P'.G)
    (hφ : ∀ e, dmap φ (P.R.rot e) = P'.R.rot (dmap φ e)) {k : ℕ} {H : HexChoice P k} {d : ℝ}
    {x : Pts P k → E3} (hx : Realisation P H d x) :
    Realisation P' (H.map φ hφ) d (fun a => x (Sum.map φ.symm id a)) where
  d_mem := hx.d_mem
  unit a := hx.unit _
  edge v w h := hx.edge _ _ (φ.symm.map_adj_iff.mpr h)
  angular := isAngular_iso P.R P'.R φ hφ (fun v => x (.inl v)) hx.angular
  convex := strictSupportFace_iso P.R P'.R φ hφ (fun v => x (.inl v)) hx.convex
  corners e' := by
    obtain ⟨e, rfl⟩ : ∃ e, dmap φ e = e' := ⟨dmap φ.symm e', dmap_dmap_symm φ e'⟩
    have hr : P'.R.rot (dmap φ e) = dmap φ (P.R.rot e) := (hφ e).symm
    have h := hx.corners e
    rw [hr]
    simpa only [Sum.map_inl, dmap, RelIso.symm_apply_apply] using h
  sep a b hab := hx.sep _ _ (fun h => hab ((Sum.map_injective.mpr ⟨φ.symm.injective,
    Function.injective_id⟩) h))
  inside m j := by
    have h := hx.inside m j
    show 0 < ⟪cross (x (.inl (φ.symm ((P'.R.face ^ j) (dmap φ (H.base m))).fst)))
      (x (.inl (φ.symm ((P'.R.face ^ j) (dmap φ (H.base m))).snd))), x (.inr m)⟫
    rw [← dmap_face_pow P.R P'.R φ hφ]
    simpa [dmap] using h

/-- Transport of the class and of a realisation to an isomorphic plane graph (orientation kept or
reversed). -/
theorem realisation_transport {P P' : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ}
    {x : Pts P k → E3} (hP : InClass P) (hiso : P.R.IsoRefl P'.R) (hx : Realisation P H d x) :
    InClass P' ∧ ∃ (H' : HexChoice P' k) (x' : Pts P' k → E3), Realisation P' H' d x' := by
  obtain ⟨φ, hA | hB⟩ := hiso
  · exact ⟨inClass_iso φ hA hP, H.map φ hA, _, realisation_iso φ hA hx⟩
  · have hA' : ∀ e, dmap φ (P.reverse.R.rot e) = P'.R.rot (dmap φ e) := by
      intro e
      have h := hB (P.R.rot.symm e)
      rw [Equiv.apply_symm_apply] at h
      rw [h, Equiv.apply_symm_apply]
      rfl
    exact ⟨inClass_iso (P := P.reverse) φ hA' (inClass_reverse hP), H.reverse.map φ hA', _,
      realisation_iso (P := P.reverse) φ hA' (realisation_reverse hx)⟩

end Tammes15
