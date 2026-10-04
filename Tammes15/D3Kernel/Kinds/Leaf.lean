import Tammes15.D3Kernel.Kinds.LinSound
import Tammes15.PaperSteps.Search

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Pent Real
open Tammes15.PaperSteps Tammes15.PaperSteps.Search

def killChecker (ok : ℕ → ℕ → ℕ → Bool) : Checker where
  σ := Bool
  H := Unit
  init := true
  onRec _ _ _ _ := false
  onKill g box it s := s && ok g box it
  fin s _ := s
  frc s k := @Bool.rec (fun _ => List ℕ) (k false) (k true) s
  frc_eq s k := by cases s <;> rfl

theorem kill_fold (ok : ℕ → ℕ → ℕ → Bool) (hok : ∀ g box it, ok g box it = true → KillOK g box) :
    ∀ (l : List Ev) (s : Bool),
      l.foldl (fun s e => (killChecker ok).step e s) s = true → s = true ∧ ∀ e ∈ l, e.OK := by
  intro l
  induction l with
  | nil => exact fun s h => ⟨h, fun e he => by simp at he⟩
  | cons ev l ih =>
    intro s h
    change List.foldl (fun s e => (killChecker ok).step e s) ((killChecker ok).step ev s) l = true at h
    obtain ⟨h1, hl⟩ := ih _ h
    cases ev with
    | record g box it => exact absurd h1 (by change ¬ false = true; simp)
    | kill g box it =>
      change (s && ok g box it) = true at h1
      rw [Bool.and_eq_true] at h1
      refine ⟨h1.1, fun e he => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact hok g box it h1.2
      · exact hl e he

theorem killChecker_sound (ok : ℕ → ℕ → ℕ → Bool) (hok : ∀ g box it, ok g box it = true → KillOK g box)
    (adm : ℕ → Prop) : (killChecker ok).Sound adm := by
  intro tr _ _ hfin
  exact (kill_fold ok hok tr (killChecker ok).init hfin).2

theorem refuse_sound (adm : ℕ → Prop) : (killChecker fun _ _ _ => false).Sound adm :=
  killChecker_sound _ (fun _ _ _ h => absurd h (by simp)) adm

noncomputable def procs0 : Procs where
  narrow _ _ _ _ B := some B
  wheel _ _ _ _ _ := some (0, π)

theorem procs0_sound : procs0.Sound := by
  intro P k H
  refine ⟨fun m A _ B hB => ⟨B, rfl, hB⟩, fun A _ B _ m i β hβ => ?_⟩
  simp only [procs0, Option.some.injEq] at hβ
  subst hβ
  exact ⟨arccos_nonneg _, arccos_le_pi _⟩

def wheelSet {P : PlaneGraph} {k : ℕ} (B : Box (PVar P k)) (m : Fin k) (i : Fin 6) : Set ℝ :=
  {y | ∃ x z w : ℝ, (B.lo (.r m (i - 1)) ≤ x ∧ x ≤ B.hi (.r m (i - 1))) ∧ (B.lo (.r m i) ≤ z ∧ z ≤ B.hi (.r m i)) ∧
    (B.lo .d ≤ w ∧ w ≤ B.hi .d) ∧ y = gam x z w}

noncomputable def procsW : Procs where
  narrow _ _ _ _ B := some B
  wheel _ _ B m i := some (sInf (wheelSet B m i), sSup (wheelSet B m i))

theorem wheelSet_bdd {P : PlaneGraph} {k : ℕ} (B : Box (PVar P k)) (m : Fin k) (i : Fin 6) :
    BddBelow (wheelSet B m i) ∧ BddAbove (wheelSet B m i) := by
  refine ⟨⟨0, ?_⟩, ⟨π, ?_⟩⟩ <;> rintro y ⟨x, z, w, -, -, -, rfl⟩
  · exact arccos_nonneg _
  · exact arccos_le_pi _

theorem procsW_sound : procsW.Sound := by
  intro P k H
  refine ⟨fun m A _ B hB => ⟨B, rfl, hB⟩, fun A _ B hB m i β hβ => ?_⟩
  simp only [procsW, Option.some.injEq] at hβ
  subst hβ
  have hmem : gam (A.r m (i - 1)) (A.r m i) A.d ∈ wheelSet B m i :=
    ⟨_, _, _, hB (.r m (i - 1)), hB (.r m i), hB .d, rfl⟩
  exact ⟨csInf_le (wheelSet_bdd B m i).1 hmem, le_csSup (wheelSet_bdd B m i).2 hmem⟩

theorem le_sInf_wheelSet {P : PlaneGraph} {k : ℕ} {B : Box (PVar P k)} {m : Fin k} {i : Fin 6} {L : ℝ}
    (hne : (wheelSet B m i).Nonempty) (h : ∀ y ∈ wheelSet B m i, L ≤ y) : L ≤ sInf (wheelSet B m i) :=
  le_csInf hne h

theorem sSup_wheelSet_le {P : PlaneGraph} {k : ℕ} {B : Box (PVar P k)} {m : Fin k} {i : Fin 6} {U : ℝ}
    (hne : (wheelSet B m i).Nonempty) (h : ∀ y ∈ wheelSet B m i, y ≤ U) : sSup (wheelSet B m i) ≤ U :=
  csSup_le hne h

def hvB (hv n : ℕ) : ℕ := bits hv (8 * n) 8

def dOK (g w : ℕ) : Bool := Nat.blt w (Ctx.nv g) && Nat.beq (Ctx.mean g w) 1

def rOK (g w q : ℕ) : Bool := Nat.blt w (Ctx.nv g) && Nat.beq (Ctx.mean g w) (258 + q)

def vmOK (g hv : ℕ) : Bool :=
  aOK g (hvB hv 256) && dOK g (hvB hv 257) && allBelow (fun i => dvOK g (hvB hv i) i) (Ctx.D g) &&
    allBelow (fun q => rOK g (hvB hv (258 + q)) q) (6 * Ctx.k g)

def vmOf {g : ℕ} (s : Sol g) (hv : ℕ) : PVar s.P (Ctx.k g) → ℕ
  | .a => hvB hv 256
  | .c e => hvB hv (s.lab e)
  | .d => hvB hv 257
  | .r m j => hvB hv (258 + (6 * (m : ℕ) + j))

noncomputable def walkBox {P : PlaneGraph} {k : ℕ} (box : ℕ) (vm : PVar P k → ℕ) : Box (PVar P k) :=
  ⟨fun p => keyVal (bnd box (2 * vm p)), fun p => keyVal (bnd box (2 * vm p + 1))⟩

theorem sol_val_r {g : ℕ} (s : Sol g) {w : ℕ} (m : Fin (Ctx.k g)) (j : Fin 6)
    (hw : Ctx.mean g w = 258 + (6 * (m : ℕ) + j)) : Ctx.val g s.lab s.A w = s.A.r m j := by
  have hm := m.isLt
  have hj := j.isLt
  have e1 : (Ctx.mean g w - 258) / 6 = m := by omega
  have e2 : (Ctx.mean g w - 258) % 6 = j := by omega
  have hlt : (Ctx.mean g w - 258) / 6 < Ctx.k g := by omega
  have n0 : ¬ Ctx.mean g w = 0 := by omega
  have n1 : ¬ Ctx.mean g w = 1 := by omega
  have n2 : ¬ (Ctx.mean g w < 258 ∧ Ctx.mean g w - 2 < Ctx.D g) := by omega
  unfold Ctx.val
  rw [ite_eq_right n0, ite_eq_right n1, dite_eq_right n2, dite_eq_left hlt]
  have h1 : (⟨(Ctx.mean g w - 258) / 6, hlt⟩ : Fin (Ctx.k g)) = m := Fin.ext e1
  have h2 : (⟨(Ctx.mean g w - 258) % 6, Nat.mod_lt _ (by norm_num)⟩ : Fin 6) = j := Fin.ext e2
  exact congrArg₂ s.A.r h1 h2

theorem vmOf_spec {g hv : ℕ} (h : vmOK g hv = true) (s : Sol g) (p : PVar s.P (Ctx.k g)) :
    vmOf s hv p < Ctx.nv g ∧ s.x (vmOf s hv p) = PVar.val s.A p := by
  simp only [vmOK, Bool.and_eq_true, allBelow_iff] at h
  obtain ⟨⟨⟨ha, hd⟩, hc⟩, hr⟩ := h
  cases p with
  | a => exact x_of_aOK s ha
  | c e =>
    obtain ⟨hw, hi, hx⟩ := x_of_dvOK s (hc (s.lab e) (s.lab e).isLt)
    refine ⟨hw, ?_⟩
    show s.x (hvB hv (s.lab e)) = s.A.corner e
    rw [hx, Fin.eta, Equiv.symm_apply_apply]
  | d =>
    simp only [dOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hd
    refine ⟨hd.1, ?_⟩
    show Ctx.val g s.lab s.A (hvB hv 257) = s.A.d
    unfold Ctx.val
    rw [ite_eq_right (by rw [hd.2]; decide), ite_eq_left hd.2]
  | r m j =>
    have hq : 6 * (m : ℕ) + j < 6 * Ctx.k g := by have := m.isLt; have := j.isLt; omega
    have h' := hr _ hq
    simp only [rOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    show hvB hv (258 + (6 * (m : ℕ) + j)) < Ctx.nv g ∧ Ctx.val g s.lab s.A (hvB hv (258 + (6 * (m : ℕ) + j))) = s.A.r m j
    generalize hvB hv (258 + (6 * (m : ℕ) + j)) = w at h' ⊢
    refine ⟨h'.1, ?_⟩
    exact sol_val_r s m j h'.2

theorem killOK_of_leafKill {N : Procs} (hN : N.Sound) {g box hv : ℕ} (hv' : vmOK g hv = true)
    (h : ∀ s : Sol g, BoxMem (Ctx.nv g) box s.x → LeafKill N s.P s.H (walkBox box (vmOf s hv))) :
    KillOK g box := by
  intro s hs
  have hA : s.A ∈ PaperSteps.Sol s.P s.H := ⟨s.hd.1, s.hd.2, s.hR⟩
  have hB : (walkBox box (vmOf s hv)).Mem (PVar.val s.A) := by
    intro p
    obtain ⟨hlt, hx⟩ := vmOf_spec hv' s p
    rw [← hx]
    exact hs _ hlt
  exact leafKill_sound hN hA hB (h s hs)

end Tammes15.D3Kernel.Kinds
