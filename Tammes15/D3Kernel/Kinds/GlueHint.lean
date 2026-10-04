import Tammes15.D3Kernel.Kinds.Frames
import Tammes15.D3Kernel.Kinds.Cover

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Tammes15.PaperSteps Real
open scoped Classical

def lhB (lh i : ℕ) : ℕ := bits lh (8 * i) 8

def lhW (lh w : ℕ) : ℕ := bits lh (512 + 64 * w) 64

def gK : ℕ := 60

def angQ (lh α : ℕ) : ℕ := lhW lh (4 * α)

def angA (lh α : ℕ) : ℤ := (lhW lh (4 * α + 1) : ℤ)

noncomputable def cen (lh α : ℕ) : ℝ := angR gK (angQ lh α) (angA lh α)

section Glue

variable {g : ℕ}

def dartOf (s : Sol g) (hD : 0 < Ctx.D g) (i : ℕ) : s.P.G.Dart := s.lab.symm ⟨i % Ctx.D g, Nat.mod_lt _ hD⟩

def vertOf (s : Sol g) (hn : 0 < s.P.n) (v : ℕ) : Fin s.P.n := ⟨v % s.P.n, Nat.mod_lt _ hn⟩

def glueOf (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) (lh : ℕ) : GlueData s.P (Ctx.k g) where
  root := vertOf s hn (lhB lh 1)
  rootDart := dartOf s hD (lhB lh 2)
  par v := dartOf s hD (lhB lh (3 + v))
  depth v := lhB lh (19 + v)
  freeCorner m := ⟨lhB lh (35 + m) % 6, Nat.mod_lt _ (by norm_num)⟩

def glueOK (c : GCode) (n lh : ℕ) : Bool :=
  decide (0 < c.D) && decide (lhB lh 1 < n) && decide (lhB lh 2 < c.D) && c.fstAt (lhB lh 2) == lhB lh 1 &&
    lhB lh (19 + lhB lh 1) == 0 &&
    allBelow (fun v => v == lhB lh 1 || (decide (lhB lh (3 + v) < c.D) && c.fstAt (c.faceAt (lhB lh (3 + v))) == v &&
      lhB lh (19 + c.fstAt (lhB lh (3 + v))) + 1 == lhB lh (19 + v))) n

theorem sol_n (s : Sol g) {n : ℕ} (h : vertsOK (Ctx.code g) n = true) : s.P.n = n := by
  obtain ⟨h1, h2⟩ := vertsOK_spec h
  have hle := n_le_of_matches s.hm h2
  by_contra hne
  exact not_relSys_of_lt s.hm h1 (lt_of_le_of_ne hle (Ne.symm hne)) s.H s.A s.hR

theorem lab_dartOf (s : Sol g) (hD : 0 < Ctx.D g) {i : ℕ} (hi : i < Ctx.D g) :
    ((s.lab (dartOf s hD i) : Fin (Ctx.D g)) : ℕ) = i := by
  simp [dartOf, Nat.mod_eq_of_lt hi]

theorem dartOf_fst (s : Sol g) (hD : 0 < Ctx.D g) {i : ℕ} (hi : i < Ctx.D g) :
    ((dartOf s hD i).fst : ℕ) = (Ctx.code g).fstAt i := by
  have h : (Ctx.code g).fstAt ((s.lab (dartOf s hD i) : Fin (Ctx.D g)) : ℕ) = ((dartOf s hD i).fst : ℕ) :=
    s.hm.fst _
  rw [lab_dartOf s hD hi] at h
  exact h.symm

theorem dartOf_snd (s : Sol g) (hD : 0 < Ctx.D g) {i : ℕ} (hi : i < Ctx.D g) :
    ((dartOf s hD i).snd : ℕ) = (Ctx.code g).fstAt ((Ctx.code g).faceAt i) := by
  have h1 : (Ctx.code g).faceAt ((s.lab (dartOf s hD i) : Fin (Ctx.D g)) : ℕ) =
      ((s.lab (s.P.R.face (dartOf s hD i)) : Fin (Ctx.D g)) : ℕ) := s.hm.face _
  have h2 : (Ctx.code g).fstAt ((s.lab (s.P.R.face (dartOf s hD i)) : Fin (Ctx.D g)) : ℕ) =
      ((s.P.R.face (dartOf s hD i)).fst : ℕ) := s.hm.fst _
  rw [face_fst'] at h2
  rw [lab_dartOf s hD hi] at h1
  rw [← h2, ← h1]

theorem glueOf_valid (s : Sol g) {n lh : ℕ} (hn' : s.P.n = n) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g)
    (h : glueOK (Ctx.code g) n lh = true) : (glueOf s hn hD lh).Valid := by
  simp only [glueOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelow_iff, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, hr⟩, hrd⟩, hrf⟩, hdr⟩, hv⟩ := h
  subst hn'
  have hrmod : lhB lh 1 % s.P.n = lhB lh 1 := Nat.mod_eq_of_lt hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    show ((dartOf s hD (lhB lh 2)).fst : ℕ) = lhB lh 1 % s.P.n
    rw [dartOf_fst s hD hrd, hrf, hrmod]
  · show lhB lh (19 + (lhB lh 1 % s.P.n)) = 0
    rw [hrmod, hdr]
  · intro v hne
    rcases hv v v.isLt with h1 | ⟨⟨h1, h2⟩, -⟩
    · exact absurd (Fin.ext (by show (v : ℕ) = lhB lh 1 % s.P.n; rw [hrmod]; exact h1)) hne
    · apply Fin.ext
      show ((dartOf s hD (lhB lh (3 + v))).snd : ℕ) = v
      rw [dartOf_snd s hD h1, h2]
  · intro v hne
    rcases hv v v.isLt with h1 | ⟨⟨h1, -⟩, h3⟩
    · exact absurd (Fin.ext (by show (v : ℕ) = lhB lh 1 % s.P.n; rw [hrmod]; exact h1)) hne
    · show lhB lh (19 + ((dartOf s hD (lhB lh (3 + v))).fst : ℕ)) + 1 = lhB lh (19 + v)
      rw [dartOf_fst s hD h1, h3]

end Glue

def frameI (c : GCode) (lh : ℕ) : ℕ → ℕ → M3
  | 0, _ => M3.one
  | t + 1, v =>
    if v = lhB lh 1 then M3.one
    else (frameI c lh t (c.fstAt (lhB lh (3 + v)))).mul
      (stepI gK (angQ lh (1 + v)) (angA lh (1 + v)) (angQ lh 0) (angA lh 0))

def frameQ (c : GCode) (lh : ℕ) : ℕ → ℕ → ℤ
  | 0, _ => 1
  | t + 1, v =>
    if v = lhB lh 1 then 1
    else frameQ c lh t (c.fstAt (lhB lh (3 + v))) * (angDen gK (angA lh (1 + v)) * angDen gK (angA lh 0))

theorem frameQ_pos (c : GCode) (lh : ℕ) : ∀ t v, 0 < frameQ c lh t v := by
  intro t
  induction t with
  | zero => intro v; simp [frameQ]
  | succ t ih =>
    intro v
    unfold frameQ
    split_ifs
    · exact one_pos
    · exact mul_pos (ih _) (mul_pos (angDen_pos _ _) (angDen_pos _ _))

theorem frameAng_eq {g : ℕ} (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) {lh : ℕ}
    (hr : lhB lh 1 < s.P.n) (hpar : ∀ v : Fin s.P.n, v ≠ (glueOf s hn hD lh).root → lhB lh (3 + v) < Ctx.D g) :
    ∀ t (v : Fin s.P.n), frameAng (glueOf s hn hD lh) (fun v => cen lh (1 + v)) (cen lh 0) t v =
      (1 / (frameQ (Ctx.code g) lh t v : ℝ)) • (frameI (Ctx.code g) lh t v).toMat := by
  intro t
  induction t with
  | zero => intro v; simp [frameAng, frameQ, frameI, M3.toMat_one]
  | succ t ih =>
    intro v
    have hroot : (v = (glueOf s hn hD lh).root) ↔ ((v : ℕ) = lhB lh 1) := by
      constructor
      · intro h
        rw [h]
        show lhB lh 1 % s.P.n = lhB lh 1
        exact Nat.mod_eq_of_lt hr
      · intro h
        apply Fin.ext
        show (v : ℕ) = lhB lh 1 % s.P.n
        rw [Nat.mod_eq_of_lt hr]
        exact h
    by_cases hv : (v : ℕ) = lhB lh 1
    · have hv' := hroot.2 hv
      rw [frameAng, ite_eq_left hv', frameQ, frameI, ite_eq_left hv, ite_eq_left hv, M3.toMat_one]
      simp
    · have hv' : v ≠ (glueOf s hn hD lh).root := fun h => hv (hroot.1 h)
      have hp := hpar v hv'
      have hfst : (((glueOf s hn hD lh).par v).fst : ℕ) = (Ctx.code g).fstAt (lhB lh (3 + v)) :=
        dartOf_fst s hD hp
      rw [frameAng, ite_eq_right hv', frameQ, frameI, ite_eq_right hv, ite_eq_right hv, ih, hfst]
      unfold cen
      rw [stepM_angR, scaled_mul', M3.toMat_mul]
      congr 1
      push_cast
      field_simp

end Tammes15.D3Kernel.Kinds
