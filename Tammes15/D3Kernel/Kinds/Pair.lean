import Tammes15.D3Kernel.Kinds.Centre
import Tammes15.D3Kernel.Kinds.Leaf

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3lp.TrigNat Tammes15.D3Kernel Tammes15.PaperSteps Real
open scoped Classical

theorem pr_col3 (A : M3) (x : ℝ) :
    (Matrix.toEuclideanLin (x • A.toMat) e3).ofLp 0 = x * A.a02 ∧ (Matrix.toEuclideanLin (x • A.toMat) e3).ofLp 1 = x * A.a12 ∧
      (Matrix.toEuclideanLin (x • A.toMat) e3).ofLp 2 = x * A.a22 := by
  simp [e3, M3.toMat, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

theorem pr_pair_norm_lt {u w : EuclideanSpace ℝ (Fin 3)} {x0 x1 x2 y0 y1 y2 Qa Qb T : ℤ} (hQa : 0 < Qa)
    (hQb : 0 < Qb) (hT : 0 < T)
    (hu : u.ofLp 0 = 1 / (Qa : ℝ) * x0 ∧ u.ofLp 1 = 1 / (Qa : ℝ) * x1 ∧ u.ofLp 2 = 1 / (Qa : ℝ) * x2)
    (hw : w.ofLp 0 = 1 / (Qb : ℝ) * y0 ∧ w.ofLp 1 = 1 / (Qb : ℝ) * y1 ∧ w.ofLp 2 = 1 / (Qb : ℝ) * y2)
    (h : ((x0 * Qb - y0 * Qa) * (x0 * Qb - y0 * Qa) + (x1 * Qb - y1 * Qa) * (x1 * Qb - y1 * Qa) +
        (x2 * Qb - y2 * Qa) * (x2 * Qb - y2 * Qa)) * ((2 ^ 128 : ℕ) : ℤ) < (T * Qa * Qb) * (T * Qa * Qb)) :
    ‖u - w‖ < (T : ℝ) / 2 ^ 64 := by
  rcases hu with ⟨hu0, hu1, hu2⟩
  rcases hw with ⟨hw0, hw1, hw2⟩
  have hQa' : (0 : ℝ) < Qa := by exact_mod_cast hQa
  have hQb' : (0 : ℝ) < Qb := by exact_mod_cast hQb
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hQa_ne : (Qa : ℝ) ≠ 0 := by linarith
  have hQb_ne : (Qb : ℝ) ≠ 0 := by linarith
  have h_nonneg_target : 0 ≤ (T : ℝ) / (2 ^ 64 : ℝ) := by positivity

  have hsub0 : (u - w).ofLp 0 = ((x0 : ℝ) * (Qb : ℝ) - (y0 : ℝ) * (Qa : ℝ)) / ((Qa : ℝ) * (Qb : ℝ)) := by
    rw [PiLp.sub_apply, hu0, hw0]
    field_simp [hQa_ne, hQb_ne]
  have hsub1 : (u - w).ofLp 1 = ((x1 : ℝ) * (Qb : ℝ) - (y1 : ℝ) * (Qa : ℝ)) / ((Qa : ℝ) * (Qb : ℝ)) := by
    rw [PiLp.sub_apply, hu1, hw1]
    field_simp [hQa_ne, hQb_ne]
  have hsub2 : (u - w).ofLp 2 = ((x2 : ℝ) * (Qb : ℝ) - (y2 : ℝ) * (Qa : ℝ)) / ((Qa : ℝ) * (Qb : ℝ)) := by
    rw [PiLp.sub_apply, hu2, hw2]
    field_simp [hQa_ne, hQb_ne]

  have h_sq_ineq : ‖u - w‖ ^ 2 < ((T : ℝ) / (2 ^ 64 : ℝ)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [Real.norm_eq_abs, sq_abs]
    rw [Fin.sum_univ_three, hsub0, hsub1, hsub2]
    set A := ((x0 : ℝ) * (Qb : ℝ) - (y0 : ℝ) * (Qa : ℝ)) ^ 2 + ((x1 : ℝ) * (Qb : ℝ) - (y1 : ℝ) * (Qa : ℝ)) ^ 2 + ((x2 : ℝ) * (Qb : ℝ) - (y2 : ℝ) * (Qa : ℝ)) ^ 2 with hA
    have h_main : A * ((2 ^ 128 : ℕ) : ℝ) < ((T : ℝ) * (Qa : ℝ) * (Qb : ℝ)) ^ 2 := by
      have h_sq : ((x0 * Qb - y0 * Qa) ^ 2 + (x1 * Qb - y1 * Qa) ^ 2 + (x2 * Qb - y2 * Qa) ^ 2) * ((2 ^ 128 : ℕ) : ℤ) < (T * Qa * Qb) ^ 2 := by
        nlinarith
      have h_cast : A = (((x0 * Qb - y0 * Qa) ^ 2 + (x1 * Qb - y1 * Qa) ^ 2 + (x2 * Qb - y2 * Qa) ^ 2 : ℤ) : ℝ) := by
        simp [hA, Int.cast_pow, Int.cast_mul, Int.cast_sub, Int.cast_add]
      rw [h_cast]
      exact mod_cast h_sq
    have h_goal : A / (((Qa : ℝ) * (Qb : ℝ)) ^ 2) < ((T : ℝ) / (2 ^ 64 : ℝ)) ^ 2 := by
      field_simp [hQa_ne, hQb_ne]
      norm_num
      have hRHS : ((↑T : ℝ) * (↑Qa : ℝ) * (↑Qb : ℝ)) ^ 2 = (↑Qa : ℝ) ^ 2 * (↑Qb : ℝ) ^ 2 * (↑T : ℝ) ^ 2 := by ring
      exact lt_of_lt_of_eq h_main hRHS

    calc
      (((x0 : ℝ) * (Qb : ℝ) - (y0 : ℝ) * (Qa : ℝ)) / ((Qa : ℝ) * (Qb : ℝ))) ^ 2 +
          (((x1 : ℝ) * (Qb : ℝ) - (y1 : ℝ) * (Qa : ℝ)) / ((Qa : ℝ) * (Qb : ℝ))) ^ 2 +
          (((x2 : ℝ) * (Qb : ℝ) - (y2 : ℝ) * (Qa : ℝ)) / ((Qa : ℝ) * (Qb : ℝ))) ^ 2
          = A / (((Qa : ℝ) * (Qb : ℝ)) ^ 2) := by
        simp [hA, div_pow]
        ring
      _ < ((T : ℝ) / (2 ^ 64 : ℝ)) ^ 2 := h_goal

  exact lt_of_pow_lt_pow_left₀ 2 h_nonneg_target h_sq_ineq

theorem pr_abs_cover (x y : ℝ) : x - |y - x| ≤ x ∧ y ≤ x + |y - x| :=
  ⟨by linarith [abs_nonneg (y - x)], by linarith [le_abs_self (y - x)]⟩

theorem pr_pair_close {y ra rb : ℝ} {S x : ℕ} {T : ℤ} (hy : y < (T : ℝ) / 2 ^ 64)
    (hT : (T : ℝ) = 4 * (S : ℝ) - ra - rb) (hS : (S : ℝ) / 2 ^ 63 ≤ Real.sin ((x : ℝ) / 2 ^ 63)) :
    y + ra / 2 ^ 64 + rb / 2 ^ 64 < 2 * Real.sin ((x : ℝ) / 2 ^ 62 / 2) := by
  have e : (x : ℝ) / 2 ^ 62 / 2 = (x : ℝ) / 2 ^ 63 := by ring
  rw [e]
  rw [hT] at hy
  have e2 : (4 * (S : ℝ) - ra - rb) / 2 ^ 64 = 2 * ((S : ℝ) / 2 ^ 63) - ra / 2 ^ 64 - rb / 2 ^ 64 := by ring
  rw [e2] at hy
  linarith

def angLb (lh α : ℕ) : ℕ := lhW lh (4 * α + 2)

def angUb (lh α : ℕ) : ℕ := lhW lh (4 * α + 3)

def cenOK (lh α : ℕ) : Bool :=
  brLo gK (lhW lh (4 * α + 1)) (angLb lh α) && brHi gK (lhW lh (4 * α + 1)) (angUb lh α)

def radA (lh α : ℕ) (lo hi : ℤ) : ℤ := radI (angQ lh α) (angLb lh α) (angUb lh α) lo hi

theorem cover_cen {lh α : ℕ} {lo hi : ℤ} (h : cenOK lh α = true) :
    cen lh α - (radA lh α lo hi : ℝ) / 2 ^ 64 ≤ (lo : ℝ) / 2 ^ 62 ∧
      (hi : ℝ) / 2 ^ 62 ≤ cen lh α + (radA lh α lo hi : ℝ) / 2 ^ 64 := by
  simp only [cenOK, Bool.and_eq_true] at h
  exact cover_angle h.1 h.2

def dKey (box hv : ℕ) : ℕ := bnd box (2 * hvB hv 257)

def dKeyH (box hv : ℕ) : ℕ := bnd box (2 * hvB hv 257 + 1)

def drI (box hv lh : ℕ) : ℤ := radA lh 0 (kfix (dKey box hv)) (kfix (dKeyH box hv))

def refI (c : GCode) (lh u : ℕ) : ℕ := if u = lhB lh 1 then lhB lh 2 else revC c (lhB lh (3 + u))

def refV (c : GCode) (lh v : ℕ) : ℕ := refI c lh (c.fstAt (lhB lh (3 + v)))

def prI (box hv : ℕ) (c : GCode) (n lh v : ℕ) : ℤ :=
  radA lh (1 + v) (turnLoZ box hv c n (refV c lh v) (lhB lh (3 + v)))
    (turnHiZ box hv c n (refV c lh v) (lhB lh (3 + v)))

def radNI (box hv : ℕ) (c : GCode) (n lh : ℕ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | t + 1, v =>
    if v = lhB lh 1 then 0
    else radNI box hv c n lh t (c.fstAt (lhB lh (3 + v))) + prI box hv c n lh v + drI box hv lh

section Encl

variable {g : ℕ}

noncomputable def enclOf (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) (box hv lh n : ℕ) :
    Encl s.P (Ctx.k g) where
  dc := cen lh 0
  dr := (drI box hv lh : ℝ) / 2 ^ 64
  pc v := cen lh (1 + v)
  pr v := (prI box hv (Ctx.code g) n lh v : ℝ) / 2 ^ 64
  qc m := turnLo (walkBox box (vmOf s hv)) ((glueOf s hn hD lh).refD (freeDart s.H (glueOf s hn hD lh) m).fst)
      (freeBack s.H (glueOf s hn hD lh) m) +
    sInf (wheelSet (walkBox box (vmOf s hv)) m ((glueOf s hn hD lh).freeCorner m))
  qr m := |turnHi (walkBox box (vmOf s hv)) ((glueOf s hn hD lh).refD (freeDart s.H (glueOf s hn hD lh) m).fst)
      (freeBack s.H (glueOf s hn hD lh) m) +
    sSup (wheelSet (walkBox box (vmOf s hv)) m ((glueOf s hn hD lh).freeCorner m)) -
      (turnLo (walkBox box (vmOf s hv)) ((glueOf s hn hD lh).refD (freeDart s.H (glueOf s hn hD lh) m).fst)
        (freeBack s.H (glueOf s hn hD lh) m) +
      sInf (wheelSet (walkBox box (vmOf s hv)) m ((glueOf s hn hD lh).freeCorner m)))|
  rc m := (walkBox box (vmOf s hv)).lo (.r m ((glueOf s hn hD lh).freeCorner m))
  rr m := |(walkBox box (vmOf s hv)).hi (.r m ((glueOf s hn hD lh).freeCorner m)) -
    (walkBox box (vmOf s hv)).lo (.r m ((glueOf s hn hD lh).freeCorner m))|

theorem radN_eq (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) {box hv lh n : ℕ} (hr : lhB lh 1 < s.P.n)
    (hpar : ∀ v : Fin s.P.n, v ≠ (glueOf s hn hD lh).root → lhB lh (3 + v) < Ctx.D g) :
    ∀ t (v : Fin s.P.n), radN (glueOf s hn hD lh) (enclOf s hn hD box hv lh n).pr
      (enclOf s hn hD box hv lh n).dr t v = (radNI box hv (Ctx.code g) n lh t v : ℝ) / 2 ^ 64 := by
  intro t
  induction t with
  | zero => intro v; simp [radN, radNI]
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
      rw [radN, ite_eq_left hv', radNI, ite_eq_left hv]
      simp
    · have hv' : v ≠ (glueOf s hn hD lh).root := fun h => hv (hroot.1 h)
      have hp := hpar v hv'
      have hfst : (((glueOf s hn hD lh).par v).fst : ℕ) = (Ctx.code g).fstAt (lhB lh (3 + v)) :=
        dartOf_fst s hD hp
      rw [radN, ite_eq_right hv', radNI, ite_eq_right hv, ih, hfst]
      simp only [enclOf]
      push_cast
      ring

theorem revC_sol (s : Sol g) (a : s.P.G.Dart) :
    revC (Ctx.code g) (s.lab a : ℕ) = s.lab a.symm := revC_lab s.hm a

theorem lab_refD (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) {lh : ℕ} (hr : lhB lh 1 < s.P.n)
    (h2 : lhB lh 2 < Ctx.D g)
    (hpar : ∀ v : Fin s.P.n, v ≠ (glueOf s hn hD lh).root → lhB lh (3 + v) < Ctx.D g) (u : Fin s.P.n) :
    ((s.lab ((glueOf s hn hD lh).refD u) : Fin (Ctx.D g)) : ℕ) = refI (Ctx.code g) lh u := by
  have hroot : (u = (glueOf s hn hD lh).root) ↔ ((u : ℕ) = lhB lh 1) := by
    constructor
    · intro h
      rw [h]
      show lhB lh 1 % s.P.n = lhB lh 1
      exact Nat.mod_eq_of_lt hr
    · intro h
      apply Fin.ext
      show (u : ℕ) = lhB lh 1 % s.P.n
      rw [Nat.mod_eq_of_lt hr]
      exact h
  unfold GlueData.refD refI
  by_cases hu : (u : ℕ) = lhB lh 1
  · rw [ite_eq_left (hroot.2 hu), ite_eq_left hu]
    exact lab_dartOf s hD h2
  · have hu' : u ≠ (glueOf s hn hD lh).root := fun h => hu (hroot.1 h)
    rw [ite_eq_right hu', ite_eq_right hu, ← revC_sol]
    show revC (Ctx.code g) ((s.lab (dartOf s hD (lhB lh (3 + u))) : Fin (Ctx.D g)) : ℕ) = _
    rw [lab_dartOf s hD (hpar u hu')]

end Encl

def nonAdjC (c : GCode) (a b : ℕ) : Bool :=
  allBelow (fun i => !(c.fstAt i == a && c.fstAt (c.faceAt i) == b)) c.D

def perOK (c : GCode) : Bool := allBelow (fun i => decide (0 < c.period i)) c.D

def pvertOK (box hv : ℕ) (c : GCode) (n lh v : ℕ) : Bool :=
  v == lhB lh 1 || (cenOK lh (1 + v) && goodAll box hv (tf c n (refV c lh v)) (degC c (refV c lh v)))

def sdI (box hv : ℕ) : ℕ := sinDn 63 nT (kfix (dKey box hv))

def pairT (box hv : ℕ) (c : GCode) (n lh : ℕ) : ℤ :=
  4 * (sdI box hv : ℤ) - radNI box hv c n lh (lhB lh (19 + lhB lh 39)) (lhB lh 39) -
    radNI box hv c n lh (lhB lh (19 + lhB lh 40)) (lhB lh 40)

def sq3 (A B : M3) (Qa Qb : ℤ) : ℤ :=
  (A.a02 * Qb - B.a02 * Qa) * (A.a02 * Qb - B.a02 * Qa) + (A.a12 * Qb - B.a12 * Qa) * (A.a12 * Qb - B.a12 * Qa) +
    (A.a22 * Qb - B.a22 * Qa) * (A.a22 * Qb - B.a22 * Qa)

def pairTest (box hv : ℕ) (c : GCode) (n lh : ℕ) : Bool :=
  decide (lhB lh 39 < n) && decide (lhB lh 40 < n) && !(lhB lh 39 == lhB lh 40) &&
    nonAdjC c (lhB lh 39) (lhB lh 40) && sinGe 63 nT (kfix (dKey box hv)) (sdI box hv) &&
    decide (0 < pairT box hv c n lh) &&
    decide (sq3 (frameI c lh (lhB lh (19 + lhB lh 39)) (lhB lh 39)) (frameI c lh (lhB lh (19 + lhB lh 40)) (lhB lh 40))
        (frameQ c lh (lhB lh (19 + lhB lh 39)) (lhB lh 39)) (frameQ c lh (lhB lh (19 + lhB lh 40)) (lhB lh 40)) *
        ((2 ^ 128 : ℕ) : ℤ) <
      (pairT box hv c n lh * frameQ c lh (lhB lh (19 + lhB lh 39)) (lhB lh 39) *
          frameQ c lh (lhB lh (19 + lhB lh 40)) (lhB lh 40)) *
        (pairT box hv c n lh * frameQ c lh (lhB lh (19 + lhB lh 39)) (lhB lh 39) *
          frameQ c lh (lhB lh (19 + lhB lh 40)) (lhB lh 40)))

def hvOf (lh : ℕ) : ℕ := lh / 2 ^ 7424

def leafPairOK (g box it : ℕ) : Bool :=
  vmOK g (hvOf it) && vertsOK (Ctx.code g) (lhB it 63) && glueOK (Ctx.code g) (lhB it 63) it &&
    perOK (Ctx.code g) && kgood (dKey box (hvOf it)) && kgood (dKeyH box (hvOf it)) && cenOK it 0 &&
    allBelow (pvertOK box (hvOf it) (Ctx.code g) (lhB it 63) it) (lhB it 63) &&
    pairTest box (hvOf it) (Ctx.code g) (lhB it 63) it

section Sound

variable {g : ℕ}

theorem not_adj (s : Sol g) {a b : Fin s.P.n} (h : nonAdjC (Ctx.code g) a b = true) : ¬ s.P.G.Adj a b := by
  intro hab
  simp only [nonAdjC, allBelow_iff] at h
  set e : s.P.G.Dart := ⟨(a, b), hab⟩
  have h1 : (Ctx.code g).fstAt ((s.lab e : Fin (Ctx.D g)) : ℕ) = (e.fst : ℕ) := s.hm.fst _
  have h2 : (Ctx.code g).faceAt ((s.lab e : Fin (Ctx.D g)) : ℕ) = ((s.lab (s.P.R.face e) : Fin (Ctx.D g)) : ℕ) :=
    s.hm.face _
  have h3 : (Ctx.code g).fstAt ((s.lab (s.P.R.face e) : Fin (Ctx.D g)) : ℕ) = ((s.P.R.face e).fst : ℕ) :=
    s.hm.fst _
  rw [face_fst'] at h3
  have hi := h _ (s.lab e).isLt
  rw [h2, h3, h1] at hi
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
  rcases hi with hi | hi <;> exact hi rfl

theorem glueOK_facts {c : GCode} {n lh : ℕ} (h : glueOK c n lh = true) :
    0 < c.D ∧ lhB lh 1 < n ∧ lhB lh 2 < c.D ∧ ∀ v < n, v ≠ lhB lh 1 → lhB lh (3 + v) < c.D := by
  simp only [glueOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelow_iff, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hD, hr⟩, h2⟩, -⟩, -⟩, hv⟩ := h
  refine ⟨hD, hr, h2, fun v hv' hne => ?_⟩
  rcases hv v hv' with h1 | ⟨⟨h1, -⟩, -⟩
  · exact absurd h1 hne
  · exact h1

theorem vertOf_val (s : Sol g) (hn : 0 < s.P.n) {x : ℕ} (hx : x < s.P.n) : ((vertOf s hn x : Fin s.P.n) : ℕ) = x :=
  Nat.mod_eq_of_lt hx

theorem leafPairOK_sound {box it : ℕ} (h : leafPairOK g box it = true) : KillOK g box := by
  simp only [leafPairOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hvm, hverts⟩, hglue⟩, hper⟩, hk1⟩, hk2⟩, hc0⟩, hall⟩, hpt⟩ := h
  rw [allBelow_iff] at hall
  simp only [perOK, allBelow_iff, decide_eq_true_eq] at hper
  simp only [pairTest, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hpt
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, hnadj⟩, hsin⟩, hT⟩, hsq⟩ := hpt
  obtain ⟨hD, hr, h2, hpar0⟩ := glueOK_facts hglue
  set n := lhB it 63 with hn_def
  set hv := hvOf it with hv_def
  apply killOK_of_leafKill procsW_sound hvm
  intro s _
  have hn' : s.P.n = n := sol_n s hverts
  have hn : 0 < s.P.n := by omega
  have hD' : 0 < Ctx.D g := hD
  have hr' : lhB it 1 < s.P.n := by omega
  set gl := glueOf s hn hD' it with hgl
  have hval : gl.Valid := glueOf_valid s hn' hn hD' hglue
  have hroot : ∀ v : Fin s.P.n, v = gl.root ↔ (v : ℕ) = lhB it 1 := by
    intro v
    constructor
    · intro h
      rw [h]
      exact Nat.mod_eq_of_lt hr'
    · intro h
      apply Fin.ext
      show (v : ℕ) = lhB it 1 % s.P.n
      rw [Nat.mod_eq_of_lt hr']
      exact h
  have hpar : ∀ v : Fin s.P.n, v ≠ gl.root → lhB it (3 + v) < Ctx.D g :=
    fun v hv' => hpar0 v (by omega) (fun h => hv' ((hroot v).2 h))
  set E := enclOf s hn hD' box hv it n with hE
  set B := walkBox box (vmOf s hv) with hB
  have hlo : B.lo .d = (kfix (dKey box hv) : ℝ) / 2 ^ 62 := keyVal_kgood hk1
  have hhi : B.hi .d = (kfix (dKeyH box hv) : ℝ) / 2 ^ 62 := keyVal_kgood hk2
  refine ⟨gl, hval, E, ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, Or.inl ?_⟩
  ·
    have hd := (cover_cen (lo := (kfix (dKey box hv) : ℤ)) (hi := (kfix (dKeyH box hv) : ℤ)) hc0).1
    rw [hlo]
    push_cast at hd
    exact hd
  · have hd := (cover_cen (lo := (kfix (dKey box hv) : ℤ)) (hi := (kfix (dKeyH box hv) : ℤ)) hc0).2
    rw [hhi]
    push_cast at hd
    exact hd
  ·
    intro v hv'
    have hvn : (v : ℕ) ≠ lhB it 1 := fun h => hv' ((hroot v).2 h)
    have hvlt : (v : ℕ) < n := by omega
    have hvo := hall v hvlt
    simp only [pvertOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hvo
    rcases hvo with hvo | ⟨hcen, hgood⟩
    · exact absurd hvo hvn
    have hp := hpar v hv'
    have hfst : ((gl.par v).fst : ℕ) = (Ctx.code g).fstAt (lhB it (3 + v)) := dartOf_fst s hD' hp
    have hlabA : ((s.lab (gl.refD (gl.par v).fst) : Fin (Ctx.D g)) : ℕ) = refV (Ctx.code g) it v := by
      rw [lab_refD s hn hD' hr' h2 hpar, hfst]
      rfl
    have hlabB : ((s.lab (gl.par v) : Fin (Ctx.D g)) : ℕ) = lhB it (3 + v) := lab_dartOf s hD' hp
    have hper' : ∀ i < Ctx.D g, 0 < (Ctx.code g).period i := hper
    have hgood' : goodAll box hv (tf (Ctx.code g) s.P.n ((s.lab (gl.refD (gl.par v).fst) : Fin (Ctx.D g)) : ℕ))
        (degC (Ctx.code g) ((s.lab (gl.refD (gl.par v).fst) : Fin (Ctx.D g)) : ℕ)) = true := by
      have hgood2 := hgood
      rw [← hn'] at hgood2
      rw [hlabA]
      exact hgood2
    have h1 := turnLo_ge s hper' (gl.refD (gl.par v).fst) (gl.par v) hgood'
    have h2' := turnHi_le s hper' (gl.refD (gl.par v).fst) (gl.par v) hgood'
    have e1 : turnLoZ box hv (Ctx.code g) s.P.n (refV (Ctx.code g) it v) (lhB it (3 + v)) =
        turnLoZ box hv (Ctx.code g) n (refV (Ctx.code g) it v) (lhB it (3 + v)) :=
      congrArg (fun m => turnLoZ box hv (Ctx.code g) m (refV (Ctx.code g) it v) (lhB it (3 + v))) hn'
    have e2 : turnHiZ box hv (Ctx.code g) s.P.n (refV (Ctx.code g) it v) (lhB it (3 + v)) =
        turnHiZ box hv (Ctx.code g) n (refV (Ctx.code g) it v) (lhB it (3 + v)) :=
      congrArg (fun m => turnHiZ box hv (Ctx.code g) m (refV (Ctx.code g) it v) (lhB it (3 + v))) hn'
    rw [hlabA, hlabB, e1] at h1
    rw [hlabA, hlabB, e2] at h2'
    have hc := cover_cen (lo := turnLoZ box hv (Ctx.code g) n (refV (Ctx.code g) it v) (lhB it (3 + v)))
      (hi := turnHiZ box hv (Ctx.code g) n (refV (Ctx.code g) it v) (lhB it (3 + v))) hcen
    constructor
    · show cen it (1 + v) - (prI box hv (Ctx.code g) n it v : ℝ) / 2 ^ 64 ≤ _
      exact le_trans hc.1 h1
    · show _ ≤ cen it (1 + v) + (prI box hv (Ctx.code g) n it v : ℝ) / 2 ^ 64
      exact le_trans h2' hc.2
  ·
    intro m
    refine ⟨(sInf (wheelSet B m (gl.freeCorner m)), sSup (wheelSet B m (gl.freeCorner m))), rfl, ?_⟩
    exact pr_abs_cover _ _
  · intro m
    exact pr_abs_cover _ _
  ·
    have ha' : lhB it 39 < s.P.n := by omega
    have hb' : lhB it 40 < s.P.n := by omega
    have hva : ((vertOf s hn (lhB it 39) : Fin s.P.n) : ℕ) = lhB it 39 := vertOf_val s hn ha'
    have hvb : ((vertOf s hn (lhB it 40) : Fin s.P.n) : ℕ) = lhB it 40 := vertOf_val s hn hb'
    refine ⟨by rw [hlo]; exact div_nonneg (Nat.cast_nonneg _) (by norm_num), Sum.inl (vertOf s hn (lhB it 39)), Sum.inl (vertOf s hn (lhB it 40)), ?_, ?_,
      ?_⟩
    · intro heq
      have h' := congrArg Fin.val (Sum.inl.inj heq)
      rw [hva, hvb] at h'
      exact hab h'
    · intro hadj
      refine not_adj s ?_ hadj
      rw [hva, hvb]
      exact hnadj
    · have hpt : ∀ (x : ℕ) (hx : x < s.P.n),
          glueC s.H gl E (Sum.inl (vertOf s hn x)) = Matrix.toEuclideanLin
            ((1 / (frameQ (Ctx.code g) it (lhB it (19 + x)) x : ℝ)) • (frameI (Ctx.code g) it (lhB it (19 + x)) x).toMat)
            e3 ∧
          radC s.H gl E (Sum.inl (vertOf s hn x)) = (radNI box hv (Ctx.code g) n it (lhB it (19 + x)) x : ℝ) / 2 ^ 64 := by
        intro x hx
        have hvx : ((vertOf s hn x : Fin s.P.n) : ℕ) = x := vertOf_val s hn hx
        have hdep : gl.depth (vertOf s hn x) = lhB it (19 + x) := by
          show lhB it (19 + ((vertOf s hn x : Fin s.P.n) : ℕ)) = _
          rw [hvx]
        have hf := frameAng_eq s hn hD' hr' hpar (lhB it (19 + x)) (vertOf s hn x)
        have hr := radN_eq s hn hD' (box := box) (hv := hv) (n := n) hr' hpar (lhB it (19 + x)) (vertOf s hn x)
        rw [hvx] at hf hr
        constructor
        · show Matrix.toEuclideanLin (frameAng gl (fun v : Fin s.P.n => cen it (1 + (v : ℕ))) (cen it 0)
            (gl.depth (vertOf s hn x)) (vertOf s hn x)) e3 = _
          rw [hdep]
          exact congrArg (fun M => Matrix.toEuclideanLin M e3) hf
        · show radN gl E.pr E.dr (gl.depth (vertOf s hn x)) (vertOf s hn x) = _
          rw [hdep]
          exact hr
      obtain ⟨hga, hra⟩ := hpt _ ha'
      obtain ⟨hgb, hrb⟩ := hpt _ hb'
      rw [hra, hrb, hlo]
      have hQa := frameQ_pos (Ctx.code g) it (lhB it (19 + lhB it 39)) (lhB it 39)
      have hQb := frameQ_pos (Ctx.code g) it (lhB it (19 + lhB it 40)) (lhB it 40)
      have hy := pr_pair_norm_lt (u := glueC s.H gl E (Sum.inl (vertOf s hn (lhB it 39))))
        (w := glueC s.H gl E (Sum.inl (vertOf s hn (lhB it 40)))) hQa hQb hT
        (by rw [hga]; exact pr_col3 _ _) (by rw [hgb]; exact pr_col3 _ _) hsq
      refine pr_pair_close hy ?_ (sinGe_sound hsin)
      unfold pairT
      push_cast
      ring

end Sound

def pairVOK (g box it : ℕ) : Bool := leafPairOK g box (it / 2 ^ 128)

theorem pairVOK_sound {g box it : ℕ} (h : pairVOK g box it = true) : KillOK g box := leafPairOK_sound h

def pairVChecker : Checker := killChecker pairVOK

theorem pairVChecker_sound : pairVChecker.Sound (kindIs 11) :=
  killChecker_sound pairVOK (fun _ _ _ h => pairVOK_sound h) _

end Tammes15.D3Kernel.Kinds
