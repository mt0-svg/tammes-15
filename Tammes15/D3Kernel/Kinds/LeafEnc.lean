import Tammes15.D3Kernel.Kinds.FreePt

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3lp.TrigNat Tammes15.D3Kernel Tammes15.PaperSteps Real
open scoped Classical

def encOK (g box lh : ℕ) : Bool :=
  vmOK g (hvOf lh) && vertsOK (Ctx.code g) (lhB lh 63) && glueOK (Ctx.code g) (lhB lh 63) lh &&
    perOK (Ctx.code g) && kgood (dKey box (hvOf lh)) && kgood (dKeyH box (hvOf lh)) && cenOK lh 0 &&
    allBelow (pvertOK box (hvOf lh) (Ctx.code g) (lhB lh 63) lh) (lhB lh 63) &&
    allBelow (freeOK g box (hvOf lh) (lhB lh 63) lh) (Ctx.k g)

section Sound

variable {g : ℕ}

theorem encOK_facts {box lh : ℕ} (h : encOK g box lh = true) :
    vmOK g (hvOf lh) = true ∧ vertsOK (Ctx.code g) (lhB lh 63) = true ∧
      glueOK (Ctx.code g) (lhB lh 63) lh = true ∧ (∀ i < Ctx.D g, 0 < (Ctx.code g).period i) ∧
      kgood (dKey box (hvOf lh)) = true ∧ kgood (dKeyH box (hvOf lh)) = true ∧ cenOK lh 0 = true ∧
      (∀ v < lhB lh 63, pvertOK box (hvOf lh) (Ctx.code g) (lhB lh 63) lh v = true) ∧
      ∀ m < Ctx.k g, freeOK g box (hvOf lh) (lhB lh 63) lh m = true := by
  simp only [encOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hvm, hverts⟩, hglue⟩, hper⟩, hk1⟩, hk2⟩, hc0⟩, hall⟩, hfree⟩ := h
  rw [allBelow_iff] at hall hfree
  simp only [perOK, allBelow_iff, decide_eq_true_eq] at hper
  exact ⟨hvm, hverts, hglue, hper, hk1, hk2, hc0, hall, hfree⟩

theorem encl_covers {box lh : ℕ} (h : encOK g box lh = true) (s : Sol g) (hs : BoxMem (Ctx.nv g) box s.x)
    (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) :
    (enclF s hn hD box (hvOf lh) lh (lhB lh 63)).Covers (procsW.wheel s.P (Ctx.k g)) s.H (glueOf s hn hD lh)
      (walkBox box (vmOf s (hvOf lh))) := by
  obtain ⟨hvm, hverts, hglue, hper, hk1, hk2, hc0, hall, hfree⟩ := encOK_facts h
  obtain ⟨-, hr, h2, hpar0⟩ := glueOK_facts hglue
  set n := lhB lh 63 with hn_def
  set hv := hvOf lh with hv_def
  have hn' : s.P.n = n := sol_n s hverts
  have hr' : lhB lh 1 < s.P.n := by omega
  set gl := glueOf s hn hD lh with hgl
  have hroot : ∀ v : Fin s.P.n, v = gl.root ↔ (v : ℕ) = lhB lh 1 := by
    intro v
    constructor
    · intro h
      rw [h]
      exact Nat.mod_eq_of_lt hr'
    · intro h
      apply Fin.ext
      show (v : ℕ) = lhB lh 1 % s.P.n
      rw [Nat.mod_eq_of_lt hr']
      exact h
  have hpar : ∀ v : Fin s.P.n, v ≠ gl.root → lhB lh (3 + v) < Ctx.D g :=
    fun v hv' => hpar0 v (by omega) (fun h => hv' ((hroot v).2 h))
  have hB : (walkBox box (vmOf s hv)).Mem (PVar.val s.A) := by
    intro p
    obtain ⟨hlt, hx⟩ := vmOf_spec hvm s p
    rw [← hx]
    exact hs _ hlt
  set E := enclF s hn hD box hv lh n with hE
  set B := walkBox box (vmOf s hv) with hBdef
  have hlo : B.lo .d = (kfix (dKey box hv) : ℝ) / 2 ^ 62 := keyVal_kgood hk1
  have hhi : B.hi .d = (kfix (dKeyH box hv) : ℝ) / 2 ^ 62 := keyVal_kgood hk2
  refine ⟨⟨?_, ?_⟩, ?_, fun m => (freeCover s hn hD hn' hr' h2 hpar hper hk1 hk2 hB m (hfree m m.isLt)).1,
    fun m => (freeCover s hn hD hn' hr' h2 hpar hper hk1 hk2 hB m (hfree m m.isLt)).2⟩
  · have hd := (cover_cen (lo := (kfix (dKey box hv) : ℤ)) (hi := (kfix (dKeyH box hv) : ℤ)) hc0).1
    rw [hlo]
    push_cast at hd
    exact hd
  · have hd := (cover_cen (lo := (kfix (dKey box hv) : ℤ)) (hi := (kfix (dKeyH box hv) : ℤ)) hc0).2
    rw [hhi]
    push_cast at hd
    exact hd
  · intro v hv'
    have hvn : (v : ℕ) ≠ lhB lh 1 := fun h => hv' ((hroot v).2 h)
    have hvlt : (v : ℕ) < n := by omega
    have hvo := hall v hvlt
    simp only [pvertOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hvo
    rcases hvo with hvo | ⟨hcen, hgood⟩
    · exact absurd hvo hvn
    have hp := hpar v hv'
    have hfst : ((gl.par v).fst : ℕ) = (Ctx.code g).fstAt (lhB lh (3 + v)) := dartOf_fst s hD hp
    have hlabA : ((s.lab (gl.refD (gl.par v).fst) : Fin (Ctx.D g)) : ℕ) = refV (Ctx.code g) lh v := by
      rw [lab_refD s hn hD hr' h2 hpar, hfst]
      rfl
    have hlabB : ((s.lab (gl.par v) : Fin (Ctx.D g)) : ℕ) = lhB lh (3 + v) := lab_dartOf s hD hp
    have hgood' : goodAll box hv (tf (Ctx.code g) s.P.n ((s.lab (gl.refD (gl.par v).fst) : Fin (Ctx.D g)) : ℕ))
        (degC (Ctx.code g) ((s.lab (gl.refD (gl.par v).fst) : Fin (Ctx.D g)) : ℕ)) = true := by
      have hgood2 := hgood
      rw [← hn'] at hgood2
      rw [hlabA]
      exact hgood2
    have h1 := turnLo_ge s hper (gl.refD (gl.par v).fst) (gl.par v) hgood'
    have h2' := turnHi_le s hper (gl.refD (gl.par v).fst) (gl.par v) hgood'
    have e1 : turnLoZ box hv (Ctx.code g) s.P.n (refV (Ctx.code g) lh v) (lhB lh (3 + v)) =
        turnLoZ box hv (Ctx.code g) n (refV (Ctx.code g) lh v) (lhB lh (3 + v)) :=
      congrArg (fun k => turnLoZ box hv (Ctx.code g) k (refV (Ctx.code g) lh v) (lhB lh (3 + v))) hn'
    have e2 : turnHiZ box hv (Ctx.code g) s.P.n (refV (Ctx.code g) lh v) (lhB lh (3 + v)) =
        turnHiZ box hv (Ctx.code g) n (refV (Ctx.code g) lh v) (lhB lh (3 + v)) :=
      congrArg (fun k => turnHiZ box hv (Ctx.code g) k (refV (Ctx.code g) lh v) (lhB lh (3 + v))) hn'
    rw [hlabA, hlabB, e1] at h1
    rw [hlabA, hlabB, e2] at h2'
    have hc := cover_cen (lo := turnLoZ box hv (Ctx.code g) n (refV (Ctx.code g) lh v) (lhB lh (3 + v)))
      (hi := turnHiZ box hv (Ctx.code g) n (refV (Ctx.code g) lh v) (lhB lh (3 + v))) hcen
    constructor
    · show cen lh (1 + v) - (prI box hv (Ctx.code g) n lh v : ℝ) / 2 ^ 64 ≤ _
      exact le_trans hc.1 h1
    · show _ ≤ cen lh (1 + v) + (prI box hv (Ctx.code g) n lh v : ℝ) / 2 ^ 64
      exact le_trans h2' hc.2

end Sound

def fU (g lh m : ℕ) : ℕ := (Ctx.code g).fstAt (fdI g lh m)

def rzA (lh α : ℕ) : M3 := rzI (angC gK (angQ lh α) (angA lh α)) (angS gK (angQ lh α) (angA lh α)) (angDen gK (angA lh α))

def ryA (lh α : ℕ) : M3 := ryI (angC gK (angQ lh α) (angA lh α)) (angS gK (angQ lh α) (angA lh α)) (angDen gK (angA lh α))

def ptM (g lh n p : ℕ) : M3 :=
  if p < n then frameI (Ctx.code g) lh (lhB lh (19 + p)) p
  else ((frameI (Ctx.code g) lh (lhB lh (19 + fU g lh (p - n))) (fU g lh (p - n))).mul (rzA lh (17 + (p - n)))).mul
    (ryA lh (21 + (p - n)))

def ptQ (g lh n p : ℕ) : ℤ :=
  if p < n then frameQ (Ctx.code g) lh (lhB lh (19 + p)) p
  else frameQ (Ctx.code g) lh (lhB lh (19 + fU g lh (p - n))) (fU g lh (p - n)) *
    angDen gK (angA lh (17 + (p - n))) * angDen gK (angA lh (21 + (p - n)))

def ptR (g box hv lh n p : ℕ) : ℤ :=
  if p < n then radNI box hv (Ctx.code g) n lh (lhB lh (19 + p)) p
  else radNI box hv (Ctx.code g) n lh (lhB lh (19 + fU g lh (p - n))) (fU g lh (p - n)) + qrI g box hv n lh (p - n) +
    rrI box hv lh (p - n)

theorem ptQ_pos (g lh n p : ℕ) : 0 < ptQ g lh n p := by
  unfold ptQ
  split_ifs
  · exact frameQ_pos _ _ _ _
  · exact mul_pos (mul_pos (frameQ_pos _ _ _ _) (angDen_pos _ _)) (angDen_pos _ _)

section Points

variable {g : ℕ}

noncomputable def ptOf (s : Sol g) (hn : 0 < s.P.n) (n p : ℕ) : Pts s.P (Ctx.k g) :=
  if p < n then .inl (vertOf s hn p) else if h : p - n < Ctx.k g then .inr ⟨p - n, h⟩ else .inl (vertOf s hn 0)

theorem toLin_three (A B C : M3) (x y z : ℝ) :
    (x • A.toMat) * (y • B.toMat) * (z • C.toMat) = (x * y * z) • ((A.mul B).mul C).toMat := by
  rw [scaled_mul', scaled_mul']

theorem pt_spec (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) {box lh : ℕ} (hn' : s.P.n = lhB lh 63)
    (hr : lhB lh 1 < s.P.n)
    (hpar : ∀ v : Fin s.P.n, v ≠ (glueOf s hn hD lh).root → lhB lh (3 + v) < Ctx.D g)
    {p : ℕ} (hp : p < lhB lh 63 + Ctx.k g) :
    glueC s.H (glueOf s hn hD lh) (enclF s hn hD box (hvOf lh) lh (lhB lh 63)) (ptOf s hn (lhB lh 63) p) =
        Matrix.toEuclideanLin ((1 / (ptQ g lh (lhB lh 63) p : ℝ)) • (ptM g lh (lhB lh 63) p).toMat) e3 ∧
      radC s.H (glueOf s hn hD lh) (enclF s hn hD box (hvOf lh) lh (lhB lh 63)) (ptOf s hn (lhB lh 63) p) =
        (ptR g box (hvOf lh) lh (lhB lh 63) p : ℝ) / 2 ^ 64 := by
  set n := lhB lh 63 with hn_def
  set gl := glueOf s hn hD lh with hgl
  set E := enclF s hn hD box (hvOf lh) lh n with hE

  have hvx : ∀ x : ℕ, x < s.P.n →
      frameAng gl (fun v : Fin s.P.n => cen lh (1 + (v : ℕ))) (cen lh 0) (gl.depth (vertOf s hn x)) (vertOf s hn x) =
          (1 / (frameQ (Ctx.code g) lh (lhB lh (19 + x)) x : ℝ)) • (frameI (Ctx.code g) lh (lhB lh (19 + x)) x).toMat ∧
        radN gl E.pr E.dr (gl.depth (vertOf s hn x)) (vertOf s hn x) =
          (radNI box (hvOf lh) (Ctx.code g) n lh (lhB lh (19 + x)) x : ℝ) / 2 ^ 64 := by
    intro x hx
    have hvx : ((vertOf s hn x : Fin s.P.n) : ℕ) = x := vertOf_val s hn hx
    have hdep : gl.depth (vertOf s hn x) = lhB lh (19 + x) := by
      show lhB lh (19 + ((vertOf s hn x : Fin s.P.n) : ℕ)) = _
      rw [hvx]
    have hf := frameAng_eq s hn hD hr hpar (lhB lh (19 + x)) (vertOf s hn x)
    have hr2 := radN_eq s hn hD (box := box) (hv := hvOf lh) (n := n) hr hpar (lhB lh (19 + x)) (vertOf s hn x)
    rw [hvx] at hf hr2
    rw [hdep]
    exact ⟨hf, hr2⟩
  by_cases hpn : p < n
  · have hpt : ptOf s hn n p = .inl (vertOf s hn p) := by simp [ptOf, hpn]
    obtain ⟨h1, h2⟩ := hvx p (by omega)
    rw [hpt]
    constructor
    · show Matrix.toEuclideanLin (frameAng gl (fun v : Fin s.P.n => cen lh (1 + (v : ℕ))) (cen lh 0)
        (gl.depth (vertOf s hn p)) (vertOf s hn p)) e3 = _
      rw [h1]
      simp only [ptQ, ptM, ite_eq_left hpn]
    · show radN gl E.pr E.dr (gl.depth (vertOf s hn p)) (vertOf s hn p) = _
      rw [h2]
      simp only [ptR, ite_eq_left hpn]
  · have hk : p - n < Ctx.k g := by omega
    set m : Fin (Ctx.k g) := ⟨p - n, hk⟩ with hm
    have hpt : ptOf s hn n p = .inr m := by simp [ptOf, hpn, hk, hm]
    have hfst := freeDart_fst s hn hD lh m
    set u := (freeDart s.H gl m).fst with hu
    have huv : (u : ℕ) = fU g lh (p - n) := hfst
    have hult : fU g lh (p - n) < s.P.n := by rw [← huv]; exact u.isLt
    have hux : u = vertOf s hn (fU g lh (p - n)) := by
      apply Fin.ext
      rw [vertOf_val s hn hult]
      exact huv
    obtain ⟨h1, h2⟩ := hvx (fU g lh (p - n)) hult
    rw [hpt]
    constructor
    · show Matrix.toEuclideanLin (frameAng gl (fun v : Fin s.P.n => cen lh (1 + (v : ℕ))) (cen lh 0) (gl.depth u) u *
        rotZ (cen lh (17 + (p - n))) * rotY (cen lh (21 + (p - n)))) e3 = _
      rw [hux, h1]
      unfold cen
      rw [rotZ_angR, rotY_angR, toLin_three]
      simp only [ptQ, ptM, ite_eq_right hpn, rzA, ryA]
      congr 2
      push_cast
      field_simp
    · show radN gl E.pr E.dr (gl.depth u) u + (qrI g box (hvOf lh) n lh (p - n) : ℝ) / 2 ^ 64 +
        (rrI box (hvOf lh) lh (p - n) : ℝ) / 2 ^ 64 = _
      rw [hux, h2]
      simp only [ptR, ite_eq_right hpn]
      push_cast
      ring

end Points

def pairT2 (g box lh : ℕ) : ℤ :=
  4 * (sdI box (hvOf lh) : ℤ) - ptR g box (hvOf lh) lh (lhB lh 63) (lhB lh 39) -
    ptR g box (hvOf lh) lh (lhB lh 63) (lhB lh 40)

def pairTest2 (g box lh : ℕ) : Bool :=
  decide (lhB lh 39 < lhB lh 63 + Ctx.k g) && decide (lhB lh 40 < lhB lh 63 + Ctx.k g) &&
    !(lhB lh 39 == lhB lh 40) &&
    (!(decide (lhB lh 39 < lhB lh 63) && decide (lhB lh 40 < lhB lh 63)) ||
      nonAdjC (Ctx.code g) (lhB lh 39) (lhB lh 40)) &&
    sinGe 63 nT (kfix (dKey box (hvOf lh))) (sdI box (hvOf lh)) && decide (0 < pairT2 g box lh) &&
    decide (sq3 (ptM g lh (lhB lh 63) (lhB lh 39)) (ptM g lh (lhB lh 63) (lhB lh 40))
        (ptQ g lh (lhB lh 63) (lhB lh 39)) (ptQ g lh (lhB lh 63) (lhB lh 40)) * ((2 ^ 128 : ℕ) : ℤ) <
      (pairT2 g box lh * ptQ g lh (lhB lh 63) (lhB lh 39) * ptQ g lh (lhB lh 63) (lhB lh 40)) *
        (pairT2 g box lh * ptQ g lh (lhB lh 63) (lhB lh 39) * ptQ g lh (lhB lh 63) (lhB lh 40)))

def pairOK (g box it : ℕ) : Bool := encOK g box (it / 2 ^ 128) && pairTest2 g box (it / 2 ^ 128)

section PairSound

variable {g : ℕ}

theorem par_lt (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) {lh n : ℕ} (hn' : s.P.n = n)
    (hr : lhB lh 1 < s.P.n) (hpar0 : ∀ v < n, v ≠ lhB lh 1 → lhB lh (3 + v) < (Ctx.code g).D) :
    ∀ v : Fin s.P.n, v ≠ (glueOf s hn hD lh).root → lhB lh (3 + v) < Ctx.D g := by
  intro v hv'
  apply hpar0 v (by omega)
  intro h
  apply hv'
  apply Fin.ext
  show (v : ℕ) = lhB lh 1 % s.P.n
  rw [Nat.mod_eq_of_lt hr]
  exact h

theorem ptOf_ne (s : Sol g) (hn : 0 < s.P.n) {n a b : ℕ} (hn' : s.P.n = n) (ha : a < n + Ctx.k g)
    (hb : b < n + Ctx.k g) (hab : a ≠ b) : ptOf s hn n a ≠ ptOf s hn n b := by
  unfold ptOf
  by_cases h1 : a < n <;> by_cases h2 : b < n
  · rw [ite_eq_left h1, ite_eq_left h2]
    intro he
    have := congrArg Fin.val (Sum.inl.inj he)
    rw [vertOf_val s hn (by omega), vertOf_val s hn (by omega)] at this
    exact hab this
  · have hk : b - n < Ctx.k g := by omega
    rw [ite_eq_left h1, ite_eq_right h2, dite_eq_left hk]
    exact Sum.inl_ne_inr
  · have hk : a - n < Ctx.k g := by omega
    rw [ite_eq_right h1, ite_eq_left h2, dite_eq_left hk]
    exact Sum.inr_ne_inl
  · have hka : a - n < Ctx.k g := by omega
    have hkb : b - n < Ctx.k g := by omega
    rw [ite_eq_right h1, ite_eq_right h2, dite_eq_left hka, dite_eq_left hkb]
    intro he
    have := congrArg Fin.val (Sum.inr.inj he)
    simp only at this
    omega

theorem ptOf_nadj (s : Sol g) (hn : 0 < s.P.n) {n a b : ℕ} (hn' : s.P.n = n) (ha : a < n + Ctx.k g)
    (hb : b < n + Ctx.k g)
    (h : (!(decide (a < n) && decide (b < n)) || nonAdjC (Ctx.code g) a b) = true) :
    ¬ PAdj s.P (ptOf s hn n a) (ptOf s hn n b) := by
  unfold ptOf
  by_cases h1 : a < n <;> by_cases h2 : b < n
  · rw [ite_eq_left h1, ite_eq_left h2]
    simp only [h1, h2, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at h
    intro hadj
    refine not_adj s ?_ hadj
    rw [vertOf_val s hn (by omega), vertOf_val s hn (by omega)]
    exact h
  · have hk : b - n < Ctx.k g := by omega
    rw [ite_eq_left h1, ite_eq_right h2, dite_eq_left hk]
    exact id
  · have hk : a - n < Ctx.k g := by omega
    rw [ite_eq_right h1, ite_eq_left h2, dite_eq_left hk]
    exact id
  · have hka : a - n < Ctx.k g := by omega
    have hkb : b - n < Ctx.k g := by omega
    rw [ite_eq_right h1, ite_eq_right h2, dite_eq_left hka, dite_eq_left hkb]
    exact id

theorem pairOK_sound {box it : ℕ} (h : pairOK g box it = true) : KillOK g box := by
  simp only [pairOK, Bool.and_eq_true] at h
  obtain ⟨henc, hpt⟩ := h
  set lh := it / 2 ^ 128 with hlh
  obtain ⟨hvm, hverts, hglue, -, hk1, -, -, -, -⟩ := encOK_facts henc
  obtain ⟨hD, hr, h2, hpar0⟩ := glueOK_facts hglue
  simp only [pairTest2, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hpt
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, hnadj⟩, hsin⟩, hT⟩, hsq⟩ := hpt
  apply killOK_of_leafKill procsW_sound hvm
  intro s hs
  have hn' : s.P.n = lhB lh 63 := sol_n s hverts
  have hn : 0 < s.P.n := by omega
  have hD' : 0 < Ctx.D g := hD
  have hr' : lhB lh 1 < s.P.n := by omega
  have hpar := par_lt s hn hD' hn' hr' hpar0
  refine ⟨glueOf s hn hD' lh, glueOf_valid s hn' hn hD' hglue, enclF s hn hD' box (hvOf lh) lh (lhB lh 63),
    encl_covers henc s hs hn hD', Or.inl ?_⟩
  have hlo : (walkBox box (vmOf s (hvOf lh))).lo .d = (kfix (dKey box (hvOf lh)) : ℝ) / 2 ^ 62 := keyVal_kgood hk1
  refine ⟨by rw [hlo]; exact div_nonneg (Nat.cast_nonneg _) (by norm_num), ptOf s hn (lhB lh 63) (lhB lh 39),
    ptOf s hn (lhB lh 63) (lhB lh 40), ptOf_ne s hn hn' ha hb hab, ptOf_nadj s hn hn' ha hb hnadj, ?_⟩
  obtain ⟨hga, hra⟩ := pt_spec s hn hD' (box := box) hn' hr' hpar ha
  obtain ⟨hgb, hrb⟩ := pt_spec s hn hD' (box := box) hn' hr' hpar hb
  rw [hra, hrb, hlo]
  have hy := pr_pair_norm_lt
    (u := glueC s.H (glueOf s hn hD' lh) (enclF s hn hD' box (hvOf lh) lh (lhB lh 63)) (ptOf s hn (lhB lh 63) (lhB lh 39)))
    (w := glueC s.H (glueOf s hn hD' lh) (enclF s hn hD' box (hvOf lh) lh (lhB lh 63)) (ptOf s hn (lhB lh 63) (lhB lh 40)))
    (ptQ_pos g lh _ _) (ptQ_pos g lh _ _) hT (by rw [hga]; exact pr_col3 _ _) (by rw [hgb]; exact pr_col3 _ _) hsq
  refine pr_pair_close hy ?_ (sinGe_sound hsin)
  unfold pairT2
  push_cast
  ring

end PairSound

def pairChecker : Checker := killChecker pairOK

theorem pairChecker_sound : pairChecker.Sound (kindIs 11) :=
  killChecker_sound pairOK (fun _ _ _ h => pairOK_sound h) _

end Tammes15.D3Kernel.Kinds
