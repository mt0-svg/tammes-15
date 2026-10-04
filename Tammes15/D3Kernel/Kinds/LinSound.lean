import Tammes15.D3Kernel.Kinds.LinFarm
import Tammes15.D3lp.Fields

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Pent Real

theorem ntabK_eq (g : ℕ) : ntabK g = ntab g := land_shiftRight g 5184 8

theorem entK_eq (g j : ℕ) : entK g j = ent g j := by
  have h : Nat.add (nat_lit 5248) (Nat.shiftLeft j (nat_lit 7)) = 5248 + 128 * j := by
    rw [shl_eq]
    show 5248 + j * 2 ^ 7 = 5248 + 128 * j
    ring
  unfold entK
  rw [h]
  exact land_shiftRight g _ 128

theorem new_raw (x : ℕ) : Nat.land x (nat_lit 18446744073709551615) = itNew x := land_shiftRight x 0 64

theorem cc_raw (E : ℕ) : Nat.land (Nat.shiftRight E (nat_lit 3)) (nat_lit 3) = eCc E := land_shiftRight E 3 2

theorem nt_raw (E : ℕ) : Nat.land E (nat_lit 7) = eNt E := land_shiftRight E 0 3

theorem ts_raw (E : ℕ) : Nat.shiftRight E (nat_lit 8) = eTs E := Nat.shiftRight_eq_div_pow E 8

theorem half_raw (t : ℕ) : Nat.shiftRight t (nat_lit 1) = t / 2 :=
  (Nat.shiftRight_eq_div_pow t 1).trans (by norm_num)

theorem par_raw (t : ℕ) : Nat.land t (nat_lit 1) = t % 2 := Nat.and_one_is_mod t

theorem linRec_spec {g box it : ℕ} (h : linRec g box it = true) :
    bits it 75 7 < ntab g ∧
      ((kgood (itNew it) = true ∧
          linAcc box (itBound it / 2) (recFin (itBound it % 2) (kfix (itNew it)) (eCc (ent g (bits it 75 7))))
            (eNt (ent g (bits it 75 7))) (eTs (ent g (bits it 75 7))) 0 0 0 0 = true) ∨
        linAcc box 64 (emptyFin (eCc (ent g (bits it 75 7)))) (eNt (ent g (bits it 75 7)))
          (eTs (ent g (bits it 75 7))) 0 0 0 0 = true) := by
  simp only [linRec] at h
  rw [fk_bits7, fk_bits7, entK_eq, ntabK_eq, cc_raw, nt_raw, ts_raw, half_raw, par_raw, new_raw] at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases hb : (kgood (itNew it) &&
      linAcc box (bits it 64 7 / 2) (recFin (bits it 64 7 % 2) (kfix (itNew it)) (eCc (ent g (bits it 75 7))))
        (eNt (ent g (bits it 75 7))) (eTs (ent g (bits it 75 7))) 0 0 0 0)
  · rw [hb] at h2
    exact Or.inr h2
  · rw [Bool.and_eq_true] at hb
    exact Or.inl hb

theorem linKill_spec {g box it : ℕ} (h : linKill g box it = true) :
    bits it 75 7 < ntab g ∧
      linAcc box 64 (emptyFin (eCc (ent g (bits it 75 7)))) (eNt (ent g (bits it 75 7)))
        (eTs (ent g (bits it 75 7))) 0 0 0 0 = true := by
  simp only [linKill] at h
  rw [fk_bits7, entK_eq, ntabK_eq, cc_raw, nt_raw, ts_raw] at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  exact h

theorem x_of_aOK {g w : ℕ} (s : Sol g) (h : aOK g w = true) : w < Ctx.nv g ∧ s.x w = alpha s.A.d := by
  unfold aOK at h
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  refine ⟨h.1, ?_⟩
  simp [Sol.x, Ctx.val, h.2]

theorem aOK_lt {g w : ℕ} (h : aOK g w = true) : w < Ctx.nv g := by
  unfold aOK at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1

theorem dvOK_lt {g w i : ℕ} (h : dvOK g w i = true) : w < Ctx.nv g := by
  unfold dvOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1.1

theorem x_of_dvOK {g w i : ℕ} (s : Sol g) (h : dvOK g w i = true) :
    w < Ctx.nv g ∧ ∃ hi : i < Ctx.D g, s.x w = s.A.corner (s.lab.symm ⟨i, hi⟩) := by
  unfold dvOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨hw, hi⟩, hm⟩ := h
  refine ⟨hw, hi, ?_⟩
  set e := s.lab.symm ⟨i, hi⟩ with he
  have hlab : (s.lab e : ℕ) = i := by simp [he]
  rcases hm with (hm | ⟨hm, hper⟩) | ⟨hm, hper⟩
  · exact val_corner s.lab s.A e (by rw [hlab]; exact hm)
  · have hfs : fsize s.P e = 3 :=
      fsize_of_period s.hm e ((congrArg (Ctx.code g).period hlab).trans hper) (by norm_num)
    rw [s.hR.tri e hfs]
    simp [Sol.x, Ctx.val, hm]
  · have hfs : fsize s.P e = 4 :=
      fsize_of_period s.hm e ((congrArg (Ctx.code g).period hlab).trans hper) (by norm_num)
    have hit : (Ctx.code g).faceIter i 2 = (s.lab ((s.P.R.face ^ 2) e) : ℕ) :=
      (congrArg (fun j => (Ctx.code g).faceIter j 2) hlab).symm.trans (faceIter_lab s.hm e 2)
    rw [hit] at hm
    rw [show s.x w = s.A.corner ((s.P.R.face ^ 2) e) from val_corner s.lab s.A _ hm]
    have := (s.hR.rhombus e hfs).1
    simpa [Assign.fc] using this

theorem d_range {g : ℕ} (s : Sol g) : 0 < s.A.d ∧ s.A.d < π / 2 := by
  obtain ⟨h1, h2⟩ := s.hd
  unfold dlo at h1
  unfold dhi at h2
  constructor <;> nlinarith [pi_pos]

theorem rhombus_facts {g i : ℕ} (s : Sol g) (hi : i < Ctx.D g) (hper : (Ctx.code g).period i = 4) :
    ∃ hf : (Ctx.code g).faceAt i < Ctx.D g,
      s.A.corner (s.lab.symm ⟨i, hi⟩) ≤ 2 * alpha s.A.d ∧
      3 * alpha s.A.d ≤ s.A.corner (s.lab.symm ⟨i, hi⟩) + s.A.corner (s.lab.symm ⟨(Ctx.code g).faceAt i, hf⟩) ∧
      s.A.corner (s.lab.symm ⟨i, hi⟩) + s.A.corner (s.lab.symm ⟨(Ctx.code g).faceAt i, hf⟩) ≤ Ssum s.A.d := by
  set e := s.lab.symm ⟨i, hi⟩ with he
  have hlab : (s.lab e : ℕ) = i := by simp [he]
  have hfs : fsize s.P e = 4 :=
    fsize_of_period s.hm e ((congrArg (Ctx.code g).period hlab).trans hper) (by norm_num)
  have hface : (Ctx.code g).faceAt i = (s.lab (s.P.R.face e) : ℕ) :=
    (congrArg (Ctx.code g).faceAt hlab).symm.trans (s.hm.face e)
  have hf : (Ctx.code g).faceAt i < Ctx.D g := by rw [hface]; exact (s.lab _).isLt
  have hfe : s.lab.symm ⟨(Ctx.code g).faceAt i, hf⟩ = s.P.R.face e := by
    apply s.lab.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext hface
  refine ⟨hf, ?_⟩
  rw [hfe]
  obtain ⟨-, h1⟩ := s.hR.rhombus e hfs
  have h0 : s.A.fc e 0 = s.A.corner e := by simp [Assign.fc]
  have h1' : s.A.fc e 1 = s.A.corner (s.P.R.face e) := by simp [Assign.fc]
  obtain ⟨ha, hpi⟩ := s.hR.corner_mem e
  obtain ⟨hb, -⟩ := s.hR.corner_mem (s.P.R.face e)
  obtain ⟨r1, -, r3, r4⟩ := rhombus_rows s.A.d (s.A.fc e 0) (s.A.fc e 1) (d_range s) h1
    ⟨by rw [h0]; exact ha, by rw [h0]; exact hpi⟩ (by rw [h1']; exact hb)
  rw [h0, h1'] at *
  exact ⟨r1, r3, r4⟩

theorem tCoef_pos {Ts q m : ℕ} (h : tIs Ts q 0 m = true) : tCoef Ts q = m := by
  unfold tIs at h
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  unfold tCoef
  rw [if_neg (by omega), h.2]

theorem tCoef_neg {Ts q m : ℕ} (h : tIs Ts q 1 m = true) : tCoef Ts q = -(m : ℝ) := by
  unfold tIs at h
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  unfold tCoef
  rw [if_pos h.1, h.2]

theorem rowSum_two {E : ℕ} (h : eNt E = 2) (x : ℕ → ℝ) :
    rowSum E x = tCoef (eTs E) 0 * x (tVar (eTs E) 0) + tCoef (eTs E) 1 * x (tVar (eTs E) 1) := by
  unfold rowSum
  rw [h]
  simp [Finset.sum_range_succ]

theorem rowSum_three {E : ℕ} (h : eNt E = 3) (x : ℕ → ℝ) :
    rowSum E x = tCoef (eTs E) 0 * x (tVar (eTs E) 0) + tCoef (eTs E) 1 * x (tVar (eTs E) 1) +
      tCoef (eTs E) 2 * x (tVar (eTs E) 2) := by
  unfold rowSum
  rw [h]
  simp [Finset.sum_range_succ]

theorem bP_zero : bP 0 = 0 := rfl
theorem bN_zero : bN 0 = 0 := rfl
theorem bP_one : bP 1 = cTPH := rfl
theorem bN_one : bN 1 = 0 := rfl
theorem bP_two : bP 2 = 0 := rfl
theorem bN_two : bN 2 = cTPL := rfl
theorem bP_three : bP 3 = cSHI := rfl
theorem bN_three : bN 3 = 0 := rfl

theorem rowRhs_zero {E : ℕ} (h : eCc E = 0) : rowRhs E = 0 := by
  unfold rowRhs
  rw [h]
  simp [bP_zero, bN_zero]

theorem rowRhs_one {E : ℕ} (h : eCc E = 1) : rowRhs E = (cTPH : ℝ) / 2 ^ 62 := by
  unfold rowRhs
  rw [h]
  simp [bP_one, bN_one]

theorem rowRhs_two {E : ℕ} (h : eCc E = 2) : rowRhs E = -(cTPL : ℝ) / 2 ^ 62 := by
  unfold rowRhs
  rw [h]
  simp [bP_two, bN_two]

theorem rowRhs_three {E : ℕ} (h : eCc E = 3) : rowRhs E = (cSHI : ℝ) / 2 ^ 62 := by
  unfold rowRhs
  rw [h]
  simp [bP_three, bN_three]

theorem two_vars {E nv : ℕ} (h : eNt E = 2) (h0 : tVar (eTs E) 0 < nv) (h1 : tVar (eTs E) 1 < nv) :
    ∀ q < eNt E, tVar (eTs E) q < nv := by
  intro q hq
  rw [h] at hq
  interval_cases q <;> assumption

theorem three_vars {E nv : ℕ} (h : eNt E = 3) (h0 : tVar (eTs E) 0 < nv) (h1 : tVar (eTs E) 1 < nv)
    (h2 : tVar (eTs E) 2 < nv) : ∀ q < eNt E, tVar (eTs E) q < nv := by
  intro q hq
  rw [h] at hq
  interval_cases q <;> assumption

theorem block_sum {g : ℕ} (s : Sol g) {o e v : ℕ} (hoe : o < e) (heD : e ≤ Ctx.D g)
    (hblk : ∀ i < Ctx.D g, (Ctx.code g).fstAt i = v ↔ o ≤ i ∧ i < e) :
    ∑ i ∈ Finset.range (e - o), (if h : o + i < Ctx.D g then s.A.corner (s.lab.symm ⟨o + i, h⟩) else 0) =
      2 * π := by
  have hoD : o < Ctx.D g := by omega
  set d0 := s.lab.symm ⟨o, hoD⟩ with hd0
  have hfst : ∀ d : s.P.G.Dart, (Ctx.code g).fstAt (s.lab d) = (d.fst : ℕ) := s.hm.fst
  have hv0 : (d0.fst : ℕ) = v := by
    rw [← hfst d0, hd0, Equiv.apply_symm_apply]
    exact (hblk o hoD).2 ⟨le_refl o, hoe⟩
  have hmem : ∀ d : s.P.G.Dart, d.fst = d0.fst ↔ o ≤ (s.lab d : ℕ) ∧ (s.lab d : ℕ) < e := by
    intro d
    rw [← hblk _ (s.lab d).isLt, hfst d, ← hv0, Fin.val_inj]
  rw [← s.hR.vertex_sum d0.fst]
  symm
  apply Finset.sum_bij (fun d _ => (s.lab d : ℕ) - o)
  · intro d hd
    rw [Finset.mem_filter] at hd
    have := (hmem d).1 hd.2
    rw [Finset.mem_range]
    omega
  · intro d1 hd1 d2 hd2 h12
    rw [Finset.mem_filter] at hd1 hd2
    have h1 := (hmem d1).1 hd1.2
    have h2 := (hmem d2).1 hd2.2
    apply s.lab.injective
    apply Fin.ext
    omega
  · intro b hb
    rw [Finset.mem_range] at hb
    have hbD : o + b < Ctx.D g := by omega
    refine ⟨s.lab.symm ⟨o + b, hbD⟩, ?_, ?_⟩
    · rw [Finset.mem_filter, hmem, Equiv.apply_symm_apply]
      exact ⟨by simp, Nat.le_add_right _ _, by show o + b < e; omega⟩
    · simp only [Equiv.apply_symm_apply]
      omega
  · intro d hd
    rw [Finset.mem_filter] at hd
    have h1 := (hmem d).1 hd.2
    have hD : o + ((s.lab d : ℕ) - o) < Ctx.D g := by have := (s.lab d).isLt; omega
    rw [dif_pos hD]
    congr 1
    apply s.lab.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    simp only
    omega

theorem vert_vars {g E ng : ℕ} (h : vertOK g E ng = true) : ∀ q < eNt E, tVar (eTs E) q < Ctx.nv g := by
  unfold vertOK at h
  simp only [Bool.and_eq_true, allBelow_iff] at h
  intro q hq
  have := (h.2 q hq).1
  rw [Nat.blt_eq] at this
  exact this

theorem vert_sum {g E ng : ℕ} (s : Sol g) (hs : fstSorted (Ctx.code g) = true) (h : vertOK g E ng = true) :
    (∀ q < eNt E, tVar (eTs E) q < Ctx.nv g) ∧
      rowSum E s.x = (if ng = 1 then -1 else 1) * (2 * π) := by
  unfold vertOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq, allBelow_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hnt, hoe⟩, heD⟩, -⟩, ho⟩, he⟩, hdarts⟩, hterms⟩ := h
  unfold fstSorted at hs
  rw [allBelow_iff] at hs
  simp only [Nat.ble_eq] at hs
  have hblk := sorted_block (Ctx.code g).fstAt (Ctx.code g).D (eO E) (eE E) (eX E)
    (fun i hi => hs i (by omega)) hoe heD ho he (fun i hi => ((hdarts i hi).1.1.1))
  refine ⟨fun q hq => (hterms q hq).1, ?_⟩

  have hcoef : ∀ q < eNt E, tCoef (eTs E) q =
      (if ng = 1 then -1 else 1) * (countBelow (fun i => Nat.beq (eTau E i) q) (eE E - eO E) : ℝ) := by
    intro q hq
    rw [← (hterms q hq).2]
    by_cases hm : tMag (eTs E) q = 0
    · unfold tCoef
      rw [hm]
      split_ifs <;> simp
    · have hpos : 0 < countBelow (fun i => Nat.beq (eTau E i) q) (eE E - eO E) := by
        rw [← (hterms q hq).2]; omega
      rw [countBelow_eq, Finset.card_pos] at hpos
      obtain ⟨i, hi⟩ := hpos
      rw [Finset.mem_filter, Finset.mem_range, Nat.beq_eq] at hi
      have hng := (hdarts i hi.1).2
      rw [hi.2] at hng
      unfold tCoef
      rw [hng]
      split_ifs <;> simp
  have hsum : rowSum E s.x = (if ng = 1 then -1 else 1) *
      ∑ q ∈ Finset.range (eNt E),
        (countBelow (fun i => Nat.beq (eTau E i) q) (eE E - eO E) : ℝ) * s.x (tVar (eTs E) q) := by
    unfold rowSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_range] at hq
    rw [hcoef q hq]
    ring
  rw [hsum, sum_regroup (eNt E) (eE E - eO E) (eTau E) (fun q => s.x (tVar (eTs E) q))
    (fun i hi => (hdarts i hi).1.1.2)]
  congr 1
  rw [← block_sum s hoe heD hblk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  obtain ⟨-, hD, hx⟩ := x_of_dvOK s (hdarts i hi).1.2
  rw [hx, dif_pos hD]

theorem rowValid_of_entOK {g E : ℕ} (hs : fstSorted (Ctx.code g) = true) (h : entOK g E = true) :
    RowValid g E := by
  simp only [entOK] at h
  cases h0 : Nat.beq (eFam E) 0
  · rw [h0] at h
    cases h1 : Nat.beq (eFam E) 1
    · rw [h1] at h
      cases h2 : Nat.beq (eFam E) 2
      · rw [h2] at h
        cases h3 : Nat.beq (eFam E) 3
        · rw [h3] at h
          cases h4 : Nat.beq (eFam E) 4
          ·
            rw [h4] at h
            simp only [Bool.and_eq_true, Nat.beq_eq] at h
            obtain ⟨⟨-, hcc⟩, hv⟩ := h
            refine ⟨fun q hq => ?_, fun s => ?_⟩
            · exact vert_vars hv q hq
            · rw [(vert_sum s hs hv).2, rowRhs_two hcc]
              have := cTPL_le_two_pi
              rw [if_pos rfl]
              have : (-(cTPL : ℝ)) / 2 ^ 62 = -((cTPL : ℝ) / 2 ^ 62) := neg_div _ _
              linarith
          ·
            rw [h4] at h
            simp only [Bool.and_eq_true, Nat.beq_eq] at h
            obtain ⟨hcc, hv⟩ := h
            refine ⟨fun q hq => ?_, fun s => ?_⟩
            · exact vert_vars hv q hq
            · rw [(vert_sum s hs hv).2, rowRhs_one hcc]
              have := two_pi_le_cTPH
              rw [if_neg (by norm_num)]
              linarith
        ·
          rw [h3] at h
          simp only [Bool.and_eq_true, Nat.beq_eq] at h
          obtain ⟨⟨⟨⟨⟨⟨hnt, hcc⟩, hper⟩, t0⟩, d0⟩, t1⟩, d1⟩ := h
          refine ⟨two_vars hnt (dvOK_lt d0) (dvOK_lt d1), fun s => ?_⟩
          obtain ⟨-, hi, hx0⟩ := x_of_dvOK s d0
          obtain ⟨-, hf, hx1⟩ := x_of_dvOK s d1
          obtain ⟨hf', -, -, r4⟩ := rhombus_facts s hi hper
          rw [rowSum_two hnt, tCoef_pos t0, tCoef_pos t1, hx0, hx1, rowRhs_three hcc]
          have hS := pFull_ssum_hi s.A.d (by have := s.hd.1; unfold dlo at this; unfold dloFull; exact this)
            (by have := s.hd.2; unfold dhi at this; unfold dhiFull; exact this)
          have hc := shi_le_cSHI
          have e1 : ((pFull.shi : ℤ) : ℝ) / ((pFull.S : ℕ) : ℝ) =
              ((373170040409990243346 : ℕ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) := by
            norm_num [pFull]
          push_cast
          linarith
      ·
        rw [h2] at h
        simp only [Bool.and_eq_true, Nat.beq_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨hnt, hcc⟩, hper⟩, t0⟩, a0⟩, t1⟩, d1⟩, t2⟩, d2⟩ := h
        refine ⟨three_vars hnt (aOK_lt a0) (dvOK_lt d1) (dvOK_lt d2), fun s => ?_⟩
        obtain ⟨-, hxa⟩ := x_of_aOK s a0
        obtain ⟨-, hi, hx1⟩ := x_of_dvOK s d1
        obtain ⟨-, hf, hx2⟩ := x_of_dvOK s d2
        obtain ⟨hf', -, r3, -⟩ := rhombus_facts s hi hper
        rw [rowSum_three hnt, tCoef_pos t0, tCoef_neg t1, tCoef_neg t2, hxa, hx1, hx2, rowRhs_zero hcc]
        push_cast
        linarith
    ·
      rw [h1] at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨hnt, hcc⟩, hper⟩, t0⟩, d0⟩, t1⟩, a1⟩ := h
      refine ⟨two_vars hnt (dvOK_lt d0) (aOK_lt a1), fun s => ?_⟩
      obtain ⟨-, hi, hx0⟩ := x_of_dvOK s d0
      obtain ⟨-, hxa⟩ := x_of_aOK s a1
      obtain ⟨-, r1, -, -⟩ := rhombus_facts s hi hper
      rw [rowSum_two hnt, tCoef_pos t0, tCoef_neg t1, hx0, hxa, rowRhs_zero hcc]
      push_cast
      linarith
  ·
    rw [h0] at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨⟨hnt, hcc⟩, t0⟩, a0⟩, t1⟩, d1⟩ := h
    refine ⟨two_vars hnt (aOK_lt a0) (dvOK_lt d1), fun s => ?_⟩
    obtain ⟨-, hxa⟩ := x_of_aOK s a0
    obtain ⟨-, hi, hx1⟩ := x_of_dvOK s d1
    have hc := (s.hR.corner_mem (s.lab.symm ⟨eX E, hi⟩)).1
    rw [rowSum_two hnt, tCoef_pos t0, tCoef_neg t1, hxa, hx1, rowRhs_zero hcc]
    push_cast
    linarith

theorem validCtx_sound {g : ℕ} (h : validCtx g = true) : ∀ j < ntab g, RowValid g (ent g j) := by
  unfold validCtx at h
  rw [Bool.and_eq_true, allBelow_iff] at h
  intro j hj
  exact rowValid_of_entOK h.1 (h.2 j hj)

theorem linAcc_row {box v E : ℕ} {k : ℕ → ℕ → ℕ → ℕ → Bool} (x : ℕ → ℝ)
    (hS : ∀ q < eNt E, keyVal (bnd box (2 * tVar (eTs E) q)) ≤ x (tVar (eTs E) q) ∧
      x (tVar (eTs E) q) ≤ keyVal (bnd box (2 * tVar (eTs E) q + 1)))
    (h : linAcc box v k (eNt E) (eTs E) 0 0 0 0 = true) :
    ∃ cp cn P Q, k cp cn P Q = true ∧ ((cp : ℝ) - cn) * x v + ((P : ℝ) - Q) / 2 ^ 62 ≤ rowSum E x := by
  have hb : ∀ q < eNt E, tVar (eTs E) q ≠ v →
      (kgood (bk box (2 * tVar (eTs E) q)) = true →
        (kfix (bk box (2 * tVar (eTs E) q)) : ℝ) / 2 ^ 62 ≤ x (tVar (eTs E) q)) ∧
      (kgood (bk box (2 * tVar (eTs E) q + 1)) = true →
        x (tVar (eTs E) q) ≤ (kfix (bk box (2 * tVar (eTs E) q + 1)) : ℝ) / 2 ^ 62) := by
    intro q hq _
    obtain ⟨h1, h2⟩ := hS q hq
    constructor
    · intro hg
      rw [← keyVal_kgood hg, bk_eq]
      exact h1
    · intro hg
      rw [← keyVal_kgood hg, bk_eq]
      exact h2
  obtain ⟨cp, cn, P, Q, hk, hle⟩ := linAcc_spec box v k x (eNt E) (eTs E) 0 0 0 0 hb h
  refine ⟨cp, cn, P, Q, hk, ?_⟩
  unfold rowSum
  simpa using hle

theorem empty_of {g box E : ℕ} (hE : RowValid g E) (s : Sol g) (hS : BoxMem (Ctx.nv g) box s.x)
    (h : linAcc box 64 (emptyFin (eCc E)) (eNt E) (eTs E) 0 0 0 0 = true) : False := by
  let x' : ℕ → ℝ := fun w => if w = 64 then 0 else s.x w
  have hx' : ∀ q, x' (tVar (eTs E) q) = s.x (tVar (eTs E) q) := fun q => by
    have : tVar (eTs E) q < 64 := bits_lt _ _ 6
    simp only [x']
    rw [if_neg (by omega)]
  obtain ⟨cp, cn, P, Q, hk, hle⟩ :=
    linAcc_row (box := box) (v := 64) (E := E) x' (fun q hq => by rw [hx']; exact hS _ (hE.1 q hq)) h
  have hsum : rowSum E x' = rowSum E s.x := Finset.sum_congr rfl (fun q _ => by rw [hx'])
  have h64 : x' 64 = 0 := by simp [x']
  rw [h64, mul_zero, zero_add, hsum] at hle
  exact emptyFin_sound _ cp cn P Q _ hle (hE.2 s) hk

theorem recOK_of_linRec {g box it : ℕ} (hv : validCtx g = true) (h : linRec g box it = true) :
    RecOK g box it := by
  obtain ⟨hj, hr⟩ := linRec_spec h
  have hE := validCtx_sound hv _ hj
  intro s hS
  rcases hr with ⟨hn, hacc⟩ | hacc
  · obtain ⟨cp, cn, P, Q, hk, hle⟩ :=
      linAcc_row s.x (fun q hq => hS _ (hE.1 q hq)) hacc
    have hfin := recFin_sound _ _ _ cp cn P Q _ _ hle (hE.2 s) hk
    rw [← keyVal_kgood hn] at hfin
    exact boxMem_set (bits_lt it 0 64) hS (fun h0 => hfin.2 (by omega)) (fun h1 => hfin.1 h1)
  · exact (empty_of hE s hS hacc).elim

theorem killOK_of_linKill {g box it : ℕ} (hv : validCtx g = true) (h : linKill g box it = true) :
    KillOK g box := by
  obtain ⟨hj, hacc⟩ := linKill_spec h
  have hE := validCtx_sound hv _ hj
  intro s hS
  exact (empty_of hE s hS hacc).elim

theorem ctxOK_valid {g last : ℕ} (hl : last = 0 ∨ validCtx (last - 1) = true) (h : ctxOK g last = true) :
    validCtx g = true := by
  unfold ctxOK at h
  cases hb : Nat.beq (Nat.succ g) last
  · rw [hb] at h
    exact h
  · rw [Nat.beq_eq] at hb
    rcases hl with hl | hl
    · omega
    · rw [← hb] at hl
      simpa using hl

theorem lin_step {ev : Ev} {s : Bool × ℕ} (hs : s.1 = true → s.2 = 0 ∨ validCtx (s.2 - 1) = true)
    (h : (linChecker.step ev s).1 = true) :
    s.1 = true ∧ ev.OK ∧ ((linChecker.step ev s).2 = 0 ∨ validCtx ((linChecker.step ev s).2 - 1) = true) := by
  cases ev with
  | record g box it =>
    change (s.1 && ctxOK g s.2 && linRec g box it) = true at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, hc⟩, hr⟩ := h
    have hvg := ctxOK_valid (hs h1) hc
    exact ⟨h1, recOK_of_linRec hvg hr, Or.inr (by change validCtx (Nat.succ g - 1) = true; simpa using hvg)⟩
  | kill g box it =>
    change (s.1 && ctxOK g s.2 && linKill g box it) = true at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, hc⟩, hr⟩ := h
    have hvg := ctxOK_valid (hs h1) hc
    exact ⟨h1, killOK_of_linKill hvg hr, Or.inr (by change validCtx (Nat.succ g - 1) = true; simpa using hvg)⟩

theorem lin_fold : ∀ (l : List Ev) (s : Bool × ℕ), (s.1 = true → s.2 = 0 ∨ validCtx (s.2 - 1) = true) →
    (l.foldl (fun s e => linChecker.step e s) s).1 = true → s.1 = true ∧ ∀ e ∈ l, e.OK := by
  intro l
  induction l with
  | nil => exact fun s _ h => ⟨h, fun e he => by simp at he⟩
  | cons ev l ih =>
    intro s hs h
    change (List.foldl (fun s e => linChecker.step e s) (linChecker.step ev s) l).1 = true at h
    have hinv : (linChecker.step ev s).1 = true →
        (linChecker.step ev s).2 = 0 ∨ validCtx ((linChecker.step ev s).2 - 1) = true :=
      fun h1 => (lin_step hs h1).2.2
    obtain ⟨h1, hl⟩ := ih _ hinv h
    obtain ⟨hs1, hev, -⟩ := lin_step hs h1
    refine ⟨hs1, fun e he => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact hev
    · exact hl e he

theorem linChecker_sound : linChecker.Sound (kindIs 0) := by
  intro tr _ _ hfin
  exact (lin_fold tr linChecker.init (fun _ => Or.inl rfl) hfin).2

end Tammes15.D3Kernel.Kinds
