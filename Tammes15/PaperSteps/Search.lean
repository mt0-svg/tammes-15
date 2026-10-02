import Tammes15.PaperSteps.SearchDefs
import Tammes15.Trigrows.Rows
import Tammes15.TwoConn.Blocks

/-!
# Soundness of the level-2 search, from the replayed trees to `ProgKilled`

Proposition 5.6 (2) of the paper with the narrowings of the program as parameters. The
variables `PVar`, the procedures `Procs` and their soundness `Procs.Sound`, the leaf test
`LeafKill` and the replayed trees `ProgTrees` are defined in SearchDefs.lean.

* `progKilled_of_progTrees`: `ProgTrees L N` and `N.Sound` give `ProgKilled L`.
-/

open Real Matrix
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15 Search

open scoped Classical

variable {P : PlaneGraph} {k : ℕ}

/-! ## The variables of the program -/

/-- The key of a dart determines it. -/
theorem dartKey_inj {e e' : P.G.Dart} (h : dartKey e = dartKey e') : e = e' := by
  unfold dartKey at h
  have hb := e.snd.isLt
  have hb' := e'.snd.isLt
  have hn : 0 < P.n := by omega
  have key : ∀ a b : ℕ, b < P.n → (a * P.n + b) / P.n = a := fun a b hb => by
    rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
  have k1 := key e.fst.val e.snd.val hb
  have k2 := key e'.fst.val e'.snd.val hb'
  rw [h] at k1
  have h1 : e.fst.val = e'.fst.val := k1.symm.trans k2
  have h2 : e.snd.val = e'.snd.val := by rw [h1] at h; omega
  exact SimpleGraph.Dart.ext _ _ (Prod.ext (Fin.ext h1) (Fin.ext h2))

/-- The two opposite corners of a rhombus have the same variable. -/
theorem cvar_face_two (e : P.G.Dart) (he : fsize P e = 4) :
    (cvar ((P.R.face ^ 2) e) : PVar P k) = cvar e := by
  have he4 : Function.minimalPeriod P.R.face e = 4 := he
  have hper : Function.IsPeriodicPt P.R.face 4 e := by
    have := Function.isPeriodicPt_minimalPeriod P.R.face e
    rwa [he4] at this
  have hee : (P.R.face ^ 2) ((P.R.face ^ 2) e) = e := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, ← Equiv.Perm.iterate_eq_pow]
    exact hper
  have hfs : fsize P ((P.R.face ^ 2) e) = 4 := by
    unfold fsize
    rw [← Equiv.Perm.iterate_eq_pow,
      Function.minimalPeriod_apply_iterate (Function.mk_mem_periodicPts (by norm_num) hper)]
    exact he4
  unfold cvar
  simp only [hee, hfs, he, show (4 : ℕ) ≠ 3 by norm_num, ↓reduceIte]
  split_ifs with h1 h2 h2
  · rw [dartKey_inj (le_antisymm h1 h2)]
  · rfl
  · rfl
  · omega

/-! ## The root box -/

/-- The root box holds the values of every solution with `d` in the range of the run. -/
theorem root_mem {H : HexChoice P k} {lo hi : ℝ} {B : Box (PVar P k)} (hB : RootOK lo hi B)
    {A : Assign P k} (hA : A ∈ Sol P H) (hlo : lo ≤ A.d) (hhi : A.d ≤ hi) :
    B.Mem (PVar.val A) := by
  obtain ⟨hdlo, hdhi, hR⟩ := hA
  obtain ⟨ha, hc, hd, hr⟩ := hB
  have h1 := pi_div_four_lt_dlo
  have h2 := dhi_lt_pi_div_three
  have hpi := Real.pi_pos
  have hdI : A.d ∈ Set.Ioo 0 (π / 2) := ⟨by linarith, by linarith⟩
  have hloI : dlo ∈ Set.Ioo 0 (π / 2) := ⟨by linarith, by linarith⟩
  have hhiI : dhi ∈ Set.Ioo 0 (π / 2) := ⟨by linarith, by linarith⟩
  have hal : alpha dlo ≤ alpha A.d := alpha_strictMonoOn.monotoneOn hloI hdI hdlo
  have hah : alpha A.d ≤ alpha dhi := alpha_strictMonoOn.monotoneOn hdI hhiI hdhi
  intro i
  cases i with
  | a => exact ⟨ha.1.trans hal, hah.trans ha.2⟩
  | c e =>
    obtain ⟨hc0, hc3, hc4, hco⟩ := hc e
    obtain ⟨hm1, hm2⟩ := hR.corner_mem e
    refine ⟨hc0.trans (hal.trans hm1), ?_⟩
    show A.corner e ≤ B.hi (.c e)
    by_cases h3 : fsize P e = 3
    · rw [hR.tri e h3]; exact hah.trans (hc3 h3)
    by_cases h4 : fsize P e = 4
    · have hrh := (hR.rhombus e h4).2
      have hx : A.fc e 0 = A.corner e := by simp [Assign.fc]
      rw [hx] at hrh
      have := rhombus_rows A.d (A.corner e) (A.fc e 1) ⟨hdI.1, hdI.2⟩ hrh ⟨hm1, hm2⟩
        (hR.corner_mem ((P.R.face ^ 1) e)).1
      linarith [hc4 h4]
    · exact hm2.le.trans (hco h3 h4)
  | d => exact ⟨hd.1.trans hlo, hhi.trans hd.2⟩
  | r m j =>
    obtain ⟨hr1, hr2⟩ := (hR.wheel m).1 j
    obtain ⟨hb1, hb2⟩ := hr m j
    refine ⟨hb1.trans (hlo.trans hr1), ?_⟩
    show A.r m j ≤ B.hi (.r m j)
    linarith

/-- The variable of a corner encloses the corner of a solution. -/
theorem cvar_mem {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H) {B : Box (PVar P k)}
    (hB : B.Mem (PVar.val A)) (e : P.G.Dart) :
    B.lo (cvar e) ≤ A.corner e ∧ A.corner e ≤ B.hi (cvar e) := by
  have hR : RelSys P H A := hA.2.2
  unfold cvar
  split_ifs with h3 h4 hk
  · have h := hB .a
    simp only [PVar.val] at h
    rw [hR.tri e h3]
    exact h
  · exact hB (.c e)
  · have h := hB (.c ((P.R.face ^ 2) e))
    simp only [PVar.val] at h
    have he : A.corner ((P.R.face ^ 2) e) = A.corner e := by
      have := (hR.rhombus e h4).1
      simpa [Assign.fc] using this
    rw [he] at h
    exact h
  · exact hB (.c e)

/-! ## Enclosure of the turns -/

/-- The rotation system with the inverse rotation (the program's rotation order). -/
def rotInv {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (R : RotSys G) : RotSys G where
  rot := R.rot.symm
  rot_fst x := by
    have h := R.rot_fst (R.rot.symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  rot_cycle x y h := Equiv.Perm.sameCycle_inv.mpr (R.rot_cycle x y h)

/-- The darts at a vertex are the iterates of `rot⁻¹` over one period, each once. -/
theorem sum_range_rotDeg (a : P.G.Dart) (f : P.G.Dart → ℝ) :
    ∑ t ∈ Finset.range (rotDeg a), f ((P.R.rot.symm ^ (t + 1)) a) =
      ∑ e ∈ Finset.univ.filter (fun e : P.G.Dart => e.fst = a.fst), f e := by
  rw [sum_darts_at_eq_sum_rot (rotInv P.R) a f]
  show _ = ∑ i ∈ Finset.range (rotDeg a), f ((P.R.rot.symm ^ i) a)
  have hper : (P.R.rot.symm ^ rotDeg a) a = a := by
    rw [← Equiv.Perm.iterate_eq_pow]
    exact Function.iterate_minimalPeriod
  obtain ⟨j, hj, -⟩ := rot_pow_surj (rotInv P.R) a a rfl
  obtain ⟨q, hq⟩ : ∃ q, rotDeg a = q + 1 := ⟨rotDeg a - 1, by unfold rotDeg; simp only [rotInv] at hj; omega⟩
  rw [hq] at hper ⊢
  rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun i => f ((P.R.rot.symm ^ i) a)), hper,
    pow_zero, Equiv.Perm.one_apply]

/-- The program's turn passes at most the darts of the vertex. -/
theorem turnStepsR_le_rotDeg {a b : P.G.Dart} (hab : a.fst = b.fst) :
    turnStepsR P.R a b ≤ rotDeg a := by
  obtain ⟨j, hj, hjb⟩ := rot_pow_surj (rotInv P.R) a b hab.symm
  have h : ∃ s, (P.R.rot.symm ^ s) a = b := ⟨j, hjb⟩
  unfold turnStepsR
  split_ifs with h'
  · exact (Nat.find_min' h' hjb).trans hj.le
  · exact absurd h h'

/-- The turn of a solution in a box lies in the enclosure. -/
theorem turnR_mem {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H) {B : Box (PVar P k)}
    (hB : B.Mem (PVar.val A)) {a b : P.G.Dart} (hab : a.fst = b.fst) :
    turnLo B a b ≤ turnR A a b ∧ turnR A a b ≤ turnHi B a b := by
  have hsp : turnStepsR P.R a b ≤ rotDeg a := turnStepsR_le_rotDeg hab
  have htot : ∑ t ∈ Finset.range (turnStepsR P.R a b), A.corner ((P.R.rot.symm ^ (t + 1)) a) +
      ∑ t ∈ Finset.Ico (turnStepsR P.R a b) (rotDeg a), A.corner ((P.R.rot.symm ^ (t + 1)) a) =
      2 * π := by
    rw [Finset.sum_range_add_sum_Ico _ hsp, sum_range_rotDeg a A.corner]
    exact hA.2.2.vertex_sum a.fst
  have hl1 : ∑ t ∈ Finset.range (turnStepsR P.R a b), B.lo (cvar ((P.R.rot.symm ^ (t + 1)) a)) ≤
      ∑ t ∈ Finset.range (turnStepsR P.R a b), A.corner ((P.R.rot.symm ^ (t + 1)) a) :=
    Finset.sum_le_sum fun t _ => (cvar_mem hA hB _).1
  have hu1 : ∑ t ∈ Finset.range (turnStepsR P.R a b), A.corner ((P.R.rot.symm ^ (t + 1)) a) ≤
      ∑ t ∈ Finset.range (turnStepsR P.R a b), B.hi (cvar ((P.R.rot.symm ^ (t + 1)) a)) :=
    Finset.sum_le_sum fun t _ => (cvar_mem hA hB _).2
  have hl2 : ∑ t ∈ Finset.Ico (turnStepsR P.R a b) (rotDeg a),
        B.lo (cvar ((P.R.rot.symm ^ (t + 1)) a)) ≤
      ∑ t ∈ Finset.Ico (turnStepsR P.R a b) (rotDeg a), A.corner ((P.R.rot.symm ^ (t + 1)) a) :=
    Finset.sum_le_sum fun t _ => (cvar_mem hA hB _).1
  have hu2 : ∑ t ∈ Finset.Ico (turnStepsR P.R a b) (rotDeg a),
        A.corner ((P.R.rot.symm ^ (t + 1)) a) ≤
      ∑ t ∈ Finset.Ico (turnStepsR P.R a b) (rotDeg a),
        B.hi (cvar ((P.R.rot.symm ^ (t + 1)) a)) :=
    Finset.sum_le_sum fun t _ => (cvar_mem hA hB _).2
  unfold turnLo turnHi turnR
  exact ⟨max_le hl1 (by linarith), le_min hu1 (by linarith)⟩

/-! ## From the leaves to the configuration glued from a solution -/

/-- The program's frames are the frames with the program's turns. -/
theorem progFrameN_eq_frameAng (g : GlueData P k) (A : Assign P k) (n : ℕ) (v : Fin P.n) :
    progFrameN g A n v =
      frameAng g (fun w => turnR A (g.refD (g.par w).fst) (g.par w)) A.d n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [progFrameN, frameAng, ih]

/-- The frames are rotations: they preserve norms. -/
theorem frameAng_norm (g : GlueData P k) (φ : Fin P.n → ℝ) (δ : ℝ) (n : ℕ) (v : Fin P.n)
    (w : E3) : ‖toEuclideanLin (frameAng g φ δ n v) w‖ = ‖w‖ := by
  induction n generalizing v w with
  | zero => simp [frameAng]
  | succ n ih =>
    simp only [frameAng]
    split_ifs
    · simp
    · rw [toEuclideanLin_mul_apply, ih, stepM_norm_apply]

/-- Two frames with turns and steps within the radii differ by at most the radius of the frame, in
operator norm. -/
theorem frameAng_sub_le (g : GlueData P k) (φ φ' : Fin P.n → ℝ) (δ δ' : ℝ) (pr : Fin P.n → ℝ)
    (dr : ℝ) (hφ : ∀ v, v ≠ g.root → |φ v - φ' v| ≤ pr v) (hδ : |δ - δ'| ≤ dr) (n : ℕ)
    (v : Fin P.n) (w : E3) :
    ‖toEuclideanLin (frameAng g φ δ n v) w - toEuclideanLin (frameAng g φ' δ' n v) w‖ ≤
      radN g pr dr n v * ‖w‖ := by
  induction n generalizing v w with
  | zero => simp [frameAng, radN]
  | succ n ih =>
    simp only [frameAng, radN]
    split_ifs with hv
    · simp
    · set u := (g.par v).fst
      rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
      set S := toEuclideanLin (stepM (φ v) δ) w
      set S' := toEuclideanLin (stepM (φ' v) δ') w
      have h1 : ‖toEuclideanLin (frameAng g φ δ n u) S - toEuclideanLin (frameAng g φ δ n u) S'‖ =
          ‖S - S'‖ := by rw [← map_sub, frameAng_norm]
      have h2 := ih u S'
      have h3 : ‖S - S'‖ ≤ (|φ v - φ' v| + |δ - δ'|) * ‖w‖ := stepM_sub_apply_le _ _ _ _ w
      have h4 : ‖S'‖ = ‖w‖ := stepM_norm_apply _ _ w
      have hw := norm_nonneg w
      have h5 : (|φ v - φ' v| + |δ - δ'|) * ‖w‖ ≤ (pr v + dr) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (add_le_add (hφ v hv) hδ) hw
      calc ‖toEuclideanLin (frameAng g φ δ n u) S - toEuclideanLin (frameAng g φ' δ' n u) S'‖
          ≤ ‖toEuclideanLin (frameAng g φ δ n u) S - toEuclideanLin (frameAng g φ δ n u) S'‖ +
            ‖toEuclideanLin (frameAng g φ δ n u) S' - toEuclideanLin (frameAng g φ' δ' n u) S'‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (pr v + dr) * ‖w‖ + radN g pr dr n u * ‖w‖ := by
            rw [h1, ← h4]; rw [h4] at h2 ⊢; linarith
        _ = (radN g pr dr n u + pr v + dr) * ‖w‖ := by ring

/-- The reference dart of a vertex starts at it. -/
theorem refD_fst_of_valid {g : GlueData P k} (hg : g.Valid) (v : Fin P.n) :
    (g.refD v).fst = v := by
  unfold GlueData.refD
  split_ifs with h
  · rw [h]; exact hg.root_fst
  · exact hg.par_snd v h

/-- The dart towards `A_{i-1}` starts at `A_i`. -/
theorem freeBack_fst (H : HexChoice P k) (g : GlueData P k) (m : Fin k) :
    (freeBack H g m).fst = (freeDart H g m).fst := by
  have hface : ∀ x : P.G.Dart, (P.R.face x).fst = x.snd := by
    intro x
    have h := P.R.rot_fst (P.R.rot.symm x.symm)
    rw [Equiv.apply_symm_apply] at h
    simp only [RotSys.face, Equiv.trans_apply, Function.Involutive.coe_toPerm]
    rw [← h]
    rfl
  have key : ∀ j : ℕ, ((P.R.face ^ (j + 1)) (H.base m)).fst = ((P.R.face ^ j) (H.base m)).snd := by
    intro j
    rw [pow_succ', Equiv.Perm.mul_apply, hface]
  have h6 : (P.R.face ^ (5 + 1)) (H.base m) = H.base m := by
    rw [← Equiv.Perm.iterate_eq_pow, show 5 + 1 = Function.minimalPeriod P.R.face (H.base m) from
      (H.hex m).symm]
    exact Function.iterate_minimalPeriod
  unfold freeBack freeDart
  rw [SimpleGraph.Dart.symm_toProd, Prod.fst_swap]
  generalize g.freeCorner m = i
  by_cases hi : i = 0
  · subst hi
    rw [show ((0 - 1 : Fin 6) : ℕ) = 5 from rfl, ← key 5, h6]
    simp
  · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    have hii : ((i - 1 : Fin 6) : ℕ) + 1 = (i : ℕ) := by
      simp only [Fin.coe_sub_one, hi, ↓reduceIte]
      omega
    rw [← key, hii]

/-- The enclosure: if the centres and radii cover a box, the configuration that the program glues
from a solution in the box is within the radius of the configuration glued from the centres, point
by point. -/
theorem glue_enclosure {N : Procs} (hN : N.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : B.Mem (PVar.val A)) {g : GlueData P k}
    (hg : g.Valid) {E : Encl P k} (hE : E.Covers (N.wheel P k) H g B) (p : Pts P k) :
    ‖progGlueY H A g p - glueC H g E p‖ ≤ radC H g E p := by
  obtain ⟨hd, hstep, hfree, hr⟩ := hE
  have hφ : ∀ v, v ≠ g.root →
      |turnR A (g.refD (g.par v).fst) (g.par v) - E.pc v| ≤ E.pr v := by
    intro v hv
    obtain ⟨h1, h2⟩ := turnR_mem hA hB (refD_fst_of_valid hg (g.par v).fst)
    obtain ⟨h3, h4⟩ := hstep v hv
    rw [abs_le]
    constructor <;> linarith
  have hδ : |A.d - E.dc| ≤ E.dr := by
    have h := hB .d
    simp only [PVar.val] at h
    rw [abs_le]
    constructor <;> linarith [hd.1, hd.2]
  have hF : ∀ (n : ℕ) (v : Fin P.n) (w : E3),
      ‖toEuclideanLin (progFrameN g A n v) w - toEuclideanLin (frameAng g E.pc E.dc n v) w‖ ≤
        radN g E.pr E.dr n v * ‖w‖ := by
    intro n v w
    rw [progFrameN_eq_frameAng]
    exact frameAng_sub_le g _ E.pc A.d E.dc E.pr E.dr hφ hδ n v w
  have he3 : ‖e3‖ = 1 := by simp [e3]
  cases p with
  | inl v =>
    have h := hF (g.depth v) v e3
    rw [he3, mul_one] at h
    simpa only [progGlueY, glueC, radC, progFrame] using h
  | inr m =>
    set a := (freeDart H g m).fst with ha
    set i := g.freeCorner m with hi
    set ψ := turnR A (g.refD a) (freeBack H g m) + gam (A.r m (i - 1)) (A.r m i) A.d with hψ
    have hψ' : |ψ - E.qc m| ≤ E.qr m := by
      obtain ⟨β, hβ, h1, h2⟩ := hfree m
      have hfst : (g.refD a).fst = (freeBack H g m).fst := by
        rw [refD_fst_of_valid hg, freeBack_fst]
      obtain ⟨h3, h4⟩ := turnR_mem hA hB hfst
      obtain ⟨h5, h6⟩ := (hN P k H).2 A hA B hB m i β hβ
      rw [abs_le]
      constructor <;> linarith
    have hr' : |A.r m i - E.rc m| ≤ E.rr m := by
      have h := hB (.r m i)
      simp only [PVar.val] at h
      obtain ⟨h1, h2⟩ := hr m
      rw [abs_le]
      constructor <;> linarith
    set F := progFrameN g A (g.depth a) a with hFdef
    set F' := frameAng g E.pc E.dc (g.depth a) a with hF'def
    set y := toEuclideanLin (rotY (A.r m i)) e3 with hy
    set y' := toEuclideanLin (rotY (E.rc m)) e3 with hy'
    set x := toEuclideanLin (rotZ ψ) y with hx
    set x' := toEuclideanLin (rotZ (E.qc m)) y' with hx'
    have hyn : ‖y‖ = 1 := by rw [hy, norm_rotY_apply, he3]
    have hxn : ‖x‖ = 1 := by rw [hx, norm_rotZ_apply, hyn]
    have hYp : progGlueY H A g (.inr m) = toEuclideanLin F x := by
      simp only [progGlueY, progFrame, hFdef, hx, hy, hψ, ha, hi, freeDart, freeBack,
        toEuclideanLin_mul_apply]
    have hYc : glueC H g E (.inr m) = toEuclideanLin F' x' := by
      simp only [glueC, hF'def, hx', hy', ha, toEuclideanLin_mul_apply]
    have hR : radC H g E (.inr m) = radN g E.pr E.dr (g.depth a) a + E.qr m + E.rr m := by
      simp only [radC, ha]
    rw [hYp, hYc, hR]
    have h1 : ‖toEuclideanLin F x - toEuclideanLin F' x‖ ≤ radN g E.pr E.dr (g.depth a) a := by
      have h := hF (g.depth a) a x
      rwa [hxn, mul_one] at h
    have h2 : ‖toEuclideanLin F' x - toEuclideanLin F' x'‖ = ‖x - x'‖ := by
      rw [← map_sub, frameAng_norm]
    have h3 : ‖x - x'‖ ≤ ‖x - toEuclideanLin (rotZ (E.qc m)) y‖ +
        ‖toEuclideanLin (rotZ (E.qc m)) y - x'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h4 : ‖x - toEuclideanLin (rotZ (E.qc m)) y‖ ≤ |ψ - E.qc m| := by
      have h := rotZ_sub_apply_le ψ (E.qc m) y
      rwa [hyn, mul_one] at h
    have h5 : ‖toEuclideanLin (rotZ (E.qc m)) y - x'‖ ≤ |A.r m i - E.rc m| := by
      rw [hx', ← map_sub, norm_rotZ_apply]
      have h := rotY_sub_apply_le (A.r m i) (E.rc m) e3
      rwa [he3, mul_one] at h
    calc ‖toEuclideanLin F x - toEuclideanLin F' x'‖
        ≤ ‖toEuclideanLin F x - toEuclideanLin F' x‖ + ‖toEuclideanLin F' x - toEuclideanLin F' x'‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ radN g E.pr E.dr (g.depth a) a + E.qr m + E.rr m := by
          rw [h2]; linarith

/-- Pair on the enclosure fires Pair on the configuration. -/
theorem pairFires_of_pairC {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H)
    {B : Box (PVar P k)} (hB : B.Mem (PVar.val A)) {g : GlueData P k} {E : Encl P k}
    {Y : Pts P k → E3} (hY : ∀ p, ‖Y p - glueC H g E p‖ ≤ radC H g E p) (h : PairC H g E B) :
    PairFires P A Y := by
  obtain ⟨h0, a, b, hab, hadj, hlt⟩ := h
  refine ⟨a, b, hab, hadj, ?_⟩
  have hd := hB .d
  simp only [PVar.val] at hd
  have hdhi : A.d ≤ dhi := hA.2.1
  have hpi := dhi_lt_pi_div_three
  have hsin : sin (B.lo .d / 2) ≤ sin (A.d / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  have ha := hY a
  have hb := hY b
  calc ‖Y a - Y b‖ ≤ ‖Y a - glueC H g E a‖ + ‖glueC H g E a - glueC H g E b‖ +
        ‖glueC H g E b - Y b‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (Y a) (glueC H g E a) (Y b)
        have := norm_sub_le_norm_sub_add_norm_sub (glueC H g E a) (glueC H g E b) (Y b)
        linarith
    _ ≤ radC H g E a + ‖glueC H g E a - glueC H g E b‖ + radC H g E b := by
        rw [norm_sub_rev (glueC H g E b)]; linarith
    _ < 2 * sin (B.lo .d / 2) := by linarith
    _ ≤ 2 * sin (A.d / 2) := by linarith

/-- Local on the enclosure fires Local on the configuration. -/
theorem tieFires_of_tieC {H : HexChoice P k} {g : GlueData P k} {E : Encl P k}
    {Y : Pts P k → E3} (hY : ∀ p, ‖Y p - glueC H g E p‖ ≤ radC H g E p) (h : TieC H g E) :
    TieFires Y := by
  obtain ⟨c, e, he, ab, hab, mirror, j, hz⟩ := h
  refine ⟨c, e, he, ab, hab, mirror, j, fun z hzc v => ?_⟩
  have h1 := hz z hzc v
  have h2 := hY v
  calc ‖Y v - tieNormalize (z ab.1) (z ab.2) mirror (z (j v))‖
      ≤ ‖Y v - glueC H g E v‖ + ‖glueC H g E v - tieNormalize (z ab.1) (z ab.2) mirror (z (j v))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ rLocal := by linarith

/-- A leaf that passes the test of the program fires Pair or Local on the configuration glued from
every solution in its box. -/
theorem leafKill_sound {N : Procs} (hN : N.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : B.Mem (PVar.val A)) (h : LeafKill N P H B) :
    ∃ g : GlueData P k, g.Valid ∧
      (PairFires P A (progGlueY H A g) ∨ TieFires (progGlueY H A g)) := by
  obtain ⟨g, hg, E, hE, hPT⟩ := h
  have hY := glue_enclosure hN hA hB hg hE
  refine ⟨g, hg, ?_⟩
  rcases hPT with hP | hT
  · exact Or.inl (pairFires_of_pairC hA hB hY hP)
  · exact Or.inr (tieFires_of_tieC hY hT)

/-! ## The verdicts -/

/-- Proposition 5.6 (2): the trees that the replays accept, with sound procedures, give
the verdicts of the program in pointwise form. -/
theorem progKilled_of_progTrees {L : Set PlaneGraph} {N : Procs} (h : ProgTrees L N)
    (hN : N.Sound) : ProgKilled L := by
  intro P hP k hk H
  obtain ⟨H₀, hH₀, hT⟩ := h P hP k hk H
  refine ⟨H₀, hH₀, fun A hdlo hdhi hR => ?_⟩
  have hA : A ∈ Sol P H₀ := ⟨hdlo, hdhi, hR⟩
  obtain ⟨lo, hi, hlo, hhi, m, B₀, t, hroot, hok⟩ := hT A.d hdlo hdhi
  obtain ⟨B', hB', hK⟩ :=
    Search.Tree.sound ((hN P k H₀).1 m) t B₀ hok A hA (root_mem hroot hA hlo hhi)
  exact leafKill_sound hN hA hB' hK

end Tammes15.PaperSteps
