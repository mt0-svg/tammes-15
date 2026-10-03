import Tammes15.FaceChain.Basic
import Tammes15.Vendor.EM8.BoundaryFaceSupport
import Tammes15.Vendor.EM8.EmptyContactSector
import Tammes15.Draw.Angular
import Tammes15.TwoConn.Farm
import Tammes15.Trigrows.Points
import Tammes15.Trigrows.Sdist

/-!
# Lemma A.7 through the eight-point face chain

Lemma A.7 of the paper in cone form (`StrictSupportFace`), from the face chain of
Kryvonos, Liehr and Taylor (arXiv 2609.22077, the vendored library `VendorEM8`), which the port
states for any number of points (`Fin nPts`) and with the two-connectivity of the contacts
(`ContactTwoConnected`) in place of their bound `c ≤ aInf`, the only use the chain made of it.

* `boundary_strictSupport`: every boundary cycle of the contact graph of a configuration whose
  contacts are two-connected has strict support (the vendored chain).
* `Setup`: the data of Lemma A.7 for vertices `Fin n`: a drawing `x` of its contact graph `G`
  at distance `d`, with an angular rotation system `R` whose corners lie in `(0, π)`.
* The bridge from a `Setup` to the eight-point objects at `c = cos d`: a configuration
  (`Setup.hY`), the inner product bound (`Setup.bound`), contacts (`Setup.contactAdj_iff`),
  two-connectivity (`Setup.twoConnected`), irreducibility (`Setup.irreducible`), darts
  (`Setup.dartEquiv`), the rotation (`Setup.dartEquiv_rotate`) and the faces
  (`Setup.dartEquiv_faceNext`), and strict support (`Setup.strictSupportFace_of_boundary`).
* `Setup.strictSupportFace`: Lemma A.7 in cone form.
-/

open Real Matrix WithLp InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15.FaceChain

open Tammes15.Vendor.EM8.SquareAntiprismVerification

/-- The face chain for any number of points: every boundary cycle has strict support. -/
theorem boundary_strictSupport {n : ℕ} (Y : Fin n → E3) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (hirr : PackingIrreducible c Y) (hconn : ContactTwoConnected Y c)
    (C : ContactBoundaryCycle Y c hY hc) : C.StrictSupport :=
  C.strict_support_of_weak_support hirr hbound (C.weak_support_from_actual_face hconn hbound hirr)

/-- The data of Lemma A.7 for vertices `Fin n`: unit vectors `x` at pairwise distance at least
`d`, their contact graph `G` at distance `d`, and an angular rotation system `R` of it whose
corners lie in `(0, π)`. -/
structure Setup (n : ℕ) where
  d : ℝ
  x : Fin n → E3
  G : SimpleGraph (Fin n)
  R : RotSys G
  hd : 0 < d ∧ d < π / 2
  unit : ∀ v, ‖x v‖ = 1
  sep : ∀ a b, a ≠ b → d ≤ sdist (x a) (x b)
  adj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ sdist (x a) (x b) = d
  angular : IsAngular R x
  corner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
    ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π

namespace Setup

variable {n : ℕ} (S : Setup n)

theorem hc : cos S.d ∈ Set.Ioo (0 : ℝ) 1 := by
  rcases S.hd with ⟨hpos, hbound⟩
  have hpos_cos : 0 < cos S.d := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  have h_lt_one : cos S.d < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by linarith) hpos
    simpa [Real.cos_zero] using this
  exact ⟨hpos_cos, h_lt_one⟩

theorem hY : IsConfiguration S.x := by
  refine ⟨?_, ?_⟩
  · intro i
    dsimp [unitSphere]
    exact S.unit i
  · intro a b h
    by_contra hne
    have hsep := S.sep a b hne
    have hsdist_self : sdist (S.x a) (S.x a) = 0 := by
      dsimp [sdist]
      have hnorm_sq : ⟪S.x a, S.x a⟫ = 1 := by
        calc
          ⟪S.x a, S.x a⟫ = ‖S.x a‖ ^ 2 := real_inner_self_eq_norm_sq _
          _ = 1 ^ 2 := by rw [S.unit a]
          _ = 1 := by norm_num
      rw [hnorm_sq, Real.arccos_one]
    have hsdist : sdist (S.x a) (S.x b) = 0 := by simpa [h] using hsdist_self
    rw [hsdist] at hsep
    have hpos : 0 < S.d := S.hd.1
    linarith

theorem bound : PackingInnerBound (cos S.d) S.x := by
  intro i j hij
  have hsep : S.d ≤ sdist (S.x i) (S.x j) := S.sep i j hij
  have hunit_i : ‖S.x i‖ = 1 := S.unit i
  have hunit_j : ‖S.x j‖ = 1 := S.unit j
  set t := inner ℝ (S.x i) (S.x j) with ht
  have h_abs : |t| ≤ 1 := by
    have h := abs_real_inner_le_norm (S.x i) (S.x j)
    calc
      |t| ≤ ‖S.x i‖ * ‖S.x j‖ := h
      _ = 1 * 1 := by simp [hunit_i, hunit_j]
      _ = 1 := by norm_num
  have ht_le_one : t ≤ 1 := by
    have := abs_le.mp h_abs
    exact this.2
  have ht_ge_neg_one : -1 ≤ t := by
    have := abs_le.mp h_abs
    exact this.1
  have hcos_eq : Real.cos (Real.arccos t) = t :=
    Real.cos_arccos ht_ge_neg_one ht_le_one
  have hd_pos : 0 ≤ S.d := by linarith [S.hd.1]
  have harccos_le_pi : Real.arccos t ≤ π := Real.arccos_le_pi t
  have h_cos_le : Real.cos (Real.arccos t) ≤ Real.cos S.d :=
    Real.cos_le_cos_of_nonneg_of_le_pi hd_pos harccos_le_pi hsep
  calc
    inner ℝ (S.x i) (S.x j) = t := rfl
    _ = Real.cos (Real.arccos t) := by rw [hcos_eq]
    _ ≤ Real.cos S.d := h_cos_le

theorem contactAdj_iff (a b : Fin n) : ContactAdj S.x (cos S.d) a b ↔ S.G.Adj a b := by
  have hd_pos : 0 ≤ S.d := le_of_lt S.hd.1
  have hd_le_pi : S.d ≤ π := by linarith [S.hd.2]
  have hinner_abs_le_one : |inner ℝ (S.x a) (S.x b)| ≤ 1 := by
    have h := abs_real_inner_le_norm (S.x a) (S.x b)
    rw [S.unit a, S.unit b, mul_one] at h
    exact h
  have hinner_range : -1 ≤ inner ℝ (S.x a) (S.x b) ∧ inner ℝ (S.x a) (S.x b) ≤ 1 :=
    abs_le.mp hinner_abs_le_one
  rcases hinner_range with ⟨hinner_low, hinner_high⟩
  constructor
  · intro h
    rcases h with ⟨hne, hinner_eq⟩
    have harccos_eq : arccos (inner ℝ (S.x a) (S.x b)) = S.d := by
      rw [hinner_eq]
      exact Real.arccos_cos hd_pos hd_le_pi
    refine (S.adj a b).mpr ⟨hne, ?_⟩
    dsimp [sdist]
    rw [harccos_eq]
  · intro h
    rcases (S.adj a b).mp h with ⟨hne, hsdist_eq⟩
    dsimp [sdist] at hsdist_eq
    have hinner_eq : inner ℝ (S.x a) (S.x b) = cos S.d := by
      calc
        inner ℝ (S.x a) (S.x b) = cos (arccos (inner ℝ (S.x a) (S.x b))) := by
          rw [Real.cos_arccos hinner_low hinner_high]
        _ = cos S.d := by rw [hsdist_eq]
    exact ⟨hne, hinner_eq⟩

theorem tdir_ne_zero (v w : Fin n) (h : S.G.Adj v w) : tdir (S.x v) (S.x w) ≠ 0 := by
  have hadj := (S.adj v w).mp h
  have hd_pos : 0 < S.d := S.hd.1
  have hd_lt_pi : S.d < π := by linarith [S.hd.2]
  have hnorm : ‖tdir (S.x v) (S.x w)‖ = sin (sdist (S.x v) (S.x w)) :=
    tdir_norm (S.x v) (S.x w) (S.unit v) (S.unit w)
  have hsdist : sdist (S.x v) (S.x w) = S.d := hadj.2
  have hsin_pos : 0 < sin (sdist (S.x v) (S.x w)) := by
    rw [hsdist]
    exact Real.sin_pos_of_pos_of_lt_pi hd_pos hd_lt_pi
  have hnorm_pos : 0 < ‖tdir (S.x v) (S.x w)‖ := by
    rw [hnorm]
    exact hsin_pos
  intro hzero
  have hzero_norm : ‖tdir (S.x v) (S.x w)‖ = 0 := by simpa [hzero] using norm_zero
  linarith

theorem ocorner_ne_zero (v a b : Fin n) (ha : S.G.Adj v a) (hb : S.G.Adj v b) (hab : a ≠ b) :
    ocorner (S.x v) (S.x a) (S.x b) ≠ 0 := by
  intro hzero
  have hv_unit : ‖S.x v‖ = 1 := S.unit v
  have ha_unit : ‖S.x a‖ = 1 := S.unit a
  have hb_unit : ‖S.x b‖ = 1 := S.unit b
  have hd_pos : 0 < S.d := S.hd.1
  have hd_lt_pi : S.d < π := by linarith [S.hd.2]
  -- from adjacency, get sdist = d for both pairs
  have ha_adj := (S.adj v a).mp ha
  have hb_adj := (S.adj v b).mp hb
  rcases ha_adj with ⟨hva_ne, hva_sdist⟩
  rcases hb_adj with ⟨hvb_ne, hvb_sdist⟩
  -- so inner products equal cos S.d
  have h_inner_eq : ⟪S.x v, S.x a⟫ = ⟪S.x v, S.x b⟫ := by
    calc
      ⟪S.x v, S.x a⟫ = cos (sdist (S.x v) (S.x a)) := by rw [← cos_sdist (S.x v) (S.x a) hv_unit ha_unit]
      _ = cos S.d := by rw [hva_sdist]
      _ = cos (sdist (S.x v) (S.x b)) := by rw [hvb_sdist]
      _ = ⟪S.x v, S.x b⟫ := by rw [cos_sdist (S.x v) (S.x b) hv_unit hb_unit]
  -- tdir (S.x v) (S.x a) ≠ 0
  have h_tdir_ne_zero : tdir (S.x v) (S.x a) ≠ 0 := by
    intro hzero_tdir
    have h_tdir_eq : S.x a - ⟪S.x v, S.x a⟫ • S.x v = 0 := hzero_tdir
    have h_eq : S.x a = ⟪S.x v, S.x a⟫ • S.x v := sub_eq_zero.mp h_tdir_eq
    -- take norms: ‖S.x a‖ = |⟪S.x v, S.x a⟫| * ‖S.x v‖
    have h_norm_eq : ‖S.x a‖ = |⟪S.x v, S.x a⟫| * ‖S.x v‖ := by
      have htemp := congrArg norm h_eq
      -- htemp : ‖S.x a‖ = ‖⟪S.x v, S.x a⟫ • S.x v‖
      rw [htemp, norm_smul, Real.norm_eq_abs]
    rw [ha_unit, hv_unit, mul_one] at h_norm_eq
    have h_abs_inner : |⟪S.x v, S.x a⟫| = 1 := by linarith
    have h_inner_range : -1 ≤ ⟪S.x v, S.x a⟫ ∧ ⟪S.x v, S.x a⟫ ≤ 1 := by
      have h_abs_le : |⟪S.x v, S.x a⟫| ≤ 1 := by
        have h_cs : |⟪S.x v, S.x a⟫| ≤ ‖S.x v‖ * ‖S.x a‖ := abs_real_inner_le_norm _ _
        rw [hv_unit, ha_unit, mul_one] at h_cs
        exact h_cs
      exact abs_le.mp h_abs_le
    -- from |inner| = 1 and -1 ≤ inner ≤ 1, we get inner = 1 or inner = -1
    have h_inner_cases : ⟪S.x v, S.x a⟫ = 1 ∨ ⟪S.x v, S.x a⟫ = -1 := by
      rcases eq_or_lt_of_le h_inner_range.2 with h | h
      · left; exact h
      · -- inner < 1, so inner must be -1 since |inner| = 1
        by_cases h_nonneg : 0 ≤ ⟪S.x v, S.x a⟫
        · -- then |inner| = inner, so inner = 1, contradiction with h
          have h_abs_eq : |⟪S.x v, S.x a⟫| = ⟪S.x v, S.x a⟫ := abs_of_nonneg h_nonneg
          rw [h_abs_eq] at h_abs_inner
          linarith
        · -- then inner < 0, so |inner| = -inner, so -inner = 1, so inner = -1
          have h_neg : ⟪S.x v, S.x a⟫ < 0 := by linarith
          have h_abs : |⟪S.x v, S.x a⟫| = -⟪S.x v, S.x a⟫ := abs_of_neg h_neg
          rw [h_abs] at h_abs_inner
          right; linarith
    rcases h_inner_cases with h | h
    · -- inner = 1, so S.x a = S.x v
      have h_eq_vec : S.x a = S.x v := by
        calc
          S.x a = ⟪S.x v, S.x a⟫ • S.x v := h_eq
          _ = (1 : ℝ) • S.x v := by rw [h]
          _ = S.x v := by simp
      have h_sdist_zero : sdist (S.x v) (S.x a) = 0 := by
        rw [h_eq_vec, sdist_self _ hv_unit]
      rw [hva_sdist] at h_sdist_zero
      linarith
    · -- inner = -1, so S.x a = -S.x v
      have h_eq_vec : S.x a = -S.x v := by
        calc
          S.x a = ⟪S.x v, S.x a⟫ • S.x v := h_eq
          _ = (-1 : ℝ) • S.x v := by rw [h]
          _ = -S.x v := by simp
      have h_sdist_pi : sdist (S.x v) (S.x a) = π := by
        rw [h_eq_vec]
        dsimp [sdist]
        rw [inner_neg_right]
        have h_inner_self : ⟪S.x v, S.x v⟫ = (1 : ℝ) := by
          rw [real_inner_self_eq_norm_sq, hv_unit]
          norm_num
        rw [h_inner_self]
        exact Real.arccos_neg_one
      rw [hva_sdist] at h_sdist_pi
      linarith
  -- apply eq_of_ocorner_eq_zero
  have h_points_eq : S.x a = S.x b :=
    eq_of_ocorner_eq_zero (S.x v) (S.x a) (S.x b) hv_unit ha_unit hb_unit h_inner_eq
      h_tdir_ne_zero hzero
  -- now a = b follows from sep and sdist_self
  have hsep := S.sep a b hab
  rw [h_points_eq] at hsep
  have h_sdist_self : sdist (S.x b) (S.x b) = 0 := sdist_self (S.x b) hb_unit
  rw [h_sdist_self] at hsep
  linarith

theorem twoConnected (h2 : KConnected S.G 2) : ContactTwoConnected S.x (cos S.d) := by
  intro root hroot v i j _hi _hj hne_i hne_j
  let T : Set (Fin n) := (({v} : Finset (Fin n)) : Set (Fin n))ᶜ
  have hcard : ({v} : Finset (Fin n)).card < 2 := by
    simp
  have hconnect := h2.2 {v} hcard
  have hi_mem : i ∈ T := by
    dsimp [T]
    rw [Set.mem_compl_iff, Finset.coe_singleton, Set.mem_singleton_iff]
    exact hne_i
  have hj_mem : j ∈ T := by
    dsimp [T]
    rw [Set.mem_compl_iff, Finset.coe_singleton, Set.mem_singleton_iff]
    exact hne_j
  let i' : T := ⟨i, hi_mem⟩
  let j' : T := ⟨j, hj_mem⟩
  have hreach_induced : (S.G.induce T).Reachable i' j' :=
    hconnect i' j'
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach_induced
  have hmem_not_singleton : ∀ (x : T), x.val ≠ v := by
    intro x
    intro h_eq
    have hx_notin_T : x.val ∉ T := by
      dsimp [T]
      simp [h_eq]
    exact hx_notin_T x.property
  have hstep : ∀ (a b : T),
      (S.G.induce T).Adj a b →
      (ContactAdj S.x (cos S.d) a.val b.val ∧ a.val ≠ v ∧ b.val ≠ v) := by
    intro a b hadj
    have hGadj : S.G.Adj a.val b.val := by
      rwa [SimpleGraph.induce_adj] at hadj
    have hcontact : ContactAdj S.x (cos S.d) a.val b.val :=
      (S.contactAdj_iff a.val b.val).mpr hGadj
    exact ⟨hcontact, hmem_not_singleton a, hmem_not_singleton b⟩
  have hlift := Relation.ReflTransGen.lift (α := T) (β := Fin n)
    (r := (S.G.induce T).Adj)
    (p := fun (i j : Fin n) => ContactAdj S.x (cos S.d) i j ∧ i ≠ v ∧ j ≠ v)
    (f := Subtype.val) (fun a b h => hstep a b h)
  -- hlift : Relation.ReflTransGen r ≤ Function.onFun (Relation.ReflTransGen p) f
  -- i.e., ∀ a b, r a b → Relation.ReflTransGen p (f a) (f b)
  have hresult : Relation.ReflTransGen (fun (i j : Fin n) => ContactAdj S.x (cos S.d) i j ∧ i ≠ v ∧ j ≠ v) i j :=
    hlift i' j' hreach_induced
  exact hresult

/-- If `z.re ≤ 0` and `z ≠ 0`, then `|z.arg| ≥ π/2`. -/
lemma _root_.Tammes15.FaceChain.abs_arg_ge_pi_div_two_of_re_nonpos {z : ℂ} (hre : z.re ≤ 0) (hz : z ≠ 0) : π/2 ≤ |z.arg| := by
  by_contra! h
  have h_abs_lt : |z.arg| < π/2 := by linarith
  have h_abs_le : |z.arg| ≤ π/2 := by linarith
  have h_re : 0 ≤ z.re := ((Complex.abs_arg_le_pi_div_two_iff).mp h_abs_le)
  have h_re_eq_zero : z.re = 0 := by linarith
  rcases ((Complex.abs_arg_lt_pi_div_two_iff).mp h_abs_lt) with (h_re_pos | hz_zero)
  · linarith
  · exact hz hz_zero

/-- If `z.re ≤ 0` and `z ≠ 0`, then `toIcoMod two_pi_pos 0 (z.arg) ∈ [π/2, 3π/2]`. -/
lemma _root_.Tammes15.FaceChain.toIcoMod_two_pi_pos_arg_mem_Icc_of_re_nonpos {z : ℂ} (hre : z.re ≤ 0) (hz : z ≠ 0) :
    toIcoMod Real.two_pi_pos 0 z.arg ∈ Set.Icc (π/2) (3*π/2) := by
  have h_abs : π/2 ≤ |z.arg| := abs_arg_ge_pi_div_two_of_re_nonpos hre hz
  have h_arg_mem : z.arg ∈ Set.Ioc (-π) π := Complex.arg_mem_Ioc z
  rcases h_arg_mem with ⟨h_low, h_high⟩
  by_cases h_nonneg : 0 ≤ z.arg
  · have h_arg_ge : π/2 ≤ z.arg := by
      have : |z.arg| = z.arg := abs_of_nonneg h_nonneg
      rw [this] at h_abs
      exact h_abs
    have h_mem : z.arg ∈ Set.Icc (π/2) (3*π/2) := by
      refine ⟨h_arg_ge, ?_⟩
      linarith
    have h_self : toIcoMod Real.two_pi_pos 0 z.arg = z.arg := by
      rw [toIcoMod_eq_self]
      refine ⟨by linarith, ?_⟩
      linarith [Real.two_pi_pos]
    rw [h_self]
    exact h_mem
  · have hz_neg : z.arg < 0 := by linarith
    have h_neg_ge : z.arg ≤ -π/2 := by
      have : |z.arg| = -z.arg := abs_of_neg hz_neg
      rw [this] at h_abs
      linarith
    have h_add_mem_Ico : z.arg + 2*π ∈ Set.Ico (0 : ℝ) (2*π) := by
      constructor
      · linarith
      · linarith
    have h_add_mem_target : z.arg + 2*π ∈ Set.Icc (π/2) (3*π/2) := by
      constructor
      · linarith
      · linarith
    have h_mod : toIcoMod Real.two_pi_pos 0 z.arg = z.arg + 2*π := by
      calc
        toIcoMod Real.two_pi_pos 0 z.arg = toIcoMod Real.two_pi_pos 0 (z.arg + 2*π) := by
          rw [toIcoMod_add_right]
        _ = z.arg + 2*π := by
          rw [toIcoMod_eq_self]
          simpa [add_comm] using h_add_mem_Ico
    rw [h_mod]
    exact h_add_mem_target

/-- For `δ ∈ [-π, 0)`, `toIcoMod two_pi_pos 0 δ = δ + 2π`. -/
lemma _root_.Tammes15.FaceChain.toIcoMod_two_pi_pos_of_neg {δ : ℝ} (hδ_low : -π ≤ δ) (hδ_high : δ < 0) :
    toIcoMod Real.two_pi_pos 0 δ = δ + 2*π := by
  have h_add_mem : δ + 2*π ∈ Set.Ico (0 : ℝ) (2*π) := by
    constructor
    · linarith
    · linarith
  calc
    toIcoMod Real.two_pi_pos 0 δ = toIcoMod Real.two_pi_pos 0 (δ + 2*π) := by
      rw [toIcoMod_add_right]
    _ = δ + 2*π := by
      rw [toIcoMod_eq_self]
      simpa [add_comm] using h_add_mem

theorem irreducible : PackingIrreducible (cos S.d) S.x := by
  classical
  intro i
  intro hcontact
  rcases hcontact with ⟨j, hj_ne, hj_inner⟩
  intro h
  rcases h with ⟨v, hv_norm, hv_orth, hv_nonpos⟩
  -- From hj_inner: inner ℝ (S.x i) (S.x j) = cos S.d
  -- Step 1: Show S.G.Adj i j
  have h_adj : S.G.Adj i j := by
    rw [S.adj i j]
    refine ⟨hj_ne.symm, ?_⟩
    have h_cos_sdist : cos (sdist (S.x i) (S.x j)) = ⟪S.x i, S.x j⟫ :=
      cos_sdist (S.x i) (S.x j) (S.unit i) (S.unit j)
    have h_cos_eq : cos (sdist (S.x i) (S.x j)) = cos S.d := by
      rw [h_cos_sdist, hj_inner]
    have h_sdist_mem : sdist (S.x i) (S.x j) ∈ Set.Icc (0 : ℝ) π := by
      dsimp [sdist]
      have h_inner : ⟪S.x i, S.x j⟫ ∈ Set.Icc (-1 : ℝ) 1 := by
        have h_abs : |⟪S.x i, S.x j⟫| ≤ ‖S.x i‖ * ‖S.x j‖ := abs_real_inner_le_norm _ _
        have h_norm : ‖S.x i‖ * ‖S.x j‖ = 1 := by simp [S.unit i, S.unit j]
        rw [h_norm] at h_abs
        constructor
        · linarith [abs_le.mp h_abs]
        · linarith [abs_le.mp h_abs]
      exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have h_d_mem : S.d ∈ Set.Icc (0 : ℝ) π := by
      rcases S.hd with ⟨hd_pos, hd_lt⟩
      exact ⟨by linarith, by linarith⟩
    apply Real.injOn_cos h_sdist_mem h_d_mem
    exact h_cos_eq
  -- Step 2: Get a dart from i to j
  let e : S.G.Dart := ⟨(i, j), h_adj⟩
  -- Step 3: The set of darts at i
  let darts_at_i : Finset S.G.Dart := Finset.filter (fun d => d.fst = i) Finset.univ
  have h_nonempty : darts_at_i.Nonempty := by
    refine ⟨e, ?_⟩
    simp [darts_at_i, e]
  -- Step 4: Pick a dart with maximal fangle
  obtain ⟨e', he', h_max⟩ := Finset.exists_max_image darts_at_i
    (fun d => fangle (S.x i) v (S.x d.snd)) h_nonempty
  -- Step 5: Define a and b
  set a := e'.snd with ha
  set b := (S.R.rot e').snd with hb
  have h_fst' : e'.fst = i := by
    simpa [darts_at_i] using he'
  have h_rot_fst : (S.R.rot e').fst = i := by
    rw [S.R.rot_fst e', h_fst']
  -- Step 6: a and b are neighbors of i
  have h_adj_ia : S.G.Adj i a := by
    rw [← h_fst', ha]
    exact e'.adj
  have h_adj_ib : S.G.Adj i b := by
    -- (S.R.rot e').fst = i, and (S.R.rot e').adj : S.G.Adj (S.R.rot e').fst (S.R.rot e').snd
    -- So S.G.Adj i b
    have h_fst' : (S.R.rot e').fst = i := h_rot_fst
    rw [← h_fst']
    exact (S.R.rot e').adj
  -- Step 7: fangle a and fangle b are in [π/2, 3π/2]
  have h_fangle_a_mem : fangle (S.x i) v (S.x a) ∈ Set.Icc (π/2) (3*π/2) := by
    -- Need: tcoord (S.x i) v (S.x a) has re ≤ 0 and ≠ 0
    have h_re_nonpos : (tcoord (S.x i) v (S.x a)).re ≤ 0 := by
      -- tcoord re = ⟪S.x a, v⟫
      -- hv_nonpos a ?_ ?_ gives inner ℝ v (S.x a) ≤ 0
      -- by real_inner_comm, these are equal
      have h_contact_a : inner ℝ (S.x i) (S.x a) = cos S.d := by
        have h_adj_ia' := ((S.adj i a).mp h_adj_ia)
        rcases h_adj_ia' with ⟨_, h_sdist_eq⟩
        have h_cos : cos (sdist (S.x i) (S.x a)) = ⟪S.x i, S.x a⟫ :=
          cos_sdist (S.x i) (S.x a) (S.unit i) (S.unit a)
        rw [h_sdist_eq] at h_cos
        rw [← h_cos]
      have h_v_nonpos : inner ℝ v (S.x a) ≤ 0 :=
        hv_nonpos a (h_adj_ia.ne).symm h_contact_a
      -- Now, (tcoord (S.x i) v (S.x a)).re = ⟪S.x a, v⟫ = inner ℝ (S.x a) v
      -- = inner ℝ v (S.x a) (by real_inner_comm) ≤ 0
      simpa [tcoord, real_inner_comm] using h_v_nonpos
    have h_ne_zero : tcoord (S.x i) v (S.x a) ≠ 0 := by
      intro hzero
      have h_tdir_ne_zero : tdir (S.x i) (S.x a) ≠ 0 := tdir_ne_zero S i a h_adj_ia
      have h_norm_eq : ‖tdir (S.x i) (S.x a)‖ = ‖tcoord (S.x i) v (S.x a)‖ :=
        norm_tdir_eq_norm_tcoord (S.x i) v (S.x a) (S.unit i) hv_norm hv_orth
      have h_norm_zero : ‖tdir (S.x i) (S.x a)‖ = 0 := by
        rw [h_norm_eq, hzero, norm_zero]
      rw [norm_eq_zero] at h_norm_zero
      exact h_tdir_ne_zero h_norm_zero
    -- Now use the lemma
    have h_mem := toIcoMod_two_pi_pos_arg_mem_Icc_of_re_nonpos h_re_nonpos h_ne_zero
    -- h_mem : toIcoMod Real.two_pi_pos 0 (tcoord (S.x i) v (S.x a)).arg ∈ Set.Icc (π/2) (3*π/2)
    -- But fangle (S.x i) v (S.x a) = toIcoMod Real.two_pi_pos 0 (Complex.arg (tcoord (S.x i) v (S.x a)))
    -- So we need to unfold fangle
    simpa [fangle] using h_mem
  have h_fangle_b_mem : fangle (S.x i) v (S.x b) ∈ Set.Icc (π/2) (3*π/2) := by
    have h_re_nonpos : (tcoord (S.x i) v (S.x b)).re ≤ 0 := by
      have h_contact_b : inner ℝ (S.x i) (S.x b) = cos S.d := by
        have h_adj_ib' := ((S.adj i b).mp h_adj_ib)
        rcases h_adj_ib' with ⟨_, h_sdist_eq⟩
        have h_cos : cos (sdist (S.x i) (S.x b)) = ⟪S.x i, S.x b⟫ :=
          cos_sdist (S.x i) (S.x b) (S.unit i) (S.unit b)
        rw [h_sdist_eq] at h_cos
        rw [← h_cos]
      have h_v_nonpos : inner ℝ v (S.x b) ≤ 0 :=
        hv_nonpos b (h_adj_ib.ne).symm h_contact_b
      simpa [tcoord, real_inner_comm] using h_v_nonpos
    have h_ne_zero : tcoord (S.x i) v (S.x b) ≠ 0 := by
      intro hzero
      have h_tdir_ne_zero : tdir (S.x i) (S.x b) ≠ 0 := tdir_ne_zero S i b h_adj_ib
      have h_norm_eq : ‖tdir (S.x i) (S.x b)‖ = ‖tcoord (S.x i) v (S.x b)‖ :=
        norm_tdir_eq_norm_tcoord (S.x i) v (S.x b) (S.unit i) hv_norm hv_orth
      have h_norm_zero : ‖tdir (S.x i) (S.x b)‖ = 0 := by
        rw [h_norm_eq, hzero, norm_zero]
      rw [norm_eq_zero] at h_norm_zero
      exact h_tdir_ne_zero h_norm_zero
    have h_mem := toIcoMod_two_pi_pos_arg_mem_Icc_of_re_nonpos h_re_nonpos h_ne_zero
    simpa [fangle] using h_mem
  -- By maximality of e', fangle b ≤ fangle a
  have h_fangle_le : fangle (S.x i) v (S.x b) ≤ fangle (S.x i) v (S.x a) := by
    -- We need to show that the dart with snd = b is in darts_at_i
    have h_dart_b_mem : S.R.rot e' ∈ darts_at_i := by
      simp [darts_at_i, h_rot_fst]
    exact h_max (S.R.rot e') h_dart_b_mem
  rcases h_fangle_a_mem with ⟨h_fa_low, h_fa_high⟩
  rcases h_fangle_b_mem with ⟨h_fb_low, h_fb_high⟩
  set δ := fangle (S.x i) v (S.x b) - fangle (S.x i) v (S.x a) with hδ
  have hδ_le : δ ≤ 0 := by linarith
  have hδ_ge : -π ≤ δ := by linarith
  -- Now use ocorner_eq_fangle_sub
  have h_ocorner_eq : ocorner (S.x i) (S.x a) (S.x b) = toIcoMod Real.two_pi_pos 0 δ := by
    rw [hδ]
    apply ocorner_eq_fangle_sub (S.x i) v (S.x a) (S.x b) (S.unit i) hv_norm hv_orth
    · exact tdir_ne_zero S i a h_adj_ia
    · exact tdir_ne_zero S i b h_adj_ib
  -- Get the corner bounds from S.corner e'
  have h_corner := S.corner e'
  rcases h_corner with ⟨h_corner_pos, h_corner_lt⟩
  -- Rewrite using the definitions of a and b
  rw [h_fst', ← ha, ← hb] at h_corner_pos h_corner_lt
  rw [h_ocorner_eq] at h_corner_pos h_corner_lt
  -- Now case analysis on δ
  by_cases hδ_zero : δ = 0
  · -- Then toIcoMod ... 0 = 0, contradiction
    rw [hδ_zero] at h_corner_pos
    simp at h_corner_pos
  · -- Then δ < 0, so toIcoMod two_pi_pos 0 δ = δ + 2π
    have hδ_neg : δ < 0 := by
      by_contra! h
      exact hδ_zero (by linarith)
    have h_mod : toIcoMod Real.two_pi_pos 0 δ = δ + 2*π :=
      toIcoMod_two_pi_pos_of_neg hδ_ge hδ_neg
    rw [h_mod] at h_corner_lt
    -- Now δ + 2π ≥ π (since δ ≥ -π), contradicting h_corner_lt : ... < π
    have h_ge_pi : π ≤ δ + 2*π := by linarith
    linarith

/-- The darts of the eight-point contact graph are the darts of `G`. -/
def dartEquiv : ContactDart S.x (cos S.d) ≃ S.G.Dart where
  toFun e := ⟨(e.1, e.2.val), (S.contactAdj_iff e.1 e.2.val).mp ⟨e.2.property.1.symm, e.2.property.2⟩⟩
  invFun e := ⟨e.fst, ⟨e.snd, e.adj.ne.symm, ((S.contactAdj_iff e.fst e.snd).mpr e.adj).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem dartEquiv_rotate (e : ContactDart S.x (cos S.d)) :
    S.dartEquiv (contactRotate S.x (cos S.d) S.hY S.hc e) = S.R.rot (S.dartEquiv e) := by
  obtain ⟨i, q⟩ := e
  have hq : S.G.Adj i q.val := (S.contactAdj_iff i q.val).mp ⟨q.2.1.symm, q.2.2⟩
  set g : S.G.Dart := S.R.rot (S.dartEquiv ⟨i, q⟩) with hg
  have hg1 : g.fst = i := S.R.rot_fst _
  have hadj : S.G.Adj i g.snd := hg1 ▸ g.adj
  have hr := (S.contactAdj_iff i g.snd).mpr hadj
  let r' : ContactNeighbor S.x (cos S.d) i := ⟨g.snd, hr.1.symm, hr.2⟩
  have hcorner : 0 < ocorner (S.x i) (S.x q.val) (S.x g.snd) ∧
      ocorner (S.x i) (S.x q.val) (S.x g.snd) < π := S.corner (S.dartEquiv ⟨i, q⟩)
  have hrot : contactRotateAt S.x (cos S.d) S.hY S.hc i q = r' := by
    refine contactRotateAt_eq_of_empty_sector S.x (cos S.d) S.hY S.hc S.irreducible i q r' ?_ ?_
    · have h := (ocorner_pos_lt_pi_iff _ _ _).mp hcorner
      rw [cross_eq_crossVec] at h
      exact h
    · rintro k hkq - ⟨h1, h2⟩
      rw [← cross_eq_crossVec] at h1 h2
      have hα := (ocorner_pos_lt_pi_iff _ _ _).mpr h1
      have hβ := (ocorner_pos_lt_pi_iff _ _ _).mpr h2
      have hk : S.G.Adj i k.val := (S.contactAdj_iff i k.val).mp ⟨k.2.1.symm, k.2.2⟩
      have hadd := ocorner_add (S.x i) (S.x q.val) (S.x k.val) (S.x g.snd) (S.unit i)
        (S.tdir_ne_zero i q.val hq) (S.tdir_ne_zero i k.val hk) (S.tdir_ne_zero i g.snd hadj)
      rw [(toIcoMod_eq_self two_pi_pos).mpr ⟨by linarith, by linarith⟩] at hadd
      have hne : S.dartEquiv ⟨i, k⟩ ≠ S.dartEquiv ⟨i, q⟩ := by
        intro h
        apply hkq
        have h2 := congrArg (fun e : S.G.Dart => e.snd) h
        exact Subtype.ext h2
      have hang : ocorner (S.x i) (S.x q.val) (S.x g.snd) ≤
          ocorner (S.x i) (S.x q.val) (S.x k.val) :=
        S.angular (S.dartEquiv ⟨i, q⟩) (S.dartEquiv ⟨i, k⟩) rfl hne
      linarith
  show S.dartEquiv ⟨i, contactRotateAt S.x (cos S.d) S.hY S.hc i q⟩ = g
  rw [hrot]
  exact SimpleGraph.Dart.ext _ _ (Prod.ext hg1.symm rfl)

theorem dartEquiv_faceNext (e : ContactDart S.x (cos S.d)) :
    S.dartEquiv (contactFaceNext S.x (cos S.d) S.hY S.hc e) = S.R.face (S.dartEquiv e) := by
  set g := contactFaceNext S.x (cos S.d) S.hY S.hc e with hg
  have h_contactRotate_g : contactRotate S.x (cos S.d) S.hY S.hc g = contactReverse S.x (cos S.d) e := by
    dsimp [g, contactFaceNext]
    simp [Equiv.apply_symm_apply]
  have h_reverse : S.dartEquiv (contactReverse S.x (cos S.d) e) = (S.dartEquiv e).symm := by
    apply SimpleGraph.Dart.ext
    rfl
  have h_eq : S.R.rot (S.dartEquiv g) = (S.dartEquiv e).symm := by
    calc
      S.R.rot (S.dartEquiv g) = S.dartEquiv (contactRotate S.x (cos S.d) S.hY S.hc g) := by
        rw [S.dartEquiv_rotate]
      _ = S.dartEquiv (contactReverse S.x (cos S.d) e) := by rw [h_contactRotate_g]
      _ = (S.dartEquiv e).symm := by rw [h_reverse]
  have h_face : S.R.face (S.dartEquiv e) = S.R.rot.symm ((S.dartEquiv e).symm) := by
    dsimp [RotSys.face]
  rw [h_face]
  apply_fun S.R.rot.symm at h_eq
  simpa [Equiv.symm_apply_apply] using h_eq

theorem strictSupportFace_of_boundary
    (hall : ∀ C : ContactBoundaryCycle S.x (cos S.d) S.hY S.hc, C.StrictSupport) :
    StrictSupportFace S.R S.x := by
  intro f m h_ne h_ne_face
  set p := contactFaceNext S.x (cos S.d) S.hY S.hc with hp
  set e := S.dartEquiv.symm f with he
  obtain ⟨C, hC⟩ := permutation_cycle_enumeration_exists p e
  have h_transport : ∀ k : ℕ, S.dartEquiv (p^[k] e) = (S.R.face ^ k) f := by
    intro k
    induction' k with k ih
    · simp [he]
    · rw [Function.iterate_succ', Function.comp_apply]
      rw [S.dartEquiv_faceNext (e := p^[k] e), ih]
      simp [pow_succ']
  have h_period : ∀ k : ℕ, p^[k] e = C.point (Fin.ofNat (C.size + 1) k) := by
    intro k
    induction' k with k ih
    · rw [Function.iterate_zero]
      simpa [Fin.ofNat] using (hC 0).symm
    · rw [Function.iterate_succ', Function.comp_apply, ih, C.step]
      congr
      apply Fin.ext
      simp [Fin.val_add]
  set j : Fin (C.size + 1) := Fin.ofNat (C.size + 1) m with hj
  -- First, prove C.size > 0, otherwise j = 0 leads to contradiction with h_ne
  have h_size_pos : C.size > 0 := by
    by_contra! h_le
    have h_size0 : C.size = 0 := by omega
    have hj0 : j = (0 : Fin (C.size + 1)) := by
      rw [hj, h_size0]
      ext
      simp
    have h_period_m : p^[m] e = e := by
      rw [h_period m, ← hj, hj0]
      simpa using (hC 0)
    have h_eq : S.dartEquiv (p^[m] e) = f := by
      rw [h_period_m]
      rw [he]
      simp
    have h_eq2 : S.dartEquiv (p^[m] e) = (S.R.face ^ m) f := h_transport m
    rw [h_eq] at h_eq2
    exact h_ne h_eq2.symm
  have hC0 : C.point (0 : Fin (C.size + 1)) = e := by
    simpa using (hC 0)
  have hC1 : C.point (1 : Fin (C.size + 1)) = p e := by
    have h := hC 1
    have h_val : ((1 : Fin (C.size + 1)).val : ℕ) = 1 := by
      simp [h_size_pos]
    rw [h_val] at h
    simpa [← hp] using h
  have h_face_fst : ∀ (d : S.G.Dart), (S.R.face d).fst = d.snd := by
    intro d
    have h_symm_fst : ∀ (d' : S.G.Dart), (d'.symm).fst = d'.snd := by
      intro d'; rfl
    have h_rot_symm_fst : ∀ (d' : S.G.Dart), (S.R.rot.symm d').fst = d'.fst := by
      intro d'
      have h := S.R.rot_fst (S.R.rot.symm d')
      simpa using h.symm
    calc
      (S.R.face d).fst = (S.R.rot.symm (d.symm)).fst := rfl
      _ = (d.symm).fst := h_rot_symm_fst (d.symm)
      _ = d.snd := h_symm_fst d
  have h_vertex0 : (C.point (0 : Fin (C.size + 1))).1 = f.fst := by
    rw [hC0, he]
    rfl
  have h_vertex1 : (C.point (1 : Fin (C.size + 1))).1 = f.snd := by
    rw [hC1]
    have h_dart : S.dartEquiv (p e) = S.R.face f := S.dartEquiv_faceNext (e := e)
    calc
      (p e).1 = (S.dartEquiv (p e)).fst := rfl
      _ = (S.R.face f).fst := by rw [h_dart]
      _ = f.snd := h_face_fst f
  have h_vertex_j : (C.point j).1 = ((S.R.face ^ m) f).fst := by
    rw [hj, ← h_period m]
    have h_dart : S.dartEquiv (p^[m] e) = (S.R.face ^ m) f := h_transport m
    calc
      (p^[m] e).1 = (S.dartEquiv (p^[m] e)).fst := rfl
      _ = ((S.R.face ^ m) f).fst := by rw [h_dart]
  have hj_ne_zero : j ≠ 0 := by
    intro h_eq
    apply h_ne
    have h_period_m : p^[m] e = e := by
      rw [h_period m, ← hj, h_eq]
      exact hC0
    have h1 : S.dartEquiv (p^[m] e) = f := by
      rw [h_period_m]
      rw [he]
      simp
    have h2 : S.dartEquiv (p^[m] e) = (S.R.face ^ m) f := h_transport m
    rw [h1] at h2
    exact h2.symm
  have hj_ne_one : j ≠ 1 := by
    intro h_eq
    apply h_ne_face
    have h_period_m : p^[m] e = p e := by
      rw [h_period m, ← hj, h_eq]
      exact hC1
    have h1 : S.dartEquiv (p^[m] e) = S.R.face f := by
      rw [h_period_m, S.dartEquiv_faceNext (e := e), he]
      simp
    have h2 : S.dartEquiv (p^[m] e) = (S.R.face ^ m) f := h_transport m
    rw [h1] at h2
    exact h2.symm
  have h_strict := hall C 0 j hj_ne_zero (by simpa using hj_ne_one)
  -- h_strict : 0 < inner ℝ (crossVec (S.x ((C.point 0).1)) (S.x ((C.point 1).1))) (S.x ((C.point j).1))
  -- Rewrite using the vertex identities and cross_eq_crossVec
  simpa [ContactBoundaryCycle.vertex, h_vertex0, h_vertex1, h_vertex_j, cross_eq_crossVec] using h_strict

/-- Lemma A.7 in cone form, for vertices `Fin n`. -/
theorem strictSupportFace (h2 : KConnected S.G 2) : StrictSupportFace S.R S.x :=
  S.strictSupportFace_of_boundary fun C =>
    boundary_strictSupport S.x (cos S.d) S.hY S.hc S.bound S.irreducible (S.twoConnected h2) C

end Setup

end Tammes15.FaceChain
