import Tammes15.Hyps.Case
import Tammes15.Draw.Frame
import Tammes15.Fans.Hexagon
import Tammes15.Trigrows.Points

/-!
# Face walks of a realisation

The bridges from the corners of `assignOf` to the angles of the cores (Trigrows, Fans, Glue),
shared by `Tammes15.Trigrows.Realise`, `Tammes15.Fans.Realise` and `Tammes15.Glue.Reconstruct`.

For a dart `e` whose face has `m = fsize P e` darts, the walk vertices are
`fv P e j = ((P.R.face ^ j) e).fst`, read modulo `m`. The corner of `assignOf` at
`(P.R.face ^ j) e` is the counterclockwise corner at `fv P e j` from the side to `fv P e (j + 1)`
to the side to `fv P e (j + m - 1)` (`fc_eq_ocorner`); with the fields of `Realisation` it is the
unoriented angle of the two tangent directions (`fc_eq_angle`). Every other vertex of the walk lies
strictly on the inner side of every side (`support`), hence in the open cone of each corner
(`exists_cone`, Cramer's rule in the tangent plane).
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15.FaceWalk

open scoped Classical

/-! ## Geometry of the tangent plane -/

/-- The oriented area of two tangent directions at a unit `v` is the triple product. -/
theorem inner_cross_tdir (v a b : E3) (hv : ‖v‖ = 1) :
    ⟪v, cross (tdir v a) (tdir v b)⟫ = ⟪cross v a, b⟫ := by
  set s := ⟪v, a⟫ with hs
  set t := ⟪v, b⟫ with ht
  -- vanishing lemmas
  have hvan1 : ⟪v, cross a v⟫ = 0 := by
    rw [cross_anticomm_E3 a v, inner_neg_right, Tammes15.inner_cross_self v a, neg_zero]
  have hvan2 : ⟪v, cross v b⟫ = 0 := by
    rw [Tammes15.inner_cross_self v b]
  have hvan3 : cross v v = 0 := Tammes15.cross_self_eq_zero v
  -- bilinearity helpers
  have hcross_add_left (x y z : E3) : cross (x + y) z = cross x z + cross y z := by
    calc
      cross (x + y) z = -cross z (x + y) := by rw [cross_anticomm_E3]
      _ = -(cross z x + cross z y) := by rw [cross_add_right]
      _ = -cross z x + -cross z y := by rw [neg_add]
      _ = -cross z x - cross z y := by rw [sub_eq_add_neg]
      _ = (-cross z x) - cross z y := rfl
      _ = (-(-cross x z)) - (-cross y z) := by rw [cross_anticomm_E3 z x, cross_anticomm_E3 z y]
      _ = cross x z + cross y z := by simp
  have hcross_sub_right (x y z : E3) : cross x (y - z) = cross x y - cross x z := by
    rw [sub_eq_add_neg, cross_add_right]
    have hneg : cross x (-z) = -cross x z := by
      rw [← neg_one_smul ℝ z, cross_smul_right, neg_one_smul ℝ (cross x z)]
    rw [hneg, sub_eq_add_neg]
  have hcross_sub_left (x y z : E3) : cross (x - y) z = cross x z - cross y z := by
    rw [sub_eq_add_neg, hcross_add_left]
    have hneg : cross (-y) z = -cross y z := by
      rw [← neg_one_smul ℝ y, cross_smul_left, neg_one_smul ℝ (cross y z)]
    rw [hneg, sub_eq_add_neg]
  -- expand cross (a - s•v) (b - t•v) using bilinearity
  have h_expand : cross (a - s • v) (b - t • v) = cross a b - t • cross a v - s • cross v b := by
    calc
      cross (a - s • v) (b - t • v)
          = cross a (b - t • v) - cross (s • v) (b - t • v) := by rw [hcross_sub_left]
      _ = (cross a b - cross a (t • v)) - (s • cross v (b - t • v)) := by
        rw [hcross_sub_right, cross_smul_left]
      _ = (cross a b - t • cross a v) - s • (cross v b - cross v (t • v)) := by
        rw [cross_smul_right, hcross_sub_right]
      _ = (cross a b - t • cross a v) - s • (cross v b - t • cross v v) := by
        rw [cross_smul_right]
      _ = (cross a b - t • cross a v) - s • (cross v b - t • 0) := by rw [hvan3]
      _ = (cross a b - t • cross a v) - s • cross v b := by simp
      _ = cross a b - t • cross a v - s • cross v b := by abel
  unfold tdir
  rw [← hs, ← ht]
  rw [h_expand]
  calc
    ⟪v, cross a b - t • cross a v - s • cross v b⟫
        = ⟪v, cross a b⟫ - ⟪v, t • cross a v⟫ - ⟪v, s • cross v b⟫ := by
      rw [inner_sub_right, inner_sub_right]
    _ = ⟪v, cross a b⟫ - t * ⟪v, cross a v⟫ - s * ⟪v, cross v b⟫ := by
      simp [inner_smul_right]
    _ = ⟪v, cross a b⟫ - t * 0 - s * 0 := by rw [hvan1, hvan2]
    _ = ⟪v, cross a b⟫ := by ring
    _ = ⟪cross v a, b⟫ := by
      calc
        ⟪v, cross a b⟫ = ⟪a, cross b v⟫ := by rw [Tammes15.inner_cross_perm]
        _ = ⟪b, cross v a⟫ := by rw [Tammes15.inner_cross_perm]
        _ = ⟪cross v a, b⟫ := by rw [real_inner_comm]

/-- Cyclic invariance of the triple product. -/
theorem inner_cross_cycle (a b c : E3) : ⟪cross a b, c⟫ = ⟪cross b c, a⟫ := by
  calc
    ⟪cross a b, c⟫ = ⟪c, cross a b⟫ := by rw [real_inner_comm]
    _ = ⟪a, cross b c⟫ := by rw [Tammes15.inner_cross_perm]
    _ = ⟪cross b c, a⟫ := by rw [real_inner_comm]

/-- A nonzero triple product at `v` makes both tangent directions nonzero. -/
theorem tdir_ne_zero_of_inner_cross (v a b : E3) (hv : ‖v‖ = 1) (h : ⟪cross v a, b⟫ ≠ 0) :
    tdir v a ≠ 0 ∧ tdir v b ≠ 0 := by
  have h_inner := Tammes15.FaceWalk.inner_cross_tdir v a b hv
  have h_zero : ⟪v, (0 : E3)⟫ = 0 := by simp
  by_cases h1 : tdir v a = 0
  · have h_cross_zero : cross (tdir v a) (tdir v b) = 0 := by
      simpa [h1, Tammes15.cross]
    rw [h_cross_zero] at h_inner
    rw [h_zero] at h_inner
    exfalso
    exact h h_inner.symm
  · by_cases h2 : tdir v b = 0
    · have h_cross_zero : cross (tdir v a) (tdir v b) = 0 := by
        simpa [h2, Tammes15.cross]
      rw [h_cross_zero] at h_inner
      rw [h_zero] at h_inner
      exfalso
      exact h h_inner.symm
    · exact ⟨h1, h2⟩

/-- A corner at most `π` is the unoriented angle of its tangent directions. -/
theorem ocorner_eq_angle_of_le_pi (v a b : E3) (hv : ‖v‖ = 1) (ha : tdir v a ≠ 0)
    (hb : tdir v b ≠ 0) (h : ocorner v a b ≤ π) :
    ocorner v a b = angle (tdir v a) (tdir v b) := by
  obtain ⟨e, he, hve⟩ := exists_unit_orthogonal v
  set z := tcoord v e a with hz_def
  set w := tcoord v e b with hw_def
  set q := conj z * w with hq_def
  have hz0 : z ≠ 0 := by
    intro h0
    apply ha
    rw [← norm_eq_zero, norm_tdir_eq_norm_tcoord v e a hv he hve, ← hz_def, h0, norm_zero]
  have hw0 : w ≠ 0 := by
    intro h0
    apply hb
    rw [← norm_eq_zero, norm_tdir_eq_norm_tcoord v e b hv he hve, ← hw_def, h0, norm_zero]
  have hq0 : q ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hz0) hw0
  have h_oc : ocorner v a b = toIcoMod two_pi_pos 0 (Complex.arg q) :=
    ocorner_eq_arg v e a b hv he hve
  have h_inner : ⟪tdir v a, tdir v b⟫ = q.re := by
    rw [hq_def, hz_def, hw_def, inner_tdir_frame v e a b hv he hve]
    simp [tcoord, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have h_norm : ‖tdir v a‖ * ‖tdir v b‖ = ‖q‖ := by
    rw [hq_def, norm_mul, Complex.norm_conj, hz_def, hw_def,
      norm_tdir_eq_norm_tcoord v e a hv he hve, norm_tdir_eq_norm_tcoord v e b hv he hve]
  have h_angle : angle (tdir v a) (tdir v b) = arccos (q.re / ‖q‖) := by
    rw [angle, h_inner, h_norm]
  have h_mem := Complex.arg_mem_Ioc q
  have h_nonneg : 0 ≤ Complex.arg q := by
    by_contra hneg0
    have hneg : Complex.arg q < 0 := lt_of_not_ge hneg0
    have h2 : toIcoMod two_pi_pos 0 (Complex.arg q) = Complex.arg q + 2 * π := by
      rw [← toIcoMod_add_right two_pi_pos 0 (Complex.arg q)]
      rw [toIcoMod_eq_self]
      constructor <;> linarith [h_mem.1]
    rw [h_oc, h2] at h
    linarith [h_mem.1]
  have h_self : toIcoMod two_pi_pos 0 (Complex.arg q) = Complex.arg q := by
    rw [toIcoMod_eq_self]
    constructor <;> linarith [h_mem.2, pi_pos]
  rw [h_angle, h_oc, h_self, ← Complex.cos_arg hq0, arccos_cos h_nonneg h_mem.2]

/-- A corner below `π` is the unoriented angle of its tangent directions. -/
theorem ocorner_eq_angle_of_lt_pi (v a b : E3) (hv : ‖v‖ = 1) (ha : tdir v a ≠ 0)
    (hb : tdir v b ≠ 0) (h : ocorner v a b < π) :
    ocorner v a b = angle (tdir v a) (tdir v b) :=
  ocorner_eq_angle_of_le_pi v a b hv ha hb h.le

/-- A corner with `b` on the nonnegative side of the arc `v a` is the unoriented angle of its
tangent directions. -/
theorem ocorner_eq_angle_of_nonneg (v a b : E3) (hv : ‖v‖ = 1) (ha : tdir v a ≠ 0)
    (hb : tdir v b ≠ 0) (h : 0 ≤ ⟪cross v a, b⟫) :
    ocorner v a b = angle (tdir v a) (tdir v b) := by
  refine ocorner_eq_angle_of_le_pi v a b hv ha hb ?_
  set z : ℂ := ⟨⟪tdir v a, tdir v b⟫, ⟪v, cross (tdir v a) (tdir v b)⟫⟩ with hz_def
  have hz_im : 0 ≤ z.im := by
    rw [hz_def]
    change 0 ≤ ⟪v, cross (tdir v a) (tdir v b)⟫
    rw [inner_cross_tdir v a b hv]
    exact h
  have h_arg0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr hz_im
  have h_self : toIcoMod two_pi_pos 0 (Complex.arg z) = Complex.arg z := by
    rw [toIcoMod_eq_self]
    constructor <;> linarith [Complex.arg_le_pi z, pi_pos]
  have h_oc : ocorner v a b = toIcoMod two_pi_pos 0 (Complex.arg z) := rfl
  rw [h_oc, h_self]
  exact Complex.arg_le_pi z

/-- Cramer's rule in the tangent plane at `v`. -/
theorem tdir_eq_cone (v p q w : E3) (hv : ‖v‖ = 1) (hpq : ⟪cross v p, q⟫ ≠ 0) :
    tdir v w = (⟪cross q v, w⟫ / ⟪cross v p, q⟫) • tdir v p +
      (⟪cross v p, w⟫ / ⟪cross v p, q⟫) • tdir v q := by
  have hC : ⟪cross v p, q⟫ • w =
      ⟪cross w p, q⟫ • v + ⟪cross q v, w⟫ • p + ⟪cross v p, w⟫ • q := by
    ext i
    fin_cases i <;>
      simp [cross, PiLp.inner_apply, Fin.sum_univ_three, cross_apply] <;> ring
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hs : ⟪cross v p, q⟫ * ⟪v, w⟫ =
      ⟪cross w p, q⟫ + ⟪cross q v, w⟫ * ⟪v, p⟫ + ⟪cross v p, w⟫ * ⟪v, q⟫ := by
    have h := congrArg (fun z => ⟪v, z⟫) hC
    simp only [inner_add_right, inner_smul_right, hvv, mul_one] at h
    exact h
  have key : ⟪cross v p, q⟫ • tdir v w =
      ⟪cross q v, w⟫ • tdir v p + ⟪cross v p, w⟫ • tdir v q := by
    unfold tdir
    linear_combination (norm := module) hC - hs • v
  calc tdir v w = (⟪cross v p, q⟫)⁻¹ • (⟪cross v p, q⟫ • tdir v w) := by
        rw [smul_smul, inv_mul_cancel₀ hpq, one_smul]
    _ = _ := by
        rw [key, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

/-- A point on the inner side of both arcs of a corner at `v` has its direction in the open cone
of the corner. -/
theorem exists_cone (v p q w : E3) (hv : ‖v‖ = 1) (hpq : 0 < ⟪cross v p, q⟫)
    (hpw : 0 < ⟪cross v p, w⟫) (hqw : 0 < ⟪cross q v, w⟫) :
    ∃ l m : ℝ, 0 < l ∧ 0 < m ∧ tdir v w = l • tdir v p + m • tdir v q := by
  have hpq_ne : ⟪cross v p, q⟫ ≠ 0 := by linarith
  have h := tdir_eq_cone v p q w hv hpq_ne
  refine ⟨⟪cross q v, w⟫ / ⟪cross v p, q⟫, ⟪cross v p, w⟫ / ⟪cross v p, q⟫,
    div_pos hqw hpq, div_pos hpw hpq, ?_⟩
  simpa using h

/-- The direction of such a point splits the angle of the corner. -/
theorem angle_split (v p q w : E3) (hv : ‖v‖ = 1) (hpq : 0 < ⟪cross v p, q⟫)
    (hpw : 0 < ⟪cross v p, w⟫) (hqw : 0 < ⟪cross q v, w⟫) :
    angle (tdir v p) (tdir v w) + angle (tdir v w) (tdir v q) = angle (tdir v p) (tdir v q) := by
  obtain ⟨l, m, hl, hm, hw⟩ := exists_cone v p q w hv hpq hpw hqw
  have htp : tdir v p ≠ 0 := (tdir_ne_zero_of_inner_cross v p q hv (by linarith)).1
  have htq : tdir v q ≠ 0 := (tdir_ne_zero_of_inner_cross v p q hv (by linarith)).2
  have htw : tdir v w ≠ 0 := (tdir_ne_zero_of_inner_cross v p w hv (by linarith)).2
  have hc : l • tdir v p + m • tdir v q ≠ 0 := by
    rw [← hw]
    exact htw
  calc
    angle (tdir v p) (tdir v w) + angle (tdir v w) (tdir v q)
        = angle (tdir v p) (l • tdir v p + m • tdir v q) + angle (l • tdir v p + m • tdir v q) (tdir v q) := by rw [hw]
    _ = angle (tdir v p) (tdir v q) := by
      rw [angle_add_of_cone (tdir v p) (tdir v q) htp htq l m (by linarith) (by linarith) hc]

/-- The alternate triple of a strictly convex hexagon `a₀ … a₅`: if `[a₀ a₂ a₄] ≤ 0`, Cramer's rule
`[a₀ a₁ a₂] a₄ = [a₄ a₁ a₂] a₀ + [a₀ a₄ a₂] a₁ + [a₀ a₁ a₄] a₂` paired with `cross a₃ a₄` gives
`0 > 0` from the supports of the sides `a₀ a₁`, `a₁ a₂`, `a₃ a₄`. -/
theorem hex_triple (a₀ a₁ a₂ a₃ a₄ : E3) (h014 : 0 < ⟪cross a₀ a₁, a₄⟫)
    (h124 : 0 < ⟪cross a₁ a₂, a₄⟫)
    (h340 : 0 < ⟪cross a₃ a₄, a₀⟫) (h341 : 0 < ⟪cross a₃ a₄, a₁⟫)
    (h342 : 0 < ⟪cross a₃ a₄, a₂⟫) : 0 < ⟪cross a₀ a₂, a₄⟫ := by
  have key : ⟪cross a₀ a₂, a₄⟫ * ⟪cross a₃ a₄, a₁⟫ =
      ⟪cross a₁ a₂, a₄⟫ * ⟪cross a₃ a₄, a₀⟫ + ⟪cross a₀ a₁, a₄⟫ * ⟪cross a₃ a₄, a₂⟫ := by
    simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, cross_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, RCLike.inner_apply, conj_trivial]
    ring
  have hpos : 0 < ⟪cross a₀ a₂, a₄⟫ * ⟪cross a₃ a₄, a₁⟫ := by
    rw [key]
    positivity
  exact pos_of_mul_pos_left hpos h341.le

/-- Unit vectors neither equal nor antipodal are at a distance in `(0, π)`. -/
theorem sdist_mem_Ioo (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hne : p ≠ q) (hna : p ≠ -q) :
    0 < sdist p q ∧ sdist p q < π := by
  have hIcc := Tammes15.sdist_mem_Icc p q
  rcases hIcc with ⟨hle0, hleπ⟩
  have hpos : 0 < sdist p q := by
    by_contra! h
    have heq0 : sdist p q = 0 := by linarith
    have hpq : p = q := ((Tammes15.sdist_eq_zero_iff p q hp hq).mp heq0)
    exact hne hpq
  have hltπ : sdist p q < π := by
    by_contra! h
    have heqπ : sdist p q = π := by linarith
    have hneg : sdist p (-q) = 0 := by
      rw [Tammes15.sdist_neg_right p q, heqπ, sub_self]
    have hneg_norm : ‖-q‖ = 1 := by
      rw [norm_neg, hq]
    have hpnegq : p = -q := ((Tammes15.sdist_eq_zero_iff p (-q) hp hneg_norm).mp hneg)
    exact hna hpnegq
  exact And.intro hpos hltπ

/-- `η(g; e, f)` is symmetric in `e, f`. -/
theorem eta_comm (g e f : ℝ) : eta g e f = eta g f e := by
  unfold eta
  rw [mul_comm (cos e), mul_comm (sin e)]

/-- `γ(g; e, f)` is symmetric in `e, f`. -/
theorem gam_comm (g e f : ℝ) : gam g e f = gam g f e := by
  unfold gam eta
  rw [mul_comm (cos e), mul_comm (sin e)]

/-! ## Convex walks

A face of a realisation read as a periodic sequence of points. -/

/-- A convex walk with `m` vertices and sides `d`: unit points of period `m`, sides of length `d`,
each side strictly supporting every other vertex (the cone form of `StrictSupportFace`), and at each
vertex an angle between the two sides in `[α(d), π)`. -/
structure Walk (m : ℕ) (d : ℝ) (X : ℕ → E3) : Prop where
  three : 3 ≤ m
  d_mem : 0 < d ∧ d < π / 2
  unit : ∀ i, ‖X i‖ = 1
  periodic : ∀ i, X (i + m) = X i
  side : ∀ i, sdist (X i) (X (i + 1)) = d
  support : ∀ i n, n % m ≠ 0 → n % m ≠ 1 → 0 < ⟪cross (X i) (X (i + 1)), X (i + n)⟫
  corner : ∀ i, alpha d ≤ angle (tdir (X i) (X (i + 1))) (tdir (X i) (X (i + m - 1))) ∧
    angle (tdir (X i) (X (i + 1))) (tdir (X i) (X (i + m - 1))) < π

/-- The angle of a walk at its vertex `i`, from the side to `i + 1` to the side to `i - 1`. -/
noncomputable def wangle (m : ℕ) (X : ℕ → E3) (i : ℕ) : ℝ :=
  angle (tdir (X i) (X (i + 1))) (tdir (X i) (X (i + m - 1)))

namespace Walk

variable {m : ℕ} {d : ℝ} {X : ℕ → E3}

theorem mod (hW : Walk m d X) (i : ℕ) : X i = X (i % m) := by
  conv_lhs => rw [← Nat.mod_add_div i m]
  induction i / m with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, ← add_assoc, hW.periodic, ih]

/-- A shifted walk is a walk, with the shifted angles. -/
theorem shift (hW : Walk m d X) (j : ℕ) : Walk m d (fun i => X (j + i)) := by
  have hm := hW.three
  refine ⟨hm, hW.d_mem, fun i => hW.unit _, fun i => ?_, fun i => ?_, fun i n h0 h1 => ?_,
    fun i => ?_⟩
  · simp only [← add_assoc, hW.periodic]
  · simp only [← add_assoc]
    exact hW.side _
  · simp only [← add_assoc]
    exact hW.support _ n h0 h1
  · have e1 : j + (i + 1) = j + i + 1 := by omega
    have e2 : j + (i + m - 1) = j + i + m - 1 := by omega
    simp only [e1, e2]
    exact hW.corner (j + i)

theorem wangle_shift (m j i : ℕ) (X : ℕ → E3) (hm : 1 ≤ m) :
    wangle m (fun i => X (j + i)) i = wangle m X (j + i) := by
  unfold wangle
  have e1 : j + (i + 1) = j + i + 1 := by omega
  have e2 : j + (i + m - 1) = j + i + m - 1 := by omega
  simp only [e1, e2]

theorem wangle_add (hW : Walk m d X) (i : ℕ) : wangle m X (i + m) = wangle m X i := by
  have hm := hW.three
  unfold wangle
  rw [hW.periodic, show i + m + 1 = i + 1 + m by omega, hW.periodic,
    show i + m + m - 1 = i + m - 1 + m by omega, hW.periodic]

theorem side_pred (hW : Walk m d X) (i : ℕ) : sdist (X i) (X (i + m - 1)) = d := by
  have hm := hW.three
  have h := hW.side (i + m - 1)
  rw [show i + m - 1 + 1 = i + m by omega, hW.periodic] at h
  rw [sdist_comm]
  exact h

/-- Two vertices with different indices modulo `m` are at a distance in `(0, π)`. -/
theorem sdist_mem (hW : Walk m d X) (i n : ℕ) (h0 : n % m ≠ 0) :
    0 < sdist (X i) (X (i + n)) ∧ sdist (X i) (X (i + n)) < π := by
  have hm := hW.three
  by_cases h1 : n % m = 1
  · have hX : X (i + n) = X (i + 1) := by
      have h1' : n ≡ 1 [MOD m] := by rw [Nat.ModEq, h1, Nat.mod_eq_of_lt (by omega)]
      rw [hW.mod (i + n), hW.mod (i + 1), Nat.ModEq.add_left i h1']
    rw [hX, hW.side]
    exact ⟨hW.d_mem.1, by linarith [hW.d_mem.2, pi_pos]⟩
  · have hs := hW.support i n h0 h1
    have hz : ⟪cross (X i) (X (i + 1)), X i⟫ = 0 := by
      rw [real_inner_comm]
      exact inner_cross_self _ _
    refine sdist_mem_Ioo _ _ (hW.unit _) (hW.unit _) ?_ ?_
    · intro h
      rw [← h, hz] at hs
      exact lt_irrefl _ hs
    · intro h
      have h' : X (i + n) = -X i := by rw [h, neg_neg]
      rw [h', inner_neg_right, hz, neg_zero] at hs
      exact lt_irrefl _ hs

theorem tdir_ne_zero (hW : Walk m d X) (i n : ℕ) (h0 : n % m ≠ 0) : tdir (X i) (X (i + n)) ≠ 0 := by
  intro h
  have hs := hW.sdist_mem i n h0
  have hn := tdir_norm _ _ (hW.unit i) (hW.unit (i + n))
  rw [h, norm_zero] at hn
  exact (sin_pos_of_pos_of_lt_pi hs.1 hs.2).ne hn

/-- The side after the vertex `i - 1` supports every vertex other than `i - 1`, `i`. -/
theorem support_pred (hW : Walk m d X) (i n : ℕ) (h0 : n % m ≠ 0) (h1 : n % m ≠ m - 1) :
    0 < ⟪cross (X (i + m - 1)) (X i), X (i + n)⟫ := by
  have hm := hW.three
  have hr := Nat.mod_lt n (by omega : 0 < m)
  have hn1 : (n + 1) % m = n % m + 1 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt (by omega)]
  have h := hW.support (i + m - 1) (n + 1) (by omega) (by omega)
  rw [show i + m - 1 + 1 = i + m by omega, hW.periodic,
    show i + m - 1 + (n + 1) = i + n + m by omega, hW.periodic] at h
  exact h

/-- The direction of every other vertex lies in the open cone of the corner at `i`. -/
theorem exists_cone (hW : Walk m d X) (i n : ℕ) (h0 : n % m ≠ 0) (h1 : n % m ≠ 1)
    (h2 : n % m ≠ m - 1) :
    ∃ l l' : ℝ, 0 < l ∧ 0 < l' ∧
      tdir (X i) (X (i + n)) = l • tdir (X i) (X (i + 1)) + l' • tdir (X i) (X (i + m - 1)) := by
  have hm := hW.three
  have hq : 0 < ⟪cross (X i) (X (i + 1)), X (i + m - 1)⟫ := by
    have h := hW.support i (m - 1) (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
    rwa [show i + (m - 1) = i + m - 1 by omega] at h
  exact FaceWalk.exists_cone _ _ _ _ (hW.unit i) hq (hW.support i n h0 h1)
    (hW.support_pred i n h0 h2)

/-- ... and splits its angle. -/
theorem angle_split (hW : Walk m d X) (i n : ℕ) (h0 : n % m ≠ 0) (h1 : n % m ≠ 1)
    (h2 : n % m ≠ m - 1) :
    angle (tdir (X i) (X (i + 1))) (tdir (X i) (X (i + n))) +
        angle (tdir (X i) (X (i + n))) (tdir (X i) (X (i + m - 1))) = wangle m X i := by
  have hm := hW.three
  have hq : 0 < ⟪cross (X i) (X (i + 1)), X (i + m - 1)⟫ := by
    have h := hW.support i (m - 1) (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
    rwa [show i + (m - 1) = i + m - 1 by omega] at h
  exact FaceWalk.angle_split _ _ _ _ (hW.unit i) hq (hW.support i n h0 h1)
    (hW.support_pred i n h0 h2)

end Walk

/-! ## The face walk of a realisation -/

/-- The `j`-th vertex of the face walk of `e`. -/
abbrev fv (P : PlaneGraph) (e : P.G.Dart) (j : ℕ) : Fin P.n := ((P.R.face ^ j) e).fst

variable {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ} {x : Pts P k → E3}

theorem face_apply (f : P.G.Dart) : P.R.face f = P.R.rot.symm f.symm := rfl

theorem fst_face (f : P.G.Dart) : (P.R.face f).fst = f.snd := by
  rw [face_apply]
  have h := P.R.rot_fst (P.R.rot.symm f.symm)
  rw [Equiv.apply_symm_apply] at h
  rw [← h]
  rfl

theorem rot_face (f : P.G.Dart) : P.R.rot (P.R.face f) = f.symm := by
  rw [face_apply, Equiv.apply_symm_apply]

theorem face_pow_succ_apply (e : P.G.Dart) (j : ℕ) :
    (P.R.face ^ (j + 1)) e = P.R.face ((P.R.face ^ j) e) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

theorem face_pow_snd (e : P.G.Dart) (j : ℕ) : ((P.R.face ^ j) e).snd = fv P e (j + 1) := by
  rw [fv, face_pow_succ_apply, fst_face]

theorem face_pow_add_apply (e : P.G.Dart) (i j : ℕ) :
    (P.R.face ^ j) ((P.R.face ^ i) e) = (P.R.face ^ (i + j)) e := by
  rw [add_comm, pow_add, Equiv.Perm.mul_apply]

theorem face_pow_fsize (e : P.G.Dart) : (P.R.face ^ fsize P e) e = e := by
  rw [fsize, ← Equiv.Perm.iterate_eq_pow]
  exact Function.iterate_minimalPeriod

theorem face_pow_add_fsize (e : P.G.Dart) (j : ℕ) :
    (P.R.face ^ (j + fsize P e)) e = (P.R.face ^ j) e := by
  rw [add_comm, ← face_pow_add_apply, face_pow_fsize]

theorem fv_add_fsize (e : P.G.Dart) (j : ℕ) : fv P e (j + fsize P e) = fv P e j := by
  rw [fv, face_pow_add_fsize]

theorem face_pow_mod (e : P.G.Dart) (j : ℕ) :
    (P.R.face ^ j) e = (P.R.face ^ (j % fsize P e)) e := by
  conv_lhs => rw [← Nat.mod_add_div j (fsize P e)]
  induction j / fsize P e with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, ← add_assoc, face_pow_add_fsize, ih]

theorem fv_mod (e : P.G.Dart) (j : ℕ) : fv P e j = fv P e (j % fsize P e) := by
  rw [fv, face_pow_mod]

theorem fsize_face_pow (e : P.G.Dart) (i : ℕ) : fsize P ((P.R.face ^ i) e) = fsize P e := by
  rw [fsize, fsize, ← Equiv.Perm.iterate_eq_pow]
  exact Function.minimalPeriod_apply_iterate (P.R.face.injective.mem_periodicPts e) i

theorem fv_face_pow (e : P.G.Dart) (i j : ℕ) : fv P ((P.R.face ^ i) e) j = fv P e (i + j) := by
  rw [fv, fv, face_pow_add_apply]

theorem fc_face_pow (A : Assign P k) (e : P.G.Dart) (i j : ℕ) :
    A.fc ((P.R.face ^ i) e) j = A.fc e (i + j) := by
  rw [Assign.fc, Assign.fc, face_pow_add_apply]

theorem three_le_fsize (hP : InClass P) (e : P.G.Dart) : 3 ≤ fsize P e :=
  (hP.2.2.1 e).1

/-- The far end of the dart after `(P.R.face ^ j) e` in the rotation is the previous walk vertex. -/
theorem rot_face_pow_snd (hP : InClass P) (e : P.G.Dart) (j : ℕ) :
    (P.R.rot ((P.R.face ^ j) e)).snd = fv P e (j + fsize P e - 1) := by
  have hm := three_le_fsize hP e
  have h : (P.R.face ^ j) e = P.R.face ((P.R.face ^ (j + fsize P e - 1)) e) := by
    rw [← face_pow_succ_apply, show j + fsize P e - 1 + 1 = j + fsize P e by omega,
      face_pow_add_fsize]
  rw [h, rot_face]
  rfl

/-- The corners of `assignOf` along a face walk. -/
theorem fc_eq_ocorner (hP : InClass P) (e : P.G.Dart) (j : ℕ) :
    (assignOf P H d x).fc e j = ocorner (x (.inl (fv P e j))) (x (.inl (fv P e (j + 1))))
      (x (.inl (fv P e (j + fsize P e - 1)))) := by
  rw [Assign.fc, ← rot_face_pow_snd hP e j, ← face_pow_snd]
  rfl

theorem sdist_fv_succ (hx : Realisation P H d x) (e : P.G.Dart) (j : ℕ) :
    sdist (x (.inl (fv P e j))) (x (.inl (fv P e (j + 1)))) = d := by
  rw [← face_pow_snd]
  exact hx.edge _ _ ((P.R.face ^ j) e).adj

/-- Strict support of the side `j, j + 1` of a face walk at every other vertex. -/
theorem support (hP : InClass P) (hx : Realisation P H d x) (e : P.G.Dart) (j n : ℕ)
    (h0 : n % fsize P e ≠ 0) (h1 : n % fsize P e ≠ 1) :
    0 < ⟪cross (x (.inl (fv P e j))) (x (.inl (fv P e (j + 1)))), x (.inl (fv P e (j + n)))⟫ := by
  have hm := three_le_fsize hP e
  have hdvd : ∀ c, (P.R.face ^ c) ((P.R.face ^ j) e) = (P.R.face ^ j) e → fsize P e ∣ c := by
    intro c hc
    rw [← fsize_face_pow e j, fsize]
    apply Function.IsPeriodicPt.minimalPeriod_dvd
    show (⇑P.R.face)^[c] _ = _
    rw [Equiv.Perm.iterate_eq_pow]
    exact hc
  have hne0 : (P.R.face ^ n) ((P.R.face ^ j) e) ≠ (P.R.face ^ j) e := fun h =>
    h0 (Nat.mod_eq_zero_of_dvd (hdvd n h))
  have hne1 : (P.R.face ^ n) ((P.R.face ^ j) e) ≠ P.R.face ((P.R.face ^ j) e) := by
    intro h
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h' | h'
      · subst h'
        simp at h0
      · exact h'
    have h' : (P.R.face ^ (n - 1)) ((P.R.face ^ j) e) = (P.R.face ^ j) e := by
      apply P.R.face.injective
      rw [← face_pow_succ_apply, Nat.sub_add_cancel hn]
      exact h
    obtain ⟨c, hc⟩ := hdvd _ h'
    apply h1
    rw [show n = fsize P e * c + 1 by omega, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have h := hx.convex ((P.R.face ^ j) e) n hne0 hne1
  simp only at h
  rw [face_pow_snd, face_pow_add_apply] at h
  exact h

/-- Two walk vertices with different indices modulo the face size are at a distance in
`(0, π)`: they differ and are not antipodal, since either they are the ends of a side, or the
support of the side at the first one is positive at the second. -/
theorem sdist_fv_mem (hP : InClass P) (hx : Realisation P H d x) (e : P.G.Dart) (j n : ℕ)
    (h0 : n % fsize P e ≠ 0) :
    0 < sdist (x (.inl (fv P e j))) (x (.inl (fv P e (j + n)))) ∧
      sdist (x (.inl (fv P e j))) (x (.inl (fv P e (j + n)))) < π := by
  have hm := three_le_fsize hP e
  by_cases h1 : n % fsize P e = 1
  · have hfv : fv P e (j + n) = fv P e (j + 1) := by
      have h1' : n ≡ 1 [MOD fsize P e] := by rw [Nat.ModEq, h1, Nat.mod_eq_of_lt (by omega)]
      rw [fv_mod e (j + n), fv_mod e (j + 1)]
      exact congrArg _ (Nat.ModEq.add_left j h1')
    rw [hfv, sdist_fv_succ hx]
    exact ⟨hx.d_mem.1, by linarith [hx.d_mem.2, pi_pos]⟩
  · have hs := support hP hx e j n h0 h1
    have hz : ⟪cross (x (.inl (fv P e j))) (x (.inl (fv P e (j + 1)))), x (.inl (fv P e j))⟫ =
        0 := by
      rw [real_inner_comm]
      exact inner_cross_self _ _
    refine sdist_mem_Ioo _ _ (hx.unit _) (hx.unit _) ?_ ?_
    · intro h
      rw [← h, hz] at hs
      exact lt_irrefl _ hs
    · intro h
      have h' : x (.inl (fv P e (j + n))) = -x (.inl (fv P e j)) := by rw [h, neg_neg]
      rw [h', inner_neg_right, hz, neg_zero] at hs
      exact lt_irrefl _ hs

theorem tdir_fv_ne_zero (hP : InClass P) (hx : Realisation P H d x) (e : P.G.Dart) (j n : ℕ)
    (h0 : n % fsize P e ≠ 0) : tdir (x (.inl (fv P e j))) (x (.inl (fv P e (j + n)))) ≠ 0 := by
  intro h
  have hs := sdist_fv_mem hP hx e j n h0
  have hn := tdir_norm _ _ (hx.unit (.inl (fv P e j))) (hx.unit (.inl (fv P e (j + n))))
  rw [h, norm_zero] at hn
  exact (sin_pos_of_pos_of_lt_pi hs.1 hs.2).ne hn

theorem fc_mem (hx : Realisation P H d x) (e : P.G.Dart) (j : ℕ) :
    alpha d ≤ (assignOf P H d x).fc e j ∧ (assignOf P H d x).fc e j < π := by
  rw [Assign.fc]
  exact hx.corners _

/-- The corners of a realisation along a face walk are angles of tangent directions. -/
theorem fc_eq_angle (hP : InClass P) (hx : Realisation P H d x) (e : P.G.Dart) (j : ℕ) :
    (assignOf P H d x).fc e j = angle (tdir (x (.inl (fv P e j))) (x (.inl (fv P e (j + 1)))))
      (tdir (x (.inl (fv P e j))) (x (.inl (fv P e (j + fsize P e - 1))))) := by
  have hm := three_le_fsize hP e
  rw [fc_eq_ocorner hP e j]
  apply ocorner_eq_angle_of_lt_pi _ _ _ (hx.unit _)
  · exact tdir_fv_ne_zero hP hx e j 1 (by rw [Nat.mod_eq_of_lt (by omega)]; norm_num)
  · have h := tdir_fv_ne_zero hP hx e j (fsize P e - 1) (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
    rwa [show j + (fsize P e - 1) = j + fsize P e - 1 by omega] at h
  · rw [← fc_eq_ocorner (H := H) (d := d) hP e j]
    exact (fc_mem hx e j).2

theorem sdist_fv_pred (hP : InClass P) (hx : Realisation P H d x) (e : P.G.Dart) (j : ℕ) :
    sdist (x (.inl (fv P e j))) (x (.inl (fv P e (j + fsize P e - 1)))) = d := by
  have hm := three_le_fsize hP e
  have h := sdist_fv_succ hx e (j + fsize P e - 1)
  rw [show j + fsize P e - 1 + 1 = j + fsize P e by omega, fv_add_fsize] at h
  rw [sdist_comm]
  exact h

/-- The face walk of a dart of a realisation is a convex walk. -/
theorem walk_of_realisation (hP : InClass P) (hx : Realisation P H d x) (e : P.G.Dart) :
    Walk (fsize P e) d (fun i => x (.inl (fv P e i))) where
  three := three_le_fsize hP e
  d_mem := hx.d_mem
  unit _ := hx.unit _
  periodic i := by simp only [fv_add_fsize]
  side i := sdist_fv_succ hx e i
  support i n h0 h1 := support hP hx e i n h0 h1
  corner i := by
    rw [← fc_eq_angle hP hx e i]
    exact fc_mem hx e i

/-- The corners of a realisation along a face walk are the angles of the walk. -/
theorem fc_eq_wangle (hP : InClass P) (hx : Realisation P H d x) (e : P.G.Dart) (j : ℕ) :
    (assignOf P H d x).fc e j = wangle (fsize P e) (fun i => x (.inl (fv P e i))) j :=
  fc_eq_angle hP hx e j

end Tammes15.FaceWalk
