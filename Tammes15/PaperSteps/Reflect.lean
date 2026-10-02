import Tammes15.PaperSteps.Defs

/-!
# Step (ii) of the proof of Proposition 7.7: the reflection Θ

The program turns at a vertex in the order opposite to `P.R.rot` and places a free point through
`A_{i-1}` instead of `A_{i+1}`. As the corners at a vertex sum to `2π`, each turn of the program is
`2π` minus the turn of Definition 7.2 (`turn_add_turnR`, `turn_add_corner_add_turnR`), and by the
corner equation of (T8) the same holds for the angle that places a free point. With
`Θ = diag(1, -1, 1)`, `Θ R_z(φ) Θ = R_z(-φ)`, `Θ R_y(θ) Θ = R_y(θ)`, `Θ Z Θ = Z` and `Θ e₃ = e₃`,
so the frames of Definition 7.2 are those of the program conjugated by `Θ` (`frameN_theta`) and
the glued configuration is `Θ` applied to the program's (`glueY_theta`).
-/

open Real Matrix
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15

open scoped Classical

variable {P : PlaneGraph} {k : ℕ}

/-- `Θ = diag(1, -1, 1)`. -/
def thetaM : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- `Θ` as a linear isometry: the reflection in the plane `y = 0`. -/
noncomputable def thetaL : E3 ≃ₗᵢ[ℝ] E3 := Submodule.reflection (ℝ ∙ e2)ᗮ

theorem thetaL_apply (v : E3) : thetaL v = toEuclideanLin thetaM v := by
  have he2_norm : ‖e2‖ = 1 := by simp [e2]
  ext i
  fin_cases i <;> (
    rw [thetaL, Submodule.reflection_apply, Submodule.starProjection_orthogonal,
      _root_.sub_apply, ContinuousLinearMap.id_apply,
      Submodule.starProjection_unit_singleton Real he2_norm v]
    simp [thetaM, Matrix.toEuclideanLin, toLpLin, e2, EuclideanSpace.single, inner, Matrix.vecHead, Matrix.vecTail]
    try ring)

/-- Conjugation of one step of the tree by `Θ`, when the two turns agree modulo `2π` up to sign. -/
theorem theta_stepM (φ ψ θ : ℝ) (h : rotZ (-ψ) = rotZ φ) :
    thetaM * stepM ψ θ * thetaM = stepM φ θ := by
  have hcos : cos ψ = cos φ := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
    simpa [rotZ, Real.cos_neg] using this
  have hsin : sin ψ = -sin φ := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
    simpa [rotZ, Real.cos_neg, Real.sin_neg] using this
  ext i j; fin_cases i <;> fin_cases j <;> simp [thetaM, stepM, rotZ, rotY, flipZ, Matrix.mul_apply, Fin.sum_univ_three, hcos, hsin]

theorem theta_mul_theta : thetaM * thetaM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaM, Matrix.mul_apply] <;>
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide] <;>
    simp

theorem theta_e3 : toEuclideanLin thetaM e3 = e3 := by
  rw [Matrix.toLpLin_apply (p := 2) (q := 2)]
  ext i
  fin_cases i <;> simp [thetaM, e3, Matrix.col]

/-- `Θ R_z(ψ) R_y(θ) e₃ = R_z(φ) R_y(θ) e₃` when `R_z(-ψ) = R_z(φ)`. -/
theorem theta_rotZ_rotY_e3 (φ ψ θ : ℝ) (h : rotZ (-ψ) = rotZ φ) :
    toEuclideanLin (thetaM * (rotZ ψ * rotY θ)) e3 = toEuclideanLin (rotZ φ * rotY θ) e3 := by
  rw [← h]
  ext l
  fin_cases l <;>
    simp [thetaM, rotZ, rotY, e3, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

theorem rotZ_neg_of_add (φ ψ : ℝ) (h : φ + ψ = 2 * π) : rotZ (-ψ) = rotZ φ := by
  have hneg : -ψ = φ - 2 * π := by linarith
  rw [hneg]
  unfold rotZ
  simp [Real.cos_sub_two_pi, Real.sin_sub_two_pi]

/-! ## One vertex: the cycle of `rot` -/

section Cycle

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem rot_pow_fst (R : RotSys G) (a : G.Dart) (t : ℕ) : ((R.rot ^ t) a).fst = a.fst := by
  induction' t with n ih
  · rfl
  · rw [pow_succ', Equiv.Perm.mul_apply, R.rot_fst, ih]

/-- The darts at a vertex are the first `minimalPeriod rot a` iterates of `rot` from any of them. -/
theorem cycle_sum (R : RotSys G) (c : G.Dart → ℝ) (a : G.Dart) :
    ∑ t ∈ Finset.range (Function.minimalPeriod R.rot a), c ((R.rot ^ t) a) =
      ∑ e ∈ Finset.univ.filter (fun e : G.Dart => e.fst = a.fst), c e := by
  have h_fst (t : ℕ) : ((R.rot ^ t) a).fst = a.fst := by
    induction t generalizing a with
    | zero => rfl
    | succ t ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih (R.rot a), R.rot_fst]
  set N := Function.minimalPeriod R.rot a with hN
  have hNpos : 0 < N := by
    have hmem : a ∈ Function.periodicPts R.rot := by
      refine ⟨orderOf R.rot, orderOf_pos _, ?_⟩
      calc
        R.rot^[orderOf R.rot] a = ((R.rot : Equiv.Perm G.Dart) ^ orderOf R.rot) a := by
          rw [← Equiv.Perm.coe_pow]
        _ = (1 : Equiv.Perm G.Dart) a := by rw [pow_orderOf_eq_one]
        _ = a := rfl
    exact Function.minimalPeriod_pos_of_mem_periodicPts hmem
  apply Finset.sum_nbij (fun t => (R.rot ^ t) a) ?_ ?_ ?_ ?_
  · -- map lands in target
    intro t ht
    rw [Finset.mem_range] at ht
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [h_fst]
  · -- injectivity
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_range] at hx hy
    have hx' : x < N := hx
    have hy' : y < N := hy
    -- hxy : (R.rot ^ x) a = (R.rot ^ y) a
    -- Using Equiv.Perm.coe_pow, this gives R.rot^[x] a = R.rot^[y] a
    have hxy_iter : R.rot^[x] a = R.rot^[y] a := by
      simpa [Equiv.Perm.coe_pow] using hxy
    -- Now use Function.iterate_injOn_Iio_minimalPeriod
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := R.rot) (x := a)
    have hx_mem : x ∈ Set.Iio N := hx'
    have hy_mem : y ∈ Set.Iio N := hy'
    exact hinj hx_mem hy_mem hxy_iter
  · -- surjectivity
    intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    rcases he with ⟨_, he_fst⟩
    have hcycle : R.rot.SameCycle a e := R.rot_cycle a e he_fst.symm
    rcases Equiv.Perm.SameCycle.exists_nat_pow_eq hcycle with ⟨i, hi⟩
    -- hi : (R.rot ^ i) a = e
    use i % N
    constructor
    · rw [Finset.mem_coe, Finset.mem_range]
      exact Nat.mod_lt _ hNpos
    · -- (R.rot ^ (i % N)) a = e
      calc
        (R.rot ^ (i % N)) a = R.rot^[i % N] a := by rw [Equiv.Perm.coe_pow]
        _ = R.rot^[i] a := by rw [Function.iterate_mod_minimalPeriod_eq]
        _ = (R.rot ^ i) a := by rw [Equiv.Perm.coe_pow]
        _ = e := hi
  · -- value equality
    intro t ht
    rfl

theorem turnSteps_spec (R : RotSys G) {a b : G.Dart} (hab : a.fst = b.fst) :
    (R.rot ^ turnSteps R a b) a = b ∧ turnSteps R a b < Function.minimalPeriod R.rot a := by
  have h_cycle : R.rot.SameCycle a b := R.rot_cycle a b hab
  have h_exists : ∃ s : ℕ, (R.rot ^ s) a = b := by
    obtain ⟨s, _, hs⟩ := h_cycle.exists_pow_eq'
    exact ⟨s, hs⟩
  have h_turn_eq : turnSteps R a b = Nat.find h_exists := by
    dsimp [turnSteps]
    rw [dite_eq_left h_exists]
  have h_first : (R.rot ^ turnSteps R a b) a = b := by
    rw [h_turn_eq]
    exact Nat.find_spec h_exists
  set s := Nat.find h_exists with hs_def
  have hs_spec : (R.rot ^ s) a = b := by
    rw [hs_def]
    exact Nat.find_spec h_exists
  have h_second : turnSteps R a b < Function.minimalPeriod (R.rot : G.Dart → G.Dart) a := by
    rw [h_turn_eq, hs_def]
    have h_periodic : a ∈ Function.periodicPts (R.rot : G.Dart → G.Dart) :=
      Function.Injective.mem_periodicPts R.rot.injective a
    have h_pos : 0 < Function.minimalPeriod (R.rot : G.Dart → G.Dart) a :=
      Function.minimalPeriod_pos_of_mem_periodicPts h_periodic
    have h_mod : (R.rot ^ (s % Function.minimalPeriod (R.rot : G.Dart → G.Dart) a)) a = b := by
      calc
        (R.rot ^ (s % Function.minimalPeriod (R.rot : G.Dart → G.Dart) a)) a =
            ((R.rot : G.Dart → G.Dart)^[s % Function.minimalPeriod (R.rot : G.Dart → G.Dart) a]) a := by
          simp [Equiv.Perm.coe_pow]
        _ = ((R.rot : G.Dart → G.Dart)^[s]) a := by
          rw [Function.iterate_mod_minimalPeriod_eq]
        _ = (R.rot ^ s) a := by simp [Equiv.Perm.coe_pow]
        _ = b := hs_spec
    have h_le : s ≤ s % Function.minimalPeriod (R.rot : G.Dart → G.Dart) a :=
      Nat.find_min' h_exists h_mod
    have h_mod_lt : s % Function.minimalPeriod (R.rot : G.Dart → G.Dart) a <
        Function.minimalPeriod (R.rot : G.Dart → G.Dart) a :=
      Nat.mod_lt _ h_pos
    exact lt_of_le_of_lt h_le h_mod_lt
  exact And.intro h_first h_second

theorem turnSteps_self (R : RotSys G) (a : G.Dart) : turnSteps R a a = 0 := by
  unfold turnSteps; simp

theorem turnStepsR_self (R : RotSys G) (a : G.Dart) : turnStepsR R a a = 0 := by
  unfold turnStepsR
  have h0 : (R.rot.symm ^ 0) a = a := by simp
  have h_exists : ∃ s, (R.rot.symm ^ s) a = a := ⟨0, h0⟩
  rw [dite_eq_left h_exists]
  apply (Nat.find_eq_zero h_exists).mpr
  exact h0

theorem rot_symm_pow (R : RotSys G) (a : G.Dart) {j : ℕ}
    (hj : j ≤ Function.minimalPeriod R.rot a) :
    (R.rot.symm ^ j) a = (R.rot ^ (Function.minimalPeriod R.rot a - j)) a := by
  set N := Function.minimalPeriod R.rot a with hN_def
  have hN : (R.rot ^ N) a = a := by
    rw [Equiv.Perm.coe_pow]
    exact Function.iterate_minimalPeriod
  have h_add : j + (N - j) = N := Nat.add_sub_cancel' hj
  have h_symm_eq_inv : R.rot.symm = R.rot⁻¹ := by
    rw [Equiv.Perm.inv_def]
  have h_inv_pow : R.rot.symm ^ j = (R.rot ^ j)⁻¹ := by
    rw [h_symm_eq_inv, inv_pow]
  have h_cancel (x : G.Dart) : (R.rot.symm ^ j) ((R.rot ^ j) x) = x := by
    rw [h_inv_pow]
    exact Equiv.symm_apply_apply (R.rot ^ j) x
  calc
    (R.rot.symm ^ j) a = (R.rot.symm ^ j) ((R.rot ^ N) a) := by rw [hN]
    _ = (R.rot.symm ^ j) ((R.rot ^ (j + (N - j))) a) := by rw [h_add]
    _ = (R.rot.symm ^ j) (((R.rot ^ j) * (R.rot ^ (N - j))) a) := by rw [pow_add]
    _ = (R.rot.symm ^ j) ((R.rot ^ j) ((R.rot ^ (N - j)) a)) := by rw [Equiv.Perm.mul_apply]
    _ = (R.rot ^ (N - j)) a := by rw [h_cancel]

theorem turnStepsR_eq (R : RotSys G) {a b : G.Dart} (hab : a.fst = b.fst) (hne : a ≠ b) :
    turnStepsR R a b = Function.minimalPeriod R.rot a - turnSteps R a b := by
  set N := Function.minimalPeriod R.rot a with hN
  set s := turnSteps R a b with hs
  set t := turnStepsR R a b with ht
  -- a and b are in the same cycle under R.rot
  have hcycle : R.rot.SameCycle a b := R.rot_cycle a b hab
  -- There exists i such that (R.rot ^ i) a = b
  have h_exists : ∃ i, (R.rot ^ i) a = b :=
    Equiv.Perm.SameCycle.exists_nat_pow_eq hcycle
  -- So s is defined by Nat.find
  have hs_def : s = Nat.find h_exists := by
    rw [hs, turnSteps, dif_pos h_exists]
  -- Property of s: (R.rot ^ s) a = b
  have hs_spec : (R.rot ^ s) a = b := by
    rw [hs_def]
    exact Nat.find_spec h_exists
  -- s is minimal: for any i with (R.rot ^ i) a = b, we have s ≤ i
  have hs_min : ∀ i, (R.rot ^ i) a = b → s ≤ i := by
    intro i hi
    rw [hs_def]
    exact Nat.find_min' h_exists hi
  -- N is the minimal period: (R.rot ^ N) a = a
  have hN_spec : (R.rot ^ N) a = a := by
    have h := Function.iterate_minimalPeriod (f := (R.rot : G.Dart → G.Dart)) (x := a)
    rw [Equiv.Perm.iterate_eq_pow R.rot N] at h
    exact h
  -- N > 0 since a is periodic (same cycle as b, a ≠ b)
  have hN_pos : 0 < N := by
    have hcycle_self : R.rot.SameCycle a a := Equiv.Perm.SameCycle.refl _ _
    obtain ⟨k, hk_pos, hk_le, hk⟩ := Equiv.Perm.SameCycle.exists_pow_eq'' hcycle_self
    have h_periodic : Function.IsPeriodicPt R.rot k a := by
      rw [Function.IsPeriodicPt, Equiv.Perm.iterate_eq_pow R.rot k]
      exact hk
    have h_dvd : N ∣ k := Function.IsPeriodicPt.minimalPeriod_dvd h_periodic
    by_contra! hN0
    have hN0' : N = 0 := by omega
    rw [hN0'] at h_dvd
    rcases h_dvd with ⟨m, hm⟩
    have hk0 : k = 0 := by omega
    omega
  -- s > 0 since a ≠ b
  have hs_pos : 0 < s := by
    by_contra! h
    have hs0 : s = 0 := by omega
    rw [hs0, pow_zero] at hs_spec
    -- hs_spec : (1 : Equiv.Perm G.Dart) a = b, which simplifies to a = b
    have h_ab : a = b := by simpa using hs_spec
    exact hne h_ab
  -- Show s < N using the division algorithm
  have hs_lt_N : s < N := by
    set r := s % N with hr
    set q := s / N with hq
    have h_divmod : s = r + N * q := by
      rw [hr, hq, Nat.mod_add_div s N]
    -- (R.rot ^ (N * q)) a = a because (R.rot ^ N) a = a
    have h_mul : (R.rot ^ (N * q)) a = a := by
      rw [pow_mul]
      induction' q with m ih
      · simp
      · rw [pow_succ, Equiv.Perm.mul_apply, hN_spec, ih]
    -- Now (R.rot ^ s) a = (R.rot ^ (r + N * q)) a = (R.rot ^ r) ((R.rot ^ (N * q)) a) = (R.rot ^ r) a
    have h_mod : (R.rot ^ r) a = b := by
      calc
        (R.rot ^ r) a = (R.rot ^ r) ((R.rot ^ (N * q)) a) := by rw [h_mul]
        _ = ((R.rot ^ r) * (R.rot ^ (N * q))) a := by rw [Equiv.Perm.mul_apply]
        _ = (R.rot ^ (r + N * q)) a := by rw [← pow_add]
        _ = (R.rot ^ s) a := by rw [h_divmod]
        _ = b := hs_spec
    -- If s ≥ N, then r < s, contradicting the minimality of s
    by_contra! hge
    -- hge : N ≤ s
    have hr_lt_s : r < s := by
      rw [hr]
      have h_lt_N : s % N < N := Nat.mod_lt s hN_pos
      omega
    have h_le := hs_min r h_mod
    omega
  -- Now we have s < N, so s ≤ N
  have hs_le_N : s ≤ N := Nat.le_of_lt hs_lt_N
  -- There also exists i such that (R.rot.symm ^ i) a = b
  have hcycle_symm : Equiv.Perm.SameCycle (R.rot.symm : Equiv.Perm G.Dart) a b :=
    Equiv.Perm.SameCycle.inv hcycle
  have h_existsR : ∃ i, ((R.rot.symm : Equiv.Perm G.Dart) ^ i) a = b :=
    Equiv.Perm.SameCycle.exists_nat_pow_eq hcycle_symm
  have ht_def : t = Nat.find h_existsR := by
    rw [ht, turnStepsR, dif_pos h_existsR]
  -- Show that (R.rot.symm ^ (N - s)) a = b
  have hR_spec : ((R.rot.symm : Equiv.Perm G.Dart) ^ (N - s)) a = b := by
    -- (R.rot.symm : Equiv.Perm G.Dart) = R.rot⁻¹
    rw [← Equiv.Perm.inv_def]
    -- Now we have (R.rot⁻¹ ^ (N - s)) a = b
    -- (R.rot⁻¹ ^ (N - s)) = (R.rot ^ (N - s))⁻¹ by inv_pow
    rw [inv_pow (a := R.rot) (n := N - s)]
    -- Now we have (R.rot ^ (N - s))⁻¹ a
    -- = (R.rot ^ (N - s))⁻¹ ((R.rot ^ N) a) since (R.rot ^ N) a = a
    rw [← hN_spec]
    -- pow_sub R.rot hs_le_N : R.rot ^ (N - s) = R.rot ^ N * (R.rot ^ s)⁻¹
    have h_pow_sub : R.rot ^ (N - s) = R.rot ^ N * (R.rot ^ s)⁻¹ := by
      rw [pow_sub R.rot hs_le_N]
    -- Take inverses of both sides
    have h_inv : (R.rot ^ (N - s))⁻¹ = (R.rot ^ s) * (R.rot ^ N)⁻¹ := by
      calc
        (R.rot ^ (N - s))⁻¹ = (R.rot ^ N * (R.rot ^ s)⁻¹)⁻¹ := by rw [h_pow_sub]
        _ = ((R.rot ^ s)⁻¹)⁻¹ * (R.rot ^ N)⁻¹ := by rw [_root_.mul_inv_rev]
        _ = R.rot ^ s * (R.rot ^ N)⁻¹ := by simp
    rw [h_inv]
    -- Now (R.rot ^ s) * (R.rot ^ N)⁻¹ applied to a
    -- = (R.rot ^ s) ((R.rot ^ N)⁻¹ a)
    -- = (R.rot ^ s) a since (R.rot ^ N)⁻¹ a = a
    have hN_inv : (R.rot ^ N)⁻¹ ((R.rot ^ N) a) = a :=
      Equiv.symm_apply_apply (R.rot ^ N) a
    -- Now rewrite the target using this
    -- Target: (R.rot ^ s * (R.rot ^ N)⁻¹) ((R.rot ^ N) a) = b
    -- = (R.rot ^ s) ((R.rot ^ N)⁻¹ ((R.rot ^ N) a)) = b
    -- = (R.rot ^ s) a = b
    calc
      (R.rot ^ s * (R.rot ^ N)⁻¹) ((R.rot ^ N) a) = (R.rot ^ s) ((R.rot ^ N)⁻¹ ((R.rot ^ N) a)) := by rfl
      _ = (R.rot ^ s) a := by rw [hN_inv]
      _ = b := hs_spec
  -- Now t ≤ N - s by minimality of Nat.find
  have ht_le : t ≤ N - s := by
    rw [ht_def]
    exact Nat.find_min' h_existsR hR_spec
  -- Show that for any j < N - s, (R.rot.symm ^ j) a ≠ b
  have hR_min : ∀ j, j < N - s → ((R.rot.symm : Equiv.Perm G.Dart) ^ j) a ≠ b := by
    intro j hj
    intro h_eq
    rw [← Equiv.Perm.inv_def] at h_eq
    -- Apply R.rot ^ j to both sides: a = (R.rot ^ j) b = (R.rot ^ (s + j)) a
    have h_per : (R.rot ^ (s + j)) a = a := by
      calc
        (R.rot ^ (s + j)) a = (R.rot ^ (j + s)) a := by rw [add_comm]
        _ = (R.rot ^ j * R.rot ^ s) a := by rw [pow_add]
        _ = (R.rot ^ j) ((R.rot ^ s) a) := by rw [Equiv.Perm.mul_apply]
        _ = (R.rot ^ j) b := by rw [hs_spec]
        _ = (R.rot ^ j) ((R.rot⁻¹ ^ j) a) := by rw [h_eq]
        _ = ((R.rot ^ j) * (R.rot⁻¹ ^ j)) a := rfl
        _ = ((R.rot ^ j) * (R.rot ^ j)⁻¹) a := by rw [← inv_pow, Equiv.Perm.inv_def]
        _ = a := by simp
    -- So Function.IsPeriodicPt R.rot (s + j) a
    have h_periodic : Function.IsPeriodicPt R.rot (s + j) a := by
      rw [Function.IsPeriodicPt, Equiv.Perm.iterate_eq_pow R.rot (s + j)]
      exact h_per
    -- By minimimalPeriod_dvd, N ∣ s + j
    have h_dvd : N ∣ s + j :=
      Function.IsPeriodicPt.minimalPeriod_dvd h_periodic
    -- But 0 < s + j < N (since s > 0 and j < N - s)
    have h_sum_lt_N : s + j < N := by
      omega
    have h_sum_pos : 0 < s + j := by omega
    -- N divides a positive number less than N, impossible
    have h_le := Nat.le_of_dvd h_sum_pos h_dvd
    omega
  -- Now t = N - s by Nat.find_eq_iff
  rw [ht_def, Nat.find_eq_iff h_existsR]
  constructor
  · exact hR_spec
  · intro j hj
    exact hR_min j hj

/-- The corners passed by `rot⁻¹` from `a` to `b ≠ a` are those of the darts `rot^t a` with
`turnSteps a b ≤ t < minimalPeriod rot a`. -/
theorem sum_turnR_eq (R : RotSys G) (c : G.Dart → ℝ) {a b : G.Dart} (hab : a.fst = b.fst)
    (hne : a ≠ b) :
    ∑ t ∈ Finset.range (turnStepsR R a b), c ((R.rot.symm ^ (t + 1)) a) =
      ∑ t ∈ Finset.Ico (turnSteps R a b) (Function.minimalPeriod R.rot a), c ((R.rot ^ t) a) := by
  set N := Function.minimalPeriod R.rot a
  set s := turnSteps R a b
  set r := turnStepsR R a b
  have hspec := turnSteps_spec R hab
  rcases hspec with ⟨h_eq, h_lt⟩
  have hr_eq := turnStepsR_eq R hab hne
  have h_r_eq : r = N - s := hr_eq
  have hs_le_N : s ≤ N := by omega
  rw [h_r_eq]
  calc
    ∑ t ∈ Finset.range (N - s), c ((R.rot.symm ^ (t + 1)) a)
        = ∑ t ∈ Finset.range (N - s), c ((R.rot ^ (N - (t + 1))) a) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht_range : t < N - s := Finset.mem_range.1 ht
      have h_le : t + 1 ≤ N := by omega
      rw [rot_symm_pow R a h_le]
    _ = ∑ t ∈ Finset.range (N - s), c ((R.rot ^ (N - 1 - t)) a) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht_range : t < N - s := Finset.mem_range.1 ht
      have h_exp_eq : N - (t + 1) = N - 1 - t := by omega
      rw [h_exp_eq]
    _ = ∑ t ∈ Finset.range (N - s), c ((R.rot ^ (s + (N - s - 1 - t))) a) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht_range : t < N - s := Finset.mem_range.1 ht
      have h1 : 1 ≤ N - s := by omega
      have h2 : t ≤ (N - s) - 1 := by omega
      have h_exp_eq : N - 1 - t = s + (N - s - 1 - t) := by
        calc
          N - 1 - t = ((s + (N - s)) - 1) - t := by rw [Nat.add_sub_cancel' hs_le_N]
          _ = (s + ((N - s) - 1)) - t := by rw [Nat.add_sub_assoc h1]
          _ = s + (((N - s) - 1) - t) := by rw [Nat.add_sub_assoc h2]
          _ = s + (N - s - 1 - t) := rfl
      rw [h_exp_eq]
    _ = ∑ t ∈ Finset.range (N - s), c ((R.rot ^ (s + t)) a) := by
      rw [Finset.sum_range_reflect (f := fun x => c ((R.rot ^ (s + x)) a)) (n := N - s)]
    _ = ∑ t ∈ Finset.Ico s N, c ((R.rot ^ t) a) := by
      rw [Finset.sum_Ico_eq_sum_range]

theorem turnSteps_rot (R : RotSys G) {a e : G.Dart} (hae : a.fst = e.fst) (hne : R.rot e ≠ a) :
    turnSteps R a (R.rot e) = turnSteps R a e + 1 := by
  set s := turnSteps R a e with hs
  have hspec := turnSteps_spec R hae
  rcases hspec with ⟨h_eq, h_lt⟩
  have h_eq' : (R.rot ^ s) a = e := by
    rw [← hs] at h_eq
    exact h_eq
  have h_pow_succ : (R.rot ^ (s + 1)) a = R.rot e := by
    calc
      (R.rot ^ (s + 1)) a = (R.rot * (R.rot ^ s)) a := by rw [pow_succ']
      _ = R.rot ((R.rot ^ s) a) := rfl
      _ = R.rot e := by rw [h_eq']
  have h_ex_re : ∃ m, (R.rot ^ m) a = R.rot e := ⟨s + 1, h_pow_succ⟩
  rw [turnSteps]
  rw [dite_eq_left h_ex_re]
  rw [Nat.find_eq_iff h_ex_re]
  constructor
  · exact h_pow_succ
  · intro n hn
    rcases Nat.eq_zero_or_pos n with (rfl | hpos)
    · intro hzero
      have : a = R.rot e := by simpa using hzero
      exact hne this.symm
    · have ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hpos
      rcases hm with rfl
      have hm_lt_s : m < s := by omega
      intro h_eq2
      have h_eq_m : (R.rot ^ m) a = e := by
        have : (R.rot ^ (m + 1)) a = R.rot ((R.rot ^ m) a) := by
          calc
            (R.rot ^ (m + 1)) a = (R.rot * (R.rot ^ m)) a := by rw [pow_succ']
            _ = R.rot ((R.rot ^ m) a) := rfl
        rw [this] at h_eq2
        exact R.rot.injective h_eq2
      have h_cycle : R.rot.SameCycle a e := R.rot_cycle a e hae
      have h_ex_e : ∃ t, (R.rot ^ t) a = e := h_cycle.exists_nat_pow_eq
      have h_turn_eq : turnSteps R a e = Nat.find h_ex_e := by
        rw [turnSteps, dite_eq_left h_ex_e]
      have hm_lt_find : m < Nat.find h_ex_e := by
        rw [← h_turn_eq]
        exact hm_lt_s
      have h_min := Nat.find_min h_ex_e hm_lt_find
      exact h_min h_eq_m

theorem turnSteps_rot_eq (R : RotSys G) {a e : G.Dart} (hae : a.fst = e.fst) (h : R.rot e = a) :
    turnSteps R a e + 1 = Function.minimalPeriod R.rot a := by
  set s := turnSteps R a e with hs
  set N := Function.minimalPeriod R.rot a with hN
  have hspec := turnSteps_spec R hae
  rcases hspec with ⟨h_eq, h_lt⟩
  have h_periodic : Function.IsPeriodicPt R.rot (s + 1) a := by
    rw [Function.IsPeriodicPt, ← Equiv.Perm.coe_pow]
    calc
      (R.rot ^ (s + 1)) a = (R.rot * (R.rot ^ s)) a := by
        rw [pow_succ']
      _ = R.rot ((R.rot ^ s) a) := rfl
      _ = R.rot e := by rw [h_eq]
      _ = a := h
  have h_dvd : N ∣ s + 1 :=
    Function.IsPeriodicPt.minimalPeriod_dvd h_periodic
  have h_pos : 0 < s + 1 := by omega
  have h_le : N ≤ s + 1 := Nat.le_of_dvd h_pos h_dvd
  omega

end Cycle

/-- The corners passed by `rot` from `a` and by `rot⁻¹` from `a` to the same dart make up the
whole vertex: the two turns sum to `2π`, or both vanish when the darts agree. -/
theorem turn_add_turnR {A : Assign P k} (hsum : ∀ v, ∑ e ∈ Finset.univ.filter
      (fun e : P.G.Dart => e.fst = v), A.corner e = 2 * π)
    {a b : P.G.Dart} (hab : a.fst = b.fst) :
    (a = b ∧ A.turn a b = 0 ∧ turnR A a b = 0) ∨ A.turn a b + turnR A a b = 2 * π := by
  by_cases h : a = b
  · subst h
    left
    refine ⟨rfl, ?_, ?_⟩
    · rw [Assign.turn, turnSteps_self, Finset.sum_range_zero]
    · rw [turnR, turnStepsR_self, Finset.sum_range_zero]
  · right
    have hv := hsum a.fst
    rw [← cycle_sum P.R A.corner a] at hv
    obtain ⟨-, hsN⟩ := turnSteps_spec P.R hab
    rw [Assign.turn, turnR, sum_turnR_eq P.R A.corner hab h,
      Finset.sum_range_add_sum_Ico _ hsN.le, hv]

/-- The turns of the two gluings at a vertex give the same rotation about the third axis, up to
the sign of the angle. -/
theorem rotZ_turnR {A : Assign P k} (hsum : ∀ v, ∑ e ∈ Finset.univ.filter
      (fun e : P.G.Dart => e.fst = v), A.corner e = 2 * π)
    {a b : P.G.Dart} (hab : a.fst = b.fst) : rotZ (-(turnR A a b)) = rotZ (A.turn a b) := by
  have hturn := turn_add_turnR hsum hab
  rcases hturn with (⟨heq, hturn0, hturnR0⟩ | hsum')
  · subst heq
    simp [hturn0, hturnR0]
  · have h := rotZ_neg_of_add (A.turn a b) (turnR A a b) hsum'
    exact h

/-- The turn by `rot` from `a` to `e`, the corner of `e` and the turn by `rot⁻¹` from `a` to `rot e`
make up the whole vertex. -/
theorem turn_add_corner_add_turnR {A : Assign P k} (hsum : ∀ v, ∑ e ∈ Finset.univ.filter
      (fun e : P.G.Dart => e.fst = v), A.corner e = 2 * π)
    {a e : P.G.Dart} (hae : a.fst = e.fst) :
    A.turn a e + A.corner e + turnR A a (P.R.rot e) = 2 * π := by
  have hv := hsum a.fst
  rw [← cycle_sum P.R A.corner a] at hv
  obtain ⟨hs, hsN⟩ := turnSteps_spec P.R hae
  have hturn : A.turn a e + A.corner e =
      ∑ t ∈ Finset.range (turnSteps P.R a e + 1), A.corner ((P.R.rot ^ t) a) := by
    rw [Finset.sum_range_succ, hs]
    rfl
  by_cases h : P.R.rot e = a
  · rw [hturn, turnSteps_rot_eq P.R hae h, h, turnR, turnStepsR_self, Finset.sum_range_zero,
      add_zero, hv]
  · have hae' : a.fst = (P.R.rot e).fst := by rw [P.R.rot_fst, hae]
    have hR : turnR A a (P.R.rot e) = ∑ t ∈ Finset.Ico (turnSteps P.R a e + 1)
        (Function.minimalPeriod P.R.rot a), A.corner ((P.R.rot ^ t) a) := by
      rw [turnR, sum_turnR_eq P.R A.corner hae' (Ne.symm h), turnSteps_rot P.R hae h]
    rw [hturn, hR, Finset.sum_range_add_sum_Ico _ (by omega), hv]

/-- The dart after `face e` in the rotation is the reverse of `e`. -/
theorem rot_face_eq_symm {P : PlaneGraph} (x : P.G.Dart) : P.R.rot (P.R.face x) = x.symm := by
  have hface : P.R.face = (Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive).trans P.R.rot.symm := rfl
  calc
    P.R.rot (P.R.face x) = P.R.rot (((Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive).trans P.R.rot.symm) x) := rfl
    _ = P.R.rot (P.R.rot.symm (x.symm)) := by
      simp [Function.Involutive.toPerm, Equiv.trans_apply]
    _ = x.symm := by simp

/-- In a face, the dart after `e_i = face^i b` in the rotation is the reverse of `e_{i-1}`. -/
theorem rot_face_pow {b : P.G.Dart} (hb : Function.minimalPeriod P.R.face b = 6) (i : Fin 6) :
    P.R.rot ((P.R.face ^ (i : ℕ)) b) = ((P.R.face ^ ((i - 1 : Fin 6) : ℕ)) b).symm := by
  by_cases hi : i = 0
  · -- case i = 0
    subst hi
    have h_period : (P.R.face ^ (6 : ℕ)) b = b := by
      have h := Function.iterate_minimalPeriod (f := P.R.face) (x := b)
      rw [hb] at h
      -- h : (P.R.face)^[6] b = b
      -- Convert to monoid power using Equiv.Perm.iterate_eq_pow
      have h' := congrArg (fun (g : P.G.Dart → P.G.Dart) => g b) (Equiv.Perm.iterate_eq_pow (P.R.face) 6)
      -- h' : (P.R.face)^[6] b = (P.R.face ^ 6) b
      rw [h'] at h
      exact h
    have h_pow_succ : (P.R.face ^ (6 : ℕ)) = P.R.face * (P.R.face ^ (5 : ℕ)) := by
      simpa using congrArg (fun (f : Equiv.Perm _) => f) (pow_succ' (P.R.face) (5 : ℕ))
    calc
      P.R.rot b = P.R.rot ((P.R.face ^ (6 : ℕ)) b) := by rw [h_period]
      _ = P.R.rot ((P.R.face * (P.R.face ^ (5 : ℕ))) b) := by rw [h_pow_succ]
      _ = P.R.rot (P.R.face ((P.R.face ^ (5 : ℕ)) b)) := rfl
      _ = ((P.R.face ^ (5 : ℕ)) b).symm := by rw [rot_face_eq_symm]
  · -- case i ≠ 0
    have h_eq : (i : ℕ) = ((i - 1 : Fin 6) : ℕ) + 1 := by
      fin_cases i <;> simp at hi <;> simp
    have h_pow_succ : (P.R.face ^ (((i - 1 : Fin 6) : ℕ) + 1)) = P.R.face * (P.R.face ^ ((i - 1 : Fin 6) : ℕ)) := by
      simpa using congrArg (fun (f : Equiv.Perm _) => f) (pow_succ' (P.R.face) ((i - 1 : Fin 6) : ℕ))
    calc
      P.R.rot ((P.R.face ^ (i : ℕ)) b) = P.R.rot ((P.R.face ^ (((i - 1 : Fin 6) : ℕ) + 1)) b) := by rw [h_eq]
      _ = P.R.rot ((P.R.face * (P.R.face ^ ((i - 1 : Fin 6) : ℕ))) b) := by rw [h_pow_succ]
      _ = P.R.rot (P.R.face ((P.R.face ^ ((i - 1 : Fin 6) : ℕ)) b)) := rfl
      _ = ((P.R.face ^ ((i - 1 : Fin 6) : ℕ)) b).symm := by rw [rot_face_eq_symm]

/-- The reference dart of a vertex starts at it. -/
theorem refD_fst {g : GlueData P k} (hg : g.Valid) (v : Fin P.n) : (g.refD v).fst = v := by
  by_cases h : v = g.root
  · subst h
    simp [GlueData.refD, hg.root_fst]
  · simp [GlueData.refD, h, hg.par_snd v h]

/-- The frames of Definition 7.2 are those of the program conjugated by `Θ`. -/
theorem frameN_theta {A : Assign P k} (hsum : ∀ v, ∑ e ∈ Finset.univ.filter
      (fun e : P.G.Dart => e.fst = v), A.corner e = 2 * π)
    {g : GlueData P k} (hg : g.Valid) (n : ℕ) (v : Fin P.n) :
    thetaM * progFrameN g A n v * thetaM = g.frameN A n v := by
  induction n generalizing v with
  | zero =>
      simp [progFrameN, GlueData.frameN, theta_mul_theta]
  | succ n ih =>
      by_cases hv : v = g.root
      · subst hv
        simp [progFrameN, GlueData.frameN, theta_mul_theta]
      · set w := (g.par v).fst with hw_def
        have h_refD_fst : (g.refD w).fst = w := refD_fst hg w
        have h_par_fst : (g.par v).fst = w := hw_def
        have h_turn_eq : rotZ (-(turnR A (g.refD w) (g.par v))) = rotZ (A.turn (g.refD w) (g.par v)) :=
          rotZ_turnR hsum (by rw [h_refD_fst, h_par_fst])
        have h_step_eq : thetaM * stepM (turnR A (g.refD w) (g.par v)) A.d * thetaM =
            stepM (A.turn (g.refD w) (g.par v)) A.d :=
          theta_stepM (A.turn (g.refD w) (g.par v)) (turnR A (g.refD w) (g.par v)) A.d h_turn_eq
        have h_ih := ih w
        have h_prog : progFrameN g A (n + 1) v =
            progFrameN g A n w * stepM (turnR A (g.refD w) (g.par v)) A.d := by
          rw [progFrameN, hw_def]
          simp [hv]
        have h_frame : g.frameN A (n + 1) v =
            g.frameN A n w * stepM (A.turn (g.refD w) (g.par v)) A.d := by
          rw [GlueData.frameN, hw_def]
          simp [hv]
        rw [h_prog, h_frame]
        calc
          thetaM * (progFrameN g A n w * stepM (turnR A (g.refD w) (g.par v)) A.d) * thetaM =
              thetaM * progFrameN g A n w * stepM (turnR A (g.refD w) (g.par v)) A.d * thetaM := by
            simp [Matrix.mul_assoc]
          _ = thetaM * progFrameN g A n w * 1 * stepM (turnR A (g.refD w) (g.par v)) A.d * thetaM := by
            simp
          _ = thetaM * progFrameN g A n w * (thetaM * thetaM) * stepM (turnR A (g.refD w) (g.par v)) A.d * thetaM := by
            rw [← theta_mul_theta]
          _ = (thetaM * progFrameN g A n w * thetaM) * (thetaM * stepM (turnR A (g.refD w) (g.par v)) A.d * thetaM) := by
            simp [Matrix.mul_assoc]
          _ = g.frameN A n w * stepM (A.turn (g.refD w) (g.par v)) A.d := by
            rw [h_ih, h_step_eq]

/-- The angle placing a free point in Definition 7.2 and in the program sum to `2π`. -/
theorem free_angle_sum {H : HexChoice P k} {A : Assign P k} (hR : RelSys P H A)
    {g : GlueData P k} (hg : g.Valid) (m : Fin k) :
    (A.turn (g.refD ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst)
        ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)) +
      gam (A.r m (g.freeCorner m + 1)) (A.r m (g.freeCorner m)) A.d) +
    (turnR A (g.refD ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst)
        ((P.R.face ^ ((g.freeCorner m - 1 : Fin 6) : ℕ)) (H.base m)).symm +
      gam (A.r m (g.freeCorner m - 1)) (A.r m (g.freeCorner m)) A.d) = 2 * π := by
  let b := H.base m
  let i : Fin 6 := g.freeCorner m
  let e := (P.R.face ^ (i : ℕ)) b
  let a := g.refD e.fst
  have hae : a.fst = e.fst := by
    simpa [a] using refD_fst hg e.fst
  have h_rot : ((P.R.face ^ ((i - 1 : Fin 6) : ℕ)) b).symm = P.R.rot e := by
    simpa [e] using (rot_face_pow (H.hex m) i).symm
  have h_turn : A.turn a e + A.corner e + turnR A a (P.R.rot e) = 2 * π :=
    turn_add_corner_add_turnR hR.vertex_sum hae
  have h_corner : A.corner e = gam (A.r m (i + 1)) (A.r m i) A.d + gam (A.r m (i - 1)) (A.r m i) A.d := by
    have h_wheel := hR.wheel m
    have h_wheel_clauses := h_wheel.2.2.2.2
    simpa [e, b, Assign.fc] using h_wheel_clauses i
  calc
    (A.turn (g.refD ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst)
        ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)) +
      gam (A.r m (g.freeCorner m + 1)) (A.r m (g.freeCorner m)) A.d) +
    (turnR A (g.refD ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst)
        ((P.R.face ^ ((g.freeCorner m - 1 : Fin 6) : ℕ)) (H.base m)).symm +
      gam (A.r m (g.freeCorner m - 1)) (A.r m (g.freeCorner m)) A.d)
        = (A.turn a e + gam (A.r m (i + 1)) (A.r m i) A.d) +
          (turnR A a (P.R.rot e) + gam (A.r m (i - 1)) (A.r m i) A.d) := by
      simp [a, e, b, i, h_rot]
    _ = (A.turn a e + A.corner e + turnR A a (P.R.rot e)) := by
      rw [h_corner]
      ring
    _ = 2 * π := h_turn

/-- Step (ii): the configuration of Definition 7.2 is `Θ` applied to the program's, point by point,
for the same tree and the same corners of the free points. -/
theorem glueY_theta {H : HexChoice P k} {A : Assign P k} (hR : RelSys P H A)
    {g : GlueData P k} (hg : g.Valid) : ∀ a, glueY H A g a = thetaL (progGlueY H A g a) := by
  intro a
  cases a with
  | inl v =>
    -- glueY H A g (Sum.inl v) = toEuclideanLin (g.frame A v) e3
    -- g.frame A v = thetaM * progFrame g A v * thetaM  (by frameN_theta)
    -- thetaM fixes e3 (theta_e3)
    -- toEuclideanLin of product is composition (Matrix.toLpLin_mul_same)
    -- thetaL_apply: thetaL v = toEuclideanLin thetaM v
    have hframe : g.frame A v = thetaM * progFrame g A v * thetaM := by
      dsimp [GlueData.frame, progFrame]
      rw [← (frameN_theta hR.vertex_sum hg (g.depth v) v).symm]
    calc
      glueY H A g (Sum.inl v) = toEuclideanLin (g.frame A v) e3 := rfl
      _ = toEuclideanLin (thetaM * progFrame g A v * thetaM) e3 := by rw [hframe]
      _ = toEuclideanLin (thetaM * progFrame g A v) (toEuclideanLin thetaM e3) := by
        simpa [Matrix.toLpLin_mul_same, LinearMap.coe_comp] using rfl
      _ = toEuclideanLin (thetaM * progFrame g A v) e3 := by rw [theta_e3]
      _ = toEuclideanLin thetaM (toEuclideanLin (progFrame g A v) e3) := by
        simpa [Matrix.toLpLin_mul_same, LinearMap.coe_comp] using rfl
      _ = thetaL (toEuclideanLin (progFrame g A v) e3) := by rw [thetaL_apply]
      _ = thetaL (progGlueY H A g (Sum.inl v)) := rfl
  | inr m =>
    -- Let v_i = ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst
    -- glueY: toEuclideanLin (g.frame A v_i * rotZ ψ * rotY r) e3
    -- progGlueY: toEuclideanLin (progFrame g A v_i * rotZ φ * rotY r) e3
    -- ψ + φ = 2π (free_angle_sum hR hg m)
    -- rotZ (-φ) = rotZ ψ (rotZ_neg_of_add)
    -- thetaM * (rotZ ψ * rotY r) e3 = (rotZ φ * rotY r) e3 (theta_rotZ_rotY_e3)
    -- g.frame A v_i = thetaM * progFrame g A v_i * thetaM (frameN_theta)
    -- thetaL_apply, toLpLin_mul_same
    set v_i := ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst with hv_i
    set ψ := A.turn (g.refD v_i) ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)) +
      gam (A.r m (g.freeCorner m + 1)) (A.r m (g.freeCorner m)) A.d with hψ
    set φ := turnR A (g.refD v_i) ((P.R.face ^ ((g.freeCorner m - 1 : Fin 6) : ℕ)) (H.base m)).symm +
      gam (A.r m (g.freeCorner m - 1)) (A.r m (g.freeCorner m)) A.d with hφ
    set r := A.r m (g.freeCorner m) with hr
    have hsum : ψ + φ = 2 * π := by
      dsimp [ψ, φ]
      exact free_angle_sum hR hg m
    have hrot' : rotZ (-ψ) = rotZ φ :=
      rotZ_neg_of_add φ ψ (by rw [add_comm]; exact hsum)
    have hframe : g.frame A v_i = thetaM * progFrame g A v_i * thetaM := by
      dsimp [v_i, GlueData.frame, progFrame]
      rw [← (frameN_theta hR.vertex_sum hg
        (g.depth ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst)
        ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst).symm]
    have htheta_rotY : toEuclideanLin (thetaM * (rotZ ψ * rotY r)) e3 =
        toEuclideanLin (rotZ φ * rotY r) e3 := by
      rw [theta_rotZ_rotY_e3 φ ψ r hrot']
    calc
      glueY H A g (Sum.inr m) = toEuclideanLin
        (g.frame A v_i * rotZ ψ * rotY r) e3 := by
        dsimp [glueY, v_i, ψ, r]
      _ = toEuclideanLin
        ((thetaM * progFrame g A v_i * thetaM) * rotZ ψ * rotY r) e3 := by rw [hframe]
      _ = toEuclideanLin (thetaM * progFrame g A v_i * thetaM * rotZ ψ * rotY r) e3 := rfl
      _ = toEuclideanLin ((thetaM * progFrame g A v_i) * (thetaM * rotZ ψ * rotY r)) e3 := by
        simp [Matrix.mul_assoc]
      _ = toEuclideanLin (thetaM * progFrame g A v_i)
          (toEuclideanLin (thetaM * rotZ ψ * rotY r) e3) := by
        simpa [Matrix.toLpLin_mul_same, LinearMap.coe_comp] using rfl
      _ = toEuclideanLin thetaM
          (toEuclideanLin (progFrame g A v_i)
            (toEuclideanLin (thetaM * rotZ ψ * rotY r) e3)) := by
        simpa [Matrix.toLpLin_mul_same, LinearMap.coe_comp] using rfl
      _ = toEuclideanLin thetaM
          (toEuclideanLin (progFrame g A v_i)
            (toEuclideanLin (thetaM * (rotZ ψ * rotY r)) e3)) := by
        simp [Matrix.mul_assoc]
      _ = toEuclideanLin thetaM
          (toEuclideanLin (progFrame g A v_i)
            (toEuclideanLin (rotZ φ * rotY r) e3)) := by rw [htheta_rotY]
      _ = toEuclideanLin thetaM
          (toEuclideanLin (progFrame g A v_i * rotZ φ * rotY r) e3) := by
        simpa [Matrix.toLpLin_mul_same, LinearMap.coe_comp, Matrix.mul_assoc] using rfl
      _ = thetaL (toEuclideanLin (progFrame g A v_i * rotZ φ * rotY r) e3) := by
        rw [thetaL_apply]
      _ = thetaL (progGlueY H A g (Sum.inr m)) := by
        dsimp [progGlueY, v_i, φ, r]

/-- Pair fires on the configuration of Definition 7.2 when it fires on the program's. -/
theorem pairFires_theta {H : HexChoice P k} {A : Assign P k} (hR : RelSys P H A)
    {g : GlueData P k} (hg : g.Valid) (h : PairFires P A (progGlueY H A g)) :
    PairFires P A (glueY H A g) := by
  obtain ⟨a, b, hab, hadj, hlt⟩ := h
  refine ⟨a, b, hab, hadj, ?_⟩
  rw [glueY_theta hR hg a, glueY_theta hR hg b, ← map_sub, LinearIsometryEquiv.norm_map]
  exact hlt

end Tammes15.PaperSteps
