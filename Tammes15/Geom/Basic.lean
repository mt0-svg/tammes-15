import Tammes15.Local41.Rotation
import Tammes15.Trigrows.Sdist

/-!
# Convex spherical polygons in cone form

A face of the drawn contact graph (paper, Lemma A.7, and Section 9.5) is read as a
sequence `A : ℕ → E3` of period `m`, unit vertices, with strict support in the cone form of
`StrictSupportFace`: every vertex other than `A i`, `A (i + 1)` lies strictly on the positive side
of `cross (A i) (A (i + 1))`. A point is inside when it is strictly on the positive side of every
side, in the closed face when it is on the nonnegative side.

Main statements: the four vector identity `cramer4`, positivity of every cyclically ordered triple
of vertices (`IsCPoly.triple_pos`), invariance under shifts, and the perimeter.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Geom

/-- A strictly convex spherical polygon with `m` vertices in cone form, indexed periodically. -/
structure IsCPoly (m : ℕ) (A : ℕ → E3) : Prop where
  three : 3 ≤ m
  unit : ∀ i, ‖A i‖ = 1
  periodic : ∀ i, A (i + m) = A i
  support : ∀ i k, 2 ≤ k → k < m → 0 < ⟪cross (A i) (A (i + 1)), A (i + k)⟫

/-- `x` lies strictly inside the polygon `A`. -/
def Inside (A : ℕ → E3) (x : E3) : Prop := ∀ i, 0 < ⟪cross (A i) (A (i + 1)), x⟫

/-- `x` lies in the closed polygon `A`. -/
def InClosed (A : ℕ → E3) (x : E3) : Prop := ∀ i, 0 ≤ ⟪cross (A i) (A (i + 1)), x⟫

/-- Perimeter of the polygon `A` with `m` sides. -/
noncomputable def perim (m : ℕ) (A : ℕ → E3) : ℝ := ∑ i ∈ Finset.range m, sdist (A i) (A (i + 1))

/-- The cross product in coordinates. -/
theorem cross_coords (a b : E3) :
    cross a b = !₂[a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] := by
  ext i; fin_cases i <;> simp [cross, cross_apply]

/-- The inner product in coordinates. -/
theorem inner_coords (a b : E3) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem triple_cycle (a b c : E3) : ⟪cross a b, c⟫ = ⟪cross b c, a⟫ := by
  simp only [inner_coords, cross_coords]; simp; ring

theorem cross_swap (a b : E3) : cross b a = -cross a b := by
  ext i; simp only [cross_coords]; fin_cases i <;> simp <;> ring

/-- The four vector identity (Cramer's rule in `ℝ³`). -/
theorem cramer4 (a b c d n : E3) :
    ⟪cross b c, d⟫ * ⟪a, n⟫ - ⟪cross a c, d⟫ * ⟪b, n⟫ + ⟪cross a b, d⟫ * ⟪c, n⟫ -
      ⟪cross a b, c⟫ * ⟪d, n⟫ = 0 := by
  simp only [inner_coords, cross_coords]; simp; ring

theorem IsCPoly.periodic_mul {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (i k : ℕ) :
    A (i + k * m) = A i := by
  induction' k with k ih
  · simp
  · rw [Nat.succ_mul, ← add_assoc, hA.periodic, ih]

theorem IsCPoly.mod {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (i : ℕ) : A i = A (i % m) := by
  calc
    A i = A (i % m + m * (i / m)) := by rw [Nat.mod_add_div i m]
    _ = A (i % m + (i / m) * m) := by rw [mul_comm m (i / m)]
    _ = A (i % m) := by rw [hA.periodic_mul (i % m) (i / m)]

theorem IsCPoly.shift {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (j : ℕ) :
    IsCPoly m (fun i => A (j + i)) := by
  refine ⟨hA.three, ?_, ?_, ?_⟩
  · intro i
    exact hA.unit (j + i)
  · intro i
    calc
      A (j + (i + m)) = A ((j + i) + m) := by simp [add_assoc]
      _ = A (j + i) := hA.periodic (j + i)
  · intro i k h2 hk
    simpa [add_assoc] using hA.support (j + i) k h2 hk

/-- Support against any vertex other than the two ends of the side. -/
theorem IsCPoly.support_of_ne {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (i j : ℕ)
    (h0 : j % m ≠ i % m) (h1 : j % m ≠ (i + 1) % m) :
    0 < ⟪cross (A i) (A (i + 1)), A j⟫ := by
  have hm : 0 < m := by
    have h3 : 3 ≤ m := hA.three
    omega
  set ri := i % m with hri_def
  set rj := j % m with hrj_def
  have hri_lt : ri < m := Nat.mod_lt i hm
  have hrj_lt : rj < m := Nat.mod_lt j hm
  rcases Nat.le_total ri rj with (hle | hlt)
  · -- case ri ≤ rj
    set k := rj - ri with hk_def
    have hk_lt_m : k < m := by
      rw [hk_def]
      exact lt_of_le_of_lt (Nat.sub_le rj ri) hrj_lt
    have hk_ge_2 : 2 ≤ k := by
      rw [hk_def]
      by_contra! h
      have hk_le_1 : rj - ri ≤ 1 := by omega
      have h_cases : rj - ri = 0 ∨ rj - ri = 1 := by omega
      rcases h_cases with (hzero | hone)
      · -- rj - ri = 0, so rj = ri
        have heq : rj = ri := by
          have := Nat.add_sub_cancel' hle
          rw [hzero, add_zero] at this
          exact this.symm
        rw [hri_def, hrj_def] at heq
        exact h0 heq
      · -- rj - ri = 1, so rj = ri + 1
        have heq : rj = ri + 1 := by
          have := Nat.add_sub_cancel' hle
          rw [hone] at this
          omega
        -- then (i+1)%m = ri+1 = rj, contradicting h1
        have h_contra : rj = (i + 1) % m := by
          rw [heq]
          have hri1_lt_m : ri + 1 < m := by
            rw [← heq]
            exact hrj_lt
          calc
            ri + 1 = (ri + 1) % m := by rw [Nat.mod_eq_of_lt hri1_lt_m]
            _ = ((i % m) + 1) % m := by rfl
            _ = (i + 1) % m := by rw [Nat.mod_add_mod]
        rw [hrj_def] at h_contra
        exact h1 h_contra
    have h_mod_eq : (i + k) % m = j % m := by
      rw [hk_def]
      calc
        (i + (rj - ri)) % m = ((i % m) + (rj - ri)) % m := by rw [← Nat.mod_add_mod]
        _ = (ri + (rj - ri)) % m := by rw [hri_def]
        _ = rj % m := by rw [Nat.add_sub_cancel' hle]
        _ = rj := Nat.mod_eq_of_lt hrj_lt
        _ = j % m := by rw [hrj_def]
    have hA_eq : A (i + k) = A j := by
      rw [hA.mod (i + k), h_mod_eq, hA.mod j]
    rw [← hA_eq]
    exact hA.support i k hk_ge_2 hk_lt_m
  · -- case rj < ri
    set k := rj + m - ri with hk_def
    have hk_lt_m : k < m := by
      rw [hk_def]
      have hsub : 1 ≤ ri - rj := by omega
      omega
    have hk_ge_2 : 2 ≤ k := by
      rw [hk_def]
      by_contra! h
      have hk_le_1 : rj + m - ri ≤ 1 := by omega
      have hri_eq_m_sub_one : ri = m - 1 := by
        have hsub_pos : 1 ≤ ri - rj := by omega
        omega
      have hrj_eq_zero : rj = 0 := by
        omega
      -- Now rj = 0 = (m-1+1)%m = (ri+1)%m
      have h_contra : rj = (ri + 1) % m := by
        rw [hri_eq_m_sub_one, hrj_eq_zero]
        have hm_eq : m - 1 + 1 = m := by omega
        rw [hm_eq, Nat.mod_self]
      rw [hrj_def] at h_contra
      have h_contra' : j % m = (i + 1) % m := by
        rw [← Nat.mod_add_mod, ← hri_def]
        exact h_contra
      exact h1 h_contra'
    have h_mod_eq : (i + k) % m = j % m := by
      rw [hk_def]
      calc
        (i + (rj + m - ri)) % m = ((i % m) + (rj + m - ri)) % m := by rw [← Nat.mod_add_mod]
        _ = (ri + (rj + m - ri)) % m := by rw [hri_def]
        _ = (rj + m) % m := by
          rw [Nat.add_sub_cancel' (by omega : ri ≤ rj + m)]
        _ = rj % m := by rw [Nat.add_mod_right]
        _ = rj := Nat.mod_eq_of_lt hrj_lt
        _ = j % m := by rw [hrj_def]
    have hA_eq : A (i + k) = A j := by
      rw [hA.mod (i + k), h_mod_eq, hA.mod j]
    rw [← hA_eq]
    exact hA.support i k hk_ge_2 hk_lt_m

theorem inner_cross_right_zero (a b : E3) : ⟪cross a b, b⟫ = 0 := by
  simp only [inner_coords, cross_coords]; simp; ring

/-- Triple positivity from the first vertex, by induction on the middle index: dotting the four
vector identity with the pole of the side `(k, k + 1)` gives
`[0, j+1, k] [k, k+1, j] = [j, j+1, k] [k, k+1, 0] + [0, j, k] [k, k+1, j+1]`. -/
theorem IsCPoly.triple_pos_zero {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (j k : ℕ) (hj : 1 ≤ j)
    (hjk : j < k) (hk : k < m) : 0 < ⟪cross (A 0) (A j), A k⟫ := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using hA.support 0 k (by omega) hk
    · have h1 : 0 < ⟪cross (A 0) (A j), A k⟫ := ih hj0 (by omega)
      have h2 : 0 < ⟪cross (A j) (A (j + 1)), A k⟫ := by
        have := hA.support j (k - j) (by omega) (by omega)
        rwa [show j + (k - j) = k by omega] at this
      have h3 : 0 ≤ ⟪cross (A k) (A (k + 1)), A 0⟫ := by
        rcases Nat.lt_or_ge (k + 1) m with hk1 | hk1
        · have := hA.support k (m - k) (by omega) (by omega)
          rw [show k + (m - k) = 0 + m by omega, hA.periodic 0] at this
          exact this.le
        · rw [show k + 1 = 0 + m by omega, hA.periodic 0, inner_cross_right_zero]
      have h4 : 0 < ⟪cross (A k) (A (k + 1)), A (j + 1)⟫ := by
        have := hA.support k (m - k + (j + 1)) (by omega) (by omega)
        rwa [show k + (m - k + (j + 1)) = (j + 1) + m by omega, hA.periodic] at this
      have h5 : 0 < ⟪cross (A k) (A (k + 1)), A j⟫ := by
        have := hA.support k (m - k + j) (by omega) (by omega)
        rwa [show k + (m - k + j) = j + m by omega, hA.periodic] at this
      have key : ⟪cross (A 0) (A (j + 1)), A k⟫ * ⟪cross (A k) (A (k + 1)), A j⟫ =
          ⟪cross (A j) (A (j + 1)), A k⟫ * ⟪cross (A k) (A (k + 1)), A 0⟫ +
            ⟪cross (A 0) (A j), A k⟫ * ⟪cross (A k) (A (k + 1)), A (j + 1)⟫ := by
        simp only [inner_coords, cross_coords]; simp; ring
      by_contra hneg
      rw [not_lt] at hneg
      have := mul_nonpos_of_nonpos_of_nonneg hneg h5.le
      nlinarith [mul_pos h1 h4, mul_nonneg h2.le h3]

/-- Every cyclically ordered triple of vertices is positively oriented. -/
theorem IsCPoly.triple_pos {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (i a b : ℕ) (ha : 0 < a)
    (hab : a < b) (hb : b < m) : 0 < ⟪cross (A i) (A (i + a)), A (i + b)⟫ := by
  simpa using (hA.shift i).triple_pos_zero a b ha hab hb

theorem inside_iff {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (x : E3) :
    Inside A x ↔ ∀ i < m, 0 < ⟪cross (A i) (A (i + 1)), x⟫ := by
  constructor
  · intro h i _hi
    exact h i
  · intro h i
    have hm : 0 < m := by
      have h3 : 3 ≤ m := hA.three
      omega
    have hm1 : 1 < m := by
      have h3 : 3 ≤ m := hA.three
      omega
    have hmod_lt : i % m < m := Nat.mod_lt i hm
    have h_eq : A i = A (i % m) := hA.mod i
    have h_eq_next : A (i + 1) = A ((i % m) + 1) := by
      calc
        A (i + 1) = A ((i + 1) % m) := hA.mod (i + 1)
        _ = A (((i % m) + 1) % m) := by
          congr 1
          calc
            (i + 1) % m = ((i % m) + (1 % m)) % m := by rw [Nat.add_mod]
            _ = ((i % m) + 1) % m := by
              rw [Nat.mod_eq_of_lt hm1]
        _ = A ((i % m) + 1) := (hA.mod ((i % m) + 1)).symm
    rw [h_eq, h_eq_next]
    exact h (i % m) hmod_lt

theorem inClosed_iff {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (x : E3) :
    InClosed A x ↔ ∀ i < m, 0 ≤ ⟪cross (A i) (A (i + 1)), x⟫ := by
  have hm : 0 < m := by
    have h3 := hA.three
    omega
  have h1m : 1 < m := by
    have h3 := hA.three
    omega
  constructor
  · intro h i hi
    exact h i
  · intro h i
    have hmod_i := hA.mod i
    have hmod_i1 := hA.mod (i + 1)
    have hmod_im1 := (hA.mod ((i % m) + 1)).symm
    have h_eq : A (i + 1) = A ((i % m) + 1) := by
      calc
        A (i + 1) = A ((i + 1) % m) := hmod_i1
        _ = A (((i % m) + 1) % m) := by
          rw [Nat.add_mod, show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt h1m]
        _ = A ((i % m) + 1) := hmod_im1
    have h_inner_eq : ⟪cross (A i) (A (i + 1)), x⟫ = ⟪cross (A (i % m)) (A ((i % m) + 1)), x⟫ := by
      rw [hmod_i, h_eq]
    rw [h_inner_eq]
    exact h (i % m) (Nat.mod_lt i hm)

theorem Inside.shift {A : ℕ → E3} {x : E3} (hx : Inside A x) (j : ℕ) :
    Inside (fun i => A (j + i)) x := by
  intro i
  have h := hx (j + i)
  simpa [add_assoc] using h

theorem perim_shift {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (j : ℕ) :
    perim m (fun i => A (j + i)) = perim m A := by
  set f := fun i : ℕ => sdist (A i) (A (i + 1)) with hf
  have hf_periodic : ∀ i, f (i + m) = f i := by
    intro i
    dsimp [f]
    rw [hA.periodic i]
    have h : (i + m) + 1 = (i + 1) + m := by omega
    rw [h, hA.periodic (i + 1)]
  have hstep : ∀ k, (∑ i ∈ Finset.range m, f (k + 1 + i)) = (∑ i ∈ Finset.range m, f (k + i)) := by
    intro k
    have hsum_succ' := Finset.sum_range_succ' (fun i => f (k + i)) m
    have hsum_succ := Finset.sum_range_succ (fun i => f (k + i)) m
    have h_eq : f (k + 0) = f (k + m) := by
      simpa [add_comm] using (hf_periodic k).symm
    have hshift : (∑ i ∈ Finset.range m, f (k + (i + 1))) = (∑ i ∈ Finset.range m, f (k + 1 + i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [show k + (i + 1) = k + 1 + i by omega]
    rw [← hshift]
    linarith [hsum_succ', hsum_succ, h_eq]
  induction' j with k ih
  · simp [perim]
  · have ih_unfolded : (∑ i ∈ Finset.range m, f (k + i)) = (∑ i ∈ Finset.range m, f i) := by
      simpa [perim, f, add_assoc] using ih
    have h_eq : (∑ i ∈ Finset.range m, f (k + 1 + i)) = (∑ i ∈ Finset.range m, f i) := by
      rw [hstep k, ih_unfolded]
    simpa [perim, f, add_assoc] using h_eq

end Tammes15.Geom
