import Tammes15.D3Kernel.Kinds.LeafFarm
import Tammes15.D3Kernel.Kinds.Turn

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Real

structure M3 where
  a00 : ℤ
  a01 : ℤ
  a02 : ℤ
  a10 : ℤ
  a11 : ℤ
  a12 : ℤ
  a20 : ℤ
  a21 : ℤ
  a22 : ℤ

namespace M3

def mul (A B : M3) : M3 :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10 + A.a02 * B.a20, A.a00 * B.a01 + A.a01 * B.a11 + A.a02 * B.a21,
    A.a00 * B.a02 + A.a01 * B.a12 + A.a02 * B.a22,
    A.a10 * B.a00 + A.a11 * B.a10 + A.a12 * B.a20, A.a10 * B.a01 + A.a11 * B.a11 + A.a12 * B.a21,
    A.a10 * B.a02 + A.a11 * B.a12 + A.a12 * B.a22,
    A.a20 * B.a00 + A.a21 * B.a10 + A.a22 * B.a20, A.a20 * B.a01 + A.a21 * B.a11 + A.a22 * B.a21,
    A.a20 * B.a02 + A.a21 * B.a12 + A.a22 * B.a22⟩

def one : M3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

noncomputable def toMat (A : M3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(A.a00 : ℝ), A.a01, A.a02; A.a10, A.a11, A.a12; A.a20, A.a21, A.a22]

theorem toMat_mul (A B : M3) : (A.mul B).toMat = A.toMat * B.toMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, mul, Matrix.mul_apply, Fin.sum_univ_three] <;> push_cast <;> ring

theorem toMat_one : one.toMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, one]

end M3

def rzI (c s q : ℤ) : M3 := ⟨c, -s, 0, s, c, 0, 0, 0, q⟩

def ryI (c s q : ℤ) : M3 := ⟨c, 0, s, 0, q, 0, -s, 0, c⟩

def flipI : M3 := ⟨-1, 0, 0, 0, -1, 0, 0, 0, 1⟩

theorem rotZ_eq {φ : ℝ} {c s q : ℤ} (hq : (q : ℝ) ≠ 0) (hc : Real.cos φ = c / q) (hs : Real.sin φ = s / q) :
    rotZ φ = (1 / (q : ℝ)) • (rzI c s q).toMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ, rzI, M3.toMat, hc, hs, hq] <;> field_simp

theorem rotY_eq {θ : ℝ} {c s q : ℤ} (hq : (q : ℝ) ≠ 0) (hc : Real.cos θ = c / q) (hs : Real.sin θ = s / q) :
    rotY θ = (1 / (q : ℝ)) • (ryI c s q).toMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotY, ryI, M3.toMat, hc, hs, hq] <;> field_simp

theorem flipZ_eq : flipZ = flipI.toMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flipZ, flipI, M3.toMat]

noncomputable def angR (K q : ℕ) (a : ℤ) : ℝ := q * (π / 2) + 2 * Real.arctan (a / 2 ^ K)

def qcI (q : ℕ) (c s : ℤ) : ℤ := if q % 4 = 0 then c else if q % 4 = 1 then -s else if q % 4 = 2 then -c else s

def qsI (q : ℕ) (c s : ℤ) : ℤ := if q % 4 = 0 then s else if q % 4 = 1 then c else if q % 4 = 2 then -s else -c

def angDen (K : ℕ) (a : ℤ) : ℤ := ((4 ^ K : ℕ) : ℤ) + a * a

def angC (K q : ℕ) (a : ℤ) : ℤ := qcI q (((4 ^ K : ℕ) : ℤ) - a * a) (((2 ^ (K + 1) : ℕ) : ℤ) * a)

def angS (K q : ℕ) (a : ℤ) : ℤ := qsI q (((4 ^ K : ℕ) : ℤ) - a * a) (((2 ^ (K + 1) : ℕ) : ℤ) * a)

theorem angDen_pos (K : ℕ) (a : ℤ) : 0 < angDen K a := by
  unfold angDen
  have : (0 : ℤ) < ((4 ^ K : ℕ) : ℤ) := by exact_mod_cast pow_pos (by norm_num : 0 < 4) K
  nlinarith [mul_self_nonneg a]

theorem lf_qc_div (q : ℕ) (c s d : ℝ) : lf_qc q (c / d) (s / d) = lf_qc q c s / d := by
  unfold lf_qc
  split_ifs <;> ring

theorem lf_qs_div (q : ℕ) (c s d : ℝ) : lf_qs q (c / d) (s / d) = lf_qs q c s / d := by
  unfold lf_qs
  split_ifs <;> ring

theorem lf_qc_cast (q : ℕ) (c s : ℤ) : lf_qc q c s = (qcI q c s : ℝ) := by
  unfold lf_qc qcI
  split_ifs <;> push_cast <;> rfl

theorem lf_qs_cast (q : ℕ) (c s : ℤ) : lf_qs q c s = (qsI q c s : ℝ) := by
  unfold lf_qs qsI
  split_ifs <;> push_cast <;> rfl

theorem two_arctan_ratio (K : ℕ) (a : ℤ) :
    (1 - ((a : ℝ) / 2 ^ K) ^ 2) / (1 + ((a : ℝ) / 2 ^ K) ^ 2) =
        ((((4 ^ K : ℕ) : ℤ) - a * a : ℤ) : ℝ) / (angDen K a : ℝ) ∧
      2 * ((a : ℝ) / 2 ^ K) / (1 + ((a : ℝ) / 2 ^ K) ^ 2) =
        ((((2 ^ (K + 1) : ℕ) : ℤ) * a : ℤ) : ℝ) / (angDen K a : ℝ) := by
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  have h4 : (4 : ℝ) ^ K = (2 ^ K) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hD : (angDen K a : ℝ) = (2 ^ K) ^ 2 + (a : ℝ) ^ 2 := by unfold angDen; push_cast; rw [h4]; ring
  have hDpos : (0 : ℝ) < (2 ^ K) ^ 2 + (a : ℝ) ^ 2 := by positivity
  constructor
  · rw [hD]
    push_cast
    rw [h4]
    field_simp
  · rw [hD]
    push_cast
    rw [pow_succ]
    field_simp
    ring

theorem cos_angR (K q : ℕ) (a : ℤ) : Real.cos (angR K q a) = (angC K q a : ℝ) / (angDen K a : ℝ) := by
  unfold angR angC
  rw [lf_cos_quarter, lf_cos_two_arctan, lf_sin_two_arctan, (two_arctan_ratio K a).1,
    (two_arctan_ratio K a).2, lf_qc_div, lf_qc_cast]

theorem sin_angR (K q : ℕ) (a : ℤ) : Real.sin (angR K q a) = (angS K q a : ℝ) / (angDen K a : ℝ) := by
  unfold angR angS
  rw [lf_sin_quarter, lf_cos_two_arctan, lf_sin_two_arctan, (two_arctan_ratio K a).1,
    (two_arctan_ratio K a).2, lf_qs_div, lf_qs_cast]

theorem rotZ_angR (K q : ℕ) (a : ℤ) :
    rotZ (angR K q a) = (1 / (angDen K a : ℝ)) • (rzI (angC K q a) (angS K q a) (angDen K a)).toMat :=
  rotZ_eq (by exact_mod_cast (angDen_pos K a).ne') (cos_angR K q a) (sin_angR K q a)

theorem rotY_angR (K q : ℕ) (a : ℤ) :
    rotY (angR K q a) = (1 / (angDen K a : ℝ)) • (ryI (angC K q a) (angS K q a) (angDen K a)).toMat :=
  rotY_eq (by exact_mod_cast (angDen_pos K a).ne') (cos_angR K q a) (sin_angR K q a)

def stepI (K qφ : ℕ) (aφ : ℤ) (qδ : ℕ) (aδ : ℤ) : M3 :=
  ((rzI (angC K qφ aφ) (angS K qφ aφ) (angDen K aφ)).mul
    (ryI (angC K qδ aδ) (angS K qδ aδ) (angDen K aδ))).mul flipI

theorem scaled_mul' (A B : M3) (x y : ℝ) : (x • A.toMat) * (y • B.toMat) = (x * y) • (A.mul B).toMat := by
  rw [M3.toMat_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem stepM_angR (K qφ : ℕ) (aφ : ℤ) (qδ : ℕ) (aδ : ℤ) :
    stepM (angR K qφ aφ) (angR K qδ aδ) =
      (1 / ((angDen K aφ : ℝ) * angDen K aδ)) • (stepI K qφ aφ qδ aδ).toMat := by
  unfold stepM stepI
  rw [rotZ_angR, rotY_angR, flipZ_eq, M3.toMat_mul, M3.toMat_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  field_simp

end Tammes15.D3Kernel.Kinds
