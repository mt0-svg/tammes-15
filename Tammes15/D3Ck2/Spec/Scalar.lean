import Mathlib

namespace D3Ck2Spec

open Real

def rshN (x s : ℕ) : ℕ := (x + 2 ^ (s - 1)) / 2 ^ s

def kcN (a c : ℕ) : ℕ := a * c / 2 ^ 28

theorem rshN_err (x s : ℕ) (hs : 1 ≤ s) : |(rshN x s : ℝ) - (x : ℝ) / 2 ^ s| ≤ 1 / 2 := by
  have hm_pos : 0 < 2 ^ s := pow_pos (by norm_num) s
  have hm_pos' : 0 < ((2 : ℝ) ^ s) := by exact_mod_cast hm_pos
  have hpow : ((2 : ℝ) ^ (s - 1)) = ((2 : ℝ) ^ s) / 2 := by
    have h : ((2 : ℝ) ^ s) = 2 * ((2 : ℝ) ^ (s - 1)) := by
      calc
        ((2 : ℝ) ^ s) = ((2 : ℝ) ^ ((s - 1) + 1)) := by rw [Nat.sub_add_cancel hs]
        _ = ((2 : ℝ) ^ (s - 1)) * ((2 : ℝ) ^ 1) := by rw [pow_add]
        _ = ((2 : ℝ) ^ (s - 1)) * 2 := by norm_num
        _ = 2 * ((2 : ℝ) ^ (s - 1)) := by ring
    linarith
  have hdiv := Nat.div_add_mod (x + 2 ^ (s - 1)) (2 ^ s)
  have hmod := Nat.mod_lt (x + 2 ^ (s - 1)) hm_pos
  have hineq1 : (rshN x s) * (2 ^ s) ≤ x + 2 ^ (s - 1) := by
    rw [← hdiv]
    dsimp [rshN]
    rw [Nat.mul_comm ((x + 2 ^ (s - 1)) / 2 ^ s) (2 ^ s)]
    exact Nat.le_add_right _ _
  have hineq2 : x + 2 ^ (s - 1) < ((rshN x s) + 1) * (2 ^ s) := by
    rw [← hdiv]
    dsimp [rshN]
    rw [Nat.mul_comm (2 ^ s) ((x + 2 ^ (s - 1)) / 2 ^ s), Nat.succ_mul]
    exact Nat.add_lt_add_left hmod (((x + 2 ^ (s - 1)) / 2 ^ s) * (2 ^ s))
  have hineq1' : ((rshN x s : ℕ) : ℝ) * ((2 : ℝ) ^ s) ≤ (x : ℝ) + ((2 : ℝ) ^ (s - 1)) := by
    exact_mod_cast hineq1
  have hineq2' : (x : ℝ) + ((2 : ℝ) ^ (s - 1)) < (((rshN x s : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ s) := by
    exact_mod_cast hineq2
  rw [hpow] at hineq1' hineq2'
  rw [abs_le]
  constructor
  ·
    field_simp [hm_pos'.ne.symm]
    linarith
  ·
    field_simp [hm_pos'.ne.symm]
    linarith

theorem kcN_floor (a c : ℕ) :
    (kcN a c : ℝ) ≤ (a : ℝ) * c / 2 ^ 28 ∧ (a : ℝ) * c / 2 ^ 28 < (kcN a c : ℝ) + 1 := by
  have hpos : 0 < 2 ^ 28 := by norm_num
  have hpos' : (0 : ℝ) < (2 ^ 28 : ℝ) := by norm_num
  have hle_nat : kcN a c * 2 ^ 28 ≤ a * c := by
    dsimp [kcN]
    exact Nat.div_mul_le_self (a * c) (2 ^ 28)
  have hlt_nat : a * c < kcN a c * 2 ^ 28 + 2 ^ 28 := by
    have h := Nat.lt_mul_div_succ (a * c) hpos

    have h' : 2 ^ 28 * (a * c / 2 ^ 28 + 1) = (a * c / 2 ^ 28) * 2 ^ 28 + 2 ^ 28 := by
      calc
        2 ^ 28 * (a * c / 2 ^ 28 + 1) = 2 ^ 28 * (a * c / 2 ^ 28) + 2 ^ 28 * 1 := by rw [mul_add]
        _ = 2 ^ 28 * (a * c / 2 ^ 28) + 2 ^ 28 := by rw [mul_one]
        _ = (a * c / 2 ^ 28) * 2 ^ 28 + 2 ^ 28 := by rw [mul_comm]
    rw [h'] at h
    dsimp [kcN]
    exact h
  have hle : (kcN a c : ℝ) ≤ (a : ℝ) * c / 2 ^ 28 := by
    have hcast : (kcN a c : ℝ) * (2 ^ 28 : ℝ) ≤ (a : ℝ) * (c : ℝ) := by
      exact_mod_cast hle_nat
    exact (le_div_iff₀ hpos').mpr hcast
  have hlt : (a : ℝ) * c / 2 ^ 28 < (kcN a c : ℝ) + 1 := by
    have hcast : (a : ℝ) * (c : ℝ) < (kcN a c : ℝ) * (2 ^ 28 : ℝ) + (2 ^ 28 : ℝ) := by
      exact_mod_cast hlt_nat
    apply (div_lt_iff₀ hpos').mpr
    simpa [add_mul, one_mul] using hcast
  exact And.intro hle hlt

def QPI : ℕ := 210828714

def HPI_LO : ℕ := 421657428

def PI_LO : ℕ := 843314856

def p2 (z : ℕ) : ℕ := rshN (z * z) 28

def p4 (z2 : ℕ) : ℕ := rshN (z2 * rshN z2 2) 26

def p6 (z2 z4 : ℕ) : ℕ := rshN (z4 * rshN z2 8) 20

def p8 (z4 : ℕ) : ℕ := rshN (z4 * rshN z4 14) 14

def p10 (z2 z8 : ℕ) : ℕ := rshN (z8 * rshN z2 22) 6

def cosP (z2 z4 z6 z8 z10 : ℕ) : ℕ :=
  rshN ((2 ^ 36 + kcN z4 2863311531 + kcN z8 1704352) -
    (z2 * 2 ^ 7 + kcN z6 95443718 + kcN z10 18937)) 8

def sinP (z z2 z4 z6 z8 : ℕ) : ℕ :=
  rshN (rshN ((2 ^ 36 + kcN z4 572662306 + kcN z8 189372) -
    (kcN z2 11453246123 + kcN z6 13634817)) 6 * z) 30

def sc28pZ (z : ℕ) : ℕ × ℕ :=
  let z2 := p2 z
  let z4 := p4 z2
  let z6 := p6 z2 z4
  let z8 := p8 z4
  let z10 := p10 z2 z8
  (sinP z z2 z4 z6 z8, cosP z2 z4 z6 z8 z10)

def sc28pS (x : ℕ) : ℤ × ℤ :=
  let x := min x (PI_LO + 1)
  let x1 := if HPI_LO < x then PI_LO - x else x
  let z := if QPI < x1 then HPI_LO - x1 else x1
  let p := sc28pZ z
  let sv := if QPI < x1 then p.2 else p.1
  let cv := if QPI < x1 then p.1 else p.2
  ((sv : ℤ), if HPI_LO < x then -(cv : ℤ) else (cv : ℤ))

theorem p2_err (z : ℕ) (_hz : z ≤ QPI) :
    |(p2 z : ℝ) - 2 ^ 28 * ((z : ℝ) / 2 ^ 28) ^ 2| ≤ 1 / 2 := by
  unfold p2 rshN
  have hpos : 0 < 2 ^ 28 := by positivity
  set q := (z * z + 2 ^ 27) / 2 ^ 28 with hq
  have hdiv_raw := Nat.div_add_mod (z * z + 2 ^ 27) (2 ^ 28)

  have hdiv : q * 2 ^ 28 + ((z * z + 2 ^ 27) % 2 ^ 28) = z * z + 2 ^ 27 := by
    rw [mul_comm]; exact hdiv_raw
  have hmod := Nat.mod_lt (z * z + 2 ^ 27) hpos
  have h_lower_nat : q * 2 ^ 28 ≤ z * z + 2 ^ 27 := by
    calc
      q * 2 ^ 28 ≤ q * 2 ^ 28 + ((z * z + 2 ^ 27) % 2 ^ 28) := Nat.le_add_right _ _
      _ = z * z + 2 ^ 27 := by rw [hdiv]
  have h_upper_nat : z * z + 2 ^ 27 < (q + 1) * 2 ^ 28 := by
    rw [← hdiv]
    have h := Nat.add_lt_add_left hmod (q * 2 ^ 28)

    simpa [Nat.succ_mul] using h
  have h_target : 2 ^ 28 * ((z : ℝ) / 2 ^ 28) ^ 2 = ((z : ℝ) * (z : ℝ)) / (2 ^ 28 : ℝ) := by
    field_simp
  rw [h_target]
  have hpos28 : (0 : ℝ) < (2 : ℝ) ^ 28 := by positivity
  have h_lower_real : (q : ℝ) * ((2 : ℝ) ^ 28) ≤ (z : ℝ) * (z : ℝ) + ((2 : ℝ) ^ 27) := by
    exact_mod_cast h_lower_nat
  have h_upper_real : (z : ℝ) * (z : ℝ) + ((2 : ℝ) ^ 27) < ((q : ℝ) + 1) * ((2 : ℝ) ^ 28) := by
    exact_mod_cast h_upper_nat
  have hpos28_ne : (2 : ℝ) ^ 28 ≠ 0 := by positivity
  have hdiv_eq : ((z : ℝ) * (z : ℝ) / ((2 : ℝ) ^ 28)) * ((2 : ℝ) ^ 28) = (z : ℝ) * (z : ℝ) := by
    field_simp [hpos28_ne]
  rw [abs_le]
  constructor
  ·
    have h_mul : (z : ℝ) * (z : ℝ) - ((2 : ℝ) ^ 27) ≤ (q : ℝ) * ((2 : ℝ) ^ 28) := by
      linarith
    have hhalf : -(1/2 : ℝ) * ((2 : ℝ) ^ 28) = -((2 : ℝ) ^ 27) := by
      calc
        -(1/2 : ℝ) * ((2 : ℝ) ^ 28) = -(1/2 : ℝ) * (2 * (2 : ℝ) ^ 27) := by rw [pow_succ']
        _ = (-(1/2 : ℝ) * 2) * (2 : ℝ) ^ 27 := by rw [mul_assoc]
        _ = (-1) * (2 : ℝ) ^ 27 := by rw [show (-(1/2 : ℝ)) * 2 = (-1 : ℝ) by ring]
        _ = -((2 : ℝ) ^ 27) := by ring
    have hgoal : -(1/2 : ℝ) * ((2 : ℝ) ^ 28) ≤ ((q : ℝ) - (z : ℝ) * (z : ℝ) / ((2 : ℝ) ^ 28)) * ((2 : ℝ) ^ 28) := by
      calc
        -(1/2 : ℝ) * ((2 : ℝ) ^ 28) = -((2 : ℝ) ^ 27) := hhalf
        _ ≤ (q : ℝ) * ((2 : ℝ) ^ 28) - (z : ℝ) * (z : ℝ) := by linarith
        _ = ((q : ℝ) - (z : ℝ) * (z : ℝ) / ((2 : ℝ) ^ 28)) * ((2 : ℝ) ^ 28) := by
          rw [sub_mul, hdiv_eq]
    exact (le_of_mul_le_mul_right hgoal hpos28)
  ·
    have h_mul : (q : ℝ) * ((2 : ℝ) ^ 28) - (z : ℝ) * (z : ℝ) ≤ ((2 : ℝ) ^ 27) := by
      linarith
    have hhalf : (1/2 : ℝ) * ((2 : ℝ) ^ 28) = ((2 : ℝ) ^ 27) := by
      calc
        (1/2 : ℝ) * ((2 : ℝ) ^ 28) = (1/2 : ℝ) * (2 * (2 : ℝ) ^ 27) := by rw [pow_succ']
        _ = ((1/2 : ℝ) * 2) * (2 : ℝ) ^ 27 := by rw [mul_assoc]
        _ = 1 * (2 : ℝ) ^ 27 := by rw [show ((1/2 : ℝ) * 2) = (1 : ℝ) by ring]
        _ = (2 : ℝ) ^ 27 := by simp
    have hgoal : ((q : ℝ) - (z : ℝ) * (z : ℝ) / ((2 : ℝ) ^ 28)) * ((2 : ℝ) ^ 28) ≤ (1/2 : ℝ) * ((2 : ℝ) ^ 28) := by
      calc
        ((q : ℝ) - (z : ℝ) * (z : ℝ) / ((2 : ℝ) ^ 28)) * ((2 : ℝ) ^ 28) =
            (q : ℝ) * ((2 : ℝ) ^ 28) - ((z : ℝ) * (z : ℝ) / ((2 : ℝ) ^ 28)) * ((2 : ℝ) ^ 28) := by rw [sub_mul]
        _ = (q : ℝ) * ((2 : ℝ) ^ 28) - (z : ℝ) * (z : ℝ) := by rw [hdiv_eq]
        _ ≤ ((2 : ℝ) ^ 27) := h_mul
        _ = (1/2 : ℝ) * ((2 : ℝ) ^ 28) := by rw [hhalf]
    exact (le_of_mul_le_mul_right hgoal hpos28)

theorem p4_err (z2 : ℕ) (t2 : ℝ) (ht0 : 0 ≤ t2) (ht : t2 ≤ 0.6169 * 2 ^ 28) (h2 : |(z2 : ℝ) - t2| ≤ 1 / 2) :
    |(p4 z2 : ℝ) - t2 ^ 2 / 2 ^ 28| ≤ 5 / 2 := by
  have hm := rshN_err z2 2 (by norm_num)
  have hp := rshN_err (z2 * rshN z2 2) 26 (by norm_num)
  have hp4 : p4 z2 = rshN (z2 * rshN z2 2) 26 := rfl
  rw [hp4]
  push_cast at hp
  set z : ℝ := (z2 : ℝ) with hz
  set M : ℝ := ((rshN z2 2 : ℕ) : ℝ) with hM
  set P : ℝ := ((rshN (z2 * rshN z2 2) 26 : ℕ) : ℝ) with hP
  have hz0 : 0 ≤ z := Nat.cast_nonneg _
  rw [abs_le] at hm hp h2
  have hA : |z * (4 * M - z)| ≤ z * 2 := by
    rw [abs_mul, abs_of_nonneg hz0]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩) hz0
  have hB : |(z - t2) * (z + t2)| ≤ 1 / 2 * (z + t2) := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ z + t2)]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr h2) (by linarith)
  rw [abs_le] at hA hB
  rw [abs_le]
  constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2, hp.1, hp.2, h2.1, h2.2]

namespace H_p6_err

lemma rshN_bound (x s : ℕ) (hs : s ≥ 1) : |((rshN x s : ℕ) : ℝ) - ((x : ℕ) : ℝ) / ((2 : ℝ) ^ s)| ≤ 1/2 := by
  have hpos : 0 < 2 ^ s := pow_pos (by norm_num) s
  have hposR : ((2 ^ s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne.symm
  have hdiv := Nat.div_add_mod (x + 2 ^ (s - 1)) (2 ^ s)
  have hmod := Nat.mod_lt (x + 2 ^ (s - 1)) hpos
  have hdivR : ((2 ^ s : ℕ) : ℝ) * (((rshN x s : ℕ) : ℕ) : ℝ) + (((x + 2 ^ (s - 1)) % (2 ^ s) : ℕ) : ℝ) = ((x + 2 ^ (s - 1) : ℕ) : ℝ) := by
    simpa [rshN, add_comm] using congrArg (fun n : ℕ => (n : ℝ)) hdiv
  have hmodR_lt : (((x + 2 ^ (s - 1)) % (2 ^ s) : ℕ) : ℝ) < ((2 ^ s : ℕ) : ℝ) := by
    exact_mod_cast hmod
  have hmodR_nonneg : 0 ≤ (((x + 2 ^ (s - 1)) % (2 ^ s) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h_eq : ((rshN x s : ℕ) : ℝ) = ((x + 2 ^ (s - 1) : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) - (((x + 2 ^ (s - 1)) % (2 ^ s) : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) := by
    field_simp [hposR]
    nlinarith
  rw [h_eq]
  have h_split : ((x + 2 ^ (s - 1) : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) = ((x : ℕ) : ℝ) / ((2 : ℝ) ^ s) + 1/2 := by
    push_cast
    have hp : (2 : ℝ) ^ (s - 1) * 2 = (2 : ℝ) ^ s := by
      calc
        (2 : ℝ) ^ (s - 1) * 2 = (2 : ℝ) ^ (s - 1) * (2 : ℝ) ^ 1 := by norm_num
        _ = (2 : ℝ) ^ ((s - 1) + 1) := by rw [pow_add]
        _ = (2 : ℝ) ^ s := by rw [Nat.sub_add_cancel hs]
    field_simp [show (2 : ℝ) ^ s ≠ 0 from by positivity]
    nlinarith
  rw [h_split]
  have h_simp : ((x : ℕ) : ℝ) / ((2 : ℝ) ^ s) + 1/2 - (((x + 2 ^ (s - 1)) % (2 ^ s) : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) - ((x : ℕ) : ℝ) / ((2 : ℝ) ^ s) =
      1/2 - (((x + 2 ^ (s - 1)) % (2 ^ s) : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) := by
    ring
  rw [h_simp]
  have h_ratio_nonneg : 0 ≤ (((x + 2 ^ (s - 1)) % (2 ^ s) : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) :=
    div_nonneg hmodR_nonneg (by exact_mod_cast hpos.le)
  have h_ratio_lt_one : (((x + 2 ^ (s - 1)) % (2 ^ s) : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) < 1 :=
    (div_lt_one (by exact_mod_cast hpos)).mpr hmodR_lt
  rw [abs_le]
  constructor
  · have htemp : (((x + 2 ^ (s - 1)) % (2 ^ s) : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) ≤ 1 := le_of_lt h_ratio_lt_one
    linarith
  · linarith
end H_p6_err

open H_p6_err in
theorem p6_err (z2 z4 : ℕ) (t2 t4 : ℝ) (ht2 : 0 ≤ t2 ∧ t2 ≤ 0.6169 * 2 ^ 28) (ht4 : 0 ≤ t4 ∧ t4 ≤ 0.3806 * 2 ^ 28)
    (h2 : |(z2 : ℝ) - t2| ≤ 1 / 2) (h4 : |(z4 : ℝ) - t4| ≤ 5 / 2) :
    |(p6 z2 z4 : ℝ) - t4 * t2 / 2 ^ 28| ≤ 52 := by
  rcases ht2 with ⟨ht2_nonneg, ht2_le⟩
  rcases ht4 with ⟨ht4_nonneg, ht4_le⟩
  set m := rshN z2 8 with hm_def
  have hm_bound : |(m : ℝ) - (z2 : ℝ) / 256| ≤ 1/2 := by
    have : (256 : ℝ) = ((2 : ℝ) ^ 8) := by norm_num
    rw [this]
    exact rshN_bound z2 8 (by norm_num)
  have hp6_bound : |(p6 z2 z4 : ℝ) - (z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20)| ≤ 1/2 := by
    have hp6_eq : (p6 z2 z4 : ℝ) = (rshN (z4 * m) 20 : ℝ) := by
      simp [p6, hm_def]
    rw [hp6_eq]
    have h_eq : (z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20) = ((z4 * m : ℕ) : ℝ) / ((2 : ℝ) ^ 20) := by
      push_cast
      ring
    rw [h_eq]
    exact rshN_bound (z4 * m) 20 (by norm_num)

  have abs_add_two (a b : ℝ) : |a + b| ≤ |a| + |b| := by
    have h := abs_add_three a b 0
    simpa [add_zero, abs_zero] using h

  have h_tri : |(p6 z2 z4 : ℝ) - t4 * t2 / ((2 : ℝ) ^ 28)| ≤
      |(p6 z2 z4 : ℝ) - (z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20)| +
      |(z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20) - (z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28)| +
      |(z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28) - t4 * t2 / ((2 : ℝ) ^ 28)| := by
    have h_eq : (p6 z2 z4 : ℝ) - t4 * t2 / ((2 : ℝ) ^ 28) =
        ((p6 z2 z4 : ℝ) - (z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20)) +
        ((z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20) - (z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28)) +
        ((z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28) - t4 * t2 / ((2 : ℝ) ^ 28)) := by
      ring
    rw [h_eq]
    set a := (p6 z2 z4 : ℝ) - (z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20) with ha
    set b := (z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20) - (z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28) with hb
    set c := (z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28) - t4 * t2 / ((2 : ℝ) ^ 28) with hc
    have h := abs_add_three a b c
    simpa [add_assoc] using h

  have h_term2 : |(z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20) - (z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28)| ≤ (z4 : ℝ) / ((2 : ℝ) ^ 21) := by
    have h_eq : (z4 : ℝ) * (m : ℝ) / ((2 : ℝ) ^ 20) - (z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28) =
        (z4 : ℝ) * ((m : ℝ) - (z2 : ℝ) / 256) / ((2 : ℝ) ^ 20) := by
      ring
    rw [h_eq]
    have hz4_nonneg : 0 ≤ (z4 : ℝ) := Nat.cast_nonneg _
    have h_denom_pos : 0 < (2 : ℝ) ^ 20 := by positivity
    calc
      |(z4 : ℝ) * ((m : ℝ) - (z2 : ℝ) / 256) / ((2 : ℝ) ^ 20)|
          = |(z4 : ℝ)| * |(m : ℝ) - (z2 : ℝ) / 256| / |((2 : ℝ) ^ 20)| := by rw [abs_div, abs_mul]
      _ = (z4 : ℝ) * |(m : ℝ) - (z2 : ℝ) / 256| / ((2 : ℝ) ^ 20) := by
        rw [abs_of_nonneg hz4_nonneg, abs_of_pos h_denom_pos]
      _ ≤ (z4 : ℝ) * (1/2) / ((2 : ℝ) ^ 20) := by
        refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm_bound hz4_nonneg) (by positivity))
      _ = (z4 : ℝ) / ((2 : ℝ) ^ 21) := by ring

  have h_term3 : |(z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28) - t4 * t2 / ((2 : ℝ) ^ 28)| ≤
      0.1903 + 1.25 / ((2 : ℝ) ^ 28) + 1.54225 := by
    have h_eq : (z4 : ℝ) * (z2 : ℝ) / ((2 : ℝ) ^ 28) - t4 * t2 / ((2 : ℝ) ^ 28) =
        ((z4 : ℝ) * (z2 : ℝ) - t4 * t2) / ((2 : ℝ) ^ 28) := by ring
    rw [h_eq]
    have h_denom_pos : 0 < (2 : ℝ) ^ 28 := by positivity
    rw [abs_div, abs_of_pos h_denom_pos]
    have h_num : |(z4 : ℝ) * (z2 : ℝ) - t4 * t2| ≤ 0.1903 * (2 : ℝ) ^ 28 + 1.25 + 1.54225 * (2 : ℝ) ^ 28 := by
      have h_tri : |(z4 : ℝ) * (z2 : ℝ) - t4 * t2| ≤ (z4 : ℝ) * |(z2 : ℝ) - t2| + t2 * |(z4 : ℝ) - t4| := by
        calc
          |(z4 : ℝ) * (z2 : ℝ) - t4 * t2| = |(z4 : ℝ) * ((z2 : ℝ) - t2) + t2 * ((z4 : ℝ) - t4)| := by ring_nf
          _ ≤ |(z4 : ℝ) * ((z2 : ℝ) - t2)| + |t2 * ((z4 : ℝ) - t4)| := abs_add_two _ _
          _ = |(z4 : ℝ)| * |(z2 : ℝ) - t2| + |t2| * |(z4 : ℝ) - t4| := by rw [abs_mul, abs_mul]
          _ = (z4 : ℝ) * |(z2 : ℝ) - t2| + t2 * |(z4 : ℝ) - t4| := by
            rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg ht2_nonneg]
      have hz4_bound : (z4 : ℝ) ≤ 0.3806 * (2 : ℝ) ^ 28 + 5/2 := by
        have : (z4 : ℝ) - t4 ≤ 5/2 := by
          have h4_abs := abs_le.mp h4
          linarith
        linarith
      have h_bound : (z4 : ℝ) * |(z2 : ℝ) - t2| + t2 * |(z4 : ℝ) - t4| ≤
          0.1903 * (2 : ℝ) ^ 28 + 1.25 + 1.54225 * (2 : ℝ) ^ 28 := by
        nlinarith
      linarith
    have h_div : |(z4 : ℝ) * (z2 : ℝ) - t4 * t2| / ((2 : ℝ) ^ 28) ≤
        (0.1903 * (2 : ℝ) ^ 28 + 1.25 + 1.54225 * (2 : ℝ) ^ 28) / ((2 : ℝ) ^ 28) :=
      (div_le_div_of_nonneg_right h_num (by positivity))
    have h_simp : (0.1903 * (2 : ℝ) ^ 28 + 1.25 + 1.54225 * (2 : ℝ) ^ 28) / ((2 : ℝ) ^ 28) =
        0.1903 + 1.25 / ((2 : ℝ) ^ 28) + 1.54225 := by
      field_simp [h_denom_pos.ne.symm]
    rw [h_simp] at h_div
    exact h_div

  have h_sum : |(p6 z2 z4 : ℝ) - t4 * t2 / ((2 : ℝ) ^ 28)| ≤
      1/2 + (z4 : ℝ) / ((2 : ℝ) ^ 21) + (0.1903 + 1.25 / ((2 : ℝ) ^ 28) + 1.54225) := by
    apply le_trans h_tri
    apply add_le_add (add_le_add hp6_bound h_term2) h_term3

  have h_final : 1/2 + (z4 : ℝ) / ((2 : ℝ) ^ 21) + (0.1903 + 1.25 / ((2 : ℝ) ^ 28) + 1.54225) ≤ 52 := by
    have hz4_bound : (z4 : ℝ) ≤ 0.3806 * (2 : ℝ) ^ 28 + 5/2 := by
      have : (z4 : ℝ) - t4 ≤ 5/2 := by
        have h4_abs := abs_le.mp h4
        linarith
      linarith
    nlinarith
  linarith

set_option maxRecDepth 200000 in
theorem p8_err (z4 : ℕ) (t4 : ℝ) (ht4 : 0 ≤ t4 ∧ t4 ≤ 0.3806 * 2 ^ 28) (h4 : |(z4 : ℝ) - t4| ≤ 5 / 2) :
    |(p8 z4 : ℝ) - t4 ^ 2 / 2 ^ 28| ≤ 3200 := by
  set m := rshN z4 14 with hm
  have hz4_nonneg : 0 ≤ (z4 : ℝ) := Nat.cast_nonneg _
  have ht4_nonneg : 0 ≤ t4 := ht4.1
  have ht4_le : t4 ≤ 0.3806 * ((2 : ℝ) ^ 28) := ht4.2
  have hz4_sub_t4 : |(z4 : ℝ) - t4| ≤ 5 / 2 := h4
  have hz4_le : (z4 : ℝ) ≤ t4 + 5/2 := by
    have := abs_le.mp hz4_sub_t4
    linarith
  have hz4_le' : (z4 : ℝ) ≤ 0.3806 * ((2 : ℝ) ^ 28) + 5/2 := by
    linarith
  have hpos14 : 0 < (2 : ℕ) ^ 14 := by norm_num

  have hm_abs_bound : |(m : ℝ) - (z4 : ℝ) / ((2 : ℝ) ^ 14)| ≤ 1/2 := by
    have hm_eq : m = (z4 + 2 ^ 13) / 2 ^ 14 := rfl
    have h_eq_nat := Nat.div_add_mod (z4 + 2 ^ 13) (2 ^ 14)
    have h_mod_lt : (z4 + 2 ^ 13) % (2 ^ 14) < 2 ^ 14 := Nat.mod_lt (z4 + 2 ^ 13) hpos14
    rw [← hm_eq] at h_eq_nat

    have htemp := congrArg (fun x : ℕ => (x : ℝ)) h_eq_nat

    have h_eq_nat' : ((2 ^ 14 : ℝ) * (m : ℝ) + (Nat.cast ((z4 + 2 ^ 13) % (2 ^ 14)) : ℝ)) = ((z4 : ℝ) + (2 ^ 13 : ℝ)) := by
      norm_num at htemp ⊢
      exact htemp
    have h_mul_le : (2 ^ 14 : ℝ) * (m : ℝ) ≤ (z4 : ℝ) + (2 ^ 13 : ℝ) := by
      have h_nonneg_mod : 0 ≤ (Nat.cast ((z4 + 2 ^ 13) % (2 ^ 14)) : ℝ) := Nat.cast_nonneg _
      linarith
    have h_mod_lt' : (Nat.cast ((z4 + 2 ^ 13) % (2 ^ 14)) : ℝ) < ((2 : ℝ) ^ 14) := by
      exact_mod_cast h_mod_lt
    have h_lt : (z4 : ℝ) + (2 ^ 13 : ℝ) < (2 ^ 14 : ℝ) * ((m : ℝ) + 1) := by
      linarith
    have h_le : (m : ℝ) ≤ (z4 : ℝ) / ((2 : ℝ) ^ 14) + 1/2 := by
      linarith
    have h_lt' : (z4 : ℝ) / ((2 : ℝ) ^ 14) - (m : ℝ) < 1/2 := by
      linarith
    apply abs_le.mpr
    constructor
    · linarith
    · linarith

  have hp8_abs_bound : |(p8 z4 : ℝ) - ((z4 : ℝ) * (m : ℝ)) / ((2 : ℝ) ^ 14)| ≤ 1/2 := by
    have hp8_eq' : (p8 z4 : ℕ) = (z4 * m + 2 ^ 13) / 2 ^ 14 := rfl
    have h_eq_nat := Nat.div_add_mod (z4 * m + 2 ^ 13) (2 ^ 14)
    have h_mod_lt : (z4 * m + 2 ^ 13) % (2 ^ 14) < 2 ^ 14 := Nat.mod_lt (z4 * m + 2 ^ 13) hpos14
    rw [← hp8_eq'] at h_eq_nat

    have htemp := congrArg (fun x : ℕ => (x : ℝ)) h_eq_nat
    have h_eq_nat' : ((2 ^ 14 : ℝ) * ((p8 z4 : ℕ) : ℝ) + (Nat.cast ((z4 * m + 2 ^ 13) % (2 ^ 14)) : ℝ)) = ((z4 : ℝ) * (m : ℝ) + (2 ^ 13 : ℝ)) := by
      norm_num at htemp ⊢
      exact htemp
    have h_mul_le : (2 ^ 14 : ℝ) * ((p8 z4 : ℕ) : ℝ) ≤ (z4 : ℝ) * (m : ℝ) + (2 ^ 13 : ℝ) := by
      have h_nonneg_mod : 0 ≤ (Nat.cast ((z4 * m + 2 ^ 13) % (2 ^ 14)) : ℝ) := Nat.cast_nonneg _
      linarith
    have h_mod_lt' : (Nat.cast ((z4 * m + 2 ^ 13) % (2 ^ 14)) : ℝ) < ((2 : ℝ) ^ 14) := by
      exact_mod_cast h_mod_lt
    have h_lt : (z4 : ℝ) * (m : ℝ) + (2 ^ 13 : ℝ) < (2 ^ 14 : ℝ) * (((p8 z4 : ℕ) : ℝ) + 1) := by
      linarith
    have h_le : (p8 z4 : ℝ) ≤ ((z4 : ℝ) * (m : ℝ)) / ((2 : ℝ) ^ 14) + 1/2 := by
      linarith
    have h_lt' : ((z4 : ℝ) * (m : ℝ)) / ((2 : ℝ) ^ 14) - (p8 z4 : ℝ) < 1/2 := by
      linarith
    apply abs_le.mpr
    constructor
    · linarith
    · linarith

  have h_decomp : ((z4 : ℝ) * (m : ℝ)) / ((2 : ℝ) ^ 14) = (z4 : ℝ) ^ 2 / ((2 : ℝ) ^ 28) + (z4 : ℝ) * ((m : ℝ) - (z4 : ℝ) / ((2 : ℝ) ^ 14)) / ((2 : ℝ) ^ 14) := by
    ring
  have h_main : |(p8 z4 : ℝ) - (z4 : ℝ) ^ 2 / ((2 : ℝ) ^ 28)| ≤ 1/2 + (z4 : ℝ) / ((2 : ℝ) ^ 15) := by
    have h_diff : (p8 z4 : ℝ) - (z4 : ℝ) ^ 2 / ((2 : ℝ) ^ 28) =
        ((p8 z4 : ℝ) - ((z4 : ℝ) * (m : ℝ)) / ((2 : ℝ) ^ 14)) + (z4 : ℝ) * ((m : ℝ) - (z4 : ℝ) / ((2 : ℝ) ^ 14)) / ((2 : ℝ) ^ 14) := by
      rw [h_decomp]; ring
    rw [h_diff]
    have h_tri : |((p8 z4 : ℝ) - ((z4 : ℝ) * (m : ℝ)) / ((2 : ℝ) ^ 14)) + (z4 : ℝ) * ((m : ℝ) - (z4 : ℝ) / ((2 : ℝ) ^ 14)) / ((2 : ℝ) ^ 14)| ≤
        |(p8 z4 : ℝ) - ((z4 : ℝ) * (m : ℝ)) / ((2 : ℝ) ^ 14)| + |(z4 : ℝ) * ((m : ℝ) - (z4 : ℝ) / ((2 : ℝ) ^ 14)) / ((2 : ℝ) ^ 14)| :=
      abs_add_le _ _
    have h1 : |(p8 z4 : ℝ) - ((z4 : ℝ) * (m : ℝ)) / ((2 : ℝ) ^ 14)| ≤ 1/2 := hp8_abs_bound
    have h2 : |(z4 : ℝ) * ((m : ℝ) - (z4 : ℝ) / ((2 : ℝ) ^ 14)) / ((2 : ℝ) ^ 14)| ≤ (z4 : ℝ) / ((2 : ℝ) ^ 15) := by
      calc
        |(z4 : ℝ) * ((m : ℝ) - (z4 : ℝ) / ((2 : ℝ) ^ 14)) / ((2 : ℝ) ^ 14)|
            = |(z4 : ℝ)| * |(m : ℝ) - (z4 : ℝ) / ((2 : ℝ) ^ 14)| / |((2 : ℝ) ^ 14)| := by simp [abs_mul, abs_div]
        _ = (z4 : ℝ) * |(m : ℝ) - (z4 : ℝ) / ((2 : ℝ) ^ 14)| / ((2 : ℝ) ^ 14) := by
          have hpos : 0 ≤ ((2 : ℝ) ^ 14) := by norm_num
          simp [abs_of_nonneg hpos]
        _ ≤ (z4 : ℝ) * (1/2) / ((2 : ℝ) ^ 14) := by
          apply (div_le_div_of_nonneg_right ?_ (by norm_num : 0 ≤ ((2 : ℝ) ^ 14)))
          apply (mul_le_mul_of_nonneg_left hm_abs_bound hz4_nonneg)
        _ = (z4 : ℝ) / ((2 : ℝ) ^ 15) := by ring
    linarith

  have h_sq_bound : |(z4 : ℝ) ^ 2 / ((2 : ℝ) ^ 28) - t4 ^ 2 / ((2 : ℝ) ^ 28)| ≤ 5/2 * ((z4 : ℝ) + t4) / ((2 : ℝ) ^ 28) := by
    have h_eq : (z4 : ℝ) ^ 2 / ((2 : ℝ) ^ 28) - t4 ^ 2 / ((2 : ℝ) ^ 28) = ((z4 : ℝ) - t4) * ((z4 : ℝ) + t4) / ((2 : ℝ) ^ 28) := by
      ring
    rw [h_eq]
    rw [abs_div, abs_mul]

    have h_sum_nonneg : 0 ≤ (z4 : ℝ) + t4 := by linarith
    have h_abs_sum : |(z4 : ℝ) + t4| = (z4 : ℝ) + t4 := abs_of_nonneg h_sum_nonneg
    rw [h_abs_sum]
    have h_abs_sub : |(z4 : ℝ) - t4| ≤ 5/2 := h4
    have h_abs_denom : |((2 : ℝ) ^ 28)| = ((2 : ℝ) ^ 28) := abs_of_nonneg (by norm_num)
    rw [h_abs_denom]
    have h_num : |(z4 : ℝ) - t4| * ((z4 : ℝ) + t4) ≤ 5/2 * ((z4 : ℝ) + t4) := by
      calc
        |(z4 : ℝ) - t4| * ((z4 : ℝ) + t4) ≤ (5/2) * ((z4 : ℝ) + t4) := by
          apply mul_le_mul_of_nonneg_right h_abs_sub h_sum_nonneg
        _ = 5/2 * ((z4 : ℝ) + t4) := rfl
    exact div_le_div_of_nonneg_right h_num (by norm_num)

  have h_total : |(p8 z4 : ℝ) - t4 ^ 2 / ((2 : ℝ) ^ 28)| ≤ (1/2 + (z4 : ℝ) / ((2 : ℝ) ^ 15)) + (5/2 * ((z4 : ℝ) + t4) / ((2 : ℝ) ^ 28)) := by
    have h := calc
      |(p8 z4 : ℝ) - t4 ^ 2 / ((2 : ℝ) ^ 28)| ≤ |(p8 z4 : ℝ) - (z4 : ℝ) ^ 2 / ((2 : ℝ) ^ 28)| + |(z4 : ℝ) ^ 2 / ((2 : ℝ) ^ 28) - t4 ^ 2 / ((2 : ℝ) ^ 28)| :=
        abs_sub_le _ _ _
      _ ≤ (1/2 + (z4 : ℝ) / ((2 : ℝ) ^ 15)) + (5/2 * ((z4 : ℝ) + t4) / ((2 : ℝ) ^ 28)) :=
        add_le_add h_main h_sq_bound
    exact h

  have h_final : (1/2 + (z4 : ℝ) / ((2 : ℝ) ^ 15)) + (5/2 * ((z4 : ℝ) + t4) / ((2 : ℝ) ^ 28)) ≤ 3200 := by
    have hz4_bound : (z4 : ℝ) / ((2 : ℝ) ^ 15) ≤ (0.3806 * ((2 : ℝ) ^ 28) + 5/2) / ((2 : ℝ) ^ 15) := by
      apply div_le_div_of_nonneg_right hz4_le'
      norm_num
    have h_sum_bound : (z4 : ℝ) + t4 ≤ 2 * (0.3806 * ((2 : ℝ) ^ 28)) + 5/2 := by
      linarith
    have h_sq_term_bound : 5/2 * ((z4 : ℝ) + t4) / ((2 : ℝ) ^ 28) ≤ 5/2 * (2 * (0.3806 * ((2 : ℝ) ^ 28)) + 5/2) / ((2 : ℝ) ^ 28) := by
      apply div_le_div_of_nonneg_right ?_ (by norm_num)
      gcongr
    have h_num : (1/2 : ℝ) + ((0.3806 * ((2 : ℝ) ^ 28) + 5/2) / ((2 : ℝ) ^ 15)) +
        (5/2 * (2 * (0.3806 * ((2 : ℝ) ^ 28)) + 5/2) / ((2 : ℝ) ^ 28)) ≤ 3200 := by
      norm_num
    linarith
  linarith

namespace H_p10_err

lemma rshN_bound (x s : ℕ) (hs : 1 ≤ s) : |((rshN x s : ℕ) : ℝ) - ((x : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ)| ≤ 1/2 := by
  have hpos_pow : 0 < 2 ^ s := Nat.pow_pos (a := 2) (n := s) (by norm_num : 0 < 2)
  set q := rshN x s with hq_def
  set r := (x + 2 ^ (s - 1)) % (2 ^ s) with hr_def
  have hdiv : (2 ^ s) * q + r = x + 2 ^ (s - 1) := by
    rw [hq_def, hr_def]
    dsimp [rshN]
    rw [Nat.div_add_mod (x + 2 ^ (s - 1)) (2 ^ s)]
  have hr_lt : r < 2 ^ s := Nat.mod_lt (x + 2 ^ (s - 1)) hpos_pow
  have hpos_pow' : (0 : ℝ) < (2 ^ s : ℕ) := by exact_mod_cast hpos_pow
  have hq_eq : (q : ℝ) * ((2 ^ s : ℕ) : ℝ) = (x : ℝ) + ((2 : ℝ) ^ (s - 1)) - (r : ℝ) := by
    have h := congrArg (fun t : ℕ => (t : ℝ)) hdiv

    have h' := h
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at h'

    calc
      (q : ℝ) * ((2 ^ s : ℕ) : ℝ) = (q : ℝ) * ((2 : ℝ) ^ s) := by simp
      _ = ((2 : ℝ) ^ s) * (q : ℝ) := by ring
      _ = ((x : ℝ) + (2 : ℝ) ^ (s - 1)) - (r : ℝ) := by

        have h'' : (2 : ℝ) ^ s * (q : ℝ) + (r : ℝ) = (x : ℝ) + (2 : ℝ) ^ (s - 1) := by
          simpa [Nat.cast_pow] using h'
        linarith
      _ = (x : ℝ) + ((2 : ℝ) ^ (s - 1)) - (r : ℝ) := rfl
  have h_diff : (q : ℝ) - ((x : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) = (1/2 : ℝ) - (r : ℝ) / ((2 ^ s : ℕ) : ℝ) := by

    calc
      (q : ℝ) - ((x : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ)
          = (((x : ℝ) + ((2 : ℝ) ^ (s - 1)) - (r : ℝ)) / ((2 ^ s : ℕ) : ℝ)) - ((x : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) := by
        field_simp [hpos_pow'.ne.symm]
        nlinarith
      _ = (((2 : ℝ) ^ (s - 1)) - (r : ℝ)) / ((2 ^ s : ℕ) : ℝ) := by ring
      _ = ((2 : ℝ) ^ (s - 1)) / ((2 ^ s : ℕ) : ℝ) - (r : ℝ) / ((2 ^ s : ℕ) : ℝ) := by ring
      _ = (1/2 : ℝ) - (r : ℝ) / ((2 ^ s : ℕ) : ℝ) := by
        have h_pow_eq : ((2 : ℝ) ^ (s - 1)) / ((2 ^ s : ℕ) : ℝ) = (1/2 : ℝ) := by

          have h_pow_succ : (2 : ℝ) ^ s = (2 : ℝ) * (2 : ℝ) ^ (s - 1) := by
            calc
              (2 : ℝ) ^ s = (2 : ℝ) ^ ((s - 1) + 1) := by rw [Nat.sub_add_cancel hs]
              _ = (2 : ℝ) ^ (s - 1) * (2 : ℝ) ^ 1 := by rw [pow_add]
              _ = (2 : ℝ) ^ (s - 1) * 2 := by norm_num
              _ = (2 : ℝ) * (2 : ℝ) ^ (s - 1) := by ring
          calc
            ((2 : ℝ) ^ (s - 1)) / ((2 ^ s : ℕ) : ℝ) = ((2 : ℝ) ^ (s - 1)) / ((2 : ℝ) ^ s) := by simp
            _ = ((2 : ℝ) ^ (s - 1)) / ((2 : ℝ) * (2 : ℝ) ^ (s - 1)) := by rw [h_pow_succ]
            _ = 1 / (2 : ℝ) := by field_simp [show (2 : ℝ) ^ (s - 1) ≠ 0 from pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
            _ = (1/2 : ℝ) := by norm_num
        rw [h_pow_eq]
  have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast Nat.zero_le _
  have hr_lt' : (r : ℝ) < (2 ^ s : ℕ) := by exact_mod_cast hr_lt
  have h_bound : |(q : ℝ) - ((x : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ)| ≤ 1/2 := by
    rw [h_diff]
    have hdiv_nonneg : 0 ≤ (r : ℝ) / ((2 ^ s : ℕ) : ℝ) := div_nonneg hr_nonneg (by positivity)
    have hdiv_lt_one : (r : ℝ) / ((2 ^ s : ℕ) : ℝ) < 1 := by
      refine (div_lt_one ?_).mpr hr_lt'
      exact_mod_cast hpos_pow
    have h_low : -(1/2 : ℝ) ≤ (1/2 : ℝ) - (r : ℝ) / ((2 ^ s : ℕ) : ℝ) := by
      linarith
    have h_high : (1/2 : ℝ) - (r : ℝ) / ((2 ^ s : ℕ) : ℝ) ≤ 1/2 := by
      linarith
    exact abs_le.mpr ⟨h_low, h_high⟩
  simpa [hq_def] using h_bound
end H_p10_err

open H_p10_err in
theorem p10_err (z2 z8 : ℕ) (t2 t8 : ℝ) (ht2 : 0 ≤ t2 ∧ t2 ≤ 0.6169 * 2 ^ 28) (ht8 : 0 ≤ t8 ∧ t8 ≤ 0.1448 * 2 ^ 28)
    (h2 : |(z2 : ℝ) - t2| ≤ 1 / 2) (h8 : |(z8 : ℝ) - t8| ≤ 3200) :
    |(p10 z2 z8 : ℝ) - t8 * t2 / 2 ^ 28| ≤ 310000 := by
  rcases ht2 with ⟨ht2_nonneg, ht2_le⟩
  rcases ht8 with ⟨ht8_nonneg, ht8_le⟩
  set m := rshN z2 22 with hm_def
  have hm_bound : |(m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ)| ≤ 1/2 := by
    rw [hm_def]
    exact rshN_bound z2 22 (by norm_num : 1 ≤ 22)
  have hp10_bound : |((p10 z2 z8 : ℕ) : ℝ) - ((z8 * m : ℕ) : ℝ) / ((2 ^ 6 : ℕ) : ℝ)| ≤ 1/2 := by
    dsimp [p10]
    rw [hm_def]
    exact rshN_bound (z8 * m) 6 (by norm_num : 1 ≤ 6)

  have h_tri : |((p10 z2 z8 : ℕ) : ℝ) - t8 * t2 / ((2 ^ 28 : ℕ) : ℝ)| ≤
      |((p10 z2 z8 : ℕ) : ℝ) - ((z8 * m : ℕ) : ℝ) / ((2 ^ 6 : ℕ) : ℝ)| +
      |((z8 * m : ℕ) : ℝ) / ((2 ^ 6 : ℕ) : ℝ) - t8 * t2 / ((2 ^ 28 : ℕ) : ℝ)| :=
    abs_sub_le _ _ _

  have h_main : |((p10 z2 z8 : ℕ) : ℝ) - t8 * t2 / ((2 ^ 28 : ℕ) : ℝ)| ≤
      1/2 + |((z8 * m : ℕ) : ℝ) / ((2 ^ 6 : ℕ) : ℝ) - t8 * t2 / ((2 ^ 28 : ℕ) : ℝ)| := by
    linarith

  have h2_6 : ((2 ^ 6 : ℕ) : ℝ) = (64 : ℝ) := by norm_num
  have h2_22 : ((2 ^ 22 : ℕ) : ℝ) = (4194304 : ℝ) := by norm_num
  have h2_28 : ((2 ^ 28 : ℕ) : ℝ) = (268435456 : ℝ) := by norm_num
  have h_identity : ((z8 * m : ℕ) : ℝ) / ((2 ^ 6 : ℕ) : ℝ) =
      ((z8 : ℝ) * (z2 : ℝ)) / ((2 ^ 28 : ℕ) : ℝ) +
      ((z8 : ℝ) * ((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))) / ((2 ^ 6 : ℕ) : ℝ) := by
    rw [h2_6, h2_22, h2_28]
    field_simp [show (64 : ℝ) ≠ 0 from by norm_num, show (4194304 : ℝ) ≠ 0 from by norm_num,
               show (268435456 : ℝ) ≠ 0 from by norm_num]
    ring_nf
    simp [Nat.cast_mul]

  have hz8_nonneg : 0 ≤ (z8 : ℝ) := by exact_mod_cast Nat.zero_le _
  have hz2_nonneg : 0 ≤ (z2 : ℝ) := by exact_mod_cast Nat.zero_le _
  have hz8_abs_le : |(z8 : ℝ)| ≤ t8 + 3200 := by
    have h := abs_add_le ((z8 : ℝ) - t8) t8
    have h_sub_add : ((z8 : ℝ) - t8) + t8 = (z8 : ℝ) := by ring
    rw [h_sub_add] at h
    have ht8_abs : |t8| = t8 := abs_of_nonneg ht8_nonneg
    rw [ht8_abs] at h
    have hz8_sub_t8 : |(z8 : ℝ) - t8| ≤ 3200 := h8
    linarith
  have h_prod_bound : |((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| ≤
      |(z8 : ℝ)| * (1/2) + (0.6169 * ((2 ^ 28 : ℕ) : ℝ)) * 3200 := by
    calc
      |((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| = |(((z8 : ℝ) * (z2 : ℝ)) - ((z8 : ℝ) * t2)) + (((z8 : ℝ) * t2) - t8 * t2)| := by ring
      _ ≤ |((z8 : ℝ) * (z2 : ℝ)) - ((z8 : ℝ) * t2)| + |((z8 : ℝ) * t2) - t8 * t2| := abs_add_le _ _
      _ = |(z8 : ℝ) * ((z2 : ℝ) - t2)| + |t2 * ((z8 : ℝ) - t8)| := by ring
      _ = |(z8 : ℝ)| * |(z2 : ℝ) - t2| + |t2| * |(z8 : ℝ) - t8| := by rw [abs_mul, abs_mul]
      _ ≤ |(z8 : ℝ)| * (1/2) + |t2| * 3200 := by
        have ht2_abs : |t2| = t2 := abs_of_nonneg ht2_nonneg
        rw [ht2_abs]

        have h_abs_nonneg : 0 ≤ |(z8 : ℝ)| := abs_nonneg _
        have h_mul : |(z8 : ℝ)| * |(z2 : ℝ) - t2| ≤ |(z8 : ℝ)| * (1/2) :=
          mul_le_mul_of_nonneg_left h2 h_abs_nonneg
        nlinarith
      _ ≤ |(z8 : ℝ)| * (1/2) + (0.6169 * ((2 ^ 28 : ℕ) : ℝ)) * 3200 := by
        have ht2_abs : |t2| = t2 := abs_of_nonneg ht2_nonneg
        rw [ht2_abs]

        nlinarith

  have h_total : |((p10 z2 z8 : ℕ) : ℝ) - t8 * t2 / ((2 ^ 28 : ℕ) : ℝ)| ≤ 310000 := by

    have h_bound : |((z8 * m : ℕ) : ℝ) / ((2 ^ 6 : ℕ) : ℝ) - t8 * t2 / ((2 ^ 28 : ℕ) : ℝ)| ≤
        |((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| / ((2 ^ 28 : ℕ) : ℝ) + |(z8 : ℝ)| / 128 := by
      rw [h_identity]
      have h_sum : ((z8 : ℝ) * (z2 : ℝ)) / ((2 ^ 28 : ℕ) : ℝ) +
          ((z8 : ℝ) * ((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))) / ((2 ^ 6 : ℕ) : ℝ) -
          t8 * t2 / ((2 ^ 28 : ℕ) : ℝ) =
          (((z8 : ℝ) * (z2 : ℝ)) - t8 * t2) / ((2 ^ 28 : ℕ) : ℝ) +
          ((z8 : ℝ) * ((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))) / ((2 ^ 6 : ℕ) : ℝ) := by
        ring
      rw [h_sum]
      calc
        |(((z8 : ℝ) * (z2 : ℝ)) - t8 * t2) / ((2 ^ 28 : ℕ) : ℝ) +
          ((z8 : ℝ) * ((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))) / ((2 ^ 6 : ℕ) : ℝ)|
        ≤ |(((z8 : ℝ) * (z2 : ℝ)) - t8 * t2) / ((2 ^ 28 : ℕ) : ℝ)| +
          |((z8 : ℝ) * ((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))) / ((2 ^ 6 : ℕ) : ℝ)| :=
          abs_add_le _ _
        _ = |((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| / |((2 ^ 28 : ℕ) : ℝ)| +
          |(z8 : ℝ) * ((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))| / |((2 ^ 6 : ℕ) : ℝ)| := by
          rw [abs_div, abs_div]
        _ = |((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| / ((2 ^ 28 : ℕ) : ℝ) +
          |(z8 : ℝ) * ((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))| / ((2 ^ 6 : ℕ) : ℝ) := by

          rw [abs_of_pos (by norm_num : 0 < ((2 ^ 28 : ℕ) : ℝ)),
            abs_of_pos (by norm_num : 0 < ((2 ^ 6 : ℕ) : ℝ))]
        _ = |((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| / ((2 ^ 28 : ℕ) : ℝ) +
          (|(z8 : ℝ)| * |((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))|) / ((2 ^ 6 : ℕ) : ℝ) := by rw [abs_mul]
        _ ≤ |((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| / ((2 ^ 28 : ℕ) : ℝ) +
          |(z8 : ℝ)| * (|((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))| / ((2 ^ 6 : ℕ) : ℝ)) := by

          rw [mul_div_assoc]
        _ ≤ |((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| / ((2 ^ 28 : ℕ) : ℝ) +
          |(z8 : ℝ)| * ((1/2) / ((2 ^ 6 : ℕ) : ℝ)) := by

          have hm_nonneg : 0 ≤ |(z8 : ℝ)| := abs_nonneg _

          have h_div : |((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))| / ((2 ^ 6 : ℕ) : ℝ) ≤
              (1/2) / ((2 ^ 6 : ℕ) : ℝ) := by

            have hpos : 0 ≤ ((2 ^ 6 : ℕ) : ℝ) := by norm_num
            exact div_le_div_of_nonneg_right hm_bound hpos
          have h_mul : |(z8 : ℝ)| * (|((m : ℝ) - ((z2 : ℕ) : ℝ) / ((2 ^ 22 : ℕ) : ℝ))| / ((2 ^ 6 : ℕ) : ℝ)) ≤
              |(z8 : ℝ)| * ((1/2) / ((2 ^ 6 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left h_div hm_nonneg
          nlinarith
        _ = |((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| / ((2 ^ 28 : ℕ) : ℝ) + |(z8 : ℝ)| / 128 := by
          have : (1/2 : ℝ) / ((2 ^ 6 : ℕ) : ℝ) = (1/128 : ℝ) := by norm_num
          rw [this]
          ring

    have h_all : |((p10 z2 z8 : ℕ) : ℝ) - t8 * t2 / ((2 ^ 28 : ℕ) : ℝ)| ≤
        1/2 + (|((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| / ((2 ^ 28 : ℕ) : ℝ) + |(z8 : ℝ)| / 128) := by
      linarith

    have h_final : 1/2 + (|((z8 : ℝ) * (z2 : ℝ)) - t8 * t2| / ((2 ^ 28 : ℕ) : ℝ) + |(z8 : ℝ)| / 128) ≤ 310000 := by

      nlinarith
    linarith

  simpa [show ((2 : ℝ) ^ 28) = ((2 ^ 28 : ℕ) : ℝ) by norm_num] using h_total

theorem cosP_err (z2 z4 z6 z8 z10 : ℕ) (Z : ℝ) (hZ : 0 ≤ Z ∧ Z ≤ 0.7854)
    (h2 : |(z2 : ℝ) - 2 ^ 28 * Z ^ 2| ≤ 1 / 2) (h4 : |(z4 : ℝ) - 2 ^ 28 * Z ^ 4| ≤ 5 / 2)
    (h6 : |(z6 : ℝ) - 2 ^ 28 * Z ^ 6| ≤ 52) (h8 : |(z8 : ℝ) - 2 ^ 28 * Z ^ 8| ≤ 3200)
    (h10 : |(z10 : ℝ) - 2 ^ 28 * Z ^ 10| ≤ 310000) :
    |(cosP z2 z4 z6 z8 z10 : ℝ) -
      2 ^ 28 * (1 - Z ^ 2 / 2 + Z ^ 4 / 24 - Z ^ 6 / 720 + Z ^ 8 / 40320 - Z ^ 10 / 3628800)| ≤ 5 / 4 := by
  obtain ⟨hZ0, hZ1⟩ := hZ
  have hZ1' : Z ≤ 1 := by linarith
  have e2 : 0 ≤ Z ^ 2 ∧ Z ^ 2 ≤ 1 := ⟨by positivity, pow_le_one₀ hZ0 hZ1'⟩
  have e4 : 0 ≤ Z ^ 4 ∧ Z ^ 4 ≤ 1 := ⟨by positivity, pow_le_one₀ hZ0 hZ1'⟩
  have e6 : 0 ≤ Z ^ 6 ∧ Z ^ 6 ≤ 1 := ⟨by positivity, pow_le_one₀ hZ0 hZ1'⟩
  have e8 : 0 ≤ Z ^ 8 ∧ Z ^ 8 ≤ 1 := ⟨by positivity, pow_le_one₀ hZ0 hZ1'⟩
  have e10 : 0 ≤ Z ^ 10 ∧ Z ^ 10 ≤ 1 := ⟨by positivity, pow_le_one₀ hZ0 hZ1'⟩

  have e2' : Z ^ 2 ≤ 0.62 := by nlinarith
  have k4 := kcN_floor z4 2863311531
  have k8 := kcN_floor z8 1704352
  have k6 := kcN_floor z6 95443718
  have k10 := kcN_floor z10 18937
  push_cast at k4 k8 k6 k10
  rw [abs_le] at h2 h4 h6 h8 h10
  set A : ℕ := 2 ^ 36 + kcN z4 2863311531 + kcN z8 1704352 with hA
  set B : ℕ := z2 * 2 ^ 7 + kcN z6 95443718 + kcN z10 18937 with hB
  have hAr : (A : ℝ) = 2 ^ 36 + (kcN z4 2863311531 : ℝ) + (kcN z8 1704352 : ℝ) := by rw [hA]; push_cast; ring
  have hBr : (B : ℝ) = (z2 : ℝ) * 2 ^ 7 + (kcN z6 95443718 : ℝ) + (kcN z10 18937 : ℝ) := by rw [hB]; push_cast; ring
  have hBA : B ≤ A := by
    have : (B : ℝ) ≤ (A : ℝ) := by rw [hAr, hBr]; linarith [k4.1, k4.2, k8.1, k8.2, k6.1, k6.2, k10.1, k10.2]
    exact_mod_cast this
  have hr := rshN_err (A - B) 8 (by norm_num)
  have hc : cosP z2 z4 z6 z8 z10 = rshN (A - B) 8 := rfl
  rw [hc]
  rw [Nat.cast_sub hBA, hAr, hBr] at hr
  rw [abs_le] at hr ⊢
  constructor <;> linarith [k4.1, k4.2, k8.1, k8.2, k6.1, k6.2, k10.1, k10.2, hr.1, hr.2]

theorem sinP_err (z z2 z4 z6 z8 : ℕ) (hz : z ≤ QPI)
    (h2 : |(z2 : ℝ) - 2 ^ 28 * ((z : ℝ) / 2 ^ 28) ^ 2| ≤ 1 / 2)
    (h4 : |(z4 : ℝ) - 2 ^ 28 * ((z : ℝ) / 2 ^ 28) ^ 4| ≤ 5 / 2)
    (h6 : |(z6 : ℝ) - 2 ^ 28 * ((z : ℝ) / 2 ^ 28) ^ 6| ≤ 52)
    (h8 : |(z8 : ℝ) - 2 ^ 28 * ((z : ℝ) / 2 ^ 28) ^ 8| ≤ 3200) :
    |(sinP z z2 z4 z6 z8 : ℝ) - 2 ^ 28 * ((z : ℝ) / 2 ^ 28) *
      (1 - ((z : ℝ) / 2 ^ 28) ^ 2 / 6 + ((z : ℝ) / 2 ^ 28) ^ 4 / 120 - ((z : ℝ) / 2 ^ 28) ^ 6 / 5040 +
        ((z : ℝ) / 2 ^ 28) ^ 8 / 362880)| ≤ 3 / 4 := by
  set Zr : ℝ := (z : ℝ) / 2 ^ 28 with hZr
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg _
  have hzq : (z : ℝ) ≤ 210828714 := by
    have h' : z ≤ 210828714 := hz
    exact_mod_cast h'
  have hZ0 : 0 ≤ Zr := by positivity
  have hZ1 : Zr ≤ 0.7854 := by
    rw [hZr, div_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 28)]
    linarith
  have hZ1' : Zr ≤ 1 := by linarith
  have e2 : 0 ≤ Zr ^ 2 ∧ Zr ^ 2 ≤ 1 := ⟨by positivity, pow_le_one₀ hZ0 hZ1'⟩
  have e4 : 0 ≤ Zr ^ 4 ∧ Zr ^ 4 ≤ 1 := ⟨by positivity, pow_le_one₀ hZ0 hZ1'⟩
  have e6 : 0 ≤ Zr ^ 6 ∧ Zr ^ 6 ≤ 1 := ⟨by positivity, pow_le_one₀ hZ0 hZ1'⟩
  have e8 : 0 ≤ Zr ^ 8 ∧ Zr ^ 8 ≤ 1 := ⟨by positivity, pow_le_one₀ hZ0 hZ1'⟩
  have e2' : Zr ^ 2 ≤ 0.62 := by nlinarith
  have k4 := kcN_floor z4 572662306
  have k8 := kcN_floor z8 189372
  have k2 := kcN_floor z2 11453246123
  have k6 := kcN_floor z6 13634817
  push_cast at k4 k8 k2 k6
  rw [abs_le] at h2 h4 h6 h8
  set A : ℕ := 2 ^ 36 + kcN z4 572662306 + kcN z8 189372 with hA
  set B : ℕ := kcN z2 11453246123 + kcN z6 13634817 with hB
  have hAr : (A : ℝ) = 2 ^ 36 + (kcN z4 572662306 : ℝ) + (kcN z8 189372 : ℝ) := by rw [hA]; push_cast; ring
  have hBr : (B : ℝ) = (kcN z2 11453246123 : ℝ) + (kcN z6 13634817 : ℝ) := by rw [hB]; push_cast; ring
  have hBA : B ≤ A := by
    have : (B : ℝ) ≤ (A : ℝ) := by rw [hAr, hBr]; linarith [k4.1, k4.2, k8.1, k8.2, k2.1, k2.2, k6.1, k6.2]
    exact_mod_cast this

  have hbr : |((A - B : ℕ) : ℝ) - 2 ^ 36 * (1 - Zr ^ 2 / 6 + Zr ^ 4 / 120 - Zr ^ 6 / 5040 + Zr ^ 8 / 362880)| ≤ 36 := by
    rw [Nat.cast_sub hBA, hAr, hBr, abs_le]
    constructor <;> linarith [k4.1, k4.2, k8.1, k8.2, k2.1, k2.2, k6.1, k6.2]
  have hr1 := rshN_err (A - B) 6 (by norm_num)
  have hr2 := rshN_err (rshN (A - B) 6 * z) 30 (by norm_num)
  have hs : sinP z z2 z4 z6 z8 = rshN (rshN (A - B) 6 * z) 30 := rfl
  rw [hs]
  push_cast at hr2
  have hid : ((rshN (rshN (A - B) 6 * z) 30 : ℕ) : ℝ) - 2 ^ 28 * Zr *
        (1 - Zr ^ 2 / 6 + Zr ^ 4 / 120 - Zr ^ 6 / 5040 + Zr ^ 8 / 362880) =
      (((rshN (rshN (A - B) 6 * z) 30 : ℕ) : ℝ) - ((rshN (A - B) 6 : ℕ) : ℝ) * z / 2 ^ 30) +
        (((rshN (A - B) 6 : ℕ) : ℝ) - ((A - B : ℕ) : ℝ) / 2 ^ 6) * ((z : ℝ) / 2 ^ 30) +
        (((A - B : ℕ) : ℝ) - 2 ^ 36 * (1 - Zr ^ 2 / 6 + Zr ^ 4 / 120 - Zr ^ 6 / 5040 + Zr ^ 8 / 362880)) * Zr / 2 ^ 8 := by
    rw [hZr]; ring
  rw [hid]
  have t2 : |(((rshN (A - B) 6 : ℕ) : ℝ) - ((A - B : ℕ) : ℝ) / 2 ^ 6) * ((z : ℝ) / 2 ^ 30)| ≤
      1 / 2 * (210828714 / 2 ^ 30) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (z : ℝ) / 2 ^ 30)]
    exact mul_le_mul hr1 (div_le_div_of_nonneg_right hzq (by norm_num)) (by positivity) (by norm_num)
  have t3 : |(((A - B : ℕ) : ℝ) - 2 ^ 36 * (1 - Zr ^ 2 / 6 + Zr ^ 4 / 120 - Zr ^ 6 / 5040 + Zr ^ 8 / 362880)) *
      Zr / 2 ^ 8| ≤ 36 * 0.7854 / 2 ^ 8 := by
    rw [abs_div, abs_mul, abs_of_nonneg hZ0, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 8)]
    exact div_le_div_of_nonneg_right (mul_le_mul hbr hZ1 hZ0 (by norm_num)) (by norm_num)
  have t1 := abs_add_three
    (((rshN (rshN (A - B) 6 * z) 30 : ℕ) : ℝ) - ((rshN (A - B) 6 : ℕ) : ℝ) * z / 2 ^ 30)
    ((((rshN (A - B) 6 : ℕ) : ℝ) - ((A - B : ℕ) : ℝ) / 2 ^ 6) * ((z : ℝ) / 2 ^ 30))
    ((((A - B : ℕ) : ℝ) - 2 ^ 36 * (1 - Zr ^ 2 / 6 + Zr ^ 4 / 120 - Zr ^ 6 / 5040 + Zr ^ 8 / 362880)) * Zr / 2 ^ 8)
  have hn : (1 : ℝ) / 2 + 1 / 2 * (210828714 / 2 ^ 30) + 36 * 0.7854 / 2 ^ 8 ≤ 3 / 4 := by norm_num
  linarith [hr2, t2, t3, t1]

theorem cos_taylor10 (Z : ℝ) (hZ : 0 ≤ Z ∧ Z ≤ 0.7854) :
    |Real.cos Z - (1 - Z ^ 2 / 2 + Z ^ 4 / 24 - Z ^ 6 / 720 + Z ^ 8 / 40320 - Z ^ 10 / 3628800)| ≤ 1 / 2 ^ 31 := by
  rcases hZ with ⟨hZ0, hZ1⟩
  have hZ_le_one : Z ≤ 1 := by linarith

  set f : ℕ → ℝ := fun n => Z ^ (2 * n) / ↑((2 * n).factorial) with hf_def

  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    refine div_nonneg (pow_nonneg hZ0 _) (by positivity)

  have hf_antitone : Antitone f := by
    intro a b h
    dsimp [f]
    have hpow : Z ^ (2 * b) ≤ Z ^ (2 * a) := by
      have h_exp : 2 * a ≤ 2 * b := by omega
      exact pow_le_pow_of_le_one hZ0 hZ_le_one h_exp
    calc
      Z ^ (2 * b) / ↑((2 * b).factorial) ≤ Z ^ (2 * a) / ↑((2 * b).factorial) :=
        div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ Z ^ (2 * a) / ↑((2 * a).factorial) := by
        have hfact' : (2 * a).factorial ≤ (2 * b).factorial :=
          Nat.factorial_le (by omega)
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        exact mod_cast hfact'

  have hf_summable : Summable f := by
    have hexp_summable : Summable (fun n : ℕ => Z ^ n / ↑(n.factorial) : ℕ → ℝ) := by
      have h := NormedSpace.expSeries_div_hasSum_exp (Z : ℝ)
      exact h.summable
    have h_even_summable : Summable (fun n : ℕ => Z ^ (2 * n) / ↑((2 * n).factorial) : ℕ → ℝ) :=
      Summable.comp_injective hexp_summable (fun a b h => by omega)
    exact h_even_summable

  have herror := alternating_series_error_bound f hf_antitone hf_summable 6

  have hcos_eq : Real.cos Z = ∑' i : ℕ, (-1) ^ i * f i := by
    rw [Real.cos_eq_tsum Z]
    refine tsum_congr (fun n => ?_)
    dsimp [f]
    simp [mul_div_assoc]
  have hpartial_eq : (∑ i ∈ Finset.range 6, (-1) ^ i * f i) = 1 - Z ^ 2 / 2 + Z ^ 4 / 24 - Z ^ 6 / 720 + Z ^ 8 / 40320 - Z ^ 10 / 3628800 := by
    dsimp [f]
    simp [Finset.sum_range_succ]
    ring
  have hf6 : f 6 = Z ^ 12 / ↑((12).factorial) := by
    dsimp [f]

  rw [hcos_eq]

  have herror' : |(∑' i : ℕ, (-1) ^ i * f i) - (1 - Z ^ 2 / 2 + Z ^ 4 / 24 - Z ^ 6 / 720 + Z ^ 8 / 40320 - Z ^ 10 / 3628800)| ≤ f 6 := by
    rw [← hpartial_eq]
    exact herror
  apply le_trans herror'
  rw [hf6]

  have hpos12 : 0 < ↑((12).factorial) := by norm_num
  have hpos31 : 0 < (2 ^ 31 : ℝ) := by norm_num
  field_simp [hpos12.ne.symm, hpos31.ne.symm]

  have h1 : Z ^ 12 * (2 ^ 31 : ℝ) ≤ (0.7854 : ℝ) ^ 12 * (2 ^ 31 : ℝ) := by
    gcongr
  have h2 : (0.7854 : ℝ) ^ 12 * (2 ^ 31 : ℝ) ≤ (479001600 : ℝ) := by norm_num
  have h3 : (479001600 : ℝ) = ↑((12).factorial) := by norm_num

  refine le_trans h1 ?_
  refine le_trans h2 ?_
  rw [h3]

theorem sin_taylor9 (Z : ℝ) (hZ : 0 ≤ Z ∧ Z ≤ 0.7854) :
    |Real.sin Z - Z * (1 - Z ^ 2 / 6 + Z ^ 4 / 120 - Z ^ 6 / 5040 + Z ^ 8 / 362880)| ≤ 1 / 2 ^ 29 := by
  rcases hZ with ⟨hZ0, hZ1⟩
  have hZ_le_one : Z ≤ 1 := by linarith

  have h_poly_eq : Z * (1 - Z ^ 2 / 6 + Z ^ 4 / 120 - Z ^ 6 / 5040 + Z ^ 8 / 362880) =
      ∑ i ∈ Finset.range 5, (-1) ^ i * Z ^ (2 * i + 1) / ↑(2 * i + 1).factorial := by
    simp [Finset.sum_range_succ]
    ring
  rw [h_poly_eq]

  set f := fun (n : ℕ) => Z ^ (2 * n + 1) / ↑(2 * n + 1).factorial with hf
  have h_antitone : Antitone f := by
    intro a b h
    dsimp [f]
    have h_exp : 2 * a + 1 ≤ 2 * b + 1 := by omega
    have h_fact : ((2 * a + 1).factorial : ℝ) ≤ ((2 * b + 1).factorial : ℝ) := by
      exact mod_cast Nat.factorial_le h_exp
    have h_pow : Z ^ (2 * b + 1) ≤ Z ^ (2 * a + 1) := by

      exact pow_le_pow_of_le_one hZ0 hZ_le_one h_exp

    have h_denom_pos : 0 ≤ ((2 * b + 1).factorial : ℝ) := by exact mod_cast Nat.zero_le _
    have h_div1 : Z ^ (2 * b + 1) / ((2 * b + 1).factorial : ℝ) ≤
        Z ^ (2 * a + 1) / ((2 * b + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_right h_pow h_denom_pos
    have h_div2 : Z ^ (2 * a + 1) / ((2 * b + 1).factorial : ℝ) ≤
        Z ^ (2 * a + 1) / ((2 * a + 1).factorial : ℝ) := by

      have h_denom_pos' : 0 < ((2 * a + 1).factorial : ℝ) := by
        exact mod_cast Nat.factorial_pos _
      exact div_le_div_of_nonneg_left (pow_nonneg hZ0 _) h_denom_pos' h_fact
    exact le_trans h_div1 h_div2
  have h_summable : Summable f := by

    have h_full : Summable (fun n : ℕ => Z ^ n / (n.factorial : ℝ)) :=
      Real.summable_pow_div_factorial Z

    have h_hasSum : HasSum (fun n : ℕ => (-1) ^ n * Z ^ (2 * n + 1) / ↑(2 * n + 1).factorial) (Real.sin Z) :=
      Real.hasSum_sin Z

    have hZ_sq_lt_one : Z ^ 2 < 1 := by
      nlinarith
    have h_geom : Summable (fun n : ℕ => (Z ^ 2) ^ n) := by
      apply summable_geometric_of_lt_one (by nlinarith) (by nlinarith)

    have h_bound : ∀ n : ℕ, f n ≤ Z * (Z ^ 2) ^ n := by
      intro n
      dsimp [f]

      have h_fact_ge_one : 1 ≤ ((2 * n + 1).factorial : ℝ) := by
        have hpos : 0 < (2 * n + 1).factorial := Nat.factorial_pos _
        have h_one_le : 1 ≤ (2 * n + 1).factorial := Nat.succ_le_of_lt hpos
        exact mod_cast h_one_le
      calc
        Z ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) ≤ Z ^ (2 * n + 1) / 1 := by
          exact (div_le_div_of_nonneg_left (pow_nonneg hZ0 _) (by norm_num) h_fact_ge_one)
        _ = Z ^ (2 * n + 1) := by simp
        _ = Z * (Z ^ 2) ^ n := by
          rw [pow_succ, mul_comm, pow_mul]

    have h_nonneg : ∀ n : ℕ, 0 ≤ f n := by
      intro n
      dsimp [f]
      refine div_nonneg (pow_nonneg hZ0 _) (by exact mod_cast Nat.zero_le _)
    have h_geom' : Summable (fun n : ℕ => Z * (Z ^ 2) ^ n) :=
      h_geom.mul_left Z
    exact Summable.of_nonneg_of_le h_nonneg h_bound h_geom'
  have h_error := alternating_series_error_bound f h_antitone h_summable 5

  have h_tsum : ∑' i : ℕ, (-1) ^ i * f i = Real.sin Z := by
    rw [Real.sin_eq_tsum]
    simp [f, mul_div_assoc]
  rw [h_tsum] at h_error

  have h_f5 : f 5 = Z ^ 11 / ↑(11).factorial := by
    unfold f
    ring
  rw [h_f5] at h_error

  have h_bound : Z ^ 11 / ↑(11).factorial ≤ 1 / 2 ^ 29 := by
    have hZ_pow : Z ^ 11 ≤ (0.7854 : ℝ) ^ 11 := by
      gcongr
    have h_num : (0.7854 : ℝ) ^ 11 / ↑(11).factorial ≤ 1 / 2 ^ 29 := by
      norm_num
    have h_pos : 0 ≤ (↑(11).factorial : ℝ) := by exact mod_cast Nat.zero_le _
    have h_div : Z ^ 11 / (↑(11).factorial : ℝ) ≤ (0.7854 : ℝ) ^ 11 / (↑(11).factorial : ℝ) :=
      div_le_div_of_nonneg_right hZ_pow h_pos
    exact le_trans h_div h_num

  simpa [f, mul_div_assoc] using le_trans h_error h_bound

theorem sc28pZ_err (z : ℕ) (hz : z ≤ QPI) :
    |((sc28pZ z).1 : ℝ) - 2 ^ 28 * Real.sin ((z : ℝ) / 2 ^ 28)| ≤ 2 ∧
      |((sc28pZ z).2 : ℝ) - 2 ^ 28 * Real.cos ((z : ℝ) / 2 ^ 28)| ≤ 2 := by
  set Z := (z : ℝ) / 2 ^ 28 with hZ_def
  have hZ_nonneg : 0 ≤ Z := div_nonneg (Nat.cast_nonneg _) (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
  have hZ_bound : Z ≤ 0.7854 := by
    rw [hZ_def]
    have hz' : (z : ℝ) ≤ (QPI : ℝ) := by exact_mod_cast hz
    have hpos : 0 ≤ (2 ^ 28 : ℝ) := by norm_num
    refine (div_le_div_of_nonneg_right hz' hpos).trans ?_
    norm_num [QPI]
  have hZ_cos_bound : 0 ≤ Z ∧ Z ≤ 0.7854 := And.intro hZ_nonneg hZ_bound
  set z2 := p2 z with hz2_def
  set z4 := p4 z2 with hz4_def
  set z6 := p6 z2 z4 with hz6_def
  set z8 := p8 z4 with hz8_def
  set z10 := p10 z2 z8 with hz10_def
  set t2 := 2 ^ 28 * Z ^ 2 with ht2_def
  set t4 := 2 ^ 28 * Z ^ 4 with ht4_def
  set t6 := 2 ^ 28 * Z ^ 6 with ht6_def
  set t8 := 2 ^ 28 * Z ^ 8 with ht8_def
  set t10 := 2 ^ 28 * Z ^ 10 with ht10_def
  have ht2_nonneg : 0 ≤ t2 := by
    rw [ht2_def]
    nlinarith
  have ht4_nonneg : 0 ≤ t4 := by
    rw [ht4_def]
    nlinarith
  have ht8_nonneg : 0 ≤ t8 := by
    rw [ht8_def]
    nlinarith
  have ht2_bound : t2 ≤ 0.6169 * 2 ^ 28 := by
    rw [ht2_def]
    have hZsq : Z ^ 2 ≤ (0.7854 : ℝ) ^ 2 := by nlinarith
    nlinarith
  have ht4_bound : t4 ≤ 0.3806 * 2 ^ 28 := by
    rw [ht4_def]
    have hZsq : Z ^ 2 ≤ (0.7854 : ℝ) ^ 2 := by nlinarith
    have hZquad : Z ^ 4 ≤ (0.7854 : ℝ) ^ 4 := by
      have hposZsq : 0 ≤ Z ^ 2 := pow_two_nonneg Z
      have hpos0sq : 0 ≤ (0.7854 : ℝ) ^ 2 := by norm_num
      have htemp : (Z ^ 2) ^ 2 ≤ ((0.7854 : ℝ) ^ 2) ^ 2 := by nlinarith
      have hleft : (Z ^ 2) ^ 2 = Z ^ 4 := by ring
      have hright : ((0.7854 : ℝ) ^ 2) ^ 2 = (0.7854 : ℝ) ^ 4 := by ring
      simpa [hleft, hright] using htemp
    nlinarith
  have ht8_bound : t8 ≤ 0.1448 * 2 ^ 28 := by
    rw [ht8_def]
    have hZsq : Z ^ 2 ≤ (0.7854 : ℝ) ^ 2 := by nlinarith
    have hZquad : Z ^ 4 ≤ (0.7854 : ℝ) ^ 4 := by
      have hposZsq : 0 ≤ Z ^ 2 := pow_two_nonneg Z
      have hpos0sq : 0 ≤ (0.7854 : ℝ) ^ 2 := by norm_num
      have htemp : (Z ^ 2) ^ 2 ≤ ((0.7854 : ℝ) ^ 2) ^ 2 := by nlinarith
      have hleft : (Z ^ 2) ^ 2 = Z ^ 4 := by ring
      have hright : ((0.7854 : ℝ) ^ 2) ^ 2 = (0.7854 : ℝ) ^ 4 := by ring
      simpa [hleft, hright] using htemp
    have hZoct : Z ^ 8 ≤ (0.7854 : ℝ) ^ 8 := by
      have hposZquad : 0 ≤ Z ^ 4 := by
        have : 0 ≤ Z := hZ_nonneg
        nlinarith
      have hpos0quad : 0 ≤ (0.7854 : ℝ) ^ 4 := by norm_num
      have htemp : (Z ^ 4) ^ 2 ≤ ((0.7854 : ℝ) ^ 4) ^ 2 := by nlinarith
      have hleft : (Z ^ 4) ^ 2 = Z ^ 8 := by ring
      have hright : ((0.7854 : ℝ) ^ 4) ^ 2 = (0.7854 : ℝ) ^ 8 := by ring
      simpa [hleft, hright] using htemp
    nlinarith
  have ht2_and : 0 ≤ t2 ∧ t2 ≤ 0.6169 * 2 ^ 28 := And.intro ht2_nonneg ht2_bound
  have ht4_and : 0 ≤ t4 ∧ t4 ≤ 0.3806 * 2 ^ 28 := And.intro ht4_nonneg ht4_bound
  have ht8_and : 0 ≤ t8 ∧ t8 ≤ 0.1448 * 2 ^ 28 := And.intro ht8_nonneg ht8_bound
  have h2 : |(z2 : ℝ) - 2 ^ 28 * Z ^ 2| ≤ 1 / 2 := by
    dsimp [z2, Z]
    simpa [hZ_def] using p2_err z hz
  have h4 : |(z4 : ℝ) - 2 ^ 28 * Z ^ 4| ≤ 5 / 2 := by
    rw [hz4_def]
    have h_eq : t2 ^ 2 / 2 ^ 28 = t4 := by
      dsimp [t2, t4]
      field_simp
    have htemp := p4_err z2 t2 ht2_nonneg ht2_bound h2
    simpa [hz4_def, h_eq] using htemp
  have h6 : |(z6 : ℝ) - 2 ^ 28 * Z ^ 6| ≤ 52 := by
    rw [hz6_def]
    have h_eq : t4 * t2 / 2 ^ 28 = t6 := by
      dsimp [t2, t4, t6]
      field_simp
    have htemp := p6_err z2 z4 t2 t4 ht2_and ht4_and h2 h4
    simpa [hz6_def, h_eq] using htemp
  have h8 : |(z8 : ℝ) - 2 ^ 28 * Z ^ 8| ≤ 3200 := by
    rw [hz8_def]
    have h_eq : t4 ^ 2 / 2 ^ 28 = t8 := by
      dsimp [t4, t8]
      field_simp
    have htemp := p8_err z4 t4 ht4_and h4
    simpa [hz8_def, h_eq] using htemp
  have h10 : |(z10 : ℝ) - 2 ^ 28 * Z ^ 10| ≤ 310000 := by
    rw [hz10_def]
    have h_eq : t8 * t2 / 2 ^ 28 = t10 := by
      dsimp [t2, t8, t10]
      field_simp
    have htemp := p10_err z2 z8 t2 t8 ht2_and ht8_and h2 h8
    simpa [hz10_def, h_eq] using htemp
  have h_cosP := cosP_err z2 z4 z6 z8 z10 Z hZ_cos_bound h2 h4 h6 h8 h10
  have h_sinP_raw := sinP_err z z2 z4 z6 z8 hz h2 h4 h6 h8
  have h_cos_taylor := cos_taylor10 Z hZ_cos_bound
  have h_sin_taylor := sin_taylor9 Z hZ_cos_bound
  have h_cos_goal : |((sc28pZ z).2 : ℝ) - 2 ^ 28 * Real.cos Z| ≤ 2 := by
    dsimp [sc28pZ]
    set taylor_cos := 1 - Z ^ 2 / 2 + Z ^ 4 / 24 - Z ^ 6 / 720 + Z ^ 8 / 40320 - Z ^ 10 / 3628800 with h_taylor_cos_def
    have h_tri : (cosP z2 z4 z6 z8 z10 : ℝ) - 2 ^ 28 * Real.cos Z =
      ((cosP z2 z4 z6 z8 z10 : ℝ) - 2 ^ 28 * taylor_cos) + 2 ^ 28 * (taylor_cos - Real.cos Z) := by
      dsimp [taylor_cos]
      ring
    rw [h_tri]
    calc
      |((cosP z2 z4 z6 z8 z10 : ℝ) - 2 ^ 28 * taylor_cos) + 2 ^ 28 * (taylor_cos - Real.cos Z)|
      ≤ |(cosP z2 z4 z6 z8 z10 : ℝ) - 2 ^ 28 * taylor_cos| + |2 ^ 28 * (taylor_cos - Real.cos Z)| := abs_add_le _ _
      _ ≤ 5/4 + |2 ^ 28 * (taylor_cos - Real.cos Z)| := by
        exact add_le_add_left h_cosP (|2 ^ 28 * (taylor_cos - Real.cos Z)|)
      _ = 5/4 + |(2 ^ 28 : ℝ)| * |taylor_cos - Real.cos Z| := by rw [abs_mul]
      _ = 5/4 + (2 ^ 28 : ℝ) * |taylor_cos - Real.cos Z| := by rw [abs_of_pos (by norm_num : 0 < (2 ^ 28 : ℝ))]
      _ = 5/4 + (2 ^ 28 : ℝ) * |Real.cos Z - taylor_cos| := by rw [abs_sub_comm]
      _ ≤ 5/4 + (2 ^ 28 : ℝ) * (1 / 2 ^ 31) := by

        have htemp : (2 ^ 28 : ℝ) * |Real.cos Z - taylor_cos| ≤ (2 ^ 28 : ℝ) * (1 / 2 ^ 31) :=
          mul_le_mul_of_nonneg_left h_cos_taylor (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
        nlinarith
      _ ≤ 2 := by norm_num
  have h_sin_goal : |((sc28pZ z).1 : ℝ) - 2 ^ 28 * Real.sin Z| ≤ 2 := by
    dsimp [sc28pZ]
    set taylor_sin := Z * (1 - Z ^ 2 / 6 + Z ^ 4 / 120 - Z ^ 6 / 5040 + Z ^ 8 / 362880) with h_taylor_sin_def
    have h_tri : (sinP z z2 z4 z6 z8 : ℝ) - 2 ^ 28 * Real.sin Z =
      ((sinP z z2 z4 z6 z8 : ℝ) - 2 ^ 28 * taylor_sin) + 2 ^ 28 * (taylor_sin - Real.sin Z) := by
      dsimp [taylor_sin]
      ring
    rw [h_tri]
    have h_sinP : |(sinP z z2 z4 z6 z8 : ℝ) - 2 ^ 28 * taylor_sin| ≤ 3/4 := by
      simpa [hZ_def, taylor_sin, mul_assoc] using h_sinP_raw
    have h_bound : |2 ^ 28 * (taylor_sin - Real.sin Z)| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : 0 < (2 ^ 28 : ℝ))]
      have h_triple : |taylor_sin - Real.sin Z| ≤ 1 / 2 ^ 29 := by
        dsimp [taylor_sin]
        rw [abs_sub_comm]
        exact h_sin_taylor
      have htemp : (2 ^ 28 : ℝ) * |taylor_sin - Real.sin Z| ≤ (2 ^ 28 : ℝ) * (1 / 2 ^ 29) :=
        mul_le_mul_of_nonneg_left h_triple (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
      have h_eq : (2 ^ 28 : ℝ) * (1 / 2 ^ 29) = 1 / 2 := by
        ring
      rw [h_eq] at htemp
      exact htemp
    calc
      |((sinP z z2 z4 z6 z8 : ℝ) - 2 ^ 28 * taylor_sin) + 2 ^ 28 * (taylor_sin - Real.sin Z)|
      ≤ |(sinP z z2 z4 z6 z8 : ℝ) - 2 ^ 28 * taylor_sin| + |2 ^ 28 * (taylor_sin - Real.sin Z)| := abs_add_le _ _
      _ ≤ 3/4 + |2 ^ 28 * (taylor_sin - Real.sin Z)| := by
        exact add_le_add_left h_sinP (|2 ^ 28 * (taylor_sin - Real.sin Z)|)
      _ ≤ 3/4 + (1 / 2) := by
        nlinarith
      _ = 5/4 := by norm_num
      _ ≤ 2 := by norm_num
  have h_sin_goal' : |((sc28pZ z).1 : ℝ) - 2 ^ 28 * Real.sin ((z : ℝ) / 2 ^ 28)| ≤ 2 := by
    simpa [hZ_def] using h_sin_goal
  exact And.intro h_sin_goal' h_cos_goal

theorem sc28pS_err (x : ℕ) (hx : x ≤ PI_LO + 1) :
    |((sc28pS x).1 : ℝ) - 2 ^ 28 * Real.sin ((x : ℝ) / 2 ^ 28)| ≤ 3 ∧
      |((sc28pS x).2 : ℝ) - 2 ^ 28 * Real.cos ((x : ℝ) / 2 ^ 28)| ≤ 3 := by
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have eQ : QPI = 210828714 := rfl
  have eH : HPI_LO = 421657428 := rfl
  have eP : PI_LO = 843314856 := rfl

  have L : ∀ a b : ℝ, |a - b| ≤ 1 →
      |2 ^ 28 * Real.sin (a / 2 ^ 28) - 2 ^ 28 * Real.sin (b / 2 ^ 28)| ≤ 1 ∧
        |2 ^ 28 * Real.cos (a / 2 ^ 28) - 2 ^ 28 * Real.cos (b / 2 ^ 28)| ≤ 1 := by
    intro a b hab
    have hd : |a / 2 ^ 28 - b / 2 ^ 28| ≤ 1 / 2 ^ 28 := by
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 28)]
      exact div_le_div_of_nonneg_right hab (by norm_num)
    have h28 : (2 : ℝ) ^ 28 * (1 / 2 ^ 28) = 1 := by norm_num
    constructor
    · rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 28)]
      have := (Real.abs_sin_sub_sin_le _ _).trans hd
      nlinarith
    · rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 28)]
      have := (Real.abs_cos_sub_cos_le _ _).trans hd
      nlinarith
  unfold sc28pS
  simp only [min_eq_left hx]
  by_cases hH : HPI_LO < x
  · by_cases hQ : QPI < PI_LO - x
    ·
      simp only [hH, hQ, if_true]
      have hz : HPI_LO - (PI_LO - x) ≤ QPI := by omega
      obtain ⟨h1, h2⟩ := sc28pZ_err _ hz
      have hzr : ((HPI_LO - (PI_LO - x) : ℕ) : ℝ) = (x : ℝ) - 421657428 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), eH, eP]; push_cast; ring
      have hs : Real.sin ((x : ℝ) / 2 ^ 28) = Real.cos (((x : ℝ) - π * 2 ^ 27) / 2 ^ 28) := by
        rw [show ((x : ℝ) - π * 2 ^ 27) / 2 ^ 28 = (x : ℝ) / 2 ^ 28 - π / 2 by ring, Real.cos_sub_pi_div_two]
      have hc : Real.cos ((x : ℝ) / 2 ^ 28) = -Real.sin (((x : ℝ) - π * 2 ^ 27) / 2 ^ 28) := by
        rw [show ((x : ℝ) - π * 2 ^ 27) / 2 ^ 28 = (x : ℝ) / 2 ^ 28 - π / 2 by ring, Real.sin_sub_pi_div_two]
        ring
      obtain ⟨Ls, Lc⟩ := L ((x : ℝ) - π * 2 ^ 27) ((HPI_LO - (PI_LO - x) : ℕ) : ℝ)
        (by rw [hzr, abs_le]; constructor <;> nlinarith)
      push_cast
      rw [hs, hc]
      rw [abs_le] at h1 h2 Ls Lc
      constructor <;> rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, Ls.1, Ls.2, Lc.1, Lc.2]
    ·
      simp only [hH, hQ, if_true, if_false]
      have hz : PI_LO - x ≤ QPI := by omega
      obtain ⟨h1, h2⟩ := sc28pZ_err _ hz
      have hzr : |(π * 2 ^ 28 - x) - ((PI_LO - x : ℕ) : ℝ)| ≤ 1 := by
        rcases Nat.lt_or_ge PI_LO x with hx' | hx'
        · have : x = PI_LO + 1 := by omega
          rw [this, show PI_LO - (PI_LO + 1) = 0 by omega, eP]
          push_cast
          rw [abs_le]; constructor <;> nlinarith
        · rw [Nat.cast_sub hx', eP]
          push_cast
          rw [abs_le]; constructor <;> nlinarith
      have hs : Real.sin ((x : ℝ) / 2 ^ 28) = Real.sin ((π * 2 ^ 28 - x) / 2 ^ 28) := by
        rw [show (π * 2 ^ 28 - x) / 2 ^ 28 = π - (x : ℝ) / 2 ^ 28 by ring, Real.sin_pi_sub]
      have hc : Real.cos ((x : ℝ) / 2 ^ 28) = -Real.cos ((π * 2 ^ 28 - x) / 2 ^ 28) := by
        rw [show (π * 2 ^ 28 - x) / 2 ^ 28 = π - (x : ℝ) / 2 ^ 28 by ring, Real.cos_pi_sub]
        ring
      obtain ⟨Ls, Lc⟩ := L (π * 2 ^ 28 - x) ((PI_LO - x : ℕ) : ℝ) hzr
      push_cast
      rw [hs, hc]
      rw [abs_le] at h1 h2 Ls Lc
      constructor <;> rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, Ls.1, Ls.2, Lc.1, Lc.2]
  · by_cases hQ : QPI < x
    ·
      simp only [hH, hQ, if_true, if_false]
      have hz : HPI_LO - x ≤ QPI := by omega
      obtain ⟨h1, h2⟩ := sc28pZ_err _ hz
      have hzr : ((HPI_LO - x : ℕ) : ℝ) = 421657428 - (x : ℝ) := by
        rw [Nat.cast_sub (by omega), eH]; push_cast; ring
      have hs : Real.sin ((x : ℝ) / 2 ^ 28) = Real.cos ((π * 2 ^ 27 - x) / 2 ^ 28) := by
        rw [show (π * 2 ^ 27 - x) / 2 ^ 28 = π / 2 - (x : ℝ) / 2 ^ 28 by ring, Real.cos_pi_div_two_sub]
      have hc : Real.cos ((x : ℝ) / 2 ^ 28) = Real.sin ((π * 2 ^ 27 - x) / 2 ^ 28) := by
        rw [show (π * 2 ^ 27 - x) / 2 ^ 28 = π / 2 - (x : ℝ) / 2 ^ 28 by ring, Real.sin_pi_div_two_sub]
      obtain ⟨Ls, Lc⟩ := L (π * 2 ^ 27 - x) ((HPI_LO - x : ℕ) : ℝ)
        (by rw [hzr, abs_le]; constructor <;> nlinarith)
      push_cast
      rw [hs, hc]
      rw [abs_le] at h1 h2 Ls Lc
      constructor <;> rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, Ls.1, Ls.2, Lc.1, Lc.2]
    ·
      simp only [hH, hQ, if_false]
      have hz : x ≤ QPI := by omega
      obtain ⟨h1, h2⟩ := sc28pZ_err _ hz
      push_cast
      rw [abs_le] at h1 h2
      constructor <;> rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

def sqStepS (q : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 + q ≤ s.1 then (s.1 - (s.2 + q), s.2 / 2 + q) else (s.1, s.2 / 2)

def sqLoopS : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | k + 1, s => sqLoopS k (sqStepS (4 ^ k) s)

theorem sqStepS_inv (k x : ℕ) :
    sqStepS (4 ^ k) (x - Nat.sqrt (x / 4 ^ (k + 1)) ^ 2 * 4 ^ (k + 1), Nat.sqrt (x / 4 ^ (k + 1)) * 4 ^ (k + 1)) =
      (x - Nat.sqrt (x / 4 ^ k) ^ 2 * 4 ^ k, Nat.sqrt (x / 4 ^ k) * 4 ^ k) := by
  have h4 : 4 ^ (k + 1) = 4 ^ k * 4 := pow_succ 4 k
  have hm : x / 4 ^ (k + 1) = x / 4 ^ k / 4 := by rw [h4, Nat.div_div_eq_div_mul]
  rw [hm, h4]
  generalize hQ : 4 ^ k = Q
  have hQpos : 0 < Q := hQ ▸ by positivity
  generalize hM : x / Q = m
  have hxQ : m * Q ≤ x := hM ▸ Nat.div_mul_le_self x Q
  generalize ha : Nat.sqrt (m / 4) = a
  generalize ha' : Nat.sqrt m = a'
  have hA1 : a * a ≤ m / 4 := ha ▸ Nat.sqrt_le (m / 4)
  have hA2 : m / 4 < (a + 1) * (a + 1) := ha ▸ Nat.lt_succ_sqrt (m / 4)
  have hm4 : 4 * (m / 4) ≤ m := Nat.mul_div_le m 4
  have hm4' : m < 4 * (m / 4) + 4 := by omega
  have hB1 : 2 * a ≤ a' := ha' ▸ Nat.le_sqrt.mpr (by nlinarith)
  have hB2 : a' < 2 * a + 2 := ha' ▸ Nat.sqrt_lt.mpr (by nlinarith)
  have hC1 : a' * a' ≤ m := ha' ▸ Nat.sqrt_le m
  have hC2 : m < (a' + 1) * (a' + 1) := ha' ▸ Nat.lt_succ_sqrt m
  have hle : a ^ 2 * (Q * 4) ≤ x := by nlinarith
  unfold sqStepS
  have e1 : a * (Q * 4) / 2 = 2 * a * Q := by
    rw [show a * (Q * 4) = 2 * (2 * a * Q) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  simp only [e1]
  rcases (by omega : a' = 2 * a ∨ a' = 2 * a + 1) with h | h
  · subst h
    have hn : ¬ (a * (Q * 4) + Q ≤ x - a ^ 2 * (Q * 4)) := by
      intro hc
      have h1 : (2 * a + 1) * (2 * a + 1) * Q ≤ x := by
        have : a * (Q * 4) + Q + a ^ 2 * (Q * 4) ≤ x := by omega
        nlinarith
      have h2 : (2 * a + 1) * (2 * a + 1) ≤ m := by
        rw [← hM]; exact (Nat.le_div_iff_mul_le hQpos).mpr h1
      exact absurd h2 (not_le.mpr hC2)
    rw [if_neg hn]
    ext
    · show x - a ^ 2 * (Q * 4) = x - (2 * a) ^ 2 * Q
      congr 1; ring
    · rfl
  · subst h
    have hc : a * (Q * 4) + Q ≤ x - a ^ 2 * (Q * 4) := by
      have h1 : (2 * a + 1) * (2 * a + 1) * Q ≤ x := le_trans (Nat.mul_le_mul_right Q hC1) hxQ
      have : a * (Q * 4) + Q + a ^ 2 * (Q * 4) ≤ x := by nlinarith
      omega
    rw [if_pos hc]
    ext
    · show x - a ^ 2 * (Q * 4) - (a * (Q * 4) + Q) = x - (2 * a + 1) ^ 2 * Q
      rw [Nat.sub_sub]; congr 1; ring
    · show 2 * a * Q + Q = (2 * a + 1) * Q
      ring

namespace H_sqLoopS_sqrt

lemma sqLoopS_inv (j x : ℕ) : sqLoopS j (x - (Nat.sqrt (x / 4 ^ j)) ^ 2 * 4 ^ j, Nat.sqrt (x / 4 ^ j) * 4 ^ j) = (x - (Nat.sqrt x) ^ 2, Nat.sqrt x) := by
  induction' j with j ih
  · simp [sqLoopS, pow_zero, Nat.div_one]
  · rw [sqLoopS, sqStepS_inv j x, ih]
end H_sqLoopS_sqrt

open H_sqLoopS_sqrt in
theorem sqLoopS_sqrt (K x : ℕ) (hx : x < 4 ^ K) : (sqLoopS K (x, 0)).2 = Nat.sqrt x := by
  have hdiv : x / 4 ^ K = 0 := Nat.div_eq_of_lt hx
  have hsqrt : (x / 4 ^ K).sqrt = 0 := by rw [hdiv, Nat.sqrt_zero]
  have hstate : (x, 0) = (x - (x / 4 ^ K).sqrt ^ 2 * 4 ^ K, (x / 4 ^ K).sqrt * 4 ^ K) := by
    rw [hsqrt]; simp
  rw [hstate]
  rw [sqLoopS_inv K x]

def HPI_HI : ℤ := 421657429

def acosLoX (n d a cl : ℤ) : ℤ :=
  if a ≤ 0 ∨ (n * 2 ^ 28 ≤ cl * d ∧ a ≤ (PI_LO : ℤ)) then a else 0

def acosHiX (n d a ch : ℤ) : ℤ :=
  if (PI_LO : ℤ) + 1 ≤ a ∨ ch * d ≤ n * 2 ^ 28 then a else (PI_LO : ℤ) + 1

def atanEndX (hi : Bool) (n d b sl sh cl ch : ℤ) : ℤ :=
  let ng := decide (n < 0)
  let lot := if hi then ng else !ng
  let cc := if lot then cl else ch
  let ss := if lot then sh else sl
  let l := ss * d
  let r := |n| * cc
  let clo := b ≤ 0 ∨ (l ≤ r ∧ 0 ≤ cl ∧ b ≤ (HPI_LO : ℤ))
  let chi := HPI_HI ≤ b ∨ r ≤ l
  let c := (lot = true ∧ clo) ∨ (lot = false ∧ chi)
  if c then (if ng then -b else b) else (if hi then HPI_HI else -HPI_HI)

theorem acosLoX_sound (n d a cl : ℤ) (hd : 0 < d) (ha : 0 ≤ a)
    (hcl : (cl : ℝ) ≤ 2 ^ 28 * Real.cos ((a : ℝ) / 2 ^ 28)) (y : ℝ) (hy : y ≤ (n : ℝ) / d) (_hy1 : -1 ≤ y) :
    (acosLoX n d a cl : ℝ) / 2 ^ 28 ≤ Real.arccos y := by
  simp [acosLoX]
  split_ifs with hcond
  ·
    rcases hcond with (ha0 | ⟨hineq, haPI⟩)
    ·
      have haz : (a : ℝ) = 0 := by
        have haz_int : a = (0 : ℤ) := le_antisymm ha0 ha
        exact_mod_cast haz_int
      simp [haz, Real.arccos_nonneg y]
    ·
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
      have ha_nonneg : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have haPI_real : (a : ℝ) ≤ (PI_LO : ℝ) := by exact_mod_cast haPI

      have hy_mul : y * (d : ℝ) ≤ (n : ℝ) :=
        (le_div_iff₀ hdpos).mp hy

      have hineq_real : (n : ℝ) * (2 ^ 28 : ℝ) ≤ (cl : ℝ) * (d : ℝ) := by
        exact_mod_cast hineq

      have hy_mul2 : y * (2 ^ 28 : ℝ) ≤ (cl : ℝ) := by
        nlinarith

      have hy_le_cos : y ≤ Real.cos ((a : ℝ) / 2 ^ 28) := by
        nlinarith

      have h_pi_gt : (PI_LO : ℝ) / 2 ^ 28 < Real.pi := by
        have hpos : (0 : ℝ) < 2 ^ 28 := by norm_num
        rw [div_lt_iff₀ hpos]

        unfold PI_LO
        have h_bound : (843314856 : ℝ) < (3.14159265358979323846 : ℝ) * (2 ^ 28 : ℝ) := by
          norm_num
        have h_pi_gt' : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
        have h_mul : (3.14159265358979323846 : ℝ) * (2 ^ 28 : ℝ) < Real.pi * (2 ^ 28 : ℝ) := by
          exact mul_lt_mul_of_pos_right h_pi_gt' hpos
        exact lt_trans h_bound h_mul
      have h_cos_high : (a : ℝ) / 2 ^ 28 ≤ Real.pi := by
        have h_div_le : (a : ℝ) / 2 ^ 28 ≤ (PI_LO : ℝ) / 2 ^ 28 := by
          have hpos28 : (0 : ℝ) ≤ 2 ^ 28 := by norm_num
          exact div_le_div_of_nonneg_right haPI_real hpos28
        linarith
      have h_cos_low : 0 ≤ (a : ℝ) / 2 ^ 28 :=
        div_nonneg ha_nonneg (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
      have h_arccos_cos : Real.arccos (Real.cos ((a : ℝ) / 2 ^ 28)) = (a : ℝ) / 2 ^ 28 :=
        Real.arccos_cos h_cos_low h_cos_high
      have h_arccos_le : Real.arccos (Real.cos ((a : ℝ) / 2 ^ 28)) ≤ Real.arccos y :=
        Real.arccos_le_arccos hy_le_cos
      linarith
  ·

    have : (0 : ℝ) / 2 ^ 28 = 0 := by norm_num
    simp [this, Real.arccos_nonneg y]

theorem acosHiX_sound (n d a ch : ℤ) (hd : 0 < d) (ha : 0 ≤ a)
    (hch : 2 ^ 28 * Real.cos ((a : ℝ) / 2 ^ 28) ≤ (ch : ℝ)) (y : ℝ) (hy : (n : ℝ) / d ≤ y) (_hy1 : y ≤ 1) :
    Real.arccos y ≤ (acosHiX n d a ch : ℝ) / 2 ^ 28 := by
  unfold acosHiX
  split
  ·
    rename_i h
    rcases h with (hpi | hch')
    ·
      have ha_large : (PI_LO : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hpi
      have hpi_bound : Real.pi < ((PI_LO : ℤ) + 1 : ℝ) / (2 ^ 28 : ℝ) := by
        have h := Real.pi_lt_d20
        have h' : (3.14159265358979323847 : ℝ) ≤ ((PI_LO : ℤ) + 1 : ℝ) / (2 ^ 28 : ℝ) := by
          unfold PI_LO; norm_num
        linarith
      have harccos_le_pi : Real.arccos y ≤ Real.pi := Real.arccos_le_pi y
      have hdiv : ((PI_LO : ℤ) + 1 : ℝ) / (2 ^ 28 : ℝ) ≤ (a : ℝ) / (2 ^ 28 : ℝ) :=
        (div_le_div_of_nonneg_right ha_large (by norm_num : 0 ≤ (2 ^ 28 : ℝ)))
      linarith
    ·
      have hch'_real : (ch : ℝ) * (d : ℝ) ≤ (n : ℝ) * (2 ^ 28 : ℝ) := by exact_mod_cast hch'
      have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd
      have h_two28_pos : 0 < (2 ^ 28 : ℝ) := by norm_num
      have hcos_le_nd : Real.cos ((a : ℝ) / 2 ^ 28) ≤ (n : ℝ) / (d : ℝ) := by
        have hcos_le_ch : Real.cos ((a : ℝ) / 2 ^ 28) ≤ (ch : ℝ) / (2 ^ 28 : ℝ) := by
          linarith
        have hch_le_nd : (ch : ℝ) / (2 ^ 28 : ℝ) ≤ (n : ℝ) / (d : ℝ) :=
          (div_le_div_iff₀ h_two28_pos hd_pos).mpr hch'_real
        linarith
      have hcos_le_y : Real.cos ((a : ℝ) / 2 ^ 28) ≤ y := by
        linarith
      have ha_nonneg : 0 ≤ (a : ℝ) := by exact_mod_cast ha
      have ha_div_nonneg : 0 ≤ (a : ℝ) / (2 ^ 28 : ℝ) :=
        div_nonneg ha_nonneg (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
      by_cases hpi_le_a : (PI_LO : ℤ) + 1 ≤ a
      ·
        have ha_large : (PI_LO : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hpi_le_a
        have hpi_bound : Real.pi < ((PI_LO : ℤ) + 1 : ℝ) / (2 ^ 28 : ℝ) := by
          have h := Real.pi_lt_d20
          have h' : (3.14159265358979323847 : ℝ) ≤ ((PI_LO : ℤ) + 1 : ℝ) / (2 ^ 28 : ℝ) := by
            unfold PI_LO; norm_num
          linarith
        have harccos_le_pi : Real.arccos y ≤ Real.pi := Real.arccos_le_pi y
        have hdiv : ((PI_LO : ℤ) + 1 : ℝ) / (2 ^ 28 : ℝ) ≤ (a : ℝ) / (2 ^ 28 : ℝ) :=
          (div_le_div_of_nonneg_right ha_large (by norm_num : 0 ≤ (2 ^ 28 : ℝ)))
        linarith
      ·
        have ha_le_piLO : (a : ℤ) ≤ (PI_LO : ℤ) := by omega
        have ha_le_piLO_real : (a : ℝ) ≤ (PI_LO : ℝ) := by exact_mod_cast ha_le_piLO
        have hpiLO_div_le_pi : (PI_LO : ℝ) / (2 ^ 28 : ℝ) ≤ Real.pi := by
          have h := Real.pi_gt_d20
          have h' : (PI_LO : ℝ) / (2 ^ 28 : ℝ) ≤ (3.14159265358979323846 : ℝ) := by
            unfold PI_LO; norm_num
          linarith
        have ha_div_le_pi : (a : ℝ) / (2 ^ 28 : ℝ) ≤ Real.pi := by
          have hdiv' : (a : ℝ) / (2 ^ 28 : ℝ) ≤ (PI_LO : ℝ) / (2 ^ 28 : ℝ) :=
            (div_le_div_of_nonneg_right ha_le_piLO_real (by norm_num : 0 ≤ (2 ^ 28 : ℝ)))
          linarith
        have harccos_cos : Real.arccos (Real.cos ((a : ℝ) / 2 ^ 28)) = (a : ℝ) / 2 ^ 28 :=
          Real.arccos_cos ha_div_nonneg ha_div_le_pi
        have harccos_le : Real.arccos y ≤ Real.arccos (Real.cos ((a : ℝ) / 2 ^ 28)) :=
          Real.arccos_le_arccos hcos_le_y
        linarith
  ·
    rename_i h
    have hnot := not_or.mp h
    rcases hnot with ⟨hnotpi, hnotch⟩
    have ha_le_piLO : (a : ℤ) ≤ (PI_LO : ℤ) := by omega
    have hpi_bound : Real.pi < ((PI_LO : ℤ) + 1 : ℝ) / (2 ^ 28 : ℝ) := by
      have h := Real.pi_lt_d20
      have h' : (3.14159265358979323847 : ℝ) ≤ ((PI_LO : ℤ) + 1 : ℝ) / (2 ^ 28 : ℝ) := by
        unfold PI_LO; norm_num
      linarith
    have harccos_le_pi : Real.arccos y ≤ Real.pi := Real.arccos_le_pi y
    have htarget : Real.arccos y ≤ ((PI_LO : ℤ) + 1 : ℝ) / (2 ^ 28 : ℝ) := by
      linarith
    simpa using htarget

theorem atanEndX_lo_sound (n d b sl sh cl ch : ℤ) (hd : 0 < d) (hb : 0 ≤ b)
    (hs : (sl : ℝ) ≤ 2 ^ 28 * Real.sin ((b : ℝ) / 2 ^ 28) ∧ 2 ^ 28 * Real.sin ((b : ℝ) / 2 ^ 28) ≤ sh)
    (hc : (cl : ℝ) ≤ 2 ^ 28 * Real.cos ((b : ℝ) / 2 ^ 28) ∧ 2 ^ 28 * Real.cos ((b : ℝ) / 2 ^ 28) ≤ ch)
    (q : ℝ) (hq : (n : ℝ) / d ≤ q) :
    (atanEndX false n d b sl sh cl ch : ℝ) / 2 ^ 28 ≤ Real.arctan q := by

  set β := (b : ℝ) / (2 ^ 28 : ℝ) with hβ
  have hβ_eq : β = (b : ℝ) / (2 ^ 28 : ℝ) := rfl

  rcases hs with ⟨hsl, hsh⟩

  rcases hc with ⟨hcl, hch⟩

  have hsin_lower : (sl : ℝ) ≤ (2 ^ 28 : ℝ) * Real.sin β := by
    simpa [hβ] using hsl
  have hsin_upper : (2 ^ 28 : ℝ) * Real.sin β ≤ (sh : ℝ) := by
    simpa [hβ] using hsh
  have hcos_lower : (cl : ℝ) ≤ (2 ^ 28 : ℝ) * Real.cos β := by
    simpa [hβ] using hcl
  have hcos_upper : (2 ^ 28 : ℝ) * Real.cos β ≤ (ch : ℝ) := by
    simpa [hβ] using hch

  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd_int_pos : (0 : ℤ) < d := hd
  have hb_int_nonneg : (0 : ℤ) ≤ b := hb

  have hq_div : (n : ℝ) / (d : ℝ) ≤ q := by
    simpa using hq

  have hb_zero_of_nonpos : (b : ℝ) ≤ 0 → (b : ℝ) = 0 := by
    intro h
    have hb' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith

  have hpi_gt_d20 : (3.14159265358979323846 : ℝ) < π := by exact_mod_cast Real.pi_gt_d20
  have hpi_lt_d20 : π < (3.14159265358979323847 : ℝ) := by exact_mod_cast Real.pi_lt_d20
  have h_HPI_LO_div_lt_pi_div_two : (HPI_LO : ℝ) / (2 ^ 28 : ℝ) < π / 2 := by
    unfold HPI_LO
    have hpos1 : (0 : ℝ) < 2 ^ 28 := by norm_num
    have hpos2 : (0 : ℝ) < 2 := by norm_num
    apply (div_lt_div_iff₀ hpos1 hpos2).mpr
    have h3 : (3.14159265358979323846 : ℝ) * (2 ^ 28 : ℝ) < π * (2 ^ 28 : ℝ) := by
      nlinarith [Real.pi_gt_d20]
    calc
      (421657428 : ℝ) * 2 = (843314856 : ℝ) := by norm_num
      _ < (3.14159265358979323846 : ℝ) * (2 ^ 28 : ℝ) := by norm_num
      _ < π * (2 ^ 28 : ℝ) := h3
  have h_pi_div_two_lt_HPI_HI_div : π / 2 < (HPI_HI : ℝ) / (2 ^ 28 : ℝ) := by
    unfold HPI_HI
    have hpos1 : (0 : ℝ) < 2 := by norm_num
    have hpos2 : (0 : ℝ) < 2 ^ 28 := by norm_num
    apply (div_lt_div_iff₀ hpos1 hpos2).mpr
    have h1 : π * (2 ^ 28 : ℝ) < (3.14159265358979323847 : ℝ) * (2 ^ 28 : ℝ) := by
      nlinarith [Real.pi_lt_d20]
    calc
      π * (2 ^ 28 : ℝ) < (3.14159265358979323847 : ℝ) * (2 ^ 28 : ℝ) := h1
      _ < (421657429 : ℝ) * 2 := by norm_num

  by_cases hng : (n : ℤ) < 0
  ·
    have hng' : (n : ℝ) < 0 := by exact_mod_cast hng
    have h_abs_n : |(n : ℝ)| = -(n : ℝ) := abs_of_neg hng'
    have h_abs_n_int : |n| = -n := abs_of_neg hng

    have h_atan_val : (atanEndX false n d b sl sh cl ch : ℝ) =
      if (HPI_HI : ℤ) ≤ b ∨ ((|n| : ℤ) * ch ≤ sl * d) then (-b : ℤ) else (-HPI_HI : ℤ) := by
      unfold atanEndX
      simp [hng, h_abs_n_int]

    by_cases hcheck : (HPI_HI : ℤ) ≤ b ∨ ((|n| : ℤ) * ch ≤ sl * d)
    ·
      have h_atan_eq : (atanEndX false n d b sl sh cl ch : ℝ) = (-b : ℝ) := by
        rw [h_atan_val]
        simp [hcheck]
      rw [h_atan_eq]

      by_cases h_HPI_HI_le_b : (HPI_HI : ℤ) ≤ b
      ·
        have h_HPI_HI_le_b' : (HPI_HI : ℝ) ≤ (b : ℝ) := by exact_mod_cast h_HPI_HI_le_b
        have h_neg_b_div : (-(b : ℝ)) / (2 ^ 28 : ℝ) = -β := by
          simp [hβ, div_eq_mul_inv]
        rw [h_neg_b_div]

        have h_neg_b_lt : -((b : ℝ) / (2 ^ 28 : ℝ)) ≤ -((HPI_HI : ℝ) / (2 ^ 28 : ℝ)) := by
          apply neg_le_neg
          apply div_le_div_of_nonneg_right h_HPI_HI_le_b' (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
        have h_neg_HPI_HI_lt : -((HPI_HI : ℝ) / (2 ^ 28 : ℝ)) < -(π / 2) := by
          linarith [h_pi_div_two_lt_HPI_HI_div]
        have h_neg_pi_div_two_lt_arctan_q : -(π / 2) < Real.arctan q :=
          Real.neg_pi_div_two_lt_arctan q
        linarith
      ·
        have h_not_HPI_HI : ¬ ((HPI_HI : ℤ) ≤ b) := h_HPI_HI_le_b
        have h_ineq_int : (|n| : ℤ) * ch ≤ sl * d := by
          rcases hcheck with (h | h)
          · exact absurd h h_not_HPI_HI
          · exact h
        have h_ineq_int' : (|n| : ℤ) * ch ≤ sl * d := h_ineq_int

        have h_ineq_real : (|n| : ℝ) * (ch : ℝ) ≤ (sl : ℝ) * (d : ℝ) := by
          exact_mod_cast h_ineq_int'

        have h_tan_ineq : |(n : ℝ)| * Real.cos β ≤ Real.sin β * (d : ℝ) := by
          have h_mul : (2 ^ 28 : ℝ) * |(n : ℝ)| * Real.cos β ≤ (2 ^ 28 : ℝ) * Real.sin β * (d : ℝ) := by
            nlinarith
          have hpos : (0 : ℝ) < 2 ^ 28 := by norm_num
          have h_mul' : (2 ^ 28 : ℝ) * (|(n : ℝ)| * Real.cos β) ≤ (2 ^ 28 : ℝ) * (Real.sin β * (d : ℝ)) := by
            nlinarith
          exact le_of_mul_le_mul_left h_mul' hpos

        have h_tan_ineq' : (-(n : ℝ)) * Real.cos β ≤ Real.sin β * (d : ℝ) := by
          simpa [h_abs_n] using h_tan_ineq

        have h_b_lt_HPI_HI : (b : ℤ) < HPI_HI := by
          apply lt_of_not_ge h_not_HPI_HI
        have h_b_le_HPI_LO : (b : ℤ) ≤ HPI_LO := by
          unfold HPI_HI at h_b_lt_HPI_HI
          unfold HPI_LO
          omega
        have h_b_lt_HPI_HI' : (b : ℝ) < (HPI_HI : ℝ) := by exact_mod_cast h_b_lt_HPI_HI
        have h_b_le_HPI_LO' : (b : ℝ) ≤ (HPI_LO : ℝ) := by exact_mod_cast h_b_le_HPI_LO
        have h_beta_lt_pi_div_two : β < π / 2 := by
          calc
            β = (b : ℝ) / (2 ^ 28 : ℝ) := rfl
            _ ≤ (HPI_LO : ℝ) / (2 ^ 28 : ℝ) :=
              div_le_div_of_nonneg_right h_b_le_HPI_LO' (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
            _ < π / 2 := h_HPI_LO_div_lt_pi_div_two
        have h_beta_gt_neg_pi_div_two : -(π / 2) < β := by

          have h_nonneg : 0 ≤ β := div_nonneg (by exact_mod_cast hb) (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
          linarith [Real.pi_pos, h_nonneg]

        have h_cos_pos : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
        have h_tan_bound : |(n : ℝ)| / (d : ℝ) ≤ Real.tan β := by
          rw [Real.tan_eq_sin_div_cos]
          apply (div_le_div_iff₀ hd' h_cos_pos).mpr
          nlinarith

        have h_arctan_tan_eq : Real.arctan (Real.tan β) = β :=
          Real.arctan_tan h_beta_gt_neg_pi_div_two h_beta_lt_pi_div_two
        have h_arctan_bound : Real.arctan (|(n : ℝ)| / (d : ℝ)) ≤ β := by
          calc
            Real.arctan (|(n : ℝ)| / (d : ℝ)) ≤ Real.arctan (Real.tan β) :=
              arctan_mono h_tan_bound
            _ = β := h_arctan_tan_eq

        have h_arctan_n_div_d : Real.arctan ((n : ℝ) / (d : ℝ)) ≤ Real.arctan q :=
          arctan_mono hq_div
        have h_arctan_n_div_d_eq : Real.arctan ((n : ℝ) / (d : ℝ)) = -Real.arctan (|(n : ℝ)| / (d : ℝ)) := by
          rw [h_abs_n]

          rw [neg_div]

          rw [Real.arctan_neg]

          simp

        have h_neg_b_div' : (-(b : ℝ)) / (2 ^ 28 : ℝ) = -β := by
          simp [hβ, div_eq_mul_inv]
        rw [h_neg_b_div']
        have h_goal : -β ≤ Real.arctan q := by
          linarith
        exact h_goal
    ·
      have h_atan_eq : (atanEndX false n d b sl sh cl ch : ℝ) = (-HPI_HI : ℝ) := by
        rw [h_atan_val]
        simp [hcheck]
      rw [h_atan_eq]

      have h_val : (-HPI_HI : ℝ) / (2 ^ 28 : ℝ) < -(π / 2) := by
        linarith [h_pi_div_two_lt_HPI_HI_div]
      have h_lt_arctan : -(π / 2) < Real.arctan q := Real.neg_pi_div_two_lt_arctan q
      linarith
  ·
    have hng' : ¬ ((n : ℤ) < 0) := hng
    have hn_nonneg : (0 : ℤ) ≤ n := by omega
    have hn_nonneg' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_nonneg
    have h_abs_n_int : |n| = n := abs_of_nonneg hn_nonneg
    have h_abs_n : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg hn_nonneg'

    have h_atan_val : (atanEndX false n d b sl sh cl ch : ℝ) =
      if b ≤ 0 ∨ ((sh * d : ℤ) ≤ (|n| : ℤ) * cl ∧ (0 : ℤ) ≤ cl ∧ b ≤ (HPI_LO : ℤ)) then (b : ℝ) else (-HPI_HI : ℝ) := by
      unfold atanEndX
      simp [hng, h_abs_n_int]

    by_cases hcheck : b ≤ 0 ∨ ((sh * d : ℤ) ≤ (|n| : ℤ) * cl ∧ (0 : ℤ) ≤ cl ∧ b ≤ (HPI_LO : ℤ))
    ·
      have h_atan_eq : (atanEndX false n d b sl sh cl ch : ℝ) = (b : ℝ) := by
        rw [h_atan_val]
        simp [hcheck]
      rw [h_atan_eq]

      rcases hcheck with (hb_nonpos | ⟨hineq_int, hcl_nonneg, hb_HPI_LO⟩)
      ·
        have hb_zero : (b : ℝ) = 0 := hb_zero_of_nonpos (by exact_mod_cast hb_nonpos)
        rw [hb_zero, zero_div]

        have h_n_div_d_nonneg : 0 ≤ (n : ℝ) / (d : ℝ) := div_nonneg hn_nonneg' (by exact_mod_cast hd.le)
        have h_arctan_nonneg : 0 ≤ Real.arctan ((n : ℝ) / (d : ℝ)) := by
          calc
            0 = Real.arctan 0 := by rw [Real.arctan_zero]
            _ ≤ Real.arctan ((n : ℝ) / (d : ℝ)) := arctan_mono h_n_div_d_nonneg

        have h_arctan_q_nonneg : 0 ≤ Real.arctan q := by
          linarith [arctan_mono hq_div, h_arctan_nonneg]
        exact h_arctan_q_nonneg
      ·

        have hineq_int' : (sh : ℤ) * d ≤ n * cl := by

          simpa [h_abs_n_int] using hineq_int
        have hineq_real : (sh : ℝ) * (d : ℝ) ≤ (n : ℝ) * (cl : ℝ) := by exact_mod_cast hineq_int'
        have hcl_nonneg' : (0 : ℝ) ≤ (cl : ℝ) := by exact_mod_cast hcl_nonneg
        have hb_HPI_LO' : (b : ℝ) ≤ (HPI_LO : ℝ) := by exact_mod_cast hb_HPI_LO

        have h_tan_ineq : Real.sin β * (d : ℝ) ≤ (n : ℝ) * Real.cos β := by
          have h_mul : (2 ^ 28 : ℝ) * Real.sin β * (d : ℝ) ≤ (2 ^ 28 : ℝ) * (n : ℝ) * Real.cos β := by
            nlinarith
          have hpos : (0 : ℝ) < 2 ^ 28 := by norm_num
          have h_mul' : (2 ^ 28 : ℝ) * (Real.sin β * (d : ℝ)) ≤ (2 ^ 28 : ℝ) * ((n : ℝ) * Real.cos β) := by
            nlinarith
          exact le_of_mul_le_mul_left h_mul' hpos

        have h_beta_lt_pi_div_two : β < π / 2 := by
          calc
            β = (b : ℝ) / (2 ^ 28 : ℝ) := rfl
            _ ≤ (HPI_LO : ℝ) / (2 ^ 28 : ℝ) :=
              div_le_div_of_nonneg_right hb_HPI_LO' (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
            _ < π / 2 := h_HPI_LO_div_lt_pi_div_two
        have h_beta_gt_neg_pi_div_two : -(π / 2) < β := by
          have h_nonneg : 0 ≤ β := div_nonneg (by exact_mod_cast hb) (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
          linarith [Real.pi_pos, h_nonneg]
        have h_cos_pos : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

        have h_tan_bound : Real.tan β ≤ (n : ℝ) / (d : ℝ) := by
          rw [Real.tan_eq_sin_div_cos]
          apply (div_le_div_iff₀ h_cos_pos hd').mpr
          nlinarith

        have h_arctan_tan_eq : Real.arctan (Real.tan β) = β :=
          Real.arctan_tan h_beta_gt_neg_pi_div_two h_beta_lt_pi_div_two

        calc
          β = Real.arctan (Real.tan β) := by rw [h_arctan_tan_eq]
          _ ≤ Real.arctan ((n : ℝ) / (d : ℝ)) := arctan_mono h_tan_bound
          _ ≤ Real.arctan q := arctan_mono hq_div
    ·
      have h_atan_eq : (atanEndX false n d b sl sh cl ch : ℝ) = (-HPI_HI : ℝ) := by
        rw [h_atan_val]
        simp [hcheck]
      rw [h_atan_eq]

      have h_val : (-HPI_HI : ℝ) / (2 ^ 28 : ℝ) < -(π / 2) := by
        linarith [h_pi_div_two_lt_HPI_HI_div]
      have h_lt_arctan : -(π / 2) < Real.arctan q := Real.neg_pi_div_two_lt_arctan q
      linarith

namespace H_atanEndX_hi_sound
set_option maxHeartbeats 400000

private lemma hpi_lo_lt_pi_mul_two_pow_27 : (HPI_LO : ℝ) < Real.pi * (2 ^ 27 : ℝ) := by
  have h : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have h_num : (HPI_LO : ℝ) < (3.14159265358979323846 : ℝ) * (2 ^ 27 : ℝ) := by

    have h_int : ((HPI_LO : ℕ) : ℤ) * 100000000000000000000 < 314159265358979323846 * 134217728 := by
      simpa [HPI_LO] using (by norm_num : (421657428 : ℤ) * 100000000000000000000 < 314159265358979323846 * 134217728)
    have h_real : (HPI_LO : ℝ) * (100000000000000000000 : ℝ) < (314159265358979323846 : ℝ) * (134217728 : ℝ) := by
      simpa [HPI_LO] using mod_cast h_int
    have h_eq : (3.14159265358979323846 : ℝ) * (2 ^ 27 : ℝ) = ((314159265358979323846 : ℝ) * (134217728 : ℝ)) / (100000000000000000000 : ℝ) := by
      norm_num
    rw [h_eq]
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 100000000000000000000)).mpr
    exact h_real
  linarith

private lemma pi_mul_two_pow_27_lt_hpi_hi : Real.pi * (2 ^ 27 : ℝ) < (HPI_HI : ℝ) := by
  have h : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_num : (3.14159265358979323847 : ℝ) * (2 ^ 27 : ℝ) < (HPI_HI : ℝ) := by

    have h_int : 314159265358979323847 * 134217728 < ((HPI_HI : ℤ) : ℤ) * 100000000000000000000 := by
      simpa [HPI_HI] using (by norm_num : 314159265358979323847 * 134217728 < (421657429 : ℤ) * 100000000000000000000)
    have h_real : (314159265358979323847 : ℝ) * (134217728 : ℝ) < (HPI_HI : ℝ) * (100000000000000000000 : ℝ) := by
      exact mod_cast h_int
    have h_eq : (3.14159265358979323847 : ℝ) * (2 ^ 27 : ℝ) = ((314159265358979323847 : ℝ) * (134217728 : ℝ)) / (100000000000000000000 : ℝ) := by
      norm_num
    rw [h_eq]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 100000000000000000000)).mpr
    exact h_real
  linarith

private lemma beta_lt_pi_div_two_of_lt_hpi_hi {b : ℤ} (hb_lt : (b : ℤ) < (HPI_HI : ℤ)) : (b : ℝ) / (2 ^ 28 : ℝ) < Real.pi / 2 := by
  have hb_le_HPI_HI_sub_one : (b : ℤ) ≤ (HPI_HI : ℤ) - 1 := by omega
  have hb_le' : (b : ℝ) ≤ ((HPI_HI : ℤ) - 1 : ℤ) := by exact mod_cast hb_le_HPI_HI_sub_one
  have h_HPI_sub_one_lt : ((HPI_HI : ℤ) - 1 : ℝ) < Real.pi * (2 ^ 27 : ℝ) := by

    have : ((HPI_HI : ℤ) - 1 : ℝ) = (HPI_LO : ℝ) := by
      have h : (HPI_HI : ℤ) - 1 = (HPI_LO : ℤ) := by
        simp [HPI_HI, HPI_LO]
      exact mod_cast h
    rw [this]
    exact hpi_lo_lt_pi_mul_two_pow_27
  calc
    (b : ℝ) / (2 ^ 28 : ℝ) ≤ ((HPI_HI : ℤ) - 1 : ℝ) / (2 ^ 28 : ℝ) := by
      refine ((div_le_div_iff_of_pos_right (by norm_num)).mpr ?_)
      exact mod_cast hb_le_HPI_HI_sub_one
    _ < (Real.pi * (2 ^ 27 : ℝ)) / (2 ^ 28 : ℝ) := by
      refine ((div_lt_div_iff_of_pos_right (by norm_num)).mpr h_HPI_sub_one_lt)
    _ = Real.pi / 2 := by
      field_simp [show (2 ^ 28 : ℝ) ≠ 0 from by norm_num]

private lemma beta_nonneg_and_lt_pi_div_two_of_le_hpi_lo {b : ℤ} (hb_nonneg : 0 ≤ (b : ℤ)) (hb_le : (b : ℤ) ≤ (HPI_LO : ℤ)) :
    0 ≤ (b : ℝ) / (2 ^ 28 : ℝ) ∧ (b : ℝ) / (2 ^ 28 : ℝ) < Real.pi / 2 := by
  have hb_nonneg' : 0 ≤ (b : ℝ) := by exact mod_cast hb_nonneg
  have hb_le' : (b : ℝ) ≤ (HPI_LO : ℝ) := by exact mod_cast hb_le
  have h_div_nonneg : 0 ≤ (b : ℝ) / (2 ^ 28 : ℝ) := div_nonneg hb_nonneg' (by norm_num)
  have h_HPI_LO_lt_pi_mul : (HPI_LO : ℝ) < Real.pi * (2 ^ 27 : ℝ) := hpi_lo_lt_pi_mul_two_pow_27
  have h_div_lt : (b : ℝ) / (2 ^ 28 : ℝ) < Real.pi / 2 := by
    calc
      (b : ℝ) / (2 ^ 28 : ℝ) ≤ (HPI_LO : ℝ) / (2 ^ 28 : ℝ) := by
        refine ((div_le_div_iff_of_pos_right (by norm_num)).mpr hb_le')
      _ < (Real.pi * (2 ^ 27 : ℝ)) / (2 ^ 28 : ℝ) := by
        refine ((div_lt_div_iff_of_pos_right (by norm_num)).mpr h_HPI_LO_lt_pi_mul)
      _ = Real.pi / 2 := by
        field_simp [show (2 ^ 28 : ℝ) ≠ 0 from by norm_num]
  exact ⟨h_div_nonneg, h_div_lt⟩
end H_atanEndX_hi_sound

set_option maxHeartbeats 400000 in
open H_atanEndX_hi_sound in
theorem atanEndX_hi_sound (n d b sl sh cl ch : ℤ) (hd : 0 < d) (hb : 0 ≤ b)
    (hs : (sl : ℝ) ≤ 2 ^ 28 * Real.sin ((b : ℝ) / 2 ^ 28) ∧ 2 ^ 28 * Real.sin ((b : ℝ) / 2 ^ 28) ≤ sh)
    (hc : (cl : ℝ) ≤ 2 ^ 28 * Real.cos ((b : ℝ) / 2 ^ 28) ∧ 2 ^ 28 * Real.cos ((b : ℝ) / 2 ^ 28) ≤ ch)
    (q : ℝ) (hq : q ≤ (n : ℝ) / d) :
    Real.arctan q ≤ (atanEndX true n d b sl sh cl ch : ℝ) / 2 ^ 28 := by
  rcases hs with ⟨hsl, hsh⟩
  rcases hc with ⟨hcl, hch⟩
  have h2pow_pos : 0 < (2 ^ 28 : ℝ) := by norm_num
  have hd' : 0 < (d : ℝ) := by exact mod_cast hd
  have hb' : 0 ≤ (b : ℝ) := by exact mod_cast hb
  set β := (b : ℝ) / (2 ^ 28 : ℝ) with hβdef
  have harctan_q_le_arctan_div : Real.arctan q ≤ Real.arctan ((n : ℝ) / (d : ℝ)) :=
    Real.arctan_mono hq
  have harctan_div_lt_pi_div_two : Real.arctan ((n : ℝ) / (d : ℝ)) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _

  by_cases hn : (n : ℤ) < 0
  ·

    have hn' : (n : ℝ) < 0 := by exact mod_cast hn
    have h_abs_n : |(n : ℝ)| = -(n : ℝ) := abs_of_neg hn'
    by_cases hb0 : (b : ℤ) ≤ 0
    ·
      have hb0' : (b : ℝ) ≤ 0 := by exact mod_cast hb0
      have h_div_nonpos : (n : ℝ) / (d : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hn'.le hd'.le
      have harctan_div_nonpos : Real.arctan ((n : ℝ) / (d : ℝ)) ≤ 0 :=
        (Real.arctan_le_zero.mpr h_div_nonpos)
      have harctan_q_nonpos : Real.arctan q ≤ 0 :=
        harctan_q_le_arctan_div.trans harctan_div_nonpos
      have h_neg_b_nonneg : 0 ≤ (-b : ℝ) / (2 ^ 28 : ℝ) := by
        refine div_nonneg (by linarith) (by norm_num)
      have h_val : (atanEndX true n d b sl sh cl ch : ℝ) = (-b : ℝ) := by
        have : atanEndX true n d b sl sh cl ch = (-b : ℤ) := by
          simp [atanEndX, hn, hb0]
        exact mod_cast this
      rw [h_val]

      linarith
    ·
      by_cases h_clo : (b ≤ 0 ∨ (sh * d ≤ |n| * cl ∧ 0 ≤ cl ∧ (b : ℤ) ≤ (HPI_LO : ℤ)))
      ·
        have h_clo' : (sh * d ≤ |n| * cl ∧ 0 ≤ cl ∧ (b : ℤ) ≤ (HPI_LO : ℤ)) := by
          rcases h_clo with (h | h)
          · exfalso; exact hb0 h
          · exact h
        rcases h_clo' with ⟨h_shd_le_absn_cl, h_cl_nonneg, h_b_le_HPI_LO⟩

        have h_ineq_int : sh * d ≤ |n| * cl := h_shd_le_absn_cl
        have h_ineq_real : (sh : ℝ) * (d : ℝ) ≤ |(n : ℝ)| * (cl : ℝ) := by exact mod_cast h_ineq_int

        have h_sin_ineq : (2 ^ 28 : ℝ) * Real.sin β ≤ (sh : ℝ) := hsh
        have h_cos_ineq : (cl : ℝ) ≤ (2 ^ 28 : ℝ) * Real.cos β := hcl

        have h_combined : (2 ^ 28 : ℝ) * Real.sin β * (d : ℝ) ≤ |(n : ℝ)| * (2 ^ 28 : ℝ) * Real.cos β := by
          nlinarith

        have h_sin_d_le_absn_cos : Real.sin β * (d : ℝ) ≤ |(n : ℝ)| * Real.cos β := by
          nlinarith

        have h_beta_bounds : 0 ≤ β ∧ β < Real.pi / 2 :=
          beta_nonneg_and_lt_pi_div_two_of_le_hpi_lo hb h_b_le_HPI_LO
        rcases h_beta_bounds with ⟨hβ_nonneg, hβ_lt_pi_div_two⟩
        have h_cos_pos : 0 < Real.cos β :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith, hβ_lt_pi_div_two⟩

        have h_tan_ineq : Real.tan β ≤ |(n : ℝ)| / (d : ℝ) := by
          rw [Real.tan_eq_sin_div_cos]

          field_simp [ne_of_gt hd', ne_of_gt h_cos_pos]
          nlinarith

        have h_arctan_tan_β : Real.arctan (Real.tan β) = β := by
          refine Real.arctan_tan (by linarith) hβ_lt_pi_div_two

        have h_arctan_tan_le_arctan_abs_div : Real.arctan (Real.tan β) ≤ Real.arctan (|(n : ℝ)| / (d : ℝ)) :=
          Real.arctan_mono h_tan_ineq

        have h_arctan_abs_div : Real.arctan (|(n : ℝ)| / (d : ℝ)) = -Real.arctan ((n : ℝ) / (d : ℝ)) := by
          rw [h_abs_n, neg_div, Real.arctan_neg]

        have h_arctan_div_le_neg_β : Real.arctan ((n : ℝ) / (d : ℝ)) ≤ -β := by
          calc
            Real.arctan ((n : ℝ) / (d : ℝ)) = -Real.arctan (|(n : ℝ)| / (d : ℝ)) := by
              rw [h_arctan_abs_div, neg_neg]
            _ ≤ -Real.arctan (Real.tan β) := by

              have h : Real.arctan (Real.tan β) ≤ Real.arctan (|(n : ℝ)| / (d : ℝ)) :=
                Real.arctan_mono h_tan_ineq
              linarith
            _ = -β := by rw [h_arctan_tan_β]

        have h_val : (atanEndX true n d b sl sh cl ch : ℝ) = (-b : ℝ) := by
          have : atanEndX true n d b sl sh cl ch = (-b : ℤ) := by
            simp [atanEndX, hn, h_clo]
          exact mod_cast this
        rw [h_val]

        have h_neg_div : (-b : ℝ) / (2 ^ 28 : ℝ) = -β := by
          rw [hβdef, neg_div]
        rw [h_neg_div]

        exact harctan_q_le_arctan_div.trans h_arctan_div_le_neg_β
      ·
        have h_val : (atanEndX true n d b sl sh cl ch : ℝ) = (HPI_HI : ℝ) := by
          have : atanEndX true n d b sl sh cl ch = (HPI_HI : ℤ) := by
            simp [atanEndX, hn, h_clo]
          exact mod_cast this
        rw [h_val]

        have h_HPI_HI_div_gt_pi_div_two : Real.pi / 2 < (HPI_HI : ℝ) / (2 ^ 28 : ℝ) := by
          have h : Real.pi * (2 ^ 27 : ℝ) < (HPI_HI : ℝ) := pi_mul_two_pow_27_lt_hpi_hi
          calc
            Real.pi / 2 = (Real.pi * (2 ^ 27 : ℝ)) / (2 ^ 28 : ℝ) := by
              field_simp [show (2 ^ 28 : ℝ) ≠ 0 from by norm_num]
            _ < (HPI_HI : ℝ) / (2 ^ 28 : ℝ) := by
              refine ((div_lt_div_iff_of_pos_right (by norm_num)).mpr h)
        have : Real.arctan q < (HPI_HI : ℝ) / (2 ^ 28 : ℝ) := by
          linarith
        exact this.le
  ·

    have hn' : 0 ≤ (n : ℤ) := by omega
    have hn'' : 0 ≤ (n : ℝ) := by exact mod_cast hn'
    have h_abs_n : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg hn''

    by_cases h_chi : ((HPI_HI : ℤ) ≤ b ∨ |n| * ch ≤ sl * d)
    ·
      by_cases h_HPI_HI_le_b : (HPI_HI : ℤ) ≤ b
      ·
        have h_HPI_HI_le_b' : (HPI_HI : ℝ) ≤ (b : ℝ) := by exact mod_cast h_HPI_HI_le_b
        have h_val : (atanEndX true n d b sl sh cl ch : ℝ) = (b : ℝ) := by
          have : atanEndX true n d b sl sh cl ch = (b : ℤ) := by
            simp [atanEndX, hn, h_chi]
          exact mod_cast this
        rw [h_val]

        have h_HPI_HI_div_gt_pi_div_two : Real.pi / 2 < (HPI_HI : ℝ) / (2 ^ 28 : ℝ) := by
          have h : Real.pi * (2 ^ 27 : ℝ) < (HPI_HI : ℝ) := pi_mul_two_pow_27_lt_hpi_hi
          calc
            Real.pi / 2 = (Real.pi * (2 ^ 27 : ℝ)) / (2 ^ 28 : ℝ) := by
              field_simp [show (2 ^ 28 : ℝ) ≠ 0 from by norm_num]
            _ < (HPI_HI : ℝ) / (2 ^ 28 : ℝ) := by
              refine ((div_lt_div_iff_of_pos_right (by norm_num)).mpr h)
        have h_β_ge_HPI_div : (HPI_HI : ℝ) / (2 ^ 28 : ℝ) ≤ β := by
          refine ((div_le_div_iff_of_pos_right (by norm_num)).mpr h_HPI_HI_le_b')
        have h_arctan_q_lt_β : Real.arctan q < β := by
          linarith
        exact h_arctan_q_lt_β.le
      ·
        have h_r_l : |n| * ch ≤ sl * d := by
          rcases h_chi with (h | h)
          · exfalso; exact h_HPI_HI_le_b h
          · exact h

        have h_val : (atanEndX true n d b sl sh cl ch : ℝ) = (b : ℝ) := by
          have : atanEndX true n d b sl sh cl ch = (b : ℤ) := by
            simp [atanEndX, hn, h_chi]
          exact mod_cast this
        rw [h_val]

        have h_ineq_int : |n| * ch ≤ sl * d := h_r_l
        have h_ineq_real : |(n : ℝ)| * (ch : ℝ) ≤ (sl : ℝ) * (d : ℝ) := by exact mod_cast h_ineq_int

        have h_sin_ineq : (sl : ℝ) ≤ (2 ^ 28 : ℝ) * Real.sin β := hsl
        have h_cos_ineq : (2 ^ 28 : ℝ) * Real.cos β ≤ (ch : ℝ) := hch

        have h_combined : |(n : ℝ)| * (2 ^ 28 : ℝ) * Real.cos β ≤ (2 ^ 28 : ℝ) * Real.sin β * (d : ℝ) := by
          nlinarith

        have h_absn_cos_le_sin_d : |(n : ℝ)| * Real.cos β ≤ Real.sin β * (d : ℝ) := by
          nlinarith

        have hb_lt_HPI_HI : (b : ℤ) < (HPI_HI : ℤ) := by

          omega
        have hβ_lt_pi_div_two : β < Real.pi / 2 :=
          beta_lt_pi_div_two_of_lt_hpi_hi hb_lt_HPI_HI
        have hβ_nonneg : 0 ≤ β := div_nonneg hb' (by norm_num)
        have h_cos_pos : 0 < Real.cos β :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith, hβ_lt_pi_div_two⟩

        have h_abs_div_le_tan : |(n : ℝ)| / (d : ℝ) ≤ Real.tan β := by
          rw [Real.tan_eq_sin_div_cos]
          field_simp [ne_of_gt hd', ne_of_gt h_cos_pos]
          nlinarith

        have h_n_div_le_tan : (n : ℝ) / (d : ℝ) ≤ Real.tan β := by
          rw [← h_abs_n]
          exact h_abs_div_le_tan

        have h_arctan_div_le_β : Real.arctan ((n : ℝ) / (d : ℝ)) ≤ β := by
          calc
            Real.arctan ((n : ℝ) / (d : ℝ)) ≤ Real.arctan (Real.tan β) :=
              Real.arctan_mono h_n_div_le_tan
            _ = β := Real.arctan_tan (by linarith) hβ_lt_pi_div_two

        exact harctan_q_le_arctan_div.trans h_arctan_div_le_β
    ·
      have h_val : (atanEndX true n d b sl sh cl ch : ℝ) = (HPI_HI : ℝ) := by
        have : atanEndX true n d b sl sh cl ch = (HPI_HI : ℤ) := by
          simp [atanEndX, hn, h_chi]
        exact mod_cast this
      rw [h_val]

      have h_HPI_HI_div_gt_pi_div_two : Real.pi / 2 < (HPI_HI : ℝ) / (2 ^ 28 : ℝ) := by
        have h : Real.pi * (2 ^ 27 : ℝ) < (HPI_HI : ℝ) := pi_mul_two_pow_27_lt_hpi_hi
        calc
          Real.pi / 2 = (Real.pi * (2 ^ 27 : ℝ)) / (2 ^ 28 : ℝ) := by
            field_simp [show (2 ^ 28 : ℝ) ≠ 0 from by norm_num]
          _ < (HPI_HI : ℝ) / (2 ^ 28 : ℝ) := by
            refine ((div_lt_div_iff_of_pos_right (by norm_num)).mpr h)
      have : Real.arctan q < (HPI_HI : ℝ) / (2 ^ 28 : ℝ) := by
        linarith
      exact this.le

theorem pair_lt_neg_one (n d : ℤ) (hd : 0 < d) : n < -d ↔ (n : ℝ) / d < -1 := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  constructor
  · intro h
    have h' : (n : ℝ) < (-d : ℝ) := by exact_mod_cast h
    rw [div_lt_iff₀ hd']
    simpa [Int.cast_neg d] using h'
  · intro h
    rw [div_lt_iff₀ hd'] at h
    have h' : (n : ℝ) < (-d : ℝ) := by
      simpa [Int.cast_neg d] using h
    exact_mod_cast h'

theorem pair_one_le (n d : ℤ) (hd : 0 < d) : d ≤ n ↔ 1 ≤ (n : ℝ) / d := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [← Int.cast_le (R := ℝ), ← one_le_div hd']

def decTestX (full : Bool) (t1lo nl dl nh dh yl yh : ℤ) : Bool :=
  let al := decide (nl < 0)
  let pa := !al
  let ah := decide (0 < nh)
  let na := !ah && al
  let za := al && ah
  let bl := decide (yl < 0)
  let pb := !bl
  let bh := decide (0 < yh)
  let nbg := !bh && bl
  let zb := bl && bh
  let both := za && zb
  let m := nbg || (pa && zb)
  let xn := if m then nh else nl
  let xd := if m then dh else dl
  let t := if full then za && !nbg else za && pb
  let y := if na || t then yh else yl
  let r1 := decide (-t1lo * xd < xn * y)
  if full then r1 && (!both || decide (-t1lo * dh < nh * yl)) else r1

theorem decTestX_sound (full : Bool) (t1lo nl dl nh dh yl yh : ℤ) (hdl : 0 < dl) (hdh : 0 < dh)
    (hfull : full = true ∨ ¬(nl < 0 ∧ 0 < nh ∧ yl < 0 ∧ 0 < yh))
    (h : decTestX full t1lo nl dl nh dh yl yh = true)
    (t1 x y : ℝ) (ht : (t1lo : ℝ) ≤ t1) (hx : (nl : ℝ) / dl ≤ x ∧ x ≤ (nh : ℝ) / dh) (hy : (yl : ℝ) ≤ y ∧ y ≤ yh) :
    0 < t1 + x * y := by
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hyc, hyd⟩ := hy
  have hdl' : (0 : ℝ) < dl := by exact_mod_cast hdl
  have hdh' : (0 : ℝ) < dh := by exact_mod_cast hdh

  have key : ∀ xn xd yv : ℤ, 0 < xd → -t1lo * xd < xn * yv → 0 < (t1lo : ℝ) + (xn : ℝ) / xd * yv := by
    intro xn xd yv hxd hlt
    have hxd' : (0 : ℝ) < xd := by exact_mod_cast hxd
    have hlt' : -(t1lo : ℝ) * xd < (xn : ℝ) * yv := by exact_mod_cast hlt
    have e : (t1lo : ℝ) + (xn : ℝ) / xd * yv = ((t1lo : ℝ) * xd + xn * yv) / xd := by field_simp
    rw [e]
    exact div_pos (by linarith) hxd'
  suffices hs : 0 < (t1lo : ℝ) + x * y by linarith
  have kac := key nl dl yl hdl
  have kad := key nl dl yh hdl
  have kbc := key nh dh yl hdh
  have kbd := key nh dh yh hdh
  unfold decTestX at h

  by_cases h1 : nl < 0
  · have ha : (nl : ℝ) / dl ≤ 0 := (div_neg_of_neg_of_pos (by exact_mod_cast h1) hdl').le
    by_cases h2 : 0 < nh
    · have hb : 0 ≤ (nh : ℝ) / dh := (div_pos (by exact_mod_cast h2) hdh').le
      by_cases h3 : yl < 0
      · by_cases h4 : 0 < yh
        ·
          cases full
          · simp [h1, h2, h3, h4] at hfull
          · simp [h1, h2, h3, h4] at h
            have e1 := kad (by linarith [h.1])
            have e2 := kbc (by linarith [h.2])
            by_cases hy0 : 0 ≤ y
            · nlinarith [mul_nonneg (sub_nonneg.2 hxa) hy0, mul_nonneg_of_nonpos_of_nonpos ha (sub_nonpos.2 hyd)]
            · push_neg at hy0
              nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hxb) hy0.le, mul_nonneg hb (sub_nonneg.2 hyc)]
        ·
          have hd : (yh : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp h4
          have e := kbc (by cases full <;> simp [h1, h2, h3, h4] at h <;> linarith)
          have hy0 : y ≤ 0 := by linarith
          nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hxb) hy0, mul_nonneg hb (sub_nonneg.2 hyc)]
      ·
        have hc : (0 : ℝ) ≤ yl := by exact_mod_cast not_lt.mp h3
        have hy0 : 0 ≤ y := by linarith
        have e := kad (by cases full <;> by_cases h4 : 0 < yh <;> simp [h1, h2, h3, h4] at h <;> linarith)
        nlinarith [mul_nonneg (sub_nonneg.2 hxa) hy0, mul_nonneg_of_nonpos_of_nonpos ha (sub_nonpos.2 hyd)]
    ·
      have hb : (nh : ℝ) / dh ≤ 0 := by
        rw [div_le_iff₀ hdh', zero_mul]
        exact_mod_cast not_lt.mp h2
      have hx0 : x ≤ 0 := by linarith
      by_cases h3 : yl < 0
      · by_cases h4 : 0 < yh
        ·
          have hd : (0 : ℝ) ≤ yh := by exact_mod_cast h4.le
          have e := kad (by cases full <;> simp [h1, h2, h3, h4] at h <;> linarith)
          nlinarith [mul_nonneg_of_nonpos_of_nonpos hx0 (sub_nonpos.2 hyd), mul_nonneg hd (sub_nonneg.2 hxa)]
        ·
          have hd : (yh : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp h4
          have hy0 : y ≤ 0 := by linarith
          have e := kbd (by cases full <;> simp [h1, h2, h3, h4] at h <;> linarith)
          nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hxb) hy0,
            mul_nonneg_of_nonpos_of_nonpos hb (sub_nonpos.2 hyd)]
      ·
        have hc : (0 : ℝ) ≤ yl := by exact_mod_cast not_lt.mp h3
        have hy0 : 0 ≤ y := by linarith
        have e := kad (by cases full <;> by_cases h4 : 0 < yh <;> simp [h1, h2, h3, h4] at h <;> linarith)
        nlinarith [mul_nonneg (sub_nonneg.2 hxa) hy0, mul_nonneg_of_nonpos_of_nonpos ha (sub_nonpos.2 hyd)]
  ·
    have ha : 0 ≤ (nl : ℝ) / dl := div_nonneg (by exact_mod_cast not_lt.mp h1) hdl'.le
    have hx0 : 0 ≤ x := by linarith
    by_cases h3 : yl < 0
    ·
      have hc : (yl : ℝ) ≤ 0 := by exact_mod_cast h3.le
      have e := kbc (by
        cases full <;> by_cases h2 : 0 < nh <;> by_cases h4 : 0 < yh <;> simp [h1, h2, h3, h4] at h <;> linarith)
      nlinarith [mul_nonneg hx0 (sub_nonneg.2 hyc), mul_nonneg_of_nonpos_of_nonpos hc (sub_nonpos.2 hxb)]
    ·
      have hc : (0 : ℝ) ≤ yl := by exact_mod_cast not_lt.mp h3
      have hy0 : 0 ≤ y := by linarith
      have e := kac (by
        cases full <;> by_cases h2 : 0 < nh <;> by_cases h4 : 0 < yh <;> simp [h1, h2, h3, h4] at h <;> linarith)
      nlinarith [mul_nonneg (sub_nonneg.2 hxa) hy0, mul_nonneg ha (sub_nonneg.2 hyc)]

def isinX (E xl xh sl sh : ℤ) : ℤ × ℤ :=
  (min sl sh - E, if xl < HPI_HI + 1 ∧ (HPI_LO : ℤ) - 1 < xh then 2 ^ 28 else min (max sl sh + E) (2 ^ 28))

def icosX (E xl xh cl ch : ℤ) : ℤ × ℤ :=
  (if (PI_LO : ℤ) - 1 < xh then -2 ^ 28 else ch - E, if xl < 1 then 2 ^ 28 else cl + E)

namespace H_isinX_sound
set_option maxHeartbeats 400000

private lemma sin_decreasing_on_Icc_pi_div_two_three_pi_div_two {x y : ℝ} (hx : π/2 ≤ x) (hy : y ≤ 3*π/2) (hxy : x ≤ y) :
    Real.sin y ≤ Real.sin x := by
  have hx' : -(π/2) ≤ π - y := by linarith
  have hy' : π - x ≤ π/2 := by linarith
  have h_sub : π - y ≤ π - x := by linarith
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two hx' hy' h_sub
  rw [Real.sin_pi_sub, Real.sin_pi_sub] at h
  exact h

private lemma hpi_lo_div_two_pow_lt_pi_div_two : ((HPI_LO : ℤ) : ℝ) / (2 ^ 28 : ℝ) < π/2 := by
  have h2pow_pos : 0 < (2 : ℝ) ^ 28 := by norm_num
  field_simp [h2pow_pos.ne.symm]
  have hpi_gt : 3.14159265358979323846 < π := Real.pi_gt_d20
  have h_hpi_lo : ((HPI_LO : ℤ) : ℝ) * 2 < 3.14159265358979323846 * ((2 : ℝ) ^ 28) := by
    dsimp [HPI_LO]
    norm_num
  have h_pi_mul : 3.14159265358979323846 * ((2 : ℝ) ^ 28) < π * ((2 : ℝ) ^ 28) := by
    exact mul_lt_mul_of_pos_right hpi_gt h2pow_pos
  linarith

private lemma pi_div_two_lt_hpi_hi_div_two_pow : π/2 < ((HPI_HI : ℤ) : ℝ) / (2 ^ 28 : ℝ) := by
  have h2pow_pos : 0 < (2 : ℝ) ^ 28 := by norm_num
  field_simp [h2pow_pos.ne.symm]
  have hpi_lt : π < 3.14159265358979323847 := Real.pi_lt_d20
  have h_hpi_hi : 3.14159265358979323847 * ((2 : ℝ) ^ 28) < ((HPI_HI : ℤ) : ℝ) * 2 := by
    dsimp [HPI_HI]
    norm_num
  have h_pi_mul : π * ((2 : ℝ) ^ 28) < 3.14159265358979323847 * ((2 : ℝ) ^ 28) := by
    exact mul_lt_mul_of_pos_right hpi_lt h2pow_pos
  linarith
end H_isinX_sound

set_option maxHeartbeats 400000 in
open H_isinX_sound in
theorem isinX_sound (E xl xh sl sh : ℤ) (h0 : 0 ≤ xl) (h1 : xh ≤ (PI_LO : ℤ) + 1)
    (hsl : |(sl : ℝ) - 2 ^ 28 * Real.sin ((xl : ℝ) / 2 ^ 28)| ≤ (E : ℝ))
    (hsh : |(sh : ℝ) - 2 ^ 28 * Real.sin ((xh : ℝ) / 2 ^ 28)| ≤ (E : ℝ))
    (t : ℝ) (ht : (xl : ℝ) ≤ t ∧ t ≤ xh) :
    ((isinX E xl xh sl sh).1 : ℝ) ≤ 2 ^ 28 * Real.sin (t / 2 ^ 28) ∧
      2 ^ 28 * Real.sin (t / 2 ^ 28) ≤ ((isinX E xl xh sl sh).2 : ℝ) := by
  rcases ht with ⟨htl, htr⟩
  have h2pow_pos : (0 : ℝ) < 2 ^ 28 := by norm_num
  have h2pow_nonneg : 0 ≤ (2 : ℝ) ^ 28 := by positivity
  set a := (xl : ℝ) / (2 : ℝ) ^ 28 with ha
  set b := (xh : ℝ) / (2 : ℝ) ^ 28 with hb
  set s := t / (2 : ℝ) ^ 28 with hs
  have ha0 : 0 ≤ a := by
    rw [ha]
    have hxl0 : (0 : ℝ) ≤ (xl : ℝ) := by exact_mod_cast h0
    positivity
  have hab : a ≤ b := by
    rw [ha, hb]
    have hxl_le_xh : (xl : ℝ) ≤ (xh : ℝ) := by linarith
    gcongr
  have ha_le_s : a ≤ s := by
    rw [ha, hs]
    gcongr
  have hs_le_b : s ≤ b := by
    rw [hs, hb]
    gcongr
  have hb_le_pi_plus : b ≤ ((PI_LO : ℤ) + 1 : ℝ) / (2 : ℝ) ^ 28 := by
    rw [hb]
    have hxh : (xh : ℝ) ≤ ((PI_LO : ℤ) + 1 : ℝ) := by exact_mod_cast h1
    gcongr
  have hb_lt_three_pi_div_two : b < 3 * π / 2 := by
    have h_pi_plus_lt_4 : ((PI_LO : ℤ) + 1 : ℝ) / (2 : ℝ) ^ 28 < 4 := by
      dsimp [PI_LO]
      norm_num

    have h_4_lt_three_pi_div_two : 4 < 3 * π / 2 := by
      have hpi_gt_3 : 3 < π := Real.pi_gt_three
      linarith
    linarith

  rcases abs_le.mp hsl with ⟨hsl_low, hsl_high⟩
  rcases abs_le.mp hsh with ⟨hsh_low, hsh_high⟩
  have hsl_le : (sl : ℝ) - (E : ℝ) ≤ (2 : ℝ) ^ 28 * Real.sin a := by linarith
  have hsh_le : (sh : ℝ) - (E : ℝ) ≤ (2 : ℝ) ^ 28 * Real.sin b := by linarith
  have hsin_a_le_sl : (2 : ℝ) ^ 28 * Real.sin a ≤ (sl : ℝ) + (E : ℝ) := by linarith
  have hsin_b_le_sh : (2 : ℝ) ^ 28 * Real.sin b ≤ (sh : ℝ) + (E : ℝ) := by linarith

  have h_sin_ge_min : min (Real.sin a) (Real.sin b) ≤ Real.sin s := by
    by_cases hb_le_pi2 : b ≤ π/2
    ·
      have h_min_eq : min (Real.sin a) (Real.sin b) = Real.sin a :=
        min_eq_left (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hab)
      rw [h_min_eq]
      refine Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) ha_le_s
    ·
      by_cases ha_ge_pi2 : π/2 ≤ a
      ·
        have h_min_eq : min (Real.sin a) (Real.sin b) = Real.sin b :=
          min_eq_right (sin_decreasing_on_Icc_pi_div_two_three_pi_div_two ha_ge_pi2
            (by linarith [hb_lt_three_pi_div_two]) hab)
        rw [h_min_eq]
        have h_pi2_le_s : π/2 ≤ s := by linarith
        exact sin_decreasing_on_Icc_pi_div_two_three_pi_div_two h_pi2_le_s
          (by linarith [hb_lt_three_pi_div_two]) hs_le_b
      ·
        by_cases hs_le_pi2 : s ≤ π/2
        ·
          have h_min_le_sin_a : min (Real.sin a) (Real.sin b) ≤ Real.sin a := min_le_left _ _
          have h_sin_a_le_sin_s : Real.sin a ≤ Real.sin s :=
            Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) ha_le_s
          linarith
        ·
          have h_min_le_sin_b : min (Real.sin a) (Real.sin b) ≤ Real.sin b := min_le_right _ _
          have h_pi2_le_s : π/2 ≤ s := by linarith
          have h_sin_b_le_sin_s : Real.sin b ≤ Real.sin s :=
            sin_decreasing_on_Icc_pi_div_two_three_pi_div_two h_pi2_le_s
              (by linarith [hb_lt_three_pi_div_two]) hs_le_b
          linarith

  have h_sin_le_max_of_not_contains_pi2 : ¬ ((xl < (HPI_HI : ℤ) + 1) ∧ ((HPI_LO : ℤ) - 1 < xh)) → Real.sin s ≤ max (Real.sin a) (Real.sin b) := by
    intro h_not_contains
    rcases not_and_or.mp h_not_contains with (hxl | hxh)
    ·
      have ha_gt_pi2 : π/2 < a := by
        have hxl' : (HPI_HI : ℤ) + 1 ≤ xl := by omega
        have hxl_real : ((HPI_HI : ℤ) + 1 : ℝ) ≤ (xl : ℝ) := by exact_mod_cast hxl'
        rw [ha]
        calc
          π/2 < ((HPI_HI : ℤ) : ℝ) / (2 : ℝ) ^ 28 := pi_div_two_lt_hpi_hi_div_two_pow
          _ ≤ ((HPI_HI : ℤ) + 1 : ℝ) / (2 : ℝ) ^ 28 := by gcongr; norm_num
          _ ≤ (xl : ℝ) / (2 : ℝ) ^ 28 := by gcongr
      have h_sin_s_le_sin_a : Real.sin s ≤ Real.sin a :=
        sin_decreasing_on_Icc_pi_div_two_three_pi_div_two (by linarith)
          (by linarith [hb_lt_three_pi_div_two]) ha_le_s
      have h_sin_a_le_max : Real.sin a ≤ max (Real.sin a) (Real.sin b) := le_max_left _ _
      linarith
    ·
      have hb_lt_pi2 : b < π/2 := by
        have hxh' : xh ≤ (HPI_LO : ℤ) - 1 := by omega
        have hxh_real : (xh : ℝ) ≤ ((HPI_LO : ℤ) - 1 : ℝ) := by exact_mod_cast hxh'
        rw [hb]
        calc
          (xh : ℝ) / (2 : ℝ) ^ 28 ≤ ((HPI_LO : ℤ) - 1 : ℝ) / (2 : ℝ) ^ 28 := by gcongr
          _ < ((HPI_LO : ℤ) : ℝ) / (2 : ℝ) ^ 28 := by
            gcongr
            norm_num
          _ < π/2 := hpi_lo_div_two_pow_lt_pi_div_two
      have h_s_le_pi2 : s ≤ π/2 := by linarith
      have h_sin_s_le_sin_b : Real.sin s ≤ Real.sin b :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hs_le_b
      have h_sin_b_le_max : Real.sin b ≤ max (Real.sin a) (Real.sin b) := le_max_right _ _
      linarith

  have h_lower : ((isinX E xl xh sl sh).1 : ℝ) ≤ (2 : ℝ) ^ 28 * Real.sin s := by
    have h1 : ((isinX E xl xh sl sh).1 : ℝ) = ((min sl sh : ℤ) : ℝ) - (E : ℝ) := by
      simp [isinX]
    rw [h1]
    have h_eq : ((min sl sh : ℤ) : ℝ) - (E : ℝ) = min ((sl : ℝ) - (E : ℝ)) ((sh : ℝ) - (E : ℝ)) := by
      rcases le_total (sl : ℝ) (sh : ℝ) with (h | h)
      · simp [h]
      · simp [h]
    rw [h_eq]
    have h_min_le : min ((sl : ℝ) - (E : ℝ)) ((sh : ℝ) - (E : ℝ)) ≤
        min ((2 : ℝ) ^ 28 * Real.sin a) ((2 : ℝ) ^ 28 * Real.sin b) := by
      exact min_le_min hsl_le hsh_le
    have h_min_eq : min ((2 : ℝ) ^ 28 * Real.sin a) ((2 : ℝ) ^ 28 * Real.sin b) =
        (2 : ℝ) ^ 28 * min (Real.sin a) (Real.sin b) := by
      rw [mul_min_of_nonneg (Real.sin a) (Real.sin b) h2pow_nonneg]
    rw [h_min_eq] at h_min_le
    have h_sin_min_le_sin_s : (2 : ℝ) ^ 28 * min (Real.sin a) (Real.sin b) ≤ (2 : ℝ) ^ 28 * Real.sin s := by
      gcongr
    linarith

  have h_upper : (2 : ℝ) ^ 28 * Real.sin s ≤ ((isinX E xl xh sl sh).2 : ℝ) := by
    by_cases h_contains : (xl < (HPI_HI : ℤ) + 1) ∧ ((HPI_LO : ℤ) - 1 < xh)
    ·
      rcases h_contains with ⟨hxl, hxh⟩
      have h2 : ((isinX E xl xh sl sh).2 : ℝ) = (2 : ℝ) ^ 28 := by
        dsimp [isinX]
        have h_cond : (xl < (HPI_HI : ℤ) + 1) ∧ ((HPI_LO : ℤ) - 1 < xh) := And.intro hxl hxh
        rw [if_pos h_cond]
        norm_num
      rw [h2]
      have h_sin_le_one : Real.sin s ≤ 1 := Real.sin_le_one _
      nlinarith
    ·
      have h2 : ((isinX E xl xh sl sh).2 : ℝ) = min (max (sl : ℝ) (sh : ℝ) + (E : ℝ)) ((2 : ℝ) ^ 28) := by
        dsimp [isinX]
        rw [if_neg h_contains]
        simp; norm_num
      rw [h2]
      have h_sin_le_one : Real.sin s ≤ 1 := Real.sin_le_one _
      have h_upper1 : (2 : ℝ) ^ 28 * Real.sin s ≤ (2 : ℝ) ^ 28 := by
        nlinarith
      have h_upper2 : (2 : ℝ) ^ 28 * Real.sin s ≤ max (sl : ℝ) (sh : ℝ) + (E : ℝ) := by
        have h_sin_s_le_max : Real.sin s ≤ max (Real.sin a) (Real.sin b) :=
          h_sin_le_max_of_not_contains_pi2 h_contains
        have h_max_sin_le : (2 : ℝ) ^ 28 * max (Real.sin a) (Real.sin b) ≤
            max (sl : ℝ) (sh : ℝ) + (E : ℝ) := by
          rcases le_total (Real.sin a) (Real.sin b) with (h | h)
          · have hmax : max (Real.sin a) (Real.sin b) = Real.sin b := max_eq_right h
            rw [hmax]
            have hsh_le_max : (sh : ℝ) ≤ max (sl : ℝ) (sh : ℝ) := le_max_right _ _
            linarith
          · have hmax : max (Real.sin a) (Real.sin b) = Real.sin a := max_eq_left h
            rw [hmax]
            have hsl_le_max : (sl : ℝ) ≤ max (sl : ℝ) (sh : ℝ) := le_max_left _ _
            linarith
        nlinarith
      exact le_min h_upper2 h_upper1
  exact And.intro h_lower h_upper

theorem icosX_sound (E xl xh cl ch : ℤ) (h0 : 0 ≤ xl) (h1 : xh ≤ (PI_LO : ℤ) + 1)
    (hcl : |(cl : ℝ) - 2 ^ 28 * Real.cos ((xl : ℝ) / 2 ^ 28)| ≤ (E : ℝ))
    (hch : |(ch : ℝ) - 2 ^ 28 * Real.cos ((xh : ℝ) / 2 ^ 28)| ≤ (E : ℝ))
    (t : ℝ) (ht : (xl : ℝ) ≤ t ∧ t ≤ xh) :
    ((icosX E xl xh cl ch).1 : ℝ) ≤ 2 ^ 28 * Real.cos (t / 2 ^ 28) ∧
      2 ^ 28 * Real.cos (t / 2 ^ 28) ≤ ((icosX E xl xh cl ch).2 : ℝ) := by
  rcases ht with ⟨htl, htr⟩
  have hxl_nonneg : 0 ≤ (xl : ℝ) := by exact_mod_cast h0
  have hxh_le_pi_plus_one : (xh : ℝ) ≤ (PI_LO : ℝ) + 1 := by exact_mod_cast h1
  have ht_nonneg : 0 ≤ t := by linarith
  have h2pow_pos : 0 < (2 ^ 28 : ℝ) := by norm_num
  have h2pow_nonneg : 0 ≤ (2 ^ 28 : ℝ) := by norm_num
  set c := fun (x : ℝ) => (2 ^ 28 : ℝ) * Real.cos (x / (2 ^ 28 : ℝ)) with hc
  have hcl_abs := abs_le.mp hcl
  have hch_abs := abs_le.mp hch
  have hcl_upper : c (xl : ℝ) ≤ (cl : ℝ) + (E : ℝ) := by
    dsimp [c]
    linarith
  have hch_lower : (ch : ℝ) - (E : ℝ) ≤ c (xh : ℝ) := by
    dsimp [c]
    linarith
  have hcos_decr {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π) (hab : a ≤ b) : Real.cos b ≤ Real.cos a :=
    Real.cos_le_cos_of_nonneg_of_le_pi ha hb hab

  have h_pi_lo_div_lt_pi : (PI_LO : ℝ) / (2 ^ 28 : ℝ) < π := by
    have h_pi_gt : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
    have h_bound : (PI_LO : ℝ) / (2 ^ 28 : ℝ) < (3.14159265358979323846 : ℝ) := by
      norm_num [PI_LO, show (2 ^ 28 : ℝ) = 268435456 by norm_num]
    linarith
  have h_pi_lt_pi_plus_one_div : π < ((PI_LO : ℝ) + 1) / (2 ^ 28 : ℝ) := by
    have h_pi_lt : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
    have h_bound : (3.14159265358979323847 : ℝ) < ((PI_LO : ℝ) + 1) / (2 ^ 28 : ℝ) := by
      norm_num [PI_LO, show (2 ^ 28 : ℝ) = 268435456 by norm_num]
    linarith
  have hxh_div_le_pi_plus_one_div : (xh : ℝ) / (2 ^ 28 : ℝ) ≤ ((PI_LO : ℝ) + 1) / (2 ^ 28 : ℝ) := by
    gcongr
  have hxl_div_nonneg : 0 ≤ (xl : ℝ) / (2 ^ 28 : ℝ) :=
    div_nonneg hxl_nonneg (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
  have ht_div_nonneg : 0 ≤ t / (2 ^ 28 : ℝ) :=
    div_nonneg ht_nonneg (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
  have ht_div_le_xh_div : t / (2 ^ 28 : ℝ) ≤ (xh : ℝ) / (2 ^ 28 : ℝ) := by
    gcongr
  have h_2pi_mul_gt_2pi_plus_one : 2 * (PI_LO : ℝ) + 1 < 2 * π * (2 ^ 28 : ℝ) := by
    have h_pi_gt : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
    have h_bound : 2 * (PI_LO : ℝ) + 1 < 2 * (3.14159265358979323846 : ℝ) * (2 ^ 28 : ℝ) := by
      norm_num [PI_LO, show (2 ^ 28 : ℝ) = 268435456 by norm_num]
    nlinarith

  have h_lo : ((icosX E xl xh cl ch).1 : ℝ) ≤ c t := by
    dsimp [icosX]
    split
    ·
      dsimp [c]
      have hcos_ge : -1 ≤ Real.cos (t / (2 ^ 28 : ℝ)) := Real.neg_one_le_cos _
      nlinarith
    ·
      have hxh_le_pi_lo_sub_one : (xh : ℝ) ≤ (PI_LO : ℝ) - 1 := by
        have h_not_lt : ¬ ((PI_LO : ℤ) - 1 < xh) := by assumption
        have h_le_int : xh ≤ (PI_LO : ℤ) - 1 := by omega
        exact_mod_cast h_le_int
      have hxh_div_lt_pi : (xh : ℝ) / (2 ^ 28 : ℝ) < π := by
        calc
          (xh : ℝ) / (2 ^ 28 : ℝ) ≤ ((PI_LO : ℝ) - 1) / (2 ^ 28 : ℝ) := by gcongr
          _ < (PI_LO : ℝ) / (2 ^ 28 : ℝ) := by
            have hpos : 0 < (2 ^ 28 : ℝ) := by norm_num
            linarith
          _ < π := h_pi_lo_div_lt_pi
      have ht_div_le_pi : t / (2 ^ 28 : ℝ) ≤ π := by linarith
      have hcos_le : Real.cos ((xh : ℝ) / (2 ^ 28 : ℝ)) ≤ Real.cos (t / (2 ^ 28 : ℝ)) :=
        hcos_decr ht_div_nonneg hxh_div_lt_pi.le ht_div_le_xh_div
      have h_cxh_le_ct : c (xh : ℝ) ≤ c t := by
        dsimp [c]
        gcongr
      simpa [c, Int.cast_sub] using le_trans hch_lower h_cxh_le_ct

  have h_hi : c t ≤ ((icosX E xl xh cl ch).2 : ℝ) := by
    dsimp [icosX]
    split
    ·
      dsimp [c]
      have hcos_le_one : Real.cos (t / (2 ^ 28 : ℝ)) ≤ 1 := Real.cos_le_one _
      nlinarith
    ·
      have h_one_le_xl : (1 : ℝ) ≤ (xl : ℝ) := by
        have h_not_lt : ¬ (xl < (1 : ℤ)) := by assumption
        have h_le_int : (1 : ℤ) ≤ xl := by omega
        exact_mod_cast h_le_int
      have hxl_div_pos : 0 < (xl : ℝ) / (2 ^ 28 : ℝ) :=
        div_pos (by linarith) (by norm_num : 0 < (2 ^ 28 : ℝ))
      have ht_div_ge_xl_div : (xl : ℝ) / (2 ^ 28 : ℝ) ≤ t / (2 ^ 28 : ℝ) := by
        gcongr
      by_cases ht_div_le_pi : t / (2 ^ 28 : ℝ) ≤ π
      ·
        have hcos_le : Real.cos (t / (2 ^ 28 : ℝ)) ≤ Real.cos ((xl : ℝ) / (2 ^ 28 : ℝ)) :=
          hcos_decr hxl_div_pos.le ht_div_le_pi ht_div_ge_xl_div
        have h_ct_le_cxl : c t ≤ c (xl : ℝ) := by
          dsimp [c]
          gcongr
        simpa [c, Int.cast_add] using le_trans h_ct_le_cxl hcl_upper
      ·
        have ht_div_gt_pi : π < t / (2 ^ 28 : ℝ) := by linarith

        have ht_gt_pi_lo : (PI_LO : ℝ) < t := by
          have h : π * (2 ^ 28 : ℝ) < t := by
            have hpos : 0 < (2 ^ 28 : ℝ) := by norm_num
            linarith
          have h_pi_lo_lt_pi_mul : (PI_LO : ℝ) < π * (2 ^ 28 : ℝ) := by
            have hpos : 0 < (2 ^ 28 : ℝ) := by norm_num
            linarith [h_pi_lo_div_lt_pi]
          linarith

        by_cases h_xl_eq_pi_lo_plus_one : (xl : ℤ) = (PI_LO : ℤ) + 1
        ·
          have h_t_eq : (t : ℝ) = (PI_LO : ℝ) + 1 := by
            have h_xl_eq : (xl : ℝ) = (PI_LO : ℝ) + 1 := by exact_mod_cast h_xl_eq_pi_lo_plus_one
            have h_t_ge : (PI_LO : ℝ) + 1 ≤ t := by linarith
            have h_t_le : t ≤ (PI_LO : ℝ) + 1 := by
              linarith
            linarith
          have h_xl_eq_real : (xl : ℝ) = (PI_LO : ℝ) + 1 := by exact_mod_cast h_xl_eq_pi_lo_plus_one
          dsimp [c]
          rw [h_t_eq, ← h_xl_eq_real]
          simpa [c, Int.cast_add] using hcl_upper
        ·
          have h_xl_le_pi_lo : (xl : ℝ) ≤ (PI_LO : ℝ) := by
            have h_xl_le_xh_int : (xl : ℤ) ≤ xh := by
              have h : (xl : ℝ) ≤ (xh : ℝ) := htl.trans htr
              exact_mod_cast h
            have h_xl_le_pi_lo_plus_one : xl ≤ (PI_LO : ℤ) + 1 := by omega
            have h_xl_le_pi_lo_int : xl ≤ (PI_LO : ℤ) := by
              have h_not_eq : xl ≠ (PI_LO : ℤ) + 1 := h_xl_eq_pi_lo_plus_one
              omega
            exact_mod_cast h_xl_le_pi_lo_int

          have h_cos_eq : Real.cos (t / (2 ^ 28 : ℝ)) = Real.cos (2 * π - t / (2 ^ 28 : ℝ)) := by
            rw [Real.cos_two_pi_sub]
          have h_two_pi_sub_nonneg : 0 ≤ 2 * π - t / (2 ^ 28 : ℝ) := by
            have h_2pi_gt : ((PI_LO : ℝ) + 1) / (2 ^ 28 : ℝ) < 2 * π := by
              have h_pi_gt : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
              have h_bound : ((PI_LO : ℝ) + 1) / (2 ^ 28 : ℝ) < 2 * (3.14159265358979323846 : ℝ) := by
                norm_num [PI_LO, show (2 ^ 28 : ℝ) = 268435456 by norm_num]
              linarith
            linarith
          have h_two_pi_sub_le_pi : 2 * π - t / (2 ^ 28 : ℝ) ≤ π := by
            linarith

          have h_xl_plus_t_le_two_pi_mul : (xl : ℝ) + t ≤ 2 * π * (2 ^ 28 : ℝ) := by
            have h_sum_le : (xl : ℝ) + t ≤ 2 * (PI_LO : ℝ) + 1 := by
              linarith
            linarith
          have h_xl_div_le_two_pi_sub : (xl : ℝ) / (2 ^ 28 : ℝ) ≤ 2 * π - t / (2 ^ 28 : ℝ) := by
            linarith
          have hcos_le : Real.cos (2 * π - t / (2 ^ 28 : ℝ)) ≤ Real.cos ((xl : ℝ) / (2 ^ 28 : ℝ)) :=
            hcos_decr hxl_div_pos.le h_two_pi_sub_le_pi h_xl_div_le_two_pi_sub
          dsimp [c]
          rw [h_cos_eq]
          have h_mul_le : (2 ^ 28 : ℝ) * Real.cos (2 * π - t / (2 ^ 28 : ℝ)) ≤ (2 ^ 28 : ℝ) * Real.cos ((xl : ℝ) / (2 ^ 28 : ℝ)) := by
            gcongr
          have h_cxl_le_cl_plus_e : (2 ^ 28 : ℝ) * Real.cos ((xl : ℝ) / (2 ^ 28 : ℝ)) ≤ (cl : ℝ) + (E : ℝ) := by
            dsimp [c] at hcl_upper
            exact hcl_upper
          simpa [Int.cast_add] using le_trans h_mul_le h_cxl_le_cl_plus_e
  exact And.intro h_lo h_hi

theorem cos_two_arcsin (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Real.cos (2 * Real.arcsin q) = 1 - 2 * q ^ 2 := by
  have hneg1 : -1 ≤ q := by linarith
  calc
    Real.cos (2 * Real.arcsin q) = Real.cos (Real.arcsin q) ^ 2 - Real.sin (Real.arcsin q) ^ 2 := by
      rw [Real.cos_two_mul']
    _ = (1 - Real.sin (Real.arcsin q) ^ 2) - Real.sin (Real.arcsin q) ^ 2 := by
      have h := Real.cos_sq_add_sin_sq (Real.arcsin q)
      linarith
    _ = 1 - 2 * Real.sin (Real.arcsin q) ^ 2 := by ring
    _ = 1 - 2 * q ^ 2 := by
      rw [Real.sin_arcsin hneg1 h1]

theorem sin_two_arcsin (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    Real.sin (2 * Real.arcsin q) = 2 * q * Real.sqrt (1 - q ^ 2) := by
  have hneg1 : -1 ≤ q := by linarith
  have hsin := Real.sin_arcsin hneg1 h1
  have hcos := Real.cos_arcsin q
  calc
    Real.sin (2 * Real.arcsin q) = 2 * Real.sin (Real.arcsin q) * Real.cos (Real.arcsin q) := by
      rw [Real.sin_two_mul]
    _ = 2 * q * Real.cos (Real.arcsin q) := by rw [hsin]
    _ = 2 * q * Real.sqrt (1 - q ^ 2) := by rw [hcos]

theorem s_end_sound (q : ℕ) (hq : q ≤ 2 ^ 28) :
    ((2 * ((q * Nat.sqrt (2 ^ 56 - q * q)) / 2 ^ 28) : ℕ) : ℝ) ≤
        2 ^ 28 * (2 * ((q : ℝ) / 2 ^ 28) * Real.sqrt (1 - ((q : ℝ) / 2 ^ 28) ^ 2)) ∧
      2 ^ 28 * (2 * ((q : ℝ) / 2 ^ 28) * Real.sqrt (1 - ((q : ℝ) / 2 ^ 28) ^ 2)) ≤
        min (2 * (((q * (Nat.sqrt (2 ^ 56 - q * q) + 1) + (2 ^ 28 - 1)) / 2 ^ 28 : ℕ) : ℝ)) (2 ^ 28) := by
  have hqq : q * q ≤ 2 ^ 56 := by
    have := Nat.mul_le_mul hq hq
    simpa [← pow_two, ← pow_mul] using this
  have hSr : ((2 ^ 56 - q * q : ℕ) : ℝ) = 2 ^ 56 - (q : ℝ) ^ 2 := by
    rw [Nat.cast_sub hqq]; push_cast; ring
  generalize hS : 2 ^ 56 - q * q = S at hSr ⊢
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hr1 : (Nat.sqrt S : ℝ) ≤ Real.sqrt S :=
    (Real.le_sqrt (Nat.cast_nonneg _) hS0).mpr (by exact_mod_cast Nat.sqrt_le' S)
  have hr2 : Real.sqrt S < (Nat.sqrt S : ℝ) + 1 :=
    (Real.sqrt_lt' (by positivity)).mpr (by exact_mod_cast Nat.lt_succ_sqrt' S)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hkey : 2 ^ 28 * (2 * ((q : ℝ) / 2 ^ 28) * Real.sqrt (1 - ((q : ℝ) / 2 ^ 28) ^ 2)) =
      2 * q * Real.sqrt S / 2 ^ 28 := by
    have h1 : 1 - ((q : ℝ) / 2 ^ 28) ^ 2 = (S : ℝ) / (2 ^ 28) ^ 2 := by
      rw [hSr]; field_simp
    rw [h1, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
    field_simp
  rw [hkey]
  generalize Nat.sqrt S = r at hr1 hr2 ⊢
  constructor
  ·
    have h1 : ((q * r / 2 ^ 28 : ℕ) : ℝ) * 2 ^ 28 ≤ (q : ℝ) * r := by
      exact_mod_cast Nat.div_mul_le_self (q * r) (2 ^ 28)
    have h2 : (q : ℝ) * r ≤ q * Real.sqrt S := mul_le_mul_of_nonneg_left hr1 hq0
    rw [Nat.cast_mul, Nat.cast_ofNat, le_div_iff₀ (by norm_num)]
    linarith
  · apply le_min
    ·
      have hc : q * (r + 1) ≤ 2 ^ 28 * ((q * (r + 1) + (2 ^ 28 - 1)) / 2 ^ 28) := by
        have h := Nat.div_add_mod (q * (r + 1) + (2 ^ 28 - 1)) (2 ^ 28)
        have hm := Nat.mod_lt (q * (r + 1) + (2 ^ 28 - 1)) (by norm_num : 0 < 2 ^ 28)
        omega
      have hc' : (q : ℝ) * (r + 1) ≤ 2 ^ 28 * (((q * (r + 1) + (2 ^ 28 - 1)) / 2 ^ 28 : ℕ) : ℝ) := by
        exact_mod_cast hc
      have h2 : (q : ℝ) * Real.sqrt S ≤ q * (r + 1) := mul_le_mul_of_nonneg_left hr2.le hq0
      rw [div_le_iff₀ (by norm_num)]
      linarith
    ·
      rw [div_le_iff₀ (by norm_num)]
      have hsq := Real.sq_sqrt hS0
      nlinarith [sq_nonneg ((q : ℝ) - Real.sqrt S)]

theorem two_q_sqrt_min (ql qh q : ℝ) (h0 : 0 ≤ ql) (hl : ql ≤ q) (hh : q ≤ qh) (h1 : qh ≤ 1) :
    min (2 * ql * Real.sqrt (1 - ql ^ 2)) (2 * qh * Real.sqrt (1 - qh ^ 2)) ≤ 2 * q * Real.sqrt (1 - q ^ 2) := by
  set g := λ (x : ℝ) => 2 * x * Real.sqrt (1 - x ^ 2) with hg
  have hq0 : 0 ≤ q := le_trans h0 hl
  have hq1 : q ≤ 1 := le_trans hh h1
  have hql1 : ql ≤ 1 := le_trans hl hq1
  have hqh0 : 0 ≤ qh := le_trans hq0 hh

  have hg_nonneg : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ g x := by
    intro x hx0 hx1
    dsimp [g]
    have hsqrt : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg _
    have h_sq_nonneg : 0 ≤ 1 - x ^ 2 := by nlinarith
    nlinarith
  have hgql_nonneg : 0 ≤ g ql := hg_nonneg ql h0 hql1
  have hgqh_nonneg : 0 ≤ g qh := hg_nonneg qh hqh0 h1
  have hgq_nonneg : 0 ≤ g q := hg_nonneg q hq0 hq1

  have hg_sq_eq : ∀ x, 0 ≤ x → x ≤ 1 → g x ^ 2 = 1 - (1 - 2 * x ^ 2) ^ 2 := by
    intro x hx0 hx1
    dsimp [g]
    have h_sq_under : 0 ≤ 1 - x ^ 2 := by nlinarith
    calc
      (2 * x * Real.sqrt (1 - x ^ 2)) ^ 2 = (2 * x) ^ 2 * (Real.sqrt (1 - x ^ 2)) ^ 2 := by ring
      _ = (2 * x) ^ 2 * (1 - x ^ 2) := by rw [Real.sq_sqrt h_sq_under]
      _ = 4 * x ^ 2 * (1 - x ^ 2) := by ring
      _ = 1 - (1 - 2 * x ^ 2) ^ 2 := by ring

  set a := 1 - 2 * ql ^ 2 with ha
  set b := 1 - 2 * q ^ 2 with hb
  set c := 1 - 2 * qh ^ 2 with hc

  have hc_le_b : c ≤ b := by
    dsimp [c, b]
    nlinarith
  have hb_le_a : b ≤ a := by
    dsimp [b, a]
    nlinarith

  have hb_sq_le_max : b ^ 2 ≤ max (a ^ 2) (c ^ 2) := by
    by_cases hb_nonneg : 0 ≤ b
    ·
      have hb_sq_le_a_sq : b ^ 2 ≤ a ^ 2 := by
        nlinarith
      have ha_sq_le_max : a ^ 2 ≤ max (a ^ 2) (c ^ 2) := le_max_left _ _
      nlinarith
    ·
      have hb_neg : b < 0 := by linarith
      have hc_neg : c < 0 := by linarith

      have hb_sq_le_c_sq : b ^ 2 ≤ c ^ 2 := by
        nlinarith
      have hc_sq_le_max : c ^ 2 ≤ max (a ^ 2) (c ^ 2) := le_max_right _ _
      nlinarith

  have h_sq_ineq : g q ^ 2 ≥ min (g ql ^ 2) (g qh ^ 2) := by
    rw [hg_sq_eq q hq0 hq1, hg_sq_eq ql h0 hql1, hg_sq_eq qh hqh0 h1]
    rw [min_sub_sub_left]
    nlinarith

  by_cases h : g ql ≤ g qh
  ·
    have h_min : min (g ql) (g qh) = g ql := min_eq_left h
    rw [h_min]

    have h_min_sq : min (g ql ^ 2) (g qh ^ 2) = g ql ^ 2 := by
      apply min_eq_left
      nlinarith
    rw [h_min_sq] at h_sq_ineq
    exact (sq_le_sq₀ hgql_nonneg hgq_nonneg).mp h_sq_ineq
  ·
    have h_min : min (g ql) (g qh) = g qh := min_eq_right (by linarith)
    rw [h_min]
    have h_min_sq : min (g ql ^ 2) (g qh ^ 2) = g qh ^ 2 := by
      apply min_eq_right
      nlinarith
    rw [h_min_sq] at h_sq_ineq
    exact (sq_le_sq₀ hgqh_nonneg hgq_nonneg).mp h_sq_ineq

end D3Ck2Spec
