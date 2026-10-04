import Tammes15.D3Prog.L2.Defs
import Tammes15.Contractors.Encl

namespace D3Prog.L2

open Real Tammes15 D3Ck2Spec

set_option linter.unusedVariables false

theorem K1_ix (F s : ℕ) (V : ℤ) (h : V = ((F / 2 ^ s % 2 ^ 32 * 16 : ℕ) : ℤ)) : (V : ℝ) = 2 ^ 28 * fld F s := by
  subst h
  rw [Int.cast_natCast, Nat.cast_mul]
  unfold fld
  ring

theorem K2_sin (X V : ℤ) (h : V = sinI X) (h0 : 0 ≤ X) (h1 : X ≤ 843314857) :
    |(V : ℝ) - 2 ^ 28 * sin ((X : ℝ) / 2 ^ 28)| ≤ 3 := by
  subst h
  have hXtoNat_eq : ((X.toNat : ℕ) : ℝ) = (X : ℝ) := by
    exact mod_cast (Int.toNat_of_nonneg h0)
  have hXle : X.toNat ≤ D3Ck2Spec.PI_LO + 1 := by
    have hXle' : X ≤ (D3Ck2Spec.PI_LO : ℤ) + 1 := by
      simpa [D3Ck2Spec.PI_LO] using h1
    have hpos : 0 ≤ (D3Ck2Spec.PI_LO : ℤ) + 1 := by omega
    have hXtoNat_le : X.toNat ≤ ((D3Ck2Spec.PI_LO : ℤ) + 1).toNat :=
      Int.toNat_le_toNat hXle'
    simpa [Int.toNat_of_nonneg hpos] using hXtoNat_le
  have hscI : D3Prog.L2.scI X = X.toNat := by
    unfold D3Prog.L2.scI
    have hnotneg : ¬ (X < 0) := by omega
    simp [hnotneg]
  unfold D3Prog.L2.sinI
  rw [hscI]
  rw [← hXtoNat_eq]
  exact (sc28pS_err X.toNat hXle).1

theorem K2_cos (X V : ℤ) (h : V = cosI X) (h0 : 0 ≤ X) (h1 : X ≤ 843314857) :
    |(V : ℝ) - 2 ^ 28 * cos ((X : ℝ) / 2 ^ 28)| ≤ 3 := by
  rw [h]
  unfold cosI scI
  have h_not_lt : ¬ (X < 0) := by linarith
  simp [h_not_lt]
  have hx : X.toNat ≤ PI_LO + 1 := by
    have h1' : X ≤ (PI_LO : ℤ) + 1 := by

      have : (PI_LO : ℤ) = 843314856 := rfl
      omega
    have := Int.toNat_le_toNat h1'

    have hpos : 0 ≤ (PI_LO : ℤ) + 1 := by
      have : 0 ≤ (PI_LO : ℤ) := by decide
      linarith
    have htoNat : ((PI_LO : ℤ) + 1).toNat = PI_LO + 1 := by

      omega
    omega
  rcases sc28pS_err (X.toNat) hx with ⟨_, hcos⟩
  have hcast : (X.toNat : ℝ) = (X : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h0
  simpa [hcast] using hcos

theorem K3_sin_lo (X s V : ℤ) (hs : s = sinI X) (hv : V = s + -4) :
    0 ≤ X → X ≤ 843314857 → (V : ℝ) ≤ 2 ^ 28 * sin ((X : ℝ) / 2 ^ 28) := by
  intro hX0 hX1
  have hX_not_neg : ¬ X < 0 := by omega
  have h_scI : scI X = X.toNat := by
    unfold scI
    simp [hX_not_neg]
  have h_sinI : sinI X = (sc28pS (X.toNat)).1 := by
    unfold sinI
    rw [h_scI]
  rw [h_sinI] at hs
  have hX_nat_bound : X.toNat ≤ D3Ck2Spec.PI_LO + 1 := by
    have hX1' : (X : ℤ) ≤ ((D3Ck2Spec.PI_LO + 1 : ℕ) : ℤ) := by
      simpa [D3Ck2Spec.PI_LO] using hX1
    exact Int.toNat_le_toNat hX1'
  have h_err := D3Ck2Spec.sc28pS_err (X.toNat) hX_nat_bound
  rcases h_err with ⟨h_err_sin, _⟩
  have h_cast : ((X.toNat : ℕ) : ℝ) = (X : ℝ) := by
    have h_int : (X.toNat : ℤ) = X := Int.toNat_of_nonneg hX0
    exact mod_cast h_int
  rw [h_cast] at h_err_sin
  rw [← hs] at h_err_sin
  have h_abs := abs_le.mp h_err_sin
  rcases h_abs with ⟨h_le, h_ge⟩
  rw [hv]
  push_cast
  linarith

theorem K3_sin_hi (X s t one V : ℤ) (hs : s = sinI X) (ht : t = s + 4) (hone : one = 268435456)
    (hv : V = min t one) : 0 ≤ X → X ≤ 843314857 → 2 ^ 28 * sin ((X : ℝ) / 2 ^ 28) ≤ V := by
  intro hX0 hX843314857
  have hX_not_lt : ¬ X < 0 := by omega
  have hsinI_eq : sinI X = (D3Ck2Spec.sc28pS (X.toNat)).1 := by
    dsimp [sinI, scI]
    simp [hX_not_lt]
  have hXnat_le : X.toNat ≤ D3Ck2Spec.PI_LO + 1 := by
    dsimp [D3Ck2Spec.PI_LO]
    omega
  have herr := D3Ck2Spec.sc28pS_err (X.toNat) hXnat_le
  rcases herr with ⟨herr_sin, herr_cos⟩
  have hXcast : ((X.toNat : ℕ) : ℝ) = (X : ℝ) := by
    have h := Int.toNat_of_nonneg hX0
    calc
      ((X.toNat : ℕ) : ℝ) = ((X.toNat : ℤ) : ℝ) := by norm_cast
      _ = (X : ℝ) := by rw [h]
  rw [← hsinI_eq, ← hs] at herr_sin
  rw [hXcast] at herr_sin
  have habs := abs_le.mp herr_sin
  rcases habs with ⟨hleft, hright⟩
  have hA_le_s_plus_3 : 2 ^ 28 * Real.sin ((X : ℝ) / 2 ^ 28) ≤ (s : ℝ) + 3 := by
    linarith
  have hA_le_s_plus_4 : 2 ^ 28 * Real.sin ((X : ℝ) / 2 ^ 28) ≤ (s : ℝ) + 4 := by
    linarith
  have hA_le_2pow28 : 2 ^ 28 * Real.sin ((X : ℝ) / 2 ^ 28) ≤ (2 ^ 28 : ℝ) := by
    have hsin_le_one : Real.sin ((X : ℝ) / 2 ^ 28) ≤ 1 := Real.sin_le_one _
    have hpos : (0 : ℝ) ≤ 2 ^ 28 := by norm_num
    have h := mul_le_mul_of_nonneg_left hsin_le_one hpos
    simpa [mul_one] using h
  rw [hv, ht, hone]
  rw [Int.cast_min]
  rw [le_min_iff]
  constructor
  · push_cast
    exact hA_le_s_plus_4
  · have h268435456 : (268435456 : ℝ) = (2 : ℝ) ^ 28 := by norm_num
    simpa [h268435456] using hA_le_2pow28

theorem K3_cos_lo (X s t m V : ℤ) (hs : s = cosI X) (ht : t = s + -4) (hm : m = -268435456)
    (hv : V = max t m) : 0 ≤ X → X ≤ 843314857 → (V : ℝ) ≤ 2 ^ 28 * cos ((X : ℝ) / 2 ^ 28) := by
  intro hX0 hXbound
  have hX0' : ¬ X < 0 := by omega
  have hscI : scI X = X.toNat := by
    dsimp [scI]
    rw [ite_eq_right hX0']
  have hcosI_eq : (cosI X : ℝ) = ((sc28pS (X.toNat)).2 : ℝ) := by
    dsimp [cosI]
    rw [hscI]
  have hXtoNat_bound : X.toNat ≤ PI_LO + 1 := by
    have hX_int_le : (X : ℤ) ≤ (PI_LO + 1 : ℕ) := by
      simpa [PI_LO] using hXbound
    have := Int.toNat_le_toNat hX_int_le
    simpa using this
  have h_err := sc28pS_err (X.toNat) hXtoNat_bound
  rcases h_err with ⟨_, h_cos_err⟩

  have hX_cast : (X.toNat : ℝ) = (X : ℝ) := by
    exact mod_cast Int.toNat_of_nonneg hX0
  have h_cos_bound : |(cosI X : ℝ) - 2 ^ 28 * Real.cos ((X : ℝ) / 2 ^ 28)| ≤ 3 := by
    rw [hcosI_eq]
    simpa [hX_cast] using h_cos_err
  have h_abs := abs_le.mp h_cos_bound
  rcases h_abs with ⟨h_low, h_high⟩

  have h_neg_one_le_cos : -1 ≤ Real.cos ((X : ℝ) / 2 ^ 28) := Real.neg_one_le_cos _
  have h_2_28_cos_ge : -(2 ^ 28 : ℝ) ≤ 2 ^ 28 * Real.cos ((X : ℝ) / 2 ^ 28) := by
    nlinarith
  have h_cosI_minus_4_le : (cosI X : ℝ) - 4 ≤ 2 ^ 28 * Real.cos ((X : ℝ) / 2 ^ 28) := by
    nlinarith
  rw [hv, ht, hs]

  have hm_val : (m : ℝ) = -(2 ^ 28 : ℝ) := by
    rw [hm]
    norm_num
  have h_max_cast : ((max (cosI X + -4) m : ℤ) : ℝ) = max ((cosI X : ℝ) + (-4 : ℝ)) (m : ℝ) := by
    simp
  rw [h_max_cast, hm_val]

  apply max_le
  ·
    exact h_cosI_minus_4_le
  ·
    exact h_2_28_cos_ge

theorem K3_cos_hi (X s t one V : ℤ) (hs : s = cosI X) (ht : t = s + 4) (hone : one = 268435456)
    (hv : V = min t one) : 0 ≤ X → X ≤ 843314857 → 2 ^ 28 * cos ((X : ℝ) / 2 ^ 28) ≤ V := by
  intro hX0 hXbound
  have hscI : scI X = X.toNat := by
    simp [scI, not_lt.mpr hX0]
  have hcosI : (cosI X : ℝ) = (sc28pS (scI X)).2 := by
    simp [cosI]
  have hcosI' : (s : ℝ) = (sc28pS X.toNat).2 := by
    rw [hs, hcosI, hscI]
  have hPI_LO_bound : X.toNat ≤ PI_LO + 1 := by
    have hPI : (PI_LO : ℤ) = 843314856 := rfl
    omega
  have herr := sc28pS_err X.toNat hPI_LO_bound
  rcases herr with ⟨_, herr_cos⟩
  rw [← hcosI'] at herr_cos
  have hXtoNat_eq : (X.toNat : ℝ) = (X : ℝ) := by
    exact mod_cast Int.toNat_of_nonneg hX0
  have hcos_bound : |(s : ℝ) - 2 ^ 28 * cos ((X : ℝ) / 2 ^ 28)| ≤ 3 := by
    simpa [hXtoNat_eq] using herr_cos
  have hcos_le_one : cos ((X : ℝ) / 2 ^ 28) ≤ 1 := Real.cos_le_one _
  have hcos_lower : (s : ℝ) - 3 ≤ 2 ^ 28 * cos ((X : ℝ) / 2 ^ 28) := by
    linarith [abs_le.mp hcos_bound]
  have hcos_upper : 2 ^ 28 * cos ((X : ℝ) / 2 ^ 28) ≤ (s : ℝ) + 3 := by
    linarith [abs_le.mp hcos_bound]
  have hone_val : (one : ℝ) = (2 : ℝ) ^ 28 := by
    rw [hone]
    norm_num
  have hV_eq : (V : ℝ) = min (t : ℝ) (one : ℝ) := by
    rw [hv]
    simp
  rw [hV_eq]
  have ht_val : (t : ℝ) = (s : ℝ) + 4 := by
    rw [ht]
    simp
  rw [ht_val]
  have h_lower : 2 ^ 28 * cos ((X : ℝ) / 2 ^ 28) ≤ (s : ℝ) + 4 := by
    linarith
  have h_upper : 2 ^ 28 * cos ((X : ℝ) / 2 ^ 28) ≤ (2 : ℝ) ^ 28 := by
    nlinarith [Real.cos_le_one ((X : ℝ) / 2 ^ 28)]
  apply le_min
  ·
    linarith
  ·
    nlinarith [Real.cos_le_one ((X : ℝ) / 2 ^ 28)]

theorem K4_iadd (AL AH BL BH LO HI : ℤ) (hlo : LO = AL + BL) (hhi : HI = AH + BH) :
    ∀ r s : ℝ, Enc AL AH r → Enc BL BH s → Enc LO HI (r + s) := by
  intro r s ⟨hALr, hHrA⟩ ⟨hBLs, hHBs⟩
  rw [hlo, hhi]
  constructor
  · push_cast; nlinarith
  · push_cast; nlinarith

theorem K4_isub (AL AH BL BH LO HI : ℤ) (hlo : LO = AL - BH) (hhi : HI = AH - BL) :
    ∀ r s : ℝ, Enc AL AH r → Enc BL BH s → Enc LO HI (r - s) := by
  intro r s ⟨hal, har⟩ ⟨hbl, hbr⟩
  rw [Enc, hlo, hhi]
  push_cast
  constructor
  · linarith
  · linarith

theorem K5_ihalf (AL AH LO HI : ℤ) (hlo : LO = AL / 2) (hhi : HI = (AH + 1) / 2) :
    ∀ r : ℝ, Enc AL AH r → Enc LO HI (r / 2) := by
  intro r ⟨hal, har⟩
  have h_lo : (LO : ℝ) ≤ (2 : ℝ) ^ 28 * (r / 2) := by
    rw [hlo]
    have h_cast_le : ((AL / 2 : ℤ) : ℝ) ≤ (AL : ℝ) / 2 := by
      have h := Int.ediv_mul_le AL (by norm_num : (2 : ℤ) ≠ 0)
      have h' : ((AL / 2 : ℤ) : ℝ) * (2 : ℝ) ≤ (AL : ℝ) := by exact_mod_cast h
      linarith
    have h_div_eq : (2 : ℝ) ^ 28 * (r / 2) = ((2 : ℝ) ^ 28 * r) / 2 := by rw [mul_div_assoc]
    rw [h_div_eq]
    linarith
  have h_hi : (2 : ℝ) ^ 28 * (r / 2) ≤ (HI : ℝ) := by
    rw [hhi]
    have h_div_eq : (2 : ℝ) ^ 28 * (r / 2) = ((2 : ℝ) ^ 28 * r) / 2 := by rw [mul_div_assoc]
    rw [h_div_eq]
    have h_cast_le : (AH : ℝ) / 2 ≤ (((AH + 1) / 2 : ℤ) : ℝ) := by
      have h_int : AH ≤ (AH + 1) / 2 * 2 := by
        have h_eq := Int.ediv_mul_add_emod (AH + 1) 2
        omega
      have h_real : (AH : ℝ) ≤ (((AH + 1) / 2 : ℤ) : ℝ) * (2 : ℝ) := by
        simpa [mul_comm] using mod_cast h_int
      linarith
    linarith
  exact And.intro h_lo h_hi

theorem imul_round2 (P Q LO HI : ℤ) (x y : ℝ) (e1 : LO * 268435456 ≤ P) (e2 : Q ≤ HI * 268435456)
    (h1 : (P : ℝ) ≤ x * y) (h2 : x * y ≤ Q) : Enc LO HI (x / 2 ^ 28 * (y / 2 ^ 28)) := by
  have r1 : (LO : ℝ) * 268435456 ≤ P := by exact_mod_cast e1
  have r2 : (Q : ℝ) ≤ HI * 268435456 := by exact_mod_cast e2
  have ex : 2 ^ 28 * (x / 2 ^ 28 * (y / 2 ^ 28)) = x * y / 268435456 := by ring
  unfold Enc
  rw [ex]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [div_le_iff₀ (by norm_num)]; linarith

theorem imul_round (P Q LO HI : ℤ) (x y : ℝ) (hlo : LO = P / 2 ^ 28) (hhi : HI = -(-Q / 2 ^ 28))
    (h1 : (P : ℝ) ≤ x * y) (h2 : x * y ≤ Q) : Enc LO HI (x / 2 ^ 28 * (y / 2 ^ 28)) :=
  imul_round2 P Q LO HI x y (by rw [hlo]; omega) (by rw [hhi]; omega) h1 h2

theorem int_neg_cast (a : ℤ) : (a < 0 → (a : ℝ) < 0) ∧ (¬a < 0 → 0 ≤ (a : ℝ)) :=
  ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast not_lt.1 h⟩

theorem int_pos_cast (a : ℤ) : (0 < a → 0 < (a : ℝ)) ∧ (¬0 < a → (a : ℝ) ≤ 0) :=
  ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast not_lt.1 h⟩

theorem imul_corner (AL AH BL BH : ℤ) (x y : ℝ) (hx1 : (AL : ℝ) ≤ x) (hx2 : x ≤ AH) (hy1 : (BL : ℝ) ≤ y)
    (hy2 : y ≤ BH) (hnb : ¬((AL < 0 ∧ 0 < AH) ∧ (BL < 0 ∧ 0 < BH))) :
    ((if (¬0 < BH ∧ BL < 0) ∨ (¬AL < 0 ∧ (BL < 0 ∧ 0 < BH)) then AH else AL : ℤ) : ℝ) *
        ((if (¬0 < AH ∧ AL < 0) ∨ ((AL < 0 ∧ 0 < AH) ∧ ¬BL < 0) then BH else BL : ℤ) : ℝ) ≤ x * y ∧
      x * y ≤ ((if (¬0 < BH ∧ BL < 0) ∨ ((¬0 < AH ∧ AL < 0) ∧ (BL < 0 ∧ 0 < BH)) then AL else AH : ℤ) : ℝ) *
        ((if (¬0 < AH ∧ AL < 0) ∨ ((AL < 0 ∧ 0 < AH) ∧ (¬0 < BH ∧ BL < 0)) then BL else BH : ℤ) : ℝ) := by
  have a1 := sub_nonneg.2 hx1
  have a2 := sub_nonneg.2 hx2
  have b1 := sub_nonneg.2 hy1
  have b2 := sub_nonneg.2 hy2
  by_cases c1 : AL < 0 <;> by_cases c2 : 0 < AH <;> by_cases c3 : BL < 0 <;> by_cases c4 : 0 < BH <;>
    simp only [c1, c2, c3, c4, not_true_eq_false, not_false_eq_true, and_true, and_false,
      or_false, or_true, ite_true, ite_false, and_self] at hnb ⊢ <;>
    (first | have s1 := (int_neg_cast AL).1 c1 | have s1 := (int_neg_cast AL).2 c1) <;>
    (first | have s2 := (int_pos_cast AH).1 c2 | have s2 := (int_pos_cast AH).2 c2) <;>
    (first | have s3 := (int_neg_cast BL).1 c3 | have s3 := (int_neg_cast BL).2 c3) <;>
    (first | have s4 := (int_pos_cast BH).1 c4 | have s4 := (int_pos_cast BH).2 c4) <;>
    constructor <;> nlinarith [mul_nonneg a1 b1, mul_nonneg a2 b2, mul_nonneg a1 b2, mul_nonneg a2 b1]

theorem imul_corner7 (AL AH BL BH : ℤ) (x y : ℝ) (hx1 : (AL : ℝ) ≤ x) (hx2 : x ≤ AH) (hy1 : (BL : ℝ) ≤ y)
    (hy2 : y ≤ BH) (hnb : ¬((AL < 0 ∧ 0 < AH) ∧ (BL < 0 ∧ 0 < BH))) :
    ((if (¬0 < BH ∧ BL < 0) ∨ (¬AL < 0 ∧ (BL < 0 ∧ 0 < BH)) then AH else AL : ℤ) : ℝ) *
        ((if (¬0 < AH ∧ AL < 0) ∨ ((AL < 0 ∧ 0 < AH) ∧ ¬(¬0 < BH ∧ BL < 0)) then BH else BL : ℤ) : ℝ) ≤ x * y ∧
      x * y ≤ ((if (¬0 < BH ∧ BL < 0) ∨ ((¬0 < AH ∧ AL < 0) ∧ (BL < 0 ∧ 0 < BH)) then AL else AH : ℤ) : ℝ) *
        ((if (¬0 < AH ∧ AL < 0) ∨ ((AL < 0 ∧ 0 < AH) ∧ (¬0 < BH ∧ BL < 0)) then BL else BH : ℤ) : ℝ) := by
  have a1 := sub_nonneg.2 hx1
  have a2 := sub_nonneg.2 hx2
  have b1 := sub_nonneg.2 hy1
  have b2 := sub_nonneg.2 hy2
  by_cases c1 : AL < 0 <;> by_cases c2 : 0 < AH <;> by_cases c3 : BL < 0 <;> by_cases c4 : 0 < BH <;>
    simp only [c1, c2, c3, c4, not_true_eq_false, not_false_eq_true, and_true, and_false,
      or_false, or_true, ite_true, ite_false, and_self] at hnb ⊢ <;>
    (first | have s1 := (int_neg_cast AL).1 c1 | have s1 := (int_neg_cast AL).2 c1) <;>
    (first | have s2 := (int_pos_cast AH).1 c2 | have s2 := (int_pos_cast AH).2 c2) <;>
    (first | have s3 := (int_neg_cast BL).1 c3 | have s3 := (int_neg_cast BL).2 c3) <;>
    (first | have s4 := (int_pos_cast BH).1 c4 | have s4 := (int_pos_cast BH).2 c4) <;>
    constructor <;> nlinarith [mul_nonneg a1 b1, mul_nonneg a2 b2, mul_nonneg a1 b2, mul_nonneg a2 b1]

theorem imul_both (AL AH BL BH : ℤ) (x y : ℝ) (hx1 : (AL : ℝ) ≤ x) (hx2 : x ≤ AH) (hy1 : (BL : ℝ) ≤ y)
    (hy2 : y ≤ BH) (h : (AL < 0 ∧ 0 < AH) ∧ (BL < 0 ∧ 0 < BH)) :
    ((min (AL * BH) (AH * BL) : ℤ) : ℝ) ≤ x * y ∧ x * y ≤ ((max (AH * BH) (AL * BL) : ℤ) : ℝ) := by
  obtain ⟨⟨c1, c2⟩, c3, c4⟩ := h
  have s1 := (int_neg_cast AL).1 c1
  have s2 := (int_pos_cast AH).1 c2
  have s3 := (int_neg_cast BL).1 c3
  have s4 := (int_pos_cast BH).1 c4
  have a1 := sub_nonneg.2 hx1
  have a2 := sub_nonneg.2 hx2
  have b1 := sub_nonneg.2 hy1
  have b2 := sub_nonneg.2 hy2
  push_cast
  constructor
  · rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
    · exact min_le_of_left_le (by nlinarith)
    · exact min_le_of_right_le (by nlinarith)
    · exact min_le_of_left_le (by nlinarith)
    · exact min_le_of_left_le (by nlinarith)
  · rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
    · exact le_max_of_le_left (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
    · exact le_max_of_le_right (by nlinarith)

theorem K6_imul (G : Prop) (AL AH BL BH : ℤ) (z : ℤ) (al pa ah na0 na za bl pb bh nb0 nb zb both nboth : ℕ)
    (t1 m1 : ℕ) (xlo : ℤ) (t2 m2 : ℕ) (ylo : ℤ) (t3 m3 : ℕ) (xhi : ℤ) (t4 m4 : ℕ) (yhi LO HI : ℤ)
    (hz : z = 0) (hal : al = 1 ↔ AL < z) (hpa : pa = 1 ↔ ¬al = 1) (hah : ah = 1 ↔ z < AH)
    (hna0 : na0 = 1 ↔ ¬ah = 1) (hna : na = 1 ↔ na0 = 1 ∧ al = 1) (hza : za = 1 ↔ al = 1 ∧ ah = 1)
    (hbl : bl = 1 ↔ BL < z) (hpb : pb = 1 ↔ ¬bl = 1) (hbh : bh = 1 ↔ z < BH) (hnb0 : nb0 = 1 ↔ ¬bh = 1)
    (hnb : nb = 1 ↔ nb0 = 1 ∧ bl = 1) (hzb : zb = 1 ↔ bl = 1 ∧ bh = 1) (hboth : both = 1 ↔ za = 1 ∧ zb = 1)
    (hnboth : nboth = 1 ↔ ¬both = 1) (hck : G → nboth = 1)
    (ht1 : t1 = 1 ↔ pa = 1 ∧ zb = 1) (hm1 : m1 = 1 ↔ nb = 1 ∨ t1 = 1) (hxlo : xlo = if m1 = 1 then AH else AL)
    (ht2 : t2 = 1 ↔ za = 1 ∧ pb = 1) (hm2 : m2 = 1 ↔ na = 1 ∨ t2 = 1) (hylo : ylo = if m2 = 1 then BH else BL)
    (ht3 : t3 = 1 ↔ na = 1 ∧ zb = 1) (hm3 : m3 = 1 ↔ nb = 1 ∨ t3 = 1) (hxhi : xhi = if m3 = 1 then AL else AH)
    (ht4 : t4 = 1 ↔ za = 1 ∧ nb = 1) (hm4 : m4 = 1 ↔ na = 1 ∨ t4 = 1) (hyhi : yhi = if m4 = 1 then BL else BH)
    (hlo : LO = xlo * ylo / 2 ^ 28) (hhi : HI = -(-(xhi * yhi) / 2 ^ 28)) :
    G → ∀ r s : ℝ, Enc AL AH r → Enc BL BH s → Enc LO HI (r * s) := by
  intro hG r s hr hs
  subst hz
  have hck' := hck hG
  have fal : al = 1 ↔ AL < 0 := hal
  have fah : ah = 1 ↔ 0 < AH := hah
  have fbl : bl = 1 ↔ BL < 0 := hbl
  have fbh : bh = 1 ↔ 0 < BH := hbh
  have fpa : pa = 1 ↔ ¬AL < 0 := by rw [hpa, fal]
  have fna : na = 1 ↔ ¬0 < AH ∧ AL < 0 := by rw [hna, hna0, fah, fal]
  have fza : za = 1 ↔ AL < 0 ∧ 0 < AH := by rw [hza, fal, fah]
  have fpb : pb = 1 ↔ ¬BL < 0 := by rw [hpb, fbl]
  have fnb : nb = 1 ↔ ¬0 < BH ∧ BL < 0 := by rw [hnb, hnb0, fbh, fbl]
  have fzb : zb = 1 ↔ BL < 0 ∧ 0 < BH := by rw [hzb, fbl, fbh]
  have fnboth : ¬((AL < 0 ∧ 0 < AH) ∧ (BL < 0 ∧ 0 < BH)) := by
    have := hnboth.1 hck'; rw [hboth, fza, fzb] at this; exact this
  have exlo : xlo = if (¬0 < BH ∧ BL < 0) ∨ (¬AL < 0 ∧ (BL < 0 ∧ 0 < BH)) then AH else AL := by
    rw [hxlo]; exact if_congr (by rw [hm1, fnb, ht1, fpa, fzb]) rfl rfl
  have eylo : ylo = if (¬0 < AH ∧ AL < 0) ∨ ((AL < 0 ∧ 0 < AH) ∧ ¬BL < 0) then BH else BL := by
    rw [hylo]; exact if_congr (by rw [hm2, fna, ht2, fza, fpb]) rfl rfl
  have exhi : xhi = if (¬0 < BH ∧ BL < 0) ∨ ((¬0 < AH ∧ AL < 0) ∧ (BL < 0 ∧ 0 < BH)) then AL else AH := by
    rw [hxhi]; exact if_congr (by rw [hm3, fnb, ht3, fna, fzb]) rfl rfl
  have eyhi : yhi = if (¬0 < AH ∧ AL < 0) ∨ ((AL < 0 ∧ 0 < AH) ∧ (¬0 < BH ∧ BL < 0)) then BL else BH := by
    rw [hyhi]; exact if_congr (by rw [hm4, fna, ht4, fza, fnb]) rfl rfl
  obtain ⟨hx1, hx2⟩ := hr
  obtain ⟨hy1, hy2⟩ := hs
  have key := imul_corner AL AH BL BH (2 ^ 28 * r) (2 ^ 28 * s) hx1 hx2 hy1 hy2 fnboth
  rw [← exlo, ← eylo, ← exhi, ← eyhi] at key
  have hrs : r * s = (2 ^ 28 * r) / 2 ^ 28 * ((2 ^ 28 * s) / 2 ^ 28) := by field_simp
  rw [hrs]
  exact imul_round (xlo * ylo) (xhi * yhi) LO HI _ _ hlo hhi (by push_cast; exact key.1) (by push_cast; exact key.2)

theorem K7_imul_full (G : Prop) (AL AH BL BH : ℤ) (z : ℤ) (al pa ah na0 na za bl pb bh nb0 nb zb both : ℕ)
    (t1 m1 : ℕ) (xlo : ℤ) (nnb t2 m2 : ℕ) (ylo : ℤ) (t3 m3 : ℕ) (xhi : ℤ) (t4 m4 : ℕ)
    (yhi lo1 hi1 lo2 hi2 ml mh LO HI : ℤ)
    (hz : z = 0) (hal : al = 1 ↔ AL < z) (hpa : pa = 1 ↔ ¬al = 1) (hah : ah = 1 ↔ z < AH)
    (hna0 : na0 = 1 ↔ ¬ah = 1) (hna : na = 1 ↔ na0 = 1 ∧ al = 1) (hza : za = 1 ↔ al = 1 ∧ ah = 1)
    (hbl : bl = 1 ↔ BL < z) (hpb : pb = 1 ↔ ¬bl = 1) (hbh : bh = 1 ↔ z < BH) (hnb0 : nb0 = 1 ↔ ¬bh = 1)
    (hnb : nb = 1 ↔ nb0 = 1 ∧ bl = 1) (hzb : zb = 1 ↔ bl = 1 ∧ bh = 1) (hboth : both = 1 ↔ za = 1 ∧ zb = 1)
    (ht1 : t1 = 1 ↔ pa = 1 ∧ zb = 1) (hm1 : m1 = 1 ↔ nb = 1 ∨ t1 = 1) (hxlo : xlo = if m1 = 1 then AH else AL)
    (hnnb : nnb = 1 ↔ ¬nb = 1) (ht2 : t2 = 1 ↔ za = 1 ∧ nnb = 1) (hm2 : m2 = 1 ↔ na = 1 ∨ t2 = 1)
    (hylo : ylo = if m2 = 1 then BH else BL)
    (ht3 : t3 = 1 ↔ na = 1 ∧ zb = 1) (hm3 : m3 = 1 ↔ nb = 1 ∨ t3 = 1) (hxhi : xhi = if m3 = 1 then AL else AH)
    (ht4 : t4 = 1 ↔ za = 1 ∧ nb = 1) (hm4 : m4 = 1 ↔ na = 1 ∨ t4 = 1) (hyhi : yhi = if m4 = 1 then BL else BH)
    (hlo1 : lo1 = xlo * ylo / 2 ^ 28) (hhi1 : hi1 = -(-(xhi * yhi) / 2 ^ 28))
    (hlo2 : lo2 = AH * BL / 2 ^ 28) (hhi2 : hi2 = -(-(AL * BL) / 2 ^ 28))
    (hml : ml = min lo1 lo2) (hmh : mh = max hi1 hi2)
    (hLO : LO = if both = 1 then ml else lo1) (hHI : HI = if both = 1 then mh else hi1) :
    G → ∀ r s : ℝ, Enc AL AH r → Enc BL BH s → Enc LO HI (r * s) := by
  intro hG r s hr hs
  subst hz
  have fal : al = 1 ↔ AL < 0 := hal
  have fah : ah = 1 ↔ 0 < AH := hah
  have fbl : bl = 1 ↔ BL < 0 := hbl
  have fbh : bh = 1 ↔ 0 < BH := hbh
  have fpa : pa = 1 ↔ ¬AL < 0 := by rw [hpa, fal]
  have fna : na = 1 ↔ ¬0 < AH ∧ AL < 0 := by rw [hna, hna0, fah, fal]
  have fza : za = 1 ↔ AL < 0 ∧ 0 < AH := by rw [hza, fal, fah]
  have fnb : nb = 1 ↔ ¬0 < BH ∧ BL < 0 := by rw [hnb, hnb0, fbh, fbl]
  have fzb : zb = 1 ↔ BL < 0 ∧ 0 < BH := by rw [hzb, fbl, fbh]
  have fnnb : nnb = 1 ↔ ¬(¬0 < BH ∧ BL < 0) := by rw [hnnb, fnb]
  have exlo : xlo = if (¬0 < BH ∧ BL < 0) ∨ (¬AL < 0 ∧ (BL < 0 ∧ 0 < BH)) then AH else AL := by
    rw [hxlo]; exact if_congr (by rw [hm1, fnb, ht1, fpa, fzb]) rfl rfl
  have eylo : ylo = if (¬0 < AH ∧ AL < 0) ∨ ((AL < 0 ∧ 0 < AH) ∧ ¬(¬0 < BH ∧ BL < 0)) then BH else BL := by
    rw [hylo]; exact if_congr (by rw [hm2, fna, ht2, fza, fnnb]) rfl rfl
  have exhi : xhi = if (¬0 < BH ∧ BL < 0) ∨ ((¬0 < AH ∧ AL < 0) ∧ (BL < 0 ∧ 0 < BH)) then AL else AH := by
    rw [hxhi]; exact if_congr (by rw [hm3, fnb, ht3, fna, fzb]) rfl rfl
  have eyhi : yhi = if (¬0 < AH ∧ AL < 0) ∨ ((AL < 0 ∧ 0 < AH) ∧ (¬0 < BH ∧ BL < 0)) then BL else BH := by
    rw [hyhi]; exact if_congr (by rw [hm4, fna, ht4, fza, fnb]) rfl rfl
  obtain ⟨hx1, hx2⟩ := hr
  obtain ⟨hy1, hy2⟩ := hs
  have hrs : r * s = (2 ^ 28 * r) / 2 ^ 28 * ((2 ^ 28 * s) / 2 ^ 28) := by field_simp
  rw [hrs]
  by_cases hb : (AL < 0 ∧ 0 < AH) ∧ (BL < 0 ∧ 0 < BH)
  · have eb : both = 1 := by rw [hboth, fza, fzb]; exact hb
    obtain ⟨⟨c1, c2⟩, c3, c4⟩ := hb
    have exlo' : xlo = AL := by rw [exlo]; split_ifs <;> omega
    have eylo' : ylo = BH := by rw [eylo]; split_ifs <;> omega
    have key := imul_both AL AH BL BH (2 ^ 28 * r) (2 ^ 28 * s) hx1 hx2 hy1 hy2 ⟨⟨c1, c2⟩, c3, c4⟩
    rw [hLO, hHI, ite_eq_left_of_eq_true _ _ (eq_true eb), ite_eq_left_of_eq_true _ _ (eq_true eb), hml, hmh, hlo1, hhi1, hlo2, hhi2, exlo', eylo']
    have exhi' : xhi = AH := by rw [exhi]; split_ifs <;> omega
    have eyhi' : yhi = BH := by rw [eyhi]; split_ifs <;> omega
    rw [exhi', eyhi']
    apply imul_round2 (min (AL * BH) (AH * BL)) (max (AH * BH) (AL * BL)) _ _ _ _ _ _ key.1 key.2
    · generalize AL * BH = p at *; generalize AH * BL = q at *; omega
    · generalize AH * BH = p at *; generalize AL * BL = q at *; omega
  · have eb : ¬both = 1 := by rw [hboth, fza, fzb]; exact hb
    rw [hLO, hHI, ite_eq_right_of_eq_false _ _ (eq_false eb), ite_eq_right_of_eq_false _ _ (eq_false eb)]
    have key := imul_corner7 AL AH BL BH (2 ^ 28 * r) (2 ^ 28 * s) hx1 hx2 hy1 hy2 hb
    rw [← exlo, ← eylo, ← exhi, ← eyhi] at key
    exact imul_round (xlo * ylo) (xhi * yhi) lo1 hi1 _ _ hlo1 hhi1 (by push_cast; exact key.1)
      (by push_cast; exact key.2)

theorem K8_in_range (G : Prop) (XL XH : ℤ) (a : ℕ) (pih : ℤ) (b c : ℕ) (ha : a = 1 ↔ -1 < XL)
    (hpih : pih = 843314857) (hb : b = 1 ↔ XH ≤ pih) (hc : c = 1 ↔ a = 1 ∧ b = 1) (hck : G → c = 1) :
    G → 0 ≤ XL ∧ XH ≤ 843314857 := by
  intro hG
  have hc1 : c = 1 := hck hG
  have hand : a = 1 ∧ b = 1 := (hc.mp hc1)
  have ha1 : a = 1 := hand.left
  have hb1 : b = 1 := hand.right
  have hneg : -1 < XL := (ha.mp ha1)
  have hXHle : XH ≤ pih := (hb.mp hb1)
  have h0XL : 0 ≤ XL := by omega
  have hXH' : XH ≤ 843314857 := by
    rw [hpih] at hXHle
    exact hXHle
  exact And.intro h0XL hXH'

theorem K9_isin (G : Prop) (XL XH : ℤ) (sl sh mn LO mx t one hi0 : ℤ) (a b m : ℕ) (HI : ℤ)
    (hr : G → 0 ≤ XL ∧ XH ≤ 843314857) (hsl : sl = sinI XL) (hsh : sh = sinI XH) (hmn : mn = min sl sh)
    (hlo : LO = mn + -4) (hmx : mx = max sl sh) (ht : t = mx + 4) (hone : one = 268435456)
    (hhi0 : hi0 = min t one) (ha : a = 1 ↔ XL < 421657430) (hb : b = 1 ↔ 421657427 < XH)
    (hm : m = 1 ↔ a = 1 ∧ b = 1) (hhi : HI = if m = 1 then one else hi0) :
    G → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc LO HI (sin r) := by
  intro hG
  have hXL_nonneg : 0 ≤ XL := (hr hG).1
  have hXH_le : XH ≤ 843314857 := (hr hG).2
  refine ⟨⟨hXL_nonneg, hXH_le⟩, ?_⟩
  intro r hEnc
  rcases hEnc with ⟨hEncL, hEncH⟩
  have hXL_le_XH_real : (XL : ℝ) ≤ (XH : ℝ) := by linarith
  have hXL_le_XH : XL ≤ XH := by exact mod_cast hXL_le_XH_real
  have hXH_nonneg : 0 ≤ XH := le_trans hXL_nonneg hXL_le_XH
  have hXH_real_le : (XH : ℝ) ≤ (843314857 : ℝ) := by exact mod_cast hXH_le
  have hXL_int_le : XL ≤ (PI_LO : ℤ) + 1 := by
    have hXL_real_le : (XL : ℝ) ≤ (843314857 : ℝ) := by linarith
    have h_eq : (843314857 : ℤ) = (PI_LO : ℤ) + 1 := by norm_num [PI_LO]
    simpa [h_eq] using mod_cast hXL_real_le
  have hXH_int_le : XH ≤ (PI_LO : ℤ) + 1 := by
    have h_eq : (843314857 : ℤ) = (PI_LO : ℤ) + 1 := by norm_num [PI_LO]
    simpa [h_eq] using hXH_le
  have hscI_XL_le : scI XL ≤ PI_LO + 1 := by
    dsimp [scI]
    rw [if_neg (not_lt.mpr hXL_nonneg)]
    simpa [show ((PI_LO : ℤ) + 1).toNat = PI_LO + 1 by norm_num [PI_LO]] using Int.toNat_le_toNat hXL_int_le
  have hscI_XH_le : scI XH ≤ PI_LO + 1 := by
    dsimp [scI]
    rw [if_neg (not_lt.mpr hXH_nonneg)]
    simpa [show ((PI_LO : ℤ) + 1).toNat = PI_LO + 1 by norm_num [PI_LO]] using Int.toNat_le_toNat hXH_int_le
  have hscI_XL_eq : (scI XL : ℝ) = (XL : ℝ) := by
    dsimp [scI]
    rw [if_neg (not_lt.mpr hXL_nonneg)]
    exact mod_cast (Int.toNat_of_nonneg hXL_nonneg)
  have hscI_XH_eq : (scI XH : ℝ) = (XH : ℝ) := by
    dsimp [scI]
    rw [if_neg (not_lt.mpr hXH_nonneg)]
    exact mod_cast (Int.toNat_of_nonneg hXH_nonneg)
  have hsl_err' : |(sl : ℝ) - 2 ^ 28 * Real.sin ((XL : ℝ) / 2 ^ 28)| ≤ (4 : ℝ) := by
    rw [← hscI_XL_eq]
    have h := (sc28pS_err (scI XL) hscI_XL_le).1
    have h' : (3 : ℝ) ≤ (4 : ℝ) := by norm_num
    simpa [sinI, hsl] using le_trans h h'
  have hsh_err' : |(sh : ℝ) - 2 ^ 28 * Real.sin ((XH : ℝ) / 2 ^ 28)| ≤ (4 : ℝ) := by
    rw [← hscI_XH_eq]
    have h := (sc28pS_err (scI XH) hscI_XH_le).1
    have h' : (3 : ℝ) ≤ (4 : ℝ) := by norm_num
    simpa [sinI, hsh] using le_trans h h'
  have h_enc_sound := isinX_sound 4 XL XH sl sh hXL_nonneg hXH_int_le hsl_err' hsh_err' (2 ^ 28 * r)
    ⟨hEncL, hEncH⟩
  rcases h_enc_sound with ⟨h_lo, h_hi⟩
  have h_simp : (2 ^ 28 * r) / (2 ^ 28 : ℝ) = r := by
    field_simp [show (2 ^ 28 : ℝ) ≠ 0 by norm_num]
  rw [h_simp] at h_lo h_hi
  have h_lo_eq : (LO : ℝ) = ((isinX 4 XL XH sl sh).1 : ℝ) := by
    dsimp [isinX]
    rw [hlo, hmn]
    rfl
  have h_hi_eq : (HI : ℝ) = ((isinX 4 XL XH sl sh).2 : ℝ) := by
    dsimp [isinX]
    rw [hhi, hone, hhi0, ht, hmx, hone]
    by_cases hm1 : m = 1
    · rw [if_pos hm1]
      have ha1 : a = 1 := (hm.mp hm1).1
      have hb1 : b = 1 := (hm.mp hm1).2
      have hXL_lt : XL < 421657430 := ha.mp ha1
      have hXH_lt : (421657427 : ℤ) < XH := hb.mp hb1
      have h_cond : XL < HPI_HI + 1 ∧ (HPI_LO : ℤ) - 1 < XH := by
        dsimp [HPI_HI, HPI_LO]
        exact ⟨by simpa using hXL_lt, by simpa using hXH_lt⟩
      rw [if_pos h_cond]
    · rw [if_neg hm1]
      have h_cond_false : ¬ (XL < HPI_HI + 1 ∧ (HPI_LO : ℤ) - 1 < XH) := by
        intro hcond
        have hm1' : m = 1 := hm.mpr ⟨ha.mpr hcond.1, hb.mpr hcond.2⟩
        exact hm1 hm1'
      rw [if_neg h_cond_false]
  have h_goal := And.intro h_lo h_hi
  rw [← h_lo_eq, ← h_hi_eq] at h_goal
  exact h_goal

set_option maxHeartbeats 400000 in

theorem K10_icos (G : Prop) (XL XH : ℤ) (lo0 m : ℤ) (atpi : ℕ) (LO hi0 one : ℤ) (at0 : ℕ) (HI : ℤ)
    (hr : G → 0 ≤ XL ∧ XH ≤ 843314857)
    (hlo0 : 0 ≤ XH → XH ≤ 843314857 → (lo0 : ℝ) ≤ 2 ^ 28 * cos ((XH : ℝ) / 2 ^ 28))
    (hm : m = -268435456) (hatpi : atpi = 1 ↔ 843314855 < XH) (hlo : LO = if atpi = 1 then m else lo0)
    (hhi0 : 0 ≤ XL → XL ≤ 843314857 → 2 ^ 28 * cos ((XL : ℝ) / 2 ^ 28) ≤ hi0)
    (hone : one = 268435456) (hat0 : at0 = 1 ↔ XL < 1) (hhi : HI = if at0 = 1 then one else hi0) :
    G → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc LO HI (cos r) := by
  intro hG
  have hXL_XH := hr hG
  rcases hXL_XH with ⟨hXL0, hXH843314857⟩
  have hXL0' : (0 : ℝ) ≤ (XL : ℝ) := by exact_mod_cast hXL0
  have hXH843314857' : (XH : ℝ) ≤ 843314857 := by exact_mod_cast hXH843314857
  refine ⟨⟨hXL0, hXH843314857⟩, ?_⟩
  intro r h_enc
  rcases h_enc with ⟨h_enc_lo, h_enc_hi⟩
  have h_r_ge : (XL : ℝ) / (2 ^ 28 : ℝ) ≤ r := by
    linarith
  have h_r_le : r ≤ (XH : ℝ) / (2 ^ 28 : ℝ) := by
    linarith
  have h_two_pow_pos : 0 < (2 ^ 28 : ℝ) := by norm_num
  have h_pi_gt_d20 : 3.14159265358979323846 < π := Real.pi_gt_d20
  have h_pi_lt_d20 : π < 3.14159265358979323847 := Real.pi_lt_d20

  have h_843314857_div_gt_pi : π < (843314857 : ℝ) / (2 ^ 28 : ℝ) := by
    have h : (3.14159265358979323847 : ℝ) * (2 ^ 28 : ℝ) ≤ (843314857 : ℝ) := by norm_num
    linarith
  have h_843314856_div_lt_pi : (843314856 : ℝ) / (2 ^ 28 : ℝ) < π := by
    have h : (843314856 : ℝ) ≤ (3.14159265358979323846 : ℝ) * (2 ^ 28 : ℝ) := by norm_num
    linarith
  have h_1686629713_div_lt_two_pi : (1686629713 : ℝ) / (2 ^ 28 : ℝ) < 2 * π := by
    have h : (1686629713 : ℝ) ≤ (2 * (3.14159265358979323846 : ℝ)) * (2 ^ 28 : ℝ) := by norm_num
    linarith
  have h_lo : (LO : ℝ) ≤ (2 : ℝ) ^ 28 * cos r := by
    by_cases hXH_gt : (843314855 : ℤ) < XH
    ·
      have hatpi1 : atpi = 1 := (hatpi.mpr hXH_gt)
      have hLO_eq : (LO : ℝ) = -((2 : ℝ) ^ 28) := by
        rw [hlo, hatpi1, hm]
        norm_num
      rw [hLO_eq]
      have h_cos_ge_neg_one : -1 ≤ cos r := Real.neg_one_le_cos r
      nlinarith
    ·
      have hXH_le : XH ≤ (843314855 : ℤ) := by omega
      have hXH_le' : (XH : ℝ) ≤ 843314855 := by exact_mod_cast hXH_le
      have hatpi_ne_one : atpi ≠ 1 := by
        intro h_eq
        have : (843314855 : ℤ) < XH := (hatpi.mp h_eq)
        omega
      have hLO_eq : (LO : ℝ) = (lo0 : ℝ) := by
        rw [hlo]
        simp [hatpi_ne_one]
      rw [hLO_eq]

      have hXH0 : 0 ≤ XH := by
        have h0 : (0 : ℝ) ≤ (XH : ℝ) := by
          linarith [hXL0', h_enc_lo, h_enc_hi]
        exact_mod_cast h0
      have hlo0_bound : (lo0 : ℝ) ≤ (2 : ℝ) ^ 28 * cos ((XH : ℝ) / (2 : ℝ) ^ 28) :=
        hlo0 hXH0 hXH843314857
      have h_cos_le : cos ((XH : ℝ) / (2 : ℝ) ^ 28) ≤ cos r := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ h_r_le
        ·
          linarith [hXL0']
        ·
          have h_div_le : (XH : ℝ) / (2 ^ 28 : ℝ) ≤ (843314855 : ℝ) / (2 ^ 28 : ℝ) :=
            div_le_div_of_nonneg_right hXH_le' (by norm_num)
          have h_843314855_div_le_pi : (843314855 : ℝ) / (2 ^ 28 : ℝ) ≤ π := by
            have : (843314855 : ℝ) / (2 ^ 28 : ℝ) < (843314857 : ℝ) / (2 ^ 28 : ℝ) :=
              div_lt_div_of_pos_right (by norm_num) h_two_pow_pos
            linarith
          linarith
      nlinarith
  have h_hi : (2 : ℝ) ^ 28 * cos r ≤ (HI : ℝ) := by
    by_cases hXL_lt_one : (XL : ℤ) < 1
    ·
      have hat01 : at0 = 1 := (hat0.mpr hXL_lt_one)
      have hHI_eq : (HI : ℝ) = (2 : ℝ) ^ 28 := by
        rw [hhi, hat01, hone]
        norm_num
      rw [hHI_eq]
      have h_cos_le_one : cos r ≤ 1 := Real.cos_le_one r
      nlinarith
    ·
      have hXL_ge_one : (1 : ℤ) ≤ XL := by omega
      have hXL_ge_one' : (1 : ℝ) ≤ (XL : ℝ) := by exact_mod_cast hXL_ge_one
      have hat0_ne_one : at0 ≠ 1 := by
        intro h_eq
        have : (XL : ℤ) < 1 := (hat0.mp h_eq)
        omega
      have hHI_eq : (HI : ℝ) = (hi0 : ℝ) := by
        rw [hhi]
        simp [hat0_ne_one]
      rw [hHI_eq]

      have hXL843314857 : XL ≤ (843314857 : ℤ) := by
        have hXL_le : (XL : ℝ) ≤ 843314857 := by
          linarith [h_enc_lo, h_enc_hi, hXH843314857']
        exact_mod_cast hXL_le
      have hhi0_bound : (2 : ℝ) ^ 28 * cos ((XL : ℝ) / (2 : ℝ) ^ 28) ≤ (hi0 : ℝ) :=
        hhi0 (by omega) hXL843314857
      by_cases h_r_le_pi : r ≤ π
      ·
        have h_cos_le : cos r ≤ cos ((XL : ℝ) / (2 : ℝ) ^ 28) := by
          apply Real.cos_le_cos_of_nonneg_of_le_pi ?_ h_r_le_pi h_r_ge
          nlinarith
        nlinarith
      ·
        have h_r_gt_pi : π < r := by linarith
        have h_cos_eq : cos r = cos (2 * π - r) := by
          rw [Real.cos_two_pi_sub]
        rw [h_cos_eq]
        have h_two_pi_sub_r_nonneg : 0 ≤ 2 * π - r := by
          have h_lt_two_pi : r < 2 * π := by
            have h_843314857_div_lt_2pi : (843314857 : ℝ) / (2 ^ 28 : ℝ) < 2 * π := by
              have h4 : (843314857 : ℝ) / (2 ^ 28 : ℝ) < 4 := by norm_num
              have h_2pi_gt_4 : 4 < 2 * π := by
                have h_pi_gt_3 : 3 < π := by linarith [Real.pi_pos]
                linarith
              linarith
            linarith [h_r_le, h_843314857_div_lt_2pi]
          linarith
        have h_two_pi_sub_r_le_pi : 2 * π - r ≤ π := by linarith
        by_cases hXL_eq : (XL : ℤ) = 843314857
        ·
          have hXL_le_XH : (XL : ℤ) ≤ XH := by
            have hXL_le_XH_real : (XL : ℝ) ≤ (XH : ℝ) := by
              linarith [h_enc_lo, h_enc_hi]
            exact_mod_cast hXL_le_XH_real
          have hXH_eq : XH = (843314857 : ℤ) := by
            have : XH ≤ 843314857 := hXH843314857
            omega
          have hXL_eq_XH : (XL : ℝ) = (XH : ℝ) := by
            rw [hXL_eq, hXH_eq]
          have h_r_eq : r = (XL : ℝ) / (2 : ℝ) ^ 28 := by
            have h1 : (XL : ℝ) ≤ (2 : ℝ) ^ 28 * r := h_enc_lo
            have h2 : (2 : ℝ) ^ 28 * r ≤ (XH : ℝ) := h_enc_hi
            linarith

          have h_cos_eq2 : cos (2 * π - r) = cos ((XL : ℝ) / (2 : ℝ) ^ 28) := by
            rw [h_r_eq, Real.cos_two_pi_sub]
          rw [h_cos_eq2]

          exact hhi0_bound
        ·
          have hXL_le : (XL : ℤ) ≤ 843314856 := by omega
          have hXL_le' : (XL : ℝ) ≤ 843314856 := by exact_mod_cast hXL_le
          have h_ineq : (XL : ℝ) / (2 : ℝ) ^ 28 ≤ 2 * π - r := by
            have h1 : (XL : ℝ) / (2 : ℝ) ^ 28 ≤ (843314856 : ℝ) / (2 : ℝ) ^ 28 :=
              div_le_div_of_nonneg_right hXL_le' (by norm_num)
            have h2 : (843314856 : ℝ) / (2 : ℝ) ^ 28 ≤ 2 * π - r := by
              have h_sum : (843314856 : ℝ) / (2 : ℝ) ^ 28 + (843314857 : ℝ) / (2 : ℝ) ^ 28 ≤ 2 * π := by
                have : (843314856 : ℝ) / (2 : ℝ) ^ 28 + (843314857 : ℝ) / (2 : ℝ) ^ 28 =
                    (1686629713 : ℝ) / (2 : ℝ) ^ 28 := by
                  ring
                rw [this]
                exact h_1686629713_div_lt_two_pi.le
              linarith [h_r_le, h_sum]
            linarith
          have h_cos_le : cos (2 * π - r) ≤ cos ((XL : ℝ) / (2 : ℝ) ^ 28) := by
            apply Real.cos_le_cos_of_nonneg_of_le_pi ?_ h_two_pi_sub_r_le_pi h_ineq
            nlinarith
          nlinarith
  exact ⟨h_lo, h_hi⟩

theorem K11_qdiv (AL AH BL BH : ℤ) (pos bad : ℕ) (z : ℤ) (al : ℕ) (DL : ℤ) (ah : ℕ) (DH : ℤ)
    (hpos : pos = 1 ↔ 0 < BL) (hbad : bad = 1 ↔ ¬pos = 1) (hz : z = 0) (hal : al = 1 ↔ AL < z)
    (hdl : DL = if al = 1 then BL else BH) (hah : ah = 1 ↔ AH < z) (hdh : DH = if ah = 1 then BH else BL) :
    ¬bad = 1 → ∀ r s : ℝ, Enc AL AH r → Enc BL BH s →
        0 < s ∧ 0 < DL ∧ 0 < DH ∧ (AL : ℝ) / DL ≤ r / s ∧ r / s ≤ (AH : ℝ) / DH := by
  intro hnbad
  have hpos1 : pos = 1 := by
    by_contra h
    have hbad1 : bad = 1 := (hbad.mpr h)
    exact hnbad hbad1
  have hBLpos_int : 0 < BL := (hpos.mp hpos1)
  have hBLpos : 0 < (BL : ℝ) := by exact_mod_cast hBLpos_int
  intro r s hEncAL hEncBL
  rcases hEncAL with ⟨hALr, hrAH⟩
  rcases hEncBL with ⟨hBLs, hsBH⟩
  have hy_pos : 0 < (2^28 : ℝ) * s := by
    have hs_nonneg : 0 ≤ s := by
      linarith
    have h2_28_pos : 0 < (2^28 : ℝ) := by norm_num
    nlinarith
  have hBHpos_int : 0 < BH := by
    have hBHpos : 0 < (BH : ℝ) := by
      linarith
    exact_mod_cast hBHpos
  have hBHpos : 0 < (BH : ℝ) := by exact_mod_cast hBHpos_int
  have hposDL_int : 0 < DL := by
    by_cases hal1 : al = 1
    · rw [hdl, if_pos hal1]
      exact hBLpos_int
    · rw [hdl, if_neg hal1]
      exact hBHpos_int
  have hposDH_int : 0 < DH := by
    by_cases hah1 : ah = 1
    · rw [hdh, if_pos hah1]
      exact hBHpos_int
    · rw [hdh, if_neg hah1]
      exact hBLpos_int
  have hAL_nonpos_of_al1 : al = 1 → (AL : ℝ) ≤ 0 := by
    intro hal1
    have h := (hal.mp hal1)
    rw [hz] at h
    exact mod_cast h.le
  have hAL_nonneg_of_al0 : al ≠ 1 → 0 ≤ (AL : ℝ) := by
    intro hal0
    have hnot : ¬ (AL < (0 : ℤ)) := by
      intro hlt
      apply hal0
      exact (hal.mpr (hz ▸ hlt))
    have h := not_lt.mp hnot
    exact mod_cast h
  have hAH_nonpos_of_ah1 : ah = 1 → (AH : ℝ) ≤ 0 := by
    intro hah1
    have h := (hah.mp hah1)
    rw [hz] at h
    exact mod_cast h.le
  have hAH_nonneg_of_ah0 : ah ≠ 1 → 0 ≤ (AH : ℝ) := by
    intro hah0
    have hnot : ¬ (AH < (0 : ℤ)) := by
      intro hlt
      apply hah0
      exact (hah.mpr (hz ▸ hlt))
    have h := not_lt.mp hnot
    exact mod_cast h
  have h_lower : (AL : ℝ) / (DL : ℝ) ≤ r / s := by
    by_cases hal1 : al = 1
    · rw [hdl, if_pos hal1]
      have hAL_nonpos : (AL : ℝ) ≤ 0 := hAL_nonpos_of_al1 hal1
      have h_inv : ((2^28 : ℝ) * s)⁻¹ ≤ (BL : ℝ)⁻¹ := by
        simpa using one_div_le_one_div_of_le hBLpos hBLs
      have h1 : (AL : ℝ) / (BL : ℝ) ≤ (AL : ℝ) / ((2^28 : ℝ) * s) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        simpa [mul_comm] using mul_le_mul_of_nonpos_left h_inv hAL_nonpos
      have h2 : (AL : ℝ) / ((2^28 : ℝ) * s) ≤ r / s := by
        calc
          (AL : ℝ) / ((2^28 : ℝ) * s) ≤ ((2^28 : ℝ) * r) / ((2^28 : ℝ) * s) :=
            div_le_div_of_nonneg_right hALr (by linarith)
          _ = r / s := by
            field_simp [show (2^28 : ℝ) ≠ 0 by norm_num, ne_of_gt hy_pos]
      exact le_trans h1 h2
    · rw [hdl, if_neg hal1]
      have hAL_nonneg : 0 ≤ (AL : ℝ) := hAL_nonneg_of_al0 hal1
      have hy_le_BH : (2^28 : ℝ) * s ≤ (BH : ℝ) := hsBH
      have h1 : (AL : ℝ) / (BH : ℝ) ≤ (AL : ℝ) / ((2^28 : ℝ) * s) :=
        div_le_div_of_nonneg_left hAL_nonneg hy_pos hy_le_BH
      have h2 : (AL : ℝ) / ((2^28 : ℝ) * s) ≤ r / s := by
        calc
          (AL : ℝ) / ((2^28 : ℝ) * s) ≤ ((2^28 : ℝ) * r) / ((2^28 : ℝ) * s) :=
            div_le_div_of_nonneg_right hALr (by linarith)
          _ = r / s := by
            field_simp [show (2^28 : ℝ) ≠ 0 by norm_num, ne_of_gt hy_pos]
      exact le_trans h1 h2
  have h_upper : r / s ≤ (AH : ℝ) / (DH : ℝ) := by
    by_cases hah1 : ah = 1
    · rw [hdh, if_pos hah1]
      have hAH_nonpos : (AH : ℝ) ≤ 0 := hAH_nonpos_of_ah1 hah1
      have h_inv : (BH : ℝ)⁻¹ ≤ ((2^28 : ℝ) * s)⁻¹ := by
        simpa using one_div_le_one_div_of_le hy_pos hsBH
      have h1 : r / s ≤ (AH : ℝ) / ((2^28 : ℝ) * s) := by
        calc
          r / s = ((2^28 : ℝ) * r) / ((2^28 : ℝ) * s) := by
            field_simp [show (2^28 : ℝ) ≠ 0 by norm_num, ne_of_gt hy_pos]
          _ ≤ (AH : ℝ) / ((2^28 : ℝ) * s) :=
            div_le_div_of_nonneg_right hrAH (by linarith)
      have h2 : (AH : ℝ) / ((2^28 : ℝ) * s) ≤ (AH : ℝ) / (BH : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        simpa [mul_comm] using mul_le_mul_of_nonpos_left h_inv hAH_nonpos
      exact le_trans h1 h2
    · rw [hdh, if_neg hah1]
      have hAH_nonneg : 0 ≤ (AH : ℝ) := hAH_nonneg_of_ah0 hah1
      have hBL_le_y : (BL : ℝ) ≤ (2^28 : ℝ) * s := hBLs
      have h1 : r / s ≤ (AH : ℝ) / ((2^28 : ℝ) * s) := by
        calc
          r / s = ((2^28 : ℝ) * r) / ((2^28 : ℝ) * s) := by
            field_simp [show (2^28 : ℝ) ≠ 0 by norm_num, ne_of_gt hy_pos]
          _ ≤ (AH : ℝ) / ((2^28 : ℝ) * s) :=
            div_le_div_of_nonneg_right hrAH (by linarith)
      have h2 : (AH : ℝ) / ((2^28 : ℝ) * s) ≤ (AH : ℝ) / (BL : ℝ) :=
        div_le_div_of_nonneg_left hAH_nonneg hBLpos hBL_le_y
      exact le_trans h1 h2
  exact ⟨by linarith, hposDL_int, hposDH_int, h_lower, h_upper⟩

theorem K12_atan_lo (N D : ℤ) (z : ℤ) (ng : ℕ) (nn a beta : ℤ) (lot : ℕ) (cl ch sh sl cc ss l r : ℤ)
    (lle lge b0 nb0 : ℕ) (hl : ℤ) (bhl cnn t1 t2 clo : ℕ) (hh : ℤ) (top chi x nl y c : ℕ) (nb rr tt OUT : ℤ)
    (hz : z = 0) (hng : ng = 1 ↔ N < z) (hnn : nn = z - N) (ha : a = if ng = 1 then nn else N) (hbeta : 0 ≤ beta)
    (hlot : lot = 1 ↔ ¬ng = 1)
    (hcl : 0 ≤ beta → beta ≤ 843314857 → (cl : ℝ) ≤ 2 ^ 28 * cos ((beta : ℝ) / 2 ^ 28))
    (hch : 0 ≤ beta → beta ≤ 843314857 → 2 ^ 28 * cos ((beta : ℝ) / 2 ^ 28) ≤ ch)
    (hsh : 0 ≤ beta → beta ≤ 843314857 → 2 ^ 28 * sin ((beta : ℝ) / 2 ^ 28) ≤ sh)
    (hsl : 0 ≤ beta → beta ≤ 843314857 → (sl : ℝ) ≤ 2 ^ 28 * sin ((beta : ℝ) / 2 ^ 28))
    (hcc : cc = if lot = 1 then cl else ch) (hss : ss = if lot = 1 then sh else sl) (hl' : l = ss * D)
    (hr : r = a * cc) (hlle : lle = 1 ↔ l ≤ r) (hlge : lge = 1 ↔ r ≤ l) (hb0 : b0 = 1 ↔ z < beta)
    (hnb0 : nb0 = 1 ↔ ¬b0 = 1) (hhl : hl = 421657428) (hbhl : bhl = 1 ↔ beta ≤ hl) (hcnn : cnn = 1 ↔ -1 < cl)
    (ht1 : t1 = 1 ↔ lle = 1 ∧ cnn = 1) (ht2 : t2 = 1 ↔ t1 = 1 ∧ bhl = 1) (hclo : clo = 1 ↔ nb0 = 1 ∨ t2 = 1)
    (hhh : hh = 421657429) (htop : top = 1 ↔ hh ≤ beta) (hchi : chi = 1 ↔ top = 1 ∨ lge = 1)
    (hx : x = 1 ↔ lot = 1 ∧ clo = 1) (hnl : nl = 1 ↔ ¬lot = 1) (hy : y = 1 ↔ nl = 1 ∧ chi = 1)
    (hc : c = 1 ↔ x = 1 ∨ y = 1) (hnb : nb = z - beta) (hrr : rr = if ng = 1 then nb else beta)
    (htt : tt = -421657429) (hout : OUT = if c = 1 then rr else tt) :
    0 < D → ∀ q : ℝ, (N : ℝ) / D ≤ q → (OUT : ℝ) / 2 ^ 28 ≤ arctan q := by
  intro hD q hq
  subst hz
  have hat := Real.neg_pi_div_two_lt_arctan q
  have hpi : π < 3.14159265358979323847 := Real.pi_lt_d20
  have eng : ng = 1 ↔ N < 0 := hng
  have ea : a = |N| := by
    rw [ha, hnn]
    split_ifs with h
    · rw [abs_of_neg (eng.1 h)]; ring
    · rw [abs_of_nonneg (not_lt.1 (fun h' => h (eng.2 h')))]
  have e1 : lot = 1 ↔ ¬ N < 0 := by rw [hlot, eng]
  have err : rr = if N < 0 then -beta else beta := by
    rw [hrr, hnb]; simp only [eng]; split_ifs <;> ring
  have eclo : clo = 1 ↔ (beta ≤ 0 ∨ (l ≤ r ∧ 0 ≤ cl ∧ beta ≤ 421657428)) := by
    rw [hclo, hnb0, hb0, ht2, ht1, hlle, hcnn, hbhl, hhl]; omega
  have echi : chi = 1 ↔ (421657429 ≤ beta ∨ r ≤ l) := by rw [hchi, htop, hhh, hlge]
  have ec : c = 1 ↔ ((¬ N < 0) ∧ (beta ≤ 0 ∨ (l ≤ r ∧ 0 ≤ cl ∧ beta ≤ 421657428))) ∨
      (N < 0 ∧ (421657429 ≤ beta ∨ r ≤ l)) := by
    rw [hc, hx, hy, hnl, e1, eclo, echi, not_not]
  by_cases hbig : beta ≤ 843314857
  · have hE : OUT = atanEndX false N D beta sl sh cl ch := by
      unfold atanEndX
      have ecc : cc = if N < 0 then ch else cl := by rw [hcc]; simp only [e1]; split_ifs <;> simp_all
      have ess : ss = if N < 0 then sl else sh := by rw [hss]; simp only [e1]; split_ifs <;> simp_all
      rw [hl', hr, ea, ecc, ess] at ec
      rw [hout, err, htt]
      by_cases hN : N < 0
      · simp only [hN, ite_true, not_true_eq_false, false_and, true_and, false_or] at ec ⊢
        simp [HPI_HI, HPI_LO, ec]
      · simp only [hN, ite_false, not_false_eq_true, true_and, false_and, or_false] at ec ⊢
        simp [HPI_HI, HPI_LO, ec]
    rw [hE]
    exact atanEndX_lo_sound N D beta sl sh cl ch hD hbeta ⟨hsl hbeta hbig, hsh hbeta hbig⟩
      ⟨hcl hbeta hbig, hch hbeta hbig⟩ q hq
  · have hO : OUT ≤ -421657429 := by
      rw [hout, err, htt]
      split_ifs <;> omega
    have : (OUT : ℝ) ≤ -421657429 := by exact_mod_cast hO
    have h2 : (OUT : ℝ) / 2 ^ 28 ≤ -421657429 / 2 ^ 28 := by
      apply div_le_div_of_nonneg_right this (by norm_num)
    linarith

theorem K12_atan_hi (N D : ℤ) (z : ℤ) (ng : ℕ) (nn a beta : ℤ) (cl ch sh sl cc ss l r : ℤ)
    (lle lge b0 nb0 : ℕ) (hl : ℤ) (bhl cnn t1 t2 clo : ℕ) (hh : ℤ) (top chi x nl y c : ℕ) (nb rr tt OUT : ℤ)
    (hz : z = 0) (hng : ng = 1 ↔ N < z) (hnn : nn = z - N) (ha : a = if ng = 1 then nn else N) (hbeta : 0 ≤ beta)
    (hcl : 0 ≤ beta → beta ≤ 843314857 → (cl : ℝ) ≤ 2 ^ 28 * cos ((beta : ℝ) / 2 ^ 28))
    (hch : 0 ≤ beta → beta ≤ 843314857 → 2 ^ 28 * cos ((beta : ℝ) / 2 ^ 28) ≤ ch)
    (hsh : 0 ≤ beta → beta ≤ 843314857 → 2 ^ 28 * sin ((beta : ℝ) / 2 ^ 28) ≤ sh)
    (hsl : 0 ≤ beta → beta ≤ 843314857 → (sl : ℝ) ≤ 2 ^ 28 * sin ((beta : ℝ) / 2 ^ 28))
    (hcc : cc = if ng = 1 then cl else ch) (hss : ss = if ng = 1 then sh else sl) (hl' : l = ss * D)
    (hr : r = a * cc) (hlle : lle = 1 ↔ l ≤ r) (hlge : lge = 1 ↔ r ≤ l) (hb0 : b0 = 1 ↔ z < beta)
    (hnb0 : nb0 = 1 ↔ ¬b0 = 1) (hhl : hl = 421657428) (hbhl : bhl = 1 ↔ beta ≤ hl) (hcnn : cnn = 1 ↔ -1 < cl)
    (ht1 : t1 = 1 ↔ lle = 1 ∧ cnn = 1) (ht2 : t2 = 1 ↔ t1 = 1 ∧ bhl = 1) (hclo : clo = 1 ↔ nb0 = 1 ∨ t2 = 1)
    (hhh : hh = 421657429) (htop : top = 1 ↔ hh ≤ beta) (hchi : chi = 1 ↔ top = 1 ∨ lge = 1)
    (hx : x = 1 ↔ ng = 1 ∧ clo = 1) (hnl : nl = 1 ↔ ¬ng = 1) (hy : y = 1 ↔ nl = 1 ∧ chi = 1)
    (hc : c = 1 ↔ x = 1 ∨ y = 1) (hnb : nb = z - beta) (hrr : rr = if ng = 1 then nb else beta)
    (htt : tt = 421657429) (hout : OUT = if c = 1 then rr else tt) :
    0 < D → ∀ q : ℝ, q ≤ (N : ℝ) / D → arctan q ≤ (OUT : ℝ) / 2 ^ 28 := by
  intro hD q hq
  subst hz
  have hat := Real.arctan_lt_pi_div_two q
  have hpi : 3.14159265358979323846 < π := Real.pi_gt_d20
  have hpi' : π < 3.14159265358979323847 := Real.pi_lt_d20
  have eng : ng = 1 ↔ N < 0 := hng
  have ea : a = |N| := by
    rw [ha, hnn]
    split_ifs with h
    · rw [abs_of_neg (eng.1 h)]; ring
    · rw [abs_of_nonneg (not_lt.1 (fun h' => h (eng.2 h')))]
  have err : rr = if N < 0 then -beta else beta := by
    rw [hrr, hnb]; simp only [eng]; split_ifs <;> ring
  have eclo : clo = 1 ↔ (beta ≤ 0 ∨ (l ≤ r ∧ 0 ≤ cl ∧ beta ≤ 421657428)) := by
    rw [hclo, hnb0, hb0, ht2, ht1, hlle, hcnn, hbhl, hhl]; omega
  have echi : chi = 1 ↔ (421657429 ≤ beta ∨ r ≤ l) := by rw [hchi, htop, hhh, hlge]
  have ec : c = 1 ↔ (N < 0 ∧ (beta ≤ 0 ∨ (l ≤ r ∧ 0 ≤ cl ∧ beta ≤ 421657428))) ∨
      ((¬ N < 0) ∧ (421657429 ≤ beta ∨ r ≤ l)) := by
    rw [hc, hx, hy, hnl, eng, eclo, echi]
  by_cases hbig : beta ≤ 843314857
  · have hE : OUT = atanEndX true N D beta sl sh cl ch := by
      unfold atanEndX
      have ecc : cc = if N < 0 then cl else ch := by rw [hcc]; simp only [eng]
      have ess : ss = if N < 0 then sh else sl := by rw [hss]; simp only [eng]
      rw [hl', hr, ea, ecc, ess] at ec
      rw [hout, err, htt]
      by_cases hN : N < 0
      · simp only [hN, ite_true, not_true_eq_false, false_and, true_and, or_false] at ec ⊢
        simp [HPI_HI, HPI_LO, ec]
      · simp only [hN, ite_false, not_false_eq_true, true_and, false_and, false_or] at ec ⊢
        simp [HPI_HI, HPI_LO, ec]
    rw [hE]
    exact atanEndX_hi_sound N D beta sl sh cl ch hD hbeta ⟨hsl hbeta hbig, hsh hbeta hbig⟩
      ⟨hcl hbeta hbig, hch hbeta hbig⟩ q hq
  · have hO : 421657429 ≤ OUT := by
      rw [hout, err, htt]
      split_ifs with h1 h2
      · exfalso
        rw [ec] at h1
        omega
      · omega
      · omega
    have : (421657429 : ℝ) ≤ OUT := by exact_mod_cast hO
    have h2 : (421657429 : ℝ) / 2 ^ 28 ≤ OUT / 2 ^ 28 := by
      apply div_le_div_of_nonneg_right this (by norm_num)
    linarith

theorem K13_acos_lo (N D : ℤ) (a z : ℤ) (a0 na0 : ℕ) (cl n28 cd : ℤ) (s1 : ℕ) (pl : ℤ) (s2 s c : ℕ) (OUT : ℤ)
    (ha : 0 ≤ a) (hz : z = 0) (ha0 : a0 = 1 ↔ z < a) (hna0 : na0 = 1 ↔ ¬a0 = 1)
    (hcl : 0 ≤ a → a ≤ 843314857 → (cl : ℝ) ≤ 2 ^ 28 * cos ((a : ℝ) / 2 ^ 28)) (hn28 : n28 = N * 2 ^ 28)
    (hcd : cd = cl * D) (hs1 : s1 = 1 ↔ n28 ≤ cd) (hpl : pl = 843314856) (hs2 : s2 = 1 ↔ a ≤ pl)
    (hs : s = 1 ↔ s1 = 1 ∧ s2 = 1) (hc : c = 1 ↔ na0 = 1 ∨ s = 1) (hout : OUT = if c = 1 then a else z) :
    0 < D → ∀ y : ℝ, y ≤ (N : ℝ) / D → -1 ≤ y → (OUT : ℝ) / 2 ^ 28 ≤ arccos y := by
  intro hDpos y hy hyle1
  have ha0_iff : (a0 = 1) ↔ (0 : ℤ) < a := by
    simpa [hz] using ha0
  have hna0_iff : (na0 = 1) ↔ a ≤ 0 := by
    rw [hna0, ha0_iff]
    exact ⟨not_lt.mp, not_lt.mpr⟩
  have hs1_iff : (s1 = 1) ↔ (N * 2 ^ 28 ≤ cl * D) := by
    simpa [hn28, hcd] using hs1
  have hs2_iff : (s2 = 1) ↔ a ≤ (PI_LO : ℤ) := by
    simpa [hpl, PI_LO] using hs2
  have hs_iff : (s = 1) ↔ (N * 2 ^ 28 ≤ cl * D ∧ a ≤ (PI_LO : ℤ)) := by
    rw [hs]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨hs1_iff.mp h1, hs2_iff.mp h2⟩
    · intro ⟨h1, h2⟩; exact ⟨hs1_iff.mpr h1, hs2_iff.mpr h2⟩
  have hc_iff : (c = 1) ↔ (a ≤ 0 ∨ (N * 2 ^ 28 ≤ cl * D ∧ a ≤ (PI_LO : ℤ))) := by
    rw [hc]
    constructor
    · intro h; rcases h with (h | h)
      · exact Or.inl (hna0_iff.mp h)
      · exact Or.inr (hs_iff.mp h)
    · intro h; rcases h with (h | h)
      · exact Or.inl (hna0_iff.mpr h)
      · exact Or.inr (hs_iff.mpr h)
  have hOUT_eq : OUT = acosLoX N D a cl := by
    rw [hout, hz]
    simp [acosLoX, hc_iff]
  rw [hOUT_eq]
  by_cases ha_le : a ≤ 843314857
  · have hcl_bound : (cl : ℝ) ≤ 2 ^ 28 * cos ((a : ℝ) / 2 ^ 28) := hcl ha ha_le
    have h := D3Ck2Spec.acosLoX_sound N D a cl hDpos ha hcl_bound y hy hyle1
    simpa using h
  · have ha_pos : 0 < a := by
      have : (843314857 : ℤ) ≤ a := by omega
      omega
    have h_not_le : ¬ (a ≤ 0 ∨ (N * 2 ^ 28 ≤ cl * D ∧ a ≤ (PI_LO : ℤ))) := by
      intro h
      rcases h with (h0 | ⟨_, hle⟩)
      · omega
      · have hPI : (PI_LO : ℤ) = 843314856 := rfl
        rw [hPI] at hle
        omega
    have hacos_eq_zero : acosLoX N D a cl = 0 := by
      rw [acosLoX]
      exact if_neg h_not_le
    rw [hacos_eq_zero]
    norm_num
    exact Real.arccos_nonneg _

theorem K13_acos_hi (N D : ℤ) (a ph : ℤ) (top : ℕ) (ch n28 cd : ℤ) (s1 c : ℕ) (OUT : ℤ)
    (ha : 0 ≤ a) (hph : ph = 843314857) (htop : top = 1 ↔ ph ≤ a)
    (hch : 0 ≤ a → a ≤ 843314857 → 2 ^ 28 * cos ((a : ℝ) / 2 ^ 28) ≤ ch) (hn28 : n28 = N * 2 ^ 28)
    (hcd : cd = ch * D) (hs1 : s1 = 1 ↔ cd ≤ n28) (hc : c = 1 ↔ top = 1 ∨ s1 = 1)
    (hout : OUT = if c = 1 then a else ph) :
    0 < D → ∀ y : ℝ, (N : ℝ) / D ≤ y → y ≤ 1 → arccos y ≤ (OUT : ℝ) / 2 ^ 28 := by
  intro hDpos y hNy hy1
  have hPI_eq : (PI_LO : ℤ) + 1 = (843314857 : ℤ) := by decide
  have hc_cond : (c = 1) ↔ ((PI_LO : ℤ) + 1 ≤ a ∨ ch * D ≤ N * 2 ^ 28) := by
    rw [hc, htop, hs1, hcd, hn28, hph, hPI_eq]
  have hOUT_eq : (OUT : ℝ) = (acosHiX N D a ch : ℝ) := by
    have hOUT_int : OUT = acosHiX N D a ch := by
      rw [hout, acosHiX, hph, hPI_eq]
      by_cases hc1 : c = 1
      · have h_cond : (843314857 : ℤ) ≤ a ∨ ch * D ≤ N * 2 ^ 28 := by
          rw [← hPI_eq]
          exact hc_cond.mp hc1
        rw [ite_eq_left hc1, ite_eq_left h_cond]
      · have h_not_cond : ¬ ((843314857 : ℤ) ≤ a ∨ ch * D ≤ N * 2 ^ 28) := by
          rw [← hPI_eq]
          exact mt (hc_cond.mpr) hc1
        rw [ite_eq_right hc1, ite_eq_right h_not_cond]
    exact congrArg (fun x : ℤ => (x : ℝ)) hOUT_int
  rw [hOUT_eq]
  by_cases ha_le : a ≤ (843314857 : ℤ)
  · have h_hch : 2 ^ 28 * Real.cos ((a : ℝ) / 2 ^ 28) ≤ (ch : ℝ) := hch ha ha_le
    exact acosHiX_sound N D a ch hDpos ha h_hch y hNy hy1
  · have ha_gt : (843314857 : ℤ) < a := by omega
    have hph_le_a : ph ≤ a := by
      rw [hph]
      exact ha_gt.le
    have htop1 : top = 1 := (htop.mpr hph_le_a)
    have hc1 : c = 1 := by
      rw [hc]
      left
      exact htop1
    have hacos_eq_a : acosHiX N D a ch = a := by
      rw [acosHiX, hPI_eq]
      have h_cond : (843314857 : ℤ) ≤ a ∨ ch * D ≤ N * 2 ^ 28 := by
        rw [← hPI_eq]
        exact hc_cond.mp hc1
      rw [ite_eq_left h_cond]
    rw [hacos_eq_a]
    have harccos_le_pi : Real.arccos y ≤ Real.pi := Real.arccos_le_pi y
    have hpi_lt_a_div : Real.pi < (a : ℝ) / (2 ^ 28 : ℝ) := by
      have hpi_lt_d20 : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
      have h_bound : (3.14159265358979323847 : ℝ) * (2 ^ 28 : ℝ) ≤ (843314858 : ℝ) := by
        norm_num
      have ha_int_ge : (843314858 : ℤ) ≤ a := by
        omega
      have ha_real_ge : (843314858 : ℝ) ≤ (a : ℝ) := by exact mod_cast ha_int_ge
      have h_mul : Real.pi * (2 ^ 28 : ℝ) < (a : ℝ) := by
        linarith
      have hpos : (0 : ℝ) < (2 ^ 28 : ℝ) := by norm_num
      exact (lt_div_iff₀ hpos).mpr h_mul
    linarith

end D3Prog.L2
