import Tammes15.D3Prog.L2B.Base

namespace D3Prog.L2B

open Real Tammes15 D3Ck2Spec D3Prog.L2

set_option linter.unusedVariables false

theorem K27_corner (UL UH : ℤ) (m side : ℕ) (s tp : ℤ) (lp : ℕ) (LEH pl : ℤ) (hp : ℕ) (mx HEL l h LO HI : ℤ)
    (hs : s = UL + UH) (htp : tp = 1686629712) (hlp : lp = 1 ↔ s ≤ tp) (hleh : LEH = if lp = 1 then UL else UH)
    (hpl : pl = 843314856) (hhp : hp = 1 ↔ UH ≤ pl) (hmx : mx = max UL pl) (hhel : HEL = if hp = 1 then UH else mx)
    (hl : l = if side = 1 then UL else HEL) (hh : h = if side = 1 then LEH else UH)
    (hlo : LO = if m = 1 then l else UL) (hhi : HI = if m = 1 then h else UH) :
    ∀ t : ℝ, Enc UL UH t → t ≤ π → ∃ w : ℝ, Enc LO HI w ∧ (UL : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((UH : ℝ) / 2 ^ 28) π ∧ (m = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬m = 1 → w = t) := by
  intro t ht htpi
  have hmem := mem_of_enc ht
  rcases hmem with ⟨hmem_lo, hmem_hi⟩
  have hle_int : UL ≤ UH := Enc.le ht
  have h28pos : (0 : ℝ) < 2 ^ 28 := by norm_num
  have h28pos_nonneg : 0 ≤ (2 : ℝ) ^ 28 := by norm_num
  by_cases hm : m = 1
  ·
    have hLO : LO = l := by
      simp [hlo, hm]
    have hHI : HI = h := by
      simp [hhi, hm]
    rw [hLO, hHI]
    by_cases hside : side = 1
    ·
      have hl_eq : l = UL := by
        rw [hl, ite_eq_left hside]
      have hh_eq : h = LEH := by
        rw [hh, ite_eq_left hside]
      rw [hl_eq, hh_eq]
      have hUL_le_LEH : (UL : ℝ) ≤ (LEH : ℝ) := by
        by_cases hlp1 : lp = 1
        · rw [hleh, ite_eq_left hlp1]
        · rw [hleh, ite_eq_right hlp1]; exact mod_cast hle_int
      refine ⟨(UL : ℝ) / 2 ^ 28, ?_, ?_, ?_, ?_, ?_⟩
      ·
        constructor
        ·
          have h_eq : (UL : ℝ) = 2 ^ 28 * ((UL : ℝ) / 2 ^ 28) := by
            field_simp [show (2 : ℝ) ^ 28 ≠ 0 by norm_num]
          exact h_eq.le
        ·
          have h_eq : 2 ^ 28 * ((UL : ℝ) / 2 ^ 28) = (UL : ℝ) := by
            field_simp [show (2 : ℝ) ^ 28 ≠ 0 by norm_num]
          rw [h_eq]
          exact hUL_le_LEH
      ·
        rfl
      ·
        have h1 : (UL : ℝ) / 2 ^ 28 ≤ (UH : ℝ) / 2 ^ 28 := by
          have hle_int' : (UL : ℝ) ≤ (UH : ℝ) := mod_cast hle_int
          exact (div_le_div_of_nonneg_right hle_int' (by norm_num : 0 ≤ (2 : ℝ) ^ 28))
        have h2 : (UL : ℝ) / 2 ^ 28 ≤ π := by linarith
        exact le_min h1 h2
      ·
        intro hm1
        constructor
        · intro hside1; exact hmem_lo
        · intro hside_not1; exfalso; exact hside_not1 hside
      ·
        intro hm1; exfalso; exact hm1 hm
    ·
      have hl_eq : l = HEL := by
        rw [hl, ite_eq_right hside]
      have hh_eq : h = UH := by
        rw [hh, ite_eq_right hside]
      rw [hl_eq, hh_eq]
      set w := min ((UH : ℝ) / 2 ^ 28) π with hw_def
      have hw_le_UH_div : w ≤ (UH : ℝ) / 2 ^ 28 := min_le_left _ _
      have hw_le_pi : w ≤ π := min_le_right _ _
      have h_mul_min_eq : 2 ^ 28 * w = min ((UH : ℝ)) (2 ^ 28 * π) := by
        rw [hw_def]
        rw [mul_min_of_nonneg _ _ h28pos_nonneg]
        congr 1
        field_simp
      have h_enc_HEL_UH : Enc HEL UH w := by
        constructor
        ·
          rw [h_mul_min_eq]
          by_cases hp1 : hp = 1
          ·
            have hHEL : HEL = UH := by
              rw [hhel, ite_eq_left hp1]
            rw [hHEL]
            have hUH_le_843314856 : UH ≤ (843314856 : ℤ) := by
              have := (hhp.mp hp1)
              rw [hpl] at this
              exact this
            have hUH_le_2pi : (UH : ℝ) ≤ 2 ^ 28 * π := by
              have h_lt : (843314856 : ℝ) < 2 ^ 28 * π := pi_lo_lt
              have hUH_le_843314856' : (UH : ℝ) ≤ (843314856 : ℝ) := mod_cast hUH_le_843314856
              linarith
            exact le_min (le_refl _) hUH_le_2pi
          ·
            have hHEL : HEL = mx := by
              rw [hhel, ite_eq_right hp1]
            rw [hHEL, hmx, hpl]
            have h843314856_le_UH : (843314856 : ℤ) ≤ UH := by
              have h_notle : ¬ UH ≤ (843314856 : ℤ) := by
                rw [← hpl, ← hhp]
                exact hp1
              exact le_of_lt (lt_of_not_ge h_notle)
            have h843314856_le_UH' : (843314856 : ℝ) ≤ (UH : ℝ) := by exact mod_cast h843314856_le_UH
            have h843314856_le_2pi : (843314856 : ℝ) ≤ 2 ^ 28 * π := by
              linarith [pi_lo_lt]
            have hUL_le_2pi : (UL : ℝ) ≤ 2 ^ 28 * π := by
              have hpos : (0 : ℝ) ≤ 2 ^ 28 := by norm_num
              calc
                (UL : ℝ) = ((UL : ℝ) / 2 ^ 28) * 2 ^ 28 := by field_simp
                _ ≤ t * 2 ^ 28 := by
                  nlinarith
                _ ≤ π * 2 ^ 28 := by nlinarith
                _ = 2 ^ 28 * π := by ring
            push_cast
            apply max_le
            · apply le_min
              · exact mod_cast hle_int
              · exact hUL_le_2pi
            · apply le_min
              · exact h843314856_le_UH'
              · exact h843314856_le_2pi
        ·
          rw [h_mul_min_eq]
          exact min_le_left _ _
      refine ⟨w, h_enc_HEL_UH, ?_, ?_, ?_, ?_⟩
      ·
        have h1 : (UL : ℝ) / 2 ^ 28 ≤ (UH : ℝ) / 2 ^ 28 := by
          have hle_int' : (UL : ℝ) ≤ (UH : ℝ) := mod_cast hle_int
          exact (div_le_div_of_nonneg_right hle_int' (by norm_num : 0 ≤ (2 : ℝ) ^ 28))
        have h2 : (UL : ℝ) / 2 ^ 28 ≤ π := by linarith
        exact le_min h1 h2
      ·
        rfl
      ·
        intro hm1
        constructor
        · intro hside1; exfalso; exact hside hside1
        · intro hside_not1
          have h1 : t ≤ (UH : ℝ) / 2 ^ 28 := by
            linarith
          have h2 : t ≤ π := htpi
          exact le_min h1 h2
      ·
        intro hm1; exfalso; exact hm1 hm
  ·
    have hLO : LO = UL := by
      simp [hlo, hm]
    have hHI : HI = UH := by
      simp [hhi, hm]
    rw [hLO, hHI]
    refine ⟨t, ht, hmem_lo, ?_, ?_, ?_⟩
    ·
      have h1 : t ≤ (UH : ℝ) / 2 ^ 28 := by
        linarith
      have h2 : t ≤ π := htpi
      exact le_min h1 h2
    ·
      intro hm1; exfalso; exact hm hm1
    ·
      intro hm1; rfl

theorem K27_corner_fixed (UL UH : ℤ) (side : ℕ) (s tp : ℤ) (lp : ℕ) (LEH pl : ℤ) (hp : ℕ) (mx HEL LO HI : ℤ)
    (hs : s = UL + UH) (htp : tp = 1686629712) (hlp : lp = 1 ↔ s ≤ tp) (hleh : LEH = if lp = 1 then UL else UH)
    (hpl : pl = 843314856) (hhp : hp = 1 ↔ UH ≤ pl) (hmx : mx = max UL pl) (hhel : HEL = if hp = 1 then UH else mx)
    (hlo : LO = if side = 1 then HEL else UL) (hhi : HI = if side = 1 then UH else LEH) :
    ∀ t : ℝ, Enc UL UH t → t ≤ π → ∃ w : ℝ, Enc LO HI w ∧ (UL : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((UH : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t) := by
  intro t ht_enc ht_pi
  rcases ht_enc with ⟨hULt_mul, htUH_mul⟩
  have hUL_le_UH : UL ≤ UH := Enc.le ⟨hULt_mul, htUH_mul⟩
  have hUL_le_UH_real : (UL : ℝ) ≤ (UH : ℝ) := by exact_mod_cast hUL_le_UH
  have hpos : 0 < (2 ^ 28 : ℝ) := by norm_num
  have hpos' : 0 ≤ (2 ^ 28 : ℝ) := by norm_num

  have hULt_div : (UL : ℝ) / 2 ^ 28 ≤ t := by
    rw [div_le_iff₀ hpos]

    rw [mul_comm]
    exact hULt_mul
  have htUH_div : t ≤ (UH : ℝ) / 2 ^ 28 := by
    rw [le_div_iff₀ hpos]

    rw [mul_comm]
    exact htUH_mul
  have hULt_div_pi : (UL : ℝ) / 2 ^ 28 ≤ π := by
    linarith
  by_cases hside : side = 1
  ·
    have hLO : LO = HEL := by
      rw [hlo, ite_eq_left hside]
    have hHI : HI = UH := by
      rw [hhi, ite_eq_left hside]
    rw [hLO, hHI]
    set w := min ((UH : ℝ) / 2 ^ 28) π with hw_def
    have hw_mul_UH : 2 ^ 28 * w ≤ (UH : ℝ) := by
      rw [hw_def]
      calc
        2 ^ 28 * min ((UH : ℝ) / 2 ^ 28) π ≤ 2 ^ 28 * ((UH : ℝ) / 2 ^ 28) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hpos'
        _ = (UH : ℝ) := by field_simp
    have ht_le_w : t ≤ w := le_min htUH_div ht_pi
    have hEnc_HEL_UH_w : Enc HEL UH w := by
      rw [Enc]
      have hHEL_le_mul : (HEL : ℝ) ≤ 2 ^ 28 * w := by
        rw [hhel]
        by_cases hp1 : hp = 1
        · rw [ite_eq_left hp1]

          have hUH_le_843314856 : UH ≤ (843314856 : ℤ) := by
            rw [← hpl]
            exact (hhp.mp hp1)
          have hUH_le_843314856_real : (UH : ℝ) ≤ (843314856 : ℝ) := by exact_mod_cast hUH_le_843314856
          have h_lt_pi : (UH : ℝ) / 2 ^ 28 < π := by
            have h := pi_lo_lt
            linarith
          have h_min_eq : min ((UH : ℝ) / 2 ^ 28) π = (UH : ℝ) / 2 ^ 28 := min_eq_left (by linarith)
          rw [hw_def, h_min_eq]
          field_simp
          exact le_rfl
        · rw [ite_eq_right hp1, hmx, hpl]

          have h_cast_max : ((max UL (843314856 : ℤ) : ℤ) : ℝ) = max ((UL : ℤ) : ℝ) ((843314856 : ℤ) : ℝ) := by
            simp
          rw [h_cast_max, max_le_iff]
          constructor
          ·
            have h_min_ge_t : t ≤ min ((UH : ℝ) / 2 ^ 28) π := ht_le_w
            linarith
          ·
            have h_not_UH_le : ¬ UH ≤ (843314856 : ℤ) := by
              intro hle
              apply hp1

              have hle' : UH ≤ pl := hpl ▸ hle
              exact hhp.mpr hle'
            have h_843314856_lt_UH : (843314856 : ℤ) < UH := Int.not_le.mp h_not_UH_le
            have h_843314856_lt_UH_real : (843314856 : ℝ) < (UH : ℝ) := by exact_mod_cast h_843314856_lt_UH
            have h_843314856_lt_pi : (843314856 : ℝ) < 2 ^ 28 * π := pi_lo_lt

            have h1 : (843314856 : ℝ) / 2 ^ 28 ≤ (UH : ℝ) / 2 ^ 28 := by
              exact (div_le_div_of_nonneg_right (by linarith) hpos')
            have h2 : (843314856 : ℝ) / 2 ^ 28 ≤ π := by
              rw [div_le_iff₀ hpos]

              rw [mul_comm]
              linarith [pi_lo_lt]
            have h_min_div : (843314856 : ℝ) / 2 ^ 28 ≤ min ((UH : ℝ) / 2 ^ 28) π := le_min h1 h2
            rw [div_le_iff₀ hpos] at h_min_div

            rw [mul_comm] at h_min_div
            exact h_min_div
      exact ⟨hHEL_le_mul, hw_mul_UH⟩
    have h_UL_div_le_w : (UL : ℝ) / 2 ^ 28 ≤ w := by
      rw [hw_def, le_min_iff]
      exact ⟨
        (div_le_div_of_nonneg_right hUL_le_UH_real hpos'),
        hULt_div_pi
      ⟩
    refine ⟨w, hEnc_HEL_UH_w, h_UL_div_le_w, ?_, ?_, ?_⟩
    ·
      rw [hw_def]
    ·
      intro _; exact ht_le_w
    ·
      intro h; exact absurd hside h
  ·
    have hLO : LO = UL := by
      rw [hlo, ite_eq_right hside]
    have hHI : HI = LEH := by
      rw [hhi, ite_eq_right hside]
    rw [hLO, hHI]
    set w := (UL : ℝ) / 2 ^ 28 with hw_def
    have hEnc_UL_LEH_w : Enc UL LEH w := by
      rw [Enc, hw_def]
      have hw_mul_LEH : 2 ^ 28 * w ≤ (LEH : ℝ) := by
        rw [hw_def]
        calc
          2 ^ 28 * ((UL : ℝ) / 2 ^ 28) = (UL : ℝ) := by field_simp
          _ ≤ (LEH : ℝ) := by
            rw [hleh]
            by_cases lp1 : lp = 1
            · rw [ite_eq_left lp1]
            · rw [ite_eq_right lp1]
              exact hUL_le_UH_real
      have hUL_le_mul : (UL : ℝ) ≤ 2 ^ 28 * w := by
        rw [hw_def]
        field_simp
        exact le_rfl
      exact ⟨hUL_le_mul, hw_mul_LEH⟩
    have h_UL_div_le_w : (UL : ℝ) / 2 ^ 28 ≤ w := by rw [hw_def]
    have hw_le_min : w ≤ min ((UH : ℝ) / 2 ^ 28) π := by
      rw [hw_def, le_min_iff]
      exact ⟨
        (div_le_div_of_nonneg_right hUL_le_UH_real hpos'),
        hULt_div_pi
      ⟩
    have hw_le_t : w ≤ t := by rw [hw_def]; exact hULt_div
    refine ⟨w, hEnc_UL_LEH_w, h_UL_div_le_w, hw_le_min, ?_, ?_⟩
    · intro h; exact absurd h hside
    · intro _; exact hw_le_t

end D3Prog.L2B
