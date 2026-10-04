import Tammes15.D3Prog.L2B.Base

namespace D3Prog.L2B

open Real Tammes15 D3Ck2Spec D3Prog.L2

set_option linter.unusedVariables false

theorem K24_tri_tail_x (pg pe pf : Bool) (G : Prop) (GaL GaH : ℤ) (guard : ℕ) (E1L E1H F1L F1H E2L E2H F2L F2H : ℤ)
    (one mone : ℤ) (N1L D1L N1 D1 : ℤ) (BAD1 nbad1 : ℕ) (nd1 : ℤ) (lt1 m1 ge1 one1 : ℕ) (y1n y1d : ℤ)
    (N2 D2 N2H D2H : ℤ) (BAD2 nbad2 gt2 m2 : ℕ) (nd2 : ℤ) (le2 mone2 : ℕ) (y2n y2d : ℤ) (er ner : ℕ)
    (LO HI zero pih pil OKL OKH : ℤ) (ERR : ℕ) (EVL EVH : ℤ)
    (hone : one = 268435456) (hmone : mone = -268435456)
    (hh1 : G ∧ guard = 1 → ¬BAD1 = 1 →
      ∀ θg θe θf : ℝ, AF pg GaL GaL θg → AF pe E1L E1H θe → AF pf F1L F1H θf →
        0 < D1L ∧ 0 < D1 ∧ (N1L : ℝ) / D1L ≤ eta θg θe θf ∧ eta θg θe θf ≤ (N1 : ℝ) / D1)
    (hnbad1 : nbad1 = 1 ↔ ¬BAD1 = 1) (hnd1 : nd1 = -D1) (hlt1 : lt1 = 1 ↔ N1 < nd1)
    (hm1 : m1 = 1 ↔ nbad1 = 1 ∧ lt1 = 1) (hge1 : ge1 = 1 ↔ D1 ≤ N1) (hone1 : one1 = 1 ↔ BAD1 = 1 ∨ ge1 = 1)
    (hy1n : y1n = if one1 = 1 then one else N1) (hy1d : y1d = if one1 = 1 then one else D1)
    (hh2 : G ∧ guard = 1 → ¬BAD2 = 1 →
      ∀ θg θe θf : ℝ, AF pg GaH GaH θg → AF pe E2L E2H θe → AF pf F2L F2H θf →
        0 < D2 ∧ 0 < D2H ∧ (N2 : ℝ) / D2 ≤ eta θg θe θf ∧ eta θg θe θf ≤ (N2H : ℝ) / D2H)
    (hnbad2 : nbad2 = 1 ↔ ¬BAD2 = 1) (hgt2 : gt2 = 1 ↔ D2 < N2) (hm2 : m2 = 1 ↔ nbad2 = 1 ∧ gt2 = 1)
    (hnd2 : nd2 = -D2) (hle2 : le2 = 1 ↔ N2 ≤ nd2) (hmone2 : mone2 = 1 ↔ BAD2 = 1 ∨ le2 = 1)
    (hy2n : y2n = if mone2 = 1 then mone else N2) (hy2d : y2d = if mone2 = 1 then one else D2)
    (her : er = 1 ↔ m1 = 1 ∨ m2 = 1) (hner : ner = 1 ↔ ¬er = 1)
    (hlo : 0 < y1d → ∀ y : ℝ, y ≤ (y1n : ℝ) / y1d → -1 ≤ y → (LO : ℝ) / 2 ^ 28 ≤ arccos y)
    (hhi : 0 < y2d → ∀ y : ℝ, (y2n : ℝ) / y2d ≤ y → y ≤ 1 → arccos y ≤ (HI : ℝ) / 2 ^ 28)
    (hzero : zero = 0) (hpih : pih = 843314857) (hpil : pil = 843314856)
    (hokl : OKL = if guard = 1 then LO else zero) (hokh : OKH = if guard = 1 then HI else pih)
    (herr : ERR = 1 ↔ guard = 1 ∧ er = 1) (hevl : EVL = if m1 = 1 then pil else zero)
    (hevh : EVH = if m1 = 1 then pih else zero) :
    G → ∀ y : ℝ,
      (guard = 1 →
        (∃ θg θe θf : ℝ, AF pg GaL GaL θg ∧ AF pe E1L E1H θe ∧ AF pf F1L F1H θf ∧ y ≤ eta θg θe θf) ∧
          ∃ θg θe θf : ℝ, AF pg GaH GaH θg ∧ AF pe E2L E2H θe ∧ AF pf F2L F2H θf ∧ eta θg θe θf ≤ y) →
      (¬ERR = 1 → Enc OKL OKH (arccos y)) ∧ (ERR = 1 → Enc EVL EVH (arccos y)) := by
  intro hG y hpts
  have hS : (0 : ℝ) < 2 ^ 28 := by norm_num
  by_cases hg : guard = 1
  swap
  · have hE : ¬ERR = 1 := fun h => hg (herr.1 h).1
    refine ⟨fun _ => ?_, fun h => absurd h hE⟩
    simp only [hokl, hokh, hg, ↓reduceIte, hzero, hpih]
    exact enc_arccos_top y
  obtain ⟨⟨g1, e1, f1, hg1, he1, hf1, hy1⟩, ⟨g2, e2, f2, hg2, he2, hf2, hy2⟩⟩ := hpts hg
  have hGg : G ∧ guard = 1 := ⟨hG, hg⟩
  have P1 : ¬BAD1 = 1 → 0 < D1 ∧ y ≤ (N1 : ℝ) / D1 := fun hb => by
    obtain ⟨-, hD, -, hup⟩ := hh1 hGg hb g1 e1 f1 hg1 he1 hf1
    exact ⟨hD, hy1.trans hup⟩
  have P2 : ¬BAD2 = 1 → 0 < D2 ∧ (N2 : ℝ) / D2 ≤ y := fun hb => by
    obtain ⟨hD, -, hlo', -⟩ := hh2 hGg hb g2 e2 f2 hg2 he2 hf2
    exact ⟨hD, hlo'.trans hy2⟩
  by_cases hE : ERR = 1
  · refine ⟨fun h => absurd hE h, fun _ => ?_⟩
    have her1 : er = 1 := (herr.1 hE).2
    by_cases hm1' : m1 = 1
    · obtain ⟨hnb, hlt⟩ := hm1.1 hm1'
      obtain ⟨hD, hyN⟩ := P1 (hnbad1.1 hnb)
      have hN : N1 < -D1 := hnd1 ▸ hlt1.1 hlt
      have h1 : (N1 : ℝ) / D1 < -1 := (pair_lt_neg_one N1 D1 hD).1 hN
      have hpi : arccos y = π := Real.arccos_of_le_neg_one (by linarith)
      simp only [hevl, hevh, hm1', ↓reduceIte, hpil, hpih, hpi]
      exact ⟨by have := pi_lo_lt; push_cast; linarith, by have := pi_hi_gt; push_cast; linarith⟩
    · have hm2' : m2 = 1 := (her.1 her1).resolve_left hm1'
      obtain ⟨hnb, hgt⟩ := hm2.1 hm2'
      obtain ⟨hD, hyN⟩ := P2 (hnbad2.1 hnb)
      have hN : D2 < N2 := hgt2.1 hgt
      have hD' : (0 : ℝ) < D2 := by exact_mod_cast hD
      have h1 : 1 < (N2 : ℝ) / D2 := by
        rw [lt_div_iff₀ hD', one_mul]
        exact_mod_cast hN
      have h0 : arccos y = 0 := Real.arccos_of_one_le (by linarith)
      simp only [hevl, hevh, hm1', ↓reduceIte, hzero, h0]
      exact ⟨by norm_num, by norm_num⟩
  · refine ⟨fun _ => ?_, fun h => absurd h hE⟩
    have her0 : ¬er = 1 := fun h => hE (herr.2 ⟨hg, h⟩)
    have hm1n : ¬m1 = 1 := fun h => her0 (her.2 (Or.inl h))
    have hm2n : ¬m2 = 1 := fun h => her0 (her.2 (Or.inr h))
    simp only [hokl, hokh, hg, ↓reduceIte]
    set c := max (-1) (min 1 y) with hc
    have hc1 : -1 ≤ c := le_max_left _ _
    have hc2 : c ≤ 1 := max_le (by norm_num) (min_le_left _ _)
    have hac : arccos y = arccos c := arccos_clamp y
    have hL : (LO : ℝ) / 2 ^ 28 ≤ arccos y := by
      rw [hac]
      by_cases ho : one1 = 1
      · have e1 : y1n = 268435456 := by simp only [hy1n, ho, ↓reduceIte, hone]
        have e2 : y1d = 268435456 := by simp only [hy1d, ho, ↓reduceIte, hone]
        refine hlo (by rw [e2]; norm_num) c ?_ hc1
        rw [e1, e2]
        norm_num
        exact hc2
      · have hb : ¬BAD1 = 1 := fun h => ho (hone1.2 (Or.inl h))
        have e1 : y1n = N1 := by simp only [hy1n, ho, ↓reduceIte]
        have e2 : y1d = D1 := by simp only [hy1d, ho, ↓reduceIte]
        obtain ⟨hD, hyN⟩ := P1 hb
        have hlt : ¬N1 < -D1 := fun h => hm1n (hm1.2 ⟨hnbad1.2 hb, hlt1.2 (hnd1 ▸ h)⟩)
        have hN : -1 ≤ (N1 : ℝ) / D1 := not_lt.1 (fun h => hlt ((pair_lt_neg_one N1 D1 hD).2 h))
        refine hlo (by rw [e2]; exact hD) c ?_ hc1
        rw [e1, e2]
        exact max_le hN ((min_le_right _ _).trans hyN)
    have hH : arccos y ≤ (HI : ℝ) / 2 ^ 28 := by
      rw [hac]
      by_cases ho : mone2 = 1
      · have e1 : y2n = -268435456 := by simp only [hy2n, ho, ↓reduceIte, hmone]
        have e2 : y2d = 268435456 := by simp only [hy2d, ho, ↓reduceIte, hone]
        refine hhi (by rw [e2]; norm_num) c ?_ hc2
        rw [e1, e2]
        norm_num
        exact hc1
      · have hb : ¬BAD2 = 1 := fun h => ho (hmone2.2 (Or.inl h))
        have e1 : y2n = N2 := by simp only [hy2n, ho, ↓reduceIte]
        have e2 : y2d = D2 := by simp only [hy2d, ho, ↓reduceIte]
        obtain ⟨hD, hyN⟩ := P2 hb
        have hD' : (0 : ℝ) < D2 := by exact_mod_cast hD
        have hgt : ¬D2 < N2 := fun h => hm2n (hm2.2 ⟨hnbad2.2 hb, hgt2.2 h⟩)
        have hN : (N2 : ℝ) / D2 ≤ 1 := by
          rw [div_le_one hD']
          exact_mod_cast not_lt.1 hgt
        refine hhi (by rw [e2]; exact hD) c ?_ hc2
        rw [e1, e2]
        exact le_max_of_le_right (le_min hN hyN)
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hS] at hL; linarith
    · rw [le_div_iff₀ hS] at hH; linarith

end D3Prog.L2B
