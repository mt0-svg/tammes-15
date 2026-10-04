import Tammes15.D3Prog.L2B.Base

namespace D3Prog.L2B

open Real Tammes15 D3Ck2Spec D3Prog.L2

set_option linter.unusedVariables false

theorem dec_dir_early (UL UH BXL BXH XL XH : ℤ) (hb : BXH < 843314857) (d : ℝ) (Y : ℝ → ℝ) (hd0 : 0 < d)
    (hd1 : d < π / 2) (hUL : (0 : ℝ) < UL)
    (hY : ∀ u : ℝ, Enc UL UH u → 0 < Y u → Y u < π → Enc XL XH (Y u) ∧ Enc BXL BXH (bangle d u + Y u)) :
    ∀ u ∈ Set.Icc ((UL : ℝ) / 2 ^ 28) (min ((UH : ℝ) / 2 ^ 28) π), 0 < Y u → Y u < π →
      0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
  have hS : (0 : ℝ) < 2 ^ 28 := by norm_num
  have hbx : (BXH : ℝ) / 2 ^ 28 ≤ π := by
    have h1 : (BXH : ℝ) ≤ 843314856 := by exact_mod_cast (by omega : BXH ≤ 843314856)
    have := pi_lo_lt
    rw [div_le_iff₀ hS]
    linarith
  exact decDirX_early Y (lo := (UL : ℝ) / 2 ^ 28) (hi := (UH : ℝ) / 2 ^ 28) (by positivity) ⟨hd0, hd1⟩
    ((BXH : ℝ) / 2 ^ 28)
    (fun u' hu' h0 h1 => (mem_of_enc ((hY u' (enc_of_mem hu'.1 (hu'.2.trans (min_le_left _ _))) h0 h1).2)).2) hbx

theorem dec_dir_test (full : Bool) (T1L T1H CXL CXH SXL SXH DLq DHq CHL CHH : ℤ) (d u y : ℝ)
    (hfull : full = true ∨ ¬(CXL < 0 ∧ 0 < CXH ∧ CHL < 0 ∧ 0 < CHH))
    (htest : decTestX full T1L CXL DLq CXH DHq CHL CHH = true)
    (ht1 : Enc T1L T1H (cos d * sin (u / 2))) (hcx : Enc CXL CXH (cos y)) (hsx : Enc SXL SXH (sin y))
    (hq : ∀ r s : ℝ, Enc CXL CXH r → Enc SXL SXH s →
        0 < s ∧ 0 < DLq ∧ 0 < DHq ∧ (CXL : ℝ) / DLq ≤ r / s ∧ r / s ≤ (CXH : ℝ) / DHq)
    (hch : Enc CHL CHH (cos (u / 2))) :
    0 ≤ cos d * sin (u / 2) + cot y * cos (u / 2) := by
  obtain ⟨-, hDL, hDH, hq1, hq2⟩ := hq _ _ hcx hsx
  have hcot : (CXL : ℝ) / DLq ≤ cot y ∧ cot y ≤ (CXH : ℝ) / DHq := by
    rw [Real.cot_eq_cos_div_sin]
    exact ⟨hq1, hq2⟩
  have key := decTestX_sound full T1L CXL DLq CXH DHq CHL CHH hDL hDH hfull htest (2 ^ 28 * (cos d * sin (u / 2)))
    (cot y) (2 ^ 28 * cos (u / 2)) ht1.1 hcot ⟨hch.1, hch.2⟩
  have h2 : 2 ^ 28 * (cos d * sin (u / 2)) + cot y * (2 ^ 28 * cos (u / 2)) =
      2 ^ 28 * (cos d * sin (u / 2) + cot y * cos (u / 2)) := by ring
  rw [h2] at key
  exact (pos_of_mul_pos_right key (by positivity)).le

theorem K26_dec_dir_x (G : Prop) (UL UH BXL BXH XL XH DL DH : ℤ) (a b early ne : ℕ)
    (HL HH CDL CDH SHL SHH T1L T1H CXL CXH SXL SXH DLq DHq : ℤ) (bad nb : ℕ) (CHL CHH z : ℤ)
    (al pa ah na0 na za bl pb bh nb0 nbg zb both nboth t m : ℕ) (xn xd : ℤ) (t' m' : ℕ) (ylo k l r : ℤ)
    (r1 r' OUT : ℕ)
    (ha : a = 1 ↔ UH < 843314857) (hb : b = 1 ↔ BXH < 843314857) (hearly : early = 1 ↔ a = 1 ∧ b = 1)
    (hne : ne = 1 ↔ ¬early = 1) (hh : ∀ r : ℝ, Enc UL UH r → Enc HL HH (r / 2))
    (hcd : G ∧ ne = 1 → (0 ≤ DL ∧ DH ≤ 843314857) ∧ ∀ r : ℝ, Enc DL DH r → Enc CDL CDH (cos r))
    (hsh : G ∧ ne = 1 → (0 ≤ HL ∧ HH ≤ 843314857) ∧ ∀ r : ℝ, Enc HL HH r → Enc SHL SHH (sin r))
    (ht1 : G ∧ ne = 1 → ∀ r s : ℝ, Enc CDL CDH r → Enc SHL SHH s → Enc T1L T1H (r * s))
    (hcx : G ∧ ne = 1 → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc CXL CXH (cos r))
    (hsx : G ∧ ne = 1 → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc SXL SXH (sin r))
    (hq : ¬bad = 1 → ∀ r s : ℝ, Enc CXL CXH r → Enc SXL SXH s →
        0 < s ∧ 0 < DLq ∧ 0 < DHq ∧ (CXL : ℝ) / DLq ≤ r / s ∧ r / s ≤ (CXH : ℝ) / DHq)
    (hnb : nb = 1 ↔ ¬bad = 1)
    (hch : (G ∧ ne = 1) ∧ nb = 1 → (0 ≤ HL ∧ HH ≤ 843314857) ∧
      ∀ r : ℝ, Enc HL HH r → Enc CHL CHH (cos r))
    (hz : z = 0) (hal : al = 1 ↔ CXL < z) (hpa : pa = 1 ↔ ¬al = 1) (hah : ah = 1 ↔ z < CXH)
    (hna0 : na0 = 1 ↔ ¬ah = 1) (hna : na = 1 ↔ na0 = 1 ∧ al = 1) (hza : za = 1 ↔ al = 1 ∧ ah = 1)
    (hbl : bl = 1 ↔ CHL < z) (hpb : pb = 1 ↔ ¬bl = 1) (hbh : bh = 1 ↔ z < CHH) (hnb0 : nb0 = 1 ↔ ¬bh = 1)
    (hnbg : nbg = 1 ↔ nb0 = 1 ∧ bl = 1) (hzb : zb = 1 ↔ bl = 1 ∧ bh = 1) (hboth : both = 1 ↔ za = 1 ∧ zb = 1)
    (hnboth : nboth = 1 ↔ ¬both = 1) (hck : (G ∧ ne = 1) ∧ nb = 1 → nboth = 1)
    (ht : t = 1 ↔ pa = 1 ∧ zb = 1) (hm : m = 1 ↔ nbg = 1 ∨ t = 1) (hxn : xn = if m = 1 then CXH else CXL)
    (hxd : xd = if m = 1 then DHq else DLq) (ht' : t' = 1 ↔ za = 1 ∧ pb = 1) (hm' : m' = 1 ↔ na = 1 ∨ t' = 1)
    (hylo : ylo = if m' = 1 then CHH else CHL) (hk : k = -T1L) (hl : l = k * xd) (hr : r = xn * ylo)
    (hr1 : r1 = 1 ↔ l < r) (hr' : r' = 1 ↔ r1 = 1 ∧ nb = 1) (hout : OUT = 1 ↔ early = 1 ∨ r' = 1) :
    G → OUT = 1 → ∀ (d : ℝ) (Y : ℝ → ℝ), Enc DL DH d → 0 < d → d < π / 2 → (0 : ℝ) < UL →
      (∀ u : ℝ, Enc UL UH u → 0 < Y u → Y u < π → Enc XL XH (Y u) ∧ Enc BXL BXH (bangle d u + Y u)) →
      ∀ u ∈ Set.Icc ((UL : ℝ) / 2 ^ 28) (min ((UH : ℝ) / 2 ^ 28) π), 0 < Y u → Y u < π →
        0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
  intro hG hOUT d Y hd hd0 hd1 hUL hY u hu hY0 hY1
  subst hz
  by_cases he : early = 1
  · exact dec_dir_early UL UH BXL BXH XL XH (hb.1 (hearly.1 he).2) d Y hd0 hd1 hUL hY u hu hY0 hY1
  have hR : r' = 1 := (hout.1 hOUT).resolve_left he
  obtain ⟨hr1', hnb1⟩ := hr'.1 hR
  have G' : G ∧ ne = 1 := ⟨hG, hne.2 he⟩
  have huE : Enc UL UH u := enc_of_mem hu.1 (hu.2.trans (min_le_left _ _))
  have hYE := (hY u huE hY0 hY1).1
  have hhE := hh u huE
  have hfull : false = true ∨ ¬(CXL < 0 ∧ 0 < CXH ∧ CHL < 0 ∧ 0 < CHH) := by
    right
    rintro ⟨h1, h2, h3, h4⟩
    exact hnboth.1 (hck ⟨G', hnb1⟩) (hboth.2 ⟨hza.2 ⟨hal.2 h1, hah.2 h2⟩, hzb.2 ⟨hbl.2 h3, hbh.2 h4⟩⟩)
  have htest : decTestX false T1L CXL DLq CXH DHq CHL CHH = true := by
    have hlr := hr1.1 hr1'
    rw [hl, hr, hk] at hlr
    simp only [hm, hnbg, ht, hnb0, hbh, hbl, hpa, hal, hzb] at hxn hxd
    simp only [hm', hna, ht', hna0, hah, hal, hza, hpb, hbl] at hylo
    rw [hxn, hxd, hylo] at hlr
    unfold decTestX
    by_cases p1 : CXL < 0 <;> by_cases p2 : 0 < CXH <;> by_cases p3 : CHL < 0 <;> by_cases p4 : 0 < CHH <;>
      simpa [p1, p2, p3, p4] using hlr
  exact dec_dir_test false T1L T1H CXL CXH SXL SXH DLq DHq CHL CHH d u (Y u) hfull htest
    (ht1 G' _ _ ((hcd G').2 d hd) ((hsh G').2 _ hhE)) ((hcx G').2 _ hYE) ((hsx G').2 _ hYE) (hq (hnb.1 hnb1))
    ((hch ⟨G', hnb1⟩).2 _ hhE)

theorem K26_dec_dir_x_full (G : Prop) (UL UH BXL BXH XL XH DL DH : ℤ) (a b early ne : ℕ)
    (HL HH CDL CDH SHL SHH T1L T1H CXL CXH SXL SXH DLq DHq : ℤ) (bad nb : ℕ) (CHL CHH z : ℤ)
    (al pa ah na0 na za bl pb bh nb0 nbg zb both t m : ℕ) (xn xd : ℤ) (nnb t' m' : ℕ) (ylo k l r : ℤ) (r1 : ℕ)
    (l2 r2 : ℤ) (t2 nbo c2 rr r' OUT : ℕ)
    (ha : a = 1 ↔ UH < 843314857) (hb : b = 1 ↔ BXH < 843314857) (hearly : early = 1 ↔ a = 1 ∧ b = 1)
    (hne : ne = 1 ↔ ¬early = 1) (hh : ∀ r : ℝ, Enc UL UH r → Enc HL HH (r / 2))
    (hcd : G ∧ ne = 1 → (0 ≤ DL ∧ DH ≤ 843314857) ∧ ∀ r : ℝ, Enc DL DH r → Enc CDL CDH (cos r))
    (hsh : G ∧ ne = 1 → (0 ≤ HL ∧ HH ≤ 843314857) ∧ ∀ r : ℝ, Enc HL HH r → Enc SHL SHH (sin r))
    (ht1 : G ∧ ne = 1 → ∀ r s : ℝ, Enc CDL CDH r → Enc SHL SHH s → Enc T1L T1H (r * s))
    (hcx : G ∧ ne = 1 → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc CXL CXH (cos r))
    (hsx : G ∧ ne = 1 → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc SXL SXH (sin r))
    (hq : ¬bad = 1 → ∀ r s : ℝ, Enc CXL CXH r → Enc SXL SXH s →
        0 < s ∧ 0 < DLq ∧ 0 < DHq ∧ (CXL : ℝ) / DLq ≤ r / s ∧ r / s ≤ (CXH : ℝ) / DHq)
    (hnb : nb = 1 ↔ ¬bad = 1)
    (hch : (G ∧ ne = 1) ∧ nb = 1 → (0 ≤ HL ∧ HH ≤ 843314857) ∧
      ∀ r : ℝ, Enc HL HH r → Enc CHL CHH (cos r))
    (hz : z = 0) (hal : al = 1 ↔ CXL < z) (hpa : pa = 1 ↔ ¬al = 1) (hah : ah = 1 ↔ z < CXH)
    (hna0 : na0 = 1 ↔ ¬ah = 1) (hna : na = 1 ↔ na0 = 1 ∧ al = 1) (hza : za = 1 ↔ al = 1 ∧ ah = 1)
    (hbl : bl = 1 ↔ CHL < z) (hpb : pb = 1 ↔ ¬bl = 1) (hbh : bh = 1 ↔ z < CHH) (hnb0 : nb0 = 1 ↔ ¬bh = 1)
    (hnbg : nbg = 1 ↔ nb0 = 1 ∧ bl = 1) (hzb : zb = 1 ↔ bl = 1 ∧ bh = 1) (hboth : both = 1 ↔ za = 1 ∧ zb = 1)
    (ht : t = 1 ↔ pa = 1 ∧ zb = 1) (hm : m = 1 ↔ nbg = 1 ∨ t = 1) (hxn : xn = if m = 1 then CXH else CXL)
    (hxd : xd = if m = 1 then DHq else DLq) (hnnb : nnb = 1 ↔ ¬nbg = 1) (ht' : t' = 1 ↔ za = 1 ∧ nnb = 1)
    (hm' : m' = 1 ↔ na = 1 ∨ t' = 1) (hylo : ylo = if m' = 1 then CHH else CHL) (hk : k = -T1L)
    (hl : l = k * xd) (hr : r = xn * ylo) (hr1 : r1 = 1 ↔ l < r) (hl2 : l2 = k * DHq) (hr2 : r2 = CXH * CHL)
    (ht2 : t2 = 1 ↔ l2 < r2) (hnbo : nbo = 1 ↔ ¬both = 1) (hc2 : c2 = 1 ↔ nbo = 1 ∨ t2 = 1)
    (hrr : rr = 1 ↔ r1 = 1 ∧ c2 = 1) (hr' : r' = 1 ↔ rr = 1 ∧ nb = 1) (hout : OUT = 1 ↔ early = 1 ∨ r' = 1) :
    G → OUT = 1 → ∀ (d : ℝ) (Y : ℝ → ℝ), Enc DL DH d → 0 < d → d < π / 2 → (0 : ℝ) < UL →
      (∀ u : ℝ, Enc UL UH u → 0 < Y u → Y u < π → Enc XL XH (Y u) ∧ Enc BXL BXH (bangle d u + Y u)) →
      ∀ u ∈ Set.Icc ((UL : ℝ) / 2 ^ 28) (min ((UH : ℝ) / 2 ^ 28) π), 0 < Y u → Y u < π →
        0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
  intro hG hOUT d Y hd hd0 hd1 hUL hY u hu hY0 hY1
  subst hz
  by_cases he : early = 1
  · exact dec_dir_early UL UH BXL BXH XL XH (hb.1 (hearly.1 he).2) d Y hd0 hd1 hUL hY u hu hY0 hY1
  have hR : r' = 1 := (hout.1 hOUT).resolve_left he
  obtain ⟨hrr1, hnb1⟩ := hr'.1 hR
  obtain ⟨hr1', hc21⟩ := hrr.1 hrr1
  have G' : G ∧ ne = 1 := ⟨hG, hne.2 he⟩
  have huE : Enc UL UH u := enc_of_mem hu.1 (hu.2.trans (min_le_left _ _))
  have hYE := (hY u huE hY0 hY1).1
  have hhE := hh u huE
  have htest : decTestX true T1L CXL DLq CXH DHq CHL CHH = true := by
    have hlr := hr1.1 hr1'
    rw [hl, hr, hk] at hlr
    simp only [hm, hnbg, ht, hnb0, hbh, hbl, hpa, hal, hzb] at hxn hxd
    simp only [hm', hna, ht', hnnb, hnbg, hnb0, hbh, hah, hal, hza, hbl] at hylo
    rw [hxn, hxd, hylo] at hlr
    have hc2 := hc2.1 hc21
    rw [hnbo, hboth, hza, hzb, hal, hah, hbl, hbh, ht2, hl2, hr2, hk] at hc2
    unfold decTestX
    by_cases p1 : CXL < 0 <;> by_cases p2 : 0 < CXH <;> by_cases p3 : CHL < 0 <;> by_cases p4 : 0 < CHH <;>
      simp [p1, p2, p3, p4] at hlr hc2 ⊢ <;> simp_all
  exact dec_dir_test true T1L T1H CXL CXH SXL SXH DLq DHq CHL CHH d u (Y u) (Or.inl rfl) htest
    (ht1 G' _ _ ((hcd G').2 d hd) ((hsh G').2 _ hhE)) ((hcx G').2 _ hYE) ((hsx G').2 _ hYE) (hq (hnb.1 hnb1))
    ((hch ⟨G', hnb1⟩).2 _ hhE)

end D3Prog.L2B
