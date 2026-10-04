import Tammes15.D3Prog.L2B.Base

namespace D3Prog.L2B

open Real Tammes15 D3Ck2Spec D3Prog.L2

set_option linter.unusedVariables false

theorem K31_M0 (hi : Bool) (F0 F1 F2 F3 : ℕ) (hD : InDom F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C : ℤ)
    (side : ℕ) (EL EH B1L B1H FL FH B3L B3H GPL GPH GML GMH BX0L BX0H BX1L BX1H : ℤ) (d0 d1 : ℕ)
    (P0L P0H P1L P1H OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hside : side = 1 ↔ hi = true)
    (he : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EL EH (ebase d u))
    (hb1 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true FL FH (ebase d u))
    (hb3 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc Y0 Y1 u → 0 < u → u < 2 * π →
      Enc B3L B3H (bangle d u))
    (hgp : True → ∀ θg θe θf : ℝ, AF true FL FH θg → AF true EL EH θe → AF false D0 D1 θf →
      Enc GPL GPH (gam θg θe θf))
    (hgm : True → ∀ θg θe θf : ℝ, AF true EL EH θg → AF true FL FH θe → AF false D0 D1 θf →
      Enc GML GMH (gam θg θe θf))
    (hbx0 : ∀ r s : ℝ, Enc B1L B1H r → Enc GPL GPH s → Enc BX0L BX0H (r + s))
    (hbx1 : ∀ r s : ℝ, Enc B3L B3H r → Enc GML GMH s → Enc BX1L BX1H (r + s))
    (hd0 : True → DirOK X0 X1 BX0L BX0H GPL GPH D0 D1 d0)
    (hd1 : True → DirOK Y0 Y1 BX1L BX1H GML GMH D0 D1 d1)
    (hx0 : ∀ t : ℝ, Enc X0 X1 t → t ≤ π → ∃ w : ℝ, Enc P0L P0H w ∧ (X0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((X1 : ℝ) / 2 ^ 28) π ∧ (d0 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d0 = 1 → w = t))
    (hx1 : ∀ t : ℝ, Enc Y0 Y1 t → t ≤ π → ∃ w : ℝ, Enc P1L P1H w ∧ (Y0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((Y1 : ℝ) / 2 ^ 28) π ∧ (d1 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d1 = 1 → w = t))
    (hout : True → ∀ d x y : ℝ, Enc D0 D1 d → Enc P0L P0H x → Enc P1L P1H y → 0 < d → d < π / 2 → 0 < x →
      x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (pentOut 0 d x y))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaim 0 hi F0 F1 F2 F3 := by
  obtain ⟨hdbox, hX0p, hY0p, boxX, boxY⟩ := lane_box hD hD0 hD1 hX0 hX1 hY0 hY1
  unfold LaneClaim
  intro d x y hdl hdh hxl hxh hyl hyh hxpi hypi _
  have hdE : Enc D0 D1 d := enc_fld hD0 hD1 hdl hdh
  have hxE : Enc X0 X1 x := enc_fld hX0 hX1 hxl hxh
  have hyE : Enc Y0 Y1 y := enc_fld hY0 hY1 hyl hyh
  have hd := hdbox d hdE
  obtain ⟨w0, hw0E, hw0l, hw0h, hw0d, hw0n⟩ := hx0 x hxE hxpi.le
  obtain ⟨w1, hw1E, hw1l, hw1h, hw1d, hw1n⟩ := hx1 y hyE hypi.le
  have hw0X : Enc X0 X1 w0 := enc_of_mem hw0l (hw0h.trans (min_le_left _ _))
  have hw1Y : Enc Y0 Y1 w1 := enc_of_mem hw1l (hw1h.trans (min_le_left _ _))
  have hw0pi : w0 ≤ π := hw0h.trans (min_le_right _ _)
  have hw1pi : w1 ≤ π := hw1h.trans (min_le_right _ _)
  have hw0b := boxX w0 hw0X
  have hw1b := boxY w1 hw1Y
  have hxb := boxX x hxE
  have hyb := boxY y hyE
  have hxI : x ∈ Set.Icc ((X0 : ℝ) / 2 ^ 28) (min ((X1 : ℝ) / 2 ^ 28) π) :=
    ⟨(mem_of_enc hxE).1, le_min (mem_of_enc hxE).2 hxpi.le⟩
  have hyI : y ∈ Set.Icc ((Y0 : ℝ) / 2 ^ 28) (min ((Y1 : ℝ) / 2 ^ 28) π) :=
    ⟨(mem_of_enc hyE).1, le_min (mem_of_enc hyE).2 hypi.le⟩
  have hw0I : w0 ∈ Set.Icc ((X0 : ℝ) / 2 ^ 28) (min ((X1 : ℝ) / 2 ^ 28) π) := ⟨hw0l, hw0h⟩
  have hw1I : w1 ∈ Set.Icc ((Y0 : ℝ) / 2 ^ 28) (min ((Y1 : ℝ) / 2 ^ 28) π) := ⟨hw1l, hw1h⟩
  have hp0 : (0 : ℝ) < (X0 : ℝ) / 2 ^ 28 := by positivity
  have hp1 : (0 : ℝ) < (Y0 : ℝ) / 2 ^ 28 := by positivity
  have hc := claim_of_check hi side C OL OH lo_ok hi_ok cl hside hlo_ok hhi_ok hcl hck _
    (hout trivial d w0 w1 hdE hw0E hw1E hd.1 hd.2 hw0b.1 hw0b.2 hw1b.1 hw1b.2)
  rw [div_fld hC] at hc
  have stepX : (side = 1 → pentOut 0 d x y ≤ pentOut 0 d w0 y) ∧
      (¬side = 1 → pentOut 0 d w0 y ≤ pentOut 0 d x y) := by
    by_cases h1 : d0 = 1
    · have hanti := pentOut0_antitoneOn_x (y := y) (p := (X0 : ℝ) / 2 ^ 28) (q := min ((X1 : ℝ) / 2 ^ 28) π)
        hd ⟨hyb.1, hypi.le⟩ hp0 (min_le_right _ _)
        (fun u hu _ _ => fan_sign_of_dir (hd0 trivial) h1 hdE hd.1 hd.2 hX0p
          (fun u => eta (ebase d y) (ebase d u) d)
          (fun u hu =>
            have hg := hgp trivial (ebase d y) (ebase d u) d (hf trivial d y hdE hyE) (he trivial d u hdE hu)
              (af_false hdE)
            ⟨hg, hbx0 _ _ (hb1 trivial d u hd.1 hd.2 hdE hu (boxX u hu).1 (boxX u hu).2) hg⟩) u hu)
      obtain ⟨hs1, hs0⟩ := hw0d h1
      exact ⟨fun hs => hanti hw0I hxI (hs1 hs), fun hs => hanti hxI hw0I (hs0 hs)⟩
    · rw [hw0n h1]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  have stepY : (side = 1 → pentOut 0 d w0 y ≤ pentOut 0 d w0 w1) ∧
      (¬side = 1 → pentOut 0 d w0 w1 ≤ pentOut 0 d w0 y) := by
    by_cases h1 : d1 = 1
    · have hanti := pentOut0_antitoneOn_y (x := w0) (p := (Y0 : ℝ) / 2 ^ 28) (q := min ((Y1 : ℝ) / 2 ^ 28) π)
        hd ⟨hw0b.1, hw0pi⟩ hp1 (min_le_right _ _)
        (fun u hu _ _ => fan_sign_of_dir (hd1 trivial) h1 hdE hd.1 hd.2 hY0p
          (fun u => eta (ebase d w0) (ebase d u) d)
          (fun u hu =>
            have hg := hgm trivial (ebase d w0) (ebase d u) d (he trivial d w0 hdE hw0X) (hf trivial d u hdE hu)
              (af_false hdE)
            ⟨hg, hbx1 _ _ (hb3 trivial d u hd.1 hd.2 hdE hu (boxY u hu).1 (boxY u hu).2) hg⟩) u hu)
      obtain ⟨hs1, hs0⟩ := hw1d h1
      exact ⟨fun hs => hanti hw1I hyI (hs1 hs), fun hs => hanti hyI hw1I (hs0 hs)⟩
    · rw [hw1n h1]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  unfold Claim at hc ⊢
  cases hi with
  | false =>
    have hs : ¬side = 1 := fun h => Bool.false_ne_true (hside.1 h)
    simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    linarith [stepX.2 hs, stepY.2 hs]
  | true =>
    have hs : side = 1 := hside.2 rfl
    simp only [↓reduceIte] at hc ⊢
    linarith [stepX.1 hs, stepY.1 hs]

theorem K31_M1 (hi : Bool) (F0 F1 F2 F3 : ℕ) (hD : InDom F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C : ℤ)
    (side : ℕ) (EL EH B1L B1H FL FH GIL GIH BX0L BX0H : ℤ) (d0 : ℕ) (P0L P0H P1L P1H OL OH : ℤ)
    (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hside : side = 1 ↔ hi = true)
    (he : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EL EH (ebase d u))
    (hb1 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true FL FH (ebase d u))
    (hgi : True → ∀ θg θe θf : ℝ, AF false D0 D1 θg → AF true EL EH θe → AF true FL FH θf →
      Enc GIL GIH (gam θg θe θf))
    (hbx0 : ∀ r s : ℝ, Enc B1L B1H r → Enc GIL GIH s → Enc BX0L BX0H (r + s))
    (hd0 : True → DirOK X0 X1 BX0L BX0H GIL GIH D0 D1 d0)
    (hx0 : ∀ t : ℝ, Enc X0 X1 t → t ≤ π → ∃ w : ℝ, Enc P0L P0H w ∧ (X0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((X1 : ℝ) / 2 ^ 28) π ∧ (d0 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d0 = 1 → w = t))
    (hx1 : ∀ t : ℝ, Enc Y0 Y1 t → t ≤ π → ∃ w : ℝ, Enc P1L P1H w ∧ (Y0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((Y1 : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t))
    (hout : True → ∀ d x y : ℝ, Enc D0 D1 d → Enc P0L P0H x → Enc P1L P1H y → 0 < d → d < π / 2 → 0 < x →
      x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (pentOut 1 d x y))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaim 1 hi F0 F1 F2 F3 := by
  obtain ⟨hdbox, hX0p, hY0p, boxX, boxY⟩ := lane_box hD hD0 hD1 hX0 hX1 hY0 hY1
  unfold LaneClaim
  intro d x y hdl hdh hxl hxh hyl hyh hxpi hypi _
  have hdE : Enc D0 D1 d := enc_fld hD0 hD1 hdl hdh
  have hxE : Enc X0 X1 x := enc_fld hX0 hX1 hxl hxh
  have hyE : Enc Y0 Y1 y := enc_fld hY0 hY1 hyl hyh
  have hd := hdbox d hdE
  obtain ⟨w0, hw0E, hw0l, hw0h, hw0d, hw0n⟩ := hx0 x hxE hxpi.le
  obtain ⟨w1, hw1E, hw1l, hw1h, hw1s, hw1n⟩ := hx1 y hyE hypi.le
  have hw0X : Enc X0 X1 w0 := enc_of_mem hw0l (hw0h.trans (min_le_left _ _))
  have hw1Y : Enc Y0 Y1 w1 := enc_of_mem hw1l (hw1h.trans (min_le_left _ _))
  have hw0pi : w0 ≤ π := hw0h.trans (min_le_right _ _)
  have hw1pi : w1 ≤ π := hw1h.trans (min_le_right _ _)
  have hw0b := boxX w0 hw0X
  have hw1b := boxY w1 hw1Y
  have hxb := boxX x hxE
  have hyb := boxY y hyE
  have hxI : x ∈ Set.Icc ((X0 : ℝ) / 2 ^ 28) (min ((X1 : ℝ) / 2 ^ 28) π) :=
    ⟨(mem_of_enc hxE).1, le_min (mem_of_enc hxE).2 hxpi.le⟩
  have hw0I : w0 ∈ Set.Icc ((X0 : ℝ) / 2 ^ 28) (min ((X1 : ℝ) / 2 ^ 28) π) := ⟨hw0l, hw0h⟩
  have hp0 : (0 : ℝ) < (X0 : ℝ) / 2 ^ 28 := by positivity
  have hc := claim_of_check hi side C OL OH lo_ok hi_ok cl hside hlo_ok hhi_ok hcl hck _
    (hout trivial d w0 w1 hdE hw0E hw1E hd.1 hd.2 hw0b.1 hw0b.2 hw1b.1 hw1b.2)
  rw [div_fld hC] at hc
  have stepX : (side = 1 → pentOut 1 d x w1 ≤ pentOut 1 d w0 w1) ∧
      (¬side = 1 → pentOut 1 d w0 w1 ≤ pentOut 1 d x w1) := by
    by_cases h1 : d0 = 1
    · have hanti := pentOut1_antitoneOn_x (y := w1) (p := (X0 : ℝ) / 2 ^ 28) (q := min ((X1 : ℝ) / 2 ^ 28) π)
        hd ⟨hw1b.1, hw1pi⟩ hp0 (min_le_right _ _)
        (fun u hu _ _ => fan_sign_of_dir (hd0 trivial) h1 hdE hd.1 hd.2 hX0p
          (fun u => eta d (ebase d u) (ebase d w1))
          (fun u hu =>
            have hg := hgi trivial d (ebase d u) (ebase d w1) (af_false hdE) (he trivial d u hdE hu)
              (hf trivial d w1 hdE hw1Y)
            ⟨hg, hbx0 _ _ (hb1 trivial d u hd.1 hd.2 hdE hu (boxX u hu).1 (boxX u hu).2) hg⟩) u hu)
      obtain ⟨hs1, hs0⟩ := hw0d h1
      exact ⟨fun hs => hanti hw0I hxI (hs1 hs), fun hs => hanti hxI hw0I (hs0 hs)⟩
    · rw [hw0n h1]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  have stepY : (side = 1 → pentOut 1 d x y ≤ pentOut 1 d x w1) ∧
      (¬side = 1 → pentOut 1 d x w1 ≤ pentOut 1 d x y) :=
    ⟨fun hs => pentOut1_mono_y hd ⟨hxb.1, hxpi.le⟩ hyb.1 (hw1s hs) hw1pi,
      fun hs => pentOut1_mono_y hd ⟨hxb.1, hxpi.le⟩ hw1b.1 (hw1n hs) hypi.le⟩
  unfold Claim at hc ⊢
  cases hi with
  | false =>
    have hs : ¬side = 1 := fun h => Bool.false_ne_true (hside.1 h)
    simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    linarith [stepX.2 hs, stepY.2 hs]
  | true =>
    have hs : side = 1 := hside.2 rfl
    simp only [↓reduceIte] at hc ⊢
    linarith [stepX.1 hs, stepY.1 hs]

end D3Prog.L2B
