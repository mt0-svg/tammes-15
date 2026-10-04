import Tammes15.D3Data.Alpha

open Real

namespace Tammes15.D3Data

open Tammes15 Tammes15.D3Kernel Tammes15.D3Kernel.Kinds Tammes15.D3Kernel.Pent Tammes15.D3lp.TrigNat

def alphaRecI (g box it : ℕ) : Bool :=
  let t := fk it 64 127
  let av := fk it 97 63
  let nw := Nat.land it 18446744073709551615
  let al := bk box (2 * av)
  let ah := bk box (2 * av + 1)
  Nat.blt (t / 2) (nvK g) && Nat.blt av (nvK g) && Nat.beq (Ctx.mean g (t / 2)) 1 &&
    Nat.beq (Ctx.mean g av) 0 && kgood nw && kgood al && kgood ah && Nat.blt (4 * kfix nw) cTPL &&
    Nat.ble (2 * kfix al) cTPL && Nat.ble (2 * kfix ah) cTPL &&
    (if t % 2 = 1 then aLo (xA nw) (xA ah) else aHi (xA nw) (xA al))

def alphaRecX (g box it : ℕ) : Bool :=
  @Bool.rec (fun _ => Bool) (alphaRec g box it) (alphaRecI g box it) (Nat.beq (fk it 104 1) 1)

def alphaCheckerX : Checker where
  σ := Bool
  H := Unit
  init := true
  onRec g box it s := s && alphaRecX g box it
  onKill _ _ _ _ := false
  fin s _ := s
  frc s k := @Bool.rec (fun _ => List ℕ) (k false) (k true) s
  frc_eq s k := by cases s <;> rfl

theorem recOK_of_alphaRecI {g box it : ℕ} (h : alphaRecI g box it = true) : RecOK g box it := by
  simp only [alphaRecI, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ho, hav⟩, mo⟩, mav⟩, knew⟩, kal⟩, kah⟩, hnw⟩, hal⟩, hah⟩, hside⟩ := h
  rw [fk_bits7, nvK_eq, Nat.blt_eq] at ho
  rw [fk_bits6, nvK_eq, Nat.blt_eq] at hav
  rw [fk_bits7, Nat.beq_eq] at mo
  rw [fk_bits6, Nat.beq_eq] at mav
  rw [Walk.kf_new] at knew
  rw [Walk.kf_new, Nat.blt_eq] at hnw
  rw [fk_bits6, bk_eq] at kal
  rw [fk_bits6, bk_eq] at kah
  rw [fk_bits6, bk_eq, Nat.ble_eq] at hal
  rw [fk_bits6, bk_eq, Nat.ble_eq] at hah
  rw [fk_bits7, fk_bits6, Walk.kf_new, bk_eq, bk_eq] at hside
  intro S hS
  show BoxMem (Ctx.nv g) (setBnd box (bits it 64 7) (itNew it)) S.x
  set o := bits it 64 7 / 2 with ho'
  set av := bits it 97 6 with hav'
  have hxo : S.x o = S.A.d := val_d S.lab S.A mo
  have hxa : S.x av = alpha S.A.d := by simp [Sol.x, Ctx.val, mav]
  have hdr := d_range S
  have hbd := hS av hav
  rw [hxa, keyVal_kgood kal, keyVal_kgood kah] at hbd
  have hpi := cTPL_le_two_pi
  have hP62 : (0 : ℝ) < 2 ^ 62 := by positivity
  have hpi' := (div_le_iff₀ hP62).mp hpi

  have hr : ∀ k, 2 * kfix k ≤ cTPL → 0 ≤ (kfix k : ℝ) / 2 ^ 62 ∧ (kfix k : ℝ) / 2 ^ 62 ≤ π := by
    intro k hk
    refine ⟨div_nonneg (Nat.cast_nonneg _) hP62.le, ?_⟩
    have h2 : ((2 * kfix k : ℕ) : ℝ) ≤ (cTPL : ℝ) := by exact_mod_cast hk
    push_cast at h2
    rw [div_le_iff₀ hP62]
    linarith

  set b : ℝ := (kfix (itNew it) : ℝ) / 2 ^ 62 with hb'
  have hb : 0 < b ∧ b < π / 2 := by
    refine ⟨div_pos (Nat.cast_pos.mpr (kfix_pos _)) hP62, ?_⟩
    have h4 : ((4 * kfix (itNew it) : ℕ) : ℝ) < (cTPL : ℝ) := by exact_mod_cast hnw
    push_cast at h4
    rw [hb', div_lt_iff₀ hP62]
    linarith
  have hkb : keyVal (itNew it) = b := keyVal_kgood knew
  refine boxMem_set (bits_lt it 0 64) hS (fun h0 => ?_) (fun h1 => ?_)
  ·
    have hs0 : ¬ bits it 64 7 % 2 = 1 := by omega
    simp only [hs0, ↓reduceIte] at hside
    rw [hkb, ← ho', hxo]
    have hab := alpha_le_of_aHi hside hb (hr _ hal) (xA_real _) (xA_real _)
    exact (alpha_strictMonoOn.le_iff_le ⟨hb.1, hb.2⟩ ⟨hdr.1, hdr.2⟩).1 (hab.trans hbd.1)
  ·
    simp only [h1, ↓reduceIte] at hside
    rw [hkb, ← ho', hxo]
    have hab := le_alpha_of_aLo hside hb (hr _ hah) (xA_real _) (xA_real _)
    exact (alpha_strictMonoOn.le_iff_le ⟨hdr.1, hdr.2⟩ ⟨hb.1, hb.2⟩).1 (hbd.2.trans hab)

theorem recOK_of_alphaRecX {g box it : ℕ} (h : alphaRecX g box it = true) : RecOK g box it := by
  unfold alphaRecX at h
  cases hb : Nat.beq (fk it 104 1) 1
  · rw [hb] at h
    exact recOK_of_alphaRec h
  · rw [hb] at h
    exact recOK_of_alphaRecI h

theorem alphaX_fold : ∀ (l : List Ev) (s : Bool),
    l.foldl (fun s e => alphaCheckerX.step e s) s = true → s = true ∧ ∀ e ∈ l, e.OK := by
  intro l
  induction l with
  | nil => exact fun s h => ⟨h, fun e he => by simp at he⟩
  | cons ev l ih =>
    intro s h
    change List.foldl (fun s e => alphaCheckerX.step e s) (alphaCheckerX.step ev s) l = true at h
    obtain ⟨h1, hl⟩ := ih _ h
    cases ev with
    | kill g box it => exact absurd h1 (by change ¬ false = true; simp)
    | record g box it =>
      change (s && alphaRecX g box it) = true at h1
      rw [Bool.and_eq_true] at h1
      refine ⟨h1.1, fun e he => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact recOK_of_alphaRecX h1.2
      · exact hl e he

theorem alphaCheckerX_sound : alphaCheckerX.Sound (kindIs 1) := by
  intro tr _ _ hfin
  exact (alphaX_fold tr alphaCheckerX.init hfin).2

end Tammes15.D3Data
