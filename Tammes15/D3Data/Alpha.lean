import Tammes15.D3Kernel.Kinds.LinSound
import Tammes15.D3lp.TrigNat
import Tammes15.Trigrows.Mono

open Real

namespace Tammes15.D3Data

open Tammes15 Tammes15.D3Kernel Tammes15.D3Kernel.Kinds Tammes15.D3Kernel.Pent Tammes15.D3lp.TrigNat

def sA : ℕ := 8

def bA : ℕ := 62 + sA

def nA : ℕ := 13

def cF : ℕ := (2 * nA).factorial * 2 ^ (bA * (2 * nA))

def xA (k : ℕ) : ℕ := kfix k * 2 ^ sA

def cosLo (x : ℕ) : ℕ :=
  (cosSum bA nA x 0 nA - (cosSum bA nA x 1 nA + x ^ (2 * nA) * 2 ^ bA)) / cF

def cosHi (x : ℕ) : ℕ :=
  (cosSum bA nA x 0 nA + x ^ (2 * nA) * 2 ^ bA - cosSum bA nA x 1 nA) / cF + 1

def aLo (xd xc : ℕ) : Bool :=
  Nat.ble (cosHi xd * 2 ^ bA) (cosLo xc * (2 ^ bA + cosHi xd))

def aHi (xd xc : ℕ) : Bool :=
  Nat.ble (cosHi xc * (2 ^ bA + cosLo xd)) (cosLo xd * 2 ^ bA)

def alphaRec (g box it : ℕ) : Bool :=
  let t := fk it 64 127
  let dv := fk it 97 63
  let nw := Nat.land it 18446744073709551615
  let dl := bk box (2 * dv)
  let dh := bk box (2 * dv + 1)
  Nat.blt (t / 2) (nvK g) && Nat.blt dv (nvK g) && Nat.beq (Ctx.mean g (t / 2)) 0 &&
    Nat.beq (Ctx.mean g dv) 1 && kgood nw && kgood dl && kgood dh && Nat.blt (4 * kfix dh) cTPL &&
    Nat.ble (2 * kfix nw) cTPL &&
    (if t % 2 = 1 then aHi (xA dh) (xA nw) else aLo (xA dl) (xA nw))

def alphaChecker : Checker where
  σ := Bool
  H := Unit
  init := true
  onRec g box it s := s && alphaRec g box it
  onKill _ _ _ _ := false
  fin s _ := s
  frc s k := @Bool.rec (fun _ => List ℕ) (k false) (k true) s
  frc_eq s k := by cases s <;> rfl

theorem cosHi_pos (x : ℕ) : 0 < cosHi x := Nat.succ_pos _

theorem cosGe_cosLo {x : ℕ} (h : 0 < cosLo x) : cosGe bA nA x (cosLo x) = true := by
  unfold cosGe
  rw [Nat.ble_eq]
  unfold cosLo at h ⊢
  set A := cosSum bA nA x 0 nA
  set B := cosSum bA nA x 1 nA + x ^ (2 * nA) * 2 ^ bA
  have hF : 0 < cF := by unfold cF; positivity
  have hB : B ≤ A := by
    by_contra hc
    rw [Nat.sub_eq_zero_of_le (by omega), Nat.zero_div] at h
    exact absurd h (lt_irrefl 0)
  have hm : (A - B) / cF * cF ≤ A - B := Nat.div_mul_le_self _ _
  have he : (A - B) / cF * (2 * nA).factorial * 2 ^ (bA * (2 * nA)) = (A - B) / cF * cF := by
    unfold cF; rw [Nat.mul_assoc]
  rw [he]
  omega

theorem cosLe_cosHi (x : ℕ) : cosLe bA nA x (cosHi x) = true := by
  unfold cosLe
  rw [Nat.ble_eq]
  unfold cosHi
  set A := cosSum bA nA x 0 nA + x ^ (2 * nA) * 2 ^ bA
  set B := cosSum bA nA x 1 nA
  have hF : 0 < cF := by unfold cF; positivity
  have hm : A - B < ((A - B) / cF + 1) * cF := by
    have := Nat.lt_div_mul_add (a := A - B) hF
    rw [add_mul, one_mul]
    exact this
  have he : ((A - B) / cF + 1) * (2 * nA).factorial * 2 ^ (bA * (2 * nA)) = ((A - B) / cF + 1) * cF := by
    unfold cF; rw [Nat.mul_assoc]
  rw [he]
  omega

theorem cosLo_le {x : ℕ} (h : 0 < cosLo x) : (cosLo x : ℝ) / 2 ^ bA ≤ cos ((x : ℝ) / 2 ^ bA) :=
  cosGe_sound (cosGe_cosLo h)

theorem le_cosHi (x : ℕ) : cos ((x : ℝ) / 2 ^ bA) ≤ (cosHi x : ℝ) / 2 ^ bA :=
  cosLe_sound (cosLe_cosHi x)

theorem xA_real (k : ℕ) : (xA k : ℝ) / 2 ^ bA = (kfix k : ℝ) / 2 ^ 62 := by
  unfold xA
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, show bA = 62 + sA from rfl, pow_add]
  have : (0 : ℝ) < 2 ^ sA := by positivity
  exact mul_div_mul_right _ _ (ne_of_gt this)

theorem le_alpha_of {d a u l : ℝ} (hd : 0 < d ∧ d < π / 2) (ha : 0 ≤ a ∧ a ≤ π)
    (hu : cos d ≤ u) (hl : l ≤ cos a) (hul : u ≤ l * (1 + u)) : a ≤ alpha d := by
  have hc : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith, hd.2⟩
  have hu0 : 0 < u := lt_of_lt_of_le hc hu
  have h1 : cos d / (1 + cos d) ≤ u / (1 + u) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : u / (1 + u) ≤ l := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h3 : cos d / (1 + cos d) ≤ cos a := h1.trans (h2.trans hl)
  unfold alpha
  calc a = arccos (cos a) := (arccos_cos ha.1 ha.2).symm
    _ ≤ arccos (cos d / (1 + cos d)) := arccos_le_arccos h3

theorem alpha_le_of {d a u l : ℝ} (hd : 0 < d ∧ d < π / 2) (ha : 0 ≤ a ∧ a ≤ π)
    (hl : l ≤ cos d) (hl0 : 0 ≤ l) (hu : cos a ≤ u) (hul : u * (1 + l) ≤ l) : alpha d ≤ a := by
  have hc : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith, hd.2⟩
  have h1 : l / (1 + l) ≤ cos d / (1 + cos d) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : u ≤ l / (1 + l) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h3 : cos a ≤ cos d / (1 + cos d) := hu.trans (h2.trans h1)
  unfold alpha
  calc arccos (cos d / (1 + cos d)) ≤ arccos (cos a) := arccos_le_arccos h3
    _ = a := arccos_cos ha.1 ha.2

theorem alpha_mono {x y : ℝ} (hx : 0 < x) (hy : y < π / 2) (hxy : x ≤ y) : alpha x ≤ alpha y :=
  alpha_strictMonoOn.monotoneOn ⟨hx, by linarith⟩ ⟨by linarith, hy⟩ hxy

theorem le_alpha_of_aLo {d a : ℝ} {xd xc : ℕ} (h : aLo xd xc = true) (hd : 0 < d ∧ d < π / 2)
    (ha : 0 ≤ a ∧ a ≤ π) (hxd : (xd : ℝ) / 2 ^ bA = d) (hxc : (xc : ℝ) / 2 ^ bA = a) : a ≤ alpha d := by
  unfold aLo at h
  rw [Nat.ble_eq] at h
  have hU := cosHi_pos xd
  have hL : 0 < cosLo xc := by
    rcases Nat.eq_zero_or_pos (cosLo xc) with h0 | h0
    · rw [h0, zero_mul] at h
      have : 0 < cosHi xd * 2 ^ bA := by positivity
      omega
    · exact h0
  have hP : (0 : ℝ) < 2 ^ bA := by positivity
  refine le_alpha_of hd ha (u := (cosHi xd : ℝ) / 2 ^ bA) (l := (cosLo xc : ℝ) / 2 ^ bA) ?_ ?_ ?_
  · rw [← hxd]; exact le_cosHi xd
  · rw [← hxc]; exact cosLo_le hL
  · have hr : ((cosHi xd * 2 ^ bA : ℕ) : ℝ) ≤ ((cosLo xc * (2 ^ bA + cosHi xd) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at hr
    rw [div_le_iff₀ hP]
    have e : (cosLo xc : ℝ) / 2 ^ bA * (1 + (cosHi xd : ℝ) / 2 ^ bA) * 2 ^ bA =
        (cosLo xc : ℝ) * (2 ^ bA + cosHi xd) / 2 ^ bA := by
      field_simp
    rw [e, le_div_iff₀ hP]
    linarith

theorem alpha_le_of_aHi {d a : ℝ} {xd xc : ℕ} (h : aHi xd xc = true) (hd : 0 < d ∧ d < π / 2)
    (ha : 0 ≤ a ∧ a ≤ π) (hxd : (xd : ℝ) / 2 ^ bA = d) (hxc : (xc : ℝ) / 2 ^ bA = a) : alpha d ≤ a := by
  unfold aHi at h
  rw [Nat.ble_eq] at h
  have hU := cosHi_pos xc
  have hL : 0 < cosLo xd := by
    rcases Nat.eq_zero_or_pos (cosLo xd) with h0 | h0
    · rw [h0, zero_mul] at h
      have : 0 < cosHi xc * (2 ^ bA + 0) := by positivity
      omega
    · exact h0
  have hP : (0 : ℝ) < 2 ^ bA := by positivity
  refine alpha_le_of hd ha (u := (cosHi xc : ℝ) / 2 ^ bA) (l := (cosLo xd : ℝ) / 2 ^ bA) ?_ (by positivity) ?_ ?_
  · rw [← hxd]; exact cosLo_le hL
  · rw [← hxc]; exact le_cosHi xc
  · have hr : ((cosHi xc * (2 ^ bA + cosLo xd) : ℕ) : ℝ) ≤ ((cosLo xd * 2 ^ bA : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at hr
    have e : (cosHi xc : ℝ) / 2 ^ bA * (1 + (cosLo xd : ℝ) / 2 ^ bA) =
        (cosHi xc : ℝ) * (2 ^ bA + cosLo xd) / 2 ^ bA / 2 ^ bA := by
      field_simp
    rw [e, div_le_div_iff_of_pos_right hP, div_le_iff₀ hP]
    linarith

theorem kfix_pos (k : ℕ) : 0 < kfix k := by
  unfold kfix
  rw [shl_eq]
  have : 0 < kman k := by unfold kman; exact Nat.add_pos_right _ (by norm_num)
  positivity

theorem recOK_of_alphaRec {g box it : ℕ} (h : alphaRec g box it = true) : RecOK g box it := by
  simp only [alphaRec, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ho, hdv⟩, mo⟩, mdv⟩, knew⟩, kdl⟩, kdh⟩, hdh⟩, hnw⟩, hside⟩ := h
  rw [fk_bits7, nvK_eq, Nat.blt_eq] at ho
  rw [fk_bits6, nvK_eq, Nat.blt_eq] at hdv
  rw [fk_bits7, Nat.beq_eq] at mo
  rw [fk_bits6, Nat.beq_eq] at mdv
  rw [Walk.kf_new] at knew
  rw [Walk.kf_new] at hnw
  rw [fk_bits6, bk_eq] at kdl
  rw [fk_bits6, bk_eq] at kdh
  rw [fk_bits6, bk_eq] at hdh
  rw [Nat.blt_eq] at hdh
  rw [Nat.ble_eq] at hnw
  rw [fk_bits7, fk_bits6, Walk.kf_new, bk_eq, bk_eq] at hside
  intro S hS
  show BoxMem (Ctx.nv g) (setBnd box (bits it 64 7) (itNew it)) S.x
  set o := bits it 64 7 / 2 with ho'
  set dv := bits it 97 6 with hdv'
  have hxo : S.x o = alpha S.A.d := by simp [Sol.x, Ctx.val, mo]
  have hxd : S.x dv = S.A.d := val_d S.lab S.A mdv
  have hdr := d_range S
  have hbd := hS dv hdv
  rw [hxd, keyVal_kgood kdl, keyVal_kgood kdh] at hbd
  have hpi := cTPL_le_two_pi
  have hP62 : (0 : ℝ) < 2 ^ 62 := by positivity

  set a : ℝ := (kfix (itNew it) : ℝ) / 2 ^ 62 with ha'
  have ha : 0 ≤ a ∧ a ≤ π := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hP62.le, ?_⟩
    have h2 : ((2 * kfix (itNew it) : ℕ) : ℝ) ≤ (cTPL : ℝ) := by exact_mod_cast hnw
    push_cast at h2
    rw [ha', div_le_iff₀ hP62]
    have := (div_le_iff₀ hP62).mp hpi
    linarith
  have hka : keyVal (itNew it) = a := keyVal_kgood knew
  refine boxMem_set (bits_lt it 0 64) hS (fun h0 => ?_) (fun h1 => ?_)
  ·
    have hs0 : ¬ bits it 64 7 % 2 = 1 := by omega
    simp only [hs0, ↓reduceIte] at hside
    rw [hka, ← ho', hxo]
    set dl : ℝ := (kfix (bnd box (2 * dv)) : ℝ) / 2 ^ 62
    have hdl0 : 0 < dl := div_pos (Nat.cast_pos.mpr (kfix_pos _)) hP62
    have hdl : 0 < dl ∧ dl < π / 2 := ⟨hdl0, lt_of_le_of_lt hbd.1 hdr.2⟩
    exact (le_alpha_of_aLo hside hdl ha (xA_real _) (xA_real _)).trans (alpha_mono hdl0 hdr.2 hbd.1)
  ·
    simp only [h1, ↓reduceIte] at hside
    rw [hka, ← ho', hxo]
    set dh : ℝ := (kfix (bnd box (2 * dv + 1)) : ℝ) / 2 ^ 62
    have hdh' : dh < π / 2 := by
      have h4 : ((4 * kfix (bnd box (2 * dv + 1)) : ℕ) : ℝ) < (cTPL : ℝ) := by exact_mod_cast hdh
      push_cast at h4
      have := (div_le_iff₀ hP62).mp hpi
      show (kfix (bnd box (2 * dv + 1)) : ℝ) / 2 ^ 62 < π / 2
      rw [div_lt_iff₀ hP62]
      linarith
    have hdh0 : 0 < dh := lt_of_lt_of_le hdr.1 hbd.2
    exact (alpha_mono hdr.1 hdh' hbd.2).trans (alpha_le_of_aHi hside ⟨hdh0, hdh'⟩ ha (xA_real _) (xA_real _))

theorem alpha_fold : ∀ (l : List Ev) (s : Bool),
    l.foldl (fun s e => alphaChecker.step e s) s = true → s = true ∧ ∀ e ∈ l, e.OK := by
  intro l
  induction l with
  | nil => exact fun s h => ⟨h, fun e he => by simp at he⟩
  | cons ev l ih =>
    intro s h
    change List.foldl (fun s e => alphaChecker.step e s) (alphaChecker.step ev s) l = true at h
    obtain ⟨h1, hl⟩ := ih _ h
    cases ev with
    | kill g box it => exact absurd h1 (by change ¬ false = true; simp)
    | record g box it =>
      change (s && alphaRec g box it) = true at h1
      rw [Bool.and_eq_true] at h1
      refine ⟨h1.1, fun e he => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact recOK_of_alphaRec h1.2
      · exact hl e he

theorem alphaChecker_sound : alphaChecker.Sound (kindIs 1) := by
  intro tr _ _ hfin
  exact (alpha_fold tr alphaChecker.init hfin).2

end Tammes15.D3Data
