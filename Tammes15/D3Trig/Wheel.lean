import Tammes15.D3Trig.WheelSpec

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel Tammes15.D3Kernel.Pent Tammes15.D3Kernel.KForm

def wRoute (it : ℕ) : ℕ := fk it 75 3

def wM (it : ℕ) : ℕ := fk it 77 3

def wD (it : ℕ) : ℕ := fk it 79 63

def wTy (it : ℕ) : ℕ := fk it 85 3

def wI (it : ℕ) : ℕ := fk it 87 7

def wRp (it : ℕ) : ℕ := fk it 90 63

def wRi (it : ℕ) : ℕ := fk it 96 63

def wRm (it : ℕ) : ℕ := fk it 102 63

def wU (it : ℕ) : ℕ := fk it 108 63

def wKr (it : ℕ) : ℕ := fk it 114 7

def wKd (it : ℕ) : ℕ := fk it 117 3

def wRj (it j : ℕ) : ℕ := fk it (Nat.add 85 (Nat.mul 6 j)) 63

def wB (it j : ℕ) : ℕ := fk it (Nat.add 128 (Nat.mul 32 j)) 4294967295

def wO (it : ℕ) : ℕ := Nat.shiftRight (fk it 64 127) 1

def wOth (it : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) (wRp it) (wRm it) (Nat.beq (wO it) (wRp it))

def endW (up : Bool) (box v : ℕ) : ℕ :=
  @Bool.rec (fun _ => ℕ) (kfl (bk box (Nat.shiftLeft v 1))) (kce (bk box (Nat.add (Nat.shiftLeft v 1) 1))) up

def wF2 (hi : Bool) (box it : ℕ) : ℕ :=
  @Bool.rec (fun _ => ℕ) (Nat.add (claim it) (Nat.shiftLeft (endW hi box (wOth it)) 32))
    (Nat.add (endW hi box (wRp it)) (Nat.shiftLeft (endW hi box (wRm it)) 32)) (Nat.beq (wTy it) 1)

def wF3 (hi : Bool) (box it : ℕ) : ℕ :=
  @Bool.rec (fun _ => ℕ) (endW (!hi) box (wU it)) (claim it) (Nat.beq (wTy it) 1)

def lo32 (F : ℕ) : ℕ := Nat.land F 4294967295

def hi32 (F : ℕ) : ℕ := Nat.land (Nat.shiftRight F 32) 4294967295

def cutW : ℕ → ℕ → ℕ → List ℕ
  | 0, lo, hi => [Nat.add lo (Nat.shiftLeft hi 32)]
  | k + 1, lo, hi => cutW k lo (Nat.shiftRight (Nat.add lo hi) 1) ++ cutW k (Nat.shiftRight (Nat.add lo hi) 1) hi

def subsW (kr kd F0 F1 : ℕ) : List (ℕ × ℕ) :=
  (cutW kr (lo32 F1) (hi32 F1)).flatMap fun pr => (cutW kd (lo32 F0) (hi32 F0)).map fun pd => (pd, pr)

theorem fld_lo32 (F : ℕ) : fld F 0 = (lo32 F : ℝ) / 2 ^ 24 ∧ fld F 32 = (hi32 F : ℝ) / 2 ^ 24 := by
  have h4294967295 : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
  have hlo_val : (lo32 F : ℝ) = ((F % 2 ^ 32 : ℕ) : ℝ) := by
    dsimp [lo32]
    rw [h4294967295, Nat.and_two_pow_sub_one_eq_mod]
  have hhi_val : (hi32 F : ℝ) = (((F / 2 ^ 32) % 2 ^ 32 : ℕ) : ℝ) := by
    dsimp [hi32]
    rw [h4294967295, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  have hfld0 : fld F 0 = ((F % 2 ^ 32 : ℕ) : ℝ) / 2 ^ 24 := by
    simp [fld, pow_zero, Nat.div_one]
  have hfld32 : fld F 32 = (((F / 2 ^ 32) % 2 ^ 32 : ℕ) : ℝ) / 2 ^ 24 := by
    simp [fld]
  constructor
  · rw [hfld0, hlo_val]
  · rw [hfld32, hhi_val]

theorem cutW_cover (k lo hi : ℕ) (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 32) (x : ℝ)
    (h1 : (lo : ℝ) / 2 ^ 24 ≤ x) (h2 : x ≤ (hi : ℝ) / 2 ^ 24) : ∃ p ∈ cutW k lo hi, fld p 0 ≤ x ∧ x ≤ fld p 32 := by
  induction' k with k ih generalizing lo hi
  ·
    rw [cutW]
    have hpos : 0 < 2 ^ 32 := by norm_num
    have hfld0 : fld (Nat.add lo (Nat.shiftLeft hi 32)) 0 = (lo : ℝ) / 2 ^ 24 := by
      dsimp [fld]

      have h4294967296 : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
      rw [h4294967296, Nat.div_one]
      have hshift : hi <<< 32 = hi * 2 ^ 32 := Nat.shiftLeft_eq hi 32
      simpa [hshift] using (Nat.add_mul_mod_self_right lo hi (2 ^ 32)).trans (Nat.mod_eq_of_lt hlo)
    have hfld32 : fld (Nat.add lo (Nat.shiftLeft hi 32)) 32 = (hi : ℝ) / 2 ^ 24 := by
      dsimp [fld]

      have h4294967296 : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
      rw [h4294967296]

      have hshift : hi <<< 32 = hi * 2 ^ 32 := Nat.shiftLeft_eq hi 32
      rw [hshift]

      have hdiv_inner : (Nat.add lo (hi * 2 ^ 32)) / 2 ^ 32 = hi := by
        have h := Nat.add_mul_div_right lo hi hpos

        rw [Nat.div_eq_of_lt hlo] at h

        simpa [Nat.zero_add] using h
      have hnum : ((Nat.add lo (hi * 2 ^ 32)) / 2 ^ 32 % 2 ^ 32 : ℕ) = hi := by
        rw [hdiv_inner]
        exact Nat.mod_eq_of_lt hhi

      simpa [hnum]
    refine ⟨Nat.add lo (Nat.shiftLeft hi 32), by simp, ?_, ?_⟩
    · rw [hfld0]
      exact h1
    · rw [hfld32]
      exact h2
  ·
    rw [cutW]
    set m := Nat.shiftRight (Nat.add lo hi) 1 with hm
    have hm_lt : m < 2 ^ 32 := by
      rw [hm]

      have h' : (Nat.add lo hi).shiftRight 1 = (Nat.add lo hi) / 2 := by
        simpa using Nat.shiftRight_eq_div_pow (Nat.add lo hi) 1
      rw [h']

      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]

      have hsum : lo + hi < 2 ^ 33 := by
        have h : 2 ^ 32 + 2 ^ 32 = 2 ^ 33 := by norm_num
        omega

      have h_mul : (2 : ℕ) ^ 32 * 2 = (2 : ℕ) ^ 33 := by norm_num
      rw [h_mul]
      exact hsum
    by_cases hx : (x : ℝ) ≤ (m : ℝ) / 2 ^ 24
    ·
      rcases ih lo m hlo hm_lt h1 hx with ⟨p, hp, hp0, hp32⟩
      refine ⟨p, ?_, hp0, hp32⟩
      rw [List.mem_append]
      left
      exact hp
    ·
      have hx' : (m : ℝ) / 2 ^ 24 ≤ x := by

        linarith
      rcases ih m hi hm_lt hhi hx' h2 with ⟨p, hp, hp0, hp32⟩
      refine ⟨p, ?_, hp0, hp32⟩
      rw [List.mem_append]
      right
      exact hp

theorem laneClaimW_of_subs (hi : Bool) (kr kd F0 F1 F2 F3 : ℕ)
    (h : ∀ x ∈ subsW kr kd F0 F1, LaneClaimW hi x.1 x.2 F2 F3) : LaneClaimW hi F0 F1 F2 F3 := by
  intro d r hd0 hd32 hr0 hr32

  have hF0 := fld_lo32 F0
  have hF1 := fld_lo32 F1
  rcases hF0 with ⟨hF0_0, hF0_32⟩
  rcases hF1 with ⟨hF1_0, hF1_32⟩

  have hd0' : (lo32 F0 : ℝ) / (2 ^ 24 : ℝ) ≤ d := by
    simpa [hF0_0] using hd0
  have hd32' : d ≤ (hi32 F0 : ℝ) / (2 ^ 24 : ℝ) := by
    simpa [hF0_32] using hd32
  have hr0' : (lo32 F1 : ℝ) / (2 ^ 24 : ℝ) ≤ r := by
    simpa [hF1_0] using hr0
  have hr32' : r ≤ (hi32 F1 : ℝ) / (2 ^ 24 : ℝ) := by
    simpa [hF1_32] using hr32

  have hlo32_0 : lo32 F0 < 2 ^ 32 := by
    have : lo32 F0 = Nat.land F0 4294967295 := rfl
    rw [this, Nat.land_eq]
    have hle : F0 &&& 4294967295 ≤ 4294967295 := Nat.and_le_right
    have hlt : 4294967295 < 2 ^ 32 := by decide
    exact lt_of_le_of_lt hle hlt
  have hhi32_0 : hi32 F0 < 2 ^ 32 := by
    have : hi32 F0 = Nat.land (Nat.shiftRight F0 32) 4294967295 := rfl
    rw [this, Nat.land_eq]
    have hle : (Nat.shiftRight F0 32) &&& 4294967295 ≤ 4294967295 := Nat.and_le_right
    have hlt : 4294967295 < 2 ^ 32 := by decide
    exact lt_of_le_of_lt hle hlt
  have hlo32_1 : lo32 F1 < 2 ^ 32 := by
    have : lo32 F1 = Nat.land F1 4294967295 := rfl
    rw [this, Nat.land_eq]
    have hle : F1 &&& 4294967295 ≤ 4294967295 := Nat.and_le_right
    have hlt : 4294967295 < 2 ^ 32 := by decide
    exact lt_of_le_of_lt hle hlt
  have hhi32_1 : hi32 F1 < 2 ^ 32 := by
    have : hi32 F1 = Nat.land (Nat.shiftRight F1 32) 4294967295 := rfl
    rw [this, Nat.land_eq]
    have hle : (Nat.shiftRight F1 32) &&& 4294967295 ≤ 4294967295 := Nat.and_le_right
    have hlt : 4294967295 < 2 ^ 32 := by decide
    exact lt_of_le_of_lt hle hlt

  obtain ⟨pd, hpd, hpd0, hpd32⟩ := cutW_cover kd (lo32 F0) (hi32 F0) hlo32_0 hhi32_0 d hd0' hd32'
  obtain ⟨pr, hpr, hpr0, hpr32⟩ := cutW_cover kr (lo32 F1) (hi32 F1) hlo32_1 hhi32_1 r hr0' hr32'

  have hmem : (pd, pr) ∈ subsW kr kd F0 F1 := by
    unfold subsW
    apply List.mem_flatMap.mpr
    refine ⟨pr, hpr, ?_⟩
    apply List.mem_map.mpr
    exact ⟨pd, hpd, rfl⟩

  have hresult := h (pd, pr) hmem
  exact hresult d r hpd0 hpd32 hpr0 hpr32

def inDomBW (F0 F1 F2 F3 : ℕ) : Bool :=
  Nat.blt F0 18446744073709551616 && Nat.blt F1 18446744073709551616 && Nat.blt F2 18446744073709551616 &&
  Nat.blt F3 4294967296 &&
  Nat.ble 15099495 (F0 % 4294967296) && Nat.ble (F0 / 4294967296 % 4294967296) 16777216 &&
  Nat.ble (F2 % 4294967296) 52680458 && Nat.ble (F2 / 4294967296 % 4294967296) 52680458

def inDomBWS (F0 F1 F2 F3 : ℕ) : Bool :=
  Nat.blt F0 18446744073709551616 && Nat.blt F1 18446744073709551616 && Nat.blt F2 18446744073709551616 &&
  Nat.blt F3 4294967296

theorem inDomBW_sound {F0 F1 F2 F3 : ℕ} (h : inDomBW F0 F1 F2 F3 = true) : InDomW F0 F1 F2 F3 := by
  simp only [inDomBW, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hF0, hF1⟩, hF2⟩, hF3⟩, hF0lo⟩, hF0hi⟩, hF2lo⟩, hF2hi⟩
  have h2_64 : (18446744073709551616 : ℕ) = (2 : ℕ) ^ 64 := by norm_num
  have h2_32 : (4294967296 : ℕ) = (2 : ℕ) ^ 32 := by norm_num
  rw [h2_64] at hF0 hF1 hF2
  rw [h2_32] at hF3
  have hF0lo' : (0.9 : ℝ) ≤ fld F0 0 := by
    simp [fld]
    have hnum : (15099495 : ℝ) ≤ ((F0 % (2 : ℕ) ^ 32 : ℕ) : ℝ) := by exact_mod_cast hF0lo
    have hdiv : (0.9 : ℝ) ≤ (15099495 : ℝ) / ((2 : ℝ) ^ 24) := by norm_num
    calc
      (0.9 : ℝ) ≤ (15099495 : ℝ) / ((2 : ℝ) ^ 24) := hdiv
      _ ≤ ((F0 % (2 : ℕ) ^ 32 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) := by
        exact (div_le_div_of_nonneg_right hnum (by positivity))
  have hF0hi' : fld F0 32 ≤ (1 : ℝ) := by
    simp [fld]
    have hnum : (((F0 / (2 : ℕ) ^ 32) % (2 : ℕ) ^ 32 : ℕ) : ℝ) ≤ (16777216 : ℝ) := by exact_mod_cast hF0hi
    have hone : (16777216 : ℝ) / ((2 : ℝ) ^ 24) = (1 : ℝ) := by norm_num
    calc
      (((F0 / (2 : ℕ) ^ 32) % (2 : ℕ) ^ 32 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) ≤ (16777216 : ℝ) / ((2 : ℝ) ^ 24) := by
        exact (div_le_div_of_nonneg_right hnum (by positivity))
      _ = (1 : ℝ) := hone
  have hF2lo' : fld F2 0 ≤ (3.14 : ℝ) := by
    simp [fld]
    have hnum : ((F2 % (2 : ℕ) ^ 32 : ℕ) : ℝ) ≤ (52680458 : ℝ) := by exact_mod_cast hF2lo
    have hbound : (52680458 : ℝ) / ((2 : ℝ) ^ 24) ≤ (3.14 : ℝ) := by norm_num
    calc
      ((F2 % (2 : ℕ) ^ 32 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) ≤ (52680458 : ℝ) / ((2 : ℝ) ^ 24) := by
        exact (div_le_div_of_nonneg_right hnum (by positivity))
      _ ≤ (3.14 : ℝ) := hbound
  have hF2hi' : fld F2 32 ≤ (3.14 : ℝ) := by
    simp [fld]
    have hnum : (((F2 / (2 : ℕ) ^ 32) % (2 : ℕ) ^ 32 : ℕ) : ℝ) ≤ (52680458 : ℝ) := by exact_mod_cast hF2hi
    have hbound : (52680458 : ℝ) / ((2 : ℝ) ^ 24) ≤ (3.14 : ℝ) := by norm_num
    calc
      (((F2 / (2 : ℕ) ^ 32) % (2 : ℕ) ^ 32 : ℕ) : ℝ) / ((2 : ℝ) ^ 24) ≤ (52680458 : ℝ) / ((2 : ℝ) ^ 24) := by
        exact (div_le_div_of_nonneg_right hnum (by positivity))
      _ ≤ (3.14 : ℝ) := hbound
  exact ⟨hF0, hF1, hF2, hF3, hF0lo', hF0hi', hF2lo', hF2hi'⟩

theorem inDomBWS_sound {F0 F1 F2 F3 : ℕ} (h : inDomBWS F0 F1 F2 F3 = true) : InDomWS F0 F1 F2 F3 := by
  simp only [inDomBWS, Bool.and_eq_true, Nat.blt_eq] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> omega

theorem two_pi_gt : (105414356 : ℝ) / 2 ^ 24 < 2 * Real.pi := by
  have h : (105414356 : ℝ) / 2 ^ 24 < 2 * (3.14159265358979323846 : ℝ) := by
    norm_num
  linarith [Real.pi_gt_d20, h]

def okWV (g box it : ℕ) : Bool :=
  let m := wM it
  let i := wI it
  let nv := Ctx.nv g
  let b := Nat.add 258 (Nat.mul 6 m)
  Nat.blt m (Ctx.k g) && Nat.blt i 6 &&
  Nat.blt (wD it) nv && Nat.blt (wRp it) nv && Nat.blt (wRi it) nv && Nat.blt (wRm it) nv &&
  Nat.beq (Ctx.mean g (wD it)) 1 &&
  Nat.beq (Ctx.mean g (wRp it)) (Nat.add b (Nat.mod (Nat.add i 1) 6)) &&
  Nat.beq (Ctx.mean g (wRi it)) (Nat.add b i) &&
  Nat.beq (Ctx.mean g (wRm it)) (Nat.add b (Nat.mod (Nat.add i 5) 6)) &&
  kok (bk box (2 * wD it)) && kok (bk box (2 * wD it + 1)) && kok (Nat.land it 18446744073709551615)

def okW (hi : Bool) (g box it : ℕ) : Bool :=
  let c := Ctx.code g
  let s := fk it 64 1
  let o := wO it
  okWV g box it && Nat.blt (wU it) (Ctx.nv g) &&
  Nat.beq (Ctx.mean g (wU it)) (Nat.add 2 (c.faceIter (Ctx.base g (wM it)) (wI it))) &&
  kok (bk box (2 * wRi it)) && kok (bk box (2 * wRi it + 1)) &&
  kok (bk box (2 * wRp it)) && kok (bk box (2 * wRp it + 1)) && kok (bk box (2 * wRm it)) &&
  kok (bk box (2 * wRm it + 1)) && kok (bk box (2 * wU it)) && kok (bk box (2 * wU it + 1)) &&
  ((Nat.beq (wTy it) 1 && Nat.beq o (wU it) && Nat.beq s (@Bool.rec (fun _ => ℕ) 0 1 hi)) ||
    (Nat.beq (wTy it) 2 && (Nat.beq o (wRp it) || Nat.beq o (wRm it)) &&
      Nat.beq s (@Bool.rec (fun _ => ℕ) 1 0 hi))) &&
  inDomBW (lf box (wD it)) (lf box (wRi it)) (wF2 hi box it) (wF3 hi box it)

def okWA (g box it : ℕ) : Bool :=
  let s := fk it 64 1
  let nw := Nat.land it 18446744073709551615
  okWV g box it && Nat.beq (wO it) (wRi it) &&
  @Bool.rec (fun _ => Bool) (Nat.ble (kce nw) (kfl (bk box (2 * wD it))))
    (Nat.ble (Nat.mul 3 (kce (bk box (2 * wD it + 1)))) (kfl nw)) (Nat.beq s 1)

def okWT (g box it : ℕ) : Bool :=
  let s := fk it 64 1
  let dl := kfl (bk box (2 * wD it))
  let dh := kce (bk box (2 * wD it + 1))
  let rl := kfl (bk box (2 * wRi it))
  let rh := kce (bk box (2 * wRi it + 1))
  okWV g box it && Nat.beq (wTy it) 3 && (Nat.beq (wO it) (wRp it) || Nat.beq (wO it) (wRm it)) &&
  kok (bk box (2 * wRi it)) && kok (bk box (2 * wRi it + 1)) &&
  Nat.ble 15099495 dl && Nat.ble dh 16777216 &&
  @Bool.rec (fun _ => Bool) (Nat.ble (Nat.add (claim it) dh) rl || Nat.ble (Nat.add (claim it) rh) dl)
    (Nat.ble (Nat.add rh dh) (claim it)) (Nat.beq s 1)

def okWX (g box it : ℕ) : Bool := @Bool.rec (fun _ => Bool) (okWT g box it) (okWA g box it) (Nat.beq (wTy it) 0)

def okWS (g box it : ℕ) : Bool :=
  let m := wM it
  let nv := Ctx.nv g
  Nat.blt m (Ctx.k g) && Nat.blt (wD it) nv && Nat.beq (Ctx.mean g (wD it)) 1 &&
  kok (bk box (2 * wD it)) && kok (bk box (2 * wD it + 1)) &&
  [0, 1, 2, 3, 4, 5].all (fun j => Nat.blt (wRj it j) nv &&
    Nat.beq (Ctx.mean g (wRj it j)) (Nat.add (Nat.add 258 (Nat.mul 6 m)) j) &&
    kok (bk box (2 * wRj it j)) && kok (bk box (2 * wRj it j + 1))) &&
  Nat.ble (Nat.add (Nat.add (Nat.add (wB it 0) (wB it 1)) (Nat.add (wB it 2) (wB it 3)))
    (Nat.add (wB it 4) (wB it 5))) 105414356

def inDomBWK (F0 F1 F2 F3 : ℕ) : Bool :=
  Nat.blt F0 18446744073709551616 && Nat.blt F1 18446744073709551616 && Nat.blt F2 18446744073709551616 &&
  Nat.blt F3 4294967296 &&
  Nat.ble 15099495 (Nat.land F0 4294967295) && Nat.ble (Nat.land (Nat.shiftRight F0 32) 4294967295) 16777216 &&
  Nat.ble (Nat.land F2 4294967295) 52680458 && Nat.ble (Nat.land (Nat.shiftRight F2 32) 4294967295) 52680458

def okWVK (g box it : ℕ) : Bool :=
  let m := wM it
  let i := wI it
  let nv := nvCK g
  let b := Nat.add 258 (Nat.mul 6 m)
  Nat.blt m (kK g) && Nat.blt i 6 &&
  Nat.blt (wD it) nv && Nat.blt (wRp it) nv && Nat.blt (wRi it) nv && Nat.blt (wRm it) nv &&
  Nat.beq (meanK g (wD it)) 1 &&
  Nat.beq (meanK g (wRp it)) (Nat.add b (Nat.mod (Nat.add i 1) 6)) &&
  Nat.beq (meanK g (wRi it)) (Nat.add b i) &&
  Nat.beq (meanK g (wRm it)) (Nat.add b (Nat.mod (Nat.add i 5) 6)) &&
  kokK (bk box (Nat.shiftLeft (wD it) 1)) && kokK (bk box (Nat.add (Nat.shiftLeft (wD it) 1) 1)) &&
  kokK (Nat.land it 18446744073709551615)

def okWK (hi : Bool) (g box it : ℕ) : Bool :=
  let s := fk it 64 1
  let o := wO it
  okWVK g box it && Nat.blt (wU it) (nvCK g) &&
  Nat.beq (meanK g (wU it)) (Nat.add 2 (iterK (Nat.shiftRight g 64) (baseK g (wM it)) (wI it))) &&
  kokK (bk box (Nat.shiftLeft (wRi it) 1)) && kokK (bk box (Nat.add (Nat.shiftLeft (wRi it) 1) 1)) &&
  kokK (bk box (Nat.shiftLeft (wRp it) 1)) && kokK (bk box (Nat.add (Nat.shiftLeft (wRp it) 1) 1)) &&
  kokK (bk box (Nat.shiftLeft (wRm it) 1)) && kokK (bk box (Nat.add (Nat.shiftLeft (wRm it) 1) 1)) &&
  kokK (bk box (Nat.shiftLeft (wU it) 1)) && kokK (bk box (Nat.add (Nat.shiftLeft (wU it) 1) 1)) &&
  ((Nat.beq (wTy it) 1 && Nat.beq o (wU it) && Nat.beq s (@Bool.rec (fun _ => ℕ) 0 1 hi)) ||
    (Nat.beq (wTy it) 2 && (Nat.beq o (wRp it) || Nat.beq o (wRm it)) &&
      Nat.beq s (@Bool.rec (fun _ => ℕ) 1 0 hi))) &&
  inDomBWK (lf box (wD it)) (lf box (wRi it)) (wF2 hi box it) (wF3 hi box it)

def okWAK (g box it : ℕ) : Bool :=
  let s := fk it 64 1
  let nw := Nat.land it 18446744073709551615
  okWVK g box it && Nat.beq (wO it) (wRi it) &&
  @Bool.rec (fun _ => Bool) (Nat.ble (kce nw) (kfl (bk box (Nat.shiftLeft (wD it) 1))))
    (Nat.ble (Nat.mul 3 (kce (bk box (Nat.add (Nat.shiftLeft (wD it) 1) 1)))) (kfl nw)) (Nat.beq s 1)

def okWTK (g box it : ℕ) : Bool :=
  let s := fk it 64 1
  let dl := kfl (bk box (Nat.shiftLeft (wD it) 1))
  let dh := kce (bk box (Nat.add (Nat.shiftLeft (wD it) 1) 1))
  let rl := kfl (bk box (Nat.shiftLeft (wRi it) 1))
  let rh := kce (bk box (Nat.add (Nat.shiftLeft (wRi it) 1) 1))
  okWVK g box it && Nat.beq (wTy it) 3 && (Nat.beq (wO it) (wRp it) || Nat.beq (wO it) (wRm it)) &&
  kokK (bk box (Nat.shiftLeft (wRi it) 1)) && kokK (bk box (Nat.add (Nat.shiftLeft (wRi it) 1) 1)) &&
  Nat.ble 15099495 dl && Nat.ble dh 16777216 &&
  @Bool.rec (fun _ => Bool) (Nat.ble (Nat.add (claim it) dh) rl || Nat.ble (Nat.add (claim it) rh) dl)
    (Nat.ble (Nat.add rh dh) (claim it)) (Nat.beq s 1)

def okWXK (g box it : ℕ) : Bool := @Bool.rec (fun _ => Bool) (okWTK g box it) (okWAK g box it) (Nat.beq (wTy it) 0)

def wsK (g box it nv b j : ℕ) : Bool :=
  Nat.blt (wRj it j) nv && Nat.beq (meanK g (wRj it j)) (Nat.add b j) &&
    kokK (bk box (Nat.shiftLeft (wRj it j) 1)) && kokK (bk box (Nat.add (Nat.shiftLeft (wRj it j) 1) 1))

def okWSK (g box it : ℕ) : Bool :=
  let m := wM it
  let nv := nvCK g
  let b := Nat.add 258 (Nat.mul 6 m)
  Nat.blt m (kK g) && Nat.blt (wD it) nv && Nat.beq (meanK g (wD it)) 1 &&
  kokK (bk box (Nat.shiftLeft (wD it) 1)) && kokK (bk box (Nat.add (Nat.shiftLeft (wD it) 1) 1)) &&
  (wsK g box it nv b 0 && (wsK g box it nv b 1 && (wsK g box it nv b 2 && (wsK g box it nv b 3 &&
    (wsK g box it nv b 4 && wsK g box it nv b 5))))) &&
  Nat.ble (Nat.add (Nat.add (Nat.add (wB it 0) (wB it 1)) (Nat.add (wB it 2) (wB it 3)))
    (Nat.add (wB it 4) (wB it 5))) 105414356

theorem shl1_eq (v : ℕ) : Nat.shiftLeft v 1 = 2 * v := by
  show v <<< 1 = 2 * v
  rw [Nat.shiftLeft_eq]; ring

theorem inDomBWK_eq (F0 F1 F2 F3 : ℕ) : inDomBWK F0 F1 F2 F3 = inDomBW F0 F1 F2 F3 := by
  have hland : ∀ F : ℕ, Nat.land F 4294967295 = F % 4294967296 := fun F => by
    show F &&& 4294967295 = F % 4294967296
    rw [show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hshift : ∀ F : ℕ, Nat.land (Nat.shiftRight F 32) 4294967295 = F / 4294967296 % 4294967296 := fun F => by
    show (F >>> 32) &&& 4294967295 = F / 4294967296 % 4294967296
    rw [show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow]
  unfold inDomBWK inDomBW
  rw [hland F0, hland F2, hshift F0, hshift F2]

theorem okWVK_eq (g box it : ℕ) : okWVK g box it = okWV g box it := by
  unfold okWVK okWV
  simp only [nvCK_eq, kK_eq, meanK_eq, kokK_eq, shl1_eq]

theorem okWK_eq (hi : Bool) (g box it : ℕ) : okWK hi g box it = okW hi g box it := by
  have hb : Ctx.base g (wM it) < 256 := by
    unfold Ctx.base bits; exact Nat.mod_lt _ (by norm_num)
  unfold okWK okW
  simp only [okWVK_eq, nvCK_eq, meanK_eq, kokK_eq, shl1_eq, baseK_eq, iterK_eq g _ _ hb, inDomBWK_eq]

theorem okWAK_eq (g box it : ℕ) : okWAK g box it = okWA g box it := by
  unfold okWAK okWA
  simp only [okWVK_eq, shl1_eq]

theorem okWTK_eq (g box it : ℕ) : okWTK g box it = okWT g box it := by
  unfold okWTK okWT
  simp only [okWVK_eq, kokK_eq, shl1_eq]

theorem okWXK_eq (g box it : ℕ) : okWXK g box it = okWX g box it := by
  unfold okWXK okWX
  rw [okWAK_eq, okWTK_eq]

theorem okWSK_eq (g box it : ℕ) : okWSK g box it = okWS g box it := by
  unfold okWSK okWS wsK
  simp only [nvCK_eq, kK_eq, meanK_eq, kokK_eq, shl1_eq, List.all_cons, List.all_nil, Bool.and_true]

theorem endW_lo (box v : ℕ) : endW false box v = kfl (bnd box (2 * v)) := by
  have h2 : Nat.shiftLeft v 1 = 2 * v := by rw [shl_eq]; ring
  show kfl (bk box (Nat.shiftLeft v 1)) = _
  rw [bk_eq, h2]

theorem endW_hi (box v : ℕ) : endW true box v = kce (bnd box (2 * v + 1)) := by
  have h2 : Nat.shiftLeft v 1 = 2 * v := by rw [shl_eq]; ring
  show kce (bk box (Nat.add (Nat.shiftLeft v 1) 1)) = _
  rw [bk_eq, h2]

theorem endW_lt {box v : ℕ} (up : Bool) (h1 : kok (bnd box (2 * v)) = true) (h2 : kok (bnd box (2 * v + 1)) = true) :
    endW up box v < 2 ^ 32 := by
  cases up
  · rw [endW_lo]; exact lt_trans (kce_lt h1).2 (by norm_num)
  · rw [endW_hi]; exact lt_trans (kce_lt h2).1 (by norm_num)

theorem endW_le {box v : ℕ} {y : ℝ} (h1 : kok (bnd box (2 * v)) = true) (hy : keyVal (bnd box (2 * v)) ≤ y) :
    (endW false box v : ℝ) / 2 ^ 24 ≤ y := by
  rw [endW_lo]; exact (kfl_le h1).trans hy

theorem le_endW {box v : ℕ} {y : ℝ} (h2 : kok (bnd box (2 * v + 1)) = true) (hy : y ≤ keyVal (bnd box (2 * v + 1))) :
    y ≤ (endW true box v : ℝ) / 2 ^ 24 := by
  rw [endW_hi]; exact hy.trans (le_kce h2)

theorem claimW_lt {it : ℕ} (h : kok (Nat.land it 18446744073709551615) = true) : claim it < 2 ^ 32 := by
  unfold claim
  cases Nat.beq (fk it 64 1) 1
  · exact lt_trans (kce_lt h).1 (by norm_num)
  · exact lt_trans (kce_lt h).2 (by norm_num)

theorem wO_eq (it : ℕ) : wO it = bits it 64 7 / 2 := by
  unfold wO; rw [fk_bits7]; exact Nat.shiftRight_eq_div_pow _ _

theorem side_eq (it : ℕ) : fk it 64 1 = bits it 64 7 % 2 := by
  rw [fk_bits1]; unfold bits; rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 7)]; rfl

theorem claim_s0 {it : ℕ} (h : fk it 64 1 = 0) : claim it = kce (Nat.land it 18446744073709551615) := by
  unfold claim; rw [h]; rfl

theorem claim_s1 {it : ℕ} (h : fk it 64 1 = 1) : claim it = kfl (Nat.land it 18446744073709551615) := by
  unfold claim; rw [h]; rfl

theorem recW_finish {g box it : ℕ} {S : Sol g} (hS : BoxMem (Ctx.nv g) box S.x)
    (knew : kok (Nat.land it 18446744073709551615) = true)
    (hlo : fk it 64 1 = 0 → (claim it : ℝ) / 2 ^ 24 ≤ S.x (wO it))
    (hhi : fk it 64 1 = 1 → S.x (wO it) ≤ (claim it : ℝ) / 2 ^ 24) :
    BoxMem (Ctx.nv g) (recBox box it) S.x := by
  have hs := side_eq it
  rw [wO_eq] at hlo hhi
  refine boxMem_set (bits_lt it 0 64) hS (fun h0 => ?_) (fun h1 => ?_)
  · have h0' : bits it 64 7 % 2 = 0 := h0
    have hs0 : fk it 64 1 = 0 := hs.trans h0'
    have hc := hlo hs0
    rw [claim_s0 hs0, Walk.kf_new] at hc
    rw [Walk.kf_new] at knew
    exact (le_kce knew).trans hc
  · have h1' : bits it 64 7 % 2 = 1 := h1
    have hs1 : fk it 64 1 = 1 := hs.trans h1'
    have hc := hhi hs1
    rw [claim_s1 hs1, Walk.kf_new] at hc
    rw [Walk.kf_new] at knew
    exact hc.trans (kfl_le knew)

theorem wheelC_lo {P Q p q r d T : ℝ} (hP : 0 ≤ P) (hPp : P ≤ p) (hp : p ≤ Real.pi) (hQ : 0 ≤ Q) (hQq : Q ≤ q)
    (hq : q ≤ Real.pi) (hr : 0 < r) (hr' : r < Real.pi) (hd : 0 < d) (hd' : d < Real.pi)
    (hL : T < wheelOut P Q r d) : T < wheelOut p q r d :=
  lt_of_lt_of_le hL (wheelOut_mono hP hPp hp hQ hQq hq hr hr' hd hd')

theorem wheelC_hi {P Q p q r d T : ℝ} (hp0 : 0 ≤ p) (hpP : p ≤ P) (hP : P ≤ Real.pi) (hq0 : 0 ≤ q) (hqQ : q ≤ Q)
    (hQ : Q ≤ Real.pi) (hr : 0 < r) (hr' : r < Real.pi) (hd : 0 < d) (hd' : d < Real.pi)
    (hL : wheelOut P Q r d < T) : wheelOut p q r d < T :=
  lt_of_le_of_lt (wheelOut_mono hp0 hpP hP hq0 hqQ hQ hr hr' hd hd') hL

theorem wheelD_up {c Q T w o r d u : ℝ} (hc0 : 0 ≤ c) (hQ0 : 0 ≤ Q) (hQo : Q ≤ o) (ho : o ≤ Real.pi)
    (hw : w ≤ Real.pi) (hr : 0 < r) (hr' : r < Real.pi) (hd : 0 < d) (hd' : d < Real.pi)
    (hu : u = gam w r d + gam o r d) (huT : u ≤ T) (hL : T < wheelOut c Q r d) : w < c := by
  refine lt_of_not_ge fun hcw => ?_
  have := wheelOut_mono hc0 hcw hw hQ0 hQo ho hr hr' hd hd'
  unfold wheelOut at this hL
  linarith

theorem wheelD_lo {c Q T w o r d u : ℝ} (hw0 : 0 ≤ w) (hc : c ≤ Real.pi) (ho0 : 0 ≤ o) (hoQ : o ≤ Q)
    (hQ : Q ≤ Real.pi) (hr : 0 < r) (hr' : r < Real.pi) (hd : 0 < d) (hd' : d < Real.pi)
    (hu : u = gam w r d + gam o r d) (hTu : T ≤ u) (hL : wheelOut c Q r d < T) : c < w := by
  refine lt_of_not_ge fun hcw => ?_
  have := wheelOut_mono hw0 hcw hc ho0 hoQ hQ hr hr' hd hd'
  unfold wheelOut at this hL
  linarith

theorem recOK_of_wheel {hi : Bool} {g box it : ℕ} (hok : okW hi g box it = true)
    (hc : LaneClaimW hi (lf box (wD it)) (lf box (wRi it)) (wF2 hi box it) (wF3 hi box it)) :
    RecOK g box it := by
  have hok' := hok
  simp only [okW, okWV, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, bk_eq, and_assoc] at hok'
  obtain ⟨hm, hi6, hdv, hpv, hiv, hmv, mdv, mpv, miv, mmv, kd1, kd2, knew, huv, muv, ki1, ki2, kp1, kp2, km1, km2,
    ku1, ku2, hty, hdom⟩ := hok'
  obtain ⟨-, -, -, -, hD1, hD2, hD3, hD4⟩ := inDomBW_sound hdom
  intro S hS
  set m : Fin (Ctx.k g) := ⟨wM it, hm⟩ with hmdef

  have hd : S.x (wD it) = S.A.d := val_d S.lab S.A mdv
  have hri : S.x (wRi it) = S.A.r m ⟨wI it, hi6⟩ := val_r S.lab S.A hm hi6 miv
  have hrp : S.x (wRp it) = S.A.r m ⟨(wI it + 1) % 6, Nat.mod_lt _ (by norm_num)⟩ :=
    val_r S.lab S.A hm (Nat.mod_lt _ (by norm_num)) mpv
  have hrm : S.x (wRm it) = S.A.r m ⟨(wI it + 5) % 6, Nat.mod_lt _ (by norm_num)⟩ :=
    val_r S.lab S.A hm (Nat.mod_lt _ (by norm_num)) mmv
  have hu : S.x (wU it) = S.A.fc (S.H.base m) (wI it) := by
    have hlab : ((S.lab (S.H.base m) : Fin (Ctx.D g)) : ℕ) = Ctx.base g (wM it) := S.hH m
    have hfi : (Ctx.code g).faceIter (Ctx.base g (wM it)) (wI it) = S.lab ((S.P.R.face ^ wI it) (S.H.base m)) := by
      rw [← hlab]; exact D3lp.faceIter_lab S.hm (S.H.base m) (wI it)
    have muv' : Ctx.mean g (wU it) = 2 + (S.lab ((S.P.R.face ^ (wI it)) (S.H.base m)) : ℕ) := by
      rw [← hfi]; exact muv
    exact val_corner S.lab S.A _ muv'
  have hrel : S.x (wU it) = wheelOut (S.x (wRp it)) (S.x (wRm it)) (S.x (wRi it)) (S.x (wD it)) := by
    rw [hu, hrp, hrm, hri, hd]; exact wheel_fc S.hR m hi6

  have hdB : fld (lf box (wD it)) 0 ≤ S.x (wD it) ∧ S.x (wD it) ≤ fld (lf box (wD it)) 32 :=
    lf_bounds kd1 kd2 (hS _ hdv)
  have hiB := lf_bounds ki1 ki2 (hS _ hiv)
  have hd09 : 0.9 ≤ S.x (wD it) := hD1.trans hdB.1
  have hd1 : S.x (wD it) ≤ 1 := hdB.2.trans hD2
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_gt_d2
  have rad : ∀ v j (hj : j < 6), S.x v = S.A.r m ⟨j, hj⟩ → 0.9 ≤ S.x v ∧ S.x v ≤ 3 := by
    intro v j hj hv
    have := wheel_r S.hR m ⟨j, hj⟩
    rw [← hv, ← hd] at this
    constructor <;> linarith
  have Rp := rad _ _ _ hrp
  have Ri := rad _ _ _ hri
  have Rm := rad _ _ _ hrm
  have hr0 : 0 < S.x (wRi it) := by linarith
  have hr1 : S.x (wRi it) < Real.pi := by linarith
  have hd0 : 0 < S.x (wD it) := by linarith
  have hd1' : S.x (wD it) < Real.pi := by linarith
  have hL := hc (S.x (wD it)) (S.x (wRi it)) hdB.1 hdB.2 hiB.1 hiB.2
  have nn : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) / 2 ^ 24 := fun n => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hclt : claim it < 2 ^ 32 := claimW_lt knew
  rcases hty with ⟨hty1, hoU, hs⟩ | ⟨hty2, hoR, hs⟩
  ·
    have hb1 : Nat.beq (wTy it) 1 = true := by rw [hty1]; rfl
    have hF3 : wF3 hi box it = claim it := by unfold wF3; rw [hb1]
    have hpl := endW_lt hi kp1 kp2
    have hml := endW_lt hi km1 km2
    have hF2 : wF2 hi box it = endW hi box (wRp it) + Nat.shiftLeft (endW hi box (wRm it)) 32 := by
      unfold wF2; rw [hb1]; rfl
    have hP := fld_pair _ _ hpl hml
    rw [hF2] at hL hD3 hD4
    rw [hP.1] at hL hD3
    rw [hP.2] at hL hD4
    rw [hF3, fld0_of_lt hclt] at hL
    cases hi
    · have hs0 : fk it 64 1 = 0 := hs
      simp only [Bool.false_eq_true, ↓reduceIte] at hL
      refine recW_finish hS knew (fun _ => ?_) (fun h1 => absurd (hs0.symm.trans h1) (by norm_num))
      rw [hoU, hrel]
      exact le_of_lt (wheelC_lo (nn _) (endW_le kp1 (hS _ hpv).1) (by linarith) (nn _)
        (endW_le km1 (hS _ hmv).1) (by linarith) hr0 hr1 hd0 hd1' hL)
    · have hs1 : fk it 64 1 = 1 := hs
      simp only [↓reduceIte] at hL
      refine recW_finish hS knew (fun h0 => absurd (hs1.symm.trans h0) (by norm_num)) (fun _ => ?_)
      rw [hoU, hrel]
      exact le_of_lt (wheelC_hi (by linarith) (le_endW kp2 (hS _ hpv).2) (by linarith) (by linarith)
        (le_endW km2 (hS _ hmv).2) (by linarith) hr0 hr1 hd0 hd1' hL)
  ·
    have hb1 : Nat.beq (wTy it) 1 = false := by rw [hty2]; rfl

    have hoth : S.x (wU it) = gam (S.x (wO it)) (S.x (wRi it)) (S.x (wD it)) +
          gam (S.x (wOth it)) (S.x (wRi it)) (S.x (wD it)) ∧
        kok (bnd box (2 * wOth it)) = true ∧ kok (bnd box (2 * wOth it + 1)) = true ∧ wOth it < Ctx.nv g ∧
        0.9 ≤ S.x (wOth it) ∧ S.x (wOth it) ≤ 3 ∧ 0.9 ≤ S.x (wO it) ∧ S.x (wO it) ≤ 3 := by
      by_cases hb : wO it = wRp it
      · have hbb : Nat.beq (wO it) (wRp it) = true := by rw [Nat.beq_eq]; exact hb
        have ho : wOth it = wRm it := by unfold wOth; rw [hbb]
        rw [ho, hb, hrel]
        exact ⟨rfl, km1, km2, hmv, Rm.1, Rm.2, Rp.1, Rp.2⟩
      · have hbb : Nat.beq (wO it) (wRp it) = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hb
        have ho : wOth it = wRp it := by unfold wOth; rw [hbb]
        have hom : wO it = wRm it := hoR.resolve_left hb
        rw [ho, hom, hrel]
        exact ⟨add_comm _ _, kp1, kp2, hpv, Rp.1, Rp.2, Rm.1, Rm.2⟩
    obtain ⟨hU, ko1, ko2, hov, O1, O2, W1, W2⟩ := hoth
    have hol := endW_lt hi ko1 ko2
    have hF2 : wF2 hi box it = claim it + Nat.shiftLeft (endW hi box (wOth it)) 32 := by
      unfold wF2; rw [hb1]; rfl
    have hP := fld_pair _ _ hclt hol
    rw [hF2] at hL hD3 hD4
    rw [hP.1] at hL hD3
    rw [hP.2] at hL hD4
    cases hi
    · have hs1 : fk it 64 1 = 1 := hs
      have hF3 : wF3 false box it = endW true box (wU it) := by unfold wF3; rw [hb1]; rfl
      have hul := endW_lt true ku1 ku2
      rw [hF3, fld0_of_lt hul] at hL
      simp only [Bool.false_eq_true, ↓reduceIte] at hL
      refine recW_finish hS knew (fun h0 => absurd (hs1.symm.trans h0) (by norm_num)) (fun _ => ?_)
      exact le_of_lt (wheelD_up (nn _) (nn _) (endW_le ko1 (hS _ hov).1) (by linarith)
        (by linarith) hr0 hr1 hd0 hd1' hU (le_endW ku2 (hS _ huv).2) hL)
    · have hs0 : fk it 64 1 = 0 := hs
      have hF3 : wF3 true box it = endW false box (wU it) := by unfold wF3; rw [hb1]; rfl
      have hul := endW_lt false ku1 ku2
      rw [hF3, fld0_of_lt hul] at hL
      simp only [↓reduceIte] at hL
      refine recW_finish hS knew (fun _ => ?_) (fun h1 => absurd (hs0.symm.trans h1) (by norm_num))
      exact le_of_lt (wheelD_lo (by linarith) (by linarith) (by linarith) (le_endW ko2 (hS _ hov).2)
        (by linarith) hr0 hr1 hd0 hd1' hU (endW_le ku1 (hS _ huv).1) hL)

theorem recOK_of_wheelA {g box it : ℕ} (hok : okWA g box it = true) : RecOK g box it := by
  have hok' := hok
  simp only [okWA, okWV, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, bk_eq, and_assoc] at hok'
  obtain ⟨hm, hi6, hdv, -, -, -, mdv, -, miv, -, kd1, kd2, knew, hoi, hX⟩ := hok'
  intro S hS
  set m : Fin (Ctx.k g) := ⟨wM it, hm⟩ with hmdef
  have hd : S.x (wD it) = S.A.d := val_d S.lab S.A mdv
  have hri : S.x (wRi it) = S.A.r m ⟨wI it, hi6⟩ := val_r S.lab S.A hm hi6 miv
  have hwr := wheel_r S.hR m ⟨wI it, hi6⟩
  rw [← hri, ← hd] at hwr
  have hdl := (hS _ hdv).1
  have hdh := (hS _ hdv).2
  refine recW_finish hS knew (fun hs0 => ?_) (fun hs1 => ?_)
  · rw [hs0] at hX
    have hX' : Nat.ble (kce (Nat.land it 18446744073709551615)) (kfl (bnd box (2 * wD it))) = true := hX
    rw [Nat.ble_eq] at hX'
    have hX'' : (kce (Nat.land it 18446744073709551615) : ℝ) ≤ kfl (bnd box (2 * wD it)) := by exact_mod_cast hX'
    rw [hoi, claim_s0 hs0]
    calc (kce (Nat.land it 18446744073709551615) : ℝ) / 2 ^ 24 ≤ kfl (bnd box (2 * wD it)) / 2 ^ 24 := by
          gcongr
      _ ≤ keyVal (bnd box (2 * wD it)) := kfl_le kd1
      _ ≤ S.x (wD it) := hdl
      _ ≤ S.x (wRi it) := hwr.1
  · rw [hs1] at hX
    have hX' : Nat.ble (Nat.mul 3 (kce (bnd box (2 * wD it + 1)))) (kfl (Nat.land it 18446744073709551615)) = true :=
      hX
    rw [Nat.ble_eq] at hX'
    have hX'' : (3 : ℝ) * kce (bnd box (2 * wD it + 1)) ≤ kfl (Nat.land it 18446744073709551615) := by
      have h3 : 3 * kce (bnd box (2 * wD it + 1)) ≤ kfl (Nat.land it 18446744073709551615) := hX'
      exact_mod_cast h3
    rw [hoi, claim_s1 hs1]
    have hk := le_kce kd2
    calc S.x (wRi it) ≤ 3 * S.x (wD it) := hwr.2
      _ ≤ 3 * ((kce (bnd box (2 * wD it + 1)) : ℝ) / 2 ^ 24) := by linarith
      _ ≤ (kfl (Nat.land it 18446744073709551615) : ℝ) / 2 ^ 24 := by
          rw [← mul_div_assoc]; gcongr

theorem recOK_of_wheelT {g box it : ℕ} (hok : okWT g box it = true) : RecOK g box it := by
  have hok' := hok
  simp only [okWT, okWV, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, bk_eq,
    and_assoc] at hok'
  obtain ⟨hm, hi6, hdv, hpv, hiv, hmv, mdv, mpv, miv, mmv, kd1, kd2, knew, -, hoR, ki1, ki2, hdl, hdh, hX⟩ := hok'
  intro S hS
  set m : Fin (Ctx.k g) := ⟨wM it, hm⟩ with hmdef
  have hd : S.x (wD it) = S.A.d := val_d S.lab S.A mdv
  have hri : S.x (wRi it) = S.A.r m ⟨wI it, hi6⟩ := val_r S.lab S.A hm hi6 miv
  have hrp : S.x (wRp it) = S.A.r m ⟨(wI it + 1) % 6, Nat.mod_lt _ (by norm_num)⟩ :=
    val_r S.lab S.A hm (Nat.mod_lt _ (by norm_num)) mpv
  have hrm : S.x (wRm it) = S.A.r m ⟨(wI it + 5) % 6, Nat.mod_lt _ (by norm_num)⟩ :=
    val_r S.lab S.A hm (Nat.mod_lt _ (by norm_num)) mmv

  have hwe : ∃ j : Fin 6, S.x (wO it) = S.A.r m j ∧
      eta (S.x (wO it)) (S.x (wRi it)) (S.x (wD it)) ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases hoR with ho | ho
    · refine ⟨_, by rw [ho]; exact hrp, ?_⟩
      rw [ho, hrp, hri, hd]; exact (wheel_eta S.hR m hi6).1
    · refine ⟨_, by rw [ho]; exact hrm, ?_⟩
      rw [ho, hrm, hri, hd]; exact (wheel_eta S.hR m hi6).2
  obtain ⟨j, hwj, heta⟩ := hwe
  have hwr := wheel_r S.hR m j
  rw [← hwj, ← hd] at hwr
  have hir := wheel_r S.hR m ⟨wI it, hi6⟩
  rw [← hri, ← hd] at hir

  have hdlo := (kfl_le kd1).trans (hS _ hdv).1
  have hdhi := (hS _ hdv).2.trans (le_kce kd2)
  have hdl' : (15099495 : ℝ) ≤ kfl (bnd box (2 * wD it)) := by exact_mod_cast hdl
  have hdh' : (kce (bnd box (2 * wD it + 1)) : ℝ) ≤ 16777216 := by exact_mod_cast hdh
  have hd09 : 0.9 ≤ S.x (wD it) := by
    have : (0.9 : ℝ) ≤ kfl (bnd box (2 * wD it)) / 2 ^ 24 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have hd1 : S.x (wD it) ≤ 1 := by
    have : (kce (bnd box (2 * wD it + 1)) : ℝ) / 2 ^ 24 ≤ 1 := by rw [div_le_iff₀ (by norm_num)]; linarith
    linarith
  have hpi := Real.pi_gt_three
  obtain ⟨t1, t2, t3⟩ := tri_of_eta heta (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hrlo := (kfl_le ki1).trans (hS _ hiv).1
  have hrhi := (hS _ hiv).2.trans (le_kce ki2)
  refine recW_finish hS knew (fun hs0 => ?_) (fun hs1 => ?_)
  · rw [hs0] at hX
    have hX' : (Nat.ble ((claim it).add (kce (bnd box (2 * wD it + 1)))) (kfl (bnd box (2 * wRi it))) ||
        Nat.ble ((claim it).add (kce (bnd box (2 * wRi it + 1)))) (kfl (bnd box (2 * wD it)))) = true := hX
    rw [Bool.or_eq_true, Nat.ble_eq, Nat.ble_eq] at hX'
    rcases hX' with h | h
    · have h' : claim it + kce (bnd box (2 * wD it + 1)) ≤ kfl (bnd box (2 * wRi it)) := h
      have h'' : (claim it : ℝ) + kce (bnd box (2 * wD it + 1)) ≤ kfl (bnd box (2 * wRi it)) := by exact_mod_cast h'
      have : (claim it : ℝ) / 2 ^ 24 + (kce (bnd box (2 * wD it + 1)) : ℝ) / 2 ^ 24 ≤
          (kfl (bnd box (2 * wRi it)) : ℝ) / 2 ^ 24 := by
        rw [← add_div]; gcongr
      linarith
    · have h' : claim it + kce (bnd box (2 * wRi it + 1)) ≤ kfl (bnd box (2 * wD it)) := h
      have h'' : (claim it : ℝ) + kce (bnd box (2 * wRi it + 1)) ≤ kfl (bnd box (2 * wD it)) := by exact_mod_cast h'
      have : (claim it : ℝ) / 2 ^ 24 + (kce (bnd box (2 * wRi it + 1)) : ℝ) / 2 ^ 24 ≤
          (kfl (bnd box (2 * wD it)) : ℝ) / 2 ^ 24 := by
        rw [← add_div]; gcongr
      linarith
  · rw [hs1] at hX
    have hX' : Nat.ble ((kce (bnd box (2 * wRi it + 1))).add (kce (bnd box (2 * wD it + 1)))) (claim it) = true := hX
    rw [Nat.ble_eq] at hX'
    have h' : kce (bnd box (2 * wRi it + 1)) + kce (bnd box (2 * wD it + 1)) ≤ claim it := hX'
    have h'' : (kce (bnd box (2 * wRi it + 1)) : ℝ) + kce (bnd box (2 * wD it + 1)) ≤ claim it := by exact_mod_cast h'
    have : (kce (bnd box (2 * wRi it + 1)) : ℝ) / 2 ^ 24 + (kce (bnd box (2 * wD it + 1)) : ℝ) / 2 ^ 24 ≤
        (claim it : ℝ) / 2 ^ 24 := by
      rw [← add_div]; gcongr
    linarith

theorem recOK_of_wheelX {g box it : ℕ} (hok : okWX g box it = true) : RecOK g box it := by
  unfold okWX at hok
  by_cases h0 : wTy it = 0
  · have hb : Nat.beq (wTy it) 0 = true := by rw [h0]; rfl
    rw [hb] at hok
    exact recOK_of_wheelA hok
  · have hb : Nat.beq (wTy it) 0 = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact h0
    rw [hb] at hok
    exact recOK_of_wheelT hok

theorem wB_lt (it j : ℕ) : wB it j < 2 ^ 32 := by
  have : wB it j = bits it (Nat.add 128 (Nat.mul 32 j)) 32 := land_shiftRight _ _ 32
  rw [this]; exact bits_lt _ _ _

theorem killOK_of_wsum {g box it : ℕ} (hok : okWS g box it = true)
    (hc : ∀ j < 6, LaneClaimWS (lf box (wD it)) (lf box (wRj it j)) (lf box (wRj it ((j + 1) % 6))) (wB it j)) :
    KillOK g box := by
  have hok' := hok
  simp only [okWS, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, List.all_eq_true, bk_eq, and_assoc] at hok'
  obtain ⟨hm, hdv, mdv, kd1, kd2, hall, hsum⟩ := hok'
  intro S hS
  exfalso
  set m : Fin (Ctx.k g) := ⟨wM it, hm⟩ with hmdef
  have hd : S.x (wD it) = S.A.d := val_d S.lab S.A mdv
  have hdB := lf_bounds kd1 kd2 (hS _ hdv)
  rw [hd] at hdB
  have hrad : ∀ j (hj : j < 6), fld (lf box (wRj it j)) 0 ≤ S.A.r m ⟨j, hj⟩ ∧
      S.A.r m ⟨j, hj⟩ ≤ fld (lf box (wRj it j)) 32 := by
    intro j hj
    obtain ⟨hv, hmean, k1, k2⟩ := hall j (by simp; omega)
    have hx : S.x (wRj it j) = S.A.r m ⟨j, hj⟩ := val_r S.lab S.A hm hj hmean
    have hb := lf_bounds k1 k2 (hS _ hv)
    rw [hx] at hb
    exact hb
  have hj : ∀ j : Fin 6, gam S.A.d (S.A.r m j) (S.A.r m (j + 1)) < (wB it j : ℝ) / 2 ^ 24 := by
    intro j
    have h1 := hrad j j.isLt
    have h2 := hrad ((j + 1) % 6) (Nat.mod_lt _ (by norm_num))
    have hj1 : (j + 1 : Fin 6) = ⟨((j : ℕ) + 1) % 6, Nat.mod_lt _ (by norm_num)⟩ := fin6_succ j.isLt
    have := hc j j.isLt S.A.d (S.A.r m j) (S.A.r m (j + 1)) hdB.1 hdB.2 h1.1 h1.2 (by rw [hj1]; exact h2.1)
      (by rw [hj1]; exact h2.2)
    rwa [fld0_of_lt (wB_lt it j)] at this
  have hsum6 := wheel_sum S.hR m
  have hlt : ∑ j : Fin 6, gam S.A.d (S.A.r m j) (S.A.r m (j + 1)) < ∑ j : Fin 6, (wB it j : ℝ) / 2 ^ 24 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hj j)
  have hsum' : wB it 0 + wB it 1 + (wB it 2 + wB it 3) + (wB it 4 + wB it 5) ≤ 105414356 := hsum
  have hs : ((wB it 0 : ℝ) + wB it 1 + (wB it 2 + wB it 3) + (wB it 4 + wB it 5)) ≤ 105414356 := by
    exact_mod_cast hsum'
  have hsumR : ∑ j : Fin 6, (wB it j : ℝ) / 2 ^ 24 ≤ 105414356 / 2 ^ 24 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (wB it j : ℝ) / 2 ^ 24) 6]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have key : (wB it 0 : ℝ) / 2 ^ 24 + (wB it 1 : ℝ) / 2 ^ 24 + (wB it 2 : ℝ) / 2 ^ 24 + (wB it 3 : ℝ) / 2 ^ 24 +
        (wB it 4 : ℝ) / 2 ^ 24 + (wB it 5 : ℝ) / 2 ^ 24 =
        ((wB it 0 : ℝ) + wB it 1 + (wB it 2 + wB it 3) + (wB it 4 + wB it 5)) / 2 ^ 24 := by ring
    rw [key]
    exact div_le_div_of_nonneg_right hs (by positivity)
  linarith [two_pi_gt]

def addW (s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool) (a b F2 F3 : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × Bool :=
  let sh := Nat.shiftLeft s.1 (nat_lit 6)
  (Nat.add s.1 1, Nat.add s.2.1 (Nat.shiftLeft a sh), Nat.add s.2.2.1 (Nat.shiftLeft b sh),
    Nat.add s.2.2.2.1 (Nat.shiftLeft F2 sh), Nat.add s.2.2.2.2.1 (Nat.shiftLeft F3 sh),
    s.2.2.2.2.2 && inDomBWK a b F2 F3)

def addWS (s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool) (a b c F3 : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × Bool :=
  let sh := Nat.shiftLeft s.1 (nat_lit 6)
  (Nat.add s.1 1, Nat.add s.2.1 (Nat.shiftLeft a sh), Nat.add s.2.2.1 (Nat.shiftLeft b sh),
    Nat.add s.2.2.2.1 (Nat.shiftLeft c sh), Nat.add s.2.2.2.2.1 (Nat.shiftLeft F3 sh),
    s.2.2.2.2.2 && inDomBWS a b c F3)

def ProgOKW (hi : Bool) (prog : Prog) : Prop :=
  ∀ (n F0 F1 F2 F3 : ℕ) (hs : List ℕ) (v : ℕ),
    (∀ i < n, InDomW (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) →
      Nat.beq (prog (oN n) F0 F1 F2 F3 hs) v = true → ∀ l < n, lane v l = 1 →
        LaneClaimW hi (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)

def ProgOKWS (prog : Prog) : Prop :=
  ∀ (n F0 F1 F2 F3 : ℕ) (hs : List ℕ) (v : ℕ),
    (∀ i < n, InDomWS (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) →
      Nat.beq (prog (oN n) F0 F1 F2 F3 hs) v = true → ∀ l < n, lane v l = 1 →
        LaneClaimWS (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)

def progCheckerW (hi : Bool) (prog : Prog) : Checker where
  σ := ℕ × ℕ × ℕ × ℕ × ℕ × Bool
  H := List ℕ
  init := (0, 0, 0, 0, 0, true)
  onRec g box it s :=
    (subsW (wKr it) (wKd it) (lf box (wD it)) (lf box (wRi it))).foldl
      (fun s x => addW s x.1 x.2 (wF2 hi box it) (wF3 hi box it))
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2 && okWK hi g box it)
  onKill _ _ _ s := (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, false)
  fin s hs := s.2.2.2.2.2 && Nat.beq (prog (oN s.1) s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 hs) (oN s.1)
  frc s k := @Bool.rec (fun _ => List ℕ) (k s) (k s)
    (Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0)
  frc_eq s k := by
    cases Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0 <;> rfl

def progCheckerWS (prog : Prog) : Checker where
  σ := ℕ × ℕ × ℕ × ℕ × ℕ × Bool
  H := List ℕ
  init := (0, 0, 0, 0, 0, true)
  onRec _ _ _ s := (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, false)
  onKill g box it s :=
    [0, 1, 2, 3, 4, 5].foldl
      (fun s j => addWS s (lf box (wD it)) (lf box (wRj it j)) (lf box (wRj it (Nat.mod (Nat.add j 1) 6))) (wB it j))
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2 && okWSK g box it)
  fin s hs := s.2.2.2.2.2 && Nat.beq (prog (oN s.1) s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 hs) (oN s.1)
  frc s k := @Bool.rec (fun _ => List ℕ) (k s) (k s)
    (Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0)
  frc_eq s k := by
    cases Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0 <;> rfl

def exactCheckerW : Checker where
  σ := Bool
  H := Unit
  init := true
  onRec g box it s := s && okWXK g box it
  onKill _ _ _ _ := false
  fin s _ := s
  frc s k := @Bool.rec (fun _ => List ℕ) (k s) (k s) s
  frc_eq s k := by cases s <;> rfl

abbrev WSt := ℕ × ℕ × ℕ × ℕ × ℕ × Bool

def LanesOK (D : ℕ → ℕ → ℕ → ℕ → Prop) (s : WSt) : Prop :=
  s.2.1 < 2 ^ (64 * s.1) ∧ s.2.2.1 < 2 ^ (64 * s.1) ∧ s.2.2.2.1 < 2 ^ (64 * s.1) ∧
    s.2.2.2.2.1 < 2 ^ (64 * s.1) ∧
    ∀ l < s.1, D (lane s.2.1 l) (lane s.2.2.1 l) (lane s.2.2.2.1 l) (lane s.2.2.2.2.1 l)

def HasLane (s : WSt) (q : ℕ × ℕ × ℕ × ℕ) : Prop :=
  ∃ l < s.1, lane s.2.1 l = q.1 ∧ lane s.2.2.1 l = q.2.1 ∧ lane s.2.2.2.1 l = q.2.2.1 ∧
    lane s.2.2.2.2.1 l = q.2.2.2

theorem lanes_append {D : ℕ → ℕ → ℕ → ℕ → Prop}
    (hD : ∀ {a b c d}, D a b c d → a < 2 ^ 64 ∧ b < 2 ^ 64 ∧ c < 2 ^ 64 ∧ d < 2 ^ 64)
    {n F0 F1 F2 F3 : ℕ} {ok ok' : Bool} (h : LanesOK D (n, F0, F1, F2, F3, ok)) {a b c d : ℕ} (hq : D a b c d) :
    LanesOK D (n + 1, F0 + a * 2 ^ (64 * n), F1 + b * 2 ^ (64 * n), F2 + c * 2 ^ (64 * n),
        F3 + d * 2 ^ (64 * n), ok') ∧
      HasLane (n + 1, F0 + a * 2 ^ (64 * n), F1 + b * 2 ^ (64 * n), F2 + c * 2 ^ (64 * n),
        F3 + d * 2 ^ (64 * n), ok') (a, b, c, d) ∧
      ∀ q, HasLane (n, F0, F1, F2, F3, ok) q →
        HasLane (n + 1, F0 + a * 2 ^ (64 * n), F1 + b * 2 ^ (64 * n), F2 + c * 2 ^ (64 * n),
          F3 + d * 2 ^ (64 * n), ok') q := by
  obtain ⟨b0, b1, b2, b3, hdom⟩ := h
  obtain ⟨f0, f1, f2, f3⟩ := hD hq
  refine ⟨⟨append_lt _ _ _ b0 f0, append_lt _ _ _ b1 f1, append_lt _ _ _ b2 f2, append_lt _ _ _ b3 f3, ?_⟩, ?_, ?_⟩
  · intro l hl
    dsimp only at hl ⊢
    rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2, lane_append _ _ _ _ b3 f3]
    by_cases hln : l < n
    · simp only [hln, ite_true]
      exact hdom l hln
    · have hle : l = n := by omega
      simp [hle]
      exact hq
  · refine ⟨n, by dsimp only; omega, ?_⟩
    dsimp only
    rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2, lane_append _ _ _ _ b3 f3]
    simp
  · rintro q ⟨l, hl, h0, h1, h2, h3⟩
    dsimp only at hl h0 h1 h2 h3
    refine ⟨l, by dsimp only; omega, ?_⟩
    dsimp only
    rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2, lane_append _ _ _ _ b3 f3]
    simp only [hl, ite_true]
    exact ⟨h0, h1, h2, h3⟩

theorem fold_lanes {D : ℕ → ℕ → ℕ → ℕ → Prop} {α : Type} (F : WSt → α → WSt) (f : α → ℕ × ℕ × ℕ × ℕ)
    (hF : ∀ s x, (F s x).2.2.2.2.2 = true → s.2.2.2.2.2 = true ∧
      (LanesOK D s → LanesOK D (F s x) ∧ HasLane (F s x) (f x) ∧ ∀ q, HasLane s q → HasLane (F s x) q)) :
    ∀ (L : List α) (s : WSt), (L.foldl F s).2.2.2.2.2 = true → s.2.2.2.2.2 = true ∧
      (LanesOK D s → LanesOK D (L.foldl F s) ∧ (∀ x ∈ L, HasLane (L.foldl F s) (f x)) ∧
        ∀ q, HasLane s q → HasLane (L.foldl F s) q) := by
  intro L
  induction L with
  | nil => intro s h; exact ⟨h, fun hs => ⟨hs, fun x hx => absurd hx (by simp), fun q hq => hq⟩⟩
  | cons x L ih =>
    intro s h
    rw [List.foldl_cons] at h ⊢
    obtain ⟨h1, h2⟩ := ih (F s x) h
    obtain ⟨h3, h4⟩ := hF s x h1
    refine ⟨h3, fun hs => ?_⟩
    obtain ⟨a1, a2, a3⟩ := h4 hs
    obtain ⟨b1, b2, b3⟩ := h2 a1
    refine ⟨b1, ?_, fun q hq => b3 q (a3 q hq)⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact b3 _ a2
    · exact b2 y hy

theorem addW_eq (n F0 F1 F2 F3 : ℕ) (ok : Bool) (a b c d : ℕ) :
    addW (n, F0, F1, F2, F3, ok) a b c d =
      (n + 1, F0 + a * 2 ^ (64 * n), F1 + b * 2 ^ (64 * n), F2 + c * 2 ^ (64 * n), F3 + d * 2 ^ (64 * n),
        ok && inDomBW a b c d) := by
  show (Nat.add n 1, Nat.add F0 (Nat.shiftLeft a (Nat.shiftLeft n 6)), Nat.add F1 (Nat.shiftLeft b (Nat.shiftLeft n 6)),
    Nat.add F2 (Nat.shiftLeft c (Nat.shiftLeft n 6)), Nat.add F3 (Nat.shiftLeft d (Nat.shiftLeft n 6)),
    ok && inDomBWK a b c d) = _
  rw [Walk.shl6, inDomBWK_eq]
  simp only [shl_eq]
  rfl

theorem addWS_eq (n F0 F1 F2 F3 : ℕ) (ok : Bool) (a b c d : ℕ) :
    addWS (n, F0, F1, F2, F3, ok) a b c d =
      (n + 1, F0 + a * 2 ^ (64 * n), F1 + b * 2 ^ (64 * n), F2 + c * 2 ^ (64 * n), F3 + d * 2 ^ (64 * n),
        ok && inDomBWS a b c d) := by
  show (Nat.add n 1, Nat.add F0 (Nat.shiftLeft a (Nat.shiftLeft n 6)), Nat.add F1 (Nat.shiftLeft b (Nat.shiftLeft n 6)),
    Nat.add F2 (Nat.shiftLeft c (Nat.shiftLeft n 6)), Nat.add F3 (Nat.shiftLeft d (Nat.shiftLeft n 6)),
    ok && inDomBWS a b c d) = _
  rw [Walk.shl6]
  simp only [shl_eq]
  rfl

theorem addW_step (a b c d : ℕ) (s : WSt) :
    (addW s a b c d).2.2.2.2.2 = true → s.2.2.2.2.2 = true ∧
      (LanesOK InDomW s → LanesOK InDomW (addW s a b c d) ∧ HasLane (addW s a b c d) (a, b, c, d) ∧
        ∀ q, HasLane s q → HasLane (addW s a b c d) q) := by
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := s
  rw [addW_eq]
  intro h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, fun hs => lanes_append (fun hq => ⟨hq.1, hq.2.1, hq.2.2.1, lt_trans hq.2.2.2.1 (by norm_num)⟩) hs
    (inDomBW_sound h.2)⟩

theorem addWS_step (a b c d : ℕ) (s : WSt) :
    (addWS s a b c d).2.2.2.2.2 = true → s.2.2.2.2.2 = true ∧
      (LanesOK InDomWS s → LanesOK InDomWS (addWS s a b c d) ∧ HasLane (addWS s a b c d) (a, b, c, d) ∧
        ∀ q, HasLane s q → HasLane (addWS s a b c d) q) := by
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := s
  rw [addWS_eq]
  intro h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, fun hs => lanes_append (fun hq => ⟨hq.1, hq.2.1, hq.2.2.1, lt_trans hq.2.2.2 (by norm_num)⟩) hs
    (inDomBWS_sound h.2)⟩

def PInvW (hi : Bool) (s : WSt) (tr : List Ev) : Prop :=
  s.2.2.2.2.2 = true → LanesOK InDomW s ∧ ∀ e ∈ tr, ∃ g box it, e = .record g box it ∧ okW hi g box it = true ∧
    ∀ x ∈ subsW (wKr it) (wKd it) (lf box (wD it)) (lf box (wRi it)),
      HasLane s (x.1, x.2, wF2 hi box it, wF3 hi box it)

theorem pinvW_step {hi : Bool} {prog : Prog} {s : WSt} {tr : List Ev}
    (h : PInvW hi s tr) (e : Ev) : PInvW hi ((progCheckerW hi prog).step e s) (tr ++ [e]) := by
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := s
  cases e with
  | kill g box it =>
    intro hf
    have h' : false = true := hf
    cases h'
  | record g box it =>
    show PInvW hi (List.foldl (fun (s : WSt) (x : ℕ × ℕ) => addW s x.1 x.2 (wF2 hi box it) (wF3 hi box it))
        (n, F0, F1, F2, F3, ok && okWK hi g box it)
        (subsW (wKr it) (wKd it) (lf box (wD it)) (lf box (wRi it)))) (tr ++ [Ev.record g box it])
    rw [okWK_eq]
    intro hf
    have hf' : (List.foldl (fun (s : WSt) (x : ℕ × ℕ) => addW s x.1 x.2 (wF2 hi box it) (wF3 hi box it))
        (n, F0, F1, F2, F3, ok && okW hi g box it)
        (subsW (wKr it) (wKd it) (lf box (wD it)) (lf box (wRi it)))).2.2.2.2.2 = true := hf
    obtain ⟨hok0, hrest⟩ := fold_lanes (D := InDomW)
      (fun (s : WSt) (x : ℕ × ℕ) => addW s x.1 x.2 (wF2 hi box it) (wF3 hi box it))
      (fun x => (x.1, x.2, wF2 hi box it, wF3 hi box it)) (fun s x => addW_step _ _ _ _ s)
      (subsW (wKr it) (wKd it) (lf box (wD it)) (lf box (wRi it))) (n, F0, F1, F2, F3, ok && okW hi g box it) hf'
    have hok1 : (ok && okW hi g box it) = true := hok0
    rw [Bool.and_eq_true] at hok1
    obtain ⟨rfl, hok⟩ := hok1
    obtain ⟨hlanes, hev⟩ := h rfl
    obtain ⟨l1, l2, l3⟩ := hrest hlanes
    refine ⟨l1, fun e' he' => ?_⟩
    rcases List.mem_append.mp he' with he' | he'
    · obtain ⟨g', box', it', rfl, hok', hs⟩ := hev e' he'
      exact ⟨g', box', it', rfl, hok', fun x hx => l3 _ (hs x hx)⟩
    · rw [List.mem_singleton] at he'
      subst he'
      exact ⟨g, box, it, rfl, hok, fun x hx => l2 x hx⟩

theorem pinvW_fold {hi : Bool} {prog : Prog} (tr : List Ev) :
    ∀ (s : WSt) (tr0 : List Ev), PInvW hi s tr0 →
      PInvW hi (tr.foldl (fun s e => (progCheckerW hi prog).step e s) s) (tr0 ++ tr) := by
  induction tr with
  | nil => intro s tr0 h; rw [List.append_nil]; exact h
  | cons e tr ih =>
    intro s tr0 h
    have := ih _ _ (pinvW_step (prog := prog) h e)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

theorem progCheckerW_sound {hi : Bool} {prog : Prog} (hp : ProgOKW hi prog) :
    (progCheckerW hi prog).Sound fun _ => True := by
  intro tr hs _ hfin e he
  have hinv : PInvW hi ((progCheckerW hi prog).run tr) tr := by
    have h0 : PInvW hi (0, 0, 0, 0, 0, true) [] := by
      intro _
      exact ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, fun l hl => absurd hl (Nat.not_lt_zero _)⟩,
        fun e he => absurd he (by simp)⟩
    have := pinvW_fold (prog := prog) tr _ _ h0
    rw [List.nil_append] at this
    exact this
  generalize (progCheckerW hi prog).run tr = S at hinv hfin
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := S
  have hf : (ok && Nat.beq (prog (oN n) F0 F1 F2 F3 hs) (oN n)) = true := hfin
  rw [Bool.and_eq_true] at hf
  obtain ⟨rfl, hv⟩ := hf
  obtain ⟨⟨-, -, -, -, hdom⟩, hev⟩ := hinv rfl
  obtain ⟨g, box, it, rfl, hok, hsub⟩ := hev e he
  refine recOK_of_wheel hok (laneClaimW_of_subs hi (wKr it) (wKd it) _ _ _ _ fun x hx => ?_)
  obtain ⟨l, hl, h0, h1, h2, h3⟩ := hsub x hx
  have hc := hp n F0 F1 F2 F3 hs (oN n) hdom hv l hl (lane_oN n l hl)
  rw [h0, h1, h2, h3] at hc
  exact hc

def PInvWS (s : WSt) (tr : List Ev) : Prop :=
  s.2.2.2.2.2 = true → LanesOK InDomWS s ∧ ∀ e ∈ tr, ∃ g box it, e = .kill g box it ∧ okWS g box it = true ∧
    ∀ j < 6, HasLane s (lf box (wD it), lf box (wRj it j), lf box (wRj it ((j + 1) % 6)), wB it j)

theorem pinvWS_step {prog : Prog} {s : WSt} {tr : List Ev}
    (h : PInvWS s tr) (e : Ev) : PInvWS ((progCheckerWS prog).step e s) (tr ++ [e]) := by
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := s
  cases e with
  | record g box it =>
    intro hf
    have h' : false = true := hf
    cases h'
  | kill g box it =>
    show PInvWS (List.foldl (fun (s : WSt) (j : ℕ) => addWS s (lf box (wD it)) (lf box (wRj it j))
        (lf box (wRj it (Nat.mod (Nat.add j 1) 6))) (wB it j))
        (n, F0, F1, F2, F3, ok && okWSK g box it) [0, 1, 2, 3, 4, 5]) (tr ++ [Ev.kill g box it])
    rw [okWSK_eq]
    intro hf
    have hf' : (List.foldl (fun (s : WSt) (j : ℕ) => addWS s (lf box (wD it)) (lf box (wRj it j))
        (lf box (wRj it (Nat.mod (Nat.add j 1) 6))) (wB it j))
        (n, F0, F1, F2, F3, ok && okWS g box it) [0, 1, 2, 3, 4, 5]).2.2.2.2.2 = true := hf
    obtain ⟨hok0, hrest⟩ := fold_lanes (D := InDomWS)
      (fun (s : WSt) (j : ℕ) => addWS s (lf box (wD it)) (lf box (wRj it j))
        (lf box (wRj it (Nat.mod (Nat.add j 1) 6))) (wB it j))
      (fun j => (lf box (wD it), lf box (wRj it j), lf box (wRj it (Nat.mod (Nat.add j 1) 6)), wB it j))
      (fun s j => addWS_step _ _ _ _ s) [0, 1, 2, 3, 4, 5] (n, F0, F1, F2, F3, ok && okWS g box it) hf'
    have hok1 : (ok && okWS g box it) = true := hok0
    rw [Bool.and_eq_true] at hok1
    obtain ⟨rfl, hok⟩ := hok1
    obtain ⟨hlanes, hev⟩ := h rfl
    obtain ⟨l1, l2, l3⟩ := hrest hlanes
    refine ⟨l1, fun e' he' => ?_⟩
    rcases List.mem_append.mp he' with he' | he'
    · obtain ⟨g', box', it', rfl, hok', hs⟩ := hev e' he'
      exact ⟨g', box', it', rfl, hok', fun j hj => l3 _ (hs j hj)⟩
    · rw [List.mem_singleton] at he'
      subst he'
      exact ⟨g, box, it, rfl, hok, fun j hj => l2 j (by simp; omega)⟩

theorem pinvWS_fold {prog : Prog} (tr : List Ev) :
    ∀ (s : WSt) (tr0 : List Ev), PInvWS s tr0 →
      PInvWS (tr.foldl (fun s e => (progCheckerWS prog).step e s) s) (tr0 ++ tr) := by
  induction tr with
  | nil => intro s tr0 h; rw [List.append_nil]; exact h
  | cons e tr ih =>
    intro s tr0 h
    have := ih _ _ (pinvWS_step (prog := prog) h e)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

theorem progCheckerWS_sound {prog : Prog} (hp : ProgOKWS prog) : (progCheckerWS prog).Sound fun _ => True := by
  intro tr hs _ hfin e he
  have hinv : PInvWS ((progCheckerWS prog).run tr) tr := by
    have h0 : PInvWS (0, 0, 0, 0, 0, true) [] := by
      intro _
      exact ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, fun l hl => absurd hl (Nat.not_lt_zero _)⟩,
        fun e he => absurd he (by simp)⟩
    have := pinvWS_fold (prog := prog) tr _ _ h0
    rw [List.nil_append] at this
    exact this
  generalize (progCheckerWS prog).run tr = S at hinv hfin
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := S
  have hf : (ok && Nat.beq (prog (oN n) F0 F1 F2 F3 hs) (oN n)) = true := hfin
  rw [Bool.and_eq_true] at hf
  obtain ⟨rfl, hv⟩ := hf
  obtain ⟨⟨-, -, -, -, hdom⟩, hev⟩ := hinv rfl
  obtain ⟨g, box, it, rfl, hok, hsub⟩ := hev e he
  refine killOK_of_wsum hok fun j hj => ?_
  obtain ⟨l, hl, h0, h1, h2, h3⟩ := hsub j hj
  dsimp only at hl h0 h1 h2 h3
  have hc := hp n F0 F1 F2 F3 hs (oN n) hdom hv l hl (lane_oN n l hl)
  rw [h0, h1, h2, h3] at hc
  exact hc

theorem exactW_fold (tr : List Ev) : ∀ (s : Bool) (tr0 : List Ev),
    (s = true → ∀ e ∈ tr0, ∃ g box it, e = .record g box it ∧ okWX g box it = true) →
    tr.foldl (fun s e => exactCheckerW.step e s) s = true →
      ∀ e ∈ tr0 ++ tr, ∃ g box it, e = .record g box it ∧ okWX g box it = true := by
  induction tr with
  | nil => intro s tr0 h hf; rw [List.append_nil]; exact h hf
  | cons e tr ih =>
    intro s tr0 h hf
    replace hf : List.foldl (fun s e => exactCheckerW.step e s) (exactCheckerW.step e s) tr = true := hf
    have := ih _ (tr0 ++ [e]) ?_ hf
    · rwa [List.append_assoc, List.singleton_append] at this
    · intro hs e' he'
      cases e with
      | kill g box it =>
        have h' : false = true := hs
        cases h'
      | record g box it =>
        have hs' : (s && okWXK g box it) = true := hs
        rw [okWXK_eq] at hs'
        rw [Bool.and_eq_true] at hs'
        rcases List.mem_append.mp he' with he' | he'
        · exact h hs'.1 e' he'
        · rw [List.mem_singleton] at he'
          exact ⟨g, box, it, he', hs'.2⟩

theorem exactCheckerW_sound : exactCheckerW.Sound fun _ => True := by
  intro tr _ _ hfin e he
  obtain ⟨g, box, it, rfl, hok⟩ :=
    exactW_fold tr true [] (fun _ e he => absurd he (by simp)) hfin e (by rw [List.nil_append]; exact he)
  exact recOK_of_wheelX hok

def wheelSub (pL pH pS : Prog) (i : ℕ) : Checker :=
  @Bool.rec (fun _ => Checker)
    (@Bool.rec (fun _ => Checker) exactCheckerW (progCheckerWS pS) (Nat.beq i 2))
    (@Bool.rec (fun _ => Checker) (progCheckerW true pH) (progCheckerW false pL) (Nat.beq i 0)) (Nat.blt i 2)

def wheelChecker (pL pH pS : Prog) : Checker := btree (wheelSub pL pH pS) wRoute 2 0

theorem wheelChecker_sound {pL pH pS : Prog} (hL : ProgOKW false pL) (hH : ProgOKW true pH) (hS : ProgOKWS pS) :
    (wheelChecker pL pH pS).Sound (kindIs 6) := by
  refine btree_sound _ wRoute (fun i => ?_) 2 0 _
  unfold wheelSub
  cases Nat.blt i 2 <;> cases Nat.beq i 0 <;> cases Nat.beq i 2
  all_goals first
    | exact progCheckerW_sound hL
    | exact progCheckerW_sound hH
    | exact progCheckerWS_sound hS
    | exact exactCheckerW_sound

noncomputable def wheelProgL : Prog := fun O F0 F1 F2 F3 hs => progWL O F0 F1 F2 F3 (hs.getD 0 0)
noncomputable def wheelProgH : Prog := fun O F0 F1 F2 F3 hs => progWH O F0 F1 F2 F3 (hs.getD 0 0)
noncomputable def wheelProgS : Prog := fun O F0 F1 F2 F3 hs => progWSH O F0 F1 F2 F3 (hs.getD 0 0)

theorem wheelProgL_ok : ProgOKW false wheelProgL :=
  fun n F0 F1 F2 F3 _ v hD hv l hl h1 => progWL_decl n F0 F1 F2 F3 _ v hD hv l hl h1

theorem wheelProgH_ok : ProgOKW true wheelProgH :=
  fun n F0 F1 F2 F3 _ v hD hv l hl h1 => progWH_decl n F0 F1 F2 F3 _ v hD hv l hl h1

theorem wheelProgS_ok : ProgOKWS wheelProgS :=
  fun n F0 F1 F2 F3 _ v hD hv l hl h1 => progWSH_decl n F0 F1 F2 F3 _ v hD hv l hl h1

noncomputable def wheelQ : Checker := wheelChecker wheelProgL wheelProgH wheelProgS

theorem wheelQ_sound : wheelQ.Sound (kindIs 6) := wheelChecker_sound wheelProgL_ok wheelProgH_ok wheelProgS_ok

end Tammes15.D3Trig
