import Tammes15.D3Trig.HexSpec

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel Tammes15.D3Kernel.Pent Tammes15.D3Kernel.KForm

def zEnd (hi : Bool) (box zv : ℕ) : ℕ :=
  @Bool.rec (fun _ => ℕ) (kfl (bk box (Nat.shiftLeft zv 1))) (kce (bk box (Nat.add (Nat.shiftLeft zv 1) 1))) hi

def claimH (hi : Bool) (box zv it : ℕ) : ℕ := Nat.add (claim it) (Nat.shiftLeft (zEnd hi box zv) (nat_lit 32))

def inDomBH (F0 F1 F2 F3 : ℕ) : Bool :=
  Nat.blt F3 18446744073709551616 && inDomB F0 F1 F2 (F3 % 4294967296) &&
    Nat.ble 18454938 (F3 / 4294967296 % 4294967296) && Nat.ble (F3 / 4294967296 % 4294967296) 53687091

def okH (hi : Bool) (g box it : ℕ) : Bool :=
  let c := Ctx.code g
  let e := fk it 75 127
  let t := fk it 64 127
  let o := Nat.shiftRight t 1
  let xv := fk it 82 63
  let yv := fk it 88 63
  let zv := fk it 94 63
  let dv := fk it 100 63
  let nv := Ctx.nv g
  Nat.blt e c.D && Nat.beq (c.period e) 6 &&
  Nat.beq (Nat.land t 1) (@Bool.rec (fun _ => ℕ) 0 1 hi) &&
  Nat.blt dv nv && Nat.blt xv nv && Nat.blt yv nv && Nat.blt zv nv && Nat.blt o nv &&
  Nat.beq (Ctx.mean g dv) 1 &&
  Nat.beq (Ctx.mean g xv) (2 + c.faceIter e 1) &&
  Nat.beq (Ctx.mean g yv) (2 + c.faceIter e 5) &&
  Nat.beq (Ctx.mean g zv) (2 + c.faceIter e 3) &&
  Nat.beq (Ctx.mean g o) (2 + c.faceIter e 0) &&
  kok (bk box (2 * dv)) && kok (bk box (2 * dv + 1)) && kok (bk box (2 * xv)) && kok (bk box (2 * xv + 1)) &&
  kok (bk box (2 * yv)) && kok (bk box (2 * yv + 1)) &&
  @Bool.rec (fun _ => Bool) (kok (bk box (2 * zv))) (kok (bk box (2 * zv + 1))) hi &&
  kok (Nat.land it 18446744073709551615) &&
  inDomBH (lf box dv) (lf box xv) (lf box yv) (claimH hi box zv it)

def inDomBHK (F0 F1 F2 F3 : ℕ) : Bool :=
  Nat.blt F3 18446744073709551616 && inDomBK F0 F1 F2 (Nat.land F3 4294967295) &&
    Nat.ble 18454938 (Nat.land (Nat.shiftRight F3 32) 4294967295) &&
    Nat.ble (Nat.land (Nat.shiftRight F3 32) 4294967295) 53687091

def okHK (hi : Bool) (g box it : ℕ) : Bool :=
  let face := Nat.shiftRight g 64
  let e := fk it 75 127
  let t := fk it 64 127
  let o := Nat.shiftRight t 1
  let xv := fk it 82 63
  let yv := fk it 88 63
  let zv := fk it 94 63
  let dv := fk it 100 63
  let nv := nvCK g
  Nat.blt e (DK g) && Nat.beq (periodK face e) 6 &&
  Nat.beq (Nat.land t 1) (@Bool.rec (fun _ => ℕ) 0 1 hi) &&
  Nat.blt dv nv && Nat.blt xv nv && Nat.blt yv nv && Nat.blt zv nv && Nat.blt o nv &&
  Nat.beq (meanK g dv) 1 &&
  Nat.beq (meanK g xv) (Nat.add 2 (iterK face e 1)) &&
  Nat.beq (meanK g yv) (Nat.add 2 (iterK face e 5)) &&
  Nat.beq (meanK g zv) (Nat.add 2 (iterK face e 3)) &&
  Nat.beq (meanK g o) (Nat.add 2 (iterK face e 0)) &&
  kokK (bk box (Nat.shiftLeft dv 1)) && kokK (bk box (Nat.add (Nat.shiftLeft dv 1) 1)) &&
  kokK (bk box (Nat.shiftLeft xv 1)) && kokK (bk box (Nat.add (Nat.shiftLeft xv 1) 1)) &&
  kokK (bk box (Nat.shiftLeft yv 1)) && kokK (bk box (Nat.add (Nat.shiftLeft yv 1) 1)) &&
  @Bool.rec (fun _ => Bool) (kokK (bk box (Nat.shiftLeft zv 1))) (kokK (bk box (Nat.add (Nat.shiftLeft zv 1) 1))) hi &&
  kokK (Nat.land it 18446744073709551615) &&
  inDomBHK (lf box dv) (lf box xv) (lf box yv) (claimH hi box zv it)

theorem inDomBHK_eq (F0 F1 F2 F3 : ℕ) : inDomBHK F0 F1 F2 F3 = inDomBH F0 F1 F2 F3 := by
  have hland : Nat.land F3 4294967295 = F3 % 4294967296 := by
    show F3 &&& 4294967295 = F3 % 4294967296
    rw [show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hshift : Nat.land (Nat.shiftRight F3 32) 4294967295 = F3 / 4294967296 % 4294967296 := by
    show (F3 >>> 32) &&& 4294967295 = F3 / 4294967296 % 4294967296
    rw [show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow]
  unfold inDomBHK inDomBH
  rw [inDomBK_eq, hland, hshift]

theorem okHK_eq (hi : Bool) (g box it : ℕ) : okHK hi g box it = okH hi g box it := by
  have he : fk it 75 127 < 256 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hs : ∀ v, Nat.shiftLeft v 1 = 2 * v := fun v => by
    show v <<< 1 = 2 * v
    rw [Nat.shiftLeft_eq]; ring
  have hD : (Ctx.code g).D = Ctx.D g := rfl
  unfold okHK okH
  simp only [nvCK_eq, DK_eq, meanK_eq, periodK_eq g _ he, iterK_eq g _ _ he, inDomBHK_eq, kokK_eq, hs, hD,
    Nat.add_eq]

def ProgOKH (hi : Bool) (prog : Prog) : Prop :=
  ∀ (n F0 F1 F2 F3 : ℕ) (hs : List ℕ) (v : ℕ),
    (∀ i < n, InDomH (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) →
      Nat.beq (prog (oN n) F0 F1 F2 F3 hs) v = true → ∀ l < n, lane v l = 1 →
        LaneClaimH hi (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)

def progCheckerH (hi : Bool) (prog : Prog) : Checker where
  σ := ℕ × ℕ × ℕ × ℕ × ℕ × Bool
  H := List ℕ
  init := (0, 0, 0, 0, 0, true)
  onRec g box it s :=
    let sh := Nat.shiftLeft s.1 (nat_lit 6)
    (Nat.add s.1 1,
      Nat.add s.2.1 (Nat.shiftLeft (lf box (fk it 100 63)) sh),
      Nat.add s.2.2.1 (Nat.shiftLeft (lf box (fk it 82 63)) sh),
      Nat.add s.2.2.2.1 (Nat.shiftLeft (lf box (fk it 88 63)) sh),
      Nat.add s.2.2.2.2.1 (Nat.shiftLeft (claimH hi box (fk it 94 63) it) sh),
      s.2.2.2.2.2 && okH hi g box it)
  onKill _ _ _ s := (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, false)
  fin s hs := s.2.2.2.2.2 && Nat.beq (prog (oN s.1) s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 hs) (oN s.1)
  frc s k := @Bool.rec (fun _ => List ℕ) (k s) (k s)
    (Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0)
  frc_eq s k := by
    cases Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0 <;> rfl

def hIdx (it : ℕ) : ℕ := Nat.add (Nat.shiftLeft (fk it 106 3) 1) (fk it 64 1)

def hexChecker (progs : ℕ → Prog) : Checker :=
  btree (fun i => if i < 6 then progCheckerH (hiOf i) (progs i) else Checker.none) hIdx 3 0

theorem zEnd_lo (box zv : ℕ) : zEnd false box zv = kfl (bnd box (2 * zv)) := by
  have h2 : Nat.shiftLeft zv 1 = 2 * zv := by rw [shl_eq]; ring
  show kfl (bk box (Nat.shiftLeft zv 1)) = _
  rw [bk_eq, h2]

theorem zEnd_hi (box zv : ℕ) : zEnd true box zv = kce (bnd box (2 * zv + 1)) := by
  have h2 : Nat.shiftLeft zv 1 = 2 * zv := by rw [shl_eq]; ring
  show kce (bk box (Nat.add (Nat.shiftLeft zv 1) 1)) = _
  rw [bk_eq, h2]

theorem claimH_flds {hi : Bool} {box zv it : ℕ} (hc : claim it < 2 ^ 32) (hz : zEnd hi box zv < 2 ^ 32) :
    fld (claimH hi box zv it) 0 = fld (claim it) 0 ∧
      fld (claimH hi box zv it) 32 = (zEnd hi box zv : ℝ) / 2 ^ 24 := by
  have h := fld_pair _ _ hc hz
  refine ⟨?_, h.2⟩
  rw [fld0_of_lt hc]
  exact h.1

theorem claim_lt {it : ℕ} (h : kok (Nat.land it 18446744073709551615) = true) : claim it < 2 ^ 32 := by
  unfold claim
  cases Nat.beq (fk it 64 1) 1
  · exact lt_trans (kce_lt h).1 (by norm_num)
  · exact lt_trans (kce_lt h).2 (by norm_num)

theorem inDomBH_sound {F0 F1 F2 F3 : ℕ} (h : inDomBH F0 F1 F2 F3 = true) : InDomH F0 F1 F2 F3 := by
  unfold inDomBH at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨h3, hp⟩, hlo⟩, hhi⟩ := h
  obtain ⟨f0, f1, f2, -, a0, a1, a2, a3, a4, a5⟩ := inDomB_sound hp
  have e : F3 / 2 ^ 32 % 2 ^ 32 = F3 / 4294967296 % 4294967296 := by norm_num
  have hlo' : (18454938 : ℝ) ≤ ((F3 / 2 ^ 32 % 2 ^ 32 : ℕ) : ℝ) := by rw [e]; exact_mod_cast hlo
  have hhi' : ((F3 / 2 ^ 32 % 2 ^ 32 : ℕ) : ℝ) ≤ 53687091 := by rw [e]; exact_mod_cast hhi
  refine ⟨f0, f1, f2, h3, a0, a1, a2, a3, a4, a5, ?_, ?_⟩
  · unfold fld
    rw [le_div_iff₀ (by norm_num)]
    linarith
  · unfold fld
    rw [div_le_iff₀ (by norm_num)]
    linarith

theorem recOK_of_hex {hi : Bool} {g box it : ℕ} (hok : okH hi g box it = true)
    (hc : LaneClaimH hi (lf box (fk it 100 63)) (lf box (fk it 82 63)) (lf box (fk it 88 63))
      (claimH hi box (fk it 94 63) it)) :
    RecOK g box it := by
  have hok' := hok
  simp only [okH, fk_bits7, fk_bits6, bk_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    and_assoc] at hok'
  obtain ⟨he, hper, hside, hdv, hxv, hyv, hzv, -, mdv, mxv, myv, mzv, mo, k1, k2, k3, k4, k5, k6, kz, knew, hdom⟩ :=
    hok'
  rw [fk_bits6, fk_bits6, fk_bits6, fk_bits6] at hc
  have hoe : Nat.shiftRight (bits it 64 7) 1 = bits it 64 7 / 2 := Nat.shiftRight_eq_div_pow _ _
  rw [hoe] at mo
  have hclt : claim it < 2 ^ 32 := claim_lt knew
  have hzlt : zEnd hi box (bits it 94 6) < 2 ^ 32 := by
    cases hi
    · rw [zEnd_lo]; exact lt_trans (kce_lt kz).2 (by norm_num)
    · rw [zEnd_hi]; exact lt_trans (kce_lt kz).1 (by norm_num)
  have hF := claimH_flds (box := box) (zv := bits it 94 6) hclt hzlt
  have hD := inDomBH_sound hdom
  intro S hS

  set e' : S.P.G.Dart := S.lab.symm ⟨bits it 75 7, he⟩ with he'
  have hlab : (S.lab e' : ℕ) = bits it 75 7 := by simp [he']
  have hfs : fsize S.P e' = 6 :=
    D3lp.fsize_of_period S.hm e' ((congrArg (Ctx.code g).period hlab).trans hper) (by norm_num)
  have hiter : ∀ j, (Ctx.code g).faceIter (bits it 75 7) j = S.lab ((S.P.R.face ^ j) e') := by
    intro j; rw [← hlab]; exact D3lp.faceIter_lab S.hm e' j
  have hcorner : ∀ v j, Ctx.mean g v = 2 + (Ctx.code g).faceIter (bits it 75 7) j → S.x v = S.A.fc e' j := by
    intro v j hm
    rw [hiter] at hm
    exact val_corner S.lab S.A _ hm
  have hd : fld (lf box (bits it 100 6)) 0 ≤ S.A.d ∧ S.A.d ≤ fld (lf box (bits it 100 6)) 32 := by
    rw [← val_d S.lab S.A mdv]; exact lf_bounds k1 k2 (hS _ hdv)
  have hX := lf_bounds k3 k4 (hS _ hxv)
  have hY := lf_bounds k5 k6 (hS _ hyv)

  have hx1 : S.x (bits it 82 6) = S.A.fc e' 1 := hcorner _ 1 mxv
  have hy5 : S.x (bits it 88 6) = S.A.fc e' 5 := hcorner _ 5 myv
  have hz3 : S.x (bits it 94 6) = S.A.fc e' 3 := hcorner _ 3 mzv
  have ho0 : S.x (bits it 64 7 / 2) = S.A.fc e' 0 := hcorner _ 0 mo
  have hrel : S.x (bits it 64 7 / 2) =
      hexOut S.A.d (S.x (bits it 82 6)) (S.x (bits it 88 6)) (S.x (bits it 94 6)) := by
    rw [ho0, hx1, hy5, hz3]; exact hex_fc S.hR hfs
  have hxpi : S.x (bits it 82 6) < Real.pi := by rw [hx1]; exact (S.hR.corner_mem _).2
  have hypi : S.x (bits it 88 6) < Real.pi := by rw [hy5]; exact (S.hR.corner_mem _).2
  have hzpi : S.x (bits it 94 6) < Real.pi := by rw [hz3]; exact (S.hR.corner_mem _).2
  have hdd : 0 < S.A.d ∧ S.A.d < Real.pi / 2 := by
    have h09 : (0.9 : ℝ) ≤ fld (lf box (bits it 100 6)) 0 := hD.2.2.2.2.1
    have h1 : fld (lf box (bits it 100 6)) 32 ≤ 1 := hD.2.2.2.2.2.1
    constructor <;> linarith [Real.pi_gt_three]
  have hz0 : 0 < S.x (bits it 94 6) := by
    rw [hz3]
    have h1 := (S.hR.corner_mem ((S.P.R.face ^ 3) e')).1
    have h2 := (alpha_bounds _ hdd).1
    have h3 := Real.pi_pos
    exact lt_of_lt_of_le (by linarith) h1

  have hzt : if hi then 0 < S.x (bits it 94 6) ∧ S.x (bits it 94 6) ≤ fld (claimH hi box (bits it 94 6) it) 32
      else fld (claimH hi box (bits it 94 6) it) 32 ≤ S.x (bits it 94 6) := by
    rw [hF.2]
    cases hi
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [zEnd_lo]
      exact (kfl_le kz).trans (hS _ hzv).1
    · simp only [↓reduceIte]
      rw [zEnd_hi]
      exact ⟨hz0, (hS _ hzv).2.trans (le_kce kz)⟩
  have hL := hc S.A.d (S.x (bits it 82 6)) (S.x (bits it 88 6)) (S.x (bits it 94 6)) hd.1 hd.2 hX.1 hX.2 hY.1
    hY.2 hxpi hypi hzpi hzt

  have hcl : Claim hi (fld (claim it) 0) (S.x (bits it 64 7 / 2)) := by
    rw [hrel, ← hF.1]
    exact hL

  have hb1 : bits it 64 1 = bits it 64 7 % 2 := by
    unfold bits; rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 7)]; rfl
  have hside' : bits it 64 7 % 2 = @Bool.rec (fun _ => ℕ) 0 1 hi := by
    rw [← hside]; exact (Nat.and_one_is_mod _).symm
  rw [Walk.kf_new] at knew
  refine boxMem_set (bits_lt it 0 64) hS (fun h0 => ?_) (fun h1 => ?_)
  · have h0' : bits it 64 7 % 2 = 0 := h0
    cases hi
    · have hcl' : (claim it : ℝ) / 2 ^ 24 ≤ S.x (bits it 64 7 / 2) := by
        rw [← fld0_of_lt hclt]; exact hcl
      rw [claim_lo (hb1.trans h0')] at hcl'
      exact (le_kce knew).trans hcl'
    · have h1' : bits it 64 7 % 2 = 1 := hside'
      omega
  · have h1' : bits it 64 7 % 2 = 1 := h1
    cases hi
    · have h0' : bits it 64 7 % 2 = 0 := hside'
      omega
    · have hcl' : S.x (bits it 64 7 / 2) ≤ (claim it : ℝ) / 2 ^ 24 := by
        rw [← fld0_of_lt hclt]; exact hcl
      rw [claim_hi (hb1.trans h1')] at hcl'
      exact hcl'.trans (kfl_le knew)

def PInvH (hi : Bool) (s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool) (tr : List Ev) : Prop :=
  s.2.2.2.2.2 = true →
    s.2.1 < 2 ^ (64 * s.1) ∧ s.2.2.1 < 2 ^ (64 * s.1) ∧ s.2.2.2.1 < 2 ^ (64 * s.1) ∧
      s.2.2.2.2.1 < 2 ^ (64 * s.1) ∧
      (∀ l < s.1, InDomH (lane s.2.1 l) (lane s.2.2.1 l) (lane s.2.2.2.1 l) (lane s.2.2.2.2.1 l)) ∧
      ∀ e ∈ tr, ∃ g box it, e = .record g box it ∧ okH hi g box it = true ∧
        ∃ l < s.1, lane s.2.1 l = lf box (fk it 100 63) ∧ lane s.2.2.1 l = lf box (fk it 82 63) ∧
          lane s.2.2.2.1 l = lf box (fk it 88 63) ∧ lane s.2.2.2.2.1 l = claimH hi box (fk it 94 63) it

theorem okH_inDomBH {hi : Bool} {g box it : ℕ} (h : okH hi g box it = true) :
    inDomBH (lf box (fk it 100 63)) (lf box (fk it 82 63)) (lf box (fk it 88 63))
      (claimH hi box (fk it 94 63) it) = true := by
  unfold okH at h
  exact ((Bool.and_eq_true _ _).mp h).2

theorem progH_step_rec (hi : Bool) (prog : Prog) (n F0 F1 F2 F3 : ℕ) (ok : Bool) (g box it : ℕ) :
    (progCheckerH hi prog).step (.record g box it) (n, F0, F1, F2, F3, ok) =
      (n + 1, F0 + lf box (fk it 100 63) * 2 ^ (64 * n), F1 + lf box (fk it 82 63) * 2 ^ (64 * n),
        F2 + lf box (fk it 88 63) * 2 ^ (64 * n), F3 + claimH hi box (fk it 94 63) it * 2 ^ (64 * n),
        ok && okH hi g box it) := by
  show (Nat.add n 1, Nat.add F0 (Nat.shiftLeft (lf box (fk it 100 63)) (Nat.shiftLeft n 6)),
    Nat.add F1 (Nat.shiftLeft (lf box (fk it 82 63)) (Nat.shiftLeft n 6)),
    Nat.add F2 (Nat.shiftLeft (lf box (fk it 88 63)) (Nat.shiftLeft n 6)),
    Nat.add F3 (Nat.shiftLeft (claimH hi box (fk it 94 63) it) (Nat.shiftLeft n 6)), ok && okH hi g box it) = _
  rw [Walk.shl6]
  simp only [shl_eq]
  rfl

theorem pinvH_record {hi : Bool} {n F0 F1 F2 F3 : ℕ} {tr : List Ev} {g box it : ℕ}
    (h : PInvH hi (n, F0, F1, F2, F3, true) tr) (hok : okH hi g box it = true) :
    PInvH hi (n + 1, F0 + lf box (fk it 100 63) * 2 ^ (64 * n), F1 + lf box (fk it 82 63) * 2 ^ (64 * n),
      F2 + lf box (fk it 88 63) * 2 ^ (64 * n), F3 + claimH hi box (fk it 94 63) it * 2 ^ (64 * n), true)
      (tr ++ [.record g box it]) := by
  unfold PInvH at h ⊢
  dsimp only at h ⊢
  intro _
  obtain ⟨b0, b1, b2, b3, hdom, hev⟩ := h rfl
  have hD := inDomBH_sound (okH_inDomBH hok)
  have f0 := hD.1
  have f1 := hD.2.1
  have f2 := hD.2.2.1
  have f3 := hD.2.2.2.1
  refine ⟨append_lt _ _ _ b0 f0, append_lt _ _ _ b1 f1, append_lt _ _ _ b2 f2, append_lt _ _ _ b3 f3, ?_, ?_⟩
  · intro l hl
    rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2, lane_append _ _ _ _ b3 f3]
    by_cases hln : l < n
    · simp only [hln, ite_true]
      exact hdom l hln
    · have hle : l = n := by omega
      simp [hle]
      exact hD
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨g', box', it', rfl, hok', l, hl, h0, h1, h2, h3⟩ := hev e he
      refine ⟨g', box', it', rfl, hok', l, by omega, ?_⟩
      rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2,
        lane_append _ _ _ _ b3 f3]
      simp only [hl, ite_true]
      exact ⟨h0, h1, h2, h3⟩
    · rw [List.mem_singleton] at he
      subst he
      refine ⟨g, box, it, rfl, hok, n, by omega, ?_⟩
      rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2,
        lane_append _ _ _ _ b3 f3]
      simp

theorem pinvH_step {hi : Bool} {prog : Prog} {s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool} {tr : List Ev}
    (h : PInvH hi s tr) (e : Ev) : PInvH hi ((progCheckerH hi prog).step e s) (tr ++ [e]) := by
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := s
  cases e with
  | kill g box it =>
    intro hf
    have h' : false = true := hf
    cases h'
  | record g box it =>
    rw [progH_step_rec]
    unfold PInvH
    dsimp only
    intro hf
    rw [Bool.and_eq_true] at hf
    obtain ⟨rfl, hok⟩ := hf
    have := pinvH_record h hok
    unfold PInvH at this
    dsimp only at this
    exact this rfl

theorem pinvH_fold {hi : Bool} {prog : Prog} (tr : List Ev) :
    ∀ (s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool) (tr0 : List Ev), PInvH hi s tr0 →
      PInvH hi (tr.foldl (fun s e => (progCheckerH hi prog).step e s) s) (tr0 ++ tr) := by
  induction tr with
  | nil => intro s tr0 h; rw [List.append_nil]; exact h
  | cons e tr ih =>
    intro s tr0 h
    have := ih _ _ (pinvH_step (prog := prog) h e)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

theorem progCheckerH_sound {hi : Bool} {prog : Prog} (hp : ProgOKH hi prog) :
    (progCheckerH hi prog).Sound fun _ => True := by
  intro tr hs _ hfin e he
  have hinv : PInvH hi ((progCheckerH hi prog).run tr) tr := by
    have h0 : PInvH hi (0, 0, 0, 0, 0, true) [] := by
      intro _
      refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun l hl => absurd hl (Nat.not_lt_zero _),
        fun e he => absurd he (by simp)⟩
    have := pinvH_fold (prog := prog) tr _ _ h0
    rw [List.nil_append] at this
    exact this
  generalize (progCheckerH hi prog).run tr = S at hinv hfin
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := S
  have hf : (ok && Nat.beq (prog (oN n) F0 F1 F2 F3 hs) (oN n)) = true := hfin
  rw [Bool.and_eq_true] at hf
  obtain ⟨rfl, hv⟩ := hf
  unfold PInvH at hinv
  dsimp only at hinv
  obtain ⟨-, -, -, -, hdom, hev⟩ := hinv rfl
  obtain ⟨g, box, it, rfl, hok, l, hl, h0, h1, h2, h3⟩ := hev e he
  have hc := hp n F0 F1 F2 F3 hs (oN n) hdom hv l hl (lane_oN n l hl)
  rw [h0, h1, h2, h3] at hc
  exact recOK_of_hex hok hc

theorem hexChecker_sound (progs : ℕ → Prog) (hp : ∀ i < 6, ProgOKH (hiOf i) (progs i)) :
    (hexChecker progs).Sound (kindIs 4) := by
  refine btree_sound _ hIdx (fun i => ?_) 3 0 _
  split_ifs with h
  · exact progCheckerH_sound (hp i h)
  · exact Checker.none_sound _

noncomputable def hexProgs (i : ℕ) : Prog :=
  match i with
  | 0 => fun O F0 F1 F2 F3 hs => progHNL O F0 F1 F2 F3 (hs.getD 0 0) (hs.getD 1 0)
  | 1 => fun O F0 F1 F2 F3 hs => progHNH O F0 F1 F2 F3 (hs.getD 0 0) (hs.getD 1 0)
  | 2 => fun O F0 F1 F2 F3 hs =>
    progHML O F0 F1 F2 F3 (hs.getD 0 0) (hs.getD 1 0) (hs.getD 2 0) (hs.getD 3 0) (hs.getD 4 0)
  | 3 => fun O F0 F1 F2 F3 hs => progHMH O F0 F1 F2 F3 (hs.getD 0 0) (hs.getD 1 0) (hs.getD 2 0) (hs.getD 3 0)
  | 4 => fun O F0 F1 F2 F3 hs =>
    progHFL O F0 F1 F2 F3 (hs.getD 0 0) (hs.getD 1 0) (hs.getD 2 0) (hs.getD 3 0) (hs.getD 4 0)
  | 5 => fun O F0 F1 F2 F3 hs => progHFH O F0 F1 F2 F3 (hs.getD 0 0) (hs.getD 1 0) (hs.getD 2 0) (hs.getD 3 0)
  | _ => fun _ _ _ _ _ _ => 0

theorem hexProgs_ok : ∀ i < 6, ProgOKH (hiOf i) (hexProgs i) := by
  intro i hi
  interval_cases i
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [hexProgs] at hv
    exact progHNL_decl n F0 F1 F2 F3 _ _ v hD hv l hl h1
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [hexProgs] at hv
    exact progHNH_decl n F0 F1 F2 F3 _ _ v hD hv l hl h1
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [hexProgs] at hv
    exact progHML_decl n F0 F1 F2 F3 _ _ _ _ _ v hD hv l hl h1
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [hexProgs] at hv
    exact progHMH_decl n F0 F1 F2 F3 _ _ _ _ v hD hv l hl h1
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [hexProgs] at hv
    exact progHFL_decl n F0 F1 F2 F3 _ _ _ _ _ v hD hv l hl h1
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [hexProgs] at hv
    exact progHFH_decl n F0 F1 F2 F3 _ _ _ _ v hD hv l hl h1

noncomputable def hexQ : Checker := hexChecker hexProgs

theorem hexQ_sound : hexQ.Sound (kindIs 4) := hexChecker_sound hexProgs hexProgs_ok

end Tammes15.D3Trig
