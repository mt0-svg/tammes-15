import Tammes15.Hyps.Case
import Tammes15.Contractors.Fan
import Tammes15.D3Ck2.Prog
import Tammes15.D3Ck2.Spec.Lanes
import Tammes15.D3Prog.Lane
import Tammes15.D3Prog.L2.SoundN0L
import Tammes15.D3Prog.L2.SoundN0H
import Tammes15.D3Prog.L2.SoundN1L
import Tammes15.D3Prog.L2.SoundN1H
import Tammes15.D3Prog.L2.SoundM0L
import Tammes15.D3Prog.L2.SoundM0H
import Tammes15.D3Prog.L2.SoundM1L
import Tammes15.D3Prog.L2.SoundM1H
import Tammes15.D3Prog.L2.SoundF0L
import Tammes15.D3Prog.L2.SoundF0H
import Tammes15.D3Prog.L2.SoundF1L
import Tammes15.D3Prog.L2.SoundF1H

namespace D3Ck2Spec

open Real Tammes15

noncomputable def fld (F s : ℕ) : ℝ := ((F / 2 ^ s % 2 ^ 32 : ℕ) : ℝ) / 2 ^ 24

noncomputable def pentOut (k : Fin 2) (d x y : ℝ) : ℝ :=
  if k = 0 then bangle d x + gam d (ebase d x) (ebase d y) + bangle d y
  else bangle d x + gam (ebase d y) (ebase d x) d

def FanOK (d x y : ℝ) : Prop :=
  eta d (ebase d x) (ebase d y) ∈ Set.Icc (-1 : ℝ) 1 ∧ eta (ebase d y) (ebase d x) d ∈ Set.Icc (-1 : ℝ) 1 ∧
    eta (ebase d x) (ebase d y) d ∈ Set.Icc (-1 : ℝ) 1

def Claim (hi : Bool) (c v : ℝ) : Prop := if hi then v ≤ c else c ≤ v

def LaneClaim (k : Fin 2) (hi : Bool) (F0 F1 F2 F3 : ℕ) : Prop :=
  ∀ d x y : ℝ, fld F0 0 ≤ d → d ≤ fld F0 32 → fld F1 0 ≤ x → x ≤ fld F1 32 → fld F2 0 ≤ y → y ≤ fld F2 32 →
    x < π → y < π → FanOK d x y → Claim hi (fld F3 0) (pentOut k d x y)

def InDom (F0 F1 F2 F3 : ℕ) : Prop :=
  F0 < 2 ^ 64 ∧ F1 < 2 ^ 64 ∧ F2 < 2 ^ 64 ∧ F3 < 2 ^ 32 ∧
    0.9 ≤ fld F0 0 ∧ fld F0 32 ≤ 1 ∧ 1.1 ≤ fld F1 0 ∧ fld F1 32 ≤ 3.2 ∧ 1.1 ≤ fld F2 0 ∧ fld F2 32 ≤ 3.2

theorem progN0L_sound (F0 F1 F2 F3 H0 H1 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64)
    (h : D3Ck2.progN0L 1 F0 F1 F2 F3 H0 H1 = 1) : LaneClaim 0 false F0 F1 F2 F3 := by
  exact D3Prog.progN0L_l2 F0 F1 F2 F3 H0 H1
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2 h hD

theorem progN0L_lane (n F0 F1 F2 F3 H0 H1 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progN0L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1) l =
      D3Ck2.progN0L 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) := by
  exact D3Prog.progN0L_lane' n F0 F1 F2 F3 H0 H1 l hl

theorem progN0L_decl (n F0 F1 F2 F3 H0 H1 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progN0L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 0 false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progN0L_lane n F0 F1 F2 F3 H0 H1 hD l hl] at h1
  exact progN0L_sound _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem progN0H_sound (F0 F1 F2 F3 H0 H1 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64)
    (h : D3Ck2.progN0H 1 F0 F1 F2 F3 H0 H1 = 1) : LaneClaim 0 true F0 F1 F2 F3 := by
  exact D3Prog.progN0H_l2 F0 F1 F2 F3 H0 H1
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2 h hD

theorem progN0H_lane (n F0 F1 F2 F3 H0 H1 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progN0H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1) l =
      D3Ck2.progN0H 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) := by
  exact D3Prog.progN0H_lane' n F0 F1 F2 F3 H0 H1 l hl

theorem progN0H_decl (n F0 F1 F2 F3 H0 H1 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progN0H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 0 true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progN0H_lane n F0 F1 F2 F3 H0 H1 hD l hl] at h1
  exact progN0H_sound _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem progN1L_sound (F0 F1 F2 F3 H0 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64)
    (h : D3Ck2.progN1L 1 F0 F1 F2 F3 H0 = 1) : LaneClaim 1 false F0 F1 F2 F3 := by
  exact D3Prog.progN1L_l2 F0 F1 F2 F3 H0
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH h hD

theorem progN1L_lane (n F0 F1 F2 F3 H0 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progN1L (D3Ck2.oN n) F0 F1 F2 F3 H0) l =
      D3Ck2.progN1L 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) := by
  exact D3Prog.progN1L_lane' n F0 F1 F2 F3 H0 l hl

theorem progN1L_decl (n F0 F1 F2 F3 H0 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progN1L (D3Ck2.oN n) F0 F1 F2 F3 H0) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 1 false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progN1L_lane n F0 F1 F2 F3 H0 hD l hl] at h1
  exact progN1L_sound _ _ _ _ _ (hD l hl) (lane_lt _ _) h1

theorem progN1H_sound (F0 F1 F2 F3 H0 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64)
    (h : D3Ck2.progN1H 1 F0 F1 F2 F3 H0 = 1) : LaneClaim 1 true F0 F1 F2 F3 := by
  exact D3Prog.progN1H_l2 F0 F1 F2 F3 H0
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH h hD

theorem progN1H_lane (n F0 F1 F2 F3 H0 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progN1H (D3Ck2.oN n) F0 F1 F2 F3 H0) l =
      D3Ck2.progN1H 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) := by
  exact D3Prog.progN1H_lane' n F0 F1 F2 F3 H0 l hl

theorem progN1H_decl (n F0 F1 F2 F3 H0 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progN1H (D3Ck2.oN n) F0 F1 F2 F3 H0) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 1 true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progN1H_lane n F0 F1 F2 F3 H0 hD l hl] at h1
  exact progN1H_sound _ _ _ _ _ (hD l hl) (lane_lt _ _) h1

theorem progM0L_sound (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hD : InDom F0 F1 F2 F3)
    (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64 ∧ H4 < 2 ^ 64)
    (h : D3Ck2.progM0L 1 F0 F1 F2 F3 H0 H1 H2 H3 H4 = 1) : LaneClaim 0 false F0 F1 F2 F3 := by
  exact D3Prog.progM0L_l2 F0 F1 F2 F3 H0 H1 H2 H3 H4
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2 h hD

theorem progM0L_lane (n F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progM0L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2 H3 H4) l =
      D3Ck2.progM0L 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)
        (lane H0 l) (lane H1 l) (lane H2 l) (lane H3 l) (lane H4 l) := by
  exact D3Prog.progM0L_lane' n F0 F1 F2 F3 H0 H1 H2 H3 H4 l hl

theorem progM0L_decl (n F0 F1 F2 F3 H0 H1 H2 H3 H4 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progM0L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2 H3 H4) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 0 false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progM0L_lane n F0 F1 F2 F3 H0 H1 H2 H3 H4 hD l hl] at h1
  exact progM0L_sound _ _ _ _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem progM0H_sound (F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (hD : InDom F0 F1 F2 F3)
    (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64)
    (h : D3Ck2.progM0H 1 F0 F1 F2 F3 H0 H1 H2 H3 = 1) : LaneClaim 0 true F0 F1 F2 F3 := by
  exact D3Prog.progM0H_l2 F0 F1 F2 F3 H0 H1 H2 H3
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2.1 hH.2.2.1 hH.2.2.2 h hD

theorem progM0H_lane (n F0 F1 F2 F3 H0 H1 H2 H3 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progM0H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2 H3) l =
      D3Ck2.progM0H 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)
        (lane H0 l) (lane H1 l) (lane H2 l) (lane H3 l) := by
  exact D3Prog.progM0H_lane' n F0 F1 F2 F3 H0 H1 H2 H3 l hl

theorem progM0H_decl (n F0 F1 F2 F3 H0 H1 H2 H3 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progM0H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2 H3) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 0 true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progM0H_lane n F0 F1 F2 F3 H0 H1 H2 H3 hD l hl] at h1
  exact progM0H_sound _ _ _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem progM1L_sound (F0 F1 F2 F3 H0 H1 H2 : ℕ) (hD : InDom F0 F1 F2 F3)
    (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64)
    (h : D3Ck2.progM1L 1 F0 F1 F2 F3 H0 H1 H2 = 1) : LaneClaim 1 false F0 F1 F2 F3 := by
  exact D3Prog.progM1L_l2 F0 F1 F2 F3 H0 H1 H2
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2.1 hH.2.2 h hD

theorem progM1L_lane (n F0 F1 F2 F3 H0 H1 H2 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progM1L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2) l =
      D3Ck2.progM1L 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) (lane H2 l) := by
  exact D3Prog.progM1L_lane' n F0 F1 F2 F3 H0 H1 H2 l hl

theorem progM1L_decl (n F0 F1 F2 F3 H0 H1 H2 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progM1L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 1 false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progM1L_lane n F0 F1 F2 F3 H0 H1 H2 hD l hl] at h1
  exact progM1L_sound _ _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem progM1H_sound (F0 F1 F2 F3 H0 H1 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64)
    (h : D3Ck2.progM1H 1 F0 F1 F2 F3 H0 H1 = 1) : LaneClaim 1 true F0 F1 F2 F3 := by
  exact D3Prog.progM1H_l2 F0 F1 F2 F3 H0 H1
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2 h hD

theorem progM1H_lane (n F0 F1 F2 F3 H0 H1 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progM1H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1) l =
      D3Ck2.progM1H 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) := by
  exact D3Prog.progM1H_lane' n F0 F1 F2 F3 H0 H1 l hl

theorem progM1H_decl (n F0 F1 F2 F3 H0 H1 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progM1H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 1 true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progM1H_lane n F0 F1 F2 F3 H0 H1 hD l hl] at h1
  exact progM1H_sound _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem progF0L_sound (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hD : InDom F0 F1 F2 F3)
    (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64 ∧ H4 < 2 ^ 64)
    (h : D3Ck2.progF0L 1 F0 F1 F2 F3 H0 H1 H2 H3 H4 = 1) : LaneClaim 0 false F0 F1 F2 F3 := by
  exact D3Prog.progF0L_l2 F0 F1 F2 F3 H0 H1 H2 H3 H4
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2 h hD

theorem progF0L_lane (n F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progF0L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2 H3 H4) l =
      D3Ck2.progF0L 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)
        (lane H0 l) (lane H1 l) (lane H2 l) (lane H3 l) (lane H4 l) := by
  exact D3Prog.progF0L_lane' n F0 F1 F2 F3 H0 H1 H2 H3 H4 l hl

theorem progF0L_decl (n F0 F1 F2 F3 H0 H1 H2 H3 H4 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progF0L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2 H3 H4) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 0 false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progF0L_lane n F0 F1 F2 F3 H0 H1 H2 H3 H4 hD l hl] at h1
  exact progF0L_sound _ _ _ _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem progF0H_sound (F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (hD : InDom F0 F1 F2 F3)
    (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64)
    (h : D3Ck2.progF0H 1 F0 F1 F2 F3 H0 H1 H2 H3 = 1) : LaneClaim 0 true F0 F1 F2 F3 := by
  exact D3Prog.progF0H_l2 F0 F1 F2 F3 H0 H1 H2 H3
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2.1 hH.2.2.1 hH.2.2.2 h hD

theorem progF0H_lane (n F0 F1 F2 F3 H0 H1 H2 H3 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progF0H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2 H3) l =
      D3Ck2.progF0H 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)
        (lane H0 l) (lane H1 l) (lane H2 l) (lane H3 l) := by
  exact D3Prog.progF0H_lane' n F0 F1 F2 F3 H0 H1 H2 H3 l hl

theorem progF0H_decl (n F0 F1 F2 F3 H0 H1 H2 H3 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progF0H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2 H3) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 0 true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progF0H_lane n F0 F1 F2 F3 H0 H1 H2 H3 hD l hl] at h1
  exact progF0H_sound _ _ _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem progF1L_sound (F0 F1 F2 F3 H0 H1 H2 : ℕ) (hD : InDom F0 F1 F2 F3)
    (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64)
    (h : D3Ck2.progF1L 1 F0 F1 F2 F3 H0 H1 H2 = 1) : LaneClaim 1 false F0 F1 F2 F3 := by
  exact D3Prog.progF1L_l2 F0 F1 F2 F3 H0 H1 H2
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2.1 hH.2.2 h hD

theorem progF1L_lane (n F0 F1 F2 F3 H0 H1 H2 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progF1L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2) l =
      D3Ck2.progF1L 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) (lane H2 l) := by
  exact D3Prog.progF1L_lane' n F0 F1 F2 F3 H0 H1 H2 l hl

theorem progF1L_decl (n F0 F1 F2 F3 H0 H1 H2 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progF1L (D3Ck2.oN n) F0 F1 F2 F3 H0 H1 H2) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 1 false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progF1L_lane n F0 F1 F2 F3 H0 H1 H2 hD l hl] at h1
  exact progF1L_sound _ _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem progF1H_sound (F0 F1 F2 F3 H0 H1 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64)
    (h : D3Ck2.progF1H 1 F0 F1 F2 F3 H0 H1 = 1) : LaneClaim 1 true F0 F1 F2 F3 := by
  exact D3Prog.progF1H_l2 F0 F1 F2 F3 H0 H1
    hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num))
    hH.1 hH.2 h hD

theorem progF1H_lane (n F0 F1 F2 F3 H0 H1 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (D3Ck2.progF1H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1) l =
      D3Ck2.progF1H 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) := by
  exact D3Prog.progF1H_lane' n F0 F1 F2 F3 H0 H1 l hl

theorem progF1H_decl (n F0 F1 F2 F3 H0 H1 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (D3Ck2.progF1H (D3Ck2.oN n) F0 F1 F2 F3 H0 H1) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaim 1 true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progF1H_lane n F0 F1 F2 F3 H0 H1 hD l hl] at h1
  exact progF1H_sound _ _ _ _ _ _ (hD l hl) (by simp only [lane_lt, and_self]) h1

theorem decDirX_sound {lo hi d : ℝ} (Y : ℝ → ℝ) (full : Bool) (t1lo nl dl nh dh yl yh : ℤ) (hdl : 0 < dl)
    (hdh : 0 < dh) (hfull : full = true ∨ ¬(nl < 0 ∧ 0 < nh ∧ yl < 0 ∧ 0 < yh))
    (htest : decTestX full t1lo nl dl nh dh yl yh = true)
    (ht1 : ∀ u ∈ Set.Icc lo (min hi π), (t1lo : ℝ) ≤ 2 ^ 28 * (cos d * sin (u / 2)))
    (hcot : ∀ u ∈ Set.Icc lo (min hi π), 0 < Y u → Y u < π →
      (nl : ℝ) / dl ≤ cot (Y u) ∧ cot (Y u) ≤ (nh : ℝ) / dh)
    (hch : ∀ u ∈ Set.Icc lo (min hi π), (yl : ℝ) ≤ 2 ^ 28 * cos (u / 2) ∧ 2 ^ 28 * cos (u / 2) ≤ yh) :
    ∀ u ∈ Set.Icc lo (min hi π), 0 < Y u → Y u < π → 0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
  intro u hu hY0 hY1
  have h := decTestX_sound full t1lo nl dl nh dh yl yh hdl hdh hfull htest (2 ^ 28 * (cos d * sin (u / 2)))
    (cot (Y u)) (2 ^ 28 * cos (u / 2)) (ht1 u hu) (hcot u hu hY0 hY1) (hch u hu)
  have h2 : 2 ^ 28 * (cos d * sin (u / 2)) + cot (Y u) * (2 ^ 28 * cos (u / 2)) =
      2 ^ 28 * (cos d * sin (u / 2) + cot (Y u) * cos (u / 2)) := by ring
  rw [h2] at h
  exact (pos_of_mul_pos_right h (by positivity)).le

theorem decDirX_early {lo hi d : ℝ} (Y : ℝ → ℝ) (hlo : 0 < lo) (hd0 : 0 < d ∧ d < π / 2) (bxhi : ℝ)
    (hbx : ∀ u ∈ Set.Icc lo (min hi π), 0 < Y u → Y u < π → bangle d u + Y u ≤ bxhi) (hbxpi : bxhi ≤ π) :
    ∀ u ∈ Set.Icc lo (min hi π), 0 < Y u → Y u < π → 0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
  intro u hu hYpos hYlt
  have hu_le_pi : u ≤ π := hu.2.trans (min_le_right _ _)
  have hu_pos : 0 < u := hlo.trans_le hu.1
  have hcos_d_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith [hd0.1], hd0.2⟩
  have hsum_le_pi : bangle d u + Y u ≤ π := (hbx u hu hYpos hYlt).trans hbxpi
  by_cases hu_eq_pi : u = π
  · subst hu_eq_pi
    have h_target_eq : cos d * sin (π / 2) + cot (Y π) * cos (π / 2) = cos d := by
      simp [Real.sin_pi_div_two, Real.cos_pi_div_two, Real.cot_eq_cos_div_sin]
    rw [h_target_eq]
    exact hcos_d_pos.le
  · have hu_lt_pi : u < π := lt_of_le_of_ne hu_le_pi hu_eq_pi
    have hcos_u2_pos : 0 < cos (u / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hsin_u2_pos : 0 < sin (u / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hbangle_pos : 0 < bangle d u := by
      rw [bangle]
      exact Real.arctan_pos.mpr (div_pos hcos_u2_pos (mul_pos hcos_d_pos hsin_u2_pos))
    have hsin_sum_nonneg : 0 ≤ sin (bangle d u + Y u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hsum_le_pi
    have hbangle_lt : bangle d u < π / 2 := Real.arctan_lt_pi_div_two _
    have hsin_bangle_pos : 0 < sin (bangle d u) :=
      Real.sin_pos_of_pos_of_lt_pi hbangle_pos (by linarith [Real.pi_pos])
    have hsin_Y_pos : 0 < sin (Y u) := Real.sin_pos_of_pos_of_lt_pi hYpos hYlt
    rw [Tammes15.fan_sign_identity d u (Y u) hd0 ⟨hu_pos, hu_lt_pi⟩ ⟨hYpos, hYlt⟩]
    exact div_nonneg (mul_nonneg hcos_u2_pos.le hsin_sum_nonneg) (mul_nonneg hsin_bangle_pos.le hsin_Y_pos.le)

theorem gam_swap (g e f : ℝ) : gam g e f = gam g f e := by
  simp only [gam, eta, mul_comm]

theorem pentOut0_antitoneOn_x {d y p q : ℝ} (hd : 0 < d ∧ d < π / 2) (hy : 0 < y ∧ y ≤ π) (hp : 0 < p)
    (hq : q ≤ π)
    (hF : ∀ u ∈ Set.Icc p q, -1 < eta d (ebase d u) (ebase d y) → eta d (ebase d u) (ebase d y) < 1 →
      0 ≤ cos d * sin (u / 2) + cot (gam (ebase d y) (ebase d u) d) * cos (u / 2)) :
    AntitoneOn (fun u => pentOut 0 d u y) (Set.Icc p q) := by
  have hb := Tammes15.ebase_mem_Ioo d y hd hy
  have h := Tammes15.Contractors.fanC_antitoneOn hd ⟨hb.1, hb.2⟩ ⟨hd.1, by linarith [Real.pi_gt_three]⟩ hp hq hF
  intro a ha b hb' hab
  have := h ha hb' hab
  have e0 : ∀ u v, pentOut 0 d u v = bangle d u + gam d (ebase d u) (ebase d v) + bangle d v := fun u v => by
    simp [pentOut]
  simp only [e0]
  simp only at this
  linarith

theorem pentOut0_antitoneOn_y {d x p q : ℝ} (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x ≤ π) (hp : 0 < p)
    (hq : q ≤ π)
    (hF : ∀ u ∈ Set.Icc p q, -1 < eta d (ebase d u) (ebase d x) → eta d (ebase d u) (ebase d x) < 1 →
      0 ≤ cos d * sin (u / 2) + cot (gam (ebase d x) (ebase d u) d) * cos (u / 2)) :
    AntitoneOn (fun u => pentOut 0 d x u) (Set.Icc p q) := by
  have hb := Tammes15.ebase_mem_Ioo d x hd hx
  have h := Tammes15.Contractors.fanC_antitoneOn hd ⟨hb.1, hb.2⟩ ⟨hd.1, by linarith [Real.pi_gt_three]⟩ hp hq hF
  intro a ha b hb' hab
  have := h ha hb' hab
  have e0 : ∀ u v, pentOut 0 d u v = bangle d u + gam d (ebase d u) (ebase d v) + bangle d v := fun u v => by
    simp [pentOut]
  simp only [e0, gam_swap d (ebase d x)]
  simp only at this
  linarith

theorem pentOut1_antitoneOn_x {d y p q : ℝ} (hd : 0 < d ∧ d < π / 2) (hy : 0 < y ∧ y ≤ π) (hp : 0 < p)
    (hq : q ≤ π)
    (hF : ∀ u ∈ Set.Icc p q, -1 < eta (ebase d y) (ebase d u) d → eta (ebase d y) (ebase d u) d < 1 →
      0 ≤ cos d * sin (u / 2) + cot (gam d (ebase d u) (ebase d y)) * cos (u / 2)) :
    AntitoneOn (fun u => pentOut 1 d u y) (Set.Icc p q) := by
  have hb := Tammes15.ebase_mem_Ioo d y hd hy
  have h := Tammes15.Contractors.fanC_antitoneOn hd ⟨hd.1, by linarith [Real.pi_gt_three]⟩ ⟨hb.1, hb.2⟩ hp hq hF
  intro a ha b hb' hab
  have := h ha hb' hab
  have e1 : ∀ u v, pentOut 1 d u v = bangle d u + gam (ebase d v) (ebase d u) d := fun u v => by
    simp [pentOut]
  simp only [e1]
  simpa using this

theorem claim_of_eq {hi : Bool} {c v w : ℝ} (h : Claim hi c v) (hw : w = v) : Claim hi c w := hw ▸ h

theorem laneClaim_pent0 {d u₀ u₁ u₂ u₃ u₄ : ℝ} (hP : PentRel d u₀ u₁ u₂ u₃ u₄) (h1 : u₁ < π) (h4 : u₄ < π)
    {hi : Bool} {F0 F1 F2 F3 : ℕ} (hc : LaneClaim 0 hi F0 F1 F2 F3) (hd : fld F0 0 ≤ d ∧ d ≤ fld F0 32)
    (hx : fld F1 0 ≤ u₁ ∧ u₁ ≤ fld F1 32) (hy : fld F2 0 ≤ u₄ ∧ u₄ ≤ fld F2 32) :
    Claim hi (fld F3 0) u₀ := by
  obtain ⟨he1, he2, he3, hu0, -, -⟩ := hP
  refine claim_of_eq (hc d u₁ u₄ hd.1 hd.2 hx.1 hx.2 hy.1 hy.2 h1 h4 ⟨he1, he2, he3⟩) ?_
  simp [pentOut, hu0]

theorem laneClaim_pent2 {d u₀ u₁ u₂ u₃ u₄ : ℝ} (hP : PentRel d u₀ u₁ u₂ u₃ u₄) (h1 : u₁ < π) (h4 : u₄ < π)
    {hi : Bool} {F0 F1 F2 F3 : ℕ} (hc : LaneClaim 1 hi F0 F1 F2 F3) (hd : fld F0 0 ≤ d ∧ d ≤ fld F0 32)
    (hx : fld F1 0 ≤ u₁ ∧ u₁ ≤ fld F1 32) (hy : fld F2 0 ≤ u₄ ∧ u₄ ≤ fld F2 32) :
    Claim hi (fld F3 0) u₂ := by
  obtain ⟨he1, he2, he3, -, hu2, -⟩ := hP
  refine claim_of_eq (hc d u₁ u₄ hd.1 hd.2 hx.1 hx.2 hy.1 hy.2 h1 h4 ⟨he1, he2, he3⟩) ?_
  simp [pentOut, hu2]

theorem laneClaim_pent3 {d u₀ u₁ u₂ u₃ u₄ : ℝ} (hP : PentRel d u₀ u₁ u₂ u₃ u₄) (h1 : u₁ < π) (h4 : u₄ < π)
    {hi : Bool} {F0 F1 F2 F3 : ℕ} (hc : LaneClaim 1 hi F0 F1 F2 F3) (hd : fld F0 0 ≤ d ∧ d ≤ fld F0 32)
    (hx : fld F1 0 ≤ u₄ ∧ u₄ ≤ fld F1 32) (hy : fld F2 0 ≤ u₁ ∧ u₁ ≤ fld F2 32) :
    Claim hi (fld F3 0) u₃ := by
  obtain ⟨he1, he2, he3, -, -, hu3⟩ := hP
  have hF : FanOK d u₄ u₁ := by
    refine ⟨?_, he3, he2⟩
    simpa [eta, mul_comm] using he1
  refine claim_of_eq (hc d u₄ u₁ hd.1 hd.2 hx.1 hx.2 hy.1 hy.2 h4 h1 hF) ?_
  simp [pentOut, hu3]

theorem laneClaim_relSys {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k} (hA : RelSys P H A)
    {e : P.G.Dart} (he : fsize P e = 5) {hi : Bool} {F0 F1 F2 F3 : ℕ} (hd : fld F0 0 ≤ A.d ∧ A.d ≤ fld F0 32) :
    ((fld F1 0 ≤ A.fc e 1 ∧ A.fc e 1 ≤ fld F1 32) → (fld F2 0 ≤ A.fc e 4 ∧ A.fc e 4 ≤ fld F2 32) →
        (LaneClaim 0 hi F0 F1 F2 F3 → Claim hi (fld F3 0) (A.fc e 0)) ∧
          (LaneClaim 1 hi F0 F1 F2 F3 → Claim hi (fld F3 0) (A.fc e 2))) ∧
      ((fld F1 0 ≤ A.fc e 4 ∧ A.fc e 4 ≤ fld F1 32) → (fld F2 0 ≤ A.fc e 1 ∧ A.fc e 1 ≤ fld F2 32) →
        LaneClaim 1 hi F0 F1 F2 F3 → Claim hi (fld F3 0) (A.fc e 3)) := by
  have hP := hA.pent e he
  have h1 : A.fc e 1 < π := (hA.corner_mem _).2
  have h4 : A.fc e 4 < π := (hA.corner_mem _).2
  exact ⟨fun hx hy => ⟨fun hc => laneClaim_pent0 hP h1 h4 hc hd hx hy,
    fun hc => laneClaim_pent2 hP h1 h4 hc hd hx hy⟩, fun hx hy hc => laneClaim_pent3 hP h1 h4 hc hd hx hy⟩

end D3Ck2Spec
