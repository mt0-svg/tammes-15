import Tammes15.D3Trig.HexLink
import Tammes15.D3Trig.Prog.HNL
import Tammes15.D3Trig.Prog.HNH
import Tammes15.D3Trig.Prog.HML
import Tammes15.D3Trig.Prog.HMH
import Tammes15.D3Trig.Prog.HFL
import Tammes15.D3Trig.Prog.HFH
import Tammes15.D3Trig.LaneHNL
import Tammes15.D3Trig.LaneHNH
import Tammes15.D3Trig.LaneHML
import Tammes15.D3Trig.LaneHMH
import Tammes15.D3Trig.LaneHFL
import Tammes15.D3Trig.LaneHFH
import Tammes15.D3Trig.SoundHNL
import Tammes15.D3Trig.SoundHNH
import Tammes15.D3Trig.SoundHML
import Tammes15.D3Trig.SoundHMH
import Tammes15.D3Trig.SoundHFL
import Tammes15.D3Trig.SoundHFH

namespace Tammes15.D3Trig

open Tammes15.D3Kernel

theorem lane_lt64H (A l : ℕ) : lane A l < 2 ^ 64 := Nat.mod_lt _ (by positivity)

theorem progHNL_sound (F0 F1 F2 F3 H0 H1 : ℕ) (hD : InDomH F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64)
    (h : progHNL 1 F0 F1 F2 F3 H0 H1 = 1) : LaneClaimH false F0 F1 F2 F3 := by
  exact progHNL_l2 F0 F1 F2 F3 H0 H1 hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hH.1 hH.2 h hD

theorem progHNL_lane (n F0 F1 F2 F3 H0 H1 : ℕ) (l : ℕ) (hl : l < n) :
    lane (progHNL (oN n) F0 F1 F2 F3 H0 H1) l =
      progHNL 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) := by
  exact progHNL_lane' n F0 F1 F2 F3 H0 H1 l hl

theorem progHNL_decl (n F0 F1 F2 F3 H0 H1 v : ℕ)
    (hD : ∀ i < n, InDomH (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progHNL (oN n) F0 F1 F2 F3 H0 H1) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimH false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progHNL_lane n F0 F1 F2 F3 H0 H1 l hl] at h1
  exact progHNL_sound _ _ _ _ _ _ (hD l hl) ⟨lane_lt64H H0 l, lane_lt64H H1 l⟩ h1

theorem progHNH_sound (F0 F1 F2 F3 H0 H1 : ℕ) (hD : InDomH F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64)
    (h : progHNH 1 F0 F1 F2 F3 H0 H1 = 1) : LaneClaimH true F0 F1 F2 F3 := by
  exact progHNH_l2 F0 F1 F2 F3 H0 H1 hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hH.1 hH.2 h hD

theorem progHNH_lane (n F0 F1 F2 F3 H0 H1 : ℕ) (l : ℕ) (hl : l < n) :
    lane (progHNH (oN n) F0 F1 F2 F3 H0 H1) l =
      progHNH 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) := by
  exact progHNH_lane' n F0 F1 F2 F3 H0 H1 l hl

theorem progHNH_decl (n F0 F1 F2 F3 H0 H1 v : ℕ)
    (hD : ∀ i < n, InDomH (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progHNH (oN n) F0 F1 F2 F3 H0 H1) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimH true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progHNH_lane n F0 F1 F2 F3 H0 H1 l hl] at h1
  exact progHNH_sound _ _ _ _ _ _ (hD l hl) ⟨lane_lt64H H0 l, lane_lt64H H1 l⟩ h1

theorem progHML_sound (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hD : InDomH F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64 ∧ H4 < 2 ^ 64)
    (h : progHML 1 F0 F1 F2 F3 H0 H1 H2 H3 H4 = 1) : LaneClaimH false F0 F1 F2 F3 := by
  exact progHML_l2 F0 F1 F2 F3 H0 H1 H2 H3 H4 hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2 h hD

theorem progHML_lane (n F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (l : ℕ) (hl : l < n) :
    lane (progHML (oN n) F0 F1 F2 F3 H0 H1 H2 H3 H4) l =
      progHML 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) (lane H2 l) (lane H3 l) (lane H4 l) := by
  exact progHML_lane' n F0 F1 F2 F3 H0 H1 H2 H3 H4 l hl

theorem progHML_decl (n F0 F1 F2 F3 H0 H1 H2 H3 H4 v : ℕ)
    (hD : ∀ i < n, InDomH (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progHML (oN n) F0 F1 F2 F3 H0 H1 H2 H3 H4) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimH false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progHML_lane n F0 F1 F2 F3 H0 H1 H2 H3 H4 l hl] at h1
  exact progHML_sound _ _ _ _ _ _ _ _ _ (hD l hl) ⟨lane_lt64H H0 l, lane_lt64H H1 l, lane_lt64H H2 l, lane_lt64H H3 l, lane_lt64H H4 l⟩ h1

theorem progHMH_sound (F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (hD : InDomH F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64)
    (h : progHMH 1 F0 F1 F2 F3 H0 H1 H2 H3 = 1) : LaneClaimH true F0 F1 F2 F3 := by
  exact progHMH_l2 F0 F1 F2 F3 H0 H1 H2 H3 hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hH.1 hH.2.1 hH.2.2.1 hH.2.2.2 h hD

theorem progHMH_lane (n F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (l : ℕ) (hl : l < n) :
    lane (progHMH (oN n) F0 F1 F2 F3 H0 H1 H2 H3) l =
      progHMH 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) (lane H2 l) (lane H3 l) := by
  exact progHMH_lane' n F0 F1 F2 F3 H0 H1 H2 H3 l hl

theorem progHMH_decl (n F0 F1 F2 F3 H0 H1 H2 H3 v : ℕ)
    (hD : ∀ i < n, InDomH (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progHMH (oN n) F0 F1 F2 F3 H0 H1 H2 H3) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimH true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progHMH_lane n F0 F1 F2 F3 H0 H1 H2 H3 l hl] at h1
  exact progHMH_sound _ _ _ _ _ _ _ _ (hD l hl) ⟨lane_lt64H H0 l, lane_lt64H H1 l, lane_lt64H H2 l, lane_lt64H H3 l⟩ h1

theorem progHFL_sound (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hD : InDomH F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64 ∧ H4 < 2 ^ 64)
    (h : progHFL 1 F0 F1 F2 F3 H0 H1 H2 H3 H4 = 1) : LaneClaimH false F0 F1 F2 F3 := by
  exact progHFL_l2 F0 F1 F2 F3 H0 H1 H2 H3 H4 hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2 h hD

theorem progHFL_lane (n F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (l : ℕ) (hl : l < n) :
    lane (progHFL (oN n) F0 F1 F2 F3 H0 H1 H2 H3 H4) l =
      progHFL 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) (lane H2 l) (lane H3 l) (lane H4 l) := by
  exact progHFL_lane' n F0 F1 F2 F3 H0 H1 H2 H3 H4 l hl

theorem progHFL_decl (n F0 F1 F2 F3 H0 H1 H2 H3 H4 v : ℕ)
    (hD : ∀ i < n, InDomH (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progHFL (oN n) F0 F1 F2 F3 H0 H1 H2 H3 H4) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimH false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progHFL_lane n F0 F1 F2 F3 H0 H1 H2 H3 H4 l hl] at h1
  exact progHFL_sound _ _ _ _ _ _ _ _ _ (hD l hl) ⟨lane_lt64H H0 l, lane_lt64H H1 l, lane_lt64H H2 l, lane_lt64H H3 l, lane_lt64H H4 l⟩ h1

theorem progHFH_sound (F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (hD : InDomH F0 F1 F2 F3) (hH : H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64)
    (h : progHFH 1 F0 F1 F2 F3 H0 H1 H2 H3 = 1) : LaneClaimH true F0 F1 F2 F3 := by
  exact progHFH_l2 F0 F1 F2 F3 H0 H1 H2 H3 hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hH.1 hH.2.1 hH.2.2.1 hH.2.2.2 h hD

theorem progHFH_lane (n F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (l : ℕ) (hl : l < n) :
    lane (progHFH (oN n) F0 F1 F2 F3 H0 H1 H2 H3) l =
      progHFH 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) (lane H1 l) (lane H2 l) (lane H3 l) := by
  exact progHFH_lane' n F0 F1 F2 F3 H0 H1 H2 H3 l hl

theorem progHFH_decl (n F0 F1 F2 F3 H0 H1 H2 H3 v : ℕ)
    (hD : ∀ i < n, InDomH (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progHFH (oN n) F0 F1 F2 F3 H0 H1 H2 H3) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimH true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progHFH_lane n F0 F1 F2 F3 H0 H1 H2 H3 l hl] at h1
  exact progHFH_sound _ _ _ _ _ _ _ _ (hD l hl) ⟨lane_lt64H H0 l, lane_lt64H H1 l, lane_lt64H H2 l, lane_lt64H H3 l⟩ h1

end Tammes15.D3Trig
