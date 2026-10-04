import Tammes15.D3Trig.RhoLink
import Tammes15.D3Trig.Prog.RL
import Tammes15.D3Trig.Prog.RH
import Tammes15.D3Trig.Prog.DL
import Tammes15.D3Trig.Prog.DH
import Tammes15.D3Trig.LaneRL
import Tammes15.D3Trig.LaneRH
import Tammes15.D3Trig.LaneDL
import Tammes15.D3Trig.LaneDH
import Tammes15.D3Trig.SoundRL
import Tammes15.D3Trig.SoundRH
import Tammes15.D3Trig.SoundDL
import Tammes15.D3Trig.SoundDH

namespace Tammes15.D3Trig

open Tammes15.D3Kernel

theorem lane_lt64 (A l : ℕ) : lane A l < 2 ^ 64 := Nat.mod_lt _ (by positivity)

theorem progRL_sound (F0 F1 F2 F3 H0 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64)
    (h : progRL 1 F0 F1 F2 F3 H0 = 1) : LaneClaimR 0 false F0 F1 F2 F3 := by
  exact progRL_l2 F0 F1 F2 F3 H0 hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num)) hH h hD

theorem progRL_lane (n F0 F1 F2 F3 H0 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (progRL (oN n) F0 F1 F2 F3 H0) l =
      progRL 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) := by
  exact progRL_lane' n F0 F1 F2 F3 H0 l hl

theorem progRL_decl (n F0 F1 F2 F3 H0 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progRL (oN n) F0 F1 F2 F3 H0) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimR 0 false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progRL_lane n F0 F1 F2 F3 H0 hD l hl] at h1
  exact progRL_sound _ _ _ _ _ (hD l hl) (lane_lt64 H0 l) h1

theorem progRH_sound (F0 F1 F2 F3 H0 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64)
    (h : progRH 1 F0 F1 F2 F3 H0 = 1) : LaneClaimR 0 true F0 F1 F2 F3 := by
  exact progRH_l2 F0 F1 F2 F3 H0 hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num)) hH h hD

theorem progRH_lane (n F0 F1 F2 F3 H0 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (progRH (oN n) F0 F1 F2 F3 H0) l =
      progRH 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) := by
  exact progRH_lane' n F0 F1 F2 F3 H0 l hl

theorem progRH_decl (n F0 F1 F2 F3 H0 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progRH (oN n) F0 F1 F2 F3 H0) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimR 0 true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progRH_lane n F0 F1 F2 F3 H0 hD l hl] at h1
  exact progRH_sound _ _ _ _ _ (hD l hl) (lane_lt64 H0 l) h1

theorem progDL_sound (F0 F1 F2 F3 H0 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64)
    (h : progDL 1 F0 F1 F2 F3 H0 = 1) : LaneClaimR 1 false F0 F1 F2 F3 := by
  exact progDL_l2 F0 F1 F2 F3 H0 hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num)) hH h hD

theorem progDL_lane (n F0 F1 F2 F3 H0 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (progDL (oN n) F0 F1 F2 F3 H0) l =
      progDL 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) := by
  exact progDL_lane' n F0 F1 F2 F3 H0 l hl

theorem progDL_decl (n F0 F1 F2 F3 H0 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progDL (oN n) F0 F1 F2 F3 H0) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimR 1 false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progDL_lane n F0 F1 F2 F3 H0 hD l hl] at h1
  exact progDL_sound _ _ _ _ _ (hD l hl) (lane_lt64 H0 l) h1

theorem progDH_sound (F0 F1 F2 F3 H0 : ℕ) (hD : InDom F0 F1 F2 F3) (hH : H0 < 2 ^ 64)
    (h : progDH 1 F0 F1 F2 F3 H0 = 1) : LaneClaimR 1 true F0 F1 F2 F3 := by
  exact progDH_l2 F0 F1 F2 F3 H0 hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num)) hH h hD

theorem progDH_lane (n F0 F1 F2 F3 H0 : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) (l : ℕ) (hl : l < n) :
    lane (progDH (oN n) F0 F1 F2 F3 H0) l =
      progDH 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) := by
  exact progDH_lane' n F0 F1 F2 F3 H0 l hl

theorem progDH_decl (n F0 F1 F2 F3 H0 v : ℕ)
    (hD : ∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progDH (oN n) F0 F1 F2 F3 H0) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimR 1 true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progDH_lane n F0 F1 F2 F3 H0 hD l hl] at h1
  exact progDH_sound _ _ _ _ _ (hD l hl) (lane_lt64 H0 l) h1

end Tammes15.D3Trig
