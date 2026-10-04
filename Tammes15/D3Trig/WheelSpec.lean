import Tammes15.D3Trig.WheelLink
import Tammes15.D3Trig.Prog.WL
import Tammes15.D3Trig.Prog.WH
import Tammes15.D3Trig.Prog.WSH
import Tammes15.D3Trig.LaneWL
import Tammes15.D3Trig.LaneWH
import Tammes15.D3Trig.LaneWSH
import Tammes15.D3Trig.SoundWL
import Tammes15.D3Trig.SoundWH
import Tammes15.D3Trig.SoundWSH

namespace Tammes15.D3Trig

open Tammes15.D3Kernel

theorem lane_lt64W (A l : ℕ) : lane A l < 2 ^ 64 := Nat.mod_lt _ (by positivity)

theorem progWL_sound (F0 F1 F2 F3 H0 : ℕ) (hD : InDomW F0 F1 F2 F3) (hH : H0 < 2 ^ 64)
    (h : progWL 1 F0 F1 F2 F3 H0 = 1) : LaneClaimW false F0 F1 F2 F3 := by
  exact progWL_l2 F0 F1 F2 F3 H0 hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num)) hH h hD

theorem progWL_lane (n F0 F1 F2 F3 H0 : ℕ) (l : ℕ) (hl : l < n) :
    lane (progWL (oN n) F0 F1 F2 F3 H0) l = progWL 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) := by
  exact progWL_lane' n F0 F1 F2 F3 H0 l hl

theorem progWL_decl (n F0 F1 F2 F3 H0 v : ℕ)
    (hD : ∀ i < n, InDomW (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progWL (oN n) F0 F1 F2 F3 H0) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimW false (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progWL_lane n F0 F1 F2 F3 H0 l hl] at h1
  exact progWL_sound _ _ _ _ _ (hD l hl) (lane_lt64W H0 l) h1

theorem progWH_sound (F0 F1 F2 F3 H0 : ℕ) (hD : InDomW F0 F1 F2 F3) (hH : H0 < 2 ^ 64)
    (h : progWH 1 F0 F1 F2 F3 H0 = 1) : LaneClaimW true F0 F1 F2 F3 := by
  exact progWH_l2 F0 F1 F2 F3 H0 hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2.1 (by norm_num)) hH h hD

theorem progWH_lane (n F0 F1 F2 F3 H0 : ℕ) (l : ℕ) (hl : l < n) :
    lane (progWH (oN n) F0 F1 F2 F3 H0) l = progWH 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) := by
  exact progWH_lane' n F0 F1 F2 F3 H0 l hl

theorem progWH_decl (n F0 F1 F2 F3 H0 v : ℕ)
    (hD : ∀ i < n, InDomW (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progWH (oN n) F0 F1 F2 F3 H0) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimW true (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progWH_lane n F0 F1 F2 F3 H0 l hl] at h1
  exact progWH_sound _ _ _ _ _ (hD l hl) (lane_lt64W H0 l) h1

theorem progWSH_sound (F0 F1 F2 F3 H0 : ℕ) (hD : InDomWS F0 F1 F2 F3) (hH : H0 < 2 ^ 64)
    (h : progWSH 1 F0 F1 F2 F3 H0 = 1) : LaneClaimWS F0 F1 F2 F3 := by
  exact progWSH_l2 F0 F1 F2 F3 H0 hD.1 hD.2.1 hD.2.2.1 (lt_trans hD.2.2.2 (by norm_num)) hH h hD

theorem progWSH_lane (n F0 F1 F2 F3 H0 : ℕ) (l : ℕ) (hl : l < n) :
    lane (progWSH (oN n) F0 F1 F2 F3 H0) l =
      progWSH 1 (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) (lane H0 l) := by
  exact progWSH_lane' n F0 F1 F2 F3 H0 l hl

theorem progWSH_decl (n F0 F1 F2 F3 H0 v : ℕ)
    (hD : ∀ i < n, InDomWS (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i))
    (hv : Nat.beq (progWSH (oN n) F0 F1 F2 F3 H0) v = true)
    (l : ℕ) (hl : l < n) (h1 : lane v l = 1) :
    LaneClaimWS (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l) := by
  have hv' := Nat.eq_of_beq_eq_true hv
  rw [← hv', progWSH_lane n F0 F1 F2 F3 H0 l hl] at h1
  exact progWSH_sound _ _ _ _ _ (hD l hl) (lane_lt64W H0 l) h1

end Tammes15.D3Trig
