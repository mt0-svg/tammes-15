import Tammes15.D3Trig.Slice
import Tammes15.D3Prog.Bridge
import Tammes15.D3Trig.Rho
import Tammes15.D3Trig.Hex
import Tammes15.D3Trig.Wheel

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel Tammes15.D3Kernel.Pent

theorem pentBatch {i : ℕ} (hi : i < 12) {D : ℕ} {B : Batch} {hs : List ℕ}
    (h : batchOK (D3Prog.progs i) inDomB D B hs = true) : BatchClaims (LaneClaim (kOf i) (hiOf i)) B :=
  batchClaims_of_ok (Dom := InDom) inDomB_sound (D3Prog.progs_ok i hi) h

theorem rhoBatch {i : ℕ} (hi : i < 4) {D : ℕ} {B : Batch} {hs : List ℕ}
    (h : batchOK (rhoProgs i) inDomB D B hs = true) : BatchClaims (LaneClaimR (kOf i) (hiOf i)) B :=
  batchClaims_of_ok (Dom := InDom) inDomB_sound (rhoProgs_ok i hi) h

theorem hexBatch {i : ℕ} (hi : i < 6) {D : ℕ} {B : Batch} {hs : List ℕ}
    (h : batchOK (hexProgs i) inDomBH D B hs = true) : BatchClaims (LaneClaimH (hiOf i)) B :=
  batchClaims_of_ok (Dom := InDomH) inDomBH_sound (hexProgs_ok i hi) h

theorem wheelBatchL {D : ℕ} {B : Batch} {hs : List ℕ} (h : batchOK wheelProgL inDomBW D B hs = true) :
    BatchClaims (LaneClaimW false) B :=
  batchClaims_of_ok (Dom := InDomW) inDomBW_sound wheelProgL_ok h

theorem wheelBatchH {D : ℕ} {B : Batch} {hs : List ℕ} (h : batchOK wheelProgH inDomBW D B hs = true) :
    BatchClaims (LaneClaimW true) B :=
  batchClaims_of_ok (Dom := InDomW) inDomBW_sound wheelProgH_ok h

theorem wheelBatchS {D : ℕ} {B : Batch} {hs : List ℕ} (h : batchOK wheelProgS inDomBWS D B hs = true) :
    BatchClaims LaneClaimWS B :=
  batchClaims_of_ok (Dom := InDomWS) inDomBWS_sound wheelProgS_ok h

theorem pentSlice_ok (tP : ℕ → BT) (Dt : ℕ → ℕ)
    (ht : ∀ i < 12, (tP i).All (BatchClaims (LaneClaim (kOf i) (hiOf i)))) :
    ∀ i < 12, ProgOK (kOf i) (hiOf i) (sliceProg (tP i) (Dt i)) :=
  fun i hi => sliceProg_ok (Dom := InDom) (Dt i) (ht i hi)

theorem pentSlice_sound (tP : ℕ → BT) (Dt : ℕ → ℕ)
    (ht : ∀ i < 12, (tP i).All (BatchClaims (LaneClaim (kOf i) (hiOf i)))) :
    (pentChecker fun i => sliceProg (tP i) (Dt i)).Sound (kindIs 3) :=
  pentChecker_sound _ (pentSlice_ok tP Dt ht)

theorem rhoSlice_sound (tR : ℕ → BT) (Dt : ℕ → ℕ)
    (ht : ∀ i < 4, (tR i).All (BatchClaims (LaneClaimR (kOf i) (hiOf i)))) :
    (rhoChecker fun i => sliceProg (tR i) (Dt i)).Sound (kindIs 2) :=
  rhoChecker_sound _ fun i hi => sliceProg_ok (Dom := InDom) (Dt i) (ht i hi)

theorem hexSlice_sound (tH : ℕ → BT) (Dt : ℕ → ℕ)
    (ht : ∀ i < 6, (tH i).All (BatchClaims (LaneClaimH (hiOf i)))) :
    (hexChecker fun i => sliceProg (tH i) (Dt i)).Sound (kindIs 4) :=
  hexChecker_sound _ fun i hi => sliceProg_ok (Dom := InDomH) (Dt i) (ht i hi)

theorem wheelSlice_sound {tL tH tS : BT} (DL DH DS : ℕ) (hL : tL.All (BatchClaims (LaneClaimW false)))
    (hH : tH.All (BatchClaims (LaneClaimW true))) (hS : tS.All (BatchClaims LaneClaimWS)) :
    (wheelChecker (sliceProg tL DL) (sliceProg tH DH) (sliceProg tS DS)).Sound (kindIs 6) :=
  wheelChecker_sound (sliceProg_ok (Dom := InDomW) DL hL) (sliceProg_ok (Dom := InDomW) DH hH)
    (sliceProg_ok (Dom := InDomWS) DS hS)

end Tammes15.D3Trig
