import Tammes15.D3Kernel.Pent
import Tammes15.D3Ck2.Spec.Link

namespace Tammes15.D3Prog

open Tammes15.D3Kernel Tammes15.D3Kernel.Pent

def hint (hs : List ℕ) (j : ℕ) : ℕ := hs.getD j 0

noncomputable def progs (i : ℕ) : Prog :=
  match i with
  | 0 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progN0L O F0 F1 F2 F3 (hint hs 0) (hint hs 1)
  | 1 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progN0H O F0 F1 F2 F3 (hint hs 0) (hint hs 1)
  | 2 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progN1L O F0 F1 F2 F3 (hint hs 0)
  | 3 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progN1H O F0 F1 F2 F3 (hint hs 0)
  | 4 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progM0L O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) (hint hs 4)
  | 5 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progM0H O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3)
  | 6 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progM1L O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2)
  | 7 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progM1H O F0 F1 F2 F3 (hint hs 0) (hint hs 1)
  | 8 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progF0L O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) (hint hs 4)
  | 9 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progF0H O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3)
  | 10 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progF1L O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2)
  | 11 => fun O F0 F1 F2 F3 hs =>
    D3Ck2.progF1H O F0 F1 F2 F3 (hint hs 0) (hint hs 1)
  | _ => fun _ _ _ _ _ _ => 0

def Sound12 : Prop :=
  (∀ F0 F1 F2 F3 H0 H1 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64) →
      D3Ck2.progN0L 1 F0 F1 F2 F3 H0 H1 = 1 → D3Ck2Spec.LaneClaim 0 false F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 H1 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64) →
      D3Ck2.progN0H 1 F0 F1 F2 F3 H0 H1 = 1 → D3Ck2Spec.LaneClaim 0 true F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64) →
      D3Ck2.progN1L 1 F0 F1 F2 F3 H0 = 1 → D3Ck2Spec.LaneClaim 1 false F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64) →
      D3Ck2.progN1H 1 F0 F1 F2 F3 H0 = 1 → D3Ck2Spec.LaneClaim 1 true F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64 ∧ H4 < 2 ^ 64) →
      D3Ck2.progM0L 1 F0 F1 F2 F3 H0 H1 H2 H3 H4 = 1 → D3Ck2Spec.LaneClaim 0 false F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 H1 H2 H3 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64) →
      D3Ck2.progM0H 1 F0 F1 F2 F3 H0 H1 H2 H3 = 1 → D3Ck2Spec.LaneClaim 0 true F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 H1 H2 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64) →
      D3Ck2.progM1L 1 F0 F1 F2 F3 H0 H1 H2 = 1 → D3Ck2Spec.LaneClaim 1 false F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 H1 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64) →
      D3Ck2.progM1H 1 F0 F1 F2 F3 H0 H1 = 1 → D3Ck2Spec.LaneClaim 1 true F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64 ∧ H4 < 2 ^ 64) →
      D3Ck2.progF0L 1 F0 F1 F2 F3 H0 H1 H2 H3 H4 = 1 → D3Ck2Spec.LaneClaim 0 false F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 H1 H2 H3 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64) →
      D3Ck2.progF0H 1 F0 F1 F2 F3 H0 H1 H2 H3 = 1 → D3Ck2Spec.LaneClaim 0 true F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 H1 H2 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64) →
      D3Ck2.progF1L 1 F0 F1 F2 F3 H0 H1 H2 = 1 → D3Ck2Spec.LaneClaim 1 false F0 F1 F2 F3)
  ∧ (∀ F0 F1 F2 F3 H0 H1 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64) →
      D3Ck2.progF1H 1 F0 F1 F2 F3 H0 H1 = 1 → D3Ck2Spec.LaneClaim 1 true F0 F1 F2 F3)

theorem sound12 : Sound12 :=
  ⟨D3Ck2Spec.progN0L_sound,
   D3Ck2Spec.progN0H_sound,
   D3Ck2Spec.progN1L_sound,
   D3Ck2Spec.progN1H_sound,
   D3Ck2Spec.progM0L_sound,
   D3Ck2Spec.progM0H_sound,
   D3Ck2Spec.progM1L_sound,
   D3Ck2Spec.progM1H_sound,
   D3Ck2Spec.progF0L_sound,
   D3Ck2Spec.progF0H_sound,
   D3Ck2Spec.progF1L_sound,
   D3Ck2Spec.progF1H_sound⟩

theorem progs_eq_0 : progs 0 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progN0L O F0 F1 F2 F3 (hint hs 0) (hint hs 1) := rfl

theorem progOK_0 (s : ∀ F0 F1 F2 F3 H0 H1 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64) →
      D3Ck2.progN0L 1 F0 F1 F2 F3 H0 H1 = 1 → D3Ck2Spec.LaneClaim 0 false F0 F1 F2 F3) :
    ProgOK 0 false (progs 0) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_0] at h1
  have e := D3Ck2Spec.progN0L_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) hD l hl
  exact s _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_eq_1 : progs 1 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progN0H O F0 F1 F2 F3 (hint hs 0) (hint hs 1) := rfl

theorem progOK_1 (s : ∀ F0 F1 F2 F3 H0 H1 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64) →
      D3Ck2.progN0H 1 F0 F1 F2 F3 H0 H1 = 1 → D3Ck2Spec.LaneClaim 0 true F0 F1 F2 F3) :
    ProgOK 0 true (progs 1) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_1] at h1
  have e := D3Ck2Spec.progN0H_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) hD l hl
  exact s _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_eq_2 : progs 2 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progN1L O F0 F1 F2 F3 (hint hs 0) := rfl

theorem progOK_2 (s : ∀ F0 F1 F2 F3 H0 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64) →
      D3Ck2.progN1L 1 F0 F1 F2 F3 H0 = 1 → D3Ck2Spec.LaneClaim 1 false F0 F1 F2 F3) :
    ProgOK 1 false (progs 2) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_2] at h1
  have e := D3Ck2Spec.progN1L_lane n F0 F1 F2 F3
    (hint hs 0) hD l hl
  exact s _ _ _ _ _ (hD l hl) (D3Ck2Spec.lane_lt _ _)
    (e.symm.trans h1)

theorem progs_eq_3 : progs 3 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progN1H O F0 F1 F2 F3 (hint hs 0) := rfl

theorem progOK_3 (s : ∀ F0 F1 F2 F3 H0 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64) →
      D3Ck2.progN1H 1 F0 F1 F2 F3 H0 = 1 → D3Ck2Spec.LaneClaim 1 true F0 F1 F2 F3) :
    ProgOK 1 true (progs 3) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_3] at h1
  have e := D3Ck2Spec.progN1H_lane n F0 F1 F2 F3
    (hint hs 0) hD l hl
  exact s _ _ _ _ _ (hD l hl) (D3Ck2Spec.lane_lt _ _)
    (e.symm.trans h1)

theorem progs_eq_4 : progs 4 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progM0L O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) (hint hs 4) := rfl

theorem progOK_4 (s : ∀ F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64 ∧ H4 < 2 ^ 64) →
      D3Ck2.progM0L 1 F0 F1 F2 F3 H0 H1 H2 H3 H4 = 1 → D3Ck2Spec.LaneClaim 0 false F0 F1 F2 F3) :
    ProgOK 0 false (progs 4) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_4] at h1
  have e := D3Ck2Spec.progM0L_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) (hint hs 4) hD l hl
  exact s _ _ _ _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_eq_5 : progs 5 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progM0H O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) := rfl

theorem progOK_5 (s : ∀ F0 F1 F2 F3 H0 H1 H2 H3 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64) →
      D3Ck2.progM0H 1 F0 F1 F2 F3 H0 H1 H2 H3 = 1 → D3Ck2Spec.LaneClaim 0 true F0 F1 F2 F3) :
    ProgOK 0 true (progs 5) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_5] at h1
  have e := D3Ck2Spec.progM0H_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) hD l hl
  exact s _ _ _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_eq_6 : progs 6 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progM1L O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) := rfl

theorem progOK_6 (s : ∀ F0 F1 F2 F3 H0 H1 H2 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64) →
      D3Ck2.progM1L 1 F0 F1 F2 F3 H0 H1 H2 = 1 → D3Ck2Spec.LaneClaim 1 false F0 F1 F2 F3) :
    ProgOK 1 false (progs 6) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_6] at h1
  have e := D3Ck2Spec.progM1L_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) (hint hs 2) hD l hl
  exact s _ _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_eq_7 : progs 7 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progM1H O F0 F1 F2 F3 (hint hs 0) (hint hs 1) := rfl

theorem progOK_7 (s : ∀ F0 F1 F2 F3 H0 H1 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64) →
      D3Ck2.progM1H 1 F0 F1 F2 F3 H0 H1 = 1 → D3Ck2Spec.LaneClaim 1 true F0 F1 F2 F3) :
    ProgOK 1 true (progs 7) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_7] at h1
  have e := D3Ck2Spec.progM1H_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) hD l hl
  exact s _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_eq_8 : progs 8 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progF0L O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) (hint hs 4) := rfl

theorem progOK_8 (s : ∀ F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64 ∧ H4 < 2 ^ 64) →
      D3Ck2.progF0L 1 F0 F1 F2 F3 H0 H1 H2 H3 H4 = 1 → D3Ck2Spec.LaneClaim 0 false F0 F1 F2 F3) :
    ProgOK 0 false (progs 8) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_8] at h1
  have e := D3Ck2Spec.progF0L_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) (hint hs 4) hD l hl
  exact s _ _ _ _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_eq_9 : progs 9 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progF0H O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) := rfl

theorem progOK_9 (s : ∀ F0 F1 F2 F3 H0 H1 H2 H3 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64 ∧ H3 < 2 ^ 64) →
      D3Ck2.progF0H 1 F0 F1 F2 F3 H0 H1 H2 H3 = 1 → D3Ck2Spec.LaneClaim 0 true F0 F1 F2 F3) :
    ProgOK 0 true (progs 9) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_9] at h1
  have e := D3Ck2Spec.progF0H_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) (hint hs 2) (hint hs 3) hD l hl
  exact s _ _ _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_eq_10 : progs 10 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progF1L O F0 F1 F2 F3 (hint hs 0) (hint hs 1) (hint hs 2) := rfl

theorem progOK_10 (s : ∀ F0 F1 F2 F3 H0 H1 H2 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64 ∧ H2 < 2 ^ 64) →
      D3Ck2.progF1L 1 F0 F1 F2 F3 H0 H1 H2 = 1 → D3Ck2Spec.LaneClaim 1 false F0 F1 F2 F3) :
    ProgOK 1 false (progs 10) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_10] at h1
  have e := D3Ck2Spec.progF1L_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) (hint hs 2) hD l hl
  exact s _ _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_eq_11 : progs 11 = fun O F0 F1 F2 F3 hs =>
    D3Ck2.progF1H O F0 F1 F2 F3 (hint hs 0) (hint hs 1) := rfl

theorem progOK_11 (s : ∀ F0 F1 F2 F3 H0 H1 : ℕ, D3Ck2Spec.InDom F0 F1 F2 F3 →
      (H0 < 2 ^ 64 ∧ H1 < 2 ^ 64) →
      D3Ck2.progF1H 1 F0 F1 F2 F3 H0 H1 = 1 → D3Ck2Spec.LaneClaim 1 true F0 F1 F2 F3) :
    ProgOK 1 true (progs 11) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  rw [← Nat.eq_of_beq_eq_true hv, progs_eq_11] at h1
  have e := D3Ck2Spec.progF1H_lane n F0 F1 F2 F3
    (hint hs 0) (hint hs 1) hD l hl
  exact s _ _ _ _ _ _ (hD l hl) (by simp only [D3Ck2Spec.lane_lt, and_self])
    (e.symm.trans h1)

theorem progs_ok_of (hS : Sound12) : ∀ i < 12, ProgOK (kOf i) (hiOf i) (progs i) := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hS
  intro i hi
  interval_cases i
  · exact progOK_0 s0
  · exact progOK_1 s1
  · exact progOK_2 s2
  · exact progOK_3 s3
  · exact progOK_4 s4
  · exact progOK_5 s5
  · exact progOK_6 s6
  · exact progOK_7 s7
  · exact progOK_8 s8
  · exact progOK_9 s9
  · exact progOK_10 s10
  · exact progOK_11 s11

theorem progs_ok : ∀ i < 12, ProgOK (kOf i) (hiOf i) (progs i) := progs_ok_of sound12

end Tammes15.D3Prog
