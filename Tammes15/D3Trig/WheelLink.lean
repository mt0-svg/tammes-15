import Tammes15.D3Kernel.Pent

open Real

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel

noncomputable def wheelOut (P Q r d : ℝ) : ℝ := gam P r d + gam Q r d

def InDomW (F0 F1 F2 F3 : ℕ) : Prop :=
  F0 < 2 ^ 64 ∧ F1 < 2 ^ 64 ∧ F2 < 2 ^ 64 ∧ F3 < 2 ^ 32 ∧
    0.9 ≤ fld F0 0 ∧ fld F0 32 ≤ 1 ∧ fld F2 0 ≤ 3.14 ∧ fld F2 32 ≤ 3.14

def LaneClaimW (hi : Bool) (F0 F1 F2 F3 : ℕ) : Prop :=
  ∀ d r : ℝ, fld F0 0 ≤ d → d ≤ fld F0 32 → fld F1 0 ≤ r → r ≤ fld F1 32 →
    if hi then wheelOut (fld F2 0) (fld F2 32) r d < fld F3 0 else fld F3 0 < wheelOut (fld F2 0) (fld F2 32) r d

def InDomWS (F0 F1 F2 F3 : ℕ) : Prop := F0 < 2 ^ 64 ∧ F1 < 2 ^ 64 ∧ F2 < 2 ^ 64 ∧ F3 < 2 ^ 32

def LaneClaimWS (F0 F1 F2 F3 : ℕ) : Prop :=
  ∀ d r r' : ℝ, fld F0 0 ≤ d → d ≤ fld F0 32 → fld F1 0 ≤ r → r ≤ fld F1 32 → fld F2 0 ≤ r' → r' ≤ fld F2 32 →
    gam d r r' < fld F3 0

theorem gam_mono_left {a a' b c : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (ha' : a' ≤ π) (hb : 0 < b) (hb' : b < π)
    (hc : 0 < c) (hc' : c < π) : gam a b c ≤ gam a' b c := by
  have hsin_pos : 0 < sin b * sin c :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi hb hb') (Real.sin_pos_of_pos_of_lt_pi hc hc')
  have hcos_le : cos a' ≤ cos a :=
    Real.cos_le_cos_of_nonneg_of_le_pi ha ha' haa
  have hnum_le : cos a' - cos b * cos c ≤ cos a - cos b * cos c :=
    sub_le_sub_right hcos_le (cos b * cos c)
  have heta_le : eta a' b c ≤ eta a b c :=
    div_le_div_of_nonneg_right hnum_le (by linarith)
  exact Real.arccos_le_arccos heta_le

theorem wheelOut_mono {P P' Q Q' r d : ℝ} (hP : 0 ≤ P) (hPP : P ≤ P') (hP' : P' ≤ π) (hQ : 0 ≤ Q)
    (hQQ : Q ≤ Q') (hQ' : Q' ≤ π) (hr : 0 < r) (hr' : r < π) (hd : 0 < d) (hd' : d < π) :
    wheelOut P Q r d ≤ wheelOut P' Q' r d := by
  unfold wheelOut
  have h1 : gam P r d ≤ gam P' r d := gam_mono_left hP hPP hP' hr hr' hd hd'
  have h2 : gam Q r d ≤ gam Q' r d := gam_mono_left hQ hQQ hQ' hr hr' hd hd'
  exact add_le_add h1 h2

theorem tri_lower {a b c : ℝ} (h : eta a b c ≤ 1) (ha : 0 ≤ a) (_ha' : a ≤ π) (hb : 0 < b)
    (hb' : b < π) (hc : 0 < c) (hc' : c < π) : b - c ≤ a ∧ c - b ≤ a := by
  have hsinb_pos : 0 < sin b := Real.sin_pos_of_pos_of_lt_pi hb hb'
  have hsinc_pos : 0 < sin c := Real.sin_pos_of_pos_of_lt_pi hc hc'
  have hsin_prod_pos : 0 < sin b * sin c := mul_pos hsinb_pos hsinc_pos
  have hcos_ineq : cos a - cos b * cos c ≤ sin b * sin c := by
    unfold eta at h
    exact (div_le_one hsin_prod_pos).mp h
  have hcos_le : cos a ≤ cos (b - c) := by
    have : cos a ≤ cos b * cos c + sin b * sin c := by linarith
    rw [Real.cos_sub b c]
    exact this
  have hcos_abs_le : cos a ≤ cos |b - c| := by
    rw [Real.cos_abs]
    exact hcos_le
  have habs_le_pi : |b - c| ≤ π := by
    have h_abs_lt : |b - c| < π := by
      rw [abs_lt]
      constructor <;> linarith
    exact le_of_lt h_abs_lt
  have h_abs_le_a : |b - c| ≤ a := by
    by_contra! hlt
    have hcos_lt : cos |b - c| < cos a :=
      Real.cos_lt_cos_of_nonneg_of_le_pi ha habs_le_pi hlt
    linarith
  have h1 : b - c ≤ a := by
    have : b - c ≤ |b - c| := le_abs_self (b - c)
    linarith
  have h2 : c - b ≤ a := by
    have hle : c - b ≤ |c - b| := le_abs_self (c - b)
    have heq : |c - b| = |b - c| := abs_sub_comm _ _
    linarith
  exact And.intro h1 h2

theorem tri_upper {a b c : ℝ} (h : -1 ≤ eta a b c) (_ha : 0 ≤ a) (ha' : a ≤ π) (hb : 0 < b)
    (hb' : b < π) (hc : 0 < c) (hc' : c < π) : a ≤ b + c := by
  have hsinb : 0 < sin b := Real.sin_pos_of_pos_of_lt_pi hb hb'
  have hsinc : 0 < sin c := Real.sin_pos_of_pos_of_lt_pi hc hc'
  have hsinprod : 0 < sin b * sin c := mul_pos hsinb hsinc
  have hineq : -1 * (sin b * sin c) ≤ cos a - cos b * cos c :=
    (le_div_iff₀ hsinprod).mp h
  have hcosbc : cos (b + c) ≤ cos a := by
    rw [Real.cos_add]
    linarith
  by_cases hbc : π ≤ b + c
  · linarith
  · have hbc_nonneg : 0 ≤ b + c := by linarith
    have hbc_le_pi : b + c ≤ π := by linarith
    by_contra! hlt
    have hcos_lt : cos a < cos (b + c) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hbc_nonneg ha' hlt
    linarith

theorem tri_of_eta {a b c : ℝ} (h : eta a b c ∈ Set.Icc (-1 : ℝ) 1) (ha : 0 ≤ a) (ha' : a ≤ π) (hb : 0 < b)
    (hb' : b < π) (hc : 0 < c) (hc' : c < π) : b - c ≤ a ∧ c - b ≤ a ∧ a ≤ b + c := by
  obtain ⟨h1, h2⟩ := tri_lower h.2 ha ha' hb hb' hc hc'
  exact ⟨h1, h2, tri_upper h.1 ha ha' hb hb' hc hc'⟩

theorem val_r {g : ℕ} {P : PlaneGraph} {kk : ℕ} (lab : P.G.Dart ≃ Fin (Ctx.D g)) (A : Assign P kk) {v m j : ℕ}
    (hm : m < kk) (hj : j < 6) (h : Ctx.mean g v = 258 + 6 * m + j) : Ctx.val g lab A v = A.r ⟨m, hm⟩ ⟨j, hj⟩ := by
  have hq : (Ctx.mean g v - 258) / 6 = m := by omega
  have hr : (Ctx.mean g v - 258) % 6 = j := by omega
  unfold Ctx.val
  rw [ite_eq_right (show ¬ Ctx.mean g v = 0 by omega), ite_eq_right (show ¬ Ctx.mean g v = 1 by omega),
    dite_eq_right (show ¬ (Ctx.mean g v < 258 ∧ Ctx.mean g v - 2 < Ctx.D g) by omega),
    dite_eq_left (show (Ctx.mean g v - 258) / 6 < kk by omega)]
  exact congrArg₂ A.r (Fin.ext hq) (Fin.ext hr)

theorem fin6_succ {i : ℕ} (hi : i < 6) : (⟨i, hi⟩ + 1 : Fin 6) = ⟨(i + 1) % 6, Nat.mod_lt _ (by norm_num)⟩ := by
  apply Fin.ext
  interval_cases i <;> rfl

theorem fin6_pred {i : ℕ} (hi : i < 6) : (⟨i, hi⟩ - 1 : Fin 6) = ⟨(i + 5) % 6, Nat.mod_lt _ (by norm_num)⟩ := by
  apply Fin.ext
  interval_cases i <;> rfl

theorem wheel_fc {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k} (hA : RelSys P H A) (m : Fin k)
    {i : ℕ} (hi : i < 6) :
    A.fc (H.base m) i = wheelOut (A.r m ⟨(i + 1) % 6, Nat.mod_lt _ (by norm_num)⟩)
      (A.r m ⟨(i + 5) % 6, Nat.mod_lt _ (by norm_num)⟩) (A.r m ⟨i, hi⟩) A.d := by
  have h := (hA.wheel m).2.2.2.2 ⟨i, hi⟩
  rw [fin6_succ hi, fin6_pred hi] at h
  exact h

theorem wheel_r {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k} (hA : RelSys P H A) (m : Fin k)
    (j : Fin 6) : A.d ≤ A.r m j ∧ A.r m j ≤ 3 * A.d :=
  (hA.wheel m).1 j

theorem wheel_eta {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k} (hA : RelSys P H A) (m : Fin k)
    {i : ℕ} (hi : i < 6) :
    eta (A.r m ⟨(i + 1) % 6, Nat.mod_lt _ (by norm_num)⟩) (A.r m ⟨i, hi⟩) A.d ∈ Set.Icc (-1 : ℝ) 1 ∧
      eta (A.r m ⟨(i + 5) % 6, Nat.mod_lt _ (by norm_num)⟩) (A.r m ⟨i, hi⟩) A.d ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := (hA.wheel m).2.2.2.1 ⟨i, hi⟩
  rw [fin6_succ hi, fin6_pred hi] at h
  exact h

theorem wheel_sum {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k} (hA : RelSys P H A) (m : Fin k) :
    ∑ j : Fin 6, gam A.d (A.r m j) (A.r m (j + 1)) = 2 * π :=
  (hA.wheel m).2.2.1

end Tammes15.D3Trig
