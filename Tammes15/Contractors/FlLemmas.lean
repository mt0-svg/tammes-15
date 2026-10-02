import Tammes15.Contractors.Arith

/-!
# Order lemmas for the float values `Fl`
-/

namespace Tammes15.Contractors

namespace Fl

theorem ofReal_le_ofReal {x y : ℝ} : Fl.le (.ofReal x) (.ofReal y) ↔ x ≤ y := by
  simp [Fl.le, Fl.ofReal]

theorem ofReal_lt_ofReal {x y : ℝ} : Fl.lt (.ofReal x) (.ofReal y) ↔ x < y := by
  simp [Fl.lt, Fl.ofReal]

theorem le_trans {a b c : Fl} (h₁ : Fl.le a b) (h₂ : Fl.le b c) : Fl.le a c := by
  cases a <;> cases b <;> cases c <;> simp_all [Fl.le]
  exact _root_.le_trans h₁ h₂

theorem lt_of_lt_of_le {a b c : Fl} (h₁ : Fl.lt a b) (h₂ : Fl.le b c) : Fl.lt a c := by
  cases a <;> cases b <;> cases c <;> simp_all [Fl.le, Fl.lt]
  exact _root_.lt_of_lt_of_le h₁ h₂

theorem lt_of_le_of_lt {a b c : Fl} (h₁ : Fl.le a b) (h₂ : Fl.lt b c) : Fl.lt a c := by
  cases a <;> cases b <;> cases c <;> simp_all [Fl.le, Fl.lt]
  exact _root_.lt_of_le_of_lt h₁ h₂

theorem le_of_lt {a b : Fl} (h : Fl.lt a b) : Fl.le a b := by
  cases a <;> cases b <;> simp_all [Fl.le, Fl.lt]
  exact h.le

theorem not_lt_of_le {a b : Fl} (h : Fl.le a b) : ¬ Fl.lt b a := by
  cases a <;> cases b <;> simp_all [Fl.le, Fl.lt]

/-- A value between two reals is the real it reads as. -/
theorem eq_ofReal_toReal {a : Fl} {x y : ℝ} (h₁ : Fl.le (.ofReal x) a) (h₂ : Fl.le a (.ofReal y)) :
    a = .ofReal a.toReal := by
  cases a with
  | nan => simp [Fl.le] at h₁
  | num a =>
    simp only [Fl.le, Fl.ofReal] at h₁ h₂
    have h1 : a ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot x) h₁
    have h2 : a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top y) h₂
    simp [Fl.ofReal, Fl.toReal, EReal.coe_toReal h2 h1]

theorem le_ofReal_toReal {a : Fl} {x y : ℝ} (h₁ : Fl.le (.ofReal x) a) (h₂ : Fl.le a (.ofReal y)) :
    x ≤ a.toReal ∧ a.toReal ≤ y := by
  have h := eq_ofReal_toReal h₁ h₂
  rw [h, ofReal_le_ofReal] at h₁ h₂
  exact ⟨h₁, h₂⟩

theorem max_le {a b c : Fl} (ha : Fl.le a c) (hb : Fl.le b c) : Fl.le (Fl.max a b) c := by
  cases a <;> cases b <;> cases c <;> simp_all [Fl.le, Fl.max]

theorem le_min {a b c : Fl} (ha : Fl.le c a) (hb : Fl.le c b) : Fl.le c (Fl.min a b) := by
  cases a <;> cases b <;> cases c <;> simp_all [Fl.le, Fl.min]

theorem le_max_left {a b : Fl} (ha : a ≠ .nan) : Fl.le a (Fl.max a b) := by
  cases a <;> cases b <;> simp_all [Fl.le, Fl.max]

theorem min_le_left {a b : Fl} (ha : a ≠ .nan) : Fl.le (Fl.min a b) a := by
  cases a <;> cases b <;> simp_all [Fl.le, Fl.min]

theorem min_le_right {a b : Fl} (hb : b ≠ .nan) : Fl.le (Fl.min a b) b := by
  cases a <;> cases b <;> simp_all [Fl.le, Fl.min]

theorem le_max_right {a b : Fl} (hb : b ≠ .nan) : Fl.le b (Fl.max a b) := by
  cases a <;> cases b <;> simp_all [Fl.le, Fl.max]

/-- The clamp `min U 1` of deep.rs, for an upper bound `U ≥ y` that is not below `-1`. -/
theorem min_one_eq {U : Fl} {y : ℝ} (hU : Fl.le (.ofReal y) U)
    (hU1 : ¬ Fl.lt U (.ofReal (-1))) :
    ∃ r : ℝ, Fl.min U (.ofReal 1) = .ofReal r ∧ -1 ≤ r ∧ r ≤ 1 ∧ Min.min y 1 ≤ r := by
  cases U with
  | nan => simp [Fl.le] at hU
  | num z =>
    cases z using EReal.rec with
    | bot => simp [Fl.le, Fl.ofReal] at hU
    | coe z =>
      simp only [Fl.le, Fl.lt, Fl.ofReal, EReal.coe_le_coe_iff, EReal.coe_lt_coe_iff,
        not_lt] at hU hU1
      refine ⟨Min.min z 1, ?_, _root_.le_min hU1 (by norm_num), _root_.min_le_right _ _,
        min_le_min hU le_rfl⟩
      simp only [Fl.min, Fl.ofReal, Fl.num.injEq]
      rw [EReal.coe_strictMono.monotone.map_min, EReal.coe_one]
    | top =>
      refine ⟨1, ?_, by norm_num, le_rfl, _root_.min_le_right _ _⟩
      simp [Fl.min, Fl.ofReal]

/-- The clamp `max L (-1)` of deep.rs, for a lower bound `L ≤ y` that is not above `1`. -/
theorem max_neg_one_eq {L : Fl} {y : ℝ} (hL : Fl.le L (.ofReal y))
    (hL1 : ¬ Fl.lt (.ofReal 1) L) :
    ∃ r : ℝ, Fl.max L (.ofReal (-1)) = .ofReal r ∧ -1 ≤ r ∧ r ≤ 1 ∧ r ≤ Max.max y (-1) := by
  cases L with
  | nan => simp [Fl.le] at hL
  | num z =>
    cases z using EReal.rec with
    | bot =>
      refine ⟨-1, ?_, le_rfl, by norm_num, _root_.le_max_right _ _⟩
      simp [Fl.max, Fl.ofReal]
    | coe z =>
      simp only [Fl.le, Fl.lt, Fl.ofReal, EReal.coe_le_coe_iff, EReal.coe_lt_coe_iff,
        not_lt] at hL hL1
      refine ⟨Max.max z (-1), ?_, _root_.le_max_right _ _, _root_.max_le hL1 (by norm_num),
        max_le_max hL le_rfl⟩
      simp only [Fl.max, Fl.ofReal, Fl.num.injEq]
      rw [EReal.coe_strictMono.monotone.map_max]
    | top => simp [Fl.le, Fl.ofReal] at hL

theorem ne_nan_of_le {a b : Fl} (h : Fl.le a b) : a ≠ .nan := by
  rintro rfl; simp [Fl.le] at h

theorem ne_nan_of_le' {a b : Fl} (h : Fl.le a b) : b ≠ .nan := by
  rintro rfl; cases a <;> simp [Fl.le] at h

@[simp] theorem toReal_ofReal (x : ℝ) : (Fl.ofReal x).toReal = x := by
  simp [Fl.ofReal, Fl.toReal]

/-- A value below every real is `-∞`. -/
theorem eq_ninf_of_le_all {a : Fl} (h : ∀ r : ℝ, Fl.le a (.ofReal r)) : a = Fl.ninf := by
  cases a with
  | nan => simpa [Fl.le] using h 0
  | num z =>
    cases z using EReal.rec with
    | bot => rfl
    | coe z =>
      have := h (z - 1)
      simp only [Fl.le, Fl.ofReal, EReal.coe_le_coe_iff] at this
      linarith
    | top => simpa [Fl.le, Fl.ofReal] using h 0

/-- A value above every real is `∞`. -/
theorem eq_inf_of_ge_all {a : Fl} (h : ∀ r : ℝ, Fl.le (.ofReal r) a) : a = Fl.inf := by
  cases a with
  | nan => simpa [Fl.le] using h 0
  | num z =>
    cases z using EReal.rec with
    | bot => simpa [Fl.le, Fl.ofReal] using h 0
    | coe z =>
      have := h (z + 1)
      simp only [Fl.le, Fl.ofReal, EReal.coe_le_coe_iff] at this
      linarith
    | top => rfl

/-- A value below a real, other than `-∞`, is a real. -/
theorem eq_ofReal_of_le {a : Fl} {y : ℝ} (h : Fl.le a (.ofReal y)) (hn : a ≠ Fl.ninf) :
    a = .ofReal a.toReal ∧ a.toReal ≤ y := by
  cases a with
  | nan => simp [Fl.le] at h
  | num z =>
    cases z using EReal.rec with
    | bot => exact absurd rfl hn
    | coe z => simp_all [Fl.le, Fl.ofReal, Fl.toReal]
    | top => simp [Fl.le, Fl.ofReal] at h

/-- A value above a real, other than `∞`, is a real. -/
theorem eq_ofReal_of_ge {a : Fl} {y : ℝ} (h : Fl.le (.ofReal y) a) (hn : a ≠ Fl.inf) :
    a = .ofReal a.toReal ∧ y ≤ a.toReal := by
  cases a with
  | nan => simp [Fl.le] at h
  | num z =>
    cases z using EReal.rec with
    | bot => simp [Fl.le, Fl.ofReal] at h
    | coe z => simp_all [Fl.le, Fl.ofReal, Fl.toReal]
    | top => exact absurd rfl hn

theorem ninf_le (x : ℝ) : Fl.le Fl.ninf (.ofReal x) := by
  simp [Fl.le, Fl.ninf, Fl.ofReal]

theorem le_inf (x : ℝ) : Fl.le (.ofReal x) Fl.inf := by
  simp [Fl.le, Fl.inf, Fl.ofReal]

end Fl

theorem Iv.mem_ofReal {lo hi x : ℝ} : (Iv.ofReal lo hi).Mem x ↔ lo ≤ x ∧ x ≤ hi := by
  simp [Iv.Mem, Iv.ofReal, Fl.ofReal_le_ofReal]

theorem Iv.mem_pt {x : ℝ} : (Iv.pt (.ofReal x)).Mem x := by
  simp [Iv.Mem, Iv.pt, Fl.ofReal_le_ofReal]

theorem Iv.pos_of_lt_lo {I : Iv} {x : ℝ} (h : Fl.lt (.ofReal 0) I.lo) (hx : I.Mem x) : 0 < x :=
  Fl.ofReal_lt_ofReal.mp (Fl.lt_of_lt_of_le h hx.1)

theorem Iv.neg_of_hi_lt {I : Iv} {x : ℝ} (h : Fl.lt I.hi (.ofReal 0)) (hx : I.Mem x) : x < 0 :=
  Fl.ofReal_lt_ofReal.mp (Fl.lt_of_le_of_lt hx.2 h)

theorem Iv.mem_of_eq {I : Iv} {l h x : ℝ} (hl : I.lo = .ofReal l) (hh : I.hi = .ofReal h)
    (h1 : l ≤ x) (h2 : x ≤ h) : I.Mem x := by
  unfold Iv.Mem
  rw [hl, hh]
  exact ⟨Fl.ofReal_le_ofReal.mpr h1, Fl.ofReal_le_ofReal.mpr h2⟩

theorem Iv.lo_le {I : Iv} {x : ℝ} (hx : I.Mem x) : Fl.le I.lo (.ofReal x) := hx.1

theorem Iv.le_hi {I : Iv} {x : ℝ} (hx : I.Mem x) : Fl.le (.ofReal x) I.hi := hx.2

end Tammes15.Contractors
