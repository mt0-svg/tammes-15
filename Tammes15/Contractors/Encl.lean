import Tammes15.Contractors.Prims
import Tammes15.Contractors.FlLemmas
import Tammes15.Trigrows.Rows
import Tammes15.Hyps.Case

/-!
# Interval enclosures of the contractors (proof of Proposition B.2 of the paper)

Each lemma reads one computation of `Tammes15.Contractors.Prims` over an arithmetic with
`Rnd.Sound`: the directed sums and the update of a row of `fbbt`, and the enclosures of `alpha`,
its inverse, `rho`, the rhombus side, the isosceles base and base angle and the long-diagonal bound
at the real values they stand for; and the monotonicity of `eta` in a side.
-/

namespace Tammes15.Contractors

open Real
open scoped Classical
open Tammes15 Tammes15.PaperSteps.Search

theorem cmin_le {R : Rnd} (hR : R.Sound) {c l u x : ℝ} (hl : l ≤ x)
    (hu : x ≤ u) : Fl.le (cmin R c l u) (.ofReal (c * x)) := by
  unfold cmin
  split
  · -- case 0 ≤ c
    have hmul := hR.mulDn c l
    have hmul_le : Fl.le (R.mulDn (.ofReal c) (.ofReal l)) (.ofReal (c * l)) := hmul
    have h_mul_le : c * l ≤ c * x := mul_le_mul_of_nonneg_left hl (by linarith)
    have h_ofReal : Fl.le (.ofReal (c * l)) (.ofReal (c * x)) :=
      (Fl.ofReal_le_ofReal.mpr h_mul_le)
    exact Fl.le_trans hmul_le h_ofReal
  · -- case c < 0
    have hmul := hR.mulDn c u
    have hmul_le : Fl.le (R.mulDn (.ofReal c) (.ofReal u)) (.ofReal (c * u)) := hmul
    have hc : c ≤ 0 := by linarith
    have h_mul_le : c * u ≤ c * x := mul_le_mul_of_nonpos_left hu hc
    have h_ofReal : Fl.le (.ofReal (c * u)) (.ofReal (c * x)) :=
      (Fl.ofReal_le_ofReal.mpr h_mul_le)
    exact Fl.le_trans hmul_le h_ofReal

theorem le_cmax {R : Rnd} (hR : R.Sound) {c l u x : ℝ} (hl : l ≤ x)
    (hu : x ≤ u) : Fl.le (.ofReal (c * x)) (cmax R c l u) := by
  unfold cmax
  split
  · -- case 0 ≤ c
    have hmul : c * x ≤ c * u := mul_le_mul_of_nonneg_left hu (by linarith)
    have hfl : Fl.le (.ofReal (c * x)) (.ofReal (c * u)) := by
      rw [Fl.ofReal_le_ofReal]
      exact hmul
    have hRmul := hR.mulUp c u
    exact Fl.le_trans hfl hRmul
  · -- case ¬ 0 ≤ c, i.e., c < 0
    have hmul : c * x ≤ c * l := mul_le_mul_of_nonpos_left hl (by linarith)
    have hfl : Fl.le (.ofReal (c * x)) (.ofReal (c * l)) := by
      rw [Fl.ofReal_le_ofReal]
      exact hmul
    have hRmul := hR.mulUp c l
    exact Fl.le_trans hfl hRmul

theorem foldl_addDn_le {R : Rnd} (hR : R.Sound) {α : Type} (l : List α)
    (f : α → Fl) (y : α → ℝ) (hf : ∀ t ∈ l, Fl.le (f t) (.ofReal (y t))) (a : Fl) (s : ℝ)
    (ha : Fl.le a (.ofReal s)) :
    Fl.le ((l.map f).foldl R.addDn a) (.ofReal (s + (l.map y).sum)) := by
  revert hf
  induction l generalizing a s with
  | nil =>
    intro hf
    simp [ha]
  | cons t l ih =>
    intro hf
    simp only [List.map_cons, List.foldl_cons, List.sum_cons]
    have h_add : Fl.le (R.addDn a (f t)) (.ofReal (s + y t)) :=
      hR.addDn a (f t) s (y t) ha (hf t (by simp))
    have hf' : ∀ x ∈ l, Fl.le (f x) (.ofReal (y x)) := by
      intro x hx; exact hf x (by simp [hx])
    have h_ih := ih (R.addDn a (f t)) (s + y t) h_add hf'
    simpa [add_assoc] using h_ih

theorem le_foldl_addUp {R : Rnd} (hR : R.Sound) {α : Type} (l : List α)
    (g : α → Fl) (y : α → ℝ) (hg : ∀ t ∈ l, Fl.le (.ofReal (y t)) (g t)) (a : Fl) (s : ℝ)
    (ha : Fl.le (.ofReal s) a) :
    Fl.le (.ofReal (s + (l.map y).sum)) ((l.map g).foldl R.addUp a) := by
  induction l generalizing a s with
  | nil =>
      simpa [add_zero] using ha
  | cons t l' ih =>
      have hg_t : Fl.le (.ofReal (y t)) (g t) := hg t (by simp)
      have hg_rest : ∀ t' ∈ l', Fl.le (.ofReal (y t')) (g t') := by
        intro t' ht'
        apply hg t'
        simp [ht']
      have h_add : Fl.le (.ofReal (s + y t)) (R.addUp a (g t)) :=
        hR.addUp a (g t) s (y t) ha hg_t
      have ih' := ih hg_rest (R.addUp a (g t)) (s + y t) h_add
      simpa [List.sum_cons, List.map_cons, List.foldl_cons, add_assoc] using ih'

theorem addDn_ninf_left {R : Rnd} (hR : R.Sound) {b : Fl} {y : ℝ} (hb : Fl.le b (.ofReal y)) :
    R.addDn Fl.ninf b = Fl.ninf :=
  Fl.eq_ninf_of_le_all fun r => by
    simpa using hR.addDn Fl.ninf b (r - y) y (Fl.ninf_le _) hb

theorem addDn_ninf_right {R : Rnd} (hR : R.Sound) {a : Fl} {x : ℝ} (ha : Fl.le a (.ofReal x)) :
    R.addDn a Fl.ninf = Fl.ninf :=
  Fl.eq_ninf_of_le_all fun r => by
    simpa using hR.addDn a Fl.ninf x (r - x) ha (Fl.ninf_le _)

theorem addUp_inf_left {R : Rnd} (hR : R.Sound) {b : Fl} {y : ℝ} (hb : Fl.le (.ofReal y) b) :
    R.addUp Fl.inf b = Fl.inf :=
  Fl.eq_inf_of_ge_all fun r => by
    simpa using hR.addUp Fl.inf b (r - y) y (Fl.le_inf _) hb

theorem addUp_inf_right {R : Rnd} (hR : R.Sound) {a : Fl} {x : ℝ} (ha : Fl.le (.ofReal x) a) :
    R.addUp a Fl.inf = Fl.inf :=
  Fl.eq_inf_of_ge_all fun r => by
    simpa using hR.addUp a Fl.inf x (r - x) ha (Fl.le_inf _)

/-- A directed sum with a `-∞` term (or start) is `-∞`. -/
theorem foldl_addDn_eq_ninf {R : Rnd} (hR : R.Sound) {α : Type} (l : List α) (f : α → Fl)
    (y : α → ℝ) (hf : ∀ t ∈ l, Fl.le (f t) (.ofReal (y t))) (a : Fl) (s : ℝ)
    (ha : Fl.le a (.ofReal s)) (h : a = Fl.ninf ∨ ∃ t ∈ l, f t = Fl.ninf) :
    (l.map f).foldl R.addDn a = Fl.ninf := by
  induction l generalizing a s with
  | nil =>
    rcases h with h | ⟨t, ht, -⟩
    · simpa using h
    · simp at ht
  | cons t l ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hft := hf t (by simp)
    refine ih (fun u hu => hf u (List.mem_cons_of_mem _ hu)) _ (s + y t)
      (hR.addDn a (f t) s (y t) ha hft) ?_
    rcases h with h | ⟨u, hu, hfu⟩
    · left; rw [h]; exact addDn_ninf_left hR hft
    · rcases List.mem_cons.mp hu with rfl | hu
      · left; rw [hfu]; exact addDn_ninf_right hR ha
      · right; exact ⟨u, hu, hfu⟩

/-- A directed sum with a `∞` term (or start) is `∞`. -/
theorem foldl_addUp_eq_inf {R : Rnd} (hR : R.Sound) {α : Type} (l : List α) (g : α → Fl)
    (y : α → ℝ) (hg : ∀ t ∈ l, Fl.le (.ofReal (y t)) (g t)) (a : Fl) (s : ℝ)
    (ha : Fl.le (.ofReal s) a) (h : a = Fl.inf ∨ ∃ t ∈ l, g t = Fl.inf) :
    (l.map g).foldl R.addUp a = Fl.inf := by
  induction l generalizing a s with
  | nil =>
    rcases h with h | ⟨t, ht, -⟩
    · simpa using h
    · simp at ht
  | cons t l ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hgt := hg t (by simp)
    refine ih (fun u hu => hg u (List.mem_cons_of_mem _ hu)) _ (s + y t)
      (hR.addUp a (g t) s (y t) ha hgt) ?_
    rcases h with h | ⟨u, hu, hgu⟩
    · left; rw [h]; exact addUp_inf_left hR hgt
    · rcases List.mem_cons.mp hu with rfl | hu
      · left; rw [hgu]; exact addUp_inf_right hR ha
      · right; exact ⟨u, hu, hgu⟩

/-- One term out of a sum of nonnegative gaps. -/
theorem sum_sub_le_sum_sub {α : Type} (l : List α) (y z : α → ℝ) (h : ∀ u ∈ l, z u ≤ y u)
    {t : α} (ht : t ∈ l) : (l.map z).sum - z t ≤ (l.map y).sum - y t := by
  induction l with
  | nil => simp at ht
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (by simp)
    have hl : ∀ u ∈ l, z u ≤ y u := fun u hu => h u (List.mem_cons_of_mem _ hu)
    have hsum : (l.map z).sum ≤ (l.map y).sum := List.sum_le_sum hl
    rcases List.mem_cons.mp ht with rfl | ht'
    · linarith
    · have := ih hl ht'
      linarith

theorem subDn_foldl_addDn {R : Rnd} (hR : R.Sound) {α : Type} (l : List α)
    (f : α → Fl) (y : α → ℝ) (hf : ∀ t ∈ l, Fl.le (f t) (.ofReal (y t))) {t : α} (ht : t ∈ l) :
    R.subDn ((l.map f).foldl R.addDn (.ofReal 0)) (f t) = .nan ∨
      Fl.le (R.subDn ((l.map f).foldl R.addDn (.ofReal 0)) (f t))
        (.ofReal ((l.map y).sum - y t)) := by
  by_cases hn : ∃ u ∈ l, f u = Fl.ninf
  · rw [foldl_addDn_eq_ninf hR l f y hf (.ofReal 0) 0 (Fl.ofReal_le_ofReal.mpr le_rfl)
      (Or.inr hn)]
    by_cases hft : f t = Fl.ninf
    · left; rw [hft]; exact hR.subDn_ninf
    · right
      have hz := (Fl.eq_ofReal_of_le (hf t ht) hft).1
      have hle : Fl.le (.ofReal (f t).toReal) (f t) := by
        nth_rewrite 2 [hz]; exact Fl.ofReal_le_ofReal.mpr le_rfl
      simpa using hR.subDn Fl.ninf (f t) ((l.map y).sum - y t + (f t).toReal) (f t).toReal
        (Fl.ninf_le _) hle
  · push Not at hn
    right
    have hz : ∀ u ∈ l, f u = .ofReal (f u).toReal ∧ (f u).toReal ≤ y u :=
      fun u hu => Fl.eq_ofReal_of_le (hf u hu) (hn u hu)
    have h1 := foldl_addDn_le hR l f (fun u => (f u).toReal)
      (fun u hu => by nth_rewrite 1 [(hz u hu).1]; exact Fl.ofReal_le_ofReal.mpr (by simp))
      (.ofReal 0) 0 (Fl.ofReal_le_ofReal.mpr le_rfl)
    have hle : Fl.le (.ofReal (f t).toReal) (f t) := by
      nth_rewrite 2 [(hz t ht).1]; exact Fl.ofReal_le_ofReal.mpr le_rfl
    refine Fl.le_trans (hR.subDn _ (f t) _ (f t).toReal h1 hle) (Fl.ofReal_le_ofReal.mpr ?_)
    have := sum_sub_le_sum_sub l y (fun u => (f u).toReal) (fun u hu => (hz u hu).2) ht
    simpa using this

theorem subUp_foldl_addUp {R : Rnd} (hR : R.Sound) {α : Type} (l : List α)
    (g : α → Fl) (y : α → ℝ) (hg : ∀ t ∈ l, Fl.le (.ofReal (y t)) (g t)) {t : α} (ht : t ∈ l) :
    R.subUp ((l.map g).foldl R.addUp (.ofReal 0)) (g t) = .nan ∨
      Fl.le (.ofReal ((l.map y).sum - y t))
        (R.subUp ((l.map g).foldl R.addUp (.ofReal 0)) (g t)) := by
  by_cases hn : ∃ u ∈ l, g u = Fl.inf
  · rw [foldl_addUp_eq_inf hR l g y hg (.ofReal 0) 0 (Fl.ofReal_le_ofReal.mpr le_rfl)
      (Or.inr hn)]
    by_cases hgt : g t = Fl.inf
    · left; rw [hgt]; exact hR.subUp_inf
    · right
      have hz := (Fl.eq_ofReal_of_ge (hg t ht) hgt).1
      have hle : Fl.le (g t) (.ofReal (g t).toReal) := by
        nth_rewrite 1 [hz]; exact Fl.ofReal_le_ofReal.mpr (by simp)
      simpa using hR.subUp Fl.inf (g t) ((l.map y).sum - y t + (g t).toReal) (g t).toReal
        (Fl.le_inf _) hle
  · push Not at hn
    right
    have hz : ∀ u ∈ l, g u = .ofReal (g u).toReal ∧ y u ≤ (g u).toReal :=
      fun u hu => Fl.eq_ofReal_of_ge (hg u hu) (hn u hu)
    have h1 := le_foldl_addUp hR l g (fun u => (g u).toReal)
      (fun u hu => by nth_rewrite 2 [(hz u hu).1]; exact Fl.ofReal_le_ofReal.mpr (by simp))
      (.ofReal 0) 0 (Fl.ofReal_le_ofReal.mpr le_rfl)
    have hle : Fl.le (g t) (.ofReal (g t).toReal) := by
      nth_rewrite 1 [(hz t ht).1]; exact Fl.ofReal_le_ofReal.mpr (by simp)
    refine Fl.le_trans (Fl.ofReal_le_ofReal.mpr ?_) (hR.subUp _ (g t) _ (g t).toReal h1 hle)
    have := sum_sub_le_sum_sub l (fun u => (g u).toReal) y (fun u hu => (hz u hu).2) ht
    simpa using this

theorem rowUpd_cup {R : Rnd} (hR : R.Sound) {hi omin : Fl} {S X : ℝ}
    (hhi : Fl.le (.ofReal S) hi) (h : omin = .nan ∨ Fl.le omin (.ofReal (S - X)))
    (hfin : (if hi.IsFinite then R.subUp hi omin else Fl.inf).IsFinite) :
    Fl.le (.ofReal X) (if hi.IsFinite then R.subUp hi omin else Fl.inf) := by
  by_cases hfin_hi : hi.IsFinite
  · rw [if_pos hfin_hi]
    have hfin' : (R.subUp hi omin).IsFinite := by
      simpa [if_pos hfin_hi] using hfin
    rcases h with (hnan | hle)
    · rw [hnan, hR.subUp_nan] at hfin'
      simp [Fl.IsFinite] at hfin'
    · have hsub := hR.subUp hi omin S (S - X) hhi hle
      have h_eq : S - (S - X) = X := by ring
      rw [h_eq] at hsub
      exact hsub
  · rw [if_neg hfin_hi]
    simp [Fl.inf, Fl.le, Fl.ofReal, le_top]

theorem rowUpd_cdn {R : Rnd} (hR : R.Sound) {lo omax : Fl} {S X : ℝ}
    (hlo : Fl.le lo (.ofReal S)) (h : omax = .nan ∨ Fl.le (.ofReal (S - X)) omax)
    (hfin : (if lo.IsFinite then R.subDn lo omax else Fl.ninf).IsFinite) :
    Fl.le (if lo.IsFinite then R.subDn lo omax else Fl.ninf) (.ofReal X) := by
  by_cases hfi : lo.IsFinite
  · cases lo with
    | nan =>
      simp [Fl.IsFinite] at hfi
    | num a =>
      simp only [Fl.IsFinite, Fl.ofReal] at hlo hfi
      have h_omax_le : Fl.le (.ofReal (S - X)) omax := by
        rcases h with (rfl | hle)
        · exfalso
          have hnan : R.subDn (.num a) (.nan) = .nan := hR.subDn_nan (.num a)
          have hfin' := hfin
          -- hfin : (if (Fl.num a).IsFinite then R.subDn (Fl.num a) Fl.nan else Fl.ninf).IsFinite
          -- Since (Fl.num a).IsFinite is true, the if reduces to R.subDn (Fl.num a) Fl.nan = .nan
          -- and .nan.IsFinite is false
          simp [Fl.IsFinite, hnan, hfi] at hfin'
        · exact hle
      have hsub := hR.subDn (.num a) omax S (S - X) hlo h_omax_le
      have hsub' : Fl.le (R.subDn (.num a) omax) (.ofReal X) := by
        simpa [EReal.coe_sub, sub_sub, add_comm, add_left_comm, add_assoc] using hsub
      simpa [Fl.IsFinite, hfi] using hsub'
  · simp [hfi, Fl.le, Fl.ninf]
    exact bot_le

/-- A finite float equals `ofReal` of its `toReal`. -/
theorem isFinite_eq_ofReal_toReal {a : Fl} (h : a.IsFinite) : a = .ofReal a.toReal := by
  cases a with
  | nan => simp [Fl.IsFinite] at h
  | num z =>
    simp [Fl.IsFinite, Fl.ofReal, Fl.toReal] at h ⊢
    rcases h with ⟨hz, hz'⟩
    have h_eq := EReal.coe_toReal hz hz'
    simpa using congrArg Fl.num h_eq.symm

theorem rowUpd_bounds {R : Rnd} (hR : R.Sound) {c xv : ℝ} {cup cdn : Fl}
    (hc : c ≠ 0) (hcup : cup.IsFinite → Fl.le (.ofReal (c * xv)) cup)
    (hcdn : cdn.IsFinite → Fl.le cdn (.ofReal (c * xv))) :
    Fl.le (if 0 < c then (if cdn.IsFinite then R.divDn cdn (.ofReal c) else Fl.ninf)
        else (if cup.IsFinite then R.divDn cup (.ofReal c) else Fl.ninf)) (.ofReal xv) ∧
      Fl.le (.ofReal xv) (if 0 < c then (if cup.IsFinite then R.divUp cup (.ofReal c) else Fl.inf)
        else (if cdn.IsFinite then R.divUp cdn (.ofReal c) else Fl.inf)) := by
  have h_lt_or : c < 0 ∨ 0 < c := lt_or_gt_of_ne hc
  rcases h_lt_or with (h_neg | h_pos)
  · -- case c < 0
    constructor
    · -- lower bound
      by_cases h_pos' : 0 < c
      · linarith
      · rw [ite_eq_right h_pos']
        by_cases h_cup_fin : cup.IsFinite
        · rw [ite_eq_left h_cup_fin]
          have h_cup_eq : cup = .ofReal cup.toReal := isFinite_eq_ofReal_toReal h_cup_fin
          have h_cup_le : Fl.le (.ofReal (c * xv)) cup := hcup h_cup_fin
          have h_cup_le' : Fl.le (.ofReal (c * xv)) (.ofReal cup.toReal) :=
            h_cup_eq ▸ h_cup_le
          have h_cup_toReal : c * xv ≤ cup.toReal := by
            simpa [Fl.ofReal_le_ofReal] using h_cup_le'
          have h_divDn := hR.divDn cup.toReal c hc
          have h_divDn' : Fl.le (R.divDn cup (.ofReal c)) (.ofReal (cup.toReal / c)) :=
            h_cup_eq.symm ▸ h_divDn
          have h_div_le : Fl.le (.ofReal (cup.toReal / c)) (.ofReal xv) := by
            rw [Fl.ofReal_le_ofReal]
            rw [div_le_iff_of_neg h_neg]
            simpa [mul_comm] using h_cup_toReal
          exact Fl.le_trans h_divDn' h_div_le
        · rw [ite_eq_right h_cup_fin]
          dsimp [Fl.le, Fl.ninf, Fl.ofReal]
          exact bot_le
    · -- upper bound
      by_cases h_pos' : 0 < c
      · linarith
      · rw [ite_eq_right h_pos']
        by_cases h_cdn_fin : cdn.IsFinite
        · rw [ite_eq_left h_cdn_fin]
          have h_cdn_eq : cdn = .ofReal cdn.toReal := isFinite_eq_ofReal_toReal h_cdn_fin
          have h_cdn_le : Fl.le cdn (.ofReal (c * xv)) := hcdn h_cdn_fin
          have h_cdn_le' : Fl.le (.ofReal cdn.toReal) (.ofReal (c * xv)) :=
            h_cdn_eq ▸ h_cdn_le
          have h_cdn_toReal : cdn.toReal ≤ c * xv := by
            simpa [Fl.ofReal_le_ofReal] using h_cdn_le'
          have h_divUp := hR.divUp cdn.toReal c hc
          have h_divUp' : Fl.le (.ofReal (cdn.toReal / c)) (R.divUp cdn (.ofReal c)) :=
            h_cdn_eq.symm ▸ h_divUp
          have h_div_le' : Fl.le (.ofReal xv) (.ofReal (cdn.toReal / c)) := by
            rw [Fl.ofReal_le_ofReal]
            rw [le_div_iff_of_neg h_neg]
            simpa [mul_comm] using h_cdn_toReal
          exact Fl.le_trans h_div_le' h_divUp'
        · rw [ite_eq_right h_cdn_fin]
          dsimp [Fl.le, Fl.inf, Fl.ofReal]
          exact le_top
  · -- case 0 < c
    constructor
    · -- lower bound
      by_cases h_pos' : 0 < c
      · rw [ite_eq_left h_pos']
        by_cases h_cdn_fin : cdn.IsFinite
        · rw [ite_eq_left h_cdn_fin]
          have h_cdn_eq : cdn = .ofReal cdn.toReal := isFinite_eq_ofReal_toReal h_cdn_fin
          have h_cdn_le : Fl.le cdn (.ofReal (c * xv)) := hcdn h_cdn_fin
          have h_cdn_le' : Fl.le (.ofReal cdn.toReal) (.ofReal (c * xv)) :=
            h_cdn_eq ▸ h_cdn_le
          have h_cdn_toReal : cdn.toReal ≤ c * xv := by
            simpa [Fl.ofReal_le_ofReal] using h_cdn_le'
          have h_divDn := hR.divDn cdn.toReal c hc
          have h_divDn' : Fl.le (R.divDn cdn (.ofReal c)) (.ofReal (cdn.toReal / c)) :=
            h_cdn_eq.symm ▸ h_divDn
          have h_div_le : Fl.le (.ofReal (cdn.toReal / c)) (.ofReal xv) := by
            rw [Fl.ofReal_le_ofReal]
            rw [div_le_iff₀ h_pos]
            simpa [mul_comm] using h_cdn_toReal
          exact Fl.le_trans h_divDn' h_div_le
        · rw [ite_eq_right h_cdn_fin]
          dsimp [Fl.le, Fl.ninf, Fl.ofReal]
          exact bot_le
      · linarith
    · -- upper bound
      by_cases h_pos' : 0 < c
      · rw [ite_eq_left h_pos']
        by_cases h_cup_fin : cup.IsFinite
        · rw [ite_eq_left h_cup_fin]
          have h_cup_eq : cup = .ofReal cup.toReal := isFinite_eq_ofReal_toReal h_cup_fin
          have h_cup_le : Fl.le (.ofReal (c * xv)) cup := hcup h_cup_fin
          have h_cup_le' : Fl.le (.ofReal (c * xv)) (.ofReal cup.toReal) :=
            h_cup_eq ▸ h_cup_le
          have h_cup_toReal : c * xv ≤ cup.toReal := by
            simpa [Fl.ofReal_le_ofReal] using h_cup_le'
          have h_divUp := hR.divUp cup.toReal c hc
          have h_divUp' : Fl.le (.ofReal (cup.toReal / c)) (R.divUp cup (.ofReal c)) :=
            h_cup_eq.symm ▸ h_divUp
          have h_div_le' : Fl.le (.ofReal xv) (.ofReal (cup.toReal / c)) := by
            rw [Fl.ofReal_le_ofReal]
            rw [le_div_iff₀ h_pos]
            simpa [mul_comm] using h_cup_toReal
          exact Fl.le_trans h_div_le' h_divUp'
        · rw [ite_eq_right h_cup_fin]
          dsimp [Fl.le, Fl.inf, Fl.ofReal]
          exact le_top
      · linarith

theorem rowUpd_box {ι : Type} {B : Box ι} {x : ι → ℝ} (hx : B.Mem x)
    (v : ι) {nlo nhi : Fl} (h1 : Fl.le nlo (.ofReal (x v))) (h2 : Fl.le (.ofReal (x v)) nhi) :
    ¬ ((if Fl.lt nhi (.ofReal (B.hi v)) then nhi.toReal else B.hi v) <
        (if Fl.lt (.ofReal (B.lo v)) nlo then nlo.toReal else B.lo v)) ∧
      (⟨Function.update B.lo v (if Fl.lt (.ofReal (B.lo v)) nlo then nlo.toReal else B.lo v),
        Function.update B.hi v (if Fl.lt nhi (.ofReal (B.hi v)) then nhi.toReal else B.hi v)⟩ :
          Box ι).Mem x := by
  set lo' := if Fl.lt (.ofReal (B.lo v)) nlo then nlo.toReal else B.lo v with hlo'
  set hi' := if Fl.lt nhi (.ofReal (B.hi v)) then nhi.toReal else B.hi v with hhi'
  have hlo'_le_xv : lo' ≤ x v := by
    by_cases hcond : Fl.lt (.ofReal (B.lo v)) nlo
    · rw [hlo', if_pos hcond]
      have hle1 : Fl.le (.ofReal (B.lo v)) nlo := Fl.le_of_lt hcond
      exact (Fl.le_ofReal_toReal hle1 h1).2
    · rw [hlo', if_neg hcond]
      exact (hx v).1
  have hxv_le_hi' : x v ≤ hi' := by
    by_cases hcond : Fl.lt nhi (.ofReal (B.hi v))
    · rw [hhi', if_pos hcond]
      have hle_nhi : Fl.le nhi (.ofReal (B.hi v)) := Fl.le_of_lt hcond
      exact (Fl.le_ofReal_toReal h2 hle_nhi).1
    · rw [hhi', if_neg hcond]
      exact (hx v).2
  have h_not_lt : ¬ (hi' < lo') := by
    intro hlt
    have hle : lo' ≤ hi' := le_trans hlo'_le_xv hxv_le_hi'
    linarith
  have h_mem : (⟨Function.update B.lo v lo', Function.update B.hi v hi'⟩ : Box ι).Mem x := by
    intro i
    by_cases hi_eq_v : i = v
    · subst hi_eq_v
      -- goal: (Function.update B.lo v lo') v ≤ x v ∧ x v ≤ (Function.update B.hi v hi') v
      -- which simplifies to lo' ≤ x v ∧ x v ≤ hi'
      simp [Function.update_self, hlo'_le_xv, hxv_le_hi']
    · -- goal: (Function.update B.lo v lo') i ≤ x i ∧ x i ≤ (Function.update B.hi v hi') i
      -- which simplifies to B.lo i ≤ x i ∧ x i ≤ B.hi i
      simp [hi_eq_v, hx i]
  exact And.intro h_not_lt h_mem

theorem rowUpd_sound {R : Rnd} (hR : R.Sound) {ι : Type} (r : Row ι)
    (smin smax : Fl) {x : ι → ℝ} (S : ℝ) (hlo : Fl.le r.lo (.ofReal S))
    (hhi : Fl.le (.ofReal S) r.hi) :
    ∀ (L : List ((ι × ℝ) × Fl × Fl)) (B : Box ι), B.Mem x →
      (∀ p ∈ L, (R.subDn smin p.2.1 = .nan ∨
          Fl.le (R.subDn smin p.2.1) (.ofReal (S - p.1.2 * x p.1.1))) ∧
        (R.subUp smax p.2.2 = .nan ∨
          Fl.le (.ofReal (S - p.1.2 * x p.1.1)) (R.subUp smax p.2.2))) →
      ∃ B', rowUpd R r smin smax L B = some B' ∧ B'.Mem x := by
  intro L
  induction L with
  | nil =>
    intro B hB hL
    refine ⟨B, ?_, hB⟩
    rfl
  | cons p L ih =>
    intro B hB hL
    obtain ⟨⟨v, c⟩, mn, mx⟩ := p
    by_cases hc : c = 0
    · simp only [rowUpd, hc, ↓reduceIte]
      apply ih B hB
      intro q hq
      apply hL q
      exact List.mem_cons_of_mem _ hq
    · rw [rowUpd]
      simp only [hc, ↓reduceIte]
      have hLp := hL ((v, c), mn, mx) (by simp)
      rcases hLp with ⟨hsubDn, hsubUp⟩
      -- simplify the projection types in hsubDn and hsubUp
      have hsubDn_simp : R.subDn smin mn = .nan ∨ Fl.le (R.subDn smin mn) (.ofReal (S - c * x v)) := by
        simpa using hsubDn
      have hsubUp_simp : R.subUp smax mx = .nan ∨ Fl.le (.ofReal (S - c * x v)) (R.subUp smax mx) := by
        simpa using hsubUp
      set omin := R.subDn smin mn with h_omin
      set omax := R.subUp smax mx with h_omax
      set cup := if r.hi.IsFinite then R.subUp r.hi omin else Fl.inf with h_cup
      set cdn := if r.lo.IsFinite then R.subDn r.lo omax else Fl.ninf with h_cdn
      -- prove cup.IsFinite → Fl.le (.ofReal (c * x v)) cup
      have hcup_fn : cup.IsFinite → Fl.le (.ofReal (c * x v)) cup := by
        intro hfin
        have hhi_fin : r.hi.IsFinite := by
          by_contra h
          dsimp [cup] at hfin
          have : (if r.hi.IsFinite then R.subUp r.hi omin else Fl.inf) = Fl.inf := by simp [h]
          rw [this] at hfin
          have : ¬ Fl.inf.IsFinite := by
            simp [Fl.IsFinite, Fl.inf]
          exact this hfin
        have hcup_eq : cup = R.subUp r.hi omin := by
          simp [cup, hhi_fin]
        have h_omin_not_nan : omin ≠ .nan := by
          intro h_eq
          have h_not_fin : ¬ (R.subUp r.hi .nan).IsFinite := by
            simp [Fl.IsFinite, hR.subUp_nan]
          rw [h_eq] at hcup_eq
          rw [hcup_eq] at hfin
          exact h_not_fin hfin
        have hsubDn_le' : Fl.le omin (.ofReal (S - c * x v)) := by
          rcases hsubDn_simp with (h_eq | h_le)
          · exact absurd h_eq h_omin_not_nan
          · exact h_le
        have h := hR.subUp r.hi omin S (S - c * x v) hhi hsubDn_le'
        have hsub : S - (S - c * x v) = c * x v := by ring
        rw [hcup_eq]
        simpa [hsub] using h
      -- prove cdn.IsFinite → Fl.le cdn (.ofReal (c * x v))
      have hcdn_fn : cdn.IsFinite → Fl.le cdn (.ofReal (c * x v)) := by
        intro hfin
        have hlo_fin : r.lo.IsFinite := by
          by_contra h
          dsimp [cdn] at hfin
          have : (if r.lo.IsFinite then R.subDn r.lo omax else Fl.ninf) = Fl.ninf := by simp [h]
          rw [this] at hfin
          have : ¬ Fl.ninf.IsFinite := by
            simp [Fl.IsFinite, Fl.ninf]
          exact this hfin
        have hcdn_eq : cdn = R.subDn r.lo omax := by
          simp [cdn, hlo_fin]
        have h_omax_not_nan : omax ≠ .nan := by
          intro h_eq
          have h_not_fin : ¬ (R.subDn r.lo .nan).IsFinite := by
            simp [Fl.IsFinite, hR.subDn_nan]
          rw [h_eq] at hcdn_eq
          rw [hcdn_eq] at hfin
          exact h_not_fin hfin
        have hsubUp_le' : Fl.le (.ofReal (S - c * x v)) omax := by
          rcases hsubUp_simp with (h_eq | h_le)
          · exact absurd h_eq h_omax_not_nan
          · exact h_le
        have h := hR.subDn r.lo omax S (S - c * x v) hlo hsubUp_le'
        have hsub : S - (S - c * x v) = c * x v := by ring
        rw [hcdn_eq]
        simpa [hsub] using h
      -- use rowUpd_bounds to get bounds on nlo and nhi
      have hbounds := rowUpd_bounds hR hc hcup_fn hcdn_fn
      rcases hbounds with ⟨hnlo, hnhi⟩
      -- use rowUpd_box to show the box is not empty and the updated box holds x
      have hbox := rowUpd_box hB v hnlo hnhi
      rcases hbox with ⟨hnotlt, hmem⟩
      -- Now the goal is:
      -- ∃ B', (if <cond> then none else rowUpd ... L (updated box)) = some B' ∧ B'.Mem x
      -- We split on the condition
      by_cases hlt : (if Fl.lt (if 0 < c then if cup.IsFinite then R.divUp cup (Fl.ofReal c) else Fl.inf
          else if cdn.IsFinite then R.divUp cdn (Fl.ofReal c) else Fl.inf) (.ofReal (B.hi v)) then
        (if 0 < c then if cup.IsFinite then R.divUp cup (Fl.ofReal c) else Fl.inf
          else if cdn.IsFinite then R.divUp cdn (Fl.ofReal c) else Fl.inf).toReal
        else B.hi v) <
        (if Fl.lt (.ofReal (B.lo v)) (if 0 < c then if cdn.IsFinite then R.divDn cdn (Fl.ofReal c) else Fl.ninf
          else if cup.IsFinite then R.divDn cup (Fl.ofReal c) else Fl.ninf) then
          (if 0 < c then if cdn.IsFinite then R.divDn cdn (Fl.ofReal c) else Fl.ninf
            else if cup.IsFinite then R.divDn cup (Fl.ofReal c) else Fl.ninf).toReal
          else B.lo v)
      · exfalso; exact hnotlt hlt
      · -- hlt is false, so the if reduces to the else branch
        have hL_tail : ∀ p ∈ L, (R.subDn smin p.2.1 = .nan ∨
            Fl.le (R.subDn smin p.2.1) (.ofReal (S - p.1.2 * x p.1.1))) ∧
          (R.subUp smax p.2.2 = .nan ∨
            Fl.le (.ofReal (S - p.1.2 * x p.1.1)) (R.subUp smax p.2.2)) := by
          intro q hq
          apply hL q
          exact List.mem_cons_of_mem _ hq
        simp [hlt]
        exact ih _ hmem hL_tail

theorem alphaIv_mem {R : Rnd} (hR : R.Sound) {lo hi x : ℝ} (h0 : 0 < lo)
    (hlo : lo ≤ x) (hhi : x ≤ hi) (h1 : hi < π / 2) :
    (alphaIv R (Iv.ofReal lo hi)).Mem (alpha x) := by
  let f : Fl → Iv := fun x =>
    let c := R.cos (Iv.pt x)
    R.acos (R.div c (R.add c (Iv.pt (.ofReal 1))))
  have h_alpha_mono : MonotoneOn alpha (Set.Ioo (0 : ℝ) (π / 2)) :=
    alpha_strictMonoOn.monotoneOn
  have hlo_lt_pi_div_two : lo < π / 2 :=
    lt_of_le_of_lt (le_trans hlo hhi) h1
  have hx_lt_pi_div_two : x < π / 2 :=
    lt_of_le_of_lt hhi h1
  have hlo_mem_Ioo : lo ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, hlo_lt_pi_div_two⟩
  have hx_mem_Ioo : x ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨lt_of_lt_of_le h0 hlo, hx_lt_pi_div_two⟩
  have hhi_mem_Ioo : hi ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨lt_of_lt_of_le h0 (le_trans hlo hhi), h1⟩
  have h_alpha_lo_le_alpha_x : alpha lo ≤ alpha x :=
    h_alpha_mono hlo_mem_Ioo hx_mem_Ioo hlo
  have h_alpha_x_le_alpha_hi : alpha x ≤ alpha hi :=
    h_alpha_mono hx_mem_Ioo hhi_mem_Ioo hhi
  have h_cos_lo_pos : 0 < Real.cos lo :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hlo_lt_pi_div_two⟩
  have h_cos_hi_pos : 0 < Real.cos hi :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have h_cos_lo_plus_one_ne_zero : Real.cos lo + 1 ≠ 0 := by linarith
  have h_cos_hi_plus_one_ne_zero : Real.cos hi + 1 ≠ 0 := by linarith
  have h_cos_lo_div_le_one : Real.cos lo / (Real.cos lo + 1) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have h_cos_hi_div_le_one : Real.cos hi / (Real.cos hi + 1) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have h_cos_lo_div_ge_neg_one : -1 ≤ Real.cos lo / (Real.cos lo + 1) := by
    have h : 0 ≤ Real.cos lo / (Real.cos lo + 1) := div_nonneg (by linarith) (by linarith)
    linarith
  have h_cos_hi_div_ge_neg_one : -1 ≤ Real.cos hi / (Real.cos hi + 1) := by
    have h : 0 ≤ Real.cos hi / (Real.cos hi + 1) := div_nonneg (by linarith) (by linarith)
    linarith
  -- Build the soundness proof for the lower bound
  have h_cos_lo_mem : (R.cos (Iv.pt (Fl.ofReal lo))).Mem (Real.cos lo) :=
    hR.cos (Iv.pt (Fl.ofReal lo)) lo (Iv.mem_pt)
  have h_one_mem : (Iv.pt (.ofReal (1 : ℝ))).Mem (1 : ℝ) := Iv.mem_pt
  have h_denom_lo_mem : (R.add (R.cos (Iv.pt (Fl.ofReal lo))) (Iv.pt (.ofReal 1))).Mem (Real.cos lo + 1) :=
    hR.add (R.cos (Iv.pt (Fl.ofReal lo))) (Iv.pt (.ofReal 1)) (Real.cos lo) 1 h_cos_lo_mem h_one_mem
  have h_quot_lo_mem : (R.div (R.cos (Iv.pt (Fl.ofReal lo))) (R.add (R.cos (Iv.pt (Fl.ofReal lo))) (Iv.pt (.ofReal 1)))).Mem (Real.cos lo / (Real.cos lo + 1)) :=
    hR.div (R.cos (Iv.pt (Fl.ofReal lo))) (R.add (R.cos (Iv.pt (Fl.ofReal lo))) (Iv.pt (.ofReal 1))) (Real.cos lo) (Real.cos lo + 1) h_cos_lo_mem h_denom_lo_mem h_cos_lo_plus_one_ne_zero
  have h_f_lo_mem : (f (Fl.ofReal lo)).Mem (Real.arccos (Real.cos lo / (Real.cos lo + 1))) :=
    hR.acos (R.div (R.cos (Iv.pt (Fl.ofReal lo))) (R.add (R.cos (Iv.pt (Fl.ofReal lo))) (Iv.pt (.ofReal 1)))) (Real.cos lo / (Real.cos lo + 1)) h_quot_lo_mem h_cos_lo_div_ge_neg_one h_cos_lo_div_le_one
  have h_alpha_lo_eq : Real.arccos (Real.cos lo / (Real.cos lo + 1)) = alpha lo := by
    rw [Tammes15.alpha, add_comm]
  have h_f_lo_mem_alpha_lo : (f (Fl.ofReal lo)).Mem (alpha lo) := by
    rw [h_alpha_lo_eq] at h_f_lo_mem
    exact h_f_lo_mem
  have h_lower_fl : Fl.le ((f (Fl.ofReal lo)).lo) (Fl.ofReal (alpha lo)) :=
    h_f_lo_mem_alpha_lo.1
  have h_upper_fl_lo : Fl.le (Fl.ofReal (alpha lo)) ((f (Fl.ofReal lo)).hi) :=
    h_f_lo_mem_alpha_lo.2
  -- Build the soundness proof for the upper bound
  have h_cos_hi_mem : (R.cos (Iv.pt (Fl.ofReal hi))).Mem (Real.cos hi) :=
    hR.cos (Iv.pt (Fl.ofReal hi)) hi (Iv.mem_pt)
  have h_denom_hi_mem : (R.add (R.cos (Iv.pt (Fl.ofReal hi))) (Iv.pt (.ofReal 1))).Mem (Real.cos hi + 1) :=
    hR.add (R.cos (Iv.pt (Fl.ofReal hi))) (Iv.pt (.ofReal 1)) (Real.cos hi) 1 h_cos_hi_mem h_one_mem
  have h_quot_hi_mem : (R.div (R.cos (Iv.pt (Fl.ofReal hi))) (R.add (R.cos (Iv.pt (Fl.ofReal hi))) (Iv.pt (.ofReal 1)))).Mem (Real.cos hi / (Real.cos hi + 1)) :=
    hR.div (R.cos (Iv.pt (Fl.ofReal hi))) (R.add (R.cos (Iv.pt (Fl.ofReal hi))) (Iv.pt (.ofReal 1))) (Real.cos hi) (Real.cos hi + 1) h_cos_hi_mem h_denom_hi_mem h_cos_hi_plus_one_ne_zero
  have h_f_hi_mem : (f (Fl.ofReal hi)).Mem (Real.arccos (Real.cos hi / (Real.cos hi + 1))) :=
    hR.acos (R.div (R.cos (Iv.pt (Fl.ofReal hi))) (R.add (R.cos (Iv.pt (Fl.ofReal hi))) (Iv.pt (.ofReal 1)))) (Real.cos hi / (Real.cos hi + 1)) h_quot_hi_mem h_cos_hi_div_ge_neg_one h_cos_hi_div_le_one
  have h_alpha_hi_eq : Real.arccos (Real.cos hi / (Real.cos hi + 1)) = alpha hi := by
    rw [Tammes15.alpha, add_comm]
  have h_f_hi_mem_alpha_hi : (f (Fl.ofReal hi)).Mem (alpha hi) := by
    rw [h_alpha_hi_eq] at h_f_hi_mem
    exact h_f_hi_mem
  have h_lower_fl_hi : Fl.le ((f (Fl.ofReal hi)).lo) (Fl.ofReal (alpha hi)) :=
    h_f_hi_mem_alpha_hi.1
  have h_upper_fl_hi : Fl.le (Fl.ofReal (alpha hi)) ((f (Fl.ofReal hi)).hi) :=
    h_f_hi_mem_alpha_hi.2
  -- Combine: Fl.le ((f lo).lo) (Fl.ofReal (alpha x))
  have h_alpha_lo_fl : Fl.le (Fl.ofReal (alpha lo)) (Fl.ofReal (alpha x)) :=
    (Fl.ofReal_le_ofReal.mpr h_alpha_lo_le_alpha_x)
  have h_lower_fl_final : Fl.le ((f (Fl.ofReal lo)).lo) (Fl.ofReal (alpha x)) :=
    Fl.le_trans h_lower_fl h_alpha_lo_fl
  have h_upper_fl_final : Fl.le (Fl.ofReal (alpha x)) ((f (Fl.ofReal hi)).hi) :=
    Fl.le_trans (Fl.ofReal_le_ofReal.mpr h_alpha_x_le_alpha_hi) h_upper_fl_hi
  -- Now we need to show the Iv.Mem condition
  unfold alphaIv
  simp [Iv.Mem, Iv.ofReal]
  exact ⟨h_lower_fl_final, h_upper_fl_final⟩

theorem alphaInvIv_mem {R : Rnd} (hR : R.Sound) {lo hi d : ℝ}
    (hd : 0 < d ∧ d < π / 2) (hlo : lo ≤ alpha d) (hhi : alpha d ≤ hi) (h0 : π / 3 < lo)
    (h1 : hi < π / 2) : (alphaInvIv R (Iv.ofReal lo hi)).Mem d := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hpi_pos : 0 < π := Real.pi_pos
  have hpi2_pos : 0 < π / 2 := by linarith
  have hlo_pos : 0 < lo := by linarith
  have hhi_pos : 0 < hi := by linarith
  have hlo_lt_pi2 : lo < π / 2 := by linarith
  have hhi_lt_pi2 : hi < π / 2 := h1
  have halpha_pos : π / 3 < alpha d := by linarith
  have halpha_lt_pi2 : alpha d < π / 2 := by linarith
  have hd_nonneg : 0 ≤ d := by linarith
  have hd_le_pi : d ≤ π := by linarith
  -- define g(a) = arccos(cos a / (1 - cos a))
  set g := fun (a : ℝ) => arccos (cos a / (1 - cos a)) with hg_def
  -- some basic facts about cos on (0, π/2)
  have hcos_pos : ∀ x, 0 < x → x < π / 2 → 0 < cos x := by
    intro x hxpos hxlt
    have hx_lower : -(π / 2) < x := by linarith
    exact Real.cos_pos_of_mem_Ioo ⟨hx_lower, hxlt⟩
  have hcos_lt_one : ∀ x, 0 < x → x < π / 2 → cos x < 1 := by
    intro x hxpos hxlt
    have hxle : x ≤ π := by linarith
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) hxle hxpos
    simpa [Real.cos_zero] using h
  have hcos_decreasing : ∀ x y, 0 ≤ x → y ≤ π → x ≤ y → cos y ≤ cos x :=
    fun x y hx hy hxy => Real.cos_le_cos_of_nonneg_of_le_pi hx hy hxy
  -- prove g(alpha d) = d
  have hg_alpha : g (alpha d) = d := by
    dsimp [g, alpha]
    have hcos_alpha : cos (arccos (cos d / (1 + cos d))) = cos d / (1 + cos d) := by
      apply Real.cos_arccos
      · -- -1 ≤ cos d / (1 + cos d)
        have hcos_d_pos : 0 < cos d := hcos_pos d hdpos hdlt
        have h_ratio_nonneg : 0 ≤ cos d / (1 + cos d) := div_nonneg (by linarith) (by linarith)
        linarith
      · -- cos d / (1 + cos d) ≤ 1
        have hcos_d_pos : 0 < cos d := hcos_pos d hdpos hdlt
        exact (div_le_one (by linarith)).mpr (by linarith)
    rw [hcos_alpha]
    have hcos_d_pos : 0 < cos d := hcos_pos d hdpos hdlt
    have hcos_d_lt_one : cos d < 1 := hcos_lt_one d hdpos hdlt
    have h_den_ne_zero : 1 + cos d ≠ 0 := by linarith
    have h_eq : (cos d / (1 + cos d)) / (1 - cos d / (1 + cos d)) = cos d := by
      field_simp [h_den_ne_zero]
      ring
    rw [h_eq]
    exact Real.arccos_cos hd_nonneg hd_le_pi
  -- prove g is monotone increasing on (π/3, π/2)
  have hg_mono : ∀ a b, π / 3 < a → b < π / 2 → a ≤ b → g a ≤ g b := by
    intro a b ha hb hle
    dsimp [g]
    have ha_pos : 0 < a := by linarith
    have hb_pos : 0 < b := by linarith
    have ha_le_pi : a ≤ π := by linarith
    have hb_le_pi : b ≤ π := by linarith
    have hcos_le : cos b ≤ cos a :=
      hcos_decreasing a b (by linarith) hb_le_pi hle
    have hcos_a_pos : 0 < cos a := hcos_pos a ha_pos (by linarith)
    have hcos_b_pos : 0 < cos b := hcos_pos b hb_pos (by linarith)
    have hcos_a_lt_one : cos a < 1 := hcos_lt_one a ha_pos (by linarith)
    have hcos_b_lt_one : cos b < 1 := hcos_lt_one b hb_pos (by linarith)
    -- arccos is antitone, so we need cos b / (1 - cos b) ≤ cos a / (1 - cos a)
    apply Real.arccos_le_arccos
    -- prove the division inequality
    have h_div_le : cos b / (1 - cos b) ≤ cos a / (1 - cos a) := by
      have h_den_a_pos : 0 < 1 - cos a := by linarith
      have h_den_b_pos : 0 < 1 - cos b := by linarith
      -- cos b / (1 - cos b) ≤ cos a / (1 - cos a)
      -- ↔ cos b * (1 - cos a) ≤ cos a * (1 - cos b)
      -- ↔ cos b - cos b * cos a ≤ cos a - cos a * cos b
      -- ↔ cos b ≤ cos a
      have h_eq : cos a / (1 - cos a) - cos b / (1 - cos b) = (cos a - cos b) / ((1 - cos a) * (1 - cos b)) := by
        field_simp [h_den_a_pos.ne.symm, h_den_b_pos.ne.symm]
        ring
      have h_nonneg : 0 ≤ cos a - cos b := by linarith
      have h_den_pos : 0 < (1 - cos a) * (1 - cos b) := mul_pos h_den_a_pos h_den_b_pos
      have h_div_nonneg : 0 ≤ (cos a - cos b) / ((1 - cos a) * (1 - cos b)) :=
        div_nonneg h_nonneg h_den_pos.le
      linarith
    exact h_div_le
  -- Now use the monotonicity
  have hg_lo_le_d : g lo ≤ d := by
    have h := hg_mono lo (alpha d) h0 halpha_lt_pi2 hlo
    rw [hg_alpha] at h
    exact h
  have hd_le_g_hi : d ≤ g hi := by
    have h := hg_mono (alpha d) hi halpha_pos h1 hhi
    rw [hg_alpha] at h
    exact h
  -- Now handle the interval arithmetic
  -- We inline the definitions to avoid let/unfold issues
  have hc_lo_mem : (R.cos (Iv.pt (Fl.ofReal lo))).Mem (cos lo) :=
    hR.cos (Iv.pt (Fl.ofReal lo)) lo Iv.mem_pt
  have hs_lo_mem : (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal lo)))).Mem (1 - cos lo) :=
    hR.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal lo))) (1 : ℝ) (cos lo) Iv.mem_pt hc_lo_mem
  have hcos_lo_pos : 0 < cos lo := hcos_pos lo hlo_pos hlo_lt_pi2
  have hcos_lo_lt_one : cos lo < 1 := hcos_lt_one lo hlo_pos hlo_lt_pi2
  have h_sub_lo_ne_zero : 1 - cos lo ≠ 0 := by linarith
  have hcos_lo_lt_half : cos lo < 1/2 := by
    have h0le : (0 : ℝ) ≤ π/3 := by linarith
    have hlo_le_pi : lo ≤ π := by linarith
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi h0le hlo_le_pi h0
    simpa [Real.cos_pi_div_three] using h
  have h_ratio_lo_le_one : cos lo / (1 - cos lo) ≤ 1 := by
    refine (div_le_one ?_).mpr ?_
    · linarith
    linarith
  have hq_lo_mem : (R.div (R.cos (Iv.pt (Fl.ofReal lo))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal lo))))).Mem (cos lo / (1 - cos lo)) :=
    hR.div (R.cos (Iv.pt (Fl.ofReal lo))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal lo)))) (cos lo) (1 - cos lo) hc_lo_mem hs_lo_mem h_sub_lo_ne_zero
  have ha_lo_mem : (R.acos (R.div (R.cos (Iv.pt (Fl.ofReal lo))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal lo)))))).Mem (arccos (cos lo / (1 - cos lo))) :=
    hR.acos (R.div (R.cos (Iv.pt (Fl.ofReal lo))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal lo))))) (cos lo / (1 - cos lo)) hq_lo_mem
      (by
        -- -1 ≤ cos lo / (1 - cos lo)
        have : 0 ≤ cos lo / (1 - cos lo) := div_nonneg (by linarith) (by linarith)
        linarith)
      (by linarith)
  -- Similarly for hi
  have hc_hi_mem : (R.cos (Iv.pt (Fl.ofReal hi))).Mem (cos hi) :=
    hR.cos (Iv.pt (Fl.ofReal hi)) hi Iv.mem_pt
  have hs_hi_mem : (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal hi)))).Mem (1 - cos hi) :=
    hR.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal hi))) (1 : ℝ) (cos hi) Iv.mem_pt hc_hi_mem
  have hcos_hi_pos : 0 < cos hi := hcos_pos hi hhi_pos hhi_lt_pi2
  have hcos_hi_lt_one : cos hi < 1 := hcos_lt_one hi hhi_pos hhi_lt_pi2
  have h_sub_hi_ne_zero : 1 - cos hi ≠ 0 := by linarith
  have hcos_hi_lt_half : cos hi < 1/2 := by
    have h0le : (0 : ℝ) ≤ π/3 := by linarith
    have hhi_le_pi : hi ≤ π := by linarith
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi h0le hhi_le_pi (by linarith)
    simpa [Real.cos_pi_div_three] using h
  have h_ratio_hi_le_one : cos hi / (1 - cos hi) ≤ 1 := by
    refine (div_le_one ?_).mpr ?_
    · linarith
    linarith
  have hq_hi_mem : (R.div (R.cos (Iv.pt (Fl.ofReal hi))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal hi))))).Mem (cos hi / (1 - cos hi)) :=
    hR.div (R.cos (Iv.pt (Fl.ofReal hi))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal hi)))) (cos hi) (1 - cos hi) hc_hi_mem hs_hi_mem h_sub_hi_ne_zero
  have ha_hi_mem : (R.acos (R.div (R.cos (Iv.pt (Fl.ofReal hi))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal hi)))))).Mem (arccos (cos hi / (1 - cos hi))) :=
    hR.acos (R.div (R.cos (Iv.pt (Fl.ofReal hi))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal hi))))) (cos hi / (1 - cos hi)) hq_hi_mem
      (by
        -- -1 ≤ cos hi / (1 - cos hi)
        have : 0 ≤ cos hi / (1 - cos hi) := div_nonneg (by linarith) (by linarith)
        linarith)
      (by linarith)
  -- Now expand the goal
  simp [Iv.Mem, alphaInvIv]
  -- Goal: Fl.le (R.acos (R.div (R.cos (Iv.pt (Fl.ofReal lo))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal lo)))))).lo (Fl.ofReal d) ∧ Fl.le (Fl.ofReal d) (R.acos (R.div (R.cos (Iv.pt (Fl.ofReal hi))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal hi)))))).hi
  rcases ha_lo_mem with ⟨h_lo_le_glo, h_glo_le_lo⟩
  rcases ha_hi_mem with ⟨h_lo_le_ghi, h_ghi_le_hi⟩
  -- We have: (R.acos ...).lo ≤ g lo ≤ d and d ≤ g hi ≤ (R.acos ...).hi
  -- Need: (R.acos ...).lo ≤ d and d ≤ (R.acos ...).hi
  have h_lo_le_d : Fl.le (R.acos (R.div (R.cos (Iv.pt (Fl.ofReal lo))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal lo)))))).lo (Fl.ofReal d) := by
    have h_glo_le_d : Fl.le (Fl.ofReal (g lo)) (Fl.ofReal d) := by
      simpa [Fl.ofReal_le_ofReal] using hg_lo_le_d
    exact Fl.le_trans h_lo_le_glo h_glo_le_d
  have h_d_le_hi : Fl.le (Fl.ofReal d) (R.acos (R.div (R.cos (Iv.pt (Fl.ofReal hi))) (R.sub (Iv.pt (Fl.ofReal 1)) (R.cos (Iv.pt (Fl.ofReal hi)))))).hi := by
    have h_d_le_ghi : Fl.le (Fl.ofReal d) (Fl.ofReal (g hi)) := by
      simpa [Fl.ofReal_le_ofReal] using hd_le_g_hi
    exact Fl.le_trans h_d_le_ghi h_ghi_le_hi
  exact ⟨h_lo_le_d, h_d_le_hi⟩

theorem rho_eq_two_arctan_inv {d x : ℝ} (hd : 0 < d ∧ d < π / 2)
    (hx : 0 < x ∧ x < π) : rho d x = 2 * arctan (1 / (tan (x / 2) * cos d)) := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases hx with ⟨hx_pos, hx_lt⟩
  have hcos_pos : 0 < cos d := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have hx2_pos : 0 < x / 2 := by linarith
  have hx2_lt : x / 2 < π / 2 := by linarith
  have htan_pos : 0 < tan (x / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hx2_pos hx2_lt
  have ht_pos : 0 < cos d * tan (x / 2) := mul_pos hcos_pos htan_pos
  set t := cos d * tan (x / 2) with ht_def
  have h_inv : 1 / (tan (x / 2) * cos d) = t⁻¹ := by
    rw [ht_def]
    rw [one_div, mul_comm]
  calc
    rho d x = π - 2 * arctan (cos d * tan (x / 2)) := rfl
    _ = π - 2 * arctan t := by rw [ht_def]
    _ = 2 * (π / 2 - arctan t) := by ring
    _ = 2 * arctan (t⁻¹) := by rw [Real.arctan_inv_of_pos ht_pos]
    _ = 2 * arctan (1 / (tan (x / 2) * cos d)) := by rw [h_inv]

theorem rhoF_mem {R : Rnd} (hR : R.Sound) {x d : ℝ} (hx : 0 < x ∧ x < π)
    (hd : 0 < d ∧ d < π / 2) :
    (R.scale (R.atan (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)) (R.cos (Iv.pt (.ofReal d)))))) 2).Mem
      (2 * arctan (1 / (tan (x / 2) * cos d))) := by
  rcases hx with ⟨hx_pos, hx_lt⟩
  rcases hd with ⟨hd_pos, hd_lt⟩
  have hx_mul_half_pos : 0 < x * 0.5 := by nlinarith
  have hx_mul_half_lt_pi_div_two : x * 0.5 < π / 2 := by nlinarith
  have hcos_pos : 0 < cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hd_lt⟩
  have hprod_ne_zero : tan (x * 0.5) * cos d ≠ 0 := by
    have htan_pos : 0 < tan (x * 0.5) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two hx_mul_half_pos hx_mul_half_lt_pi_div_two
    nlinarith
  have h1 : (R.scale (Iv.pt (.ofReal x)) 0.5).Mem (x * 0.5) := by
    simp only [Rnd.scale]
    exact hR.mul (Iv.pt (.ofReal x)) (Iv.pt (.ofReal (0.5 : ℝ))) x 0.5
      Iv.mem_pt Iv.mem_pt
  have h2 : (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)).Mem (tan (x * 0.5)) :=
    hR.tan (R.scale (Iv.pt (.ofReal x)) 0.5) (x * 0.5) h1
      (by nlinarith) (by nlinarith)
  have h3 : (R.cos (Iv.pt (.ofReal d))).Mem (cos d) :=
    hR.cos (Iv.pt (.ofReal d)) d Iv.mem_pt
  have h4 : (R.mul (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)) (R.cos (Iv.pt (.ofReal d)))).Mem
      (tan (x * 0.5) * cos d) :=
    hR.mul (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)) (R.cos (Iv.pt (.ofReal d)))
      (tan (x * 0.5)) (cos d) h2 h3
  have h5 : (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)) (R.cos (Iv.pt (.ofReal d))))).Mem
      (1 / (tan (x * 0.5) * cos d)) :=
    hR.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)) (R.cos (Iv.pt (.ofReal d))))
      1 (tan (x * 0.5) * cos d) Iv.mem_pt h4 hprod_ne_zero
  have h6 : (R.atan (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)) (R.cos (Iv.pt (.ofReal d)))))).Mem
      (arctan (1 / (tan (x * 0.5) * cos d))) :=
    hR.atan (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)) (R.cos (Iv.pt (.ofReal d)))))
      (1 / (tan (x * 0.5) * cos d)) h5
  have h7 : (R.scale (R.atan (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)) (R.cos (Iv.pt (.ofReal d)))))) 2).Mem
      (arctan (1 / (tan (x * 0.5) * cos d)) * 2) := by
    simp only [Rnd.scale]
    exact hR.mul (R.atan (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal x)) 0.5)) (R.cos (Iv.pt (.ofReal d))))))
      (Iv.pt (.ofReal (2 : ℝ))) (arctan (1 / (tan (x * 0.5) * cos d))) 2 h6 Iv.mem_pt
  have hx_mul_half : x * 0.5 = x / 2 := by ring
  convert h7 using 1
  rw [hx_mul_half, mul_comm]

theorem rhoIv_mem {R : Rnd} (hR : R.Sound) {xl xh dl dh x d : ℝ}
    (hx : xl ≤ x ∧ x ≤ xh) (hd : dl ≤ d ∧ d ≤ dh) (hx0 : 0 < xl) (hx1 : xh < π) (hd0 : 0 < dl)
    (hd1 : dh < π / 2) : (rhoIv R (Iv.ofReal xl xh) (Iv.ofReal dl dh)).Mem (rho d x) := by
  rcases hx with ⟨hxlx, hxxh⟩
  rcases hd with ⟨hdld, hddh⟩
  have hxhpos : 0 < xh := by linarith
  have hxpos : 0 < x := by linarith
  have hxl_lt_pi : xl < π := by linarith
  have hx_lt_pi : x < π := by linarith
  have hdhpos : 0 < dh := by linarith
  have hd_lt_pi2 : d < π / 2 := by linarith
  have hdl_lt_pi2 : dl < π / 2 := by linarith
  have hxh_mem : xh ∈ Set.Ioo (0 : ℝ) π := Set.mem_Ioo.mpr ⟨hxhpos, hx1⟩
  have hxl_mem : xl ∈ Set.Ioo (0 : ℝ) π := Set.mem_Ioo.mpr ⟨hx0, hxl_lt_pi⟩
  have hx_mem : x ∈ Set.Ioo (0 : ℝ) π := Set.mem_Ioo.mpr ⟨hxpos, hx_lt_pi⟩
  have hdl_mem : dl ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hd0, hdl_lt_pi2⟩
  have hd_mem : d ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨by linarith, hd_lt_pi2⟩
  have hdh_mem : dh ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hdhpos, hd1⟩
  -- membership from rhoF_mem at (xh, dl) rewritten with rho_eq_two_arctan_inv
  have hmem1 : (R.scale (R.atan (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal xh)) 0.5)) (R.cos (Iv.pt (.ofReal dl)))))) 2).Mem
      (rho dl xh) := by
    have := rhoF_mem hR ⟨hxhpos, hx1⟩ ⟨hd0, hdl_lt_pi2⟩
    simpa [rho_eq_two_arctan_inv ⟨hd0, hdl_lt_pi2⟩ ⟨hxhpos, hx1⟩] using this
  -- membership from rhoF_mem at (xl, dh) rewritten with rho_eq_two_arctan_inv
  have hmem2 : (R.scale (R.atan (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal xl)) 0.5)) (R.cos (Iv.pt (.ofReal dh)))))) 2).Mem
      (rho dh xl) := by
    have := rhoF_mem hR ⟨hx0, hxl_lt_pi⟩ ⟨hdhpos, hd1⟩
    simpa [rho_eq_two_arctan_inv ⟨hdhpos, hd1⟩ ⟨hx0, hxl_lt_pi⟩] using this
  rcases hmem1 with ⟨hlo1, _⟩
  rcases hmem2 with ⟨_, hhi2⟩
  -- monotonicity chains
  have hanti_d : AntitoneOn (rho d) (Set.Ioo (0 : ℝ) π) :=
    (rho_strictAntiOn_x d ⟨by linarith, hd_lt_pi2⟩).antitoneOn
  have hanti_dh : AntitoneOn (rho dh) (Set.Ioo (0 : ℝ) π) :=
    (rho_strictAntiOn_x dh ⟨hdhpos, hd1⟩).antitoneOn
  have hmono_xh : MonotoneOn (fun dd => rho dd xh) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (rho_strictMonoOn_d xh ⟨hxhpos, hx1⟩).monotoneOn
  have hmono_x : MonotoneOn (fun dd => rho dd x) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (rho_strictMonoOn_d x ⟨hxpos, hx_lt_pi⟩).monotoneOn
  have hrho_dl_xh_le_rho_d_xh : rho dl xh ≤ rho d xh :=
    hmono_xh hdl_mem hd_mem hdld
  have hrho_d_xh_le_rho_d_x : rho d xh ≤ rho d x :=
    hanti_d hx_mem hxh_mem hxxh
  have hrho_d_x_le_rho_dh_x : rho d x ≤ rho dh x :=
    hmono_x hd_mem hdh_mem hddh
  have hrho_dh_x_le_rho_dh_xl : rho dh x ≤ rho dh xl :=
    hanti_dh hxl_mem hx_mem hxlx
  -- combine with Fl.ofReal_le_ofReal
  have hleft : (R.scale (R.atan (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal xh)) 0.5)) (R.cos (Iv.pt (.ofReal dl)))))) 2).lo.le
      (Fl.ofReal (rho d x)) := by
    apply Fl.le_trans hlo1
    simpa [Fl.ofReal_le_ofReal] using hrho_dl_xh_le_rho_d_xh.trans hrho_d_xh_le_rho_d_x
  have hright : (Fl.ofReal (rho d x)).le
      (R.scale (R.atan (R.div (Iv.pt (.ofReal 1))
      (R.mul (R.tan (R.scale (Iv.pt (.ofReal xl)) 0.5)) (R.cos (Iv.pt (.ofReal dh)))))) 2).hi :=
    Fl.le_trans (by
      simpa [Fl.ofReal_le_ofReal] using hrho_d_x_le_rho_dh_x.trans hrho_dh_x_le_rho_dh_xl) hhi2
  unfold rhoIv
  simp [Iv.Mem, Iv.ofReal, hleft, hright]

theorem cot_half_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < π) :
    cot (t / 2) ≤ cot (s / 2) ∧ 0 < cot (t / 2) := by
  have hpos_s2 : 0 < s / 2 := by linarith
  have hpos_t2 : 0 < t / 2 := by linarith
  have ht2_lt_pi_div_two : t / 2 < π / 2 := by linarith
  have hs2_le_t2 : s / 2 ≤ t / 2 := by linarith
  have hcos_pos_s2 : 0 < cos (s / 2) :=
    Real.cos_pos_of_mem_Ioo (by
      constructor <;> linarith)
  have hcos_pos_t2 : 0 < cos (t / 2) :=
    Real.cos_pos_of_mem_Ioo (by
      constructor <;> linarith)
  have hsin_pos_s2 : 0 < sin (s / 2) :=
    Real.sin_pos_of_mem_Ioo (by
      constructor <;> linarith)
  have hsin_pos_t2 : 0 < sin (t / 2) :=
    Real.sin_pos_of_mem_Ioo (by
      constructor <;> linarith)
  have hcos_t2_le_cos_s2 : cos (t / 2) ≤ cos (s / 2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hs2_le_t2
  have hsin_s2_le_sin_t2 : sin (s / 2) ≤ sin (t / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hs2_le_t2
  have hcot_t2_le_cot_s2 : cot (t / 2) ≤ cot (s / 2) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
    calc
      cos (t / 2) / sin (t / 2) ≤ cos (s / 2) / sin (t / 2) :=
        div_le_div_of_nonneg_right hcos_t2_le_cos_s2 (by linarith)
      _ ≤ cos (s / 2) / sin (s / 2) :=
        div_le_div_of_nonneg_left (by linarith) hsin_pos_s2 hsin_s2_le_sin_t2
  have hpos_cot_t2 : 0 < cot (t / 2) := by
    rw [Real.cot_eq_cos_div_sin]
    exact div_pos hcos_pos_t2 hsin_pos_t2
  exact And.intro hcot_t2_le_cot_s2 hpos_cot_t2

theorem cotPt_mem {R : Rnd} (hR : R.Sound) {t : ℝ} (h0 : 0 < t)
    (h1 : t < π) :
    (R.div (R.cos (R.scale (Iv.pt (.ofReal t)) 0.5)) (R.sin (R.scale (Iv.pt (.ofReal t)) 0.5))).Mem
      (cot (t / 2)) := by
  have hpos : 0 < t * 0.5 := by nlinarith
  have hlt : t * 0.5 < π := by nlinarith
  have hsin_pos : sin (t * 0.5) > 0 := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  have hsin_ne_zero : sin (t * 0.5) ≠ 0 := by linarith
  have hmem : (R.scale (Iv.pt (.ofReal t)) 0.5).Mem (t * 0.5) := by
    have h1 : (Iv.pt (.ofReal t)).Mem t := Iv.mem_pt
    have h2 : (Iv.pt (.ofReal (0.5 : ℝ))).Mem (0.5 : ℝ) := Iv.mem_pt
    simpa [Rnd.scale] using hR.mul (Iv.pt (.ofReal t)) (Iv.pt (.ofReal (0.5 : ℝ))) t (0.5 : ℝ) h1 h2
  have hcos : (R.cos (R.scale (Iv.pt (.ofReal t)) 0.5)).Mem (Real.cos (t * 0.5)) :=
    hR.cos _ _ hmem
  have hsin : (R.sin (R.scale (Iv.pt (.ofReal t)) 0.5)).Mem (Real.sin (t * 0.5)) :=
    hR.sin _ _ hmem
  have hdiv : (R.div (R.cos (R.scale (Iv.pt (.ofReal t)) 0.5)) (R.sin (R.scale (Iv.pt (.ofReal t)) 0.5))).Mem
    (Real.cos (t * 0.5) / Real.sin (t * 0.5)) :=
    hR.div _ _ _ _ hcos hsin hsin_ne_zero
  have h_eq : Real.cos (t * 0.5) / Real.sin (t * 0.5) = cot (t / 2) := by
    have h_arg : t * 0.5 = t / 2 := by field_simp; norm_num
    rw [Real.cot_eq_cos_div_sin, h_arg]
  simpa [h_eq] using hdiv

theorem rhombusD_sound {R : Rnd} (hR : R.Sound) {xl xh yl yh x y d : ℝ}
    (hx : xl ≤ x ∧ x ≤ xh) (hy : yl ≤ y ∧ y ≤ yh) (hx0 : 0 < xl) (hx1 : xh < π) (hy0 : 0 < yl)
    (hy1 : yh < π) (hd : 0 ≤ d ∧ d ≤ π) (hc : cos d = cot (x / 2) * cot (y / 2)) :
    ∃ I, rhombusD R (Iv.ofReal xl xh) (Iv.ofReal yl yh) = some I ∧ I.Mem d := by
  rcases hx with ⟨hxl, hxh⟩
  rcases hy with ⟨hyl, hyh⟩
  rcases hd with ⟨hd0, hd1⟩
  have hx_lt_pi : x < π := lt_of_le_of_lt hxh hx1
  have hy_lt_pi : y < π := lt_of_le_of_lt hyh hy1
  have hxl_lt_pi : xl < π := lt_of_le_of_lt hxl hx_lt_pi
  have hyl_lt_pi : yl < π := lt_of_le_of_lt hyl hy_lt_pi
  unfold rhombusD
  set cx := fun (t : ℝ) => cot (t / 2) with hcx
  have hcx_pos : ∀ t, 0 < t → t < π → 0 < cx t := by
    intro t ht0 ht1
    dsimp [cx]
    exact (cot_half_le ht0 (by rfl) ht1).2
  have hx_pos : 0 < x := lt_of_lt_of_le hx0 hxl
  have hy_pos : 0 < y := lt_of_lt_of_le hy0 hyl
  have hcx_bound_x : 0 < cx xh ∧ cx xh ≤ cx x ∧ cx x ≤ cx xl := by
    have hpos_xh : 0 < cx xh := by
      dsimp [cx]
      have := cot_half_le (s := x) (t := xh) hx_pos hxh hx1
      exact this.2
    have hx_le_xh : cx xh ≤ cx x := by
      dsimp [cx]
      have := cot_half_le (s := x) (t := xh) hx_pos hxh hx1
      exact this.1
    have hx_le_xl : cx x ≤ cx xl := by
      dsimp [cx]
      have := cot_half_le (s := xl) (t := x) hx0 hxl hx_lt_pi
      exact this.1
    exact ⟨hpos_xh, hx_le_xh, hx_le_xl⟩
  have hcx_bound_y : 0 < cx yh ∧ cx yh ≤ cx y ∧ cx y ≤ cx yl := by
    have hpos_yh : 0 < cx yh := by
      dsimp [cx]
      have := cot_half_le (s := y) (t := yh) hy_pos hyh hy1
      exact this.2
    have hy_le_yh : cx yh ≤ cx y := by
      dsimp [cx]
      have := cot_half_le (s := y) (t := yh) hy_pos hyh hy1
      exact this.1
    have hy_le_yl : cx y ≤ cx yl := by
      dsimp [cx]
      have := cot_half_le (s := yl) (t := y) hy0 hyl hy_lt_pi
      exact this.1
    exact ⟨hpos_yh, hy_le_yh, hy_le_yl⟩
  -- Now we have bounds: cx xh * cx yh ≤ cos d ≤ cx xl * cx yl
  have hcos_d_eq : cos d = cx x * cx y := by
    dsimp [cx]
    rw [hc]
  have hxh_nonneg : 0 ≤ cx xh := le_of_lt hcx_bound_x.1
  have hyh_nonneg : 0 ≤ cx yh := le_of_lt hcx_bound_y.1
  have hxl_nonneg : 0 ≤ cx xl := le_of_lt (by
    have := cot_half_le (s := xl) (t := xl) hx0 (le_refl xl) hxl_lt_pi
    dsimp [cx]
    exact this.2)
  have hyl_nonneg : 0 ≤ cx yl := le_of_lt (by
    have := cot_half_le (s := yl) (t := yl) hy0 (le_refl yl) hyl_lt_pi
    dsimp [cx]
    exact this.2)
  have hx_nonneg : 0 ≤ cx x := le_of_lt (by
    have := cot_half_le (s := xl) (t := x) hx0 hxl hx_lt_pi
    dsimp [cx]
    exact this.2)
  have hy_nonneg : 0 ≤ cx y := le_of_lt (by
    have := cot_half_le (s := yl) (t := y) hy0 hyl hy_lt_pi
    dsimp [cx]
    exact this.2)
  have hprod_lower : cx xh * cx yh ≤ cos d := by
    rw [hcos_d_eq]
    exact mul_le_mul hcx_bound_x.2.1 hcx_bound_y.2.1 hyh_nonneg hx_nonneg
  have hprod_upper : cos d ≤ cx xl * cx yl := by
    rw [hcos_d_eq]
    exact mul_le_mul hcx_bound_x.2.2 hcx_bound_y.2.2 hy_nonneg hxl_nonneg
  -- Now we case split on the conditions in rhombusD
  -- define the local cot from rhombusD
  set cot := fun (t : Fl) =>
    let h := R.scale (Iv.pt t) 0.5
    R.div (R.cos h) (R.sin h) with hcot
  -- cotPt_mem gives us the enclosure
  have hcot_xl_mem : (cot (Fl.ofReal xl)).Mem (cx xl) := by
    dsimp [cot, cx]
    simpa using cotPt_mem hR hx0 hxl_lt_pi
  have hxh_pos : 0 < xh := lt_of_lt_of_le hx_pos hxh
  have hyh_pos : 0 < yh := lt_of_lt_of_le hy_pos hyh
  have hcot_xh_mem : (cot (Fl.ofReal xh)).Mem (cx xh) := by
    dsimp [cot, cx]
    simpa using cotPt_mem hR hxh_pos hx1
  have hcot_yl_mem : (cot (Fl.ofReal yl)).Mem (cx yl) := by
    dsimp [cot, cx]
    simpa using cotPt_mem hR hy0 hyl_lt_pi
  have hcot_yh_mem : (cot (Fl.ofReal yh)).Mem (cx yh) := by
    dsimp [cot, cx]
    simpa using cotPt_mem hR hyh_pos hy1
  -- pmax and pmin
  set pmax := R.mul (cot (Iv.ofReal xl xh).lo) (cot (Iv.ofReal yl yh).lo) with hpmax
  set pmin := R.mul (cot (Iv.ofReal xl xh).hi) (cot (Iv.ofReal yl yh).hi) with hpmin
  have hpmax_mem : pmax.Mem (cx xl * cx yl) := by
    rw [hpmax]
    simpa [Iv.ofReal] using hR.mul (cot (Fl.ofReal xl)) (cot (Fl.ofReal yl)) (cx xl) (cx yl)
      hcot_xl_mem hcot_yl_mem
  have hpmin_mem : pmin.Mem (cx xh * cx yh) := by
    rw [hpmin]
    simpa [Iv.ofReal] using hR.mul (cot (Fl.ofReal xh)) (cot (Fl.ofReal yh)) (cx xh) (cx yh)
      hcot_xh_mem hcot_yh_mem
  -- key inequalities from the interval enclosures
  have h_cos_d_le_pmax_hi : Fl.le (Fl.ofReal (cos d)) pmax.hi := by
    have h : Fl.le (Fl.ofReal (cos d)) (Fl.ofReal (cx xl * cx yl)) :=
      Fl.ofReal_le_ofReal.mpr hprod_upper
    have h' : Fl.le (Fl.ofReal (cx xl * cx yl)) pmax.hi := (hpmax_mem).2
    exact Fl.le_trans h h'
  have h_pmin_lo_le_cos_d : Fl.le pmin.lo (Fl.ofReal (cos d)) := by
    have h : Fl.le pmin.lo (Fl.ofReal (cx xh * cx yh)) := (hpmin_mem).1
    have h' : Fl.le (Fl.ofReal (cx xh * cx yh)) (Fl.ofReal (cos d)) :=
      Fl.ofReal_le_ofReal.mpr hprod_lower
    exact Fl.le_trans h h'
  -- now case split on the conditions
  dsimp only [pmax, pmin]
  by_cases h_not_usable : ¬ (R.mul (cot (Iv.ofReal xl xh).lo) (cot (Iv.ofReal yl yh).lo)).Usable
    ∨ ¬ (R.mul (cot (Iv.ofReal xl xh).hi) (cot (Iv.ofReal yl yh).hi)).Usable
  · -- case 1: not usable → returns some ⟨.ofReal 0, .ofReal R.piHi⟩
    refine ⟨Iv.ofReal 0 R.piHi, ?_, ?_⟩
    · -- rhombusD ... = some (Iv.ofReal 0 R.piHi)
      rw [if_pos h_not_usable]
      rfl
    · -- Iv.Mem (Iv.ofReal 0 R.piHi) d
      rw [Iv.mem_ofReal]
      have hd_le_piHi : d ≤ R.piHi := le_trans hd1 hR.piHi
      exact ⟨hd0, hd_le_piHi⟩
  · -- pmax and pmin are usable
    rcases not_or.mp h_not_usable with ⟨hpmax_us, hpmin_us⟩
    by_cases h_lt_one : Fl.lt (.ofReal 1) (R.mul (cot (Iv.ofReal xl xh).hi) (cot (Iv.ofReal yl yh).hi)).lo
    · -- case 2: Fl.lt .ofReal 1 pmin.lo → returns none, but this is impossible
      have h_not_lt : Fl.le (R.mul (cot (Iv.ofReal xl xh).hi) (cot (Iv.ofReal yl yh).hi)).lo (Fl.ofReal 1) := by
        have hcos_le_one' : Fl.le (Fl.ofReal (cos d)) (Fl.ofReal 1) :=
          Fl.ofReal_le_ofReal.mpr (Real.cos_le_one d)
        exact Fl.le_trans h_pmin_lo_le_cos_d hcos_le_one'
      exact absurd h_lt_one (Fl.not_lt_of_le h_not_lt)
    · -- case 3: the main case
      have h_cos_d_ge_neg_one : -1 ≤ cos d := Real.neg_one_le_cos d
      have h_cos_d_le_one : cos d ≤ 1 := Real.cos_le_one d
      -- For Fl.min_one_eq: we need Fl.le (.ofReal (cos d)) pmax.hi and ¬ Fl.lt pmax.hi (.ofReal (-1))
      have hU : Fl.le (Fl.ofReal (cos d)) pmax.hi := h_cos_d_le_pmax_hi
      have hU1 : ¬ Fl.lt pmax.hi (Fl.ofReal (-1)) := by
        have hneg_one_le : Fl.le (Fl.ofReal (-1)) (Fl.ofReal (cos d)) :=
          Fl.ofReal_le_ofReal.mpr h_cos_d_ge_neg_one
        have hle : Fl.le (Fl.ofReal (-1)) pmax.hi := Fl.le_trans hneg_one_le h_cos_d_le_pmax_hi
        exact Fl.not_lt_of_le hle
      -- Get r from Fl.min_one_eq
      obtain ⟨r, hr_min_eq, hr_ge_neg_one, hr_le_one, hr_min_y⟩ :=
        Fl.min_one_eq hU hU1
      -- hr_min_eq : Fl.min pmax.hi (.ofReal 1) = .ofReal r
      -- hr_min_y : Min.min (cos d) 1 ≤ r
      -- Since cos d ≤ 1, Min.min (cos d) 1 = cos d, so cos d ≤ r
      have h_min_y_eq : Min.min (cos d) 1 = cos d := by
        rw [min_eq_left h_cos_d_le_one]
      have h_cos_d_le_r : cos d ≤ r := by
        rw [h_min_y_eq] at hr_min_y
        exact hr_min_y
      -- Now use hR.acos on Iv.pt (.ofReal r)
      have hr_mem : (Iv.pt (Fl.ofReal r)).Mem r := by
        simpa using Iv.mem_pt (x := r)
      have hR_acos_mem : (R.acos (Iv.pt (Fl.ofReal r))).Mem (Real.arccos r) :=
        hR.acos (Iv.pt (Fl.ofReal r)) r hr_mem hr_ge_neg_one hr_le_one
      -- So (R.acos (Iv.pt (Fl.ofReal r))).lo ≤ .ofReal (arccos r)
      have h_acos_lo : Fl.le (R.acos (Iv.pt (Fl.ofReal r))).lo (Fl.ofReal (Real.arccos r)) := by
        simpa using hR_acos_mem.1
      -- Now, arccos r ≤ arccos (cos d) = d (since 0 ≤ d ≤ π)
      have h_arccos_r_le_arccos_cos_d : Real.arccos r ≤ Real.arccos (cos d) :=
        Real.arccos_le_arccos h_cos_d_le_r
      have h_arccos_cos_d_eq_d : Real.arccos (cos d) = d :=
        Real.arccos_cos hd0 hd1
      have h_arccos_r_le_d : Real.arccos r ≤ d := by
        rw [h_arccos_cos_d_eq_d] at h_arccos_r_le_arccos_cos_d
        exact h_arccos_r_le_arccos_cos_d
      -- So Fl.le (R.acos ...).lo (.ofReal d)
      have h_lo_le_d : Fl.le (R.acos (Iv.pt (Fl.ofReal r))).lo (Fl.ofReal d) :=
        Fl.le_trans h_acos_lo (Fl.ofReal_le_ofReal.mpr h_arccos_r_le_d)
      -- Now for the upper bound: Fl.max_neg_one_eq
      have hL : Fl.le pmin.lo (Fl.ofReal (cos d)) := h_pmin_lo_le_cos_d
      have hL1 : ¬ Fl.lt (.ofReal 1) pmin.lo := h_lt_one
      obtain ⟨r', hr_max_eq, hr'_ge_neg_one, hr'_le_one, hr'_max_y⟩ :=
        Fl.max_neg_one_eq hL hL1
      -- hr_max_eq : Fl.max pmin.lo (.ofReal (-1)) = .ofReal r'
      -- hr'_max_y : r' ≤ Max.max (cos d) (-1)
      -- Since -1 ≤ cos d, Max.max (cos d) (-1) = cos d, so r' ≤ cos d
      have h_max_y_eq : Max.max (cos d) (-1) = cos d := by
        rw [max_eq_left h_cos_d_ge_neg_one]
      have hr'_le_cos_d : r' ≤ cos d := by
        rw [h_max_y_eq] at hr'_max_y
        exact hr'_max_y
      -- Use hR.acos on Iv.pt (.ofReal r')
      have hr'_mem : (Iv.pt (Fl.ofReal r')).Mem r' := by
        simpa using Iv.mem_pt (x := r')
      have hR_acos_mem' : (R.acos (Iv.pt (Fl.ofReal r'))).Mem (Real.arccos r') :=
        hR.acos (Iv.pt (Fl.ofReal r')) r' hr'_mem hr'_ge_neg_one hr'_le_one
      -- (R.acos ...).hi ≥ .ofReal (arccos r')
      have h_acos_hi : Fl.le (Fl.ofReal (Real.arccos r')) (R.acos (Iv.pt (Fl.ofReal r'))).hi := by
        simpa using hR_acos_mem'.2
      -- arccos (cos d) ≤ arccos r' (since r' ≤ cos d)
      have h_arccos_d_le_arccos_r' : Real.arccos (cos d) ≤ Real.arccos r' :=
        Real.arccos_le_arccos hr'_le_cos_d
      have h_d_le_arccos_r' : d ≤ Real.arccos r' := by
        rw [h_arccos_cos_d_eq_d] at h_arccos_d_le_arccos_r'
        exact h_arccos_d_le_arccos_r'
      -- So Fl.le (.ofReal d) (R.acos ...).hi
      have h_d_le_hi : Fl.le (Fl.ofReal d) (R.acos (Iv.pt (Fl.ofReal r'))).hi :=
        Fl.le_trans (Fl.ofReal_le_ofReal.mpr h_d_le_arccos_r') h_acos_hi
      -- Now we have the interval
      have h_result_lo : (R.acos (Iv.pt (Fl.min pmax.hi (.ofReal 1)))).lo = (R.acos (Iv.pt (Fl.ofReal r))).lo := by
        rw [hr_min_eq]
      have h_result_hi : (R.acos (Iv.pt (Fl.max pmin.lo (.ofReal (-1))))).hi = (R.acos (Iv.pt (Fl.ofReal r'))).hi := by
        rw [hr_max_eq]
      refine ⟨⟨(R.acos (Iv.pt (Fl.ofReal r))).lo, (R.acos (Iv.pt (Fl.ofReal r'))).hi⟩, ?_, ?_⟩
      · -- equality with rhombusD result
        -- In this branch, h_not_usable is false (it's ¬ (¬ ... ∨ ¬ ...))
        -- and h_lt_one is false
        -- So the first if condition is false, and the second is false
        have h_not_cond : ¬ (¬ (R.mul (cot (Iv.ofReal xl xh).lo) (cot (Iv.ofReal yl yh).lo)).Usable ∨
          ¬ (R.mul (cot (Iv.ofReal xl xh).hi) (cot (Iv.ofReal yl yh).hi)).Usable) := h_not_usable
        have h_not_lt : ¬ Fl.lt (.ofReal 1) (R.mul (cot (Iv.ofReal xl xh).hi) (cot (Iv.ofReal yl yh).hi)).lo := h_lt_one
        -- Use if_neg for the first if, and if_neg for the second
        rw [if_neg h_not_cond, if_neg h_not_lt]
        -- Now the goal is: some { lo := ..., hi := ... } = some ⟨...⟩
        -- Need to show the Iv equality
        -- hr_min_eq: pmax.hi.min (Fl.ofReal 1) = Fl.ofReal r
        -- hr_max_eq: pmin.lo.max (Fl.ofReal (-1)) = Fl.ofReal r'
        -- But the goal uses (R.mul ...).hi instead of pmax.hi
        dsimp [pmax, pmin] at hr_min_eq hr_max_eq
        rw [hr_min_eq, hr_max_eq]
      · -- Mem d: show Fl.le lo (.ofReal d) ∧ Fl.le (.ofReal d) hi
        dsimp [Iv.Mem]
        exact ⟨h_lo_le_d, h_d_le_hi⟩

theorem isoBase_mem {R : Rnd} (hR : R.Sound) {I J : Iv} {u d : ℝ}
    (hu : I.Mem u) (hd : J.Mem d) : (isoBase R I J).Mem (ebase d u) := by
  have hsinJ : (R.sin J).Mem (sin d) := hR.sin J d hd
  have hscale_mem : (R.scale I 0.5).Mem (u * 0.5) := by
    simpa [Rnd.scale] using hR.mul I (Iv.pt (.ofReal 0.5)) u 0.5 hu (Iv.mem_pt (x := 0.5))
  have hsin_scale : (R.sin (R.scale I 0.5)).Mem (sin (u * 0.5)) :=
    hR.sin (R.scale I 0.5) (u * 0.5) hscale_mem
  have hprod : (R.mul (R.sin J) (R.sin (R.scale I 0.5))).Mem (sin d * sin (u * 0.5)) :=
    hR.mul (R.sin J) (R.sin (R.scale I 0.5)) (sin d) (sin (u * 0.5)) hsinJ hsin_scale
  have hbound : -1 ≤ sin d * sin (u * 0.5) ∧ sin d * sin (u * 0.5) ≤ 1 := by
    have habs : |sin d * sin (u * 0.5)| ≤ 1 := by
      calc
        |sin d * sin (u * 0.5)| = |sin d| * |sin (u * 0.5)| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    exact abs_le.mp habs
  rcases hbound with ⟨hl, hr⟩
  have hasin : (R.asin (R.mul (R.sin J) (R.sin (R.scale I 0.5)))).Mem (arcsin (sin d * sin (u * 0.5))) :=
    hR.asin (R.mul (R.sin J) (R.sin (R.scale I 0.5))) (sin d * sin (u * 0.5)) hprod hl hr
  have hscale_final : (R.scale (R.asin (R.mul (R.sin J) (R.sin (R.scale I 0.5)))) 2).Mem
      (arcsin (sin d * sin (u * 0.5)) * 2) := by
    simpa [Rnd.scale] using hR.mul (R.asin (R.mul (R.sin J) (R.sin (R.scale I 0.5))))
      (Iv.pt (.ofReal 2)) (arcsin (sin d * sin (u * 0.5))) 2 hasin (Iv.mem_pt (x := 2))
  have hu_eq : u * 0.5 = u / 2 := by ring
  simpa [isoBase, ebase, hu_eq, mul_comm] using hscale_final

theorem bangle_antitoneOn_Ioo {d : ℝ} (hd0 : 0 < d ∧ d < π / 2) :
    AntitoneOn (bangle d) (Set.Ioo 0 (2 * π)) := by
  rintro u₁ hu₁ u₂ hu₂ hule
  rcases hd0 with ⟨hd0l, hd0r⟩
  have hcosd_pos : 0 < cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hu₁_pos : 0 < u₁ := (Set.mem_Ioo.mp hu₁).1
  have hu₁_lt_2pi : u₁ < 2 * π := (Set.mem_Ioo.mp hu₁).2
  have hu₂_pos : 0 < u₂ := (Set.mem_Ioo.mp hu₂).1
  have hu₂_lt_2pi : u₂ < 2 * π := (Set.mem_Ioo.mp hu₂).2
  have ht₁_pos : 0 < u₁ / 2 := by linarith
  have ht₁_lt_pi : u₁ / 2 < π := by linarith
  have ht₂_pos : 0 < u₂ / 2 := by linarith
  have ht₂_lt_pi : u₂ / 2 < π := by linarith
  have hsin_pos₁ : 0 < sin (u₁ / 2) :=
    Real.sin_pos_of_mem_Ioo ⟨ht₁_pos, ht₁_lt_pi⟩
  have hsin_pos₂ : 0 < sin (u₂ / 2) :=
    Real.sin_pos_of_mem_Ioo ⟨ht₂_pos, ht₂_lt_pi⟩
  have hden_pos₁ : 0 < cos d * sin (u₁ / 2) := mul_pos hcosd_pos hsin_pos₁
  have hden_pos₂ : 0 < cos d * sin (u₂ / 2) := mul_pos hcosd_pos hsin_pos₂
  by_cases heq : u₁ = u₂
  · subst heq; rfl
  · have hlt : u₁ < u₂ := lt_of_le_of_ne hule heq
    have hsub_lt_zero : (u₁ - u₂) / 2 < 0 := by linarith
    have hsub_gt_neg_pi : -π < (u₁ - u₂) / 2 := by
      have : u₂ - u₁ < 2 * π := by linarith
      linarith
    have hsin_sub_nonpos : sin ((u₁ - u₂) / 2) ≤ 0 :=
      le_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hsub_lt_zero hsub_gt_neg_pi)
    have hineq : cos (u₂ / 2) * sin (u₁ / 2) ≤ cos (u₁ / 2) * sin (u₂ / 2) := by
      have hsin_sub_eq : sin ((u₁ - u₂) / 2) = sin (u₁ / 2 - u₂ / 2) := by ring_nf
      rw [hsin_sub_eq, Real.sin_sub] at hsin_sub_nonpos
      linarith
    have h_div_ineq : cos (u₂ / 2) / (cos d * sin (u₂ / 2)) ≤
        cos (u₁ / 2) / (cos d * sin (u₁ / 2)) := by
      have h_mul : cos (u₂ / 2) * (cos d * sin (u₁ / 2)) ≤
          cos (u₁ / 2) * (cos d * sin (u₂ / 2)) := by
        nlinarith
      have h_denom_nonneg : 0 ≤ (cos d * sin (u₂ / 2)) * (cos d * sin (u₁ / 2)) :=
        mul_nonneg (by linarith) (by linarith)
      have h_eq₁ : cos (u₂ / 2) / (cos d * sin (u₂ / 2)) =
          (cos (u₂ / 2) * (cos d * sin (u₁ / 2))) /
          ((cos d * sin (u₂ / 2)) * (cos d * sin (u₁ / 2))) := by
        field_simp [hden_pos₁.ne.symm, hden_pos₂.ne.symm]
      have h_eq₂ : cos (u₁ / 2) / (cos d * sin (u₁ / 2)) =
          (cos (u₁ / 2) * (cos d * sin (u₂ / 2))) /
          ((cos d * sin (u₂ / 2)) * (cos d * sin (u₁ / 2))) := by
        field_simp [hden_pos₁.ne.symm, hden_pos₂.ne.symm]
      rw [h_eq₁, h_eq₂]
      exact div_le_div_of_nonneg_right h_mul h_denom_nonneg
    dsimp [bangle]
    exact Real.arctan_mono h_div_ineq


theorem isoAngle_mem {R : Rnd} (hR : R.Sound) {ul uh u d : ℝ} {J : Iv}
    (hu : ul ≤ u ∧ u ≤ uh) (h0 : 0 < ul) (h1 : uh < 2 * π) (hd : J.Mem d)
    (hd0 : 0 < d ∧ d < π / 2) : (isoAngle R (Iv.ofReal ul uh) J).Mem (bangle d u) := by
  rcases hu with ⟨hule, hueh⟩
  rcases hd0 with ⟨hd0l, hd0r⟩
  have hcosd_pos : 0 < cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hul_lt_2pi : ul < 2 * π := by linarith
  have hu_pos : 0 < u := by linarith
  have hu_lt_2pi : u < 2 * π := by linarith
  have hul_mem : ul ∈ Set.Ioo 0 (2 * π) := ⟨h0, hul_lt_2pi⟩
  have hu_mem : u ∈ Set.Ioo 0 (2 * π) := ⟨hu_pos, hu_lt_2pi⟩
  have huh_mem : uh ∈ Set.Ioo 0 (2 * π) := ⟨by linarith, h1⟩
  -- antitone property: bangle d is antitone on (0, 2π)
  have h_anti := bangle_antitoneOn_Ioo ⟨hd0l, hd0r⟩
  have h_bangle_u_le_ul : bangle d u ≤ bangle d ul :=
    h_anti hul_mem hu_mem hule
  have h_bangle_uh_le_u : bangle d uh ≤ bangle d u :=
    h_anti hu_mem huh_mem hueh
  -- define the function f from isoAngle
  let cd := R.cos J
  let f := fun x : Fl =>
    let h := R.scale (Iv.pt x) 0.5
    R.atan (R.div (R.cos h) (R.mul cd (R.sin h)))
  have hf_mem (x : ℝ) (hx_pos : 0 < x) (hx_lt_2pi : x < 2 * π) : (f (Fl.ofReal x)).Mem (bangle d x) := by
    have hx2_pos : 0 < x / 2 := by linarith
    have hx2_lt_pi : x / 2 < π := by linarith
    have hsin_pos : 0 < sin (x / 2) :=
      Real.sin_pos_of_mem_Ioo ⟨hx2_pos, hx2_lt_pi⟩
    have hden_pos : 0 < cos d * sin (x / 2) := mul_pos hcosd_pos hsin_pos
    have hden_ne_zero : cos d * sin (x / 2) ≠ 0 := by linarith
    let h := R.scale (Iv.pt (Fl.ofReal x)) 0.5
    have h_mem_h : h.Mem (x / 2) := by
      dsimp [h, Rnd.scale]
      have h_pt_mem : (Iv.pt (Fl.ofReal x)).Mem x := Iv.mem_pt
      have h_pt_half_mem : (Iv.pt (Fl.ofReal (0.5 : ℝ))).Mem (0.5 : ℝ) := Iv.mem_pt
      have h_mul_mem : (R.mul (Iv.pt (Fl.ofReal x)) (Iv.pt (Fl.ofReal (0.5 : ℝ)))).Mem (x * (0.5 : ℝ)) :=
        hR.mul (Iv.pt (Fl.ofReal x)) (Iv.pt (Fl.ofReal (0.5 : ℝ))) x (0.5 : ℝ) h_pt_mem h_pt_half_mem
      simpa [show x * (0.5 : ℝ) = x / 2 by ring] using h_mul_mem
    have h_cos_mem : (R.cos h).Mem (cos (x / 2)) :=
      hR.cos h (x / 2) h_mem_h
    have h_sin_mem : (R.sin h).Mem (sin (x / 2)) :=
      hR.sin h (x / 2) h_mem_h
    have h_cd_mem : cd.Mem (cos d) := by
      dsimp [cd]
      simpa using hR.cos J d hd
    have h_mul_mem : (R.mul cd (R.sin h)).Mem (cos d * sin (x / 2)) :=
      hR.mul cd (R.sin h) (cos d) (sin (x / 2)) h_cd_mem h_sin_mem
    have h_div_mem : (R.div (R.cos h) (R.mul cd (R.sin h))).Mem
      (cos (x / 2) / (cos d * sin (x / 2))) :=
      hR.div (R.cos h) (R.mul cd (R.sin h)) (cos (x / 2)) (cos d * sin (x / 2)) h_cos_mem h_mul_mem hden_ne_zero
    have h_atan_mem : (R.atan (R.div (R.cos h) (R.mul cd (R.sin h)))).Mem
      (arctan (cos (x / 2) / (cos d * sin (x / 2)))) :=
      hR.atan (R.div (R.cos h) (R.mul cd (R.sin h))) (cos (x / 2) / (cos d * sin (x / 2))) h_div_mem
    simpa [f, bangle, cd, h] using h_atan_mem
  have h_mem_uh : (f (Fl.ofReal uh)).Mem (bangle d uh) := hf_mem uh (by linarith) h1
  have h_mem_ul : (f (Fl.ofReal ul)).Mem (bangle d ul) := hf_mem ul h0 (by linarith)
  rcases h_mem_uh with ⟨h_uh_lo, h_uh_hi⟩
  rcases h_mem_ul with ⟨h_ul_lo, h_ul_hi⟩
  -- Now we have:
  -- h_uh_lo : Fl.le (f (Fl.ofReal uh)).lo (Fl.ofReal (bangle d uh))
  -- h_uh_hi : Fl.le (Fl.ofReal (bangle d uh)) (f (Fl.ofReal uh)).hi
  -- h_ul_lo : Fl.le (f (Fl.ofReal ul)).lo (Fl.ofReal (bangle d ul))
  -- h_ul_hi : Fl.le (Fl.ofReal (bangle d ul)) (f (Fl.ofReal ul)).hi
  -- But we need:
  -- Fl.le (f (Fl.ofReal uh)).lo (Fl.ofReal (bangle d u))
  -- Fl.le (Fl.ofReal (bangle d u)) (f (Fl.ofReal ul)).hi
  have h_ofReal_uh_le_u : Fl.le (Fl.ofReal (bangle d uh)) (Fl.ofReal (bangle d u)) :=
    (Fl.ofReal_le_ofReal.mpr h_bangle_uh_le_u)
  have h_ofReal_u_le_ul : Fl.le (Fl.ofReal (bangle d u)) (Fl.ofReal (bangle d ul)) :=
    (Fl.ofReal_le_ofReal.mpr h_bangle_u_le_ul)
  have h_goal1 : Fl.le (f (Fl.ofReal uh)).lo (Fl.ofReal (bangle d u)) :=
    Fl.le_trans h_uh_lo h_ofReal_uh_le_u
  have h_goal2 : Fl.le (Fl.ofReal (bangle d u)) (f (Fl.ofReal ul)).hi :=
    Fl.le_trans h_ofReal_u_le_ul h_ul_hi
  -- Now we need to relate this to isoAngle
  -- isoAngle R (Iv.ofReal ul uh) J = ⟨(f (Fl.ofReal uh)).lo, (f (Fl.ofReal ul)).hi⟩
  have h_isoAngle_eq : isoAngle R (Iv.ofReal ul uh) J = ⟨(f (Fl.ofReal uh)).lo, (f (Fl.ofReal ul)).hi⟩ := by
    dsimp [isoAngle, f, cd]
    have h_hi : (Iv.ofReal ul uh).hi = Fl.ofReal uh := rfl
    have h_lo : (Iv.ofReal ul uh).lo = Fl.ofReal ul := rfl
    rw [h_hi, h_lo]
  rw [h_isoAngle_eq]
  exact ⟨h_goal1, h_goal2⟩

theorem cot_tan_ebase_ge {d u : ℝ} (hd : 0 < d ∧ d < π / 2)
    (hu : 0 < u ∧ u < 2 * π) : cos d * sin (u / 2) ≤ cot d * tan (ebase d u / 2) := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hu with ⟨hupos, hult⟩
  have hd_mem_Ioo : d ∈ Set.Ioo 0 (π / 2) := Set.mem_Ioo.mpr ⟨hdpos, hdlt⟩
  have hu_half_pos : 0 < u / 2 := by linarith
  have hu_half_lt_pi : u / 2 < π := by linarith
  have hu_half_mem_Ioo : u / 2 ∈ Set.Ioo 0 π :=
    Set.mem_Ioo.mpr ⟨hu_half_pos, hu_half_lt_pi⟩
  have hsin_d_pos : 0 < sin d :=
    Real.sin_pos_of_mem_Ioo (Set.mem_Ioo.mpr ⟨hdpos, by linarith⟩)
  have hsin_uhalf_pos : 0 < sin (u / 2) :=
    Real.sin_pos_of_mem_Ioo hu_half_mem_Ioo
  have hcos_d_pos : 0 < cos d :=
    Real.cos_pos_of_mem_Ioo (Set.mem_Ioo.mpr ⟨by linarith, hdlt⟩)
  have hsin_d_lt_one : sin d < 1 := by
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hdlt
    simpa [Real.sin_pi_div_two] using this
  have hprod_nonneg : 0 ≤ cos d * sin (u / 2) := by
    positivity
  set s := sin d * sin (u / 2) with hs_def
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  have hs_lt_one : s < 1 := by
    dsimp [s]
    have h_sin_uhalf_le_one : sin (u / 2) ≤ 1 := Real.sin_le_one _
    nlinarith
  have h_sqrt_pos : 0 < √(1 - s ^ 2) := by
    refine Real.sqrt_pos.mpr ?_
    nlinarith
  have h_sqrt_le_one : √(1 - s ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith
  calc
    cos d * sin (u / 2) ≤ cos d * sin (u / 2) / √(1 - s ^ 2) :=
      le_div_self hprod_nonneg h_sqrt_pos h_sqrt_le_one
    _ = (cos d / sin d) * ((sin d * sin (u / 2)) / √(1 - s ^ 2)) := by
      field_simp [hsin_d_pos.ne.symm]
    _ = cot d * (s / √(1 - s ^ 2)) := by
      rw [Real.cot_eq_cos_div_sin, hs_def]
    _ = cot d * tan (Real.arcsin s) := by rw [Real.tan_arcsin]
    _ = cot d * tan (Real.arcsin (sin d * sin (u / 2))) := by rfl
    _ = cot d * tan ((2 * Real.arcsin (sin d * sin (u / 2))) / 2) := by
      field_simp
    _ = cot d * tan (ebase d u / 2) := by rw [ebase]

theorem longdiagArg_mem {R : Rnd} (hR : R.Sound) {uh d : ℝ} {J : Iv}
    (hd : J.Mem d) (hd0 : 0 < d ∧ d < π / 2) (hu : 0 < uh ∧ uh < 2 * π) :
    (R.mul (R.div (R.cos J) (R.sin J))
      (R.tan (R.scale (isoBase R (Iv.pt (.ofReal uh)) J) 0.5))).Mem
        (cot d * tan (ebase d uh / 2)) := by
  rcases hd0 with ⟨hd0_pos, hd0_lt⟩
  rcases hu with ⟨hu_pos, hu_lt⟩
  have hd_mem_Ioo : d ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> linarith
  have hsin_d_pos : 0 < sin d :=
    Real.sin_pos_of_pos_of_lt_pi hd0_pos (by linarith)
  have hsin_d_lt_one : sin d < 1 := by
    have := Real.mapsTo_sin_Ioo hd_mem_Ioo
    rcases this with ⟨hlo, hhi⟩
    exact hhi
  have hsin_uh2_pos : 0 < sin (uh / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin_uh2_le_one : sin (uh / 2) ≤ 1 := Real.sin_le_one _
  have hprod_lt_one : sin d * sin (uh / 2) < 1 := by
    nlinarith
  have hprod_gt_neg_one : -1 < sin d * sin (uh / 2) := by
    nlinarith
  have h_arcsin_range : -(π / 2) < arcsin (sin d * sin (uh / 2)) ∧
      arcsin (sin d * sin (uh / 2)) < π / 2 := by
    constructor
    · rw [Real.neg_pi_div_two_lt_arcsin]
      exact hprod_gt_neg_one
    · rw [Real.arcsin_lt_pi_div_two]
      exact hprod_lt_one
  have hebase_eq : ebase d uh / 2 = arcsin (sin d * sin (uh / 2)) := by
    dsimp [ebase]
    ring
  have hebase_half_range : -(π / 2) < ebase d uh / 2 ∧ ebase d uh / 2 < π / 2 := by
    rw [hebase_eq]
    exact h_arcsin_range
  have h_isoBase_mem : (isoBase R (Iv.pt (.ofReal uh)) J).Mem (ebase d uh) :=
    isoBase_mem hR (Iv.mem_pt (x := uh)) hd
  have h_scale_mem : (R.scale (isoBase R (Iv.pt (.ofReal uh)) J) 0.5).Mem (ebase d uh * 0.5) := by
    dsimp [Rnd.scale]
    apply hR.mul
    · exact h_isoBase_mem
    · exact Iv.mem_pt (x := (0.5 : ℝ))
  have h_tan_mem : (R.tan (R.scale (isoBase R (Iv.pt (.ofReal uh)) J) 0.5)).Mem
      (tan (ebase d uh / 2)) := by
    have : ebase d uh * 0.5 = ebase d uh / 2 := by ring
    rw [this] at h_scale_mem
    exact hR.tan (R.scale (isoBase R (Iv.pt (.ofReal uh)) J) 0.5) (ebase d uh / 2)
      h_scale_mem hebase_half_range.1 hebase_half_range.2
  have h_sin_d_ne_zero : sin d ≠ 0 := by linarith
  have h_div_mem : (R.div (R.cos J) (R.sin J)).Mem (cos d / sin d) :=
    hR.div (R.cos J) (R.sin J) (cos d) (sin d) (hR.cos J d hd) (hR.sin J d hd) h_sin_d_ne_zero
  have h_cos_div_sin : cos d / sin d = cot d := by
    rw [Real.cot_eq_cos_div_sin]
  have h_div_mem' : (R.div (R.cos J) (R.sin J)).Mem (cot d) := by
    rw [h_cos_div_sin] at h_div_mem
    exact h_div_mem
  exact hR.mul (R.div (R.cos J) (R.sin J))
    (R.tan (R.scale (isoBase R (Iv.pt (.ofReal uh)) J) 0.5)) (cot d) (tan (ebase d uh / 2))
    h_div_mem' h_tan_mem

theorem longdiagLb_le {R : Rnd} (hR : R.Sound) {ul uh d : ℝ} {J : Iv}
    (hd : J.Mem d) (hd0 : 0 < d ∧ d < π / 2) (hu : 0 < uh ∧ uh < 2 * π) :
    Fl.le (longdiagLb R (Iv.ofReal ul uh) J) (.ofReal (longDiag d uh)) := by
  unfold longdiagLb longDiag
  dsimp
  -- Now the goal is:
  -- (if ¬A.Usable ∨ ¬B.Usable then Fl.ninf else C.lo).le (.ofReal (bangle d uh + arccos (min 1 (cot d * tan (ebase d uh / 2)))))
  -- where A = R.mul (R.div (R.cos J) (R.sin J)) (R.tan (R.scale (isoBase R (Iv.pt (Iv.ofReal ul uh).hi) J) 0.5))
  --       B = isoAngle R (Iv.pt (Iv.ofReal ul uh).hi) J
  --       C = R.add B (Iv.pt (R.acos (Iv.pt (A.hi.min (Fl.ofReal 1)))).lo)
  -- Note: Iv.pt (Iv.ofReal ul uh).hi = Iv.ofReal uh uh definitionally (by rfl)

  set X := cot d * tan (ebase d uh / 2) with hX
  have hX_nonneg : 0 ≤ X := by
    have h := cot_tan_ebase_ge hd0 hu
    have hpos : 0 ≤ cos d * sin (uh / 2) := by
      have hcos : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith, hd0.2⟩
      have hsin : 0 ≤ sin (uh / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by
        have : uh < 2 * π := hu.2
        linarith)
      nlinarith
    linarith

  -- Work with the simplified expressions (Iv.ofReal uh uh is definitionally equal to Iv.pt (Iv.ofReal ul uh).hi)
  -- Let's define abbreviations for readability
  let A : Iv := R.mul (R.div (R.cos J) (R.sin J))
    (R.tan (R.scale (isoBase R (Iv.ofReal uh uh) J) 0.5))
  let B : Iv := isoAngle R (Iv.ofReal uh uh) J

  have hA_mem : A.Mem X :=
    longdiagArg_mem hR hd hd0 hu
  have hB_mem : B.Mem (bangle d uh) :=
    isoAngle_mem hR (hu := ⟨le_rfl, le_rfl⟩) (h0 := hu.1) (h1 := hu.2) (hd := hd) (hd0 := hd0)

  have hA_hi : Fl.le (.ofReal X) A.hi := hA_mem.2
  have hB_lo : Fl.le B.lo (.ofReal (bangle d uh)) := hB_mem.1

  by_cases h_usable : A.Usable ∧ B.Usable
  · rcases h_usable with ⟨hA_u, hB_u⟩
    have h_not_unusable : ¬ (¬ A.Usable ∨ ¬ B.Usable) := by
      intro h; rcases h with (h | h)
      · exact h hA_u
      · exact h hB_u
    dsimp [A, B] at h_not_unusable ⊢
    split_ifs with h_cond
    · exact (h_not_unusable h_cond).elim
    · -- Now the goal is: (R.add (isoAngle R (Iv.ofReal uh uh) J) ...).lo.le (Fl.ofReal ...)
      set m := Fl.min (A.hi) (.ofReal 1) with hm
      have hm_le_one : Fl.le m (.ofReal 1) :=
        Fl.min_le_right (by simp [Fl.ofReal])
      have hlo_le_m : Fl.le (.ofReal (min 1 X)) m := by
        apply Fl.le_min
        · have h_min_le_X : Fl.le (.ofReal (min 1 X)) (.ofReal X) := by
            rw [Fl.ofReal_le_ofReal]
            exact min_le_right _ _
          exact Fl.le_trans h_min_le_X hA_hi
        · rw [Fl.ofReal_le_ofReal]
          exact min_le_left _ _
      have hm_eq : m = .ofReal m.toReal := Fl.eq_ofReal_toReal hlo_le_m hm_le_one
      set r := m.toReal with hr
      have hm_eq' : m = .ofReal r := hm_eq
      have h_min1X_le_r : min 1 X ≤ r := by
        rw [hm_eq'] at hlo_le_m
        rwa [Fl.ofReal_le_ofReal] at hlo_le_m
      have h_neg_one_le_r : (-1 : ℝ) ≤ r := by
        have : 0 ≤ min 1 X := le_min (by norm_num) hX_nonneg
        linarith
      have h_mem : (Iv.pt m).Mem r := by
        dsimp [Iv.Mem, Iv.pt]
        rw [hm_eq']
        exact ⟨le_rfl, le_rfl⟩
      have h_acos_mem : (R.acos (Iv.pt m)).Mem (Real.arccos r) :=
        hR.acos (Iv.pt m) r h_mem h_neg_one_le_r (by
          rw [hm_eq'] at hm_le_one
          rwa [Fl.ofReal_le_ofReal] at hm_le_one)
      have h_acos_lo : Fl.le (R.acos (Iv.pt m)).lo (.ofReal (Real.arccos r)) :=
        h_acos_mem.1
      have h_arccos_le : Real.arccos r ≤ Real.arccos (min 1 X) :=
        Real.arccos_le_arccos h_min1X_le_r
      have h_acos_lo' : Fl.le (R.acos (Iv.pt m)).lo (.ofReal (Real.arccos (min 1 X))) := by
        apply Fl.le_trans h_acos_lo
        rw [Fl.ofReal_le_ofReal]
        exact h_arccos_le
      have h_add_lo : Fl.le (R.add B (Iv.pt (R.acos (Iv.pt m)).lo)).lo
          (.ofReal (bangle d uh + Real.arccos (min 1 X))) :=
        hR.add_lo B (Iv.pt (R.acos (Iv.pt m)).lo) (bangle d uh) (Real.arccos (min 1 X))
          hB_lo (by
            dsimp [Iv.Mem, Iv.pt]
            exact h_acos_lo')
      have h_pt_eq : Iv.pt ((Iv.ofReal ul uh).hi) = Iv.ofReal uh uh := by rfl
      simpa [h_pt_eq, A, B, hX] using h_add_lo
  · -- not usable case
    have h_unusable : ¬ A.Usable ∨ ¬ B.Usable := by
      rcases not_and_or.mp h_usable with (h | h)
      · exact Or.inl h
      · exact Or.inr h
    dsimp [A, B] at h_unusable ⊢
    split_ifs with h_cond
    · -- h_cond is true, so we need to prove Fl.le Fl.ninf (.ofReal ...)
      simp [Fl.le, Fl.ninf, Fl.ofReal]
    · -- h_cond is false, but h_unusable says it's true, contradiction
      exact absurd h_unusable h_cond

theorem bangle_nonpos_of_pi_le {d u : ℝ} (hd : 0 < d ∧ d < π / 2)
    (hu : π ≤ u ∧ u < 2 * π) : bangle d u ≤ 0 := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases hu with ⟨hu_le, hu_lt⟩
  have hd_cos_pos : 0 < cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hd_lt⟩
  have hu_half_pos : 0 < u / 2 := by linarith
  have hu_half_lt_pi : u / 2 < π := by linarith
  have hu_half_ge_pi_div_two : π / 2 ≤ u / 2 := by linarith
  have hcos_nonpos : cos (u / 2) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hu_half_ge_pi_div_two (by linarith)
  have hsin_pos : 0 < sin (u / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hu_half_pos hu_half_lt_pi
  have h_div_nonpos : cos (u / 2) / (cos d * sin (u / 2)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg hcos_nonpos
    nlinarith
  unfold bangle
  exact (Real.arctan_le_zero.mpr h_div_nonpos)

theorem cos_one_gt : (0.53 : ℝ) < cos 1 := by
  have hcos_eq : cos 1 = 2 * cos (1/2) ^ 2 - 1 := by
    calc
      cos 1 = cos (2 * (1/2 : ℝ)) := by norm_num
      _ = 2 * cos (1/2) ^ 2 - 1 := Real.cos_two_mul (1/2)
  have hcos_lower : 7/8 ≤ cos (1/2) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := 1/2)
    have : (1 : ℝ) - ((1 : ℝ)/2)^2 / 2 = 7/8 := by norm_num
    linarith
  have hcos_nonneg : 0 ≤ cos (1/2) := by
    have hmem : (1/2 : ℝ) ∈ Set.Icc (-(π/2)) (π/2) := by
      have hpi : 0 < π := by exact Real.pi_pos
      have hone_lt_pi : (1 : ℝ) < π := by linarith [Real.pi_gt_three]
      constructor <;> linarith
    exact Real.cos_nonneg_of_mem_Icc hmem
  have h_target : (0.53 : ℝ) < 2 * ((7/8 : ℝ) ^ 2) - 1 := by
    norm_num
  have h_bound : 2 * ((7/8 : ℝ) ^ 2) - 1 ≤ 2 * (cos (1/2) ^ 2) - 1 := by
    nlinarith
  linarith

theorem sin_half_ge {u : ℝ} (hu : π < u ∧ u ≤ 3.2) :
    (0.95 : ℝ) ≤ sin (u / 2) := by
  rcases hu with ⟨hπu, hu32⟩
  have hpi_pos : 0 < π := Real.pi_pos
  have h_pi_gt_three : (3 : ℝ) < π := Real.pi_gt_three
  -- from π < u ≤ 3.2 we get π/2 < u/2 ≤ 1.6, hence π/2 < 1.6
  have hu2_low : π / 2 < u / 2 := by linarith
  have hu2_high : u / 2 ≤ 1.6 := by linarith
  have h_pi_div_two_lt_16 : π / 2 < 1.6 := by linarith
  have h16_lt_pi : (1.6 : ℝ) < π := by linarith
  -- set a := u/2 - π/2, b := 1.6 - π/2; both are in [0, π]
  have ha_nonneg : 0 ≤ u / 2 - π / 2 := by linarith
  have ha_le_pi : u / 2 - π / 2 ≤ π := by linarith
  have hb_nonneg : 0 ≤ 1.6 - π / 2 := by linarith
  have hb_le_pi : 1.6 - π / 2 ≤ π := by linarith
  have h_ab : u / 2 - π / 2 ≤ 1.6 - π / 2 := by linarith
  -- cos is antitone on [0, π], so cos(b) ≤ cos(a) when a ≤ b
  have h_cos_le : cos (1.6 - π / 2) ≤ cos (u / 2 - π / 2) :=
    antitoneOn_cos (Set.mem_Icc.mpr ⟨ha_nonneg, ha_le_pi⟩)
      (Set.mem_Icc.mpr ⟨hb_nonneg, hb_le_pi⟩) h_ab
  -- rewrite using cos(x - π/2) = sin x
  have h_cos_a_eq_sin_u : cos (u / 2 - π / 2) = sin (u / 2) := by
    rw [Real.cos_sub_pi_div_two]
  have h_cos_b_eq_sin_16 : cos (1.6 - π / 2) = sin (1.6) := by
    rw [Real.cos_sub_pi_div_two]
  rw [h_cos_a_eq_sin_u, h_cos_b_eq_sin_16] at h_cos_le
  -- now h_cos_le : sin 1.6 ≤ sin (u/2)
  -- need to show sin 1.6 ≥ 0.95
  have h_sin_16_ge : (0.95 : ℝ) ≤ sin (1.6) := by
    -- sin(1.6) = cos(1.6 - π/2) ≥ 1 - (1.6 - π/2)²/2
    have h_cos_ge : 1 - ((1.6 - π / 2) ^ 2) / 2 ≤ cos (1.6 - π / 2) :=
      Real.one_sub_sq_div_two_le_cos
    have h_sin_16_eq_cos : sin (1.6) = cos (1.6 - π / 2) := by
      rw [Real.cos_sub_pi_div_two]
    rw [h_sin_16_eq_cos]
    -- t := 1.6 - π/2 satisfies 0 ≤ t < 0.1 because π > 3
    have ht_nonneg : 0 ≤ 1.6 - π / 2 := by linarith
    have ht_lt : 1.6 - π / 2 < 0.1 := by
      have h : (1.5 : ℝ) < π / 2 := by linarith
      linarith
    -- (1.6 - π/2)² / 2 < 0.05
    have ht_sq_div_two_lt : ((1.6 - π / 2) ^ 2) / 2 < 0.05 := by
      have hsq : (1.6 - π / 2) ^ 2 < (0.1 : ℝ) ^ 2 := by
        nlinarith
      nlinarith
    -- chain: 0.95 = 1 - 0.05 ≤ 1 - t²/2 ≤ cos t = sin 1.6
    calc
      (0.95 : ℝ) = 1 - 0.05 := by norm_num
      _ ≤ 1 - ((1.6 - π / 2) ^ 2) / 2 := by linarith
      _ ≤ cos (1.6 - π / 2) := h_cos_ge
  linarith

theorem longDiag_le_of_pi_lt {d u : ℝ} (hd : 0 < d ∧ d ≤ 1)
    (hu : π < u ∧ u ≤ 3.2) : longDiag d u ≤ π / 3 := by
  rcases hd with ⟨hd_pos, hd_le_one⟩
  rcases hu with ⟨hu_lt, hu_le⟩
  have hd_lt_pi_div_two : d < π / 2 := by
    have h_one_lt_pi_div_two : (1 : ℝ) < π / 2 := by linarith [Real.pi_gt_three]
    linarith
  have hd_bounds : 0 < d ∧ d < π / 2 := ⟨hd_pos, hd_lt_pi_div_two⟩
  have hu_pos : 0 < u := by linarith [Real.pi_pos]
  have hu_lt_two_pi : u < 2 * π := by
    have h_32_lt_2pi : (3.2 : ℝ) < 2 * π := by
      have h3 : (3 : ℝ) < π := Real.pi_gt_three
      linarith
    linarith
  have hu_bounds : π ≤ u ∧ u < 2 * π := ⟨by linarith, hu_lt_two_pi⟩
  have hu_bounds' : 0 < u ∧ u < 2 * π := ⟨hu_pos, hu_lt_two_pi⟩
  have hbangle_nonpos : bangle d u ≤ 0 :=
    bangle_nonpos_of_pi_le hd_bounds hu_bounds
  have h_cot_ge : cos d * sin (u / 2) ≤ cot d * tan (ebase d u / 2) :=
    cot_tan_ebase_ge hd_bounds hu_bounds'
  have h_one_le_pi : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have h_cos_d_ge_cos_one : cos 1 ≤ cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) h_one_le_pi hd_le_one
  have h_cos_d_gt_half : 1/2 < cos d := by
    linarith [cos_one_gt, h_cos_d_ge_cos_one]
  have h_sin_half_ge : (0.95 : ℝ) ≤ sin (u / 2) := sin_half_ge ⟨hu_lt, hu_le⟩
  have h_cos_d_nonneg : 0 ≤ cos d := by
    have h_neg_pi_div_two_lt_d : -(π / 2) < d := by
      have : 0 < π := Real.pi_pos
      linarith
    have hpos : 0 < cos d :=
      Real.cos_pos_of_mem_Ioo ⟨h_neg_pi_div_two_lt_d, hd_lt_pi_div_two⟩
    linarith
  have h_sin_half_nonneg : 0 ≤ sin (u / 2) := by
    have hpos : 0 < sin (u / 2) := Real.sin_pos_of_mem_Ioo ⟨by
      have : 0 < π := Real.pi_pos
      linarith, by
      have : u / 2 < π := by linarith [hu_lt_two_pi]
      exact this⟩
    linarith
  have h_prod_gt_half : 1/2 < cos d * sin (u / 2) := by
    have h_prod : (0.53 : ℝ) * (0.95 : ℝ) ≤ cos d * sin (u / 2) :=
      mul_le_mul (by linarith [cos_one_gt, h_cos_d_ge_cos_one]) h_sin_half_ge (by norm_num) h_cos_d_nonneg
    have h_053_095_gt_half : 1/2 < (0.53 : ℝ) * (0.95 : ℝ) := by norm_num
    linarith
  have h_X_gt_half : 1/2 < cot d * tan (ebase d u / 2) := by
    linarith
  have h_min_ge_half : 1/2 ≤ min 1 (cot d * tan (ebase d u / 2)) := by
    have h_one_ge_half : 1/2 ≤ (1 : ℝ) := by norm_num
    exact le_min h_one_ge_half (by linarith)
  have h_arccos_min_le_arccos_half : arccos (min 1 (cot d * tan (ebase d u / 2))) ≤ arccos (1/2) :=
    Real.arccos_le_arccos h_min_ge_half
  have h_arccos_half_eq : arccos (1/2) = π/3 := by
    have h_cos_pi_div_three : cos (π/3) = 1/2 := Real.cos_pi_div_three
    have h_pi_div_three_nonneg : 0 ≤ π/3 := by linarith [Real.pi_pos]
    have h_pi_div_three_le_pi : π/3 ≤ π := by linarith
    calc
      arccos (1/2) = arccos (cos (π/3)) := by rw [h_cos_pi_div_three]
      _ = π/3 := Real.arccos_cos h_pi_div_three_nonneg h_pi_div_three_le_pi
  rw [longDiag]
  linarith

theorem eta_monotoneOn_e {g f a b : ℝ} (hf : 0 < f ∧ f < π) (ha : 0 < a)
    (hb : b < π) (hs : ∀ e ∈ Set.Icc a b, 0 ≤ cos f - cos e * cos g) :
    MonotoneOn (fun e => eta g e f) (Set.Icc a b) := by
  have hf_pos : 0 < f := hf.1
  have hf_lt_pi : f < π := hf.2
  have h_convex : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have h_cont : ContinuousOn (fun e => eta g e f) (Set.Icc a b) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    have hx_lt_pi : x < π := lt_of_le_of_lt hx.2 hb
    have h_deriv := eta_hasDerivAt_e g x f ⟨hx_pos, hx_lt_pi⟩ ⟨hf_pos, hf_lt_pi⟩
    exact h_deriv.continuousAt.continuousWithinAt
  have h_diff : DifferentiableOn ℝ (fun e => eta g e f) (interior (Set.Icc a b)) := by
    rw [interior_Icc]
    intro x hx
    have hx_pos : 0 < x := lt_trans ha hx.1
    have hx_lt_pi : x < π := lt_trans hx.2 hb
    have h_deriv := eta_hasDerivAt_e g x f ⟨hx_pos, hx_lt_pi⟩ ⟨hf_pos, hf_lt_pi⟩
    exact h_deriv.differentiableAt.differentiableWithinAt
  have h_deriv_nonneg : ∀ x ∈ interior (Set.Icc a b), 0 ≤ deriv (fun e => eta g e f) x := by
    rw [interior_Icc]
    intro x hx
    have hx_pos : 0 < x := lt_trans ha hx.1
    have hx_lt_pi : x < π := lt_trans hx.2 hb
    have h_deriv := eta_hasDerivAt_e g x f ⟨hx_pos, hx_lt_pi⟩ ⟨hf_pos, hf_lt_pi⟩
    have h_deriv_eq : deriv (fun e => eta g e f) x =
        sin f * (cos f - cos x * cos g) / (sin x * sin f) ^ 2 :=
      h_deriv.deriv
    rw [h_deriv_eq]
    have h_sin_f_pos : 0 < sin f := sin_pos_of_pos_of_lt_pi hf_pos hf_lt_pi
    have h_sin_x_pos : 0 < sin x := sin_pos_of_pos_of_lt_pi hx_pos hx_lt_pi
    have h_num_nonneg : 0 ≤ sin f * (cos f - cos x * cos g) := by
      have h_cos_diff_nonneg : 0 ≤ cos f - cos x * cos g :=
        hs x (Set.mem_Icc.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
      nlinarith
    have h_denom_nonneg : 0 ≤ (sin x * sin f) ^ 2 := by
      have h_prod_nonneg : 0 ≤ sin x * sin f := mul_nonneg (le_of_lt h_sin_x_pos) (le_of_lt h_sin_f_pos)
      nlinarith [sq_nonneg (sin x * sin f)]
    exact div_nonneg h_num_nonneg h_denom_nonneg
  exact monotoneOn_of_deriv_nonneg h_convex h_cont h_diff h_deriv_nonneg

theorem eta_antitoneOn_e {g f a b : ℝ} (hf : 0 < f ∧ f < π) (ha : 0 < a)
    (hb : b < π) (hs : ∀ e ∈ Set.Icc a b, cos f - cos e * cos g ≤ 0) :
    AntitoneOn (fun e => eta g e f) (Set.Icc a b) := by
  rcases hf with ⟨hf_pos, hf_lt_pi⟩
  have h_sin_f_pos : 0 < sin f := Real.sin_pos_of_pos_of_lt_pi hf_pos hf_lt_pi
  have h_convex : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have h_cont : ContinuousOn (fun e => eta g e f) (Set.Icc a b) := by
    have h_den_nonzero : ∀ e ∈ Set.Icc a b, sin e * sin f ≠ 0 := by
      intro e he
      rcases he with ⟨he_left, he_right⟩
      have h_sin_e_pos : 0 < sin e := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      exact mul_ne_zero (ne_of_gt h_sin_e_pos) (ne_of_gt h_sin_f_pos)
    have h_num_cont : ContinuousOn (fun e : ℝ => cos g - cos e * cos f) (Set.Icc a b) :=
      (continuous_const.sub ((Real.continuous_cos.comp continuous_id).mul continuous_const)).continuousOn
    have h_den_cont : ContinuousOn (fun e : ℝ => sin e * sin f) (Set.Icc a b) :=
      ((Real.continuous_sin.comp continuous_id).mul continuous_const).continuousOn
    refine h_num_cont.div h_den_cont h_den_nonzero
  have h_diff : DifferentiableOn ℝ (fun e => eta g e f) (interior (Set.Icc a b)) := by
    rw [interior_Icc]
    intro x hx
    rcases hx with ⟨hx_left, hx_right⟩
    have hx_pos : 0 < x := by linarith
    have hx_lt_pi : x < π := by linarith
    have h_hasDeriv : HasDerivAt (fun e => eta g e f)
        (sin f * (cos f - cos x * cos g) / (sin x * sin f) ^ 2) x :=
      eta_hasDerivAt_e g x f ⟨hx_pos, hx_lt_pi⟩ ⟨hf_pos, hf_lt_pi⟩
    exact h_hasDeriv.differentiableAt.differentiableWithinAt
  have h_deriv_nonpos : ∀ x ∈ interior (Set.Icc a b), deriv (fun e => eta g e f) x ≤ 0 := by
    rw [interior_Icc]
    intro x hx
    rcases hx with ⟨hx_left, hx_right⟩
    have hx_pos : 0 < x := by linarith
    have hx_lt_pi : x < π := by linarith
    have h_sin_x_pos : 0 < sin x := Real.sin_pos_of_pos_of_lt_pi hx_pos hx_lt_pi
    have h_hasDeriv : HasDerivAt (fun e => eta g e f)
        (sin f * (cos f - cos x * cos g) / (sin x * sin f) ^ 2) x :=
      eta_hasDerivAt_e g x f ⟨hx_pos, hx_lt_pi⟩ ⟨hf_pos, hf_lt_pi⟩
    have h_deriv_eq : deriv (fun e => eta g e f) x =
        sin f * (cos f - cos x * cos g) / (sin x * sin f) ^ 2 :=
      h_hasDeriv.deriv
    rw [h_deriv_eq]
    have h_num_nonpos : sin f * (cos f - cos x * cos g) ≤ 0 := by
      have h_cos_nonpos : cos f - cos x * cos g ≤ 0 :=
        hs x ⟨by linarith, by linarith⟩
      have h_sin_f_nonneg : 0 ≤ sin f := by linarith
      have h := mul_nonpos_of_nonpos_of_nonneg h_cos_nonpos h_sin_f_nonneg
      simpa [mul_comm] using h
    have h_den_nonneg : 0 ≤ (sin x * sin f) ^ 2 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg h_num_nonpos h_den_nonneg
  exact antitoneOn_of_deriv_nonpos h_convex h_cont h_diff h_deriv_nonpos

theorem meet_mem {I J : Iv} {x : ℝ} (hI : I.Mem x) (hJ : J.Mem x) :
    (I.meet J).Mem x := by
  rcases hI with ⟨hIlo, hIhi⟩
  rcases hJ with ⟨hJlo, hJhi⟩
  exact ⟨Fl.max_le hIlo hJlo, Fl.le_min hIhi hJhi⟩

theorem nar_subset {ι : Type} {B B' : Box ι} {j : ι} {n : Iv}
    (h : nar B j n = some B') (v : ι) : B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v := by
  unfold nar at h
  by_cases hUsable : n.Usable
  · simp [hUsable] at h
    by_cases hlt : Fl.lt (Fl.min (Fl.ofReal (B.hi j)) n.hi) (Fl.max (Fl.ofReal (B.lo j)) n.lo)
    · simp [hlt] at h
    · simp [hlt] at h
      have h_inner : (⟨Function.update B.lo j (Fl.max (Fl.ofReal (B.lo j)) n.lo).toReal,
        Function.update B.hi j (Fl.min (Fl.ofReal (B.hi j)) n.hi).toReal⟩ : Box ι) = B' := h
      rcases h_inner with rfl
      by_cases hvj : v = j
      · rw [hvj]
        simp
        cases n with | mk nlo nhi =>
          cases nlo with
          | num a =>
            cases nhi with
            | num b =>
              have hUsable' : a ≤ b := by
                simpa [Iv.Usable, Fl.le] using hUsable
              have hlt' : ¬ (min (B.hi j : EReal) b) < (max (B.lo j : EReal) a) := by
                simpa [Fl.ofReal, Fl.min, Fl.max, Fl.lt] using hlt
              have hle : max (B.lo j : EReal) a ≤ min (B.hi j : EReal) b :=
                not_lt.mp hlt'
              have hlo_fl : Fl.le (Fl.ofReal (B.lo j)) (Fl.max (Fl.ofReal (B.lo j)) (Fl.num a)) := by
                have h_ne_nan : Fl.ofReal (B.lo j) ≠ Fl.nan := by simp [Fl.ofReal]
                exact Fl.le_max_left h_ne_nan
              have hhi_fl : Fl.le (Fl.max (Fl.ofReal (B.lo j)) (Fl.num a)) (Fl.ofReal (B.hi j)) := by
                have h_max_le_hi : max (B.lo j : EReal) a ≤ (B.hi j : EReal) := by
                  have h_min_le_hi : min (B.hi j : EReal) b ≤ (B.hi j : EReal) := min_le_left _ _
                  exact le_trans hle h_min_le_hi
                simpa [Fl.ofReal, Fl.max, Fl.le] using h_max_le_hi
              have hbounds := Fl.le_ofReal_toReal hlo_fl hhi_fl
              rcases hbounds with ⟨hlo, hhi⟩
              have hlo_min_fl : Fl.le (Fl.ofReal (B.lo j)) (Fl.min (Fl.ofReal (B.hi j)) (Fl.num b)) := by
                have h_lo_le_min : (B.lo j : EReal) ≤ min (B.hi j : EReal) b :=
                  le_trans (le_max_left _ _) hle
                simpa [Fl.ofReal, Fl.min, Fl.le] using h_lo_le_min
              have hhi_min_fl : Fl.le (Fl.min (Fl.ofReal (B.hi j)) (Fl.num b)) (Fl.ofReal (B.hi j)) := by
                simp [Fl.ofReal, Fl.min, Fl.le, min_le_left (B.hi j : EReal) b]
              have hbounds2 := Fl.le_ofReal_toReal hlo_min_fl hhi_min_fl
              rcases hbounds2 with ⟨_, hhi2⟩
              exact ⟨hlo, hhi2⟩
            | nan => simp [Iv.Usable, Fl.le] at hUsable
          | nan => simp [Iv.Usable, Fl.le] at hUsable
      · simp [hvj]
  · simp [hUsable] at h
    rcases h with rfl
    exact ⟨le_refl _, le_refl _⟩

theorem ite_none_eq_some {α : Type} {p : Prop} [Decidable p] {x : Option α} {y : α}
    (h : (if p then none else x) = some y) : x = some y := by
  split_ifs at h
  exact h

/-- The new lower end of a variable in system.rs `fbbt` is not below the old one. -/
theorem le_ite_toReal {a : Fl} {l : ℝ} (ha : ∃ y, Fl.le a (.ofReal y)) :
    l ≤ (if Fl.lt (.ofReal l) a then a.toReal else l) := by
  split_ifs with hlt
  · obtain ⟨y, hy⟩ := ha
    exact (Fl.le_ofReal_toReal (Fl.le_of_lt hlt) hy).1
  · exact le_rfl

/-- The new upper end of a variable in system.rs `fbbt` is not above the old one. -/
theorem ite_toReal_le {a : Fl} {h : ℝ} (ha : ∃ y, Fl.le (.ofReal y) a) :
    (if Fl.lt a (.ofReal h) then a.toReal else h) ≤ h := by
  split_ifs with hlt
  · obtain ⟨y, hy⟩ := ha
    exact (Fl.le_ofReal_toReal hy (Fl.le_of_lt hlt)).2
  · exact le_rfl

theorem nlo_bounded {R : Rnd} (hR : R.Sound) {c : ℝ} (hc : c ≠ 0) (cup cdn : Fl) :
    ∃ y, Fl.le (if 0 < c then (if cdn.IsFinite then R.divDn cdn (.ofReal c) else Fl.ninf)
      else (if cup.IsFinite then R.divDn cup (.ofReal c) else Fl.ninf)) (.ofReal y) := by
  split_ifs with h1 h2 h3
  · have h := hR.divDn cdn.toReal c hc
    rw [← isFinite_eq_ofReal_toReal h2] at h
    exact ⟨_, h⟩
  · exact ⟨0, Fl.ninf_le 0⟩
  · have h := hR.divDn cup.toReal c hc
    rw [← isFinite_eq_ofReal_toReal h3] at h
    exact ⟨_, h⟩
  · exact ⟨0, Fl.ninf_le 0⟩

theorem nhi_bounded {R : Rnd} (hR : R.Sound) {c : ℝ} (hc : c ≠ 0) (cup cdn : Fl) :
    ∃ y, Fl.le (.ofReal y) (if 0 < c then (if cup.IsFinite then R.divUp cup (.ofReal c) else Fl.inf)
      else (if cdn.IsFinite then R.divUp cdn (.ofReal c) else Fl.inf)) := by
  split_ifs with h1 h2 h3
  · have h := hR.divUp cup.toReal c hc
    rw [← isFinite_eq_ofReal_toReal h2] at h
    exact ⟨_, h⟩
  · exact ⟨0, Fl.le_inf 0⟩
  · have h := hR.divUp cdn.toReal c hc
    rw [← isFinite_eq_ofReal_toReal h3] at h
    exact ⟨_, h⟩
  · exact ⟨0, Fl.le_inf 0⟩

/-- The second loop of system.rs `fbbt` only shrinks the box. -/
theorem rowUpd_subset {ι : Type} {R : Rnd} (hR : R.Sound) (r : Row ι) (smin smax : Fl) :
    ∀ (L : List ((ι × ℝ) × Fl × Fl)) (B B' : Box ι), rowUpd R r smin smax L B = some B' →
      ∀ v, B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v := by
  intro L
  induction L with
  | nil =>
    intro B B' h v
    simp only [rowUpd, Option.some.injEq] at h
    subst h
    exact ⟨le_rfl, le_rfl⟩
  | cons p l ih =>
    intro B B' h u
    obtain ⟨⟨w, c⟩, mn, mx⟩ := p
    by_cases hc : c = 0
    · simp only [rowUpd, hc, ↓reduceIte] at h
      exact ih B B' h u
    · simp only [rowUpd, hc, ↓reduceIte] at h
      have h' := ite_none_eq_some h
      obtain ⟨h1, h2⟩ := ih _ B' h' u
      refine ⟨le_trans ?_ h1, le_trans h2 ?_⟩
      · by_cases hu : u = w
        · subst hu
          simp only [Function.update_self]
          exact le_ite_toReal (nlo_bounded hR hc _ _)
        · simp [Function.update_of_ne hu]
      · by_cases hu : u = w
        · subst hu
          simp only [Function.update_self]
          exact ite_toReal_le (nhi_bounded hR hc _ _)
        · simp [Function.update_of_ne hu]

theorem rowStep_subset {ι : Type} {R : Rnd} (hR : R.Sound) (r : Row ι)
    {B B' : Box ι} (h : rowStep R r B = some B') (v : ι) :
    B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v := by
  unfold rowStep at h
  dsimp only at h
  exact rowUpd_subset hR r _ _ _ B B' (ite_none_eq_some h) v

end Tammes15.Contractors
