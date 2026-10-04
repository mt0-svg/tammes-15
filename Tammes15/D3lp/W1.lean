import Tammes15.D3lp.Kill
import Tammes15.D3lp.Monot
import Tammes15.Params.Checks

open Real

namespace Tammes15.D3lp

open Tammes15

open scoped Classical

noncomputable def darts (P : PlaneGraph) (v : Fin P.n) : Finset P.G.Dart :=
  Finset.univ.filter (fun e : P.G.Dart => e.fst = v)

noncomputable def triCount (P : PlaneGraph) (v : Fin P.n) : ℕ :=
  ((darts P v).filter (fun e => fsize P e = 3)).card

noncomputable def rhoCount (P : PlaneGraph) (v : Fin P.n) : ℕ :=
  ((darts P v).filter (fun e => fsize P e = 4)).card

noncomputable def bigCount (P : PlaneGraph) (v : Fin P.n) : ℕ :=
  ((darts P v).filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4)).card

def W1Type (t q p : ℕ) : Prop :=
  t + q + p ≤ 5 ∧ (2 ≤ p ∨ (p = 1 ∧ 3 ≤ t + 2 * q) ∨ (p = 0 ∧ 6 ≤ t + 2 * q))

instance (t q p : ℕ) : Decidable (W1Type t q p) := by
  unfold W1Type
  infer_instance

def W1Graph (P : PlaneGraph) : Prop :=
  ∀ v, W1Type (triCount P v) (rhoCount P v) (bigCount P v)

def W1Real (t q p : ℕ) : Prop :=
  ∃ a : ℝ, alpha dlo ≤ a ∧ a ≤ alpha dhi ∧ ((t + q + p : ℕ) : ℝ) * a ≤ 2 * π ∧
    2 * π ≤ ((t + 2 * q : ℕ) : ℝ) * a + (p : ℝ) * π

theorem sum_split3 {ι : Type} (s : Finset ι) (g : ι → ℕ) (f : ι → ℝ) :
    ∑ e ∈ s, f e = ∑ e ∈ s.filter (fun e => g e = 3), f e +
      ∑ e ∈ s.filter (fun e => g e = 4), f e +
      ∑ e ∈ s.filter (fun e => g e ≠ 3 ∧ g e ≠ 4), f e := by
  calc
    ∑ e ∈ s, f e = (∑ e ∈ s.filter (fun e => g e = 3), f e) + (∑ e ∈ s.filter (fun e => g e ≠ 3), f e) := by
      rw [← Finset.sum_filter_add_sum_filter_not s (fun e => g e = 3) f]
    _ = (∑ e ∈ s.filter (fun e => g e = 3), f e) + ((∑ e ∈ (s.filter (fun e => g e ≠ 3)).filter (fun e => g e = 4), f e) + (∑ e ∈ (s.filter (fun e => g e ≠ 3)).filter (fun e => g e ≠ 4), f e)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun e => g e ≠ 3)) (fun e => g e = 4) f]
    _ = (∑ e ∈ s.filter (fun e => g e = 3), f e) + ((∑ e ∈ s.filter (fun e => g e = 4), f e) + (∑ e ∈ s.filter (fun e => g e ≠ 3 ∧ g e ≠ 4), f e)) := by
      have h1 : (s.filter (fun e => g e ≠ 3)).filter (fun e => g e = 4) = s.filter (fun e => g e = 4) := by
        ext e; simp; omega
      have h2 : (s.filter (fun e => g e ≠ 3)).filter (fun e => g e ≠ 4) = s.filter (fun e => g e ≠ 3 ∧ g e ≠ 4) := by
        simp [Finset.filter_filter]
      simp [h1, h2]
    _ = ∑ e ∈ s.filter (fun e => g e = 3), f e + ∑ e ∈ s.filter (fun e => g e = 4), f e + ∑ e ∈ s.filter (fun e => g e ≠ 3 ∧ g e ≠ 4), f e := by ring

theorem card_split3 {ι : Type} (s : Finset ι) (g : ι → ℕ) :
    s.card = (s.filter (fun e => g e = 3)).card + (s.filter (fun e => g e = 4)).card +
      (s.filter (fun e => g e ≠ 3 ∧ g e ≠ 4)).card := by
  have h1 := Finset.card_filter_add_card_filter_not (fun e => g e = 3) (s := s)
  have h2 := Finset.card_filter_add_card_filter_not (fun e => g e = 4) (s := s.filter (fun e => g e ≠ 3))
  have hfilter4 : (s.filter (fun e => g e ≠ 3)).filter (fun e => g e = 4) = s.filter (fun e => g e = 4) := by
    ext e
    constructor
    · intro h
      rcases Finset.mem_filter.mp h with ⟨he_mem, hg⟩
      rcases Finset.mem_filter.mp he_mem with ⟨he, hg_ne_3⟩
      exact Finset.mem_filter.mpr ⟨he, hg⟩
    · intro h
      rcases Finset.mem_filter.mp h with ⟨he, hg⟩
      have hg_ne_3 : g e ≠ 3 := by
        rw [hg]
        decide
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he, hg_ne_3⟩, hg⟩
  have hfilter_other : (s.filter (fun e => g e ≠ 3)).filter (fun e => g e ≠ 4) = s.filter (fun e => g e ≠ 3 ∧ g e ≠ 4) := by
    ext e
    simp [and_assoc]
  rw [hfilter4, hfilter_other] at h2
  calc
    s.card = (s.filter (fun e => g e = 3)).card + (s.filter (fun e => g e ≠ 3)).card := by rw [← h1]
    _ = (s.filter (fun e => g e = 3)).card + ((s.filter (fun e => g e = 4)).card + (s.filter (fun e => g e ≠ 3 ∧ g e ≠ 4)).card) := by rw [← h2]
    _ = (s.filter (fun e => g e = 3)).card + (s.filter (fun e => g e = 4)).card + (s.filter (fun e => g e ≠ 3 ∧ g e ≠ 4)).card := by rw [add_assoc]

theorem rhombus_corner_le {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k}
    (hR : RelSys P H A) (hd : 0 < A.d ∧ A.d < π / 2) (e : P.G.Dart) (he : fsize P e = 4) :
    A.corner e ≤ 2 * alpha A.d := by
  have hrhombus := hR.rhombus e he
  rcases hrhombus with ⟨h_eq, h_rho⟩
  have hx : alpha A.d ≤ A.fc e 0 ∧ A.fc e 0 < π := by
    simpa [Assign.fc] using hR.corner_mem e
  have hy' : alpha A.d ≤ A.fc e 1 := by
    simpa [Assign.fc] using (hR.corner_mem (P.R.face e)).1
  have h_result := rhombus_rows A.d (A.fc e 0) (A.fc e 1) hd h_rho hx hy'
  rcases h_result with ⟨h_le, _, _, _⟩
  simpa [Assign.fc] using h_le

theorem vertex_bounds {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k}
    (hR : RelSys P H A) (hd : 0 < A.d ∧ A.d < π / 2) (v : Fin P.n) :
    ((triCount P v + rhoCount P v + bigCount P v : ℕ) : ℝ) * alpha A.d ≤ 2 * π ∧
      2 * π ≤ ((triCount P v + 2 * rhoCount P v : ℕ) : ℝ) * alpha A.d +
        (bigCount P v : ℝ) * π := by
  rcases hd with ⟨hdpos, hdlt⟩
  set s := darts P v with hs
  have hsum : ∑ e ∈ s, A.corner e = 2 * π := by
    simpa [hs, darts] using hR.vertex_sum v
  have hcard_split := card_split3 s (fsize P)
  have hsum_split := sum_split3 s (fsize P) A.corner
  have htri_eq : ∑ e ∈ s.filter (fun e => fsize P e = 3), A.corner e = (triCount P v : ℝ) * alpha A.d := by
    calc
      ∑ e ∈ s.filter (fun e => fsize P e = 3), A.corner e
          = ∑ e ∈ s.filter (fun e => fsize P e = 3), alpha A.d := by
            refine Finset.sum_congr rfl (fun e he => ?_)
            have he_size : fsize P e = 3 := (Finset.mem_filter.mp he).2
            exact hR.tri e he_size
      _ = ((s.filter (fun e => fsize P e = 3)).card : ℝ) * alpha A.d := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (triCount P v : ℝ) * alpha A.d := by simp [triCount, darts, hs]
  have hrho_le : ∑ e ∈ s.filter (fun e => fsize P e = 4), A.corner e ≤ (rhoCount P v : ℝ) * (2 * alpha A.d) := by
    calc
      ∑ e ∈ s.filter (fun e => fsize P e = 4), A.corner e
          ≤ ∑ e ∈ s.filter (fun e => fsize P e = 4), (2 * alpha A.d) :=
            Finset.sum_le_sum (fun e he => ?_)
      _ = ((s.filter (fun e => fsize P e = 4)).card : ℝ) * (2 * alpha A.d) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (rhoCount P v : ℝ) * (2 * alpha A.d) := by simp [rhoCount, darts, hs]
    have he_size : fsize P e = 4 := (Finset.mem_filter.mp he).2
    exact rhombus_corner_le hR ⟨hdpos, hdlt⟩ e he_size
  have hbig_le : ∑ e ∈ s.filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4), A.corner e ≤ (bigCount P v : ℝ) * π := by
    calc
      ∑ e ∈ s.filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4), A.corner e
          ≤ ∑ e ∈ s.filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4), π :=
            Finset.sum_le_sum (fun e he => ?_)
      _ = ((s.filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4)).card : ℝ) * π := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (bigCount P v : ℝ) * π := by simp [bigCount, darts, hs]
    have hcorner_lt := (hR.corner_mem e).2
    exact le_of_lt hcorner_lt
  have hlower : (s.card : ℝ) * alpha A.d ≤ 2 * π := by
    have hle : s.card • alpha A.d ≤ ∑ e ∈ s, A.corner e :=
      Finset.card_nsmul_le_sum s A.corner (alpha A.d) (fun e _ => (hR.corner_mem e).1)
    have htemp := hle.trans_eq hsum
    simpa [nsmul_eq_mul] using htemp
  have hcard_eq : (s.card : ℝ) = ((triCount P v + rhoCount P v + bigCount P v : ℕ) : ℝ) := by
    simpa [triCount, rhoCount, bigCount, darts, hs] using congrArg (fun x : ℕ => (x : ℝ)) hcard_split
  have hlower' : ((triCount P v + rhoCount P v + bigCount P v : ℕ) : ℝ) * alpha A.d ≤ 2 * π := by
    simpa [hcard_eq] using hlower
  have hupper : 2 * π ≤ ((triCount P v + 2 * rhoCount P v : ℕ) : ℝ) * alpha A.d + (bigCount P v : ℝ) * π := by
    have hsum_eq := hsum
    rw [hsum_split] at hsum_eq
    rw [htri_eq] at hsum_eq
    have hineq : (triCount P v : ℝ) * alpha A.d + (rhoCount P v : ℝ) * (2 * alpha A.d) + (bigCount P v : ℝ) * π ≥ 2 * π := by
      linarith
    have hrearr : (triCount P v : ℝ) * alpha A.d + (rhoCount P v : ℝ) * (2 * alpha A.d) + (bigCount P v : ℝ) * π
        = ((triCount P v + 2 * rhoCount P v : ℕ) : ℝ) * alpha A.d + (bigCount P v : ℝ) * π := by
      push_cast
      ring
    rw [hrearr] at hineq
    exact hineq
  exact And.intro hlower' hupper

theorem deg_le_five {m : ℕ} {a : ℝ} (ha : π / 3 < a) (h : (m : ℝ) * a ≤ 2 * π) : m ≤ 5 := by
  by_contra! hc
  have hm : (6 : ℕ) ≤ m := by omega
  have hm' : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ha_pos : 0 < a := by
    have hpi : 0 < π := by exact Real.pi_pos
    linarith
  have hineq : (6 : ℝ) * a ≤ (m : ℝ) * a := by
    nlinarith
  have hbound : 2 * π < (6 : ℝ) * a := by
    nlinarith
  nlinarith

theorem three_le_of_one {s : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ (1.20830549335659207180 : ℝ))
    (h : 2 * π ≤ (s : ℝ) * a + 1 * π) : 3 ≤ s := by
  by_contra! hlt

  have hs : s ≤ 2 := by omega
  have hs' : (s : ℝ) ≤ 2 := by exact_mod_cast hs
  have hineq1 : π ≤ (s : ℝ) * a := by
    linarith
  have hineq2 : (s : ℝ) * a ≤ 2 * a := by
    nlinarith
  have hineq3 : 2 * a ≤ 2 * (1.20830549335659207180 : ℝ) := by
    nlinarith
  have hpi : 2 * (1.20830549335659207180 : ℝ) < π := by
    have h3 : 2 * (1.20830549335659207180 : ℝ) < (3 : ℝ) := by norm_num
    have h3pi : (3 : ℝ) < π := Real.pi_gt_three
    linarith
  linarith

theorem six_le_of_zero {s : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ (1.20830549335659207180 : ℝ))
    (h : 2 * π ≤ (s : ℝ) * a + 0 * π) : 6 ≤ s := by
  by_contra! H
  have hs_nat : s ≤ 5 := by
    have : s < 6 := H
    omega
  have hs : (s : ℝ) ≤ 5 := by exact_mod_cast hs_nat
  have hprod : (s : ℝ) * a ≤ 5 * a := by
    nlinarith
  have hbound : 5 * a ≤ 5 * (1.20830549335659207180 : ℝ) := by
    nlinarith
  have hcalc : 5 * (1.20830549335659207180 : ℝ) < 2 * π := by
    nlinarith [Real.pi_gt_d2]
  have hfinal : (s : ℝ) * a < 2 * π := by
    nlinarith
  have hfromh : 2 * π ≤ (s : ℝ) * a := by
    simpa [zero_mul, add_zero] using h
  nlinarith

theorem w1Type_of_bounds {t q p : ℕ} {a : ℝ} (ha1 : π / 3 < a)
    (ha2 : a ≤ (1.20830549335659207180 : ℝ)) (hlo : ((t + q + p : ℕ) : ℝ) * a ≤ 2 * π)
    (hhi : 2 * π ≤ ((t + 2 * q : ℕ) : ℝ) * a + (p : ℝ) * π) : W1Type t q p := by
  have hsum : t + q + p ≤ 5 := deg_le_five ha1 hlo
  have ha0 : 0 ≤ a := by linarith [ha1, Real.pi_pos]
  rcases Nat.lt_or_ge p 2 with (hp | hp)
  · have hp' : p = 0 ∨ p = 1 := by omega
    rcases hp' with (rfl | rfl)
    · have h6 : 6 ≤ t + 2 * q := six_le_of_zero ha0 ha2 (by simpa [Nat.cast_zero] using hhi)
      refine ⟨hsum, Or.inr (Or.inr ⟨rfl, h6⟩)⟩
    · have h3 : 3 ≤ t + 2 * q := three_le_of_one ha0 ha2 (by simpa [Nat.cast_one] using hhi)
      refine ⟨hsum, Or.inr (Or.inl ⟨rfl, h3⟩)⟩
  · refine ⟨hsum, Or.inl hp⟩

theorem bounds_of_w1Type {t q p : ℕ} {a : ℝ} (ha1 : π / 3 ≤ a)
    (ha2 : a ≤ (1.20830549335659207180 : ℝ)) (h : W1Type t q p) :
    ((t + q + p : ℕ) : ℝ) * a ≤ 2 * π ∧ 2 * π ≤ ((t + 2 * q : ℕ) : ℝ) * a + (p : ℝ) * π := by
  rcases h with ⟨hle, hcases⟩
  have ha_nonneg : 0 ≤ a := by
    have : 0 < π := Real.pi_pos
    nlinarith
  have hle' : ((t + q + p : ℕ) : ℝ) ≤ (5 : ℝ) := by exact_mod_cast hle
  have h_first : ((t + q + p : ℕ) : ℝ) * a ≤ 2 * π := by
    have hprod : ((t + q + p : ℕ) : ℝ) * a ≤ (5 : ℝ) * a := by
      nlinarith
    have h5a : (5 : ℝ) * a ≤ 2 * π := by
      have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
      have hcalc : (5 : ℝ) * (1.20830549335659207180 : ℝ) < 2 * (3.14 : ℝ) := by
        norm_num
      have h5a' : (5 : ℝ) * a ≤ (5 : ℝ) * (1.20830549335659207180 : ℝ) := by
        nlinarith
      have h2pi : 2 * (3.14 : ℝ) < 2 * π := by nlinarith
      linarith
    nlinarith
  have h_second : 2 * π ≤ ((t + 2 * q : ℕ) : ℝ) * a + (p : ℝ) * π := by
    rcases hcases with (hp2 | hpcase | hpcase)
    ·
      have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have h_nonneg : 0 ≤ ((t + 2 * q : ℕ) : ℝ) * a := by
        have : 0 ≤ ((t + 2 * q : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
        nlinarith
      nlinarith [Real.pi_pos]
    ·
      rcases hpcase with ⟨hp1, hsum⟩
      have hp1' : (p : ℝ) = 1 := by exact_mod_cast hp1
      have hsum' : (3 : ℝ) ≤ ((t + 2 * q : ℕ) : ℝ) := by exact_mod_cast hsum
      nlinarith
    ·
      rcases hpcase with ⟨hp0, hsum⟩
      have hp0' : (p : ℝ) = 0 := by exact_mod_cast hp0
      have hsum' : (6 : ℝ) ≤ ((t + 2 * q : ℕ) : ℝ) := by exact_mod_cast hsum
      nlinarith
  exact And.intro h_first h_second

theorem w1Type_iff_real (t q p : ℕ) : W1Type t q p ↔ W1Real t q p := by
  have hπ_pos : 0 < π := by exact Real.pi_pos
  have hdlo_pos : 0 < dlo := by
    have h := pi_div_four_lt_dlo
    linarith
  have hdhi_pos : 0 < dhi := by
    linarith [dlo_lt_dhi, hdlo_pos]
  have hdlo_lt_pi2 : dlo < π / 2 := by
    have h := dlo_lt_dhi
    have hdhi_lt : dhi < π / 2 := by
      linarith [dhi_lt_pi_div_three]
    linarith
  have hdhi_lt_pi2 : dhi < π / 2 := by
    linarith [dhi_lt_pi_div_three]
  have hdlo_mem : dlo ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hdlo_pos, hdlo_lt_pi2⟩
  have hdhi_mem : dhi ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hdhi_pos, hdhi_lt_pi2⟩
  have hπ3_dlo : π / 3 < alpha dlo := (alpha_bounds dlo ⟨hdlo_pos, hdlo_lt_pi2⟩).1
  have hπ3_dhi : π / 3 ≤ alpha dhi := by
    have hlt : alpha dlo < alpha dhi := alpha_strictMonoOn hdlo_mem hdhi_mem dlo_lt_dhi
    linarith
  have hdlo_le_dhi : alpha dlo ≤ alpha dhi :=
    le_of_lt (alpha_strictMonoOn hdlo_mem hdhi_mem dlo_lt_dhi)
  constructor
  · intro h
    refine ⟨alpha dhi, hdlo_le_dhi, le_refl _, ?_⟩
    exact bounds_of_w1Type hπ3_dhi (Params.alpha_dhi_le_file) h
  · intro h
    rcases h with ⟨a, ha1, ha2, hlo, hhi⟩
    have hπ3_a : π / 3 < a := by
      linarith
    have ha2_file : a ≤ (1.20830549335659207180 : ℝ) :=
      le_trans ha2 Tammes15.Params.alpha_dhi_le_file
    exact w1Type_of_bounds hπ3_a ha2_file hlo hhi

theorem w1Type_iff_table :
    ∀ t q p : Fin 6, 3 ≤ t.val + q.val + p.val → t.val + q.val + p.val ≤ 5 →
      (W1Type t.val q.val p.val ↔
        (t.val, q.val, p.val) ∉ [(3, 0, 0), (2, 1, 0), (2, 0, 1), (1, 2, 0), (4, 0, 0), (3, 1, 0),
          (5, 0, 0)]) := by
  intro t q p ht3 ht5
  fin_cases t <;> fin_cases q <;> fin_cases p <;>
    simp at ht3 ht5 ⊢ <;>
    decide

theorem w1Graph_of_relSys {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k}
    (hR : RelSys P H A) (h1 : dlo ≤ A.d) (h2 : A.d ≤ dhi) : W1Graph P := by
  unfold W1Graph
  intro v
  have h0 : 0 < dlo := by
    have hpi : 0 < π := Real.pi_pos
    have hpi4 : 0 < π / 4 := by linarith
    linarith [pi_div_four_lt_dlo, hpi4]
  have hhi : dhi < π / 2 := by
    have hpi : 0 < π := Real.pi_pos
    have hpi3_lt_pi2 : π / 3 < π / 2 := by linarith
    linarith [dhi_lt_pi_div_three, hpi3_lt_pi2]
  have hd : 0 < A.d ∧ A.d < π / 2 := by
    constructor
    · linarith
    · linarith
  have hπ3 : π / 3 < alpha A.d := (alpha_bounds A.d hd).1
  have hle : alpha A.d ≤ (1.20830549335659207180 : ℝ) :=
    alpha_hi_of_end (lo := dlo) (hi := dhi) h0 hhi Params.alpha_dhi_le_file A.d h1 h2
  obtain ⟨hlo, hup⟩ := vertex_bounds hR hd v
  exact w1Type_of_bounds hπ3 hle hlo hup

theorem killedEntry_of_not_w1Graph {F : Set Frame} {P : PlaneGraph} (h : ¬ W1Graph P) :
    KilledEntry F P := by
  intro k _ H A h1 h2 hR
  exact absurd (w1Graph_of_relSys hR h1 h2) h

theorem killed_of_w1 {L : Set PlaneGraph} {F : Set Frame}
    (h : ∀ P ∈ L, W1Graph P → KilledEntry F P) : Killed L F := by
  refine killed_of_entries fun P hP => ?_
  by_cases hw : W1Graph P
  · exact h P hP hw
  · exact killedEntry_of_not_w1Graph hw

end Tammes15.D3lp
