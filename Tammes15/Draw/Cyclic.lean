import Mathlib

/-!
# Cyclic successors of finitely many angles

For finitely many distinct angles `φ a ∈ [0, 2π)`, the counterclockwise successor permutation:
each `a` goes to the `b ≠ a` with the least positive gap `toIcoMod 2π 0 (φ b - φ a)`. It is a
single cycle, and when there are at least two angles its gaps sum to `2π`. These are the
combinatorial facts behind the angular rotation system of a drawing and the angle sum at a
vertex (Section 4 of the paper).
-/

open Real

namespace Tammes15

theorem exists_equiv_fin_strictMono {α : Type*} [Fintype α] (φ : α → ℝ)
    (hφ : Function.Injective φ) :
    ∃ E : Fin (Fintype.card α) ≃ α, StrictMono (φ ∘ E) := by
  let S : Finset ℝ := Finset.univ.image φ
  have hcard : S.card = Fintype.card α := by
    simpa [S] using Finset.card_image_of_injective (Finset.univ : Finset α) hφ
  let f : Fin (Fintype.card α) ↪o ℝ := S.orderEmbOfFin hcard
  have hf_mem : ∀ i, f i ∈ S := fun i => Finset.orderEmbOfFin_mem S hcard i
  have hf_image : ∀ i, ∃ a, φ a = f i := by
    intro i
    rcases Finset.mem_image.mp (hf_mem i) with ⟨a, _, ha⟩
    exact ⟨a, ha⟩
  choose e he using hf_image
  have he_inj : Function.Injective e := by
    intro i j h
    have hφeq : φ (e i) = φ (e j) := by rw [h]
    rw [he i, he j] at hφeq
    exact f.injective hφeq
  have hbij : Function.Bijective e := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨he_inj, by simp⟩
  let E : Fin (Fintype.card α) ≃ α := Equiv.ofBijective e hbij
  refine ⟨E, ?_⟩
  have h_eq : φ ∘ E = f := by
    ext i
    simp [E, he i]
  rw [h_eq]
  exact f.strictMono

theorem finRotate_sameCycle (n : ℕ) (i j : Fin n) : (finRotate n).SameCycle i j := by
  by_cases hn : n = 0
  · subst hn
    exact Fin.elim0 i
  · have hpos : NeZero n := ⟨hn⟩
    set k := j - i with hk
    have h_eq : ((finRotate n) ^ (k.val : ℤ)) i = j := by
      calc
        ((finRotate n) ^ (k.val : ℤ)) i = ((finRotate n) ^ (k.val : ℕ)) i := by simp [zpow_natCast]
        _ = ((finRotate n)^[k.val]) i := rfl
        _ = (finCycle k) i := by
          simpa using congrArg (fun f : Fin n → Fin n => f i) (finCycle_eq_finRotate_iterate (k := k) (n := n)).symm
        _ = i + k := by simp [finCycle_apply]
        _ = i + (j - i) := rfl
        _ = j := by simp [add_sub_cancel]
    exact ⟨(k.val : ℤ), h_eq⟩

theorem toIcoMod_eq_self_of_nonneg_lt {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x < 2 * π) :
    toIcoMod two_pi_pos 0 x = x := by
  rw [toIcoMod_eq_self]
  have h : (0 : ℝ) + 2 * π = 2 * π := by simp
  rw [h]
  exact ⟨hx0, hx2⟩

theorem toIcoMod_eq_add_two_pi_of_nonpos_gt_neg {x : ℝ} (hx_low : -(2 * π) ≤ x) (hx_high : x < 0) :
    toIcoMod two_pi_pos 0 x = x + 2 * π := by
  rw [toIcoMod_eq_iff two_pi_pos]
  constructor
  · have hlow : 0 ≤ x + 2 * π := by linarith
    have hhigh : x + 2 * π < 2 * π := by linarith
    simpa [zero_add] using And.intro hlow hhigh
  · refine ⟨-1, ?_⟩
    ring

theorem finRotate_gap_le (n : ℕ) (f : Fin n → ℝ) (hf : StrictMono f)
    (hrange : ∀ i, 0 ≤ f i ∧ f i < 2 * π) (i j : Fin n) (hji : j ≠ i) :
    toIcoMod two_pi_pos 0 (f (finRotate n i) - f i) ≤ toIcoMod two_pi_pos 0 (f j - f i) := by
  have hnpos : 0 < n := by
    by_contra! h
    have : IsEmpty (Fin n) := by
      rw [Nat.eq_zero_of_le_zero h]
      exact inferInstance
    exact this.elim i
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  -- Now n = m + 1
  by_cases hi_last : i = Fin.last m
  · -- Case 1: i is the last element
    subst hi_last
    rw [finRotate_last]
    have hji_lt : j < Fin.last m := by
      by_contra! h
      have heq : j = Fin.last m := Fin.le_antisymm (Fin.le_last _) h
      exact hji heq
    have hf0_le_fj : f 0 ≤ f j := hf.monotone (Fin.zero_le _)
    have hfj_lt_fi : f j < f (Fin.last m) := hf hji_lt
    have hlow0 : -(2 * π) ≤ f 0 - f (Fin.last m) := by
      have h0 := hrange 0
      have hi := hrange (Fin.last m)
      linarith
    have hhigh0 : f 0 - f (Fin.last m) < 0 := by linarith
    have hlowj : -(2 * π) ≤ f j - f (Fin.last m) := by
      have hj := hrange j
      have hi := hrange (Fin.last m)
      linarith
    have hhighj : f j - f (Fin.last m) < 0 := by linarith
    rw [toIcoMod_eq_add_two_pi_of_nonpos_gt_neg hlow0 hhigh0,
      toIcoMod_eq_add_two_pi_of_nonpos_gt_neg hlowj hhighj]
    linarith
  · -- Case 2: i is not the last element
    have h_lt_last : i < Fin.last m := Fin.lt_last_iff_ne_last.mpr hi_last
    have h_fin_rotate : finRotate (m + 1) i = i + 1 := finRotate_apply i
    rw [h_fin_rotate]
    -- f i < f (i+1) since i < i+1
    have hi_lt_i1 : i < i + 1 := (Fin.lt_add_one_iff.mpr h_lt_last)
    have hfi_lt_fi1 : f i < f (i + 1) := hf hi_lt_i1
    have hgap_left_nonneg : 0 ≤ f (i + 1) - f i := by linarith
    have hgap_left_lt_two_pi : f (i + 1) - f i < 2 * π := by
      have hi1 := hrange (i + 1)
      have hi := hrange i
      linarith
    rw [toIcoMod_eq_self_of_nonneg_lt hgap_left_nonneg hgap_left_lt_two_pi]
    -- Now compare with the right gap
    by_cases hij : i < j
    · -- i < j: then f i < f j and i+1 ≤ j
      have hfi_lt_fj : f i < f j := hf hij
      have hgap_right_nonneg : 0 ≤ f j - f i := by linarith
      have hgap_right_lt_two_pi : f j - f i < 2 * π := by
        have hj := hrange j
        have hi := hrange i
        linarith
      rw [toIcoMod_eq_self_of_nonneg_lt hgap_right_nonneg hgap_right_lt_two_pi]
      -- Need: f(i+1) - f i ≤ f j - f i, i.e., f(i+1) ≤ f j
      have hi1_le_j : i + 1 ≤ j := by
        rw [Fin.le_iff_val_le_val]
        have hij_val : (i : ℕ) < (j : ℕ) := (Fin.lt_def.mp hij)
        have hval_i1 : (i + 1 : Fin (m + 1)).val = i.val + 1 := by
          simpa [hi_last] using Fin.val_add_one i
        rw [hval_i1]
        omega
      have hfi1_le_fj : f (i + 1) ≤ f j := hf.monotone hi1_le_j
      linarith
    · -- ¬ i < j, so j ≤ i; since j ≠ i, we have j < i
      have hji_le : j ≤ i := not_lt.mp hij
      have hji_lt : j < i := lt_of_le_of_ne hji_le hji
      have hfj_lt_fi : f j < f i := hf hji_lt
      have hgap_right_low : -(2 * π) ≤ f j - f i := by
        have hj := hrange j
        have hi := hrange i
        linarith
      have hgap_right_high : f j - f i < 0 := by linarith
      rw [toIcoMod_eq_add_two_pi_of_nonpos_gt_neg hgap_right_low hgap_right_high]
      -- Need: f(i+1) - f i ≤ f j - f i + 2π
      -- Simplify: f(i+1) ≤ f j + 2π
      -- Since f j ≥ 0 and f(i+1) < 2π, this holds
      have hfj_nonneg : 0 ≤ f j := (hrange j).1
      have hfi1_lt_two_pi : f (i + 1) < 2 * π := (hrange (i + 1)).2
      linarith

theorem exists_cyclic_succ {α : Type*} [Fintype α] [DecidableEq α] (φ : α → ℝ)
    (hφ : Function.Injective φ) (hrange : ∀ a, 0 ≤ φ a ∧ φ a < 2 * π) :
    ∃ σ : Equiv.Perm α, (∀ a b, σ.SameCycle a b) ∧
      ∀ a b, b ≠ a →
        toIcoMod two_pi_pos 0 (φ (σ a) - φ a) ≤ toIcoMod two_pi_pos 0 (φ b - φ a) := by
  obtain ⟨E, hE⟩ := Tammes15.exists_equiv_fin_strictMono φ hφ
  let n := Fintype.card α
  let σ := E.permCongr (finRotate n)
  have h_sameCycle : ∀ a b : α, σ.SameCycle a b := by
    intro a b
    have h := Tammes15.finRotate_sameCycle n (E.symm a) (E.symm b)
    rcases h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hzpow : (E.permCongr (finRotate n)) ^ k = E.permCongr ((finRotate n) ^ k) := by
      simpa using (map_zpow E.permCongrHom (finRotate n) k).symm
    calc
      (σ ^ k) a = ((E.permCongr (finRotate n)) ^ k) a := rfl
      _ = (E.permCongr ((finRotate n) ^ k)) a := by rw [hzpow]
      _ = E (((finRotate n) ^ k) (E.symm a)) := by rw [Equiv.permCongr_apply]
      _ = E (E.symm b) := by rw [hk]
      _ = b := by rw [Equiv.apply_symm_apply]
  have h_gap : ∀ a b : α, b ≠ a →
      toIcoMod two_pi_pos 0 (φ (σ a) - φ a) ≤ toIcoMod two_pi_pos 0 (φ b - φ a) := by
    intro a b h_ne
    have hji : E.symm b ≠ E.symm a := by
      intro h_eq
      apply h_ne
      exact E.symm.injective h_eq
    have h_range : ∀ i : Fin n, 0 ≤ (φ ∘ E) i ∧ (φ ∘ E) i < 2 * π := by
      intro i
      exact hrange (E i)
    have h := Tammes15.finRotate_gap_le n (φ ∘ E) hE h_range (E.symm a) (E.symm b) hji
    simpa [σ, Equiv.permCongr_apply, Function.comp] using h
  exact ⟨σ, h_sameCycle, h_gap⟩

theorem sum_cyclic_succ {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (φ : α → ℝ)
    (hφ : Function.Injective φ) (hrange : ∀ a, 0 ≤ φ a ∧ φ a < 2 * π) (σ : Equiv.Perm α)
    (hfix : ∀ a, σ a ≠ a)
    (hmin : ∀ a b, b ≠ a →
      toIcoMod two_pi_pos 0 (φ (σ a) - φ a) ≤ toIcoMod two_pi_pos 0 (φ b - φ a)) :
    ∑ a, toIcoMod two_pi_pos 0 (φ (σ a) - φ a) = 2 * π := by
  set g := fun (a : α) => toIcoMod two_pi_pos 0 (φ (σ a) - φ a) with hg
  have hsum_comp : ∑ a, φ (σ a) = ∑ a, φ a :=
    Equiv.sum_comp σ φ
  have hrange_low (a : α) : 0 ≤ φ a := (hrange a).1
  have hrange_high (a : α) : φ a < 2 * π := (hrange a).2
  have h_toIcoMod_lt (x y : α) (hlt : φ x < φ y) : toIcoMod two_pi_pos 0 (φ x - φ y) = φ x - φ y + 2 * π := by
    have hmem : (φ x - φ y + 2 * π) ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by
      have hlow : 0 ≤ φ x - φ y + 2 * π := by
        have hx_low := hrange_low x
        have hy_high := hrange_high y
        linarith
      have hhigh : φ x - φ y + 2 * π < 0 + 2 * π := by linarith
      exact ⟨hlow, hhigh⟩
    have hz : ∃ z : ℤ, (φ x - φ y) = (φ x - φ y + 2 * π) + z • (2 * π) := by
      use -1
      ring
    rw [toIcoMod_eq_iff two_pi_pos]
    exact ⟨hmem, hz⟩
  have h_toIcoMod_nonneg (x y : α) (hle : φ y ≤ φ x) : toIcoMod two_pi_pos 0 (φ x - φ y) = φ x - φ y := by
    have hmem : (φ x - φ y) ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by
      have hlow : 0 ≤ φ x - φ y := sub_nonneg.mpr hle
      have hhigh : φ x - φ y < 0 + 2 * π := by
        have hx_high := hrange_high x
        have hy_low := hrange_low y
        linarith
      exact ⟨hlow, hhigh⟩
    rw [toIcoMod_eq_self two_pi_pos]
    exact hmem
  have hg_cases (a : α) : g a = φ (σ a) - φ a + (if φ (σ a) < φ a then 2 * π else 0) := by
    by_cases hle : φ a ≤ φ (σ a)
    · have heq : g a = φ (σ a) - φ a := by
        rw [hg]
        exact h_toIcoMod_nonneg (σ a) a hle
      rw [heq]
      simp [hle]
    · have hlt : φ (σ a) < φ a := by linarith
      have heq : g a = φ (σ a) - φ a + 2 * π := by
        rw [hg]
        exact h_toIcoMod_lt (σ a) a hlt
      rw [heq]
      simp [hlt]
  let D : Finset α := Finset.filter (fun a => φ (σ a) < φ a) Finset.univ
  have hD_card_one : D.card = 1 := by
    have h_univ_nonempty : (Finset.univ : Finset α).Nonempty := by
      have : Nonempty α := inferInstance
      exact Finset.univ_nonempty
    obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image Finset.univ φ h_univ_nonempty
    have hm_D : m ∈ D := by
      have hne : σ m ≠ m := hfix m
      have hne_φ : φ (σ m) ≠ φ m := hφ.ne hne
      have hle : φ (σ m) ≤ φ m := hm_max (σ m) (Finset.mem_univ _)
      have hlt : φ (σ m) < φ m := by
        by_contra! hge
        exact hne_φ (le_antisymm hle hge)
      rw [Finset.mem_filter]
      exact ⟨hm_mem, hlt⟩
    have hD_sub_singleton : ∀ a ∈ D, a = m := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rcases ha with ⟨ha_mem, ha_lt⟩
      by_contra! hne
      have h_φa_le_φm : φ a ≤ φ m := hm_max a (Finset.mem_univ _)
      have h_cases : φ a < φ m ∨ φ a = φ m := lt_or_eq_of_le h_φa_le_φm
      rcases h_cases with (h_lt | h_eq)
      · have hmin' := hmin a m hne.symm
        have hLHS : toIcoMod two_pi_pos 0 (φ (σ a) - φ a) = φ (σ a) - φ a + 2 * π :=
          h_toIcoMod_lt (σ a) a ha_lt
        have hRHS : toIcoMod two_pi_pos 0 (φ m - φ a) = φ m - φ a :=
          h_toIcoMod_nonneg m a (by linarith)
        rw [hLHS, hRHS] at hmin'
        have hσ_low := hrange_low (σ a)
        have hm_high := hrange_high m
        linarith
      · exact hne (hφ h_eq)
    have hD_eq : D = {m} := by
      ext a
      constructor
      · intro ha
        rw [Finset.mem_singleton]
        exact hD_sub_singleton a ha
      · intro ha
        rw [Finset.mem_singleton] at ha
        rw [ha]
        exact hm_D
    rw [hD_eq]
    simp
  calc
    ∑ a, g a = ∑ a, (φ (σ a) - φ a + (if φ (σ a) < φ a then 2 * π else 0)) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hg_cases a]
    _ = (∑ a, (φ (σ a) - φ a)) + (∑ a, (if φ (σ a) < φ a then 2 * π else 0)) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a, φ (σ a) - ∑ a, φ a) + (∑ a, (if φ (σ a) < φ a then 2 * π else 0)) := by
      rw [Finset.sum_sub_distrib]
    _ = 0 + (∑ a, (if φ (σ a) < φ a then 2 * π else 0)) := by rw [hsum_comp, sub_self]
    _ = ∑ a, (if φ (σ a) < φ a then 2 * π else 0) := by simp
    _ = ∑ a ∈ D, 2 * π := by
      rw [← Finset.sum_filter]
    _ = (D.card : ℝ) * (2 * π) := by simp
    _ = (1 : ℝ) * (2 * π) := by
      rw [show (D.card : ℝ) = (1 : ℝ) from by exact_mod_cast hD_card_one]
    _ = 2 * π := by ring

end Tammes15
