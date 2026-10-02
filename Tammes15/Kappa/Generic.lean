import Tammes15.Kappa.Defs

/-!
# D1: the generic lemmas of the certificate

The generic statements of the certificate of D1, plus the sums of the integer
data (`sum_lamOf`, `sum_muOf`, `sum_abs_mkOf`) and `Cpert_mono`, `lamOf_nonneg`, `muOf_nonneg`.

`cert_of_check` turns the matrix bound at the rounded frame `q` into the certificate inequality on
`TPerp p` for the frame `p` (with `|p - q| ≤ δ` coordinatewise), and `kappa_of_cert` turns the
certificate inequality into `KappaBound`.
-/

open scoped RealInnerProductSpace

namespace Tammes15.Kappa

/-! ## 0. Sums over `Fin 46` and entries at the index `ix i m` -/

theorem sum_fin46 (f : Fin 46 → ℝ) : ∑ a, f a = f 0 + ∑ i : Fin 15, ∑ m : Fin 3, f (ix i m) := by
  have h_succ_eq : ∀ (i : Fin 15) (m : Fin 3), Fin.succ (finProdFinEquiv (i, m)) = ix i m := by
    intro i m
    apply Fin.ext
    simp [Fin.val_succ, ix]
    rw [finProdFinEquiv_apply_val]
    simp
    ring
  calc
    ∑ a : Fin 46, f a = f 0 + ∑ j : Fin 45, f (Fin.succ j) := by
      rw [Fin.sum_univ_succ]
    _ = f 0 + ∑ x : Fin 15 × Fin 3, f (Fin.succ (finProdFinEquiv x)) := by
      have h := (Equiv.sum_comp (finProdFinEquiv (m := 15) (n := 3)) (fun j : Fin 45 => f (Fin.succ j))).symm
      simpa using congrArg (fun s => f 0 + s) h
    _ = f 0 + ∑ i : Fin 15, ∑ m : Fin 3, f (Fin.succ (finProdFinEquiv (i, m))) := by
      rw [Fintype.sum_prod_type]
    _ = f 0 + ∑ i : Fin 15, ∑ m : Fin 3, f (ix i m) := by
      simp [h_succ_eq]

theorem zv_zero (w : ℝ) (t : Fin 15 → E3) : zv w t 0 = w := by
  simp [zv]

theorem zv_ix (w : ℝ) (t : Fin 15 → E3) (i : Fin 15) (m : Fin 3) : zv w t (ix i m) = t i m := by
  unfold zv ix
  simp
  have hdiv : (1 + 3 * (i : ℕ) + (m : ℕ) - 1) / 3 = (i : ℕ) := by omega
  have hmod : (1 + 3 * (i : ℕ) + (m : ℕ) - 1) % 3 = (m : ℕ) := by omega
  simp [hdiv, hmod]

theorem vr_zero (p : Fin 15 → E3) (e : Fin 15 × Fin 15) : vr p e 0 = 1 := by
  simp [vr]

theorem vr_ix (p : Fin 15 → E3) (e : Fin 15 × Fin 15) (i : Fin 15) (m : Fin 3) :
    vr p e (ix i m) = (if i = e.2 then -(p e.1 m) else 0) + (if i = e.1 then -(p e.2 m) else 0) := by
  dsimp [vr, ix]
  have hdiv : ((1 + 3 * i.val + m.val) - 1) / 3 = i.val := by omega
  have hmod : ((1 + 3 * i.val + m.val) - 1) % 3 = m.val := by omega
  simp
  simp [hdiv, hmod, Fin.ext_iff]

theorem gr_zero (p : Fin 15 → E3) (k : Fin 18) : gr p k 0 = 0 := by
  simp [gr]

theorem gr_ix_pt (p : Fin 15 → E3) (k i : Fin 15) (m : Fin 3) :
    gr p ⟨k.val, by omega⟩ (ix i m) = if i = k then p i m else 0 := by
  unfold gr ix
  have hk_lt : k.val < 15 := k.isLt
  have hmodk : k.val % 15 = k.val := Nat.mod_eq_of_lt hk_lt
  have hsub : (1 + 3 * i.val + m.val) - 1 = 3 * i.val + m.val := by omega
  have hdiv : (3 * i.val + m.val) / 3 = i.val := by omega
  have hmod : (3 * i.val + m.val) % 3 = m.val := by omega
  simp [hk_lt, hsub, hdiv, hmod, hmodk]
  by_cases hik : i = k
  · subst hik
    simp
  · have hval_ne : i.val ≠ k.val := by
      intro heq; apply hik; exact Fin.ext heq
    simp [hik, hval_ne]

theorem gr_ix_rot (p : Fin 15 → E3) (c : Fin 3) (i : Fin 15) (m : Fin 3) :
    gr p ⟨15 + c.val, by omega⟩ (ix i m) =
      if m = c + 2 then p i (c + 1) else if m = c + 1 then -(p i (c + 2)) else 0 := by
  have hindex : ∀ (i : Fin 15) (m : Fin 3), (⟨(1 + 3 * (i : ℕ) + (m : ℕ) - 1) / 3, by omega⟩ : Fin 15) = i := by
    intro i m
    ext; simp; omega
  have hmod : ∀ (i : Fin 15) (m : Fin 3), (1 + 3 * (i : ℕ) + (m : ℕ) - 1) % 3 = (m : ℕ) := by
    intro i m; omega
  unfold gr ix
  simp [hindex i m, hmod i m]
  by_cases h1 : m = c + 2
  · subst h1
    have hfin1 : (⟨((c : ℕ) + 1) % 3, by omega⟩ : Fin 3) = c + 1 := by
      ext; simp [Fin.val_add]
    have hcond1 : ((c + 2 : Fin 3) : ℕ) = ((c : ℕ) + 2) % 3 := by
      simp [Fin.val_add]
    have hcond2 : ((c + 2 : Fin 3) : ℕ) ≠ ((c : ℕ) + 1) % 3 := by
      simp [Fin.val_add]; omega
    simp [hcond1, hfin1]
  · by_cases h2 : m = c + 1
    · subst h2
      have hfin2 : (⟨((c : ℕ) + 2) % 3, by omega⟩ : Fin 3) = c + 2 := by
        ext; simp [Fin.val_add]
      have hcond1 : ((c + 1 : Fin 3) : ℕ) = ((c : ℕ) + 1) % 3 := by
        simp [Fin.val_add]
      have hcond2 : ((c + 1 : Fin 3) : ℕ) ≠ ((c : ℕ) + 2) % 3 := by
        simp [Fin.val_add]; omega
      simp [hcond1, hfin2]
      intro h_eq
      have h_contra : ((c + 1 : Fin 3) : ℕ) = ((c : ℕ) + 2) % 3 := by
        calc
          ((c + 1 : Fin 3) : ℕ) = ((c : ℕ) + 1) % 3 := hcond1
          _ = ((c : ℕ) + 2) % 3 := h_eq
      exact absurd h_contra hcond2
    · have h1' : (m : ℕ) ≠ ((c : ℕ) + 2) % 3 := by
        intro h
        apply h1
        ext
        simp [Fin.val_add, h]
      have h2' : (m : ℕ) ≠ ((c : ℕ) + 1) % 3 := by
        intro h
        apply h2
        ext
        simp [Fin.val_add, h]
      simp [h1, h2, h1', h2']

theorem inner_E3 (x y : E3) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem norm_sq_E3 (x : E3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  calc
    ‖x‖ ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
      simpa using EuclideanSpace.real_norm_sq_eq x
    _ = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
      simpa using Fin.sum_univ_three (fun i : Fin 3 => x i ^ 2)

theorem qOf_apply (P : List (List ℤ)) (i : Fin 15) (m : Fin 3) :
    qOf P i m = ((P.getD i []).getD m 0 : ℝ) / 2 ^ 100 := by
  simp [qOf]
  fin_cases m <;> rfl

theorem cross_apply_E3 (a b : E3) (c : Fin 3) :
    cross a b c = a (c + 1) * b (c + 2) - a (c + 2) * b (c + 1) := by
  unfold cross; simp [cross_apply]; fin_cases c <;> simp

/-! ## 1. Coordinates and quadratic forms -/

theorem sum_zv_sq (w : ℝ) (t : Fin 15 → E3) :
    ∑ a, zv w t a ^ 2 = w ^ 2 + ∑ i, ‖t i‖ ^ 2 := by
  rw [Fin.sum_univ_succ]
  have h0 : zv w t 0 = w := by
    unfold zv; simp
  rw [h0]
  rw [add_left_cancel_iff]
  -- Create an equivalence Fin 15 × Fin 3 ≃ Fin 45
  let e : Fin 15 × Fin 3 ≃ Fin 45 :=
    finProdFinEquiv.trans (finCongr (by norm_num : (15*3) = 45))
  -- Reindex the sum using the equivalence
  rw [← Equiv.sum_comp e (fun i : Fin 45 => (zv w t i.succ) ^ 2)]
  -- Now prove termwise equality
  have hterm : ∀ p : Fin 15 × Fin 3, (zv w t (e p).succ) ^ 2 = (t p.1 p.2) ^ 2 := by
    intro p
    have heval : (e p).val = p.2.val + 3 * p.1.val := by
      simp [e, finCongr, finProdFinEquiv]
    unfold zv
    simp [heval]
    have hm : p.2.val < 3 := p.2.isLt
    have hm' : (⟨p.2.val % 3, by
      have h := (e p).isLt
      rw [heval] at h
      omega⟩ : Fin 3) = p.2 := by
      ext; exact Nat.mod_eq_of_lt hm
    rw [hm']
    have hdiv : (p.2.val + 3 * p.1.val) / 3 = p.1.val := by
      omega
    have hk : (⟨(p.2.val + 3 * p.1.val) / 3, by
      have h := (e p).isLt
      rw [heval] at h
      omega⟩ : Fin 15) = p.1 := by
      ext; exact hdiv
    rw [hk]
  simp_rw [hterm]
  -- Rewrite RHS using EuclideanSpace.real_norm_sq_eq
  have hnorm : ∀ (x : E3), ‖x‖ ^ 2 = ∑ j : Fin 3, (x j) ^ 2 := by
    intro x; rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hnorm]
  rw [Fintype.sum_prod_type (f := fun (p : Fin 15 × Fin 3) => (t p.1 p.2) ^ 2)]

theorem quad_abs_le (N : Fin 46 → Fin 46 → ℝ) (z : Fin 46 → ℝ) :
    |quad N z| ≤ (∑ a, ∑ b, |N a b + N b a|) / 2 * ∑ a, z a ^ 2 := by
  set S := ∑ a : Fin 46, z a ^ 2 with hS
  have h_quad_eq : quad N z = (1/2 : ℝ) * (∑ a, ∑ b, (N a b + N b a) * z a * z b) := by
    have h_sum_symm : ∑ a, ∑ b, N b a * z a * z b = quad N z := by
      calc
        ∑ a, ∑ b, N b a * z a * z b = ∑ b, ∑ a, N b a * z a * z b := Finset.sum_comm
        _ = ∑ a, ∑ b, N a b * z b * z a := by rw [Finset.sum_comm]
        _ = ∑ a, ∑ b, N a b * (z b * z a) := by simp [mul_assoc]
        _ = ∑ a, ∑ b, N a b * (z a * z b) := by
          refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
          rw [mul_comm (z b) (z a)]
        _ = ∑ a, ∑ b, N a b * z a * z b := by
          refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
          ring
        _ = quad N z := rfl
    calc
      quad N z = (1/2 : ℝ) * (2 * quad N z) := by ring
      _ = (1/2 : ℝ) * ((∑ a, ∑ b, N a b * z a * z b) + quad N z) := by
        rw [two_mul]; simp [quad]
      _ = (1/2 : ℝ) * ((∑ a, ∑ b, N a b * z a * z b) + (∑ a, ∑ b, N b a * z a * z b)) := by rw [h_sum_symm]
      _ = (1/2 : ℝ) * (∑ a, (∑ b, N a b * z a * z b + ∑ b, N b a * z a * z b)) := by rw [Finset.sum_add_distrib]
      _ = (1/2 : ℝ) * (∑ a, ∑ b, (N a b * z a * z b + N b a * z a * z b)) := by
        refine congrArg (fun t => (1/2 : ℝ) * t) (Finset.sum_congr rfl (fun a ha => ?_))
        rw [Finset.sum_add_distrib]
      _ = (1/2 : ℝ) * (∑ a, ∑ b, ((N a b + N b a) * z a * z b)) := by
        refine congrArg (fun t => (1/2 : ℝ) * t) (Finset.sum_congr rfl (fun a ha => ?_))
        refine Finset.sum_congr rfl (fun b hb => ?_)
        ring
  have h_abs_mul_le_S (a b : Fin 46) : |z a * z b| ≤ S := by
    have h1 : |z a * z b| ≤ (z a ^ 2 + z b ^ 2) / 2 := by
      rw [abs_le]
      constructor
      · have h := two_mul_le_add_sq (-(z a)) (z b)
        linarith
      · have h := two_mul_le_add_sq (z a) (z b)
        linarith
    have h2 : (z a ^ 2 + z b ^ 2) / 2 ≤ S := by
      have hza : z a ^ 2 ≤ S :=
        Finset.single_le_sum (fun i hi => sq_nonneg (z i)) (Finset.mem_univ a)
      have hzb : z b ^ 2 ≤ S :=
        Finset.single_le_sum (fun i hi => sq_nonneg (z i)) (Finset.mem_univ b)
      linarith
    linarith
  calc
    |quad N z| = |(1/2 : ℝ) * (∑ a, ∑ b, (N a b + N b a) * z a * z b)| := by rw [h_quad_eq]
    _ = |(1/2 : ℝ)| * |∑ a, ∑ b, (N a b + N b a) * z a * z b| := by rw [abs_mul]
    _ = (1/2 : ℝ) * |∑ a, ∑ b, (N a b + N b a) * z a * z b| := by
      rw [abs_of_pos (by norm_num : 0 < (1/2 : ℝ))]
    _ ≤ (1/2 : ℝ) * ∑ a, |∑ b, (N a b + N b a) * z a * z b| := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : 0 ≤ (1/2 : ℝ))
      exact Finset.abs_sum_le_sum_abs (fun a => ∑ b, (N a b + N b a) * z a * z b) Finset.univ
    _ ≤ (1/2 : ℝ) * ∑ a, ∑ b, |(N a b + N b a) * z a * z b| := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : 0 ≤ (1/2 : ℝ))
      refine Finset.sum_le_sum (fun a ha => ?_)
      exact Finset.abs_sum_le_sum_abs (fun b => (N a b + N b a) * z a * z b) Finset.univ
    _ = (1/2 : ℝ) * ∑ a, ∑ b, (|N a b + N b a| * |z a * z b|) := by
      refine congrArg (fun t => (1/2 : ℝ) * t) (Finset.sum_congr rfl (fun a ha => ?_))
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [abs_mul, abs_mul, mul_assoc, ← abs_mul]
    _ ≤ (1/2 : ℝ) * ∑ a, ∑ b, (|N a b + N b a| * S) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : 0 ≤ (1/2 : ℝ))
      refine Finset.sum_le_sum (fun a ha => ?_)
      refine Finset.sum_le_sum (fun b hb => ?_)
      have h_nonneg_abs : 0 ≤ |N a b + N b a| := abs_nonneg _
      exact mul_le_mul_of_nonneg_left (h_abs_mul_le_S a b) h_nonneg_abs
    _ = (1/2 : ℝ) * ((∑ a, ∑ b, |N a b + N b a|) * S) := by
      simp [Finset.sum_mul]
    _ = (∑ a, ∑ b, |N a b + N b a|) / 2 * S := by ring

/-! ## 2. The certificate form -/

theorem vr_dot (p t : Fin 15 → E3) (w : ℝ) (e : Fin 15 × Fin 15) :
    ∑ a, vr p e a * zv w t a = w - Lmap p t e := by
  -- Expand Lmap into explicit coordinate sums
  have hLmap : Lmap p t e = (∑ m : Fin 3, p e.1 m * t e.2 m) + (∑ m : Fin 3, p e.2 m * t e.1 m) := by
    simp [Lmap, PiLp.inner_apply, Fin.sum_univ_three]; ring
  rw [hLmap]
  -- Split Fin 46 into a=0 and the remaining 45 elements
  rw [Fin.sum_univ_succ]
  -- Simplify the a=0 term: vr p e 0 = 1, zv w t 0 = w, so product = w
  have h0 : vr p e 0 * zv w t 0 = w := by
    simp [vr, zv]
  rw [h0]
  -- Goal: w + ∑ a : Fin 45, vr p e (Fin.succ a) * zv w t (Fin.succ a) = w - (∑ m, p e.1 m * t e.2 m + ∑ m, p e.2 m * t e.1 m)
  -- Subtract w from both sides: it suffices to show the sum equals the negative part
  have hgoal : ∑ a : Fin 45, vr p e (Fin.succ a) * zv w t (Fin.succ a) = -(∑ m : Fin 3, p e.1 m * t e.2 m + ∑ m : Fin 3, p e.2 m * t e.1 m) := by
    -- Reindex Fin 45 as Fin 15 × Fin 3 via finProdFinEquiv
    -- Use Finset.sum_equiv with all arguments explicit
    let e_equiv : Fin 45 ≃ Fin 15 × Fin 3 := (finProdFinEquiv (m := 15) (n := 3)).symm
    have hreindex := Finset.sum_equiv
      (e := e_equiv)
      (s := Finset.univ)
      (t := Finset.univ)
      (f := λ a : Fin 45 => vr p e (Fin.succ a) * zv w t (Fin.succ a))
      (g := λ (x : Fin 15 × Fin 3) => vr p e (Fin.succ (e_equiv.symm x)) * zv w t (Fin.succ (e_equiv.symm x)))
      (by simp)
      (by
        intro a ha
        dsimp [e_equiv]
        simp [Equiv.apply_symm_apply])
    rw [hreindex]
    -- Now goal: ∑ x : Fin 15 × Fin 3, vr p e (e_equiv.symm x).succ * zv w t (e_equiv.symm x).succ = ...
    -- Split into nested sums
    rw [Fintype.sum_prod_type]
    -- Now: ∑ k : Fin 15, ∑ m : Fin 3, vr p e (e_equiv.symm (k, m)).succ * zv w t (e_equiv.symm (k, m)).succ = ...
    -- Simplify e_equiv.symm (k, m) = finProdFinEquiv (k, m)
    have h_symm : e_equiv.symm = finProdFinEquiv (m := 15) (n := 3) := by
      simp [e_equiv]
    rw [h_symm]
    -- Now: ∑ k, ∑ m, vr p e (Fin.succ (finProdFinEquiv (k, m))) * zv w t (Fin.succ (finProdFinEquiv (k, m))) = ...
    -- Compute vr and zv for this index using the definitions
    -- For index a = Fin.succ (finProdFinEquiv (k, m)), we have a.val = k.val * 3 + m.val + 1
    -- So (a.val - 1) / 3 = k.val and (a.val - 1) % 3 = m.val
    have h_val : ∀ (k : Fin 15) (m : Fin 3), ((finProdFinEquiv (m := 15) (n := 3) (k, m)).val : ℕ) = k.val * 3 + m.val := by
      intro k m; simp [finProdFinEquiv]; omega
    have h_vr_zv : ∀ (k : Fin 15) (m : Fin 3),
        vr p e (Fin.succ (finProdFinEquiv (m := 15) (n := 3) (k, m))) * zv w t (Fin.succ (finProdFinEquiv (m := 15) (n := 3) (k, m))) =
        ((if k.val = e.2.val then -(p e.1 m) else 0) + (if k.val = e.1.val then -(p e.2 m) else 0)) * t k m := by
      intro k m
      set a := Fin.succ (finProdFinEquiv (m := 15) (n := 3) (k, m)) with ha
      have ha_val : (a.val : ℕ) = k.val * 3 + m.val + 1 := by
        dsimp [a]
        have h_fin : (finProdFinEquiv (m := 15) (n := 3) (k, m)).val = k.val * 3 + m.val := h_val k m
        simp [h_fin]
      have ha_val_ne_zero : a.val ≠ 0 := by
        rw [ha_val]
        omega
      have h_div : ((a.val : ℕ) - 1) / 3 = k.val := by
        rw [ha_val]
        omega
      have h_mod : ((a.val : ℕ) - 1) % 3 = m.val := by
        rw [ha_val]
        omega
      dsimp [vr, zv]
      rw [ite_eq_right ha_val_ne_zero]
      -- Now we need to replace (a.val - 1) / 3 with k.val and (a.val - 1) % 3 with m.val
      -- Use simp with the hypotheses to avoid dependent type issues
      have h_div' : ((a.val : ℕ) - 1) / 3 = (k.val : ℕ) := h_div
      have h_mod' : ((a.val : ℕ) - 1) % 3 = (m.val : ℕ) := h_mod
      simp [h_div', h_mod', ha_val_ne_zero]
    -- Now the sum simplifies using h_vr_zv
    simp_rw [h_vr_zv]
    -- Now goal: ∑ k, ∑ m, ((if k.val = e.2.val then -(p e.1 m) else 0) + (if k.val = e.1.val then -(p e.2 m) else 0)) * t k m = ...
    -- Split (A + B) * C into A*C + B*C
    simp_rw [add_mul]
    -- Split the nested sum: ∑ k, (∑ m, A k m + ∑ m, B k m) = (∑ k, ∑ m, A k m) + (∑ k, ∑ m, B k m)
    simp_rw [Finset.sum_add_distrib]
    -- Handle the first sum: ∑ k, ∑ m, (if k.val = e.2.val then -(p e.1 m) else 0) * t k m
    -- Only k = e.2 contributes
    have hsum1 : ∑ k : Fin 15, ∑ m : Fin 3, ((if k.val = e.2.val then -(p e.1 m) else 0) * t k m) = -∑ m : Fin 3, p e.1 m * t e.2 m := by
      have h_inner : ∀ (m : Fin 3), ∑ k : Fin 15, ((if k.val = e.2.val then -(p e.1 m) else 0) * t k m) = -(p e.1 m) * t e.2 m := by
        intro m
        calc
          ∑ k : Fin 15, ((if k.val = e.2.val then -(p e.1 m) else 0) * t k m)
              = ∑ k : Fin 15, (if k.val = e.2.val then -(p e.1 m) * t k m else 0) := by
                refine Finset.sum_congr rfl (λ k hk => ?_)
                by_cases h : k.val = e.2.val
                · simp [h]
                · simp [h]
          _ = ∑ k : Fin 15, (if k = e.2 then -(p e.1 m) * t k m else 0) := by
            refine Finset.sum_congr rfl (λ k hk => ?_)
            simp [Fin.ext_iff]
          _ = -(p e.1 m) * t e.2 m := by
            simp
      calc
        ∑ k : Fin 15, ∑ m : Fin 3, ((if k.val = e.2.val then -(p e.1 m) else 0) * t k m)
            = ∑ m : Fin 3, ∑ k : Fin 15, ((if k.val = e.2.val then -(p e.1 m) else 0) * t k m) := by rw [Finset.sum_comm]
        _ = ∑ m : Fin 3, (-(p e.1 m) * t e.2 m) := by
          simp_rw [h_inner]
        _ = -∑ m : Fin 3, p e.1 m * t e.2 m := by
          simp [Finset.sum_neg_distrib]
    -- Handle the second sum similarly
    have hsum2 : ∑ k : Fin 15, ∑ m : Fin 3, ((if k.val = e.1.val then -(p e.2 m) else 0) * t k m) = -∑ m : Fin 3, p e.2 m * t e.1 m := by
      have h_inner : ∀ (m : Fin 3), ∑ k : Fin 15, ((if k.val = e.1.val then -(p e.2 m) else 0) * t k m) = -(p e.2 m) * t e.1 m := by
        intro m
        calc
          ∑ k : Fin 15, ((if k.val = e.1.val then -(p e.2 m) else 0) * t k m)
              = ∑ k : Fin 15, (if k.val = e.1.val then -(p e.2 m) * t k m else 0) := by
                refine Finset.sum_congr rfl (λ k hk => ?_)
                by_cases h : k.val = e.1.val
                · simp [h]
                · simp [h]
          _ = ∑ k : Fin 15, (if k = e.1 then -(p e.2 m) * t k m else 0) := by
            refine Finset.sum_congr rfl (λ k hk => ?_)
            simp [Fin.ext_iff]
          _ = -(p e.2 m) * t e.1 m := by
            simp
      calc
        ∑ k : Fin 15, ∑ m : Fin 3, ((if k.val = e.1.val then -(p e.2 m) else 0) * t k m)
            = ∑ m : Fin 3, ∑ k : Fin 15, ((if k.val = e.1.val then -(p e.2 m) else 0) * t k m) := by rw [Finset.sum_comm]
        _ = ∑ m : Fin 3, (-(p e.2 m) * t e.1 m) := by
          simp_rw [h_inner]
        _ = -∑ m : Fin 3, p e.2 m * t e.1 m := by
          simp [Finset.sum_neg_distrib]
    rw [hsum1, hsum2]
    ring
  rw [hgoal]
  ring

theorem abs_apply_le_norm (x : E3) (m : Fin 3) : |x m| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  refine Real.abs_le_sqrt ?_
  have h := Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ m)
  simpa [Real.norm_eq_abs, sq_abs] using h

theorem sum_norm_le_four (t : Fin 15 → E3) :
    ∑ i, ‖t i‖ ≤ 4 * Real.sqrt (∑ i, ‖t i‖ ^ 2) := by
  have hT : 0 ≤ Real.sqrt (∑ i, ‖t i‖ ^ 2) := Real.sqrt_nonneg _
  have hT2 : Real.sqrt (∑ i, ‖t i‖ ^ 2) ^ 2 = ∑ i, ‖t i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 15 => ‖t i‖)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hcs
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  have h0 : 0 ≤ ∑ i, ‖t i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  rw [mul_pow, hT2]
  linarith

theorem gr_dot_pt (p t : Fin 15 → E3) (w : ℝ) (k : Fin 15) :
    ∑ a, gr p ⟨k.val, by omega⟩ a * zv w t a = ⟪p k, t k⟫ := by
  rw [sum_fin46, gr_zero, zero_mul, zero_add]
  simp_rw [gr_ix_pt, zv_ix, ite_mul, zero_mul]
  rw [Finset.sum_eq_single k (fun i _ hi => by simp [hi]) (by simp)]
  simp [inner_E3, Fin.sum_univ_three]

theorem gr_dot_rot (p t : Fin 15 → E3) (w : ℝ) (c : Fin 3) :
    ∑ a, gr p ⟨15 + c.val, by omega⟩ a * zv w t a = (∑ i, cross (p i) (t i)) c := by
  rw [sum_fin46, gr_zero, zero_mul, zero_add]
  simp_rw [gr_ix_rot, zv_ix]
  have h : (∑ i, cross (p i) (t i)) c = ∑ i, cross (p i) (t i) c := by simp
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cross_apply_E3, Fin.sum_univ_three]
  fin_cases c <;> simp <;> ring

theorem gr_dot_eq_zero (p t : Fin 15 → E3) (w : ℝ) (h : TPerp p t) (k : Fin 18) :
    ∑ a, gr p k a * zv w t a = 0 := by
  by_cases hk : k.val < 15
  · have hk' : k = ⟨(⟨k.val, hk⟩ : Fin 15).val, by omega⟩ := Fin.ext rfl
    rw [hk', gr_dot_pt]
    exact h.1 _
  · have hk' : k = ⟨15 + (⟨k.val - 15, by omega⟩ : Fin 3).val, by omega⟩ := Fin.ext (by simp; omega)
    rw [hk', gr_dot_rot, h.2]
    simp

theorem quad_sub (N1 N2 : Fin 46 → Fin 46 → ℝ) (z : Fin 46 → ℝ) :
    quad (fun a b => N1 a b - N2 a b) z = quad N1 z - quad N2 z := by
  unfold quad; simp only [sub_mul, Finset.sum_sub_distrib]

theorem quad_outer (u v z : Fin 46 → ℝ) :
    quad (fun a b => u a * v b) z = (∑ a, u a * z a) * ∑ b, v b * z b := by
  unfold quad
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem quad_sum {ι : Type*} [Fintype ι] (N : ι → Fin 46 → Fin 46 → ℝ) (z : Fin 46 → ℝ) :
    quad (fun a b => ∑ e, N e a b) z = ∑ e, quad (N e) z := by
  unfold quad
  simp only [Finset.sum_mul]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem quad_base (Rc2 w : ℝ) (t : Fin 15 → E3) :
    quad (fun a b => if a.val = 0 ∧ b.val = 0 then Rc2 else if a = b then -1 else 0) (zv w t) =
      Rc2 * w ^ 2 - ∑ i, ‖t i‖ ^ 2 := by
  have hrow : ∀ a : Fin 46, ∑ b, (if a.val = 0 ∧ b.val = 0 then Rc2 else if a = b then -1 else 0) *
      zv w t a * zv w t b = if a = 0 then Rc2 * w ^ 2 else -(zv w t a ^ 2) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [Finset.sum_eq_single 0]
      · simp [zv_zero]; ring
      · intro b _ hb
        have hb' : b.val ≠ 0 := fun h => hb (Fin.ext h)
        simp [hb', Ne.symm hb]
      · simp
    · have ha' : a.val ≠ 0 := fun h => ha (Fin.ext h)
      rw [Finset.sum_eq_single a]
      · simp [ha, ha']; ring
      · intro b _ hb
        simp [ha', Ne.symm hb]
      · simp
  simp only [quad]
  rw [Finset.sum_congr rfl fun a _ => hrow a, Fin.sum_univ_succ]
  simp only [Fin.succ_ne_zero, ↓reduceIte, Finset.sum_neg_distrib]
  have h := sum_zv_sq w t
  rw [Fin.sum_univ_succ, zv_zero] at h
  linarith

theorem sum_ind0_zv (w : ℝ) (t : Fin 15 → E3) :
    ∑ a : Fin 46, (if a.val = 0 then (1 : ℝ) else 0) * zv w t a = w := by
  rw [Fin.sum_univ_succ]
  simp [zv_zero]

theorem Fform_expand (p : Fin 15 → E3) (Sl : Fin 30 → Fin 15 × Fin 15) (lam : Fin 30 → ℝ)
    (mu : Fin 30 → Fin 30 → ℝ) (Rc2 : ℝ) (mk : Fin 18 → Fin 46 → ℝ) (w : ℝ) (t : Fin 15 → E3) :
    Fform p Sl lam mu Rc2 w t =
      ∑ k, (∑ a, gr p k a * zv w t a) * (∑ b, mk k b * zv w t b) +
        quad (Nr p Sl lam mu Rc2 mk) (zv w t) := by
  have hN : Nr p Sl lam mu Rc2 mk = fun a b =>
      (((if a.val = 0 ∧ b.val = 0 then Rc2 else if a = b then -1 else 0) -
        (if a.val = 0 then (1 : ℝ) else 0) * (∑ e, lam e * vr p (Sl e) b)) -
        ∑ e, ∑ f, mu e f * vr p (Sl e) a * vr p (Sl f) b) - ∑ k, gr p k a * mk k b := by
    funext a b
    simp only [Nr, ite_mul, one_mul, zero_mul]
  rw [hN, quad_sub, quad_sub, quad_sub, quad_base, quad_outer, sum_ind0_zv, quad_sum, quad_sum]
  simp only [quad_sum, quad_outer]
  have h2 : w * ∑ b, (∑ e, lam e * vr p (Sl e) b) * zv w t b =
      ∑ e, lam e * w * (w - Lmap p t (Sl e)) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← vr_dot p t w (Sl e), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have h3 : ∀ e f, (∑ a, mu e f * vr p (Sl e) a * zv w t a) * ∑ b, vr p (Sl f) b * zv w t b =
      mu e f * (w - Lmap p t (Sl e)) * (w - Lmap p t (Sl f)) := by
    intro e f
    have h : ∑ a, mu e f * vr p (Sl e) a * zv w t a = mu e f * ∑ a, vr p (Sl e) a * zv w t a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h, vr_dot, vr_dot]
  simp only [h3]
  rw [h2]
  unfold Fform
  ring

/-! ## 3. Perturbation from the rounded frame `q` to the frame `p` -/

theorem Cpert_mono (δ L M L' M' : ℝ) (hδ : 0 ≤ δ) (hL : L ≤ L') (hM : M ≤ M') :
    Cpert δ L M ≤ Cpert δ L' M' := by
  unfold Cpert
  have hc1 : 0 ≤ 2 * δ := by nlinarith
  have hc2 : 0 ≤ 4 * δ * (5 + 4 * δ) := by nlinarith
  have h1 : 2 * δ * L ≤ 2 * δ * L' := mul_le_mul_of_nonneg_left hL hc1
  have h2 : 4 * δ * (5 + 4 * δ) * M ≤ 4 * δ * (5 + 4 * δ) * M' := mul_le_mul_of_nonneg_left hM hc2
  exact add_le_add h1 h2

theorem norm_le_sqrt_sumsq (t : Fin 15 → E3) (j : Fin 15) :
    ‖t j‖ ≤ Real.sqrt (∑ i, ‖t i‖ ^ 2) := by
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  exact Finset.single_le_sum (f := fun i => ‖t i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)

theorem norm_sub_le_two_mul (x y : E3) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ m, |x m - y m| ≤ δ) :
    ‖x - y‖ ≤ 2 * δ := by
  have hm : ∀ m, ‖(x - y) m‖ ^ 2 ≤ δ ^ 2 := by
    intro m
    rw [PiLp.sub_apply, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h m) 2
  calc ‖x - y‖ = Real.sqrt (∑ m, ‖(x - y) m‖ ^ 2) := EuclideanSpace.norm_eq _
    _ ≤ Real.sqrt ((2 * δ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [Fin.sum_univ_three]
        nlinarith [hm 0, hm 1, hm 2, sq_nonneg δ]
    _ = 2 * δ := Real.sqrt_sq (by linarith)

theorem Lmap_abs_le_two (p t : Fin 15 → E3) (hp : ∀ i, ‖p i‖ = 1) (e : Fin 15 × Fin 15) :
    |Lmap p t e| ≤ 2 * Real.sqrt (∑ i, ‖t i‖ ^ 2) := by
  unfold Lmap
  have h1 := abs_real_inner_le_norm (p e.1) (t e.2)
  have h2 := abs_real_inner_le_norm (p e.2) (t e.1)
  rw [hp, one_mul] at h1 h2
  have h3 := norm_le_sqrt_sumsq t e.1
  have h4 := norm_le_sqrt_sumsq t e.2
  calc _ ≤ |⟪p e.1, t e.2⟫| + |⟪p e.2, t e.1⟫| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem Lmap_sub_abs_le (p q t : Fin 15 → E3) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpq : ∀ i m, |p i m - q i m| ≤ δ) (e : Fin 15 × Fin 15) :
    |Lmap p t e - Lmap q t e| ≤ 4 * δ * Real.sqrt (∑ i, ‖t i‖ ^ 2) := by
  have hd : Lmap p t e - Lmap q t e = ⟪p e.1 - q e.1, t e.2⟫ + ⟪p e.2 - q e.2, t e.1⟫ := by
    unfold Lmap; rw [inner_sub_left, inner_sub_left]; ring
  rw [hd]
  have n1 := norm_sub_le_two_mul (p e.1) (q e.1) δ hδ (hpq e.1)
  have n2 := norm_sub_le_two_mul (p e.2) (q e.2) δ hδ (hpq e.2)
  have h3 := norm_le_sqrt_sumsq t e.1
  have h4 := norm_le_sqrt_sumsq t e.2
  have i1 : |⟪p e.1 - q e.1, t e.2⟫| ≤ 2 * δ * Real.sqrt (∑ i, ‖t i‖ ^ 2) :=
    le_trans (abs_real_inner_le_norm _ _) (mul_le_mul n1 h4 (norm_nonneg _) (by positivity))
  have i2 : |⟪p e.2 - q e.2, t e.1⟫| ≤ 2 * δ * Real.sqrt (∑ i, ‖t i‖ ^ 2) :=
    le_trans (abs_real_inner_le_norm _ _) (mul_le_mul n2 h3 (norm_nonneg _) (by positivity))
  calc _ ≤ |⟪p e.1 - q e.1, t e.2⟫| + |⟪p e.2 - q e.2, t e.1⟫| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem pert_pt (w T δ ae af be bf : ℝ) (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hae : |ae| ≤ |w| + 2 * T)
    (haf : |af| ≤ |w| + 2 * T) (hde : |ae - be| ≤ 4 * δ * T) (hdf : |af - bf| ≤ 4 * δ * T) :
    |be * bf - ae * af| ≤ 4 * δ * (5 + 4 * δ) * (w ^ 2 + T ^ 2) := by
  have e1 : be * bf - ae * af = -(ae * (af - bf)) - (ae - be) * af + (ae - be) * (af - bf) := by ring
  rw [e1]
  have hw := abs_nonneg w
  have hA : |ae * (af - bf)| ≤ (|w| + 2 * T) * (4 * δ * T) := by
    rw [abs_mul]; exact mul_le_mul hae hdf (abs_nonneg _) (by positivity)
  have hB : |(ae - be) * af| ≤ (4 * δ * T) * (|w| + 2 * T) := by
    rw [abs_mul]; exact mul_le_mul hde haf (abs_nonneg _) (by positivity)
  have hC : |(ae - be) * (af - bf)| ≤ (4 * δ * T) * (4 * δ * T) := by
    rw [abs_mul]; exact mul_le_mul hde hdf (abs_nonneg _) (by positivity)
  have h1 : |-(ae * (af - bf)) - (ae - be) * af| ≤ |ae * (af - bf)| + |(ae - be) * af| := by
    calc _ ≤ |-(ae * (af - bf))| + |(ae - be) * af| := abs_sub _ _
      _ = _ := by rw [abs_neg]
  have h2 := abs_add_le (-(ae * (af - bf)) - (ae - be) * af) ((ae - be) * (af - bf))
  have hwT : 2 * |w| * T ≤ w ^ 2 + T ^ 2 := by nlinarith [sq_nonneg (|w| - T), sq_abs w]
  have k1 := mul_le_mul_of_nonneg_left hwT hδ
  have k2 : 0 ≤ δ * w ^ 2 := by positivity
  have k3 : 0 ≤ δ ^ 2 * w ^ 2 := by positivity
  nlinarith

theorem Fform_perturb (p q : Fin 15 → E3) (Sl : Fin 30 → Fin 15 × Fin 15) (lam : Fin 30 → ℝ)
    (mu : Fin 30 → Fin 30 → ℝ) (Rc2 δ : ℝ) (hlam : ∀ e, 0 ≤ lam e) (hmu : ∀ e f, 0 ≤ mu e f)
    (hδ : 0 ≤ δ) (hpq : ∀ i m, |p i m - q i m| ≤ δ) (hp : ∀ i, ‖p i‖ = 1) (w : ℝ)
    (t : Fin 15 → E3) :
    |Fform p Sl lam mu Rc2 w t - Fform q Sl lam mu Rc2 w t| ≤
      Cpert δ (∑ e, lam e) (∑ e, ∑ f, mu e f) * (w ^ 2 + ∑ i, ‖t i‖ ^ 2) := by
  have hT : 0 ≤ Real.sqrt (∑ i, ‖t i‖ ^ 2) := Real.sqrt_nonneg _
  have hT2 : Real.sqrt (∑ i, ‖t i‖ ^ 2) ^ 2 = ∑ i, ‖t i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  set T := Real.sqrt (∑ i, ‖t i‖ ^ 2) with hTdef
  obtain ⟨a, ha⟩ : ∃ a : Fin 30 → ℝ, ∀ e, a e = w - Lmap p t (Sl e) := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin 30 → ℝ, ∀ e, b e = w - Lmap q t (Sl e) := ⟨_, fun _ => rfl⟩
  have hs : ∀ e, |a e| ≤ |w| + 2 * T := fun e => by
    have := Lmap_abs_le_two p t hp (Sl e)
    rw [ha]
    calc |w - Lmap p t (Sl e)| ≤ |w| + |Lmap p t (Sl e)| := abs_sub _ _
      _ ≤ _ := by linarith
  have hd : ∀ e, |a e - b e| ≤ 4 * δ * T := fun e => by
    have := Lmap_sub_abs_le p q t δ hδ hpq (Sl e)
    rw [ha, hb, show w - Lmap p t (Sl e) - (w - Lmap q t (Sl e)) =
      -(Lmap p t (Sl e) - Lmap q t (Sl e)) by ring, abs_neg]
    exact this
  have hFp : Fform p Sl lam mu Rc2 w t = Rc2 * w ^ 2 - ∑ i, ‖t i‖ ^ 2 - ∑ e, lam e * w * a e -
      ∑ e, ∑ f, mu e f * a e * a f := by
    simp only [ha]; rfl
  have hFq : Fform q Sl lam mu Rc2 w t = Rc2 * w ^ 2 - ∑ i, ‖t i‖ ^ 2 - ∑ e, lam e * w * b e -
      ∑ e, ∑ f, mu e f * b e * b f := by
    simp only [hb]; rfl
  have key : Fform p Sl lam mu Rc2 w t - Fform q Sl lam mu Rc2 w t =
      (∑ e, (lam e * w * b e - lam e * w * a e)) +
        ∑ e, ∑ f, (mu e f * b e * b f - mu e f * a e * a f) := by
    rw [hFp, hFq]
    simp only [Finset.sum_sub_distrib]
    ring
  have hwT : 2 * |w| * T ≤ w ^ 2 + T ^ 2 := by nlinarith [sq_nonneg (|w| - T), sq_abs w]
  have hA : |∑ e, (lam e * w * b e - lam e * w * a e)| ≤
      2 * δ * (∑ e, lam e) * (w ^ 2 + T ^ 2) := by
    calc _ ≤ ∑ e, |lam e * w * b e - lam e * w * a e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e, lam e * (2 * δ * (w ^ 2 + T ^ 2)) := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [show lam e * w * b e - lam e * w * a e = lam e * (w * (b e - a e)) by ring, abs_mul,
            abs_of_nonneg (hlam e), abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (hlam e)
          have h := hd e
          rw [abs_sub_comm] at h
          calc |w| * |b e - a e| ≤ |w| * (4 * δ * T) := mul_le_mul_of_nonneg_left h (abs_nonneg w)
            _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hwT hδ]
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hM : |∑ e, ∑ f, (mu e f * b e * b f - mu e f * a e * a f)| ≤
      4 * δ * (5 + 4 * δ) * (∑ e, ∑ f, mu e f) * (w ^ 2 + T ^ 2) := by
    calc _ ≤ ∑ e, |∑ f, (mu e f * b e * b f - mu e f * a e * a f)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e, ∑ f, |mu e f * b e * b f - mu e f * a e * a f| :=
          Finset.sum_le_sum fun e _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e, ∑ f, mu e f * (4 * δ * (5 + 4 * δ) * (w ^ 2 + T ^ 2)) := by
          refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ => ?_
          rw [show mu e f * b e * b f - mu e f * a e * a f = mu e f * (b e * b f - a e * a f) by ring,
            abs_mul, abs_of_nonneg (hmu e f)]
          exact mul_le_mul_of_nonneg_left
            (pert_pt w T δ (a e) (a f) (b e) (b f) hδ hT (hs e) (hs f) (hd e) (hd f)) (hmu e f)
      _ = _ := by simp only [← Finset.sum_mul]; ring
  rw [key, ← hT2]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hA hM
    _ = _ := by unfold Cpert; ring

theorem gr_perturb (p q t : Fin 15 → E3) (δ w : ℝ) (hδ : 0 ≤ δ) (hpq : ∀ i m, |p i m - q i m| ≤ δ)
    (h : TPerp p t) (k : Fin 18) :
    |∑ a, gr q k a * zv w t a| ≤ 8 * δ * Real.sqrt (∑ i, ‖t i‖ ^ 2) := by
  have hT : 0 ≤ Real.sqrt (∑ i, ‖t i‖ ^ 2) := Real.sqrt_nonneg _
  by_cases hk : k.val < 15
  · have hk' : k = ⟨(⟨k.val, hk⟩ : Fin 15).val, by omega⟩ := Fin.ext rfl
    rw [hk', gr_dot_pt]
    set j : Fin 15 := ⟨k.val, hk⟩
    have e : ⟪q j, t j⟫ = ⟪q j - p j, t j⟫ := by rw [inner_sub_left, h.1 j, sub_zero]
    rw [e]
    have n1 := norm_sub_le_two_mul (q j) (p j) δ hδ (fun m => by rw [abs_sub_comm]; exact hpq j m)
    have n2 := norm_le_sqrt_sumsq t j
    calc _ ≤ ‖q j - p j‖ * ‖t j‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * δ) * Real.sqrt (∑ i, ‖t i‖ ^ 2) := mul_le_mul n1 n2 (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith
  · have hk' : k = ⟨15 + (⟨k.val - 15, by omega⟩ : Fin 3).val, by omega⟩ := Fin.ext (by simp; omega)
    rw [hk', gr_dot_rot]
    set c : Fin 3 := ⟨k.val - 15, by omega⟩
    have hs : ∀ r : Fin 15 → E3, (∑ i, cross (r i) (t i)) c =
        ∑ i, (r i (c + 1) * t i (c + 2) - r i (c + 2) * t i (c + 1)) := by
      intro r; simp [cross_apply_E3]
    have h0 : (∑ i, cross (p i) (t i)) c = 0 := by rw [h.2]; simp
    have e : (∑ i, cross (q i) (t i)) c = ∑ i, ((q i (c + 1) - p i (c + 1)) * t i (c + 2) -
        (q i (c + 2) - p i (c + 2)) * t i (c + 1)) := by
      rw [hs] at h0 ⊢
      rw [← sub_zero (∑ i, _), ← h0, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have hterm : ∀ i, |(q i (c + 1) - p i (c + 1)) * t i (c + 2) -
        (q i (c + 2) - p i (c + 2)) * t i (c + 1)| ≤ 2 * δ * ‖t i‖ := by
      intro i
      have d1 : |q i (c + 1) - p i (c + 1)| ≤ δ := by rw [abs_sub_comm]; exact hpq i _
      have d2 : |q i (c + 2) - p i (c + 2)| ≤ δ := by rw [abs_sub_comm]; exact hpq i _
      have a1 := abs_apply_le_norm (t i) (c + 2)
      have a2 := abs_apply_le_norm (t i) (c + 1)
      calc _ ≤ |(q i (c + 1) - p i (c + 1)) * t i (c + 2)| +
            |(q i (c + 2) - p i (c + 2)) * t i (c + 1)| := abs_sub _ _
        _ = |q i (c + 1) - p i (c + 1)| * |t i (c + 2)| +
            |q i (c + 2) - p i (c + 2)| * |t i (c + 1)| := by rw [abs_mul, abs_mul]
        _ ≤ δ * ‖t i‖ + δ * ‖t i‖ := add_le_add (mul_le_mul d1 a1 (abs_nonneg _) hδ)
            (mul_le_mul d2 a2 (abs_nonneg _) hδ)
        _ = _ := by ring
    calc _ ≤ ∑ i, |(q i (c + 1) - p i (c + 1)) * t i (c + 2) -
          (q i (c + 2) - p i (c + 2)) * t i (c + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, 2 * δ * ‖t i‖ := Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * δ * ∑ i, ‖t i‖ := by rw [Finset.mul_sum]
      _ ≤ 2 * δ * (4 * Real.sqrt (∑ i, ‖t i‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (sum_norm_le_four t) (by positivity)
      _ = _ := by ring

theorem mform_bound (mk : Fin 18 → Fin 46 → ℝ) (z : Fin 46 → ℝ) (k : Fin 18) :
    |∑ b, mk k b * z b| ≤ (∑ b, |mk k b|) * Real.sqrt (∑ a, z a ^ 2) := by
  calc
    |∑ b, mk k b * z b| ≤ ∑ b, |mk k b * z b| := Finset.abs_sum_le_sum_abs (fun b => mk k b * z b) Finset.univ
    _ = ∑ b, |mk k b| * |z b| := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [abs_mul]
    _ ≤ ∑ b, |mk k b| * Real.sqrt (∑ a, z a ^ 2) := by
      refine Finset.sum_le_sum fun b _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      apply Real.abs_le_sqrt
      have h : z b ^ 2 ≤ ∑ a : Fin 46, z a ^ 2 := by
        apply Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_univ b)
      simpa using h
    _ = (∑ b, |mk k b|) * Real.sqrt (∑ a, z a ^ 2) := by rw [Finset.sum_mul]

/-- The certificate inequality on `T'`, from the matrix bound at the rounded frame `q`. -/
theorem cert_of_check (p q : Fin 15 → E3) (Sl : Fin 30 → Fin 15 × Fin 15) (lam : Fin 30 → ℝ)
    (mu : Fin 30 → Fin 30 → ℝ) (Rc2 δ η0 : ℝ) (mk : Fin 18 → Fin 46 → ℝ)
    (hlam : ∀ e, 0 ≤ lam e) (hmu : ∀ e f, 0 ≤ mu e f) (hδ : 0 ≤ δ)
    (hpq : ∀ i m, |p i m - q i m| ≤ δ) (hp : ∀ i, ‖p i‖ = 1)
    (hN : (∑ a, ∑ b, |Nr q Sl lam mu Rc2 mk a b + Nr q Sl lam mu Rc2 mk b a|) / 2 ≤ η0) :
    ∀ w t, TPerp p t →
      -((η0 + Cpert δ (∑ e, lam e) (∑ e, ∑ f, mu e f) + 8 * δ * ∑ k, ∑ b, |mk k b|) *
        (w ^ 2 + ∑ i, ‖t i‖ ^ 2)) ≤ Fform p Sl lam mu Rc2 w t := by
  intro w t hT
  set z := zv w t with hz_def
  set Z := w ^ 2 + ∑ i, ‖t i‖ ^ 2 with hZ_def
  have hZsum : ∑ a : Fin 46, z a ^ 2 = Z := by
    rw [hz_def, hZ_def, Tammes15.Kappa.sum_zv_sq]
  have hZ_nonneg : 0 ≤ Z := by
    rw [hZ_def]
    positivity
  set T := Real.sqrt (∑ i : Fin 15, ‖t i‖ ^ 2) with hT_def
  have hT_nonneg : 0 ≤ T := Real.sqrt_nonneg _
  have hT_sq_eq : T ^ 2 = ∑ i : Fin 15, ‖t i‖ ^ 2 := by
    rw [hT_def]
    have hsum_nonneg : 0 ≤ ∑ i : Fin 15, ‖t i‖ ^ 2 := Finset.sum_nonneg (λ i _ => by positivity)
    rw [Real.sq_sqrt hsum_nonneg]
  have hT_sq_le_Z : T ^ 2 ≤ Z := by
    rw [hT_sq_eq, hZ_def]
    nlinarith
  have hT_le_sqrtZ : T ≤ Real.sqrt Z := by
    have h := Real.sqrt_le_sqrt hT_sq_le_Z
    rw [Real.sqrt_sq hT_nonneg] at h
    exact h
  -- From Fform_perturb: Fform p ≥ Fform q - Cpert * Z
  have hFp_ge_Fq : Fform p Sl lam mu Rc2 w t ≥ Fform q Sl lam mu Rc2 w t -
      Cpert δ (∑ e, lam e) (∑ e, ∑ f, mu e f) * Z := by
    have hFperturb := Tammes15.Kappa.Fform_perturb p q Sl lam mu Rc2 δ hlam hmu hδ hpq hp w t
    rw [← hZ_def] at hFperturb
    have h_abs := abs_le.mp hFperturb
    linarith
  -- From Fform_expand: Fform q = ∑_k (∑_a gr q k a * z a) * (∑_b mk k b * z b) + quad (Nr q ...) z
  have hFexpand := Tammes15.Kappa.Fform_expand q Sl lam mu Rc2 mk w t
  rw [← hz_def] at hFexpand
  -- From quad_abs_le and hN: quad (Nr q ...) z ≥ -η0 * Z
  have hQuad_lower : -η0 * Z ≤ quad (Nr q Sl lam mu Rc2 mk) z := by
    have hQuad_bound := Tammes15.Kappa.quad_abs_le (Nr q Sl lam mu Rc2 mk) z
    rw [hZsum] at hQuad_bound
    have h_abs := abs_le.mp hQuad_bound
    have h_bound : (∑ a : Fin 46, ∑ b : Fin 46, |Nr q Sl lam mu Rc2 mk a b + Nr q Sl lam mu Rc2 mk b a|) / 2 * Z ≤ η0 * Z := by
      nlinarith
    nlinarith
  -- For each k, bound the product term
  have hProd_bound (k : Fin 18) : -(8 * δ * (∑ b : Fin 46, |mk k b|) * Z) ≤
      (∑ a : Fin 46, gr q k a * z a) * (∑ b : Fin 46, mk k b * z b) := by
    have hGr := Tammes15.Kappa.gr_perturb p q t δ w hδ hpq hT k
    rw [← hz_def, ← hT_def] at hGr
    have hMk := Tammes15.Kappa.mform_bound mk z k
    rw [hZsum] at hMk
    have h_T_sqrtZ_le_Z : T * Real.sqrt Z ≤ Z := by
      calc
        T * Real.sqrt Z ≤ Real.sqrt Z * Real.sqrt Z :=
          mul_le_mul_of_nonneg_right hT_le_sqrtZ (Real.sqrt_nonneg _)
        _ = Z := Real.mul_self_sqrt hZ_nonneg
    have h_mul_bound : |(∑ a : Fin 46, gr q k a * z a) * (∑ b : Fin 46, mk k b * z b)| ≤
        8 * δ * (∑ b : Fin 46, |mk k b|) * Z := by
      calc
        |(∑ a : Fin 46, gr q k a * z a) * (∑ b : Fin 46, mk k b * z b)|
            = |∑ a : Fin 46, gr q k a * z a| * |∑ b : Fin 46, mk k b * z b| := abs_mul _ _
        _ ≤ (8 * δ * T) * ((∑ b : Fin 46, |mk k b|) * Real.sqrt Z) :=
          mul_le_mul hGr hMk (abs_nonneg _) (by positivity)
        _ = 8 * δ * (∑ b : Fin 46, |mk k b|) * (T * Real.sqrt Z) := by ring
        _ ≤ 8 * δ * (∑ b : Fin 46, |mk k b|) * Z :=
          mul_le_mul_of_nonneg_left h_T_sqrtZ_le_Z (by positivity)
    have h_abs := abs_le.mp h_mul_bound
    linarith
  -- Sum over k
  have hSumProd : -(8 * δ * ∑ k : Fin 18, (∑ b : Fin 46, |mk k b|) * Z) ≤
      ∑ k : Fin 18, (∑ a : Fin 46, gr q k a * z a) * (∑ b : Fin 46, mk k b * z b) := by
    calc
      -(8 * δ * ∑ k : Fin 18, (∑ b : Fin 46, |mk k b|) * Z)
          = ∑ k : Fin 18, -(8 * δ * (∑ b : Fin 46, |mk k b|) * Z) := by
        simp [Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ ≤ ∑ k : Fin 18, (∑ a : Fin 46, gr q k a * z a) * (∑ b : Fin 46, mk k b * z b) :=
        Finset.sum_le_sum (λ k hk => hProd_bound k)
  -- Combine: Fform q ≥ -(η0 + 8*δ*∑∑|mk|)*Z
  have hFq_lower : -(η0 + 8 * δ * ∑ k : Fin 18, ∑ b : Fin 46, |mk k b|) * Z ≤ Fform q Sl lam mu Rc2 w t := by
    rw [hFexpand]
    have hSumProd' : -(8 * δ * ∑ k : Fin 18, ∑ b : Fin 46, |mk k b|) * Z ≤
        ∑ k : Fin 18, (∑ a : Fin 46, gr q k a * z a) * (∑ b : Fin 46, mk k b * z b) := by
      simpa [Finset.sum_mul, Finset.mul_sum, mul_assoc] using hSumProd
    nlinarith
  -- Final: Fform p ≥ -(η0 + Cpert + 8*δ*∑∑|mk|)*Z
  have hFinal : -(η0 + Cpert δ (∑ e, lam e) (∑ e, ∑ f, mu e f) + 8 * δ * ∑ k, ∑ b, |mk k b|) * Z ≤
      Fform p Sl lam mu Rc2 w t := by
    linarith
  rw [hZ_def, ← neg_mul]
  exact hFinal

/-- `KappaBound` from the certificate inequality. -/
theorem kappa_of_cert (p : Fin 15 → E3) (S : Finset (Fin 15 × Fin 15))
    (Sl : Fin 30 → Fin 15 × Fin 15) (hS : ∀ e, Sl e ∈ S) (lam : Fin 30 → ℝ)
    (mu : Fin 30 → Fin 30 → ℝ) (Rc2 η κ0 : ℝ) (hlam : ∀ e, 0 ≤ lam e)
    (hmu : ∀ e f, 0 ≤ mu e f) (hκ : 0 < κ0) (hmargin : (Rc2 + η) * κ0 ^ 2 + η < 1)
    (hcert : ∀ w t, TPerp p t → -(η * (w ^ 2 + ∑ i, ‖t i‖ ^ 2)) ≤ Fform p Sl lam mu Rc2 w t) :
    KappaBound p S κ0 := by
  intro t ht
  by_contra h
  push_neg at h
  -- h: ∀ ij, ij ∈ S → κ0 * Real.sqrt (∑ i, ‖t i‖ ^ 2) > Lmap p t ij
  set T := Real.sqrt (∑ i, ‖t i‖ ^ 2) with hT_def
  have hT_nonneg : 0 ≤ T := Real.sqrt_nonneg _
  have hsum_nonneg : 0 ≤ ∑ i : Fin 15, ‖t i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => pow_two_nonneg _)
  have hT_sq : T ^ 2 = ∑ i : Fin 15, ‖t i‖ ^ 2 := Real.sq_sqrt hsum_nonneg
  set w := κ0 * T with hw_def
  have hw_nonneg : 0 ≤ w := mul_nonneg hκ.le hT_nonneg
  have hs_pos : ∀ e : Fin 30, 0 < w - Lmap p t (Sl e) := by
    intro e
    have hmem : Sl e ∈ S := hS e
    have hlt := h (Sl e) hmem
    linarith
  have hFform_le : Fform p Sl lam mu Rc2 w t ≤ Rc2 * w ^ 2 - (∑ i : Fin 15, ‖t i‖ ^ 2) := by
    dsimp [Fform]
    have hsum1 : 0 ≤ ∑ e : Fin 30, lam e * w * (w - Lmap p t (Sl e)) := by
      refine Finset.sum_nonneg (fun e _ => ?_)
      have hpos : 0 ≤ w - Lmap p t (Sl e) := by linarith [hs_pos e]
      have h_nonneg : 0 ≤ lam e * w := mul_nonneg (hlam e) hw_nonneg
      exact mul_nonneg h_nonneg hpos
    have hsum2 : 0 ≤ ∑ e : Fin 30, ∑ f : Fin 30, mu e f * (w - Lmap p t (Sl e)) * (w - Lmap p t (Sl f)) := by
      refine Finset.sum_nonneg (fun e _ => ?_)
      refine Finset.sum_nonneg (fun f _ => ?_)
      have hpos_e : 0 ≤ w - Lmap p t (Sl e) := by linarith [hs_pos e]
      have hpos_f : 0 ≤ w - Lmap p t (Sl f) := by linarith [hs_pos f]
      have h_nonneg_prod : 0 ≤ mu e f * (w - Lmap p t (Sl e)) := mul_nonneg (hmu e f) hpos_e
      exact mul_nonneg h_nonneg_prod hpos_f
    linarith
  have hFform_le' : Fform p Sl lam mu Rc2 w t ≤ Rc2 * κ0 ^ 2 * T ^ 2 - T ^ 2 := by
    calc
      Fform p Sl lam mu Rc2 w t ≤ Rc2 * w ^ 2 - (∑ i : Fin 15, ‖t i‖ ^ 2) := hFform_le
      _ = Rc2 * (κ0 * T) ^ 2 - T ^ 2 := by simp [hw_def, hT_sq]
      _ = Rc2 * κ0 ^ 2 * T ^ 2 - T ^ 2 := by ring
  have hcert_wt := hcert w t ht
  have hineq : -(η * (w ^ 2 + ∑ i : Fin 15, ‖t i‖ ^ 2)) ≤ Rc2 * κ0 ^ 2 * T ^ 2 - T ^ 2 := by
    linarith
  have hw_sq : w ^ 2 = κ0 ^ 2 * T ^ 2 := by
    simp [hw_def]
    ring
  have hsum_sq : ∑ i : Fin 15, ‖t i‖ ^ 2 = T ^ 2 := hT_sq.symm
  rw [hw_sq, hsum_sq] at hineq
  have hfactor_pos : 0 < 1 - (Rc2 + η) * κ0 ^ 2 - η := by
    linarith
  have hT_sq_nonpos : T ^ 2 ≤ 0 := by
    nlinarith
  have hT_sq_nonneg : 0 ≤ T ^ 2 := pow_two_nonneg _
  have hT_sq_zero : T ^ 2 = 0 := by
    linarith
  have hT_zero : T = 0 := by
    nlinarith
  have hw_zero : w = 0 := by
    simp [hw_def, hT_zero]
  have ht_zero : ∀ i, t i = 0 := by
    have hsum_zero : ∑ i : Fin 15, ‖t i‖ ^ 2 = 0 := by
      rw [← hT_sq, hT_sq_zero]
    have h_all_zero := Finset.sum_eq_zero_iff_of_nonneg (fun i hi => pow_two_nonneg _) |>.mp hsum_zero
    intro i
    have hi := h_all_zero i (Finset.mem_univ i)
    have hnorm_sq_zero : ‖t i‖ ^ 2 = 0 := hi
    have hnorm_zero : ‖t i‖ = 0 := by nlinarith
    exact norm_eq_zero.mp hnorm_zero
  have hLmap_zero : ∀ ij, Lmap p t ij = 0 := by
    intro ij
    dsimp [Lmap]
    simp [ht_zero]
  have hmem0 : Sl 0 ∈ S := hS 0
  have hlt0 : Lmap p t (Sl 0) < κ0 * T := h (Sl 0) hmem0
  rw [hLmap_zero (Sl 0), hT_zero] at hlt0
  simp at hlt0

/-! ## 4. The integer data as reals -/

theorem lamOf_nonneg (Lam : List Nat) (e : Fin 30) : 0 ≤ lamOf Lam e := by
  unfold lamOf; positivity

theorem muOf_nonneg (Mu : List (List Nat)) (e f : Fin 30) : 0 ≤ muOf Mu e f := by
  unfold muOf; positivity

theorem sum_lamOf (Lam : List Nat) (h : Lam.length = 30) :
    ∑ e, lamOf Lam e = ((Lam.sum : ℕ) : ℝ) / 2 ^ 64 := by
  have hLam : Lam = List.ofFn (fun (e : Fin 30) => Lam.getD e 0) := by
    apply List.ext_get
    · simp [h]
    · intro n hn₁ hn₂
      rw [List.get_ofFn]
      simpa using (List.getD_eq_get Lam 0 ⟨n, hn₁⟩).symm
  calc
    ∑ e : Fin 30, lamOf Lam e = ∑ e : Fin 30, ((Lam.getD e 0 : ℝ) / 2 ^ 64) := rfl
    _ = (∑ e : Fin 30, (Lam.getD e 0 : ℝ)) / 2 ^ 64 := by rw [Finset.sum_div]
    _ = ((List.ofFn (fun e : Fin 30 => Lam.getD e 0)).sum : ℝ) / 2 ^ 64 := by
      rw [← Nat.cast_sum, List.sum_ofFn]
    _ = ((Lam.sum : ℕ) : ℝ) / 2 ^ 64 := by rw [← hLam]

theorem list_sum_cast_eq (L : List ℕ) (n : ℕ) (h : L.length = n) :
    ((L.sum : ℕ) : ℝ) = ∑ j : Fin n, ((L.getD j 0 : ℕ) : ℝ) := by
  subst h
  have hL : List.ofFn (fun j : Fin L.length => L.getD j 0) = L := by
    apply List.ext_get
    · simp
    · intro k h1 h2
      rw [List.get_ofFn]
      simpa using (List.getD_eq_get L 0 ⟨k, h2⟩)
  rw [← Nat.cast_sum, ← List.sum_ofFn, hL]

theorem getD_map_natAbs (r : List ℤ) (b : ℕ) : (r.map Int.natAbs).getD b 0 = (r.getD b 0).natAbs := by
  cases h : r[b]? <;> simp [List.getD_eq_getElem?_getD, h]

theorem sum_muOf (Mu : List (List Nat)) (h : Mu.length = 30) (h' : ∀ r ∈ Mu, r.length = 30) :
    ∑ e, ∑ f, muOf Mu e f = (((Mu.map List.sum).sum : ℕ) : ℝ) / 2 ^ 64 := by
  have hrow : ∀ e : Fin 30, (Mu.getD e []).length = 30 := fun e => by
    apply h'
    rw [List.getD_eq_getElem _ _ (by rw [h]; exact e.isLt)]
    exact List.getElem_mem _
  have hMu : List.ofFn (fun e : Fin 30 => Mu.getD e []) = Mu := by
    apply List.ext_get
    · simp [h]
    · intro k h1 h2
      rw [List.get_ofFn]
      simpa using (List.getD_eq_get Mu [] ⟨k, h2⟩)
  conv_rhs => rw [← hMu, List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  simp only [muOf, ← Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Function.comp_apply, list_sum_cast_eq _ 30 (hrow e)]

theorem sum_abs_mkOf (Mk : List (List Int)) (h : Mk.length = 18) (h' : ∀ r ∈ Mk, r.length = 46) :
    ∑ k, ∑ b, |mkOf Mk k b| = (((Mk.map fun r => (r.map Int.natAbs).sum).sum : ℕ) : ℝ) / 2 ^ 64 := by
  have hrow : ∀ k : Fin 18, ((Mk.getD k []).map Int.natAbs).length = 46 := fun k => by
    rw [List.length_map]
    apply h'
    rw [List.getD_eq_getElem _ _ (by rw [h]; exact k.isLt)]
    exact List.getElem_mem _
  have hMk : List.ofFn (fun k : Fin 18 => Mk.getD k []) = Mk := by
    apply List.ext_get
    · simp [h]
    · intro k h1 h2
      rw [List.get_ofFn]
      simpa using (List.getD_eq_get Mk [] ⟨k, h2⟩)
  conv_rhs => rw [← hMk, List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  have habs : ∀ k b, |mkOf Mk k b| = (((Mk.getD k []).getD b 0).natAbs : ℝ) / 2 ^ 64 := by
    intro k b
    rw [mkOf, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64), Nat.cast_natAbs, Int.cast_abs]
  simp only [habs, ← Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Function.comp_apply, list_sum_cast_eq _ 46 (hrow k)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [getD_map_natAbs]

end Tammes15.Kappa
