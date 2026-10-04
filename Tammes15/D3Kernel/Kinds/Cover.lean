import Tammes15.D3Kernel.Kinds.CoverFarm
import Tammes15.D3Kernel.Kinds.LinSound

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Walk Real
open scoped Classical

theorem cover_spec {c : GCode} {R : List ℕ} (h : cover c R = true) :
    vertsOK c (nV c) = true ∧ nV c ≤ 15 ∧ (∀ p ∈ rootPairs R, rootOK c (15 - nV c) p.1 p.2 = true) ∧
      ∀ s ∈ List.sublistsLen (15 - nV c) (canonList c), ∃ p ∈ rootPairs R, repsOf c p.1 (15 - nV c) = s := by
  simp only [cover, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem vertsOK_spec {c : GCode} {n : ℕ} (h : vertsOK c n = true) :
    (∀ i < c.D, c.fstAt i < n) ∧ ∃ i < c.D, c.fstAt i + 1 = n := by
  simp only [vertsOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1, h.2⟩

theorem rootOK_spec {c : GCode} {k g box : ℕ} (h : rootOK c k g box = true) :
    Ctx.code g = c ∧ Ctx.k g = k ∧ (∀ m < k, Ctx.base g m < c.D) ∧ boxOK g box = true := by
  simp only [rootOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hD, hf⟩, hs⟩, hk⟩, hb⟩, hbox⟩ := h
  refine ⟨?_, hk, hb, hbox⟩
  cases c
  simp only [Ctx.code] at hD hf hs ⊢
  rw [hD, hf, hs]

theorem n_le_of_matches {P : PlaneGraph} {c : GCode} {lab : P.G.Dart ≃ Fin c.D} (hm : Matches P c lab)
    {n : ℕ} (h : ∃ i < c.D, c.fstAt i + 1 = n) : n ≤ P.n := by
  obtain ⟨i, hi, he⟩ := h
  have h1 := hm.fst (lab.symm ⟨i, hi⟩)
  simp only [Equiv.apply_symm_apply] at h1
  have h2 := (lab.symm ⟨i, hi⟩).fst.isLt
  omega

theorem not_relSys_of_lt {P : PlaneGraph} {c : GCode} {lab : P.G.Dart ≃ Fin c.D} (hm : Matches P c lab)
    {n : ℕ} (h : ∀ i < c.D, c.fstAt i < n) (hn : n < P.n) {k : ℕ} (H : HexChoice P k) (A : Assign P k) :
    ¬ RelSys P H A := by
  intro hR
  have hv := hR.vertex_sum ⟨n, hn⟩
  rw [Finset.sum_eq_zero (fun e he => ?_)] at hv
  · have := Real.pi_pos
    linarith
  exfalso
  have he' := (Finset.mem_filter.mp he).2
  have h1 := hm.fst e
  have h2 := h (lab e) (lab e).isLt
  rw [h1, he'] at h2
  exact lt_irrefl _ h2

section Box

variable {g : ℕ}

theorem sol_dFull (s : Sol g) : dloFull ≤ s.A.d ∧ s.A.d ≤ dhiFull := by
  have h := s.hd
  unfold dlo dhi at h
  unfold dloFull dhiFull
  exact h

theorem cALO_le_alpha (s : Sol g) : ((cALO : ℕ) : ℝ) / 2 ^ 62 ≤ alpha s.A.d := by
  have h := pFull_alpha_lo s.A.d (sol_dFull s).1 (sol_dFull s).2
  have e : (pFull.alo : ℝ) / (pFull.S : ℝ) = (118952772983819258225 : ℝ) / 100000000000000000000 := by
    norm_num [pFull]
  rw [e] at h
  have := cv_consts_pFull.1
  simp only [cALO]
  push_cast
  linarith

theorem alpha_le_cAHI (s : Sol g) : alpha s.A.d ≤ ((cAHI : ℕ) : ℝ) / 2 ^ 62 := by
  have h := pFull_alpha_hi s.A.d (sol_dFull s).1 (sol_dFull s).2
  have e : (pFull.ahi : ℝ) / (pFull.S : ℝ) = (120830549335659207180 : ℝ) / 100000000000000000000 := by
    norm_num [pFull]
  rw [e] at h
  have := cv_consts_pFull.2.1
  simp only [cAHI]
  push_cast
  linarith

theorem two_alpha_le_c2AHI (s : Sol g) : 2 * alpha s.A.d ≤ ((c2AHI : ℕ) : ℝ) / 2 ^ 62 := by
  have h := pFull_alpha_hi s.A.d (sol_dFull s).1 (sol_dFull s).2
  have e : (pFull.ahi : ℝ) / (pFull.S : ℝ) = (120830549335659207180 : ℝ) / 100000000000000000000 := by
    norm_num [pFull]
  rw [e] at h
  have := cv_consts_pFull.2.2.1
  simp only [c2AHI]
  push_cast
  linarith

theorem pi_le_cPI : π ≤ ((cPI : ℕ) : ℝ) / 2 ^ 62 := by
  have h := pi_le_pihi
  have e : ((314159265358979323847 : ℤ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) =
      (314159265358979323847 : ℝ) / 100000000000000000000 := by norm_num
  rw [e] at h
  have := cv_consts_pFull.2.2.2
  simp only [cPI]
  push_cast
  linarith

theorem cDLO_le_d (s : Sol g) : ((cDLO : ℕ) : ℝ) / 2 ^ 62 ≤ s.A.d := by
  have h := s.hd.1
  unfold dlo at h
  have := cv_consts_d.1
  simp only [cDLO]
  push_cast
  linarith

theorem d_le_cDHI (s : Sol g) : s.A.d ≤ ((cDHI : ℕ) : ℝ) / 2 ^ 62 := by
  have h := s.hd.2
  unfold dhi at h
  have := cv_consts_d.2.1
  simp only [cDHI]
  push_cast
  linarith

theorem three_d_le_c3DHI (s : Sol g) : 3 * s.A.d ≤ ((c3DHI : ℕ) : ℝ) / 2 ^ 62 := by
  have h := s.hd.2
  unfold dhi at h
  have := cv_consts_d.2.2
  simp only [c3DHI]
  push_cast
  linarith

theorem keyVal_le_of {k a : ℕ} (hk : kgood k = true) (h : kfix k ≤ a) :
    keyVal k ≤ (a : ℝ) / 2 ^ 62 := by
  rw [keyVal_kgood hk]
  have : (kfix k : ℝ) ≤ a := by exact_mod_cast h
  exact div_le_div_of_nonneg_right this (by positivity)

theorem le_keyVal_of {k a : ℕ} (hk : kgood k = true) (h : a ≤ kfix k) :
    (a : ℝ) / 2 ^ 62 ≤ keyVal k := by
  rw [keyVal_kgood hk]
  have : (a : ℝ) ≤ kfix k := by exact_mod_cast h
  exact div_le_div_of_nonneg_right this (by positivity)

theorem varOK_mem {box v : ℕ} (h : varOK g box v = true) (s : Sol g) :
    keyVal (bnd box (2 * v)) ≤ s.x v ∧ s.x v ≤ keyVal (bnd box (2 * v + 1)) := by
  unfold varOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hlo, hhi⟩, h⟩ := h
  unfold Sol.x Ctx.val
  by_cases h0 : Ctx.mean g v = 0
  · rw [ite_eq_left h0] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨(keyVal_le_of hlo h.1).trans (cALO_le_alpha s),
      (alpha_le_cAHI s).trans (le_keyVal_of hhi h.2)⟩
  rw [ite_eq_right h0] at h ⊢
  by_cases h1 : Ctx.mean g v = 1
  · rw [ite_eq_left h1] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨(keyVal_le_of hlo h.1).trans (cDLO_le_d s), (d_le_cDHI s).trans (le_keyVal_of hhi h.2)⟩
  rw [ite_eq_right h1] at h ⊢
  by_cases h2 : Ctx.mean g v < 258
  · rw [ite_eq_left h2] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hD, hl⟩, hu⟩ := h
    rw [dite_eq_left ⟨h2, hD⟩]
    have hc := s.hR.corner_mem (s.lab.symm ⟨Ctx.mean g v - 2, hD⟩)
    refine ⟨(keyVal_le_of hlo hl).trans ((cALO_le_alpha s).trans hc.1), ?_⟩
    rcases hu with hu | ⟨hper, hu⟩
    · exact (le_of_lt hc.2).trans (pi_le_cPI.trans (le_keyVal_of hhi hu))
    · obtain ⟨-, hr, -⟩ := rhombus_facts s hD hper
      exact hr.trans ((two_alpha_le_c2AHI s).trans (le_keyVal_of hhi hu))
  · rw [ite_eq_right h2] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hk, hl⟩, hu⟩ := h
    rw [dite_eq_right (fun hh => h2 hh.1), dite_eq_left hk]
    have hw := (s.hR.wheel ⟨(Ctx.mean g v - 258) / 6, hk⟩).1
      ⟨(Ctx.mean g v - 258) % 6, Nat.mod_lt _ (by norm_num)⟩
    exact ⟨(keyVal_le_of hlo hl).trans ((cDLO_le_d s).trans hw.1),
      hw.2.trans ((three_d_le_c3DHI s).trans (le_keyVal_of hhi hu))⟩

theorem boxMem_of_boxOK {box : ℕ} (h : boxOK g box = true) (s : Sol g) : BoxMem (Ctx.nv g) box s.x := by
  intro v hv
  simp only [boxOK, List.all_eq_true, List.mem_range] at h
  exact varOK_mem (h v hv) s

end Box

section Hex

variable {P : PlaneGraph} {c : GCode} {lab : P.G.Dart ≃ Fin c.D}

theorem face_lab (hm : Matches P c lab) (e : P.G.Dart) : c.faceAt (lab e) = lab (P.R.face e) := hm.face e

theorem canon_hrep (hm : Matches P c lab) (e : P.G.Dart) (he : Function.minimalPeriod P.R.face e = 6) :
    canon c (hrep c (lab e)) = true := by
  rw [canon_eq, hrep_eq]
  exact cv_canon_hrep P.R.face lab c.faceAt (face_lab hm) e he

theorem hrep_mem (hm : Matches P c lab) (e : P.G.Dart) :
    ∃ j < 6, hrep c (lab e) = ((lab ((P.R.face ^ j) e) : Fin c.D) : ℕ) := by
  rw [hrep_eq]
  exact cv_hrep_mem P.R.face lab c.faceAt (face_lab hm) e

theorem minimalPeriod_of_canon (hm : Matches P c lab) (e : P.G.Dart) (h : canon c (lab e) = true) :
    Function.minimalPeriod P.R.face e = 6 := by
  rw [canon_eq] at h
  exact cv_minimalPeriod_of_canon P.R.face lab c.faceAt (face_lab hm) e h

theorem eq_of_canon_sameCycle (hm : Matches P c lab) (e e' : P.G.Dart) (h : canon c (lab e) = true)
    (h' : canon c (lab e') = true) (hs : P.R.face.SameCycle e e') : e = e' := by
  rw [canon_eq] at h h'
  exact cv_eq_of_canon_sameCycle P.R.face lab c.faceAt (face_lab hm) e e' h h' hs

theorem sameCycle_pow (f : Equiv.Perm P.G.Dart) (e : P.G.Dart) (j : ℕ) : f.SameCycle e ((f ^ j) e) :=
  ⟨(j : ℤ), by simp⟩

theorem rep_facts (hm : Matches P c lab) (e : P.G.Dart) (he : Function.minimalPeriod P.R.face e = 6) :
    ∃ e₀ : P.G.Dart, (lab e₀ : ℕ) = hrep c (lab e) ∧ canon c (lab e₀) = true ∧ P.R.face.SameCycle e e₀ := by
  obtain ⟨j, -, hj⟩ := hrep_mem hm e
  refine ⟨(P.R.face ^ j) e, hj.symm, ?_, sameCycle_pow _ e j⟩
  rw [← hj]
  exact canon_hrep hm e he

theorem hrep_eq_iff (hm : Matches P c lab) (e e' : P.G.Dart) (he : Function.minimalPeriod P.R.face e = 6)
    (he' : Function.minimalPeriod P.R.face e' = 6) :
    hrep c (lab e) = hrep c (lab e') ↔ P.R.face.SameCycle e e' := by
  obtain ⟨e₀, h0, hc0, hs0⟩ := rep_facts hm e he
  obtain ⟨e₁, h1, hc1, hs1⟩ := rep_facts hm e' he'
  constructor
  · intro h
    have : e₀ = e₁ := by
      apply lab.injective
      apply Fin.val_injective
      rw [h0, h1, h]
    subst this
    exact hs0.trans hs1.symm
  · intro h
    have : e₀ = e₁ := eq_of_canon_sameCycle hm e₀ e₁ hc0 hc1 ((hs0.symm.trans h).trans hs1)
    rw [← h0, ← h1, this]

end Hex

theorem cover_sound : CoverSound cover := by
  intro c R hc hR
  obtain ⟨hv, -, hroots, hsub⟩ := cover_spec hc
  obtain ⟨hlt, hex⟩ := vertsOK_spec hv
  apply killedCode_of_casesKilled
  intro P lab hm k hk H
  have hnle := n_le_of_matches hm hex
  by_cases hPn : P.n = nV c
  swap
  · refine ⟨H, ⟨Equiv.refl _, fun m => Equiv.Perm.SameCycle.refl _ _⟩,
      fun d _ _ => ⟨d, d, le_rfl, le_rfl, ?_⟩⟩
    intro A _ _ _ _ hR'
    exact absurd hR' (not_relSys_of_lt hm hlt (lt_of_le_of_ne hnle (Ne.symm hPn)) H A)
  have hk' : k = 15 - nV c := by omega

  set r : Fin k → ℕ := fun m => hrep c (lab (H.base m)) with hr
  have hr_inj : Function.Injective r := by
    intro m m' h
    exact H.distinct m m' ((hrep_eq_iff hm _ _ (H.hex m) (H.hex m')).mp h)
  have hr_canon : ∀ m, canon c (r m) = true := fun m => canon_hrep hm (H.base m) (H.hex m)
  set S : Finset ℕ := Finset.univ.image r with hS
  have hScard : S.card = k := by
    rw [hS, Finset.card_image_of_injective _ hr_inj, Finset.card_univ, Fintype.card_fin]
  have hmem : S.sort (· ≤ ·) ∈ List.sublistsLen (15 - nV c) (canonList c) := by
    rw [← hk', ← hScard, canonList_eq]
    refine cv_sort_mem_sublistsLen _ (cv_canonList_spec _ _).1 S fun x hx => ?_
    rw [(cv_canonList_spec _ _).2, ← canon_eq]
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hx
    exact hr_canon m
  obtain ⟨⟨g, box⟩, hp, hreps⟩ := hsub _ hmem
  obtain ⟨hcode, hkg, hbase, hbox⟩ := rootOK_spec (hroots _ hp)
  simp only at hcode hkg hbase hbox hreps
  rw [← hk'] at hkg hreps hbase

  have hrep_root : ∀ m (hm' : m < k), ∃ m' : Fin k, r m' = hrep c (Ctx.base g m) := by
    intro m hm'
    have : hrep c (Ctx.base g m) ∈ S.sort (· ≤ ·) := by
      rw [← hreps]
      exact List.mem_map.mpr ⟨m, List.mem_range.mpr hm', rfl⟩
    rw [Finset.mem_sort, hS] at this
    obtain ⟨m', -, h⟩ := Finset.mem_image.mp this
    exact ⟨m', h⟩
  have hnodup : ((List.range k).map (fun m => hrep c (Ctx.base g m))).Nodup := by
    have := Finset.sort_nodup S (· ≤ ·)
    rw [← hreps] at this
    exact this
  subst hcode
  subst hkg

  let b : Fin (Ctx.k g) → P.G.Dart := fun m => lab.symm ⟨Ctx.base g m, hbase m m.isLt⟩
  have hb : ∀ m, ((lab (b m) : Fin (Ctx.D g)) : ℕ) = Ctx.base g m := fun m => by simp [b]
  have hb_hex : ∀ m, Function.minimalPeriod P.R.face (b m) = 6 := by
    intro m
    obtain ⟨m', hm'⟩ := hrep_root m m.isLt
    obtain ⟨j, -, hj⟩ := hrep_mem hm (b m)
    have hc : canon (Ctx.code g) (lab ((P.R.face ^ j) (b m))) = true := by
      rw [← hj, hb, ← hm']
      exact hr_canon m'
    have := minimalPeriod_of_canon hm _ hc
    rwa [← Equiv.Perm.iterate_eq_pow, Function.minimalPeriod_apply_iterate
      (Function.Injective.mem_periodicPts (Equiv.injective _) _)] at this
  let H₀ : HexChoice P (Ctx.k g) :=
    { base := b
      hex := hb_hex
      distinct := by
        intro m m' hs
        have h := (hrep_eq_iff hm _ _ (hb_hex m) (hb_hex m')).mpr hs
        rw [hb, hb] at h
        exact Fin.ext (cv_inj_of_nodup _ _ hnodup m m' m.isLt m'.isLt h) }

  obtain ⟨σ, hσ⟩ := cv_perm_of_mem r hr_inj (fun m => hrep (Ctx.code g) (lab (H₀.base m))) (by
    intro m
    have : r m ∈ S.sort (· ≤ ·) := by
      rw [Finset.mem_sort, hS]
      exact Finset.mem_image_of_mem r (Finset.mem_univ m)
    rw [← hreps] at this
    obtain ⟨m', hm', h⟩ := List.mem_map.mp this
    exact ⟨⟨m', List.mem_range.mp hm'⟩, by rw [← h]; simp [H₀, hb]⟩)
  refine ⟨H₀, ⟨σ, fun m => ?_⟩, fun d hd1 hd2 => ⟨dlo, dhi, hd1, hd2, ?_⟩⟩
  · exact (hrep_eq_iff hm _ _ (H.hex m) (hb_hex (σ m))).mp (hσ m).symm
  · intro A h1 h2 _ _ hRel
    let s : Sol g := ⟨P, lab, hm, H₀, fun m => hb m, A, ⟨h1, h2⟩, hRel⟩
    exact hR (g, box) hp s (boxMem_of_boxOK hbox s)

end Tammes15.D3Kernel.Kinds
