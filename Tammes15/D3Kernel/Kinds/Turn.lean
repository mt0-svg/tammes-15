import Tammes15.D3Kernel.Kinds.GlueCode

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Tammes15.PaperSteps
open scoped Classical

def cvarB (c : GCode) (n i : ℕ) : ℕ :=
  if c.period i = 3 then 256
  else if c.period i = 4 then
    (if c.fstAt i * n + c.fstAt (c.faceAt i) ≤
        c.fstAt (c.faceIter i 2) * n + c.fstAt (c.faceAt (c.faceIter i 2)) then i else c.faceIter i 2)
  else i

theorem dartKey_code {P : PlaneGraph} {c : GCode} {lab : P.G.Dart ≃ Fin c.D} (hm : Matches P c lab)
    (e : P.G.Dart) : c.fstAt (lab e) * P.n + c.fstAt (c.faceAt (lab e)) = dartKey e := by
  rw [hm.face, hm.fst, hm.fst, face_fst']
  rfl

theorem rsymC_iter_sol {g : ℕ} (s : Sol g) (a : s.P.G.Dart) (t : ℕ) :
    (rsymC (Ctx.code g))^[t] (s.lab a : ℕ) = s.lab ((s.P.R.rot.symm ^ t) a) := rsymC_iter s.hm a t

theorem vmOf_cvar {g hv : ℕ} (s : Sol g) (e : s.P.G.Dart) (hper : 0 < (Ctx.code g).period (s.lab e)) :
    vmOf s hv (cvar e) = hvB hv (cvarB (Ctx.code g) s.P.n (s.lab e)) := by
  have hf : fsize s.P e = (Ctx.code g).period (s.lab e) := fsize_of_period s.hm e rfl hper
  have h2 : (Ctx.code g).faceIter (s.lab e) 2 = s.lab ((s.P.R.face ^ 2) e) := faceIter_lab s.hm e 2
  have hk1 : (Ctx.code g).fstAt (s.lab e) * s.P.n + (Ctx.code g).fstAt ((Ctx.code g).faceAt (s.lab e)) =
      dartKey e := dartKey_code s.hm e
  have hk2 : (Ctx.code g).fstAt (s.lab ((s.P.R.face ^ 2) e)) * s.P.n +
      (Ctx.code g).fstAt ((Ctx.code g).faceAt (s.lab ((s.P.R.face ^ 2) e))) = dartKey ((s.P.R.face ^ 2) e) :=
    dartKey_code s.hm _
  have hk : ((Ctx.code g).fstAt (s.lab e) * s.P.n + (Ctx.code g).fstAt ((Ctx.code g).faceAt (s.lab e)) ≤
      (Ctx.code g).fstAt ((Ctx.code g).faceIter (s.lab e) 2) * s.P.n +
        (Ctx.code g).fstAt ((Ctx.code g).faceAt ((Ctx.code g).faceIter (s.lab e) 2))) ↔
      dartKey e ≤ dartKey ((s.P.R.face ^ 2) e) := by
    rw [h2, hk1, hk2]
  unfold cvar cvarB
  rw [hf]
  by_cases h3 : (Ctx.code g).period (s.lab e) = 3
  · rw [ite_eq_left h3, ite_eq_left h3]
    rfl
  · rw [ite_eq_right h3, ite_eq_right h3]
    by_cases h4 : (Ctx.code g).period (s.lab e) = 4
    · rw [ite_eq_left h4, ite_eq_left h4]
      by_cases hd : dartKey e ≤ dartKey ((s.P.R.face ^ 2) e)
      · rw [ite_eq_left hd, ite_eq_left (hk.2 hd)]
        rfl
      · rw [ite_eq_right hd, ite_eq_right (fun h => hd (hk.1 h)), h2]
        rfl
    · rw [ite_eq_right h4, ite_eq_right h4]
      rfl

def sumLo (box hv : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => sumLo box hv f t + kfix (bnd box (2 * hvB hv (f t)))

def sumHi (box hv : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => sumHi box hv f t + kfix (bnd box (2 * hvB hv (f t) + 1))

def goodAll (box hv : ℕ) (f : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | t + 1 => goodAll box hv f t && kgood (bnd box (2 * hvB hv (f t))) && kgood (bnd box (2 * hvB hv (f t) + 1))

theorem goodAll_spec {box hv : ℕ} {f : ℕ → ℕ} : ∀ {n : ℕ}, goodAll box hv f n = true → ∀ t < n,
    kgood (bnd box (2 * hvB hv (f t))) = true ∧ kgood (bnd box (2 * hvB hv (f t) + 1)) = true := by
  intro n
  induction n with
  | zero => intro _ t ht; omega
  | succ n ih =>
    intro h t ht
    simp only [goodAll, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact ih h.1.1 t ht
    · exact ⟨h.1.2, h.2⟩

theorem sumLo_eq {box hv : ℕ} {f : ℕ → ℕ} : ∀ {n : ℕ},
    (∀ t < n, kgood (bnd box (2 * hvB hv (f t))) = true) →
      (sumLo box hv f n : ℝ) / 2 ^ 62 = ∑ t ∈ Finset.range n, keyVal (bnd box (2 * hvB hv (f t))) := by
  intro n
  induction n with
  | zero => intro _; simp [sumLo]
  | succ n ih =>
    intro h
    rw [Finset.sum_range_succ, ← ih (fun t ht => h t (by omega)), keyVal_kgood (h n (by omega)), sumLo]
    push_cast
    ring

theorem sumHi_eq {box hv : ℕ} {f : ℕ → ℕ} : ∀ {n : ℕ},
    (∀ t < n, kgood (bnd box (2 * hvB hv (f t) + 1)) = true) →
      (sumHi box hv f n : ℝ) / 2 ^ 62 = ∑ t ∈ Finset.range n, keyVal (bnd box (2 * hvB hv (f t) + 1)) := by
  intro n
  induction n with
  | zero => intro _; simp [sumHi]
  | succ n ih =>
    intro h
    rw [Finset.sum_range_succ, ← ih (fun t ht => h t (by omega)), keyVal_kgood (h n (by omega)), sumHi]
    push_cast
    ring

def tf (c : GCode) (n i t : ℕ) : ℕ := cvarB c n ((rsymC c)^[t + 1] i)

theorem turnStepsR_le_rotDeg (P : PlaneGraph) (a b : P.G.Dart) : turnStepsR P.R a b ≤ rotDeg a := by
  unfold turnStepsR rotDeg
  set f := P.R.rot.symm
  have hper : a ∈ Function.periodicPts f := Function.Injective.mem_periodicPts f.injective a
  have hpos : 0 < Function.minimalPeriod f a := Function.minimalPeriod_pos_of_mem_periodicPts hper
  by_cases h : ∃ s, (f ^ s) a = b
  · rw [dite_eq_left h]
    have hmod : (f ^ (Nat.find h % Function.minimalPeriod f a)) a = b := by
      rw [Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq, ← Equiv.Perm.coe_pow]
      exact Nat.find_spec h
    have := Nat.find_min' h hmod
    have := Nat.mod_lt (Nat.find h) hpos
    omega
  · rw [dite_eq_right h]
    exact Nat.zero_le _

theorem walkBox_lo_cvar {g hv box : ℕ} (s : Sol g) (hper : ∀ i < Ctx.D g, 0 < (Ctx.code g).period i)
    (a : s.P.G.Dart) (t : ℕ) :
    (walkBox box (vmOf s hv)).lo (cvar ((s.P.R.rot.symm ^ (t + 1)) a)) =
      keyVal (bnd box (2 * hvB hv (tf (Ctx.code g) s.P.n (s.lab a) t))) := by
  show keyVal (bnd box (2 * vmOf s hv (cvar ((s.P.R.rot.symm ^ (t + 1)) a)))) = _
  rw [vmOf_cvar s _ (hper _ (s.lab _).isLt), tf, rsymC_iter_sol s]

theorem walkBox_hi_cvar {g hv box : ℕ} (s : Sol g) (hper : ∀ i < Ctx.D g, 0 < (Ctx.code g).period i)
    (a : s.P.G.Dart) (t : ℕ) :
    (walkBox box (vmOf s hv)).hi (cvar ((s.P.R.rot.symm ^ (t + 1)) a)) =
      keyVal (bnd box (2 * hvB hv (tf (Ctx.code g) s.P.n (s.lab a) t) + 1)) := by
  show keyVal (bnd box (2 * vmOf s hv (cvar ((s.P.R.rot.symm ^ (t + 1)) a)) + 1)) = _
  rw [vmOf_cvar s _ (hper _ (s.lab _).isLt), tf, rsymC_iter_sol s]

def turnLoZ (box hv : ℕ) (c : GCode) (n i j : ℕ) : ℤ :=
  max (sumLo box hv (tf c n i) (stepsC c i j))
    ((cTPL : ℤ) - ((sumHi box hv (tf c n i) (degC c i) : ℤ) - sumHi box hv (tf c n i) (stepsC c i j)))

def turnHiZ (box hv : ℕ) (c : GCode) (n i j : ℕ) : ℤ :=
  min (sumHi box hv (tf c n i) (stepsC c i j))
    ((cTPH : ℤ) - ((sumLo box hv (tf c n i) (degC c i) : ℤ) - sumLo box hv (tf c n i) (stepsC c i j)))

theorem sum_Ico_eq_sub' (f : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) :
    ∑ t ∈ Finset.Ico m n, f t = ∑ t ∈ Finset.range n, f t - ∑ t ∈ Finset.range m, f t := by
  rw [Finset.sum_Ico_eq_sub _ h]

theorem turnLo_ge {g hv box : ℕ} (s : Sol g) (hper : ∀ i < Ctx.D g, 0 < (Ctx.code g).period i)
    (a b : s.P.G.Dart)
    (hgood : goodAll box hv (tf (Ctx.code g) s.P.n (s.lab a)) (degC (Ctx.code g) (s.lab a)) = true) :
    (turnLoZ box hv (Ctx.code g) s.P.n (s.lab a) (s.lab b) : ℝ) / 2 ^ 62 ≤
      turnLo (walkBox box (vmOf s hv)) a b := by
  have hst : turnStepsR s.P.R a b = stepsC (Ctx.code g) (s.lab a) (s.lab b) := stepsC_eq s.hm a b
  have hdg : rotDeg a = degC (Ctx.code g) (s.lab a) := degC_eq s.hm a
  have hle := turnStepsR_le_rotDeg s.P a b
  have hg := goodAll_spec hgood
  set St := stepsC (Ctx.code g) (s.lab a) (s.lab b)
  set Dg := degC (Ctx.code g) (s.lab a)
  have hlo : (sumLo box hv (tf (Ctx.code g) s.P.n (s.lab a)) St : ℝ) / 2 ^ 62 =
      ∑ t ∈ Finset.range (turnStepsR s.P.R a b), (walkBox box (vmOf s hv)).lo (cvar ((s.P.R.rot.symm ^ (t + 1)) a)) := by
    rw [hst, sumLo_eq (fun t ht => (hg t (by omega)).1)]
    exact Finset.sum_congr rfl (fun t _ => (walkBox_lo_cvar s hper a t).symm)
  have hhi : ∀ m ≤ Dg, (sumHi box hv (tf (Ctx.code g) s.P.n (s.lab a)) m : ℝ) / 2 ^ 62 =
      ∑ t ∈ Finset.range m, (walkBox box (vmOf s hv)).hi (cvar ((s.P.R.rot.symm ^ (t + 1)) a)) := by
    intro m hm
    rw [sumHi_eq (fun t ht => (hg t (by omega)).2)]
    exact Finset.sum_congr rfl (fun t _ => (walkBox_hi_cvar s hper a t).symm)
  unfold turnLoZ turnLo
  rw [Int.cast_max, ← max_div_div_right (by positivity : (0 : ℝ) ≤ 2 ^ 62)]
  apply max_le_max
  · rw [Int.cast_natCast, hlo]
  · have h2pi := cTPL_le_two_pi
    rw [Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]
    rw [sum_Ico_eq_sub' _ hle, hst, hdg, ← hhi Dg le_rfl, ← hhi St (by rw [hst, hdg] at hle; exact hle)]
    rw [sub_div, sub_div]
    linarith

theorem turnHi_le {g hv box : ℕ} (s : Sol g) (hper : ∀ i < Ctx.D g, 0 < (Ctx.code g).period i)
    (a b : s.P.G.Dart)
    (hgood : goodAll box hv (tf (Ctx.code g) s.P.n (s.lab a)) (degC (Ctx.code g) (s.lab a)) = true) :
    turnHi (walkBox box (vmOf s hv)) a b ≤
      (turnHiZ box hv (Ctx.code g) s.P.n (s.lab a) (s.lab b) : ℝ) / 2 ^ 62 := by
  have hst : turnStepsR s.P.R a b = stepsC (Ctx.code g) (s.lab a) (s.lab b) := stepsC_eq s.hm a b
  have hdg : rotDeg a = degC (Ctx.code g) (s.lab a) := degC_eq s.hm a
  have hle := turnStepsR_le_rotDeg s.P a b
  have hg := goodAll_spec hgood
  set St := stepsC (Ctx.code g) (s.lab a) (s.lab b)
  set Dg := degC (Ctx.code g) (s.lab a)
  have hhi : (sumHi box hv (tf (Ctx.code g) s.P.n (s.lab a)) St : ℝ) / 2 ^ 62 =
      ∑ t ∈ Finset.range (turnStepsR s.P.R a b), (walkBox box (vmOf s hv)).hi (cvar ((s.P.R.rot.symm ^ (t + 1)) a)) := by
    rw [hst, sumHi_eq (fun t ht => (hg t (by omega)).2)]
    exact Finset.sum_congr rfl (fun t _ => (walkBox_hi_cvar s hper a t).symm)
  have hlo : ∀ m ≤ Dg, (sumLo box hv (tf (Ctx.code g) s.P.n (s.lab a)) m : ℝ) / 2 ^ 62 =
      ∑ t ∈ Finset.range m, (walkBox box (vmOf s hv)).lo (cvar ((s.P.R.rot.symm ^ (t + 1)) a)) := by
    intro m hm
    rw [sumLo_eq (fun t ht => (hg t (by omega)).1)]
    exact Finset.sum_congr rfl (fun t _ => (walkBox_lo_cvar s hper a t).symm)
  unfold turnHiZ turnHi
  rw [Int.cast_min, ← min_div_div_right (by positivity : (0 : ℝ) ≤ 2 ^ 62)]
  apply min_le_min
  · rw [Int.cast_natCast, hhi]
  · have h2pi := two_pi_le_cTPH
    rw [Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]
    rw [sum_Ico_eq_sub' _ hle, hst, hdg, ← hlo Dg le_rfl, ← hlo St (by rw [hst, hdg] at hle; exact hle)]
    rw [sub_div, sub_div]
    linarith

end Tammes15.D3Kernel.Kinds
