import Tammes15.Contractors.Defs
import Tammes15.Contractors.Fan
import Tammes15.PaperSteps.MainSearch
import Tammes15.Params.Checks

/-!
# Soundness of the contractors (Proposition B.2 and Theorem B.9 of the paper)

`Tammes15.conjecture_of_enum_progTreesDom` replaces the hypothesis `hN : N.Sound` of
`Tammes15.conjecture_of_enum_progTrees` (PaperSteps/MainSearch.lean) by `Contractors.Impl N`, which
says only how the procedures `N` compute, and by the variant `ProgTreesDom` of `ProgTrees` whose root
boxes also lie in the domain `DomOK` (the program's root box does).

* `RowKind`, `SysRow`: the rows of system.rs `Sys::build` under `--no-face --no-cuts`, each by its
  linear form (any order of terms) and bounds that contain the range of the form at the solutions.
* `Prim`, `Prim.Allowed`, `primStep`: one application of one contractor of deep.rs `Prob::pass`
  (`Contractors.Prims`), or one row of system.rs `fbbt`.
* `DomOK`: every variable of the box within its range in the program's root box (`a ∈ [1.1, 1.3]`,
  `d ∈ [0.9, 1]`, corners in `[1.1, 3.2]` and rhombus corners up to `2.5`, `r ∈ [0.9, 3]`).
* `Run H B o`: `o` is reached from `B` by a finite sequence of primitive steps on boxes of the
  domain, each computed with some arithmetic `R` with `R.Sound`, and of 3B cuts (a slice that a run
  empties is removed). This is what deep.rs `Prob::propagate`, `Prob::shave` and system.rs `fbbt`
  do, whatever their order, their stopping rules and the contractors they skip.
* `Impl N`: on every box of the domain the narrowing of `N` is the outcome of a run, and the wheel
  enclosure of `N` is deep.rs `tri_angle` computed with some `R` with `R.Sound`.

What remains outside Lean is therefore: that the program's arithmetic satisfies `Rnd.Sound` (its
outward rounding), and that its code computes `Run` and `triAngle` (the transcription in
`Contractors.Prims`, with the two guards described there).

The definitions above are in `Tammes15.Contractors.Defs`, a module of definitions only.
-/

namespace Tammes15.Contractors

open Real
open scoped Classical
open Tammes15 Tammes15.PaperSteps Tammes15.PaperSteps.Search

variable {P : PlaneGraph} {k : ℕ}

/-! ## Statements: the primitive steps -/

theorem nar_sound {ι : Type} {B : Box ι} {x : ι → ℝ} (hx : B.Mem x) (j : ι) {n : Iv}
    (hn : n.Mem (x j)) : ∃ B', nar B j n = some B' ∧ B'.Mem x := by
  have hn_mem : Fl.le n.lo (Fl.ofReal (x j)) ∧ Fl.le (Fl.ofReal (x j)) n.hi := hn
  have hxj : B.lo j ≤ x j ∧ x j ≤ B.hi j := hx j
  have h_usable : n.Usable := by
    rcases hn_mem with ⟨hlo, hhi⟩
    exact Fl.le_trans hlo hhi
  have hlo_ofReal : Fl.le (Fl.ofReal (B.lo j)) (Fl.ofReal (x j)) := by
    simpa [Fl.ofReal_le_ofReal] using hxj.1
  have hhi_ofReal : Fl.le (Fl.ofReal (x j)) (Fl.ofReal (B.hi j)) := by
    simpa [Fl.ofReal_le_ofReal] using hxj.2
  have hmax : Fl.le (Fl.max (Fl.ofReal (B.lo j)) n.lo) (Fl.ofReal (x j)) :=
    Fl.max_le hlo_ofReal hn_mem.1
  have hmin : Fl.le (Fl.ofReal (x j)) (Fl.min (Fl.ofReal (B.hi j)) n.hi) :=
    Fl.le_min hhi_ofReal hn_mem.2
  have h_not_lt : ¬ Fl.lt (Fl.min (Fl.ofReal (B.hi j)) n.hi) (Fl.max (Fl.ofReal (B.lo j)) n.lo) := by
    have h_trans : Fl.le (Fl.max (Fl.ofReal (B.lo j)) n.lo) (Fl.min (Fl.ofReal (B.hi j)) n.hi) :=
      Fl.le_trans hmax hmin
    exact Fl.not_lt_of_le h_trans
  have h_nar_eq : nar B j n = some ⟨Function.update B.lo j (Fl.max (Fl.ofReal (B.lo j)) n.lo).toReal,
    Function.update B.hi j (Fl.min (Fl.ofReal (B.hi j)) n.hi).toReal⟩ := by
    unfold nar
    simp [h_usable, h_not_lt]
  refine ⟨⟨Function.update B.lo j (Fl.max (Fl.ofReal (B.lo j)) n.lo).toReal,
    Function.update B.hi j (Fl.min (Fl.ofReal (B.hi j)) n.hi).toReal⟩, h_nar_eq, ?_⟩
  intro i
  by_cases hij : i = j
  · rw [hij]
    simp
    have h_not_nan_lo : Fl.ofReal (B.lo j) ≠ Fl.nan := by simp [Fl.ofReal]
    have h_not_nan_hi : Fl.ofReal (B.hi j) ≠ Fl.nan := by simp [Fl.ofReal]
    have hlo' : Fl.le (Fl.ofReal (B.lo j)) (Fl.max (Fl.ofReal (B.lo j)) n.lo) :=
      Fl.le_max_left h_not_nan_lo
    have hhi' : Fl.le (Fl.min (Fl.ofReal (B.hi j)) n.hi) (Fl.ofReal (B.hi j)) :=
      Fl.min_le_left h_not_nan_hi
    have hlo_res := Fl.le_ofReal_toReal hlo' hmax
    have hhi_res := Fl.le_ofReal_toReal hmin hhi'
    exact ⟨hlo_res.2, hhi_res.1⟩
  · simp [hij, hx i]

theorem rowStep_sound {ι : Type} {R : Rnd} (hR : R.Sound) (r : Row ι) {B : Box ι} {x : ι → ℝ}
    (hx : B.Mem x) (hlo : Fl.le r.lo (.ofReal (r.form x))) (hhi : Fl.le (.ofReal (r.form x)) r.hi) :
    ∃ B', rowStep R r B = some B' ∧ B'.Mem x := by
  let f (t : ι × ℝ) : Fl := cmin R t.2 (B.lo t.1) (B.hi t.1)
  let g (t : ι × ℝ) : Fl := cmax R t.2 (B.lo t.1) (B.hi t.1)
  let y (t : ι × ℝ) : ℝ := t.2 * x t.1
  have hform : r.form x = (r.terms.map y).sum := by
    simp [Row.form, y]
  have hf : ∀ t ∈ r.terms, Fl.le (f t) (.ofReal (y t)) := by
    intro t ht
    rcases hx t.1 with ⟨hlo_t, hhi_t⟩
    dsimp [f, y]
    exact cmin_le hR hlo_t hhi_t
  have hg : ∀ t ∈ r.terms, Fl.le (.ofReal (y t)) (g t) := by
    intro t ht
    rcases hx t.1 with ⟨hlo_t, hhi_t⟩
    dsimp [g, y]
    exact le_cmax hR hlo_t hhi_t
  let mn := r.terms.map f
  let mx := r.terms.map g
  let smin := mn.foldl R.addDn (.ofReal 0)
  let smax := mx.foldl R.addUp (.ofReal 0)
  have hsmin : Fl.le smin (.ofReal (r.form x)) := by
    have := foldl_addDn_le hR r.terms f y hf (.ofReal 0) 0 (le_refl _)
    simpa [smin, hform, zero_add] using this
  have hsmax : Fl.le (.ofReal (r.form x)) smax := by
    have := le_foldl_addUp hR r.terms g y hg (.ofReal 0) 0 (le_refl _)
    simpa [smax, hform, zero_add] using this
  have h_not_lt : ¬ (Fl.lt r.hi smin ∨ Fl.lt smax r.lo) := by
    intro h
    rcases h with (hlt | hlt)
    · have hle : Fl.le smin r.hi := Fl.le_trans hsmin hhi
      exact Fl.not_lt_of_le hle hlt
    · have hle : Fl.le r.lo smax := Fl.le_trans hlo hsmax
      exact Fl.not_lt_of_le hle hlt
  have hzip : mn.zip mx = r.terms.map (fun t => (f t, g t)) := by
    dsimp [mn, mx]
    rw [List.zip_map']
  have hzip' : r.terms.zip (mn.zip mx) = r.terms.map (fun t => (t, f t, g t)) := by
    rw [hzip]
    induction' r.terms with a l ih
    · rfl
    · simp [ih]
  have hL : ∀ p ∈ r.terms.zip (mn.zip mx),
      (R.subDn smin p.2.1 = .nan ∨
        Fl.le (R.subDn smin p.2.1) (.ofReal (r.form x - p.1.2 * x p.1.1))) ∧
      (R.subUp smax p.2.2 = .nan ∨
        Fl.le (.ofReal (r.form x - p.1.2 * x p.1.1)) (R.subUp smax p.2.2)) := by
    intro p hp
    rw [hzip'] at hp
    rcases List.mem_map.mp hp with ⟨t, ht, rfl⟩
    have hsubDn := subDn_foldl_addDn hR r.terms f y hf ht
    have hsubUp := subUp_foldl_addUp hR r.terms g y hg ht
    have hy_eq : y t = t.2 * x t.1 := rfl
    refine ⟨?_, ?_⟩
    · rcases hsubDn with (h | h)
      · left; exact h
      · right; simpa [smin, hform, y] using h
    · rcases hsubUp with (h | h)
      · left; exact h
      · right; simpa [smax, hform, y] using h
  have hstep : rowStep R r B = rowUpd R r smin smax (r.terms.zip (mn.zip mx)) B := by
    rw [rowStep]
    simp [h_not_lt, smin, smax, mn, mx, f, g]
  rcases rowUpd_sound hR r smin smax (r.form x) hlo hhi (r.terms.zip (mn.zip mx)) B hx hL with
    ⟨B', hB', hB'_mem⟩
  refine ⟨B', ?_, hB'_mem⟩
  rw [hstep, hB']

/-! ## Helpers: the values of the corner variables, the domain -/

theorem val_cvar {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H) (e : P.G.Dart) :
    PVar.val A (cvar e : PVar P k) = A.corner e := by
  have hR : RelSys P H A := hA.2.2
  unfold cvar
  split_ifs with h3 h4 hk
  · exact (hR.tri e h3).symm
  · rfl
  · simpa [PVar.val, Assign.fc] using (hR.rhombus e h4).1
  · rfl

theorem val_fv {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H) (e : P.G.Dart) (j : ℕ) :
    PVar.val A (fv e j : PVar P k) = A.fc e j :=
  val_cvar hA _

theorem dom_cvar {B : Box (PVar P k)} (hB : DomOK B) (e : P.G.Dart) :
    1.1 ≤ B.lo (cvar e) ∧ B.hi (cvar e) ≤ 3.2 ∧ (fsize P e = 4 → B.hi (cvar e) ≤ 2.5) := by
  obtain ⟨⟨ha1, ha2⟩, -, hc, -⟩ := hB
  unfold cvar
  split_ifs with h3 h4 hk
  · exact ⟨ha1, by linarith, fun h => by omega⟩
  · exact hc e
  · obtain ⟨h1, h2, h3'⟩ := hc ((P.R.face ^ 2) e)
    exact ⟨h1, h2, fun h => h3' (by rw [FaceWalk.fsize_face_pow]; exact h)⟩
  · exact hc e

theorem dom_fv {B : Box (PVar P k)} (hB : DomOK B) (e : P.G.Dart) (j : ℕ) :
    1.1 ≤ B.lo (fv e j) ∧ B.hi (fv e j) ≤ 3.2 ∧ (fsize P e = 4 → B.hi (fv e j) ≤ 2.5) := by
  obtain ⟨h1, h2, h3⟩ := dom_cvar hB ((P.R.face ^ j) e)
  exact ⟨h1, h2, fun h => h3 (by rw [FaceWalk.fsize_face_pow]; exact h)⟩

theorem ivOf_mem {ι : Type} {B : Box ι} {x : ι → ℝ} (hx : B.Mem x) (v : ι) :
    (ivOf B v).Mem (x v) :=
  Iv.mem_ofReal.mpr (hx v)

/-- The value of the corner `j` steps along the face of `e`, between the ends of its variable. -/
theorem fv_mem {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H) {B : Box (PVar P k)}
    (hm : B.Mem (PVar.val A)) (e : P.G.Dart) (j : ℕ) :
    B.lo (fv e j) ≤ A.fc e j ∧ A.fc e j ≤ B.hi (fv e j) := by
  have h := hm (fv e j)
  rwa [val_fv hA] at h

theorem d_mem {A : Assign P k} {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A)) :
    0.9 ≤ B.lo .d ∧ B.lo .d ≤ A.d ∧ A.d ≤ B.hi .d ∧ B.hi .d ≤ 1 :=
  ⟨hB.2.1.1, (hm .d).1, (hm .d).2, hB.2.1.2⟩

theorem d_pos_lt {A : Assign P k} {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A)) :
    0 < A.d ∧ A.d < π / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := d_mem hB hm
  constructor <;> linarith [Real.pi_gt_three]

/-- (T7) at the upper end `uh` of a corner `u ≤ uh`, against a corner `v ≥ α(d)` with
`L(u, d) ≤ v`. -/
theorem longDiag_le_corner {d u uh v : ℝ} (hd : 0.9 ≤ d ∧ d ≤ 1) (hu : 0 < u) (huh : u ≤ uh)
    (huh' : uh ≤ 3.2) (hv : alpha d ≤ v) (hL : longDiag d u ≤ v) : longDiag d uh ≤ v := by
  have hd' : 0 < d ∧ d < π / 2 := ⟨by linarith, by linarith [Real.pi_gt_three]⟩
  by_cases hpi : uh ≤ π
  · have h := T7_bound_antitoneOn d hd' ⟨hu, huh.trans hpi⟩ ⟨hu.trans_le huh, hpi⟩ huh
    exact le_trans h hL
  · have h1 := longDiag_le_of_pi_lt ⟨by linarith, hd.2⟩ ⟨lt_of_not_ge hpi, huh'⟩
    have h2 := (alpha_bounds d hd').1
    linarith

/-! ## The contractors of deep.rs -/

/-- `DomOK` passes to sub-boxes. -/
theorem DomOK.mono {B B' : Box (PVar P k)} (hB : DomOK B)
    (h : ∀ v, B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v) : DomOK B' := by
  obtain ⟨⟨ha1, ha2⟩, ⟨hd1, hd2⟩, hc, hr⟩ := hB
  refine ⟨⟨ha1.trans (h .a).1, (h .a).2.trans ha2⟩, ⟨hd1.trans (h .d).1, (h .d).2.trans hd2⟩,
    fun e => ?_, fun m j => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hc e
    exact ⟨h1.trans (h (.c e)).1, (h (.c e)).2.trans h2, fun h4 => (h (.c e)).2.trans (h3 h4)⟩
  · obtain ⟨h1, h2⟩ := hr m j
    exact ⟨h1.trans (h (.r m j)).1, (h (.r m j)).2.trans h2⟩


/-! Generic lemmas. -/

theorem cos_side_of_gam {s b c : ℝ} (hb : 0 < b ∧ b < π)
    (hc : 0 < c ∧ c < π) (he : eta s b c ∈ Set.Icc (-1 : ℝ) 1) :
    cos s = cos b * cos c + sin b * sin c * cos (gam s b c) := by
  rcases hb with ⟨hb_pos, hb_lt⟩
  rcases hc with ⟨hc_pos, hc_lt⟩
  rcases he with ⟨hlo, hhi⟩
  have hcos_arccos : cos (gam s b c) = eta s b c := by
    rw [gam, eta]
    exact Real.cos_arccos hlo hhi
  have hsinb_pos : sin b > 0 := Real.sin_pos_of_pos_of_lt_pi hb_pos hb_lt
  have hsinc_pos : sin c > 0 := Real.sin_pos_of_pos_of_lt_pi hc_pos hc_lt
  have h_denom_ne_zero : sin b * sin c ≠ 0 := by
    exact mul_ne_zero (ne_of_gt hsinb_pos) (ne_of_gt hsinc_pos)
  rw [hcos_arccos, eta]
  field_simp [h_denom_ne_zero]
  ring

theorem triAngle_of_eta {R : Rnd} (hR : R.Sound) {G E F : Iv}
    {g e f : ℝ} (hg : G.Mem g) (he : E.Mem e) (hf : F.Mem f) (hη : eta g e f ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ I, triAngle R G E F = some I ∧ I.Mem (gam g e f) := by
  unfold triAngle
  rcases triAngleSt_mem hR hg he hf with ⟨I, hI, hm⟩ | ⟨I, -, -, hout⟩
  · refine ⟨I, ?_, hm⟩
    rw [hI]
    rfl
  · exfalso
    rcases hout with (hlt | hgt)
    · have hmem := Set.mem_Icc.mp hη
      linarith
    · have hmem := Set.mem_Icc.mp hη
      linarith

theorem foldlM_option_inv {α β : Type} (f : β → α → Option β)
    (Inv : β → Prop) (l : List α) (h : ∀ b a, a ∈ l → Inv b → ∃ b', f b a = some b' ∧ Inv b')
    (b : β) (hb : Inv b) : ∃ b', l.foldlM f b = some b' ∧ Inv b' := by
  induction l generalizing b with
  | nil =>
    refine ⟨b, ?_, hb⟩
    simp [List.foldlM]
  | cons a l ih =>
    have ha_mem : a ∈ a :: l := List.mem_cons_self
    rcases h b a ha_mem hb with ⟨b₁, hf, hb₁⟩
    simp only [List.foldlM_cons, hf]
    have h_rest : ∀ b' a', a' ∈ l → Inv b' → ∃ b'', f b' a' = some b'' ∧ Inv b'' := by
      intro b' a' ha'_mem hb'
      apply h b' a' (List.mem_cons_of_mem a ha'_mem) hb'
    rcases ih h_rest b₁ hb₁ with ⟨b', hfold, hb'⟩
    exact ⟨b', hfold, hb'⟩

theorem foldlM_option_rel {α β : Type} (f : β → α → Option β)
    (Rel : β → β → Prop) (hrefl : ∀ b, Rel b b) (htrans : ∀ a b c, Rel a b → Rel b c → Rel a c)
    (h : ∀ b a b', f b a = some b' → Rel b b') (l : List α) (b b' : β)
    (hl : l.foldlM f b = some b') : Rel b b' := by
  induction l generalizing b with
  | nil =>
      -- List.foldlM f b [] = some b, so hl : some b = some b'
      have h_eq : b = b' := Option.some.inj hl
      subst h_eq
      exact hrefl b
  | cons a l ih =>
      -- List.foldlM f b (a :: l) = (f b a).bind (fun b₁ => l.foldlM f b₁)
      have hbind := (Option.bind_eq_some_iff (x := f b a) (f := fun b₁ => l.foldlM f b₁)).mp hl
      rcases hbind with ⟨b₁, hfb, hrest⟩
      have hrel1 : Rel b b₁ := h b a b₁ hfb
      have hrel2 : Rel b₁ b' := ih b₁ hrest
      exact htrans b b₁ b' hrel1 hrel2

theorem mapM_option_forall2 {α β : Type} (f : α → Option β)
    (Q : α → β → Prop) (l : List α) (h : ∀ a ∈ l, ∃ b, f a = some b ∧ Q a b) :
    ∃ L, l.mapM f = some L ∧ List.Forall₂ Q l L := by
  induction' l with a l ih
  · refine ⟨[], ?_, List.Forall₂.nil⟩
    rfl
  · have ha := h a (by simp)
    rcases ha with ⟨b, hfa, hQab⟩
    have hl : ∀ a' ∈ l, ∃ b', f a' = some b' ∧ Q a' b' := by
      intro a' ha'
      exact h a' (by simp [ha'])
    rcases ih hl with ⟨L, hLmap, hLforall⟩
    refine ⟨b :: L, ?_, List.Forall₂.cons hQab hLforall⟩
    simp [List.mapM_cons, hfa, hLmap]

theorem foldl_add_mem {R : Rnd} (hR : R.Sound) {α : Type} (g : α → ℝ) :
    ∀ (l : List α) (L : List Iv), List.Forall₂ (fun a I => I.Mem (g a)) l L →
      ∀ (J : Iv) (s : ℝ), J.Mem s → (L.foldl R.add J).Mem (s + (l.map g).sum) := by
  intro l L h
  induction h
  case nil =>
    intro J s hJ
    simp [hJ]
  case cons a I l' L' hI hForall ih =>
    intro J s hJ
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    have h_add : (R.add J I).Mem (s + g a) := hR.add J I s (g a) hJ hI
    have ih' := ih (R.add J I) (s + g a) h_add
    simp [add_assoc] at ih' ⊢
    exact ih'

theorem Ssum_monotoneOn : MonotoneOn Ssum (Set.Ico 0 (π / 2)) := by
  intro d₁ hd₁ d₂ hd₂ hle
  rcases hd₁ with ⟨hd₁l, hd₁r⟩
  rcases hd₂ with ⟨hd₂l, hd₂r⟩
  have hcos : cos d₂ ≤ cos d₁ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hd₁l (by linarith) hle
  have hcos_pos₂ : 0 < cos d₂ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos_pos₁ : 0 < cos d₁ := by linarith
  have hsqrt_pos₂ : 0 < Real.sqrt (cos d₂) := Real.sqrt_pos.mpr hcos_pos₂
  have hsqrt_pos₁ : 0 < Real.sqrt (cos d₁) := Real.sqrt_pos.mpr hcos_pos₁
  have hsqrt_le : Real.sqrt (cos d₂) ≤ Real.sqrt (cos d₁) :=
    Real.sqrt_le_sqrt hcos
  have hone_div : 1 / Real.sqrt (cos d₁) ≤ 1 / Real.sqrt (cos d₂) :=
    ((one_div_le_one_div hsqrt_pos₁ hsqrt_pos₂).mpr hsqrt_le)
  have harctan : Real.arctan (1 / Real.sqrt (cos d₁)) ≤ Real.arctan (1 / Real.sqrt (cos d₂)) :=
    Real.arctan_mono hone_div
  have hSsum : Ssum d₁ ≤ Ssum d₂ := by
    unfold Ssum
    nlinarith
  exact hSsum

/-- The kinds of rows hold at the solutions. -/
theorem rowKind_holds {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H) (κ : RowKind P k)
    (hκ : κ.Allowed) :
    κ.lo ≤ ((κ.form (PVar.val A) : ℝ) : EReal) ∧ ((κ.form (PVar.val A) : ℝ) : EReal) ≤ κ.hi := by
  have hR : RelSys P H A := hA.2.2
  have hd : 0 < A.d ∧ A.d < π / 2 :=
    ⟨by linarith [pi_div_four_lt_dlo, Real.pi_pos, hA.1],
      by linarith [dhi_lt_pi_div_three, hA.2.1, Real.pi_pos]⟩
  have hrr : ∀ e, fsize P e = 4 → A.fc e 0 ≤ 2 * alpha A.d ∧ A.fc e 1 ≤ 2 * alpha A.d ∧
      3 * alpha A.d ≤ A.fc e 0 + A.fc e 1 ∧ A.fc e 0 + A.fc e 1 ≤ Ssum A.d := fun e he =>
    rhombus_rows A.d (A.fc e 0) (A.fc e 1) hd (hR.rhombus e he).2
      (hR.corner_mem ((P.R.face ^ 0) e)) (hR.corner_mem ((P.R.face ^ 1) e)).1
  have hc0 : ∀ e, alpha A.d ≤ A.fc e 0 := fun e => (hR.corner_mem ((P.R.face ^ 0) e)).1
  cases κ with
  | vertex v =>
    have h : RowKind.form (.vertex v) (PVar.val A) = 2 * π := by
      simp only [RowKind.form]
      rw [Finset.sum_congr rfl (fun e _ => val_cvar hA e)]
      exact hR.vertex_sum v
    rw [h]
    exact ⟨le_rfl, le_rfl⟩
  | rhSum e =>
    have h : RowKind.form (.rhSum e) (PVar.val A) = A.fc e 0 + A.fc e 1 - 3 * alpha A.d := by
      simp only [RowKind.form, val_fv hA]; rfl
    obtain ⟨-, -, h3, -⟩ := hrr e hκ
    rw [h]
    exact ⟨EReal.coe_nonneg.mpr (by linarith), le_top⟩
  | rhSumHi e =>
    have h : RowKind.form (.rhSumHi e) (PVar.val A) = A.fc e 0 + A.fc e 1 := by
      simp only [RowKind.form, val_fv hA]
    obtain ⟨-, -, -, h4⟩ := hrr e hκ
    have hdhi : 0 ≤ dhi := by linarith [pi_div_four_lt_dlo, dlo_lt_dhi, Real.pi_pos]
    have hS : Ssum A.d ≤ Ssum dhi :=
      Ssum_monotoneOn ⟨hd.1.le, hd.2⟩ ⟨hdhi, by linarith [dhi_lt_pi_div_three, Real.pi_pos]⟩
        hA.2.1
    have hS' : Ssum dhi ≤ (3.73170040409990243346 : ℝ) := Params.smax_dhi_le_file
    rw [h]
    exact ⟨bot_le, EReal.coe_le_coe_iff.mpr (by linarith)⟩
  | rhLo e =>
    have h : RowKind.form (.rhLo e) (PVar.val A) = A.fc e 0 - alpha A.d := by
      simp only [RowKind.form, val_fv hA]; rfl
    rw [h]
    exact ⟨EReal.coe_nonneg.mpr (by linarith [hc0 e]), le_top⟩
  | rhHi e =>
    have h : RowKind.form (.rhHi e) (PVar.val A) = A.fc e 0 - 2 * alpha A.d := by
      simp only [RowKind.form, val_fv hA]; rfl
    obtain ⟨h1, -, -, -⟩ := hrr e hκ
    rw [h]
    refine ⟨bot_le, ?_⟩
    simp only [RowKind.hi]
    exact_mod_cast (show A.fc e 0 - 2 * alpha A.d ≤ 0 by linarith)
  | corner e =>
    have h : RowKind.form (.corner e) (PVar.val A) = A.fc e 0 - alpha A.d := by
      simp only [RowKind.form, val_fv hA]; rfl
    rw [h]
    exact ⟨EReal.coe_nonneg.mpr (by linarith [hc0 e]), le_top⟩

theorem sysRow_holds {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H)
    {r : Row (PVar P k)} (hr : SysRow r) :
    Fl.le r.lo (.ofReal (r.form (PVar.val A))) ∧ Fl.le (.ofReal (r.form (PVar.val A))) r.hi := by
  obtain ⟨κ, hκ, hform, hlo, hhi⟩ := hr
  obtain ⟨h1, h2⟩ := rowKind_holds hA κ hκ
  rw [hform]
  exact ⟨Fl.le_trans hlo (show Fl.le (.num κ.lo) (.ofReal _) from h1),
    Fl.le_trans (show Fl.le (.ofReal _) (.num κ.hi) from h2) hhi⟩

theorem alphaStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A)) :
    ∃ B', alphaStep R B = some B' ∧ B'.Mem (PVar.val A) := by
  obtain ⟨h1, h2, h3, h4⟩ := d_mem hB hm
  unfold alphaStep
  exact nar_sound hm .a (alphaIv_mem hR (by linarith) h2 h3 (by linarith [Real.pi_gt_three]))

theorem alphaInvStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A)) :
    ∃ B', alphaInvStep R B = some B' ∧ B'.Mem (PVar.val A) := by
  have hd := d_pos_lt hB hm
  have ha : B.lo .a ≤ alpha A.d ∧ alpha A.d ≤ B.hi .a := hm .a
  obtain ⟨⟨ha1, ha2⟩, -⟩ := hB
  unfold alphaInvStep
  exact nar_sound hm .d (alphaInvIv_mem hR hd ha.1 ha.2 (by linarith [Real.pi_lt_d2])
    (by linarith [Real.pi_gt_three]))

theorem rhoStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A))
    {e : P.G.Dart} (he : fsize P e = 4) :
    ∃ B', rhoStep R B e = some B' ∧ B'.Mem (PVar.val A) := by
  have hR' : RelSys P H A := hA.2.2
  obtain ⟨hx1, -, hx3⟩ := dom_fv hB e 0
  have hx := fv_mem hA hm e 0
  obtain ⟨h1, h2, h3, h4⟩ := d_mem hB hm
  have hrh := (hR'.rhombus e he).2
  unfold rhoStep
  refine nar_sound hm (fv e 1) ?_
  rw [val_fv hA, hrh]
  exact rhoIv_mem hR hx ⟨h2, h3⟩ (by linarith) (by linarith [hx3 he, Real.pi_gt_three])
    (by linarith) (by linarith [Real.pi_gt_three])

theorem rhoDStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A))
    {e : P.G.Dart} (he : fsize P e = 4) :
    ∃ B', rhoDStep R B e = some B' ∧ B'.Mem (PVar.val A) := by
  have hR' : RelSys P H A := hA.2.2
  have hd := d_pos_lt hB hm
  obtain ⟨hx1, -, hx3⟩ := dom_fv hB e 0
  obtain ⟨hy1, -, hy3⟩ := dom_fv hB e 1
  have hx := fv_mem hA hm e 0
  have hy := fv_mem hA hm e 1
  have hrh := (hR'.rhombus e he).2
  have hxc : 0 < A.fc e 0 ∧ A.fc e 0 < π :=
    ⟨by linarith, by linarith [hx3 he, Real.pi_gt_three]⟩
  have hc := cot_mul_cot_rho A.d (A.fc e 0) hd hxc
  rw [← hrh] at hc
  obtain ⟨I, hI, hIm⟩ := rhombusD_sound hR hx hy (by linarith)
    (by linarith [hx3 he, Real.pi_gt_three]) (by linarith) (by linarith [hy3 he, Real.pi_gt_three])
    ⟨hd.1.le, by linarith [Real.pi_gt_three]⟩ hc
  unfold rhoDStep
  have h' : rhombusD R (ivOf B (fv e 0)) (ivOf B (fv e 1)) = some I := hI
  rw [h']
  exact nar_sound hm .d hIm

/-! ## The fans of pentagons and hexagons -/

/-! Fan lemmas. -/

theorem tri_strict_of_eta {b c e : ℝ} (hb : 0 < b ∧ b < π)
    (hc : 0 < c ∧ c < π) (he : 0 < e ∧ e < π) (h : -1 < eta c e b ∧ eta c e b < 1) :
    |b - c| < e ∧ e < min (b + c) (2 * π - b - c) := by
  rcases hb with ⟨hb0, hb1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases he with ⟨he0, he1⟩
  rcases h with ⟨hlo, hhi⟩
  by_cases h_abs : |b - c| < e
  · by_cases h_min : e < min (b + c) (2 * π - b - c)
    · exact ⟨h_abs, h_min⟩
    · -- h_min : ¬ e < min (b + c) (2 * π - b - c), so min (b + c) (2 * π - b - c) ≤ e
      have h_min_le : min (b + c) (2 * π - b - c) ≤ e := by linarith
      have hgam := gam_of_min_le ⟨hb0, hb1⟩ ⟨hc0, hc1⟩ ⟨he0, he1⟩ h_min_le
      dsimp [gam] at hgam
      split_ifs at hgam with hbc
      · have h_one_le : 1 ≤ eta c e b := (Real.arccos_eq_zero.mp hgam)
        linarith
      · have h_neg_one : eta c e b ≤ -1 := (Real.arccos_eq_pi.mp hgam)
        linarith
  · -- h_abs : ¬ |b - c| < e, so e ≤ |b - c|
    have hle : e ≤ |b - c| := by linarith
    have hgam := gam_of_le_abs ⟨hb0, hb1⟩ ⟨hc0, hc1⟩ ⟨he0, he1⟩ hle
    dsimp [gam] at hgam
    split_ifs at hgam with hcb
    · have h_one_le : 1 ≤ eta c e b := (Real.arccos_eq_zero.mp hgam)
      linarith
    · have h_neg_one : eta c e b ≤ -1 := (Real.arccos_eq_pi.mp hgam)
      linarith

theorem gam_Ioo_of_eta {b c e : ℝ} (hb : 0 < b ∧ b < π)
    (hc : 0 < c ∧ c < π) (he : 0 < e ∧ e < π) (h : -1 < eta c e b ∧ eta c e b < 1) :
    0 < gam b e c ∧ gam b e c < π := by
  rcases hb with ⟨hb_left, hb_right⟩
  rcases hc with ⟨hc_left, hc_right⟩
  rcases he with ⟨he_left, he_right⟩
  rcases h with ⟨h_eta_gt, h_eta_lt⟩
  have hsin_e_pos : 0 < sin e := Real.sin_pos_of_mem_Ioo ⟨he_left, he_right⟩
  have hsin_c_pos : 0 < sin c := Real.sin_pos_of_mem_Ioo ⟨hc_left, hc_right⟩
  have hsin_b_pos : 0 < sin b := Real.sin_pos_of_mem_Ioo ⟨hb_left, hb_right⟩
  have h_denom_pos : 0 < sin e * sin c := mul_pos hsin_e_pos hsin_c_pos
  have h_denom_pos' : 0 < sin e * sin b := mul_pos hsin_e_pos hsin_b_pos
  have h_denom_ne_zero : sin e * sin c ≠ 0 := by linarith
  have h_denom_ne_zero' : sin e * sin b ≠ 0 := by linarith
  -- Expand definitions
  dsimp [gam, eta] at *
  -- rewrite -1 as (-denom)/denom to use div_lt_div_right
  have h_neg_one_eq : (-1 : ℝ) = (-(sin e * sin b)) / (sin e * sin b) := by
    field_simp [h_denom_ne_zero']
  rw [h_neg_one_eq] at h_eta_gt
  have h_cos_lt : cos c - cos e * cos b < sin e * sin b := by
    exact (div_lt_one h_denom_pos').mp h_eta_lt
  have h_cos_gt : -(sin e * sin b) < cos c - cos e * cos b := by
    exact ((div_lt_div_iff_of_pos_right h_denom_pos').mp h_eta_gt)
  -- Square both sides: |cos c - cos e * cos b| < sin e * sin b → (cos c - cos e * cos b)^2 < (sin e * sin b)^2
  have h_sq_lt : (cos c - cos e * cos b)^2 < (sin e * sin b)^2 := by
    have h_abs : |cos c - cos e * cos b| < sin e * sin b := by
      rw [abs_lt]
      exact ⟨h_cos_gt, h_cos_lt⟩
    have h_sq_abs : (cos c - cos e * cos b)^2 = |cos c - cos e * cos b|^2 := by
      rw [sq_abs]
    have h_nonneg : 0 ≤ |cos c - cos e * cos b| := abs_nonneg _
    nlinarith
  -- The key algebraic identity: swapping b and c preserves the squared difference
  have h_sq_lt_symm : (cos b - cos e * cos c)^2 < (sin e * sin c)^2 := by
    have h_expand_eq : (cos c - cos e * cos b)^2 - (sin e * sin b)^2 =
                       (cos b - cos e * cos c)^2 - (sin e * sin c)^2 := by
      nlinarith [Real.cos_sq_add_sin_sq e, Real.cos_sq_add_sin_sq b, Real.cos_sq_add_sin_sq c]
    have h_neg : (cos c - cos e * cos b)^2 - (sin e * sin b)^2 < 0 := by linarith
    have h_neg_symm : (cos b - cos e * cos c)^2 - (sin e * sin c)^2 < 0 := by
      rw [← h_expand_eq]
      exact h_neg
    linarith
  -- Now convert back: from squared inequality to the original bounds
  have h_bound_symm : -(sin e * sin c) < cos b - cos e * cos c ∧ cos b - cos e * cos c < sin e * sin c := by
    have h_nonneg_denom : 0 ≤ sin e * sin c := by linarith
    exact abs_lt_of_sq_lt_sq' h_sq_lt_symm h_nonneg_denom
  rcases h_bound_symm with ⟨h_cos_gt_symm, h_cos_lt_symm⟩
  -- Now divide by the positive denominator to get bounds on eta b e c
  have h_eta_b_lt_one : (cos b - cos e * cos c) / (sin e * sin c) < 1 := by
    exact (div_lt_one h_denom_pos).mpr h_cos_lt_symm
  have h_eta_b_gt_neg_one : -1 < (cos b - cos e * cos c) / (sin e * sin c) := by
    have h_neg_one_eq' : (-1 : ℝ) = (-(sin e * sin c)) / (sin e * sin c) := by
      field_simp [h_denom_ne_zero]
    rw [h_neg_one_eq']
    exact ((div_lt_div_iff_of_pos_right h_denom_pos).mpr h_cos_gt_symm)
  -- Now use arccos properties
  have h_pos : 0 < arccos ((cos b - cos e * cos c) / (sin e * sin c)) := by
    rw [Real.arccos_pos]
    exact h_eta_b_lt_one
  have h_lt_pi : arccos ((cos b - cos e * cos c) / (sin e * sin c)) < π := by
    by_contra! hge
    have h_eq : arccos ((cos b - cos e * cos c) / (sin e * sin c)) = π := by
      have hle := Real.arccos_le_pi ((cos b - cos e * cos c) / (sin e * sin c))
      linarith
    have h_le_neg_one : (cos b - cos e * cos c) / (sin e * sin c) ≤ -1 :=
      (Real.arccos_eq_pi.mp h_eq)
    linarith
  exact And.intro h_pos h_lt_pi

theorem fan_anti_of_decDir {R : Rnd} (hR : R.Sound) {lo hi d b c : ℝ}
    {D BX X : Iv} (hlo : 0 < lo) (hD : D.Mem d) (hd : 0 < d ∧ d < π / 2)
    (hb : 0 < b ∧ b < π) (hc : 0 < c ∧ c < π)
    (hbx : ∀ u ∈ Set.Icc lo (min hi π), BX.Mem (bangle d u + gam b (ebase d u) c))
    (hx : ∀ u ∈ Set.Icc lo (min hi π), X.Mem (gam b (ebase d u) c))
    (hdir : decDir R (Iv.ofReal lo hi) BX X D = -1) :
    AntitoneOn (fun u => bangle d u + gam c (ebase d u) b) (Set.Icc lo (min hi π)) := by
  refine fanC_antitoneOn hd hb hc hlo (min_le_right hi π) ?_
  intro u hu h_eta_lo h_eta_hi
  have hu_mem := Set.mem_Icc.1 hu
  have hlo_u : 0 < u := by linarith
  have hpi_u : u ≤ π := by
    have h_min := min_le_right hi π
    linarith
  have he : 0 < ebase d u ∧ ebase d u < π :=
    ebase_mem_Ioo d u hd ⟨hlo_u, hpi_u⟩
  have h_gam : 0 < gam b (ebase d u) c ∧ gam b (ebase d u) c < π :=
    gam_Ioo_of_eta hb hc he ⟨h_eta_lo, h_eta_hi⟩
  exact decDir_sound hR (Y := fun u => gam b (ebase d u) c) hlo hD hd
    (fun u hu _ _ => hbx u hu) (fun u hu _ _ => hx u hu) hdir u hu h_gam.1 h_gam.2

theorem decDir_ne_one (R : Rnd) (u bx x d : Iv) :
    decDir R u bx x d ≠ 1 := by
  unfold decDir
  dsimp only
  split_ifs <;> norm_num

theorem triAngleC_mem {R : Rnd} (hR : R.Sound) {G E F : Iv}
    {g e f : ℝ} (hg : G.Mem g) (he : E.Mem e) (hf : F.Mem f) :
    (triAngleC R G E F).Mem (gam g e f) := by
  rcases triAngleSt_mem hR hg he hf with ⟨I, hI, hm⟩ | ⟨I, hI, hm, -⟩
  · simpa [triAngleC, hI] using hm
  · simpa [triAngleC, hI] using hm

theorem triAngle_mem_of_some {R : Rnd} (hR : R.Sound)
    {G E F I : Iv} {g e f : ℝ} (h : triAngle R G E F = some I) (hg : G.Mem g) (he : E.Mem e)
    (hf : F.Mem f) : I.Mem (gam g e f) := by
  unfold triAngle at h
  have hcases := triAngleSt_mem hR hg he hf
  rcases hcases with (⟨I', hst, hI'⟩ | ⟨I', hst, hI', heta⟩)
  · rw [hst] at h
    simp [Except.toOption] at h
    rw [h] at hI'
    exact hI'
  · rw [hst] at h
    simp [Except.toOption] at h

theorem ends_form (R : Rnd) {lo hi x : ℝ} {X : Iv} (hlo : 0 < lo)
    (hlh : lo ≤ hi) (hhi : hi < 2 * π)
    (hX : X = Iv.ofReal lo hi ∨ X = (cornerEnds R (Iv.ofReal lo hi)).1 ∨
      X = (cornerEnds R (Iv.ofReal lo hi)).2) (hx : X.Mem x) :
    ∃ ul uh, X = Iv.ofReal ul uh ∧ 0 < ul ∧ uh < 2 * π ∧ ul ≤ x ∧ x ≤ uh := by
  rcases hX with rfl | rfl | rfl
  · -- X = Iv.ofReal lo hi
    rcases (Iv.mem_ofReal.mp hx) with ⟨hx1, hx2⟩
    exact ⟨lo, hi, rfl, hlo, hhi, hx1, hx2⟩
  · -- X = (cornerEnds R (Iv.ofReal lo hi)).1
    rcases cornerEnds_forms R lo hi with ⟨h1, h2⟩
    rcases h1 with h | h
    · -- h: (cornerEnds R B).1 = Iv.ofReal lo lo
      rw [h] at hx ⊢
      rcases (Iv.mem_ofReal.mp hx) with ⟨hx1, hx2⟩
      have hlo_lt_2pi : lo < 2 * π := by linarith
      exact ⟨lo, lo, rfl, hlo, hlo_lt_2pi, hx1, hx2⟩
    · -- h: (cornerEnds R B).1 = Iv.ofReal lo hi
      rw [h] at hx ⊢
      rcases (Iv.mem_ofReal.mp hx) with ⟨hx1, hx2⟩
      exact ⟨lo, hi, rfl, hlo, hhi, hx1, hx2⟩
  · -- X = (cornerEnds R (Iv.ofReal lo hi)).2
    rcases cornerEnds_forms R lo hi with ⟨h1, h2⟩
    rcases h2 with h | h
    · -- h: (cornerEnds R B).2 = Iv.ofReal hi hi
      rw [h] at hx ⊢
      rcases (Iv.mem_ofReal.mp hx) with ⟨hx1, hx2⟩
      have hhi_pos : 0 < hi := by linarith
      exact ⟨hi, hi, rfl, hhi_pos, hhi, hx1, hx2⟩
    · -- h: (cornerEnds R B).2 = Iv.ofReal (max lo R.piLo) hi
      rw [h] at hx ⊢
      rcases (Iv.mem_ofReal.mp hx) with ⟨hx1, hx2⟩
      have hmax_pos : 0 < max lo R.piLo :=
        lt_of_lt_of_le hlo (le_max_left _ _)
      exact ⟨max lo R.piLo, hi, rfl, hmax_pos, hhi, hx1, hx2⟩

theorem pentEvalC_mem {R : Rnd} (hR : R.Sound) {D : Iv} {d : ℝ}
    (hD : D.Mem d) (hd : 0 < d ∧ d < π / 2) {X : Fin 2 → Iv} {x : Fin 2 → ℝ}
    (hX : ∀ j, ∃ ul uh, X j = Iv.ofReal ul uh ∧ 0 < ul ∧ uh < 2 * π ∧ ul ≤ x j ∧ x j ≤ uh) :
    (pentEvalC R D X 0).Mem
        (bangle d (x 0) + gam d (ebase d (x 0)) (ebase d (x 1)) + bangle d (x 1)) ∧
      (pentEvalC R D X 1).Mem (bangle d (x 0) + gam (ebase d (x 1)) (ebase d (x 0)) d) ∧
      (pentEvalC R D X 2).Mem (bangle d (x 1) + gam (ebase d (x 0)) (ebase d (x 1)) d) := by
  rcases hX 0 with ⟨ul₀, uh₀, hX0, h0pos, h0lt, h0le, h0ge⟩
  rcases hX 1 with ⟨ul₁, uh₁, hX1, h1pos, h1lt, h1le, h1ge⟩
  have hX0mem : (X 0).Mem (x 0) := by
    rw [hX0]
    exact (Iv.mem_ofReal.mpr ⟨h0le, h0ge⟩)
  have hX1mem : (X 1).Mem (x 1) := by
    rw [hX1]
    exact (Iv.mem_ofReal.mpr ⟨h1le, h1ge⟩)
  have he0 : (isoBase R (X 0) D).Mem (ebase d (x 0)) :=
    isoBase_mem hR hX0mem hD
  have he1 : (isoBase R (X 1) D).Mem (ebase d (x 1)) :=
    isoBase_mem hR hX1mem hD
  have hb0 : (isoAngle R (X 0) D).Mem (bangle d (x 0)) := by
    rw [hX0]
    exact isoAngle_mem hR ⟨h0le, h0ge⟩ h0pos h0lt hD hd
  have hb1 : (isoAngle R (X 1) D).Mem (bangle d (x 1)) := by
    rw [hX1]
    exact isoAngle_mem hR ⟨h1le, h1ge⟩ h1pos h1lt hD hd
  have hg0 : (triAngleC R D (isoBase R (X 0) D) (isoBase R (X 1) D)).Mem
      (gam d (ebase d (x 0)) (ebase d (x 1))) :=
    triAngleC_mem hR hD he0 he1
  have hg1 : (triAngleC R (isoBase R (X 1) D) (isoBase R (X 0) D) D).Mem
      (gam (ebase d (x 1)) (ebase d (x 0)) d) :=
    triAngleC_mem hR he1 he0 hD
  have hg2 : (triAngleC R (isoBase R (X 0) D) (isoBase R (X 1) D) D).Mem
      (gam (ebase d (x 0)) (ebase d (x 1)) d) :=
    triAngleC_mem hR he0 he1 hD
  have hsum0 : (R.add (isoAngle R (X 0) D) (triAngleC R D (isoBase R (X 0) D) (isoBase R (X 1) D))).Mem
      (bangle d (x 0) + gam d (ebase d (x 0)) (ebase d (x 1))) :=
    hR.add (isoAngle R (X 0) D) (triAngleC R D (isoBase R (X 0) D) (isoBase R (X 1) D))
      (bangle d (x 0)) (gam d (ebase d (x 0)) (ebase d (x 1))) hb0 hg0
  have hsum1 : (R.add (isoAngle R (X 0) D) (triAngleC R (isoBase R (X 1) D) (isoBase R (X 0) D) D)).Mem
      (bangle d (x 0) + gam (ebase d (x 1)) (ebase d (x 0)) d) :=
    hR.add (isoAngle R (X 0) D) (triAngleC R (isoBase R (X 1) D) (isoBase R (X 0) D) D)
      (bangle d (x 0)) (gam (ebase d (x 1)) (ebase d (x 0)) d) hb0 hg1
  have hsum2 : (R.add (isoAngle R (X 1) D) (triAngleC R (isoBase R (X 0) D) (isoBase R (X 1) D) D)).Mem
      (bangle d (x 1) + gam (ebase d (x 0)) (ebase d (x 1)) d) :=
    hR.add (isoAngle R (X 1) D) (triAngleC R (isoBase R (X 0) D) (isoBase R (X 1) D) D)
      (bangle d (x 1)) (gam (ebase d (x 0)) (ebase d (x 1)) d) hb1 hg2
  have h0 : (pentEvalC R D X 0).Mem
      (bangle d (x 0) + gam d (ebase d (x 0)) (ebase d (x 1)) + bangle d (x 1)) := by
    unfold pentEvalC; simp; exact hR.add _ _ _ _ hsum0 hb1
  have h1 : (pentEvalC R D X 1).Mem
      (bangle d (x 0) + gam (ebase d (x 1)) (ebase d (x 0)) d) := by
    unfold pentEvalC; simp; exact hsum1
  have h2 : (pentEvalC R D X 2).Mem
      (bangle d (x 1) + gam (ebase d (x 0)) (ebase d (x 1)) d) := by
    unfold pentEvalC; simp; exact hsum2
  exact ⟨h0, h1, h2⟩

theorem hexEvalC_mem {R : Rnd} (hR : R.Sound) {D : Iv} {d : ℝ}
    (hD : D.Mem d) (hd : 0 < d ∧ d < π / 2) {X : Fin 3 → Iv} {x : Fin 3 → ℝ}
    (hX : ∀ j, ∃ ul uh, X j = Iv.ofReal ul uh ∧ 0 < ul ∧ uh < 2 * π ∧ ul ≤ x j ∧ x j ≤ uh) :
    (hexEvalC R D X 0).Mem (bangle d (x 2) +
        gam (ebase d (x 1)) (ebase d (x 0)) (ebase d (x 2)) + bangle d (x 0)) ∧
      (hexEvalC R D X 1).Mem (bangle d (x 0) +
        gam (ebase d (x 2)) (ebase d (x 0)) (ebase d (x 1)) + bangle d (x 1)) ∧
      (hexEvalC R D X 2).Mem (bangle d (x 1) +
        gam (ebase d (x 0)) (ebase d (x 1)) (ebase d (x 2)) + bangle d (x 2)) := by
  rcases hX 0 with ⟨ul0, uh0, hX0_eq, h0_lt, h_uh0_lt, h_ul0_le_x0, h_x0_le_uh0⟩
  rcases hX 1 with ⟨ul1, uh1, hX1_eq, h1_lt, h_uh1_lt, h_ul1_le_x1, h_x1_le_uh1⟩
  rcases hX 2 with ⟨ul2, uh2, hX2_eq, h2_lt, h_uh2_lt, h_ul2_le_x2, h_x2_le_uh2⟩
  have hM0 : (X 0).Mem (x 0) := by
    rw [hX0_eq]
    exact Iv.mem_ofReal.mpr ⟨h_ul0_le_x0, h_x0_le_uh0⟩
  have hM1 : (X 1).Mem (x 1) := by
    rw [hX1_eq]
    exact Iv.mem_ofReal.mpr ⟨h_ul1_le_x1, h_x1_le_uh1⟩
  have hM2 : (X 2).Mem (x 2) := by
    rw [hX2_eq]
    exact Iv.mem_ofReal.mpr ⟨h_ul2_le_x2, h_x2_le_uh2⟩
  have hb1 : (isoAngle R (Iv.ofReal ul0 uh0) D).Mem (bangle d (x 0)) :=
    isoAngle_mem hR ⟨h_ul0_le_x0, h_x0_le_uh0⟩ h0_lt h_uh0_lt hD hd
  have hb3 : (isoAngle R (Iv.ofReal ul1 uh1) D).Mem (bangle d (x 1)) :=
    isoAngle_mem hR ⟨h_ul1_le_x1, h_x1_le_uh1⟩ h1_lt h_uh1_lt hD hd
  have hb5 : (isoAngle R (Iv.ofReal ul2 uh2) D).Mem (bangle d (x 2)) :=
    isoAngle_mem hR ⟨h_ul2_le_x2, h_x2_le_uh2⟩ h2_lt h_uh2_lt hD hd
  have he1 : (isoBase R (X 0) D).Mem (ebase d (x 0)) := isoBase_mem hR hM0 hD
  have he3 : (isoBase R (X 1) D).Mem (ebase d (x 1)) := isoBase_mem hR hM1 hD
  have he5 : (isoBase R (X 2) D).Mem (ebase d (x 2)) := isoBase_mem hR hM2 hD
  have hg0 : (triAngleC R (isoBase R (X 1) D) (isoBase R (X 0) D) (isoBase R (X 2) D)).Mem
      (gam (ebase d (x 1)) (ebase d (x 0)) (ebase d (x 2))) :=
    triAngleC_mem hR he3 he1 he5
  have hg1 : (triAngleC R (isoBase R (X 2) D) (isoBase R (X 0) D) (isoBase R (X 1) D)).Mem
      (gam (ebase d (x 2)) (ebase d (x 0)) (ebase d (x 1))) :=
    triAngleC_mem hR he5 he1 he3
  have hg2 : (triAngleC R (isoBase R (X 0) D) (isoBase R (X 1) D) (isoBase R (X 2) D)).Mem
      (gam (ebase d (x 0)) (ebase d (x 1)) (ebase d (x 2))) :=
    triAngleC_mem hR he1 he3 he5
  have hb1' : (isoAngle R (X 0) D).Mem (bangle d (x 0)) := by rw [hX0_eq]; exact hb1
  have hb3' : (isoAngle R (X 1) D).Mem (bangle d (x 1)) := by rw [hX1_eq]; exact hb3
  have hb5' : (isoAngle R (X 2) D).Mem (bangle d (x 2)) := by rw [hX2_eq]; exact hb5
  unfold hexEvalC
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  refine ⟨?_, ?_, ?_⟩
  · have h_inner : (R.add (isoAngle R (X 2) D) (triAngleC R (isoBase R (X 1) D) (isoBase R (X 0) D) (isoBase R (X 2) D))).Mem
      (bangle d (x 2) + gam (ebase d (x 1)) (ebase d (x 0)) (ebase d (x 2))) :=
      hR.add (isoAngle R (X 2) D) (triAngleC R (isoBase R (X 1) D) (isoBase R (X 0) D) (isoBase R (X 2) D))
        (bangle d (x 2)) (gam (ebase d (x 1)) (ebase d (x 0)) (ebase d (x 2))) hb5' hg0
    exact hR.add (R.add (isoAngle R (X 2) D) (triAngleC R (isoBase R (X 1) D) (isoBase R (X 0) D) (isoBase R (X 2) D)))
      (isoAngle R (X 0) D) (bangle d (x 2) + gam (ebase d (x 1)) (ebase d (x 0)) (ebase d (x 2)))
      (bangle d (x 0)) h_inner hb1'
  · have h_inner : (R.add (isoAngle R (X 0) D) (triAngleC R (isoBase R (X 2) D) (isoBase R (X 0) D) (isoBase R (X 1) D))).Mem
      (bangle d (x 0) + gam (ebase d (x 2)) (ebase d (x 0)) (ebase d (x 1))) :=
      hR.add (isoAngle R (X 0) D) (triAngleC R (isoBase R (X 2) D) (isoBase R (X 0) D) (isoBase R (X 1) D))
        (bangle d (x 0)) (gam (ebase d (x 2)) (ebase d (x 0)) (ebase d (x 1))) hb1' hg1
    exact hR.add (R.add (isoAngle R (X 0) D) (triAngleC R (isoBase R (X 2) D) (isoBase R (X 0) D) (isoBase R (X 1) D)))
      (isoAngle R (X 1) D) (bangle d (x 0) + gam (ebase d (x 2)) (ebase d (x 0)) (ebase d (x 1)))
      (bangle d (x 1)) h_inner hb3'
  · have h_inner : (R.add (isoAngle R (X 1) D) (triAngleC R (isoBase R (X 0) D) (isoBase R (X 1) D) (isoBase R (X 2) D))).Mem
      (bangle d (x 1) + gam (ebase d (x 0)) (ebase d (x 1)) (ebase d (x 2))) :=
      hR.add (isoAngle R (X 1) D) (triAngleC R (isoBase R (X 0) D) (isoBase R (X 1) D) (isoBase R (X 2) D))
        (bangle d (x 1)) (gam (ebase d (x 0)) (ebase d (x 1)) (ebase d (x 2))) hb3' hg2
    exact hR.add (R.add (isoAngle R (X 1) D) (triAngleC R (isoBase R (X 0) D) (isoBase R (X 1) D) (isoBase R (X 2) D)))
      (isoAngle R (X 2) D) (bangle d (x 1) + gam (ebase d (x 0)) (ebase d (x 1)) (ebase d (x 2)))
      (bangle d (x 2)) h_inner hb5'

theorem fanOpp_monotoneOn_Icc {d a b lo hi : ℝ}
    (hd : 0 < d ∧ d < π / 2) (ha : 0 < a ∧ a < π) (hb : 0 < b ∧ b < π) (hlo : 0 < lo) :
    MonotoneOn (fun u => gam (ebase d u) a b) (Set.Icc lo (min hi π)) := by
  have hmono : MonotoneOn (fun u => gam (ebase d u) a b) (Set.Ioc 0 π) :=
    fanOpp_monotoneOn hd ha hb
  refine hmono.mono ?_
  intro u hu
  rcases hu with ⟨hulo, huhi⟩
  have hulo' : 0 < u := lt_of_lt_of_le hlo hulo
  have huhi' : u ≤ π := le_trans huhi (min_le_right _ _)
  exact ⟨hulo', huhi'⟩

theorem gam_swap (g e f : ℝ) : gam g e f = gam g f e := by
  unfold gam
  rw [eta_swap]

/-! Assembly. -/

/-- deep.rs `dec_dir` at `-1` on the box of a corner: the fan is non-increasing there. -/
theorem fanBox_anti {R : Rnd} (hR : R.Sound) {lo hi d b c : ℝ} {D X : Iv}
    (hlo : 0 < lo) (hhi : hi < 2 * π) (hD : D.Mem d) (hd : 0 < d ∧ d < π / 2)
    (hb : 0 < b ∧ b < π) (hc : 0 < c ∧ c < π)
    (hx : ∀ u ∈ Set.Icc lo (min hi π), X.Mem (gam b (ebase d u) c))
    (hdir : decDir R (Iv.ofReal lo hi) (R.add (isoAngle R (Iv.ofReal lo hi) D) X) X D = -1) :
    AntitoneOn (fun u => bangle d u + gam c (ebase d u) b) (Set.Icc lo (min hi π)) :=
  fan_anti_of_decDir hR hlo hD hd hb hc
    (fun u hu => hR.add _ _ _ _
      (isoAngle_mem hR ⟨hu.1, hu.2.trans (min_le_left _ _)⟩ hlo hhi hD hd) (hx u hu))
    hx hdir

/-- The narrowing of three corners in a row keeps a point that each enclosure holds. -/
theorem nar3_sound {ι : Type} {B : Box ι} {x : ι → ℝ} (hx : B.Mem x) {j₁ j₂ j₃ : ι}
    {n₁ n₂ n₃ : Iv} (h₁ : n₁.Mem (x j₁)) (h₂ : n₂.Mem (x j₂)) (h₃ : n₃.Mem (x j₃)) :
    ∃ B', ((nar B j₁ n₁).bind fun B₁ => (nar B₁ j₂ n₂).bind fun B₂ => nar B₂ j₃ n₃) = some B' ∧
      B'.Mem x := by
  obtain ⟨B₁, hB₁, hm₁⟩ := nar_sound hx j₁ h₁
  obtain ⟨B₂, hB₂, hm₂⟩ := nar_sound hm₁ j₂ h₂
  obtain ⟨B₃, hB₃, hm₃⟩ := nar_sound hm₂ j₃ h₃
  exact ⟨B₃, by simp only [hB₁, hB₂, hB₃, Option.bind], hm₃⟩

/-- The facts on the corners of a face used by its fan. -/
theorem face_facts {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H)
    {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A)) (e : P.G.Dart) (j : ℕ) :
    (ivOf B (fv e j)).Mem (A.fc e j) ∧ 0 < B.lo (fv e j) ∧ B.hi (fv e j) < 2 * π ∧
      B.lo (fv e j) ≤ B.hi (fv e j) ∧ B.lo (fv e j) ≤ A.fc e j ∧
      A.fc e j ≤ min (B.hi (fv e j)) π := by
  have h := ivOf_mem hm (fv e j)
  rw [val_fv hA] at h
  obtain ⟨h1, h2, -⟩ := dom_fv hB e j
  obtain ⟨h3, h4⟩ := fv_mem hA hm e j
  have h5 := (hA.2.2.corner_mem ((P.R.face ^ j) e)).2
  exact ⟨h, by linarith, by linarith [Real.pi_gt_three], h3.trans h4, h3,
    le_min h4 h5.le⟩

/-- A point of the box of a corner, up to `π`. -/
theorem box_facts {B : Box (PVar P k)} {v : PVar P k} {d u : ℝ} (hd : 0 < d ∧ d < π / 2)
    (hlo : 0 < B.lo v) (hu : u ∈ Set.Icc (B.lo v) (min (B.hi v) π)) :
    (ivOf B v).Mem u ∧ 0 < ebase d u ∧ ebase d u < π :=
  ⟨Iv.mem_ofReal.mpr ⟨hu.1, hu.2.trans (min_le_left _ _)⟩,
    ebase_mem_Ioo d u hd ⟨hlo.trans_le hu.1, hu.2.trans (min_le_right _ _)⟩⟩

theorem fin2_forall {p : Fin 2 → Prop} (h0 : p 0) (h1 : p 1) : ∀ j, p j := by
  intro j; fin_cases j
  · exact h0
  · exact h1

theorem fin3_forall {p : Fin 3 → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) : ∀ j, p j := by
  intro j; fin_cases j
  · exact h0
  · exact h1
  · exact h2

theorem pentStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A))
    {e : P.G.Dart} (he : fsize P e = 5) :
    ∃ B', pentStep R B e = some B' ∧ B'.Mem (PVar.val A) := by
  have hR' : RelSys P H A := hA.2.2
  have hd := d_pos_lt hB hm
  have hdπ : 0 < A.d ∧ A.d < π := ⟨hd.1, by linarith [Real.pi_pos, hd.2]⟩
  have hDm : (ivOf B .d).Mem A.d := ivOf_mem hm .d
  obtain ⟨hη1, hη2, hη3, hu0, hu2, hu3⟩ := hR'.pent e he
  obtain ⟨hm1, hlo1, hhi1, hlh1, hx1l, hx1h⟩ := face_facts hA hB hm e 1
  obtain ⟨hm4, hlo4, hhi4, hlh4, hx4l, hx4h⟩ := face_facts hA hB hm e 4
  have hee := isoBase_mem hR hm1 hDm
  have hff := isoBase_mem hR hm4 hDm
  obtain ⟨gi, hgi, hgim⟩ := triAngle_of_eta hR hDm hee hff hη1
  obtain ⟨gp, hgp, hgpm⟩ := triAngle_of_eta hR hff hee hDm hη2
  obtain ⟨gm, hgm, hgmm⟩ := triAngle_of_eta hR hee hff hDm hη3
  have hb1 : (isoAngle R (ivOf B (fv e 1)) (ivOf B .d)).Mem (bangle A.d (A.fc e 1)) :=
    isoAngle_mem hR ⟨hx1l, hx1h.trans (min_le_left _ _)⟩ hlo1 hhi1 hDm hd
  have hb3 : (isoAngle R (ivOf B (fv e 4)) (ivOf B .d)).Mem (bangle A.d (A.fc e 4)) :=
    isoAngle_mem hR ⟨hx4l, hx4h.trans (min_le_left _ _)⟩ hlo4 hhi4 hDm hd
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  -- the hypotheses of `monoBounds_mem` common to the three outputs
  have hU : ∀ j, (![B.lo (fv e 1), B.lo (fv e 4)] : Fin 2 → ℝ) j ≤ (![A.fc e 1, A.fc e 4] : Fin 2 → ℝ) j ∧
      (![A.fc e 1, A.fc e 4] : Fin 2 → ℝ) j ≤
        (![min (B.hi (fv e 1)) π, min (B.hi (fv e 4)) π] : Fin 2 → ℝ) j := by
    refine fin2_forall ?_ ?_
    · exact ⟨hx1l, hx1h⟩
    · exact ⟨hx4l, hx4h⟩
  have hinp : ∀ j t, (![B.lo (fv e 1), B.lo (fv e 4)] : Fin 2 → ℝ) j ≤ t →
      t ≤ (![min (B.hi (fv e 1)) π, min (B.hi (fv e 4)) π] : Fin 2 → ℝ) j →
        Iv.Mem ((![ivOf B (fv e 1), ivOf B (fv e 4)] : Fin 2 → Iv) j) t := by
    refine fin2_forall ?_ ?_
    · exact fun t h1 h2 => Iv.mem_ofReal.mpr ⟨h1, h2.trans (min_le_left _ _)⟩
    · exact fun t h1 h2 => Iv.mem_ofReal.mpr ⟨h1, h2.trans (min_le_left _ _)⟩
  have hend1 : ∀ j t, (![B.lo (fv e 1), B.lo (fv e 4)] : Fin 2 → ℝ) j ≤ t →
      t ≤ (![min (B.hi (fv e 1)) π, min (B.hi (fv e 4)) π] : Fin 2 → ℝ) j →
        ∃ w, (![B.lo (fv e 1), B.lo (fv e 4)] : Fin 2 → ℝ) j ≤ w ∧ w ≤ t ∧
          ((![cornerEnds R (ivOf B (fv e 1)), cornerEnds R (ivOf B (fv e 4))] :
            Fin 2 → Iv × Iv) j).1.Mem w := by
    refine fin2_forall ?_ ?_
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).1
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).1
  have hend2 : ∀ j t, (![B.lo (fv e 1), B.lo (fv e 4)] : Fin 2 → ℝ) j ≤ t →
      t ≤ (![min (B.hi (fv e 1)) π, min (B.hi (fv e 4)) π] : Fin 2 → ℝ) j →
        ∃ w, t ≤ w ∧ w ≤ (![min (B.hi (fv e 1)) π, min (B.hi (fv e 4)) π] : Fin 2 → ℝ) j ∧
          ((![cornerEnds R (ivOf B (fv e 1)), cornerEnds R (ivOf B (fv e 4))] :
            Fin 2 → Iv × Iv) j).2.Mem w := by
    refine fin2_forall ?_ ?_
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).2
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).2
  have hX : ∀ (X : Fin 2 → Iv) (x : Fin 2 → ℝ),
      (∀ j, X j = (![ivOf B (fv e 1), ivOf B (fv e 4)] : Fin 2 → Iv) j ∨
        X j = ((![cornerEnds R (ivOf B (fv e 1)), cornerEnds R (ivOf B (fv e 4))] :
          Fin 2 → Iv × Iv) j).1 ∨
        X j = ((![cornerEnds R (ivOf B (fv e 1)), cornerEnds R (ivOf B (fv e 4))] :
          Fin 2 → Iv × Iv) j).2) → (∀ j, (X j).Mem (x j)) →
      ∀ j, ∃ ul uh, X j = Iv.ofReal ul uh ∧ 0 < ul ∧ uh < 2 * π ∧ ul ≤ x j ∧ x j ≤ uh := by
    intro X x hsel hmem
    refine fin2_forall ?_ ?_
    · exact ends_form R hlo1 hlh1 hhi1 (hsel 0) (hmem 0)
    · exact ends_form R hlo4 hlh4 hhi4 (hsel 1) (hmem 1)
  -- the enclosures at every point of the boxes
  have hbox1 := fun u (hu : u ∈ Set.Icc (B.lo (fv e 1)) (min (B.hi (fv e 1)) π)) =>
    box_facts (d := A.d) hd hlo1 hu
  have hbox4 := fun u (hu : u ∈ Set.Icc (B.lo (fv e 4)) (min (B.hi (fv e 4)) π)) =>
    box_facts (d := A.d) hd hlo4 hu
  unfold pentStep
  simp only [hgi, hgp, hgm]
  refine nar3_sound hm (meet_mem ?_ ?_) (meet_mem ?_ ?_) (meet_mem ?_ ?_)
  · rw [val_fv hA, hu0]
    exact hR.add _ _ _ _ (hR.add _ _ _ _ hb1 hgim) hb3
  · rw [val_fv hA, hu0]
    refine monoBounds_mem _ _ _ _ 0
      (fun x => bangle A.d (x 0) + gam A.d (ebase A.d (x 0)) (ebase A.d (x 1)) + bangle A.d (x 1))
      ![B.lo (fv e 1), B.lo (fv e 4)] ![min (B.hi (fv e 1)) π, min (B.hi (fv e 4)) π]
      ![A.fc e 1, A.fc e 4] hU
      (fun X x hsel hmem _ => (pentEvalC_mem hR hDm hd (hX X x hsel hmem)).1)
      hinp hend1 hend2 ?_ ?_
    · refine fin2_forall ?_ ?_
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
    · refine fin2_forall ?_ ?_
      · intro hj x hx
        have hF := fanBox_anti hR hlo1 hhi1 hDm hd (hbox4 (x 1) (hx 1)).2 hdπ
          (fun u hu => triAngle_mem_of_some hR hgp (isoBase_mem hR (hbox4 (x 1) (hx 1)).1 hDm)
            (isoBase_mem hR (hbox1 u hu).1 hDm) hDm) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h10]
        linarith
      · intro hj x hx
        have hF := fanBox_anti hR hlo4 hhi4 hDm hd (hbox1 (x 0) (hx 0)).2 hdπ
          (fun u hu => triAngle_mem_of_some hR hgm (isoBase_mem hR (hbox1 (x 0) (hx 0)).1 hDm)
            (isoBase_mem hR (hbox4 u hu).1 hDm) hDm) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h01]
        rw [gam_swap A.d (ebase A.d (x 0)) (ebase A.d a),
          gam_swap A.d (ebase A.d (x 0)) (ebase A.d b)]
        linarith
  · rw [val_fv hA, hu2]
    exact hR.add _ _ _ _ hb1 hgpm
  · rw [val_fv hA, hu2]
    refine monoBounds_mem _ _ _ _ 1
      (fun x => bangle A.d (x 0) + gam (ebase A.d (x 1)) (ebase A.d (x 0)) A.d)
      ![B.lo (fv e 1), B.lo (fv e 4)] ![min (B.hi (fv e 1)) π, min (B.hi (fv e 4)) π]
      ![A.fc e 1, A.fc e 4] hU
      (fun X x hsel hmem _ => (pentEvalC_mem hR hDm hd (hX X x hsel hmem)).2.1)
      hinp hend1 hend2 ?_ ?_
    · refine fin2_forall ?_ ?_
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
      · intro _ x hx
        have hF := fanOpp_monotoneOn_Icc (hi := B.hi (fv e 4)) hd (hbox1 (x 0) (hx 0)).2 hdπ hlo4
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h01]
        linarith
    · refine fin2_forall ?_ ?_
      · intro hj x hx
        have hF := fanBox_anti hR hlo1 hhi1 hDm hd hdπ (hbox4 (x 1) (hx 1)).2
          (fun u hu => triAngle_mem_of_some hR hgi hDm (isoBase_mem hR (hbox1 u hu).1 hDm)
            (isoBase_mem hR (hbox4 (x 1) (hx 1)).1 hDm)) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h10]
        linarith
      · exact fun hj => absurd hj (by norm_num)
  · rw [val_fv hA, hu3]
    exact hR.add _ _ _ _ hb3 hgmm
  · rw [val_fv hA, hu3]
    refine monoBounds_mem _ _ _ _ 2
      (fun x => bangle A.d (x 1) + gam (ebase A.d (x 0)) (ebase A.d (x 1)) A.d)
      ![B.lo (fv e 1), B.lo (fv e 4)] ![min (B.hi (fv e 1)) π, min (B.hi (fv e 4)) π]
      ![A.fc e 1, A.fc e 4] hU
      (fun X x hsel hmem _ => (pentEvalC_mem hR hDm hd (hX X x hsel hmem)).2.2)
      hinp hend1 hend2 ?_ ?_
    · refine fin2_forall ?_ ?_
      · intro _ x hx
        have hF := fanOpp_monotoneOn_Icc (hi := B.hi (fv e 1)) hd (hbox4 (x 1) (hx 1)).2 hdπ hlo1
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h10]
        linarith
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
    · refine fin2_forall ?_ ?_
      · exact fun hj => absurd hj (by norm_num)
      · intro hj x hx
        have hF := fanBox_anti hR hlo4 hhi4 hDm hd hdπ (hbox1 (x 0) (hx 0)).2
          (fun u hu => by
            rw [gam_swap]
            exact triAngle_mem_of_some hR hgi hDm (isoBase_mem hR (hbox1 (x 0) (hx 0)).1 hDm)
              (isoBase_mem hR (hbox4 u hu).1 hDm)) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h01]
        linarith

theorem hexStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A))
    {e : P.G.Dart} (he : fsize P e = 6) :
    ∃ B', hexStep R B e = some B' ∧ B'.Mem (PVar.val A) := by
  have hR' : RelSys P H A := hA.2.2
  have hd := d_pos_lt hB hm
  have hdπ : 0 < A.d ∧ A.d < π := ⟨hd.1, by linarith [Real.pi_pos, hd.2]⟩
  have hDm : (ivOf B .d).Mem A.d := ivOf_mem hm .d
  obtain ⟨hη0, hη2, hη4, hu0, hu2, hu4⟩ := hR'.hex e he
  obtain ⟨hm1, hlo1, hhi1, hlh1, hx1l, hx1h⟩ := face_facts hA hB hm e 1
  obtain ⟨hm3, hlo3, hhi3, hlh3, hx3l, hx3h⟩ := face_facts hA hB hm e 3
  obtain ⟨hm5, hlo5, hhi5, hlh5, hx5l, hx5h⟩ := face_facts hA hB hm e 5
  have he1 := isoBase_mem hR hm1 hDm
  have he3 := isoBase_mem hR hm3 hDm
  have he5 := isoBase_mem hR hm5 hDm
  obtain ⟨g0, hg0, hg0m⟩ := triAngle_of_eta hR he3 he1 he5 hη0
  obtain ⟨g2, hg2, hg2m⟩ := triAngle_of_eta hR he5 he1 he3 hη2
  obtain ⟨g4, hg4, hg4m⟩ := triAngle_of_eta hR he1 he3 he5 hη4
  have hb1 : (isoAngle R (ivOf B (fv e 1)) (ivOf B .d)).Mem (bangle A.d (A.fc e 1)) :=
    isoAngle_mem hR ⟨hx1l, hx1h.trans (min_le_left _ _)⟩ hlo1 hhi1 hDm hd
  have hb3 : (isoAngle R (ivOf B (fv e 3)) (ivOf B .d)).Mem (bangle A.d (A.fc e 3)) :=
    isoAngle_mem hR ⟨hx3l, hx3h.trans (min_le_left _ _)⟩ hlo3 hhi3 hDm hd
  have hb5 : (isoAngle R (ivOf B (fv e 5)) (ivOf B .d)).Mem (bangle A.d (A.fc e 5)) :=
    isoAngle_mem hR ⟨hx5l, hx5h.trans (min_le_left _ _)⟩ hlo5 hhi5 hDm hd
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  -- the hypotheses of `monoBounds_mem` common to the three outputs
  have hU : ∀ j, (![B.lo (fv e 1), B.lo (fv e 3), B.lo (fv e 5)] : Fin 3 → ℝ) j ≤
      (![A.fc e 1, A.fc e 3, A.fc e 5] : Fin 3 → ℝ) j ∧
      (![A.fc e 1, A.fc e 3, A.fc e 5] : Fin 3 → ℝ) j ≤
        (![min (B.hi (fv e 1)) π, min (B.hi (fv e 3)) π, min (B.hi (fv e 5)) π] : Fin 3 → ℝ) j := by
    refine fin3_forall ?_ ?_ ?_
    · exact ⟨hx1l, hx1h⟩
    · exact ⟨hx3l, hx3h⟩
    · exact ⟨hx5l, hx5h⟩
  have hinp : ∀ j t, (![B.lo (fv e 1), B.lo (fv e 3), B.lo (fv e 5)] : Fin 3 → ℝ) j ≤ t →
      t ≤ (![min (B.hi (fv e 1)) π, min (B.hi (fv e 3)) π, min (B.hi (fv e 5)) π] :
        Fin 3 → ℝ) j →
        Iv.Mem ((![ivOf B (fv e 1), ivOf B (fv e 3), ivOf B (fv e 5)] : Fin 3 → Iv) j) t := by
    refine fin3_forall ?_ ?_ ?_
    · exact fun t h1 h2 => Iv.mem_ofReal.mpr ⟨h1, h2.trans (min_le_left _ _)⟩
    · exact fun t h1 h2 => Iv.mem_ofReal.mpr ⟨h1, h2.trans (min_le_left _ _)⟩
    · exact fun t h1 h2 => Iv.mem_ofReal.mpr ⟨h1, h2.trans (min_le_left _ _)⟩
  have hend1 : ∀ j t, (![B.lo (fv e 1), B.lo (fv e 3), B.lo (fv e 5)] : Fin 3 → ℝ) j ≤ t →
      t ≤ (![min (B.hi (fv e 1)) π, min (B.hi (fv e 3)) π, min (B.hi (fv e 5)) π] :
        Fin 3 → ℝ) j →
        ∃ w, (![B.lo (fv e 1), B.lo (fv e 3), B.lo (fv e 5)] : Fin 3 → ℝ) j ≤ w ∧ w ≤ t ∧
          ((![cornerEnds R (ivOf B (fv e 1)), cornerEnds R (ivOf B (fv e 3)),
            cornerEnds R (ivOf B (fv e 5))] : Fin 3 → Iv × Iv) j).1.Mem w := by
    refine fin3_forall ?_ ?_ ?_
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).1
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).1
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).1
  have hend2 : ∀ j t, (![B.lo (fv e 1), B.lo (fv e 3), B.lo (fv e 5)] : Fin 3 → ℝ) j ≤ t →
      t ≤ (![min (B.hi (fv e 1)) π, min (B.hi (fv e 3)) π, min (B.hi (fv e 5)) π] :
        Fin 3 → ℝ) j →
        ∃ w, t ≤ w ∧ w ≤ (![min (B.hi (fv e 1)) π, min (B.hi (fv e 3)) π,
            min (B.hi (fv e 5)) π] : Fin 3 → ℝ) j ∧
          ((![cornerEnds R (ivOf B (fv e 1)), cornerEnds R (ivOf B (fv e 3)),
            cornerEnds R (ivOf B (fv e 5))] : Fin 3 → Iv × Iv) j).2.Mem w := by
    refine fin3_forall ?_ ?_ ?_
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).2
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).2
    · exact fun t h1 h2 => (cornerEnds_spec hR ⟨h1, h2⟩).2
  have hX : ∀ (X : Fin 3 → Iv) (x : Fin 3 → ℝ),
      (∀ j, X j = (![ivOf B (fv e 1), ivOf B (fv e 3), ivOf B (fv e 5)] : Fin 3 → Iv) j ∨
        X j = ((![cornerEnds R (ivOf B (fv e 1)), cornerEnds R (ivOf B (fv e 3)),
          cornerEnds R (ivOf B (fv e 5))] : Fin 3 → Iv × Iv) j).1 ∨
        X j = ((![cornerEnds R (ivOf B (fv e 1)), cornerEnds R (ivOf B (fv e 3)),
          cornerEnds R (ivOf B (fv e 5))] : Fin 3 → Iv × Iv) j).2) → (∀ j, (X j).Mem (x j)) →
      ∀ j, ∃ ul uh, X j = Iv.ofReal ul uh ∧ 0 < ul ∧ uh < 2 * π ∧ ul ≤ x j ∧ x j ≤ uh := by
    intro X x hsel hmem
    refine fin3_forall ?_ ?_ ?_
    · exact ends_form R hlo1 hlh1 hhi1 (hsel 0) (hmem 0)
    · exact ends_form R hlo3 hlh3 hhi3 (hsel 1) (hmem 1)
    · exact ends_form R hlo5 hlh5 hhi5 (hsel 2) (hmem 2)
  -- the enclosures at every point of the boxes
  have hbox1 := fun u (hu : u ∈ Set.Icc (B.lo (fv e 1)) (min (B.hi (fv e 1)) π)) =>
    box_facts (d := A.d) hd hlo1 hu
  have hbox3 := fun u (hu : u ∈ Set.Icc (B.lo (fv e 3)) (min (B.hi (fv e 3)) π)) =>
    box_facts (d := A.d) hd hlo3 hu
  have hbox5 := fun u (hu : u ∈ Set.Icc (B.lo (fv e 5)) (min (B.hi (fv e 5)) π)) =>
    box_facts (d := A.d) hd hlo5 hu
  unfold hexStep
  simp only [hg0, hg2, hg4]
  refine nar3_sound hm (meet_mem ?_ ?_) (meet_mem ?_ ?_) (meet_mem ?_ ?_)
  · rw [val_fv hA, hu0]
    exact hR.add _ _ _ _ (hR.add _ _ _ _ hb5 hg0m) hb1
  · rw [val_fv hA, hu0]
    refine monoBounds_mem _ _ _ _ 0
      (fun x => bangle A.d (x 2) + gam (ebase A.d (x 1)) (ebase A.d (x 0)) (ebase A.d (x 2)) +
        bangle A.d (x 0))
      ![B.lo (fv e 1), B.lo (fv e 3), B.lo (fv e 5)]
      ![min (B.hi (fv e 1)) π, min (B.hi (fv e 3)) π, min (B.hi (fv e 5)) π]
      ![A.fc e 1, A.fc e 3, A.fc e 5] hU
      (fun X x hsel hmem _ => (hexEvalC_mem hR hDm hd (hX X x hsel hmem)).1)
      hinp hend1 hend2 ?_ ?_
    · refine fin3_forall ?_ ?_ ?_
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
      · intro _ x hx
        have hF := fanOpp_monotoneOn_Icc (hi := B.hi (fv e 3)) hd (hbox1 (x 0) (hx 0)).2
          (hbox5 (x 2) (hx 2)).2 hlo3
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h01, Function.update_of_ne h21]
        linarith
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
    · refine fin3_forall ?_ ?_ ?_
      · intro hj x hx
        have hF := fanBox_anti hR hlo1 hhi1 hDm hd (hbox5 (x 2) (hx 2)).2 (hbox3 (x 1) (hx 1)).2
          (fun u hu => triAngle_mem_of_some hR hg2 (isoBase_mem hR (hbox5 (x 2) (hx 2)).1 hDm)
            (isoBase_mem hR (hbox1 u hu).1 hDm) (isoBase_mem hR (hbox3 (x 1) (hx 1)).1 hDm)) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h10, Function.update_of_ne h20]
        linarith
      · exact fun hj => absurd hj (by norm_num)
      · intro hj x hx
        have hF := fanBox_anti hR hlo5 hhi5 hDm hd (hbox1 (x 0) (hx 0)).2 (hbox3 (x 1) (hx 1)).2
          (fun u hu => by
            rw [gam_swap]
            exact triAngle_mem_of_some hR hg4 (isoBase_mem hR (hbox1 (x 0) (hx 0)).1 hDm)
              (isoBase_mem hR (hbox3 (x 1) (hx 1)).1 hDm) (isoBase_mem hR (hbox5 u hu).1 hDm)) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h02, Function.update_of_ne h12]
        rw [gam_swap (ebase A.d (x 1)) (ebase A.d (x 0)) (ebase A.d a),
          gam_swap (ebase A.d (x 1)) (ebase A.d (x 0)) (ebase A.d b)]
        linarith
  · rw [val_fv hA, hu2]
    exact hR.add _ _ _ _ (hR.add _ _ _ _ hb1 hg2m) hb3
  · rw [val_fv hA, hu2]
    refine monoBounds_mem _ _ _ _ 1
      (fun x => bangle A.d (x 0) + gam (ebase A.d (x 2)) (ebase A.d (x 0)) (ebase A.d (x 1)) +
        bangle A.d (x 1))
      ![B.lo (fv e 1), B.lo (fv e 3), B.lo (fv e 5)]
      ![min (B.hi (fv e 1)) π, min (B.hi (fv e 3)) π, min (B.hi (fv e 5)) π]
      ![A.fc e 1, A.fc e 3, A.fc e 5] hU
      (fun X x hsel hmem _ => (hexEvalC_mem hR hDm hd (hX X x hsel hmem)).2.1)
      hinp hend1 hend2 ?_ ?_
    · refine fin3_forall ?_ ?_ ?_
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
      · intro _ x hx
        have hF := fanOpp_monotoneOn_Icc (hi := B.hi (fv e 5)) hd (hbox1 (x 0) (hx 0)).2
          (hbox3 (x 1) (hx 1)).2 hlo5
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h02, Function.update_of_ne h12]
        linarith
    · refine fin3_forall ?_ ?_ ?_
      · intro hj x hx
        have hF := fanBox_anti hR hlo1 hhi1 hDm hd (hbox3 (x 1) (hx 1)).2 (hbox5 (x 2) (hx 2)).2
          (fun u hu => triAngle_mem_of_some hR hg0 (isoBase_mem hR (hbox3 (x 1) (hx 1)).1 hDm)
            (isoBase_mem hR (hbox1 u hu).1 hDm) (isoBase_mem hR (hbox5 (x 2) (hx 2)).1 hDm)) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h10, Function.update_of_ne h20]
        linarith
      · intro hj x hx
        have hF := fanBox_anti hR hlo3 hhi3 hDm hd (hbox1 (x 0) (hx 0)).2 (hbox5 (x 2) (hx 2)).2
          (fun u hu => triAngle_mem_of_some hR hg4 (isoBase_mem hR (hbox1 (x 0) (hx 0)).1 hDm)
            (isoBase_mem hR (hbox3 u hu).1 hDm) (isoBase_mem hR (hbox5 (x 2) (hx 2)).1 hDm)) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h01, Function.update_of_ne h21]
        rw [gam_swap (ebase A.d (x 2)) (ebase A.d (x 0)) (ebase A.d a),
          gam_swap (ebase A.d (x 2)) (ebase A.d (x 0)) (ebase A.d b)]
        linarith
      · exact fun hj => absurd hj (by norm_num)
  · rw [val_fv hA, hu4]
    exact hR.add _ _ _ _ (hR.add _ _ _ _ hb3 hg4m) hb5
  · rw [val_fv hA, hu4]
    refine monoBounds_mem _ _ _ _ 2
      (fun x => bangle A.d (x 1) + gam (ebase A.d (x 0)) (ebase A.d (x 1)) (ebase A.d (x 2)) +
        bangle A.d (x 2))
      ![B.lo (fv e 1), B.lo (fv e 3), B.lo (fv e 5)]
      ![min (B.hi (fv e 1)) π, min (B.hi (fv e 3)) π, min (B.hi (fv e 5)) π]
      ![A.fc e 1, A.fc e 3, A.fc e 5] hU
      (fun X x hsel hmem _ => (hexEvalC_mem hR hDm hd (hX X x hsel hmem)).2.2)
      hinp hend1 hend2 ?_ ?_
    · refine fin3_forall ?_ ?_ ?_
      · intro _ x hx
        have hF := fanOpp_monotoneOn_Icc (hi := B.hi (fv e 1)) hd (hbox3 (x 1) (hx 1)).2
          (hbox5 (x 2) (hx 2)).2 hlo1
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h10, Function.update_of_ne h20]
        linarith
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
      · exact fun hj => absurd hj (decDir_ne_one _ _ _ _ _)
    · refine fin3_forall ?_ ?_ ?_
      · exact fun hj => absurd hj (by norm_num)
      · intro hj x hx
        have hF := fanBox_anti hR hlo3 hhi3 hDm hd (hbox5 (x 2) (hx 2)).2 (hbox1 (x 0) (hx 0)).2
          (fun u hu => by
            rw [gam_swap]
            exact triAngle_mem_of_some hR hg2 (isoBase_mem hR (hbox5 (x 2) (hx 2)).1 hDm)
              (isoBase_mem hR (hbox1 (x 0) (hx 0)).1 hDm) (isoBase_mem hR (hbox3 u hu).1 hDm)) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h01, Function.update_of_ne h21]
        linarith
      · intro hj x hx
        have hF := fanBox_anti hR hlo5 hhi5 hDm hd (hbox3 (x 1) (hx 1)).2 (hbox1 (x 0) (hx 0)).2
          (fun u hu => by
            rw [gam_swap]
            exact triAngle_mem_of_some hR hg0 (isoBase_mem hR (hbox3 (x 1) (hx 1)).1 hDm)
              (isoBase_mem hR (hbox1 (x 0) (hx 0)).1 hDm) (isoBase_mem hR (hbox5 u hu).1 hDm)) hj
        intro a ha b hb hab
        have := hF ha hb hab
        simp only [Function.update_self, Function.update_of_ne h02, Function.update_of_ne h12]
        rw [gam_swap (ebase A.d (x 0)) (ebase A.d (x 1)) (ebase A.d a),
          gam_swap (ebase A.d (x 0)) (ebase A.d (x 1)) (ebase A.d b)]
        linarith

theorem diagFwdStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A))
    {e : P.G.Dart} (he : fsize P e = 6) :
    ∃ B', diagFwdStep R B e = some B' ∧ B'.Mem (PVar.val A) := by
  have hR' : RelSys P H A := hA.2.2
  have hd := d_pos_lt hB hm
  obtain ⟨hd1, hd2, hd3, hd4⟩ := d_mem hB hm
  obtain ⟨hx1, hx2, -⟩ := dom_fv hB e 0
  have hx := fv_mem hA hm e 0
  have hv : alpha A.d ≤ A.fc e 1 := (hR'.corner_mem ((P.R.face ^ 1) e)).1
  have hle := longDiag_le_corner ⟨hd1.trans hd2, hd3.trans hd4⟩ (by linarith [hx.1]) hx.2 hx2 hv
    (hR'.hexDiag e he).1
  have hlb := longdiagLb_le (ul := B.lo (fv e 0)) (uh := B.hi (fv e 0)) hR (ivOf_mem hm .d) hd
    ⟨by linarith [hx.1], by linarith [Real.pi_gt_three]⟩
  unfold diagFwdStep
  refine nar_sound hm (fv e 1) ?_
  rw [val_fv hA]
  exact ⟨Fl.le_trans hlb (Fl.ofReal_le_ofReal.mpr hle), Fl.le_inf _⟩

theorem diagBwdStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A))
    {e : P.G.Dart} (he : fsize P e = 6) :
    ∃ B', diagBwdStep R B e = some B' ∧ B'.Mem (PVar.val A) := by
  have hR' : RelSys P H A := hA.2.2
  have hd := d_pos_lt hB hm
  obtain ⟨hd1, hd2, hd3, hd4⟩ := d_mem hB hm
  obtain ⟨hx1, hx2, -⟩ := dom_fv hB e 1
  have hx := fv_mem hA hm e 1
  have hv : alpha A.d ≤ A.fc e 0 := (hR'.corner_mem ((P.R.face ^ 0) e)).1
  have hle := longDiag_le_corner ⟨hd1.trans hd2, hd3.trans hd4⟩ (by linarith [hx.1]) hx.2 hx2 hv
    (hR'.hexDiag e he).2
  have hlb := longdiagLb_le (ul := B.lo (fv e 1)) (uh := B.hi (fv e 1)) hR (ivOf_mem hm .d) hd
    ⟨by linarith [hx.1], by linarith [Real.pi_gt_three]⟩
  unfold diagBwdStep
  refine nar_sound hm (fv e 0) ?_
  rw [val_fv hA]
  exact ⟨Fl.le_trans hlb (Fl.ofReal_le_ofReal.mpr hle), Fl.le_inf _⟩

/-! ## The wheel -/

theorem gam_mem_Icc (g e f : ℝ) : 0 ≤ gam g e f ∧ gam g e f ≤ π :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- One turn of the wheel keeps the solutions. -/
theorem wheelTurn_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) (m : Fin k) {dl dh : ℝ} (hdl : dl ≤ A.d ∧ A.d ≤ dh) (hd0 : 0 ≤ dl)
    (hd1 : dh ≤ π) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A)) (i : Fin 6) :
    ∃ B', wheelTurn R H m (Iv.ofReal dl dh) B i = some B' ∧ B'.Mem (PVar.val A) := by
  obtain ⟨hW1, -, -, hW4, hW5⟩ := hA.2.2.wheel m
  have hdpos := d_pos_lt hB hm
  obtain ⟨-, -, hd3, hd4⟩ := d_mem hB hm
  have hrr : ∀ j, 0 < A.r m j ∧ A.r m j < π := fun j => by
    obtain ⟨h1, h2⟩ := hW1 j
    constructor <;> linarith [Real.pi_gt_three]
  have hD : (Iv.ofReal dl dh).Mem A.d := Iv.mem_ofReal.mpr hdl
  have hd' : 0 < A.d ∧ A.d < π := ⟨hdpos.1, by linarith [hdpos.2, Real.pi_pos]⟩
  have hr : ∀ j, (ivOf B (.r m j)).Mem (A.r m j) := fun j => ivOf_mem hm (.r m j)
  obtain ⟨a1, ha1, ha1m⟩ := triAngle_of_eta hR (hr (i + 1)) (hr i) hD (hW4 i).1
  obtain ⟨a2, ha2, ha2m⟩ := triAngle_of_eta hR (hr (i - 1)) (hr i) hD (hW4 i).2
  have hu : PVar.val A (fv (H.base m) i : PVar P k) =
      gam (A.r m (i + 1)) (A.r m i) A.d + gam (A.r m (i - 1)) (A.r m i) A.d := by
    rw [val_fv hA]
    exact hW5 i
  obtain ⟨B₂, hB₂, hm₂⟩ := nar_sound hm (fv (H.base m) i)
    (by rw [hu]; exact hR.add a1 a2 _ _ ha1m ha2m)
  have hu₂ : (ivOf B₂ (fv (H.base m) i)).Mem
      (gam (A.r m (i + 1)) (A.r m i) A.d + gam (A.r m (i - 1)) (A.r m i) A.d) := by
    have h := ivOf_mem hm₂ (fv (H.base m) i)
    rwa [hu] at h
  have hang1 : (R.sub (ivOf B₂ (fv (H.base m) i)) a2).Mem (gam (A.r m (i + 1)) (A.r m i) A.d) := by
    have h := hR.sub _ _ _ _ hu₂ ha2m
    simpa using h
  have hb : B.lo (.r m i) ≤ A.r m i ∧ A.r m i ≤ B.hi (.r m i) := hm (.r m i)
  obtain ⟨hB0, hB3⟩ := hB.2.2.2 m i
  obtain ⟨rp, hrp, hrpm⟩ := side_sound hR hb hdl (by linarith) (by linarith [Real.pi_gt_three])
    hd0 hd1 hang1 (gam_mem_Icc _ _ _).1 (gam_mem_Icc _ _ _).2 (hrr (i + 1)).1.le
    (hrr (i + 1)).2.le (cos_side_of_gam (hrr i) hd' (hW4 i).1)
  have hrp' : side R (ivOf B (.r m i)) (Iv.ofReal dl dh) (R.sub (ivOf B₂ (fv (H.base m) i)) a2) =
      some rp := hrp
  obtain ⟨B₃, hB₃, hm₃⟩ := nar_sound hm₂ (.r m (i + 1)) hrpm
  have hu₃ : (ivOf B₃ (fv (H.base m) i)).Mem
      (gam (A.r m (i + 1)) (A.r m i) A.d + gam (A.r m (i - 1)) (A.r m i) A.d) := by
    have h := ivOf_mem hm₃ (fv (H.base m) i)
    rwa [hu] at h
  have hang2 : (R.sub (ivOf B₃ (fv (H.base m) i)) a1).Mem (gam (A.r m (i - 1)) (A.r m i) A.d) := by
    have h := hR.sub _ _ _ _ hu₃ ha1m
    simpa using h
  obtain ⟨rm, hrm, hrmm⟩ := side_sound hR hb hdl (by linarith) (by linarith [Real.pi_gt_three])
    hd0 hd1 hang2 (gam_mem_Icc _ _ _).1 (gam_mem_Icc _ _ _).2 (hrr (i - 1)).1.le
    (hrr (i - 1)).2.le (cos_side_of_gam (hrr i) hd' (hW4 i).2)
  have hrm' : side R (ivOf B (.r m i)) (Iv.ofReal dl dh) (R.sub (ivOf B₃ (fv (H.base m) i)) a1) =
      some rm := hrm
  obtain ⟨B₄, hB₄, hm₄⟩ := nar_sound hm₃ (.r m (i - 1)) hrmm
  refine ⟨B₄, ?_, hm₄⟩
  unfold wheelTurn
  dsimp only
  simp only [ha1, ha2, hB₂, hrp', hB₃, hrm', hB₄, Option.bind]

/-- One turn of the wheel only shrinks the box. -/
theorem wheelTurn_subset {R : Rnd} {H : HexChoice P k} (m : Fin k) (d : Iv)
    {B B' : Box (PVar P k)} (i : Fin 6) (h : wheelTurn R H m d B i = some B') (v : PVar P k) :
    B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v := by
  unfold wheelTurn at h
  dsimp only at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨a1, -, a2, -, B₂, h2, rp, -, B₃, h3, rm, -, h4⟩ := h
  have s2 := nar_subset h2 v
  have s3 := nar_subset h3 v
  have s4 := nar_subset h4 v
  exact ⟨s2.1.trans (s3.1.trans s4.1), (s4.2.trans s3.2).trans s2.2⟩

theorem wheelStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A))
    (m : Fin k) :
    ∃ B', wheelStep R H m B = some B' ∧ B'.Mem (PVar.val A) := by
  obtain ⟨hW1, hW2, hW3, -, -⟩ := hA.2.2.wheel m
  obtain ⟨hd1, hd2, hd3, hd4⟩ := d_mem hB hm
  have hDm : (ivOf B .d).Mem A.d := ivOf_mem hm .d
  have h3 : (R.scale (ivOf B .d) 3).Mem (A.d * 3) := hR.mul _ _ _ _ hDm Iv.mem_pt
  obtain ⟨B₁, hB₁, hm₁, hs₁⟩ := foldlM_option_inv
    (fun B' i => nar B' (.r m i) ⟨(ivOf B .d).lo, (R.scale (ivOf B .d) 3).hi⟩)
    (fun B' => B'.Mem (PVar.val A) ∧ ∀ v, B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v) (List.finRange 6)
    (fun B' i _ ⟨hm', hs'⟩ => by
      have hI : (⟨(ivOf B .d).lo, (R.scale (ivOf B .d) 3).hi⟩ : Iv).Mem (A.r m i) :=
        ⟨Fl.le_trans hDm.1 (Fl.ofReal_le_ofReal.mpr (hW1 i).1),
          Fl.le_trans (Fl.ofReal_le_ofReal.mpr (by linarith [(hW1 i).2])) h3.2⟩
      obtain ⟨B'', h1, h2⟩ := nar_sound hm' (.r m i) hI
      exact ⟨B'', h1, h2, fun v =>
        ⟨(hs' v).1.trans (nar_subset h1 v).1, (nar_subset h1 v).2.trans (hs' v).2⟩⟩)
    B ⟨hm, fun v => ⟨le_rfl, le_rfl⟩⟩
  have hB₁D : DomOK B₁ := DomOK.mono hB hs₁
  obtain ⟨th, hth, hthm⟩ := mapM_option_forall2
    (fun i => triAngle R (ivOf B .d) (ivOf B₁ (.r m i)) (ivOf B₁ (.r m (i + 1))))
    (fun i I => I.Mem (gam A.d (A.r m i) (A.r m (i + 1)))) (List.finRange 6)
    (fun i _ => triAngle_of_eta hR hDm (ivOf_mem hm₁ (.r m i)) (ivOf_mem hm₁ (.r m (i + 1)))
      (hW2 i))
  have hsum := foldl_add_mem hR (fun i => gam A.d (A.r m i) (A.r m (i + 1))) (List.finRange 6) th
    hthm (Iv.pt (.ofReal 0)) 0 Iv.mem_pt
  have hS : ((List.finRange 6).map (fun i => gam A.d (A.r m i) (A.r m (i + 1)))).sum = 2 * π := by
    rw [← Fin.sum_univ_def]
    exact hW3
  rw [hS, zero_add] at hsum
  have hnot : ¬ (Fl.lt (th.foldl R.add (Iv.pt (.ofReal 0))).hi (.ofReal R.twoPiLo) ∨
      Fl.lt (.ofReal R.twoPiHi) (th.foldl R.add (Iv.pt (.ofReal 0))).lo) := by
    rintro (h | h)
    · exact Fl.not_lt_of_le (Fl.le_trans (Fl.ofReal_le_ofReal.mpr hR.twoPiLo) hsum.2) h
    · exact Fl.not_lt_of_le (Fl.le_trans hsum.1 (Fl.ofReal_le_ofReal.mpr hR.twoPiHi)) h
  obtain ⟨B₅, hB₅, hm₅, -⟩ := foldlM_option_inv (wheelTurn R H m (ivOf B .d))
    (fun B' => B'.Mem (PVar.val A) ∧ DomOK B') (List.finRange 6)
    (fun B' i _ ⟨hm', hD'⟩ => by
      obtain ⟨B'', h1, h2⟩ := wheelTurn_sound hR hA m ⟨hd2, hd3⟩ (by linarith)
        (by linarith [Real.pi_gt_three]) hD' hm' i
      exact ⟨B'', h1, h2, DomOK.mono hD' (wheelTurn_subset m _ i h1)⟩)
    B₁ ⟨hm₁, hB₁D⟩
  refine ⟨B₅, ?_, hm₅⟩
  unfold wheelStep
  dsimp only
  simp only [Option.bind_eq_some_iff]
  exact ⟨B₁, hB₁, th, hth, by simp only [hnot, ↓reduceIte]; exact hB₅⟩

theorem primStep_sound {R : Rnd} (hR : R.Sound) {H : HexChoice P k} {A : Assign P k}
    (hA : A ∈ Sol P H) {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A))
    {s : Prim P k} (hs : s.Allowed) :
    ∃ B', primStep R H s B = some B' ∧ B'.Mem (PVar.val A) := by
  cases s with
  | row r =>
    obtain ⟨h1, h2⟩ := sysRow_holds hA hs
    exact rowStep_sound hR r hm h1 h2
  | alpha => exact alphaStep_sound hR hA hB hm
  | alphaInv => exact alphaInvStep_sound hR hA hB hm
  | rho e => exact rhoStep_sound hR hA hB hm hs
  | rhoD e => exact rhoDStep_sound hR hA hB hm hs
  | pent e => exact pentStep_sound hR hA hB hm hs
  | hex e => exact hexStep_sound hR hA hB hm hs
  | diagFwd e => exact diagFwdStep_sound hR hA hB hm hs
  | diagBwd e => exact diagBwdStep_sound hR hA hB hm hs
  | wheel m => exact wheelStep_sound hR hA hB hm m

/-- Shrinking along a fold of steps that shrink. -/
theorem foldlM_subset {α : Type} (f : Box (PVar P k) → α → Option (Box (PVar P k)))
    (hf : ∀ B a B', f B a = some B' → ∀ v, B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v) (l : List α)
    {B B' : Box (PVar P k)} (h : l.foldlM f B = some B') (v : PVar P k) :
    B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v :=
  foldlM_option_rel f (fun B B' => B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v)
    (fun _ => ⟨le_rfl, le_rfl⟩) (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩)
    (fun B a B' h => hf B a B' h v) l B B' h

/-- Three narrowings in a row only shrink the box. -/
theorem nar3_subset {B B' : Box (PVar P k)} {j₁ j₂ j₃ : PVar P k} {n₁ n₂ n₃ : Iv}
    (h : ((nar B j₁ n₁).bind fun B₁ => (nar B₁ j₂ n₂).bind fun B₂ => nar B₂ j₃ n₃) = some B')
    (v : PVar P k) : B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v := by
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨B₁, h1, B₂, h2, h3⟩ := h
  have s1 := nar_subset h1 v
  have s2 := nar_subset h2 v
  have s3 := nar_subset h3 v
  exact ⟨s1.1.trans (s2.1.trans s3.1), (s3.2.trans s2.2).trans s1.2⟩

/-- Every primitive step only shrinks the box. -/
theorem primStep_subset {R : Rnd} (hR : R.Sound) (H : HexChoice P k) (s : Prim P k)
    {B B' : Box (PVar P k)} (h : primStep R H s B = some B') (v : PVar P k) :
    B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v := by
  cases s with
  | row r => exact rowStep_subset hR r h v
  | alpha => exact nar_subset h v
  | alphaInv => exact nar_subset h v
  | rho e => exact nar_subset h v
  | rhoD e =>
    simp only [primStep, rhoDStep, Option.bind_eq_some_iff] at h
    obtain ⟨I, -, h⟩ := h
    exact nar_subset h v
  | pent e =>
    simp only [primStep, pentStep] at h
    split at h
    · exact nar3_subset h v
    · cases h
  | hex e =>
    simp only [primStep, hexStep] at h
    split at h
    · exact nar3_subset h v
    · cases h
  | diagFwd e => exact nar_subset h v
  | diagBwd e => exact nar_subset h v
  | wheel m =>
    simp only [primStep, wheelStep, Option.bind_eq_some_iff] at h
    obtain ⟨B₁, h1, th, -, h2⟩ := h
    split_ifs at h2
    have s1 := foldlM_subset _ (fun B a B' h => nar_subset h) _ h1 v
    have s2 := foldlM_subset _ (fun B a B' h => wheelTurn_subset m _ a h) _ h2 v
    exact ⟨s1.1.trans s2.1, s2.2.trans s1.2⟩

/-! ## Statements: runs, procedures, the main theorem -/

theorem Run.sound {H : HexChoice P k} {B : Box (PVar P k)} {o : Option (Box (PVar P k))}
    (h : Run H B o) {A : Assign P k} (hA : A ∈ Sol P H) (hm : B.Mem (PVar.val A)) :
    ∃ B', o = some B' ∧ B'.Mem (PVar.val A) := by
  induction h with
  | stop B => exact ⟨B, rfl, hm⟩
  | step R hR s hs hB h _ ih =>
    obtain ⟨B'', h', hm''⟩ := primStep_sound hR hA hB hm hs
    rw [h] at h'
    cases h'
    exact ih hm''
  | kill R hR s hs hB h =>
    obtain ⟨B'', h', -⟩ := primStep_sound hR hA hB hm hs
    rw [h] at h'
    cases h'
  | cutLo v t ht _ _ ih₁ ih₂ =>
    rcases Box.mem_lower_or_upper _ v t hm with hl | hu
    · obtain ⟨_, h', -⟩ := ih₁ hl
      cases h'
    · exact ih₂ hu
  | cutHi v t ht _ _ ih₁ ih₂ =>
    rcases Box.mem_lower_or_upper _ v t hm with hl | hu
    · exact ih₂ hl
    · obtain ⟨_, h', -⟩ := ih₁ hu
      cases h'

theorem Run.subset {H : HexChoice P k} {B B' : Box (PVar P k)} (h : Run H B (some B'))
    (v : PVar P k) : B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v := by
  suffices ∀ o, Run H B o → ∀ B', o = some B' → B.lo v ≤ B'.lo v ∧ B'.hi v ≤ B.hi v from
    this _ h B' rfl
  clear h
  intro o h
  induction h with
  | stop B =>
    intro B' hB'
    cases hB'
    exact ⟨le_rfl, le_rfl⟩
  | step R hR s hs hB h _ ih =>
    intro B'' hB''
    have h₁ := primStep_subset hR H s h v
    have h₂ := ih B'' hB''
    exact ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
  | kill R hR s hs hB h =>
    intro B' hB'
    cases hB'
  | cutLo w t ht _ _ _ ih₂ =>
    intro B'' hB''
    have h₂ := ih₂ B'' hB''
    by_cases hw : v = w
    · subst hw
      simp only [Box.upper, Function.update_self] at h₂
      exact ⟨ht.1.trans h₂.1, h₂.2⟩
    · simpa [Box.upper, Function.update_of_ne hw] using h₂
  | cutHi w t ht _ _ _ ih₂ =>
    intro B'' hB''
    have h₂ := ih₂ B'' hB''
    by_cases hw : v = w
    · subst hw
      simp only [Box.lower, Function.update_self] at h₂
      exact ⟨h₂.1, h₂.2.trans ht.2⟩
    · simpa [Box.lower, Function.update_of_ne hw] using h₂

theorem wheelOut_sound {H : HexChoice P k} {A : Assign P k} (hA : A ∈ Sol P H)
    {B : Box (PVar P k)} (hB : DomOK B) (hm : B.Mem (PVar.val A)) {m : Fin k} {i : Fin 6}
    {β : ℝ × ℝ} (h : WheelOut B m i β) :
    β.1 ≤ gam (A.r m (i - 1)) (A.r m i) A.d ∧ gam (A.r m (i - 1)) (A.r m i) A.d ≤ β.2 := by
  obtain ⟨R, hR, I, hI, h1, h2⟩ := h
  unfold triAngle at hI
  rcases triAngleSt_mem hR (ivOf_mem hm (.r m (i - 1))) (ivOf_mem hm (.r m i)) (ivOf_mem hm .d)
    with ⟨I', hI', hm'⟩ | ⟨I', hI', -, -⟩
  · rw [hI'] at hI
    cases hI
    exact ⟨Fl.ofReal_le_ofReal.mp (Fl.le_trans h1 hm'.1),
      Fl.ofReal_le_ofReal.mp (Fl.le_trans hm'.2 h2)⟩
  · rw [hI'] at hI
    simp [Except.toOption] at hI

theorem Impl.onDom_sound {N : Procs} (hN : Impl N) : (onDom N).Sound := by
  intro P k H
  refine ⟨fun m A hA B hm => ?_, fun A hA B hm m i β h => ?_⟩
  · simp only [onDom]
    split_ifs with hB
    · exact (hN.1 P k H m B hB).sound hA hm
    · exact ⟨B, rfl, hm⟩
  · simp only [onDom] at h
    split_ifs at h with hB
    exact wheelOut_sound hA hB hm (hN.2 P k B m i β hB h)

/-- On a box of the domain, the leaf test of `onDom N` is the leaf test of `N`. -/
theorem leafKill_onDom {N : Procs} {P : PlaneGraph} {k : ℕ} {H : HexChoice P k}
    {B : Box (PVar P k)} (hB : DomOK B) : LeafKill (onDom N) P H B ↔ LeafKill N P H B := by
  have hW : ∀ m i, (onDom N).wheel P k B m i = N.wheel P k B m i := by
    intro m i
    simp only [onDom, hB, ↓reduceIte]
  simp only [LeafKill, Encl.Covers, hW]

/-- A tree accepted with the procedures of `N` from a box of the domain is accepted with those of
`onDom N`. -/
theorem tree_ok_onDom {N : Procs} (hN : Impl N) {P : PlaneGraph} {k : ℕ} {H : HexChoice P k}
    (m : Mode) (t : Search.Tree (PVar P k)) :
    ∀ B : Box (PVar P k), DomOK B → t.OK (N.narrow P k H m) (LeafKill N P H) B →
      t.OK ((onDom N).narrow P k H m) (LeafKill (onDom N) P H) B := by
  have hnar : ∀ B : Box (PVar P k), DomOK B →
      (onDom N).narrow P k H m B = N.narrow P k H m B := by
    intro B hB
    simp only [onDom, hB, ↓reduceIte]
  have hsub : ∀ B B' : Box (PVar P k), DomOK B → N.narrow P k H m B = some B' → DomOK B' := by
    intro B B' hB h
    have hr := hN.1 P k H m B hB
    rw [h] at hr
    exact hB.mono (hr.subset)
  induction t with
  | leaf =>
    intro B hB ht B' hB'
    rw [hnar B hB] at hB'
    exact (leafKill_onDom (hsub B B' hB hB')).mpr (ht B' hB')
  | split v t l r ihl ihr =>
    intro B hB ht B' hB'
    rw [hnar B hB] at hB'
    have hB'D := hsub B B' hB hB'
    rcases ht B' hB' with hK | hT
    · exact Or.inl ((leafKill_onDom hB'D).mpr hK)
    · right
      split_ifs at hT ⊢ with h1 h2
      · exact ihr B' hB'D hT
      · exact ihl B' hB'D hT
      · refine ⟨ihl _ (hB'D.mono fun w => ?_) hT.1, ihr _ (hB'D.mono fun w => ?_) hT.2⟩
        · by_cases hw : w = v
          · subst hw
            simp only [Box.lower, Function.update_self]
            exact ⟨le_rfl, not_lt.mp h2⟩
          · simp [Box.lower, Function.update_of_ne hw]
        · by_cases hw : w = v
          · subst hw
            simp only [Box.upper, Function.update_self]
            exact ⟨not_lt.mp h1, le_rfl⟩
          · simp [Box.upper, Function.update_of_ne hw]

theorem progTrees_onDom {L : Set PlaneGraph} {N : Procs} (hN : Impl N) (h : ProgTreesDom L N) :
    ProgTrees L (onDom N) := by
  intro P hP k hk H
  obtain ⟨H₀, hH, h'⟩ := h P hP k hk H
  refine ⟨H₀, hH, fun d hd1 hd2 => ?_⟩
  obtain ⟨lo, hi, hlo, hhi, m, B₀, t, hroot, hdom, ht⟩ := h' d hd1 hd2
  exact ⟨lo, hi, hlo, hhi, m, B₀, t, hroot, tree_ok_onDom hN m t B₀ hdom ht⟩

end Tammes15.Contractors

namespace Tammes15

/-- `Tammes15.Conjecture` from `EnumComplete L` (D2), the replayed trees of the program on `L`
with root boxes in the domain, and how its procedures compute (`Contractors.Impl`): the soundness
of its contractors is proved, not assumed. -/
theorem conjecture_of_enum_progTreesDom (L : Set PlaneGraph) (N : PaperSteps.Procs)
    (h2 : EnumComplete L) (h3 : Contractors.ProgTreesDom L N) (hN : Contractors.Impl N) :
    Conjecture :=
  conjecture_of_enum_progTrees L (Contractors.onDom N) h2 (Contractors.progTrees_onDom hN h3)
    (Contractors.Impl.onDom_sound hN)

end Tammes15
