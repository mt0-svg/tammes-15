import Mathlib.Basic.Real.Basic

/-!
# Boxes, narrowings and search trees

The abstract part of Proposition 5.6 (2) of the paper, for any type `ι` of variables.

* A box gives each variable a lower and an upper end; a point `x : ι → ℝ` is in it when every
  coordinate is between its ends. The two closed halves of a split of `v` at `t` cover the box
  (`Box.mem_lower_or_upper`).
* A narrowing `N : Box ι → Option (Box ι)` (`none`: the box is empty) is sound for the points
  `val a`, `a ∈ S`, when it keeps every such point of the box (`NarrowSound`).
* A search tree is the preorder of tokens of the program (code/impl1/rust/src/deep.rs, `Tok`):
  a leaf, or a split of a variable at a point followed by the trees of the lower and the upper half.
  `Tree.OK N K t B` is what the replay of the tree from the box `B` checks (deep.rs,
  `Prob::replay`): at every node the box is narrowed; at a leaf the narrowing empties the box or the
  narrowed box passes the test `K`; at a split node either the same, or the children are OK on the
  halves of the narrowed box (on the narrowed box itself when the split point lies outside the
  interval of the variable, the replay sending the whole box to one side).
* `Tree.sound`: a sound narrowing and an OK tree put every point of `S` in the box into a narrowed
  box that passes `K`.
* 3B shaving (deep.rs, `Prob::shave`): a slice of a variable at one end is narrowed alone and removed
  when the narrowing empties it; the steps keep the points of `S` (`shaveSeq_mem`), so shaving after
  a sound narrowing is sound (`NarrowSound.shave`).
-/

namespace Tammes15.PaperSteps.Search

open scoped Classical

variable {ι X : Type}

/-- A box over the variables `ι`: a lower and an upper end for each variable. -/
structure Box (ι : Type) where
  lo : ι → ℝ
  hi : ι → ℝ

/-- The point `x` (a value for each variable) lies in the box. -/
def Box.Mem (B : Box ι) (x : ι → ℝ) : Prop :=
  ∀ i, B.lo i ≤ x i ∧ x i ≤ B.hi i

/-- The lower half of the split of `v` at `t`: the upper end of `v` becomes `t`. -/
noncomputable def Box.lower (B : Box ι) (v : ι) (t : ℝ) : Box ι :=
  ⟨B.lo, Function.update B.hi v t⟩

/-- The upper half of the split of `v` at `t`: the lower end of `v` becomes `t`. -/
noncomputable def Box.upper (B : Box ι) (v : ι) (t : ℝ) : Box ι :=
  ⟨Function.update B.lo v t, B.hi⟩

/-- The two closed halves of a split cover the box. -/
theorem Box.mem_lower_or_upper (B : Box ι) (v : ι) (t : ℝ) {x : ι → ℝ} (h : B.Mem x) :
    (B.lower v t).Mem x ∨ (B.upper v t).Mem x := by
  by_cases hv : x v ≤ t
  · left
    intro i
    by_cases hi : i = v
    · subst hi
      exact ⟨(h i).1, by simp [Box.lower, hv]⟩
    · exact ⟨(h i).1, by simp [Box.lower, Function.update_of_ne hi, (h i).2]⟩
  · right
    intro i
    by_cases hi : i = v
    · subst hi
      exact ⟨by simpa [Box.upper] using (not_le.mp hv).le, (h i).2⟩
    · exact ⟨by simp [Box.upper, Function.update_of_ne hi, (h i).1], (h i).2⟩

/-- A narrowing is sound for the points `val a`, `a ∈ S`: a box that holds such a point is narrowed
to a box (not to `none`) that still holds it. -/
def NarrowSound (S : Set X) (val : X → ι → ℝ) (N : Box ι → Option (Box ι)) : Prop :=
  ∀ a ∈ S, ∀ B : Box ι, B.Mem (val a) → ∃ B', N B = some B' ∧ B'.Mem (val a)

/-- A search tree, in the preorder of the tokens of the program: a leaf, or the split of the
variable `v` at `t` followed by the trees of the lower and the upper half. -/
inductive Tree (ι : Type) where
  | leaf : Tree ι
  | split (v : ι) (t : ℝ) (l r : Tree ι) : Tree ι

/-- What the replay of a tree from the box `B` checks, with the narrowing `N` and the leaf test `K`.
At a leaf, the narrowing empties the box or the narrowed box passes `K`. At a split node, the same,
or the children are OK: on the narrowed box itself when `t` lies below (above) the interval of `v`,
for the upper (lower) child, the other child being skipped; on the two halves otherwise. -/
noncomputable def Tree.OK (N : Box ι → Option (Box ι)) (K : Box ι → Prop) :
    Tree ι → Box ι → Prop
  | .leaf, B => ∀ B', N B = some B' → K B'
  | .split v t l r, B => ∀ B', N B = some B' → K B' ∨
      (if t < B'.lo v then r.OK N K B'
      else if B'.hi v < t then l.OK N K B'
      else l.OK N K (B'.lower v t) ∧ r.OK N K (B'.upper v t))

/-- Soundness of the search: a point of `S` in the root box lies in a narrowed box of the tree that
passes the leaf test. -/
theorem Tree.sound {S : Set X} {val : X → ι → ℝ} {N : Box ι → Option (Box ι)}
    {K : Box ι → Prop} (hN : NarrowSound S val N) :
    ∀ (t : Tree ι) (B : Box ι), t.OK N K B → ∀ a ∈ S, B.Mem (val a) →
      ∃ B', B'.Mem (val a) ∧ K B' := by
  intro t
  induction t with
  | leaf =>
    intro B hB a ha hm
    obtain ⟨B', hNB, hm'⟩ := hN a ha B hm
    exact ⟨B', hm', hB B' hNB⟩
  | split v t l r ihl ihr =>
    intro B hB a ha hm
    obtain ⟨B', hNB, hm'⟩ := hN a ha B hm
    rcases hB B' hNB with hK | hC
    · exact ⟨B', hm', hK⟩
    · split_ifs at hC with h1 h2
      · exact ihr B' hC a ha hm'
      · exact ihl B' hC a ha hm'
      · rcases B'.mem_lower_or_upper v t hm' with hlo | hup
        · exact ihl _ hC.1 a ha hlo
        · exact ihr _ hC.2 a ha hup

/-! ## 3B shaving -/

/-- A shaving step at the lower end of `v` (deep.rs `Prob::shave`, side 0): the slice of `v` below
`t` is narrowed alone, and removed if the narrowing empties it. -/
noncomputable def shaveLo (N : Box ι → Option (Box ι)) (v : ι) (t : ℝ) (B : Box ι) : Box ι :=
  if N (B.lower v t) = none then B.upper v t else B

/-- A shaving step at the upper end of `v` (side 1): the slice above `t`. -/
noncomputable def shaveHi (N : Box ι → Option (Box ι)) (v : ι) (t : ℝ) (B : Box ι) : Box ι :=
  if N (B.upper v t) = none then B.lower v t else B

theorem shaveLo_mem {S : Set X} {val : X → ι → ℝ} {N : Box ι → Option (Box ι)}
    (hN : NarrowSound S val N) {a : X} (ha : a ∈ S) {B : Box ι} (hB : B.Mem (val a)) (v : ι)
    (t : ℝ) : (shaveLo N v t B).Mem (val a) := by
  unfold shaveLo
  split_ifs with h
  · rcases B.mem_lower_or_upper v t hB with hlo | hup
    · obtain ⟨B', hB', -⟩ := hN a ha _ hlo
      rw [h] at hB'
      exact absurd hB' (by simp)
    · exact hup
  · exact hB

theorem shaveHi_mem {S : Set X} {val : X → ι → ℝ} {N : Box ι → Option (Box ι)}
    (hN : NarrowSound S val N) {a : X} (ha : a ∈ S) {B : Box ι} (hB : B.Mem (val a)) (v : ι)
    (t : ℝ) : (shaveHi N v t B).Mem (val a) := by
  unfold shaveHi
  split_ifs with h
  · rcases B.mem_lower_or_upper v t hB with hlo | hup
    · exact hlo
    · obtain ⟨B', hB', -⟩ := hN a ha _ hup
      rw [h] at hB'
      exact absurd hB' (by simp)
  · exact hB

/-- A sequence of shaving steps: the end (`true`: upper), the variable, and the cut as a function of
the current box (the program cuts at `1/s` of the width, and skips a variable narrower than
`10⁻¹²`, which is the step at the cut `lo` or `hi`, a step that changes nothing). -/
noncomputable def shaveSeq (N : Box ι → Option (Box ι)) :
    List (Bool × ι × (Box ι → ℝ)) → Box ι → Box ι
  | [], B => B
  | s :: l, B => shaveSeq N l (if s.1 then shaveHi N s.2.1 (s.2.2 B) B else shaveLo N s.2.1 (s.2.2 B) B)

theorem shaveSeq_mem {S : Set X} {val : X → ι → ℝ} {N : Box ι → Option (Box ι)}
    (hN : NarrowSound S val N) {a : X} (ha : a ∈ S) :
    ∀ (l : List (Bool × ι × (Box ι → ℝ))) (B : Box ι), B.Mem (val a) →
      (shaveSeq N l B).Mem (val a) := by
  intro l
  induction l with
  | nil => intro B hB; exact hB
  | cons s l ih =>
    intro B hB
    apply ih
    split_ifs
    · exact shaveHi_mem hN ha hB _ _
    · exact shaveLo_mem hN ha hB _ _

/-- 3B shaving of a sound narrowing is sound: narrow, shave with the steps `l`, and narrow again
when the shaving changed the box (deep.rs `Prob::check` with `--shave`, `Prob::shave`). -/
theorem NarrowSound.shave {S : Set X} {val : X → ι → ℝ} {N : Box ι → Option (Box ι)}
    (hN : NarrowSound S val N) (l : List (Bool × ι × (Box ι → ℝ))) :
    NarrowSound S val (fun B => (N B).bind fun B₁ =>
      if shaveSeq N l B₁ = B₁ then some B₁ else N (shaveSeq N l B₁)) := by
  intro a ha B hB
  obtain ⟨B₁, hB₁, hm₁⟩ := hN a ha B hB
  have hm₂ := shaveSeq_mem hN ha l B₁ hm₁
  simp only [hB₁, Option.bind_some]
  split_ifs with h
  · exact ⟨B₁, rfl, hm₁⟩
  · exact hN a ha _ hm₂

end Tammes15.PaperSteps.Search
