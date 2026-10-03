import Tammes15.PaperSteps.LocalEq

/-!
# Proposition 3.1 (3): the orbits of `D` on the eight frame configurations

The paper states: the group `D` acts on the eight frame configurations with two orbits: `C3` and the
configuration keeping the other three toggle points form one orbit, the six others the second, which
contains `C1`. A frame configuration is the set of the frame points kept by a choice `t` in the
three toggle pairs (`frameSet t`); `C3` keeps the points `6, 7, 8` (`t` constantly `true`) and `C1`
the points `6, 7, 10` (`tC1`). `optima_four` states the four facts as sets of points of the sphere.
The indices carry the combinatorics (`decide`); the frame points are pairwise distinct
(`pt_injective`, by the first coordinates, which `sym_close` knows to `1e-39`). `frameSet`, `tC1`
and `dWord` are defined in FrameDefs.lean.
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15 Attained

set_option maxHeartbeats 400000 in
/-- The first coordinates of the eighteen frame points are at least `1e-3` apart. -/
theorem ptPat_symMid_sep (k k' : Fin 18) (h : k ≠ k') :
    1e-3 ≤ |ptPat symMid k 0 - ptPat symMid k' 0| := by
  fin_cases k <;> fin_cases k' <;>
    first
    | exfalso; exact h rfl
    | simp [ptPat, symMid] <;> norm_num

/-- The eighteen frame points are distinct. -/
theorem pt_injective : Function.Injective (fun k => pt bR uR k) := by
  intro k k' h
  by_contra hne
  have h0 : (pt bR uR k).ofLp 0 = (pt bR uR k').ofLp 0 := by simpa [h]
  have hV_eq : ptPat (fun s => symN bR uR s / 225008) k 0 = ptPat (fun s => symN bR uR s / 225008) k' 0 := by
    simpa [pt_ofLp] using h0
  set V := fun s => symN bR uR s / 225008 with hV
  have hV_close : ∀ s, |V s - symMid s| ≤ (1e-39 : ℝ) := by
    intro s
    dsimp [V]
    exact sym_close s
  have hclose_k : |ptPat V k 0 - ptPat symMid k 0| ≤ (1e-39 : ℝ) :=
    ptPat_close hV_close k 0
  have hclose_k' : |ptPat V k' 0 - ptPat symMid k' 0| ≤ (1e-39 : ℝ) :=
    ptPat_close hV_close k' 0
  have hsum : |ptPat symMid k 0 - ptPat symMid k' 0| ≤ (2e-39 : ℝ) := by
    have h_eq : ptPat symMid k 0 - ptPat symMid k' 0 =
        (ptPat symMid k 0 - ptPat V k 0) + (ptPat V k 0 - ptPat V k' 0) + (ptPat V k' 0 - ptPat symMid k' 0) := by
      ring
    rw [h_eq]
    calc
      |(ptPat symMid k 0 - ptPat V k 0) + (ptPat V k 0 - ptPat V k' 0) + (ptPat V k' 0 - ptPat symMid k' 0)|
          ≤ |(ptPat symMid k 0 - ptPat V k 0) + (ptPat V k 0 - ptPat V k' 0)| + |ptPat V k' 0 - ptPat symMid k' 0| :=
        abs_add_le _ _
      _ ≤ (|ptPat symMid k 0 - ptPat V k 0| + |ptPat V k 0 - ptPat V k' 0|) + |ptPat V k' 0 - ptPat symMid k' 0| := by
        nlinarith [abs_add_le (ptPat symMid k 0 - ptPat V k 0) (ptPat V k 0 - ptPat V k' 0)]
      _ = |ptPat symMid k 0 - ptPat V k 0| + |ptPat V k 0 - ptPat V k' 0| + |ptPat V k' 0 - ptPat symMid k' 0| := by ring
      _ = |ptPat V k 0 - ptPat symMid k 0| + |ptPat V k 0 - ptPat V k' 0| + |ptPat V k' 0 - ptPat symMid k' 0| := by
        simp [abs_sub_comm]
      _ = |ptPat V k 0 - ptPat symMid k 0| + 0 + |ptPat V k' 0 - ptPat symMid k' 0| := by
        rw [hV_eq, sub_self, abs_zero]
      _ = |ptPat V k 0 - ptPat symMid k 0| + |ptPat V k' 0 - ptPat symMid k' 0| := by simp
      _ ≤ (1e-39 : ℝ) + (1e-39 : ℝ) := by
        nlinarith
      _ = (2e-39 : ℝ) := by norm_num
  have hsep : (1e-3 : ℝ) ≤ |ptPat symMid k 0 - ptPat symMid k' 0| :=
    ptPat_symMid_sep k k' hne
  have h_contra : (1e-3 : ℝ) ≤ (2e-39 : ℝ) := le_trans hsep hsum
  norm_num at h_contra

theorem dIdx_frameIdx (w : Fin 6) (t : Fin 3 → Bool) :
    ∃ t', (frameIdx t).image (dIdx w) = frameIdx t' := by
  revert w t
  decide

theorem frameIdx_injective : Function.Injective frameIdx := by
  decide

theorem image_dWord_frameSet (w : Fin 6) (t t' : Fin 3 → Bool)
    (h : (frameIdx t).image (dIdx w) = frameIdx t') : dWord w '' frameSet t = frameSet t' := by
  dsimp [frameSet]
  calc
    dWord w '' ((fun k => pt bR uR k) '' (frameIdx t : Set (Fin 18)))
        = (fun k => dWord w (pt bR uR k)) '' (frameIdx t : Set (Fin 18)) := by
      rw [Set.image_image]
    _ = (fun k => pt bR uR (dIdx w k)) '' (frameIdx t : Set (Fin 18)) := by
      simp [pt_dWord]
    _ = (pt bR uR) '' ((dIdx w) '' (frameIdx t : Set (Fin 18))) := by
      rw [← Set.image_image]
    _ = (pt bR uR) '' ((frameIdx t).image (dIdx w) : Set (Fin 18)) := by
      rw [Finset.coe_image]
    _ = (pt bR uR) '' (frameIdx t' : Set (Fin 18)) := by rw [h]
    _ = frameSet t' := rfl

theorem frameSet_injective : Function.Injective frameSet := by
  intro t t' h
  have h_inj : Function.Injective (fun k => pt bR uR k) := pt_injective
  have h_image_inj : Function.Injective (Set.image (fun k => pt bR uR k)) :=
    (Set.image_injective).mpr h_inj
  have h_sets : (frameIdx t : Set (Fin 18)) = (frameIdx t' : Set (Fin 18)) :=
    h_image_inj h
  have h_finset : frameIdx t = frameIdx t' := Finset.coe_inj.mp h_sets
  exact frameIdx_injective h_finset

theorem range_frameC3 : Set.range frameC3.p = frameSet (fun _ => true) := by
  have h_image : Set.range keepC3 = (Finset.univ.image keepC3 : Set (Fin 18)) := by
    calc
      Set.range keepC3 = (fun i => keepC3 i) '' Set.univ := (Set.image_univ (f := keepC3)).symm
      _ = (fun i => keepC3 i) '' ((Finset.univ : Finset (Fin 15)) : Set (Fin 15)) := by simp
      _ = (Finset.univ.image keepC3 : Set (Fin 18)) := by rw [Finset.coe_image]
  have h_eq : Finset.univ.image keepC3 = frameIdx (fun _ => true) := by
    decide
  calc
    Set.range frameC3.p = Set.range ((fun k => pt bR uR k) ∘ keepC3) := rfl
    _ = (fun k => pt bR uR k) '' Set.range keepC3 := by rw [Set.range_comp]
    _ = (fun k => pt bR uR k) '' (Finset.univ.image keepC3 : Set (Fin 18)) := by rw [h_image]
    _ = (fun k => pt bR uR k) '' (frameIdx (fun _ => true) : Set (Fin 18)) := by rw [h_eq]
    _ = frameSet (fun _ => true) := rfl

theorem range_frameC1 : Set.range frameC1.p = frameSet tC1 := by
  have h_image : Finset.univ.image keepC1 = frameIdx tC1 := by
    decide
  calc
    Set.range frameC1.p = Set.range ((fun k => pt bR uR k) ∘ keepC1) := by
      ext y; simp [frameC1, keepC1]
    _ = (fun k => pt bR uR k) '' Set.range keepC1 := by rw [Set.range_comp]
    _ = (fun k => pt bR uR k) '' (keepC1 '' Set.univ) := by
      ext y; simp [Set.mem_range, Set.mem_image]
    _ = (fun k => pt bR uR k) '' (keepC1 '' ((Finset.univ : Finset (Fin 15)) : Set (Fin 15))) := by rw [← Finset.coe_univ]
    _ = (fun k => pt bR uR k) '' ((Finset.image keepC1 (Finset.univ : Finset (Fin 15))) : Set (Fin 18)) := by
      rw [← Finset.coe_image]
    _ = (fun k => pt bR uR k) '' (frameIdx tC1 : Set (Fin 18)) := by rw [h_image]
    _ = frameSet tC1 := rfl

/-- The orbit of `C3` on the indices: the choices constant on the three toggle pairs. -/
theorem orbit_C3_idx (t : Fin 3 → Bool) :
    (∃ w, (frameIdx (fun _ => true)).image (dIdx w) = frameIdx t) ↔ ∀ i j, t i = t j := by
  revert t
  decide

/-- The orbit of `C1` on the indices: the six other choices. -/
theorem orbit_C1_idx (t : Fin 3 → Bool) :
    (∃ w, (frameIdx tC1).image (dIdx w) = frameIdx t) ↔ ¬ ∀ i j, t i = t j := by
  revert t
  decide

/-- Proposition 3.1 (3): `D` maps each frame configuration to a frame configuration; `C3`
and `C1` are frame configurations; the orbit of `C3` is made of the two choices constant on the
toggle pairs (`C3` and the configuration keeping the other three toggle points), and the orbit of
`C1` of the six others. -/
theorem optima_four :
    (∀ w : Fin 6, ∀ t : Fin 3 → Bool, ∃ t', dWord w '' frameSet t = frameSet t') ∧
      Set.range frameC3.p = frameSet (fun _ => true) ∧ Set.range frameC1.p = frameSet tC1 ∧
      (∀ t, (∃ w, dWord w '' Set.range frameC3.p = frameSet t) ↔ ∀ i j, t i = t j) ∧
      (∀ t, (∃ w, dWord w '' Set.range frameC1.p = frameSet t) ↔ ¬ ∀ i j, t i = t j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- first conjunct: ∀ w, ∀ t, ∃ t', dWord w '' frameSet t = frameSet t'
    intro w t
    rcases dIdx_frameIdx w t with ⟨t', h⟩
    exact ⟨t', image_dWord_frameSet w t t' h⟩
  · -- second conjunct: Set.range frameC3.p = frameSet (fun _ => true)
    exact range_frameC3
  · -- third conjunct: Set.range frameC1.p = frameSet tC1
    exact range_frameC1
  · -- fourth conjunct: (∀ t, (∃ w, dWord w '' Set.range frameC3.p = frameSet t) ↔ ∀ i j, t i = t j)
    intro t
    rw [range_frameC3]
    constructor
    · intro h
      rcases h with ⟨w, h⟩
      rcases dIdx_frameIdx w (fun _ => true) with ⟨t₀, h₀⟩
      have h_image : dWord w '' frameSet (fun _ => true) = frameSet t₀ :=
        image_dWord_frameSet w (fun _ => true) t₀ h₀
      rw [h_image] at h
      have h_eq : t₀ = t := frameSet_injective h
      rw [h_eq] at h₀
      exact (orbit_C3_idx t).mp ⟨w, h₀⟩
    · intro h
      rcases (orbit_C3_idx t).mpr h with ⟨w, h_w⟩
      exact ⟨w, image_dWord_frameSet w (fun _ => true) t h_w⟩
  · -- fifth conjunct: (∀ t, (∃ w, dWord w '' Set.range frameC1.p = frameSet t) ↔ ¬ ∀ i j, t i = t j)
    intro t
    rw [range_frameC1]
    constructor
    · intro h
      rcases h with ⟨w, h⟩
      rcases dIdx_frameIdx w tC1 with ⟨t₀, h₀⟩
      have h_image : dWord w '' frameSet tC1 = frameSet t₀ :=
        image_dWord_frameSet w tC1 t₀ h₀
      rw [h_image] at h
      have h_eq : t₀ = t := frameSet_injective h
      rw [h_eq] at h₀
      exact (orbit_C1_idx t).mp ⟨w, h₀⟩
    · intro h
      rcases (orbit_C1_idx t).mpr h with ⟨w, h_w⟩
      exact ⟨w, image_dWord_frameSet w tC1 t h_w⟩

end Tammes15.PaperSteps
