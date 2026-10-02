import Tammes15.Attained.Data

/-!
# The roots `uR` and `bR`

The sign lemmas are generated in SageMath.
The intermediate value
theorem gives a root of `quintic` in `[ul, uh]` and, for each `u` there, a root of `Q4 · u` in
`[bl, bh]`; `uR` and `bR` of Data.lean are such roots.
-/

set_option maxHeartbeats 0

open scoped RealInnerProductSpace

namespace Tammes15.Attained

set_option linter.unusedSimpArgs false

/-! ## Signs at the ends of the enclosures -/

theorem quintic_lo : quintic ul < 0 := by
  norm_num [quintic, ul]

theorem quintic_hi : 0 < quintic uh := by
  norm_num [quintic, uh]

theorem Q4_lo (u : ℝ) (hu : u ∈ Set.Icc ul uh) : Q4 bl u < 0 := by
  simp only [ul, uh] at hu
  simp only [Q4, bl]
  dyadic_interval [prec := 256]

theorem Q4_hi (u : ℝ) (hu : u ∈ Set.Icc ul uh) : 0 < Q4 bh u := by
  simp only [ul, uh] at hu
  simp only [Q4, bh]
  dyadic_interval [prec := 256]

theorem u_root : ∃ u ∈ Set.Icc ul uh, quintic u = 0 := by
  have hle : ul ≤ uh := by
    unfold ul uh
    norm_num
  have hcont : ContinuousOn quintic (Set.Icc ul uh) := by
    unfold quintic
    fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc (quintic ul) (quintic uh) := by
    refine ⟨by linarith [quintic_lo], by linarith [quintic_hi]⟩
  rcases (intermediate_value_Icc hle hcont) h0 with ⟨u, hu, hquintic⟩
  exact ⟨u, hu, hquintic⟩

theorem b_root (u : ℝ) (hu : u ∈ Set.Icc ul uh) : ∃ b ∈ Set.Icc bl bh, Q4 b u = 0 := by
  have hblbh : bl ≤ bh := by
    unfold bl bh
    norm_num
  have h_cont : ContinuousOn (fun b => Q4 b u) (Set.Icc bl bh) := by
    unfold Q4
    fun_prop
  have h0_mem : (0 : ℝ) ∈ Set.Icc (Q4 bl u) (Q4 bh u) := by
    refine ⟨by linarith [Q4_lo u hu], by linarith [Q4_hi u hu]⟩
  have h_subset := intermediate_value_Icc hblbh h_cont
  have h0_image : (0 : ℝ) ∈ (fun b => Q4 b u) '' Set.Icc bl bh :=
    h_subset h0_mem
  rcases h0_image with ⟨b, hb, hb_eq⟩
  exact ⟨b, hb, hb_eq⟩

theorem uR_spec : uR ∈ Set.Icc ul uh ∧ quintic uR = 0 :=
  Classical.epsilon_spec u_root

theorem bR_spec : bR ∈ Set.Icc bl bh ∧ Q4 bR uR = 0 :=
  Classical.epsilon_spec (b_root uR uR_spec.1)

theorem bounds_of_mem (u : ℝ) (hu : u ∈ Set.Icc ul uh) : 1 / 2 < u ∧ u < 7 / 10 := by
  obtain ⟨hul, huh⟩ := hu
  have h1 : (1 : ℝ) / 2 < ul := by
    norm_num [ul]
  have h2 : uh < 7 / 10 := by
    norm_num [uh]
  constructor
  · linarith
  · linarith

end Tammes15.Attained
