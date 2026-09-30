import Tammes15.Rattlers.NorPoly
import Tammes15.Numerics.HexData

/-!
# Proposition onehex by an inscribed polygon: the closed form and the margin


See code/lean/numerics/onehex_poly.gp. For two discs of
radius `h` whose centres are at distance `l < π - 2h`, the polygon made of the two common tangent
points of each side and five points on each outer arc has perimeter `hexPoly l h = 2 L + 8 c`,
with `cos L = (cos l - sin² h) / cos² h` (`tanLen`, the common tangent segment), `cos γ = -tan h tan (l/2)`
(`tanAng`, the angle at a centre between the tangency point and the other centre) and `c` the chord
of the step `(2π - 2γ)/4` on a circle of radius `h` (`chordC`). The margin `6 d < hexPoly d (hrad d)` on
`[dlo, dhi]` is cut into ten pieces `[dpt i, dpt (i+1)]`, on each of which the worst-end bound holds
(`hexPoly_lower`, from the monotonicity of the three functions); margins 10.1 to 2.5 degrees.
-/

open Real

namespace Tammes15

/-- The common tangent segment of two discs of radius `h` at centre distance `l`. -/
noncomputable def tanLen (l h : ℝ) : ℝ := arccos ((cos l - sin h ^ 2) / cos h ^ 2)

/-- The angle at a centre between its tangency point and the other centre. -/
noncomputable def tanAng (l h : ℝ) : ℝ := arccos (-(tan h * tan (l / 2)))

/-- The chord of the arc of angle `s` on a circle of radius `h`. -/
noncomputable def chordC (h s : ℝ) : ℝ := arccos (cos h ^ 2 + sin h ^ 2 * cos s)

/-- The perimeter of the inscribed polygon of Proposition onehex, `k = 4`. -/
noncomputable def hexPoly (l h : ℝ) : ℝ := 2 * tanLen l h + 8 * chordC h ((2 * π - 2 * tanAng l h) / 4)

/-- The subdivision points `dpt i = 53.65785° + i · 0.301375°`; `dpt 0 = dlo`, `dpt 10 = dhi`. -/
noncomputable def dpt (i : ℕ) : ℝ := (10731570 + 60275 * (i : ℝ)) / 200000 * (π / 180)

theorem dpt_zero : dpt 0 = dlo := by
  unfold dpt dlo; push_cast; ring

theorem dpt_ten : dpt 10 = dhi := by
  unfold dpt dhi
  push_cast
  ring

theorem dpt_mono (i j : ℕ) (h : i ≤ j) : dpt i ≤ dpt j := by
  unfold dpt
  have h' : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr h
  have hpos200000 : 0 ≤ (200000 : ℝ) := by norm_num
  have hpos_pi_div_180 : 0 ≤ π / 180 := by
    have hpi : 0 < π := Real.pi_pos
    positivity
  have hnum : (10731570 + 60275 * (i : ℝ)) / 200000 ≤ (10731570 + 60275 * (j : ℝ)) / 200000 :=
    div_le_div_of_nonneg_right (by nlinarith) hpos200000
  exact mul_le_mul_of_nonneg_right hnum hpos_pi_div_180

theorem chordC_monotoneOn_h (s : ℝ) (hs : 0 ≤ s ∧ s ≤ π) :
    MonotoneOn (fun h => chordC h s) (Set.Icc 0 (π / 2)) := by
  intro x hx y hy hxy
  unfold chordC
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ π / 2 := hx.2
  have hy0 : 0 ≤ y := hy.1
  have hy1 : y ≤ π / 2 := hy.2
  have hsinx_nonneg : 0 ≤ sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
  have hsiny_nonneg : 0 ≤ sin y :=
    Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith)
  have hsin_le : sin x ≤ sin y :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hy1 hxy
  have h_sin_sq : sin x ^ 2 ≤ sin y ^ 2 :=
    pow_le_pow_left₀ hsinx_nonneg hsin_le 2
  have h_nonneg : 0 ≤ 1 - cos s :=
    sub_nonneg.mpr (Real.cos_le_one s)
  have h_mul : sin x ^ 2 * (1 - cos s) ≤ sin y ^ 2 * (1 - cos s) :=
    mul_le_mul_of_nonneg_right h_sin_sq h_nonneg
  have h_arg : cos y ^ 2 + sin y ^ 2 * cos s ≤ cos x ^ 2 + sin x ^ 2 * cos s := by
    calc
      cos y ^ 2 + sin y ^ 2 * cos s = (1 - sin y ^ 2) + sin y ^ 2 * cos s := by rw [Real.cos_sq']
      _ = 1 - sin y ^ 2 * (1 - cos s) := by ring
      _ ≤ 1 - sin x ^ 2 * (1 - cos s) := by linarith
      _ = (1 - sin x ^ 2) + sin x ^ 2 * cos s := by ring
      _ = cos x ^ 2 + sin x ^ 2 * cos s := by rw [Real.cos_sq']
  exact Real.arccos_le_arccos h_arg

theorem chordC_monotoneOn_s (h : ℝ) : MonotoneOn (fun s => chordC h s) (Set.Icc 0 π) := by
  intro x hx y hy hxy
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  unfold chordC
  have hcos : cos y ≤ cos x := Real.cos_le_cos_of_nonneg_of_le_pi hx0 hy1 hxy
  have hsin_sq_nonneg : 0 ≤ sin h ^ 2 := pow_two_nonneg _
  have harg : cos h ^ 2 + sin h ^ 2 * cos y ≤ cos h ^ 2 + sin h ^ 2 * cos x := by
    nlinarith
  exact Real.arccos_le_arccos harg

theorem tanLen_monotoneOn_l (h : ℝ) (hh : 0 ≤ h ∧ h < π / 2) :
    MonotoneOn (fun l => tanLen l h) (Set.Icc 0 π) := by
  rcases hh with ⟨hh0, hh1⟩
  intro x hx y hy hxy
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  unfold tanLen
  apply Real.arccos_le_arccos
  have hcos_sq_pos : 0 < cos h ^ 2 := by
    have hcos_pos : 0 < cos h := Real.cos_pos_of_mem_Ioo ⟨by linarith, hh1⟩
    exact pow_pos hcos_pos 2
  have hcos_le : cos y ≤ cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi hx0 hy1 hxy
  have hnum : cos y - sin h ^ 2 ≤ cos x - sin h ^ 2 := by
    linarith
  exact div_le_div_of_nonneg_right hnum (by positivity)

theorem tanLen_monotoneOn_h (l : ℝ) (hl : 0 ≤ l ∧ l ≤ π) :
    MonotoneOn (fun h => tanLen l h) (Set.Ico 0 (π / 2)) := by
  rcases hl with ⟨hl0, hl1⟩
  intro x hx y hy hxy
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  unfold tanLen
  apply Real.arccos_le_arccos
  have hcosx_pos : 0 < cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have hcosy_pos : 0 < cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith, hy1⟩
  have hsinx_nonneg : 0 ≤ sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
  have hsiny_nonneg : 0 ≤ sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith)
  have hsinx_le_siny : sin x ≤ sin y :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hy1.le hxy
  have hsinx_sq_le_siny_sq : sin x ^ 2 ≤ sin y ^ 2 := by nlinarith
  have hsinx_lt_one : sin x < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hx1
    simpa [Real.sin_pi_div_two] using h
  have hsiny_lt_one : sin y < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hy1
    simpa [Real.sin_pi_div_two] using h
  have h_cos_le_one : cos l ≤ 1 := Real.cos_le_one l
  have hcosx_sq_eq : cos x ^ 2 = 1 - sin x ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq x]
  have hcosy_sq_eq : cos y ^ 2 = 1 - sin y ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq y]
  rw [hcosx_sq_eq, hcosy_sq_eq]
  have hsinx_sq_lt_one : sin x ^ 2 < 1 := by
    nlinarith
  have hsiny_sq_lt_one : sin y ^ 2 < 1 := by
    nlinarith
  have h_denom_x_pos : 0 < 1 - sin x ^ 2 := by linarith
  have h_denom_y_pos : 0 < 1 - sin y ^ 2 := by linarith
  rw [div_le_div_iff₀ h_denom_y_pos h_denom_x_pos]
  nlinarith

theorem tanAng_monotoneOn_l (h : ℝ) (hh : 0 ≤ h ∧ h < π / 2) :
    MonotoneOn (fun l => tanAng l h) (Set.Ico 0 π) := by
  rcases hh with ⟨hh0, hh2⟩
  intro x hx y hy hxy
  rcases hx with ⟨hx0, hxπ⟩
  rcases hy with ⟨hy0, hyπ⟩
  have hx2 : x / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> nlinarith
  have hy2 : y / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> nlinarith
  have htanx2_le_htany2 : tan (x / 2) ≤ tan (y / 2) :=
    Real.strictMonoOn_tan.monotoneOn hx2 hy2 (by nlinarith)
  have htan_h_nonneg : 0 ≤ tan h :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hh0 (by nlinarith)
  have h_mul : tan h * tan (x / 2) ≤ tan h * tan (y / 2) :=
    mul_le_mul_of_nonneg_left htanx2_le_htany2 htan_h_nonneg
  have h_neg : -(tan h * tan (y / 2)) ≤ -(tan h * tan (x / 2)) := by nlinarith
  have h_arccos : arccos (-(tan h * tan (x / 2))) ≤ arccos (-(tan h * tan (y / 2))) :=
    Real.arccos_le_arccos h_neg
  unfold tanAng
  exact h_arccos

theorem tanAng_monotoneOn_h (l : ℝ) (hl : 0 ≤ l ∧ l < π) :
    MonotoneOn (fun h => tanAng l h) (Set.Ico 0 (π / 2)) := by
  rcases hl with ⟨hl0, hl1⟩
  intro x hx y hy hxy
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  unfold tanAng
  have hx_mem : x ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> linarith
  have hy_mem : y ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> linarith
  have htan : tan x ≤ tan y := by
    by_cases hxy' : x < y
    · exact (Real.strictMonoOn_tan hx_mem hy_mem hxy').le
    · have h_eq : x = y := by linarith
      subst h_eq
      exact le_refl _
  have htan_nonneg : 0 ≤ tan (l / 2) := by
    apply Real.tan_nonneg_of_nonneg_of_le_pi_div_two
    · nlinarith
    · nlinarith
  have hprod : tan x * tan (l / 2) ≤ tan y * tan (l / 2) :=
    mul_le_mul_of_nonneg_right htan htan_nonneg
  have hneg : -(tan y * tan (l / 2)) ≤ -(tan x * tan (l / 2)) := by linarith
  exact antitone_arccos hneg

/-- The worst-end bound on a piece `[a, b]` of `[dlo, dhi]`. -/
theorem hexPoly_lower (a b d : ℝ) (ha : dlo ≤ a) (had : a ≤ d) (hdb : d ≤ b) (hb : b ≤ dhi) :
    2 * tanLen a (hrad a) + 8 * chordC (hrad a) ((2 * π - 2 * tanAng b (hrad b)) / 4) ≤
      hexPoly d (hrad d) := by
  unfold hexPoly
  have ha_pos : 0 < a := by
    have h := pi_div_four_lt_dlo
    linarith [pi_pos]
  have ha_lt_pi_div_two : a < π / 2 := by
    have h := dhi_lt_pi_div_three
    linarith
  have ha_lt_pi : a < π := by linarith [pi_pos]
  have hd_pos : 0 < d := by linarith
  have hd_lt_pi_div_two : d < π / 2 := by
    have h := dhi_lt_pi_div_three
    linarith
  have hd_lt_pi : d < π := by linarith
  have hb_pos : 0 < b := by linarith
  have hb_lt_pi_div_two : b < π / 2 := by
    have h := dhi_lt_pi_div_three
    linarith
  have hb_lt_pi : b < π := by linarith
  have ha_nonneg : 0 ≤ a := by linarith
  have ha_le_pi : a ≤ π := by linarith
  have hd_nonneg : 0 ≤ d := by linarith
  have hd_le_pi : d ≤ π := by linarith
  have hb_nonneg : 0 ≤ b := by linarith
  have hb_le_pi : b ≤ π := by linarith
  have hrad_a_bounds := hrad_bounds a ⟨ha_pos, ha_lt_pi_div_two⟩
  have hrad_a_pos : 0 < hrad a := by linarith
  have hrad_a_lt_a : hrad a < a := hrad_a_bounds.2
  have hrad_a_lt_pi_div_two : hrad a < π / 2 := by linarith
  have hrad_d_bounds := hrad_bounds d ⟨hd_pos, hd_lt_pi_div_two⟩
  have hrad_d_pos : 0 < hrad d := by linarith
  have hrad_d_lt_d : hrad d < d := hrad_d_bounds.2
  have hrad_d_lt_pi_div_two : hrad d < π / 2 := by linarith
  have hrad_b_bounds := hrad_bounds b ⟨hb_pos, hb_lt_pi_div_two⟩
  have hrad_b_pos : 0 < hrad b := by linarith
  have hrad_b_lt_b : hrad b < b := hrad_b_bounds.2
  have hrad_b_lt_pi_div_two : hrad b < π / 2 := by linarith
  have hrad_a_nonneg : 0 ≤ hrad a := by linarith
  have hrad_d_nonneg : 0 ≤ hrad d := by linarith
  have hrad_b_nonneg : 0 ≤ hrad b := by linarith
  have ha_mem_Ioo : a ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨ha_pos, ha_lt_pi_div_two⟩
  have hd_mem_Ioo : d ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hd_pos, hd_lt_pi_div_two⟩
  have hb_mem_Ioo : b ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hb_pos, hb_lt_pi_div_two⟩
  have hrad_a_mem_Ico : hrad a ∈ Set.Ico (0 : ℝ) (π / 2) :=
    Set.mem_Ico.mpr ⟨hrad_a_nonneg, hrad_a_lt_pi_div_two⟩
  have hrad_d_mem_Ico : hrad d ∈ Set.Ico (0 : ℝ) (π / 2) :=
    Set.mem_Ico.mpr ⟨hrad_d_nonneg, hrad_d_lt_pi_div_two⟩
  have hrad_b_mem_Ico : hrad b ∈ Set.Ico (0 : ℝ) (π / 2) :=
    Set.mem_Ico.mpr ⟨hrad_b_nonneg, hrad_b_lt_pi_div_two⟩
  have hrad_a_mem_Icc : hrad a ∈ Set.Icc (0 : ℝ) (π / 2) :=
    Set.mem_Icc.mpr ⟨hrad_a_nonneg, by linarith⟩
  have hrad_d_mem_Icc : hrad d ∈ Set.Icc (0 : ℝ) (π / 2) :=
    Set.mem_Icc.mpr ⟨hrad_d_nonneg, by linarith⟩
  have hrad_a_le_rad_d : hrad a ≤ hrad d :=
    hrad_strictMonoOn.monotoneOn ha_mem_Ioo hd_mem_Ioo had
  have hrad_d_le_rad_b : hrad d ≤ hrad b :=
    hrad_strictMonoOn.monotoneOn hd_mem_Ioo hb_mem_Ioo hdb
  have h_tanLen1 : tanLen a (hrad a) ≤ tanLen a (hrad d) :=
    tanLen_monotoneOn_h a ⟨ha_nonneg, ha_le_pi⟩ hrad_a_mem_Ico hrad_d_mem_Ico hrad_a_le_rad_d
  have h_tanLen2 : tanLen a (hrad d) ≤ tanLen d (hrad d) :=
    tanLen_monotoneOn_l (hrad d) ⟨hrad_d_nonneg, hrad_d_lt_pi_div_two⟩
      (Set.mem_Icc.mpr ⟨ha_nonneg, ha_le_pi⟩) (Set.mem_Icc.mpr ⟨hd_nonneg, hd_le_pi⟩) had
  have h_tanAng1 : tanAng d (hrad d) ≤ tanAng d (hrad b) :=
    tanAng_monotoneOn_h d ⟨hd_nonneg, hd_lt_pi⟩ hrad_d_mem_Ico hrad_b_mem_Ico hrad_d_le_rad_b
  have h_tanAng2 : tanAng d (hrad b) ≤ tanAng b (hrad b) :=
    tanAng_monotoneOn_l (hrad b) ⟨hrad_b_nonneg, hrad_b_lt_pi_div_two⟩
      (Set.mem_Ico.mpr ⟨hd_nonneg, hd_lt_pi⟩) (Set.mem_Ico.mpr ⟨hb_nonneg, hb_lt_pi⟩) hdb
  have h_tanAng : tanAng d (hrad d) ≤ tanAng b (hrad b) := by linarith
  have h_step : (2 * π - 2 * tanAng b (hrad b)) / 4 ≤ (2 * π - 2 * tanAng d (hrad d)) / 4 := by
    have h : 2 * π - 2 * tanAng b (hrad b) ≤ 2 * π - 2 * tanAng d (hrad d) := by linarith
    linarith
  have h_tanAng_d_nonneg : 0 ≤ tanAng d (hrad d) := Real.arccos_nonneg _
  have h_tanAng_d_le_pi : tanAng d (hrad d) ≤ π := Real.arccos_le_pi _
  have h_tanAng_b_nonneg : 0 ≤ tanAng b (hrad b) := Real.arccos_nonneg _
  have h_tanAng_b_le_pi : tanAng b (hrad b) ≤ π := Real.arccos_le_pi _
  have h_step_nonneg : 0 ≤ (2 * π - 2 * tanAng b (hrad b)) / 4 := by
    have : 0 ≤ 2 * π - 2 * tanAng b (hrad b) := by linarith
    linarith
  have h_step_le_pi : (2 * π - 2 * tanAng b (hrad b)) / 4 ≤ π := by
    have : 2 * π - 2 * tanAng b (hrad b) ≤ 2 * π := by linarith
    linarith
  have h_step_d_nonneg : 0 ≤ (2 * π - 2 * tanAng d (hrad d)) / 4 := by
    have : 0 ≤ 2 * π - 2 * tanAng d (hrad d) := by linarith
    linarith
  have h_step_d_le_pi : (2 * π - 2 * tanAng d (hrad d)) / 4 ≤ π := by
    have : 2 * π - 2 * tanAng d (hrad d) ≤ 2 * π := by linarith
    linarith
  have h_chord1 : chordC (hrad a) ((2 * π - 2 * tanAng b (hrad b)) / 4) ≤
      chordC (hrad a) ((2 * π - 2 * tanAng d (hrad d)) / 4) :=
    chordC_monotoneOn_s (hrad a) (Set.mem_Icc.mpr ⟨h_step_nonneg, h_step_le_pi⟩)
      (Set.mem_Icc.mpr ⟨h_step_d_nonneg, h_step_d_le_pi⟩) h_step
  have h_chord2 : chordC (hrad a) ((2 * π - 2 * tanAng d (hrad d)) / 4) ≤
      chordC (hrad d) ((2 * π - 2 * tanAng d (hrad d)) / 4) :=
    chordC_monotoneOn_h ((2 * π - 2 * tanAng d (hrad d)) / 4)
      ⟨h_step_d_nonneg, h_step_d_le_pi⟩ hrad_a_mem_Icc hrad_d_mem_Icc hrad_a_le_rad_d
  have h_total : 2 * tanLen a (hrad a) + 8 * chordC (hrad a) ((2 * π - 2 * tanAng b (hrad b)) / 4) ≤
      2 * tanLen d (hrad d) + 8 * chordC (hrad d) ((2 * π - 2 * tanAng d (hrad d)) / 4) := by
    linarith
  exact h_total

/-! ## The pieces from rational checkpoints

Each piece inequality `hex_piece_i` follows from three monotone ends at rational checkpoints `T1`, `G`, `T2`
(`hex_piece_of`), and each end reduces, through `cos (hrad a) = cos a / cos (a/2)`, to enclosures of `cos` and
`sin` at `a`, `a/2` and the checkpoints (`Numerics/HexData.lean`, generated and checked by
code/lean/numerics/pieces.gp; paper, Proposition onehex). -/

/-- The piece inequality from its three monotone ends. -/
theorem hex_piece_of {a b T1 G T2 : ℝ} (h1 : T1 ≤ tanLen a (hrad a)) (h2 : tanAng b (hrad b) ≤ G)
    (hG : G ≤ π) (h3 : T2 ≤ chordC (hrad a) ((2 * π - 2 * G) / 4)) (h4 : 6 * b < 2 * T1 + 8 * T2) :
    6 * b < 2 * tanLen a (hrad a) + 8 * chordC (hrad a) ((2 * π - 2 * tanAng b (hrad b)) / 4) := by
  have htanAng_nonneg : 0 ≤ tanAng b (hrad b) := by
    unfold tanAng
    exact Real.arccos_nonneg _
  have htanAng_le_pi : tanAng b (hrad b) ≤ π := by
    unfold tanAng
    exact Real.arccos_le_pi _
  have h_sG_mem : (2 * π - 2 * G) / 4 ∈ Set.Icc (0 : ℝ) π := by
    constructor
    · have : 0 ≤ 2 * π - 2 * G := by linarith
      positivity
    · have : 2 * π - 2 * G ≤ 4 * π := by linarith
      linarith
  have h_sb_mem : (2 * π - 2 * tanAng b (hrad b)) / 4 ∈ Set.Icc (0 : ℝ) π := by
    constructor
    · have : 0 ≤ 2 * π - 2 * tanAng b (hrad b) := by linarith
      positivity
    · have : 2 * π - 2 * tanAng b (hrad b) ≤ 4 * π := by linarith
      linarith
  have h_sG_le_sb : (2 * π - 2 * G) / 4 ≤ (2 * π - 2 * tanAng b (hrad b)) / 4 := by
    have : 2 * π - 2 * G ≤ 2 * π - 2 * tanAng b (hrad b) := by linarith
    linarith
  have h_chord_le : chordC (hrad a) ((2 * π - 2 * G) / 4) ≤
      chordC (hrad a) ((2 * π - 2 * tanAng b (hrad b)) / 4) :=
    chordC_monotoneOn_s (hrad a) h_sG_mem h_sb_mem h_sG_le_sb
  linarith

/-- Lower end of the tangent segment: `cos (hrad a) = ρ = cos a / cos (a/2) ≤ C / L`, and
`(cos a - sin² h) / cos² h = 1 - (1 - cos a) / ρ² ≤ 1 - (1 - C) L² / C²`. -/
theorem le_tanLen_hrad {a t C L K : ℝ} (hc0 : 0 < cos a) (hcC : cos a ≤ C) (hL0 : 0 < L)
    (hL : L ≤ cos (a / 2)) (hCL : C ≤ L) (ht0 : 0 ≤ t) (htπ : t ≤ π) (hK : K ≤ cos t)
    (hY : 1 - (1 - C) * L ^ 2 / C ^ 2 ≤ K) : t ≤ tanLen a (hrad a) := by
  have hh0 : 0 < cos (a / 2) := lt_of_lt_of_le hL0 hL
  have hC0 : 0 < C := lt_of_lt_of_le hc0 hcC
  have hC1 : C ≤ 1 := le_trans hCL (le_trans hL (cos_le_one _))
  have hρ0 : 0 < cos a / cos (a / 2) := div_pos hc0 hh0
  have hρL : cos a / cos (a / 2) * L ≤ C := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hh0]
    nlinarith
  have hρ1 : cos a / cos (a / 2) ≤ 1 := by
    rw [div_le_one hh0]; linarith
  have hcos : cos (hrad a) = cos a / cos (a / 2) := by
    unfold hrad; exact Real.cos_arccos (by linarith) hρ1
  have hsin : sin (hrad a) ^ 2 = 1 - (cos a / cos (a / 2)) ^ 2 := by rw [Real.sin_sq, hcos]
  unfold tanLen
  rw [hcos, hsin]
  apply Numerics.le_arccos_of_le_cos ht0 htπ
  set ρ := cos a / cos (a / 2) with hρ
  have e1 : 1 - C ≤ 1 - cos a := by linarith
  have e2 : L ^ 2 / C ^ 2 ≤ 1 / ρ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 0 ≤ ρ * L := by positivity
    nlinarith
  have e3 : (1 - C) * (L ^ 2 / C ^ 2) ≤ (1 - cos a) * (1 / ρ ^ 2) :=
    mul_le_mul e1 e2 (by positivity) (by linarith)
  have eq : (cos a - (1 - ρ ^ 2)) / ρ ^ 2 = 1 - (1 - cos a) * (1 / ρ ^ 2) := by
    field_simp
    ring
  have eq2 : (1 - C) * L ^ 2 / C ^ 2 = (1 - C) * (L ^ 2 / C ^ 2) := by ring
  rw [eq]
  linarith

/-- Upper end of the angle at the centre: `X = tan (hrad b) tan (b/2)`, `X² = (1 - ρ²)/ρ² · sin² (b/2) / cos² (b/2)`
with `ρ = cos b / cos (b/2) ≥ c / H1`, so `X ≤ M` and `cos G ≤ -M ≤ -X`. -/
theorem tanAng_hrad_le {b G c H1 H2 S M : ℝ} (hc0 : 0 < c) (hc : c ≤ cos b) (hH1 : cos (b / 2) ≤ H1)
    (hH20 : 0 < H2) (hH2 : H2 ≤ cos (b / 2)) (hρ : cos b ≤ cos (b / 2)) (hS0 : 0 ≤ sin (b / 2))
    (hS : sin (b / 2) ≤ S) (hM0 : 0 ≤ M) (hM : (H1 ^ 2 - c ^ 2) / c ^ 2 * (S ^ 2 / H2 ^ 2) ≤ M ^ 2)
    (hG0 : 0 ≤ G) (hGπ : G ≤ π) (hG : cos G ≤ -M) : tanAng b (hrad b) ≤ G := by
  have hh0 : 0 < cos (b / 2) := lt_of_lt_of_le hH20 hH2
  have hcb : 0 < cos b := lt_of_lt_of_le hc0 hc
  have hρ0 : 0 < cos b / cos (b / 2) := div_pos hcb hh0
  have hρ1 : cos b / cos (b / 2) ≤ 1 := by rw [div_le_one hh0]; exact hρ
  have hρc : c ≤ cos b / cos (b / 2) * H1 := by
    calc c ≤ cos b := hc
      _ = cos b / cos (b / 2) * cos (b / 2) := by field_simp
      _ ≤ cos b / cos (b / 2) * H1 := mul_le_mul_of_nonneg_left hH1 hρ0.le
  have htan : tan (hrad b) = √(1 - (cos b / cos (b / 2)) ^ 2) / (cos b / cos (b / 2)) := by
    unfold hrad; exact Real.tan_arccos _
  have htanb : tan (b / 2) = sin (b / 2) / cos (b / 2) := Real.tan_eq_sin_div_cos _
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = cos b / cos (b / 2) := ⟨_, rfl⟩
  rw [← hρdef] at hρ0 hρ1 hρc htan
  have h1ρ : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have hX0 : 0 ≤ tan (hrad b) * tan (b / 2) := by rw [htan, htanb]; positivity
  have hX2 : (tan (hrad b) * tan (b / 2)) ^ 2 =
      (1 - ρ ^ 2) / ρ ^ 2 * (sin (b / 2) ^ 2 / cos (b / 2) ^ 2) := by
    rw [htan, htanb, mul_pow, div_pow, div_pow, Real.sq_sqrt h1ρ]
  have hH1c : c ≤ H1 := le_trans hc (le_trans hρ hH1)
  have hXM : tan (hrad b) * tan (b / 2) ≤ M := by
    have h2 : (tan (hrad b) * tan (b / 2)) ^ 2 ≤ M ^ 2 := by
      rw [hX2]
      refine le_trans ?_ hM
      apply mul_le_mul
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_self_le_mul_self hc0.le hρc
        nlinarith
      · exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hS0 hS 2) (by positivity)
          (pow_le_pow_left₀ hH20.le hH2 2)
      · positivity
      · apply div_nonneg _ (by positivity)
        nlinarith
    exact (pow_le_pow_iff_left₀ hX0 hM0 two_ne_zero).mp h2
  unfold tanAng
  apply Numerics.arccos_le_of_cos_le hG0 hGπ
  linarith

/-- Lower end of the chord: `cos² h + sin² h cos s = ρ² + (1 - ρ²) cos s ≤ R + (1 - R) Kc`, `R = C² / L²`. -/
theorem le_chordC_hrad {a s t C L Kc K : ℝ} (hc0 : 0 < cos a) (hcC : cos a ≤ C) (hL0 : 0 < L)
    (hL : L ≤ cos (a / 2)) (hCL : C ≤ L) (hs : cos s ≤ Kc) (hKc : Kc ≤ 1) (ht0 : 0 ≤ t)
    (htπ : t ≤ π) (hK : K ≤ cos t) (hY : C ^ 2 / L ^ 2 + (1 - C ^ 2 / L ^ 2) * Kc ≤ K) :
    t ≤ chordC (hrad a) s := by
  have hh0 : 0 < cos (a / 2) := lt_of_lt_of_le hL0 hL
  have hC0 : 0 < C := lt_of_lt_of_le hc0 hcC
  have hρ0 : 0 < cos a / cos (a / 2) := div_pos hc0 hh0
  have hρL : cos a / cos (a / 2) * L ≤ C := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hh0]
    nlinarith
  have hρ1 : cos a / cos (a / 2) ≤ 1 := by
    rw [div_le_one hh0]; linarith
  have hcos : cos (hrad a) = cos a / cos (a / 2) := by
    unfold hrad; exact Real.cos_arccos (by linarith) hρ1
  have hsin : sin (hrad a) ^ 2 = 1 - (cos a / cos (a / 2)) ^ 2 := by rw [Real.sin_sq, hcos]
  unfold chordC
  rw [hcos, hsin]
  apply Numerics.le_arccos_of_le_cos ht0 htπ
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = cos a / cos (a / 2) := ⟨_, rfl⟩
  rw [← hρdef] at hρ0 hρL hρ1 ⊢
  have hR : ρ ^ 2 ≤ C ^ 2 / L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_self_le_mul_self (by positivity) hρL
    nlinarith
  have hR1 : C ^ 2 / L ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hρ2 : ρ ^ 2 ≤ 1 := le_trans hR hR1
  have e1 : ρ ^ 2 + (1 - ρ ^ 2) * cos s ≤ ρ ^ 2 + (1 - ρ ^ 2) * Kc :=
    by nlinarith
  have e2 : ρ ^ 2 + (1 - ρ ^ 2) * Kc ≤ C ^ 2 / L ^ 2 + (1 - C ^ 2 / L ^ 2) * Kc := by
    nlinarith
  linarith

open Numerics

theorem hex_piece_0 : 6 * dpt 1 < 2 * tanLen (dpt 0) (hrad (dpt 0)) +
    8 * chordC (hrad (dpt 0)) ((2 * π - 2 * tanAng (dpt 1) (hrad (dpt 1))) / 4) := by
  have ha : dpt 0 = 357719/1200000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 0 / 2 = 357719/2400000 * π := by rw [ha]; ring
  have hb : dpt 1 = 2158369/7200000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 1 / 2 = 2158369/14400000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 703/1500 * π) (G := 125393/180000 * π) (T2 := 667/6000 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 296302953/500000000) (L := 223089521/250000000) (K := 49138837/500000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_0 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_0
    · rw [ha]; exact cos_dpt_le_0
    · rw [ha2]; exact le_cos_hdpt_0
  · refine tanAng_hrad_le (c := 117672169/200000000) (H1 := 222792003/250000000) (H2 := 891168009/1000000000) (S := 453673427/1000000000) (M := 11582833/20000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_0 (by norm_num))
    · rw [hb]; exact le_cos_dpt_1
    · rw [hb2]; exact cos_hdpt_le_1
    · rw [hb2]; exact le_cos_hdpt_1
    · rw [hb2, hb]; exact le_trans cos_dpt_le_1 (le_trans (by norm_num) le_cos_hdpt_1)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_1
  · have hs : (2 * π - 2 * (125393/180000 * π)) / 4 = 54607/360000 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 296302953/500000000) (L := 223089521/250000000) (Kc := 177717843/200000000) (K := 939632911/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_0 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_0 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_0
    · rw [ha]; exact cos_dpt_le_0
    · rw [ha2]; exact le_cos_hdpt_0

theorem hex_piece_1 : 6 * dpt 2 < 2 * tanLen (dpt 1) (hrad (dpt 1)) +
    8 * chordC (hrad (dpt 1)) ((2 * π - 2 * tanAng (dpt 2) (hrad (dpt 2))) / 4) := by
  have ha : dpt 1 = 2158369/7200000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 1 / 2 = 2158369/14400000 * π := by rw [ha]; ring
  have hb : dpt 2 = 271303/900000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 2 / 2 = 271303/1800000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 2141/4500 * π) (G := 31523/45000 * π) (T2 := 331/3000 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 36772553/62500000) (L := 891168009/1000000000) (K := 38011467/500000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_1 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_1
    · rw [ha]; exact cos_dpt_le_1
    · rw [ha2]; exact le_cos_hdpt_1
  · refine tanAng_hrad_le (c := 584099509/1000000000) (H1 := 444985887/500000000) (H2 := 889971771/1000000000) (S := 22800781/50000000) (M := 29452079/50000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_1 (by norm_num))
    · rw [hb]; exact le_cos_dpt_2
    · rw [hb2]; exact cos_hdpt_le_2
    · rw [hb2]; exact le_cos_hdpt_2
    · rw [hb2, hb]; exact le_trans cos_dpt_le_2 (le_trans (by norm_num) le_cos_hdpt_2)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_2
  · have hs : (2 * π - 2 * (31523/45000 * π)) / 4 = 13477/90000 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 36772553/62500000) (L := 891168009/1000000000) (Kc := 35654829/40000000) (K := 470262763/500000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_1 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_1 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_1
    · rw [ha]; exact cos_dpt_le_1
    · rw [ha2]; exact le_cos_hdpt_1

theorem hex_piece_2 : 6 * dpt 3 < 2 * tanLen (dpt 2) (hrad (dpt 2)) +
    8 * chordC (hrad (dpt 2)) ((2 * π - 2 * tanAng (dpt 3) (hrad (dpt 3))) / 4) := by
  have ha : dpt 2 = 271303/900000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 2 / 2 = 271303/1800000 * π := by rw [ha]; ring
  have hb : dpt 3 = 727493/2400000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 3 / 2 = 727493/4800000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 1739/3600 * π) (G := 126809/180000 * π) (T2 := 219/2000 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 73012439/125000000) (L := 889971771/1000000000) (K := 53207403/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_2 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_2
    · rw [ha]; exact cos_dpt_le_2
    · rw [ha2]; exact le_cos_hdpt_2
  · refine tanAng_hrad_le (c := 144955503/250000000) (H1 := 888769379/1000000000) (H2 := 27774043/31250000) (S := 22917733/50000000) (M := 59911559/100000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_2 (by norm_num))
    · rw [hb]; exact le_cos_dpt_3
    · rw [hb2]; exact cos_hdpt_le_3
    · rw [hb2]; exact le_cos_hdpt_3
    · rw [hb2, hb]; exact le_trans cos_dpt_le_3 (le_trans (by norm_num) le_cos_hdpt_3)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_3
  · have hs : (2 * π - 2 * (126809/180000 * π)) / 4 = 53191/360000 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 73012439/125000000) (L := 889971771/1000000000) (Kc := 894189403/1000000000) (K := 188282339/200000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_2 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_2 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_2
    · rw [ha]; exact cos_dpt_le_2
    · rw [ha2]; exact le_cos_hdpt_2

theorem hex_piece_3 : 6 * dpt 4 < 2 * tanLen (dpt 3) (hrad (dpt 3)) +
    8 * chordC (hrad (dpt 3)) ((2 * π - 2 * tanAng (dpt 4) (hrad (dpt 4))) / 4) := by
  have ha : dpt 3 = 727493/2400000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 3 / 2 = 727493/4800000 * π := by rw [ha]; ring
  have hb : dpt 4 = 1097267/3600000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 4 / 2 = 1097267/7200000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 981/2000 * π) (G := 63773/90000 * π) (T2 := 391/3600 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 115964403/200000000) (L := 27774043/31250000) (K := 14920349/500000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_3 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_3
    · rw [ha]; exact cos_dpt_le_3
    · rw [ha2]; exact le_cos_hdpt_3
  · refine tanAng_hrad_le (c := 575528473/1000000000) (H1 := 887560837/1000000000) (H2 := 443780417/500000000) (S := 46069053/100000000) (M := 60936793/100000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_3 (by norm_num))
    · rw [hb]; exact le_cos_dpt_4
    · rw [hb2]; exact cos_hdpt_le_4
    · rw [hb2]; exact le_cos_hdpt_4
    · rw [hb2, hb]; exact le_trans cos_dpt_le_4 (le_trans (by norm_num) le_cos_hdpt_4)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_4
  · have hs : (2 * π - 2 * (63773/90000 * π)) / 4 = 26227/180000 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 115964403/200000000) (L := 27774043/31250000) (Kc := 897050217/1000000000) (K := 942349829/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_3 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_3 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_3
    · rw [ha]; exact cos_dpt_le_3
    · rw [ha2]; exact le_cos_hdpt_3

theorem hex_piece_4 : 6 * dpt 5 < 2 * tanLen (dpt 4) (hrad (dpt 4)) +
    8 * chordC (hrad (dpt 4)) ((2 * π - 2 * tanAng (dpt 5) (hrad (dpt 5))) / 4) := by
  have ha : dpt 4 = 1097267/3600000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 4 / 2 = 1097267/7200000 * π := by rw [ha]; ring
  have hb : dpt 5 = 2206589/7200000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 5 / 2 = 2206589/14400000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 2989/6000 * π) (G := 891/1250 * π) (T2 := 323/3000 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 143882119/250000000) (L := 443780417/500000000) (K := 5759553/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_4 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_4
    · rw [ha]; exact cos_dpt_le_4
    · rw [ha2]; exact le_cos_hdpt_4
  · refine tanAng_hrad_le (c := 571219011/1000000000) (H1 := 221586539/250000000) (H2 := 886346153/1000000000) (S := 115755803/250000000) (M := 61980297/100000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_4 (by norm_num))
    · rw [hb]; exact le_cos_dpt_5
    · rw [hb2]; exact cos_hdpt_le_5
    · rw [hb2]; exact le_cos_hdpt_5
    · rw [hb2, hb]; exact le_trans cos_dpt_le_5 (le_trans (by norm_num) le_cos_hdpt_5)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_5
  · have hs : (2 * π - 2 * (891/1250 * π)) / 4 = 359/2500 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 143882119/250000000) (L := 443780417/500000000) (Kc := 899953839/1000000000) (K := 188667709/200000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_4 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_4 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_4
    · rw [ha]; exact cos_dpt_le_4
    · rw [ha2]; exact le_cos_hdpt_4

theorem hex_piece_5 : 6 * dpt 6 < 2 * tanLen (dpt 5) (hrad (dpt 5)) +
    8 * chordC (hrad (dpt 5)) ((2 * π - 2 * tanAng (dpt 6) (hrad (dpt 6))) / 4) := by
  have ha : dpt 5 = 2206589/7200000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 5 / 2 = 2206589/14400000 * π := by rw [ha]; ring
  have hb : dpt 6 = 61629/200000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 6 / 2 = 61629/400000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 9109/18000 * π) (G := 10757/15000 * π) (T2 := 8/75 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 285609507/500000000) (L := 886346153/1000000000) (K := -19022943/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_5 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_5
    · rw [ha]; exact cos_dpt_le_5
    · rw [ha2]; exact le_cos_hdpt_5
  · refine tanAng_hrad_le (c := 35430859/62500000) (H1 := 177025069/200000000) (H2 := 442562671/500000000) (S := 465352693/1000000000) (M := 1970079/3125000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_5 (by norm_num))
    · rw [hb]; exact le_cos_dpt_6
    · rw [hb2]; exact cos_hdpt_le_6
    · rw [hb2]; exact le_cos_hdpt_6
    · rw [hb2, hb]; exact le_trans cos_dpt_le_6 (le_trans (by norm_num) le_cos_hdpt_6)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_6
  · have hs : (2 * π - 2 * (10757/15000 * π)) / 4 = 4243/30000 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 285609507/500000000) (L := 886346153/1000000000) (Kc := 56431289/62500000) (K := 944376369/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_5 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_5 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_5
    · rw [ha]; exact cos_dpt_le_5
    · rw [ha2]; exact le_cos_hdpt_5

theorem hex_piece_6 : 6 * dpt 7 < 2 * tanLen (dpt 6) (hrad (dpt 6)) +
    8 * chordC (hrad (dpt 6)) ((2 * π - 2 * tanAng (dpt 7) (hrad (dpt 7))) / 4) := by
  have ha : dpt 6 = 61629/200000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 6 / 2 = 61629/400000 * π := by rw [ha]; ring
  have hb : dpt 7 = 2230699/7200000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 7 / 2 = 2230699/14400000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 4627/9000 * π) (G := 129887/180000 * π) (T2 := 1901/18000 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 566893747/1000000000) (L := 442562671/500000000) (K := -8863369/200000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_6 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_6
    · rw [ha]; exact cos_dpt_le_6
    · rw [ha2]; exact le_cos_hdpt_6
  · refine tanAng_hrad_le (c := 562552793/1000000000) (H1 := 88389841/100000000) (H2 := 883898407/1000000000) (S := 233839477/500000000) (M := 64123953/100000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_6 (by norm_num))
    · rw [hb]; exact le_cos_dpt_7
    · rw [hb2]; exact cos_hdpt_le_7
    · rw [hb2]; exact le_cos_hdpt_7
    · rw [hb2, hb]; exact le_trans cos_dpt_le_7 (le_trans (by norm_num) le_cos_hdpt_7)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_7
  · have hs : (2 * π - 2 * (129887/180000 * π)) / 4 = 50113/360000 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 566893747/1000000000) (L := 442562671/500000000) (Kc := 905890599/1000000000) (K := 945461737/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_6 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_6 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_6
    · rw [ha]; exact cos_dpt_le_6
    · rw [ha2]; exact le_cos_hdpt_6

theorem hex_piece_7 : 6 * dpt 8 < 2 * tanLen (dpt 7) (hrad (dpt 7)) +
    8 * chordC (hrad (dpt 7)) ((2 * π - 2 * tanAng (dpt 8) (hrad (dpt 8))) / 4) := by
  have ha : dpt 7 = 2230699/7200000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 7 / 2 = 2230699/14400000 * π := by rw [ha]; ring
  have hb : dpt 8 = 1121377/3600000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 8 / 2 = 1121377/7200000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 2351/4500 * π) (G := 65357/90000 * π) (T2 := 209/2000 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 140638199/250000000) (L := 883898407/1000000000) (K := -70452889/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_7 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_7
    · rw [ha]; exact cos_dpt_le_7
    · rw [ha2]; exact le_cos_hdpt_7
  · refine tanAng_hrad_le (c := 279098139/500000000) (H1 := 882665363/1000000000) (H2 := 11033317/12500000) (S := 470001981/1000000000) (M := 65225059/100000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_7 (by norm_num))
    · rw [hb]; exact le_cos_dpt_8
    · rw [hb2]; exact cos_hdpt_le_8
    · rw [hb2]; exact le_cos_hdpt_8
    · rw [hb2, hb]; exact le_trans cos_dpt_le_8 (le_trans (by norm_num) le_cos_hdpt_8)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_8
  · have hs : (2 * π - 2 * (65357/90000 * π)) / 4 = 24643/180000 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 140638199/250000000) (L := 883898407/1000000000) (Kc := 908923439/1000000000) (K := 473296499/500000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_7 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_7 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_7
    · rw [ha]; exact cos_dpt_le_7
    · rw [ha2]; exact le_cos_hdpt_7

theorem hex_piece_8 : 6 * dpt 9 < 2 * tanLen (dpt 8) (hrad (dpt 8)) +
    8 * chordC (hrad (dpt 8)) ((2 * π - 2 * tanAng (dpt 9) (hrad (dpt 9))) / 4) := by
  have ha : dpt 8 = 1121377/3600000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 8 / 2 = 1121377/7200000 * π := by rw [ha]; ring
  have hb : dpt 9 = 751603/2400000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 9 / 2 = 751603/4800000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 531/1000 * π) (G := 131567/180000 * π) (T2 := 1859/18000 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 558196281/1000000000) (L := 11033317/12500000) (K := -19447099/200000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_8 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_8
    · rw [ha]; exact cos_dpt_le_8
    · rw [ha2]; exact le_cos_hdpt_8
  · refine tanAng_hrad_le (c := 553824319/1000000000) (H1 := 881426209/1000000000) (H2 := 440713103/500000000) (S := 118080439/250000000) (M := 1326927/2000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_8 (by norm_num))
    · rw [hb]; exact le_cos_dpt_9
    · rw [hb2]; exact cos_hdpt_le_9
    · rw [hb2]; exact le_cos_hdpt_9
    · rw [hb2, hb]; exact le_trans cos_dpt_le_9 (le_trans (by norm_num) le_cos_hdpt_9)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_9
  · have hs : (2 * π - 2 * (131567/180000 * π)) / 4 = 48433/360000 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 558196281/1000000000) (L := 11033317/12500000) (Kc := 91200203/100000000) (K := 947824063/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_8 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_8 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_8
    · rw [ha]; exact cos_dpt_le_8
    · rw [ha2]; exact le_cos_hdpt_8

theorem hex_piece_9 : 6 * dpt 10 < 2 * tanLen (dpt 9) (hrad (dpt 9)) +
    8 * chordC (hrad (dpt 9)) ((2 * π - 2 * tanAng (dpt 10) (hrad (dpt 10))) / 4) := by
  have ha : dpt 9 = 751603/2400000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 9 / 2 = 751603/4800000 * π := by rw [ha]; ring
  have hb : dpt 10 = 141679/450000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 10 / 2 = 141679/900000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine hex_piece_of (T1 := 2429/4500 * π) (G := 4139/5625 * π) (T2 := 51/500 * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)
  · refine le_tanLen_hrad (C := 276912161/500000000) (L := 440713103/500000000) (K := -62320289/500000000) ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_9 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_9
    · rw [ha]; exact cos_dpt_le_9
    · rw [ha2]; exact le_cos_hdpt_9
  · refine tanAng_hrad_le (c := 549437037/1000000000) (H1 := 5501131/6250000) (H2 := 880180957/1000000000) (S := 94927653/200000000) (M := 16872087/25000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_9 (by norm_num))
    · rw [hb]; exact le_cos_dpt_10
    · rw [hb2]; exact cos_hdpt_le_10
    · rw [hb2]; exact le_cos_hdpt_10
    · rw [hb2, hb]; exact le_trans cos_dpt_le_10 (le_trans (by norm_num) le_cos_hdpt_10)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_10
  · have hs : (2 * π - 2 * (4139/5625 * π)) / 4 = 743/5625 * π := by ring
    rw [hs]
    refine le_chordC_hrad (C := 276912161/500000000) (L := 440713103/500000000) (Kc := 457564313/500000000) (K := 949096143/1000000000) ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_9 (by norm_num) (by positivity) (by nlinarith) le_cos_T2_9 (by norm_num)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_9
    · rw [ha]; exact cos_dpt_le_9
    · rw [ha2]; exact le_cos_hdpt_9

/-- The margin of Proposition onehex in the polygon form. -/
theorem margin_onehex_poly (d : ℝ) (hd : dlo ≤ d ∧ d ≤ dhi) : 6 * d < hexPoly d (hrad d) := by
  rcases hd with ⟨hdlo, hdhi⟩
  by_cases h1 : d ≤ dpt 1
  · -- Case 1: d ≤ dpt 1
    have h0_le_d : dpt 0 ≤ d := by
      rw [dpt_zero]
      exact hdlo
    have h1_le_dhi : dpt 1 ≤ dhi := by
      have h := dpt_mono 1 10 (by decide)
      rw [dpt_ten] at h
      exact h
    have h_lower := hexPoly_lower (dpt 0) (dpt 1) d
      (by rw [dpt_zero])
      h0_le_d h1 h1_le_dhi
    have h_piece := hex_piece_0
    have h_lt : 6 * dpt 1 < hexPoly d (hrad d) := by linarith
    have h_mul : 6 * d ≤ 6 * dpt 1 := by nlinarith
    linarith
  · have h1_lt_d : dpt 1 < d := lt_of_not_ge h1
    by_cases h2 : d ≤ dpt 2
    · -- Case 2: d ≤ dpt 2
      have h1_le_d : dpt 1 ≤ d := h1_lt_d.le
      have h2_le_dhi : dpt 2 ≤ dhi := by
        have h := dpt_mono 2 10 (by decide)
        rw [dpt_ten] at h
        exact h
      have h_lo : dlo ≤ dpt 1 := by
        rw [← dpt_zero]
        exact dpt_mono 0 1 (by decide)
      have h_lower := hexPoly_lower (dpt 1) (dpt 2) d h_lo h1_le_d h2 h2_le_dhi
      have h_piece := hex_piece_1
      have h_lt : 6 * dpt 2 < hexPoly d (hrad d) := by linarith
      have h_mul : 6 * d ≤ 6 * dpt 2 := by nlinarith
      linarith
    · have h2_lt_d : dpt 2 < d := lt_of_not_ge h2
      by_cases h3 : d ≤ dpt 3
      · -- Case 3: d ≤ dpt 3
        have h2_le_d : dpt 2 ≤ d := h2_lt_d.le
        have h3_le_dhi : dpt 3 ≤ dhi := by
          have h := dpt_mono 3 10 (by decide)
          rw [dpt_ten] at h
          exact h
        have h_lo : dlo ≤ dpt 2 := by
          rw [← dpt_zero]
          exact dpt_mono 0 2 (by decide)
        have h_lower := hexPoly_lower (dpt 2) (dpt 3) d h_lo h2_le_d h3 h3_le_dhi
        have h_piece := hex_piece_2
        have h_lt : 6 * dpt 3 < hexPoly d (hrad d) := by linarith
        have h_mul : 6 * d ≤ 6 * dpt 3 := by nlinarith
        linarith
      · have h3_lt_d : dpt 3 < d := lt_of_not_ge h3
        by_cases h4 : d ≤ dpt 4
        · -- Case 4: d ≤ dpt 4
          have h3_le_d : dpt 3 ≤ d := h3_lt_d.le
          have h4_le_dhi : dpt 4 ≤ dhi := by
            have h := dpt_mono 4 10 (by decide)
            rw [dpt_ten] at h
            exact h
          have h_lo : dlo ≤ dpt 3 := by
            rw [← dpt_zero]
            exact dpt_mono 0 3 (by decide)
          have h_lower := hexPoly_lower (dpt 3) (dpt 4) d h_lo h3_le_d h4 h4_le_dhi
          have h_piece := hex_piece_3
          have h_lt : 6 * dpt 4 < hexPoly d (hrad d) := by linarith
          have h_mul : 6 * d ≤ 6 * dpt 4 := by nlinarith
          linarith
        · have h4_lt_d : dpt 4 < d := lt_of_not_ge h4
          by_cases h5 : d ≤ dpt 5
          · -- Case 5: d ≤ dpt 5
            have h4_le_d : dpt 4 ≤ d := h4_lt_d.le
            have h5_le_dhi : dpt 5 ≤ dhi := by
              have h := dpt_mono 5 10 (by decide)
              rw [dpt_ten] at h
              exact h
            have h_lo : dlo ≤ dpt 4 := by
              rw [← dpt_zero]
              exact dpt_mono 0 4 (by decide)
            have h_lower := hexPoly_lower (dpt 4) (dpt 5) d h_lo h4_le_d h5 h5_le_dhi
            have h_piece := hex_piece_4
            have h_lt : 6 * dpt 5 < hexPoly d (hrad d) := by linarith
            have h_mul : 6 * d ≤ 6 * dpt 5 := by nlinarith
            linarith
          · have h5_lt_d : dpt 5 < d := lt_of_not_ge h5
            by_cases h6 : d ≤ dpt 6
            · -- Case 6: d ≤ dpt 6
              have h5_le_d : dpt 5 ≤ d := h5_lt_d.le
              have h6_le_dhi : dpt 6 ≤ dhi := by
                have h := dpt_mono 6 10 (by decide)
                rw [dpt_ten] at h
                exact h
              have h_lo : dlo ≤ dpt 5 := by
                rw [← dpt_zero]
                exact dpt_mono 0 5 (by decide)
              have h_lower := hexPoly_lower (dpt 5) (dpt 6) d h_lo h5_le_d h6 h6_le_dhi
              have h_piece := hex_piece_5
              have h_lt : 6 * dpt 6 < hexPoly d (hrad d) := by linarith
              have h_mul : 6 * d ≤ 6 * dpt 6 := by nlinarith
              linarith
            · have h6_lt_d : dpt 6 < d := lt_of_not_ge h6
              by_cases h7 : d ≤ dpt 7
              · -- Case 7: d ≤ dpt 7
                have h6_le_d : dpt 6 ≤ d := h6_lt_d.le
                have h7_le_dhi : dpt 7 ≤ dhi := by
                  have h := dpt_mono 7 10 (by decide)
                  rw [dpt_ten] at h
                  exact h
                have h_lo : dlo ≤ dpt 6 := by
                  rw [← dpt_zero]
                  exact dpt_mono 0 6 (by decide)
                have h_lower := hexPoly_lower (dpt 6) (dpt 7) d h_lo h6_le_d h7 h7_le_dhi
                have h_piece := hex_piece_6
                have h_lt : 6 * dpt 7 < hexPoly d (hrad d) := by linarith
                have h_mul : 6 * d ≤ 6 * dpt 7 := by nlinarith
                linarith
              · have h7_lt_d : dpt 7 < d := lt_of_not_ge h7
                by_cases h8 : d ≤ dpt 8
                · -- Case 8: d ≤ dpt 8
                  have h7_le_d : dpt 7 ≤ d := h7_lt_d.le
                  have h8_le_dhi : dpt 8 ≤ dhi := by
                    have h := dpt_mono 8 10 (by decide)
                    rw [dpt_ten] at h
                    exact h
                  have h_lo : dlo ≤ dpt 7 := by
                    rw [← dpt_zero]
                    exact dpt_mono 0 7 (by decide)
                  have h_lower := hexPoly_lower (dpt 7) (dpt 8) d h_lo h7_le_d h8 h8_le_dhi
                  have h_piece := hex_piece_7
                  have h_lt : 6 * dpt 8 < hexPoly d (hrad d) := by linarith
                  have h_mul : 6 * d ≤ 6 * dpt 8 := by nlinarith
                  linarith
                · have h8_lt_d : dpt 8 < d := lt_of_not_ge h8
                  by_cases h9 : d ≤ dpt 9
                  · -- Case 9: d ≤ dpt 9
                    have h8_le_d : dpt 8 ≤ d := h8_lt_d.le
                    have h9_le_dhi : dpt 9 ≤ dhi := by
                      have h := dpt_mono 9 10 (by decide)
                      rw [dpt_ten] at h
                      exact h
                    have h_lo : dlo ≤ dpt 8 := by
                      rw [← dpt_zero]
                      exact dpt_mono 0 8 (by decide)
                    have h_lower := hexPoly_lower (dpt 8) (dpt 9) d h_lo h8_le_d h9 h9_le_dhi
                    have h_piece := hex_piece_8
                    have h_lt : 6 * dpt 9 < hexPoly d (hrad d) := by linarith
                    have h_mul : 6 * d ≤ 6 * dpt 9 := by nlinarith
                    linarith
                  · -- Case 10: dpt 9 < d ≤ dhi
                    have h9_lt_d : dpt 9 < d := lt_of_not_ge h9
                    have h9_le_d : dpt 9 ≤ d := h9_lt_d.le
                    have h_d_le_10 : d ≤ dpt 10 := by
                      rw [dpt_ten]
                      exact hdhi
                    have h_lo : dlo ≤ dpt 9 := by
                      rw [← dpt_zero]
                      exact dpt_mono 0 9 (by decide)
                    have h_lower := hexPoly_lower (dpt 9) (dpt 10) d h_lo h9_le_d h_d_le_10 (by
                      rw [dpt_ten])
                    have h_piece := hex_piece_9
                    have h_lt : 6 * dpt 10 < hexPoly d (hrad d) := by linarith
                    have h_mul : 6 * d ≤ 6 * dpt 10 := by nlinarith
                    linarith

end Tammes15
