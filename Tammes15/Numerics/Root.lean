import Tammes15.Numerics.HexData

/-!
# `dlo` lies below `ψ* = arccos u`

`u` is the root in `(1/2, 7/10)` of `13u⁵ - u⁴ + 6u³ + 2u² - 3u - 1`, `ψ* = arccos u = 53.6578501299…°` and
`dlo = 53.65785°`. The quintic is increasing on `[1/2, 7/10]` and positive at `c = 0.592605903`, so `u < c`,
and `c ≤ cos dlo` is the enclosure `le_cos_dpt_0` of Numerics/HexData.lean.
-/

open Real

namespace Tammes15.Numerics

/-- The quintic increases on `[1/2, 7/10]`: a point where it is positive lies above its root. -/
theorem quintic_lt_of_root {u c : ℝ} (h1 : 1 / 2 < u) (h2 : u < 7 / 10) (hc1 : 1 / 2 ≤ c)
    (hc2 : c ≤ 7 / 10) (h0 : 13 * u ^ 5 - u ^ 4 + 6 * u ^ 3 + 2 * u ^ 2 - 3 * u - 1 = 0)
    (hc : 0 < 13 * c ^ 5 - c ^ 4 + 6 * c ^ 3 + 2 * c ^ 2 - 3 * c - 1) : u < c := by
  by_contra hcu'
  have hcu : c ≤ u := not_lt.mp hcu'
  have hP : 0 < 13 * (u ^ 4 + u ^ 3 * c + u ^ 2 * c ^ 2 + u * c ^ 3 + c ^ 4) -
      (u ^ 3 + u ^ 2 * c + u * c ^ 2 + c ^ 3) + 6 * (u ^ 2 + u * c + c ^ 2) + 2 * (u + c) - 3 := by
    have hu0 : 0 < u := by linarith
    have hc0 : 0 < c := by linarith
    have e1 : u ^ 3 ≤ 343 / 1000 := by nlinarith [pow_le_pow_left₀ hu0.le h2.le 3]
    have e2 : c ^ 3 ≤ 343 / 1000 := by nlinarith [pow_le_pow_left₀ hc0.le hc2 3]
    have e3 : u ^ 2 * c ≤ 343 / 1000 := by
      have := mul_le_mul (pow_le_pow_left₀ hu0.le h2.le 2) hc2 hc0.le (by positivity); nlinarith
    have e4 : u * c ^ 2 ≤ 343 / 1000 := by
      have := mul_le_mul h2.le (pow_le_pow_left₀ hc0.le hc2 2) (by positivity) (by norm_num); nlinarith
    have f1 : 0 ≤ u ^ 4 + u ^ 3 * c + u ^ 2 * c ^ 2 + u * c ^ 3 + c ^ 4 := by positivity
    have f2 : 3 / 4 ≤ u ^ 2 + u * c + c ^ 2 := by nlinarith
    nlinarith
  have hdiff : (13 * u ^ 5 - u ^ 4 + 6 * u ^ 3 + 2 * u ^ 2 - 3 * u - 1) -
      (13 * c ^ 5 - c ^ 4 + 6 * c ^ 3 + 2 * c ^ 2 - 3 * c - 1) = (u - c) *
      (13 * (u ^ 4 + u ^ 3 * c + u ^ 2 * c ^ 2 + u * c ^ 3 + c ^ 4) -
      (u ^ 3 + u ^ 2 * c + u * c ^ 2 + c ^ 3) + 6 * (u ^ 2 + u * c + c ^ 2) + 2 * (u + c) - 3) := by ring
  have : 0 ≤ (u - c) * (13 * (u ^ 4 + u ^ 3 * c + u ^ 2 * c ^ 2 + u * c ^ 3 + c ^ 4) -
      (u ^ 3 + u ^ 2 * c + u * c ^ 2 + c ^ 3) + 6 * (u ^ 2 + u * c + c ^ 2) + 2 * (u + c) - 3) :=
    mul_nonneg (by linarith) hP.le
  linarith

/-- `dlo < arccos u` for the root `u` of the quintic in `(1/2, 7/10)`. -/
theorem dlo_lt_arccos_quintic_root (u : ℝ) (h1 : 1 / 2 < u) (h2 : u < 7 / 10)
    (h0 : 13 * u ^ 5 - u ^ 4 + 6 * u ^ 3 + 2 * u ^ 2 - 3 * u - 1 = 0) :
    5365785 / 100000 * (π / 180) < arccos u := by
  have hu : u < 592605903 / 1000000000 :=
    quintic_lt_of_root h1 h2 (by norm_num) (by norm_num) h0 (by norm_num)
  have hq : (5365785 / 100000 * (π / 180) : ℝ) = 357719 / 1200000 * π := by ring
  have hπ := Real.pi_pos
  rw [hq]
  exact lt_arccos_of_lt_cos (by positivity) (by nlinarith) (by linarith)
    (lt_of_lt_of_le hu le_cos_dpt_0)

end Tammes15.Numerics
