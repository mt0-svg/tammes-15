import Tammes15.Attained.Data

/-!
# Separations of the 18 frame points

Generated in SageMath: the lemmas `sp_k1_k2`.
For every
non-contact pair, the inner product numerator is at most `225008² · u` on the enclosures of `u` and
`b`, proved by `dyadic_interval`.
-/

set_option maxHeartbeats 0

open scoped RealInnerProductSpace

namespace Tammes15.Attained

set_option linter.unusedSimpArgs false

/-! ## Separations -/

theorem sp_0_4 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * fN b u + bN b u * dN b u + cN b u * eN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_0_7 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * tN b u + bN b u * rN b u + cN b u * sN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_0_8 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * sN b u + bN b u * tN b u + cN b u * rN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_0_10 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * (-(rN b u)) + bN b u * (-(tN b u)) + cN b u * (-(sN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_0_12 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * (-(fN b u)) + bN b u * (-(eN b u)) + cN b u * (-(dN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_0_13 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * (-(eN b u)) + bN b u * (-(dN b u)) + cN b u * (-(fN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_0_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * (-(dN b u)) + bN b u * (-(fN b u)) + cN b u * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_0_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * (-(cN b u)) + bN b u * (-(bN b u)) + cN b u * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_0_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * (-(bN b u)) + bN b u * (-(aN b u)) + cN b u * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_0_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    aN b u * (-(aN b u)) + bN b u * (-(cN b u)) + cN b u * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_5 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * eN b u + aN b u * fN b u + bN b u * dN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_6 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * rN b u + aN b u * sN b u + bN b u * tN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_8 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * sN b u + aN b u * tN b u + bN b u * rN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_10 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * (-(rN b u)) + aN b u * (-(tN b u)) + bN b u * (-(sN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_12 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * (-(fN b u)) + aN b u * (-(eN b u)) + bN b u * (-(dN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_13 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * (-(eN b u)) + aN b u * (-(dN b u)) + bN b u * (-(fN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * (-(dN b u)) + aN b u * (-(fN b u)) + bN b u * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * (-(cN b u)) + aN b u * (-(bN b u)) + bN b u * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * (-(bN b u)) + aN b u * (-(aN b u)) + bN b u * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_1_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    cN b u * (-(aN b u)) + aN b u * (-(cN b u)) + bN b u * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_3 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * dN b u + cN b u * eN b u + aN b u * fN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_6 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * rN b u + cN b u * sN b u + aN b u * tN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_7 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * tN b u + cN b u * rN b u + aN b u * sN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_10 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * (-(rN b u)) + cN b u * (-(tN b u)) + aN b u * (-(sN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_12 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * (-(fN b u)) + cN b u * (-(eN b u)) + aN b u * (-(dN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_13 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * (-(eN b u)) + cN b u * (-(dN b u)) + aN b u * (-(fN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * (-(dN b u)) + cN b u * (-(fN b u)) + aN b u * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * (-(cN b u)) + cN b u * (-(bN b u)) + aN b u * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * (-(bN b u)) + cN b u * (-(aN b u)) + aN b u * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_2_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    bN b u * (-(aN b u)) + cN b u * (-(cN b u)) + aN b u * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_4 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * fN b u + eN b u * dN b u + fN b u * eN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_5 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * eN b u + eN b u * fN b u + fN b u * dN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_6 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * rN b u + eN b u * sN b u + fN b u * tN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_8 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * sN b u + eN b u * tN b u + fN b u * rN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_10 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * (-(rN b u)) + eN b u * (-(tN b u)) + fN b u * (-(sN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_13 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * (-(eN b u)) + eN b u * (-(dN b u)) + fN b u * (-(fN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * (-(dN b u)) + eN b u * (-(fN b u)) + fN b u * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * (-(cN b u)) + eN b u * (-(bN b u)) + fN b u * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * (-(bN b u)) + eN b u * (-(aN b u)) + fN b u * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_3_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    dN b u * (-(aN b u)) + eN b u * (-(cN b u)) + fN b u * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_4_5 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    fN b u * eN b u + dN b u * fN b u + eN b u * dN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_4_6 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    fN b u * rN b u + dN b u * sN b u + eN b u * tN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_4_7 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    fN b u * tN b u + dN b u * rN b u + eN b u * sN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_4_12 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    fN b u * (-(fN b u)) + dN b u * (-(eN b u)) + eN b u * (-(dN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_4_13 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    fN b u * (-(eN b u)) + dN b u * (-(dN b u)) + eN b u * (-(fN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_4_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    fN b u * (-(cN b u)) + dN b u * (-(bN b u)) + eN b u * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_4_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    fN b u * (-(bN b u)) + dN b u * (-(aN b u)) + eN b u * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_4_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    fN b u * (-(aN b u)) + dN b u * (-(cN b u)) + eN b u * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_5_7 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    eN b u * tN b u + fN b u * rN b u + dN b u * sN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_5_8 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    eN b u * sN b u + fN b u * tN b u + dN b u * rN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_5_10 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    eN b u * (-(rN b u)) + fN b u * (-(tN b u)) + dN b u * (-(sN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_5_12 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    eN b u * (-(fN b u)) + fN b u * (-(eN b u)) + dN b u * (-(dN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_5_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    eN b u * (-(dN b u)) + fN b u * (-(fN b u)) + dN b u * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_5_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    eN b u * (-(cN b u)) + fN b u * (-(bN b u)) + dN b u * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_5_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    eN b u * (-(bN b u)) + fN b u * (-(aN b u)) + dN b u * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_5_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    eN b u * (-(aN b u)) + fN b u * (-(cN b u)) + dN b u * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_6_7 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    rN b u * tN b u + sN b u * rN b u + tN b u * sN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_6_8 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    rN b u * sN b u + sN b u * tN b u + tN b u * rN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_6_10 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    rN b u * (-(rN b u)) + sN b u * (-(tN b u)) + tN b u * (-(sN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_6_13 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    rN b u * (-(eN b u)) + sN b u * (-(dN b u)) + tN b u * (-(fN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_6_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    rN b u * (-(dN b u)) + sN b u * (-(fN b u)) + tN b u * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_6_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    rN b u * (-(cN b u)) + sN b u * (-(bN b u)) + tN b u * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_6_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    rN b u * (-(bN b u)) + sN b u * (-(aN b u)) + tN b u * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_6_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    rN b u * (-(aN b u)) + sN b u * (-(cN b u)) + tN b u * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_7_8 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    tN b u * sN b u + rN b u * tN b u + sN b u * rN b u ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_7_10 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    tN b u * (-(rN b u)) + rN b u * (-(tN b u)) + sN b u * (-(sN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_7_12 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    tN b u * (-(fN b u)) + rN b u * (-(eN b u)) + sN b u * (-(dN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_7_13 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    tN b u * (-(eN b u)) + rN b u * (-(dN b u)) + sN b u * (-(fN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_7_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    tN b u * (-(cN b u)) + rN b u * (-(bN b u)) + sN b u * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_7_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    tN b u * (-(bN b u)) + rN b u * (-(aN b u)) + sN b u * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_7_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    tN b u * (-(aN b u)) + rN b u * (-(cN b u)) + sN b u * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_8_12 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    sN b u * (-(fN b u)) + tN b u * (-(eN b u)) + rN b u * (-(dN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_8_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    sN b u * (-(dN b u)) + tN b u * (-(fN b u)) + rN b u * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_8_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    sN b u * (-(cN b u)) + tN b u * (-(bN b u)) + rN b u * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_8_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    sN b u * (-(bN b u)) + tN b u * (-(aN b u)) + rN b u * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_8_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    sN b u * (-(aN b u)) + tN b u * (-(cN b u)) + rN b u * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_10_12 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(rN b u)) * (-(fN b u)) + (-(tN b u)) * (-(eN b u)) + (-(sN b u)) * (-(dN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_10_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(rN b u)) * (-(dN b u)) + (-(tN b u)) * (-(fN b u)) + (-(sN b u)) * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_10_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(rN b u)) * (-(cN b u)) + (-(tN b u)) * (-(bN b u)) + (-(sN b u)) * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_10_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(rN b u)) * (-(bN b u)) + (-(tN b u)) * (-(aN b u)) + (-(sN b u)) * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_12_13 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(fN b u)) * (-(eN b u)) + (-(eN b u)) * (-(dN b u)) + (-(dN b u)) * (-(fN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_12_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(fN b u)) * (-(dN b u)) + (-(eN b u)) * (-(fN b u)) + (-(dN b u)) * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_12_17 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(fN b u)) * (-(aN b u)) + (-(eN b u)) * (-(cN b u)) + (-(dN b u)) * (-(bN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_13_14 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(eN b u)) * (-(dN b u)) + (-(dN b u)) * (-(fN b u)) + (-(fN b u)) * (-(eN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_13_15 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(eN b u)) * (-(cN b u)) + (-(dN b u)) * (-(bN b u)) + (-(fN b u)) * (-(aN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

theorem sp_14_16 (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (-(dN b u)) * (-(bN b u)) + (-(fN b u)) * (-(aN b u)) + (-(eN b u)) * (-(cN b u)) ≤ (225008 * 225008 : ℝ) * u := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  dyadic_interval [prec := 60]

end Tammes15.Attained
