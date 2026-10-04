import Tammes15.D3lp.Code

open Real

namespace Tammes15.D3lp

open Tammes15

def PentCut (lo hi : ℝ) (w : Fin 5 → ℝ) (a b : ℝ) : Prop :=
  ∀ d : ℝ, lo ≤ d → d ≤ hi → ∀ u : Fin 5 → ℝ, (∀ j, alpha d ≤ u j ∧ u j < π) →
    (∀ s : Fin 5, PentRel d (u s) (u (s + 1)) (u (s + 2)) (u (s + 3)) (u (s + 4))) →
      a ≤ ∑ j, w j * u j ∧ ∑ j, w j * u j ≤ b

def HexCut (lo hi : ℝ) (w : Fin 6 → ℝ) (a b : ℝ) : Prop :=
  ∀ d : ℝ, lo ≤ d → d ≤ hi → ∀ u : Fin 6 → ℝ, (∀ j, alpha d ≤ u j ∧ u j < π) →
    (∀ s : Fin 6,
      HexRel d (u s) (u (s + 1)) (u (s + 2)) (u (s + 3)) (u (s + 4)) (u (s + 5))) →
    (∀ s : Fin 6, HexDiagRel d (u s) (u (s + 1))) →
      a ≤ ∑ j, w j * u j ∧ ∑ j, w j * u j ≤ b

noncomputable def wOf (S : ℕ) (m : ℕ) (w : List ℤ) : Fin m → ℝ :=
  fun j => (w.getD j 0 : ℝ) / S

structure ParamsValid (lo hi : ℝ) (p : Params) : Prop where
  S_pos : 0 < p.S
  lo_pos : 0 < lo
  hi_lt : hi < π / 2
  alpha_lo : ∀ d, lo ≤ d → d ≤ hi → (p.alo : ℝ) / p.S ≤ alpha d
  alpha_hi : ∀ d, lo ≤ d → d ≤ hi → alpha d ≤ (p.ahi : ℝ) / p.S
  ssum_hi : ∀ d, lo ≤ d → d ≤ hi → Ssum d ≤ (p.shi : ℝ) / p.S
  pi_hi : π ≤ (p.pihi : ℝ) / p.S
  twopi_lo : (p.twopilo : ℝ) / p.S ≤ 2 * π
  twopi_hi : 2 * π ≤ (p.twopihi : ℝ) / p.S
  pent : ∀ cr ∈ p.pent, cr.w.length = 5 ∧
    PentCut lo hi (wOf p.S 5 cr.w) ((cr.lo : ℝ) / p.S) ((cr.hi : ℝ) / p.S)
  hex : ∀ cr ∈ p.hex, cr.w.length = 6 ∧
    HexCut lo hi (wOf p.S 6 cr.w) ((cr.lo : ℝ) / p.S) ((cr.hi : ℝ) / p.S)

end Tammes15.D3lp
