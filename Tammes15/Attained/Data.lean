import Tammes15.Hyps.Computations

/-!
# The frames C1 and C3 of D4

The two frame configurations `frameC1` and `frameC3` of `AttainedHyp {frameC1, frameC3}` (D4 of
Tammes15/Hyps/Computations.lean). By `LocalFires` (isometries and bijections) these two frames stand
for all eight.

The definitions `aN` to `bh` are generated in SageMath from the exact coordinates of
data/bk15_exact.txt (paper, Section 3).
`u` is the root of `quintic` in `[ul, uh]` and `b` the
root of `Q4 b u` in `[bl, bh]` (decimal enclosures of width 1e-40 and 1e-30). The frame coordinates
lie in `ℚ(u, b)`, of degree 20; each one is `xN b u / 225008` with `xN` a polynomial with integer
coefficients written with products. The 18 points `pt b u k` are signed cyclic permutations of the
triples `(aN, bN, cN)`, `(dN, eN, fN)`, `(rN, sN, tN)`; `frameC1` and `frameC3` keep 15 of them.

`uR` and `bR` are chosen by `Classical.epsilon` among the roots in the enclosures, so that the
definitions of the frames reach no theorem of the package; that the roots exist is `u_root` and
`b_root` (Roots.lean).
-/

open scoped RealInnerProductSpace

namespace Tammes15.Attained

/-- Numerator of a frame coordinate: the coordinate is `aN b u / 225008`. -/
def aN (b u : ℝ) : ℝ :=
  (-2254005 : ℝ) * b * b * b * u * u * u * u + (-1083312 : ℝ) * b * b * b * u * u * u + (-1544202 : ℝ) * b * b * b * u * u + (-1108152 : ℝ) * b * b * b * u + (-112689 : ℝ) * b * b * b + (7726537 : ℝ) * b * u * u * u * u + (-1953252 : ℝ) * b * u * u * u + (4777822 : ℝ) * b * u * u + (300804 : ℝ) * b * u + (-1174831 : ℝ) * b

/-- Numerator of a frame coordinate: the coordinate is `bN b u / 225008`. -/
def bN (b _u : ℝ) : ℝ :=
  (225008 : ℝ) * b

/-- Numerator of a frame coordinate: the coordinate is `cN b u / 225008`. -/
def cN (b u : ℝ) : ℝ :=
  (1084473 : ℝ) * b * b * b * u * u * u * u + (-1693224 : ℝ) * b * b * b * u * u * u + (651618 : ℝ) * b * b * b * u * u + (-465336 : ℝ) * b * b * b * u + (-337131 : ℝ) * b * b * b + (-4658745 : ℝ) * b * u * u * u * u + (3500868 : ℝ) * b * u * u * u + (-3142398 : ℝ) * b * u * u + (1038268 : ℝ) * b * u + (892199 : ℝ) * b

/-- Numerator of a frame coordinate: the coordinate is `dN b u / 225008`. -/
def dN (b u : ℝ) : ℝ :=
  (-5325957 : ℝ) * b * b * b * u * u * u * u + (2646 : ℝ) * b * b * b * u * u * u + (-3166380 : ℝ) * b * b * b * u * u + (-440118 : ℝ) * b * b * b * u + (229761 : ℝ) * b * b * b + (3643003 : ℝ) * b * u * u * u * u + (-356034 : ℝ) * b * u * u * u + (2476460 : ℝ) * b * u * u + (-181790 : ℝ) * b * u + (-33271 : ℝ) * b

/-- Numerator of a frame coordinate: the coordinate is `eN b u / 225008`. -/
def eN (b u : ℝ) : ℝ :=
  (-2798406 : ℝ) * b * b * b * u * u * u * u + (1025604 : ℝ) * b * b * b * u * u * u + (-1782828 : ℝ) * b * b * b * u * u + (-189900 : ℝ) * b * b * b * u + (122202 : ℝ) * b * b * b + (-1349530 : ℝ) * b * u * u * u * u + (251776 : ℝ) * b * u * u * u + (-959840 : ℝ) * b * u * u + (363832 : ℝ) * b * u + (758674 : ℝ) * b

/-- Numerator of a frame coordinate: the coordinate is `fN b u / 225008`. -/
def fN (b u : ℝ) : ℝ :=
  (-1358019 : ℝ) * b * b * b * u * u * u * u + (1753578 : ℝ) * b * b * b * u * u * u + (-490968 : ℝ) * b * b * b * u * u + (1323270 : ℝ) * b * b * b * u + (557379 : ℝ) * b * b * b + (1193465 : ℝ) * b * u * u * u * u + (-1367898 : ℝ) * b * u * u * u + (675836 : ℝ) * b * u * u + (-872158 : ℝ) * b * u + (-228053 : ℝ) * b

/-- Numerator of a frame coordinate: the coordinate is `rN b u / 225008`. -/
def rN (b u : ℝ) : ℝ :=
  (1293201 : ℝ) * b * b * b * u * u * u * u + (-2285388 : ℝ) * b * b * b * u * u * u + (891954 : ℝ) * b * b * b * u * u + (-1734516 : ℝ) * b * b * b * u + (-876771 : ℝ) * b * b * b + (-4821453 : ℝ) * b * u * u * u * u + (2770460 : ℝ) * b * u * u * u + (-3246250 : ℝ) * b * u * u + (1871604 : ℝ) * b * u + (1126951 : ℝ) * b

/-- Numerator of a frame coordinate: the coordinate is `sN b u / 225008`. -/
def sN (b u : ℝ) : ℝ :=
  (3298230 : ℝ) * b * b * b * u * u * u * u + (271620 : ℝ) * b * b * b * u * u * u + (3064392 : ℝ) * b * b * b * u * u + (487980 : ℝ) * b * b * b * u + (-208926 : ℝ) * b * b * b + (372918 : ℝ) * b * u * u * u * u + (-1437548 : ℝ) * b * u * u * u + (-648984 : ℝ) * b * u * u + (-17780 : ℝ) * b * u + (-378910 : ℝ) * b

/-- Numerator of a frame coordinate: the coordinate is `tN b u / 225008`. -/
def tN (b u : ℝ) : ℝ :=
  (705861 : ℝ) * b * b * b * u * u * u * u + (-1283148 : ℝ) * b * b * b * u * u * u + (2081826 : ℝ) * b * b * b * u * u + (-173484 : ℝ) * b * b * b * u + (-420759 : ℝ) * b * b * b + (-1918917 : ℝ) * b * u * u * u * u + (1832292 : ℝ) * b * u * u * u + (-2370690 : ℝ) * b * u * u + (211036 : ℝ) * b * u + (571823 : ℝ) * b

/-- The quartic whose root `b` generates `ℚ(u, b)` over `ℚ(u)`, written with products. -/
def Q4 (b u : ℝ) : ℝ :=
  (324 : ℝ) * b * b * b * b * u * u * u * u + (135 : ℝ) * b * b * b * b * u * u * u + (-99 : ℝ) * b * b * b * b * u * u + (-63 : ℝ) * b * b * b * b * u + (-9 : ℝ) * b * b * b * b + (124 : ℝ) * b * b * u * u * u * u * u + (-310 : ℝ) * b * b * u * u * u * u + (-74 : ℝ) * b * b * u * u * u + (102 : ℝ) * b * b * u * u + (30 : ℝ) * b * b * u + (100 : ℝ) * u * u * u * u * u * u + (-65 : ℝ) * u * u * u * u * u + (-11 : ℝ) * u * u * u * u + (9 : ℝ) * u * u * u + (-1 : ℝ) * u * u

/-- Numerators of the 18 frame points (order of bk15_exact.txt: V1 V2 V3 V12 V23 V31 P I A Q J B
W12 W23 W31 W1 W2 W3). -/
def ptN (b u : ℝ) : Fin 18 → Fin 3 → ℝ :=
  ![![aN b u, bN b u, cN b u],
    ![cN b u, aN b u, bN b u],
    ![bN b u, cN b u, aN b u],
    ![dN b u, eN b u, fN b u],
    ![fN b u, dN b u, eN b u],
    ![eN b u, fN b u, dN b u],
    ![rN b u, sN b u, tN b u],
    ![tN b u, rN b u, sN b u],
    ![sN b u, tN b u, rN b u],
    ![(-(tN b u)), (-(sN b u)), (-(rN b u))],
    ![(-(rN b u)), (-(tN b u)), (-(sN b u))],
    ![(-(sN b u)), (-(rN b u)), (-(tN b u))],
    ![(-(fN b u)), (-(eN b u)), (-(dN b u))],
    ![(-(eN b u)), (-(dN b u)), (-(fN b u))],
    ![(-(dN b u)), (-(fN b u)), (-(eN b u))],
    ![(-(cN b u)), (-(bN b u)), (-(aN b u))],
    ![(-(bN b u)), (-(aN b u)), (-(cN b u))],
    ![(-(aN b u)), (-(cN b u)), (-(bN b u))]]

/-- The 18 frame points. -/
noncomputable def pt (b u : ℝ) (k : Fin 18) : E3 :=
  !₂[ptN b u k 0 / 225008, ptN b u k 1 / 225008, ptN b u k 2 / 225008]

/-- Enclosure of `u`. -/
def ul : ℝ := 0.59260590292507377809642492233275771867520
/-- Enclosure of `u`. -/
def uh : ℝ := 0.59260590292507377809642492233275771867530
/-- Enclosure of `b`. -/
def bl : ℝ := 0.17149030980937497554112205562500000000000
/-- Enclosure of `b`. -/
def bh : ℝ := 0.17149030980937497554112205562600000000000

/-- The contact cosine `u`: a root of `quintic` in `[ul, uh]` (one exists, `u_root`). -/
noncomputable def uR : ℝ := Classical.epsilon fun u => u ∈ Set.Icc ul uh ∧ quintic u = 0

/-- The generator `b` of `ℚ(u, b)`: a root of `Q4 · uR` in `[bl, bh]` (one exists, `b_root`). -/
noncomputable def bR : ℝ := Classical.epsilon fun b => b ∈ Set.Icc bl bh ∧ Q4 b uR = 0

/-- The 15 points of C1 among the 18 (bk15_exact.txt, `C1 keep`, as 0-based indices). -/
def keepC1 : Fin 15 → Fin 18 := ![0, 1, 2, 3, 4, 5, 6, 7, 10, 12, 13, 14, 15, 16, 17]

/-- The frame C1 with its 30 contacts (bk15_exact.txt, `C1 contacts`). -/
noncomputable def frameC1 : Frame where
  p i := pt bR uR (keepC1 i)
  S := {(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 7), (2, 4), (2, 5), (3, 7), (3, 9), (4, 8), (4, 11), (5, 6), (5, 10), (6, 9), (7, 11), (8, 10), (8, 14), (9, 12), (9, 13), (10, 13), (10, 14), (11, 12), (11, 14), (12, 13), (12, 14), (13, 14)}

/-- The 15 points of C3 among the 18 (bk15_exact.txt, `C3 keep`, as 0-based indices). -/
def keepC3 : Fin 15 → Fin 18 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17]

/-- The frame C3 with its 30 contacts (bk15_exact.txt, `C3 contacts`). -/
noncomputable def frameC3 : Frame where
  p i := pt bR uR (keepC3 i)
  S := {(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 7), (2, 4), (2, 5), (2, 8), (3, 7), (3, 9), (4, 8), (4, 11), (5, 6), (5, 10), (6, 9), (7, 11), (8, 10), (9, 12), (9, 13), (10, 13), (10, 14), (11, 12), (11, 14), (12, 13), (12, 14), (13, 14)}

end Tammes15.Attained
