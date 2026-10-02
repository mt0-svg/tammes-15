import Tammes15.Attained.Roots
import Tammes15.Kappa.C1
import Tammes15.Kappa.C3

/-!
# D1: the rounded frames are within `2·10⁻²⁰` of `frameC1` and `frameC3`

The nine coordinate enclosures `encl_aN` to `encl_tN`, generated in SageMath with their proofs
by `dyadic_interval`, are stated for the
numerators of Tammes15.Attained.Data. Each gives an interval of width `2·10⁻²⁰ + 10⁻⁴⁰` for a
coordinate `xN b u / 225008` when `u ∈ [ul, uh]` and `b ∈ [bl, bh]`; the rounded frames `qC1` and
`qC3` of the certificates are within `2·10⁻²⁰` of the frames (`close_C1`, `close_C3`).
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace

namespace Tammes15.Kappa

open Attained

theorem encl_aN (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (225008 : ℝ) * 0.8950239687385675817652053027298145402868 ≤ aN b u ∧ aN b u ≤ (225008 : ℝ) * 0.8950239687385675817852053027298145402869 := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  constructor <;> dyadic_interval [prec := 100]

theorem encl_bN (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (225008 : ℝ) * 0.1714903098093749755311220556252805122250 ≤ bN b u ∧ bN b u ≤ (225008 : ℝ) * 0.1714903098093749755511220556252805122251 := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  constructor <;> dyadic_interval [prec := 100]

theorem encl_cN (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (225008 : ℝ) * 0.4117319140228847855750930801627343179317 ≤ cN b u ∧ cN b u ≤ (225008 : ℝ) * 0.4117319140228847855950930801627343179318 := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  constructor <;> dyadic_interval [prec := 100]

theorem encl_dN (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (225008 : ℝ) * 0.8009928994820256966889893094450818379701 ≤ dN b u ∧ dN b u ≤ (225008 : ℝ) * 0.8009928994820256967089893094450818379702 := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  constructor <;> dyadic_interval [prec := 100]

theorem encl_eN (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (225008 : ℝ) * 0.3819643241495056538059414100763549391535 ≤ eN b u ∧ eN b u ≤ (225008 : ℝ) * 0.3819643241495056538259414100763549391536 := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  constructor <;> dyadic_interval [prec := 100]

theorem encl_fN (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (225008 : ℝ) * -0.4609920064994498908233393714791485654564 ≤ fN b u ∧ fN b u ≤ (225008 : ℝ) * -0.4609920064994498908033393714791485654563 := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  constructor <;> dyadic_interval [prec := 100]

theorem encl_rN (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (225008 : ℝ) * 0.7788399620322553112120048616995802314997 ≤ rN b u ∧ rN b u ≤ (225008 : ℝ) * 0.7788399620322553112320048616995802314998 := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  constructor <;> dyadic_interval [prec := 100]

theorem encl_sN (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (225008 : ℝ) * -0.6271780756254064502295746100188486074899 ≤ sN b u ∧ sN b u ≤ (225008 : ℝ) * -0.6271780756254064502095746100188486074898 := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  constructor <;> dyadic_interval [prec := 100]

theorem encl_tN (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :
    (225008 : ℝ) * 0.0074816439642001671633910575441031380183 ≤ tN b u ∧ tN b u ≤ (225008 : ℝ) * 0.0074816439642001671833910575441031380184 := by
  simp only [ul, uh, bl, bh] at hu hb
  simp only [aN, bN, cN, dN, eN, fN, rN, sN, tN]
  constructor <;> dyadic_interval [prec := 100]

/-- The frame C1 rounded to `2^-100`, the frame of the certificate `C1`. -/
noncomputable def qC1 : Fin 15 → E3 := qOf (dLL oP C1.Pn)

/-- The frame C3 rounded to `2^-100`, the frame of the certificate `C3`. -/
noncomputable def qC3 : Fin 15 → E3 := qOf (dLL oP C3.Pn)

/-- `2^100` times the nine coordinates `X / 225008` of the frames (`X = aN, ..., tN` at `bR, uR`), rounded: the entries of `C1.Pn` and `C3.Pn` minus `2^101` are these up to sign. -/
def QA : ℤ := 1134577671190097222888295346076
def QB : ℤ := 217389794163179204139966559912
def QC : ℤ := 521932207944227640492349650481
def QD : ℤ := 1015379129806939693687783493192
def QE : ℤ := 484197304773890820856904832009
def QF : ℤ := -584376793739443483497597904950
def QR : ℤ := 987296945351919843020097874112
def QS : ℤ := -795042664016532338696554461155
def QT : ℤ := 9484110461912251561610304267
/-- The rounded coordinates placed as in `ptN`. -/
def Qall : Fin 18 → Fin 3 → ℤ := ![![QA, QB, QC], ![QC, QA, QB], ![QB, QC, QA], ![QD, QE, QF], ![QF, QD, QE], ![QE, QF, QD], ![QR, QS, QT], ![QT, QR, QS], ![QS, QT, QR], ![-QT, -QS, -QR], ![-QR, -QT, -QS], ![-QS, -QR, -QT], ![-QF, -QE, -QD], ![-QE, -QD, -QF], ![-QD, -QF, -QE], ![-QC, -QB, -QA], ![-QB, -QA, -QC], ![-QA, -QC, -QB]]

theorem qtab_C1 : ∀ i : Fin 15, ∀ m : Fin 3,
    ((dLL oP C1.Pn).getD i []).getD m 0 = Qall (keepC1 i) m := by
  decide +kernel

theorem qtab_C3 : ∀ i : Fin 15, ∀ m : Fin 3,
    ((dLL oP C3.Pn).getD i []).getD m 0 = Qall (keepC3 i) m := by
  decide +kernel

theorem frame_p_C1 (i : Fin 15) (m : Fin 3) : frameC1.p i m = ptN bR uR (keepC1 i) m / 225008 := by
  fin_cases m <;> rfl

theorem frame_p_C3 (i : Fin 15) (m : Fin 3) : frameC3.p i m = ptN bR uR (keepC3 i) m / 225008 := by
  fin_cases m <;> rfl

theorem rnd_neg (x : ℝ) (q : ℤ) (δ : ℝ) (h : |x / 225008 - (q : ℝ) / 2 ^ 100| ≤ δ) :
    |-x / 225008 - ((-q : ℤ) : ℝ) / 2 ^ 100| ≤ δ := by
  rw [Int.cast_neg, neg_div, neg_div, sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm]
  exact h

theorem rnd_a : |aN bR uR / 225008 - (QA : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  have h := encl_aN bR uR uR_spec.1 bR_spec.1
  rw [abs_le]
  unfold QA
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem rnd_b : |bN bR uR / 225008 - (QB : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  have h := encl_bN bR uR uR_spec.1 bR_spec.1
  rw [abs_le]
  unfold QB
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem rnd_c : |cN bR uR / 225008 - (QC : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  have h := encl_cN bR uR uR_spec.1 bR_spec.1
  rw [abs_le]
  unfold QC
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem rnd_d : |dN bR uR / 225008 - (QD : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  have h := encl_dN bR uR uR_spec.1 bR_spec.1
  rw [abs_le]
  unfold QD
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem rnd_e : |eN bR uR / 225008 - (QE : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  have h := encl_eN bR uR uR_spec.1 bR_spec.1
  rw [abs_le]
  unfold QE
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem rnd_f : |fN bR uR / 225008 - (QF : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  have h := encl_fN bR uR uR_spec.1 bR_spec.1
  rw [abs_le]
  unfold QF
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem rnd_r : |rN bR uR / 225008 - (QR : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  have h := encl_rN bR uR uR_spec.1 bR_spec.1
  rw [abs_le]
  unfold QR
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem rnd_s : |sN bR uR / 225008 - (QS : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  have h := encl_sN bR uR uR_spec.1 bR_spec.1
  rw [abs_le]
  unfold QS
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem rnd_t : |tN bR uR / 225008 - (QT : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  have h := encl_tN bR uR uR_spec.1 bR_spec.1
  rw [abs_le]
  unfold QT
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem entry_close : ∀ k : Fin 18, ∀ m : Fin 3,
    |ptN bR uR k m / 225008 - (Qall k m : ℝ) / 2 ^ 100| ≤ 2 / 10 ^ 20 := by
  intro k m
  fin_cases k <;> fin_cases m <;>
    first
    | exact rnd_a | exact rnd_b | exact rnd_c | exact rnd_d | exact rnd_e | exact rnd_f
    | exact rnd_r | exact rnd_s | exact rnd_t
    | exact rnd_neg _ _ _ rnd_a | exact rnd_neg _ _ _ rnd_b | exact rnd_neg _ _ _ rnd_c
    | exact rnd_neg _ _ _ rnd_d | exact rnd_neg _ _ _ rnd_e | exact rnd_neg _ _ _ rnd_f
    | exact rnd_neg _ _ _ rnd_r | exact rnd_neg _ _ _ rnd_s | exact rnd_neg _ _ _ rnd_t

theorem close_C1 : ∀ i m, |frameC1.p i m - qC1 i m| ≤ 2 / 10 ^ 20 := by
  intro i m
  rw [frame_p_C1, qC1, qOf_apply, qtab_C1]
  exact entry_close _ _

theorem close_C3 : ∀ i m, |frameC3.p i m - qC3 i m| ≤ 2 / 10 ^ 20 := by
  intro i m
  rw [frame_p_C3, qC3, qOf_apply, qtab_C3]
  exact entry_close _ _

end Tammes15.Kappa
