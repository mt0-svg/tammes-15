import Tammes15.D3lp.Cuts
import Tammes15.Trigrows.Mono

open Real

namespace Tammes15.D3lp

open Tammes15

theorem alpha_lo_of_end {lo hi a : ℝ} (hlo : 0 < lo) (hhi : hi < π / 2)
    (h : a ≤ alpha lo) : ∀ d, lo ≤ d → d ≤ hi → a ≤ alpha d := by
  intro d hdlo hdhi
  have hdpos : 0 < d := lt_of_lt_of_le hlo hdlo
  have hdlt : d < π / 2 := lt_of_le_of_lt hdhi hhi
  have hlo_lt_pi2 : lo < π / 2 := lt_of_le_of_lt (le_trans hdlo hdhi) hhi
  have hmem_lo : lo ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hlo, hlo_lt_pi2⟩
  have hmem_d : d ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hdpos, hdlt⟩
  have halpha_le : alpha lo ≤ alpha d :=
    alpha_strictMonoOn.monotoneOn hmem_lo hmem_d hdlo
  exact le_trans h halpha_le

theorem alpha_hi_of_end {lo hi a : ℝ} (hlo : 0 < lo) (hhi : hi < π / 2)
    (h : alpha hi ≤ a) : ∀ d, lo ≤ d → d ≤ hi → alpha d ≤ a := by
  intro d hdlo hdhi
  have hdpos : 0 < d := by linarith
  have hd_range : d ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    exact ⟨hdpos, by linarith⟩
  have hi_range : hi ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    exact ⟨by linarith, hhi⟩
  have h_alpha_le : alpha d ≤ alpha hi :=
    alpha_strictMonoOn.monotoneOn hd_range hi_range hdhi
  linarith

theorem ssum_hi_of_end {lo hi a : ℝ} (hlo : 0 < lo) (hhi : hi < π / 2)
    (h : Ssum hi ≤ a) : ∀ d, lo ≤ d → d ≤ hi → Ssum d ≤ a := by
  intro d hdlo hdhi
  have hdpos : 0 < d := lt_of_lt_of_le hlo hdlo
  have hdlt : d < π / 2 := lt_of_le_of_lt hdhi hhi
  have hipos : 0 < hi := lt_of_lt_of_le hlo (le_trans hdlo hdhi)
  have hd_mem : d ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hdpos, hdlt⟩
  have hhi_mem : hi ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hipos, hhi⟩
  have hS : Ssum d ≤ Ssum hi := Ssum_strictMonoOn.monotoneOn hd_mem hhi_mem hdhi
  exact le_trans hS h

theorem pi_le_pihi :
    π ≤ ((314159265358979323847 : ℤ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) := by
  have h : ((314159265358979323847 : ℤ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) = 3.14159265358979323847 := by
    norm_num
  rw [h]
  exact Real.pi_lt_d20.le

theorem twopilo_le :
    ((628318530717958647692 : ℤ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) ≤ 2 * π := by
  push_cast
  have h : (628318530717958647692 : ℝ) / (100000000000000000000 : ℝ) = 2 * (3.14159265358979323846 : ℝ) := by
    norm_num
  rw [h]
  nlinarith [Real.pi_gt_d20]

theorem le_twopihi :
    2 * π ≤ ((628318530717958647694 : ℤ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) := by
  have h : ((628318530717958647694 : ℤ) : ℝ) / ((100000000000000000000 : ℕ) : ℝ) = 2 * (3.14159265358979323847 : ℝ) := by
    norm_num
  rw [h]
  nlinarith [Real.pi_lt_d20]

theorem pentCut_unit {lo hi a b : ℝ} (ha : ∀ d, lo ≤ d → d ≤ hi → a ≤ alpha d)
    (hb : π ≤ b) : PentCut lo hi ![1, 0, 0, 0, 0] a b := by
  intro d hlo hhi u hu _
  have hsum : ∑ j : Fin 5, ![1, 0, 0, 0, 0] j * u j = u 0 := by
    simp [Fin.sum_univ_five]
  have ha_le : a ≤ alpha d := ha d hlo hhi
  have halpha_le_u0 : alpha d ≤ u 0 := (hu 0).1
  have hu0_lt_pi : u 0 < π := (hu 0).2
  have ha_le_u0 : a ≤ u 0 := le_trans ha_le halpha_le_u0
  have hu0_le_b : u 0 ≤ b := le_trans (le_of_lt hu0_lt_pi) hb
  rw [hsum]
  exact And.intro ha_le_u0 hu0_le_b

theorem hexCut_unit {lo hi a b : ℝ} (ha : ∀ d, lo ≤ d → d ≤ hi → a ≤ alpha d)
    (hb : π ≤ b) : HexCut lo hi ![1, 0, 0, 0, 0, 0] a b := by
  intro d hlo hhi u hu _ _
  have hsum : ∑ j : Fin 6, ![1, 0, 0, 0, 0, 0] j * u j = u 0 := by
    simp [Fin.sum_univ_six]
  have ha_le_u0 : a ≤ u 0 :=
    le_trans (ha d hlo hhi) (hu 0).1
  have hu0_le_b : u 0 ≤ b :=
    le_trans (le_of_lt (hu 0).2) hb
  exact And.intro (by rwa [hsum]) (by rwa [hsum])

theorem PentCut_mono {lo hi a b a' b' : ℝ} {w w' : Fin 5 → ℝ}
    (h : PentCut lo hi w a b) (hw : ∀ j, w j = w' j) (ha : a' ≤ a) (hb : b ≤ b') :
    PentCut lo hi w' a' b' := by
  have hw_eq : w = w' := funext hw
  subst hw_eq
  intro d hdlo hdhi u hu hpent
  rcases h d hdlo hdhi u hu hpent with ⟨hle1, hle2⟩
  constructor
  · exact le_trans ha hle1
  · exact le_trans hle2 hb

theorem HexCut_mono {lo hi a b a' b' : ℝ} {w w' : Fin 6 → ℝ}
    (h : HexCut lo hi w a b) (hw : ∀ j, w j = w' j) (ha : a' ≤ a) (hb : b ≤ b') :
    HexCut lo hi w' a' b' := by
  intro d hdlo hdhi u hu hhex hdiag
  have ⟨hsumlo, hsumhi⟩ := h d hdlo hdhi u hu hhex hdiag
  have hsumlo' : a' ≤ ∑ j : Fin 6, w' j * u j := by
    calc
      a' ≤ a := ha
      _ ≤ ∑ j : Fin 6, w j * u j := hsumlo
      _ = ∑ j : Fin 6, w' j * u j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hw j]
  have hsumhi' : ∑ j : Fin 6, w' j * u j ≤ b' := by
    calc
      ∑ j : Fin 6, w' j * u j = ∑ j : Fin 6, w j * u j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hw j]
      _ ≤ b := hsumhi
      _ ≤ b' := hb
  exact And.intro hsumlo' hsumhi'

theorem PentCut_mono_range {lo hi lo' hi' a b : ℝ} {w : Fin 5 → ℝ}
    (h : PentCut lo hi w a b) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) : PentCut lo' hi' w a b := by
  unfold PentCut
  intro d hdlo hdhi u hu hPent
  exact h d (le_trans hlo hdlo) (le_trans hdhi hhi) u hu hPent

theorem HexCut_mono_range {lo hi lo' hi' a b : ℝ} {w : Fin 6 → ℝ}
    (h : HexCut lo hi w a b) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) : HexCut lo' hi' w a b := by
  unfold HexCut
  intro d hdlo hdhi
  apply h d (le_trans hlo hdlo) (le_trans hdhi hhi)

end Tammes15.D3lp
