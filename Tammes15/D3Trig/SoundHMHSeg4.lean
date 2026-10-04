import Tammes15.D3Trig.Prog.HMH
import Tammes15.D3Prog.Sem

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progHMH_seg4 (F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (v23 : ℕ) (v259 : ℕ) (v290 : ℕ) (v584 : ℕ) (v615 : ℕ) (v728 : ℕ) (v749 : ℕ) (v766 : ℕ) (v1685 : ℕ) (v1724 : ℕ) (v1737 : ℕ) (v1755 : ℕ) (v1756 : ℕ) (v1759 : ℕ) (v1780 : ℕ) (v1819 : ℕ) (v1832 : ℕ) (v1870 : ℕ) (v1890 : ℕ) (v1907 : ℕ) (v1911 : ℕ) (v1945 : ℕ) (v2056 : ℕ) (v2076 : ℕ) (v2093 : ℕ) (v2097 : ℕ) (v2131 : ℕ) (v2275 : ℕ) (v2302 : ℕ) (v2372 : ℕ) (v2469 : ℕ) (v2537 : ℕ) (v2634 : ℕ) (v2710 : ℕ) (v2753 : ℕ) (h_v23 : R 1 0 0 1 v23 v23) (h_v259 : R 1 0 0 1 v259 v259) (h_v290 : R 1 0 0 1 v290 v290) (h_v584 : R 1 0 0 1 v584 v584) (h_v615 : R 1 0 0 1 v615 v615) (h_v728 : R 1 0 0 1 v728 v728) (h_v749 : R 1 0 0 1 v749 v749) (h_v766 : R 1 0 0 1 v766 v766) (h_v1685 : R 1 0 0 1 v1685 v1685) (h_v1724 : R 1 0 0 1 v1724 v1724) (h_v1737 : R 1 0 0 1 v1737 v1737) (h_v1755 : R 1 0 0 1 v1755 v1755) (h_v1756 : R 1 0 0 1 v1756 v1756) (h_v1759 : R 1 0 0 1 v1759 v1759) (h_v1780 : R 1 0 0 1 v1780 v1780) (h_v1819 : R 1 0 0 1 v1819 v1819) (h_v1832 : R 1 0 0 1 v1832 v1832) (h_v1870 : R 1 0 0 1 v1870 v1870) (h_v1890 : R 1 0 0 1 v1890 v1890) (h_v1907 : R 1 0 0 1 v1907 v1907) (h_v1911 : R 1 0 0 1 v1911 v1911) (h_v1945 : R 1 0 0 1 v1945 v1945) (h_v2056 : R 1 0 0 1 v2056 v2056) (h_v2076 : R 1 0 0 1 v2076 v2076) (h_v2093 : R 1 0 0 1 v2093 v2093) (h_v2097 : R 1 0 0 1 v2097 v2097) (h_v2131 : R 1 0 0 1 v2131 v2131) (h_v2275 : R 1 0 0 1 v2275 v2275) (h_v2302 : R 1 0 0 1 v2302 v2302) (h_v2372 : R 1 0 0 1 v2372 v2372) (h_v2469 : R 1 0 0 1 v2469 v2469) (h_v2537 : R 1 0 0 1 v2537 v2537) (h_v2634 : R 1 0 0 1 v2634 v2634) (h_v2710 : R 1 0 0 1 v2710 v2710) (h_v2753 : R 1 0 0 1 v2753 v2753) :
    let v2754 := Nat.land v1685 v2753
    let v2755 := Nat.land v1724 v2754
    let v2756 := Nat.land v1737 v2755
    let v2757 := Nat.land v1755 v2756
    let v2758 := Nat.land v1756 v2757
    let v2759 := Nat.land v1759 v2758
    let v2760 := Nat.land v1780 v2759
    let v2761 := Nat.land v1780 v2760
    let v2762 := Nat.land v1819 v2761
    let v2763 := Nat.land v1832 v2762
    let v2764 := Nat.land v23 v2763
    let v2765 := Nat.land v1870 v2764
    let v2766 := Nat.land v1890 v2765
    let v2767 := Nat.land v1907 v2766
    let v2768 := Nat.land v23 v2767
    let v2769 := Nat.land v1911 v2768
    let v2770 := Nat.land v1911 v2769
    let v2771 := Nat.land v1945 v2770
    let v2772 := Nat.land v259 v2771
    let v2773 := Nat.land v259 v2772
    let v2774 := Nat.land v290 v2773
    let v2775 := Nat.land v23 v2774
    let v2776 := Nat.land v2056 v2775
    let v2777 := Nat.land v2076 v2776
    let v2778 := Nat.land v2093 v2777
    let v2779 := Nat.land v23 v2778
    let v2780 := Nat.land v2097 v2779
    let v2781 := Nat.land v2097 v2780
    let v2782 := Nat.land v2131 v2781
    let v2783 := Nat.land v584 v2782
    let v2784 := Nat.land v584 v2783
    let v2785 := Nat.land v615 v2784
    let v2786 := Nat.land v23 v2785
    let v2787 := Nat.land v728 v2786
    let v2788 := Nat.land v749 v2787
    let v2789 := Nat.land v766 v2788
    let v2790 := Nat.land v2275 v2789
    let v2791 := Nat.land v2302 v2790
    let v2792 := Nat.land v2372 v2791
    let v2793 := Nat.land v2469 v2792
    let v2794 := Nat.land v2537 v2793
    let v2795 := Nat.land v2634 v2794
    let v2796 := Nat.land v2710 v2795
    ∀ (P : Prop), (((v2754 = 1 ↔ v1685 = 1 ∧ v2753 = 1)) → ((v2755 = 1 ↔ v1724 = 1 ∧ v2754 = 1)) → ((v2756 = 1 ↔ v1737 = 1 ∧ v2755 = 1)) → ((v2757 = 1 ↔ v1755 = 1 ∧ v2756 = 1)) → ((v2758 = 1 ↔ v1756 = 1 ∧ v2757 = 1)) → ((v2759 = 1 ↔ v1759 = 1 ∧ v2758 = 1)) → ((v2760 = 1 ↔ v1780 = 1 ∧ v2759 = 1)) → ((v2761 = 1 ↔ v1780 = 1 ∧ v2760 = 1)) → ((v2762 = 1 ↔ v1819 = 1 ∧ v2761 = 1)) → ((v2763 = 1 ↔ v1832 = 1 ∧ v2762 = 1)) → ((v2764 = 1 ↔ v23 = 1 ∧ v2763 = 1)) → ((v2765 = 1 ↔ v1870 = 1 ∧ v2764 = 1)) → ((v2766 = 1 ↔ v1890 = 1 ∧ v2765 = 1)) → ((v2767 = 1 ↔ v1907 = 1 ∧ v2766 = 1)) → ((v2768 = 1 ↔ v23 = 1 ∧ v2767 = 1)) → ((v2769 = 1 ↔ v1911 = 1 ∧ v2768 = 1)) → ((v2770 = 1 ↔ v1911 = 1 ∧ v2769 = 1)) → ((v2771 = 1 ↔ v1945 = 1 ∧ v2770 = 1)) → ((v2772 = 1 ↔ v259 = 1 ∧ v2771 = 1)) → ((v2773 = 1 ↔ v259 = 1 ∧ v2772 = 1)) → ((v2774 = 1 ↔ v290 = 1 ∧ v2773 = 1)) → ((v2775 = 1 ↔ v23 = 1 ∧ v2774 = 1)) → ((v2776 = 1 ↔ v2056 = 1 ∧ v2775 = 1)) → ((v2777 = 1 ↔ v2076 = 1 ∧ v2776 = 1)) → ((v2778 = 1 ↔ v2093 = 1 ∧ v2777 = 1)) → ((v2779 = 1 ↔ v23 = 1 ∧ v2778 = 1)) → ((v2780 = 1 ↔ v2097 = 1 ∧ v2779 = 1)) → ((v2781 = 1 ↔ v2097 = 1 ∧ v2780 = 1)) → ((v2782 = 1 ↔ v2131 = 1 ∧ v2781 = 1)) → ((v2783 = 1 ↔ v584 = 1 ∧ v2782 = 1)) → ((v2784 = 1 ↔ v584 = 1 ∧ v2783 = 1)) → ((v2785 = 1 ↔ v615 = 1 ∧ v2784 = 1)) → ((v2786 = 1 ↔ v23 = 1 ∧ v2785 = 1)) → ((v2787 = 1 ↔ v728 = 1 ∧ v2786 = 1)) → ((v2788 = 1 ↔ v749 = 1 ∧ v2787 = 1)) → ((v2789 = 1 ↔ v766 = 1 ∧ v2788 = 1)) → ((v2790 = 1 ↔ v2275 = 1 ∧ v2789 = 1)) → ((v2791 = 1 ↔ v2302 = 1 ∧ v2790 = 1)) → ((v2792 = 1 ↔ v2372 = 1 ∧ v2791 = 1)) → ((v2793 = 1 ↔ v2469 = 1 ∧ v2792 = 1)) → ((v2794 = 1 ↔ v2537 = 1 ∧ v2793 = 1)) → ((v2795 = 1 ↔ v2634 = 1 ∧ v2794 = 1)) → ((v2796 = 1 ↔ v2710 = 1 ∧ v2795 = 1)) → P) → P := by
  intro v2754 v2755 v2756 v2757 v2758 v2759 v2760 v2761 v2762 v2763 v2764 v2765 v2766 v2767 v2768 v2769 v2770 v2771 v2772 v2773 v2774 v2775 v2776 v2777 v2778 v2779 v2780 v2781 v2782 v2783 v2784 v2785 v2786 v2787 v2788 v2789 v2790 v2791 v2792 v2793 v2794 v2795 v2796
  have hl : 0 < 1 := Nat.one_pos
  have h_v2754 : R 1 0 0 1 v2754 v2754 := (r_land hl h_v1685 h_v2753 (of_decide_eq_true rfl))
  have e_v2754 : (v2754 = 1 ↔ v1685 = 1 ∧ v2753 = 1) := e_land h_v1685 h_v2753 (of_decide_eq_true rfl)
  have h_v2755 : R 1 0 0 1 v2755 v2755 := (r_land hl h_v1724 h_v2754 (of_decide_eq_true rfl))
  have e_v2755 : (v2755 = 1 ↔ v1724 = 1 ∧ v2754 = 1) := e_land h_v1724 h_v2754 (of_decide_eq_true rfl)
  have h_v2756 : R 1 0 0 1 v2756 v2756 := (r_land hl h_v1737 h_v2755 (of_decide_eq_true rfl))
  have e_v2756 : (v2756 = 1 ↔ v1737 = 1 ∧ v2755 = 1) := e_land h_v1737 h_v2755 (of_decide_eq_true rfl)
  have h_v2757 : R 1 0 0 1 v2757 v2757 := (r_land hl h_v1755 h_v2756 (of_decide_eq_true rfl))
  have e_v2757 : (v2757 = 1 ↔ v1755 = 1 ∧ v2756 = 1) := e_land h_v1755 h_v2756 (of_decide_eq_true rfl)
  have h_v2758 : R 1 0 0 1 v2758 v2758 := (r_land hl h_v1756 h_v2757 (of_decide_eq_true rfl))
  have e_v2758 : (v2758 = 1 ↔ v1756 = 1 ∧ v2757 = 1) := e_land h_v1756 h_v2757 (of_decide_eq_true rfl)
  have h_v2759 : R 1 0 0 1 v2759 v2759 := (r_land hl h_v1759 h_v2758 (of_decide_eq_true rfl))
  have e_v2759 : (v2759 = 1 ↔ v1759 = 1 ∧ v2758 = 1) := e_land h_v1759 h_v2758 (of_decide_eq_true rfl)
  have h_v2760 : R 1 0 0 1 v2760 v2760 := (r_land hl h_v1780 h_v2759 (of_decide_eq_true rfl))
  have e_v2760 : (v2760 = 1 ↔ v1780 = 1 ∧ v2759 = 1) := e_land h_v1780 h_v2759 (of_decide_eq_true rfl)
  have h_v2761 : R 1 0 0 1 v2761 v2761 := (r_land hl h_v1780 h_v2760 (of_decide_eq_true rfl))
  have e_v2761 : (v2761 = 1 ↔ v1780 = 1 ∧ v2760 = 1) := e_land h_v1780 h_v2760 (of_decide_eq_true rfl)
  have h_v2762 : R 1 0 0 1 v2762 v2762 := (r_land hl h_v1819 h_v2761 (of_decide_eq_true rfl))
  have e_v2762 : (v2762 = 1 ↔ v1819 = 1 ∧ v2761 = 1) := e_land h_v1819 h_v2761 (of_decide_eq_true rfl)
  have h_v2763 : R 1 0 0 1 v2763 v2763 := (r_land hl h_v1832 h_v2762 (of_decide_eq_true rfl))
  have e_v2763 : (v2763 = 1 ↔ v1832 = 1 ∧ v2762 = 1) := e_land h_v1832 h_v2762 (of_decide_eq_true rfl)
  have h_v2764 : R 1 0 0 1 v2764 v2764 := (r_land hl h_v23 h_v2763 (of_decide_eq_true rfl))
  have e_v2764 : (v2764 = 1 ↔ v23 = 1 ∧ v2763 = 1) := e_land h_v23 h_v2763 (of_decide_eq_true rfl)
  have h_v2765 : R 1 0 0 1 v2765 v2765 := (r_land hl h_v1870 h_v2764 (of_decide_eq_true rfl))
  have e_v2765 : (v2765 = 1 ↔ v1870 = 1 ∧ v2764 = 1) := e_land h_v1870 h_v2764 (of_decide_eq_true rfl)
  have h_v2766 : R 1 0 0 1 v2766 v2766 := (r_land hl h_v1890 h_v2765 (of_decide_eq_true rfl))
  clear h_v2754 h_v2755 h_v2756 h_v2757 h_v2758 h_v2759 h_v2760 h_v2761 h_v2762 h_v2763 h_v2764
  have e_v2766 : (v2766 = 1 ↔ v1890 = 1 ∧ v2765 = 1) := e_land h_v1890 h_v2765 (of_decide_eq_true rfl)
  have h_v2767 : R 1 0 0 1 v2767 v2767 := (r_land hl h_v1907 h_v2766 (of_decide_eq_true rfl))
  have e_v2767 : (v2767 = 1 ↔ v1907 = 1 ∧ v2766 = 1) := e_land h_v1907 h_v2766 (of_decide_eq_true rfl)
  have h_v2768 : R 1 0 0 1 v2768 v2768 := (r_land hl h_v23 h_v2767 (of_decide_eq_true rfl))
  have e_v2768 : (v2768 = 1 ↔ v23 = 1 ∧ v2767 = 1) := e_land h_v23 h_v2767 (of_decide_eq_true rfl)
  have h_v2769 : R 1 0 0 1 v2769 v2769 := (r_land hl h_v1911 h_v2768 (of_decide_eq_true rfl))
  have e_v2769 : (v2769 = 1 ↔ v1911 = 1 ∧ v2768 = 1) := e_land h_v1911 h_v2768 (of_decide_eq_true rfl)
  have h_v2770 : R 1 0 0 1 v2770 v2770 := (r_land hl h_v1911 h_v2769 (of_decide_eq_true rfl))
  have e_v2770 : (v2770 = 1 ↔ v1911 = 1 ∧ v2769 = 1) := e_land h_v1911 h_v2769 (of_decide_eq_true rfl)
  have h_v2771 : R 1 0 0 1 v2771 v2771 := (r_land hl h_v1945 h_v2770 (of_decide_eq_true rfl))
  have e_v2771 : (v2771 = 1 ↔ v1945 = 1 ∧ v2770 = 1) := e_land h_v1945 h_v2770 (of_decide_eq_true rfl)
  have h_v2772 : R 1 0 0 1 v2772 v2772 := (r_land hl h_v259 h_v2771 (of_decide_eq_true rfl))
  have e_v2772 : (v2772 = 1 ↔ v259 = 1 ∧ v2771 = 1) := e_land h_v259 h_v2771 (of_decide_eq_true rfl)
  have h_v2773 : R 1 0 0 1 v2773 v2773 := (r_land hl h_v259 h_v2772 (of_decide_eq_true rfl))
  have e_v2773 : (v2773 = 1 ↔ v259 = 1 ∧ v2772 = 1) := e_land h_v259 h_v2772 (of_decide_eq_true rfl)
  have h_v2774 : R 1 0 0 1 v2774 v2774 := (r_land hl h_v290 h_v2773 (of_decide_eq_true rfl))
  have e_v2774 : (v2774 = 1 ↔ v290 = 1 ∧ v2773 = 1) := e_land h_v290 h_v2773 (of_decide_eq_true rfl)
  have h_v2775 : R 1 0 0 1 v2775 v2775 := (r_land hl h_v23 h_v2774 (of_decide_eq_true rfl))
  have e_v2775 : (v2775 = 1 ↔ v23 = 1 ∧ v2774 = 1) := e_land h_v23 h_v2774 (of_decide_eq_true rfl)
  have h_v2776 : R 1 0 0 1 v2776 v2776 := (r_land hl h_v2056 h_v2775 (of_decide_eq_true rfl))
  have e_v2776 : (v2776 = 1 ↔ v2056 = 1 ∧ v2775 = 1) := e_land h_v2056 h_v2775 (of_decide_eq_true rfl)
  have h_v2777 : R 1 0 0 1 v2777 v2777 := (r_land hl h_v2076 h_v2776 (of_decide_eq_true rfl))
  have e_v2777 : (v2777 = 1 ↔ v2076 = 1 ∧ v2776 = 1) := e_land h_v2076 h_v2776 (of_decide_eq_true rfl)
  have h_v2778 : R 1 0 0 1 v2778 v2778 := (r_land hl h_v2093 h_v2777 (of_decide_eq_true rfl))
  have e_v2778 : (v2778 = 1 ↔ v2093 = 1 ∧ v2777 = 1) := e_land h_v2093 h_v2777 (of_decide_eq_true rfl)
  clear h_v2765 h_v2766 h_v2767 h_v2768 h_v2769 h_v2770 h_v2771 h_v2772 h_v2773 h_v2774 h_v2775 h_v2776 h_v2777
  have h_v2779 : R 1 0 0 1 v2779 v2779 := (r_land hl h_v23 h_v2778 (of_decide_eq_true rfl))
  have e_v2779 : (v2779 = 1 ↔ v23 = 1 ∧ v2778 = 1) := e_land h_v23 h_v2778 (of_decide_eq_true rfl)
  have h_v2780 : R 1 0 0 1 v2780 v2780 := (r_land hl h_v2097 h_v2779 (of_decide_eq_true rfl))
  have e_v2780 : (v2780 = 1 ↔ v2097 = 1 ∧ v2779 = 1) := e_land h_v2097 h_v2779 (of_decide_eq_true rfl)
  have h_v2781 : R 1 0 0 1 v2781 v2781 := (r_land hl h_v2097 h_v2780 (of_decide_eq_true rfl))
  have e_v2781 : (v2781 = 1 ↔ v2097 = 1 ∧ v2780 = 1) := e_land h_v2097 h_v2780 (of_decide_eq_true rfl)
  have h_v2782 : R 1 0 0 1 v2782 v2782 := (r_land hl h_v2131 h_v2781 (of_decide_eq_true rfl))
  have e_v2782 : (v2782 = 1 ↔ v2131 = 1 ∧ v2781 = 1) := e_land h_v2131 h_v2781 (of_decide_eq_true rfl)
  have h_v2783 : R 1 0 0 1 v2783 v2783 := (r_land hl h_v584 h_v2782 (of_decide_eq_true rfl))
  have e_v2783 : (v2783 = 1 ↔ v584 = 1 ∧ v2782 = 1) := e_land h_v584 h_v2782 (of_decide_eq_true rfl)
  have h_v2784 : R 1 0 0 1 v2784 v2784 := (r_land hl h_v584 h_v2783 (of_decide_eq_true rfl))
  have e_v2784 : (v2784 = 1 ↔ v584 = 1 ∧ v2783 = 1) := e_land h_v584 h_v2783 (of_decide_eq_true rfl)
  have h_v2785 : R 1 0 0 1 v2785 v2785 := (r_land hl h_v615 h_v2784 (of_decide_eq_true rfl))
  have e_v2785 : (v2785 = 1 ↔ v615 = 1 ∧ v2784 = 1) := e_land h_v615 h_v2784 (of_decide_eq_true rfl)
  have h_v2786 : R 1 0 0 1 v2786 v2786 := (r_land hl h_v23 h_v2785 (of_decide_eq_true rfl))
  have e_v2786 : (v2786 = 1 ↔ v23 = 1 ∧ v2785 = 1) := e_land h_v23 h_v2785 (of_decide_eq_true rfl)
  have h_v2787 : R 1 0 0 1 v2787 v2787 := (r_land hl h_v728 h_v2786 (of_decide_eq_true rfl))
  have e_v2787 : (v2787 = 1 ↔ v728 = 1 ∧ v2786 = 1) := e_land h_v728 h_v2786 (of_decide_eq_true rfl)
  have h_v2788 : R 1 0 0 1 v2788 v2788 := (r_land hl h_v749 h_v2787 (of_decide_eq_true rfl))
  have e_v2788 : (v2788 = 1 ↔ v749 = 1 ∧ v2787 = 1) := e_land h_v749 h_v2787 (of_decide_eq_true rfl)
  have h_v2789 : R 1 0 0 1 v2789 v2789 := (r_land hl h_v766 h_v2788 (of_decide_eq_true rfl))
  have e_v2789 : (v2789 = 1 ↔ v766 = 1 ∧ v2788 = 1) := e_land h_v766 h_v2788 (of_decide_eq_true rfl)
  have h_v2790 : R 1 0 0 1 v2790 v2790 := (r_land hl h_v2275 h_v2789 (of_decide_eq_true rfl))
  have e_v2790 : (v2790 = 1 ↔ v2275 = 1 ∧ v2789 = 1) := e_land h_v2275 h_v2789 (of_decide_eq_true rfl)
  have h_v2791 : R 1 0 0 1 v2791 v2791 := (r_land hl h_v2302 h_v2790 (of_decide_eq_true rfl))
  clear h_v2778 h_v2779 h_v2780 h_v2781 h_v2782 h_v2783 h_v2784 h_v2785 h_v2786 h_v2787 h_v2788 h_v2789
  have e_v2791 : (v2791 = 1 ↔ v2302 = 1 ∧ v2790 = 1) := e_land h_v2302 h_v2790 (of_decide_eq_true rfl)
  have h_v2792 : R 1 0 0 1 v2792 v2792 := (r_land hl h_v2372 h_v2791 (of_decide_eq_true rfl))
  have e_v2792 : (v2792 = 1 ↔ v2372 = 1 ∧ v2791 = 1) := e_land h_v2372 h_v2791 (of_decide_eq_true rfl)
  have h_v2793 : R 1 0 0 1 v2793 v2793 := (r_land hl h_v2469 h_v2792 (of_decide_eq_true rfl))
  have e_v2793 : (v2793 = 1 ↔ v2469 = 1 ∧ v2792 = 1) := e_land h_v2469 h_v2792 (of_decide_eq_true rfl)
  have h_v2794 : R 1 0 0 1 v2794 v2794 := (r_land hl h_v2537 h_v2793 (of_decide_eq_true rfl))
  have e_v2794 : (v2794 = 1 ↔ v2537 = 1 ∧ v2793 = 1) := e_land h_v2537 h_v2793 (of_decide_eq_true rfl)
  have h_v2795 : R 1 0 0 1 v2795 v2795 := (r_land hl h_v2634 h_v2794 (of_decide_eq_true rfl))
  have e_v2795 : (v2795 = 1 ↔ v2634 = 1 ∧ v2794 = 1) := e_land h_v2634 h_v2794 (of_decide_eq_true rfl)
  have h_v2796 : R 1 0 0 1 v2796 v2796 := (r_land hl h_v2710 h_v2795 (of_decide_eq_true rfl))
  have e_v2796 : (v2796 = 1 ↔ v2710 = 1 ∧ v2795 = 1) := e_land h_v2710 h_v2795 (of_decide_eq_true rfl)
  exact fun _ k => k e_v2754 e_v2755 e_v2756 e_v2757 e_v2758 e_v2759 e_v2760 e_v2761 e_v2762 e_v2763 e_v2764 e_v2765 e_v2766 e_v2767 e_v2768 e_v2769 e_v2770 e_v2771 e_v2772 e_v2773 e_v2774 e_v2775 e_v2776 e_v2777 e_v2778 e_v2779 e_v2780 e_v2781 e_v2782 e_v2783 e_v2784 e_v2785 e_v2786 e_v2787 e_v2788 e_v2789 e_v2790 e_v2791 e_v2792 e_v2793 e_v2794 e_v2795 e_v2796

end Tammes15.D3Trig
