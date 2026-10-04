import Tammes15.D3Ck2.Prog.F0L
import Tammes15.D3Prog.Sem

namespace D3Prog

open D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progF0L_seg4 (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (hb_H4 : H4 < 2 ^ 64) (v13 : ℕ) (v37 : ℕ) (v92 : ℕ) (v100 : ℕ) (v110 : ℕ) (v265 : ℕ) (v270 : ℕ) (v423 : ℕ) (v471 : ℕ) (v474 : ℕ) (v620 : ℕ) (v625 : ℕ) (v796 : ℕ) (v910 : ℕ) (v1083 : ℕ) (v1273 : ℕ) (v1348 : ℕ) (v1519 : ℕ) (v1709 : ℕ) (v1718 : ℕ) (v1719 : ℕ) (v1751 : ℕ) (v1790 : ℕ) (v1825 : ℕ) (v1826 : ℕ) (v1858 : ℕ) (v1897 : ℕ) (v1953 : ℕ) (v2001 : ℕ) (v2007 : ℕ) (v2165 : ℕ) (v2213 : ℕ) (v2219 : ℕ) (v2380 : ℕ) (v2382 : ℕ) (v2481 : ℕ) (v2482 : ℕ) (v2485 : ℕ) (v2486 : ℕ) (v2490 : ℕ) (v2670 : ℕ) (v2674 : ℕ) (v2675 : ℕ) (v2678 : ℕ) (h_v13 : R 1 0 0 1 v13 v13) (h_v37 : R 1 0 0 1 v37 v37) (h_v92 : R 1 0 0 1 v92 v92) (h_v100 : R 1 0 4611686018158952441 4611686018695823359 v100 v100) (h_v110 : R 1 0 0 1 v110 v110) (h_v265 : R 1 0 4611686017353646081 4611686019501129727 v265 v265) (h_v270 : R 1 0 0 1 v270 v270) (h_v423 : R 1 0 0 1 v423 v423) (h_v471 : R 1 0 0 1 v471 v471) (h_v474 : R 1 0 0 1 v474 v474) (h_v620 : R 1 0 4611686017353646081 4611686019501129727 v620 v620) (h_v625 : R 1 0 0 1 v625 v625) (h_v796 : R 1 0 0 1 v796 v796) (h_v910 : R 1 0 0 1 v910 v910) (h_v1083 : R 1 0 0 1 v1083 v1083) (h_v1273 : R 1 0 0 1 v1273 v1273) (h_v1348 : R 1 0 0 1 v1348 v1348) (h_v1519 : R 1 0 0 1 v1519 v1519) (h_v1709 : R 1 0 0 1 v1709 v1709) (h_v1718 : R 1 0 0 1 v1718 v1718) (h_v1719 : R 1 0 0 1 v1719 v1719) (h_v1751 : R 1 0 0 1 v1751 v1751) (h_v1790 : R 1 0 0 1 v1790 v1790) (h_v1825 : R 1 0 0 1 v1825 v1825) (h_v1826 : R 1 0 0 1 v1826 v1826) (h_v1858 : R 1 0 0 1 v1858 v1858) (h_v1897 : R 1 0 0 1 v1897 v1897) (h_v1953 : R 1 0 0 1 v1953 v1953) (h_v2001 : R 1 0 0 1 v2001 v2001) (h_v2007 : R 1 0 0 1 v2007 v2007) (h_v2165 : R 1 0 0 1 v2165 v2165) (h_v2213 : R 1 0 0 1 v2213 v2213) (h_v2219 : R 1 0 0 1 v2219 v2219) (h_v2380 : R 1 0 0 1 v2380 v2380) (h_v2382 : R 1 0 0 1 v2382 v2382) (h_v2481 : R 1 0 4611686018427387899 4611686018695823375 v2481 v2481) (h_v2482 : R 1 0 4611686018427387899 4611686018695823375 v2482 v2482) (h_v2485 : R 1 0 4611686018427387899 4611686018695823375 v2485 v2485) (h_v2486 : R 1 0 4611686018427387899 4611686018695823375 v2486 v2486) (h_v2490 : R 1 0 0 1 v2490 v2490) (h_v2670 : R 1 0 0 1 v2670 v2670) (h_v2674 : R 1 0 4611686017890516869 4611686018964258885 v2674 v2674) (h_v2675 : R 1 0 4611686018427387893 4611686018695823369 v2675 v2675) (h_v2678 : R 1 0 0 1 v2678 v2678) :
    let OFFr := Nat.mul 1 4611686018427387904
    let v6 := ix 1 F3 0
    let v18 := Nat.mul 1 4611686018427387900
    let v23 := Nat.mul 1 4611686018695823360
    let v51 := Nat.mul 1 4611686018427387904
    let v95 := Nat.mul 1 4611686018158952448
    let v105 := Nat.mul 1 4611686018427387905
    let v780 := Nat.mul 1 4611686019270702760
    let v965 := Nat.mul 1 4683743612465315840
    let v992 := Nat.mul 1 4647714815446351872
    let v2684 := smx 29 1 v2482 v2482
    let v2685 := srdC 1 v2684
    let v2686 := Nat.sub (Nat.add v2685 v2685) OFFr
    let v2687 := Nat.sub (Nat.add v23 OFFr) v2686
    let v2688 := plt 1 v2687 v95
    let v2689 := psel (pmask v2688) v95 v2687
    let v2690 := smx 29 1 v2481 v2481
    let v2691 := srdF 1 v2690
    let v2692 := Nat.sub (Nat.add v2691 v2691) OFFr
    let v2693 := Nat.sub (Nat.add v23 OFFr) v2692
    let v2694 := smx 29 1 v2486 v2486
    let v2695 := srdC 1 v2694
    let v2696 := Nat.sub (Nat.add v2695 v2695) OFFr
    let v2697 := Nat.sub (Nat.add v23 OFFr) v2696
    let v2698 := plt 1 v2697 v95
    let v2699 := psel (pmask v2698) v95 v2697
    let v2700 := smx 29 1 v2485 v2485
    let v2701 := srdF 1 v2700
    let v2702 := Nat.sub (Nat.add v2701 v2701) OFFr
    let v2703 := Nat.sub (Nat.add v23 OFFr) v2702
    let v2704 := plt 1 v2689 v51
    let v2706 := plt 1 v51 v2693
    let v2707 := Nat.sub 1 v2706
    let v2708 := Nat.land v2704 v2707
    let v2709 := Nat.land v2704 v2706
    let v2710 := plt 1 v2699 v51
    let v2712 := plt 1 v51 v2703
    let v2713 := Nat.sub 1 v2712
    let v2714 := Nat.land v2710 v2713
    let v2715 := Nat.land v2710 v2712
    let v2716 := Nat.land v2709 v2715
    let v2724 := Nat.land v2708 v2715
    let v2725 := Nat.lor v2714 v2724
    let v2726 := psel (pmask v2725) v2689 v2693
    let v2727 := Nat.land v2709 v2714
    let v2728 := Nat.lor v2708 v2727
    let v2729 := psel (pmask v2728) v2699 v2703
    let v2732 := smx 30 1 v2729 v2726
    let v2733 := srdC 1 v2732
    let v2736 := smx 30 1 v2699 v2689
    let v2737 := srdC 1 v2736
    let v2740 := plt 1 v2733 v2737
    let v2741 := psel (pmask v2740) v2737 v2733
    let v2743 := psel (pmask v2716) v2741 v2733
    let v2744 := Nat.sub (Nat.add v100 OFFr) v2743
    let v2746 := Nat.sub (Nat.add v965 OFFr) v2690
    let v2747 := psqrt 1 v2746
    let v2748 := Nat.sub (Nat.add v105 v2747) OFFr
    let v2749 := smx 29 1 v2747 v2481
    let v2750 := srdF 1 v2749
    let v2751 := Nat.sub (Nat.add v2750 v2750) OFFr
    let v2752 := smx 29 1 v2748 v2481
    let v2753 := srdC 1 v2752
    let v2754 := Nat.sub (Nat.add v2753 v2753) OFFr
    let v2755 := plt 1 v2754 v23
    let v2756 := psel (pmask v2755) v2754 v23
    let v2757 := Nat.sub (Nat.add v965 OFFr) v2684
    let v2758 := psqrt 1 v2757
    let v2759 := Nat.sub (Nat.add v105 v2758) OFFr
    let v2760 := smx 29 1 v2758 v2482
    let v2761 := srdF 1 v2760
    let v2762 := Nat.sub (Nat.add v2761 v2761) OFFr
    let v2763 := smx 29 1 v2759 v2482
    let v2764 := srdC 1 v2763
    let v2765 := Nat.sub (Nat.add v2764 v2764) OFFr
    let v2766 := plt 1 v2765 v23
    let v2767 := psel (pmask v2766) v2765 v23
    let v2768 := plt 1 v2751 v2762
    let v2769 := psel (pmask v2768) v2751 v2762
    let v2770 := plt 1 v2756 v2767
    let v2771 := psel (pmask v2770) v2767 v2756
    let v2772 := plt 1 v992 v2690
    let v2773 := Nat.sub 1 v2772
    let v2774 := plt 1 v2684 v992
    let v2775 := Nat.sub 1 v2774
    let v2776 := Nat.land v2773 v2775
    let v2777 := psel (pmask v2776) v23 v2771
    let v2778 := Nat.sub (Nat.add v965 OFFr) v2700
    let v2779 := psqrt 1 v2778
    let v2780 := Nat.sub (Nat.add v105 v2779) OFFr
    let v2781 := smx 29 1 v2779 v2485
    let v2782 := srdF 1 v2781
    let v2783 := Nat.sub (Nat.add v2782 v2782) OFFr
    let v2784 := smx 29 1 v2780 v2485
    let v2785 := srdC 1 v2784
    let v2786 := Nat.sub (Nat.add v2785 v2785) OFFr
    let v2787 := plt 1 v2786 v23
    let v2788 := psel (pmask v2787) v2786 v23
    let v2789 := Nat.sub (Nat.add v965 OFFr) v2694
    let v2790 := psqrt 1 v2789
    let v2791 := Nat.sub (Nat.add v105 v2790) OFFr
    let v2792 := smx 29 1 v2790 v2486
    let v2793 := srdF 1 v2792
    let v2794 := Nat.sub (Nat.add v2793 v2793) OFFr
    let v2795 := smx 29 1 v2791 v2486
    let v2796 := srdC 1 v2795
    let v2797 := Nat.sub (Nat.add v2796 v2796) OFFr
    let v2798 := plt 1 v2797 v23
    let v2799 := psel (pmask v2798) v2797 v23
    let v2800 := plt 1 v2783 v2794
    let v2801 := psel (pmask v2800) v2783 v2794
    let v2802 := plt 1 v2788 v2799
    let v2803 := psel (pmask v2802) v2799 v2788
    let v2804 := plt 1 v992 v2700
    let v2805 := Nat.sub 1 v2804
    let v2806 := plt 1 v2694 v992
    let v2807 := Nat.sub 1 v2806
    let v2808 := Nat.land v2805 v2807
    let v2809 := psel (pmask v2808) v23 v2803
    let v2810 := plt 1 v2769 v51
    let v2811 := Nat.sub 1 v2810
    let v2812 := plt 1 v51 v2777
    let v2813 := Nat.sub 1 v2812
    let v2814 := Nat.land v2810 v2813
    let v2815 := Nat.land v2810 v2812
    let v2816 := plt 1 v2801 v51
    let v2818 := plt 1 v51 v2809
    let v2819 := Nat.sub 1 v2818
    let v2820 := Nat.land v2816 v2819
    let v2821 := Nat.land v2816 v2818
    let v2822 := Nat.land v2815 v2821
    let v2823 := Nat.land v2811 v2821
    let v2824 := Nat.lor v2820 v2823
    let v2825 := psel (pmask v2824) v2777 v2769
    let v2826 := Nat.sub 1 v2820
    let v2827 := Nat.land v2815 v2826
    let v2828 := Nat.lor v2814 v2827
    let v2829 := psel (pmask v2828) v2809 v2801
    let v2830 := Nat.land v2814 v2821
    let v2831 := Nat.lor v2820 v2830
    let v2832 := psel (pmask v2831) v2769 v2777
    let v2833 := Nat.land v2815 v2820
    let v2834 := Nat.lor v2814 v2833
    let v2835 := psel (pmask v2834) v2801 v2809
    let v2836 := smx 29 1 v2829 v2825
    let v2837 := srdF 1 v2836
    let v2838 := smx 29 1 v2835 v2832
    let v2839 := srdC 1 v2838
    let v2840 := smx 29 1 v2801 v2777
    let v2841 := srdF 1 v2840
    let v2842 := smx 29 1 v2801 v2769
    let v2843 := srdC 1 v2842
    let v2844 := plt 1 v2837 v2841
    let v2845 := psel (pmask v2844) v2837 v2841
    let v2846 := plt 1 v2839 v2843
    let v2847 := psel (pmask v2846) v2843 v2839
    let v2848 := psel (pmask v2822) v2845 v2837
    let v2849 := psel (pmask v2822) v2847 v2839
    let v2850 := plt 1 v51 v2848
    let v2852 := plt 1 v2744 v51
    let v2853 := psel (pmask v2852) v2848 v2849
    let v2856 := plt 1 v2853 v2744
    let v2857 := Nat.land v2850 v2856
    let v2864 := Nat.lor v2670 v2857
    let v2866 := hxa 1 H4 0
    let v2867 := plt 1 v51 v2866
    let v2868 := Nat.sub 1 v2867
    let t2866 := sc28u 1 v2866
    let v2870 := Nat.sub (Nat.add v18 t2866.2) OFFr
    let v2871 := plt 1 v2870 v95
    let v2872 := psel (pmask v2871) v95 v2870
    let v2873 := sshl 1 v2674
    let v2874 := smx 29 1 v2872 v2675
    let v2875 := plt 1 v2874 v2873
    let v2876 := Nat.sub 1 v2875
    let v2877 := plt 1 v780 v2866
    let v2878 := Nat.sub 1 v2877
    let v2879 := Nat.land v2876 v2878
    let v2880 := Nat.lor v2868 v2879
    let v2881 := psel (pmask v2880) v2866 v51
    let v2895 := psel (pmask v2380) v2881 v51
    let v2897 := Nat.land v2380 v2864
    let v2898 := psel (pmask v2670) v780 v51
    let v2900 := psel (pmask v2897) v2898 v2895
    let v2902 := Nat.sub (Nat.add v265 v2900) OFFr
    let v2904 := Nat.sub (Nat.add v620 v2902) OFFr
    let v2906 := plt 1 v2904 v6
    let v2907 := Nat.sub 1 v2906
    let v2911 := Nat.land v13 v37
    let v2912 := Nat.land v92 v2911
    let v2913 := Nat.land v13 v2912
    let v2914 := Nat.land v110 v2913
    let v2915 := Nat.land v110 v2914
    let v2916 := Nat.land v270 v2915
    let v2917 := Nat.land v270 v2916
    let v2918 := Nat.land v13 v2917
    let v2919 := Nat.land v423 v2918
    let v2920 := Nat.land v471 v2919
    let v2921 := Nat.land v13 v2920
    let v2922 := Nat.land v474 v2921
    let v2923 := Nat.land v474 v2922
    let v2924 := Nat.land v625 v2923
    let v2925 := Nat.land v625 v2924
    let v2926 := Nat.land v796 v2925
    let v2927 := Nat.land v910 v2926
    let v2928 := Nat.land v910 v2927
    let v2929 := Nat.land v1083 v2928
    let v2930 := Nat.land v1083 v2929
    let v2931 := Nat.land v1273 v2930
    let v2932 := Nat.land v796 v2931
    let v2933 := Nat.land v1348 v2932
    let v2934 := Nat.land v1348 v2933
    let v2935 := Nat.land v1519 v2934
    let v2936 := Nat.land v1519 v2935
    let v2937 := Nat.land v1709 v2936
    let v2938 := Nat.land v1718 v2937
    let v2939 := Nat.land v1719 v2938
    let v2940 := Nat.land v1751 v2939
    let v2941 := Nat.land v1751 v2940
    let v2942 := Nat.land v1790 v2941
    let v2943 := Nat.land v1825 v2942
    let v2944 := Nat.land v1826 v2943
    let v2945 := Nat.land v1858 v2944
    let v2946 := Nat.land v1858 v2945
    let v2947 := Nat.land v1897 v2946
    let v2948 := Nat.land v13 v2947
    let v2949 := Nat.land v1953 v2948
    let v2950 := Nat.land v2001 v2949
    let v2951 := Nat.land v13 v2950
    let v2952 := Nat.land v110 v2951
    let v2953 := Nat.land v110 v2952
    let v2954 := Nat.land v2007 v2953
    let v2955 := Nat.land v2007 v2954
    let v2956 := Nat.land v13 v2955
    let v2957 := Nat.land v2165 v2956
    let v2958 := Nat.land v2213 v2957
    let v2959 := Nat.land v13 v2958
    let v2960 := Nat.land v474 v2959
    let v2961 := Nat.land v474 v2960
    let v2962 := Nat.land v2219 v2961
    let v2963 := Nat.land v2219 v2962
    let v2964 := Nat.land v2382 v2963
    let v2965 := Nat.land v2490 v2964
    let v2966 := Nat.land v2678 v2965
    let v2967 := Nat.land v2907 v2966
    ∀ (P : Prop), ((sv v2684 = sv v2482 * sv v2482) → (sv v2685 = -((-sv v2684) / 2 ^ 28)) → (sv v2686 = sv v2685 + sv v2685) → (sv v2687 = sv v23 - sv v2686) → ((v2688 = 1 ↔ sv v2687 < sv v95)) → (v2689 = if v2688 = 1 then v95 else v2687) → (sv v2690 = sv v2481 * sv v2481) → (sv v2691 = sv v2690 / 2 ^ 28) → (sv v2692 = sv v2691 + sv v2691) → (sv v2693 = sv v23 - sv v2692) → (sv v2694 = sv v2486 * sv v2486) → (sv v2695 = -((-sv v2694) / 2 ^ 28)) → (sv v2696 = sv v2695 + sv v2695) → (sv v2697 = sv v23 - sv v2696) → ((v2698 = 1 ↔ sv v2697 < sv v95)) → (v2699 = if v2698 = 1 then v95 else v2697) → (sv v2700 = sv v2485 * sv v2485) → (sv v2701 = sv v2700 / 2 ^ 28) → (sv v2702 = sv v2701 + sv v2701) → (sv v2703 = sv v23 - sv v2702) → ((v2704 = 1 ↔ sv v2689 < sv v51)) → ((v2706 = 1 ↔ sv v51 < sv v2693)) → ((v2707 = 1 ↔ ¬v2706 = 1)) → ((v2708 = 1 ↔ v2704 = 1 ∧ v2707 = 1)) → ((v2709 = 1 ↔ v2704 = 1 ∧ v2706 = 1)) → ((v2710 = 1 ↔ sv v2699 < sv v51)) → ((v2712 = 1 ↔ sv v51 < sv v2703)) → ((v2713 = 1 ↔ ¬v2712 = 1)) → ((v2714 = 1 ↔ v2710 = 1 ∧ v2713 = 1)) → ((v2715 = 1 ↔ v2710 = 1 ∧ v2712 = 1)) → ((v2716 = 1 ↔ v2709 = 1 ∧ v2715 = 1)) → ((v2724 = 1 ↔ v2708 = 1 ∧ v2715 = 1)) → ((v2725 = 1 ↔ v2714 = 1 ∨ v2724 = 1)) → (v2726 = if v2725 = 1 then v2689 else v2693) → ((v2727 = 1 ↔ v2709 = 1 ∧ v2714 = 1)) → ((v2728 = 1 ↔ v2708 = 1 ∨ v2727 = 1)) → (v2729 = if v2728 = 1 then v2699 else v2703) → (sv v2732 = sv v2729 * sv v2726) → (sv v2733 = -((-sv v2732) / 2 ^ 28)) → (sv v2736 = sv v2699 * sv v2689) → (sv v2737 = -((-sv v2736) / 2 ^ 28)) → ((v2740 = 1 ↔ sv v2733 < sv v2737)) → (v2741 = if v2740 = 1 then v2737 else v2733) → (v2743 = if v2716 = 1 then v2741 else v2733) → (sv v2744 = sv v100 - sv v2743) → (sv v2746 = sv v965 - sv v2690) → (sv v2747 = ((Nat.sqrt (v2746 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2748 = sv v105 + sv v2747) → (sv v2749 = sv v2747 * sv v2481) → (sv v2750 = sv v2749 / 2 ^ 28) → (sv v2751 = sv v2750 + sv v2750) → (sv v2752 = sv v2748 * sv v2481) → (sv v2753 = -((-sv v2752) / 2 ^ 28)) → (sv v2754 = sv v2753 + sv v2753) → ((v2755 = 1 ↔ sv v2754 < sv v23)) → (v2756 = if v2755 = 1 then v2754 else v23) → (sv v2757 = sv v965 - sv v2684) → (sv v2758 = ((Nat.sqrt (v2757 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2759 = sv v105 + sv v2758) → (sv v2760 = sv v2758 * sv v2482) → (sv v2761 = sv v2760 / 2 ^ 28) → (sv v2762 = sv v2761 + sv v2761) → (sv v2763 = sv v2759 * sv v2482) → (sv v2764 = -((-sv v2763) / 2 ^ 28)) → (sv v2765 = sv v2764 + sv v2764) → ((v2766 = 1 ↔ sv v2765 < sv v23)) → (v2767 = if v2766 = 1 then v2765 else v23) → ((v2768 = 1 ↔ sv v2751 < sv v2762)) → (v2769 = if v2768 = 1 then v2751 else v2762) → ((v2770 = 1 ↔ sv v2756 < sv v2767)) → (v2771 = if v2770 = 1 then v2767 else v2756) → ((v2772 = 1 ↔ sv v992 < sv v2690)) → ((v2773 = 1 ↔ ¬v2772 = 1)) → ((v2774 = 1 ↔ sv v2684 < sv v992)) → ((v2775 = 1 ↔ ¬v2774 = 1)) → ((v2776 = 1 ↔ v2773 = 1 ∧ v2775 = 1)) → (v2777 = if v2776 = 1 then v23 else v2771) → (sv v2778 = sv v965 - sv v2700) → (sv v2779 = ((Nat.sqrt (v2778 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2780 = sv v105 + sv v2779) → (sv v2781 = sv v2779 * sv v2485) → (sv v2782 = sv v2781 / 2 ^ 28) → (sv v2783 = sv v2782 + sv v2782) → (sv v2784 = sv v2780 * sv v2485) → (sv v2785 = -((-sv v2784) / 2 ^ 28)) → (sv v2786 = sv v2785 + sv v2785) → ((v2787 = 1 ↔ sv v2786 < sv v23)) → (v2788 = if v2787 = 1 then v2786 else v23) → (sv v2789 = sv v965 - sv v2694) → (sv v2790 = ((Nat.sqrt (v2789 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2791 = sv v105 + sv v2790) → (sv v2792 = sv v2790 * sv v2486) → (sv v2793 = sv v2792 / 2 ^ 28) → (sv v2794 = sv v2793 + sv v2793) → (sv v2795 = sv v2791 * sv v2486) → (sv v2796 = -((-sv v2795) / 2 ^ 28)) → (sv v2797 = sv v2796 + sv v2796) → ((v2798 = 1 ↔ sv v2797 < sv v23)) → (v2799 = if v2798 = 1 then v2797 else v23) → ((v2800 = 1 ↔ sv v2783 < sv v2794)) → (v2801 = if v2800 = 1 then v2783 else v2794) → ((v2802 = 1 ↔ sv v2788 < sv v2799)) → (v2803 = if v2802 = 1 then v2799 else v2788) → ((v2804 = 1 ↔ sv v992 < sv v2700)) → ((v2805 = 1 ↔ ¬v2804 = 1)) → ((v2806 = 1 ↔ sv v2694 < sv v992)) → ((v2807 = 1 ↔ ¬v2806 = 1)) → ((v2808 = 1 ↔ v2805 = 1 ∧ v2807 = 1)) → (v2809 = if v2808 = 1 then v23 else v2803) → ((v2810 = 1 ↔ sv v2769 < sv v51)) → ((v2811 = 1 ↔ ¬v2810 = 1)) → ((v2812 = 1 ↔ sv v51 < sv v2777)) → ((v2813 = 1 ↔ ¬v2812 = 1)) → ((v2814 = 1 ↔ v2810 = 1 ∧ v2813 = 1)) → ((v2815 = 1 ↔ v2810 = 1 ∧ v2812 = 1)) → ((v2816 = 1 ↔ sv v2801 < sv v51)) → ((v2818 = 1 ↔ sv v51 < sv v2809)) → ((v2819 = 1 ↔ ¬v2818 = 1)) → ((v2820 = 1 ↔ v2816 = 1 ∧ v2819 = 1)) → ((v2821 = 1 ↔ v2816 = 1 ∧ v2818 = 1)) → ((v2822 = 1 ↔ v2815 = 1 ∧ v2821 = 1)) → ((v2823 = 1 ↔ v2811 = 1 ∧ v2821 = 1)) → ((v2824 = 1 ↔ v2820 = 1 ∨ v2823 = 1)) → (v2825 = if v2824 = 1 then v2777 else v2769) → ((v2826 = 1 ↔ ¬v2820 = 1)) → ((v2827 = 1 ↔ v2815 = 1 ∧ v2826 = 1)) → ((v2828 = 1 ↔ v2814 = 1 ∨ v2827 = 1)) → (v2829 = if v2828 = 1 then v2809 else v2801) → ((v2830 = 1 ↔ v2814 = 1 ∧ v2821 = 1)) → ((v2831 = 1 ↔ v2820 = 1 ∨ v2830 = 1)) → (v2832 = if v2831 = 1 then v2769 else v2777) → ((v2833 = 1 ↔ v2815 = 1 ∧ v2820 = 1)) → ((v2834 = 1 ↔ v2814 = 1 ∨ v2833 = 1)) → (v2835 = if v2834 = 1 then v2801 else v2809) → (sv v2836 = sv v2829 * sv v2825) → (sv v2837 = sv v2836 / 2 ^ 28) → (sv v2838 = sv v2835 * sv v2832) → (sv v2839 = -((-sv v2838) / 2 ^ 28)) → (sv v2840 = sv v2801 * sv v2777) → (sv v2841 = sv v2840 / 2 ^ 28) → (sv v2842 = sv v2801 * sv v2769) → (sv v2843 = -((-sv v2842) / 2 ^ 28)) → ((v2844 = 1 ↔ sv v2837 < sv v2841)) → (v2845 = if v2844 = 1 then v2837 else v2841) → ((v2846 = 1 ↔ sv v2839 < sv v2843)) → (v2847 = if v2846 = 1 then v2843 else v2839) → (v2848 = if v2822 = 1 then v2845 else v2837) → (v2849 = if v2822 = 1 then v2847 else v2839) → ((v2850 = 1 ↔ sv v51 < sv v2848)) → ((v2852 = 1 ↔ sv v2744 < sv v51)) → (v2853 = if v2852 = 1 then v2848 else v2849) → ((v2856 = 1 ↔ sv v2853 < sv v2744)) → ((v2857 = 1 ↔ v2850 = 1 ∧ v2856 = 1)) → ((v2864 = 1 ↔ v2670 = 1 ∨ v2857 = 1)) → (sv v2866 = ((H4 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ)) → ((v2867 = 1 ↔ sv v51 < sv v2866)) → ((v2868 = 1 ↔ ¬v2867 = 1)) → (sv t2866.2 = (sc28pS (scArg v2866)).2) → (sv v2870 = sv v18 + sv t2866.2) → ((v2871 = 1 ↔ sv v2870 < sv v95)) → (v2872 = if v2871 = 1 then v95 else v2870) → (sv v2873 = sv v2674 * 2 ^ 28) → (sv v2874 = sv v2872 * sv v2675) → ((v2875 = 1 ↔ sv v2874 < sv v2873)) → ((v2876 = 1 ↔ ¬v2875 = 1)) → ((v2877 = 1 ↔ sv v780 < sv v2866)) → ((v2878 = 1 ↔ ¬v2877 = 1)) → ((v2879 = 1 ↔ v2876 = 1 ∧ v2878 = 1)) → ((v2880 = 1 ↔ v2868 = 1 ∨ v2879 = 1)) → (v2881 = if v2880 = 1 then v2866 else v51) → (v2895 = if v2380 = 1 then v2881 else v51) → ((v2897 = 1 ↔ v2380 = 1 ∧ v2864 = 1)) → (v2898 = if v2670 = 1 then v780 else v51) → (v2900 = if v2897 = 1 then v2898 else v2895) → (sv v2902 = sv v265 + sv v2900) → (sv v2904 = sv v620 + sv v2902) → ((v2906 = 1 ↔ sv v2904 < sv v6)) → ((v2907 = 1 ↔ ¬v2906 = 1)) → ((v2911 = 1 ↔ v13 = 1 ∧ v37 = 1)) → ((v2912 = 1 ↔ v92 = 1 ∧ v2911 = 1)) → ((v2913 = 1 ↔ v13 = 1 ∧ v2912 = 1)) → ((v2914 = 1 ↔ v110 = 1 ∧ v2913 = 1)) → ((v2915 = 1 ↔ v110 = 1 ∧ v2914 = 1)) → ((v2916 = 1 ↔ v270 = 1 ∧ v2915 = 1)) → ((v2917 = 1 ↔ v270 = 1 ∧ v2916 = 1)) → ((v2918 = 1 ↔ v13 = 1 ∧ v2917 = 1)) → ((v2919 = 1 ↔ v423 = 1 ∧ v2918 = 1)) → ((v2920 = 1 ↔ v471 = 1 ∧ v2919 = 1)) → ((v2921 = 1 ↔ v13 = 1 ∧ v2920 = 1)) → ((v2922 = 1 ↔ v474 = 1 ∧ v2921 = 1)) → ((v2923 = 1 ↔ v474 = 1 ∧ v2922 = 1)) → ((v2924 = 1 ↔ v625 = 1 ∧ v2923 = 1)) → ((v2925 = 1 ↔ v625 = 1 ∧ v2924 = 1)) → ((v2926 = 1 ↔ v796 = 1 ∧ v2925 = 1)) → ((v2927 = 1 ↔ v910 = 1 ∧ v2926 = 1)) → ((v2928 = 1 ↔ v910 = 1 ∧ v2927 = 1)) → ((v2929 = 1 ↔ v1083 = 1 ∧ v2928 = 1)) → ((v2930 = 1 ↔ v1083 = 1 ∧ v2929 = 1)) → ((v2931 = 1 ↔ v1273 = 1 ∧ v2930 = 1)) → ((v2932 = 1 ↔ v796 = 1 ∧ v2931 = 1)) → ((v2933 = 1 ↔ v1348 = 1 ∧ v2932 = 1)) → ((v2934 = 1 ↔ v1348 = 1 ∧ v2933 = 1)) → ((v2935 = 1 ↔ v1519 = 1 ∧ v2934 = 1)) → ((v2936 = 1 ↔ v1519 = 1 ∧ v2935 = 1)) → ((v2937 = 1 ↔ v1709 = 1 ∧ v2936 = 1)) → ((v2938 = 1 ↔ v1718 = 1 ∧ v2937 = 1)) → ((v2939 = 1 ↔ v1719 = 1 ∧ v2938 = 1)) → ((v2940 = 1 ↔ v1751 = 1 ∧ v2939 = 1)) → ((v2941 = 1 ↔ v1751 = 1 ∧ v2940 = 1)) → ((v2942 = 1 ↔ v1790 = 1 ∧ v2941 = 1)) → ((v2943 = 1 ↔ v1825 = 1 ∧ v2942 = 1)) → ((v2944 = 1 ↔ v1826 = 1 ∧ v2943 = 1)) → ((v2945 = 1 ↔ v1858 = 1 ∧ v2944 = 1)) → ((v2946 = 1 ↔ v1858 = 1 ∧ v2945 = 1)) → ((v2947 = 1 ↔ v1897 = 1 ∧ v2946 = 1)) → ((v2948 = 1 ↔ v13 = 1 ∧ v2947 = 1)) → ((v2949 = 1 ↔ v1953 = 1 ∧ v2948 = 1)) → ((v2950 = 1 ↔ v2001 = 1 ∧ v2949 = 1)) → ((v2951 = 1 ↔ v13 = 1 ∧ v2950 = 1)) → ((v2952 = 1 ↔ v110 = 1 ∧ v2951 = 1)) → ((v2953 = 1 ↔ v110 = 1 ∧ v2952 = 1)) → ((v2954 = 1 ↔ v2007 = 1 ∧ v2953 = 1)) → ((v2955 = 1 ↔ v2007 = 1 ∧ v2954 = 1)) → ((v2956 = 1 ↔ v13 = 1 ∧ v2955 = 1)) → ((v2957 = 1 ↔ v2165 = 1 ∧ v2956 = 1)) → ((v2958 = 1 ↔ v2213 = 1 ∧ v2957 = 1)) → ((v2959 = 1 ↔ v13 = 1 ∧ v2958 = 1)) → ((v2960 = 1 ↔ v474 = 1 ∧ v2959 = 1)) → ((v2961 = 1 ↔ v474 = 1 ∧ v2960 = 1)) → ((v2962 = 1 ↔ v2219 = 1 ∧ v2961 = 1)) → ((v2963 = 1 ↔ v2219 = 1 ∧ v2962 = 1)) → ((v2964 = 1 ↔ v2382 = 1 ∧ v2963 = 1)) → ((v2965 = 1 ↔ v2490 = 1 ∧ v2964 = 1)) → ((v2966 = 1 ↔ v2678 = 1 ∧ v2965 = 1)) → ((v2967 = 1 ↔ v2907 = 1 ∧ v2966 = 1)) → P) → P := by
  intro OFFr v6 v18 v23 v51 v95 v105 v780 v965 v992 v2684 v2685 v2686 v2687 v2688 v2689 v2690 v2691 v2692 v2693 v2694 v2695 v2696 v2697 v2698 v2699 v2700 v2701 v2702 v2703 v2704 v2706 v2707 v2708 v2709 v2710 v2712 v2713 v2714 v2715 v2716 v2724 v2725 v2726 v2727 v2728 v2729 v2732 v2733 v2736 v2737 v2740 v2741 v2743 v2744 v2746 v2747 v2748 v2749 v2750 v2751 v2752 v2753 v2754 v2755 v2756 v2757 v2758 v2759 v2760 v2761 v2762 v2763 v2764 v2765 v2766 v2767 v2768 v2769 v2770 v2771 v2772 v2773 v2774 v2775 v2776 v2777 v2778 v2779 v2780 v2781 v2782 v2783 v2784 v2785 v2786 v2787 v2788 v2789 v2790 v2791 v2792 v2793 v2794 v2795 v2796 v2797 v2798 v2799 v2800 v2801 v2802 v2803 v2804 v2805 v2806 v2807 v2808 v2809 v2810 v2811 v2812 v2813 v2814 v2815 v2816 v2818 v2819 v2820 v2821 v2822 v2823 v2824 v2825 v2826 v2827 v2828 v2829 v2830 v2831 v2832 v2833 v2834 v2835 v2836 v2837 v2838 v2839 v2840 v2841 v2842 v2843 v2844 v2845 v2846 v2847 v2848 v2849 v2850 v2852 v2853 v2856 v2857 v2864 v2866 v2867 v2868 t2866 v2870 v2871 v2872 v2873 v2874 v2875 v2876 v2877 v2878 v2879 v2880 v2881 v2895 v2897 v2898 v2900 v2902 v2904 v2906 v2907 v2911 v2912 v2913 v2914 v2915 v2916 v2917 v2918 v2919 v2920 v2921 v2922 v2923 v2924 v2925 v2926 v2927 v2928 v2929 v2930 v2931 v2932 v2933 v2934 v2935 v2936 v2937 v2938 v2939 v2940 v2941 v2942 v2943 v2944 v2945 v2946 v2947 v2948 v2949 v2950 v2951 v2952 v2953 v2954 v2955 v2956 v2957 v2958 v2959 v2960 v2961 v2962 v2963 v2964 v2965 v2966 v2967
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v6 : R 1 0 4611686018427387904 4611686087146864624 v6 v6 := (r1_ix hb_F3 0 (of_decide_eq_true rfl))
  have h_v18 : R 1 0 4611686018427387900 4611686018427387900 v18 v18 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have h_v23 : R 1 0 4611686018695823360 4611686018695823360 v23 v23 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have h_v51 : R 1 0 4611686018427387904 4611686018427387904 v51 v51 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v95 : R 1 0 4611686018158952448 4611686018158952448 v95 v95 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have h_v105 : R 1 0 4611686018427387905 4611686018427387905 v105 v105 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have h_v780 : R 1 0 4611686019270702760 4611686019270702760 v780 v780 := (r_c hl 4611686019270702760 (of_decide_eq_true rfl))
  have h_v965 : R 1 0 4683743612465315840 4683743612465315840 v965 v965 := (r_c hl 4683743612465315840 (of_decide_eq_true rfl))
  have h_v992 : R 1 0 4647714815446351872 4647714815446351872 v992 v992 := (r_c hl 4647714815446351872 (of_decide_eq_true rfl))
  have h_v2684 : R 1 0 4611686018427387904 4683743620518379745 v2684 v2684 := (r_smx_sq hl 29 h_v2482 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2684 : sv v2684 = sv v2482 * sv v2482 := e_smx_sq 29 h_v2482 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2685 : R 1 0 4611686018427387904 4611686018695823391 v2685 v2685 := (r_srdC hl h_v2684 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v2685 : sv v2685 = -((-sv v2684) / 2 ^ 28) := e_srdC h_v2684 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v2686 : R 1 0 4611686018427387904 4611686018964258878 v2686 v2686 := (r_sub hl (r_add hl h_v2685 h_v2685 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2686 : sv v2686 = sv v2685 + sv v2685 := e_add h_v2685 h_v2685 (of_decide_eq_true rfl)
  have h_v2687 : R 1 0 4611686018158952386 4611686018695823360 v2687 v2687 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v2686 (of_decide_eq_true rfl))
  have e_v2687 : sv v2687 = sv v23 - sv v2686 := e_sub h_v23 h_v2686 (of_decide_eq_true rfl)
  have h_v2688 : R 1 0 0 1 v2688 v2688 := (r_plt hl h_v2687 h_v95 (of_decide_eq_true rfl))
  have e_v2688 : (v2688 = 1 ↔ sv v2687 < sv v95) := e_plt h_v2687 h_v95 (of_decide_eq_true rfl)
  have h_v2689 : R 1 0 4611686018158952386 4611686018695823360 v2689 v2689 := (r_psel hl h_v2688 h_v95 h_v2687 (of_decide_eq_true rfl))
  have e_v2689 : v2689 = if v2688 = 1 then v95 else v2687 := e_psel h_v2688 h_v95 h_v2687 (of_decide_eq_true rfl)
  have h_v2690 : R 1 0 4611686018427387904 4683743620518379745 v2690 v2690 := (r_smx_sq hl 29 h_v2481 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2690 : sv v2690 = sv v2481 * sv v2481 := e_smx_sq 29 h_v2481 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2691 : R 1 0 4611686018427387904 4611686018695823390 v2691 v2691 := (r_srdF hl h_v2690 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  clear h_v2685 h_v2686 h_v2687 h_v2688
  have e_v2691 : sv v2691 = sv v2690 / 2 ^ 28 := e_srdF h_v2690 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v2692 : R 1 0 4611686018427387904 4611686018964258876 v2692 v2692 := (r_sub hl (r_add hl h_v2691 h_v2691 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2692 : sv v2692 = sv v2691 + sv v2691 := e_add h_v2691 h_v2691 (of_decide_eq_true rfl)
  have h_v2693 : R 1 0 4611686018158952388 4611686018695823360 v2693 v2693 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v2692 (of_decide_eq_true rfl))
  have e_v2693 : sv v2693 = sv v23 - sv v2692 := e_sub h_v23 h_v2692 (of_decide_eq_true rfl)
  have h_v2694 : R 1 0 4611686018427387904 4683743620518379745 v2694 v2694 := (r_smx_sq hl 29 h_v2486 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2694 : sv v2694 = sv v2486 * sv v2486 := e_smx_sq 29 h_v2486 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2695 : R 1 0 4611686018427387904 4611686018695823391 v2695 v2695 := (r_srdC hl h_v2694 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v2695 : sv v2695 = -((-sv v2694) / 2 ^ 28) := e_srdC h_v2694 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v2696 : R 1 0 4611686018427387904 4611686018964258878 v2696 v2696 := (r_sub hl (r_add hl h_v2695 h_v2695 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2696 : sv v2696 = sv v2695 + sv v2695 := e_add h_v2695 h_v2695 (of_decide_eq_true rfl)
  have h_v2697 : R 1 0 4611686018158952386 4611686018695823360 v2697 v2697 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v2696 (of_decide_eq_true rfl))
  have e_v2697 : sv v2697 = sv v23 - sv v2696 := e_sub h_v23 h_v2696 (of_decide_eq_true rfl)
  have h_v2698 : R 1 0 0 1 v2698 v2698 := (r_plt hl h_v2697 h_v95 (of_decide_eq_true rfl))
  have e_v2698 : (v2698 = 1 ↔ sv v2697 < sv v95) := e_plt h_v2697 h_v95 (of_decide_eq_true rfl)
  have h_v2699 : R 1 0 4611686018158952386 4611686018695823360 v2699 v2699 := (r_psel hl h_v2698 h_v95 h_v2697 (of_decide_eq_true rfl))
  have e_v2699 : v2699 = if v2698 = 1 then v95 else v2697 := e_psel h_v2698 h_v95 h_v2697 (of_decide_eq_true rfl)
  have h_v2700 : R 1 0 4611686018427387904 4683743620518379745 v2700 v2700 := (r_smx_sq hl 29 h_v2485 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2700 : sv v2700 = sv v2485 * sv v2485 := e_smx_sq 29 h_v2485 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2701 : R 1 0 4611686018427387904 4611686018695823390 v2701 v2701 := (r_srdF hl h_v2700 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v2701 : sv v2701 = sv v2700 / 2 ^ 28 := e_srdF h_v2700 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v2702 : R 1 0 4611686018427387904 4611686018964258876 v2702 v2702 := (r_sub hl (r_add hl h_v2701 h_v2701 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2702 : sv v2702 = sv v2701 + sv v2701 := e_add h_v2701 h_v2701 (of_decide_eq_true rfl)
  have h_v2703 : R 1 0 4611686018158952388 4611686018695823360 v2703 v2703 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v2702 (of_decide_eq_true rfl))
  have e_v2703 : sv v2703 = sv v23 - sv v2702 := e_sub h_v23 h_v2702 (of_decide_eq_true rfl)
  clear h_v2691 h_v2692 h_v2695 h_v2696 h_v2697 h_v2698 h_v2701 h_v2702
  have h_v2704 : R 1 0 0 1 v2704 v2704 := (r_plt hl h_v2689 h_v51 (of_decide_eq_true rfl))
  have e_v2704 : (v2704 = 1 ↔ sv v2689 < sv v51) := e_plt h_v2689 h_v51 (of_decide_eq_true rfl)
  have h_v2706 : R 1 0 0 1 v2706 v2706 := (r_plt hl h_v51 h_v2693 (of_decide_eq_true rfl))
  have e_v2706 : (v2706 = 1 ↔ sv v51 < sv v2693) := e_plt h_v51 h_v2693 (of_decide_eq_true rfl)
  have h_v2707 : R 1 0 0 1 v2707 v2707 := (r_sub hl (r_O hl) h_v2706 (of_decide_eq_true rfl))
  have e_v2707 : (v2707 = 1 ↔ ¬v2706 = 1) := e_not h_v2706 (of_decide_eq_true rfl)
  have h_v2708 : R 1 0 0 1 v2708 v2708 := (r_land hl h_v2704 h_v2707 (of_decide_eq_true rfl))
  have e_v2708 : (v2708 = 1 ↔ v2704 = 1 ∧ v2707 = 1) := e_land h_v2704 h_v2707 (of_decide_eq_true rfl)
  have h_v2709 : R 1 0 0 1 v2709 v2709 := (r_land hl h_v2704 h_v2706 (of_decide_eq_true rfl))
  have e_v2709 : (v2709 = 1 ↔ v2704 = 1 ∧ v2706 = 1) := e_land h_v2704 h_v2706 (of_decide_eq_true rfl)
  have h_v2710 : R 1 0 0 1 v2710 v2710 := (r_plt hl h_v2699 h_v51 (of_decide_eq_true rfl))
  have e_v2710 : (v2710 = 1 ↔ sv v2699 < sv v51) := e_plt h_v2699 h_v51 (of_decide_eq_true rfl)
  have h_v2712 : R 1 0 0 1 v2712 v2712 := (r_plt hl h_v51 h_v2703 (of_decide_eq_true rfl))
  have e_v2712 : (v2712 = 1 ↔ sv v51 < sv v2703) := e_plt h_v51 h_v2703 (of_decide_eq_true rfl)
  have h_v2713 : R 1 0 0 1 v2713 v2713 := (r_sub hl (r_O hl) h_v2712 (of_decide_eq_true rfl))
  have e_v2713 : (v2713 = 1 ↔ ¬v2712 = 1) := e_not h_v2712 (of_decide_eq_true rfl)
  have h_v2714 : R 1 0 0 1 v2714 v2714 := (r_land hl h_v2710 h_v2713 (of_decide_eq_true rfl))
  have e_v2714 : (v2714 = 1 ↔ v2710 = 1 ∧ v2713 = 1) := e_land h_v2710 h_v2713 (of_decide_eq_true rfl)
  have h_v2715 : R 1 0 0 1 v2715 v2715 := (r_land hl h_v2710 h_v2712 (of_decide_eq_true rfl))
  have e_v2715 : (v2715 = 1 ↔ v2710 = 1 ∧ v2712 = 1) := e_land h_v2710 h_v2712 (of_decide_eq_true rfl)
  have h_v2716 : R 1 0 0 1 v2716 v2716 := (r_land hl h_v2709 h_v2715 (of_decide_eq_true rfl))
  have e_v2716 : (v2716 = 1 ↔ v2709 = 1 ∧ v2715 = 1) := e_land h_v2709 h_v2715 (of_decide_eq_true rfl)
  have h_v2724 : R 1 0 0 1 v2724 v2724 := (r_land hl h_v2708 h_v2715 (of_decide_eq_true rfl))
  have e_v2724 : (v2724 = 1 ↔ v2708 = 1 ∧ v2715 = 1) := e_land h_v2708 h_v2715 (of_decide_eq_true rfl)
  have h_v2725 : R 1 0 0 1 v2725 v2725 := (r_lor hl h_v2714 h_v2724 (of_decide_eq_true rfl))
  clear h_v2704 h_v2706 h_v2707 h_v2710 h_v2712 h_v2713 h_v2715
  have e_v2725 : (v2725 = 1 ↔ v2714 = 1 ∨ v2724 = 1) := e_lor h_v2714 h_v2724 (of_decide_eq_true rfl)
  have h_v2726 : R 1 0 4611686018158952386 4611686018695823360 v2726 v2726 := (r_psel hl h_v2725 h_v2689 h_v2693 (of_decide_eq_true rfl))
  have e_v2726 : v2726 = if v2725 = 1 then v2689 else v2693 := e_psel h_v2725 h_v2689 h_v2693 (of_decide_eq_true rfl)
  have h_v2727 : R 1 0 0 1 v2727 v2727 := (r_land hl h_v2709 h_v2714 (of_decide_eq_true rfl))
  have e_v2727 : (v2727 = 1 ↔ v2709 = 1 ∧ v2714 = 1) := e_land h_v2709 h_v2714 (of_decide_eq_true rfl)
  have h_v2728 : R 1 0 0 1 v2728 v2728 := (r_lor hl h_v2708 h_v2727 (of_decide_eq_true rfl))
  have e_v2728 : (v2728 = 1 ↔ v2708 = 1 ∨ v2727 = 1) := e_lor h_v2708 h_v2727 (of_decide_eq_true rfl)
  have h_v2729 : R 1 0 4611686018158952386 4611686018695823360 v2729 v2729 := (r_psel hl h_v2728 h_v2699 h_v2703 (of_decide_eq_true rfl))
  have e_v2729 : v2729 = if v2728 = 1 then v2699 else v2703 := e_psel h_v2728 h_v2699 h_v2703 (of_decide_eq_true rfl)
  have h_v2732 : R 1 0 4539628407746461696 4683743645751316228 v2732 v2732 := (r_smx hl 30 h_v2729 h_v2726 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v2732 : sv v2732 = sv v2729 * sv v2726 := e_smx 30 h_v2729 h_v2726 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v2733 : R 1 0 4611686018158952386 4611686018695823485 v2733 v2733 := (r_srdC hl h_v2732 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v2733 : sv v2733 = -((-sv v2732) / 2 ^ 28) := e_srdC h_v2732 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v2736 : R 1 0 4539628407746461696 4683743645751316228 v2736 v2736 := (r_smx hl 30 h_v2699 h_v2689 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v2736 : sv v2736 = sv v2699 * sv v2689 := e_smx 30 h_v2699 h_v2689 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v2737 : R 1 0 4611686018158952386 4611686018695823485 v2737 v2737 := (r_srdC hl h_v2736 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v2737 : sv v2737 = -((-sv v2736) / 2 ^ 28) := e_srdC h_v2736 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v2740 : R 1 0 0 1 v2740 v2740 := (r_plt hl h_v2733 h_v2737 (of_decide_eq_true rfl))
  have e_v2740 : (v2740 = 1 ↔ sv v2733 < sv v2737) := e_plt h_v2733 h_v2737 (of_decide_eq_true rfl)
  have h_v2741 : R 1 0 4611686018158952386 4611686018695823485 v2741 v2741 := (r_psel hl h_v2740 h_v2737 h_v2733 (of_decide_eq_true rfl))
  have e_v2741 : v2741 = if v2740 = 1 then v2737 else v2733 := e_psel h_v2740 h_v2737 h_v2733 (of_decide_eq_true rfl)
  have h_v2743 : R 1 0 4611686018158952386 4611686018695823485 v2743 v2743 := (r_psel hl h_v2716 h_v2741 h_v2733 (of_decide_eq_true rfl))
  have e_v2743 : v2743 = if v2716 = 1 then v2741 else v2733 := e_psel h_v2716 h_v2741 h_v2733 (of_decide_eq_true rfl)
  have h_v2744 : R 1 0 4611686017890516860 4611686018964258877 v2744 v2744 := (r_sub hl (r_add hl h_v100 h_OFFr (of_decide_eq_true rfl)) h_v2743 (of_decide_eq_true rfl))
  have e_v2744 : sv v2744 = sv v100 - sv v2743 := e_sub h_v100 h_v2743 (of_decide_eq_true rfl)
  clear h_v2689 h_v2693 h_v2699 h_v2703 h_v2708 h_v2709 h_v2714 h_v2716 h_v2724 h_v2725 h_v2726 h_v2727 h_v2728 h_v2729 h_v2732 h_v2733 h_v2736 h_v2737 h_v2740 h_v2741 h_v2743
  have h_v2746 : R 1 0 4611686010374323999 4683743612465315840 v2746 v2746 := (r_sub hl (r_add hl h_v965 h_OFFr (of_decide_eq_true rfl)) h_v2690 (of_decide_eq_true rfl))
  have e_v2746 : sv v2746 = sv v965 - sv v2690 := e_sub h_v965 h_v2690 (of_decide_eq_true rfl)
  have h_v2747 : R 1 0 4611686018427387904 4611686018695823360 v2747 v2747 := (r_psqrt hl h_v2746 (of_decide_eq_true rfl))
  have e_v2747 : sv v2747 = ((Nat.sqrt (v2746 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2746 (of_decide_eq_true rfl)
  have h_v2748 : R 1 0 4611686018427387905 4611686018695823361 v2748 v2748 := (r_sub hl (r_add hl h_v105 h_v2747 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2748 : sv v2748 = sv v105 + sv v2747 := e_add h_v105 h_v2747 (of_decide_eq_true rfl)
  have pb_v2747_v2481 : PB 1 v2747 v2481 36028797018963968 := pb_sqrt hl h_v2481 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v2749 : R 1 0 4611686017085210624 4647714815446351872 v2749 v2749 := (r_smx_pb hl 29 h_v2747 h_v2481 pb_v2747_v2481 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2749 : sv v2749 = sv v2747 * sv v2481 := e_smx_pb 29 h_v2747 h_v2481 pb_v2747_v2481 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2750 : R 1 0 4611686018427387899 4611686018561605632 v2750 v2750 := (r_srdF hl h_v2749 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2750 : sv v2750 = sv v2749 / 2 ^ 28 := e_srdF h_v2749 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2751 : R 1 0 4611686018427387894 4611686018695823360 v2751 v2751 := (r_sub hl (r_add hl h_v2750 h_v2750 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2751 : sv v2751 = sv v2750 + sv v2750 := e_add h_v2750 h_v2750 (of_decide_eq_true rfl)
  have pb_v2748_v2481 : PB 1 v2748 v2481 36028797287399439 := pb_sqrt1 hl h_v2481 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2752 : R 1 0 4611686017085210619 4647714815714787343 v2752 v2752 := (r_smx_pb hl 29 h_v2748 h_v2481 pb_v2748_v2481 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2752 : sv v2752 = sv v2748 * sv v2481 := e_smx_pb 29 h_v2748 h_v2481 pb_v2748_v2481 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2753 : R 1 0 4611686018427387899 4611686018561605634 v2753 v2753 := (r_srdC hl h_v2752 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2753 : sv v2753 = -((-sv v2752) / 2 ^ 28) := e_srdC h_v2752 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2754 : R 1 0 4611686018427387894 4611686018695823364 v2754 v2754 := (r_sub hl (r_add hl h_v2753 h_v2753 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2754 : sv v2754 = sv v2753 + sv v2753 := e_add h_v2753 h_v2753 (of_decide_eq_true rfl)
  have h_v2755 : R 1 0 0 1 v2755 v2755 := (r_plt hl h_v2754 h_v23 (of_decide_eq_true rfl))
  have e_v2755 : (v2755 = 1 ↔ sv v2754 < sv v23) := e_plt h_v2754 h_v23 (of_decide_eq_true rfl)
  have h_v2756 : R 1 0 4611686018427387894 4611686018695823364 v2756 v2756 := (r_psel hl h_v2755 h_v2754 h_v23 (of_decide_eq_true rfl))
  have e_v2756 : v2756 = if v2755 = 1 then v2754 else v23 := e_psel h_v2755 h_v2754 h_v23 (of_decide_eq_true rfl)
  have h_v2757 : R 1 0 4611686010374323999 4683743612465315840 v2757 v2757 := (r_sub hl (r_add hl h_v965 h_OFFr (of_decide_eq_true rfl)) h_v2684 (of_decide_eq_true rfl))
  clear h_v2746 h_v2747 h_v2748 pb_v2747_v2481 h_v2749 h_v2750 pb_v2748_v2481 h_v2752 h_v2753 h_v2754 h_v2755
  have e_v2757 : sv v2757 = sv v965 - sv v2684 := e_sub h_v965 h_v2684 (of_decide_eq_true rfl)
  have h_v2758 : R 1 0 4611686018427387904 4611686018695823360 v2758 v2758 := (r_psqrt hl h_v2757 (of_decide_eq_true rfl))
  have e_v2758 : sv v2758 = ((Nat.sqrt (v2757 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2757 (of_decide_eq_true rfl)
  have h_v2759 : R 1 0 4611686018427387905 4611686018695823361 v2759 v2759 := (r_sub hl (r_add hl h_v105 h_v2758 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2759 : sv v2759 = sv v105 + sv v2758 := e_add h_v105 h_v2758 (of_decide_eq_true rfl)
  have pb_v2758_v2482 : PB 1 v2758 v2482 36028797018963968 := pb_sqrt hl h_v2482 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v2760 : R 1 0 4611686017085210624 4647714815446351872 v2760 v2760 := (r_smx_pb hl 29 h_v2758 h_v2482 pb_v2758_v2482 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2760 : sv v2760 = sv v2758 * sv v2482 := e_smx_pb 29 h_v2758 h_v2482 pb_v2758_v2482 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2761 : R 1 0 4611686018427387899 4611686018561605632 v2761 v2761 := (r_srdF hl h_v2760 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2761 : sv v2761 = sv v2760 / 2 ^ 28 := e_srdF h_v2760 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2762 : R 1 0 4611686018427387894 4611686018695823360 v2762 v2762 := (r_sub hl (r_add hl h_v2761 h_v2761 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2762 : sv v2762 = sv v2761 + sv v2761 := e_add h_v2761 h_v2761 (of_decide_eq_true rfl)
  have pb_v2759_v2482 : PB 1 v2759 v2482 36028797287399439 := pb_sqrt1 hl h_v2482 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2763 : R 1 0 4611686017085210619 4647714815714787343 v2763 v2763 := (r_smx_pb hl 29 h_v2759 h_v2482 pb_v2759_v2482 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2763 : sv v2763 = sv v2759 * sv v2482 := e_smx_pb 29 h_v2759 h_v2482 pb_v2759_v2482 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2764 : R 1 0 4611686018427387899 4611686018561605634 v2764 v2764 := (r_srdC hl h_v2763 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2764 : sv v2764 = -((-sv v2763) / 2 ^ 28) := e_srdC h_v2763 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2765 : R 1 0 4611686018427387894 4611686018695823364 v2765 v2765 := (r_sub hl (r_add hl h_v2764 h_v2764 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2765 : sv v2765 = sv v2764 + sv v2764 := e_add h_v2764 h_v2764 (of_decide_eq_true rfl)
  have h_v2766 : R 1 0 0 1 v2766 v2766 := (r_plt hl h_v2765 h_v23 (of_decide_eq_true rfl))
  have e_v2766 : (v2766 = 1 ↔ sv v2765 < sv v23) := e_plt h_v2765 h_v23 (of_decide_eq_true rfl)
  have h_v2767 : R 1 0 4611686018427387894 4611686018695823364 v2767 v2767 := (r_psel hl h_v2766 h_v2765 h_v23 (of_decide_eq_true rfl))
  have e_v2767 : v2767 = if v2766 = 1 then v2765 else v23 := e_psel h_v2766 h_v2765 h_v23 (of_decide_eq_true rfl)
  have h_v2768 : R 1 0 0 1 v2768 v2768 := (r_plt hl h_v2751 h_v2762 (of_decide_eq_true rfl))
  have e_v2768 : (v2768 = 1 ↔ sv v2751 < sv v2762) := e_plt h_v2751 h_v2762 (of_decide_eq_true rfl)
  clear h_v2757 h_v2758 h_v2759 pb_v2758_v2482 h_v2760 h_v2761 pb_v2759_v2482 h_v2763 h_v2764 h_v2765 h_v2766
  have h_v2769 : R 1 0 4611686018427387894 4611686018695823360 v2769 v2769 := (r_psel hl h_v2768 h_v2751 h_v2762 (of_decide_eq_true rfl))
  have e_v2769 : v2769 = if v2768 = 1 then v2751 else v2762 := e_psel h_v2768 h_v2751 h_v2762 (of_decide_eq_true rfl)
  have h_v2770 : R 1 0 0 1 v2770 v2770 := (r_plt hl h_v2756 h_v2767 (of_decide_eq_true rfl))
  have e_v2770 : (v2770 = 1 ↔ sv v2756 < sv v2767) := e_plt h_v2756 h_v2767 (of_decide_eq_true rfl)
  have h_v2771 : R 1 0 4611686018427387894 4611686018695823364 v2771 v2771 := (r_psel hl h_v2770 h_v2767 h_v2756 (of_decide_eq_true rfl))
  have e_v2771 : v2771 = if v2770 = 1 then v2767 else v2756 := e_psel h_v2770 h_v2767 h_v2756 (of_decide_eq_true rfl)
  have h_v2772 : R 1 0 0 1 v2772 v2772 := (r_plt hl h_v992 h_v2690 (of_decide_eq_true rfl))
  have e_v2772 : (v2772 = 1 ↔ sv v992 < sv v2690) := e_plt h_v992 h_v2690 (of_decide_eq_true rfl)
  have h_v2773 : R 1 0 0 1 v2773 v2773 := (r_sub hl (r_O hl) h_v2772 (of_decide_eq_true rfl))
  have e_v2773 : (v2773 = 1 ↔ ¬v2772 = 1) := e_not h_v2772 (of_decide_eq_true rfl)
  have h_v2774 : R 1 0 0 1 v2774 v2774 := (r_plt hl h_v2684 h_v992 (of_decide_eq_true rfl))
  have e_v2774 : (v2774 = 1 ↔ sv v2684 < sv v992) := e_plt h_v2684 h_v992 (of_decide_eq_true rfl)
  have h_v2775 : R 1 0 0 1 v2775 v2775 := (r_sub hl (r_O hl) h_v2774 (of_decide_eq_true rfl))
  have e_v2775 : (v2775 = 1 ↔ ¬v2774 = 1) := e_not h_v2774 (of_decide_eq_true rfl)
  have h_v2776 : R 1 0 0 1 v2776 v2776 := (r_land hl h_v2773 h_v2775 (of_decide_eq_true rfl))
  have e_v2776 : (v2776 = 1 ↔ v2773 = 1 ∧ v2775 = 1) := e_land h_v2773 h_v2775 (of_decide_eq_true rfl)
  have h_v2777 : R 1 0 4611686018427387894 4611686018695823364 v2777 v2777 := (r_psel hl h_v2776 h_v23 h_v2771 (of_decide_eq_true rfl))
  have e_v2777 : v2777 = if v2776 = 1 then v23 else v2771 := e_psel h_v2776 h_v23 h_v2771 (of_decide_eq_true rfl)
  have h_v2778 : R 1 0 4611686010374323999 4683743612465315840 v2778 v2778 := (r_sub hl (r_add hl h_v965 h_OFFr (of_decide_eq_true rfl)) h_v2700 (of_decide_eq_true rfl))
  have e_v2778 : sv v2778 = sv v965 - sv v2700 := e_sub h_v965 h_v2700 (of_decide_eq_true rfl)
  have h_v2779 : R 1 0 4611686018427387904 4611686018695823360 v2779 v2779 := (r_psqrt hl h_v2778 (of_decide_eq_true rfl))
  have e_v2779 : sv v2779 = ((Nat.sqrt (v2778 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2778 (of_decide_eq_true rfl)
  have h_v2780 : R 1 0 4611686018427387905 4611686018695823361 v2780 v2780 := (r_sub hl (r_add hl h_v105 h_v2779 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2780 : sv v2780 = sv v105 + sv v2779 := e_add h_v105 h_v2779 (of_decide_eq_true rfl)
  have pb_v2779_v2485 : PB 1 v2779 v2485 36028797018963968 := pb_sqrt hl h_v2485 29 36028797018963968 (of_decide_eq_true rfl)
  clear h_v2684 h_v2690 h_v2751 h_v2756 h_v2762 h_v2767 h_v2768 h_v2770 h_v2771 h_v2772 h_v2773 h_v2774 h_v2775 h_v2776 h_v2778
  have h_v2781 : R 1 0 4611686017085210624 4647714815446351872 v2781 v2781 := (r_smx_pb hl 29 h_v2779 h_v2485 pb_v2779_v2485 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2781 : sv v2781 = sv v2779 * sv v2485 := e_smx_pb 29 h_v2779 h_v2485 pb_v2779_v2485 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2782 : R 1 0 4611686018427387899 4611686018561605632 v2782 v2782 := (r_srdF hl h_v2781 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2782 : sv v2782 = sv v2781 / 2 ^ 28 := e_srdF h_v2781 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2783 : R 1 0 4611686018427387894 4611686018695823360 v2783 v2783 := (r_sub hl (r_add hl h_v2782 h_v2782 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2783 : sv v2783 = sv v2782 + sv v2782 := e_add h_v2782 h_v2782 (of_decide_eq_true rfl)
  have pb_v2780_v2485 : PB 1 v2780 v2485 36028797287399439 := pb_sqrt1 hl h_v2485 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2784 : R 1 0 4611686017085210619 4647714815714787343 v2784 v2784 := (r_smx_pb hl 29 h_v2780 h_v2485 pb_v2780_v2485 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2784 : sv v2784 = sv v2780 * sv v2485 := e_smx_pb 29 h_v2780 h_v2485 pb_v2780_v2485 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2785 : R 1 0 4611686018427387899 4611686018561605634 v2785 v2785 := (r_srdC hl h_v2784 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2785 : sv v2785 = -((-sv v2784) / 2 ^ 28) := e_srdC h_v2784 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2786 : R 1 0 4611686018427387894 4611686018695823364 v2786 v2786 := (r_sub hl (r_add hl h_v2785 h_v2785 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2786 : sv v2786 = sv v2785 + sv v2785 := e_add h_v2785 h_v2785 (of_decide_eq_true rfl)
  have h_v2787 : R 1 0 0 1 v2787 v2787 := (r_plt hl h_v2786 h_v23 (of_decide_eq_true rfl))
  have e_v2787 : (v2787 = 1 ↔ sv v2786 < sv v23) := e_plt h_v2786 h_v23 (of_decide_eq_true rfl)
  have h_v2788 : R 1 0 4611686018427387894 4611686018695823364 v2788 v2788 := (r_psel hl h_v2787 h_v2786 h_v23 (of_decide_eq_true rfl))
  have e_v2788 : v2788 = if v2787 = 1 then v2786 else v23 := e_psel h_v2787 h_v2786 h_v23 (of_decide_eq_true rfl)
  have h_v2789 : R 1 0 4611686010374323999 4683743612465315840 v2789 v2789 := (r_sub hl (r_add hl h_v965 h_OFFr (of_decide_eq_true rfl)) h_v2694 (of_decide_eq_true rfl))
  have e_v2789 : sv v2789 = sv v965 - sv v2694 := e_sub h_v965 h_v2694 (of_decide_eq_true rfl)
  have h_v2790 : R 1 0 4611686018427387904 4611686018695823360 v2790 v2790 := (r_psqrt hl h_v2789 (of_decide_eq_true rfl))
  have e_v2790 : sv v2790 = ((Nat.sqrt (v2789 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2789 (of_decide_eq_true rfl)
  have h_v2791 : R 1 0 4611686018427387905 4611686018695823361 v2791 v2791 := (r_sub hl (r_add hl h_v105 h_v2790 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2791 : sv v2791 = sv v105 + sv v2790 := e_add h_v105 h_v2790 (of_decide_eq_true rfl)
  have pb_v2790_v2486 : PB 1 v2790 v2486 36028797018963968 := pb_sqrt hl h_v2486 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v2792 : R 1 0 4611686017085210624 4647714815446351872 v2792 v2792 := (r_smx_pb hl 29 h_v2790 h_v2486 pb_v2790_v2486 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  clear h_v105 h_v965 h_v2779 h_v2780 pb_v2779_v2485 h_v2781 h_v2782 pb_v2780_v2485 h_v2784 h_v2785 h_v2786 h_v2787 h_v2789
  have e_v2792 : sv v2792 = sv v2790 * sv v2486 := e_smx_pb 29 h_v2790 h_v2486 pb_v2790_v2486 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2793 : R 1 0 4611686018427387899 4611686018561605632 v2793 v2793 := (r_srdF hl h_v2792 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2793 : sv v2793 = sv v2792 / 2 ^ 28 := e_srdF h_v2792 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2794 : R 1 0 4611686018427387894 4611686018695823360 v2794 v2794 := (r_sub hl (r_add hl h_v2793 h_v2793 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2794 : sv v2794 = sv v2793 + sv v2793 := e_add h_v2793 h_v2793 (of_decide_eq_true rfl)
  have pb_v2791_v2486 : PB 1 v2791 v2486 36028797287399439 := pb_sqrt1 hl h_v2486 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2795 : R 1 0 4611686017085210619 4647714815714787343 v2795 v2795 := (r_smx_pb hl 29 h_v2791 h_v2486 pb_v2791_v2486 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2795 : sv v2795 = sv v2791 * sv v2486 := e_smx_pb 29 h_v2791 h_v2486 pb_v2791_v2486 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2796 : R 1 0 4611686018427387899 4611686018561605634 v2796 v2796 := (r_srdC hl h_v2795 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2796 : sv v2796 = -((-sv v2795) / 2 ^ 28) := e_srdC h_v2795 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2797 : R 1 0 4611686018427387894 4611686018695823364 v2797 v2797 := (r_sub hl (r_add hl h_v2796 h_v2796 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2797 : sv v2797 = sv v2796 + sv v2796 := e_add h_v2796 h_v2796 (of_decide_eq_true rfl)
  have h_v2798 : R 1 0 0 1 v2798 v2798 := (r_plt hl h_v2797 h_v23 (of_decide_eq_true rfl))
  have e_v2798 : (v2798 = 1 ↔ sv v2797 < sv v23) := e_plt h_v2797 h_v23 (of_decide_eq_true rfl)
  have h_v2799 : R 1 0 4611686018427387894 4611686018695823364 v2799 v2799 := (r_psel hl h_v2798 h_v2797 h_v23 (of_decide_eq_true rfl))
  have e_v2799 : v2799 = if v2798 = 1 then v2797 else v23 := e_psel h_v2798 h_v2797 h_v23 (of_decide_eq_true rfl)
  have h_v2800 : R 1 0 0 1 v2800 v2800 := (r_plt hl h_v2783 h_v2794 (of_decide_eq_true rfl))
  have e_v2800 : (v2800 = 1 ↔ sv v2783 < sv v2794) := e_plt h_v2783 h_v2794 (of_decide_eq_true rfl)
  have h_v2801 : R 1 0 4611686018427387894 4611686018695823360 v2801 v2801 := (r_psel hl h_v2800 h_v2783 h_v2794 (of_decide_eq_true rfl))
  have e_v2801 : v2801 = if v2800 = 1 then v2783 else v2794 := e_psel h_v2800 h_v2783 h_v2794 (of_decide_eq_true rfl)
  have h_v2802 : R 1 0 0 1 v2802 v2802 := (r_plt hl h_v2788 h_v2799 (of_decide_eq_true rfl))
  have e_v2802 : (v2802 = 1 ↔ sv v2788 < sv v2799) := e_plt h_v2788 h_v2799 (of_decide_eq_true rfl)
  have h_v2803 : R 1 0 4611686018427387894 4611686018695823364 v2803 v2803 := (r_psel hl h_v2802 h_v2799 h_v2788 (of_decide_eq_true rfl))
  have e_v2803 : v2803 = if v2802 = 1 then v2799 else v2788 := e_psel h_v2802 h_v2799 h_v2788 (of_decide_eq_true rfl)
  have h_v2804 : R 1 0 0 1 v2804 v2804 := (r_plt hl h_v992 h_v2700 (of_decide_eq_true rfl))
  clear h_v2783 h_v2788 h_v2790 h_v2791 pb_v2790_v2486 h_v2792 h_v2793 h_v2794 pb_v2791_v2486 h_v2795 h_v2796 h_v2797 h_v2798 h_v2799 h_v2800 h_v2802
  have e_v2804 : (v2804 = 1 ↔ sv v992 < sv v2700) := e_plt h_v992 h_v2700 (of_decide_eq_true rfl)
  have h_v2805 : R 1 0 0 1 v2805 v2805 := (r_sub hl (r_O hl) h_v2804 (of_decide_eq_true rfl))
  have e_v2805 : (v2805 = 1 ↔ ¬v2804 = 1) := e_not h_v2804 (of_decide_eq_true rfl)
  have h_v2806 : R 1 0 0 1 v2806 v2806 := (r_plt hl h_v2694 h_v992 (of_decide_eq_true rfl))
  have e_v2806 : (v2806 = 1 ↔ sv v2694 < sv v992) := e_plt h_v2694 h_v992 (of_decide_eq_true rfl)
  have h_v2807 : R 1 0 0 1 v2807 v2807 := (r_sub hl (r_O hl) h_v2806 (of_decide_eq_true rfl))
  have e_v2807 : (v2807 = 1 ↔ ¬v2806 = 1) := e_not h_v2806 (of_decide_eq_true rfl)
  have h_v2808 : R 1 0 0 1 v2808 v2808 := (r_land hl h_v2805 h_v2807 (of_decide_eq_true rfl))
  have e_v2808 : (v2808 = 1 ↔ v2805 = 1 ∧ v2807 = 1) := e_land h_v2805 h_v2807 (of_decide_eq_true rfl)
  have h_v2809 : R 1 0 4611686018427387894 4611686018695823364 v2809 v2809 := (r_psel hl h_v2808 h_v23 h_v2803 (of_decide_eq_true rfl))
  have e_v2809 : v2809 = if v2808 = 1 then v23 else v2803 := e_psel h_v2808 h_v23 h_v2803 (of_decide_eq_true rfl)
  have h_v2810 : R 1 0 0 1 v2810 v2810 := (r_plt hl h_v2769 h_v51 (of_decide_eq_true rfl))
  have e_v2810 : (v2810 = 1 ↔ sv v2769 < sv v51) := e_plt h_v2769 h_v51 (of_decide_eq_true rfl)
  have h_v2811 : R 1 0 0 1 v2811 v2811 := (r_sub hl (r_O hl) h_v2810 (of_decide_eq_true rfl))
  have e_v2811 : (v2811 = 1 ↔ ¬v2810 = 1) := e_not h_v2810 (of_decide_eq_true rfl)
  have h_v2812 : R 1 0 0 1 v2812 v2812 := (r_plt hl h_v51 h_v2777 (of_decide_eq_true rfl))
  have e_v2812 : (v2812 = 1 ↔ sv v51 < sv v2777) := e_plt h_v51 h_v2777 (of_decide_eq_true rfl)
  have h_v2813 : R 1 0 0 1 v2813 v2813 := (r_sub hl (r_O hl) h_v2812 (of_decide_eq_true rfl))
  have e_v2813 : (v2813 = 1 ↔ ¬v2812 = 1) := e_not h_v2812 (of_decide_eq_true rfl)
  have h_v2814 : R 1 0 0 1 v2814 v2814 := (r_land hl h_v2810 h_v2813 (of_decide_eq_true rfl))
  have e_v2814 : (v2814 = 1 ↔ v2810 = 1 ∧ v2813 = 1) := e_land h_v2810 h_v2813 (of_decide_eq_true rfl)
  have h_v2815 : R 1 0 0 1 v2815 v2815 := (r_land hl h_v2810 h_v2812 (of_decide_eq_true rfl))
  have e_v2815 : (v2815 = 1 ↔ v2810 = 1 ∧ v2812 = 1) := e_land h_v2810 h_v2812 (of_decide_eq_true rfl)
  have h_v2816 : R 1 0 0 1 v2816 v2816 := (r_plt hl h_v2801 h_v51 (of_decide_eq_true rfl))
  have e_v2816 : (v2816 = 1 ↔ sv v2801 < sv v51) := e_plt h_v2801 h_v51 (of_decide_eq_true rfl)
  clear h_v23 h_v992 h_v2694 h_v2700 h_v2803 h_v2804 h_v2805 h_v2806 h_v2807 h_v2808 h_v2810 h_v2812 h_v2813
  have h_v2818 : R 1 0 0 1 v2818 v2818 := (r_plt hl h_v51 h_v2809 (of_decide_eq_true rfl))
  have e_v2818 : (v2818 = 1 ↔ sv v51 < sv v2809) := e_plt h_v51 h_v2809 (of_decide_eq_true rfl)
  have h_v2819 : R 1 0 0 1 v2819 v2819 := (r_sub hl (r_O hl) h_v2818 (of_decide_eq_true rfl))
  have e_v2819 : (v2819 = 1 ↔ ¬v2818 = 1) := e_not h_v2818 (of_decide_eq_true rfl)
  have h_v2820 : R 1 0 0 1 v2820 v2820 := (r_land hl h_v2816 h_v2819 (of_decide_eq_true rfl))
  have e_v2820 : (v2820 = 1 ↔ v2816 = 1 ∧ v2819 = 1) := e_land h_v2816 h_v2819 (of_decide_eq_true rfl)
  have h_v2821 : R 1 0 0 1 v2821 v2821 := (r_land hl h_v2816 h_v2818 (of_decide_eq_true rfl))
  have e_v2821 : (v2821 = 1 ↔ v2816 = 1 ∧ v2818 = 1) := e_land h_v2816 h_v2818 (of_decide_eq_true rfl)
  have h_v2822 : R 1 0 0 1 v2822 v2822 := (r_land hl h_v2815 h_v2821 (of_decide_eq_true rfl))
  have e_v2822 : (v2822 = 1 ↔ v2815 = 1 ∧ v2821 = 1) := e_land h_v2815 h_v2821 (of_decide_eq_true rfl)
  have h_v2823 : R 1 0 0 1 v2823 v2823 := (r_land hl h_v2811 h_v2821 (of_decide_eq_true rfl))
  have e_v2823 : (v2823 = 1 ↔ v2811 = 1 ∧ v2821 = 1) := e_land h_v2811 h_v2821 (of_decide_eq_true rfl)
  have h_v2824 : R 1 0 0 1 v2824 v2824 := (r_lor hl h_v2820 h_v2823 (of_decide_eq_true rfl))
  have e_v2824 : (v2824 = 1 ↔ v2820 = 1 ∨ v2823 = 1) := e_lor h_v2820 h_v2823 (of_decide_eq_true rfl)
  have h_v2825 : R 1 0 4611686018427387894 4611686018695823364 v2825 v2825 := (r_psel hl h_v2824 h_v2777 h_v2769 (of_decide_eq_true rfl))
  have e_v2825 : v2825 = if v2824 = 1 then v2777 else v2769 := e_psel h_v2824 h_v2777 h_v2769 (of_decide_eq_true rfl)
  have h_v2826 : R 1 0 0 1 v2826 v2826 := (r_sub hl (r_O hl) h_v2820 (of_decide_eq_true rfl))
  have e_v2826 : (v2826 = 1 ↔ ¬v2820 = 1) := e_not h_v2820 (of_decide_eq_true rfl)
  have h_v2827 : R 1 0 0 1 v2827 v2827 := (r_land hl h_v2815 h_v2826 (of_decide_eq_true rfl))
  have e_v2827 : (v2827 = 1 ↔ v2815 = 1 ∧ v2826 = 1) := e_land h_v2815 h_v2826 (of_decide_eq_true rfl)
  have h_v2828 : R 1 0 0 1 v2828 v2828 := (r_lor hl h_v2814 h_v2827 (of_decide_eq_true rfl))
  have e_v2828 : (v2828 = 1 ↔ v2814 = 1 ∨ v2827 = 1) := e_lor h_v2814 h_v2827 (of_decide_eq_true rfl)
  have h_v2829 : R 1 0 4611686018427387894 4611686018695823364 v2829 v2829 := (r_psel hl h_v2828 h_v2809 h_v2801 (of_decide_eq_true rfl))
  have e_v2829 : v2829 = if v2828 = 1 then v2809 else v2801 := e_psel h_v2828 h_v2809 h_v2801 (of_decide_eq_true rfl)
  have h_v2830 : R 1 0 0 1 v2830 v2830 := (r_land hl h_v2814 h_v2821 (of_decide_eq_true rfl))
  clear h_v2811 h_v2816 h_v2818 h_v2819 h_v2823 h_v2824 h_v2826 h_v2827 h_v2828
  have e_v2830 : (v2830 = 1 ↔ v2814 = 1 ∧ v2821 = 1) := e_land h_v2814 h_v2821 (of_decide_eq_true rfl)
  have h_v2831 : R 1 0 0 1 v2831 v2831 := (r_lor hl h_v2820 h_v2830 (of_decide_eq_true rfl))
  have e_v2831 : (v2831 = 1 ↔ v2820 = 1 ∨ v2830 = 1) := e_lor h_v2820 h_v2830 (of_decide_eq_true rfl)
  have h_v2832 : R 1 0 4611686018427387894 4611686018695823364 v2832 v2832 := (r_psel hl h_v2831 h_v2769 h_v2777 (of_decide_eq_true rfl))
  have e_v2832 : v2832 = if v2831 = 1 then v2769 else v2777 := e_psel h_v2831 h_v2769 h_v2777 (of_decide_eq_true rfl)
  have h_v2833 : R 1 0 0 1 v2833 v2833 := (r_land hl h_v2815 h_v2820 (of_decide_eq_true rfl))
  have e_v2833 : (v2833 = 1 ↔ v2815 = 1 ∧ v2820 = 1) := e_land h_v2815 h_v2820 (of_decide_eq_true rfl)
  have h_v2834 : R 1 0 0 1 v2834 v2834 := (r_lor hl h_v2814 h_v2833 (of_decide_eq_true rfl))
  have e_v2834 : (v2834 = 1 ↔ v2814 = 1 ∨ v2833 = 1) := e_lor h_v2814 h_v2833 (of_decide_eq_true rfl)
  have h_v2835 : R 1 0 4611686018427387894 4611686018695823364 v2835 v2835 := (r_psel hl h_v2834 h_v2801 h_v2809 (of_decide_eq_true rfl))
  have e_v2835 : v2835 = if v2834 = 1 then v2801 else v2809 := e_psel h_v2834 h_v2801 h_v2809 (of_decide_eq_true rfl)
  have h_v2836 : R 1 0 4611686015743033304 4683743614612799504 v2836 v2836 := (r_smx hl 29 h_v2829 h_v2825 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v2836 : sv v2836 = sv v2829 * sv v2825 := e_smx 29 h_v2829 h_v2825 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v2837 : R 1 0 4611686018427387893 4611686018695823368 v2837 v2837 := (r_srdF hl h_v2836 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v2837 : sv v2837 = sv v2836 / 2 ^ 28 := e_srdF h_v2836 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v2838 : R 1 0 4611686015743033304 4683743614612799504 v2838 v2838 := (r_smx hl 29 h_v2835 h_v2832 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v2838 : sv v2838 = sv v2835 * sv v2832 := e_smx 29 h_v2835 h_v2832 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v2839 : R 1 0 4611686018427387894 4611686018695823369 v2839 v2839 := (r_srdC hl h_v2838 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v2839 : sv v2839 = -((-sv v2838) / 2 ^ 28) := e_srdC h_v2838 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v2840 : R 1 0 4611686015743033304 4683743613539057664 v2840 v2840 := (r_smx hl 29 h_v2801 h_v2777 4611686015743033304 4683743613539057664 (of_decide_eq_true rfl))
  have e_v2840 : sv v2840 = sv v2801 * sv v2777 := e_smx 29 h_v2801 h_v2777 4611686015743033304 4683743613539057664 (of_decide_eq_true rfl)
  have h_v2841 : R 1 0 4611686018427387893 4611686018695823364 v2841 v2841 := (r_srdF hl h_v2840 4611686018427387893 4611686018695823364 (of_decide_eq_true rfl))
  have e_v2841 : sv v2841 = sv v2840 / 2 ^ 28 := e_srdF h_v2840 4611686018427387893 4611686018695823364 (of_decide_eq_true rfl)
  have h_v2842 : R 1 0 4611686015743033344 4683743612465315840 v2842 v2842 := (r_smx hl 29 h_v2801 h_v2769 4611686015743033344 4683743612465315840 (of_decide_eq_true rfl))
  have e_v2842 : sv v2842 = sv v2801 * sv v2769 := e_smx 29 h_v2801 h_v2769 4611686015743033344 4683743612465315840 (of_decide_eq_true rfl)
  clear h_v2769 h_v2777 h_v2801 h_v2809 h_v2814 h_v2815 h_v2820 h_v2821 h_v2825 h_v2829 h_v2830 h_v2831 h_v2832 h_v2833 h_v2834 h_v2835 h_v2836 h_v2838 h_v2840
  have h_v2843 : R 1 0 4611686018427387894 4611686018695823360 v2843 v2843 := (r_srdC hl h_v2842 4611686018427387894 4611686018695823360 (of_decide_eq_true rfl))
  have e_v2843 : sv v2843 = -((-sv v2842) / 2 ^ 28) := e_srdC h_v2842 4611686018427387894 4611686018695823360 (of_decide_eq_true rfl)
  have h_v2844 : R 1 0 0 1 v2844 v2844 := (r_plt hl h_v2837 h_v2841 (of_decide_eq_true rfl))
  have e_v2844 : (v2844 = 1 ↔ sv v2837 < sv v2841) := e_plt h_v2837 h_v2841 (of_decide_eq_true rfl)
  have h_v2845 : R 1 0 4611686018427387893 4611686018695823368 v2845 v2845 := (r_psel hl h_v2844 h_v2837 h_v2841 (of_decide_eq_true rfl))
  have e_v2845 : v2845 = if v2844 = 1 then v2837 else v2841 := e_psel h_v2844 h_v2837 h_v2841 (of_decide_eq_true rfl)
  have h_v2846 : R 1 0 0 1 v2846 v2846 := (r_plt hl h_v2839 h_v2843 (of_decide_eq_true rfl))
  have e_v2846 : (v2846 = 1 ↔ sv v2839 < sv v2843) := e_plt h_v2839 h_v2843 (of_decide_eq_true rfl)
  have h_v2847 : R 1 0 4611686018427387894 4611686018695823369 v2847 v2847 := (r_psel hl h_v2846 h_v2843 h_v2839 (of_decide_eq_true rfl))
  have e_v2847 : v2847 = if v2846 = 1 then v2843 else v2839 := e_psel h_v2846 h_v2843 h_v2839 (of_decide_eq_true rfl)
  have h_v2848 : R 1 0 4611686018427387893 4611686018695823368 v2848 v2848 := (r_psel hl h_v2822 h_v2845 h_v2837 (of_decide_eq_true rfl))
  have e_v2848 : v2848 = if v2822 = 1 then v2845 else v2837 := e_psel h_v2822 h_v2845 h_v2837 (of_decide_eq_true rfl)
  have h_v2849 : R 1 0 4611686018427387894 4611686018695823369 v2849 v2849 := (r_psel hl h_v2822 h_v2847 h_v2839 (of_decide_eq_true rfl))
  have e_v2849 : v2849 = if v2822 = 1 then v2847 else v2839 := e_psel h_v2822 h_v2847 h_v2839 (of_decide_eq_true rfl)
  have h_v2850 : R 1 0 0 1 v2850 v2850 := (r_plt hl h_v51 h_v2848 (of_decide_eq_true rfl))
  have e_v2850 : (v2850 = 1 ↔ sv v51 < sv v2848) := e_plt h_v51 h_v2848 (of_decide_eq_true rfl)
  have h_v2852 : R 1 0 0 1 v2852 v2852 := (r_plt hl h_v2744 h_v51 (of_decide_eq_true rfl))
  have e_v2852 : (v2852 = 1 ↔ sv v2744 < sv v51) := e_plt h_v2744 h_v51 (of_decide_eq_true rfl)
  have h_v2853 : R 1 0 4611686018427387893 4611686018695823369 v2853 v2853 := (r_psel hl h_v2852 h_v2848 h_v2849 (of_decide_eq_true rfl))
  have e_v2853 : v2853 = if v2852 = 1 then v2848 else v2849 := e_psel h_v2852 h_v2848 h_v2849 (of_decide_eq_true rfl)
  have h_v2856 : R 1 0 0 1 v2856 v2856 := (r_plt hl h_v2853 h_v2744 (of_decide_eq_true rfl))
  have e_v2856 : (v2856 = 1 ↔ sv v2853 < sv v2744) := e_plt h_v2853 h_v2744 (of_decide_eq_true rfl)
  have h_v2857 : R 1 0 0 1 v2857 v2857 := (r_land hl h_v2850 h_v2856 (of_decide_eq_true rfl))
  have e_v2857 : (v2857 = 1 ↔ v2850 = 1 ∧ v2856 = 1) := e_land h_v2850 h_v2856 (of_decide_eq_true rfl)
  have h_v2864 : R 1 0 0 1 v2864 v2864 := (r_lor hl h_v2670 h_v2857 (of_decide_eq_true rfl))
  clear h_v2744 h_v2822 h_v2837 h_v2839 h_v2841 h_v2842 h_v2843 h_v2844 h_v2845 h_v2846 h_v2847 h_v2848 h_v2849 h_v2850 h_v2852 h_v2853 h_v2856
  have e_v2864 : (v2864 = 1 ↔ v2670 = 1 ∨ v2857 = 1) := e_lor h_v2670 h_v2857 (of_decide_eq_true rfl)
  have h_v2866 : R 1 0 4611686018427387904 4611686019501129727 v2866 v2866 := (r1_hxa hb_H4 0 (of_decide_eq_true rfl))
  have e_v2866 : sv v2866 = ((H4 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H4 0 (of_decide_eq_true rfl)
  have h_v2867 : R 1 0 0 1 v2867 v2867 := (r_plt hl h_v51 h_v2866 (of_decide_eq_true rfl))
  have e_v2867 : (v2867 = 1 ↔ sv v51 < sv v2866) := e_plt h_v51 h_v2866 (of_decide_eq_true rfl)
  have h_v2868 : R 1 0 0 1 v2868 v2868 := (r_sub hl (r_O hl) h_v2867 (of_decide_eq_true rfl))
  have e_v2868 : (v2868 = 1 ↔ ¬v2867 = 1) := e_not h_v2867 (of_decide_eq_true rfl)
  have h_t2866_1 : R 1 0 4611686018427387904 4611686018695823363 t2866.1 t2866.1 := r_sc1 hl h_v2866 (of_decide_eq_true rfl)
  have h_t2866_2 : R 1 0 4611686018158952445 4611686018695823363 t2866.2 t2866.2 := r_sc2 hl h_v2866 (of_decide_eq_true rfl)
  have e_t2866_1 : sv t2866.1 = (sc28pS (scArg v2866)).1 := e_sc1 h_v2866 (of_decide_eq_true rfl)
  have e_t2866_2 : sv t2866.2 = (sc28pS (scArg v2866)).2 := e_sc2 h_v2866 (of_decide_eq_true rfl)
  have h_v2870 : R 1 0 4611686018158952441 4611686018695823359 v2870 v2870 := (r_sub hl (r_add hl h_v18 h_t2866_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2870 : sv v2870 = sv v18 + sv t2866.2 := e_add h_v18 h_t2866_2 (of_decide_eq_true rfl)
  have h_v2871 : R 1 0 0 1 v2871 v2871 := (r_plt hl h_v2870 h_v95 (of_decide_eq_true rfl))
  have e_v2871 : (v2871 = 1 ↔ sv v2870 < sv v95) := e_plt h_v2870 h_v95 (of_decide_eq_true rfl)
  have h_v2872 : R 1 0 4611686018158952441 4611686018695823359 v2872 v2872 := (r_psel hl h_v2871 h_v95 h_v2870 (of_decide_eq_true rfl))
  have e_v2872 : v2872 = if v2871 = 1 then v95 else v2870 := e_psel h_v2871 h_v95 h_v2870 (of_decide_eq_true rfl)
  have h_v2873 : R 1 0 4467570797333970944 4755801225025290240 v2873 v2873 := (r_sshl hl h_v2674 4467570797333970944 4755801225025290240 (of_decide_eq_true rfl))
  have e_v2873 : sv v2873 = sv v2674 * 2 ^ 28 := e_sshl h_v2674 4467570797333970944 4755801225025290240 (of_decide_eq_true rfl)
  have h_v2874 : R 1 0 4539628420094492609 4683743614612799479 v2874 v2874 := (r_smx hl 29 h_v2872 h_v2675 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl))
  have e_v2874 : sv v2874 = sv v2872 * sv v2675 := e_smx 29 h_v2872 h_v2675 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl)
  have h_v2875 : R 1 0 0 1 v2875 v2875 := (r_plt hl h_v2874 h_v2873 (of_decide_eq_true rfl))
  have e_v2875 : (v2875 = 1 ↔ sv v2874 < sv v2873) := e_plt h_v2874 h_v2873 (of_decide_eq_true rfl)
  have h_v2876 : R 1 0 0 1 v2876 v2876 := (r_sub hl (r_O hl) h_v2875 (of_decide_eq_true rfl))
  have e_v2876 : (v2876 = 1 ↔ ¬v2875 = 1) := e_not h_v2875 (of_decide_eq_true rfl)
  clear h_v18 h_v95 h_v2857 h_v2867 h_t2866_1 h_t2866_2 e_t2866_1 h_v2870 h_v2871 h_v2872 h_v2873 h_v2874 h_v2875
  have h_v2877 : R 1 0 0 1 v2877 v2877 := (r_plt hl h_v780 h_v2866 (of_decide_eq_true rfl))
  have e_v2877 : (v2877 = 1 ↔ sv v780 < sv v2866) := e_plt h_v780 h_v2866 (of_decide_eq_true rfl)
  have h_v2878 : R 1 0 0 1 v2878 v2878 := (r_sub hl (r_O hl) h_v2877 (of_decide_eq_true rfl))
  have e_v2878 : (v2878 = 1 ↔ ¬v2877 = 1) := e_not h_v2877 (of_decide_eq_true rfl)
  have h_v2879 : R 1 0 0 1 v2879 v2879 := (r_land hl h_v2876 h_v2878 (of_decide_eq_true rfl))
  have e_v2879 : (v2879 = 1 ↔ v2876 = 1 ∧ v2878 = 1) := e_land h_v2876 h_v2878 (of_decide_eq_true rfl)
  have h_v2880 : R 1 0 0 1 v2880 v2880 := (r_lor hl h_v2868 h_v2879 (of_decide_eq_true rfl))
  have e_v2880 : (v2880 = 1 ↔ v2868 = 1 ∨ v2879 = 1) := e_lor h_v2868 h_v2879 (of_decide_eq_true rfl)
  have h_v2881 : R 1 0 4611686018427387904 4611686019501129727 v2881 v2881 := (r_psel hl h_v2880 h_v2866 h_v51 (of_decide_eq_true rfl))
  have e_v2881 : v2881 = if v2880 = 1 then v2866 else v51 := e_psel h_v2880 h_v2866 h_v51 (of_decide_eq_true rfl)
  have h_v2895 : R 1 0 4611686018427387904 4611686019501129727 v2895 v2895 := (r_psel hl h_v2380 h_v2881 h_v51 (of_decide_eq_true rfl))
  have e_v2895 : v2895 = if v2380 = 1 then v2881 else v51 := e_psel h_v2380 h_v2881 h_v51 (of_decide_eq_true rfl)
  have h_v2897 : R 1 0 0 1 v2897 v2897 := (r_land hl h_v2380 h_v2864 (of_decide_eq_true rfl))
  have e_v2897 : (v2897 = 1 ↔ v2380 = 1 ∧ v2864 = 1) := e_land h_v2380 h_v2864 (of_decide_eq_true rfl)
  have h_v2898 : R 1 0 4611686018427387904 4611686019270702760 v2898 v2898 := (r_psel hl h_v2670 h_v780 h_v51 (of_decide_eq_true rfl))
  have e_v2898 : v2898 = if v2670 = 1 then v780 else v51 := e_psel h_v2670 h_v780 h_v51 (of_decide_eq_true rfl)
  have h_v2900 : R 1 0 4611686018427387904 4611686019501129727 v2900 v2900 := (r_psel hl h_v2897 h_v2898 h_v2895 (of_decide_eq_true rfl))
  have e_v2900 : v2900 = if v2897 = 1 then v2898 else v2895 := e_psel h_v2897 h_v2898 h_v2895 (of_decide_eq_true rfl)
  have h_v2902 : R 1 0 4611686017353646081 4611686020574871550 v2902 v2902 := (r_sub hl (r_add hl h_v265 h_v2900 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2902 : sv v2902 = sv v265 + sv v2900 := e_add h_v265 h_v2900 (of_decide_eq_true rfl)
  have h_v2904 : R 1 0 4611686016279904258 4611686021648613373 v2904 v2904 := (r_sub hl (r_add hl h_v620 h_v2902 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2904 : sv v2904 = sv v620 + sv v2902 := e_add h_v620 h_v2902 (of_decide_eq_true rfl)
  have h_v2906 : R 1 0 0 1 v2906 v2906 := (r_plt hl h_v2904 h_v6 (of_decide_eq_true rfl))
  have e_v2906 : (v2906 = 1 ↔ sv v2904 < sv v6) := e_plt h_v2904 h_v6 (of_decide_eq_true rfl)
  have h_v2907 : R 1 0 0 1 v2907 v2907 := (r_sub hl (r_O hl) h_v2906 (of_decide_eq_true rfl))
  clear h_OFFr h_v6 h_v51 h_v780 h_v2864 h_v2866 h_v2868 h_v2876 h_v2877 h_v2878 h_v2879 h_v2880 h_v2881 h_v2895 h_v2897 h_v2898 h_v2900 h_v2902 h_v2904
  have e_v2907 : (v2907 = 1 ↔ ¬v2906 = 1) := e_not h_v2906 (of_decide_eq_true rfl)
  have h_v2911 : R 1 0 0 1 v2911 v2911 := (r_land hl h_v13 h_v37 (of_decide_eq_true rfl))
  have e_v2911 : (v2911 = 1 ↔ v13 = 1 ∧ v37 = 1) := e_land h_v13 h_v37 (of_decide_eq_true rfl)
  have h_v2912 : R 1 0 0 1 v2912 v2912 := (r_land hl h_v92 h_v2911 (of_decide_eq_true rfl))
  have e_v2912 : (v2912 = 1 ↔ v92 = 1 ∧ v2911 = 1) := e_land h_v92 h_v2911 (of_decide_eq_true rfl)
  have h_v2913 : R 1 0 0 1 v2913 v2913 := (r_land hl h_v13 h_v2912 (of_decide_eq_true rfl))
  have e_v2913 : (v2913 = 1 ↔ v13 = 1 ∧ v2912 = 1) := e_land h_v13 h_v2912 (of_decide_eq_true rfl)
  have h_v2914 : R 1 0 0 1 v2914 v2914 := (r_land hl h_v110 h_v2913 (of_decide_eq_true rfl))
  have e_v2914 : (v2914 = 1 ↔ v110 = 1 ∧ v2913 = 1) := e_land h_v110 h_v2913 (of_decide_eq_true rfl)
  have h_v2915 : R 1 0 0 1 v2915 v2915 := (r_land hl h_v110 h_v2914 (of_decide_eq_true rfl))
  have e_v2915 : (v2915 = 1 ↔ v110 = 1 ∧ v2914 = 1) := e_land h_v110 h_v2914 (of_decide_eq_true rfl)
  have h_v2916 : R 1 0 0 1 v2916 v2916 := (r_land hl h_v270 h_v2915 (of_decide_eq_true rfl))
  have e_v2916 : (v2916 = 1 ↔ v270 = 1 ∧ v2915 = 1) := e_land h_v270 h_v2915 (of_decide_eq_true rfl)
  have h_v2917 : R 1 0 0 1 v2917 v2917 := (r_land hl h_v270 h_v2916 (of_decide_eq_true rfl))
  have e_v2917 : (v2917 = 1 ↔ v270 = 1 ∧ v2916 = 1) := e_land h_v270 h_v2916 (of_decide_eq_true rfl)
  have h_v2918 : R 1 0 0 1 v2918 v2918 := (r_land hl h_v13 h_v2917 (of_decide_eq_true rfl))
  have e_v2918 : (v2918 = 1 ↔ v13 = 1 ∧ v2917 = 1) := e_land h_v13 h_v2917 (of_decide_eq_true rfl)
  have h_v2919 : R 1 0 0 1 v2919 v2919 := (r_land hl h_v423 h_v2918 (of_decide_eq_true rfl))
  have e_v2919 : (v2919 = 1 ↔ v423 = 1 ∧ v2918 = 1) := e_land h_v423 h_v2918 (of_decide_eq_true rfl)
  have h_v2920 : R 1 0 0 1 v2920 v2920 := (r_land hl h_v471 h_v2919 (of_decide_eq_true rfl))
  have e_v2920 : (v2920 = 1 ↔ v471 = 1 ∧ v2919 = 1) := e_land h_v471 h_v2919 (of_decide_eq_true rfl)
  have h_v2921 : R 1 0 0 1 v2921 v2921 := (r_land hl h_v13 h_v2920 (of_decide_eq_true rfl))
  have e_v2921 : (v2921 = 1 ↔ v13 = 1 ∧ v2920 = 1) := e_land h_v13 h_v2920 (of_decide_eq_true rfl)
  have h_v2922 : R 1 0 0 1 v2922 v2922 := (r_land hl h_v474 h_v2921 (of_decide_eq_true rfl))
  have e_v2922 : (v2922 = 1 ↔ v474 = 1 ∧ v2921 = 1) := e_land h_v474 h_v2921 (of_decide_eq_true rfl)
  clear h_v2906 h_v2911 h_v2912 h_v2913 h_v2914 h_v2915 h_v2916 h_v2917 h_v2918 h_v2919 h_v2920 h_v2921
  have h_v2923 : R 1 0 0 1 v2923 v2923 := (r_land hl h_v474 h_v2922 (of_decide_eq_true rfl))
  have e_v2923 : (v2923 = 1 ↔ v474 = 1 ∧ v2922 = 1) := e_land h_v474 h_v2922 (of_decide_eq_true rfl)
  have h_v2924 : R 1 0 0 1 v2924 v2924 := (r_land hl h_v625 h_v2923 (of_decide_eq_true rfl))
  have e_v2924 : (v2924 = 1 ↔ v625 = 1 ∧ v2923 = 1) := e_land h_v625 h_v2923 (of_decide_eq_true rfl)
  have h_v2925 : R 1 0 0 1 v2925 v2925 := (r_land hl h_v625 h_v2924 (of_decide_eq_true rfl))
  have e_v2925 : (v2925 = 1 ↔ v625 = 1 ∧ v2924 = 1) := e_land h_v625 h_v2924 (of_decide_eq_true rfl)
  have h_v2926 : R 1 0 0 1 v2926 v2926 := (r_land hl h_v796 h_v2925 (of_decide_eq_true rfl))
  have e_v2926 : (v2926 = 1 ↔ v796 = 1 ∧ v2925 = 1) := e_land h_v796 h_v2925 (of_decide_eq_true rfl)
  have h_v2927 : R 1 0 0 1 v2927 v2927 := (r_land hl h_v910 h_v2926 (of_decide_eq_true rfl))
  have e_v2927 : (v2927 = 1 ↔ v910 = 1 ∧ v2926 = 1) := e_land h_v910 h_v2926 (of_decide_eq_true rfl)
  have h_v2928 : R 1 0 0 1 v2928 v2928 := (r_land hl h_v910 h_v2927 (of_decide_eq_true rfl))
  have e_v2928 : (v2928 = 1 ↔ v910 = 1 ∧ v2927 = 1) := e_land h_v910 h_v2927 (of_decide_eq_true rfl)
  have h_v2929 : R 1 0 0 1 v2929 v2929 := (r_land hl h_v1083 h_v2928 (of_decide_eq_true rfl))
  have e_v2929 : (v2929 = 1 ↔ v1083 = 1 ∧ v2928 = 1) := e_land h_v1083 h_v2928 (of_decide_eq_true rfl)
  have h_v2930 : R 1 0 0 1 v2930 v2930 := (r_land hl h_v1083 h_v2929 (of_decide_eq_true rfl))
  have e_v2930 : (v2930 = 1 ↔ v1083 = 1 ∧ v2929 = 1) := e_land h_v1083 h_v2929 (of_decide_eq_true rfl)
  have h_v2931 : R 1 0 0 1 v2931 v2931 := (r_land hl h_v1273 h_v2930 (of_decide_eq_true rfl))
  have e_v2931 : (v2931 = 1 ↔ v1273 = 1 ∧ v2930 = 1) := e_land h_v1273 h_v2930 (of_decide_eq_true rfl)
  have h_v2932 : R 1 0 0 1 v2932 v2932 := (r_land hl h_v796 h_v2931 (of_decide_eq_true rfl))
  have e_v2932 : (v2932 = 1 ↔ v796 = 1 ∧ v2931 = 1) := e_land h_v796 h_v2931 (of_decide_eq_true rfl)
  have h_v2933 : R 1 0 0 1 v2933 v2933 := (r_land hl h_v1348 h_v2932 (of_decide_eq_true rfl))
  have e_v2933 : (v2933 = 1 ↔ v1348 = 1 ∧ v2932 = 1) := e_land h_v1348 h_v2932 (of_decide_eq_true rfl)
  have h_v2934 : R 1 0 0 1 v2934 v2934 := (r_land hl h_v1348 h_v2933 (of_decide_eq_true rfl))
  have e_v2934 : (v2934 = 1 ↔ v1348 = 1 ∧ v2933 = 1) := e_land h_v1348 h_v2933 (of_decide_eq_true rfl)
  have h_v2935 : R 1 0 0 1 v2935 v2935 := (r_land hl h_v1519 h_v2934 (of_decide_eq_true rfl))
  clear h_v2922 h_v2923 h_v2924 h_v2925 h_v2926 h_v2927 h_v2928 h_v2929 h_v2930 h_v2931 h_v2932 h_v2933
  have e_v2935 : (v2935 = 1 ↔ v1519 = 1 ∧ v2934 = 1) := e_land h_v1519 h_v2934 (of_decide_eq_true rfl)
  have h_v2936 : R 1 0 0 1 v2936 v2936 := (r_land hl h_v1519 h_v2935 (of_decide_eq_true rfl))
  have e_v2936 : (v2936 = 1 ↔ v1519 = 1 ∧ v2935 = 1) := e_land h_v1519 h_v2935 (of_decide_eq_true rfl)
  have h_v2937 : R 1 0 0 1 v2937 v2937 := (r_land hl h_v1709 h_v2936 (of_decide_eq_true rfl))
  have e_v2937 : (v2937 = 1 ↔ v1709 = 1 ∧ v2936 = 1) := e_land h_v1709 h_v2936 (of_decide_eq_true rfl)
  have h_v2938 : R 1 0 0 1 v2938 v2938 := (r_land hl h_v1718 h_v2937 (of_decide_eq_true rfl))
  have e_v2938 : (v2938 = 1 ↔ v1718 = 1 ∧ v2937 = 1) := e_land h_v1718 h_v2937 (of_decide_eq_true rfl)
  have h_v2939 : R 1 0 0 1 v2939 v2939 := (r_land hl h_v1719 h_v2938 (of_decide_eq_true rfl))
  have e_v2939 : (v2939 = 1 ↔ v1719 = 1 ∧ v2938 = 1) := e_land h_v1719 h_v2938 (of_decide_eq_true rfl)
  have h_v2940 : R 1 0 0 1 v2940 v2940 := (r_land hl h_v1751 h_v2939 (of_decide_eq_true rfl))
  have e_v2940 : (v2940 = 1 ↔ v1751 = 1 ∧ v2939 = 1) := e_land h_v1751 h_v2939 (of_decide_eq_true rfl)
  have h_v2941 : R 1 0 0 1 v2941 v2941 := (r_land hl h_v1751 h_v2940 (of_decide_eq_true rfl))
  have e_v2941 : (v2941 = 1 ↔ v1751 = 1 ∧ v2940 = 1) := e_land h_v1751 h_v2940 (of_decide_eq_true rfl)
  have h_v2942 : R 1 0 0 1 v2942 v2942 := (r_land hl h_v1790 h_v2941 (of_decide_eq_true rfl))
  have e_v2942 : (v2942 = 1 ↔ v1790 = 1 ∧ v2941 = 1) := e_land h_v1790 h_v2941 (of_decide_eq_true rfl)
  have h_v2943 : R 1 0 0 1 v2943 v2943 := (r_land hl h_v1825 h_v2942 (of_decide_eq_true rfl))
  have e_v2943 : (v2943 = 1 ↔ v1825 = 1 ∧ v2942 = 1) := e_land h_v1825 h_v2942 (of_decide_eq_true rfl)
  have h_v2944 : R 1 0 0 1 v2944 v2944 := (r_land hl h_v1826 h_v2943 (of_decide_eq_true rfl))
  have e_v2944 : (v2944 = 1 ↔ v1826 = 1 ∧ v2943 = 1) := e_land h_v1826 h_v2943 (of_decide_eq_true rfl)
  have h_v2945 : R 1 0 0 1 v2945 v2945 := (r_land hl h_v1858 h_v2944 (of_decide_eq_true rfl))
  have e_v2945 : (v2945 = 1 ↔ v1858 = 1 ∧ v2944 = 1) := e_land h_v1858 h_v2944 (of_decide_eq_true rfl)
  have h_v2946 : R 1 0 0 1 v2946 v2946 := (r_land hl h_v1858 h_v2945 (of_decide_eq_true rfl))
  have e_v2946 : (v2946 = 1 ↔ v1858 = 1 ∧ v2945 = 1) := e_land h_v1858 h_v2945 (of_decide_eq_true rfl)
  have h_v2947 : R 1 0 0 1 v2947 v2947 := (r_land hl h_v1897 h_v2946 (of_decide_eq_true rfl))
  have e_v2947 : (v2947 = 1 ↔ v1897 = 1 ∧ v2946 = 1) := e_land h_v1897 h_v2946 (of_decide_eq_true rfl)
  clear h_v2934 h_v2935 h_v2936 h_v2937 h_v2938 h_v2939 h_v2940 h_v2941 h_v2942 h_v2943 h_v2944 h_v2945 h_v2946
  have h_v2948 : R 1 0 0 1 v2948 v2948 := (r_land hl h_v13 h_v2947 (of_decide_eq_true rfl))
  have e_v2948 : (v2948 = 1 ↔ v13 = 1 ∧ v2947 = 1) := e_land h_v13 h_v2947 (of_decide_eq_true rfl)
  have h_v2949 : R 1 0 0 1 v2949 v2949 := (r_land hl h_v1953 h_v2948 (of_decide_eq_true rfl))
  have e_v2949 : (v2949 = 1 ↔ v1953 = 1 ∧ v2948 = 1) := e_land h_v1953 h_v2948 (of_decide_eq_true rfl)
  have h_v2950 : R 1 0 0 1 v2950 v2950 := (r_land hl h_v2001 h_v2949 (of_decide_eq_true rfl))
  have e_v2950 : (v2950 = 1 ↔ v2001 = 1 ∧ v2949 = 1) := e_land h_v2001 h_v2949 (of_decide_eq_true rfl)
  have h_v2951 : R 1 0 0 1 v2951 v2951 := (r_land hl h_v13 h_v2950 (of_decide_eq_true rfl))
  have e_v2951 : (v2951 = 1 ↔ v13 = 1 ∧ v2950 = 1) := e_land h_v13 h_v2950 (of_decide_eq_true rfl)
  have h_v2952 : R 1 0 0 1 v2952 v2952 := (r_land hl h_v110 h_v2951 (of_decide_eq_true rfl))
  have e_v2952 : (v2952 = 1 ↔ v110 = 1 ∧ v2951 = 1) := e_land h_v110 h_v2951 (of_decide_eq_true rfl)
  have h_v2953 : R 1 0 0 1 v2953 v2953 := (r_land hl h_v110 h_v2952 (of_decide_eq_true rfl))
  have e_v2953 : (v2953 = 1 ↔ v110 = 1 ∧ v2952 = 1) := e_land h_v110 h_v2952 (of_decide_eq_true rfl)
  have h_v2954 : R 1 0 0 1 v2954 v2954 := (r_land hl h_v2007 h_v2953 (of_decide_eq_true rfl))
  have e_v2954 : (v2954 = 1 ↔ v2007 = 1 ∧ v2953 = 1) := e_land h_v2007 h_v2953 (of_decide_eq_true rfl)
  have h_v2955 : R 1 0 0 1 v2955 v2955 := (r_land hl h_v2007 h_v2954 (of_decide_eq_true rfl))
  have e_v2955 : (v2955 = 1 ↔ v2007 = 1 ∧ v2954 = 1) := e_land h_v2007 h_v2954 (of_decide_eq_true rfl)
  have h_v2956 : R 1 0 0 1 v2956 v2956 := (r_land hl h_v13 h_v2955 (of_decide_eq_true rfl))
  have e_v2956 : (v2956 = 1 ↔ v13 = 1 ∧ v2955 = 1) := e_land h_v13 h_v2955 (of_decide_eq_true rfl)
  have h_v2957 : R 1 0 0 1 v2957 v2957 := (r_land hl h_v2165 h_v2956 (of_decide_eq_true rfl))
  have e_v2957 : (v2957 = 1 ↔ v2165 = 1 ∧ v2956 = 1) := e_land h_v2165 h_v2956 (of_decide_eq_true rfl)
  have h_v2958 : R 1 0 0 1 v2958 v2958 := (r_land hl h_v2213 h_v2957 (of_decide_eq_true rfl))
  have e_v2958 : (v2958 = 1 ↔ v2213 = 1 ∧ v2957 = 1) := e_land h_v2213 h_v2957 (of_decide_eq_true rfl)
  have h_v2959 : R 1 0 0 1 v2959 v2959 := (r_land hl h_v13 h_v2958 (of_decide_eq_true rfl))
  have e_v2959 : (v2959 = 1 ↔ v13 = 1 ∧ v2958 = 1) := e_land h_v13 h_v2958 (of_decide_eq_true rfl)
  have h_v2960 : R 1 0 0 1 v2960 v2960 := (r_land hl h_v474 h_v2959 (of_decide_eq_true rfl))
  clear h_v2947 h_v2948 h_v2949 h_v2950 h_v2951 h_v2952 h_v2953 h_v2954 h_v2955 h_v2956 h_v2957 h_v2958
  have e_v2960 : (v2960 = 1 ↔ v474 = 1 ∧ v2959 = 1) := e_land h_v474 h_v2959 (of_decide_eq_true rfl)
  have h_v2961 : R 1 0 0 1 v2961 v2961 := (r_land hl h_v474 h_v2960 (of_decide_eq_true rfl))
  have e_v2961 : (v2961 = 1 ↔ v474 = 1 ∧ v2960 = 1) := e_land h_v474 h_v2960 (of_decide_eq_true rfl)
  have h_v2962 : R 1 0 0 1 v2962 v2962 := (r_land hl h_v2219 h_v2961 (of_decide_eq_true rfl))
  have e_v2962 : (v2962 = 1 ↔ v2219 = 1 ∧ v2961 = 1) := e_land h_v2219 h_v2961 (of_decide_eq_true rfl)
  have h_v2963 : R 1 0 0 1 v2963 v2963 := (r_land hl h_v2219 h_v2962 (of_decide_eq_true rfl))
  have e_v2963 : (v2963 = 1 ↔ v2219 = 1 ∧ v2962 = 1) := e_land h_v2219 h_v2962 (of_decide_eq_true rfl)
  have h_v2964 : R 1 0 0 1 v2964 v2964 := (r_land hl h_v2382 h_v2963 (of_decide_eq_true rfl))
  have e_v2964 : (v2964 = 1 ↔ v2382 = 1 ∧ v2963 = 1) := e_land h_v2382 h_v2963 (of_decide_eq_true rfl)
  have h_v2965 : R 1 0 0 1 v2965 v2965 := (r_land hl h_v2490 h_v2964 (of_decide_eq_true rfl))
  have e_v2965 : (v2965 = 1 ↔ v2490 = 1 ∧ v2964 = 1) := e_land h_v2490 h_v2964 (of_decide_eq_true rfl)
  have h_v2966 : R 1 0 0 1 v2966 v2966 := (r_land hl h_v2678 h_v2965 (of_decide_eq_true rfl))
  have e_v2966 : (v2966 = 1 ↔ v2678 = 1 ∧ v2965 = 1) := e_land h_v2678 h_v2965 (of_decide_eq_true rfl)
  have h_v2967 : R 1 0 0 1 v2967 v2967 := (r_land hl h_v2907 h_v2966 (of_decide_eq_true rfl))
  have e_v2967 : (v2967 = 1 ↔ v2907 = 1 ∧ v2966 = 1) := e_land h_v2907 h_v2966 (of_decide_eq_true rfl)
  exact fun _ k => k e_v2684 e_v2685 e_v2686 e_v2687 e_v2688 e_v2689 e_v2690 e_v2691 e_v2692 e_v2693 e_v2694 e_v2695 e_v2696 e_v2697 e_v2698 e_v2699 e_v2700 e_v2701 e_v2702 e_v2703 e_v2704 e_v2706 e_v2707 e_v2708 e_v2709 e_v2710 e_v2712 e_v2713 e_v2714 e_v2715 e_v2716 e_v2724 e_v2725 e_v2726 e_v2727 e_v2728 e_v2729 e_v2732 e_v2733 e_v2736 e_v2737 e_v2740 e_v2741 e_v2743 e_v2744 e_v2746 e_v2747 e_v2748 e_v2749 e_v2750 e_v2751 e_v2752 e_v2753 e_v2754 e_v2755 e_v2756 e_v2757 e_v2758 e_v2759 e_v2760 e_v2761 e_v2762 e_v2763 e_v2764 e_v2765 e_v2766 e_v2767 e_v2768 e_v2769 e_v2770 e_v2771 e_v2772 e_v2773 e_v2774 e_v2775 e_v2776 e_v2777 e_v2778 e_v2779 e_v2780 e_v2781 e_v2782 e_v2783 e_v2784 e_v2785 e_v2786 e_v2787 e_v2788 e_v2789 e_v2790 e_v2791 e_v2792 e_v2793 e_v2794 e_v2795 e_v2796 e_v2797 e_v2798 e_v2799 e_v2800 e_v2801 e_v2802 e_v2803 e_v2804 e_v2805 e_v2806 e_v2807 e_v2808 e_v2809 e_v2810 e_v2811 e_v2812 e_v2813 e_v2814 e_v2815 e_v2816 e_v2818 e_v2819 e_v2820 e_v2821 e_v2822 e_v2823 e_v2824 e_v2825 e_v2826 e_v2827 e_v2828 e_v2829 e_v2830 e_v2831 e_v2832 e_v2833 e_v2834 e_v2835 e_v2836 e_v2837 e_v2838 e_v2839 e_v2840 e_v2841 e_v2842 e_v2843 e_v2844 e_v2845 e_v2846 e_v2847 e_v2848 e_v2849 e_v2850 e_v2852 e_v2853 e_v2856 e_v2857 e_v2864 e_v2866 e_v2867 e_v2868 e_t2866_2 e_v2870 e_v2871 e_v2872 e_v2873 e_v2874 e_v2875 e_v2876 e_v2877 e_v2878 e_v2879 e_v2880 e_v2881 e_v2895 e_v2897 e_v2898 e_v2900 e_v2902 e_v2904 e_v2906 e_v2907 e_v2911 e_v2912 e_v2913 e_v2914 e_v2915 e_v2916 e_v2917 e_v2918 e_v2919 e_v2920 e_v2921 e_v2922 e_v2923 e_v2924 e_v2925 e_v2926 e_v2927 e_v2928 e_v2929 e_v2930 e_v2931 e_v2932 e_v2933 e_v2934 e_v2935 e_v2936 e_v2937 e_v2938 e_v2939 e_v2940 e_v2941 e_v2942 e_v2943 e_v2944 e_v2945 e_v2946 e_v2947 e_v2948 e_v2949 e_v2950 e_v2951 e_v2952 e_v2953 e_v2954 e_v2955 e_v2956 e_v2957 e_v2958 e_v2959 e_v2960 e_v2961 e_v2962 e_v2963 e_v2964 e_v2965 e_v2966 e_v2967

end D3Prog
