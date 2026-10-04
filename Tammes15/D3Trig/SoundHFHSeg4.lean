import Tammes15.D3Trig.Prog.HFH
import Tammes15.D3Prog.Sem

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progHFH_seg4 (F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (v23 : ℕ) (v47 : ℕ) (v101 : ℕ) (v119 : ℕ) (v279 : ℕ) (v426 : ℕ) (v432 : ℕ) (v480 : ℕ) (v483 : ℕ) (v634 : ℕ) (v781 : ℕ) (v788 : ℕ) (v836 : ℕ) (v863 : ℕ) (v1374 : ℕ) (v1834 : ℕ) (v1843 : ℕ) (v1844 : ℕ) (v1876 : ℕ) (v1915 : ℕ) (v1950 : ℕ) (v1951 : ℕ) (v1983 : ℕ) (v2022 : ℕ) (v2077 : ℕ) (v2124 : ℕ) (v2128 : ℕ) (v2283 : ℕ) (v2330 : ℕ) (v2334 : ℕ) (v2492 : ℕ) (v2591 : ℕ) (v2592 : ℕ) (v2595 : ℕ) (v2596 : ℕ) (v2776 : ℕ) (h_v23 : R 1 0 0 1 v23 v23) (h_v47 : R 1 0 0 1 v47 v47) (h_v101 : R 1 0 0 1 v101 v101) (h_v119 : R 1 0 0 1 v119 v119) (h_v279 : R 1 0 0 1 v279 v279) (h_v426 : R 1 0 4611686017353646081 4611686019501129727 v426 v426) (h_v432 : R 1 0 0 1 v432 v432) (h_v480 : R 1 0 0 1 v480 v480) (h_v483 : R 1 0 0 1 v483 v483) (h_v634 : R 1 0 0 1 v634 v634) (h_v781 : R 1 0 4611686017353646081 4611686019501129727 v781 v781) (h_v788 : R 1 0 0 1 v788 v788) (h_v836 : R 1 0 0 1 v836 v836) (h_v863 : R 1 0 4611686018158952386 4611686018695823360 v863 v863) (h_v1374 : R 1 0 0 1 v1374 v1374) (h_v1834 : R 1 0 0 1 v1834 v1834) (h_v1843 : R 1 0 0 1 v1843 v1843) (h_v1844 : R 1 0 0 1 v1844 v1844) (h_v1876 : R 1 0 0 1 v1876 v1876) (h_v1915 : R 1 0 0 1 v1915 v1915) (h_v1950 : R 1 0 0 1 v1950 v1950) (h_v1951 : R 1 0 0 1 v1951 v1951) (h_v1983 : R 1 0 0 1 v1983 v1983) (h_v2022 : R 1 0 0 1 v2022 v2022) (h_v2077 : R 1 0 0 1 v2077 v2077) (h_v2124 : R 1 0 0 1 v2124 v2124) (h_v2128 : R 1 0 0 1 v2128 v2128) (h_v2283 : R 1 0 0 1 v2283 v2283) (h_v2330 : R 1 0 0 1 v2330 v2330) (h_v2334 : R 1 0 0 1 v2334 v2334) (h_v2492 : R 1 0 0 1 v2492 v2492) (h_v2591 : R 1 0 4611686018427387899 4611686018695823375 v2591 v2591) (h_v2592 : R 1 0 4611686018427387899 4611686018695823375 v2592 v2592) (h_v2595 : R 1 0 4611686018427387899 4611686018695823375 v2595 v2595) (h_v2596 : R 1 0 4611686018427387899 4611686018695823375 v2596 v2596) (h_v2776 : R 1 0 0 1 v2776 v2776) :
    let OFFr := Nat.mul 1 4611686018427387904
    let v6 := ix 1 F3 0
    let v9 := Nat.mul 1 4611686018427387904
    let v20 := Nat.mul 1 4611686019270702761
    let v31 := Nat.mul 1 4611686018427387908
    let v33 := Nat.mul 1 4611686018695823360
    let v104 := Nat.mul 1 4611686018158952448
    let v114 := Nat.mul 1 4611686018427387905
    let v1035 := Nat.mul 1 4683743612465315840
    let v1062 := Nat.mul 1 4647714815446351872
    let v2785 := smx 29 1 v2592 v2592
    let v2786 := srdC 1 v2785
    let v2787 := Nat.sub (Nat.add v2786 v2786) OFFr
    let v2788 := Nat.sub (Nat.add v33 OFFr) v2787
    let v2789 := plt 1 v2788 v104
    let v2790 := psel (pmask v2789) v104 v2788
    let v2791 := smx 29 1 v2591 v2591
    let v2792 := srdF 1 v2791
    let v2793 := Nat.sub (Nat.add v2792 v2792) OFFr
    let v2794 := Nat.sub (Nat.add v33 OFFr) v2793
    let v2795 := smx 29 1 v2596 v2596
    let v2796 := srdC 1 v2795
    let v2797 := Nat.sub (Nat.add v2796 v2796) OFFr
    let v2798 := Nat.sub (Nat.add v33 OFFr) v2797
    let v2799 := plt 1 v2798 v104
    let v2800 := psel (pmask v2799) v104 v2798
    let v2801 := smx 29 1 v2595 v2595
    let v2802 := srdF 1 v2801
    let v2803 := Nat.sub (Nat.add v2802 v2802) OFFr
    let v2804 := Nat.sub (Nat.add v33 OFFr) v2803
    let v2805 := plt 1 v2790 v9
    let v2807 := plt 1 v9 v2794
    let v2808 := Nat.sub 1 v2807
    let v2809 := Nat.land v2805 v2808
    let v2810 := Nat.land v2805 v2807
    let v2811 := plt 1 v2800 v9
    let v2813 := plt 1 v9 v2804
    let v2814 := Nat.sub 1 v2813
    let v2815 := Nat.land v2811 v2814
    let v2816 := Nat.land v2811 v2813
    let v2817 := Nat.land v2810 v2816
    let v2825 := Nat.land v2809 v2816
    let v2826 := Nat.lor v2815 v2825
    let v2827 := psel (pmask v2826) v2790 v2794
    let v2828 := Nat.land v2810 v2815
    let v2829 := Nat.lor v2809 v2828
    let v2830 := psel (pmask v2829) v2800 v2804
    let v2833 := smx 30 1 v2830 v2827
    let v2834 := srdC 1 v2833
    let v2837 := smx 30 1 v2800 v2790
    let v2838 := srdC 1 v2837
    let v2841 := plt 1 v2834 v2838
    let v2842 := psel (pmask v2841) v2838 v2834
    let v2844 := psel (pmask v2817) v2842 v2834
    let v2845 := Nat.sub (Nat.add v863 OFFr) v2844
    let v2847 := Nat.sub (Nat.add v1035 OFFr) v2791
    let v2848 := psqrt 1 v2847
    let v2849 := Nat.sub (Nat.add v114 v2848) OFFr
    let v2850 := smx 29 1 v2848 v2591
    let v2851 := srdF 1 v2850
    let v2852 := Nat.sub (Nat.add v2851 v2851) OFFr
    let v2853 := smx 29 1 v2849 v2591
    let v2854 := srdC 1 v2853
    let v2855 := Nat.sub (Nat.add v2854 v2854) OFFr
    let v2856 := plt 1 v2855 v33
    let v2857 := psel (pmask v2856) v2855 v33
    let v2858 := Nat.sub (Nat.add v1035 OFFr) v2785
    let v2859 := psqrt 1 v2858
    let v2860 := Nat.sub (Nat.add v114 v2859) OFFr
    let v2861 := smx 29 1 v2859 v2592
    let v2862 := srdF 1 v2861
    let v2863 := Nat.sub (Nat.add v2862 v2862) OFFr
    let v2864 := smx 29 1 v2860 v2592
    let v2865 := srdC 1 v2864
    let v2866 := Nat.sub (Nat.add v2865 v2865) OFFr
    let v2867 := plt 1 v2866 v33
    let v2868 := psel (pmask v2867) v2866 v33
    let v2869 := plt 1 v2852 v2863
    let v2870 := psel (pmask v2869) v2852 v2863
    let v2871 := plt 1 v2857 v2868
    let v2872 := psel (pmask v2871) v2868 v2857
    let v2873 := plt 1 v1062 v2791
    let v2874 := Nat.sub 1 v2873
    let v2875 := plt 1 v2785 v1062
    let v2876 := Nat.sub 1 v2875
    let v2877 := Nat.land v2874 v2876
    let v2878 := psel (pmask v2877) v33 v2872
    let v2879 := Nat.sub (Nat.add v1035 OFFr) v2801
    let v2880 := psqrt 1 v2879
    let v2881 := Nat.sub (Nat.add v114 v2880) OFFr
    let v2882 := smx 29 1 v2880 v2595
    let v2883 := srdF 1 v2882
    let v2884 := Nat.sub (Nat.add v2883 v2883) OFFr
    let v2885 := smx 29 1 v2881 v2595
    let v2886 := srdC 1 v2885
    let v2887 := Nat.sub (Nat.add v2886 v2886) OFFr
    let v2888 := plt 1 v2887 v33
    let v2889 := psel (pmask v2888) v2887 v33
    let v2890 := Nat.sub (Nat.add v1035 OFFr) v2795
    let v2891 := psqrt 1 v2890
    let v2892 := Nat.sub (Nat.add v114 v2891) OFFr
    let v2893 := smx 29 1 v2891 v2596
    let v2894 := srdF 1 v2893
    let v2895 := Nat.sub (Nat.add v2894 v2894) OFFr
    let v2896 := smx 29 1 v2892 v2596
    let v2897 := srdC 1 v2896
    let v2898 := Nat.sub (Nat.add v2897 v2897) OFFr
    let v2899 := plt 1 v2898 v33
    let v2900 := psel (pmask v2899) v2898 v33
    let v2901 := plt 1 v2884 v2895
    let v2902 := psel (pmask v2901) v2884 v2895
    let v2903 := plt 1 v2889 v2900
    let v2904 := psel (pmask v2903) v2900 v2889
    let v2905 := plt 1 v1062 v2801
    let v2906 := Nat.sub 1 v2905
    let v2907 := plt 1 v2795 v1062
    let v2908 := Nat.sub 1 v2907
    let v2909 := Nat.land v2906 v2908
    let v2910 := psel (pmask v2909) v33 v2904
    let v2911 := plt 1 v2870 v9
    let v2912 := Nat.sub 1 v2911
    let v2913 := plt 1 v9 v2878
    let v2914 := Nat.sub 1 v2913
    let v2915 := Nat.land v2911 v2914
    let v2916 := Nat.land v2911 v2913
    let v2917 := plt 1 v2902 v9
    let v2919 := plt 1 v9 v2910
    let v2920 := Nat.sub 1 v2919
    let v2921 := Nat.land v2917 v2920
    let v2922 := Nat.land v2917 v2919
    let v2923 := Nat.land v2916 v2922
    let v2924 := Nat.land v2912 v2922
    let v2925 := Nat.lor v2921 v2924
    let v2926 := psel (pmask v2925) v2878 v2870
    let v2927 := Nat.sub 1 v2921
    let v2928 := Nat.land v2916 v2927
    let v2929 := Nat.lor v2915 v2928
    let v2930 := psel (pmask v2929) v2910 v2902
    let v2931 := Nat.land v2915 v2922
    let v2932 := Nat.lor v2921 v2931
    let v2933 := psel (pmask v2932) v2870 v2878
    let v2934 := Nat.land v2916 v2921
    let v2935 := Nat.lor v2915 v2934
    let v2936 := psel (pmask v2935) v2902 v2910
    let v2937 := smx 29 1 v2930 v2926
    let v2938 := srdF 1 v2937
    let v2939 := smx 29 1 v2936 v2933
    let v2940 := srdC 1 v2939
    let v2941 := smx 29 1 v2902 v2878
    let v2942 := srdF 1 v2941
    let v2943 := smx 29 1 v2902 v2870
    let v2944 := srdC 1 v2943
    let v2945 := plt 1 v2938 v2942
    let v2946 := psel (pmask v2945) v2938 v2942
    let v2947 := plt 1 v2940 v2944
    let v2948 := psel (pmask v2947) v2944 v2940
    let v2949 := psel (pmask v2923) v2946 v2938
    let v2950 := psel (pmask v2923) v2948 v2940
    let v2951 := plt 1 v9 v2949
    let v2952 := Nat.sub 1 v2951
    let v2953 := plt 1 v2845 v9
    let v2954 := psel (pmask v2953) v2949 v2950
    let v2957 := plt 1 v2954 v2845
    let v2958 := Nat.land v2951 v2957
    let v2959 := Nat.sub (Nat.add v9 OFFr) v2954
    let v2960 := plt 1 v2959 v2845
    let v2961 := Nat.sub 1 v2960
    let v2962 := Nat.lor v2952 v2961
    let v2963 := psel (pmask v2962) v104 v2845
    let v2964 := psel (pmask v2962) v33 v2954
    let v2965 := Nat.lor v2776 v2958
    let v2983 := hxa 1 H3 0
    let v2984 := plt 1 v2983 v20
    let v2985 := Nat.sub 1 v2984
    let t2983 := sc28u 1 v2983
    let v2987 := Nat.sub (Nat.add v31 t2983.2) OFFr
    let v2988 := plt 1 v2987 v33
    let v2989 := psel (pmask v2988) v2987 v33
    let v2990 := sshl 1 v2963
    let v2991 := smx 29 1 v2989 v2964
    let v2992 := plt 1 v2990 v2991
    let v2993 := Nat.sub 1 v2992
    let v2994 := Nat.lor v2985 v2993
    let v2995 := psel (pmask v2994) v2983 v20
    let v2997 := psel (pmask v2492) v2995 v20
    let v2998 := Nat.land v2492 v2965
    let v3000 := psel (pmask v2776) v20 v9
    let v3002 := psel (pmask v2998) v3000 v2997
    let v3004 := Nat.sub (Nat.add v426 v3002) OFFr
    let v3006 := Nat.sub (Nat.add v781 v3004) OFFr
    let v3009 := plt 1 v6 v3006
    let v3010 := Nat.sub 1 v3009
    let v3011 := Nat.land v23 v47
    let v3012 := Nat.land v101 v3011
    let v3013 := Nat.land v23 v3012
    let v3014 := Nat.land v119 v3013
    let v3015 := Nat.land v119 v3014
    let v3016 := Nat.land v279 v3015
    let v3017 := Nat.land v279 v3016
    let v3018 := Nat.land v23 v3017
    let v3019 := Nat.land v432 v3018
    let v3020 := Nat.land v480 v3019
    let v3021 := Nat.land v23 v3020
    let v3022 := Nat.land v483 v3021
    let v3023 := Nat.land v483 v3022
    let v3024 := Nat.land v634 v3023
    let v3025 := Nat.land v634 v3024
    let v3026 := Nat.land v23 v3025
    let v3027 := Nat.land v788 v3026
    let v3028 := Nat.land v836 v3027
    let v3029 := Nat.land v1374 v3028
    let v3030 := Nat.land v1834 v3029
    let v3031 := Nat.land v1843 v3030
    let v3032 := Nat.land v1844 v3031
    let v3033 := Nat.land v1876 v3032
    let v3034 := Nat.land v1876 v3033
    let v3035 := Nat.land v1915 v3034
    let v3036 := Nat.land v1950 v3035
    let v3037 := Nat.land v1951 v3036
    let v3038 := Nat.land v1983 v3037
    let v3039 := Nat.land v1983 v3038
    let v3040 := Nat.land v2022 v3039
    let v3041 := Nat.land v23 v3040
    let v3042 := Nat.land v2077 v3041
    let v3043 := Nat.land v2124 v3042
    let v3044 := Nat.land v23 v3043
    let v3045 := Nat.land v2128 v3044
    let v3046 := Nat.land v2128 v3045
    let v3047 := Nat.land v279 v3046
    let v3048 := Nat.land v279 v3047
    let v3049 := Nat.land v23 v3048
    let v3050 := Nat.land v2283 v3049
    let v3051 := Nat.land v2330 v3050
    let v3052 := Nat.land v23 v3051
    let v3053 := Nat.land v2334 v3052
    let v3054 := Nat.land v2334 v3053
    let v3055 := Nat.land v634 v3054
    let v3056 := Nat.land v634 v3055
    let v3057 := Nat.land v23 v3056
    let v3058 := Nat.land v788 v3057
    let v3059 := Nat.land v836 v3058
    let v3060 := Nat.land v3010 v3059
    ∀ (P : Prop), ((sv v2785 = sv v2592 * sv v2592) → (sv v2786 = -((-sv v2785) / 2 ^ 28)) → (sv v2787 = sv v2786 + sv v2786) → (sv v2788 = sv v33 - sv v2787) → ((v2789 = 1 ↔ sv v2788 < sv v104)) → (v2790 = if v2789 = 1 then v104 else v2788) → (sv v2791 = sv v2591 * sv v2591) → (sv v2792 = sv v2791 / 2 ^ 28) → (sv v2793 = sv v2792 + sv v2792) → (sv v2794 = sv v33 - sv v2793) → (sv v2795 = sv v2596 * sv v2596) → (sv v2796 = -((-sv v2795) / 2 ^ 28)) → (sv v2797 = sv v2796 + sv v2796) → (sv v2798 = sv v33 - sv v2797) → ((v2799 = 1 ↔ sv v2798 < sv v104)) → (v2800 = if v2799 = 1 then v104 else v2798) → (sv v2801 = sv v2595 * sv v2595) → (sv v2802 = sv v2801 / 2 ^ 28) → (sv v2803 = sv v2802 + sv v2802) → (sv v2804 = sv v33 - sv v2803) → ((v2805 = 1 ↔ sv v2790 < sv v9)) → ((v2807 = 1 ↔ sv v9 < sv v2794)) → ((v2808 = 1 ↔ ¬v2807 = 1)) → ((v2809 = 1 ↔ v2805 = 1 ∧ v2808 = 1)) → ((v2810 = 1 ↔ v2805 = 1 ∧ v2807 = 1)) → ((v2811 = 1 ↔ sv v2800 < sv v9)) → ((v2813 = 1 ↔ sv v9 < sv v2804)) → ((v2814 = 1 ↔ ¬v2813 = 1)) → ((v2815 = 1 ↔ v2811 = 1 ∧ v2814 = 1)) → ((v2816 = 1 ↔ v2811 = 1 ∧ v2813 = 1)) → ((v2817 = 1 ↔ v2810 = 1 ∧ v2816 = 1)) → ((v2825 = 1 ↔ v2809 = 1 ∧ v2816 = 1)) → ((v2826 = 1 ↔ v2815 = 1 ∨ v2825 = 1)) → (v2827 = if v2826 = 1 then v2790 else v2794) → ((v2828 = 1 ↔ v2810 = 1 ∧ v2815 = 1)) → ((v2829 = 1 ↔ v2809 = 1 ∨ v2828 = 1)) → (v2830 = if v2829 = 1 then v2800 else v2804) → (sv v2833 = sv v2830 * sv v2827) → (sv v2834 = -((-sv v2833) / 2 ^ 28)) → (sv v2837 = sv v2800 * sv v2790) → (sv v2838 = -((-sv v2837) / 2 ^ 28)) → ((v2841 = 1 ↔ sv v2834 < sv v2838)) → (v2842 = if v2841 = 1 then v2838 else v2834) → (v2844 = if v2817 = 1 then v2842 else v2834) → (sv v2845 = sv v863 - sv v2844) → (sv v2847 = sv v1035 - sv v2791) → (sv v2848 = ((Nat.sqrt (v2847 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2849 = sv v114 + sv v2848) → (sv v2850 = sv v2848 * sv v2591) → (sv v2851 = sv v2850 / 2 ^ 28) → (sv v2852 = sv v2851 + sv v2851) → (sv v2853 = sv v2849 * sv v2591) → (sv v2854 = -((-sv v2853) / 2 ^ 28)) → (sv v2855 = sv v2854 + sv v2854) → ((v2856 = 1 ↔ sv v2855 < sv v33)) → (v2857 = if v2856 = 1 then v2855 else v33) → (sv v2858 = sv v1035 - sv v2785) → (sv v2859 = ((Nat.sqrt (v2858 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2860 = sv v114 + sv v2859) → (sv v2861 = sv v2859 * sv v2592) → (sv v2862 = sv v2861 / 2 ^ 28) → (sv v2863 = sv v2862 + sv v2862) → (sv v2864 = sv v2860 * sv v2592) → (sv v2865 = -((-sv v2864) / 2 ^ 28)) → (sv v2866 = sv v2865 + sv v2865) → ((v2867 = 1 ↔ sv v2866 < sv v33)) → (v2868 = if v2867 = 1 then v2866 else v33) → ((v2869 = 1 ↔ sv v2852 < sv v2863)) → (v2870 = if v2869 = 1 then v2852 else v2863) → ((v2871 = 1 ↔ sv v2857 < sv v2868)) → (v2872 = if v2871 = 1 then v2868 else v2857) → ((v2873 = 1 ↔ sv v1062 < sv v2791)) → ((v2874 = 1 ↔ ¬v2873 = 1)) → ((v2875 = 1 ↔ sv v2785 < sv v1062)) → ((v2876 = 1 ↔ ¬v2875 = 1)) → ((v2877 = 1 ↔ v2874 = 1 ∧ v2876 = 1)) → (v2878 = if v2877 = 1 then v33 else v2872) → (sv v2879 = sv v1035 - sv v2801) → (sv v2880 = ((Nat.sqrt (v2879 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2881 = sv v114 + sv v2880) → (sv v2882 = sv v2880 * sv v2595) → (sv v2883 = sv v2882 / 2 ^ 28) → (sv v2884 = sv v2883 + sv v2883) → (sv v2885 = sv v2881 * sv v2595) → (sv v2886 = -((-sv v2885) / 2 ^ 28)) → (sv v2887 = sv v2886 + sv v2886) → ((v2888 = 1 ↔ sv v2887 < sv v33)) → (v2889 = if v2888 = 1 then v2887 else v33) → (sv v2890 = sv v1035 - sv v2795) → (sv v2891 = ((Nat.sqrt (v2890 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2892 = sv v114 + sv v2891) → (sv v2893 = sv v2891 * sv v2596) → (sv v2894 = sv v2893 / 2 ^ 28) → (sv v2895 = sv v2894 + sv v2894) → (sv v2896 = sv v2892 * sv v2596) → (sv v2897 = -((-sv v2896) / 2 ^ 28)) → (sv v2898 = sv v2897 + sv v2897) → ((v2899 = 1 ↔ sv v2898 < sv v33)) → (v2900 = if v2899 = 1 then v2898 else v33) → ((v2901 = 1 ↔ sv v2884 < sv v2895)) → (v2902 = if v2901 = 1 then v2884 else v2895) → ((v2903 = 1 ↔ sv v2889 < sv v2900)) → (v2904 = if v2903 = 1 then v2900 else v2889) → ((v2905 = 1 ↔ sv v1062 < sv v2801)) → ((v2906 = 1 ↔ ¬v2905 = 1)) → ((v2907 = 1 ↔ sv v2795 < sv v1062)) → ((v2908 = 1 ↔ ¬v2907 = 1)) → ((v2909 = 1 ↔ v2906 = 1 ∧ v2908 = 1)) → (v2910 = if v2909 = 1 then v33 else v2904) → ((v2911 = 1 ↔ sv v2870 < sv v9)) → ((v2912 = 1 ↔ ¬v2911 = 1)) → ((v2913 = 1 ↔ sv v9 < sv v2878)) → ((v2914 = 1 ↔ ¬v2913 = 1)) → ((v2915 = 1 ↔ v2911 = 1 ∧ v2914 = 1)) → ((v2916 = 1 ↔ v2911 = 1 ∧ v2913 = 1)) → ((v2917 = 1 ↔ sv v2902 < sv v9)) → ((v2919 = 1 ↔ sv v9 < sv v2910)) → ((v2920 = 1 ↔ ¬v2919 = 1)) → ((v2921 = 1 ↔ v2917 = 1 ∧ v2920 = 1)) → ((v2922 = 1 ↔ v2917 = 1 ∧ v2919 = 1)) → ((v2923 = 1 ↔ v2916 = 1 ∧ v2922 = 1)) → ((v2924 = 1 ↔ v2912 = 1 ∧ v2922 = 1)) → ((v2925 = 1 ↔ v2921 = 1 ∨ v2924 = 1)) → (v2926 = if v2925 = 1 then v2878 else v2870) → ((v2927 = 1 ↔ ¬v2921 = 1)) → ((v2928 = 1 ↔ v2916 = 1 ∧ v2927 = 1)) → ((v2929 = 1 ↔ v2915 = 1 ∨ v2928 = 1)) → (v2930 = if v2929 = 1 then v2910 else v2902) → ((v2931 = 1 ↔ v2915 = 1 ∧ v2922 = 1)) → ((v2932 = 1 ↔ v2921 = 1 ∨ v2931 = 1)) → (v2933 = if v2932 = 1 then v2870 else v2878) → ((v2934 = 1 ↔ v2916 = 1 ∧ v2921 = 1)) → ((v2935 = 1 ↔ v2915 = 1 ∨ v2934 = 1)) → (v2936 = if v2935 = 1 then v2902 else v2910) → (sv v2937 = sv v2930 * sv v2926) → (sv v2938 = sv v2937 / 2 ^ 28) → (sv v2939 = sv v2936 * sv v2933) → (sv v2940 = -((-sv v2939) / 2 ^ 28)) → (sv v2941 = sv v2902 * sv v2878) → (sv v2942 = sv v2941 / 2 ^ 28) → (sv v2943 = sv v2902 * sv v2870) → (sv v2944 = -((-sv v2943) / 2 ^ 28)) → ((v2945 = 1 ↔ sv v2938 < sv v2942)) → (v2946 = if v2945 = 1 then v2938 else v2942) → ((v2947 = 1 ↔ sv v2940 < sv v2944)) → (v2948 = if v2947 = 1 then v2944 else v2940) → (v2949 = if v2923 = 1 then v2946 else v2938) → (v2950 = if v2923 = 1 then v2948 else v2940) → ((v2951 = 1 ↔ sv v9 < sv v2949)) → ((v2952 = 1 ↔ ¬v2951 = 1)) → ((v2953 = 1 ↔ sv v2845 < sv v9)) → (v2954 = if v2953 = 1 then v2949 else v2950) → ((v2957 = 1 ↔ sv v2954 < sv v2845)) → ((v2958 = 1 ↔ v2951 = 1 ∧ v2957 = 1)) → (sv v2959 = sv v9 - sv v2954) → ((v2960 = 1 ↔ sv v2959 < sv v2845)) → ((v2961 = 1 ↔ ¬v2960 = 1)) → ((v2962 = 1 ↔ v2952 = 1 ∨ v2961 = 1)) → (v2963 = if v2962 = 1 then v104 else v2845) → (v2964 = if v2962 = 1 then v33 else v2954) → ((v2965 = 1 ↔ v2776 = 1 ∨ v2958 = 1)) → (sv v2983 = ((H3 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ)) → ((v2984 = 1 ↔ sv v2983 < sv v20)) → ((v2985 = 1 ↔ ¬v2984 = 1)) → (sv t2983.2 = (sc28pS (scArg v2983)).2) → (sv v2987 = sv v31 + sv t2983.2) → ((v2988 = 1 ↔ sv v2987 < sv v33)) → (v2989 = if v2988 = 1 then v2987 else v33) → (sv v2990 = sv v2963 * 2 ^ 28) → (sv v2991 = sv v2989 * sv v2964) → ((v2992 = 1 ↔ sv v2990 < sv v2991)) → ((v2993 = 1 ↔ ¬v2992 = 1)) → ((v2994 = 1 ↔ v2985 = 1 ∨ v2993 = 1)) → (v2995 = if v2994 = 1 then v2983 else v20) → (v2997 = if v2492 = 1 then v2995 else v20) → ((v2998 = 1 ↔ v2492 = 1 ∧ v2965 = 1)) → (v3000 = if v2776 = 1 then v20 else v9) → (v3002 = if v2998 = 1 then v3000 else v2997) → (sv v3004 = sv v426 + sv v3002) → (sv v3006 = sv v781 + sv v3004) → ((v3009 = 1 ↔ sv v6 < sv v3006)) → ((v3010 = 1 ↔ ¬v3009 = 1)) → ((v3011 = 1 ↔ v23 = 1 ∧ v47 = 1)) → ((v3012 = 1 ↔ v101 = 1 ∧ v3011 = 1)) → ((v3013 = 1 ↔ v23 = 1 ∧ v3012 = 1)) → ((v3014 = 1 ↔ v119 = 1 ∧ v3013 = 1)) → ((v3015 = 1 ↔ v119 = 1 ∧ v3014 = 1)) → ((v3016 = 1 ↔ v279 = 1 ∧ v3015 = 1)) → ((v3017 = 1 ↔ v279 = 1 ∧ v3016 = 1)) → ((v3018 = 1 ↔ v23 = 1 ∧ v3017 = 1)) → ((v3019 = 1 ↔ v432 = 1 ∧ v3018 = 1)) → ((v3020 = 1 ↔ v480 = 1 ∧ v3019 = 1)) → ((v3021 = 1 ↔ v23 = 1 ∧ v3020 = 1)) → ((v3022 = 1 ↔ v483 = 1 ∧ v3021 = 1)) → ((v3023 = 1 ↔ v483 = 1 ∧ v3022 = 1)) → ((v3024 = 1 ↔ v634 = 1 ∧ v3023 = 1)) → ((v3025 = 1 ↔ v634 = 1 ∧ v3024 = 1)) → ((v3026 = 1 ↔ v23 = 1 ∧ v3025 = 1)) → ((v3027 = 1 ↔ v788 = 1 ∧ v3026 = 1)) → ((v3028 = 1 ↔ v836 = 1 ∧ v3027 = 1)) → ((v3029 = 1 ↔ v1374 = 1 ∧ v3028 = 1)) → ((v3030 = 1 ↔ v1834 = 1 ∧ v3029 = 1)) → ((v3031 = 1 ↔ v1843 = 1 ∧ v3030 = 1)) → ((v3032 = 1 ↔ v1844 = 1 ∧ v3031 = 1)) → ((v3033 = 1 ↔ v1876 = 1 ∧ v3032 = 1)) → ((v3034 = 1 ↔ v1876 = 1 ∧ v3033 = 1)) → ((v3035 = 1 ↔ v1915 = 1 ∧ v3034 = 1)) → ((v3036 = 1 ↔ v1950 = 1 ∧ v3035 = 1)) → ((v3037 = 1 ↔ v1951 = 1 ∧ v3036 = 1)) → ((v3038 = 1 ↔ v1983 = 1 ∧ v3037 = 1)) → ((v3039 = 1 ↔ v1983 = 1 ∧ v3038 = 1)) → ((v3040 = 1 ↔ v2022 = 1 ∧ v3039 = 1)) → ((v3041 = 1 ↔ v23 = 1 ∧ v3040 = 1)) → ((v3042 = 1 ↔ v2077 = 1 ∧ v3041 = 1)) → ((v3043 = 1 ↔ v2124 = 1 ∧ v3042 = 1)) → ((v3044 = 1 ↔ v23 = 1 ∧ v3043 = 1)) → ((v3045 = 1 ↔ v2128 = 1 ∧ v3044 = 1)) → ((v3046 = 1 ↔ v2128 = 1 ∧ v3045 = 1)) → ((v3047 = 1 ↔ v279 = 1 ∧ v3046 = 1)) → ((v3048 = 1 ↔ v279 = 1 ∧ v3047 = 1)) → ((v3049 = 1 ↔ v23 = 1 ∧ v3048 = 1)) → ((v3050 = 1 ↔ v2283 = 1 ∧ v3049 = 1)) → ((v3051 = 1 ↔ v2330 = 1 ∧ v3050 = 1)) → ((v3052 = 1 ↔ v23 = 1 ∧ v3051 = 1)) → ((v3053 = 1 ↔ v2334 = 1 ∧ v3052 = 1)) → ((v3054 = 1 ↔ v2334 = 1 ∧ v3053 = 1)) → ((v3055 = 1 ↔ v634 = 1 ∧ v3054 = 1)) → ((v3056 = 1 ↔ v634 = 1 ∧ v3055 = 1)) → ((v3057 = 1 ↔ v23 = 1 ∧ v3056 = 1)) → ((v3058 = 1 ↔ v788 = 1 ∧ v3057 = 1)) → ((v3059 = 1 ↔ v836 = 1 ∧ v3058 = 1)) → ((v3060 = 1 ↔ v3010 = 1 ∧ v3059 = 1)) → P) → P := by
  intro OFFr v6 v9 v20 v31 v33 v104 v114 v1035 v1062 v2785 v2786 v2787 v2788 v2789 v2790 v2791 v2792 v2793 v2794 v2795 v2796 v2797 v2798 v2799 v2800 v2801 v2802 v2803 v2804 v2805 v2807 v2808 v2809 v2810 v2811 v2813 v2814 v2815 v2816 v2817 v2825 v2826 v2827 v2828 v2829 v2830 v2833 v2834 v2837 v2838 v2841 v2842 v2844 v2845 v2847 v2848 v2849 v2850 v2851 v2852 v2853 v2854 v2855 v2856 v2857 v2858 v2859 v2860 v2861 v2862 v2863 v2864 v2865 v2866 v2867 v2868 v2869 v2870 v2871 v2872 v2873 v2874 v2875 v2876 v2877 v2878 v2879 v2880 v2881 v2882 v2883 v2884 v2885 v2886 v2887 v2888 v2889 v2890 v2891 v2892 v2893 v2894 v2895 v2896 v2897 v2898 v2899 v2900 v2901 v2902 v2903 v2904 v2905 v2906 v2907 v2908 v2909 v2910 v2911 v2912 v2913 v2914 v2915 v2916 v2917 v2919 v2920 v2921 v2922 v2923 v2924 v2925 v2926 v2927 v2928 v2929 v2930 v2931 v2932 v2933 v2934 v2935 v2936 v2937 v2938 v2939 v2940 v2941 v2942 v2943 v2944 v2945 v2946 v2947 v2948 v2949 v2950 v2951 v2952 v2953 v2954 v2957 v2958 v2959 v2960 v2961 v2962 v2963 v2964 v2965 v2983 v2984 v2985 t2983 v2987 v2988 v2989 v2990 v2991 v2992 v2993 v2994 v2995 v2997 v2998 v3000 v3002 v3004 v3006 v3009 v3010 v3011 v3012 v3013 v3014 v3015 v3016 v3017 v3018 v3019 v3020 v3021 v3022 v3023 v3024 v3025 v3026 v3027 v3028 v3029 v3030 v3031 v3032 v3033 v3034 v3035 v3036 v3037 v3038 v3039 v3040 v3041 v3042 v3043 v3044 v3045 v3046 v3047 v3048 v3049 v3050 v3051 v3052 v3053 v3054 v3055 v3056 v3057 v3058 v3059 v3060
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v6 : R 1 0 4611686018427387904 4611686087146864624 v6 v6 := (r1_ix hb_F3 0 (of_decide_eq_true rfl))
  have h_v9 : R 1 0 4611686018427387904 4611686018427387904 v9 v9 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v20 : R 1 0 4611686019270702761 4611686019270702761 v20 v20 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have h_v31 : R 1 0 4611686018427387908 4611686018427387908 v31 v31 := (r_c hl 4611686018427387908 (of_decide_eq_true rfl))
  have h_v33 : R 1 0 4611686018695823360 4611686018695823360 v33 v33 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have h_v104 : R 1 0 4611686018158952448 4611686018158952448 v104 v104 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have h_v114 : R 1 0 4611686018427387905 4611686018427387905 v114 v114 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have h_v1035 : R 1 0 4683743612465315840 4683743612465315840 v1035 v1035 := (r_c hl 4683743612465315840 (of_decide_eq_true rfl))
  have h_v1062 : R 1 0 4647714815446351872 4647714815446351872 v1062 v1062 := (r_c hl 4647714815446351872 (of_decide_eq_true rfl))
  have h_v2785 : R 1 0 4611686018427387904 4683743620518379745 v2785 v2785 := (r_smx_sq hl 29 h_v2592 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2785 : sv v2785 = sv v2592 * sv v2592 := e_smx_sq 29 h_v2592 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2786 : R 1 0 4611686018427387904 4611686018695823391 v2786 v2786 := (r_srdC hl h_v2785 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v2786 : sv v2786 = -((-sv v2785) / 2 ^ 28) := e_srdC h_v2785 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v2787 : R 1 0 4611686018427387904 4611686018964258878 v2787 v2787 := (r_sub hl (r_add hl h_v2786 h_v2786 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2787 : sv v2787 = sv v2786 + sv v2786 := e_add h_v2786 h_v2786 (of_decide_eq_true rfl)
  have h_v2788 : R 1 0 4611686018158952386 4611686018695823360 v2788 v2788 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v2787 (of_decide_eq_true rfl))
  have e_v2788 : sv v2788 = sv v33 - sv v2787 := e_sub h_v33 h_v2787 (of_decide_eq_true rfl)
  have h_v2789 : R 1 0 0 1 v2789 v2789 := (r_plt hl h_v2788 h_v104 (of_decide_eq_true rfl))
  have e_v2789 : (v2789 = 1 ↔ sv v2788 < sv v104) := e_plt h_v2788 h_v104 (of_decide_eq_true rfl)
  have h_v2790 : R 1 0 4611686018158952386 4611686018695823360 v2790 v2790 := (r_psel hl h_v2789 h_v104 h_v2788 (of_decide_eq_true rfl))
  have e_v2790 : v2790 = if v2789 = 1 then v104 else v2788 := e_psel h_v2789 h_v104 h_v2788 (of_decide_eq_true rfl)
  have h_v2791 : R 1 0 4611686018427387904 4683743620518379745 v2791 v2791 := (r_smx_sq hl 29 h_v2591 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2791 : sv v2791 = sv v2591 * sv v2591 := e_smx_sq 29 h_v2591 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2792 : R 1 0 4611686018427387904 4611686018695823390 v2792 v2792 := (r_srdF hl h_v2791 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  clear h_v2786 h_v2787 h_v2788 h_v2789
  have e_v2792 : sv v2792 = sv v2791 / 2 ^ 28 := e_srdF h_v2791 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v2793 : R 1 0 4611686018427387904 4611686018964258876 v2793 v2793 := (r_sub hl (r_add hl h_v2792 h_v2792 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2793 : sv v2793 = sv v2792 + sv v2792 := e_add h_v2792 h_v2792 (of_decide_eq_true rfl)
  have h_v2794 : R 1 0 4611686018158952388 4611686018695823360 v2794 v2794 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v2793 (of_decide_eq_true rfl))
  have e_v2794 : sv v2794 = sv v33 - sv v2793 := e_sub h_v33 h_v2793 (of_decide_eq_true rfl)
  have h_v2795 : R 1 0 4611686018427387904 4683743620518379745 v2795 v2795 := (r_smx_sq hl 29 h_v2596 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2795 : sv v2795 = sv v2596 * sv v2596 := e_smx_sq 29 h_v2596 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2796 : R 1 0 4611686018427387904 4611686018695823391 v2796 v2796 := (r_srdC hl h_v2795 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v2796 : sv v2796 = -((-sv v2795) / 2 ^ 28) := e_srdC h_v2795 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v2797 : R 1 0 4611686018427387904 4611686018964258878 v2797 v2797 := (r_sub hl (r_add hl h_v2796 h_v2796 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2797 : sv v2797 = sv v2796 + sv v2796 := e_add h_v2796 h_v2796 (of_decide_eq_true rfl)
  have h_v2798 : R 1 0 4611686018158952386 4611686018695823360 v2798 v2798 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v2797 (of_decide_eq_true rfl))
  have e_v2798 : sv v2798 = sv v33 - sv v2797 := e_sub h_v33 h_v2797 (of_decide_eq_true rfl)
  have h_v2799 : R 1 0 0 1 v2799 v2799 := (r_plt hl h_v2798 h_v104 (of_decide_eq_true rfl))
  have e_v2799 : (v2799 = 1 ↔ sv v2798 < sv v104) := e_plt h_v2798 h_v104 (of_decide_eq_true rfl)
  have h_v2800 : R 1 0 4611686018158952386 4611686018695823360 v2800 v2800 := (r_psel hl h_v2799 h_v104 h_v2798 (of_decide_eq_true rfl))
  have e_v2800 : v2800 = if v2799 = 1 then v104 else v2798 := e_psel h_v2799 h_v104 h_v2798 (of_decide_eq_true rfl)
  have h_v2801 : R 1 0 4611686018427387904 4683743620518379745 v2801 v2801 := (r_smx_sq hl 29 h_v2595 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2801 : sv v2801 = sv v2595 * sv v2595 := e_smx_sq 29 h_v2595 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2802 : R 1 0 4611686018427387904 4611686018695823390 v2802 v2802 := (r_srdF hl h_v2801 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v2802 : sv v2802 = sv v2801 / 2 ^ 28 := e_srdF h_v2801 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v2803 : R 1 0 4611686018427387904 4611686018964258876 v2803 v2803 := (r_sub hl (r_add hl h_v2802 h_v2802 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2803 : sv v2803 = sv v2802 + sv v2802 := e_add h_v2802 h_v2802 (of_decide_eq_true rfl)
  have h_v2804 : R 1 0 4611686018158952388 4611686018695823360 v2804 v2804 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v2803 (of_decide_eq_true rfl))
  have e_v2804 : sv v2804 = sv v33 - sv v2803 := e_sub h_v33 h_v2803 (of_decide_eq_true rfl)
  clear h_v2792 h_v2793 h_v2796 h_v2797 h_v2798 h_v2799 h_v2802 h_v2803
  have h_v2805 : R 1 0 0 1 v2805 v2805 := (r_plt hl h_v2790 h_v9 (of_decide_eq_true rfl))
  have e_v2805 : (v2805 = 1 ↔ sv v2790 < sv v9) := e_plt h_v2790 h_v9 (of_decide_eq_true rfl)
  have h_v2807 : R 1 0 0 1 v2807 v2807 := (r_plt hl h_v9 h_v2794 (of_decide_eq_true rfl))
  have e_v2807 : (v2807 = 1 ↔ sv v9 < sv v2794) := e_plt h_v9 h_v2794 (of_decide_eq_true rfl)
  have h_v2808 : R 1 0 0 1 v2808 v2808 := (r_sub hl (r_O hl) h_v2807 (of_decide_eq_true rfl))
  have e_v2808 : (v2808 = 1 ↔ ¬v2807 = 1) := e_not h_v2807 (of_decide_eq_true rfl)
  have h_v2809 : R 1 0 0 1 v2809 v2809 := (r_land hl h_v2805 h_v2808 (of_decide_eq_true rfl))
  have e_v2809 : (v2809 = 1 ↔ v2805 = 1 ∧ v2808 = 1) := e_land h_v2805 h_v2808 (of_decide_eq_true rfl)
  have h_v2810 : R 1 0 0 1 v2810 v2810 := (r_land hl h_v2805 h_v2807 (of_decide_eq_true rfl))
  have e_v2810 : (v2810 = 1 ↔ v2805 = 1 ∧ v2807 = 1) := e_land h_v2805 h_v2807 (of_decide_eq_true rfl)
  have h_v2811 : R 1 0 0 1 v2811 v2811 := (r_plt hl h_v2800 h_v9 (of_decide_eq_true rfl))
  have e_v2811 : (v2811 = 1 ↔ sv v2800 < sv v9) := e_plt h_v2800 h_v9 (of_decide_eq_true rfl)
  have h_v2813 : R 1 0 0 1 v2813 v2813 := (r_plt hl h_v9 h_v2804 (of_decide_eq_true rfl))
  have e_v2813 : (v2813 = 1 ↔ sv v9 < sv v2804) := e_plt h_v9 h_v2804 (of_decide_eq_true rfl)
  have h_v2814 : R 1 0 0 1 v2814 v2814 := (r_sub hl (r_O hl) h_v2813 (of_decide_eq_true rfl))
  have e_v2814 : (v2814 = 1 ↔ ¬v2813 = 1) := e_not h_v2813 (of_decide_eq_true rfl)
  have h_v2815 : R 1 0 0 1 v2815 v2815 := (r_land hl h_v2811 h_v2814 (of_decide_eq_true rfl))
  have e_v2815 : (v2815 = 1 ↔ v2811 = 1 ∧ v2814 = 1) := e_land h_v2811 h_v2814 (of_decide_eq_true rfl)
  have h_v2816 : R 1 0 0 1 v2816 v2816 := (r_land hl h_v2811 h_v2813 (of_decide_eq_true rfl))
  have e_v2816 : (v2816 = 1 ↔ v2811 = 1 ∧ v2813 = 1) := e_land h_v2811 h_v2813 (of_decide_eq_true rfl)
  have h_v2817 : R 1 0 0 1 v2817 v2817 := (r_land hl h_v2810 h_v2816 (of_decide_eq_true rfl))
  have e_v2817 : (v2817 = 1 ↔ v2810 = 1 ∧ v2816 = 1) := e_land h_v2810 h_v2816 (of_decide_eq_true rfl)
  have h_v2825 : R 1 0 0 1 v2825 v2825 := (r_land hl h_v2809 h_v2816 (of_decide_eq_true rfl))
  have e_v2825 : (v2825 = 1 ↔ v2809 = 1 ∧ v2816 = 1) := e_land h_v2809 h_v2816 (of_decide_eq_true rfl)
  have h_v2826 : R 1 0 0 1 v2826 v2826 := (r_lor hl h_v2815 h_v2825 (of_decide_eq_true rfl))
  clear h_v2805 h_v2807 h_v2808 h_v2811 h_v2813 h_v2814 h_v2816
  have e_v2826 : (v2826 = 1 ↔ v2815 = 1 ∨ v2825 = 1) := e_lor h_v2815 h_v2825 (of_decide_eq_true rfl)
  have h_v2827 : R 1 0 4611686018158952386 4611686018695823360 v2827 v2827 := (r_psel hl h_v2826 h_v2790 h_v2794 (of_decide_eq_true rfl))
  have e_v2827 : v2827 = if v2826 = 1 then v2790 else v2794 := e_psel h_v2826 h_v2790 h_v2794 (of_decide_eq_true rfl)
  have h_v2828 : R 1 0 0 1 v2828 v2828 := (r_land hl h_v2810 h_v2815 (of_decide_eq_true rfl))
  have e_v2828 : (v2828 = 1 ↔ v2810 = 1 ∧ v2815 = 1) := e_land h_v2810 h_v2815 (of_decide_eq_true rfl)
  have h_v2829 : R 1 0 0 1 v2829 v2829 := (r_lor hl h_v2809 h_v2828 (of_decide_eq_true rfl))
  have e_v2829 : (v2829 = 1 ↔ v2809 = 1 ∨ v2828 = 1) := e_lor h_v2809 h_v2828 (of_decide_eq_true rfl)
  have h_v2830 : R 1 0 4611686018158952386 4611686018695823360 v2830 v2830 := (r_psel hl h_v2829 h_v2800 h_v2804 (of_decide_eq_true rfl))
  have e_v2830 : v2830 = if v2829 = 1 then v2800 else v2804 := e_psel h_v2829 h_v2800 h_v2804 (of_decide_eq_true rfl)
  have h_v2833 : R 1 0 4539628407746461696 4683743645751316228 v2833 v2833 := (r_smx hl 30 h_v2830 h_v2827 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v2833 : sv v2833 = sv v2830 * sv v2827 := e_smx 30 h_v2830 h_v2827 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v2834 : R 1 0 4611686018158952386 4611686018695823485 v2834 v2834 := (r_srdC hl h_v2833 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v2834 : sv v2834 = -((-sv v2833) / 2 ^ 28) := e_srdC h_v2833 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v2837 : R 1 0 4539628407746461696 4683743645751316228 v2837 v2837 := (r_smx hl 30 h_v2800 h_v2790 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v2837 : sv v2837 = sv v2800 * sv v2790 := e_smx 30 h_v2800 h_v2790 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v2838 : R 1 0 4611686018158952386 4611686018695823485 v2838 v2838 := (r_srdC hl h_v2837 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v2838 : sv v2838 = -((-sv v2837) / 2 ^ 28) := e_srdC h_v2837 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v2841 : R 1 0 0 1 v2841 v2841 := (r_plt hl h_v2834 h_v2838 (of_decide_eq_true rfl))
  have e_v2841 : (v2841 = 1 ↔ sv v2834 < sv v2838) := e_plt h_v2834 h_v2838 (of_decide_eq_true rfl)
  have h_v2842 : R 1 0 4611686018158952386 4611686018695823485 v2842 v2842 := (r_psel hl h_v2841 h_v2838 h_v2834 (of_decide_eq_true rfl))
  have e_v2842 : v2842 = if v2841 = 1 then v2838 else v2834 := e_psel h_v2841 h_v2838 h_v2834 (of_decide_eq_true rfl)
  have h_v2844 : R 1 0 4611686018158952386 4611686018695823485 v2844 v2844 := (r_psel hl h_v2817 h_v2842 h_v2834 (of_decide_eq_true rfl))
  have e_v2844 : v2844 = if v2817 = 1 then v2842 else v2834 := e_psel h_v2817 h_v2842 h_v2834 (of_decide_eq_true rfl)
  have h_v2845 : R 1 0 4611686017890516805 4611686018964258878 v2845 v2845 := (r_sub hl (r_add hl h_v863 h_OFFr (of_decide_eq_true rfl)) h_v2844 (of_decide_eq_true rfl))
  have e_v2845 : sv v2845 = sv v863 - sv v2844 := e_sub h_v863 h_v2844 (of_decide_eq_true rfl)
  clear h_v2790 h_v2794 h_v2800 h_v2804 h_v2809 h_v2810 h_v2815 h_v2817 h_v2825 h_v2826 h_v2827 h_v2828 h_v2829 h_v2830 h_v2833 h_v2834 h_v2837 h_v2838 h_v2841 h_v2842 h_v2844
  have h_v2847 : R 1 0 4611686010374323999 4683743612465315840 v2847 v2847 := (r_sub hl (r_add hl h_v1035 h_OFFr (of_decide_eq_true rfl)) h_v2791 (of_decide_eq_true rfl))
  have e_v2847 : sv v2847 = sv v1035 - sv v2791 := e_sub h_v1035 h_v2791 (of_decide_eq_true rfl)
  have h_v2848 : R 1 0 4611686018427387904 4611686018695823360 v2848 v2848 := (r_psqrt hl h_v2847 (of_decide_eq_true rfl))
  have e_v2848 : sv v2848 = ((Nat.sqrt (v2847 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2847 (of_decide_eq_true rfl)
  have h_v2849 : R 1 0 4611686018427387905 4611686018695823361 v2849 v2849 := (r_sub hl (r_add hl h_v114 h_v2848 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2849 : sv v2849 = sv v114 + sv v2848 := e_add h_v114 h_v2848 (of_decide_eq_true rfl)
  have pb_v2848_v2591 : PB 1 v2848 v2591 36028797018963968 := pb_sqrt hl h_v2591 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v2850 : R 1 0 4611686017085210624 4647714815446351872 v2850 v2850 := (r_smx_pb hl 29 h_v2848 h_v2591 pb_v2848_v2591 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2850 : sv v2850 = sv v2848 * sv v2591 := e_smx_pb 29 h_v2848 h_v2591 pb_v2848_v2591 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2851 : R 1 0 4611686018427387899 4611686018561605632 v2851 v2851 := (r_srdF hl h_v2850 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2851 : sv v2851 = sv v2850 / 2 ^ 28 := e_srdF h_v2850 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2852 : R 1 0 4611686018427387894 4611686018695823360 v2852 v2852 := (r_sub hl (r_add hl h_v2851 h_v2851 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2852 : sv v2852 = sv v2851 + sv v2851 := e_add h_v2851 h_v2851 (of_decide_eq_true rfl)
  have pb_v2849_v2591 : PB 1 v2849 v2591 36028797287399439 := pb_sqrt1 hl h_v2591 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2853 : R 1 0 4611686017085210619 4647714815714787343 v2853 v2853 := (r_smx_pb hl 29 h_v2849 h_v2591 pb_v2849_v2591 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2853 : sv v2853 = sv v2849 * sv v2591 := e_smx_pb 29 h_v2849 h_v2591 pb_v2849_v2591 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2854 : R 1 0 4611686018427387899 4611686018561605634 v2854 v2854 := (r_srdC hl h_v2853 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2854 : sv v2854 = -((-sv v2853) / 2 ^ 28) := e_srdC h_v2853 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2855 : R 1 0 4611686018427387894 4611686018695823364 v2855 v2855 := (r_sub hl (r_add hl h_v2854 h_v2854 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2855 : sv v2855 = sv v2854 + sv v2854 := e_add h_v2854 h_v2854 (of_decide_eq_true rfl)
  have h_v2856 : R 1 0 0 1 v2856 v2856 := (r_plt hl h_v2855 h_v33 (of_decide_eq_true rfl))
  have e_v2856 : (v2856 = 1 ↔ sv v2855 < sv v33) := e_plt h_v2855 h_v33 (of_decide_eq_true rfl)
  have h_v2857 : R 1 0 4611686018427387894 4611686018695823364 v2857 v2857 := (r_psel hl h_v2856 h_v2855 h_v33 (of_decide_eq_true rfl))
  have e_v2857 : v2857 = if v2856 = 1 then v2855 else v33 := e_psel h_v2856 h_v2855 h_v33 (of_decide_eq_true rfl)
  have h_v2858 : R 1 0 4611686010374323999 4683743612465315840 v2858 v2858 := (r_sub hl (r_add hl h_v1035 h_OFFr (of_decide_eq_true rfl)) h_v2785 (of_decide_eq_true rfl))
  clear h_v2847 h_v2848 h_v2849 pb_v2848_v2591 h_v2850 h_v2851 pb_v2849_v2591 h_v2853 h_v2854 h_v2855 h_v2856
  have e_v2858 : sv v2858 = sv v1035 - sv v2785 := e_sub h_v1035 h_v2785 (of_decide_eq_true rfl)
  have h_v2859 : R 1 0 4611686018427387904 4611686018695823360 v2859 v2859 := (r_psqrt hl h_v2858 (of_decide_eq_true rfl))
  have e_v2859 : sv v2859 = ((Nat.sqrt (v2858 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2858 (of_decide_eq_true rfl)
  have h_v2860 : R 1 0 4611686018427387905 4611686018695823361 v2860 v2860 := (r_sub hl (r_add hl h_v114 h_v2859 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2860 : sv v2860 = sv v114 + sv v2859 := e_add h_v114 h_v2859 (of_decide_eq_true rfl)
  have pb_v2859_v2592 : PB 1 v2859 v2592 36028797018963968 := pb_sqrt hl h_v2592 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v2861 : R 1 0 4611686017085210624 4647714815446351872 v2861 v2861 := (r_smx_pb hl 29 h_v2859 h_v2592 pb_v2859_v2592 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2861 : sv v2861 = sv v2859 * sv v2592 := e_smx_pb 29 h_v2859 h_v2592 pb_v2859_v2592 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2862 : R 1 0 4611686018427387899 4611686018561605632 v2862 v2862 := (r_srdF hl h_v2861 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2862 : sv v2862 = sv v2861 / 2 ^ 28 := e_srdF h_v2861 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2863 : R 1 0 4611686018427387894 4611686018695823360 v2863 v2863 := (r_sub hl (r_add hl h_v2862 h_v2862 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2863 : sv v2863 = sv v2862 + sv v2862 := e_add h_v2862 h_v2862 (of_decide_eq_true rfl)
  have pb_v2860_v2592 : PB 1 v2860 v2592 36028797287399439 := pb_sqrt1 hl h_v2592 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2864 : R 1 0 4611686017085210619 4647714815714787343 v2864 v2864 := (r_smx_pb hl 29 h_v2860 h_v2592 pb_v2860_v2592 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2864 : sv v2864 = sv v2860 * sv v2592 := e_smx_pb 29 h_v2860 h_v2592 pb_v2860_v2592 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2865 : R 1 0 4611686018427387899 4611686018561605634 v2865 v2865 := (r_srdC hl h_v2864 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2865 : sv v2865 = -((-sv v2864) / 2 ^ 28) := e_srdC h_v2864 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2866 : R 1 0 4611686018427387894 4611686018695823364 v2866 v2866 := (r_sub hl (r_add hl h_v2865 h_v2865 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2866 : sv v2866 = sv v2865 + sv v2865 := e_add h_v2865 h_v2865 (of_decide_eq_true rfl)
  have h_v2867 : R 1 0 0 1 v2867 v2867 := (r_plt hl h_v2866 h_v33 (of_decide_eq_true rfl))
  have e_v2867 : (v2867 = 1 ↔ sv v2866 < sv v33) := e_plt h_v2866 h_v33 (of_decide_eq_true rfl)
  have h_v2868 : R 1 0 4611686018427387894 4611686018695823364 v2868 v2868 := (r_psel hl h_v2867 h_v2866 h_v33 (of_decide_eq_true rfl))
  have e_v2868 : v2868 = if v2867 = 1 then v2866 else v33 := e_psel h_v2867 h_v2866 h_v33 (of_decide_eq_true rfl)
  have h_v2869 : R 1 0 0 1 v2869 v2869 := (r_plt hl h_v2852 h_v2863 (of_decide_eq_true rfl))
  have e_v2869 : (v2869 = 1 ↔ sv v2852 < sv v2863) := e_plt h_v2852 h_v2863 (of_decide_eq_true rfl)
  clear h_v2858 h_v2859 h_v2860 pb_v2859_v2592 h_v2861 h_v2862 pb_v2860_v2592 h_v2864 h_v2865 h_v2866 h_v2867
  have h_v2870 : R 1 0 4611686018427387894 4611686018695823360 v2870 v2870 := (r_psel hl h_v2869 h_v2852 h_v2863 (of_decide_eq_true rfl))
  have e_v2870 : v2870 = if v2869 = 1 then v2852 else v2863 := e_psel h_v2869 h_v2852 h_v2863 (of_decide_eq_true rfl)
  have h_v2871 : R 1 0 0 1 v2871 v2871 := (r_plt hl h_v2857 h_v2868 (of_decide_eq_true rfl))
  have e_v2871 : (v2871 = 1 ↔ sv v2857 < sv v2868) := e_plt h_v2857 h_v2868 (of_decide_eq_true rfl)
  have h_v2872 : R 1 0 4611686018427387894 4611686018695823364 v2872 v2872 := (r_psel hl h_v2871 h_v2868 h_v2857 (of_decide_eq_true rfl))
  have e_v2872 : v2872 = if v2871 = 1 then v2868 else v2857 := e_psel h_v2871 h_v2868 h_v2857 (of_decide_eq_true rfl)
  have h_v2873 : R 1 0 0 1 v2873 v2873 := (r_plt hl h_v1062 h_v2791 (of_decide_eq_true rfl))
  have e_v2873 : (v2873 = 1 ↔ sv v1062 < sv v2791) := e_plt h_v1062 h_v2791 (of_decide_eq_true rfl)
  have h_v2874 : R 1 0 0 1 v2874 v2874 := (r_sub hl (r_O hl) h_v2873 (of_decide_eq_true rfl))
  have e_v2874 : (v2874 = 1 ↔ ¬v2873 = 1) := e_not h_v2873 (of_decide_eq_true rfl)
  have h_v2875 : R 1 0 0 1 v2875 v2875 := (r_plt hl h_v2785 h_v1062 (of_decide_eq_true rfl))
  have e_v2875 : (v2875 = 1 ↔ sv v2785 < sv v1062) := e_plt h_v2785 h_v1062 (of_decide_eq_true rfl)
  have h_v2876 : R 1 0 0 1 v2876 v2876 := (r_sub hl (r_O hl) h_v2875 (of_decide_eq_true rfl))
  have e_v2876 : (v2876 = 1 ↔ ¬v2875 = 1) := e_not h_v2875 (of_decide_eq_true rfl)
  have h_v2877 : R 1 0 0 1 v2877 v2877 := (r_land hl h_v2874 h_v2876 (of_decide_eq_true rfl))
  have e_v2877 : (v2877 = 1 ↔ v2874 = 1 ∧ v2876 = 1) := e_land h_v2874 h_v2876 (of_decide_eq_true rfl)
  have h_v2878 : R 1 0 4611686018427387894 4611686018695823364 v2878 v2878 := (r_psel hl h_v2877 h_v33 h_v2872 (of_decide_eq_true rfl))
  have e_v2878 : v2878 = if v2877 = 1 then v33 else v2872 := e_psel h_v2877 h_v33 h_v2872 (of_decide_eq_true rfl)
  have h_v2879 : R 1 0 4611686010374323999 4683743612465315840 v2879 v2879 := (r_sub hl (r_add hl h_v1035 h_OFFr (of_decide_eq_true rfl)) h_v2801 (of_decide_eq_true rfl))
  have e_v2879 : sv v2879 = sv v1035 - sv v2801 := e_sub h_v1035 h_v2801 (of_decide_eq_true rfl)
  have h_v2880 : R 1 0 4611686018427387904 4611686018695823360 v2880 v2880 := (r_psqrt hl h_v2879 (of_decide_eq_true rfl))
  have e_v2880 : sv v2880 = ((Nat.sqrt (v2879 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2879 (of_decide_eq_true rfl)
  have h_v2881 : R 1 0 4611686018427387905 4611686018695823361 v2881 v2881 := (r_sub hl (r_add hl h_v114 h_v2880 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2881 : sv v2881 = sv v114 + sv v2880 := e_add h_v114 h_v2880 (of_decide_eq_true rfl)
  have pb_v2880_v2595 : PB 1 v2880 v2595 36028797018963968 := pb_sqrt hl h_v2595 29 36028797018963968 (of_decide_eq_true rfl)
  clear h_v2785 h_v2791 h_v2852 h_v2857 h_v2863 h_v2868 h_v2869 h_v2871 h_v2872 h_v2873 h_v2874 h_v2875 h_v2876 h_v2877 h_v2879
  have h_v2882 : R 1 0 4611686017085210624 4647714815446351872 v2882 v2882 := (r_smx_pb hl 29 h_v2880 h_v2595 pb_v2880_v2595 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2882 : sv v2882 = sv v2880 * sv v2595 := e_smx_pb 29 h_v2880 h_v2595 pb_v2880_v2595 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2883 : R 1 0 4611686018427387899 4611686018561605632 v2883 v2883 := (r_srdF hl h_v2882 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2883 : sv v2883 = sv v2882 / 2 ^ 28 := e_srdF h_v2882 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2884 : R 1 0 4611686018427387894 4611686018695823360 v2884 v2884 := (r_sub hl (r_add hl h_v2883 h_v2883 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2884 : sv v2884 = sv v2883 + sv v2883 := e_add h_v2883 h_v2883 (of_decide_eq_true rfl)
  have pb_v2881_v2595 : PB 1 v2881 v2595 36028797287399439 := pb_sqrt1 hl h_v2595 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2885 : R 1 0 4611686017085210619 4647714815714787343 v2885 v2885 := (r_smx_pb hl 29 h_v2881 h_v2595 pb_v2881_v2595 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2885 : sv v2885 = sv v2881 * sv v2595 := e_smx_pb 29 h_v2881 h_v2595 pb_v2881_v2595 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2886 : R 1 0 4611686018427387899 4611686018561605634 v2886 v2886 := (r_srdC hl h_v2885 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2886 : sv v2886 = -((-sv v2885) / 2 ^ 28) := e_srdC h_v2885 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2887 : R 1 0 4611686018427387894 4611686018695823364 v2887 v2887 := (r_sub hl (r_add hl h_v2886 h_v2886 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2887 : sv v2887 = sv v2886 + sv v2886 := e_add h_v2886 h_v2886 (of_decide_eq_true rfl)
  have h_v2888 : R 1 0 0 1 v2888 v2888 := (r_plt hl h_v2887 h_v33 (of_decide_eq_true rfl))
  have e_v2888 : (v2888 = 1 ↔ sv v2887 < sv v33) := e_plt h_v2887 h_v33 (of_decide_eq_true rfl)
  have h_v2889 : R 1 0 4611686018427387894 4611686018695823364 v2889 v2889 := (r_psel hl h_v2888 h_v2887 h_v33 (of_decide_eq_true rfl))
  have e_v2889 : v2889 = if v2888 = 1 then v2887 else v33 := e_psel h_v2888 h_v2887 h_v33 (of_decide_eq_true rfl)
  have h_v2890 : R 1 0 4611686010374323999 4683743612465315840 v2890 v2890 := (r_sub hl (r_add hl h_v1035 h_OFFr (of_decide_eq_true rfl)) h_v2795 (of_decide_eq_true rfl))
  have e_v2890 : sv v2890 = sv v1035 - sv v2795 := e_sub h_v1035 h_v2795 (of_decide_eq_true rfl)
  have h_v2891 : R 1 0 4611686018427387904 4611686018695823360 v2891 v2891 := (r_psqrt hl h_v2890 (of_decide_eq_true rfl))
  have e_v2891 : sv v2891 = ((Nat.sqrt (v2890 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2890 (of_decide_eq_true rfl)
  have h_v2892 : R 1 0 4611686018427387905 4611686018695823361 v2892 v2892 := (r_sub hl (r_add hl h_v114 h_v2891 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2892 : sv v2892 = sv v114 + sv v2891 := e_add h_v114 h_v2891 (of_decide_eq_true rfl)
  have pb_v2891_v2596 : PB 1 v2891 v2596 36028797018963968 := pb_sqrt hl h_v2596 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v2893 : R 1 0 4611686017085210624 4647714815446351872 v2893 v2893 := (r_smx_pb hl 29 h_v2891 h_v2596 pb_v2891_v2596 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  clear h_v114 h_v1035 h_v2880 h_v2881 pb_v2880_v2595 h_v2882 h_v2883 pb_v2881_v2595 h_v2885 h_v2886 h_v2887 h_v2888 h_v2890
  have e_v2893 : sv v2893 = sv v2891 * sv v2596 := e_smx_pb 29 h_v2891 h_v2596 pb_v2891_v2596 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2894 : R 1 0 4611686018427387899 4611686018561605632 v2894 v2894 := (r_srdF hl h_v2893 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2894 : sv v2894 = sv v2893 / 2 ^ 28 := e_srdF h_v2893 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2895 : R 1 0 4611686018427387894 4611686018695823360 v2895 v2895 := (r_sub hl (r_add hl h_v2894 h_v2894 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2895 : sv v2895 = sv v2894 + sv v2894 := e_add h_v2894 h_v2894 (of_decide_eq_true rfl)
  have pb_v2892_v2596 : PB 1 v2892 v2596 36028797287399439 := pb_sqrt1 hl h_v2596 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2896 : R 1 0 4611686017085210619 4647714815714787343 v2896 v2896 := (r_smx_pb hl 29 h_v2892 h_v2596 pb_v2892_v2596 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2896 : sv v2896 = sv v2892 * sv v2596 := e_smx_pb 29 h_v2892 h_v2596 pb_v2892_v2596 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2897 : R 1 0 4611686018427387899 4611686018561605634 v2897 v2897 := (r_srdC hl h_v2896 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2897 : sv v2897 = -((-sv v2896) / 2 ^ 28) := e_srdC h_v2896 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2898 : R 1 0 4611686018427387894 4611686018695823364 v2898 v2898 := (r_sub hl (r_add hl h_v2897 h_v2897 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2898 : sv v2898 = sv v2897 + sv v2897 := e_add h_v2897 h_v2897 (of_decide_eq_true rfl)
  have h_v2899 : R 1 0 0 1 v2899 v2899 := (r_plt hl h_v2898 h_v33 (of_decide_eq_true rfl))
  have e_v2899 : (v2899 = 1 ↔ sv v2898 < sv v33) := e_plt h_v2898 h_v33 (of_decide_eq_true rfl)
  have h_v2900 : R 1 0 4611686018427387894 4611686018695823364 v2900 v2900 := (r_psel hl h_v2899 h_v2898 h_v33 (of_decide_eq_true rfl))
  have e_v2900 : v2900 = if v2899 = 1 then v2898 else v33 := e_psel h_v2899 h_v2898 h_v33 (of_decide_eq_true rfl)
  have h_v2901 : R 1 0 0 1 v2901 v2901 := (r_plt hl h_v2884 h_v2895 (of_decide_eq_true rfl))
  have e_v2901 : (v2901 = 1 ↔ sv v2884 < sv v2895) := e_plt h_v2884 h_v2895 (of_decide_eq_true rfl)
  have h_v2902 : R 1 0 4611686018427387894 4611686018695823360 v2902 v2902 := (r_psel hl h_v2901 h_v2884 h_v2895 (of_decide_eq_true rfl))
  have e_v2902 : v2902 = if v2901 = 1 then v2884 else v2895 := e_psel h_v2901 h_v2884 h_v2895 (of_decide_eq_true rfl)
  have h_v2903 : R 1 0 0 1 v2903 v2903 := (r_plt hl h_v2889 h_v2900 (of_decide_eq_true rfl))
  have e_v2903 : (v2903 = 1 ↔ sv v2889 < sv v2900) := e_plt h_v2889 h_v2900 (of_decide_eq_true rfl)
  have h_v2904 : R 1 0 4611686018427387894 4611686018695823364 v2904 v2904 := (r_psel hl h_v2903 h_v2900 h_v2889 (of_decide_eq_true rfl))
  have e_v2904 : v2904 = if v2903 = 1 then v2900 else v2889 := e_psel h_v2903 h_v2900 h_v2889 (of_decide_eq_true rfl)
  have h_v2905 : R 1 0 0 1 v2905 v2905 := (r_plt hl h_v1062 h_v2801 (of_decide_eq_true rfl))
  clear h_v2884 h_v2889 h_v2891 h_v2892 pb_v2891_v2596 h_v2893 h_v2894 h_v2895 pb_v2892_v2596 h_v2896 h_v2897 h_v2898 h_v2899 h_v2900 h_v2901 h_v2903
  have e_v2905 : (v2905 = 1 ↔ sv v1062 < sv v2801) := e_plt h_v1062 h_v2801 (of_decide_eq_true rfl)
  have h_v2906 : R 1 0 0 1 v2906 v2906 := (r_sub hl (r_O hl) h_v2905 (of_decide_eq_true rfl))
  have e_v2906 : (v2906 = 1 ↔ ¬v2905 = 1) := e_not h_v2905 (of_decide_eq_true rfl)
  have h_v2907 : R 1 0 0 1 v2907 v2907 := (r_plt hl h_v2795 h_v1062 (of_decide_eq_true rfl))
  have e_v2907 : (v2907 = 1 ↔ sv v2795 < sv v1062) := e_plt h_v2795 h_v1062 (of_decide_eq_true rfl)
  have h_v2908 : R 1 0 0 1 v2908 v2908 := (r_sub hl (r_O hl) h_v2907 (of_decide_eq_true rfl))
  have e_v2908 : (v2908 = 1 ↔ ¬v2907 = 1) := e_not h_v2907 (of_decide_eq_true rfl)
  have h_v2909 : R 1 0 0 1 v2909 v2909 := (r_land hl h_v2906 h_v2908 (of_decide_eq_true rfl))
  have e_v2909 : (v2909 = 1 ↔ v2906 = 1 ∧ v2908 = 1) := e_land h_v2906 h_v2908 (of_decide_eq_true rfl)
  have h_v2910 : R 1 0 4611686018427387894 4611686018695823364 v2910 v2910 := (r_psel hl h_v2909 h_v33 h_v2904 (of_decide_eq_true rfl))
  have e_v2910 : v2910 = if v2909 = 1 then v33 else v2904 := e_psel h_v2909 h_v33 h_v2904 (of_decide_eq_true rfl)
  have h_v2911 : R 1 0 0 1 v2911 v2911 := (r_plt hl h_v2870 h_v9 (of_decide_eq_true rfl))
  have e_v2911 : (v2911 = 1 ↔ sv v2870 < sv v9) := e_plt h_v2870 h_v9 (of_decide_eq_true rfl)
  have h_v2912 : R 1 0 0 1 v2912 v2912 := (r_sub hl (r_O hl) h_v2911 (of_decide_eq_true rfl))
  have e_v2912 : (v2912 = 1 ↔ ¬v2911 = 1) := e_not h_v2911 (of_decide_eq_true rfl)
  have h_v2913 : R 1 0 0 1 v2913 v2913 := (r_plt hl h_v9 h_v2878 (of_decide_eq_true rfl))
  have e_v2913 : (v2913 = 1 ↔ sv v9 < sv v2878) := e_plt h_v9 h_v2878 (of_decide_eq_true rfl)
  have h_v2914 : R 1 0 0 1 v2914 v2914 := (r_sub hl (r_O hl) h_v2913 (of_decide_eq_true rfl))
  have e_v2914 : (v2914 = 1 ↔ ¬v2913 = 1) := e_not h_v2913 (of_decide_eq_true rfl)
  have h_v2915 : R 1 0 0 1 v2915 v2915 := (r_land hl h_v2911 h_v2914 (of_decide_eq_true rfl))
  have e_v2915 : (v2915 = 1 ↔ v2911 = 1 ∧ v2914 = 1) := e_land h_v2911 h_v2914 (of_decide_eq_true rfl)
  have h_v2916 : R 1 0 0 1 v2916 v2916 := (r_land hl h_v2911 h_v2913 (of_decide_eq_true rfl))
  have e_v2916 : (v2916 = 1 ↔ v2911 = 1 ∧ v2913 = 1) := e_land h_v2911 h_v2913 (of_decide_eq_true rfl)
  have h_v2917 : R 1 0 0 1 v2917 v2917 := (r_plt hl h_v2902 h_v9 (of_decide_eq_true rfl))
  have e_v2917 : (v2917 = 1 ↔ sv v2902 < sv v9) := e_plt h_v2902 h_v9 (of_decide_eq_true rfl)
  clear h_v1062 h_v2795 h_v2801 h_v2904 h_v2905 h_v2906 h_v2907 h_v2908 h_v2909 h_v2911 h_v2913 h_v2914
  have h_v2919 : R 1 0 0 1 v2919 v2919 := (r_plt hl h_v9 h_v2910 (of_decide_eq_true rfl))
  have e_v2919 : (v2919 = 1 ↔ sv v9 < sv v2910) := e_plt h_v9 h_v2910 (of_decide_eq_true rfl)
  have h_v2920 : R 1 0 0 1 v2920 v2920 := (r_sub hl (r_O hl) h_v2919 (of_decide_eq_true rfl))
  have e_v2920 : (v2920 = 1 ↔ ¬v2919 = 1) := e_not h_v2919 (of_decide_eq_true rfl)
  have h_v2921 : R 1 0 0 1 v2921 v2921 := (r_land hl h_v2917 h_v2920 (of_decide_eq_true rfl))
  have e_v2921 : (v2921 = 1 ↔ v2917 = 1 ∧ v2920 = 1) := e_land h_v2917 h_v2920 (of_decide_eq_true rfl)
  have h_v2922 : R 1 0 0 1 v2922 v2922 := (r_land hl h_v2917 h_v2919 (of_decide_eq_true rfl))
  have e_v2922 : (v2922 = 1 ↔ v2917 = 1 ∧ v2919 = 1) := e_land h_v2917 h_v2919 (of_decide_eq_true rfl)
  have h_v2923 : R 1 0 0 1 v2923 v2923 := (r_land hl h_v2916 h_v2922 (of_decide_eq_true rfl))
  have e_v2923 : (v2923 = 1 ↔ v2916 = 1 ∧ v2922 = 1) := e_land h_v2916 h_v2922 (of_decide_eq_true rfl)
  have h_v2924 : R 1 0 0 1 v2924 v2924 := (r_land hl h_v2912 h_v2922 (of_decide_eq_true rfl))
  have e_v2924 : (v2924 = 1 ↔ v2912 = 1 ∧ v2922 = 1) := e_land h_v2912 h_v2922 (of_decide_eq_true rfl)
  have h_v2925 : R 1 0 0 1 v2925 v2925 := (r_lor hl h_v2921 h_v2924 (of_decide_eq_true rfl))
  have e_v2925 : (v2925 = 1 ↔ v2921 = 1 ∨ v2924 = 1) := e_lor h_v2921 h_v2924 (of_decide_eq_true rfl)
  have h_v2926 : R 1 0 4611686018427387894 4611686018695823364 v2926 v2926 := (r_psel hl h_v2925 h_v2878 h_v2870 (of_decide_eq_true rfl))
  have e_v2926 : v2926 = if v2925 = 1 then v2878 else v2870 := e_psel h_v2925 h_v2878 h_v2870 (of_decide_eq_true rfl)
  have h_v2927 : R 1 0 0 1 v2927 v2927 := (r_sub hl (r_O hl) h_v2921 (of_decide_eq_true rfl))
  have e_v2927 : (v2927 = 1 ↔ ¬v2921 = 1) := e_not h_v2921 (of_decide_eq_true rfl)
  have h_v2928 : R 1 0 0 1 v2928 v2928 := (r_land hl h_v2916 h_v2927 (of_decide_eq_true rfl))
  have e_v2928 : (v2928 = 1 ↔ v2916 = 1 ∧ v2927 = 1) := e_land h_v2916 h_v2927 (of_decide_eq_true rfl)
  have h_v2929 : R 1 0 0 1 v2929 v2929 := (r_lor hl h_v2915 h_v2928 (of_decide_eq_true rfl))
  have e_v2929 : (v2929 = 1 ↔ v2915 = 1 ∨ v2928 = 1) := e_lor h_v2915 h_v2928 (of_decide_eq_true rfl)
  have h_v2930 : R 1 0 4611686018427387894 4611686018695823364 v2930 v2930 := (r_psel hl h_v2929 h_v2910 h_v2902 (of_decide_eq_true rfl))
  have e_v2930 : v2930 = if v2929 = 1 then v2910 else v2902 := e_psel h_v2929 h_v2910 h_v2902 (of_decide_eq_true rfl)
  have h_v2931 : R 1 0 0 1 v2931 v2931 := (r_land hl h_v2915 h_v2922 (of_decide_eq_true rfl))
  clear h_v2912 h_v2917 h_v2919 h_v2920 h_v2924 h_v2925 h_v2927 h_v2928 h_v2929
  have e_v2931 : (v2931 = 1 ↔ v2915 = 1 ∧ v2922 = 1) := e_land h_v2915 h_v2922 (of_decide_eq_true rfl)
  have h_v2932 : R 1 0 0 1 v2932 v2932 := (r_lor hl h_v2921 h_v2931 (of_decide_eq_true rfl))
  have e_v2932 : (v2932 = 1 ↔ v2921 = 1 ∨ v2931 = 1) := e_lor h_v2921 h_v2931 (of_decide_eq_true rfl)
  have h_v2933 : R 1 0 4611686018427387894 4611686018695823364 v2933 v2933 := (r_psel hl h_v2932 h_v2870 h_v2878 (of_decide_eq_true rfl))
  have e_v2933 : v2933 = if v2932 = 1 then v2870 else v2878 := e_psel h_v2932 h_v2870 h_v2878 (of_decide_eq_true rfl)
  have h_v2934 : R 1 0 0 1 v2934 v2934 := (r_land hl h_v2916 h_v2921 (of_decide_eq_true rfl))
  have e_v2934 : (v2934 = 1 ↔ v2916 = 1 ∧ v2921 = 1) := e_land h_v2916 h_v2921 (of_decide_eq_true rfl)
  have h_v2935 : R 1 0 0 1 v2935 v2935 := (r_lor hl h_v2915 h_v2934 (of_decide_eq_true rfl))
  have e_v2935 : (v2935 = 1 ↔ v2915 = 1 ∨ v2934 = 1) := e_lor h_v2915 h_v2934 (of_decide_eq_true rfl)
  have h_v2936 : R 1 0 4611686018427387894 4611686018695823364 v2936 v2936 := (r_psel hl h_v2935 h_v2902 h_v2910 (of_decide_eq_true rfl))
  have e_v2936 : v2936 = if v2935 = 1 then v2902 else v2910 := e_psel h_v2935 h_v2902 h_v2910 (of_decide_eq_true rfl)
  have h_v2937 : R 1 0 4611686015743033304 4683743614612799504 v2937 v2937 := (r_smx hl 29 h_v2930 h_v2926 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v2937 : sv v2937 = sv v2930 * sv v2926 := e_smx 29 h_v2930 h_v2926 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v2938 : R 1 0 4611686018427387893 4611686018695823368 v2938 v2938 := (r_srdF hl h_v2937 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v2938 : sv v2938 = sv v2937 / 2 ^ 28 := e_srdF h_v2937 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v2939 : R 1 0 4611686015743033304 4683743614612799504 v2939 v2939 := (r_smx hl 29 h_v2936 h_v2933 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v2939 : sv v2939 = sv v2936 * sv v2933 := e_smx 29 h_v2936 h_v2933 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v2940 : R 1 0 4611686018427387894 4611686018695823369 v2940 v2940 := (r_srdC hl h_v2939 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v2940 : sv v2940 = -((-sv v2939) / 2 ^ 28) := e_srdC h_v2939 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v2941 : R 1 0 4611686015743033304 4683743613539057664 v2941 v2941 := (r_smx hl 29 h_v2902 h_v2878 4611686015743033304 4683743613539057664 (of_decide_eq_true rfl))
  have e_v2941 : sv v2941 = sv v2902 * sv v2878 := e_smx 29 h_v2902 h_v2878 4611686015743033304 4683743613539057664 (of_decide_eq_true rfl)
  have h_v2942 : R 1 0 4611686018427387893 4611686018695823364 v2942 v2942 := (r_srdF hl h_v2941 4611686018427387893 4611686018695823364 (of_decide_eq_true rfl))
  have e_v2942 : sv v2942 = sv v2941 / 2 ^ 28 := e_srdF h_v2941 4611686018427387893 4611686018695823364 (of_decide_eq_true rfl)
  have h_v2943 : R 1 0 4611686015743033344 4683743612465315840 v2943 v2943 := (r_smx hl 29 h_v2902 h_v2870 4611686015743033344 4683743612465315840 (of_decide_eq_true rfl))
  have e_v2943 : sv v2943 = sv v2902 * sv v2870 := e_smx 29 h_v2902 h_v2870 4611686015743033344 4683743612465315840 (of_decide_eq_true rfl)
  clear h_v2870 h_v2878 h_v2902 h_v2910 h_v2915 h_v2916 h_v2921 h_v2922 h_v2926 h_v2930 h_v2931 h_v2932 h_v2933 h_v2934 h_v2935 h_v2936 h_v2937 h_v2939 h_v2941
  have h_v2944 : R 1 0 4611686018427387894 4611686018695823360 v2944 v2944 := (r_srdC hl h_v2943 4611686018427387894 4611686018695823360 (of_decide_eq_true rfl))
  have e_v2944 : sv v2944 = -((-sv v2943) / 2 ^ 28) := e_srdC h_v2943 4611686018427387894 4611686018695823360 (of_decide_eq_true rfl)
  have h_v2945 : R 1 0 0 1 v2945 v2945 := (r_plt hl h_v2938 h_v2942 (of_decide_eq_true rfl))
  have e_v2945 : (v2945 = 1 ↔ sv v2938 < sv v2942) := e_plt h_v2938 h_v2942 (of_decide_eq_true rfl)
  have h_v2946 : R 1 0 4611686018427387893 4611686018695823368 v2946 v2946 := (r_psel hl h_v2945 h_v2938 h_v2942 (of_decide_eq_true rfl))
  have e_v2946 : v2946 = if v2945 = 1 then v2938 else v2942 := e_psel h_v2945 h_v2938 h_v2942 (of_decide_eq_true rfl)
  have h_v2947 : R 1 0 0 1 v2947 v2947 := (r_plt hl h_v2940 h_v2944 (of_decide_eq_true rfl))
  have e_v2947 : (v2947 = 1 ↔ sv v2940 < sv v2944) := e_plt h_v2940 h_v2944 (of_decide_eq_true rfl)
  have h_v2948 : R 1 0 4611686018427387894 4611686018695823369 v2948 v2948 := (r_psel hl h_v2947 h_v2944 h_v2940 (of_decide_eq_true rfl))
  have e_v2948 : v2948 = if v2947 = 1 then v2944 else v2940 := e_psel h_v2947 h_v2944 h_v2940 (of_decide_eq_true rfl)
  have h_v2949 : R 1 0 4611686018427387893 4611686018695823368 v2949 v2949 := (r_psel hl h_v2923 h_v2946 h_v2938 (of_decide_eq_true rfl))
  have e_v2949 : v2949 = if v2923 = 1 then v2946 else v2938 := e_psel h_v2923 h_v2946 h_v2938 (of_decide_eq_true rfl)
  have h_v2950 : R 1 0 4611686018427387894 4611686018695823369 v2950 v2950 := (r_psel hl h_v2923 h_v2948 h_v2940 (of_decide_eq_true rfl))
  have e_v2950 : v2950 = if v2923 = 1 then v2948 else v2940 := e_psel h_v2923 h_v2948 h_v2940 (of_decide_eq_true rfl)
  have h_v2951 : R 1 0 0 1 v2951 v2951 := (r_plt hl h_v9 h_v2949 (of_decide_eq_true rfl))
  have e_v2951 : (v2951 = 1 ↔ sv v9 < sv v2949) := e_plt h_v9 h_v2949 (of_decide_eq_true rfl)
  have h_v2952 : R 1 0 0 1 v2952 v2952 := (r_sub hl (r_O hl) h_v2951 (of_decide_eq_true rfl))
  have e_v2952 : (v2952 = 1 ↔ ¬v2951 = 1) := e_not h_v2951 (of_decide_eq_true rfl)
  have h_v2953 : R 1 0 0 1 v2953 v2953 := (r_plt hl h_v2845 h_v9 (of_decide_eq_true rfl))
  have e_v2953 : (v2953 = 1 ↔ sv v2845 < sv v9) := e_plt h_v2845 h_v9 (of_decide_eq_true rfl)
  have h_v2954 : R 1 0 4611686018427387893 4611686018695823369 v2954 v2954 := (r_psel hl h_v2953 h_v2949 h_v2950 (of_decide_eq_true rfl))
  have e_v2954 : v2954 = if v2953 = 1 then v2949 else v2950 := e_psel h_v2953 h_v2949 h_v2950 (of_decide_eq_true rfl)
  have h_v2957 : R 1 0 0 1 v2957 v2957 := (r_plt hl h_v2954 h_v2845 (of_decide_eq_true rfl))
  have e_v2957 : (v2957 = 1 ↔ sv v2954 < sv v2845) := e_plt h_v2954 h_v2845 (of_decide_eq_true rfl)
  have h_v2958 : R 1 0 0 1 v2958 v2958 := (r_land hl h_v2951 h_v2957 (of_decide_eq_true rfl))
  clear h_v2923 h_v2938 h_v2940 h_v2942 h_v2943 h_v2944 h_v2945 h_v2946 h_v2947 h_v2948 h_v2949 h_v2950 h_v2953
  have e_v2958 : (v2958 = 1 ↔ v2951 = 1 ∧ v2957 = 1) := e_land h_v2951 h_v2957 (of_decide_eq_true rfl)
  have h_v2959 : R 1 0 4611686018158952439 4611686018427387915 v2959 v2959 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v2954 (of_decide_eq_true rfl))
  have e_v2959 : sv v2959 = sv v9 - sv v2954 := e_sub h_v9 h_v2954 (of_decide_eq_true rfl)
  have h_v2960 : R 1 0 0 1 v2960 v2960 := (r_plt hl h_v2959 h_v2845 (of_decide_eq_true rfl))
  have e_v2960 : (v2960 = 1 ↔ sv v2959 < sv v2845) := e_plt h_v2959 h_v2845 (of_decide_eq_true rfl)
  have h_v2961 : R 1 0 0 1 v2961 v2961 := (r_sub hl (r_O hl) h_v2960 (of_decide_eq_true rfl))
  have e_v2961 : (v2961 = 1 ↔ ¬v2960 = 1) := e_not h_v2960 (of_decide_eq_true rfl)
  have h_v2962 : R 1 0 0 1 v2962 v2962 := (r_lor hl h_v2952 h_v2961 (of_decide_eq_true rfl))
  have e_v2962 : (v2962 = 1 ↔ v2952 = 1 ∨ v2961 = 1) := e_lor h_v2952 h_v2961 (of_decide_eq_true rfl)
  have h_v2963 : R 1 0 4611686017890516805 4611686018964258878 v2963 v2963 := (r_psel hl h_v2962 h_v104 h_v2845 (of_decide_eq_true rfl))
  have e_v2963 : v2963 = if v2962 = 1 then v104 else v2845 := e_psel h_v2962 h_v104 h_v2845 (of_decide_eq_true rfl)
  have h_v2964 : R 1 0 4611686018427387893 4611686018695823369 v2964 v2964 := (r_psel hl h_v2962 h_v33 h_v2954 (of_decide_eq_true rfl))
  have e_v2964 : v2964 = if v2962 = 1 then v33 else v2954 := e_psel h_v2962 h_v33 h_v2954 (of_decide_eq_true rfl)
  have h_v2965 : R 1 0 0 1 v2965 v2965 := (r_lor hl h_v2776 h_v2958 (of_decide_eq_true rfl))
  have e_v2965 : (v2965 = 1 ↔ v2776 = 1 ∨ v2958 = 1) := e_lor h_v2776 h_v2958 (of_decide_eq_true rfl)
  have h_v2983 : R 1 0 4611686018427387904 4611686019501129727 v2983 v2983 := (r1_hxa hb_H3 0 (of_decide_eq_true rfl))
  have e_v2983 : sv v2983 = ((H3 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H3 0 (of_decide_eq_true rfl)
  have h_v2984 : R 1 0 0 1 v2984 v2984 := (r_plt hl h_v2983 h_v20 (of_decide_eq_true rfl))
  have e_v2984 : (v2984 = 1 ↔ sv v2983 < sv v20) := e_plt h_v2983 h_v20 (of_decide_eq_true rfl)
  have h_v2985 : R 1 0 0 1 v2985 v2985 := (r_sub hl (r_O hl) h_v2984 (of_decide_eq_true rfl))
  have e_v2985 : (v2985 = 1 ↔ ¬v2984 = 1) := e_not h_v2984 (of_decide_eq_true rfl)
  have h_t2983_1 : R 1 0 4611686018427387904 4611686018695823363 t2983.1 t2983.1 := r_sc1 hl h_v2983 (of_decide_eq_true rfl)
  have h_t2983_2 : R 1 0 4611686018158952445 4611686018695823363 t2983.2 t2983.2 := r_sc2 hl h_v2983 (of_decide_eq_true rfl)
  have e_t2983_1 : sv t2983.1 = (sc28pS (scArg v2983)).1 := e_sc1 h_v2983 (of_decide_eq_true rfl)
  have e_t2983_2 : sv t2983.2 = (sc28pS (scArg v2983)).2 := e_sc2 h_v2983 (of_decide_eq_true rfl)
  clear h_v104 h_v2845 h_v2951 h_v2952 h_v2954 h_v2957 h_v2958 h_v2959 h_v2960 h_v2961 h_v2962 h_v2984 h_t2983_1 e_t2983_1
  have h_v2987 : R 1 0 4611686018158952449 4611686018695823367 v2987 v2987 := (r_sub hl (r_add hl h_v31 h_t2983_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2987 : sv v2987 = sv v31 + sv t2983.2 := e_add h_v31 h_t2983_2 (of_decide_eq_true rfl)
  have h_v2988 : R 1 0 0 1 v2988 v2988 := (r_plt hl h_v2987 h_v33 (of_decide_eq_true rfl))
  have e_v2988 : (v2988 = 1 ↔ sv v2987 < sv v33) := e_plt h_v2987 h_v33 (of_decide_eq_true rfl)
  have h_v2989 : R 1 0 4611686018158952449 4611686018695823367 v2989 v2989 := (r_psel hl h_v2988 h_v2987 h_v33 (of_decide_eq_true rfl))
  have e_v2989 : v2989 = if v2988 = 1 then v2987 else v33 := e_psel h_v2988 h_v2987 h_v33 (of_decide_eq_true rfl)
  have h_v2990 : R 1 0 4467570780154101760 4755801223146242048 v2990 v2990 := (r_sshl hl h_v2963 4467570780154101760 4755801223146242048 (of_decide_eq_true rfl))
  have e_v2990 : sv v2990 = sv v2963 * 2 ^ 28 := e_sshl h_v2963 4467570780154101760 4755801223146242048 (of_decide_eq_true rfl)
  have h_v2991 : R 1 0 4539628422241976329 4683743616760283199 v2991 v2991 := (r_smx hl 29 h_v2989 h_v2964 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl))
  have e_v2991 : sv v2991 = sv v2989 * sv v2964 := e_smx 29 h_v2989 h_v2964 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl)
  have h_v2992 : R 1 0 0 1 v2992 v2992 := (r_plt hl h_v2990 h_v2991 (of_decide_eq_true rfl))
  have e_v2992 : (v2992 = 1 ↔ sv v2990 < sv v2991) := e_plt h_v2990 h_v2991 (of_decide_eq_true rfl)
  have h_v2993 : R 1 0 0 1 v2993 v2993 := (r_sub hl (r_O hl) h_v2992 (of_decide_eq_true rfl))
  have e_v2993 : (v2993 = 1 ↔ ¬v2992 = 1) := e_not h_v2992 (of_decide_eq_true rfl)
  have h_v2994 : R 1 0 0 1 v2994 v2994 := (r_lor hl h_v2985 h_v2993 (of_decide_eq_true rfl))
  have e_v2994 : (v2994 = 1 ↔ v2985 = 1 ∨ v2993 = 1) := e_lor h_v2985 h_v2993 (of_decide_eq_true rfl)
  have h_v2995 : R 1 0 4611686018427387904 4611686019501129727 v2995 v2995 := (r_psel hl h_v2994 h_v2983 h_v20 (of_decide_eq_true rfl))
  have e_v2995 : v2995 = if v2994 = 1 then v2983 else v20 := e_psel h_v2994 h_v2983 h_v20 (of_decide_eq_true rfl)
  have h_v2997 : R 1 0 4611686018427387904 4611686019501129727 v2997 v2997 := (r_psel hl h_v2492 h_v2995 h_v20 (of_decide_eq_true rfl))
  have e_v2997 : v2997 = if v2492 = 1 then v2995 else v20 := e_psel h_v2492 h_v2995 h_v20 (of_decide_eq_true rfl)
  have h_v2998 : R 1 0 0 1 v2998 v2998 := (r_land hl h_v2492 h_v2965 (of_decide_eq_true rfl))
  have e_v2998 : (v2998 = 1 ↔ v2492 = 1 ∧ v2965 = 1) := e_land h_v2492 h_v2965 (of_decide_eq_true rfl)
  have h_v3000 : R 1 0 4611686018427387904 4611686019270702761 v3000 v3000 := (r_psel hl h_v2776 h_v20 h_v9 (of_decide_eq_true rfl))
  have e_v3000 : v3000 = if v2776 = 1 then v20 else v9 := e_psel h_v2776 h_v20 h_v9 (of_decide_eq_true rfl)
  have h_v3002 : R 1 0 4611686018427387904 4611686019501129727 v3002 v3002 := (r_psel hl h_v2998 h_v3000 h_v2997 (of_decide_eq_true rfl))
  clear h_v9 h_v20 h_v31 h_v33 h_v2963 h_v2964 h_v2965 h_v2983 h_v2985 h_t2983_2 h_v2987 h_v2988 h_v2989 h_v2990 h_v2991 h_v2992 h_v2993 h_v2994 h_v2995
  have e_v3002 : v3002 = if v2998 = 1 then v3000 else v2997 := e_psel h_v2998 h_v3000 h_v2997 (of_decide_eq_true rfl)
  have h_v3004 : R 1 0 4611686017353646081 4611686020574871550 v3004 v3004 := (r_sub hl (r_add hl h_v426 h_v3002 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v3004 : sv v3004 = sv v426 + sv v3002 := e_add h_v426 h_v3002 (of_decide_eq_true rfl)
  have h_v3006 : R 1 0 4611686016279904258 4611686021648613373 v3006 v3006 := (r_sub hl (r_add hl h_v781 h_v3004 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v3006 : sv v3006 = sv v781 + sv v3004 := e_add h_v781 h_v3004 (of_decide_eq_true rfl)
  have h_v3009 : R 1 0 0 1 v3009 v3009 := (r_plt hl h_v6 h_v3006 (of_decide_eq_true rfl))
  have e_v3009 : (v3009 = 1 ↔ sv v6 < sv v3006) := e_plt h_v6 h_v3006 (of_decide_eq_true rfl)
  have h_v3010 : R 1 0 0 1 v3010 v3010 := (r_sub hl (r_O hl) h_v3009 (of_decide_eq_true rfl))
  have e_v3010 : (v3010 = 1 ↔ ¬v3009 = 1) := e_not h_v3009 (of_decide_eq_true rfl)
  have h_v3011 : R 1 0 0 1 v3011 v3011 := (r_land hl h_v23 h_v47 (of_decide_eq_true rfl))
  have e_v3011 : (v3011 = 1 ↔ v23 = 1 ∧ v47 = 1) := e_land h_v23 h_v47 (of_decide_eq_true rfl)
  have h_v3012 : R 1 0 0 1 v3012 v3012 := (r_land hl h_v101 h_v3011 (of_decide_eq_true rfl))
  have e_v3012 : (v3012 = 1 ↔ v101 = 1 ∧ v3011 = 1) := e_land h_v101 h_v3011 (of_decide_eq_true rfl)
  have h_v3013 : R 1 0 0 1 v3013 v3013 := (r_land hl h_v23 h_v3012 (of_decide_eq_true rfl))
  have e_v3013 : (v3013 = 1 ↔ v23 = 1 ∧ v3012 = 1) := e_land h_v23 h_v3012 (of_decide_eq_true rfl)
  have h_v3014 : R 1 0 0 1 v3014 v3014 := (r_land hl h_v119 h_v3013 (of_decide_eq_true rfl))
  have e_v3014 : (v3014 = 1 ↔ v119 = 1 ∧ v3013 = 1) := e_land h_v119 h_v3013 (of_decide_eq_true rfl)
  have h_v3015 : R 1 0 0 1 v3015 v3015 := (r_land hl h_v119 h_v3014 (of_decide_eq_true rfl))
  have e_v3015 : (v3015 = 1 ↔ v119 = 1 ∧ v3014 = 1) := e_land h_v119 h_v3014 (of_decide_eq_true rfl)
  have h_v3016 : R 1 0 0 1 v3016 v3016 := (r_land hl h_v279 h_v3015 (of_decide_eq_true rfl))
  have e_v3016 : (v3016 = 1 ↔ v279 = 1 ∧ v3015 = 1) := e_land h_v279 h_v3015 (of_decide_eq_true rfl)
  have h_v3017 : R 1 0 0 1 v3017 v3017 := (r_land hl h_v279 h_v3016 (of_decide_eq_true rfl))
  have e_v3017 : (v3017 = 1 ↔ v279 = 1 ∧ v3016 = 1) := e_land h_v279 h_v3016 (of_decide_eq_true rfl)
  have h_v3018 : R 1 0 0 1 v3018 v3018 := (r_land hl h_v23 h_v3017 (of_decide_eq_true rfl))
  have e_v3018 : (v3018 = 1 ↔ v23 = 1 ∧ v3017 = 1) := e_land h_v23 h_v3017 (of_decide_eq_true rfl)
  clear h_OFFr h_v6 h_v2997 h_v2998 h_v3000 h_v3002 h_v3004 h_v3006 h_v3009 h_v3011 h_v3012 h_v3013 h_v3014 h_v3015 h_v3016 h_v3017
  have h_v3019 : R 1 0 0 1 v3019 v3019 := (r_land hl h_v432 h_v3018 (of_decide_eq_true rfl))
  have e_v3019 : (v3019 = 1 ↔ v432 = 1 ∧ v3018 = 1) := e_land h_v432 h_v3018 (of_decide_eq_true rfl)
  have h_v3020 : R 1 0 0 1 v3020 v3020 := (r_land hl h_v480 h_v3019 (of_decide_eq_true rfl))
  have e_v3020 : (v3020 = 1 ↔ v480 = 1 ∧ v3019 = 1) := e_land h_v480 h_v3019 (of_decide_eq_true rfl)
  have h_v3021 : R 1 0 0 1 v3021 v3021 := (r_land hl h_v23 h_v3020 (of_decide_eq_true rfl))
  have e_v3021 : (v3021 = 1 ↔ v23 = 1 ∧ v3020 = 1) := e_land h_v23 h_v3020 (of_decide_eq_true rfl)
  have h_v3022 : R 1 0 0 1 v3022 v3022 := (r_land hl h_v483 h_v3021 (of_decide_eq_true rfl))
  have e_v3022 : (v3022 = 1 ↔ v483 = 1 ∧ v3021 = 1) := e_land h_v483 h_v3021 (of_decide_eq_true rfl)
  have h_v3023 : R 1 0 0 1 v3023 v3023 := (r_land hl h_v483 h_v3022 (of_decide_eq_true rfl))
  have e_v3023 : (v3023 = 1 ↔ v483 = 1 ∧ v3022 = 1) := e_land h_v483 h_v3022 (of_decide_eq_true rfl)
  have h_v3024 : R 1 0 0 1 v3024 v3024 := (r_land hl h_v634 h_v3023 (of_decide_eq_true rfl))
  have e_v3024 : (v3024 = 1 ↔ v634 = 1 ∧ v3023 = 1) := e_land h_v634 h_v3023 (of_decide_eq_true rfl)
  have h_v3025 : R 1 0 0 1 v3025 v3025 := (r_land hl h_v634 h_v3024 (of_decide_eq_true rfl))
  have e_v3025 : (v3025 = 1 ↔ v634 = 1 ∧ v3024 = 1) := e_land h_v634 h_v3024 (of_decide_eq_true rfl)
  have h_v3026 : R 1 0 0 1 v3026 v3026 := (r_land hl h_v23 h_v3025 (of_decide_eq_true rfl))
  have e_v3026 : (v3026 = 1 ↔ v23 = 1 ∧ v3025 = 1) := e_land h_v23 h_v3025 (of_decide_eq_true rfl)
  have h_v3027 : R 1 0 0 1 v3027 v3027 := (r_land hl h_v788 h_v3026 (of_decide_eq_true rfl))
  have e_v3027 : (v3027 = 1 ↔ v788 = 1 ∧ v3026 = 1) := e_land h_v788 h_v3026 (of_decide_eq_true rfl)
  have h_v3028 : R 1 0 0 1 v3028 v3028 := (r_land hl h_v836 h_v3027 (of_decide_eq_true rfl))
  have e_v3028 : (v3028 = 1 ↔ v836 = 1 ∧ v3027 = 1) := e_land h_v836 h_v3027 (of_decide_eq_true rfl)
  have h_v3029 : R 1 0 0 1 v3029 v3029 := (r_land hl h_v1374 h_v3028 (of_decide_eq_true rfl))
  have e_v3029 : (v3029 = 1 ↔ v1374 = 1 ∧ v3028 = 1) := e_land h_v1374 h_v3028 (of_decide_eq_true rfl)
  have h_v3030 : R 1 0 0 1 v3030 v3030 := (r_land hl h_v1834 h_v3029 (of_decide_eq_true rfl))
  have e_v3030 : (v3030 = 1 ↔ v1834 = 1 ∧ v3029 = 1) := e_land h_v1834 h_v3029 (of_decide_eq_true rfl)
  have h_v3031 : R 1 0 0 1 v3031 v3031 := (r_land hl h_v1843 h_v3030 (of_decide_eq_true rfl))
  clear h_v3018 h_v3019 h_v3020 h_v3021 h_v3022 h_v3023 h_v3024 h_v3025 h_v3026 h_v3027 h_v3028 h_v3029
  have e_v3031 : (v3031 = 1 ↔ v1843 = 1 ∧ v3030 = 1) := e_land h_v1843 h_v3030 (of_decide_eq_true rfl)
  have h_v3032 : R 1 0 0 1 v3032 v3032 := (r_land hl h_v1844 h_v3031 (of_decide_eq_true rfl))
  have e_v3032 : (v3032 = 1 ↔ v1844 = 1 ∧ v3031 = 1) := e_land h_v1844 h_v3031 (of_decide_eq_true rfl)
  have h_v3033 : R 1 0 0 1 v3033 v3033 := (r_land hl h_v1876 h_v3032 (of_decide_eq_true rfl))
  have e_v3033 : (v3033 = 1 ↔ v1876 = 1 ∧ v3032 = 1) := e_land h_v1876 h_v3032 (of_decide_eq_true rfl)
  have h_v3034 : R 1 0 0 1 v3034 v3034 := (r_land hl h_v1876 h_v3033 (of_decide_eq_true rfl))
  have e_v3034 : (v3034 = 1 ↔ v1876 = 1 ∧ v3033 = 1) := e_land h_v1876 h_v3033 (of_decide_eq_true rfl)
  have h_v3035 : R 1 0 0 1 v3035 v3035 := (r_land hl h_v1915 h_v3034 (of_decide_eq_true rfl))
  have e_v3035 : (v3035 = 1 ↔ v1915 = 1 ∧ v3034 = 1) := e_land h_v1915 h_v3034 (of_decide_eq_true rfl)
  have h_v3036 : R 1 0 0 1 v3036 v3036 := (r_land hl h_v1950 h_v3035 (of_decide_eq_true rfl))
  have e_v3036 : (v3036 = 1 ↔ v1950 = 1 ∧ v3035 = 1) := e_land h_v1950 h_v3035 (of_decide_eq_true rfl)
  have h_v3037 : R 1 0 0 1 v3037 v3037 := (r_land hl h_v1951 h_v3036 (of_decide_eq_true rfl))
  have e_v3037 : (v3037 = 1 ↔ v1951 = 1 ∧ v3036 = 1) := e_land h_v1951 h_v3036 (of_decide_eq_true rfl)
  have h_v3038 : R 1 0 0 1 v3038 v3038 := (r_land hl h_v1983 h_v3037 (of_decide_eq_true rfl))
  have e_v3038 : (v3038 = 1 ↔ v1983 = 1 ∧ v3037 = 1) := e_land h_v1983 h_v3037 (of_decide_eq_true rfl)
  have h_v3039 : R 1 0 0 1 v3039 v3039 := (r_land hl h_v1983 h_v3038 (of_decide_eq_true rfl))
  have e_v3039 : (v3039 = 1 ↔ v1983 = 1 ∧ v3038 = 1) := e_land h_v1983 h_v3038 (of_decide_eq_true rfl)
  have h_v3040 : R 1 0 0 1 v3040 v3040 := (r_land hl h_v2022 h_v3039 (of_decide_eq_true rfl))
  have e_v3040 : (v3040 = 1 ↔ v2022 = 1 ∧ v3039 = 1) := e_land h_v2022 h_v3039 (of_decide_eq_true rfl)
  have h_v3041 : R 1 0 0 1 v3041 v3041 := (r_land hl h_v23 h_v3040 (of_decide_eq_true rfl))
  have e_v3041 : (v3041 = 1 ↔ v23 = 1 ∧ v3040 = 1) := e_land h_v23 h_v3040 (of_decide_eq_true rfl)
  have h_v3042 : R 1 0 0 1 v3042 v3042 := (r_land hl h_v2077 h_v3041 (of_decide_eq_true rfl))
  have e_v3042 : (v3042 = 1 ↔ v2077 = 1 ∧ v3041 = 1) := e_land h_v2077 h_v3041 (of_decide_eq_true rfl)
  have h_v3043 : R 1 0 0 1 v3043 v3043 := (r_land hl h_v2124 h_v3042 (of_decide_eq_true rfl))
  have e_v3043 : (v3043 = 1 ↔ v2124 = 1 ∧ v3042 = 1) := e_land h_v2124 h_v3042 (of_decide_eq_true rfl)
  clear h_v3030 h_v3031 h_v3032 h_v3033 h_v3034 h_v3035 h_v3036 h_v3037 h_v3038 h_v3039 h_v3040 h_v3041 h_v3042
  have h_v3044 : R 1 0 0 1 v3044 v3044 := (r_land hl h_v23 h_v3043 (of_decide_eq_true rfl))
  have e_v3044 : (v3044 = 1 ↔ v23 = 1 ∧ v3043 = 1) := e_land h_v23 h_v3043 (of_decide_eq_true rfl)
  have h_v3045 : R 1 0 0 1 v3045 v3045 := (r_land hl h_v2128 h_v3044 (of_decide_eq_true rfl))
  have e_v3045 : (v3045 = 1 ↔ v2128 = 1 ∧ v3044 = 1) := e_land h_v2128 h_v3044 (of_decide_eq_true rfl)
  have h_v3046 : R 1 0 0 1 v3046 v3046 := (r_land hl h_v2128 h_v3045 (of_decide_eq_true rfl))
  have e_v3046 : (v3046 = 1 ↔ v2128 = 1 ∧ v3045 = 1) := e_land h_v2128 h_v3045 (of_decide_eq_true rfl)
  have h_v3047 : R 1 0 0 1 v3047 v3047 := (r_land hl h_v279 h_v3046 (of_decide_eq_true rfl))
  have e_v3047 : (v3047 = 1 ↔ v279 = 1 ∧ v3046 = 1) := e_land h_v279 h_v3046 (of_decide_eq_true rfl)
  have h_v3048 : R 1 0 0 1 v3048 v3048 := (r_land hl h_v279 h_v3047 (of_decide_eq_true rfl))
  have e_v3048 : (v3048 = 1 ↔ v279 = 1 ∧ v3047 = 1) := e_land h_v279 h_v3047 (of_decide_eq_true rfl)
  have h_v3049 : R 1 0 0 1 v3049 v3049 := (r_land hl h_v23 h_v3048 (of_decide_eq_true rfl))
  have e_v3049 : (v3049 = 1 ↔ v23 = 1 ∧ v3048 = 1) := e_land h_v23 h_v3048 (of_decide_eq_true rfl)
  have h_v3050 : R 1 0 0 1 v3050 v3050 := (r_land hl h_v2283 h_v3049 (of_decide_eq_true rfl))
  have e_v3050 : (v3050 = 1 ↔ v2283 = 1 ∧ v3049 = 1) := e_land h_v2283 h_v3049 (of_decide_eq_true rfl)
  have h_v3051 : R 1 0 0 1 v3051 v3051 := (r_land hl h_v2330 h_v3050 (of_decide_eq_true rfl))
  have e_v3051 : (v3051 = 1 ↔ v2330 = 1 ∧ v3050 = 1) := e_land h_v2330 h_v3050 (of_decide_eq_true rfl)
  have h_v3052 : R 1 0 0 1 v3052 v3052 := (r_land hl h_v23 h_v3051 (of_decide_eq_true rfl))
  have e_v3052 : (v3052 = 1 ↔ v23 = 1 ∧ v3051 = 1) := e_land h_v23 h_v3051 (of_decide_eq_true rfl)
  have h_v3053 : R 1 0 0 1 v3053 v3053 := (r_land hl h_v2334 h_v3052 (of_decide_eq_true rfl))
  have e_v3053 : (v3053 = 1 ↔ v2334 = 1 ∧ v3052 = 1) := e_land h_v2334 h_v3052 (of_decide_eq_true rfl)
  have h_v3054 : R 1 0 0 1 v3054 v3054 := (r_land hl h_v2334 h_v3053 (of_decide_eq_true rfl))
  have e_v3054 : (v3054 = 1 ↔ v2334 = 1 ∧ v3053 = 1) := e_land h_v2334 h_v3053 (of_decide_eq_true rfl)
  have h_v3055 : R 1 0 0 1 v3055 v3055 := (r_land hl h_v634 h_v3054 (of_decide_eq_true rfl))
  have e_v3055 : (v3055 = 1 ↔ v634 = 1 ∧ v3054 = 1) := e_land h_v634 h_v3054 (of_decide_eq_true rfl)
  have h_v3056 : R 1 0 0 1 v3056 v3056 := (r_land hl h_v634 h_v3055 (of_decide_eq_true rfl))
  clear h_v3043 h_v3044 h_v3045 h_v3046 h_v3047 h_v3048 h_v3049 h_v3050 h_v3051 h_v3052 h_v3053 h_v3054
  have e_v3056 : (v3056 = 1 ↔ v634 = 1 ∧ v3055 = 1) := e_land h_v634 h_v3055 (of_decide_eq_true rfl)
  have h_v3057 : R 1 0 0 1 v3057 v3057 := (r_land hl h_v23 h_v3056 (of_decide_eq_true rfl))
  have e_v3057 : (v3057 = 1 ↔ v23 = 1 ∧ v3056 = 1) := e_land h_v23 h_v3056 (of_decide_eq_true rfl)
  have h_v3058 : R 1 0 0 1 v3058 v3058 := (r_land hl h_v788 h_v3057 (of_decide_eq_true rfl))
  have e_v3058 : (v3058 = 1 ↔ v788 = 1 ∧ v3057 = 1) := e_land h_v788 h_v3057 (of_decide_eq_true rfl)
  have h_v3059 : R 1 0 0 1 v3059 v3059 := (r_land hl h_v836 h_v3058 (of_decide_eq_true rfl))
  have e_v3059 : (v3059 = 1 ↔ v836 = 1 ∧ v3058 = 1) := e_land h_v836 h_v3058 (of_decide_eq_true rfl)
  have h_v3060 : R 1 0 0 1 v3060 v3060 := (r_land hl h_v3010 h_v3059 (of_decide_eq_true rfl))
  have e_v3060 : (v3060 = 1 ↔ v3010 = 1 ∧ v3059 = 1) := e_land h_v3010 h_v3059 (of_decide_eq_true rfl)
  exact fun _ k => k e_v2785 e_v2786 e_v2787 e_v2788 e_v2789 e_v2790 e_v2791 e_v2792 e_v2793 e_v2794 e_v2795 e_v2796 e_v2797 e_v2798 e_v2799 e_v2800 e_v2801 e_v2802 e_v2803 e_v2804 e_v2805 e_v2807 e_v2808 e_v2809 e_v2810 e_v2811 e_v2813 e_v2814 e_v2815 e_v2816 e_v2817 e_v2825 e_v2826 e_v2827 e_v2828 e_v2829 e_v2830 e_v2833 e_v2834 e_v2837 e_v2838 e_v2841 e_v2842 e_v2844 e_v2845 e_v2847 e_v2848 e_v2849 e_v2850 e_v2851 e_v2852 e_v2853 e_v2854 e_v2855 e_v2856 e_v2857 e_v2858 e_v2859 e_v2860 e_v2861 e_v2862 e_v2863 e_v2864 e_v2865 e_v2866 e_v2867 e_v2868 e_v2869 e_v2870 e_v2871 e_v2872 e_v2873 e_v2874 e_v2875 e_v2876 e_v2877 e_v2878 e_v2879 e_v2880 e_v2881 e_v2882 e_v2883 e_v2884 e_v2885 e_v2886 e_v2887 e_v2888 e_v2889 e_v2890 e_v2891 e_v2892 e_v2893 e_v2894 e_v2895 e_v2896 e_v2897 e_v2898 e_v2899 e_v2900 e_v2901 e_v2902 e_v2903 e_v2904 e_v2905 e_v2906 e_v2907 e_v2908 e_v2909 e_v2910 e_v2911 e_v2912 e_v2913 e_v2914 e_v2915 e_v2916 e_v2917 e_v2919 e_v2920 e_v2921 e_v2922 e_v2923 e_v2924 e_v2925 e_v2926 e_v2927 e_v2928 e_v2929 e_v2930 e_v2931 e_v2932 e_v2933 e_v2934 e_v2935 e_v2936 e_v2937 e_v2938 e_v2939 e_v2940 e_v2941 e_v2942 e_v2943 e_v2944 e_v2945 e_v2946 e_v2947 e_v2948 e_v2949 e_v2950 e_v2951 e_v2952 e_v2953 e_v2954 e_v2957 e_v2958 e_v2959 e_v2960 e_v2961 e_v2962 e_v2963 e_v2964 e_v2965 e_v2983 e_v2984 e_v2985 e_t2983_2 e_v2987 e_v2988 e_v2989 e_v2990 e_v2991 e_v2992 e_v2993 e_v2994 e_v2995 e_v2997 e_v2998 e_v3000 e_v3002 e_v3004 e_v3006 e_v3009 e_v3010 e_v3011 e_v3012 e_v3013 e_v3014 e_v3015 e_v3016 e_v3017 e_v3018 e_v3019 e_v3020 e_v3021 e_v3022 e_v3023 e_v3024 e_v3025 e_v3026 e_v3027 e_v3028 e_v3029 e_v3030 e_v3031 e_v3032 e_v3033 e_v3034 e_v3035 e_v3036 e_v3037 e_v3038 e_v3039 e_v3040 e_v3041 e_v3042 e_v3043 e_v3044 e_v3045 e_v3046 e_v3047 e_v3048 e_v3049 e_v3050 e_v3051 e_v3052 e_v3053 e_v3054 e_v3055 e_v3056 e_v3057 e_v3058 e_v3059 e_v3060

end Tammes15.D3Trig
