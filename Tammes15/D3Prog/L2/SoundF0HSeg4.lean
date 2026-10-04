import Tammes15.D3Ck2.Prog.F0H
import Tammes15.D3Prog.Sem

namespace D3Prog

open D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progF0H_seg4 (F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (v13 : ℕ) (v270 : ℕ) (v625 : ℕ) (v796 : ℕ) (v1348 : ℕ) (v1519 : ℕ) (v1709 : ℕ) (v1718 : ℕ) (v1719 : ℕ) (v1751 : ℕ) (v1790 : ℕ) (v1825 : ℕ) (v1826 : ℕ) (v1858 : ℕ) (v1897 : ℕ) (v1953 : ℕ) (v2000 : ℕ) (v2004 : ℕ) (v2159 : ℕ) (v2206 : ℕ) (v2210 : ℕ) (v2370 : ℕ) (v2478 : ℕ) (v2666 : ℕ) (v2897 : ℕ) (v2918 : ℕ) (h_v13 : R 1 0 0 1 v13 v13) (h_v270 : R 1 0 0 1 v270 v270) (h_v625 : R 1 0 0 1 v625 v625) (h_v796 : R 1 0 0 1 v796 v796) (h_v1348 : R 1 0 0 1 v1348 v1348) (h_v1519 : R 1 0 0 1 v1519 v1519) (h_v1709 : R 1 0 0 1 v1709 v1709) (h_v1718 : R 1 0 0 1 v1718 v1718) (h_v1719 : R 1 0 0 1 v1719 v1719) (h_v1751 : R 1 0 0 1 v1751 v1751) (h_v1790 : R 1 0 0 1 v1790 v1790) (h_v1825 : R 1 0 0 1 v1825 v1825) (h_v1826 : R 1 0 0 1 v1826 v1826) (h_v1858 : R 1 0 0 1 v1858 v1858) (h_v1897 : R 1 0 0 1 v1897 v1897) (h_v1953 : R 1 0 0 1 v1953 v1953) (h_v2000 : R 1 0 0 1 v2000 v2000) (h_v2004 : R 1 0 0 1 v2004 v2004) (h_v2159 : R 1 0 0 1 v2159 v2159) (h_v2206 : R 1 0 0 1 v2206 v2206) (h_v2210 : R 1 0 0 1 v2210 v2210) (h_v2370 : R 1 0 0 1 v2370 v2370) (h_v2478 : R 1 0 0 1 v2478 v2478) (h_v2666 : R 1 0 0 1 v2666 v2666) (h_v2897 : R 1 0 0 1 v2897 v2897) (h_v2918 : R 1 0 0 1 v2918 v2918) :
    let v2919 := Nat.land v796 v2918
    let v2920 := Nat.land v1348 v2919
    let v2921 := Nat.land v1348 v2920
    let v2922 := Nat.land v1519 v2921
    let v2923 := Nat.land v1519 v2922
    let v2924 := Nat.land v1709 v2923
    let v2925 := Nat.land v1718 v2924
    let v2926 := Nat.land v1719 v2925
    let v2927 := Nat.land v1751 v2926
    let v2928 := Nat.land v1751 v2927
    let v2929 := Nat.land v1790 v2928
    let v2930 := Nat.land v1825 v2929
    let v2931 := Nat.land v1826 v2930
    let v2932 := Nat.land v1858 v2931
    let v2933 := Nat.land v1858 v2932
    let v2934 := Nat.land v1897 v2933
    let v2935 := Nat.land v13 v2934
    let v2936 := Nat.land v1953 v2935
    let v2937 := Nat.land v2000 v2936
    let v2938 := Nat.land v13 v2937
    let v2939 := Nat.land v2004 v2938
    let v2940 := Nat.land v2004 v2939
    let v2941 := Nat.land v270 v2940
    let v2942 := Nat.land v270 v2941
    let v2943 := Nat.land v13 v2942
    let v2944 := Nat.land v2159 v2943
    let v2945 := Nat.land v2206 v2944
    let v2946 := Nat.land v13 v2945
    let v2947 := Nat.land v2210 v2946
    let v2948 := Nat.land v2210 v2947
    let v2949 := Nat.land v625 v2948
    let v2950 := Nat.land v625 v2949
    let v2951 := Nat.land v2370 v2950
    let v2952 := Nat.land v2478 v2951
    let v2953 := Nat.land v2666 v2952
    let v2954 := Nat.land v2897 v2953
    ∀ (P : Prop), (((v2919 = 1 ↔ v796 = 1 ∧ v2918 = 1)) → ((v2920 = 1 ↔ v1348 = 1 ∧ v2919 = 1)) → ((v2921 = 1 ↔ v1348 = 1 ∧ v2920 = 1)) → ((v2922 = 1 ↔ v1519 = 1 ∧ v2921 = 1)) → ((v2923 = 1 ↔ v1519 = 1 ∧ v2922 = 1)) → ((v2924 = 1 ↔ v1709 = 1 ∧ v2923 = 1)) → ((v2925 = 1 ↔ v1718 = 1 ∧ v2924 = 1)) → ((v2926 = 1 ↔ v1719 = 1 ∧ v2925 = 1)) → ((v2927 = 1 ↔ v1751 = 1 ∧ v2926 = 1)) → ((v2928 = 1 ↔ v1751 = 1 ∧ v2927 = 1)) → ((v2929 = 1 ↔ v1790 = 1 ∧ v2928 = 1)) → ((v2930 = 1 ↔ v1825 = 1 ∧ v2929 = 1)) → ((v2931 = 1 ↔ v1826 = 1 ∧ v2930 = 1)) → ((v2932 = 1 ↔ v1858 = 1 ∧ v2931 = 1)) → ((v2933 = 1 ↔ v1858 = 1 ∧ v2932 = 1)) → ((v2934 = 1 ↔ v1897 = 1 ∧ v2933 = 1)) → ((v2935 = 1 ↔ v13 = 1 ∧ v2934 = 1)) → ((v2936 = 1 ↔ v1953 = 1 ∧ v2935 = 1)) → ((v2937 = 1 ↔ v2000 = 1 ∧ v2936 = 1)) → ((v2938 = 1 ↔ v13 = 1 ∧ v2937 = 1)) → ((v2939 = 1 ↔ v2004 = 1 ∧ v2938 = 1)) → ((v2940 = 1 ↔ v2004 = 1 ∧ v2939 = 1)) → ((v2941 = 1 ↔ v270 = 1 ∧ v2940 = 1)) → ((v2942 = 1 ↔ v270 = 1 ∧ v2941 = 1)) → ((v2943 = 1 ↔ v13 = 1 ∧ v2942 = 1)) → ((v2944 = 1 ↔ v2159 = 1 ∧ v2943 = 1)) → ((v2945 = 1 ↔ v2206 = 1 ∧ v2944 = 1)) → ((v2946 = 1 ↔ v13 = 1 ∧ v2945 = 1)) → ((v2947 = 1 ↔ v2210 = 1 ∧ v2946 = 1)) → ((v2948 = 1 ↔ v2210 = 1 ∧ v2947 = 1)) → ((v2949 = 1 ↔ v625 = 1 ∧ v2948 = 1)) → ((v2950 = 1 ↔ v625 = 1 ∧ v2949 = 1)) → ((v2951 = 1 ↔ v2370 = 1 ∧ v2950 = 1)) → ((v2952 = 1 ↔ v2478 = 1 ∧ v2951 = 1)) → ((v2953 = 1 ↔ v2666 = 1 ∧ v2952 = 1)) → ((v2954 = 1 ↔ v2897 = 1 ∧ v2953 = 1)) → P) → P := by
  intro v2919 v2920 v2921 v2922 v2923 v2924 v2925 v2926 v2927 v2928 v2929 v2930 v2931 v2932 v2933 v2934 v2935 v2936 v2937 v2938 v2939 v2940 v2941 v2942 v2943 v2944 v2945 v2946 v2947 v2948 v2949 v2950 v2951 v2952 v2953 v2954
  have hl : 0 < 1 := Nat.one_pos
  have h_v2919 : R 1 0 0 1 v2919 v2919 := (r_land hl h_v796 h_v2918 (of_decide_eq_true rfl))
  have e_v2919 : (v2919 = 1 ↔ v796 = 1 ∧ v2918 = 1) := e_land h_v796 h_v2918 (of_decide_eq_true rfl)
  have h_v2920 : R 1 0 0 1 v2920 v2920 := (r_land hl h_v1348 h_v2919 (of_decide_eq_true rfl))
  have e_v2920 : (v2920 = 1 ↔ v1348 = 1 ∧ v2919 = 1) := e_land h_v1348 h_v2919 (of_decide_eq_true rfl)
  have h_v2921 : R 1 0 0 1 v2921 v2921 := (r_land hl h_v1348 h_v2920 (of_decide_eq_true rfl))
  have e_v2921 : (v2921 = 1 ↔ v1348 = 1 ∧ v2920 = 1) := e_land h_v1348 h_v2920 (of_decide_eq_true rfl)
  have h_v2922 : R 1 0 0 1 v2922 v2922 := (r_land hl h_v1519 h_v2921 (of_decide_eq_true rfl))
  have e_v2922 : (v2922 = 1 ↔ v1519 = 1 ∧ v2921 = 1) := e_land h_v1519 h_v2921 (of_decide_eq_true rfl)
  have h_v2923 : R 1 0 0 1 v2923 v2923 := (r_land hl h_v1519 h_v2922 (of_decide_eq_true rfl))
  have e_v2923 : (v2923 = 1 ↔ v1519 = 1 ∧ v2922 = 1) := e_land h_v1519 h_v2922 (of_decide_eq_true rfl)
  have h_v2924 : R 1 0 0 1 v2924 v2924 := (r_land hl h_v1709 h_v2923 (of_decide_eq_true rfl))
  have e_v2924 : (v2924 = 1 ↔ v1709 = 1 ∧ v2923 = 1) := e_land h_v1709 h_v2923 (of_decide_eq_true rfl)
  have h_v2925 : R 1 0 0 1 v2925 v2925 := (r_land hl h_v1718 h_v2924 (of_decide_eq_true rfl))
  have e_v2925 : (v2925 = 1 ↔ v1718 = 1 ∧ v2924 = 1) := e_land h_v1718 h_v2924 (of_decide_eq_true rfl)
  have h_v2926 : R 1 0 0 1 v2926 v2926 := (r_land hl h_v1719 h_v2925 (of_decide_eq_true rfl))
  have e_v2926 : (v2926 = 1 ↔ v1719 = 1 ∧ v2925 = 1) := e_land h_v1719 h_v2925 (of_decide_eq_true rfl)
  have h_v2927 : R 1 0 0 1 v2927 v2927 := (r_land hl h_v1751 h_v2926 (of_decide_eq_true rfl))
  have e_v2927 : (v2927 = 1 ↔ v1751 = 1 ∧ v2926 = 1) := e_land h_v1751 h_v2926 (of_decide_eq_true rfl)
  have h_v2928 : R 1 0 0 1 v2928 v2928 := (r_land hl h_v1751 h_v2927 (of_decide_eq_true rfl))
  have e_v2928 : (v2928 = 1 ↔ v1751 = 1 ∧ v2927 = 1) := e_land h_v1751 h_v2927 (of_decide_eq_true rfl)
  have h_v2929 : R 1 0 0 1 v2929 v2929 := (r_land hl h_v1790 h_v2928 (of_decide_eq_true rfl))
  have e_v2929 : (v2929 = 1 ↔ v1790 = 1 ∧ v2928 = 1) := e_land h_v1790 h_v2928 (of_decide_eq_true rfl)
  have h_v2930 : R 1 0 0 1 v2930 v2930 := (r_land hl h_v1825 h_v2929 (of_decide_eq_true rfl))
  have e_v2930 : (v2930 = 1 ↔ v1825 = 1 ∧ v2929 = 1) := e_land h_v1825 h_v2929 (of_decide_eq_true rfl)
  have h_v2931 : R 1 0 0 1 v2931 v2931 := (r_land hl h_v1826 h_v2930 (of_decide_eq_true rfl))
  clear h_v2919 h_v2920 h_v2921 h_v2922 h_v2923 h_v2924 h_v2925 h_v2926 h_v2927 h_v2928 h_v2929
  have e_v2931 : (v2931 = 1 ↔ v1826 = 1 ∧ v2930 = 1) := e_land h_v1826 h_v2930 (of_decide_eq_true rfl)
  have h_v2932 : R 1 0 0 1 v2932 v2932 := (r_land hl h_v1858 h_v2931 (of_decide_eq_true rfl))
  have e_v2932 : (v2932 = 1 ↔ v1858 = 1 ∧ v2931 = 1) := e_land h_v1858 h_v2931 (of_decide_eq_true rfl)
  have h_v2933 : R 1 0 0 1 v2933 v2933 := (r_land hl h_v1858 h_v2932 (of_decide_eq_true rfl))
  have e_v2933 : (v2933 = 1 ↔ v1858 = 1 ∧ v2932 = 1) := e_land h_v1858 h_v2932 (of_decide_eq_true rfl)
  have h_v2934 : R 1 0 0 1 v2934 v2934 := (r_land hl h_v1897 h_v2933 (of_decide_eq_true rfl))
  have e_v2934 : (v2934 = 1 ↔ v1897 = 1 ∧ v2933 = 1) := e_land h_v1897 h_v2933 (of_decide_eq_true rfl)
  have h_v2935 : R 1 0 0 1 v2935 v2935 := (r_land hl h_v13 h_v2934 (of_decide_eq_true rfl))
  have e_v2935 : (v2935 = 1 ↔ v13 = 1 ∧ v2934 = 1) := e_land h_v13 h_v2934 (of_decide_eq_true rfl)
  have h_v2936 : R 1 0 0 1 v2936 v2936 := (r_land hl h_v1953 h_v2935 (of_decide_eq_true rfl))
  have e_v2936 : (v2936 = 1 ↔ v1953 = 1 ∧ v2935 = 1) := e_land h_v1953 h_v2935 (of_decide_eq_true rfl)
  have h_v2937 : R 1 0 0 1 v2937 v2937 := (r_land hl h_v2000 h_v2936 (of_decide_eq_true rfl))
  have e_v2937 : (v2937 = 1 ↔ v2000 = 1 ∧ v2936 = 1) := e_land h_v2000 h_v2936 (of_decide_eq_true rfl)
  have h_v2938 : R 1 0 0 1 v2938 v2938 := (r_land hl h_v13 h_v2937 (of_decide_eq_true rfl))
  have e_v2938 : (v2938 = 1 ↔ v13 = 1 ∧ v2937 = 1) := e_land h_v13 h_v2937 (of_decide_eq_true rfl)
  have h_v2939 : R 1 0 0 1 v2939 v2939 := (r_land hl h_v2004 h_v2938 (of_decide_eq_true rfl))
  have e_v2939 : (v2939 = 1 ↔ v2004 = 1 ∧ v2938 = 1) := e_land h_v2004 h_v2938 (of_decide_eq_true rfl)
  have h_v2940 : R 1 0 0 1 v2940 v2940 := (r_land hl h_v2004 h_v2939 (of_decide_eq_true rfl))
  have e_v2940 : (v2940 = 1 ↔ v2004 = 1 ∧ v2939 = 1) := e_land h_v2004 h_v2939 (of_decide_eq_true rfl)
  have h_v2941 : R 1 0 0 1 v2941 v2941 := (r_land hl h_v270 h_v2940 (of_decide_eq_true rfl))
  have e_v2941 : (v2941 = 1 ↔ v270 = 1 ∧ v2940 = 1) := e_land h_v270 h_v2940 (of_decide_eq_true rfl)
  have h_v2942 : R 1 0 0 1 v2942 v2942 := (r_land hl h_v270 h_v2941 (of_decide_eq_true rfl))
  have e_v2942 : (v2942 = 1 ↔ v270 = 1 ∧ v2941 = 1) := e_land h_v270 h_v2941 (of_decide_eq_true rfl)
  have h_v2943 : R 1 0 0 1 v2943 v2943 := (r_land hl h_v13 h_v2942 (of_decide_eq_true rfl))
  have e_v2943 : (v2943 = 1 ↔ v13 = 1 ∧ v2942 = 1) := e_land h_v13 h_v2942 (of_decide_eq_true rfl)
  clear h_v2930 h_v2931 h_v2932 h_v2933 h_v2934 h_v2935 h_v2936 h_v2937 h_v2938 h_v2939 h_v2940 h_v2941 h_v2942
  have h_v2944 : R 1 0 0 1 v2944 v2944 := (r_land hl h_v2159 h_v2943 (of_decide_eq_true rfl))
  have e_v2944 : (v2944 = 1 ↔ v2159 = 1 ∧ v2943 = 1) := e_land h_v2159 h_v2943 (of_decide_eq_true rfl)
  have h_v2945 : R 1 0 0 1 v2945 v2945 := (r_land hl h_v2206 h_v2944 (of_decide_eq_true rfl))
  have e_v2945 : (v2945 = 1 ↔ v2206 = 1 ∧ v2944 = 1) := e_land h_v2206 h_v2944 (of_decide_eq_true rfl)
  have h_v2946 : R 1 0 0 1 v2946 v2946 := (r_land hl h_v13 h_v2945 (of_decide_eq_true rfl))
  have e_v2946 : (v2946 = 1 ↔ v13 = 1 ∧ v2945 = 1) := e_land h_v13 h_v2945 (of_decide_eq_true rfl)
  have h_v2947 : R 1 0 0 1 v2947 v2947 := (r_land hl h_v2210 h_v2946 (of_decide_eq_true rfl))
  have e_v2947 : (v2947 = 1 ↔ v2210 = 1 ∧ v2946 = 1) := e_land h_v2210 h_v2946 (of_decide_eq_true rfl)
  have h_v2948 : R 1 0 0 1 v2948 v2948 := (r_land hl h_v2210 h_v2947 (of_decide_eq_true rfl))
  have e_v2948 : (v2948 = 1 ↔ v2210 = 1 ∧ v2947 = 1) := e_land h_v2210 h_v2947 (of_decide_eq_true rfl)
  have h_v2949 : R 1 0 0 1 v2949 v2949 := (r_land hl h_v625 h_v2948 (of_decide_eq_true rfl))
  have e_v2949 : (v2949 = 1 ↔ v625 = 1 ∧ v2948 = 1) := e_land h_v625 h_v2948 (of_decide_eq_true rfl)
  have h_v2950 : R 1 0 0 1 v2950 v2950 := (r_land hl h_v625 h_v2949 (of_decide_eq_true rfl))
  have e_v2950 : (v2950 = 1 ↔ v625 = 1 ∧ v2949 = 1) := e_land h_v625 h_v2949 (of_decide_eq_true rfl)
  have h_v2951 : R 1 0 0 1 v2951 v2951 := (r_land hl h_v2370 h_v2950 (of_decide_eq_true rfl))
  have e_v2951 : (v2951 = 1 ↔ v2370 = 1 ∧ v2950 = 1) := e_land h_v2370 h_v2950 (of_decide_eq_true rfl)
  have h_v2952 : R 1 0 0 1 v2952 v2952 := (r_land hl h_v2478 h_v2951 (of_decide_eq_true rfl))
  have e_v2952 : (v2952 = 1 ↔ v2478 = 1 ∧ v2951 = 1) := e_land h_v2478 h_v2951 (of_decide_eq_true rfl)
  have h_v2953 : R 1 0 0 1 v2953 v2953 := (r_land hl h_v2666 h_v2952 (of_decide_eq_true rfl))
  have e_v2953 : (v2953 = 1 ↔ v2666 = 1 ∧ v2952 = 1) := e_land h_v2666 h_v2952 (of_decide_eq_true rfl)
  have h_v2954 : R 1 0 0 1 v2954 v2954 := (r_land hl h_v2897 h_v2953 (of_decide_eq_true rfl))
  have e_v2954 : (v2954 = 1 ↔ v2897 = 1 ∧ v2953 = 1) := e_land h_v2897 h_v2953 (of_decide_eq_true rfl)
  exact fun _ k => k e_v2919 e_v2920 e_v2921 e_v2922 e_v2923 e_v2924 e_v2925 e_v2926 e_v2927 e_v2928 e_v2929 e_v2930 e_v2931 e_v2932 e_v2933 e_v2934 e_v2935 e_v2936 e_v2937 e_v2938 e_v2939 e_v2940 e_v2941 e_v2942 e_v2943 e_v2944 e_v2945 e_v2946 e_v2947 e_v2948 e_v2949 e_v2950 e_v2951 e_v2952 e_v2953 e_v2954

end D3Prog
