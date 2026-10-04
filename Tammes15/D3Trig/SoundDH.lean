import Tammes15.D3Trig.Prog.DH
import Tammes15.D3Prog.L2.Kinds
import Tammes15.D3Prog.L2.PLib
import Tammes15.D3Trig.RhoKinds

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem progDH_l2 (F0 F1 F2 F3 H0 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (h : Tammes15.D3Trig.progDH 1 F0 F1 F2 F3 H0 = 1) (hD : D3Prog.L2.InDom F0 F1 F2 F3) : LaneClaimR 1 true F0 F1 F2 F3 := by
  unfold Tammes15.D3Trig.progDH at h
  extract_lets -merge OFFr H61r v0 v3 v5 v6 v8 v9 v10 v11 v12 v13 t6 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 t32 v38 v39 v40 v41 v42 t31 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v101 v102 v103 v104 t103 v106 v107 v108 v109 v110 v111 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v186 v188 v190 v191 v194 v195 v196 v198 v199 v200 v201 v202 v203 v204 at h
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have e_OFFr : sv OFFr = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have h_H61r : R 1 0 2305843009213693952 2305843009213693952 H61r H61r := (r_c hl 2305843009213693952 (of_decide_eq_true rfl))
  have e_H61r : sv H61r = (-2305843009213693952) := e_c 2305843009213693952 (-2305843009213693952) (of_decide_eq_true rfl)
  have h_v0 : R 1 0 4611686018427387904 4611686087146864624 v0 v0 := (r1_ix hb_F0 0 (of_decide_eq_true rfl))
  have e_v0 : sv v0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F0 0 (of_decide_eq_true rfl)
  have h_v3 : R 1 0 4611686018427387904 4611686087146864624 v3 v3 := (r1_ix hb_F1 32 (of_decide_eq_true rfl))
  have e_v3 : sv v3 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F1 32 (of_decide_eq_true rfl)
  have h_v5 : R 1 0 4611686018427387904 4611686087146864624 v5 v5 := (r1_ix hb_F2 32 (of_decide_eq_true rfl))
  have e_v5 : sv v5 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F2 32 (of_decide_eq_true rfl)
  have h_v6 : R 1 0 4611686018427387904 4611686087146864624 v6 v6 := (r1_ix hb_F3 0 (of_decide_eq_true rfl))
  have e_v6 : sv v6 = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F3 0 (of_decide_eq_true rfl)
  have h_v8 : R 1 0 4611686018427387903 4611686018427387903 v8 v8 := (r_c hl 4611686018427387903 (of_decide_eq_true rfl))
  have e_v8 : sv v8 = (-1) := e_c 4611686018427387903 (-1) (of_decide_eq_true rfl)
  have h_v9 : R 1 0 0 1 v9 v9 := (r_plt hl h_v8 h_v6 (of_decide_eq_true rfl))
  have e_v9 : (v9 = 1 ↔ sv v8 < sv v6) := e_plt h_v8 h_v6 (of_decide_eq_true rfl)
  have h_v10 : R 1 0 4611686019270702761 4611686019270702761 v10 v10 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have e_v10 : sv v10 = (843314857) := e_c 4611686019270702761 (843314857) (of_decide_eq_true rfl)
  have h_v11 : R 1 0 0 1 v11 v11 := (r_plt hl h_v10 h_v6 (of_decide_eq_true rfl))
  have e_v11 : (v11 = 1 ↔ sv v10 < sv v6) := e_plt h_v10 h_v6 (of_decide_eq_true rfl)
  have h_v12 : R 1 0 0 1 v12 v12 := (r_sub hl (r_O hl) h_v11 (of_decide_eq_true rfl))
  have e_v12 : (v12 = 1 ↔ ¬v11 = 1) := e_not h_v11 (of_decide_eq_true rfl)
  have h_v13 : R 1 0 0 1 v13 v13 := (r_land hl h_v9 h_v12 (of_decide_eq_true rfl))
  have e_v13 : (v13 = 1 ↔ v9 = 1 ∧ v12 = 1) := e_land h_v9 h_v12 (of_decide_eq_true rfl)
  have h_t6_1 : R 1 0 4611686018427387904 4611686018695823363 t6.1 t6.1 := r_sc1 hl h_v6 (of_decide_eq_true rfl)
  clear e_OFFr e_H61r h_v9 h_v11 h_v12 h_t6_1
  have h_t6_2 : R 1 0 4611686018158952445 4611686018695823363 t6.2 t6.2 := r_sc2 hl h_v6 (of_decide_eq_true rfl)
  have e_t6_1 : sv t6.1 = (sc28pS (scArg v6)).1 := e_sc1 h_v6 (of_decide_eq_true rfl)
  have e_t6_2 : sv t6.2 = (sc28pS (scArg v6)).2 := e_sc2 h_v6 (of_decide_eq_true rfl)
  have h_v15 : R 1 0 4611686018427387900 4611686018427387900 v15 v15 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have e_v15 : sv v15 = (-4) := e_c 4611686018427387900 (-4) (of_decide_eq_true rfl)
  have h_v16 : R 1 0 4611686018158952441 4611686018695823359 v16 v16 := (r_sub hl (r_add hl h_t6_2 h_v15 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v16 : sv v16 = sv t6.2 + sv v15 := e_add h_t6_2 h_v15 (of_decide_eq_true rfl)
  have h_v17 : R 1 0 4611686018158952448 4611686018158952448 v17 v17 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have e_v17 : sv v17 = (-268435456) := e_c 4611686018158952448 (-268435456) (of_decide_eq_true rfl)
  have h_v18 : R 1 0 0 1 v18 v18 := (r_plt hl h_v16 h_v17 (of_decide_eq_true rfl))
  have e_v18 : (v18 = 1 ↔ sv v16 < sv v17) := e_plt h_v16 h_v17 (of_decide_eq_true rfl)
  have h_v19 : R 1 0 4611686018158952441 4611686018695823359 v19 v19 := (r_psel hl h_v18 h_v17 h_v16 (of_decide_eq_true rfl))
  have e_v19 : v19 = if v18 = 1 then v17 else v16 := e_psel h_v18 h_v17 h_v16 (of_decide_eq_true rfl)
  have h_v20 : R 1 0 4611686019270702759 4611686019270702759 v20 v20 := (r_c hl 4611686019270702759 (of_decide_eq_true rfl))
  have e_v20 : sv v20 = (843314855) := e_c 4611686019270702759 (843314855) (of_decide_eq_true rfl)
  have h_v21 : R 1 0 0 1 v21 v21 := (r_plt hl h_v20 h_v6 (of_decide_eq_true rfl))
  have e_v21 : (v21 = 1 ↔ sv v20 < sv v6) := e_plt h_v20 h_v6 (of_decide_eq_true rfl)
  have h_v22 : R 1 0 4611686018158952441 4611686018695823359 v22 v22 := (r_psel hl h_v21 h_v17 h_v19 (of_decide_eq_true rfl))
  have e_v22 : v22 = if v21 = 1 then v17 else v19 := e_psel h_v21 h_v17 h_v19 (of_decide_eq_true rfl)
  have h_v23 : R 1 0 4611686018427387908 4611686018427387908 v23 v23 := (r_c hl 4611686018427387908 (of_decide_eq_true rfl))
  have e_v23 : sv v23 = (4) := e_c 4611686018427387908 (4) (of_decide_eq_true rfl)
  have h_v24 : R 1 0 4611686018158952449 4611686018695823367 v24 v24 := (r_sub hl (r_add hl h_t6_2 h_v23 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v24 : sv v24 = sv t6.2 + sv v23 := e_add h_t6_2 h_v23 (of_decide_eq_true rfl)
  have h_v25 : R 1 0 4611686018695823360 4611686018695823360 v25 v25 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have e_v25 : sv v25 = (268435456) := e_c 4611686018695823360 (268435456) (of_decide_eq_true rfl)
  clear h_t6_2 e_t6_1 h_v16 h_v18 h_v19 h_v21
  have h_v26 : R 1 0 0 1 v26 v26 := (r_plt hl h_v24 h_v25 (of_decide_eq_true rfl))
  have e_v26 : (v26 = 1 ↔ sv v24 < sv v25) := e_plt h_v24 h_v25 (of_decide_eq_true rfl)
  have h_v27 : R 1 0 4611686018158952449 4611686018695823367 v27 v27 := (r_psel hl h_v26 h_v24 h_v25 (of_decide_eq_true rfl))
  have e_v27 : v27 = if v26 = 1 then v24 else v25 := e_psel h_v26 h_v24 h_v25 (of_decide_eq_true rfl)
  have h_v28 : R 1 0 4611686018427387905 4611686018427387905 v28 v28 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have e_v28 : sv v28 = (1) := e_c 4611686018427387905 (1) (of_decide_eq_true rfl)
  have h_v29 : R 1 0 0 1 v29 v29 := (r_plt hl h_v6 h_v28 (of_decide_eq_true rfl))
  have e_v29 : (v29 = 1 ↔ sv v6 < sv v28) := e_plt h_v6 h_v28 (of_decide_eq_true rfl)
  have h_v30 : R 1 0 4611686018158952449 4611686018695823367 v30 v30 := (r_psel hl h_v29 h_v25 h_v27 (of_decide_eq_true rfl))
  have e_v30 : v30 = if v29 = 1 then v25 else v27 := e_psel h_v29 h_v25 h_v27 (of_decide_eq_true rfl)
  have h_v31 : R 1 0 4611686018427387904 4611686052787126264 v31 v31 := (r_add hl (r_pshr1 hl h_v3) h_H61r (of_decide_eq_true rfl))
  have e_v31 : sv v31 = sv v3 / 2 := e_halfF h_v3
  have h_v32 : R 1 0 4611686018427387904 4611686052787126264 v32 v32 := (r_add hl (r_pshr1 hl (r_add hl h_v3 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v32 : sv v32 = (sv v3 + 1) / 2 := e_halfC h_v3 (of_decide_eq_true rfl)
  have h_v33 : R 1 0 0 1 v33 v33 := (r_plt hl h_v8 h_v31 (of_decide_eq_true rfl))
  have e_v33 : (v33 = 1 ↔ sv v8 < sv v31) := e_plt h_v8 h_v31 (of_decide_eq_true rfl)
  have h_v34 : R 1 0 0 1 v34 v34 := (r_plt hl h_v10 h_v32 (of_decide_eq_true rfl))
  have e_v34 : (v34 = 1 ↔ sv v10 < sv v32) := e_plt h_v10 h_v32 (of_decide_eq_true rfl)
  have h_v35 : R 1 0 0 1 v35 v35 := (r_sub hl (r_O hl) h_v34 (of_decide_eq_true rfl))
  have e_v35 : (v35 = 1 ↔ ¬v34 = 1) := e_not h_v34 (of_decide_eq_true rfl)
  have h_v36 : R 1 0 0 1 v36 v36 := (r_land hl h_v33 h_v35 (of_decide_eq_true rfl))
  have e_v36 : (v36 = 1 ↔ v33 = 1 ∧ v35 = 1) := e_land h_v33 h_v35 (of_decide_eq_true rfl)
  have h_t32_1 : R 1 0 4611686018427387904 4611686018695823363 t32.1 t32.1 := r_sc1 hl h_v32 (of_decide_eq_true rfl)
  have h_t32_2 : R 1 0 4611686018158952445 4611686018695823363 t32.2 t32.2 := r_sc2 hl h_v32 (of_decide_eq_true rfl)
  have e_t32_1 : sv t32.1 = (sc28pS (scArg v32)).1 := e_sc1 h_v32 (of_decide_eq_true rfl)
  clear h_H61r h_v3 h_v10 h_v24 h_v26 h_v27 h_v28 h_v29 h_v33 h_v34 h_v35
  have e_t32_2 : sv t32.2 = (sc28pS (scArg v32)).2 := e_sc2 h_v32 (of_decide_eq_true rfl)
  have h_v38 : R 1 0 4611686018158952441 4611686018695823359 v38 v38 := (r_sub hl (r_add hl h_v15 h_t32_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v38 : sv v38 = sv v15 + sv t32.2 := e_add h_v15 h_t32_2 (of_decide_eq_true rfl)
  have h_v39 : R 1 0 0 1 v39 v39 := (r_plt hl h_v38 h_v17 (of_decide_eq_true rfl))
  have e_v39 : (v39 = 1 ↔ sv v38 < sv v17) := e_plt h_v38 h_v17 (of_decide_eq_true rfl)
  have h_v40 : R 1 0 4611686018158952441 4611686018695823359 v40 v40 := (r_psel hl h_v39 h_v17 h_v38 (of_decide_eq_true rfl))
  have e_v40 : v40 = if v39 = 1 then v17 else v38 := e_psel h_v39 h_v17 h_v38 (of_decide_eq_true rfl)
  have h_v41 : R 1 0 0 1 v41 v41 := (r_plt hl h_v20 h_v32 (of_decide_eq_true rfl))
  have e_v41 : (v41 = 1 ↔ sv v20 < sv v32) := e_plt h_v20 h_v32 (of_decide_eq_true rfl)
  have h_v42 : R 1 0 4611686018158952441 4611686018695823359 v42 v42 := (r_psel hl h_v41 h_v17 h_v40 (of_decide_eq_true rfl))
  have e_v42 : v42 = if v41 = 1 then v17 else v40 := e_psel h_v41 h_v17 h_v40 (of_decide_eq_true rfl)
  have h_t31_1 : R 1 0 4611686018427387904 4611686018695823363 t31.1 t31.1 := r_sc1 hl h_v31 (of_decide_eq_true rfl)
  have h_t31_2 : R 1 0 4611686018158952445 4611686018695823363 t31.2 t31.2 := r_sc2 hl h_v31 (of_decide_eq_true rfl)
  have e_t31_1 : sv t31.1 = (sc28pS (scArg v31)).1 := e_sc1 h_v31 (of_decide_eq_true rfl)
  have e_t31_2 : sv t31.2 = (sc28pS (scArg v31)).2 := e_sc2 h_v31 (of_decide_eq_true rfl)
  have h_v51 : R 1 0 0 1 v51 v51 := (r_plt hl h_t31_1 h_t32_1 (of_decide_eq_true rfl))
  have e_v51 : (v51 = 1 ↔ sv t31.1 < sv t32.1) := e_plt h_t31_1 h_t32_1 (of_decide_eq_true rfl)
  have h_v52 : R 1 0 4611686018427387904 4611686018695823363 v52 v52 := (r_psel hl h_v51 h_t31_1 h_t32_1 (of_decide_eq_true rfl))
  have e_v52 : v52 = if v51 = 1 then t31.1 else t32.1 := e_psel h_v51 h_t31_1 h_t32_1 (of_decide_eq_true rfl)
  have h_v53 : R 1 0 4611686018427387900 4611686018695823359 v53 v53 := (r_sub hl (r_add hl h_v15 h_v52 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v53 : sv v53 = sv v15 + sv v52 := e_add h_v15 h_v52 (of_decide_eq_true rfl)
  have h_v54 : R 1 0 4611686018427387904 4611686018695823363 v54 v54 := (r_psel hl h_v51 h_t32_1 h_t31_1 (of_decide_eq_true rfl))
  have e_v54 : v54 = if v51 = 1 then t32.1 else t31.1 := e_psel h_v51 h_t32_1 h_t31_1 (of_decide_eq_true rfl)
  have h_v55 : R 1 0 4611686018427387908 4611686018695823367 v55 v55 := (r_sub hl (r_add hl h_v23 h_v54 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v55 : sv v55 = sv v23 + sv v54 := e_add h_v23 h_v54 (of_decide_eq_true rfl)
  clear h_v20 h_t32_1 h_t32_2 h_v38 h_v39 h_v40 h_v41 h_t31_1 h_t31_2 e_t31_2 h_v51 h_v52 h_v54
  have h_v56 : R 1 0 0 1 v56 v56 := (r_plt hl h_v55 h_v25 (of_decide_eq_true rfl))
  have e_v56 : (v56 = 1 ↔ sv v55 < sv v25) := e_plt h_v55 h_v25 (of_decide_eq_true rfl)
  have h_v57 : R 1 0 4611686018427387908 4611686018695823367 v57 v57 := (r_psel hl h_v56 h_v55 h_v25 (of_decide_eq_true rfl))
  have e_v57 : v57 = if v56 = 1 then v55 else v25 := e_psel h_v56 h_v55 h_v25 (of_decide_eq_true rfl)
  have h_v58 : R 1 0 4611686018849045334 4611686018849045334 v58 v58 := (r_c hl 4611686018849045334 (of_decide_eq_true rfl))
  have e_v58 : sv v58 = (421657430) := e_c 4611686018849045334 (421657430) (of_decide_eq_true rfl)
  have h_v59 : R 1 0 0 1 v59 v59 := (r_plt hl h_v31 h_v58 (of_decide_eq_true rfl))
  have e_v59 : (v59 = 1 ↔ sv v31 < sv v58) := e_plt h_v31 h_v58 (of_decide_eq_true rfl)
  have h_v60 : R 1 0 4611686018849045331 4611686018849045331 v60 v60 := (r_c hl 4611686018849045331 (of_decide_eq_true rfl))
  have e_v60 : sv v60 = (421657427) := e_c 4611686018849045331 (421657427) (of_decide_eq_true rfl)
  have h_v61 : R 1 0 0 1 v61 v61 := (r_plt hl h_v60 h_v32 (of_decide_eq_true rfl))
  have e_v61 : (v61 = 1 ↔ sv v60 < sv v32) := e_plt h_v60 h_v32 (of_decide_eq_true rfl)
  have h_v62 : R 1 0 0 1 v62 v62 := (r_land hl h_v59 h_v61 (of_decide_eq_true rfl))
  have e_v62 : (v62 = 1 ↔ v59 = 1 ∧ v61 = 1) := e_land h_v59 h_v61 (of_decide_eq_true rfl)
  have h_v63 : R 1 0 4611686018427387908 4611686018695823367 v63 v63 := (r_psel hl h_v62 h_v25 h_v57 (of_decide_eq_true rfl))
  have e_v63 : v63 = if v62 = 1 then v25 else v57 := e_psel h_v62 h_v25 h_v57 (of_decide_eq_true rfl)
  have h_v64 : R 1 0 4611686018427387904 4611686018427387904 v64 v64 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have e_v64 : sv v64 = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have h_v65 : R 1 0 0 1 v65 v65 := (r_plt hl h_v22 h_v64 (of_decide_eq_true rfl))
  have e_v65 : (v65 = 1 ↔ sv v22 < sv v64) := e_plt h_v22 h_v64 (of_decide_eq_true rfl)
  have h_v66 : R 1 0 0 1 v66 v66 := (r_sub hl (r_O hl) h_v65 (of_decide_eq_true rfl))
  have e_v66 : (v66 = 1 ↔ ¬v65 = 1) := e_not h_v65 (of_decide_eq_true rfl)
  have h_v67 : R 1 0 0 1 v67 v67 := (r_plt hl h_v64 h_v30 (of_decide_eq_true rfl))
  have e_v67 : (v67 = 1 ↔ sv v64 < sv v30) := e_plt h_v64 h_v30 (of_decide_eq_true rfl)
  have h_v68 : R 1 0 0 1 v68 v68 := (r_sub hl (r_O hl) h_v67 (of_decide_eq_true rfl))
  clear h_v31 h_v32 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
  have e_v68 : (v68 = 1 ↔ ¬v67 = 1) := e_not h_v67 (of_decide_eq_true rfl)
  have h_v69 : R 1 0 0 1 v69 v69 := (r_land hl h_v65 h_v68 (of_decide_eq_true rfl))
  have e_v69 : (v69 = 1 ↔ v65 = 1 ∧ v68 = 1) := e_land h_v65 h_v68 (of_decide_eq_true rfl)
  have h_v70 : R 1 0 0 1 v70 v70 := (r_land hl h_v65 h_v67 (of_decide_eq_true rfl))
  have e_v70 : (v70 = 1 ↔ v65 = 1 ∧ v67 = 1) := e_land h_v65 h_v67 (of_decide_eq_true rfl)
  have h_v71 : R 1 0 0 1 v71 v71 := (r_plt hl h_v53 h_v64 (of_decide_eq_true rfl))
  have e_v71 : (v71 = 1 ↔ sv v53 < sv v64) := e_plt h_v53 h_v64 (of_decide_eq_true rfl)
  have h_v72 : R 1 0 0 1 v72 v72 := (r_sub hl (r_O hl) h_v71 (of_decide_eq_true rfl))
  have e_v72 : (v72 = 1 ↔ ¬v71 = 1) := e_not h_v71 (of_decide_eq_true rfl)
  have h_v73 : R 1 0 0 1 v73 v73 := (r_plt hl h_v64 h_v63 (of_decide_eq_true rfl))
  have e_v73 : (v73 = 1 ↔ sv v64 < sv v63) := e_plt h_v64 h_v63 (of_decide_eq_true rfl)
  have h_v74 : R 1 0 0 1 v74 v74 := (r_sub hl (r_O hl) h_v73 (of_decide_eq_true rfl))
  have e_v74 : (v74 = 1 ↔ ¬v73 = 1) := e_not h_v73 (of_decide_eq_true rfl)
  have h_v75 : R 1 0 0 1 v75 v75 := (r_land hl h_v71 h_v74 (of_decide_eq_true rfl))
  have e_v75 : (v75 = 1 ↔ v71 = 1 ∧ v74 = 1) := e_land h_v71 h_v74 (of_decide_eq_true rfl)
  have h_v76 : R 1 0 0 1 v76 v76 := (r_land hl h_v71 h_v73 (of_decide_eq_true rfl))
  have e_v76 : (v76 = 1 ↔ v71 = 1 ∧ v73 = 1) := e_land h_v71 h_v73 (of_decide_eq_true rfl)
  have h_v77 : R 1 0 0 1 v77 v77 := (r_land hl h_v70 h_v76 (of_decide_eq_true rfl))
  have e_v77 : (v77 = 1 ↔ v70 = 1 ∧ v76 = 1) := e_land h_v70 h_v76 (of_decide_eq_true rfl)
  have h_v78 : R 1 0 0 1 v78 v78 := (r_sub hl (r_O hl) h_v77 (of_decide_eq_true rfl))
  have e_v78 : (v78 = 1 ↔ ¬v77 = 1) := e_not h_v77 (of_decide_eq_true rfl)
  have h_v79 : R 1 0 0 1 v79 v79 := (r_land hl h_v66 h_v76 (of_decide_eq_true rfl))
  have e_v79 : (v79 = 1 ↔ v66 = 1 ∧ v76 = 1) := e_land h_v66 h_v76 (of_decide_eq_true rfl)
  have h_v80 : R 1 0 0 1 v80 v80 := (r_lor hl h_v75 h_v79 (of_decide_eq_true rfl))
  have e_v80 : (v80 = 1 ↔ v75 = 1 ∨ v79 = 1) := e_lor h_v75 h_v79 (of_decide_eq_true rfl)
  clear h_v65 h_v66 h_v67 h_v68 h_v71 h_v73 h_v74 h_v77 h_v79
  have h_v81 : R 1 0 4611686018158952441 4611686018695823367 v81 v81 := (r_psel hl h_v80 h_v30 h_v22 (of_decide_eq_true rfl))
  have e_v81 : v81 = if v80 = 1 then v30 else v22 := e_psel h_v80 h_v30 h_v22 (of_decide_eq_true rfl)
  have h_v82 : R 1 0 0 1 v82 v82 := (r_land hl h_v70 h_v72 (of_decide_eq_true rfl))
  have e_v82 : (v82 = 1 ↔ v70 = 1 ∧ v72 = 1) := e_land h_v70 h_v72 (of_decide_eq_true rfl)
  have h_v83 : R 1 0 0 1 v83 v83 := (r_lor hl h_v69 h_v82 (of_decide_eq_true rfl))
  have e_v83 : (v83 = 1 ↔ v69 = 1 ∨ v82 = 1) := e_lor h_v69 h_v82 (of_decide_eq_true rfl)
  have h_v84 : R 1 0 4611686018427387900 4611686018695823367 v84 v84 := (r_psel hl h_v83 h_v63 h_v53 (of_decide_eq_true rfl))
  have e_v84 : v84 = if v83 = 1 then v63 else v53 := e_psel h_v83 h_v63 h_v53 (of_decide_eq_true rfl)
  have h_v85 : R 1 0 0 1 v85 v85 := (r_land hl h_v69 h_v76 (of_decide_eq_true rfl))
  have e_v85 : (v85 = 1 ↔ v69 = 1 ∧ v76 = 1) := e_land h_v69 h_v76 (of_decide_eq_true rfl)
  have h_v86 : R 1 0 0 1 v86 v86 := (r_lor hl h_v75 h_v85 (of_decide_eq_true rfl))
  have e_v86 : (v86 = 1 ↔ v75 = 1 ∨ v85 = 1) := e_lor h_v75 h_v85 (of_decide_eq_true rfl)
  have h_v87 : R 1 0 4611686018158952441 4611686018695823367 v87 v87 := (r_psel hl h_v86 h_v22 h_v30 (of_decide_eq_true rfl))
  have e_v87 : v87 = if v86 = 1 then v22 else v30 := e_psel h_v86 h_v22 h_v30 (of_decide_eq_true rfl)
  have h_v88 : R 1 0 0 1 v88 v88 := (r_land hl h_v70 h_v75 (of_decide_eq_true rfl))
  have e_v88 : (v88 = 1 ↔ v70 = 1 ∧ v75 = 1) := e_land h_v70 h_v75 (of_decide_eq_true rfl)
  have h_v89 : R 1 0 0 1 v89 v89 := (r_lor hl h_v69 h_v88 (of_decide_eq_true rfl))
  have e_v89 : (v89 = 1 ↔ v69 = 1 ∨ v88 = 1) := e_lor h_v69 h_v88 (of_decide_eq_true rfl)
  have h_v90 : R 1 0 4611686018427387900 4611686018695823367 v90 v90 := (r_psel hl h_v89 h_v53 h_v63 (of_decide_eq_true rfl))
  have e_v90 : v90 = if v89 = 1 then v53 else v63 := e_psel h_v89 h_v53 h_v63 (of_decide_eq_true rfl)
  have h_v91 : R 1 0 4539628420631363535 4683743616223412273 v91 v91 := (r_smx hl 29 h_v84 h_v81 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v91 : sv v91 = sv v84 * sv v81 := e_smx 29 h_v84 h_v81 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v92 : R 1 0 4611686018158952433 4611686018695823374 v92 v92 := (r_srdF hl h_v91 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v92 : sv v92 = sv v91 / 2 ^ 28 := e_srdF h_v91 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v93 : R 1 0 4539628420631363535 4683743616223412273 v93 v93 := (r_smx hl 29 h_v90 h_v87 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  clear h_v22 h_v30 h_v53 h_v63 h_v69 h_v70 h_v72 h_v75 h_v76 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91
  have e_v93 : sv v93 = sv v90 * sv v87 := e_smx 29 h_v90 h_v87 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v94 : R 1 0 4611686018158952434 4611686018695823375 v94 v94 := (r_srdC hl h_v93 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v94 : sv v94 = -((-sv v93) / 2 ^ 28) := e_srdC h_v93 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v95 : R 1 0 0 1 v95 v95 := (r_plt hl h_v64 h_v92 (of_decide_eq_true rfl))
  have e_v95 : (v95 = 1 ↔ sv v64 < sv v92) := e_plt h_v64 h_v92 (of_decide_eq_true rfl)
  have h_v96 : R 1 0 0 1 v96 v96 := (r_sub hl (r_O hl) h_v95 (of_decide_eq_true rfl))
  have e_v96 : (v96 = 1 ↔ ¬v95 = 1) := e_not h_v95 (of_decide_eq_true rfl)
  have h_v97 : R 1 0 0 1 v97 v97 := (r_plt hl h_v42 h_v64 (of_decide_eq_true rfl))
  have e_v97 : (v97 = 1 ↔ sv v42 < sv v64) := e_plt h_v42 h_v64 (of_decide_eq_true rfl)
  have h_v98 : R 1 0 4611686018158952433 4611686018695823375 v98 v98 := (r_psel hl h_v97 h_v92 h_v94 (of_decide_eq_true rfl))
  have e_v98 : v98 = if v97 = 1 then v92 else v94 := e_psel h_v97 h_v92 h_v94 (of_decide_eq_true rfl)
  have h_v101 : R 1 0 4611686018158952449 4611686018695823367 v101 v101 := (r_sub hl (r_add hl h_v64 h_OFFr (of_decide_eq_true rfl)) h_v42 (of_decide_eq_true rfl))
  have e_v101 : sv v101 = sv v64 - sv v42 := e_sub h_v64 h_v42 (of_decide_eq_true rfl)
  have h_v102 : R 1 0 4611686018158952441 4611686018695823367 v102 v102 := (r_psel hl h_v97 h_v101 h_v42 (of_decide_eq_true rfl))
  have e_v102 : v102 = if v97 = 1 then v101 else v42 := e_psel h_v97 h_v101 h_v42 (of_decide_eq_true rfl)
  have h_v103 : R 1 0 4611686018427387904 4611686019501129727 v103 v103 := (r1_hxa hb_H0 0 (of_decide_eq_true rfl))
  have e_v103 : sv v103 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 0 (of_decide_eq_true rfl)
  have h_v104 : R 1 0 0 1 v104 v104 := (r_sub hl (r_O hl) h_v97 (of_decide_eq_true rfl))
  have e_v104 : (v104 = 1 ↔ ¬v97 = 1) := e_not h_v97 (of_decide_eq_true rfl)
  have h_t103_1 : R 1 0 4611686018427387904 4611686018695823363 t103.1 t103.1 := r_sc1 hl h_v103 (of_decide_eq_true rfl)
  have h_t103_2 : R 1 0 4611686018158952445 4611686018695823363 t103.2 t103.2 := r_sc2 hl h_v103 (of_decide_eq_true rfl)
  have e_t103_1 : sv t103.1 = (sc28pS (scArg v103)).1 := e_sc1 h_v103 (of_decide_eq_true rfl)
  have e_t103_2 : sv t103.2 = (sc28pS (scArg v103)).2 := e_sc2 h_v103 (of_decide_eq_true rfl)
  have h_v106 : R 1 0 4611686018158952441 4611686018695823359 v106 v106 := (r_sub hl (r_add hl h_v15 h_t103_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v106 : sv v106 = sv v15 + sv t103.2 := e_add h_v15 h_t103_2 (of_decide_eq_true rfl)
  clear h_v42 h_v87 h_v90 h_v92 h_v93 h_v94 h_v95 h_v101
  have h_v107 : R 1 0 0 1 v107 v107 := (r_plt hl h_v106 h_v17 (of_decide_eq_true rfl))
  have e_v107 : (v107 = 1 ↔ sv v106 < sv v17) := e_plt h_v106 h_v17 (of_decide_eq_true rfl)
  have h_v108 : R 1 0 4611686018158952441 4611686018695823359 v108 v108 := (r_psel hl h_v107 h_v17 h_v106 (of_decide_eq_true rfl))
  have e_v108 : v108 = if v107 = 1 then v17 else v106 := e_psel h_v107 h_v17 h_v106 (of_decide_eq_true rfl)
  have h_v109 : R 1 0 4611686018158952449 4611686018695823367 v109 v109 := (r_sub hl (r_add hl h_v23 h_t103_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v109 : sv v109 = sv v23 + sv t103.2 := e_add h_v23 h_t103_2 (of_decide_eq_true rfl)
  have h_v110 : R 1 0 0 1 v110 v110 := (r_plt hl h_v109 h_v25 (of_decide_eq_true rfl))
  have e_v110 : (v110 = 1 ↔ sv v109 < sv v25) := e_plt h_v109 h_v25 (of_decide_eq_true rfl)
  have h_v111 : R 1 0 4611686018158952449 4611686018695823367 v111 v111 := (r_psel hl h_v110 h_v109 h_v25 (of_decide_eq_true rfl))
  have e_v111 : v111 = if v110 = 1 then v109 else v25 := e_psel h_v110 h_v109 h_v25 (of_decide_eq_true rfl)
  have h_v113 : R 1 0 4611686018427387908 4611686018695823367 v113 v113 := (r_sub hl (r_add hl h_v23 h_t103_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v113 : sv v113 = sv v23 + sv t103.1 := e_add h_v23 h_t103_1 (of_decide_eq_true rfl)
  have h_v114 : R 1 0 0 1 v114 v114 := (r_plt hl h_v113 h_v25 (of_decide_eq_true rfl))
  have e_v114 : (v114 = 1 ↔ sv v113 < sv v25) := e_plt h_v113 h_v25 (of_decide_eq_true rfl)
  have h_v115 : R 1 0 4611686018427387908 4611686018695823367 v115 v115 := (r_psel hl h_v114 h_v113 h_v25 (of_decide_eq_true rfl))
  have e_v115 : v115 = if v114 = 1 then v113 else v25 := e_psel h_v114 h_v113 h_v25 (of_decide_eq_true rfl)
  have h_v116 : R 1 0 4611686018427387900 4611686018695823359 v116 v116 := (r_sub hl (r_add hl h_v15 h_t103_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v116 : sv v116 = sv v15 + sv t103.1 := e_add h_v15 h_t103_1 (of_decide_eq_true rfl)
  have h_v117 : R 1 0 4611686018158952441 4611686018695823367 v117 v117 := (r_psel hl h_v104 h_v108 h_v111 (of_decide_eq_true rfl))
  have e_v117 : v117 = if v104 = 1 then v108 else v111 := e_psel h_v104 h_v108 h_v111 (of_decide_eq_true rfl)
  have h_v118 : R 1 0 4611686018427387900 4611686018695823367 v118 v118 := (r_psel hl h_v104 h_v115 h_v116 (of_decide_eq_true rfl))
  have e_v118 : v118 = if v104 = 1 then v115 else v116 := e_psel h_v104 h_v115 h_v116 (of_decide_eq_true rfl)
  have h_v119 : R 1 0 4539628418483879831 4683743618370895977 v119 v119 := (r_smx hl 29 h_v98 h_v118 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v119 : sv v119 = sv v98 * sv v118 := e_smx 29 h_v98 h_v118 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v120 : R 1 0 4539628420631363535 4683743616223412273 v120 v120 := (r_smx hl 29 h_v117 h_v102 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  clear h_v15 h_v17 h_v23 h_v25 h_v98 h_t103_1 h_t103_2 h_v106 h_v107 h_v109 h_v110 h_v111 h_v113 h_v114 h_v115 h_v116 h_v118
  have e_v120 : sv v120 = sv v117 * sv v102 := e_smx 29 h_v117 h_v102 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v121 : R 1 0 0 1 v121 v121 := (r_plt hl h_v120 h_v119 (of_decide_eq_true rfl))
  have e_v121 : (v121 = 1 ↔ sv v120 < sv v119) := e_plt h_v120 h_v119 (of_decide_eq_true rfl)
  have h_v122 : R 1 0 0 1 v122 v122 := (r_sub hl (r_O hl) h_v121 (of_decide_eq_true rfl))
  have e_v122 : (v122 = 1 ↔ ¬v121 = 1) := e_not h_v121 (of_decide_eq_true rfl)
  have h_v123 : R 1 0 0 1 v123 v123 := (r_plt hl h_v119 h_v120 (of_decide_eq_true rfl))
  have e_v123 : (v123 = 1 ↔ sv v119 < sv v120) := e_plt h_v119 h_v120 (of_decide_eq_true rfl)
  have h_v124 : R 1 0 0 1 v124 v124 := (r_sub hl (r_O hl) h_v123 (of_decide_eq_true rfl))
  have e_v124 : (v124 = 1 ↔ ¬v123 = 1) := e_not h_v123 (of_decide_eq_true rfl)
  have h_v125 : R 1 0 0 1 v125 v125 := (r_plt hl h_v64 h_v103 (of_decide_eq_true rfl))
  have e_v125 : (v125 = 1 ↔ sv v64 < sv v103) := e_plt h_v64 h_v103 (of_decide_eq_true rfl)
  have h_v126 : R 1 0 0 1 v126 v126 := (r_sub hl (r_O hl) h_v125 (of_decide_eq_true rfl))
  have e_v126 : (v126 = 1 ↔ ¬v125 = 1) := e_not h_v125 (of_decide_eq_true rfl)
  have h_v127 : R 1 0 4611686018849045332 4611686018849045332 v127 v127 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  have e_v127 : sv v127 = (421657428) := e_c 4611686018849045332 (421657428) (of_decide_eq_true rfl)
  have h_v128 : R 1 0 0 1 v128 v128 := (r_plt hl h_v127 h_v103 (of_decide_eq_true rfl))
  have e_v128 : (v128 = 1 ↔ sv v127 < sv v103) := e_plt h_v127 h_v103 (of_decide_eq_true rfl)
  have h_v129 : R 1 0 0 1 v129 v129 := (r_sub hl (r_O hl) h_v128 (of_decide_eq_true rfl))
  have e_v129 : (v129 = 1 ↔ ¬v128 = 1) := e_not h_v128 (of_decide_eq_true rfl)
  have h_v130 : R 1 0 0 1 v130 v130 := (r_plt hl h_v8 h_v108 (of_decide_eq_true rfl))
  have e_v130 : (v130 = 1 ↔ sv v8 < sv v108) := e_plt h_v8 h_v108 (of_decide_eq_true rfl)
  have h_v131 : R 1 0 0 1 v131 v131 := (r_land hl h_v122 h_v130 (of_decide_eq_true rfl))
  have e_v131 : (v131 = 1 ↔ v122 = 1 ∧ v130 = 1) := e_land h_v122 h_v130 (of_decide_eq_true rfl)
  have h_v132 : R 1 0 0 1 v132 v132 := (r_land hl h_v129 h_v131 (of_decide_eq_true rfl))
  have e_v132 : (v132 = 1 ↔ v129 = 1 ∧ v131 = 1) := e_land h_v129 h_v131 (of_decide_eq_true rfl)
  clear h_v8 h_v102 h_v108 h_v117 h_v119 h_v120 h_v121 h_v122 h_v123 h_v125 h_v127 h_v128 h_v129 h_v130 h_v131
  have h_v133 : R 1 0 0 1 v133 v133 := (r_lor hl h_v126 h_v132 (of_decide_eq_true rfl))
  have e_v133 : (v133 = 1 ↔ v126 = 1 ∨ v132 = 1) := e_lor h_v126 h_v132 (of_decide_eq_true rfl)
  have h_v134 : R 1 0 4611686018849045333 4611686018849045333 v134 v134 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have e_v134 : sv v134 = (421657429) := e_c 4611686018849045333 (421657429) (of_decide_eq_true rfl)
  have h_v135 : R 1 0 0 1 v135 v135 := (r_plt hl h_v103 h_v134 (of_decide_eq_true rfl))
  have e_v135 : (v135 = 1 ↔ sv v103 < sv v134) := e_plt h_v103 h_v134 (of_decide_eq_true rfl)
  have h_v136 : R 1 0 0 1 v136 v136 := (r_sub hl (r_O hl) h_v135 (of_decide_eq_true rfl))
  have e_v136 : (v136 = 1 ↔ ¬v135 = 1) := e_not h_v135 (of_decide_eq_true rfl)
  have h_v137 : R 1 0 0 1 v137 v137 := (r_lor hl h_v124 h_v136 (of_decide_eq_true rfl))
  have e_v137 : (v137 = 1 ↔ v124 = 1 ∨ v136 = 1) := e_lor h_v124 h_v136 (of_decide_eq_true rfl)
  have h_v138 : R 1 0 0 1 v138 v138 := (r_land hl h_v104 h_v133 (of_decide_eq_true rfl))
  have e_v138 : (v138 = 1 ↔ v104 = 1 ∧ v133 = 1) := e_land h_v104 h_v133 (of_decide_eq_true rfl)
  have h_v139 : R 1 0 0 1 v139 v139 := (r_land hl h_v97 h_v137 (of_decide_eq_true rfl))
  have e_v139 : (v139 = 1 ↔ v97 = 1 ∧ v137 = 1) := e_land h_v97 h_v137 (of_decide_eq_true rfl)
  have h_v140 : R 1 0 0 1 v140 v140 := (r_lor hl h_v138 h_v139 (of_decide_eq_true rfl))
  have e_v140 : (v140 = 1 ↔ v138 = 1 ∨ v139 = 1) := e_lor h_v138 h_v139 (of_decide_eq_true rfl)
  have h_v141 : R 1 0 4611686017353646081 4611686018427387904 v141 v141 := (r_sub hl (r_add hl h_v64 h_OFFr (of_decide_eq_true rfl)) h_v103 (of_decide_eq_true rfl))
  have e_v141 : sv v141 = sv v64 - sv v103 := e_sub h_v64 h_v103 (of_decide_eq_true rfl)
  have h_v142 : R 1 0 4611686017353646081 4611686019501129727 v142 v142 := (r_psel hl h_v97 h_v141 h_v103 (of_decide_eq_true rfl))
  have e_v142 : v142 = if v97 = 1 then v141 else v103 := e_psel h_v97 h_v141 h_v103 (of_decide_eq_true rfl)
  have h_v143 : R 1 0 4611686018005730475 4611686018005730475 v143 v143 := (r_c hl 4611686018005730475 (of_decide_eq_true rfl))
  have e_v143 : sv v143 = (-421657429) := e_c 4611686018005730475 (-421657429) (of_decide_eq_true rfl)
  have h_v144 : R 1 0 4611686017353646081 4611686019501129727 v144 v144 := (r_psel hl h_v140 h_v142 h_v143 (of_decide_eq_true rfl))
  have e_v144 : v144 = if v140 = 1 then v142 else v143 := e_psel h_v140 h_v142 h_v143 (of_decide_eq_true rfl)
  have h_v186 : R 1 0 4611686017353646081 4611686019501129727 v186 v186 := (r_psel hl h_v96 h_v143 h_v144 (of_decide_eq_true rfl))
  clear h_v64 h_v97 h_v103 h_v104 h_v124 h_v126 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140 h_v141 h_v142
  have e_v186 : v186 = if v96 = 1 then v143 else v144 := e_psel h_v96 h_v143 h_v144 (of_decide_eq_true rfl)
  have h_v188 : R 1 0 4611686016279904258 4611686020574871550 v188 v188 := (r_sub hl (r_add hl h_v186 h_v186 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v188 : sv v188 = sv v186 + sv v186 := e_add h_v186 h_v186 (of_decide_eq_true rfl)
  have h_v190 : R 1 0 0 1 v190 v190 := (r_plt hl h_v188 h_v5 (of_decide_eq_true rfl))
  have e_v190 : (v190 = 1 ↔ sv v188 < sv v5) := e_plt h_v188 h_v5 (of_decide_eq_true rfl)
  have h_v191 : R 1 0 0 1 v191 v191 := (r_sub hl (r_O hl) h_v190 (of_decide_eq_true rfl))
  have e_v191 : (v191 = 1 ↔ ¬v190 = 1) := e_not h_v190 (of_decide_eq_true rfl)
  have h_v194 : R 1 0 0 1 v194 v194 := (r_plt hl h_v6 h_v0 (of_decide_eq_true rfl))
  have e_v194 : (v194 = 1 ↔ sv v6 < sv v0) := e_plt h_v6 h_v0 (of_decide_eq_true rfl)
  have h_v195 : R 1 0 0 1 v195 v195 := (r_sub hl (r_O hl) h_v194 (of_decide_eq_true rfl))
  have e_v195 : (v195 = 1 ↔ ¬v194 = 1) := e_not h_v194 (of_decide_eq_true rfl)
  have h_v196 : R 1 0 0 1 v196 v196 := (r_land hl h_v191 h_v195 (of_decide_eq_true rfl))
  have e_v196 : (v196 = 1 ↔ v191 = 1 ∧ v195 = 1) := e_land h_v191 h_v195 (of_decide_eq_true rfl)
  have h_v198 : R 1 0 0 1 v198 v198 := (r_land hl h_v13 h_v36 (of_decide_eq_true rfl))
  have e_v198 : (v198 = 1 ↔ v13 = 1 ∧ v36 = 1) := e_land h_v13 h_v36 (of_decide_eq_true rfl)
  have h_v199 : R 1 0 0 1 v199 v199 := (r_land hl h_v36 h_v198 (of_decide_eq_true rfl))
  have e_v199 : (v199 = 1 ↔ v36 = 1 ∧ v198 = 1) := e_land h_v36 h_v198 (of_decide_eq_true rfl)
  have h_v200 : R 1 0 0 1 v200 v200 := (r_land hl h_v78 h_v199 (of_decide_eq_true rfl))
  have e_v200 : (v200 = 1 ↔ v78 = 1 ∧ v199 = 1) := e_land h_v78 h_v199 (of_decide_eq_true rfl)
  have h_v201 : R 1 0 0 1 v201 v201 := (r_land hl h_v36 h_v200 (of_decide_eq_true rfl))
  have e_v201 : (v201 = 1 ↔ v36 = 1 ∧ v200 = 1) := e_land h_v36 h_v200 (of_decide_eq_true rfl)
  have h_v202 : R 1 0 0 1 v202 v202 := (r_land hl h_v36 h_v201 (of_decide_eq_true rfl))
  have e_v202 : (v202 = 1 ↔ v36 = 1 ∧ v201 = 1) := e_land h_v36 h_v201 (of_decide_eq_true rfl)
  have h_v203 : R 1 0 0 1 v203 v203 := (r_land hl h_v78 h_v202 (of_decide_eq_true rfl))
  have e_v203 : (v203 = 1 ↔ v78 = 1 ∧ v202 = 1) := e_land h_v78 h_v202 (of_decide_eq_true rfl)
  clear h_OFFr h_v0 h_v5 h_v6 h_v13 h_v36 h_v78 h_v96 h_v143 h_v144 h_v186 h_v188 h_v190 h_v191 h_v194 h_v195 h_v198 h_v199 h_v200 h_v201 h_v202
  have h_v204 : R 1 0 0 1 v204 v204 := (r_land hl h_v196 h_v203 (of_decide_eq_true rfl))
  have e_v204 : (v204 = 1 ↔ v196 = 1 ∧ v203 = 1) := e_land h_v196 h_v203 (of_decide_eq_true rfl)
  have k_v204 : v204 = 1 := h
  have k_v196 : v196 = 1 := ((e_v204).1 k_v204).1
  have k_v203 : v203 = 1 := ((e_v204).1 k_v204).2
  have k_v78 : v78 = 1 := ((e_v203).1 k_v203).1
  have k_v202 : v202 = 1 := ((e_v203).1 k_v203).2
  have k_v36 : v36 = 1 := ((e_v202).1 k_v202).1
  have k_v201 : v201 = 1 := ((e_v202).1 k_v202).2
  have k_v200 : v200 = 1 := ((e_v201).1 k_v201).2
  have k_v199 : v199 = 1 := ((e_v200).1 k_v200).2
  have k_v198 : v198 = 1 := ((e_v199).1 k_v199).2
  have k_v13 : v13 = 1 := ((e_v198).1 k_v198).1
  have k_v9 : v9 = 1 := ((e_v13).1 k_v13).1
  have k_v12 : v12 = 1 := ((e_v13).1 k_v13).2
  have k_v33 : v33 = 1 := ((e_v36).1 k_v36).1
  have k_v35 : v35 = 1 := ((e_v36).1 k_v36).2
  have k_v191 : v191 = 1 := ((e_v196).1 k_v196).1
  have k_v195 : v195 = 1 := ((e_v196).1 k_v196).2
  have f3 := L2.K8_in_range True (sv v6) (sv v6) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f13 := L2.K3_cos_lo (sv v6) (sv t6.2) (sv v16) (sv v17) (sv v19) (L2.p_cos e_t6_2) (L2.p_addc (-4) e_v16 e_v15) e_v17 (L2.p_max e_v18 (L2.p_sel e_v19))
  have f27 := L2.K3_cos_hi (sv v6) (sv t6.2) (sv v24) (sv v25) (sv v27) (L2.p_cos e_t6_2) (L2.p_addc (4) e_v24 e_v23) e_v25 (L2.p_min e_v26 (L2.p_sel e_v27))
  have f2 := L2.K10_icos True (sv v6) (sv v6) (sv v19) (sv v17) v21 (sv v22) (sv v27) (sv v25) v29 (sv v30) f3 f13 e_v17 (L2.p_clt (843314855) e_v20 e_v21) (L2.p_sel e_v22) f27 e_v25 (L2.p_ltc (1) e_v28 e_v29) (L2.p_sel e_v30)
  have f42 := L2.K5_ihalf (sv v3) (sv v3) (sv v31) (sv v32) e_v31 e_v32
  have f46 := L2.K8_in_range True (sv v31) (sv v32) v33 (sv v10) v35 v36 (L2.p_clt (-1) e_v8 e_v33) e_v10 (L2.p_le e_v34 e_v35) e_v36 (L2.X1_top _ k_v36)
  have f56 := L2.K3_cos_lo (sv v32) (sv t32.2) (sv v38) (sv v17) (sv v40) (L2.p_cos e_t32_2) (L2.p_addc (-4) (L2.p_add_comm e_v38) e_v15) e_v17 (L2.p_max e_v39 (L2.p_sel e_v40))
  let u43 : ℤ := L2.cosI (sv v31)
  let u44 : ℤ := (sv v23) + u43
  let u45 : ℕ := if u44 < (sv v25) then 1 else 0
  let u46 : ℤ := if u45 = 1 then u44 else (sv v25)
  have f70 := L2.K3_cos_hi (sv v31) u43 u44 (sv v25) u46 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  let u47 : ℕ := if (sv v31) < (sv v28) then 1 else 0
  let u48 : ℤ := if u47 = 1 then (sv v25) else u46
  have f45 := L2.K10_icos True (sv v31) (sv v32) (sv v40) (sv v17) v41 (sv v42) u46 (sv v25) u47 u48 f46 f56 e_v17 (L2.p_clt (843314855) e_v20 e_v41) (L2.p_sel e_v42) f70 e_v25 (L2.p_ltc (1) e_v28 (L2.p_ult _ _)) rfl
  have f85 := L2.K8_in_range True (sv v31) (sv v32) v33 (sv v10) v35 v36 (L2.p_clt (-1) e_v8 e_v33) e_v10 (L2.p_le e_v34 e_v35) e_v36 (L2.X1_top _ k_v36)
  have f84 := L2.K9_isin True (sv v31) (sv v32) (sv t31.1) (sv t32.1) (sv v52) (sv v53) (sv v54) (sv v55) (sv v25) (sv v57) v59 v61 v62 (sv v63) f85 (L2.p_sin e_t31_1) (L2.p_sin e_t32_1) (L2.p_min e_v51 (L2.p_sel e_v52)) (L2.p_addc (-4) (L2.p_add_comm e_v53) e_v15) (L2.p_max e_v51 (L2.p_sel e_v54)) (L2.p_addc (4) (L2.p_add_comm e_v55) e_v23) e_v25 (L2.p_min e_v56 (L2.p_sel e_v57)) (L2.p_ltc (421657430) e_v58 e_v59) (L2.p_clt (421657427) e_v60 e_v61) e_v62 (L2.p_sel e_v63)
  have f121 := L2.K6_imul True (sv v22) (sv v30) (sv v53) (sv v63) (sv v64) v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 (sv v81) v82 v83 (sv v84) v85 v86 (sv v87) v88 v89 (sv v90) (sv v92) (sv v94) e_v64 e_v65 e_v66 e_v67 e_v68 (L2.p_and_comm e_v69) e_v70 e_v71 e_v72 e_v73 e_v74 (L2.p_and_comm e_v75) e_v76 e_v77 e_v78 (L2.X1_top _ k_v78) e_v79 e_v80 (L2.p_sel e_v81) e_v82 e_v83 (L2.p_sel e_v84) e_v85 e_v86 (L2.p_sel e_v87) e_v88 e_v89 (L2.p_sel e_v90) (L2.p_mul (L2.p_mul_comm e_v91) e_v92) (L2.p_mulc (L2.p_mul_comm e_v93) e_v94)
  let u99 : ℕ := if u48 < (sv v64) then 1 else 0
  let u100 : ℤ := if u99 = 1 then (sv v94) else (sv v92)
  have f154 := L2.K11_qdiv (sv v42) u48 (sv v92) (sv v94) v95 v96 (sv v64) v97 (sv v98) u99 u100 (L2.p_clt (0) e_v64 e_v95) e_v96 e_v64 e_v97 (L2.p_sel e_v98) (L2.p_ult _ _) rfl
  have f172 := L2.K3_cos_lo (sv v103) (sv t103.2) (sv v106) (sv v17) (sv v108) (L2.p_cos e_t103_2) (L2.p_addc (-4) (L2.p_add_comm e_v106) e_v15) e_v17 (L2.p_max e_v107 (L2.p_sel e_v108))
  have f181 := L2.K3_cos_hi (sv v103) (sv t103.2) (sv v109) (sv v25) (sv v111) (L2.p_cos e_t103_2) (L2.p_addc (4) (L2.p_add_comm e_v109) e_v23) e_v25 (L2.p_min e_v110 (L2.p_sel e_v111))
  have f190 := L2.K3_sin_hi (sv v103) (sv t103.1) (sv v113) (sv v25) (sv v115) (L2.p_sin e_t103_1) (L2.p_addc (4) (L2.p_add_comm e_v113) e_v23) e_v25 (L2.p_min e_v114 (L2.p_sel e_v115))
  have f199 := L2.K3_sin_lo (sv v103) (sv t103.1) (sv v116) (L2.p_sin e_t103_1) (L2.p_addc (-4) (L2.p_add_comm e_v116) e_v15)
  have f165 := L2.K12_atan_lo (sv v42) (sv v98) (sv v64) v97 (sv v101) (sv v102) (sv v103) v104 (sv v108) (sv v111) (sv v115) (sv v116) (sv v117) (sv v118) (sv v119) (sv v120) v122 v124 v125 v126 (sv v127) v129 v130 v131 v132 v133 (sv v134) v136 v137 v138 v97 v139 v140 (sv v141) (sv v142) (sv v143) (sv v144) e_v64 e_v97 e_v101 (L2.p_sel e_v102) (L2.p_hint e_v103) e_v104 f172 f181 f190 f199 (L2.p_sel e_v117) (L2.p_sel e_v118) (L2.p_mul_comm e_v119) (L2.p_mul_comm e_v120) (L2.p_le e_v121 e_v122) (L2.p_le e_v123 e_v124) e_v125 e_v126 e_v127 (L2.p_le e_v128 e_v129) (L2.p_clt (-1) e_v8 e_v130) e_v131 (L2.p_and_comm e_v132) e_v133 e_v134 (L2.p_le e_v135 e_v136) (L2.p_or_comm e_v137) e_v138 (L2.p_not_not e_v104) e_v139 e_v140 e_v141 (L2.p_sel e_v142) e_v143 (L2.p_sel e_v144)
  let u145 : ℤ := (sv v64) - u48
  let u146 : ℤ := if u99 = 1 then u145 else u48
  let u147 : ℤ := 0
  let u148 : ℤ := L2.cosI u147
  let u149 : ℤ := (sv v15) + u148
  let u150 : ℕ := if u149 < (sv v17) then 1 else 0
  let u151 : ℤ := if u150 = 1 then (sv v17) else u149
  have f245 := L2.K3_cos_lo u147 u148 u149 (sv v17) u151 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u152 : ℤ := (sv v23) + u148
  let u153 : ℕ := if u152 < (sv v25) then 1 else 0
  let u154 : ℤ := if u153 = 1 then u152 else (sv v25)
  have f254 := L2.K3_cos_hi u147 u148 u152 (sv v25) u154 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  let u155 : ℤ := L2.sinI u147
  let u156 : ℤ := (sv v23) + u155
  let u157 : ℕ := if u156 < (sv v25) then 1 else 0
  let u158 : ℤ := if u157 = 1 then u156 else (sv v25)
  have f263 := L2.K3_sin_hi u147 u155 u156 (sv v25) u158 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  let u159 : ℤ := (sv v15) + u155
  have f272 := L2.K3_sin_lo u147 u155 u159 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15)
  let u160 : ℤ := if u99 = 1 then u151 else u154
  let u161 : ℤ := if u99 = 1 then u158 else u159
  let u162 : ℤ := u100 * u161
  let u163 : ℤ := u146 * u160
  let u164 : ℕ := if u163 < u162 then 1 else 0
  let u165 : ℕ := if u164 = 1 then 0 else 1
  let u166 : ℕ := if u162 < u163 then 1 else 0
  let u167 : ℕ := if u166 = 1 then 0 else 1
  let u168 : ℕ := if (sv v64) < u147 then 1 else 0
  let u169 : ℕ := if u168 = 1 then 0 else 1
  let u170 : ℕ := if (sv v127) < u147 then 1 else 0
  let u171 : ℕ := if u170 = 1 then 0 else 1
  let u172 : ℕ := if (sv v8) < u151 then 1 else 0
  let u173 : ℕ := if u165 = 1 ∧ u172 = 1 then 1 else 0
  let u174 : ℕ := if u171 = 1 ∧ u173 = 1 then 1 else 0
  let u175 : ℕ := if u169 = 1 ∨ u174 = 1 then 1 else 0
  let u176 : ℕ := if u147 < (sv v134) then 1 else 0
  let u177 : ℕ := if u176 = 1 then 0 else 1
  let u178 : ℕ := if u167 = 1 ∨ u177 = 1 then 1 else 0
  let u179 : ℕ := if u99 = 1 ∧ u175 = 1 then 1 else 0
  let u180 : ℕ := if u99 = 1 then 0 else 1
  let u181 : ℕ := if u178 = 1 ∧ u180 = 1 then 1 else 0
  let u182 : ℕ := if u179 = 1 ∨ u181 = 1 then 1 else 0
  let u183 : ℤ := (sv v64) - u147
  let u184 : ℤ := if u99 = 1 then u183 else u147
  let u185 : ℤ := if u182 = 1 then u184 else (sv v134)
  have f239 := L2.K12_atan_hi u48 u100 (sv v64) u99 u145 u146 u147 u151 u154 u158 u159 u160 u161 u162 u163 u165 u167 u168 u169 (sv v127) u171 u172 u173 u174 u175 (sv v134) u177 u178 u179 u180 u181 u182 u183 u184 (sv v134) u185 e_v64 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f245 f254 f263 f272 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v127 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v134 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v134 rfl
  let u187 : ℤ := if v96 = 1 then (sv v134) else u185
  have f41 := L2.K19_iso_angle_pt True (sv v3) (sv v22) (sv v30) (sv v31) (sv v32) (sv v42) u48 (sv v53) (sv v63) (sv v92) (sv v94) (sv v98) u100 v96 v95 (sv v144) u185 (sv v143) (sv v134) (sv v186) u187 f42 f45 f84 f121 f154 (L2.p_not_not e_v96) f165 f239 e_v143 e_v134 (L2.p_sel e_v186) rfl
  have f317 := L2.K5_ihalf (sv v3) (sv v3) (sv v31) (sv v32) e_v31 e_v32
  have f321 := L2.K8_in_range True (sv v31) (sv v32) v33 (sv v10) v35 v36 (L2.p_clt (-1) e_v8 e_v33) e_v10 (L2.p_le e_v34 e_v35) e_v36 (L2.X1_top _ k_v36)
  have f331 := L2.K3_cos_lo (sv v32) (sv t32.2) (sv v38) (sv v17) (sv v40) (L2.p_cos e_t32_2) (L2.p_addc (-4) (L2.p_add_comm e_v38) e_v15) e_v17 (L2.p_max e_v39 (L2.p_sel e_v40))
  have f345 := L2.K3_cos_hi (sv v31) u43 u44 (sv v25) u46 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  have f320 := L2.K10_icos True (sv v31) (sv v32) (sv v40) (sv v17) v41 (sv v42) u46 (sv v25) u47 u48 f321 f331 e_v17 (L2.p_clt (843314855) e_v20 e_v41) (L2.p_sel e_v42) f345 e_v25 (L2.p_ltc (1) e_v28 (L2.p_ult _ _)) rfl
  have f360 := L2.K8_in_range True (sv v31) (sv v32) v33 (sv v10) v35 v36 (L2.p_clt (-1) e_v8 e_v33) e_v10 (L2.p_le e_v34 e_v35) e_v36 (L2.X1_top _ k_v36)
  have f359 := L2.K9_isin True (sv v31) (sv v32) (sv t31.1) (sv t32.1) (sv v52) (sv v53) (sv v54) (sv v55) (sv v25) (sv v57) v59 v61 v62 (sv v63) f360 (L2.p_sin e_t31_1) (L2.p_sin e_t32_1) (L2.p_min e_v51 (L2.p_sel e_v52)) (L2.p_addc (-4) (L2.p_add_comm e_v53) e_v15) (L2.p_max e_v51 (L2.p_sel e_v54)) (L2.p_addc (4) (L2.p_add_comm e_v55) e_v23) e_v25 (L2.p_min e_v56 (L2.p_sel e_v57)) (L2.p_ltc (421657430) e_v58 e_v59) (L2.p_clt (421657427) e_v60 e_v61) e_v62 (L2.p_sel e_v63)
  have f396 := L2.K6_imul True (sv v22) (sv v30) (sv v53) (sv v63) (sv v64) v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 (sv v81) v82 v83 (sv v84) v85 v86 (sv v87) v88 v89 (sv v90) (sv v92) (sv v94) e_v64 e_v65 e_v66 e_v67 e_v68 (L2.p_and_comm e_v69) e_v70 e_v71 e_v72 e_v73 e_v74 (L2.p_and_comm e_v75) e_v76 e_v77 e_v78 (L2.X1_top _ k_v78) e_v79 e_v80 (L2.p_sel e_v81) e_v82 e_v83 (L2.p_sel e_v84) e_v85 e_v86 (L2.p_sel e_v87) e_v88 e_v89 (L2.p_sel e_v90) (L2.p_mul (L2.p_mul_comm e_v91) e_v92) (L2.p_mulc (L2.p_mul_comm e_v93) e_v94)
  have f429 := L2.K11_qdiv (sv v42) u48 (sv v92) (sv v94) v95 v96 (sv v64) v97 (sv v98) u99 u100 (L2.p_clt (0) e_v64 e_v95) e_v96 e_v64 e_v97 (L2.p_sel e_v98) (L2.p_ult _ _) rfl
  have f447 := L2.K3_cos_lo (sv v103) (sv t103.2) (sv v106) (sv v17) (sv v108) (L2.p_cos e_t103_2) (L2.p_addc (-4) (L2.p_add_comm e_v106) e_v15) e_v17 (L2.p_max e_v107 (L2.p_sel e_v108))
  have f456 := L2.K3_cos_hi (sv v103) (sv t103.2) (sv v109) (sv v25) (sv v111) (L2.p_cos e_t103_2) (L2.p_addc (4) (L2.p_add_comm e_v109) e_v23) e_v25 (L2.p_min e_v110 (L2.p_sel e_v111))
  have f465 := L2.K3_sin_hi (sv v103) (sv t103.1) (sv v113) (sv v25) (sv v115) (L2.p_sin e_t103_1) (L2.p_addc (4) (L2.p_add_comm e_v113) e_v23) e_v25 (L2.p_min e_v114 (L2.p_sel e_v115))
  have f474 := L2.K3_sin_lo (sv v103) (sv t103.1) (sv v116) (L2.p_sin e_t103_1) (L2.p_addc (-4) (L2.p_add_comm e_v116) e_v15)
  have f440 := L2.K12_atan_lo (sv v42) (sv v98) (sv v64) v97 (sv v101) (sv v102) (sv v103) v104 (sv v108) (sv v111) (sv v115) (sv v116) (sv v117) (sv v118) (sv v119) (sv v120) v122 v124 v125 v126 (sv v127) v129 v130 v131 v132 v133 (sv v134) v136 v137 v138 v97 v139 v140 (sv v141) (sv v142) (sv v143) (sv v144) e_v64 e_v97 e_v101 (L2.p_sel e_v102) (L2.p_hint e_v103) e_v104 f447 f456 f465 f474 (L2.p_sel e_v117) (L2.p_sel e_v118) (L2.p_mul_comm e_v119) (L2.p_mul_comm e_v120) (L2.p_le e_v121 e_v122) (L2.p_le e_v123 e_v124) e_v125 e_v126 e_v127 (L2.p_le e_v128 e_v129) (L2.p_clt (-1) e_v8 e_v130) e_v131 (L2.p_and_comm e_v132) e_v133 e_v134 (L2.p_le e_v135 e_v136) (L2.p_or_comm e_v137) e_v138 (L2.p_not_not e_v104) e_v139 e_v140 e_v141 (L2.p_sel e_v142) e_v143 (L2.p_sel e_v144)
  have f520 := L2.K3_cos_lo u147 u148 u149 (sv v17) u151 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  have f529 := L2.K3_cos_hi u147 u148 u152 (sv v25) u154 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  have f538 := L2.K3_sin_hi u147 u155 u156 (sv v25) u158 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  have f547 := L2.K3_sin_lo u147 u155 u159 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15)
  have f514 := L2.K12_atan_hi u48 u100 (sv v64) u99 u145 u146 u147 u151 u154 u158 u159 u160 u161 u162 u163 u165 u167 u168 u169 (sv v127) u171 u172 u173 u174 u175 (sv v134) u177 u178 u179 u180 u181 u182 u183 u184 (sv v134) u185 e_v64 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f520 f529 f538 f547 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v127 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v134 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v134 rfl
  have f316 := L2.K19_iso_angle_pt True (sv v3) (sv v22) (sv v30) (sv v31) (sv v32) (sv v42) u48 (sv v53) (sv v63) (sv v92) (sv v94) (sv v98) u100 v96 v95 (sv v144) u185 (sv v143) (sv v134) (sv v186) u187 f317 f320 f359 f396 f429 (L2.p_not_not e_v96) f440 f514 e_v143 e_v134 (L2.p_sel e_v186) rfl
  have f1 := L2.K20_iso_angle True (sv v3) (sv v3) (sv v6) (sv v6) (sv v22) (sv v30) (sv v186) u187 v96 (sv v186) u187 v96 f2 f41 f316
  let u189 : ℤ := u187 + u187
  have f591 := L2.K4_iadd (sv v186) u187 (sv v186) u187 (sv v188) u189 e_v188 rfl
  let u192 : ℕ := if (sv v5) < u189 then 1 else 0
  let u193 : ℕ := if u192 = 1 then 0 else 1
  exact Tammes15.D3Trig.TDH F0 F1 F2 F3 hD (sv v0) (sv v3) (sv v5) (sv v6) (0 : ℕ) (sv v186) u187 (sv v188) u189 v191 u193 v191 v195 v196 e_v0 e_v3 e_v5 e_v6 (of_decide_eq_true rfl) f1 f591 (L2.p_le e_v190 e_v191) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_sel_f _ _) (L2.p_le e_v194 e_v195) e_v196 (L2.X1_top _ k_v196)

end Tammes15.D3Trig
