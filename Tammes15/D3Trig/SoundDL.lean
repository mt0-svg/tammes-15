import Tammes15.D3Trig.Prog.DL
import Tammes15.D3Prog.L2.Kinds
import Tammes15.D3Prog.L2.PLib
import Tammes15.D3Trig.RhoKinds

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem progDL_l2 (F0 F1 F2 F3 H0 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (h : Tammes15.D3Trig.progDL 1 F0 F1 F2 F3 H0 = 1) (hD : D3Prog.L2.InDom F0 F1 F2 F3) : LaneClaimR 1 false F0 F1 F2 F3 := by
  unfold Tammes15.D3Trig.progDL at h
  extract_lets -merge OFFr H61r v1 v2 v4 v6 v8 v9 v10 v11 v12 v13 t6 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 t31 v44 v45 v46 v47 v48 t32 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v99 v100 v127 v134 v145 v146 v147 t147 v149 v150 v151 v152 v153 v154 v156 v157 v158 v159 v160 v161 v162 v163 v164 v165 v166 v167 v168 v169 v170 v171 v172 v173 v174 v175 v176 v177 v178 v179 v180 v181 v182 v183 v184 v185 v187 v189 v192 v193 v194 v195 v196 v197 v198 v199 v200 v201 v202 v203 at h
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have e_OFFr : sv OFFr = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have h_H61r : R 1 0 2305843009213693952 2305843009213693952 H61r H61r := (r_c hl 2305843009213693952 (of_decide_eq_true rfl))
  have e_H61r : sv H61r = (-2305843009213693952) := e_c 2305843009213693952 (-2305843009213693952) (of_decide_eq_true rfl)
  have h_v1 : R 1 0 4611686018427387904 4611686087146864624 v1 v1 := (r1_ix hb_F0 32 (of_decide_eq_true rfl))
  have e_v1 : sv v1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F0 32 (of_decide_eq_true rfl)
  have h_v2 : R 1 0 4611686018427387904 4611686087146864624 v2 v2 := (r1_ix hb_F1 0 (of_decide_eq_true rfl))
  have e_v2 : sv v2 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F1 0 (of_decide_eq_true rfl)
  have h_v4 : R 1 0 4611686018427387904 4611686087146864624 v4 v4 := (r1_ix hb_F2 0 (of_decide_eq_true rfl))
  have e_v4 : sv v4 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F2 0 (of_decide_eq_true rfl)
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
  clear h_t6_2 e_t6_1 h_v16 h_v18 h_v19 h_v20 h_v21
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
  have h_v31 : R 1 0 4611686018427387904 4611686052787126264 v31 v31 := (r_add hl (r_pshr1 hl h_v2) h_H61r (of_decide_eq_true rfl))
  have e_v31 : sv v31 = sv v2 / 2 := e_halfF h_v2
  have h_v32 : R 1 0 4611686018427387904 4611686052787126264 v32 v32 := (r_add hl (r_pshr1 hl (r_add hl h_v2 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v32 : sv v32 = (sv v2 + 1) / 2 := e_halfC h_v2 (of_decide_eq_true rfl)
  have h_v33 : R 1 0 0 1 v33 v33 := (r_plt hl h_v8 h_v31 (of_decide_eq_true rfl))
  have e_v33 : (v33 = 1 ↔ sv v8 < sv v31) := e_plt h_v8 h_v31 (of_decide_eq_true rfl)
  have h_v34 : R 1 0 0 1 v34 v34 := (r_plt hl h_v10 h_v32 (of_decide_eq_true rfl))
  have e_v34 : (v34 = 1 ↔ sv v10 < sv v32) := e_plt h_v10 h_v32 (of_decide_eq_true rfl)
  have h_v35 : R 1 0 0 1 v35 v35 := (r_sub hl (r_O hl) h_v34 (of_decide_eq_true rfl))
  have e_v35 : (v35 = 1 ↔ ¬v34 = 1) := e_not h_v34 (of_decide_eq_true rfl)
  have h_v36 : R 1 0 0 1 v36 v36 := (r_land hl h_v33 h_v35 (of_decide_eq_true rfl))
  have e_v36 : (v36 = 1 ↔ v33 = 1 ∧ v35 = 1) := e_land h_v33 h_v35 (of_decide_eq_true rfl)
  have h_t31_1 : R 1 0 4611686018427387904 4611686018695823363 t31.1 t31.1 := r_sc1 hl h_v31 (of_decide_eq_true rfl)
  have h_t31_2 : R 1 0 4611686018158952445 4611686018695823363 t31.2 t31.2 := r_sc2 hl h_v31 (of_decide_eq_true rfl)
  have e_t31_1 : sv t31.1 = (sc28pS (scArg v31)).1 := e_sc1 h_v31 (of_decide_eq_true rfl)
  clear h_H61r h_v2 h_v10 h_v24 h_v26 h_v27 h_v29 h_v33 h_v34 h_v35
  have e_t31_2 : sv t31.2 = (sc28pS (scArg v31)).2 := e_sc2 h_v31 (of_decide_eq_true rfl)
  have h_v44 : R 1 0 4611686018158952449 4611686018695823367 v44 v44 := (r_sub hl (r_add hl h_v23 h_t31_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v44 : sv v44 = sv v23 + sv t31.2 := e_add h_v23 h_t31_2 (of_decide_eq_true rfl)
  have h_v45 : R 1 0 0 1 v45 v45 := (r_plt hl h_v44 h_v25 (of_decide_eq_true rfl))
  have e_v45 : (v45 = 1 ↔ sv v44 < sv v25) := e_plt h_v44 h_v25 (of_decide_eq_true rfl)
  have h_v46 : R 1 0 4611686018158952449 4611686018695823367 v46 v46 := (r_psel hl h_v45 h_v44 h_v25 (of_decide_eq_true rfl))
  have e_v46 : v46 = if v45 = 1 then v44 else v25 := e_psel h_v45 h_v44 h_v25 (of_decide_eq_true rfl)
  have h_v47 : R 1 0 0 1 v47 v47 := (r_plt hl h_v31 h_v28 (of_decide_eq_true rfl))
  have e_v47 : (v47 = 1 ↔ sv v31 < sv v28) := e_plt h_v31 h_v28 (of_decide_eq_true rfl)
  have h_v48 : R 1 0 4611686018158952449 4611686018695823367 v48 v48 := (r_psel hl h_v47 h_v25 h_v46 (of_decide_eq_true rfl))
  have e_v48 : v48 = if v47 = 1 then v25 else v46 := e_psel h_v47 h_v25 h_v46 (of_decide_eq_true rfl)
  have h_t32_1 : R 1 0 4611686018427387904 4611686018695823363 t32.1 t32.1 := r_sc1 hl h_v32 (of_decide_eq_true rfl)
  have h_t32_2 : R 1 0 4611686018158952445 4611686018695823363 t32.2 t32.2 := r_sc2 hl h_v32 (of_decide_eq_true rfl)
  have e_t32_1 : sv t32.1 = (sc28pS (scArg v32)).1 := e_sc1 h_v32 (of_decide_eq_true rfl)
  have e_t32_2 : sv t32.2 = (sc28pS (scArg v32)).2 := e_sc2 h_v32 (of_decide_eq_true rfl)
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
  clear h_v28 h_t31_1 h_t31_2 h_v44 h_v45 h_v46 h_v47 h_t32_1 h_t32_2 e_t32_2 h_v51 h_v52 h_v54
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
  have h_v99 : R 1 0 0 1 v99 v99 := (r_plt hl h_v48 h_v64 (of_decide_eq_true rfl))
  have e_v99 : (v99 = 1 ↔ sv v48 < sv v64) := e_plt h_v48 h_v64 (of_decide_eq_true rfl)
  have h_v100 : R 1 0 4611686018158952433 4611686018695823375 v100 v100 := (r_psel hl h_v99 h_v94 h_v92 (of_decide_eq_true rfl))
  have e_v100 : v100 = if v99 = 1 then v94 else v92 := e_psel h_v99 h_v94 h_v92 (of_decide_eq_true rfl)
  have h_v127 : R 1 0 4611686018849045332 4611686018849045332 v127 v127 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  have e_v127 : sv v127 = (421657428) := e_c 4611686018849045332 (421657428) (of_decide_eq_true rfl)
  have h_v134 : R 1 0 4611686018849045333 4611686018849045333 v134 v134 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have e_v134 : sv v134 = (421657429) := e_c 4611686018849045333 (421657429) (of_decide_eq_true rfl)
  have h_v145 : R 1 0 4611686018158952441 4611686018695823359 v145 v145 := (r_sub hl (r_add hl h_v64 h_OFFr (of_decide_eq_true rfl)) h_v48 (of_decide_eq_true rfl))
  have e_v145 : sv v145 = sv v64 - sv v48 := e_sub h_v64 h_v48 (of_decide_eq_true rfl)
  have h_v146 : R 1 0 4611686018158952441 4611686018695823367 v146 v146 := (r_psel hl h_v99 h_v145 h_v48 (of_decide_eq_true rfl))
  have e_v146 : v146 = if v99 = 1 then v145 else v48 := e_psel h_v99 h_v145 h_v48 (of_decide_eq_true rfl)
  have h_v147 : R 1 0 4611686018427387904 4611686019501129727 v147 v147 := (r1_hxa hb_H0 0 (of_decide_eq_true rfl))
  have e_v147 : sv v147 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 0 (of_decide_eq_true rfl)
  have h_t147_1 : R 1 0 4611686018427387904 4611686018695823363 t147.1 t147.1 := r_sc1 hl h_v147 (of_decide_eq_true rfl)
  have h_t147_2 : R 1 0 4611686018158952445 4611686018695823363 t147.2 t147.2 := r_sc2 hl h_v147 (of_decide_eq_true rfl)
  have e_t147_1 : sv t147.1 = (sc28pS (scArg v147)).1 := e_sc1 h_v147 (of_decide_eq_true rfl)
  have e_t147_2 : sv t147.2 = (sc28pS (scArg v147)).2 := e_sc2 h_v147 (of_decide_eq_true rfl)
  clear h_v48 h_v87 h_v90 h_v92 h_v93 h_v94 h_v95 h_v145
  have h_v149 : R 1 0 4611686018158952441 4611686018695823359 v149 v149 := (r_sub hl (r_add hl h_v15 h_t147_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v149 : sv v149 = sv v15 + sv t147.2 := e_add h_v15 h_t147_2 (of_decide_eq_true rfl)
  have h_v150 : R 1 0 0 1 v150 v150 := (r_plt hl h_v149 h_v17 (of_decide_eq_true rfl))
  have e_v150 : (v150 = 1 ↔ sv v149 < sv v17) := e_plt h_v149 h_v17 (of_decide_eq_true rfl)
  have h_v151 : R 1 0 4611686018158952441 4611686018695823359 v151 v151 := (r_psel hl h_v150 h_v17 h_v149 (of_decide_eq_true rfl))
  have e_v151 : v151 = if v150 = 1 then v17 else v149 := e_psel h_v150 h_v17 h_v149 (of_decide_eq_true rfl)
  have h_v152 : R 1 0 4611686018158952449 4611686018695823367 v152 v152 := (r_sub hl (r_add hl h_v23 h_t147_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v152 : sv v152 = sv v23 + sv t147.2 := e_add h_v23 h_t147_2 (of_decide_eq_true rfl)
  have h_v153 : R 1 0 0 1 v153 v153 := (r_plt hl h_v152 h_v25 (of_decide_eq_true rfl))
  have e_v153 : (v153 = 1 ↔ sv v152 < sv v25) := e_plt h_v152 h_v25 (of_decide_eq_true rfl)
  have h_v154 : R 1 0 4611686018158952449 4611686018695823367 v154 v154 := (r_psel hl h_v153 h_v152 h_v25 (of_decide_eq_true rfl))
  have e_v154 : v154 = if v153 = 1 then v152 else v25 := e_psel h_v153 h_v152 h_v25 (of_decide_eq_true rfl)
  have h_v156 : R 1 0 4611686018427387908 4611686018695823367 v156 v156 := (r_sub hl (r_add hl h_v23 h_t147_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v156 : sv v156 = sv v23 + sv t147.1 := e_add h_v23 h_t147_1 (of_decide_eq_true rfl)
  have h_v157 : R 1 0 0 1 v157 v157 := (r_plt hl h_v156 h_v25 (of_decide_eq_true rfl))
  have e_v157 : (v157 = 1 ↔ sv v156 < sv v25) := e_plt h_v156 h_v25 (of_decide_eq_true rfl)
  have h_v158 : R 1 0 4611686018427387908 4611686018695823367 v158 v158 := (r_psel hl h_v157 h_v156 h_v25 (of_decide_eq_true rfl))
  have e_v158 : v158 = if v157 = 1 then v156 else v25 := e_psel h_v157 h_v156 h_v25 (of_decide_eq_true rfl)
  have h_v159 : R 1 0 4611686018427387900 4611686018695823359 v159 v159 := (r_sub hl (r_add hl h_v15 h_t147_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v159 : sv v159 = sv v15 + sv t147.1 := e_add h_v15 h_t147_1 (of_decide_eq_true rfl)
  have h_v160 : R 1 0 4611686018158952441 4611686018695823367 v160 v160 := (r_psel hl h_v99 h_v151 h_v154 (of_decide_eq_true rfl))
  have e_v160 : v160 = if v99 = 1 then v151 else v154 := e_psel h_v99 h_v151 h_v154 (of_decide_eq_true rfl)
  have h_v161 : R 1 0 4611686018427387900 4611686018695823367 v161 v161 := (r_psel hl h_v99 h_v158 h_v159 (of_decide_eq_true rfl))
  have e_v161 : v161 = if v99 = 1 then v158 else v159 := e_psel h_v99 h_v158 h_v159 (of_decide_eq_true rfl)
  have h_v162 : R 1 0 4539628418483879831 4683743618370895977 v162 v162 := (r_smx hl 29 h_v100 h_v161 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  clear h_v15 h_v17 h_v23 h_v25 h_t147_1 h_t147_2 h_v149 h_v150 h_v152 h_v153 h_v154 h_v156 h_v157 h_v158 h_v159
  have e_v162 : sv v162 = sv v100 * sv v161 := e_smx 29 h_v100 h_v161 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v163 : R 1 0 4539628420631363535 4683743616223412273 v163 v163 := (r_smx hl 29 h_v160 h_v146 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v163 : sv v163 = sv v160 * sv v146 := e_smx 29 h_v160 h_v146 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v164 : R 1 0 0 1 v164 v164 := (r_plt hl h_v163 h_v162 (of_decide_eq_true rfl))
  have e_v164 : (v164 = 1 ↔ sv v163 < sv v162) := e_plt h_v163 h_v162 (of_decide_eq_true rfl)
  have h_v165 : R 1 0 0 1 v165 v165 := (r_sub hl (r_O hl) h_v164 (of_decide_eq_true rfl))
  have e_v165 : (v165 = 1 ↔ ¬v164 = 1) := e_not h_v164 (of_decide_eq_true rfl)
  have h_v166 : R 1 0 0 1 v166 v166 := (r_plt hl h_v162 h_v163 (of_decide_eq_true rfl))
  have e_v166 : (v166 = 1 ↔ sv v162 < sv v163) := e_plt h_v162 h_v163 (of_decide_eq_true rfl)
  have h_v167 : R 1 0 0 1 v167 v167 := (r_sub hl (r_O hl) h_v166 (of_decide_eq_true rfl))
  have e_v167 : (v167 = 1 ↔ ¬v166 = 1) := e_not h_v166 (of_decide_eq_true rfl)
  have h_v168 : R 1 0 0 1 v168 v168 := (r_plt hl h_v64 h_v147 (of_decide_eq_true rfl))
  have e_v168 : (v168 = 1 ↔ sv v64 < sv v147) := e_plt h_v64 h_v147 (of_decide_eq_true rfl)
  have h_v169 : R 1 0 0 1 v169 v169 := (r_sub hl (r_O hl) h_v168 (of_decide_eq_true rfl))
  have e_v169 : (v169 = 1 ↔ ¬v168 = 1) := e_not h_v168 (of_decide_eq_true rfl)
  have h_v170 : R 1 0 0 1 v170 v170 := (r_plt hl h_v127 h_v147 (of_decide_eq_true rfl))
  have e_v170 : (v170 = 1 ↔ sv v127 < sv v147) := e_plt h_v127 h_v147 (of_decide_eq_true rfl)
  have h_v171 : R 1 0 0 1 v171 v171 := (r_sub hl (r_O hl) h_v170 (of_decide_eq_true rfl))
  have e_v171 : (v171 = 1 ↔ ¬v170 = 1) := e_not h_v170 (of_decide_eq_true rfl)
  have h_v172 : R 1 0 0 1 v172 v172 := (r_plt hl h_v8 h_v151 (of_decide_eq_true rfl))
  have e_v172 : (v172 = 1 ↔ sv v8 < sv v151) := e_plt h_v8 h_v151 (of_decide_eq_true rfl)
  have h_v173 : R 1 0 0 1 v173 v173 := (r_land hl h_v165 h_v172 (of_decide_eq_true rfl))
  have e_v173 : (v173 = 1 ↔ v165 = 1 ∧ v172 = 1) := e_land h_v165 h_v172 (of_decide_eq_true rfl)
  have h_v174 : R 1 0 0 1 v174 v174 := (r_land hl h_v171 h_v173 (of_decide_eq_true rfl))
  have e_v174 : (v174 = 1 ↔ v171 = 1 ∧ v173 = 1) := e_land h_v171 h_v173 (of_decide_eq_true rfl)
  clear h_v8 h_v100 h_v127 h_v146 h_v151 h_v160 h_v161 h_v162 h_v163 h_v164 h_v165 h_v166 h_v168 h_v170 h_v171 h_v172 h_v173
  have h_v175 : R 1 0 0 1 v175 v175 := (r_lor hl h_v169 h_v174 (of_decide_eq_true rfl))
  have e_v175 : (v175 = 1 ↔ v169 = 1 ∨ v174 = 1) := e_lor h_v169 h_v174 (of_decide_eq_true rfl)
  have h_v176 : R 1 0 0 1 v176 v176 := (r_plt hl h_v147 h_v134 (of_decide_eq_true rfl))
  have e_v176 : (v176 = 1 ↔ sv v147 < sv v134) := e_plt h_v147 h_v134 (of_decide_eq_true rfl)
  have h_v177 : R 1 0 0 1 v177 v177 := (r_sub hl (r_O hl) h_v176 (of_decide_eq_true rfl))
  have e_v177 : (v177 = 1 ↔ ¬v176 = 1) := e_not h_v176 (of_decide_eq_true rfl)
  have h_v178 : R 1 0 0 1 v178 v178 := (r_lor hl h_v167 h_v177 (of_decide_eq_true rfl))
  have e_v178 : (v178 = 1 ↔ v167 = 1 ∨ v177 = 1) := e_lor h_v167 h_v177 (of_decide_eq_true rfl)
  have h_v179 : R 1 0 0 1 v179 v179 := (r_land hl h_v99 h_v175 (of_decide_eq_true rfl))
  have e_v179 : (v179 = 1 ↔ v99 = 1 ∧ v175 = 1) := e_land h_v99 h_v175 (of_decide_eq_true rfl)
  have h_v180 : R 1 0 0 1 v180 v180 := (r_sub hl (r_O hl) h_v99 (of_decide_eq_true rfl))
  have e_v180 : (v180 = 1 ↔ ¬v99 = 1) := e_not h_v99 (of_decide_eq_true rfl)
  have h_v181 : R 1 0 0 1 v181 v181 := (r_land hl h_v178 h_v180 (of_decide_eq_true rfl))
  have e_v181 : (v181 = 1 ↔ v178 = 1 ∧ v180 = 1) := e_land h_v178 h_v180 (of_decide_eq_true rfl)
  have h_v182 : R 1 0 0 1 v182 v182 := (r_lor hl h_v179 h_v181 (of_decide_eq_true rfl))
  have e_v182 : (v182 = 1 ↔ v179 = 1 ∨ v181 = 1) := e_lor h_v179 h_v181 (of_decide_eq_true rfl)
  have h_v183 : R 1 0 4611686017353646081 4611686018427387904 v183 v183 := (r_sub hl (r_add hl h_v64 h_OFFr (of_decide_eq_true rfl)) h_v147 (of_decide_eq_true rfl))
  have e_v183 : sv v183 = sv v64 - sv v147 := e_sub h_v64 h_v147 (of_decide_eq_true rfl)
  have h_v184 : R 1 0 4611686017353646081 4611686019501129727 v184 v184 := (r_psel hl h_v99 h_v183 h_v147 (of_decide_eq_true rfl))
  have e_v184 : v184 = if v99 = 1 then v183 else v147 := e_psel h_v99 h_v183 h_v147 (of_decide_eq_true rfl)
  have h_v185 : R 1 0 4611686017353646081 4611686019501129727 v185 v185 := (r_psel hl h_v182 h_v184 h_v134 (of_decide_eq_true rfl))
  have e_v185 : v185 = if v182 = 1 then v184 else v134 := e_psel h_v182 h_v184 h_v134 (of_decide_eq_true rfl)
  have h_v187 : R 1 0 4611686017353646081 4611686019501129727 v187 v187 := (r_psel hl h_v96 h_v134 h_v185 (of_decide_eq_true rfl))
  have e_v187 : v187 = if v96 = 1 then v134 else v185 := e_psel h_v96 h_v134 h_v185 (of_decide_eq_true rfl)
  have h_v189 : R 1 0 4611686016279904258 4611686020574871550 v189 v189 := (r_sub hl (r_add hl h_v187 h_v187 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_OFFr h_v64 h_v96 h_v99 h_v134 h_v147 h_v167 h_v169 h_v174 h_v175 h_v176 h_v177 h_v178 h_v179 h_v180 h_v181 h_v182 h_v183 h_v184 h_v185
  have e_v189 : sv v189 = sv v187 + sv v187 := e_add h_v187 h_v187 (of_decide_eq_true rfl)
  have h_v192 : R 1 0 0 1 v192 v192 := (r_plt hl h_v4 h_v189 (of_decide_eq_true rfl))
  have e_v192 : (v192 = 1 ↔ sv v4 < sv v189) := e_plt h_v4 h_v189 (of_decide_eq_true rfl)
  have h_v193 : R 1 0 0 1 v193 v193 := (r_sub hl (r_O hl) h_v192 (of_decide_eq_true rfl))
  have e_v193 : (v193 = 1 ↔ ¬v192 = 1) := e_not h_v192 (of_decide_eq_true rfl)
  have h_v194 : R 1 0 0 1 v194 v194 := (r_plt hl h_v1 h_v6 (of_decide_eq_true rfl))
  have e_v194 : (v194 = 1 ↔ sv v1 < sv v6) := e_plt h_v1 h_v6 (of_decide_eq_true rfl)
  have h_v195 : R 1 0 0 1 v195 v195 := (r_sub hl (r_O hl) h_v194 (of_decide_eq_true rfl))
  have e_v195 : (v195 = 1 ↔ ¬v194 = 1) := e_not h_v194 (of_decide_eq_true rfl)
  have h_v196 : R 1 0 0 1 v196 v196 := (r_land hl h_v193 h_v195 (of_decide_eq_true rfl))
  have e_v196 : (v196 = 1 ↔ v193 = 1 ∧ v195 = 1) := e_land h_v193 h_v195 (of_decide_eq_true rfl)
  have h_v197 : R 1 0 0 1 v197 v197 := (r_land hl h_v13 h_v36 (of_decide_eq_true rfl))
  have e_v197 : (v197 = 1 ↔ v13 = 1 ∧ v36 = 1) := e_land h_v13 h_v36 (of_decide_eq_true rfl)
  have h_v198 : R 1 0 0 1 v198 v198 := (r_land hl h_v36 h_v197 (of_decide_eq_true rfl))
  have e_v198 : (v198 = 1 ↔ v36 = 1 ∧ v197 = 1) := e_land h_v36 h_v197 (of_decide_eq_true rfl)
  have h_v199 : R 1 0 0 1 v199 v199 := (r_land hl h_v78 h_v198 (of_decide_eq_true rfl))
  have e_v199 : (v199 = 1 ↔ v78 = 1 ∧ v198 = 1) := e_land h_v78 h_v198 (of_decide_eq_true rfl)
  have h_v200 : R 1 0 0 1 v200 v200 := (r_land hl h_v36 h_v199 (of_decide_eq_true rfl))
  have e_v200 : (v200 = 1 ↔ v36 = 1 ∧ v199 = 1) := e_land h_v36 h_v199 (of_decide_eq_true rfl)
  have h_v201 : R 1 0 0 1 v201 v201 := (r_land hl h_v36 h_v200 (of_decide_eq_true rfl))
  have e_v201 : (v201 = 1 ↔ v36 = 1 ∧ v200 = 1) := e_land h_v36 h_v200 (of_decide_eq_true rfl)
  have h_v202 : R 1 0 0 1 v202 v202 := (r_land hl h_v78 h_v201 (of_decide_eq_true rfl))
  have e_v202 : (v202 = 1 ↔ v78 = 1 ∧ v201 = 1) := e_land h_v78 h_v201 (of_decide_eq_true rfl)
  have h_v203 : R 1 0 0 1 v203 v203 := (r_land hl h_v196 h_v202 (of_decide_eq_true rfl))
  have e_v203 : (v203 = 1 ↔ v196 = 1 ∧ v202 = 1) := e_land h_v196 h_v202 (of_decide_eq_true rfl)
  clear h_v1 h_v4 h_v6 h_v13 h_v36 h_v78 h_v187 h_v189 h_v192 h_v193 h_v194 h_v195 h_v196 h_v197 h_v198 h_v199 h_v200 h_v201 h_v202
  have k_v203 : v203 = 1 := h
  have k_v196 : v196 = 1 := ((e_v203).1 k_v203).1
  have k_v202 : v202 = 1 := ((e_v203).1 k_v203).2
  have k_v78 : v78 = 1 := ((e_v202).1 k_v202).1
  have k_v201 : v201 = 1 := ((e_v202).1 k_v202).2
  have k_v36 : v36 = 1 := ((e_v201).1 k_v201).1
  have k_v200 : v200 = 1 := ((e_v201).1 k_v201).2
  have k_v199 : v199 = 1 := ((e_v200).1 k_v200).2
  have k_v198 : v198 = 1 := ((e_v199).1 k_v199).2
  have k_v197 : v197 = 1 := ((e_v198).1 k_v198).2
  have k_v13 : v13 = 1 := ((e_v197).1 k_v197).1
  have k_v9 : v9 = 1 := ((e_v13).1 k_v13).1
  have k_v12 : v12 = 1 := ((e_v13).1 k_v13).2
  have k_v33 : v33 = 1 := ((e_v36).1 k_v36).1
  have k_v35 : v35 = 1 := ((e_v36).1 k_v36).2
  have k_v193 : v193 = 1 := ((e_v196).1 k_v196).1
  have k_v195 : v195 = 1 := ((e_v196).1 k_v196).2
  have f3 := L2.K8_in_range True (sv v6) (sv v6) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f13 := L2.K3_cos_lo (sv v6) (sv t6.2) (sv v16) (sv v17) (sv v19) (L2.p_cos e_t6_2) (L2.p_addc (-4) e_v16 e_v15) e_v17 (L2.p_max e_v18 (L2.p_sel e_v19))
  have f27 := L2.K3_cos_hi (sv v6) (sv t6.2) (sv v24) (sv v25) (sv v27) (L2.p_cos e_t6_2) (L2.p_addc (4) e_v24 e_v23) e_v25 (L2.p_min e_v26 (L2.p_sel e_v27))
  have f2 := L2.K10_icos True (sv v6) (sv v6) (sv v19) (sv v17) v21 (sv v22) (sv v27) (sv v25) v29 (sv v30) f3 f13 e_v17 (L2.p_clt (843314855) e_v20 e_v21) (L2.p_sel e_v22) f27 e_v25 (L2.p_ltc (1) e_v28 e_v29) (L2.p_sel e_v30)
  have f42 := L2.K5_ihalf (sv v2) (sv v2) (sv v31) (sv v32) e_v31 e_v32
  have f46 := L2.K8_in_range True (sv v31) (sv v32) v33 (sv v10) v35 v36 (L2.p_clt (-1) e_v8 e_v33) e_v10 (L2.p_le e_v34 e_v35) e_v36 (L2.X1_top _ k_v36)
  let u37 : ℤ := L2.cosI (sv v32)
  let u38 : ℤ := (sv v15) + u37
  let u39 : ℕ := if u38 < (sv v17) then 1 else 0
  let u40 : ℤ := if u39 = 1 then (sv v17) else u38
  have f56 := L2.K3_cos_lo (sv v32) u37 u38 (sv v17) u40 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u41 : ℕ := if (sv v20) < (sv v32) then 1 else 0
  let u42 : ℤ := if u41 = 1 then (sv v17) else u40
  have f70 := L2.K3_cos_hi (sv v31) (sv t31.2) (sv v44) (sv v25) (sv v46) (L2.p_cos e_t31_2) (L2.p_addc (4) (L2.p_add_comm e_v44) e_v23) e_v25 (L2.p_min e_v45 (L2.p_sel e_v46))
  have f45 := L2.K10_icos True (sv v31) (sv v32) u40 (sv v17) u41 u42 (sv v46) (sv v25) v47 (sv v48) f46 f56 e_v17 (L2.p_clt (843314855) e_v20 (L2.p_ult _ _)) rfl f70 e_v25 (L2.p_ltc (1) e_v28 e_v47) (L2.p_sel e_v48)
  have f85 := L2.K8_in_range True (sv v31) (sv v32) v33 (sv v10) v35 v36 (L2.p_clt (-1) e_v8 e_v33) e_v10 (L2.p_le e_v34 e_v35) e_v36 (L2.X1_top _ k_v36)
  have f84 := L2.K9_isin True (sv v31) (sv v32) (sv t31.1) (sv t32.1) (sv v52) (sv v53) (sv v54) (sv v55) (sv v25) (sv v57) v59 v61 v62 (sv v63) f85 (L2.p_sin e_t31_1) (L2.p_sin e_t32_1) (L2.p_min e_v51 (L2.p_sel e_v52)) (L2.p_addc (-4) (L2.p_add_comm e_v53) e_v15) (L2.p_max e_v51 (L2.p_sel e_v54)) (L2.p_addc (4) (L2.p_add_comm e_v55) e_v23) e_v25 (L2.p_min e_v56 (L2.p_sel e_v57)) (L2.p_ltc (421657430) e_v58 e_v59) (L2.p_clt (421657427) e_v60 e_v61) e_v62 (L2.p_sel e_v63)
  have f121 := L2.K6_imul True (sv v22) (sv v30) (sv v53) (sv v63) (sv v64) v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 (sv v81) v82 v83 (sv v84) v85 v86 (sv v87) v88 v89 (sv v90) (sv v92) (sv v94) e_v64 e_v65 e_v66 e_v67 e_v68 (L2.p_and_comm e_v69) e_v70 e_v71 e_v72 e_v73 e_v74 (L2.p_and_comm e_v75) e_v76 e_v77 e_v78 (L2.X1_top _ k_v78) e_v79 e_v80 (L2.p_sel e_v81) e_v82 e_v83 (L2.p_sel e_v84) e_v85 e_v86 (L2.p_sel e_v87) e_v88 e_v89 (L2.p_sel e_v90) (L2.p_mul (L2.p_mul_comm e_v91) e_v92) (L2.p_mulc (L2.p_mul_comm e_v93) e_v94)
  let u97 : ℕ := if u42 < (sv v64) then 1 else 0
  let u98 : ℤ := if u97 = 1 then (sv v92) else (sv v94)
  have f154 := L2.K11_qdiv u42 (sv v48) (sv v92) (sv v94) v95 v96 (sv v64) u97 u98 v99 (sv v100) (L2.p_clt (0) e_v64 e_v95) e_v96 e_v64 (L2.p_ult _ _) rfl e_v99 (L2.p_sel e_v100)
  let u101 : ℤ := (sv v64) - u42
  let u102 : ℤ := if u97 = 1 then u101 else u42
  let u103 : ℤ := 0
  let u104 : ℕ := if u97 = 1 then 0 else 1
  let u105 : ℤ := L2.cosI u103
  let u106 : ℤ := (sv v15) + u105
  let u107 : ℕ := if u106 < (sv v17) then 1 else 0
  let u108 : ℤ := if u107 = 1 then (sv v17) else u106
  have f172 := L2.K3_cos_lo u103 u105 u106 (sv v17) u108 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u109 : ℤ := (sv v23) + u105
  let u110 : ℕ := if u109 < (sv v25) then 1 else 0
  let u111 : ℤ := if u110 = 1 then u109 else (sv v25)
  have f181 := L2.K3_cos_hi u103 u105 u109 (sv v25) u111 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  let u112 : ℤ := L2.sinI u103
  let u113 : ℤ := (sv v23) + u112
  let u114 : ℕ := if u113 < (sv v25) then 1 else 0
  let u115 : ℤ := if u114 = 1 then u113 else (sv v25)
  have f190 := L2.K3_sin_hi u103 u112 u113 (sv v25) u115 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  let u116 : ℤ := (sv v15) + u112
  have f199 := L2.K3_sin_lo u103 u112 u116 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15)
  let u117 : ℤ := if u104 = 1 then u108 else u111
  let u118 : ℤ := if u104 = 1 then u115 else u116
  let u119 : ℤ := u98 * u118
  let u120 : ℤ := u102 * u117
  let u121 : ℕ := if u120 < u119 then 1 else 0
  let u122 : ℕ := if u121 = 1 then 0 else 1
  let u123 : ℕ := if u119 < u120 then 1 else 0
  let u124 : ℕ := if u123 = 1 then 0 else 1
  let u125 : ℕ := if (sv v64) < u103 then 1 else 0
  let u126 : ℕ := if u125 = 1 then 0 else 1
  let u128 : ℕ := if (sv v127) < u103 then 1 else 0
  let u129 : ℕ := if u128 = 1 then 0 else 1
  let u130 : ℕ := if (sv v8) < u108 then 1 else 0
  let u131 : ℕ := if u122 = 1 ∧ u130 = 1 then 1 else 0
  let u132 : ℕ := if u129 = 1 ∧ u131 = 1 then 1 else 0
  let u133 : ℕ := if u126 = 1 ∨ u132 = 1 then 1 else 0
  let u135 : ℕ := if u103 < (sv v134) then 1 else 0
  let u136 : ℕ := if u135 = 1 then 0 else 1
  let u137 : ℕ := if u124 = 1 ∨ u136 = 1 then 1 else 0
  let u138 : ℕ := if u104 = 1 ∧ u133 = 1 then 1 else 0
  let u139 : ℕ := if u97 = 1 ∧ u137 = 1 then 1 else 0
  let u140 : ℕ := if u138 = 1 ∨ u139 = 1 then 1 else 0
  let u141 : ℤ := (sv v64) - u103
  let u142 : ℤ := if u97 = 1 then u141 else u103
  let u143 : ℤ := -421657429
  let u144 : ℤ := if u140 = 1 then u142 else u143
  have f165 := L2.K12_atan_lo u42 u98 (sv v64) u97 u101 u102 u103 u104 u108 u111 u115 u116 u117 u118 u119 u120 u122 u124 u125 u126 (sv v127) u129 u130 u131 u132 u133 (sv v134) u136 u137 u138 u97 u139 u140 u141 u142 u143 u144 e_v64 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f172 f181 f190 f199 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v127 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v134 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  have f245 := L2.K3_cos_lo (sv v147) (sv t147.2) (sv v149) (sv v17) (sv v151) (L2.p_cos e_t147_2) (L2.p_addc (-4) (L2.p_add_comm e_v149) e_v15) e_v17 (L2.p_max e_v150 (L2.p_sel e_v151))
  have f254 := L2.K3_cos_hi (sv v147) (sv t147.2) (sv v152) (sv v25) (sv v154) (L2.p_cos e_t147_2) (L2.p_addc (4) (L2.p_add_comm e_v152) e_v23) e_v25 (L2.p_min e_v153 (L2.p_sel e_v154))
  have f263 := L2.K3_sin_hi (sv v147) (sv t147.1) (sv v156) (sv v25) (sv v158) (L2.p_sin e_t147_1) (L2.p_addc (4) (L2.p_add_comm e_v156) e_v23) e_v25 (L2.p_min e_v157 (L2.p_sel e_v158))
  have f272 := L2.K3_sin_lo (sv v147) (sv t147.1) (sv v159) (L2.p_sin e_t147_1) (L2.p_addc (-4) (L2.p_add_comm e_v159) e_v15)
  have f239 := L2.K12_atan_hi (sv v48) (sv v100) (sv v64) v99 (sv v145) (sv v146) (sv v147) (sv v151) (sv v154) (sv v158) (sv v159) (sv v160) (sv v161) (sv v162) (sv v163) v165 v167 v168 v169 (sv v127) v171 v172 v173 v174 v175 (sv v134) v177 v178 v179 v180 v181 v182 (sv v183) (sv v184) (sv v134) (sv v185) e_v64 e_v99 e_v145 (L2.p_sel e_v146) (L2.p_hint e_v147) f245 f254 f263 f272 (L2.p_sel e_v160) (L2.p_sel e_v161) (L2.p_mul_comm e_v162) (L2.p_mul_comm e_v163) (L2.p_le e_v164 e_v165) (L2.p_le e_v166 e_v167) e_v168 e_v169 e_v127 (L2.p_le e_v170 e_v171) (L2.p_clt (-1) e_v8 e_v172) e_v173 (L2.p_and_comm e_v174) e_v175 e_v134 (L2.p_le e_v176 e_v177) (L2.p_or_comm e_v178) e_v179 e_v180 (L2.p_and_comm e_v181) e_v182 e_v183 (L2.p_sel e_v184) e_v134 (L2.p_sel e_v185)
  let u186 : ℤ := if v96 = 1 then u143 else u144
  have f41 := L2.K19_iso_angle_pt True (sv v2) (sv v22) (sv v30) (sv v31) (sv v32) u42 (sv v48) (sv v53) (sv v63) (sv v92) (sv v94) u98 (sv v100) v96 v95 u144 (sv v185) u143 (sv v134) u186 (sv v187) f42 f45 f84 f121 f154 (L2.p_not_not e_v96) f165 f239 rfl e_v134 rfl (L2.p_sel e_v187)
  have f317 := L2.K5_ihalf (sv v2) (sv v2) (sv v31) (sv v32) e_v31 e_v32
  have f321 := L2.K8_in_range True (sv v31) (sv v32) v33 (sv v10) v35 v36 (L2.p_clt (-1) e_v8 e_v33) e_v10 (L2.p_le e_v34 e_v35) e_v36 (L2.X1_top _ k_v36)
  have f331 := L2.K3_cos_lo (sv v32) u37 u38 (sv v17) u40 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  have f345 := L2.K3_cos_hi (sv v31) (sv t31.2) (sv v44) (sv v25) (sv v46) (L2.p_cos e_t31_2) (L2.p_addc (4) (L2.p_add_comm e_v44) e_v23) e_v25 (L2.p_min e_v45 (L2.p_sel e_v46))
  have f320 := L2.K10_icos True (sv v31) (sv v32) u40 (sv v17) u41 u42 (sv v46) (sv v25) v47 (sv v48) f321 f331 e_v17 (L2.p_clt (843314855) e_v20 (L2.p_ult _ _)) rfl f345 e_v25 (L2.p_ltc (1) e_v28 e_v47) (L2.p_sel e_v48)
  have f360 := L2.K8_in_range True (sv v31) (sv v32) v33 (sv v10) v35 v36 (L2.p_clt (-1) e_v8 e_v33) e_v10 (L2.p_le e_v34 e_v35) e_v36 (L2.X1_top _ k_v36)
  have f359 := L2.K9_isin True (sv v31) (sv v32) (sv t31.1) (sv t32.1) (sv v52) (sv v53) (sv v54) (sv v55) (sv v25) (sv v57) v59 v61 v62 (sv v63) f360 (L2.p_sin e_t31_1) (L2.p_sin e_t32_1) (L2.p_min e_v51 (L2.p_sel e_v52)) (L2.p_addc (-4) (L2.p_add_comm e_v53) e_v15) (L2.p_max e_v51 (L2.p_sel e_v54)) (L2.p_addc (4) (L2.p_add_comm e_v55) e_v23) e_v25 (L2.p_min e_v56 (L2.p_sel e_v57)) (L2.p_ltc (421657430) e_v58 e_v59) (L2.p_clt (421657427) e_v60 e_v61) e_v62 (L2.p_sel e_v63)
  have f396 := L2.K6_imul True (sv v22) (sv v30) (sv v53) (sv v63) (sv v64) v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 (sv v81) v82 v83 (sv v84) v85 v86 (sv v87) v88 v89 (sv v90) (sv v92) (sv v94) e_v64 e_v65 e_v66 e_v67 e_v68 (L2.p_and_comm e_v69) e_v70 e_v71 e_v72 e_v73 e_v74 (L2.p_and_comm e_v75) e_v76 e_v77 e_v78 (L2.X1_top _ k_v78) e_v79 e_v80 (L2.p_sel e_v81) e_v82 e_v83 (L2.p_sel e_v84) e_v85 e_v86 (L2.p_sel e_v87) e_v88 e_v89 (L2.p_sel e_v90) (L2.p_mul (L2.p_mul_comm e_v91) e_v92) (L2.p_mulc (L2.p_mul_comm e_v93) e_v94)
  have f429 := L2.K11_qdiv u42 (sv v48) (sv v92) (sv v94) v95 v96 (sv v64) u97 u98 v99 (sv v100) (L2.p_clt (0) e_v64 e_v95) e_v96 e_v64 (L2.p_ult _ _) rfl e_v99 (L2.p_sel e_v100)
  have f447 := L2.K3_cos_lo u103 u105 u106 (sv v17) u108 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  have f456 := L2.K3_cos_hi u103 u105 u109 (sv v25) u111 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  have f465 := L2.K3_sin_hi u103 u112 u113 (sv v25) u115 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v23) e_v25 (L2.p_min (L2.p_ult _ _) rfl)
  have f474 := L2.K3_sin_lo u103 u112 u116 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15)
  have f440 := L2.K12_atan_lo u42 u98 (sv v64) u97 u101 u102 u103 u104 u108 u111 u115 u116 u117 u118 u119 u120 u122 u124 u125 u126 (sv v127) u129 u130 u131 u132 u133 (sv v134) u136 u137 u138 u97 u139 u140 u141 u142 u143 u144 e_v64 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f447 f456 f465 f474 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v127 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v134 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  have f520 := L2.K3_cos_lo (sv v147) (sv t147.2) (sv v149) (sv v17) (sv v151) (L2.p_cos e_t147_2) (L2.p_addc (-4) (L2.p_add_comm e_v149) e_v15) e_v17 (L2.p_max e_v150 (L2.p_sel e_v151))
  have f529 := L2.K3_cos_hi (sv v147) (sv t147.2) (sv v152) (sv v25) (sv v154) (L2.p_cos e_t147_2) (L2.p_addc (4) (L2.p_add_comm e_v152) e_v23) e_v25 (L2.p_min e_v153 (L2.p_sel e_v154))
  have f538 := L2.K3_sin_hi (sv v147) (sv t147.1) (sv v156) (sv v25) (sv v158) (L2.p_sin e_t147_1) (L2.p_addc (4) (L2.p_add_comm e_v156) e_v23) e_v25 (L2.p_min e_v157 (L2.p_sel e_v158))
  have f547 := L2.K3_sin_lo (sv v147) (sv t147.1) (sv v159) (L2.p_sin e_t147_1) (L2.p_addc (-4) (L2.p_add_comm e_v159) e_v15)
  have f514 := L2.K12_atan_hi (sv v48) (sv v100) (sv v64) v99 (sv v145) (sv v146) (sv v147) (sv v151) (sv v154) (sv v158) (sv v159) (sv v160) (sv v161) (sv v162) (sv v163) v165 v167 v168 v169 (sv v127) v171 v172 v173 v174 v175 (sv v134) v177 v178 v179 v180 v181 v182 (sv v183) (sv v184) (sv v134) (sv v185) e_v64 e_v99 e_v145 (L2.p_sel e_v146) (L2.p_hint e_v147) f520 f529 f538 f547 (L2.p_sel e_v160) (L2.p_sel e_v161) (L2.p_mul_comm e_v162) (L2.p_mul_comm e_v163) (L2.p_le e_v164 e_v165) (L2.p_le e_v166 e_v167) e_v168 e_v169 e_v127 (L2.p_le e_v170 e_v171) (L2.p_clt (-1) e_v8 e_v172) e_v173 (L2.p_and_comm e_v174) e_v175 e_v134 (L2.p_le e_v176 e_v177) (L2.p_or_comm e_v178) e_v179 e_v180 (L2.p_and_comm e_v181) e_v182 e_v183 (L2.p_sel e_v184) e_v134 (L2.p_sel e_v185)
  have f316 := L2.K19_iso_angle_pt True (sv v2) (sv v22) (sv v30) (sv v31) (sv v32) u42 (sv v48) (sv v53) (sv v63) (sv v92) (sv v94) u98 (sv v100) v96 v95 u144 (sv v185) u143 (sv v134) u186 (sv v187) f317 f320 f359 f396 f429 (L2.p_not_not e_v96) f440 f514 rfl e_v134 rfl (L2.p_sel e_v187)
  have f1 := L2.K20_iso_angle True (sv v2) (sv v2) (sv v6) (sv v6) (sv v22) (sv v30) u186 (sv v187) v96 u186 (sv v187) v96 f2 f41 f316
  let u188 : ℤ := u186 + u186
  have f591 := L2.K4_iadd u186 (sv v187) u186 (sv v187) u188 (sv v189) rfl e_v189
  let u190 : ℕ := if u188 < (sv v4) then 1 else 0
  let u191 : ℕ := if u190 = 1 then 0 else 1
  exact Tammes15.D3Trig.TDL F0 F1 F2 F3 hD (sv v1) (sv v2) (sv v4) (sv v6) (1 : ℕ) u186 (sv v187) u188 (sv v189) u191 v193 v193 v195 v196 e_v1 e_v2 e_v4 e_v6 (of_decide_eq_true rfl) f1 f591 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le e_v192 e_v193) (L2.p_sel_t _ _) (L2.p_le e_v194 e_v195) e_v196 (L2.X1_top _ k_v196)

end Tammes15.D3Trig
