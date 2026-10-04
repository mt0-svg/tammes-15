import Tammes15.D3Trig.Prog.RL
import Tammes15.D3Prog.L2.Kinds
import Tammes15.D3Prog.L2.PLib
import Tammes15.D3Trig.RhoKinds

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem progRL_l2 (F0 F1 F2 F3 H0 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (h : Tammes15.D3Trig.progRL 1 F0 F1 F2 F3 H0 = 1) (hD : D3Prog.L2.InDom F0 F1 F2 F3) : LaneClaimR 0 false F0 F1 F2 F3 := by
  unfold Tammes15.D3Trig.progRL at h
  extract_lets -merge OFFr H61r v0 v1 v2 v3 v6 v8 v9 v10 v11 v12 v13 t1 v15 v16 v17 v18 v19 v20 v21 v22 t0 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 t33 v39 v40 v41 v42 v43 t32 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v102 v103 v104 v105 t104 v107 v108 v109 v110 v111 v112 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v187 v189 v190 v191 v192 v193 v194 t189 t190 v209 v210 v211 v212 v213 v214 v215 v216 v217 v218 v219 v220 v222 v225 v226 v227 v334 v336 v337 v341 v342 v343 v344 v345 v346 v347 at h
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have e_OFFr : sv OFFr = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have h_H61r : R 1 0 2305843009213693952 2305843009213693952 H61r H61r := (r_c hl 2305843009213693952 (of_decide_eq_true rfl))
  have e_H61r : sv H61r = (-2305843009213693952) := e_c 2305843009213693952 (-2305843009213693952) (of_decide_eq_true rfl)
  have h_v0 : R 1 0 4611686018427387904 4611686087146864624 v0 v0 := (r1_ix hb_F0 0 (of_decide_eq_true rfl))
  have e_v0 : sv v0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F0 0 (of_decide_eq_true rfl)
  have h_v1 : R 1 0 4611686018427387904 4611686087146864624 v1 v1 := (r1_ix hb_F0 32 (of_decide_eq_true rfl))
  have e_v1 : sv v1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F0 32 (of_decide_eq_true rfl)
  have h_v2 : R 1 0 4611686018427387904 4611686087146864624 v2 v2 := (r1_ix hb_F1 0 (of_decide_eq_true rfl))
  have e_v2 : sv v2 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F1 0 (of_decide_eq_true rfl)
  have h_v3 : R 1 0 4611686018427387904 4611686087146864624 v3 v3 := (r1_ix hb_F1 32 (of_decide_eq_true rfl))
  have e_v3 : sv v3 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F1 32 (of_decide_eq_true rfl)
  have h_v6 : R 1 0 4611686018427387904 4611686087146864624 v6 v6 := (r1_ix hb_F3 0 (of_decide_eq_true rfl))
  have e_v6 : sv v6 = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F3 0 (of_decide_eq_true rfl)
  have h_v8 : R 1 0 4611686018427387903 4611686018427387903 v8 v8 := (r_c hl 4611686018427387903 (of_decide_eq_true rfl))
  have e_v8 : sv v8 = (-1) := e_c 4611686018427387903 (-1) (of_decide_eq_true rfl)
  have h_v9 : R 1 0 0 1 v9 v9 := (r_plt hl h_v8 h_v0 (of_decide_eq_true rfl))
  have e_v9 : (v9 = 1 ↔ sv v8 < sv v0) := e_plt h_v8 h_v0 (of_decide_eq_true rfl)
  have h_v10 : R 1 0 4611686019270702761 4611686019270702761 v10 v10 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have e_v10 : sv v10 = (843314857) := e_c 4611686019270702761 (843314857) (of_decide_eq_true rfl)
  have h_v11 : R 1 0 0 1 v11 v11 := (r_plt hl h_v10 h_v1 (of_decide_eq_true rfl))
  have e_v11 : (v11 = 1 ↔ sv v10 < sv v1) := e_plt h_v10 h_v1 (of_decide_eq_true rfl)
  have h_v12 : R 1 0 0 1 v12 v12 := (r_sub hl (r_O hl) h_v11 (of_decide_eq_true rfl))
  have e_v12 : (v12 = 1 ↔ ¬v11 = 1) := e_not h_v11 (of_decide_eq_true rfl)
  have h_v13 : R 1 0 0 1 v13 v13 := (r_land hl h_v9 h_v12 (of_decide_eq_true rfl))
  clear e_OFFr e_H61r h_v11
  have e_v13 : (v13 = 1 ↔ v9 = 1 ∧ v12 = 1) := e_land h_v9 h_v12 (of_decide_eq_true rfl)
  have h_t1_1 : R 1 0 4611686018427387904 4611686018695823363 t1.1 t1.1 := r_sc1 hl h_v1 (of_decide_eq_true rfl)
  have h_t1_2 : R 1 0 4611686018158952445 4611686018695823363 t1.2 t1.2 := r_sc2 hl h_v1 (of_decide_eq_true rfl)
  have e_t1_1 : sv t1.1 = (sc28pS (scArg v1)).1 := e_sc1 h_v1 (of_decide_eq_true rfl)
  have e_t1_2 : sv t1.2 = (sc28pS (scArg v1)).2 := e_sc2 h_v1 (of_decide_eq_true rfl)
  have h_v15 : R 1 0 4611686018427387900 4611686018427387900 v15 v15 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have e_v15 : sv v15 = (-4) := e_c 4611686018427387900 (-4) (of_decide_eq_true rfl)
  have h_v16 : R 1 0 4611686018158952441 4611686018695823359 v16 v16 := (r_sub hl (r_add hl h_t1_2 h_v15 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v16 : sv v16 = sv t1.2 + sv v15 := e_add h_t1_2 h_v15 (of_decide_eq_true rfl)
  have h_v17 : R 1 0 4611686018158952448 4611686018158952448 v17 v17 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have e_v17 : sv v17 = (-268435456) := e_c 4611686018158952448 (-268435456) (of_decide_eq_true rfl)
  have h_v18 : R 1 0 0 1 v18 v18 := (r_plt hl h_v16 h_v17 (of_decide_eq_true rfl))
  have e_v18 : (v18 = 1 ↔ sv v16 < sv v17) := e_plt h_v16 h_v17 (of_decide_eq_true rfl)
  have h_v19 : R 1 0 4611686018158952441 4611686018695823359 v19 v19 := (r_psel hl h_v18 h_v17 h_v16 (of_decide_eq_true rfl))
  have e_v19 : v19 = if v18 = 1 then v17 else v16 := e_psel h_v18 h_v17 h_v16 (of_decide_eq_true rfl)
  have h_v20 : R 1 0 4611686019270702759 4611686019270702759 v20 v20 := (r_c hl 4611686019270702759 (of_decide_eq_true rfl))
  have e_v20 : sv v20 = (843314855) := e_c 4611686019270702759 (843314855) (of_decide_eq_true rfl)
  have h_v21 : R 1 0 0 1 v21 v21 := (r_plt hl h_v20 h_v1 (of_decide_eq_true rfl))
  have e_v21 : (v21 = 1 ↔ sv v20 < sv v1) := e_plt h_v20 h_v1 (of_decide_eq_true rfl)
  have h_v22 : R 1 0 4611686018158952441 4611686018695823359 v22 v22 := (r_psel hl h_v21 h_v17 h_v19 (of_decide_eq_true rfl))
  have e_v22 : v22 = if v21 = 1 then v17 else v19 := e_psel h_v21 h_v17 h_v19 (of_decide_eq_true rfl)
  have h_t0_1 : R 1 0 4611686018427387904 4611686018695823363 t0.1 t0.1 := r_sc1 hl h_v0 (of_decide_eq_true rfl)
  have h_t0_2 : R 1 0 4611686018158952445 4611686018695823363 t0.2 t0.2 := r_sc2 hl h_v0 (of_decide_eq_true rfl)
  have e_t0_1 : sv t0.1 = (sc28pS (scArg v0)).1 := e_sc1 h_v0 (of_decide_eq_true rfl)
  have e_t0_2 : sv t0.2 = (sc28pS (scArg v0)).2 := e_sc2 h_v0 (of_decide_eq_true rfl)
  clear h_v1 h_v9 h_v12 h_t1_1 h_t1_2 e_t1_1 h_v16 h_v18 h_v19 h_v21 h_t0_1 e_t0_1
  have h_v24 : R 1 0 4611686018427387908 4611686018427387908 v24 v24 := (r_c hl 4611686018427387908 (of_decide_eq_true rfl))
  have e_v24 : sv v24 = (4) := e_c 4611686018427387908 (4) (of_decide_eq_true rfl)
  have h_v25 : R 1 0 4611686018158952449 4611686018695823367 v25 v25 := (r_sub hl (r_add hl h_t0_2 h_v24 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v25 : sv v25 = sv t0.2 + sv v24 := e_add h_t0_2 h_v24 (of_decide_eq_true rfl)
  have h_v26 : R 1 0 4611686018695823360 4611686018695823360 v26 v26 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have e_v26 : sv v26 = (268435456) := e_c 4611686018695823360 (268435456) (of_decide_eq_true rfl)
  have h_v27 : R 1 0 0 1 v27 v27 := (r_plt hl h_v25 h_v26 (of_decide_eq_true rfl))
  have e_v27 : (v27 = 1 ↔ sv v25 < sv v26) := e_plt h_v25 h_v26 (of_decide_eq_true rfl)
  have h_v28 : R 1 0 4611686018158952449 4611686018695823367 v28 v28 := (r_psel hl h_v27 h_v25 h_v26 (of_decide_eq_true rfl))
  have e_v28 : v28 = if v27 = 1 then v25 else v26 := e_psel h_v27 h_v25 h_v26 (of_decide_eq_true rfl)
  have h_v29 : R 1 0 4611686018427387905 4611686018427387905 v29 v29 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have e_v29 : sv v29 = (1) := e_c 4611686018427387905 (1) (of_decide_eq_true rfl)
  have h_v30 : R 1 0 0 1 v30 v30 := (r_plt hl h_v0 h_v29 (of_decide_eq_true rfl))
  have e_v30 : (v30 = 1 ↔ sv v0 < sv v29) := e_plt h_v0 h_v29 (of_decide_eq_true rfl)
  have h_v31 : R 1 0 4611686018158952449 4611686018695823367 v31 v31 := (r_psel hl h_v30 h_v26 h_v28 (of_decide_eq_true rfl))
  have e_v31 : v31 = if v30 = 1 then v26 else v28 := e_psel h_v30 h_v26 h_v28 (of_decide_eq_true rfl)
  have h_v32 : R 1 0 4611686018427387904 4611686052787126264 v32 v32 := (r_add hl (r_pshr1 hl h_v3) h_H61r (of_decide_eq_true rfl))
  have e_v32 : sv v32 = sv v3 / 2 := e_halfF h_v3
  have h_v33 : R 1 0 4611686018427387904 4611686052787126264 v33 v33 := (r_add hl (r_pshr1 hl (r_add hl h_v3 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v33 : sv v33 = (sv v3 + 1) / 2 := e_halfC h_v3 (of_decide_eq_true rfl)
  have h_v34 : R 1 0 0 1 v34 v34 := (r_plt hl h_v8 h_v32 (of_decide_eq_true rfl))
  have e_v34 : (v34 = 1 ↔ sv v8 < sv v32) := e_plt h_v8 h_v32 (of_decide_eq_true rfl)
  have h_v35 : R 1 0 0 1 v35 v35 := (r_plt hl h_v10 h_v33 (of_decide_eq_true rfl))
  have e_v35 : (v35 = 1 ↔ sv v10 < sv v33) := e_plt h_v10 h_v33 (of_decide_eq_true rfl)
  have h_v36 : R 1 0 0 1 v36 v36 := (r_sub hl (r_O hl) h_v35 (of_decide_eq_true rfl))
  clear h_v0 h_v3 h_t0_2 h_v25 h_v27 h_v28 h_v29 h_v30
  have e_v36 : (v36 = 1 ↔ ¬v35 = 1) := e_not h_v35 (of_decide_eq_true rfl)
  have h_v37 : R 1 0 0 1 v37 v37 := (r_land hl h_v34 h_v36 (of_decide_eq_true rfl))
  have e_v37 : (v37 = 1 ↔ v34 = 1 ∧ v36 = 1) := e_land h_v34 h_v36 (of_decide_eq_true rfl)
  have h_t33_1 : R 1 0 4611686018427387904 4611686018695823363 t33.1 t33.1 := r_sc1 hl h_v33 (of_decide_eq_true rfl)
  have h_t33_2 : R 1 0 4611686018158952445 4611686018695823363 t33.2 t33.2 := r_sc2 hl h_v33 (of_decide_eq_true rfl)
  have e_t33_1 : sv t33.1 = (sc28pS (scArg v33)).1 := e_sc1 h_v33 (of_decide_eq_true rfl)
  have e_t33_2 : sv t33.2 = (sc28pS (scArg v33)).2 := e_sc2 h_v33 (of_decide_eq_true rfl)
  have h_v39 : R 1 0 4611686018158952441 4611686018695823359 v39 v39 := (r_sub hl (r_add hl h_v15 h_t33_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v39 : sv v39 = sv v15 + sv t33.2 := e_add h_v15 h_t33_2 (of_decide_eq_true rfl)
  have h_v40 : R 1 0 0 1 v40 v40 := (r_plt hl h_v39 h_v17 (of_decide_eq_true rfl))
  have e_v40 : (v40 = 1 ↔ sv v39 < sv v17) := e_plt h_v39 h_v17 (of_decide_eq_true rfl)
  have h_v41 : R 1 0 4611686018158952441 4611686018695823359 v41 v41 := (r_psel hl h_v40 h_v17 h_v39 (of_decide_eq_true rfl))
  have e_v41 : v41 = if v40 = 1 then v17 else v39 := e_psel h_v40 h_v17 h_v39 (of_decide_eq_true rfl)
  have h_v42 : R 1 0 0 1 v42 v42 := (r_plt hl h_v20 h_v33 (of_decide_eq_true rfl))
  have e_v42 : (v42 = 1 ↔ sv v20 < sv v33) := e_plt h_v20 h_v33 (of_decide_eq_true rfl)
  have h_v43 : R 1 0 4611686018158952441 4611686018695823359 v43 v43 := (r_psel hl h_v42 h_v17 h_v41 (of_decide_eq_true rfl))
  have e_v43 : v43 = if v42 = 1 then v17 else v41 := e_psel h_v42 h_v17 h_v41 (of_decide_eq_true rfl)
  have h_t32_1 : R 1 0 4611686018427387904 4611686018695823363 t32.1 t32.1 := r_sc1 hl h_v32 (of_decide_eq_true rfl)
  have h_t32_2 : R 1 0 4611686018158952445 4611686018695823363 t32.2 t32.2 := r_sc2 hl h_v32 (of_decide_eq_true rfl)
  have e_t32_1 : sv t32.1 = (sc28pS (scArg v32)).1 := e_sc1 h_v32 (of_decide_eq_true rfl)
  have e_t32_2 : sv t32.2 = (sc28pS (scArg v32)).2 := e_sc2 h_v32 (of_decide_eq_true rfl)
  have h_v52 : R 1 0 0 1 v52 v52 := (r_plt hl h_t32_1 h_t33_1 (of_decide_eq_true rfl))
  have e_v52 : (v52 = 1 ↔ sv t32.1 < sv t33.1) := e_plt h_t32_1 h_t33_1 (of_decide_eq_true rfl)
  have h_v53 : R 1 0 4611686018427387904 4611686018695823363 v53 v53 := (r_psel hl h_v52 h_t32_1 h_t33_1 (of_decide_eq_true rfl))
  have e_v53 : v53 = if v52 = 1 then t32.1 else t33.1 := e_psel h_v52 h_t32_1 h_t33_1 (of_decide_eq_true rfl)
  clear h_v20 h_v34 h_v35 h_v36 h_t33_2 h_v39 h_v40 h_v41 h_v42 h_t32_2 e_t32_2
  have h_v54 : R 1 0 4611686018427387900 4611686018695823359 v54 v54 := (r_sub hl (r_add hl h_v15 h_v53 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v54 : sv v54 = sv v15 + sv v53 := e_add h_v15 h_v53 (of_decide_eq_true rfl)
  have h_v55 : R 1 0 4611686018427387904 4611686018695823363 v55 v55 := (r_psel hl h_v52 h_t33_1 h_t32_1 (of_decide_eq_true rfl))
  have e_v55 : v55 = if v52 = 1 then t33.1 else t32.1 := e_psel h_v52 h_t33_1 h_t32_1 (of_decide_eq_true rfl)
  have h_v56 : R 1 0 4611686018427387908 4611686018695823367 v56 v56 := (r_sub hl (r_add hl h_v24 h_v55 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v56 : sv v56 = sv v24 + sv v55 := e_add h_v24 h_v55 (of_decide_eq_true rfl)
  have h_v57 : R 1 0 0 1 v57 v57 := (r_plt hl h_v56 h_v26 (of_decide_eq_true rfl))
  have e_v57 : (v57 = 1 ↔ sv v56 < sv v26) := e_plt h_v56 h_v26 (of_decide_eq_true rfl)
  have h_v58 : R 1 0 4611686018427387908 4611686018695823367 v58 v58 := (r_psel hl h_v57 h_v56 h_v26 (of_decide_eq_true rfl))
  have e_v58 : v58 = if v57 = 1 then v56 else v26 := e_psel h_v57 h_v56 h_v26 (of_decide_eq_true rfl)
  have h_v59 : R 1 0 4611686018849045334 4611686018849045334 v59 v59 := (r_c hl 4611686018849045334 (of_decide_eq_true rfl))
  have e_v59 : sv v59 = (421657430) := e_c 4611686018849045334 (421657430) (of_decide_eq_true rfl)
  have h_v60 : R 1 0 0 1 v60 v60 := (r_plt hl h_v32 h_v59 (of_decide_eq_true rfl))
  have e_v60 : (v60 = 1 ↔ sv v32 < sv v59) := e_plt h_v32 h_v59 (of_decide_eq_true rfl)
  have h_v61 : R 1 0 4611686018849045331 4611686018849045331 v61 v61 := (r_c hl 4611686018849045331 (of_decide_eq_true rfl))
  have e_v61 : sv v61 = (421657427) := e_c 4611686018849045331 (421657427) (of_decide_eq_true rfl)
  have h_v62 : R 1 0 0 1 v62 v62 := (r_plt hl h_v61 h_v33 (of_decide_eq_true rfl))
  have e_v62 : (v62 = 1 ↔ sv v61 < sv v33) := e_plt h_v61 h_v33 (of_decide_eq_true rfl)
  have h_v63 : R 1 0 0 1 v63 v63 := (r_land hl h_v60 h_v62 (of_decide_eq_true rfl))
  have e_v63 : (v63 = 1 ↔ v60 = 1 ∧ v62 = 1) := e_land h_v60 h_v62 (of_decide_eq_true rfl)
  have h_v64 : R 1 0 4611686018427387908 4611686018695823367 v64 v64 := (r_psel hl h_v63 h_v26 h_v58 (of_decide_eq_true rfl))
  have e_v64 : v64 = if v63 = 1 then v26 else v58 := e_psel h_v63 h_v26 h_v58 (of_decide_eq_true rfl)
  have h_v65 : R 1 0 4611686018427387904 4611686018427387904 v65 v65 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have e_v65 : sv v65 = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have h_v66 : R 1 0 0 1 v66 v66 := (r_plt hl h_v22 h_v65 (of_decide_eq_true rfl))
  clear h_v32 h_v33 h_t33_1 h_t32_1 h_v52 h_v53 h_v55 h_v56 h_v57 h_v58 h_v60 h_v62 h_v63
  have e_v66 : (v66 = 1 ↔ sv v22 < sv v65) := e_plt h_v22 h_v65 (of_decide_eq_true rfl)
  have h_v67 : R 1 0 0 1 v67 v67 := (r_sub hl (r_O hl) h_v66 (of_decide_eq_true rfl))
  have e_v67 : (v67 = 1 ↔ ¬v66 = 1) := e_not h_v66 (of_decide_eq_true rfl)
  have h_v68 : R 1 0 0 1 v68 v68 := (r_plt hl h_v65 h_v31 (of_decide_eq_true rfl))
  have e_v68 : (v68 = 1 ↔ sv v65 < sv v31) := e_plt h_v65 h_v31 (of_decide_eq_true rfl)
  have h_v69 : R 1 0 0 1 v69 v69 := (r_sub hl (r_O hl) h_v68 (of_decide_eq_true rfl))
  have e_v69 : (v69 = 1 ↔ ¬v68 = 1) := e_not h_v68 (of_decide_eq_true rfl)
  have h_v70 : R 1 0 0 1 v70 v70 := (r_land hl h_v66 h_v69 (of_decide_eq_true rfl))
  have e_v70 : (v70 = 1 ↔ v66 = 1 ∧ v69 = 1) := e_land h_v66 h_v69 (of_decide_eq_true rfl)
  have h_v71 : R 1 0 0 1 v71 v71 := (r_land hl h_v66 h_v68 (of_decide_eq_true rfl))
  have e_v71 : (v71 = 1 ↔ v66 = 1 ∧ v68 = 1) := e_land h_v66 h_v68 (of_decide_eq_true rfl)
  have h_v72 : R 1 0 0 1 v72 v72 := (r_plt hl h_v54 h_v65 (of_decide_eq_true rfl))
  have e_v72 : (v72 = 1 ↔ sv v54 < sv v65) := e_plt h_v54 h_v65 (of_decide_eq_true rfl)
  have h_v73 : R 1 0 0 1 v73 v73 := (r_sub hl (r_O hl) h_v72 (of_decide_eq_true rfl))
  have e_v73 : (v73 = 1 ↔ ¬v72 = 1) := e_not h_v72 (of_decide_eq_true rfl)
  have h_v74 : R 1 0 0 1 v74 v74 := (r_plt hl h_v65 h_v64 (of_decide_eq_true rfl))
  have e_v74 : (v74 = 1 ↔ sv v65 < sv v64) := e_plt h_v65 h_v64 (of_decide_eq_true rfl)
  have h_v75 : R 1 0 0 1 v75 v75 := (r_sub hl (r_O hl) h_v74 (of_decide_eq_true rfl))
  have e_v75 : (v75 = 1 ↔ ¬v74 = 1) := e_not h_v74 (of_decide_eq_true rfl)
  have h_v76 : R 1 0 0 1 v76 v76 := (r_land hl h_v72 h_v75 (of_decide_eq_true rfl))
  have e_v76 : (v76 = 1 ↔ v72 = 1 ∧ v75 = 1) := e_land h_v72 h_v75 (of_decide_eq_true rfl)
  have h_v77 : R 1 0 0 1 v77 v77 := (r_land hl h_v72 h_v74 (of_decide_eq_true rfl))
  have e_v77 : (v77 = 1 ↔ v72 = 1 ∧ v74 = 1) := e_land h_v72 h_v74 (of_decide_eq_true rfl)
  have h_v78 : R 1 0 0 1 v78 v78 := (r_land hl h_v71 h_v77 (of_decide_eq_true rfl))
  have e_v78 : (v78 = 1 ↔ v71 = 1 ∧ v77 = 1) := e_land h_v71 h_v77 (of_decide_eq_true rfl)
  clear h_v66 h_v68 h_v69 h_v72 h_v74 h_v75
  have h_v79 : R 1 0 0 1 v79 v79 := (r_sub hl (r_O hl) h_v78 (of_decide_eq_true rfl))
  have e_v79 : (v79 = 1 ↔ ¬v78 = 1) := e_not h_v78 (of_decide_eq_true rfl)
  have h_v80 : R 1 0 0 1 v80 v80 := (r_land hl h_v67 h_v77 (of_decide_eq_true rfl))
  have e_v80 : (v80 = 1 ↔ v67 = 1 ∧ v77 = 1) := e_land h_v67 h_v77 (of_decide_eq_true rfl)
  have h_v81 : R 1 0 0 1 v81 v81 := (r_lor hl h_v76 h_v80 (of_decide_eq_true rfl))
  have e_v81 : (v81 = 1 ↔ v76 = 1 ∨ v80 = 1) := e_lor h_v76 h_v80 (of_decide_eq_true rfl)
  have h_v82 : R 1 0 4611686018158952441 4611686018695823367 v82 v82 := (r_psel hl h_v81 h_v31 h_v22 (of_decide_eq_true rfl))
  have e_v82 : v82 = if v81 = 1 then v31 else v22 := e_psel h_v81 h_v31 h_v22 (of_decide_eq_true rfl)
  have h_v83 : R 1 0 0 1 v83 v83 := (r_land hl h_v71 h_v73 (of_decide_eq_true rfl))
  have e_v83 : (v83 = 1 ↔ v71 = 1 ∧ v73 = 1) := e_land h_v71 h_v73 (of_decide_eq_true rfl)
  have h_v84 : R 1 0 0 1 v84 v84 := (r_lor hl h_v70 h_v83 (of_decide_eq_true rfl))
  have e_v84 : (v84 = 1 ↔ v70 = 1 ∨ v83 = 1) := e_lor h_v70 h_v83 (of_decide_eq_true rfl)
  have h_v85 : R 1 0 4611686018427387900 4611686018695823367 v85 v85 := (r_psel hl h_v84 h_v64 h_v54 (of_decide_eq_true rfl))
  have e_v85 : v85 = if v84 = 1 then v64 else v54 := e_psel h_v84 h_v64 h_v54 (of_decide_eq_true rfl)
  have h_v86 : R 1 0 0 1 v86 v86 := (r_land hl h_v70 h_v77 (of_decide_eq_true rfl))
  have e_v86 : (v86 = 1 ↔ v70 = 1 ∧ v77 = 1) := e_land h_v70 h_v77 (of_decide_eq_true rfl)
  have h_v87 : R 1 0 0 1 v87 v87 := (r_lor hl h_v76 h_v86 (of_decide_eq_true rfl))
  have e_v87 : (v87 = 1 ↔ v76 = 1 ∨ v86 = 1) := e_lor h_v76 h_v86 (of_decide_eq_true rfl)
  have h_v88 : R 1 0 4611686018158952441 4611686018695823367 v88 v88 := (r_psel hl h_v87 h_v22 h_v31 (of_decide_eq_true rfl))
  have e_v88 : v88 = if v87 = 1 then v22 else v31 := e_psel h_v87 h_v22 h_v31 (of_decide_eq_true rfl)
  have h_v89 : R 1 0 0 1 v89 v89 := (r_land hl h_v71 h_v76 (of_decide_eq_true rfl))
  have e_v89 : (v89 = 1 ↔ v71 = 1 ∧ v76 = 1) := e_land h_v71 h_v76 (of_decide_eq_true rfl)
  have h_v90 : R 1 0 0 1 v90 v90 := (r_lor hl h_v70 h_v89 (of_decide_eq_true rfl))
  have e_v90 : (v90 = 1 ↔ v70 = 1 ∨ v89 = 1) := e_lor h_v70 h_v89 (of_decide_eq_true rfl)
  have h_v91 : R 1 0 4611686018427387900 4611686018695823367 v91 v91 := (r_psel hl h_v90 h_v54 h_v64 (of_decide_eq_true rfl))
  clear h_v22 h_v31 h_v67 h_v70 h_v73 h_v76 h_v77 h_v78 h_v80 h_v81 h_v83 h_v84 h_v86 h_v87 h_v89
  have e_v91 : v91 = if v90 = 1 then v54 else v64 := e_psel h_v90 h_v54 h_v64 (of_decide_eq_true rfl)
  have h_v92 : R 1 0 4539628420631363535 4683743616223412273 v92 v92 := (r_smx hl 29 h_v85 h_v82 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v92 : sv v92 = sv v85 * sv v82 := e_smx 29 h_v85 h_v82 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v93 : R 1 0 4611686018158952433 4611686018695823374 v93 v93 := (r_srdF hl h_v92 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v93 : sv v93 = sv v92 / 2 ^ 28 := e_srdF h_v92 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v94 : R 1 0 4539628420631363535 4683743616223412273 v94 v94 := (r_smx hl 29 h_v91 h_v88 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v94 : sv v94 = sv v91 * sv v88 := e_smx 29 h_v91 h_v88 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v95 : R 1 0 4611686018158952434 4611686018695823375 v95 v95 := (r_srdC hl h_v94 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v95 : sv v95 = -((-sv v94) / 2 ^ 28) := e_srdC h_v94 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v96 : R 1 0 0 1 v96 v96 := (r_plt hl h_v65 h_v93 (of_decide_eq_true rfl))
  have e_v96 : (v96 = 1 ↔ sv v65 < sv v93) := e_plt h_v65 h_v93 (of_decide_eq_true rfl)
  have h_v97 : R 1 0 0 1 v97 v97 := (r_sub hl (r_O hl) h_v96 (of_decide_eq_true rfl))
  have e_v97 : (v97 = 1 ↔ ¬v96 = 1) := e_not h_v96 (of_decide_eq_true rfl)
  have h_v98 : R 1 0 0 1 v98 v98 := (r_plt hl h_v43 h_v65 (of_decide_eq_true rfl))
  have e_v98 : (v98 = 1 ↔ sv v43 < sv v65) := e_plt h_v43 h_v65 (of_decide_eq_true rfl)
  have h_v99 : R 1 0 4611686018158952433 4611686018695823375 v99 v99 := (r_psel hl h_v98 h_v93 h_v95 (of_decide_eq_true rfl))
  have e_v99 : v99 = if v98 = 1 then v93 else v95 := e_psel h_v98 h_v93 h_v95 (of_decide_eq_true rfl)
  have h_v102 : R 1 0 4611686018158952449 4611686018695823367 v102 v102 := (r_sub hl (r_add hl h_v65 h_OFFr (of_decide_eq_true rfl)) h_v43 (of_decide_eq_true rfl))
  have e_v102 : sv v102 = sv v65 - sv v43 := e_sub h_v65 h_v43 (of_decide_eq_true rfl)
  have h_v103 : R 1 0 4611686018158952441 4611686018695823367 v103 v103 := (r_psel hl h_v98 h_v102 h_v43 (of_decide_eq_true rfl))
  have e_v103 : v103 = if v98 = 1 then v102 else v43 := e_psel h_v98 h_v102 h_v43 (of_decide_eq_true rfl)
  have h_v104 : R 1 0 4611686018427387904 4611686019501129727 v104 v104 := (r1_hxa hb_H0 0 (of_decide_eq_true rfl))
  have e_v104 : sv v104 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 0 (of_decide_eq_true rfl)
  have h_v105 : R 1 0 0 1 v105 v105 := (r_sub hl (r_O hl) h_v98 (of_decide_eq_true rfl))
  have e_v105 : (v105 = 1 ↔ ¬v98 = 1) := e_not h_v98 (of_decide_eq_true rfl)
  clear h_v43 h_v54 h_v64 h_v82 h_v85 h_v88 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v102
  have h_t104_1 : R 1 0 4611686018427387904 4611686018695823363 t104.1 t104.1 := r_sc1 hl h_v104 (of_decide_eq_true rfl)
  have h_t104_2 : R 1 0 4611686018158952445 4611686018695823363 t104.2 t104.2 := r_sc2 hl h_v104 (of_decide_eq_true rfl)
  have e_t104_1 : sv t104.1 = (sc28pS (scArg v104)).1 := e_sc1 h_v104 (of_decide_eq_true rfl)
  have e_t104_2 : sv t104.2 = (sc28pS (scArg v104)).2 := e_sc2 h_v104 (of_decide_eq_true rfl)
  have h_v107 : R 1 0 4611686018158952441 4611686018695823359 v107 v107 := (r_sub hl (r_add hl h_v15 h_t104_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v107 : sv v107 = sv v15 + sv t104.2 := e_add h_v15 h_t104_2 (of_decide_eq_true rfl)
  have h_v108 : R 1 0 0 1 v108 v108 := (r_plt hl h_v107 h_v17 (of_decide_eq_true rfl))
  have e_v108 : (v108 = 1 ↔ sv v107 < sv v17) := e_plt h_v107 h_v17 (of_decide_eq_true rfl)
  have h_v109 : R 1 0 4611686018158952441 4611686018695823359 v109 v109 := (r_psel hl h_v108 h_v17 h_v107 (of_decide_eq_true rfl))
  have e_v109 : v109 = if v108 = 1 then v17 else v107 := e_psel h_v108 h_v17 h_v107 (of_decide_eq_true rfl)
  have h_v110 : R 1 0 4611686018158952449 4611686018695823367 v110 v110 := (r_sub hl (r_add hl h_v24 h_t104_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v110 : sv v110 = sv v24 + sv t104.2 := e_add h_v24 h_t104_2 (of_decide_eq_true rfl)
  have h_v111 : R 1 0 0 1 v111 v111 := (r_plt hl h_v110 h_v26 (of_decide_eq_true rfl))
  have e_v111 : (v111 = 1 ↔ sv v110 < sv v26) := e_plt h_v110 h_v26 (of_decide_eq_true rfl)
  have h_v112 : R 1 0 4611686018158952449 4611686018695823367 v112 v112 := (r_psel hl h_v111 h_v110 h_v26 (of_decide_eq_true rfl))
  have e_v112 : v112 = if v111 = 1 then v110 else v26 := e_psel h_v111 h_v110 h_v26 (of_decide_eq_true rfl)
  have h_v114 : R 1 0 4611686018427387908 4611686018695823367 v114 v114 := (r_sub hl (r_add hl h_v24 h_t104_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v114 : sv v114 = sv v24 + sv t104.1 := e_add h_v24 h_t104_1 (of_decide_eq_true rfl)
  have h_v115 : R 1 0 0 1 v115 v115 := (r_plt hl h_v114 h_v26 (of_decide_eq_true rfl))
  have e_v115 : (v115 = 1 ↔ sv v114 < sv v26) := e_plt h_v114 h_v26 (of_decide_eq_true rfl)
  have h_v116 : R 1 0 4611686018427387908 4611686018695823367 v116 v116 := (r_psel hl h_v115 h_v114 h_v26 (of_decide_eq_true rfl))
  have e_v116 : v116 = if v115 = 1 then v114 else v26 := e_psel h_v115 h_v114 h_v26 (of_decide_eq_true rfl)
  have h_v117 : R 1 0 4611686018427387900 4611686018695823359 v117 v117 := (r_sub hl (r_add hl h_v15 h_t104_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v117 : sv v117 = sv v15 + sv t104.1 := e_add h_v15 h_t104_1 (of_decide_eq_true rfl)
  have h_v118 : R 1 0 4611686018158952441 4611686018695823367 v118 v118 := (r_psel hl h_v105 h_v109 h_v112 (of_decide_eq_true rfl))
  clear h_v17 h_t104_1 h_t104_2 h_v107 h_v108 h_v110 h_v111 h_v114 h_v115
  have e_v118 : v118 = if v105 = 1 then v109 else v112 := e_psel h_v105 h_v109 h_v112 (of_decide_eq_true rfl)
  have h_v119 : R 1 0 4611686018427387900 4611686018695823367 v119 v119 := (r_psel hl h_v105 h_v116 h_v117 (of_decide_eq_true rfl))
  have e_v119 : v119 = if v105 = 1 then v116 else v117 := e_psel h_v105 h_v116 h_v117 (of_decide_eq_true rfl)
  have h_v120 : R 1 0 4539628418483879831 4683743618370895977 v120 v120 := (r_smx hl 29 h_v99 h_v119 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v120 : sv v120 = sv v99 * sv v119 := e_smx 29 h_v99 h_v119 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v121 : R 1 0 4539628420631363535 4683743616223412273 v121 v121 := (r_smx hl 29 h_v118 h_v103 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v121 : sv v121 = sv v118 * sv v103 := e_smx 29 h_v118 h_v103 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v122 : R 1 0 0 1 v122 v122 := (r_plt hl h_v121 h_v120 (of_decide_eq_true rfl))
  have e_v122 : (v122 = 1 ↔ sv v121 < sv v120) := e_plt h_v121 h_v120 (of_decide_eq_true rfl)
  have h_v123 : R 1 0 0 1 v123 v123 := (r_sub hl (r_O hl) h_v122 (of_decide_eq_true rfl))
  have e_v123 : (v123 = 1 ↔ ¬v122 = 1) := e_not h_v122 (of_decide_eq_true rfl)
  have h_v124 : R 1 0 0 1 v124 v124 := (r_plt hl h_v120 h_v121 (of_decide_eq_true rfl))
  have e_v124 : (v124 = 1 ↔ sv v120 < sv v121) := e_plt h_v120 h_v121 (of_decide_eq_true rfl)
  have h_v125 : R 1 0 0 1 v125 v125 := (r_sub hl (r_O hl) h_v124 (of_decide_eq_true rfl))
  have e_v125 : (v125 = 1 ↔ ¬v124 = 1) := e_not h_v124 (of_decide_eq_true rfl)
  have h_v126 : R 1 0 0 1 v126 v126 := (r_plt hl h_v65 h_v104 (of_decide_eq_true rfl))
  have e_v126 : (v126 = 1 ↔ sv v65 < sv v104) := e_plt h_v65 h_v104 (of_decide_eq_true rfl)
  have h_v127 : R 1 0 0 1 v127 v127 := (r_sub hl (r_O hl) h_v126 (of_decide_eq_true rfl))
  have e_v127 : (v127 = 1 ↔ ¬v126 = 1) := e_not h_v126 (of_decide_eq_true rfl)
  have h_v128 : R 1 0 4611686018849045332 4611686018849045332 v128 v128 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  have e_v128 : sv v128 = (421657428) := e_c 4611686018849045332 (421657428) (of_decide_eq_true rfl)
  have h_v129 : R 1 0 0 1 v129 v129 := (r_plt hl h_v128 h_v104 (of_decide_eq_true rfl))
  have e_v129 : (v129 = 1 ↔ sv v128 < sv v104) := e_plt h_v128 h_v104 (of_decide_eq_true rfl)
  have h_v130 : R 1 0 0 1 v130 v130 := (r_sub hl (r_O hl) h_v129 (of_decide_eq_true rfl))
  have e_v130 : (v130 = 1 ↔ ¬v129 = 1) := e_not h_v129 (of_decide_eq_true rfl)
  clear h_v99 h_v103 h_v112 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v124 h_v126 h_v128 h_v129
  have h_v131 : R 1 0 0 1 v131 v131 := (r_plt hl h_v8 h_v109 (of_decide_eq_true rfl))
  have e_v131 : (v131 = 1 ↔ sv v8 < sv v109) := e_plt h_v8 h_v109 (of_decide_eq_true rfl)
  have h_v132 : R 1 0 0 1 v132 v132 := (r_land hl h_v123 h_v131 (of_decide_eq_true rfl))
  have e_v132 : (v132 = 1 ↔ v123 = 1 ∧ v131 = 1) := e_land h_v123 h_v131 (of_decide_eq_true rfl)
  have h_v133 : R 1 0 0 1 v133 v133 := (r_land hl h_v130 h_v132 (of_decide_eq_true rfl))
  have e_v133 : (v133 = 1 ↔ v130 = 1 ∧ v132 = 1) := e_land h_v130 h_v132 (of_decide_eq_true rfl)
  have h_v134 : R 1 0 0 1 v134 v134 := (r_lor hl h_v127 h_v133 (of_decide_eq_true rfl))
  have e_v134 : (v134 = 1 ↔ v127 = 1 ∨ v133 = 1) := e_lor h_v127 h_v133 (of_decide_eq_true rfl)
  have h_v135 : R 1 0 4611686018849045333 4611686018849045333 v135 v135 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have e_v135 : sv v135 = (421657429) := e_c 4611686018849045333 (421657429) (of_decide_eq_true rfl)
  have h_v136 : R 1 0 0 1 v136 v136 := (r_plt hl h_v104 h_v135 (of_decide_eq_true rfl))
  have e_v136 : (v136 = 1 ↔ sv v104 < sv v135) := e_plt h_v104 h_v135 (of_decide_eq_true rfl)
  have h_v137 : R 1 0 0 1 v137 v137 := (r_sub hl (r_O hl) h_v136 (of_decide_eq_true rfl))
  have e_v137 : (v137 = 1 ↔ ¬v136 = 1) := e_not h_v136 (of_decide_eq_true rfl)
  have h_v138 : R 1 0 0 1 v138 v138 := (r_lor hl h_v125 h_v137 (of_decide_eq_true rfl))
  have e_v138 : (v138 = 1 ↔ v125 = 1 ∨ v137 = 1) := e_lor h_v125 h_v137 (of_decide_eq_true rfl)
  have h_v139 : R 1 0 0 1 v139 v139 := (r_land hl h_v105 h_v134 (of_decide_eq_true rfl))
  have e_v139 : (v139 = 1 ↔ v105 = 1 ∧ v134 = 1) := e_land h_v105 h_v134 (of_decide_eq_true rfl)
  have h_v140 : R 1 0 0 1 v140 v140 := (r_land hl h_v98 h_v138 (of_decide_eq_true rfl))
  have e_v140 : (v140 = 1 ↔ v98 = 1 ∧ v138 = 1) := e_land h_v98 h_v138 (of_decide_eq_true rfl)
  have h_v141 : R 1 0 0 1 v141 v141 := (r_lor hl h_v139 h_v140 (of_decide_eq_true rfl))
  have e_v141 : (v141 = 1 ↔ v139 = 1 ∨ v140 = 1) := e_lor h_v139 h_v140 (of_decide_eq_true rfl)
  have h_v142 : R 1 0 4611686017353646081 4611686018427387904 v142 v142 := (r_sub hl (r_add hl h_v65 h_OFFr (of_decide_eq_true rfl)) h_v104 (of_decide_eq_true rfl))
  have e_v142 : sv v142 = sv v65 - sv v104 := e_sub h_v65 h_v104 (of_decide_eq_true rfl)
  have h_v143 : R 1 0 4611686017353646081 4611686019501129727 v143 v143 := (r_psel hl h_v98 h_v142 h_v104 (of_decide_eq_true rfl))
  clear h_v105 h_v109 h_v123 h_v125 h_v127 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140
  have e_v143 : v143 = if v98 = 1 then v142 else v104 := e_psel h_v98 h_v142 h_v104 (of_decide_eq_true rfl)
  have h_v144 : R 1 0 4611686018005730475 4611686018005730475 v144 v144 := (r_c hl 4611686018005730475 (of_decide_eq_true rfl))
  have e_v144 : sv v144 = (-421657429) := e_c 4611686018005730475 (-421657429) (of_decide_eq_true rfl)
  have h_v145 : R 1 0 4611686017353646081 4611686019501129727 v145 v145 := (r_psel hl h_v141 h_v143 h_v144 (of_decide_eq_true rfl))
  have e_v145 : v145 = if v141 = 1 then v143 else v144 := e_psel h_v141 h_v143 h_v144 (of_decide_eq_true rfl)
  have h_v187 : R 1 0 4611686017353646081 4611686019501129727 v187 v187 := (r_psel hl h_v97 h_v144 h_v145 (of_decide_eq_true rfl))
  have e_v187 : v187 = if v97 = 1 then v144 else v145 := e_psel h_v97 h_v144 h_v145 (of_decide_eq_true rfl)
  have h_v189 : R 1 0 4611686018427387904 4611686052787126264 v189 v189 := (r_add hl (r_pshr1 hl h_v2) h_H61r (of_decide_eq_true rfl))
  have e_v189 : sv v189 = sv v2 / 2 := e_halfF h_v2
  have h_v190 : R 1 0 4611686018427387904 4611686052787126264 v190 v190 := (r_add hl (r_pshr1 hl (r_add hl h_v2 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v190 : sv v190 = (sv v2 + 1) / 2 := e_halfC h_v2 (of_decide_eq_true rfl)
  have h_v191 : R 1 0 0 1 v191 v191 := (r_plt hl h_v8 h_v189 (of_decide_eq_true rfl))
  have e_v191 : (v191 = 1 ↔ sv v8 < sv v189) := e_plt h_v8 h_v189 (of_decide_eq_true rfl)
  have h_v192 : R 1 0 0 1 v192 v192 := (r_plt hl h_v10 h_v190 (of_decide_eq_true rfl))
  have e_v192 : (v192 = 1 ↔ sv v10 < sv v190) := e_plt h_v10 h_v190 (of_decide_eq_true rfl)
  have h_v193 : R 1 0 0 1 v193 v193 := (r_sub hl (r_O hl) h_v192 (of_decide_eq_true rfl))
  have e_v193 : (v193 = 1 ↔ ¬v192 = 1) := e_not h_v192 (of_decide_eq_true rfl)
  have h_v194 : R 1 0 0 1 v194 v194 := (r_land hl h_v191 h_v193 (of_decide_eq_true rfl))
  have e_v194 : (v194 = 1 ↔ v191 = 1 ∧ v193 = 1) := e_land h_v191 h_v193 (of_decide_eq_true rfl)
  have h_t189_1 : R 1 0 4611686018427387904 4611686018695823363 t189.1 t189.1 := r_sc1 hl h_v189 (of_decide_eq_true rfl)
  have h_t189_2 : R 1 0 4611686018158952445 4611686018695823363 t189.2 t189.2 := r_sc2 hl h_v189 (of_decide_eq_true rfl)
  have e_t189_1 : sv t189.1 = (sc28pS (scArg v189)).1 := e_sc1 h_v189 (of_decide_eq_true rfl)
  have e_t189_2 : sv t189.2 = (sc28pS (scArg v189)).2 := e_sc2 h_v189 (of_decide_eq_true rfl)
  have h_t190_1 : R 1 0 4611686018427387904 4611686018695823363 t190.1 t190.1 := r_sc1 hl h_v190 (of_decide_eq_true rfl)
  have h_t190_2 : R 1 0 4611686018158952445 4611686018695823363 t190.2 t190.2 := r_sc2 hl h_v190 (of_decide_eq_true rfl)
  clear h_H61r h_v2 h_v8 h_v10 h_v97 h_v98 h_v104 h_v141 h_v142 h_v143 h_v144 h_v145 h_v191 h_v192 h_v193 h_t189_2 e_t189_2 h_t190_2
  have e_t190_1 : sv t190.1 = (sc28pS (scArg v190)).1 := e_sc1 h_v190 (of_decide_eq_true rfl)
  have e_t190_2 : sv t190.2 = (sc28pS (scArg v190)).2 := e_sc2 h_v190 (of_decide_eq_true rfl)
  have h_v209 : R 1 0 0 1 v209 v209 := (r_plt hl h_t189_1 h_t190_1 (of_decide_eq_true rfl))
  have e_v209 : (v209 = 1 ↔ sv t189.1 < sv t190.1) := e_plt h_t189_1 h_t190_1 (of_decide_eq_true rfl)
  have h_v210 : R 1 0 4611686018427387904 4611686018695823363 v210 v210 := (r_psel hl h_v209 h_t189_1 h_t190_1 (of_decide_eq_true rfl))
  have e_v210 : v210 = if v209 = 1 then t189.1 else t190.1 := e_psel h_v209 h_t189_1 h_t190_1 (of_decide_eq_true rfl)
  have h_v211 : R 1 0 4611686018427387900 4611686018695823359 v211 v211 := (r_sub hl (r_add hl h_v15 h_v210 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v211 : sv v211 = sv v15 + sv v210 := e_add h_v15 h_v210 (of_decide_eq_true rfl)
  have h_v212 : R 1 0 4611686018427387904 4611686018695823363 v212 v212 := (r_psel hl h_v209 h_t190_1 h_t189_1 (of_decide_eq_true rfl))
  have e_v212 : v212 = if v209 = 1 then t190.1 else t189.1 := e_psel h_v209 h_t190_1 h_t189_1 (of_decide_eq_true rfl)
  have h_v213 : R 1 0 4611686018427387908 4611686018695823367 v213 v213 := (r_sub hl (r_add hl h_v24 h_v212 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v213 : sv v213 = sv v24 + sv v212 := e_add h_v24 h_v212 (of_decide_eq_true rfl)
  have h_v214 : R 1 0 0 1 v214 v214 := (r_plt hl h_v213 h_v26 (of_decide_eq_true rfl))
  have e_v214 : (v214 = 1 ↔ sv v213 < sv v26) := e_plt h_v213 h_v26 (of_decide_eq_true rfl)
  have h_v215 : R 1 0 4611686018427387908 4611686018695823367 v215 v215 := (r_psel hl h_v214 h_v213 h_v26 (of_decide_eq_true rfl))
  have e_v215 : v215 = if v214 = 1 then v213 else v26 := e_psel h_v214 h_v213 h_v26 (of_decide_eq_true rfl)
  have h_v216 : R 1 0 0 1 v216 v216 := (r_plt hl h_v189 h_v59 (of_decide_eq_true rfl))
  have e_v216 : (v216 = 1 ↔ sv v189 < sv v59) := e_plt h_v189 h_v59 (of_decide_eq_true rfl)
  have h_v217 : R 1 0 0 1 v217 v217 := (r_plt hl h_v61 h_v190 (of_decide_eq_true rfl))
  have e_v217 : (v217 = 1 ↔ sv v61 < sv v190) := e_plt h_v61 h_v190 (of_decide_eq_true rfl)
  have h_v218 : R 1 0 0 1 v218 v218 := (r_land hl h_v216 h_v217 (of_decide_eq_true rfl))
  have e_v218 : (v218 = 1 ↔ v216 = 1 ∧ v217 = 1) := e_land h_v216 h_v217 (of_decide_eq_true rfl)
  have h_v219 : R 1 0 4611686018427387908 4611686018695823367 v219 v219 := (r_psel hl h_v218 h_v26 h_v215 (of_decide_eq_true rfl))
  have e_v219 : v219 = if v218 = 1 then v26 else v215 := e_psel h_v218 h_v26 h_v215 (of_decide_eq_true rfl)
  have h_v220 : R 1 0 0 1 v220 v220 := (r_plt hl h_v211 h_v65 (of_decide_eq_true rfl))
  clear h_v15 h_v24 h_v26 h_v59 h_v61 h_v189 h_v190 h_t189_1 h_t190_1 e_t190_2 h_v209 h_v210 h_v212 h_v213 h_v214 h_v215 h_v216 h_v217 h_v218
  have e_v220 : (v220 = 1 ↔ sv v211 < sv v65) := e_plt h_v211 h_v65 (of_decide_eq_true rfl)
  have h_v222 : R 1 0 0 1 v222 v222 := (r_plt hl h_v65 h_v219 (of_decide_eq_true rfl))
  have e_v222 : (v222 = 1 ↔ sv v65 < sv v219) := e_plt h_v65 h_v219 (of_decide_eq_true rfl)
  have h_v225 : R 1 0 0 1 v225 v225 := (r_land hl h_v220 h_v222 (of_decide_eq_true rfl))
  have e_v225 : (v225 = 1 ↔ v220 = 1 ∧ v222 = 1) := e_land h_v220 h_v222 (of_decide_eq_true rfl)
  have h_v226 : R 1 0 0 1 v226 v226 := (r_land hl h_v71 h_v225 (of_decide_eq_true rfl))
  have e_v226 : (v226 = 1 ↔ v71 = 1 ∧ v225 = 1) := e_land h_v71 h_v225 (of_decide_eq_true rfl)
  have h_v227 : R 1 0 0 1 v227 v227 := (r_sub hl (r_O hl) h_v226 (of_decide_eq_true rfl))
  have e_v227 : (v227 = 1 ↔ ¬v226 = 1) := e_not h_v226 (of_decide_eq_true rfl)
  have h_v334 : R 1 0 4611686016279904258 4611686020574871550 v334 v334 := (r_sub hl (r_add hl h_v187 h_v187 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v334 : sv v334 = sv v187 + sv v187 := e_add h_v187 h_v187 (of_decide_eq_true rfl)
  have h_v336 : R 1 0 0 1 v336 v336 := (r_plt hl h_v334 h_v6 (of_decide_eq_true rfl))
  have e_v336 : (v336 = 1 ↔ sv v334 < sv v6) := e_plt h_v334 h_v6 (of_decide_eq_true rfl)
  have h_v337 : R 1 0 0 1 v337 v337 := (r_sub hl (r_O hl) h_v336 (of_decide_eq_true rfl))
  have e_v337 : (v337 = 1 ↔ ¬v336 = 1) := e_not h_v336 (of_decide_eq_true rfl)
  have h_v341 : R 1 0 0 1 v341 v341 := (r_land hl h_v13 h_v37 (of_decide_eq_true rfl))
  have e_v341 : (v341 = 1 ↔ v13 = 1 ∧ v37 = 1) := e_land h_v13 h_v37 (of_decide_eq_true rfl)
  have h_v342 : R 1 0 0 1 v342 v342 := (r_land hl h_v37 h_v341 (of_decide_eq_true rfl))
  have e_v342 : (v342 = 1 ↔ v37 = 1 ∧ v341 = 1) := e_land h_v37 h_v341 (of_decide_eq_true rfl)
  have h_v343 : R 1 0 0 1 v343 v343 := (r_land hl h_v79 h_v342 (of_decide_eq_true rfl))
  have e_v343 : (v343 = 1 ↔ v79 = 1 ∧ v342 = 1) := e_land h_v79 h_v342 (of_decide_eq_true rfl)
  have h_v344 : R 1 0 0 1 v344 v344 := (r_land hl h_v194 h_v343 (of_decide_eq_true rfl))
  have e_v344 : (v344 = 1 ↔ v194 = 1 ∧ v343 = 1) := e_land h_v194 h_v343 (of_decide_eq_true rfl)
  have h_v345 : R 1 0 0 1 v345 v345 := (r_land hl h_v194 h_v344 (of_decide_eq_true rfl))
  have e_v345 : (v345 = 1 ↔ v194 = 1 ∧ v344 = 1) := e_land h_v194 h_v344 (of_decide_eq_true rfl)
  clear h_OFFr h_v6 h_v13 h_v37 h_v65 h_v71 h_v79 h_v187 h_v194 h_v211 h_v219 h_v220 h_v222 h_v225 h_v226 h_v334 h_v336 h_v341 h_v342 h_v343 h_v344
  have h_v346 : R 1 0 0 1 v346 v346 := (r_land hl h_v227 h_v345 (of_decide_eq_true rfl))
  have e_v346 : (v346 = 1 ↔ v227 = 1 ∧ v345 = 1) := e_land h_v227 h_v345 (of_decide_eq_true rfl)
  have h_v347 : R 1 0 0 1 v347 v347 := (r_land hl h_v337 h_v346 (of_decide_eq_true rfl))
  have e_v347 : (v347 = 1 ↔ v337 = 1 ∧ v346 = 1) := e_land h_v337 h_v346 (of_decide_eq_true rfl)
  have k_v347 : v347 = 1 := h
  have k_v337 : v337 = 1 := ((e_v347).1 k_v347).1
  have k_v346 : v346 = 1 := ((e_v347).1 k_v347).2
  have k_v227 : v227 = 1 := ((e_v346).1 k_v346).1
  have k_v345 : v345 = 1 := ((e_v346).1 k_v346).2
  have k_v194 : v194 = 1 := ((e_v345).1 k_v345).1
  have k_v344 : v344 = 1 := ((e_v345).1 k_v345).2
  have k_v343 : v343 = 1 := ((e_v344).1 k_v344).2
  have k_v79 : v79 = 1 := ((e_v343).1 k_v343).1
  have k_v342 : v342 = 1 := ((e_v343).1 k_v343).2
  have k_v37 : v37 = 1 := ((e_v342).1 k_v342).1
  have k_v341 : v341 = 1 := ((e_v342).1 k_v342).2
  have k_v13 : v13 = 1 := ((e_v341).1 k_v341).1
  have k_v9 : v9 = 1 := ((e_v13).1 k_v13).1
  have k_v12 : v12 = 1 := ((e_v13).1 k_v13).2
  have k_v34 : v34 = 1 := ((e_v37).1 k_v37).1
  have k_v36 : v36 = 1 := ((e_v37).1 k_v37).2
  have k_v191 : v191 = 1 := ((e_v194).1 k_v194).1
  have k_v193 : v193 = 1 := ((e_v194).1 k_v194).2
  have f3 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f13 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v16) (sv v17) (sv v19) (L2.p_cos e_t1_2) (L2.p_addc (-4) e_v16 e_v15) e_v17 (L2.p_max e_v18 (L2.p_sel e_v19))
  have f27 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v25) (sv v26) (sv v28) (L2.p_cos e_t0_2) (L2.p_addc (4) e_v25 e_v24) e_v26 (L2.p_min e_v27 (L2.p_sel e_v28))
  have f2 := L2.K10_icos True (sv v0) (sv v1) (sv v19) (sv v17) v21 (sv v22) (sv v28) (sv v26) v30 (sv v31) f3 f13 e_v17 (L2.p_clt (843314855) e_v20 e_v21) (L2.p_sel e_v22) f27 e_v26 (L2.p_ltc (1) e_v29 e_v30) (L2.p_sel e_v31)
  have f42 := L2.K5_ihalf (sv v3) (sv v3) (sv v32) (sv v33) e_v32 e_v33
  have f46 := L2.K8_in_range True (sv v32) (sv v33) v34 (sv v10) v36 v37 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v35 e_v36) e_v37 (L2.X1_top _ k_v37)
  have f56 := L2.K3_cos_lo (sv v33) (sv t33.2) (sv v39) (sv v17) (sv v41) (L2.p_cos e_t33_2) (L2.p_addc (-4) (L2.p_add_comm e_v39) e_v15) e_v17 (L2.p_max e_v40 (L2.p_sel e_v41))
  let u44 : ℤ := L2.cosI (sv v32)
  let u45 : ℤ := (sv v24) + u44
  let u46 : ℕ := if u45 < (sv v26) then 1 else 0
  let u47 : ℤ := if u46 = 1 then u45 else (sv v26)
  have f70 := L2.K3_cos_hi (sv v32) u44 u45 (sv v26) u47 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u48 : ℕ := if (sv v32) < (sv v29) then 1 else 0
  let u49 : ℤ := if u48 = 1 then (sv v26) else u47
  have f45 := L2.K10_icos True (sv v32) (sv v33) (sv v41) (sv v17) v42 (sv v43) u47 (sv v26) u48 u49 f46 f56 e_v17 (L2.p_clt (843314855) e_v20 e_v42) (L2.p_sel e_v43) f70 e_v26 (L2.p_ltc (1) e_v29 (L2.p_ult _ _)) rfl
  have f85 := L2.K8_in_range True (sv v32) (sv v33) v34 (sv v10) v36 v37 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v35 e_v36) e_v37 (L2.X1_top _ k_v37)
  have f84 := L2.K9_isin True (sv v32) (sv v33) (sv t32.1) (sv t33.1) (sv v53) (sv v54) (sv v55) (sv v56) (sv v26) (sv v58) v60 v62 v63 (sv v64) f85 (L2.p_sin e_t32_1) (L2.p_sin e_t33_1) (L2.p_min e_v52 (L2.p_sel e_v53)) (L2.p_addc (-4) (L2.p_add_comm e_v54) e_v15) (L2.p_max e_v52 (L2.p_sel e_v55)) (L2.p_addc (4) (L2.p_add_comm e_v56) e_v24) e_v26 (L2.p_min e_v57 (L2.p_sel e_v58)) (L2.p_ltc (421657430) e_v59 e_v60) (L2.p_clt (421657427) e_v61 e_v62) e_v63 (L2.p_sel e_v64)
  have f121 := L2.K6_imul True (sv v22) (sv v31) (sv v54) (sv v64) (sv v65) v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 (sv v82) v83 v84 (sv v85) v86 v87 (sv v88) v89 v90 (sv v91) (sv v93) (sv v95) e_v65 e_v66 e_v67 e_v68 e_v69 (L2.p_and_comm e_v70) e_v71 e_v72 e_v73 e_v74 e_v75 (L2.p_and_comm e_v76) e_v77 e_v78 e_v79 (L2.X1_top _ k_v79) e_v80 e_v81 (L2.p_sel e_v82) e_v83 e_v84 (L2.p_sel e_v85) e_v86 e_v87 (L2.p_sel e_v88) e_v89 e_v90 (L2.p_sel e_v91) (L2.p_mul (L2.p_mul_comm e_v92) e_v93) (L2.p_mulc (L2.p_mul_comm e_v94) e_v95)
  let u100 : ℕ := if u49 < (sv v65) then 1 else 0
  let u101 : ℤ := if u100 = 1 then (sv v95) else (sv v93)
  have f154 := L2.K11_qdiv (sv v43) u49 (sv v93) (sv v95) v96 v97 (sv v65) v98 (sv v99) u100 u101 (L2.p_clt (0) e_v65 e_v96) e_v97 e_v65 e_v98 (L2.p_sel e_v99) (L2.p_ult _ _) rfl
  have f172 := L2.K3_cos_lo (sv v104) (sv t104.2) (sv v107) (sv v17) (sv v109) (L2.p_cos e_t104_2) (L2.p_addc (-4) (L2.p_add_comm e_v107) e_v15) e_v17 (L2.p_max e_v108 (L2.p_sel e_v109))
  have f181 := L2.K3_cos_hi (sv v104) (sv t104.2) (sv v110) (sv v26) (sv v112) (L2.p_cos e_t104_2) (L2.p_addc (4) (L2.p_add_comm e_v110) e_v24) e_v26 (L2.p_min e_v111 (L2.p_sel e_v112))
  have f190 := L2.K3_sin_hi (sv v104) (sv t104.1) (sv v114) (sv v26) (sv v116) (L2.p_sin e_t104_1) (L2.p_addc (4) (L2.p_add_comm e_v114) e_v24) e_v26 (L2.p_min e_v115 (L2.p_sel e_v116))
  have f199 := L2.K3_sin_lo (sv v104) (sv t104.1) (sv v117) (L2.p_sin e_t104_1) (L2.p_addc (-4) (L2.p_add_comm e_v117) e_v15)
  have f165 := L2.K12_atan_lo (sv v43) (sv v99) (sv v65) v98 (sv v102) (sv v103) (sv v104) v105 (sv v109) (sv v112) (sv v116) (sv v117) (sv v118) (sv v119) (sv v120) (sv v121) v123 v125 v126 v127 (sv v128) v130 v131 v132 v133 v134 (sv v135) v137 v138 v139 v98 v140 v141 (sv v142) (sv v143) (sv v144) (sv v145) e_v65 e_v98 e_v102 (L2.p_sel e_v103) (L2.p_hint e_v104) e_v105 f172 f181 f190 f199 (L2.p_sel e_v118) (L2.p_sel e_v119) (L2.p_mul_comm e_v120) (L2.p_mul_comm e_v121) (L2.p_le e_v122 e_v123) (L2.p_le e_v124 e_v125) e_v126 e_v127 e_v128 (L2.p_le e_v129 e_v130) (L2.p_clt (-1) e_v8 e_v131) e_v132 (L2.p_and_comm e_v133) e_v134 e_v135 (L2.p_le e_v136 e_v137) (L2.p_or_comm e_v138) e_v139 (L2.p_not_not e_v105) e_v140 e_v141 e_v142 (L2.p_sel e_v143) e_v144 (L2.p_sel e_v145)
  let u146 : ℤ := (sv v65) - u49
  let u147 : ℤ := if u100 = 1 then u146 else u49
  let u148 : ℤ := 0
  let u149 : ℤ := L2.cosI u148
  let u150 : ℤ := (sv v15) + u149
  let u151 : ℕ := if u150 < (sv v17) then 1 else 0
  let u152 : ℤ := if u151 = 1 then (sv v17) else u150
  have f245 := L2.K3_cos_lo u148 u149 u150 (sv v17) u152 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u153 : ℤ := (sv v24) + u149
  let u154 : ℕ := if u153 < (sv v26) then 1 else 0
  let u155 : ℤ := if u154 = 1 then u153 else (sv v26)
  have f254 := L2.K3_cos_hi u148 u149 u153 (sv v26) u155 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u156 : ℤ := L2.sinI u148
  let u157 : ℤ := (sv v24) + u156
  let u158 : ℕ := if u157 < (sv v26) then 1 else 0
  let u159 : ℤ := if u158 = 1 then u157 else (sv v26)
  have f263 := L2.K3_sin_hi u148 u156 u157 (sv v26) u159 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u160 : ℤ := (sv v15) + u156
  have f272 := L2.K3_sin_lo u148 u156 u160 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15)
  let u161 : ℤ := if u100 = 1 then u152 else u155
  let u162 : ℤ := if u100 = 1 then u159 else u160
  let u163 : ℤ := u101 * u162
  let u164 : ℤ := u147 * u161
  let u165 : ℕ := if u164 < u163 then 1 else 0
  let u166 : ℕ := if u165 = 1 then 0 else 1
  let u167 : ℕ := if u163 < u164 then 1 else 0
  let u168 : ℕ := if u167 = 1 then 0 else 1
  let u169 : ℕ := if (sv v65) < u148 then 1 else 0
  let u170 : ℕ := if u169 = 1 then 0 else 1
  let u171 : ℕ := if (sv v128) < u148 then 1 else 0
  let u172 : ℕ := if u171 = 1 then 0 else 1
  let u173 : ℕ := if (sv v8) < u152 then 1 else 0
  let u174 : ℕ := if u166 = 1 ∧ u173 = 1 then 1 else 0
  let u175 : ℕ := if u172 = 1 ∧ u174 = 1 then 1 else 0
  let u176 : ℕ := if u170 = 1 ∨ u175 = 1 then 1 else 0
  let u177 : ℕ := if u148 < (sv v135) then 1 else 0
  let u178 : ℕ := if u177 = 1 then 0 else 1
  let u179 : ℕ := if u168 = 1 ∨ u178 = 1 then 1 else 0
  let u180 : ℕ := if u100 = 1 ∧ u176 = 1 then 1 else 0
  let u181 : ℕ := if u100 = 1 then 0 else 1
  let u182 : ℕ := if u179 = 1 ∧ u181 = 1 then 1 else 0
  let u183 : ℕ := if u180 = 1 ∨ u182 = 1 then 1 else 0
  let u184 : ℤ := (sv v65) - u148
  let u185 : ℤ := if u100 = 1 then u184 else u148
  let u186 : ℤ := if u183 = 1 then u185 else (sv v135)
  have f239 := L2.K12_atan_hi u49 u101 (sv v65) u100 u146 u147 u148 u152 u155 u159 u160 u161 u162 u163 u164 u166 u168 u169 u170 (sv v128) u172 u173 u174 u175 u176 (sv v135) u178 u179 u180 u181 u182 u183 u184 u185 (sv v135) u186 e_v65 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f245 f254 f263 f272 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v128 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v135 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v135 rfl
  let u188 : ℤ := if v97 = 1 then (sv v135) else u186
  have f41 := L2.K19_iso_angle_pt True (sv v3) (sv v22) (sv v31) (sv v32) (sv v33) (sv v43) u49 (sv v54) (sv v64) (sv v93) (sv v95) (sv v99) u101 v97 v96 (sv v145) u186 (sv v144) (sv v135) (sv v187) u188 f42 f45 f84 f121 f154 (L2.p_not_not e_v97) f165 f239 e_v144 e_v135 (L2.p_sel e_v187) rfl
  have f317 := L2.K5_ihalf (sv v2) (sv v2) (sv v189) (sv v190) e_v189 e_v190
  have f321 := L2.K8_in_range True (sv v189) (sv v190) v191 (sv v10) v193 v194 (L2.p_clt (-1) e_v8 e_v191) e_v10 (L2.p_le e_v192 e_v193) e_v194 (L2.X1_top _ k_v194)
  let u195 : ℤ := L2.cosI (sv v190)
  let u196 : ℤ := (sv v15) + u195
  let u197 : ℕ := if u196 < (sv v17) then 1 else 0
  let u198 : ℤ := if u197 = 1 then (sv v17) else u196
  have f331 := L2.K3_cos_lo (sv v190) u195 u196 (sv v17) u198 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u199 : ℕ := if (sv v20) < (sv v190) then 1 else 0
  let u200 : ℤ := if u199 = 1 then (sv v17) else u198
  let u201 : ℤ := L2.cosI (sv v189)
  let u202 : ℤ := (sv v24) + u201
  let u203 : ℕ := if u202 < (sv v26) then 1 else 0
  let u204 : ℤ := if u203 = 1 then u202 else (sv v26)
  have f345 := L2.K3_cos_hi (sv v189) u201 u202 (sv v26) u204 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u205 : ℕ := if (sv v189) < (sv v29) then 1 else 0
  let u206 : ℤ := if u205 = 1 then (sv v26) else u204
  have f320 := L2.K10_icos True (sv v189) (sv v190) u198 (sv v17) u199 u200 u204 (sv v26) u205 u206 f321 f331 e_v17 (L2.p_clt (843314855) e_v20 (L2.p_ult _ _)) rfl f345 e_v26 (L2.p_ltc (1) e_v29 (L2.p_ult _ _)) rfl
  have f360 := L2.K8_in_range True (sv v189) (sv v190) v191 (sv v10) v193 v194 (L2.p_clt (-1) e_v8 e_v191) e_v10 (L2.p_le e_v192 e_v193) e_v194 (L2.X1_top _ k_v194)
  have f359 := L2.K9_isin True (sv v189) (sv v190) (sv t189.1) (sv t190.1) (sv v210) (sv v211) (sv v212) (sv v213) (sv v26) (sv v215) v216 v217 v218 (sv v219) f360 (L2.p_sin e_t189_1) (L2.p_sin e_t190_1) (L2.p_min e_v209 (L2.p_sel e_v210)) (L2.p_addc (-4) (L2.p_add_comm e_v211) e_v15) (L2.p_max e_v209 (L2.p_sel e_v212)) (L2.p_addc (4) (L2.p_add_comm e_v213) e_v24) e_v26 (L2.p_min e_v214 (L2.p_sel e_v215)) (L2.p_ltc (421657430) e_v59 e_v216) (L2.p_clt (421657427) e_v61 e_v217) e_v218 (L2.p_sel e_v219)
  let u221 : ℕ := if v220 = 1 then 0 else 1
  let u223 : ℕ := if v222 = 1 then 0 else 1
  let u224 : ℕ := if v220 = 1 ∧ u223 = 1 then 1 else 0
  let u228 : ℕ := if v67 = 1 ∧ v225 = 1 then 1 else 0
  let u229 : ℕ := if u224 = 1 ∨ u228 = 1 then 1 else 0
  let u230 : ℤ := if u229 = 1 then (sv v31) else (sv v22)
  let u231 : ℕ := if v71 = 1 ∧ u221 = 1 then 1 else 0
  let u232 : ℕ := if v70 = 1 ∨ u231 = 1 then 1 else 0
  let u233 : ℤ := if u232 = 1 then (sv v219) else (sv v211)
  let u234 : ℕ := if v70 = 1 ∧ v225 = 1 then 1 else 0
  let u235 : ℕ := if u224 = 1 ∨ u234 = 1 then 1 else 0
  let u236 : ℤ := if u235 = 1 then (sv v22) else (sv v31)
  let u237 : ℕ := if v71 = 1 ∧ u224 = 1 then 1 else 0
  let u238 : ℕ := if v70 = 1 ∨ u237 = 1 then 1 else 0
  let u239 : ℤ := if u238 = 1 then (sv v211) else (sv v219)
  let u240 : ℤ := u230 * u233
  let u241 : ℤ := u240 / 2 ^ 28
  let u242 : ℤ := u236 * u239
  let u243 : ℤ := -((-u242) / 2 ^ 28)
  have f396 := L2.K6_imul True (sv v22) (sv v31) (sv v211) (sv v219) (sv v65) v66 v67 v68 v69 v70 v71 v220 u221 v222 u223 u224 v225 v226 v227 u228 u229 u230 u231 u232 u233 u234 u235 u236 u237 u238 u239 u241 u243 e_v65 e_v66 e_v67 e_v68 e_v69 (L2.p_and_comm e_v70) e_v71 e_v220 (L2.p_unot _) e_v222 (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) e_v225 e_v226 e_v227 (L2.X1_top _ k_v227) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl)
  let u244 : ℕ := if (sv v65) < u241 then 1 else 0
  let u245 : ℕ := if u244 = 1 then 0 else 1
  let u246 : ℕ := if u200 < (sv v65) then 1 else 0
  let u247 : ℤ := if u246 = 1 then u241 else u243
  let u248 : ℕ := if u206 < (sv v65) then 1 else 0
  let u249 : ℤ := if u248 = 1 then u243 else u241
  have f429 := L2.K11_qdiv u200 u206 u241 u243 u244 u245 (sv v65) u246 u247 u248 u249 (L2.p_clt (0) e_v65 (L2.p_ult _ _)) (L2.p_unot _) e_v65 (L2.p_ult _ _) rfl (L2.p_ult _ _) rfl
  let u250 : ℤ := (sv v65) - u200
  let u251 : ℤ := if u246 = 1 then u250 else u200
  let u252 : ℤ := 0
  let u253 : ℕ := if u246 = 1 then 0 else 1
  let u254 : ℤ := L2.cosI u252
  let u255 : ℤ := (sv v15) + u254
  let u256 : ℕ := if u255 < (sv v17) then 1 else 0
  let u257 : ℤ := if u256 = 1 then (sv v17) else u255
  have f447 := L2.K3_cos_lo u252 u254 u255 (sv v17) u257 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u258 : ℤ := (sv v24) + u254
  let u259 : ℕ := if u258 < (sv v26) then 1 else 0
  let u260 : ℤ := if u259 = 1 then u258 else (sv v26)
  have f456 := L2.K3_cos_hi u252 u254 u258 (sv v26) u260 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u261 : ℤ := L2.sinI u252
  let u262 : ℤ := (sv v24) + u261
  let u263 : ℕ := if u262 < (sv v26) then 1 else 0
  let u264 : ℤ := if u263 = 1 then u262 else (sv v26)
  have f465 := L2.K3_sin_hi u252 u261 u262 (sv v26) u264 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u265 : ℤ := (sv v15) + u261
  have f474 := L2.K3_sin_lo u252 u261 u265 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15)
  let u266 : ℤ := if u253 = 1 then u257 else u260
  let u267 : ℤ := if u253 = 1 then u264 else u265
  let u268 : ℤ := u247 * u267
  let u269 : ℤ := u251 * u266
  let u270 : ℕ := if u269 < u268 then 1 else 0
  let u271 : ℕ := if u270 = 1 then 0 else 1
  let u272 : ℕ := if u268 < u269 then 1 else 0
  let u273 : ℕ := if u272 = 1 then 0 else 1
  let u274 : ℕ := if (sv v65) < u252 then 1 else 0
  let u275 : ℕ := if u274 = 1 then 0 else 1
  let u276 : ℕ := if (sv v128) < u252 then 1 else 0
  let u277 : ℕ := if u276 = 1 then 0 else 1
  let u278 : ℕ := if (sv v8) < u257 then 1 else 0
  let u279 : ℕ := if u271 = 1 ∧ u278 = 1 then 1 else 0
  let u280 : ℕ := if u277 = 1 ∧ u279 = 1 then 1 else 0
  let u281 : ℕ := if u275 = 1 ∨ u280 = 1 then 1 else 0
  let u282 : ℕ := if u252 < (sv v135) then 1 else 0
  let u283 : ℕ := if u282 = 1 then 0 else 1
  let u284 : ℕ := if u273 = 1 ∨ u283 = 1 then 1 else 0
  let u285 : ℕ := if u253 = 1 ∧ u281 = 1 then 1 else 0
  let u286 : ℕ := if u246 = 1 ∧ u284 = 1 then 1 else 0
  let u287 : ℕ := if u285 = 1 ∨ u286 = 1 then 1 else 0
  let u288 : ℤ := (sv v65) - u252
  let u289 : ℤ := if u246 = 1 then u288 else u252
  let u290 : ℤ := if u287 = 1 then u289 else (sv v144)
  have f440 := L2.K12_atan_lo u200 u247 (sv v65) u246 u250 u251 u252 u253 u257 u260 u264 u265 u266 u267 u268 u269 u271 u273 u274 u275 (sv v128) u277 u278 u279 u280 u281 (sv v135) u283 u284 u285 u246 u286 u287 u288 u289 (sv v144) u290 e_v65 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f447 f456 f465 f474 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v128 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v135 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl e_v144 rfl
  let u291 : ℤ := (sv v65) - u206
  let u292 : ℤ := if u248 = 1 then u291 else u206
  let u293 : ℤ := 0
  let u294 : ℤ := L2.cosI u293
  let u295 : ℤ := (sv v15) + u294
  let u296 : ℕ := if u295 < (sv v17) then 1 else 0
  let u297 : ℤ := if u296 = 1 then (sv v17) else u295
  have f520 := L2.K3_cos_lo u293 u294 u295 (sv v17) u297 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u298 : ℤ := (sv v24) + u294
  let u299 : ℕ := if u298 < (sv v26) then 1 else 0
  let u300 : ℤ := if u299 = 1 then u298 else (sv v26)
  have f529 := L2.K3_cos_hi u293 u294 u298 (sv v26) u300 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u301 : ℤ := L2.sinI u293
  let u302 : ℤ := (sv v24) + u301
  let u303 : ℕ := if u302 < (sv v26) then 1 else 0
  let u304 : ℤ := if u303 = 1 then u302 else (sv v26)
  have f538 := L2.K3_sin_hi u293 u301 u302 (sv v26) u304 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u305 : ℤ := (sv v15) + u301
  have f547 := L2.K3_sin_lo u293 u301 u305 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15)
  let u306 : ℤ := if u248 = 1 then u297 else u300
  let u307 : ℤ := if u248 = 1 then u304 else u305
  let u308 : ℤ := u249 * u307
  let u309 : ℤ := u292 * u306
  let u310 : ℕ := if u309 < u308 then 1 else 0
  let u311 : ℕ := if u310 = 1 then 0 else 1
  let u312 : ℕ := if u308 < u309 then 1 else 0
  let u313 : ℕ := if u312 = 1 then 0 else 1
  let u314 : ℕ := if (sv v65) < u293 then 1 else 0
  let u315 : ℕ := if u314 = 1 then 0 else 1
  let u316 : ℕ := if (sv v128) < u293 then 1 else 0
  let u317 : ℕ := if u316 = 1 then 0 else 1
  let u318 : ℕ := if (sv v8) < u297 then 1 else 0
  let u319 : ℕ := if u311 = 1 ∧ u318 = 1 then 1 else 0
  let u320 : ℕ := if u317 = 1 ∧ u319 = 1 then 1 else 0
  let u321 : ℕ := if u315 = 1 ∨ u320 = 1 then 1 else 0
  let u322 : ℕ := if u293 < (sv v135) then 1 else 0
  let u323 : ℕ := if u322 = 1 then 0 else 1
  let u324 : ℕ := if u313 = 1 ∨ u323 = 1 then 1 else 0
  let u325 : ℕ := if u248 = 1 ∧ u321 = 1 then 1 else 0
  let u326 : ℕ := if u248 = 1 then 0 else 1
  let u327 : ℕ := if u324 = 1 ∧ u326 = 1 then 1 else 0
  let u328 : ℕ := if u325 = 1 ∨ u327 = 1 then 1 else 0
  let u329 : ℤ := (sv v65) - u293
  let u330 : ℤ := if u248 = 1 then u329 else u293
  let u331 : ℤ := if u328 = 1 then u330 else (sv v135)
  have f514 := L2.K12_atan_hi u206 u249 (sv v65) u248 u291 u292 u293 u297 u300 u304 u305 u306 u307 u308 u309 u311 u313 u314 u315 (sv v128) u317 u318 u319 u320 u321 (sv v135) u323 u324 u325 u326 u327 u328 u329 u330 (sv v135) u331 e_v65 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f520 f529 f538 f547 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v128 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v135 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v135 rfl
  let u332 : ℤ := if u245 = 1 then (sv v144) else u290
  let u333 : ℤ := if u245 = 1 then (sv v135) else u331
  have f316 := L2.K19_iso_angle_pt True (sv v2) (sv v22) (sv v31) (sv v189) (sv v190) u200 u206 (sv v211) (sv v219) u241 u243 u247 u249 u245 u244 u290 u331 (sv v144) (sv v135) u332 u333 f317 f320 f359 f396 f429 (L2.p_not_not (L2.p_unot _)) f440 f514 e_v144 e_v135 rfl rfl
  have f1 := L2.K20_iso_angle True (sv v2) (sv v3) (sv v0) (sv v1) (sv v22) (sv v31) (sv v187) u188 v97 u332 u333 u245 f2 f41 f316
  let u335 : ℤ := u333 + u333
  have f591 := L2.K4_iadd (sv v187) u333 (sv v187) u333 (sv v334) u335 e_v334 rfl
  let u338 : ℕ := if (sv v6) < u335 then 1 else 0
  let u339 : ℕ := if u338 = 1 then 0 else 1
  exact Tammes15.D3Trig.TR false F0 F1 F2 F3 hD (sv v0) (sv v1) (sv v2) (sv v3) (sv v6) (0 : ℕ) (sv v187) u333 (sv v334) u335 v337 u339 v337 e_v0 e_v1 e_v2 e_v3 e_v6 (of_decide_eq_true rfl) f1 f591 (L2.p_le e_v336 e_v337) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_sel_f _ _) (L2.X1_top _ k_v337)

end Tammes15.D3Trig
