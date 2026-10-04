import Tammes15.D3Trig.Prog.RH
import Tammes15.D3Prog.L2.Kinds
import Tammes15.D3Prog.L2.PLib
import Tammes15.D3Trig.RhoKinds

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem progRH_l2 (F0 F1 F2 F3 H0 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (h : Tammes15.D3Trig.progRH 1 F0 F1 F2 F3 H0 = 1) (hD : D3Prog.L2.InDom F0 F1 F2 F3) : LaneClaimR 0 true F0 F1 F2 F3 := by
  unfold Tammes15.D3Trig.progRH at h
  extract_lets -merge OFFr H61r v0 v1 v2 v3 v6 v8 v9 v10 v11 v12 v13 t1 v15 v16 v17 v18 v19 v20 v21 v22 t0 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 t32 t33 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v74 v77 v78 v79 v128 v135 v189 v190 v191 v192 v193 v194 t189 v202 v203 v204 v205 v206 t190 v209 v210 v211 v212 v213 v214 v215 v216 v217 v218 v219 v220 v221 v222 v223 v224 v225 v226 v227 v228 v229 v230 v231 v232 v233 v234 v235 v236 v237 v238 v239 v240 v241 v242 v243 v244 v245 v248 v249 v291 v292 v293 t293 v295 v296 v297 v298 v299 v300 v302 v303 v304 v305 v306 v307 v308 v309 v310 v311 v312 v313 v314 v315 v316 v317 v318 v319 v320 v321 v322 v323 v324 v325 v326 v327 v328 v329 v330 v331 v333 v335 v338 v339 v340 v341 v342 v343 v344 v345 v346 at h
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
  clear h_v1 h_v9 h_v12 h_t1_1 h_t1_2 e_t1_1 h_v16 h_v18 h_v19 h_v20 h_v21 h_t0_1 e_t0_1
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
  clear h_v0 h_v3 h_t0_2 h_v25 h_v27 h_v28 h_v30
  have e_v36 : (v36 = 1 ↔ ¬v35 = 1) := e_not h_v35 (of_decide_eq_true rfl)
  have h_v37 : R 1 0 0 1 v37 v37 := (r_land hl h_v34 h_v36 (of_decide_eq_true rfl))
  have e_v37 : (v37 = 1 ↔ v34 = 1 ∧ v36 = 1) := e_land h_v34 h_v36 (of_decide_eq_true rfl)
  have h_t32_1 : R 1 0 4611686018427387904 4611686018695823363 t32.1 t32.1 := r_sc1 hl h_v32 (of_decide_eq_true rfl)
  have h_t32_2 : R 1 0 4611686018158952445 4611686018695823363 t32.2 t32.2 := r_sc2 hl h_v32 (of_decide_eq_true rfl)
  have e_t32_1 : sv t32.1 = (sc28pS (scArg v32)).1 := e_sc1 h_v32 (of_decide_eq_true rfl)
  have e_t32_2 : sv t32.2 = (sc28pS (scArg v32)).2 := e_sc2 h_v32 (of_decide_eq_true rfl)
  have h_t33_1 : R 1 0 4611686018427387904 4611686018695823363 t33.1 t33.1 := r_sc1 hl h_v33 (of_decide_eq_true rfl)
  have h_t33_2 : R 1 0 4611686018158952445 4611686018695823363 t33.2 t33.2 := r_sc2 hl h_v33 (of_decide_eq_true rfl)
  have e_t33_1 : sv t33.1 = (sc28pS (scArg v33)).1 := e_sc1 h_v33 (of_decide_eq_true rfl)
  have e_t33_2 : sv t33.2 = (sc28pS (scArg v33)).2 := e_sc2 h_v33 (of_decide_eq_true rfl)
  have h_v52 : R 1 0 0 1 v52 v52 := (r_plt hl h_t32_1 h_t33_1 (of_decide_eq_true rfl))
  have e_v52 : (v52 = 1 ↔ sv t32.1 < sv t33.1) := e_plt h_t32_1 h_t33_1 (of_decide_eq_true rfl)
  have h_v53 : R 1 0 4611686018427387904 4611686018695823363 v53 v53 := (r_psel hl h_v52 h_t32_1 h_t33_1 (of_decide_eq_true rfl))
  have e_v53 : v53 = if v52 = 1 then t32.1 else t33.1 := e_psel h_v52 h_t32_1 h_t33_1 (of_decide_eq_true rfl)
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
  clear h_v34 h_v35 h_v36 h_t32_1 h_t32_2 e_t32_2 h_t33_1 h_t33_2 e_t33_2 h_v52 h_v53 h_v55 h_v56 h_v57
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
  clear h_v32 h_v33 h_v58 h_v60 h_v62 h_v63 h_v69
  have e_v71 : (v71 = 1 ↔ v66 = 1 ∧ v68 = 1) := e_land h_v66 h_v68 (of_decide_eq_true rfl)
  have h_v72 : R 1 0 0 1 v72 v72 := (r_plt hl h_v54 h_v65 (of_decide_eq_true rfl))
  have e_v72 : (v72 = 1 ↔ sv v54 < sv v65) := e_plt h_v54 h_v65 (of_decide_eq_true rfl)
  have h_v74 : R 1 0 0 1 v74 v74 := (r_plt hl h_v65 h_v64 (of_decide_eq_true rfl))
  have e_v74 : (v74 = 1 ↔ sv v65 < sv v64) := e_plt h_v65 h_v64 (of_decide_eq_true rfl)
  have h_v77 : R 1 0 0 1 v77 v77 := (r_land hl h_v72 h_v74 (of_decide_eq_true rfl))
  have e_v77 : (v77 = 1 ↔ v72 = 1 ∧ v74 = 1) := e_land h_v72 h_v74 (of_decide_eq_true rfl)
  have h_v78 : R 1 0 0 1 v78 v78 := (r_land hl h_v71 h_v77 (of_decide_eq_true rfl))
  have e_v78 : (v78 = 1 ↔ v71 = 1 ∧ v77 = 1) := e_land h_v71 h_v77 (of_decide_eq_true rfl)
  have h_v79 : R 1 0 0 1 v79 v79 := (r_sub hl (r_O hl) h_v78 (of_decide_eq_true rfl))
  have e_v79 : (v79 = 1 ↔ ¬v78 = 1) := e_not h_v78 (of_decide_eq_true rfl)
  have h_v128 : R 1 0 4611686018849045332 4611686018849045332 v128 v128 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  have e_v128 : sv v128 = (421657428) := e_c 4611686018849045332 (421657428) (of_decide_eq_true rfl)
  have h_v135 : R 1 0 4611686018849045333 4611686018849045333 v135 v135 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have e_v135 : sv v135 = (421657429) := e_c 4611686018849045333 (421657429) (of_decide_eq_true rfl)
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
  clear h_H61r h_v2 h_v10 h_v54 h_v64 h_v66 h_v68 h_v72 h_v74 h_v77 h_v78 h_v192
  have h_v194 : R 1 0 0 1 v194 v194 := (r_land hl h_v191 h_v193 (of_decide_eq_true rfl))
  have e_v194 : (v194 = 1 ↔ v191 = 1 ∧ v193 = 1) := e_land h_v191 h_v193 (of_decide_eq_true rfl)
  have h_t189_1 : R 1 0 4611686018427387904 4611686018695823363 t189.1 t189.1 := r_sc1 hl h_v189 (of_decide_eq_true rfl)
  have h_t189_2 : R 1 0 4611686018158952445 4611686018695823363 t189.2 t189.2 := r_sc2 hl h_v189 (of_decide_eq_true rfl)
  have e_t189_1 : sv t189.1 = (sc28pS (scArg v189)).1 := e_sc1 h_v189 (of_decide_eq_true rfl)
  have e_t189_2 : sv t189.2 = (sc28pS (scArg v189)).2 := e_sc2 h_v189 (of_decide_eq_true rfl)
  have h_v202 : R 1 0 4611686018158952449 4611686018695823367 v202 v202 := (r_sub hl (r_add hl h_v24 h_t189_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v202 : sv v202 = sv v24 + sv t189.2 := e_add h_v24 h_t189_2 (of_decide_eq_true rfl)
  have h_v203 : R 1 0 0 1 v203 v203 := (r_plt hl h_v202 h_v26 (of_decide_eq_true rfl))
  have e_v203 : (v203 = 1 ↔ sv v202 < sv v26) := e_plt h_v202 h_v26 (of_decide_eq_true rfl)
  have h_v204 : R 1 0 4611686018158952449 4611686018695823367 v204 v204 := (r_psel hl h_v203 h_v202 h_v26 (of_decide_eq_true rfl))
  have e_v204 : v204 = if v203 = 1 then v202 else v26 := e_psel h_v203 h_v202 h_v26 (of_decide_eq_true rfl)
  have h_v205 : R 1 0 0 1 v205 v205 := (r_plt hl h_v189 h_v29 (of_decide_eq_true rfl))
  have e_v205 : (v205 = 1 ↔ sv v189 < sv v29) := e_plt h_v189 h_v29 (of_decide_eq_true rfl)
  have h_v206 : R 1 0 4611686018158952449 4611686018695823367 v206 v206 := (r_psel hl h_v205 h_v26 h_v204 (of_decide_eq_true rfl))
  have e_v206 : v206 = if v205 = 1 then v26 else v204 := e_psel h_v205 h_v26 h_v204 (of_decide_eq_true rfl)
  have h_t190_1 : R 1 0 4611686018427387904 4611686018695823363 t190.1 t190.1 := r_sc1 hl h_v190 (of_decide_eq_true rfl)
  have h_t190_2 : R 1 0 4611686018158952445 4611686018695823363 t190.2 t190.2 := r_sc2 hl h_v190 (of_decide_eq_true rfl)
  have e_t190_1 : sv t190.1 = (sc28pS (scArg v190)).1 := e_sc1 h_v190 (of_decide_eq_true rfl)
  have e_t190_2 : sv t190.2 = (sc28pS (scArg v190)).2 := e_sc2 h_v190 (of_decide_eq_true rfl)
  have h_v209 : R 1 0 0 1 v209 v209 := (r_plt hl h_t189_1 h_t190_1 (of_decide_eq_true rfl))
  have e_v209 : (v209 = 1 ↔ sv t189.1 < sv t190.1) := e_plt h_t189_1 h_t190_1 (of_decide_eq_true rfl)
  have h_v210 : R 1 0 4611686018427387904 4611686018695823363 v210 v210 := (r_psel hl h_v209 h_t189_1 h_t190_1 (of_decide_eq_true rfl))
  have e_v210 : v210 = if v209 = 1 then t189.1 else t190.1 := e_psel h_v209 h_t189_1 h_t190_1 (of_decide_eq_true rfl)
  have h_v211 : R 1 0 4611686018427387900 4611686018695823359 v211 v211 := (r_sub hl (r_add hl h_v15 h_v210 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v29 h_v191 h_v193 h_t189_2 h_v202 h_v203 h_v204 h_v205 h_t190_2 e_t190_2
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
  have e_v220 : (v220 = 1 ↔ sv v211 < sv v65) := e_plt h_v211 h_v65 (of_decide_eq_true rfl)
  have h_v221 : R 1 0 0 1 v221 v221 := (r_sub hl (r_O hl) h_v220 (of_decide_eq_true rfl))
  have e_v221 : (v221 = 1 ↔ ¬v220 = 1) := e_not h_v220 (of_decide_eq_true rfl)
  have h_v222 : R 1 0 0 1 v222 v222 := (r_plt hl h_v65 h_v219 (of_decide_eq_true rfl))
  have e_v222 : (v222 = 1 ↔ sv v65 < sv v219) := e_plt h_v65 h_v219 (of_decide_eq_true rfl)
  have h_v223 : R 1 0 0 1 v223 v223 := (r_sub hl (r_O hl) h_v222 (of_decide_eq_true rfl))
  have e_v223 : (v223 = 1 ↔ ¬v222 = 1) := e_not h_v222 (of_decide_eq_true rfl)
  clear h_v59 h_v61 h_v189 h_v190 h_t189_1 h_t190_1 h_v209 h_v210 h_v212 h_v213 h_v214 h_v215 h_v216 h_v217 h_v218
  have h_v224 : R 1 0 0 1 v224 v224 := (r_land hl h_v220 h_v223 (of_decide_eq_true rfl))
  have e_v224 : (v224 = 1 ↔ v220 = 1 ∧ v223 = 1) := e_land h_v220 h_v223 (of_decide_eq_true rfl)
  have h_v225 : R 1 0 0 1 v225 v225 := (r_land hl h_v220 h_v222 (of_decide_eq_true rfl))
  have e_v225 : (v225 = 1 ↔ v220 = 1 ∧ v222 = 1) := e_land h_v220 h_v222 (of_decide_eq_true rfl)
  have h_v226 : R 1 0 0 1 v226 v226 := (r_land hl h_v71 h_v225 (of_decide_eq_true rfl))
  have e_v226 : (v226 = 1 ↔ v71 = 1 ∧ v225 = 1) := e_land h_v71 h_v225 (of_decide_eq_true rfl)
  have h_v227 : R 1 0 0 1 v227 v227 := (r_sub hl (r_O hl) h_v226 (of_decide_eq_true rfl))
  have e_v227 : (v227 = 1 ↔ ¬v226 = 1) := e_not h_v226 (of_decide_eq_true rfl)
  have h_v228 : R 1 0 0 1 v228 v228 := (r_land hl h_v67 h_v225 (of_decide_eq_true rfl))
  have e_v228 : (v228 = 1 ↔ v67 = 1 ∧ v225 = 1) := e_land h_v67 h_v225 (of_decide_eq_true rfl)
  have h_v229 : R 1 0 0 1 v229 v229 := (r_lor hl h_v224 h_v228 (of_decide_eq_true rfl))
  have e_v229 : (v229 = 1 ↔ v224 = 1 ∨ v228 = 1) := e_lor h_v224 h_v228 (of_decide_eq_true rfl)
  have h_v230 : R 1 0 4611686018158952441 4611686018695823367 v230 v230 := (r_psel hl h_v229 h_v31 h_v22 (of_decide_eq_true rfl))
  have e_v230 : v230 = if v229 = 1 then v31 else v22 := e_psel h_v229 h_v31 h_v22 (of_decide_eq_true rfl)
  have h_v231 : R 1 0 0 1 v231 v231 := (r_land hl h_v71 h_v221 (of_decide_eq_true rfl))
  have e_v231 : (v231 = 1 ↔ v71 = 1 ∧ v221 = 1) := e_land h_v71 h_v221 (of_decide_eq_true rfl)
  have h_v232 : R 1 0 0 1 v232 v232 := (r_lor hl h_v70 h_v231 (of_decide_eq_true rfl))
  have e_v232 : (v232 = 1 ↔ v70 = 1 ∨ v231 = 1) := e_lor h_v70 h_v231 (of_decide_eq_true rfl)
  have h_v233 : R 1 0 4611686018427387900 4611686018695823367 v233 v233 := (r_psel hl h_v232 h_v219 h_v211 (of_decide_eq_true rfl))
  have e_v233 : v233 = if v232 = 1 then v219 else v211 := e_psel h_v232 h_v219 h_v211 (of_decide_eq_true rfl)
  have h_v234 : R 1 0 0 1 v234 v234 := (r_land hl h_v70 h_v225 (of_decide_eq_true rfl))
  have e_v234 : (v234 = 1 ↔ v70 = 1 ∧ v225 = 1) := e_land h_v70 h_v225 (of_decide_eq_true rfl)
  have h_v235 : R 1 0 0 1 v235 v235 := (r_lor hl h_v224 h_v234 (of_decide_eq_true rfl))
  have e_v235 : (v235 = 1 ↔ v224 = 1 ∨ v234 = 1) := e_lor h_v224 h_v234 (of_decide_eq_true rfl)
  have h_v236 : R 1 0 4611686018158952441 4611686018695823367 v236 v236 := (r_psel hl h_v235 h_v22 h_v31 (of_decide_eq_true rfl))
  clear h_v67 h_v220 h_v221 h_v222 h_v223 h_v225 h_v226 h_v228 h_v229 h_v231 h_v232 h_v234
  have e_v236 : v236 = if v235 = 1 then v22 else v31 := e_psel h_v235 h_v22 h_v31 (of_decide_eq_true rfl)
  have h_v237 : R 1 0 0 1 v237 v237 := (r_land hl h_v71 h_v224 (of_decide_eq_true rfl))
  have e_v237 : (v237 = 1 ↔ v71 = 1 ∧ v224 = 1) := e_land h_v71 h_v224 (of_decide_eq_true rfl)
  have h_v238 : R 1 0 0 1 v238 v238 := (r_lor hl h_v70 h_v237 (of_decide_eq_true rfl))
  have e_v238 : (v238 = 1 ↔ v70 = 1 ∨ v237 = 1) := e_lor h_v70 h_v237 (of_decide_eq_true rfl)
  have h_v239 : R 1 0 4611686018427387900 4611686018695823367 v239 v239 := (r_psel hl h_v238 h_v211 h_v219 (of_decide_eq_true rfl))
  have e_v239 : v239 = if v238 = 1 then v211 else v219 := e_psel h_v238 h_v211 h_v219 (of_decide_eq_true rfl)
  have h_v240 : R 1 0 4539628420631363535 4683743616223412273 v240 v240 := (r_smx hl 29 h_v233 h_v230 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v240 : sv v240 = sv v233 * sv v230 := e_smx 29 h_v233 h_v230 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v241 : R 1 0 4611686018158952433 4611686018695823374 v241 v241 := (r_srdF hl h_v240 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v241 : sv v241 = sv v240 / 2 ^ 28 := e_srdF h_v240 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v242 : R 1 0 4539628420631363535 4683743616223412273 v242 v242 := (r_smx hl 29 h_v239 h_v236 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v242 : sv v242 = sv v239 * sv v236 := e_smx 29 h_v239 h_v236 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v243 : R 1 0 4611686018158952434 4611686018695823375 v243 v243 := (r_srdC hl h_v242 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v243 : sv v243 = -((-sv v242) / 2 ^ 28) := e_srdC h_v242 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v244 : R 1 0 0 1 v244 v244 := (r_plt hl h_v65 h_v241 (of_decide_eq_true rfl))
  have e_v244 : (v244 = 1 ↔ sv v65 < sv v241) := e_plt h_v65 h_v241 (of_decide_eq_true rfl)
  have h_v245 : R 1 0 0 1 v245 v245 := (r_sub hl (r_O hl) h_v244 (of_decide_eq_true rfl))
  have e_v245 : (v245 = 1 ↔ ¬v244 = 1) := e_not h_v244 (of_decide_eq_true rfl)
  have h_v248 : R 1 0 0 1 v248 v248 := (r_plt hl h_v206 h_v65 (of_decide_eq_true rfl))
  have e_v248 : (v248 = 1 ↔ sv v206 < sv v65) := e_plt h_v206 h_v65 (of_decide_eq_true rfl)
  have h_v249 : R 1 0 4611686018158952433 4611686018695823375 v249 v249 := (r_psel hl h_v248 h_v243 h_v241 (of_decide_eq_true rfl))
  have e_v249 : v249 = if v248 = 1 then v243 else v241 := e_psel h_v248 h_v243 h_v241 (of_decide_eq_true rfl)
  have h_v291 : R 1 0 4611686018158952441 4611686018695823359 v291 v291 := (r_sub hl (r_add hl h_v65 h_OFFr (of_decide_eq_true rfl)) h_v206 (of_decide_eq_true rfl))
  have e_v291 : sv v291 = sv v65 - sv v206 := e_sub h_v65 h_v206 (of_decide_eq_true rfl)
  clear h_v22 h_v31 h_v70 h_v71 h_v211 h_v219 h_v224 h_v230 h_v233 h_v235 h_v236 h_v237 h_v238 h_v239 h_v240 h_v241 h_v242 h_v243 h_v244
  have h_v292 : R 1 0 4611686018158952441 4611686018695823367 v292 v292 := (r_psel hl h_v248 h_v291 h_v206 (of_decide_eq_true rfl))
  have e_v292 : v292 = if v248 = 1 then v291 else v206 := e_psel h_v248 h_v291 h_v206 (of_decide_eq_true rfl)
  have h_v293 : R 1 0 4611686018427387904 4611686019501129727 v293 v293 := (r1_hxa hb_H0 0 (of_decide_eq_true rfl))
  have e_v293 : sv v293 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 0 (of_decide_eq_true rfl)
  have h_t293_1 : R 1 0 4611686018427387904 4611686018695823363 t293.1 t293.1 := r_sc1 hl h_v293 (of_decide_eq_true rfl)
  have h_t293_2 : R 1 0 4611686018158952445 4611686018695823363 t293.2 t293.2 := r_sc2 hl h_v293 (of_decide_eq_true rfl)
  have e_t293_1 : sv t293.1 = (sc28pS (scArg v293)).1 := e_sc1 h_v293 (of_decide_eq_true rfl)
  have e_t293_2 : sv t293.2 = (sc28pS (scArg v293)).2 := e_sc2 h_v293 (of_decide_eq_true rfl)
  have h_v295 : R 1 0 4611686018158952441 4611686018695823359 v295 v295 := (r_sub hl (r_add hl h_v15 h_t293_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v295 : sv v295 = sv v15 + sv t293.2 := e_add h_v15 h_t293_2 (of_decide_eq_true rfl)
  have h_v296 : R 1 0 0 1 v296 v296 := (r_plt hl h_v295 h_v17 (of_decide_eq_true rfl))
  have e_v296 : (v296 = 1 ↔ sv v295 < sv v17) := e_plt h_v295 h_v17 (of_decide_eq_true rfl)
  have h_v297 : R 1 0 4611686018158952441 4611686018695823359 v297 v297 := (r_psel hl h_v296 h_v17 h_v295 (of_decide_eq_true rfl))
  have e_v297 : v297 = if v296 = 1 then v17 else v295 := e_psel h_v296 h_v17 h_v295 (of_decide_eq_true rfl)
  have h_v298 : R 1 0 4611686018158952449 4611686018695823367 v298 v298 := (r_sub hl (r_add hl h_v24 h_t293_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v298 : sv v298 = sv v24 + sv t293.2 := e_add h_v24 h_t293_2 (of_decide_eq_true rfl)
  have h_v299 : R 1 0 0 1 v299 v299 := (r_plt hl h_v298 h_v26 (of_decide_eq_true rfl))
  have e_v299 : (v299 = 1 ↔ sv v298 < sv v26) := e_plt h_v298 h_v26 (of_decide_eq_true rfl)
  have h_v300 : R 1 0 4611686018158952449 4611686018695823367 v300 v300 := (r_psel hl h_v299 h_v298 h_v26 (of_decide_eq_true rfl))
  have e_v300 : v300 = if v299 = 1 then v298 else v26 := e_psel h_v299 h_v298 h_v26 (of_decide_eq_true rfl)
  have h_v302 : R 1 0 4611686018427387908 4611686018695823367 v302 v302 := (r_sub hl (r_add hl h_v24 h_t293_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v302 : sv v302 = sv v24 + sv t293.1 := e_add h_v24 h_t293_1 (of_decide_eq_true rfl)
  have h_v303 : R 1 0 0 1 v303 v303 := (r_plt hl h_v302 h_v26 (of_decide_eq_true rfl))
  have e_v303 : (v303 = 1 ↔ sv v302 < sv v26) := e_plt h_v302 h_v26 (of_decide_eq_true rfl)
  have h_v304 : R 1 0 4611686018427387908 4611686018695823367 v304 v304 := (r_psel hl h_v303 h_v302 h_v26 (of_decide_eq_true rfl))
  clear h_v17 h_v24 h_v206 h_v291 h_t293_2 h_v295 h_v296 h_v298 h_v299
  have e_v304 : v304 = if v303 = 1 then v302 else v26 := e_psel h_v303 h_v302 h_v26 (of_decide_eq_true rfl)
  have h_v305 : R 1 0 4611686018427387900 4611686018695823359 v305 v305 := (r_sub hl (r_add hl h_v15 h_t293_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v305 : sv v305 = sv v15 + sv t293.1 := e_add h_v15 h_t293_1 (of_decide_eq_true rfl)
  have h_v306 : R 1 0 4611686018158952441 4611686018695823367 v306 v306 := (r_psel hl h_v248 h_v297 h_v300 (of_decide_eq_true rfl))
  have e_v306 : v306 = if v248 = 1 then v297 else v300 := e_psel h_v248 h_v297 h_v300 (of_decide_eq_true rfl)
  have h_v307 : R 1 0 4611686018427387900 4611686018695823367 v307 v307 := (r_psel hl h_v248 h_v304 h_v305 (of_decide_eq_true rfl))
  have e_v307 : v307 = if v248 = 1 then v304 else v305 := e_psel h_v248 h_v304 h_v305 (of_decide_eq_true rfl)
  have h_v308 : R 1 0 4539628418483879831 4683743618370895977 v308 v308 := (r_smx hl 29 h_v249 h_v307 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v308 : sv v308 = sv v249 * sv v307 := e_smx 29 h_v249 h_v307 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v309 : R 1 0 4539628420631363535 4683743616223412273 v309 v309 := (r_smx hl 29 h_v306 h_v292 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v309 : sv v309 = sv v306 * sv v292 := e_smx 29 h_v306 h_v292 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v310 : R 1 0 0 1 v310 v310 := (r_plt hl h_v309 h_v308 (of_decide_eq_true rfl))
  have e_v310 : (v310 = 1 ↔ sv v309 < sv v308) := e_plt h_v309 h_v308 (of_decide_eq_true rfl)
  have h_v311 : R 1 0 0 1 v311 v311 := (r_sub hl (r_O hl) h_v310 (of_decide_eq_true rfl))
  have e_v311 : (v311 = 1 ↔ ¬v310 = 1) := e_not h_v310 (of_decide_eq_true rfl)
  have h_v312 : R 1 0 0 1 v312 v312 := (r_plt hl h_v308 h_v309 (of_decide_eq_true rfl))
  have e_v312 : (v312 = 1 ↔ sv v308 < sv v309) := e_plt h_v308 h_v309 (of_decide_eq_true rfl)
  have h_v313 : R 1 0 0 1 v313 v313 := (r_sub hl (r_O hl) h_v312 (of_decide_eq_true rfl))
  have e_v313 : (v313 = 1 ↔ ¬v312 = 1) := e_not h_v312 (of_decide_eq_true rfl)
  have h_v314 : R 1 0 0 1 v314 v314 := (r_plt hl h_v65 h_v293 (of_decide_eq_true rfl))
  have e_v314 : (v314 = 1 ↔ sv v65 < sv v293) := e_plt h_v65 h_v293 (of_decide_eq_true rfl)
  have h_v315 : R 1 0 0 1 v315 v315 := (r_sub hl (r_O hl) h_v314 (of_decide_eq_true rfl))
  have e_v315 : (v315 = 1 ↔ ¬v314 = 1) := e_not h_v314 (of_decide_eq_true rfl)
  have h_v316 : R 1 0 0 1 v316 v316 := (r_plt hl h_v128 h_v293 (of_decide_eq_true rfl))
  have e_v316 : (v316 = 1 ↔ sv v128 < sv v293) := e_plt h_v128 h_v293 (of_decide_eq_true rfl)
  clear h_v15 h_v26 h_v128 h_v249 h_v292 h_t293_1 h_v300 h_v302 h_v303 h_v304 h_v305 h_v306 h_v307 h_v308 h_v309 h_v310 h_v312 h_v314
  have h_v317 : R 1 0 0 1 v317 v317 := (r_sub hl (r_O hl) h_v316 (of_decide_eq_true rfl))
  have e_v317 : (v317 = 1 ↔ ¬v316 = 1) := e_not h_v316 (of_decide_eq_true rfl)
  have h_v318 : R 1 0 0 1 v318 v318 := (r_plt hl h_v8 h_v297 (of_decide_eq_true rfl))
  have e_v318 : (v318 = 1 ↔ sv v8 < sv v297) := e_plt h_v8 h_v297 (of_decide_eq_true rfl)
  have h_v319 : R 1 0 0 1 v319 v319 := (r_land hl h_v311 h_v318 (of_decide_eq_true rfl))
  have e_v319 : (v319 = 1 ↔ v311 = 1 ∧ v318 = 1) := e_land h_v311 h_v318 (of_decide_eq_true rfl)
  have h_v320 : R 1 0 0 1 v320 v320 := (r_land hl h_v317 h_v319 (of_decide_eq_true rfl))
  have e_v320 : (v320 = 1 ↔ v317 = 1 ∧ v319 = 1) := e_land h_v317 h_v319 (of_decide_eq_true rfl)
  have h_v321 : R 1 0 0 1 v321 v321 := (r_lor hl h_v315 h_v320 (of_decide_eq_true rfl))
  have e_v321 : (v321 = 1 ↔ v315 = 1 ∨ v320 = 1) := e_lor h_v315 h_v320 (of_decide_eq_true rfl)
  have h_v322 : R 1 0 0 1 v322 v322 := (r_plt hl h_v293 h_v135 (of_decide_eq_true rfl))
  have e_v322 : (v322 = 1 ↔ sv v293 < sv v135) := e_plt h_v293 h_v135 (of_decide_eq_true rfl)
  have h_v323 : R 1 0 0 1 v323 v323 := (r_sub hl (r_O hl) h_v322 (of_decide_eq_true rfl))
  have e_v323 : (v323 = 1 ↔ ¬v322 = 1) := e_not h_v322 (of_decide_eq_true rfl)
  have h_v324 : R 1 0 0 1 v324 v324 := (r_lor hl h_v313 h_v323 (of_decide_eq_true rfl))
  have e_v324 : (v324 = 1 ↔ v313 = 1 ∨ v323 = 1) := e_lor h_v313 h_v323 (of_decide_eq_true rfl)
  have h_v325 : R 1 0 0 1 v325 v325 := (r_land hl h_v248 h_v321 (of_decide_eq_true rfl))
  have e_v325 : (v325 = 1 ↔ v248 = 1 ∧ v321 = 1) := e_land h_v248 h_v321 (of_decide_eq_true rfl)
  have h_v326 : R 1 0 0 1 v326 v326 := (r_sub hl (r_O hl) h_v248 (of_decide_eq_true rfl))
  have e_v326 : (v326 = 1 ↔ ¬v248 = 1) := e_not h_v248 (of_decide_eq_true rfl)
  have h_v327 : R 1 0 0 1 v327 v327 := (r_land hl h_v324 h_v326 (of_decide_eq_true rfl))
  have e_v327 : (v327 = 1 ↔ v324 = 1 ∧ v326 = 1) := e_land h_v324 h_v326 (of_decide_eq_true rfl)
  have h_v328 : R 1 0 0 1 v328 v328 := (r_lor hl h_v325 h_v327 (of_decide_eq_true rfl))
  have e_v328 : (v328 = 1 ↔ v325 = 1 ∨ v327 = 1) := e_lor h_v325 h_v327 (of_decide_eq_true rfl)
  have h_v329 : R 1 0 4611686017353646081 4611686018427387904 v329 v329 := (r_sub hl (r_add hl h_v65 h_OFFr (of_decide_eq_true rfl)) h_v293 (of_decide_eq_true rfl))
  clear h_v8 h_v297 h_v311 h_v313 h_v315 h_v316 h_v317 h_v318 h_v319 h_v320 h_v321 h_v322 h_v323 h_v324 h_v325 h_v326 h_v327
  have e_v329 : sv v329 = sv v65 - sv v293 := e_sub h_v65 h_v293 (of_decide_eq_true rfl)
  have h_v330 : R 1 0 4611686017353646081 4611686019501129727 v330 v330 := (r_psel hl h_v248 h_v329 h_v293 (of_decide_eq_true rfl))
  have e_v330 : v330 = if v248 = 1 then v329 else v293 := e_psel h_v248 h_v329 h_v293 (of_decide_eq_true rfl)
  have h_v331 : R 1 0 4611686017353646081 4611686019501129727 v331 v331 := (r_psel hl h_v328 h_v330 h_v135 (of_decide_eq_true rfl))
  have e_v331 : v331 = if v328 = 1 then v330 else v135 := e_psel h_v328 h_v330 h_v135 (of_decide_eq_true rfl)
  have h_v333 : R 1 0 4611686017353646081 4611686019501129727 v333 v333 := (r_psel hl h_v245 h_v135 h_v331 (of_decide_eq_true rfl))
  have e_v333 : v333 = if v245 = 1 then v135 else v331 := e_psel h_v245 h_v135 h_v331 (of_decide_eq_true rfl)
  have h_v335 : R 1 0 4611686016279904258 4611686020574871550 v335 v335 := (r_sub hl (r_add hl h_v333 h_v333 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v335 : sv v335 = sv v333 + sv v333 := e_add h_v333 h_v333 (of_decide_eq_true rfl)
  have h_v338 : R 1 0 0 1 v338 v338 := (r_plt hl h_v6 h_v335 (of_decide_eq_true rfl))
  have e_v338 : (v338 = 1 ↔ sv v6 < sv v335) := e_plt h_v6 h_v335 (of_decide_eq_true rfl)
  have h_v339 : R 1 0 0 1 v339 v339 := (r_sub hl (r_O hl) h_v338 (of_decide_eq_true rfl))
  have e_v339 : (v339 = 1 ↔ ¬v338 = 1) := e_not h_v338 (of_decide_eq_true rfl)
  have h_v340 : R 1 0 0 1 v340 v340 := (r_land hl h_v13 h_v37 (of_decide_eq_true rfl))
  have e_v340 : (v340 = 1 ↔ v13 = 1 ∧ v37 = 1) := e_land h_v13 h_v37 (of_decide_eq_true rfl)
  have h_v341 : R 1 0 0 1 v341 v341 := (r_land hl h_v37 h_v340 (of_decide_eq_true rfl))
  have e_v341 : (v341 = 1 ↔ v37 = 1 ∧ v340 = 1) := e_land h_v37 h_v340 (of_decide_eq_true rfl)
  have h_v342 : R 1 0 0 1 v342 v342 := (r_land hl h_v79 h_v341 (of_decide_eq_true rfl))
  have e_v342 : (v342 = 1 ↔ v79 = 1 ∧ v341 = 1) := e_land h_v79 h_v341 (of_decide_eq_true rfl)
  have h_v343 : R 1 0 0 1 v343 v343 := (r_land hl h_v194 h_v342 (of_decide_eq_true rfl))
  have e_v343 : (v343 = 1 ↔ v194 = 1 ∧ v342 = 1) := e_land h_v194 h_v342 (of_decide_eq_true rfl)
  have h_v344 : R 1 0 0 1 v344 v344 := (r_land hl h_v194 h_v343 (of_decide_eq_true rfl))
  have e_v344 : (v344 = 1 ↔ v194 = 1 ∧ v343 = 1) := e_land h_v194 h_v343 (of_decide_eq_true rfl)
  have h_v345 : R 1 0 0 1 v345 v345 := (r_land hl h_v227 h_v344 (of_decide_eq_true rfl))
  have e_v345 : (v345 = 1 ↔ v227 = 1 ∧ v344 = 1) := e_land h_v227 h_v344 (of_decide_eq_true rfl)
  clear h_OFFr h_v6 h_v13 h_v37 h_v65 h_v79 h_v135 h_v194 h_v227 h_v245 h_v248 h_v293 h_v328 h_v329 h_v330 h_v331 h_v333 h_v335 h_v338 h_v340 h_v341 h_v342 h_v343 h_v344
  have h_v346 : R 1 0 0 1 v346 v346 := (r_land hl h_v339 h_v345 (of_decide_eq_true rfl))
  have e_v346 : (v346 = 1 ↔ v339 = 1 ∧ v345 = 1) := e_land h_v339 h_v345 (of_decide_eq_true rfl)
  have k_v346 : v346 = 1 := h
  have k_v339 : v339 = 1 := ((e_v346).1 k_v346).1
  have k_v345 : v345 = 1 := ((e_v346).1 k_v346).2
  have k_v227 : v227 = 1 := ((e_v345).1 k_v345).1
  have k_v344 : v344 = 1 := ((e_v345).1 k_v345).2
  have k_v194 : v194 = 1 := ((e_v344).1 k_v344).1
  have k_v343 : v343 = 1 := ((e_v344).1 k_v344).2
  have k_v342 : v342 = 1 := ((e_v343).1 k_v343).2
  have k_v79 : v79 = 1 := ((e_v342).1 k_v342).1
  have k_v341 : v341 = 1 := ((e_v342).1 k_v342).2
  have k_v37 : v37 = 1 := ((e_v341).1 k_v341).1
  have k_v340 : v340 = 1 := ((e_v341).1 k_v341).2
  have k_v13 : v13 = 1 := ((e_v340).1 k_v340).1
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
  let u38 : ℤ := L2.cosI (sv v33)
  let u39 : ℤ := (sv v15) + u38
  let u40 : ℕ := if u39 < (sv v17) then 1 else 0
  let u41 : ℤ := if u40 = 1 then (sv v17) else u39
  have f56 := L2.K3_cos_lo (sv v33) u38 u39 (sv v17) u41 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u42 : ℕ := if (sv v20) < (sv v33) then 1 else 0
  let u43 : ℤ := if u42 = 1 then (sv v17) else u41
  let u44 : ℤ := L2.cosI (sv v32)
  let u45 : ℤ := (sv v24) + u44
  let u46 : ℕ := if u45 < (sv v26) then 1 else 0
  let u47 : ℤ := if u46 = 1 then u45 else (sv v26)
  have f70 := L2.K3_cos_hi (sv v32) u44 u45 (sv v26) u47 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u48 : ℕ := if (sv v32) < (sv v29) then 1 else 0
  let u49 : ℤ := if u48 = 1 then (sv v26) else u47
  have f45 := L2.K10_icos True (sv v32) (sv v33) u41 (sv v17) u42 u43 u47 (sv v26) u48 u49 f46 f56 e_v17 (L2.p_clt (843314855) e_v20 (L2.p_ult _ _)) rfl f70 e_v26 (L2.p_ltc (1) e_v29 (L2.p_ult _ _)) rfl
  have f85 := L2.K8_in_range True (sv v32) (sv v33) v34 (sv v10) v36 v37 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v35 e_v36) e_v37 (L2.X1_top _ k_v37)
  have f84 := L2.K9_isin True (sv v32) (sv v33) (sv t32.1) (sv t33.1) (sv v53) (sv v54) (sv v55) (sv v56) (sv v26) (sv v58) v60 v62 v63 (sv v64) f85 (L2.p_sin e_t32_1) (L2.p_sin e_t33_1) (L2.p_min e_v52 (L2.p_sel e_v53)) (L2.p_addc (-4) (L2.p_add_comm e_v54) e_v15) (L2.p_max e_v52 (L2.p_sel e_v55)) (L2.p_addc (4) (L2.p_add_comm e_v56) e_v24) e_v26 (L2.p_min e_v57 (L2.p_sel e_v58)) (L2.p_ltc (421657430) e_v59 e_v60) (L2.p_clt (421657427) e_v61 e_v62) e_v63 (L2.p_sel e_v64)
  let u73 : ℕ := if v72 = 1 then 0 else 1
  let u75 : ℕ := if v74 = 1 then 0 else 1
  let u76 : ℕ := if v72 = 1 ∧ u75 = 1 then 1 else 0
  let u80 : ℕ := if v67 = 1 ∧ v77 = 1 then 1 else 0
  let u81 : ℕ := if u76 = 1 ∨ u80 = 1 then 1 else 0
  let u82 : ℤ := if u81 = 1 then (sv v31) else (sv v22)
  let u83 : ℕ := if v71 = 1 ∧ u73 = 1 then 1 else 0
  let u84 : ℕ := if v70 = 1 ∨ u83 = 1 then 1 else 0
  let u85 : ℤ := if u84 = 1 then (sv v64) else (sv v54)
  let u86 : ℕ := if v70 = 1 ∧ v77 = 1 then 1 else 0
  let u87 : ℕ := if u76 = 1 ∨ u86 = 1 then 1 else 0
  let u88 : ℤ := if u87 = 1 then (sv v22) else (sv v31)
  let u89 : ℕ := if v71 = 1 ∧ u76 = 1 then 1 else 0
  let u90 : ℕ := if v70 = 1 ∨ u89 = 1 then 1 else 0
  let u91 : ℤ := if u90 = 1 then (sv v54) else (sv v64)
  let u92 : ℤ := u82 * u85
  let u93 : ℤ := u92 / 2 ^ 28
  let u94 : ℤ := u88 * u91
  let u95 : ℤ := -((-u94) / 2 ^ 28)
  have f121 := L2.K6_imul True (sv v22) (sv v31) (sv v54) (sv v64) (sv v65) v66 v67 v68 v69 v70 v71 v72 u73 v74 u75 u76 v77 v78 v79 u80 u81 u82 u83 u84 u85 u86 u87 u88 u89 u90 u91 u93 u95 e_v65 e_v66 e_v67 e_v68 e_v69 (L2.p_and_comm e_v70) e_v71 e_v72 (L2.p_unot _) e_v74 (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) e_v77 e_v78 e_v79 (L2.X1_top _ k_v79) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl)
  let u96 : ℕ := if (sv v65) < u93 then 1 else 0
  let u97 : ℕ := if u96 = 1 then 0 else 1
  let u98 : ℕ := if u43 < (sv v65) then 1 else 0
  let u99 : ℤ := if u98 = 1 then u93 else u95
  let u100 : ℕ := if u49 < (sv v65) then 1 else 0
  let u101 : ℤ := if u100 = 1 then u95 else u93
  have f154 := L2.K11_qdiv u43 u49 u93 u95 u96 u97 (sv v65) u98 u99 u100 u101 (L2.p_clt (0) e_v65 (L2.p_ult _ _)) (L2.p_unot _) e_v65 (L2.p_ult _ _) rfl (L2.p_ult _ _) rfl
  let u102 : ℤ := (sv v65) - u43
  let u103 : ℤ := if u98 = 1 then u102 else u43
  let u104 : ℤ := 0
  let u105 : ℕ := if u98 = 1 then 0 else 1
  let u106 : ℤ := L2.cosI u104
  let u107 : ℤ := (sv v15) + u106
  let u108 : ℕ := if u107 < (sv v17) then 1 else 0
  let u109 : ℤ := if u108 = 1 then (sv v17) else u107
  have f172 := L2.K3_cos_lo u104 u106 u107 (sv v17) u109 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u110 : ℤ := (sv v24) + u106
  let u111 : ℕ := if u110 < (sv v26) then 1 else 0
  let u112 : ℤ := if u111 = 1 then u110 else (sv v26)
  have f181 := L2.K3_cos_hi u104 u106 u110 (sv v26) u112 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u113 : ℤ := L2.sinI u104
  let u114 : ℤ := (sv v24) + u113
  let u115 : ℕ := if u114 < (sv v26) then 1 else 0
  let u116 : ℤ := if u115 = 1 then u114 else (sv v26)
  have f190 := L2.K3_sin_hi u104 u113 u114 (sv v26) u116 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v24) e_v26 (L2.p_min (L2.p_ult _ _) rfl)
  let u117 : ℤ := (sv v15) + u113
  have f199 := L2.K3_sin_lo u104 u113 u117 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15)
  let u118 : ℤ := if u105 = 1 then u109 else u112
  let u119 : ℤ := if u105 = 1 then u116 else u117
  let u120 : ℤ := u99 * u119
  let u121 : ℤ := u103 * u118
  let u122 : ℕ := if u121 < u120 then 1 else 0
  let u123 : ℕ := if u122 = 1 then 0 else 1
  let u124 : ℕ := if u120 < u121 then 1 else 0
  let u125 : ℕ := if u124 = 1 then 0 else 1
  let u126 : ℕ := if (sv v65) < u104 then 1 else 0
  let u127 : ℕ := if u126 = 1 then 0 else 1
  let u129 : ℕ := if (sv v128) < u104 then 1 else 0
  let u130 : ℕ := if u129 = 1 then 0 else 1
  let u131 : ℕ := if (sv v8) < u109 then 1 else 0
  let u132 : ℕ := if u123 = 1 ∧ u131 = 1 then 1 else 0
  let u133 : ℕ := if u130 = 1 ∧ u132 = 1 then 1 else 0
  let u134 : ℕ := if u127 = 1 ∨ u133 = 1 then 1 else 0
  let u136 : ℕ := if u104 < (sv v135) then 1 else 0
  let u137 : ℕ := if u136 = 1 then 0 else 1
  let u138 : ℕ := if u125 = 1 ∨ u137 = 1 then 1 else 0
  let u139 : ℕ := if u105 = 1 ∧ u134 = 1 then 1 else 0
  let u140 : ℕ := if u98 = 1 ∧ u138 = 1 then 1 else 0
  let u141 : ℕ := if u139 = 1 ∨ u140 = 1 then 1 else 0
  let u142 : ℤ := (sv v65) - u104
  let u143 : ℤ := if u98 = 1 then u142 else u104
  let u144 : ℤ := -421657429
  let u145 : ℤ := if u141 = 1 then u143 else u144
  have f165 := L2.K12_atan_lo u43 u99 (sv v65) u98 u102 u103 u104 u105 u109 u112 u116 u117 u118 u119 u120 u121 u123 u125 u126 u127 (sv v128) u130 u131 u132 u133 u134 (sv v135) u137 u138 u139 u98 u140 u141 u142 u143 u144 u145 e_v65 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f172 f181 f190 f199 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v128 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v135 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
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
  let u187 : ℤ := if u97 = 1 then u144 else u145
  let u188 : ℤ := if u97 = 1 then (sv v135) else u186
  have f41 := L2.K19_iso_angle_pt True (sv v3) (sv v22) (sv v31) (sv v32) (sv v33) u43 u49 (sv v54) (sv v64) u93 u95 u99 u101 u97 u96 u145 u186 u144 (sv v135) u187 u188 f42 f45 f84 f121 f154 (L2.p_not_not (L2.p_unot _)) f165 f239 rfl e_v135 rfl rfl
  have f317 := L2.K5_ihalf (sv v2) (sv v2) (sv v189) (sv v190) e_v189 e_v190
  have f321 := L2.K8_in_range True (sv v189) (sv v190) v191 (sv v10) v193 v194 (L2.p_clt (-1) e_v8 e_v191) e_v10 (L2.p_le e_v192 e_v193) e_v194 (L2.X1_top _ k_v194)
  let u195 : ℤ := L2.cosI (sv v190)
  let u196 : ℤ := (sv v15) + u195
  let u197 : ℕ := if u196 < (sv v17) then 1 else 0
  let u198 : ℤ := if u197 = 1 then (sv v17) else u196
  have f331 := L2.K3_cos_lo (sv v190) u195 u196 (sv v17) u198 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v15) e_v17 (L2.p_max (L2.p_ult _ _) rfl)
  let u199 : ℕ := if (sv v20) < (sv v190) then 1 else 0
  let u200 : ℤ := if u199 = 1 then (sv v17) else u198
  have f345 := L2.K3_cos_hi (sv v189) (sv t189.2) (sv v202) (sv v26) (sv v204) (L2.p_cos e_t189_2) (L2.p_addc (4) (L2.p_add_comm e_v202) e_v24) e_v26 (L2.p_min e_v203 (L2.p_sel e_v204))
  have f320 := L2.K10_icos True (sv v189) (sv v190) u198 (sv v17) u199 u200 (sv v204) (sv v26) v205 (sv v206) f321 f331 e_v17 (L2.p_clt (843314855) e_v20 (L2.p_ult _ _)) rfl f345 e_v26 (L2.p_ltc (1) e_v29 e_v205) (L2.p_sel e_v206)
  have f360 := L2.K8_in_range True (sv v189) (sv v190) v191 (sv v10) v193 v194 (L2.p_clt (-1) e_v8 e_v191) e_v10 (L2.p_le e_v192 e_v193) e_v194 (L2.X1_top _ k_v194)
  have f359 := L2.K9_isin True (sv v189) (sv v190) (sv t189.1) (sv t190.1) (sv v210) (sv v211) (sv v212) (sv v213) (sv v26) (sv v215) v216 v217 v218 (sv v219) f360 (L2.p_sin e_t189_1) (L2.p_sin e_t190_1) (L2.p_min e_v209 (L2.p_sel e_v210)) (L2.p_addc (-4) (L2.p_add_comm e_v211) e_v15) (L2.p_max e_v209 (L2.p_sel e_v212)) (L2.p_addc (4) (L2.p_add_comm e_v213) e_v24) e_v26 (L2.p_min e_v214 (L2.p_sel e_v215)) (L2.p_ltc (421657430) e_v59 e_v216) (L2.p_clt (421657427) e_v61 e_v217) e_v218 (L2.p_sel e_v219)
  have f396 := L2.K6_imul True (sv v22) (sv v31) (sv v211) (sv v219) (sv v65) v66 v67 v68 v69 v70 v71 v220 v221 v222 v223 v224 v225 v226 v227 v228 v229 (sv v230) v231 v232 (sv v233) v234 v235 (sv v236) v237 v238 (sv v239) (sv v241) (sv v243) e_v65 e_v66 e_v67 e_v68 e_v69 (L2.p_and_comm e_v70) e_v71 e_v220 e_v221 e_v222 e_v223 (L2.p_and_comm e_v224) e_v225 e_v226 e_v227 (L2.X1_top _ k_v227) e_v228 e_v229 (L2.p_sel e_v230) e_v231 e_v232 (L2.p_sel e_v233) e_v234 e_v235 (L2.p_sel e_v236) e_v237 e_v238 (L2.p_sel e_v239) (L2.p_mul (L2.p_mul_comm e_v240) e_v241) (L2.p_mulc (L2.p_mul_comm e_v242) e_v243)
  let u246 : ℕ := if u200 < (sv v65) then 1 else 0
  let u247 : ℤ := if u246 = 1 then (sv v241) else (sv v243)
  have f429 := L2.K11_qdiv u200 (sv v206) (sv v241) (sv v243) v244 v245 (sv v65) u246 u247 v248 (sv v249) (L2.p_clt (0) e_v65 e_v244) e_v245 e_v65 (L2.p_ult _ _) rfl e_v248 (L2.p_sel e_v249)
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
  let u290 : ℤ := if u287 = 1 then u289 else u144
  have f440 := L2.K12_atan_lo u200 u247 (sv v65) u246 u250 u251 u252 u253 u257 u260 u264 u265 u266 u267 u268 u269 u271 u273 u274 u275 (sv v128) u277 u278 u279 u280 u281 (sv v135) u283 u284 u285 u246 u286 u287 u288 u289 u144 u290 e_v65 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f447 f456 f465 f474 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v128 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v135 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  have f520 := L2.K3_cos_lo (sv v293) (sv t293.2) (sv v295) (sv v17) (sv v297) (L2.p_cos e_t293_2) (L2.p_addc (-4) (L2.p_add_comm e_v295) e_v15) e_v17 (L2.p_max e_v296 (L2.p_sel e_v297))
  have f529 := L2.K3_cos_hi (sv v293) (sv t293.2) (sv v298) (sv v26) (sv v300) (L2.p_cos e_t293_2) (L2.p_addc (4) (L2.p_add_comm e_v298) e_v24) e_v26 (L2.p_min e_v299 (L2.p_sel e_v300))
  have f538 := L2.K3_sin_hi (sv v293) (sv t293.1) (sv v302) (sv v26) (sv v304) (L2.p_sin e_t293_1) (L2.p_addc (4) (L2.p_add_comm e_v302) e_v24) e_v26 (L2.p_min e_v303 (L2.p_sel e_v304))
  have f547 := L2.K3_sin_lo (sv v293) (sv t293.1) (sv v305) (L2.p_sin e_t293_1) (L2.p_addc (-4) (L2.p_add_comm e_v305) e_v15)
  have f514 := L2.K12_atan_hi (sv v206) (sv v249) (sv v65) v248 (sv v291) (sv v292) (sv v293) (sv v297) (sv v300) (sv v304) (sv v305) (sv v306) (sv v307) (sv v308) (sv v309) v311 v313 v314 v315 (sv v128) v317 v318 v319 v320 v321 (sv v135) v323 v324 v325 v326 v327 v328 (sv v329) (sv v330) (sv v135) (sv v331) e_v65 e_v248 e_v291 (L2.p_sel e_v292) (L2.p_hint e_v293) f520 f529 f538 f547 (L2.p_sel e_v306) (L2.p_sel e_v307) (L2.p_mul_comm e_v308) (L2.p_mul_comm e_v309) (L2.p_le e_v310 e_v311) (L2.p_le e_v312 e_v313) e_v314 e_v315 e_v128 (L2.p_le e_v316 e_v317) (L2.p_clt (-1) e_v8 e_v318) e_v319 (L2.p_and_comm e_v320) e_v321 e_v135 (L2.p_le e_v322 e_v323) (L2.p_or_comm e_v324) e_v325 e_v326 (L2.p_and_comm e_v327) e_v328 e_v329 (L2.p_sel e_v330) e_v135 (L2.p_sel e_v331)
  let u332 : ℤ := if v245 = 1 then u144 else u290
  have f316 := L2.K19_iso_angle_pt True (sv v2) (sv v22) (sv v31) (sv v189) (sv v190) u200 (sv v206) (sv v211) (sv v219) (sv v241) (sv v243) u247 (sv v249) v245 v244 u290 (sv v331) u144 (sv v135) u332 (sv v333) f317 f320 f359 f396 f429 (L2.p_not_not e_v245) f440 f514 rfl e_v135 rfl (L2.p_sel e_v333)
  have f1 := L2.K20_iso_angle True (sv v2) (sv v3) (sv v0) (sv v1) (sv v22) (sv v31) u187 u188 u97 u332 (sv v333) v245 f2 f41 f316
  let u334 : ℤ := u187 + u187
  have f591 := L2.K4_iadd u187 (sv v333) u187 (sv v333) u334 (sv v335) rfl e_v335
  let u336 : ℕ := if u334 < (sv v6) then 1 else 0
  let u337 : ℕ := if u336 = 1 then 0 else 1
  exact Tammes15.D3Trig.TR true F0 F1 F2 F3 hD (sv v0) (sv v1) (sv v2) (sv v3) (sv v6) (1 : ℕ) u187 (sv v333) u334 (sv v335) u337 v339 v339 e_v0 e_v1 e_v2 e_v3 e_v6 (of_decide_eq_true rfl) f1 f591 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le e_v338 e_v339) (L2.p_sel_t _ _) (L2.X1_top _ k_v339)

end Tammes15.D3Trig
