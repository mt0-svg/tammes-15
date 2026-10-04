import Tammes15.D3Trig.Prog.HFL
import Tammes15.D3Prog.Sem

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progHFL_seg0 (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (hb_H4 : H4 < 2 ^ 64) :
    let OFFr := Nat.mul 1 4611686018427387904
    let H61r := Nat.mul 1 2305843009213693952
    let v0 := ix 1 F0 0
    let v1 := ix 1 F0 32
    let v2 := ix 1 F1 0
    let v3 := ix 1 F1 32
    let v4 := ix 1 F2 0
    let v5 := ix 1 F2 32
    let v6 := ix 1 F3 0
    let v7 := ix 1 F3 32
    let v9 := Nat.mul 1 4611686019270702761
    let v10 := Nat.sub (Nat.add v7 v9) OFFr
    let v11 := Nat.mul 1 4611686020114017616
    let v12 := plt 1 v11 v10
    let v13 := Nat.sub 1 v12
    let v15 := Nat.mul 1 4611686019270702760
    let v19 := Nat.mul 1 4611686018427387903
    let v20 := plt 1 v19 v0
    let v21 := plt 1 v9 v1
    let v22 := Nat.sub 1 v21
    let v23 := Nat.land v20 v22
    let t0 := sc28u 1 v0
    let t1 := sc28u 1 v1
    let v26 := plt 1 t0.1 t1.1
    let v27 := psel (pmask v26) t0.1 t1.1
    let v28 := Nat.mul 1 4611686018427387900
    let v29 := Nat.sub (Nat.add v27 v28) OFFr
    let v30 := psel (pmask v26) t1.1 t0.1
    let v31 := Nat.mul 1 4611686018427387908
    let v32 := Nat.sub (Nat.add v30 v31) OFFr
    let v33 := Nat.mul 1 4611686018695823360
    let v34 := plt 1 v32 v33
    let v35 := psel (pmask v34) v32 v33
    let v36 := Nat.mul 1 4611686018849045334
    let v37 := plt 1 v0 v36
    let v38 := Nat.mul 1 4611686018849045331
    let v39 := plt 1 v38 v1
    let v40 := Nat.land v37 v39
    let v41 := psel (pmask v40) v33 v35
    let v42 := Nat.add (pshr1 1 v2) H61r
    let v43 := Nat.add (pshr1 1 (Nat.add v3 1)) H61r
    let v44 := plt 1 v19 v42
    let v45 := plt 1 v9 v43
    let v46 := Nat.sub 1 v45
    let v47 := Nat.land v44 v46
    let t42 := sc28u 1 v42
    let t43 := sc28u 1 v43
    let v50 := plt 1 t42.1 t43.1
    let v51 := psel (pmask v50) t42.1 t43.1
    let v52 := Nat.sub (Nat.add v28 v51) OFFr
    let v53 := psel (pmask v50) t43.1 t42.1
    let v54 := Nat.sub (Nat.add v31 v53) OFFr
    let v55 := plt 1 v54 v33
    let v56 := psel (pmask v55) v54 v33
    let v57 := plt 1 v42 v36
    let v58 := plt 1 v38 v43
    let v59 := Nat.land v57 v58
    let v60 := psel (pmask v59) v33 v56
    let v61 := Nat.mul 1 4611686018427387904
    let v62 := plt 1 v29 v61
    let v63 := Nat.sub 1 v62
    let v64 := plt 1 v61 v41
    let v65 := Nat.sub 1 v64
    let v66 := Nat.land v62 v65
    let v67 := Nat.land v62 v64
    let v68 := plt 1 v52 v61
    let v70 := plt 1 v61 v60
    let v71 := Nat.sub 1 v70
    let v72 := Nat.land v68 v71
    let v73 := Nat.land v68 v70
    let v74 := Nat.land v67 v73
    let v75 := Nat.land v63 v73
    let v76 := Nat.lor v72 v75
    let v77 := psel (pmask v76) v41 v29
    let v78 := Nat.sub 1 v72
    let v79 := Nat.land v67 v78
    let v80 := Nat.lor v66 v79
    let v81 := psel (pmask v80) v60 v52
    let v82 := Nat.land v66 v73
    let v83 := Nat.lor v72 v82
    let v84 := psel (pmask v83) v29 v41
    let v85 := Nat.land v67 v72
    let v86 := Nat.lor v66 v85
    let v87 := psel (pmask v86) v52 v60
    let v88 := smx 29 1 v81 v77
    let v89 := srdF 1 v88
    let v90 := smx 29 1 v87 v84
    let v91 := srdC 1 v90
    let v92 := smx 29 1 v52 v41
    let v93 := srdF 1 v92
    let v94 := smx 29 1 v52 v29
    let v95 := srdC 1 v94
    let v96 := plt 1 v89 v93
    let v97 := psel (pmask v96) v89 v93
    let v98 := plt 1 v91 v95
    let v99 := psel (pmask v98) v95 v91
    let v100 := psel (pmask v74) v97 v89
    let v101 := psel (pmask v74) v99 v91
    let v102 := plt 1 v19 v100
    let v104 := Nat.sub (Nat.add v28 t1.2) OFFr
    let v105 := Nat.mul 1 4611686018158952448
    let v106 := plt 1 v104 v105
    let v107 := psel (pmask v106) v105 v104
    let v108 := Nat.mul 1 4611686019270702759
    let v109 := plt 1 v108 v1
    let v110 := psel (pmask v109) v105 v107
    let v112 := Nat.sub (Nat.add v31 t0.2) OFFr
    let v113 := plt 1 v112 v33
    let v114 := psel (pmask v113) v112 v33
    let v115 := Nat.mul 1 4611686018427387905
    let v116 := plt 1 v0 v115
    let v117 := psel (pmask v116) v33 v114
    let v118 := Nat.add (pshr1 1 v3) H61r
    let v119 := plt 1 v19 v118
    let v120 := Nat.land v46 v119
    let v122 := Nat.sub (Nat.add v28 t43.2) OFFr
    let v123 := plt 1 v122 v105
    let v124 := psel (pmask v123) v105 v122
    let v125 := plt 1 v108 v43
    let v126 := psel (pmask v125) v105 v124
    let t118 := sc28u 1 v118
    let v134 := plt 1 t118.1 t43.1
    let v135 := psel (pmask v134) t118.1 t43.1
    let v136 := Nat.sub (Nat.add v28 v135) OFFr
    let v137 := psel (pmask v134) t43.1 t118.1
    let v138 := Nat.sub (Nat.add v31 v137) OFFr
    let v139 := plt 1 v138 v33
    let v140 := psel (pmask v139) v138 v33
    let v141 := plt 1 v118 v36
    let v142 := Nat.land v58 v141
    let v143 := psel (pmask v142) v33 v140
    let v144 := plt 1 v110 v61
    let v145 := Nat.sub 1 v144
    let v146 := plt 1 v61 v117
    let v147 := Nat.sub 1 v146
    let v148 := Nat.land v144 v147
    let v149 := Nat.land v144 v146
    let v150 := plt 1 v136 v61
    let v152 := plt 1 v61 v143
    let v153 := Nat.sub 1 v152
    let v154 := Nat.land v150 v153
    let v155 := Nat.land v150 v152
    let v156 := Nat.land v149 v155
    let v157 := Nat.land v145 v155
    let v158 := Nat.lor v154 v157
    let v159 := psel (pmask v158) v117 v110
    let v160 := Nat.sub 1 v154
    let v161 := Nat.land v149 v160
    let v162 := Nat.lor v148 v161
    let v163 := psel (pmask v162) v143 v136
    let v164 := Nat.land v148 v155
    let v165 := Nat.lor v154 v164
    let v166 := psel (pmask v165) v110 v117
    let v167 := Nat.land v149 v154
    let v168 := Nat.lor v148 v167
    let v169 := psel (pmask v168) v136 v143
    let v170 := smx 29 1 v163 v159
    let v171 := srdF 1 v170
    let v172 := smx 29 1 v169 v166
    let v173 := srdC 1 v172
    let v174 := smx 29 1 v136 v117
    let v175 := srdF 1 v174
    let v176 := smx 29 1 v136 v110
    let v177 := srdC 1 v176
    let v178 := plt 1 v171 v175
    let v179 := psel (pmask v178) v171 v175
    let v180 := plt 1 v173 v177
    let v181 := psel (pmask v180) v177 v173
    let v182 := psel (pmask v156) v179 v171
    let v183 := psel (pmask v156) v181 v173
    let v184 := plt 1 v61 v182
    let v185 := Nat.sub 1 v184
    let v186 := plt 1 v126 v61
    let v187 := psel (pmask v186) v182 v183
    let v190 := Nat.sub (Nat.add v61 OFFr) v126
    let v191 := psel (pmask v186) v190 v126
    let v192 := hxa 1 H0 0
    let v193 := Nat.sub 1 v186
    let t192 := sc28u 1 v192
    let v195 := Nat.sub (Nat.add v28 t192.2) OFFr
    let v196 := plt 1 v195 v105
    let v197 := psel (pmask v196) v105 v195
    let v198 := Nat.sub (Nat.add v31 t192.2) OFFr
    let v199 := plt 1 v198 v33
    let v200 := psel (pmask v199) v198 v33
    let v202 := Nat.sub (Nat.add v31 t192.1) OFFr
    let v203 := plt 1 v202 v33
    let v204 := psel (pmask v203) v202 v33
    let v205 := Nat.sub (Nat.add v28 t192.1) OFFr
    let v206 := psel (pmask v193) v197 v200
    let v207 := psel (pmask v193) v204 v205
    let v208 := smx 29 1 v187 v207
    let v209 := smx 29 1 v206 v191
    let v210 := plt 1 v209 v208
    let v211 := Nat.sub 1 v210
    let v212 := plt 1 v208 v209
    let v213 := Nat.sub 1 v212
    let v214 := plt 1 v61 v192
    let v215 := Nat.sub 1 v214
    let v216 := Nat.mul 1 4611686018849045332
    let v217 := plt 1 v216 v192
    let v218 := Nat.sub 1 v217
    let v219 := plt 1 v19 v197
    let v220 := Nat.land v211 v219
    let v221 := Nat.land v218 v220
    let v222 := Nat.lor v215 v221
    let v223 := Nat.mul 1 4611686018849045333
    let v224 := plt 1 v192 v223
    let v225 := Nat.sub 1 v224
    let v226 := Nat.lor v213 v225
    let v227 := Nat.land v193 v222
    let v228 := Nat.land v186 v226
    let v229 := Nat.lor v227 v228
    let v230 := Nat.sub (Nat.add v61 OFFr) v192
    let v231 := psel (pmask v186) v230 v192
    let v232 := Nat.mul 1 4611686018005730475
    let v233 := psel (pmask v229) v231 v232
    let v275 := psel (pmask v185) v232 v233
    let v277 := Nat.add (pshr1 1 (Nat.add v2 1)) H61r
    let v278 := plt 1 v9 v277
    let v279 := Nat.sub 1 v278
    let v280 := Nat.land v44 v279
    let v288 := Nat.sub (Nat.add v31 t42.2) OFFr
    let v289 := plt 1 v288 v33
    let v290 := psel (pmask v289) v288 v33
    let v291 := plt 1 v42 v115
    let v292 := psel (pmask v291) v33 v290
    let t277 := sc28u 1 v277
    let v294 := plt 1 t42.1 t277.1
    let v295 := psel (pmask v294) t42.1 t277.1
    let v296 := Nat.sub (Nat.add v28 v295) OFFr
    let v297 := psel (pmask v294) t277.1 t42.1
    let v298 := Nat.sub (Nat.add v31 v297) OFFr
    let v299 := plt 1 v298 v33
    let v300 := psel (pmask v299) v298 v33
    let v301 := plt 1 v38 v277
    let v302 := Nat.land v57 v301
    let v303 := psel (pmask v302) v33 v300
    let v304 := plt 1 v296 v61
    let v306 := plt 1 v61 v303
    let v307 := Nat.sub 1 v306
    let v308 := Nat.land v304 v307
    let v309 := Nat.land v304 v306
    let v310 := Nat.land v149 v309
    let v311 := Nat.land v145 v309
    let v312 := Nat.lor v308 v311
    let v313 := psel (pmask v312) v117 v110
    let v314 := Nat.sub 1 v308
    let v315 := Nat.land v149 v314
    let v316 := Nat.lor v148 v315
    let v317 := psel (pmask v316) v303 v296
    let v318 := Nat.land v148 v309
    let v319 := Nat.lor v308 v318
    let v320 := psel (pmask v319) v110 v117
    let v321 := Nat.land v149 v308
    let v322 := Nat.lor v148 v321
    let v323 := psel (pmask v322) v296 v303
    let v324 := smx 29 1 v317 v313
    let v325 := srdF 1 v324
    let v326 := smx 29 1 v323 v320
    let v327 := srdC 1 v326
    let v328 := smx 29 1 v296 v117
    let v329 := srdF 1 v328
    let v330 := smx 29 1 v296 v110
    let v331 := srdC 1 v330
    let v332 := plt 1 v325 v329
    let v333 := psel (pmask v332) v325 v329
    let v334 := plt 1 v327 v331
    let v335 := psel (pmask v334) v331 v327
    let v336 := psel (pmask v310) v333 v325
    let v337 := psel (pmask v310) v335 v327
    let v338 := plt 1 v61 v336
    let v339 := Nat.sub 1 v338
    let v342 := plt 1 v292 v61
    let v343 := psel (pmask v342) v337 v336
    let v385 := Nat.sub (Nat.add v61 OFFr) v292
    let v386 := psel (pmask v342) v385 v292
    let v387 := hxa 1 H0 32
    let t387 := sc28u 1 v387
    let v389 := Nat.sub (Nat.add v28 t387.2) OFFr
    let v390 := plt 1 v389 v105
    let v391 := psel (pmask v390) v105 v389
    let v392 := Nat.sub (Nat.add v31 t387.2) OFFr
    let v393 := plt 1 v392 v33
    let v394 := psel (pmask v393) v392 v33
    let v396 := Nat.sub (Nat.add v31 t387.1) OFFr
    let v397 := plt 1 v396 v33
    let v398 := psel (pmask v397) v396 v33
    let v399 := Nat.sub (Nat.add v28 t387.1) OFFr
    let v400 := psel (pmask v342) v391 v394
    let v401 := psel (pmask v342) v398 v399
    let v402 := smx 29 1 v343 v401
    let v403 := smx 29 1 v400 v386
    let v404 := plt 1 v403 v402
    let v405 := Nat.sub 1 v404
    let v406 := plt 1 v402 v403
    let v407 := Nat.sub 1 v406
    let v408 := plt 1 v61 v387
    let v409 := Nat.sub 1 v408
    let v410 := plt 1 v216 v387
    let v411 := Nat.sub 1 v410
    let v412 := plt 1 v19 v391
    let v413 := Nat.land v405 v412
    let v414 := Nat.land v411 v413
    let v415 := Nat.lor v409 v414
    let v416 := plt 1 v387 v223
    let v417 := Nat.sub 1 v416
    let v418 := Nat.lor v407 v417
    let v419 := Nat.land v342 v415
    let v420 := Nat.sub 1 v342
    let v421 := Nat.land v418 v420
    let v422 := Nat.lor v419 v421
    let v423 := Nat.sub (Nat.add v61 OFFr) v387
    let v424 := psel (pmask v342) v423 v387
    let v425 := psel (pmask v422) v424 v223
    let v427 := psel (pmask v339) v223 v425
    let v428 := Nat.add (pshr1 1 v4) H61r
    let v429 := Nat.add (pshr1 1 (Nat.add v5 1)) H61r
    let v430 := plt 1 v19 v428
    let v431 := plt 1 v9 v429
    let v432 := Nat.sub 1 v431
    let v433 := Nat.land v430 v432
    let t428 := sc28u 1 v428
    let t429 := sc28u 1 v429
    let v436 := plt 1 t428.1 t429.1
    let v437 := psel (pmask v436) t428.1 t429.1
    let v438 := Nat.sub (Nat.add v28 v437) OFFr
    let v439 := psel (pmask v436) t429.1 t428.1
    let v440 := Nat.sub (Nat.add v31 v439) OFFr
    let v441 := plt 1 v440 v33
    let v442 := psel (pmask v441) v440 v33
    let v443 := plt 1 v428 v36
    let v444 := plt 1 v38 v429
    let v445 := Nat.land v443 v444
    let v446 := psel (pmask v445) v33 v442
    let v447 := plt 1 v438 v61
    let v449 := plt 1 v61 v446
    let v450 := Nat.sub 1 v449
    let v451 := Nat.land v447 v450
    let v452 := Nat.land v447 v449
    let v453 := Nat.land v67 v452
    let v454 := Nat.land v63 v452
    let v455 := Nat.lor v451 v454
    let v456 := psel (pmask v455) v41 v29
    let v457 := Nat.sub 1 v451
    let v458 := Nat.land v67 v457
    let v459 := Nat.lor v66 v458
    let v460 := psel (pmask v459) v446 v438
    let v461 := Nat.land v66 v452
    let v462 := Nat.lor v451 v461
    let v463 := psel (pmask v462) v29 v41
    let v464 := Nat.land v67 v451
    let v465 := Nat.lor v66 v464
    let v466 := psel (pmask v465) v438 v446
    let v467 := smx 29 1 v460 v456
    let v468 := srdF 1 v467
    let v469 := smx 29 1 v466 v463
    let v470 := srdC 1 v469
    let v471 := smx 29 1 v438 v41
    let v472 := srdF 1 v471
    let v473 := smx 29 1 v438 v29
    let v474 := srdC 1 v473
    let v475 := plt 1 v468 v472
    let v476 := psel (pmask v475) v468 v472
    let v477 := plt 1 v470 v474
    let v478 := psel (pmask v477) v474 v470
    let v479 := psel (pmask v453) v476 v468
    let v480 := psel (pmask v453) v478 v470
    let v481 := plt 1 v19 v479
    let v482 := Nat.add (pshr1 1 v5) H61r
    let v483 := plt 1 v19 v482
    let v484 := Nat.land v432 v483
    let v486 := Nat.sub (Nat.add v28 t429.2) OFFr
    let v487 := plt 1 v486 v105
    let v488 := psel (pmask v487) v105 v486
    let v489 := plt 1 v108 v429
    let v490 := psel (pmask v489) v105 v488
    let t482 := sc28u 1 v482
    let v498 := plt 1 t482.1 t429.1
    let v499 := psel (pmask v498) t482.1 t429.1
    let v500 := Nat.sub (Nat.add v28 v499) OFFr
    let v501 := psel (pmask v498) t429.1 t482.1
    let v502 := Nat.sub (Nat.add v31 v501) OFFr
    let v503 := plt 1 v502 v33
    let v504 := psel (pmask v503) v502 v33
    let v505 := plt 1 v482 v36
    let v506 := Nat.land v444 v505
    let v507 := psel (pmask v506) v33 v504
    let v508 := plt 1 v500 v61
    let v510 := plt 1 v61 v507
    let v511 := Nat.sub 1 v510
    let v512 := Nat.land v508 v511
    let v513 := Nat.land v508 v510
    let v514 := Nat.land v149 v513
    let v515 := Nat.land v145 v513
    let v516 := Nat.lor v512 v515
    let v517 := psel (pmask v516) v117 v110
    let v518 := Nat.sub 1 v512
    let v519 := Nat.land v149 v518
    let v520 := Nat.lor v148 v519
    let v521 := psel (pmask v520) v507 v500
    let v522 := Nat.land v148 v513
    let v523 := Nat.lor v512 v522
    let v524 := psel (pmask v523) v110 v117
    let v525 := Nat.land v149 v512
    let v526 := Nat.lor v148 v525
    let v527 := psel (pmask v526) v500 v507
    let v528 := smx 29 1 v521 v517
    let v529 := srdF 1 v528
    let v530 := smx 29 1 v527 v524
    let v531 := srdC 1 v530
    let v532 := smx 29 1 v500 v117
    let v533 := srdF 1 v532
    let v534 := smx 29 1 v500 v110
    let v535 := srdC 1 v534
    let v536 := plt 1 v529 v533
    let v537 := psel (pmask v536) v529 v533
    let v538 := plt 1 v531 v535
    let v539 := psel (pmask v538) v535 v531
    let v540 := psel (pmask v514) v537 v529
    let v541 := psel (pmask v514) v539 v531
    let v542 := plt 1 v61 v540
    let v543 := Nat.sub 1 v542
    let v544 := plt 1 v490 v61
    let v545 := psel (pmask v544) v540 v541
    let v548 := Nat.sub (Nat.add v61 OFFr) v490
    let v549 := psel (pmask v544) v548 v490
    let v550 := hxa 1 H1 0
    let v551 := Nat.sub 1 v544
    let t550 := sc28u 1 v550
    let v553 := Nat.sub (Nat.add v28 t550.2) OFFr
    let v554 := plt 1 v553 v105
    let v555 := psel (pmask v554) v105 v553
    let v556 := Nat.sub (Nat.add v31 t550.2) OFFr
    let v557 := plt 1 v556 v33
    let v558 := psel (pmask v557) v556 v33
    let v560 := Nat.sub (Nat.add v31 t550.1) OFFr
    let v561 := plt 1 v560 v33
    let v562 := psel (pmask v561) v560 v33
    let v563 := Nat.sub (Nat.add v28 t550.1) OFFr
    let v564 := psel (pmask v551) v555 v558
    let v565 := psel (pmask v551) v562 v563
    let v566 := smx 29 1 v545 v565
    let v567 := smx 29 1 v564 v549
    let v568 := plt 1 v567 v566
    let v569 := Nat.sub 1 v568
    let v570 := plt 1 v566 v567
    let v571 := Nat.sub 1 v570
    let v572 := plt 1 v61 v550
    let v573 := Nat.sub 1 v572
    let v574 := plt 1 v216 v550
    let v575 := Nat.sub 1 v574
    let v576 := plt 1 v19 v555
    let v577 := Nat.land v569 v576
    let v578 := Nat.land v575 v577
    let v579 := Nat.lor v573 v578
    let v580 := plt 1 v550 v223
    let v581 := Nat.sub 1 v580
    let v582 := Nat.lor v571 v581
    let v583 := Nat.land v551 v579
    let v584 := Nat.land v544 v582
    let v585 := Nat.lor v583 v584
    let v586 := Nat.sub (Nat.add v61 OFFr) v550
    let v587 := psel (pmask v544) v586 v550
    let v588 := psel (pmask v585) v587 v232
    let v630 := psel (pmask v543) v232 v588
    let v632 := Nat.add (pshr1 1 (Nat.add v4 1)) H61r
    let v633 := plt 1 v9 v632
    let v634 := Nat.sub 1 v633
    let v635 := Nat.land v430 v634
    let v643 := Nat.sub (Nat.add v31 t428.2) OFFr
    let v644 := plt 1 v643 v33
    let v645 := psel (pmask v644) v643 v33
    let v646 := plt 1 v428 v115
    let v647 := psel (pmask v646) v33 v645
    let t632 := sc28u 1 v632
    let v649 := plt 1 t428.1 t632.1
    let v650 := psel (pmask v649) t428.1 t632.1
    let v651 := Nat.sub (Nat.add v28 v650) OFFr
    let v652 := psel (pmask v649) t632.1 t428.1
    let v653 := Nat.sub (Nat.add v31 v652) OFFr
    let v654 := plt 1 v653 v33
    let v655 := psel (pmask v654) v653 v33
    let v656 := plt 1 v38 v632
    let v657 := Nat.land v443 v656
    let v658 := psel (pmask v657) v33 v655
    let v659 := plt 1 v651 v61
    let v661 := plt 1 v61 v658
    let v662 := Nat.sub 1 v661
    let v663 := Nat.land v659 v662
    let v664 := Nat.land v659 v661
    let v665 := Nat.land v149 v664
    let v666 := Nat.land v145 v664
    let v667 := Nat.lor v663 v666
    let v668 := psel (pmask v667) v117 v110
    let v669 := Nat.sub 1 v663
    let v670 := Nat.land v149 v669
    let v671 := Nat.lor v148 v670
    let v672 := psel (pmask v671) v658 v651
    let v673 := Nat.land v148 v664
    ∀ (P : Prop), ((sv v0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v2 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v3 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v4 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v5 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v6 = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v7 = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v9 = (843314857)) → (sv v10 = sv v7 + sv v9) → (sv v11 = (1686629712)) → ((v12 = 1 ↔ sv v11 < sv v10)) → (R 1 0 0 1 v13 v13) → ((v13 = 1 ↔ ¬v12 = 1)) → (sv v15 = (843314856)) → (sv v19 = (-1)) → ((v20 = 1 ↔ sv v19 < sv v0)) → ((v21 = 1 ↔ sv v9 < sv v1)) → ((v22 = 1 ↔ ¬v21 = 1)) → (R 1 0 0 1 v23 v23) → ((v23 = 1 ↔ v20 = 1 ∧ v22 = 1)) → (sv t0.1 = (sc28pS (scArg v0)).1) → (sv t0.2 = (sc28pS (scArg v0)).2) → (sv t1.1 = (sc28pS (scArg v1)).1) → (sv t1.2 = (sc28pS (scArg v1)).2) → ((v26 = 1 ↔ sv t0.1 < sv t1.1)) → (v27 = if v26 = 1 then t0.1 else t1.1) → (sv v28 = (-4)) → (R 1 0 4611686018427387900 4611686018695823359 v29 v29) → (sv v29 = sv v27 + sv v28) → (v30 = if v26 = 1 then t1.1 else t0.1) → (sv v31 = (4)) → (sv v32 = sv v30 + sv v31) → (sv v33 = (268435456)) → ((v34 = 1 ↔ sv v32 < sv v33)) → (v35 = if v34 = 1 then v32 else v33) → (sv v36 = (421657430)) → ((v37 = 1 ↔ sv v0 < sv v36)) → (sv v38 = (421657427)) → ((v39 = 1 ↔ sv v38 < sv v1)) → ((v40 = 1 ↔ v37 = 1 ∧ v39 = 1)) → (R 1 0 4611686018427387908 4611686018695823367 v41 v41) → (v41 = if v40 = 1 then v33 else v35) → (R 1 0 4611686018427387904 4611686052787126264 v42 v42) → (sv v42 = sv v2 / 2) → (R 1 0 4611686018427387904 4611686052787126264 v43 v43) → (sv v43 = (sv v3 + 1) / 2) → ((v44 = 1 ↔ sv v19 < sv v42)) → ((v45 = 1 ↔ sv v9 < sv v43)) → (R 1 0 0 1 v46 v46) → ((v46 = 1 ↔ ¬v45 = 1)) → (R 1 0 0 1 v47 v47) → ((v47 = 1 ↔ v44 = 1 ∧ v46 = 1)) → (R 1 0 4611686018427387904 4611686018695823363 t42.1 t42.1) → (sv t42.1 = (sc28pS (scArg v42)).1) → (sv t42.2 = (sc28pS (scArg v42)).2) → (R 1 0 4611686018427387904 4611686018695823363 t43.1 t43.1) → (sv t43.1 = (sc28pS (scArg v43)).1) → (sv t43.2 = (sc28pS (scArg v43)).2) → ((v50 = 1 ↔ sv t42.1 < sv t43.1)) → (v51 = if v50 = 1 then t42.1 else t43.1) → (R 1 0 4611686018427387900 4611686018695823359 v52 v52) → (sv v52 = sv v28 + sv v51) → (v53 = if v50 = 1 then t43.1 else t42.1) → (sv v54 = sv v31 + sv v53) → ((v55 = 1 ↔ sv v54 < sv v33)) → (v56 = if v55 = 1 then v54 else v33) → ((v57 = 1 ↔ sv v42 < sv v36)) → (R 1 0 0 1 v58 v58) → ((v58 = 1 ↔ sv v38 < sv v43)) → ((v59 = 1 ↔ v57 = 1 ∧ v58 = 1)) → (R 1 0 4611686018427387908 4611686018695823367 v60 v60) → (v60 = if v59 = 1 then v33 else v56) → (sv v61 = (0)) → ((v62 = 1 ↔ sv v29 < sv v61)) → (R 1 0 0 1 v63 v63) → ((v63 = 1 ↔ ¬v62 = 1)) → ((v64 = 1 ↔ sv v61 < sv v41)) → ((v65 = 1 ↔ ¬v64 = 1)) → (R 1 0 0 1 v66 v66) → ((v66 = 1 ↔ v62 = 1 ∧ v65 = 1)) → (R 1 0 0 1 v67 v67) → ((v67 = 1 ↔ v62 = 1 ∧ v64 = 1)) → ((v68 = 1 ↔ sv v52 < sv v61)) → ((v70 = 1 ↔ sv v61 < sv v60)) → ((v71 = 1 ↔ ¬v70 = 1)) → (R 1 0 0 1 v72 v72) → ((v72 = 1 ↔ v68 = 1 ∧ v71 = 1)) → (R 1 0 0 1 v73 v73) → ((v73 = 1 ↔ v68 = 1 ∧ v70 = 1)) → ((v74 = 1 ↔ v67 = 1 ∧ v73 = 1)) → ((v75 = 1 ↔ v63 = 1 ∧ v73 = 1)) → ((v76 = 1 ↔ v72 = 1 ∨ v75 = 1)) → (v77 = if v76 = 1 then v41 else v29) → (R 1 0 0 1 v78 v78) → ((v78 = 1 ↔ ¬v72 = 1)) → ((v79 = 1 ↔ v67 = 1 ∧ v78 = 1)) → ((v80 = 1 ↔ v66 = 1 ∨ v79 = 1)) → (v81 = if v80 = 1 then v60 else v52) → ((v82 = 1 ↔ v66 = 1 ∧ v73 = 1)) → ((v83 = 1 ↔ v72 = 1 ∨ v82 = 1)) → (v84 = if v83 = 1 then v29 else v41) → ((v85 = 1 ↔ v67 = 1 ∧ v72 = 1)) → ((v86 = 1 ↔ v66 = 1 ∨ v85 = 1)) → (v87 = if v86 = 1 then v52 else v60) → (sv v88 = sv v81 * sv v77) → (sv v89 = sv v88 / 2 ^ 28) → (sv v90 = sv v87 * sv v84) → (sv v91 = -((-sv v90) / 2 ^ 28)) → (sv v92 = sv v52 * sv v41) → (sv v93 = sv v92 / 2 ^ 28) → (sv v94 = sv v52 * sv v29) → (sv v95 = -((-sv v94) / 2 ^ 28)) → ((v96 = 1 ↔ sv v89 < sv v93)) → (v97 = if v96 = 1 then v89 else v93) → ((v98 = 1 ↔ sv v91 < sv v95)) → (v99 = if v98 = 1 then v95 else v91) → (R 1 0 4611686018427387899 4611686018695823374 v100 v100) → (v100 = if v74 = 1 then v97 else v89) → (R 1 0 4611686018427387900 4611686018695823375 v101 v101) → (v101 = if v74 = 1 then v99 else v91) → (R 1 0 0 1 v102 v102) → ((v102 = 1 ↔ sv v19 < sv v100)) → (sv v104 = sv v28 + sv t1.2) → (sv v105 = (-268435456)) → ((v106 = 1 ↔ sv v104 < sv v105)) → (v107 = if v106 = 1 then v105 else v104) → (sv v108 = (843314855)) → ((v109 = 1 ↔ sv v108 < sv v1)) → (R 1 0 4611686018158952441 4611686018695823359 v110 v110) → (v110 = if v109 = 1 then v105 else v107) → (sv v112 = sv v31 + sv t0.2) → ((v113 = 1 ↔ sv v112 < sv v33)) → (v114 = if v113 = 1 then v112 else v33) → (sv v115 = (1)) → ((v116 = 1 ↔ sv v0 < sv v115)) → (R 1 0 4611686018158952449 4611686018695823367 v117 v117) → (v117 = if v116 = 1 then v33 else v114) → (R 1 0 4611686018427387904 4611686052787126264 v118 v118) → (sv v118 = sv v3 / 2) → ((v119 = 1 ↔ sv v19 < sv v118)) → (R 1 0 0 1 v120 v120) → ((v120 = 1 ↔ v46 = 1 ∧ v119 = 1)) → (sv v122 = sv v28 + sv t43.2) → ((v123 = 1 ↔ sv v122 < sv v105)) → (v124 = if v123 = 1 then v105 else v122) → ((v125 = 1 ↔ sv v108 < sv v43)) → (R 1 0 4611686018158952441 4611686018695823359 v126 v126) → (v126 = if v125 = 1 then v105 else v124) → (R 1 0 4611686018427387904 4611686018695823363 t118.1 t118.1) → (sv t118.1 = (sc28pS (scArg v118)).1) → ((v134 = 1 ↔ sv t118.1 < sv t43.1)) → (v135 = if v134 = 1 then t118.1 else t43.1) → (sv v136 = sv v28 + sv v135) → (v137 = if v134 = 1 then t43.1 else t118.1) → (sv v138 = sv v31 + sv v137) → ((v139 = 1 ↔ sv v138 < sv v33)) → (v140 = if v139 = 1 then v138 else v33) → ((v141 = 1 ↔ sv v118 < sv v36)) → ((v142 = 1 ↔ v58 = 1 ∧ v141 = 1)) → (v143 = if v142 = 1 then v33 else v140) → ((v144 = 1 ↔ sv v110 < sv v61)) → (R 1 0 0 1 v145 v145) → ((v145 = 1 ↔ ¬v144 = 1)) → ((v146 = 1 ↔ sv v61 < sv v117)) → ((v147 = 1 ↔ ¬v146 = 1)) → (R 1 0 0 1 v148 v148) → ((v148 = 1 ↔ v144 = 1 ∧ v147 = 1)) → (R 1 0 0 1 v149 v149) → ((v149 = 1 ↔ v144 = 1 ∧ v146 = 1)) → ((v150 = 1 ↔ sv v136 < sv v61)) → ((v152 = 1 ↔ sv v61 < sv v143)) → ((v153 = 1 ↔ ¬v152 = 1)) → ((v154 = 1 ↔ v150 = 1 ∧ v153 = 1)) → ((v155 = 1 ↔ v150 = 1 ∧ v152 = 1)) → ((v156 = 1 ↔ v149 = 1 ∧ v155 = 1)) → ((v157 = 1 ↔ v145 = 1 ∧ v155 = 1)) → ((v158 = 1 ↔ v154 = 1 ∨ v157 = 1)) → (v159 = if v158 = 1 then v117 else v110) → ((v160 = 1 ↔ ¬v154 = 1)) → ((v161 = 1 ↔ v149 = 1 ∧ v160 = 1)) → ((v162 = 1 ↔ v148 = 1 ∨ v161 = 1)) → (v163 = if v162 = 1 then v143 else v136) → ((v164 = 1 ↔ v148 = 1 ∧ v155 = 1)) → ((v165 = 1 ↔ v154 = 1 ∨ v164 = 1)) → (v166 = if v165 = 1 then v110 else v117) → ((v167 = 1 ↔ v149 = 1 ∧ v154 = 1)) → ((v168 = 1 ↔ v148 = 1 ∨ v167 = 1)) → (v169 = if v168 = 1 then v136 else v143) → (sv v170 = sv v163 * sv v159) → (sv v171 = sv v170 / 2 ^ 28) → (sv v172 = sv v169 * sv v166) → (sv v173 = -((-sv v172) / 2 ^ 28)) → (sv v174 = sv v136 * sv v117) → (sv v175 = sv v174 / 2 ^ 28) → (sv v176 = sv v136 * sv v110) → (sv v177 = -((-sv v176) / 2 ^ 28)) → ((v178 = 1 ↔ sv v171 < sv v175)) → (v179 = if v178 = 1 then v171 else v175) → ((v180 = 1 ↔ sv v173 < sv v177)) → (v181 = if v180 = 1 then v177 else v173) → (v182 = if v156 = 1 then v179 else v171) → (v183 = if v156 = 1 then v181 else v173) → ((v184 = 1 ↔ sv v61 < sv v182)) → ((v185 = 1 ↔ ¬v184 = 1)) → (R 1 0 0 1 v186 v186) → ((v186 = 1 ↔ sv v126 < sv v61)) → (v187 = if v186 = 1 then v182 else v183) → (sv v190 = sv v61 - sv v126) → (v191 = if v186 = 1 then v190 else v126) → (sv v192 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ)) → ((v193 = 1 ↔ ¬v186 = 1)) → (sv t192.1 = (sc28pS (scArg v192)).1) → (sv t192.2 = (sc28pS (scArg v192)).2) → (sv v195 = sv v28 + sv t192.2) → ((v196 = 1 ↔ sv v195 < sv v105)) → (v197 = if v196 = 1 then v105 else v195) → (sv v198 = sv v31 + sv t192.2) → ((v199 = 1 ↔ sv v198 < sv v33)) → (v200 = if v199 = 1 then v198 else v33) → (sv v202 = sv v31 + sv t192.1) → ((v203 = 1 ↔ sv v202 < sv v33)) → (v204 = if v203 = 1 then v202 else v33) → (sv v205 = sv v28 + sv t192.1) → (v206 = if v193 = 1 then v197 else v200) → (v207 = if v193 = 1 then v204 else v205) → (sv v208 = sv v187 * sv v207) → (sv v209 = sv v206 * sv v191) → ((v210 = 1 ↔ sv v209 < sv v208)) → ((v211 = 1 ↔ ¬v210 = 1)) → ((v212 = 1 ↔ sv v208 < sv v209)) → ((v213 = 1 ↔ ¬v212 = 1)) → ((v214 = 1 ↔ sv v61 < sv v192)) → ((v215 = 1 ↔ ¬v214 = 1)) → (sv v216 = (421657428)) → ((v217 = 1 ↔ sv v216 < sv v192)) → ((v218 = 1 ↔ ¬v217 = 1)) → ((v219 = 1 ↔ sv v19 < sv v197)) → ((v220 = 1 ↔ v211 = 1 ∧ v219 = 1)) → ((v221 = 1 ↔ v218 = 1 ∧ v220 = 1)) → ((v222 = 1 ↔ v215 = 1 ∨ v221 = 1)) → (sv v223 = (421657429)) → ((v224 = 1 ↔ sv v192 < sv v223)) → ((v225 = 1 ↔ ¬v224 = 1)) → ((v226 = 1 ↔ v213 = 1 ∨ v225 = 1)) → ((v227 = 1 ↔ v193 = 1 ∧ v222 = 1)) → ((v228 = 1 ↔ v186 = 1 ∧ v226 = 1)) → ((v229 = 1 ↔ v227 = 1 ∨ v228 = 1)) → (sv v230 = sv v61 - sv v192) → (v231 = if v186 = 1 then v230 else v192) → (sv v232 = (-421657429)) → (v233 = if v229 = 1 then v231 else v232) → (R 1 0 4611686017353646081 4611686019501129727 v275 v275) → (v275 = if v185 = 1 then v232 else v233) → (R 1 0 4611686018427387904 4611686052787126264 v277 v277) → (sv v277 = (sv v2 + 1) / 2) → ((v278 = 1 ↔ sv v9 < sv v277)) → ((v279 = 1 ↔ ¬v278 = 1)) → (R 1 0 0 1 v280 v280) → ((v280 = 1 ↔ v44 = 1 ∧ v279 = 1)) → (sv v288 = sv v31 + sv t42.2) → ((v289 = 1 ↔ sv v288 < sv v33)) → (v290 = if v289 = 1 then v288 else v33) → ((v291 = 1 ↔ sv v42 < sv v115)) → (R 1 0 4611686018158952449 4611686018695823367 v292 v292) → (v292 = if v291 = 1 then v33 else v290) → (sv t277.1 = (sc28pS (scArg v277)).1) → ((v294 = 1 ↔ sv t42.1 < sv t277.1)) → (v295 = if v294 = 1 then t42.1 else t277.1) → (sv v296 = sv v28 + sv v295) → (v297 = if v294 = 1 then t277.1 else t42.1) → (sv v298 = sv v31 + sv v297) → ((v299 = 1 ↔ sv v298 < sv v33)) → (v300 = if v299 = 1 then v298 else v33) → ((v301 = 1 ↔ sv v38 < sv v277)) → ((v302 = 1 ↔ v57 = 1 ∧ v301 = 1)) → (v303 = if v302 = 1 then v33 else v300) → ((v304 = 1 ↔ sv v296 < sv v61)) → ((v306 = 1 ↔ sv v61 < sv v303)) → ((v307 = 1 ↔ ¬v306 = 1)) → ((v308 = 1 ↔ v304 = 1 ∧ v307 = 1)) → ((v309 = 1 ↔ v304 = 1 ∧ v306 = 1)) → ((v310 = 1 ↔ v149 = 1 ∧ v309 = 1)) → ((v311 = 1 ↔ v145 = 1 ∧ v309 = 1)) → ((v312 = 1 ↔ v308 = 1 ∨ v311 = 1)) → (v313 = if v312 = 1 then v117 else v110) → ((v314 = 1 ↔ ¬v308 = 1)) → ((v315 = 1 ↔ v149 = 1 ∧ v314 = 1)) → ((v316 = 1 ↔ v148 = 1 ∨ v315 = 1)) → (v317 = if v316 = 1 then v303 else v296) → ((v318 = 1 ↔ v148 = 1 ∧ v309 = 1)) → ((v319 = 1 ↔ v308 = 1 ∨ v318 = 1)) → (v320 = if v319 = 1 then v110 else v117) → ((v321 = 1 ↔ v149 = 1 ∧ v308 = 1)) → ((v322 = 1 ↔ v148 = 1 ∨ v321 = 1)) → (v323 = if v322 = 1 then v296 else v303) → (sv v324 = sv v317 * sv v313) → (sv v325 = sv v324 / 2 ^ 28) → (sv v326 = sv v323 * sv v320) → (sv v327 = -((-sv v326) / 2 ^ 28)) → (sv v328 = sv v296 * sv v117) → (sv v329 = sv v328 / 2 ^ 28) → (sv v330 = sv v296 * sv v110) → (sv v331 = -((-sv v330) / 2 ^ 28)) → ((v332 = 1 ↔ sv v325 < sv v329)) → (v333 = if v332 = 1 then v325 else v329) → ((v334 = 1 ↔ sv v327 < sv v331)) → (v335 = if v334 = 1 then v331 else v327) → (v336 = if v310 = 1 then v333 else v325) → (v337 = if v310 = 1 then v335 else v327) → ((v338 = 1 ↔ sv v61 < sv v336)) → ((v339 = 1 ↔ ¬v338 = 1)) → ((v342 = 1 ↔ sv v292 < sv v61)) → (v343 = if v342 = 1 then v337 else v336) → (sv v385 = sv v61 - sv v292) → (v386 = if v342 = 1 then v385 else v292) → (sv v387 = ((H0 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ)) → (sv t387.1 = (sc28pS (scArg v387)).1) → (sv t387.2 = (sc28pS (scArg v387)).2) → (sv v389 = sv v28 + sv t387.2) → ((v390 = 1 ↔ sv v389 < sv v105)) → (v391 = if v390 = 1 then v105 else v389) → (sv v392 = sv v31 + sv t387.2) → ((v393 = 1 ↔ sv v392 < sv v33)) → (v394 = if v393 = 1 then v392 else v33) → (sv v396 = sv v31 + sv t387.1) → ((v397 = 1 ↔ sv v396 < sv v33)) → (v398 = if v397 = 1 then v396 else v33) → (sv v399 = sv v28 + sv t387.1) → (v400 = if v342 = 1 then v391 else v394) → (v401 = if v342 = 1 then v398 else v399) → (sv v402 = sv v343 * sv v401) → (sv v403 = sv v400 * sv v386) → ((v404 = 1 ↔ sv v403 < sv v402)) → ((v405 = 1 ↔ ¬v404 = 1)) → ((v406 = 1 ↔ sv v402 < sv v403)) → ((v407 = 1 ↔ ¬v406 = 1)) → ((v408 = 1 ↔ sv v61 < sv v387)) → ((v409 = 1 ↔ ¬v408 = 1)) → ((v410 = 1 ↔ sv v216 < sv v387)) → ((v411 = 1 ↔ ¬v410 = 1)) → ((v412 = 1 ↔ sv v19 < sv v391)) → ((v413 = 1 ↔ v405 = 1 ∧ v412 = 1)) → ((v414 = 1 ↔ v411 = 1 ∧ v413 = 1)) → ((v415 = 1 ↔ v409 = 1 ∨ v414 = 1)) → ((v416 = 1 ↔ sv v387 < sv v223)) → ((v417 = 1 ↔ ¬v416 = 1)) → ((v418 = 1 ↔ v407 = 1 ∨ v417 = 1)) → ((v419 = 1 ↔ v342 = 1 ∧ v415 = 1)) → ((v420 = 1 ↔ ¬v342 = 1)) → ((v421 = 1 ↔ v418 = 1 ∧ v420 = 1)) → ((v422 = 1 ↔ v419 = 1 ∨ v421 = 1)) → (sv v423 = sv v61 - sv v387) → (v424 = if v342 = 1 then v423 else v387) → (v425 = if v422 = 1 then v424 else v223) → (R 1 0 4611686017353646081 4611686019501129727 v427 v427) → (v427 = if v339 = 1 then v223 else v425) → (R 1 0 4611686018427387904 4611686052787126264 v428 v428) → (sv v428 = sv v4 / 2) → (R 1 0 4611686018427387904 4611686052787126264 v429 v429) → (sv v429 = (sv v5 + 1) / 2) → ((v430 = 1 ↔ sv v19 < sv v428)) → ((v431 = 1 ↔ sv v9 < sv v429)) → (R 1 0 0 1 v432 v432) → ((v432 = 1 ↔ ¬v431 = 1)) → (R 1 0 0 1 v433 v433) → ((v433 = 1 ↔ v430 = 1 ∧ v432 = 1)) → (R 1 0 4611686018427387904 4611686018695823363 t428.1 t428.1) → (sv t428.1 = (sc28pS (scArg v428)).1) → (sv t428.2 = (sc28pS (scArg v428)).2) → (R 1 0 4611686018427387904 4611686018695823363 t429.1 t429.1) → (sv t429.1 = (sc28pS (scArg v429)).1) → (sv t429.2 = (sc28pS (scArg v429)).2) → ((v436 = 1 ↔ sv t428.1 < sv t429.1)) → (v437 = if v436 = 1 then t428.1 else t429.1) → (R 1 0 4611686018427387900 4611686018695823359 v438 v438) → (sv v438 = sv v28 + sv v437) → (v439 = if v436 = 1 then t429.1 else t428.1) → (sv v440 = sv v31 + sv v439) → ((v441 = 1 ↔ sv v440 < sv v33)) → (v442 = if v441 = 1 then v440 else v33) → ((v443 = 1 ↔ sv v428 < sv v36)) → (R 1 0 0 1 v444 v444) → ((v444 = 1 ↔ sv v38 < sv v429)) → ((v445 = 1 ↔ v443 = 1 ∧ v444 = 1)) → (R 1 0 4611686018427387908 4611686018695823367 v446 v446) → (v446 = if v445 = 1 then v33 else v442) → ((v447 = 1 ↔ sv v438 < sv v61)) → ((v449 = 1 ↔ sv v61 < sv v446)) → ((v450 = 1 ↔ ¬v449 = 1)) → (R 1 0 0 1 v451 v451) → ((v451 = 1 ↔ v447 = 1 ∧ v450 = 1)) → (R 1 0 0 1 v452 v452) → ((v452 = 1 ↔ v447 = 1 ∧ v449 = 1)) → ((v453 = 1 ↔ v67 = 1 ∧ v452 = 1)) → ((v454 = 1 ↔ v63 = 1 ∧ v452 = 1)) → ((v455 = 1 ↔ v451 = 1 ∨ v454 = 1)) → (v456 = if v455 = 1 then v41 else v29) → (R 1 0 0 1 v457 v457) → ((v457 = 1 ↔ ¬v451 = 1)) → ((v458 = 1 ↔ v67 = 1 ∧ v457 = 1)) → ((v459 = 1 ↔ v66 = 1 ∨ v458 = 1)) → (v460 = if v459 = 1 then v446 else v438) → ((v461 = 1 ↔ v66 = 1 ∧ v452 = 1)) → ((v462 = 1 ↔ v451 = 1 ∨ v461 = 1)) → (v463 = if v462 = 1 then v29 else v41) → ((v464 = 1 ↔ v67 = 1 ∧ v451 = 1)) → ((v465 = 1 ↔ v66 = 1 ∨ v464 = 1)) → (v466 = if v465 = 1 then v438 else v446) → (sv v467 = sv v460 * sv v456) → (sv v468 = sv v467 / 2 ^ 28) → (sv v469 = sv v466 * sv v463) → (sv v470 = -((-sv v469) / 2 ^ 28)) → (sv v471 = sv v438 * sv v41) → (sv v472 = sv v471 / 2 ^ 28) → (sv v473 = sv v438 * sv v29) → (sv v474 = -((-sv v473) / 2 ^ 28)) → ((v475 = 1 ↔ sv v468 < sv v472)) → (v476 = if v475 = 1 then v468 else v472) → ((v477 = 1 ↔ sv v470 < sv v474)) → (v478 = if v477 = 1 then v474 else v470) → (R 1 0 4611686018427387899 4611686018695823374 v479 v479) → (v479 = if v453 = 1 then v476 else v468) → (R 1 0 4611686018427387900 4611686018695823375 v480 v480) → (v480 = if v453 = 1 then v478 else v470) → (R 1 0 0 1 v481 v481) → ((v481 = 1 ↔ sv v19 < sv v479)) → (R 1 0 4611686018427387904 4611686052787126264 v482 v482) → (sv v482 = sv v5 / 2) → ((v483 = 1 ↔ sv v19 < sv v482)) → (R 1 0 0 1 v484 v484) → ((v484 = 1 ↔ v432 = 1 ∧ v483 = 1)) → (sv v486 = sv v28 + sv t429.2) → ((v487 = 1 ↔ sv v486 < sv v105)) → (v488 = if v487 = 1 then v105 else v486) → ((v489 = 1 ↔ sv v108 < sv v429)) → (R 1 0 4611686018158952441 4611686018695823359 v490 v490) → (v490 = if v489 = 1 then v105 else v488) → (R 1 0 4611686018427387904 4611686018695823363 t482.1 t482.1) → (sv t482.1 = (sc28pS (scArg v482)).1) → ((v498 = 1 ↔ sv t482.1 < sv t429.1)) → (v499 = if v498 = 1 then t482.1 else t429.1) → (sv v500 = sv v28 + sv v499) → (v501 = if v498 = 1 then t429.1 else t482.1) → (sv v502 = sv v31 + sv v501) → ((v503 = 1 ↔ sv v502 < sv v33)) → (v504 = if v503 = 1 then v502 else v33) → ((v505 = 1 ↔ sv v482 < sv v36)) → ((v506 = 1 ↔ v444 = 1 ∧ v505 = 1)) → (v507 = if v506 = 1 then v33 else v504) → ((v508 = 1 ↔ sv v500 < sv v61)) → ((v510 = 1 ↔ sv v61 < sv v507)) → ((v511 = 1 ↔ ¬v510 = 1)) → ((v512 = 1 ↔ v508 = 1 ∧ v511 = 1)) → ((v513 = 1 ↔ v508 = 1 ∧ v510 = 1)) → ((v514 = 1 ↔ v149 = 1 ∧ v513 = 1)) → ((v515 = 1 ↔ v145 = 1 ∧ v513 = 1)) → ((v516 = 1 ↔ v512 = 1 ∨ v515 = 1)) → (v517 = if v516 = 1 then v117 else v110) → ((v518 = 1 ↔ ¬v512 = 1)) → ((v519 = 1 ↔ v149 = 1 ∧ v518 = 1)) → ((v520 = 1 ↔ v148 = 1 ∨ v519 = 1)) → (v521 = if v520 = 1 then v507 else v500) → ((v522 = 1 ↔ v148 = 1 ∧ v513 = 1)) → ((v523 = 1 ↔ v512 = 1 ∨ v522 = 1)) → (v524 = if v523 = 1 then v110 else v117) → ((v525 = 1 ↔ v149 = 1 ∧ v512 = 1)) → ((v526 = 1 ↔ v148 = 1 ∨ v525 = 1)) → (v527 = if v526 = 1 then v500 else v507) → (sv v528 = sv v521 * sv v517) → (sv v529 = sv v528 / 2 ^ 28) → (sv v530 = sv v527 * sv v524) → (sv v531 = -((-sv v530) / 2 ^ 28)) → (sv v532 = sv v500 * sv v117) → (sv v533 = sv v532 / 2 ^ 28) → (sv v534 = sv v500 * sv v110) → (sv v535 = -((-sv v534) / 2 ^ 28)) → ((v536 = 1 ↔ sv v529 < sv v533)) → (v537 = if v536 = 1 then v529 else v533) → ((v538 = 1 ↔ sv v531 < sv v535)) → (v539 = if v538 = 1 then v535 else v531) → (v540 = if v514 = 1 then v537 else v529) → (v541 = if v514 = 1 then v539 else v531) → ((v542 = 1 ↔ sv v61 < sv v540)) → ((v543 = 1 ↔ ¬v542 = 1)) → (R 1 0 0 1 v544 v544) → ((v544 = 1 ↔ sv v490 < sv v61)) → (v545 = if v544 = 1 then v540 else v541) → (sv v548 = sv v61 - sv v490) → (v549 = if v544 = 1 then v548 else v490) → (sv v550 = ((H1 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ)) → ((v551 = 1 ↔ ¬v544 = 1)) → (sv t550.1 = (sc28pS (scArg v550)).1) → (sv t550.2 = (sc28pS (scArg v550)).2) → (sv v553 = sv v28 + sv t550.2) → ((v554 = 1 ↔ sv v553 < sv v105)) → (v555 = if v554 = 1 then v105 else v553) → (sv v556 = sv v31 + sv t550.2) → ((v557 = 1 ↔ sv v556 < sv v33)) → (v558 = if v557 = 1 then v556 else v33) → (sv v560 = sv v31 + sv t550.1) → ((v561 = 1 ↔ sv v560 < sv v33)) → (v562 = if v561 = 1 then v560 else v33) → (sv v563 = sv v28 + sv t550.1) → (v564 = if v551 = 1 then v555 else v558) → (v565 = if v551 = 1 then v562 else v563) → (sv v566 = sv v545 * sv v565) → (sv v567 = sv v564 * sv v549) → ((v568 = 1 ↔ sv v567 < sv v566)) → ((v569 = 1 ↔ ¬v568 = 1)) → ((v570 = 1 ↔ sv v566 < sv v567)) → ((v571 = 1 ↔ ¬v570 = 1)) → ((v572 = 1 ↔ sv v61 < sv v550)) → ((v573 = 1 ↔ ¬v572 = 1)) → ((v574 = 1 ↔ sv v216 < sv v550)) → ((v575 = 1 ↔ ¬v574 = 1)) → ((v576 = 1 ↔ sv v19 < sv v555)) → ((v577 = 1 ↔ v569 = 1 ∧ v576 = 1)) → ((v578 = 1 ↔ v575 = 1 ∧ v577 = 1)) → ((v579 = 1 ↔ v573 = 1 ∨ v578 = 1)) → ((v580 = 1 ↔ sv v550 < sv v223)) → ((v581 = 1 ↔ ¬v580 = 1)) → ((v582 = 1 ↔ v571 = 1 ∨ v581 = 1)) → ((v583 = 1 ↔ v551 = 1 ∧ v579 = 1)) → ((v584 = 1 ↔ v544 = 1 ∧ v582 = 1)) → ((v585 = 1 ↔ v583 = 1 ∨ v584 = 1)) → (sv v586 = sv v61 - sv v550) → (v587 = if v544 = 1 then v586 else v550) → (v588 = if v585 = 1 then v587 else v232) → (R 1 0 4611686017353646081 4611686019501129727 v630 v630) → (v630 = if v543 = 1 then v232 else v588) → (R 1 0 4611686018427387904 4611686052787126264 v632 v632) → (sv v632 = (sv v4 + 1) / 2) → ((v633 = 1 ↔ sv v9 < sv v632)) → ((v634 = 1 ↔ ¬v633 = 1)) → (R 1 0 0 1 v635 v635) → ((v635 = 1 ↔ v430 = 1 ∧ v634 = 1)) → (sv v643 = sv v31 + sv t428.2) → ((v644 = 1 ↔ sv v643 < sv v33)) → (v645 = if v644 = 1 then v643 else v33) → ((v646 = 1 ↔ sv v428 < sv v115)) → (R 1 0 4611686018158952449 4611686018695823367 v647 v647) → (v647 = if v646 = 1 then v33 else v645) → (sv t632.1 = (sc28pS (scArg v632)).1) → ((v649 = 1 ↔ sv t428.1 < sv t632.1)) → (v650 = if v649 = 1 then t428.1 else t632.1) → (R 1 0 4611686018427387900 4611686018695823359 v651 v651) → (sv v651 = sv v28 + sv v650) → (v652 = if v649 = 1 then t632.1 else t428.1) → (sv v653 = sv v31 + sv v652) → ((v654 = 1 ↔ sv v653 < sv v33)) → (v655 = if v654 = 1 then v653 else v33) → ((v656 = 1 ↔ sv v38 < sv v632)) → ((v657 = 1 ↔ v443 = 1 ∧ v656 = 1)) → (R 1 0 4611686018427387908 4611686018695823367 v658 v658) → (v658 = if v657 = 1 then v33 else v655) → ((v659 = 1 ↔ sv v651 < sv v61)) → ((v661 = 1 ↔ sv v61 < sv v658)) → ((v662 = 1 ↔ ¬v661 = 1)) → (R 1 0 0 1 v663 v663) → ((v663 = 1 ↔ v659 = 1 ∧ v662 = 1)) → ((v664 = 1 ↔ v659 = 1 ∧ v661 = 1)) → (R 1 0 0 1 v665 v665) → ((v665 = 1 ↔ v149 = 1 ∧ v664 = 1)) → ((v666 = 1 ↔ v145 = 1 ∧ v664 = 1)) → ((v667 = 1 ↔ v663 = 1 ∨ v666 = 1)) → (R 1 0 4611686018158952441 4611686018695823367 v668 v668) → (v668 = if v667 = 1 then v117 else v110) → ((v669 = 1 ↔ ¬v663 = 1)) → ((v670 = 1 ↔ v149 = 1 ∧ v669 = 1)) → ((v671 = 1 ↔ v148 = 1 ∨ v670 = 1)) → (R 1 0 4611686018427387900 4611686018695823367 v672 v672) → (v672 = if v671 = 1 then v658 else v651) → (R 1 0 0 1 v673 v673) → ((v673 = 1 ↔ v148 = 1 ∧ v664 = 1)) → P) → P := by
  intro OFFr H61r v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11 v12 v13 v15 v19 v20 v21 v22 v23 t0 t1 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 t42 t43 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v104 v105 v106 v107 v108 v109 v110 v112 v113 v114 v115 v116 v117 v118 v119 v120 v122 v123 v124 v125 v126 t118 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v152 v153 v154 v155 v156 v157 v158 v159 v160 v161 v162 v163 v164 v165 v166 v167 v168 v169 v170 v171 v172 v173 v174 v175 v176 v177 v178 v179 v180 v181 v182 v183 v184 v185 v186 v187 v190 v191 v192 v193 t192 v195 v196 v197 v198 v199 v200 v202 v203 v204 v205 v206 v207 v208 v209 v210 v211 v212 v213 v214 v215 v216 v217 v218 v219 v220 v221 v222 v223 v224 v225 v226 v227 v228 v229 v230 v231 v232 v233 v275 v277 v278 v279 v280 v288 v289 v290 v291 v292 t277 v294 v295 v296 v297 v298 v299 v300 v301 v302 v303 v304 v306 v307 v308 v309 v310 v311 v312 v313 v314 v315 v316 v317 v318 v319 v320 v321 v322 v323 v324 v325 v326 v327 v328 v329 v330 v331 v332 v333 v334 v335 v336 v337 v338 v339 v342 v343 v385 v386 v387 t387 v389 v390 v391 v392 v393 v394 v396 v397 v398 v399 v400 v401 v402 v403 v404 v405 v406 v407 v408 v409 v410 v411 v412 v413 v414 v415 v416 v417 v418 v419 v420 v421 v422 v423 v424 v425 v427 v428 v429 v430 v431 v432 v433 t428 t429 v436 v437 v438 v439 v440 v441 v442 v443 v444 v445 v446 v447 v449 v450 v451 v452 v453 v454 v455 v456 v457 v458 v459 v460 v461 v462 v463 v464 v465 v466 v467 v468 v469 v470 v471 v472 v473 v474 v475 v476 v477 v478 v479 v480 v481 v482 v483 v484 v486 v487 v488 v489 v490 t482 v498 v499 v500 v501 v502 v503 v504 v505 v506 v507 v508 v510 v511 v512 v513 v514 v515 v516 v517 v518 v519 v520 v521 v522 v523 v524 v525 v526 v527 v528 v529 v530 v531 v532 v533 v534 v535 v536 v537 v538 v539 v540 v541 v542 v543 v544 v545 v548 v549 v550 v551 t550 v553 v554 v555 v556 v557 v558 v560 v561 v562 v563 v564 v565 v566 v567 v568 v569 v570 v571 v572 v573 v574 v575 v576 v577 v578 v579 v580 v581 v582 v583 v584 v585 v586 v587 v588 v630 v632 v633 v634 v635 v643 v644 v645 v646 v647 t632 v649 v650 v651 v652 v653 v654 v655 v656 v657 v658 v659 v661 v662 v663 v664 v665 v666 v667 v668 v669 v670 v671 v672 v673
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_H61r : R 1 0 2305843009213693952 2305843009213693952 H61r H61r := (r_c hl 2305843009213693952 (of_decide_eq_true rfl))
  have h_v0 : R 1 0 4611686018427387904 4611686087146864624 v0 v0 := (r1_ix hb_F0 0 (of_decide_eq_true rfl))
  have e_v0 : sv v0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F0 0 (of_decide_eq_true rfl)
  have h_v1 : R 1 0 4611686018427387904 4611686087146864624 v1 v1 := (r1_ix hb_F0 32 (of_decide_eq_true rfl))
  have e_v1 : sv v1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F0 32 (of_decide_eq_true rfl)
  have h_v2 : R 1 0 4611686018427387904 4611686087146864624 v2 v2 := (r1_ix hb_F1 0 (of_decide_eq_true rfl))
  have e_v2 : sv v2 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F1 0 (of_decide_eq_true rfl)
  have h_v3 : R 1 0 4611686018427387904 4611686087146864624 v3 v3 := (r1_ix hb_F1 32 (of_decide_eq_true rfl))
  have e_v3 : sv v3 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F1 32 (of_decide_eq_true rfl)
  have h_v4 : R 1 0 4611686018427387904 4611686087146864624 v4 v4 := (r1_ix hb_F2 0 (of_decide_eq_true rfl))
  have e_v4 : sv v4 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F2 0 (of_decide_eq_true rfl)
  have h_v5 : R 1 0 4611686018427387904 4611686087146864624 v5 v5 := (r1_ix hb_F2 32 (of_decide_eq_true rfl))
  have e_v5 : sv v5 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F2 32 (of_decide_eq_true rfl)
  have e_v6 : sv v6 = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F3 0 (of_decide_eq_true rfl)
  have h_v7 : R 1 0 4611686018427387904 4611686087146864624 v7 v7 := (r1_ix hb_F3 32 (of_decide_eq_true rfl))
  have e_v7 : sv v7 = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F3 32 (of_decide_eq_true rfl)
  have h_v9 : R 1 0 4611686019270702761 4611686019270702761 v9 v9 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have e_v9 : sv v9 = (843314857) := e_c 4611686019270702761 (843314857) (of_decide_eq_true rfl)
  have h_v10 : R 1 0 4611686019270702761 4611686087990179481 v10 v10 := (r_sub hl (r_add hl h_v7 h_v9 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v10 : sv v10 = sv v7 + sv v9 := e_add h_v7 h_v9 (of_decide_eq_true rfl)
  have h_v11 : R 1 0 4611686020114017616 4611686020114017616 v11 v11 := (r_c hl 4611686020114017616 (of_decide_eq_true rfl))
  have e_v11 : sv v11 = (1686629712) := e_c 4611686020114017616 (1686629712) (of_decide_eq_true rfl)
  have h_v12 : R 1 0 0 1 v12 v12 := (r_plt hl h_v11 h_v10 (of_decide_eq_true rfl))
  have e_v12 : (v12 = 1 ↔ sv v11 < sv v10) := e_plt h_v11 h_v10 (of_decide_eq_true rfl)
  clear h_v7 h_v10 h_v11
  have h_v13 : R 1 0 0 1 v13 v13 := (r_sub hl (r_O hl) h_v12 (of_decide_eq_true rfl))
  have e_v13 : (v13 = 1 ↔ ¬v12 = 1) := e_not h_v12 (of_decide_eq_true rfl)
  have e_v15 : sv v15 = (843314856) := e_c 4611686019270702760 (843314856) (of_decide_eq_true rfl)
  have h_v19 : R 1 0 4611686018427387903 4611686018427387903 v19 v19 := (r_c hl 4611686018427387903 (of_decide_eq_true rfl))
  have e_v19 : sv v19 = (-1) := e_c 4611686018427387903 (-1) (of_decide_eq_true rfl)
  have h_v20 : R 1 0 0 1 v20 v20 := (r_plt hl h_v19 h_v0 (of_decide_eq_true rfl))
  have e_v20 : (v20 = 1 ↔ sv v19 < sv v0) := e_plt h_v19 h_v0 (of_decide_eq_true rfl)
  have h_v21 : R 1 0 0 1 v21 v21 := (r_plt hl h_v9 h_v1 (of_decide_eq_true rfl))
  have e_v21 : (v21 = 1 ↔ sv v9 < sv v1) := e_plt h_v9 h_v1 (of_decide_eq_true rfl)
  have h_v22 : R 1 0 0 1 v22 v22 := (r_sub hl (r_O hl) h_v21 (of_decide_eq_true rfl))
  have e_v22 : (v22 = 1 ↔ ¬v21 = 1) := e_not h_v21 (of_decide_eq_true rfl)
  have h_v23 : R 1 0 0 1 v23 v23 := (r_land hl h_v20 h_v22 (of_decide_eq_true rfl))
  have e_v23 : (v23 = 1 ↔ v20 = 1 ∧ v22 = 1) := e_land h_v20 h_v22 (of_decide_eq_true rfl)
  have h_t0_1 : R 1 0 4611686018427387904 4611686018695823363 t0.1 t0.1 := r_sc1 hl h_v0 (of_decide_eq_true rfl)
  have h_t0_2 : R 1 0 4611686018158952445 4611686018695823363 t0.2 t0.2 := r_sc2 hl h_v0 (of_decide_eq_true rfl)
  have e_t0_1 : sv t0.1 = (sc28pS (scArg v0)).1 := e_sc1 h_v0 (of_decide_eq_true rfl)
  have e_t0_2 : sv t0.2 = (sc28pS (scArg v0)).2 := e_sc2 h_v0 (of_decide_eq_true rfl)
  have h_t1_1 : R 1 0 4611686018427387904 4611686018695823363 t1.1 t1.1 := r_sc1 hl h_v1 (of_decide_eq_true rfl)
  have h_t1_2 : R 1 0 4611686018158952445 4611686018695823363 t1.2 t1.2 := r_sc2 hl h_v1 (of_decide_eq_true rfl)
  have e_t1_1 : sv t1.1 = (sc28pS (scArg v1)).1 := e_sc1 h_v1 (of_decide_eq_true rfl)
  have e_t1_2 : sv t1.2 = (sc28pS (scArg v1)).2 := e_sc2 h_v1 (of_decide_eq_true rfl)
  have h_v26 : R 1 0 0 1 v26 v26 := (r_plt hl h_t0_1 h_t1_1 (of_decide_eq_true rfl))
  have e_v26 : (v26 = 1 ↔ sv t0.1 < sv t1.1) := e_plt h_t0_1 h_t1_1 (of_decide_eq_true rfl)
  have h_v27 : R 1 0 4611686018427387904 4611686018695823363 v27 v27 := (r_psel hl h_v26 h_t0_1 h_t1_1 (of_decide_eq_true rfl))
  have e_v27 : v27 = if v26 = 1 then t0.1 else t1.1 := e_psel h_v26 h_t0_1 h_t1_1 (of_decide_eq_true rfl)
  clear h_v12 h_v20 h_v21 h_v22
  have h_v28 : R 1 0 4611686018427387900 4611686018427387900 v28 v28 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have e_v28 : sv v28 = (-4) := e_c 4611686018427387900 (-4) (of_decide_eq_true rfl)
  have h_v29 : R 1 0 4611686018427387900 4611686018695823359 v29 v29 := (r_sub hl (r_add hl h_v27 h_v28 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v29 : sv v29 = sv v27 + sv v28 := e_add h_v27 h_v28 (of_decide_eq_true rfl)
  have h_v30 : R 1 0 4611686018427387904 4611686018695823363 v30 v30 := (r_psel hl h_v26 h_t1_1 h_t0_1 (of_decide_eq_true rfl))
  have e_v30 : v30 = if v26 = 1 then t1.1 else t0.1 := e_psel h_v26 h_t1_1 h_t0_1 (of_decide_eq_true rfl)
  have h_v31 : R 1 0 4611686018427387908 4611686018427387908 v31 v31 := (r_c hl 4611686018427387908 (of_decide_eq_true rfl))
  have e_v31 : sv v31 = (4) := e_c 4611686018427387908 (4) (of_decide_eq_true rfl)
  have h_v32 : R 1 0 4611686018427387908 4611686018695823367 v32 v32 := (r_sub hl (r_add hl h_v30 h_v31 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v32 : sv v32 = sv v30 + sv v31 := e_add h_v30 h_v31 (of_decide_eq_true rfl)
  have h_v33 : R 1 0 4611686018695823360 4611686018695823360 v33 v33 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have e_v33 : sv v33 = (268435456) := e_c 4611686018695823360 (268435456) (of_decide_eq_true rfl)
  have h_v34 : R 1 0 0 1 v34 v34 := (r_plt hl h_v32 h_v33 (of_decide_eq_true rfl))
  have e_v34 : (v34 = 1 ↔ sv v32 < sv v33) := e_plt h_v32 h_v33 (of_decide_eq_true rfl)
  have h_v35 : R 1 0 4611686018427387908 4611686018695823367 v35 v35 := (r_psel hl h_v34 h_v32 h_v33 (of_decide_eq_true rfl))
  have e_v35 : v35 = if v34 = 1 then v32 else v33 := e_psel h_v34 h_v32 h_v33 (of_decide_eq_true rfl)
  have h_v36 : R 1 0 4611686018849045334 4611686018849045334 v36 v36 := (r_c hl 4611686018849045334 (of_decide_eq_true rfl))
  have e_v36 : sv v36 = (421657430) := e_c 4611686018849045334 (421657430) (of_decide_eq_true rfl)
  have h_v37 : R 1 0 0 1 v37 v37 := (r_plt hl h_v0 h_v36 (of_decide_eq_true rfl))
  have e_v37 : (v37 = 1 ↔ sv v0 < sv v36) := e_plt h_v0 h_v36 (of_decide_eq_true rfl)
  have h_v38 : R 1 0 4611686018849045331 4611686018849045331 v38 v38 := (r_c hl 4611686018849045331 (of_decide_eq_true rfl))
  have e_v38 : sv v38 = (421657427) := e_c 4611686018849045331 (421657427) (of_decide_eq_true rfl)
  have h_v39 : R 1 0 0 1 v39 v39 := (r_plt hl h_v38 h_v1 (of_decide_eq_true rfl))
  have e_v39 : (v39 = 1 ↔ sv v38 < sv v1) := e_plt h_v38 h_v1 (of_decide_eq_true rfl)
  have h_v40 : R 1 0 0 1 v40 v40 := (r_land hl h_v37 h_v39 (of_decide_eq_true rfl))
  clear h_t0_1 h_t1_1 h_v26 h_v27 h_v30 h_v32 h_v34
  have e_v40 : (v40 = 1 ↔ v37 = 1 ∧ v39 = 1) := e_land h_v37 h_v39 (of_decide_eq_true rfl)
  have h_v41 : R 1 0 4611686018427387908 4611686018695823367 v41 v41 := (r_psel hl h_v40 h_v33 h_v35 (of_decide_eq_true rfl))
  have e_v41 : v41 = if v40 = 1 then v33 else v35 := e_psel h_v40 h_v33 h_v35 (of_decide_eq_true rfl)
  have h_v42 : R 1 0 4611686018427387904 4611686052787126264 v42 v42 := (r_add hl (r_pshr1 hl h_v2) h_H61r (of_decide_eq_true rfl))
  have e_v42 : sv v42 = sv v2 / 2 := e_halfF h_v2
  have h_v43 : R 1 0 4611686018427387904 4611686052787126264 v43 v43 := (r_add hl (r_pshr1 hl (r_add hl h_v3 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v43 : sv v43 = (sv v3 + 1) / 2 := e_halfC h_v3 (of_decide_eq_true rfl)
  have h_v44 : R 1 0 0 1 v44 v44 := (r_plt hl h_v19 h_v42 (of_decide_eq_true rfl))
  have e_v44 : (v44 = 1 ↔ sv v19 < sv v42) := e_plt h_v19 h_v42 (of_decide_eq_true rfl)
  have h_v45 : R 1 0 0 1 v45 v45 := (r_plt hl h_v9 h_v43 (of_decide_eq_true rfl))
  have e_v45 : (v45 = 1 ↔ sv v9 < sv v43) := e_plt h_v9 h_v43 (of_decide_eq_true rfl)
  have h_v46 : R 1 0 0 1 v46 v46 := (r_sub hl (r_O hl) h_v45 (of_decide_eq_true rfl))
  have e_v46 : (v46 = 1 ↔ ¬v45 = 1) := e_not h_v45 (of_decide_eq_true rfl)
  have h_v47 : R 1 0 0 1 v47 v47 := (r_land hl h_v44 h_v46 (of_decide_eq_true rfl))
  have e_v47 : (v47 = 1 ↔ v44 = 1 ∧ v46 = 1) := e_land h_v44 h_v46 (of_decide_eq_true rfl)
  have h_t42_1 : R 1 0 4611686018427387904 4611686018695823363 t42.1 t42.1 := r_sc1 hl h_v42 (of_decide_eq_true rfl)
  have h_t42_2 : R 1 0 4611686018158952445 4611686018695823363 t42.2 t42.2 := r_sc2 hl h_v42 (of_decide_eq_true rfl)
  have e_t42_1 : sv t42.1 = (sc28pS (scArg v42)).1 := e_sc1 h_v42 (of_decide_eq_true rfl)
  have e_t42_2 : sv t42.2 = (sc28pS (scArg v42)).2 := e_sc2 h_v42 (of_decide_eq_true rfl)
  have h_t43_1 : R 1 0 4611686018427387904 4611686018695823363 t43.1 t43.1 := r_sc1 hl h_v43 (of_decide_eq_true rfl)
  have h_t43_2 : R 1 0 4611686018158952445 4611686018695823363 t43.2 t43.2 := r_sc2 hl h_v43 (of_decide_eq_true rfl)
  have e_t43_1 : sv t43.1 = (sc28pS (scArg v43)).1 := e_sc1 h_v43 (of_decide_eq_true rfl)
  have e_t43_2 : sv t43.2 = (sc28pS (scArg v43)).2 := e_sc2 h_v43 (of_decide_eq_true rfl)
  have h_v50 : R 1 0 0 1 v50 v50 := (r_plt hl h_t42_1 h_t43_1 (of_decide_eq_true rfl))
  have e_v50 : (v50 = 1 ↔ sv t42.1 < sv t43.1) := e_plt h_t42_1 h_t43_1 (of_decide_eq_true rfl)
  clear h_v35 h_v37 h_v39 h_v40 h_v45
  have h_v51 : R 1 0 4611686018427387904 4611686018695823363 v51 v51 := (r_psel hl h_v50 h_t42_1 h_t43_1 (of_decide_eq_true rfl))
  have e_v51 : v51 = if v50 = 1 then t42.1 else t43.1 := e_psel h_v50 h_t42_1 h_t43_1 (of_decide_eq_true rfl)
  have h_v52 : R 1 0 4611686018427387900 4611686018695823359 v52 v52 := (r_sub hl (r_add hl h_v28 h_v51 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v52 : sv v52 = sv v28 + sv v51 := e_add h_v28 h_v51 (of_decide_eq_true rfl)
  have h_v53 : R 1 0 4611686018427387904 4611686018695823363 v53 v53 := (r_psel hl h_v50 h_t43_1 h_t42_1 (of_decide_eq_true rfl))
  have e_v53 : v53 = if v50 = 1 then t43.1 else t42.1 := e_psel h_v50 h_t43_1 h_t42_1 (of_decide_eq_true rfl)
  have h_v54 : R 1 0 4611686018427387908 4611686018695823367 v54 v54 := (r_sub hl (r_add hl h_v31 h_v53 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v54 : sv v54 = sv v31 + sv v53 := e_add h_v31 h_v53 (of_decide_eq_true rfl)
  have h_v55 : R 1 0 0 1 v55 v55 := (r_plt hl h_v54 h_v33 (of_decide_eq_true rfl))
  have e_v55 : (v55 = 1 ↔ sv v54 < sv v33) := e_plt h_v54 h_v33 (of_decide_eq_true rfl)
  have h_v56 : R 1 0 4611686018427387908 4611686018695823367 v56 v56 := (r_psel hl h_v55 h_v54 h_v33 (of_decide_eq_true rfl))
  have e_v56 : v56 = if v55 = 1 then v54 else v33 := e_psel h_v55 h_v54 h_v33 (of_decide_eq_true rfl)
  have h_v57 : R 1 0 0 1 v57 v57 := (r_plt hl h_v42 h_v36 (of_decide_eq_true rfl))
  have e_v57 : (v57 = 1 ↔ sv v42 < sv v36) := e_plt h_v42 h_v36 (of_decide_eq_true rfl)
  have h_v58 : R 1 0 0 1 v58 v58 := (r_plt hl h_v38 h_v43 (of_decide_eq_true rfl))
  have e_v58 : (v58 = 1 ↔ sv v38 < sv v43) := e_plt h_v38 h_v43 (of_decide_eq_true rfl)
  have h_v59 : R 1 0 0 1 v59 v59 := (r_land hl h_v57 h_v58 (of_decide_eq_true rfl))
  have e_v59 : (v59 = 1 ↔ v57 = 1 ∧ v58 = 1) := e_land h_v57 h_v58 (of_decide_eq_true rfl)
  have h_v60 : R 1 0 4611686018427387908 4611686018695823367 v60 v60 := (r_psel hl h_v59 h_v33 h_v56 (of_decide_eq_true rfl))
  have e_v60 : v60 = if v59 = 1 then v33 else v56 := e_psel h_v59 h_v33 h_v56 (of_decide_eq_true rfl)
  have h_v61 : R 1 0 4611686018427387904 4611686018427387904 v61 v61 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have e_v61 : sv v61 = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have h_v62 : R 1 0 0 1 v62 v62 := (r_plt hl h_v29 h_v61 (of_decide_eq_true rfl))
  have e_v62 : (v62 = 1 ↔ sv v29 < sv v61) := e_plt h_v29 h_v61 (of_decide_eq_true rfl)
  have h_v63 : R 1 0 0 1 v63 v63 := (r_sub hl (r_O hl) h_v62 (of_decide_eq_true rfl))
  clear h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v59
  have e_v63 : (v63 = 1 ↔ ¬v62 = 1) := e_not h_v62 (of_decide_eq_true rfl)
  have h_v64 : R 1 0 0 1 v64 v64 := (r_plt hl h_v61 h_v41 (of_decide_eq_true rfl))
  have e_v64 : (v64 = 1 ↔ sv v61 < sv v41) := e_plt h_v61 h_v41 (of_decide_eq_true rfl)
  have h_v65 : R 1 0 0 1 v65 v65 := (r_sub hl (r_O hl) h_v64 (of_decide_eq_true rfl))
  have e_v65 : (v65 = 1 ↔ ¬v64 = 1) := e_not h_v64 (of_decide_eq_true rfl)
  have h_v66 : R 1 0 0 1 v66 v66 := (r_land hl h_v62 h_v65 (of_decide_eq_true rfl))
  have e_v66 : (v66 = 1 ↔ v62 = 1 ∧ v65 = 1) := e_land h_v62 h_v65 (of_decide_eq_true rfl)
  have h_v67 : R 1 0 0 1 v67 v67 := (r_land hl h_v62 h_v64 (of_decide_eq_true rfl))
  have e_v67 : (v67 = 1 ↔ v62 = 1 ∧ v64 = 1) := e_land h_v62 h_v64 (of_decide_eq_true rfl)
  have h_v68 : R 1 0 0 1 v68 v68 := (r_plt hl h_v52 h_v61 (of_decide_eq_true rfl))
  have e_v68 : (v68 = 1 ↔ sv v52 < sv v61) := e_plt h_v52 h_v61 (of_decide_eq_true rfl)
  have h_v70 : R 1 0 0 1 v70 v70 := (r_plt hl h_v61 h_v60 (of_decide_eq_true rfl))
  have e_v70 : (v70 = 1 ↔ sv v61 < sv v60) := e_plt h_v61 h_v60 (of_decide_eq_true rfl)
  have h_v71 : R 1 0 0 1 v71 v71 := (r_sub hl (r_O hl) h_v70 (of_decide_eq_true rfl))
  have e_v71 : (v71 = 1 ↔ ¬v70 = 1) := e_not h_v70 (of_decide_eq_true rfl)
  have h_v72 : R 1 0 0 1 v72 v72 := (r_land hl h_v68 h_v71 (of_decide_eq_true rfl))
  have e_v72 : (v72 = 1 ↔ v68 = 1 ∧ v71 = 1) := e_land h_v68 h_v71 (of_decide_eq_true rfl)
  have h_v73 : R 1 0 0 1 v73 v73 := (r_land hl h_v68 h_v70 (of_decide_eq_true rfl))
  have e_v73 : (v73 = 1 ↔ v68 = 1 ∧ v70 = 1) := e_land h_v68 h_v70 (of_decide_eq_true rfl)
  have h_v74 : R 1 0 0 1 v74 v74 := (r_land hl h_v67 h_v73 (of_decide_eq_true rfl))
  have e_v74 : (v74 = 1 ↔ v67 = 1 ∧ v73 = 1) := e_land h_v67 h_v73 (of_decide_eq_true rfl)
  have h_v75 : R 1 0 0 1 v75 v75 := (r_land hl h_v63 h_v73 (of_decide_eq_true rfl))
  have e_v75 : (v75 = 1 ↔ v63 = 1 ∧ v73 = 1) := e_land h_v63 h_v73 (of_decide_eq_true rfl)
  have h_v76 : R 1 0 0 1 v76 v76 := (r_lor hl h_v72 h_v75 (of_decide_eq_true rfl))
  have e_v76 : (v76 = 1 ↔ v72 = 1 ∨ v75 = 1) := e_lor h_v72 h_v75 (of_decide_eq_true rfl)
  clear h_v62 h_v64 h_v65 h_v68 h_v70 h_v71 h_v75
  have h_v77 : R 1 0 4611686018427387900 4611686018695823367 v77 v77 := (r_psel hl h_v76 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v77 : v77 = if v76 = 1 then v41 else v29 := e_psel h_v76 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v78 : R 1 0 0 1 v78 v78 := (r_sub hl (r_O hl) h_v72 (of_decide_eq_true rfl))
  have e_v78 : (v78 = 1 ↔ ¬v72 = 1) := e_not h_v72 (of_decide_eq_true rfl)
  have h_v79 : R 1 0 0 1 v79 v79 := (r_land hl h_v67 h_v78 (of_decide_eq_true rfl))
  have e_v79 : (v79 = 1 ↔ v67 = 1 ∧ v78 = 1) := e_land h_v67 h_v78 (of_decide_eq_true rfl)
  have h_v80 : R 1 0 0 1 v80 v80 := (r_lor hl h_v66 h_v79 (of_decide_eq_true rfl))
  have e_v80 : (v80 = 1 ↔ v66 = 1 ∨ v79 = 1) := e_lor h_v66 h_v79 (of_decide_eq_true rfl)
  have h_v81 : R 1 0 4611686018427387900 4611686018695823367 v81 v81 := (r_psel hl h_v80 h_v60 h_v52 (of_decide_eq_true rfl))
  have e_v81 : v81 = if v80 = 1 then v60 else v52 := e_psel h_v80 h_v60 h_v52 (of_decide_eq_true rfl)
  have h_v82 : R 1 0 0 1 v82 v82 := (r_land hl h_v66 h_v73 (of_decide_eq_true rfl))
  have e_v82 : (v82 = 1 ↔ v66 = 1 ∧ v73 = 1) := e_land h_v66 h_v73 (of_decide_eq_true rfl)
  have h_v83 : R 1 0 0 1 v83 v83 := (r_lor hl h_v72 h_v82 (of_decide_eq_true rfl))
  have e_v83 : (v83 = 1 ↔ v72 = 1 ∨ v82 = 1) := e_lor h_v72 h_v82 (of_decide_eq_true rfl)
  have h_v84 : R 1 0 4611686018427387900 4611686018695823367 v84 v84 := (r_psel hl h_v83 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v84 : v84 = if v83 = 1 then v29 else v41 := e_psel h_v83 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v85 : R 1 0 0 1 v85 v85 := (r_land hl h_v67 h_v72 (of_decide_eq_true rfl))
  have e_v85 : (v85 = 1 ↔ v67 = 1 ∧ v72 = 1) := e_land h_v67 h_v72 (of_decide_eq_true rfl)
  have h_v86 : R 1 0 0 1 v86 v86 := (r_lor hl h_v66 h_v85 (of_decide_eq_true rfl))
  have e_v86 : (v86 = 1 ↔ v66 = 1 ∨ v85 = 1) := e_lor h_v66 h_v85 (of_decide_eq_true rfl)
  have h_v87 : R 1 0 4611686018427387900 4611686018695823367 v87 v87 := (r_psel hl h_v86 h_v52 h_v60 (of_decide_eq_true rfl))
  have e_v87 : v87 = if v86 = 1 then v52 else v60 := e_psel h_v86 h_v52 h_v60 (of_decide_eq_true rfl)
  have h_v88 : R 1 0 4611686017353646052 4683743616223412273 v88 v88 := (r_smx hl 29 h_v81 h_v77 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v88 : sv v88 = sv v81 * sv v77 := e_smx 29 h_v81 h_v77 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v89 : R 1 0 4611686018427387899 4611686018695823374 v89 v89 := (r_srdF hl h_v88 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  clear h_v76 h_v77 h_v79 h_v80 h_v81 h_v82 h_v83 h_v85 h_v86
  have e_v89 : sv v89 = sv v88 / 2 ^ 28 := e_srdF h_v88 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v90 : R 1 0 4611686017353646052 4683743616223412273 v90 v90 := (r_smx hl 29 h_v87 h_v84 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v90 : sv v90 = sv v87 * sv v84 := e_smx 29 h_v87 h_v84 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v91 : R 1 0 4611686018427387900 4611686018695823375 v91 v91 := (r_srdC hl h_v90 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v91 : sv v91 = -((-sv v90) / 2 ^ 28) := e_srdC h_v90 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v92 : R 1 0 4611686017353646052 4683743614075928569 v92 v92 := (r_smx hl 29 h_v52 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl))
  have e_v92 : sv v92 = sv v52 * sv v41 := e_smx 29 h_v52 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl)
  have h_v93 : R 1 0 4611686018427387899 4611686018695823365 v93 v93 := (r_srdF hl h_v92 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl))
  have e_v93 : sv v93 = sv v92 / 2 ^ 28 := e_srdF h_v92 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl)
  have h_v94 : R 1 0 4611686017353646084 4683743611928444929 v94 v94 := (r_smx hl 29 h_v52 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl))
  have e_v94 : sv v94 = sv v52 * sv v29 := e_smx 29 h_v52 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl)
  have h_v95 : R 1 0 4611686018427387901 4611686018695823359 v95 v95 := (r_srdC hl h_v94 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl))
  have e_v95 : sv v95 = -((-sv v94) / 2 ^ 28) := e_srdC h_v94 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl)
  have h_v96 : R 1 0 0 1 v96 v96 := (r_plt hl h_v89 h_v93 (of_decide_eq_true rfl))
  have e_v96 : (v96 = 1 ↔ sv v89 < sv v93) := e_plt h_v89 h_v93 (of_decide_eq_true rfl)
  have h_v97 : R 1 0 4611686018427387899 4611686018695823374 v97 v97 := (r_psel hl h_v96 h_v89 h_v93 (of_decide_eq_true rfl))
  have e_v97 : v97 = if v96 = 1 then v89 else v93 := e_psel h_v96 h_v89 h_v93 (of_decide_eq_true rfl)
  have h_v98 : R 1 0 0 1 v98 v98 := (r_plt hl h_v91 h_v95 (of_decide_eq_true rfl))
  have e_v98 : (v98 = 1 ↔ sv v91 < sv v95) := e_plt h_v91 h_v95 (of_decide_eq_true rfl)
  have h_v99 : R 1 0 4611686018427387900 4611686018695823375 v99 v99 := (r_psel hl h_v98 h_v95 h_v91 (of_decide_eq_true rfl))
  have e_v99 : v99 = if v98 = 1 then v95 else v91 := e_psel h_v98 h_v95 h_v91 (of_decide_eq_true rfl)
  have h_v100 : R 1 0 4611686018427387899 4611686018695823374 v100 v100 := (r_psel hl h_v74 h_v97 h_v89 (of_decide_eq_true rfl))
  have e_v100 : v100 = if v74 = 1 then v97 else v89 := e_psel h_v74 h_v97 h_v89 (of_decide_eq_true rfl)
  have h_v101 : R 1 0 4611686018427387900 4611686018695823375 v101 v101 := (r_psel hl h_v74 h_v99 h_v91 (of_decide_eq_true rfl))
  have e_v101 : v101 = if v74 = 1 then v99 else v91 := e_psel h_v74 h_v99 h_v91 (of_decide_eq_true rfl)
  clear h_v74 h_v84 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99
  have h_v102 : R 1 0 0 1 v102 v102 := (r_plt hl h_v19 h_v100 (of_decide_eq_true rfl))
  have e_v102 : (v102 = 1 ↔ sv v19 < sv v100) := e_plt h_v19 h_v100 (of_decide_eq_true rfl)
  have h_v104 : R 1 0 4611686018158952441 4611686018695823359 v104 v104 := (r_sub hl (r_add hl h_v28 h_t1_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v104 : sv v104 = sv v28 + sv t1.2 := e_add h_v28 h_t1_2 (of_decide_eq_true rfl)
  have h_v105 : R 1 0 4611686018158952448 4611686018158952448 v105 v105 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have e_v105 : sv v105 = (-268435456) := e_c 4611686018158952448 (-268435456) (of_decide_eq_true rfl)
  have h_v106 : R 1 0 0 1 v106 v106 := (r_plt hl h_v104 h_v105 (of_decide_eq_true rfl))
  have e_v106 : (v106 = 1 ↔ sv v104 < sv v105) := e_plt h_v104 h_v105 (of_decide_eq_true rfl)
  have h_v107 : R 1 0 4611686018158952441 4611686018695823359 v107 v107 := (r_psel hl h_v106 h_v105 h_v104 (of_decide_eq_true rfl))
  have e_v107 : v107 = if v106 = 1 then v105 else v104 := e_psel h_v106 h_v105 h_v104 (of_decide_eq_true rfl)
  have h_v108 : R 1 0 4611686019270702759 4611686019270702759 v108 v108 := (r_c hl 4611686019270702759 (of_decide_eq_true rfl))
  have e_v108 : sv v108 = (843314855) := e_c 4611686019270702759 (843314855) (of_decide_eq_true rfl)
  have h_v109 : R 1 0 0 1 v109 v109 := (r_plt hl h_v108 h_v1 (of_decide_eq_true rfl))
  have e_v109 : (v109 = 1 ↔ sv v108 < sv v1) := e_plt h_v108 h_v1 (of_decide_eq_true rfl)
  have h_v110 : R 1 0 4611686018158952441 4611686018695823359 v110 v110 := (r_psel hl h_v109 h_v105 h_v107 (of_decide_eq_true rfl))
  have e_v110 : v110 = if v109 = 1 then v105 else v107 := e_psel h_v109 h_v105 h_v107 (of_decide_eq_true rfl)
  have h_v112 : R 1 0 4611686018158952449 4611686018695823367 v112 v112 := (r_sub hl (r_add hl h_v31 h_t0_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v112 : sv v112 = sv v31 + sv t0.2 := e_add h_v31 h_t0_2 (of_decide_eq_true rfl)
  have h_v113 : R 1 0 0 1 v113 v113 := (r_plt hl h_v112 h_v33 (of_decide_eq_true rfl))
  have e_v113 : (v113 = 1 ↔ sv v112 < sv v33) := e_plt h_v112 h_v33 (of_decide_eq_true rfl)
  have h_v114 : R 1 0 4611686018158952449 4611686018695823367 v114 v114 := (r_psel hl h_v113 h_v112 h_v33 (of_decide_eq_true rfl))
  have e_v114 : v114 = if v113 = 1 then v112 else v33 := e_psel h_v113 h_v112 h_v33 (of_decide_eq_true rfl)
  have h_v115 : R 1 0 4611686018427387905 4611686018427387905 v115 v115 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have e_v115 : sv v115 = (1) := e_c 4611686018427387905 (1) (of_decide_eq_true rfl)
  have h_v116 : R 1 0 0 1 v116 v116 := (r_plt hl h_v0 h_v115 (of_decide_eq_true rfl))
  clear h_v1 h_t0_2 h_t1_2 h_v104 h_v106 h_v107 h_v109 h_v112 h_v113
  have e_v116 : (v116 = 1 ↔ sv v0 < sv v115) := e_plt h_v0 h_v115 (of_decide_eq_true rfl)
  have h_v117 : R 1 0 4611686018158952449 4611686018695823367 v117 v117 := (r_psel hl h_v116 h_v33 h_v114 (of_decide_eq_true rfl))
  have e_v117 : v117 = if v116 = 1 then v33 else v114 := e_psel h_v116 h_v33 h_v114 (of_decide_eq_true rfl)
  have h_v118 : R 1 0 4611686018427387904 4611686052787126264 v118 v118 := (r_add hl (r_pshr1 hl h_v3) h_H61r (of_decide_eq_true rfl))
  have e_v118 : sv v118 = sv v3 / 2 := e_halfF h_v3
  have h_v119 : R 1 0 0 1 v119 v119 := (r_plt hl h_v19 h_v118 (of_decide_eq_true rfl))
  have e_v119 : (v119 = 1 ↔ sv v19 < sv v118) := e_plt h_v19 h_v118 (of_decide_eq_true rfl)
  have h_v120 : R 1 0 0 1 v120 v120 := (r_land hl h_v46 h_v119 (of_decide_eq_true rfl))
  have e_v120 : (v120 = 1 ↔ v46 = 1 ∧ v119 = 1) := e_land h_v46 h_v119 (of_decide_eq_true rfl)
  have h_v122 : R 1 0 4611686018158952441 4611686018695823359 v122 v122 := (r_sub hl (r_add hl h_v28 h_t43_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v122 : sv v122 = sv v28 + sv t43.2 := e_add h_v28 h_t43_2 (of_decide_eq_true rfl)
  have h_v123 : R 1 0 0 1 v123 v123 := (r_plt hl h_v122 h_v105 (of_decide_eq_true rfl))
  have e_v123 : (v123 = 1 ↔ sv v122 < sv v105) := e_plt h_v122 h_v105 (of_decide_eq_true rfl)
  have h_v124 : R 1 0 4611686018158952441 4611686018695823359 v124 v124 := (r_psel hl h_v123 h_v105 h_v122 (of_decide_eq_true rfl))
  have e_v124 : v124 = if v123 = 1 then v105 else v122 := e_psel h_v123 h_v105 h_v122 (of_decide_eq_true rfl)
  have h_v125 : R 1 0 0 1 v125 v125 := (r_plt hl h_v108 h_v43 (of_decide_eq_true rfl))
  have e_v125 : (v125 = 1 ↔ sv v108 < sv v43) := e_plt h_v108 h_v43 (of_decide_eq_true rfl)
  have h_v126 : R 1 0 4611686018158952441 4611686018695823359 v126 v126 := (r_psel hl h_v125 h_v105 h_v124 (of_decide_eq_true rfl))
  have e_v126 : v126 = if v125 = 1 then v105 else v124 := e_psel h_v125 h_v105 h_v124 (of_decide_eq_true rfl)
  have h_t118_1 : R 1 0 4611686018427387904 4611686018695823363 t118.1 t118.1 := r_sc1 hl h_v118 (of_decide_eq_true rfl)
  have h_t118_2 : R 1 0 4611686018158952445 4611686018695823363 t118.2 t118.2 := r_sc2 hl h_v118 (of_decide_eq_true rfl)
  have e_t118_1 : sv t118.1 = (sc28pS (scArg v118)).1 := e_sc1 h_v118 (of_decide_eq_true rfl)
  have e_t118_2 : sv t118.2 = (sc28pS (scArg v118)).2 := e_sc2 h_v118 (of_decide_eq_true rfl)
  have h_v134 : R 1 0 0 1 v134 v134 := (r_plt hl h_t118_1 h_t43_1 (of_decide_eq_true rfl))
  have e_v134 : (v134 = 1 ↔ sv t118.1 < sv t43.1) := e_plt h_t118_1 h_t43_1 (of_decide_eq_true rfl)
  clear h_v0 h_v3 h_t43_2 h_v114 h_v116 h_v119 h_v122 h_v123 h_v124 h_v125 h_t118_2 e_t118_2
  have h_v135 : R 1 0 4611686018427387904 4611686018695823363 v135 v135 := (r_psel hl h_v134 h_t118_1 h_t43_1 (of_decide_eq_true rfl))
  have e_v135 : v135 = if v134 = 1 then t118.1 else t43.1 := e_psel h_v134 h_t118_1 h_t43_1 (of_decide_eq_true rfl)
  have h_v136 : R 1 0 4611686018427387900 4611686018695823359 v136 v136 := (r_sub hl (r_add hl h_v28 h_v135 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v136 : sv v136 = sv v28 + sv v135 := e_add h_v28 h_v135 (of_decide_eq_true rfl)
  have h_v137 : R 1 0 4611686018427387904 4611686018695823363 v137 v137 := (r_psel hl h_v134 h_t43_1 h_t118_1 (of_decide_eq_true rfl))
  have e_v137 : v137 = if v134 = 1 then t43.1 else t118.1 := e_psel h_v134 h_t43_1 h_t118_1 (of_decide_eq_true rfl)
  have h_v138 : R 1 0 4611686018427387908 4611686018695823367 v138 v138 := (r_sub hl (r_add hl h_v31 h_v137 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v138 : sv v138 = sv v31 + sv v137 := e_add h_v31 h_v137 (of_decide_eq_true rfl)
  have h_v139 : R 1 0 0 1 v139 v139 := (r_plt hl h_v138 h_v33 (of_decide_eq_true rfl))
  have e_v139 : (v139 = 1 ↔ sv v138 < sv v33) := e_plt h_v138 h_v33 (of_decide_eq_true rfl)
  have h_v140 : R 1 0 4611686018427387908 4611686018695823367 v140 v140 := (r_psel hl h_v139 h_v138 h_v33 (of_decide_eq_true rfl))
  have e_v140 : v140 = if v139 = 1 then v138 else v33 := e_psel h_v139 h_v138 h_v33 (of_decide_eq_true rfl)
  have h_v141 : R 1 0 0 1 v141 v141 := (r_plt hl h_v118 h_v36 (of_decide_eq_true rfl))
  have e_v141 : (v141 = 1 ↔ sv v118 < sv v36) := e_plt h_v118 h_v36 (of_decide_eq_true rfl)
  have h_v142 : R 1 0 0 1 v142 v142 := (r_land hl h_v58 h_v141 (of_decide_eq_true rfl))
  have e_v142 : (v142 = 1 ↔ v58 = 1 ∧ v141 = 1) := e_land h_v58 h_v141 (of_decide_eq_true rfl)
  have h_v143 : R 1 0 4611686018427387908 4611686018695823367 v143 v143 := (r_psel hl h_v142 h_v33 h_v140 (of_decide_eq_true rfl))
  have e_v143 : v143 = if v142 = 1 then v33 else v140 := e_psel h_v142 h_v33 h_v140 (of_decide_eq_true rfl)
  have h_v144 : R 1 0 0 1 v144 v144 := (r_plt hl h_v110 h_v61 (of_decide_eq_true rfl))
  have e_v144 : (v144 = 1 ↔ sv v110 < sv v61) := e_plt h_v110 h_v61 (of_decide_eq_true rfl)
  have h_v145 : R 1 0 0 1 v145 v145 := (r_sub hl (r_O hl) h_v144 (of_decide_eq_true rfl))
  have e_v145 : (v145 = 1 ↔ ¬v144 = 1) := e_not h_v144 (of_decide_eq_true rfl)
  have h_v146 : R 1 0 0 1 v146 v146 := (r_plt hl h_v61 h_v117 (of_decide_eq_true rfl))
  have e_v146 : (v146 = 1 ↔ sv v61 < sv v117) := e_plt h_v61 h_v117 (of_decide_eq_true rfl)
  have h_v147 : R 1 0 0 1 v147 v147 := (r_sub hl (r_O hl) h_v146 (of_decide_eq_true rfl))
  clear h_v134 h_v135 h_v137 h_v138 h_v139 h_v140 h_v141 h_v142
  have e_v147 : (v147 = 1 ↔ ¬v146 = 1) := e_not h_v146 (of_decide_eq_true rfl)
  have h_v148 : R 1 0 0 1 v148 v148 := (r_land hl h_v144 h_v147 (of_decide_eq_true rfl))
  have e_v148 : (v148 = 1 ↔ v144 = 1 ∧ v147 = 1) := e_land h_v144 h_v147 (of_decide_eq_true rfl)
  have h_v149 : R 1 0 0 1 v149 v149 := (r_land hl h_v144 h_v146 (of_decide_eq_true rfl))
  have e_v149 : (v149 = 1 ↔ v144 = 1 ∧ v146 = 1) := e_land h_v144 h_v146 (of_decide_eq_true rfl)
  have h_v150 : R 1 0 0 1 v150 v150 := (r_plt hl h_v136 h_v61 (of_decide_eq_true rfl))
  have e_v150 : (v150 = 1 ↔ sv v136 < sv v61) := e_plt h_v136 h_v61 (of_decide_eq_true rfl)
  have h_v152 : R 1 0 0 1 v152 v152 := (r_plt hl h_v61 h_v143 (of_decide_eq_true rfl))
  have e_v152 : (v152 = 1 ↔ sv v61 < sv v143) := e_plt h_v61 h_v143 (of_decide_eq_true rfl)
  have h_v153 : R 1 0 0 1 v153 v153 := (r_sub hl (r_O hl) h_v152 (of_decide_eq_true rfl))
  have e_v153 : (v153 = 1 ↔ ¬v152 = 1) := e_not h_v152 (of_decide_eq_true rfl)
  have h_v154 : R 1 0 0 1 v154 v154 := (r_land hl h_v150 h_v153 (of_decide_eq_true rfl))
  have e_v154 : (v154 = 1 ↔ v150 = 1 ∧ v153 = 1) := e_land h_v150 h_v153 (of_decide_eq_true rfl)
  have h_v155 : R 1 0 0 1 v155 v155 := (r_land hl h_v150 h_v152 (of_decide_eq_true rfl))
  have e_v155 : (v155 = 1 ↔ v150 = 1 ∧ v152 = 1) := e_land h_v150 h_v152 (of_decide_eq_true rfl)
  have h_v156 : R 1 0 0 1 v156 v156 := (r_land hl h_v149 h_v155 (of_decide_eq_true rfl))
  have e_v156 : (v156 = 1 ↔ v149 = 1 ∧ v155 = 1) := e_land h_v149 h_v155 (of_decide_eq_true rfl)
  have h_v157 : R 1 0 0 1 v157 v157 := (r_land hl h_v145 h_v155 (of_decide_eq_true rfl))
  have e_v157 : (v157 = 1 ↔ v145 = 1 ∧ v155 = 1) := e_land h_v145 h_v155 (of_decide_eq_true rfl)
  have h_v158 : R 1 0 0 1 v158 v158 := (r_lor hl h_v154 h_v157 (of_decide_eq_true rfl))
  have e_v158 : (v158 = 1 ↔ v154 = 1 ∨ v157 = 1) := e_lor h_v154 h_v157 (of_decide_eq_true rfl)
  have h_v159 : R 1 0 4611686018158952441 4611686018695823367 v159 v159 := (r_psel hl h_v158 h_v117 h_v110 (of_decide_eq_true rfl))
  have e_v159 : v159 = if v158 = 1 then v117 else v110 := e_psel h_v158 h_v117 h_v110 (of_decide_eq_true rfl)
  have h_v160 : R 1 0 0 1 v160 v160 := (r_sub hl (r_O hl) h_v154 (of_decide_eq_true rfl))
  have e_v160 : (v160 = 1 ↔ ¬v154 = 1) := e_not h_v154 (of_decide_eq_true rfl)
  clear h_v144 h_v146 h_v147 h_v150 h_v152 h_v153 h_v157 h_v158
  have h_v161 : R 1 0 0 1 v161 v161 := (r_land hl h_v149 h_v160 (of_decide_eq_true rfl))
  have e_v161 : (v161 = 1 ↔ v149 = 1 ∧ v160 = 1) := e_land h_v149 h_v160 (of_decide_eq_true rfl)
  have h_v162 : R 1 0 0 1 v162 v162 := (r_lor hl h_v148 h_v161 (of_decide_eq_true rfl))
  have e_v162 : (v162 = 1 ↔ v148 = 1 ∨ v161 = 1) := e_lor h_v148 h_v161 (of_decide_eq_true rfl)
  have h_v163 : R 1 0 4611686018427387900 4611686018695823367 v163 v163 := (r_psel hl h_v162 h_v143 h_v136 (of_decide_eq_true rfl))
  have e_v163 : v163 = if v162 = 1 then v143 else v136 := e_psel h_v162 h_v143 h_v136 (of_decide_eq_true rfl)
  have h_v164 : R 1 0 0 1 v164 v164 := (r_land hl h_v148 h_v155 (of_decide_eq_true rfl))
  have e_v164 : (v164 = 1 ↔ v148 = 1 ∧ v155 = 1) := e_land h_v148 h_v155 (of_decide_eq_true rfl)
  have h_v165 : R 1 0 0 1 v165 v165 := (r_lor hl h_v154 h_v164 (of_decide_eq_true rfl))
  have e_v165 : (v165 = 1 ↔ v154 = 1 ∨ v164 = 1) := e_lor h_v154 h_v164 (of_decide_eq_true rfl)
  have h_v166 : R 1 0 4611686018158952441 4611686018695823367 v166 v166 := (r_psel hl h_v165 h_v110 h_v117 (of_decide_eq_true rfl))
  have e_v166 : v166 = if v165 = 1 then v110 else v117 := e_psel h_v165 h_v110 h_v117 (of_decide_eq_true rfl)
  have h_v167 : R 1 0 0 1 v167 v167 := (r_land hl h_v149 h_v154 (of_decide_eq_true rfl))
  have e_v167 : (v167 = 1 ↔ v149 = 1 ∧ v154 = 1) := e_land h_v149 h_v154 (of_decide_eq_true rfl)
  have h_v168 : R 1 0 0 1 v168 v168 := (r_lor hl h_v148 h_v167 (of_decide_eq_true rfl))
  have e_v168 : (v168 = 1 ↔ v148 = 1 ∨ v167 = 1) := e_lor h_v148 h_v167 (of_decide_eq_true rfl)
  have h_v169 : R 1 0 4611686018427387900 4611686018695823367 v169 v169 := (r_psel hl h_v168 h_v136 h_v143 (of_decide_eq_true rfl))
  have e_v169 : v169 = if v168 = 1 then v136 else v143 := e_psel h_v168 h_v136 h_v143 (of_decide_eq_true rfl)
  have h_v170 : R 1 0 4539628420631363535 4683743616223412273 v170 v170 := (r_smx hl 29 h_v163 h_v159 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v170 : sv v170 = sv v163 * sv v159 := e_smx 29 h_v163 h_v159 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v171 : R 1 0 4611686018158952433 4611686018695823374 v171 v171 := (r_srdF hl h_v170 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v171 : sv v171 = sv v170 / 2 ^ 28 := e_srdF h_v170 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v172 : R 1 0 4539628420631363535 4683743616223412273 v172 v172 := (r_smx hl 29 h_v169 h_v166 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v172 : sv v172 = sv v169 * sv v166 := e_smx 29 h_v169 h_v166 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v173 : R 1 0 4611686018158952434 4611686018695823375 v173 v173 := (r_srdC hl h_v172 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  clear h_v143 h_v154 h_v155 h_v159 h_v160 h_v161 h_v162 h_v163 h_v164 h_v165 h_v166 h_v167 h_v168 h_v169 h_v170
  have e_v173 : sv v173 = -((-sv v172) / 2 ^ 28) := e_srdC h_v172 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v174 : R 1 0 4539628424926330879 4683743614075928569 v174 v174 := (r_smx hl 29 h_v136 h_v117 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl))
  have e_v174 : sv v174 = sv v136 * sv v117 := e_smx 29 h_v136 h_v117 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl)
  have h_v175 : R 1 0 4611686018158952449 4611686018695823365 v175 v175 := (r_srdF hl h_v174 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl))
  have e_v175 : sv v175 = sv v174 / 2 ^ 28 := e_srdF h_v174 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl)
  have h_v176 : R 1 0 4539628422778847239 4683743611928444929 v176 v176 := (r_smx hl 29 h_v136 h_v110 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl))
  have e_v176 : sv v176 = sv v136 * sv v110 := e_smx 29 h_v136 h_v110 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl)
  have h_v177 : R 1 0 4611686018158952443 4611686018695823359 v177 v177 := (r_srdC hl h_v176 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl))
  have e_v177 : sv v177 = -((-sv v176) / 2 ^ 28) := e_srdC h_v176 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl)
  have h_v178 : R 1 0 0 1 v178 v178 := (r_plt hl h_v171 h_v175 (of_decide_eq_true rfl))
  have e_v178 : (v178 = 1 ↔ sv v171 < sv v175) := e_plt h_v171 h_v175 (of_decide_eq_true rfl)
  have h_v179 : R 1 0 4611686018158952433 4611686018695823374 v179 v179 := (r_psel hl h_v178 h_v171 h_v175 (of_decide_eq_true rfl))
  have e_v179 : v179 = if v178 = 1 then v171 else v175 := e_psel h_v178 h_v171 h_v175 (of_decide_eq_true rfl)
  have h_v180 : R 1 0 0 1 v180 v180 := (r_plt hl h_v173 h_v177 (of_decide_eq_true rfl))
  have e_v180 : (v180 = 1 ↔ sv v173 < sv v177) := e_plt h_v173 h_v177 (of_decide_eq_true rfl)
  have h_v181 : R 1 0 4611686018158952434 4611686018695823375 v181 v181 := (r_psel hl h_v180 h_v177 h_v173 (of_decide_eq_true rfl))
  have e_v181 : v181 = if v180 = 1 then v177 else v173 := e_psel h_v180 h_v177 h_v173 (of_decide_eq_true rfl)
  have h_v182 : R 1 0 4611686018158952433 4611686018695823374 v182 v182 := (r_psel hl h_v156 h_v179 h_v171 (of_decide_eq_true rfl))
  have e_v182 : v182 = if v156 = 1 then v179 else v171 := e_psel h_v156 h_v179 h_v171 (of_decide_eq_true rfl)
  have h_v183 : R 1 0 4611686018158952434 4611686018695823375 v183 v183 := (r_psel hl h_v156 h_v181 h_v173 (of_decide_eq_true rfl))
  have e_v183 : v183 = if v156 = 1 then v181 else v173 := e_psel h_v156 h_v181 h_v173 (of_decide_eq_true rfl)
  have h_v184 : R 1 0 0 1 v184 v184 := (r_plt hl h_v61 h_v182 (of_decide_eq_true rfl))
  have e_v184 : (v184 = 1 ↔ sv v61 < sv v182) := e_plt h_v61 h_v182 (of_decide_eq_true rfl)
  have h_v185 : R 1 0 0 1 v185 v185 := (r_sub hl (r_O hl) h_v184 (of_decide_eq_true rfl))
  have e_v185 : (v185 = 1 ↔ ¬v184 = 1) := e_not h_v184 (of_decide_eq_true rfl)
  clear h_v136 h_v156 h_v171 h_v172 h_v173 h_v174 h_v175 h_v176 h_v177 h_v178 h_v179 h_v180 h_v181 h_v184
  have h_v186 : R 1 0 0 1 v186 v186 := (r_plt hl h_v126 h_v61 (of_decide_eq_true rfl))
  have e_v186 : (v186 = 1 ↔ sv v126 < sv v61) := e_plt h_v126 h_v61 (of_decide_eq_true rfl)
  have h_v187 : R 1 0 4611686018158952433 4611686018695823375 v187 v187 := (r_psel hl h_v186 h_v182 h_v183 (of_decide_eq_true rfl))
  have e_v187 : v187 = if v186 = 1 then v182 else v183 := e_psel h_v186 h_v182 h_v183 (of_decide_eq_true rfl)
  have h_v190 : R 1 0 4611686018158952449 4611686018695823367 v190 v190 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v126 (of_decide_eq_true rfl))
  have e_v190 : sv v190 = sv v61 - sv v126 := e_sub h_v61 h_v126 (of_decide_eq_true rfl)
  have h_v191 : R 1 0 4611686018158952441 4611686018695823367 v191 v191 := (r_psel hl h_v186 h_v190 h_v126 (of_decide_eq_true rfl))
  have e_v191 : v191 = if v186 = 1 then v190 else v126 := e_psel h_v186 h_v190 h_v126 (of_decide_eq_true rfl)
  have h_v192 : R 1 0 4611686018427387904 4611686019501129727 v192 v192 := (r1_hxa hb_H0 0 (of_decide_eq_true rfl))
  have e_v192 : sv v192 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 0 (of_decide_eq_true rfl)
  have h_v193 : R 1 0 0 1 v193 v193 := (r_sub hl (r_O hl) h_v186 (of_decide_eq_true rfl))
  have e_v193 : (v193 = 1 ↔ ¬v186 = 1) := e_not h_v186 (of_decide_eq_true rfl)
  have h_t192_1 : R 1 0 4611686018427387904 4611686018695823363 t192.1 t192.1 := r_sc1 hl h_v192 (of_decide_eq_true rfl)
  have h_t192_2 : R 1 0 4611686018158952445 4611686018695823363 t192.2 t192.2 := r_sc2 hl h_v192 (of_decide_eq_true rfl)
  have e_t192_1 : sv t192.1 = (sc28pS (scArg v192)).1 := e_sc1 h_v192 (of_decide_eq_true rfl)
  have e_t192_2 : sv t192.2 = (sc28pS (scArg v192)).2 := e_sc2 h_v192 (of_decide_eq_true rfl)
  have h_v195 : R 1 0 4611686018158952441 4611686018695823359 v195 v195 := (r_sub hl (r_add hl h_v28 h_t192_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v195 : sv v195 = sv v28 + sv t192.2 := e_add h_v28 h_t192_2 (of_decide_eq_true rfl)
  have h_v196 : R 1 0 0 1 v196 v196 := (r_plt hl h_v195 h_v105 (of_decide_eq_true rfl))
  have e_v196 : (v196 = 1 ↔ sv v195 < sv v105) := e_plt h_v195 h_v105 (of_decide_eq_true rfl)
  have h_v197 : R 1 0 4611686018158952441 4611686018695823359 v197 v197 := (r_psel hl h_v196 h_v105 h_v195 (of_decide_eq_true rfl))
  have e_v197 : v197 = if v196 = 1 then v105 else v195 := e_psel h_v196 h_v105 h_v195 (of_decide_eq_true rfl)
  have h_v198 : R 1 0 4611686018158952449 4611686018695823367 v198 v198 := (r_sub hl (r_add hl h_v31 h_t192_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v198 : sv v198 = sv v31 + sv t192.2 := e_add h_v31 h_t192_2 (of_decide_eq_true rfl)
  have h_v199 : R 1 0 0 1 v199 v199 := (r_plt hl h_v198 h_v33 (of_decide_eq_true rfl))
  clear h_v182 h_v183 h_v190 h_t192_2 h_v195 h_v196
  have e_v199 : (v199 = 1 ↔ sv v198 < sv v33) := e_plt h_v198 h_v33 (of_decide_eq_true rfl)
  have h_v200 : R 1 0 4611686018158952449 4611686018695823367 v200 v200 := (r_psel hl h_v199 h_v198 h_v33 (of_decide_eq_true rfl))
  have e_v200 : v200 = if v199 = 1 then v198 else v33 := e_psel h_v199 h_v198 h_v33 (of_decide_eq_true rfl)
  have h_v202 : R 1 0 4611686018427387908 4611686018695823367 v202 v202 := (r_sub hl (r_add hl h_v31 h_t192_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v202 : sv v202 = sv v31 + sv t192.1 := e_add h_v31 h_t192_1 (of_decide_eq_true rfl)
  have h_v203 : R 1 0 0 1 v203 v203 := (r_plt hl h_v202 h_v33 (of_decide_eq_true rfl))
  have e_v203 : (v203 = 1 ↔ sv v202 < sv v33) := e_plt h_v202 h_v33 (of_decide_eq_true rfl)
  have h_v204 : R 1 0 4611686018427387908 4611686018695823367 v204 v204 := (r_psel hl h_v203 h_v202 h_v33 (of_decide_eq_true rfl))
  have e_v204 : v204 = if v203 = 1 then v202 else v33 := e_psel h_v203 h_v202 h_v33 (of_decide_eq_true rfl)
  have h_v205 : R 1 0 4611686018427387900 4611686018695823359 v205 v205 := (r_sub hl (r_add hl h_v28 h_t192_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v205 : sv v205 = sv v28 + sv t192.1 := e_add h_v28 h_t192_1 (of_decide_eq_true rfl)
  have h_v206 : R 1 0 4611686018158952441 4611686018695823367 v206 v206 := (r_psel hl h_v193 h_v197 h_v200 (of_decide_eq_true rfl))
  have e_v206 : v206 = if v193 = 1 then v197 else v200 := e_psel h_v193 h_v197 h_v200 (of_decide_eq_true rfl)
  have h_v207 : R 1 0 4611686018427387900 4611686018695823367 v207 v207 := (r_psel hl h_v193 h_v204 h_v205 (of_decide_eq_true rfl))
  have e_v207 : v207 = if v193 = 1 then v204 else v205 := e_psel h_v193 h_v204 h_v205 (of_decide_eq_true rfl)
  have h_v208 : R 1 0 4539628418483879831 4683743618370895977 v208 v208 := (r_smx hl 29 h_v187 h_v207 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v208 : sv v208 = sv v187 * sv v207 := e_smx 29 h_v187 h_v207 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v209 : R 1 0 4539628420631363535 4683743616223412273 v209 v209 := (r_smx hl 29 h_v206 h_v191 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v209 : sv v209 = sv v206 * sv v191 := e_smx 29 h_v206 h_v191 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v210 : R 1 0 0 1 v210 v210 := (r_plt hl h_v209 h_v208 (of_decide_eq_true rfl))
  have e_v210 : (v210 = 1 ↔ sv v209 < sv v208) := e_plt h_v209 h_v208 (of_decide_eq_true rfl)
  have h_v211 : R 1 0 0 1 v211 v211 := (r_sub hl (r_O hl) h_v210 (of_decide_eq_true rfl))
  have e_v211 : (v211 = 1 ↔ ¬v210 = 1) := e_not h_v210 (of_decide_eq_true rfl)
  have h_v212 : R 1 0 0 1 v212 v212 := (r_plt hl h_v208 h_v209 (of_decide_eq_true rfl))
  have e_v212 : (v212 = 1 ↔ sv v208 < sv v209) := e_plt h_v208 h_v209 (of_decide_eq_true rfl)
  clear h_v187 h_v191 h_t192_1 h_v198 h_v199 h_v200 h_v202 h_v203 h_v204 h_v205 h_v206 h_v207 h_v208 h_v209 h_v210
  have h_v213 : R 1 0 0 1 v213 v213 := (r_sub hl (r_O hl) h_v212 (of_decide_eq_true rfl))
  have e_v213 : (v213 = 1 ↔ ¬v212 = 1) := e_not h_v212 (of_decide_eq_true rfl)
  have h_v214 : R 1 0 0 1 v214 v214 := (r_plt hl h_v61 h_v192 (of_decide_eq_true rfl))
  have e_v214 : (v214 = 1 ↔ sv v61 < sv v192) := e_plt h_v61 h_v192 (of_decide_eq_true rfl)
  have h_v215 : R 1 0 0 1 v215 v215 := (r_sub hl (r_O hl) h_v214 (of_decide_eq_true rfl))
  have e_v215 : (v215 = 1 ↔ ¬v214 = 1) := e_not h_v214 (of_decide_eq_true rfl)
  have h_v216 : R 1 0 4611686018849045332 4611686018849045332 v216 v216 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  have e_v216 : sv v216 = (421657428) := e_c 4611686018849045332 (421657428) (of_decide_eq_true rfl)
  have h_v217 : R 1 0 0 1 v217 v217 := (r_plt hl h_v216 h_v192 (of_decide_eq_true rfl))
  have e_v217 : (v217 = 1 ↔ sv v216 < sv v192) := e_plt h_v216 h_v192 (of_decide_eq_true rfl)
  have h_v218 : R 1 0 0 1 v218 v218 := (r_sub hl (r_O hl) h_v217 (of_decide_eq_true rfl))
  have e_v218 : (v218 = 1 ↔ ¬v217 = 1) := e_not h_v217 (of_decide_eq_true rfl)
  have h_v219 : R 1 0 0 1 v219 v219 := (r_plt hl h_v19 h_v197 (of_decide_eq_true rfl))
  have e_v219 : (v219 = 1 ↔ sv v19 < sv v197) := e_plt h_v19 h_v197 (of_decide_eq_true rfl)
  have h_v220 : R 1 0 0 1 v220 v220 := (r_land hl h_v211 h_v219 (of_decide_eq_true rfl))
  have e_v220 : (v220 = 1 ↔ v211 = 1 ∧ v219 = 1) := e_land h_v211 h_v219 (of_decide_eq_true rfl)
  have h_v221 : R 1 0 0 1 v221 v221 := (r_land hl h_v218 h_v220 (of_decide_eq_true rfl))
  have e_v221 : (v221 = 1 ↔ v218 = 1 ∧ v220 = 1) := e_land h_v218 h_v220 (of_decide_eq_true rfl)
  have h_v222 : R 1 0 0 1 v222 v222 := (r_lor hl h_v215 h_v221 (of_decide_eq_true rfl))
  have e_v222 : (v222 = 1 ↔ v215 = 1 ∨ v221 = 1) := e_lor h_v215 h_v221 (of_decide_eq_true rfl)
  have h_v223 : R 1 0 4611686018849045333 4611686018849045333 v223 v223 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have e_v223 : sv v223 = (421657429) := e_c 4611686018849045333 (421657429) (of_decide_eq_true rfl)
  have h_v224 : R 1 0 0 1 v224 v224 := (r_plt hl h_v192 h_v223 (of_decide_eq_true rfl))
  have e_v224 : (v224 = 1 ↔ sv v192 < sv v223) := e_plt h_v192 h_v223 (of_decide_eq_true rfl)
  have h_v225 : R 1 0 0 1 v225 v225 := (r_sub hl (r_O hl) h_v224 (of_decide_eq_true rfl))
  clear h_v197 h_v211 h_v212 h_v214 h_v215 h_v217 h_v218 h_v219 h_v220 h_v221
  have e_v225 : (v225 = 1 ↔ ¬v224 = 1) := e_not h_v224 (of_decide_eq_true rfl)
  have h_v226 : R 1 0 0 1 v226 v226 := (r_lor hl h_v213 h_v225 (of_decide_eq_true rfl))
  have e_v226 : (v226 = 1 ↔ v213 = 1 ∨ v225 = 1) := e_lor h_v213 h_v225 (of_decide_eq_true rfl)
  have h_v227 : R 1 0 0 1 v227 v227 := (r_land hl h_v193 h_v222 (of_decide_eq_true rfl))
  have e_v227 : (v227 = 1 ↔ v193 = 1 ∧ v222 = 1) := e_land h_v193 h_v222 (of_decide_eq_true rfl)
  have h_v228 : R 1 0 0 1 v228 v228 := (r_land hl h_v186 h_v226 (of_decide_eq_true rfl))
  have e_v228 : (v228 = 1 ↔ v186 = 1 ∧ v226 = 1) := e_land h_v186 h_v226 (of_decide_eq_true rfl)
  have h_v229 : R 1 0 0 1 v229 v229 := (r_lor hl h_v227 h_v228 (of_decide_eq_true rfl))
  have e_v229 : (v229 = 1 ↔ v227 = 1 ∨ v228 = 1) := e_lor h_v227 h_v228 (of_decide_eq_true rfl)
  have h_v230 : R 1 0 4611686017353646081 4611686018427387904 v230 v230 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v192 (of_decide_eq_true rfl))
  have e_v230 : sv v230 = sv v61 - sv v192 := e_sub h_v61 h_v192 (of_decide_eq_true rfl)
  have h_v231 : R 1 0 4611686017353646081 4611686019501129727 v231 v231 := (r_psel hl h_v186 h_v230 h_v192 (of_decide_eq_true rfl))
  have e_v231 : v231 = if v186 = 1 then v230 else v192 := e_psel h_v186 h_v230 h_v192 (of_decide_eq_true rfl)
  have h_v232 : R 1 0 4611686018005730475 4611686018005730475 v232 v232 := (r_c hl 4611686018005730475 (of_decide_eq_true rfl))
  have e_v232 : sv v232 = (-421657429) := e_c 4611686018005730475 (-421657429) (of_decide_eq_true rfl)
  have h_v233 : R 1 0 4611686017353646081 4611686019501129727 v233 v233 := (r_psel hl h_v229 h_v231 h_v232 (of_decide_eq_true rfl))
  have e_v233 : v233 = if v229 = 1 then v231 else v232 := e_psel h_v229 h_v231 h_v232 (of_decide_eq_true rfl)
  have h_v275 : R 1 0 4611686017353646081 4611686019501129727 v275 v275 := (r_psel hl h_v185 h_v232 h_v233 (of_decide_eq_true rfl))
  have e_v275 : v275 = if v185 = 1 then v232 else v233 := e_psel h_v185 h_v232 h_v233 (of_decide_eq_true rfl)
  have h_v277 : R 1 0 4611686018427387904 4611686052787126264 v277 v277 := (r_add hl (r_pshr1 hl (r_add hl h_v2 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v277 : sv v277 = (sv v2 + 1) / 2 := e_halfC h_v2 (of_decide_eq_true rfl)
  have h_v278 : R 1 0 0 1 v278 v278 := (r_plt hl h_v9 h_v277 (of_decide_eq_true rfl))
  have e_v278 : (v278 = 1 ↔ sv v9 < sv v277) := e_plt h_v9 h_v277 (of_decide_eq_true rfl)
  have h_v279 : R 1 0 0 1 v279 v279 := (r_sub hl (r_O hl) h_v278 (of_decide_eq_true rfl))
  have e_v279 : (v279 = 1 ↔ ¬v278 = 1) := e_not h_v278 (of_decide_eq_true rfl)
  clear h_v2 h_v185 h_v192 h_v193 h_v213 h_v222 h_v224 h_v225 h_v226 h_v227 h_v228 h_v229 h_v230 h_v231 h_v233 h_v278
  have h_v280 : R 1 0 0 1 v280 v280 := (r_land hl h_v44 h_v279 (of_decide_eq_true rfl))
  have e_v280 : (v280 = 1 ↔ v44 = 1 ∧ v279 = 1) := e_land h_v44 h_v279 (of_decide_eq_true rfl)
  have h_v288 : R 1 0 4611686018158952449 4611686018695823367 v288 v288 := (r_sub hl (r_add hl h_v31 h_t42_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v288 : sv v288 = sv v31 + sv t42.2 := e_add h_v31 h_t42_2 (of_decide_eq_true rfl)
  have h_v289 : R 1 0 0 1 v289 v289 := (r_plt hl h_v288 h_v33 (of_decide_eq_true rfl))
  have e_v289 : (v289 = 1 ↔ sv v288 < sv v33) := e_plt h_v288 h_v33 (of_decide_eq_true rfl)
  have h_v290 : R 1 0 4611686018158952449 4611686018695823367 v290 v290 := (r_psel hl h_v289 h_v288 h_v33 (of_decide_eq_true rfl))
  have e_v290 : v290 = if v289 = 1 then v288 else v33 := e_psel h_v289 h_v288 h_v33 (of_decide_eq_true rfl)
  have h_v291 : R 1 0 0 1 v291 v291 := (r_plt hl h_v42 h_v115 (of_decide_eq_true rfl))
  have e_v291 : (v291 = 1 ↔ sv v42 < sv v115) := e_plt h_v42 h_v115 (of_decide_eq_true rfl)
  have h_v292 : R 1 0 4611686018158952449 4611686018695823367 v292 v292 := (r_psel hl h_v291 h_v33 h_v290 (of_decide_eq_true rfl))
  have e_v292 : v292 = if v291 = 1 then v33 else v290 := e_psel h_v291 h_v33 h_v290 (of_decide_eq_true rfl)
  have h_t277_1 : R 1 0 4611686018427387904 4611686018695823363 t277.1 t277.1 := r_sc1 hl h_v277 (of_decide_eq_true rfl)
  have h_t277_2 : R 1 0 4611686018158952445 4611686018695823363 t277.2 t277.2 := r_sc2 hl h_v277 (of_decide_eq_true rfl)
  have e_t277_1 : sv t277.1 = (sc28pS (scArg v277)).1 := e_sc1 h_v277 (of_decide_eq_true rfl)
  have e_t277_2 : sv t277.2 = (sc28pS (scArg v277)).2 := e_sc2 h_v277 (of_decide_eq_true rfl)
  have h_v294 : R 1 0 0 1 v294 v294 := (r_plt hl h_t42_1 h_t277_1 (of_decide_eq_true rfl))
  have e_v294 : (v294 = 1 ↔ sv t42.1 < sv t277.1) := e_plt h_t42_1 h_t277_1 (of_decide_eq_true rfl)
  have h_v295 : R 1 0 4611686018427387904 4611686018695823363 v295 v295 := (r_psel hl h_v294 h_t42_1 h_t277_1 (of_decide_eq_true rfl))
  have e_v295 : v295 = if v294 = 1 then t42.1 else t277.1 := e_psel h_v294 h_t42_1 h_t277_1 (of_decide_eq_true rfl)
  have h_v296 : R 1 0 4611686018427387900 4611686018695823359 v296 v296 := (r_sub hl (r_add hl h_v28 h_v295 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v296 : sv v296 = sv v28 + sv v295 := e_add h_v28 h_v295 (of_decide_eq_true rfl)
  have h_v297 : R 1 0 4611686018427387904 4611686018695823363 v297 v297 := (r_psel hl h_v294 h_t277_1 h_t42_1 (of_decide_eq_true rfl))
  have e_v297 : v297 = if v294 = 1 then t277.1 else t42.1 := e_psel h_v294 h_t277_1 h_t42_1 (of_decide_eq_true rfl)
  have h_v298 : R 1 0 4611686018427387908 4611686018695823367 v298 v298 := (r_sub hl (r_add hl h_v31 h_v297 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v44 h_t42_2 h_v279 h_v288 h_v289 h_v290 h_v291 h_t277_1 h_t277_2 e_t277_2 h_v294 h_v295
  have e_v298 : sv v298 = sv v31 + sv v297 := e_add h_v31 h_v297 (of_decide_eq_true rfl)
  have h_v299 : R 1 0 0 1 v299 v299 := (r_plt hl h_v298 h_v33 (of_decide_eq_true rfl))
  have e_v299 : (v299 = 1 ↔ sv v298 < sv v33) := e_plt h_v298 h_v33 (of_decide_eq_true rfl)
  have h_v300 : R 1 0 4611686018427387908 4611686018695823367 v300 v300 := (r_psel hl h_v299 h_v298 h_v33 (of_decide_eq_true rfl))
  have e_v300 : v300 = if v299 = 1 then v298 else v33 := e_psel h_v299 h_v298 h_v33 (of_decide_eq_true rfl)
  have h_v301 : R 1 0 0 1 v301 v301 := (r_plt hl h_v38 h_v277 (of_decide_eq_true rfl))
  have e_v301 : (v301 = 1 ↔ sv v38 < sv v277) := e_plt h_v38 h_v277 (of_decide_eq_true rfl)
  have h_v302 : R 1 0 0 1 v302 v302 := (r_land hl h_v57 h_v301 (of_decide_eq_true rfl))
  have e_v302 : (v302 = 1 ↔ v57 = 1 ∧ v301 = 1) := e_land h_v57 h_v301 (of_decide_eq_true rfl)
  have h_v303 : R 1 0 4611686018427387908 4611686018695823367 v303 v303 := (r_psel hl h_v302 h_v33 h_v300 (of_decide_eq_true rfl))
  have e_v303 : v303 = if v302 = 1 then v33 else v300 := e_psel h_v302 h_v33 h_v300 (of_decide_eq_true rfl)
  have h_v304 : R 1 0 0 1 v304 v304 := (r_plt hl h_v296 h_v61 (of_decide_eq_true rfl))
  have e_v304 : (v304 = 1 ↔ sv v296 < sv v61) := e_plt h_v296 h_v61 (of_decide_eq_true rfl)
  have h_v306 : R 1 0 0 1 v306 v306 := (r_plt hl h_v61 h_v303 (of_decide_eq_true rfl))
  have e_v306 : (v306 = 1 ↔ sv v61 < sv v303) := e_plt h_v61 h_v303 (of_decide_eq_true rfl)
  have h_v307 : R 1 0 0 1 v307 v307 := (r_sub hl (r_O hl) h_v306 (of_decide_eq_true rfl))
  have e_v307 : (v307 = 1 ↔ ¬v306 = 1) := e_not h_v306 (of_decide_eq_true rfl)
  have h_v308 : R 1 0 0 1 v308 v308 := (r_land hl h_v304 h_v307 (of_decide_eq_true rfl))
  have e_v308 : (v308 = 1 ↔ v304 = 1 ∧ v307 = 1) := e_land h_v304 h_v307 (of_decide_eq_true rfl)
  have h_v309 : R 1 0 0 1 v309 v309 := (r_land hl h_v304 h_v306 (of_decide_eq_true rfl))
  have e_v309 : (v309 = 1 ↔ v304 = 1 ∧ v306 = 1) := e_land h_v304 h_v306 (of_decide_eq_true rfl)
  have h_v310 : R 1 0 0 1 v310 v310 := (r_land hl h_v149 h_v309 (of_decide_eq_true rfl))
  have e_v310 : (v310 = 1 ↔ v149 = 1 ∧ v309 = 1) := e_land h_v149 h_v309 (of_decide_eq_true rfl)
  have h_v311 : R 1 0 0 1 v311 v311 := (r_land hl h_v145 h_v309 (of_decide_eq_true rfl))
  have e_v311 : (v311 = 1 ↔ v145 = 1 ∧ v309 = 1) := e_land h_v145 h_v309 (of_decide_eq_true rfl)
  clear h_v57 h_v297 h_v298 h_v299 h_v300 h_v301 h_v302 h_v304 h_v306 h_v307
  have h_v312 : R 1 0 0 1 v312 v312 := (r_lor hl h_v308 h_v311 (of_decide_eq_true rfl))
  have e_v312 : (v312 = 1 ↔ v308 = 1 ∨ v311 = 1) := e_lor h_v308 h_v311 (of_decide_eq_true rfl)
  have h_v313 : R 1 0 4611686018158952441 4611686018695823367 v313 v313 := (r_psel hl h_v312 h_v117 h_v110 (of_decide_eq_true rfl))
  have e_v313 : v313 = if v312 = 1 then v117 else v110 := e_psel h_v312 h_v117 h_v110 (of_decide_eq_true rfl)
  have h_v314 : R 1 0 0 1 v314 v314 := (r_sub hl (r_O hl) h_v308 (of_decide_eq_true rfl))
  have e_v314 : (v314 = 1 ↔ ¬v308 = 1) := e_not h_v308 (of_decide_eq_true rfl)
  have h_v315 : R 1 0 0 1 v315 v315 := (r_land hl h_v149 h_v314 (of_decide_eq_true rfl))
  have e_v315 : (v315 = 1 ↔ v149 = 1 ∧ v314 = 1) := e_land h_v149 h_v314 (of_decide_eq_true rfl)
  have h_v316 : R 1 0 0 1 v316 v316 := (r_lor hl h_v148 h_v315 (of_decide_eq_true rfl))
  have e_v316 : (v316 = 1 ↔ v148 = 1 ∨ v315 = 1) := e_lor h_v148 h_v315 (of_decide_eq_true rfl)
  have h_v317 : R 1 0 4611686018427387900 4611686018695823367 v317 v317 := (r_psel hl h_v316 h_v303 h_v296 (of_decide_eq_true rfl))
  have e_v317 : v317 = if v316 = 1 then v303 else v296 := e_psel h_v316 h_v303 h_v296 (of_decide_eq_true rfl)
  have h_v318 : R 1 0 0 1 v318 v318 := (r_land hl h_v148 h_v309 (of_decide_eq_true rfl))
  have e_v318 : (v318 = 1 ↔ v148 = 1 ∧ v309 = 1) := e_land h_v148 h_v309 (of_decide_eq_true rfl)
  have h_v319 : R 1 0 0 1 v319 v319 := (r_lor hl h_v308 h_v318 (of_decide_eq_true rfl))
  have e_v319 : (v319 = 1 ↔ v308 = 1 ∨ v318 = 1) := e_lor h_v308 h_v318 (of_decide_eq_true rfl)
  have h_v320 : R 1 0 4611686018158952441 4611686018695823367 v320 v320 := (r_psel hl h_v319 h_v110 h_v117 (of_decide_eq_true rfl))
  have e_v320 : v320 = if v319 = 1 then v110 else v117 := e_psel h_v319 h_v110 h_v117 (of_decide_eq_true rfl)
  have h_v321 : R 1 0 0 1 v321 v321 := (r_land hl h_v149 h_v308 (of_decide_eq_true rfl))
  have e_v321 : (v321 = 1 ↔ v149 = 1 ∧ v308 = 1) := e_land h_v149 h_v308 (of_decide_eq_true rfl)
  have h_v322 : R 1 0 0 1 v322 v322 := (r_lor hl h_v148 h_v321 (of_decide_eq_true rfl))
  have e_v322 : (v322 = 1 ↔ v148 = 1 ∨ v321 = 1) := e_lor h_v148 h_v321 (of_decide_eq_true rfl)
  have h_v323 : R 1 0 4611686018427387900 4611686018695823367 v323 v323 := (r_psel hl h_v322 h_v296 h_v303 (of_decide_eq_true rfl))
  have e_v323 : v323 = if v322 = 1 then v296 else v303 := e_psel h_v322 h_v296 h_v303 (of_decide_eq_true rfl)
  have h_v324 : R 1 0 4539628420631363535 4683743616223412273 v324 v324 := (r_smx hl 29 h_v317 h_v313 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  clear h_v303 h_v308 h_v309 h_v311 h_v312 h_v314 h_v315 h_v316 h_v318 h_v319 h_v321 h_v322
  have e_v324 : sv v324 = sv v317 * sv v313 := e_smx 29 h_v317 h_v313 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v325 : R 1 0 4611686018158952433 4611686018695823374 v325 v325 := (r_srdF hl h_v324 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v325 : sv v325 = sv v324 / 2 ^ 28 := e_srdF h_v324 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v326 : R 1 0 4539628420631363535 4683743616223412273 v326 v326 := (r_smx hl 29 h_v323 h_v320 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v326 : sv v326 = sv v323 * sv v320 := e_smx 29 h_v323 h_v320 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v327 : R 1 0 4611686018158952434 4611686018695823375 v327 v327 := (r_srdC hl h_v326 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v327 : sv v327 = -((-sv v326) / 2 ^ 28) := e_srdC h_v326 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v328 : R 1 0 4539628424926330879 4683743614075928569 v328 v328 := (r_smx hl 29 h_v296 h_v117 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl))
  have e_v328 : sv v328 = sv v296 * sv v117 := e_smx 29 h_v296 h_v117 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl)
  have h_v329 : R 1 0 4611686018158952449 4611686018695823365 v329 v329 := (r_srdF hl h_v328 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl))
  have e_v329 : sv v329 = sv v328 / 2 ^ 28 := e_srdF h_v328 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl)
  have h_v330 : R 1 0 4539628422778847239 4683743611928444929 v330 v330 := (r_smx hl 29 h_v296 h_v110 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl))
  have e_v330 : sv v330 = sv v296 * sv v110 := e_smx 29 h_v296 h_v110 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl)
  have h_v331 : R 1 0 4611686018158952443 4611686018695823359 v331 v331 := (r_srdC hl h_v330 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl))
  have e_v331 : sv v331 = -((-sv v330) / 2 ^ 28) := e_srdC h_v330 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl)
  have h_v332 : R 1 0 0 1 v332 v332 := (r_plt hl h_v325 h_v329 (of_decide_eq_true rfl))
  have e_v332 : (v332 = 1 ↔ sv v325 < sv v329) := e_plt h_v325 h_v329 (of_decide_eq_true rfl)
  have h_v333 : R 1 0 4611686018158952433 4611686018695823374 v333 v333 := (r_psel hl h_v332 h_v325 h_v329 (of_decide_eq_true rfl))
  have e_v333 : v333 = if v332 = 1 then v325 else v329 := e_psel h_v332 h_v325 h_v329 (of_decide_eq_true rfl)
  have h_v334 : R 1 0 0 1 v334 v334 := (r_plt hl h_v327 h_v331 (of_decide_eq_true rfl))
  have e_v334 : (v334 = 1 ↔ sv v327 < sv v331) := e_plt h_v327 h_v331 (of_decide_eq_true rfl)
  have h_v335 : R 1 0 4611686018158952434 4611686018695823375 v335 v335 := (r_psel hl h_v334 h_v331 h_v327 (of_decide_eq_true rfl))
  have e_v335 : v335 = if v334 = 1 then v331 else v327 := e_psel h_v334 h_v331 h_v327 (of_decide_eq_true rfl)
  have h_v336 : R 1 0 4611686018158952433 4611686018695823374 v336 v336 := (r_psel hl h_v310 h_v333 h_v325 (of_decide_eq_true rfl))
  have e_v336 : v336 = if v310 = 1 then v333 else v325 := e_psel h_v310 h_v333 h_v325 (of_decide_eq_true rfl)
  clear h_v296 h_v313 h_v317 h_v320 h_v323 h_v324 h_v325 h_v326 h_v328 h_v329 h_v330 h_v331 h_v332 h_v333 h_v334
  have h_v337 : R 1 0 4611686018158952434 4611686018695823375 v337 v337 := (r_psel hl h_v310 h_v335 h_v327 (of_decide_eq_true rfl))
  have e_v337 : v337 = if v310 = 1 then v335 else v327 := e_psel h_v310 h_v335 h_v327 (of_decide_eq_true rfl)
  have h_v338 : R 1 0 0 1 v338 v338 := (r_plt hl h_v61 h_v336 (of_decide_eq_true rfl))
  have e_v338 : (v338 = 1 ↔ sv v61 < sv v336) := e_plt h_v61 h_v336 (of_decide_eq_true rfl)
  have h_v339 : R 1 0 0 1 v339 v339 := (r_sub hl (r_O hl) h_v338 (of_decide_eq_true rfl))
  have e_v339 : (v339 = 1 ↔ ¬v338 = 1) := e_not h_v338 (of_decide_eq_true rfl)
  have h_v342 : R 1 0 0 1 v342 v342 := (r_plt hl h_v292 h_v61 (of_decide_eq_true rfl))
  have e_v342 : (v342 = 1 ↔ sv v292 < sv v61) := e_plt h_v292 h_v61 (of_decide_eq_true rfl)
  have h_v343 : R 1 0 4611686018158952433 4611686018695823375 v343 v343 := (r_psel hl h_v342 h_v337 h_v336 (of_decide_eq_true rfl))
  have e_v343 : v343 = if v342 = 1 then v337 else v336 := e_psel h_v342 h_v337 h_v336 (of_decide_eq_true rfl)
  have h_v385 : R 1 0 4611686018158952441 4611686018695823359 v385 v385 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v292 (of_decide_eq_true rfl))
  have e_v385 : sv v385 = sv v61 - sv v292 := e_sub h_v61 h_v292 (of_decide_eq_true rfl)
  have h_v386 : R 1 0 4611686018158952441 4611686018695823367 v386 v386 := (r_psel hl h_v342 h_v385 h_v292 (of_decide_eq_true rfl))
  have e_v386 : v386 = if v342 = 1 then v385 else v292 := e_psel h_v342 h_v385 h_v292 (of_decide_eq_true rfl)
  have h_v387 : R 1 0 4611686018427387904 4611686019501129727 v387 v387 := (r1_hxa hb_H0 32 (of_decide_eq_true rfl))
  have e_v387 : sv v387 = ((H0 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 32 (of_decide_eq_true rfl)
  have h_t387_1 : R 1 0 4611686018427387904 4611686018695823363 t387.1 t387.1 := r_sc1 hl h_v387 (of_decide_eq_true rfl)
  have h_t387_2 : R 1 0 4611686018158952445 4611686018695823363 t387.2 t387.2 := r_sc2 hl h_v387 (of_decide_eq_true rfl)
  have e_t387_1 : sv t387.1 = (sc28pS (scArg v387)).1 := e_sc1 h_v387 (of_decide_eq_true rfl)
  have e_t387_2 : sv t387.2 = (sc28pS (scArg v387)).2 := e_sc2 h_v387 (of_decide_eq_true rfl)
  have h_v389 : R 1 0 4611686018158952441 4611686018695823359 v389 v389 := (r_sub hl (r_add hl h_v28 h_t387_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v389 : sv v389 = sv v28 + sv t387.2 := e_add h_v28 h_t387_2 (of_decide_eq_true rfl)
  have h_v390 : R 1 0 0 1 v390 v390 := (r_plt hl h_v389 h_v105 (of_decide_eq_true rfl))
  have e_v390 : (v390 = 1 ↔ sv v389 < sv v105) := e_plt h_v389 h_v105 (of_decide_eq_true rfl)
  have h_v391 : R 1 0 4611686018158952441 4611686018695823359 v391 v391 := (r_psel hl h_v390 h_v105 h_v389 (of_decide_eq_true rfl))
  clear h_v310 h_v327 h_v335 h_v336 h_v337 h_v338 h_v385
  have e_v391 : v391 = if v390 = 1 then v105 else v389 := e_psel h_v390 h_v105 h_v389 (of_decide_eq_true rfl)
  have h_v392 : R 1 0 4611686018158952449 4611686018695823367 v392 v392 := (r_sub hl (r_add hl h_v31 h_t387_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v392 : sv v392 = sv v31 + sv t387.2 := e_add h_v31 h_t387_2 (of_decide_eq_true rfl)
  have h_v393 : R 1 0 0 1 v393 v393 := (r_plt hl h_v392 h_v33 (of_decide_eq_true rfl))
  have e_v393 : (v393 = 1 ↔ sv v392 < sv v33) := e_plt h_v392 h_v33 (of_decide_eq_true rfl)
  have h_v394 : R 1 0 4611686018158952449 4611686018695823367 v394 v394 := (r_psel hl h_v393 h_v392 h_v33 (of_decide_eq_true rfl))
  have e_v394 : v394 = if v393 = 1 then v392 else v33 := e_psel h_v393 h_v392 h_v33 (of_decide_eq_true rfl)
  have h_v396 : R 1 0 4611686018427387908 4611686018695823367 v396 v396 := (r_sub hl (r_add hl h_v31 h_t387_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v396 : sv v396 = sv v31 + sv t387.1 := e_add h_v31 h_t387_1 (of_decide_eq_true rfl)
  have h_v397 : R 1 0 0 1 v397 v397 := (r_plt hl h_v396 h_v33 (of_decide_eq_true rfl))
  have e_v397 : (v397 = 1 ↔ sv v396 < sv v33) := e_plt h_v396 h_v33 (of_decide_eq_true rfl)
  have h_v398 : R 1 0 4611686018427387908 4611686018695823367 v398 v398 := (r_psel hl h_v397 h_v396 h_v33 (of_decide_eq_true rfl))
  have e_v398 : v398 = if v397 = 1 then v396 else v33 := e_psel h_v397 h_v396 h_v33 (of_decide_eq_true rfl)
  have h_v399 : R 1 0 4611686018427387900 4611686018695823359 v399 v399 := (r_sub hl (r_add hl h_v28 h_t387_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v399 : sv v399 = sv v28 + sv t387.1 := e_add h_v28 h_t387_1 (of_decide_eq_true rfl)
  have h_v400 : R 1 0 4611686018158952441 4611686018695823367 v400 v400 := (r_psel hl h_v342 h_v391 h_v394 (of_decide_eq_true rfl))
  have e_v400 : v400 = if v342 = 1 then v391 else v394 := e_psel h_v342 h_v391 h_v394 (of_decide_eq_true rfl)
  have h_v401 : R 1 0 4611686018427387900 4611686018695823367 v401 v401 := (r_psel hl h_v342 h_v398 h_v399 (of_decide_eq_true rfl))
  have e_v401 : v401 = if v342 = 1 then v398 else v399 := e_psel h_v342 h_v398 h_v399 (of_decide_eq_true rfl)
  have h_v402 : R 1 0 4539628418483879831 4683743618370895977 v402 v402 := (r_smx hl 29 h_v343 h_v401 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v402 : sv v402 = sv v343 * sv v401 := e_smx 29 h_v343 h_v401 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v403 : R 1 0 4539628420631363535 4683743616223412273 v403 v403 := (r_smx hl 29 h_v400 h_v386 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v403 : sv v403 = sv v400 * sv v386 := e_smx 29 h_v400 h_v386 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v404 : R 1 0 0 1 v404 v404 := (r_plt hl h_v403 h_v402 (of_decide_eq_true rfl))
  have e_v404 : (v404 = 1 ↔ sv v403 < sv v402) := e_plt h_v403 h_v402 (of_decide_eq_true rfl)
  clear h_v343 h_v386 h_t387_1 h_t387_2 h_v389 h_v390 h_v392 h_v393 h_v394 h_v396 h_v397 h_v398 h_v399 h_v400 h_v401
  have h_v405 : R 1 0 0 1 v405 v405 := (r_sub hl (r_O hl) h_v404 (of_decide_eq_true rfl))
  have e_v405 : (v405 = 1 ↔ ¬v404 = 1) := e_not h_v404 (of_decide_eq_true rfl)
  have h_v406 : R 1 0 0 1 v406 v406 := (r_plt hl h_v402 h_v403 (of_decide_eq_true rfl))
  have e_v406 : (v406 = 1 ↔ sv v402 < sv v403) := e_plt h_v402 h_v403 (of_decide_eq_true rfl)
  have h_v407 : R 1 0 0 1 v407 v407 := (r_sub hl (r_O hl) h_v406 (of_decide_eq_true rfl))
  have e_v407 : (v407 = 1 ↔ ¬v406 = 1) := e_not h_v406 (of_decide_eq_true rfl)
  have h_v408 : R 1 0 0 1 v408 v408 := (r_plt hl h_v61 h_v387 (of_decide_eq_true rfl))
  have e_v408 : (v408 = 1 ↔ sv v61 < sv v387) := e_plt h_v61 h_v387 (of_decide_eq_true rfl)
  have h_v409 : R 1 0 0 1 v409 v409 := (r_sub hl (r_O hl) h_v408 (of_decide_eq_true rfl))
  have e_v409 : (v409 = 1 ↔ ¬v408 = 1) := e_not h_v408 (of_decide_eq_true rfl)
  have h_v410 : R 1 0 0 1 v410 v410 := (r_plt hl h_v216 h_v387 (of_decide_eq_true rfl))
  have e_v410 : (v410 = 1 ↔ sv v216 < sv v387) := e_plt h_v216 h_v387 (of_decide_eq_true rfl)
  have h_v411 : R 1 0 0 1 v411 v411 := (r_sub hl (r_O hl) h_v410 (of_decide_eq_true rfl))
  have e_v411 : (v411 = 1 ↔ ¬v410 = 1) := e_not h_v410 (of_decide_eq_true rfl)
  have h_v412 : R 1 0 0 1 v412 v412 := (r_plt hl h_v19 h_v391 (of_decide_eq_true rfl))
  have e_v412 : (v412 = 1 ↔ sv v19 < sv v391) := e_plt h_v19 h_v391 (of_decide_eq_true rfl)
  have h_v413 : R 1 0 0 1 v413 v413 := (r_land hl h_v405 h_v412 (of_decide_eq_true rfl))
  have e_v413 : (v413 = 1 ↔ v405 = 1 ∧ v412 = 1) := e_land h_v405 h_v412 (of_decide_eq_true rfl)
  have h_v414 : R 1 0 0 1 v414 v414 := (r_land hl h_v411 h_v413 (of_decide_eq_true rfl))
  have e_v414 : (v414 = 1 ↔ v411 = 1 ∧ v413 = 1) := e_land h_v411 h_v413 (of_decide_eq_true rfl)
  have h_v415 : R 1 0 0 1 v415 v415 := (r_lor hl h_v409 h_v414 (of_decide_eq_true rfl))
  have e_v415 : (v415 = 1 ↔ v409 = 1 ∨ v414 = 1) := e_lor h_v409 h_v414 (of_decide_eq_true rfl)
  have h_v416 : R 1 0 0 1 v416 v416 := (r_plt hl h_v387 h_v223 (of_decide_eq_true rfl))
  have e_v416 : (v416 = 1 ↔ sv v387 < sv v223) := e_plt h_v387 h_v223 (of_decide_eq_true rfl)
  have h_v417 : R 1 0 0 1 v417 v417 := (r_sub hl (r_O hl) h_v416 (of_decide_eq_true rfl))
  clear h_v391 h_v402 h_v403 h_v404 h_v405 h_v406 h_v408 h_v409 h_v410 h_v411 h_v412 h_v413 h_v414
  have e_v417 : (v417 = 1 ↔ ¬v416 = 1) := e_not h_v416 (of_decide_eq_true rfl)
  have h_v418 : R 1 0 0 1 v418 v418 := (r_lor hl h_v407 h_v417 (of_decide_eq_true rfl))
  have e_v418 : (v418 = 1 ↔ v407 = 1 ∨ v417 = 1) := e_lor h_v407 h_v417 (of_decide_eq_true rfl)
  have h_v419 : R 1 0 0 1 v419 v419 := (r_land hl h_v342 h_v415 (of_decide_eq_true rfl))
  have e_v419 : (v419 = 1 ↔ v342 = 1 ∧ v415 = 1) := e_land h_v342 h_v415 (of_decide_eq_true rfl)
  have h_v420 : R 1 0 0 1 v420 v420 := (r_sub hl (r_O hl) h_v342 (of_decide_eq_true rfl))
  have e_v420 : (v420 = 1 ↔ ¬v342 = 1) := e_not h_v342 (of_decide_eq_true rfl)
  have h_v421 : R 1 0 0 1 v421 v421 := (r_land hl h_v418 h_v420 (of_decide_eq_true rfl))
  have e_v421 : (v421 = 1 ↔ v418 = 1 ∧ v420 = 1) := e_land h_v418 h_v420 (of_decide_eq_true rfl)
  have h_v422 : R 1 0 0 1 v422 v422 := (r_lor hl h_v419 h_v421 (of_decide_eq_true rfl))
  have e_v422 : (v422 = 1 ↔ v419 = 1 ∨ v421 = 1) := e_lor h_v419 h_v421 (of_decide_eq_true rfl)
  have h_v423 : R 1 0 4611686017353646081 4611686018427387904 v423 v423 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v387 (of_decide_eq_true rfl))
  have e_v423 : sv v423 = sv v61 - sv v387 := e_sub h_v61 h_v387 (of_decide_eq_true rfl)
  have h_v424 : R 1 0 4611686017353646081 4611686019501129727 v424 v424 := (r_psel hl h_v342 h_v423 h_v387 (of_decide_eq_true rfl))
  have e_v424 : v424 = if v342 = 1 then v423 else v387 := e_psel h_v342 h_v423 h_v387 (of_decide_eq_true rfl)
  have h_v425 : R 1 0 4611686017353646081 4611686019501129727 v425 v425 := (r_psel hl h_v422 h_v424 h_v223 (of_decide_eq_true rfl))
  have e_v425 : v425 = if v422 = 1 then v424 else v223 := e_psel h_v422 h_v424 h_v223 (of_decide_eq_true rfl)
  have h_v427 : R 1 0 4611686017353646081 4611686019501129727 v427 v427 := (r_psel hl h_v339 h_v223 h_v425 (of_decide_eq_true rfl))
  have e_v427 : v427 = if v339 = 1 then v223 else v425 := e_psel h_v339 h_v223 h_v425 (of_decide_eq_true rfl)
  have h_v428 : R 1 0 4611686018427387904 4611686052787126264 v428 v428 := (r_add hl (r_pshr1 hl h_v4) h_H61r (of_decide_eq_true rfl))
  have e_v428 : sv v428 = sv v4 / 2 := e_halfF h_v4
  have h_v429 : R 1 0 4611686018427387904 4611686052787126264 v429 v429 := (r_add hl (r_pshr1 hl (r_add hl h_v5 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v429 : sv v429 = (sv v5 + 1) / 2 := e_halfC h_v5 (of_decide_eq_true rfl)
  have h_v430 : R 1 0 0 1 v430 v430 := (r_plt hl h_v19 h_v428 (of_decide_eq_true rfl))
  have e_v430 : (v430 = 1 ↔ sv v19 < sv v428) := e_plt h_v19 h_v428 (of_decide_eq_true rfl)
  clear h_v339 h_v342 h_v387 h_v407 h_v415 h_v416 h_v417 h_v418 h_v419 h_v420 h_v421 h_v422 h_v423 h_v424 h_v425
  have h_v431 : R 1 0 0 1 v431 v431 := (r_plt hl h_v9 h_v429 (of_decide_eq_true rfl))
  have e_v431 : (v431 = 1 ↔ sv v9 < sv v429) := e_plt h_v9 h_v429 (of_decide_eq_true rfl)
  have h_v432 : R 1 0 0 1 v432 v432 := (r_sub hl (r_O hl) h_v431 (of_decide_eq_true rfl))
  have e_v432 : (v432 = 1 ↔ ¬v431 = 1) := e_not h_v431 (of_decide_eq_true rfl)
  have h_v433 : R 1 0 0 1 v433 v433 := (r_land hl h_v430 h_v432 (of_decide_eq_true rfl))
  have e_v433 : (v433 = 1 ↔ v430 = 1 ∧ v432 = 1) := e_land h_v430 h_v432 (of_decide_eq_true rfl)
  have h_t428_1 : R 1 0 4611686018427387904 4611686018695823363 t428.1 t428.1 := r_sc1 hl h_v428 (of_decide_eq_true rfl)
  have h_t428_2 : R 1 0 4611686018158952445 4611686018695823363 t428.2 t428.2 := r_sc2 hl h_v428 (of_decide_eq_true rfl)
  have e_t428_1 : sv t428.1 = (sc28pS (scArg v428)).1 := e_sc1 h_v428 (of_decide_eq_true rfl)
  have e_t428_2 : sv t428.2 = (sc28pS (scArg v428)).2 := e_sc2 h_v428 (of_decide_eq_true rfl)
  have h_t429_1 : R 1 0 4611686018427387904 4611686018695823363 t429.1 t429.1 := r_sc1 hl h_v429 (of_decide_eq_true rfl)
  have h_t429_2 : R 1 0 4611686018158952445 4611686018695823363 t429.2 t429.2 := r_sc2 hl h_v429 (of_decide_eq_true rfl)
  have e_t429_1 : sv t429.1 = (sc28pS (scArg v429)).1 := e_sc1 h_v429 (of_decide_eq_true rfl)
  have e_t429_2 : sv t429.2 = (sc28pS (scArg v429)).2 := e_sc2 h_v429 (of_decide_eq_true rfl)
  have h_v436 : R 1 0 0 1 v436 v436 := (r_plt hl h_t428_1 h_t429_1 (of_decide_eq_true rfl))
  have e_v436 : (v436 = 1 ↔ sv t428.1 < sv t429.1) := e_plt h_t428_1 h_t429_1 (of_decide_eq_true rfl)
  have h_v437 : R 1 0 4611686018427387904 4611686018695823363 v437 v437 := (r_psel hl h_v436 h_t428_1 h_t429_1 (of_decide_eq_true rfl))
  have e_v437 : v437 = if v436 = 1 then t428.1 else t429.1 := e_psel h_v436 h_t428_1 h_t429_1 (of_decide_eq_true rfl)
  have h_v438 : R 1 0 4611686018427387900 4611686018695823359 v438 v438 := (r_sub hl (r_add hl h_v28 h_v437 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v438 : sv v438 = sv v28 + sv v437 := e_add h_v28 h_v437 (of_decide_eq_true rfl)
  have h_v439 : R 1 0 4611686018427387904 4611686018695823363 v439 v439 := (r_psel hl h_v436 h_t429_1 h_t428_1 (of_decide_eq_true rfl))
  have e_v439 : v439 = if v436 = 1 then t429.1 else t428.1 := e_psel h_v436 h_t429_1 h_t428_1 (of_decide_eq_true rfl)
  have h_v440 : R 1 0 4611686018427387908 4611686018695823367 v440 v440 := (r_sub hl (r_add hl h_v31 h_v439 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v440 : sv v440 = sv v31 + sv v439 := e_add h_v31 h_v439 (of_decide_eq_true rfl)
  have h_v441 : R 1 0 0 1 v441 v441 := (r_plt hl h_v440 h_v33 (of_decide_eq_true rfl))
  clear h_v431 h_v436 h_v437 h_v439
  have e_v441 : (v441 = 1 ↔ sv v440 < sv v33) := e_plt h_v440 h_v33 (of_decide_eq_true rfl)
  have h_v442 : R 1 0 4611686018427387908 4611686018695823367 v442 v442 := (r_psel hl h_v441 h_v440 h_v33 (of_decide_eq_true rfl))
  have e_v442 : v442 = if v441 = 1 then v440 else v33 := e_psel h_v441 h_v440 h_v33 (of_decide_eq_true rfl)
  have h_v443 : R 1 0 0 1 v443 v443 := (r_plt hl h_v428 h_v36 (of_decide_eq_true rfl))
  have e_v443 : (v443 = 1 ↔ sv v428 < sv v36) := e_plt h_v428 h_v36 (of_decide_eq_true rfl)
  have h_v444 : R 1 0 0 1 v444 v444 := (r_plt hl h_v38 h_v429 (of_decide_eq_true rfl))
  have e_v444 : (v444 = 1 ↔ sv v38 < sv v429) := e_plt h_v38 h_v429 (of_decide_eq_true rfl)
  have h_v445 : R 1 0 0 1 v445 v445 := (r_land hl h_v443 h_v444 (of_decide_eq_true rfl))
  have e_v445 : (v445 = 1 ↔ v443 = 1 ∧ v444 = 1) := e_land h_v443 h_v444 (of_decide_eq_true rfl)
  have h_v446 : R 1 0 4611686018427387908 4611686018695823367 v446 v446 := (r_psel hl h_v445 h_v33 h_v442 (of_decide_eq_true rfl))
  have e_v446 : v446 = if v445 = 1 then v33 else v442 := e_psel h_v445 h_v33 h_v442 (of_decide_eq_true rfl)
  have h_v447 : R 1 0 0 1 v447 v447 := (r_plt hl h_v438 h_v61 (of_decide_eq_true rfl))
  have e_v447 : (v447 = 1 ↔ sv v438 < sv v61) := e_plt h_v438 h_v61 (of_decide_eq_true rfl)
  have h_v449 : R 1 0 0 1 v449 v449 := (r_plt hl h_v61 h_v446 (of_decide_eq_true rfl))
  have e_v449 : (v449 = 1 ↔ sv v61 < sv v446) := e_plt h_v61 h_v446 (of_decide_eq_true rfl)
  have h_v450 : R 1 0 0 1 v450 v450 := (r_sub hl (r_O hl) h_v449 (of_decide_eq_true rfl))
  have e_v450 : (v450 = 1 ↔ ¬v449 = 1) := e_not h_v449 (of_decide_eq_true rfl)
  have h_v451 : R 1 0 0 1 v451 v451 := (r_land hl h_v447 h_v450 (of_decide_eq_true rfl))
  have e_v451 : (v451 = 1 ↔ v447 = 1 ∧ v450 = 1) := e_land h_v447 h_v450 (of_decide_eq_true rfl)
  have h_v452 : R 1 0 0 1 v452 v452 := (r_land hl h_v447 h_v449 (of_decide_eq_true rfl))
  have e_v452 : (v452 = 1 ↔ v447 = 1 ∧ v449 = 1) := e_land h_v447 h_v449 (of_decide_eq_true rfl)
  have h_v453 : R 1 0 0 1 v453 v453 := (r_land hl h_v67 h_v452 (of_decide_eq_true rfl))
  have e_v453 : (v453 = 1 ↔ v67 = 1 ∧ v452 = 1) := e_land h_v67 h_v452 (of_decide_eq_true rfl)
  have h_v454 : R 1 0 0 1 v454 v454 := (r_land hl h_v63 h_v452 (of_decide_eq_true rfl))
  have e_v454 : (v454 = 1 ↔ v63 = 1 ∧ v452 = 1) := e_land h_v63 h_v452 (of_decide_eq_true rfl)
  clear h_v440 h_v441 h_v442 h_v445 h_v447 h_v449 h_v450
  have h_v455 : R 1 0 0 1 v455 v455 := (r_lor hl h_v451 h_v454 (of_decide_eq_true rfl))
  have e_v455 : (v455 = 1 ↔ v451 = 1 ∨ v454 = 1) := e_lor h_v451 h_v454 (of_decide_eq_true rfl)
  have h_v456 : R 1 0 4611686018427387900 4611686018695823367 v456 v456 := (r_psel hl h_v455 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v456 : v456 = if v455 = 1 then v41 else v29 := e_psel h_v455 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v457 : R 1 0 0 1 v457 v457 := (r_sub hl (r_O hl) h_v451 (of_decide_eq_true rfl))
  have e_v457 : (v457 = 1 ↔ ¬v451 = 1) := e_not h_v451 (of_decide_eq_true rfl)
  have h_v458 : R 1 0 0 1 v458 v458 := (r_land hl h_v67 h_v457 (of_decide_eq_true rfl))
  have e_v458 : (v458 = 1 ↔ v67 = 1 ∧ v457 = 1) := e_land h_v67 h_v457 (of_decide_eq_true rfl)
  have h_v459 : R 1 0 0 1 v459 v459 := (r_lor hl h_v66 h_v458 (of_decide_eq_true rfl))
  have e_v459 : (v459 = 1 ↔ v66 = 1 ∨ v458 = 1) := e_lor h_v66 h_v458 (of_decide_eq_true rfl)
  have h_v460 : R 1 0 4611686018427387900 4611686018695823367 v460 v460 := (r_psel hl h_v459 h_v446 h_v438 (of_decide_eq_true rfl))
  have e_v460 : v460 = if v459 = 1 then v446 else v438 := e_psel h_v459 h_v446 h_v438 (of_decide_eq_true rfl)
  have h_v461 : R 1 0 0 1 v461 v461 := (r_land hl h_v66 h_v452 (of_decide_eq_true rfl))
  have e_v461 : (v461 = 1 ↔ v66 = 1 ∧ v452 = 1) := e_land h_v66 h_v452 (of_decide_eq_true rfl)
  have h_v462 : R 1 0 0 1 v462 v462 := (r_lor hl h_v451 h_v461 (of_decide_eq_true rfl))
  have e_v462 : (v462 = 1 ↔ v451 = 1 ∨ v461 = 1) := e_lor h_v451 h_v461 (of_decide_eq_true rfl)
  have h_v463 : R 1 0 4611686018427387900 4611686018695823367 v463 v463 := (r_psel hl h_v462 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v463 : v463 = if v462 = 1 then v29 else v41 := e_psel h_v462 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v464 : R 1 0 0 1 v464 v464 := (r_land hl h_v67 h_v451 (of_decide_eq_true rfl))
  have e_v464 : (v464 = 1 ↔ v67 = 1 ∧ v451 = 1) := e_land h_v67 h_v451 (of_decide_eq_true rfl)
  have h_v465 : R 1 0 0 1 v465 v465 := (r_lor hl h_v66 h_v464 (of_decide_eq_true rfl))
  have e_v465 : (v465 = 1 ↔ v66 = 1 ∨ v464 = 1) := e_lor h_v66 h_v464 (of_decide_eq_true rfl)
  have h_v466 : R 1 0 4611686018427387900 4611686018695823367 v466 v466 := (r_psel hl h_v465 h_v438 h_v446 (of_decide_eq_true rfl))
  have e_v466 : v466 = if v465 = 1 then v438 else v446 := e_psel h_v465 h_v438 h_v446 (of_decide_eq_true rfl)
  have h_v467 : R 1 0 4611686017353646052 4683743616223412273 v467 v467 := (r_smx hl 29 h_v460 h_v456 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  clear h_v454 h_v455 h_v458 h_v459 h_v461 h_v462 h_v464 h_v465
  have e_v467 : sv v467 = sv v460 * sv v456 := e_smx 29 h_v460 h_v456 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v468 : R 1 0 4611686018427387899 4611686018695823374 v468 v468 := (r_srdF hl h_v467 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v468 : sv v468 = sv v467 / 2 ^ 28 := e_srdF h_v467 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v469 : R 1 0 4611686017353646052 4683743616223412273 v469 v469 := (r_smx hl 29 h_v466 h_v463 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v469 : sv v469 = sv v466 * sv v463 := e_smx 29 h_v466 h_v463 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v470 : R 1 0 4611686018427387900 4611686018695823375 v470 v470 := (r_srdC hl h_v469 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v470 : sv v470 = -((-sv v469) / 2 ^ 28) := e_srdC h_v469 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v471 : R 1 0 4611686017353646052 4683743614075928569 v471 v471 := (r_smx hl 29 h_v438 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl))
  have e_v471 : sv v471 = sv v438 * sv v41 := e_smx 29 h_v438 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl)
  have h_v472 : R 1 0 4611686018427387899 4611686018695823365 v472 v472 := (r_srdF hl h_v471 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl))
  have e_v472 : sv v472 = sv v471 / 2 ^ 28 := e_srdF h_v471 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl)
  have h_v473 : R 1 0 4611686017353646084 4683743611928444929 v473 v473 := (r_smx hl 29 h_v438 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl))
  have e_v473 : sv v473 = sv v438 * sv v29 := e_smx 29 h_v438 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl)
  have h_v474 : R 1 0 4611686018427387901 4611686018695823359 v474 v474 := (r_srdC hl h_v473 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl))
  have e_v474 : sv v474 = -((-sv v473) / 2 ^ 28) := e_srdC h_v473 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl)
  have h_v475 : R 1 0 0 1 v475 v475 := (r_plt hl h_v468 h_v472 (of_decide_eq_true rfl))
  have e_v475 : (v475 = 1 ↔ sv v468 < sv v472) := e_plt h_v468 h_v472 (of_decide_eq_true rfl)
  have h_v476 : R 1 0 4611686018427387899 4611686018695823374 v476 v476 := (r_psel hl h_v475 h_v468 h_v472 (of_decide_eq_true rfl))
  have e_v476 : v476 = if v475 = 1 then v468 else v472 := e_psel h_v475 h_v468 h_v472 (of_decide_eq_true rfl)
  have h_v477 : R 1 0 0 1 v477 v477 := (r_plt hl h_v470 h_v474 (of_decide_eq_true rfl))
  have e_v477 : (v477 = 1 ↔ sv v470 < sv v474) := e_plt h_v470 h_v474 (of_decide_eq_true rfl)
  have h_v478 : R 1 0 4611686018427387900 4611686018695823375 v478 v478 := (r_psel hl h_v477 h_v474 h_v470 (of_decide_eq_true rfl))
  have e_v478 : v478 = if v477 = 1 then v474 else v470 := e_psel h_v477 h_v474 h_v470 (of_decide_eq_true rfl)
  have h_v479 : R 1 0 4611686018427387899 4611686018695823374 v479 v479 := (r_psel hl h_v453 h_v476 h_v468 (of_decide_eq_true rfl))
  have e_v479 : v479 = if v453 = 1 then v476 else v468 := e_psel h_v453 h_v476 h_v468 (of_decide_eq_true rfl)
  clear h_v456 h_v460 h_v463 h_v466 h_v467 h_v468 h_v469 h_v471 h_v472 h_v473 h_v474 h_v475 h_v476 h_v477
  have h_v480 : R 1 0 4611686018427387900 4611686018695823375 v480 v480 := (r_psel hl h_v453 h_v478 h_v470 (of_decide_eq_true rfl))
  have e_v480 : v480 = if v453 = 1 then v478 else v470 := e_psel h_v453 h_v478 h_v470 (of_decide_eq_true rfl)
  have h_v481 : R 1 0 0 1 v481 v481 := (r_plt hl h_v19 h_v479 (of_decide_eq_true rfl))
  have e_v481 : (v481 = 1 ↔ sv v19 < sv v479) := e_plt h_v19 h_v479 (of_decide_eq_true rfl)
  have h_v482 : R 1 0 4611686018427387904 4611686052787126264 v482 v482 := (r_add hl (r_pshr1 hl h_v5) h_H61r (of_decide_eq_true rfl))
  have e_v482 : sv v482 = sv v5 / 2 := e_halfF h_v5
  have h_v483 : R 1 0 0 1 v483 v483 := (r_plt hl h_v19 h_v482 (of_decide_eq_true rfl))
  have e_v483 : (v483 = 1 ↔ sv v19 < sv v482) := e_plt h_v19 h_v482 (of_decide_eq_true rfl)
  have h_v484 : R 1 0 0 1 v484 v484 := (r_land hl h_v432 h_v483 (of_decide_eq_true rfl))
  have e_v484 : (v484 = 1 ↔ v432 = 1 ∧ v483 = 1) := e_land h_v432 h_v483 (of_decide_eq_true rfl)
  have h_v486 : R 1 0 4611686018158952441 4611686018695823359 v486 v486 := (r_sub hl (r_add hl h_v28 h_t429_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v486 : sv v486 = sv v28 + sv t429.2 := e_add h_v28 h_t429_2 (of_decide_eq_true rfl)
  have h_v487 : R 1 0 0 1 v487 v487 := (r_plt hl h_v486 h_v105 (of_decide_eq_true rfl))
  have e_v487 : (v487 = 1 ↔ sv v486 < sv v105) := e_plt h_v486 h_v105 (of_decide_eq_true rfl)
  have h_v488 : R 1 0 4611686018158952441 4611686018695823359 v488 v488 := (r_psel hl h_v487 h_v105 h_v486 (of_decide_eq_true rfl))
  have e_v488 : v488 = if v487 = 1 then v105 else v486 := e_psel h_v487 h_v105 h_v486 (of_decide_eq_true rfl)
  have h_v489 : R 1 0 0 1 v489 v489 := (r_plt hl h_v108 h_v429 (of_decide_eq_true rfl))
  have e_v489 : (v489 = 1 ↔ sv v108 < sv v429) := e_plt h_v108 h_v429 (of_decide_eq_true rfl)
  have h_v490 : R 1 0 4611686018158952441 4611686018695823359 v490 v490 := (r_psel hl h_v489 h_v105 h_v488 (of_decide_eq_true rfl))
  have e_v490 : v490 = if v489 = 1 then v105 else v488 := e_psel h_v489 h_v105 h_v488 (of_decide_eq_true rfl)
  have h_t482_1 : R 1 0 4611686018427387904 4611686018695823363 t482.1 t482.1 := r_sc1 hl h_v482 (of_decide_eq_true rfl)
  have h_t482_2 : R 1 0 4611686018158952445 4611686018695823363 t482.2 t482.2 := r_sc2 hl h_v482 (of_decide_eq_true rfl)
  have e_t482_1 : sv t482.1 = (sc28pS (scArg v482)).1 := e_sc1 h_v482 (of_decide_eq_true rfl)
  have e_t482_2 : sv t482.2 = (sc28pS (scArg v482)).2 := e_sc2 h_v482 (of_decide_eq_true rfl)
  have h_v498 : R 1 0 0 1 v498 v498 := (r_plt hl h_t482_1 h_t429_1 (of_decide_eq_true rfl))
  clear h_v5 h_v108 h_t429_2 h_v453 h_v470 h_v478 h_v483 h_v486 h_v487 h_v488 h_v489 h_t482_2 e_t482_2
  have e_v498 : (v498 = 1 ↔ sv t482.1 < sv t429.1) := e_plt h_t482_1 h_t429_1 (of_decide_eq_true rfl)
  have h_v499 : R 1 0 4611686018427387904 4611686018695823363 v499 v499 := (r_psel hl h_v498 h_t482_1 h_t429_1 (of_decide_eq_true rfl))
  have e_v499 : v499 = if v498 = 1 then t482.1 else t429.1 := e_psel h_v498 h_t482_1 h_t429_1 (of_decide_eq_true rfl)
  have h_v500 : R 1 0 4611686018427387900 4611686018695823359 v500 v500 := (r_sub hl (r_add hl h_v28 h_v499 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v500 : sv v500 = sv v28 + sv v499 := e_add h_v28 h_v499 (of_decide_eq_true rfl)
  have h_v501 : R 1 0 4611686018427387904 4611686018695823363 v501 v501 := (r_psel hl h_v498 h_t429_1 h_t482_1 (of_decide_eq_true rfl))
  have e_v501 : v501 = if v498 = 1 then t429.1 else t482.1 := e_psel h_v498 h_t429_1 h_t482_1 (of_decide_eq_true rfl)
  have h_v502 : R 1 0 4611686018427387908 4611686018695823367 v502 v502 := (r_sub hl (r_add hl h_v31 h_v501 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v502 : sv v502 = sv v31 + sv v501 := e_add h_v31 h_v501 (of_decide_eq_true rfl)
  have h_v503 : R 1 0 0 1 v503 v503 := (r_plt hl h_v502 h_v33 (of_decide_eq_true rfl))
  have e_v503 : (v503 = 1 ↔ sv v502 < sv v33) := e_plt h_v502 h_v33 (of_decide_eq_true rfl)
  have h_v504 : R 1 0 4611686018427387908 4611686018695823367 v504 v504 := (r_psel hl h_v503 h_v502 h_v33 (of_decide_eq_true rfl))
  have e_v504 : v504 = if v503 = 1 then v502 else v33 := e_psel h_v503 h_v502 h_v33 (of_decide_eq_true rfl)
  have h_v505 : R 1 0 0 1 v505 v505 := (r_plt hl h_v482 h_v36 (of_decide_eq_true rfl))
  have e_v505 : (v505 = 1 ↔ sv v482 < sv v36) := e_plt h_v482 h_v36 (of_decide_eq_true rfl)
  have h_v506 : R 1 0 0 1 v506 v506 := (r_land hl h_v444 h_v505 (of_decide_eq_true rfl))
  have e_v506 : (v506 = 1 ↔ v444 = 1 ∧ v505 = 1) := e_land h_v444 h_v505 (of_decide_eq_true rfl)
  have h_v507 : R 1 0 4611686018427387908 4611686018695823367 v507 v507 := (r_psel hl h_v506 h_v33 h_v504 (of_decide_eq_true rfl))
  have e_v507 : v507 = if v506 = 1 then v33 else v504 := e_psel h_v506 h_v33 h_v504 (of_decide_eq_true rfl)
  have h_v508 : R 1 0 0 1 v508 v508 := (r_plt hl h_v500 h_v61 (of_decide_eq_true rfl))
  have e_v508 : (v508 = 1 ↔ sv v500 < sv v61) := e_plt h_v500 h_v61 (of_decide_eq_true rfl)
  have h_v510 : R 1 0 0 1 v510 v510 := (r_plt hl h_v61 h_v507 (of_decide_eq_true rfl))
  have e_v510 : (v510 = 1 ↔ sv v61 < sv v507) := e_plt h_v61 h_v507 (of_decide_eq_true rfl)
  have h_v511 : R 1 0 0 1 v511 v511 := (r_sub hl (r_O hl) h_v510 (of_decide_eq_true rfl))
  have e_v511 : (v511 = 1 ↔ ¬v510 = 1) := e_not h_v510 (of_decide_eq_true rfl)
  clear h_v36 h_v498 h_v499 h_v501 h_v502 h_v503 h_v504 h_v505 h_v506
  have h_v512 : R 1 0 0 1 v512 v512 := (r_land hl h_v508 h_v511 (of_decide_eq_true rfl))
  have e_v512 : (v512 = 1 ↔ v508 = 1 ∧ v511 = 1) := e_land h_v508 h_v511 (of_decide_eq_true rfl)
  have h_v513 : R 1 0 0 1 v513 v513 := (r_land hl h_v508 h_v510 (of_decide_eq_true rfl))
  have e_v513 : (v513 = 1 ↔ v508 = 1 ∧ v510 = 1) := e_land h_v508 h_v510 (of_decide_eq_true rfl)
  have h_v514 : R 1 0 0 1 v514 v514 := (r_land hl h_v149 h_v513 (of_decide_eq_true rfl))
  have e_v514 : (v514 = 1 ↔ v149 = 1 ∧ v513 = 1) := e_land h_v149 h_v513 (of_decide_eq_true rfl)
  have h_v515 : R 1 0 0 1 v515 v515 := (r_land hl h_v145 h_v513 (of_decide_eq_true rfl))
  have e_v515 : (v515 = 1 ↔ v145 = 1 ∧ v513 = 1) := e_land h_v145 h_v513 (of_decide_eq_true rfl)
  have h_v516 : R 1 0 0 1 v516 v516 := (r_lor hl h_v512 h_v515 (of_decide_eq_true rfl))
  have e_v516 : (v516 = 1 ↔ v512 = 1 ∨ v515 = 1) := e_lor h_v512 h_v515 (of_decide_eq_true rfl)
  have h_v517 : R 1 0 4611686018158952441 4611686018695823367 v517 v517 := (r_psel hl h_v516 h_v117 h_v110 (of_decide_eq_true rfl))
  have e_v517 : v517 = if v516 = 1 then v117 else v110 := e_psel h_v516 h_v117 h_v110 (of_decide_eq_true rfl)
  have h_v518 : R 1 0 0 1 v518 v518 := (r_sub hl (r_O hl) h_v512 (of_decide_eq_true rfl))
  have e_v518 : (v518 = 1 ↔ ¬v512 = 1) := e_not h_v512 (of_decide_eq_true rfl)
  have h_v519 : R 1 0 0 1 v519 v519 := (r_land hl h_v149 h_v518 (of_decide_eq_true rfl))
  have e_v519 : (v519 = 1 ↔ v149 = 1 ∧ v518 = 1) := e_land h_v149 h_v518 (of_decide_eq_true rfl)
  have h_v520 : R 1 0 0 1 v520 v520 := (r_lor hl h_v148 h_v519 (of_decide_eq_true rfl))
  have e_v520 : (v520 = 1 ↔ v148 = 1 ∨ v519 = 1) := e_lor h_v148 h_v519 (of_decide_eq_true rfl)
  have h_v521 : R 1 0 4611686018427387900 4611686018695823367 v521 v521 := (r_psel hl h_v520 h_v507 h_v500 (of_decide_eq_true rfl))
  have e_v521 : v521 = if v520 = 1 then v507 else v500 := e_psel h_v520 h_v507 h_v500 (of_decide_eq_true rfl)
  have h_v522 : R 1 0 0 1 v522 v522 := (r_land hl h_v148 h_v513 (of_decide_eq_true rfl))
  have e_v522 : (v522 = 1 ↔ v148 = 1 ∧ v513 = 1) := e_land h_v148 h_v513 (of_decide_eq_true rfl)
  have h_v523 : R 1 0 0 1 v523 v523 := (r_lor hl h_v512 h_v522 (of_decide_eq_true rfl))
  have e_v523 : (v523 = 1 ↔ v512 = 1 ∨ v522 = 1) := e_lor h_v512 h_v522 (of_decide_eq_true rfl)
  have h_v524 : R 1 0 4611686018158952441 4611686018695823367 v524 v524 := (r_psel hl h_v523 h_v110 h_v117 (of_decide_eq_true rfl))
  clear h_v508 h_v510 h_v511 h_v513 h_v515 h_v516 h_v518 h_v519 h_v520 h_v522
  have e_v524 : v524 = if v523 = 1 then v110 else v117 := e_psel h_v523 h_v110 h_v117 (of_decide_eq_true rfl)
  have h_v525 : R 1 0 0 1 v525 v525 := (r_land hl h_v149 h_v512 (of_decide_eq_true rfl))
  have e_v525 : (v525 = 1 ↔ v149 = 1 ∧ v512 = 1) := e_land h_v149 h_v512 (of_decide_eq_true rfl)
  have h_v526 : R 1 0 0 1 v526 v526 := (r_lor hl h_v148 h_v525 (of_decide_eq_true rfl))
  have e_v526 : (v526 = 1 ↔ v148 = 1 ∨ v525 = 1) := e_lor h_v148 h_v525 (of_decide_eq_true rfl)
  have h_v527 : R 1 0 4611686018427387900 4611686018695823367 v527 v527 := (r_psel hl h_v526 h_v500 h_v507 (of_decide_eq_true rfl))
  have e_v527 : v527 = if v526 = 1 then v500 else v507 := e_psel h_v526 h_v500 h_v507 (of_decide_eq_true rfl)
  have h_v528 : R 1 0 4539628420631363535 4683743616223412273 v528 v528 := (r_smx hl 29 h_v521 h_v517 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v528 : sv v528 = sv v521 * sv v517 := e_smx 29 h_v521 h_v517 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v529 : R 1 0 4611686018158952433 4611686018695823374 v529 v529 := (r_srdF hl h_v528 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v529 : sv v529 = sv v528 / 2 ^ 28 := e_srdF h_v528 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v530 : R 1 0 4539628420631363535 4683743616223412273 v530 v530 := (r_smx hl 29 h_v527 h_v524 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v530 : sv v530 = sv v527 * sv v524 := e_smx 29 h_v527 h_v524 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v531 : R 1 0 4611686018158952434 4611686018695823375 v531 v531 := (r_srdC hl h_v530 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v531 : sv v531 = -((-sv v530) / 2 ^ 28) := e_srdC h_v530 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v532 : R 1 0 4539628424926330879 4683743614075928569 v532 v532 := (r_smx hl 29 h_v500 h_v117 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl))
  have e_v532 : sv v532 = sv v500 * sv v117 := e_smx 29 h_v500 h_v117 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl)
  have h_v533 : R 1 0 4611686018158952449 4611686018695823365 v533 v533 := (r_srdF hl h_v532 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl))
  have e_v533 : sv v533 = sv v532 / 2 ^ 28 := e_srdF h_v532 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl)
  have h_v534 : R 1 0 4539628422778847239 4683743611928444929 v534 v534 := (r_smx hl 29 h_v500 h_v110 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl))
  have e_v534 : sv v534 = sv v500 * sv v110 := e_smx 29 h_v500 h_v110 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl)
  have h_v535 : R 1 0 4611686018158952443 4611686018695823359 v535 v535 := (r_srdC hl h_v534 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl))
  have e_v535 : sv v535 = -((-sv v534) / 2 ^ 28) := e_srdC h_v534 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl)
  have h_v536 : R 1 0 0 1 v536 v536 := (r_plt hl h_v529 h_v533 (of_decide_eq_true rfl))
  have e_v536 : (v536 = 1 ↔ sv v529 < sv v533) := e_plt h_v529 h_v533 (of_decide_eq_true rfl)
  clear h_v500 h_v507 h_v512 h_v517 h_v521 h_v523 h_v524 h_v525 h_v526 h_v527 h_v528 h_v530 h_v532 h_v534
  have h_v537 : R 1 0 4611686018158952433 4611686018695823374 v537 v537 := (r_psel hl h_v536 h_v529 h_v533 (of_decide_eq_true rfl))
  have e_v537 : v537 = if v536 = 1 then v529 else v533 := e_psel h_v536 h_v529 h_v533 (of_decide_eq_true rfl)
  have h_v538 : R 1 0 0 1 v538 v538 := (r_plt hl h_v531 h_v535 (of_decide_eq_true rfl))
  have e_v538 : (v538 = 1 ↔ sv v531 < sv v535) := e_plt h_v531 h_v535 (of_decide_eq_true rfl)
  have h_v539 : R 1 0 4611686018158952434 4611686018695823375 v539 v539 := (r_psel hl h_v538 h_v535 h_v531 (of_decide_eq_true rfl))
  have e_v539 : v539 = if v538 = 1 then v535 else v531 := e_psel h_v538 h_v535 h_v531 (of_decide_eq_true rfl)
  have h_v540 : R 1 0 4611686018158952433 4611686018695823374 v540 v540 := (r_psel hl h_v514 h_v537 h_v529 (of_decide_eq_true rfl))
  have e_v540 : v540 = if v514 = 1 then v537 else v529 := e_psel h_v514 h_v537 h_v529 (of_decide_eq_true rfl)
  have h_v541 : R 1 0 4611686018158952434 4611686018695823375 v541 v541 := (r_psel hl h_v514 h_v539 h_v531 (of_decide_eq_true rfl))
  have e_v541 : v541 = if v514 = 1 then v539 else v531 := e_psel h_v514 h_v539 h_v531 (of_decide_eq_true rfl)
  have h_v542 : R 1 0 0 1 v542 v542 := (r_plt hl h_v61 h_v540 (of_decide_eq_true rfl))
  have e_v542 : (v542 = 1 ↔ sv v61 < sv v540) := e_plt h_v61 h_v540 (of_decide_eq_true rfl)
  have h_v543 : R 1 0 0 1 v543 v543 := (r_sub hl (r_O hl) h_v542 (of_decide_eq_true rfl))
  have e_v543 : (v543 = 1 ↔ ¬v542 = 1) := e_not h_v542 (of_decide_eq_true rfl)
  have h_v544 : R 1 0 0 1 v544 v544 := (r_plt hl h_v490 h_v61 (of_decide_eq_true rfl))
  have e_v544 : (v544 = 1 ↔ sv v490 < sv v61) := e_plt h_v490 h_v61 (of_decide_eq_true rfl)
  have h_v545 : R 1 0 4611686018158952433 4611686018695823375 v545 v545 := (r_psel hl h_v544 h_v540 h_v541 (of_decide_eq_true rfl))
  have e_v545 : v545 = if v544 = 1 then v540 else v541 := e_psel h_v544 h_v540 h_v541 (of_decide_eq_true rfl)
  have h_v548 : R 1 0 4611686018158952449 4611686018695823367 v548 v548 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v490 (of_decide_eq_true rfl))
  have e_v548 : sv v548 = sv v61 - sv v490 := e_sub h_v61 h_v490 (of_decide_eq_true rfl)
  have h_v549 : R 1 0 4611686018158952441 4611686018695823367 v549 v549 := (r_psel hl h_v544 h_v548 h_v490 (of_decide_eq_true rfl))
  have e_v549 : v549 = if v544 = 1 then v548 else v490 := e_psel h_v544 h_v548 h_v490 (of_decide_eq_true rfl)
  have h_v550 : R 1 0 4611686018427387904 4611686019501129727 v550 v550 := (r1_hxa hb_H1 0 (of_decide_eq_true rfl))
  have e_v550 : sv v550 = ((H1 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H1 0 (of_decide_eq_true rfl)
  have h_v551 : R 1 0 0 1 v551 v551 := (r_sub hl (r_O hl) h_v544 (of_decide_eq_true rfl))
  clear h_v514 h_v529 h_v531 h_v533 h_v535 h_v536 h_v537 h_v538 h_v539 h_v540 h_v541 h_v542 h_v548
  have e_v551 : (v551 = 1 ↔ ¬v544 = 1) := e_not h_v544 (of_decide_eq_true rfl)
  have h_t550_1 : R 1 0 4611686018427387904 4611686018695823363 t550.1 t550.1 := r_sc1 hl h_v550 (of_decide_eq_true rfl)
  have h_t550_2 : R 1 0 4611686018158952445 4611686018695823363 t550.2 t550.2 := r_sc2 hl h_v550 (of_decide_eq_true rfl)
  have e_t550_1 : sv t550.1 = (sc28pS (scArg v550)).1 := e_sc1 h_v550 (of_decide_eq_true rfl)
  have e_t550_2 : sv t550.2 = (sc28pS (scArg v550)).2 := e_sc2 h_v550 (of_decide_eq_true rfl)
  have h_v553 : R 1 0 4611686018158952441 4611686018695823359 v553 v553 := (r_sub hl (r_add hl h_v28 h_t550_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v553 : sv v553 = sv v28 + sv t550.2 := e_add h_v28 h_t550_2 (of_decide_eq_true rfl)
  have h_v554 : R 1 0 0 1 v554 v554 := (r_plt hl h_v553 h_v105 (of_decide_eq_true rfl))
  have e_v554 : (v554 = 1 ↔ sv v553 < sv v105) := e_plt h_v553 h_v105 (of_decide_eq_true rfl)
  have h_v555 : R 1 0 4611686018158952441 4611686018695823359 v555 v555 := (r_psel hl h_v554 h_v105 h_v553 (of_decide_eq_true rfl))
  have e_v555 : v555 = if v554 = 1 then v105 else v553 := e_psel h_v554 h_v105 h_v553 (of_decide_eq_true rfl)
  have h_v556 : R 1 0 4611686018158952449 4611686018695823367 v556 v556 := (r_sub hl (r_add hl h_v31 h_t550_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v556 : sv v556 = sv v31 + sv t550.2 := e_add h_v31 h_t550_2 (of_decide_eq_true rfl)
  have h_v557 : R 1 0 0 1 v557 v557 := (r_plt hl h_v556 h_v33 (of_decide_eq_true rfl))
  have e_v557 : (v557 = 1 ↔ sv v556 < sv v33) := e_plt h_v556 h_v33 (of_decide_eq_true rfl)
  have h_v558 : R 1 0 4611686018158952449 4611686018695823367 v558 v558 := (r_psel hl h_v557 h_v556 h_v33 (of_decide_eq_true rfl))
  have e_v558 : v558 = if v557 = 1 then v556 else v33 := e_psel h_v557 h_v556 h_v33 (of_decide_eq_true rfl)
  have h_v560 : R 1 0 4611686018427387908 4611686018695823367 v560 v560 := (r_sub hl (r_add hl h_v31 h_t550_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v560 : sv v560 = sv v31 + sv t550.1 := e_add h_v31 h_t550_1 (of_decide_eq_true rfl)
  have h_v561 : R 1 0 0 1 v561 v561 := (r_plt hl h_v560 h_v33 (of_decide_eq_true rfl))
  have e_v561 : (v561 = 1 ↔ sv v560 < sv v33) := e_plt h_v560 h_v33 (of_decide_eq_true rfl)
  have h_v562 : R 1 0 4611686018427387908 4611686018695823367 v562 v562 := (r_psel hl h_v561 h_v560 h_v33 (of_decide_eq_true rfl))
  have e_v562 : v562 = if v561 = 1 then v560 else v33 := e_psel h_v561 h_v560 h_v33 (of_decide_eq_true rfl)
  have h_v563 : R 1 0 4611686018427387900 4611686018695823359 v563 v563 := (r_sub hl (r_add hl h_v28 h_t550_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v563 : sv v563 = sv v28 + sv t550.1 := e_add h_v28 h_t550_1 (of_decide_eq_true rfl)
  clear h_v105 h_t550_1 h_t550_2 h_v553 h_v554 h_v556 h_v557 h_v560 h_v561
  have h_v564 : R 1 0 4611686018158952441 4611686018695823367 v564 v564 := (r_psel hl h_v551 h_v555 h_v558 (of_decide_eq_true rfl))
  have e_v564 : v564 = if v551 = 1 then v555 else v558 := e_psel h_v551 h_v555 h_v558 (of_decide_eq_true rfl)
  have h_v565 : R 1 0 4611686018427387900 4611686018695823367 v565 v565 := (r_psel hl h_v551 h_v562 h_v563 (of_decide_eq_true rfl))
  have e_v565 : v565 = if v551 = 1 then v562 else v563 := e_psel h_v551 h_v562 h_v563 (of_decide_eq_true rfl)
  have h_v566 : R 1 0 4539628418483879831 4683743618370895977 v566 v566 := (r_smx hl 29 h_v545 h_v565 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v566 : sv v566 = sv v545 * sv v565 := e_smx 29 h_v545 h_v565 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v567 : R 1 0 4539628420631363535 4683743616223412273 v567 v567 := (r_smx hl 29 h_v564 h_v549 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v567 : sv v567 = sv v564 * sv v549 := e_smx 29 h_v564 h_v549 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v568 : R 1 0 0 1 v568 v568 := (r_plt hl h_v567 h_v566 (of_decide_eq_true rfl))
  have e_v568 : (v568 = 1 ↔ sv v567 < sv v566) := e_plt h_v567 h_v566 (of_decide_eq_true rfl)
  have h_v569 : R 1 0 0 1 v569 v569 := (r_sub hl (r_O hl) h_v568 (of_decide_eq_true rfl))
  have e_v569 : (v569 = 1 ↔ ¬v568 = 1) := e_not h_v568 (of_decide_eq_true rfl)
  have h_v570 : R 1 0 0 1 v570 v570 := (r_plt hl h_v566 h_v567 (of_decide_eq_true rfl))
  have e_v570 : (v570 = 1 ↔ sv v566 < sv v567) := e_plt h_v566 h_v567 (of_decide_eq_true rfl)
  have h_v571 : R 1 0 0 1 v571 v571 := (r_sub hl (r_O hl) h_v570 (of_decide_eq_true rfl))
  have e_v571 : (v571 = 1 ↔ ¬v570 = 1) := e_not h_v570 (of_decide_eq_true rfl)
  have h_v572 : R 1 0 0 1 v572 v572 := (r_plt hl h_v61 h_v550 (of_decide_eq_true rfl))
  have e_v572 : (v572 = 1 ↔ sv v61 < sv v550) := e_plt h_v61 h_v550 (of_decide_eq_true rfl)
  have h_v573 : R 1 0 0 1 v573 v573 := (r_sub hl (r_O hl) h_v572 (of_decide_eq_true rfl))
  have e_v573 : (v573 = 1 ↔ ¬v572 = 1) := e_not h_v572 (of_decide_eq_true rfl)
  have h_v574 : R 1 0 0 1 v574 v574 := (r_plt hl h_v216 h_v550 (of_decide_eq_true rfl))
  have e_v574 : (v574 = 1 ↔ sv v216 < sv v550) := e_plt h_v216 h_v550 (of_decide_eq_true rfl)
  have h_v575 : R 1 0 0 1 v575 v575 := (r_sub hl (r_O hl) h_v574 (of_decide_eq_true rfl))
  have e_v575 : (v575 = 1 ↔ ¬v574 = 1) := e_not h_v574 (of_decide_eq_true rfl)
  have h_v576 : R 1 0 0 1 v576 v576 := (r_plt hl h_v19 h_v555 (of_decide_eq_true rfl))
  clear h_v216 h_v545 h_v549 h_v558 h_v562 h_v563 h_v564 h_v565 h_v566 h_v567 h_v568 h_v570 h_v572 h_v574
  have e_v576 : (v576 = 1 ↔ sv v19 < sv v555) := e_plt h_v19 h_v555 (of_decide_eq_true rfl)
  have h_v577 : R 1 0 0 1 v577 v577 := (r_land hl h_v569 h_v576 (of_decide_eq_true rfl))
  have e_v577 : (v577 = 1 ↔ v569 = 1 ∧ v576 = 1) := e_land h_v569 h_v576 (of_decide_eq_true rfl)
  have h_v578 : R 1 0 0 1 v578 v578 := (r_land hl h_v575 h_v577 (of_decide_eq_true rfl))
  have e_v578 : (v578 = 1 ↔ v575 = 1 ∧ v577 = 1) := e_land h_v575 h_v577 (of_decide_eq_true rfl)
  have h_v579 : R 1 0 0 1 v579 v579 := (r_lor hl h_v573 h_v578 (of_decide_eq_true rfl))
  have e_v579 : (v579 = 1 ↔ v573 = 1 ∨ v578 = 1) := e_lor h_v573 h_v578 (of_decide_eq_true rfl)
  have h_v580 : R 1 0 0 1 v580 v580 := (r_plt hl h_v550 h_v223 (of_decide_eq_true rfl))
  have e_v580 : (v580 = 1 ↔ sv v550 < sv v223) := e_plt h_v550 h_v223 (of_decide_eq_true rfl)
  have h_v581 : R 1 0 0 1 v581 v581 := (r_sub hl (r_O hl) h_v580 (of_decide_eq_true rfl))
  have e_v581 : (v581 = 1 ↔ ¬v580 = 1) := e_not h_v580 (of_decide_eq_true rfl)
  have h_v582 : R 1 0 0 1 v582 v582 := (r_lor hl h_v571 h_v581 (of_decide_eq_true rfl))
  have e_v582 : (v582 = 1 ↔ v571 = 1 ∨ v581 = 1) := e_lor h_v571 h_v581 (of_decide_eq_true rfl)
  have h_v583 : R 1 0 0 1 v583 v583 := (r_land hl h_v551 h_v579 (of_decide_eq_true rfl))
  have e_v583 : (v583 = 1 ↔ v551 = 1 ∧ v579 = 1) := e_land h_v551 h_v579 (of_decide_eq_true rfl)
  have h_v584 : R 1 0 0 1 v584 v584 := (r_land hl h_v544 h_v582 (of_decide_eq_true rfl))
  have e_v584 : (v584 = 1 ↔ v544 = 1 ∧ v582 = 1) := e_land h_v544 h_v582 (of_decide_eq_true rfl)
  have h_v585 : R 1 0 0 1 v585 v585 := (r_lor hl h_v583 h_v584 (of_decide_eq_true rfl))
  have e_v585 : (v585 = 1 ↔ v583 = 1 ∨ v584 = 1) := e_lor h_v583 h_v584 (of_decide_eq_true rfl)
  have h_v586 : R 1 0 4611686017353646081 4611686018427387904 v586 v586 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v550 (of_decide_eq_true rfl))
  have e_v586 : sv v586 = sv v61 - sv v550 := e_sub h_v61 h_v550 (of_decide_eq_true rfl)
  have h_v587 : R 1 0 4611686017353646081 4611686019501129727 v587 v587 := (r_psel hl h_v544 h_v586 h_v550 (of_decide_eq_true rfl))
  have e_v587 : v587 = if v544 = 1 then v586 else v550 := e_psel h_v544 h_v586 h_v550 (of_decide_eq_true rfl)
  have h_v588 : R 1 0 4611686017353646081 4611686019501129727 v588 v588 := (r_psel hl h_v585 h_v587 h_v232 (of_decide_eq_true rfl))
  have e_v588 : v588 = if v585 = 1 then v587 else v232 := e_psel h_v585 h_v587 h_v232 (of_decide_eq_true rfl)
  clear h_v19 h_v223 h_v550 h_v551 h_v555 h_v569 h_v571 h_v573 h_v575 h_v576 h_v577 h_v578 h_v579 h_v580 h_v581 h_v582 h_v583 h_v584 h_v585 h_v586 h_v587
  have h_v630 : R 1 0 4611686017353646081 4611686019501129727 v630 v630 := (r_psel hl h_v543 h_v232 h_v588 (of_decide_eq_true rfl))
  have e_v630 : v630 = if v543 = 1 then v232 else v588 := e_psel h_v543 h_v232 h_v588 (of_decide_eq_true rfl)
  have h_v632 : R 1 0 4611686018427387904 4611686052787126264 v632 v632 := (r_add hl (r_pshr1 hl (r_add hl h_v4 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v632 : sv v632 = (sv v4 + 1) / 2 := e_halfC h_v4 (of_decide_eq_true rfl)
  have h_v633 : R 1 0 0 1 v633 v633 := (r_plt hl h_v9 h_v632 (of_decide_eq_true rfl))
  have e_v633 : (v633 = 1 ↔ sv v9 < sv v632) := e_plt h_v9 h_v632 (of_decide_eq_true rfl)
  have h_v634 : R 1 0 0 1 v634 v634 := (r_sub hl (r_O hl) h_v633 (of_decide_eq_true rfl))
  have e_v634 : (v634 = 1 ↔ ¬v633 = 1) := e_not h_v633 (of_decide_eq_true rfl)
  have h_v635 : R 1 0 0 1 v635 v635 := (r_land hl h_v430 h_v634 (of_decide_eq_true rfl))
  have e_v635 : (v635 = 1 ↔ v430 = 1 ∧ v634 = 1) := e_land h_v430 h_v634 (of_decide_eq_true rfl)
  have h_v643 : R 1 0 4611686018158952449 4611686018695823367 v643 v643 := (r_sub hl (r_add hl h_v31 h_t428_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v643 : sv v643 = sv v31 + sv t428.2 := e_add h_v31 h_t428_2 (of_decide_eq_true rfl)
  have h_v644 : R 1 0 0 1 v644 v644 := (r_plt hl h_v643 h_v33 (of_decide_eq_true rfl))
  have e_v644 : (v644 = 1 ↔ sv v643 < sv v33) := e_plt h_v643 h_v33 (of_decide_eq_true rfl)
  have h_v645 : R 1 0 4611686018158952449 4611686018695823367 v645 v645 := (r_psel hl h_v644 h_v643 h_v33 (of_decide_eq_true rfl))
  have e_v645 : v645 = if v644 = 1 then v643 else v33 := e_psel h_v644 h_v643 h_v33 (of_decide_eq_true rfl)
  have h_v646 : R 1 0 0 1 v646 v646 := (r_plt hl h_v428 h_v115 (of_decide_eq_true rfl))
  have e_v646 : (v646 = 1 ↔ sv v428 < sv v115) := e_plt h_v428 h_v115 (of_decide_eq_true rfl)
  have h_v647 : R 1 0 4611686018158952449 4611686018695823367 v647 v647 := (r_psel hl h_v646 h_v33 h_v645 (of_decide_eq_true rfl))
  have e_v647 : v647 = if v646 = 1 then v33 else v645 := e_psel h_v646 h_v33 h_v645 (of_decide_eq_true rfl)
  have h_t632_1 : R 1 0 4611686018427387904 4611686018695823363 t632.1 t632.1 := r_sc1 hl h_v632 (of_decide_eq_true rfl)
  have h_t632_2 : R 1 0 4611686018158952445 4611686018695823363 t632.2 t632.2 := r_sc2 hl h_v632 (of_decide_eq_true rfl)
  have e_t632_1 : sv t632.1 = (sc28pS (scArg v632)).1 := e_sc1 h_v632 (of_decide_eq_true rfl)
  have e_t632_2 : sv t632.2 = (sc28pS (scArg v632)).2 := e_sc2 h_v632 (of_decide_eq_true rfl)
  have h_v649 : R 1 0 0 1 v649 v649 := (r_plt hl h_t428_1 h_t632_1 (of_decide_eq_true rfl))
  clear h_H61r h_v4 h_v9 h_v115 h_v232 h_v430 h_t428_2 h_v543 h_v588 h_v633 h_v634 h_v643 h_v644 h_v645 h_v646 h_t632_2 e_t632_2
  have e_v649 : (v649 = 1 ↔ sv t428.1 < sv t632.1) := e_plt h_t428_1 h_t632_1 (of_decide_eq_true rfl)
  have h_v650 : R 1 0 4611686018427387904 4611686018695823363 v650 v650 := (r_psel hl h_v649 h_t428_1 h_t632_1 (of_decide_eq_true rfl))
  have e_v650 : v650 = if v649 = 1 then t428.1 else t632.1 := e_psel h_v649 h_t428_1 h_t632_1 (of_decide_eq_true rfl)
  have h_v651 : R 1 0 4611686018427387900 4611686018695823359 v651 v651 := (r_sub hl (r_add hl h_v28 h_v650 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v651 : sv v651 = sv v28 + sv v650 := e_add h_v28 h_v650 (of_decide_eq_true rfl)
  have h_v652 : R 1 0 4611686018427387904 4611686018695823363 v652 v652 := (r_psel hl h_v649 h_t632_1 h_t428_1 (of_decide_eq_true rfl))
  have e_v652 : v652 = if v649 = 1 then t632.1 else t428.1 := e_psel h_v649 h_t632_1 h_t428_1 (of_decide_eq_true rfl)
  have h_v653 : R 1 0 4611686018427387908 4611686018695823367 v653 v653 := (r_sub hl (r_add hl h_v31 h_v652 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v653 : sv v653 = sv v31 + sv v652 := e_add h_v31 h_v652 (of_decide_eq_true rfl)
  have h_v654 : R 1 0 0 1 v654 v654 := (r_plt hl h_v653 h_v33 (of_decide_eq_true rfl))
  have e_v654 : (v654 = 1 ↔ sv v653 < sv v33) := e_plt h_v653 h_v33 (of_decide_eq_true rfl)
  have h_v655 : R 1 0 4611686018427387908 4611686018695823367 v655 v655 := (r_psel hl h_v654 h_v653 h_v33 (of_decide_eq_true rfl))
  have e_v655 : v655 = if v654 = 1 then v653 else v33 := e_psel h_v654 h_v653 h_v33 (of_decide_eq_true rfl)
  have h_v656 : R 1 0 0 1 v656 v656 := (r_plt hl h_v38 h_v632 (of_decide_eq_true rfl))
  have e_v656 : (v656 = 1 ↔ sv v38 < sv v632) := e_plt h_v38 h_v632 (of_decide_eq_true rfl)
  have h_v657 : R 1 0 0 1 v657 v657 := (r_land hl h_v443 h_v656 (of_decide_eq_true rfl))
  have e_v657 : (v657 = 1 ↔ v443 = 1 ∧ v656 = 1) := e_land h_v443 h_v656 (of_decide_eq_true rfl)
  have h_v658 : R 1 0 4611686018427387908 4611686018695823367 v658 v658 := (r_psel hl h_v657 h_v33 h_v655 (of_decide_eq_true rfl))
  have e_v658 : v658 = if v657 = 1 then v33 else v655 := e_psel h_v657 h_v33 h_v655 (of_decide_eq_true rfl)
  have h_v659 : R 1 0 0 1 v659 v659 := (r_plt hl h_v651 h_v61 (of_decide_eq_true rfl))
  have e_v659 : (v659 = 1 ↔ sv v651 < sv v61) := e_plt h_v651 h_v61 (of_decide_eq_true rfl)
  have h_v661 : R 1 0 0 1 v661 v661 := (r_plt hl h_v61 h_v658 (of_decide_eq_true rfl))
  have e_v661 : (v661 = 1 ↔ sv v61 < sv v658) := e_plt h_v61 h_v658 (of_decide_eq_true rfl)
  have h_v662 : R 1 0 0 1 v662 v662 := (r_sub hl (r_O hl) h_v661 (of_decide_eq_true rfl))
  have e_v662 : (v662 = 1 ↔ ¬v661 = 1) := e_not h_v661 (of_decide_eq_true rfl)
  clear h_OFFr h_v28 h_v31 h_v33 h_v38 h_v61 h_v443 h_t632_1 h_v649 h_v650 h_v652 h_v653 h_v654 h_v655 h_v656 h_v657
  have h_v663 : R 1 0 0 1 v663 v663 := (r_land hl h_v659 h_v662 (of_decide_eq_true rfl))
  have e_v663 : (v663 = 1 ↔ v659 = 1 ∧ v662 = 1) := e_land h_v659 h_v662 (of_decide_eq_true rfl)
  have h_v664 : R 1 0 0 1 v664 v664 := (r_land hl h_v659 h_v661 (of_decide_eq_true rfl))
  have e_v664 : (v664 = 1 ↔ v659 = 1 ∧ v661 = 1) := e_land h_v659 h_v661 (of_decide_eq_true rfl)
  have h_v665 : R 1 0 0 1 v665 v665 := (r_land hl h_v149 h_v664 (of_decide_eq_true rfl))
  have e_v665 : (v665 = 1 ↔ v149 = 1 ∧ v664 = 1) := e_land h_v149 h_v664 (of_decide_eq_true rfl)
  have h_v666 : R 1 0 0 1 v666 v666 := (r_land hl h_v145 h_v664 (of_decide_eq_true rfl))
  have e_v666 : (v666 = 1 ↔ v145 = 1 ∧ v664 = 1) := e_land h_v145 h_v664 (of_decide_eq_true rfl)
  have h_v667 : R 1 0 0 1 v667 v667 := (r_lor hl h_v663 h_v666 (of_decide_eq_true rfl))
  have e_v667 : (v667 = 1 ↔ v663 = 1 ∨ v666 = 1) := e_lor h_v663 h_v666 (of_decide_eq_true rfl)
  have h_v668 : R 1 0 4611686018158952441 4611686018695823367 v668 v668 := (r_psel hl h_v667 h_v117 h_v110 (of_decide_eq_true rfl))
  have e_v668 : v668 = if v667 = 1 then v117 else v110 := e_psel h_v667 h_v117 h_v110 (of_decide_eq_true rfl)
  have h_v669 : R 1 0 0 1 v669 v669 := (r_sub hl (r_O hl) h_v663 (of_decide_eq_true rfl))
  have e_v669 : (v669 = 1 ↔ ¬v663 = 1) := e_not h_v663 (of_decide_eq_true rfl)
  have h_v670 : R 1 0 0 1 v670 v670 := (r_land hl h_v149 h_v669 (of_decide_eq_true rfl))
  have e_v670 : (v670 = 1 ↔ v149 = 1 ∧ v669 = 1) := e_land h_v149 h_v669 (of_decide_eq_true rfl)
  have h_v671 : R 1 0 0 1 v671 v671 := (r_lor hl h_v148 h_v670 (of_decide_eq_true rfl))
  have e_v671 : (v671 = 1 ↔ v148 = 1 ∨ v670 = 1) := e_lor h_v148 h_v670 (of_decide_eq_true rfl)
  have h_v672 : R 1 0 4611686018427387900 4611686018695823367 v672 v672 := (r_psel hl h_v671 h_v658 h_v651 (of_decide_eq_true rfl))
  have e_v672 : v672 = if v671 = 1 then v658 else v651 := e_psel h_v671 h_v658 h_v651 (of_decide_eq_true rfl)
  have h_v673 : R 1 0 0 1 v673 v673 := (r_land hl h_v148 h_v664 (of_decide_eq_true rfl))
  have e_v673 : (v673 = 1 ↔ v148 = 1 ∧ v664 = 1) := e_land h_v148 h_v664 (of_decide_eq_true rfl)
  exact fun _ k => k e_v0 e_v1 e_v2 e_v3 e_v4 e_v5 e_v6 e_v7 e_v9 e_v10 e_v11 e_v12 h_v13 e_v13 e_v15 e_v19 e_v20 e_v21 e_v22 h_v23 e_v23 e_t0_1 e_t0_2 e_t1_1 e_t1_2 e_v26 e_v27 e_v28 h_v29 e_v29 e_v30 e_v31 e_v32 e_v33 e_v34 e_v35 e_v36 e_v37 e_v38 e_v39 e_v40 h_v41 e_v41 h_v42 e_v42 h_v43 e_v43 e_v44 e_v45 h_v46 e_v46 h_v47 e_v47 h_t42_1 e_t42_1 e_t42_2 h_t43_1 e_t43_1 e_t43_2 e_v50 e_v51 h_v52 e_v52 e_v53 e_v54 e_v55 e_v56 e_v57 h_v58 e_v58 e_v59 h_v60 e_v60 e_v61 e_v62 h_v63 e_v63 e_v64 e_v65 h_v66 e_v66 h_v67 e_v67 e_v68 e_v70 e_v71 h_v72 e_v72 h_v73 e_v73 e_v74 e_v75 e_v76 e_v77 h_v78 e_v78 e_v79 e_v80 e_v81 e_v82 e_v83 e_v84 e_v85 e_v86 e_v87 e_v88 e_v89 e_v90 e_v91 e_v92 e_v93 e_v94 e_v95 e_v96 e_v97 e_v98 e_v99 h_v100 e_v100 h_v101 e_v101 h_v102 e_v102 e_v104 e_v105 e_v106 e_v107 e_v108 e_v109 h_v110 e_v110 e_v112 e_v113 e_v114 e_v115 e_v116 h_v117 e_v117 h_v118 e_v118 e_v119 h_v120 e_v120 e_v122 e_v123 e_v124 e_v125 h_v126 e_v126 h_t118_1 e_t118_1 e_v134 e_v135 e_v136 e_v137 e_v138 e_v139 e_v140 e_v141 e_v142 e_v143 e_v144 h_v145 e_v145 e_v146 e_v147 h_v148 e_v148 h_v149 e_v149 e_v150 e_v152 e_v153 e_v154 e_v155 e_v156 e_v157 e_v158 e_v159 e_v160 e_v161 e_v162 e_v163 e_v164 e_v165 e_v166 e_v167 e_v168 e_v169 e_v170 e_v171 e_v172 e_v173 e_v174 e_v175 e_v176 e_v177 e_v178 e_v179 e_v180 e_v181 e_v182 e_v183 e_v184 e_v185 h_v186 e_v186 e_v187 e_v190 e_v191 e_v192 e_v193 e_t192_1 e_t192_2 e_v195 e_v196 e_v197 e_v198 e_v199 e_v200 e_v202 e_v203 e_v204 e_v205 e_v206 e_v207 e_v208 e_v209 e_v210 e_v211 e_v212 e_v213 e_v214 e_v215 e_v216 e_v217 e_v218 e_v219 e_v220 e_v221 e_v222 e_v223 e_v224 e_v225 e_v226 e_v227 e_v228 e_v229 e_v230 e_v231 e_v232 e_v233 h_v275 e_v275 h_v277 e_v277 e_v278 e_v279 h_v280 e_v280 e_v288 e_v289 e_v290 e_v291 h_v292 e_v292 e_t277_1 e_v294 e_v295 e_v296 e_v297 e_v298 e_v299 e_v300 e_v301 e_v302 e_v303 e_v304 e_v306 e_v307 e_v308 e_v309 e_v310 e_v311 e_v312 e_v313 e_v314 e_v315 e_v316 e_v317 e_v318 e_v319 e_v320 e_v321 e_v322 e_v323 e_v324 e_v325 e_v326 e_v327 e_v328 e_v329 e_v330 e_v331 e_v332 e_v333 e_v334 e_v335 e_v336 e_v337 e_v338 e_v339 e_v342 e_v343 e_v385 e_v386 e_v387 e_t387_1 e_t387_2 e_v389 e_v390 e_v391 e_v392 e_v393 e_v394 e_v396 e_v397 e_v398 e_v399 e_v400 e_v401 e_v402 e_v403 e_v404 e_v405 e_v406 e_v407 e_v408 e_v409 e_v410 e_v411 e_v412 e_v413 e_v414 e_v415 e_v416 e_v417 e_v418 e_v419 e_v420 e_v421 e_v422 e_v423 e_v424 e_v425 h_v427 e_v427 h_v428 e_v428 h_v429 e_v429 e_v430 e_v431 h_v432 e_v432 h_v433 e_v433 h_t428_1 e_t428_1 e_t428_2 h_t429_1 e_t429_1 e_t429_2 e_v436 e_v437 h_v438 e_v438 e_v439 e_v440 e_v441 e_v442 e_v443 h_v444 e_v444 e_v445 h_v446 e_v446 e_v447 e_v449 e_v450 h_v451 e_v451 h_v452 e_v452 e_v453 e_v454 e_v455 e_v456 h_v457 e_v457 e_v458 e_v459 e_v460 e_v461 e_v462 e_v463 e_v464 e_v465 e_v466 e_v467 e_v468 e_v469 e_v470 e_v471 e_v472 e_v473 e_v474 e_v475 e_v476 e_v477 e_v478 h_v479 e_v479 h_v480 e_v480 h_v481 e_v481 h_v482 e_v482 e_v483 h_v484 e_v484 e_v486 e_v487 e_v488 e_v489 h_v490 e_v490 h_t482_1 e_t482_1 e_v498 e_v499 e_v500 e_v501 e_v502 e_v503 e_v504 e_v505 e_v506 e_v507 e_v508 e_v510 e_v511 e_v512 e_v513 e_v514 e_v515 e_v516 e_v517 e_v518 e_v519 e_v520 e_v521 e_v522 e_v523 e_v524 e_v525 e_v526 e_v527 e_v528 e_v529 e_v530 e_v531 e_v532 e_v533 e_v534 e_v535 e_v536 e_v537 e_v538 e_v539 e_v540 e_v541 e_v542 e_v543 h_v544 e_v544 e_v545 e_v548 e_v549 e_v550 e_v551 e_t550_1 e_t550_2 e_v553 e_v554 e_v555 e_v556 e_v557 e_v558 e_v560 e_v561 e_v562 e_v563 e_v564 e_v565 e_v566 e_v567 e_v568 e_v569 e_v570 e_v571 e_v572 e_v573 e_v574 e_v575 e_v576 e_v577 e_v578 e_v579 e_v580 e_v581 e_v582 e_v583 e_v584 e_v585 e_v586 e_v587 e_v588 h_v630 e_v630 h_v632 e_v632 e_v633 e_v634 h_v635 e_v635 e_v643 e_v644 e_v645 e_v646 h_v647 e_v647 e_t632_1 e_v649 e_v650 h_v651 e_v651 e_v652 e_v653 e_v654 e_v655 e_v656 e_v657 h_v658 e_v658 e_v659 e_v661 e_v662 h_v663 e_v663 e_v664 h_v665 e_v665 e_v666 e_v667 h_v668 e_v668 e_v669 e_v670 e_v671 h_v672 e_v672 h_v673 e_v673

end Tammes15.D3Trig
