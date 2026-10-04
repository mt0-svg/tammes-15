import Tammes15.D3Trig.Prog.HFH
import Tammes15.D3Prog.Sem

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progHFH_seg0 (F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) :
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
    let v9 := Nat.mul 1 4611686018427387904
    let v10 := Nat.mul 1 4611686020114017616
    let v14 := Nat.mul 1 4611686019270702760
    let v15 := plt 1 v14 v7
    let v16 := Nat.sub 1 v15
    let v18 := Nat.mul 1 4611686018427387903
    let v19 := plt 1 v18 v0
    let v20 := Nat.mul 1 4611686019270702761
    let v21 := plt 1 v20 v1
    let v22 := Nat.sub 1 v21
    let v23 := Nat.land v19 v22
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
    let v44 := plt 1 v18 v42
    let v45 := plt 1 v20 v43
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
    let v61 := plt 1 v29 v9
    let v62 := Nat.sub 1 v61
    let v63 := plt 1 v9 v41
    let v64 := Nat.sub 1 v63
    let v65 := Nat.land v61 v64
    let v66 := Nat.land v61 v63
    let v67 := plt 1 v52 v9
    let v69 := plt 1 v9 v60
    let v70 := Nat.sub 1 v69
    let v71 := Nat.land v67 v70
    let v72 := Nat.land v67 v69
    let v73 := Nat.land v66 v72
    let v74 := Nat.land v62 v72
    let v75 := Nat.lor v71 v74
    let v76 := psel (pmask v75) v41 v29
    let v77 := Nat.sub 1 v71
    let v78 := Nat.land v66 v77
    let v79 := Nat.lor v65 v78
    let v80 := psel (pmask v79) v60 v52
    let v81 := Nat.land v65 v72
    let v82 := Nat.lor v71 v81
    let v83 := psel (pmask v82) v29 v41
    let v84 := Nat.land v66 v71
    let v85 := Nat.lor v65 v84
    let v86 := psel (pmask v85) v52 v60
    let v87 := smx 29 1 v80 v76
    let v88 := srdF 1 v87
    let v89 := smx 29 1 v86 v83
    let v90 := srdC 1 v89
    let v91 := smx 29 1 v52 v41
    let v92 := srdF 1 v91
    let v93 := smx 29 1 v52 v29
    let v94 := srdC 1 v93
    let v95 := plt 1 v88 v92
    let v96 := psel (pmask v95) v88 v92
    let v97 := plt 1 v90 v94
    let v98 := psel (pmask v97) v94 v90
    let v99 := psel (pmask v73) v96 v88
    let v100 := psel (pmask v73) v98 v90
    let v101 := plt 1 v18 v99
    let v103 := Nat.sub (Nat.add v28 t1.2) OFFr
    let v104 := Nat.mul 1 4611686018158952448
    let v105 := plt 1 v103 v104
    let v106 := psel (pmask v105) v104 v103
    let v107 := Nat.mul 1 4611686019270702759
    let v108 := plt 1 v107 v1
    let v109 := psel (pmask v108) v104 v106
    let v111 := Nat.sub (Nat.add v31 t0.2) OFFr
    let v112 := plt 1 v111 v33
    let v113 := psel (pmask v112) v111 v33
    let v114 := Nat.mul 1 4611686018427387905
    let v115 := plt 1 v0 v114
    let v116 := psel (pmask v115) v33 v113
    let v117 := Nat.add (pshr1 1 v3) H61r
    let v118 := plt 1 v18 v117
    let v119 := Nat.land v46 v118
    let v121 := Nat.sub (Nat.add v28 t43.2) OFFr
    let v122 := plt 1 v121 v104
    let v123 := psel (pmask v122) v104 v121
    let v124 := plt 1 v107 v43
    let v125 := psel (pmask v124) v104 v123
    let v143 := plt 1 v109 v9
    let v144 := Nat.sub 1 v143
    let v145 := plt 1 v9 v116
    let v146 := Nat.sub 1 v145
    let v147 := Nat.land v143 v146
    let v148 := Nat.land v143 v145
    let v185 := plt 1 v125 v9
    let v215 := Nat.mul 1 4611686018849045332
    let v222 := Nat.mul 1 4611686018849045333
    let v276 := Nat.add (pshr1 1 (Nat.add v2 1)) H61r
    let v277 := plt 1 v20 v276
    let v278 := Nat.sub 1 v277
    let v279 := Nat.land v44 v278
    let v287 := Nat.sub (Nat.add v31 t42.2) OFFr
    let v288 := plt 1 v287 v33
    let v289 := psel (pmask v288) v287 v33
    let v290 := plt 1 v42 v114
    let v291 := psel (pmask v290) v33 v289
    let t276 := sc28u 1 v276
    let v293 := plt 1 t42.1 t276.1
    let v294 := psel (pmask v293) t42.1 t276.1
    let v295 := Nat.sub (Nat.add v28 v294) OFFr
    let v296 := psel (pmask v293) t276.1 t42.1
    let v297 := Nat.sub (Nat.add v31 v296) OFFr
    let v298 := plt 1 v297 v33
    let v299 := psel (pmask v298) v297 v33
    let v300 := plt 1 v38 v276
    let v301 := Nat.land v57 v300
    let v302 := psel (pmask v301) v33 v299
    let v303 := plt 1 v295 v9
    let v305 := plt 1 v9 v302
    let v306 := Nat.sub 1 v305
    let v307 := Nat.land v303 v306
    let v308 := Nat.land v303 v305
    let v309 := Nat.land v148 v308
    let v310 := Nat.land v144 v308
    let v311 := Nat.lor v307 v310
    let v312 := psel (pmask v311) v116 v109
    let v313 := Nat.sub 1 v307
    let v314 := Nat.land v148 v313
    let v315 := Nat.lor v147 v314
    let v316 := psel (pmask v315) v302 v295
    let v317 := Nat.land v147 v308
    let v318 := Nat.lor v307 v317
    let v319 := psel (pmask v318) v109 v116
    let v320 := Nat.land v148 v307
    let v321 := Nat.lor v147 v320
    let v322 := psel (pmask v321) v295 v302
    let v323 := smx 29 1 v316 v312
    let v324 := srdF 1 v323
    let v325 := smx 29 1 v322 v319
    let v326 := srdC 1 v325
    let v327 := smx 29 1 v295 v116
    let v328 := srdF 1 v327
    let v329 := smx 29 1 v295 v109
    let v330 := srdC 1 v329
    let v331 := plt 1 v324 v328
    let v332 := psel (pmask v331) v324 v328
    let v333 := plt 1 v326 v330
    let v334 := psel (pmask v333) v330 v326
    let v335 := psel (pmask v309) v332 v324
    let v336 := psel (pmask v309) v334 v326
    let v337 := plt 1 v9 v335
    let v338 := Nat.sub 1 v337
    let v341 := plt 1 v291 v9
    let v342 := psel (pmask v341) v336 v335
    let v384 := Nat.sub (Nat.add v9 OFFr) v291
    let v385 := psel (pmask v341) v384 v291
    let v386 := hxa 1 H0 0
    let t386 := sc28u 1 v386
    let v388 := Nat.sub (Nat.add v28 t386.2) OFFr
    let v389 := plt 1 v388 v104
    let v390 := psel (pmask v389) v104 v388
    let v391 := Nat.sub (Nat.add v31 t386.2) OFFr
    let v392 := plt 1 v391 v33
    let v393 := psel (pmask v392) v391 v33
    let v395 := Nat.sub (Nat.add v31 t386.1) OFFr
    let v396 := plt 1 v395 v33
    let v397 := psel (pmask v396) v395 v33
    let v398 := Nat.sub (Nat.add v28 t386.1) OFFr
    let v399 := psel (pmask v341) v390 v393
    let v400 := psel (pmask v341) v397 v398
    let v401 := smx 29 1 v342 v400
    let v402 := smx 29 1 v399 v385
    let v403 := plt 1 v402 v401
    let v404 := Nat.sub 1 v403
    let v405 := plt 1 v401 v402
    let v406 := Nat.sub 1 v405
    let v407 := plt 1 v9 v386
    let v408 := Nat.sub 1 v407
    let v409 := plt 1 v215 v386
    let v410 := Nat.sub 1 v409
    let v411 := plt 1 v18 v390
    let v412 := Nat.land v404 v411
    let v413 := Nat.land v410 v412
    let v414 := Nat.lor v408 v413
    let v415 := plt 1 v386 v222
    let v416 := Nat.sub 1 v415
    let v417 := Nat.lor v406 v416
    let v418 := Nat.land v341 v414
    let v419 := Nat.sub 1 v341
    let v420 := Nat.land v417 v419
    let v421 := Nat.lor v418 v420
    let v422 := Nat.sub (Nat.add v9 OFFr) v386
    let v423 := psel (pmask v341) v422 v386
    let v424 := psel (pmask v421) v423 v222
    let v426 := psel (pmask v338) v222 v424
    let v427 := Nat.add (pshr1 1 v4) H61r
    let v428 := Nat.add (pshr1 1 (Nat.add v5 1)) H61r
    let v429 := plt 1 v18 v427
    let v430 := plt 1 v20 v428
    let v431 := Nat.sub 1 v430
    let v432 := Nat.land v429 v431
    let t427 := sc28u 1 v427
    let t428 := sc28u 1 v428
    let v435 := plt 1 t427.1 t428.1
    let v436 := psel (pmask v435) t427.1 t428.1
    let v437 := Nat.sub (Nat.add v28 v436) OFFr
    let v438 := psel (pmask v435) t428.1 t427.1
    let v439 := Nat.sub (Nat.add v31 v438) OFFr
    let v440 := plt 1 v439 v33
    let v441 := psel (pmask v440) v439 v33
    let v442 := plt 1 v427 v36
    let v443 := plt 1 v38 v428
    let v444 := Nat.land v442 v443
    let v445 := psel (pmask v444) v33 v441
    let v446 := plt 1 v437 v9
    let v448 := plt 1 v9 v445
    let v449 := Nat.sub 1 v448
    let v450 := Nat.land v446 v449
    let v451 := Nat.land v446 v448
    let v452 := Nat.land v66 v451
    let v453 := Nat.land v62 v451
    let v454 := Nat.lor v450 v453
    let v455 := psel (pmask v454) v41 v29
    let v456 := Nat.sub 1 v450
    let v457 := Nat.land v66 v456
    let v458 := Nat.lor v65 v457
    let v459 := psel (pmask v458) v445 v437
    let v460 := Nat.land v65 v451
    let v461 := Nat.lor v450 v460
    let v462 := psel (pmask v461) v29 v41
    let v463 := Nat.land v66 v450
    let v464 := Nat.lor v65 v463
    let v465 := psel (pmask v464) v437 v445
    let v466 := smx 29 1 v459 v455
    let v467 := srdF 1 v466
    let v468 := smx 29 1 v465 v462
    let v469 := srdC 1 v468
    let v470 := smx 29 1 v437 v41
    let v471 := srdF 1 v470
    let v472 := smx 29 1 v437 v29
    let v473 := srdC 1 v472
    let v474 := plt 1 v467 v471
    let v475 := psel (pmask v474) v467 v471
    let v476 := plt 1 v469 v473
    let v477 := psel (pmask v476) v473 v469
    let v478 := psel (pmask v452) v475 v467
    let v479 := psel (pmask v452) v477 v469
    let v480 := plt 1 v18 v478
    let v481 := Nat.add (pshr1 1 v5) H61r
    let v482 := plt 1 v18 v481
    let v483 := Nat.land v431 v482
    let v485 := Nat.sub (Nat.add v28 t428.2) OFFr
    let v486 := plt 1 v485 v104
    let v487 := psel (pmask v486) v104 v485
    let v488 := plt 1 v107 v428
    let v489 := psel (pmask v488) v104 v487
    let v543 := plt 1 v489 v9
    let v631 := Nat.add (pshr1 1 (Nat.add v4 1)) H61r
    let v632 := plt 1 v20 v631
    let v633 := Nat.sub 1 v632
    let v634 := Nat.land v429 v633
    let v642 := Nat.sub (Nat.add v31 t427.2) OFFr
    let v643 := plt 1 v642 v33
    let v644 := psel (pmask v643) v642 v33
    let v645 := plt 1 v427 v114
    let v646 := psel (pmask v645) v33 v644
    let t631 := sc28u 1 v631
    let v648 := plt 1 t427.1 t631.1
    let v649 := psel (pmask v648) t427.1 t631.1
    let v650 := Nat.sub (Nat.add v28 v649) OFFr
    let v651 := psel (pmask v648) t631.1 t427.1
    let v652 := Nat.sub (Nat.add v31 v651) OFFr
    let v653 := plt 1 v652 v33
    let v654 := psel (pmask v653) v652 v33
    let v655 := plt 1 v38 v631
    let v656 := Nat.land v442 v655
    let v657 := psel (pmask v656) v33 v654
    let v658 := plt 1 v650 v9
    let v660 := plt 1 v9 v657
    let v661 := Nat.sub 1 v660
    let v662 := Nat.land v658 v661
    let v663 := Nat.land v658 v660
    let v664 := Nat.land v148 v663
    let v665 := Nat.land v144 v663
    let v666 := Nat.lor v662 v665
    let v667 := psel (pmask v666) v116 v109
    let v668 := Nat.sub 1 v662
    let v669 := Nat.land v148 v668
    let v670 := Nat.lor v147 v669
    let v671 := psel (pmask v670) v657 v650
    let v672 := Nat.land v147 v663
    let v673 := Nat.lor v662 v672
    let v674 := psel (pmask v673) v109 v116
    let v675 := Nat.land v148 v662
    let v676 := Nat.lor v147 v675
    let v677 := psel (pmask v676) v650 v657
    let v678 := smx 29 1 v671 v667
    let v679 := srdF 1 v678
    let v680 := smx 29 1 v677 v674
    let v681 := srdC 1 v680
    let v682 := smx 29 1 v650 v116
    let v683 := srdF 1 v682
    let v684 := smx 29 1 v650 v109
    let v685 := srdC 1 v684
    let v686 := plt 1 v679 v683
    let v687 := psel (pmask v686) v679 v683
    let v688 := plt 1 v681 v685
    let v689 := psel (pmask v688) v685 v681
    let v690 := psel (pmask v664) v687 v679
    let v691 := psel (pmask v664) v689 v681
    let v692 := plt 1 v9 v690
    let v693 := Nat.sub 1 v692
    let v696 := plt 1 v646 v9
    let v697 := psel (pmask v696) v691 v690
    let v739 := Nat.sub (Nat.add v9 OFFr) v646
    let v740 := psel (pmask v696) v739 v646
    let v741 := hxa 1 H0 32
    let t741 := sc28u 1 v741
    let v743 := Nat.sub (Nat.add v28 t741.2) OFFr
    let v744 := plt 1 v743 v104
    let v745 := psel (pmask v744) v104 v743
    let v746 := Nat.sub (Nat.add v31 t741.2) OFFr
    let v747 := plt 1 v746 v33
    let v748 := psel (pmask v747) v746 v33
    let v750 := Nat.sub (Nat.add v31 t741.1) OFFr
    let v751 := plt 1 v750 v33
    let v752 := psel (pmask v751) v750 v33
    let v753 := Nat.sub (Nat.add v28 t741.1) OFFr
    let v754 := psel (pmask v696) v745 v748
    let v755 := psel (pmask v696) v752 v753
    let v756 := smx 29 1 v697 v755
    let v757 := smx 29 1 v754 v740
    let v758 := plt 1 v757 v756
    let v759 := Nat.sub 1 v758
    let v760 := plt 1 v756 v757
    let v761 := Nat.sub 1 v760
    let v762 := plt 1 v9 v741
    let v763 := Nat.sub 1 v762
    let v764 := plt 1 v215 v741
    let v765 := Nat.sub 1 v764
    let v766 := plt 1 v18 v745
    let v767 := Nat.land v759 v766
    let v768 := Nat.land v765 v767
    let v769 := Nat.lor v763 v768
    let v770 := plt 1 v741 v222
    let v771 := Nat.sub 1 v770
    let v772 := Nat.lor v761 v771
    let v773 := Nat.land v696 v769
    let v774 := Nat.sub 1 v696
    let v775 := Nat.land v772 v774
    let v776 := Nat.lor v773 v775
    let v777 := Nat.sub (Nat.add v9 OFFr) v741
    let v778 := psel (pmask v696) v777 v741
    let v779 := psel (pmask v776) v778 v222
    let v781 := psel (pmask v693) v222 v779
    let v782 := Nat.add (pshr1 1 v7) H61r
    let v783 := psel (pmask v16) v782 v215
    let v784 := Nat.add (pshr1 1 (Nat.add v7 1)) H61r
    let v785 := plt 1 v18 v783
    let v786 := plt 1 v20 v784
    let v787 := Nat.sub 1 v786
    let v788 := Nat.land v785 v787
    let t783 := sc28u 1 v783
    let t784 := sc28u 1 v784
    let v791 := plt 1 t783.1 t784.1
    let v792 := psel (pmask v791) t783.1 t784.1
    let v793 := Nat.sub (Nat.add v28 v792) OFFr
    let v794 := psel (pmask v791) t784.1 t783.1
    let v795 := Nat.sub (Nat.add v31 v794) OFFr
    let v796 := plt 1 v795 v33
    let v797 := psel (pmask v796) v795 v33
    let v798 := plt 1 v783 v36
    let v799 := plt 1 v38 v784
    let v800 := Nat.land v798 v799
    let v801 := psel (pmask v800) v33 v797
    let v802 := plt 1 v793 v9
    let v804 := plt 1 v9 v801
    let v805 := Nat.sub 1 v804
    let v806 := Nat.land v802 v805
    let v807 := Nat.land v802 v804
    let v808 := Nat.land v66 v807
    let v809 := Nat.land v62 v807
    let v810 := Nat.lor v806 v809
    let v811 := psel (pmask v810) v41 v29
    let v812 := Nat.sub 1 v806
    let v813 := Nat.land v66 v812
    let v814 := Nat.lor v65 v813
    let v815 := psel (pmask v814) v801 v793
    let v816 := Nat.land v65 v807
    let v817 := Nat.lor v806 v816
    let v818 := psel (pmask v817) v29 v41
    let v819 := Nat.land v66 v806
    let v820 := Nat.lor v65 v819
    let v821 := psel (pmask v820) v793 v801
    let v822 := smx 29 1 v815 v811
    let v823 := srdF 1 v822
    let v824 := smx 29 1 v821 v818
    let v825 := srdC 1 v824
    let v826 := smx 29 1 v793 v41
    let v827 := srdF 1 v826
    let v828 := smx 29 1 v793 v29
    let v829 := srdC 1 v828
    let v830 := plt 1 v823 v827
    let v831 := psel (pmask v830) v823 v827
    let v832 := plt 1 v825 v829
    let v833 := psel (pmask v832) v829 v825
    let v834 := psel (pmask v808) v831 v823
    let v835 := psel (pmask v808) v833 v825
    let v836 := plt 1 v18 v834
    let v837 := plt 1 v9 v478
    let v838 := plt 1 v479 v33
    let v839 := Nat.land v837 v838
    let v840 := plt 1 v9 v99
    let v841 := plt 1 v100 v33
    let v842 := Nat.land v840 v841
    let v843 := plt 1 v9 v834
    let v844 := plt 1 v835 v33
    let v845 := Nat.land v843 v844
    let v846 := Nat.land v839 v842
    let v847 := Nat.land v845 v846
    let v848 := smx 29 1 v479 v479
    let v849 := srdC 1 v848
    let v850 := Nat.sub (Nat.add v849 v849) OFFr
    let v851 := Nat.sub (Nat.add v33 OFFr) v850
    let v852 := plt 1 v851 v104
    let v853 := psel (pmask v852) v104 v851
    let v854 := smx 29 1 v478 v478
    let v855 := srdF 1 v854
    let v856 := Nat.sub (Nat.add v855 v855) OFFr
    let v857 := Nat.sub (Nat.add v33 OFFr) v856
    let v858 := smx 29 1 v835 v835
    let v859 := srdC 1 v858
    let v860 := Nat.sub (Nat.add v859 v859) OFFr
    let v861 := Nat.sub (Nat.add v33 OFFr) v860
    let v862 := plt 1 v861 v104
    let v863 := psel (pmask v862) v104 v861
    let v864 := smx 29 1 v834 v834
    let v865 := srdF 1 v864
    let v866 := Nat.sub (Nat.add v865 v865) OFFr
    let v867 := Nat.sub (Nat.add v33 OFFr) v866
    let v868 := smx 29 1 v100 v100
    let v869 := srdC 1 v868
    let v870 := Nat.sub (Nat.add v869 v869) OFFr
    let v871 := Nat.sub (Nat.add v33 OFFr) v870
    let v872 := plt 1 v871 v104
    let v873 := psel (pmask v872) v104 v871
    let v874 := smx 29 1 v99 v99
    let v875 := srdF 1 v874
    let v876 := Nat.sub (Nat.add v875 v875) OFFr
    let v877 := Nat.sub (Nat.add v33 OFFr) v876
    let v878 := plt 1 v853 v9
    let v879 := Nat.sub 1 v878
    let v880 := plt 1 v9 v857
    let v881 := Nat.sub 1 v880
    let v882 := Nat.land v878 v881
    let v883 := Nat.land v878 v880
    let v884 := plt 1 v873 v9
    let v885 := Nat.sub 1 v884
    let v886 := plt 1 v9 v877
    let v887 := Nat.sub 1 v886
    let v888 := Nat.land v884 v887
    let v889 := Nat.land v884 v886
    let v890 := Nat.land v883 v889
    let v891 := Nat.land v879 v889
    let v892 := Nat.lor v888 v891
    let v893 := psel (pmask v892) v857 v853
    let v894 := Nat.sub 1 v888
    let v895 := Nat.land v883 v894
    let v896 := Nat.lor v882 v895
    ∀ (P : Prop), ((sv v0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v2 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v3 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v4 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v5 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v6 = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v7 = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) → (sv v9 = (0)) → (sv v10 = (1686629712)) → (sv v14 = (843314856)) → ((v15 = 1 ↔ sv v14 < sv v7)) → ((v16 = 1 ↔ ¬v15 = 1)) → (sv v18 = (-1)) → ((v19 = 1 ↔ sv v18 < sv v0)) → (sv v20 = (843314857)) → ((v21 = 1 ↔ sv v20 < sv v1)) → ((v22 = 1 ↔ ¬v21 = 1)) → (R 1 0 0 1 v23 v23) → ((v23 = 1 ↔ v19 = 1 ∧ v22 = 1)) → (sv t0.1 = (sc28pS (scArg v0)).1) → (sv t0.2 = (sc28pS (scArg v0)).2) → (sv t1.1 = (sc28pS (scArg v1)).1) → (sv t1.2 = (sc28pS (scArg v1)).2) → ((v26 = 1 ↔ sv t0.1 < sv t1.1)) → (v27 = if v26 = 1 then t0.1 else t1.1) → (sv v28 = (-4)) → (R 1 0 4611686018427387900 4611686018695823359 v29 v29) → (sv v29 = sv v27 + sv v28) → (v30 = if v26 = 1 then t1.1 else t0.1) → (sv v31 = (4)) → (sv v32 = sv v30 + sv v31) → (sv v33 = (268435456)) → ((v34 = 1 ↔ sv v32 < sv v33)) → (v35 = if v34 = 1 then v32 else v33) → (sv v36 = (421657430)) → ((v37 = 1 ↔ sv v0 < sv v36)) → (sv v38 = (421657427)) → ((v39 = 1 ↔ sv v38 < sv v1)) → ((v40 = 1 ↔ v37 = 1 ∧ v39 = 1)) → (R 1 0 4611686018427387908 4611686018695823367 v41 v41) → (v41 = if v40 = 1 then v33 else v35) → (R 1 0 4611686018427387904 4611686052787126264 v42 v42) → (sv v42 = sv v2 / 2) → (R 1 0 4611686018427387904 4611686052787126264 v43 v43) → (sv v43 = (sv v3 + 1) / 2) → (R 1 0 0 1 v44 v44) → ((v44 = 1 ↔ sv v18 < sv v42)) → ((v45 = 1 ↔ sv v20 < sv v43)) → ((v46 = 1 ↔ ¬v45 = 1)) → (R 1 0 0 1 v47 v47) → ((v47 = 1 ↔ v44 = 1 ∧ v46 = 1)) → (R 1 0 4611686018427387904 4611686018695823363 t42.1 t42.1) → (sv t42.1 = (sc28pS (scArg v42)).1) → (sv t42.2 = (sc28pS (scArg v42)).2) → (R 1 0 4611686018427387904 4611686018695823363 t43.1 t43.1) → (sv t43.1 = (sc28pS (scArg v43)).1) → (sv t43.2 = (sc28pS (scArg v43)).2) → ((v50 = 1 ↔ sv t42.1 < sv t43.1)) → (v51 = if v50 = 1 then t42.1 else t43.1) → (R 1 0 4611686018427387900 4611686018695823359 v52 v52) → (sv v52 = sv v28 + sv v51) → (v53 = if v50 = 1 then t43.1 else t42.1) → (sv v54 = sv v31 + sv v53) → ((v55 = 1 ↔ sv v54 < sv v33)) → (v56 = if v55 = 1 then v54 else v33) → (R 1 0 0 1 v57 v57) → ((v57 = 1 ↔ sv v42 < sv v36)) → ((v58 = 1 ↔ sv v38 < sv v43)) → ((v59 = 1 ↔ v57 = 1 ∧ v58 = 1)) → (R 1 0 4611686018427387908 4611686018695823367 v60 v60) → (v60 = if v59 = 1 then v33 else v56) → ((v61 = 1 ↔ sv v29 < sv v9)) → (R 1 0 0 1 v62 v62) → ((v62 = 1 ↔ ¬v61 = 1)) → ((v63 = 1 ↔ sv v9 < sv v41)) → ((v64 = 1 ↔ ¬v63 = 1)) → (R 1 0 0 1 v65 v65) → ((v65 = 1 ↔ v61 = 1 ∧ v64 = 1)) → (R 1 0 0 1 v66 v66) → ((v66 = 1 ↔ v61 = 1 ∧ v63 = 1)) → ((v67 = 1 ↔ sv v52 < sv v9)) → ((v69 = 1 ↔ sv v9 < sv v60)) → ((v70 = 1 ↔ ¬v69 = 1)) → (R 1 0 0 1 v71 v71) → ((v71 = 1 ↔ v67 = 1 ∧ v70 = 1)) → (R 1 0 0 1 v72 v72) → ((v72 = 1 ↔ v67 = 1 ∧ v69 = 1)) → ((v73 = 1 ↔ v66 = 1 ∧ v72 = 1)) → ((v74 = 1 ↔ v62 = 1 ∧ v72 = 1)) → ((v75 = 1 ↔ v71 = 1 ∨ v74 = 1)) → (v76 = if v75 = 1 then v41 else v29) → (R 1 0 0 1 v77 v77) → ((v77 = 1 ↔ ¬v71 = 1)) → ((v78 = 1 ↔ v66 = 1 ∧ v77 = 1)) → ((v79 = 1 ↔ v65 = 1 ∨ v78 = 1)) → (v80 = if v79 = 1 then v60 else v52) → ((v81 = 1 ↔ v65 = 1 ∧ v72 = 1)) → ((v82 = 1 ↔ v71 = 1 ∨ v81 = 1)) → (v83 = if v82 = 1 then v29 else v41) → ((v84 = 1 ↔ v66 = 1 ∧ v71 = 1)) → ((v85 = 1 ↔ v65 = 1 ∨ v84 = 1)) → (v86 = if v85 = 1 then v52 else v60) → (sv v87 = sv v80 * sv v76) → (sv v88 = sv v87 / 2 ^ 28) → (sv v89 = sv v86 * sv v83) → (sv v90 = -((-sv v89) / 2 ^ 28)) → (sv v91 = sv v52 * sv v41) → (sv v92 = sv v91 / 2 ^ 28) → (sv v93 = sv v52 * sv v29) → (sv v94 = -((-sv v93) / 2 ^ 28)) → ((v95 = 1 ↔ sv v88 < sv v92)) → (v96 = if v95 = 1 then v88 else v92) → ((v97 = 1 ↔ sv v90 < sv v94)) → (v98 = if v97 = 1 then v94 else v90) → (R 1 0 4611686018427387899 4611686018695823374 v99 v99) → (v99 = if v73 = 1 then v96 else v88) → (R 1 0 4611686018427387900 4611686018695823375 v100 v100) → (v100 = if v73 = 1 then v98 else v90) → (R 1 0 0 1 v101 v101) → ((v101 = 1 ↔ sv v18 < sv v99)) → (sv v103 = sv v28 + sv t1.2) → (sv v104 = (-268435456)) → ((v105 = 1 ↔ sv v103 < sv v104)) → (v106 = if v105 = 1 then v104 else v103) → (sv v107 = (843314855)) → ((v108 = 1 ↔ sv v107 < sv v1)) → (R 1 0 4611686018158952441 4611686018695823359 v109 v109) → (v109 = if v108 = 1 then v104 else v106) → (sv v111 = sv v31 + sv t0.2) → ((v112 = 1 ↔ sv v111 < sv v33)) → (v113 = if v112 = 1 then v111 else v33) → (sv v114 = (1)) → ((v115 = 1 ↔ sv v0 < sv v114)) → (R 1 0 4611686018158952449 4611686018695823367 v116 v116) → (v116 = if v115 = 1 then v33 else v113) → (R 1 0 4611686018427387904 4611686052787126264 v117 v117) → (sv v117 = sv v3 / 2) → ((v118 = 1 ↔ sv v18 < sv v117)) → (R 1 0 0 1 v119 v119) → ((v119 = 1 ↔ v46 = 1 ∧ v118 = 1)) → (sv v121 = sv v28 + sv t43.2) → ((v122 = 1 ↔ sv v121 < sv v104)) → (v123 = if v122 = 1 then v104 else v121) → ((v124 = 1 ↔ sv v107 < sv v43)) → (R 1 0 4611686018158952441 4611686018695823359 v125 v125) → (v125 = if v124 = 1 then v104 else v123) → ((v143 = 1 ↔ sv v109 < sv v9)) → (R 1 0 0 1 v144 v144) → ((v144 = 1 ↔ ¬v143 = 1)) → ((v145 = 1 ↔ sv v9 < sv v116)) → ((v146 = 1 ↔ ¬v145 = 1)) → (R 1 0 0 1 v147 v147) → ((v147 = 1 ↔ v143 = 1 ∧ v146 = 1)) → (R 1 0 0 1 v148 v148) → ((v148 = 1 ↔ v143 = 1 ∧ v145 = 1)) → (R 1 0 0 1 v185 v185) → ((v185 = 1 ↔ sv v125 < sv v9)) → (sv v215 = (421657428)) → (sv v222 = (421657429)) → (R 1 0 4611686018427387904 4611686052787126264 v276 v276) → (sv v276 = (sv v2 + 1) / 2) → ((v277 = 1 ↔ sv v20 < sv v276)) → ((v278 = 1 ↔ ¬v277 = 1)) → (R 1 0 0 1 v279 v279) → ((v279 = 1 ↔ v44 = 1 ∧ v278 = 1)) → (sv v287 = sv v31 + sv t42.2) → ((v288 = 1 ↔ sv v287 < sv v33)) → (v289 = if v288 = 1 then v287 else v33) → ((v290 = 1 ↔ sv v42 < sv v114)) → (R 1 0 4611686018158952449 4611686018695823367 v291 v291) → (v291 = if v290 = 1 then v33 else v289) → (R 1 0 4611686018427387904 4611686018695823363 t276.1 t276.1) → (sv t276.1 = (sc28pS (scArg v276)).1) → ((v293 = 1 ↔ sv t42.1 < sv t276.1)) → (v294 = if v293 = 1 then t42.1 else t276.1) → (sv v295 = sv v28 + sv v294) → (v296 = if v293 = 1 then t276.1 else t42.1) → (sv v297 = sv v31 + sv v296) → ((v298 = 1 ↔ sv v297 < sv v33)) → (v299 = if v298 = 1 then v297 else v33) → ((v300 = 1 ↔ sv v38 < sv v276)) → ((v301 = 1 ↔ v57 = 1 ∧ v300 = 1)) → (v302 = if v301 = 1 then v33 else v299) → ((v303 = 1 ↔ sv v295 < sv v9)) → ((v305 = 1 ↔ sv v9 < sv v302)) → ((v306 = 1 ↔ ¬v305 = 1)) → ((v307 = 1 ↔ v303 = 1 ∧ v306 = 1)) → ((v308 = 1 ↔ v303 = 1 ∧ v305 = 1)) → ((v309 = 1 ↔ v148 = 1 ∧ v308 = 1)) → ((v310 = 1 ↔ v144 = 1 ∧ v308 = 1)) → ((v311 = 1 ↔ v307 = 1 ∨ v310 = 1)) → (v312 = if v311 = 1 then v116 else v109) → ((v313 = 1 ↔ ¬v307 = 1)) → ((v314 = 1 ↔ v148 = 1 ∧ v313 = 1)) → ((v315 = 1 ↔ v147 = 1 ∨ v314 = 1)) → (v316 = if v315 = 1 then v302 else v295) → ((v317 = 1 ↔ v147 = 1 ∧ v308 = 1)) → ((v318 = 1 ↔ v307 = 1 ∨ v317 = 1)) → (v319 = if v318 = 1 then v109 else v116) → ((v320 = 1 ↔ v148 = 1 ∧ v307 = 1)) → ((v321 = 1 ↔ v147 = 1 ∨ v320 = 1)) → (v322 = if v321 = 1 then v295 else v302) → (sv v323 = sv v316 * sv v312) → (sv v324 = sv v323 / 2 ^ 28) → (sv v325 = sv v322 * sv v319) → (sv v326 = -((-sv v325) / 2 ^ 28)) → (sv v327 = sv v295 * sv v116) → (sv v328 = sv v327 / 2 ^ 28) → (sv v329 = sv v295 * sv v109) → (sv v330 = -((-sv v329) / 2 ^ 28)) → ((v331 = 1 ↔ sv v324 < sv v328)) → (v332 = if v331 = 1 then v324 else v328) → ((v333 = 1 ↔ sv v326 < sv v330)) → (v334 = if v333 = 1 then v330 else v326) → (v335 = if v309 = 1 then v332 else v324) → (v336 = if v309 = 1 then v334 else v326) → ((v337 = 1 ↔ sv v9 < sv v335)) → ((v338 = 1 ↔ ¬v337 = 1)) → ((v341 = 1 ↔ sv v291 < sv v9)) → (v342 = if v341 = 1 then v336 else v335) → (sv v384 = sv v9 - sv v291) → (v385 = if v341 = 1 then v384 else v291) → (sv v386 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ)) → (sv t386.1 = (sc28pS (scArg v386)).1) → (sv t386.2 = (sc28pS (scArg v386)).2) → (sv v388 = sv v28 + sv t386.2) → ((v389 = 1 ↔ sv v388 < sv v104)) → (v390 = if v389 = 1 then v104 else v388) → (sv v391 = sv v31 + sv t386.2) → ((v392 = 1 ↔ sv v391 < sv v33)) → (v393 = if v392 = 1 then v391 else v33) → (sv v395 = sv v31 + sv t386.1) → ((v396 = 1 ↔ sv v395 < sv v33)) → (v397 = if v396 = 1 then v395 else v33) → (sv v398 = sv v28 + sv t386.1) → (v399 = if v341 = 1 then v390 else v393) → (v400 = if v341 = 1 then v397 else v398) → (sv v401 = sv v342 * sv v400) → (sv v402 = sv v399 * sv v385) → ((v403 = 1 ↔ sv v402 < sv v401)) → ((v404 = 1 ↔ ¬v403 = 1)) → ((v405 = 1 ↔ sv v401 < sv v402)) → ((v406 = 1 ↔ ¬v405 = 1)) → ((v407 = 1 ↔ sv v9 < sv v386)) → ((v408 = 1 ↔ ¬v407 = 1)) → ((v409 = 1 ↔ sv v215 < sv v386)) → ((v410 = 1 ↔ ¬v409 = 1)) → ((v411 = 1 ↔ sv v18 < sv v390)) → ((v412 = 1 ↔ v404 = 1 ∧ v411 = 1)) → ((v413 = 1 ↔ v410 = 1 ∧ v412 = 1)) → ((v414 = 1 ↔ v408 = 1 ∨ v413 = 1)) → ((v415 = 1 ↔ sv v386 < sv v222)) → ((v416 = 1 ↔ ¬v415 = 1)) → ((v417 = 1 ↔ v406 = 1 ∨ v416 = 1)) → ((v418 = 1 ↔ v341 = 1 ∧ v414 = 1)) → ((v419 = 1 ↔ ¬v341 = 1)) → ((v420 = 1 ↔ v417 = 1 ∧ v419 = 1)) → ((v421 = 1 ↔ v418 = 1 ∨ v420 = 1)) → (sv v422 = sv v9 - sv v386) → (v423 = if v341 = 1 then v422 else v386) → (v424 = if v421 = 1 then v423 else v222) → (R 1 0 4611686017353646081 4611686019501129727 v426 v426) → (v426 = if v338 = 1 then v222 else v424) → (R 1 0 4611686018427387904 4611686052787126264 v427 v427) → (sv v427 = sv v4 / 2) → (R 1 0 4611686018427387904 4611686052787126264 v428 v428) → (sv v428 = (sv v5 + 1) / 2) → (R 1 0 0 1 v429 v429) → ((v429 = 1 ↔ sv v18 < sv v427)) → ((v430 = 1 ↔ sv v20 < sv v428)) → ((v431 = 1 ↔ ¬v430 = 1)) → (R 1 0 0 1 v432 v432) → ((v432 = 1 ↔ v429 = 1 ∧ v431 = 1)) → (R 1 0 4611686018427387904 4611686018695823363 t427.1 t427.1) → (sv t427.1 = (sc28pS (scArg v427)).1) → (sv t427.2 = (sc28pS (scArg v427)).2) → (R 1 0 4611686018427387904 4611686018695823363 t428.1 t428.1) → (sv t428.1 = (sc28pS (scArg v428)).1) → (sv t428.2 = (sc28pS (scArg v428)).2) → ((v435 = 1 ↔ sv t427.1 < sv t428.1)) → (v436 = if v435 = 1 then t427.1 else t428.1) → (R 1 0 4611686018427387900 4611686018695823359 v437 v437) → (sv v437 = sv v28 + sv v436) → (v438 = if v435 = 1 then t428.1 else t427.1) → (sv v439 = sv v31 + sv v438) → ((v440 = 1 ↔ sv v439 < sv v33)) → (v441 = if v440 = 1 then v439 else v33) → (R 1 0 0 1 v442 v442) → ((v442 = 1 ↔ sv v427 < sv v36)) → ((v443 = 1 ↔ sv v38 < sv v428)) → ((v444 = 1 ↔ v442 = 1 ∧ v443 = 1)) → (R 1 0 4611686018427387908 4611686018695823367 v445 v445) → (v445 = if v444 = 1 then v33 else v441) → ((v446 = 1 ↔ sv v437 < sv v9)) → ((v448 = 1 ↔ sv v9 < sv v445)) → ((v449 = 1 ↔ ¬v448 = 1)) → (R 1 0 0 1 v450 v450) → ((v450 = 1 ↔ v446 = 1 ∧ v449 = 1)) → (R 1 0 0 1 v451 v451) → ((v451 = 1 ↔ v446 = 1 ∧ v448 = 1)) → ((v452 = 1 ↔ v66 = 1 ∧ v451 = 1)) → ((v453 = 1 ↔ v62 = 1 ∧ v451 = 1)) → ((v454 = 1 ↔ v450 = 1 ∨ v453 = 1)) → (v455 = if v454 = 1 then v41 else v29) → (R 1 0 0 1 v456 v456) → ((v456 = 1 ↔ ¬v450 = 1)) → ((v457 = 1 ↔ v66 = 1 ∧ v456 = 1)) → ((v458 = 1 ↔ v65 = 1 ∨ v457 = 1)) → (v459 = if v458 = 1 then v445 else v437) → ((v460 = 1 ↔ v65 = 1 ∧ v451 = 1)) → ((v461 = 1 ↔ v450 = 1 ∨ v460 = 1)) → (v462 = if v461 = 1 then v29 else v41) → ((v463 = 1 ↔ v66 = 1 ∧ v450 = 1)) → ((v464 = 1 ↔ v65 = 1 ∨ v463 = 1)) → (v465 = if v464 = 1 then v437 else v445) → (sv v466 = sv v459 * sv v455) → (sv v467 = sv v466 / 2 ^ 28) → (sv v468 = sv v465 * sv v462) → (sv v469 = -((-sv v468) / 2 ^ 28)) → (sv v470 = sv v437 * sv v41) → (sv v471 = sv v470 / 2 ^ 28) → (sv v472 = sv v437 * sv v29) → (sv v473 = -((-sv v472) / 2 ^ 28)) → ((v474 = 1 ↔ sv v467 < sv v471)) → (v475 = if v474 = 1 then v467 else v471) → ((v476 = 1 ↔ sv v469 < sv v473)) → (v477 = if v476 = 1 then v473 else v469) → (R 1 0 4611686018427387899 4611686018695823374 v478 v478) → (v478 = if v452 = 1 then v475 else v467) → (R 1 0 4611686018427387900 4611686018695823375 v479 v479) → (v479 = if v452 = 1 then v477 else v469) → (R 1 0 0 1 v480 v480) → ((v480 = 1 ↔ sv v18 < sv v478)) → (R 1 0 4611686018427387904 4611686052787126264 v481 v481) → (sv v481 = sv v5 / 2) → ((v482 = 1 ↔ sv v18 < sv v481)) → (R 1 0 0 1 v483 v483) → ((v483 = 1 ↔ v431 = 1 ∧ v482 = 1)) → (sv v485 = sv v28 + sv t428.2) → ((v486 = 1 ↔ sv v485 < sv v104)) → (v487 = if v486 = 1 then v104 else v485) → ((v488 = 1 ↔ sv v107 < sv v428)) → (R 1 0 4611686018158952441 4611686018695823359 v489 v489) → (v489 = if v488 = 1 then v104 else v487) → (R 1 0 0 1 v543 v543) → ((v543 = 1 ↔ sv v489 < sv v9)) → (R 1 0 4611686018427387904 4611686052787126264 v631 v631) → (sv v631 = (sv v4 + 1) / 2) → ((v632 = 1 ↔ sv v20 < sv v631)) → ((v633 = 1 ↔ ¬v632 = 1)) → (R 1 0 0 1 v634 v634) → ((v634 = 1 ↔ v429 = 1 ∧ v633 = 1)) → (sv v642 = sv v31 + sv t427.2) → ((v643 = 1 ↔ sv v642 < sv v33)) → (v644 = if v643 = 1 then v642 else v33) → ((v645 = 1 ↔ sv v427 < sv v114)) → (R 1 0 4611686018158952449 4611686018695823367 v646 v646) → (v646 = if v645 = 1 then v33 else v644) → (R 1 0 4611686018427387904 4611686018695823363 t631.1 t631.1) → (sv t631.1 = (sc28pS (scArg v631)).1) → ((v648 = 1 ↔ sv t427.1 < sv t631.1)) → (v649 = if v648 = 1 then t427.1 else t631.1) → (sv v650 = sv v28 + sv v649) → (v651 = if v648 = 1 then t631.1 else t427.1) → (sv v652 = sv v31 + sv v651) → ((v653 = 1 ↔ sv v652 < sv v33)) → (v654 = if v653 = 1 then v652 else v33) → ((v655 = 1 ↔ sv v38 < sv v631)) → ((v656 = 1 ↔ v442 = 1 ∧ v655 = 1)) → (v657 = if v656 = 1 then v33 else v654) → ((v658 = 1 ↔ sv v650 < sv v9)) → ((v660 = 1 ↔ sv v9 < sv v657)) → ((v661 = 1 ↔ ¬v660 = 1)) → ((v662 = 1 ↔ v658 = 1 ∧ v661 = 1)) → ((v663 = 1 ↔ v658 = 1 ∧ v660 = 1)) → ((v664 = 1 ↔ v148 = 1 ∧ v663 = 1)) → ((v665 = 1 ↔ v144 = 1 ∧ v663 = 1)) → ((v666 = 1 ↔ v662 = 1 ∨ v665 = 1)) → (v667 = if v666 = 1 then v116 else v109) → ((v668 = 1 ↔ ¬v662 = 1)) → ((v669 = 1 ↔ v148 = 1 ∧ v668 = 1)) → ((v670 = 1 ↔ v147 = 1 ∨ v669 = 1)) → (v671 = if v670 = 1 then v657 else v650) → ((v672 = 1 ↔ v147 = 1 ∧ v663 = 1)) → ((v673 = 1 ↔ v662 = 1 ∨ v672 = 1)) → (v674 = if v673 = 1 then v109 else v116) → ((v675 = 1 ↔ v148 = 1 ∧ v662 = 1)) → ((v676 = 1 ↔ v147 = 1 ∨ v675 = 1)) → (v677 = if v676 = 1 then v650 else v657) → (sv v678 = sv v671 * sv v667) → (sv v679 = sv v678 / 2 ^ 28) → (sv v680 = sv v677 * sv v674) → (sv v681 = -((-sv v680) / 2 ^ 28)) → (sv v682 = sv v650 * sv v116) → (sv v683 = sv v682 / 2 ^ 28) → (sv v684 = sv v650 * sv v109) → (sv v685 = -((-sv v684) / 2 ^ 28)) → ((v686 = 1 ↔ sv v679 < sv v683)) → (v687 = if v686 = 1 then v679 else v683) → ((v688 = 1 ↔ sv v681 < sv v685)) → (v689 = if v688 = 1 then v685 else v681) → (v690 = if v664 = 1 then v687 else v679) → (v691 = if v664 = 1 then v689 else v681) → ((v692 = 1 ↔ sv v9 < sv v690)) → ((v693 = 1 ↔ ¬v692 = 1)) → ((v696 = 1 ↔ sv v646 < sv v9)) → (v697 = if v696 = 1 then v691 else v690) → (sv v739 = sv v9 - sv v646) → (v740 = if v696 = 1 then v739 else v646) → (sv v741 = ((H0 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ)) → (sv t741.1 = (sc28pS (scArg v741)).1) → (sv t741.2 = (sc28pS (scArg v741)).2) → (sv v743 = sv v28 + sv t741.2) → ((v744 = 1 ↔ sv v743 < sv v104)) → (v745 = if v744 = 1 then v104 else v743) → (sv v746 = sv v31 + sv t741.2) → ((v747 = 1 ↔ sv v746 < sv v33)) → (v748 = if v747 = 1 then v746 else v33) → (sv v750 = sv v31 + sv t741.1) → ((v751 = 1 ↔ sv v750 < sv v33)) → (v752 = if v751 = 1 then v750 else v33) → (sv v753 = sv v28 + sv t741.1) → (v754 = if v696 = 1 then v745 else v748) → (v755 = if v696 = 1 then v752 else v753) → (sv v756 = sv v697 * sv v755) → (sv v757 = sv v754 * sv v740) → ((v758 = 1 ↔ sv v757 < sv v756)) → ((v759 = 1 ↔ ¬v758 = 1)) → ((v760 = 1 ↔ sv v756 < sv v757)) → ((v761 = 1 ↔ ¬v760 = 1)) → ((v762 = 1 ↔ sv v9 < sv v741)) → ((v763 = 1 ↔ ¬v762 = 1)) → ((v764 = 1 ↔ sv v215 < sv v741)) → ((v765 = 1 ↔ ¬v764 = 1)) → ((v766 = 1 ↔ sv v18 < sv v745)) → ((v767 = 1 ↔ v759 = 1 ∧ v766 = 1)) → ((v768 = 1 ↔ v765 = 1 ∧ v767 = 1)) → ((v769 = 1 ↔ v763 = 1 ∨ v768 = 1)) → ((v770 = 1 ↔ sv v741 < sv v222)) → ((v771 = 1 ↔ ¬v770 = 1)) → ((v772 = 1 ↔ v761 = 1 ∨ v771 = 1)) → ((v773 = 1 ↔ v696 = 1 ∧ v769 = 1)) → ((v774 = 1 ↔ ¬v696 = 1)) → ((v775 = 1 ↔ v772 = 1 ∧ v774 = 1)) → ((v776 = 1 ↔ v773 = 1 ∨ v775 = 1)) → (sv v777 = sv v9 - sv v741) → (v778 = if v696 = 1 then v777 else v741) → (v779 = if v776 = 1 then v778 else v222) → (R 1 0 4611686017353646081 4611686019501129727 v781 v781) → (v781 = if v693 = 1 then v222 else v779) → (sv v782 = sv v7 / 2) → (v783 = if v16 = 1 then v782 else v215) → (sv v784 = (sv v7 + 1) / 2) → ((v785 = 1 ↔ sv v18 < sv v783)) → ((v786 = 1 ↔ sv v20 < sv v784)) → ((v787 = 1 ↔ ¬v786 = 1)) → (R 1 0 0 1 v788 v788) → ((v788 = 1 ↔ v785 = 1 ∧ v787 = 1)) → (sv t783.1 = (sc28pS (scArg v783)).1) → (sv t784.1 = (sc28pS (scArg v784)).1) → ((v791 = 1 ↔ sv t783.1 < sv t784.1)) → (v792 = if v791 = 1 then t783.1 else t784.1) → (sv v793 = sv v28 + sv v792) → (v794 = if v791 = 1 then t784.1 else t783.1) → (sv v795 = sv v31 + sv v794) → ((v796 = 1 ↔ sv v795 < sv v33)) → (v797 = if v796 = 1 then v795 else v33) → ((v798 = 1 ↔ sv v783 < sv v36)) → ((v799 = 1 ↔ sv v38 < sv v784)) → ((v800 = 1 ↔ v798 = 1 ∧ v799 = 1)) → (v801 = if v800 = 1 then v33 else v797) → ((v802 = 1 ↔ sv v793 < sv v9)) → ((v804 = 1 ↔ sv v9 < sv v801)) → ((v805 = 1 ↔ ¬v804 = 1)) → ((v806 = 1 ↔ v802 = 1 ∧ v805 = 1)) → ((v807 = 1 ↔ v802 = 1 ∧ v804 = 1)) → ((v808 = 1 ↔ v66 = 1 ∧ v807 = 1)) → ((v809 = 1 ↔ v62 = 1 ∧ v807 = 1)) → ((v810 = 1 ↔ v806 = 1 ∨ v809 = 1)) → (v811 = if v810 = 1 then v41 else v29) → ((v812 = 1 ↔ ¬v806 = 1)) → ((v813 = 1 ↔ v66 = 1 ∧ v812 = 1)) → ((v814 = 1 ↔ v65 = 1 ∨ v813 = 1)) → (v815 = if v814 = 1 then v801 else v793) → ((v816 = 1 ↔ v65 = 1 ∧ v807 = 1)) → ((v817 = 1 ↔ v806 = 1 ∨ v816 = 1)) → (v818 = if v817 = 1 then v29 else v41) → ((v819 = 1 ↔ v66 = 1 ∧ v806 = 1)) → ((v820 = 1 ↔ v65 = 1 ∨ v819 = 1)) → (v821 = if v820 = 1 then v793 else v801) → (sv v822 = sv v815 * sv v811) → (sv v823 = sv v822 / 2 ^ 28) → (sv v824 = sv v821 * sv v818) → (sv v825 = -((-sv v824) / 2 ^ 28)) → (sv v826 = sv v793 * sv v41) → (sv v827 = sv v826 / 2 ^ 28) → (sv v828 = sv v793 * sv v29) → (sv v829 = -((-sv v828) / 2 ^ 28)) → ((v830 = 1 ↔ sv v823 < sv v827)) → (v831 = if v830 = 1 then v823 else v827) → ((v832 = 1 ↔ sv v825 < sv v829)) → (v833 = if v832 = 1 then v829 else v825) → (R 1 0 4611686018427387899 4611686018695823374 v834 v834) → (v834 = if v808 = 1 then v831 else v823) → (R 1 0 4611686018427387900 4611686018695823375 v835 v835) → (v835 = if v808 = 1 then v833 else v825) → (R 1 0 0 1 v836 v836) → ((v836 = 1 ↔ sv v18 < sv v834)) → ((v837 = 1 ↔ sv v9 < sv v478)) → ((v838 = 1 ↔ sv v479 < sv v33)) → ((v839 = 1 ↔ v837 = 1 ∧ v838 = 1)) → ((v840 = 1 ↔ sv v9 < sv v99)) → ((v841 = 1 ↔ sv v100 < sv v33)) → ((v842 = 1 ↔ v840 = 1 ∧ v841 = 1)) → ((v843 = 1 ↔ sv v9 < sv v834)) → ((v844 = 1 ↔ sv v835 < sv v33)) → (R 1 0 0 1 v845 v845) → ((v845 = 1 ↔ v843 = 1 ∧ v844 = 1)) → ((v846 = 1 ↔ v839 = 1 ∧ v842 = 1)) → (R 1 0 0 1 v847 v847) → ((v847 = 1 ↔ v845 = 1 ∧ v846 = 1)) → (sv v848 = sv v479 * sv v479) → (sv v849 = -((-sv v848) / 2 ^ 28)) → (sv v850 = sv v849 + sv v849) → (sv v851 = sv v33 - sv v850) → ((v852 = 1 ↔ sv v851 < sv v104)) → (R 1 0 4611686018158952386 4611686018695823360 v853 v853) → (v853 = if v852 = 1 then v104 else v851) → (sv v854 = sv v478 * sv v478) → (sv v855 = sv v854 / 2 ^ 28) → (sv v856 = sv v855 + sv v855) → (R 1 0 4611686018158952392 4611686018695823360 v857 v857) → (sv v857 = sv v33 - sv v856) → (sv v858 = sv v835 * sv v835) → (sv v859 = -((-sv v858) / 2 ^ 28)) → (sv v860 = sv v859 + sv v859) → (sv v861 = sv v33 - sv v860) → ((v862 = 1 ↔ sv v861 < sv v104)) → (R 1 0 4611686018158952386 4611686018695823360 v863 v863) → (v863 = if v862 = 1 then v104 else v861) → (sv v864 = sv v834 * sv v834) → (sv v865 = sv v864 / 2 ^ 28) → (sv v866 = sv v865 + sv v865) → (R 1 0 4611686018158952392 4611686018695823360 v867 v867) → (sv v867 = sv v33 - sv v866) → (sv v868 = sv v100 * sv v100) → (sv v869 = -((-sv v868) / 2 ^ 28)) → (sv v870 = sv v869 + sv v869) → (sv v871 = sv v33 - sv v870) → ((v872 = 1 ↔ sv v871 < sv v104)) → (R 1 0 4611686018158952386 4611686018695823360 v873 v873) → (v873 = if v872 = 1 then v104 else v871) → (sv v874 = sv v99 * sv v99) → (sv v875 = sv v874 / 2 ^ 28) → (sv v876 = sv v875 + sv v875) → (R 1 0 4611686018158952392 4611686018695823360 v877 v877) → (sv v877 = sv v33 - sv v876) → ((v878 = 1 ↔ sv v853 < sv v9)) → (R 1 0 0 1 v879 v879) → ((v879 = 1 ↔ ¬v878 = 1)) → ((v880 = 1 ↔ sv v9 < sv v857)) → ((v881 = 1 ↔ ¬v880 = 1)) → (R 1 0 0 1 v882 v882) → ((v882 = 1 ↔ v878 = 1 ∧ v881 = 1)) → (R 1 0 0 1 v883 v883) → ((v883 = 1 ↔ v878 = 1 ∧ v880 = 1)) → ((v884 = 1 ↔ sv v873 < sv v9)) → (R 1 0 0 1 v885 v885) → ((v885 = 1 ↔ ¬v884 = 1)) → ((v886 = 1 ↔ sv v9 < sv v877)) → ((v887 = 1 ↔ ¬v886 = 1)) → (R 1 0 0 1 v888 v888) → ((v888 = 1 ↔ v884 = 1 ∧ v887 = 1)) → (R 1 0 0 1 v889 v889) → ((v889 = 1 ↔ v884 = 1 ∧ v886 = 1)) → (R 1 0 0 1 v890 v890) → ((v890 = 1 ↔ v883 = 1 ∧ v889 = 1)) → ((v891 = 1 ↔ v879 = 1 ∧ v889 = 1)) → ((v892 = 1 ↔ v888 = 1 ∨ v891 = 1)) → (R 1 0 4611686018158952386 4611686018695823360 v893 v893) → (v893 = if v892 = 1 then v857 else v853) → ((v894 = 1 ↔ ¬v888 = 1)) → ((v895 = 1 ↔ v883 = 1 ∧ v894 = 1)) → (R 1 0 0 1 v896 v896) → ((v896 = 1 ↔ v882 = 1 ∨ v895 = 1)) → P) → P := by
  intro OFFr H61r v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v14 v15 v16 v18 v19 v20 v21 v22 v23 t0 t1 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 t42 t43 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v103 v104 v105 v106 v107 v108 v109 v111 v112 v113 v114 v115 v116 v117 v118 v119 v121 v122 v123 v124 v125 v143 v144 v145 v146 v147 v148 v185 v215 v222 v276 v277 v278 v279 v287 v288 v289 v290 v291 t276 v293 v294 v295 v296 v297 v298 v299 v300 v301 v302 v303 v305 v306 v307 v308 v309 v310 v311 v312 v313 v314 v315 v316 v317 v318 v319 v320 v321 v322 v323 v324 v325 v326 v327 v328 v329 v330 v331 v332 v333 v334 v335 v336 v337 v338 v341 v342 v384 v385 v386 t386 v388 v389 v390 v391 v392 v393 v395 v396 v397 v398 v399 v400 v401 v402 v403 v404 v405 v406 v407 v408 v409 v410 v411 v412 v413 v414 v415 v416 v417 v418 v419 v420 v421 v422 v423 v424 v426 v427 v428 v429 v430 v431 v432 t427 t428 v435 v436 v437 v438 v439 v440 v441 v442 v443 v444 v445 v446 v448 v449 v450 v451 v452 v453 v454 v455 v456 v457 v458 v459 v460 v461 v462 v463 v464 v465 v466 v467 v468 v469 v470 v471 v472 v473 v474 v475 v476 v477 v478 v479 v480 v481 v482 v483 v485 v486 v487 v488 v489 v543 v631 v632 v633 v634 v642 v643 v644 v645 v646 t631 v648 v649 v650 v651 v652 v653 v654 v655 v656 v657 v658 v660 v661 v662 v663 v664 v665 v666 v667 v668 v669 v670 v671 v672 v673 v674 v675 v676 v677 v678 v679 v680 v681 v682 v683 v684 v685 v686 v687 v688 v689 v690 v691 v692 v693 v696 v697 v739 v740 v741 t741 v743 v744 v745 v746 v747 v748 v750 v751 v752 v753 v754 v755 v756 v757 v758 v759 v760 v761 v762 v763 v764 v765 v766 v767 v768 v769 v770 v771 v772 v773 v774 v775 v776 v777 v778 v779 v781 v782 v783 v784 v785 v786 v787 v788 t783 t784 v791 v792 v793 v794 v795 v796 v797 v798 v799 v800 v801 v802 v804 v805 v806 v807 v808 v809 v810 v811 v812 v813 v814 v815 v816 v817 v818 v819 v820 v821 v822 v823 v824 v825 v826 v827 v828 v829 v830 v831 v832 v833 v834 v835 v836 v837 v838 v839 v840 v841 v842 v843 v844 v845 v846 v847 v848 v849 v850 v851 v852 v853 v854 v855 v856 v857 v858 v859 v860 v861 v862 v863 v864 v865 v866 v867 v868 v869 v870 v871 v872 v873 v874 v875 v876 v877 v878 v879 v880 v881 v882 v883 v884 v885 v886 v887 v888 v889 v890 v891 v892 v893 v894 v895 v896
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
  have h_v9 : R 1 0 4611686018427387904 4611686018427387904 v9 v9 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have e_v9 : sv v9 = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have e_v10 : sv v10 = (1686629712) := e_c 4611686020114017616 (1686629712) (of_decide_eq_true rfl)
  have h_v14 : R 1 0 4611686019270702760 4611686019270702760 v14 v14 := (r_c hl 4611686019270702760 (of_decide_eq_true rfl))
  have e_v14 : sv v14 = (843314856) := e_c 4611686019270702760 (843314856) (of_decide_eq_true rfl)
  have h_v15 : R 1 0 0 1 v15 v15 := (r_plt hl h_v14 h_v7 (of_decide_eq_true rfl))
  have e_v15 : (v15 = 1 ↔ sv v14 < sv v7) := e_plt h_v14 h_v7 (of_decide_eq_true rfl)
  have h_v16 : R 1 0 0 1 v16 v16 := (r_sub hl (r_O hl) h_v15 (of_decide_eq_true rfl))
  clear h_v14
  have e_v16 : (v16 = 1 ↔ ¬v15 = 1) := e_not h_v15 (of_decide_eq_true rfl)
  have h_v18 : R 1 0 4611686018427387903 4611686018427387903 v18 v18 := (r_c hl 4611686018427387903 (of_decide_eq_true rfl))
  have e_v18 : sv v18 = (-1) := e_c 4611686018427387903 (-1) (of_decide_eq_true rfl)
  have h_v19 : R 1 0 0 1 v19 v19 := (r_plt hl h_v18 h_v0 (of_decide_eq_true rfl))
  have e_v19 : (v19 = 1 ↔ sv v18 < sv v0) := e_plt h_v18 h_v0 (of_decide_eq_true rfl)
  have h_v20 : R 1 0 4611686019270702761 4611686019270702761 v20 v20 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have e_v20 : sv v20 = (843314857) := e_c 4611686019270702761 (843314857) (of_decide_eq_true rfl)
  have h_v21 : R 1 0 0 1 v21 v21 := (r_plt hl h_v20 h_v1 (of_decide_eq_true rfl))
  have e_v21 : (v21 = 1 ↔ sv v20 < sv v1) := e_plt h_v20 h_v1 (of_decide_eq_true rfl)
  have h_v22 : R 1 0 0 1 v22 v22 := (r_sub hl (r_O hl) h_v21 (of_decide_eq_true rfl))
  have e_v22 : (v22 = 1 ↔ ¬v21 = 1) := e_not h_v21 (of_decide_eq_true rfl)
  have h_v23 : R 1 0 0 1 v23 v23 := (r_land hl h_v19 h_v22 (of_decide_eq_true rfl))
  have e_v23 : (v23 = 1 ↔ v19 = 1 ∧ v22 = 1) := e_land h_v19 h_v22 (of_decide_eq_true rfl)
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
  clear h_v15 h_v19 h_v21 h_v22
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
  have h_v44 : R 1 0 0 1 v44 v44 := (r_plt hl h_v18 h_v42 (of_decide_eq_true rfl))
  have e_v44 : (v44 = 1 ↔ sv v18 < sv v42) := e_plt h_v18 h_v42 (of_decide_eq_true rfl)
  have h_v45 : R 1 0 0 1 v45 v45 := (r_plt hl h_v20 h_v43 (of_decide_eq_true rfl))
  have e_v45 : (v45 = 1 ↔ sv v20 < sv v43) := e_plt h_v20 h_v43 (of_decide_eq_true rfl)
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
  have h_v61 : R 1 0 0 1 v61 v61 := (r_plt hl h_v29 h_v9 (of_decide_eq_true rfl))
  have e_v61 : (v61 = 1 ↔ sv v29 < sv v9) := e_plt h_v29 h_v9 (of_decide_eq_true rfl)
  have h_v62 : R 1 0 0 1 v62 v62 := (r_sub hl (r_O hl) h_v61 (of_decide_eq_true rfl))
  have e_v62 : (v62 = 1 ↔ ¬v61 = 1) := e_not h_v61 (of_decide_eq_true rfl)
  have h_v63 : R 1 0 0 1 v63 v63 := (r_plt hl h_v9 h_v41 (of_decide_eq_true rfl))
  clear h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v58 h_v59
  have e_v63 : (v63 = 1 ↔ sv v9 < sv v41) := e_plt h_v9 h_v41 (of_decide_eq_true rfl)
  have h_v64 : R 1 0 0 1 v64 v64 := (r_sub hl (r_O hl) h_v63 (of_decide_eq_true rfl))
  have e_v64 : (v64 = 1 ↔ ¬v63 = 1) := e_not h_v63 (of_decide_eq_true rfl)
  have h_v65 : R 1 0 0 1 v65 v65 := (r_land hl h_v61 h_v64 (of_decide_eq_true rfl))
  have e_v65 : (v65 = 1 ↔ v61 = 1 ∧ v64 = 1) := e_land h_v61 h_v64 (of_decide_eq_true rfl)
  have h_v66 : R 1 0 0 1 v66 v66 := (r_land hl h_v61 h_v63 (of_decide_eq_true rfl))
  have e_v66 : (v66 = 1 ↔ v61 = 1 ∧ v63 = 1) := e_land h_v61 h_v63 (of_decide_eq_true rfl)
  have h_v67 : R 1 0 0 1 v67 v67 := (r_plt hl h_v52 h_v9 (of_decide_eq_true rfl))
  have e_v67 : (v67 = 1 ↔ sv v52 < sv v9) := e_plt h_v52 h_v9 (of_decide_eq_true rfl)
  have h_v69 : R 1 0 0 1 v69 v69 := (r_plt hl h_v9 h_v60 (of_decide_eq_true rfl))
  have e_v69 : (v69 = 1 ↔ sv v9 < sv v60) := e_plt h_v9 h_v60 (of_decide_eq_true rfl)
  have h_v70 : R 1 0 0 1 v70 v70 := (r_sub hl (r_O hl) h_v69 (of_decide_eq_true rfl))
  have e_v70 : (v70 = 1 ↔ ¬v69 = 1) := e_not h_v69 (of_decide_eq_true rfl)
  have h_v71 : R 1 0 0 1 v71 v71 := (r_land hl h_v67 h_v70 (of_decide_eq_true rfl))
  have e_v71 : (v71 = 1 ↔ v67 = 1 ∧ v70 = 1) := e_land h_v67 h_v70 (of_decide_eq_true rfl)
  have h_v72 : R 1 0 0 1 v72 v72 := (r_land hl h_v67 h_v69 (of_decide_eq_true rfl))
  have e_v72 : (v72 = 1 ↔ v67 = 1 ∧ v69 = 1) := e_land h_v67 h_v69 (of_decide_eq_true rfl)
  have h_v73 : R 1 0 0 1 v73 v73 := (r_land hl h_v66 h_v72 (of_decide_eq_true rfl))
  have e_v73 : (v73 = 1 ↔ v66 = 1 ∧ v72 = 1) := e_land h_v66 h_v72 (of_decide_eq_true rfl)
  have h_v74 : R 1 0 0 1 v74 v74 := (r_land hl h_v62 h_v72 (of_decide_eq_true rfl))
  have e_v74 : (v74 = 1 ↔ v62 = 1 ∧ v72 = 1) := e_land h_v62 h_v72 (of_decide_eq_true rfl)
  have h_v75 : R 1 0 0 1 v75 v75 := (r_lor hl h_v71 h_v74 (of_decide_eq_true rfl))
  have e_v75 : (v75 = 1 ↔ v71 = 1 ∨ v74 = 1) := e_lor h_v71 h_v74 (of_decide_eq_true rfl)
  have h_v76 : R 1 0 4611686018427387900 4611686018695823367 v76 v76 := (r_psel hl h_v75 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v76 : v76 = if v75 = 1 then v41 else v29 := e_psel h_v75 h_v41 h_v29 (of_decide_eq_true rfl)
  clear h_v61 h_v63 h_v64 h_v67 h_v69 h_v70 h_v74 h_v75
  have h_v77 : R 1 0 0 1 v77 v77 := (r_sub hl (r_O hl) h_v71 (of_decide_eq_true rfl))
  have e_v77 : (v77 = 1 ↔ ¬v71 = 1) := e_not h_v71 (of_decide_eq_true rfl)
  have h_v78 : R 1 0 0 1 v78 v78 := (r_land hl h_v66 h_v77 (of_decide_eq_true rfl))
  have e_v78 : (v78 = 1 ↔ v66 = 1 ∧ v77 = 1) := e_land h_v66 h_v77 (of_decide_eq_true rfl)
  have h_v79 : R 1 0 0 1 v79 v79 := (r_lor hl h_v65 h_v78 (of_decide_eq_true rfl))
  have e_v79 : (v79 = 1 ↔ v65 = 1 ∨ v78 = 1) := e_lor h_v65 h_v78 (of_decide_eq_true rfl)
  have h_v80 : R 1 0 4611686018427387900 4611686018695823367 v80 v80 := (r_psel hl h_v79 h_v60 h_v52 (of_decide_eq_true rfl))
  have e_v80 : v80 = if v79 = 1 then v60 else v52 := e_psel h_v79 h_v60 h_v52 (of_decide_eq_true rfl)
  have h_v81 : R 1 0 0 1 v81 v81 := (r_land hl h_v65 h_v72 (of_decide_eq_true rfl))
  have e_v81 : (v81 = 1 ↔ v65 = 1 ∧ v72 = 1) := e_land h_v65 h_v72 (of_decide_eq_true rfl)
  have h_v82 : R 1 0 0 1 v82 v82 := (r_lor hl h_v71 h_v81 (of_decide_eq_true rfl))
  have e_v82 : (v82 = 1 ↔ v71 = 1 ∨ v81 = 1) := e_lor h_v71 h_v81 (of_decide_eq_true rfl)
  have h_v83 : R 1 0 4611686018427387900 4611686018695823367 v83 v83 := (r_psel hl h_v82 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v83 : v83 = if v82 = 1 then v29 else v41 := e_psel h_v82 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v84 : R 1 0 0 1 v84 v84 := (r_land hl h_v66 h_v71 (of_decide_eq_true rfl))
  have e_v84 : (v84 = 1 ↔ v66 = 1 ∧ v71 = 1) := e_land h_v66 h_v71 (of_decide_eq_true rfl)
  have h_v85 : R 1 0 0 1 v85 v85 := (r_lor hl h_v65 h_v84 (of_decide_eq_true rfl))
  have e_v85 : (v85 = 1 ↔ v65 = 1 ∨ v84 = 1) := e_lor h_v65 h_v84 (of_decide_eq_true rfl)
  have h_v86 : R 1 0 4611686018427387900 4611686018695823367 v86 v86 := (r_psel hl h_v85 h_v52 h_v60 (of_decide_eq_true rfl))
  have e_v86 : v86 = if v85 = 1 then v52 else v60 := e_psel h_v85 h_v52 h_v60 (of_decide_eq_true rfl)
  have h_v87 : R 1 0 4611686017353646052 4683743616223412273 v87 v87 := (r_smx hl 29 h_v80 h_v76 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v87 : sv v87 = sv v80 * sv v76 := e_smx 29 h_v80 h_v76 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v88 : R 1 0 4611686018427387899 4611686018695823374 v88 v88 := (r_srdF hl h_v87 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v88 : sv v88 = sv v87 / 2 ^ 28 := e_srdF h_v87 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v89 : R 1 0 4611686017353646052 4683743616223412273 v89 v89 := (r_smx hl 29 h_v86 h_v83 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  clear h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v84 h_v85 h_v87
  have e_v89 : sv v89 = sv v86 * sv v83 := e_smx 29 h_v86 h_v83 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v90 : R 1 0 4611686018427387900 4611686018695823375 v90 v90 := (r_srdC hl h_v89 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v90 : sv v90 = -((-sv v89) / 2 ^ 28) := e_srdC h_v89 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v91 : R 1 0 4611686017353646052 4683743614075928569 v91 v91 := (r_smx hl 29 h_v52 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl))
  have e_v91 : sv v91 = sv v52 * sv v41 := e_smx 29 h_v52 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl)
  have h_v92 : R 1 0 4611686018427387899 4611686018695823365 v92 v92 := (r_srdF hl h_v91 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl))
  have e_v92 : sv v92 = sv v91 / 2 ^ 28 := e_srdF h_v91 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl)
  have h_v93 : R 1 0 4611686017353646084 4683743611928444929 v93 v93 := (r_smx hl 29 h_v52 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl))
  have e_v93 : sv v93 = sv v52 * sv v29 := e_smx 29 h_v52 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl)
  have h_v94 : R 1 0 4611686018427387901 4611686018695823359 v94 v94 := (r_srdC hl h_v93 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl))
  have e_v94 : sv v94 = -((-sv v93) / 2 ^ 28) := e_srdC h_v93 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl)
  have h_v95 : R 1 0 0 1 v95 v95 := (r_plt hl h_v88 h_v92 (of_decide_eq_true rfl))
  have e_v95 : (v95 = 1 ↔ sv v88 < sv v92) := e_plt h_v88 h_v92 (of_decide_eq_true rfl)
  have h_v96 : R 1 0 4611686018427387899 4611686018695823374 v96 v96 := (r_psel hl h_v95 h_v88 h_v92 (of_decide_eq_true rfl))
  have e_v96 : v96 = if v95 = 1 then v88 else v92 := e_psel h_v95 h_v88 h_v92 (of_decide_eq_true rfl)
  have h_v97 : R 1 0 0 1 v97 v97 := (r_plt hl h_v90 h_v94 (of_decide_eq_true rfl))
  have e_v97 : (v97 = 1 ↔ sv v90 < sv v94) := e_plt h_v90 h_v94 (of_decide_eq_true rfl)
  have h_v98 : R 1 0 4611686018427387900 4611686018695823375 v98 v98 := (r_psel hl h_v97 h_v94 h_v90 (of_decide_eq_true rfl))
  have e_v98 : v98 = if v97 = 1 then v94 else v90 := e_psel h_v97 h_v94 h_v90 (of_decide_eq_true rfl)
  have h_v99 : R 1 0 4611686018427387899 4611686018695823374 v99 v99 := (r_psel hl h_v73 h_v96 h_v88 (of_decide_eq_true rfl))
  have e_v99 : v99 = if v73 = 1 then v96 else v88 := e_psel h_v73 h_v96 h_v88 (of_decide_eq_true rfl)
  have h_v100 : R 1 0 4611686018427387900 4611686018695823375 v100 v100 := (r_psel hl h_v73 h_v98 h_v90 (of_decide_eq_true rfl))
  have e_v100 : v100 = if v73 = 1 then v98 else v90 := e_psel h_v73 h_v98 h_v90 (of_decide_eq_true rfl)
  have h_v101 : R 1 0 0 1 v101 v101 := (r_plt hl h_v18 h_v99 (of_decide_eq_true rfl))
  have e_v101 : (v101 = 1 ↔ sv v18 < sv v99) := e_plt h_v18 h_v99 (of_decide_eq_true rfl)
  clear h_v73 h_v83 h_v86 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98
  have h_v103 : R 1 0 4611686018158952441 4611686018695823359 v103 v103 := (r_sub hl (r_add hl h_v28 h_t1_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v103 : sv v103 = sv v28 + sv t1.2 := e_add h_v28 h_t1_2 (of_decide_eq_true rfl)
  have h_v104 : R 1 0 4611686018158952448 4611686018158952448 v104 v104 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have e_v104 : sv v104 = (-268435456) := e_c 4611686018158952448 (-268435456) (of_decide_eq_true rfl)
  have h_v105 : R 1 0 0 1 v105 v105 := (r_plt hl h_v103 h_v104 (of_decide_eq_true rfl))
  have e_v105 : (v105 = 1 ↔ sv v103 < sv v104) := e_plt h_v103 h_v104 (of_decide_eq_true rfl)
  have h_v106 : R 1 0 4611686018158952441 4611686018695823359 v106 v106 := (r_psel hl h_v105 h_v104 h_v103 (of_decide_eq_true rfl))
  have e_v106 : v106 = if v105 = 1 then v104 else v103 := e_psel h_v105 h_v104 h_v103 (of_decide_eq_true rfl)
  have h_v107 : R 1 0 4611686019270702759 4611686019270702759 v107 v107 := (r_c hl 4611686019270702759 (of_decide_eq_true rfl))
  have e_v107 : sv v107 = (843314855) := e_c 4611686019270702759 (843314855) (of_decide_eq_true rfl)
  have h_v108 : R 1 0 0 1 v108 v108 := (r_plt hl h_v107 h_v1 (of_decide_eq_true rfl))
  have e_v108 : (v108 = 1 ↔ sv v107 < sv v1) := e_plt h_v107 h_v1 (of_decide_eq_true rfl)
  have h_v109 : R 1 0 4611686018158952441 4611686018695823359 v109 v109 := (r_psel hl h_v108 h_v104 h_v106 (of_decide_eq_true rfl))
  have e_v109 : v109 = if v108 = 1 then v104 else v106 := e_psel h_v108 h_v104 h_v106 (of_decide_eq_true rfl)
  have h_v111 : R 1 0 4611686018158952449 4611686018695823367 v111 v111 := (r_sub hl (r_add hl h_v31 h_t0_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v111 : sv v111 = sv v31 + sv t0.2 := e_add h_v31 h_t0_2 (of_decide_eq_true rfl)
  have h_v112 : R 1 0 0 1 v112 v112 := (r_plt hl h_v111 h_v33 (of_decide_eq_true rfl))
  have e_v112 : (v112 = 1 ↔ sv v111 < sv v33) := e_plt h_v111 h_v33 (of_decide_eq_true rfl)
  have h_v113 : R 1 0 4611686018158952449 4611686018695823367 v113 v113 := (r_psel hl h_v112 h_v111 h_v33 (of_decide_eq_true rfl))
  have e_v113 : v113 = if v112 = 1 then v111 else v33 := e_psel h_v112 h_v111 h_v33 (of_decide_eq_true rfl)
  have h_v114 : R 1 0 4611686018427387905 4611686018427387905 v114 v114 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have e_v114 : sv v114 = (1) := e_c 4611686018427387905 (1) (of_decide_eq_true rfl)
  have h_v115 : R 1 0 0 1 v115 v115 := (r_plt hl h_v0 h_v114 (of_decide_eq_true rfl))
  have e_v115 : (v115 = 1 ↔ sv v0 < sv v114) := e_plt h_v0 h_v114 (of_decide_eq_true rfl)
  have h_v116 : R 1 0 4611686018158952449 4611686018695823367 v116 v116 := (r_psel hl h_v115 h_v33 h_v113 (of_decide_eq_true rfl))
  clear h_v0 h_v1 h_t0_2 h_t1_2 h_v103 h_v105 h_v106 h_v108 h_v111 h_v112
  have e_v116 : v116 = if v115 = 1 then v33 else v113 := e_psel h_v115 h_v33 h_v113 (of_decide_eq_true rfl)
  have h_v117 : R 1 0 4611686018427387904 4611686052787126264 v117 v117 := (r_add hl (r_pshr1 hl h_v3) h_H61r (of_decide_eq_true rfl))
  have e_v117 : sv v117 = sv v3 / 2 := e_halfF h_v3
  have h_v118 : R 1 0 0 1 v118 v118 := (r_plt hl h_v18 h_v117 (of_decide_eq_true rfl))
  have e_v118 : (v118 = 1 ↔ sv v18 < sv v117) := e_plt h_v18 h_v117 (of_decide_eq_true rfl)
  have h_v119 : R 1 0 0 1 v119 v119 := (r_land hl h_v46 h_v118 (of_decide_eq_true rfl))
  have e_v119 : (v119 = 1 ↔ v46 = 1 ∧ v118 = 1) := e_land h_v46 h_v118 (of_decide_eq_true rfl)
  have h_v121 : R 1 0 4611686018158952441 4611686018695823359 v121 v121 := (r_sub hl (r_add hl h_v28 h_t43_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v121 : sv v121 = sv v28 + sv t43.2 := e_add h_v28 h_t43_2 (of_decide_eq_true rfl)
  have h_v122 : R 1 0 0 1 v122 v122 := (r_plt hl h_v121 h_v104 (of_decide_eq_true rfl))
  have e_v122 : (v122 = 1 ↔ sv v121 < sv v104) := e_plt h_v121 h_v104 (of_decide_eq_true rfl)
  have h_v123 : R 1 0 4611686018158952441 4611686018695823359 v123 v123 := (r_psel hl h_v122 h_v104 h_v121 (of_decide_eq_true rfl))
  have e_v123 : v123 = if v122 = 1 then v104 else v121 := e_psel h_v122 h_v104 h_v121 (of_decide_eq_true rfl)
  have h_v124 : R 1 0 0 1 v124 v124 := (r_plt hl h_v107 h_v43 (of_decide_eq_true rfl))
  have e_v124 : (v124 = 1 ↔ sv v107 < sv v43) := e_plt h_v107 h_v43 (of_decide_eq_true rfl)
  have h_v125 : R 1 0 4611686018158952441 4611686018695823359 v125 v125 := (r_psel hl h_v124 h_v104 h_v123 (of_decide_eq_true rfl))
  have e_v125 : v125 = if v124 = 1 then v104 else v123 := e_psel h_v124 h_v104 h_v123 (of_decide_eq_true rfl)
  have h_v143 : R 1 0 0 1 v143 v143 := (r_plt hl h_v109 h_v9 (of_decide_eq_true rfl))
  have e_v143 : (v143 = 1 ↔ sv v109 < sv v9) := e_plt h_v109 h_v9 (of_decide_eq_true rfl)
  have h_v144 : R 1 0 0 1 v144 v144 := (r_sub hl (r_O hl) h_v143 (of_decide_eq_true rfl))
  have e_v144 : (v144 = 1 ↔ ¬v143 = 1) := e_not h_v143 (of_decide_eq_true rfl)
  have h_v145 : R 1 0 0 1 v145 v145 := (r_plt hl h_v9 h_v116 (of_decide_eq_true rfl))
  have e_v145 : (v145 = 1 ↔ sv v9 < sv v116) := e_plt h_v9 h_v116 (of_decide_eq_true rfl)
  have h_v146 : R 1 0 0 1 v146 v146 := (r_sub hl (r_O hl) h_v145 (of_decide_eq_true rfl))
  have e_v146 : (v146 = 1 ↔ ¬v145 = 1) := e_not h_v145 (of_decide_eq_true rfl)
  clear h_v3 h_v46 h_t43_2 h_v113 h_v115 h_v118 h_v121 h_v122 h_v123 h_v124
  have h_v147 : R 1 0 0 1 v147 v147 := (r_land hl h_v143 h_v146 (of_decide_eq_true rfl))
  have e_v147 : (v147 = 1 ↔ v143 = 1 ∧ v146 = 1) := e_land h_v143 h_v146 (of_decide_eq_true rfl)
  have h_v148 : R 1 0 0 1 v148 v148 := (r_land hl h_v143 h_v145 (of_decide_eq_true rfl))
  have e_v148 : (v148 = 1 ↔ v143 = 1 ∧ v145 = 1) := e_land h_v143 h_v145 (of_decide_eq_true rfl)
  have h_v185 : R 1 0 0 1 v185 v185 := (r_plt hl h_v125 h_v9 (of_decide_eq_true rfl))
  have e_v185 : (v185 = 1 ↔ sv v125 < sv v9) := e_plt h_v125 h_v9 (of_decide_eq_true rfl)
  have h_v215 : R 1 0 4611686018849045332 4611686018849045332 v215 v215 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  have e_v215 : sv v215 = (421657428) := e_c 4611686018849045332 (421657428) (of_decide_eq_true rfl)
  have h_v222 : R 1 0 4611686018849045333 4611686018849045333 v222 v222 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have e_v222 : sv v222 = (421657429) := e_c 4611686018849045333 (421657429) (of_decide_eq_true rfl)
  have h_v276 : R 1 0 4611686018427387904 4611686052787126264 v276 v276 := (r_add hl (r_pshr1 hl (r_add hl h_v2 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v276 : sv v276 = (sv v2 + 1) / 2 := e_halfC h_v2 (of_decide_eq_true rfl)
  have h_v277 : R 1 0 0 1 v277 v277 := (r_plt hl h_v20 h_v276 (of_decide_eq_true rfl))
  have e_v277 : (v277 = 1 ↔ sv v20 < sv v276) := e_plt h_v20 h_v276 (of_decide_eq_true rfl)
  have h_v278 : R 1 0 0 1 v278 v278 := (r_sub hl (r_O hl) h_v277 (of_decide_eq_true rfl))
  have e_v278 : (v278 = 1 ↔ ¬v277 = 1) := e_not h_v277 (of_decide_eq_true rfl)
  have h_v279 : R 1 0 0 1 v279 v279 := (r_land hl h_v44 h_v278 (of_decide_eq_true rfl))
  have e_v279 : (v279 = 1 ↔ v44 = 1 ∧ v278 = 1) := e_land h_v44 h_v278 (of_decide_eq_true rfl)
  have h_v287 : R 1 0 4611686018158952449 4611686018695823367 v287 v287 := (r_sub hl (r_add hl h_v31 h_t42_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v287 : sv v287 = sv v31 + sv t42.2 := e_add h_v31 h_t42_2 (of_decide_eq_true rfl)
  have h_v288 : R 1 0 0 1 v288 v288 := (r_plt hl h_v287 h_v33 (of_decide_eq_true rfl))
  have e_v288 : (v288 = 1 ↔ sv v287 < sv v33) := e_plt h_v287 h_v33 (of_decide_eq_true rfl)
  have h_v289 : R 1 0 4611686018158952449 4611686018695823367 v289 v289 := (r_psel hl h_v288 h_v287 h_v33 (of_decide_eq_true rfl))
  have e_v289 : v289 = if v288 = 1 then v287 else v33 := e_psel h_v288 h_v287 h_v33 (of_decide_eq_true rfl)
  have h_v290 : R 1 0 0 1 v290 v290 := (r_plt hl h_v42 h_v114 (of_decide_eq_true rfl))
  clear h_v2 h_t42_2 h_v143 h_v145 h_v146 h_v277 h_v278 h_v287 h_v288
  have e_v290 : (v290 = 1 ↔ sv v42 < sv v114) := e_plt h_v42 h_v114 (of_decide_eq_true rfl)
  have h_v291 : R 1 0 4611686018158952449 4611686018695823367 v291 v291 := (r_psel hl h_v290 h_v33 h_v289 (of_decide_eq_true rfl))
  have e_v291 : v291 = if v290 = 1 then v33 else v289 := e_psel h_v290 h_v33 h_v289 (of_decide_eq_true rfl)
  have h_t276_1 : R 1 0 4611686018427387904 4611686018695823363 t276.1 t276.1 := r_sc1 hl h_v276 (of_decide_eq_true rfl)
  have h_t276_2 : R 1 0 4611686018158952445 4611686018695823363 t276.2 t276.2 := r_sc2 hl h_v276 (of_decide_eq_true rfl)
  have e_t276_1 : sv t276.1 = (sc28pS (scArg v276)).1 := e_sc1 h_v276 (of_decide_eq_true rfl)
  have e_t276_2 : sv t276.2 = (sc28pS (scArg v276)).2 := e_sc2 h_v276 (of_decide_eq_true rfl)
  have h_v293 : R 1 0 0 1 v293 v293 := (r_plt hl h_t42_1 h_t276_1 (of_decide_eq_true rfl))
  have e_v293 : (v293 = 1 ↔ sv t42.1 < sv t276.1) := e_plt h_t42_1 h_t276_1 (of_decide_eq_true rfl)
  have h_v294 : R 1 0 4611686018427387904 4611686018695823363 v294 v294 := (r_psel hl h_v293 h_t42_1 h_t276_1 (of_decide_eq_true rfl))
  have e_v294 : v294 = if v293 = 1 then t42.1 else t276.1 := e_psel h_v293 h_t42_1 h_t276_1 (of_decide_eq_true rfl)
  have h_v295 : R 1 0 4611686018427387900 4611686018695823359 v295 v295 := (r_sub hl (r_add hl h_v28 h_v294 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v295 : sv v295 = sv v28 + sv v294 := e_add h_v28 h_v294 (of_decide_eq_true rfl)
  have h_v296 : R 1 0 4611686018427387904 4611686018695823363 v296 v296 := (r_psel hl h_v293 h_t276_1 h_t42_1 (of_decide_eq_true rfl))
  have e_v296 : v296 = if v293 = 1 then t276.1 else t42.1 := e_psel h_v293 h_t276_1 h_t42_1 (of_decide_eq_true rfl)
  have h_v297 : R 1 0 4611686018427387908 4611686018695823367 v297 v297 := (r_sub hl (r_add hl h_v31 h_v296 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v297 : sv v297 = sv v31 + sv v296 := e_add h_v31 h_v296 (of_decide_eq_true rfl)
  have h_v298 : R 1 0 0 1 v298 v298 := (r_plt hl h_v297 h_v33 (of_decide_eq_true rfl))
  have e_v298 : (v298 = 1 ↔ sv v297 < sv v33) := e_plt h_v297 h_v33 (of_decide_eq_true rfl)
  have h_v299 : R 1 0 4611686018427387908 4611686018695823367 v299 v299 := (r_psel hl h_v298 h_v297 h_v33 (of_decide_eq_true rfl))
  have e_v299 : v299 = if v298 = 1 then v297 else v33 := e_psel h_v298 h_v297 h_v33 (of_decide_eq_true rfl)
  have h_v300 : R 1 0 0 1 v300 v300 := (r_plt hl h_v38 h_v276 (of_decide_eq_true rfl))
  have e_v300 : (v300 = 1 ↔ sv v38 < sv v276) := e_plt h_v38 h_v276 (of_decide_eq_true rfl)
  have h_v301 : R 1 0 0 1 v301 v301 := (r_land hl h_v57 h_v300 (of_decide_eq_true rfl))
  have e_v301 : (v301 = 1 ↔ v57 = 1 ∧ v300 = 1) := e_land h_v57 h_v300 (of_decide_eq_true rfl)
  clear h_v289 h_v290 h_t276_2 e_t276_2 h_v293 h_v294 h_v296 h_v297 h_v298 h_v300
  have h_v302 : R 1 0 4611686018427387908 4611686018695823367 v302 v302 := (r_psel hl h_v301 h_v33 h_v299 (of_decide_eq_true rfl))
  have e_v302 : v302 = if v301 = 1 then v33 else v299 := e_psel h_v301 h_v33 h_v299 (of_decide_eq_true rfl)
  have h_v303 : R 1 0 0 1 v303 v303 := (r_plt hl h_v295 h_v9 (of_decide_eq_true rfl))
  have e_v303 : (v303 = 1 ↔ sv v295 < sv v9) := e_plt h_v295 h_v9 (of_decide_eq_true rfl)
  have h_v305 : R 1 0 0 1 v305 v305 := (r_plt hl h_v9 h_v302 (of_decide_eq_true rfl))
  have e_v305 : (v305 = 1 ↔ sv v9 < sv v302) := e_plt h_v9 h_v302 (of_decide_eq_true rfl)
  have h_v306 : R 1 0 0 1 v306 v306 := (r_sub hl (r_O hl) h_v305 (of_decide_eq_true rfl))
  have e_v306 : (v306 = 1 ↔ ¬v305 = 1) := e_not h_v305 (of_decide_eq_true rfl)
  have h_v307 : R 1 0 0 1 v307 v307 := (r_land hl h_v303 h_v306 (of_decide_eq_true rfl))
  have e_v307 : (v307 = 1 ↔ v303 = 1 ∧ v306 = 1) := e_land h_v303 h_v306 (of_decide_eq_true rfl)
  have h_v308 : R 1 0 0 1 v308 v308 := (r_land hl h_v303 h_v305 (of_decide_eq_true rfl))
  have e_v308 : (v308 = 1 ↔ v303 = 1 ∧ v305 = 1) := e_land h_v303 h_v305 (of_decide_eq_true rfl)
  have h_v309 : R 1 0 0 1 v309 v309 := (r_land hl h_v148 h_v308 (of_decide_eq_true rfl))
  have e_v309 : (v309 = 1 ↔ v148 = 1 ∧ v308 = 1) := e_land h_v148 h_v308 (of_decide_eq_true rfl)
  have h_v310 : R 1 0 0 1 v310 v310 := (r_land hl h_v144 h_v308 (of_decide_eq_true rfl))
  have e_v310 : (v310 = 1 ↔ v144 = 1 ∧ v308 = 1) := e_land h_v144 h_v308 (of_decide_eq_true rfl)
  have h_v311 : R 1 0 0 1 v311 v311 := (r_lor hl h_v307 h_v310 (of_decide_eq_true rfl))
  have e_v311 : (v311 = 1 ↔ v307 = 1 ∨ v310 = 1) := e_lor h_v307 h_v310 (of_decide_eq_true rfl)
  have h_v312 : R 1 0 4611686018158952441 4611686018695823367 v312 v312 := (r_psel hl h_v311 h_v116 h_v109 (of_decide_eq_true rfl))
  have e_v312 : v312 = if v311 = 1 then v116 else v109 := e_psel h_v311 h_v116 h_v109 (of_decide_eq_true rfl)
  have h_v313 : R 1 0 0 1 v313 v313 := (r_sub hl (r_O hl) h_v307 (of_decide_eq_true rfl))
  have e_v313 : (v313 = 1 ↔ ¬v307 = 1) := e_not h_v307 (of_decide_eq_true rfl)
  have h_v314 : R 1 0 0 1 v314 v314 := (r_land hl h_v148 h_v313 (of_decide_eq_true rfl))
  have e_v314 : (v314 = 1 ↔ v148 = 1 ∧ v313 = 1) := e_land h_v148 h_v313 (of_decide_eq_true rfl)
  have h_v315 : R 1 0 0 1 v315 v315 := (r_lor hl h_v147 h_v314 (of_decide_eq_true rfl))
  clear h_v299 h_v301 h_v303 h_v305 h_v306 h_v310 h_v311 h_v313
  have e_v315 : (v315 = 1 ↔ v147 = 1 ∨ v314 = 1) := e_lor h_v147 h_v314 (of_decide_eq_true rfl)
  have h_v316 : R 1 0 4611686018427387900 4611686018695823367 v316 v316 := (r_psel hl h_v315 h_v302 h_v295 (of_decide_eq_true rfl))
  have e_v316 : v316 = if v315 = 1 then v302 else v295 := e_psel h_v315 h_v302 h_v295 (of_decide_eq_true rfl)
  have h_v317 : R 1 0 0 1 v317 v317 := (r_land hl h_v147 h_v308 (of_decide_eq_true rfl))
  have e_v317 : (v317 = 1 ↔ v147 = 1 ∧ v308 = 1) := e_land h_v147 h_v308 (of_decide_eq_true rfl)
  have h_v318 : R 1 0 0 1 v318 v318 := (r_lor hl h_v307 h_v317 (of_decide_eq_true rfl))
  have e_v318 : (v318 = 1 ↔ v307 = 1 ∨ v317 = 1) := e_lor h_v307 h_v317 (of_decide_eq_true rfl)
  have h_v319 : R 1 0 4611686018158952441 4611686018695823367 v319 v319 := (r_psel hl h_v318 h_v109 h_v116 (of_decide_eq_true rfl))
  have e_v319 : v319 = if v318 = 1 then v109 else v116 := e_psel h_v318 h_v109 h_v116 (of_decide_eq_true rfl)
  have h_v320 : R 1 0 0 1 v320 v320 := (r_land hl h_v148 h_v307 (of_decide_eq_true rfl))
  have e_v320 : (v320 = 1 ↔ v148 = 1 ∧ v307 = 1) := e_land h_v148 h_v307 (of_decide_eq_true rfl)
  have h_v321 : R 1 0 0 1 v321 v321 := (r_lor hl h_v147 h_v320 (of_decide_eq_true rfl))
  have e_v321 : (v321 = 1 ↔ v147 = 1 ∨ v320 = 1) := e_lor h_v147 h_v320 (of_decide_eq_true rfl)
  have h_v322 : R 1 0 4611686018427387900 4611686018695823367 v322 v322 := (r_psel hl h_v321 h_v295 h_v302 (of_decide_eq_true rfl))
  have e_v322 : v322 = if v321 = 1 then v295 else v302 := e_psel h_v321 h_v295 h_v302 (of_decide_eq_true rfl)
  have h_v323 : R 1 0 4539628420631363535 4683743616223412273 v323 v323 := (r_smx hl 29 h_v316 h_v312 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v323 : sv v323 = sv v316 * sv v312 := e_smx 29 h_v316 h_v312 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v324 : R 1 0 4611686018158952433 4611686018695823374 v324 v324 := (r_srdF hl h_v323 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v324 : sv v324 = sv v323 / 2 ^ 28 := e_srdF h_v323 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v325 : R 1 0 4539628420631363535 4683743616223412273 v325 v325 := (r_smx hl 29 h_v322 h_v319 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v325 : sv v325 = sv v322 * sv v319 := e_smx 29 h_v322 h_v319 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v326 : R 1 0 4611686018158952434 4611686018695823375 v326 v326 := (r_srdC hl h_v325 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v326 : sv v326 = -((-sv v325) / 2 ^ 28) := e_srdC h_v325 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v327 : R 1 0 4539628424926330879 4683743614075928569 v327 v327 := (r_smx hl 29 h_v295 h_v116 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl))
  have e_v327 : sv v327 = sv v295 * sv v116 := e_smx 29 h_v295 h_v116 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl)
  clear h_v302 h_v307 h_v308 h_v312 h_v314 h_v315 h_v316 h_v317 h_v318 h_v319 h_v320 h_v321 h_v322 h_v323 h_v325
  have h_v328 : R 1 0 4611686018158952449 4611686018695823365 v328 v328 := (r_srdF hl h_v327 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl))
  have e_v328 : sv v328 = sv v327 / 2 ^ 28 := e_srdF h_v327 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl)
  have h_v329 : R 1 0 4539628422778847239 4683743611928444929 v329 v329 := (r_smx hl 29 h_v295 h_v109 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl))
  have e_v329 : sv v329 = sv v295 * sv v109 := e_smx 29 h_v295 h_v109 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl)
  have h_v330 : R 1 0 4611686018158952443 4611686018695823359 v330 v330 := (r_srdC hl h_v329 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl))
  have e_v330 : sv v330 = -((-sv v329) / 2 ^ 28) := e_srdC h_v329 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl)
  have h_v331 : R 1 0 0 1 v331 v331 := (r_plt hl h_v324 h_v328 (of_decide_eq_true rfl))
  have e_v331 : (v331 = 1 ↔ sv v324 < sv v328) := e_plt h_v324 h_v328 (of_decide_eq_true rfl)
  have h_v332 : R 1 0 4611686018158952433 4611686018695823374 v332 v332 := (r_psel hl h_v331 h_v324 h_v328 (of_decide_eq_true rfl))
  have e_v332 : v332 = if v331 = 1 then v324 else v328 := e_psel h_v331 h_v324 h_v328 (of_decide_eq_true rfl)
  have h_v333 : R 1 0 0 1 v333 v333 := (r_plt hl h_v326 h_v330 (of_decide_eq_true rfl))
  have e_v333 : (v333 = 1 ↔ sv v326 < sv v330) := e_plt h_v326 h_v330 (of_decide_eq_true rfl)
  have h_v334 : R 1 0 4611686018158952434 4611686018695823375 v334 v334 := (r_psel hl h_v333 h_v330 h_v326 (of_decide_eq_true rfl))
  have e_v334 : v334 = if v333 = 1 then v330 else v326 := e_psel h_v333 h_v330 h_v326 (of_decide_eq_true rfl)
  have h_v335 : R 1 0 4611686018158952433 4611686018695823374 v335 v335 := (r_psel hl h_v309 h_v332 h_v324 (of_decide_eq_true rfl))
  have e_v335 : v335 = if v309 = 1 then v332 else v324 := e_psel h_v309 h_v332 h_v324 (of_decide_eq_true rfl)
  have h_v336 : R 1 0 4611686018158952434 4611686018695823375 v336 v336 := (r_psel hl h_v309 h_v334 h_v326 (of_decide_eq_true rfl))
  have e_v336 : v336 = if v309 = 1 then v334 else v326 := e_psel h_v309 h_v334 h_v326 (of_decide_eq_true rfl)
  have h_v337 : R 1 0 0 1 v337 v337 := (r_plt hl h_v9 h_v335 (of_decide_eq_true rfl))
  have e_v337 : (v337 = 1 ↔ sv v9 < sv v335) := e_plt h_v9 h_v335 (of_decide_eq_true rfl)
  have h_v338 : R 1 0 0 1 v338 v338 := (r_sub hl (r_O hl) h_v337 (of_decide_eq_true rfl))
  have e_v338 : (v338 = 1 ↔ ¬v337 = 1) := e_not h_v337 (of_decide_eq_true rfl)
  have h_v341 : R 1 0 0 1 v341 v341 := (r_plt hl h_v291 h_v9 (of_decide_eq_true rfl))
  have e_v341 : (v341 = 1 ↔ sv v291 < sv v9) := e_plt h_v291 h_v9 (of_decide_eq_true rfl)
  have h_v342 : R 1 0 4611686018158952433 4611686018695823375 v342 v342 := (r_psel hl h_v341 h_v336 h_v335 (of_decide_eq_true rfl))
  clear h_v295 h_v309 h_v324 h_v326 h_v327 h_v328 h_v329 h_v330 h_v331 h_v332 h_v333 h_v334 h_v337
  have e_v342 : v342 = if v341 = 1 then v336 else v335 := e_psel h_v341 h_v336 h_v335 (of_decide_eq_true rfl)
  have h_v384 : R 1 0 4611686018158952441 4611686018695823359 v384 v384 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v291 (of_decide_eq_true rfl))
  have e_v384 : sv v384 = sv v9 - sv v291 := e_sub h_v9 h_v291 (of_decide_eq_true rfl)
  have h_v385 : R 1 0 4611686018158952441 4611686018695823367 v385 v385 := (r_psel hl h_v341 h_v384 h_v291 (of_decide_eq_true rfl))
  have e_v385 : v385 = if v341 = 1 then v384 else v291 := e_psel h_v341 h_v384 h_v291 (of_decide_eq_true rfl)
  have h_v386 : R 1 0 4611686018427387904 4611686019501129727 v386 v386 := (r1_hxa hb_H0 0 (of_decide_eq_true rfl))
  have e_v386 : sv v386 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 0 (of_decide_eq_true rfl)
  have h_t386_1 : R 1 0 4611686018427387904 4611686018695823363 t386.1 t386.1 := r_sc1 hl h_v386 (of_decide_eq_true rfl)
  have h_t386_2 : R 1 0 4611686018158952445 4611686018695823363 t386.2 t386.2 := r_sc2 hl h_v386 (of_decide_eq_true rfl)
  have e_t386_1 : sv t386.1 = (sc28pS (scArg v386)).1 := e_sc1 h_v386 (of_decide_eq_true rfl)
  have e_t386_2 : sv t386.2 = (sc28pS (scArg v386)).2 := e_sc2 h_v386 (of_decide_eq_true rfl)
  have h_v388 : R 1 0 4611686018158952441 4611686018695823359 v388 v388 := (r_sub hl (r_add hl h_v28 h_t386_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v388 : sv v388 = sv v28 + sv t386.2 := e_add h_v28 h_t386_2 (of_decide_eq_true rfl)
  have h_v389 : R 1 0 0 1 v389 v389 := (r_plt hl h_v388 h_v104 (of_decide_eq_true rfl))
  have e_v389 : (v389 = 1 ↔ sv v388 < sv v104) := e_plt h_v388 h_v104 (of_decide_eq_true rfl)
  have h_v390 : R 1 0 4611686018158952441 4611686018695823359 v390 v390 := (r_psel hl h_v389 h_v104 h_v388 (of_decide_eq_true rfl))
  have e_v390 : v390 = if v389 = 1 then v104 else v388 := e_psel h_v389 h_v104 h_v388 (of_decide_eq_true rfl)
  have h_v391 : R 1 0 4611686018158952449 4611686018695823367 v391 v391 := (r_sub hl (r_add hl h_v31 h_t386_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v391 : sv v391 = sv v31 + sv t386.2 := e_add h_v31 h_t386_2 (of_decide_eq_true rfl)
  have h_v392 : R 1 0 0 1 v392 v392 := (r_plt hl h_v391 h_v33 (of_decide_eq_true rfl))
  have e_v392 : (v392 = 1 ↔ sv v391 < sv v33) := e_plt h_v391 h_v33 (of_decide_eq_true rfl)
  have h_v393 : R 1 0 4611686018158952449 4611686018695823367 v393 v393 := (r_psel hl h_v392 h_v391 h_v33 (of_decide_eq_true rfl))
  have e_v393 : v393 = if v392 = 1 then v391 else v33 := e_psel h_v392 h_v391 h_v33 (of_decide_eq_true rfl)
  have h_v395 : R 1 0 4611686018427387908 4611686018695823367 v395 v395 := (r_sub hl (r_add hl h_v31 h_t386_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v395 : sv v395 = sv v31 + sv t386.1 := e_add h_v31 h_t386_1 (of_decide_eq_true rfl)
  clear h_v335 h_v336 h_v384 h_t386_2 h_v388 h_v389 h_v391 h_v392
  have h_v396 : R 1 0 0 1 v396 v396 := (r_plt hl h_v395 h_v33 (of_decide_eq_true rfl))
  have e_v396 : (v396 = 1 ↔ sv v395 < sv v33) := e_plt h_v395 h_v33 (of_decide_eq_true rfl)
  have h_v397 : R 1 0 4611686018427387908 4611686018695823367 v397 v397 := (r_psel hl h_v396 h_v395 h_v33 (of_decide_eq_true rfl))
  have e_v397 : v397 = if v396 = 1 then v395 else v33 := e_psel h_v396 h_v395 h_v33 (of_decide_eq_true rfl)
  have h_v398 : R 1 0 4611686018427387900 4611686018695823359 v398 v398 := (r_sub hl (r_add hl h_v28 h_t386_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v398 : sv v398 = sv v28 + sv t386.1 := e_add h_v28 h_t386_1 (of_decide_eq_true rfl)
  have h_v399 : R 1 0 4611686018158952441 4611686018695823367 v399 v399 := (r_psel hl h_v341 h_v390 h_v393 (of_decide_eq_true rfl))
  have e_v399 : v399 = if v341 = 1 then v390 else v393 := e_psel h_v341 h_v390 h_v393 (of_decide_eq_true rfl)
  have h_v400 : R 1 0 4611686018427387900 4611686018695823367 v400 v400 := (r_psel hl h_v341 h_v397 h_v398 (of_decide_eq_true rfl))
  have e_v400 : v400 = if v341 = 1 then v397 else v398 := e_psel h_v341 h_v397 h_v398 (of_decide_eq_true rfl)
  have h_v401 : R 1 0 4539628418483879831 4683743618370895977 v401 v401 := (r_smx hl 29 h_v342 h_v400 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v401 : sv v401 = sv v342 * sv v400 := e_smx 29 h_v342 h_v400 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v402 : R 1 0 4539628420631363535 4683743616223412273 v402 v402 := (r_smx hl 29 h_v399 h_v385 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v402 : sv v402 = sv v399 * sv v385 := e_smx 29 h_v399 h_v385 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v403 : R 1 0 0 1 v403 v403 := (r_plt hl h_v402 h_v401 (of_decide_eq_true rfl))
  have e_v403 : (v403 = 1 ↔ sv v402 < sv v401) := e_plt h_v402 h_v401 (of_decide_eq_true rfl)
  have h_v404 : R 1 0 0 1 v404 v404 := (r_sub hl (r_O hl) h_v403 (of_decide_eq_true rfl))
  have e_v404 : (v404 = 1 ↔ ¬v403 = 1) := e_not h_v403 (of_decide_eq_true rfl)
  have h_v405 : R 1 0 0 1 v405 v405 := (r_plt hl h_v401 h_v402 (of_decide_eq_true rfl))
  have e_v405 : (v405 = 1 ↔ sv v401 < sv v402) := e_plt h_v401 h_v402 (of_decide_eq_true rfl)
  have h_v406 : R 1 0 0 1 v406 v406 := (r_sub hl (r_O hl) h_v405 (of_decide_eq_true rfl))
  have e_v406 : (v406 = 1 ↔ ¬v405 = 1) := e_not h_v405 (of_decide_eq_true rfl)
  have h_v407 : R 1 0 0 1 v407 v407 := (r_plt hl h_v9 h_v386 (of_decide_eq_true rfl))
  have e_v407 : (v407 = 1 ↔ sv v9 < sv v386) := e_plt h_v9 h_v386 (of_decide_eq_true rfl)
  have h_v408 : R 1 0 0 1 v408 v408 := (r_sub hl (r_O hl) h_v407 (of_decide_eq_true rfl))
  clear h_v342 h_v385 h_t386_1 h_v393 h_v395 h_v396 h_v397 h_v398 h_v399 h_v400 h_v401 h_v402 h_v403 h_v405
  have e_v408 : (v408 = 1 ↔ ¬v407 = 1) := e_not h_v407 (of_decide_eq_true rfl)
  have h_v409 : R 1 0 0 1 v409 v409 := (r_plt hl h_v215 h_v386 (of_decide_eq_true rfl))
  have e_v409 : (v409 = 1 ↔ sv v215 < sv v386) := e_plt h_v215 h_v386 (of_decide_eq_true rfl)
  have h_v410 : R 1 0 0 1 v410 v410 := (r_sub hl (r_O hl) h_v409 (of_decide_eq_true rfl))
  have e_v410 : (v410 = 1 ↔ ¬v409 = 1) := e_not h_v409 (of_decide_eq_true rfl)
  have h_v411 : R 1 0 0 1 v411 v411 := (r_plt hl h_v18 h_v390 (of_decide_eq_true rfl))
  have e_v411 : (v411 = 1 ↔ sv v18 < sv v390) := e_plt h_v18 h_v390 (of_decide_eq_true rfl)
  have h_v412 : R 1 0 0 1 v412 v412 := (r_land hl h_v404 h_v411 (of_decide_eq_true rfl))
  have e_v412 : (v412 = 1 ↔ v404 = 1 ∧ v411 = 1) := e_land h_v404 h_v411 (of_decide_eq_true rfl)
  have h_v413 : R 1 0 0 1 v413 v413 := (r_land hl h_v410 h_v412 (of_decide_eq_true rfl))
  have e_v413 : (v413 = 1 ↔ v410 = 1 ∧ v412 = 1) := e_land h_v410 h_v412 (of_decide_eq_true rfl)
  have h_v414 : R 1 0 0 1 v414 v414 := (r_lor hl h_v408 h_v413 (of_decide_eq_true rfl))
  have e_v414 : (v414 = 1 ↔ v408 = 1 ∨ v413 = 1) := e_lor h_v408 h_v413 (of_decide_eq_true rfl)
  have h_v415 : R 1 0 0 1 v415 v415 := (r_plt hl h_v386 h_v222 (of_decide_eq_true rfl))
  have e_v415 : (v415 = 1 ↔ sv v386 < sv v222) := e_plt h_v386 h_v222 (of_decide_eq_true rfl)
  have h_v416 : R 1 0 0 1 v416 v416 := (r_sub hl (r_O hl) h_v415 (of_decide_eq_true rfl))
  have e_v416 : (v416 = 1 ↔ ¬v415 = 1) := e_not h_v415 (of_decide_eq_true rfl)
  have h_v417 : R 1 0 0 1 v417 v417 := (r_lor hl h_v406 h_v416 (of_decide_eq_true rfl))
  have e_v417 : (v417 = 1 ↔ v406 = 1 ∨ v416 = 1) := e_lor h_v406 h_v416 (of_decide_eq_true rfl)
  have h_v418 : R 1 0 0 1 v418 v418 := (r_land hl h_v341 h_v414 (of_decide_eq_true rfl))
  have e_v418 : (v418 = 1 ↔ v341 = 1 ∧ v414 = 1) := e_land h_v341 h_v414 (of_decide_eq_true rfl)
  have h_v419 : R 1 0 0 1 v419 v419 := (r_sub hl (r_O hl) h_v341 (of_decide_eq_true rfl))
  have e_v419 : (v419 = 1 ↔ ¬v341 = 1) := e_not h_v341 (of_decide_eq_true rfl)
  have h_v420 : R 1 0 0 1 v420 v420 := (r_land hl h_v417 h_v419 (of_decide_eq_true rfl))
  have e_v420 : (v420 = 1 ↔ v417 = 1 ∧ v419 = 1) := e_land h_v417 h_v419 (of_decide_eq_true rfl)
  clear h_v390 h_v404 h_v406 h_v407 h_v408 h_v409 h_v410 h_v411 h_v412 h_v413 h_v414 h_v415 h_v416 h_v417 h_v419
  have h_v421 : R 1 0 0 1 v421 v421 := (r_lor hl h_v418 h_v420 (of_decide_eq_true rfl))
  have e_v421 : (v421 = 1 ↔ v418 = 1 ∨ v420 = 1) := e_lor h_v418 h_v420 (of_decide_eq_true rfl)
  have h_v422 : R 1 0 4611686017353646081 4611686018427387904 v422 v422 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v386 (of_decide_eq_true rfl))
  have e_v422 : sv v422 = sv v9 - sv v386 := e_sub h_v9 h_v386 (of_decide_eq_true rfl)
  have h_v423 : R 1 0 4611686017353646081 4611686019501129727 v423 v423 := (r_psel hl h_v341 h_v422 h_v386 (of_decide_eq_true rfl))
  have e_v423 : v423 = if v341 = 1 then v422 else v386 := e_psel h_v341 h_v422 h_v386 (of_decide_eq_true rfl)
  have h_v424 : R 1 0 4611686017353646081 4611686019501129727 v424 v424 := (r_psel hl h_v421 h_v423 h_v222 (of_decide_eq_true rfl))
  have e_v424 : v424 = if v421 = 1 then v423 else v222 := e_psel h_v421 h_v423 h_v222 (of_decide_eq_true rfl)
  have h_v426 : R 1 0 4611686017353646081 4611686019501129727 v426 v426 := (r_psel hl h_v338 h_v222 h_v424 (of_decide_eq_true rfl))
  have e_v426 : v426 = if v338 = 1 then v222 else v424 := e_psel h_v338 h_v222 h_v424 (of_decide_eq_true rfl)
  have h_v427 : R 1 0 4611686018427387904 4611686052787126264 v427 v427 := (r_add hl (r_pshr1 hl h_v4) h_H61r (of_decide_eq_true rfl))
  have e_v427 : sv v427 = sv v4 / 2 := e_halfF h_v4
  have h_v428 : R 1 0 4611686018427387904 4611686052787126264 v428 v428 := (r_add hl (r_pshr1 hl (r_add hl h_v5 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v428 : sv v428 = (sv v5 + 1) / 2 := e_halfC h_v5 (of_decide_eq_true rfl)
  have h_v429 : R 1 0 0 1 v429 v429 := (r_plt hl h_v18 h_v427 (of_decide_eq_true rfl))
  have e_v429 : (v429 = 1 ↔ sv v18 < sv v427) := e_plt h_v18 h_v427 (of_decide_eq_true rfl)
  have h_v430 : R 1 0 0 1 v430 v430 := (r_plt hl h_v20 h_v428 (of_decide_eq_true rfl))
  have e_v430 : (v430 = 1 ↔ sv v20 < sv v428) := e_plt h_v20 h_v428 (of_decide_eq_true rfl)
  have h_v431 : R 1 0 0 1 v431 v431 := (r_sub hl (r_O hl) h_v430 (of_decide_eq_true rfl))
  have e_v431 : (v431 = 1 ↔ ¬v430 = 1) := e_not h_v430 (of_decide_eq_true rfl)
  have h_v432 : R 1 0 0 1 v432 v432 := (r_land hl h_v429 h_v431 (of_decide_eq_true rfl))
  have e_v432 : (v432 = 1 ↔ v429 = 1 ∧ v431 = 1) := e_land h_v429 h_v431 (of_decide_eq_true rfl)
  have h_t427_1 : R 1 0 4611686018427387904 4611686018695823363 t427.1 t427.1 := r_sc1 hl h_v427 (of_decide_eq_true rfl)
  have h_t427_2 : R 1 0 4611686018158952445 4611686018695823363 t427.2 t427.2 := r_sc2 hl h_v427 (of_decide_eq_true rfl)
  have e_t427_1 : sv t427.1 = (sc28pS (scArg v427)).1 := e_sc1 h_v427 (of_decide_eq_true rfl)
  clear h_v338 h_v341 h_v386 h_v418 h_v420 h_v421 h_v422 h_v423 h_v424 h_v430
  have e_t427_2 : sv t427.2 = (sc28pS (scArg v427)).2 := e_sc2 h_v427 (of_decide_eq_true rfl)
  have h_t428_1 : R 1 0 4611686018427387904 4611686018695823363 t428.1 t428.1 := r_sc1 hl h_v428 (of_decide_eq_true rfl)
  have h_t428_2 : R 1 0 4611686018158952445 4611686018695823363 t428.2 t428.2 := r_sc2 hl h_v428 (of_decide_eq_true rfl)
  have e_t428_1 : sv t428.1 = (sc28pS (scArg v428)).1 := e_sc1 h_v428 (of_decide_eq_true rfl)
  have e_t428_2 : sv t428.2 = (sc28pS (scArg v428)).2 := e_sc2 h_v428 (of_decide_eq_true rfl)
  have h_v435 : R 1 0 0 1 v435 v435 := (r_plt hl h_t427_1 h_t428_1 (of_decide_eq_true rfl))
  have e_v435 : (v435 = 1 ↔ sv t427.1 < sv t428.1) := e_plt h_t427_1 h_t428_1 (of_decide_eq_true rfl)
  have h_v436 : R 1 0 4611686018427387904 4611686018695823363 v436 v436 := (r_psel hl h_v435 h_t427_1 h_t428_1 (of_decide_eq_true rfl))
  have e_v436 : v436 = if v435 = 1 then t427.1 else t428.1 := e_psel h_v435 h_t427_1 h_t428_1 (of_decide_eq_true rfl)
  have h_v437 : R 1 0 4611686018427387900 4611686018695823359 v437 v437 := (r_sub hl (r_add hl h_v28 h_v436 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v437 : sv v437 = sv v28 + sv v436 := e_add h_v28 h_v436 (of_decide_eq_true rfl)
  have h_v438 : R 1 0 4611686018427387904 4611686018695823363 v438 v438 := (r_psel hl h_v435 h_t428_1 h_t427_1 (of_decide_eq_true rfl))
  have e_v438 : v438 = if v435 = 1 then t428.1 else t427.1 := e_psel h_v435 h_t428_1 h_t427_1 (of_decide_eq_true rfl)
  have h_v439 : R 1 0 4611686018427387908 4611686018695823367 v439 v439 := (r_sub hl (r_add hl h_v31 h_v438 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v439 : sv v439 = sv v31 + sv v438 := e_add h_v31 h_v438 (of_decide_eq_true rfl)
  have h_v440 : R 1 0 0 1 v440 v440 := (r_plt hl h_v439 h_v33 (of_decide_eq_true rfl))
  have e_v440 : (v440 = 1 ↔ sv v439 < sv v33) := e_plt h_v439 h_v33 (of_decide_eq_true rfl)
  have h_v441 : R 1 0 4611686018427387908 4611686018695823367 v441 v441 := (r_psel hl h_v440 h_v439 h_v33 (of_decide_eq_true rfl))
  have e_v441 : v441 = if v440 = 1 then v439 else v33 := e_psel h_v440 h_v439 h_v33 (of_decide_eq_true rfl)
  have h_v442 : R 1 0 0 1 v442 v442 := (r_plt hl h_v427 h_v36 (of_decide_eq_true rfl))
  have e_v442 : (v442 = 1 ↔ sv v427 < sv v36) := e_plt h_v427 h_v36 (of_decide_eq_true rfl)
  have h_v443 : R 1 0 0 1 v443 v443 := (r_plt hl h_v38 h_v428 (of_decide_eq_true rfl))
  have e_v443 : (v443 = 1 ↔ sv v38 < sv v428) := e_plt h_v38 h_v428 (of_decide_eq_true rfl)
  have h_v444 : R 1 0 0 1 v444 v444 := (r_land hl h_v442 h_v443 (of_decide_eq_true rfl))
  have e_v444 : (v444 = 1 ↔ v442 = 1 ∧ v443 = 1) := e_land h_v442 h_v443 (of_decide_eq_true rfl)
  clear h_v435 h_v436 h_v438 h_v439 h_v440 h_v443
  have h_v445 : R 1 0 4611686018427387908 4611686018695823367 v445 v445 := (r_psel hl h_v444 h_v33 h_v441 (of_decide_eq_true rfl))
  have e_v445 : v445 = if v444 = 1 then v33 else v441 := e_psel h_v444 h_v33 h_v441 (of_decide_eq_true rfl)
  have h_v446 : R 1 0 0 1 v446 v446 := (r_plt hl h_v437 h_v9 (of_decide_eq_true rfl))
  have e_v446 : (v446 = 1 ↔ sv v437 < sv v9) := e_plt h_v437 h_v9 (of_decide_eq_true rfl)
  have h_v448 : R 1 0 0 1 v448 v448 := (r_plt hl h_v9 h_v445 (of_decide_eq_true rfl))
  have e_v448 : (v448 = 1 ↔ sv v9 < sv v445) := e_plt h_v9 h_v445 (of_decide_eq_true rfl)
  have h_v449 : R 1 0 0 1 v449 v449 := (r_sub hl (r_O hl) h_v448 (of_decide_eq_true rfl))
  have e_v449 : (v449 = 1 ↔ ¬v448 = 1) := e_not h_v448 (of_decide_eq_true rfl)
  have h_v450 : R 1 0 0 1 v450 v450 := (r_land hl h_v446 h_v449 (of_decide_eq_true rfl))
  have e_v450 : (v450 = 1 ↔ v446 = 1 ∧ v449 = 1) := e_land h_v446 h_v449 (of_decide_eq_true rfl)
  have h_v451 : R 1 0 0 1 v451 v451 := (r_land hl h_v446 h_v448 (of_decide_eq_true rfl))
  have e_v451 : (v451 = 1 ↔ v446 = 1 ∧ v448 = 1) := e_land h_v446 h_v448 (of_decide_eq_true rfl)
  have h_v452 : R 1 0 0 1 v452 v452 := (r_land hl h_v66 h_v451 (of_decide_eq_true rfl))
  have e_v452 : (v452 = 1 ↔ v66 = 1 ∧ v451 = 1) := e_land h_v66 h_v451 (of_decide_eq_true rfl)
  have h_v453 : R 1 0 0 1 v453 v453 := (r_land hl h_v62 h_v451 (of_decide_eq_true rfl))
  have e_v453 : (v453 = 1 ↔ v62 = 1 ∧ v451 = 1) := e_land h_v62 h_v451 (of_decide_eq_true rfl)
  have h_v454 : R 1 0 0 1 v454 v454 := (r_lor hl h_v450 h_v453 (of_decide_eq_true rfl))
  have e_v454 : (v454 = 1 ↔ v450 = 1 ∨ v453 = 1) := e_lor h_v450 h_v453 (of_decide_eq_true rfl)
  have h_v455 : R 1 0 4611686018427387900 4611686018695823367 v455 v455 := (r_psel hl h_v454 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v455 : v455 = if v454 = 1 then v41 else v29 := e_psel h_v454 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v456 : R 1 0 0 1 v456 v456 := (r_sub hl (r_O hl) h_v450 (of_decide_eq_true rfl))
  have e_v456 : (v456 = 1 ↔ ¬v450 = 1) := e_not h_v450 (of_decide_eq_true rfl)
  have h_v457 : R 1 0 0 1 v457 v457 := (r_land hl h_v66 h_v456 (of_decide_eq_true rfl))
  have e_v457 : (v457 = 1 ↔ v66 = 1 ∧ v456 = 1) := e_land h_v66 h_v456 (of_decide_eq_true rfl)
  have h_v458 : R 1 0 0 1 v458 v458 := (r_lor hl h_v65 h_v457 (of_decide_eq_true rfl))
  clear h_v441 h_v444 h_v446 h_v448 h_v449 h_v453 h_v454
  have e_v458 : (v458 = 1 ↔ v65 = 1 ∨ v457 = 1) := e_lor h_v65 h_v457 (of_decide_eq_true rfl)
  have h_v459 : R 1 0 4611686018427387900 4611686018695823367 v459 v459 := (r_psel hl h_v458 h_v445 h_v437 (of_decide_eq_true rfl))
  have e_v459 : v459 = if v458 = 1 then v445 else v437 := e_psel h_v458 h_v445 h_v437 (of_decide_eq_true rfl)
  have h_v460 : R 1 0 0 1 v460 v460 := (r_land hl h_v65 h_v451 (of_decide_eq_true rfl))
  have e_v460 : (v460 = 1 ↔ v65 = 1 ∧ v451 = 1) := e_land h_v65 h_v451 (of_decide_eq_true rfl)
  have h_v461 : R 1 0 0 1 v461 v461 := (r_lor hl h_v450 h_v460 (of_decide_eq_true rfl))
  have e_v461 : (v461 = 1 ↔ v450 = 1 ∨ v460 = 1) := e_lor h_v450 h_v460 (of_decide_eq_true rfl)
  have h_v462 : R 1 0 4611686018427387900 4611686018695823367 v462 v462 := (r_psel hl h_v461 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v462 : v462 = if v461 = 1 then v29 else v41 := e_psel h_v461 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v463 : R 1 0 0 1 v463 v463 := (r_land hl h_v66 h_v450 (of_decide_eq_true rfl))
  have e_v463 : (v463 = 1 ↔ v66 = 1 ∧ v450 = 1) := e_land h_v66 h_v450 (of_decide_eq_true rfl)
  have h_v464 : R 1 0 0 1 v464 v464 := (r_lor hl h_v65 h_v463 (of_decide_eq_true rfl))
  have e_v464 : (v464 = 1 ↔ v65 = 1 ∨ v463 = 1) := e_lor h_v65 h_v463 (of_decide_eq_true rfl)
  have h_v465 : R 1 0 4611686018427387900 4611686018695823367 v465 v465 := (r_psel hl h_v464 h_v437 h_v445 (of_decide_eq_true rfl))
  have e_v465 : v465 = if v464 = 1 then v437 else v445 := e_psel h_v464 h_v437 h_v445 (of_decide_eq_true rfl)
  have h_v466 : R 1 0 4611686017353646052 4683743616223412273 v466 v466 := (r_smx hl 29 h_v459 h_v455 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v466 : sv v466 = sv v459 * sv v455 := e_smx 29 h_v459 h_v455 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v467 : R 1 0 4611686018427387899 4611686018695823374 v467 v467 := (r_srdF hl h_v466 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v467 : sv v467 = sv v466 / 2 ^ 28 := e_srdF h_v466 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v468 : R 1 0 4611686017353646052 4683743616223412273 v468 v468 := (r_smx hl 29 h_v465 h_v462 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v468 : sv v468 = sv v465 * sv v462 := e_smx 29 h_v465 h_v462 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v469 : R 1 0 4611686018427387900 4611686018695823375 v469 v469 := (r_srdC hl h_v468 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v469 : sv v469 = -((-sv v468) / 2 ^ 28) := e_srdC h_v468 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v470 : R 1 0 4611686017353646052 4683743614075928569 v470 v470 := (r_smx hl 29 h_v437 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl))
  have e_v470 : sv v470 = sv v437 * sv v41 := e_smx 29 h_v437 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl)
  clear h_v455 h_v457 h_v458 h_v459 h_v460 h_v461 h_v462 h_v463 h_v464 h_v465 h_v466 h_v468
  have h_v471 : R 1 0 4611686018427387899 4611686018695823365 v471 v471 := (r_srdF hl h_v470 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl))
  have e_v471 : sv v471 = sv v470 / 2 ^ 28 := e_srdF h_v470 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl)
  have h_v472 : R 1 0 4611686017353646084 4683743611928444929 v472 v472 := (r_smx hl 29 h_v437 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl))
  have e_v472 : sv v472 = sv v437 * sv v29 := e_smx 29 h_v437 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl)
  have h_v473 : R 1 0 4611686018427387901 4611686018695823359 v473 v473 := (r_srdC hl h_v472 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl))
  have e_v473 : sv v473 = -((-sv v472) / 2 ^ 28) := e_srdC h_v472 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl)
  have h_v474 : R 1 0 0 1 v474 v474 := (r_plt hl h_v467 h_v471 (of_decide_eq_true rfl))
  have e_v474 : (v474 = 1 ↔ sv v467 < sv v471) := e_plt h_v467 h_v471 (of_decide_eq_true rfl)
  have h_v475 : R 1 0 4611686018427387899 4611686018695823374 v475 v475 := (r_psel hl h_v474 h_v467 h_v471 (of_decide_eq_true rfl))
  have e_v475 : v475 = if v474 = 1 then v467 else v471 := e_psel h_v474 h_v467 h_v471 (of_decide_eq_true rfl)
  have h_v476 : R 1 0 0 1 v476 v476 := (r_plt hl h_v469 h_v473 (of_decide_eq_true rfl))
  have e_v476 : (v476 = 1 ↔ sv v469 < sv v473) := e_plt h_v469 h_v473 (of_decide_eq_true rfl)
  have h_v477 : R 1 0 4611686018427387900 4611686018695823375 v477 v477 := (r_psel hl h_v476 h_v473 h_v469 (of_decide_eq_true rfl))
  have e_v477 : v477 = if v476 = 1 then v473 else v469 := e_psel h_v476 h_v473 h_v469 (of_decide_eq_true rfl)
  have h_v478 : R 1 0 4611686018427387899 4611686018695823374 v478 v478 := (r_psel hl h_v452 h_v475 h_v467 (of_decide_eq_true rfl))
  have e_v478 : v478 = if v452 = 1 then v475 else v467 := e_psel h_v452 h_v475 h_v467 (of_decide_eq_true rfl)
  have h_v479 : R 1 0 4611686018427387900 4611686018695823375 v479 v479 := (r_psel hl h_v452 h_v477 h_v469 (of_decide_eq_true rfl))
  have e_v479 : v479 = if v452 = 1 then v477 else v469 := e_psel h_v452 h_v477 h_v469 (of_decide_eq_true rfl)
  have h_v480 : R 1 0 0 1 v480 v480 := (r_plt hl h_v18 h_v478 (of_decide_eq_true rfl))
  have e_v480 : (v480 = 1 ↔ sv v18 < sv v478) := e_plt h_v18 h_v478 (of_decide_eq_true rfl)
  have h_v481 : R 1 0 4611686018427387904 4611686052787126264 v481 v481 := (r_add hl (r_pshr1 hl h_v5) h_H61r (of_decide_eq_true rfl))
  have e_v481 : sv v481 = sv v5 / 2 := e_halfF h_v5
  have h_v482 : R 1 0 0 1 v482 v482 := (r_plt hl h_v18 h_v481 (of_decide_eq_true rfl))
  have e_v482 : (v482 = 1 ↔ sv v18 < sv v481) := e_plt h_v18 h_v481 (of_decide_eq_true rfl)
  have h_v483 : R 1 0 0 1 v483 v483 := (r_land hl h_v431 h_v482 (of_decide_eq_true rfl))
  clear h_v5 h_v452 h_v467 h_v469 h_v470 h_v471 h_v472 h_v473 h_v474 h_v475 h_v476 h_v477
  have e_v483 : (v483 = 1 ↔ v431 = 1 ∧ v482 = 1) := e_land h_v431 h_v482 (of_decide_eq_true rfl)
  have h_v485 : R 1 0 4611686018158952441 4611686018695823359 v485 v485 := (r_sub hl (r_add hl h_v28 h_t428_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v485 : sv v485 = sv v28 + sv t428.2 := e_add h_v28 h_t428_2 (of_decide_eq_true rfl)
  have h_v486 : R 1 0 0 1 v486 v486 := (r_plt hl h_v485 h_v104 (of_decide_eq_true rfl))
  have e_v486 : (v486 = 1 ↔ sv v485 < sv v104) := e_plt h_v485 h_v104 (of_decide_eq_true rfl)
  have h_v487 : R 1 0 4611686018158952441 4611686018695823359 v487 v487 := (r_psel hl h_v486 h_v104 h_v485 (of_decide_eq_true rfl))
  have e_v487 : v487 = if v486 = 1 then v104 else v485 := e_psel h_v486 h_v104 h_v485 (of_decide_eq_true rfl)
  have h_v488 : R 1 0 0 1 v488 v488 := (r_plt hl h_v107 h_v428 (of_decide_eq_true rfl))
  have e_v488 : (v488 = 1 ↔ sv v107 < sv v428) := e_plt h_v107 h_v428 (of_decide_eq_true rfl)
  have h_v489 : R 1 0 4611686018158952441 4611686018695823359 v489 v489 := (r_psel hl h_v488 h_v104 h_v487 (of_decide_eq_true rfl))
  have e_v489 : v489 = if v488 = 1 then v104 else v487 := e_psel h_v488 h_v104 h_v487 (of_decide_eq_true rfl)
  have h_v543 : R 1 0 0 1 v543 v543 := (r_plt hl h_v489 h_v9 (of_decide_eq_true rfl))
  have e_v543 : (v543 = 1 ↔ sv v489 < sv v9) := e_plt h_v489 h_v9 (of_decide_eq_true rfl)
  have h_v631 : R 1 0 4611686018427387904 4611686052787126264 v631 v631 := (r_add hl (r_pshr1 hl (r_add hl h_v4 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v631 : sv v631 = (sv v4 + 1) / 2 := e_halfC h_v4 (of_decide_eq_true rfl)
  have h_v632 : R 1 0 0 1 v632 v632 := (r_plt hl h_v20 h_v631 (of_decide_eq_true rfl))
  have e_v632 : (v632 = 1 ↔ sv v20 < sv v631) := e_plt h_v20 h_v631 (of_decide_eq_true rfl)
  have h_v633 : R 1 0 0 1 v633 v633 := (r_sub hl (r_O hl) h_v632 (of_decide_eq_true rfl))
  have e_v633 : (v633 = 1 ↔ ¬v632 = 1) := e_not h_v632 (of_decide_eq_true rfl)
  have h_v634 : R 1 0 0 1 v634 v634 := (r_land hl h_v429 h_v633 (of_decide_eq_true rfl))
  have e_v634 : (v634 = 1 ↔ v429 = 1 ∧ v633 = 1) := e_land h_v429 h_v633 (of_decide_eq_true rfl)
  have h_v642 : R 1 0 4611686018158952449 4611686018695823367 v642 v642 := (r_sub hl (r_add hl h_v31 h_t427_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v642 : sv v642 = sv v31 + sv t427.2 := e_add h_v31 h_t427_2 (of_decide_eq_true rfl)
  have h_v643 : R 1 0 0 1 v643 v643 := (r_plt hl h_v642 h_v33 (of_decide_eq_true rfl))
  have e_v643 : (v643 = 1 ↔ sv v642 < sv v33) := e_plt h_v642 h_v33 (of_decide_eq_true rfl)
  clear h_v4 h_v107 h_v431 h_t427_2 h_t428_2 h_v482 h_v485 h_v486 h_v487 h_v488 h_v632 h_v633
  have h_v644 : R 1 0 4611686018158952449 4611686018695823367 v644 v644 := (r_psel hl h_v643 h_v642 h_v33 (of_decide_eq_true rfl))
  have e_v644 : v644 = if v643 = 1 then v642 else v33 := e_psel h_v643 h_v642 h_v33 (of_decide_eq_true rfl)
  have h_v645 : R 1 0 0 1 v645 v645 := (r_plt hl h_v427 h_v114 (of_decide_eq_true rfl))
  have e_v645 : (v645 = 1 ↔ sv v427 < sv v114) := e_plt h_v427 h_v114 (of_decide_eq_true rfl)
  have h_v646 : R 1 0 4611686018158952449 4611686018695823367 v646 v646 := (r_psel hl h_v645 h_v33 h_v644 (of_decide_eq_true rfl))
  have e_v646 : v646 = if v645 = 1 then v33 else v644 := e_psel h_v645 h_v33 h_v644 (of_decide_eq_true rfl)
  have h_t631_1 : R 1 0 4611686018427387904 4611686018695823363 t631.1 t631.1 := r_sc1 hl h_v631 (of_decide_eq_true rfl)
  have h_t631_2 : R 1 0 4611686018158952445 4611686018695823363 t631.2 t631.2 := r_sc2 hl h_v631 (of_decide_eq_true rfl)
  have e_t631_1 : sv t631.1 = (sc28pS (scArg v631)).1 := e_sc1 h_v631 (of_decide_eq_true rfl)
  have e_t631_2 : sv t631.2 = (sc28pS (scArg v631)).2 := e_sc2 h_v631 (of_decide_eq_true rfl)
  have h_v648 : R 1 0 0 1 v648 v648 := (r_plt hl h_t427_1 h_t631_1 (of_decide_eq_true rfl))
  have e_v648 : (v648 = 1 ↔ sv t427.1 < sv t631.1) := e_plt h_t427_1 h_t631_1 (of_decide_eq_true rfl)
  have h_v649 : R 1 0 4611686018427387904 4611686018695823363 v649 v649 := (r_psel hl h_v648 h_t427_1 h_t631_1 (of_decide_eq_true rfl))
  have e_v649 : v649 = if v648 = 1 then t427.1 else t631.1 := e_psel h_v648 h_t427_1 h_t631_1 (of_decide_eq_true rfl)
  have h_v650 : R 1 0 4611686018427387900 4611686018695823359 v650 v650 := (r_sub hl (r_add hl h_v28 h_v649 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v650 : sv v650 = sv v28 + sv v649 := e_add h_v28 h_v649 (of_decide_eq_true rfl)
  have h_v651 : R 1 0 4611686018427387904 4611686018695823363 v651 v651 := (r_psel hl h_v648 h_t631_1 h_t427_1 (of_decide_eq_true rfl))
  have e_v651 : v651 = if v648 = 1 then t631.1 else t427.1 := e_psel h_v648 h_t631_1 h_t427_1 (of_decide_eq_true rfl)
  have h_v652 : R 1 0 4611686018427387908 4611686018695823367 v652 v652 := (r_sub hl (r_add hl h_v31 h_v651 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v652 : sv v652 = sv v31 + sv v651 := e_add h_v31 h_v651 (of_decide_eq_true rfl)
  have h_v653 : R 1 0 0 1 v653 v653 := (r_plt hl h_v652 h_v33 (of_decide_eq_true rfl))
  have e_v653 : (v653 = 1 ↔ sv v652 < sv v33) := e_plt h_v652 h_v33 (of_decide_eq_true rfl)
  have h_v654 : R 1 0 4611686018427387908 4611686018695823367 v654 v654 := (r_psel hl h_v653 h_v652 h_v33 (of_decide_eq_true rfl))
  have e_v654 : v654 = if v653 = 1 then v652 else v33 := e_psel h_v653 h_v652 h_v33 (of_decide_eq_true rfl)
  have h_v655 : R 1 0 0 1 v655 v655 := (r_plt hl h_v38 h_v631 (of_decide_eq_true rfl))
  clear h_v114 h_v642 h_v643 h_v644 h_v645 h_t631_2 e_t631_2 h_v648 h_v649 h_v651 h_v652 h_v653
  have e_v655 : (v655 = 1 ↔ sv v38 < sv v631) := e_plt h_v38 h_v631 (of_decide_eq_true rfl)
  have h_v656 : R 1 0 0 1 v656 v656 := (r_land hl h_v442 h_v655 (of_decide_eq_true rfl))
  have e_v656 : (v656 = 1 ↔ v442 = 1 ∧ v655 = 1) := e_land h_v442 h_v655 (of_decide_eq_true rfl)
  have h_v657 : R 1 0 4611686018427387908 4611686018695823367 v657 v657 := (r_psel hl h_v656 h_v33 h_v654 (of_decide_eq_true rfl))
  have e_v657 : v657 = if v656 = 1 then v33 else v654 := e_psel h_v656 h_v33 h_v654 (of_decide_eq_true rfl)
  have h_v658 : R 1 0 0 1 v658 v658 := (r_plt hl h_v650 h_v9 (of_decide_eq_true rfl))
  have e_v658 : (v658 = 1 ↔ sv v650 < sv v9) := e_plt h_v650 h_v9 (of_decide_eq_true rfl)
  have h_v660 : R 1 0 0 1 v660 v660 := (r_plt hl h_v9 h_v657 (of_decide_eq_true rfl))
  have e_v660 : (v660 = 1 ↔ sv v9 < sv v657) := e_plt h_v9 h_v657 (of_decide_eq_true rfl)
  have h_v661 : R 1 0 0 1 v661 v661 := (r_sub hl (r_O hl) h_v660 (of_decide_eq_true rfl))
  have e_v661 : (v661 = 1 ↔ ¬v660 = 1) := e_not h_v660 (of_decide_eq_true rfl)
  have h_v662 : R 1 0 0 1 v662 v662 := (r_land hl h_v658 h_v661 (of_decide_eq_true rfl))
  have e_v662 : (v662 = 1 ↔ v658 = 1 ∧ v661 = 1) := e_land h_v658 h_v661 (of_decide_eq_true rfl)
  have h_v663 : R 1 0 0 1 v663 v663 := (r_land hl h_v658 h_v660 (of_decide_eq_true rfl))
  have e_v663 : (v663 = 1 ↔ v658 = 1 ∧ v660 = 1) := e_land h_v658 h_v660 (of_decide_eq_true rfl)
  have h_v664 : R 1 0 0 1 v664 v664 := (r_land hl h_v148 h_v663 (of_decide_eq_true rfl))
  have e_v664 : (v664 = 1 ↔ v148 = 1 ∧ v663 = 1) := e_land h_v148 h_v663 (of_decide_eq_true rfl)
  have h_v665 : R 1 0 0 1 v665 v665 := (r_land hl h_v144 h_v663 (of_decide_eq_true rfl))
  have e_v665 : (v665 = 1 ↔ v144 = 1 ∧ v663 = 1) := e_land h_v144 h_v663 (of_decide_eq_true rfl)
  have h_v666 : R 1 0 0 1 v666 v666 := (r_lor hl h_v662 h_v665 (of_decide_eq_true rfl))
  have e_v666 : (v666 = 1 ↔ v662 = 1 ∨ v665 = 1) := e_lor h_v662 h_v665 (of_decide_eq_true rfl)
  have h_v667 : R 1 0 4611686018158952441 4611686018695823367 v667 v667 := (r_psel hl h_v666 h_v116 h_v109 (of_decide_eq_true rfl))
  have e_v667 : v667 = if v666 = 1 then v116 else v109 := e_psel h_v666 h_v116 h_v109 (of_decide_eq_true rfl)
  have h_v668 : R 1 0 0 1 v668 v668 := (r_sub hl (r_O hl) h_v662 (of_decide_eq_true rfl))
  have e_v668 : (v668 = 1 ↔ ¬v662 = 1) := e_not h_v662 (of_decide_eq_true rfl)
  clear h_v654 h_v655 h_v656 h_v658 h_v660 h_v661 h_v665 h_v666
  have h_v669 : R 1 0 0 1 v669 v669 := (r_land hl h_v148 h_v668 (of_decide_eq_true rfl))
  have e_v669 : (v669 = 1 ↔ v148 = 1 ∧ v668 = 1) := e_land h_v148 h_v668 (of_decide_eq_true rfl)
  have h_v670 : R 1 0 0 1 v670 v670 := (r_lor hl h_v147 h_v669 (of_decide_eq_true rfl))
  have e_v670 : (v670 = 1 ↔ v147 = 1 ∨ v669 = 1) := e_lor h_v147 h_v669 (of_decide_eq_true rfl)
  have h_v671 : R 1 0 4611686018427387900 4611686018695823367 v671 v671 := (r_psel hl h_v670 h_v657 h_v650 (of_decide_eq_true rfl))
  have e_v671 : v671 = if v670 = 1 then v657 else v650 := e_psel h_v670 h_v657 h_v650 (of_decide_eq_true rfl)
  have h_v672 : R 1 0 0 1 v672 v672 := (r_land hl h_v147 h_v663 (of_decide_eq_true rfl))
  have e_v672 : (v672 = 1 ↔ v147 = 1 ∧ v663 = 1) := e_land h_v147 h_v663 (of_decide_eq_true rfl)
  have h_v673 : R 1 0 0 1 v673 v673 := (r_lor hl h_v662 h_v672 (of_decide_eq_true rfl))
  have e_v673 : (v673 = 1 ↔ v662 = 1 ∨ v672 = 1) := e_lor h_v662 h_v672 (of_decide_eq_true rfl)
  have h_v674 : R 1 0 4611686018158952441 4611686018695823367 v674 v674 := (r_psel hl h_v673 h_v109 h_v116 (of_decide_eq_true rfl))
  have e_v674 : v674 = if v673 = 1 then v109 else v116 := e_psel h_v673 h_v109 h_v116 (of_decide_eq_true rfl)
  have h_v675 : R 1 0 0 1 v675 v675 := (r_land hl h_v148 h_v662 (of_decide_eq_true rfl))
  have e_v675 : (v675 = 1 ↔ v148 = 1 ∧ v662 = 1) := e_land h_v148 h_v662 (of_decide_eq_true rfl)
  have h_v676 : R 1 0 0 1 v676 v676 := (r_lor hl h_v147 h_v675 (of_decide_eq_true rfl))
  have e_v676 : (v676 = 1 ↔ v147 = 1 ∨ v675 = 1) := e_lor h_v147 h_v675 (of_decide_eq_true rfl)
  have h_v677 : R 1 0 4611686018427387900 4611686018695823367 v677 v677 := (r_psel hl h_v676 h_v650 h_v657 (of_decide_eq_true rfl))
  have e_v677 : v677 = if v676 = 1 then v650 else v657 := e_psel h_v676 h_v650 h_v657 (of_decide_eq_true rfl)
  have h_v678 : R 1 0 4539628420631363535 4683743616223412273 v678 v678 := (r_smx hl 29 h_v671 h_v667 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v678 : sv v678 = sv v671 * sv v667 := e_smx 29 h_v671 h_v667 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v679 : R 1 0 4611686018158952433 4611686018695823374 v679 v679 := (r_srdF hl h_v678 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v679 : sv v679 = sv v678 / 2 ^ 28 := e_srdF h_v678 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v680 : R 1 0 4539628420631363535 4683743616223412273 v680 v680 := (r_smx hl 29 h_v677 h_v674 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v680 : sv v680 = sv v677 * sv v674 := e_smx 29 h_v677 h_v674 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v681 : R 1 0 4611686018158952434 4611686018695823375 v681 v681 := (r_srdC hl h_v680 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  clear h_v657 h_v662 h_v663 h_v667 h_v668 h_v669 h_v670 h_v671 h_v672 h_v673 h_v674 h_v675 h_v676 h_v677 h_v678
  have e_v681 : sv v681 = -((-sv v680) / 2 ^ 28) := e_srdC h_v680 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v682 : R 1 0 4539628424926330879 4683743614075928569 v682 v682 := (r_smx hl 29 h_v650 h_v116 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl))
  have e_v682 : sv v682 = sv v650 * sv v116 := e_smx 29 h_v650 h_v116 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl)
  have h_v683 : R 1 0 4611686018158952449 4611686018695823365 v683 v683 := (r_srdF hl h_v682 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl))
  have e_v683 : sv v683 = sv v682 / 2 ^ 28 := e_srdF h_v682 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl)
  have h_v684 : R 1 0 4539628422778847239 4683743611928444929 v684 v684 := (r_smx hl 29 h_v650 h_v109 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl))
  have e_v684 : sv v684 = sv v650 * sv v109 := e_smx 29 h_v650 h_v109 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl)
  have h_v685 : R 1 0 4611686018158952443 4611686018695823359 v685 v685 := (r_srdC hl h_v684 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl))
  have e_v685 : sv v685 = -((-sv v684) / 2 ^ 28) := e_srdC h_v684 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl)
  have h_v686 : R 1 0 0 1 v686 v686 := (r_plt hl h_v679 h_v683 (of_decide_eq_true rfl))
  have e_v686 : (v686 = 1 ↔ sv v679 < sv v683) := e_plt h_v679 h_v683 (of_decide_eq_true rfl)
  have h_v687 : R 1 0 4611686018158952433 4611686018695823374 v687 v687 := (r_psel hl h_v686 h_v679 h_v683 (of_decide_eq_true rfl))
  have e_v687 : v687 = if v686 = 1 then v679 else v683 := e_psel h_v686 h_v679 h_v683 (of_decide_eq_true rfl)
  have h_v688 : R 1 0 0 1 v688 v688 := (r_plt hl h_v681 h_v685 (of_decide_eq_true rfl))
  have e_v688 : (v688 = 1 ↔ sv v681 < sv v685) := e_plt h_v681 h_v685 (of_decide_eq_true rfl)
  have h_v689 : R 1 0 4611686018158952434 4611686018695823375 v689 v689 := (r_psel hl h_v688 h_v685 h_v681 (of_decide_eq_true rfl))
  have e_v689 : v689 = if v688 = 1 then v685 else v681 := e_psel h_v688 h_v685 h_v681 (of_decide_eq_true rfl)
  have h_v690 : R 1 0 4611686018158952433 4611686018695823374 v690 v690 := (r_psel hl h_v664 h_v687 h_v679 (of_decide_eq_true rfl))
  have e_v690 : v690 = if v664 = 1 then v687 else v679 := e_psel h_v664 h_v687 h_v679 (of_decide_eq_true rfl)
  have h_v691 : R 1 0 4611686018158952434 4611686018695823375 v691 v691 := (r_psel hl h_v664 h_v689 h_v681 (of_decide_eq_true rfl))
  have e_v691 : v691 = if v664 = 1 then v689 else v681 := e_psel h_v664 h_v689 h_v681 (of_decide_eq_true rfl)
  have h_v692 : R 1 0 0 1 v692 v692 := (r_plt hl h_v9 h_v690 (of_decide_eq_true rfl))
  have e_v692 : (v692 = 1 ↔ sv v9 < sv v690) := e_plt h_v9 h_v690 (of_decide_eq_true rfl)
  have h_v693 : R 1 0 0 1 v693 v693 := (r_sub hl (r_O hl) h_v692 (of_decide_eq_true rfl))
  have e_v693 : (v693 = 1 ↔ ¬v692 = 1) := e_not h_v692 (of_decide_eq_true rfl)
  clear h_v650 h_v664 h_v679 h_v680 h_v681 h_v682 h_v683 h_v684 h_v685 h_v686 h_v687 h_v688 h_v689 h_v692
  have h_v696 : R 1 0 0 1 v696 v696 := (r_plt hl h_v646 h_v9 (of_decide_eq_true rfl))
  have e_v696 : (v696 = 1 ↔ sv v646 < sv v9) := e_plt h_v646 h_v9 (of_decide_eq_true rfl)
  have h_v697 : R 1 0 4611686018158952433 4611686018695823375 v697 v697 := (r_psel hl h_v696 h_v691 h_v690 (of_decide_eq_true rfl))
  have e_v697 : v697 = if v696 = 1 then v691 else v690 := e_psel h_v696 h_v691 h_v690 (of_decide_eq_true rfl)
  have h_v739 : R 1 0 4611686018158952441 4611686018695823359 v739 v739 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v646 (of_decide_eq_true rfl))
  have e_v739 : sv v739 = sv v9 - sv v646 := e_sub h_v9 h_v646 (of_decide_eq_true rfl)
  have h_v740 : R 1 0 4611686018158952441 4611686018695823367 v740 v740 := (r_psel hl h_v696 h_v739 h_v646 (of_decide_eq_true rfl))
  have e_v740 : v740 = if v696 = 1 then v739 else v646 := e_psel h_v696 h_v739 h_v646 (of_decide_eq_true rfl)
  have h_v741 : R 1 0 4611686018427387904 4611686019501129727 v741 v741 := (r1_hxa hb_H0 32 (of_decide_eq_true rfl))
  have e_v741 : sv v741 = ((H0 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 32 (of_decide_eq_true rfl)
  have h_t741_1 : R 1 0 4611686018427387904 4611686018695823363 t741.1 t741.1 := r_sc1 hl h_v741 (of_decide_eq_true rfl)
  have h_t741_2 : R 1 0 4611686018158952445 4611686018695823363 t741.2 t741.2 := r_sc2 hl h_v741 (of_decide_eq_true rfl)
  have e_t741_1 : sv t741.1 = (sc28pS (scArg v741)).1 := e_sc1 h_v741 (of_decide_eq_true rfl)
  have e_t741_2 : sv t741.2 = (sc28pS (scArg v741)).2 := e_sc2 h_v741 (of_decide_eq_true rfl)
  have h_v743 : R 1 0 4611686018158952441 4611686018695823359 v743 v743 := (r_sub hl (r_add hl h_v28 h_t741_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v743 : sv v743 = sv v28 + sv t741.2 := e_add h_v28 h_t741_2 (of_decide_eq_true rfl)
  have h_v744 : R 1 0 0 1 v744 v744 := (r_plt hl h_v743 h_v104 (of_decide_eq_true rfl))
  have e_v744 : (v744 = 1 ↔ sv v743 < sv v104) := e_plt h_v743 h_v104 (of_decide_eq_true rfl)
  have h_v745 : R 1 0 4611686018158952441 4611686018695823359 v745 v745 := (r_psel hl h_v744 h_v104 h_v743 (of_decide_eq_true rfl))
  have e_v745 : v745 = if v744 = 1 then v104 else v743 := e_psel h_v744 h_v104 h_v743 (of_decide_eq_true rfl)
  have h_v746 : R 1 0 4611686018158952449 4611686018695823367 v746 v746 := (r_sub hl (r_add hl h_v31 h_t741_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v746 : sv v746 = sv v31 + sv t741.2 := e_add h_v31 h_t741_2 (of_decide_eq_true rfl)
  have h_v747 : R 1 0 0 1 v747 v747 := (r_plt hl h_v746 h_v33 (of_decide_eq_true rfl))
  have e_v747 : (v747 = 1 ↔ sv v746 < sv v33) := e_plt h_v746 h_v33 (of_decide_eq_true rfl)
  have h_v748 : R 1 0 4611686018158952449 4611686018695823367 v748 v748 := (r_psel hl h_v747 h_v746 h_v33 (of_decide_eq_true rfl))
  clear h_v690 h_v691 h_v739 h_t741_2 h_v743 h_v744
  have e_v748 : v748 = if v747 = 1 then v746 else v33 := e_psel h_v747 h_v746 h_v33 (of_decide_eq_true rfl)
  have h_v750 : R 1 0 4611686018427387908 4611686018695823367 v750 v750 := (r_sub hl (r_add hl h_v31 h_t741_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v750 : sv v750 = sv v31 + sv t741.1 := e_add h_v31 h_t741_1 (of_decide_eq_true rfl)
  have h_v751 : R 1 0 0 1 v751 v751 := (r_plt hl h_v750 h_v33 (of_decide_eq_true rfl))
  have e_v751 : (v751 = 1 ↔ sv v750 < sv v33) := e_plt h_v750 h_v33 (of_decide_eq_true rfl)
  have h_v752 : R 1 0 4611686018427387908 4611686018695823367 v752 v752 := (r_psel hl h_v751 h_v750 h_v33 (of_decide_eq_true rfl))
  have e_v752 : v752 = if v751 = 1 then v750 else v33 := e_psel h_v751 h_v750 h_v33 (of_decide_eq_true rfl)
  have h_v753 : R 1 0 4611686018427387900 4611686018695823359 v753 v753 := (r_sub hl (r_add hl h_v28 h_t741_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v753 : sv v753 = sv v28 + sv t741.1 := e_add h_v28 h_t741_1 (of_decide_eq_true rfl)
  have h_v754 : R 1 0 4611686018158952441 4611686018695823367 v754 v754 := (r_psel hl h_v696 h_v745 h_v748 (of_decide_eq_true rfl))
  have e_v754 : v754 = if v696 = 1 then v745 else v748 := e_psel h_v696 h_v745 h_v748 (of_decide_eq_true rfl)
  have h_v755 : R 1 0 4611686018427387900 4611686018695823367 v755 v755 := (r_psel hl h_v696 h_v752 h_v753 (of_decide_eq_true rfl))
  have e_v755 : v755 = if v696 = 1 then v752 else v753 := e_psel h_v696 h_v752 h_v753 (of_decide_eq_true rfl)
  have h_v756 : R 1 0 4539628418483879831 4683743618370895977 v756 v756 := (r_smx hl 29 h_v697 h_v755 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v756 : sv v756 = sv v697 * sv v755 := e_smx 29 h_v697 h_v755 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v757 : R 1 0 4539628420631363535 4683743616223412273 v757 v757 := (r_smx hl 29 h_v754 h_v740 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v757 : sv v757 = sv v754 * sv v740 := e_smx 29 h_v754 h_v740 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v758 : R 1 0 0 1 v758 v758 := (r_plt hl h_v757 h_v756 (of_decide_eq_true rfl))
  have e_v758 : (v758 = 1 ↔ sv v757 < sv v756) := e_plt h_v757 h_v756 (of_decide_eq_true rfl)
  have h_v759 : R 1 0 0 1 v759 v759 := (r_sub hl (r_O hl) h_v758 (of_decide_eq_true rfl))
  have e_v759 : (v759 = 1 ↔ ¬v758 = 1) := e_not h_v758 (of_decide_eq_true rfl)
  have h_v760 : R 1 0 0 1 v760 v760 := (r_plt hl h_v756 h_v757 (of_decide_eq_true rfl))
  have e_v760 : (v760 = 1 ↔ sv v756 < sv v757) := e_plt h_v756 h_v757 (of_decide_eq_true rfl)
  have h_v761 : R 1 0 0 1 v761 v761 := (r_sub hl (r_O hl) h_v760 (of_decide_eq_true rfl))
  have e_v761 : (v761 = 1 ↔ ¬v760 = 1) := e_not h_v760 (of_decide_eq_true rfl)
  clear h_v697 h_v740 h_t741_1 h_v746 h_v747 h_v748 h_v750 h_v751 h_v752 h_v753 h_v754 h_v755 h_v756 h_v757 h_v758 h_v760
  have h_v762 : R 1 0 0 1 v762 v762 := (r_plt hl h_v9 h_v741 (of_decide_eq_true rfl))
  have e_v762 : (v762 = 1 ↔ sv v9 < sv v741) := e_plt h_v9 h_v741 (of_decide_eq_true rfl)
  have h_v763 : R 1 0 0 1 v763 v763 := (r_sub hl (r_O hl) h_v762 (of_decide_eq_true rfl))
  have e_v763 : (v763 = 1 ↔ ¬v762 = 1) := e_not h_v762 (of_decide_eq_true rfl)
  have h_v764 : R 1 0 0 1 v764 v764 := (r_plt hl h_v215 h_v741 (of_decide_eq_true rfl))
  have e_v764 : (v764 = 1 ↔ sv v215 < sv v741) := e_plt h_v215 h_v741 (of_decide_eq_true rfl)
  have h_v765 : R 1 0 0 1 v765 v765 := (r_sub hl (r_O hl) h_v764 (of_decide_eq_true rfl))
  have e_v765 : (v765 = 1 ↔ ¬v764 = 1) := e_not h_v764 (of_decide_eq_true rfl)
  have h_v766 : R 1 0 0 1 v766 v766 := (r_plt hl h_v18 h_v745 (of_decide_eq_true rfl))
  have e_v766 : (v766 = 1 ↔ sv v18 < sv v745) := e_plt h_v18 h_v745 (of_decide_eq_true rfl)
  have h_v767 : R 1 0 0 1 v767 v767 := (r_land hl h_v759 h_v766 (of_decide_eq_true rfl))
  have e_v767 : (v767 = 1 ↔ v759 = 1 ∧ v766 = 1) := e_land h_v759 h_v766 (of_decide_eq_true rfl)
  have h_v768 : R 1 0 0 1 v768 v768 := (r_land hl h_v765 h_v767 (of_decide_eq_true rfl))
  have e_v768 : (v768 = 1 ↔ v765 = 1 ∧ v767 = 1) := e_land h_v765 h_v767 (of_decide_eq_true rfl)
  have h_v769 : R 1 0 0 1 v769 v769 := (r_lor hl h_v763 h_v768 (of_decide_eq_true rfl))
  have e_v769 : (v769 = 1 ↔ v763 = 1 ∨ v768 = 1) := e_lor h_v763 h_v768 (of_decide_eq_true rfl)
  have h_v770 : R 1 0 0 1 v770 v770 := (r_plt hl h_v741 h_v222 (of_decide_eq_true rfl))
  have e_v770 : (v770 = 1 ↔ sv v741 < sv v222) := e_plt h_v741 h_v222 (of_decide_eq_true rfl)
  have h_v771 : R 1 0 0 1 v771 v771 := (r_sub hl (r_O hl) h_v770 (of_decide_eq_true rfl))
  have e_v771 : (v771 = 1 ↔ ¬v770 = 1) := e_not h_v770 (of_decide_eq_true rfl)
  have h_v772 : R 1 0 0 1 v772 v772 := (r_lor hl h_v761 h_v771 (of_decide_eq_true rfl))
  have e_v772 : (v772 = 1 ↔ v761 = 1 ∨ v771 = 1) := e_lor h_v761 h_v771 (of_decide_eq_true rfl)
  have h_v773 : R 1 0 0 1 v773 v773 := (r_land hl h_v696 h_v769 (of_decide_eq_true rfl))
  have e_v773 : (v773 = 1 ↔ v696 = 1 ∧ v769 = 1) := e_land h_v696 h_v769 (of_decide_eq_true rfl)
  have h_v774 : R 1 0 0 1 v774 v774 := (r_sub hl (r_O hl) h_v696 (of_decide_eq_true rfl))
  clear h_v745 h_v759 h_v761 h_v762 h_v763 h_v764 h_v765 h_v766 h_v767 h_v768 h_v769 h_v770 h_v771
  have e_v774 : (v774 = 1 ↔ ¬v696 = 1) := e_not h_v696 (of_decide_eq_true rfl)
  have h_v775 : R 1 0 0 1 v775 v775 := (r_land hl h_v772 h_v774 (of_decide_eq_true rfl))
  have e_v775 : (v775 = 1 ↔ v772 = 1 ∧ v774 = 1) := e_land h_v772 h_v774 (of_decide_eq_true rfl)
  have h_v776 : R 1 0 0 1 v776 v776 := (r_lor hl h_v773 h_v775 (of_decide_eq_true rfl))
  have e_v776 : (v776 = 1 ↔ v773 = 1 ∨ v775 = 1) := e_lor h_v773 h_v775 (of_decide_eq_true rfl)
  have h_v777 : R 1 0 4611686017353646081 4611686018427387904 v777 v777 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v741 (of_decide_eq_true rfl))
  have e_v777 : sv v777 = sv v9 - sv v741 := e_sub h_v9 h_v741 (of_decide_eq_true rfl)
  have h_v778 : R 1 0 4611686017353646081 4611686019501129727 v778 v778 := (r_psel hl h_v696 h_v777 h_v741 (of_decide_eq_true rfl))
  have e_v778 : v778 = if v696 = 1 then v777 else v741 := e_psel h_v696 h_v777 h_v741 (of_decide_eq_true rfl)
  have h_v779 : R 1 0 4611686017353646081 4611686019501129727 v779 v779 := (r_psel hl h_v776 h_v778 h_v222 (of_decide_eq_true rfl))
  have e_v779 : v779 = if v776 = 1 then v778 else v222 := e_psel h_v776 h_v778 h_v222 (of_decide_eq_true rfl)
  have h_v781 : R 1 0 4611686017353646081 4611686019501129727 v781 v781 := (r_psel hl h_v693 h_v222 h_v779 (of_decide_eq_true rfl))
  have e_v781 : v781 = if v693 = 1 then v222 else v779 := e_psel h_v693 h_v222 h_v779 (of_decide_eq_true rfl)
  have h_v782 : R 1 0 4611686018427387904 4611686052787126264 v782 v782 := (r_add hl (r_pshr1 hl h_v7) h_H61r (of_decide_eq_true rfl))
  have e_v782 : sv v782 = sv v7 / 2 := e_halfF h_v7
  have h_v783 : R 1 0 4611686018427387904 4611686052787126264 v783 v783 := (r_psel hl h_v16 h_v782 h_v215 (of_decide_eq_true rfl))
  have e_v783 : v783 = if v16 = 1 then v782 else v215 := e_psel h_v16 h_v782 h_v215 (of_decide_eq_true rfl)
  have h_v784 : R 1 0 4611686018427387904 4611686052787126264 v784 v784 := (r_add hl (r_pshr1 hl (r_add hl h_v7 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v784 : sv v784 = (sv v7 + 1) / 2 := e_halfC h_v7 (of_decide_eq_true rfl)
  have h_v785 : R 1 0 0 1 v785 v785 := (r_plt hl h_v18 h_v783 (of_decide_eq_true rfl))
  have e_v785 : (v785 = 1 ↔ sv v18 < sv v783) := e_plt h_v18 h_v783 (of_decide_eq_true rfl)
  have h_v786 : R 1 0 0 1 v786 v786 := (r_plt hl h_v20 h_v784 (of_decide_eq_true rfl))
  have e_v786 : (v786 = 1 ↔ sv v20 < sv v784) := e_plt h_v20 h_v784 (of_decide_eq_true rfl)
  have h_v787 : R 1 0 0 1 v787 v787 := (r_sub hl (r_O hl) h_v786 (of_decide_eq_true rfl))
  have e_v787 : (v787 = 1 ↔ ¬v786 = 1) := e_not h_v786 (of_decide_eq_true rfl)
  clear h_H61r h_v7 h_v16 h_v20 h_v215 h_v222 h_v693 h_v696 h_v741 h_v772 h_v773 h_v774 h_v775 h_v776 h_v777 h_v778 h_v779 h_v782 h_v786
  have h_v788 : R 1 0 0 1 v788 v788 := (r_land hl h_v785 h_v787 (of_decide_eq_true rfl))
  have e_v788 : (v788 = 1 ↔ v785 = 1 ∧ v787 = 1) := e_land h_v785 h_v787 (of_decide_eq_true rfl)
  have h_t783_1 : R 1 0 4611686018427387904 4611686018695823363 t783.1 t783.1 := r_sc1 hl h_v783 (of_decide_eq_true rfl)
  have h_t783_2 : R 1 0 4611686018158952445 4611686018695823363 t783.2 t783.2 := r_sc2 hl h_v783 (of_decide_eq_true rfl)
  have e_t783_1 : sv t783.1 = (sc28pS (scArg v783)).1 := e_sc1 h_v783 (of_decide_eq_true rfl)
  have e_t783_2 : sv t783.2 = (sc28pS (scArg v783)).2 := e_sc2 h_v783 (of_decide_eq_true rfl)
  have h_t784_1 : R 1 0 4611686018427387904 4611686018695823363 t784.1 t784.1 := r_sc1 hl h_v784 (of_decide_eq_true rfl)
  have h_t784_2 : R 1 0 4611686018158952445 4611686018695823363 t784.2 t784.2 := r_sc2 hl h_v784 (of_decide_eq_true rfl)
  have e_t784_1 : sv t784.1 = (sc28pS (scArg v784)).1 := e_sc1 h_v784 (of_decide_eq_true rfl)
  have e_t784_2 : sv t784.2 = (sc28pS (scArg v784)).2 := e_sc2 h_v784 (of_decide_eq_true rfl)
  have h_v791 : R 1 0 0 1 v791 v791 := (r_plt hl h_t783_1 h_t784_1 (of_decide_eq_true rfl))
  have e_v791 : (v791 = 1 ↔ sv t783.1 < sv t784.1) := e_plt h_t783_1 h_t784_1 (of_decide_eq_true rfl)
  have h_v792 : R 1 0 4611686018427387904 4611686018695823363 v792 v792 := (r_psel hl h_v791 h_t783_1 h_t784_1 (of_decide_eq_true rfl))
  have e_v792 : v792 = if v791 = 1 then t783.1 else t784.1 := e_psel h_v791 h_t783_1 h_t784_1 (of_decide_eq_true rfl)
  have h_v793 : R 1 0 4611686018427387900 4611686018695823359 v793 v793 := (r_sub hl (r_add hl h_v28 h_v792 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v793 : sv v793 = sv v28 + sv v792 := e_add h_v28 h_v792 (of_decide_eq_true rfl)
  have h_v794 : R 1 0 4611686018427387904 4611686018695823363 v794 v794 := (r_psel hl h_v791 h_t784_1 h_t783_1 (of_decide_eq_true rfl))
  have e_v794 : v794 = if v791 = 1 then t784.1 else t783.1 := e_psel h_v791 h_t784_1 h_t783_1 (of_decide_eq_true rfl)
  have h_v795 : R 1 0 4611686018427387908 4611686018695823367 v795 v795 := (r_sub hl (r_add hl h_v31 h_v794 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v795 : sv v795 = sv v31 + sv v794 := e_add h_v31 h_v794 (of_decide_eq_true rfl)
  have h_v796 : R 1 0 0 1 v796 v796 := (r_plt hl h_v795 h_v33 (of_decide_eq_true rfl))
  have e_v796 : (v796 = 1 ↔ sv v795 < sv v33) := e_plt h_v795 h_v33 (of_decide_eq_true rfl)
  have h_v797 : R 1 0 4611686018427387908 4611686018695823367 v797 v797 := (r_psel hl h_v796 h_v795 h_v33 (of_decide_eq_true rfl))
  have e_v797 : v797 = if v796 = 1 then v795 else v33 := e_psel h_v796 h_v795 h_v33 (of_decide_eq_true rfl)
  have h_v798 : R 1 0 0 1 v798 v798 := (r_plt hl h_v783 h_v36 (of_decide_eq_true rfl))
  clear h_v28 h_v31 h_v785 h_v787 h_t783_1 h_t783_2 e_t783_2 h_t784_1 h_t784_2 e_t784_2 h_v791 h_v792 h_v794 h_v795 h_v796
  have e_v798 : (v798 = 1 ↔ sv v783 < sv v36) := e_plt h_v783 h_v36 (of_decide_eq_true rfl)
  have h_v799 : R 1 0 0 1 v799 v799 := (r_plt hl h_v38 h_v784 (of_decide_eq_true rfl))
  have e_v799 : (v799 = 1 ↔ sv v38 < sv v784) := e_plt h_v38 h_v784 (of_decide_eq_true rfl)
  have h_v800 : R 1 0 0 1 v800 v800 := (r_land hl h_v798 h_v799 (of_decide_eq_true rfl))
  have e_v800 : (v800 = 1 ↔ v798 = 1 ∧ v799 = 1) := e_land h_v798 h_v799 (of_decide_eq_true rfl)
  have h_v801 : R 1 0 4611686018427387908 4611686018695823367 v801 v801 := (r_psel hl h_v800 h_v33 h_v797 (of_decide_eq_true rfl))
  have e_v801 : v801 = if v800 = 1 then v33 else v797 := e_psel h_v800 h_v33 h_v797 (of_decide_eq_true rfl)
  have h_v802 : R 1 0 0 1 v802 v802 := (r_plt hl h_v793 h_v9 (of_decide_eq_true rfl))
  have e_v802 : (v802 = 1 ↔ sv v793 < sv v9) := e_plt h_v793 h_v9 (of_decide_eq_true rfl)
  have h_v804 : R 1 0 0 1 v804 v804 := (r_plt hl h_v9 h_v801 (of_decide_eq_true rfl))
  have e_v804 : (v804 = 1 ↔ sv v9 < sv v801) := e_plt h_v9 h_v801 (of_decide_eq_true rfl)
  have h_v805 : R 1 0 0 1 v805 v805 := (r_sub hl (r_O hl) h_v804 (of_decide_eq_true rfl))
  have e_v805 : (v805 = 1 ↔ ¬v804 = 1) := e_not h_v804 (of_decide_eq_true rfl)
  have h_v806 : R 1 0 0 1 v806 v806 := (r_land hl h_v802 h_v805 (of_decide_eq_true rfl))
  have e_v806 : (v806 = 1 ↔ v802 = 1 ∧ v805 = 1) := e_land h_v802 h_v805 (of_decide_eq_true rfl)
  have h_v807 : R 1 0 0 1 v807 v807 := (r_land hl h_v802 h_v804 (of_decide_eq_true rfl))
  have e_v807 : (v807 = 1 ↔ v802 = 1 ∧ v804 = 1) := e_land h_v802 h_v804 (of_decide_eq_true rfl)
  have h_v808 : R 1 0 0 1 v808 v808 := (r_land hl h_v66 h_v807 (of_decide_eq_true rfl))
  have e_v808 : (v808 = 1 ↔ v66 = 1 ∧ v807 = 1) := e_land h_v66 h_v807 (of_decide_eq_true rfl)
  have h_v809 : R 1 0 0 1 v809 v809 := (r_land hl h_v62 h_v807 (of_decide_eq_true rfl))
  have e_v809 : (v809 = 1 ↔ v62 = 1 ∧ v807 = 1) := e_land h_v62 h_v807 (of_decide_eq_true rfl)
  have h_v810 : R 1 0 0 1 v810 v810 := (r_lor hl h_v806 h_v809 (of_decide_eq_true rfl))
  have e_v810 : (v810 = 1 ↔ v806 = 1 ∨ v809 = 1) := e_lor h_v806 h_v809 (of_decide_eq_true rfl)
  have h_v811 : R 1 0 4611686018427387900 4611686018695823367 v811 v811 := (r_psel hl h_v810 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v811 : v811 = if v810 = 1 then v41 else v29 := e_psel h_v810 h_v41 h_v29 (of_decide_eq_true rfl)
  clear h_v36 h_v38 h_v783 h_v784 h_v797 h_v798 h_v799 h_v800 h_v802 h_v804 h_v805 h_v809 h_v810
  have h_v812 : R 1 0 0 1 v812 v812 := (r_sub hl (r_O hl) h_v806 (of_decide_eq_true rfl))
  have e_v812 : (v812 = 1 ↔ ¬v806 = 1) := e_not h_v806 (of_decide_eq_true rfl)
  have h_v813 : R 1 0 0 1 v813 v813 := (r_land hl h_v66 h_v812 (of_decide_eq_true rfl))
  have e_v813 : (v813 = 1 ↔ v66 = 1 ∧ v812 = 1) := e_land h_v66 h_v812 (of_decide_eq_true rfl)
  have h_v814 : R 1 0 0 1 v814 v814 := (r_lor hl h_v65 h_v813 (of_decide_eq_true rfl))
  have e_v814 : (v814 = 1 ↔ v65 = 1 ∨ v813 = 1) := e_lor h_v65 h_v813 (of_decide_eq_true rfl)
  have h_v815 : R 1 0 4611686018427387900 4611686018695823367 v815 v815 := (r_psel hl h_v814 h_v801 h_v793 (of_decide_eq_true rfl))
  have e_v815 : v815 = if v814 = 1 then v801 else v793 := e_psel h_v814 h_v801 h_v793 (of_decide_eq_true rfl)
  have h_v816 : R 1 0 0 1 v816 v816 := (r_land hl h_v65 h_v807 (of_decide_eq_true rfl))
  have e_v816 : (v816 = 1 ↔ v65 = 1 ∧ v807 = 1) := e_land h_v65 h_v807 (of_decide_eq_true rfl)
  have h_v817 : R 1 0 0 1 v817 v817 := (r_lor hl h_v806 h_v816 (of_decide_eq_true rfl))
  have e_v817 : (v817 = 1 ↔ v806 = 1 ∨ v816 = 1) := e_lor h_v806 h_v816 (of_decide_eq_true rfl)
  have h_v818 : R 1 0 4611686018427387900 4611686018695823367 v818 v818 := (r_psel hl h_v817 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v818 : v818 = if v817 = 1 then v29 else v41 := e_psel h_v817 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v819 : R 1 0 0 1 v819 v819 := (r_land hl h_v66 h_v806 (of_decide_eq_true rfl))
  have e_v819 : (v819 = 1 ↔ v66 = 1 ∧ v806 = 1) := e_land h_v66 h_v806 (of_decide_eq_true rfl)
  have h_v820 : R 1 0 0 1 v820 v820 := (r_lor hl h_v65 h_v819 (of_decide_eq_true rfl))
  have e_v820 : (v820 = 1 ↔ v65 = 1 ∨ v819 = 1) := e_lor h_v65 h_v819 (of_decide_eq_true rfl)
  have h_v821 : R 1 0 4611686018427387900 4611686018695823367 v821 v821 := (r_psel hl h_v820 h_v793 h_v801 (of_decide_eq_true rfl))
  have e_v821 : v821 = if v820 = 1 then v793 else v801 := e_psel h_v820 h_v793 h_v801 (of_decide_eq_true rfl)
  have h_v822 : R 1 0 4611686017353646052 4683743616223412273 v822 v822 := (r_smx hl 29 h_v815 h_v811 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v822 : sv v822 = sv v815 * sv v811 := e_smx 29 h_v815 h_v811 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v823 : R 1 0 4611686018427387899 4611686018695823374 v823 v823 := (r_srdF hl h_v822 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v823 : sv v823 = sv v822 / 2 ^ 28 := e_srdF h_v822 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v824 : R 1 0 4611686017353646052 4683743616223412273 v824 v824 := (r_smx hl 29 h_v821 h_v818 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  clear h_v801 h_v806 h_v807 h_v811 h_v812 h_v813 h_v814 h_v815 h_v816 h_v817 h_v819 h_v820 h_v822
  have e_v824 : sv v824 = sv v821 * sv v818 := e_smx 29 h_v821 h_v818 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v825 : R 1 0 4611686018427387900 4611686018695823375 v825 v825 := (r_srdC hl h_v824 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v825 : sv v825 = -((-sv v824) / 2 ^ 28) := e_srdC h_v824 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v826 : R 1 0 4611686017353646052 4683743614075928569 v826 v826 := (r_smx hl 29 h_v793 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl))
  have e_v826 : sv v826 = sv v793 * sv v41 := e_smx 29 h_v793 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl)
  have h_v827 : R 1 0 4611686018427387899 4611686018695823365 v827 v827 := (r_srdF hl h_v826 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl))
  have e_v827 : sv v827 = sv v826 / 2 ^ 28 := e_srdF h_v826 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl)
  have h_v828 : R 1 0 4611686017353646084 4683743611928444929 v828 v828 := (r_smx hl 29 h_v793 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl))
  have e_v828 : sv v828 = sv v793 * sv v29 := e_smx 29 h_v793 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl)
  have h_v829 : R 1 0 4611686018427387901 4611686018695823359 v829 v829 := (r_srdC hl h_v828 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl))
  have e_v829 : sv v829 = -((-sv v828) / 2 ^ 28) := e_srdC h_v828 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl)
  have h_v830 : R 1 0 0 1 v830 v830 := (r_plt hl h_v823 h_v827 (of_decide_eq_true rfl))
  have e_v830 : (v830 = 1 ↔ sv v823 < sv v827) := e_plt h_v823 h_v827 (of_decide_eq_true rfl)
  have h_v831 : R 1 0 4611686018427387899 4611686018695823374 v831 v831 := (r_psel hl h_v830 h_v823 h_v827 (of_decide_eq_true rfl))
  have e_v831 : v831 = if v830 = 1 then v823 else v827 := e_psel h_v830 h_v823 h_v827 (of_decide_eq_true rfl)
  have h_v832 : R 1 0 0 1 v832 v832 := (r_plt hl h_v825 h_v829 (of_decide_eq_true rfl))
  have e_v832 : (v832 = 1 ↔ sv v825 < sv v829) := e_plt h_v825 h_v829 (of_decide_eq_true rfl)
  have h_v833 : R 1 0 4611686018427387900 4611686018695823375 v833 v833 := (r_psel hl h_v832 h_v829 h_v825 (of_decide_eq_true rfl))
  have e_v833 : v833 = if v832 = 1 then v829 else v825 := e_psel h_v832 h_v829 h_v825 (of_decide_eq_true rfl)
  have h_v834 : R 1 0 4611686018427387899 4611686018695823374 v834 v834 := (r_psel hl h_v808 h_v831 h_v823 (of_decide_eq_true rfl))
  have e_v834 : v834 = if v808 = 1 then v831 else v823 := e_psel h_v808 h_v831 h_v823 (of_decide_eq_true rfl)
  have h_v835 : R 1 0 4611686018427387900 4611686018695823375 v835 v835 := (r_psel hl h_v808 h_v833 h_v825 (of_decide_eq_true rfl))
  have e_v835 : v835 = if v808 = 1 then v833 else v825 := e_psel h_v808 h_v833 h_v825 (of_decide_eq_true rfl)
  have h_v836 : R 1 0 0 1 v836 v836 := (r_plt hl h_v18 h_v834 (of_decide_eq_true rfl))
  have e_v836 : (v836 = 1 ↔ sv v18 < sv v834) := e_plt h_v18 h_v834 (of_decide_eq_true rfl)
  clear h_v18 h_v793 h_v808 h_v818 h_v821 h_v823 h_v824 h_v825 h_v826 h_v827 h_v828 h_v829 h_v830 h_v831 h_v832 h_v833
  have h_v837 : R 1 0 0 1 v837 v837 := (r_plt hl h_v9 h_v478 (of_decide_eq_true rfl))
  have e_v837 : (v837 = 1 ↔ sv v9 < sv v478) := e_plt h_v9 h_v478 (of_decide_eq_true rfl)
  have h_v838 : R 1 0 0 1 v838 v838 := (r_plt hl h_v479 h_v33 (of_decide_eq_true rfl))
  have e_v838 : (v838 = 1 ↔ sv v479 < sv v33) := e_plt h_v479 h_v33 (of_decide_eq_true rfl)
  have h_v839 : R 1 0 0 1 v839 v839 := (r_land hl h_v837 h_v838 (of_decide_eq_true rfl))
  have e_v839 : (v839 = 1 ↔ v837 = 1 ∧ v838 = 1) := e_land h_v837 h_v838 (of_decide_eq_true rfl)
  have h_v840 : R 1 0 0 1 v840 v840 := (r_plt hl h_v9 h_v99 (of_decide_eq_true rfl))
  have e_v840 : (v840 = 1 ↔ sv v9 < sv v99) := e_plt h_v9 h_v99 (of_decide_eq_true rfl)
  have h_v841 : R 1 0 0 1 v841 v841 := (r_plt hl h_v100 h_v33 (of_decide_eq_true rfl))
  have e_v841 : (v841 = 1 ↔ sv v100 < sv v33) := e_plt h_v100 h_v33 (of_decide_eq_true rfl)
  have h_v842 : R 1 0 0 1 v842 v842 := (r_land hl h_v840 h_v841 (of_decide_eq_true rfl))
  have e_v842 : (v842 = 1 ↔ v840 = 1 ∧ v841 = 1) := e_land h_v840 h_v841 (of_decide_eq_true rfl)
  have h_v843 : R 1 0 0 1 v843 v843 := (r_plt hl h_v9 h_v834 (of_decide_eq_true rfl))
  have e_v843 : (v843 = 1 ↔ sv v9 < sv v834) := e_plt h_v9 h_v834 (of_decide_eq_true rfl)
  have h_v844 : R 1 0 0 1 v844 v844 := (r_plt hl h_v835 h_v33 (of_decide_eq_true rfl))
  have e_v844 : (v844 = 1 ↔ sv v835 < sv v33) := e_plt h_v835 h_v33 (of_decide_eq_true rfl)
  have h_v845 : R 1 0 0 1 v845 v845 := (r_land hl h_v843 h_v844 (of_decide_eq_true rfl))
  have e_v845 : (v845 = 1 ↔ v843 = 1 ∧ v844 = 1) := e_land h_v843 h_v844 (of_decide_eq_true rfl)
  have h_v846 : R 1 0 0 1 v846 v846 := (r_land hl h_v839 h_v842 (of_decide_eq_true rfl))
  have e_v846 : (v846 = 1 ↔ v839 = 1 ∧ v842 = 1) := e_land h_v839 h_v842 (of_decide_eq_true rfl)
  have h_v847 : R 1 0 0 1 v847 v847 := (r_land hl h_v845 h_v846 (of_decide_eq_true rfl))
  have e_v847 : (v847 = 1 ↔ v845 = 1 ∧ v846 = 1) := e_land h_v845 h_v846 (of_decide_eq_true rfl)
  have h_v848 : R 1 0 4611686018427387904 4683743620518379745 v848 v848 := (r_smx_sq hl 29 h_v479 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v848 : sv v848 = sv v479 * sv v479 := e_smx_sq 29 h_v479 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v849 : R 1 0 4611686018427387904 4611686018695823391 v849 v849 := (r_srdC hl h_v848 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  clear h_v837 h_v838 h_v839 h_v840 h_v841 h_v842 h_v843 h_v844 h_v846
  have e_v849 : sv v849 = -((-sv v848) / 2 ^ 28) := e_srdC h_v848 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v850 : R 1 0 4611686018427387904 4611686018964258878 v850 v850 := (r_sub hl (r_add hl h_v849 h_v849 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v850 : sv v850 = sv v849 + sv v849 := e_add h_v849 h_v849 (of_decide_eq_true rfl)
  have h_v851 : R 1 0 4611686018158952386 4611686018695823360 v851 v851 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v850 (of_decide_eq_true rfl))
  have e_v851 : sv v851 = sv v33 - sv v850 := e_sub h_v33 h_v850 (of_decide_eq_true rfl)
  have h_v852 : R 1 0 0 1 v852 v852 := (r_plt hl h_v851 h_v104 (of_decide_eq_true rfl))
  have e_v852 : (v852 = 1 ↔ sv v851 < sv v104) := e_plt h_v851 h_v104 (of_decide_eq_true rfl)
  have h_v853 : R 1 0 4611686018158952386 4611686018695823360 v853 v853 := (r_psel hl h_v852 h_v104 h_v851 (of_decide_eq_true rfl))
  have e_v853 : v853 = if v852 = 1 then v104 else v851 := e_psel h_v852 h_v104 h_v851 (of_decide_eq_true rfl)
  have h_v854 : R 1 0 4611686018427387904 4683743619981508804 v854 v854 := (r_smx_sq hl 29 h_v478 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v854 : sv v854 = sv v478 * sv v478 := e_smx_sq 29 h_v478 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v855 : R 1 0 4611686018427387904 4611686018695823388 v855 v855 := (r_srdF hl h_v854 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v855 : sv v855 = sv v854 / 2 ^ 28 := e_srdF h_v854 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v856 : R 1 0 4611686018427387904 4611686018964258872 v856 v856 := (r_sub hl (r_add hl h_v855 h_v855 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v856 : sv v856 = sv v855 + sv v855 := e_add h_v855 h_v855 (of_decide_eq_true rfl)
  have h_v857 : R 1 0 4611686018158952392 4611686018695823360 v857 v857 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v856 (of_decide_eq_true rfl))
  have e_v857 : sv v857 = sv v33 - sv v856 := e_sub h_v33 h_v856 (of_decide_eq_true rfl)
  have h_v858 : R 1 0 4611686018427387904 4683743620518379745 v858 v858 := (r_smx_sq hl 29 h_v835 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v858 : sv v858 = sv v835 * sv v835 := e_smx_sq 29 h_v835 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v859 : R 1 0 4611686018427387904 4611686018695823391 v859 v859 := (r_srdC hl h_v858 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v859 : sv v859 = -((-sv v858) / 2 ^ 28) := e_srdC h_v858 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v860 : R 1 0 4611686018427387904 4611686018964258878 v860 v860 := (r_sub hl (r_add hl h_v859 h_v859 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v860 : sv v860 = sv v859 + sv v859 := e_add h_v859 h_v859 (of_decide_eq_true rfl)
  have h_v861 : R 1 0 4611686018158952386 4611686018695823360 v861 v861 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v860 (of_decide_eq_true rfl))
  have e_v861 : sv v861 = sv v33 - sv v860 := e_sub h_v33 h_v860 (of_decide_eq_true rfl)
  clear h_v848 h_v849 h_v850 h_v851 h_v852 h_v854 h_v855 h_v856 h_v858 h_v859 h_v860
  have h_v862 : R 1 0 0 1 v862 v862 := (r_plt hl h_v861 h_v104 (of_decide_eq_true rfl))
  have e_v862 : (v862 = 1 ↔ sv v861 < sv v104) := e_plt h_v861 h_v104 (of_decide_eq_true rfl)
  have h_v863 : R 1 0 4611686018158952386 4611686018695823360 v863 v863 := (r_psel hl h_v862 h_v104 h_v861 (of_decide_eq_true rfl))
  have e_v863 : v863 = if v862 = 1 then v104 else v861 := e_psel h_v862 h_v104 h_v861 (of_decide_eq_true rfl)
  have h_v864 : R 1 0 4611686018427387904 4683743619981508804 v864 v864 := (r_smx_sq hl 29 h_v834 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v864 : sv v864 = sv v834 * sv v834 := e_smx_sq 29 h_v834 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v865 : R 1 0 4611686018427387904 4611686018695823388 v865 v865 := (r_srdF hl h_v864 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v865 : sv v865 = sv v864 / 2 ^ 28 := e_srdF h_v864 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v866 : R 1 0 4611686018427387904 4611686018964258872 v866 v866 := (r_sub hl (r_add hl h_v865 h_v865 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v866 : sv v866 = sv v865 + sv v865 := e_add h_v865 h_v865 (of_decide_eq_true rfl)
  have h_v867 : R 1 0 4611686018158952392 4611686018695823360 v867 v867 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v866 (of_decide_eq_true rfl))
  have e_v867 : sv v867 = sv v33 - sv v866 := e_sub h_v33 h_v866 (of_decide_eq_true rfl)
  have h_v868 : R 1 0 4611686018427387904 4683743620518379745 v868 v868 := (r_smx_sq hl 29 h_v100 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v868 : sv v868 = sv v100 * sv v100 := e_smx_sq 29 h_v100 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v869 : R 1 0 4611686018427387904 4611686018695823391 v869 v869 := (r_srdC hl h_v868 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v869 : sv v869 = -((-sv v868) / 2 ^ 28) := e_srdC h_v868 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v870 : R 1 0 4611686018427387904 4611686018964258878 v870 v870 := (r_sub hl (r_add hl h_v869 h_v869 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v870 : sv v870 = sv v869 + sv v869 := e_add h_v869 h_v869 (of_decide_eq_true rfl)
  have h_v871 : R 1 0 4611686018158952386 4611686018695823360 v871 v871 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v870 (of_decide_eq_true rfl))
  have e_v871 : sv v871 = sv v33 - sv v870 := e_sub h_v33 h_v870 (of_decide_eq_true rfl)
  have h_v872 : R 1 0 0 1 v872 v872 := (r_plt hl h_v871 h_v104 (of_decide_eq_true rfl))
  have e_v872 : (v872 = 1 ↔ sv v871 < sv v104) := e_plt h_v871 h_v104 (of_decide_eq_true rfl)
  have h_v873 : R 1 0 4611686018158952386 4611686018695823360 v873 v873 := (r_psel hl h_v872 h_v104 h_v871 (of_decide_eq_true rfl))
  have e_v873 : v873 = if v872 = 1 then v104 else v871 := e_psel h_v872 h_v104 h_v871 (of_decide_eq_true rfl)
  have h_v874 : R 1 0 4611686018427387904 4683743619981508804 v874 v874 := (r_smx_sq hl 29 h_v99 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  clear h_v104 h_v861 h_v862 h_v864 h_v865 h_v866 h_v868 h_v869 h_v870 h_v871 h_v872
  have e_v874 : sv v874 = sv v99 * sv v99 := e_smx_sq 29 h_v99 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v875 : R 1 0 4611686018427387904 4611686018695823388 v875 v875 := (r_srdF hl h_v874 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v875 : sv v875 = sv v874 / 2 ^ 28 := e_srdF h_v874 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v876 : R 1 0 4611686018427387904 4611686018964258872 v876 v876 := (r_sub hl (r_add hl h_v875 h_v875 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v876 : sv v876 = sv v875 + sv v875 := e_add h_v875 h_v875 (of_decide_eq_true rfl)
  have h_v877 : R 1 0 4611686018158952392 4611686018695823360 v877 v877 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v876 (of_decide_eq_true rfl))
  have e_v877 : sv v877 = sv v33 - sv v876 := e_sub h_v33 h_v876 (of_decide_eq_true rfl)
  have h_v878 : R 1 0 0 1 v878 v878 := (r_plt hl h_v853 h_v9 (of_decide_eq_true rfl))
  have e_v878 : (v878 = 1 ↔ sv v853 < sv v9) := e_plt h_v853 h_v9 (of_decide_eq_true rfl)
  have h_v879 : R 1 0 0 1 v879 v879 := (r_sub hl (r_O hl) h_v878 (of_decide_eq_true rfl))
  have e_v879 : (v879 = 1 ↔ ¬v878 = 1) := e_not h_v878 (of_decide_eq_true rfl)
  have h_v880 : R 1 0 0 1 v880 v880 := (r_plt hl h_v9 h_v857 (of_decide_eq_true rfl))
  have e_v880 : (v880 = 1 ↔ sv v9 < sv v857) := e_plt h_v9 h_v857 (of_decide_eq_true rfl)
  have h_v881 : R 1 0 0 1 v881 v881 := (r_sub hl (r_O hl) h_v880 (of_decide_eq_true rfl))
  have e_v881 : (v881 = 1 ↔ ¬v880 = 1) := e_not h_v880 (of_decide_eq_true rfl)
  have h_v882 : R 1 0 0 1 v882 v882 := (r_land hl h_v878 h_v881 (of_decide_eq_true rfl))
  have e_v882 : (v882 = 1 ↔ v878 = 1 ∧ v881 = 1) := e_land h_v878 h_v881 (of_decide_eq_true rfl)
  have h_v883 : R 1 0 0 1 v883 v883 := (r_land hl h_v878 h_v880 (of_decide_eq_true rfl))
  have e_v883 : (v883 = 1 ↔ v878 = 1 ∧ v880 = 1) := e_land h_v878 h_v880 (of_decide_eq_true rfl)
  have h_v884 : R 1 0 0 1 v884 v884 := (r_plt hl h_v873 h_v9 (of_decide_eq_true rfl))
  have e_v884 : (v884 = 1 ↔ sv v873 < sv v9) := e_plt h_v873 h_v9 (of_decide_eq_true rfl)
  have h_v885 : R 1 0 0 1 v885 v885 := (r_sub hl (r_O hl) h_v884 (of_decide_eq_true rfl))
  have e_v885 : (v885 = 1 ↔ ¬v884 = 1) := e_not h_v884 (of_decide_eq_true rfl)
  have h_v886 : R 1 0 0 1 v886 v886 := (r_plt hl h_v9 h_v877 (of_decide_eq_true rfl))
  have e_v886 : (v886 = 1 ↔ sv v9 < sv v877) := e_plt h_v9 h_v877 (of_decide_eq_true rfl)
  clear h_OFFr h_v9 h_v33 h_v874 h_v875 h_v876 h_v878 h_v880 h_v881
  have h_v887 : R 1 0 0 1 v887 v887 := (r_sub hl (r_O hl) h_v886 (of_decide_eq_true rfl))
  have e_v887 : (v887 = 1 ↔ ¬v886 = 1) := e_not h_v886 (of_decide_eq_true rfl)
  have h_v888 : R 1 0 0 1 v888 v888 := (r_land hl h_v884 h_v887 (of_decide_eq_true rfl))
  have e_v888 : (v888 = 1 ↔ v884 = 1 ∧ v887 = 1) := e_land h_v884 h_v887 (of_decide_eq_true rfl)
  have h_v889 : R 1 0 0 1 v889 v889 := (r_land hl h_v884 h_v886 (of_decide_eq_true rfl))
  have e_v889 : (v889 = 1 ↔ v884 = 1 ∧ v886 = 1) := e_land h_v884 h_v886 (of_decide_eq_true rfl)
  have h_v890 : R 1 0 0 1 v890 v890 := (r_land hl h_v883 h_v889 (of_decide_eq_true rfl))
  have e_v890 : (v890 = 1 ↔ v883 = 1 ∧ v889 = 1) := e_land h_v883 h_v889 (of_decide_eq_true rfl)
  have h_v891 : R 1 0 0 1 v891 v891 := (r_land hl h_v879 h_v889 (of_decide_eq_true rfl))
  have e_v891 : (v891 = 1 ↔ v879 = 1 ∧ v889 = 1) := e_land h_v879 h_v889 (of_decide_eq_true rfl)
  have h_v892 : R 1 0 0 1 v892 v892 := (r_lor hl h_v888 h_v891 (of_decide_eq_true rfl))
  have e_v892 : (v892 = 1 ↔ v888 = 1 ∨ v891 = 1) := e_lor h_v888 h_v891 (of_decide_eq_true rfl)
  have h_v893 : R 1 0 4611686018158952386 4611686018695823360 v893 v893 := (r_psel hl h_v892 h_v857 h_v853 (of_decide_eq_true rfl))
  have e_v893 : v893 = if v892 = 1 then v857 else v853 := e_psel h_v892 h_v857 h_v853 (of_decide_eq_true rfl)
  have h_v894 : R 1 0 0 1 v894 v894 := (r_sub hl (r_O hl) h_v888 (of_decide_eq_true rfl))
  have e_v894 : (v894 = 1 ↔ ¬v888 = 1) := e_not h_v888 (of_decide_eq_true rfl)
  have h_v895 : R 1 0 0 1 v895 v895 := (r_land hl h_v883 h_v894 (of_decide_eq_true rfl))
  have e_v895 : (v895 = 1 ↔ v883 = 1 ∧ v894 = 1) := e_land h_v883 h_v894 (of_decide_eq_true rfl)
  have h_v896 : R 1 0 0 1 v896 v896 := (r_lor hl h_v882 h_v895 (of_decide_eq_true rfl))
  have e_v896 : (v896 = 1 ↔ v882 = 1 ∨ v895 = 1) := e_lor h_v882 h_v895 (of_decide_eq_true rfl)
  exact fun _ k => k e_v0 e_v1 e_v2 e_v3 e_v4 e_v5 e_v6 e_v7 e_v9 e_v10 e_v14 e_v15 e_v16 e_v18 e_v19 e_v20 e_v21 e_v22 h_v23 e_v23 e_t0_1 e_t0_2 e_t1_1 e_t1_2 e_v26 e_v27 e_v28 h_v29 e_v29 e_v30 e_v31 e_v32 e_v33 e_v34 e_v35 e_v36 e_v37 e_v38 e_v39 e_v40 h_v41 e_v41 h_v42 e_v42 h_v43 e_v43 h_v44 e_v44 e_v45 e_v46 h_v47 e_v47 h_t42_1 e_t42_1 e_t42_2 h_t43_1 e_t43_1 e_t43_2 e_v50 e_v51 h_v52 e_v52 e_v53 e_v54 e_v55 e_v56 h_v57 e_v57 e_v58 e_v59 h_v60 e_v60 e_v61 h_v62 e_v62 e_v63 e_v64 h_v65 e_v65 h_v66 e_v66 e_v67 e_v69 e_v70 h_v71 e_v71 h_v72 e_v72 e_v73 e_v74 e_v75 e_v76 h_v77 e_v77 e_v78 e_v79 e_v80 e_v81 e_v82 e_v83 e_v84 e_v85 e_v86 e_v87 e_v88 e_v89 e_v90 e_v91 e_v92 e_v93 e_v94 e_v95 e_v96 e_v97 e_v98 h_v99 e_v99 h_v100 e_v100 h_v101 e_v101 e_v103 e_v104 e_v105 e_v106 e_v107 e_v108 h_v109 e_v109 e_v111 e_v112 e_v113 e_v114 e_v115 h_v116 e_v116 h_v117 e_v117 e_v118 h_v119 e_v119 e_v121 e_v122 e_v123 e_v124 h_v125 e_v125 e_v143 h_v144 e_v144 e_v145 e_v146 h_v147 e_v147 h_v148 e_v148 h_v185 e_v185 e_v215 e_v222 h_v276 e_v276 e_v277 e_v278 h_v279 e_v279 e_v287 e_v288 e_v289 e_v290 h_v291 e_v291 h_t276_1 e_t276_1 e_v293 e_v294 e_v295 e_v296 e_v297 e_v298 e_v299 e_v300 e_v301 e_v302 e_v303 e_v305 e_v306 e_v307 e_v308 e_v309 e_v310 e_v311 e_v312 e_v313 e_v314 e_v315 e_v316 e_v317 e_v318 e_v319 e_v320 e_v321 e_v322 e_v323 e_v324 e_v325 e_v326 e_v327 e_v328 e_v329 e_v330 e_v331 e_v332 e_v333 e_v334 e_v335 e_v336 e_v337 e_v338 e_v341 e_v342 e_v384 e_v385 e_v386 e_t386_1 e_t386_2 e_v388 e_v389 e_v390 e_v391 e_v392 e_v393 e_v395 e_v396 e_v397 e_v398 e_v399 e_v400 e_v401 e_v402 e_v403 e_v404 e_v405 e_v406 e_v407 e_v408 e_v409 e_v410 e_v411 e_v412 e_v413 e_v414 e_v415 e_v416 e_v417 e_v418 e_v419 e_v420 e_v421 e_v422 e_v423 e_v424 h_v426 e_v426 h_v427 e_v427 h_v428 e_v428 h_v429 e_v429 e_v430 e_v431 h_v432 e_v432 h_t427_1 e_t427_1 e_t427_2 h_t428_1 e_t428_1 e_t428_2 e_v435 e_v436 h_v437 e_v437 e_v438 e_v439 e_v440 e_v441 h_v442 e_v442 e_v443 e_v444 h_v445 e_v445 e_v446 e_v448 e_v449 h_v450 e_v450 h_v451 e_v451 e_v452 e_v453 e_v454 e_v455 h_v456 e_v456 e_v457 e_v458 e_v459 e_v460 e_v461 e_v462 e_v463 e_v464 e_v465 e_v466 e_v467 e_v468 e_v469 e_v470 e_v471 e_v472 e_v473 e_v474 e_v475 e_v476 e_v477 h_v478 e_v478 h_v479 e_v479 h_v480 e_v480 h_v481 e_v481 e_v482 h_v483 e_v483 e_v485 e_v486 e_v487 e_v488 h_v489 e_v489 h_v543 e_v543 h_v631 e_v631 e_v632 e_v633 h_v634 e_v634 e_v642 e_v643 e_v644 e_v645 h_v646 e_v646 h_t631_1 e_t631_1 e_v648 e_v649 e_v650 e_v651 e_v652 e_v653 e_v654 e_v655 e_v656 e_v657 e_v658 e_v660 e_v661 e_v662 e_v663 e_v664 e_v665 e_v666 e_v667 e_v668 e_v669 e_v670 e_v671 e_v672 e_v673 e_v674 e_v675 e_v676 e_v677 e_v678 e_v679 e_v680 e_v681 e_v682 e_v683 e_v684 e_v685 e_v686 e_v687 e_v688 e_v689 e_v690 e_v691 e_v692 e_v693 e_v696 e_v697 e_v739 e_v740 e_v741 e_t741_1 e_t741_2 e_v743 e_v744 e_v745 e_v746 e_v747 e_v748 e_v750 e_v751 e_v752 e_v753 e_v754 e_v755 e_v756 e_v757 e_v758 e_v759 e_v760 e_v761 e_v762 e_v763 e_v764 e_v765 e_v766 e_v767 e_v768 e_v769 e_v770 e_v771 e_v772 e_v773 e_v774 e_v775 e_v776 e_v777 e_v778 e_v779 h_v781 e_v781 e_v782 e_v783 e_v784 e_v785 e_v786 e_v787 h_v788 e_v788 e_t783_1 e_t784_1 e_v791 e_v792 e_v793 e_v794 e_v795 e_v796 e_v797 e_v798 e_v799 e_v800 e_v801 e_v802 e_v804 e_v805 e_v806 e_v807 e_v808 e_v809 e_v810 e_v811 e_v812 e_v813 e_v814 e_v815 e_v816 e_v817 e_v818 e_v819 e_v820 e_v821 e_v822 e_v823 e_v824 e_v825 e_v826 e_v827 e_v828 e_v829 e_v830 e_v831 e_v832 e_v833 h_v834 e_v834 h_v835 e_v835 h_v836 e_v836 e_v837 e_v838 e_v839 e_v840 e_v841 e_v842 e_v843 e_v844 h_v845 e_v845 e_v846 h_v847 e_v847 e_v848 e_v849 e_v850 e_v851 e_v852 h_v853 e_v853 e_v854 e_v855 e_v856 h_v857 e_v857 e_v858 e_v859 e_v860 e_v861 e_v862 h_v863 e_v863 e_v864 e_v865 e_v866 h_v867 e_v867 e_v868 e_v869 e_v870 e_v871 e_v872 h_v873 e_v873 e_v874 e_v875 e_v876 h_v877 e_v877 e_v878 h_v879 e_v879 e_v880 e_v881 h_v882 e_v882 h_v883 e_v883 e_v884 h_v885 e_v885 e_v886 e_v887 h_v888 e_v888 h_v889 e_v889 h_v890 e_v890 e_v891 e_v892 h_v893 e_v893 e_v894 e_v895 h_v896 e_v896

end Tammes15.D3Trig
