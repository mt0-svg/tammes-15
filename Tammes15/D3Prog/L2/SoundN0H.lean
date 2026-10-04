import Tammes15.D3Ck2.Prog.N0H
import Tammes15.D3Prog.L2.Kinds
import Tammes15.D3Prog.L2.PLib

namespace D3Prog

open D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem progN0H_l2 (F0 F1 F2 F3 H0 H1 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (h : D3Ck2.progN0H 1 F0 F1 F2 F3 H0 H1 = 1) (hD : L2.InDom F0 F1 F2 F3) : L2.LaneClaim 0 true F0 F1 F2 F3 := by
  unfold D3Ck2.progN0H at h
  extract_lets -merge OFFr H61r v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 v12 v13 t0 t1 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 t32 t33 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v84 v85 v86 v87 v88 v89 v90 v92 v93 v94 v95 v96 v97 v98 v99 v100 t98 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v132 v135 v136 v137 v186 v193 v247 v248 v249 v250 v258 v259 v260 v261 v262 t247 v264 v265 v266 v267 v268 v269 v270 v271 v272 v273 v274 v275 v276 v277 v278 v279 v280 v281 v282 v283 v284 v285 v286 v287 v288 v289 v290 v291 v292 v293 v294 v295 v296 v297 v298 v299 v302 v303 v345 v346 v347 t347 v349 v350 v351 v352 v353 v354 v356 v357 v358 v359 v360 v361 v362 v363 v364 v365 v366 v367 v368 v369 v370 v371 v372 v373 v374 v375 v376 v377 v378 v379 v380 v381 v382 v383 v384 v385 v387 v388 v389 v390 v391 v392 v393 t388 t389 v396 v397 v398 v399 v400 v401 v402 v403 v404 v405 v406 v407 v408 v409 v410 v411 v412 v413 v414 v415 v416 v417 v418 v419 v420 v421 v422 v423 v424 v425 v426 v427 v428 v429 v430 v431 v432 v433 v434 t432 v448 v449 v450 v451 v452 v453 v454 v455 v456 v457 v458 v460 v463 v464 v465 v572 v573 v574 v575 v583 v584 v585 v586 v587 t572 v589 v590 v591 v592 v593 v594 v595 v596 v597 v598 v599 v600 v601 v602 v603 v604 v605 v606 v607 v608 v609 v610 v611 v612 v613 v614 v615 v616 v617 v618 v619 v620 v621 v622 v623 v624 v627 v628 v670 v671 v672 t672 v674 v675 v676 v677 v678 v679 v681 v682 v683 v684 v685 v686 v687 v688 v689 v690 v691 v692 v693 v694 v695 v696 v697 v698 v699 v700 v701 v702 v703 v704 v705 v706 v707 v708 v709 v710 v712 v713 v714 v715 v716 v717 v718 v719 v720 v721 v722 v723 v724 v725 v726 v727 v728 v729 v730 v731 v732 v733 v734 v735 v736 v737 v738 v739 v740 v741 v742 v743 v744 v745 v746 v747 v748 v749 v750 v751 v752 v753 v754 v755 v756 v757 v758 v759 v760 v761 v762 v763 v764 v765 v766 v767 v768 v769 v770 v771 v772 v773 v774 v775 v776 v777 v778 v779 v780 v781 v782 v783 v784 v785 v786 v787 v788 v789 v790 v791 v792 v793 v794 v795 v796 v797 v798 v799 v800 v801 v802 v803 v804 v805 v806 v807 v808 v809 v810 v811 v812 v813 v814 v815 v816 v822 v823 v824 v825 v826 v827 v828 v829 v830 v831 v832 v833 v834 v835 v836 v837 v838 v839 v840 v841 v842 v843 v844 v845 v846 v847 v848 v849 v850 v851 v852 v853 v854 v855 v856 v857 v858 v859 v860 v861 v862 v869 v870 v874 v875 v876 v877 v878 v879 v880 v881 v882 v883 v884 v885 v886 v887 v888 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 v918 v919 v920 v921 v922 v923 v924 v925 v926 v927 v928 v929 v930 v931 v932 v933 v934 v935 v936 v937 v938 v939 v940 v941 v942 v943 v944 v945 v946 v947 v948 v949 v950 v951 v952 v953 v954 v955 v956 v957 v958 v959 v960 v961 v962 v963 v964 v965 v966 v967 v968 v969 v970 v971 v972 v976 v977 v978 v979 v980 v986 v987 v988 v994 v995 v996 v997 v998 v999 v1000 v1001 v1002 v1003 v1004 v1005 v1006 v1007 v1008 v1009 v1010 v1011 v1012 v1013 v1014 v1016 v1017 v1018 v1019 v1020 v1022 v1023 v1024 v1025 v1026 v1027 v1028 v1035 v1036 v1037 v1038 v1039 v1040 v1043 v1044 v1045 v1047 v1048 v1049 v1050 v1051 v1052 v1053 v1054 v1055 v1056 v1057 v1058 v1059 v1060 v1061 v1062 v1063 v1064 v1065 v1066 v1067 v1068 v1069 v1070 v1071 v1072 v1073 v1074 v1075 v1076 v1077 v1078 v1079 v1080 v1081 v1082 v1083 v1084 v1085 v1086 v1087 v1088 v1089 v1090 v1091 v1092 v1093 v1094 v1095 v1096 v1097 v1098 v1099 v1100 v1101 v1102 v1103 v1104 v1105 v1106 v1107 v1108 v1109 v1110 v1111 v1112 v1113 v1114 v1115 v1116 v1117 v1118 v1119 v1120 v1121 v1122 v1123 v1124 v1125 v1126 v1127 v1128 v1129 v1130 v1131 v1132 v1133 v1134 v1135 v1136 v1137 v1138 v1139 v1140 v1141 v1142 v1143 v1144 v1145 v1148 v1149 v1150 v1151 v1152 v1153 v1154 v1155 v1156 v1174 v1175 v1176 t1174 v1178 v1179 v1180 v1181 v1182 v1183 v1184 v1185 v1186 v1188 v1189 v1192 v1194 v1196 v1199 v1200 v1201 v1202 v1203 v1204 v1205 v1206 v1207 v1208 v1209 v1210 v1211 v1212 v1213 v1214 v1215 v1216 v1217 v1218 v1219 v1220 v1221 v1222 v1223 v1224 v1225 v1226 v1227 v1228 v1229 v1230 v1231 v1232 at h
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
  have h_v4 : R 1 0 4611686018427387904 4611686087146864624 v4 v4 := (r1_ix hb_F2 0 (of_decide_eq_true rfl))
  have e_v4 : sv v4 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F2 0 (of_decide_eq_true rfl)
  have h_v5 : R 1 0 4611686018427387904 4611686087146864624 v5 v5 := (r1_ix hb_F2 32 (of_decide_eq_true rfl))
  have e_v5 : sv v5 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F2 32 (of_decide_eq_true rfl)
  have h_v6 : R 1 0 4611686018427387904 4611686087146864624 v6 v6 := (r1_ix hb_F3 0 (of_decide_eq_true rfl))
  have e_v6 : sv v6 = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F3 0 (of_decide_eq_true rfl)
  have h_v8 : R 1 0 4611686018427387903 4611686018427387903 v8 v8 := (r_c hl 4611686018427387903 (of_decide_eq_true rfl))
  have e_v8 : sv v8 = (-1) := e_c 4611686018427387903 (-1) (of_decide_eq_true rfl)
  have h_v9 : R 1 0 0 1 v9 v9 := (r_plt hl h_v8 h_v0 (of_decide_eq_true rfl))
  have e_v9 : (v9 = 1 ↔ sv v8 < sv v0) := e_plt h_v8 h_v0 (of_decide_eq_true rfl)
  have h_v10 : R 1 0 4611686019270702761 4611686019270702761 v10 v10 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have e_v10 : sv v10 = (843314857) := e_c 4611686019270702761 (843314857) (of_decide_eq_true rfl)
  have h_v11 : R 1 0 0 1 v11 v11 := (r_plt hl h_v10 h_v1 (of_decide_eq_true rfl))
  clear e_OFFr e_H61r
  have e_v11 : (v11 = 1 ↔ sv v10 < sv v1) := e_plt h_v10 h_v1 (of_decide_eq_true rfl)
  have h_v12 : R 1 0 0 1 v12 v12 := (r_sub hl (r_O hl) h_v11 (of_decide_eq_true rfl))
  have e_v12 : (v12 = 1 ↔ ¬v11 = 1) := e_not h_v11 (of_decide_eq_true rfl)
  have h_v13 : R 1 0 0 1 v13 v13 := (r_land hl h_v9 h_v12 (of_decide_eq_true rfl))
  have e_v13 : (v13 = 1 ↔ v9 = 1 ∧ v12 = 1) := e_land h_v9 h_v12 (of_decide_eq_true rfl)
  have h_t0_1 : R 1 0 4611686018427387904 4611686018695823363 t0.1 t0.1 := r_sc1 hl h_v0 (of_decide_eq_true rfl)
  have h_t0_2 : R 1 0 4611686018158952445 4611686018695823363 t0.2 t0.2 := r_sc2 hl h_v0 (of_decide_eq_true rfl)
  have e_t0_1 : sv t0.1 = (sc28pS (scArg v0)).1 := e_sc1 h_v0 (of_decide_eq_true rfl)
  have e_t0_2 : sv t0.2 = (sc28pS (scArg v0)).2 := e_sc2 h_v0 (of_decide_eq_true rfl)
  have h_t1_1 : R 1 0 4611686018427387904 4611686018695823363 t1.1 t1.1 := r_sc1 hl h_v1 (of_decide_eq_true rfl)
  have h_t1_2 : R 1 0 4611686018158952445 4611686018695823363 t1.2 t1.2 := r_sc2 hl h_v1 (of_decide_eq_true rfl)
  have e_t1_1 : sv t1.1 = (sc28pS (scArg v1)).1 := e_sc1 h_v1 (of_decide_eq_true rfl)
  have e_t1_2 : sv t1.2 = (sc28pS (scArg v1)).2 := e_sc2 h_v1 (of_decide_eq_true rfl)
  have h_v16 : R 1 0 0 1 v16 v16 := (r_plt hl h_t0_1 h_t1_1 (of_decide_eq_true rfl))
  have e_v16 : (v16 = 1 ↔ sv t0.1 < sv t1.1) := e_plt h_t0_1 h_t1_1 (of_decide_eq_true rfl)
  have h_v17 : R 1 0 4611686018427387904 4611686018695823363 v17 v17 := (r_psel hl h_v16 h_t0_1 h_t1_1 (of_decide_eq_true rfl))
  have e_v17 : v17 = if v16 = 1 then t0.1 else t1.1 := e_psel h_v16 h_t0_1 h_t1_1 (of_decide_eq_true rfl)
  have h_v18 : R 1 0 4611686018427387900 4611686018427387900 v18 v18 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have e_v18 : sv v18 = (-4) := e_c 4611686018427387900 (-4) (of_decide_eq_true rfl)
  have h_v19 : R 1 0 4611686018427387900 4611686018695823359 v19 v19 := (r_sub hl (r_add hl h_v17 h_v18 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v19 : sv v19 = sv v17 + sv v18 := e_add h_v17 h_v18 (of_decide_eq_true rfl)
  have h_v20 : R 1 0 4611686018427387904 4611686018695823363 v20 v20 := (r_psel hl h_v16 h_t1_1 h_t0_1 (of_decide_eq_true rfl))
  have e_v20 : v20 = if v16 = 1 then t1.1 else t0.1 := e_psel h_v16 h_t1_1 h_t0_1 (of_decide_eq_true rfl)
  have h_v21 : R 1 0 4611686018427387908 4611686018427387908 v21 v21 := (r_c hl 4611686018427387908 (of_decide_eq_true rfl))
  have e_v21 : sv v21 = (4) := e_c 4611686018427387908 (4) (of_decide_eq_true rfl)
  clear h_v11 h_t0_1 h_t1_1 h_v16 h_v17
  have h_v22 : R 1 0 4611686018427387908 4611686018695823367 v22 v22 := (r_sub hl (r_add hl h_v20 h_v21 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v22 : sv v22 = sv v20 + sv v21 := e_add h_v20 h_v21 (of_decide_eq_true rfl)
  have h_v23 : R 1 0 4611686018695823360 4611686018695823360 v23 v23 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have e_v23 : sv v23 = (268435456) := e_c 4611686018695823360 (268435456) (of_decide_eq_true rfl)
  have h_v24 : R 1 0 0 1 v24 v24 := (r_plt hl h_v22 h_v23 (of_decide_eq_true rfl))
  have e_v24 : (v24 = 1 ↔ sv v22 < sv v23) := e_plt h_v22 h_v23 (of_decide_eq_true rfl)
  have h_v25 : R 1 0 4611686018427387908 4611686018695823367 v25 v25 := (r_psel hl h_v24 h_v22 h_v23 (of_decide_eq_true rfl))
  have e_v25 : v25 = if v24 = 1 then v22 else v23 := e_psel h_v24 h_v22 h_v23 (of_decide_eq_true rfl)
  have h_v26 : R 1 0 4611686018849045334 4611686018849045334 v26 v26 := (r_c hl 4611686018849045334 (of_decide_eq_true rfl))
  have e_v26 : sv v26 = (421657430) := e_c 4611686018849045334 (421657430) (of_decide_eq_true rfl)
  have h_v27 : R 1 0 0 1 v27 v27 := (r_plt hl h_v0 h_v26 (of_decide_eq_true rfl))
  have e_v27 : (v27 = 1 ↔ sv v0 < sv v26) := e_plt h_v0 h_v26 (of_decide_eq_true rfl)
  have h_v28 : R 1 0 4611686018849045331 4611686018849045331 v28 v28 := (r_c hl 4611686018849045331 (of_decide_eq_true rfl))
  have e_v28 : sv v28 = (421657427) := e_c 4611686018849045331 (421657427) (of_decide_eq_true rfl)
  have h_v29 : R 1 0 0 1 v29 v29 := (r_plt hl h_v28 h_v1 (of_decide_eq_true rfl))
  have e_v29 : (v29 = 1 ↔ sv v28 < sv v1) := e_plt h_v28 h_v1 (of_decide_eq_true rfl)
  have h_v30 : R 1 0 0 1 v30 v30 := (r_land hl h_v27 h_v29 (of_decide_eq_true rfl))
  have e_v30 : (v30 = 1 ↔ v27 = 1 ∧ v29 = 1) := e_land h_v27 h_v29 (of_decide_eq_true rfl)
  have h_v31 : R 1 0 4611686018427387908 4611686018695823367 v31 v31 := (r_psel hl h_v30 h_v23 h_v25 (of_decide_eq_true rfl))
  have e_v31 : v31 = if v30 = 1 then v23 else v25 := e_psel h_v30 h_v23 h_v25 (of_decide_eq_true rfl)
  have h_v32 : R 1 0 4611686018427387904 4611686052787126264 v32 v32 := (r_add hl (r_pshr1 hl h_v2) h_H61r (of_decide_eq_true rfl))
  have e_v32 : sv v32 = sv v2 / 2 := e_halfF h_v2
  have h_v33 : R 1 0 4611686018427387904 4611686052787126264 v33 v33 := (r_add hl (r_pshr1 hl (r_add hl h_v3 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v33 : sv v33 = (sv v3 + 1) / 2 := e_halfC h_v3 (of_decide_eq_true rfl)
  have h_v34 : R 1 0 0 1 v34 v34 := (r_plt hl h_v8 h_v32 (of_decide_eq_true rfl))
  clear h_v20 h_v22 h_v24 h_v25 h_v27 h_v29 h_v30
  have e_v34 : (v34 = 1 ↔ sv v8 < sv v32) := e_plt h_v8 h_v32 (of_decide_eq_true rfl)
  have h_v35 : R 1 0 0 1 v35 v35 := (r_plt hl h_v10 h_v33 (of_decide_eq_true rfl))
  have e_v35 : (v35 = 1 ↔ sv v10 < sv v33) := e_plt h_v10 h_v33 (of_decide_eq_true rfl)
  have h_v36 : R 1 0 0 1 v36 v36 := (r_sub hl (r_O hl) h_v35 (of_decide_eq_true rfl))
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
  have h_v40 : R 1 0 0 1 v40 v40 := (r_plt hl h_t32_1 h_t33_1 (of_decide_eq_true rfl))
  have e_v40 : (v40 = 1 ↔ sv t32.1 < sv t33.1) := e_plt h_t32_1 h_t33_1 (of_decide_eq_true rfl)
  have h_v41 : R 1 0 4611686018427387904 4611686018695823363 v41 v41 := (r_psel hl h_v40 h_t32_1 h_t33_1 (of_decide_eq_true rfl))
  have e_v41 : v41 = if v40 = 1 then t32.1 else t33.1 := e_psel h_v40 h_t32_1 h_t33_1 (of_decide_eq_true rfl)
  have h_v42 : R 1 0 4611686018427387900 4611686018695823359 v42 v42 := (r_sub hl (r_add hl h_v18 h_v41 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v42 : sv v42 = sv v18 + sv v41 := e_add h_v18 h_v41 (of_decide_eq_true rfl)
  have h_v43 : R 1 0 4611686018427387904 4611686018695823363 v43 v43 := (r_psel hl h_v40 h_t33_1 h_t32_1 (of_decide_eq_true rfl))
  have e_v43 : v43 = if v40 = 1 then t33.1 else t32.1 := e_psel h_v40 h_t33_1 h_t32_1 (of_decide_eq_true rfl)
  have h_v44 : R 1 0 4611686018427387908 4611686018695823367 v44 v44 := (r_sub hl (r_add hl h_v21 h_v43 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v44 : sv v44 = sv v21 + sv v43 := e_add h_v21 h_v43 (of_decide_eq_true rfl)
  clear h_v35 h_t33_2 e_t33_2 h_v40 h_v41 h_v43
  have h_v45 : R 1 0 0 1 v45 v45 := (r_plt hl h_v44 h_v23 (of_decide_eq_true rfl))
  have e_v45 : (v45 = 1 ↔ sv v44 < sv v23) := e_plt h_v44 h_v23 (of_decide_eq_true rfl)
  have h_v46 : R 1 0 4611686018427387908 4611686018695823367 v46 v46 := (r_psel hl h_v45 h_v44 h_v23 (of_decide_eq_true rfl))
  have e_v46 : v46 = if v45 = 1 then v44 else v23 := e_psel h_v45 h_v44 h_v23 (of_decide_eq_true rfl)
  have h_v47 : R 1 0 0 1 v47 v47 := (r_plt hl h_v32 h_v26 (of_decide_eq_true rfl))
  have e_v47 : (v47 = 1 ↔ sv v32 < sv v26) := e_plt h_v32 h_v26 (of_decide_eq_true rfl)
  have h_v48 : R 1 0 0 1 v48 v48 := (r_plt hl h_v28 h_v33 (of_decide_eq_true rfl))
  have e_v48 : (v48 = 1 ↔ sv v28 < sv v33) := e_plt h_v28 h_v33 (of_decide_eq_true rfl)
  have h_v49 : R 1 0 0 1 v49 v49 := (r_land hl h_v47 h_v48 (of_decide_eq_true rfl))
  have e_v49 : (v49 = 1 ↔ v47 = 1 ∧ v48 = 1) := e_land h_v47 h_v48 (of_decide_eq_true rfl)
  have h_v50 : R 1 0 4611686018427387908 4611686018695823367 v50 v50 := (r_psel hl h_v49 h_v23 h_v46 (of_decide_eq_true rfl))
  have e_v50 : v50 = if v49 = 1 then v23 else v46 := e_psel h_v49 h_v23 h_v46 (of_decide_eq_true rfl)
  have h_v51 : R 1 0 4611686018427387904 4611686018427387904 v51 v51 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have e_v51 : sv v51 = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have h_v52 : R 1 0 0 1 v52 v52 := (r_plt hl h_v19 h_v51 (of_decide_eq_true rfl))
  have e_v52 : (v52 = 1 ↔ sv v19 < sv v51) := e_plt h_v19 h_v51 (of_decide_eq_true rfl)
  have h_v53 : R 1 0 0 1 v53 v53 := (r_sub hl (r_O hl) h_v52 (of_decide_eq_true rfl))
  have e_v53 : (v53 = 1 ↔ ¬v52 = 1) := e_not h_v52 (of_decide_eq_true rfl)
  have h_v54 : R 1 0 0 1 v54 v54 := (r_plt hl h_v51 h_v31 (of_decide_eq_true rfl))
  have e_v54 : (v54 = 1 ↔ sv v51 < sv v31) := e_plt h_v51 h_v31 (of_decide_eq_true rfl)
  have h_v55 : R 1 0 0 1 v55 v55 := (r_sub hl (r_O hl) h_v54 (of_decide_eq_true rfl))
  have e_v55 : (v55 = 1 ↔ ¬v54 = 1) := e_not h_v54 (of_decide_eq_true rfl)
  have h_v56 : R 1 0 0 1 v56 v56 := (r_land hl h_v52 h_v55 (of_decide_eq_true rfl))
  have e_v56 : (v56 = 1 ↔ v52 = 1 ∧ v55 = 1) := e_land h_v52 h_v55 (of_decide_eq_true rfl)
  have h_v57 : R 1 0 0 1 v57 v57 := (r_land hl h_v52 h_v54 (of_decide_eq_true rfl))
  clear h_v33 h_v44 h_v45 h_v46 h_v49 h_v55
  have e_v57 : (v57 = 1 ↔ v52 = 1 ∧ v54 = 1) := e_land h_v52 h_v54 (of_decide_eq_true rfl)
  have h_v58 : R 1 0 0 1 v58 v58 := (r_plt hl h_v42 h_v51 (of_decide_eq_true rfl))
  have e_v58 : (v58 = 1 ↔ sv v42 < sv v51) := e_plt h_v42 h_v51 (of_decide_eq_true rfl)
  have h_v59 : R 1 0 0 1 v59 v59 := (r_sub hl (r_O hl) h_v58 (of_decide_eq_true rfl))
  have e_v59 : (v59 = 1 ↔ ¬v58 = 1) := e_not h_v58 (of_decide_eq_true rfl)
  have h_v60 : R 1 0 0 1 v60 v60 := (r_plt hl h_v51 h_v50 (of_decide_eq_true rfl))
  have e_v60 : (v60 = 1 ↔ sv v51 < sv v50) := e_plt h_v51 h_v50 (of_decide_eq_true rfl)
  have h_v61 : R 1 0 0 1 v61 v61 := (r_sub hl (r_O hl) h_v60 (of_decide_eq_true rfl))
  have e_v61 : (v61 = 1 ↔ ¬v60 = 1) := e_not h_v60 (of_decide_eq_true rfl)
  have h_v62 : R 1 0 0 1 v62 v62 := (r_land hl h_v58 h_v61 (of_decide_eq_true rfl))
  have e_v62 : (v62 = 1 ↔ v58 = 1 ∧ v61 = 1) := e_land h_v58 h_v61 (of_decide_eq_true rfl)
  have h_v63 : R 1 0 0 1 v63 v63 := (r_land hl h_v58 h_v60 (of_decide_eq_true rfl))
  have e_v63 : (v63 = 1 ↔ v58 = 1 ∧ v60 = 1) := e_land h_v58 h_v60 (of_decide_eq_true rfl)
  have h_v64 : R 1 0 0 1 v64 v64 := (r_land hl h_v57 h_v63 (of_decide_eq_true rfl))
  have e_v64 : (v64 = 1 ↔ v57 = 1 ∧ v63 = 1) := e_land h_v57 h_v63 (of_decide_eq_true rfl)
  have h_v65 : R 1 0 0 1 v65 v65 := (r_sub hl (r_O hl) h_v64 (of_decide_eq_true rfl))
  have e_v65 : (v65 = 1 ↔ ¬v64 = 1) := e_not h_v64 (of_decide_eq_true rfl)
  have h_v66 : R 1 0 0 1 v66 v66 := (r_land hl h_v53 h_v63 (of_decide_eq_true rfl))
  have e_v66 : (v66 = 1 ↔ v53 = 1 ∧ v63 = 1) := e_land h_v53 h_v63 (of_decide_eq_true rfl)
  have h_v67 : R 1 0 0 1 v67 v67 := (r_lor hl h_v62 h_v66 (of_decide_eq_true rfl))
  have e_v67 : (v67 = 1 ↔ v62 = 1 ∨ v66 = 1) := e_lor h_v62 h_v66 (of_decide_eq_true rfl)
  have h_v68 : R 1 0 4611686018427387900 4611686018695823367 v68 v68 := (r_psel hl h_v67 h_v31 h_v19 (of_decide_eq_true rfl))
  have e_v68 : v68 = if v67 = 1 then v31 else v19 := e_psel h_v67 h_v31 h_v19 (of_decide_eq_true rfl)
  have h_v69 : R 1 0 0 1 v69 v69 := (r_land hl h_v57 h_v59 (of_decide_eq_true rfl))
  have e_v69 : (v69 = 1 ↔ v57 = 1 ∧ v59 = 1) := e_land h_v57 h_v59 (of_decide_eq_true rfl)
  clear h_v52 h_v54 h_v58 h_v59 h_v60 h_v61 h_v64 h_v66 h_v67
  have h_v70 : R 1 0 0 1 v70 v70 := (r_lor hl h_v56 h_v69 (of_decide_eq_true rfl))
  have e_v70 : (v70 = 1 ↔ v56 = 1 ∨ v69 = 1) := e_lor h_v56 h_v69 (of_decide_eq_true rfl)
  have h_v71 : R 1 0 4611686018427387900 4611686018695823367 v71 v71 := (r_psel hl h_v70 h_v50 h_v42 (of_decide_eq_true rfl))
  have e_v71 : v71 = if v70 = 1 then v50 else v42 := e_psel h_v70 h_v50 h_v42 (of_decide_eq_true rfl)
  have h_v72 : R 1 0 0 1 v72 v72 := (r_land hl h_v56 h_v63 (of_decide_eq_true rfl))
  have e_v72 : (v72 = 1 ↔ v56 = 1 ∧ v63 = 1) := e_land h_v56 h_v63 (of_decide_eq_true rfl)
  have h_v73 : R 1 0 0 1 v73 v73 := (r_lor hl h_v62 h_v72 (of_decide_eq_true rfl))
  have e_v73 : (v73 = 1 ↔ v62 = 1 ∨ v72 = 1) := e_lor h_v62 h_v72 (of_decide_eq_true rfl)
  have h_v74 : R 1 0 4611686018427387900 4611686018695823367 v74 v74 := (r_psel hl h_v73 h_v19 h_v31 (of_decide_eq_true rfl))
  have e_v74 : v74 = if v73 = 1 then v19 else v31 := e_psel h_v73 h_v19 h_v31 (of_decide_eq_true rfl)
  have h_v75 : R 1 0 0 1 v75 v75 := (r_land hl h_v57 h_v62 (of_decide_eq_true rfl))
  have e_v75 : (v75 = 1 ↔ v57 = 1 ∧ v62 = 1) := e_land h_v57 h_v62 (of_decide_eq_true rfl)
  have h_v76 : R 1 0 0 1 v76 v76 := (r_lor hl h_v56 h_v75 (of_decide_eq_true rfl))
  have e_v76 : (v76 = 1 ↔ v56 = 1 ∨ v75 = 1) := e_lor h_v56 h_v75 (of_decide_eq_true rfl)
  have h_v77 : R 1 0 4611686018427387900 4611686018695823367 v77 v77 := (r_psel hl h_v76 h_v42 h_v50 (of_decide_eq_true rfl))
  have e_v77 : v77 = if v76 = 1 then v42 else v50 := e_psel h_v76 h_v42 h_v50 (of_decide_eq_true rfl)
  have h_v78 : R 1 0 4611686017353646052 4683743616223412273 v78 v78 := (r_smx hl 29 h_v71 h_v68 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v78 : sv v78 = sv v71 * sv v68 := e_smx 29 h_v71 h_v68 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v79 : R 1 0 4611686018427387899 4611686018695823374 v79 v79 := (r_srdF hl h_v78 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v79 : sv v79 = sv v78 / 2 ^ 28 := e_srdF h_v78 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v80 : R 1 0 4611686017353646052 4683743616223412273 v80 v80 := (r_smx hl 29 h_v77 h_v74 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v80 : sv v80 = sv v77 * sv v74 := e_smx 29 h_v77 h_v74 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v81 : R 1 0 4611686018427387900 4611686018695823375 v81 v81 := (r_srdC hl h_v80 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v81 : sv v81 = -((-sv v80) / 2 ^ 28) := e_srdC h_v80 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v82 : R 1 0 0 1 v82 v82 := (r_plt hl h_v8 h_v79 (of_decide_eq_true rfl))
  clear h_v42 h_v50 h_v62 h_v63 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v80
  have e_v82 : (v82 = 1 ↔ sv v8 < sv v79) := e_plt h_v8 h_v79 (of_decide_eq_true rfl)
  have h_v84 : R 1 0 4611686018158952441 4611686018695823359 v84 v84 := (r_sub hl (r_add hl h_v18 h_t1_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v84 : sv v84 = sv v18 + sv t1.2 := e_add h_v18 h_t1_2 (of_decide_eq_true rfl)
  have h_v85 : R 1 0 4611686018158952448 4611686018158952448 v85 v85 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have e_v85 : sv v85 = (-268435456) := e_c 4611686018158952448 (-268435456) (of_decide_eq_true rfl)
  have h_v86 : R 1 0 0 1 v86 v86 := (r_plt hl h_v84 h_v85 (of_decide_eq_true rfl))
  have e_v86 : (v86 = 1 ↔ sv v84 < sv v85) := e_plt h_v84 h_v85 (of_decide_eq_true rfl)
  have h_v87 : R 1 0 4611686018158952441 4611686018695823359 v87 v87 := (r_psel hl h_v86 h_v85 h_v84 (of_decide_eq_true rfl))
  have e_v87 : v87 = if v86 = 1 then v85 else v84 := e_psel h_v86 h_v85 h_v84 (of_decide_eq_true rfl)
  have h_v88 : R 1 0 4611686019270702759 4611686019270702759 v88 v88 := (r_c hl 4611686019270702759 (of_decide_eq_true rfl))
  have e_v88 : sv v88 = (843314855) := e_c 4611686019270702759 (843314855) (of_decide_eq_true rfl)
  have h_v89 : R 1 0 0 1 v89 v89 := (r_plt hl h_v88 h_v1 (of_decide_eq_true rfl))
  have e_v89 : (v89 = 1 ↔ sv v88 < sv v1) := e_plt h_v88 h_v1 (of_decide_eq_true rfl)
  have h_v90 : R 1 0 4611686018158952441 4611686018695823359 v90 v90 := (r_psel hl h_v89 h_v85 h_v87 (of_decide_eq_true rfl))
  have e_v90 : v90 = if v89 = 1 then v85 else v87 := e_psel h_v89 h_v85 h_v87 (of_decide_eq_true rfl)
  have h_v92 : R 1 0 4611686018158952449 4611686018695823367 v92 v92 := (r_sub hl (r_add hl h_v21 h_t0_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v92 : sv v92 = sv v21 + sv t0.2 := e_add h_v21 h_t0_2 (of_decide_eq_true rfl)
  have h_v93 : R 1 0 0 1 v93 v93 := (r_plt hl h_v92 h_v23 (of_decide_eq_true rfl))
  have e_v93 : (v93 = 1 ↔ sv v92 < sv v23) := e_plt h_v92 h_v23 (of_decide_eq_true rfl)
  have h_v94 : R 1 0 4611686018158952449 4611686018695823367 v94 v94 := (r_psel hl h_v93 h_v92 h_v23 (of_decide_eq_true rfl))
  have e_v94 : v94 = if v93 = 1 then v92 else v23 := e_psel h_v93 h_v92 h_v23 (of_decide_eq_true rfl)
  have h_v95 : R 1 0 4611686018427387905 4611686018427387905 v95 v95 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have e_v95 : sv v95 = (1) := e_c 4611686018427387905 (1) (of_decide_eq_true rfl)
  have h_v96 : R 1 0 0 1 v96 v96 := (r_plt hl h_v0 h_v95 (of_decide_eq_true rfl))
  have e_v96 : (v96 = 1 ↔ sv v0 < sv v95) := e_plt h_v0 h_v95 (of_decide_eq_true rfl)
  clear h_t0_2 h_t1_2 h_v84 h_v86 h_v87 h_v88 h_v89 h_v92 h_v93
  have h_v97 : R 1 0 4611686018158952449 4611686018695823367 v97 v97 := (r_psel hl h_v96 h_v23 h_v94 (of_decide_eq_true rfl))
  have e_v97 : v97 = if v96 = 1 then v23 else v94 := e_psel h_v96 h_v23 h_v94 (of_decide_eq_true rfl)
  have h_v98 : R 1 0 4611686018427387904 4611686052787126264 v98 v98 := (r_add hl (r_pshr1 hl h_v3) h_H61r (of_decide_eq_true rfl))
  have e_v98 : sv v98 = sv v3 / 2 := e_halfF h_v3
  have h_v99 : R 1 0 0 1 v99 v99 := (r_plt hl h_v8 h_v98 (of_decide_eq_true rfl))
  have e_v99 : (v99 = 1 ↔ sv v8 < sv v98) := e_plt h_v8 h_v98 (of_decide_eq_true rfl)
  have h_v100 : R 1 0 0 1 v100 v100 := (r_land hl h_v36 h_v99 (of_decide_eq_true rfl))
  have e_v100 : (v100 = 1 ↔ v36 = 1 ∧ v99 = 1) := e_land h_v36 h_v99 (of_decide_eq_true rfl)
  have h_t98_1 : R 1 0 4611686018427387904 4611686018695823363 t98.1 t98.1 := r_sc1 hl h_v98 (of_decide_eq_true rfl)
  have h_t98_2 : R 1 0 4611686018158952445 4611686018695823363 t98.2 t98.2 := r_sc2 hl h_v98 (of_decide_eq_true rfl)
  have e_t98_1 : sv t98.1 = (sc28pS (scArg v98)).1 := e_sc1 h_v98 (of_decide_eq_true rfl)
  have e_t98_2 : sv t98.2 = (sc28pS (scArg v98)).2 := e_sc2 h_v98 (of_decide_eq_true rfl)
  have h_v114 : R 1 0 0 1 v114 v114 := (r_plt hl h_t98_1 h_t33_1 (of_decide_eq_true rfl))
  have e_v114 : (v114 = 1 ↔ sv t98.1 < sv t33.1) := e_plt h_t98_1 h_t33_1 (of_decide_eq_true rfl)
  have h_v115 : R 1 0 4611686018427387904 4611686018695823363 v115 v115 := (r_psel hl h_v114 h_t98_1 h_t33_1 (of_decide_eq_true rfl))
  have e_v115 : v115 = if v114 = 1 then t98.1 else t33.1 := e_psel h_v114 h_t98_1 h_t33_1 (of_decide_eq_true rfl)
  have h_v116 : R 1 0 4611686018427387900 4611686018695823359 v116 v116 := (r_sub hl (r_add hl h_v18 h_v115 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v116 : sv v116 = sv v18 + sv v115 := e_add h_v18 h_v115 (of_decide_eq_true rfl)
  have h_v117 : R 1 0 4611686018427387904 4611686018695823363 v117 v117 := (r_psel hl h_v114 h_t33_1 h_t98_1 (of_decide_eq_true rfl))
  have e_v117 : v117 = if v114 = 1 then t33.1 else t98.1 := e_psel h_v114 h_t33_1 h_t98_1 (of_decide_eq_true rfl)
  have h_v118 : R 1 0 4611686018427387908 4611686018695823367 v118 v118 := (r_sub hl (r_add hl h_v21 h_v117 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v118 : sv v118 = sv v21 + sv v117 := e_add h_v21 h_v117 (of_decide_eq_true rfl)
  have h_v119 : R 1 0 0 1 v119 v119 := (r_plt hl h_v118 h_v23 (of_decide_eq_true rfl))
  have e_v119 : (v119 = 1 ↔ sv v118 < sv v23) := e_plt h_v118 h_v23 (of_decide_eq_true rfl)
  have h_v120 : R 1 0 4611686018427387908 4611686018695823367 v120 v120 := (r_psel hl h_v119 h_v118 h_v23 (of_decide_eq_true rfl))
  clear h_v3 h_v36 h_t33_1 h_v94 h_v96 h_v99 h_t98_1 h_t98_2 e_t98_2 h_v114 h_v115 h_v117
  have e_v120 : v120 = if v119 = 1 then v118 else v23 := e_psel h_v119 h_v118 h_v23 (of_decide_eq_true rfl)
  have h_v121 : R 1 0 0 1 v121 v121 := (r_plt hl h_v98 h_v26 (of_decide_eq_true rfl))
  have e_v121 : (v121 = 1 ↔ sv v98 < sv v26) := e_plt h_v98 h_v26 (of_decide_eq_true rfl)
  have h_v122 : R 1 0 0 1 v122 v122 := (r_land hl h_v48 h_v121 (of_decide_eq_true rfl))
  have e_v122 : (v122 = 1 ↔ v48 = 1 ∧ v121 = 1) := e_land h_v48 h_v121 (of_decide_eq_true rfl)
  have h_v123 : R 1 0 4611686018427387908 4611686018695823367 v123 v123 := (r_psel hl h_v122 h_v23 h_v120 (of_decide_eq_true rfl))
  have e_v123 : v123 = if v122 = 1 then v23 else v120 := e_psel h_v122 h_v23 h_v120 (of_decide_eq_true rfl)
  have h_v124 : R 1 0 0 1 v124 v124 := (r_plt hl h_v90 h_v51 (of_decide_eq_true rfl))
  have e_v124 : (v124 = 1 ↔ sv v90 < sv v51) := e_plt h_v90 h_v51 (of_decide_eq_true rfl)
  have h_v125 : R 1 0 0 1 v125 v125 := (r_sub hl (r_O hl) h_v124 (of_decide_eq_true rfl))
  have e_v125 : (v125 = 1 ↔ ¬v124 = 1) := e_not h_v124 (of_decide_eq_true rfl)
  have h_v126 : R 1 0 0 1 v126 v126 := (r_plt hl h_v51 h_v97 (of_decide_eq_true rfl))
  have e_v126 : (v126 = 1 ↔ sv v51 < sv v97) := e_plt h_v51 h_v97 (of_decide_eq_true rfl)
  have h_v127 : R 1 0 0 1 v127 v127 := (r_sub hl (r_O hl) h_v126 (of_decide_eq_true rfl))
  have e_v127 : (v127 = 1 ↔ ¬v126 = 1) := e_not h_v126 (of_decide_eq_true rfl)
  have h_v128 : R 1 0 0 1 v128 v128 := (r_land hl h_v124 h_v127 (of_decide_eq_true rfl))
  have e_v128 : (v128 = 1 ↔ v124 = 1 ∧ v127 = 1) := e_land h_v124 h_v127 (of_decide_eq_true rfl)
  have h_v129 : R 1 0 0 1 v129 v129 := (r_land hl h_v124 h_v126 (of_decide_eq_true rfl))
  have e_v129 : (v129 = 1 ↔ v124 = 1 ∧ v126 = 1) := e_land h_v124 h_v126 (of_decide_eq_true rfl)
  have h_v130 : R 1 0 0 1 v130 v130 := (r_plt hl h_v116 h_v51 (of_decide_eq_true rfl))
  have e_v130 : (v130 = 1 ↔ sv v116 < sv v51) := e_plt h_v116 h_v51 (of_decide_eq_true rfl)
  have h_v132 : R 1 0 0 1 v132 v132 := (r_plt hl h_v51 h_v123 (of_decide_eq_true rfl))
  have e_v132 : (v132 = 1 ↔ sv v51 < sv v123) := e_plt h_v51 h_v123 (of_decide_eq_true rfl)
  have h_v135 : R 1 0 0 1 v135 v135 := (r_land hl h_v130 h_v132 (of_decide_eq_true rfl))
  have e_v135 : (v135 = 1 ↔ v130 = 1 ∧ v132 = 1) := e_land h_v130 h_v132 (of_decide_eq_true rfl)
  clear h_v48 h_v98 h_v116 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v126 h_v127 h_v130 h_v132
  have h_v136 : R 1 0 0 1 v136 v136 := (r_land hl h_v129 h_v135 (of_decide_eq_true rfl))
  have e_v136 : (v136 = 1 ↔ v129 = 1 ∧ v135 = 1) := e_land h_v129 h_v135 (of_decide_eq_true rfl)
  have h_v137 : R 1 0 0 1 v137 v137 := (r_sub hl (r_O hl) h_v136 (of_decide_eq_true rfl))
  have e_v137 : (v137 = 1 ↔ ¬v136 = 1) := e_not h_v136 (of_decide_eq_true rfl)
  have h_v186 : R 1 0 4611686018849045332 4611686018849045332 v186 v186 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  have e_v186 : sv v186 = (421657428) := e_c 4611686018849045332 (421657428) (of_decide_eq_true rfl)
  have h_v193 : R 1 0 4611686018849045333 4611686018849045333 v193 v193 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have e_v193 : sv v193 = (421657429) := e_c 4611686018849045333 (421657429) (of_decide_eq_true rfl)
  have h_v247 : R 1 0 4611686018427387904 4611686052787126264 v247 v247 := (r_add hl (r_pshr1 hl (r_add hl h_v2 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v247 : sv v247 = (sv v2 + 1) / 2 := e_halfC h_v2 (of_decide_eq_true rfl)
  have h_v248 : R 1 0 0 1 v248 v248 := (r_plt hl h_v10 h_v247 (of_decide_eq_true rfl))
  have e_v248 : (v248 = 1 ↔ sv v10 < sv v247) := e_plt h_v10 h_v247 (of_decide_eq_true rfl)
  have h_v249 : R 1 0 0 1 v249 v249 := (r_sub hl (r_O hl) h_v248 (of_decide_eq_true rfl))
  have e_v249 : (v249 = 1 ↔ ¬v248 = 1) := e_not h_v248 (of_decide_eq_true rfl)
  have h_v250 : R 1 0 0 1 v250 v250 := (r_land hl h_v34 h_v249 (of_decide_eq_true rfl))
  have e_v250 : (v250 = 1 ↔ v34 = 1 ∧ v249 = 1) := e_land h_v34 h_v249 (of_decide_eq_true rfl)
  have h_v258 : R 1 0 4611686018158952449 4611686018695823367 v258 v258 := (r_sub hl (r_add hl h_v21 h_t32_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v258 : sv v258 = sv v21 + sv t32.2 := e_add h_v21 h_t32_2 (of_decide_eq_true rfl)
  have h_v259 : R 1 0 0 1 v259 v259 := (r_plt hl h_v258 h_v23 (of_decide_eq_true rfl))
  have e_v259 : (v259 = 1 ↔ sv v258 < sv v23) := e_plt h_v258 h_v23 (of_decide_eq_true rfl)
  have h_v260 : R 1 0 4611686018158952449 4611686018695823367 v260 v260 := (r_psel hl h_v259 h_v258 h_v23 (of_decide_eq_true rfl))
  have e_v260 : v260 = if v259 = 1 then v258 else v23 := e_psel h_v259 h_v258 h_v23 (of_decide_eq_true rfl)
  have h_v261 : R 1 0 0 1 v261 v261 := (r_plt hl h_v32 h_v95 (of_decide_eq_true rfl))
  have e_v261 : (v261 = 1 ↔ sv v32 < sv v95) := e_plt h_v32 h_v95 (of_decide_eq_true rfl)
  have h_v262 : R 1 0 4611686018158952449 4611686018695823367 v262 v262 := (r_psel hl h_v261 h_v23 h_v260 (of_decide_eq_true rfl))
  clear h_v2 h_v32 h_v34 h_t32_2 h_v135 h_v136 h_v248 h_v249 h_v258 h_v259
  have e_v262 : v262 = if v261 = 1 then v23 else v260 := e_psel h_v261 h_v23 h_v260 (of_decide_eq_true rfl)
  have h_t247_1 : R 1 0 4611686018427387904 4611686018695823363 t247.1 t247.1 := r_sc1 hl h_v247 (of_decide_eq_true rfl)
  have h_t247_2 : R 1 0 4611686018158952445 4611686018695823363 t247.2 t247.2 := r_sc2 hl h_v247 (of_decide_eq_true rfl)
  have e_t247_1 : sv t247.1 = (sc28pS (scArg v247)).1 := e_sc1 h_v247 (of_decide_eq_true rfl)
  have e_t247_2 : sv t247.2 = (sc28pS (scArg v247)).2 := e_sc2 h_v247 (of_decide_eq_true rfl)
  have h_v264 : R 1 0 0 1 v264 v264 := (r_plt hl h_t32_1 h_t247_1 (of_decide_eq_true rfl))
  have e_v264 : (v264 = 1 ↔ sv t32.1 < sv t247.1) := e_plt h_t32_1 h_t247_1 (of_decide_eq_true rfl)
  have h_v265 : R 1 0 4611686018427387904 4611686018695823363 v265 v265 := (r_psel hl h_v264 h_t32_1 h_t247_1 (of_decide_eq_true rfl))
  have e_v265 : v265 = if v264 = 1 then t32.1 else t247.1 := e_psel h_v264 h_t32_1 h_t247_1 (of_decide_eq_true rfl)
  have h_v266 : R 1 0 4611686018427387900 4611686018695823359 v266 v266 := (r_sub hl (r_add hl h_v18 h_v265 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v266 : sv v266 = sv v18 + sv v265 := e_add h_v18 h_v265 (of_decide_eq_true rfl)
  have h_v267 : R 1 0 4611686018427387904 4611686018695823363 v267 v267 := (r_psel hl h_v264 h_t247_1 h_t32_1 (of_decide_eq_true rfl))
  have e_v267 : v267 = if v264 = 1 then t247.1 else t32.1 := e_psel h_v264 h_t247_1 h_t32_1 (of_decide_eq_true rfl)
  have h_v268 : R 1 0 4611686018427387908 4611686018695823367 v268 v268 := (r_sub hl (r_add hl h_v21 h_v267 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v268 : sv v268 = sv v21 + sv v267 := e_add h_v21 h_v267 (of_decide_eq_true rfl)
  have h_v269 : R 1 0 0 1 v269 v269 := (r_plt hl h_v268 h_v23 (of_decide_eq_true rfl))
  have e_v269 : (v269 = 1 ↔ sv v268 < sv v23) := e_plt h_v268 h_v23 (of_decide_eq_true rfl)
  have h_v270 : R 1 0 4611686018427387908 4611686018695823367 v270 v270 := (r_psel hl h_v269 h_v268 h_v23 (of_decide_eq_true rfl))
  have e_v270 : v270 = if v269 = 1 then v268 else v23 := e_psel h_v269 h_v268 h_v23 (of_decide_eq_true rfl)
  have h_v271 : R 1 0 0 1 v271 v271 := (r_plt hl h_v28 h_v247 (of_decide_eq_true rfl))
  have e_v271 : (v271 = 1 ↔ sv v28 < sv v247) := e_plt h_v28 h_v247 (of_decide_eq_true rfl)
  have h_v272 : R 1 0 0 1 v272 v272 := (r_land hl h_v47 h_v271 (of_decide_eq_true rfl))
  have e_v272 : (v272 = 1 ↔ v47 = 1 ∧ v271 = 1) := e_land h_v47 h_v271 (of_decide_eq_true rfl)
  have h_v273 : R 1 0 4611686018427387908 4611686018695823367 v273 v273 := (r_psel hl h_v272 h_v23 h_v270 (of_decide_eq_true rfl))
  have e_v273 : v273 = if v272 = 1 then v23 else v270 := e_psel h_v272 h_v23 h_v270 (of_decide_eq_true rfl)
  clear h_t32_1 h_v47 h_v247 h_v260 h_v261 h_t247_1 h_t247_2 e_t247_2 h_v264 h_v265 h_v267 h_v268 h_v269 h_v270 h_v271 h_v272
  have h_v274 : R 1 0 0 1 v274 v274 := (r_plt hl h_v266 h_v51 (of_decide_eq_true rfl))
  have e_v274 : (v274 = 1 ↔ sv v266 < sv v51) := e_plt h_v266 h_v51 (of_decide_eq_true rfl)
  have h_v275 : R 1 0 0 1 v275 v275 := (r_sub hl (r_O hl) h_v274 (of_decide_eq_true rfl))
  have e_v275 : (v275 = 1 ↔ ¬v274 = 1) := e_not h_v274 (of_decide_eq_true rfl)
  have h_v276 : R 1 0 0 1 v276 v276 := (r_plt hl h_v51 h_v273 (of_decide_eq_true rfl))
  have e_v276 : (v276 = 1 ↔ sv v51 < sv v273) := e_plt h_v51 h_v273 (of_decide_eq_true rfl)
  have h_v277 : R 1 0 0 1 v277 v277 := (r_sub hl (r_O hl) h_v276 (of_decide_eq_true rfl))
  have e_v277 : (v277 = 1 ↔ ¬v276 = 1) := e_not h_v276 (of_decide_eq_true rfl)
  have h_v278 : R 1 0 0 1 v278 v278 := (r_land hl h_v274 h_v277 (of_decide_eq_true rfl))
  have e_v278 : (v278 = 1 ↔ v274 = 1 ∧ v277 = 1) := e_land h_v274 h_v277 (of_decide_eq_true rfl)
  have h_v279 : R 1 0 0 1 v279 v279 := (r_land hl h_v274 h_v276 (of_decide_eq_true rfl))
  have e_v279 : (v279 = 1 ↔ v274 = 1 ∧ v276 = 1) := e_land h_v274 h_v276 (of_decide_eq_true rfl)
  have h_v280 : R 1 0 0 1 v280 v280 := (r_land hl h_v129 h_v279 (of_decide_eq_true rfl))
  have e_v280 : (v280 = 1 ↔ v129 = 1 ∧ v279 = 1) := e_land h_v129 h_v279 (of_decide_eq_true rfl)
  have h_v281 : R 1 0 0 1 v281 v281 := (r_sub hl (r_O hl) h_v280 (of_decide_eq_true rfl))
  have e_v281 : (v281 = 1 ↔ ¬v280 = 1) := e_not h_v280 (of_decide_eq_true rfl)
  have h_v282 : R 1 0 0 1 v282 v282 := (r_land hl h_v125 h_v279 (of_decide_eq_true rfl))
  have e_v282 : (v282 = 1 ↔ v125 = 1 ∧ v279 = 1) := e_land h_v125 h_v279 (of_decide_eq_true rfl)
  have h_v283 : R 1 0 0 1 v283 v283 := (r_lor hl h_v278 h_v282 (of_decide_eq_true rfl))
  have e_v283 : (v283 = 1 ↔ v278 = 1 ∨ v282 = 1) := e_lor h_v278 h_v282 (of_decide_eq_true rfl)
  have h_v284 : R 1 0 4611686018158952441 4611686018695823367 v284 v284 := (r_psel hl h_v283 h_v97 h_v90 (of_decide_eq_true rfl))
  have e_v284 : v284 = if v283 = 1 then v97 else v90 := e_psel h_v283 h_v97 h_v90 (of_decide_eq_true rfl)
  have h_v285 : R 1 0 0 1 v285 v285 := (r_land hl h_v129 h_v275 (of_decide_eq_true rfl))
  have e_v285 : (v285 = 1 ↔ v129 = 1 ∧ v275 = 1) := e_land h_v129 h_v275 (of_decide_eq_true rfl)
  have h_v286 : R 1 0 0 1 v286 v286 := (r_lor hl h_v128 h_v285 (of_decide_eq_true rfl))
  clear h_v274 h_v275 h_v276 h_v277 h_v280 h_v282 h_v283
  have e_v286 : (v286 = 1 ↔ v128 = 1 ∨ v285 = 1) := e_lor h_v128 h_v285 (of_decide_eq_true rfl)
  have h_v287 : R 1 0 4611686018427387900 4611686018695823367 v287 v287 := (r_psel hl h_v286 h_v273 h_v266 (of_decide_eq_true rfl))
  have e_v287 : v287 = if v286 = 1 then v273 else v266 := e_psel h_v286 h_v273 h_v266 (of_decide_eq_true rfl)
  have h_v288 : R 1 0 0 1 v288 v288 := (r_land hl h_v128 h_v279 (of_decide_eq_true rfl))
  have e_v288 : (v288 = 1 ↔ v128 = 1 ∧ v279 = 1) := e_land h_v128 h_v279 (of_decide_eq_true rfl)
  have h_v289 : R 1 0 0 1 v289 v289 := (r_lor hl h_v278 h_v288 (of_decide_eq_true rfl))
  have e_v289 : (v289 = 1 ↔ v278 = 1 ∨ v288 = 1) := e_lor h_v278 h_v288 (of_decide_eq_true rfl)
  have h_v290 : R 1 0 4611686018158952441 4611686018695823367 v290 v290 := (r_psel hl h_v289 h_v90 h_v97 (of_decide_eq_true rfl))
  have e_v290 : v290 = if v289 = 1 then v90 else v97 := e_psel h_v289 h_v90 h_v97 (of_decide_eq_true rfl)
  have h_v291 : R 1 0 0 1 v291 v291 := (r_land hl h_v129 h_v278 (of_decide_eq_true rfl))
  have e_v291 : (v291 = 1 ↔ v129 = 1 ∧ v278 = 1) := e_land h_v129 h_v278 (of_decide_eq_true rfl)
  have h_v292 : R 1 0 0 1 v292 v292 := (r_lor hl h_v128 h_v291 (of_decide_eq_true rfl))
  have e_v292 : (v292 = 1 ↔ v128 = 1 ∨ v291 = 1) := e_lor h_v128 h_v291 (of_decide_eq_true rfl)
  have h_v293 : R 1 0 4611686018427387900 4611686018695823367 v293 v293 := (r_psel hl h_v292 h_v266 h_v273 (of_decide_eq_true rfl))
  have e_v293 : v293 = if v292 = 1 then v266 else v273 := e_psel h_v292 h_v266 h_v273 (of_decide_eq_true rfl)
  have h_v294 : R 1 0 4539628420631363535 4683743616223412273 v294 v294 := (r_smx hl 29 h_v287 h_v284 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v294 : sv v294 = sv v287 * sv v284 := e_smx 29 h_v287 h_v284 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v295 : R 1 0 4611686018158952433 4611686018695823374 v295 v295 := (r_srdF hl h_v294 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v295 : sv v295 = sv v294 / 2 ^ 28 := e_srdF h_v294 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v296 : R 1 0 4539628420631363535 4683743616223412273 v296 v296 := (r_smx hl 29 h_v293 h_v290 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v296 : sv v296 = sv v293 * sv v290 := e_smx 29 h_v293 h_v290 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v297 : R 1 0 4611686018158952434 4611686018695823375 v297 v297 := (r_srdC hl h_v296 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v297 : sv v297 = -((-sv v296) / 2 ^ 28) := e_srdC h_v296 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v298 : R 1 0 0 1 v298 v298 := (r_plt hl h_v51 h_v295 (of_decide_eq_true rfl))
  have e_v298 : (v298 = 1 ↔ sv v51 < sv v295) := e_plt h_v51 h_v295 (of_decide_eq_true rfl)
  clear h_v266 h_v273 h_v278 h_v279 h_v284 h_v285 h_v286 h_v287 h_v288 h_v289 h_v290 h_v291 h_v292 h_v293 h_v294 h_v296
  have h_v299 : R 1 0 0 1 v299 v299 := (r_sub hl (r_O hl) h_v298 (of_decide_eq_true rfl))
  have e_v299 : (v299 = 1 ↔ ¬v298 = 1) := e_not h_v298 (of_decide_eq_true rfl)
  have h_v302 : R 1 0 0 1 v302 v302 := (r_plt hl h_v262 h_v51 (of_decide_eq_true rfl))
  have e_v302 : (v302 = 1 ↔ sv v262 < sv v51) := e_plt h_v262 h_v51 (of_decide_eq_true rfl)
  have h_v303 : R 1 0 4611686018158952433 4611686018695823375 v303 v303 := (r_psel hl h_v302 h_v297 h_v295 (of_decide_eq_true rfl))
  have e_v303 : v303 = if v302 = 1 then v297 else v295 := e_psel h_v302 h_v297 h_v295 (of_decide_eq_true rfl)
  have h_v345 : R 1 0 4611686018158952441 4611686018695823359 v345 v345 := (r_sub hl (r_add hl h_v51 h_OFFr (of_decide_eq_true rfl)) h_v262 (of_decide_eq_true rfl))
  have e_v345 : sv v345 = sv v51 - sv v262 := e_sub h_v51 h_v262 (of_decide_eq_true rfl)
  have h_v346 : R 1 0 4611686018158952441 4611686018695823367 v346 v346 := (r_psel hl h_v302 h_v345 h_v262 (of_decide_eq_true rfl))
  have e_v346 : v346 = if v302 = 1 then v345 else v262 := e_psel h_v302 h_v345 h_v262 (of_decide_eq_true rfl)
  have h_v347 : R 1 0 4611686018427387904 4611686019501129727 v347 v347 := (r1_hxa hb_H0 0 (of_decide_eq_true rfl))
  have e_v347 : sv v347 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 0 (of_decide_eq_true rfl)
  have h_t347_1 : R 1 0 4611686018427387904 4611686018695823363 t347.1 t347.1 := r_sc1 hl h_v347 (of_decide_eq_true rfl)
  have h_t347_2 : R 1 0 4611686018158952445 4611686018695823363 t347.2 t347.2 := r_sc2 hl h_v347 (of_decide_eq_true rfl)
  have e_t347_1 : sv t347.1 = (sc28pS (scArg v347)).1 := e_sc1 h_v347 (of_decide_eq_true rfl)
  have e_t347_2 : sv t347.2 = (sc28pS (scArg v347)).2 := e_sc2 h_v347 (of_decide_eq_true rfl)
  have h_v349 : R 1 0 4611686018158952441 4611686018695823359 v349 v349 := (r_sub hl (r_add hl h_v18 h_t347_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v349 : sv v349 = sv v18 + sv t347.2 := e_add h_v18 h_t347_2 (of_decide_eq_true rfl)
  have h_v350 : R 1 0 0 1 v350 v350 := (r_plt hl h_v349 h_v85 (of_decide_eq_true rfl))
  have e_v350 : (v350 = 1 ↔ sv v349 < sv v85) := e_plt h_v349 h_v85 (of_decide_eq_true rfl)
  have h_v351 : R 1 0 4611686018158952441 4611686018695823359 v351 v351 := (r_psel hl h_v350 h_v85 h_v349 (of_decide_eq_true rfl))
  have e_v351 : v351 = if v350 = 1 then v85 else v349 := e_psel h_v350 h_v85 h_v349 (of_decide_eq_true rfl)
  have h_v352 : R 1 0 4611686018158952449 4611686018695823367 v352 v352 := (r_sub hl (r_add hl h_v21 h_t347_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v352 : sv v352 = sv v21 + sv t347.2 := e_add h_v21 h_t347_2 (of_decide_eq_true rfl)
  have h_v353 : R 1 0 0 1 v353 v353 := (r_plt hl h_v352 h_v23 (of_decide_eq_true rfl))
  clear h_v262 h_v295 h_v297 h_v298 h_v345 h_t347_2 h_v349 h_v350
  have e_v353 : (v353 = 1 ↔ sv v352 < sv v23) := e_plt h_v352 h_v23 (of_decide_eq_true rfl)
  have h_v354 : R 1 0 4611686018158952449 4611686018695823367 v354 v354 := (r_psel hl h_v353 h_v352 h_v23 (of_decide_eq_true rfl))
  have e_v354 : v354 = if v353 = 1 then v352 else v23 := e_psel h_v353 h_v352 h_v23 (of_decide_eq_true rfl)
  have h_v356 : R 1 0 4611686018427387908 4611686018695823367 v356 v356 := (r_sub hl (r_add hl h_v21 h_t347_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v356 : sv v356 = sv v21 + sv t347.1 := e_add h_v21 h_t347_1 (of_decide_eq_true rfl)
  have h_v357 : R 1 0 0 1 v357 v357 := (r_plt hl h_v356 h_v23 (of_decide_eq_true rfl))
  have e_v357 : (v357 = 1 ↔ sv v356 < sv v23) := e_plt h_v356 h_v23 (of_decide_eq_true rfl)
  have h_v358 : R 1 0 4611686018427387908 4611686018695823367 v358 v358 := (r_psel hl h_v357 h_v356 h_v23 (of_decide_eq_true rfl))
  have e_v358 : v358 = if v357 = 1 then v356 else v23 := e_psel h_v357 h_v356 h_v23 (of_decide_eq_true rfl)
  have h_v359 : R 1 0 4611686018427387900 4611686018695823359 v359 v359 := (r_sub hl (r_add hl h_v18 h_t347_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v359 : sv v359 = sv v18 + sv t347.1 := e_add h_v18 h_t347_1 (of_decide_eq_true rfl)
  have h_v360 : R 1 0 4611686018158952441 4611686018695823367 v360 v360 := (r_psel hl h_v302 h_v351 h_v354 (of_decide_eq_true rfl))
  have e_v360 : v360 = if v302 = 1 then v351 else v354 := e_psel h_v302 h_v351 h_v354 (of_decide_eq_true rfl)
  have h_v361 : R 1 0 4611686018427387900 4611686018695823367 v361 v361 := (r_psel hl h_v302 h_v358 h_v359 (of_decide_eq_true rfl))
  have e_v361 : v361 = if v302 = 1 then v358 else v359 := e_psel h_v302 h_v358 h_v359 (of_decide_eq_true rfl)
  have h_v362 : R 1 0 4539628418483879831 4683743618370895977 v362 v362 := (r_smx hl 29 h_v303 h_v361 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v362 : sv v362 = sv v303 * sv v361 := e_smx 29 h_v303 h_v361 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v363 : R 1 0 4539628420631363535 4683743616223412273 v363 v363 := (r_smx hl 29 h_v360 h_v346 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v363 : sv v363 = sv v360 * sv v346 := e_smx 29 h_v360 h_v346 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v364 : R 1 0 0 1 v364 v364 := (r_plt hl h_v363 h_v362 (of_decide_eq_true rfl))
  have e_v364 : (v364 = 1 ↔ sv v363 < sv v362) := e_plt h_v363 h_v362 (of_decide_eq_true rfl)
  have h_v365 : R 1 0 0 1 v365 v365 := (r_sub hl (r_O hl) h_v364 (of_decide_eq_true rfl))
  have e_v365 : (v365 = 1 ↔ ¬v364 = 1) := e_not h_v364 (of_decide_eq_true rfl)
  have h_v366 : R 1 0 0 1 v366 v366 := (r_plt hl h_v362 h_v363 (of_decide_eq_true rfl))
  have e_v366 : (v366 = 1 ↔ sv v362 < sv v363) := e_plt h_v362 h_v363 (of_decide_eq_true rfl)
  clear h_v303 h_v346 h_t347_1 h_v352 h_v353 h_v354 h_v356 h_v357 h_v358 h_v359 h_v360 h_v361 h_v362 h_v363 h_v364
  have h_v367 : R 1 0 0 1 v367 v367 := (r_sub hl (r_O hl) h_v366 (of_decide_eq_true rfl))
  have e_v367 : (v367 = 1 ↔ ¬v366 = 1) := e_not h_v366 (of_decide_eq_true rfl)
  have h_v368 : R 1 0 0 1 v368 v368 := (r_plt hl h_v51 h_v347 (of_decide_eq_true rfl))
  have e_v368 : (v368 = 1 ↔ sv v51 < sv v347) := e_plt h_v51 h_v347 (of_decide_eq_true rfl)
  have h_v369 : R 1 0 0 1 v369 v369 := (r_sub hl (r_O hl) h_v368 (of_decide_eq_true rfl))
  have e_v369 : (v369 = 1 ↔ ¬v368 = 1) := e_not h_v368 (of_decide_eq_true rfl)
  have h_v370 : R 1 0 0 1 v370 v370 := (r_plt hl h_v186 h_v347 (of_decide_eq_true rfl))
  have e_v370 : (v370 = 1 ↔ sv v186 < sv v347) := e_plt h_v186 h_v347 (of_decide_eq_true rfl)
  have h_v371 : R 1 0 0 1 v371 v371 := (r_sub hl (r_O hl) h_v370 (of_decide_eq_true rfl))
  have e_v371 : (v371 = 1 ↔ ¬v370 = 1) := e_not h_v370 (of_decide_eq_true rfl)
  have h_v372 : R 1 0 0 1 v372 v372 := (r_plt hl h_v8 h_v351 (of_decide_eq_true rfl))
  have e_v372 : (v372 = 1 ↔ sv v8 < sv v351) := e_plt h_v8 h_v351 (of_decide_eq_true rfl)
  have h_v373 : R 1 0 0 1 v373 v373 := (r_land hl h_v365 h_v372 (of_decide_eq_true rfl))
  have e_v373 : (v373 = 1 ↔ v365 = 1 ∧ v372 = 1) := e_land h_v365 h_v372 (of_decide_eq_true rfl)
  have h_v374 : R 1 0 0 1 v374 v374 := (r_land hl h_v371 h_v373 (of_decide_eq_true rfl))
  have e_v374 : (v374 = 1 ↔ v371 = 1 ∧ v373 = 1) := e_land h_v371 h_v373 (of_decide_eq_true rfl)
  have h_v375 : R 1 0 0 1 v375 v375 := (r_lor hl h_v369 h_v374 (of_decide_eq_true rfl))
  have e_v375 : (v375 = 1 ↔ v369 = 1 ∨ v374 = 1) := e_lor h_v369 h_v374 (of_decide_eq_true rfl)
  have h_v376 : R 1 0 0 1 v376 v376 := (r_plt hl h_v347 h_v193 (of_decide_eq_true rfl))
  have e_v376 : (v376 = 1 ↔ sv v347 < sv v193) := e_plt h_v347 h_v193 (of_decide_eq_true rfl)
  have h_v377 : R 1 0 0 1 v377 v377 := (r_sub hl (r_O hl) h_v376 (of_decide_eq_true rfl))
  have e_v377 : (v377 = 1 ↔ ¬v376 = 1) := e_not h_v376 (of_decide_eq_true rfl)
  have h_v378 : R 1 0 0 1 v378 v378 := (r_lor hl h_v367 h_v377 (of_decide_eq_true rfl))
  have e_v378 : (v378 = 1 ↔ v367 = 1 ∨ v377 = 1) := e_lor h_v367 h_v377 (of_decide_eq_true rfl)
  have h_v379 : R 1 0 0 1 v379 v379 := (r_land hl h_v302 h_v375 (of_decide_eq_true rfl))
  clear h_v351 h_v365 h_v366 h_v367 h_v368 h_v369 h_v370 h_v371 h_v372 h_v373 h_v374 h_v376 h_v377
  have e_v379 : (v379 = 1 ↔ v302 = 1 ∧ v375 = 1) := e_land h_v302 h_v375 (of_decide_eq_true rfl)
  have h_v380 : R 1 0 0 1 v380 v380 := (r_sub hl (r_O hl) h_v302 (of_decide_eq_true rfl))
  have e_v380 : (v380 = 1 ↔ ¬v302 = 1) := e_not h_v302 (of_decide_eq_true rfl)
  have h_v381 : R 1 0 0 1 v381 v381 := (r_land hl h_v378 h_v380 (of_decide_eq_true rfl))
  have e_v381 : (v381 = 1 ↔ v378 = 1 ∧ v380 = 1) := e_land h_v378 h_v380 (of_decide_eq_true rfl)
  have h_v382 : R 1 0 0 1 v382 v382 := (r_lor hl h_v379 h_v381 (of_decide_eq_true rfl))
  have e_v382 : (v382 = 1 ↔ v379 = 1 ∨ v381 = 1) := e_lor h_v379 h_v381 (of_decide_eq_true rfl)
  have h_v383 : R 1 0 4611686017353646081 4611686018427387904 v383 v383 := (r_sub hl (r_add hl h_v51 h_OFFr (of_decide_eq_true rfl)) h_v347 (of_decide_eq_true rfl))
  have e_v383 : sv v383 = sv v51 - sv v347 := e_sub h_v51 h_v347 (of_decide_eq_true rfl)
  have h_v384 : R 1 0 4611686017353646081 4611686019501129727 v384 v384 := (r_psel hl h_v302 h_v383 h_v347 (of_decide_eq_true rfl))
  have e_v384 : v384 = if v302 = 1 then v383 else v347 := e_psel h_v302 h_v383 h_v347 (of_decide_eq_true rfl)
  have h_v385 : R 1 0 4611686017353646081 4611686019501129727 v385 v385 := (r_psel hl h_v382 h_v384 h_v193 (of_decide_eq_true rfl))
  have e_v385 : v385 = if v382 = 1 then v384 else v193 := e_psel h_v382 h_v384 h_v193 (of_decide_eq_true rfl)
  have h_v387 : R 1 0 4611686017353646081 4611686019501129727 v387 v387 := (r_psel hl h_v299 h_v193 h_v385 (of_decide_eq_true rfl))
  have e_v387 : v387 = if v299 = 1 then v193 else v385 := e_psel h_v299 h_v193 h_v385 (of_decide_eq_true rfl)
  have h_v388 : R 1 0 4611686018427387904 4611686052787126264 v388 v388 := (r_add hl (r_pshr1 hl h_v4) h_H61r (of_decide_eq_true rfl))
  have e_v388 : sv v388 = sv v4 / 2 := e_halfF h_v4
  have h_v389 : R 1 0 4611686018427387904 4611686052787126264 v389 v389 := (r_add hl (r_pshr1 hl (r_add hl h_v5 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v389 : sv v389 = (sv v5 + 1) / 2 := e_halfC h_v5 (of_decide_eq_true rfl)
  have h_v390 : R 1 0 0 1 v390 v390 := (r_plt hl h_v8 h_v388 (of_decide_eq_true rfl))
  have e_v390 : (v390 = 1 ↔ sv v8 < sv v388) := e_plt h_v8 h_v388 (of_decide_eq_true rfl)
  have h_v391 : R 1 0 0 1 v391 v391 := (r_plt hl h_v10 h_v389 (of_decide_eq_true rfl))
  have e_v391 : (v391 = 1 ↔ sv v10 < sv v389) := e_plt h_v10 h_v389 (of_decide_eq_true rfl)
  have h_v392 : R 1 0 0 1 v392 v392 := (r_sub hl (r_O hl) h_v391 (of_decide_eq_true rfl))
  have e_v392 : (v392 = 1 ↔ ¬v391 = 1) := e_not h_v391 (of_decide_eq_true rfl)
  clear h_v299 h_v302 h_v347 h_v375 h_v378 h_v379 h_v380 h_v381 h_v382 h_v383 h_v384 h_v385 h_v391
  have h_v393 : R 1 0 0 1 v393 v393 := (r_land hl h_v390 h_v392 (of_decide_eq_true rfl))
  have e_v393 : (v393 = 1 ↔ v390 = 1 ∧ v392 = 1) := e_land h_v390 h_v392 (of_decide_eq_true rfl)
  have h_t388_1 : R 1 0 4611686018427387904 4611686018695823363 t388.1 t388.1 := r_sc1 hl h_v388 (of_decide_eq_true rfl)
  have h_t388_2 : R 1 0 4611686018158952445 4611686018695823363 t388.2 t388.2 := r_sc2 hl h_v388 (of_decide_eq_true rfl)
  have e_t388_1 : sv t388.1 = (sc28pS (scArg v388)).1 := e_sc1 h_v388 (of_decide_eq_true rfl)
  have e_t388_2 : sv t388.2 = (sc28pS (scArg v388)).2 := e_sc2 h_v388 (of_decide_eq_true rfl)
  have h_t389_1 : R 1 0 4611686018427387904 4611686018695823363 t389.1 t389.1 := r_sc1 hl h_v389 (of_decide_eq_true rfl)
  have h_t389_2 : R 1 0 4611686018158952445 4611686018695823363 t389.2 t389.2 := r_sc2 hl h_v389 (of_decide_eq_true rfl)
  have e_t389_1 : sv t389.1 = (sc28pS (scArg v389)).1 := e_sc1 h_v389 (of_decide_eq_true rfl)
  have e_t389_2 : sv t389.2 = (sc28pS (scArg v389)).2 := e_sc2 h_v389 (of_decide_eq_true rfl)
  have h_v396 : R 1 0 0 1 v396 v396 := (r_plt hl h_t388_1 h_t389_1 (of_decide_eq_true rfl))
  have e_v396 : (v396 = 1 ↔ sv t388.1 < sv t389.1) := e_plt h_t388_1 h_t389_1 (of_decide_eq_true rfl)
  have h_v397 : R 1 0 4611686018427387904 4611686018695823363 v397 v397 := (r_psel hl h_v396 h_t388_1 h_t389_1 (of_decide_eq_true rfl))
  have e_v397 : v397 = if v396 = 1 then t388.1 else t389.1 := e_psel h_v396 h_t388_1 h_t389_1 (of_decide_eq_true rfl)
  have h_v398 : R 1 0 4611686018427387900 4611686018695823359 v398 v398 := (r_sub hl (r_add hl h_v18 h_v397 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v398 : sv v398 = sv v18 + sv v397 := e_add h_v18 h_v397 (of_decide_eq_true rfl)
  have h_v399 : R 1 0 4611686018427387904 4611686018695823363 v399 v399 := (r_psel hl h_v396 h_t389_1 h_t388_1 (of_decide_eq_true rfl))
  have e_v399 : v399 = if v396 = 1 then t389.1 else t388.1 := e_psel h_v396 h_t389_1 h_t388_1 (of_decide_eq_true rfl)
  have h_v400 : R 1 0 4611686018427387908 4611686018695823367 v400 v400 := (r_sub hl (r_add hl h_v21 h_v399 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v400 : sv v400 = sv v21 + sv v399 := e_add h_v21 h_v399 (of_decide_eq_true rfl)
  have h_v401 : R 1 0 0 1 v401 v401 := (r_plt hl h_v400 h_v23 (of_decide_eq_true rfl))
  have e_v401 : (v401 = 1 ↔ sv v400 < sv v23) := e_plt h_v400 h_v23 (of_decide_eq_true rfl)
  have h_v402 : R 1 0 4611686018427387908 4611686018695823367 v402 v402 := (r_psel hl h_v401 h_v400 h_v23 (of_decide_eq_true rfl))
  have e_v402 : v402 = if v401 = 1 then v400 else v23 := e_psel h_v401 h_v400 h_v23 (of_decide_eq_true rfl)
  have h_v403 : R 1 0 0 1 v403 v403 := (r_plt hl h_v388 h_v26 (of_decide_eq_true rfl))
  clear h_t389_2 e_t389_2 h_v396 h_v397 h_v399 h_v400 h_v401
  have e_v403 : (v403 = 1 ↔ sv v388 < sv v26) := e_plt h_v388 h_v26 (of_decide_eq_true rfl)
  have h_v404 : R 1 0 0 1 v404 v404 := (r_plt hl h_v28 h_v389 (of_decide_eq_true rfl))
  have e_v404 : (v404 = 1 ↔ sv v28 < sv v389) := e_plt h_v28 h_v389 (of_decide_eq_true rfl)
  have h_v405 : R 1 0 0 1 v405 v405 := (r_land hl h_v403 h_v404 (of_decide_eq_true rfl))
  have e_v405 : (v405 = 1 ↔ v403 = 1 ∧ v404 = 1) := e_land h_v403 h_v404 (of_decide_eq_true rfl)
  have h_v406 : R 1 0 4611686018427387908 4611686018695823367 v406 v406 := (r_psel hl h_v405 h_v23 h_v402 (of_decide_eq_true rfl))
  have e_v406 : v406 = if v405 = 1 then v23 else v402 := e_psel h_v405 h_v23 h_v402 (of_decide_eq_true rfl)
  have h_v407 : R 1 0 0 1 v407 v407 := (r_plt hl h_v398 h_v51 (of_decide_eq_true rfl))
  have e_v407 : (v407 = 1 ↔ sv v398 < sv v51) := e_plt h_v398 h_v51 (of_decide_eq_true rfl)
  have h_v408 : R 1 0 0 1 v408 v408 := (r_sub hl (r_O hl) h_v407 (of_decide_eq_true rfl))
  have e_v408 : (v408 = 1 ↔ ¬v407 = 1) := e_not h_v407 (of_decide_eq_true rfl)
  have h_v409 : R 1 0 0 1 v409 v409 := (r_plt hl h_v51 h_v406 (of_decide_eq_true rfl))
  have e_v409 : (v409 = 1 ↔ sv v51 < sv v406) := e_plt h_v51 h_v406 (of_decide_eq_true rfl)
  have h_v410 : R 1 0 0 1 v410 v410 := (r_sub hl (r_O hl) h_v409 (of_decide_eq_true rfl))
  have e_v410 : (v410 = 1 ↔ ¬v409 = 1) := e_not h_v409 (of_decide_eq_true rfl)
  have h_v411 : R 1 0 0 1 v411 v411 := (r_land hl h_v407 h_v410 (of_decide_eq_true rfl))
  have e_v411 : (v411 = 1 ↔ v407 = 1 ∧ v410 = 1) := e_land h_v407 h_v410 (of_decide_eq_true rfl)
  have h_v412 : R 1 0 0 1 v412 v412 := (r_land hl h_v407 h_v409 (of_decide_eq_true rfl))
  have e_v412 : (v412 = 1 ↔ v407 = 1 ∧ v409 = 1) := e_land h_v407 h_v409 (of_decide_eq_true rfl)
  have h_v413 : R 1 0 0 1 v413 v413 := (r_land hl h_v57 h_v412 (of_decide_eq_true rfl))
  have e_v413 : (v413 = 1 ↔ v57 = 1 ∧ v412 = 1) := e_land h_v57 h_v412 (of_decide_eq_true rfl)
  have h_v414 : R 1 0 0 1 v414 v414 := (r_sub hl (r_O hl) h_v413 (of_decide_eq_true rfl))
  have e_v414 : (v414 = 1 ↔ ¬v413 = 1) := e_not h_v413 (of_decide_eq_true rfl)
  have h_v415 : R 1 0 0 1 v415 v415 := (r_land hl h_v53 h_v412 (of_decide_eq_true rfl))
  have e_v415 : (v415 = 1 ↔ v53 = 1 ∧ v412 = 1) := e_land h_v53 h_v412 (of_decide_eq_true rfl)
  clear h_v53 h_v389 h_v402 h_v405 h_v407 h_v409 h_v410 h_v413
  have h_v416 : R 1 0 0 1 v416 v416 := (r_lor hl h_v411 h_v415 (of_decide_eq_true rfl))
  have e_v416 : (v416 = 1 ↔ v411 = 1 ∨ v415 = 1) := e_lor h_v411 h_v415 (of_decide_eq_true rfl)
  have h_v417 : R 1 0 4611686018427387900 4611686018695823367 v417 v417 := (r_psel hl h_v416 h_v31 h_v19 (of_decide_eq_true rfl))
  have e_v417 : v417 = if v416 = 1 then v31 else v19 := e_psel h_v416 h_v31 h_v19 (of_decide_eq_true rfl)
  have h_v418 : R 1 0 0 1 v418 v418 := (r_land hl h_v57 h_v408 (of_decide_eq_true rfl))
  have e_v418 : (v418 = 1 ↔ v57 = 1 ∧ v408 = 1) := e_land h_v57 h_v408 (of_decide_eq_true rfl)
  have h_v419 : R 1 0 0 1 v419 v419 := (r_lor hl h_v56 h_v418 (of_decide_eq_true rfl))
  have e_v419 : (v419 = 1 ↔ v56 = 1 ∨ v418 = 1) := e_lor h_v56 h_v418 (of_decide_eq_true rfl)
  have h_v420 : R 1 0 4611686018427387900 4611686018695823367 v420 v420 := (r_psel hl h_v419 h_v406 h_v398 (of_decide_eq_true rfl))
  have e_v420 : v420 = if v419 = 1 then v406 else v398 := e_psel h_v419 h_v406 h_v398 (of_decide_eq_true rfl)
  have h_v421 : R 1 0 0 1 v421 v421 := (r_land hl h_v56 h_v412 (of_decide_eq_true rfl))
  have e_v421 : (v421 = 1 ↔ v56 = 1 ∧ v412 = 1) := e_land h_v56 h_v412 (of_decide_eq_true rfl)
  have h_v422 : R 1 0 0 1 v422 v422 := (r_lor hl h_v411 h_v421 (of_decide_eq_true rfl))
  have e_v422 : (v422 = 1 ↔ v411 = 1 ∨ v421 = 1) := e_lor h_v411 h_v421 (of_decide_eq_true rfl)
  have h_v423 : R 1 0 4611686018427387900 4611686018695823367 v423 v423 := (r_psel hl h_v422 h_v19 h_v31 (of_decide_eq_true rfl))
  have e_v423 : v423 = if v422 = 1 then v19 else v31 := e_psel h_v422 h_v19 h_v31 (of_decide_eq_true rfl)
  have h_v424 : R 1 0 0 1 v424 v424 := (r_land hl h_v57 h_v411 (of_decide_eq_true rfl))
  have e_v424 : (v424 = 1 ↔ v57 = 1 ∧ v411 = 1) := e_land h_v57 h_v411 (of_decide_eq_true rfl)
  have h_v425 : R 1 0 0 1 v425 v425 := (r_lor hl h_v56 h_v424 (of_decide_eq_true rfl))
  have e_v425 : (v425 = 1 ↔ v56 = 1 ∨ v424 = 1) := e_lor h_v56 h_v424 (of_decide_eq_true rfl)
  have h_v426 : R 1 0 4611686018427387900 4611686018695823367 v426 v426 := (r_psel hl h_v425 h_v398 h_v406 (of_decide_eq_true rfl))
  have e_v426 : v426 = if v425 = 1 then v398 else v406 := e_psel h_v425 h_v398 h_v406 (of_decide_eq_true rfl)
  have h_v427 : R 1 0 4611686017353646052 4683743616223412273 v427 v427 := (r_smx hl 29 h_v420 h_v417 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v427 : sv v427 = sv v420 * sv v417 := e_smx 29 h_v420 h_v417 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v428 : R 1 0 4611686018427387899 4611686018695823374 v428 v428 := (r_srdF hl h_v427 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  clear h_v19 h_v31 h_v56 h_v57 h_v398 h_v406 h_v408 h_v411 h_v412 h_v415 h_v416 h_v417 h_v418 h_v419 h_v420 h_v421 h_v422 h_v424 h_v425
  have e_v428 : sv v428 = sv v427 / 2 ^ 28 := e_srdF h_v427 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v429 : R 1 0 4611686017353646052 4683743616223412273 v429 v429 := (r_smx hl 29 h_v426 h_v423 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v429 : sv v429 = sv v426 * sv v423 := e_smx 29 h_v426 h_v423 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v430 : R 1 0 4611686018427387900 4611686018695823375 v430 v430 := (r_srdC hl h_v429 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v430 : sv v430 = -((-sv v429) / 2 ^ 28) := e_srdC h_v429 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v431 : R 1 0 0 1 v431 v431 := (r_plt hl h_v8 h_v428 (of_decide_eq_true rfl))
  have e_v431 : (v431 = 1 ↔ sv v8 < sv v428) := e_plt h_v8 h_v428 (of_decide_eq_true rfl)
  have h_v432 : R 1 0 4611686018427387904 4611686052787126264 v432 v432 := (r_add hl (r_pshr1 hl h_v5) h_H61r (of_decide_eq_true rfl))
  have e_v432 : sv v432 = sv v5 / 2 := e_halfF h_v5
  have h_v433 : R 1 0 0 1 v433 v433 := (r_plt hl h_v8 h_v432 (of_decide_eq_true rfl))
  have e_v433 : (v433 = 1 ↔ sv v8 < sv v432) := e_plt h_v8 h_v432 (of_decide_eq_true rfl)
  have h_v434 : R 1 0 0 1 v434 v434 := (r_land hl h_v392 h_v433 (of_decide_eq_true rfl))
  have e_v434 : (v434 = 1 ↔ v392 = 1 ∧ v433 = 1) := e_land h_v392 h_v433 (of_decide_eq_true rfl)
  have h_t432_1 : R 1 0 4611686018427387904 4611686018695823363 t432.1 t432.1 := r_sc1 hl h_v432 (of_decide_eq_true rfl)
  have h_t432_2 : R 1 0 4611686018158952445 4611686018695823363 t432.2 t432.2 := r_sc2 hl h_v432 (of_decide_eq_true rfl)
  have e_t432_1 : sv t432.1 = (sc28pS (scArg v432)).1 := e_sc1 h_v432 (of_decide_eq_true rfl)
  have e_t432_2 : sv t432.2 = (sc28pS (scArg v432)).2 := e_sc2 h_v432 (of_decide_eq_true rfl)
  have h_v448 : R 1 0 0 1 v448 v448 := (r_plt hl h_t432_1 h_t389_1 (of_decide_eq_true rfl))
  have e_v448 : (v448 = 1 ↔ sv t432.1 < sv t389.1) := e_plt h_t432_1 h_t389_1 (of_decide_eq_true rfl)
  have h_v449 : R 1 0 4611686018427387904 4611686018695823363 v449 v449 := (r_psel hl h_v448 h_t432_1 h_t389_1 (of_decide_eq_true rfl))
  have e_v449 : v449 = if v448 = 1 then t432.1 else t389.1 := e_psel h_v448 h_t432_1 h_t389_1 (of_decide_eq_true rfl)
  have h_v450 : R 1 0 4611686018427387900 4611686018695823359 v450 v450 := (r_sub hl (r_add hl h_v18 h_v449 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v450 : sv v450 = sv v18 + sv v449 := e_add h_v18 h_v449 (of_decide_eq_true rfl)
  have h_v451 : R 1 0 4611686018427387904 4611686018695823363 v451 v451 := (r_psel hl h_v448 h_t389_1 h_t432_1 (of_decide_eq_true rfl))
  have e_v451 : v451 = if v448 = 1 then t389.1 else t432.1 := e_psel h_v448 h_t389_1 h_t432_1 (of_decide_eq_true rfl)
  clear h_v5 h_v392 h_t389_1 h_v423 h_v426 h_v427 h_v429 h_v433 h_t432_1 h_t432_2 e_t432_2 h_v448 h_v449
  have h_v452 : R 1 0 4611686018427387908 4611686018695823367 v452 v452 := (r_sub hl (r_add hl h_v21 h_v451 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v452 : sv v452 = sv v21 + sv v451 := e_add h_v21 h_v451 (of_decide_eq_true rfl)
  have h_v453 : R 1 0 0 1 v453 v453 := (r_plt hl h_v452 h_v23 (of_decide_eq_true rfl))
  have e_v453 : (v453 = 1 ↔ sv v452 < sv v23) := e_plt h_v452 h_v23 (of_decide_eq_true rfl)
  have h_v454 : R 1 0 4611686018427387908 4611686018695823367 v454 v454 := (r_psel hl h_v453 h_v452 h_v23 (of_decide_eq_true rfl))
  have e_v454 : v454 = if v453 = 1 then v452 else v23 := e_psel h_v453 h_v452 h_v23 (of_decide_eq_true rfl)
  have h_v455 : R 1 0 0 1 v455 v455 := (r_plt hl h_v432 h_v26 (of_decide_eq_true rfl))
  have e_v455 : (v455 = 1 ↔ sv v432 < sv v26) := e_plt h_v432 h_v26 (of_decide_eq_true rfl)
  have h_v456 : R 1 0 0 1 v456 v456 := (r_land hl h_v404 h_v455 (of_decide_eq_true rfl))
  have e_v456 : (v456 = 1 ↔ v404 = 1 ∧ v455 = 1) := e_land h_v404 h_v455 (of_decide_eq_true rfl)
  have h_v457 : R 1 0 4611686018427387908 4611686018695823367 v457 v457 := (r_psel hl h_v456 h_v23 h_v454 (of_decide_eq_true rfl))
  have e_v457 : v457 = if v456 = 1 then v23 else v454 := e_psel h_v456 h_v23 h_v454 (of_decide_eq_true rfl)
  have h_v458 : R 1 0 0 1 v458 v458 := (r_plt hl h_v450 h_v51 (of_decide_eq_true rfl))
  have e_v458 : (v458 = 1 ↔ sv v450 < sv v51) := e_plt h_v450 h_v51 (of_decide_eq_true rfl)
  have h_v460 : R 1 0 0 1 v460 v460 := (r_plt hl h_v51 h_v457 (of_decide_eq_true rfl))
  have e_v460 : (v460 = 1 ↔ sv v51 < sv v457) := e_plt h_v51 h_v457 (of_decide_eq_true rfl)
  have h_v463 : R 1 0 0 1 v463 v463 := (r_land hl h_v458 h_v460 (of_decide_eq_true rfl))
  have e_v463 : (v463 = 1 ↔ v458 = 1 ∧ v460 = 1) := e_land h_v458 h_v460 (of_decide_eq_true rfl)
  have h_v464 : R 1 0 0 1 v464 v464 := (r_land hl h_v129 h_v463 (of_decide_eq_true rfl))
  have e_v464 : (v464 = 1 ↔ v129 = 1 ∧ v463 = 1) := e_land h_v129 h_v463 (of_decide_eq_true rfl)
  have h_v465 : R 1 0 0 1 v465 v465 := (r_sub hl (r_O hl) h_v464 (of_decide_eq_true rfl))
  have e_v465 : (v465 = 1 ↔ ¬v464 = 1) := e_not h_v464 (of_decide_eq_true rfl)
  have h_v572 : R 1 0 4611686018427387904 4611686052787126264 v572 v572 := (r_add hl (r_pshr1 hl (r_add hl h_v4 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v572 : sv v572 = (sv v4 + 1) / 2 := e_halfC h_v4 (of_decide_eq_true rfl)
  have h_v573 : R 1 0 0 1 v573 v573 := (r_plt hl h_v10 h_v572 (of_decide_eq_true rfl))
  clear h_H61r h_v4 h_v26 h_v404 h_v432 h_v450 h_v451 h_v452 h_v453 h_v454 h_v455 h_v456 h_v457 h_v458 h_v460 h_v463 h_v464
  have e_v573 : (v573 = 1 ↔ sv v10 < sv v572) := e_plt h_v10 h_v572 (of_decide_eq_true rfl)
  have h_v574 : R 1 0 0 1 v574 v574 := (r_sub hl (r_O hl) h_v573 (of_decide_eq_true rfl))
  have e_v574 : (v574 = 1 ↔ ¬v573 = 1) := e_not h_v573 (of_decide_eq_true rfl)
  have h_v575 : R 1 0 0 1 v575 v575 := (r_land hl h_v390 h_v574 (of_decide_eq_true rfl))
  have e_v575 : (v575 = 1 ↔ v390 = 1 ∧ v574 = 1) := e_land h_v390 h_v574 (of_decide_eq_true rfl)
  have h_v583 : R 1 0 4611686018158952449 4611686018695823367 v583 v583 := (r_sub hl (r_add hl h_v21 h_t388_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v583 : sv v583 = sv v21 + sv t388.2 := e_add h_v21 h_t388_2 (of_decide_eq_true rfl)
  have h_v584 : R 1 0 0 1 v584 v584 := (r_plt hl h_v583 h_v23 (of_decide_eq_true rfl))
  have e_v584 : (v584 = 1 ↔ sv v583 < sv v23) := e_plt h_v583 h_v23 (of_decide_eq_true rfl)
  have h_v585 : R 1 0 4611686018158952449 4611686018695823367 v585 v585 := (r_psel hl h_v584 h_v583 h_v23 (of_decide_eq_true rfl))
  have e_v585 : v585 = if v584 = 1 then v583 else v23 := e_psel h_v584 h_v583 h_v23 (of_decide_eq_true rfl)
  have h_v586 : R 1 0 0 1 v586 v586 := (r_plt hl h_v388 h_v95 (of_decide_eq_true rfl))
  have e_v586 : (v586 = 1 ↔ sv v388 < sv v95) := e_plt h_v388 h_v95 (of_decide_eq_true rfl)
  have h_v587 : R 1 0 4611686018158952449 4611686018695823367 v587 v587 := (r_psel hl h_v586 h_v23 h_v585 (of_decide_eq_true rfl))
  have e_v587 : v587 = if v586 = 1 then v23 else v585 := e_psel h_v586 h_v23 h_v585 (of_decide_eq_true rfl)
  have h_t572_1 : R 1 0 4611686018427387904 4611686018695823363 t572.1 t572.1 := r_sc1 hl h_v572 (of_decide_eq_true rfl)
  have h_t572_2 : R 1 0 4611686018158952445 4611686018695823363 t572.2 t572.2 := r_sc2 hl h_v572 (of_decide_eq_true rfl)
  have e_t572_1 : sv t572.1 = (sc28pS (scArg v572)).1 := e_sc1 h_v572 (of_decide_eq_true rfl)
  have e_t572_2 : sv t572.2 = (sc28pS (scArg v572)).2 := e_sc2 h_v572 (of_decide_eq_true rfl)
  have h_v589 : R 1 0 0 1 v589 v589 := (r_plt hl h_t388_1 h_t572_1 (of_decide_eq_true rfl))
  have e_v589 : (v589 = 1 ↔ sv t388.1 < sv t572.1) := e_plt h_t388_1 h_t572_1 (of_decide_eq_true rfl)
  have h_v590 : R 1 0 4611686018427387904 4611686018695823363 v590 v590 := (r_psel hl h_v589 h_t388_1 h_t572_1 (of_decide_eq_true rfl))
  have e_v590 : v590 = if v589 = 1 then t388.1 else t572.1 := e_psel h_v589 h_t388_1 h_t572_1 (of_decide_eq_true rfl)
  have h_v591 : R 1 0 4611686018427387900 4611686018695823359 v591 v591 := (r_sub hl (r_add hl h_v18 h_v590 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v591 : sv v591 = sv v18 + sv v590 := e_add h_v18 h_v590 (of_decide_eq_true rfl)
  clear h_v388 h_v390 h_t388_2 h_v573 h_v574 h_v583 h_v584 h_v585 h_v586 h_t572_2 e_t572_2 h_v590
  have h_v592 : R 1 0 4611686018427387904 4611686018695823363 v592 v592 := (r_psel hl h_v589 h_t572_1 h_t388_1 (of_decide_eq_true rfl))
  have e_v592 : v592 = if v589 = 1 then t572.1 else t388.1 := e_psel h_v589 h_t572_1 h_t388_1 (of_decide_eq_true rfl)
  have h_v593 : R 1 0 4611686018427387908 4611686018695823367 v593 v593 := (r_sub hl (r_add hl h_v21 h_v592 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v593 : sv v593 = sv v21 + sv v592 := e_add h_v21 h_v592 (of_decide_eq_true rfl)
  have h_v594 : R 1 0 0 1 v594 v594 := (r_plt hl h_v593 h_v23 (of_decide_eq_true rfl))
  have e_v594 : (v594 = 1 ↔ sv v593 < sv v23) := e_plt h_v593 h_v23 (of_decide_eq_true rfl)
  have h_v595 : R 1 0 4611686018427387908 4611686018695823367 v595 v595 := (r_psel hl h_v594 h_v593 h_v23 (of_decide_eq_true rfl))
  have e_v595 : v595 = if v594 = 1 then v593 else v23 := e_psel h_v594 h_v593 h_v23 (of_decide_eq_true rfl)
  have h_v596 : R 1 0 0 1 v596 v596 := (r_plt hl h_v28 h_v572 (of_decide_eq_true rfl))
  have e_v596 : (v596 = 1 ↔ sv v28 < sv v572) := e_plt h_v28 h_v572 (of_decide_eq_true rfl)
  have h_v597 : R 1 0 0 1 v597 v597 := (r_land hl h_v403 h_v596 (of_decide_eq_true rfl))
  have e_v597 : (v597 = 1 ↔ v403 = 1 ∧ v596 = 1) := e_land h_v403 h_v596 (of_decide_eq_true rfl)
  have h_v598 : R 1 0 4611686018427387908 4611686018695823367 v598 v598 := (r_psel hl h_v597 h_v23 h_v595 (of_decide_eq_true rfl))
  have e_v598 : v598 = if v597 = 1 then v23 else v595 := e_psel h_v597 h_v23 h_v595 (of_decide_eq_true rfl)
  have h_v599 : R 1 0 0 1 v599 v599 := (r_plt hl h_v591 h_v51 (of_decide_eq_true rfl))
  have e_v599 : (v599 = 1 ↔ sv v591 < sv v51) := e_plt h_v591 h_v51 (of_decide_eq_true rfl)
  have h_v600 : R 1 0 0 1 v600 v600 := (r_sub hl (r_O hl) h_v599 (of_decide_eq_true rfl))
  have e_v600 : (v600 = 1 ↔ ¬v599 = 1) := e_not h_v599 (of_decide_eq_true rfl)
  have h_v601 : R 1 0 0 1 v601 v601 := (r_plt hl h_v51 h_v598 (of_decide_eq_true rfl))
  have e_v601 : (v601 = 1 ↔ sv v51 < sv v598) := e_plt h_v51 h_v598 (of_decide_eq_true rfl)
  have h_v602 : R 1 0 0 1 v602 v602 := (r_sub hl (r_O hl) h_v601 (of_decide_eq_true rfl))
  have e_v602 : (v602 = 1 ↔ ¬v601 = 1) := e_not h_v601 (of_decide_eq_true rfl)
  have h_v603 : R 1 0 0 1 v603 v603 := (r_land hl h_v599 h_v602 (of_decide_eq_true rfl))
  have e_v603 : (v603 = 1 ↔ v599 = 1 ∧ v602 = 1) := e_land h_v599 h_v602 (of_decide_eq_true rfl)
  have h_v604 : R 1 0 0 1 v604 v604 := (r_land hl h_v599 h_v601 (of_decide_eq_true rfl))
  clear h_v28 h_t388_1 h_v403 h_v572 h_t572_1 h_v589 h_v592 h_v593 h_v594 h_v595 h_v596 h_v597 h_v602
  have e_v604 : (v604 = 1 ↔ v599 = 1 ∧ v601 = 1) := e_land h_v599 h_v601 (of_decide_eq_true rfl)
  have h_v605 : R 1 0 0 1 v605 v605 := (r_land hl h_v129 h_v604 (of_decide_eq_true rfl))
  have e_v605 : (v605 = 1 ↔ v129 = 1 ∧ v604 = 1) := e_land h_v129 h_v604 (of_decide_eq_true rfl)
  have h_v606 : R 1 0 0 1 v606 v606 := (r_sub hl (r_O hl) h_v605 (of_decide_eq_true rfl))
  have e_v606 : (v606 = 1 ↔ ¬v605 = 1) := e_not h_v605 (of_decide_eq_true rfl)
  have h_v607 : R 1 0 0 1 v607 v607 := (r_land hl h_v125 h_v604 (of_decide_eq_true rfl))
  have e_v607 : (v607 = 1 ↔ v125 = 1 ∧ v604 = 1) := e_land h_v125 h_v604 (of_decide_eq_true rfl)
  have h_v608 : R 1 0 0 1 v608 v608 := (r_lor hl h_v603 h_v607 (of_decide_eq_true rfl))
  have e_v608 : (v608 = 1 ↔ v603 = 1 ∨ v607 = 1) := e_lor h_v603 h_v607 (of_decide_eq_true rfl)
  have h_v609 : R 1 0 4611686018158952441 4611686018695823367 v609 v609 := (r_psel hl h_v608 h_v97 h_v90 (of_decide_eq_true rfl))
  have e_v609 : v609 = if v608 = 1 then v97 else v90 := e_psel h_v608 h_v97 h_v90 (of_decide_eq_true rfl)
  have h_v610 : R 1 0 0 1 v610 v610 := (r_land hl h_v129 h_v600 (of_decide_eq_true rfl))
  have e_v610 : (v610 = 1 ↔ v129 = 1 ∧ v600 = 1) := e_land h_v129 h_v600 (of_decide_eq_true rfl)
  have h_v611 : R 1 0 0 1 v611 v611 := (r_lor hl h_v128 h_v610 (of_decide_eq_true rfl))
  have e_v611 : (v611 = 1 ↔ v128 = 1 ∨ v610 = 1) := e_lor h_v128 h_v610 (of_decide_eq_true rfl)
  have h_v612 : R 1 0 4611686018427387900 4611686018695823367 v612 v612 := (r_psel hl h_v611 h_v598 h_v591 (of_decide_eq_true rfl))
  have e_v612 : v612 = if v611 = 1 then v598 else v591 := e_psel h_v611 h_v598 h_v591 (of_decide_eq_true rfl)
  have h_v613 : R 1 0 0 1 v613 v613 := (r_land hl h_v128 h_v604 (of_decide_eq_true rfl))
  have e_v613 : (v613 = 1 ↔ v128 = 1 ∧ v604 = 1) := e_land h_v128 h_v604 (of_decide_eq_true rfl)
  have h_v614 : R 1 0 0 1 v614 v614 := (r_lor hl h_v603 h_v613 (of_decide_eq_true rfl))
  have e_v614 : (v614 = 1 ↔ v603 = 1 ∨ v613 = 1) := e_lor h_v603 h_v613 (of_decide_eq_true rfl)
  have h_v615 : R 1 0 4611686018158952441 4611686018695823367 v615 v615 := (r_psel hl h_v614 h_v90 h_v97 (of_decide_eq_true rfl))
  have e_v615 : v615 = if v614 = 1 then v90 else v97 := e_psel h_v614 h_v90 h_v97 (of_decide_eq_true rfl)
  have h_v616 : R 1 0 0 1 v616 v616 := (r_land hl h_v129 h_v603 (of_decide_eq_true rfl))
  have e_v616 : (v616 = 1 ↔ v129 = 1 ∧ v603 = 1) := e_land h_v129 h_v603 (of_decide_eq_true rfl)
  clear h_v599 h_v600 h_v601 h_v603 h_v604 h_v605 h_v607 h_v608 h_v610 h_v611 h_v613 h_v614
  have h_v617 : R 1 0 0 1 v617 v617 := (r_lor hl h_v128 h_v616 (of_decide_eq_true rfl))
  have e_v617 : (v617 = 1 ↔ v128 = 1 ∨ v616 = 1) := e_lor h_v128 h_v616 (of_decide_eq_true rfl)
  have h_v618 : R 1 0 4611686018427387900 4611686018695823367 v618 v618 := (r_psel hl h_v617 h_v591 h_v598 (of_decide_eq_true rfl))
  have e_v618 : v618 = if v617 = 1 then v591 else v598 := e_psel h_v617 h_v591 h_v598 (of_decide_eq_true rfl)
  have h_v619 : R 1 0 4539628420631363535 4683743616223412273 v619 v619 := (r_smx hl 29 h_v612 h_v609 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v619 : sv v619 = sv v612 * sv v609 := e_smx 29 h_v612 h_v609 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v620 : R 1 0 4611686018158952433 4611686018695823374 v620 v620 := (r_srdF hl h_v619 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v620 : sv v620 = sv v619 / 2 ^ 28 := e_srdF h_v619 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v621 : R 1 0 4539628420631363535 4683743616223412273 v621 v621 := (r_smx hl 29 h_v618 h_v615 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v621 : sv v621 = sv v618 * sv v615 := e_smx 29 h_v618 h_v615 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v622 : R 1 0 4611686018158952434 4611686018695823375 v622 v622 := (r_srdC hl h_v621 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v622 : sv v622 = -((-sv v621) / 2 ^ 28) := e_srdC h_v621 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v623 : R 1 0 0 1 v623 v623 := (r_plt hl h_v51 h_v620 (of_decide_eq_true rfl))
  have e_v623 : (v623 = 1 ↔ sv v51 < sv v620) := e_plt h_v51 h_v620 (of_decide_eq_true rfl)
  have h_v624 : R 1 0 0 1 v624 v624 := (r_sub hl (r_O hl) h_v623 (of_decide_eq_true rfl))
  have e_v624 : (v624 = 1 ↔ ¬v623 = 1) := e_not h_v623 (of_decide_eq_true rfl)
  have h_v627 : R 1 0 0 1 v627 v627 := (r_plt hl h_v587 h_v51 (of_decide_eq_true rfl))
  have e_v627 : (v627 = 1 ↔ sv v587 < sv v51) := e_plt h_v587 h_v51 (of_decide_eq_true rfl)
  have h_v628 : R 1 0 4611686018158952433 4611686018695823375 v628 v628 := (r_psel hl h_v627 h_v622 h_v620 (of_decide_eq_true rfl))
  have e_v628 : v628 = if v627 = 1 then v622 else v620 := e_psel h_v627 h_v622 h_v620 (of_decide_eq_true rfl)
  have h_v670 : R 1 0 4611686018158952441 4611686018695823359 v670 v670 := (r_sub hl (r_add hl h_v51 h_OFFr (of_decide_eq_true rfl)) h_v587 (of_decide_eq_true rfl))
  have e_v670 : sv v670 = sv v51 - sv v587 := e_sub h_v51 h_v587 (of_decide_eq_true rfl)
  have h_v671 : R 1 0 4611686018158952441 4611686018695823367 v671 v671 := (r_psel hl h_v627 h_v670 h_v587 (of_decide_eq_true rfl))
  have e_v671 : v671 = if v627 = 1 then v670 else v587 := e_psel h_v627 h_v670 h_v587 (of_decide_eq_true rfl)
  have h_v672 : R 1 0 4611686018427387904 4611686019501129727 v672 v672 := (r1_hxa hb_H0 32 (of_decide_eq_true rfl))
  clear h_v587 h_v591 h_v598 h_v609 h_v612 h_v615 h_v616 h_v617 h_v618 h_v619 h_v620 h_v621 h_v622 h_v623 h_v670
  have e_v672 : sv v672 = ((H0 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 32 (of_decide_eq_true rfl)
  have h_t672_1 : R 1 0 4611686018427387904 4611686018695823363 t672.1 t672.1 := r_sc1 hl h_v672 (of_decide_eq_true rfl)
  have h_t672_2 : R 1 0 4611686018158952445 4611686018695823363 t672.2 t672.2 := r_sc2 hl h_v672 (of_decide_eq_true rfl)
  have e_t672_1 : sv t672.1 = (sc28pS (scArg v672)).1 := e_sc1 h_v672 (of_decide_eq_true rfl)
  have e_t672_2 : sv t672.2 = (sc28pS (scArg v672)).2 := e_sc2 h_v672 (of_decide_eq_true rfl)
  have h_v674 : R 1 0 4611686018158952441 4611686018695823359 v674 v674 := (r_sub hl (r_add hl h_v18 h_t672_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v674 : sv v674 = sv v18 + sv t672.2 := e_add h_v18 h_t672_2 (of_decide_eq_true rfl)
  have h_v675 : R 1 0 0 1 v675 v675 := (r_plt hl h_v674 h_v85 (of_decide_eq_true rfl))
  have e_v675 : (v675 = 1 ↔ sv v674 < sv v85) := e_plt h_v674 h_v85 (of_decide_eq_true rfl)
  have h_v676 : R 1 0 4611686018158952441 4611686018695823359 v676 v676 := (r_psel hl h_v675 h_v85 h_v674 (of_decide_eq_true rfl))
  have e_v676 : v676 = if v675 = 1 then v85 else v674 := e_psel h_v675 h_v85 h_v674 (of_decide_eq_true rfl)
  have h_v677 : R 1 0 4611686018158952449 4611686018695823367 v677 v677 := (r_sub hl (r_add hl h_v21 h_t672_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v677 : sv v677 = sv v21 + sv t672.2 := e_add h_v21 h_t672_2 (of_decide_eq_true rfl)
  have h_v678 : R 1 0 0 1 v678 v678 := (r_plt hl h_v677 h_v23 (of_decide_eq_true rfl))
  have e_v678 : (v678 = 1 ↔ sv v677 < sv v23) := e_plt h_v677 h_v23 (of_decide_eq_true rfl)
  have h_v679 : R 1 0 4611686018158952449 4611686018695823367 v679 v679 := (r_psel hl h_v678 h_v677 h_v23 (of_decide_eq_true rfl))
  have e_v679 : v679 = if v678 = 1 then v677 else v23 := e_psel h_v678 h_v677 h_v23 (of_decide_eq_true rfl)
  have h_v681 : R 1 0 4611686018427387908 4611686018695823367 v681 v681 := (r_sub hl (r_add hl h_v21 h_t672_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v681 : sv v681 = sv v21 + sv t672.1 := e_add h_v21 h_t672_1 (of_decide_eq_true rfl)
  have h_v682 : R 1 0 0 1 v682 v682 := (r_plt hl h_v681 h_v23 (of_decide_eq_true rfl))
  have e_v682 : (v682 = 1 ↔ sv v681 < sv v23) := e_plt h_v681 h_v23 (of_decide_eq_true rfl)
  have h_v683 : R 1 0 4611686018427387908 4611686018695823367 v683 v683 := (r_psel hl h_v682 h_v681 h_v23 (of_decide_eq_true rfl))
  have e_v683 : v683 = if v682 = 1 then v681 else v23 := e_psel h_v682 h_v681 h_v23 (of_decide_eq_true rfl)
  have h_v684 : R 1 0 4611686018427387900 4611686018695823359 v684 v684 := (r_sub hl (r_add hl h_v18 h_t672_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v684 : sv v684 = sv v18 + sv t672.1 := e_add h_v18 h_t672_1 (of_decide_eq_true rfl)
  clear h_v18 h_t672_1 h_t672_2 h_v674 h_v675 h_v677 h_v678 h_v681 h_v682
  have h_v685 : R 1 0 4611686018158952441 4611686018695823367 v685 v685 := (r_psel hl h_v627 h_v676 h_v679 (of_decide_eq_true rfl))
  have e_v685 : v685 = if v627 = 1 then v676 else v679 := e_psel h_v627 h_v676 h_v679 (of_decide_eq_true rfl)
  have h_v686 : R 1 0 4611686018427387900 4611686018695823367 v686 v686 := (r_psel hl h_v627 h_v683 h_v684 (of_decide_eq_true rfl))
  have e_v686 : v686 = if v627 = 1 then v683 else v684 := e_psel h_v627 h_v683 h_v684 (of_decide_eq_true rfl)
  have h_v687 : R 1 0 4539628418483879831 4683743618370895977 v687 v687 := (r_smx hl 29 h_v628 h_v686 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v687 : sv v687 = sv v628 * sv v686 := e_smx 29 h_v628 h_v686 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v688 : R 1 0 4539628420631363535 4683743616223412273 v688 v688 := (r_smx hl 29 h_v685 h_v671 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v688 : sv v688 = sv v685 * sv v671 := e_smx 29 h_v685 h_v671 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v689 : R 1 0 0 1 v689 v689 := (r_plt hl h_v688 h_v687 (of_decide_eq_true rfl))
  have e_v689 : (v689 = 1 ↔ sv v688 < sv v687) := e_plt h_v688 h_v687 (of_decide_eq_true rfl)
  have h_v690 : R 1 0 0 1 v690 v690 := (r_sub hl (r_O hl) h_v689 (of_decide_eq_true rfl))
  have e_v690 : (v690 = 1 ↔ ¬v689 = 1) := e_not h_v689 (of_decide_eq_true rfl)
  have h_v691 : R 1 0 0 1 v691 v691 := (r_plt hl h_v687 h_v688 (of_decide_eq_true rfl))
  have e_v691 : (v691 = 1 ↔ sv v687 < sv v688) := e_plt h_v687 h_v688 (of_decide_eq_true rfl)
  have h_v692 : R 1 0 0 1 v692 v692 := (r_sub hl (r_O hl) h_v691 (of_decide_eq_true rfl))
  have e_v692 : (v692 = 1 ↔ ¬v691 = 1) := e_not h_v691 (of_decide_eq_true rfl)
  have h_v693 : R 1 0 0 1 v693 v693 := (r_plt hl h_v51 h_v672 (of_decide_eq_true rfl))
  have e_v693 : (v693 = 1 ↔ sv v51 < sv v672) := e_plt h_v51 h_v672 (of_decide_eq_true rfl)
  have h_v694 : R 1 0 0 1 v694 v694 := (r_sub hl (r_O hl) h_v693 (of_decide_eq_true rfl))
  have e_v694 : (v694 = 1 ↔ ¬v693 = 1) := e_not h_v693 (of_decide_eq_true rfl)
  have h_v695 : R 1 0 0 1 v695 v695 := (r_plt hl h_v186 h_v672 (of_decide_eq_true rfl))
  have e_v695 : (v695 = 1 ↔ sv v186 < sv v672) := e_plt h_v186 h_v672 (of_decide_eq_true rfl)
  have h_v696 : R 1 0 0 1 v696 v696 := (r_sub hl (r_O hl) h_v695 (of_decide_eq_true rfl))
  have e_v696 : (v696 = 1 ↔ ¬v695 = 1) := e_not h_v695 (of_decide_eq_true rfl)
  have h_v697 : R 1 0 0 1 v697 v697 := (r_plt hl h_v8 h_v676 (of_decide_eq_true rfl))
  clear h_v186 h_v628 h_v671 h_v679 h_v683 h_v684 h_v685 h_v686 h_v687 h_v688 h_v689 h_v691 h_v693 h_v695
  have e_v697 : (v697 = 1 ↔ sv v8 < sv v676) := e_plt h_v8 h_v676 (of_decide_eq_true rfl)
  have h_v698 : R 1 0 0 1 v698 v698 := (r_land hl h_v690 h_v697 (of_decide_eq_true rfl))
  have e_v698 : (v698 = 1 ↔ v690 = 1 ∧ v697 = 1) := e_land h_v690 h_v697 (of_decide_eq_true rfl)
  have h_v699 : R 1 0 0 1 v699 v699 := (r_land hl h_v696 h_v698 (of_decide_eq_true rfl))
  have e_v699 : (v699 = 1 ↔ v696 = 1 ∧ v698 = 1) := e_land h_v696 h_v698 (of_decide_eq_true rfl)
  have h_v700 : R 1 0 0 1 v700 v700 := (r_lor hl h_v694 h_v699 (of_decide_eq_true rfl))
  have e_v700 : (v700 = 1 ↔ v694 = 1 ∨ v699 = 1) := e_lor h_v694 h_v699 (of_decide_eq_true rfl)
  have h_v701 : R 1 0 0 1 v701 v701 := (r_plt hl h_v672 h_v193 (of_decide_eq_true rfl))
  have e_v701 : (v701 = 1 ↔ sv v672 < sv v193) := e_plt h_v672 h_v193 (of_decide_eq_true rfl)
  have h_v702 : R 1 0 0 1 v702 v702 := (r_sub hl (r_O hl) h_v701 (of_decide_eq_true rfl))
  have e_v702 : (v702 = 1 ↔ ¬v701 = 1) := e_not h_v701 (of_decide_eq_true rfl)
  have h_v703 : R 1 0 0 1 v703 v703 := (r_lor hl h_v692 h_v702 (of_decide_eq_true rfl))
  have e_v703 : (v703 = 1 ↔ v692 = 1 ∨ v702 = 1) := e_lor h_v692 h_v702 (of_decide_eq_true rfl)
  have h_v704 : R 1 0 0 1 v704 v704 := (r_land hl h_v627 h_v700 (of_decide_eq_true rfl))
  have e_v704 : (v704 = 1 ↔ v627 = 1 ∧ v700 = 1) := e_land h_v627 h_v700 (of_decide_eq_true rfl)
  have h_v705 : R 1 0 0 1 v705 v705 := (r_sub hl (r_O hl) h_v627 (of_decide_eq_true rfl))
  have e_v705 : (v705 = 1 ↔ ¬v627 = 1) := e_not h_v627 (of_decide_eq_true rfl)
  have h_v706 : R 1 0 0 1 v706 v706 := (r_land hl h_v703 h_v705 (of_decide_eq_true rfl))
  have e_v706 : (v706 = 1 ↔ v703 = 1 ∧ v705 = 1) := e_land h_v703 h_v705 (of_decide_eq_true rfl)
  have h_v707 : R 1 0 0 1 v707 v707 := (r_lor hl h_v704 h_v706 (of_decide_eq_true rfl))
  have e_v707 : (v707 = 1 ↔ v704 = 1 ∨ v706 = 1) := e_lor h_v704 h_v706 (of_decide_eq_true rfl)
  have h_v708 : R 1 0 4611686017353646081 4611686018427387904 v708 v708 := (r_sub hl (r_add hl h_v51 h_OFFr (of_decide_eq_true rfl)) h_v672 (of_decide_eq_true rfl))
  have e_v708 : sv v708 = sv v51 - sv v672 := e_sub h_v51 h_v672 (of_decide_eq_true rfl)
  have h_v709 : R 1 0 4611686017353646081 4611686019501129727 v709 v709 := (r_psel hl h_v627 h_v708 h_v672 (of_decide_eq_true rfl))
  have e_v709 : v709 = if v627 = 1 then v708 else v672 := e_psel h_v627 h_v708 h_v672 (of_decide_eq_true rfl)
  clear h_v627 h_v672 h_v676 h_v690 h_v692 h_v694 h_v696 h_v697 h_v698 h_v699 h_v700 h_v701 h_v702 h_v703 h_v704 h_v705 h_v706 h_v708
  have h_v710 : R 1 0 4611686017353646081 4611686019501129727 v710 v710 := (r_psel hl h_v707 h_v709 h_v193 (of_decide_eq_true rfl))
  have e_v710 : v710 = if v707 = 1 then v709 else v193 := e_psel h_v707 h_v709 h_v193 (of_decide_eq_true rfl)
  have h_v712 : R 1 0 4611686017353646081 4611686019501129727 v712 v712 := (r_psel hl h_v624 h_v193 h_v710 (of_decide_eq_true rfl))
  have e_v712 : v712 = if v624 = 1 then v193 else v710 := e_psel h_v624 h_v193 h_v710 (of_decide_eq_true rfl)
  have h_v713 : R 1 0 0 1 v713 v713 := (r_plt hl h_v51 h_v0 (of_decide_eq_true rfl))
  have e_v713 : (v713 = 1 ↔ sv v51 < sv v0) := e_plt h_v51 h_v0 (of_decide_eq_true rfl)
  have h_v714 : R 1 0 4611686019270702760 4611686019270702760 v714 v714 := (r_c hl 4611686019270702760 (of_decide_eq_true rfl))
  have e_v714 : sv v714 = (843314856) := e_c 4611686019270702760 (843314856) (of_decide_eq_true rfl)
  have h_v715 : R 1 0 0 1 v715 v715 := (r_plt hl h_v1 h_v714 (of_decide_eq_true rfl))
  have e_v715 : (v715 = 1 ↔ sv v1 < sv v714) := e_plt h_v1 h_v714 (of_decide_eq_true rfl)
  have h_v716 : R 1 0 0 1 v716 v716 := (r_land hl h_v713 h_v715 (of_decide_eq_true rfl))
  have e_v716 : (v716 = 1 ↔ v713 = 1 ∧ v715 = 1) := e_land h_v713 h_v715 (of_decide_eq_true rfl)
  have h_v717 : R 1 0 0 1 v717 v717 := (r_plt hl h_v51 h_v79 (of_decide_eq_true rfl))
  have e_v717 : (v717 = 1 ↔ sv v51 < sv v79) := e_plt h_v51 h_v79 (of_decide_eq_true rfl)
  have h_v718 : R 1 0 0 1 v718 v718 := (r_plt hl h_v81 h_v23 (of_decide_eq_true rfl))
  have e_v718 : (v718 = 1 ↔ sv v81 < sv v23) := e_plt h_v81 h_v23 (of_decide_eq_true rfl)
  have h_v719 : R 1 0 0 1 v719 v719 := (r_land hl h_v717 h_v718 (of_decide_eq_true rfl))
  have e_v719 : (v719 = 1 ↔ v717 = 1 ∧ v718 = 1) := e_land h_v717 h_v718 (of_decide_eq_true rfl)
  have h_v720 : R 1 0 0 1 v720 v720 := (r_plt hl h_v51 h_v428 (of_decide_eq_true rfl))
  have e_v720 : (v720 = 1 ↔ sv v51 < sv v428) := e_plt h_v51 h_v428 (of_decide_eq_true rfl)
  have h_v721 : R 1 0 0 1 v721 v721 := (r_plt hl h_v430 h_v23 (of_decide_eq_true rfl))
  have e_v721 : (v721 = 1 ↔ sv v430 < sv v23) := e_plt h_v430 h_v23 (of_decide_eq_true rfl)
  have h_v722 : R 1 0 0 1 v722 v722 := (r_land hl h_v720 h_v721 (of_decide_eq_true rfl))
  have e_v722 : (v722 = 1 ↔ v720 = 1 ∧ v721 = 1) := e_land h_v720 h_v721 (of_decide_eq_true rfl)
  have h_v723 : R 1 0 0 1 v723 v723 := (r_land hl h_v716 h_v719 (of_decide_eq_true rfl))
  clear h_v193 h_v624 h_v707 h_v709 h_v710 h_v713 h_v714 h_v715 h_v717 h_v718 h_v720 h_v721
  have e_v723 : (v723 = 1 ↔ v716 = 1 ∧ v719 = 1) := e_land h_v716 h_v719 (of_decide_eq_true rfl)
  have h_v724 : R 1 0 0 1 v724 v724 := (r_land hl h_v722 h_v723 (of_decide_eq_true rfl))
  have e_v724 : (v724 = 1 ↔ v722 = 1 ∧ v723 = 1) := e_land h_v722 h_v723 (of_decide_eq_true rfl)
  have h_v725 : R 1 0 0 1 v725 v725 := (r_sub hl (r_O hl) h_v724 (of_decide_eq_true rfl))
  have e_v725 : (v725 = 1 ↔ ¬v724 = 1) := e_not h_v724 (of_decide_eq_true rfl)
  have h_v726 : R 1 0 0 1 v726 v726 := (r_lor hl h_v13 h_v725 (of_decide_eq_true rfl))
  have e_v726 : (v726 = 1 ↔ v13 = 1 ∨ v725 = 1) := e_lor h_v13 h_v725 (of_decide_eq_true rfl)
  have h_v727 : R 1 0 4611686018427387904 4683743620518379745 v727 v727 := (r_smx_sq hl 29 h_v430 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v727 : sv v727 = sv v430 * sv v430 := e_smx_sq 29 h_v430 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v728 : R 1 0 4611686018427387904 4611686018695823391 v728 v728 := (r_srdC hl h_v727 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v728 : sv v728 = -((-sv v727) / 2 ^ 28) := e_srdC h_v727 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v729 : R 1 0 4611686018427387904 4611686018964258878 v729 v729 := (r_sub hl (r_add hl h_v728 h_v728 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v729 : sv v729 = sv v728 + sv v728 := e_add h_v728 h_v728 (of_decide_eq_true rfl)
  have h_v730 : R 1 0 4611686018158952386 4611686018695823360 v730 v730 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v729 (of_decide_eq_true rfl))
  have e_v730 : sv v730 = sv v23 - sv v729 := e_sub h_v23 h_v729 (of_decide_eq_true rfl)
  have h_v731 : R 1 0 0 1 v731 v731 := (r_plt hl h_v730 h_v85 (of_decide_eq_true rfl))
  have e_v731 : (v731 = 1 ↔ sv v730 < sv v85) := e_plt h_v730 h_v85 (of_decide_eq_true rfl)
  have h_v732 : R 1 0 4611686018158952386 4611686018695823360 v732 v732 := (r_psel hl h_v731 h_v85 h_v730 (of_decide_eq_true rfl))
  have e_v732 : v732 = if v731 = 1 then v85 else v730 := e_psel h_v731 h_v85 h_v730 (of_decide_eq_true rfl)
  have h_v733 : R 1 0 4611686018427387904 4683743619981508804 v733 v733 := (r_smx_sq hl 29 h_v428 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v733 : sv v733 = sv v428 * sv v428 := e_smx_sq 29 h_v428 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v734 : R 1 0 4611686018427387904 4611686018695823388 v734 v734 := (r_srdF hl h_v733 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v734 : sv v734 = sv v733 / 2 ^ 28 := e_srdF h_v733 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v735 : R 1 0 4611686018427387904 4611686018964258872 v735 v735 := (r_sub hl (r_add hl h_v734 h_v734 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v735 : sv v735 = sv v734 + sv v734 := e_add h_v734 h_v734 (of_decide_eq_true rfl)
  clear h_v716 h_v719 h_v722 h_v723 h_v727 h_v728 h_v729 h_v730 h_v731 h_v733 h_v734
  have h_v736 : R 1 0 4611686018158952392 4611686018695823360 v736 v736 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v735 (of_decide_eq_true rfl))
  have e_v736 : sv v736 = sv v23 - sv v735 := e_sub h_v23 h_v735 (of_decide_eq_true rfl)
  have h_v737 : R 1 0 4611686018427387904 4683743620518379745 v737 v737 := (r_smx_sq hl 29 h_v81 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v737 : sv v737 = sv v81 * sv v81 := e_smx_sq 29 h_v81 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v738 : R 1 0 4611686018427387904 4611686018695823391 v738 v738 := (r_srdC hl h_v737 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v738 : sv v738 = -((-sv v737) / 2 ^ 28) := e_srdC h_v737 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v739 : R 1 0 4611686018427387904 4611686018964258878 v739 v739 := (r_sub hl (r_add hl h_v738 h_v738 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v739 : sv v739 = sv v738 + sv v738 := e_add h_v738 h_v738 (of_decide_eq_true rfl)
  have h_v740 : R 1 0 4611686018158952386 4611686018695823360 v740 v740 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v739 (of_decide_eq_true rfl))
  have e_v740 : sv v740 = sv v23 - sv v739 := e_sub h_v23 h_v739 (of_decide_eq_true rfl)
  have h_v741 : R 1 0 0 1 v741 v741 := (r_plt hl h_v740 h_v85 (of_decide_eq_true rfl))
  have e_v741 : (v741 = 1 ↔ sv v740 < sv v85) := e_plt h_v740 h_v85 (of_decide_eq_true rfl)
  have h_v742 : R 1 0 4611686018158952386 4611686018695823360 v742 v742 := (r_psel hl h_v741 h_v85 h_v740 (of_decide_eq_true rfl))
  have e_v742 : v742 = if v741 = 1 then v85 else v740 := e_psel h_v741 h_v85 h_v740 (of_decide_eq_true rfl)
  have h_v743 : R 1 0 4611686018427387904 4683743619981508804 v743 v743 := (r_smx_sq hl 29 h_v79 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v743 : sv v743 = sv v79 * sv v79 := e_smx_sq 29 h_v79 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v744 : R 1 0 4611686018427387904 4611686018695823388 v744 v744 := (r_srdF hl h_v743 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v744 : sv v744 = sv v743 / 2 ^ 28 := e_srdF h_v743 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v745 : R 1 0 4611686018427387904 4611686018964258872 v745 v745 := (r_sub hl (r_add hl h_v744 h_v744 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v745 : sv v745 = sv v744 + sv v744 := e_add h_v744 h_v744 (of_decide_eq_true rfl)
  have h_v746 : R 1 0 4611686018158952392 4611686018695823360 v746 v746 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v745 (of_decide_eq_true rfl))
  have e_v746 : sv v746 = sv v23 - sv v745 := e_sub h_v23 h_v745 (of_decide_eq_true rfl)
  have h_v747 : R 1 0 0 1 v747 v747 := (r_plt hl h_v742 h_v51 (of_decide_eq_true rfl))
  have e_v747 : (v747 = 1 ↔ sv v742 < sv v51) := e_plt h_v742 h_v51 (of_decide_eq_true rfl)
  have h_v748 : R 1 0 0 1 v748 v748 := (r_sub hl (r_O hl) h_v747 (of_decide_eq_true rfl))
  clear h_v735 h_v737 h_v738 h_v739 h_v740 h_v741 h_v743 h_v744 h_v745
  have e_v748 : (v748 = 1 ↔ ¬v747 = 1) := e_not h_v747 (of_decide_eq_true rfl)
  have h_v749 : R 1 0 0 1 v749 v749 := (r_plt hl h_v51 h_v746 (of_decide_eq_true rfl))
  have e_v749 : (v749 = 1 ↔ sv v51 < sv v746) := e_plt h_v51 h_v746 (of_decide_eq_true rfl)
  have h_v750 : R 1 0 0 1 v750 v750 := (r_sub hl (r_O hl) h_v749 (of_decide_eq_true rfl))
  have e_v750 : (v750 = 1 ↔ ¬v749 = 1) := e_not h_v749 (of_decide_eq_true rfl)
  have h_v751 : R 1 0 0 1 v751 v751 := (r_land hl h_v747 h_v750 (of_decide_eq_true rfl))
  have e_v751 : (v751 = 1 ↔ v747 = 1 ∧ v750 = 1) := e_land h_v747 h_v750 (of_decide_eq_true rfl)
  have h_v752 : R 1 0 0 1 v752 v752 := (r_land hl h_v747 h_v749 (of_decide_eq_true rfl))
  have e_v752 : (v752 = 1 ↔ v747 = 1 ∧ v749 = 1) := e_land h_v747 h_v749 (of_decide_eq_true rfl)
  have h_v753 : R 1 0 0 1 v753 v753 := (r_land hl h_v129 h_v752 (of_decide_eq_true rfl))
  have e_v753 : (v753 = 1 ↔ v129 = 1 ∧ v752 = 1) := e_land h_v129 h_v752 (of_decide_eq_true rfl)
  have h_v754 : R 1 0 0 1 v754 v754 := (r_sub hl (r_O hl) h_v753 (of_decide_eq_true rfl))
  have e_v754 : (v754 = 1 ↔ ¬v753 = 1) := e_not h_v753 (of_decide_eq_true rfl)
  have h_v755 : R 1 0 0 1 v755 v755 := (r_lor hl h_v725 h_v754 (of_decide_eq_true rfl))
  have e_v755 : (v755 = 1 ↔ v725 = 1 ∨ v754 = 1) := e_lor h_v725 h_v754 (of_decide_eq_true rfl)
  have h_v756 : R 1 0 0 1 v756 v756 := (r_land hl h_v125 h_v752 (of_decide_eq_true rfl))
  have e_v756 : (v756 = 1 ↔ v125 = 1 ∧ v752 = 1) := e_land h_v125 h_v752 (of_decide_eq_true rfl)
  have h_v757 : R 1 0 0 1 v757 v757 := (r_lor hl h_v751 h_v756 (of_decide_eq_true rfl))
  have e_v757 : (v757 = 1 ↔ v751 = 1 ∨ v756 = 1) := e_lor h_v751 h_v756 (of_decide_eq_true rfl)
  have h_v758 : R 1 0 4611686018158952441 4611686018695823367 v758 v758 := (r_psel hl h_v757 h_v97 h_v90 (of_decide_eq_true rfl))
  have e_v758 : v758 = if v757 = 1 then v97 else v90 := e_psel h_v757 h_v97 h_v90 (of_decide_eq_true rfl)
  have h_v759 : R 1 0 0 1 v759 v759 := (r_land hl h_v129 h_v748 (of_decide_eq_true rfl))
  have e_v759 : (v759 = 1 ↔ v129 = 1 ∧ v748 = 1) := e_land h_v129 h_v748 (of_decide_eq_true rfl)
  have h_v760 : R 1 0 0 1 v760 v760 := (r_lor hl h_v128 h_v759 (of_decide_eq_true rfl))
  have e_v760 : (v760 = 1 ↔ v128 = 1 ∨ v759 = 1) := e_lor h_v128 h_v759 (of_decide_eq_true rfl)
  clear h_v747 h_v748 h_v749 h_v750 h_v753 h_v754 h_v756 h_v757 h_v759
  have h_v761 : R 1 0 4611686018158952386 4611686018695823360 v761 v761 := (r_psel hl h_v760 h_v746 h_v742 (of_decide_eq_true rfl))
  have e_v761 : v761 = if v760 = 1 then v746 else v742 := e_psel h_v760 h_v746 h_v742 (of_decide_eq_true rfl)
  have h_v762 : R 1 0 0 1 v762 v762 := (r_land hl h_v128 h_v752 (of_decide_eq_true rfl))
  have e_v762 : (v762 = 1 ↔ v128 = 1 ∧ v752 = 1) := e_land h_v128 h_v752 (of_decide_eq_true rfl)
  have h_v763 : R 1 0 0 1 v763 v763 := (r_lor hl h_v751 h_v762 (of_decide_eq_true rfl))
  have e_v763 : (v763 = 1 ↔ v751 = 1 ∨ v762 = 1) := e_lor h_v751 h_v762 (of_decide_eq_true rfl)
  have h_v764 : R 1 0 4611686018158952441 4611686018695823367 v764 v764 := (r_psel hl h_v763 h_v90 h_v97 (of_decide_eq_true rfl))
  have e_v764 : v764 = if v763 = 1 then v90 else v97 := e_psel h_v763 h_v90 h_v97 (of_decide_eq_true rfl)
  have h_v765 : R 1 0 0 1 v765 v765 := (r_land hl h_v129 h_v751 (of_decide_eq_true rfl))
  have e_v765 : (v765 = 1 ↔ v129 = 1 ∧ v751 = 1) := e_land h_v129 h_v751 (of_decide_eq_true rfl)
  have h_v766 : R 1 0 0 1 v766 v766 := (r_lor hl h_v128 h_v765 (of_decide_eq_true rfl))
  have e_v766 : (v766 = 1 ↔ v128 = 1 ∨ v765 = 1) := e_lor h_v128 h_v765 (of_decide_eq_true rfl)
  have h_v767 : R 1 0 4611686018158952386 4611686018695823360 v767 v767 := (r_psel hl h_v766 h_v742 h_v746 (of_decide_eq_true rfl))
  have e_v767 : v767 = if v766 = 1 then v742 else v746 := e_psel h_v766 h_v742 h_v746 (of_decide_eq_true rfl)
  have h_v768 : R 1 0 4539628405867413070 4683743630987362738 v768 v768 := (r_smx hl 29 h_v761 h_v758 4539628405867413070 4683743630987362738 (of_decide_eq_true rfl))
  have e_v768 : sv v768 = sv v761 * sv v758 := e_smx 29 h_v761 h_v758 4539628405867413070 4683743630987362738 (of_decide_eq_true rfl)
  have h_v769 : R 1 0 4611686018158952378 4611686018695823429 v769 v769 := (r_srdF hl h_v768 4611686018158952378 4611686018695823429 (of_decide_eq_true rfl))
  have e_v769 : sv v769 = sv v768 / 2 ^ 28 := e_srdF h_v768 4611686018158952378 4611686018695823429 (of_decide_eq_true rfl)
  have h_v770 : R 1 0 4539628405867413070 4683743630987362738 v770 v770 := (r_smx hl 29 h_v767 h_v764 4539628405867413070 4683743630987362738 (of_decide_eq_true rfl))
  have e_v770 : sv v770 = sv v767 * sv v764 := e_smx 29 h_v767 h_v764 4539628405867413070 4683743630987362738 (of_decide_eq_true rfl)
  have h_v771 : R 1 0 4611686018158952379 4611686018695823430 v771 v771 := (r_srdC hl h_v770 4611686018158952379 4611686018695823430 (of_decide_eq_true rfl))
  have e_v771 : sv v771 = -((-sv v770) / 2 ^ 28) := e_srdC h_v770 4611686018158952379 4611686018695823430 (of_decide_eq_true rfl)
  have h_v772 : R 1 0 4611686017890516860 4611686018964258885 v772 v772 := (r_sub hl (r_add hl h_v732 h_OFFr (of_decide_eq_true rfl)) h_v771 (of_decide_eq_true rfl))
  have e_v772 : sv v772 = sv v732 - sv v771 := e_sub h_v732 h_v771 (of_decide_eq_true rfl)
  have h_v773 : R 1 0 4611686017890516867 4611686018964258886 v773 v773 := (r_sub hl (r_add hl h_v736 h_OFFr (of_decide_eq_true rfl)) h_v769 (of_decide_eq_true rfl))
  clear h_v751 h_v752 h_v758 h_v760 h_v761 h_v762 h_v763 h_v764 h_v765 h_v766 h_v767 h_v768 h_v770 h_v771
  have e_v773 : sv v773 = sv v736 - sv v769 := e_sub h_v736 h_v769 (of_decide_eq_true rfl)
  have h_v774 : R 1 0 0 1 v774 v774 := (r_plt hl h_v732 h_v51 (of_decide_eq_true rfl))
  have e_v774 : (v774 = 1 ↔ sv v732 < sv v51) := e_plt h_v732 h_v51 (of_decide_eq_true rfl)
  have h_v775 : R 1 0 0 1 v775 v775 := (r_sub hl (r_O hl) h_v774 (of_decide_eq_true rfl))
  have e_v775 : (v775 = 1 ↔ ¬v774 = 1) := e_not h_v774 (of_decide_eq_true rfl)
  have h_v776 : R 1 0 0 1 v776 v776 := (r_plt hl h_v51 h_v736 (of_decide_eq_true rfl))
  have e_v776 : (v776 = 1 ↔ sv v51 < sv v736) := e_plt h_v51 h_v736 (of_decide_eq_true rfl)
  have h_v777 : R 1 0 0 1 v777 v777 := (r_sub hl (r_O hl) h_v776 (of_decide_eq_true rfl))
  have e_v777 : (v777 = 1 ↔ ¬v776 = 1) := e_not h_v776 (of_decide_eq_true rfl)
  have h_v778 : R 1 0 0 1 v778 v778 := (r_land hl h_v774 h_v777 (of_decide_eq_true rfl))
  have e_v778 : (v778 = 1 ↔ v774 = 1 ∧ v777 = 1) := e_land h_v774 h_v777 (of_decide_eq_true rfl)
  have h_v779 : R 1 0 0 1 v779 v779 := (r_land hl h_v774 h_v776 (of_decide_eq_true rfl))
  have e_v779 : (v779 = 1 ↔ v774 = 1 ∧ v776 = 1) := e_land h_v774 h_v776 (of_decide_eq_true rfl)
  have h_v780 : R 1 0 0 1 v780 v780 := (r_land hl h_v129 h_v779 (of_decide_eq_true rfl))
  have e_v780 : (v780 = 1 ↔ v129 = 1 ∧ v779 = 1) := e_land h_v129 h_v779 (of_decide_eq_true rfl)
  have h_v781 : R 1 0 0 1 v781 v781 := (r_sub hl (r_O hl) h_v780 (of_decide_eq_true rfl))
  have e_v781 : (v781 = 1 ↔ ¬v780 = 1) := e_not h_v780 (of_decide_eq_true rfl)
  have h_v782 : R 1 0 0 1 v782 v782 := (r_lor hl h_v725 h_v781 (of_decide_eq_true rfl))
  have e_v782 : (v782 = 1 ↔ v725 = 1 ∨ v781 = 1) := e_lor h_v725 h_v781 (of_decide_eq_true rfl)
  have h_v783 : R 1 0 0 1 v783 v783 := (r_land hl h_v125 h_v779 (of_decide_eq_true rfl))
  have e_v783 : (v783 = 1 ↔ v125 = 1 ∧ v779 = 1) := e_land h_v125 h_v779 (of_decide_eq_true rfl)
  have h_v784 : R 1 0 0 1 v784 v784 := (r_lor hl h_v778 h_v783 (of_decide_eq_true rfl))
  have e_v784 : (v784 = 1 ↔ v778 = 1 ∨ v783 = 1) := e_lor h_v778 h_v783 (of_decide_eq_true rfl)
  have h_v785 : R 1 0 4611686018158952441 4611686018695823367 v785 v785 := (r_psel hl h_v784 h_v97 h_v90 (of_decide_eq_true rfl))
  have e_v785 : v785 = if v784 = 1 then v97 else v90 := e_psel h_v784 h_v97 h_v90 (of_decide_eq_true rfl)
  clear h_v125 h_v769 h_v774 h_v776 h_v777 h_v780 h_v781 h_v783 h_v784
  have h_v786 : R 1 0 0 1 v786 v786 := (r_land hl h_v129 h_v775 (of_decide_eq_true rfl))
  have e_v786 : (v786 = 1 ↔ v129 = 1 ∧ v775 = 1) := e_land h_v129 h_v775 (of_decide_eq_true rfl)
  have h_v787 : R 1 0 0 1 v787 v787 := (r_lor hl h_v128 h_v786 (of_decide_eq_true rfl))
  have e_v787 : (v787 = 1 ↔ v128 = 1 ∨ v786 = 1) := e_lor h_v128 h_v786 (of_decide_eq_true rfl)
  have h_v788 : R 1 0 4611686018158952386 4611686018695823360 v788 v788 := (r_psel hl h_v787 h_v736 h_v732 (of_decide_eq_true rfl))
  have e_v788 : v788 = if v787 = 1 then v736 else v732 := e_psel h_v787 h_v736 h_v732 (of_decide_eq_true rfl)
  have h_v789 : R 1 0 0 1 v789 v789 := (r_land hl h_v128 h_v779 (of_decide_eq_true rfl))
  have e_v789 : (v789 = 1 ↔ v128 = 1 ∧ v779 = 1) := e_land h_v128 h_v779 (of_decide_eq_true rfl)
  have h_v790 : R 1 0 0 1 v790 v790 := (r_lor hl h_v778 h_v789 (of_decide_eq_true rfl))
  have e_v790 : (v790 = 1 ↔ v778 = 1 ∨ v789 = 1) := e_lor h_v778 h_v789 (of_decide_eq_true rfl)
  have h_v791 : R 1 0 4611686018158952441 4611686018695823367 v791 v791 := (r_psel hl h_v790 h_v90 h_v97 (of_decide_eq_true rfl))
  have e_v791 : v791 = if v790 = 1 then v90 else v97 := e_psel h_v790 h_v90 h_v97 (of_decide_eq_true rfl)
  have h_v792 : R 1 0 0 1 v792 v792 := (r_land hl h_v129 h_v778 (of_decide_eq_true rfl))
  have e_v792 : (v792 = 1 ↔ v129 = 1 ∧ v778 = 1) := e_land h_v129 h_v778 (of_decide_eq_true rfl)
  have h_v793 : R 1 0 0 1 v793 v793 := (r_lor hl h_v128 h_v792 (of_decide_eq_true rfl))
  have e_v793 : (v793 = 1 ↔ v128 = 1 ∨ v792 = 1) := e_lor h_v128 h_v792 (of_decide_eq_true rfl)
  have h_v794 : R 1 0 4611686018158952386 4611686018695823360 v794 v794 := (r_psel hl h_v793 h_v732 h_v736 (of_decide_eq_true rfl))
  have e_v794 : v794 = if v793 = 1 then v732 else v736 := e_psel h_v793 h_v732 h_v736 (of_decide_eq_true rfl)
  have h_v795 : R 1 0 4539628405867413070 4683743630987362738 v795 v795 := (r_smx hl 29 h_v788 h_v785 4539628405867413070 4683743630987362738 (of_decide_eq_true rfl))
  have e_v795 : sv v795 = sv v788 * sv v785 := e_smx 29 h_v788 h_v785 4539628405867413070 4683743630987362738 (of_decide_eq_true rfl)
  have h_v796 : R 1 0 4611686018158952378 4611686018695823429 v796 v796 := (r_srdF hl h_v795 4611686018158952378 4611686018695823429 (of_decide_eq_true rfl))
  have e_v796 : sv v796 = sv v795 / 2 ^ 28 := e_srdF h_v795 4611686018158952378 4611686018695823429 (of_decide_eq_true rfl)
  have h_v797 : R 1 0 4539628405867413070 4683743630987362738 v797 v797 := (r_smx hl 29 h_v794 h_v791 4539628405867413070 4683743630987362738 (of_decide_eq_true rfl))
  have e_v797 : sv v797 = sv v794 * sv v791 := e_smx 29 h_v794 h_v791 4539628405867413070 4683743630987362738 (of_decide_eq_true rfl)
  have h_v798 : R 1 0 4611686018158952379 4611686018695823430 v798 v798 := (r_srdC hl h_v797 4611686018158952379 4611686018695823430 (of_decide_eq_true rfl))
  clear h_v128 h_v129 h_v732 h_v736 h_v775 h_v778 h_v779 h_v785 h_v786 h_v787 h_v788 h_v789 h_v790 h_v791 h_v792 h_v793 h_v794 h_v795
  have e_v798 : sv v798 = -((-sv v797) / 2 ^ 28) := e_srdC h_v797 4611686018158952379 4611686018695823430 (of_decide_eq_true rfl)
  have h_v799 : R 1 0 4611686017890516860 4611686018964258885 v799 v799 := (r_sub hl (r_add hl h_v742 h_OFFr (of_decide_eq_true rfl)) h_v798 (of_decide_eq_true rfl))
  have e_v799 : sv v799 = sv v742 - sv v798 := e_sub h_v742 h_v798 (of_decide_eq_true rfl)
  have h_v800 : R 1 0 4611686017890516867 4611686018964258886 v800 v800 := (r_sub hl (r_add hl h_v746 h_OFFr (of_decide_eq_true rfl)) h_v796 (of_decide_eq_true rfl))
  have e_v800 : sv v800 = sv v746 - sv v796 := e_sub h_v746 h_v796 (of_decide_eq_true rfl)
  have h_v801 : R 1 0 0 1 v801 v801 := (r_plt hl h_v51 h_v772 (of_decide_eq_true rfl))
  have e_v801 : (v801 = 1 ↔ sv v51 < sv v772) := e_plt h_v51 h_v772 (of_decide_eq_true rfl)
  have h_v802 : R 1 0 0 1 v802 v802 := (r_plt hl h_v773 h_v51 (of_decide_eq_true rfl))
  have e_v802 : (v802 = 1 ↔ sv v773 < sv v51) := e_plt h_v773 h_v51 (of_decide_eq_true rfl)
  have h_v803 : R 1 0 0 1 v803 v803 := (r_plt hl h_v51 h_v799 (of_decide_eq_true rfl))
  have e_v803 : (v803 = 1 ↔ sv v51 < sv v799) := e_plt h_v51 h_v799 (of_decide_eq_true rfl)
  have h_v804 : R 1 0 0 1 v804 v804 := (r_plt hl h_v800 h_v51 (of_decide_eq_true rfl))
  have e_v804 : (v804 = 1 ↔ sv v800 < sv v51) := e_plt h_v800 h_v51 (of_decide_eq_true rfl)
  have h_v805 : R 1 0 4611686018427387899 4611686018695823375 v805 v805 := (r_psel hl h_v801 h_v81 h_v79 (of_decide_eq_true rfl))
  have e_v805 : v805 = if v801 = 1 then v81 else v79 := e_psel h_v801 h_v81 h_v79 (of_decide_eq_true rfl)
  have h_v806 : R 1 0 4611686018427387899 4611686018695823375 v806 v806 := (r_psel hl h_v802 h_v79 h_v81 (of_decide_eq_true rfl))
  have e_v806 : v806 = if v802 = 1 then v79 else v81 := e_psel h_v802 h_v79 h_v81 (of_decide_eq_true rfl)
  have h_v807 : R 1 0 4611686018427387899 4611686018695823375 v807 v807 := (r_psel hl h_v802 h_v81 h_v79 (of_decide_eq_true rfl))
  have e_v807 : v807 = if v802 = 1 then v81 else v79 := e_psel h_v802 h_v81 h_v79 (of_decide_eq_true rfl)
  have h_v808 : R 1 0 4611686018427387899 4611686018695823375 v808 v808 := (r_psel hl h_v801 h_v79 h_v81 (of_decide_eq_true rfl))
  have e_v808 : v808 = if v801 = 1 then v79 else v81 := e_psel h_v801 h_v79 h_v81 (of_decide_eq_true rfl)
  have h_v809 : R 1 0 4611686018427387899 4611686018695823375 v809 v809 := (r_psel hl h_v803 h_v430 h_v428 (of_decide_eq_true rfl))
  have e_v809 : v809 = if v803 = 1 then v430 else v428 := e_psel h_v803 h_v430 h_v428 (of_decide_eq_true rfl)
  have h_v810 : R 1 0 4611686018427387899 4611686018695823375 v810 v810 := (r_psel hl h_v804 h_v428 h_v430 (of_decide_eq_true rfl))
  have e_v810 : v810 = if v804 = 1 then v428 else v430 := e_psel h_v804 h_v428 h_v430 (of_decide_eq_true rfl)
  clear h_v79 h_v81 h_v742 h_v746 h_v772 h_v773 h_v796 h_v797 h_v798 h_v799 h_v800 h_v801 h_v802
  have h_v811 : R 1 0 4611686018427387899 4611686018695823375 v811 v811 := (r_psel hl h_v804 h_v430 h_v428 (of_decide_eq_true rfl))
  have e_v811 : v811 = if v804 = 1 then v430 else v428 := e_psel h_v804 h_v430 h_v428 (of_decide_eq_true rfl)
  have h_v812 : R 1 0 4611686018427387899 4611686018695823375 v812 v812 := (r_psel hl h_v803 h_v428 h_v430 (of_decide_eq_true rfl))
  have e_v812 : v812 = if v803 = 1 then v428 else v430 := e_psel h_v803 h_v428 h_v430 (of_decide_eq_true rfl)
  have h_v813 : R 1 0 0 1 v813 v813 := (r_plt hl h_v10 h_v0 (of_decide_eq_true rfl))
  have e_v813 : (v813 = 1 ↔ sv v10 < sv v0) := e_plt h_v10 h_v0 (of_decide_eq_true rfl)
  have h_v814 : R 1 0 0 1 v814 v814 := (r_sub hl (r_O hl) h_v813 (of_decide_eq_true rfl))
  have e_v814 : (v814 = 1 ↔ ¬v813 = 1) := e_not h_v813 (of_decide_eq_true rfl)
  have h_v815 : R 1 0 0 1 v815 v815 := (r_land hl h_v9 h_v814 (of_decide_eq_true rfl))
  have e_v815 : (v815 = 1 ↔ v9 = 1 ∧ v814 = 1) := e_land h_v9 h_v814 (of_decide_eq_true rfl)
  have h_v816 : R 1 0 0 1 v816 v816 := (r_lor hl h_v725 h_v815 (of_decide_eq_true rfl))
  have e_v816 : (v816 = 1 ↔ v725 = 1 ∨ v815 = 1) := e_lor h_v725 h_v815 (of_decide_eq_true rfl)
  have h_v822 : R 1 0 4611686018427387904 4683743620518379745 v822 v822 := (r_smx_sq hl 29 h_v806 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v822 : sv v822 = sv v806 * sv v806 := e_smx_sq 29 h_v806 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v823 : R 1 0 4611686018427387904 4611686018695823391 v823 v823 := (r_srdC hl h_v822 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v823 : sv v823 = -((-sv v822) / 2 ^ 28) := e_srdC h_v822 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v824 : R 1 0 4611686018427387904 4611686018964258878 v824 v824 := (r_sub hl (r_add hl h_v823 h_v823 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v824 : sv v824 = sv v823 + sv v823 := e_add h_v823 h_v823 (of_decide_eq_true rfl)
  have h_v825 : R 1 0 4611686018158952386 4611686018695823360 v825 v825 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v824 (of_decide_eq_true rfl))
  have e_v825 : sv v825 = sv v23 - sv v824 := e_sub h_v23 h_v824 (of_decide_eq_true rfl)
  have h_v826 : R 1 0 0 1 v826 v826 := (r_plt hl h_v825 h_v85 (of_decide_eq_true rfl))
  have e_v826 : (v826 = 1 ↔ sv v825 < sv v85) := e_plt h_v825 h_v85 (of_decide_eq_true rfl)
  have h_v827 : R 1 0 4611686018158952386 4611686018695823360 v827 v827 := (r_psel hl h_v826 h_v85 h_v825 (of_decide_eq_true rfl))
  have e_v827 : v827 = if v826 = 1 then v85 else v825 := e_psel h_v826 h_v85 h_v825 (of_decide_eq_true rfl)
  have h_v828 : R 1 0 4611686018427387904 4683743620518379745 v828 v828 := (r_smx_sq hl 29 h_v805 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  clear h_v0 h_v9 h_v428 h_v430 h_v803 h_v804 h_v813 h_v814 h_v815 h_v823 h_v824 h_v825 h_v826
  have e_v828 : sv v828 = sv v805 * sv v805 := e_smx_sq 29 h_v805 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v829 : R 1 0 4611686018427387904 4611686018695823390 v829 v829 := (r_srdF hl h_v828 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v829 : sv v829 = sv v828 / 2 ^ 28 := e_srdF h_v828 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v830 : R 1 0 4611686018427387904 4611686018964258876 v830 v830 := (r_sub hl (r_add hl h_v829 h_v829 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v830 : sv v830 = sv v829 + sv v829 := e_add h_v829 h_v829 (of_decide_eq_true rfl)
  have h_v831 : R 1 0 4611686018158952388 4611686018695823360 v831 v831 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v830 (of_decide_eq_true rfl))
  have e_v831 : sv v831 = sv v23 - sv v830 := e_sub h_v23 h_v830 (of_decide_eq_true rfl)
  have h_v832 : R 1 0 4611686018427387904 4683743620518379745 v832 v832 := (r_smx_sq hl 29 h_v810 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v832 : sv v832 = sv v810 * sv v810 := e_smx_sq 29 h_v810 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v833 : R 1 0 4611686018427387904 4611686018695823391 v833 v833 := (r_srdC hl h_v832 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v833 : sv v833 = -((-sv v832) / 2 ^ 28) := e_srdC h_v832 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v834 : R 1 0 4611686018427387904 4611686018964258878 v834 v834 := (r_sub hl (r_add hl h_v833 h_v833 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v834 : sv v834 = sv v833 + sv v833 := e_add h_v833 h_v833 (of_decide_eq_true rfl)
  have h_v835 : R 1 0 4611686018158952386 4611686018695823360 v835 v835 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v834 (of_decide_eq_true rfl))
  have e_v835 : sv v835 = sv v23 - sv v834 := e_sub h_v23 h_v834 (of_decide_eq_true rfl)
  have h_v836 : R 1 0 0 1 v836 v836 := (r_plt hl h_v835 h_v85 (of_decide_eq_true rfl))
  have e_v836 : (v836 = 1 ↔ sv v835 < sv v85) := e_plt h_v835 h_v85 (of_decide_eq_true rfl)
  have h_v837 : R 1 0 4611686018158952386 4611686018695823360 v837 v837 := (r_psel hl h_v836 h_v85 h_v835 (of_decide_eq_true rfl))
  have e_v837 : v837 = if v836 = 1 then v85 else v835 := e_psel h_v836 h_v85 h_v835 (of_decide_eq_true rfl)
  have h_v838 : R 1 0 4611686018427387904 4683743620518379745 v838 v838 := (r_smx_sq hl 29 h_v809 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v838 : sv v838 = sv v809 * sv v809 := e_smx_sq 29 h_v809 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v839 : R 1 0 4611686018427387904 4611686018695823390 v839 v839 := (r_srdF hl h_v838 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v839 : sv v839 = sv v838 / 2 ^ 28 := e_srdF h_v838 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v840 : R 1 0 4611686018427387904 4611686018964258876 v840 v840 := (r_sub hl (r_add hl h_v839 h_v839 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v840 : sv v840 = sv v839 + sv v839 := e_add h_v839 h_v839 (of_decide_eq_true rfl)
  clear h_v829 h_v830 h_v833 h_v834 h_v835 h_v836 h_v839
  have h_v841 : R 1 0 4611686018158952388 4611686018695823360 v841 v841 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v840 (of_decide_eq_true rfl))
  have e_v841 : sv v841 = sv v23 - sv v840 := e_sub h_v23 h_v840 (of_decide_eq_true rfl)
  have h_v842 : R 1 0 0 1 v842 v842 := (r_plt hl h_v827 h_v51 (of_decide_eq_true rfl))
  have e_v842 : (v842 = 1 ↔ sv v827 < sv v51) := e_plt h_v827 h_v51 (of_decide_eq_true rfl)
  have h_v843 : R 1 0 0 1 v843 v843 := (r_sub hl (r_O hl) h_v842 (of_decide_eq_true rfl))
  have e_v843 : (v843 = 1 ↔ ¬v842 = 1) := e_not h_v842 (of_decide_eq_true rfl)
  have h_v844 : R 1 0 0 1 v844 v844 := (r_plt hl h_v51 h_v831 (of_decide_eq_true rfl))
  have e_v844 : (v844 = 1 ↔ sv v51 < sv v831) := e_plt h_v51 h_v831 (of_decide_eq_true rfl)
  have h_v845 : R 1 0 0 1 v845 v845 := (r_sub hl (r_O hl) h_v844 (of_decide_eq_true rfl))
  have e_v845 : (v845 = 1 ↔ ¬v844 = 1) := e_not h_v844 (of_decide_eq_true rfl)
  have h_v846 : R 1 0 0 1 v846 v846 := (r_land hl h_v842 h_v845 (of_decide_eq_true rfl))
  have e_v846 : (v846 = 1 ↔ v842 = 1 ∧ v845 = 1) := e_land h_v842 h_v845 (of_decide_eq_true rfl)
  have h_v847 : R 1 0 0 1 v847 v847 := (r_land hl h_v842 h_v844 (of_decide_eq_true rfl))
  have e_v847 : (v847 = 1 ↔ v842 = 1 ∧ v844 = 1) := e_land h_v842 h_v844 (of_decide_eq_true rfl)
  have h_v848 : R 1 0 0 1 v848 v848 := (r_plt hl h_v837 h_v51 (of_decide_eq_true rfl))
  have e_v848 : (v848 = 1 ↔ sv v837 < sv v51) := e_plt h_v837 h_v51 (of_decide_eq_true rfl)
  have h_v849 : R 1 0 0 1 v849 v849 := (r_sub hl (r_O hl) h_v848 (of_decide_eq_true rfl))
  have e_v849 : (v849 = 1 ↔ ¬v848 = 1) := e_not h_v848 (of_decide_eq_true rfl)
  have h_v850 : R 1 0 0 1 v850 v850 := (r_plt hl h_v51 h_v841 (of_decide_eq_true rfl))
  have e_v850 : (v850 = 1 ↔ sv v51 < sv v841) := e_plt h_v51 h_v841 (of_decide_eq_true rfl)
  have h_v851 : R 1 0 0 1 v851 v851 := (r_sub hl (r_O hl) h_v850 (of_decide_eq_true rfl))
  have e_v851 : (v851 = 1 ↔ ¬v850 = 1) := e_not h_v850 (of_decide_eq_true rfl)
  have h_v852 : R 1 0 0 1 v852 v852 := (r_land hl h_v848 h_v851 (of_decide_eq_true rfl))
  have e_v852 : (v852 = 1 ↔ v848 = 1 ∧ v851 = 1) := e_land h_v848 h_v851 (of_decide_eq_true rfl)
  have h_v853 : R 1 0 0 1 v853 v853 := (r_land hl h_v848 h_v850 (of_decide_eq_true rfl))
  clear h_v840 h_v842 h_v844 h_v845 h_v851
  have e_v853 : (v853 = 1 ↔ v848 = 1 ∧ v850 = 1) := e_land h_v848 h_v850 (of_decide_eq_true rfl)
  have h_v854 : R 1 0 0 1 v854 v854 := (r_land hl h_v847 h_v853 (of_decide_eq_true rfl))
  have e_v854 : (v854 = 1 ↔ v847 = 1 ∧ v853 = 1) := e_land h_v847 h_v853 (of_decide_eq_true rfl)
  have h_v855 : R 1 0 0 1 v855 v855 := (r_sub hl (r_O hl) h_v854 (of_decide_eq_true rfl))
  have e_v855 : (v855 = 1 ↔ ¬v854 = 1) := e_not h_v854 (of_decide_eq_true rfl)
  have h_v856 : R 1 0 0 1 v856 v856 := (r_lor hl h_v725 h_v855 (of_decide_eq_true rfl))
  have e_v856 : (v856 = 1 ↔ v725 = 1 ∨ v855 = 1) := e_lor h_v725 h_v855 (of_decide_eq_true rfl)
  have h_v857 : R 1 0 0 1 v857 v857 := (r_land hl h_v843 h_v853 (of_decide_eq_true rfl))
  have e_v857 : (v857 = 1 ↔ v843 = 1 ∧ v853 = 1) := e_land h_v843 h_v853 (of_decide_eq_true rfl)
  have h_v858 : R 1 0 0 1 v858 v858 := (r_lor hl h_v852 h_v857 (of_decide_eq_true rfl))
  have e_v858 : (v858 = 1 ↔ v852 = 1 ∨ v857 = 1) := e_lor h_v852 h_v857 (of_decide_eq_true rfl)
  have h_v859 : R 1 0 4611686018158952386 4611686018695823360 v859 v859 := (r_psel hl h_v858 h_v831 h_v827 (of_decide_eq_true rfl))
  have e_v859 : v859 = if v858 = 1 then v831 else v827 := e_psel h_v858 h_v831 h_v827 (of_decide_eq_true rfl)
  have h_v860 : R 1 0 0 1 v860 v860 := (r_land hl h_v847 h_v849 (of_decide_eq_true rfl))
  have e_v860 : (v860 = 1 ↔ v847 = 1 ∧ v849 = 1) := e_land h_v847 h_v849 (of_decide_eq_true rfl)
  have h_v861 : R 1 0 0 1 v861 v861 := (r_lor hl h_v846 h_v860 (of_decide_eq_true rfl))
  have e_v861 : (v861 = 1 ↔ v846 = 1 ∨ v860 = 1) := e_lor h_v846 h_v860 (of_decide_eq_true rfl)
  have h_v862 : R 1 0 4611686018158952386 4611686018695823360 v862 v862 := (r_psel hl h_v861 h_v841 h_v837 (of_decide_eq_true rfl))
  have e_v862 : v862 = if v861 = 1 then v841 else v837 := e_psel h_v861 h_v841 h_v837 (of_decide_eq_true rfl)
  have h_v869 : R 1 0 4539628407746461696 4683743645751316228 v869 v869 := (r_smx hl 30 h_v862 h_v859 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v869 : sv v869 = sv v862 * sv v859 := e_smx 30 h_v862 h_v859 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v870 : R 1 0 4611686018158952386 4611686018695823484 v870 v870 := (r_srdF hl h_v869 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v870 : sv v870 = sv v869 / 2 ^ 28 := e_srdF h_v869 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v874 : R 1 0 4611686017890516869 4611686018964258885 v874 v874 := (r_sub hl (r_add hl h_v97 h_OFFr (of_decide_eq_true rfl)) h_v870 (of_decide_eq_true rfl))
  have e_v874 : sv v874 = sv v97 - sv v870 := e_sub h_v97 h_v870 (of_decide_eq_true rfl)
  clear h_v97 h_v827 h_v831 h_v837 h_v841 h_v843 h_v846 h_v847 h_v848 h_v849 h_v850 h_v852 h_v853 h_v854 h_v855 h_v857 h_v858 h_v859 h_v860 h_v861 h_v862 h_v869 h_v870
  have h_v875 : R 1 0 4683743612465315840 4683743612465315840 v875 v875 := (r_c hl 4683743612465315840 (of_decide_eq_true rfl))
  have e_v875 : sv v875 = (72057594037927936) := e_c 4683743612465315840 (72057594037927936) (of_decide_eq_true rfl)
  have h_v876 : R 1 0 4611686010374323999 4683743612465315840 v876 v876 := (r_sub hl (r_add hl h_v875 h_OFFr (of_decide_eq_true rfl)) h_v828 (of_decide_eq_true rfl))
  have e_v876 : sv v876 = sv v875 - sv v828 := e_sub h_v875 h_v828 (of_decide_eq_true rfl)
  have h_v877 : R 1 0 4611686018427387904 4611686018695823360 v877 v877 := (r_psqrt hl h_v876 (of_decide_eq_true rfl))
  have e_v877 : sv v877 = ((Nat.sqrt (v876 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v876 (of_decide_eq_true rfl)
  have h_v878 : R 1 0 4611686018427387905 4611686018695823361 v878 v878 := (r_sub hl (r_add hl h_v95 h_v877 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v878 : sv v878 = sv v95 + sv v877 := e_add h_v95 h_v877 (of_decide_eq_true rfl)
  have pb_v877_v805 : PB 1 v877 v805 36028797018963968 := pb_sqrt hl h_v805 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v879 : R 1 0 4611686017085210624 4647714815446351872 v879 v879 := (r_smx_pb hl 29 h_v877 h_v805 pb_v877_v805 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v879 : sv v879 = sv v877 * sv v805 := e_smx_pb 29 h_v877 h_v805 pb_v877_v805 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v880 : R 1 0 4611686018427387899 4611686018561605632 v880 v880 := (r_srdF hl h_v879 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v880 : sv v880 = sv v879 / 2 ^ 28 := e_srdF h_v879 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v881 : R 1 0 4611686018427387894 4611686018695823360 v881 v881 := (r_sub hl (r_add hl h_v880 h_v880 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v881 : sv v881 = sv v880 + sv v880 := e_add h_v880 h_v880 (of_decide_eq_true rfl)
  have pb_v878_v805 : PB 1 v878 v805 36028797287399439 := pb_sqrt1 hl h_v805 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v882 : R 1 0 4611686017085210619 4647714815714787343 v882 v882 := (r_smx_pb hl 29 h_v878 h_v805 pb_v878_v805 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v882 : sv v882 = sv v878 * sv v805 := e_smx_pb 29 h_v878 h_v805 pb_v878_v805 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v883 : R 1 0 4611686018427387899 4611686018561605634 v883 v883 := (r_srdC hl h_v882 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v883 : sv v883 = -((-sv v882) / 2 ^ 28) := e_srdC h_v882 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v884 : R 1 0 4611686018427387894 4611686018695823364 v884 v884 := (r_sub hl (r_add hl h_v883 h_v883 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v884 : sv v884 = sv v883 + sv v883 := e_add h_v883 h_v883 (of_decide_eq_true rfl)
  have h_v885 : R 1 0 0 1 v885 v885 := (r_plt hl h_v884 h_v23 (of_decide_eq_true rfl))
  have e_v885 : (v885 = 1 ↔ sv v884 < sv v23) := e_plt h_v884 h_v23 (of_decide_eq_true rfl)
  have h_v886 : R 1 0 4611686018427387894 4611686018695823364 v886 v886 := (r_psel hl h_v885 h_v884 h_v23 (of_decide_eq_true rfl))
  clear h_v805 h_v876 h_v877 h_v878 pb_v877_v805 h_v879 h_v880 pb_v878_v805 h_v882 h_v883
  have e_v886 : v886 = if v885 = 1 then v884 else v23 := e_psel h_v885 h_v884 h_v23 (of_decide_eq_true rfl)
  have h_v887 : R 1 0 4611686010374323999 4683743612465315840 v887 v887 := (r_sub hl (r_add hl h_v875 h_OFFr (of_decide_eq_true rfl)) h_v822 (of_decide_eq_true rfl))
  have e_v887 : sv v887 = sv v875 - sv v822 := e_sub h_v875 h_v822 (of_decide_eq_true rfl)
  have h_v888 : R 1 0 4611686018427387904 4611686018695823360 v888 v888 := (r_psqrt hl h_v887 (of_decide_eq_true rfl))
  have e_v888 : sv v888 = ((Nat.sqrt (v887 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v887 (of_decide_eq_true rfl)
  have h_v889 : R 1 0 4611686018427387905 4611686018695823361 v889 v889 := (r_sub hl (r_add hl h_v95 h_v888 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v889 : sv v889 = sv v95 + sv v888 := e_add h_v95 h_v888 (of_decide_eq_true rfl)
  have pb_v888_v806 : PB 1 v888 v806 36028797018963968 := pb_sqrt hl h_v806 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v890 : R 1 0 4611686017085210624 4647714815446351872 v890 v890 := (r_smx_pb hl 29 h_v888 h_v806 pb_v888_v806 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v890 : sv v890 = sv v888 * sv v806 := e_smx_pb 29 h_v888 h_v806 pb_v888_v806 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v891 : R 1 0 4611686018427387899 4611686018561605632 v891 v891 := (r_srdF hl h_v890 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v891 : sv v891 = sv v890 / 2 ^ 28 := e_srdF h_v890 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v892 : R 1 0 4611686018427387894 4611686018695823360 v892 v892 := (r_sub hl (r_add hl h_v891 h_v891 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v892 : sv v892 = sv v891 + sv v891 := e_add h_v891 h_v891 (of_decide_eq_true rfl)
  have pb_v889_v806 : PB 1 v889 v806 36028797287399439 := pb_sqrt1 hl h_v806 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v893 : R 1 0 4611686017085210619 4647714815714787343 v893 v893 := (r_smx_pb hl 29 h_v889 h_v806 pb_v889_v806 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v893 : sv v893 = sv v889 * sv v806 := e_smx_pb 29 h_v889 h_v806 pb_v889_v806 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v894 : R 1 0 4611686018427387899 4611686018561605634 v894 v894 := (r_srdC hl h_v893 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v894 : sv v894 = -((-sv v893) / 2 ^ 28) := e_srdC h_v893 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v895 : R 1 0 4611686018427387894 4611686018695823364 v895 v895 := (r_sub hl (r_add hl h_v894 h_v894 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v895 : sv v895 = sv v894 + sv v894 := e_add h_v894 h_v894 (of_decide_eq_true rfl)
  have h_v896 : R 1 0 0 1 v896 v896 := (r_plt hl h_v895 h_v23 (of_decide_eq_true rfl))
  have e_v896 : (v896 = 1 ↔ sv v895 < sv v23) := e_plt h_v895 h_v23 (of_decide_eq_true rfl)
  have h_v897 : R 1 0 4611686018427387894 4611686018695823364 v897 v897 := (r_psel hl h_v896 h_v895 h_v23 (of_decide_eq_true rfl))
  have e_v897 : v897 = if v896 = 1 then v895 else v23 := e_psel h_v896 h_v895 h_v23 (of_decide_eq_true rfl)
  clear h_v806 h_v884 h_v885 h_v887 h_v888 h_v889 pb_v888_v806 h_v890 h_v891 pb_v889_v806 h_v893 h_v894 h_v895 h_v896
  have h_v898 : R 1 0 0 1 v898 v898 := (r_plt hl h_v881 h_v892 (of_decide_eq_true rfl))
  have e_v898 : (v898 = 1 ↔ sv v881 < sv v892) := e_plt h_v881 h_v892 (of_decide_eq_true rfl)
  have h_v899 : R 1 0 4611686018427387894 4611686018695823360 v899 v899 := (r_psel hl h_v898 h_v881 h_v892 (of_decide_eq_true rfl))
  have e_v899 : v899 = if v898 = 1 then v881 else v892 := e_psel h_v898 h_v881 h_v892 (of_decide_eq_true rfl)
  have h_v900 : R 1 0 0 1 v900 v900 := (r_plt hl h_v886 h_v897 (of_decide_eq_true rfl))
  have e_v900 : (v900 = 1 ↔ sv v886 < sv v897) := e_plt h_v886 h_v897 (of_decide_eq_true rfl)
  have h_v901 : R 1 0 4611686018427387894 4611686018695823364 v901 v901 := (r_psel hl h_v900 h_v897 h_v886 (of_decide_eq_true rfl))
  have e_v901 : v901 = if v900 = 1 then v897 else v886 := e_psel h_v900 h_v897 h_v886 (of_decide_eq_true rfl)
  have h_v902 : R 1 0 4647714815446351872 4647714815446351872 v902 v902 := (r_c hl 4647714815446351872 (of_decide_eq_true rfl))
  have e_v902 : sv v902 = (36028797018963968) := e_c 4647714815446351872 (36028797018963968) (of_decide_eq_true rfl)
  have h_v903 : R 1 0 0 1 v903 v903 := (r_plt hl h_v902 h_v828 (of_decide_eq_true rfl))
  have e_v903 : (v903 = 1 ↔ sv v902 < sv v828) := e_plt h_v902 h_v828 (of_decide_eq_true rfl)
  have h_v904 : R 1 0 0 1 v904 v904 := (r_sub hl (r_O hl) h_v903 (of_decide_eq_true rfl))
  have e_v904 : (v904 = 1 ↔ ¬v903 = 1) := e_not h_v903 (of_decide_eq_true rfl)
  have h_v905 : R 1 0 0 1 v905 v905 := (r_plt hl h_v822 h_v902 (of_decide_eq_true rfl))
  have e_v905 : (v905 = 1 ↔ sv v822 < sv v902) := e_plt h_v822 h_v902 (of_decide_eq_true rfl)
  have h_v906 : R 1 0 0 1 v906 v906 := (r_sub hl (r_O hl) h_v905 (of_decide_eq_true rfl))
  have e_v906 : (v906 = 1 ↔ ¬v905 = 1) := e_not h_v905 (of_decide_eq_true rfl)
  have h_v907 : R 1 0 0 1 v907 v907 := (r_land hl h_v904 h_v906 (of_decide_eq_true rfl))
  have e_v907 : (v907 = 1 ↔ v904 = 1 ∧ v906 = 1) := e_land h_v904 h_v906 (of_decide_eq_true rfl)
  have h_v908 : R 1 0 4611686018427387894 4611686018695823364 v908 v908 := (r_psel hl h_v907 h_v23 h_v901 (of_decide_eq_true rfl))
  have e_v908 : v908 = if v907 = 1 then v23 else v901 := e_psel h_v907 h_v23 h_v901 (of_decide_eq_true rfl)
  have h_v909 : R 1 0 4611686010374323999 4683743612465315840 v909 v909 := (r_sub hl (r_add hl h_v875 h_OFFr (of_decide_eq_true rfl)) h_v838 (of_decide_eq_true rfl))
  have e_v909 : sv v909 = sv v875 - sv v838 := e_sub h_v875 h_v838 (of_decide_eq_true rfl)
  have h_v910 : R 1 0 4611686018427387904 4611686018695823360 v910 v910 := (r_psqrt hl h_v909 (of_decide_eq_true rfl))
  clear h_v822 h_v828 h_v881 h_v886 h_v892 h_v897 h_v898 h_v900 h_v901 h_v903 h_v904 h_v905 h_v906 h_v907
  have e_v910 : sv v910 = ((Nat.sqrt (v909 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v909 (of_decide_eq_true rfl)
  have h_v911 : R 1 0 4611686018427387905 4611686018695823361 v911 v911 := (r_sub hl (r_add hl h_v95 h_v910 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v911 : sv v911 = sv v95 + sv v910 := e_add h_v95 h_v910 (of_decide_eq_true rfl)
  have pb_v910_v809 : PB 1 v910 v809 36028797018963968 := pb_sqrt hl h_v809 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v912 : R 1 0 4611686017085210624 4647714815446351872 v912 v912 := (r_smx_pb hl 29 h_v910 h_v809 pb_v910_v809 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v912 : sv v912 = sv v910 * sv v809 := e_smx_pb 29 h_v910 h_v809 pb_v910_v809 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v913 : R 1 0 4611686018427387899 4611686018561605632 v913 v913 := (r_srdF hl h_v912 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v913 : sv v913 = sv v912 / 2 ^ 28 := e_srdF h_v912 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v914 : R 1 0 4611686018427387894 4611686018695823360 v914 v914 := (r_sub hl (r_add hl h_v913 h_v913 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v914 : sv v914 = sv v913 + sv v913 := e_add h_v913 h_v913 (of_decide_eq_true rfl)
  have pb_v911_v809 : PB 1 v911 v809 36028797287399439 := pb_sqrt1 hl h_v809 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v915 : R 1 0 4611686017085210619 4647714815714787343 v915 v915 := (r_smx_pb hl 29 h_v911 h_v809 pb_v911_v809 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v915 : sv v915 = sv v911 * sv v809 := e_smx_pb 29 h_v911 h_v809 pb_v911_v809 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v916 : R 1 0 4611686018427387899 4611686018561605634 v916 v916 := (r_srdC hl h_v915 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v916 : sv v916 = -((-sv v915) / 2 ^ 28) := e_srdC h_v915 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v917 : R 1 0 4611686018427387894 4611686018695823364 v917 v917 := (r_sub hl (r_add hl h_v916 h_v916 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v917 : sv v917 = sv v916 + sv v916 := e_add h_v916 h_v916 (of_decide_eq_true rfl)
  have h_v918 : R 1 0 0 1 v918 v918 := (r_plt hl h_v917 h_v23 (of_decide_eq_true rfl))
  have e_v918 : (v918 = 1 ↔ sv v917 < sv v23) := e_plt h_v917 h_v23 (of_decide_eq_true rfl)
  have h_v919 : R 1 0 4611686018427387894 4611686018695823364 v919 v919 := (r_psel hl h_v918 h_v917 h_v23 (of_decide_eq_true rfl))
  have e_v919 : v919 = if v918 = 1 then v917 else v23 := e_psel h_v918 h_v917 h_v23 (of_decide_eq_true rfl)
  have h_v920 : R 1 0 4611686010374323999 4683743612465315840 v920 v920 := (r_sub hl (r_add hl h_v875 h_OFFr (of_decide_eq_true rfl)) h_v832 (of_decide_eq_true rfl))
  have e_v920 : sv v920 = sv v875 - sv v832 := e_sub h_v875 h_v832 (of_decide_eq_true rfl)
  have h_v921 : R 1 0 4611686018427387904 4611686018695823360 v921 v921 := (r_psqrt hl h_v920 (of_decide_eq_true rfl))
  have e_v921 : sv v921 = ((Nat.sqrt (v920 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v920 (of_decide_eq_true rfl)
  clear h_v809 h_v909 h_v910 h_v911 pb_v910_v809 h_v912 h_v913 pb_v911_v809 h_v915 h_v916 h_v917 h_v918 h_v920
  have h_v922 : R 1 0 4611686018427387905 4611686018695823361 v922 v922 := (r_sub hl (r_add hl h_v95 h_v921 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v922 : sv v922 = sv v95 + sv v921 := e_add h_v95 h_v921 (of_decide_eq_true rfl)
  have pb_v921_v810 : PB 1 v921 v810 36028797018963968 := pb_sqrt hl h_v810 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v923 : R 1 0 4611686017085210624 4647714815446351872 v923 v923 := (r_smx_pb hl 29 h_v921 h_v810 pb_v921_v810 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v923 : sv v923 = sv v921 * sv v810 := e_smx_pb 29 h_v921 h_v810 pb_v921_v810 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v924 : R 1 0 4611686018427387899 4611686018561605632 v924 v924 := (r_srdF hl h_v923 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v924 : sv v924 = sv v923 / 2 ^ 28 := e_srdF h_v923 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v925 : R 1 0 4611686018427387894 4611686018695823360 v925 v925 := (r_sub hl (r_add hl h_v924 h_v924 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v925 : sv v925 = sv v924 + sv v924 := e_add h_v924 h_v924 (of_decide_eq_true rfl)
  have pb_v922_v810 : PB 1 v922 v810 36028797287399439 := pb_sqrt1 hl h_v810 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v926 : R 1 0 4611686017085210619 4647714815714787343 v926 v926 := (r_smx_pb hl 29 h_v922 h_v810 pb_v922_v810 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v926 : sv v926 = sv v922 * sv v810 := e_smx_pb 29 h_v922 h_v810 pb_v922_v810 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v927 : R 1 0 4611686018427387899 4611686018561605634 v927 v927 := (r_srdC hl h_v926 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v927 : sv v927 = -((-sv v926) / 2 ^ 28) := e_srdC h_v926 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v928 : R 1 0 4611686018427387894 4611686018695823364 v928 v928 := (r_sub hl (r_add hl h_v927 h_v927 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v928 : sv v928 = sv v927 + sv v927 := e_add h_v927 h_v927 (of_decide_eq_true rfl)
  have h_v929 : R 1 0 0 1 v929 v929 := (r_plt hl h_v928 h_v23 (of_decide_eq_true rfl))
  have e_v929 : (v929 = 1 ↔ sv v928 < sv v23) := e_plt h_v928 h_v23 (of_decide_eq_true rfl)
  have h_v930 : R 1 0 4611686018427387894 4611686018695823364 v930 v930 := (r_psel hl h_v929 h_v928 h_v23 (of_decide_eq_true rfl))
  have e_v930 : v930 = if v929 = 1 then v928 else v23 := e_psel h_v929 h_v928 h_v23 (of_decide_eq_true rfl)
  have h_v931 : R 1 0 0 1 v931 v931 := (r_plt hl h_v914 h_v925 (of_decide_eq_true rfl))
  have e_v931 : (v931 = 1 ↔ sv v914 < sv v925) := e_plt h_v914 h_v925 (of_decide_eq_true rfl)
  have h_v932 : R 1 0 4611686018427387894 4611686018695823360 v932 v932 := (r_psel hl h_v931 h_v914 h_v925 (of_decide_eq_true rfl))
  have e_v932 : v932 = if v931 = 1 then v914 else v925 := e_psel h_v931 h_v914 h_v925 (of_decide_eq_true rfl)
  have h_v933 : R 1 0 0 1 v933 v933 := (r_plt hl h_v919 h_v930 (of_decide_eq_true rfl))
  clear h_v810 h_v914 h_v921 h_v922 pb_v921_v810 h_v923 h_v924 h_v925 pb_v922_v810 h_v926 h_v927 h_v928 h_v929 h_v931
  have e_v933 : (v933 = 1 ↔ sv v919 < sv v930) := e_plt h_v919 h_v930 (of_decide_eq_true rfl)
  have h_v934 : R 1 0 4611686018427387894 4611686018695823364 v934 v934 := (r_psel hl h_v933 h_v930 h_v919 (of_decide_eq_true rfl))
  have e_v934 : v934 = if v933 = 1 then v930 else v919 := e_psel h_v933 h_v930 h_v919 (of_decide_eq_true rfl)
  have h_v935 : R 1 0 0 1 v935 v935 := (r_plt hl h_v902 h_v838 (of_decide_eq_true rfl))
  have e_v935 : (v935 = 1 ↔ sv v902 < sv v838) := e_plt h_v902 h_v838 (of_decide_eq_true rfl)
  have h_v936 : R 1 0 0 1 v936 v936 := (r_sub hl (r_O hl) h_v935 (of_decide_eq_true rfl))
  have e_v936 : (v936 = 1 ↔ ¬v935 = 1) := e_not h_v935 (of_decide_eq_true rfl)
  have h_v937 : R 1 0 0 1 v937 v937 := (r_plt hl h_v832 h_v902 (of_decide_eq_true rfl))
  have e_v937 : (v937 = 1 ↔ sv v832 < sv v902) := e_plt h_v832 h_v902 (of_decide_eq_true rfl)
  have h_v938 : R 1 0 0 1 v938 v938 := (r_sub hl (r_O hl) h_v937 (of_decide_eq_true rfl))
  have e_v938 : (v938 = 1 ↔ ¬v937 = 1) := e_not h_v937 (of_decide_eq_true rfl)
  have h_v939 : R 1 0 0 1 v939 v939 := (r_land hl h_v936 h_v938 (of_decide_eq_true rfl))
  have e_v939 : (v939 = 1 ↔ v936 = 1 ∧ v938 = 1) := e_land h_v936 h_v938 (of_decide_eq_true rfl)
  have h_v940 : R 1 0 4611686018427387894 4611686018695823364 v940 v940 := (r_psel hl h_v939 h_v23 h_v934 (of_decide_eq_true rfl))
  have e_v940 : v940 = if v939 = 1 then v23 else v934 := e_psel h_v939 h_v23 h_v934 (of_decide_eq_true rfl)
  have h_v941 : R 1 0 0 1 v941 v941 := (r_plt hl h_v899 h_v51 (of_decide_eq_true rfl))
  have e_v941 : (v941 = 1 ↔ sv v899 < sv v51) := e_plt h_v899 h_v51 (of_decide_eq_true rfl)
  have h_v942 : R 1 0 0 1 v942 v942 := (r_sub hl (r_O hl) h_v941 (of_decide_eq_true rfl))
  have e_v942 : (v942 = 1 ↔ ¬v941 = 1) := e_not h_v941 (of_decide_eq_true rfl)
  have h_v943 : R 1 0 0 1 v943 v943 := (r_plt hl h_v51 h_v908 (of_decide_eq_true rfl))
  have e_v943 : (v943 = 1 ↔ sv v51 < sv v908) := e_plt h_v51 h_v908 (of_decide_eq_true rfl)
  have h_v944 : R 1 0 0 1 v944 v944 := (r_sub hl (r_O hl) h_v943 (of_decide_eq_true rfl))
  have e_v944 : (v944 = 1 ↔ ¬v943 = 1) := e_not h_v943 (of_decide_eq_true rfl)
  have h_v945 : R 1 0 0 1 v945 v945 := (r_land hl h_v941 h_v944 (of_decide_eq_true rfl))
  have e_v945 : (v945 = 1 ↔ v941 = 1 ∧ v944 = 1) := e_land h_v941 h_v944 (of_decide_eq_true rfl)
  clear h_v832 h_v838 h_v919 h_v930 h_v933 h_v934 h_v935 h_v936 h_v937 h_v938 h_v939 h_v944
  have h_v946 : R 1 0 0 1 v946 v946 := (r_land hl h_v941 h_v943 (of_decide_eq_true rfl))
  have e_v946 : (v946 = 1 ↔ v941 = 1 ∧ v943 = 1) := e_land h_v941 h_v943 (of_decide_eq_true rfl)
  have h_v947 : R 1 0 0 1 v947 v947 := (r_plt hl h_v932 h_v51 (of_decide_eq_true rfl))
  have e_v947 : (v947 = 1 ↔ sv v932 < sv v51) := e_plt h_v932 h_v51 (of_decide_eq_true rfl)
  have h_v948 : R 1 0 0 1 v948 v948 := (r_sub hl (r_O hl) h_v947 (of_decide_eq_true rfl))
  have e_v948 : (v948 = 1 ↔ ¬v947 = 1) := e_not h_v947 (of_decide_eq_true rfl)
  have h_v949 : R 1 0 0 1 v949 v949 := (r_plt hl h_v51 h_v940 (of_decide_eq_true rfl))
  have e_v949 : (v949 = 1 ↔ sv v51 < sv v940) := e_plt h_v51 h_v940 (of_decide_eq_true rfl)
  have h_v950 : R 1 0 0 1 v950 v950 := (r_sub hl (r_O hl) h_v949 (of_decide_eq_true rfl))
  have e_v950 : (v950 = 1 ↔ ¬v949 = 1) := e_not h_v949 (of_decide_eq_true rfl)
  have h_v951 : R 1 0 0 1 v951 v951 := (r_land hl h_v947 h_v950 (of_decide_eq_true rfl))
  have e_v951 : (v951 = 1 ↔ v947 = 1 ∧ v950 = 1) := e_land h_v947 h_v950 (of_decide_eq_true rfl)
  have h_v952 : R 1 0 0 1 v952 v952 := (r_land hl h_v947 h_v949 (of_decide_eq_true rfl))
  have e_v952 : (v952 = 1 ↔ v947 = 1 ∧ v949 = 1) := e_land h_v947 h_v949 (of_decide_eq_true rfl)
  have h_v953 : R 1 0 0 1 v953 v953 := (r_land hl h_v946 h_v952 (of_decide_eq_true rfl))
  have e_v953 : (v953 = 1 ↔ v946 = 1 ∧ v952 = 1) := e_land h_v946 h_v952 (of_decide_eq_true rfl)
  have h_v954 : R 1 0 0 1 v954 v954 := (r_sub hl (r_O hl) h_v953 (of_decide_eq_true rfl))
  have e_v954 : (v954 = 1 ↔ ¬v953 = 1) := e_not h_v953 (of_decide_eq_true rfl)
  have h_v955 : R 1 0 0 1 v955 v955 := (r_lor hl h_v725 h_v954 (of_decide_eq_true rfl))
  have e_v955 : (v955 = 1 ↔ v725 = 1 ∨ v954 = 1) := e_lor h_v725 h_v954 (of_decide_eq_true rfl)
  have h_v956 : R 1 0 0 1 v956 v956 := (r_land hl h_v942 h_v952 (of_decide_eq_true rfl))
  have e_v956 : (v956 = 1 ↔ v942 = 1 ∧ v952 = 1) := e_land h_v942 h_v952 (of_decide_eq_true rfl)
  have h_v957 : R 1 0 0 1 v957 v957 := (r_lor hl h_v951 h_v956 (of_decide_eq_true rfl))
  have e_v957 : (v957 = 1 ↔ v951 = 1 ∨ v956 = 1) := e_lor h_v951 h_v956 (of_decide_eq_true rfl)
  have h_v958 : R 1 0 4611686018427387894 4611686018695823364 v958 v958 := (r_psel hl h_v957 h_v908 h_v899 (of_decide_eq_true rfl))
  clear h_v941 h_v942 h_v943 h_v947 h_v949 h_v950 h_v953 h_v954 h_v956
  have e_v958 : v958 = if v957 = 1 then v908 else v899 := e_psel h_v957 h_v908 h_v899 (of_decide_eq_true rfl)
  have h_v959 : R 1 0 0 1 v959 v959 := (r_land hl h_v946 h_v948 (of_decide_eq_true rfl))
  have e_v959 : (v959 = 1 ↔ v946 = 1 ∧ v948 = 1) := e_land h_v946 h_v948 (of_decide_eq_true rfl)
  have h_v960 : R 1 0 0 1 v960 v960 := (r_lor hl h_v945 h_v959 (of_decide_eq_true rfl))
  have e_v960 : (v960 = 1 ↔ v945 = 1 ∨ v959 = 1) := e_lor h_v945 h_v959 (of_decide_eq_true rfl)
  have h_v961 : R 1 0 4611686018427387894 4611686018695823364 v961 v961 := (r_psel hl h_v960 h_v940 h_v932 (of_decide_eq_true rfl))
  have e_v961 : v961 = if v960 = 1 then v940 else v932 := e_psel h_v960 h_v940 h_v932 (of_decide_eq_true rfl)
  have h_v962 : R 1 0 0 1 v962 v962 := (r_land hl h_v945 h_v952 (of_decide_eq_true rfl))
  have e_v962 : (v962 = 1 ↔ v945 = 1 ∧ v952 = 1) := e_land h_v945 h_v952 (of_decide_eq_true rfl)
  have h_v963 : R 1 0 0 1 v963 v963 := (r_lor hl h_v951 h_v962 (of_decide_eq_true rfl))
  have e_v963 : (v963 = 1 ↔ v951 = 1 ∨ v962 = 1) := e_lor h_v951 h_v962 (of_decide_eq_true rfl)
  have h_v964 : R 1 0 4611686018427387894 4611686018695823364 v964 v964 := (r_psel hl h_v963 h_v899 h_v908 (of_decide_eq_true rfl))
  have e_v964 : v964 = if v963 = 1 then v899 else v908 := e_psel h_v963 h_v899 h_v908 (of_decide_eq_true rfl)
  have h_v965 : R 1 0 0 1 v965 v965 := (r_land hl h_v946 h_v951 (of_decide_eq_true rfl))
  have e_v965 : (v965 = 1 ↔ v946 = 1 ∧ v951 = 1) := e_land h_v946 h_v951 (of_decide_eq_true rfl)
  have h_v966 : R 1 0 0 1 v966 v966 := (r_lor hl h_v945 h_v965 (of_decide_eq_true rfl))
  have e_v966 : (v966 = 1 ↔ v945 = 1 ∨ v965 = 1) := e_lor h_v945 h_v965 (of_decide_eq_true rfl)
  have h_v967 : R 1 0 4611686018427387894 4611686018695823364 v967 v967 := (r_psel hl h_v966 h_v932 h_v940 (of_decide_eq_true rfl))
  have e_v967 : v967 = if v966 = 1 then v932 else v940 := e_psel h_v966 h_v932 h_v940 (of_decide_eq_true rfl)
  have h_v968 : R 1 0 4611686015743033304 4683743614612799504 v968 v968 := (r_smx hl 29 h_v961 h_v958 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v968 : sv v968 = sv v961 * sv v958 := e_smx 29 h_v961 h_v958 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v969 : R 1 0 4611686018427387893 4611686018695823368 v969 v969 := (r_srdF hl h_v968 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v969 : sv v969 = sv v968 / 2 ^ 28 := e_srdF h_v968 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v970 : R 1 0 4611686015743033304 4683743614612799504 v970 v970 := (r_smx hl 29 h_v967 h_v964 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v970 : sv v970 = sv v967 * sv v964 := e_smx 29 h_v967 h_v964 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  clear h_v899 h_v908 h_v932 h_v940 h_v945 h_v946 h_v948 h_v951 h_v952 h_v957 h_v958 h_v959 h_v960 h_v961 h_v962 h_v963 h_v964 h_v965 h_v966 h_v967 h_v968
  have h_v971 : R 1 0 4611686018427387894 4611686018695823369 v971 v971 := (r_srdC hl h_v970 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v971 : sv v971 = -((-sv v970) / 2 ^ 28) := e_srdC h_v970 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v972 : R 1 0 0 1 v972 v972 := (r_plt hl h_v51 h_v969 (of_decide_eq_true rfl))
  have e_v972 : (v972 = 1 ↔ sv v51 < sv v969) := e_plt h_v51 h_v969 (of_decide_eq_true rfl)
  have h_v976 : R 1 0 0 1 v976 v976 := (r_plt hl h_v874 h_v51 (of_decide_eq_true rfl))
  have e_v976 : (v976 = 1 ↔ sv v874 < sv v51) := e_plt h_v874 h_v51 (of_decide_eq_true rfl)
  have h_v977 : R 1 0 4611686018427387893 4611686018695823369 v977 v977 := (r_psel hl h_v976 h_v971 h_v969 (of_decide_eq_true rfl))
  have e_v977 : v977 = if v976 = 1 then v971 else v969 := e_psel h_v976 h_v971 h_v969 (of_decide_eq_true rfl)
  have h_v978 : R 1 0 4611686018158952439 4611686018427387915 v978 v978 := (r_sub hl (r_add hl h_v51 h_OFFr (of_decide_eq_true rfl)) h_v977 (of_decide_eq_true rfl))
  have e_v978 : sv v978 = sv v51 - sv v977 := e_sub h_v51 h_v977 (of_decide_eq_true rfl)
  have h_v979 : R 1 0 0 1 v979 v979 := (r_plt hl h_v874 h_v978 (of_decide_eq_true rfl))
  have e_v979 : (v979 = 1 ↔ sv v874 < sv v978) := e_plt h_v874 h_v978 (of_decide_eq_true rfl)
  have h_v980 : R 1 0 0 1 v980 v980 := (r_land hl h_v972 h_v979 (of_decide_eq_true rfl))
  have e_v980 : (v980 = 1 ↔ v972 = 1 ∧ v979 = 1) := e_land h_v972 h_v979 (of_decide_eq_true rfl)
  have h_v986 : R 1 0 0 1 v986 v986 := (r_plt hl h_v8 h_v1 (of_decide_eq_true rfl))
  have e_v986 : (v986 = 1 ↔ sv v8 < sv v1) := e_plt h_v8 h_v1 (of_decide_eq_true rfl)
  have h_v987 : R 1 0 0 1 v987 v987 := (r_land hl h_v12 h_v986 (of_decide_eq_true rfl))
  have e_v987 : (v987 = 1 ↔ v12 = 1 ∧ v986 = 1) := e_land h_v12 h_v986 (of_decide_eq_true rfl)
  have h_v988 : R 1 0 0 1 v988 v988 := (r_lor hl h_v725 h_v987 (of_decide_eq_true rfl))
  have e_v988 : (v988 = 1 ↔ v725 = 1 ∨ v987 = 1) := e_lor h_v725 h_v987 (of_decide_eq_true rfl)
  have h_v994 : R 1 0 4611686018427387904 4683743620518379745 v994 v994 := (r_smx_sq hl 29 h_v808 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v994 : sv v994 = sv v808 * sv v808 := e_smx_sq 29 h_v808 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v995 : R 1 0 4611686018427387904 4611686018695823391 v995 v995 := (r_srdC hl h_v994 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v995 : sv v995 = -((-sv v994) / 2 ^ 28) := e_srdC h_v994 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v996 : R 1 0 4611686018427387904 4611686018964258878 v996 v996 := (r_sub hl (r_add hl h_v995 h_v995 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v1 h_v8 h_v12 h_v874 h_v969 h_v970 h_v971 h_v972 h_v976 h_v977 h_v978 h_v979 h_v986 h_v987
  have e_v996 : sv v996 = sv v995 + sv v995 := e_add h_v995 h_v995 (of_decide_eq_true rfl)
  have h_v997 : R 1 0 4611686018158952386 4611686018695823360 v997 v997 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v996 (of_decide_eq_true rfl))
  have e_v997 : sv v997 = sv v23 - sv v996 := e_sub h_v23 h_v996 (of_decide_eq_true rfl)
  have h_v998 : R 1 0 0 1 v998 v998 := (r_plt hl h_v997 h_v85 (of_decide_eq_true rfl))
  have e_v998 : (v998 = 1 ↔ sv v997 < sv v85) := e_plt h_v997 h_v85 (of_decide_eq_true rfl)
  have h_v999 : R 1 0 4611686018158952386 4611686018695823360 v999 v999 := (r_psel hl h_v998 h_v85 h_v997 (of_decide_eq_true rfl))
  have e_v999 : v999 = if v998 = 1 then v85 else v997 := e_psel h_v998 h_v85 h_v997 (of_decide_eq_true rfl)
  have h_v1000 : R 1 0 4611686018427387904 4683743620518379745 v1000 v1000 := (r_smx_sq hl 29 h_v807 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1000 : sv v1000 = sv v807 * sv v807 := e_smx_sq 29 h_v807 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1001 : R 1 0 4611686018427387904 4611686018695823390 v1001 v1001 := (r_srdF hl h_v1000 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1001 : sv v1001 = sv v1000 / 2 ^ 28 := e_srdF h_v1000 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1002 : R 1 0 4611686018427387904 4611686018964258876 v1002 v1002 := (r_sub hl (r_add hl h_v1001 h_v1001 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1002 : sv v1002 = sv v1001 + sv v1001 := e_add h_v1001 h_v1001 (of_decide_eq_true rfl)
  have h_v1003 : R 1 0 4611686018158952388 4611686018695823360 v1003 v1003 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v1002 (of_decide_eq_true rfl))
  have e_v1003 : sv v1003 = sv v23 - sv v1002 := e_sub h_v23 h_v1002 (of_decide_eq_true rfl)
  have h_v1004 : R 1 0 4611686018427387904 4683743620518379745 v1004 v1004 := (r_smx_sq hl 29 h_v812 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1004 : sv v1004 = sv v812 * sv v812 := e_smx_sq 29 h_v812 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1005 : R 1 0 4611686018427387904 4611686018695823391 v1005 v1005 := (r_srdC hl h_v1004 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1005 : sv v1005 = -((-sv v1004) / 2 ^ 28) := e_srdC h_v1004 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1006 : R 1 0 4611686018427387904 4611686018964258878 v1006 v1006 := (r_sub hl (r_add hl h_v1005 h_v1005 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1006 : sv v1006 = sv v1005 + sv v1005 := e_add h_v1005 h_v1005 (of_decide_eq_true rfl)
  have h_v1007 : R 1 0 4611686018158952386 4611686018695823360 v1007 v1007 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v1006 (of_decide_eq_true rfl))
  have e_v1007 : sv v1007 = sv v23 - sv v1006 := e_sub h_v23 h_v1006 (of_decide_eq_true rfl)
  have h_v1008 : R 1 0 0 1 v1008 v1008 := (r_plt hl h_v1007 h_v85 (of_decide_eq_true rfl))
  have e_v1008 : (v1008 = 1 ↔ sv v1007 < sv v85) := e_plt h_v1007 h_v85 (of_decide_eq_true rfl)
  clear h_v995 h_v996 h_v997 h_v998 h_v1001 h_v1002 h_v1005 h_v1006
  have h_v1009 : R 1 0 4611686018158952386 4611686018695823360 v1009 v1009 := (r_psel hl h_v1008 h_v85 h_v1007 (of_decide_eq_true rfl))
  have e_v1009 : v1009 = if v1008 = 1 then v85 else v1007 := e_psel h_v1008 h_v85 h_v1007 (of_decide_eq_true rfl)
  have h_v1010 : R 1 0 4611686018427387904 4683743620518379745 v1010 v1010 := (r_smx_sq hl 29 h_v811 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1010 : sv v1010 = sv v811 * sv v811 := e_smx_sq 29 h_v811 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1011 : R 1 0 4611686018427387904 4611686018695823390 v1011 v1011 := (r_srdF hl h_v1010 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1011 : sv v1011 = sv v1010 / 2 ^ 28 := e_srdF h_v1010 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1012 : R 1 0 4611686018427387904 4611686018964258876 v1012 v1012 := (r_sub hl (r_add hl h_v1011 h_v1011 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1012 : sv v1012 = sv v1011 + sv v1011 := e_add h_v1011 h_v1011 (of_decide_eq_true rfl)
  have h_v1013 : R 1 0 4611686018158952388 4611686018695823360 v1013 v1013 := (r_sub hl (r_add hl h_v23 h_OFFr (of_decide_eq_true rfl)) h_v1012 (of_decide_eq_true rfl))
  have e_v1013 : sv v1013 = sv v23 - sv v1012 := e_sub h_v23 h_v1012 (of_decide_eq_true rfl)
  have h_v1014 : R 1 0 0 1 v1014 v1014 := (r_plt hl h_v999 h_v51 (of_decide_eq_true rfl))
  have e_v1014 : (v1014 = 1 ↔ sv v999 < sv v51) := e_plt h_v999 h_v51 (of_decide_eq_true rfl)
  have h_v1016 : R 1 0 0 1 v1016 v1016 := (r_plt hl h_v51 h_v1003 (of_decide_eq_true rfl))
  have e_v1016 : (v1016 = 1 ↔ sv v51 < sv v1003) := e_plt h_v51 h_v1003 (of_decide_eq_true rfl)
  have h_v1017 : R 1 0 0 1 v1017 v1017 := (r_sub hl (r_O hl) h_v1016 (of_decide_eq_true rfl))
  have e_v1017 : (v1017 = 1 ↔ ¬v1016 = 1) := e_not h_v1016 (of_decide_eq_true rfl)
  have h_v1018 : R 1 0 0 1 v1018 v1018 := (r_land hl h_v1014 h_v1017 (of_decide_eq_true rfl))
  have e_v1018 : (v1018 = 1 ↔ v1014 = 1 ∧ v1017 = 1) := e_land h_v1014 h_v1017 (of_decide_eq_true rfl)
  have h_v1019 : R 1 0 0 1 v1019 v1019 := (r_land hl h_v1014 h_v1016 (of_decide_eq_true rfl))
  have e_v1019 : (v1019 = 1 ↔ v1014 = 1 ∧ v1016 = 1) := e_land h_v1014 h_v1016 (of_decide_eq_true rfl)
  have h_v1020 : R 1 0 0 1 v1020 v1020 := (r_plt hl h_v1009 h_v51 (of_decide_eq_true rfl))
  have e_v1020 : (v1020 = 1 ↔ sv v1009 < sv v51) := e_plt h_v1009 h_v51 (of_decide_eq_true rfl)
  have h_v1022 : R 1 0 0 1 v1022 v1022 := (r_plt hl h_v51 h_v1013 (of_decide_eq_true rfl))
  have e_v1022 : (v1022 = 1 ↔ sv v51 < sv v1013) := e_plt h_v51 h_v1013 (of_decide_eq_true rfl)
  have h_v1023 : R 1 0 0 1 v1023 v1023 := (r_sub hl (r_O hl) h_v1022 (of_decide_eq_true rfl))
  clear h_v1007 h_v1008 h_v1011 h_v1012 h_v1014 h_v1016 h_v1017
  have e_v1023 : (v1023 = 1 ↔ ¬v1022 = 1) := e_not h_v1022 (of_decide_eq_true rfl)
  have h_v1024 : R 1 0 0 1 v1024 v1024 := (r_land hl h_v1020 h_v1023 (of_decide_eq_true rfl))
  have e_v1024 : (v1024 = 1 ↔ v1020 = 1 ∧ v1023 = 1) := e_land h_v1020 h_v1023 (of_decide_eq_true rfl)
  have h_v1025 : R 1 0 0 1 v1025 v1025 := (r_land hl h_v1020 h_v1022 (of_decide_eq_true rfl))
  have e_v1025 : (v1025 = 1 ↔ v1020 = 1 ∧ v1022 = 1) := e_land h_v1020 h_v1022 (of_decide_eq_true rfl)
  have h_v1026 : R 1 0 0 1 v1026 v1026 := (r_land hl h_v1019 h_v1025 (of_decide_eq_true rfl))
  have e_v1026 : (v1026 = 1 ↔ v1019 = 1 ∧ v1025 = 1) := e_land h_v1019 h_v1025 (of_decide_eq_true rfl)
  have h_v1027 : R 1 0 0 1 v1027 v1027 := (r_sub hl (r_O hl) h_v1026 (of_decide_eq_true rfl))
  have e_v1027 : (v1027 = 1 ↔ ¬v1026 = 1) := e_not h_v1026 (of_decide_eq_true rfl)
  have h_v1028 : R 1 0 0 1 v1028 v1028 := (r_lor hl h_v725 h_v1027 (of_decide_eq_true rfl))
  have e_v1028 : (v1028 = 1 ↔ v725 = 1 ∨ v1027 = 1) := e_lor h_v725 h_v1027 (of_decide_eq_true rfl)
  have h_v1035 : R 1 0 0 1 v1035 v1035 := (r_land hl h_v1018 h_v1025 (of_decide_eq_true rfl))
  have e_v1035 : (v1035 = 1 ↔ v1018 = 1 ∧ v1025 = 1) := e_land h_v1018 h_v1025 (of_decide_eq_true rfl)
  have h_v1036 : R 1 0 0 1 v1036 v1036 := (r_lor hl h_v1024 h_v1035 (of_decide_eq_true rfl))
  have e_v1036 : (v1036 = 1 ↔ v1024 = 1 ∨ v1035 = 1) := e_lor h_v1024 h_v1035 (of_decide_eq_true rfl)
  have h_v1037 : R 1 0 4611686018158952386 4611686018695823360 v1037 v1037 := (r_psel hl h_v1036 h_v999 h_v1003 (of_decide_eq_true rfl))
  have e_v1037 : v1037 = if v1036 = 1 then v999 else v1003 := e_psel h_v1036 h_v999 h_v1003 (of_decide_eq_true rfl)
  have h_v1038 : R 1 0 0 1 v1038 v1038 := (r_land hl h_v1019 h_v1024 (of_decide_eq_true rfl))
  have e_v1038 : (v1038 = 1 ↔ v1019 = 1 ∧ v1024 = 1) := e_land h_v1019 h_v1024 (of_decide_eq_true rfl)
  have h_v1039 : R 1 0 0 1 v1039 v1039 := (r_lor hl h_v1018 h_v1038 (of_decide_eq_true rfl))
  have e_v1039 : (v1039 = 1 ↔ v1018 = 1 ∨ v1038 = 1) := e_lor h_v1018 h_v1038 (of_decide_eq_true rfl)
  have h_v1040 : R 1 0 4611686018158952386 4611686018695823360 v1040 v1040 := (r_psel hl h_v1039 h_v1009 h_v1013 (of_decide_eq_true rfl))
  have e_v1040 : v1040 = if v1039 = 1 then v1009 else v1013 := e_psel h_v1039 h_v1009 h_v1013 (of_decide_eq_true rfl)
  have h_v1043 : R 1 0 4539628407746461696 4683743645751316228 v1043 v1043 := (r_smx hl 30 h_v1040 h_v1037 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1043 : sv v1043 = sv v1040 * sv v1037 := e_smx 30 h_v1040 h_v1037 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  clear h_v999 h_v1003 h_v1009 h_v1013 h_v1018 h_v1019 h_v1020 h_v1022 h_v1023 h_v1024 h_v1025 h_v1026 h_v1027 h_v1035 h_v1036 h_v1037 h_v1038 h_v1039 h_v1040
  have h_v1044 : R 1 0 4611686018158952386 4611686018695823485 v1044 v1044 := (r_srdC hl h_v1043 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v1044 : sv v1044 = -((-sv v1043) / 2 ^ 28) := e_srdC h_v1043 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v1045 : R 1 0 4611686017890516860 4611686018964258877 v1045 v1045 := (r_sub hl (r_add hl h_v90 h_OFFr (of_decide_eq_true rfl)) h_v1044 (of_decide_eq_true rfl))
  have e_v1045 : sv v1045 = sv v90 - sv v1044 := e_sub h_v90 h_v1044 (of_decide_eq_true rfl)
  have h_v1047 : R 1 0 4611686010374323999 4683743612465315840 v1047 v1047 := (r_sub hl (r_add hl h_v875 h_OFFr (of_decide_eq_true rfl)) h_v1000 (of_decide_eq_true rfl))
  have e_v1047 : sv v1047 = sv v875 - sv v1000 := e_sub h_v875 h_v1000 (of_decide_eq_true rfl)
  have h_v1048 : R 1 0 4611686018427387904 4611686018695823360 v1048 v1048 := (r_psqrt hl h_v1047 (of_decide_eq_true rfl))
  have e_v1048 : sv v1048 = ((Nat.sqrt (v1047 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1047 (of_decide_eq_true rfl)
  have h_v1049 : R 1 0 4611686018427387905 4611686018695823361 v1049 v1049 := (r_sub hl (r_add hl h_v95 h_v1048 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1049 : sv v1049 = sv v95 + sv v1048 := e_add h_v95 h_v1048 (of_decide_eq_true rfl)
  have pb_v1048_v807 : PB 1 v1048 v807 36028797018963968 := pb_sqrt hl h_v807 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1050 : R 1 0 4611686017085210624 4647714815446351872 v1050 v1050 := (r_smx_pb hl 29 h_v1048 h_v807 pb_v1048_v807 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1050 : sv v1050 = sv v1048 * sv v807 := e_smx_pb 29 h_v1048 h_v807 pb_v1048_v807 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1051 : R 1 0 4611686018427387899 4611686018561605632 v1051 v1051 := (r_srdF hl h_v1050 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1051 : sv v1051 = sv v1050 / 2 ^ 28 := e_srdF h_v1050 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1052 : R 1 0 4611686018427387894 4611686018695823360 v1052 v1052 := (r_sub hl (r_add hl h_v1051 h_v1051 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1052 : sv v1052 = sv v1051 + sv v1051 := e_add h_v1051 h_v1051 (of_decide_eq_true rfl)
  have pb_v1049_v807 : PB 1 v1049 v807 36028797287399439 := pb_sqrt1 hl h_v807 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1053 : R 1 0 4611686017085210619 4647714815714787343 v1053 v1053 := (r_smx_pb hl 29 h_v1049 h_v807 pb_v1049_v807 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1053 : sv v1053 = sv v1049 * sv v807 := e_smx_pb 29 h_v1049 h_v807 pb_v1049_v807 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1054 : R 1 0 4611686018427387899 4611686018561605634 v1054 v1054 := (r_srdC hl h_v1053 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1054 : sv v1054 = -((-sv v1053) / 2 ^ 28) := e_srdC h_v1053 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1055 : R 1 0 4611686018427387894 4611686018695823364 v1055 v1055 := (r_sub hl (r_add hl h_v1054 h_v1054 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1055 : sv v1055 = sv v1054 + sv v1054 := e_add h_v1054 h_v1054 (of_decide_eq_true rfl)
  have h_v1056 : R 1 0 0 1 v1056 v1056 := (r_plt hl h_v1055 h_v23 (of_decide_eq_true rfl))
  clear h_v90 h_v807 h_v1043 h_v1044 h_v1047 h_v1048 h_v1049 pb_v1048_v807 h_v1050 h_v1051 pb_v1049_v807 h_v1053 h_v1054
  have e_v1056 : (v1056 = 1 ↔ sv v1055 < sv v23) := e_plt h_v1055 h_v23 (of_decide_eq_true rfl)
  have h_v1057 : R 1 0 4611686018427387894 4611686018695823364 v1057 v1057 := (r_psel hl h_v1056 h_v1055 h_v23 (of_decide_eq_true rfl))
  have e_v1057 : v1057 = if v1056 = 1 then v1055 else v23 := e_psel h_v1056 h_v1055 h_v23 (of_decide_eq_true rfl)
  have h_v1058 : R 1 0 4611686010374323999 4683743612465315840 v1058 v1058 := (r_sub hl (r_add hl h_v875 h_OFFr (of_decide_eq_true rfl)) h_v994 (of_decide_eq_true rfl))
  have e_v1058 : sv v1058 = sv v875 - sv v994 := e_sub h_v875 h_v994 (of_decide_eq_true rfl)
  have h_v1059 : R 1 0 4611686018427387904 4611686018695823360 v1059 v1059 := (r_psqrt hl h_v1058 (of_decide_eq_true rfl))
  have e_v1059 : sv v1059 = ((Nat.sqrt (v1058 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1058 (of_decide_eq_true rfl)
  have h_v1060 : R 1 0 4611686018427387905 4611686018695823361 v1060 v1060 := (r_sub hl (r_add hl h_v95 h_v1059 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1060 : sv v1060 = sv v95 + sv v1059 := e_add h_v95 h_v1059 (of_decide_eq_true rfl)
  have pb_v1059_v808 : PB 1 v1059 v808 36028797018963968 := pb_sqrt hl h_v808 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1061 : R 1 0 4611686017085210624 4647714815446351872 v1061 v1061 := (r_smx_pb hl 29 h_v1059 h_v808 pb_v1059_v808 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1061 : sv v1061 = sv v1059 * sv v808 := e_smx_pb 29 h_v1059 h_v808 pb_v1059_v808 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1062 : R 1 0 4611686018427387899 4611686018561605632 v1062 v1062 := (r_srdF hl h_v1061 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1062 : sv v1062 = sv v1061 / 2 ^ 28 := e_srdF h_v1061 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1063 : R 1 0 4611686018427387894 4611686018695823360 v1063 v1063 := (r_sub hl (r_add hl h_v1062 h_v1062 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1063 : sv v1063 = sv v1062 + sv v1062 := e_add h_v1062 h_v1062 (of_decide_eq_true rfl)
  have pb_v1060_v808 : PB 1 v1060 v808 36028797287399439 := pb_sqrt1 hl h_v808 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1064 : R 1 0 4611686017085210619 4647714815714787343 v1064 v1064 := (r_smx_pb hl 29 h_v1060 h_v808 pb_v1060_v808 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1064 : sv v1064 = sv v1060 * sv v808 := e_smx_pb 29 h_v1060 h_v808 pb_v1060_v808 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1065 : R 1 0 4611686018427387899 4611686018561605634 v1065 v1065 := (r_srdC hl h_v1064 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1065 : sv v1065 = -((-sv v1064) / 2 ^ 28) := e_srdC h_v1064 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1066 : R 1 0 4611686018427387894 4611686018695823364 v1066 v1066 := (r_sub hl (r_add hl h_v1065 h_v1065 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1066 : sv v1066 = sv v1065 + sv v1065 := e_add h_v1065 h_v1065 (of_decide_eq_true rfl)
  have h_v1067 : R 1 0 0 1 v1067 v1067 := (r_plt hl h_v1066 h_v23 (of_decide_eq_true rfl))
  have e_v1067 : (v1067 = 1 ↔ sv v1066 < sv v23) := e_plt h_v1066 h_v23 (of_decide_eq_true rfl)
  clear h_v808 h_v1055 h_v1056 h_v1058 h_v1059 h_v1060 pb_v1059_v808 h_v1061 h_v1062 pb_v1060_v808 h_v1064 h_v1065
  have h_v1068 : R 1 0 4611686018427387894 4611686018695823364 v1068 v1068 := (r_psel hl h_v1067 h_v1066 h_v23 (of_decide_eq_true rfl))
  have e_v1068 : v1068 = if v1067 = 1 then v1066 else v23 := e_psel h_v1067 h_v1066 h_v23 (of_decide_eq_true rfl)
  have h_v1069 : R 1 0 0 1 v1069 v1069 := (r_plt hl h_v1052 h_v1063 (of_decide_eq_true rfl))
  have e_v1069 : (v1069 = 1 ↔ sv v1052 < sv v1063) := e_plt h_v1052 h_v1063 (of_decide_eq_true rfl)
  have h_v1070 : R 1 0 4611686018427387894 4611686018695823360 v1070 v1070 := (r_psel hl h_v1069 h_v1052 h_v1063 (of_decide_eq_true rfl))
  have e_v1070 : v1070 = if v1069 = 1 then v1052 else v1063 := e_psel h_v1069 h_v1052 h_v1063 (of_decide_eq_true rfl)
  have h_v1071 : R 1 0 0 1 v1071 v1071 := (r_plt hl h_v1057 h_v1068 (of_decide_eq_true rfl))
  have e_v1071 : (v1071 = 1 ↔ sv v1057 < sv v1068) := e_plt h_v1057 h_v1068 (of_decide_eq_true rfl)
  have h_v1072 : R 1 0 4611686018427387894 4611686018695823364 v1072 v1072 := (r_psel hl h_v1071 h_v1068 h_v1057 (of_decide_eq_true rfl))
  have e_v1072 : v1072 = if v1071 = 1 then v1068 else v1057 := e_psel h_v1071 h_v1068 h_v1057 (of_decide_eq_true rfl)
  have h_v1073 : R 1 0 0 1 v1073 v1073 := (r_plt hl h_v902 h_v1000 (of_decide_eq_true rfl))
  have e_v1073 : (v1073 = 1 ↔ sv v902 < sv v1000) := e_plt h_v902 h_v1000 (of_decide_eq_true rfl)
  have h_v1074 : R 1 0 0 1 v1074 v1074 := (r_sub hl (r_O hl) h_v1073 (of_decide_eq_true rfl))
  have e_v1074 : (v1074 = 1 ↔ ¬v1073 = 1) := e_not h_v1073 (of_decide_eq_true rfl)
  have h_v1075 : R 1 0 0 1 v1075 v1075 := (r_plt hl h_v994 h_v902 (of_decide_eq_true rfl))
  have e_v1075 : (v1075 = 1 ↔ sv v994 < sv v902) := e_plt h_v994 h_v902 (of_decide_eq_true rfl)
  have h_v1076 : R 1 0 0 1 v1076 v1076 := (r_sub hl (r_O hl) h_v1075 (of_decide_eq_true rfl))
  have e_v1076 : (v1076 = 1 ↔ ¬v1075 = 1) := e_not h_v1075 (of_decide_eq_true rfl)
  have h_v1077 : R 1 0 0 1 v1077 v1077 := (r_land hl h_v1074 h_v1076 (of_decide_eq_true rfl))
  have e_v1077 : (v1077 = 1 ↔ v1074 = 1 ∧ v1076 = 1) := e_land h_v1074 h_v1076 (of_decide_eq_true rfl)
  have h_v1078 : R 1 0 4611686018427387894 4611686018695823364 v1078 v1078 := (r_psel hl h_v1077 h_v23 h_v1072 (of_decide_eq_true rfl))
  have e_v1078 : v1078 = if v1077 = 1 then v23 else v1072 := e_psel h_v1077 h_v23 h_v1072 (of_decide_eq_true rfl)
  have h_v1079 : R 1 0 4611686010374323999 4683743612465315840 v1079 v1079 := (r_sub hl (r_add hl h_v875 h_OFFr (of_decide_eq_true rfl)) h_v1010 (of_decide_eq_true rfl))
  have e_v1079 : sv v1079 = sv v875 - sv v1010 := e_sub h_v875 h_v1010 (of_decide_eq_true rfl)
  have h_v1080 : R 1 0 4611686018427387904 4611686018695823360 v1080 v1080 := (r_psqrt hl h_v1079 (of_decide_eq_true rfl))
  clear h_v994 h_v1000 h_v1052 h_v1057 h_v1063 h_v1066 h_v1067 h_v1068 h_v1069 h_v1071 h_v1072 h_v1073 h_v1074 h_v1075 h_v1076 h_v1077
  have e_v1080 : sv v1080 = ((Nat.sqrt (v1079 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1079 (of_decide_eq_true rfl)
  have h_v1081 : R 1 0 4611686018427387905 4611686018695823361 v1081 v1081 := (r_sub hl (r_add hl h_v95 h_v1080 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1081 : sv v1081 = sv v95 + sv v1080 := e_add h_v95 h_v1080 (of_decide_eq_true rfl)
  have pb_v1080_v811 : PB 1 v1080 v811 36028797018963968 := pb_sqrt hl h_v811 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1082 : R 1 0 4611686017085210624 4647714815446351872 v1082 v1082 := (r_smx_pb hl 29 h_v1080 h_v811 pb_v1080_v811 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1082 : sv v1082 = sv v1080 * sv v811 := e_smx_pb 29 h_v1080 h_v811 pb_v1080_v811 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1083 : R 1 0 4611686018427387899 4611686018561605632 v1083 v1083 := (r_srdF hl h_v1082 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1083 : sv v1083 = sv v1082 / 2 ^ 28 := e_srdF h_v1082 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1084 : R 1 0 4611686018427387894 4611686018695823360 v1084 v1084 := (r_sub hl (r_add hl h_v1083 h_v1083 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1084 : sv v1084 = sv v1083 + sv v1083 := e_add h_v1083 h_v1083 (of_decide_eq_true rfl)
  have pb_v1081_v811 : PB 1 v1081 v811 36028797287399439 := pb_sqrt1 hl h_v811 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1085 : R 1 0 4611686017085210619 4647714815714787343 v1085 v1085 := (r_smx_pb hl 29 h_v1081 h_v811 pb_v1081_v811 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1085 : sv v1085 = sv v1081 * sv v811 := e_smx_pb 29 h_v1081 h_v811 pb_v1081_v811 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1086 : R 1 0 4611686018427387899 4611686018561605634 v1086 v1086 := (r_srdC hl h_v1085 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1086 : sv v1086 = -((-sv v1085) / 2 ^ 28) := e_srdC h_v1085 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1087 : R 1 0 4611686018427387894 4611686018695823364 v1087 v1087 := (r_sub hl (r_add hl h_v1086 h_v1086 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1087 : sv v1087 = sv v1086 + sv v1086 := e_add h_v1086 h_v1086 (of_decide_eq_true rfl)
  have h_v1088 : R 1 0 0 1 v1088 v1088 := (r_plt hl h_v1087 h_v23 (of_decide_eq_true rfl))
  have e_v1088 : (v1088 = 1 ↔ sv v1087 < sv v23) := e_plt h_v1087 h_v23 (of_decide_eq_true rfl)
  have h_v1089 : R 1 0 4611686018427387894 4611686018695823364 v1089 v1089 := (r_psel hl h_v1088 h_v1087 h_v23 (of_decide_eq_true rfl))
  have e_v1089 : v1089 = if v1088 = 1 then v1087 else v23 := e_psel h_v1088 h_v1087 h_v23 (of_decide_eq_true rfl)
  have h_v1090 : R 1 0 4611686010374323999 4683743612465315840 v1090 v1090 := (r_sub hl (r_add hl h_v875 h_OFFr (of_decide_eq_true rfl)) h_v1004 (of_decide_eq_true rfl))
  have e_v1090 : sv v1090 = sv v875 - sv v1004 := e_sub h_v875 h_v1004 (of_decide_eq_true rfl)
  have h_v1091 : R 1 0 4611686018427387904 4611686018695823360 v1091 v1091 := (r_psqrt hl h_v1090 (of_decide_eq_true rfl))
  have e_v1091 : sv v1091 = ((Nat.sqrt (v1090 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1090 (of_decide_eq_true rfl)
  clear h_v811 h_v875 h_v1079 h_v1080 h_v1081 pb_v1080_v811 h_v1082 h_v1083 pb_v1081_v811 h_v1085 h_v1086 h_v1087 h_v1088 h_v1090
  have h_v1092 : R 1 0 4611686018427387905 4611686018695823361 v1092 v1092 := (r_sub hl (r_add hl h_v95 h_v1091 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1092 : sv v1092 = sv v95 + sv v1091 := e_add h_v95 h_v1091 (of_decide_eq_true rfl)
  have pb_v1091_v812 : PB 1 v1091 v812 36028797018963968 := pb_sqrt hl h_v812 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1093 : R 1 0 4611686017085210624 4647714815446351872 v1093 v1093 := (r_smx_pb hl 29 h_v1091 h_v812 pb_v1091_v812 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1093 : sv v1093 = sv v1091 * sv v812 := e_smx_pb 29 h_v1091 h_v812 pb_v1091_v812 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1094 : R 1 0 4611686018427387899 4611686018561605632 v1094 v1094 := (r_srdF hl h_v1093 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1094 : sv v1094 = sv v1093 / 2 ^ 28 := e_srdF h_v1093 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1095 : R 1 0 4611686018427387894 4611686018695823360 v1095 v1095 := (r_sub hl (r_add hl h_v1094 h_v1094 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1095 : sv v1095 = sv v1094 + sv v1094 := e_add h_v1094 h_v1094 (of_decide_eq_true rfl)
  have pb_v1092_v812 : PB 1 v1092 v812 36028797287399439 := pb_sqrt1 hl h_v812 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1096 : R 1 0 4611686017085210619 4647714815714787343 v1096 v1096 := (r_smx_pb hl 29 h_v1092 h_v812 pb_v1092_v812 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1096 : sv v1096 = sv v1092 * sv v812 := e_smx_pb 29 h_v1092 h_v812 pb_v1092_v812 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1097 : R 1 0 4611686018427387899 4611686018561605634 v1097 v1097 := (r_srdC hl h_v1096 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1097 : sv v1097 = -((-sv v1096) / 2 ^ 28) := e_srdC h_v1096 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1098 : R 1 0 4611686018427387894 4611686018695823364 v1098 v1098 := (r_sub hl (r_add hl h_v1097 h_v1097 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1098 : sv v1098 = sv v1097 + sv v1097 := e_add h_v1097 h_v1097 (of_decide_eq_true rfl)
  have h_v1099 : R 1 0 0 1 v1099 v1099 := (r_plt hl h_v1098 h_v23 (of_decide_eq_true rfl))
  have e_v1099 : (v1099 = 1 ↔ sv v1098 < sv v23) := e_plt h_v1098 h_v23 (of_decide_eq_true rfl)
  have h_v1100 : R 1 0 4611686018427387894 4611686018695823364 v1100 v1100 := (r_psel hl h_v1099 h_v1098 h_v23 (of_decide_eq_true rfl))
  have e_v1100 : v1100 = if v1099 = 1 then v1098 else v23 := e_psel h_v1099 h_v1098 h_v23 (of_decide_eq_true rfl)
  have h_v1101 : R 1 0 0 1 v1101 v1101 := (r_plt hl h_v1084 h_v1095 (of_decide_eq_true rfl))
  have e_v1101 : (v1101 = 1 ↔ sv v1084 < sv v1095) := e_plt h_v1084 h_v1095 (of_decide_eq_true rfl)
  have h_v1102 : R 1 0 4611686018427387894 4611686018695823360 v1102 v1102 := (r_psel hl h_v1101 h_v1084 h_v1095 (of_decide_eq_true rfl))
  have e_v1102 : v1102 = if v1101 = 1 then v1084 else v1095 := e_psel h_v1101 h_v1084 h_v1095 (of_decide_eq_true rfl)
  have h_v1103 : R 1 0 0 1 v1103 v1103 := (r_plt hl h_v1089 h_v1100 (of_decide_eq_true rfl))
  clear h_v95 h_v812 h_v1084 h_v1091 h_v1092 pb_v1091_v812 h_v1093 h_v1094 h_v1095 pb_v1092_v812 h_v1096 h_v1097 h_v1098 h_v1099 h_v1101
  have e_v1103 : (v1103 = 1 ↔ sv v1089 < sv v1100) := e_plt h_v1089 h_v1100 (of_decide_eq_true rfl)
  have h_v1104 : R 1 0 4611686018427387894 4611686018695823364 v1104 v1104 := (r_psel hl h_v1103 h_v1100 h_v1089 (of_decide_eq_true rfl))
  have e_v1104 : v1104 = if v1103 = 1 then v1100 else v1089 := e_psel h_v1103 h_v1100 h_v1089 (of_decide_eq_true rfl)
  have h_v1105 : R 1 0 0 1 v1105 v1105 := (r_plt hl h_v902 h_v1010 (of_decide_eq_true rfl))
  have e_v1105 : (v1105 = 1 ↔ sv v902 < sv v1010) := e_plt h_v902 h_v1010 (of_decide_eq_true rfl)
  have h_v1106 : R 1 0 0 1 v1106 v1106 := (r_sub hl (r_O hl) h_v1105 (of_decide_eq_true rfl))
  have e_v1106 : (v1106 = 1 ↔ ¬v1105 = 1) := e_not h_v1105 (of_decide_eq_true rfl)
  have h_v1107 : R 1 0 0 1 v1107 v1107 := (r_plt hl h_v1004 h_v902 (of_decide_eq_true rfl))
  have e_v1107 : (v1107 = 1 ↔ sv v1004 < sv v902) := e_plt h_v1004 h_v902 (of_decide_eq_true rfl)
  have h_v1108 : R 1 0 0 1 v1108 v1108 := (r_sub hl (r_O hl) h_v1107 (of_decide_eq_true rfl))
  have e_v1108 : (v1108 = 1 ↔ ¬v1107 = 1) := e_not h_v1107 (of_decide_eq_true rfl)
  have h_v1109 : R 1 0 0 1 v1109 v1109 := (r_land hl h_v1106 h_v1108 (of_decide_eq_true rfl))
  have e_v1109 : (v1109 = 1 ↔ v1106 = 1 ∧ v1108 = 1) := e_land h_v1106 h_v1108 (of_decide_eq_true rfl)
  have h_v1110 : R 1 0 4611686018427387894 4611686018695823364 v1110 v1110 := (r_psel hl h_v1109 h_v23 h_v1104 (of_decide_eq_true rfl))
  have e_v1110 : v1110 = if v1109 = 1 then v23 else v1104 := e_psel h_v1109 h_v23 h_v1104 (of_decide_eq_true rfl)
  have h_v1111 : R 1 0 0 1 v1111 v1111 := (r_plt hl h_v1070 h_v51 (of_decide_eq_true rfl))
  have e_v1111 : (v1111 = 1 ↔ sv v1070 < sv v51) := e_plt h_v1070 h_v51 (of_decide_eq_true rfl)
  have h_v1112 : R 1 0 0 1 v1112 v1112 := (r_sub hl (r_O hl) h_v1111 (of_decide_eq_true rfl))
  have e_v1112 : (v1112 = 1 ↔ ¬v1111 = 1) := e_not h_v1111 (of_decide_eq_true rfl)
  have h_v1113 : R 1 0 0 1 v1113 v1113 := (r_plt hl h_v51 h_v1078 (of_decide_eq_true rfl))
  have e_v1113 : (v1113 = 1 ↔ sv v51 < sv v1078) := e_plt h_v51 h_v1078 (of_decide_eq_true rfl)
  have h_v1114 : R 1 0 0 1 v1114 v1114 := (r_sub hl (r_O hl) h_v1113 (of_decide_eq_true rfl))
  have e_v1114 : (v1114 = 1 ↔ ¬v1113 = 1) := e_not h_v1113 (of_decide_eq_true rfl)
  have h_v1115 : R 1 0 0 1 v1115 v1115 := (r_land hl h_v1111 h_v1114 (of_decide_eq_true rfl))
  have e_v1115 : (v1115 = 1 ↔ v1111 = 1 ∧ v1114 = 1) := e_land h_v1111 h_v1114 (of_decide_eq_true rfl)
  clear h_v902 h_v1004 h_v1010 h_v1089 h_v1100 h_v1103 h_v1104 h_v1105 h_v1106 h_v1107 h_v1108 h_v1109 h_v1114
  have h_v1116 : R 1 0 0 1 v1116 v1116 := (r_land hl h_v1111 h_v1113 (of_decide_eq_true rfl))
  have e_v1116 : (v1116 = 1 ↔ v1111 = 1 ∧ v1113 = 1) := e_land h_v1111 h_v1113 (of_decide_eq_true rfl)
  have h_v1117 : R 1 0 0 1 v1117 v1117 := (r_plt hl h_v1102 h_v51 (of_decide_eq_true rfl))
  have e_v1117 : (v1117 = 1 ↔ sv v1102 < sv v51) := e_plt h_v1102 h_v51 (of_decide_eq_true rfl)
  have h_v1118 : R 1 0 0 1 v1118 v1118 := (r_sub hl (r_O hl) h_v1117 (of_decide_eq_true rfl))
  have e_v1118 : (v1118 = 1 ↔ ¬v1117 = 1) := e_not h_v1117 (of_decide_eq_true rfl)
  have h_v1119 : R 1 0 0 1 v1119 v1119 := (r_plt hl h_v51 h_v1110 (of_decide_eq_true rfl))
  have e_v1119 : (v1119 = 1 ↔ sv v51 < sv v1110) := e_plt h_v51 h_v1110 (of_decide_eq_true rfl)
  have h_v1120 : R 1 0 0 1 v1120 v1120 := (r_sub hl (r_O hl) h_v1119 (of_decide_eq_true rfl))
  have e_v1120 : (v1120 = 1 ↔ ¬v1119 = 1) := e_not h_v1119 (of_decide_eq_true rfl)
  have h_v1121 : R 1 0 0 1 v1121 v1121 := (r_land hl h_v1117 h_v1120 (of_decide_eq_true rfl))
  have e_v1121 : (v1121 = 1 ↔ v1117 = 1 ∧ v1120 = 1) := e_land h_v1117 h_v1120 (of_decide_eq_true rfl)
  have h_v1122 : R 1 0 0 1 v1122 v1122 := (r_land hl h_v1117 h_v1119 (of_decide_eq_true rfl))
  have e_v1122 : (v1122 = 1 ↔ v1117 = 1 ∧ v1119 = 1) := e_land h_v1117 h_v1119 (of_decide_eq_true rfl)
  have h_v1123 : R 1 0 0 1 v1123 v1123 := (r_land hl h_v1116 h_v1122 (of_decide_eq_true rfl))
  have e_v1123 : (v1123 = 1 ↔ v1116 = 1 ∧ v1122 = 1) := e_land h_v1116 h_v1122 (of_decide_eq_true rfl)
  have h_v1124 : R 1 0 0 1 v1124 v1124 := (r_sub hl (r_O hl) h_v1123 (of_decide_eq_true rfl))
  have e_v1124 : (v1124 = 1 ↔ ¬v1123 = 1) := e_not h_v1123 (of_decide_eq_true rfl)
  have h_v1125 : R 1 0 0 1 v1125 v1125 := (r_lor hl h_v725 h_v1124 (of_decide_eq_true rfl))
  have e_v1125 : (v1125 = 1 ↔ v725 = 1 ∨ v1124 = 1) := e_lor h_v725 h_v1124 (of_decide_eq_true rfl)
  have h_v1126 : R 1 0 0 1 v1126 v1126 := (r_land hl h_v1112 h_v1122 (of_decide_eq_true rfl))
  have e_v1126 : (v1126 = 1 ↔ v1112 = 1 ∧ v1122 = 1) := e_land h_v1112 h_v1122 (of_decide_eq_true rfl)
  have h_v1127 : R 1 0 0 1 v1127 v1127 := (r_lor hl h_v1121 h_v1126 (of_decide_eq_true rfl))
  have e_v1127 : (v1127 = 1 ↔ v1121 = 1 ∨ v1126 = 1) := e_lor h_v1121 h_v1126 (of_decide_eq_true rfl)
  have h_v1128 : R 1 0 4611686018427387894 4611686018695823364 v1128 v1128 := (r_psel hl h_v1127 h_v1078 h_v1070 (of_decide_eq_true rfl))
  clear h_v725 h_v1111 h_v1112 h_v1113 h_v1117 h_v1119 h_v1120 h_v1123 h_v1124 h_v1126
  have e_v1128 : v1128 = if v1127 = 1 then v1078 else v1070 := e_psel h_v1127 h_v1078 h_v1070 (of_decide_eq_true rfl)
  have h_v1129 : R 1 0 0 1 v1129 v1129 := (r_land hl h_v1116 h_v1118 (of_decide_eq_true rfl))
  have e_v1129 : (v1129 = 1 ↔ v1116 = 1 ∧ v1118 = 1) := e_land h_v1116 h_v1118 (of_decide_eq_true rfl)
  have h_v1130 : R 1 0 0 1 v1130 v1130 := (r_lor hl h_v1115 h_v1129 (of_decide_eq_true rfl))
  have e_v1130 : (v1130 = 1 ↔ v1115 = 1 ∨ v1129 = 1) := e_lor h_v1115 h_v1129 (of_decide_eq_true rfl)
  have h_v1131 : R 1 0 4611686018427387894 4611686018695823364 v1131 v1131 := (r_psel hl h_v1130 h_v1110 h_v1102 (of_decide_eq_true rfl))
  have e_v1131 : v1131 = if v1130 = 1 then v1110 else v1102 := e_psel h_v1130 h_v1110 h_v1102 (of_decide_eq_true rfl)
  have h_v1132 : R 1 0 0 1 v1132 v1132 := (r_land hl h_v1115 h_v1122 (of_decide_eq_true rfl))
  have e_v1132 : (v1132 = 1 ↔ v1115 = 1 ∧ v1122 = 1) := e_land h_v1115 h_v1122 (of_decide_eq_true rfl)
  have h_v1133 : R 1 0 0 1 v1133 v1133 := (r_lor hl h_v1121 h_v1132 (of_decide_eq_true rfl))
  have e_v1133 : (v1133 = 1 ↔ v1121 = 1 ∨ v1132 = 1) := e_lor h_v1121 h_v1132 (of_decide_eq_true rfl)
  have h_v1134 : R 1 0 4611686018427387894 4611686018695823364 v1134 v1134 := (r_psel hl h_v1133 h_v1070 h_v1078 (of_decide_eq_true rfl))
  have e_v1134 : v1134 = if v1133 = 1 then v1070 else v1078 := e_psel h_v1133 h_v1070 h_v1078 (of_decide_eq_true rfl)
  have h_v1135 : R 1 0 0 1 v1135 v1135 := (r_land hl h_v1116 h_v1121 (of_decide_eq_true rfl))
  have e_v1135 : (v1135 = 1 ↔ v1116 = 1 ∧ v1121 = 1) := e_land h_v1116 h_v1121 (of_decide_eq_true rfl)
  have h_v1136 : R 1 0 0 1 v1136 v1136 := (r_lor hl h_v1115 h_v1135 (of_decide_eq_true rfl))
  have e_v1136 : (v1136 = 1 ↔ v1115 = 1 ∨ v1135 = 1) := e_lor h_v1115 h_v1135 (of_decide_eq_true rfl)
  have h_v1137 : R 1 0 4611686018427387894 4611686018695823364 v1137 v1137 := (r_psel hl h_v1136 h_v1102 h_v1110 (of_decide_eq_true rfl))
  have e_v1137 : v1137 = if v1136 = 1 then v1102 else v1110 := e_psel h_v1136 h_v1102 h_v1110 (of_decide_eq_true rfl)
  have h_v1138 : R 1 0 4611686015743033304 4683743614612799504 v1138 v1138 := (r_smx hl 29 h_v1131 h_v1128 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1138 : sv v1138 = sv v1131 * sv v1128 := e_smx 29 h_v1131 h_v1128 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1139 : R 1 0 4611686018427387893 4611686018695823368 v1139 v1139 := (r_srdF hl h_v1138 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v1139 : sv v1139 = sv v1138 / 2 ^ 28 := e_srdF h_v1138 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v1140 : R 1 0 4611686015743033304 4683743614612799504 v1140 v1140 := (r_smx hl 29 h_v1137 h_v1134 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1140 : sv v1140 = sv v1137 * sv v1134 := e_smx 29 h_v1137 h_v1134 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  clear h_v1070 h_v1078 h_v1102 h_v1110 h_v1115 h_v1116 h_v1118 h_v1121 h_v1122 h_v1127 h_v1128 h_v1129 h_v1130 h_v1131 h_v1132 h_v1133 h_v1134 h_v1135 h_v1136 h_v1137 h_v1138
  have h_v1141 : R 1 0 4611686018427387894 4611686018695823369 v1141 v1141 := (r_srdC hl h_v1140 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v1141 : sv v1141 = -((-sv v1140) / 2 ^ 28) := e_srdC h_v1140 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1142 : R 1 0 0 1 v1142 v1142 := (r_plt hl h_v51 h_v1139 (of_decide_eq_true rfl))
  have e_v1142 : (v1142 = 1 ↔ sv v51 < sv v1139) := e_plt h_v51 h_v1139 (of_decide_eq_true rfl)
  have h_v1143 : R 1 0 0 1 v1143 v1143 := (r_sub hl (r_O hl) h_v1142 (of_decide_eq_true rfl))
  have e_v1143 : (v1143 = 1 ↔ ¬v1142 = 1) := e_not h_v1142 (of_decide_eq_true rfl)
  have h_v1144 : R 1 0 0 1 v1144 v1144 := (r_plt hl h_v1045 h_v51 (of_decide_eq_true rfl))
  have e_v1144 : (v1144 = 1 ↔ sv v1045 < sv v51) := e_plt h_v1045 h_v51 (of_decide_eq_true rfl)
  have h_v1145 : R 1 0 4611686018427387893 4611686018695823369 v1145 v1145 := (r_psel hl h_v1144 h_v1139 h_v1141 (of_decide_eq_true rfl))
  have e_v1145 : v1145 = if v1144 = 1 then v1139 else v1141 := e_psel h_v1144 h_v1139 h_v1141 (of_decide_eq_true rfl)
  have h_v1148 : R 1 0 0 1 v1148 v1148 := (r_plt hl h_v1145 h_v1045 (of_decide_eq_true rfl))
  have e_v1148 : (v1148 = 1 ↔ sv v1145 < sv v1045) := e_plt h_v1145 h_v1045 (of_decide_eq_true rfl)
  have h_v1149 : R 1 0 0 1 v1149 v1149 := (r_land hl h_v1142 h_v1148 (of_decide_eq_true rfl))
  have e_v1149 : (v1149 = 1 ↔ v1142 = 1 ∧ v1148 = 1) := e_land h_v1142 h_v1148 (of_decide_eq_true rfl)
  have h_v1150 : R 1 0 4611686018158952439 4611686018427387915 v1150 v1150 := (r_sub hl (r_add hl h_v51 h_OFFr (of_decide_eq_true rfl)) h_v1145 (of_decide_eq_true rfl))
  have e_v1150 : sv v1150 = sv v51 - sv v1145 := e_sub h_v51 h_v1145 (of_decide_eq_true rfl)
  have h_v1151 : R 1 0 0 1 v1151 v1151 := (r_plt hl h_v1150 h_v1045 (of_decide_eq_true rfl))
  have e_v1151 : (v1151 = 1 ↔ sv v1150 < sv v1045) := e_plt h_v1150 h_v1045 (of_decide_eq_true rfl)
  have h_v1152 : R 1 0 0 1 v1152 v1152 := (r_sub hl (r_O hl) h_v1151 (of_decide_eq_true rfl))
  have e_v1152 : (v1152 = 1 ↔ ¬v1151 = 1) := e_not h_v1151 (of_decide_eq_true rfl)
  have h_v1153 : R 1 0 0 1 v1153 v1153 := (r_lor hl h_v1143 h_v1152 (of_decide_eq_true rfl))
  have e_v1153 : (v1153 = 1 ↔ v1143 = 1 ∨ v1152 = 1) := e_lor h_v1143 h_v1152 (of_decide_eq_true rfl)
  have h_v1154 : R 1 0 4611686017890516860 4611686018964258877 v1154 v1154 := (r_psel hl h_v1153 h_v85 h_v1045 (of_decide_eq_true rfl))
  have e_v1154 : v1154 = if v1153 = 1 then v85 else v1045 := e_psel h_v1153 h_v85 h_v1045 (of_decide_eq_true rfl)
  have h_v1155 : R 1 0 4611686018427387893 4611686018695823369 v1155 v1155 := (r_psel hl h_v1153 h_v23 h_v1145 (of_decide_eq_true rfl))
  clear h_v51 h_v85 h_v1045 h_v1139 h_v1140 h_v1141 h_v1142 h_v1143 h_v1144 h_v1148 h_v1150 h_v1151 h_v1152
  have e_v1155 : v1155 = if v1153 = 1 then v23 else v1145 := e_psel h_v1153 h_v23 h_v1145 (of_decide_eq_true rfl)
  have h_v1156 : R 1 0 0 1 v1156 v1156 := (r_lor hl h_v980 h_v1149 (of_decide_eq_true rfl))
  have e_v1156 : (v1156 = 1 ↔ v980 = 1 ∨ v1149 = 1) := e_lor h_v980 h_v1149 (of_decide_eq_true rfl)
  have h_v1174 : R 1 0 4611686018427387904 4611686019501129727 v1174 v1174 := (r1_hxa hb_H1 0 (of_decide_eq_true rfl))
  have e_v1174 : sv v1174 = ((H1 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H1 0 (of_decide_eq_true rfl)
  have h_v1175 : R 1 0 0 1 v1175 v1175 := (r_plt hl h_v1174 h_v10 (of_decide_eq_true rfl))
  have e_v1175 : (v1175 = 1 ↔ sv v1174 < sv v10) := e_plt h_v1174 h_v10 (of_decide_eq_true rfl)
  have h_v1176 : R 1 0 0 1 v1176 v1176 := (r_sub hl (r_O hl) h_v1175 (of_decide_eq_true rfl))
  have e_v1176 : (v1176 = 1 ↔ ¬v1175 = 1) := e_not h_v1175 (of_decide_eq_true rfl)
  have h_t1174_1 : R 1 0 4611686018427387904 4611686018695823363 t1174.1 t1174.1 := r_sc1 hl h_v1174 (of_decide_eq_true rfl)
  have h_t1174_2 : R 1 0 4611686018158952445 4611686018695823363 t1174.2 t1174.2 := r_sc2 hl h_v1174 (of_decide_eq_true rfl)
  have e_t1174_1 : sv t1174.1 = (sc28pS (scArg v1174)).1 := e_sc1 h_v1174 (of_decide_eq_true rfl)
  have e_t1174_2 : sv t1174.2 = (sc28pS (scArg v1174)).2 := e_sc2 h_v1174 (of_decide_eq_true rfl)
  have h_v1178 : R 1 0 4611686018158952449 4611686018695823367 v1178 v1178 := (r_sub hl (r_add hl h_v21 h_t1174_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1178 : sv v1178 = sv v21 + sv t1174.2 := e_add h_v21 h_t1174_2 (of_decide_eq_true rfl)
  have h_v1179 : R 1 0 0 1 v1179 v1179 := (r_plt hl h_v1178 h_v23 (of_decide_eq_true rfl))
  have e_v1179 : (v1179 = 1 ↔ sv v1178 < sv v23) := e_plt h_v1178 h_v23 (of_decide_eq_true rfl)
  have h_v1180 : R 1 0 4611686018158952449 4611686018695823367 v1180 v1180 := (r_psel hl h_v1179 h_v1178 h_v23 (of_decide_eq_true rfl))
  have e_v1180 : v1180 = if v1179 = 1 then v1178 else v23 := e_psel h_v1179 h_v1178 h_v23 (of_decide_eq_true rfl)
  have h_v1181 : R 1 0 4467570794918051840 4755801222877806592 v1181 v1181 := (r_sshl hl h_v1154 4467570794918051840 4755801222877806592 (of_decide_eq_true rfl))
  have e_v1181 : sv v1181 = sv v1154 * 2 ^ 28 := e_sshl h_v1154 4467570794918051840 4755801222877806592 (of_decide_eq_true rfl)
  have h_v1182 : R 1 0 4539628422241976329 4683743616760283199 v1182 v1182 := (r_smx hl 29 h_v1180 h_v1155 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl))
  have e_v1182 : sv v1182 = sv v1180 * sv v1155 := e_smx 29 h_v1180 h_v1155 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl)
  have h_v1183 : R 1 0 0 1 v1183 v1183 := (r_plt hl h_v1181 h_v1182 (of_decide_eq_true rfl))
  have e_v1183 : (v1183 = 1 ↔ sv v1181 < sv v1182) := e_plt h_v1181 h_v1182 (of_decide_eq_true rfl)
  clear h_v21 h_v23 h_v980 h_v1145 h_v1149 h_v1153 h_v1154 h_v1155 h_v1175 h_t1174_1 h_t1174_2 e_t1174_1 h_v1178 h_v1179 h_v1180 h_v1181 h_v1182
  have h_v1184 : R 1 0 0 1 v1184 v1184 := (r_sub hl (r_O hl) h_v1183 (of_decide_eq_true rfl))
  have e_v1184 : (v1184 = 1 ↔ ¬v1183 = 1) := e_not h_v1183 (of_decide_eq_true rfl)
  have h_v1185 : R 1 0 0 1 v1185 v1185 := (r_lor hl h_v1176 h_v1184 (of_decide_eq_true rfl))
  have e_v1185 : (v1185 = 1 ↔ v1176 = 1 ∨ v1184 = 1) := e_lor h_v1176 h_v1184 (of_decide_eq_true rfl)
  have h_v1186 : R 1 0 4611686018427387904 4611686019501129727 v1186 v1186 := (r_psel hl h_v1185 h_v1174 h_v10 (of_decide_eq_true rfl))
  have e_v1186 : v1186 = if v1185 = 1 then v1174 else v10 := e_psel h_v1185 h_v1174 h_v10 (of_decide_eq_true rfl)
  have h_v1188 : R 1 0 4611686018427387904 4611686019501129727 v1188 v1188 := (r_psel hl h_v724 h_v1186 h_v10 (of_decide_eq_true rfl))
  have e_v1188 : v1188 = if v724 = 1 then v1186 else v10 := e_psel h_v724 h_v1186 h_v10 (of_decide_eq_true rfl)
  have h_v1189 : R 1 0 0 1 v1189 v1189 := (r_land hl h_v724 h_v1156 (of_decide_eq_true rfl))
  have e_v1189 : (v1189 = 1 ↔ v724 = 1 ∧ v1156 = 1) := e_land h_v724 h_v1156 (of_decide_eq_true rfl)
  have h_v1192 : R 1 0 0 1 v1192 v1192 := (r_sub hl (r_O hl) h_v1189 (of_decide_eq_true rfl))
  have e_v1192 : (v1192 = 1 ↔ ¬v1189 = 1) := e_not h_v1189 (of_decide_eq_true rfl)
  have h_v1194 : R 1 0 4611686017353646081 4611686020574871550 v1194 v1194 := (r_sub hl (r_add hl h_v387 h_v1188 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1194 : sv v1194 = sv v387 + sv v1188 := e_add h_v387 h_v1188 (of_decide_eq_true rfl)
  have h_v1196 : R 1 0 4611686016279904258 4611686021648613373 v1196 v1196 := (r_sub hl (r_add hl h_v712 h_v1194 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1196 : sv v1196 = sv v712 + sv v1194 := e_add h_v712 h_v1194 (of_decide_eq_true rfl)
  have h_v1199 : R 1 0 0 1 v1199 v1199 := (r_plt hl h_v6 h_v1196 (of_decide_eq_true rfl))
  have e_v1199 : (v1199 = 1 ↔ sv v6 < sv v1196) := e_plt h_v6 h_v1196 (of_decide_eq_true rfl)
  have h_v1200 : R 1 0 0 1 v1200 v1200 := (r_sub hl (r_O hl) h_v1199 (of_decide_eq_true rfl))
  have e_v1200 : (v1200 = 1 ↔ ¬v1199 = 1) := e_not h_v1199 (of_decide_eq_true rfl)
  have h_v1201 : R 1 0 0 1 v1201 v1201 := (r_land hl h_v13 h_v37 (of_decide_eq_true rfl))
  have e_v1201 : (v1201 = 1 ↔ v13 = 1 ∧ v37 = 1) := e_land h_v13 h_v37 (of_decide_eq_true rfl)
  have h_v1202 : R 1 0 0 1 v1202 v1202 := (r_land hl h_v65 h_v1201 (of_decide_eq_true rfl))
  have e_v1202 : (v1202 = 1 ↔ v65 = 1 ∧ v1201 = 1) := e_land h_v65 h_v1201 (of_decide_eq_true rfl)
  have h_v1203 : R 1 0 0 1 v1203 v1203 := (r_land hl h_v82 h_v1202 (of_decide_eq_true rfl))
  clear h_OFFr h_v6 h_v10 h_v37 h_v65 h_v387 h_v712 h_v724 h_v1156 h_v1174 h_v1176 h_v1183 h_v1184 h_v1185 h_v1186 h_v1188 h_v1189 h_v1194 h_v1196 h_v1199 h_v1201
  have e_v1203 : (v1203 = 1 ↔ v82 = 1 ∧ v1202 = 1) := e_land h_v82 h_v1202 (of_decide_eq_true rfl)
  have h_v1204 : R 1 0 0 1 v1204 v1204 := (r_land hl h_v13 h_v1203 (of_decide_eq_true rfl))
  have e_v1204 : (v1204 = 1 ↔ v13 = 1 ∧ v1203 = 1) := e_land h_v13 h_v1203 (of_decide_eq_true rfl)
  have h_v1205 : R 1 0 0 1 v1205 v1205 := (r_land hl h_v100 h_v1204 (of_decide_eq_true rfl))
  have e_v1205 : (v1205 = 1 ↔ v100 = 1 ∧ v1204 = 1) := e_land h_v100 h_v1204 (of_decide_eq_true rfl)
  have h_v1206 : R 1 0 0 1 v1206 v1206 := (r_land hl h_v100 h_v1205 (of_decide_eq_true rfl))
  have e_v1206 : (v1206 = 1 ↔ v100 = 1 ∧ v1205 = 1) := e_land h_v100 h_v1205 (of_decide_eq_true rfl)
  have h_v1207 : R 1 0 0 1 v1207 v1207 := (r_land hl h_v137 h_v1206 (of_decide_eq_true rfl))
  have e_v1207 : (v1207 = 1 ↔ v137 = 1 ∧ v1206 = 1) := e_land h_v137 h_v1206 (of_decide_eq_true rfl)
  have h_v1208 : R 1 0 0 1 v1208 v1208 := (r_land hl h_v250 h_v1207 (of_decide_eq_true rfl))
  have e_v1208 : (v1208 = 1 ↔ v250 = 1 ∧ v1207 = 1) := e_land h_v250 h_v1207 (of_decide_eq_true rfl)
  have h_v1209 : R 1 0 0 1 v1209 v1209 := (r_land hl h_v250 h_v1208 (of_decide_eq_true rfl))
  have e_v1209 : (v1209 = 1 ↔ v250 = 1 ∧ v1208 = 1) := e_land h_v250 h_v1208 (of_decide_eq_true rfl)
  have h_v1210 : R 1 0 0 1 v1210 v1210 := (r_land hl h_v281 h_v1209 (of_decide_eq_true rfl))
  have e_v1210 : (v1210 = 1 ↔ v281 = 1 ∧ v1209 = 1) := e_land h_v281 h_v1209 (of_decide_eq_true rfl)
  have h_v1211 : R 1 0 0 1 v1211 v1211 := (r_land hl h_v13 h_v1210 (of_decide_eq_true rfl))
  have e_v1211 : (v1211 = 1 ↔ v13 = 1 ∧ v1210 = 1) := e_land h_v13 h_v1210 (of_decide_eq_true rfl)
  have h_v1212 : R 1 0 0 1 v1212 v1212 := (r_land hl h_v393 h_v1211 (of_decide_eq_true rfl))
  have e_v1212 : (v1212 = 1 ↔ v393 = 1 ∧ v1211 = 1) := e_land h_v393 h_v1211 (of_decide_eq_true rfl)
  have h_v1213 : R 1 0 0 1 v1213 v1213 := (r_land hl h_v414 h_v1212 (of_decide_eq_true rfl))
  have e_v1213 : (v1213 = 1 ↔ v414 = 1 ∧ v1212 = 1) := e_land h_v414 h_v1212 (of_decide_eq_true rfl)
  have h_v1214 : R 1 0 0 1 v1214 v1214 := (r_land hl h_v431 h_v1213 (of_decide_eq_true rfl))
  have e_v1214 : (v1214 = 1 ↔ v431 = 1 ∧ v1213 = 1) := e_land h_v431 h_v1213 (of_decide_eq_true rfl)
  have h_v1215 : R 1 0 0 1 v1215 v1215 := (r_land hl h_v13 h_v1214 (of_decide_eq_true rfl))
  have e_v1215 : (v1215 = 1 ↔ v13 = 1 ∧ v1214 = 1) := e_land h_v13 h_v1214 (of_decide_eq_true rfl)
  clear h_v13 h_v82 h_v100 h_v137 h_v250 h_v281 h_v393 h_v414 h_v431 h_v1202 h_v1203 h_v1204 h_v1205 h_v1206 h_v1207 h_v1208 h_v1209 h_v1210 h_v1211 h_v1212 h_v1213 h_v1214
  have h_v1216 : R 1 0 0 1 v1216 v1216 := (r_land hl h_v434 h_v1215 (of_decide_eq_true rfl))
  have e_v1216 : (v1216 = 1 ↔ v434 = 1 ∧ v1215 = 1) := e_land h_v434 h_v1215 (of_decide_eq_true rfl)
  have h_v1217 : R 1 0 0 1 v1217 v1217 := (r_land hl h_v434 h_v1216 (of_decide_eq_true rfl))
  have e_v1217 : (v1217 = 1 ↔ v434 = 1 ∧ v1216 = 1) := e_land h_v434 h_v1216 (of_decide_eq_true rfl)
  have h_v1218 : R 1 0 0 1 v1218 v1218 := (r_land hl h_v465 h_v1217 (of_decide_eq_true rfl))
  have e_v1218 : (v1218 = 1 ↔ v465 = 1 ∧ v1217 = 1) := e_land h_v465 h_v1217 (of_decide_eq_true rfl)
  have h_v1219 : R 1 0 0 1 v1219 v1219 := (r_land hl h_v575 h_v1218 (of_decide_eq_true rfl))
  have e_v1219 : (v1219 = 1 ↔ v575 = 1 ∧ v1218 = 1) := e_land h_v575 h_v1218 (of_decide_eq_true rfl)
  have h_v1220 : R 1 0 0 1 v1220 v1220 := (r_land hl h_v575 h_v1219 (of_decide_eq_true rfl))
  have e_v1220 : (v1220 = 1 ↔ v575 = 1 ∧ v1219 = 1) := e_land h_v575 h_v1219 (of_decide_eq_true rfl)
  have h_v1221 : R 1 0 0 1 v1221 v1221 := (r_land hl h_v606 h_v1220 (of_decide_eq_true rfl))
  have e_v1221 : (v1221 = 1 ↔ v606 = 1 ∧ v1220 = 1) := e_land h_v606 h_v1220 (of_decide_eq_true rfl)
  have h_v1222 : R 1 0 0 1 v1222 v1222 := (r_land hl h_v726 h_v1221 (of_decide_eq_true rfl))
  have e_v1222 : (v1222 = 1 ↔ v726 = 1 ∧ v1221 = 1) := e_land h_v726 h_v1221 (of_decide_eq_true rfl)
  have h_v1223 : R 1 0 0 1 v1223 v1223 := (r_land hl h_v755 h_v1222 (of_decide_eq_true rfl))
  have e_v1223 : (v1223 = 1 ↔ v755 = 1 ∧ v1222 = 1) := e_land h_v755 h_v1222 (of_decide_eq_true rfl)
  have h_v1224 : R 1 0 0 1 v1224 v1224 := (r_land hl h_v782 h_v1223 (of_decide_eq_true rfl))
  have e_v1224 : (v1224 = 1 ↔ v782 = 1 ∧ v1223 = 1) := e_land h_v782 h_v1223 (of_decide_eq_true rfl)
  have h_v1225 : R 1 0 0 1 v1225 v1225 := (r_land hl h_v816 h_v1224 (of_decide_eq_true rfl))
  have e_v1225 : (v1225 = 1 ↔ v816 = 1 ∧ v1224 = 1) := e_land h_v816 h_v1224 (of_decide_eq_true rfl)
  have h_v1226 : R 1 0 0 1 v1226 v1226 := (r_land hl h_v856 h_v1225 (of_decide_eq_true rfl))
  have e_v1226 : (v1226 = 1 ↔ v856 = 1 ∧ v1225 = 1) := e_land h_v856 h_v1225 (of_decide_eq_true rfl)
  have h_v1227 : R 1 0 0 1 v1227 v1227 := (r_land hl h_v955 h_v1226 (of_decide_eq_true rfl))
  have e_v1227 : (v1227 = 1 ↔ v955 = 1 ∧ v1226 = 1) := e_land h_v955 h_v1226 (of_decide_eq_true rfl)
  have h_v1228 : R 1 0 0 1 v1228 v1228 := (r_land hl h_v988 h_v1227 (of_decide_eq_true rfl))
  clear h_v434 h_v465 h_v575 h_v606 h_v726 h_v755 h_v782 h_v816 h_v856 h_v955 h_v1215 h_v1216 h_v1217 h_v1218 h_v1219 h_v1220 h_v1221 h_v1222 h_v1223 h_v1224 h_v1225 h_v1226
  have e_v1228 : (v1228 = 1 ↔ v988 = 1 ∧ v1227 = 1) := e_land h_v988 h_v1227 (of_decide_eq_true rfl)
  have h_v1229 : R 1 0 0 1 v1229 v1229 := (r_land hl h_v1028 h_v1228 (of_decide_eq_true rfl))
  have e_v1229 : (v1229 = 1 ↔ v1028 = 1 ∧ v1228 = 1) := e_land h_v1028 h_v1228 (of_decide_eq_true rfl)
  have h_v1230 : R 1 0 0 1 v1230 v1230 := (r_land hl h_v1125 h_v1229 (of_decide_eq_true rfl))
  have e_v1230 : (v1230 = 1 ↔ v1125 = 1 ∧ v1229 = 1) := e_land h_v1125 h_v1229 (of_decide_eq_true rfl)
  have h_v1231 : R 1 0 0 1 v1231 v1231 := (r_land hl h_v1192 h_v1230 (of_decide_eq_true rfl))
  have e_v1231 : (v1231 = 1 ↔ v1192 = 1 ∧ v1230 = 1) := e_land h_v1192 h_v1230 (of_decide_eq_true rfl)
  have h_v1232 : R 1 0 0 1 v1232 v1232 := (r_land hl h_v1200 h_v1231 (of_decide_eq_true rfl))
  have e_v1232 : (v1232 = 1 ↔ v1200 = 1 ∧ v1231 = 1) := e_land h_v1200 h_v1231 (of_decide_eq_true rfl)
  have k_v1232 : v1232 = 1 := h
  have k_v1200 : v1200 = 1 := ((e_v1232).1 k_v1232).1
  have k_v1231 : v1231 = 1 := ((e_v1232).1 k_v1232).2
  have k_v1192 : v1192 = 1 := ((e_v1231).1 k_v1231).1
  have k_v1230 : v1230 = 1 := ((e_v1231).1 k_v1231).2
  have k_v1125 : v1125 = 1 := ((e_v1230).1 k_v1230).1
  have k_v1229 : v1229 = 1 := ((e_v1230).1 k_v1230).2
  have k_v1028 : v1028 = 1 := ((e_v1229).1 k_v1229).1
  have k_v1228 : v1228 = 1 := ((e_v1229).1 k_v1229).2
  have k_v988 : v988 = 1 := ((e_v1228).1 k_v1228).1
  have k_v1227 : v1227 = 1 := ((e_v1228).1 k_v1228).2
  have k_v955 : v955 = 1 := ((e_v1227).1 k_v1227).1
  have k_v1226 : v1226 = 1 := ((e_v1227).1 k_v1227).2
  have k_v856 : v856 = 1 := ((e_v1226).1 k_v1226).1
  have k_v1225 : v1225 = 1 := ((e_v1226).1 k_v1226).2
  have k_v816 : v816 = 1 := ((e_v1225).1 k_v1225).1
  have k_v1224 : v1224 = 1 := ((e_v1225).1 k_v1225).2
  have k_v782 : v782 = 1 := ((e_v1224).1 k_v1224).1
  have k_v1223 : v1223 = 1 := ((e_v1224).1 k_v1224).2
  have k_v755 : v755 = 1 := ((e_v1223).1 k_v1223).1
  have k_v1222 : v1222 = 1 := ((e_v1223).1 k_v1223).2
  have k_v726 : v726 = 1 := ((e_v1222).1 k_v1222).1
  have k_v1221 : v1221 = 1 := ((e_v1222).1 k_v1222).2
  have k_v606 : v606 = 1 := ((e_v1221).1 k_v1221).1
  have k_v1220 : v1220 = 1 := ((e_v1221).1 k_v1221).2
  have k_v575 : v575 = 1 := ((e_v1220).1 k_v1220).1
  have k_v1219 : v1219 = 1 := ((e_v1220).1 k_v1220).2
  have k_v1218 : v1218 = 1 := ((e_v1219).1 k_v1219).2
  have k_v465 : v465 = 1 := ((e_v1218).1 k_v1218).1
  have k_v1217 : v1217 = 1 := ((e_v1218).1 k_v1218).2
  have k_v434 : v434 = 1 := ((e_v1217).1 k_v1217).1
  have k_v1216 : v1216 = 1 := ((e_v1217).1 k_v1217).2
  have k_v1215 : v1215 = 1 := ((e_v1216).1 k_v1216).2
  have k_v13 : v13 = 1 := ((e_v1215).1 k_v1215).1
  have k_v1214 : v1214 = 1 := ((e_v1215).1 k_v1215).2
  have k_v431 : v431 = 1 := ((e_v1214).1 k_v1214).1
  have k_v1213 : v1213 = 1 := ((e_v1214).1 k_v1214).2
  have k_v414 : v414 = 1 := ((e_v1213).1 k_v1213).1
  have k_v1212 : v1212 = 1 := ((e_v1213).1 k_v1213).2
  have k_v393 : v393 = 1 := ((e_v1212).1 k_v1212).1
  have k_v1211 : v1211 = 1 := ((e_v1212).1 k_v1212).2
  have k_v1210 : v1210 = 1 := ((e_v1211).1 k_v1211).2
  have k_v281 : v281 = 1 := ((e_v1210).1 k_v1210).1
  have k_v1209 : v1209 = 1 := ((e_v1210).1 k_v1210).2
  have k_v250 : v250 = 1 := ((e_v1209).1 k_v1209).1
  have k_v1208 : v1208 = 1 := ((e_v1209).1 k_v1209).2
  have k_v1207 : v1207 = 1 := ((e_v1208).1 k_v1208).2
  have k_v137 : v137 = 1 := ((e_v1207).1 k_v1207).1
  have k_v1206 : v1206 = 1 := ((e_v1207).1 k_v1207).2
  have k_v100 : v100 = 1 := ((e_v1206).1 k_v1206).1
  have k_v1205 : v1205 = 1 := ((e_v1206).1 k_v1206).2
  have k_v1204 : v1204 = 1 := ((e_v1205).1 k_v1205).2
  have k_v1203 : v1203 = 1 := ((e_v1204).1 k_v1204).2
  have k_v82 : v82 = 1 := ((e_v1203).1 k_v1203).1
  have k_v1202 : v1202 = 1 := ((e_v1203).1 k_v1203).2
  have k_v65 : v65 = 1 := ((e_v1202).1 k_v1202).1
  have k_v1201 : v1201 = 1 := ((e_v1202).1 k_v1202).2
  have k_v37 : v37 = 1 := ((e_v1201).1 k_v1201).2
  have k_v34 : v34 = 1 := ((e_v37).1 k_v37).1
  have k_v36 : v36 = 1 := ((e_v37).1 k_v37).2
  have k_v99 : v99 = 1 := ((e_v100).1 k_v100).2
  have k_v249 : v249 = 1 := ((e_v250).1 k_v250).2
  have k_v390 : v390 = 1 := ((e_v393).1 k_v393).1
  have k_v392 : v392 = 1 := ((e_v393).1 k_v393).2
  have k_v9 : v9 = 1 := ((e_v13).1 k_v13).1
  have k_v12 : v12 = 1 := ((e_v13).1 k_v13).2
  have k_v433 : v433 = 1 := ((e_v434).1 k_v434).2
  have k_v574 : v574 = 1 := ((e_v575).1 k_v575).2
  have f3 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f2 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v17) (sv v19) (sv v20) (sv v22) (sv v23) (sv v25) v27 v29 v30 (sv v31) f3 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v16 (L2.p_sel e_v17)) (L2.p_addc (-4) e_v19 e_v18) (L2.p_max e_v16 (L2.p_sel e_v20)) (L2.p_addc (4) e_v22 e_v21) e_v23 (L2.p_min e_v24 (L2.p_sel e_v25)) (L2.p_ltc (421657430) e_v26 e_v27) (L2.p_clt (421657427) e_v28 e_v29) e_v30 (L2.p_sel e_v31)
  have f39 := L2.K5_ihalf (sv v2) (sv v3) (sv v32) (sv v33) e_v32 e_v33
  have f43 := L2.K8_in_range True (sv v32) (sv v33) v34 (sv v10) v36 v37 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v35 e_v36) e_v37 (L2.X1_top _ k_v37)
  have f42 := L2.K9_isin True (sv v32) (sv v33) (sv t32.1) (sv t33.1) (sv v41) (sv v42) (sv v43) (sv v44) (sv v23) (sv v46) v47 v48 v49 (sv v50) f43 (L2.p_sin e_t32_1) (L2.p_sin e_t33_1) (L2.p_min e_v40 (L2.p_sel e_v41)) (L2.p_addc (-4) (L2.p_add_comm e_v42) e_v18) (L2.p_max e_v40 (L2.p_sel e_v43)) (L2.p_addc (4) (L2.p_add_comm e_v44) e_v21) e_v23 (L2.p_min e_v45 (L2.p_sel e_v46)) (L2.p_ltc (421657430) e_v26 e_v47) (L2.p_clt (421657427) e_v28 e_v48) e_v49 (L2.p_sel e_v50)
  have f79 := L2.K6_imul True (sv v19) (sv v31) (sv v42) (sv v50) (sv v51) v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 (sv v68) v69 v70 (sv v71) v72 v73 (sv v74) v75 v76 (sv v77) (sv v79) (sv v81) e_v51 e_v52 e_v53 e_v54 e_v55 (L2.p_and_comm e_v56) e_v57 e_v58 e_v59 e_v60 e_v61 (L2.p_and_comm e_v62) e_v63 e_v64 e_v65 (L2.X1_top _ k_v65) e_v66 e_v67 (L2.p_sel e_v68) e_v69 e_v70 (L2.p_sel e_v71) e_v72 e_v73 (L2.p_sel e_v74) e_v75 e_v76 (L2.p_sel e_v77) (L2.p_mul (L2.p_mul_comm e_v78) e_v79) (L2.p_mulc (L2.p_mul_comm e_v80) e_v81)
  have f1 := L2.K14_iso_base_a True (sv v2) (sv v3) (sv v0) (sv v1) (sv v19) (sv v31) (sv v32) (sv v33) (sv v42) (sv v50) (sv v79) (sv v81) v82 f2 f39 f42 f79 (L2.p_clt (-1) e_v8 e_v82) (L2.X1_top _ k_v82)
  have f118 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f128 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v84) (sv v85) (sv v87) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v84) e_v18) e_v85 (L2.p_max e_v86 (L2.p_sel e_v87))
  have f142 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v92) (sv v23) (sv v94) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v92) e_v21) e_v23 (L2.p_min e_v93 (L2.p_sel e_v94))
  have f117 := L2.K10_icos True (sv v0) (sv v1) (sv v87) (sv v85) v89 (sv v90) (sv v94) (sv v23) v96 (sv v97) f118 f128 e_v85 (L2.p_clt (843314855) e_v88 e_v89) (L2.p_sel e_v90) f142 e_v23 (L2.p_ltc (1) e_v95 e_v96) (L2.p_sel e_v97)
  have f157 := L2.K5_ihalf (sv v3) (sv v3) (sv v98) (sv v33) e_v98 e_v33
  have f161 := L2.K8_in_range True (sv v98) (sv v33) v99 (sv v10) v36 v100 (L2.p_clt (-1) e_v8 e_v99) e_v10 (L2.p_le e_v35 e_v36) (L2.p_and_comm e_v100) (L2.X1_top _ k_v100)
  let u101 : ℤ := L2.cosI (sv v33)
  let u102 : ℤ := (sv v18) + u101
  let u103 : ℕ := if u102 < (sv v85) then 1 else 0
  let u104 : ℤ := if u103 = 1 then (sv v85) else u102
  have f171 := L2.K3_cos_lo (sv v33) u101 u102 (sv v85) u104 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u105 : ℕ := if (sv v88) < (sv v33) then 1 else 0
  let u106 : ℤ := if u105 = 1 then (sv v85) else u104
  let u107 : ℤ := L2.cosI (sv v98)
  let u108 : ℤ := (sv v21) + u107
  let u109 : ℕ := if u108 < (sv v23) then 1 else 0
  let u110 : ℤ := if u109 = 1 then u108 else (sv v23)
  have f185 := L2.K3_cos_hi (sv v98) u107 u108 (sv v23) u110 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u111 : ℕ := if (sv v98) < (sv v95) then 1 else 0
  let u112 : ℤ := if u111 = 1 then (sv v23) else u110
  have f160 := L2.K10_icos True (sv v98) (sv v33) u104 (sv v85) u105 u106 u110 (sv v23) u111 u112 f161 f171 e_v85 (L2.p_clt (843314855) e_v88 (L2.p_ult _ _)) rfl f185 e_v23 (L2.p_ltc (1) e_v95 (L2.p_ult _ _)) rfl
  have f200 := L2.K8_in_range True (sv v98) (sv v33) v99 (sv v10) v36 v100 (L2.p_clt (-1) e_v8 e_v99) e_v10 (L2.p_le e_v35 e_v36) (L2.p_and_comm e_v100) (L2.X1_top _ k_v100)
  have f199 := L2.K9_isin True (sv v98) (sv v33) (sv t98.1) (sv t33.1) (sv v115) (sv v116) (sv v117) (sv v118) (sv v23) (sv v120) v121 v48 v122 (sv v123) f200 (L2.p_sin e_t98_1) (L2.p_sin e_t33_1) (L2.p_min e_v114 (L2.p_sel e_v115)) (L2.p_addc (-4) (L2.p_add_comm e_v116) e_v18) (L2.p_max e_v114 (L2.p_sel e_v117)) (L2.p_addc (4) (L2.p_add_comm e_v118) e_v21) e_v23 (L2.p_min e_v119 (L2.p_sel e_v120)) (L2.p_ltc (421657430) e_v26 e_v121) (L2.p_clt (421657427) e_v28 e_v48) (L2.p_and_comm e_v122) (L2.p_sel e_v123)
  let u131 : ℕ := if v130 = 1 then 0 else 1
  let u133 : ℕ := if v132 = 1 then 0 else 1
  let u134 : ℕ := if v130 = 1 ∧ u133 = 1 then 1 else 0
  let u138 : ℕ := if v125 = 1 ∧ v135 = 1 then 1 else 0
  let u139 : ℕ := if u134 = 1 ∨ u138 = 1 then 1 else 0
  let u140 : ℤ := if u139 = 1 then (sv v97) else (sv v90)
  let u141 : ℕ := if v129 = 1 ∧ u131 = 1 then 1 else 0
  let u142 : ℕ := if v128 = 1 ∨ u141 = 1 then 1 else 0
  let u143 : ℤ := if u142 = 1 then (sv v123) else (sv v116)
  let u144 : ℕ := if v128 = 1 ∧ v135 = 1 then 1 else 0
  let u145 : ℕ := if u134 = 1 ∨ u144 = 1 then 1 else 0
  let u146 : ℤ := if u145 = 1 then (sv v90) else (sv v97)
  let u147 : ℕ := if v129 = 1 ∧ u134 = 1 then 1 else 0
  let u148 : ℕ := if v128 = 1 ∨ u147 = 1 then 1 else 0
  let u149 : ℤ := if u148 = 1 then (sv v116) else (sv v123)
  let u150 : ℤ := u140 * u143
  let u151 : ℤ := u150 / 2 ^ 28
  let u152 : ℤ := u146 * u149
  let u153 : ℤ := -((-u152) / 2 ^ 28)
  have f236 := L2.K6_imul True (sv v90) (sv v97) (sv v116) (sv v123) (sv v51) v124 v125 v126 v127 v128 v129 v130 u131 v132 u133 u134 v135 v136 v137 u138 u139 u140 u141 u142 u143 u144 u145 u146 u147 u148 u149 u151 u153 e_v51 e_v124 e_v125 e_v126 e_v127 (L2.p_and_comm e_v128) e_v129 e_v130 (L2.p_unot _) e_v132 (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) e_v135 e_v136 e_v137 (L2.X1_top _ k_v137) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl)
  let u154 : ℕ := if (sv v51) < u151 then 1 else 0
  let u155 : ℕ := if u154 = 1 then 0 else 1
  let u156 : ℕ := if u106 < (sv v51) then 1 else 0
  let u157 : ℤ := if u156 = 1 then u151 else u153
  let u158 : ℕ := if u112 < (sv v51) then 1 else 0
  let u159 : ℤ := if u158 = 1 then u153 else u151
  have f269 := L2.K11_qdiv u106 u112 u151 u153 u154 u155 (sv v51) u156 u157 u158 u159 (L2.p_clt (0) e_v51 (L2.p_ult _ _)) (L2.p_unot _) e_v51 (L2.p_ult _ _) rfl (L2.p_ult _ _) rfl
  let u160 : ℤ := (sv v51) - u106
  let u161 : ℤ := if u156 = 1 then u160 else u106
  let u162 : ℤ := 0
  let u163 : ℕ := if u156 = 1 then 0 else 1
  let u164 : ℤ := L2.cosI u162
  let u165 : ℤ := (sv v18) + u164
  let u166 : ℕ := if u165 < (sv v85) then 1 else 0
  let u167 : ℤ := if u166 = 1 then (sv v85) else u165
  have f287 := L2.K3_cos_lo u162 u164 u165 (sv v85) u167 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u168 : ℤ := (sv v21) + u164
  let u169 : ℕ := if u168 < (sv v23) then 1 else 0
  let u170 : ℤ := if u169 = 1 then u168 else (sv v23)
  have f296 := L2.K3_cos_hi u162 u164 u168 (sv v23) u170 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u171 : ℤ := L2.sinI u162
  let u172 : ℤ := (sv v21) + u171
  let u173 : ℕ := if u172 < (sv v23) then 1 else 0
  let u174 : ℤ := if u173 = 1 then u172 else (sv v23)
  have f305 := L2.K3_sin_hi u162 u171 u172 (sv v23) u174 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u175 : ℤ := (sv v18) + u171
  have f314 := L2.K3_sin_lo u162 u171 u175 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u176 : ℤ := if u163 = 1 then u167 else u170
  let u177 : ℤ := if u163 = 1 then u174 else u175
  let u178 : ℤ := u157 * u177
  let u179 : ℤ := u161 * u176
  let u180 : ℕ := if u179 < u178 then 1 else 0
  let u181 : ℕ := if u180 = 1 then 0 else 1
  let u182 : ℕ := if u178 < u179 then 1 else 0
  let u183 : ℕ := if u182 = 1 then 0 else 1
  let u184 : ℕ := if (sv v51) < u162 then 1 else 0
  let u185 : ℕ := if u184 = 1 then 0 else 1
  let u187 : ℕ := if (sv v186) < u162 then 1 else 0
  let u188 : ℕ := if u187 = 1 then 0 else 1
  let u189 : ℕ := if (sv v8) < u167 then 1 else 0
  let u190 : ℕ := if u181 = 1 ∧ u189 = 1 then 1 else 0
  let u191 : ℕ := if u188 = 1 ∧ u190 = 1 then 1 else 0
  let u192 : ℕ := if u185 = 1 ∨ u191 = 1 then 1 else 0
  let u194 : ℕ := if u162 < (sv v193) then 1 else 0
  let u195 : ℕ := if u194 = 1 then 0 else 1
  let u196 : ℕ := if u183 = 1 ∨ u195 = 1 then 1 else 0
  let u197 : ℕ := if u163 = 1 ∧ u192 = 1 then 1 else 0
  let u198 : ℕ := if u156 = 1 ∧ u196 = 1 then 1 else 0
  let u199 : ℕ := if u197 = 1 ∨ u198 = 1 then 1 else 0
  let u200 : ℤ := (sv v51) - u162
  let u201 : ℤ := if u156 = 1 then u200 else u162
  let u202 : ℤ := -421657429
  let u203 : ℤ := if u199 = 1 then u201 else u202
  have f280 := L2.K12_atan_lo u106 u157 (sv v51) u156 u160 u161 u162 u163 u167 u170 u174 u175 u176 u177 u178 u179 u181 u183 u184 u185 (sv v186) u188 u189 u190 u191 u192 (sv v193) u195 u196 u197 u156 u198 u199 u200 u201 u202 u203 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f287 f296 f305 f314 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v186 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v193 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  let u204 : ℤ := (sv v51) - u112
  let u205 : ℤ := if u158 = 1 then u204 else u112
  let u206 : ℤ := 0
  let u207 : ℤ := L2.cosI u206
  let u208 : ℤ := (sv v18) + u207
  let u209 : ℕ := if u208 < (sv v85) then 1 else 0
  let u210 : ℤ := if u209 = 1 then (sv v85) else u208
  have f360 := L2.K3_cos_lo u206 u207 u208 (sv v85) u210 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u211 : ℤ := (sv v21) + u207
  let u212 : ℕ := if u211 < (sv v23) then 1 else 0
  let u213 : ℤ := if u212 = 1 then u211 else (sv v23)
  have f369 := L2.K3_cos_hi u206 u207 u211 (sv v23) u213 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u214 : ℤ := L2.sinI u206
  let u215 : ℤ := (sv v21) + u214
  let u216 : ℕ := if u215 < (sv v23) then 1 else 0
  let u217 : ℤ := if u216 = 1 then u215 else (sv v23)
  have f378 := L2.K3_sin_hi u206 u214 u215 (sv v23) u217 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u218 : ℤ := (sv v18) + u214
  have f387 := L2.K3_sin_lo u206 u214 u218 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u219 : ℤ := if u158 = 1 then u210 else u213
  let u220 : ℤ := if u158 = 1 then u217 else u218
  let u221 : ℤ := u159 * u220
  let u222 : ℤ := u205 * u219
  let u223 : ℕ := if u222 < u221 then 1 else 0
  let u224 : ℕ := if u223 = 1 then 0 else 1
  let u225 : ℕ := if u221 < u222 then 1 else 0
  let u226 : ℕ := if u225 = 1 then 0 else 1
  let u227 : ℕ := if (sv v51) < u206 then 1 else 0
  let u228 : ℕ := if u227 = 1 then 0 else 1
  let u229 : ℕ := if (sv v186) < u206 then 1 else 0
  let u230 : ℕ := if u229 = 1 then 0 else 1
  let u231 : ℕ := if (sv v8) < u210 then 1 else 0
  let u232 : ℕ := if u224 = 1 ∧ u231 = 1 then 1 else 0
  let u233 : ℕ := if u230 = 1 ∧ u232 = 1 then 1 else 0
  let u234 : ℕ := if u228 = 1 ∨ u233 = 1 then 1 else 0
  let u235 : ℕ := if u206 < (sv v193) then 1 else 0
  let u236 : ℕ := if u235 = 1 then 0 else 1
  let u237 : ℕ := if u226 = 1 ∨ u236 = 1 then 1 else 0
  let u238 : ℕ := if u158 = 1 ∧ u234 = 1 then 1 else 0
  let u239 : ℕ := if u158 = 1 then 0 else 1
  let u240 : ℕ := if u237 = 1 ∧ u239 = 1 then 1 else 0
  let u241 : ℕ := if u238 = 1 ∨ u240 = 1 then 1 else 0
  let u242 : ℤ := (sv v51) - u206
  let u243 : ℤ := if u158 = 1 then u242 else u206
  let u244 : ℤ := if u241 = 1 then u243 else (sv v193)
  have f354 := L2.K12_atan_hi u112 u159 (sv v51) u158 u204 u205 u206 u210 u213 u217 u218 u219 u220 u221 u222 u224 u226 u227 u228 (sv v186) u230 u231 u232 u233 u234 (sv v193) u236 u237 u238 u239 u240 u241 u242 u243 (sv v193) u244 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f360 f369 f378 f387 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v186 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v193 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v193 rfl
  let u245 : ℤ := if u155 = 1 then u202 else u203
  let u246 : ℤ := if u155 = 1 then (sv v193) else u244
  have f156 := L2.K19_iso_angle_pt True (sv v3) (sv v90) (sv v97) (sv v98) (sv v33) u106 u112 (sv v116) (sv v123) u151 u153 u157 u159 u155 u154 u203 u244 u202 (sv v193) u245 u246 f157 f160 f199 f236 f269 (L2.p_not_not (L2.p_unot _)) f280 f354 rfl e_v193 rfl rfl
  have f432 := L2.K5_ihalf (sv v2) (sv v2) (sv v32) (sv v247) e_v32 e_v247
  have f436 := L2.K8_in_range True (sv v32) (sv v247) v34 (sv v10) v249 v250 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v248 e_v249) e_v250 (L2.X1_top _ k_v250)
  let u251 : ℤ := L2.cosI (sv v247)
  let u252 : ℤ := (sv v18) + u251
  let u253 : ℕ := if u252 < (sv v85) then 1 else 0
  let u254 : ℤ := if u253 = 1 then (sv v85) else u252
  have f446 := L2.K3_cos_lo (sv v247) u251 u252 (sv v85) u254 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u255 : ℕ := if (sv v88) < (sv v247) then 1 else 0
  let u256 : ℤ := if u255 = 1 then (sv v85) else u254
  have f460 := L2.K3_cos_hi (sv v32) (sv t32.2) (sv v258) (sv v23) (sv v260) (L2.p_cos e_t32_2) (L2.p_addc (4) (L2.p_add_comm e_v258) e_v21) e_v23 (L2.p_min e_v259 (L2.p_sel e_v260))
  have f435 := L2.K10_icos True (sv v32) (sv v247) u254 (sv v85) u255 u256 (sv v260) (sv v23) v261 (sv v262) f436 f446 e_v85 (L2.p_clt (843314855) e_v88 (L2.p_ult _ _)) rfl f460 e_v23 (L2.p_ltc (1) e_v95 e_v261) (L2.p_sel e_v262)
  have f475 := L2.K8_in_range True (sv v32) (sv v247) v34 (sv v10) v249 v250 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v248 e_v249) e_v250 (L2.X1_top _ k_v250)
  have f474 := L2.K9_isin True (sv v32) (sv v247) (sv t32.1) (sv t247.1) (sv v265) (sv v266) (sv v267) (sv v268) (sv v23) (sv v270) v47 v271 v272 (sv v273) f475 (L2.p_sin e_t32_1) (L2.p_sin e_t247_1) (L2.p_min e_v264 (L2.p_sel e_v265)) (L2.p_addc (-4) (L2.p_add_comm e_v266) e_v18) (L2.p_max e_v264 (L2.p_sel e_v267)) (L2.p_addc (4) (L2.p_add_comm e_v268) e_v21) e_v23 (L2.p_min e_v269 (L2.p_sel e_v270)) (L2.p_ltc (421657430) e_v26 e_v47) (L2.p_clt (421657427) e_v28 e_v271) e_v272 (L2.p_sel e_v273)
  have f511 := L2.K6_imul True (sv v90) (sv v97) (sv v266) (sv v273) (sv v51) v124 v125 v126 v127 v128 v129 v274 v275 v276 v277 v278 v279 v280 v281 v282 v283 (sv v284) v285 v286 (sv v287) v288 v289 (sv v290) v291 v292 (sv v293) (sv v295) (sv v297) e_v51 e_v124 e_v125 e_v126 e_v127 (L2.p_and_comm e_v128) e_v129 e_v274 e_v275 e_v276 e_v277 (L2.p_and_comm e_v278) e_v279 e_v280 e_v281 (L2.X1_top _ k_v281) e_v282 e_v283 (L2.p_sel e_v284) e_v285 e_v286 (L2.p_sel e_v287) e_v288 e_v289 (L2.p_sel e_v290) e_v291 e_v292 (L2.p_sel e_v293) (L2.p_mul (L2.p_mul_comm e_v294) e_v295) (L2.p_mulc (L2.p_mul_comm e_v296) e_v297)
  let u300 : ℕ := if u256 < (sv v51) then 1 else 0
  let u301 : ℤ := if u300 = 1 then (sv v295) else (sv v297)
  have f544 := L2.K11_qdiv u256 (sv v262) (sv v295) (sv v297) v298 v299 (sv v51) u300 u301 v302 (sv v303) (L2.p_clt (0) e_v51 e_v298) e_v299 e_v51 (L2.p_ult _ _) rfl e_v302 (L2.p_sel e_v303)
  let u304 : ℤ := (sv v51) - u256
  let u305 : ℤ := if u300 = 1 then u304 else u256
  let u306 : ℤ := 0
  let u307 : ℕ := if u300 = 1 then 0 else 1
  let u308 : ℤ := L2.cosI u306
  let u309 : ℤ := (sv v18) + u308
  let u310 : ℕ := if u309 < (sv v85) then 1 else 0
  let u311 : ℤ := if u310 = 1 then (sv v85) else u309
  have f562 := L2.K3_cos_lo u306 u308 u309 (sv v85) u311 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u312 : ℤ := (sv v21) + u308
  let u313 : ℕ := if u312 < (sv v23) then 1 else 0
  let u314 : ℤ := if u313 = 1 then u312 else (sv v23)
  have f571 := L2.K3_cos_hi u306 u308 u312 (sv v23) u314 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u315 : ℤ := L2.sinI u306
  let u316 : ℤ := (sv v21) + u315
  let u317 : ℕ := if u316 < (sv v23) then 1 else 0
  let u318 : ℤ := if u317 = 1 then u316 else (sv v23)
  have f580 := L2.K3_sin_hi u306 u315 u316 (sv v23) u318 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u319 : ℤ := (sv v18) + u315
  have f589 := L2.K3_sin_lo u306 u315 u319 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u320 : ℤ := if u307 = 1 then u311 else u314
  let u321 : ℤ := if u307 = 1 then u318 else u319
  let u322 : ℤ := u301 * u321
  let u323 : ℤ := u305 * u320
  let u324 : ℕ := if u323 < u322 then 1 else 0
  let u325 : ℕ := if u324 = 1 then 0 else 1
  let u326 : ℕ := if u322 < u323 then 1 else 0
  let u327 : ℕ := if u326 = 1 then 0 else 1
  let u328 : ℕ := if (sv v51) < u306 then 1 else 0
  let u329 : ℕ := if u328 = 1 then 0 else 1
  let u330 : ℕ := if (sv v186) < u306 then 1 else 0
  let u331 : ℕ := if u330 = 1 then 0 else 1
  let u332 : ℕ := if (sv v8) < u311 then 1 else 0
  let u333 : ℕ := if u325 = 1 ∧ u332 = 1 then 1 else 0
  let u334 : ℕ := if u331 = 1 ∧ u333 = 1 then 1 else 0
  let u335 : ℕ := if u329 = 1 ∨ u334 = 1 then 1 else 0
  let u336 : ℕ := if u306 < (sv v193) then 1 else 0
  let u337 : ℕ := if u336 = 1 then 0 else 1
  let u338 : ℕ := if u327 = 1 ∨ u337 = 1 then 1 else 0
  let u339 : ℕ := if u307 = 1 ∧ u335 = 1 then 1 else 0
  let u340 : ℕ := if u300 = 1 ∧ u338 = 1 then 1 else 0
  let u341 : ℕ := if u339 = 1 ∨ u340 = 1 then 1 else 0
  let u342 : ℤ := (sv v51) - u306
  let u343 : ℤ := if u300 = 1 then u342 else u306
  let u344 : ℤ := if u341 = 1 then u343 else u202
  have f555 := L2.K12_atan_lo u256 u301 (sv v51) u300 u304 u305 u306 u307 u311 u314 u318 u319 u320 u321 u322 u323 u325 u327 u328 u329 (sv v186) u331 u332 u333 u334 u335 (sv v193) u337 u338 u339 u300 u340 u341 u342 u343 u202 u344 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f562 f571 f580 f589 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v186 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v193 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  have f635 := L2.K3_cos_lo (sv v347) (sv t347.2) (sv v349) (sv v85) (sv v351) (L2.p_cos e_t347_2) (L2.p_addc (-4) (L2.p_add_comm e_v349) e_v18) e_v85 (L2.p_max e_v350 (L2.p_sel e_v351))
  have f644 := L2.K3_cos_hi (sv v347) (sv t347.2) (sv v352) (sv v23) (sv v354) (L2.p_cos e_t347_2) (L2.p_addc (4) (L2.p_add_comm e_v352) e_v21) e_v23 (L2.p_min e_v353 (L2.p_sel e_v354))
  have f653 := L2.K3_sin_hi (sv v347) (sv t347.1) (sv v356) (sv v23) (sv v358) (L2.p_sin e_t347_1) (L2.p_addc (4) (L2.p_add_comm e_v356) e_v21) e_v23 (L2.p_min e_v357 (L2.p_sel e_v358))
  have f662 := L2.K3_sin_lo (sv v347) (sv t347.1) (sv v359) (L2.p_sin e_t347_1) (L2.p_addc (-4) (L2.p_add_comm e_v359) e_v18)
  have f629 := L2.K12_atan_hi (sv v262) (sv v303) (sv v51) v302 (sv v345) (sv v346) (sv v347) (sv v351) (sv v354) (sv v358) (sv v359) (sv v360) (sv v361) (sv v362) (sv v363) v365 v367 v368 v369 (sv v186) v371 v372 v373 v374 v375 (sv v193) v377 v378 v379 v380 v381 v382 (sv v383) (sv v384) (sv v193) (sv v385) e_v51 e_v302 e_v345 (L2.p_sel e_v346) (L2.p_hint e_v347) f635 f644 f653 f662 (L2.p_sel e_v360) (L2.p_sel e_v361) (L2.p_mul_comm e_v362) (L2.p_mul_comm e_v363) (L2.p_le e_v364 e_v365) (L2.p_le e_v366 e_v367) e_v368 e_v369 e_v186 (L2.p_le e_v370 e_v371) (L2.p_clt (-1) e_v8 e_v372) e_v373 (L2.p_and_comm e_v374) e_v375 e_v193 (L2.p_le e_v376 e_v377) (L2.p_or_comm e_v378) e_v379 e_v380 (L2.p_and_comm e_v381) e_v382 e_v383 (L2.p_sel e_v384) e_v193 (L2.p_sel e_v385)
  let u386 : ℤ := if v299 = 1 then u202 else u344
  have f431 := L2.K19_iso_angle_pt True (sv v2) (sv v90) (sv v97) (sv v32) (sv v247) u256 (sv v262) (sv v266) (sv v273) (sv v295) (sv v297) u301 (sv v303) v299 v298 u344 (sv v385) u202 (sv v193) u386 (sv v387) f432 f435 f474 f511 f544 (L2.p_not_not e_v299) f555 f629 rfl e_v193 rfl (L2.p_sel e_v387)
  have f116 := L2.K20_iso_angle True (sv v2) (sv v3) (sv v0) (sv v1) (sv v90) (sv v97) u245 u246 u155 u386 (sv v387) v299 f117 f156 f431
  have f708 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f707 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v17) (sv v19) (sv v20) (sv v22) (sv v23) (sv v25) v27 v29 v30 (sv v31) f708 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v16 (L2.p_sel e_v17)) (L2.p_addc (-4) e_v19 e_v18) (L2.p_max e_v16 (L2.p_sel e_v20)) (L2.p_addc (4) e_v22 e_v21) e_v23 (L2.p_min e_v24 (L2.p_sel e_v25)) (L2.p_ltc (421657430) e_v26 e_v27) (L2.p_clt (421657427) e_v28 e_v29) e_v30 (L2.p_sel e_v31)
  have f744 := L2.K5_ihalf (sv v4) (sv v5) (sv v388) (sv v389) e_v388 e_v389
  have f748 := L2.K8_in_range True (sv v388) (sv v389) v390 (sv v10) v392 v393 (L2.p_clt (-1) e_v8 e_v390) e_v10 (L2.p_le e_v391 e_v392) e_v393 (L2.X1_top _ k_v393)
  have f747 := L2.K9_isin True (sv v388) (sv v389) (sv t388.1) (sv t389.1) (sv v397) (sv v398) (sv v399) (sv v400) (sv v23) (sv v402) v403 v404 v405 (sv v406) f748 (L2.p_sin e_t388_1) (L2.p_sin e_t389_1) (L2.p_min e_v396 (L2.p_sel e_v397)) (L2.p_addc (-4) (L2.p_add_comm e_v398) e_v18) (L2.p_max e_v396 (L2.p_sel e_v399)) (L2.p_addc (4) (L2.p_add_comm e_v400) e_v21) e_v23 (L2.p_min e_v401 (L2.p_sel e_v402)) (L2.p_ltc (421657430) e_v26 e_v403) (L2.p_clt (421657427) e_v28 e_v404) e_v405 (L2.p_sel e_v406)
  have f784 := L2.K6_imul True (sv v19) (sv v31) (sv v398) (sv v406) (sv v51) v52 v53 v54 v55 v56 v57 v407 v408 v409 v410 v411 v412 v413 v414 v415 v416 (sv v417) v418 v419 (sv v420) v421 v422 (sv v423) v424 v425 (sv v426) (sv v428) (sv v430) e_v51 e_v52 e_v53 e_v54 e_v55 (L2.p_and_comm e_v56) e_v57 e_v407 e_v408 e_v409 e_v410 (L2.p_and_comm e_v411) e_v412 e_v413 e_v414 (L2.X1_top _ k_v414) e_v415 e_v416 (L2.p_sel e_v417) e_v418 e_v419 (L2.p_sel e_v420) e_v421 e_v422 (L2.p_sel e_v423) e_v424 e_v425 (L2.p_sel e_v426) (L2.p_mul (L2.p_mul_comm e_v427) e_v428) (L2.p_mulc (L2.p_mul_comm e_v429) e_v430)
  have f706 := L2.K14_iso_base_a True (sv v4) (sv v5) (sv v0) (sv v1) (sv v19) (sv v31) (sv v388) (sv v389) (sv v398) (sv v406) (sv v428) (sv v430) v431 f707 f744 f747 f784 (L2.p_clt (-1) e_v8 e_v431) (L2.X1_top _ k_v431)
  have f823 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f833 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v84) (sv v85) (sv v87) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v84) e_v18) e_v85 (L2.p_max e_v86 (L2.p_sel e_v87))
  have f847 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v92) (sv v23) (sv v94) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v92) e_v21) e_v23 (L2.p_min e_v93 (L2.p_sel e_v94))
  have f822 := L2.K10_icos True (sv v0) (sv v1) (sv v87) (sv v85) v89 (sv v90) (sv v94) (sv v23) v96 (sv v97) f823 f833 e_v85 (L2.p_clt (843314855) e_v88 e_v89) (L2.p_sel e_v90) f847 e_v23 (L2.p_ltc (1) e_v95 e_v96) (L2.p_sel e_v97)
  have f862 := L2.K5_ihalf (sv v5) (sv v5) (sv v432) (sv v389) e_v432 e_v389
  have f866 := L2.K8_in_range True (sv v432) (sv v389) v433 (sv v10) v392 v434 (L2.p_clt (-1) e_v8 e_v433) e_v10 (L2.p_le e_v391 e_v392) (L2.p_and_comm e_v434) (L2.X1_top _ k_v434)
  let u435 : ℤ := L2.cosI (sv v389)
  let u436 : ℤ := (sv v18) + u435
  let u437 : ℕ := if u436 < (sv v85) then 1 else 0
  let u438 : ℤ := if u437 = 1 then (sv v85) else u436
  have f876 := L2.K3_cos_lo (sv v389) u435 u436 (sv v85) u438 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u439 : ℕ := if (sv v88) < (sv v389) then 1 else 0
  let u440 : ℤ := if u439 = 1 then (sv v85) else u438
  let u441 : ℤ := L2.cosI (sv v432)
  let u442 : ℤ := (sv v21) + u441
  let u443 : ℕ := if u442 < (sv v23) then 1 else 0
  let u444 : ℤ := if u443 = 1 then u442 else (sv v23)
  have f890 := L2.K3_cos_hi (sv v432) u441 u442 (sv v23) u444 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u445 : ℕ := if (sv v432) < (sv v95) then 1 else 0
  let u446 : ℤ := if u445 = 1 then (sv v23) else u444
  have f865 := L2.K10_icos True (sv v432) (sv v389) u438 (sv v85) u439 u440 u444 (sv v23) u445 u446 f866 f876 e_v85 (L2.p_clt (843314855) e_v88 (L2.p_ult _ _)) rfl f890 e_v23 (L2.p_ltc (1) e_v95 (L2.p_ult _ _)) rfl
  have f905 := L2.K8_in_range True (sv v432) (sv v389) v433 (sv v10) v392 v434 (L2.p_clt (-1) e_v8 e_v433) e_v10 (L2.p_le e_v391 e_v392) (L2.p_and_comm e_v434) (L2.X1_top _ k_v434)
  have f904 := L2.K9_isin True (sv v432) (sv v389) (sv t432.1) (sv t389.1) (sv v449) (sv v450) (sv v451) (sv v452) (sv v23) (sv v454) v455 v404 v456 (sv v457) f905 (L2.p_sin e_t432_1) (L2.p_sin e_t389_1) (L2.p_min e_v448 (L2.p_sel e_v449)) (L2.p_addc (-4) (L2.p_add_comm e_v450) e_v18) (L2.p_max e_v448 (L2.p_sel e_v451)) (L2.p_addc (4) (L2.p_add_comm e_v452) e_v21) e_v23 (L2.p_min e_v453 (L2.p_sel e_v454)) (L2.p_ltc (421657430) e_v26 e_v455) (L2.p_clt (421657427) e_v28 e_v404) (L2.p_and_comm e_v456) (L2.p_sel e_v457)
  let u459 : ℕ := if v458 = 1 then 0 else 1
  let u461 : ℕ := if v460 = 1 then 0 else 1
  let u462 : ℕ := if v458 = 1 ∧ u461 = 1 then 1 else 0
  let u466 : ℕ := if v125 = 1 ∧ v463 = 1 then 1 else 0
  let u467 : ℕ := if u462 = 1 ∨ u466 = 1 then 1 else 0
  let u468 : ℤ := if u467 = 1 then (sv v97) else (sv v90)
  let u469 : ℕ := if v129 = 1 ∧ u459 = 1 then 1 else 0
  let u470 : ℕ := if v128 = 1 ∨ u469 = 1 then 1 else 0
  let u471 : ℤ := if u470 = 1 then (sv v457) else (sv v450)
  let u472 : ℕ := if v128 = 1 ∧ v463 = 1 then 1 else 0
  let u473 : ℕ := if u462 = 1 ∨ u472 = 1 then 1 else 0
  let u474 : ℤ := if u473 = 1 then (sv v90) else (sv v97)
  let u475 : ℕ := if v129 = 1 ∧ u462 = 1 then 1 else 0
  let u476 : ℕ := if v128 = 1 ∨ u475 = 1 then 1 else 0
  let u477 : ℤ := if u476 = 1 then (sv v450) else (sv v457)
  let u478 : ℤ := u468 * u471
  let u479 : ℤ := u478 / 2 ^ 28
  let u480 : ℤ := u474 * u477
  let u481 : ℤ := -((-u480) / 2 ^ 28)
  have f941 := L2.K6_imul True (sv v90) (sv v97) (sv v450) (sv v457) (sv v51) v124 v125 v126 v127 v128 v129 v458 u459 v460 u461 u462 v463 v464 v465 u466 u467 u468 u469 u470 u471 u472 u473 u474 u475 u476 u477 u479 u481 e_v51 e_v124 e_v125 e_v126 e_v127 (L2.p_and_comm e_v128) e_v129 e_v458 (L2.p_unot _) e_v460 (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) e_v463 e_v464 e_v465 (L2.X1_top _ k_v465) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl)
  let u482 : ℕ := if (sv v51) < u479 then 1 else 0
  let u483 : ℕ := if u482 = 1 then 0 else 1
  let u484 : ℕ := if u440 < (sv v51) then 1 else 0
  let u485 : ℤ := if u484 = 1 then u479 else u481
  let u486 : ℕ := if u446 < (sv v51) then 1 else 0
  let u487 : ℤ := if u486 = 1 then u481 else u479
  have f974 := L2.K11_qdiv u440 u446 u479 u481 u482 u483 (sv v51) u484 u485 u486 u487 (L2.p_clt (0) e_v51 (L2.p_ult _ _)) (L2.p_unot _) e_v51 (L2.p_ult _ _) rfl (L2.p_ult _ _) rfl
  let u488 : ℤ := (sv v51) - u440
  let u489 : ℤ := if u484 = 1 then u488 else u440
  let u490 : ℤ := 0
  let u491 : ℕ := if u484 = 1 then 0 else 1
  let u492 : ℤ := L2.cosI u490
  let u493 : ℤ := (sv v18) + u492
  let u494 : ℕ := if u493 < (sv v85) then 1 else 0
  let u495 : ℤ := if u494 = 1 then (sv v85) else u493
  have f992 := L2.K3_cos_lo u490 u492 u493 (sv v85) u495 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u496 : ℤ := (sv v21) + u492
  let u497 : ℕ := if u496 < (sv v23) then 1 else 0
  let u498 : ℤ := if u497 = 1 then u496 else (sv v23)
  have f1001 := L2.K3_cos_hi u490 u492 u496 (sv v23) u498 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u499 : ℤ := L2.sinI u490
  let u500 : ℤ := (sv v21) + u499
  let u501 : ℕ := if u500 < (sv v23) then 1 else 0
  let u502 : ℤ := if u501 = 1 then u500 else (sv v23)
  have f1010 := L2.K3_sin_hi u490 u499 u500 (sv v23) u502 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u503 : ℤ := (sv v18) + u499
  have f1019 := L2.K3_sin_lo u490 u499 u503 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u504 : ℤ := if u491 = 1 then u495 else u498
  let u505 : ℤ := if u491 = 1 then u502 else u503
  let u506 : ℤ := u485 * u505
  let u507 : ℤ := u489 * u504
  let u508 : ℕ := if u507 < u506 then 1 else 0
  let u509 : ℕ := if u508 = 1 then 0 else 1
  let u510 : ℕ := if u506 < u507 then 1 else 0
  let u511 : ℕ := if u510 = 1 then 0 else 1
  let u512 : ℕ := if (sv v51) < u490 then 1 else 0
  let u513 : ℕ := if u512 = 1 then 0 else 1
  let u514 : ℕ := if (sv v186) < u490 then 1 else 0
  let u515 : ℕ := if u514 = 1 then 0 else 1
  let u516 : ℕ := if (sv v8) < u495 then 1 else 0
  let u517 : ℕ := if u509 = 1 ∧ u516 = 1 then 1 else 0
  let u518 : ℕ := if u515 = 1 ∧ u517 = 1 then 1 else 0
  let u519 : ℕ := if u513 = 1 ∨ u518 = 1 then 1 else 0
  let u520 : ℕ := if u490 < (sv v193) then 1 else 0
  let u521 : ℕ := if u520 = 1 then 0 else 1
  let u522 : ℕ := if u511 = 1 ∨ u521 = 1 then 1 else 0
  let u523 : ℕ := if u491 = 1 ∧ u519 = 1 then 1 else 0
  let u524 : ℕ := if u484 = 1 ∧ u522 = 1 then 1 else 0
  let u525 : ℕ := if u523 = 1 ∨ u524 = 1 then 1 else 0
  let u526 : ℤ := (sv v51) - u490
  let u527 : ℤ := if u484 = 1 then u526 else u490
  let u528 : ℤ := if u525 = 1 then u527 else u202
  have f985 := L2.K12_atan_lo u440 u485 (sv v51) u484 u488 u489 u490 u491 u495 u498 u502 u503 u504 u505 u506 u507 u509 u511 u512 u513 (sv v186) u515 u516 u517 u518 u519 (sv v193) u521 u522 u523 u484 u524 u525 u526 u527 u202 u528 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f992 f1001 f1010 f1019 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v186 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v193 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  let u529 : ℤ := (sv v51) - u446
  let u530 : ℤ := if u486 = 1 then u529 else u446
  let u531 : ℤ := 0
  let u532 : ℤ := L2.cosI u531
  let u533 : ℤ := (sv v18) + u532
  let u534 : ℕ := if u533 < (sv v85) then 1 else 0
  let u535 : ℤ := if u534 = 1 then (sv v85) else u533
  have f1065 := L2.K3_cos_lo u531 u532 u533 (sv v85) u535 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u536 : ℤ := (sv v21) + u532
  let u537 : ℕ := if u536 < (sv v23) then 1 else 0
  let u538 : ℤ := if u537 = 1 then u536 else (sv v23)
  have f1074 := L2.K3_cos_hi u531 u532 u536 (sv v23) u538 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u539 : ℤ := L2.sinI u531
  let u540 : ℤ := (sv v21) + u539
  let u541 : ℕ := if u540 < (sv v23) then 1 else 0
  let u542 : ℤ := if u541 = 1 then u540 else (sv v23)
  have f1083 := L2.K3_sin_hi u531 u539 u540 (sv v23) u542 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u543 : ℤ := (sv v18) + u539
  have f1092 := L2.K3_sin_lo u531 u539 u543 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u544 : ℤ := if u486 = 1 then u535 else u538
  let u545 : ℤ := if u486 = 1 then u542 else u543
  let u546 : ℤ := u487 * u545
  let u547 : ℤ := u530 * u544
  let u548 : ℕ := if u547 < u546 then 1 else 0
  let u549 : ℕ := if u548 = 1 then 0 else 1
  let u550 : ℕ := if u546 < u547 then 1 else 0
  let u551 : ℕ := if u550 = 1 then 0 else 1
  let u552 : ℕ := if (sv v51) < u531 then 1 else 0
  let u553 : ℕ := if u552 = 1 then 0 else 1
  let u554 : ℕ := if (sv v186) < u531 then 1 else 0
  let u555 : ℕ := if u554 = 1 then 0 else 1
  let u556 : ℕ := if (sv v8) < u535 then 1 else 0
  let u557 : ℕ := if u549 = 1 ∧ u556 = 1 then 1 else 0
  let u558 : ℕ := if u555 = 1 ∧ u557 = 1 then 1 else 0
  let u559 : ℕ := if u553 = 1 ∨ u558 = 1 then 1 else 0
  let u560 : ℕ := if u531 < (sv v193) then 1 else 0
  let u561 : ℕ := if u560 = 1 then 0 else 1
  let u562 : ℕ := if u551 = 1 ∨ u561 = 1 then 1 else 0
  let u563 : ℕ := if u486 = 1 ∧ u559 = 1 then 1 else 0
  let u564 : ℕ := if u486 = 1 then 0 else 1
  let u565 : ℕ := if u562 = 1 ∧ u564 = 1 then 1 else 0
  let u566 : ℕ := if u563 = 1 ∨ u565 = 1 then 1 else 0
  let u567 : ℤ := (sv v51) - u531
  let u568 : ℤ := if u486 = 1 then u567 else u531
  let u569 : ℤ := if u566 = 1 then u568 else (sv v193)
  have f1059 := L2.K12_atan_hi u446 u487 (sv v51) u486 u529 u530 u531 u535 u538 u542 u543 u544 u545 u546 u547 u549 u551 u552 u553 (sv v186) u555 u556 u557 u558 u559 (sv v193) u561 u562 u563 u564 u565 u566 u567 u568 (sv v193) u569 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f1065 f1074 f1083 f1092 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v186 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v193 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v193 rfl
  let u570 : ℤ := if u483 = 1 then u202 else u528
  let u571 : ℤ := if u483 = 1 then (sv v193) else u569
  have f861 := L2.K19_iso_angle_pt True (sv v5) (sv v90) (sv v97) (sv v432) (sv v389) u440 u446 (sv v450) (sv v457) u479 u481 u485 u487 u483 u482 u528 u569 u202 (sv v193) u570 u571 f862 f865 f904 f941 f974 (L2.p_not_not (L2.p_unot _)) f985 f1059 rfl e_v193 rfl rfl
  have f1137 := L2.K5_ihalf (sv v4) (sv v4) (sv v388) (sv v572) e_v388 e_v572
  have f1141 := L2.K8_in_range True (sv v388) (sv v572) v390 (sv v10) v574 v575 (L2.p_clt (-1) e_v8 e_v390) e_v10 (L2.p_le e_v573 e_v574) e_v575 (L2.X1_top _ k_v575)
  let u576 : ℤ := L2.cosI (sv v572)
  let u577 : ℤ := (sv v18) + u576
  let u578 : ℕ := if u577 < (sv v85) then 1 else 0
  let u579 : ℤ := if u578 = 1 then (sv v85) else u577
  have f1151 := L2.K3_cos_lo (sv v572) u576 u577 (sv v85) u579 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u580 : ℕ := if (sv v88) < (sv v572) then 1 else 0
  let u581 : ℤ := if u580 = 1 then (sv v85) else u579
  have f1165 := L2.K3_cos_hi (sv v388) (sv t388.2) (sv v583) (sv v23) (sv v585) (L2.p_cos e_t388_2) (L2.p_addc (4) (L2.p_add_comm e_v583) e_v21) e_v23 (L2.p_min e_v584 (L2.p_sel e_v585))
  have f1140 := L2.K10_icos True (sv v388) (sv v572) u579 (sv v85) u580 u581 (sv v585) (sv v23) v586 (sv v587) f1141 f1151 e_v85 (L2.p_clt (843314855) e_v88 (L2.p_ult _ _)) rfl f1165 e_v23 (L2.p_ltc (1) e_v95 e_v586) (L2.p_sel e_v587)
  have f1180 := L2.K8_in_range True (sv v388) (sv v572) v390 (sv v10) v574 v575 (L2.p_clt (-1) e_v8 e_v390) e_v10 (L2.p_le e_v573 e_v574) e_v575 (L2.X1_top _ k_v575)
  have f1179 := L2.K9_isin True (sv v388) (sv v572) (sv t388.1) (sv t572.1) (sv v590) (sv v591) (sv v592) (sv v593) (sv v23) (sv v595) v403 v596 v597 (sv v598) f1180 (L2.p_sin e_t388_1) (L2.p_sin e_t572_1) (L2.p_min e_v589 (L2.p_sel e_v590)) (L2.p_addc (-4) (L2.p_add_comm e_v591) e_v18) (L2.p_max e_v589 (L2.p_sel e_v592)) (L2.p_addc (4) (L2.p_add_comm e_v593) e_v21) e_v23 (L2.p_min e_v594 (L2.p_sel e_v595)) (L2.p_ltc (421657430) e_v26 e_v403) (L2.p_clt (421657427) e_v28 e_v596) e_v597 (L2.p_sel e_v598)
  have f1216 := L2.K6_imul True (sv v90) (sv v97) (sv v591) (sv v598) (sv v51) v124 v125 v126 v127 v128 v129 v599 v600 v601 v602 v603 v604 v605 v606 v607 v608 (sv v609) v610 v611 (sv v612) v613 v614 (sv v615) v616 v617 (sv v618) (sv v620) (sv v622) e_v51 e_v124 e_v125 e_v126 e_v127 (L2.p_and_comm e_v128) e_v129 e_v599 e_v600 e_v601 e_v602 (L2.p_and_comm e_v603) e_v604 e_v605 e_v606 (L2.X1_top _ k_v606) e_v607 e_v608 (L2.p_sel e_v609) e_v610 e_v611 (L2.p_sel e_v612) e_v613 e_v614 (L2.p_sel e_v615) e_v616 e_v617 (L2.p_sel e_v618) (L2.p_mul (L2.p_mul_comm e_v619) e_v620) (L2.p_mulc (L2.p_mul_comm e_v621) e_v622)
  let u625 : ℕ := if u581 < (sv v51) then 1 else 0
  let u626 : ℤ := if u625 = 1 then (sv v620) else (sv v622)
  have f1249 := L2.K11_qdiv u581 (sv v587) (sv v620) (sv v622) v623 v624 (sv v51) u625 u626 v627 (sv v628) (L2.p_clt (0) e_v51 e_v623) e_v624 e_v51 (L2.p_ult _ _) rfl e_v627 (L2.p_sel e_v628)
  let u629 : ℤ := (sv v51) - u581
  let u630 : ℤ := if u625 = 1 then u629 else u581
  let u631 : ℤ := 0
  let u632 : ℕ := if u625 = 1 then 0 else 1
  let u633 : ℤ := L2.cosI u631
  let u634 : ℤ := (sv v18) + u633
  let u635 : ℕ := if u634 < (sv v85) then 1 else 0
  let u636 : ℤ := if u635 = 1 then (sv v85) else u634
  have f1267 := L2.K3_cos_lo u631 u633 u634 (sv v85) u636 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u637 : ℤ := (sv v21) + u633
  let u638 : ℕ := if u637 < (sv v23) then 1 else 0
  let u639 : ℤ := if u638 = 1 then u637 else (sv v23)
  have f1276 := L2.K3_cos_hi u631 u633 u637 (sv v23) u639 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u640 : ℤ := L2.sinI u631
  let u641 : ℤ := (sv v21) + u640
  let u642 : ℕ := if u641 < (sv v23) then 1 else 0
  let u643 : ℤ := if u642 = 1 then u641 else (sv v23)
  have f1285 := L2.K3_sin_hi u631 u640 u641 (sv v23) u643 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u644 : ℤ := (sv v18) + u640
  have f1294 := L2.K3_sin_lo u631 u640 u644 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u645 : ℤ := if u632 = 1 then u636 else u639
  let u646 : ℤ := if u632 = 1 then u643 else u644
  let u647 : ℤ := u626 * u646
  let u648 : ℤ := u630 * u645
  let u649 : ℕ := if u648 < u647 then 1 else 0
  let u650 : ℕ := if u649 = 1 then 0 else 1
  let u651 : ℕ := if u647 < u648 then 1 else 0
  let u652 : ℕ := if u651 = 1 then 0 else 1
  let u653 : ℕ := if (sv v51) < u631 then 1 else 0
  let u654 : ℕ := if u653 = 1 then 0 else 1
  let u655 : ℕ := if (sv v186) < u631 then 1 else 0
  let u656 : ℕ := if u655 = 1 then 0 else 1
  let u657 : ℕ := if (sv v8) < u636 then 1 else 0
  let u658 : ℕ := if u650 = 1 ∧ u657 = 1 then 1 else 0
  let u659 : ℕ := if u656 = 1 ∧ u658 = 1 then 1 else 0
  let u660 : ℕ := if u654 = 1 ∨ u659 = 1 then 1 else 0
  let u661 : ℕ := if u631 < (sv v193) then 1 else 0
  let u662 : ℕ := if u661 = 1 then 0 else 1
  let u663 : ℕ := if u652 = 1 ∨ u662 = 1 then 1 else 0
  let u664 : ℕ := if u632 = 1 ∧ u660 = 1 then 1 else 0
  let u665 : ℕ := if u625 = 1 ∧ u663 = 1 then 1 else 0
  let u666 : ℕ := if u664 = 1 ∨ u665 = 1 then 1 else 0
  let u667 : ℤ := (sv v51) - u631
  let u668 : ℤ := if u625 = 1 then u667 else u631
  let u669 : ℤ := if u666 = 1 then u668 else u202
  have f1260 := L2.K12_atan_lo u581 u626 (sv v51) u625 u629 u630 u631 u632 u636 u639 u643 u644 u645 u646 u647 u648 u650 u652 u653 u654 (sv v186) u656 u657 u658 u659 u660 (sv v193) u662 u663 u664 u625 u665 u666 u667 u668 u202 u669 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f1267 f1276 f1285 f1294 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v186 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v193 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  have f1340 := L2.K3_cos_lo (sv v672) (sv t672.2) (sv v674) (sv v85) (sv v676) (L2.p_cos e_t672_2) (L2.p_addc (-4) (L2.p_add_comm e_v674) e_v18) e_v85 (L2.p_max e_v675 (L2.p_sel e_v676))
  have f1349 := L2.K3_cos_hi (sv v672) (sv t672.2) (sv v677) (sv v23) (sv v679) (L2.p_cos e_t672_2) (L2.p_addc (4) (L2.p_add_comm e_v677) e_v21) e_v23 (L2.p_min e_v678 (L2.p_sel e_v679))
  have f1358 := L2.K3_sin_hi (sv v672) (sv t672.1) (sv v681) (sv v23) (sv v683) (L2.p_sin e_t672_1) (L2.p_addc (4) (L2.p_add_comm e_v681) e_v21) e_v23 (L2.p_min e_v682 (L2.p_sel e_v683))
  have f1367 := L2.K3_sin_lo (sv v672) (sv t672.1) (sv v684) (L2.p_sin e_t672_1) (L2.p_addc (-4) (L2.p_add_comm e_v684) e_v18)
  have f1334 := L2.K12_atan_hi (sv v587) (sv v628) (sv v51) v627 (sv v670) (sv v671) (sv v672) (sv v676) (sv v679) (sv v683) (sv v684) (sv v685) (sv v686) (sv v687) (sv v688) v690 v692 v693 v694 (sv v186) v696 v697 v698 v699 v700 (sv v193) v702 v703 v704 v705 v706 v707 (sv v708) (sv v709) (sv v193) (sv v710) e_v51 e_v627 e_v670 (L2.p_sel e_v671) (L2.p_hint e_v672) f1340 f1349 f1358 f1367 (L2.p_sel e_v685) (L2.p_sel e_v686) (L2.p_mul_comm e_v687) (L2.p_mul_comm e_v688) (L2.p_le e_v689 e_v690) (L2.p_le e_v691 e_v692) e_v693 e_v694 e_v186 (L2.p_le e_v695 e_v696) (L2.p_clt (-1) e_v8 e_v697) e_v698 (L2.p_and_comm e_v699) e_v700 e_v193 (L2.p_le e_v701 e_v702) (L2.p_or_comm e_v703) e_v704 e_v705 (L2.p_and_comm e_v706) e_v707 e_v708 (L2.p_sel e_v709) e_v193 (L2.p_sel e_v710)
  let u711 : ℤ := if v624 = 1 then u202 else u669
  have f1136 := L2.K19_iso_angle_pt True (sv v4) (sv v90) (sv v97) (sv v388) (sv v572) u581 (sv v587) (sv v591) (sv v598) (sv v620) (sv v622) u626 (sv v628) v624 v623 u669 (sv v710) u202 (sv v193) u711 (sv v712) f1137 f1140 f1179 f1216 f1249 (L2.p_not_not e_v624) f1260 f1334 rfl e_v193 rfl (L2.p_sel e_v712)
  have f821 := L2.K20_iso_angle True (sv v4) (sv v5) (sv v0) (sv v1) (sv v90) (sv v97) u570 u571 u483 u711 (sv v712) v624 f822 f861 f1136
  have f1414 := L2.K15_in_open (sv v0) (sv v1) v713 v715 v716 (L2.p_clt (0) e_v51 e_v713) (L2.p_ltc (843314856) e_v714 e_v715) e_v716
  have f1413 := L2.K15_a_open_plain (sv v0) (sv v1) v716 f1414
  have f1422 := L2.K15_a_open (sv v79) (sv v81) v717 v718 v719 (L2.p_clt (0) e_v51 e_v717) (L2.p_ltc (268435456) e_v23 e_v718) e_v719
  have f1430 := L2.K15_a_open (sv v428) (sv v430) v720 v721 v722 (L2.p_clt (0) e_v51 e_v720) (L2.p_ltc (268435456) e_v23 e_v721) e_v722
  have f1442 := L2.K8_in_range (True ∧ v724 = 1) (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_step True v724 v725 v13 v726 e_v725 (L2.p_or_comm e_v726) (L2.X1_top _ k_v726))
  have f1454 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v84) (sv v85) (sv v87) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v84) e_v18) e_v85 (L2.p_max e_v86 (L2.p_sel e_v87))
  have f1468 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v92) (sv v23) (sv v94) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v92) e_v21) e_v23 (L2.p_min e_v93 (L2.p_sel e_v94))
  have f1441 := L2.K10_icos (True ∧ v724 = 1) (sv v0) (sv v1) (sv v87) (sv v85) v89 (sv v90) (sv v94) (sv v23) v96 (sv v97) f1442 f1454 e_v85 (L2.p_clt (843314855) e_v88 e_v89) (L2.p_sel e_v90) f1468 e_v23 (L2.p_ltc (1) e_v95 e_v96) (L2.p_sel e_v97)
  have f1440 := L2.K16_a_cos_plain (True ∧ v724 = 1) (sv v0) (sv v1) (sv v90) (sv v97) f1441
  have f1482 := L2.K16_a_cos (True ∧ v724 = 1) (sv v428) (sv v430) (sv v23) (sv v728) (sv v729) (sv v730) (sv v85) (sv v732) (sv v734) (sv v735) (sv v736) e_v23 (L2.p_mulc e_v727 e_v728) e_v729 e_v730 e_v85 (L2.p_max e_v731 (L2.p_sel e_v732)) (L2.p_mul e_v733 e_v734) e_v735 e_v736
  have f1496 := L2.K16_a_cos (True ∧ v724 = 1) (sv v79) (sv v81) (sv v23) (sv v738) (sv v739) (sv v740) (sv v85) (sv v742) (sv v744) (sv v745) (sv v746) e_v23 (L2.p_mulc e_v737 e_v738) e_v739 e_v740 e_v85 (L2.p_max e_v741 (L2.p_sel e_v742)) (L2.p_mul e_v743 e_v744) e_v745 e_v746
  have f1510 := L2.K6_imul (True ∧ v724 = 1) (sv v90) (sv v97) (sv v742) (sv v746) (sv v51) v124 v125 v126 v127 v128 v129 v747 v748 v749 v750 v751 v752 v753 v754 v756 v757 (sv v758) v759 v760 (sv v761) v762 v763 (sv v764) v765 v766 (sv v767) (sv v769) (sv v771) e_v51 e_v124 e_v125 e_v126 e_v127 (L2.p_and_comm e_v128) e_v129 e_v747 e_v748 e_v749 e_v750 (L2.p_and_comm e_v751) e_v752 e_v753 e_v754 (L2.X1_step True v724 v725 v754 v755 e_v725 e_v755 (L2.X1_top _ k_v755)) e_v756 e_v757 (L2.p_sel e_v758) e_v759 e_v760 (L2.p_sel e_v761) e_v762 e_v763 (L2.p_sel e_v764) e_v765 e_v766 (L2.p_sel e_v767) (L2.p_mul (L2.p_mul_comm e_v768) e_v769) (L2.p_mulc (L2.p_mul_comm e_v770) e_v771)
  have f1545 := L2.K4_isub (sv v732) (sv v736) (sv v769) (sv v771) (sv v772) (sv v773) e_v772 e_v773
  have f1548 := L2.K6_imul (True ∧ v724 = 1) (sv v90) (sv v97) (sv v732) (sv v736) (sv v51) v124 v125 v126 v127 v128 v129 v774 v775 v776 v777 v778 v779 v780 v781 v783 v784 (sv v785) v786 v787 (sv v788) v789 v790 (sv v791) v792 v793 (sv v794) (sv v796) (sv v798) e_v51 e_v124 e_v125 e_v126 e_v127 (L2.p_and_comm e_v128) e_v129 e_v774 e_v775 e_v776 e_v777 (L2.p_and_comm e_v778) e_v779 e_v780 e_v781 (L2.X1_step True v724 v725 v781 v782 e_v725 e_v782 (L2.X1_top _ k_v782)) e_v783 e_v784 (L2.p_sel e_v785) e_v786 e_v787 (L2.p_sel e_v788) e_v789 e_v790 (L2.p_sel e_v791) e_v792 e_v793 (L2.p_sel e_v794) (L2.p_mul (L2.p_mul_comm e_v795) e_v796) (L2.p_mulc (L2.p_mul_comm e_v797) e_v798)
  have f1583 := L2.K4_isub (sv v742) (sv v746) (sv v796) (sv v798) (sv v799) (sv v800) e_v799 e_v800
  have f1612 := L2.K8_in_range (True ∧ v724 = 1) (sv v0) (sv v0) v9 (sv v10) v814 v815 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v813 e_v814) e_v815 (L2.X1_step True v724 v725 v815 v816 e_v725 e_v816 (L2.X1_top _ k_v816))
  let u817 : ℤ := (sv v18) + (sv t0.2)
  let u818 : ℕ := if u817 < (sv v85) then 1 else 0
  let u819 : ℤ := if u818 = 1 then (sv v85) else u817
  have f1624 := L2.K3_cos_lo (sv v0) (sv t0.2) u817 (sv v85) u819 (L2.p_cos e_t0_2) (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u820 : ℕ := if (sv v88) < (sv v0) then 1 else 0
  let u821 : ℤ := if u820 = 1 then (sv v85) else u819
  have f1638 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v92) (sv v23) (sv v94) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v92) e_v21) e_v23 (L2.p_min e_v93 (L2.p_sel e_v94))
  have f1611 := L2.K10_icos (True ∧ v724 = 1) (sv v0) (sv v0) u819 (sv v85) u820 u821 (sv v94) (sv v23) v96 (sv v97) f1612 f1624 e_v85 (L2.p_clt (843314855) e_v88 (L2.p_ult _ _)) rfl f1638 e_v23 (L2.p_ltc (1) e_v95 e_v96) (L2.p_sel e_v97)
  have f1610 := L2.K16_a_cos_plain (True ∧ v724 = 1) (sv v0) (sv v0) u821 (sv v97) f1611
  have f1652 := L2.K16_a_cos (True ∧ v724 = 1) (sv v805) (sv v806) (sv v23) (sv v823) (sv v824) (sv v825) (sv v85) (sv v827) (sv v829) (sv v830) (sv v831) e_v23 (L2.p_mulc e_v822 e_v823) e_v824 e_v825 e_v85 (L2.p_max e_v826 (L2.p_sel e_v827)) (L2.p_mul e_v828 e_v829) e_v830 e_v831
  have f1666 := L2.K16_a_cos (True ∧ v724 = 1) (sv v809) (sv v810) (sv v23) (sv v833) (sv v834) (sv v835) (sv v85) (sv v837) (sv v839) (sv v840) (sv v841) e_v23 (L2.p_mulc e_v832 e_v833) e_v834 e_v835 e_v85 (L2.p_max e_v836 (L2.p_sel e_v837)) (L2.p_mul e_v838 e_v839) e_v840 e_v841
  let u863 : ℕ := if v846 = 1 ∧ v853 = 1 then 1 else 0
  let u864 : ℕ := if v852 = 1 ∨ u863 = 1 then 1 else 0
  let u865 : ℤ := if u864 = 1 then (sv v827) else (sv v831)
  let u866 : ℕ := if v847 = 1 ∧ v852 = 1 then 1 else 0
  let u867 : ℕ := if v846 = 1 ∨ u866 = 1 then 1 else 0
  let u868 : ℤ := if u867 = 1 then (sv v837) else (sv v841)
  let u871 : ℤ := u865 * u868
  let u872 : ℤ := -((-u871) / 2 ^ 28)
  have f1680 := L2.K6_imul (True ∧ v724 = 1) (sv v827) (sv v831) (sv v837) (sv v841) (sv v51) v842 v843 v844 v845 v846 v847 v848 v849 v850 v851 v852 v853 v854 v855 v857 v858 (sv v859) v860 v861 (sv v862) u863 u864 u865 u866 u867 u868 (sv v870) u872 e_v51 e_v842 e_v843 e_v844 e_v845 (L2.p_and_comm e_v846) e_v847 e_v848 e_v849 e_v850 e_v851 (L2.p_and_comm e_v852) e_v853 e_v854 e_v855 (L2.X1_step True v724 v725 v855 v856 e_v725 e_v856 (L2.X1_top _ k_v856)) e_v857 e_v858 (L2.p_sel e_v859) e_v860 e_v861 (L2.p_sel e_v862) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul (L2.p_mul_comm e_v869) e_v870) (L2.p_mulc rfl rfl)
  let u873 : ℤ := u821 - u872
  have f1715 := L2.K4_isub u821 (sv v97) (sv v870) u872 u873 (sv v874) rfl e_v874
  have f1719 := L2.K17_s_end (sv v805) (sv v828) (sv v875) (sv v876) (sv v877) (sv v878) (sv v880) (sv v881) (sv v23) (sv v883) (sv v884) (sv v886) e_v828 e_v875 e_v876 (L2.p_sqrt e_v877) (L2.p_addc (1) (L2.p_add_comm e_v878) e_v95) (L2.p_mul (L2.p_mul_comm e_v879) e_v880) e_v881 e_v23 (L2.p_mulc (L2.p_mul_comm e_v882) e_v883) e_v884 (L2.p_min e_v885 (L2.p_sel e_v886))
  have f1737 := L2.K17_s_end (sv v806) (sv v822) (sv v875) (sv v887) (sv v888) (sv v889) (sv v891) (sv v892) (sv v23) (sv v894) (sv v895) (sv v897) e_v822 e_v875 e_v887 (L2.p_sqrt e_v888) (L2.p_addc (1) (L2.p_add_comm e_v889) e_v95) (L2.p_mul (L2.p_mul_comm e_v890) e_v891) e_v892 e_v23 (L2.p_mulc (L2.p_mul_comm e_v893) e_v894) e_v895 (L2.p_min e_v896 (L2.p_sel e_v897))
  have f1718 := L2.K18_a_sin (True ∧ v724 = 1) (sv v805) (sv v806) (sv v881) (sv v886) (sv v892) (sv v897) (sv v899) (sv v901) (sv v902) (sv v828) (sv v822) v904 v906 v907 (sv v23) (sv v908) f1719 f1737 (L2.p_min e_v898 (L2.p_sel e_v899)) (L2.p_max e_v900 (L2.p_sel e_v901)) e_v902 e_v828 e_v822 (L2.p_le e_v903 e_v904) (L2.p_le e_v905 e_v906) e_v907 e_v23 (L2.p_sel e_v908)
  have f1774 := L2.K17_s_end (sv v809) (sv v838) (sv v875) (sv v909) (sv v910) (sv v911) (sv v913) (sv v914) (sv v23) (sv v916) (sv v917) (sv v919) e_v838 e_v875 e_v909 (L2.p_sqrt e_v910) (L2.p_addc (1) (L2.p_add_comm e_v911) e_v95) (L2.p_mul (L2.p_mul_comm e_v912) e_v913) e_v914 e_v23 (L2.p_mulc (L2.p_mul_comm e_v915) e_v916) e_v917 (L2.p_min e_v918 (L2.p_sel e_v919))
  have f1792 := L2.K17_s_end (sv v810) (sv v832) (sv v875) (sv v920) (sv v921) (sv v922) (sv v924) (sv v925) (sv v23) (sv v927) (sv v928) (sv v930) e_v832 e_v875 e_v920 (L2.p_sqrt e_v921) (L2.p_addc (1) (L2.p_add_comm e_v922) e_v95) (L2.p_mul (L2.p_mul_comm e_v923) e_v924) e_v925 e_v23 (L2.p_mulc (L2.p_mul_comm e_v926) e_v927) e_v928 (L2.p_min e_v929 (L2.p_sel e_v930))
  have f1773 := L2.K18_a_sin (True ∧ v724 = 1) (sv v809) (sv v810) (sv v914) (sv v919) (sv v925) (sv v930) (sv v932) (sv v934) (sv v902) (sv v838) (sv v832) v936 v938 v939 (sv v23) (sv v940) f1774 f1792 (L2.p_min e_v931 (L2.p_sel e_v932)) (L2.p_max e_v933 (L2.p_sel e_v934)) e_v902 e_v838 e_v832 (L2.p_le e_v935 e_v936) (L2.p_le e_v937 e_v938) e_v939 e_v23 (L2.p_sel e_v940)
  have f1828 := L2.K6_imul (True ∧ v724 = 1) (sv v899) (sv v908) (sv v932) (sv v940) (sv v51) v941 v942 v943 v944 v945 v946 v947 v948 v949 v950 v951 v952 v953 v954 v956 v957 (sv v958) v959 v960 (sv v961) v962 v963 (sv v964) v965 v966 (sv v967) (sv v969) (sv v971) e_v51 e_v941 e_v942 e_v943 e_v944 (L2.p_and_comm e_v945) e_v946 e_v947 e_v948 e_v949 e_v950 (L2.p_and_comm e_v951) e_v952 e_v953 e_v954 (L2.X1_step True v724 v725 v954 v955 e_v725 e_v955 (L2.X1_top _ k_v955)) e_v956 e_v957 (L2.p_sel e_v958) e_v959 e_v960 (L2.p_sel e_v961) e_v962 e_v963 (L2.p_sel e_v964) e_v965 e_v966 (L2.p_sel e_v967) (L2.p_mul (L2.p_mul_comm e_v968) e_v969) (L2.p_mulc (L2.p_mul_comm e_v970) e_v971)
  let u973 : ℕ := if v972 = 1 then 0 else 1
  let u974 : ℕ := if u873 < (sv v51) then 1 else 0
  let u975 : ℤ := if u974 = 1 then (sv v969) else (sv v971)
  have f1863 := L2.K11_qdiv u873 (sv v874) (sv v969) (sv v971) v972 u973 (sv v51) u974 u975 v976 (sv v977) (L2.p_clt (0) e_v51 e_v972) (L2.p_unot _) e_v51 (L2.p_ult _ _) rfl e_v976 (L2.p_sel e_v977)
  have f1609 := L2.K23_hn false true true (True ∧ v724 = 1) (sv v0) (sv v0) (sv v805) (sv v806) (sv v809) (sv v810) u821 (sv v97) (sv v827) (sv v831) (sv v837) (sv v841) (sv v870) u872 u873 (sv v874) (sv v899) (sv v908) (sv v932) (sv v940) (sv v969) (sv v971) u975 (sv v977) u973 f1610 f1652 f1666 f1680 f1715 f1718 f1773 f1828 f1863
  let u981 : ℕ := if (sv v874) < (sv v977) then 1 else 0
  let u982 : ℕ := if u981 = 1 then 0 else 1
  let u983 : ℕ := if u973 = 1 ∨ u982 = 1 then 1 else 0
  let u984 : ℤ := if u983 = 1 then (sv v23) else (sv v874)
  let u985 : ℤ := if u983 = 1 then (sv v23) else (sv v977)
  have f1888 := L2.K8_in_range (True ∧ v724 = 1) (sv v1) (sv v1) v986 (sv v10) v12 v987 (L2.p_clt (-1) e_v8 e_v986) e_v10 (L2.p_le e_v11 e_v12) (L2.p_and_comm e_v987) (L2.X1_step True v724 v725 v987 v988 e_v725 e_v988 (L2.X1_top _ k_v988))
  have f1900 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v84) (sv v85) (sv v87) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v84) e_v18) e_v85 (L2.p_max e_v86 (L2.p_sel e_v87))
  let u989 : ℤ := (sv v21) + (sv t1.2)
  let u990 : ℕ := if u989 < (sv v23) then 1 else 0
  let u991 : ℤ := if u990 = 1 then u989 else (sv v23)
  have f1914 := L2.K3_cos_hi (sv v1) (sv t1.2) u989 (sv v23) u991 (L2.p_cos e_t1_2) (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u992 : ℕ := if (sv v1) < (sv v95) then 1 else 0
  let u993 : ℤ := if u992 = 1 then (sv v23) else u991
  have f1887 := L2.K10_icos (True ∧ v724 = 1) (sv v1) (sv v1) (sv v87) (sv v85) v89 (sv v90) u991 (sv v23) u992 u993 f1888 f1900 e_v85 (L2.p_clt (843314855) e_v88 e_v89) (L2.p_sel e_v90) f1914 e_v23 (L2.p_ltc (1) e_v95 (L2.p_ult _ _)) rfl
  have f1886 := L2.K16_a_cos_plain (True ∧ v724 = 1) (sv v1) (sv v1) (sv v90) u993 f1887
  have f1928 := L2.K16_a_cos (True ∧ v724 = 1) (sv v807) (sv v808) (sv v23) (sv v995) (sv v996) (sv v997) (sv v85) (sv v999) (sv v1001) (sv v1002) (sv v1003) e_v23 (L2.p_mulc e_v994 e_v995) e_v996 e_v997 e_v85 (L2.p_max e_v998 (L2.p_sel e_v999)) (L2.p_mul e_v1000 e_v1001) e_v1002 e_v1003
  have f1942 := L2.K16_a_cos (True ∧ v724 = 1) (sv v811) (sv v812) (sv v23) (sv v1005) (sv v1006) (sv v1007) (sv v85) (sv v1009) (sv v1011) (sv v1012) (sv v1013) e_v23 (L2.p_mulc e_v1004 e_v1005) e_v1006 e_v1007 e_v85 (L2.p_max e_v1008 (L2.p_sel e_v1009)) (L2.p_mul e_v1010 e_v1011) e_v1012 e_v1013
  let u1015 : ℕ := if v1014 = 1 then 0 else 1
  let u1021 : ℕ := if v1020 = 1 then 0 else 1
  let u1029 : ℕ := if u1015 = 1 ∧ v1025 = 1 then 1 else 0
  let u1030 : ℕ := if v1024 = 1 ∨ u1029 = 1 then 1 else 0
  let u1031 : ℤ := if u1030 = 1 then (sv v1003) else (sv v999)
  let u1032 : ℕ := if v1019 = 1 ∧ u1021 = 1 then 1 else 0
  let u1033 : ℕ := if v1018 = 1 ∨ u1032 = 1 then 1 else 0
  let u1034 : ℤ := if u1033 = 1 then (sv v1013) else (sv v1009)
  let u1041 : ℤ := u1031 * u1034
  let u1042 : ℤ := u1041 / 2 ^ 28
  have f1956 := L2.K6_imul (True ∧ v724 = 1) (sv v999) (sv v1003) (sv v1009) (sv v1013) (sv v51) v1014 u1015 v1016 v1017 v1018 v1019 v1020 u1021 v1022 v1023 v1024 v1025 v1026 v1027 u1029 u1030 u1031 u1032 u1033 u1034 v1035 v1036 (sv v1037) v1038 v1039 (sv v1040) u1042 (sv v1044) e_v51 e_v1014 (L2.p_unot _) e_v1016 e_v1017 (L2.p_and_comm e_v1018) e_v1019 e_v1020 (L2.p_unot _) e_v1022 e_v1023 (L2.p_and_comm e_v1024) e_v1025 e_v1026 e_v1027 (L2.X1_step True v724 v725 v1027 v1028 e_v725 e_v1028 (L2.X1_top _ k_v1028)) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl e_v1035 e_v1036 (L2.p_sel e_v1037) e_v1038 e_v1039 (L2.p_sel e_v1040) (L2.p_mul rfl rfl) (L2.p_mulc (L2.p_mul_comm e_v1043) e_v1044)
  let u1046 : ℤ := u993 - u1042
  have f1991 := L2.K4_isub (sv v90) u993 u1042 (sv v1044) (sv v1045) u1046 e_v1045 rfl
  have f1995 := L2.K17_s_end (sv v807) (sv v1000) (sv v875) (sv v1047) (sv v1048) (sv v1049) (sv v1051) (sv v1052) (sv v23) (sv v1054) (sv v1055) (sv v1057) e_v1000 e_v875 e_v1047 (L2.p_sqrt e_v1048) (L2.p_addc (1) (L2.p_add_comm e_v1049) e_v95) (L2.p_mul (L2.p_mul_comm e_v1050) e_v1051) e_v1052 e_v23 (L2.p_mulc (L2.p_mul_comm e_v1053) e_v1054) e_v1055 (L2.p_min e_v1056 (L2.p_sel e_v1057))
  have f2013 := L2.K17_s_end (sv v808) (sv v994) (sv v875) (sv v1058) (sv v1059) (sv v1060) (sv v1062) (sv v1063) (sv v23) (sv v1065) (sv v1066) (sv v1068) e_v994 e_v875 e_v1058 (L2.p_sqrt e_v1059) (L2.p_addc (1) (L2.p_add_comm e_v1060) e_v95) (L2.p_mul (L2.p_mul_comm e_v1061) e_v1062) e_v1063 e_v23 (L2.p_mulc (L2.p_mul_comm e_v1064) e_v1065) e_v1066 (L2.p_min e_v1067 (L2.p_sel e_v1068))
  have f1994 := L2.K18_a_sin (True ∧ v724 = 1) (sv v807) (sv v808) (sv v1052) (sv v1057) (sv v1063) (sv v1068) (sv v1070) (sv v1072) (sv v902) (sv v1000) (sv v994) v1074 v1076 v1077 (sv v23) (sv v1078) f1995 f2013 (L2.p_min e_v1069 (L2.p_sel e_v1070)) (L2.p_max e_v1071 (L2.p_sel e_v1072)) e_v902 e_v1000 e_v994 (L2.p_le e_v1073 e_v1074) (L2.p_le e_v1075 e_v1076) e_v1077 e_v23 (L2.p_sel e_v1078)
  have f2050 := L2.K17_s_end (sv v811) (sv v1010) (sv v875) (sv v1079) (sv v1080) (sv v1081) (sv v1083) (sv v1084) (sv v23) (sv v1086) (sv v1087) (sv v1089) e_v1010 e_v875 e_v1079 (L2.p_sqrt e_v1080) (L2.p_addc (1) (L2.p_add_comm e_v1081) e_v95) (L2.p_mul (L2.p_mul_comm e_v1082) e_v1083) e_v1084 e_v23 (L2.p_mulc (L2.p_mul_comm e_v1085) e_v1086) e_v1087 (L2.p_min e_v1088 (L2.p_sel e_v1089))
  have f2068 := L2.K17_s_end (sv v812) (sv v1004) (sv v875) (sv v1090) (sv v1091) (sv v1092) (sv v1094) (sv v1095) (sv v23) (sv v1097) (sv v1098) (sv v1100) e_v1004 e_v875 e_v1090 (L2.p_sqrt e_v1091) (L2.p_addc (1) (L2.p_add_comm e_v1092) e_v95) (L2.p_mul (L2.p_mul_comm e_v1093) e_v1094) e_v1095 e_v23 (L2.p_mulc (L2.p_mul_comm e_v1096) e_v1097) e_v1098 (L2.p_min e_v1099 (L2.p_sel e_v1100))
  have f2049 := L2.K18_a_sin (True ∧ v724 = 1) (sv v811) (sv v812) (sv v1084) (sv v1089) (sv v1095) (sv v1100) (sv v1102) (sv v1104) (sv v902) (sv v1010) (sv v1004) v1106 v1108 v1109 (sv v23) (sv v1110) f2050 f2068 (L2.p_min e_v1101 (L2.p_sel e_v1102)) (L2.p_max e_v1103 (L2.p_sel e_v1104)) e_v902 e_v1010 e_v1004 (L2.p_le e_v1105 e_v1106) (L2.p_le e_v1107 e_v1108) e_v1109 e_v23 (L2.p_sel e_v1110)
  have f2104 := L2.K6_imul (True ∧ v724 = 1) (sv v1070) (sv v1078) (sv v1102) (sv v1110) (sv v51) v1111 v1112 v1113 v1114 v1115 v1116 v1117 v1118 v1119 v1120 v1121 v1122 v1123 v1124 v1126 v1127 (sv v1128) v1129 v1130 (sv v1131) v1132 v1133 (sv v1134) v1135 v1136 (sv v1137) (sv v1139) (sv v1141) e_v51 e_v1111 e_v1112 e_v1113 e_v1114 (L2.p_and_comm e_v1115) e_v1116 e_v1117 e_v1118 e_v1119 e_v1120 (L2.p_and_comm e_v1121) e_v1122 e_v1123 e_v1124 (L2.X1_step True v724 v725 v1124 v1125 e_v725 e_v1125 (L2.X1_top _ k_v1125)) e_v1126 e_v1127 (L2.p_sel e_v1128) e_v1129 e_v1130 (L2.p_sel e_v1131) e_v1132 e_v1133 (L2.p_sel e_v1134) e_v1135 e_v1136 (L2.p_sel e_v1137) (L2.p_mul (L2.p_mul_comm e_v1138) e_v1139) (L2.p_mulc (L2.p_mul_comm e_v1140) e_v1141)
  let u1146 : ℕ := if u1046 < (sv v51) then 1 else 0
  let u1147 : ℤ := if u1146 = 1 then (sv v1141) else (sv v1139)
  have f2139 := L2.K11_qdiv (sv v1045) u1046 (sv v1139) (sv v1141) v1142 v1143 (sv v51) v1144 (sv v1145) u1146 u1147 (L2.p_clt (0) e_v51 e_v1142) e_v1143 e_v51 e_v1144 (L2.p_sel e_v1145) (L2.p_ult _ _) rfl
  have f1885 := L2.K23_hn false true true (True ∧ v724 = 1) (sv v1) (sv v1) (sv v807) (sv v808) (sv v811) (sv v812) (sv v90) u993 (sv v999) (sv v1003) (sv v1009) (sv v1013) u1042 (sv v1044) (sv v1045) u1046 (sv v1070) (sv v1078) (sv v1102) (sv v1110) (sv v1139) (sv v1141) (sv v1145) u1147 v1143 f1886 f1928 f1942 f1956 f1991 f1994 f2049 f2104 f2139
  let u1157 : ℕ := if v1156 = 1 then 0 else 1
  let u1158 : ℤ := 0
  let u1159 : ℕ := if (sv v51) < u1158 then 1 else 0
  let u1160 : ℕ := if u1159 = 1 then 0 else 1
  let u1161 : ℤ := L2.cosI u1158
  let u1162 : ℤ := (sv v18) + u1161
  let u1163 : ℕ := if u1162 < (sv v85) then 1 else 0
  let u1164 : ℤ := if u1163 = 1 then (sv v85) else u1162
  have f2168 := L2.K3_cos_lo u1158 u1161 u1162 (sv v85) u1164 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v85 (L2.p_max (L2.p_ult _ _) rfl)
  let u1165 : ℤ := u984 * 2 ^ 28
  let u1166 : ℤ := u985 * u1164
  let u1167 : ℕ := if u1166 < u1165 then 1 else 0
  let u1168 : ℕ := if u1167 = 1 then 0 else 1
  let u1169 : ℕ := if (sv v714) < u1158 then 1 else 0
  let u1170 : ℕ := if u1169 = 1 then 0 else 1
  let u1171 : ℕ := if u1168 = 1 ∧ u1170 = 1 then 1 else 0
  let u1172 : ℕ := if u1160 = 1 ∨ u1171 = 1 then 1 else 0
  let u1173 : ℤ := if u1172 = 1 then u1158 else (sv v51)
  have f2163 := L2.K13_acos_lo u984 u985 u1158 (sv v51) u1159 u1160 u1164 u1165 u1166 u1168 (sv v714) u1170 u1171 u1172 u1173 (le_refl (0 : ℤ)) e_v51 (L2.p_ult _ _) (L2.p_unot _) f2168 rfl (L2.p_mul_comm rfl) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) e_v714 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl
  have f2195 := L2.K3_cos_hi (sv v1174) (sv t1174.2) (sv v1178) (sv v23) (sv v1180) (L2.p_cos e_t1174_2) (L2.p_addc (4) (L2.p_add_comm e_v1178) e_v21) e_v23 (L2.p_min e_v1179 (L2.p_sel e_v1180))
  have f2189 := L2.K13_acos_hi (sv v1154) (sv v1155) (sv v1174) (sv v10) v1176 (sv v1180) (sv v1181) (sv v1182) v1184 v1185 (sv v1186) (L2.p_hint e_v1174) e_v10 (L2.p_le e_v1175 e_v1176) f2195 e_v1181 e_v1182 (L2.p_le e_v1183 e_v1184) e_v1185 (L2.p_sel e_v1186)
  let u1187 : ℤ := if v724 = 1 then u1173 else (sv v51)
  let u1190 : ℤ := if v980 = 1 then (sv v714) else (sv v51)
  let u1191 : ℤ := if v980 = 1 then (sv v10) else (sv v51)
  have f1606 := L2.K24_tri_tail_x false true true True (sv v0) (sv v1) v724 (sv v805) (sv v806) (sv v809) (sv v810) (sv v807) (sv v808) (sv v811) (sv v812) (sv v23) (sv v85) u873 u975 (sv v874) (sv v977) u973 v972 (sv v978) v979 v980 u982 u983 u984 u985 (sv v1045) (sv v1145) u1046 u1147 v1143 v1142 v1148 v1149 (sv v1150) v1152 v1153 (sv v1154) (sv v1155) v1156 u1157 u1173 (sv v1186) (sv v51) (sv v10) (sv v714) u1187 (sv v1188) v1189 u1190 u1191 e_v23 e_v85 f1609 (L2.p_not_not (L2.p_unot _)) (L2.p_neg e_v51 e_v978) e_v979 e_v980 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_uor _ _) rfl rfl f1885 (L2.p_not_not e_v1143) e_v1148 e_v1149 (L2.p_neg e_v51 e_v1150) (L2.p_le e_v1151 e_v1152) e_v1153 (L2.p_sel e_v1154) (L2.p_sel e_v1155) e_v1156 (L2.p_unot _) f2163 f2189 e_v51 e_v10 e_v714 rfl (L2.p_sel e_v1188) e_v1189 rfl rfl
  have f1412 := L2.K21_tri_angle_st false true true True (sv v0) (sv v1) (sv v79) (sv v81) (sv v428) (sv v430) v716 v719 v722 v723 v724 (sv v90) (sv v97) (sv v732) (sv v736) (sv v742) (sv v746) (sv v769) (sv v771) (sv v772) (sv v773) (sv v796) (sv v798) (sv v799) (sv v800) v801 v802 v803 v804 (sv v805) (sv v806) (sv v807) (sv v808) (sv v809) (sv v810) (sv v811) (sv v812) u1187 (sv v1188) v1189 u1190 u1191 f1413 f1422 f1430 e_v723 (L2.p_and_comm e_v724) f1440 f1482 f1496 f1510 f1545 f1548 f1583 (L2.p_clt (0) e_v51 e_v801) (L2.p_ltc (0) e_v51 e_v802) (L2.p_clt (0) e_v51 e_v803) (L2.p_ltc (0) e_v51 e_v804) (L2.p_sel e_v805) (L2.p_sel e_v806) (L2.p_sel e_v807) (L2.p_sel e_v808) (L2.p_sel e_v809) (L2.p_sel e_v810) (L2.p_sel e_v811) (L2.p_sel e_v812) f1606
  have f1411 := L2.K25_tri_angle false true true True (sv v0) (sv v1) (sv v79) (sv v81) (sv v428) (sv v430) u1187 (sv v1188) v1189 u1190 u1191 v1192 f1412 e_v1192 (L2.X1_top _ k_v1192)
  let u1193 : ℤ := u245 + u1187
  have f2221 := L2.K4_iadd u245 (sv v387) u1187 (sv v1188) u1193 (sv v1194) rfl e_v1194
  let u1195 : ℤ := u570 + u1193
  have f2224 := L2.K4_iadd u1193 (sv v1194) u570 (sv v712) u1195 (sv v1196) (L2.p_add_comm rfl) (L2.p_add_comm e_v1196)
  let u1197 : ℕ := if u1195 < (sv v6) then 1 else 0
  let u1198 : ℕ := if u1197 = 1 then 0 else 1
  exact L2.K30_N0 true F0 F1 F2 F3 hD (sv v0) (sv v1) (sv v2) (sv v3) (sv v4) (sv v5) (sv v6) (1 : ℕ) (sv v79) (sv v81) u245 (sv v387) (sv v428) (sv v430) u570 (sv v712) u1187 (sv v1188) u1193 (sv v1194) u1195 (sv v1196) u1198 v1200 v1200 e_v0 e_v1 e_v2 e_v3 e_v4 e_v5 e_v6 (of_decide_eq_true rfl) f1 f116 f706 f821 f1411 f2221 f2224 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le e_v1199 e_v1200) (L2.p_sel_t _ _) (L2.X1_top _ k_v1200)

end D3Prog
