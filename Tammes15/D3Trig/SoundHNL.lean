import Tammes15.D3Trig.Prog.HNL
import Tammes15.D3Prog.L2.Kinds
import Tammes15.D3Prog.L2.PLib
import Tammes15.D3Trig.HexKinds

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem progHNL_l2 (F0 F1 F2 F3 H0 H1 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (h : Tammes15.D3Trig.progHNL 1 F0 F1 F2 F3 H0 H1 = 1) (hD : InDomH F0 F1 F2 F3) : LaneClaimH false F0 F1 F2 F3 := by
  unfold Tammes15.D3Trig.progHNL at h
  extract_lets -merge OFFr H61r v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11 v12 v13 v15 v19 v20 v21 v22 v23 t0 t1 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 t42 t43 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v94 v95 v96 v97 v98 v99 v100 v102 v103 v104 v105 v106 v107 v108 v109 v110 v112 v113 v114 v115 v116 t108 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 v160 v161 v162 v163 v164 v165 v166 v167 v170 v171 v172 v173 t172 v175 v176 v177 v178 v179 v180 v182 v183 v184 v185 v186 v187 v188 v189 v190 v191 v192 v193 v194 v195 v196 v197 v198 v199 v200 v201 v202 v203 v204 v205 v206 v207 v208 v209 v210 v211 v212 v213 v255 v257 v258 v259 v260 t257 v274 v275 v276 v277 v278 v279 v280 v281 v282 v283 v284 v286 v289 v290 v291 v398 v399 v400 v401 v402 v403 t398 t399 v406 v407 v408 v409 v410 v411 v412 v413 v414 v415 v416 v417 v418 v419 v420 v421 v422 v423 v424 v425 v426 v427 v428 v429 v430 v431 v432 v433 v434 v435 v436 v437 v438 v439 v440 v441 v442 v443 v444 v446 v447 v448 v449 v450 t442 v458 v459 v460 v461 v462 v463 v464 v465 v466 v467 v468 v469 v470 v471 v472 v473 v474 v475 v476 v477 v478 v479 v480 v481 v482 v483 v484 v485 v486 v487 v488 v489 v490 v491 v492 v493 v494 v495 v498 v499 v500 v501 t500 v503 v504 v505 v506 v507 v508 v510 v511 v512 v513 v514 v515 v516 v517 v518 v519 v520 v521 v522 v523 v524 v525 v526 v527 v528 v529 v530 v531 v532 v533 v534 v535 v536 v537 v538 v580 v582 v583 v584 v585 t582 v599 v600 v601 v602 v603 v604 v605 v606 v607 v608 v609 v611 v614 v615 v616 v723 v724 v725 v726 v727 v728 v729 t723 t725 v732 v733 v734 v735 v736 v737 v738 v739 v740 v741 v742 v743 v744 v745 v746 v747 v748 v749 v750 v751 v752 v753 v754 v755 v756 v757 v758 v759 v760 v761 v762 v763 v764 v765 v766 v767 v768 v769 v770 v771 v772 v773 v774 v775 v776 v777 v778 v779 v780 v781 v782 v783 v784 v785 v786 v787 v788 v789 v790 v791 v792 v793 v794 v795 v796 v797 v798 v799 v800 v801 v802 v803 v804 v805 v806 v807 v808 v809 v810 v811 v812 v813 v814 v815 v816 v817 v818 v819 v820 v821 v822 v823 v824 v825 v826 v827 v828 v829 v830 v831 v832 v833 v834 v835 v836 v837 v838 v839 v840 v841 v842 v843 v844 v845 v846 v847 v848 v849 v850 v851 v852 v853 v854 v855 v856 v857 v858 v859 v860 v861 v862 v863 v864 v865 v866 v867 v868 v869 v870 v871 v872 v873 v874 v875 v876 v877 v878 v879 v880 v881 v887 v888 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 v918 v919 v920 v921 v922 v923 v924 v925 v926 v927 v934 v935 v939 v940 v941 v942 v943 v944 v945 v946 v947 v948 v949 v950 v951 v952 v953 v954 v955 v956 v957 v958 v959 v960 v961 v962 v963 v964 v965 v966 v967 v968 v969 v970 v971 v972 v973 v974 v975 v976 v977 v978 v979 v980 v981 v982 v983 v984 v985 v986 v987 v988 v989 v990 v991 v992 v993 v994 v995 v996 v997 v998 v999 v1000 v1001 v1002 v1003 v1004 v1005 v1006 v1007 v1008 v1009 v1010 v1011 v1012 v1013 v1014 v1015 v1016 v1017 v1018 v1019 v1020 v1021 v1022 v1023 v1024 v1025 v1026 v1027 v1028 v1029 v1030 v1031 v1032 v1033 v1034 v1035 v1036 v1037 v1038 v1041 v1042 v1043 v1044 v1045 v1046 v1047 v1048 v1049 v1050 v1054 v1055 v1056 v1057 v1058 v1059 v1060 v1061 v1062 v1063 v1064 v1065 v1066 v1067 v1068 v1069 v1070 v1071 v1072 v1073 v1074 v1076 v1077 v1078 v1079 v1080 v1082 v1083 v1084 v1085 v1086 v1087 v1088 v1095 v1096 v1097 v1098 v1099 v1100 v1103 v1104 v1105 v1107 v1108 v1109 v1110 v1111 v1112 v1113 v1114 v1115 v1116 v1117 v1118 v1119 v1120 v1121 v1122 v1123 v1124 v1125 v1126 v1127 v1128 v1129 v1130 v1131 v1132 v1133 v1134 v1135 v1136 v1137 v1138 v1139 v1140 v1141 v1142 v1143 v1144 v1145 v1146 v1147 v1148 v1149 v1150 v1151 v1152 v1153 v1154 v1155 v1156 v1157 v1158 v1159 v1160 v1161 v1162 v1163 v1164 v1165 v1166 v1167 v1168 v1169 v1170 v1171 v1172 v1173 v1174 v1175 v1176 v1177 v1178 v1179 v1180 v1181 v1182 v1183 v1184 v1185 v1186 v1187 v1188 v1189 v1190 v1191 v1192 v1193 v1194 v1195 v1196 v1197 v1198 v1199 v1200 v1201 v1202 v1204 v1205 v1208 v1209 v1216 v1218 v1219 v1220 t1218 v1222 v1223 v1224 v1225 v1226 v1227 v1228 v1229 v1230 v1231 v1232 v1233 v1247 v1249 v1250 v1252 v1254 v1256 v1258 v1259 v1262 v1263 v1264 v1265 v1266 v1267 v1268 v1269 v1270 v1271 v1272 v1273 v1274 v1275 v1276 v1277 v1278 v1279 v1280 v1281 v1282 v1283 v1284 v1285 v1286 v1287 v1288 v1289 v1290 v1291 v1292 v1293 at h
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
  have h_v7 : R 1 0 4611686018427387904 4611686087146864624 v7 v7 := (r1_ix hb_F3 32 (of_decide_eq_true rfl))
  have e_v7 : sv v7 = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ) := e_ix hb_F3 32 (of_decide_eq_true rfl)
  have h_v9 : R 1 0 4611686019270702761 4611686019270702761 v9 v9 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have e_v9 : sv v9 = (843314857) := e_c 4611686019270702761 (843314857) (of_decide_eq_true rfl)
  have h_v10 : R 1 0 4611686019270702761 4611686087990179481 v10 v10 := (r_sub hl (r_add hl h_v7 h_v9 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v10 : sv v10 = sv v7 + sv v9 := e_add h_v7 h_v9 (of_decide_eq_true rfl)
  have h_v11 : R 1 0 4611686020114017616 4611686020114017616 v11 v11 := (r_c hl 4611686020114017616 (of_decide_eq_true rfl))
  clear e_OFFr e_H61r
  have e_v11 : sv v11 = (1686629712) := e_c 4611686020114017616 (1686629712) (of_decide_eq_true rfl)
  have h_v12 : R 1 0 0 1 v12 v12 := (r_plt hl h_v11 h_v10 (of_decide_eq_true rfl))
  have e_v12 : (v12 = 1 ↔ sv v11 < sv v10) := e_plt h_v11 h_v10 (of_decide_eq_true rfl)
  have h_v13 : R 1 0 0 1 v13 v13 := (r_sub hl (r_O hl) h_v12 (of_decide_eq_true rfl))
  have e_v13 : (v13 = 1 ↔ ¬v12 = 1) := e_not h_v12 (of_decide_eq_true rfl)
  have h_v15 : R 1 0 4611686019270702760 4611686019270702760 v15 v15 := (r_c hl 4611686019270702760 (of_decide_eq_true rfl))
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
  clear h_v10 h_v11 h_v12 h_v20 h_v21 h_v22
  have h_v26 : R 1 0 0 1 v26 v26 := (r_plt hl h_t0_1 h_t1_1 (of_decide_eq_true rfl))
  have e_v26 : (v26 = 1 ↔ sv t0.1 < sv t1.1) := e_plt h_t0_1 h_t1_1 (of_decide_eq_true rfl)
  have h_v27 : R 1 0 4611686018427387904 4611686018695823363 v27 v27 := (r_psel hl h_v26 h_t0_1 h_t1_1 (of_decide_eq_true rfl))
  have e_v27 : v27 = if v26 = 1 then t0.1 else t1.1 := e_psel h_v26 h_t0_1 h_t1_1 (of_decide_eq_true rfl)
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
  clear h_t0_1 h_t1_1 h_v26 h_v27 h_v30 h_v32 h_v34
  have e_v38 : sv v38 = (421657427) := e_c 4611686018849045331 (421657427) (of_decide_eq_true rfl)
  have h_v39 : R 1 0 0 1 v39 v39 := (r_plt hl h_v38 h_v1 (of_decide_eq_true rfl))
  have e_v39 : (v39 = 1 ↔ sv v38 < sv v1) := e_plt h_v38 h_v1 (of_decide_eq_true rfl)
  have h_v40 : R 1 0 0 1 v40 v40 := (r_land hl h_v37 h_v39 (of_decide_eq_true rfl))
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
  clear h_v35 h_v37 h_v39 h_v40 h_v45 h_t42_2 e_t42_2
  have e_t43_1 : sv t43.1 = (sc28pS (scArg v43)).1 := e_sc1 h_v43 (of_decide_eq_true rfl)
  have e_t43_2 : sv t43.2 = (sc28pS (scArg v43)).2 := e_sc2 h_v43 (of_decide_eq_true rfl)
  have h_v50 : R 1 0 0 1 v50 v50 := (r_plt hl h_t42_1 h_t43_1 (of_decide_eq_true rfl))
  have e_v50 : (v50 = 1 ↔ sv t42.1 < sv t43.1) := e_plt h_t42_1 h_t43_1 (of_decide_eq_true rfl)
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
  clear h_v42 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v59
  have e_v61 : sv v61 = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have h_v62 : R 1 0 0 1 v62 v62 := (r_plt hl h_v29 h_v61 (of_decide_eq_true rfl))
  have e_v62 : (v62 = 1 ↔ sv v29 < sv v61) := e_plt h_v29 h_v61 (of_decide_eq_true rfl)
  have h_v63 : R 1 0 0 1 v63 v63 := (r_sub hl (r_O hl) h_v62 (of_decide_eq_true rfl))
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
  have h_v69 : R 1 0 0 1 v69 v69 := (r_sub hl (r_O hl) h_v68 (of_decide_eq_true rfl))
  have e_v69 : (v69 = 1 ↔ ¬v68 = 1) := e_not h_v68 (of_decide_eq_true rfl)
  have h_v70 : R 1 0 0 1 v70 v70 := (r_plt hl h_v61 h_v60 (of_decide_eq_true rfl))
  have e_v70 : (v70 = 1 ↔ sv v61 < sv v60) := e_plt h_v61 h_v60 (of_decide_eq_true rfl)
  have h_v71 : R 1 0 0 1 v71 v71 := (r_sub hl (r_O hl) h_v70 (of_decide_eq_true rfl))
  have e_v71 : (v71 = 1 ↔ ¬v70 = 1) := e_not h_v70 (of_decide_eq_true rfl)
  have h_v72 : R 1 0 0 1 v72 v72 := (r_land hl h_v68 h_v71 (of_decide_eq_true rfl))
  have e_v72 : (v72 = 1 ↔ v68 = 1 ∧ v71 = 1) := e_land h_v68 h_v71 (of_decide_eq_true rfl)
  have h_v73 : R 1 0 0 1 v73 v73 := (r_land hl h_v68 h_v70 (of_decide_eq_true rfl))
  have e_v73 : (v73 = 1 ↔ v68 = 1 ∧ v70 = 1) := e_land h_v68 h_v70 (of_decide_eq_true rfl)
  clear h_v62 h_v64 h_v65 h_v68 h_v70 h_v71
  have h_v74 : R 1 0 0 1 v74 v74 := (r_land hl h_v67 h_v73 (of_decide_eq_true rfl))
  have e_v74 : (v74 = 1 ↔ v67 = 1 ∧ v73 = 1) := e_land h_v67 h_v73 (of_decide_eq_true rfl)
  have h_v75 : R 1 0 0 1 v75 v75 := (r_sub hl (r_O hl) h_v74 (of_decide_eq_true rfl))
  have e_v75 : (v75 = 1 ↔ ¬v74 = 1) := e_not h_v74 (of_decide_eq_true rfl)
  have h_v76 : R 1 0 0 1 v76 v76 := (r_land hl h_v63 h_v73 (of_decide_eq_true rfl))
  have e_v76 : (v76 = 1 ↔ v63 = 1 ∧ v73 = 1) := e_land h_v63 h_v73 (of_decide_eq_true rfl)
  have h_v77 : R 1 0 0 1 v77 v77 := (r_lor hl h_v72 h_v76 (of_decide_eq_true rfl))
  have e_v77 : (v77 = 1 ↔ v72 = 1 ∨ v76 = 1) := e_lor h_v72 h_v76 (of_decide_eq_true rfl)
  have h_v78 : R 1 0 4611686018427387900 4611686018695823367 v78 v78 := (r_psel hl h_v77 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v78 : v78 = if v77 = 1 then v41 else v29 := e_psel h_v77 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v79 : R 1 0 0 1 v79 v79 := (r_land hl h_v67 h_v69 (of_decide_eq_true rfl))
  have e_v79 : (v79 = 1 ↔ v67 = 1 ∧ v69 = 1) := e_land h_v67 h_v69 (of_decide_eq_true rfl)
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
  clear h_v69 h_v72 h_v73 h_v74 h_v76 h_v77 h_v79 h_v80 h_v82 h_v83
  have e_v86 : (v86 = 1 ↔ v66 = 1 ∨ v85 = 1) := e_lor h_v66 h_v85 (of_decide_eq_true rfl)
  have h_v87 : R 1 0 4611686018427387900 4611686018695823367 v87 v87 := (r_psel hl h_v86 h_v52 h_v60 (of_decide_eq_true rfl))
  have e_v87 : v87 = if v86 = 1 then v52 else v60 := e_psel h_v86 h_v52 h_v60 (of_decide_eq_true rfl)
  have h_v88 : R 1 0 4611686017353646052 4683743616223412273 v88 v88 := (r_smx hl 29 h_v81 h_v78 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v88 : sv v88 = sv v81 * sv v78 := e_smx 29 h_v81 h_v78 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v89 : R 1 0 4611686018427387899 4611686018695823374 v89 v89 := (r_srdF hl h_v88 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v89 : sv v89 = sv v88 / 2 ^ 28 := e_srdF h_v88 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v90 : R 1 0 4611686017353646052 4683743616223412273 v90 v90 := (r_smx hl 29 h_v87 h_v84 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v90 : sv v90 = sv v87 * sv v84 := e_smx 29 h_v87 h_v84 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v91 : R 1 0 4611686018427387900 4611686018695823375 v91 v91 := (r_srdC hl h_v90 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v91 : sv v91 = -((-sv v90) / 2 ^ 28) := e_srdC h_v90 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v92 : R 1 0 0 1 v92 v92 := (r_plt hl h_v19 h_v89 (of_decide_eq_true rfl))
  have e_v92 : (v92 = 1 ↔ sv v19 < sv v89) := e_plt h_v19 h_v89 (of_decide_eq_true rfl)
  have h_v94 : R 1 0 4611686018158952441 4611686018695823359 v94 v94 := (r_sub hl (r_add hl h_v28 h_t1_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v94 : sv v94 = sv v28 + sv t1.2 := e_add h_v28 h_t1_2 (of_decide_eq_true rfl)
  have h_v95 : R 1 0 4611686018158952448 4611686018158952448 v95 v95 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have e_v95 : sv v95 = (-268435456) := e_c 4611686018158952448 (-268435456) (of_decide_eq_true rfl)
  have h_v96 : R 1 0 0 1 v96 v96 := (r_plt hl h_v94 h_v95 (of_decide_eq_true rfl))
  have e_v96 : (v96 = 1 ↔ sv v94 < sv v95) := e_plt h_v94 h_v95 (of_decide_eq_true rfl)
  have h_v97 : R 1 0 4611686018158952441 4611686018695823359 v97 v97 := (r_psel hl h_v96 h_v95 h_v94 (of_decide_eq_true rfl))
  have e_v97 : v97 = if v96 = 1 then v95 else v94 := e_psel h_v96 h_v95 h_v94 (of_decide_eq_true rfl)
  have h_v98 : R 1 0 4611686019270702759 4611686019270702759 v98 v98 := (r_c hl 4611686019270702759 (of_decide_eq_true rfl))
  have e_v98 : sv v98 = (843314855) := e_c 4611686019270702759 (843314855) (of_decide_eq_true rfl)
  have h_v99 : R 1 0 0 1 v99 v99 := (r_plt hl h_v98 h_v1 (of_decide_eq_true rfl))
  have e_v99 : (v99 = 1 ↔ sv v98 < sv v1) := e_plt h_v98 h_v1 (of_decide_eq_true rfl)
  clear h_v1 h_t1_2 h_v52 h_v60 h_v78 h_v81 h_v84 h_v85 h_v86 h_v87 h_v88 h_v90 h_v94 h_v96
  have h_v100 : R 1 0 4611686018158952441 4611686018695823359 v100 v100 := (r_psel hl h_v99 h_v95 h_v97 (of_decide_eq_true rfl))
  have e_v100 : v100 = if v99 = 1 then v95 else v97 := e_psel h_v99 h_v95 h_v97 (of_decide_eq_true rfl)
  have h_v102 : R 1 0 4611686018158952449 4611686018695823367 v102 v102 := (r_sub hl (r_add hl h_v31 h_t0_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v102 : sv v102 = sv v31 + sv t0.2 := e_add h_v31 h_t0_2 (of_decide_eq_true rfl)
  have h_v103 : R 1 0 0 1 v103 v103 := (r_plt hl h_v102 h_v33 (of_decide_eq_true rfl))
  have e_v103 : (v103 = 1 ↔ sv v102 < sv v33) := e_plt h_v102 h_v33 (of_decide_eq_true rfl)
  have h_v104 : R 1 0 4611686018158952449 4611686018695823367 v104 v104 := (r_psel hl h_v103 h_v102 h_v33 (of_decide_eq_true rfl))
  have e_v104 : v104 = if v103 = 1 then v102 else v33 := e_psel h_v103 h_v102 h_v33 (of_decide_eq_true rfl)
  have h_v105 : R 1 0 4611686018427387905 4611686018427387905 v105 v105 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have e_v105 : sv v105 = (1) := e_c 4611686018427387905 (1) (of_decide_eq_true rfl)
  have h_v106 : R 1 0 0 1 v106 v106 := (r_plt hl h_v0 h_v105 (of_decide_eq_true rfl))
  have e_v106 : (v106 = 1 ↔ sv v0 < sv v105) := e_plt h_v0 h_v105 (of_decide_eq_true rfl)
  have h_v107 : R 1 0 4611686018158952449 4611686018695823367 v107 v107 := (r_psel hl h_v106 h_v33 h_v104 (of_decide_eq_true rfl))
  have e_v107 : v107 = if v106 = 1 then v33 else v104 := e_psel h_v106 h_v33 h_v104 (of_decide_eq_true rfl)
  have h_v108 : R 1 0 4611686018427387904 4611686052787126264 v108 v108 := (r_add hl (r_pshr1 hl h_v3) h_H61r (of_decide_eq_true rfl))
  have e_v108 : sv v108 = sv v3 / 2 := e_halfF h_v3
  have h_v109 : R 1 0 0 1 v109 v109 := (r_plt hl h_v19 h_v108 (of_decide_eq_true rfl))
  have e_v109 : (v109 = 1 ↔ sv v19 < sv v108) := e_plt h_v19 h_v108 (of_decide_eq_true rfl)
  have h_v110 : R 1 0 0 1 v110 v110 := (r_land hl h_v46 h_v109 (of_decide_eq_true rfl))
  have e_v110 : (v110 = 1 ↔ v46 = 1 ∧ v109 = 1) := e_land h_v46 h_v109 (of_decide_eq_true rfl)
  have h_v112 : R 1 0 4611686018158952441 4611686018695823359 v112 v112 := (r_sub hl (r_add hl h_v28 h_t43_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v112 : sv v112 = sv v28 + sv t43.2 := e_add h_v28 h_t43_2 (of_decide_eq_true rfl)
  have h_v113 : R 1 0 0 1 v113 v113 := (r_plt hl h_v112 h_v95 (of_decide_eq_true rfl))
  have e_v113 : (v113 = 1 ↔ sv v112 < sv v95) := e_plt h_v112 h_v95 (of_decide_eq_true rfl)
  have h_v114 : R 1 0 4611686018158952441 4611686018695823359 v114 v114 := (r_psel hl h_v113 h_v95 h_v112 (of_decide_eq_true rfl))
  clear h_v0 h_v3 h_t0_2 h_v46 h_t43_2 h_v97 h_v99 h_v102 h_v103 h_v104 h_v106 h_v109
  have e_v114 : v114 = if v113 = 1 then v95 else v112 := e_psel h_v113 h_v95 h_v112 (of_decide_eq_true rfl)
  have h_v115 : R 1 0 0 1 v115 v115 := (r_plt hl h_v98 h_v43 (of_decide_eq_true rfl))
  have e_v115 : (v115 = 1 ↔ sv v98 < sv v43) := e_plt h_v98 h_v43 (of_decide_eq_true rfl)
  have h_v116 : R 1 0 4611686018158952441 4611686018695823359 v116 v116 := (r_psel hl h_v115 h_v95 h_v114 (of_decide_eq_true rfl))
  have e_v116 : v116 = if v115 = 1 then v95 else v114 := e_psel h_v115 h_v95 h_v114 (of_decide_eq_true rfl)
  have h_t108_1 : R 1 0 4611686018427387904 4611686018695823363 t108.1 t108.1 := r_sc1 hl h_v108 (of_decide_eq_true rfl)
  have h_t108_2 : R 1 0 4611686018158952445 4611686018695823363 t108.2 t108.2 := r_sc2 hl h_v108 (of_decide_eq_true rfl)
  have e_t108_1 : sv t108.1 = (sc28pS (scArg v108)).1 := e_sc1 h_v108 (of_decide_eq_true rfl)
  have e_t108_2 : sv t108.2 = (sc28pS (scArg v108)).2 := e_sc2 h_v108 (of_decide_eq_true rfl)
  have h_v124 : R 1 0 0 1 v124 v124 := (r_plt hl h_t108_1 h_t43_1 (of_decide_eq_true rfl))
  have e_v124 : (v124 = 1 ↔ sv t108.1 < sv t43.1) := e_plt h_t108_1 h_t43_1 (of_decide_eq_true rfl)
  have h_v125 : R 1 0 4611686018427387904 4611686018695823363 v125 v125 := (r_psel hl h_v124 h_t108_1 h_t43_1 (of_decide_eq_true rfl))
  have e_v125 : v125 = if v124 = 1 then t108.1 else t43.1 := e_psel h_v124 h_t108_1 h_t43_1 (of_decide_eq_true rfl)
  have h_v126 : R 1 0 4611686018427387900 4611686018695823359 v126 v126 := (r_sub hl (r_add hl h_v28 h_v125 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v126 : sv v126 = sv v28 + sv v125 := e_add h_v28 h_v125 (of_decide_eq_true rfl)
  have h_v127 : R 1 0 4611686018427387904 4611686018695823363 v127 v127 := (r_psel hl h_v124 h_t43_1 h_t108_1 (of_decide_eq_true rfl))
  have e_v127 : v127 = if v124 = 1 then t43.1 else t108.1 := e_psel h_v124 h_t43_1 h_t108_1 (of_decide_eq_true rfl)
  have h_v128 : R 1 0 4611686018427387908 4611686018695823367 v128 v128 := (r_sub hl (r_add hl h_v31 h_v127 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v128 : sv v128 = sv v31 + sv v127 := e_add h_v31 h_v127 (of_decide_eq_true rfl)
  have h_v129 : R 1 0 0 1 v129 v129 := (r_plt hl h_v128 h_v33 (of_decide_eq_true rfl))
  have e_v129 : (v129 = 1 ↔ sv v128 < sv v33) := e_plt h_v128 h_v33 (of_decide_eq_true rfl)
  have h_v130 : R 1 0 4611686018427387908 4611686018695823367 v130 v130 := (r_psel hl h_v129 h_v128 h_v33 (of_decide_eq_true rfl))
  have e_v130 : v130 = if v129 = 1 then v128 else v33 := e_psel h_v129 h_v128 h_v33 (of_decide_eq_true rfl)
  have h_v131 : R 1 0 0 1 v131 v131 := (r_plt hl h_v108 h_v36 (of_decide_eq_true rfl))
  have e_v131 : (v131 = 1 ↔ sv v108 < sv v36) := e_plt h_v108 h_v36 (of_decide_eq_true rfl)
  clear h_v43 h_t43_1 h_v108 h_v112 h_v113 h_v114 h_v115 h_t108_1 h_t108_2 e_t108_2 h_v124 h_v125 h_v127 h_v128 h_v129
  have h_v132 : R 1 0 0 1 v132 v132 := (r_land hl h_v58 h_v131 (of_decide_eq_true rfl))
  have e_v132 : (v132 = 1 ↔ v58 = 1 ∧ v131 = 1) := e_land h_v58 h_v131 (of_decide_eq_true rfl)
  have h_v133 : R 1 0 4611686018427387908 4611686018695823367 v133 v133 := (r_psel hl h_v132 h_v33 h_v130 (of_decide_eq_true rfl))
  have e_v133 : v133 = if v132 = 1 then v33 else v130 := e_psel h_v132 h_v33 h_v130 (of_decide_eq_true rfl)
  have h_v134 : R 1 0 0 1 v134 v134 := (r_plt hl h_v100 h_v61 (of_decide_eq_true rfl))
  have e_v134 : (v134 = 1 ↔ sv v100 < sv v61) := e_plt h_v100 h_v61 (of_decide_eq_true rfl)
  have h_v135 : R 1 0 0 1 v135 v135 := (r_sub hl (r_O hl) h_v134 (of_decide_eq_true rfl))
  have e_v135 : (v135 = 1 ↔ ¬v134 = 1) := e_not h_v134 (of_decide_eq_true rfl)
  have h_v136 : R 1 0 0 1 v136 v136 := (r_plt hl h_v61 h_v107 (of_decide_eq_true rfl))
  have e_v136 : (v136 = 1 ↔ sv v61 < sv v107) := e_plt h_v61 h_v107 (of_decide_eq_true rfl)
  have h_v137 : R 1 0 0 1 v137 v137 := (r_sub hl (r_O hl) h_v136 (of_decide_eq_true rfl))
  have e_v137 : (v137 = 1 ↔ ¬v136 = 1) := e_not h_v136 (of_decide_eq_true rfl)
  have h_v138 : R 1 0 0 1 v138 v138 := (r_land hl h_v134 h_v137 (of_decide_eq_true rfl))
  have e_v138 : (v138 = 1 ↔ v134 = 1 ∧ v137 = 1) := e_land h_v134 h_v137 (of_decide_eq_true rfl)
  have h_v139 : R 1 0 0 1 v139 v139 := (r_land hl h_v134 h_v136 (of_decide_eq_true rfl))
  have e_v139 : (v139 = 1 ↔ v134 = 1 ∧ v136 = 1) := e_land h_v134 h_v136 (of_decide_eq_true rfl)
  have h_v140 : R 1 0 0 1 v140 v140 := (r_plt hl h_v126 h_v61 (of_decide_eq_true rfl))
  have e_v140 : (v140 = 1 ↔ sv v126 < sv v61) := e_plt h_v126 h_v61 (of_decide_eq_true rfl)
  have h_v141 : R 1 0 0 1 v141 v141 := (r_sub hl (r_O hl) h_v140 (of_decide_eq_true rfl))
  have e_v141 : (v141 = 1 ↔ ¬v140 = 1) := e_not h_v140 (of_decide_eq_true rfl)
  have h_v142 : R 1 0 0 1 v142 v142 := (r_plt hl h_v61 h_v133 (of_decide_eq_true rfl))
  have e_v142 : (v142 = 1 ↔ sv v61 < sv v133) := e_plt h_v61 h_v133 (of_decide_eq_true rfl)
  have h_v143 : R 1 0 0 1 v143 v143 := (r_sub hl (r_O hl) h_v142 (of_decide_eq_true rfl))
  have e_v143 : (v143 = 1 ↔ ¬v142 = 1) := e_not h_v142 (of_decide_eq_true rfl)
  have h_v144 : R 1 0 0 1 v144 v144 := (r_land hl h_v140 h_v143 (of_decide_eq_true rfl))
  clear h_v58 h_v130 h_v131 h_v132 h_v134 h_v136 h_v137
  have e_v144 : (v144 = 1 ↔ v140 = 1 ∧ v143 = 1) := e_land h_v140 h_v143 (of_decide_eq_true rfl)
  have h_v145 : R 1 0 0 1 v145 v145 := (r_land hl h_v140 h_v142 (of_decide_eq_true rfl))
  have e_v145 : (v145 = 1 ↔ v140 = 1 ∧ v142 = 1) := e_land h_v140 h_v142 (of_decide_eq_true rfl)
  have h_v146 : R 1 0 0 1 v146 v146 := (r_land hl h_v139 h_v145 (of_decide_eq_true rfl))
  have e_v146 : (v146 = 1 ↔ v139 = 1 ∧ v145 = 1) := e_land h_v139 h_v145 (of_decide_eq_true rfl)
  have h_v147 : R 1 0 0 1 v147 v147 := (r_sub hl (r_O hl) h_v146 (of_decide_eq_true rfl))
  have e_v147 : (v147 = 1 ↔ ¬v146 = 1) := e_not h_v146 (of_decide_eq_true rfl)
  have h_v148 : R 1 0 0 1 v148 v148 := (r_land hl h_v135 h_v145 (of_decide_eq_true rfl))
  have e_v148 : (v148 = 1 ↔ v135 = 1 ∧ v145 = 1) := e_land h_v135 h_v145 (of_decide_eq_true rfl)
  have h_v149 : R 1 0 0 1 v149 v149 := (r_lor hl h_v144 h_v148 (of_decide_eq_true rfl))
  have e_v149 : (v149 = 1 ↔ v144 = 1 ∨ v148 = 1) := e_lor h_v144 h_v148 (of_decide_eq_true rfl)
  have h_v150 : R 1 0 4611686018158952441 4611686018695823367 v150 v150 := (r_psel hl h_v149 h_v107 h_v100 (of_decide_eq_true rfl))
  have e_v150 : v150 = if v149 = 1 then v107 else v100 := e_psel h_v149 h_v107 h_v100 (of_decide_eq_true rfl)
  have h_v151 : R 1 0 0 1 v151 v151 := (r_land hl h_v139 h_v141 (of_decide_eq_true rfl))
  have e_v151 : (v151 = 1 ↔ v139 = 1 ∧ v141 = 1) := e_land h_v139 h_v141 (of_decide_eq_true rfl)
  have h_v152 : R 1 0 0 1 v152 v152 := (r_lor hl h_v138 h_v151 (of_decide_eq_true rfl))
  have e_v152 : (v152 = 1 ↔ v138 = 1 ∨ v151 = 1) := e_lor h_v138 h_v151 (of_decide_eq_true rfl)
  have h_v153 : R 1 0 4611686018427387900 4611686018695823367 v153 v153 := (r_psel hl h_v152 h_v133 h_v126 (of_decide_eq_true rfl))
  have e_v153 : v153 = if v152 = 1 then v133 else v126 := e_psel h_v152 h_v133 h_v126 (of_decide_eq_true rfl)
  have h_v154 : R 1 0 0 1 v154 v154 := (r_land hl h_v138 h_v145 (of_decide_eq_true rfl))
  have e_v154 : (v154 = 1 ↔ v138 = 1 ∧ v145 = 1) := e_land h_v138 h_v145 (of_decide_eq_true rfl)
  have h_v155 : R 1 0 0 1 v155 v155 := (r_lor hl h_v144 h_v154 (of_decide_eq_true rfl))
  have e_v155 : (v155 = 1 ↔ v144 = 1 ∨ v154 = 1) := e_lor h_v144 h_v154 (of_decide_eq_true rfl)
  have h_v156 : R 1 0 4611686018158952441 4611686018695823367 v156 v156 := (r_psel hl h_v155 h_v100 h_v107 (of_decide_eq_true rfl))
  have e_v156 : v156 = if v155 = 1 then v100 else v107 := e_psel h_v155 h_v100 h_v107 (of_decide_eq_true rfl)
  clear h_v140 h_v141 h_v142 h_v143 h_v145 h_v146 h_v148 h_v149 h_v151 h_v152 h_v154 h_v155
  have h_v157 : R 1 0 0 1 v157 v157 := (r_land hl h_v139 h_v144 (of_decide_eq_true rfl))
  have e_v157 : (v157 = 1 ↔ v139 = 1 ∧ v144 = 1) := e_land h_v139 h_v144 (of_decide_eq_true rfl)
  have h_v158 : R 1 0 0 1 v158 v158 := (r_lor hl h_v138 h_v157 (of_decide_eq_true rfl))
  have e_v158 : (v158 = 1 ↔ v138 = 1 ∨ v157 = 1) := e_lor h_v138 h_v157 (of_decide_eq_true rfl)
  have h_v159 : R 1 0 4611686018427387900 4611686018695823367 v159 v159 := (r_psel hl h_v158 h_v126 h_v133 (of_decide_eq_true rfl))
  have e_v159 : v159 = if v158 = 1 then v126 else v133 := e_psel h_v158 h_v126 h_v133 (of_decide_eq_true rfl)
  have h_v160 : R 1 0 4539628420631363535 4683743616223412273 v160 v160 := (r_smx hl 29 h_v153 h_v150 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v160 : sv v160 = sv v153 * sv v150 := e_smx 29 h_v153 h_v150 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v161 : R 1 0 4611686018158952433 4611686018695823374 v161 v161 := (r_srdF hl h_v160 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v161 : sv v161 = sv v160 / 2 ^ 28 := e_srdF h_v160 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v162 : R 1 0 4539628420631363535 4683743616223412273 v162 v162 := (r_smx hl 29 h_v159 h_v156 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v162 : sv v162 = sv v159 * sv v156 := e_smx 29 h_v159 h_v156 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v163 : R 1 0 4611686018158952434 4611686018695823375 v163 v163 := (r_srdC hl h_v162 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v163 : sv v163 = -((-sv v162) / 2 ^ 28) := e_srdC h_v162 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v164 : R 1 0 0 1 v164 v164 := (r_plt hl h_v61 h_v161 (of_decide_eq_true rfl))
  have e_v164 : (v164 = 1 ↔ sv v61 < sv v161) := e_plt h_v61 h_v161 (of_decide_eq_true rfl)
  have h_v165 : R 1 0 0 1 v165 v165 := (r_sub hl (r_O hl) h_v164 (of_decide_eq_true rfl))
  have e_v165 : (v165 = 1 ↔ ¬v164 = 1) := e_not h_v164 (of_decide_eq_true rfl)
  have h_v166 : R 1 0 0 1 v166 v166 := (r_plt hl h_v116 h_v61 (of_decide_eq_true rfl))
  have e_v166 : (v166 = 1 ↔ sv v116 < sv v61) := e_plt h_v116 h_v61 (of_decide_eq_true rfl)
  have h_v167 : R 1 0 4611686018158952433 4611686018695823375 v167 v167 := (r_psel hl h_v166 h_v161 h_v163 (of_decide_eq_true rfl))
  have e_v167 : v167 = if v166 = 1 then v161 else v163 := e_psel h_v166 h_v161 h_v163 (of_decide_eq_true rfl)
  have h_v170 : R 1 0 4611686018158952449 4611686018695823367 v170 v170 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v116 (of_decide_eq_true rfl))
  have e_v170 : sv v170 = sv v61 - sv v116 := e_sub h_v61 h_v116 (of_decide_eq_true rfl)
  have h_v171 : R 1 0 4611686018158952441 4611686018695823367 v171 v171 := (r_psel hl h_v166 h_v170 h_v116 (of_decide_eq_true rfl))
  clear h_v126 h_v133 h_v144 h_v150 h_v153 h_v156 h_v157 h_v158 h_v159 h_v160 h_v161 h_v162 h_v163 h_v164
  have e_v171 : v171 = if v166 = 1 then v170 else v116 := e_psel h_v166 h_v170 h_v116 (of_decide_eq_true rfl)
  have h_v172 : R 1 0 4611686018427387904 4611686019501129727 v172 v172 := (r1_hxa hb_H0 0 (of_decide_eq_true rfl))
  have e_v172 : sv v172 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 0 (of_decide_eq_true rfl)
  have h_v173 : R 1 0 0 1 v173 v173 := (r_sub hl (r_O hl) h_v166 (of_decide_eq_true rfl))
  have e_v173 : (v173 = 1 ↔ ¬v166 = 1) := e_not h_v166 (of_decide_eq_true rfl)
  have h_t172_1 : R 1 0 4611686018427387904 4611686018695823363 t172.1 t172.1 := r_sc1 hl h_v172 (of_decide_eq_true rfl)
  have h_t172_2 : R 1 0 4611686018158952445 4611686018695823363 t172.2 t172.2 := r_sc2 hl h_v172 (of_decide_eq_true rfl)
  have e_t172_1 : sv t172.1 = (sc28pS (scArg v172)).1 := e_sc1 h_v172 (of_decide_eq_true rfl)
  have e_t172_2 : sv t172.2 = (sc28pS (scArg v172)).2 := e_sc2 h_v172 (of_decide_eq_true rfl)
  have h_v175 : R 1 0 4611686018158952441 4611686018695823359 v175 v175 := (r_sub hl (r_add hl h_v28 h_t172_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v175 : sv v175 = sv v28 + sv t172.2 := e_add h_v28 h_t172_2 (of_decide_eq_true rfl)
  have h_v176 : R 1 0 0 1 v176 v176 := (r_plt hl h_v175 h_v95 (of_decide_eq_true rfl))
  have e_v176 : (v176 = 1 ↔ sv v175 < sv v95) := e_plt h_v175 h_v95 (of_decide_eq_true rfl)
  have h_v177 : R 1 0 4611686018158952441 4611686018695823359 v177 v177 := (r_psel hl h_v176 h_v95 h_v175 (of_decide_eq_true rfl))
  have e_v177 : v177 = if v176 = 1 then v95 else v175 := e_psel h_v176 h_v95 h_v175 (of_decide_eq_true rfl)
  have h_v178 : R 1 0 4611686018158952449 4611686018695823367 v178 v178 := (r_sub hl (r_add hl h_v31 h_t172_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v178 : sv v178 = sv v31 + sv t172.2 := e_add h_v31 h_t172_2 (of_decide_eq_true rfl)
  have h_v179 : R 1 0 0 1 v179 v179 := (r_plt hl h_v178 h_v33 (of_decide_eq_true rfl))
  have e_v179 : (v179 = 1 ↔ sv v178 < sv v33) := e_plt h_v178 h_v33 (of_decide_eq_true rfl)
  have h_v180 : R 1 0 4611686018158952449 4611686018695823367 v180 v180 := (r_psel hl h_v179 h_v178 h_v33 (of_decide_eq_true rfl))
  have e_v180 : v180 = if v179 = 1 then v178 else v33 := e_psel h_v179 h_v178 h_v33 (of_decide_eq_true rfl)
  have h_v182 : R 1 0 4611686018427387908 4611686018695823367 v182 v182 := (r_sub hl (r_add hl h_v31 h_t172_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v182 : sv v182 = sv v31 + sv t172.1 := e_add h_v31 h_t172_1 (of_decide_eq_true rfl)
  have h_v183 : R 1 0 0 1 v183 v183 := (r_plt hl h_v182 h_v33 (of_decide_eq_true rfl))
  have e_v183 : (v183 = 1 ↔ sv v182 < sv v33) := e_plt h_v182 h_v33 (of_decide_eq_true rfl)
  clear h_v116 h_v170 h_t172_2 h_v175 h_v176 h_v178 h_v179
  have h_v184 : R 1 0 4611686018427387908 4611686018695823367 v184 v184 := (r_psel hl h_v183 h_v182 h_v33 (of_decide_eq_true rfl))
  have e_v184 : v184 = if v183 = 1 then v182 else v33 := e_psel h_v183 h_v182 h_v33 (of_decide_eq_true rfl)
  have h_v185 : R 1 0 4611686018427387900 4611686018695823359 v185 v185 := (r_sub hl (r_add hl h_v28 h_t172_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v185 : sv v185 = sv v28 + sv t172.1 := e_add h_v28 h_t172_1 (of_decide_eq_true rfl)
  have h_v186 : R 1 0 4611686018158952441 4611686018695823367 v186 v186 := (r_psel hl h_v173 h_v177 h_v180 (of_decide_eq_true rfl))
  have e_v186 : v186 = if v173 = 1 then v177 else v180 := e_psel h_v173 h_v177 h_v180 (of_decide_eq_true rfl)
  have h_v187 : R 1 0 4611686018427387900 4611686018695823367 v187 v187 := (r_psel hl h_v173 h_v184 h_v185 (of_decide_eq_true rfl))
  have e_v187 : v187 = if v173 = 1 then v184 else v185 := e_psel h_v173 h_v184 h_v185 (of_decide_eq_true rfl)
  have h_v188 : R 1 0 4539628418483879831 4683743618370895977 v188 v188 := (r_smx hl 29 h_v167 h_v187 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v188 : sv v188 = sv v167 * sv v187 := e_smx 29 h_v167 h_v187 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v189 : R 1 0 4539628420631363535 4683743616223412273 v189 v189 := (r_smx hl 29 h_v186 h_v171 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v189 : sv v189 = sv v186 * sv v171 := e_smx 29 h_v186 h_v171 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v190 : R 1 0 0 1 v190 v190 := (r_plt hl h_v189 h_v188 (of_decide_eq_true rfl))
  have e_v190 : (v190 = 1 ↔ sv v189 < sv v188) := e_plt h_v189 h_v188 (of_decide_eq_true rfl)
  have h_v191 : R 1 0 0 1 v191 v191 := (r_sub hl (r_O hl) h_v190 (of_decide_eq_true rfl))
  have e_v191 : (v191 = 1 ↔ ¬v190 = 1) := e_not h_v190 (of_decide_eq_true rfl)
  have h_v192 : R 1 0 0 1 v192 v192 := (r_plt hl h_v188 h_v189 (of_decide_eq_true rfl))
  have e_v192 : (v192 = 1 ↔ sv v188 < sv v189) := e_plt h_v188 h_v189 (of_decide_eq_true rfl)
  have h_v193 : R 1 0 0 1 v193 v193 := (r_sub hl (r_O hl) h_v192 (of_decide_eq_true rfl))
  have e_v193 : (v193 = 1 ↔ ¬v192 = 1) := e_not h_v192 (of_decide_eq_true rfl)
  have h_v194 : R 1 0 0 1 v194 v194 := (r_plt hl h_v61 h_v172 (of_decide_eq_true rfl))
  have e_v194 : (v194 = 1 ↔ sv v61 < sv v172) := e_plt h_v61 h_v172 (of_decide_eq_true rfl)
  have h_v195 : R 1 0 0 1 v195 v195 := (r_sub hl (r_O hl) h_v194 (of_decide_eq_true rfl))
  have e_v195 : (v195 = 1 ↔ ¬v194 = 1) := e_not h_v194 (of_decide_eq_true rfl)
  have h_v196 : R 1 0 4611686018849045332 4611686018849045332 v196 v196 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  clear h_v167 h_v171 h_t172_1 h_v180 h_v182 h_v183 h_v184 h_v185 h_v186 h_v187 h_v188 h_v189 h_v190 h_v192 h_v194
  have e_v196 : sv v196 = (421657428) := e_c 4611686018849045332 (421657428) (of_decide_eq_true rfl)
  have h_v197 : R 1 0 0 1 v197 v197 := (r_plt hl h_v196 h_v172 (of_decide_eq_true rfl))
  have e_v197 : (v197 = 1 ↔ sv v196 < sv v172) := e_plt h_v196 h_v172 (of_decide_eq_true rfl)
  have h_v198 : R 1 0 0 1 v198 v198 := (r_sub hl (r_O hl) h_v197 (of_decide_eq_true rfl))
  have e_v198 : (v198 = 1 ↔ ¬v197 = 1) := e_not h_v197 (of_decide_eq_true rfl)
  have h_v199 : R 1 0 0 1 v199 v199 := (r_plt hl h_v19 h_v177 (of_decide_eq_true rfl))
  have e_v199 : (v199 = 1 ↔ sv v19 < sv v177) := e_plt h_v19 h_v177 (of_decide_eq_true rfl)
  have h_v200 : R 1 0 0 1 v200 v200 := (r_land hl h_v191 h_v199 (of_decide_eq_true rfl))
  have e_v200 : (v200 = 1 ↔ v191 = 1 ∧ v199 = 1) := e_land h_v191 h_v199 (of_decide_eq_true rfl)
  have h_v201 : R 1 0 0 1 v201 v201 := (r_land hl h_v198 h_v200 (of_decide_eq_true rfl))
  have e_v201 : (v201 = 1 ↔ v198 = 1 ∧ v200 = 1) := e_land h_v198 h_v200 (of_decide_eq_true rfl)
  have h_v202 : R 1 0 0 1 v202 v202 := (r_lor hl h_v195 h_v201 (of_decide_eq_true rfl))
  have e_v202 : (v202 = 1 ↔ v195 = 1 ∨ v201 = 1) := e_lor h_v195 h_v201 (of_decide_eq_true rfl)
  have h_v203 : R 1 0 4611686018849045333 4611686018849045333 v203 v203 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have e_v203 : sv v203 = (421657429) := e_c 4611686018849045333 (421657429) (of_decide_eq_true rfl)
  have h_v204 : R 1 0 0 1 v204 v204 := (r_plt hl h_v172 h_v203 (of_decide_eq_true rfl))
  have e_v204 : (v204 = 1 ↔ sv v172 < sv v203) := e_plt h_v172 h_v203 (of_decide_eq_true rfl)
  have h_v205 : R 1 0 0 1 v205 v205 := (r_sub hl (r_O hl) h_v204 (of_decide_eq_true rfl))
  have e_v205 : (v205 = 1 ↔ ¬v204 = 1) := e_not h_v204 (of_decide_eq_true rfl)
  have h_v206 : R 1 0 0 1 v206 v206 := (r_lor hl h_v193 h_v205 (of_decide_eq_true rfl))
  have e_v206 : (v206 = 1 ↔ v193 = 1 ∨ v205 = 1) := e_lor h_v193 h_v205 (of_decide_eq_true rfl)
  have h_v207 : R 1 0 0 1 v207 v207 := (r_land hl h_v173 h_v202 (of_decide_eq_true rfl))
  have e_v207 : (v207 = 1 ↔ v173 = 1 ∧ v202 = 1) := e_land h_v173 h_v202 (of_decide_eq_true rfl)
  have h_v208 : R 1 0 0 1 v208 v208 := (r_land hl h_v166 h_v206 (of_decide_eq_true rfl))
  have e_v208 : (v208 = 1 ↔ v166 = 1 ∧ v206 = 1) := e_land h_v166 h_v206 (of_decide_eq_true rfl)
  clear h_v173 h_v177 h_v191 h_v193 h_v195 h_v197 h_v198 h_v199 h_v200 h_v201 h_v202 h_v204 h_v205 h_v206
  have h_v209 : R 1 0 0 1 v209 v209 := (r_lor hl h_v207 h_v208 (of_decide_eq_true rfl))
  have e_v209 : (v209 = 1 ↔ v207 = 1 ∨ v208 = 1) := e_lor h_v207 h_v208 (of_decide_eq_true rfl)
  have h_v210 : R 1 0 4611686017353646081 4611686018427387904 v210 v210 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v172 (of_decide_eq_true rfl))
  have e_v210 : sv v210 = sv v61 - sv v172 := e_sub h_v61 h_v172 (of_decide_eq_true rfl)
  have h_v211 : R 1 0 4611686017353646081 4611686019501129727 v211 v211 := (r_psel hl h_v166 h_v210 h_v172 (of_decide_eq_true rfl))
  have e_v211 : v211 = if v166 = 1 then v210 else v172 := e_psel h_v166 h_v210 h_v172 (of_decide_eq_true rfl)
  have h_v212 : R 1 0 4611686018005730475 4611686018005730475 v212 v212 := (r_c hl 4611686018005730475 (of_decide_eq_true rfl))
  have e_v212 : sv v212 = (-421657429) := e_c 4611686018005730475 (-421657429) (of_decide_eq_true rfl)
  have h_v213 : R 1 0 4611686017353646081 4611686019501129727 v213 v213 := (r_psel hl h_v209 h_v211 h_v212 (of_decide_eq_true rfl))
  have e_v213 : v213 = if v209 = 1 then v211 else v212 := e_psel h_v209 h_v211 h_v212 (of_decide_eq_true rfl)
  have h_v255 : R 1 0 4611686017353646081 4611686019501129727 v255 v255 := (r_psel hl h_v165 h_v212 h_v213 (of_decide_eq_true rfl))
  have e_v255 : v255 = if v165 = 1 then v212 else v213 := e_psel h_v165 h_v212 h_v213 (of_decide_eq_true rfl)
  have h_v257 : R 1 0 4611686018427387904 4611686052787126264 v257 v257 := (r_add hl (r_pshr1 hl (r_add hl h_v2 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v257 : sv v257 = (sv v2 + 1) / 2 := e_halfC h_v2 (of_decide_eq_true rfl)
  have h_v258 : R 1 0 0 1 v258 v258 := (r_plt hl h_v9 h_v257 (of_decide_eq_true rfl))
  have e_v258 : (v258 = 1 ↔ sv v9 < sv v257) := e_plt h_v9 h_v257 (of_decide_eq_true rfl)
  have h_v259 : R 1 0 0 1 v259 v259 := (r_sub hl (r_O hl) h_v258 (of_decide_eq_true rfl))
  have e_v259 : (v259 = 1 ↔ ¬v258 = 1) := e_not h_v258 (of_decide_eq_true rfl)
  have h_v260 : R 1 0 0 1 v260 v260 := (r_land hl h_v44 h_v259 (of_decide_eq_true rfl))
  have e_v260 : (v260 = 1 ↔ v44 = 1 ∧ v259 = 1) := e_land h_v44 h_v259 (of_decide_eq_true rfl)
  have h_t257_1 : R 1 0 4611686018427387904 4611686018695823363 t257.1 t257.1 := r_sc1 hl h_v257 (of_decide_eq_true rfl)
  have h_t257_2 : R 1 0 4611686018158952445 4611686018695823363 t257.2 t257.2 := r_sc2 hl h_v257 (of_decide_eq_true rfl)
  have e_t257_1 : sv t257.1 = (sc28pS (scArg v257)).1 := e_sc1 h_v257 (of_decide_eq_true rfl)
  have e_t257_2 : sv t257.2 = (sc28pS (scArg v257)).2 := e_sc2 h_v257 (of_decide_eq_true rfl)
  have h_v274 : R 1 0 0 1 v274 v274 := (r_plt hl h_t42_1 h_t257_1 (of_decide_eq_true rfl))
  clear h_v2 h_v44 h_v165 h_v166 h_v172 h_v207 h_v208 h_v209 h_v210 h_v211 h_v213 h_v258 h_v259 h_t257_2 e_t257_2
  have e_v274 : (v274 = 1 ↔ sv t42.1 < sv t257.1) := e_plt h_t42_1 h_t257_1 (of_decide_eq_true rfl)
  have h_v275 : R 1 0 4611686018427387904 4611686018695823363 v275 v275 := (r_psel hl h_v274 h_t42_1 h_t257_1 (of_decide_eq_true rfl))
  have e_v275 : v275 = if v274 = 1 then t42.1 else t257.1 := e_psel h_v274 h_t42_1 h_t257_1 (of_decide_eq_true rfl)
  have h_v276 : R 1 0 4611686018427387900 4611686018695823359 v276 v276 := (r_sub hl (r_add hl h_v28 h_v275 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v276 : sv v276 = sv v28 + sv v275 := e_add h_v28 h_v275 (of_decide_eq_true rfl)
  have h_v277 : R 1 0 4611686018427387904 4611686018695823363 v277 v277 := (r_psel hl h_v274 h_t257_1 h_t42_1 (of_decide_eq_true rfl))
  have e_v277 : v277 = if v274 = 1 then t257.1 else t42.1 := e_psel h_v274 h_t257_1 h_t42_1 (of_decide_eq_true rfl)
  have h_v278 : R 1 0 4611686018427387908 4611686018695823367 v278 v278 := (r_sub hl (r_add hl h_v31 h_v277 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v278 : sv v278 = sv v31 + sv v277 := e_add h_v31 h_v277 (of_decide_eq_true rfl)
  have h_v279 : R 1 0 0 1 v279 v279 := (r_plt hl h_v278 h_v33 (of_decide_eq_true rfl))
  have e_v279 : (v279 = 1 ↔ sv v278 < sv v33) := e_plt h_v278 h_v33 (of_decide_eq_true rfl)
  have h_v280 : R 1 0 4611686018427387908 4611686018695823367 v280 v280 := (r_psel hl h_v279 h_v278 h_v33 (of_decide_eq_true rfl))
  have e_v280 : v280 = if v279 = 1 then v278 else v33 := e_psel h_v279 h_v278 h_v33 (of_decide_eq_true rfl)
  have h_v281 : R 1 0 0 1 v281 v281 := (r_plt hl h_v38 h_v257 (of_decide_eq_true rfl))
  have e_v281 : (v281 = 1 ↔ sv v38 < sv v257) := e_plt h_v38 h_v257 (of_decide_eq_true rfl)
  have h_v282 : R 1 0 0 1 v282 v282 := (r_land hl h_v57 h_v281 (of_decide_eq_true rfl))
  have e_v282 : (v282 = 1 ↔ v57 = 1 ∧ v281 = 1) := e_land h_v57 h_v281 (of_decide_eq_true rfl)
  have h_v283 : R 1 0 4611686018427387908 4611686018695823367 v283 v283 := (r_psel hl h_v282 h_v33 h_v280 (of_decide_eq_true rfl))
  have e_v283 : v283 = if v282 = 1 then v33 else v280 := e_psel h_v282 h_v33 h_v280 (of_decide_eq_true rfl)
  have h_v284 : R 1 0 0 1 v284 v284 := (r_plt hl h_v276 h_v61 (of_decide_eq_true rfl))
  have e_v284 : (v284 = 1 ↔ sv v276 < sv v61) := e_plt h_v276 h_v61 (of_decide_eq_true rfl)
  have h_v286 : R 1 0 0 1 v286 v286 := (r_plt hl h_v61 h_v283 (of_decide_eq_true rfl))
  have e_v286 : (v286 = 1 ↔ sv v61 < sv v283) := e_plt h_v61 h_v283 (of_decide_eq_true rfl)
  have h_v289 : R 1 0 0 1 v289 v289 := (r_land hl h_v284 h_v286 (of_decide_eq_true rfl))
  have e_v289 : (v289 = 1 ↔ v284 = 1 ∧ v286 = 1) := e_land h_v284 h_v286 (of_decide_eq_true rfl)
  clear h_t42_1 h_v57 h_v257 h_t257_1 h_v274 h_v275 h_v276 h_v277 h_v278 h_v279 h_v280 h_v281 h_v282 h_v283 h_v284 h_v286
  have h_v290 : R 1 0 0 1 v290 v290 := (r_land hl h_v139 h_v289 (of_decide_eq_true rfl))
  have e_v290 : (v290 = 1 ↔ v139 = 1 ∧ v289 = 1) := e_land h_v139 h_v289 (of_decide_eq_true rfl)
  have h_v291 : R 1 0 0 1 v291 v291 := (r_sub hl (r_O hl) h_v290 (of_decide_eq_true rfl))
  have e_v291 : (v291 = 1 ↔ ¬v290 = 1) := e_not h_v290 (of_decide_eq_true rfl)
  have h_v398 : R 1 0 4611686018427387904 4611686052787126264 v398 v398 := (r_add hl (r_pshr1 hl h_v4) h_H61r (of_decide_eq_true rfl))
  have e_v398 : sv v398 = sv v4 / 2 := e_halfF h_v4
  have h_v399 : R 1 0 4611686018427387904 4611686052787126264 v399 v399 := (r_add hl (r_pshr1 hl (r_add hl h_v5 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v399 : sv v399 = (sv v5 + 1) / 2 := e_halfC h_v5 (of_decide_eq_true rfl)
  have h_v400 : R 1 0 0 1 v400 v400 := (r_plt hl h_v19 h_v398 (of_decide_eq_true rfl))
  have e_v400 : (v400 = 1 ↔ sv v19 < sv v398) := e_plt h_v19 h_v398 (of_decide_eq_true rfl)
  have h_v401 : R 1 0 0 1 v401 v401 := (r_plt hl h_v9 h_v399 (of_decide_eq_true rfl))
  have e_v401 : (v401 = 1 ↔ sv v9 < sv v399) := e_plt h_v9 h_v399 (of_decide_eq_true rfl)
  have h_v402 : R 1 0 0 1 v402 v402 := (r_sub hl (r_O hl) h_v401 (of_decide_eq_true rfl))
  have e_v402 : (v402 = 1 ↔ ¬v401 = 1) := e_not h_v401 (of_decide_eq_true rfl)
  have h_v403 : R 1 0 0 1 v403 v403 := (r_land hl h_v400 h_v402 (of_decide_eq_true rfl))
  have e_v403 : (v403 = 1 ↔ v400 = 1 ∧ v402 = 1) := e_land h_v400 h_v402 (of_decide_eq_true rfl)
  have h_t398_1 : R 1 0 4611686018427387904 4611686018695823363 t398.1 t398.1 := r_sc1 hl h_v398 (of_decide_eq_true rfl)
  have h_t398_2 : R 1 0 4611686018158952445 4611686018695823363 t398.2 t398.2 := r_sc2 hl h_v398 (of_decide_eq_true rfl)
  have e_t398_1 : sv t398.1 = (sc28pS (scArg v398)).1 := e_sc1 h_v398 (of_decide_eq_true rfl)
  have e_t398_2 : sv t398.2 = (sc28pS (scArg v398)).2 := e_sc2 h_v398 (of_decide_eq_true rfl)
  have h_t399_1 : R 1 0 4611686018427387904 4611686018695823363 t399.1 t399.1 := r_sc1 hl h_v399 (of_decide_eq_true rfl)
  have h_t399_2 : R 1 0 4611686018158952445 4611686018695823363 t399.2 t399.2 := r_sc2 hl h_v399 (of_decide_eq_true rfl)
  have e_t399_1 : sv t399.1 = (sc28pS (scArg v399)).1 := e_sc1 h_v399 (of_decide_eq_true rfl)
  have e_t399_2 : sv t399.2 = (sc28pS (scArg v399)).2 := e_sc2 h_v399 (of_decide_eq_true rfl)
  have h_v406 : R 1 0 0 1 v406 v406 := (r_plt hl h_t398_1 h_t399_1 (of_decide_eq_true rfl))
  clear h_v289 h_v290 h_v401 h_t398_2 e_t398_2
  have e_v406 : (v406 = 1 ↔ sv t398.1 < sv t399.1) := e_plt h_t398_1 h_t399_1 (of_decide_eq_true rfl)
  have h_v407 : R 1 0 4611686018427387904 4611686018695823363 v407 v407 := (r_psel hl h_v406 h_t398_1 h_t399_1 (of_decide_eq_true rfl))
  have e_v407 : v407 = if v406 = 1 then t398.1 else t399.1 := e_psel h_v406 h_t398_1 h_t399_1 (of_decide_eq_true rfl)
  have h_v408 : R 1 0 4611686018427387900 4611686018695823359 v408 v408 := (r_sub hl (r_add hl h_v28 h_v407 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v408 : sv v408 = sv v28 + sv v407 := e_add h_v28 h_v407 (of_decide_eq_true rfl)
  have h_v409 : R 1 0 4611686018427387904 4611686018695823363 v409 v409 := (r_psel hl h_v406 h_t399_1 h_t398_1 (of_decide_eq_true rfl))
  have e_v409 : v409 = if v406 = 1 then t399.1 else t398.1 := e_psel h_v406 h_t399_1 h_t398_1 (of_decide_eq_true rfl)
  have h_v410 : R 1 0 4611686018427387908 4611686018695823367 v410 v410 := (r_sub hl (r_add hl h_v31 h_v409 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v410 : sv v410 = sv v31 + sv v409 := e_add h_v31 h_v409 (of_decide_eq_true rfl)
  have h_v411 : R 1 0 0 1 v411 v411 := (r_plt hl h_v410 h_v33 (of_decide_eq_true rfl))
  have e_v411 : (v411 = 1 ↔ sv v410 < sv v33) := e_plt h_v410 h_v33 (of_decide_eq_true rfl)
  have h_v412 : R 1 0 4611686018427387908 4611686018695823367 v412 v412 := (r_psel hl h_v411 h_v410 h_v33 (of_decide_eq_true rfl))
  have e_v412 : v412 = if v411 = 1 then v410 else v33 := e_psel h_v411 h_v410 h_v33 (of_decide_eq_true rfl)
  have h_v413 : R 1 0 0 1 v413 v413 := (r_plt hl h_v398 h_v36 (of_decide_eq_true rfl))
  have e_v413 : (v413 = 1 ↔ sv v398 < sv v36) := e_plt h_v398 h_v36 (of_decide_eq_true rfl)
  have h_v414 : R 1 0 0 1 v414 v414 := (r_plt hl h_v38 h_v399 (of_decide_eq_true rfl))
  have e_v414 : (v414 = 1 ↔ sv v38 < sv v399) := e_plt h_v38 h_v399 (of_decide_eq_true rfl)
  have h_v415 : R 1 0 0 1 v415 v415 := (r_land hl h_v413 h_v414 (of_decide_eq_true rfl))
  have e_v415 : (v415 = 1 ↔ v413 = 1 ∧ v414 = 1) := e_land h_v413 h_v414 (of_decide_eq_true rfl)
  have h_v416 : R 1 0 4611686018427387908 4611686018695823367 v416 v416 := (r_psel hl h_v415 h_v33 h_v412 (of_decide_eq_true rfl))
  have e_v416 : v416 = if v415 = 1 then v33 else v412 := e_psel h_v415 h_v33 h_v412 (of_decide_eq_true rfl)
  have h_v417 : R 1 0 0 1 v417 v417 := (r_plt hl h_v408 h_v61 (of_decide_eq_true rfl))
  have e_v417 : (v417 = 1 ↔ sv v408 < sv v61) := e_plt h_v408 h_v61 (of_decide_eq_true rfl)
  have h_v418 : R 1 0 0 1 v418 v418 := (r_sub hl (r_O hl) h_v417 (of_decide_eq_true rfl))
  have e_v418 : (v418 = 1 ↔ ¬v417 = 1) := e_not h_v417 (of_decide_eq_true rfl)
  clear h_v398 h_v406 h_v407 h_v409 h_v410 h_v411 h_v412 h_v415
  have h_v419 : R 1 0 0 1 v419 v419 := (r_plt hl h_v61 h_v416 (of_decide_eq_true rfl))
  have e_v419 : (v419 = 1 ↔ sv v61 < sv v416) := e_plt h_v61 h_v416 (of_decide_eq_true rfl)
  have h_v420 : R 1 0 0 1 v420 v420 := (r_sub hl (r_O hl) h_v419 (of_decide_eq_true rfl))
  have e_v420 : (v420 = 1 ↔ ¬v419 = 1) := e_not h_v419 (of_decide_eq_true rfl)
  have h_v421 : R 1 0 0 1 v421 v421 := (r_land hl h_v417 h_v420 (of_decide_eq_true rfl))
  have e_v421 : (v421 = 1 ↔ v417 = 1 ∧ v420 = 1) := e_land h_v417 h_v420 (of_decide_eq_true rfl)
  have h_v422 : R 1 0 0 1 v422 v422 := (r_land hl h_v417 h_v419 (of_decide_eq_true rfl))
  have e_v422 : (v422 = 1 ↔ v417 = 1 ∧ v419 = 1) := e_land h_v417 h_v419 (of_decide_eq_true rfl)
  have h_v423 : R 1 0 0 1 v423 v423 := (r_land hl h_v67 h_v422 (of_decide_eq_true rfl))
  have e_v423 : (v423 = 1 ↔ v67 = 1 ∧ v422 = 1) := e_land h_v67 h_v422 (of_decide_eq_true rfl)
  have h_v424 : R 1 0 0 1 v424 v424 := (r_sub hl (r_O hl) h_v423 (of_decide_eq_true rfl))
  have e_v424 : (v424 = 1 ↔ ¬v423 = 1) := e_not h_v423 (of_decide_eq_true rfl)
  have h_v425 : R 1 0 0 1 v425 v425 := (r_land hl h_v63 h_v422 (of_decide_eq_true rfl))
  have e_v425 : (v425 = 1 ↔ v63 = 1 ∧ v422 = 1) := e_land h_v63 h_v422 (of_decide_eq_true rfl)
  have h_v426 : R 1 0 0 1 v426 v426 := (r_lor hl h_v421 h_v425 (of_decide_eq_true rfl))
  have e_v426 : (v426 = 1 ↔ v421 = 1 ∨ v425 = 1) := e_lor h_v421 h_v425 (of_decide_eq_true rfl)
  have h_v427 : R 1 0 4611686018427387900 4611686018695823367 v427 v427 := (r_psel hl h_v426 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v427 : v427 = if v426 = 1 then v41 else v29 := e_psel h_v426 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v428 : R 1 0 0 1 v428 v428 := (r_land hl h_v67 h_v418 (of_decide_eq_true rfl))
  have e_v428 : (v428 = 1 ↔ v67 = 1 ∧ v418 = 1) := e_land h_v67 h_v418 (of_decide_eq_true rfl)
  have h_v429 : R 1 0 0 1 v429 v429 := (r_lor hl h_v66 h_v428 (of_decide_eq_true rfl))
  have e_v429 : (v429 = 1 ↔ v66 = 1 ∨ v428 = 1) := e_lor h_v66 h_v428 (of_decide_eq_true rfl)
  have h_v430 : R 1 0 4611686018427387900 4611686018695823367 v430 v430 := (r_psel hl h_v429 h_v416 h_v408 (of_decide_eq_true rfl))
  have e_v430 : v430 = if v429 = 1 then v416 else v408 := e_psel h_v429 h_v416 h_v408 (of_decide_eq_true rfl)
  have h_v431 : R 1 0 0 1 v431 v431 := (r_land hl h_v66 h_v422 (of_decide_eq_true rfl))
  clear h_v417 h_v418 h_v419 h_v420 h_v423 h_v425 h_v426 h_v428 h_v429
  have e_v431 : (v431 = 1 ↔ v66 = 1 ∧ v422 = 1) := e_land h_v66 h_v422 (of_decide_eq_true rfl)
  have h_v432 : R 1 0 0 1 v432 v432 := (r_lor hl h_v421 h_v431 (of_decide_eq_true rfl))
  have e_v432 : (v432 = 1 ↔ v421 = 1 ∨ v431 = 1) := e_lor h_v421 h_v431 (of_decide_eq_true rfl)
  have h_v433 : R 1 0 4611686018427387900 4611686018695823367 v433 v433 := (r_psel hl h_v432 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v433 : v433 = if v432 = 1 then v29 else v41 := e_psel h_v432 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v434 : R 1 0 0 1 v434 v434 := (r_land hl h_v67 h_v421 (of_decide_eq_true rfl))
  have e_v434 : (v434 = 1 ↔ v67 = 1 ∧ v421 = 1) := e_land h_v67 h_v421 (of_decide_eq_true rfl)
  have h_v435 : R 1 0 0 1 v435 v435 := (r_lor hl h_v66 h_v434 (of_decide_eq_true rfl))
  have e_v435 : (v435 = 1 ↔ v66 = 1 ∨ v434 = 1) := e_lor h_v66 h_v434 (of_decide_eq_true rfl)
  have h_v436 : R 1 0 4611686018427387900 4611686018695823367 v436 v436 := (r_psel hl h_v435 h_v408 h_v416 (of_decide_eq_true rfl))
  have e_v436 : v436 = if v435 = 1 then v408 else v416 := e_psel h_v435 h_v408 h_v416 (of_decide_eq_true rfl)
  have h_v437 : R 1 0 4611686017353646052 4683743616223412273 v437 v437 := (r_smx hl 29 h_v430 h_v427 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v437 : sv v437 = sv v430 * sv v427 := e_smx 29 h_v430 h_v427 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v438 : R 1 0 4611686018427387899 4611686018695823374 v438 v438 := (r_srdF hl h_v437 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v438 : sv v438 = sv v437 / 2 ^ 28 := e_srdF h_v437 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v439 : R 1 0 4611686017353646052 4683743616223412273 v439 v439 := (r_smx hl 29 h_v436 h_v433 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v439 : sv v439 = sv v436 * sv v433 := e_smx 29 h_v436 h_v433 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v440 : R 1 0 4611686018427387900 4611686018695823375 v440 v440 := (r_srdC hl h_v439 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v440 : sv v440 = -((-sv v439) / 2 ^ 28) := e_srdC h_v439 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v441 : R 1 0 0 1 v441 v441 := (r_plt hl h_v19 h_v438 (of_decide_eq_true rfl))
  have e_v441 : (v441 = 1 ↔ sv v19 < sv v438) := e_plt h_v19 h_v438 (of_decide_eq_true rfl)
  have h_v442 : R 1 0 4611686018427387904 4611686052787126264 v442 v442 := (r_add hl (r_pshr1 hl h_v5) h_H61r (of_decide_eq_true rfl))
  have e_v442 : sv v442 = sv v5 / 2 := e_halfF h_v5
  have h_v443 : R 1 0 0 1 v443 v443 := (r_plt hl h_v19 h_v442 (of_decide_eq_true rfl))
  have e_v443 : (v443 = 1 ↔ sv v19 < sv v442) := e_plt h_v19 h_v442 (of_decide_eq_true rfl)
  clear h_v5 h_v408 h_v416 h_v421 h_v422 h_v427 h_v430 h_v431 h_v432 h_v433 h_v434 h_v435 h_v436 h_v437 h_v439
  have h_v444 : R 1 0 0 1 v444 v444 := (r_land hl h_v402 h_v443 (of_decide_eq_true rfl))
  have e_v444 : (v444 = 1 ↔ v402 = 1 ∧ v443 = 1) := e_land h_v402 h_v443 (of_decide_eq_true rfl)
  have h_v446 : R 1 0 4611686018158952441 4611686018695823359 v446 v446 := (r_sub hl (r_add hl h_v28 h_t399_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v446 : sv v446 = sv v28 + sv t399.2 := e_add h_v28 h_t399_2 (of_decide_eq_true rfl)
  have h_v447 : R 1 0 0 1 v447 v447 := (r_plt hl h_v446 h_v95 (of_decide_eq_true rfl))
  have e_v447 : (v447 = 1 ↔ sv v446 < sv v95) := e_plt h_v446 h_v95 (of_decide_eq_true rfl)
  have h_v448 : R 1 0 4611686018158952441 4611686018695823359 v448 v448 := (r_psel hl h_v447 h_v95 h_v446 (of_decide_eq_true rfl))
  have e_v448 : v448 = if v447 = 1 then v95 else v446 := e_psel h_v447 h_v95 h_v446 (of_decide_eq_true rfl)
  have h_v449 : R 1 0 0 1 v449 v449 := (r_plt hl h_v98 h_v399 (of_decide_eq_true rfl))
  have e_v449 : (v449 = 1 ↔ sv v98 < sv v399) := e_plt h_v98 h_v399 (of_decide_eq_true rfl)
  have h_v450 : R 1 0 4611686018158952441 4611686018695823359 v450 v450 := (r_psel hl h_v449 h_v95 h_v448 (of_decide_eq_true rfl))
  have e_v450 : v450 = if v449 = 1 then v95 else v448 := e_psel h_v449 h_v95 h_v448 (of_decide_eq_true rfl)
  have h_t442_1 : R 1 0 4611686018427387904 4611686018695823363 t442.1 t442.1 := r_sc1 hl h_v442 (of_decide_eq_true rfl)
  have h_t442_2 : R 1 0 4611686018158952445 4611686018695823363 t442.2 t442.2 := r_sc2 hl h_v442 (of_decide_eq_true rfl)
  have e_t442_1 : sv t442.1 = (sc28pS (scArg v442)).1 := e_sc1 h_v442 (of_decide_eq_true rfl)
  have e_t442_2 : sv t442.2 = (sc28pS (scArg v442)).2 := e_sc2 h_v442 (of_decide_eq_true rfl)
  have h_v458 : R 1 0 0 1 v458 v458 := (r_plt hl h_t442_1 h_t399_1 (of_decide_eq_true rfl))
  have e_v458 : (v458 = 1 ↔ sv t442.1 < sv t399.1) := e_plt h_t442_1 h_t399_1 (of_decide_eq_true rfl)
  have h_v459 : R 1 0 4611686018427387904 4611686018695823363 v459 v459 := (r_psel hl h_v458 h_t442_1 h_t399_1 (of_decide_eq_true rfl))
  have e_v459 : v459 = if v458 = 1 then t442.1 else t399.1 := e_psel h_v458 h_t442_1 h_t399_1 (of_decide_eq_true rfl)
  have h_v460 : R 1 0 4611686018427387900 4611686018695823359 v460 v460 := (r_sub hl (r_add hl h_v28 h_v459 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v460 : sv v460 = sv v28 + sv v459 := e_add h_v28 h_v459 (of_decide_eq_true rfl)
  have h_v461 : R 1 0 4611686018427387904 4611686018695823363 v461 v461 := (r_psel hl h_v458 h_t399_1 h_t442_1 (of_decide_eq_true rfl))
  have e_v461 : v461 = if v458 = 1 then t399.1 else t442.1 := e_psel h_v458 h_t399_1 h_t442_1 (of_decide_eq_true rfl)
  have h_v462 : R 1 0 4611686018427387908 4611686018695823367 v462 v462 := (r_sub hl (r_add hl h_v31 h_v461 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v98 h_v399 h_v402 h_t399_1 h_t399_2 h_v443 h_v446 h_v447 h_v448 h_v449 h_t442_1 h_t442_2 e_t442_2 h_v458 h_v459
  have e_v462 : sv v462 = sv v31 + sv v461 := e_add h_v31 h_v461 (of_decide_eq_true rfl)
  have h_v463 : R 1 0 0 1 v463 v463 := (r_plt hl h_v462 h_v33 (of_decide_eq_true rfl))
  have e_v463 : (v463 = 1 ↔ sv v462 < sv v33) := e_plt h_v462 h_v33 (of_decide_eq_true rfl)
  have h_v464 : R 1 0 4611686018427387908 4611686018695823367 v464 v464 := (r_psel hl h_v463 h_v462 h_v33 (of_decide_eq_true rfl))
  have e_v464 : v464 = if v463 = 1 then v462 else v33 := e_psel h_v463 h_v462 h_v33 (of_decide_eq_true rfl)
  have h_v465 : R 1 0 0 1 v465 v465 := (r_plt hl h_v442 h_v36 (of_decide_eq_true rfl))
  have e_v465 : (v465 = 1 ↔ sv v442 < sv v36) := e_plt h_v442 h_v36 (of_decide_eq_true rfl)
  have h_v466 : R 1 0 0 1 v466 v466 := (r_land hl h_v414 h_v465 (of_decide_eq_true rfl))
  have e_v466 : (v466 = 1 ↔ v414 = 1 ∧ v465 = 1) := e_land h_v414 h_v465 (of_decide_eq_true rfl)
  have h_v467 : R 1 0 4611686018427387908 4611686018695823367 v467 v467 := (r_psel hl h_v466 h_v33 h_v464 (of_decide_eq_true rfl))
  have e_v467 : v467 = if v466 = 1 then v33 else v464 := e_psel h_v466 h_v33 h_v464 (of_decide_eq_true rfl)
  have h_v468 : R 1 0 0 1 v468 v468 := (r_plt hl h_v460 h_v61 (of_decide_eq_true rfl))
  have e_v468 : (v468 = 1 ↔ sv v460 < sv v61) := e_plt h_v460 h_v61 (of_decide_eq_true rfl)
  have h_v469 : R 1 0 0 1 v469 v469 := (r_sub hl (r_O hl) h_v468 (of_decide_eq_true rfl))
  have e_v469 : (v469 = 1 ↔ ¬v468 = 1) := e_not h_v468 (of_decide_eq_true rfl)
  have h_v470 : R 1 0 0 1 v470 v470 := (r_plt hl h_v61 h_v467 (of_decide_eq_true rfl))
  have e_v470 : (v470 = 1 ↔ sv v61 < sv v467) := e_plt h_v61 h_v467 (of_decide_eq_true rfl)
  have h_v471 : R 1 0 0 1 v471 v471 := (r_sub hl (r_O hl) h_v470 (of_decide_eq_true rfl))
  have e_v471 : (v471 = 1 ↔ ¬v470 = 1) := e_not h_v470 (of_decide_eq_true rfl)
  have h_v472 : R 1 0 0 1 v472 v472 := (r_land hl h_v468 h_v471 (of_decide_eq_true rfl))
  have e_v472 : (v472 = 1 ↔ v468 = 1 ∧ v471 = 1) := e_land h_v468 h_v471 (of_decide_eq_true rfl)
  have h_v473 : R 1 0 0 1 v473 v473 := (r_land hl h_v468 h_v470 (of_decide_eq_true rfl))
  have e_v473 : (v473 = 1 ↔ v468 = 1 ∧ v470 = 1) := e_land h_v468 h_v470 (of_decide_eq_true rfl)
  have h_v474 : R 1 0 0 1 v474 v474 := (r_land hl h_v139 h_v473 (of_decide_eq_true rfl))
  have e_v474 : (v474 = 1 ↔ v139 = 1 ∧ v473 = 1) := e_land h_v139 h_v473 (of_decide_eq_true rfl)
  clear h_v414 h_v442 h_v461 h_v462 h_v463 h_v464 h_v465 h_v466 h_v468 h_v470 h_v471
  have h_v475 : R 1 0 0 1 v475 v475 := (r_sub hl (r_O hl) h_v474 (of_decide_eq_true rfl))
  have e_v475 : (v475 = 1 ↔ ¬v474 = 1) := e_not h_v474 (of_decide_eq_true rfl)
  have h_v476 : R 1 0 0 1 v476 v476 := (r_land hl h_v135 h_v473 (of_decide_eq_true rfl))
  have e_v476 : (v476 = 1 ↔ v135 = 1 ∧ v473 = 1) := e_land h_v135 h_v473 (of_decide_eq_true rfl)
  have h_v477 : R 1 0 0 1 v477 v477 := (r_lor hl h_v472 h_v476 (of_decide_eq_true rfl))
  have e_v477 : (v477 = 1 ↔ v472 = 1 ∨ v476 = 1) := e_lor h_v472 h_v476 (of_decide_eq_true rfl)
  have h_v478 : R 1 0 4611686018158952441 4611686018695823367 v478 v478 := (r_psel hl h_v477 h_v107 h_v100 (of_decide_eq_true rfl))
  have e_v478 : v478 = if v477 = 1 then v107 else v100 := e_psel h_v477 h_v107 h_v100 (of_decide_eq_true rfl)
  have h_v479 : R 1 0 0 1 v479 v479 := (r_land hl h_v139 h_v469 (of_decide_eq_true rfl))
  have e_v479 : (v479 = 1 ↔ v139 = 1 ∧ v469 = 1) := e_land h_v139 h_v469 (of_decide_eq_true rfl)
  have h_v480 : R 1 0 0 1 v480 v480 := (r_lor hl h_v138 h_v479 (of_decide_eq_true rfl))
  have e_v480 : (v480 = 1 ↔ v138 = 1 ∨ v479 = 1) := e_lor h_v138 h_v479 (of_decide_eq_true rfl)
  have h_v481 : R 1 0 4611686018427387900 4611686018695823367 v481 v481 := (r_psel hl h_v480 h_v467 h_v460 (of_decide_eq_true rfl))
  have e_v481 : v481 = if v480 = 1 then v467 else v460 := e_psel h_v480 h_v467 h_v460 (of_decide_eq_true rfl)
  have h_v482 : R 1 0 0 1 v482 v482 := (r_land hl h_v138 h_v473 (of_decide_eq_true rfl))
  have e_v482 : (v482 = 1 ↔ v138 = 1 ∧ v473 = 1) := e_land h_v138 h_v473 (of_decide_eq_true rfl)
  have h_v483 : R 1 0 0 1 v483 v483 := (r_lor hl h_v472 h_v482 (of_decide_eq_true rfl))
  have e_v483 : (v483 = 1 ↔ v472 = 1 ∨ v482 = 1) := e_lor h_v472 h_v482 (of_decide_eq_true rfl)
  have h_v484 : R 1 0 4611686018158952441 4611686018695823367 v484 v484 := (r_psel hl h_v483 h_v100 h_v107 (of_decide_eq_true rfl))
  have e_v484 : v484 = if v483 = 1 then v100 else v107 := e_psel h_v483 h_v100 h_v107 (of_decide_eq_true rfl)
  have h_v485 : R 1 0 0 1 v485 v485 := (r_land hl h_v139 h_v472 (of_decide_eq_true rfl))
  have e_v485 : (v485 = 1 ↔ v139 = 1 ∧ v472 = 1) := e_land h_v139 h_v472 (of_decide_eq_true rfl)
  have h_v486 : R 1 0 0 1 v486 v486 := (r_lor hl h_v138 h_v485 (of_decide_eq_true rfl))
  have e_v486 : (v486 = 1 ↔ v138 = 1 ∨ v485 = 1) := e_lor h_v138 h_v485 (of_decide_eq_true rfl)
  have h_v487 : R 1 0 4611686018427387900 4611686018695823367 v487 v487 := (r_psel hl h_v486 h_v460 h_v467 (of_decide_eq_true rfl))
  clear h_v100 h_v107 h_v135 h_v138 h_v469 h_v472 h_v473 h_v474 h_v476 h_v477 h_v479 h_v480 h_v482 h_v483 h_v485
  have e_v487 : v487 = if v486 = 1 then v460 else v467 := e_psel h_v486 h_v460 h_v467 (of_decide_eq_true rfl)
  have h_v488 : R 1 0 4539628420631363535 4683743616223412273 v488 v488 := (r_smx hl 29 h_v481 h_v478 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v488 : sv v488 = sv v481 * sv v478 := e_smx 29 h_v481 h_v478 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v489 : R 1 0 4611686018158952433 4611686018695823374 v489 v489 := (r_srdF hl h_v488 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v489 : sv v489 = sv v488 / 2 ^ 28 := e_srdF h_v488 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v490 : R 1 0 4539628420631363535 4683743616223412273 v490 v490 := (r_smx hl 29 h_v487 h_v484 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v490 : sv v490 = sv v487 * sv v484 := e_smx 29 h_v487 h_v484 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v491 : R 1 0 4611686018158952434 4611686018695823375 v491 v491 := (r_srdC hl h_v490 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v491 : sv v491 = -((-sv v490) / 2 ^ 28) := e_srdC h_v490 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v492 : R 1 0 0 1 v492 v492 := (r_plt hl h_v61 h_v489 (of_decide_eq_true rfl))
  have e_v492 : (v492 = 1 ↔ sv v61 < sv v489) := e_plt h_v61 h_v489 (of_decide_eq_true rfl)
  have h_v493 : R 1 0 0 1 v493 v493 := (r_sub hl (r_O hl) h_v492 (of_decide_eq_true rfl))
  have e_v493 : (v493 = 1 ↔ ¬v492 = 1) := e_not h_v492 (of_decide_eq_true rfl)
  have h_v494 : R 1 0 0 1 v494 v494 := (r_plt hl h_v450 h_v61 (of_decide_eq_true rfl))
  have e_v494 : (v494 = 1 ↔ sv v450 < sv v61) := e_plt h_v450 h_v61 (of_decide_eq_true rfl)
  have h_v495 : R 1 0 4611686018158952433 4611686018695823375 v495 v495 := (r_psel hl h_v494 h_v489 h_v491 (of_decide_eq_true rfl))
  have e_v495 : v495 = if v494 = 1 then v489 else v491 := e_psel h_v494 h_v489 h_v491 (of_decide_eq_true rfl)
  have h_v498 : R 1 0 4611686018158952449 4611686018695823367 v498 v498 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v450 (of_decide_eq_true rfl))
  have e_v498 : sv v498 = sv v61 - sv v450 := e_sub h_v61 h_v450 (of_decide_eq_true rfl)
  have h_v499 : R 1 0 4611686018158952441 4611686018695823367 v499 v499 := (r_psel hl h_v494 h_v498 h_v450 (of_decide_eq_true rfl))
  have e_v499 : v499 = if v494 = 1 then v498 else v450 := e_psel h_v494 h_v498 h_v450 (of_decide_eq_true rfl)
  have h_v500 : R 1 0 4611686018427387904 4611686019501129727 v500 v500 := (r1_hxa hb_H0 32 (of_decide_eq_true rfl))
  have e_v500 : sv v500 = ((H0 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 32 (of_decide_eq_true rfl)
  have h_v501 : R 1 0 0 1 v501 v501 := (r_sub hl (r_O hl) h_v494 (of_decide_eq_true rfl))
  have e_v501 : (v501 = 1 ↔ ¬v494 = 1) := e_not h_v494 (of_decide_eq_true rfl)
  clear h_v450 h_v460 h_v467 h_v478 h_v481 h_v484 h_v486 h_v487 h_v488 h_v489 h_v490 h_v491 h_v492 h_v498
  have h_t500_1 : R 1 0 4611686018427387904 4611686018695823363 t500.1 t500.1 := r_sc1 hl h_v500 (of_decide_eq_true rfl)
  have h_t500_2 : R 1 0 4611686018158952445 4611686018695823363 t500.2 t500.2 := r_sc2 hl h_v500 (of_decide_eq_true rfl)
  have e_t500_1 : sv t500.1 = (sc28pS (scArg v500)).1 := e_sc1 h_v500 (of_decide_eq_true rfl)
  have e_t500_2 : sv t500.2 = (sc28pS (scArg v500)).2 := e_sc2 h_v500 (of_decide_eq_true rfl)
  have h_v503 : R 1 0 4611686018158952441 4611686018695823359 v503 v503 := (r_sub hl (r_add hl h_v28 h_t500_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v503 : sv v503 = sv v28 + sv t500.2 := e_add h_v28 h_t500_2 (of_decide_eq_true rfl)
  have h_v504 : R 1 0 0 1 v504 v504 := (r_plt hl h_v503 h_v95 (of_decide_eq_true rfl))
  have e_v504 : (v504 = 1 ↔ sv v503 < sv v95) := e_plt h_v503 h_v95 (of_decide_eq_true rfl)
  have h_v505 : R 1 0 4611686018158952441 4611686018695823359 v505 v505 := (r_psel hl h_v504 h_v95 h_v503 (of_decide_eq_true rfl))
  have e_v505 : v505 = if v504 = 1 then v95 else v503 := e_psel h_v504 h_v95 h_v503 (of_decide_eq_true rfl)
  have h_v506 : R 1 0 4611686018158952449 4611686018695823367 v506 v506 := (r_sub hl (r_add hl h_v31 h_t500_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v506 : sv v506 = sv v31 + sv t500.2 := e_add h_v31 h_t500_2 (of_decide_eq_true rfl)
  have h_v507 : R 1 0 0 1 v507 v507 := (r_plt hl h_v506 h_v33 (of_decide_eq_true rfl))
  have e_v507 : (v507 = 1 ↔ sv v506 < sv v33) := e_plt h_v506 h_v33 (of_decide_eq_true rfl)
  have h_v508 : R 1 0 4611686018158952449 4611686018695823367 v508 v508 := (r_psel hl h_v507 h_v506 h_v33 (of_decide_eq_true rfl))
  have e_v508 : v508 = if v507 = 1 then v506 else v33 := e_psel h_v507 h_v506 h_v33 (of_decide_eq_true rfl)
  have h_v510 : R 1 0 4611686018427387908 4611686018695823367 v510 v510 := (r_sub hl (r_add hl h_v31 h_t500_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v510 : sv v510 = sv v31 + sv t500.1 := e_add h_v31 h_t500_1 (of_decide_eq_true rfl)
  have h_v511 : R 1 0 0 1 v511 v511 := (r_plt hl h_v510 h_v33 (of_decide_eq_true rfl))
  have e_v511 : (v511 = 1 ↔ sv v510 < sv v33) := e_plt h_v510 h_v33 (of_decide_eq_true rfl)
  have h_v512 : R 1 0 4611686018427387908 4611686018695823367 v512 v512 := (r_psel hl h_v511 h_v510 h_v33 (of_decide_eq_true rfl))
  have e_v512 : v512 = if v511 = 1 then v510 else v33 := e_psel h_v511 h_v510 h_v33 (of_decide_eq_true rfl)
  have h_v513 : R 1 0 4611686018427387900 4611686018695823359 v513 v513 := (r_sub hl (r_add hl h_v28 h_t500_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v513 : sv v513 = sv v28 + sv t500.1 := e_add h_v28 h_t500_1 (of_decide_eq_true rfl)
  have h_v514 : R 1 0 4611686018158952441 4611686018695823367 v514 v514 := (r_psel hl h_v501 h_v505 h_v508 (of_decide_eq_true rfl))
  clear h_t500_1 h_t500_2 h_v503 h_v504 h_v506 h_v507 h_v510 h_v511
  have e_v514 : v514 = if v501 = 1 then v505 else v508 := e_psel h_v501 h_v505 h_v508 (of_decide_eq_true rfl)
  have h_v515 : R 1 0 4611686018427387900 4611686018695823367 v515 v515 := (r_psel hl h_v501 h_v512 h_v513 (of_decide_eq_true rfl))
  have e_v515 : v515 = if v501 = 1 then v512 else v513 := e_psel h_v501 h_v512 h_v513 (of_decide_eq_true rfl)
  have h_v516 : R 1 0 4539628418483879831 4683743618370895977 v516 v516 := (r_smx hl 29 h_v495 h_v515 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v516 : sv v516 = sv v495 * sv v515 := e_smx 29 h_v495 h_v515 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v517 : R 1 0 4539628420631363535 4683743616223412273 v517 v517 := (r_smx hl 29 h_v514 h_v499 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v517 : sv v517 = sv v514 * sv v499 := e_smx 29 h_v514 h_v499 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v518 : R 1 0 0 1 v518 v518 := (r_plt hl h_v517 h_v516 (of_decide_eq_true rfl))
  have e_v518 : (v518 = 1 ↔ sv v517 < sv v516) := e_plt h_v517 h_v516 (of_decide_eq_true rfl)
  have h_v519 : R 1 0 0 1 v519 v519 := (r_sub hl (r_O hl) h_v518 (of_decide_eq_true rfl))
  have e_v519 : (v519 = 1 ↔ ¬v518 = 1) := e_not h_v518 (of_decide_eq_true rfl)
  have h_v520 : R 1 0 0 1 v520 v520 := (r_plt hl h_v516 h_v517 (of_decide_eq_true rfl))
  have e_v520 : (v520 = 1 ↔ sv v516 < sv v517) := e_plt h_v516 h_v517 (of_decide_eq_true rfl)
  have h_v521 : R 1 0 0 1 v521 v521 := (r_sub hl (r_O hl) h_v520 (of_decide_eq_true rfl))
  have e_v521 : (v521 = 1 ↔ ¬v520 = 1) := e_not h_v520 (of_decide_eq_true rfl)
  have h_v522 : R 1 0 0 1 v522 v522 := (r_plt hl h_v61 h_v500 (of_decide_eq_true rfl))
  have e_v522 : (v522 = 1 ↔ sv v61 < sv v500) := e_plt h_v61 h_v500 (of_decide_eq_true rfl)
  have h_v523 : R 1 0 0 1 v523 v523 := (r_sub hl (r_O hl) h_v522 (of_decide_eq_true rfl))
  have e_v523 : (v523 = 1 ↔ ¬v522 = 1) := e_not h_v522 (of_decide_eq_true rfl)
  have h_v524 : R 1 0 0 1 v524 v524 := (r_plt hl h_v196 h_v500 (of_decide_eq_true rfl))
  have e_v524 : (v524 = 1 ↔ sv v196 < sv v500) := e_plt h_v196 h_v500 (of_decide_eq_true rfl)
  have h_v525 : R 1 0 0 1 v525 v525 := (r_sub hl (r_O hl) h_v524 (of_decide_eq_true rfl))
  have e_v525 : (v525 = 1 ↔ ¬v524 = 1) := e_not h_v524 (of_decide_eq_true rfl)
  have h_v526 : R 1 0 0 1 v526 v526 := (r_plt hl h_v19 h_v505 (of_decide_eq_true rfl))
  have e_v526 : (v526 = 1 ↔ sv v19 < sv v505) := e_plt h_v19 h_v505 (of_decide_eq_true rfl)
  clear h_v196 h_v495 h_v499 h_v505 h_v508 h_v512 h_v513 h_v514 h_v515 h_v516 h_v517 h_v518 h_v520 h_v522 h_v524
  have h_v527 : R 1 0 0 1 v527 v527 := (r_land hl h_v519 h_v526 (of_decide_eq_true rfl))
  have e_v527 : (v527 = 1 ↔ v519 = 1 ∧ v526 = 1) := e_land h_v519 h_v526 (of_decide_eq_true rfl)
  have h_v528 : R 1 0 0 1 v528 v528 := (r_land hl h_v525 h_v527 (of_decide_eq_true rfl))
  have e_v528 : (v528 = 1 ↔ v525 = 1 ∧ v527 = 1) := e_land h_v525 h_v527 (of_decide_eq_true rfl)
  have h_v529 : R 1 0 0 1 v529 v529 := (r_lor hl h_v523 h_v528 (of_decide_eq_true rfl))
  have e_v529 : (v529 = 1 ↔ v523 = 1 ∨ v528 = 1) := e_lor h_v523 h_v528 (of_decide_eq_true rfl)
  have h_v530 : R 1 0 0 1 v530 v530 := (r_plt hl h_v500 h_v203 (of_decide_eq_true rfl))
  have e_v530 : (v530 = 1 ↔ sv v500 < sv v203) := e_plt h_v500 h_v203 (of_decide_eq_true rfl)
  have h_v531 : R 1 0 0 1 v531 v531 := (r_sub hl (r_O hl) h_v530 (of_decide_eq_true rfl))
  have e_v531 : (v531 = 1 ↔ ¬v530 = 1) := e_not h_v530 (of_decide_eq_true rfl)
  have h_v532 : R 1 0 0 1 v532 v532 := (r_lor hl h_v521 h_v531 (of_decide_eq_true rfl))
  have e_v532 : (v532 = 1 ↔ v521 = 1 ∨ v531 = 1) := e_lor h_v521 h_v531 (of_decide_eq_true rfl)
  have h_v533 : R 1 0 0 1 v533 v533 := (r_land hl h_v501 h_v529 (of_decide_eq_true rfl))
  have e_v533 : (v533 = 1 ↔ v501 = 1 ∧ v529 = 1) := e_land h_v501 h_v529 (of_decide_eq_true rfl)
  have h_v534 : R 1 0 0 1 v534 v534 := (r_land hl h_v494 h_v532 (of_decide_eq_true rfl))
  have e_v534 : (v534 = 1 ↔ v494 = 1 ∧ v532 = 1) := e_land h_v494 h_v532 (of_decide_eq_true rfl)
  have h_v535 : R 1 0 0 1 v535 v535 := (r_lor hl h_v533 h_v534 (of_decide_eq_true rfl))
  have e_v535 : (v535 = 1 ↔ v533 = 1 ∨ v534 = 1) := e_lor h_v533 h_v534 (of_decide_eq_true rfl)
  have h_v536 : R 1 0 4611686017353646081 4611686018427387904 v536 v536 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v500 (of_decide_eq_true rfl))
  have e_v536 : sv v536 = sv v61 - sv v500 := e_sub h_v61 h_v500 (of_decide_eq_true rfl)
  have h_v537 : R 1 0 4611686017353646081 4611686019501129727 v537 v537 := (r_psel hl h_v494 h_v536 h_v500 (of_decide_eq_true rfl))
  have e_v537 : v537 = if v494 = 1 then v536 else v500 := e_psel h_v494 h_v536 h_v500 (of_decide_eq_true rfl)
  have h_v538 : R 1 0 4611686017353646081 4611686019501129727 v538 v538 := (r_psel hl h_v535 h_v537 h_v212 (of_decide_eq_true rfl))
  have e_v538 : v538 = if v535 = 1 then v537 else v212 := e_psel h_v535 h_v537 h_v212 (of_decide_eq_true rfl)
  have h_v580 : R 1 0 4611686017353646081 4611686019501129727 v580 v580 := (r_psel hl h_v493 h_v212 h_v538 (of_decide_eq_true rfl))
  clear h_v494 h_v500 h_v501 h_v519 h_v521 h_v523 h_v525 h_v526 h_v527 h_v528 h_v529 h_v530 h_v531 h_v532 h_v533 h_v534 h_v535 h_v536 h_v537
  have e_v580 : v580 = if v493 = 1 then v212 else v538 := e_psel h_v493 h_v212 h_v538 (of_decide_eq_true rfl)
  have h_v582 : R 1 0 4611686018427387904 4611686052787126264 v582 v582 := (r_add hl (r_pshr1 hl (r_add hl h_v4 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v582 : sv v582 = (sv v4 + 1) / 2 := e_halfC h_v4 (of_decide_eq_true rfl)
  have h_v583 : R 1 0 0 1 v583 v583 := (r_plt hl h_v9 h_v582 (of_decide_eq_true rfl))
  have e_v583 : (v583 = 1 ↔ sv v9 < sv v582) := e_plt h_v9 h_v582 (of_decide_eq_true rfl)
  have h_v584 : R 1 0 0 1 v584 v584 := (r_sub hl (r_O hl) h_v583 (of_decide_eq_true rfl))
  have e_v584 : (v584 = 1 ↔ ¬v583 = 1) := e_not h_v583 (of_decide_eq_true rfl)
  have h_v585 : R 1 0 0 1 v585 v585 := (r_land hl h_v400 h_v584 (of_decide_eq_true rfl))
  have e_v585 : (v585 = 1 ↔ v400 = 1 ∧ v584 = 1) := e_land h_v400 h_v584 (of_decide_eq_true rfl)
  have h_t582_1 : R 1 0 4611686018427387904 4611686018695823363 t582.1 t582.1 := r_sc1 hl h_v582 (of_decide_eq_true rfl)
  have h_t582_2 : R 1 0 4611686018158952445 4611686018695823363 t582.2 t582.2 := r_sc2 hl h_v582 (of_decide_eq_true rfl)
  have e_t582_1 : sv t582.1 = (sc28pS (scArg v582)).1 := e_sc1 h_v582 (of_decide_eq_true rfl)
  have e_t582_2 : sv t582.2 = (sc28pS (scArg v582)).2 := e_sc2 h_v582 (of_decide_eq_true rfl)
  have h_v599 : R 1 0 0 1 v599 v599 := (r_plt hl h_t398_1 h_t582_1 (of_decide_eq_true rfl))
  have e_v599 : (v599 = 1 ↔ sv t398.1 < sv t582.1) := e_plt h_t398_1 h_t582_1 (of_decide_eq_true rfl)
  have h_v600 : R 1 0 4611686018427387904 4611686018695823363 v600 v600 := (r_psel hl h_v599 h_t398_1 h_t582_1 (of_decide_eq_true rfl))
  have e_v600 : v600 = if v599 = 1 then t398.1 else t582.1 := e_psel h_v599 h_t398_1 h_t582_1 (of_decide_eq_true rfl)
  have h_v601 : R 1 0 4611686018427387900 4611686018695823359 v601 v601 := (r_sub hl (r_add hl h_v28 h_v600 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v601 : sv v601 = sv v28 + sv v600 := e_add h_v28 h_v600 (of_decide_eq_true rfl)
  have h_v602 : R 1 0 4611686018427387904 4611686018695823363 v602 v602 := (r_psel hl h_v599 h_t582_1 h_t398_1 (of_decide_eq_true rfl))
  have e_v602 : v602 = if v599 = 1 then t582.1 else t398.1 := e_psel h_v599 h_t582_1 h_t398_1 (of_decide_eq_true rfl)
  have h_v603 : R 1 0 4611686018427387908 4611686018695823367 v603 v603 := (r_sub hl (r_add hl h_v31 h_v602 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v603 : sv v603 = sv v31 + sv v602 := e_add h_v31 h_v602 (of_decide_eq_true rfl)
  have h_v604 : R 1 0 0 1 v604 v604 := (r_plt hl h_v603 h_v33 (of_decide_eq_true rfl))
  have e_v604 : (v604 = 1 ↔ sv v603 < sv v33) := e_plt h_v603 h_v33 (of_decide_eq_true rfl)
  clear h_v4 h_v212 h_v400 h_t398_1 h_v493 h_v538 h_v583 h_v584 h_t582_1 h_t582_2 e_t582_2 h_v599 h_v600 h_v602
  have h_v605 : R 1 0 4611686018427387908 4611686018695823367 v605 v605 := (r_psel hl h_v604 h_v603 h_v33 (of_decide_eq_true rfl))
  have e_v605 : v605 = if v604 = 1 then v603 else v33 := e_psel h_v604 h_v603 h_v33 (of_decide_eq_true rfl)
  have h_v606 : R 1 0 0 1 v606 v606 := (r_plt hl h_v38 h_v582 (of_decide_eq_true rfl))
  have e_v606 : (v606 = 1 ↔ sv v38 < sv v582) := e_plt h_v38 h_v582 (of_decide_eq_true rfl)
  have h_v607 : R 1 0 0 1 v607 v607 := (r_land hl h_v413 h_v606 (of_decide_eq_true rfl))
  have e_v607 : (v607 = 1 ↔ v413 = 1 ∧ v606 = 1) := e_land h_v413 h_v606 (of_decide_eq_true rfl)
  have h_v608 : R 1 0 4611686018427387908 4611686018695823367 v608 v608 := (r_psel hl h_v607 h_v33 h_v605 (of_decide_eq_true rfl))
  have e_v608 : v608 = if v607 = 1 then v33 else v605 := e_psel h_v607 h_v33 h_v605 (of_decide_eq_true rfl)
  have h_v609 : R 1 0 0 1 v609 v609 := (r_plt hl h_v601 h_v61 (of_decide_eq_true rfl))
  have e_v609 : (v609 = 1 ↔ sv v601 < sv v61) := e_plt h_v601 h_v61 (of_decide_eq_true rfl)
  have h_v611 : R 1 0 0 1 v611 v611 := (r_plt hl h_v61 h_v608 (of_decide_eq_true rfl))
  have e_v611 : (v611 = 1 ↔ sv v61 < sv v608) := e_plt h_v61 h_v608 (of_decide_eq_true rfl)
  have h_v614 : R 1 0 0 1 v614 v614 := (r_land hl h_v609 h_v611 (of_decide_eq_true rfl))
  have e_v614 : (v614 = 1 ↔ v609 = 1 ∧ v611 = 1) := e_land h_v609 h_v611 (of_decide_eq_true rfl)
  have h_v615 : R 1 0 0 1 v615 v615 := (r_land hl h_v139 h_v614 (of_decide_eq_true rfl))
  have e_v615 : (v615 = 1 ↔ v139 = 1 ∧ v614 = 1) := e_land h_v139 h_v614 (of_decide_eq_true rfl)
  have h_v616 : R 1 0 0 1 v616 v616 := (r_sub hl (r_O hl) h_v615 (of_decide_eq_true rfl))
  have e_v616 : (v616 = 1 ↔ ¬v615 = 1) := e_not h_v615 (of_decide_eq_true rfl)
  have h_v723 : R 1 0 4611686018427387904 4611686052787126264 v723 v723 := (r_add hl (r_pshr1 hl h_v7) h_H61r (of_decide_eq_true rfl))
  have e_v723 : sv v723 = sv v7 / 2 := e_halfF h_v7
  have h_v724 : R 1 0 4611686018427387904 4611686052787126264 v724 v724 := (r_add hl (r_pshr1 hl (r_add hl h_v7 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v724 : sv v724 = (sv v7 + 1) / 2 := e_halfC h_v7 (of_decide_eq_true rfl)
  have h_v725 : R 1 0 4611686018427387904 4611686052787126264 v725 v725 := (r_psel hl h_v13 h_v724 h_v203 (of_decide_eq_true rfl))
  have e_v725 : v725 = if v13 = 1 then v724 else v203 := e_psel h_v13 h_v724 h_v203 (of_decide_eq_true rfl)
  have h_v726 : R 1 0 0 1 v726 v726 := (r_plt hl h_v19 h_v723 (of_decide_eq_true rfl))
  clear h_H61r h_v7 h_v13 h_v139 h_v203 h_v413 h_v582 h_v601 h_v603 h_v604 h_v605 h_v606 h_v607 h_v608 h_v609 h_v611 h_v614 h_v615 h_v724
  have e_v726 : (v726 = 1 ↔ sv v19 < sv v723) := e_plt h_v19 h_v723 (of_decide_eq_true rfl)
  have h_v727 : R 1 0 0 1 v727 v727 := (r_plt hl h_v9 h_v725 (of_decide_eq_true rfl))
  have e_v727 : (v727 = 1 ↔ sv v9 < sv v725) := e_plt h_v9 h_v725 (of_decide_eq_true rfl)
  have h_v728 : R 1 0 0 1 v728 v728 := (r_sub hl (r_O hl) h_v727 (of_decide_eq_true rfl))
  have e_v728 : (v728 = 1 ↔ ¬v727 = 1) := e_not h_v727 (of_decide_eq_true rfl)
  have h_v729 : R 1 0 0 1 v729 v729 := (r_land hl h_v726 h_v728 (of_decide_eq_true rfl))
  have e_v729 : (v729 = 1 ↔ v726 = 1 ∧ v728 = 1) := e_land h_v726 h_v728 (of_decide_eq_true rfl)
  have h_t723_1 : R 1 0 4611686018427387904 4611686018695823363 t723.1 t723.1 := r_sc1 hl h_v723 (of_decide_eq_true rfl)
  have h_t723_2 : R 1 0 4611686018158952445 4611686018695823363 t723.2 t723.2 := r_sc2 hl h_v723 (of_decide_eq_true rfl)
  have e_t723_1 : sv t723.1 = (sc28pS (scArg v723)).1 := e_sc1 h_v723 (of_decide_eq_true rfl)
  have e_t723_2 : sv t723.2 = (sc28pS (scArg v723)).2 := e_sc2 h_v723 (of_decide_eq_true rfl)
  have h_t725_1 : R 1 0 4611686018427387904 4611686018695823363 t725.1 t725.1 := r_sc1 hl h_v725 (of_decide_eq_true rfl)
  have h_t725_2 : R 1 0 4611686018158952445 4611686018695823363 t725.2 t725.2 := r_sc2 hl h_v725 (of_decide_eq_true rfl)
  have e_t725_1 : sv t725.1 = (sc28pS (scArg v725)).1 := e_sc1 h_v725 (of_decide_eq_true rfl)
  have e_t725_2 : sv t725.2 = (sc28pS (scArg v725)).2 := e_sc2 h_v725 (of_decide_eq_true rfl)
  have h_v732 : R 1 0 0 1 v732 v732 := (r_plt hl h_t723_1 h_t725_1 (of_decide_eq_true rfl))
  have e_v732 : (v732 = 1 ↔ sv t723.1 < sv t725.1) := e_plt h_t723_1 h_t725_1 (of_decide_eq_true rfl)
  have h_v733 : R 1 0 4611686018427387904 4611686018695823363 v733 v733 := (r_psel hl h_v732 h_t723_1 h_t725_1 (of_decide_eq_true rfl))
  have e_v733 : v733 = if v732 = 1 then t723.1 else t725.1 := e_psel h_v732 h_t723_1 h_t725_1 (of_decide_eq_true rfl)
  have h_v734 : R 1 0 4611686018427387900 4611686018695823359 v734 v734 := (r_sub hl (r_add hl h_v28 h_v733 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v734 : sv v734 = sv v28 + sv v733 := e_add h_v28 h_v733 (of_decide_eq_true rfl)
  have h_v735 : R 1 0 4611686018427387904 4611686018695823363 v735 v735 := (r_psel hl h_v732 h_t725_1 h_t723_1 (of_decide_eq_true rfl))
  have e_v735 : v735 = if v732 = 1 then t725.1 else t723.1 := e_psel h_v732 h_t725_1 h_t723_1 (of_decide_eq_true rfl)
  have h_v736 : R 1 0 4611686018427387908 4611686018695823367 v736 v736 := (r_sub hl (r_add hl h_v31 h_v735 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v736 : sv v736 = sv v31 + sv v735 := e_add h_v31 h_v735 (of_decide_eq_true rfl)
  clear h_v9 h_v31 h_v726 h_v727 h_v728 h_t723_1 h_t723_2 e_t723_2 h_t725_1 h_t725_2 e_t725_2 h_v732 h_v733 h_v735
  have h_v737 : R 1 0 0 1 v737 v737 := (r_plt hl h_v736 h_v33 (of_decide_eq_true rfl))
  have e_v737 : (v737 = 1 ↔ sv v736 < sv v33) := e_plt h_v736 h_v33 (of_decide_eq_true rfl)
  have h_v738 : R 1 0 4611686018427387908 4611686018695823367 v738 v738 := (r_psel hl h_v737 h_v736 h_v33 (of_decide_eq_true rfl))
  have e_v738 : v738 = if v737 = 1 then v736 else v33 := e_psel h_v737 h_v736 h_v33 (of_decide_eq_true rfl)
  have h_v739 : R 1 0 0 1 v739 v739 := (r_plt hl h_v723 h_v36 (of_decide_eq_true rfl))
  have e_v739 : (v739 = 1 ↔ sv v723 < sv v36) := e_plt h_v723 h_v36 (of_decide_eq_true rfl)
  have h_v740 : R 1 0 0 1 v740 v740 := (r_plt hl h_v38 h_v725 (of_decide_eq_true rfl))
  have e_v740 : (v740 = 1 ↔ sv v38 < sv v725) := e_plt h_v38 h_v725 (of_decide_eq_true rfl)
  have h_v741 : R 1 0 0 1 v741 v741 := (r_land hl h_v739 h_v740 (of_decide_eq_true rfl))
  have e_v741 : (v741 = 1 ↔ v739 = 1 ∧ v740 = 1) := e_land h_v739 h_v740 (of_decide_eq_true rfl)
  have h_v742 : R 1 0 4611686018427387908 4611686018695823367 v742 v742 := (r_psel hl h_v741 h_v33 h_v738 (of_decide_eq_true rfl))
  have e_v742 : v742 = if v741 = 1 then v33 else v738 := e_psel h_v741 h_v33 h_v738 (of_decide_eq_true rfl)
  have h_v743 : R 1 0 0 1 v743 v743 := (r_plt hl h_v734 h_v61 (of_decide_eq_true rfl))
  have e_v743 : (v743 = 1 ↔ sv v734 < sv v61) := e_plt h_v734 h_v61 (of_decide_eq_true rfl)
  have h_v744 : R 1 0 0 1 v744 v744 := (r_sub hl (r_O hl) h_v743 (of_decide_eq_true rfl))
  have e_v744 : (v744 = 1 ↔ ¬v743 = 1) := e_not h_v743 (of_decide_eq_true rfl)
  have h_v745 : R 1 0 0 1 v745 v745 := (r_plt hl h_v61 h_v742 (of_decide_eq_true rfl))
  have e_v745 : (v745 = 1 ↔ sv v61 < sv v742) := e_plt h_v61 h_v742 (of_decide_eq_true rfl)
  have h_v746 : R 1 0 0 1 v746 v746 := (r_sub hl (r_O hl) h_v745 (of_decide_eq_true rfl))
  have e_v746 : (v746 = 1 ↔ ¬v745 = 1) := e_not h_v745 (of_decide_eq_true rfl)
  have h_v747 : R 1 0 0 1 v747 v747 := (r_land hl h_v743 h_v746 (of_decide_eq_true rfl))
  have e_v747 : (v747 = 1 ↔ v743 = 1 ∧ v746 = 1) := e_land h_v743 h_v746 (of_decide_eq_true rfl)
  have h_v748 : R 1 0 0 1 v748 v748 := (r_land hl h_v743 h_v745 (of_decide_eq_true rfl))
  have e_v748 : (v748 = 1 ↔ v743 = 1 ∧ v745 = 1) := e_land h_v743 h_v745 (of_decide_eq_true rfl)
  have h_v749 : R 1 0 0 1 v749 v749 := (r_land hl h_v67 h_v748 (of_decide_eq_true rfl))
  clear h_v36 h_v38 h_v723 h_v725 h_v736 h_v737 h_v738 h_v739 h_v740 h_v741 h_v743 h_v745 h_v746
  have e_v749 : (v749 = 1 ↔ v67 = 1 ∧ v748 = 1) := e_land h_v67 h_v748 (of_decide_eq_true rfl)
  have h_v750 : R 1 0 0 1 v750 v750 := (r_sub hl (r_O hl) h_v749 (of_decide_eq_true rfl))
  have e_v750 : (v750 = 1 ↔ ¬v749 = 1) := e_not h_v749 (of_decide_eq_true rfl)
  have h_v751 : R 1 0 0 1 v751 v751 := (r_land hl h_v63 h_v748 (of_decide_eq_true rfl))
  have e_v751 : (v751 = 1 ↔ v63 = 1 ∧ v748 = 1) := e_land h_v63 h_v748 (of_decide_eq_true rfl)
  have h_v752 : R 1 0 0 1 v752 v752 := (r_lor hl h_v747 h_v751 (of_decide_eq_true rfl))
  have e_v752 : (v752 = 1 ↔ v747 = 1 ∨ v751 = 1) := e_lor h_v747 h_v751 (of_decide_eq_true rfl)
  have h_v753 : R 1 0 4611686018427387900 4611686018695823367 v753 v753 := (r_psel hl h_v752 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v753 : v753 = if v752 = 1 then v41 else v29 := e_psel h_v752 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v754 : R 1 0 0 1 v754 v754 := (r_land hl h_v67 h_v744 (of_decide_eq_true rfl))
  have e_v754 : (v754 = 1 ↔ v67 = 1 ∧ v744 = 1) := e_land h_v67 h_v744 (of_decide_eq_true rfl)
  have h_v755 : R 1 0 0 1 v755 v755 := (r_lor hl h_v66 h_v754 (of_decide_eq_true rfl))
  have e_v755 : (v755 = 1 ↔ v66 = 1 ∨ v754 = 1) := e_lor h_v66 h_v754 (of_decide_eq_true rfl)
  have h_v756 : R 1 0 4611686018427387900 4611686018695823367 v756 v756 := (r_psel hl h_v755 h_v742 h_v734 (of_decide_eq_true rfl))
  have e_v756 : v756 = if v755 = 1 then v742 else v734 := e_psel h_v755 h_v742 h_v734 (of_decide_eq_true rfl)
  have h_v757 : R 1 0 0 1 v757 v757 := (r_land hl h_v66 h_v748 (of_decide_eq_true rfl))
  have e_v757 : (v757 = 1 ↔ v66 = 1 ∧ v748 = 1) := e_land h_v66 h_v748 (of_decide_eq_true rfl)
  have h_v758 : R 1 0 0 1 v758 v758 := (r_lor hl h_v747 h_v757 (of_decide_eq_true rfl))
  have e_v758 : (v758 = 1 ↔ v747 = 1 ∨ v757 = 1) := e_lor h_v747 h_v757 (of_decide_eq_true rfl)
  have h_v759 : R 1 0 4611686018427387900 4611686018695823367 v759 v759 := (r_psel hl h_v758 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v759 : v759 = if v758 = 1 then v29 else v41 := e_psel h_v758 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v760 : R 1 0 0 1 v760 v760 := (r_land hl h_v67 h_v747 (of_decide_eq_true rfl))
  have e_v760 : (v760 = 1 ↔ v67 = 1 ∧ v747 = 1) := e_land h_v67 h_v747 (of_decide_eq_true rfl)
  have h_v761 : R 1 0 0 1 v761 v761 := (r_lor hl h_v66 h_v760 (of_decide_eq_true rfl))
  have e_v761 : (v761 = 1 ↔ v66 = 1 ∨ v760 = 1) := e_lor h_v66 h_v760 (of_decide_eq_true rfl)
  clear h_v29 h_v41 h_v63 h_v66 h_v67 h_v744 h_v747 h_v748 h_v749 h_v751 h_v752 h_v754 h_v755 h_v757 h_v758 h_v760
  have h_v762 : R 1 0 4611686018427387900 4611686018695823367 v762 v762 := (r_psel hl h_v761 h_v734 h_v742 (of_decide_eq_true rfl))
  have e_v762 : v762 = if v761 = 1 then v734 else v742 := e_psel h_v761 h_v734 h_v742 (of_decide_eq_true rfl)
  have h_v763 : R 1 0 4611686017353646052 4683743616223412273 v763 v763 := (r_smx hl 29 h_v756 h_v753 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v763 : sv v763 = sv v756 * sv v753 := e_smx 29 h_v756 h_v753 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v764 : R 1 0 4611686018427387899 4611686018695823374 v764 v764 := (r_srdF hl h_v763 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v764 : sv v764 = sv v763 / 2 ^ 28 := e_srdF h_v763 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v765 : R 1 0 4611686017353646052 4683743616223412273 v765 v765 := (r_smx hl 29 h_v762 h_v759 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v765 : sv v765 = sv v762 * sv v759 := e_smx 29 h_v762 h_v759 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v766 : R 1 0 4611686018427387900 4611686018695823375 v766 v766 := (r_srdC hl h_v765 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v766 : sv v766 = -((-sv v765) / 2 ^ 28) := e_srdC h_v765 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v767 : R 1 0 0 1 v767 v767 := (r_plt hl h_v19 h_v764 (of_decide_eq_true rfl))
  have e_v767 : (v767 = 1 ↔ sv v19 < sv v764) := e_plt h_v19 h_v764 (of_decide_eq_true rfl)
  have h_v768 : R 1 0 0 1 v768 v768 := (r_plt hl h_v61 h_v764 (of_decide_eq_true rfl))
  have e_v768 : (v768 = 1 ↔ sv v61 < sv v764) := e_plt h_v61 h_v764 (of_decide_eq_true rfl)
  have h_v769 : R 1 0 0 1 v769 v769 := (r_plt hl h_v766 h_v33 (of_decide_eq_true rfl))
  have e_v769 : (v769 = 1 ↔ sv v766 < sv v33) := e_plt h_v766 h_v33 (of_decide_eq_true rfl)
  have h_v770 : R 1 0 0 1 v770 v770 := (r_land hl h_v768 h_v769 (of_decide_eq_true rfl))
  have e_v770 : (v770 = 1 ↔ v768 = 1 ∧ v769 = 1) := e_land h_v768 h_v769 (of_decide_eq_true rfl)
  have h_v771 : R 1 0 0 1 v771 v771 := (r_plt hl h_v61 h_v89 (of_decide_eq_true rfl))
  have e_v771 : (v771 = 1 ↔ sv v61 < sv v89) := e_plt h_v61 h_v89 (of_decide_eq_true rfl)
  have h_v772 : R 1 0 0 1 v772 v772 := (r_plt hl h_v91 h_v33 (of_decide_eq_true rfl))
  have e_v772 : (v772 = 1 ↔ sv v91 < sv v33) := e_plt h_v91 h_v33 (of_decide_eq_true rfl)
  have h_v773 : R 1 0 0 1 v773 v773 := (r_land hl h_v771 h_v772 (of_decide_eq_true rfl))
  have e_v773 : (v773 = 1 ↔ v771 = 1 ∧ v772 = 1) := e_land h_v771 h_v772 (of_decide_eq_true rfl)
  have h_v774 : R 1 0 0 1 v774 v774 := (r_plt hl h_v61 h_v438 (of_decide_eq_true rfl))
  clear h_v19 h_v734 h_v742 h_v753 h_v756 h_v759 h_v761 h_v762 h_v763 h_v765 h_v768 h_v769 h_v771 h_v772
  have e_v774 : (v774 = 1 ↔ sv v61 < sv v438) := e_plt h_v61 h_v438 (of_decide_eq_true rfl)
  have h_v775 : R 1 0 0 1 v775 v775 := (r_plt hl h_v440 h_v33 (of_decide_eq_true rfl))
  have e_v775 : (v775 = 1 ↔ sv v440 < sv v33) := e_plt h_v440 h_v33 (of_decide_eq_true rfl)
  have h_v776 : R 1 0 0 1 v776 v776 := (r_land hl h_v774 h_v775 (of_decide_eq_true rfl))
  have e_v776 : (v776 = 1 ↔ v774 = 1 ∧ v775 = 1) := e_land h_v774 h_v775 (of_decide_eq_true rfl)
  have h_v777 : R 1 0 0 1 v777 v777 := (r_land hl h_v770 h_v773 (of_decide_eq_true rfl))
  have e_v777 : (v777 = 1 ↔ v770 = 1 ∧ v773 = 1) := e_land h_v770 h_v773 (of_decide_eq_true rfl)
  have h_v778 : R 1 0 0 1 v778 v778 := (r_land hl h_v776 h_v777 (of_decide_eq_true rfl))
  have e_v778 : (v778 = 1 ↔ v776 = 1 ∧ v777 = 1) := e_land h_v776 h_v777 (of_decide_eq_true rfl)
  have h_v779 : R 1 0 4611686018427387904 4683743620518379745 v779 v779 := (r_smx_sq hl 29 h_v766 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v779 : sv v779 = sv v766 * sv v766 := e_smx_sq 29 h_v766 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v780 : R 1 0 4611686018427387904 4611686018695823391 v780 v780 := (r_srdC hl h_v779 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v780 : sv v780 = -((-sv v779) / 2 ^ 28) := e_srdC h_v779 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v781 : R 1 0 4611686018427387904 4611686018964258878 v781 v781 := (r_sub hl (r_add hl h_v780 h_v780 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v781 : sv v781 = sv v780 + sv v780 := e_add h_v780 h_v780 (of_decide_eq_true rfl)
  have h_v782 : R 1 0 4611686018158952386 4611686018695823360 v782 v782 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v781 (of_decide_eq_true rfl))
  have e_v782 : sv v782 = sv v33 - sv v781 := e_sub h_v33 h_v781 (of_decide_eq_true rfl)
  have h_v783 : R 1 0 0 1 v783 v783 := (r_plt hl h_v782 h_v95 (of_decide_eq_true rfl))
  have e_v783 : (v783 = 1 ↔ sv v782 < sv v95) := e_plt h_v782 h_v95 (of_decide_eq_true rfl)
  have h_v784 : R 1 0 4611686018158952386 4611686018695823360 v784 v784 := (r_psel hl h_v783 h_v95 h_v782 (of_decide_eq_true rfl))
  have e_v784 : v784 = if v783 = 1 then v95 else v782 := e_psel h_v783 h_v95 h_v782 (of_decide_eq_true rfl)
  have h_v785 : R 1 0 4611686018427387904 4683743619981508804 v785 v785 := (r_smx_sq hl 29 h_v764 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v785 : sv v785 = sv v764 * sv v764 := e_smx_sq 29 h_v764 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v786 : R 1 0 4611686018427387904 4611686018695823388 v786 v786 := (r_srdF hl h_v785 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v786 : sv v786 = sv v785 / 2 ^ 28 := e_srdF h_v785 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  clear h_v764 h_v766 h_v770 h_v773 h_v774 h_v775 h_v776 h_v777 h_v779 h_v780 h_v781 h_v782 h_v783 h_v785
  have h_v787 : R 1 0 4611686018427387904 4611686018964258872 v787 v787 := (r_sub hl (r_add hl h_v786 h_v786 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v787 : sv v787 = sv v786 + sv v786 := e_add h_v786 h_v786 (of_decide_eq_true rfl)
  have h_v788 : R 1 0 4611686018158952392 4611686018695823360 v788 v788 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v787 (of_decide_eq_true rfl))
  have e_v788 : sv v788 = sv v33 - sv v787 := e_sub h_v33 h_v787 (of_decide_eq_true rfl)
  have h_v789 : R 1 0 4611686018427387904 4683743620518379745 v789 v789 := (r_smx_sq hl 29 h_v440 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v789 : sv v789 = sv v440 * sv v440 := e_smx_sq 29 h_v440 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v790 : R 1 0 4611686018427387904 4611686018695823391 v790 v790 := (r_srdC hl h_v789 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v790 : sv v790 = -((-sv v789) / 2 ^ 28) := e_srdC h_v789 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v791 : R 1 0 4611686018427387904 4611686018964258878 v791 v791 := (r_sub hl (r_add hl h_v790 h_v790 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v791 : sv v791 = sv v790 + sv v790 := e_add h_v790 h_v790 (of_decide_eq_true rfl)
  have h_v792 : R 1 0 4611686018158952386 4611686018695823360 v792 v792 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v791 (of_decide_eq_true rfl))
  have e_v792 : sv v792 = sv v33 - sv v791 := e_sub h_v33 h_v791 (of_decide_eq_true rfl)
  have h_v793 : R 1 0 0 1 v793 v793 := (r_plt hl h_v792 h_v95 (of_decide_eq_true rfl))
  have e_v793 : (v793 = 1 ↔ sv v792 < sv v95) := e_plt h_v792 h_v95 (of_decide_eq_true rfl)
  have h_v794 : R 1 0 4611686018158952386 4611686018695823360 v794 v794 := (r_psel hl h_v793 h_v95 h_v792 (of_decide_eq_true rfl))
  have e_v794 : v794 = if v793 = 1 then v95 else v792 := e_psel h_v793 h_v95 h_v792 (of_decide_eq_true rfl)
  have h_v795 : R 1 0 4611686018427387904 4683743619981508804 v795 v795 := (r_smx_sq hl 29 h_v438 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v795 : sv v795 = sv v438 * sv v438 := e_smx_sq 29 h_v438 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v796 : R 1 0 4611686018427387904 4611686018695823388 v796 v796 := (r_srdF hl h_v795 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v796 : sv v796 = sv v795 / 2 ^ 28 := e_srdF h_v795 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v797 : R 1 0 4611686018427387904 4611686018964258872 v797 v797 := (r_sub hl (r_add hl h_v796 h_v796 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v797 : sv v797 = sv v796 + sv v796 := e_add h_v796 h_v796 (of_decide_eq_true rfl)
  have h_v798 : R 1 0 4611686018158952392 4611686018695823360 v798 v798 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v797 (of_decide_eq_true rfl))
  have e_v798 : sv v798 = sv v33 - sv v797 := e_sub h_v33 h_v797 (of_decide_eq_true rfl)
  have h_v799 : R 1 0 4611686018427387904 4683743620518379745 v799 v799 := (r_smx_sq hl 29 h_v91 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  clear h_v786 h_v787 h_v789 h_v790 h_v791 h_v792 h_v793 h_v795 h_v796 h_v797
  have e_v799 : sv v799 = sv v91 * sv v91 := e_smx_sq 29 h_v91 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v800 : R 1 0 4611686018427387904 4611686018695823391 v800 v800 := (r_srdC hl h_v799 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v800 : sv v800 = -((-sv v799) / 2 ^ 28) := e_srdC h_v799 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v801 : R 1 0 4611686018427387904 4611686018964258878 v801 v801 := (r_sub hl (r_add hl h_v800 h_v800 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v801 : sv v801 = sv v800 + sv v800 := e_add h_v800 h_v800 (of_decide_eq_true rfl)
  have h_v802 : R 1 0 4611686018158952386 4611686018695823360 v802 v802 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v801 (of_decide_eq_true rfl))
  have e_v802 : sv v802 = sv v33 - sv v801 := e_sub h_v33 h_v801 (of_decide_eq_true rfl)
  have h_v803 : R 1 0 0 1 v803 v803 := (r_plt hl h_v802 h_v95 (of_decide_eq_true rfl))
  have e_v803 : (v803 = 1 ↔ sv v802 < sv v95) := e_plt h_v802 h_v95 (of_decide_eq_true rfl)
  have h_v804 : R 1 0 4611686018158952386 4611686018695823360 v804 v804 := (r_psel hl h_v803 h_v95 h_v802 (of_decide_eq_true rfl))
  have e_v804 : v804 = if v803 = 1 then v95 else v802 := e_psel h_v803 h_v95 h_v802 (of_decide_eq_true rfl)
  have h_v805 : R 1 0 4611686018427387904 4683743619981508804 v805 v805 := (r_smx_sq hl 29 h_v89 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v805 : sv v805 = sv v89 * sv v89 := e_smx_sq 29 h_v89 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v806 : R 1 0 4611686018427387904 4611686018695823388 v806 v806 := (r_srdF hl h_v805 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v806 : sv v806 = sv v805 / 2 ^ 28 := e_srdF h_v805 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v807 : R 1 0 4611686018427387904 4611686018964258872 v807 v807 := (r_sub hl (r_add hl h_v806 h_v806 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v807 : sv v807 = sv v806 + sv v806 := e_add h_v806 h_v806 (of_decide_eq_true rfl)
  have h_v808 : R 1 0 4611686018158952392 4611686018695823360 v808 v808 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v807 (of_decide_eq_true rfl))
  have e_v808 : sv v808 = sv v33 - sv v807 := e_sub h_v33 h_v807 (of_decide_eq_true rfl)
  have h_v809 : R 1 0 0 1 v809 v809 := (r_plt hl h_v784 h_v61 (of_decide_eq_true rfl))
  have e_v809 : (v809 = 1 ↔ sv v784 < sv v61) := e_plt h_v784 h_v61 (of_decide_eq_true rfl)
  have h_v810 : R 1 0 0 1 v810 v810 := (r_sub hl (r_O hl) h_v809 (of_decide_eq_true rfl))
  have e_v810 : (v810 = 1 ↔ ¬v809 = 1) := e_not h_v809 (of_decide_eq_true rfl)
  have h_v811 : R 1 0 0 1 v811 v811 := (r_plt hl h_v61 h_v788 (of_decide_eq_true rfl))
  have e_v811 : (v811 = 1 ↔ sv v61 < sv v788) := e_plt h_v61 h_v788 (of_decide_eq_true rfl)
  clear h_v799 h_v800 h_v801 h_v802 h_v803 h_v805 h_v806 h_v807
  have h_v812 : R 1 0 0 1 v812 v812 := (r_sub hl (r_O hl) h_v811 (of_decide_eq_true rfl))
  have e_v812 : (v812 = 1 ↔ ¬v811 = 1) := e_not h_v811 (of_decide_eq_true rfl)
  have h_v813 : R 1 0 0 1 v813 v813 := (r_land hl h_v809 h_v812 (of_decide_eq_true rfl))
  have e_v813 : (v813 = 1 ↔ v809 = 1 ∧ v812 = 1) := e_land h_v809 h_v812 (of_decide_eq_true rfl)
  have h_v814 : R 1 0 0 1 v814 v814 := (r_land hl h_v809 h_v811 (of_decide_eq_true rfl))
  have e_v814 : (v814 = 1 ↔ v809 = 1 ∧ v811 = 1) := e_land h_v809 h_v811 (of_decide_eq_true rfl)
  have h_v815 : R 1 0 0 1 v815 v815 := (r_plt hl h_v804 h_v61 (of_decide_eq_true rfl))
  have e_v815 : (v815 = 1 ↔ sv v804 < sv v61) := e_plt h_v804 h_v61 (of_decide_eq_true rfl)
  have h_v816 : R 1 0 0 1 v816 v816 := (r_sub hl (r_O hl) h_v815 (of_decide_eq_true rfl))
  have e_v816 : (v816 = 1 ↔ ¬v815 = 1) := e_not h_v815 (of_decide_eq_true rfl)
  have h_v817 : R 1 0 0 1 v817 v817 := (r_plt hl h_v61 h_v808 (of_decide_eq_true rfl))
  have e_v817 : (v817 = 1 ↔ sv v61 < sv v808) := e_plt h_v61 h_v808 (of_decide_eq_true rfl)
  have h_v818 : R 1 0 0 1 v818 v818 := (r_sub hl (r_O hl) h_v817 (of_decide_eq_true rfl))
  have e_v818 : (v818 = 1 ↔ ¬v817 = 1) := e_not h_v817 (of_decide_eq_true rfl)
  have h_v819 : R 1 0 0 1 v819 v819 := (r_land hl h_v815 h_v818 (of_decide_eq_true rfl))
  have e_v819 : (v819 = 1 ↔ v815 = 1 ∧ v818 = 1) := e_land h_v815 h_v818 (of_decide_eq_true rfl)
  have h_v820 : R 1 0 0 1 v820 v820 := (r_land hl h_v815 h_v817 (of_decide_eq_true rfl))
  have e_v820 : (v820 = 1 ↔ v815 = 1 ∧ v817 = 1) := e_land h_v815 h_v817 (of_decide_eq_true rfl)
  have h_v821 : R 1 0 0 1 v821 v821 := (r_land hl h_v814 h_v820 (of_decide_eq_true rfl))
  have e_v821 : (v821 = 1 ↔ v814 = 1 ∧ v820 = 1) := e_land h_v814 h_v820 (of_decide_eq_true rfl)
  have h_v822 : R 1 0 0 1 v822 v822 := (r_sub hl (r_O hl) h_v821 (of_decide_eq_true rfl))
  have e_v822 : (v822 = 1 ↔ ¬v821 = 1) := e_not h_v821 (of_decide_eq_true rfl)
  have h_v823 : R 1 0 0 1 v823 v823 := (r_sub hl (r_O hl) h_v778 (of_decide_eq_true rfl))
  have e_v823 : (v823 = 1 ↔ ¬v778 = 1) := e_not h_v778 (of_decide_eq_true rfl)
  have h_v824 : R 1 0 0 1 v824 v824 := (r_lor hl h_v822 h_v823 (of_decide_eq_true rfl))
  clear h_v809 h_v811 h_v812 h_v815 h_v817 h_v818 h_v821
  have e_v824 : (v824 = 1 ↔ v822 = 1 ∨ v823 = 1) := e_lor h_v822 h_v823 (of_decide_eq_true rfl)
  have h_v825 : R 1 0 0 1 v825 v825 := (r_land hl h_v810 h_v820 (of_decide_eq_true rfl))
  have e_v825 : (v825 = 1 ↔ v810 = 1 ∧ v820 = 1) := e_land h_v810 h_v820 (of_decide_eq_true rfl)
  have h_v826 : R 1 0 0 1 v826 v826 := (r_lor hl h_v819 h_v825 (of_decide_eq_true rfl))
  have e_v826 : (v826 = 1 ↔ v819 = 1 ∨ v825 = 1) := e_lor h_v819 h_v825 (of_decide_eq_true rfl)
  have h_v827 : R 1 0 4611686018158952386 4611686018695823360 v827 v827 := (r_psel hl h_v826 h_v788 h_v784 (of_decide_eq_true rfl))
  have e_v827 : v827 = if v826 = 1 then v788 else v784 := e_psel h_v826 h_v788 h_v784 (of_decide_eq_true rfl)
  have h_v828 : R 1 0 0 1 v828 v828 := (r_land hl h_v814 h_v816 (of_decide_eq_true rfl))
  have e_v828 : (v828 = 1 ↔ v814 = 1 ∧ v816 = 1) := e_land h_v814 h_v816 (of_decide_eq_true rfl)
  have h_v829 : R 1 0 0 1 v829 v829 := (r_lor hl h_v813 h_v828 (of_decide_eq_true rfl))
  have e_v829 : (v829 = 1 ↔ v813 = 1 ∨ v828 = 1) := e_lor h_v813 h_v828 (of_decide_eq_true rfl)
  have h_v830 : R 1 0 4611686018158952386 4611686018695823360 v830 v830 := (r_psel hl h_v829 h_v808 h_v804 (of_decide_eq_true rfl))
  have e_v830 : v830 = if v829 = 1 then v808 else v804 := e_psel h_v829 h_v808 h_v804 (of_decide_eq_true rfl)
  have h_v831 : R 1 0 0 1 v831 v831 := (r_land hl h_v813 h_v820 (of_decide_eq_true rfl))
  have e_v831 : (v831 = 1 ↔ v813 = 1 ∧ v820 = 1) := e_land h_v813 h_v820 (of_decide_eq_true rfl)
  have h_v832 : R 1 0 0 1 v832 v832 := (r_lor hl h_v819 h_v831 (of_decide_eq_true rfl))
  have e_v832 : (v832 = 1 ↔ v819 = 1 ∨ v831 = 1) := e_lor h_v819 h_v831 (of_decide_eq_true rfl)
  have h_v833 : R 1 0 4611686018158952386 4611686018695823360 v833 v833 := (r_psel hl h_v832 h_v784 h_v788 (of_decide_eq_true rfl))
  have e_v833 : v833 = if v832 = 1 then v784 else v788 := e_psel h_v832 h_v784 h_v788 (of_decide_eq_true rfl)
  have h_v834 : R 1 0 0 1 v834 v834 := (r_land hl h_v814 h_v819 (of_decide_eq_true rfl))
  have e_v834 : (v834 = 1 ↔ v814 = 1 ∧ v819 = 1) := e_land h_v814 h_v819 (of_decide_eq_true rfl)
  have h_v835 : R 1 0 0 1 v835 v835 := (r_lor hl h_v813 h_v834 (of_decide_eq_true rfl))
  have e_v835 : (v835 = 1 ↔ v813 = 1 ∨ v834 = 1) := e_lor h_v813 h_v834 (of_decide_eq_true rfl)
  have h_v836 : R 1 0 4611686018158952386 4611686018695823360 v836 v836 := (r_psel hl h_v835 h_v804 h_v808 (of_decide_eq_true rfl))
  have e_v836 : v836 = if v835 = 1 then v804 else v808 := e_psel h_v835 h_v804 h_v808 (of_decide_eq_true rfl)
  clear h_v816 h_v819 h_v820 h_v822 h_v825 h_v826 h_v828 h_v829 h_v831 h_v832 h_v834 h_v835
  have h_v837 : R 1 0 4539628407746461696 4683743645751316228 v837 v837 := (r_smx hl 30 h_v830 h_v827 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v837 : sv v837 = sv v830 * sv v827 := e_smx 30 h_v830 h_v827 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v838 : R 1 0 4611686018158952386 4611686018695823484 v838 v838 := (r_srdF hl h_v837 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v838 : sv v838 = sv v837 / 2 ^ 28 := e_srdF h_v837 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v839 : R 1 0 4539628407746461696 4683743645751316228 v839 v839 := (r_smx hl 30 h_v836 h_v833 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v839 : sv v839 = sv v836 * sv v833 := e_smx 30 h_v836 h_v833 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v840 : R 1 0 4611686018158952386 4611686018695823485 v840 v840 := (r_srdC hl h_v839 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v840 : sv v840 = -((-sv v839) / 2 ^ 28) := e_srdC h_v839 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v841 : R 1 0 4611686017890516805 4611686018964258878 v841 v841 := (r_sub hl (r_add hl h_v794 h_OFFr (of_decide_eq_true rfl)) h_v840 (of_decide_eq_true rfl))
  have e_v841 : sv v841 = sv v794 - sv v840 := e_sub h_v794 h_v840 (of_decide_eq_true rfl)
  have h_v842 : R 1 0 4611686017890516812 4611686018964258878 v842 v842 := (r_sub hl (r_add hl h_v798 h_OFFr (of_decide_eq_true rfl)) h_v838 (of_decide_eq_true rfl))
  have e_v842 : sv v842 = sv v798 - sv v838 := e_sub h_v798 h_v838 (of_decide_eq_true rfl)
  have h_v843 : R 1 0 0 1 v843 v843 := (r_plt hl h_v794 h_v61 (of_decide_eq_true rfl))
  have e_v843 : (v843 = 1 ↔ sv v794 < sv v61) := e_plt h_v794 h_v61 (of_decide_eq_true rfl)
  have h_v844 : R 1 0 0 1 v844 v844 := (r_sub hl (r_O hl) h_v843 (of_decide_eq_true rfl))
  have e_v844 : (v844 = 1 ↔ ¬v843 = 1) := e_not h_v843 (of_decide_eq_true rfl)
  have h_v845 : R 1 0 0 1 v845 v845 := (r_plt hl h_v61 h_v798 (of_decide_eq_true rfl))
  have e_v845 : (v845 = 1 ↔ sv v61 < sv v798) := e_plt h_v61 h_v798 (of_decide_eq_true rfl)
  have h_v846 : R 1 0 0 1 v846 v846 := (r_sub hl (r_O hl) h_v845 (of_decide_eq_true rfl))
  have e_v846 : (v846 = 1 ↔ ¬v845 = 1) := e_not h_v845 (of_decide_eq_true rfl)
  have h_v847 : R 1 0 0 1 v847 v847 := (r_land hl h_v843 h_v846 (of_decide_eq_true rfl))
  have e_v847 : (v847 = 1 ↔ v843 = 1 ∧ v846 = 1) := e_land h_v843 h_v846 (of_decide_eq_true rfl)
  have h_v848 : R 1 0 0 1 v848 v848 := (r_land hl h_v843 h_v845 (of_decide_eq_true rfl))
  have e_v848 : (v848 = 1 ↔ v843 = 1 ∧ v845 = 1) := e_land h_v843 h_v845 (of_decide_eq_true rfl)
  have h_v849 : R 1 0 0 1 v849 v849 := (r_land hl h_v814 h_v848 (of_decide_eq_true rfl))
  clear h_v827 h_v830 h_v833 h_v836 h_v837 h_v838 h_v839 h_v840 h_v843 h_v845 h_v846
  have e_v849 : (v849 = 1 ↔ v814 = 1 ∧ v848 = 1) := e_land h_v814 h_v848 (of_decide_eq_true rfl)
  have h_v850 : R 1 0 0 1 v850 v850 := (r_sub hl (r_O hl) h_v849 (of_decide_eq_true rfl))
  have e_v850 : (v850 = 1 ↔ ¬v849 = 1) := e_not h_v849 (of_decide_eq_true rfl)
  have h_v851 : R 1 0 0 1 v851 v851 := (r_lor hl h_v823 h_v850 (of_decide_eq_true rfl))
  have e_v851 : (v851 = 1 ↔ v823 = 1 ∨ v850 = 1) := e_lor h_v823 h_v850 (of_decide_eq_true rfl)
  have h_v852 : R 1 0 0 1 v852 v852 := (r_land hl h_v810 h_v848 (of_decide_eq_true rfl))
  have e_v852 : (v852 = 1 ↔ v810 = 1 ∧ v848 = 1) := e_land h_v810 h_v848 (of_decide_eq_true rfl)
  have h_v853 : R 1 0 0 1 v853 v853 := (r_lor hl h_v847 h_v852 (of_decide_eq_true rfl))
  have e_v853 : (v853 = 1 ↔ v847 = 1 ∨ v852 = 1) := e_lor h_v847 h_v852 (of_decide_eq_true rfl)
  have h_v854 : R 1 0 4611686018158952386 4611686018695823360 v854 v854 := (r_psel hl h_v853 h_v788 h_v784 (of_decide_eq_true rfl))
  have e_v854 : v854 = if v853 = 1 then v788 else v784 := e_psel h_v853 h_v788 h_v784 (of_decide_eq_true rfl)
  have h_v855 : R 1 0 0 1 v855 v855 := (r_land hl h_v814 h_v844 (of_decide_eq_true rfl))
  have e_v855 : (v855 = 1 ↔ v814 = 1 ∧ v844 = 1) := e_land h_v814 h_v844 (of_decide_eq_true rfl)
  have h_v856 : R 1 0 0 1 v856 v856 := (r_lor hl h_v813 h_v855 (of_decide_eq_true rfl))
  have e_v856 : (v856 = 1 ↔ v813 = 1 ∨ v855 = 1) := e_lor h_v813 h_v855 (of_decide_eq_true rfl)
  have h_v857 : R 1 0 4611686018158952386 4611686018695823360 v857 v857 := (r_psel hl h_v856 h_v798 h_v794 (of_decide_eq_true rfl))
  have e_v857 : v857 = if v856 = 1 then v798 else v794 := e_psel h_v856 h_v798 h_v794 (of_decide_eq_true rfl)
  have h_v858 : R 1 0 0 1 v858 v858 := (r_land hl h_v813 h_v848 (of_decide_eq_true rfl))
  have e_v858 : (v858 = 1 ↔ v813 = 1 ∧ v848 = 1) := e_land h_v813 h_v848 (of_decide_eq_true rfl)
  have h_v859 : R 1 0 0 1 v859 v859 := (r_lor hl h_v847 h_v858 (of_decide_eq_true rfl))
  have e_v859 : (v859 = 1 ↔ v847 = 1 ∨ v858 = 1) := e_lor h_v847 h_v858 (of_decide_eq_true rfl)
  have h_v860 : R 1 0 4611686018158952386 4611686018695823360 v860 v860 := (r_psel hl h_v859 h_v784 h_v788 (of_decide_eq_true rfl))
  have e_v860 : v860 = if v859 = 1 then v784 else v788 := e_psel h_v859 h_v784 h_v788 (of_decide_eq_true rfl)
  have h_v861 : R 1 0 0 1 v861 v861 := (r_land hl h_v814 h_v847 (of_decide_eq_true rfl))
  have e_v861 : (v861 = 1 ↔ v814 = 1 ∧ v847 = 1) := e_land h_v814 h_v847 (of_decide_eq_true rfl)
  clear h_v810 h_v814 h_v844 h_v847 h_v848 h_v849 h_v850 h_v852 h_v853 h_v855 h_v856 h_v858 h_v859
  have h_v862 : R 1 0 0 1 v862 v862 := (r_lor hl h_v813 h_v861 (of_decide_eq_true rfl))
  have e_v862 : (v862 = 1 ↔ v813 = 1 ∨ v861 = 1) := e_lor h_v813 h_v861 (of_decide_eq_true rfl)
  have h_v863 : R 1 0 4611686018158952386 4611686018695823360 v863 v863 := (r_psel hl h_v862 h_v794 h_v798 (of_decide_eq_true rfl))
  have e_v863 : v863 = if v862 = 1 then v794 else v798 := e_psel h_v862 h_v794 h_v798 (of_decide_eq_true rfl)
  have h_v864 : R 1 0 4539628407746461696 4683743645751316228 v864 v864 := (r_smx hl 30 h_v857 h_v854 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v864 : sv v864 = sv v857 * sv v854 := e_smx 30 h_v857 h_v854 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v865 : R 1 0 4611686018158952386 4611686018695823484 v865 v865 := (r_srdF hl h_v864 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v865 : sv v865 = sv v864 / 2 ^ 28 := e_srdF h_v864 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v866 : R 1 0 4539628407746461696 4683743645751316228 v866 v866 := (r_smx hl 30 h_v863 h_v860 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v866 : sv v866 = sv v863 * sv v860 := e_smx 30 h_v863 h_v860 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v867 : R 1 0 4611686018158952386 4611686018695823485 v867 v867 := (r_srdC hl h_v866 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v867 : sv v867 = -((-sv v866) / 2 ^ 28) := e_srdC h_v866 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v868 : R 1 0 4611686017890516805 4611686018964258878 v868 v868 := (r_sub hl (r_add hl h_v804 h_OFFr (of_decide_eq_true rfl)) h_v867 (of_decide_eq_true rfl))
  have e_v868 : sv v868 = sv v804 - sv v867 := e_sub h_v804 h_v867 (of_decide_eq_true rfl)
  have h_v869 : R 1 0 4611686017890516812 4611686018964258878 v869 v869 := (r_sub hl (r_add hl h_v808 h_OFFr (of_decide_eq_true rfl)) h_v865 (of_decide_eq_true rfl))
  have e_v869 : sv v869 = sv v808 - sv v865 := e_sub h_v808 h_v865 (of_decide_eq_true rfl)
  have h_v870 : R 1 0 0 1 v870 v870 := (r_plt hl h_v61 h_v841 (of_decide_eq_true rfl))
  have e_v870 : (v870 = 1 ↔ sv v61 < sv v841) := e_plt h_v61 h_v841 (of_decide_eq_true rfl)
  have h_v871 : R 1 0 0 1 v871 v871 := (r_plt hl h_v842 h_v61 (of_decide_eq_true rfl))
  have e_v871 : (v871 = 1 ↔ sv v842 < sv v61) := e_plt h_v842 h_v61 (of_decide_eq_true rfl)
  have h_v872 : R 1 0 0 1 v872 v872 := (r_plt hl h_v61 h_v868 (of_decide_eq_true rfl))
  have e_v872 : (v872 = 1 ↔ sv v61 < sv v868) := e_plt h_v61 h_v868 (of_decide_eq_true rfl)
  have h_v873 : R 1 0 0 1 v873 v873 := (r_plt hl h_v869 h_v61 (of_decide_eq_true rfl))
  have e_v873 : (v873 = 1 ↔ sv v869 < sv v61) := e_plt h_v869 h_v61 (of_decide_eq_true rfl)
  have h_v874 : R 1 0 4611686018427387899 4611686018695823375 v874 v874 := (r_psel hl h_v870 h_v91 h_v89 (of_decide_eq_true rfl))
  clear h_v794 h_v798 h_v804 h_v808 h_v813 h_v841 h_v842 h_v854 h_v857 h_v860 h_v861 h_v862 h_v863 h_v864 h_v865 h_v866 h_v867 h_v868 h_v869
  have e_v874 : v874 = if v870 = 1 then v91 else v89 := e_psel h_v870 h_v91 h_v89 (of_decide_eq_true rfl)
  have h_v875 : R 1 0 4611686018427387899 4611686018695823375 v875 v875 := (r_psel hl h_v871 h_v89 h_v91 (of_decide_eq_true rfl))
  have e_v875 : v875 = if v871 = 1 then v89 else v91 := e_psel h_v871 h_v89 h_v91 (of_decide_eq_true rfl)
  have h_v876 : R 1 0 4611686018427387899 4611686018695823375 v876 v876 := (r_psel hl h_v871 h_v91 h_v89 (of_decide_eq_true rfl))
  have e_v876 : v876 = if v871 = 1 then v91 else v89 := e_psel h_v871 h_v91 h_v89 (of_decide_eq_true rfl)
  have h_v877 : R 1 0 4611686018427387899 4611686018695823375 v877 v877 := (r_psel hl h_v870 h_v89 h_v91 (of_decide_eq_true rfl))
  have e_v877 : v877 = if v870 = 1 then v89 else v91 := e_psel h_v870 h_v89 h_v91 (of_decide_eq_true rfl)
  have h_v878 : R 1 0 4611686018427387899 4611686018695823375 v878 v878 := (r_psel hl h_v872 h_v440 h_v438 (of_decide_eq_true rfl))
  have e_v878 : v878 = if v872 = 1 then v440 else v438 := e_psel h_v872 h_v440 h_v438 (of_decide_eq_true rfl)
  have h_v879 : R 1 0 4611686018427387899 4611686018695823375 v879 v879 := (r_psel hl h_v873 h_v438 h_v440 (of_decide_eq_true rfl))
  have e_v879 : v879 = if v873 = 1 then v438 else v440 := e_psel h_v873 h_v438 h_v440 (of_decide_eq_true rfl)
  have h_v880 : R 1 0 4611686018427387899 4611686018695823375 v880 v880 := (r_psel hl h_v873 h_v440 h_v438 (of_decide_eq_true rfl))
  have e_v880 : v880 = if v873 = 1 then v440 else v438 := e_psel h_v873 h_v440 h_v438 (of_decide_eq_true rfl)
  have h_v881 : R 1 0 4611686018427387899 4611686018695823375 v881 v881 := (r_psel hl h_v872 h_v438 h_v440 (of_decide_eq_true rfl))
  have e_v881 : v881 = if v872 = 1 then v438 else v440 := e_psel h_v872 h_v438 h_v440 (of_decide_eq_true rfl)
  have h_v887 : R 1 0 4611686018427387904 4683743620518379745 v887 v887 := (r_smx_sq hl 29 h_v875 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v887 : sv v887 = sv v875 * sv v875 := e_smx_sq 29 h_v875 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v888 : R 1 0 4611686018427387904 4611686018695823391 v888 v888 := (r_srdC hl h_v887 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v888 : sv v888 = -((-sv v887) / 2 ^ 28) := e_srdC h_v887 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v889 : R 1 0 4611686018427387904 4611686018964258878 v889 v889 := (r_sub hl (r_add hl h_v888 h_v888 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v889 : sv v889 = sv v888 + sv v888 := e_add h_v888 h_v888 (of_decide_eq_true rfl)
  have h_v890 : R 1 0 4611686018158952386 4611686018695823360 v890 v890 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v889 (of_decide_eq_true rfl))
  have e_v890 : sv v890 = sv v33 - sv v889 := e_sub h_v33 h_v889 (of_decide_eq_true rfl)
  have h_v891 : R 1 0 0 1 v891 v891 := (r_plt hl h_v890 h_v95 (of_decide_eq_true rfl))
  have e_v891 : (v891 = 1 ↔ sv v890 < sv v95) := e_plt h_v890 h_v95 (of_decide_eq_true rfl)
  clear h_v89 h_v91 h_v438 h_v440 h_v870 h_v871 h_v872 h_v873 h_v888 h_v889
  have h_v892 : R 1 0 4611686018158952386 4611686018695823360 v892 v892 := (r_psel hl h_v891 h_v95 h_v890 (of_decide_eq_true rfl))
  have e_v892 : v892 = if v891 = 1 then v95 else v890 := e_psel h_v891 h_v95 h_v890 (of_decide_eq_true rfl)
  have h_v893 : R 1 0 4611686018427387904 4683743620518379745 v893 v893 := (r_smx_sq hl 29 h_v874 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v893 : sv v893 = sv v874 * sv v874 := e_smx_sq 29 h_v874 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v894 : R 1 0 4611686018427387904 4611686018695823390 v894 v894 := (r_srdF hl h_v893 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v894 : sv v894 = sv v893 / 2 ^ 28 := e_srdF h_v893 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v895 : R 1 0 4611686018427387904 4611686018964258876 v895 v895 := (r_sub hl (r_add hl h_v894 h_v894 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v895 : sv v895 = sv v894 + sv v894 := e_add h_v894 h_v894 (of_decide_eq_true rfl)
  have h_v896 : R 1 0 4611686018158952388 4611686018695823360 v896 v896 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v895 (of_decide_eq_true rfl))
  have e_v896 : sv v896 = sv v33 - sv v895 := e_sub h_v33 h_v895 (of_decide_eq_true rfl)
  have h_v897 : R 1 0 4611686018427387904 4683743620518379745 v897 v897 := (r_smx_sq hl 29 h_v879 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v897 : sv v897 = sv v879 * sv v879 := e_smx_sq 29 h_v879 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v898 : R 1 0 4611686018427387904 4611686018695823391 v898 v898 := (r_srdC hl h_v897 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v898 : sv v898 = -((-sv v897) / 2 ^ 28) := e_srdC h_v897 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v899 : R 1 0 4611686018427387904 4611686018964258878 v899 v899 := (r_sub hl (r_add hl h_v898 h_v898 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v899 : sv v899 = sv v898 + sv v898 := e_add h_v898 h_v898 (of_decide_eq_true rfl)
  have h_v900 : R 1 0 4611686018158952386 4611686018695823360 v900 v900 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v899 (of_decide_eq_true rfl))
  have e_v900 : sv v900 = sv v33 - sv v899 := e_sub h_v33 h_v899 (of_decide_eq_true rfl)
  have h_v901 : R 1 0 0 1 v901 v901 := (r_plt hl h_v900 h_v95 (of_decide_eq_true rfl))
  have e_v901 : (v901 = 1 ↔ sv v900 < sv v95) := e_plt h_v900 h_v95 (of_decide_eq_true rfl)
  have h_v902 : R 1 0 4611686018158952386 4611686018695823360 v902 v902 := (r_psel hl h_v901 h_v95 h_v900 (of_decide_eq_true rfl))
  have e_v902 : v902 = if v901 = 1 then v95 else v900 := e_psel h_v901 h_v95 h_v900 (of_decide_eq_true rfl)
  have h_v903 : R 1 0 4611686018427387904 4683743620518379745 v903 v903 := (r_smx_sq hl 29 h_v878 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v903 : sv v903 = sv v878 * sv v878 := e_smx_sq 29 h_v878 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v904 : R 1 0 4611686018427387904 4611686018695823390 v904 v904 := (r_srdF hl h_v903 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  clear h_v890 h_v891 h_v894 h_v895 h_v898 h_v899 h_v900 h_v901
  have e_v904 : sv v904 = sv v903 / 2 ^ 28 := e_srdF h_v903 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v905 : R 1 0 4611686018427387904 4611686018964258876 v905 v905 := (r_sub hl (r_add hl h_v904 h_v904 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v905 : sv v905 = sv v904 + sv v904 := e_add h_v904 h_v904 (of_decide_eq_true rfl)
  have h_v906 : R 1 0 4611686018158952388 4611686018695823360 v906 v906 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v905 (of_decide_eq_true rfl))
  have e_v906 : sv v906 = sv v33 - sv v905 := e_sub h_v33 h_v905 (of_decide_eq_true rfl)
  have h_v907 : R 1 0 0 1 v907 v907 := (r_plt hl h_v892 h_v61 (of_decide_eq_true rfl))
  have e_v907 : (v907 = 1 ↔ sv v892 < sv v61) := e_plt h_v892 h_v61 (of_decide_eq_true rfl)
  have h_v908 : R 1 0 0 1 v908 v908 := (r_sub hl (r_O hl) h_v907 (of_decide_eq_true rfl))
  have e_v908 : (v908 = 1 ↔ ¬v907 = 1) := e_not h_v907 (of_decide_eq_true rfl)
  have h_v909 : R 1 0 0 1 v909 v909 := (r_plt hl h_v61 h_v896 (of_decide_eq_true rfl))
  have e_v909 : (v909 = 1 ↔ sv v61 < sv v896) := e_plt h_v61 h_v896 (of_decide_eq_true rfl)
  have h_v910 : R 1 0 0 1 v910 v910 := (r_sub hl (r_O hl) h_v909 (of_decide_eq_true rfl))
  have e_v910 : (v910 = 1 ↔ ¬v909 = 1) := e_not h_v909 (of_decide_eq_true rfl)
  have h_v911 : R 1 0 0 1 v911 v911 := (r_land hl h_v907 h_v910 (of_decide_eq_true rfl))
  have e_v911 : (v911 = 1 ↔ v907 = 1 ∧ v910 = 1) := e_land h_v907 h_v910 (of_decide_eq_true rfl)
  have h_v912 : R 1 0 0 1 v912 v912 := (r_land hl h_v907 h_v909 (of_decide_eq_true rfl))
  have e_v912 : (v912 = 1 ↔ v907 = 1 ∧ v909 = 1) := e_land h_v907 h_v909 (of_decide_eq_true rfl)
  have h_v913 : R 1 0 0 1 v913 v913 := (r_plt hl h_v902 h_v61 (of_decide_eq_true rfl))
  have e_v913 : (v913 = 1 ↔ sv v902 < sv v61) := e_plt h_v902 h_v61 (of_decide_eq_true rfl)
  have h_v914 : R 1 0 0 1 v914 v914 := (r_sub hl (r_O hl) h_v913 (of_decide_eq_true rfl))
  have e_v914 : (v914 = 1 ↔ ¬v913 = 1) := e_not h_v913 (of_decide_eq_true rfl)
  have h_v915 : R 1 0 0 1 v915 v915 := (r_plt hl h_v61 h_v906 (of_decide_eq_true rfl))
  have e_v915 : (v915 = 1 ↔ sv v61 < sv v906) := e_plt h_v61 h_v906 (of_decide_eq_true rfl)
  have h_v916 : R 1 0 0 1 v916 v916 := (r_sub hl (r_O hl) h_v915 (of_decide_eq_true rfl))
  have e_v916 : (v916 = 1 ↔ ¬v915 = 1) := e_not h_v915 (of_decide_eq_true rfl)
  clear h_v904 h_v905 h_v907 h_v909 h_v910
  have h_v917 : R 1 0 0 1 v917 v917 := (r_land hl h_v913 h_v916 (of_decide_eq_true rfl))
  have e_v917 : (v917 = 1 ↔ v913 = 1 ∧ v916 = 1) := e_land h_v913 h_v916 (of_decide_eq_true rfl)
  have h_v918 : R 1 0 0 1 v918 v918 := (r_land hl h_v913 h_v915 (of_decide_eq_true rfl))
  have e_v918 : (v918 = 1 ↔ v913 = 1 ∧ v915 = 1) := e_land h_v913 h_v915 (of_decide_eq_true rfl)
  have h_v919 : R 1 0 0 1 v919 v919 := (r_land hl h_v912 h_v918 (of_decide_eq_true rfl))
  have e_v919 : (v919 = 1 ↔ v912 = 1 ∧ v918 = 1) := e_land h_v912 h_v918 (of_decide_eq_true rfl)
  have h_v920 : R 1 0 0 1 v920 v920 := (r_sub hl (r_O hl) h_v919 (of_decide_eq_true rfl))
  have e_v920 : (v920 = 1 ↔ ¬v919 = 1) := e_not h_v919 (of_decide_eq_true rfl)
  have h_v921 : R 1 0 0 1 v921 v921 := (r_lor hl h_v823 h_v920 (of_decide_eq_true rfl))
  have e_v921 : (v921 = 1 ↔ v823 = 1 ∨ v920 = 1) := e_lor h_v823 h_v920 (of_decide_eq_true rfl)
  have h_v922 : R 1 0 0 1 v922 v922 := (r_land hl h_v908 h_v918 (of_decide_eq_true rfl))
  have e_v922 : (v922 = 1 ↔ v908 = 1 ∧ v918 = 1) := e_land h_v908 h_v918 (of_decide_eq_true rfl)
  have h_v923 : R 1 0 0 1 v923 v923 := (r_lor hl h_v917 h_v922 (of_decide_eq_true rfl))
  have e_v923 : (v923 = 1 ↔ v917 = 1 ∨ v922 = 1) := e_lor h_v917 h_v922 (of_decide_eq_true rfl)
  have h_v924 : R 1 0 4611686018158952386 4611686018695823360 v924 v924 := (r_psel hl h_v923 h_v896 h_v892 (of_decide_eq_true rfl))
  have e_v924 : v924 = if v923 = 1 then v896 else v892 := e_psel h_v923 h_v896 h_v892 (of_decide_eq_true rfl)
  have h_v925 : R 1 0 0 1 v925 v925 := (r_land hl h_v912 h_v914 (of_decide_eq_true rfl))
  have e_v925 : (v925 = 1 ↔ v912 = 1 ∧ v914 = 1) := e_land h_v912 h_v914 (of_decide_eq_true rfl)
  have h_v926 : R 1 0 0 1 v926 v926 := (r_lor hl h_v911 h_v925 (of_decide_eq_true rfl))
  have e_v926 : (v926 = 1 ↔ v911 = 1 ∨ v925 = 1) := e_lor h_v911 h_v925 (of_decide_eq_true rfl)
  have h_v927 : R 1 0 4611686018158952386 4611686018695823360 v927 v927 := (r_psel hl h_v926 h_v906 h_v902 (of_decide_eq_true rfl))
  have e_v927 : v927 = if v926 = 1 then v906 else v902 := e_psel h_v926 h_v906 h_v902 (of_decide_eq_true rfl)
  have h_v934 : R 1 0 4539628407746461696 4683743645751316228 v934 v934 := (r_smx hl 30 h_v927 h_v924 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v934 : sv v934 = sv v927 * sv v924 := e_smx 30 h_v927 h_v924 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v935 : R 1 0 4611686018158952386 4611686018695823484 v935 v935 := (r_srdF hl h_v934 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  clear h_v892 h_v896 h_v902 h_v906 h_v908 h_v911 h_v912 h_v913 h_v914 h_v915 h_v916 h_v917 h_v918 h_v919 h_v920 h_v922 h_v923 h_v924 h_v925 h_v926 h_v927
  have e_v935 : sv v935 = sv v934 / 2 ^ 28 := e_srdF h_v934 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v939 : R 1 0 4611686017890516812 4611686018964258878 v939 v939 := (r_sub hl (r_add hl h_v788 h_OFFr (of_decide_eq_true rfl)) h_v935 (of_decide_eq_true rfl))
  have e_v939 : sv v939 = sv v788 - sv v935 := e_sub h_v788 h_v935 (of_decide_eq_true rfl)
  have h_v940 : R 1 0 4683743612465315840 4683743612465315840 v940 v940 := (r_c hl 4683743612465315840 (of_decide_eq_true rfl))
  have e_v940 : sv v940 = (72057594037927936) := e_c 4683743612465315840 (72057594037927936) (of_decide_eq_true rfl)
  have h_v941 : R 1 0 4611686010374323999 4683743612465315840 v941 v941 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v893 (of_decide_eq_true rfl))
  have e_v941 : sv v941 = sv v940 - sv v893 := e_sub h_v940 h_v893 (of_decide_eq_true rfl)
  have h_v942 : R 1 0 4611686018427387904 4611686018695823360 v942 v942 := (r_psqrt hl h_v941 (of_decide_eq_true rfl))
  have e_v942 : sv v942 = ((Nat.sqrt (v941 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v941 (of_decide_eq_true rfl)
  have h_v943 : R 1 0 4611686018427387905 4611686018695823361 v943 v943 := (r_sub hl (r_add hl h_v105 h_v942 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v943 : sv v943 = sv v105 + sv v942 := e_add h_v105 h_v942 (of_decide_eq_true rfl)
  have pb_v942_v874 : PB 1 v942 v874 36028797018963968 := pb_sqrt hl h_v874 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v944 : R 1 0 4611686017085210624 4647714815446351872 v944 v944 := (r_smx_pb hl 29 h_v942 h_v874 pb_v942_v874 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v944 : sv v944 = sv v942 * sv v874 := e_smx_pb 29 h_v942 h_v874 pb_v942_v874 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v945 : R 1 0 4611686018427387899 4611686018561605632 v945 v945 := (r_srdF hl h_v944 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v945 : sv v945 = sv v944 / 2 ^ 28 := e_srdF h_v944 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v946 : R 1 0 4611686018427387894 4611686018695823360 v946 v946 := (r_sub hl (r_add hl h_v945 h_v945 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v946 : sv v946 = sv v945 + sv v945 := e_add h_v945 h_v945 (of_decide_eq_true rfl)
  have pb_v943_v874 : PB 1 v943 v874 36028797287399439 := pb_sqrt1 hl h_v874 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v947 : R 1 0 4611686017085210619 4647714815714787343 v947 v947 := (r_smx_pb hl 29 h_v943 h_v874 pb_v943_v874 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v947 : sv v947 = sv v943 * sv v874 := e_smx_pb 29 h_v943 h_v874 pb_v943_v874 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v948 : R 1 0 4611686018427387899 4611686018561605634 v948 v948 := (r_srdC hl h_v947 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v948 : sv v948 = -((-sv v947) / 2 ^ 28) := e_srdC h_v947 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v949 : R 1 0 4611686018427387894 4611686018695823364 v949 v949 := (r_sub hl (r_add hl h_v948 h_v948 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v949 : sv v949 = sv v948 + sv v948 := e_add h_v948 h_v948 (of_decide_eq_true rfl)
  clear h_v788 h_v874 h_v934 h_v935 h_v941 h_v942 h_v943 pb_v942_v874 h_v944 h_v945 pb_v943_v874 h_v947 h_v948
  have h_v950 : R 1 0 0 1 v950 v950 := (r_plt hl h_v949 h_v33 (of_decide_eq_true rfl))
  have e_v950 : (v950 = 1 ↔ sv v949 < sv v33) := e_plt h_v949 h_v33 (of_decide_eq_true rfl)
  have h_v951 : R 1 0 4611686018427387894 4611686018695823364 v951 v951 := (r_psel hl h_v950 h_v949 h_v33 (of_decide_eq_true rfl))
  have e_v951 : v951 = if v950 = 1 then v949 else v33 := e_psel h_v950 h_v949 h_v33 (of_decide_eq_true rfl)
  have h_v952 : R 1 0 4611686010374323999 4683743612465315840 v952 v952 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v887 (of_decide_eq_true rfl))
  have e_v952 : sv v952 = sv v940 - sv v887 := e_sub h_v940 h_v887 (of_decide_eq_true rfl)
  have h_v953 : R 1 0 4611686018427387904 4611686018695823360 v953 v953 := (r_psqrt hl h_v952 (of_decide_eq_true rfl))
  have e_v953 : sv v953 = ((Nat.sqrt (v952 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v952 (of_decide_eq_true rfl)
  have h_v954 : R 1 0 4611686018427387905 4611686018695823361 v954 v954 := (r_sub hl (r_add hl h_v105 h_v953 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v954 : sv v954 = sv v105 + sv v953 := e_add h_v105 h_v953 (of_decide_eq_true rfl)
  have pb_v953_v875 : PB 1 v953 v875 36028797018963968 := pb_sqrt hl h_v875 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v955 : R 1 0 4611686017085210624 4647714815446351872 v955 v955 := (r_smx_pb hl 29 h_v953 h_v875 pb_v953_v875 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v955 : sv v955 = sv v953 * sv v875 := e_smx_pb 29 h_v953 h_v875 pb_v953_v875 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v956 : R 1 0 4611686018427387899 4611686018561605632 v956 v956 := (r_srdF hl h_v955 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v956 : sv v956 = sv v955 / 2 ^ 28 := e_srdF h_v955 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v957 : R 1 0 4611686018427387894 4611686018695823360 v957 v957 := (r_sub hl (r_add hl h_v956 h_v956 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v957 : sv v957 = sv v956 + sv v956 := e_add h_v956 h_v956 (of_decide_eq_true rfl)
  have pb_v954_v875 : PB 1 v954 v875 36028797287399439 := pb_sqrt1 hl h_v875 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v958 : R 1 0 4611686017085210619 4647714815714787343 v958 v958 := (r_smx_pb hl 29 h_v954 h_v875 pb_v954_v875 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v958 : sv v958 = sv v954 * sv v875 := e_smx_pb 29 h_v954 h_v875 pb_v954_v875 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v959 : R 1 0 4611686018427387899 4611686018561605634 v959 v959 := (r_srdC hl h_v958 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v959 : sv v959 = -((-sv v958) / 2 ^ 28) := e_srdC h_v958 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v960 : R 1 0 4611686018427387894 4611686018695823364 v960 v960 := (r_sub hl (r_add hl h_v959 h_v959 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v960 : sv v960 = sv v959 + sv v959 := e_add h_v959 h_v959 (of_decide_eq_true rfl)
  have h_v961 : R 1 0 0 1 v961 v961 := (r_plt hl h_v960 h_v33 (of_decide_eq_true rfl))
  clear h_v875 h_v949 h_v950 h_v952 h_v953 h_v954 pb_v953_v875 h_v955 h_v956 pb_v954_v875 h_v958 h_v959
  have e_v961 : (v961 = 1 ↔ sv v960 < sv v33) := e_plt h_v960 h_v33 (of_decide_eq_true rfl)
  have h_v962 : R 1 0 4611686018427387894 4611686018695823364 v962 v962 := (r_psel hl h_v961 h_v960 h_v33 (of_decide_eq_true rfl))
  have e_v962 : v962 = if v961 = 1 then v960 else v33 := e_psel h_v961 h_v960 h_v33 (of_decide_eq_true rfl)
  have h_v963 : R 1 0 0 1 v963 v963 := (r_plt hl h_v946 h_v957 (of_decide_eq_true rfl))
  have e_v963 : (v963 = 1 ↔ sv v946 < sv v957) := e_plt h_v946 h_v957 (of_decide_eq_true rfl)
  have h_v964 : R 1 0 4611686018427387894 4611686018695823360 v964 v964 := (r_psel hl h_v963 h_v946 h_v957 (of_decide_eq_true rfl))
  have e_v964 : v964 = if v963 = 1 then v946 else v957 := e_psel h_v963 h_v946 h_v957 (of_decide_eq_true rfl)
  have h_v965 : R 1 0 0 1 v965 v965 := (r_plt hl h_v951 h_v962 (of_decide_eq_true rfl))
  have e_v965 : (v965 = 1 ↔ sv v951 < sv v962) := e_plt h_v951 h_v962 (of_decide_eq_true rfl)
  have h_v966 : R 1 0 4611686018427387894 4611686018695823364 v966 v966 := (r_psel hl h_v965 h_v962 h_v951 (of_decide_eq_true rfl))
  have e_v966 : v966 = if v965 = 1 then v962 else v951 := e_psel h_v965 h_v962 h_v951 (of_decide_eq_true rfl)
  have h_v967 : R 1 0 4647714815446351872 4647714815446351872 v967 v967 := (r_c hl 4647714815446351872 (of_decide_eq_true rfl))
  have e_v967 : sv v967 = (36028797018963968) := e_c 4647714815446351872 (36028797018963968) (of_decide_eq_true rfl)
  have h_v968 : R 1 0 0 1 v968 v968 := (r_plt hl h_v967 h_v893 (of_decide_eq_true rfl))
  have e_v968 : (v968 = 1 ↔ sv v967 < sv v893) := e_plt h_v967 h_v893 (of_decide_eq_true rfl)
  have h_v969 : R 1 0 0 1 v969 v969 := (r_sub hl (r_O hl) h_v968 (of_decide_eq_true rfl))
  have e_v969 : (v969 = 1 ↔ ¬v968 = 1) := e_not h_v968 (of_decide_eq_true rfl)
  have h_v970 : R 1 0 0 1 v970 v970 := (r_plt hl h_v887 h_v967 (of_decide_eq_true rfl))
  have e_v970 : (v970 = 1 ↔ sv v887 < sv v967) := e_plt h_v887 h_v967 (of_decide_eq_true rfl)
  have h_v971 : R 1 0 0 1 v971 v971 := (r_sub hl (r_O hl) h_v970 (of_decide_eq_true rfl))
  have e_v971 : (v971 = 1 ↔ ¬v970 = 1) := e_not h_v970 (of_decide_eq_true rfl)
  have h_v972 : R 1 0 0 1 v972 v972 := (r_land hl h_v969 h_v971 (of_decide_eq_true rfl))
  have e_v972 : (v972 = 1 ↔ v969 = 1 ∧ v971 = 1) := e_land h_v969 h_v971 (of_decide_eq_true rfl)
  have h_v973 : R 1 0 4611686018427387894 4611686018695823364 v973 v973 := (r_psel hl h_v972 h_v33 h_v966 (of_decide_eq_true rfl))
  have e_v973 : v973 = if v972 = 1 then v33 else v966 := e_psel h_v972 h_v33 h_v966 (of_decide_eq_true rfl)
  clear h_v887 h_v893 h_v946 h_v951 h_v957 h_v960 h_v961 h_v962 h_v963 h_v965 h_v966 h_v968 h_v969 h_v970 h_v971 h_v972
  have h_v974 : R 1 0 4611686010374323999 4683743612465315840 v974 v974 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v903 (of_decide_eq_true rfl))
  have e_v974 : sv v974 = sv v940 - sv v903 := e_sub h_v940 h_v903 (of_decide_eq_true rfl)
  have h_v975 : R 1 0 4611686018427387904 4611686018695823360 v975 v975 := (r_psqrt hl h_v974 (of_decide_eq_true rfl))
  have e_v975 : sv v975 = ((Nat.sqrt (v974 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v974 (of_decide_eq_true rfl)
  have h_v976 : R 1 0 4611686018427387905 4611686018695823361 v976 v976 := (r_sub hl (r_add hl h_v105 h_v975 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v976 : sv v976 = sv v105 + sv v975 := e_add h_v105 h_v975 (of_decide_eq_true rfl)
  have pb_v975_v878 : PB 1 v975 v878 36028797018963968 := pb_sqrt hl h_v878 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v977 : R 1 0 4611686017085210624 4647714815446351872 v977 v977 := (r_smx_pb hl 29 h_v975 h_v878 pb_v975_v878 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v977 : sv v977 = sv v975 * sv v878 := e_smx_pb 29 h_v975 h_v878 pb_v975_v878 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v978 : R 1 0 4611686018427387899 4611686018561605632 v978 v978 := (r_srdF hl h_v977 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v978 : sv v978 = sv v977 / 2 ^ 28 := e_srdF h_v977 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v979 : R 1 0 4611686018427387894 4611686018695823360 v979 v979 := (r_sub hl (r_add hl h_v978 h_v978 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v979 : sv v979 = sv v978 + sv v978 := e_add h_v978 h_v978 (of_decide_eq_true rfl)
  have pb_v976_v878 : PB 1 v976 v878 36028797287399439 := pb_sqrt1 hl h_v878 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v980 : R 1 0 4611686017085210619 4647714815714787343 v980 v980 := (r_smx_pb hl 29 h_v976 h_v878 pb_v976_v878 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v980 : sv v980 = sv v976 * sv v878 := e_smx_pb 29 h_v976 h_v878 pb_v976_v878 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v981 : R 1 0 4611686018427387899 4611686018561605634 v981 v981 := (r_srdC hl h_v980 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v981 : sv v981 = -((-sv v980) / 2 ^ 28) := e_srdC h_v980 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v982 : R 1 0 4611686018427387894 4611686018695823364 v982 v982 := (r_sub hl (r_add hl h_v981 h_v981 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v982 : sv v982 = sv v981 + sv v981 := e_add h_v981 h_v981 (of_decide_eq_true rfl)
  have h_v983 : R 1 0 0 1 v983 v983 := (r_plt hl h_v982 h_v33 (of_decide_eq_true rfl))
  have e_v983 : (v983 = 1 ↔ sv v982 < sv v33) := e_plt h_v982 h_v33 (of_decide_eq_true rfl)
  have h_v984 : R 1 0 4611686018427387894 4611686018695823364 v984 v984 := (r_psel hl h_v983 h_v982 h_v33 (of_decide_eq_true rfl))
  have e_v984 : v984 = if v983 = 1 then v982 else v33 := e_psel h_v983 h_v982 h_v33 (of_decide_eq_true rfl)
  have h_v985 : R 1 0 4611686010374323999 4683743612465315840 v985 v985 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v897 (of_decide_eq_true rfl))
  clear h_v878 h_v974 h_v975 h_v976 pb_v975_v878 h_v977 h_v978 pb_v976_v878 h_v980 h_v981 h_v982 h_v983
  have e_v985 : sv v985 = sv v940 - sv v897 := e_sub h_v940 h_v897 (of_decide_eq_true rfl)
  have h_v986 : R 1 0 4611686018427387904 4611686018695823360 v986 v986 := (r_psqrt hl h_v985 (of_decide_eq_true rfl))
  have e_v986 : sv v986 = ((Nat.sqrt (v985 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v985 (of_decide_eq_true rfl)
  have h_v987 : R 1 0 4611686018427387905 4611686018695823361 v987 v987 := (r_sub hl (r_add hl h_v105 h_v986 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v987 : sv v987 = sv v105 + sv v986 := e_add h_v105 h_v986 (of_decide_eq_true rfl)
  have pb_v986_v879 : PB 1 v986 v879 36028797018963968 := pb_sqrt hl h_v879 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v988 : R 1 0 4611686017085210624 4647714815446351872 v988 v988 := (r_smx_pb hl 29 h_v986 h_v879 pb_v986_v879 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v988 : sv v988 = sv v986 * sv v879 := e_smx_pb 29 h_v986 h_v879 pb_v986_v879 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v989 : R 1 0 4611686018427387899 4611686018561605632 v989 v989 := (r_srdF hl h_v988 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v989 : sv v989 = sv v988 / 2 ^ 28 := e_srdF h_v988 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v990 : R 1 0 4611686018427387894 4611686018695823360 v990 v990 := (r_sub hl (r_add hl h_v989 h_v989 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v990 : sv v990 = sv v989 + sv v989 := e_add h_v989 h_v989 (of_decide_eq_true rfl)
  have pb_v987_v879 : PB 1 v987 v879 36028797287399439 := pb_sqrt1 hl h_v879 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v991 : R 1 0 4611686017085210619 4647714815714787343 v991 v991 := (r_smx_pb hl 29 h_v987 h_v879 pb_v987_v879 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v991 : sv v991 = sv v987 * sv v879 := e_smx_pb 29 h_v987 h_v879 pb_v987_v879 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v992 : R 1 0 4611686018427387899 4611686018561605634 v992 v992 := (r_srdC hl h_v991 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v992 : sv v992 = -((-sv v991) / 2 ^ 28) := e_srdC h_v991 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v993 : R 1 0 4611686018427387894 4611686018695823364 v993 v993 := (r_sub hl (r_add hl h_v992 h_v992 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v993 : sv v993 = sv v992 + sv v992 := e_add h_v992 h_v992 (of_decide_eq_true rfl)
  have h_v994 : R 1 0 0 1 v994 v994 := (r_plt hl h_v993 h_v33 (of_decide_eq_true rfl))
  have e_v994 : (v994 = 1 ↔ sv v993 < sv v33) := e_plt h_v993 h_v33 (of_decide_eq_true rfl)
  have h_v995 : R 1 0 4611686018427387894 4611686018695823364 v995 v995 := (r_psel hl h_v994 h_v993 h_v33 (of_decide_eq_true rfl))
  have e_v995 : v995 = if v994 = 1 then v993 else v33 := e_psel h_v994 h_v993 h_v33 (of_decide_eq_true rfl)
  have h_v996 : R 1 0 0 1 v996 v996 := (r_plt hl h_v979 h_v990 (of_decide_eq_true rfl))
  have e_v996 : (v996 = 1 ↔ sv v979 < sv v990) := e_plt h_v979 h_v990 (of_decide_eq_true rfl)
  clear h_v879 h_v985 h_v986 h_v987 pb_v986_v879 h_v988 h_v989 pb_v987_v879 h_v991 h_v992 h_v993 h_v994
  have h_v997 : R 1 0 4611686018427387894 4611686018695823360 v997 v997 := (r_psel hl h_v996 h_v979 h_v990 (of_decide_eq_true rfl))
  have e_v997 : v997 = if v996 = 1 then v979 else v990 := e_psel h_v996 h_v979 h_v990 (of_decide_eq_true rfl)
  have h_v998 : R 1 0 0 1 v998 v998 := (r_plt hl h_v984 h_v995 (of_decide_eq_true rfl))
  have e_v998 : (v998 = 1 ↔ sv v984 < sv v995) := e_plt h_v984 h_v995 (of_decide_eq_true rfl)
  have h_v999 : R 1 0 4611686018427387894 4611686018695823364 v999 v999 := (r_psel hl h_v998 h_v995 h_v984 (of_decide_eq_true rfl))
  have e_v999 : v999 = if v998 = 1 then v995 else v984 := e_psel h_v998 h_v995 h_v984 (of_decide_eq_true rfl)
  have h_v1000 : R 1 0 0 1 v1000 v1000 := (r_plt hl h_v967 h_v903 (of_decide_eq_true rfl))
  have e_v1000 : (v1000 = 1 ↔ sv v967 < sv v903) := e_plt h_v967 h_v903 (of_decide_eq_true rfl)
  have h_v1001 : R 1 0 0 1 v1001 v1001 := (r_sub hl (r_O hl) h_v1000 (of_decide_eq_true rfl))
  have e_v1001 : (v1001 = 1 ↔ ¬v1000 = 1) := e_not h_v1000 (of_decide_eq_true rfl)
  have h_v1002 : R 1 0 0 1 v1002 v1002 := (r_plt hl h_v897 h_v967 (of_decide_eq_true rfl))
  have e_v1002 : (v1002 = 1 ↔ sv v897 < sv v967) := e_plt h_v897 h_v967 (of_decide_eq_true rfl)
  have h_v1003 : R 1 0 0 1 v1003 v1003 := (r_sub hl (r_O hl) h_v1002 (of_decide_eq_true rfl))
  have e_v1003 : (v1003 = 1 ↔ ¬v1002 = 1) := e_not h_v1002 (of_decide_eq_true rfl)
  have h_v1004 : R 1 0 0 1 v1004 v1004 := (r_land hl h_v1001 h_v1003 (of_decide_eq_true rfl))
  have e_v1004 : (v1004 = 1 ↔ v1001 = 1 ∧ v1003 = 1) := e_land h_v1001 h_v1003 (of_decide_eq_true rfl)
  have h_v1005 : R 1 0 4611686018427387894 4611686018695823364 v1005 v1005 := (r_psel hl h_v1004 h_v33 h_v999 (of_decide_eq_true rfl))
  have e_v1005 : v1005 = if v1004 = 1 then v33 else v999 := e_psel h_v1004 h_v33 h_v999 (of_decide_eq_true rfl)
  have h_v1006 : R 1 0 0 1 v1006 v1006 := (r_plt hl h_v964 h_v61 (of_decide_eq_true rfl))
  have e_v1006 : (v1006 = 1 ↔ sv v964 < sv v61) := e_plt h_v964 h_v61 (of_decide_eq_true rfl)
  have h_v1007 : R 1 0 0 1 v1007 v1007 := (r_sub hl (r_O hl) h_v1006 (of_decide_eq_true rfl))
  have e_v1007 : (v1007 = 1 ↔ ¬v1006 = 1) := e_not h_v1006 (of_decide_eq_true rfl)
  have h_v1008 : R 1 0 0 1 v1008 v1008 := (r_plt hl h_v61 h_v973 (of_decide_eq_true rfl))
  have e_v1008 : (v1008 = 1 ↔ sv v61 < sv v973) := e_plt h_v61 h_v973 (of_decide_eq_true rfl)
  have h_v1009 : R 1 0 0 1 v1009 v1009 := (r_sub hl (r_O hl) h_v1008 (of_decide_eq_true rfl))
  clear h_v897 h_v903 h_v979 h_v984 h_v990 h_v995 h_v996 h_v998 h_v999 h_v1000 h_v1001 h_v1002 h_v1003 h_v1004
  have e_v1009 : (v1009 = 1 ↔ ¬v1008 = 1) := e_not h_v1008 (of_decide_eq_true rfl)
  have h_v1010 : R 1 0 0 1 v1010 v1010 := (r_land hl h_v1006 h_v1009 (of_decide_eq_true rfl))
  have e_v1010 : (v1010 = 1 ↔ v1006 = 1 ∧ v1009 = 1) := e_land h_v1006 h_v1009 (of_decide_eq_true rfl)
  have h_v1011 : R 1 0 0 1 v1011 v1011 := (r_land hl h_v1006 h_v1008 (of_decide_eq_true rfl))
  have e_v1011 : (v1011 = 1 ↔ v1006 = 1 ∧ v1008 = 1) := e_land h_v1006 h_v1008 (of_decide_eq_true rfl)
  have h_v1012 : R 1 0 0 1 v1012 v1012 := (r_plt hl h_v997 h_v61 (of_decide_eq_true rfl))
  have e_v1012 : (v1012 = 1 ↔ sv v997 < sv v61) := e_plt h_v997 h_v61 (of_decide_eq_true rfl)
  have h_v1013 : R 1 0 0 1 v1013 v1013 := (r_sub hl (r_O hl) h_v1012 (of_decide_eq_true rfl))
  have e_v1013 : (v1013 = 1 ↔ ¬v1012 = 1) := e_not h_v1012 (of_decide_eq_true rfl)
  have h_v1014 : R 1 0 0 1 v1014 v1014 := (r_plt hl h_v61 h_v1005 (of_decide_eq_true rfl))
  have e_v1014 : (v1014 = 1 ↔ sv v61 < sv v1005) := e_plt h_v61 h_v1005 (of_decide_eq_true rfl)
  have h_v1015 : R 1 0 0 1 v1015 v1015 := (r_sub hl (r_O hl) h_v1014 (of_decide_eq_true rfl))
  have e_v1015 : (v1015 = 1 ↔ ¬v1014 = 1) := e_not h_v1014 (of_decide_eq_true rfl)
  have h_v1016 : R 1 0 0 1 v1016 v1016 := (r_land hl h_v1012 h_v1015 (of_decide_eq_true rfl))
  have e_v1016 : (v1016 = 1 ↔ v1012 = 1 ∧ v1015 = 1) := e_land h_v1012 h_v1015 (of_decide_eq_true rfl)
  have h_v1017 : R 1 0 0 1 v1017 v1017 := (r_land hl h_v1012 h_v1014 (of_decide_eq_true rfl))
  have e_v1017 : (v1017 = 1 ↔ v1012 = 1 ∧ v1014 = 1) := e_land h_v1012 h_v1014 (of_decide_eq_true rfl)
  have h_v1018 : R 1 0 0 1 v1018 v1018 := (r_land hl h_v1011 h_v1017 (of_decide_eq_true rfl))
  have e_v1018 : (v1018 = 1 ↔ v1011 = 1 ∧ v1017 = 1) := e_land h_v1011 h_v1017 (of_decide_eq_true rfl)
  have h_v1019 : R 1 0 0 1 v1019 v1019 := (r_sub hl (r_O hl) h_v1018 (of_decide_eq_true rfl))
  have e_v1019 : (v1019 = 1 ↔ ¬v1018 = 1) := e_not h_v1018 (of_decide_eq_true rfl)
  have h_v1020 : R 1 0 0 1 v1020 v1020 := (r_lor hl h_v823 h_v1019 (of_decide_eq_true rfl))
  have e_v1020 : (v1020 = 1 ↔ v823 = 1 ∨ v1019 = 1) := e_lor h_v823 h_v1019 (of_decide_eq_true rfl)
  have h_v1021 : R 1 0 0 1 v1021 v1021 := (r_land hl h_v1007 h_v1017 (of_decide_eq_true rfl))
  have e_v1021 : (v1021 = 1 ↔ v1007 = 1 ∧ v1017 = 1) := e_land h_v1007 h_v1017 (of_decide_eq_true rfl)
  clear h_v1006 h_v1007 h_v1008 h_v1009 h_v1012 h_v1014 h_v1015 h_v1018 h_v1019
  have h_v1022 : R 1 0 0 1 v1022 v1022 := (r_lor hl h_v1016 h_v1021 (of_decide_eq_true rfl))
  have e_v1022 : (v1022 = 1 ↔ v1016 = 1 ∨ v1021 = 1) := e_lor h_v1016 h_v1021 (of_decide_eq_true rfl)
  have h_v1023 : R 1 0 4611686018427387894 4611686018695823364 v1023 v1023 := (r_psel hl h_v1022 h_v973 h_v964 (of_decide_eq_true rfl))
  have e_v1023 : v1023 = if v1022 = 1 then v973 else v964 := e_psel h_v1022 h_v973 h_v964 (of_decide_eq_true rfl)
  have h_v1024 : R 1 0 0 1 v1024 v1024 := (r_land hl h_v1011 h_v1013 (of_decide_eq_true rfl))
  have e_v1024 : (v1024 = 1 ↔ v1011 = 1 ∧ v1013 = 1) := e_land h_v1011 h_v1013 (of_decide_eq_true rfl)
  have h_v1025 : R 1 0 0 1 v1025 v1025 := (r_lor hl h_v1010 h_v1024 (of_decide_eq_true rfl))
  have e_v1025 : (v1025 = 1 ↔ v1010 = 1 ∨ v1024 = 1) := e_lor h_v1010 h_v1024 (of_decide_eq_true rfl)
  have h_v1026 : R 1 0 4611686018427387894 4611686018695823364 v1026 v1026 := (r_psel hl h_v1025 h_v1005 h_v997 (of_decide_eq_true rfl))
  have e_v1026 : v1026 = if v1025 = 1 then v1005 else v997 := e_psel h_v1025 h_v1005 h_v997 (of_decide_eq_true rfl)
  have h_v1027 : R 1 0 0 1 v1027 v1027 := (r_land hl h_v1010 h_v1017 (of_decide_eq_true rfl))
  have e_v1027 : (v1027 = 1 ↔ v1010 = 1 ∧ v1017 = 1) := e_land h_v1010 h_v1017 (of_decide_eq_true rfl)
  have h_v1028 : R 1 0 0 1 v1028 v1028 := (r_lor hl h_v1016 h_v1027 (of_decide_eq_true rfl))
  have e_v1028 : (v1028 = 1 ↔ v1016 = 1 ∨ v1027 = 1) := e_lor h_v1016 h_v1027 (of_decide_eq_true rfl)
  have h_v1029 : R 1 0 4611686018427387894 4611686018695823364 v1029 v1029 := (r_psel hl h_v1028 h_v964 h_v973 (of_decide_eq_true rfl))
  have e_v1029 : v1029 = if v1028 = 1 then v964 else v973 := e_psel h_v1028 h_v964 h_v973 (of_decide_eq_true rfl)
  have h_v1030 : R 1 0 0 1 v1030 v1030 := (r_land hl h_v1011 h_v1016 (of_decide_eq_true rfl))
  have e_v1030 : (v1030 = 1 ↔ v1011 = 1 ∧ v1016 = 1) := e_land h_v1011 h_v1016 (of_decide_eq_true rfl)
  have h_v1031 : R 1 0 0 1 v1031 v1031 := (r_lor hl h_v1010 h_v1030 (of_decide_eq_true rfl))
  have e_v1031 : (v1031 = 1 ↔ v1010 = 1 ∨ v1030 = 1) := e_lor h_v1010 h_v1030 (of_decide_eq_true rfl)
  have h_v1032 : R 1 0 4611686018427387894 4611686018695823364 v1032 v1032 := (r_psel hl h_v1031 h_v997 h_v1005 (of_decide_eq_true rfl))
  have e_v1032 : v1032 = if v1031 = 1 then v997 else v1005 := e_psel h_v1031 h_v997 h_v1005 (of_decide_eq_true rfl)
  have h_v1033 : R 1 0 4611686015743033304 4683743614612799504 v1033 v1033 := (r_smx hl 29 h_v1026 h_v1023 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1033 : sv v1033 = sv v1026 * sv v1023 := e_smx 29 h_v1026 h_v1023 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1034 : R 1 0 4611686018427387893 4611686018695823368 v1034 v1034 := (r_srdF hl h_v1033 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  clear h_v964 h_v973 h_v997 h_v1005 h_v1010 h_v1011 h_v1013 h_v1016 h_v1017 h_v1021 h_v1022 h_v1023 h_v1024 h_v1025 h_v1026 h_v1027 h_v1028 h_v1030 h_v1031
  have e_v1034 : sv v1034 = sv v1033 / 2 ^ 28 := e_srdF h_v1033 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v1035 : R 1 0 4611686015743033304 4683743614612799504 v1035 v1035 := (r_smx hl 29 h_v1032 h_v1029 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1035 : sv v1035 = sv v1032 * sv v1029 := e_smx 29 h_v1032 h_v1029 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1036 : R 1 0 4611686018427387894 4611686018695823369 v1036 v1036 := (r_srdC hl h_v1035 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v1036 : sv v1036 = -((-sv v1035) / 2 ^ 28) := e_srdC h_v1035 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1037 : R 1 0 0 1 v1037 v1037 := (r_plt hl h_v61 h_v1034 (of_decide_eq_true rfl))
  have e_v1037 : (v1037 = 1 ↔ sv v61 < sv v1034) := e_plt h_v61 h_v1034 (of_decide_eq_true rfl)
  have h_v1038 : R 1 0 0 1 v1038 v1038 := (r_sub hl (r_O hl) h_v1037 (of_decide_eq_true rfl))
  have e_v1038 : (v1038 = 1 ↔ ¬v1037 = 1) := e_not h_v1037 (of_decide_eq_true rfl)
  have h_v1041 : R 1 0 0 1 v1041 v1041 := (r_plt hl h_v939 h_v61 (of_decide_eq_true rfl))
  have e_v1041 : (v1041 = 1 ↔ sv v939 < sv v61) := e_plt h_v939 h_v61 (of_decide_eq_true rfl)
  have h_v1042 : R 1 0 4611686018427387893 4611686018695823369 v1042 v1042 := (r_psel hl h_v1041 h_v1036 h_v1034 (of_decide_eq_true rfl))
  have e_v1042 : v1042 = if v1041 = 1 then v1036 else v1034 := e_psel h_v1041 h_v1036 h_v1034 (of_decide_eq_true rfl)
  have h_v1043 : R 1 0 4611686018158952439 4611686018427387915 v1043 v1043 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v1042 (of_decide_eq_true rfl))
  have e_v1043 : sv v1043 = sv v61 - sv v1042 := e_sub h_v61 h_v1042 (of_decide_eq_true rfl)
  have h_v1044 : R 1 0 0 1 v1044 v1044 := (r_plt hl h_v939 h_v1043 (of_decide_eq_true rfl))
  have e_v1044 : (v1044 = 1 ↔ sv v939 < sv v1043) := e_plt h_v939 h_v1043 (of_decide_eq_true rfl)
  have h_v1045 : R 1 0 0 1 v1045 v1045 := (r_land hl h_v1037 h_v1044 (of_decide_eq_true rfl))
  have e_v1045 : (v1045 = 1 ↔ v1037 = 1 ∧ v1044 = 1) := e_land h_v1037 h_v1044 (of_decide_eq_true rfl)
  have h_v1046 : R 1 0 0 1 v1046 v1046 := (r_plt hl h_v939 h_v1042 (of_decide_eq_true rfl))
  have e_v1046 : (v1046 = 1 ↔ sv v939 < sv v1042) := e_plt h_v939 h_v1042 (of_decide_eq_true rfl)
  have h_v1047 : R 1 0 0 1 v1047 v1047 := (r_sub hl (r_O hl) h_v1046 (of_decide_eq_true rfl))
  have e_v1047 : (v1047 = 1 ↔ ¬v1046 = 1) := e_not h_v1046 (of_decide_eq_true rfl)
  have h_v1048 : R 1 0 0 1 v1048 v1048 := (r_lor hl h_v1038 h_v1047 (of_decide_eq_true rfl))
  have e_v1048 : (v1048 = 1 ↔ v1038 = 1 ∨ v1047 = 1) := e_lor h_v1038 h_v1047 (of_decide_eq_true rfl)
  clear h_v1029 h_v1032 h_v1033 h_v1034 h_v1035 h_v1036 h_v1037 h_v1038 h_v1041 h_v1043 h_v1044 h_v1046 h_v1047
  have h_v1049 : R 1 0 4611686017890516812 4611686018964258878 v1049 v1049 := (r_psel hl h_v1048 h_v33 h_v939 (of_decide_eq_true rfl))
  have e_v1049 : v1049 = if v1048 = 1 then v33 else v939 := e_psel h_v1048 h_v33 h_v939 (of_decide_eq_true rfl)
  have h_v1050 : R 1 0 4611686018427387893 4611686018695823369 v1050 v1050 := (r_psel hl h_v1048 h_v33 h_v1042 (of_decide_eq_true rfl))
  have e_v1050 : v1050 = if v1048 = 1 then v33 else v1042 := e_psel h_v1048 h_v33 h_v1042 (of_decide_eq_true rfl)
  have h_v1054 : R 1 0 4611686018427387904 4683743620518379745 v1054 v1054 := (r_smx_sq hl 29 h_v877 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1054 : sv v1054 = sv v877 * sv v877 := e_smx_sq 29 h_v877 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1055 : R 1 0 4611686018427387904 4611686018695823391 v1055 v1055 := (r_srdC hl h_v1054 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1055 : sv v1055 = -((-sv v1054) / 2 ^ 28) := e_srdC h_v1054 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1056 : R 1 0 4611686018427387904 4611686018964258878 v1056 v1056 := (r_sub hl (r_add hl h_v1055 h_v1055 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1056 : sv v1056 = sv v1055 + sv v1055 := e_add h_v1055 h_v1055 (of_decide_eq_true rfl)
  have h_v1057 : R 1 0 4611686018158952386 4611686018695823360 v1057 v1057 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1056 (of_decide_eq_true rfl))
  have e_v1057 : sv v1057 = sv v33 - sv v1056 := e_sub h_v33 h_v1056 (of_decide_eq_true rfl)
  have h_v1058 : R 1 0 0 1 v1058 v1058 := (r_plt hl h_v1057 h_v95 (of_decide_eq_true rfl))
  have e_v1058 : (v1058 = 1 ↔ sv v1057 < sv v95) := e_plt h_v1057 h_v95 (of_decide_eq_true rfl)
  have h_v1059 : R 1 0 4611686018158952386 4611686018695823360 v1059 v1059 := (r_psel hl h_v1058 h_v95 h_v1057 (of_decide_eq_true rfl))
  have e_v1059 : v1059 = if v1058 = 1 then v95 else v1057 := e_psel h_v1058 h_v95 h_v1057 (of_decide_eq_true rfl)
  have h_v1060 : R 1 0 4611686018427387904 4683743620518379745 v1060 v1060 := (r_smx_sq hl 29 h_v876 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1060 : sv v1060 = sv v876 * sv v876 := e_smx_sq 29 h_v876 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1061 : R 1 0 4611686018427387904 4611686018695823390 v1061 v1061 := (r_srdF hl h_v1060 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1061 : sv v1061 = sv v1060 / 2 ^ 28 := e_srdF h_v1060 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1062 : R 1 0 4611686018427387904 4611686018964258876 v1062 v1062 := (r_sub hl (r_add hl h_v1061 h_v1061 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1062 : sv v1062 = sv v1061 + sv v1061 := e_add h_v1061 h_v1061 (of_decide_eq_true rfl)
  have h_v1063 : R 1 0 4611686018158952388 4611686018695823360 v1063 v1063 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1062 (of_decide_eq_true rfl))
  have e_v1063 : sv v1063 = sv v33 - sv v1062 := e_sub h_v33 h_v1062 (of_decide_eq_true rfl)
  have h_v1064 : R 1 0 4611686018427387904 4683743620518379745 v1064 v1064 := (r_smx_sq hl 29 h_v881 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  clear h_v939 h_v1042 h_v1048 h_v1055 h_v1056 h_v1057 h_v1058 h_v1061 h_v1062
  have e_v1064 : sv v1064 = sv v881 * sv v881 := e_smx_sq 29 h_v881 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1065 : R 1 0 4611686018427387904 4611686018695823391 v1065 v1065 := (r_srdC hl h_v1064 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1065 : sv v1065 = -((-sv v1064) / 2 ^ 28) := e_srdC h_v1064 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1066 : R 1 0 4611686018427387904 4611686018964258878 v1066 v1066 := (r_sub hl (r_add hl h_v1065 h_v1065 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1066 : sv v1066 = sv v1065 + sv v1065 := e_add h_v1065 h_v1065 (of_decide_eq_true rfl)
  have h_v1067 : R 1 0 4611686018158952386 4611686018695823360 v1067 v1067 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1066 (of_decide_eq_true rfl))
  have e_v1067 : sv v1067 = sv v33 - sv v1066 := e_sub h_v33 h_v1066 (of_decide_eq_true rfl)
  have h_v1068 : R 1 0 0 1 v1068 v1068 := (r_plt hl h_v1067 h_v95 (of_decide_eq_true rfl))
  have e_v1068 : (v1068 = 1 ↔ sv v1067 < sv v95) := e_plt h_v1067 h_v95 (of_decide_eq_true rfl)
  have h_v1069 : R 1 0 4611686018158952386 4611686018695823360 v1069 v1069 := (r_psel hl h_v1068 h_v95 h_v1067 (of_decide_eq_true rfl))
  have e_v1069 : v1069 = if v1068 = 1 then v95 else v1067 := e_psel h_v1068 h_v95 h_v1067 (of_decide_eq_true rfl)
  have h_v1070 : R 1 0 4611686018427387904 4683743620518379745 v1070 v1070 := (r_smx_sq hl 29 h_v880 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1070 : sv v1070 = sv v880 * sv v880 := e_smx_sq 29 h_v880 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1071 : R 1 0 4611686018427387904 4611686018695823390 v1071 v1071 := (r_srdF hl h_v1070 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1071 : sv v1071 = sv v1070 / 2 ^ 28 := e_srdF h_v1070 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1072 : R 1 0 4611686018427387904 4611686018964258876 v1072 v1072 := (r_sub hl (r_add hl h_v1071 h_v1071 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1072 : sv v1072 = sv v1071 + sv v1071 := e_add h_v1071 h_v1071 (of_decide_eq_true rfl)
  have h_v1073 : R 1 0 4611686018158952388 4611686018695823360 v1073 v1073 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1072 (of_decide_eq_true rfl))
  have e_v1073 : sv v1073 = sv v33 - sv v1072 := e_sub h_v33 h_v1072 (of_decide_eq_true rfl)
  have h_v1074 : R 1 0 0 1 v1074 v1074 := (r_plt hl h_v1059 h_v61 (of_decide_eq_true rfl))
  have e_v1074 : (v1074 = 1 ↔ sv v1059 < sv v61) := e_plt h_v1059 h_v61 (of_decide_eq_true rfl)
  have h_v1076 : R 1 0 0 1 v1076 v1076 := (r_plt hl h_v61 h_v1063 (of_decide_eq_true rfl))
  have e_v1076 : (v1076 = 1 ↔ sv v61 < sv v1063) := e_plt h_v61 h_v1063 (of_decide_eq_true rfl)
  have h_v1077 : R 1 0 0 1 v1077 v1077 := (r_sub hl (r_O hl) h_v1076 (of_decide_eq_true rfl))
  have e_v1077 : (v1077 = 1 ↔ ¬v1076 = 1) := e_not h_v1076 (of_decide_eq_true rfl)
  clear h_v1065 h_v1066 h_v1067 h_v1068 h_v1071 h_v1072
  have h_v1078 : R 1 0 0 1 v1078 v1078 := (r_land hl h_v1074 h_v1077 (of_decide_eq_true rfl))
  have e_v1078 : (v1078 = 1 ↔ v1074 = 1 ∧ v1077 = 1) := e_land h_v1074 h_v1077 (of_decide_eq_true rfl)
  have h_v1079 : R 1 0 0 1 v1079 v1079 := (r_land hl h_v1074 h_v1076 (of_decide_eq_true rfl))
  have e_v1079 : (v1079 = 1 ↔ v1074 = 1 ∧ v1076 = 1) := e_land h_v1074 h_v1076 (of_decide_eq_true rfl)
  have h_v1080 : R 1 0 0 1 v1080 v1080 := (r_plt hl h_v1069 h_v61 (of_decide_eq_true rfl))
  have e_v1080 : (v1080 = 1 ↔ sv v1069 < sv v61) := e_plt h_v1069 h_v61 (of_decide_eq_true rfl)
  have h_v1082 : R 1 0 0 1 v1082 v1082 := (r_plt hl h_v61 h_v1073 (of_decide_eq_true rfl))
  have e_v1082 : (v1082 = 1 ↔ sv v61 < sv v1073) := e_plt h_v61 h_v1073 (of_decide_eq_true rfl)
  have h_v1083 : R 1 0 0 1 v1083 v1083 := (r_sub hl (r_O hl) h_v1082 (of_decide_eq_true rfl))
  have e_v1083 : (v1083 = 1 ↔ ¬v1082 = 1) := e_not h_v1082 (of_decide_eq_true rfl)
  have h_v1084 : R 1 0 0 1 v1084 v1084 := (r_land hl h_v1080 h_v1083 (of_decide_eq_true rfl))
  have e_v1084 : (v1084 = 1 ↔ v1080 = 1 ∧ v1083 = 1) := e_land h_v1080 h_v1083 (of_decide_eq_true rfl)
  have h_v1085 : R 1 0 0 1 v1085 v1085 := (r_land hl h_v1080 h_v1082 (of_decide_eq_true rfl))
  have e_v1085 : (v1085 = 1 ↔ v1080 = 1 ∧ v1082 = 1) := e_land h_v1080 h_v1082 (of_decide_eq_true rfl)
  have h_v1086 : R 1 0 0 1 v1086 v1086 := (r_land hl h_v1079 h_v1085 (of_decide_eq_true rfl))
  have e_v1086 : (v1086 = 1 ↔ v1079 = 1 ∧ v1085 = 1) := e_land h_v1079 h_v1085 (of_decide_eq_true rfl)
  have h_v1087 : R 1 0 0 1 v1087 v1087 := (r_sub hl (r_O hl) h_v1086 (of_decide_eq_true rfl))
  have e_v1087 : (v1087 = 1 ↔ ¬v1086 = 1) := e_not h_v1086 (of_decide_eq_true rfl)
  have h_v1088 : R 1 0 0 1 v1088 v1088 := (r_lor hl h_v823 h_v1087 (of_decide_eq_true rfl))
  have e_v1088 : (v1088 = 1 ↔ v823 = 1 ∨ v1087 = 1) := e_lor h_v823 h_v1087 (of_decide_eq_true rfl)
  have h_v1095 : R 1 0 0 1 v1095 v1095 := (r_land hl h_v1078 h_v1085 (of_decide_eq_true rfl))
  have e_v1095 : (v1095 = 1 ↔ v1078 = 1 ∧ v1085 = 1) := e_land h_v1078 h_v1085 (of_decide_eq_true rfl)
  have h_v1096 : R 1 0 0 1 v1096 v1096 := (r_lor hl h_v1084 h_v1095 (of_decide_eq_true rfl))
  have e_v1096 : (v1096 = 1 ↔ v1084 = 1 ∨ v1095 = 1) := e_lor h_v1084 h_v1095 (of_decide_eq_true rfl)
  have h_v1097 : R 1 0 4611686018158952386 4611686018695823360 v1097 v1097 := (r_psel hl h_v1096 h_v1059 h_v1063 (of_decide_eq_true rfl))
  clear h_v1074 h_v1076 h_v1077 h_v1080 h_v1082 h_v1083 h_v1085 h_v1086 h_v1087 h_v1095
  have e_v1097 : v1097 = if v1096 = 1 then v1059 else v1063 := e_psel h_v1096 h_v1059 h_v1063 (of_decide_eq_true rfl)
  have h_v1098 : R 1 0 0 1 v1098 v1098 := (r_land hl h_v1079 h_v1084 (of_decide_eq_true rfl))
  have e_v1098 : (v1098 = 1 ↔ v1079 = 1 ∧ v1084 = 1) := e_land h_v1079 h_v1084 (of_decide_eq_true rfl)
  have h_v1099 : R 1 0 0 1 v1099 v1099 := (r_lor hl h_v1078 h_v1098 (of_decide_eq_true rfl))
  have e_v1099 : (v1099 = 1 ↔ v1078 = 1 ∨ v1098 = 1) := e_lor h_v1078 h_v1098 (of_decide_eq_true rfl)
  have h_v1100 : R 1 0 4611686018158952386 4611686018695823360 v1100 v1100 := (r_psel hl h_v1099 h_v1069 h_v1073 (of_decide_eq_true rfl))
  have e_v1100 : v1100 = if v1099 = 1 then v1069 else v1073 := e_psel h_v1099 h_v1069 h_v1073 (of_decide_eq_true rfl)
  have h_v1103 : R 1 0 4539628407746461696 4683743645751316228 v1103 v1103 := (r_smx hl 30 h_v1100 h_v1097 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1103 : sv v1103 = sv v1100 * sv v1097 := e_smx 30 h_v1100 h_v1097 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1104 : R 1 0 4611686018158952386 4611686018695823485 v1104 v1104 := (r_srdC hl h_v1103 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v1104 : sv v1104 = -((-sv v1103) / 2 ^ 28) := e_srdC h_v1103 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v1105 : R 1 0 4611686017890516805 4611686018964258878 v1105 v1105 := (r_sub hl (r_add hl h_v784 h_OFFr (of_decide_eq_true rfl)) h_v1104 (of_decide_eq_true rfl))
  have e_v1105 : sv v1105 = sv v784 - sv v1104 := e_sub h_v784 h_v1104 (of_decide_eq_true rfl)
  have h_v1107 : R 1 0 4611686010374323999 4683743612465315840 v1107 v1107 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1060 (of_decide_eq_true rfl))
  have e_v1107 : sv v1107 = sv v940 - sv v1060 := e_sub h_v940 h_v1060 (of_decide_eq_true rfl)
  have h_v1108 : R 1 0 4611686018427387904 4611686018695823360 v1108 v1108 := (r_psqrt hl h_v1107 (of_decide_eq_true rfl))
  have e_v1108 : sv v1108 = ((Nat.sqrt (v1107 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1107 (of_decide_eq_true rfl)
  have h_v1109 : R 1 0 4611686018427387905 4611686018695823361 v1109 v1109 := (r_sub hl (r_add hl h_v105 h_v1108 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1109 : sv v1109 = sv v105 + sv v1108 := e_add h_v105 h_v1108 (of_decide_eq_true rfl)
  have pb_v1108_v876 : PB 1 v1108 v876 36028797018963968 := pb_sqrt hl h_v876 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1110 : R 1 0 4611686017085210624 4647714815446351872 v1110 v1110 := (r_smx_pb hl 29 h_v1108 h_v876 pb_v1108_v876 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1110 : sv v1110 = sv v1108 * sv v876 := e_smx_pb 29 h_v1108 h_v876 pb_v1108_v876 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1111 : R 1 0 4611686018427387899 4611686018561605632 v1111 v1111 := (r_srdF hl h_v1110 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1111 : sv v1111 = sv v1110 / 2 ^ 28 := e_srdF h_v1110 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1112 : R 1 0 4611686018427387894 4611686018695823360 v1112 v1112 := (r_sub hl (r_add hl h_v1111 h_v1111 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v784 h_v1059 h_v1063 h_v1069 h_v1073 h_v1078 h_v1079 h_v1084 h_v1096 h_v1097 h_v1098 h_v1099 h_v1100 h_v1103 h_v1104 h_v1107 h_v1108 pb_v1108_v876 h_v1110
  have e_v1112 : sv v1112 = sv v1111 + sv v1111 := e_add h_v1111 h_v1111 (of_decide_eq_true rfl)
  have pb_v1109_v876 : PB 1 v1109 v876 36028797287399439 := pb_sqrt1 hl h_v876 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1113 : R 1 0 4611686017085210619 4647714815714787343 v1113 v1113 := (r_smx_pb hl 29 h_v1109 h_v876 pb_v1109_v876 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1113 : sv v1113 = sv v1109 * sv v876 := e_smx_pb 29 h_v1109 h_v876 pb_v1109_v876 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1114 : R 1 0 4611686018427387899 4611686018561605634 v1114 v1114 := (r_srdC hl h_v1113 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1114 : sv v1114 = -((-sv v1113) / 2 ^ 28) := e_srdC h_v1113 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1115 : R 1 0 4611686018427387894 4611686018695823364 v1115 v1115 := (r_sub hl (r_add hl h_v1114 h_v1114 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1115 : sv v1115 = sv v1114 + sv v1114 := e_add h_v1114 h_v1114 (of_decide_eq_true rfl)
  have h_v1116 : R 1 0 0 1 v1116 v1116 := (r_plt hl h_v1115 h_v33 (of_decide_eq_true rfl))
  have e_v1116 : (v1116 = 1 ↔ sv v1115 < sv v33) := e_plt h_v1115 h_v33 (of_decide_eq_true rfl)
  have h_v1117 : R 1 0 4611686018427387894 4611686018695823364 v1117 v1117 := (r_psel hl h_v1116 h_v1115 h_v33 (of_decide_eq_true rfl))
  have e_v1117 : v1117 = if v1116 = 1 then v1115 else v33 := e_psel h_v1116 h_v1115 h_v33 (of_decide_eq_true rfl)
  have h_v1118 : R 1 0 4611686010374323999 4683743612465315840 v1118 v1118 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1054 (of_decide_eq_true rfl))
  have e_v1118 : sv v1118 = sv v940 - sv v1054 := e_sub h_v940 h_v1054 (of_decide_eq_true rfl)
  have h_v1119 : R 1 0 4611686018427387904 4611686018695823360 v1119 v1119 := (r_psqrt hl h_v1118 (of_decide_eq_true rfl))
  have e_v1119 : sv v1119 = ((Nat.sqrt (v1118 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1118 (of_decide_eq_true rfl)
  have h_v1120 : R 1 0 4611686018427387905 4611686018695823361 v1120 v1120 := (r_sub hl (r_add hl h_v105 h_v1119 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1120 : sv v1120 = sv v105 + sv v1119 := e_add h_v105 h_v1119 (of_decide_eq_true rfl)
  have pb_v1119_v877 : PB 1 v1119 v877 36028797018963968 := pb_sqrt hl h_v877 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1121 : R 1 0 4611686017085210624 4647714815446351872 v1121 v1121 := (r_smx_pb hl 29 h_v1119 h_v877 pb_v1119_v877 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1121 : sv v1121 = sv v1119 * sv v877 := e_smx_pb 29 h_v1119 h_v877 pb_v1119_v877 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1122 : R 1 0 4611686018427387899 4611686018561605632 v1122 v1122 := (r_srdF hl h_v1121 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1122 : sv v1122 = sv v1121 / 2 ^ 28 := e_srdF h_v1121 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1123 : R 1 0 4611686018427387894 4611686018695823360 v1123 v1123 := (r_sub hl (r_add hl h_v1122 h_v1122 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1123 : sv v1123 = sv v1122 + sv v1122 := e_add h_v1122 h_v1122 (of_decide_eq_true rfl)
  clear h_v876 h_v1109 h_v1111 pb_v1109_v876 h_v1113 h_v1114 h_v1115 h_v1116 h_v1118 h_v1119 pb_v1119_v877 h_v1121 h_v1122
  have pb_v1120_v877 : PB 1 v1120 v877 36028797287399439 := pb_sqrt1 hl h_v877 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1124 : R 1 0 4611686017085210619 4647714815714787343 v1124 v1124 := (r_smx_pb hl 29 h_v1120 h_v877 pb_v1120_v877 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1124 : sv v1124 = sv v1120 * sv v877 := e_smx_pb 29 h_v1120 h_v877 pb_v1120_v877 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1125 : R 1 0 4611686018427387899 4611686018561605634 v1125 v1125 := (r_srdC hl h_v1124 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1125 : sv v1125 = -((-sv v1124) / 2 ^ 28) := e_srdC h_v1124 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1126 : R 1 0 4611686018427387894 4611686018695823364 v1126 v1126 := (r_sub hl (r_add hl h_v1125 h_v1125 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1126 : sv v1126 = sv v1125 + sv v1125 := e_add h_v1125 h_v1125 (of_decide_eq_true rfl)
  have h_v1127 : R 1 0 0 1 v1127 v1127 := (r_plt hl h_v1126 h_v33 (of_decide_eq_true rfl))
  have e_v1127 : (v1127 = 1 ↔ sv v1126 < sv v33) := e_plt h_v1126 h_v33 (of_decide_eq_true rfl)
  have h_v1128 : R 1 0 4611686018427387894 4611686018695823364 v1128 v1128 := (r_psel hl h_v1127 h_v1126 h_v33 (of_decide_eq_true rfl))
  have e_v1128 : v1128 = if v1127 = 1 then v1126 else v33 := e_psel h_v1127 h_v1126 h_v33 (of_decide_eq_true rfl)
  have h_v1129 : R 1 0 0 1 v1129 v1129 := (r_plt hl h_v1112 h_v1123 (of_decide_eq_true rfl))
  have e_v1129 : (v1129 = 1 ↔ sv v1112 < sv v1123) := e_plt h_v1112 h_v1123 (of_decide_eq_true rfl)
  have h_v1130 : R 1 0 4611686018427387894 4611686018695823360 v1130 v1130 := (r_psel hl h_v1129 h_v1112 h_v1123 (of_decide_eq_true rfl))
  have e_v1130 : v1130 = if v1129 = 1 then v1112 else v1123 := e_psel h_v1129 h_v1112 h_v1123 (of_decide_eq_true rfl)
  have h_v1131 : R 1 0 0 1 v1131 v1131 := (r_plt hl h_v1117 h_v1128 (of_decide_eq_true rfl))
  have e_v1131 : (v1131 = 1 ↔ sv v1117 < sv v1128) := e_plt h_v1117 h_v1128 (of_decide_eq_true rfl)
  have h_v1132 : R 1 0 4611686018427387894 4611686018695823364 v1132 v1132 := (r_psel hl h_v1131 h_v1128 h_v1117 (of_decide_eq_true rfl))
  have e_v1132 : v1132 = if v1131 = 1 then v1128 else v1117 := e_psel h_v1131 h_v1128 h_v1117 (of_decide_eq_true rfl)
  have h_v1133 : R 1 0 0 1 v1133 v1133 := (r_plt hl h_v967 h_v1060 (of_decide_eq_true rfl))
  have e_v1133 : (v1133 = 1 ↔ sv v967 < sv v1060) := e_plt h_v967 h_v1060 (of_decide_eq_true rfl)
  have h_v1134 : R 1 0 0 1 v1134 v1134 := (r_sub hl (r_O hl) h_v1133 (of_decide_eq_true rfl))
  have e_v1134 : (v1134 = 1 ↔ ¬v1133 = 1) := e_not h_v1133 (of_decide_eq_true rfl)
  have h_v1135 : R 1 0 0 1 v1135 v1135 := (r_plt hl h_v1054 h_v967 (of_decide_eq_true rfl))
  have e_v1135 : (v1135 = 1 ↔ sv v1054 < sv v967) := e_plt h_v1054 h_v967 (of_decide_eq_true rfl)
  clear h_v877 h_v1054 h_v1060 h_v1112 h_v1117 h_v1120 h_v1123 pb_v1120_v877 h_v1124 h_v1125 h_v1126 h_v1127 h_v1128 h_v1129 h_v1131 h_v1133
  have h_v1136 : R 1 0 0 1 v1136 v1136 := (r_sub hl (r_O hl) h_v1135 (of_decide_eq_true rfl))
  have e_v1136 : (v1136 = 1 ↔ ¬v1135 = 1) := e_not h_v1135 (of_decide_eq_true rfl)
  have h_v1137 : R 1 0 0 1 v1137 v1137 := (r_land hl h_v1134 h_v1136 (of_decide_eq_true rfl))
  have e_v1137 : (v1137 = 1 ↔ v1134 = 1 ∧ v1136 = 1) := e_land h_v1134 h_v1136 (of_decide_eq_true rfl)
  have h_v1138 : R 1 0 4611686018427387894 4611686018695823364 v1138 v1138 := (r_psel hl h_v1137 h_v33 h_v1132 (of_decide_eq_true rfl))
  have e_v1138 : v1138 = if v1137 = 1 then v33 else v1132 := e_psel h_v1137 h_v33 h_v1132 (of_decide_eq_true rfl)
  have h_v1139 : R 1 0 4611686010374323999 4683743612465315840 v1139 v1139 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1070 (of_decide_eq_true rfl))
  have e_v1139 : sv v1139 = sv v940 - sv v1070 := e_sub h_v940 h_v1070 (of_decide_eq_true rfl)
  have h_v1140 : R 1 0 4611686018427387904 4611686018695823360 v1140 v1140 := (r_psqrt hl h_v1139 (of_decide_eq_true rfl))
  have e_v1140 : sv v1140 = ((Nat.sqrt (v1139 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1139 (of_decide_eq_true rfl)
  have h_v1141 : R 1 0 4611686018427387905 4611686018695823361 v1141 v1141 := (r_sub hl (r_add hl h_v105 h_v1140 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1141 : sv v1141 = sv v105 + sv v1140 := e_add h_v105 h_v1140 (of_decide_eq_true rfl)
  have pb_v1140_v880 : PB 1 v1140 v880 36028797018963968 := pb_sqrt hl h_v880 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1142 : R 1 0 4611686017085210624 4647714815446351872 v1142 v1142 := (r_smx_pb hl 29 h_v1140 h_v880 pb_v1140_v880 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1142 : sv v1142 = sv v1140 * sv v880 := e_smx_pb 29 h_v1140 h_v880 pb_v1140_v880 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1143 : R 1 0 4611686018427387899 4611686018561605632 v1143 v1143 := (r_srdF hl h_v1142 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1143 : sv v1143 = sv v1142 / 2 ^ 28 := e_srdF h_v1142 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1144 : R 1 0 4611686018427387894 4611686018695823360 v1144 v1144 := (r_sub hl (r_add hl h_v1143 h_v1143 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1144 : sv v1144 = sv v1143 + sv v1143 := e_add h_v1143 h_v1143 (of_decide_eq_true rfl)
  have pb_v1141_v880 : PB 1 v1141 v880 36028797287399439 := pb_sqrt1 hl h_v880 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1145 : R 1 0 4611686017085210619 4647714815714787343 v1145 v1145 := (r_smx_pb hl 29 h_v1141 h_v880 pb_v1141_v880 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1145 : sv v1145 = sv v1141 * sv v880 := e_smx_pb 29 h_v1141 h_v880 pb_v1141_v880 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1146 : R 1 0 4611686018427387899 4611686018561605634 v1146 v1146 := (r_srdC hl h_v1145 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1146 : sv v1146 = -((-sv v1145) / 2 ^ 28) := e_srdC h_v1145 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1147 : R 1 0 4611686018427387894 4611686018695823364 v1147 v1147 := (r_sub hl (r_add hl h_v1146 h_v1146 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v880 h_v1132 h_v1134 h_v1135 h_v1136 h_v1137 h_v1139 h_v1140 h_v1141 pb_v1140_v880 h_v1142 h_v1143 pb_v1141_v880 h_v1145
  have e_v1147 : sv v1147 = sv v1146 + sv v1146 := e_add h_v1146 h_v1146 (of_decide_eq_true rfl)
  have h_v1148 : R 1 0 0 1 v1148 v1148 := (r_plt hl h_v1147 h_v33 (of_decide_eq_true rfl))
  have e_v1148 : (v1148 = 1 ↔ sv v1147 < sv v33) := e_plt h_v1147 h_v33 (of_decide_eq_true rfl)
  have h_v1149 : R 1 0 4611686018427387894 4611686018695823364 v1149 v1149 := (r_psel hl h_v1148 h_v1147 h_v33 (of_decide_eq_true rfl))
  have e_v1149 : v1149 = if v1148 = 1 then v1147 else v33 := e_psel h_v1148 h_v1147 h_v33 (of_decide_eq_true rfl)
  have h_v1150 : R 1 0 4611686010374323999 4683743612465315840 v1150 v1150 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1064 (of_decide_eq_true rfl))
  have e_v1150 : sv v1150 = sv v940 - sv v1064 := e_sub h_v940 h_v1064 (of_decide_eq_true rfl)
  have h_v1151 : R 1 0 4611686018427387904 4611686018695823360 v1151 v1151 := (r_psqrt hl h_v1150 (of_decide_eq_true rfl))
  have e_v1151 : sv v1151 = ((Nat.sqrt (v1150 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1150 (of_decide_eq_true rfl)
  have h_v1152 : R 1 0 4611686018427387905 4611686018695823361 v1152 v1152 := (r_sub hl (r_add hl h_v105 h_v1151 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1152 : sv v1152 = sv v105 + sv v1151 := e_add h_v105 h_v1151 (of_decide_eq_true rfl)
  have pb_v1151_v881 : PB 1 v1151 v881 36028797018963968 := pb_sqrt hl h_v881 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1153 : R 1 0 4611686017085210624 4647714815446351872 v1153 v1153 := (r_smx_pb hl 29 h_v1151 h_v881 pb_v1151_v881 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1153 : sv v1153 = sv v1151 * sv v881 := e_smx_pb 29 h_v1151 h_v881 pb_v1151_v881 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1154 : R 1 0 4611686018427387899 4611686018561605632 v1154 v1154 := (r_srdF hl h_v1153 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1154 : sv v1154 = sv v1153 / 2 ^ 28 := e_srdF h_v1153 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1155 : R 1 0 4611686018427387894 4611686018695823360 v1155 v1155 := (r_sub hl (r_add hl h_v1154 h_v1154 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1155 : sv v1155 = sv v1154 + sv v1154 := e_add h_v1154 h_v1154 (of_decide_eq_true rfl)
  have pb_v1152_v881 : PB 1 v1152 v881 36028797287399439 := pb_sqrt1 hl h_v881 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1156 : R 1 0 4611686017085210619 4647714815714787343 v1156 v1156 := (r_smx_pb hl 29 h_v1152 h_v881 pb_v1152_v881 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1156 : sv v1156 = sv v1152 * sv v881 := e_smx_pb 29 h_v1152 h_v881 pb_v1152_v881 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1157 : R 1 0 4611686018427387899 4611686018561605634 v1157 v1157 := (r_srdC hl h_v1156 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1157 : sv v1157 = -((-sv v1156) / 2 ^ 28) := e_srdC h_v1156 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1158 : R 1 0 4611686018427387894 4611686018695823364 v1158 v1158 := (r_sub hl (r_add hl h_v1157 h_v1157 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1158 : sv v1158 = sv v1157 + sv v1157 := e_add h_v1157 h_v1157 (of_decide_eq_true rfl)
  clear h_v105 h_v881 h_v940 h_v1146 h_v1147 h_v1148 h_v1150 h_v1151 h_v1152 pb_v1151_v881 h_v1153 h_v1154 pb_v1152_v881 h_v1156 h_v1157
  have h_v1159 : R 1 0 0 1 v1159 v1159 := (r_plt hl h_v1158 h_v33 (of_decide_eq_true rfl))
  have e_v1159 : (v1159 = 1 ↔ sv v1158 < sv v33) := e_plt h_v1158 h_v33 (of_decide_eq_true rfl)
  have h_v1160 : R 1 0 4611686018427387894 4611686018695823364 v1160 v1160 := (r_psel hl h_v1159 h_v1158 h_v33 (of_decide_eq_true rfl))
  have e_v1160 : v1160 = if v1159 = 1 then v1158 else v33 := e_psel h_v1159 h_v1158 h_v33 (of_decide_eq_true rfl)
  have h_v1161 : R 1 0 0 1 v1161 v1161 := (r_plt hl h_v1144 h_v1155 (of_decide_eq_true rfl))
  have e_v1161 : (v1161 = 1 ↔ sv v1144 < sv v1155) := e_plt h_v1144 h_v1155 (of_decide_eq_true rfl)
  have h_v1162 : R 1 0 4611686018427387894 4611686018695823360 v1162 v1162 := (r_psel hl h_v1161 h_v1144 h_v1155 (of_decide_eq_true rfl))
  have e_v1162 : v1162 = if v1161 = 1 then v1144 else v1155 := e_psel h_v1161 h_v1144 h_v1155 (of_decide_eq_true rfl)
  have h_v1163 : R 1 0 0 1 v1163 v1163 := (r_plt hl h_v1149 h_v1160 (of_decide_eq_true rfl))
  have e_v1163 : (v1163 = 1 ↔ sv v1149 < sv v1160) := e_plt h_v1149 h_v1160 (of_decide_eq_true rfl)
  have h_v1164 : R 1 0 4611686018427387894 4611686018695823364 v1164 v1164 := (r_psel hl h_v1163 h_v1160 h_v1149 (of_decide_eq_true rfl))
  have e_v1164 : v1164 = if v1163 = 1 then v1160 else v1149 := e_psel h_v1163 h_v1160 h_v1149 (of_decide_eq_true rfl)
  have h_v1165 : R 1 0 0 1 v1165 v1165 := (r_plt hl h_v967 h_v1070 (of_decide_eq_true rfl))
  have e_v1165 : (v1165 = 1 ↔ sv v967 < sv v1070) := e_plt h_v967 h_v1070 (of_decide_eq_true rfl)
  have h_v1166 : R 1 0 0 1 v1166 v1166 := (r_sub hl (r_O hl) h_v1165 (of_decide_eq_true rfl))
  have e_v1166 : (v1166 = 1 ↔ ¬v1165 = 1) := e_not h_v1165 (of_decide_eq_true rfl)
  have h_v1167 : R 1 0 0 1 v1167 v1167 := (r_plt hl h_v1064 h_v967 (of_decide_eq_true rfl))
  have e_v1167 : (v1167 = 1 ↔ sv v1064 < sv v967) := e_plt h_v1064 h_v967 (of_decide_eq_true rfl)
  have h_v1168 : R 1 0 0 1 v1168 v1168 := (r_sub hl (r_O hl) h_v1167 (of_decide_eq_true rfl))
  have e_v1168 : (v1168 = 1 ↔ ¬v1167 = 1) := e_not h_v1167 (of_decide_eq_true rfl)
  have h_v1169 : R 1 0 0 1 v1169 v1169 := (r_land hl h_v1166 h_v1168 (of_decide_eq_true rfl))
  have e_v1169 : (v1169 = 1 ↔ v1166 = 1 ∧ v1168 = 1) := e_land h_v1166 h_v1168 (of_decide_eq_true rfl)
  have h_v1170 : R 1 0 4611686018427387894 4611686018695823364 v1170 v1170 := (r_psel hl h_v1169 h_v33 h_v1164 (of_decide_eq_true rfl))
  have e_v1170 : v1170 = if v1169 = 1 then v33 else v1164 := e_psel h_v1169 h_v33 h_v1164 (of_decide_eq_true rfl)
  have h_v1171 : R 1 0 0 1 v1171 v1171 := (r_plt hl h_v1130 h_v61 (of_decide_eq_true rfl))
  clear h_v33 h_v967 h_v1064 h_v1070 h_v1144 h_v1149 h_v1155 h_v1158 h_v1159 h_v1160 h_v1161 h_v1163 h_v1164 h_v1165 h_v1166 h_v1167 h_v1168 h_v1169
  have e_v1171 : (v1171 = 1 ↔ sv v1130 < sv v61) := e_plt h_v1130 h_v61 (of_decide_eq_true rfl)
  have h_v1172 : R 1 0 0 1 v1172 v1172 := (r_sub hl (r_O hl) h_v1171 (of_decide_eq_true rfl))
  have e_v1172 : (v1172 = 1 ↔ ¬v1171 = 1) := e_not h_v1171 (of_decide_eq_true rfl)
  have h_v1173 : R 1 0 0 1 v1173 v1173 := (r_plt hl h_v61 h_v1138 (of_decide_eq_true rfl))
  have e_v1173 : (v1173 = 1 ↔ sv v61 < sv v1138) := e_plt h_v61 h_v1138 (of_decide_eq_true rfl)
  have h_v1174 : R 1 0 0 1 v1174 v1174 := (r_sub hl (r_O hl) h_v1173 (of_decide_eq_true rfl))
  have e_v1174 : (v1174 = 1 ↔ ¬v1173 = 1) := e_not h_v1173 (of_decide_eq_true rfl)
  have h_v1175 : R 1 0 0 1 v1175 v1175 := (r_land hl h_v1171 h_v1174 (of_decide_eq_true rfl))
  have e_v1175 : (v1175 = 1 ↔ v1171 = 1 ∧ v1174 = 1) := e_land h_v1171 h_v1174 (of_decide_eq_true rfl)
  have h_v1176 : R 1 0 0 1 v1176 v1176 := (r_land hl h_v1171 h_v1173 (of_decide_eq_true rfl))
  have e_v1176 : (v1176 = 1 ↔ v1171 = 1 ∧ v1173 = 1) := e_land h_v1171 h_v1173 (of_decide_eq_true rfl)
  have h_v1177 : R 1 0 0 1 v1177 v1177 := (r_plt hl h_v1162 h_v61 (of_decide_eq_true rfl))
  have e_v1177 : (v1177 = 1 ↔ sv v1162 < sv v61) := e_plt h_v1162 h_v61 (of_decide_eq_true rfl)
  have h_v1178 : R 1 0 0 1 v1178 v1178 := (r_sub hl (r_O hl) h_v1177 (of_decide_eq_true rfl))
  have e_v1178 : (v1178 = 1 ↔ ¬v1177 = 1) := e_not h_v1177 (of_decide_eq_true rfl)
  have h_v1179 : R 1 0 0 1 v1179 v1179 := (r_plt hl h_v61 h_v1170 (of_decide_eq_true rfl))
  have e_v1179 : (v1179 = 1 ↔ sv v61 < sv v1170) := e_plt h_v61 h_v1170 (of_decide_eq_true rfl)
  have h_v1180 : R 1 0 0 1 v1180 v1180 := (r_sub hl (r_O hl) h_v1179 (of_decide_eq_true rfl))
  have e_v1180 : (v1180 = 1 ↔ ¬v1179 = 1) := e_not h_v1179 (of_decide_eq_true rfl)
  have h_v1181 : R 1 0 0 1 v1181 v1181 := (r_land hl h_v1177 h_v1180 (of_decide_eq_true rfl))
  have e_v1181 : (v1181 = 1 ↔ v1177 = 1 ∧ v1180 = 1) := e_land h_v1177 h_v1180 (of_decide_eq_true rfl)
  have h_v1182 : R 1 0 0 1 v1182 v1182 := (r_land hl h_v1177 h_v1179 (of_decide_eq_true rfl))
  have e_v1182 : (v1182 = 1 ↔ v1177 = 1 ∧ v1179 = 1) := e_land h_v1177 h_v1179 (of_decide_eq_true rfl)
  have h_v1183 : R 1 0 0 1 v1183 v1183 := (r_land hl h_v1176 h_v1182 (of_decide_eq_true rfl))
  have e_v1183 : (v1183 = 1 ↔ v1176 = 1 ∧ v1182 = 1) := e_land h_v1176 h_v1182 (of_decide_eq_true rfl)
  clear h_v1171 h_v1173 h_v1174 h_v1177 h_v1179 h_v1180
  have h_v1184 : R 1 0 0 1 v1184 v1184 := (r_sub hl (r_O hl) h_v1183 (of_decide_eq_true rfl))
  have e_v1184 : (v1184 = 1 ↔ ¬v1183 = 1) := e_not h_v1183 (of_decide_eq_true rfl)
  have h_v1185 : R 1 0 0 1 v1185 v1185 := (r_lor hl h_v823 h_v1184 (of_decide_eq_true rfl))
  have e_v1185 : (v1185 = 1 ↔ v823 = 1 ∨ v1184 = 1) := e_lor h_v823 h_v1184 (of_decide_eq_true rfl)
  have h_v1186 : R 1 0 0 1 v1186 v1186 := (r_land hl h_v1172 h_v1182 (of_decide_eq_true rfl))
  have e_v1186 : (v1186 = 1 ↔ v1172 = 1 ∧ v1182 = 1) := e_land h_v1172 h_v1182 (of_decide_eq_true rfl)
  have h_v1187 : R 1 0 0 1 v1187 v1187 := (r_lor hl h_v1181 h_v1186 (of_decide_eq_true rfl))
  have e_v1187 : (v1187 = 1 ↔ v1181 = 1 ∨ v1186 = 1) := e_lor h_v1181 h_v1186 (of_decide_eq_true rfl)
  have h_v1188 : R 1 0 4611686018427387894 4611686018695823364 v1188 v1188 := (r_psel hl h_v1187 h_v1138 h_v1130 (of_decide_eq_true rfl))
  have e_v1188 : v1188 = if v1187 = 1 then v1138 else v1130 := e_psel h_v1187 h_v1138 h_v1130 (of_decide_eq_true rfl)
  have h_v1189 : R 1 0 0 1 v1189 v1189 := (r_land hl h_v1176 h_v1178 (of_decide_eq_true rfl))
  have e_v1189 : (v1189 = 1 ↔ v1176 = 1 ∧ v1178 = 1) := e_land h_v1176 h_v1178 (of_decide_eq_true rfl)
  have h_v1190 : R 1 0 0 1 v1190 v1190 := (r_lor hl h_v1175 h_v1189 (of_decide_eq_true rfl))
  have e_v1190 : (v1190 = 1 ↔ v1175 = 1 ∨ v1189 = 1) := e_lor h_v1175 h_v1189 (of_decide_eq_true rfl)
  have h_v1191 : R 1 0 4611686018427387894 4611686018695823364 v1191 v1191 := (r_psel hl h_v1190 h_v1170 h_v1162 (of_decide_eq_true rfl))
  have e_v1191 : v1191 = if v1190 = 1 then v1170 else v1162 := e_psel h_v1190 h_v1170 h_v1162 (of_decide_eq_true rfl)
  have h_v1192 : R 1 0 0 1 v1192 v1192 := (r_land hl h_v1175 h_v1182 (of_decide_eq_true rfl))
  have e_v1192 : (v1192 = 1 ↔ v1175 = 1 ∧ v1182 = 1) := e_land h_v1175 h_v1182 (of_decide_eq_true rfl)
  have h_v1193 : R 1 0 0 1 v1193 v1193 := (r_lor hl h_v1181 h_v1192 (of_decide_eq_true rfl))
  have e_v1193 : (v1193 = 1 ↔ v1181 = 1 ∨ v1192 = 1) := e_lor h_v1181 h_v1192 (of_decide_eq_true rfl)
  have h_v1194 : R 1 0 4611686018427387894 4611686018695823364 v1194 v1194 := (r_psel hl h_v1193 h_v1130 h_v1138 (of_decide_eq_true rfl))
  have e_v1194 : v1194 = if v1193 = 1 then v1130 else v1138 := e_psel h_v1193 h_v1130 h_v1138 (of_decide_eq_true rfl)
  have h_v1195 : R 1 0 0 1 v1195 v1195 := (r_land hl h_v1176 h_v1181 (of_decide_eq_true rfl))
  have e_v1195 : (v1195 = 1 ↔ v1176 = 1 ∧ v1181 = 1) := e_land h_v1176 h_v1181 (of_decide_eq_true rfl)
  have h_v1196 : R 1 0 0 1 v1196 v1196 := (r_lor hl h_v1175 h_v1195 (of_decide_eq_true rfl))
  clear h_v823 h_v1130 h_v1138 h_v1172 h_v1176 h_v1178 h_v1181 h_v1182 h_v1183 h_v1184 h_v1186 h_v1187 h_v1189 h_v1190 h_v1192 h_v1193
  have e_v1196 : (v1196 = 1 ↔ v1175 = 1 ∨ v1195 = 1) := e_lor h_v1175 h_v1195 (of_decide_eq_true rfl)
  have h_v1197 : R 1 0 4611686018427387894 4611686018695823364 v1197 v1197 := (r_psel hl h_v1196 h_v1162 h_v1170 (of_decide_eq_true rfl))
  have e_v1197 : v1197 = if v1196 = 1 then v1162 else v1170 := e_psel h_v1196 h_v1162 h_v1170 (of_decide_eq_true rfl)
  have h_v1198 : R 1 0 4611686015743033304 4683743614612799504 v1198 v1198 := (r_smx hl 29 h_v1191 h_v1188 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1198 : sv v1198 = sv v1191 * sv v1188 := e_smx 29 h_v1191 h_v1188 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1199 : R 1 0 4611686018427387893 4611686018695823368 v1199 v1199 := (r_srdF hl h_v1198 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v1199 : sv v1199 = sv v1198 / 2 ^ 28 := e_srdF h_v1198 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v1200 : R 1 0 4611686015743033304 4683743614612799504 v1200 v1200 := (r_smx hl 29 h_v1197 h_v1194 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1200 : sv v1200 = sv v1197 * sv v1194 := e_smx 29 h_v1197 h_v1194 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1201 : R 1 0 4611686018427387894 4611686018695823369 v1201 v1201 := (r_srdC hl h_v1200 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v1201 : sv v1201 = -((-sv v1200) / 2 ^ 28) := e_srdC h_v1200 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1202 : R 1 0 0 1 v1202 v1202 := (r_plt hl h_v61 h_v1199 (of_decide_eq_true rfl))
  have e_v1202 : (v1202 = 1 ↔ sv v61 < sv v1199) := e_plt h_v61 h_v1199 (of_decide_eq_true rfl)
  have h_v1204 : R 1 0 0 1 v1204 v1204 := (r_plt hl h_v1105 h_v61 (of_decide_eq_true rfl))
  have e_v1204 : (v1204 = 1 ↔ sv v1105 < sv v61) := e_plt h_v1105 h_v61 (of_decide_eq_true rfl)
  have h_v1205 : R 1 0 4611686018427387893 4611686018695823369 v1205 v1205 := (r_psel hl h_v1204 h_v1199 h_v1201 (of_decide_eq_true rfl))
  have e_v1205 : v1205 = if v1204 = 1 then v1199 else v1201 := e_psel h_v1204 h_v1199 h_v1201 (of_decide_eq_true rfl)
  have h_v1208 : R 1 0 0 1 v1208 v1208 := (r_plt hl h_v1205 h_v1105 (of_decide_eq_true rfl))
  have e_v1208 : (v1208 = 1 ↔ sv v1205 < sv v1105) := e_plt h_v1205 h_v1105 (of_decide_eq_true rfl)
  have h_v1209 : R 1 0 0 1 v1209 v1209 := (r_land hl h_v1202 h_v1208 (of_decide_eq_true rfl))
  have e_v1209 : (v1209 = 1 ↔ v1202 = 1 ∧ v1208 = 1) := e_land h_v1202 h_v1208 (of_decide_eq_true rfl)
  have h_v1216 : R 1 0 0 1 v1216 v1216 := (r_lor hl h_v1045 h_v1209 (of_decide_eq_true rfl))
  have e_v1216 : (v1216 = 1 ↔ v1045 = 1 ∨ v1209 = 1) := e_lor h_v1045 h_v1209 (of_decide_eq_true rfl)
  have h_v1218 : R 1 0 4611686018427387904 4611686019501129727 v1218 v1218 := (r1_hxa hb_H1 0 (of_decide_eq_true rfl))
  have e_v1218 : sv v1218 = ((H1 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H1 0 (of_decide_eq_true rfl)
  clear h_v1105 h_v1162 h_v1170 h_v1175 h_v1188 h_v1191 h_v1194 h_v1195 h_v1196 h_v1197 h_v1198 h_v1199 h_v1200 h_v1201 h_v1202 h_v1204 h_v1205 h_v1208 h_v1209
  have h_v1219 : R 1 0 0 1 v1219 v1219 := (r_plt hl h_v61 h_v1218 (of_decide_eq_true rfl))
  have e_v1219 : (v1219 = 1 ↔ sv v61 < sv v1218) := e_plt h_v61 h_v1218 (of_decide_eq_true rfl)
  have h_v1220 : R 1 0 0 1 v1220 v1220 := (r_sub hl (r_O hl) h_v1219 (of_decide_eq_true rfl))
  have e_v1220 : (v1220 = 1 ↔ ¬v1219 = 1) := e_not h_v1219 (of_decide_eq_true rfl)
  have h_t1218_1 : R 1 0 4611686018427387904 4611686018695823363 t1218.1 t1218.1 := r_sc1 hl h_v1218 (of_decide_eq_true rfl)
  have h_t1218_2 : R 1 0 4611686018158952445 4611686018695823363 t1218.2 t1218.2 := r_sc2 hl h_v1218 (of_decide_eq_true rfl)
  have e_t1218_1 : sv t1218.1 = (sc28pS (scArg v1218)).1 := e_sc1 h_v1218 (of_decide_eq_true rfl)
  have e_t1218_2 : sv t1218.2 = (sc28pS (scArg v1218)).2 := e_sc2 h_v1218 (of_decide_eq_true rfl)
  have h_v1222 : R 1 0 4611686018158952441 4611686018695823359 v1222 v1222 := (r_sub hl (r_add hl h_v28 h_t1218_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1222 : sv v1222 = sv v28 + sv t1218.2 := e_add h_v28 h_t1218_2 (of_decide_eq_true rfl)
  have h_v1223 : R 1 0 0 1 v1223 v1223 := (r_plt hl h_v1222 h_v95 (of_decide_eq_true rfl))
  have e_v1223 : (v1223 = 1 ↔ sv v1222 < sv v95) := e_plt h_v1222 h_v95 (of_decide_eq_true rfl)
  have h_v1224 : R 1 0 4611686018158952441 4611686018695823359 v1224 v1224 := (r_psel hl h_v1223 h_v95 h_v1222 (of_decide_eq_true rfl))
  have e_v1224 : v1224 = if v1223 = 1 then v95 else v1222 := e_psel h_v1223 h_v95 h_v1222 (of_decide_eq_true rfl)
  have h_v1225 : R 1 0 4467570782033149952 4755801223146242048 v1225 v1225 := (r_sshl hl h_v1049 4467570782033149952 4755801223146242048 (of_decide_eq_true rfl))
  have e_v1225 : sv v1225 = sv v1049 * 2 ^ 28 := e_sshl h_v1049 4467570782033149952 4755801223146242048 (of_decide_eq_true rfl)
  have h_v1226 : R 1 0 4539628420094492609 4683743614612799479 v1226 v1226 := (r_smx hl 29 h_v1224 h_v1050 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl))
  have e_v1226 : sv v1226 = sv v1224 * sv v1050 := e_smx 29 h_v1224 h_v1050 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl)
  have h_v1227 : R 1 0 0 1 v1227 v1227 := (r_plt hl h_v1226 h_v1225 (of_decide_eq_true rfl))
  have e_v1227 : (v1227 = 1 ↔ sv v1226 < sv v1225) := e_plt h_v1226 h_v1225 (of_decide_eq_true rfl)
  have h_v1228 : R 1 0 0 1 v1228 v1228 := (r_sub hl (r_O hl) h_v1227 (of_decide_eq_true rfl))
  have e_v1228 : (v1228 = 1 ↔ ¬v1227 = 1) := e_not h_v1227 (of_decide_eq_true rfl)
  have h_v1229 : R 1 0 0 1 v1229 v1229 := (r_plt hl h_v15 h_v1218 (of_decide_eq_true rfl))
  have e_v1229 : (v1229 = 1 ↔ sv v15 < sv v1218) := e_plt h_v15 h_v1218 (of_decide_eq_true rfl)
  have h_v1230 : R 1 0 0 1 v1230 v1230 := (r_sub hl (r_O hl) h_v1229 (of_decide_eq_true rfl))
  clear h_v28 h_v95 h_v1049 h_v1050 h_v1219 h_t1218_1 h_t1218_2 e_t1218_1 h_v1222 h_v1223 h_v1224 h_v1225 h_v1226 h_v1227
  have e_v1230 : (v1230 = 1 ↔ ¬v1229 = 1) := e_not h_v1229 (of_decide_eq_true rfl)
  have h_v1231 : R 1 0 0 1 v1231 v1231 := (r_land hl h_v1228 h_v1230 (of_decide_eq_true rfl))
  have e_v1231 : (v1231 = 1 ↔ v1228 = 1 ∧ v1230 = 1) := e_land h_v1228 h_v1230 (of_decide_eq_true rfl)
  have h_v1232 : R 1 0 0 1 v1232 v1232 := (r_lor hl h_v1220 h_v1231 (of_decide_eq_true rfl))
  have e_v1232 : (v1232 = 1 ↔ v1220 = 1 ∨ v1231 = 1) := e_lor h_v1220 h_v1231 (of_decide_eq_true rfl)
  have h_v1233 : R 1 0 4611686018427387904 4611686019501129727 v1233 v1233 := (r_psel hl h_v1232 h_v1218 h_v61 (of_decide_eq_true rfl))
  have e_v1233 : v1233 = if v1232 = 1 then v1218 else v61 := e_psel h_v1232 h_v1218 h_v61 (of_decide_eq_true rfl)
  have h_v1247 : R 1 0 4611686018427387904 4611686019501129727 v1247 v1247 := (r_psel hl h_v778 h_v1233 h_v61 (of_decide_eq_true rfl))
  have e_v1247 : v1247 = if v778 = 1 then v1233 else v61 := e_psel h_v778 h_v1233 h_v61 (of_decide_eq_true rfl)
  have h_v1249 : R 1 0 0 1 v1249 v1249 := (r_land hl h_v778 h_v1216 (of_decide_eq_true rfl))
  have e_v1249 : (v1249 = 1 ↔ v778 = 1 ∧ v1216 = 1) := e_land h_v778 h_v1216 (of_decide_eq_true rfl)
  have h_v1250 : R 1 0 4611686018427387904 4611686019270702760 v1250 v1250 := (r_psel hl h_v1045 h_v15 h_v61 (of_decide_eq_true rfl))
  have e_v1250 : v1250 = if v1045 = 1 then v15 else v61 := e_psel h_v1045 h_v15 h_v61 (of_decide_eq_true rfl)
  have h_v1252 : R 1 0 4611686018427387904 4611686019501129727 v1252 v1252 := (r_psel hl h_v1249 h_v1250 h_v1247 (of_decide_eq_true rfl))
  have e_v1252 : v1252 = if v1249 = 1 then v1250 else v1247 := e_psel h_v1249 h_v1250 h_v1247 (of_decide_eq_true rfl)
  have h_v1254 : R 1 0 4611686017353646081 4611686020574871550 v1254 v1254 := (r_sub hl (r_add hl h_v255 h_v1252 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1254 : sv v1254 = sv v255 + sv v1252 := e_add h_v255 h_v1252 (of_decide_eq_true rfl)
  have h_v1256 : R 1 0 4611686016279904258 4611686021648613373 v1256 v1256 := (r_sub hl (r_add hl h_v580 h_v1254 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1256 : sv v1256 = sv v580 + sv v1254 := e_add h_v580 h_v1254 (of_decide_eq_true rfl)
  have h_v1258 : R 1 0 0 1 v1258 v1258 := (r_plt hl h_v1256 h_v6 (of_decide_eq_true rfl))
  have e_v1258 : (v1258 = 1 ↔ sv v1256 < sv v6) := e_plt h_v1256 h_v6 (of_decide_eq_true rfl)
  have h_v1259 : R 1 0 0 1 v1259 v1259 := (r_sub hl (r_O hl) h_v1258 (of_decide_eq_true rfl))
  have e_v1259 : (v1259 = 1 ↔ ¬v1258 = 1) := e_not h_v1258 (of_decide_eq_true rfl)
  have h_v1262 : R 1 0 0 1 v1262 v1262 := (r_land hl h_v23 h_v47 (of_decide_eq_true rfl))
  have e_v1262 : (v1262 = 1 ↔ v23 = 1 ∧ v47 = 1) := e_land h_v23 h_v47 (of_decide_eq_true rfl)
  clear h_OFFr h_v6 h_v15 h_v47 h_v61 h_v255 h_v580 h_v778 h_v1045 h_v1216 h_v1218 h_v1220 h_v1228 h_v1229 h_v1230 h_v1231 h_v1232 h_v1233 h_v1247 h_v1249 h_v1250 h_v1252 h_v1254 h_v1256 h_v1258
  have h_v1263 : R 1 0 0 1 v1263 v1263 := (r_land hl h_v75 h_v1262 (of_decide_eq_true rfl))
  have e_v1263 : (v1263 = 1 ↔ v75 = 1 ∧ v1262 = 1) := e_land h_v75 h_v1262 (of_decide_eq_true rfl)
  have h_v1264 : R 1 0 0 1 v1264 v1264 := (r_land hl h_v92 h_v1263 (of_decide_eq_true rfl))
  have e_v1264 : (v1264 = 1 ↔ v92 = 1 ∧ v1263 = 1) := e_land h_v92 h_v1263 (of_decide_eq_true rfl)
  have h_v1265 : R 1 0 0 1 v1265 v1265 := (r_land hl h_v23 h_v1264 (of_decide_eq_true rfl))
  have e_v1265 : (v1265 = 1 ↔ v23 = 1 ∧ v1264 = 1) := e_land h_v23 h_v1264 (of_decide_eq_true rfl)
  have h_v1266 : R 1 0 0 1 v1266 v1266 := (r_land hl h_v110 h_v1265 (of_decide_eq_true rfl))
  have e_v1266 : (v1266 = 1 ↔ v110 = 1 ∧ v1265 = 1) := e_land h_v110 h_v1265 (of_decide_eq_true rfl)
  have h_v1267 : R 1 0 0 1 v1267 v1267 := (r_land hl h_v110 h_v1266 (of_decide_eq_true rfl))
  have e_v1267 : (v1267 = 1 ↔ v110 = 1 ∧ v1266 = 1) := e_land h_v110 h_v1266 (of_decide_eq_true rfl)
  have h_v1268 : R 1 0 0 1 v1268 v1268 := (r_land hl h_v147 h_v1267 (of_decide_eq_true rfl))
  have e_v1268 : (v1268 = 1 ↔ v147 = 1 ∧ v1267 = 1) := e_land h_v147 h_v1267 (of_decide_eq_true rfl)
  have h_v1269 : R 1 0 0 1 v1269 v1269 := (r_land hl h_v260 h_v1268 (of_decide_eq_true rfl))
  have e_v1269 : (v1269 = 1 ↔ v260 = 1 ∧ v1268 = 1) := e_land h_v260 h_v1268 (of_decide_eq_true rfl)
  have h_v1270 : R 1 0 0 1 v1270 v1270 := (r_land hl h_v260 h_v1269 (of_decide_eq_true rfl))
  have e_v1270 : (v1270 = 1 ↔ v260 = 1 ∧ v1269 = 1) := e_land h_v260 h_v1269 (of_decide_eq_true rfl)
  have h_v1271 : R 1 0 0 1 v1271 v1271 := (r_land hl h_v291 h_v1270 (of_decide_eq_true rfl))
  have e_v1271 : (v1271 = 1 ↔ v291 = 1 ∧ v1270 = 1) := e_land h_v291 h_v1270 (of_decide_eq_true rfl)
  have h_v1272 : R 1 0 0 1 v1272 v1272 := (r_land hl h_v23 h_v1271 (of_decide_eq_true rfl))
  have e_v1272 : (v1272 = 1 ↔ v23 = 1 ∧ v1271 = 1) := e_land h_v23 h_v1271 (of_decide_eq_true rfl)
  have h_v1273 : R 1 0 0 1 v1273 v1273 := (r_land hl h_v403 h_v1272 (of_decide_eq_true rfl))
  have e_v1273 : (v1273 = 1 ↔ v403 = 1 ∧ v1272 = 1) := e_land h_v403 h_v1272 (of_decide_eq_true rfl)
  have h_v1274 : R 1 0 0 1 v1274 v1274 := (r_land hl h_v424 h_v1273 (of_decide_eq_true rfl))
  have e_v1274 : (v1274 = 1 ↔ v424 = 1 ∧ v1273 = 1) := e_land h_v424 h_v1273 (of_decide_eq_true rfl)
  have h_v1275 : R 1 0 0 1 v1275 v1275 := (r_land hl h_v441 h_v1274 (of_decide_eq_true rfl))
  clear h_v75 h_v92 h_v110 h_v147 h_v260 h_v291 h_v403 h_v424 h_v1262 h_v1263 h_v1264 h_v1265 h_v1266 h_v1267 h_v1268 h_v1269 h_v1270 h_v1271 h_v1272 h_v1273
  have e_v1275 : (v1275 = 1 ↔ v441 = 1 ∧ v1274 = 1) := e_land h_v441 h_v1274 (of_decide_eq_true rfl)
  have h_v1276 : R 1 0 0 1 v1276 v1276 := (r_land hl h_v23 h_v1275 (of_decide_eq_true rfl))
  have e_v1276 : (v1276 = 1 ↔ v23 = 1 ∧ v1275 = 1) := e_land h_v23 h_v1275 (of_decide_eq_true rfl)
  have h_v1277 : R 1 0 0 1 v1277 v1277 := (r_land hl h_v444 h_v1276 (of_decide_eq_true rfl))
  have e_v1277 : (v1277 = 1 ↔ v444 = 1 ∧ v1276 = 1) := e_land h_v444 h_v1276 (of_decide_eq_true rfl)
  have h_v1278 : R 1 0 0 1 v1278 v1278 := (r_land hl h_v444 h_v1277 (of_decide_eq_true rfl))
  have e_v1278 : (v1278 = 1 ↔ v444 = 1 ∧ v1277 = 1) := e_land h_v444 h_v1277 (of_decide_eq_true rfl)
  have h_v1279 : R 1 0 0 1 v1279 v1279 := (r_land hl h_v475 h_v1278 (of_decide_eq_true rfl))
  have e_v1279 : (v1279 = 1 ↔ v475 = 1 ∧ v1278 = 1) := e_land h_v475 h_v1278 (of_decide_eq_true rfl)
  have h_v1280 : R 1 0 0 1 v1280 v1280 := (r_land hl h_v585 h_v1279 (of_decide_eq_true rfl))
  have e_v1280 : (v1280 = 1 ↔ v585 = 1 ∧ v1279 = 1) := e_land h_v585 h_v1279 (of_decide_eq_true rfl)
  have h_v1281 : R 1 0 0 1 v1281 v1281 := (r_land hl h_v585 h_v1280 (of_decide_eq_true rfl))
  have e_v1281 : (v1281 = 1 ↔ v585 = 1 ∧ v1280 = 1) := e_land h_v585 h_v1280 (of_decide_eq_true rfl)
  have h_v1282 : R 1 0 0 1 v1282 v1282 := (r_land hl h_v616 h_v1281 (of_decide_eq_true rfl))
  have e_v1282 : (v1282 = 1 ↔ v616 = 1 ∧ v1281 = 1) := e_land h_v616 h_v1281 (of_decide_eq_true rfl)
  have h_v1283 : R 1 0 0 1 v1283 v1283 := (r_land hl h_v23 h_v1282 (of_decide_eq_true rfl))
  have e_v1283 : (v1283 = 1 ↔ v23 = 1 ∧ v1282 = 1) := e_land h_v23 h_v1282 (of_decide_eq_true rfl)
  have h_v1284 : R 1 0 0 1 v1284 v1284 := (r_land hl h_v729 h_v1283 (of_decide_eq_true rfl))
  have e_v1284 : (v1284 = 1 ↔ v729 = 1 ∧ v1283 = 1) := e_land h_v729 h_v1283 (of_decide_eq_true rfl)
  have h_v1285 : R 1 0 0 1 v1285 v1285 := (r_land hl h_v750 h_v1284 (of_decide_eq_true rfl))
  have e_v1285 : (v1285 = 1 ↔ v750 = 1 ∧ v1284 = 1) := e_land h_v750 h_v1284 (of_decide_eq_true rfl)
  have h_v1286 : R 1 0 0 1 v1286 v1286 := (r_land hl h_v767 h_v1285 (of_decide_eq_true rfl))
  have e_v1286 : (v1286 = 1 ↔ v767 = 1 ∧ v1285 = 1) := e_land h_v767 h_v1285 (of_decide_eq_true rfl)
  have h_v1287 : R 1 0 0 1 v1287 v1287 := (r_land hl h_v824 h_v1286 (of_decide_eq_true rfl))
  have e_v1287 : (v1287 = 1 ↔ v824 = 1 ∧ v1286 = 1) := e_land h_v824 h_v1286 (of_decide_eq_true rfl)
  clear h_v23 h_v441 h_v444 h_v475 h_v585 h_v616 h_v729 h_v750 h_v767 h_v824 h_v1274 h_v1275 h_v1276 h_v1277 h_v1278 h_v1279 h_v1280 h_v1281 h_v1282 h_v1283 h_v1284 h_v1285 h_v1286
  have h_v1288 : R 1 0 0 1 v1288 v1288 := (r_land hl h_v851 h_v1287 (of_decide_eq_true rfl))
  have e_v1288 : (v1288 = 1 ↔ v851 = 1 ∧ v1287 = 1) := e_land h_v851 h_v1287 (of_decide_eq_true rfl)
  have h_v1289 : R 1 0 0 1 v1289 v1289 := (r_land hl h_v921 h_v1288 (of_decide_eq_true rfl))
  have e_v1289 : (v1289 = 1 ↔ v921 = 1 ∧ v1288 = 1) := e_land h_v921 h_v1288 (of_decide_eq_true rfl)
  have h_v1290 : R 1 0 0 1 v1290 v1290 := (r_land hl h_v1020 h_v1289 (of_decide_eq_true rfl))
  have e_v1290 : (v1290 = 1 ↔ v1020 = 1 ∧ v1289 = 1) := e_land h_v1020 h_v1289 (of_decide_eq_true rfl)
  have h_v1291 : R 1 0 0 1 v1291 v1291 := (r_land hl h_v1088 h_v1290 (of_decide_eq_true rfl))
  have e_v1291 : (v1291 = 1 ↔ v1088 = 1 ∧ v1290 = 1) := e_land h_v1088 h_v1290 (of_decide_eq_true rfl)
  have h_v1292 : R 1 0 0 1 v1292 v1292 := (r_land hl h_v1185 h_v1291 (of_decide_eq_true rfl))
  have e_v1292 : (v1292 = 1 ↔ v1185 = 1 ∧ v1291 = 1) := e_land h_v1185 h_v1291 (of_decide_eq_true rfl)
  have h_v1293 : R 1 0 0 1 v1293 v1293 := (r_land hl h_v1259 h_v1292 (of_decide_eq_true rfl))
  have e_v1293 : (v1293 = 1 ↔ v1259 = 1 ∧ v1292 = 1) := e_land h_v1259 h_v1292 (of_decide_eq_true rfl)
  have k_v1293 : v1293 = 1 := h
  have k_v1259 : v1259 = 1 := ((e_v1293).1 k_v1293).1
  have k_v1292 : v1292 = 1 := ((e_v1293).1 k_v1293).2
  have k_v1185 : v1185 = 1 := ((e_v1292).1 k_v1292).1
  have k_v1291 : v1291 = 1 := ((e_v1292).1 k_v1292).2
  have k_v1088 : v1088 = 1 := ((e_v1291).1 k_v1291).1
  have k_v1290 : v1290 = 1 := ((e_v1291).1 k_v1291).2
  have k_v1020 : v1020 = 1 := ((e_v1290).1 k_v1290).1
  have k_v1289 : v1289 = 1 := ((e_v1290).1 k_v1290).2
  have k_v921 : v921 = 1 := ((e_v1289).1 k_v1289).1
  have k_v1288 : v1288 = 1 := ((e_v1289).1 k_v1289).2
  have k_v851 : v851 = 1 := ((e_v1288).1 k_v1288).1
  have k_v1287 : v1287 = 1 := ((e_v1288).1 k_v1288).2
  have k_v824 : v824 = 1 := ((e_v1287).1 k_v1287).1
  have k_v1286 : v1286 = 1 := ((e_v1287).1 k_v1287).2
  have k_v767 : v767 = 1 := ((e_v1286).1 k_v1286).1
  have k_v1285 : v1285 = 1 := ((e_v1286).1 k_v1286).2
  have k_v750 : v750 = 1 := ((e_v1285).1 k_v1285).1
  have k_v1284 : v1284 = 1 := ((e_v1285).1 k_v1285).2
  have k_v729 : v729 = 1 := ((e_v1284).1 k_v1284).1
  have k_v1283 : v1283 = 1 := ((e_v1284).1 k_v1284).2
  have k_v23 : v23 = 1 := ((e_v1283).1 k_v1283).1
  have k_v1282 : v1282 = 1 := ((e_v1283).1 k_v1283).2
  have k_v616 : v616 = 1 := ((e_v1282).1 k_v1282).1
  have k_v1281 : v1281 = 1 := ((e_v1282).1 k_v1282).2
  have k_v585 : v585 = 1 := ((e_v1281).1 k_v1281).1
  have k_v1280 : v1280 = 1 := ((e_v1281).1 k_v1281).2
  have k_v1279 : v1279 = 1 := ((e_v1280).1 k_v1280).2
  have k_v475 : v475 = 1 := ((e_v1279).1 k_v1279).1
  have k_v1278 : v1278 = 1 := ((e_v1279).1 k_v1279).2
  have k_v444 : v444 = 1 := ((e_v1278).1 k_v1278).1
  have k_v1277 : v1277 = 1 := ((e_v1278).1 k_v1278).2
  have k_v1276 : v1276 = 1 := ((e_v1277).1 k_v1277).2
  have k_v1275 : v1275 = 1 := ((e_v1276).1 k_v1276).2
  have k_v441 : v441 = 1 := ((e_v1275).1 k_v1275).1
  have k_v1274 : v1274 = 1 := ((e_v1275).1 k_v1275).2
  have k_v424 : v424 = 1 := ((e_v1274).1 k_v1274).1
  have k_v1273 : v1273 = 1 := ((e_v1274).1 k_v1274).2
  have k_v403 : v403 = 1 := ((e_v1273).1 k_v1273).1
  have k_v1272 : v1272 = 1 := ((e_v1273).1 k_v1273).2
  have k_v1271 : v1271 = 1 := ((e_v1272).1 k_v1272).2
  have k_v291 : v291 = 1 := ((e_v1271).1 k_v1271).1
  have k_v1270 : v1270 = 1 := ((e_v1271).1 k_v1271).2
  have k_v260 : v260 = 1 := ((e_v1270).1 k_v1270).1
  have k_v1269 : v1269 = 1 := ((e_v1270).1 k_v1270).2
  have k_v1268 : v1268 = 1 := ((e_v1269).1 k_v1269).2
  have k_v147 : v147 = 1 := ((e_v1268).1 k_v1268).1
  have k_v1267 : v1267 = 1 := ((e_v1268).1 k_v1268).2
  have k_v110 : v110 = 1 := ((e_v1267).1 k_v1267).1
  have k_v1266 : v1266 = 1 := ((e_v1267).1 k_v1267).2
  have k_v1265 : v1265 = 1 := ((e_v1266).1 k_v1266).2
  have k_v1264 : v1264 = 1 := ((e_v1265).1 k_v1265).2
  have k_v92 : v92 = 1 := ((e_v1264).1 k_v1264).1
  have k_v1263 : v1263 = 1 := ((e_v1264).1 k_v1264).2
  have k_v75 : v75 = 1 := ((e_v1263).1 k_v1263).1
  have k_v1262 : v1262 = 1 := ((e_v1263).1 k_v1263).2
  have k_v47 : v47 = 1 := ((e_v1262).1 k_v1262).2
  have k_v44 : v44 = 1 := ((e_v47).1 k_v47).1
  have k_v46 : v46 = 1 := ((e_v47).1 k_v47).2
  have k_v109 : v109 = 1 := ((e_v110).1 k_v110).2
  have k_v259 : v259 = 1 := ((e_v260).1 k_v260).2
  have k_v400 : v400 = 1 := ((e_v403).1 k_v403).1
  have k_v402 : v402 = 1 := ((e_v403).1 k_v403).2
  have k_v443 : v443 = 1 := ((e_v444).1 k_v444).2
  have k_v584 : v584 = 1 := ((e_v585).1 k_v585).2
  have k_v20 : v20 = 1 := ((e_v23).1 k_v23).1
  have k_v22 : v22 = 1 := ((e_v23).1 k_v23).2
  have k_v726 : v726 = 1 := ((e_v729).1 k_v729).1
  have k_v728 : v728 = 1 := ((e_v729).1 k_v729).2
  let u14 : ℤ := if v13 = 1 then (sv v7) else (sv v9)
  let u17 : ℕ := if (sv v7) < (sv v15) then 1 else 0
  let u18 : ℤ := if u17 = 1 then (sv v15) else (sv v7)
  have f2 := L2.K27_corner_fixed (sv v7) (sv v9) (0 : ℕ) (sv v10) (sv v11) v13 u14 (sv v15) (0 : ℕ) u18 u18 (sv v7) u14 e_v10 e_v11 (L2.p_le e_v12 e_v13) rfl e_v15 (L2.p_le (L2.p_lt_cc (v := 1) (843314856) (843314857) e_v15 e_v9 (of_decide_eq_true rfl)) (of_decide_eq_true rfl)) (L2.p_max (L2.p_ult _ _) rfl) (L2.p_sel_f _ _) (L2.p_sel_f _ _) (L2.p_sel_f _ _)
  have f24 := L2.K8_in_range True (sv v0) (sv v1) v20 (sv v9) v22 v23 (L2.p_clt (-1) e_v19 e_v20) e_v9 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f23 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v27) (sv v29) (sv v30) (sv v32) (sv v33) (sv v35) v37 v39 v40 (sv v41) f24 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v26 (L2.p_sel e_v27)) (L2.p_addc (-4) e_v29 e_v28) (L2.p_max e_v26 (L2.p_sel e_v30)) (L2.p_addc (4) e_v32 e_v31) e_v33 (L2.p_min e_v34 (L2.p_sel e_v35)) (L2.p_ltc (421657430) e_v36 e_v37) (L2.p_clt (421657427) e_v38 e_v39) e_v40 (L2.p_sel e_v41)
  have f60 := L2.K5_ihalf (sv v2) (sv v3) (sv v42) (sv v43) e_v42 e_v43
  have f64 := L2.K8_in_range True (sv v42) (sv v43) v44 (sv v9) v46 v47 (L2.p_clt (-1) e_v19 e_v44) e_v9 (L2.p_le e_v45 e_v46) e_v47 (L2.X1_top _ k_v47)
  have f63 := L2.K9_isin True (sv v42) (sv v43) (sv t42.1) (sv t43.1) (sv v51) (sv v52) (sv v53) (sv v54) (sv v33) (sv v56) v57 v58 v59 (sv v60) f64 (L2.p_sin e_t42_1) (L2.p_sin e_t43_1) (L2.p_min e_v50 (L2.p_sel e_v51)) (L2.p_addc (-4) (L2.p_add_comm e_v52) e_v28) (L2.p_max e_v50 (L2.p_sel e_v53)) (L2.p_addc (4) (L2.p_add_comm e_v54) e_v31) e_v33 (L2.p_min e_v55 (L2.p_sel e_v56)) (L2.p_ltc (421657430) e_v36 e_v57) (L2.p_clt (421657427) e_v38 e_v58) e_v59 (L2.p_sel e_v60)
  have f100 := L2.K6_imul True (sv v29) (sv v41) (sv v52) (sv v60) (sv v61) v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 (sv v78) v79 v80 (sv v81) v82 v83 (sv v84) v85 v86 (sv v87) (sv v89) (sv v91) e_v61 e_v62 e_v63 e_v64 e_v65 (L2.p_and_comm e_v66) e_v67 e_v68 e_v69 e_v70 e_v71 (L2.p_and_comm e_v72) e_v73 e_v74 e_v75 (L2.X1_top _ k_v75) e_v76 e_v77 (L2.p_sel e_v78) e_v79 e_v80 (L2.p_sel e_v81) e_v82 e_v83 (L2.p_sel e_v84) e_v85 e_v86 (L2.p_sel e_v87) (L2.p_mul (L2.p_mul_comm e_v88) e_v89) (L2.p_mulc (L2.p_mul_comm e_v90) e_v91)
  have f22 := L2.K14_iso_base_a True (sv v2) (sv v3) (sv v0) (sv v1) (sv v29) (sv v41) (sv v42) (sv v43) (sv v52) (sv v60) (sv v89) (sv v91) v92 f23 f60 f63 f100 (L2.p_clt (-1) e_v19 e_v92) (L2.X1_top _ k_v92)
  have f139 := L2.K8_in_range True (sv v0) (sv v1) v20 (sv v9) v22 v23 (L2.p_clt (-1) e_v19 e_v20) e_v9 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f149 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v94) (sv v95) (sv v97) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v94) e_v28) e_v95 (L2.p_max e_v96 (L2.p_sel e_v97))
  have f163 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v102) (sv v33) (sv v104) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v102) e_v31) e_v33 (L2.p_min e_v103 (L2.p_sel e_v104))
  have f138 := L2.K10_icos True (sv v0) (sv v1) (sv v97) (sv v95) v99 (sv v100) (sv v104) (sv v33) v106 (sv v107) f139 f149 e_v95 (L2.p_clt (843314855) e_v98 e_v99) (L2.p_sel e_v100) f163 e_v33 (L2.p_ltc (1) e_v105 e_v106) (L2.p_sel e_v107)
  have f178 := L2.K5_ihalf (sv v3) (sv v3) (sv v108) (sv v43) e_v108 e_v43
  have f182 := L2.K8_in_range True (sv v108) (sv v43) v109 (sv v9) v46 v110 (L2.p_clt (-1) e_v19 e_v109) e_v9 (L2.p_le e_v45 e_v46) (L2.p_and_comm e_v110) (L2.X1_top _ k_v110)
  have f192 := L2.K3_cos_lo (sv v43) (sv t43.2) (sv v112) (sv v95) (sv v114) (L2.p_cos e_t43_2) (L2.p_addc (-4) (L2.p_add_comm e_v112) e_v28) e_v95 (L2.p_max e_v113 (L2.p_sel e_v114))
  let u117 : ℤ := L2.cosI (sv v108)
  let u118 : ℤ := (sv v31) + u117
  let u119 : ℕ := if u118 < (sv v33) then 1 else 0
  let u120 : ℤ := if u119 = 1 then u118 else (sv v33)
  have f206 := L2.K3_cos_hi (sv v108) u117 u118 (sv v33) u120 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u121 : ℕ := if (sv v108) < (sv v105) then 1 else 0
  let u122 : ℤ := if u121 = 1 then (sv v33) else u120
  have f181 := L2.K10_icos True (sv v108) (sv v43) (sv v114) (sv v95) v115 (sv v116) u120 (sv v33) u121 u122 f182 f192 e_v95 (L2.p_clt (843314855) e_v98 e_v115) (L2.p_sel e_v116) f206 e_v33 (L2.p_ltc (1) e_v105 (L2.p_ult _ _)) rfl
  have f221 := L2.K8_in_range True (sv v108) (sv v43) v109 (sv v9) v46 v110 (L2.p_clt (-1) e_v19 e_v109) e_v9 (L2.p_le e_v45 e_v46) (L2.p_and_comm e_v110) (L2.X1_top _ k_v110)
  have f220 := L2.K9_isin True (sv v108) (sv v43) (sv t108.1) (sv t43.1) (sv v125) (sv v126) (sv v127) (sv v128) (sv v33) (sv v130) v131 v58 v132 (sv v133) f221 (L2.p_sin e_t108_1) (L2.p_sin e_t43_1) (L2.p_min e_v124 (L2.p_sel e_v125)) (L2.p_addc (-4) (L2.p_add_comm e_v126) e_v28) (L2.p_max e_v124 (L2.p_sel e_v127)) (L2.p_addc (4) (L2.p_add_comm e_v128) e_v31) e_v33 (L2.p_min e_v129 (L2.p_sel e_v130)) (L2.p_ltc (421657430) e_v36 e_v131) (L2.p_clt (421657427) e_v38 e_v58) (L2.p_and_comm e_v132) (L2.p_sel e_v133)
  have f257 := L2.K6_imul True (sv v100) (sv v107) (sv v126) (sv v133) (sv v61) v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 (sv v150) v151 v152 (sv v153) v154 v155 (sv v156) v157 v158 (sv v159) (sv v161) (sv v163) e_v61 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 e_v140 e_v141 e_v142 e_v143 (L2.p_and_comm e_v144) e_v145 e_v146 e_v147 (L2.X1_top _ k_v147) e_v148 e_v149 (L2.p_sel e_v150) e_v151 e_v152 (L2.p_sel e_v153) e_v154 e_v155 (L2.p_sel e_v156) e_v157 e_v158 (L2.p_sel e_v159) (L2.p_mul (L2.p_mul_comm e_v160) e_v161) (L2.p_mulc (L2.p_mul_comm e_v162) e_v163)
  let u168 : ℕ := if u122 < (sv v61) then 1 else 0
  let u169 : ℤ := if u168 = 1 then (sv v163) else (sv v161)
  have f290 := L2.K11_qdiv (sv v116) u122 (sv v161) (sv v163) v164 v165 (sv v61) v166 (sv v167) u168 u169 (L2.p_clt (0) e_v61 e_v164) e_v165 e_v61 e_v166 (L2.p_sel e_v167) (L2.p_ult _ _) rfl
  have f308 := L2.K3_cos_lo (sv v172) (sv t172.2) (sv v175) (sv v95) (sv v177) (L2.p_cos e_t172_2) (L2.p_addc (-4) (L2.p_add_comm e_v175) e_v28) e_v95 (L2.p_max e_v176 (L2.p_sel e_v177))
  have f317 := L2.K3_cos_hi (sv v172) (sv t172.2) (sv v178) (sv v33) (sv v180) (L2.p_cos e_t172_2) (L2.p_addc (4) (L2.p_add_comm e_v178) e_v31) e_v33 (L2.p_min e_v179 (L2.p_sel e_v180))
  have f326 := L2.K3_sin_hi (sv v172) (sv t172.1) (sv v182) (sv v33) (sv v184) (L2.p_sin e_t172_1) (L2.p_addc (4) (L2.p_add_comm e_v182) e_v31) e_v33 (L2.p_min e_v183 (L2.p_sel e_v184))
  have f335 := L2.K3_sin_lo (sv v172) (sv t172.1) (sv v185) (L2.p_sin e_t172_1) (L2.p_addc (-4) (L2.p_add_comm e_v185) e_v28)
  have f301 := L2.K12_atan_lo (sv v116) (sv v167) (sv v61) v166 (sv v170) (sv v171) (sv v172) v173 (sv v177) (sv v180) (sv v184) (sv v185) (sv v186) (sv v187) (sv v188) (sv v189) v191 v193 v194 v195 (sv v196) v198 v199 v200 v201 v202 (sv v203) v205 v206 v207 v166 v208 v209 (sv v210) (sv v211) (sv v212) (sv v213) e_v61 e_v166 e_v170 (L2.p_sel e_v171) (L2.p_hint e_v172) e_v173 f308 f317 f326 f335 (L2.p_sel e_v186) (L2.p_sel e_v187) (L2.p_mul_comm e_v188) (L2.p_mul_comm e_v189) (L2.p_le e_v190 e_v191) (L2.p_le e_v192 e_v193) e_v194 e_v195 e_v196 (L2.p_le e_v197 e_v198) (L2.p_clt (-1) e_v19 e_v199) e_v200 (L2.p_and_comm e_v201) e_v202 e_v203 (L2.p_le e_v204 e_v205) (L2.p_or_comm e_v206) e_v207 (L2.p_not_not e_v173) e_v208 e_v209 e_v210 (L2.p_sel e_v211) e_v212 (L2.p_sel e_v213)
  let u214 : ℤ := (sv v61) - u122
  let u215 : ℤ := if u168 = 1 then u214 else u122
  let u216 : ℤ := 0
  let u217 : ℤ := L2.cosI u216
  let u218 : ℤ := (sv v28) + u217
  let u219 : ℕ := if u218 < (sv v95) then 1 else 0
  let u220 : ℤ := if u219 = 1 then (sv v95) else u218
  have f381 := L2.K3_cos_lo u216 u217 u218 (sv v95) u220 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u221 : ℤ := (sv v31) + u217
  let u222 : ℕ := if u221 < (sv v33) then 1 else 0
  let u223 : ℤ := if u222 = 1 then u221 else (sv v33)
  have f390 := L2.K3_cos_hi u216 u217 u221 (sv v33) u223 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u224 : ℤ := L2.sinI u216
  let u225 : ℤ := (sv v31) + u224
  let u226 : ℕ := if u225 < (sv v33) then 1 else 0
  let u227 : ℤ := if u226 = 1 then u225 else (sv v33)
  have f399 := L2.K3_sin_hi u216 u224 u225 (sv v33) u227 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u228 : ℤ := (sv v28) + u224
  have f408 := L2.K3_sin_lo u216 u224 u228 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u229 : ℤ := if u168 = 1 then u220 else u223
  let u230 : ℤ := if u168 = 1 then u227 else u228
  let u231 : ℤ := u169 * u230
  let u232 : ℤ := u215 * u229
  let u233 : ℕ := if u232 < u231 then 1 else 0
  let u234 : ℕ := if u233 = 1 then 0 else 1
  let u235 : ℕ := if u231 < u232 then 1 else 0
  let u236 : ℕ := if u235 = 1 then 0 else 1
  let u237 : ℕ := if (sv v61) < u216 then 1 else 0
  let u238 : ℕ := if u237 = 1 then 0 else 1
  let u239 : ℕ := if (sv v196) < u216 then 1 else 0
  let u240 : ℕ := if u239 = 1 then 0 else 1
  let u241 : ℕ := if (sv v19) < u220 then 1 else 0
  let u242 : ℕ := if u234 = 1 ∧ u241 = 1 then 1 else 0
  let u243 : ℕ := if u240 = 1 ∧ u242 = 1 then 1 else 0
  let u244 : ℕ := if u238 = 1 ∨ u243 = 1 then 1 else 0
  let u245 : ℕ := if u216 < (sv v203) then 1 else 0
  let u246 : ℕ := if u245 = 1 then 0 else 1
  let u247 : ℕ := if u236 = 1 ∨ u246 = 1 then 1 else 0
  let u248 : ℕ := if u168 = 1 ∧ u244 = 1 then 1 else 0
  let u249 : ℕ := if u168 = 1 then 0 else 1
  let u250 : ℕ := if u247 = 1 ∧ u249 = 1 then 1 else 0
  let u251 : ℕ := if u248 = 1 ∨ u250 = 1 then 1 else 0
  let u252 : ℤ := (sv v61) - u216
  let u253 : ℤ := if u168 = 1 then u252 else u216
  let u254 : ℤ := if u251 = 1 then u253 else (sv v203)
  have f375 := L2.K12_atan_hi u122 u169 (sv v61) u168 u214 u215 u216 u220 u223 u227 u228 u229 u230 u231 u232 u234 u236 u237 u238 (sv v196) u240 u241 u242 u243 u244 (sv v203) u246 u247 u248 u249 u250 u251 u252 u253 (sv v203) u254 e_v61 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f381 f390 f399 f408 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v196 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v19 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v203 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v203 rfl
  let u256 : ℤ := if v165 = 1 then (sv v203) else u254
  have f177 := L2.K19_iso_angle_pt True (sv v3) (sv v100) (sv v107) (sv v108) (sv v43) (sv v116) u122 (sv v126) (sv v133) (sv v161) (sv v163) (sv v167) u169 v165 v164 (sv v213) u254 (sv v212) (sv v203) (sv v255) u256 f178 f181 f220 f257 f290 (L2.p_not_not e_v165) f301 f375 e_v212 e_v203 (L2.p_sel e_v255) rfl
  have f453 := L2.K5_ihalf (sv v2) (sv v2) (sv v42) (sv v257) e_v42 e_v257
  have f457 := L2.K8_in_range True (sv v42) (sv v257) v44 (sv v9) v259 v260 (L2.p_clt (-1) e_v19 e_v44) e_v9 (L2.p_le e_v258 e_v259) e_v260 (L2.X1_top _ k_v260)
  let u261 : ℤ := L2.cosI (sv v257)
  let u262 : ℤ := (sv v28) + u261
  let u263 : ℕ := if u262 < (sv v95) then 1 else 0
  let u264 : ℤ := if u263 = 1 then (sv v95) else u262
  have f467 := L2.K3_cos_lo (sv v257) u261 u262 (sv v95) u264 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u265 : ℕ := if (sv v98) < (sv v257) then 1 else 0
  let u266 : ℤ := if u265 = 1 then (sv v95) else u264
  let u267 : ℤ := L2.cosI (sv v42)
  let u268 : ℤ := (sv v31) + u267
  let u269 : ℕ := if u268 < (sv v33) then 1 else 0
  let u270 : ℤ := if u269 = 1 then u268 else (sv v33)
  have f481 := L2.K3_cos_hi (sv v42) u267 u268 (sv v33) u270 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u271 : ℕ := if (sv v42) < (sv v105) then 1 else 0
  let u272 : ℤ := if u271 = 1 then (sv v33) else u270
  have f456 := L2.K10_icos True (sv v42) (sv v257) u264 (sv v95) u265 u266 u270 (sv v33) u271 u272 f457 f467 e_v95 (L2.p_clt (843314855) e_v98 (L2.p_ult _ _)) rfl f481 e_v33 (L2.p_ltc (1) e_v105 (L2.p_ult _ _)) rfl
  have f496 := L2.K8_in_range True (sv v42) (sv v257) v44 (sv v9) v259 v260 (L2.p_clt (-1) e_v19 e_v44) e_v9 (L2.p_le e_v258 e_v259) e_v260 (L2.X1_top _ k_v260)
  have f495 := L2.K9_isin True (sv v42) (sv v257) (sv t42.1) (sv t257.1) (sv v275) (sv v276) (sv v277) (sv v278) (sv v33) (sv v280) v57 v281 v282 (sv v283) f496 (L2.p_sin e_t42_1) (L2.p_sin e_t257_1) (L2.p_min e_v274 (L2.p_sel e_v275)) (L2.p_addc (-4) (L2.p_add_comm e_v276) e_v28) (L2.p_max e_v274 (L2.p_sel e_v277)) (L2.p_addc (4) (L2.p_add_comm e_v278) e_v31) e_v33 (L2.p_min e_v279 (L2.p_sel e_v280)) (L2.p_ltc (421657430) e_v36 e_v57) (L2.p_clt (421657427) e_v38 e_v281) e_v282 (L2.p_sel e_v283)
  let u285 : ℕ := if v284 = 1 then 0 else 1
  let u287 : ℕ := if v286 = 1 then 0 else 1
  let u288 : ℕ := if v284 = 1 ∧ u287 = 1 then 1 else 0
  let u292 : ℕ := if v135 = 1 ∧ v289 = 1 then 1 else 0
  let u293 : ℕ := if u288 = 1 ∨ u292 = 1 then 1 else 0
  let u294 : ℤ := if u293 = 1 then (sv v107) else (sv v100)
  let u295 : ℕ := if v139 = 1 ∧ u285 = 1 then 1 else 0
  let u296 : ℕ := if v138 = 1 ∨ u295 = 1 then 1 else 0
  let u297 : ℤ := if u296 = 1 then (sv v283) else (sv v276)
  let u298 : ℕ := if v138 = 1 ∧ v289 = 1 then 1 else 0
  let u299 : ℕ := if u288 = 1 ∨ u298 = 1 then 1 else 0
  let u300 : ℤ := if u299 = 1 then (sv v100) else (sv v107)
  let u301 : ℕ := if v139 = 1 ∧ u288 = 1 then 1 else 0
  let u302 : ℕ := if v138 = 1 ∨ u301 = 1 then 1 else 0
  let u303 : ℤ := if u302 = 1 then (sv v276) else (sv v283)
  let u304 : ℤ := u294 * u297
  let u305 : ℤ := u304 / 2 ^ 28
  let u306 : ℤ := u300 * u303
  let u307 : ℤ := -((-u306) / 2 ^ 28)
  have f532 := L2.K6_imul True (sv v100) (sv v107) (sv v276) (sv v283) (sv v61) v134 v135 v136 v137 v138 v139 v284 u285 v286 u287 u288 v289 v290 v291 u292 u293 u294 u295 u296 u297 u298 u299 u300 u301 u302 u303 u305 u307 e_v61 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 e_v284 (L2.p_unot _) e_v286 (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) e_v289 e_v290 e_v291 (L2.X1_top _ k_v291) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl)
  let u308 : ℕ := if (sv v61) < u305 then 1 else 0
  let u309 : ℕ := if u308 = 1 then 0 else 1
  let u310 : ℕ := if u266 < (sv v61) then 1 else 0
  let u311 : ℤ := if u310 = 1 then u305 else u307
  let u312 : ℕ := if u272 < (sv v61) then 1 else 0
  let u313 : ℤ := if u312 = 1 then u307 else u305
  have f565 := L2.K11_qdiv u266 u272 u305 u307 u308 u309 (sv v61) u310 u311 u312 u313 (L2.p_clt (0) e_v61 (L2.p_ult _ _)) (L2.p_unot _) e_v61 (L2.p_ult _ _) rfl (L2.p_ult _ _) rfl
  let u314 : ℤ := (sv v61) - u266
  let u315 : ℤ := if u310 = 1 then u314 else u266
  let u316 : ℤ := 0
  let u317 : ℕ := if u310 = 1 then 0 else 1
  let u318 : ℤ := L2.cosI u316
  let u319 : ℤ := (sv v28) + u318
  let u320 : ℕ := if u319 < (sv v95) then 1 else 0
  let u321 : ℤ := if u320 = 1 then (sv v95) else u319
  have f583 := L2.K3_cos_lo u316 u318 u319 (sv v95) u321 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u322 : ℤ := (sv v31) + u318
  let u323 : ℕ := if u322 < (sv v33) then 1 else 0
  let u324 : ℤ := if u323 = 1 then u322 else (sv v33)
  have f592 := L2.K3_cos_hi u316 u318 u322 (sv v33) u324 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u325 : ℤ := L2.sinI u316
  let u326 : ℤ := (sv v31) + u325
  let u327 : ℕ := if u326 < (sv v33) then 1 else 0
  let u328 : ℤ := if u327 = 1 then u326 else (sv v33)
  have f601 := L2.K3_sin_hi u316 u325 u326 (sv v33) u328 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u329 : ℤ := (sv v28) + u325
  have f610 := L2.K3_sin_lo u316 u325 u329 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u330 : ℤ := if u317 = 1 then u321 else u324
  let u331 : ℤ := if u317 = 1 then u328 else u329
  let u332 : ℤ := u311 * u331
  let u333 : ℤ := u315 * u330
  let u334 : ℕ := if u333 < u332 then 1 else 0
  let u335 : ℕ := if u334 = 1 then 0 else 1
  let u336 : ℕ := if u332 < u333 then 1 else 0
  let u337 : ℕ := if u336 = 1 then 0 else 1
  let u338 : ℕ := if (sv v61) < u316 then 1 else 0
  let u339 : ℕ := if u338 = 1 then 0 else 1
  let u340 : ℕ := if (sv v196) < u316 then 1 else 0
  let u341 : ℕ := if u340 = 1 then 0 else 1
  let u342 : ℕ := if (sv v19) < u321 then 1 else 0
  let u343 : ℕ := if u335 = 1 ∧ u342 = 1 then 1 else 0
  let u344 : ℕ := if u341 = 1 ∧ u343 = 1 then 1 else 0
  let u345 : ℕ := if u339 = 1 ∨ u344 = 1 then 1 else 0
  let u346 : ℕ := if u316 < (sv v203) then 1 else 0
  let u347 : ℕ := if u346 = 1 then 0 else 1
  let u348 : ℕ := if u337 = 1 ∨ u347 = 1 then 1 else 0
  let u349 : ℕ := if u317 = 1 ∧ u345 = 1 then 1 else 0
  let u350 : ℕ := if u310 = 1 ∧ u348 = 1 then 1 else 0
  let u351 : ℕ := if u349 = 1 ∨ u350 = 1 then 1 else 0
  let u352 : ℤ := (sv v61) - u316
  let u353 : ℤ := if u310 = 1 then u352 else u316
  let u354 : ℤ := if u351 = 1 then u353 else (sv v212)
  have f576 := L2.K12_atan_lo u266 u311 (sv v61) u310 u314 u315 u316 u317 u321 u324 u328 u329 u330 u331 u332 u333 u335 u337 u338 u339 (sv v196) u341 u342 u343 u344 u345 (sv v203) u347 u348 u349 u310 u350 u351 u352 u353 (sv v212) u354 e_v61 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f583 f592 f601 f610 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v196 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v19 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v203 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl e_v212 rfl
  let u355 : ℤ := (sv v61) - u272
  let u356 : ℤ := if u312 = 1 then u355 else u272
  let u357 : ℤ := 0
  let u358 : ℤ := L2.cosI u357
  let u359 : ℤ := (sv v28) + u358
  let u360 : ℕ := if u359 < (sv v95) then 1 else 0
  let u361 : ℤ := if u360 = 1 then (sv v95) else u359
  have f656 := L2.K3_cos_lo u357 u358 u359 (sv v95) u361 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u362 : ℤ := (sv v31) + u358
  let u363 : ℕ := if u362 < (sv v33) then 1 else 0
  let u364 : ℤ := if u363 = 1 then u362 else (sv v33)
  have f665 := L2.K3_cos_hi u357 u358 u362 (sv v33) u364 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u365 : ℤ := L2.sinI u357
  let u366 : ℤ := (sv v31) + u365
  let u367 : ℕ := if u366 < (sv v33) then 1 else 0
  let u368 : ℤ := if u367 = 1 then u366 else (sv v33)
  have f674 := L2.K3_sin_hi u357 u365 u366 (sv v33) u368 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u369 : ℤ := (sv v28) + u365
  have f683 := L2.K3_sin_lo u357 u365 u369 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u370 : ℤ := if u312 = 1 then u361 else u364
  let u371 : ℤ := if u312 = 1 then u368 else u369
  let u372 : ℤ := u313 * u371
  let u373 : ℤ := u356 * u370
  let u374 : ℕ := if u373 < u372 then 1 else 0
  let u375 : ℕ := if u374 = 1 then 0 else 1
  let u376 : ℕ := if u372 < u373 then 1 else 0
  let u377 : ℕ := if u376 = 1 then 0 else 1
  let u378 : ℕ := if (sv v61) < u357 then 1 else 0
  let u379 : ℕ := if u378 = 1 then 0 else 1
  let u380 : ℕ := if (sv v196) < u357 then 1 else 0
  let u381 : ℕ := if u380 = 1 then 0 else 1
  let u382 : ℕ := if (sv v19) < u361 then 1 else 0
  let u383 : ℕ := if u375 = 1 ∧ u382 = 1 then 1 else 0
  let u384 : ℕ := if u381 = 1 ∧ u383 = 1 then 1 else 0
  let u385 : ℕ := if u379 = 1 ∨ u384 = 1 then 1 else 0
  let u386 : ℕ := if u357 < (sv v203) then 1 else 0
  let u387 : ℕ := if u386 = 1 then 0 else 1
  let u388 : ℕ := if u377 = 1 ∨ u387 = 1 then 1 else 0
  let u389 : ℕ := if u312 = 1 ∧ u385 = 1 then 1 else 0
  let u390 : ℕ := if u312 = 1 then 0 else 1
  let u391 : ℕ := if u388 = 1 ∧ u390 = 1 then 1 else 0
  let u392 : ℕ := if u389 = 1 ∨ u391 = 1 then 1 else 0
  let u393 : ℤ := (sv v61) - u357
  let u394 : ℤ := if u312 = 1 then u393 else u357
  let u395 : ℤ := if u392 = 1 then u394 else (sv v203)
  have f650 := L2.K12_atan_hi u272 u313 (sv v61) u312 u355 u356 u357 u361 u364 u368 u369 u370 u371 u372 u373 u375 u377 u378 u379 (sv v196) u381 u382 u383 u384 u385 (sv v203) u387 u388 u389 u390 u391 u392 u393 u394 (sv v203) u395 e_v61 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f656 f665 f674 f683 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v196 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v19 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v203 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v203 rfl
  let u396 : ℤ := if u309 = 1 then (sv v212) else u354
  let u397 : ℤ := if u309 = 1 then (sv v203) else u395
  have f452 := L2.K19_iso_angle_pt True (sv v2) (sv v100) (sv v107) (sv v42) (sv v257) u266 u272 (sv v276) (sv v283) u305 u307 u311 u313 u309 u308 u354 u395 (sv v212) (sv v203) u396 u397 f453 f456 f495 f532 f565 (L2.p_not_not (L2.p_unot _)) f576 f650 e_v212 e_v203 rfl rfl
  have f137 := L2.K20_iso_angle True (sv v2) (sv v3) (sv v0) (sv v1) (sv v100) (sv v107) (sv v255) u256 v165 u396 u397 u309 f138 f177 f452
  have f729 := L2.K8_in_range True (sv v0) (sv v1) v20 (sv v9) v22 v23 (L2.p_clt (-1) e_v19 e_v20) e_v9 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f728 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v27) (sv v29) (sv v30) (sv v32) (sv v33) (sv v35) v37 v39 v40 (sv v41) f729 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v26 (L2.p_sel e_v27)) (L2.p_addc (-4) e_v29 e_v28) (L2.p_max e_v26 (L2.p_sel e_v30)) (L2.p_addc (4) e_v32 e_v31) e_v33 (L2.p_min e_v34 (L2.p_sel e_v35)) (L2.p_ltc (421657430) e_v36 e_v37) (L2.p_clt (421657427) e_v38 e_v39) e_v40 (L2.p_sel e_v41)
  have f765 := L2.K5_ihalf (sv v4) (sv v5) (sv v398) (sv v399) e_v398 e_v399
  have f769 := L2.K8_in_range True (sv v398) (sv v399) v400 (sv v9) v402 v403 (L2.p_clt (-1) e_v19 e_v400) e_v9 (L2.p_le e_v401 e_v402) e_v403 (L2.X1_top _ k_v403)
  have f768 := L2.K9_isin True (sv v398) (sv v399) (sv t398.1) (sv t399.1) (sv v407) (sv v408) (sv v409) (sv v410) (sv v33) (sv v412) v413 v414 v415 (sv v416) f769 (L2.p_sin e_t398_1) (L2.p_sin e_t399_1) (L2.p_min e_v406 (L2.p_sel e_v407)) (L2.p_addc (-4) (L2.p_add_comm e_v408) e_v28) (L2.p_max e_v406 (L2.p_sel e_v409)) (L2.p_addc (4) (L2.p_add_comm e_v410) e_v31) e_v33 (L2.p_min e_v411 (L2.p_sel e_v412)) (L2.p_ltc (421657430) e_v36 e_v413) (L2.p_clt (421657427) e_v38 e_v414) e_v415 (L2.p_sel e_v416)
  have f805 := L2.K6_imul True (sv v29) (sv v41) (sv v408) (sv v416) (sv v61) v62 v63 v64 v65 v66 v67 v417 v418 v419 v420 v421 v422 v423 v424 v425 v426 (sv v427) v428 v429 (sv v430) v431 v432 (sv v433) v434 v435 (sv v436) (sv v438) (sv v440) e_v61 e_v62 e_v63 e_v64 e_v65 (L2.p_and_comm e_v66) e_v67 e_v417 e_v418 e_v419 e_v420 (L2.p_and_comm e_v421) e_v422 e_v423 e_v424 (L2.X1_top _ k_v424) e_v425 e_v426 (L2.p_sel e_v427) e_v428 e_v429 (L2.p_sel e_v430) e_v431 e_v432 (L2.p_sel e_v433) e_v434 e_v435 (L2.p_sel e_v436) (L2.p_mul (L2.p_mul_comm e_v437) e_v438) (L2.p_mulc (L2.p_mul_comm e_v439) e_v440)
  have f727 := L2.K14_iso_base_a True (sv v4) (sv v5) (sv v0) (sv v1) (sv v29) (sv v41) (sv v398) (sv v399) (sv v408) (sv v416) (sv v438) (sv v440) v441 f728 f765 f768 f805 (L2.p_clt (-1) e_v19 e_v441) (L2.X1_top _ k_v441)
  have f844 := L2.K8_in_range True (sv v0) (sv v1) v20 (sv v9) v22 v23 (L2.p_clt (-1) e_v19 e_v20) e_v9 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f854 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v94) (sv v95) (sv v97) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v94) e_v28) e_v95 (L2.p_max e_v96 (L2.p_sel e_v97))
  have f868 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v102) (sv v33) (sv v104) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v102) e_v31) e_v33 (L2.p_min e_v103 (L2.p_sel e_v104))
  have f843 := L2.K10_icos True (sv v0) (sv v1) (sv v97) (sv v95) v99 (sv v100) (sv v104) (sv v33) v106 (sv v107) f844 f854 e_v95 (L2.p_clt (843314855) e_v98 e_v99) (L2.p_sel e_v100) f868 e_v33 (L2.p_ltc (1) e_v105 e_v106) (L2.p_sel e_v107)
  have f883 := L2.K5_ihalf (sv v5) (sv v5) (sv v442) (sv v399) e_v442 e_v399
  have f887 := L2.K8_in_range True (sv v442) (sv v399) v443 (sv v9) v402 v444 (L2.p_clt (-1) e_v19 e_v443) e_v9 (L2.p_le e_v401 e_v402) (L2.p_and_comm e_v444) (L2.X1_top _ k_v444)
  have f897 := L2.K3_cos_lo (sv v399) (sv t399.2) (sv v446) (sv v95) (sv v448) (L2.p_cos e_t399_2) (L2.p_addc (-4) (L2.p_add_comm e_v446) e_v28) e_v95 (L2.p_max e_v447 (L2.p_sel e_v448))
  let u451 : ℤ := L2.cosI (sv v442)
  let u452 : ℤ := (sv v31) + u451
  let u453 : ℕ := if u452 < (sv v33) then 1 else 0
  let u454 : ℤ := if u453 = 1 then u452 else (sv v33)
  have f911 := L2.K3_cos_hi (sv v442) u451 u452 (sv v33) u454 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u455 : ℕ := if (sv v442) < (sv v105) then 1 else 0
  let u456 : ℤ := if u455 = 1 then (sv v33) else u454
  have f886 := L2.K10_icos True (sv v442) (sv v399) (sv v448) (sv v95) v449 (sv v450) u454 (sv v33) u455 u456 f887 f897 e_v95 (L2.p_clt (843314855) e_v98 e_v449) (L2.p_sel e_v450) f911 e_v33 (L2.p_ltc (1) e_v105 (L2.p_ult _ _)) rfl
  have f926 := L2.K8_in_range True (sv v442) (sv v399) v443 (sv v9) v402 v444 (L2.p_clt (-1) e_v19 e_v443) e_v9 (L2.p_le e_v401 e_v402) (L2.p_and_comm e_v444) (L2.X1_top _ k_v444)
  have f925 := L2.K9_isin True (sv v442) (sv v399) (sv t442.1) (sv t399.1) (sv v459) (sv v460) (sv v461) (sv v462) (sv v33) (sv v464) v465 v414 v466 (sv v467) f926 (L2.p_sin e_t442_1) (L2.p_sin e_t399_1) (L2.p_min e_v458 (L2.p_sel e_v459)) (L2.p_addc (-4) (L2.p_add_comm e_v460) e_v28) (L2.p_max e_v458 (L2.p_sel e_v461)) (L2.p_addc (4) (L2.p_add_comm e_v462) e_v31) e_v33 (L2.p_min e_v463 (L2.p_sel e_v464)) (L2.p_ltc (421657430) e_v36 e_v465) (L2.p_clt (421657427) e_v38 e_v414) (L2.p_and_comm e_v466) (L2.p_sel e_v467)
  have f962 := L2.K6_imul True (sv v100) (sv v107) (sv v460) (sv v467) (sv v61) v134 v135 v136 v137 v138 v139 v468 v469 v470 v471 v472 v473 v474 v475 v476 v477 (sv v478) v479 v480 (sv v481) v482 v483 (sv v484) v485 v486 (sv v487) (sv v489) (sv v491) e_v61 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 e_v468 e_v469 e_v470 e_v471 (L2.p_and_comm e_v472) e_v473 e_v474 e_v475 (L2.X1_top _ k_v475) e_v476 e_v477 (L2.p_sel e_v478) e_v479 e_v480 (L2.p_sel e_v481) e_v482 e_v483 (L2.p_sel e_v484) e_v485 e_v486 (L2.p_sel e_v487) (L2.p_mul (L2.p_mul_comm e_v488) e_v489) (L2.p_mulc (L2.p_mul_comm e_v490) e_v491)
  let u496 : ℕ := if u456 < (sv v61) then 1 else 0
  let u497 : ℤ := if u496 = 1 then (sv v491) else (sv v489)
  have f995 := L2.K11_qdiv (sv v450) u456 (sv v489) (sv v491) v492 v493 (sv v61) v494 (sv v495) u496 u497 (L2.p_clt (0) e_v61 e_v492) e_v493 e_v61 e_v494 (L2.p_sel e_v495) (L2.p_ult _ _) rfl
  have f1013 := L2.K3_cos_lo (sv v500) (sv t500.2) (sv v503) (sv v95) (sv v505) (L2.p_cos e_t500_2) (L2.p_addc (-4) (L2.p_add_comm e_v503) e_v28) e_v95 (L2.p_max e_v504 (L2.p_sel e_v505))
  have f1022 := L2.K3_cos_hi (sv v500) (sv t500.2) (sv v506) (sv v33) (sv v508) (L2.p_cos e_t500_2) (L2.p_addc (4) (L2.p_add_comm e_v506) e_v31) e_v33 (L2.p_min e_v507 (L2.p_sel e_v508))
  have f1031 := L2.K3_sin_hi (sv v500) (sv t500.1) (sv v510) (sv v33) (sv v512) (L2.p_sin e_t500_1) (L2.p_addc (4) (L2.p_add_comm e_v510) e_v31) e_v33 (L2.p_min e_v511 (L2.p_sel e_v512))
  have f1040 := L2.K3_sin_lo (sv v500) (sv t500.1) (sv v513) (L2.p_sin e_t500_1) (L2.p_addc (-4) (L2.p_add_comm e_v513) e_v28)
  have f1006 := L2.K12_atan_lo (sv v450) (sv v495) (sv v61) v494 (sv v498) (sv v499) (sv v500) v501 (sv v505) (sv v508) (sv v512) (sv v513) (sv v514) (sv v515) (sv v516) (sv v517) v519 v521 v522 v523 (sv v196) v525 v526 v527 v528 v529 (sv v203) v531 v532 v533 v494 v534 v535 (sv v536) (sv v537) (sv v212) (sv v538) e_v61 e_v494 e_v498 (L2.p_sel e_v499) (L2.p_hint e_v500) e_v501 f1013 f1022 f1031 f1040 (L2.p_sel e_v514) (L2.p_sel e_v515) (L2.p_mul_comm e_v516) (L2.p_mul_comm e_v517) (L2.p_le e_v518 e_v519) (L2.p_le e_v520 e_v521) e_v522 e_v523 e_v196 (L2.p_le e_v524 e_v525) (L2.p_clt (-1) e_v19 e_v526) e_v527 (L2.p_and_comm e_v528) e_v529 e_v203 (L2.p_le e_v530 e_v531) (L2.p_or_comm e_v532) e_v533 (L2.p_not_not e_v501) e_v534 e_v535 e_v536 (L2.p_sel e_v537) e_v212 (L2.p_sel e_v538)
  let u539 : ℤ := (sv v61) - u456
  let u540 : ℤ := if u496 = 1 then u539 else u456
  let u541 : ℤ := 0
  let u542 : ℤ := L2.cosI u541
  let u543 : ℤ := (sv v28) + u542
  let u544 : ℕ := if u543 < (sv v95) then 1 else 0
  let u545 : ℤ := if u544 = 1 then (sv v95) else u543
  have f1086 := L2.K3_cos_lo u541 u542 u543 (sv v95) u545 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u546 : ℤ := (sv v31) + u542
  let u547 : ℕ := if u546 < (sv v33) then 1 else 0
  let u548 : ℤ := if u547 = 1 then u546 else (sv v33)
  have f1095 := L2.K3_cos_hi u541 u542 u546 (sv v33) u548 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u549 : ℤ := L2.sinI u541
  let u550 : ℤ := (sv v31) + u549
  let u551 : ℕ := if u550 < (sv v33) then 1 else 0
  let u552 : ℤ := if u551 = 1 then u550 else (sv v33)
  have f1104 := L2.K3_sin_hi u541 u549 u550 (sv v33) u552 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u553 : ℤ := (sv v28) + u549
  have f1113 := L2.K3_sin_lo u541 u549 u553 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u554 : ℤ := if u496 = 1 then u545 else u548
  let u555 : ℤ := if u496 = 1 then u552 else u553
  let u556 : ℤ := u497 * u555
  let u557 : ℤ := u540 * u554
  let u558 : ℕ := if u557 < u556 then 1 else 0
  let u559 : ℕ := if u558 = 1 then 0 else 1
  let u560 : ℕ := if u556 < u557 then 1 else 0
  let u561 : ℕ := if u560 = 1 then 0 else 1
  let u562 : ℕ := if (sv v61) < u541 then 1 else 0
  let u563 : ℕ := if u562 = 1 then 0 else 1
  let u564 : ℕ := if (sv v196) < u541 then 1 else 0
  let u565 : ℕ := if u564 = 1 then 0 else 1
  let u566 : ℕ := if (sv v19) < u545 then 1 else 0
  let u567 : ℕ := if u559 = 1 ∧ u566 = 1 then 1 else 0
  let u568 : ℕ := if u565 = 1 ∧ u567 = 1 then 1 else 0
  let u569 : ℕ := if u563 = 1 ∨ u568 = 1 then 1 else 0
  let u570 : ℕ := if u541 < (sv v203) then 1 else 0
  let u571 : ℕ := if u570 = 1 then 0 else 1
  let u572 : ℕ := if u561 = 1 ∨ u571 = 1 then 1 else 0
  let u573 : ℕ := if u496 = 1 ∧ u569 = 1 then 1 else 0
  let u574 : ℕ := if u496 = 1 then 0 else 1
  let u575 : ℕ := if u572 = 1 ∧ u574 = 1 then 1 else 0
  let u576 : ℕ := if u573 = 1 ∨ u575 = 1 then 1 else 0
  let u577 : ℤ := (sv v61) - u541
  let u578 : ℤ := if u496 = 1 then u577 else u541
  let u579 : ℤ := if u576 = 1 then u578 else (sv v203)
  have f1080 := L2.K12_atan_hi u456 u497 (sv v61) u496 u539 u540 u541 u545 u548 u552 u553 u554 u555 u556 u557 u559 u561 u562 u563 (sv v196) u565 u566 u567 u568 u569 (sv v203) u571 u572 u573 u574 u575 u576 u577 u578 (sv v203) u579 e_v61 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f1086 f1095 f1104 f1113 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v196 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v19 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v203 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v203 rfl
  let u581 : ℤ := if v493 = 1 then (sv v203) else u579
  have f882 := L2.K19_iso_angle_pt True (sv v5) (sv v100) (sv v107) (sv v442) (sv v399) (sv v450) u456 (sv v460) (sv v467) (sv v489) (sv v491) (sv v495) u497 v493 v492 (sv v538) u579 (sv v212) (sv v203) (sv v580) u581 f883 f886 f925 f962 f995 (L2.p_not_not e_v493) f1006 f1080 e_v212 e_v203 (L2.p_sel e_v580) rfl
  have f1158 := L2.K5_ihalf (sv v4) (sv v4) (sv v398) (sv v582) e_v398 e_v582
  have f1162 := L2.K8_in_range True (sv v398) (sv v582) v400 (sv v9) v584 v585 (L2.p_clt (-1) e_v19 e_v400) e_v9 (L2.p_le e_v583 e_v584) e_v585 (L2.X1_top _ k_v585)
  let u586 : ℤ := L2.cosI (sv v582)
  let u587 : ℤ := (sv v28) + u586
  let u588 : ℕ := if u587 < (sv v95) then 1 else 0
  let u589 : ℤ := if u588 = 1 then (sv v95) else u587
  have f1172 := L2.K3_cos_lo (sv v582) u586 u587 (sv v95) u589 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u590 : ℕ := if (sv v98) < (sv v582) then 1 else 0
  let u591 : ℤ := if u590 = 1 then (sv v95) else u589
  let u592 : ℤ := L2.cosI (sv v398)
  let u593 : ℤ := (sv v31) + u592
  let u594 : ℕ := if u593 < (sv v33) then 1 else 0
  let u595 : ℤ := if u594 = 1 then u593 else (sv v33)
  have f1186 := L2.K3_cos_hi (sv v398) u592 u593 (sv v33) u595 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u596 : ℕ := if (sv v398) < (sv v105) then 1 else 0
  let u597 : ℤ := if u596 = 1 then (sv v33) else u595
  have f1161 := L2.K10_icos True (sv v398) (sv v582) u589 (sv v95) u590 u591 u595 (sv v33) u596 u597 f1162 f1172 e_v95 (L2.p_clt (843314855) e_v98 (L2.p_ult _ _)) rfl f1186 e_v33 (L2.p_ltc (1) e_v105 (L2.p_ult _ _)) rfl
  have f1201 := L2.K8_in_range True (sv v398) (sv v582) v400 (sv v9) v584 v585 (L2.p_clt (-1) e_v19 e_v400) e_v9 (L2.p_le e_v583 e_v584) e_v585 (L2.X1_top _ k_v585)
  have f1200 := L2.K9_isin True (sv v398) (sv v582) (sv t398.1) (sv t582.1) (sv v600) (sv v601) (sv v602) (sv v603) (sv v33) (sv v605) v413 v606 v607 (sv v608) f1201 (L2.p_sin e_t398_1) (L2.p_sin e_t582_1) (L2.p_min e_v599 (L2.p_sel e_v600)) (L2.p_addc (-4) (L2.p_add_comm e_v601) e_v28) (L2.p_max e_v599 (L2.p_sel e_v602)) (L2.p_addc (4) (L2.p_add_comm e_v603) e_v31) e_v33 (L2.p_min e_v604 (L2.p_sel e_v605)) (L2.p_ltc (421657430) e_v36 e_v413) (L2.p_clt (421657427) e_v38 e_v606) e_v607 (L2.p_sel e_v608)
  let u610 : ℕ := if v609 = 1 then 0 else 1
  let u612 : ℕ := if v611 = 1 then 0 else 1
  let u613 : ℕ := if v609 = 1 ∧ u612 = 1 then 1 else 0
  let u617 : ℕ := if v135 = 1 ∧ v614 = 1 then 1 else 0
  let u618 : ℕ := if u613 = 1 ∨ u617 = 1 then 1 else 0
  let u619 : ℤ := if u618 = 1 then (sv v107) else (sv v100)
  let u620 : ℕ := if v139 = 1 ∧ u610 = 1 then 1 else 0
  let u621 : ℕ := if v138 = 1 ∨ u620 = 1 then 1 else 0
  let u622 : ℤ := if u621 = 1 then (sv v608) else (sv v601)
  let u623 : ℕ := if v138 = 1 ∧ v614 = 1 then 1 else 0
  let u624 : ℕ := if u613 = 1 ∨ u623 = 1 then 1 else 0
  let u625 : ℤ := if u624 = 1 then (sv v100) else (sv v107)
  let u626 : ℕ := if v139 = 1 ∧ u613 = 1 then 1 else 0
  let u627 : ℕ := if v138 = 1 ∨ u626 = 1 then 1 else 0
  let u628 : ℤ := if u627 = 1 then (sv v601) else (sv v608)
  let u629 : ℤ := u619 * u622
  let u630 : ℤ := u629 / 2 ^ 28
  let u631 : ℤ := u625 * u628
  let u632 : ℤ := -((-u631) / 2 ^ 28)
  have f1237 := L2.K6_imul True (sv v100) (sv v107) (sv v601) (sv v608) (sv v61) v134 v135 v136 v137 v138 v139 v609 u610 v611 u612 u613 v614 v615 v616 u617 u618 u619 u620 u621 u622 u623 u624 u625 u626 u627 u628 u630 u632 e_v61 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 e_v609 (L2.p_unot _) e_v611 (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) e_v614 e_v615 e_v616 (L2.X1_top _ k_v616) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl)
  let u633 : ℕ := if (sv v61) < u630 then 1 else 0
  let u634 : ℕ := if u633 = 1 then 0 else 1
  let u635 : ℕ := if u591 < (sv v61) then 1 else 0
  let u636 : ℤ := if u635 = 1 then u630 else u632
  let u637 : ℕ := if u597 < (sv v61) then 1 else 0
  let u638 : ℤ := if u637 = 1 then u632 else u630
  have f1270 := L2.K11_qdiv u591 u597 u630 u632 u633 u634 (sv v61) u635 u636 u637 u638 (L2.p_clt (0) e_v61 (L2.p_ult _ _)) (L2.p_unot _) e_v61 (L2.p_ult _ _) rfl (L2.p_ult _ _) rfl
  let u639 : ℤ := (sv v61) - u591
  let u640 : ℤ := if u635 = 1 then u639 else u591
  let u641 : ℤ := 0
  let u642 : ℕ := if u635 = 1 then 0 else 1
  let u643 : ℤ := L2.cosI u641
  let u644 : ℤ := (sv v28) + u643
  let u645 : ℕ := if u644 < (sv v95) then 1 else 0
  let u646 : ℤ := if u645 = 1 then (sv v95) else u644
  have f1288 := L2.K3_cos_lo u641 u643 u644 (sv v95) u646 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u647 : ℤ := (sv v31) + u643
  let u648 : ℕ := if u647 < (sv v33) then 1 else 0
  let u649 : ℤ := if u648 = 1 then u647 else (sv v33)
  have f1297 := L2.K3_cos_hi u641 u643 u647 (sv v33) u649 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u650 : ℤ := L2.sinI u641
  let u651 : ℤ := (sv v31) + u650
  let u652 : ℕ := if u651 < (sv v33) then 1 else 0
  let u653 : ℤ := if u652 = 1 then u651 else (sv v33)
  have f1306 := L2.K3_sin_hi u641 u650 u651 (sv v33) u653 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u654 : ℤ := (sv v28) + u650
  have f1315 := L2.K3_sin_lo u641 u650 u654 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u655 : ℤ := if u642 = 1 then u646 else u649
  let u656 : ℤ := if u642 = 1 then u653 else u654
  let u657 : ℤ := u636 * u656
  let u658 : ℤ := u640 * u655
  let u659 : ℕ := if u658 < u657 then 1 else 0
  let u660 : ℕ := if u659 = 1 then 0 else 1
  let u661 : ℕ := if u657 < u658 then 1 else 0
  let u662 : ℕ := if u661 = 1 then 0 else 1
  let u663 : ℕ := if (sv v61) < u641 then 1 else 0
  let u664 : ℕ := if u663 = 1 then 0 else 1
  let u665 : ℕ := if (sv v196) < u641 then 1 else 0
  let u666 : ℕ := if u665 = 1 then 0 else 1
  let u667 : ℕ := if (sv v19) < u646 then 1 else 0
  let u668 : ℕ := if u660 = 1 ∧ u667 = 1 then 1 else 0
  let u669 : ℕ := if u666 = 1 ∧ u668 = 1 then 1 else 0
  let u670 : ℕ := if u664 = 1 ∨ u669 = 1 then 1 else 0
  let u671 : ℕ := if u641 < (sv v203) then 1 else 0
  let u672 : ℕ := if u671 = 1 then 0 else 1
  let u673 : ℕ := if u662 = 1 ∨ u672 = 1 then 1 else 0
  let u674 : ℕ := if u642 = 1 ∧ u670 = 1 then 1 else 0
  let u675 : ℕ := if u635 = 1 ∧ u673 = 1 then 1 else 0
  let u676 : ℕ := if u674 = 1 ∨ u675 = 1 then 1 else 0
  let u677 : ℤ := (sv v61) - u641
  let u678 : ℤ := if u635 = 1 then u677 else u641
  let u679 : ℤ := if u676 = 1 then u678 else (sv v212)
  have f1281 := L2.K12_atan_lo u591 u636 (sv v61) u635 u639 u640 u641 u642 u646 u649 u653 u654 u655 u656 u657 u658 u660 u662 u663 u664 (sv v196) u666 u667 u668 u669 u670 (sv v203) u672 u673 u674 u635 u675 u676 u677 u678 (sv v212) u679 e_v61 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f1288 f1297 f1306 f1315 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v196 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v19 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v203 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl e_v212 rfl
  let u680 : ℤ := (sv v61) - u597
  let u681 : ℤ := if u637 = 1 then u680 else u597
  let u682 : ℤ := 0
  let u683 : ℤ := L2.cosI u682
  let u684 : ℤ := (sv v28) + u683
  let u685 : ℕ := if u684 < (sv v95) then 1 else 0
  let u686 : ℤ := if u685 = 1 then (sv v95) else u684
  have f1361 := L2.K3_cos_lo u682 u683 u684 (sv v95) u686 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u687 : ℤ := (sv v31) + u683
  let u688 : ℕ := if u687 < (sv v33) then 1 else 0
  let u689 : ℤ := if u688 = 1 then u687 else (sv v33)
  have f1370 := L2.K3_cos_hi u682 u683 u687 (sv v33) u689 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u690 : ℤ := L2.sinI u682
  let u691 : ℤ := (sv v31) + u690
  let u692 : ℕ := if u691 < (sv v33) then 1 else 0
  let u693 : ℤ := if u692 = 1 then u691 else (sv v33)
  have f1379 := L2.K3_sin_hi u682 u690 u691 (sv v33) u693 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u694 : ℤ := (sv v28) + u690
  have f1388 := L2.K3_sin_lo u682 u690 u694 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u695 : ℤ := if u637 = 1 then u686 else u689
  let u696 : ℤ := if u637 = 1 then u693 else u694
  let u697 : ℤ := u638 * u696
  let u698 : ℤ := u681 * u695
  let u699 : ℕ := if u698 < u697 then 1 else 0
  let u700 : ℕ := if u699 = 1 then 0 else 1
  let u701 : ℕ := if u697 < u698 then 1 else 0
  let u702 : ℕ := if u701 = 1 then 0 else 1
  let u703 : ℕ := if (sv v61) < u682 then 1 else 0
  let u704 : ℕ := if u703 = 1 then 0 else 1
  let u705 : ℕ := if (sv v196) < u682 then 1 else 0
  let u706 : ℕ := if u705 = 1 then 0 else 1
  let u707 : ℕ := if (sv v19) < u686 then 1 else 0
  let u708 : ℕ := if u700 = 1 ∧ u707 = 1 then 1 else 0
  let u709 : ℕ := if u706 = 1 ∧ u708 = 1 then 1 else 0
  let u710 : ℕ := if u704 = 1 ∨ u709 = 1 then 1 else 0
  let u711 : ℕ := if u682 < (sv v203) then 1 else 0
  let u712 : ℕ := if u711 = 1 then 0 else 1
  let u713 : ℕ := if u702 = 1 ∨ u712 = 1 then 1 else 0
  let u714 : ℕ := if u637 = 1 ∧ u710 = 1 then 1 else 0
  let u715 : ℕ := if u637 = 1 then 0 else 1
  let u716 : ℕ := if u713 = 1 ∧ u715 = 1 then 1 else 0
  let u717 : ℕ := if u714 = 1 ∨ u716 = 1 then 1 else 0
  let u718 : ℤ := (sv v61) - u682
  let u719 : ℤ := if u637 = 1 then u718 else u682
  let u720 : ℤ := if u717 = 1 then u719 else (sv v203)
  have f1355 := L2.K12_atan_hi u597 u638 (sv v61) u637 u680 u681 u682 u686 u689 u693 u694 u695 u696 u697 u698 u700 u702 u703 u704 (sv v196) u706 u707 u708 u709 u710 (sv v203) u712 u713 u714 u715 u716 u717 u718 u719 (sv v203) u720 e_v61 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f1361 f1370 f1379 f1388 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v196 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v19 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v203 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v203 rfl
  let u721 : ℤ := if u634 = 1 then (sv v212) else u679
  let u722 : ℤ := if u634 = 1 then (sv v203) else u720
  have f1157 := L2.K19_iso_angle_pt True (sv v4) (sv v100) (sv v107) (sv v398) (sv v582) u591 u597 (sv v601) (sv v608) u630 u632 u636 u638 u634 u633 u679 u720 (sv v212) (sv v203) u721 u722 f1158 f1161 f1200 f1237 f1270 (L2.p_not_not (L2.p_unot _)) f1281 f1355 e_v212 e_v203 rfl rfl
  have f842 := L2.K20_iso_angle True (sv v4) (sv v5) (sv v0) (sv v1) (sv v100) (sv v107) (sv v580) u581 v493 u721 u722 u634 f843 f882 f1157
  have f1434 := L2.K8_in_range True (sv v0) (sv v1) v20 (sv v9) v22 v23 (L2.p_clt (-1) e_v19 e_v20) e_v9 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f1433 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v27) (sv v29) (sv v30) (sv v32) (sv v33) (sv v35) v37 v39 v40 (sv v41) f1434 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v26 (L2.p_sel e_v27)) (L2.p_addc (-4) e_v29 e_v28) (L2.p_max e_v26 (L2.p_sel e_v30)) (L2.p_addc (4) e_v32 e_v31) e_v33 (L2.p_min e_v34 (L2.p_sel e_v35)) (L2.p_ltc (421657430) e_v36 e_v37) (L2.p_clt (421657427) e_v38 e_v39) e_v40 (L2.p_sel e_v41)
  have f1470 := L2.K5_ihalf (sv v7) u14 (sv v723) (sv v725) e_v723 (L2.X2_push (fun z : ℤ => (z + 1) / 2) v13 u14 (sv v7) (sv v9) (sv v724) (sv v203) (sv v725) rfl e_v724 (L2.p_halfc_cc (421657429) (843314857) e_v203 e_v9 (by norm_num)) (L2.p_sel e_v725))
  have f1478 := L2.K8_in_range True (sv v723) (sv v725) v726 (sv v9) v728 v729 (L2.p_clt (-1) e_v19 e_v726) e_v9 (L2.p_le e_v727 e_v728) e_v729 (L2.X1_top _ k_v729)
  have f1477 := L2.K9_isin True (sv v723) (sv v725) (sv t723.1) (sv t725.1) (sv v733) (sv v734) (sv v735) (sv v736) (sv v33) (sv v738) v739 v740 v741 (sv v742) f1478 (L2.p_sin e_t723_1) (L2.p_sin e_t725_1) (L2.p_min e_v732 (L2.p_sel e_v733)) (L2.p_addc (-4) (L2.p_add_comm e_v734) e_v28) (L2.p_max e_v732 (L2.p_sel e_v735)) (L2.p_addc (4) (L2.p_add_comm e_v736) e_v31) e_v33 (L2.p_min e_v737 (L2.p_sel e_v738)) (L2.p_ltc (421657430) e_v36 e_v739) (L2.p_clt (421657427) e_v38 e_v740) e_v741 (L2.p_sel e_v742)
  have f1514 := L2.K6_imul True (sv v29) (sv v41) (sv v734) (sv v742) (sv v61) v62 v63 v64 v65 v66 v67 v743 v744 v745 v746 v747 v748 v749 v750 v751 v752 (sv v753) v754 v755 (sv v756) v757 v758 (sv v759) v760 v761 (sv v762) (sv v764) (sv v766) e_v61 e_v62 e_v63 e_v64 e_v65 (L2.p_and_comm e_v66) e_v67 e_v743 e_v744 e_v745 e_v746 (L2.p_and_comm e_v747) e_v748 e_v749 e_v750 (L2.X1_top _ k_v750) e_v751 e_v752 (L2.p_sel e_v753) e_v754 e_v755 (L2.p_sel e_v756) e_v757 e_v758 (L2.p_sel e_v759) e_v760 e_v761 (L2.p_sel e_v762) (L2.p_mul (L2.p_mul_comm e_v763) e_v764) (L2.p_mulc (L2.p_mul_comm e_v765) e_v766)
  have f1432 := L2.K14_iso_base_a True (sv v7) u14 (sv v0) (sv v1) (sv v29) (sv v41) (sv v723) (sv v725) (sv v734) (sv v742) (sv v764) (sv v766) v767 f1433 f1470 f1477 f1514 (L2.p_clt (-1) e_v19 e_v767) (L2.X1_top _ k_v767)
  have f1553 := L2.K15_a_open (sv v764) (sv v766) v768 v769 v770 (L2.p_clt (0) e_v61 e_v768) (L2.p_ltc (268435456) e_v33 e_v769) e_v770
  have f1561 := L2.K15_a_open (sv v89) (sv v91) v771 v772 v773 (L2.p_clt (0) e_v61 e_v771) (L2.p_ltc (268435456) e_v33 e_v772) e_v773
  have f1569 := L2.K15_a_open (sv v438) (sv v440) v774 v775 v776 (L2.p_clt (0) e_v61 e_v774) (L2.p_ltc (268435456) e_v33 e_v775) e_v776
  have f1579 := L2.K16_a_cos (True ∧ v778 = 1) (sv v764) (sv v766) (sv v33) (sv v780) (sv v781) (sv v782) (sv v95) (sv v784) (sv v786) (sv v787) (sv v788) e_v33 (L2.p_mulc e_v779 e_v780) e_v781 e_v782 e_v95 (L2.p_max e_v783 (L2.p_sel e_v784)) (L2.p_mul e_v785 e_v786) e_v787 e_v788
  have f1593 := L2.K16_a_cos (True ∧ v778 = 1) (sv v438) (sv v440) (sv v33) (sv v790) (sv v791) (sv v792) (sv v95) (sv v794) (sv v796) (sv v797) (sv v798) e_v33 (L2.p_mulc e_v789 e_v790) e_v791 e_v792 e_v95 (L2.p_max e_v793 (L2.p_sel e_v794)) (L2.p_mul e_v795 e_v796) e_v797 e_v798
  have f1607 := L2.K16_a_cos (True ∧ v778 = 1) (sv v89) (sv v91) (sv v33) (sv v800) (sv v801) (sv v802) (sv v95) (sv v804) (sv v806) (sv v807) (sv v808) e_v33 (L2.p_mulc e_v799 e_v800) e_v801 e_v802 e_v95 (L2.p_max e_v803 (L2.p_sel e_v804)) (L2.p_mul e_v805 e_v806) e_v807 e_v808
  have f1621 := L2.K6_imul (True ∧ v778 = 1) (sv v784) (sv v788) (sv v804) (sv v808) (sv v61) v809 v810 v811 v812 v813 v814 v815 v816 v817 v818 v819 v820 v821 v822 v825 v826 (sv v827) v828 v829 (sv v830) v831 v832 (sv v833) v834 v835 (sv v836) (sv v838) (sv v840) e_v61 e_v809 e_v810 e_v811 e_v812 (L2.p_and_comm e_v813) e_v814 e_v815 e_v816 e_v817 e_v818 (L2.p_and_comm e_v819) e_v820 e_v821 e_v822 (L2.X1_step True v778 v823 v822 v824 e_v823 (L2.p_or_comm e_v824) (L2.X1_top _ k_v824)) e_v825 e_v826 (L2.p_sel e_v827) e_v828 e_v829 (L2.p_sel e_v830) e_v831 e_v832 (L2.p_sel e_v833) e_v834 e_v835 (L2.p_sel e_v836) (L2.p_mul (L2.p_mul_comm e_v837) e_v838) (L2.p_mulc (L2.p_mul_comm e_v839) e_v840)
  have f1656 := L2.K4_isub (sv v794) (sv v798) (sv v838) (sv v840) (sv v841) (sv v842) e_v841 e_v842
  have f1659 := L2.K6_imul (True ∧ v778 = 1) (sv v784) (sv v788) (sv v794) (sv v798) (sv v61) v809 v810 v811 v812 v813 v814 v843 v844 v845 v846 v847 v848 v849 v850 v852 v853 (sv v854) v855 v856 (sv v857) v858 v859 (sv v860) v861 v862 (sv v863) (sv v865) (sv v867) e_v61 e_v809 e_v810 e_v811 e_v812 (L2.p_and_comm e_v813) e_v814 e_v843 e_v844 e_v845 e_v846 (L2.p_and_comm e_v847) e_v848 e_v849 e_v850 (L2.X1_step True v778 v823 v850 v851 e_v823 e_v851 (L2.X1_top _ k_v851)) e_v852 e_v853 (L2.p_sel e_v854) e_v855 e_v856 (L2.p_sel e_v857) e_v858 e_v859 (L2.p_sel e_v860) e_v861 e_v862 (L2.p_sel e_v863) (L2.p_mul (L2.p_mul_comm e_v864) e_v865) (L2.p_mulc (L2.p_mul_comm e_v866) e_v867)
  have f1694 := L2.K4_isub (sv v804) (sv v808) (sv v865) (sv v867) (sv v868) (sv v869) e_v868 e_v869
  let u882 : ℤ := -((-(sv v785)) / 2 ^ 28)
  let u883 : ℤ := u882 + u882
  let u884 : ℤ := (sv v33) - u883
  let u885 : ℕ := if u884 < (sv v95) then 1 else 0
  let u886 : ℤ := if u885 = 1 then (sv v95) else u884
  have f1721 := L2.K16_a_cos (True ∧ v778 = 1) (sv v764) (sv v764) (sv v33) u882 u883 u884 (sv v95) u886 (sv v786) (sv v787) (sv v788) e_v33 (L2.p_mulc e_v785 rfl) rfl rfl e_v95 (L2.p_max (L2.p_ult _ _) rfl) (L2.p_mul e_v785 e_v786) e_v787 e_v788
  have f1735 := L2.K16_a_cos (True ∧ v778 = 1) (sv v874) (sv v875) (sv v33) (sv v888) (sv v889) (sv v890) (sv v95) (sv v892) (sv v894) (sv v895) (sv v896) e_v33 (L2.p_mulc e_v887 e_v888) e_v889 e_v890 e_v95 (L2.p_max e_v891 (L2.p_sel e_v892)) (L2.p_mul e_v893 e_v894) e_v895 e_v896
  have f1749 := L2.K16_a_cos (True ∧ v778 = 1) (sv v878) (sv v879) (sv v33) (sv v898) (sv v899) (sv v900) (sv v95) (sv v902) (sv v904) (sv v905) (sv v906) e_v33 (L2.p_mulc e_v897 e_v898) e_v899 e_v900 e_v95 (L2.p_max e_v901 (L2.p_sel e_v902)) (L2.p_mul e_v903 e_v904) e_v905 e_v906
  let u928 : ℕ := if v911 = 1 ∧ v918 = 1 then 1 else 0
  let u929 : ℕ := if v917 = 1 ∨ u928 = 1 then 1 else 0
  let u930 : ℤ := if u929 = 1 then (sv v892) else (sv v896)
  let u931 : ℕ := if v912 = 1 ∧ v917 = 1 then 1 else 0
  let u932 : ℕ := if v911 = 1 ∨ u931 = 1 then 1 else 0
  let u933 : ℤ := if u932 = 1 then (sv v902) else (sv v906)
  let u936 : ℤ := u930 * u933
  let u937 : ℤ := -((-u936) / 2 ^ 28)
  have f1763 := L2.K6_imul (True ∧ v778 = 1) (sv v892) (sv v896) (sv v902) (sv v906) (sv v61) v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 v918 v919 v920 v922 v923 (sv v924) v925 v926 (sv v927) u928 u929 u930 u931 u932 u933 (sv v935) u937 e_v61 e_v907 e_v908 e_v909 e_v910 (L2.p_and_comm e_v911) e_v912 e_v913 e_v914 e_v915 e_v916 (L2.p_and_comm e_v917) e_v918 e_v919 e_v920 (L2.X1_step True v778 v823 v920 v921 e_v823 e_v921 (L2.X1_top _ k_v921)) e_v922 e_v923 (L2.p_sel e_v924) e_v925 e_v926 (L2.p_sel e_v927) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul (L2.p_mul_comm e_v934) e_v935) (L2.p_mulc rfl rfl)
  let u938 : ℤ := u886 - u937
  have f1798 := L2.K4_isub u886 (sv v788) (sv v935) u937 u938 (sv v939) rfl e_v939
  have f1802 := L2.K17_s_end (sv v874) (sv v893) (sv v940) (sv v941) (sv v942) (sv v943) (sv v945) (sv v946) (sv v33) (sv v948) (sv v949) (sv v951) e_v893 e_v940 e_v941 (L2.p_sqrt e_v942) (L2.p_addc (1) (L2.p_add_comm e_v943) e_v105) (L2.p_mul (L2.p_mul_comm e_v944) e_v945) e_v946 e_v33 (L2.p_mulc (L2.p_mul_comm e_v947) e_v948) e_v949 (L2.p_min e_v950 (L2.p_sel e_v951))
  have f1820 := L2.K17_s_end (sv v875) (sv v887) (sv v940) (sv v952) (sv v953) (sv v954) (sv v956) (sv v957) (sv v33) (sv v959) (sv v960) (sv v962) e_v887 e_v940 e_v952 (L2.p_sqrt e_v953) (L2.p_addc (1) (L2.p_add_comm e_v954) e_v105) (L2.p_mul (L2.p_mul_comm e_v955) e_v956) e_v957 e_v33 (L2.p_mulc (L2.p_mul_comm e_v958) e_v959) e_v960 (L2.p_min e_v961 (L2.p_sel e_v962))
  have f1801 := L2.K18_a_sin (True ∧ v778 = 1) (sv v874) (sv v875) (sv v946) (sv v951) (sv v957) (sv v962) (sv v964) (sv v966) (sv v967) (sv v893) (sv v887) v969 v971 v972 (sv v33) (sv v973) f1802 f1820 (L2.p_min e_v963 (L2.p_sel e_v964)) (L2.p_max e_v965 (L2.p_sel e_v966)) e_v967 e_v893 e_v887 (L2.p_le e_v968 e_v969) (L2.p_le e_v970 e_v971) e_v972 e_v33 (L2.p_sel e_v973)
  have f1857 := L2.K17_s_end (sv v878) (sv v903) (sv v940) (sv v974) (sv v975) (sv v976) (sv v978) (sv v979) (sv v33) (sv v981) (sv v982) (sv v984) e_v903 e_v940 e_v974 (L2.p_sqrt e_v975) (L2.p_addc (1) (L2.p_add_comm e_v976) e_v105) (L2.p_mul (L2.p_mul_comm e_v977) e_v978) e_v979 e_v33 (L2.p_mulc (L2.p_mul_comm e_v980) e_v981) e_v982 (L2.p_min e_v983 (L2.p_sel e_v984))
  have f1875 := L2.K17_s_end (sv v879) (sv v897) (sv v940) (sv v985) (sv v986) (sv v987) (sv v989) (sv v990) (sv v33) (sv v992) (sv v993) (sv v995) e_v897 e_v940 e_v985 (L2.p_sqrt e_v986) (L2.p_addc (1) (L2.p_add_comm e_v987) e_v105) (L2.p_mul (L2.p_mul_comm e_v988) e_v989) e_v990 e_v33 (L2.p_mulc (L2.p_mul_comm e_v991) e_v992) e_v993 (L2.p_min e_v994 (L2.p_sel e_v995))
  have f1856 := L2.K18_a_sin (True ∧ v778 = 1) (sv v878) (sv v879) (sv v979) (sv v984) (sv v990) (sv v995) (sv v997) (sv v999) (sv v967) (sv v903) (sv v897) v1001 v1003 v1004 (sv v33) (sv v1005) f1857 f1875 (L2.p_min e_v996 (L2.p_sel e_v997)) (L2.p_max e_v998 (L2.p_sel e_v999)) e_v967 e_v903 e_v897 (L2.p_le e_v1000 e_v1001) (L2.p_le e_v1002 e_v1003) e_v1004 e_v33 (L2.p_sel e_v1005)
  have f1911 := L2.K6_imul (True ∧ v778 = 1) (sv v964) (sv v973) (sv v997) (sv v1005) (sv v61) v1006 v1007 v1008 v1009 v1010 v1011 v1012 v1013 v1014 v1015 v1016 v1017 v1018 v1019 v1021 v1022 (sv v1023) v1024 v1025 (sv v1026) v1027 v1028 (sv v1029) v1030 v1031 (sv v1032) (sv v1034) (sv v1036) e_v61 e_v1006 e_v1007 e_v1008 e_v1009 (L2.p_and_comm e_v1010) e_v1011 e_v1012 e_v1013 e_v1014 e_v1015 (L2.p_and_comm e_v1016) e_v1017 e_v1018 e_v1019 (L2.X1_step True v778 v823 v1019 v1020 e_v823 e_v1020 (L2.X1_top _ k_v1020)) e_v1021 e_v1022 (L2.p_sel e_v1023) e_v1024 e_v1025 (L2.p_sel e_v1026) e_v1027 e_v1028 (L2.p_sel e_v1029) e_v1030 e_v1031 (L2.p_sel e_v1032) (L2.p_mul (L2.p_mul_comm e_v1033) e_v1034) (L2.p_mulc (L2.p_mul_comm e_v1035) e_v1036)
  let u1039 : ℕ := if u938 < (sv v61) then 1 else 0
  let u1040 : ℤ := if u1039 = 1 then (sv v1034) else (sv v1036)
  have f1946 := L2.K11_qdiv u938 (sv v939) (sv v1034) (sv v1036) v1037 v1038 (sv v61) u1039 u1040 v1041 (sv v1042) (L2.p_clt (0) e_v61 e_v1037) e_v1038 e_v61 (L2.p_ult _ _) rfl e_v1041 (L2.p_sel e_v1042)
  have f1720 := L2.K23_hn true true true (True ∧ v778 = 1) (sv v764) (sv v764) (sv v874) (sv v875) (sv v878) (sv v879) u886 (sv v788) (sv v892) (sv v896) (sv v902) (sv v906) (sv v935) u937 u938 (sv v939) (sv v964) (sv v973) (sv v997) (sv v1005) (sv v1034) (sv v1036) u1040 (sv v1042) v1038 f1721 f1735 f1749 f1763 f1798 f1801 f1856 f1911 f1946
  let u1051 : ℤ := (sv v779) / 2 ^ 28
  let u1052 : ℤ := u1051 + u1051
  let u1053 : ℤ := (sv v33) - u1052
  have f1969 := L2.K16_a_cos (True ∧ v778 = 1) (sv v766) (sv v766) (sv v33) (sv v780) (sv v781) (sv v782) (sv v95) (sv v784) u1051 u1052 u1053 e_v33 (L2.p_mulc e_v779 e_v780) e_v781 e_v782 e_v95 (L2.p_max e_v783 (L2.p_sel e_v784)) (L2.p_mul e_v779 rfl) rfl rfl
  have f1983 := L2.K16_a_cos (True ∧ v778 = 1) (sv v876) (sv v877) (sv v33) (sv v1055) (sv v1056) (sv v1057) (sv v95) (sv v1059) (sv v1061) (sv v1062) (sv v1063) e_v33 (L2.p_mulc e_v1054 e_v1055) e_v1056 e_v1057 e_v95 (L2.p_max e_v1058 (L2.p_sel e_v1059)) (L2.p_mul e_v1060 e_v1061) e_v1062 e_v1063
  have f1997 := L2.K16_a_cos (True ∧ v778 = 1) (sv v880) (sv v881) (sv v33) (sv v1065) (sv v1066) (sv v1067) (sv v95) (sv v1069) (sv v1071) (sv v1072) (sv v1073) e_v33 (L2.p_mulc e_v1064 e_v1065) e_v1066 e_v1067 e_v95 (L2.p_max e_v1068 (L2.p_sel e_v1069)) (L2.p_mul e_v1070 e_v1071) e_v1072 e_v1073
  let u1075 : ℕ := if v1074 = 1 then 0 else 1
  let u1081 : ℕ := if v1080 = 1 then 0 else 1
  let u1089 : ℕ := if u1075 = 1 ∧ v1085 = 1 then 1 else 0
  let u1090 : ℕ := if v1084 = 1 ∨ u1089 = 1 then 1 else 0
  let u1091 : ℤ := if u1090 = 1 then (sv v1063) else (sv v1059)
  let u1092 : ℕ := if v1079 = 1 ∧ u1081 = 1 then 1 else 0
  let u1093 : ℕ := if v1078 = 1 ∨ u1092 = 1 then 1 else 0
  let u1094 : ℤ := if u1093 = 1 then (sv v1073) else (sv v1069)
  let u1101 : ℤ := u1091 * u1094
  let u1102 : ℤ := u1101 / 2 ^ 28
  have f2011 := L2.K6_imul (True ∧ v778 = 1) (sv v1059) (sv v1063) (sv v1069) (sv v1073) (sv v61) v1074 u1075 v1076 v1077 v1078 v1079 v1080 u1081 v1082 v1083 v1084 v1085 v1086 v1087 u1089 u1090 u1091 u1092 u1093 u1094 v1095 v1096 (sv v1097) v1098 v1099 (sv v1100) u1102 (sv v1104) e_v61 e_v1074 (L2.p_unot _) e_v1076 e_v1077 (L2.p_and_comm e_v1078) e_v1079 e_v1080 (L2.p_unot _) e_v1082 e_v1083 (L2.p_and_comm e_v1084) e_v1085 e_v1086 e_v1087 (L2.X1_step True v778 v823 v1087 v1088 e_v823 e_v1088 (L2.X1_top _ k_v1088)) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl e_v1095 e_v1096 (L2.p_sel e_v1097) e_v1098 e_v1099 (L2.p_sel e_v1100) (L2.p_mul rfl rfl) (L2.p_mulc (L2.p_mul_comm e_v1103) e_v1104)
  let u1106 : ℤ := u1053 - u1102
  have f2046 := L2.K4_isub (sv v784) u1053 u1102 (sv v1104) (sv v1105) u1106 e_v1105 rfl
  have f2050 := L2.K17_s_end (sv v876) (sv v1060) (sv v940) (sv v1107) (sv v1108) (sv v1109) (sv v1111) (sv v1112) (sv v33) (sv v1114) (sv v1115) (sv v1117) e_v1060 e_v940 e_v1107 (L2.p_sqrt e_v1108) (L2.p_addc (1) (L2.p_add_comm e_v1109) e_v105) (L2.p_mul (L2.p_mul_comm e_v1110) e_v1111) e_v1112 e_v33 (L2.p_mulc (L2.p_mul_comm e_v1113) e_v1114) e_v1115 (L2.p_min e_v1116 (L2.p_sel e_v1117))
  have f2068 := L2.K17_s_end (sv v877) (sv v1054) (sv v940) (sv v1118) (sv v1119) (sv v1120) (sv v1122) (sv v1123) (sv v33) (sv v1125) (sv v1126) (sv v1128) e_v1054 e_v940 e_v1118 (L2.p_sqrt e_v1119) (L2.p_addc (1) (L2.p_add_comm e_v1120) e_v105) (L2.p_mul (L2.p_mul_comm e_v1121) e_v1122) e_v1123 e_v33 (L2.p_mulc (L2.p_mul_comm e_v1124) e_v1125) e_v1126 (L2.p_min e_v1127 (L2.p_sel e_v1128))
  have f2049 := L2.K18_a_sin (True ∧ v778 = 1) (sv v876) (sv v877) (sv v1112) (sv v1117) (sv v1123) (sv v1128) (sv v1130) (sv v1132) (sv v967) (sv v1060) (sv v1054) v1134 v1136 v1137 (sv v33) (sv v1138) f2050 f2068 (L2.p_min e_v1129 (L2.p_sel e_v1130)) (L2.p_max e_v1131 (L2.p_sel e_v1132)) e_v967 e_v1060 e_v1054 (L2.p_le e_v1133 e_v1134) (L2.p_le e_v1135 e_v1136) e_v1137 e_v33 (L2.p_sel e_v1138)
  have f2105 := L2.K17_s_end (sv v880) (sv v1070) (sv v940) (sv v1139) (sv v1140) (sv v1141) (sv v1143) (sv v1144) (sv v33) (sv v1146) (sv v1147) (sv v1149) e_v1070 e_v940 e_v1139 (L2.p_sqrt e_v1140) (L2.p_addc (1) (L2.p_add_comm e_v1141) e_v105) (L2.p_mul (L2.p_mul_comm e_v1142) e_v1143) e_v1144 e_v33 (L2.p_mulc (L2.p_mul_comm e_v1145) e_v1146) e_v1147 (L2.p_min e_v1148 (L2.p_sel e_v1149))
  have f2123 := L2.K17_s_end (sv v881) (sv v1064) (sv v940) (sv v1150) (sv v1151) (sv v1152) (sv v1154) (sv v1155) (sv v33) (sv v1157) (sv v1158) (sv v1160) e_v1064 e_v940 e_v1150 (L2.p_sqrt e_v1151) (L2.p_addc (1) (L2.p_add_comm e_v1152) e_v105) (L2.p_mul (L2.p_mul_comm e_v1153) e_v1154) e_v1155 e_v33 (L2.p_mulc (L2.p_mul_comm e_v1156) e_v1157) e_v1158 (L2.p_min e_v1159 (L2.p_sel e_v1160))
  have f2104 := L2.K18_a_sin (True ∧ v778 = 1) (sv v880) (sv v881) (sv v1144) (sv v1149) (sv v1155) (sv v1160) (sv v1162) (sv v1164) (sv v967) (sv v1070) (sv v1064) v1166 v1168 v1169 (sv v33) (sv v1170) f2105 f2123 (L2.p_min e_v1161 (L2.p_sel e_v1162)) (L2.p_max e_v1163 (L2.p_sel e_v1164)) e_v967 e_v1070 e_v1064 (L2.p_le e_v1165 e_v1166) (L2.p_le e_v1167 e_v1168) e_v1169 e_v33 (L2.p_sel e_v1170)
  have f2159 := L2.K6_imul (True ∧ v778 = 1) (sv v1130) (sv v1138) (sv v1162) (sv v1170) (sv v61) v1171 v1172 v1173 v1174 v1175 v1176 v1177 v1178 v1179 v1180 v1181 v1182 v1183 v1184 v1186 v1187 (sv v1188) v1189 v1190 (sv v1191) v1192 v1193 (sv v1194) v1195 v1196 (sv v1197) (sv v1199) (sv v1201) e_v61 e_v1171 e_v1172 e_v1173 e_v1174 (L2.p_and_comm e_v1175) e_v1176 e_v1177 e_v1178 e_v1179 e_v1180 (L2.p_and_comm e_v1181) e_v1182 e_v1183 e_v1184 (L2.X1_step True v778 v823 v1184 v1185 e_v823 e_v1185 (L2.X1_top _ k_v1185)) e_v1186 e_v1187 (L2.p_sel e_v1188) e_v1189 e_v1190 (L2.p_sel e_v1191) e_v1192 e_v1193 (L2.p_sel e_v1194) e_v1195 e_v1196 (L2.p_sel e_v1197) (L2.p_mul (L2.p_mul_comm e_v1198) e_v1199) (L2.p_mulc (L2.p_mul_comm e_v1200) e_v1201)
  let u1203 : ℕ := if v1202 = 1 then 0 else 1
  let u1206 : ℕ := if u1106 < (sv v61) then 1 else 0
  let u1207 : ℤ := if u1206 = 1 then (sv v1201) else (sv v1199)
  have f2194 := L2.K11_qdiv (sv v1105) u1106 (sv v1199) (sv v1201) v1202 u1203 (sv v61) v1204 (sv v1205) u1206 u1207 (L2.p_clt (0) e_v61 e_v1202) (L2.p_unot _) e_v61 e_v1204 (L2.p_sel e_v1205) (L2.p_ult _ _) rfl
  have f1968 := L2.K23_hn true true true (True ∧ v778 = 1) (sv v766) (sv v766) (sv v876) (sv v877) (sv v880) (sv v881) (sv v784) u1053 (sv v1059) (sv v1063) (sv v1069) (sv v1073) u1102 (sv v1104) (sv v1105) u1106 (sv v1130) (sv v1138) (sv v1162) (sv v1170) (sv v1199) (sv v1201) (sv v1205) u1207 u1203 f1969 f1983 f1997 f2011 f2046 f2049 f2104 f2159 f2194
  let u1210 : ℤ := (sv v61) - (sv v1205)
  let u1211 : ℕ := if u1210 < (sv v1105) then 1 else 0
  let u1212 : ℕ := if u1211 = 1 then 0 else 1
  let u1213 : ℕ := if u1203 = 1 ∨ u1212 = 1 then 1 else 0
  let u1214 : ℤ := if u1213 = 1 then (sv v95) else (sv v1105)
  let u1215 : ℤ := if u1213 = 1 then (sv v33) else (sv v1205)
  let u1217 : ℕ := if v1216 = 1 then 0 else 1
  have f2223 := L2.K3_cos_lo (sv v1218) (sv t1218.2) (sv v1222) (sv v95) (sv v1224) (L2.p_cos e_t1218_2) (L2.p_addc (-4) (L2.p_add_comm e_v1222) e_v28) e_v95 (L2.p_max e_v1223 (L2.p_sel e_v1224))
  have f2218 := L2.K13_acos_lo (sv v1049) (sv v1050) (sv v1218) (sv v61) v1219 v1220 (sv v1224) (sv v1225) (sv v1226) v1228 (sv v15) v1230 v1231 v1232 (sv v1233) (L2.p_hint e_v1218) e_v61 e_v1219 e_v1220 f2223 e_v1225 e_v1226 (L2.p_le e_v1227 e_v1228) e_v15 (L2.p_le e_v1229 e_v1230) e_v1231 e_v1232 (L2.p_sel e_v1233)
  let u1234 : ℤ := 0
  let u1235 : ℕ := if u1234 < (sv v9) then 1 else 0
  let u1236 : ℕ := if u1235 = 1 then 0 else 1
  let u1237 : ℤ := L2.cosI u1234
  let u1238 : ℤ := (sv v31) + u1237
  let u1239 : ℕ := if u1238 < (sv v33) then 1 else 0
  let u1240 : ℤ := if u1239 = 1 then u1238 else (sv v33)
  have f2250 := L2.K3_cos_hi u1234 u1237 u1238 (sv v33) u1240 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u1241 : ℤ := u1214 * 2 ^ 28
  let u1242 : ℤ := u1215 * u1240
  let u1243 : ℕ := if u1241 < u1242 then 1 else 0
  let u1244 : ℕ := if u1243 = 1 then 0 else 1
  let u1245 : ℕ := if u1236 = 1 ∨ u1244 = 1 then 1 else 0
  let u1246 : ℤ := if u1245 = 1 then u1234 else (sv v9)
  have f2244 := L2.K13_acos_hi u1214 u1215 u1234 (sv v9) u1236 u1240 u1241 u1242 u1244 u1245 u1246 (le_refl (0 : ℤ)) e_v9 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) f2250 rfl (L2.p_mul_comm rfl) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_uor _ _) rfl
  let u1248 : ℤ := if v778 = 1 then u1246 else (sv v9)
  let u1251 : ℤ := if v1045 = 1 then (sv v9) else (sv v61)
  have f1717 := L2.K24_tri_tail_x true true true True (sv v764) (sv v766) v778 (sv v874) (sv v875) (sv v878) (sv v879) (sv v876) (sv v877) (sv v880) (sv v881) (sv v33) (sv v95) u938 u1040 (sv v939) (sv v1042) v1038 v1037 (sv v1043) v1044 v1045 v1047 v1048 (sv v1049) (sv v1050) (sv v1105) (sv v1205) u1106 u1207 u1203 v1202 v1208 v1209 u1210 u1212 u1213 u1214 u1215 v1216 u1217 (sv v1233) u1246 (sv v61) (sv v9) (sv v15) (sv v1247) u1248 v1249 (sv v1250) u1251 e_v33 e_v95 f1720 (L2.p_not_not e_v1038) (L2.p_neg e_v61 e_v1043) e_v1044 e_v1045 (L2.p_le e_v1046 e_v1047) e_v1048 (L2.p_sel e_v1049) (L2.p_sel e_v1050) f1968 (L2.p_not_not (L2.p_unot _)) e_v1208 e_v1209 (L2.p_neg e_v61 rfl) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_uor _ _) rfl rfl e_v1216 (L2.p_unot _) f2218 f2244 e_v61 e_v9 e_v15 (L2.p_sel e_v1247) rfl e_v1249 (L2.p_sel e_v1250) rfl
  have f1552 := L2.K21_tri_angle_st true true true True (sv v764) (sv v766) (sv v89) (sv v91) (sv v438) (sv v440) v770 v773 v776 v777 v778 (sv v784) (sv v788) (sv v794) (sv v798) (sv v804) (sv v808) (sv v838) (sv v840) (sv v841) (sv v842) (sv v865) (sv v867) (sv v868) (sv v869) v870 v871 v872 v873 (sv v874) (sv v875) (sv v876) (sv v877) (sv v878) (sv v879) (sv v880) (sv v881) (sv v1247) u1248 v1249 (sv v1250) u1251 f1553 f1561 f1569 e_v777 (L2.p_and_comm e_v778) f1579 f1593 f1607 f1621 f1656 f1659 f1694 (L2.p_clt (0) e_v61 e_v870) (L2.p_ltc (0) e_v61 e_v871) (L2.p_clt (0) e_v61 e_v872) (L2.p_ltc (0) e_v61 e_v873) (L2.p_sel e_v874) (L2.p_sel e_v875) (L2.p_sel e_v876) (L2.p_sel e_v877) (L2.p_sel e_v878) (L2.p_sel e_v879) (L2.p_sel e_v880) (L2.p_sel e_v881) f1717
  let u1253 : ℤ := if v1249 = 1 then u1251 else u1248
  have f1551 := L2.K25_tri_angle_c true true true True (sv v764) (sv v766) (sv v89) (sv v91) (sv v438) (sv v440) (sv v1247) u1248 v1249 (sv v1250) u1251 (sv v1252) u1253 f1552 (L2.p_sel e_v1252) rfl
  let u1255 : ℤ := u397 + u1253
  have f2276 := L2.K4_iadd (sv v255) u397 (sv v1252) u1253 (sv v1254) u1255 e_v1254 rfl
  let u1257 : ℤ := u722 + u1255
  have f2279 := L2.K4_iadd (sv v1254) u1255 (sv v580) u722 (sv v1256) u1257 (L2.p_add_comm e_v1256) (L2.p_add_comm rfl)
  have f21 := Tammes15.D3Trig.KH_hex_eval True (sv v2) (sv v3) (sv v4) (sv v5) (sv v7) u14 (sv v0) (sv v1) (sv v89) (sv v91) (sv v255) u397 (sv v438) (sv v440) (sv v580) u722 (sv v764) (sv v766) (sv v1252) u1253 (sv v1254) u1255 (sv v1256) u1257 f22 f137 f727 f842 f1432 f1551 f2276 f2279
  let u1260 : ℕ := if (sv v6) < u1257 then 1 else 0
  let u1261 : ℕ := if u1260 = 1 then 0 else 1
  exact Tammes15.D3Trig.THNL F0 F1 F2 F3 hD (sv v0) (sv v1) (sv v2) (sv v3) (sv v4) (sv v5) (sv v6) (sv v7) (0 : ℕ) (sv v9) (sv v7) u14 (sv v1256) u1257 v1259 u1261 v1259 e_v0 e_v1 e_v2 e_v3 e_v4 e_v5 e_v6 e_v7 (of_decide_eq_true rfl) e_v9 f2 f21 (L2.p_le e_v1258 e_v1259) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_sel_f _ _) (L2.X1_top _ k_v1259)

end Tammes15.D3Trig
