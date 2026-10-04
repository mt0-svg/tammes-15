import Tammes15.D3Trig.Prog.HNH
import Tammes15.D3Prog.L2.Kinds
import Tammes15.D3Prog.L2.PLib
import Tammes15.D3Trig.HexKinds

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem progHNH_l2 (F0 F1 F2 F3 H0 H1 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (h : Tammes15.D3Trig.progHNH 1 F0 F1 F2 F3 H0 H1 = 1) (hD : InDomH F0 F1 F2 F3) : LaneClaimH true F0 F1 F2 F3 := by
  unfold Tammes15.D3Trig.progHNH at h
  extract_lets -merge OFFr H61r v0 v1 v2 v3 v4 v5 v6 v7 v9 v14 v15 v16 v18 v19 v20 v21 v22 v23 t0 t1 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 t42 t43 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v93 v94 v95 v96 v97 v98 v99 v101 v102 v103 v104 v105 v106 v107 v108 v109 t107 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v141 v144 v145 v146 v195 v202 v256 v257 v258 v259 v267 v268 v269 v270 v271 t256 v273 v274 v275 v276 v277 v278 v279 v280 v281 v282 v283 v284 v285 v286 v287 v288 v289 v290 v291 v292 v293 v294 v295 v296 v297 v298 v299 v300 v301 v302 v303 v304 v305 v306 v307 v308 v311 v312 v354 v355 v356 t356 v358 v359 v360 v361 v362 v363 v365 v366 v367 v368 v369 v370 v371 v372 v373 v374 v375 v376 v377 v378 v379 v380 v381 v382 v383 v384 v385 v386 v387 v388 v389 v390 v391 v392 v393 v394 v396 v397 v398 v399 v400 v401 v402 t397 t398 v405 v406 v407 v408 v409 v410 v411 v412 v413 v414 v415 v416 v417 v418 v419 v420 v421 v422 v423 v424 v425 v426 v427 v428 v429 v430 v431 v432 v433 v434 v435 v436 v437 v438 v439 v440 v441 v442 v443 t441 v457 v458 v459 v460 v461 v462 v463 v464 v465 v466 v467 v469 v472 v473 v474 v581 v582 v583 v584 v592 v593 v594 v595 v596 t581 v598 v599 v600 v601 v602 v603 v604 v605 v606 v607 v608 v609 v610 v611 v612 v613 v614 v615 v616 v617 v618 v619 v620 v621 v622 v623 v624 v625 v626 v627 v628 v629 v630 v631 v632 v633 v636 v637 v679 v680 v681 t681 v683 v684 v685 v686 v687 v688 v690 v691 v692 v693 v694 v695 v696 v697 v698 v699 v700 v701 v702 v703 v704 v705 v706 v707 v708 v709 v710 v711 v712 v713 v714 v715 v716 v717 v718 v719 v721 v722 v723 v724 v725 v726 v727 v728 t723 t724 v731 v732 v733 v734 v735 v736 v737 v738 v739 v740 v741 v742 v743 v744 v745 v746 v747 v748 v749 v750 v751 v752 v753 v754 v755 v756 v757 v758 v759 v760 v761 v762 v763 v764 v765 v766 v767 v768 v769 v770 v771 v772 v773 v774 v775 v776 v777 v778 v779 v780 v781 v782 v783 v784 v785 v786 v787 v788 v789 v790 v791 v792 v793 v794 v795 v796 v797 v798 v799 v800 v801 v802 v803 v804 v805 v806 v807 v808 v809 v810 v811 v812 v813 v814 v815 v816 v817 v818 v819 v820 v821 v822 v823 v824 v825 v826 v827 v828 v829 v830 v831 v832 v833 v834 v835 v836 v837 v838 v839 v840 v841 v842 v843 v844 v845 v846 v847 v848 v849 v850 v851 v852 v853 v854 v855 v856 v857 v858 v859 v860 v861 v862 v863 v864 v865 v866 v867 v868 v869 v870 v871 v872 v873 v874 v875 v876 v877 v878 v879 v880 v886 v887 v888 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 v918 v919 v920 v921 v922 v923 v924 v925 v926 v933 v934 v938 v939 v940 v941 v942 v943 v944 v945 v946 v947 v948 v949 v950 v951 v952 v953 v954 v955 v956 v957 v958 v959 v960 v961 v962 v963 v964 v965 v966 v967 v968 v969 v970 v971 v972 v973 v974 v975 v976 v977 v978 v979 v980 v981 v982 v983 v984 v985 v986 v987 v988 v989 v990 v991 v992 v993 v994 v995 v996 v997 v998 v999 v1000 v1001 v1002 v1003 v1004 v1005 v1006 v1007 v1008 v1009 v1010 v1011 v1012 v1013 v1014 v1015 v1016 v1017 v1018 v1019 v1020 v1021 v1022 v1023 v1024 v1025 v1026 v1027 v1028 v1029 v1030 v1031 v1032 v1033 v1034 v1035 v1036 v1040 v1041 v1042 v1043 v1044 v1053 v1054 v1055 v1056 v1057 v1058 v1059 v1060 v1061 v1062 v1063 v1064 v1065 v1066 v1067 v1068 v1069 v1070 v1071 v1072 v1073 v1075 v1076 v1077 v1078 v1079 v1081 v1082 v1083 v1084 v1085 v1086 v1087 v1094 v1095 v1096 v1097 v1098 v1099 v1102 v1103 v1104 v1106 v1107 v1108 v1109 v1110 v1111 v1112 v1113 v1114 v1115 v1116 v1117 v1118 v1119 v1120 v1121 v1122 v1123 v1124 v1125 v1126 v1127 v1128 v1129 v1130 v1131 v1132 v1133 v1134 v1135 v1136 v1137 v1138 v1139 v1140 v1141 v1142 v1143 v1144 v1145 v1146 v1147 v1148 v1149 v1150 v1151 v1152 v1153 v1154 v1155 v1156 v1157 v1158 v1159 v1160 v1161 v1162 v1163 v1164 v1165 v1166 v1167 v1168 v1169 v1170 v1171 v1172 v1173 v1174 v1175 v1176 v1177 v1178 v1179 v1180 v1181 v1182 v1183 v1184 v1185 v1186 v1187 v1188 v1189 v1190 v1191 v1192 v1193 v1194 v1195 v1196 v1197 v1198 v1199 v1200 v1201 v1202 v1203 v1204 v1207 v1208 v1209 v1210 v1211 v1212 v1213 v1214 v1215 v1233 v1234 v1235 t1233 v1237 v1238 v1239 v1240 v1241 v1242 v1243 v1244 v1245 v1247 v1248 v1250 v1252 v1254 v1256 v1259 v1260 v1261 v1262 v1263 v1264 v1265 v1266 v1267 v1268 v1269 v1270 v1271 v1272 v1273 v1274 v1275 v1276 v1277 v1278 v1279 v1280 v1281 v1282 v1283 v1284 v1285 v1286 v1287 v1288 v1289 v1290 v1291 v1292 at h
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
  have h_v9 : R 1 0 4611686018427387904 4611686018427387904 v9 v9 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have e_v9 : sv v9 = (0) := e_c 4611686018427387904 (0) (of_decide_eq_true rfl)
  have h_v14 : R 1 0 4611686019270702760 4611686019270702760 v14 v14 := (r_c hl 4611686019270702760 (of_decide_eq_true rfl))
  have e_v14 : sv v14 = (843314856) := e_c 4611686019270702760 (843314856) (of_decide_eq_true rfl)
  have h_v15 : R 1 0 0 1 v15 v15 := (r_plt hl h_v14 h_v7 (of_decide_eq_true rfl))
  clear e_OFFr e_H61r
  have e_v15 : (v15 = 1 ↔ sv v14 < sv v7) := e_plt h_v14 h_v7 (of_decide_eq_true rfl)
  have h_v16 : R 1 0 0 1 v16 v16 := (r_sub hl (r_O hl) h_v15 (of_decide_eq_true rfl))
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
  clear h_v14 h_v15 h_v19 h_v21 h_v22
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
  have e_v38 : sv v38 = (421657427) := e_c 4611686018849045331 (421657427) (of_decide_eq_true rfl)
  have h_v39 : R 1 0 0 1 v39 v39 := (r_plt hl h_v38 h_v1 (of_decide_eq_true rfl))
  clear h_t0_1 h_t1_1 h_v26 h_v27 h_v30 h_v32 h_v34
  have e_v39 : (v39 = 1 ↔ sv v38 < sv v1) := e_plt h_v38 h_v1 (of_decide_eq_true rfl)
  have h_v40 : R 1 0 0 1 v40 v40 := (r_land hl h_v37 h_v39 (of_decide_eq_true rfl))
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
  clear h_v35 h_v37 h_v39 h_v40 h_v45 h_t43_2 e_t43_2
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
  have h_v61 : R 1 0 0 1 v61 v61 := (r_plt hl h_v29 h_v9 (of_decide_eq_true rfl))
  have e_v61 : (v61 = 1 ↔ sv v29 < sv v9) := e_plt h_v29 h_v9 (of_decide_eq_true rfl)
  have h_v62 : R 1 0 0 1 v62 v62 := (r_sub hl (r_O hl) h_v61 (of_decide_eq_true rfl))
  clear h_v43 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v59
  have e_v62 : (v62 = 1 ↔ ¬v61 = 1) := e_not h_v61 (of_decide_eq_true rfl)
  have h_v63 : R 1 0 0 1 v63 v63 := (r_plt hl h_v9 h_v41 (of_decide_eq_true rfl))
  have e_v63 : (v63 = 1 ↔ sv v9 < sv v41) := e_plt h_v9 h_v41 (of_decide_eq_true rfl)
  have h_v64 : R 1 0 0 1 v64 v64 := (r_sub hl (r_O hl) h_v63 (of_decide_eq_true rfl))
  have e_v64 : (v64 = 1 ↔ ¬v63 = 1) := e_not h_v63 (of_decide_eq_true rfl)
  have h_v65 : R 1 0 0 1 v65 v65 := (r_land hl h_v61 h_v64 (of_decide_eq_true rfl))
  have e_v65 : (v65 = 1 ↔ v61 = 1 ∧ v64 = 1) := e_land h_v61 h_v64 (of_decide_eq_true rfl)
  have h_v66 : R 1 0 0 1 v66 v66 := (r_land hl h_v61 h_v63 (of_decide_eq_true rfl))
  have e_v66 : (v66 = 1 ↔ v61 = 1 ∧ v63 = 1) := e_land h_v61 h_v63 (of_decide_eq_true rfl)
  have h_v67 : R 1 0 0 1 v67 v67 := (r_plt hl h_v52 h_v9 (of_decide_eq_true rfl))
  have e_v67 : (v67 = 1 ↔ sv v52 < sv v9) := e_plt h_v52 h_v9 (of_decide_eq_true rfl)
  have h_v68 : R 1 0 0 1 v68 v68 := (r_sub hl (r_O hl) h_v67 (of_decide_eq_true rfl))
  have e_v68 : (v68 = 1 ↔ ¬v67 = 1) := e_not h_v67 (of_decide_eq_true rfl)
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
  have h_v74 : R 1 0 0 1 v74 v74 := (r_sub hl (r_O hl) h_v73 (of_decide_eq_true rfl))
  have e_v74 : (v74 = 1 ↔ ¬v73 = 1) := e_not h_v73 (of_decide_eq_true rfl)
  clear h_v61 h_v63 h_v64 h_v67 h_v69 h_v70 h_v73
  have h_v75 : R 1 0 0 1 v75 v75 := (r_land hl h_v62 h_v72 (of_decide_eq_true rfl))
  have e_v75 : (v75 = 1 ↔ v62 = 1 ∧ v72 = 1) := e_land h_v62 h_v72 (of_decide_eq_true rfl)
  have h_v76 : R 1 0 0 1 v76 v76 := (r_lor hl h_v71 h_v75 (of_decide_eq_true rfl))
  have e_v76 : (v76 = 1 ↔ v71 = 1 ∨ v75 = 1) := e_lor h_v71 h_v75 (of_decide_eq_true rfl)
  have h_v77 : R 1 0 4611686018427387900 4611686018695823367 v77 v77 := (r_psel hl h_v76 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v77 : v77 = if v76 = 1 then v41 else v29 := e_psel h_v76 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v78 : R 1 0 0 1 v78 v78 := (r_land hl h_v66 h_v68 (of_decide_eq_true rfl))
  have e_v78 : (v78 = 1 ↔ v66 = 1 ∧ v68 = 1) := e_land h_v66 h_v68 (of_decide_eq_true rfl)
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
  have h_v87 : R 1 0 4611686017353646052 4683743616223412273 v87 v87 := (r_smx hl 29 h_v80 h_v77 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  clear h_v52 h_v60 h_v68 h_v71 h_v72 h_v75 h_v76 h_v78 h_v79 h_v81 h_v82 h_v84 h_v85
  have e_v87 : sv v87 = sv v80 * sv v77 := e_smx 29 h_v80 h_v77 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v88 : R 1 0 4611686018427387899 4611686018695823374 v88 v88 := (r_srdF hl h_v87 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v88 : sv v88 = sv v87 / 2 ^ 28 := e_srdF h_v87 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v89 : R 1 0 4611686017353646052 4683743616223412273 v89 v89 := (r_smx hl 29 h_v86 h_v83 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v89 : sv v89 = sv v86 * sv v83 := e_smx 29 h_v86 h_v83 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v90 : R 1 0 4611686018427387900 4611686018695823375 v90 v90 := (r_srdC hl h_v89 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v90 : sv v90 = -((-sv v89) / 2 ^ 28) := e_srdC h_v89 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v91 : R 1 0 0 1 v91 v91 := (r_plt hl h_v18 h_v88 (of_decide_eq_true rfl))
  have e_v91 : (v91 = 1 ↔ sv v18 < sv v88) := e_plt h_v18 h_v88 (of_decide_eq_true rfl)
  have h_v93 : R 1 0 4611686018158952441 4611686018695823359 v93 v93 := (r_sub hl (r_add hl h_v28 h_t1_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v93 : sv v93 = sv v28 + sv t1.2 := e_add h_v28 h_t1_2 (of_decide_eq_true rfl)
  have h_v94 : R 1 0 4611686018158952448 4611686018158952448 v94 v94 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have e_v94 : sv v94 = (-268435456) := e_c 4611686018158952448 (-268435456) (of_decide_eq_true rfl)
  have h_v95 : R 1 0 0 1 v95 v95 := (r_plt hl h_v93 h_v94 (of_decide_eq_true rfl))
  have e_v95 : (v95 = 1 ↔ sv v93 < sv v94) := e_plt h_v93 h_v94 (of_decide_eq_true rfl)
  have h_v96 : R 1 0 4611686018158952441 4611686018695823359 v96 v96 := (r_psel hl h_v95 h_v94 h_v93 (of_decide_eq_true rfl))
  have e_v96 : v96 = if v95 = 1 then v94 else v93 := e_psel h_v95 h_v94 h_v93 (of_decide_eq_true rfl)
  have h_v97 : R 1 0 4611686019270702759 4611686019270702759 v97 v97 := (r_c hl 4611686019270702759 (of_decide_eq_true rfl))
  have e_v97 : sv v97 = (843314855) := e_c 4611686019270702759 (843314855) (of_decide_eq_true rfl)
  have h_v98 : R 1 0 0 1 v98 v98 := (r_plt hl h_v97 h_v1 (of_decide_eq_true rfl))
  have e_v98 : (v98 = 1 ↔ sv v97 < sv v1) := e_plt h_v97 h_v1 (of_decide_eq_true rfl)
  have h_v99 : R 1 0 4611686018158952441 4611686018695823359 v99 v99 := (r_psel hl h_v98 h_v94 h_v96 (of_decide_eq_true rfl))
  have e_v99 : v99 = if v98 = 1 then v94 else v96 := e_psel h_v98 h_v94 h_v96 (of_decide_eq_true rfl)
  have h_v101 : R 1 0 4611686018158952449 4611686018695823367 v101 v101 := (r_sub hl (r_add hl h_v31 h_t0_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v101 : sv v101 = sv v31 + sv t0.2 := e_add h_v31 h_t0_2 (of_decide_eq_true rfl)
  clear h_v1 h_t0_2 h_t1_2 h_v77 h_v80 h_v83 h_v86 h_v87 h_v89 h_v93 h_v95 h_v96 h_v97 h_v98
  have h_v102 : R 1 0 0 1 v102 v102 := (r_plt hl h_v101 h_v33 (of_decide_eq_true rfl))
  have e_v102 : (v102 = 1 ↔ sv v101 < sv v33) := e_plt h_v101 h_v33 (of_decide_eq_true rfl)
  have h_v103 : R 1 0 4611686018158952449 4611686018695823367 v103 v103 := (r_psel hl h_v102 h_v101 h_v33 (of_decide_eq_true rfl))
  have e_v103 : v103 = if v102 = 1 then v101 else v33 := e_psel h_v102 h_v101 h_v33 (of_decide_eq_true rfl)
  have h_v104 : R 1 0 4611686018427387905 4611686018427387905 v104 v104 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have e_v104 : sv v104 = (1) := e_c 4611686018427387905 (1) (of_decide_eq_true rfl)
  have h_v105 : R 1 0 0 1 v105 v105 := (r_plt hl h_v0 h_v104 (of_decide_eq_true rfl))
  have e_v105 : (v105 = 1 ↔ sv v0 < sv v104) := e_plt h_v0 h_v104 (of_decide_eq_true rfl)
  have h_v106 : R 1 0 4611686018158952449 4611686018695823367 v106 v106 := (r_psel hl h_v105 h_v33 h_v103 (of_decide_eq_true rfl))
  have e_v106 : v106 = if v105 = 1 then v33 else v103 := e_psel h_v105 h_v33 h_v103 (of_decide_eq_true rfl)
  have h_v107 : R 1 0 4611686018427387904 4611686052787126264 v107 v107 := (r_add hl (r_pshr1 hl h_v3) h_H61r (of_decide_eq_true rfl))
  have e_v107 : sv v107 = sv v3 / 2 := e_halfF h_v3
  have h_v108 : R 1 0 0 1 v108 v108 := (r_plt hl h_v18 h_v107 (of_decide_eq_true rfl))
  have e_v108 : (v108 = 1 ↔ sv v18 < sv v107) := e_plt h_v18 h_v107 (of_decide_eq_true rfl)
  have h_v109 : R 1 0 0 1 v109 v109 := (r_land hl h_v46 h_v108 (of_decide_eq_true rfl))
  have e_v109 : (v109 = 1 ↔ v46 = 1 ∧ v108 = 1) := e_land h_v46 h_v108 (of_decide_eq_true rfl)
  have h_t107_1 : R 1 0 4611686018427387904 4611686018695823363 t107.1 t107.1 := r_sc1 hl h_v107 (of_decide_eq_true rfl)
  have h_t107_2 : R 1 0 4611686018158952445 4611686018695823363 t107.2 t107.2 := r_sc2 hl h_v107 (of_decide_eq_true rfl)
  have e_t107_1 : sv t107.1 = (sc28pS (scArg v107)).1 := e_sc1 h_v107 (of_decide_eq_true rfl)
  have e_t107_2 : sv t107.2 = (sc28pS (scArg v107)).2 := e_sc2 h_v107 (of_decide_eq_true rfl)
  have h_v123 : R 1 0 0 1 v123 v123 := (r_plt hl h_t107_1 h_t43_1 (of_decide_eq_true rfl))
  have e_v123 : (v123 = 1 ↔ sv t107.1 < sv t43.1) := e_plt h_t107_1 h_t43_1 (of_decide_eq_true rfl)
  have h_v124 : R 1 0 4611686018427387904 4611686018695823363 v124 v124 := (r_psel hl h_v123 h_t107_1 h_t43_1 (of_decide_eq_true rfl))
  have e_v124 : v124 = if v123 = 1 then t107.1 else t43.1 := e_psel h_v123 h_t107_1 h_t43_1 (of_decide_eq_true rfl)
  have h_v125 : R 1 0 4611686018427387900 4611686018695823359 v125 v125 := (r_sub hl (r_add hl h_v28 h_v124 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v0 h_v3 h_v46 h_v101 h_v102 h_v103 h_v105 h_v108 h_t107_2 e_t107_2
  have e_v125 : sv v125 = sv v28 + sv v124 := e_add h_v28 h_v124 (of_decide_eq_true rfl)
  have h_v126 : R 1 0 4611686018427387904 4611686018695823363 v126 v126 := (r_psel hl h_v123 h_t43_1 h_t107_1 (of_decide_eq_true rfl))
  have e_v126 : v126 = if v123 = 1 then t43.1 else t107.1 := e_psel h_v123 h_t43_1 h_t107_1 (of_decide_eq_true rfl)
  have h_v127 : R 1 0 4611686018427387908 4611686018695823367 v127 v127 := (r_sub hl (r_add hl h_v31 h_v126 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v127 : sv v127 = sv v31 + sv v126 := e_add h_v31 h_v126 (of_decide_eq_true rfl)
  have h_v128 : R 1 0 0 1 v128 v128 := (r_plt hl h_v127 h_v33 (of_decide_eq_true rfl))
  have e_v128 : (v128 = 1 ↔ sv v127 < sv v33) := e_plt h_v127 h_v33 (of_decide_eq_true rfl)
  have h_v129 : R 1 0 4611686018427387908 4611686018695823367 v129 v129 := (r_psel hl h_v128 h_v127 h_v33 (of_decide_eq_true rfl))
  have e_v129 : v129 = if v128 = 1 then v127 else v33 := e_psel h_v128 h_v127 h_v33 (of_decide_eq_true rfl)
  have h_v130 : R 1 0 0 1 v130 v130 := (r_plt hl h_v107 h_v36 (of_decide_eq_true rfl))
  have e_v130 : (v130 = 1 ↔ sv v107 < sv v36) := e_plt h_v107 h_v36 (of_decide_eq_true rfl)
  have h_v131 : R 1 0 0 1 v131 v131 := (r_land hl h_v58 h_v130 (of_decide_eq_true rfl))
  have e_v131 : (v131 = 1 ↔ v58 = 1 ∧ v130 = 1) := e_land h_v58 h_v130 (of_decide_eq_true rfl)
  have h_v132 : R 1 0 4611686018427387908 4611686018695823367 v132 v132 := (r_psel hl h_v131 h_v33 h_v129 (of_decide_eq_true rfl))
  have e_v132 : v132 = if v131 = 1 then v33 else v129 := e_psel h_v131 h_v33 h_v129 (of_decide_eq_true rfl)
  have h_v133 : R 1 0 0 1 v133 v133 := (r_plt hl h_v99 h_v9 (of_decide_eq_true rfl))
  have e_v133 : (v133 = 1 ↔ sv v99 < sv v9) := e_plt h_v99 h_v9 (of_decide_eq_true rfl)
  have h_v134 : R 1 0 0 1 v134 v134 := (r_sub hl (r_O hl) h_v133 (of_decide_eq_true rfl))
  have e_v134 : (v134 = 1 ↔ ¬v133 = 1) := e_not h_v133 (of_decide_eq_true rfl)
  have h_v135 : R 1 0 0 1 v135 v135 := (r_plt hl h_v9 h_v106 (of_decide_eq_true rfl))
  have e_v135 : (v135 = 1 ↔ sv v9 < sv v106) := e_plt h_v9 h_v106 (of_decide_eq_true rfl)
  have h_v136 : R 1 0 0 1 v136 v136 := (r_sub hl (r_O hl) h_v135 (of_decide_eq_true rfl))
  have e_v136 : (v136 = 1 ↔ ¬v135 = 1) := e_not h_v135 (of_decide_eq_true rfl)
  have h_v137 : R 1 0 0 1 v137 v137 := (r_land hl h_v133 h_v136 (of_decide_eq_true rfl))
  have e_v137 : (v137 = 1 ↔ v133 = 1 ∧ v136 = 1) := e_land h_v133 h_v136 (of_decide_eq_true rfl)
  clear h_t43_1 h_v58 h_v107 h_t107_1 h_v123 h_v124 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v136
  have h_v138 : R 1 0 0 1 v138 v138 := (r_land hl h_v133 h_v135 (of_decide_eq_true rfl))
  have e_v138 : (v138 = 1 ↔ v133 = 1 ∧ v135 = 1) := e_land h_v133 h_v135 (of_decide_eq_true rfl)
  have h_v139 : R 1 0 0 1 v139 v139 := (r_plt hl h_v125 h_v9 (of_decide_eq_true rfl))
  have e_v139 : (v139 = 1 ↔ sv v125 < sv v9) := e_plt h_v125 h_v9 (of_decide_eq_true rfl)
  have h_v141 : R 1 0 0 1 v141 v141 := (r_plt hl h_v9 h_v132 (of_decide_eq_true rfl))
  have e_v141 : (v141 = 1 ↔ sv v9 < sv v132) := e_plt h_v9 h_v132 (of_decide_eq_true rfl)
  have h_v144 : R 1 0 0 1 v144 v144 := (r_land hl h_v139 h_v141 (of_decide_eq_true rfl))
  have e_v144 : (v144 = 1 ↔ v139 = 1 ∧ v141 = 1) := e_land h_v139 h_v141 (of_decide_eq_true rfl)
  have h_v145 : R 1 0 0 1 v145 v145 := (r_land hl h_v138 h_v144 (of_decide_eq_true rfl))
  have e_v145 : (v145 = 1 ↔ v138 = 1 ∧ v144 = 1) := e_land h_v138 h_v144 (of_decide_eq_true rfl)
  have h_v146 : R 1 0 0 1 v146 v146 := (r_sub hl (r_O hl) h_v145 (of_decide_eq_true rfl))
  have e_v146 : (v146 = 1 ↔ ¬v145 = 1) := e_not h_v145 (of_decide_eq_true rfl)
  have h_v195 : R 1 0 4611686018849045332 4611686018849045332 v195 v195 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  have e_v195 : sv v195 = (421657428) := e_c 4611686018849045332 (421657428) (of_decide_eq_true rfl)
  have h_v202 : R 1 0 4611686018849045333 4611686018849045333 v202 v202 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have e_v202 : sv v202 = (421657429) := e_c 4611686018849045333 (421657429) (of_decide_eq_true rfl)
  have h_v256 : R 1 0 4611686018427387904 4611686052787126264 v256 v256 := (r_add hl (r_pshr1 hl (r_add hl h_v2 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v256 : sv v256 = (sv v2 + 1) / 2 := e_halfC h_v2 (of_decide_eq_true rfl)
  have h_v257 : R 1 0 0 1 v257 v257 := (r_plt hl h_v20 h_v256 (of_decide_eq_true rfl))
  have e_v257 : (v257 = 1 ↔ sv v20 < sv v256) := e_plt h_v20 h_v256 (of_decide_eq_true rfl)
  have h_v258 : R 1 0 0 1 v258 v258 := (r_sub hl (r_O hl) h_v257 (of_decide_eq_true rfl))
  have e_v258 : (v258 = 1 ↔ ¬v257 = 1) := e_not h_v257 (of_decide_eq_true rfl)
  have h_v259 : R 1 0 0 1 v259 v259 := (r_land hl h_v44 h_v258 (of_decide_eq_true rfl))
  have e_v259 : (v259 = 1 ↔ v44 = 1 ∧ v258 = 1) := e_land h_v44 h_v258 (of_decide_eq_true rfl)
  have h_v267 : R 1 0 4611686018158952449 4611686018695823367 v267 v267 := (r_sub hl (r_add hl h_v31 h_t42_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v2 h_v44 h_v125 h_v132 h_v133 h_v135 h_v139 h_v141 h_v144 h_v145 h_v257 h_v258
  have e_v267 : sv v267 = sv v31 + sv t42.2 := e_add h_v31 h_t42_2 (of_decide_eq_true rfl)
  have h_v268 : R 1 0 0 1 v268 v268 := (r_plt hl h_v267 h_v33 (of_decide_eq_true rfl))
  have e_v268 : (v268 = 1 ↔ sv v267 < sv v33) := e_plt h_v267 h_v33 (of_decide_eq_true rfl)
  have h_v269 : R 1 0 4611686018158952449 4611686018695823367 v269 v269 := (r_psel hl h_v268 h_v267 h_v33 (of_decide_eq_true rfl))
  have e_v269 : v269 = if v268 = 1 then v267 else v33 := e_psel h_v268 h_v267 h_v33 (of_decide_eq_true rfl)
  have h_v270 : R 1 0 0 1 v270 v270 := (r_plt hl h_v42 h_v104 (of_decide_eq_true rfl))
  have e_v270 : (v270 = 1 ↔ sv v42 < sv v104) := e_plt h_v42 h_v104 (of_decide_eq_true rfl)
  have h_v271 : R 1 0 4611686018158952449 4611686018695823367 v271 v271 := (r_psel hl h_v270 h_v33 h_v269 (of_decide_eq_true rfl))
  have e_v271 : v271 = if v270 = 1 then v33 else v269 := e_psel h_v270 h_v33 h_v269 (of_decide_eq_true rfl)
  have h_t256_1 : R 1 0 4611686018427387904 4611686018695823363 t256.1 t256.1 := r_sc1 hl h_v256 (of_decide_eq_true rfl)
  have h_t256_2 : R 1 0 4611686018158952445 4611686018695823363 t256.2 t256.2 := r_sc2 hl h_v256 (of_decide_eq_true rfl)
  have e_t256_1 : sv t256.1 = (sc28pS (scArg v256)).1 := e_sc1 h_v256 (of_decide_eq_true rfl)
  have e_t256_2 : sv t256.2 = (sc28pS (scArg v256)).2 := e_sc2 h_v256 (of_decide_eq_true rfl)
  have h_v273 : R 1 0 0 1 v273 v273 := (r_plt hl h_t42_1 h_t256_1 (of_decide_eq_true rfl))
  have e_v273 : (v273 = 1 ↔ sv t42.1 < sv t256.1) := e_plt h_t42_1 h_t256_1 (of_decide_eq_true rfl)
  have h_v274 : R 1 0 4611686018427387904 4611686018695823363 v274 v274 := (r_psel hl h_v273 h_t42_1 h_t256_1 (of_decide_eq_true rfl))
  have e_v274 : v274 = if v273 = 1 then t42.1 else t256.1 := e_psel h_v273 h_t42_1 h_t256_1 (of_decide_eq_true rfl)
  have h_v275 : R 1 0 4611686018427387900 4611686018695823359 v275 v275 := (r_sub hl (r_add hl h_v28 h_v274 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v275 : sv v275 = sv v28 + sv v274 := e_add h_v28 h_v274 (of_decide_eq_true rfl)
  have h_v276 : R 1 0 4611686018427387904 4611686018695823363 v276 v276 := (r_psel hl h_v273 h_t256_1 h_t42_1 (of_decide_eq_true rfl))
  have e_v276 : v276 = if v273 = 1 then t256.1 else t42.1 := e_psel h_v273 h_t256_1 h_t42_1 (of_decide_eq_true rfl)
  have h_v277 : R 1 0 4611686018427387908 4611686018695823367 v277 v277 := (r_sub hl (r_add hl h_v31 h_v276 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v277 : sv v277 = sv v31 + sv v276 := e_add h_v31 h_v276 (of_decide_eq_true rfl)
  have h_v278 : R 1 0 0 1 v278 v278 := (r_plt hl h_v277 h_v33 (of_decide_eq_true rfl))
  have e_v278 : (v278 = 1 ↔ sv v277 < sv v33) := e_plt h_v277 h_v33 (of_decide_eq_true rfl)
  clear h_v42 h_t42_1 h_t42_2 h_v267 h_v268 h_v269 h_v270 h_t256_1 h_t256_2 e_t256_2 h_v273 h_v274 h_v276
  have h_v279 : R 1 0 4611686018427387908 4611686018695823367 v279 v279 := (r_psel hl h_v278 h_v277 h_v33 (of_decide_eq_true rfl))
  have e_v279 : v279 = if v278 = 1 then v277 else v33 := e_psel h_v278 h_v277 h_v33 (of_decide_eq_true rfl)
  have h_v280 : R 1 0 0 1 v280 v280 := (r_plt hl h_v38 h_v256 (of_decide_eq_true rfl))
  have e_v280 : (v280 = 1 ↔ sv v38 < sv v256) := e_plt h_v38 h_v256 (of_decide_eq_true rfl)
  have h_v281 : R 1 0 0 1 v281 v281 := (r_land hl h_v57 h_v280 (of_decide_eq_true rfl))
  have e_v281 : (v281 = 1 ↔ v57 = 1 ∧ v280 = 1) := e_land h_v57 h_v280 (of_decide_eq_true rfl)
  have h_v282 : R 1 0 4611686018427387908 4611686018695823367 v282 v282 := (r_psel hl h_v281 h_v33 h_v279 (of_decide_eq_true rfl))
  have e_v282 : v282 = if v281 = 1 then v33 else v279 := e_psel h_v281 h_v33 h_v279 (of_decide_eq_true rfl)
  have h_v283 : R 1 0 0 1 v283 v283 := (r_plt hl h_v275 h_v9 (of_decide_eq_true rfl))
  have e_v283 : (v283 = 1 ↔ sv v275 < sv v9) := e_plt h_v275 h_v9 (of_decide_eq_true rfl)
  have h_v284 : R 1 0 0 1 v284 v284 := (r_sub hl (r_O hl) h_v283 (of_decide_eq_true rfl))
  have e_v284 : (v284 = 1 ↔ ¬v283 = 1) := e_not h_v283 (of_decide_eq_true rfl)
  have h_v285 : R 1 0 0 1 v285 v285 := (r_plt hl h_v9 h_v282 (of_decide_eq_true rfl))
  have e_v285 : (v285 = 1 ↔ sv v9 < sv v282) := e_plt h_v9 h_v282 (of_decide_eq_true rfl)
  have h_v286 : R 1 0 0 1 v286 v286 := (r_sub hl (r_O hl) h_v285 (of_decide_eq_true rfl))
  have e_v286 : (v286 = 1 ↔ ¬v285 = 1) := e_not h_v285 (of_decide_eq_true rfl)
  have h_v287 : R 1 0 0 1 v287 v287 := (r_land hl h_v283 h_v286 (of_decide_eq_true rfl))
  have e_v287 : (v287 = 1 ↔ v283 = 1 ∧ v286 = 1) := e_land h_v283 h_v286 (of_decide_eq_true rfl)
  have h_v288 : R 1 0 0 1 v288 v288 := (r_land hl h_v283 h_v285 (of_decide_eq_true rfl))
  have e_v288 : (v288 = 1 ↔ v283 = 1 ∧ v285 = 1) := e_land h_v283 h_v285 (of_decide_eq_true rfl)
  have h_v289 : R 1 0 0 1 v289 v289 := (r_land hl h_v138 h_v288 (of_decide_eq_true rfl))
  have e_v289 : (v289 = 1 ↔ v138 = 1 ∧ v288 = 1) := e_land h_v138 h_v288 (of_decide_eq_true rfl)
  have h_v290 : R 1 0 0 1 v290 v290 := (r_sub hl (r_O hl) h_v289 (of_decide_eq_true rfl))
  have e_v290 : (v290 = 1 ↔ ¬v289 = 1) := e_not h_v289 (of_decide_eq_true rfl)
  have h_v291 : R 1 0 0 1 v291 v291 := (r_land hl h_v134 h_v288 (of_decide_eq_true rfl))
  clear h_v57 h_v256 h_v277 h_v278 h_v279 h_v280 h_v281 h_v283 h_v285 h_v286 h_v289
  have e_v291 : (v291 = 1 ↔ v134 = 1 ∧ v288 = 1) := e_land h_v134 h_v288 (of_decide_eq_true rfl)
  have h_v292 : R 1 0 0 1 v292 v292 := (r_lor hl h_v287 h_v291 (of_decide_eq_true rfl))
  have e_v292 : (v292 = 1 ↔ v287 = 1 ∨ v291 = 1) := e_lor h_v287 h_v291 (of_decide_eq_true rfl)
  have h_v293 : R 1 0 4611686018158952441 4611686018695823367 v293 v293 := (r_psel hl h_v292 h_v106 h_v99 (of_decide_eq_true rfl))
  have e_v293 : v293 = if v292 = 1 then v106 else v99 := e_psel h_v292 h_v106 h_v99 (of_decide_eq_true rfl)
  have h_v294 : R 1 0 0 1 v294 v294 := (r_land hl h_v138 h_v284 (of_decide_eq_true rfl))
  have e_v294 : (v294 = 1 ↔ v138 = 1 ∧ v284 = 1) := e_land h_v138 h_v284 (of_decide_eq_true rfl)
  have h_v295 : R 1 0 0 1 v295 v295 := (r_lor hl h_v137 h_v294 (of_decide_eq_true rfl))
  have e_v295 : (v295 = 1 ↔ v137 = 1 ∨ v294 = 1) := e_lor h_v137 h_v294 (of_decide_eq_true rfl)
  have h_v296 : R 1 0 4611686018427387900 4611686018695823367 v296 v296 := (r_psel hl h_v295 h_v282 h_v275 (of_decide_eq_true rfl))
  have e_v296 : v296 = if v295 = 1 then v282 else v275 := e_psel h_v295 h_v282 h_v275 (of_decide_eq_true rfl)
  have h_v297 : R 1 0 0 1 v297 v297 := (r_land hl h_v137 h_v288 (of_decide_eq_true rfl))
  have e_v297 : (v297 = 1 ↔ v137 = 1 ∧ v288 = 1) := e_land h_v137 h_v288 (of_decide_eq_true rfl)
  have h_v298 : R 1 0 0 1 v298 v298 := (r_lor hl h_v287 h_v297 (of_decide_eq_true rfl))
  have e_v298 : (v298 = 1 ↔ v287 = 1 ∨ v297 = 1) := e_lor h_v287 h_v297 (of_decide_eq_true rfl)
  have h_v299 : R 1 0 4611686018158952441 4611686018695823367 v299 v299 := (r_psel hl h_v298 h_v99 h_v106 (of_decide_eq_true rfl))
  have e_v299 : v299 = if v298 = 1 then v99 else v106 := e_psel h_v298 h_v99 h_v106 (of_decide_eq_true rfl)
  have h_v300 : R 1 0 0 1 v300 v300 := (r_land hl h_v138 h_v287 (of_decide_eq_true rfl))
  have e_v300 : (v300 = 1 ↔ v138 = 1 ∧ v287 = 1) := e_land h_v138 h_v287 (of_decide_eq_true rfl)
  have h_v301 : R 1 0 0 1 v301 v301 := (r_lor hl h_v137 h_v300 (of_decide_eq_true rfl))
  have e_v301 : (v301 = 1 ↔ v137 = 1 ∨ v300 = 1) := e_lor h_v137 h_v300 (of_decide_eq_true rfl)
  have h_v302 : R 1 0 4611686018427387900 4611686018695823367 v302 v302 := (r_psel hl h_v301 h_v275 h_v282 (of_decide_eq_true rfl))
  have e_v302 : v302 = if v301 = 1 then v275 else v282 := e_psel h_v301 h_v275 h_v282 (of_decide_eq_true rfl)
  have h_v303 : R 1 0 4539628420631363535 4683743616223412273 v303 v303 := (r_smx hl 29 h_v296 h_v293 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v303 : sv v303 = sv v296 * sv v293 := e_smx 29 h_v296 h_v293 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  clear h_v275 h_v282 h_v284 h_v287 h_v288 h_v291 h_v292 h_v293 h_v294 h_v295 h_v296 h_v297 h_v298 h_v300 h_v301
  have h_v304 : R 1 0 4611686018158952433 4611686018695823374 v304 v304 := (r_srdF hl h_v303 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v304 : sv v304 = sv v303 / 2 ^ 28 := e_srdF h_v303 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v305 : R 1 0 4539628420631363535 4683743616223412273 v305 v305 := (r_smx hl 29 h_v302 h_v299 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v305 : sv v305 = sv v302 * sv v299 := e_smx 29 h_v302 h_v299 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v306 : R 1 0 4611686018158952434 4611686018695823375 v306 v306 := (r_srdC hl h_v305 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v306 : sv v306 = -((-sv v305) / 2 ^ 28) := e_srdC h_v305 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v307 : R 1 0 0 1 v307 v307 := (r_plt hl h_v9 h_v304 (of_decide_eq_true rfl))
  have e_v307 : (v307 = 1 ↔ sv v9 < sv v304) := e_plt h_v9 h_v304 (of_decide_eq_true rfl)
  have h_v308 : R 1 0 0 1 v308 v308 := (r_sub hl (r_O hl) h_v307 (of_decide_eq_true rfl))
  have e_v308 : (v308 = 1 ↔ ¬v307 = 1) := e_not h_v307 (of_decide_eq_true rfl)
  have h_v311 : R 1 0 0 1 v311 v311 := (r_plt hl h_v271 h_v9 (of_decide_eq_true rfl))
  have e_v311 : (v311 = 1 ↔ sv v271 < sv v9) := e_plt h_v271 h_v9 (of_decide_eq_true rfl)
  have h_v312 : R 1 0 4611686018158952433 4611686018695823375 v312 v312 := (r_psel hl h_v311 h_v306 h_v304 (of_decide_eq_true rfl))
  have e_v312 : v312 = if v311 = 1 then v306 else v304 := e_psel h_v311 h_v306 h_v304 (of_decide_eq_true rfl)
  have h_v354 : R 1 0 4611686018158952441 4611686018695823359 v354 v354 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v271 (of_decide_eq_true rfl))
  have e_v354 : sv v354 = sv v9 - sv v271 := e_sub h_v9 h_v271 (of_decide_eq_true rfl)
  have h_v355 : R 1 0 4611686018158952441 4611686018695823367 v355 v355 := (r_psel hl h_v311 h_v354 h_v271 (of_decide_eq_true rfl))
  have e_v355 : v355 = if v311 = 1 then v354 else v271 := e_psel h_v311 h_v354 h_v271 (of_decide_eq_true rfl)
  have h_v356 : R 1 0 4611686018427387904 4611686019501129727 v356 v356 := (r1_hxa hb_H0 0 (of_decide_eq_true rfl))
  have e_v356 : sv v356 = ((H0 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 0 (of_decide_eq_true rfl)
  have h_t356_1 : R 1 0 4611686018427387904 4611686018695823363 t356.1 t356.1 := r_sc1 hl h_v356 (of_decide_eq_true rfl)
  have h_t356_2 : R 1 0 4611686018158952445 4611686018695823363 t356.2 t356.2 := r_sc2 hl h_v356 (of_decide_eq_true rfl)
  have e_t356_1 : sv t356.1 = (sc28pS (scArg v356)).1 := e_sc1 h_v356 (of_decide_eq_true rfl)
  have e_t356_2 : sv t356.2 = (sc28pS (scArg v356)).2 := e_sc2 h_v356 (of_decide_eq_true rfl)
  have h_v358 : R 1 0 4611686018158952441 4611686018695823359 v358 v358 := (r_sub hl (r_add hl h_v28 h_t356_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v271 h_v299 h_v302 h_v303 h_v304 h_v305 h_v306 h_v307 h_v354
  have e_v358 : sv v358 = sv v28 + sv t356.2 := e_add h_v28 h_t356_2 (of_decide_eq_true rfl)
  have h_v359 : R 1 0 0 1 v359 v359 := (r_plt hl h_v358 h_v94 (of_decide_eq_true rfl))
  have e_v359 : (v359 = 1 ↔ sv v358 < sv v94) := e_plt h_v358 h_v94 (of_decide_eq_true rfl)
  have h_v360 : R 1 0 4611686018158952441 4611686018695823359 v360 v360 := (r_psel hl h_v359 h_v94 h_v358 (of_decide_eq_true rfl))
  have e_v360 : v360 = if v359 = 1 then v94 else v358 := e_psel h_v359 h_v94 h_v358 (of_decide_eq_true rfl)
  have h_v361 : R 1 0 4611686018158952449 4611686018695823367 v361 v361 := (r_sub hl (r_add hl h_v31 h_t356_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v361 : sv v361 = sv v31 + sv t356.2 := e_add h_v31 h_t356_2 (of_decide_eq_true rfl)
  have h_v362 : R 1 0 0 1 v362 v362 := (r_plt hl h_v361 h_v33 (of_decide_eq_true rfl))
  have e_v362 : (v362 = 1 ↔ sv v361 < sv v33) := e_plt h_v361 h_v33 (of_decide_eq_true rfl)
  have h_v363 : R 1 0 4611686018158952449 4611686018695823367 v363 v363 := (r_psel hl h_v362 h_v361 h_v33 (of_decide_eq_true rfl))
  have e_v363 : v363 = if v362 = 1 then v361 else v33 := e_psel h_v362 h_v361 h_v33 (of_decide_eq_true rfl)
  have h_v365 : R 1 0 4611686018427387908 4611686018695823367 v365 v365 := (r_sub hl (r_add hl h_v31 h_t356_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v365 : sv v365 = sv v31 + sv t356.1 := e_add h_v31 h_t356_1 (of_decide_eq_true rfl)
  have h_v366 : R 1 0 0 1 v366 v366 := (r_plt hl h_v365 h_v33 (of_decide_eq_true rfl))
  have e_v366 : (v366 = 1 ↔ sv v365 < sv v33) := e_plt h_v365 h_v33 (of_decide_eq_true rfl)
  have h_v367 : R 1 0 4611686018427387908 4611686018695823367 v367 v367 := (r_psel hl h_v366 h_v365 h_v33 (of_decide_eq_true rfl))
  have e_v367 : v367 = if v366 = 1 then v365 else v33 := e_psel h_v366 h_v365 h_v33 (of_decide_eq_true rfl)
  have h_v368 : R 1 0 4611686018427387900 4611686018695823359 v368 v368 := (r_sub hl (r_add hl h_v28 h_t356_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v368 : sv v368 = sv v28 + sv t356.1 := e_add h_v28 h_t356_1 (of_decide_eq_true rfl)
  have h_v369 : R 1 0 4611686018158952441 4611686018695823367 v369 v369 := (r_psel hl h_v311 h_v360 h_v363 (of_decide_eq_true rfl))
  have e_v369 : v369 = if v311 = 1 then v360 else v363 := e_psel h_v311 h_v360 h_v363 (of_decide_eq_true rfl)
  have h_v370 : R 1 0 4611686018427387900 4611686018695823367 v370 v370 := (r_psel hl h_v311 h_v367 h_v368 (of_decide_eq_true rfl))
  have e_v370 : v370 = if v311 = 1 then v367 else v368 := e_psel h_v311 h_v367 h_v368 (of_decide_eq_true rfl)
  have h_v371 : R 1 0 4539628418483879831 4683743618370895977 v371 v371 := (r_smx hl 29 h_v312 h_v370 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v371 : sv v371 = sv v312 * sv v370 := e_smx 29 h_v312 h_v370 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  clear h_v312 h_t356_1 h_t356_2 h_v358 h_v359 h_v361 h_v362 h_v363 h_v365 h_v366 h_v367 h_v368 h_v370
  have h_v372 : R 1 0 4539628420631363535 4683743616223412273 v372 v372 := (r_smx hl 29 h_v369 h_v355 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v372 : sv v372 = sv v369 * sv v355 := e_smx 29 h_v369 h_v355 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v373 : R 1 0 0 1 v373 v373 := (r_plt hl h_v372 h_v371 (of_decide_eq_true rfl))
  have e_v373 : (v373 = 1 ↔ sv v372 < sv v371) := e_plt h_v372 h_v371 (of_decide_eq_true rfl)
  have h_v374 : R 1 0 0 1 v374 v374 := (r_sub hl (r_O hl) h_v373 (of_decide_eq_true rfl))
  have e_v374 : (v374 = 1 ↔ ¬v373 = 1) := e_not h_v373 (of_decide_eq_true rfl)
  have h_v375 : R 1 0 0 1 v375 v375 := (r_plt hl h_v371 h_v372 (of_decide_eq_true rfl))
  have e_v375 : (v375 = 1 ↔ sv v371 < sv v372) := e_plt h_v371 h_v372 (of_decide_eq_true rfl)
  have h_v376 : R 1 0 0 1 v376 v376 := (r_sub hl (r_O hl) h_v375 (of_decide_eq_true rfl))
  have e_v376 : (v376 = 1 ↔ ¬v375 = 1) := e_not h_v375 (of_decide_eq_true rfl)
  have h_v377 : R 1 0 0 1 v377 v377 := (r_plt hl h_v9 h_v356 (of_decide_eq_true rfl))
  have e_v377 : (v377 = 1 ↔ sv v9 < sv v356) := e_plt h_v9 h_v356 (of_decide_eq_true rfl)
  have h_v378 : R 1 0 0 1 v378 v378 := (r_sub hl (r_O hl) h_v377 (of_decide_eq_true rfl))
  have e_v378 : (v378 = 1 ↔ ¬v377 = 1) := e_not h_v377 (of_decide_eq_true rfl)
  have h_v379 : R 1 0 0 1 v379 v379 := (r_plt hl h_v195 h_v356 (of_decide_eq_true rfl))
  have e_v379 : (v379 = 1 ↔ sv v195 < sv v356) := e_plt h_v195 h_v356 (of_decide_eq_true rfl)
  have h_v380 : R 1 0 0 1 v380 v380 := (r_sub hl (r_O hl) h_v379 (of_decide_eq_true rfl))
  have e_v380 : (v380 = 1 ↔ ¬v379 = 1) := e_not h_v379 (of_decide_eq_true rfl)
  have h_v381 : R 1 0 0 1 v381 v381 := (r_plt hl h_v18 h_v360 (of_decide_eq_true rfl))
  have e_v381 : (v381 = 1 ↔ sv v18 < sv v360) := e_plt h_v18 h_v360 (of_decide_eq_true rfl)
  have h_v382 : R 1 0 0 1 v382 v382 := (r_land hl h_v374 h_v381 (of_decide_eq_true rfl))
  have e_v382 : (v382 = 1 ↔ v374 = 1 ∧ v381 = 1) := e_land h_v374 h_v381 (of_decide_eq_true rfl)
  have h_v383 : R 1 0 0 1 v383 v383 := (r_land hl h_v380 h_v382 (of_decide_eq_true rfl))
  have e_v383 : (v383 = 1 ↔ v380 = 1 ∧ v382 = 1) := e_land h_v380 h_v382 (of_decide_eq_true rfl)
  have h_v384 : R 1 0 0 1 v384 v384 := (r_lor hl h_v378 h_v383 (of_decide_eq_true rfl))
  clear h_v355 h_v360 h_v369 h_v371 h_v372 h_v373 h_v374 h_v375 h_v377 h_v379 h_v380 h_v381 h_v382
  have e_v384 : (v384 = 1 ↔ v378 = 1 ∨ v383 = 1) := e_lor h_v378 h_v383 (of_decide_eq_true rfl)
  have h_v385 : R 1 0 0 1 v385 v385 := (r_plt hl h_v356 h_v202 (of_decide_eq_true rfl))
  have e_v385 : (v385 = 1 ↔ sv v356 < sv v202) := e_plt h_v356 h_v202 (of_decide_eq_true rfl)
  have h_v386 : R 1 0 0 1 v386 v386 := (r_sub hl (r_O hl) h_v385 (of_decide_eq_true rfl))
  have e_v386 : (v386 = 1 ↔ ¬v385 = 1) := e_not h_v385 (of_decide_eq_true rfl)
  have h_v387 : R 1 0 0 1 v387 v387 := (r_lor hl h_v376 h_v386 (of_decide_eq_true rfl))
  have e_v387 : (v387 = 1 ↔ v376 = 1 ∨ v386 = 1) := e_lor h_v376 h_v386 (of_decide_eq_true rfl)
  have h_v388 : R 1 0 0 1 v388 v388 := (r_land hl h_v311 h_v384 (of_decide_eq_true rfl))
  have e_v388 : (v388 = 1 ↔ v311 = 1 ∧ v384 = 1) := e_land h_v311 h_v384 (of_decide_eq_true rfl)
  have h_v389 : R 1 0 0 1 v389 v389 := (r_sub hl (r_O hl) h_v311 (of_decide_eq_true rfl))
  have e_v389 : (v389 = 1 ↔ ¬v311 = 1) := e_not h_v311 (of_decide_eq_true rfl)
  have h_v390 : R 1 0 0 1 v390 v390 := (r_land hl h_v387 h_v389 (of_decide_eq_true rfl))
  have e_v390 : (v390 = 1 ↔ v387 = 1 ∧ v389 = 1) := e_land h_v387 h_v389 (of_decide_eq_true rfl)
  have h_v391 : R 1 0 0 1 v391 v391 := (r_lor hl h_v388 h_v390 (of_decide_eq_true rfl))
  have e_v391 : (v391 = 1 ↔ v388 = 1 ∨ v390 = 1) := e_lor h_v388 h_v390 (of_decide_eq_true rfl)
  have h_v392 : R 1 0 4611686017353646081 4611686018427387904 v392 v392 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v356 (of_decide_eq_true rfl))
  have e_v392 : sv v392 = sv v9 - sv v356 := e_sub h_v9 h_v356 (of_decide_eq_true rfl)
  have h_v393 : R 1 0 4611686017353646081 4611686019501129727 v393 v393 := (r_psel hl h_v311 h_v392 h_v356 (of_decide_eq_true rfl))
  have e_v393 : v393 = if v311 = 1 then v392 else v356 := e_psel h_v311 h_v392 h_v356 (of_decide_eq_true rfl)
  have h_v394 : R 1 0 4611686017353646081 4611686019501129727 v394 v394 := (r_psel hl h_v391 h_v393 h_v202 (of_decide_eq_true rfl))
  have e_v394 : v394 = if v391 = 1 then v393 else v202 := e_psel h_v391 h_v393 h_v202 (of_decide_eq_true rfl)
  have h_v396 : R 1 0 4611686017353646081 4611686019501129727 v396 v396 := (r_psel hl h_v308 h_v202 h_v394 (of_decide_eq_true rfl))
  have e_v396 : v396 = if v308 = 1 then v202 else v394 := e_psel h_v308 h_v202 h_v394 (of_decide_eq_true rfl)
  have h_v397 : R 1 0 4611686018427387904 4611686052787126264 v397 v397 := (r_add hl (r_pshr1 hl h_v4) h_H61r (of_decide_eq_true rfl))
  have e_v397 : sv v397 = sv v4 / 2 := e_halfF h_v4
  clear h_v308 h_v311 h_v356 h_v376 h_v378 h_v383 h_v384 h_v385 h_v386 h_v387 h_v388 h_v389 h_v390 h_v391 h_v392 h_v393 h_v394
  have h_v398 : R 1 0 4611686018427387904 4611686052787126264 v398 v398 := (r_add hl (r_pshr1 hl (r_add hl h_v5 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v398 : sv v398 = (sv v5 + 1) / 2 := e_halfC h_v5 (of_decide_eq_true rfl)
  have h_v399 : R 1 0 0 1 v399 v399 := (r_plt hl h_v18 h_v397 (of_decide_eq_true rfl))
  have e_v399 : (v399 = 1 ↔ sv v18 < sv v397) := e_plt h_v18 h_v397 (of_decide_eq_true rfl)
  have h_v400 : R 1 0 0 1 v400 v400 := (r_plt hl h_v20 h_v398 (of_decide_eq_true rfl))
  have e_v400 : (v400 = 1 ↔ sv v20 < sv v398) := e_plt h_v20 h_v398 (of_decide_eq_true rfl)
  have h_v401 : R 1 0 0 1 v401 v401 := (r_sub hl (r_O hl) h_v400 (of_decide_eq_true rfl))
  have e_v401 : (v401 = 1 ↔ ¬v400 = 1) := e_not h_v400 (of_decide_eq_true rfl)
  have h_v402 : R 1 0 0 1 v402 v402 := (r_land hl h_v399 h_v401 (of_decide_eq_true rfl))
  have e_v402 : (v402 = 1 ↔ v399 = 1 ∧ v401 = 1) := e_land h_v399 h_v401 (of_decide_eq_true rfl)
  have h_t397_1 : R 1 0 4611686018427387904 4611686018695823363 t397.1 t397.1 := r_sc1 hl h_v397 (of_decide_eq_true rfl)
  have h_t397_2 : R 1 0 4611686018158952445 4611686018695823363 t397.2 t397.2 := r_sc2 hl h_v397 (of_decide_eq_true rfl)
  have e_t397_1 : sv t397.1 = (sc28pS (scArg v397)).1 := e_sc1 h_v397 (of_decide_eq_true rfl)
  have e_t397_2 : sv t397.2 = (sc28pS (scArg v397)).2 := e_sc2 h_v397 (of_decide_eq_true rfl)
  have h_t398_1 : R 1 0 4611686018427387904 4611686018695823363 t398.1 t398.1 := r_sc1 hl h_v398 (of_decide_eq_true rfl)
  have h_t398_2 : R 1 0 4611686018158952445 4611686018695823363 t398.2 t398.2 := r_sc2 hl h_v398 (of_decide_eq_true rfl)
  have e_t398_1 : sv t398.1 = (sc28pS (scArg v398)).1 := e_sc1 h_v398 (of_decide_eq_true rfl)
  have e_t398_2 : sv t398.2 = (sc28pS (scArg v398)).2 := e_sc2 h_v398 (of_decide_eq_true rfl)
  have h_v405 : R 1 0 0 1 v405 v405 := (r_plt hl h_t397_1 h_t398_1 (of_decide_eq_true rfl))
  have e_v405 : (v405 = 1 ↔ sv t397.1 < sv t398.1) := e_plt h_t397_1 h_t398_1 (of_decide_eq_true rfl)
  have h_v406 : R 1 0 4611686018427387904 4611686018695823363 v406 v406 := (r_psel hl h_v405 h_t397_1 h_t398_1 (of_decide_eq_true rfl))
  have e_v406 : v406 = if v405 = 1 then t397.1 else t398.1 := e_psel h_v405 h_t397_1 h_t398_1 (of_decide_eq_true rfl)
  have h_v407 : R 1 0 4611686018427387900 4611686018695823359 v407 v407 := (r_sub hl (r_add hl h_v28 h_v406 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v407 : sv v407 = sv v28 + sv v406 := e_add h_v28 h_v406 (of_decide_eq_true rfl)
  have h_v408 : R 1 0 4611686018427387904 4611686018695823363 v408 v408 := (r_psel hl h_v405 h_t398_1 h_t397_1 (of_decide_eq_true rfl))
  clear h_v400 h_t398_2 e_t398_2 h_v406
  have e_v408 : v408 = if v405 = 1 then t398.1 else t397.1 := e_psel h_v405 h_t398_1 h_t397_1 (of_decide_eq_true rfl)
  have h_v409 : R 1 0 4611686018427387908 4611686018695823367 v409 v409 := (r_sub hl (r_add hl h_v31 h_v408 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v409 : sv v409 = sv v31 + sv v408 := e_add h_v31 h_v408 (of_decide_eq_true rfl)
  have h_v410 : R 1 0 0 1 v410 v410 := (r_plt hl h_v409 h_v33 (of_decide_eq_true rfl))
  have e_v410 : (v410 = 1 ↔ sv v409 < sv v33) := e_plt h_v409 h_v33 (of_decide_eq_true rfl)
  have h_v411 : R 1 0 4611686018427387908 4611686018695823367 v411 v411 := (r_psel hl h_v410 h_v409 h_v33 (of_decide_eq_true rfl))
  have e_v411 : v411 = if v410 = 1 then v409 else v33 := e_psel h_v410 h_v409 h_v33 (of_decide_eq_true rfl)
  have h_v412 : R 1 0 0 1 v412 v412 := (r_plt hl h_v397 h_v36 (of_decide_eq_true rfl))
  have e_v412 : (v412 = 1 ↔ sv v397 < sv v36) := e_plt h_v397 h_v36 (of_decide_eq_true rfl)
  have h_v413 : R 1 0 0 1 v413 v413 := (r_plt hl h_v38 h_v398 (of_decide_eq_true rfl))
  have e_v413 : (v413 = 1 ↔ sv v38 < sv v398) := e_plt h_v38 h_v398 (of_decide_eq_true rfl)
  have h_v414 : R 1 0 0 1 v414 v414 := (r_land hl h_v412 h_v413 (of_decide_eq_true rfl))
  have e_v414 : (v414 = 1 ↔ v412 = 1 ∧ v413 = 1) := e_land h_v412 h_v413 (of_decide_eq_true rfl)
  have h_v415 : R 1 0 4611686018427387908 4611686018695823367 v415 v415 := (r_psel hl h_v414 h_v33 h_v411 (of_decide_eq_true rfl))
  have e_v415 : v415 = if v414 = 1 then v33 else v411 := e_psel h_v414 h_v33 h_v411 (of_decide_eq_true rfl)
  have h_v416 : R 1 0 0 1 v416 v416 := (r_plt hl h_v407 h_v9 (of_decide_eq_true rfl))
  have e_v416 : (v416 = 1 ↔ sv v407 < sv v9) := e_plt h_v407 h_v9 (of_decide_eq_true rfl)
  have h_v417 : R 1 0 0 1 v417 v417 := (r_sub hl (r_O hl) h_v416 (of_decide_eq_true rfl))
  have e_v417 : (v417 = 1 ↔ ¬v416 = 1) := e_not h_v416 (of_decide_eq_true rfl)
  have h_v418 : R 1 0 0 1 v418 v418 := (r_plt hl h_v9 h_v415 (of_decide_eq_true rfl))
  have e_v418 : (v418 = 1 ↔ sv v9 < sv v415) := e_plt h_v9 h_v415 (of_decide_eq_true rfl)
  have h_v419 : R 1 0 0 1 v419 v419 := (r_sub hl (r_O hl) h_v418 (of_decide_eq_true rfl))
  have e_v419 : (v419 = 1 ↔ ¬v418 = 1) := e_not h_v418 (of_decide_eq_true rfl)
  have h_v420 : R 1 0 0 1 v420 v420 := (r_land hl h_v416 h_v419 (of_decide_eq_true rfl))
  have e_v420 : (v420 = 1 ↔ v416 = 1 ∧ v419 = 1) := e_land h_v416 h_v419 (of_decide_eq_true rfl)
  clear h_v398 h_v405 h_v408 h_v409 h_v410 h_v411 h_v414 h_v419
  have h_v421 : R 1 0 0 1 v421 v421 := (r_land hl h_v416 h_v418 (of_decide_eq_true rfl))
  have e_v421 : (v421 = 1 ↔ v416 = 1 ∧ v418 = 1) := e_land h_v416 h_v418 (of_decide_eq_true rfl)
  have h_v422 : R 1 0 0 1 v422 v422 := (r_land hl h_v66 h_v421 (of_decide_eq_true rfl))
  have e_v422 : (v422 = 1 ↔ v66 = 1 ∧ v421 = 1) := e_land h_v66 h_v421 (of_decide_eq_true rfl)
  have h_v423 : R 1 0 0 1 v423 v423 := (r_sub hl (r_O hl) h_v422 (of_decide_eq_true rfl))
  have e_v423 : (v423 = 1 ↔ ¬v422 = 1) := e_not h_v422 (of_decide_eq_true rfl)
  have h_v424 : R 1 0 0 1 v424 v424 := (r_land hl h_v62 h_v421 (of_decide_eq_true rfl))
  have e_v424 : (v424 = 1 ↔ v62 = 1 ∧ v421 = 1) := e_land h_v62 h_v421 (of_decide_eq_true rfl)
  have h_v425 : R 1 0 0 1 v425 v425 := (r_lor hl h_v420 h_v424 (of_decide_eq_true rfl))
  have e_v425 : (v425 = 1 ↔ v420 = 1 ∨ v424 = 1) := e_lor h_v420 h_v424 (of_decide_eq_true rfl)
  have h_v426 : R 1 0 4611686018427387900 4611686018695823367 v426 v426 := (r_psel hl h_v425 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v426 : v426 = if v425 = 1 then v41 else v29 := e_psel h_v425 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v427 : R 1 0 0 1 v427 v427 := (r_land hl h_v66 h_v417 (of_decide_eq_true rfl))
  have e_v427 : (v427 = 1 ↔ v66 = 1 ∧ v417 = 1) := e_land h_v66 h_v417 (of_decide_eq_true rfl)
  have h_v428 : R 1 0 0 1 v428 v428 := (r_lor hl h_v65 h_v427 (of_decide_eq_true rfl))
  have e_v428 : (v428 = 1 ↔ v65 = 1 ∨ v427 = 1) := e_lor h_v65 h_v427 (of_decide_eq_true rfl)
  have h_v429 : R 1 0 4611686018427387900 4611686018695823367 v429 v429 := (r_psel hl h_v428 h_v415 h_v407 (of_decide_eq_true rfl))
  have e_v429 : v429 = if v428 = 1 then v415 else v407 := e_psel h_v428 h_v415 h_v407 (of_decide_eq_true rfl)
  have h_v430 : R 1 0 0 1 v430 v430 := (r_land hl h_v65 h_v421 (of_decide_eq_true rfl))
  have e_v430 : (v430 = 1 ↔ v65 = 1 ∧ v421 = 1) := e_land h_v65 h_v421 (of_decide_eq_true rfl)
  have h_v431 : R 1 0 0 1 v431 v431 := (r_lor hl h_v420 h_v430 (of_decide_eq_true rfl))
  have e_v431 : (v431 = 1 ↔ v420 = 1 ∨ v430 = 1) := e_lor h_v420 h_v430 (of_decide_eq_true rfl)
  have h_v432 : R 1 0 4611686018427387900 4611686018695823367 v432 v432 := (r_psel hl h_v431 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v432 : v432 = if v431 = 1 then v29 else v41 := e_psel h_v431 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v433 : R 1 0 0 1 v433 v433 := (r_land hl h_v66 h_v420 (of_decide_eq_true rfl))
  clear h_v416 h_v417 h_v418 h_v421 h_v422 h_v424 h_v425 h_v427 h_v428 h_v430 h_v431
  have e_v433 : (v433 = 1 ↔ v66 = 1 ∧ v420 = 1) := e_land h_v66 h_v420 (of_decide_eq_true rfl)
  have h_v434 : R 1 0 0 1 v434 v434 := (r_lor hl h_v65 h_v433 (of_decide_eq_true rfl))
  have e_v434 : (v434 = 1 ↔ v65 = 1 ∨ v433 = 1) := e_lor h_v65 h_v433 (of_decide_eq_true rfl)
  have h_v435 : R 1 0 4611686018427387900 4611686018695823367 v435 v435 := (r_psel hl h_v434 h_v407 h_v415 (of_decide_eq_true rfl))
  have e_v435 : v435 = if v434 = 1 then v407 else v415 := e_psel h_v434 h_v407 h_v415 (of_decide_eq_true rfl)
  have h_v436 : R 1 0 4611686017353646052 4683743616223412273 v436 v436 := (r_smx hl 29 h_v429 h_v426 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v436 : sv v436 = sv v429 * sv v426 := e_smx 29 h_v429 h_v426 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v437 : R 1 0 4611686018427387899 4611686018695823374 v437 v437 := (r_srdF hl h_v436 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v437 : sv v437 = sv v436 / 2 ^ 28 := e_srdF h_v436 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v438 : R 1 0 4611686017353646052 4683743616223412273 v438 v438 := (r_smx hl 29 h_v435 h_v432 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v438 : sv v438 = sv v435 * sv v432 := e_smx 29 h_v435 h_v432 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v439 : R 1 0 4611686018427387900 4611686018695823375 v439 v439 := (r_srdC hl h_v438 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v439 : sv v439 = -((-sv v438) / 2 ^ 28) := e_srdC h_v438 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v440 : R 1 0 0 1 v440 v440 := (r_plt hl h_v18 h_v437 (of_decide_eq_true rfl))
  have e_v440 : (v440 = 1 ↔ sv v18 < sv v437) := e_plt h_v18 h_v437 (of_decide_eq_true rfl)
  have h_v441 : R 1 0 4611686018427387904 4611686052787126264 v441 v441 := (r_add hl (r_pshr1 hl h_v5) h_H61r (of_decide_eq_true rfl))
  have e_v441 : sv v441 = sv v5 / 2 := e_halfF h_v5
  have h_v442 : R 1 0 0 1 v442 v442 := (r_plt hl h_v18 h_v441 (of_decide_eq_true rfl))
  have e_v442 : (v442 = 1 ↔ sv v18 < sv v441) := e_plt h_v18 h_v441 (of_decide_eq_true rfl)
  have h_v443 : R 1 0 0 1 v443 v443 := (r_land hl h_v401 h_v442 (of_decide_eq_true rfl))
  have e_v443 : (v443 = 1 ↔ v401 = 1 ∧ v442 = 1) := e_land h_v401 h_v442 (of_decide_eq_true rfl)
  have h_t441_1 : R 1 0 4611686018427387904 4611686018695823363 t441.1 t441.1 := r_sc1 hl h_v441 (of_decide_eq_true rfl)
  have h_t441_2 : R 1 0 4611686018158952445 4611686018695823363 t441.2 t441.2 := r_sc2 hl h_v441 (of_decide_eq_true rfl)
  have e_t441_1 : sv t441.1 = (sc28pS (scArg v441)).1 := e_sc1 h_v441 (of_decide_eq_true rfl)
  have e_t441_2 : sv t441.2 = (sc28pS (scArg v441)).2 := e_sc2 h_v441 (of_decide_eq_true rfl)
  clear h_v5 h_v401 h_v407 h_v415 h_v420 h_v426 h_v429 h_v432 h_v433 h_v434 h_v435 h_v436 h_v438 h_v442 h_t441_2 e_t441_2
  have h_v457 : R 1 0 0 1 v457 v457 := (r_plt hl h_t441_1 h_t398_1 (of_decide_eq_true rfl))
  have e_v457 : (v457 = 1 ↔ sv t441.1 < sv t398.1) := e_plt h_t441_1 h_t398_1 (of_decide_eq_true rfl)
  have h_v458 : R 1 0 4611686018427387904 4611686018695823363 v458 v458 := (r_psel hl h_v457 h_t441_1 h_t398_1 (of_decide_eq_true rfl))
  have e_v458 : v458 = if v457 = 1 then t441.1 else t398.1 := e_psel h_v457 h_t441_1 h_t398_1 (of_decide_eq_true rfl)
  have h_v459 : R 1 0 4611686018427387900 4611686018695823359 v459 v459 := (r_sub hl (r_add hl h_v28 h_v458 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v459 : sv v459 = sv v28 + sv v458 := e_add h_v28 h_v458 (of_decide_eq_true rfl)
  have h_v460 : R 1 0 4611686018427387904 4611686018695823363 v460 v460 := (r_psel hl h_v457 h_t398_1 h_t441_1 (of_decide_eq_true rfl))
  have e_v460 : v460 = if v457 = 1 then t398.1 else t441.1 := e_psel h_v457 h_t398_1 h_t441_1 (of_decide_eq_true rfl)
  have h_v461 : R 1 0 4611686018427387908 4611686018695823367 v461 v461 := (r_sub hl (r_add hl h_v31 h_v460 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v461 : sv v461 = sv v31 + sv v460 := e_add h_v31 h_v460 (of_decide_eq_true rfl)
  have h_v462 : R 1 0 0 1 v462 v462 := (r_plt hl h_v461 h_v33 (of_decide_eq_true rfl))
  have e_v462 : (v462 = 1 ↔ sv v461 < sv v33) := e_plt h_v461 h_v33 (of_decide_eq_true rfl)
  have h_v463 : R 1 0 4611686018427387908 4611686018695823367 v463 v463 := (r_psel hl h_v462 h_v461 h_v33 (of_decide_eq_true rfl))
  have e_v463 : v463 = if v462 = 1 then v461 else v33 := e_psel h_v462 h_v461 h_v33 (of_decide_eq_true rfl)
  have h_v464 : R 1 0 0 1 v464 v464 := (r_plt hl h_v441 h_v36 (of_decide_eq_true rfl))
  have e_v464 : (v464 = 1 ↔ sv v441 < sv v36) := e_plt h_v441 h_v36 (of_decide_eq_true rfl)
  have h_v465 : R 1 0 0 1 v465 v465 := (r_land hl h_v413 h_v464 (of_decide_eq_true rfl))
  have e_v465 : (v465 = 1 ↔ v413 = 1 ∧ v464 = 1) := e_land h_v413 h_v464 (of_decide_eq_true rfl)
  have h_v466 : R 1 0 4611686018427387908 4611686018695823367 v466 v466 := (r_psel hl h_v465 h_v33 h_v463 (of_decide_eq_true rfl))
  have e_v466 : v466 = if v465 = 1 then v33 else v463 := e_psel h_v465 h_v33 h_v463 (of_decide_eq_true rfl)
  have h_v467 : R 1 0 0 1 v467 v467 := (r_plt hl h_v459 h_v9 (of_decide_eq_true rfl))
  have e_v467 : (v467 = 1 ↔ sv v459 < sv v9) := e_plt h_v459 h_v9 (of_decide_eq_true rfl)
  have h_v469 : R 1 0 0 1 v469 v469 := (r_plt hl h_v9 h_v466 (of_decide_eq_true rfl))
  have e_v469 : (v469 = 1 ↔ sv v9 < sv v466) := e_plt h_v9 h_v466 (of_decide_eq_true rfl)
  have h_v472 : R 1 0 0 1 v472 v472 := (r_land hl h_v467 h_v469 (of_decide_eq_true rfl))
  clear h_t398_1 h_v413 h_v441 h_t441_1 h_v457 h_v458 h_v459 h_v460 h_v461 h_v462 h_v463 h_v464 h_v465 h_v466
  have e_v472 : (v472 = 1 ↔ v467 = 1 ∧ v469 = 1) := e_land h_v467 h_v469 (of_decide_eq_true rfl)
  have h_v473 : R 1 0 0 1 v473 v473 := (r_land hl h_v138 h_v472 (of_decide_eq_true rfl))
  have e_v473 : (v473 = 1 ↔ v138 = 1 ∧ v472 = 1) := e_land h_v138 h_v472 (of_decide_eq_true rfl)
  have h_v474 : R 1 0 0 1 v474 v474 := (r_sub hl (r_O hl) h_v473 (of_decide_eq_true rfl))
  have e_v474 : (v474 = 1 ↔ ¬v473 = 1) := e_not h_v473 (of_decide_eq_true rfl)
  have h_v581 : R 1 0 4611686018427387904 4611686052787126264 v581 v581 := (r_add hl (r_pshr1 hl (r_add hl h_v4 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v581 : sv v581 = (sv v4 + 1) / 2 := e_halfC h_v4 (of_decide_eq_true rfl)
  have h_v582 : R 1 0 0 1 v582 v582 := (r_plt hl h_v20 h_v581 (of_decide_eq_true rfl))
  have e_v582 : (v582 = 1 ↔ sv v20 < sv v581) := e_plt h_v20 h_v581 (of_decide_eq_true rfl)
  have h_v583 : R 1 0 0 1 v583 v583 := (r_sub hl (r_O hl) h_v582 (of_decide_eq_true rfl))
  have e_v583 : (v583 = 1 ↔ ¬v582 = 1) := e_not h_v582 (of_decide_eq_true rfl)
  have h_v584 : R 1 0 0 1 v584 v584 := (r_land hl h_v399 h_v583 (of_decide_eq_true rfl))
  have e_v584 : (v584 = 1 ↔ v399 = 1 ∧ v583 = 1) := e_land h_v399 h_v583 (of_decide_eq_true rfl)
  have h_v592 : R 1 0 4611686018158952449 4611686018695823367 v592 v592 := (r_sub hl (r_add hl h_v31 h_t397_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v592 : sv v592 = sv v31 + sv t397.2 := e_add h_v31 h_t397_2 (of_decide_eq_true rfl)
  have h_v593 : R 1 0 0 1 v593 v593 := (r_plt hl h_v592 h_v33 (of_decide_eq_true rfl))
  have e_v593 : (v593 = 1 ↔ sv v592 < sv v33) := e_plt h_v592 h_v33 (of_decide_eq_true rfl)
  have h_v594 : R 1 0 4611686018158952449 4611686018695823367 v594 v594 := (r_psel hl h_v593 h_v592 h_v33 (of_decide_eq_true rfl))
  have e_v594 : v594 = if v593 = 1 then v592 else v33 := e_psel h_v593 h_v592 h_v33 (of_decide_eq_true rfl)
  have h_v595 : R 1 0 0 1 v595 v595 := (r_plt hl h_v397 h_v104 (of_decide_eq_true rfl))
  have e_v595 : (v595 = 1 ↔ sv v397 < sv v104) := e_plt h_v397 h_v104 (of_decide_eq_true rfl)
  have h_v596 : R 1 0 4611686018158952449 4611686018695823367 v596 v596 := (r_psel hl h_v595 h_v33 h_v594 (of_decide_eq_true rfl))
  have e_v596 : v596 = if v595 = 1 then v33 else v594 := e_psel h_v595 h_v33 h_v594 (of_decide_eq_true rfl)
  have h_t581_1 : R 1 0 4611686018427387904 4611686018695823363 t581.1 t581.1 := r_sc1 hl h_v581 (of_decide_eq_true rfl)
  have h_t581_2 : R 1 0 4611686018158952445 4611686018695823363 t581.2 t581.2 := r_sc2 hl h_v581 (of_decide_eq_true rfl)
  clear h_v4 h_v397 h_v399 h_t397_2 h_v467 h_v469 h_v472 h_v473 h_v582 h_v583 h_v592 h_v593 h_v594 h_v595 h_t581_2
  have e_t581_1 : sv t581.1 = (sc28pS (scArg v581)).1 := e_sc1 h_v581 (of_decide_eq_true rfl)
  have e_t581_2 : sv t581.2 = (sc28pS (scArg v581)).2 := e_sc2 h_v581 (of_decide_eq_true rfl)
  have h_v598 : R 1 0 0 1 v598 v598 := (r_plt hl h_t397_1 h_t581_1 (of_decide_eq_true rfl))
  have e_v598 : (v598 = 1 ↔ sv t397.1 < sv t581.1) := e_plt h_t397_1 h_t581_1 (of_decide_eq_true rfl)
  have h_v599 : R 1 0 4611686018427387904 4611686018695823363 v599 v599 := (r_psel hl h_v598 h_t397_1 h_t581_1 (of_decide_eq_true rfl))
  have e_v599 : v599 = if v598 = 1 then t397.1 else t581.1 := e_psel h_v598 h_t397_1 h_t581_1 (of_decide_eq_true rfl)
  have h_v600 : R 1 0 4611686018427387900 4611686018695823359 v600 v600 := (r_sub hl (r_add hl h_v28 h_v599 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v600 : sv v600 = sv v28 + sv v599 := e_add h_v28 h_v599 (of_decide_eq_true rfl)
  have h_v601 : R 1 0 4611686018427387904 4611686018695823363 v601 v601 := (r_psel hl h_v598 h_t581_1 h_t397_1 (of_decide_eq_true rfl))
  have e_v601 : v601 = if v598 = 1 then t581.1 else t397.1 := e_psel h_v598 h_t581_1 h_t397_1 (of_decide_eq_true rfl)
  have h_v602 : R 1 0 4611686018427387908 4611686018695823367 v602 v602 := (r_sub hl (r_add hl h_v31 h_v601 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v602 : sv v602 = sv v31 + sv v601 := e_add h_v31 h_v601 (of_decide_eq_true rfl)
  have h_v603 : R 1 0 0 1 v603 v603 := (r_plt hl h_v602 h_v33 (of_decide_eq_true rfl))
  have e_v603 : (v603 = 1 ↔ sv v602 < sv v33) := e_plt h_v602 h_v33 (of_decide_eq_true rfl)
  have h_v604 : R 1 0 4611686018427387908 4611686018695823367 v604 v604 := (r_psel hl h_v603 h_v602 h_v33 (of_decide_eq_true rfl))
  have e_v604 : v604 = if v603 = 1 then v602 else v33 := e_psel h_v603 h_v602 h_v33 (of_decide_eq_true rfl)
  have h_v605 : R 1 0 0 1 v605 v605 := (r_plt hl h_v38 h_v581 (of_decide_eq_true rfl))
  have e_v605 : (v605 = 1 ↔ sv v38 < sv v581) := e_plt h_v38 h_v581 (of_decide_eq_true rfl)
  have h_v606 : R 1 0 0 1 v606 v606 := (r_land hl h_v412 h_v605 (of_decide_eq_true rfl))
  have e_v606 : (v606 = 1 ↔ v412 = 1 ∧ v605 = 1) := e_land h_v412 h_v605 (of_decide_eq_true rfl)
  have h_v607 : R 1 0 4611686018427387908 4611686018695823367 v607 v607 := (r_psel hl h_v606 h_v33 h_v604 (of_decide_eq_true rfl))
  have e_v607 : v607 = if v606 = 1 then v33 else v604 := e_psel h_v606 h_v33 h_v604 (of_decide_eq_true rfl)
  have h_v608 : R 1 0 0 1 v608 v608 := (r_plt hl h_v600 h_v9 (of_decide_eq_true rfl))
  have e_v608 : (v608 = 1 ↔ sv v600 < sv v9) := e_plt h_v600 h_v9 (of_decide_eq_true rfl)
  have h_v609 : R 1 0 0 1 v609 v609 := (r_sub hl (r_O hl) h_v608 (of_decide_eq_true rfl))
  clear h_t397_1 h_v412 h_v581 h_t581_1 e_t581_2 h_v598 h_v599 h_v601 h_v602 h_v603 h_v604 h_v605 h_v606
  have e_v609 : (v609 = 1 ↔ ¬v608 = 1) := e_not h_v608 (of_decide_eq_true rfl)
  have h_v610 : R 1 0 0 1 v610 v610 := (r_plt hl h_v9 h_v607 (of_decide_eq_true rfl))
  have e_v610 : (v610 = 1 ↔ sv v9 < sv v607) := e_plt h_v9 h_v607 (of_decide_eq_true rfl)
  have h_v611 : R 1 0 0 1 v611 v611 := (r_sub hl (r_O hl) h_v610 (of_decide_eq_true rfl))
  have e_v611 : (v611 = 1 ↔ ¬v610 = 1) := e_not h_v610 (of_decide_eq_true rfl)
  have h_v612 : R 1 0 0 1 v612 v612 := (r_land hl h_v608 h_v611 (of_decide_eq_true rfl))
  have e_v612 : (v612 = 1 ↔ v608 = 1 ∧ v611 = 1) := e_land h_v608 h_v611 (of_decide_eq_true rfl)
  have h_v613 : R 1 0 0 1 v613 v613 := (r_land hl h_v608 h_v610 (of_decide_eq_true rfl))
  have e_v613 : (v613 = 1 ↔ v608 = 1 ∧ v610 = 1) := e_land h_v608 h_v610 (of_decide_eq_true rfl)
  have h_v614 : R 1 0 0 1 v614 v614 := (r_land hl h_v138 h_v613 (of_decide_eq_true rfl))
  have e_v614 : (v614 = 1 ↔ v138 = 1 ∧ v613 = 1) := e_land h_v138 h_v613 (of_decide_eq_true rfl)
  have h_v615 : R 1 0 0 1 v615 v615 := (r_sub hl (r_O hl) h_v614 (of_decide_eq_true rfl))
  have e_v615 : (v615 = 1 ↔ ¬v614 = 1) := e_not h_v614 (of_decide_eq_true rfl)
  have h_v616 : R 1 0 0 1 v616 v616 := (r_land hl h_v134 h_v613 (of_decide_eq_true rfl))
  have e_v616 : (v616 = 1 ↔ v134 = 1 ∧ v613 = 1) := e_land h_v134 h_v613 (of_decide_eq_true rfl)
  have h_v617 : R 1 0 0 1 v617 v617 := (r_lor hl h_v612 h_v616 (of_decide_eq_true rfl))
  have e_v617 : (v617 = 1 ↔ v612 = 1 ∨ v616 = 1) := e_lor h_v612 h_v616 (of_decide_eq_true rfl)
  have h_v618 : R 1 0 4611686018158952441 4611686018695823367 v618 v618 := (r_psel hl h_v617 h_v106 h_v99 (of_decide_eq_true rfl))
  have e_v618 : v618 = if v617 = 1 then v106 else v99 := e_psel h_v617 h_v106 h_v99 (of_decide_eq_true rfl)
  have h_v619 : R 1 0 0 1 v619 v619 := (r_land hl h_v138 h_v609 (of_decide_eq_true rfl))
  have e_v619 : (v619 = 1 ↔ v138 = 1 ∧ v609 = 1) := e_land h_v138 h_v609 (of_decide_eq_true rfl)
  have h_v620 : R 1 0 0 1 v620 v620 := (r_lor hl h_v137 h_v619 (of_decide_eq_true rfl))
  have e_v620 : (v620 = 1 ↔ v137 = 1 ∨ v619 = 1) := e_lor h_v137 h_v619 (of_decide_eq_true rfl)
  have h_v621 : R 1 0 4611686018427387900 4611686018695823367 v621 v621 := (r_psel hl h_v620 h_v607 h_v600 (of_decide_eq_true rfl))
  have e_v621 : v621 = if v620 = 1 then v607 else v600 := e_psel h_v620 h_v607 h_v600 (of_decide_eq_true rfl)
  clear h_v134 h_v608 h_v609 h_v610 h_v611 h_v614 h_v616 h_v617 h_v619 h_v620
  have h_v622 : R 1 0 0 1 v622 v622 := (r_land hl h_v137 h_v613 (of_decide_eq_true rfl))
  have e_v622 : (v622 = 1 ↔ v137 = 1 ∧ v613 = 1) := e_land h_v137 h_v613 (of_decide_eq_true rfl)
  have h_v623 : R 1 0 0 1 v623 v623 := (r_lor hl h_v612 h_v622 (of_decide_eq_true rfl))
  have e_v623 : (v623 = 1 ↔ v612 = 1 ∨ v622 = 1) := e_lor h_v612 h_v622 (of_decide_eq_true rfl)
  have h_v624 : R 1 0 4611686018158952441 4611686018695823367 v624 v624 := (r_psel hl h_v623 h_v99 h_v106 (of_decide_eq_true rfl))
  have e_v624 : v624 = if v623 = 1 then v99 else v106 := e_psel h_v623 h_v99 h_v106 (of_decide_eq_true rfl)
  have h_v625 : R 1 0 0 1 v625 v625 := (r_land hl h_v138 h_v612 (of_decide_eq_true rfl))
  have e_v625 : (v625 = 1 ↔ v138 = 1 ∧ v612 = 1) := e_land h_v138 h_v612 (of_decide_eq_true rfl)
  have h_v626 : R 1 0 0 1 v626 v626 := (r_lor hl h_v137 h_v625 (of_decide_eq_true rfl))
  have e_v626 : (v626 = 1 ↔ v137 = 1 ∨ v625 = 1) := e_lor h_v137 h_v625 (of_decide_eq_true rfl)
  have h_v627 : R 1 0 4611686018427387900 4611686018695823367 v627 v627 := (r_psel hl h_v626 h_v600 h_v607 (of_decide_eq_true rfl))
  have e_v627 : v627 = if v626 = 1 then v600 else v607 := e_psel h_v626 h_v600 h_v607 (of_decide_eq_true rfl)
  have h_v628 : R 1 0 4539628420631363535 4683743616223412273 v628 v628 := (r_smx hl 29 h_v621 h_v618 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v628 : sv v628 = sv v621 * sv v618 := e_smx 29 h_v621 h_v618 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v629 : R 1 0 4611686018158952433 4611686018695823374 v629 v629 := (r_srdF hl h_v628 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v629 : sv v629 = sv v628 / 2 ^ 28 := e_srdF h_v628 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v630 : R 1 0 4539628420631363535 4683743616223412273 v630 v630 := (r_smx hl 29 h_v627 h_v624 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v630 : sv v630 = sv v627 * sv v624 := e_smx 29 h_v627 h_v624 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v631 : R 1 0 4611686018158952434 4611686018695823375 v631 v631 := (r_srdC hl h_v630 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v631 : sv v631 = -((-sv v630) / 2 ^ 28) := e_srdC h_v630 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v632 : R 1 0 0 1 v632 v632 := (r_plt hl h_v9 h_v629 (of_decide_eq_true rfl))
  have e_v632 : (v632 = 1 ↔ sv v9 < sv v629) := e_plt h_v9 h_v629 (of_decide_eq_true rfl)
  have h_v633 : R 1 0 0 1 v633 v633 := (r_sub hl (r_O hl) h_v632 (of_decide_eq_true rfl))
  have e_v633 : (v633 = 1 ↔ ¬v632 = 1) := e_not h_v632 (of_decide_eq_true rfl)
  have h_v636 : R 1 0 0 1 v636 v636 := (r_plt hl h_v596 h_v9 (of_decide_eq_true rfl))
  clear h_v99 h_v106 h_v137 h_v138 h_v600 h_v607 h_v612 h_v613 h_v618 h_v621 h_v622 h_v623 h_v624 h_v625 h_v626 h_v627 h_v628 h_v630 h_v632
  have e_v636 : (v636 = 1 ↔ sv v596 < sv v9) := e_plt h_v596 h_v9 (of_decide_eq_true rfl)
  have h_v637 : R 1 0 4611686018158952433 4611686018695823375 v637 v637 := (r_psel hl h_v636 h_v631 h_v629 (of_decide_eq_true rfl))
  have e_v637 : v637 = if v636 = 1 then v631 else v629 := e_psel h_v636 h_v631 h_v629 (of_decide_eq_true rfl)
  have h_v679 : R 1 0 4611686018158952441 4611686018695823359 v679 v679 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v596 (of_decide_eq_true rfl))
  have e_v679 : sv v679 = sv v9 - sv v596 := e_sub h_v9 h_v596 (of_decide_eq_true rfl)
  have h_v680 : R 1 0 4611686018158952441 4611686018695823367 v680 v680 := (r_psel hl h_v636 h_v679 h_v596 (of_decide_eq_true rfl))
  have e_v680 : v680 = if v636 = 1 then v679 else v596 := e_psel h_v636 h_v679 h_v596 (of_decide_eq_true rfl)
  have h_v681 : R 1 0 4611686018427387904 4611686019501129727 v681 v681 := (r1_hxa hb_H0 32 (of_decide_eq_true rfl))
  have e_v681 : sv v681 = ((H0 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H0 32 (of_decide_eq_true rfl)
  have h_t681_1 : R 1 0 4611686018427387904 4611686018695823363 t681.1 t681.1 := r_sc1 hl h_v681 (of_decide_eq_true rfl)
  have h_t681_2 : R 1 0 4611686018158952445 4611686018695823363 t681.2 t681.2 := r_sc2 hl h_v681 (of_decide_eq_true rfl)
  have e_t681_1 : sv t681.1 = (sc28pS (scArg v681)).1 := e_sc1 h_v681 (of_decide_eq_true rfl)
  have e_t681_2 : sv t681.2 = (sc28pS (scArg v681)).2 := e_sc2 h_v681 (of_decide_eq_true rfl)
  have h_v683 : R 1 0 4611686018158952441 4611686018695823359 v683 v683 := (r_sub hl (r_add hl h_v28 h_t681_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v683 : sv v683 = sv v28 + sv t681.2 := e_add h_v28 h_t681_2 (of_decide_eq_true rfl)
  have h_v684 : R 1 0 0 1 v684 v684 := (r_plt hl h_v683 h_v94 (of_decide_eq_true rfl))
  have e_v684 : (v684 = 1 ↔ sv v683 < sv v94) := e_plt h_v683 h_v94 (of_decide_eq_true rfl)
  have h_v685 : R 1 0 4611686018158952441 4611686018695823359 v685 v685 := (r_psel hl h_v684 h_v94 h_v683 (of_decide_eq_true rfl))
  have e_v685 : v685 = if v684 = 1 then v94 else v683 := e_psel h_v684 h_v94 h_v683 (of_decide_eq_true rfl)
  have h_v686 : R 1 0 4611686018158952449 4611686018695823367 v686 v686 := (r_sub hl (r_add hl h_v31 h_t681_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v686 : sv v686 = sv v31 + sv t681.2 := e_add h_v31 h_t681_2 (of_decide_eq_true rfl)
  have h_v687 : R 1 0 0 1 v687 v687 := (r_plt hl h_v686 h_v33 (of_decide_eq_true rfl))
  have e_v687 : (v687 = 1 ↔ sv v686 < sv v33) := e_plt h_v686 h_v33 (of_decide_eq_true rfl)
  have h_v688 : R 1 0 4611686018158952449 4611686018695823367 v688 v688 := (r_psel hl h_v687 h_v686 h_v33 (of_decide_eq_true rfl))
  have e_v688 : v688 = if v687 = 1 then v686 else v33 := e_psel h_v687 h_v686 h_v33 (of_decide_eq_true rfl)
  clear h_v596 h_v629 h_v631 h_v679 h_t681_2 h_v683 h_v684 h_v686 h_v687
  have h_v690 : R 1 0 4611686018427387908 4611686018695823367 v690 v690 := (r_sub hl (r_add hl h_v31 h_t681_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v690 : sv v690 = sv v31 + sv t681.1 := e_add h_v31 h_t681_1 (of_decide_eq_true rfl)
  have h_v691 : R 1 0 0 1 v691 v691 := (r_plt hl h_v690 h_v33 (of_decide_eq_true rfl))
  have e_v691 : (v691 = 1 ↔ sv v690 < sv v33) := e_plt h_v690 h_v33 (of_decide_eq_true rfl)
  have h_v692 : R 1 0 4611686018427387908 4611686018695823367 v692 v692 := (r_psel hl h_v691 h_v690 h_v33 (of_decide_eq_true rfl))
  have e_v692 : v692 = if v691 = 1 then v690 else v33 := e_psel h_v691 h_v690 h_v33 (of_decide_eq_true rfl)
  have h_v693 : R 1 0 4611686018427387900 4611686018695823359 v693 v693 := (r_sub hl (r_add hl h_v28 h_t681_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v693 : sv v693 = sv v28 + sv t681.1 := e_add h_v28 h_t681_1 (of_decide_eq_true rfl)
  have h_v694 : R 1 0 4611686018158952441 4611686018695823367 v694 v694 := (r_psel hl h_v636 h_v685 h_v688 (of_decide_eq_true rfl))
  have e_v694 : v694 = if v636 = 1 then v685 else v688 := e_psel h_v636 h_v685 h_v688 (of_decide_eq_true rfl)
  have h_v695 : R 1 0 4611686018427387900 4611686018695823367 v695 v695 := (r_psel hl h_v636 h_v692 h_v693 (of_decide_eq_true rfl))
  have e_v695 : v695 = if v636 = 1 then v692 else v693 := e_psel h_v636 h_v692 h_v693 (of_decide_eq_true rfl)
  have h_v696 : R 1 0 4539628418483879831 4683743618370895977 v696 v696 := (r_smx hl 29 h_v637 h_v695 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v696 : sv v696 = sv v637 * sv v695 := e_smx 29 h_v637 h_v695 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v697 : R 1 0 4539628420631363535 4683743616223412273 v697 v697 := (r_smx hl 29 h_v694 h_v680 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v697 : sv v697 = sv v694 * sv v680 := e_smx 29 h_v694 h_v680 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v698 : R 1 0 0 1 v698 v698 := (r_plt hl h_v697 h_v696 (of_decide_eq_true rfl))
  have e_v698 : (v698 = 1 ↔ sv v697 < sv v696) := e_plt h_v697 h_v696 (of_decide_eq_true rfl)
  have h_v699 : R 1 0 0 1 v699 v699 := (r_sub hl (r_O hl) h_v698 (of_decide_eq_true rfl))
  have e_v699 : (v699 = 1 ↔ ¬v698 = 1) := e_not h_v698 (of_decide_eq_true rfl)
  have h_v700 : R 1 0 0 1 v700 v700 := (r_plt hl h_v696 h_v697 (of_decide_eq_true rfl))
  have e_v700 : (v700 = 1 ↔ sv v696 < sv v697) := e_plt h_v696 h_v697 (of_decide_eq_true rfl)
  have h_v701 : R 1 0 0 1 v701 v701 := (r_sub hl (r_O hl) h_v700 (of_decide_eq_true rfl))
  have e_v701 : (v701 = 1 ↔ ¬v700 = 1) := e_not h_v700 (of_decide_eq_true rfl)
  have h_v702 : R 1 0 0 1 v702 v702 := (r_plt hl h_v9 h_v681 (of_decide_eq_true rfl))
  clear h_v637 h_v680 h_t681_1 h_v688 h_v690 h_v691 h_v692 h_v693 h_v694 h_v695 h_v696 h_v697 h_v698 h_v700
  have e_v702 : (v702 = 1 ↔ sv v9 < sv v681) := e_plt h_v9 h_v681 (of_decide_eq_true rfl)
  have h_v703 : R 1 0 0 1 v703 v703 := (r_sub hl (r_O hl) h_v702 (of_decide_eq_true rfl))
  have e_v703 : (v703 = 1 ↔ ¬v702 = 1) := e_not h_v702 (of_decide_eq_true rfl)
  have h_v704 : R 1 0 0 1 v704 v704 := (r_plt hl h_v195 h_v681 (of_decide_eq_true rfl))
  have e_v704 : (v704 = 1 ↔ sv v195 < sv v681) := e_plt h_v195 h_v681 (of_decide_eq_true rfl)
  have h_v705 : R 1 0 0 1 v705 v705 := (r_sub hl (r_O hl) h_v704 (of_decide_eq_true rfl))
  have e_v705 : (v705 = 1 ↔ ¬v704 = 1) := e_not h_v704 (of_decide_eq_true rfl)
  have h_v706 : R 1 0 0 1 v706 v706 := (r_plt hl h_v18 h_v685 (of_decide_eq_true rfl))
  have e_v706 : (v706 = 1 ↔ sv v18 < sv v685) := e_plt h_v18 h_v685 (of_decide_eq_true rfl)
  have h_v707 : R 1 0 0 1 v707 v707 := (r_land hl h_v699 h_v706 (of_decide_eq_true rfl))
  have e_v707 : (v707 = 1 ↔ v699 = 1 ∧ v706 = 1) := e_land h_v699 h_v706 (of_decide_eq_true rfl)
  have h_v708 : R 1 0 0 1 v708 v708 := (r_land hl h_v705 h_v707 (of_decide_eq_true rfl))
  have e_v708 : (v708 = 1 ↔ v705 = 1 ∧ v707 = 1) := e_land h_v705 h_v707 (of_decide_eq_true rfl)
  have h_v709 : R 1 0 0 1 v709 v709 := (r_lor hl h_v703 h_v708 (of_decide_eq_true rfl))
  have e_v709 : (v709 = 1 ↔ v703 = 1 ∨ v708 = 1) := e_lor h_v703 h_v708 (of_decide_eq_true rfl)
  have h_v710 : R 1 0 0 1 v710 v710 := (r_plt hl h_v681 h_v202 (of_decide_eq_true rfl))
  have e_v710 : (v710 = 1 ↔ sv v681 < sv v202) := e_plt h_v681 h_v202 (of_decide_eq_true rfl)
  have h_v711 : R 1 0 0 1 v711 v711 := (r_sub hl (r_O hl) h_v710 (of_decide_eq_true rfl))
  have e_v711 : (v711 = 1 ↔ ¬v710 = 1) := e_not h_v710 (of_decide_eq_true rfl)
  have h_v712 : R 1 0 0 1 v712 v712 := (r_lor hl h_v701 h_v711 (of_decide_eq_true rfl))
  have e_v712 : (v712 = 1 ↔ v701 = 1 ∨ v711 = 1) := e_lor h_v701 h_v711 (of_decide_eq_true rfl)
  have h_v713 : R 1 0 0 1 v713 v713 := (r_land hl h_v636 h_v709 (of_decide_eq_true rfl))
  have e_v713 : (v713 = 1 ↔ v636 = 1 ∧ v709 = 1) := e_land h_v636 h_v709 (of_decide_eq_true rfl)
  have h_v714 : R 1 0 0 1 v714 v714 := (r_sub hl (r_O hl) h_v636 (of_decide_eq_true rfl))
  have e_v714 : (v714 = 1 ↔ ¬v636 = 1) := e_not h_v636 (of_decide_eq_true rfl)
  clear h_v685 h_v699 h_v701 h_v702 h_v703 h_v704 h_v705 h_v706 h_v707 h_v708 h_v709 h_v710 h_v711
  have h_v715 : R 1 0 0 1 v715 v715 := (r_land hl h_v712 h_v714 (of_decide_eq_true rfl))
  have e_v715 : (v715 = 1 ↔ v712 = 1 ∧ v714 = 1) := e_land h_v712 h_v714 (of_decide_eq_true rfl)
  have h_v716 : R 1 0 0 1 v716 v716 := (r_lor hl h_v713 h_v715 (of_decide_eq_true rfl))
  have e_v716 : (v716 = 1 ↔ v713 = 1 ∨ v715 = 1) := e_lor h_v713 h_v715 (of_decide_eq_true rfl)
  have h_v717 : R 1 0 4611686017353646081 4611686018427387904 v717 v717 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v681 (of_decide_eq_true rfl))
  have e_v717 : sv v717 = sv v9 - sv v681 := e_sub h_v9 h_v681 (of_decide_eq_true rfl)
  have h_v718 : R 1 0 4611686017353646081 4611686019501129727 v718 v718 := (r_psel hl h_v636 h_v717 h_v681 (of_decide_eq_true rfl))
  have e_v718 : v718 = if v636 = 1 then v717 else v681 := e_psel h_v636 h_v717 h_v681 (of_decide_eq_true rfl)
  have h_v719 : R 1 0 4611686017353646081 4611686019501129727 v719 v719 := (r_psel hl h_v716 h_v718 h_v202 (of_decide_eq_true rfl))
  have e_v719 : v719 = if v716 = 1 then v718 else v202 := e_psel h_v716 h_v718 h_v202 (of_decide_eq_true rfl)
  have h_v721 : R 1 0 4611686017353646081 4611686019501129727 v721 v721 := (r_psel hl h_v633 h_v202 h_v719 (of_decide_eq_true rfl))
  have e_v721 : v721 = if v633 = 1 then v202 else v719 := e_psel h_v633 h_v202 h_v719 (of_decide_eq_true rfl)
  have h_v722 : R 1 0 4611686018427387904 4611686052787126264 v722 v722 := (r_add hl (r_pshr1 hl h_v7) h_H61r (of_decide_eq_true rfl))
  have e_v722 : sv v722 = sv v7 / 2 := e_halfF h_v7
  have h_v723 : R 1 0 4611686018427387904 4611686052787126264 v723 v723 := (r_psel hl h_v16 h_v722 h_v195 (of_decide_eq_true rfl))
  have e_v723 : v723 = if v16 = 1 then v722 else v195 := e_psel h_v16 h_v722 h_v195 (of_decide_eq_true rfl)
  have h_v724 : R 1 0 4611686018427387904 4611686052787126264 v724 v724 := (r_add hl (r_pshr1 hl (r_add hl h_v7 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v724 : sv v724 = (sv v7 + 1) / 2 := e_halfC h_v7 (of_decide_eq_true rfl)
  have h_v725 : R 1 0 0 1 v725 v725 := (r_plt hl h_v18 h_v723 (of_decide_eq_true rfl))
  have e_v725 : (v725 = 1 ↔ sv v18 < sv v723) := e_plt h_v18 h_v723 (of_decide_eq_true rfl)
  have h_v726 : R 1 0 0 1 v726 v726 := (r_plt hl h_v20 h_v724 (of_decide_eq_true rfl))
  have e_v726 : (v726 = 1 ↔ sv v20 < sv v724) := e_plt h_v20 h_v724 (of_decide_eq_true rfl)
  have h_v727 : R 1 0 0 1 v727 v727 := (r_sub hl (r_O hl) h_v726 (of_decide_eq_true rfl))
  have e_v727 : (v727 = 1 ↔ ¬v726 = 1) := e_not h_v726 (of_decide_eq_true rfl)
  have h_v728 : R 1 0 0 1 v728 v728 := (r_land hl h_v725 h_v727 (of_decide_eq_true rfl))
  clear h_H61r h_v7 h_v16 h_v195 h_v202 h_v633 h_v636 h_v681 h_v712 h_v713 h_v714 h_v715 h_v716 h_v717 h_v718 h_v719 h_v722 h_v726
  have e_v728 : (v728 = 1 ↔ v725 = 1 ∧ v727 = 1) := e_land h_v725 h_v727 (of_decide_eq_true rfl)
  have h_t723_1 : R 1 0 4611686018427387904 4611686018695823363 t723.1 t723.1 := r_sc1 hl h_v723 (of_decide_eq_true rfl)
  have h_t723_2 : R 1 0 4611686018158952445 4611686018695823363 t723.2 t723.2 := r_sc2 hl h_v723 (of_decide_eq_true rfl)
  have e_t723_1 : sv t723.1 = (sc28pS (scArg v723)).1 := e_sc1 h_v723 (of_decide_eq_true rfl)
  have e_t723_2 : sv t723.2 = (sc28pS (scArg v723)).2 := e_sc2 h_v723 (of_decide_eq_true rfl)
  have h_t724_1 : R 1 0 4611686018427387904 4611686018695823363 t724.1 t724.1 := r_sc1 hl h_v724 (of_decide_eq_true rfl)
  have h_t724_2 : R 1 0 4611686018158952445 4611686018695823363 t724.2 t724.2 := r_sc2 hl h_v724 (of_decide_eq_true rfl)
  have e_t724_1 : sv t724.1 = (sc28pS (scArg v724)).1 := e_sc1 h_v724 (of_decide_eq_true rfl)
  have e_t724_2 : sv t724.2 = (sc28pS (scArg v724)).2 := e_sc2 h_v724 (of_decide_eq_true rfl)
  have h_v731 : R 1 0 0 1 v731 v731 := (r_plt hl h_t723_1 h_t724_1 (of_decide_eq_true rfl))
  have e_v731 : (v731 = 1 ↔ sv t723.1 < sv t724.1) := e_plt h_t723_1 h_t724_1 (of_decide_eq_true rfl)
  have h_v732 : R 1 0 4611686018427387904 4611686018695823363 v732 v732 := (r_psel hl h_v731 h_t723_1 h_t724_1 (of_decide_eq_true rfl))
  have e_v732 : v732 = if v731 = 1 then t723.1 else t724.1 := e_psel h_v731 h_t723_1 h_t724_1 (of_decide_eq_true rfl)
  have h_v733 : R 1 0 4611686018427387900 4611686018695823359 v733 v733 := (r_sub hl (r_add hl h_v28 h_v732 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v733 : sv v733 = sv v28 + sv v732 := e_add h_v28 h_v732 (of_decide_eq_true rfl)
  have h_v734 : R 1 0 4611686018427387904 4611686018695823363 v734 v734 := (r_psel hl h_v731 h_t724_1 h_t723_1 (of_decide_eq_true rfl))
  have e_v734 : v734 = if v731 = 1 then t724.1 else t723.1 := e_psel h_v731 h_t724_1 h_t723_1 (of_decide_eq_true rfl)
  have h_v735 : R 1 0 4611686018427387908 4611686018695823367 v735 v735 := (r_sub hl (r_add hl h_v31 h_v734 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v735 : sv v735 = sv v31 + sv v734 := e_add h_v31 h_v734 (of_decide_eq_true rfl)
  have h_v736 : R 1 0 0 1 v736 v736 := (r_plt hl h_v735 h_v33 (of_decide_eq_true rfl))
  have e_v736 : (v736 = 1 ↔ sv v735 < sv v33) := e_plt h_v735 h_v33 (of_decide_eq_true rfl)
  have h_v737 : R 1 0 4611686018427387908 4611686018695823367 v737 v737 := (r_psel hl h_v736 h_v735 h_v33 (of_decide_eq_true rfl))
  have e_v737 : v737 = if v736 = 1 then v735 else v33 := e_psel h_v736 h_v735 h_v33 (of_decide_eq_true rfl)
  have h_v738 : R 1 0 0 1 v738 v738 := (r_plt hl h_v723 h_v36 (of_decide_eq_true rfl))
  have e_v738 : (v738 = 1 ↔ sv v723 < sv v36) := e_plt h_v723 h_v36 (of_decide_eq_true rfl)
  clear h_v28 h_v36 h_v723 h_v725 h_v727 h_t723_1 h_t723_2 e_t723_2 h_t724_1 h_t724_2 e_t724_2 h_v731 h_v732 h_v734 h_v735 h_v736
  have h_v739 : R 1 0 0 1 v739 v739 := (r_plt hl h_v38 h_v724 (of_decide_eq_true rfl))
  have e_v739 : (v739 = 1 ↔ sv v38 < sv v724) := e_plt h_v38 h_v724 (of_decide_eq_true rfl)
  have h_v740 : R 1 0 0 1 v740 v740 := (r_land hl h_v738 h_v739 (of_decide_eq_true rfl))
  have e_v740 : (v740 = 1 ↔ v738 = 1 ∧ v739 = 1) := e_land h_v738 h_v739 (of_decide_eq_true rfl)
  have h_v741 : R 1 0 4611686018427387908 4611686018695823367 v741 v741 := (r_psel hl h_v740 h_v33 h_v737 (of_decide_eq_true rfl))
  have e_v741 : v741 = if v740 = 1 then v33 else v737 := e_psel h_v740 h_v33 h_v737 (of_decide_eq_true rfl)
  have h_v742 : R 1 0 0 1 v742 v742 := (r_plt hl h_v733 h_v9 (of_decide_eq_true rfl))
  have e_v742 : (v742 = 1 ↔ sv v733 < sv v9) := e_plt h_v733 h_v9 (of_decide_eq_true rfl)
  have h_v743 : R 1 0 0 1 v743 v743 := (r_sub hl (r_O hl) h_v742 (of_decide_eq_true rfl))
  have e_v743 : (v743 = 1 ↔ ¬v742 = 1) := e_not h_v742 (of_decide_eq_true rfl)
  have h_v744 : R 1 0 0 1 v744 v744 := (r_plt hl h_v9 h_v741 (of_decide_eq_true rfl))
  have e_v744 : (v744 = 1 ↔ sv v9 < sv v741) := e_plt h_v9 h_v741 (of_decide_eq_true rfl)
  have h_v745 : R 1 0 0 1 v745 v745 := (r_sub hl (r_O hl) h_v744 (of_decide_eq_true rfl))
  have e_v745 : (v745 = 1 ↔ ¬v744 = 1) := e_not h_v744 (of_decide_eq_true rfl)
  have h_v746 : R 1 0 0 1 v746 v746 := (r_land hl h_v742 h_v745 (of_decide_eq_true rfl))
  have e_v746 : (v746 = 1 ↔ v742 = 1 ∧ v745 = 1) := e_land h_v742 h_v745 (of_decide_eq_true rfl)
  have h_v747 : R 1 0 0 1 v747 v747 := (r_land hl h_v742 h_v744 (of_decide_eq_true rfl))
  have e_v747 : (v747 = 1 ↔ v742 = 1 ∧ v744 = 1) := e_land h_v742 h_v744 (of_decide_eq_true rfl)
  have h_v748 : R 1 0 0 1 v748 v748 := (r_land hl h_v66 h_v747 (of_decide_eq_true rfl))
  have e_v748 : (v748 = 1 ↔ v66 = 1 ∧ v747 = 1) := e_land h_v66 h_v747 (of_decide_eq_true rfl)
  have h_v749 : R 1 0 0 1 v749 v749 := (r_sub hl (r_O hl) h_v748 (of_decide_eq_true rfl))
  have e_v749 : (v749 = 1 ↔ ¬v748 = 1) := e_not h_v748 (of_decide_eq_true rfl)
  have h_v750 : R 1 0 0 1 v750 v750 := (r_land hl h_v62 h_v747 (of_decide_eq_true rfl))
  have e_v750 : (v750 = 1 ↔ v62 = 1 ∧ v747 = 1) := e_land h_v62 h_v747 (of_decide_eq_true rfl)
  have h_v751 : R 1 0 0 1 v751 v751 := (r_lor hl h_v746 h_v750 (of_decide_eq_true rfl))
  clear h_v38 h_v62 h_v724 h_v737 h_v738 h_v739 h_v740 h_v742 h_v744 h_v745 h_v748
  have e_v751 : (v751 = 1 ↔ v746 = 1 ∨ v750 = 1) := e_lor h_v746 h_v750 (of_decide_eq_true rfl)
  have h_v752 : R 1 0 4611686018427387900 4611686018695823367 v752 v752 := (r_psel hl h_v751 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v752 : v752 = if v751 = 1 then v41 else v29 := e_psel h_v751 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v753 : R 1 0 0 1 v753 v753 := (r_land hl h_v66 h_v743 (of_decide_eq_true rfl))
  have e_v753 : (v753 = 1 ↔ v66 = 1 ∧ v743 = 1) := e_land h_v66 h_v743 (of_decide_eq_true rfl)
  have h_v754 : R 1 0 0 1 v754 v754 := (r_lor hl h_v65 h_v753 (of_decide_eq_true rfl))
  have e_v754 : (v754 = 1 ↔ v65 = 1 ∨ v753 = 1) := e_lor h_v65 h_v753 (of_decide_eq_true rfl)
  have h_v755 : R 1 0 4611686018427387900 4611686018695823367 v755 v755 := (r_psel hl h_v754 h_v741 h_v733 (of_decide_eq_true rfl))
  have e_v755 : v755 = if v754 = 1 then v741 else v733 := e_psel h_v754 h_v741 h_v733 (of_decide_eq_true rfl)
  have h_v756 : R 1 0 0 1 v756 v756 := (r_land hl h_v65 h_v747 (of_decide_eq_true rfl))
  have e_v756 : (v756 = 1 ↔ v65 = 1 ∧ v747 = 1) := e_land h_v65 h_v747 (of_decide_eq_true rfl)
  have h_v757 : R 1 0 0 1 v757 v757 := (r_lor hl h_v746 h_v756 (of_decide_eq_true rfl))
  have e_v757 : (v757 = 1 ↔ v746 = 1 ∨ v756 = 1) := e_lor h_v746 h_v756 (of_decide_eq_true rfl)
  have h_v758 : R 1 0 4611686018427387900 4611686018695823367 v758 v758 := (r_psel hl h_v757 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v758 : v758 = if v757 = 1 then v29 else v41 := e_psel h_v757 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v759 : R 1 0 0 1 v759 v759 := (r_land hl h_v66 h_v746 (of_decide_eq_true rfl))
  have e_v759 : (v759 = 1 ↔ v66 = 1 ∧ v746 = 1) := e_land h_v66 h_v746 (of_decide_eq_true rfl)
  have h_v760 : R 1 0 0 1 v760 v760 := (r_lor hl h_v65 h_v759 (of_decide_eq_true rfl))
  have e_v760 : (v760 = 1 ↔ v65 = 1 ∨ v759 = 1) := e_lor h_v65 h_v759 (of_decide_eq_true rfl)
  have h_v761 : R 1 0 4611686018427387900 4611686018695823367 v761 v761 := (r_psel hl h_v760 h_v733 h_v741 (of_decide_eq_true rfl))
  have e_v761 : v761 = if v760 = 1 then v733 else v741 := e_psel h_v760 h_v733 h_v741 (of_decide_eq_true rfl)
  have h_v762 : R 1 0 4611686017353646052 4683743616223412273 v762 v762 := (r_smx hl 29 h_v755 h_v752 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v762 : sv v762 = sv v755 * sv v752 := e_smx 29 h_v755 h_v752 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v763 : R 1 0 4611686018427387899 4611686018695823374 v763 v763 := (r_srdF hl h_v762 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v763 : sv v763 = sv v762 / 2 ^ 28 := e_srdF h_v762 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  clear h_v29 h_v41 h_v65 h_v66 h_v733 h_v741 h_v743 h_v746 h_v747 h_v750 h_v751 h_v752 h_v753 h_v754 h_v755 h_v756 h_v757 h_v759 h_v760 h_v762
  have h_v764 : R 1 0 4611686017353646052 4683743616223412273 v764 v764 := (r_smx hl 29 h_v761 h_v758 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v764 : sv v764 = sv v761 * sv v758 := e_smx 29 h_v761 h_v758 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v765 : R 1 0 4611686018427387900 4611686018695823375 v765 v765 := (r_srdC hl h_v764 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v765 : sv v765 = -((-sv v764) / 2 ^ 28) := e_srdC h_v764 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v766 : R 1 0 0 1 v766 v766 := (r_plt hl h_v18 h_v763 (of_decide_eq_true rfl))
  have e_v766 : (v766 = 1 ↔ sv v18 < sv v763) := e_plt h_v18 h_v763 (of_decide_eq_true rfl)
  have h_v767 : R 1 0 0 1 v767 v767 := (r_plt hl h_v9 h_v763 (of_decide_eq_true rfl))
  have e_v767 : (v767 = 1 ↔ sv v9 < sv v763) := e_plt h_v9 h_v763 (of_decide_eq_true rfl)
  have h_v768 : R 1 0 0 1 v768 v768 := (r_plt hl h_v765 h_v33 (of_decide_eq_true rfl))
  have e_v768 : (v768 = 1 ↔ sv v765 < sv v33) := e_plt h_v765 h_v33 (of_decide_eq_true rfl)
  have h_v769 : R 1 0 0 1 v769 v769 := (r_land hl h_v767 h_v768 (of_decide_eq_true rfl))
  have e_v769 : (v769 = 1 ↔ v767 = 1 ∧ v768 = 1) := e_land h_v767 h_v768 (of_decide_eq_true rfl)
  have h_v770 : R 1 0 0 1 v770 v770 := (r_plt hl h_v9 h_v88 (of_decide_eq_true rfl))
  have e_v770 : (v770 = 1 ↔ sv v9 < sv v88) := e_plt h_v9 h_v88 (of_decide_eq_true rfl)
  have h_v771 : R 1 0 0 1 v771 v771 := (r_plt hl h_v90 h_v33 (of_decide_eq_true rfl))
  have e_v771 : (v771 = 1 ↔ sv v90 < sv v33) := e_plt h_v90 h_v33 (of_decide_eq_true rfl)
  have h_v772 : R 1 0 0 1 v772 v772 := (r_land hl h_v770 h_v771 (of_decide_eq_true rfl))
  have e_v772 : (v772 = 1 ↔ v770 = 1 ∧ v771 = 1) := e_land h_v770 h_v771 (of_decide_eq_true rfl)
  have h_v773 : R 1 0 0 1 v773 v773 := (r_plt hl h_v9 h_v437 (of_decide_eq_true rfl))
  have e_v773 : (v773 = 1 ↔ sv v9 < sv v437) := e_plt h_v9 h_v437 (of_decide_eq_true rfl)
  have h_v774 : R 1 0 0 1 v774 v774 := (r_plt hl h_v439 h_v33 (of_decide_eq_true rfl))
  have e_v774 : (v774 = 1 ↔ sv v439 < sv v33) := e_plt h_v439 h_v33 (of_decide_eq_true rfl)
  have h_v775 : R 1 0 0 1 v775 v775 := (r_land hl h_v773 h_v774 (of_decide_eq_true rfl))
  have e_v775 : (v775 = 1 ↔ v773 = 1 ∧ v774 = 1) := e_land h_v773 h_v774 (of_decide_eq_true rfl)
  have h_v776 : R 1 0 0 1 v776 v776 := (r_land hl h_v769 h_v772 (of_decide_eq_true rfl))
  clear h_v18 h_v758 h_v761 h_v764 h_v767 h_v768 h_v770 h_v771 h_v773 h_v774
  have e_v776 : (v776 = 1 ↔ v769 = 1 ∧ v772 = 1) := e_land h_v769 h_v772 (of_decide_eq_true rfl)
  have h_v777 : R 1 0 0 1 v777 v777 := (r_land hl h_v775 h_v776 (of_decide_eq_true rfl))
  have e_v777 : (v777 = 1 ↔ v775 = 1 ∧ v776 = 1) := e_land h_v775 h_v776 (of_decide_eq_true rfl)
  have h_v778 : R 1 0 4611686018427387904 4683743620518379745 v778 v778 := (r_smx_sq hl 29 h_v765 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v778 : sv v778 = sv v765 * sv v765 := e_smx_sq 29 h_v765 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v779 : R 1 0 4611686018427387904 4611686018695823391 v779 v779 := (r_srdC hl h_v778 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v779 : sv v779 = -((-sv v778) / 2 ^ 28) := e_srdC h_v778 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v780 : R 1 0 4611686018427387904 4611686018964258878 v780 v780 := (r_sub hl (r_add hl h_v779 h_v779 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v780 : sv v780 = sv v779 + sv v779 := e_add h_v779 h_v779 (of_decide_eq_true rfl)
  have h_v781 : R 1 0 4611686018158952386 4611686018695823360 v781 v781 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v780 (of_decide_eq_true rfl))
  have e_v781 : sv v781 = sv v33 - sv v780 := e_sub h_v33 h_v780 (of_decide_eq_true rfl)
  have h_v782 : R 1 0 0 1 v782 v782 := (r_plt hl h_v781 h_v94 (of_decide_eq_true rfl))
  have e_v782 : (v782 = 1 ↔ sv v781 < sv v94) := e_plt h_v781 h_v94 (of_decide_eq_true rfl)
  have h_v783 : R 1 0 4611686018158952386 4611686018695823360 v783 v783 := (r_psel hl h_v782 h_v94 h_v781 (of_decide_eq_true rfl))
  have e_v783 : v783 = if v782 = 1 then v94 else v781 := e_psel h_v782 h_v94 h_v781 (of_decide_eq_true rfl)
  have h_v784 : R 1 0 4611686018427387904 4683743619981508804 v784 v784 := (r_smx_sq hl 29 h_v763 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v784 : sv v784 = sv v763 * sv v763 := e_smx_sq 29 h_v763 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v785 : R 1 0 4611686018427387904 4611686018695823388 v785 v785 := (r_srdF hl h_v784 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v785 : sv v785 = sv v784 / 2 ^ 28 := e_srdF h_v784 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v786 : R 1 0 4611686018427387904 4611686018964258872 v786 v786 := (r_sub hl (r_add hl h_v785 h_v785 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v786 : sv v786 = sv v785 + sv v785 := e_add h_v785 h_v785 (of_decide_eq_true rfl)
  have h_v787 : R 1 0 4611686018158952392 4611686018695823360 v787 v787 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v786 (of_decide_eq_true rfl))
  have e_v787 : sv v787 = sv v33 - sv v786 := e_sub h_v33 h_v786 (of_decide_eq_true rfl)
  have h_v788 : R 1 0 4611686018427387904 4683743620518379745 v788 v788 := (r_smx_sq hl 29 h_v439 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v788 : sv v788 = sv v439 * sv v439 := e_smx_sq 29 h_v439 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  clear h_v763 h_v765 h_v769 h_v772 h_v775 h_v776 h_v778 h_v779 h_v780 h_v781 h_v782 h_v784 h_v785 h_v786
  have h_v789 : R 1 0 4611686018427387904 4611686018695823391 v789 v789 := (r_srdC hl h_v788 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v789 : sv v789 = -((-sv v788) / 2 ^ 28) := e_srdC h_v788 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v790 : R 1 0 4611686018427387904 4611686018964258878 v790 v790 := (r_sub hl (r_add hl h_v789 h_v789 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v790 : sv v790 = sv v789 + sv v789 := e_add h_v789 h_v789 (of_decide_eq_true rfl)
  have h_v791 : R 1 0 4611686018158952386 4611686018695823360 v791 v791 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v790 (of_decide_eq_true rfl))
  have e_v791 : sv v791 = sv v33 - sv v790 := e_sub h_v33 h_v790 (of_decide_eq_true rfl)
  have h_v792 : R 1 0 0 1 v792 v792 := (r_plt hl h_v791 h_v94 (of_decide_eq_true rfl))
  have e_v792 : (v792 = 1 ↔ sv v791 < sv v94) := e_plt h_v791 h_v94 (of_decide_eq_true rfl)
  have h_v793 : R 1 0 4611686018158952386 4611686018695823360 v793 v793 := (r_psel hl h_v792 h_v94 h_v791 (of_decide_eq_true rfl))
  have e_v793 : v793 = if v792 = 1 then v94 else v791 := e_psel h_v792 h_v94 h_v791 (of_decide_eq_true rfl)
  have h_v794 : R 1 0 4611686018427387904 4683743619981508804 v794 v794 := (r_smx_sq hl 29 h_v437 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v794 : sv v794 = sv v437 * sv v437 := e_smx_sq 29 h_v437 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v795 : R 1 0 4611686018427387904 4611686018695823388 v795 v795 := (r_srdF hl h_v794 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v795 : sv v795 = sv v794 / 2 ^ 28 := e_srdF h_v794 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v796 : R 1 0 4611686018427387904 4611686018964258872 v796 v796 := (r_sub hl (r_add hl h_v795 h_v795 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v796 : sv v796 = sv v795 + sv v795 := e_add h_v795 h_v795 (of_decide_eq_true rfl)
  have h_v797 : R 1 0 4611686018158952392 4611686018695823360 v797 v797 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v796 (of_decide_eq_true rfl))
  have e_v797 : sv v797 = sv v33 - sv v796 := e_sub h_v33 h_v796 (of_decide_eq_true rfl)
  have h_v798 : R 1 0 4611686018427387904 4683743620518379745 v798 v798 := (r_smx_sq hl 29 h_v90 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v798 : sv v798 = sv v90 * sv v90 := e_smx_sq 29 h_v90 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v799 : R 1 0 4611686018427387904 4611686018695823391 v799 v799 := (r_srdC hl h_v798 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v799 : sv v799 = -((-sv v798) / 2 ^ 28) := e_srdC h_v798 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v800 : R 1 0 4611686018427387904 4611686018964258878 v800 v800 := (r_sub hl (r_add hl h_v799 h_v799 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v800 : sv v800 = sv v799 + sv v799 := e_add h_v799 h_v799 (of_decide_eq_true rfl)
  have h_v801 : R 1 0 4611686018158952386 4611686018695823360 v801 v801 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v800 (of_decide_eq_true rfl))
  clear h_v788 h_v789 h_v790 h_v791 h_v792 h_v794 h_v795 h_v796 h_v798 h_v799
  have e_v801 : sv v801 = sv v33 - sv v800 := e_sub h_v33 h_v800 (of_decide_eq_true rfl)
  have h_v802 : R 1 0 0 1 v802 v802 := (r_plt hl h_v801 h_v94 (of_decide_eq_true rfl))
  have e_v802 : (v802 = 1 ↔ sv v801 < sv v94) := e_plt h_v801 h_v94 (of_decide_eq_true rfl)
  have h_v803 : R 1 0 4611686018158952386 4611686018695823360 v803 v803 := (r_psel hl h_v802 h_v94 h_v801 (of_decide_eq_true rfl))
  have e_v803 : v803 = if v802 = 1 then v94 else v801 := e_psel h_v802 h_v94 h_v801 (of_decide_eq_true rfl)
  have h_v804 : R 1 0 4611686018427387904 4683743619981508804 v804 v804 := (r_smx_sq hl 29 h_v88 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v804 : sv v804 = sv v88 * sv v88 := e_smx_sq 29 h_v88 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v805 : R 1 0 4611686018427387904 4611686018695823388 v805 v805 := (r_srdF hl h_v804 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v805 : sv v805 = sv v804 / 2 ^ 28 := e_srdF h_v804 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v806 : R 1 0 4611686018427387904 4611686018964258872 v806 v806 := (r_sub hl (r_add hl h_v805 h_v805 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v806 : sv v806 = sv v805 + sv v805 := e_add h_v805 h_v805 (of_decide_eq_true rfl)
  have h_v807 : R 1 0 4611686018158952392 4611686018695823360 v807 v807 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v806 (of_decide_eq_true rfl))
  have e_v807 : sv v807 = sv v33 - sv v806 := e_sub h_v33 h_v806 (of_decide_eq_true rfl)
  have h_v808 : R 1 0 0 1 v808 v808 := (r_plt hl h_v783 h_v9 (of_decide_eq_true rfl))
  have e_v808 : (v808 = 1 ↔ sv v783 < sv v9) := e_plt h_v783 h_v9 (of_decide_eq_true rfl)
  have h_v809 : R 1 0 0 1 v809 v809 := (r_sub hl (r_O hl) h_v808 (of_decide_eq_true rfl))
  have e_v809 : (v809 = 1 ↔ ¬v808 = 1) := e_not h_v808 (of_decide_eq_true rfl)
  have h_v810 : R 1 0 0 1 v810 v810 := (r_plt hl h_v9 h_v787 (of_decide_eq_true rfl))
  have e_v810 : (v810 = 1 ↔ sv v9 < sv v787) := e_plt h_v9 h_v787 (of_decide_eq_true rfl)
  have h_v811 : R 1 0 0 1 v811 v811 := (r_sub hl (r_O hl) h_v810 (of_decide_eq_true rfl))
  have e_v811 : (v811 = 1 ↔ ¬v810 = 1) := e_not h_v810 (of_decide_eq_true rfl)
  have h_v812 : R 1 0 0 1 v812 v812 := (r_land hl h_v808 h_v811 (of_decide_eq_true rfl))
  have e_v812 : (v812 = 1 ↔ v808 = 1 ∧ v811 = 1) := e_land h_v808 h_v811 (of_decide_eq_true rfl)
  have h_v813 : R 1 0 0 1 v813 v813 := (r_land hl h_v808 h_v810 (of_decide_eq_true rfl))
  have e_v813 : (v813 = 1 ↔ v808 = 1 ∧ v810 = 1) := e_land h_v808 h_v810 (of_decide_eq_true rfl)
  clear h_v800 h_v801 h_v802 h_v804 h_v805 h_v806 h_v808 h_v810 h_v811
  have h_v814 : R 1 0 0 1 v814 v814 := (r_plt hl h_v803 h_v9 (of_decide_eq_true rfl))
  have e_v814 : (v814 = 1 ↔ sv v803 < sv v9) := e_plt h_v803 h_v9 (of_decide_eq_true rfl)
  have h_v815 : R 1 0 0 1 v815 v815 := (r_sub hl (r_O hl) h_v814 (of_decide_eq_true rfl))
  have e_v815 : (v815 = 1 ↔ ¬v814 = 1) := e_not h_v814 (of_decide_eq_true rfl)
  have h_v816 : R 1 0 0 1 v816 v816 := (r_plt hl h_v9 h_v807 (of_decide_eq_true rfl))
  have e_v816 : (v816 = 1 ↔ sv v9 < sv v807) := e_plt h_v9 h_v807 (of_decide_eq_true rfl)
  have h_v817 : R 1 0 0 1 v817 v817 := (r_sub hl (r_O hl) h_v816 (of_decide_eq_true rfl))
  have e_v817 : (v817 = 1 ↔ ¬v816 = 1) := e_not h_v816 (of_decide_eq_true rfl)
  have h_v818 : R 1 0 0 1 v818 v818 := (r_land hl h_v814 h_v817 (of_decide_eq_true rfl))
  have e_v818 : (v818 = 1 ↔ v814 = 1 ∧ v817 = 1) := e_land h_v814 h_v817 (of_decide_eq_true rfl)
  have h_v819 : R 1 0 0 1 v819 v819 := (r_land hl h_v814 h_v816 (of_decide_eq_true rfl))
  have e_v819 : (v819 = 1 ↔ v814 = 1 ∧ v816 = 1) := e_land h_v814 h_v816 (of_decide_eq_true rfl)
  have h_v820 : R 1 0 0 1 v820 v820 := (r_land hl h_v813 h_v819 (of_decide_eq_true rfl))
  have e_v820 : (v820 = 1 ↔ v813 = 1 ∧ v819 = 1) := e_land h_v813 h_v819 (of_decide_eq_true rfl)
  have h_v821 : R 1 0 0 1 v821 v821 := (r_sub hl (r_O hl) h_v820 (of_decide_eq_true rfl))
  have e_v821 : (v821 = 1 ↔ ¬v820 = 1) := e_not h_v820 (of_decide_eq_true rfl)
  have h_v822 : R 1 0 0 1 v822 v822 := (r_sub hl (r_O hl) h_v777 (of_decide_eq_true rfl))
  have e_v822 : (v822 = 1 ↔ ¬v777 = 1) := e_not h_v777 (of_decide_eq_true rfl)
  have h_v823 : R 1 0 0 1 v823 v823 := (r_lor hl h_v821 h_v822 (of_decide_eq_true rfl))
  have e_v823 : (v823 = 1 ↔ v821 = 1 ∨ v822 = 1) := e_lor h_v821 h_v822 (of_decide_eq_true rfl)
  have h_v824 : R 1 0 0 1 v824 v824 := (r_land hl h_v809 h_v819 (of_decide_eq_true rfl))
  have e_v824 : (v824 = 1 ↔ v809 = 1 ∧ v819 = 1) := e_land h_v809 h_v819 (of_decide_eq_true rfl)
  have h_v825 : R 1 0 0 1 v825 v825 := (r_lor hl h_v818 h_v824 (of_decide_eq_true rfl))
  have e_v825 : (v825 = 1 ↔ v818 = 1 ∨ v824 = 1) := e_lor h_v818 h_v824 (of_decide_eq_true rfl)
  have h_v826 : R 1 0 4611686018158952386 4611686018695823360 v826 v826 := (r_psel hl h_v825 h_v787 h_v783 (of_decide_eq_true rfl))
  clear h_v814 h_v816 h_v817 h_v820 h_v821 h_v824
  have e_v826 : v826 = if v825 = 1 then v787 else v783 := e_psel h_v825 h_v787 h_v783 (of_decide_eq_true rfl)
  have h_v827 : R 1 0 0 1 v827 v827 := (r_land hl h_v813 h_v815 (of_decide_eq_true rfl))
  have e_v827 : (v827 = 1 ↔ v813 = 1 ∧ v815 = 1) := e_land h_v813 h_v815 (of_decide_eq_true rfl)
  have h_v828 : R 1 0 0 1 v828 v828 := (r_lor hl h_v812 h_v827 (of_decide_eq_true rfl))
  have e_v828 : (v828 = 1 ↔ v812 = 1 ∨ v827 = 1) := e_lor h_v812 h_v827 (of_decide_eq_true rfl)
  have h_v829 : R 1 0 4611686018158952386 4611686018695823360 v829 v829 := (r_psel hl h_v828 h_v807 h_v803 (of_decide_eq_true rfl))
  have e_v829 : v829 = if v828 = 1 then v807 else v803 := e_psel h_v828 h_v807 h_v803 (of_decide_eq_true rfl)
  have h_v830 : R 1 0 0 1 v830 v830 := (r_land hl h_v812 h_v819 (of_decide_eq_true rfl))
  have e_v830 : (v830 = 1 ↔ v812 = 1 ∧ v819 = 1) := e_land h_v812 h_v819 (of_decide_eq_true rfl)
  have h_v831 : R 1 0 0 1 v831 v831 := (r_lor hl h_v818 h_v830 (of_decide_eq_true rfl))
  have e_v831 : (v831 = 1 ↔ v818 = 1 ∨ v830 = 1) := e_lor h_v818 h_v830 (of_decide_eq_true rfl)
  have h_v832 : R 1 0 4611686018158952386 4611686018695823360 v832 v832 := (r_psel hl h_v831 h_v783 h_v787 (of_decide_eq_true rfl))
  have e_v832 : v832 = if v831 = 1 then v783 else v787 := e_psel h_v831 h_v783 h_v787 (of_decide_eq_true rfl)
  have h_v833 : R 1 0 0 1 v833 v833 := (r_land hl h_v813 h_v818 (of_decide_eq_true rfl))
  have e_v833 : (v833 = 1 ↔ v813 = 1 ∧ v818 = 1) := e_land h_v813 h_v818 (of_decide_eq_true rfl)
  have h_v834 : R 1 0 0 1 v834 v834 := (r_lor hl h_v812 h_v833 (of_decide_eq_true rfl))
  have e_v834 : (v834 = 1 ↔ v812 = 1 ∨ v833 = 1) := e_lor h_v812 h_v833 (of_decide_eq_true rfl)
  have h_v835 : R 1 0 4611686018158952386 4611686018695823360 v835 v835 := (r_psel hl h_v834 h_v803 h_v807 (of_decide_eq_true rfl))
  have e_v835 : v835 = if v834 = 1 then v803 else v807 := e_psel h_v834 h_v803 h_v807 (of_decide_eq_true rfl)
  have h_v836 : R 1 0 4539628407746461696 4683743645751316228 v836 v836 := (r_smx hl 30 h_v829 h_v826 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v836 : sv v836 = sv v829 * sv v826 := e_smx 30 h_v829 h_v826 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v837 : R 1 0 4611686018158952386 4611686018695823484 v837 v837 := (r_srdF hl h_v836 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v837 : sv v837 = sv v836 / 2 ^ 28 := e_srdF h_v836 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v838 : R 1 0 4539628407746461696 4683743645751316228 v838 v838 := (r_smx hl 30 h_v835 h_v832 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v838 : sv v838 = sv v835 * sv v832 := e_smx 30 h_v835 h_v832 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  clear h_v815 h_v818 h_v819 h_v825 h_v826 h_v827 h_v828 h_v829 h_v830 h_v831 h_v832 h_v833 h_v834 h_v835 h_v836
  have h_v839 : R 1 0 4611686018158952386 4611686018695823485 v839 v839 := (r_srdC hl h_v838 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v839 : sv v839 = -((-sv v838) / 2 ^ 28) := e_srdC h_v838 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v840 : R 1 0 4611686017890516805 4611686018964258878 v840 v840 := (r_sub hl (r_add hl h_v793 h_OFFr (of_decide_eq_true rfl)) h_v839 (of_decide_eq_true rfl))
  have e_v840 : sv v840 = sv v793 - sv v839 := e_sub h_v793 h_v839 (of_decide_eq_true rfl)
  have h_v841 : R 1 0 4611686017890516812 4611686018964258878 v841 v841 := (r_sub hl (r_add hl h_v797 h_OFFr (of_decide_eq_true rfl)) h_v837 (of_decide_eq_true rfl))
  have e_v841 : sv v841 = sv v797 - sv v837 := e_sub h_v797 h_v837 (of_decide_eq_true rfl)
  have h_v842 : R 1 0 0 1 v842 v842 := (r_plt hl h_v793 h_v9 (of_decide_eq_true rfl))
  have e_v842 : (v842 = 1 ↔ sv v793 < sv v9) := e_plt h_v793 h_v9 (of_decide_eq_true rfl)
  have h_v843 : R 1 0 0 1 v843 v843 := (r_sub hl (r_O hl) h_v842 (of_decide_eq_true rfl))
  have e_v843 : (v843 = 1 ↔ ¬v842 = 1) := e_not h_v842 (of_decide_eq_true rfl)
  have h_v844 : R 1 0 0 1 v844 v844 := (r_plt hl h_v9 h_v797 (of_decide_eq_true rfl))
  have e_v844 : (v844 = 1 ↔ sv v9 < sv v797) := e_plt h_v9 h_v797 (of_decide_eq_true rfl)
  have h_v845 : R 1 0 0 1 v845 v845 := (r_sub hl (r_O hl) h_v844 (of_decide_eq_true rfl))
  have e_v845 : (v845 = 1 ↔ ¬v844 = 1) := e_not h_v844 (of_decide_eq_true rfl)
  have h_v846 : R 1 0 0 1 v846 v846 := (r_land hl h_v842 h_v845 (of_decide_eq_true rfl))
  have e_v846 : (v846 = 1 ↔ v842 = 1 ∧ v845 = 1) := e_land h_v842 h_v845 (of_decide_eq_true rfl)
  have h_v847 : R 1 0 0 1 v847 v847 := (r_land hl h_v842 h_v844 (of_decide_eq_true rfl))
  have e_v847 : (v847 = 1 ↔ v842 = 1 ∧ v844 = 1) := e_land h_v842 h_v844 (of_decide_eq_true rfl)
  have h_v848 : R 1 0 0 1 v848 v848 := (r_land hl h_v813 h_v847 (of_decide_eq_true rfl))
  have e_v848 : (v848 = 1 ↔ v813 = 1 ∧ v847 = 1) := e_land h_v813 h_v847 (of_decide_eq_true rfl)
  have h_v849 : R 1 0 0 1 v849 v849 := (r_sub hl (r_O hl) h_v848 (of_decide_eq_true rfl))
  have e_v849 : (v849 = 1 ↔ ¬v848 = 1) := e_not h_v848 (of_decide_eq_true rfl)
  have h_v850 : R 1 0 0 1 v850 v850 := (r_lor hl h_v822 h_v849 (of_decide_eq_true rfl))
  have e_v850 : (v850 = 1 ↔ v822 = 1 ∨ v849 = 1) := e_lor h_v822 h_v849 (of_decide_eq_true rfl)
  have h_v851 : R 1 0 0 1 v851 v851 := (r_land hl h_v809 h_v847 (of_decide_eq_true rfl))
  clear h_v837 h_v838 h_v839 h_v842 h_v844 h_v845 h_v848 h_v849
  have e_v851 : (v851 = 1 ↔ v809 = 1 ∧ v847 = 1) := e_land h_v809 h_v847 (of_decide_eq_true rfl)
  have h_v852 : R 1 0 0 1 v852 v852 := (r_lor hl h_v846 h_v851 (of_decide_eq_true rfl))
  have e_v852 : (v852 = 1 ↔ v846 = 1 ∨ v851 = 1) := e_lor h_v846 h_v851 (of_decide_eq_true rfl)
  have h_v853 : R 1 0 4611686018158952386 4611686018695823360 v853 v853 := (r_psel hl h_v852 h_v787 h_v783 (of_decide_eq_true rfl))
  have e_v853 : v853 = if v852 = 1 then v787 else v783 := e_psel h_v852 h_v787 h_v783 (of_decide_eq_true rfl)
  have h_v854 : R 1 0 0 1 v854 v854 := (r_land hl h_v813 h_v843 (of_decide_eq_true rfl))
  have e_v854 : (v854 = 1 ↔ v813 = 1 ∧ v843 = 1) := e_land h_v813 h_v843 (of_decide_eq_true rfl)
  have h_v855 : R 1 0 0 1 v855 v855 := (r_lor hl h_v812 h_v854 (of_decide_eq_true rfl))
  have e_v855 : (v855 = 1 ↔ v812 = 1 ∨ v854 = 1) := e_lor h_v812 h_v854 (of_decide_eq_true rfl)
  have h_v856 : R 1 0 4611686018158952386 4611686018695823360 v856 v856 := (r_psel hl h_v855 h_v797 h_v793 (of_decide_eq_true rfl))
  have e_v856 : v856 = if v855 = 1 then v797 else v793 := e_psel h_v855 h_v797 h_v793 (of_decide_eq_true rfl)
  have h_v857 : R 1 0 0 1 v857 v857 := (r_land hl h_v812 h_v847 (of_decide_eq_true rfl))
  have e_v857 : (v857 = 1 ↔ v812 = 1 ∧ v847 = 1) := e_land h_v812 h_v847 (of_decide_eq_true rfl)
  have h_v858 : R 1 0 0 1 v858 v858 := (r_lor hl h_v846 h_v857 (of_decide_eq_true rfl))
  have e_v858 : (v858 = 1 ↔ v846 = 1 ∨ v857 = 1) := e_lor h_v846 h_v857 (of_decide_eq_true rfl)
  have h_v859 : R 1 0 4611686018158952386 4611686018695823360 v859 v859 := (r_psel hl h_v858 h_v783 h_v787 (of_decide_eq_true rfl))
  have e_v859 : v859 = if v858 = 1 then v783 else v787 := e_psel h_v858 h_v783 h_v787 (of_decide_eq_true rfl)
  have h_v860 : R 1 0 0 1 v860 v860 := (r_land hl h_v813 h_v846 (of_decide_eq_true rfl))
  have e_v860 : (v860 = 1 ↔ v813 = 1 ∧ v846 = 1) := e_land h_v813 h_v846 (of_decide_eq_true rfl)
  have h_v861 : R 1 0 0 1 v861 v861 := (r_lor hl h_v812 h_v860 (of_decide_eq_true rfl))
  have e_v861 : (v861 = 1 ↔ v812 = 1 ∨ v860 = 1) := e_lor h_v812 h_v860 (of_decide_eq_true rfl)
  have h_v862 : R 1 0 4611686018158952386 4611686018695823360 v862 v862 := (r_psel hl h_v861 h_v793 h_v797 (of_decide_eq_true rfl))
  have e_v862 : v862 = if v861 = 1 then v793 else v797 := e_psel h_v861 h_v793 h_v797 (of_decide_eq_true rfl)
  have h_v863 : R 1 0 4539628407746461696 4683743645751316228 v863 v863 := (r_smx hl 30 h_v856 h_v853 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v863 : sv v863 = sv v856 * sv v853 := e_smx 30 h_v856 h_v853 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  clear h_v793 h_v797 h_v809 h_v812 h_v813 h_v843 h_v846 h_v847 h_v851 h_v852 h_v853 h_v854 h_v855 h_v856 h_v857 h_v858 h_v860 h_v861
  have h_v864 : R 1 0 4611686018158952386 4611686018695823484 v864 v864 := (r_srdF hl h_v863 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v864 : sv v864 = sv v863 / 2 ^ 28 := e_srdF h_v863 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v865 : R 1 0 4539628407746461696 4683743645751316228 v865 v865 := (r_smx hl 30 h_v862 h_v859 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v865 : sv v865 = sv v862 * sv v859 := e_smx 30 h_v862 h_v859 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v866 : R 1 0 4611686018158952386 4611686018695823485 v866 v866 := (r_srdC hl h_v865 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v866 : sv v866 = -((-sv v865) / 2 ^ 28) := e_srdC h_v865 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v867 : R 1 0 4611686017890516805 4611686018964258878 v867 v867 := (r_sub hl (r_add hl h_v803 h_OFFr (of_decide_eq_true rfl)) h_v866 (of_decide_eq_true rfl))
  have e_v867 : sv v867 = sv v803 - sv v866 := e_sub h_v803 h_v866 (of_decide_eq_true rfl)
  have h_v868 : R 1 0 4611686017890516812 4611686018964258878 v868 v868 := (r_sub hl (r_add hl h_v807 h_OFFr (of_decide_eq_true rfl)) h_v864 (of_decide_eq_true rfl))
  have e_v868 : sv v868 = sv v807 - sv v864 := e_sub h_v807 h_v864 (of_decide_eq_true rfl)
  have h_v869 : R 1 0 0 1 v869 v869 := (r_plt hl h_v9 h_v840 (of_decide_eq_true rfl))
  have e_v869 : (v869 = 1 ↔ sv v9 < sv v840) := e_plt h_v9 h_v840 (of_decide_eq_true rfl)
  have h_v870 : R 1 0 0 1 v870 v870 := (r_plt hl h_v841 h_v9 (of_decide_eq_true rfl))
  have e_v870 : (v870 = 1 ↔ sv v841 < sv v9) := e_plt h_v841 h_v9 (of_decide_eq_true rfl)
  have h_v871 : R 1 0 0 1 v871 v871 := (r_plt hl h_v9 h_v867 (of_decide_eq_true rfl))
  have e_v871 : (v871 = 1 ↔ sv v9 < sv v867) := e_plt h_v9 h_v867 (of_decide_eq_true rfl)
  have h_v872 : R 1 0 0 1 v872 v872 := (r_plt hl h_v868 h_v9 (of_decide_eq_true rfl))
  have e_v872 : (v872 = 1 ↔ sv v868 < sv v9) := e_plt h_v868 h_v9 (of_decide_eq_true rfl)
  have h_v873 : R 1 0 4611686018427387899 4611686018695823375 v873 v873 := (r_psel hl h_v869 h_v90 h_v88 (of_decide_eq_true rfl))
  have e_v873 : v873 = if v869 = 1 then v90 else v88 := e_psel h_v869 h_v90 h_v88 (of_decide_eq_true rfl)
  have h_v874 : R 1 0 4611686018427387899 4611686018695823375 v874 v874 := (r_psel hl h_v870 h_v88 h_v90 (of_decide_eq_true rfl))
  have e_v874 : v874 = if v870 = 1 then v88 else v90 := e_psel h_v870 h_v88 h_v90 (of_decide_eq_true rfl)
  have h_v875 : R 1 0 4611686018427387899 4611686018695823375 v875 v875 := (r_psel hl h_v870 h_v90 h_v88 (of_decide_eq_true rfl))
  have e_v875 : v875 = if v870 = 1 then v90 else v88 := e_psel h_v870 h_v90 h_v88 (of_decide_eq_true rfl)
  have h_v876 : R 1 0 4611686018427387899 4611686018695823375 v876 v876 := (r_psel hl h_v869 h_v88 h_v90 (of_decide_eq_true rfl))
  clear h_v803 h_v807 h_v840 h_v841 h_v859 h_v862 h_v863 h_v864 h_v865 h_v866 h_v867 h_v868 h_v870
  have e_v876 : v876 = if v869 = 1 then v88 else v90 := e_psel h_v869 h_v88 h_v90 (of_decide_eq_true rfl)
  have h_v877 : R 1 0 4611686018427387899 4611686018695823375 v877 v877 := (r_psel hl h_v871 h_v439 h_v437 (of_decide_eq_true rfl))
  have e_v877 : v877 = if v871 = 1 then v439 else v437 := e_psel h_v871 h_v439 h_v437 (of_decide_eq_true rfl)
  have h_v878 : R 1 0 4611686018427387899 4611686018695823375 v878 v878 := (r_psel hl h_v872 h_v437 h_v439 (of_decide_eq_true rfl))
  have e_v878 : v878 = if v872 = 1 then v437 else v439 := e_psel h_v872 h_v437 h_v439 (of_decide_eq_true rfl)
  have h_v879 : R 1 0 4611686018427387899 4611686018695823375 v879 v879 := (r_psel hl h_v872 h_v439 h_v437 (of_decide_eq_true rfl))
  have e_v879 : v879 = if v872 = 1 then v439 else v437 := e_psel h_v872 h_v439 h_v437 (of_decide_eq_true rfl)
  have h_v880 : R 1 0 4611686018427387899 4611686018695823375 v880 v880 := (r_psel hl h_v871 h_v437 h_v439 (of_decide_eq_true rfl))
  have e_v880 : v880 = if v871 = 1 then v437 else v439 := e_psel h_v871 h_v437 h_v439 (of_decide_eq_true rfl)
  have h_v886 : R 1 0 4611686018427387904 4683743620518379745 v886 v886 := (r_smx_sq hl 29 h_v874 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v886 : sv v886 = sv v874 * sv v874 := e_smx_sq 29 h_v874 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v887 : R 1 0 4611686018427387904 4611686018695823391 v887 v887 := (r_srdC hl h_v886 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v887 : sv v887 = -((-sv v886) / 2 ^ 28) := e_srdC h_v886 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v888 : R 1 0 4611686018427387904 4611686018964258878 v888 v888 := (r_sub hl (r_add hl h_v887 h_v887 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v888 : sv v888 = sv v887 + sv v887 := e_add h_v887 h_v887 (of_decide_eq_true rfl)
  have h_v889 : R 1 0 4611686018158952386 4611686018695823360 v889 v889 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v888 (of_decide_eq_true rfl))
  have e_v889 : sv v889 = sv v33 - sv v888 := e_sub h_v33 h_v888 (of_decide_eq_true rfl)
  have h_v890 : R 1 0 0 1 v890 v890 := (r_plt hl h_v889 h_v94 (of_decide_eq_true rfl))
  have e_v890 : (v890 = 1 ↔ sv v889 < sv v94) := e_plt h_v889 h_v94 (of_decide_eq_true rfl)
  have h_v891 : R 1 0 4611686018158952386 4611686018695823360 v891 v891 := (r_psel hl h_v890 h_v94 h_v889 (of_decide_eq_true rfl))
  have e_v891 : v891 = if v890 = 1 then v94 else v889 := e_psel h_v890 h_v94 h_v889 (of_decide_eq_true rfl)
  have h_v892 : R 1 0 4611686018427387904 4683743620518379745 v892 v892 := (r_smx_sq hl 29 h_v873 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v892 : sv v892 = sv v873 * sv v873 := e_smx_sq 29 h_v873 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v893 : R 1 0 4611686018427387904 4611686018695823390 v893 v893 := (r_srdF hl h_v892 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v893 : sv v893 = sv v892 / 2 ^ 28 := e_srdF h_v892 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  clear h_v88 h_v90 h_v437 h_v439 h_v869 h_v871 h_v872 h_v887 h_v888 h_v889 h_v890
  have h_v894 : R 1 0 4611686018427387904 4611686018964258876 v894 v894 := (r_sub hl (r_add hl h_v893 h_v893 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v894 : sv v894 = sv v893 + sv v893 := e_add h_v893 h_v893 (of_decide_eq_true rfl)
  have h_v895 : R 1 0 4611686018158952388 4611686018695823360 v895 v895 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v894 (of_decide_eq_true rfl))
  have e_v895 : sv v895 = sv v33 - sv v894 := e_sub h_v33 h_v894 (of_decide_eq_true rfl)
  have h_v896 : R 1 0 4611686018427387904 4683743620518379745 v896 v896 := (r_smx_sq hl 29 h_v878 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v896 : sv v896 = sv v878 * sv v878 := e_smx_sq 29 h_v878 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v897 : R 1 0 4611686018427387904 4611686018695823391 v897 v897 := (r_srdC hl h_v896 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v897 : sv v897 = -((-sv v896) / 2 ^ 28) := e_srdC h_v896 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v898 : R 1 0 4611686018427387904 4611686018964258878 v898 v898 := (r_sub hl (r_add hl h_v897 h_v897 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v898 : sv v898 = sv v897 + sv v897 := e_add h_v897 h_v897 (of_decide_eq_true rfl)
  have h_v899 : R 1 0 4611686018158952386 4611686018695823360 v899 v899 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v898 (of_decide_eq_true rfl))
  have e_v899 : sv v899 = sv v33 - sv v898 := e_sub h_v33 h_v898 (of_decide_eq_true rfl)
  have h_v900 : R 1 0 0 1 v900 v900 := (r_plt hl h_v899 h_v94 (of_decide_eq_true rfl))
  have e_v900 : (v900 = 1 ↔ sv v899 < sv v94) := e_plt h_v899 h_v94 (of_decide_eq_true rfl)
  have h_v901 : R 1 0 4611686018158952386 4611686018695823360 v901 v901 := (r_psel hl h_v900 h_v94 h_v899 (of_decide_eq_true rfl))
  have e_v901 : v901 = if v900 = 1 then v94 else v899 := e_psel h_v900 h_v94 h_v899 (of_decide_eq_true rfl)
  have h_v902 : R 1 0 4611686018427387904 4683743620518379745 v902 v902 := (r_smx_sq hl 29 h_v877 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v902 : sv v902 = sv v877 * sv v877 := e_smx_sq 29 h_v877 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v903 : R 1 0 4611686018427387904 4611686018695823390 v903 v903 := (r_srdF hl h_v902 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v903 : sv v903 = sv v902 / 2 ^ 28 := e_srdF h_v902 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v904 : R 1 0 4611686018427387904 4611686018964258876 v904 v904 := (r_sub hl (r_add hl h_v903 h_v903 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v904 : sv v904 = sv v903 + sv v903 := e_add h_v903 h_v903 (of_decide_eq_true rfl)
  have h_v905 : R 1 0 4611686018158952388 4611686018695823360 v905 v905 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v904 (of_decide_eq_true rfl))
  have e_v905 : sv v905 = sv v33 - sv v904 := e_sub h_v33 h_v904 (of_decide_eq_true rfl)
  have h_v906 : R 1 0 0 1 v906 v906 := (r_plt hl h_v891 h_v9 (of_decide_eq_true rfl))
  clear h_v893 h_v894 h_v897 h_v898 h_v899 h_v900 h_v903 h_v904
  have e_v906 : (v906 = 1 ↔ sv v891 < sv v9) := e_plt h_v891 h_v9 (of_decide_eq_true rfl)
  have h_v907 : R 1 0 0 1 v907 v907 := (r_sub hl (r_O hl) h_v906 (of_decide_eq_true rfl))
  have e_v907 : (v907 = 1 ↔ ¬v906 = 1) := e_not h_v906 (of_decide_eq_true rfl)
  have h_v908 : R 1 0 0 1 v908 v908 := (r_plt hl h_v9 h_v895 (of_decide_eq_true rfl))
  have e_v908 : (v908 = 1 ↔ sv v9 < sv v895) := e_plt h_v9 h_v895 (of_decide_eq_true rfl)
  have h_v909 : R 1 0 0 1 v909 v909 := (r_sub hl (r_O hl) h_v908 (of_decide_eq_true rfl))
  have e_v909 : (v909 = 1 ↔ ¬v908 = 1) := e_not h_v908 (of_decide_eq_true rfl)
  have h_v910 : R 1 0 0 1 v910 v910 := (r_land hl h_v906 h_v909 (of_decide_eq_true rfl))
  have e_v910 : (v910 = 1 ↔ v906 = 1 ∧ v909 = 1) := e_land h_v906 h_v909 (of_decide_eq_true rfl)
  have h_v911 : R 1 0 0 1 v911 v911 := (r_land hl h_v906 h_v908 (of_decide_eq_true rfl))
  have e_v911 : (v911 = 1 ↔ v906 = 1 ∧ v908 = 1) := e_land h_v906 h_v908 (of_decide_eq_true rfl)
  have h_v912 : R 1 0 0 1 v912 v912 := (r_plt hl h_v901 h_v9 (of_decide_eq_true rfl))
  have e_v912 : (v912 = 1 ↔ sv v901 < sv v9) := e_plt h_v901 h_v9 (of_decide_eq_true rfl)
  have h_v913 : R 1 0 0 1 v913 v913 := (r_sub hl (r_O hl) h_v912 (of_decide_eq_true rfl))
  have e_v913 : (v913 = 1 ↔ ¬v912 = 1) := e_not h_v912 (of_decide_eq_true rfl)
  have h_v914 : R 1 0 0 1 v914 v914 := (r_plt hl h_v9 h_v905 (of_decide_eq_true rfl))
  have e_v914 : (v914 = 1 ↔ sv v9 < sv v905) := e_plt h_v9 h_v905 (of_decide_eq_true rfl)
  have h_v915 : R 1 0 0 1 v915 v915 := (r_sub hl (r_O hl) h_v914 (of_decide_eq_true rfl))
  have e_v915 : (v915 = 1 ↔ ¬v914 = 1) := e_not h_v914 (of_decide_eq_true rfl)
  have h_v916 : R 1 0 0 1 v916 v916 := (r_land hl h_v912 h_v915 (of_decide_eq_true rfl))
  have e_v916 : (v916 = 1 ↔ v912 = 1 ∧ v915 = 1) := e_land h_v912 h_v915 (of_decide_eq_true rfl)
  have h_v917 : R 1 0 0 1 v917 v917 := (r_land hl h_v912 h_v914 (of_decide_eq_true rfl))
  have e_v917 : (v917 = 1 ↔ v912 = 1 ∧ v914 = 1) := e_land h_v912 h_v914 (of_decide_eq_true rfl)
  have h_v918 : R 1 0 0 1 v918 v918 := (r_land hl h_v911 h_v917 (of_decide_eq_true rfl))
  have e_v918 : (v918 = 1 ↔ v911 = 1 ∧ v917 = 1) := e_land h_v911 h_v917 (of_decide_eq_true rfl)
  clear h_v906 h_v908 h_v909 h_v912 h_v914 h_v915
  have h_v919 : R 1 0 0 1 v919 v919 := (r_sub hl (r_O hl) h_v918 (of_decide_eq_true rfl))
  have e_v919 : (v919 = 1 ↔ ¬v918 = 1) := e_not h_v918 (of_decide_eq_true rfl)
  have h_v920 : R 1 0 0 1 v920 v920 := (r_lor hl h_v822 h_v919 (of_decide_eq_true rfl))
  have e_v920 : (v920 = 1 ↔ v822 = 1 ∨ v919 = 1) := e_lor h_v822 h_v919 (of_decide_eq_true rfl)
  have h_v921 : R 1 0 0 1 v921 v921 := (r_land hl h_v907 h_v917 (of_decide_eq_true rfl))
  have e_v921 : (v921 = 1 ↔ v907 = 1 ∧ v917 = 1) := e_land h_v907 h_v917 (of_decide_eq_true rfl)
  have h_v922 : R 1 0 0 1 v922 v922 := (r_lor hl h_v916 h_v921 (of_decide_eq_true rfl))
  have e_v922 : (v922 = 1 ↔ v916 = 1 ∨ v921 = 1) := e_lor h_v916 h_v921 (of_decide_eq_true rfl)
  have h_v923 : R 1 0 4611686018158952386 4611686018695823360 v923 v923 := (r_psel hl h_v922 h_v895 h_v891 (of_decide_eq_true rfl))
  have e_v923 : v923 = if v922 = 1 then v895 else v891 := e_psel h_v922 h_v895 h_v891 (of_decide_eq_true rfl)
  have h_v924 : R 1 0 0 1 v924 v924 := (r_land hl h_v911 h_v913 (of_decide_eq_true rfl))
  have e_v924 : (v924 = 1 ↔ v911 = 1 ∧ v913 = 1) := e_land h_v911 h_v913 (of_decide_eq_true rfl)
  have h_v925 : R 1 0 0 1 v925 v925 := (r_lor hl h_v910 h_v924 (of_decide_eq_true rfl))
  have e_v925 : (v925 = 1 ↔ v910 = 1 ∨ v924 = 1) := e_lor h_v910 h_v924 (of_decide_eq_true rfl)
  have h_v926 : R 1 0 4611686018158952386 4611686018695823360 v926 v926 := (r_psel hl h_v925 h_v905 h_v901 (of_decide_eq_true rfl))
  have e_v926 : v926 = if v925 = 1 then v905 else v901 := e_psel h_v925 h_v905 h_v901 (of_decide_eq_true rfl)
  have h_v933 : R 1 0 4539628407746461696 4683743645751316228 v933 v933 := (r_smx hl 30 h_v926 h_v923 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v933 : sv v933 = sv v926 * sv v923 := e_smx 30 h_v926 h_v923 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v934 : R 1 0 4611686018158952386 4611686018695823484 v934 v934 := (r_srdF hl h_v933 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v934 : sv v934 = sv v933 / 2 ^ 28 := e_srdF h_v933 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v938 : R 1 0 4611686017890516812 4611686018964258878 v938 v938 := (r_sub hl (r_add hl h_v787 h_OFFr (of_decide_eq_true rfl)) h_v934 (of_decide_eq_true rfl))
  have e_v938 : sv v938 = sv v787 - sv v934 := e_sub h_v787 h_v934 (of_decide_eq_true rfl)
  have h_v939 : R 1 0 4683743612465315840 4683743612465315840 v939 v939 := (r_c hl 4683743612465315840 (of_decide_eq_true rfl))
  have e_v939 : sv v939 = (72057594037927936) := e_c 4683743612465315840 (72057594037927936) (of_decide_eq_true rfl)
  have h_v940 : R 1 0 4611686010374323999 4683743612465315840 v940 v940 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v892 (of_decide_eq_true rfl))
  clear h_v787 h_v891 h_v895 h_v901 h_v905 h_v907 h_v910 h_v911 h_v913 h_v916 h_v917 h_v918 h_v919 h_v921 h_v922 h_v923 h_v924 h_v925 h_v926 h_v933 h_v934
  have e_v940 : sv v940 = sv v939 - sv v892 := e_sub h_v939 h_v892 (of_decide_eq_true rfl)
  have h_v941 : R 1 0 4611686018427387904 4611686018695823360 v941 v941 := (r_psqrt hl h_v940 (of_decide_eq_true rfl))
  have e_v941 : sv v941 = ((Nat.sqrt (v940 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v940 (of_decide_eq_true rfl)
  have h_v942 : R 1 0 4611686018427387905 4611686018695823361 v942 v942 := (r_sub hl (r_add hl h_v104 h_v941 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v942 : sv v942 = sv v104 + sv v941 := e_add h_v104 h_v941 (of_decide_eq_true rfl)
  have pb_v941_v873 : PB 1 v941 v873 36028797018963968 := pb_sqrt hl h_v873 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v943 : R 1 0 4611686017085210624 4647714815446351872 v943 v943 := (r_smx_pb hl 29 h_v941 h_v873 pb_v941_v873 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v943 : sv v943 = sv v941 * sv v873 := e_smx_pb 29 h_v941 h_v873 pb_v941_v873 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v944 : R 1 0 4611686018427387899 4611686018561605632 v944 v944 := (r_srdF hl h_v943 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v944 : sv v944 = sv v943 / 2 ^ 28 := e_srdF h_v943 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v945 : R 1 0 4611686018427387894 4611686018695823360 v945 v945 := (r_sub hl (r_add hl h_v944 h_v944 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v945 : sv v945 = sv v944 + sv v944 := e_add h_v944 h_v944 (of_decide_eq_true rfl)
  have pb_v942_v873 : PB 1 v942 v873 36028797287399439 := pb_sqrt1 hl h_v873 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v946 : R 1 0 4611686017085210619 4647714815714787343 v946 v946 := (r_smx_pb hl 29 h_v942 h_v873 pb_v942_v873 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v946 : sv v946 = sv v942 * sv v873 := e_smx_pb 29 h_v942 h_v873 pb_v942_v873 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v947 : R 1 0 4611686018427387899 4611686018561605634 v947 v947 := (r_srdC hl h_v946 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v947 : sv v947 = -((-sv v946) / 2 ^ 28) := e_srdC h_v946 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v948 : R 1 0 4611686018427387894 4611686018695823364 v948 v948 := (r_sub hl (r_add hl h_v947 h_v947 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v948 : sv v948 = sv v947 + sv v947 := e_add h_v947 h_v947 (of_decide_eq_true rfl)
  have h_v949 : R 1 0 0 1 v949 v949 := (r_plt hl h_v948 h_v33 (of_decide_eq_true rfl))
  have e_v949 : (v949 = 1 ↔ sv v948 < sv v33) := e_plt h_v948 h_v33 (of_decide_eq_true rfl)
  have h_v950 : R 1 0 4611686018427387894 4611686018695823364 v950 v950 := (r_psel hl h_v949 h_v948 h_v33 (of_decide_eq_true rfl))
  have e_v950 : v950 = if v949 = 1 then v948 else v33 := e_psel h_v949 h_v948 h_v33 (of_decide_eq_true rfl)
  have h_v951 : R 1 0 4611686010374323999 4683743612465315840 v951 v951 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v886 (of_decide_eq_true rfl))
  have e_v951 : sv v951 = sv v939 - sv v886 := e_sub h_v939 h_v886 (of_decide_eq_true rfl)
  clear h_v873 h_v940 h_v941 h_v942 pb_v941_v873 h_v943 h_v944 pb_v942_v873 h_v946 h_v947 h_v948 h_v949
  have h_v952 : R 1 0 4611686018427387904 4611686018695823360 v952 v952 := (r_psqrt hl h_v951 (of_decide_eq_true rfl))
  have e_v952 : sv v952 = ((Nat.sqrt (v951 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v951 (of_decide_eq_true rfl)
  have h_v953 : R 1 0 4611686018427387905 4611686018695823361 v953 v953 := (r_sub hl (r_add hl h_v104 h_v952 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v953 : sv v953 = sv v104 + sv v952 := e_add h_v104 h_v952 (of_decide_eq_true rfl)
  have pb_v952_v874 : PB 1 v952 v874 36028797018963968 := pb_sqrt hl h_v874 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v954 : R 1 0 4611686017085210624 4647714815446351872 v954 v954 := (r_smx_pb hl 29 h_v952 h_v874 pb_v952_v874 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v954 : sv v954 = sv v952 * sv v874 := e_smx_pb 29 h_v952 h_v874 pb_v952_v874 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v955 : R 1 0 4611686018427387899 4611686018561605632 v955 v955 := (r_srdF hl h_v954 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v955 : sv v955 = sv v954 / 2 ^ 28 := e_srdF h_v954 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v956 : R 1 0 4611686018427387894 4611686018695823360 v956 v956 := (r_sub hl (r_add hl h_v955 h_v955 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v956 : sv v956 = sv v955 + sv v955 := e_add h_v955 h_v955 (of_decide_eq_true rfl)
  have pb_v953_v874 : PB 1 v953 v874 36028797287399439 := pb_sqrt1 hl h_v874 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v957 : R 1 0 4611686017085210619 4647714815714787343 v957 v957 := (r_smx_pb hl 29 h_v953 h_v874 pb_v953_v874 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v957 : sv v957 = sv v953 * sv v874 := e_smx_pb 29 h_v953 h_v874 pb_v953_v874 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v958 : R 1 0 4611686018427387899 4611686018561605634 v958 v958 := (r_srdC hl h_v957 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v958 : sv v958 = -((-sv v957) / 2 ^ 28) := e_srdC h_v957 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v959 : R 1 0 4611686018427387894 4611686018695823364 v959 v959 := (r_sub hl (r_add hl h_v958 h_v958 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v959 : sv v959 = sv v958 + sv v958 := e_add h_v958 h_v958 (of_decide_eq_true rfl)
  have h_v960 : R 1 0 0 1 v960 v960 := (r_plt hl h_v959 h_v33 (of_decide_eq_true rfl))
  have e_v960 : (v960 = 1 ↔ sv v959 < sv v33) := e_plt h_v959 h_v33 (of_decide_eq_true rfl)
  have h_v961 : R 1 0 4611686018427387894 4611686018695823364 v961 v961 := (r_psel hl h_v960 h_v959 h_v33 (of_decide_eq_true rfl))
  have e_v961 : v961 = if v960 = 1 then v959 else v33 := e_psel h_v960 h_v959 h_v33 (of_decide_eq_true rfl)
  have h_v962 : R 1 0 0 1 v962 v962 := (r_plt hl h_v945 h_v956 (of_decide_eq_true rfl))
  have e_v962 : (v962 = 1 ↔ sv v945 < sv v956) := e_plt h_v945 h_v956 (of_decide_eq_true rfl)
  have h_v963 : R 1 0 4611686018427387894 4611686018695823360 v963 v963 := (r_psel hl h_v962 h_v945 h_v956 (of_decide_eq_true rfl))
  clear h_v874 h_v951 h_v952 h_v953 pb_v952_v874 h_v954 h_v955 pb_v953_v874 h_v957 h_v958 h_v959 h_v960
  have e_v963 : v963 = if v962 = 1 then v945 else v956 := e_psel h_v962 h_v945 h_v956 (of_decide_eq_true rfl)
  have h_v964 : R 1 0 0 1 v964 v964 := (r_plt hl h_v950 h_v961 (of_decide_eq_true rfl))
  have e_v964 : (v964 = 1 ↔ sv v950 < sv v961) := e_plt h_v950 h_v961 (of_decide_eq_true rfl)
  have h_v965 : R 1 0 4611686018427387894 4611686018695823364 v965 v965 := (r_psel hl h_v964 h_v961 h_v950 (of_decide_eq_true rfl))
  have e_v965 : v965 = if v964 = 1 then v961 else v950 := e_psel h_v964 h_v961 h_v950 (of_decide_eq_true rfl)
  have h_v966 : R 1 0 4647714815446351872 4647714815446351872 v966 v966 := (r_c hl 4647714815446351872 (of_decide_eq_true rfl))
  have e_v966 : sv v966 = (36028797018963968) := e_c 4647714815446351872 (36028797018963968) (of_decide_eq_true rfl)
  have h_v967 : R 1 0 0 1 v967 v967 := (r_plt hl h_v966 h_v892 (of_decide_eq_true rfl))
  have e_v967 : (v967 = 1 ↔ sv v966 < sv v892) := e_plt h_v966 h_v892 (of_decide_eq_true rfl)
  have h_v968 : R 1 0 0 1 v968 v968 := (r_sub hl (r_O hl) h_v967 (of_decide_eq_true rfl))
  have e_v968 : (v968 = 1 ↔ ¬v967 = 1) := e_not h_v967 (of_decide_eq_true rfl)
  have h_v969 : R 1 0 0 1 v969 v969 := (r_plt hl h_v886 h_v966 (of_decide_eq_true rfl))
  have e_v969 : (v969 = 1 ↔ sv v886 < sv v966) := e_plt h_v886 h_v966 (of_decide_eq_true rfl)
  have h_v970 : R 1 0 0 1 v970 v970 := (r_sub hl (r_O hl) h_v969 (of_decide_eq_true rfl))
  have e_v970 : (v970 = 1 ↔ ¬v969 = 1) := e_not h_v969 (of_decide_eq_true rfl)
  have h_v971 : R 1 0 0 1 v971 v971 := (r_land hl h_v968 h_v970 (of_decide_eq_true rfl))
  have e_v971 : (v971 = 1 ↔ v968 = 1 ∧ v970 = 1) := e_land h_v968 h_v970 (of_decide_eq_true rfl)
  have h_v972 : R 1 0 4611686018427387894 4611686018695823364 v972 v972 := (r_psel hl h_v971 h_v33 h_v965 (of_decide_eq_true rfl))
  have e_v972 : v972 = if v971 = 1 then v33 else v965 := e_psel h_v971 h_v33 h_v965 (of_decide_eq_true rfl)
  have h_v973 : R 1 0 4611686010374323999 4683743612465315840 v973 v973 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v902 (of_decide_eq_true rfl))
  have e_v973 : sv v973 = sv v939 - sv v902 := e_sub h_v939 h_v902 (of_decide_eq_true rfl)
  have h_v974 : R 1 0 4611686018427387904 4611686018695823360 v974 v974 := (r_psqrt hl h_v973 (of_decide_eq_true rfl))
  have e_v974 : sv v974 = ((Nat.sqrt (v973 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v973 (of_decide_eq_true rfl)
  have h_v975 : R 1 0 4611686018427387905 4611686018695823361 v975 v975 := (r_sub hl (r_add hl h_v104 h_v974 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v975 : sv v975 = sv v104 + sv v974 := e_add h_v104 h_v974 (of_decide_eq_true rfl)
  clear h_v886 h_v892 h_v945 h_v950 h_v956 h_v961 h_v962 h_v964 h_v965 h_v967 h_v968 h_v969 h_v970 h_v971 h_v973
  have pb_v974_v877 : PB 1 v974 v877 36028797018963968 := pb_sqrt hl h_v877 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v976 : R 1 0 4611686017085210624 4647714815446351872 v976 v976 := (r_smx_pb hl 29 h_v974 h_v877 pb_v974_v877 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v976 : sv v976 = sv v974 * sv v877 := e_smx_pb 29 h_v974 h_v877 pb_v974_v877 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v977 : R 1 0 4611686018427387899 4611686018561605632 v977 v977 := (r_srdF hl h_v976 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v977 : sv v977 = sv v976 / 2 ^ 28 := e_srdF h_v976 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v978 : R 1 0 4611686018427387894 4611686018695823360 v978 v978 := (r_sub hl (r_add hl h_v977 h_v977 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v978 : sv v978 = sv v977 + sv v977 := e_add h_v977 h_v977 (of_decide_eq_true rfl)
  have pb_v975_v877 : PB 1 v975 v877 36028797287399439 := pb_sqrt1 hl h_v877 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v979 : R 1 0 4611686017085210619 4647714815714787343 v979 v979 := (r_smx_pb hl 29 h_v975 h_v877 pb_v975_v877 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v979 : sv v979 = sv v975 * sv v877 := e_smx_pb 29 h_v975 h_v877 pb_v975_v877 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v980 : R 1 0 4611686018427387899 4611686018561605634 v980 v980 := (r_srdC hl h_v979 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v980 : sv v980 = -((-sv v979) / 2 ^ 28) := e_srdC h_v979 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v981 : R 1 0 4611686018427387894 4611686018695823364 v981 v981 := (r_sub hl (r_add hl h_v980 h_v980 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v981 : sv v981 = sv v980 + sv v980 := e_add h_v980 h_v980 (of_decide_eq_true rfl)
  have h_v982 : R 1 0 0 1 v982 v982 := (r_plt hl h_v981 h_v33 (of_decide_eq_true rfl))
  have e_v982 : (v982 = 1 ↔ sv v981 < sv v33) := e_plt h_v981 h_v33 (of_decide_eq_true rfl)
  have h_v983 : R 1 0 4611686018427387894 4611686018695823364 v983 v983 := (r_psel hl h_v982 h_v981 h_v33 (of_decide_eq_true rfl))
  have e_v983 : v983 = if v982 = 1 then v981 else v33 := e_psel h_v982 h_v981 h_v33 (of_decide_eq_true rfl)
  have h_v984 : R 1 0 4611686010374323999 4683743612465315840 v984 v984 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v896 (of_decide_eq_true rfl))
  have e_v984 : sv v984 = sv v939 - sv v896 := e_sub h_v939 h_v896 (of_decide_eq_true rfl)
  have h_v985 : R 1 0 4611686018427387904 4611686018695823360 v985 v985 := (r_psqrt hl h_v984 (of_decide_eq_true rfl))
  have e_v985 : sv v985 = ((Nat.sqrt (v984 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v984 (of_decide_eq_true rfl)
  have h_v986 : R 1 0 4611686018427387905 4611686018695823361 v986 v986 := (r_sub hl (r_add hl h_v104 h_v985 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v986 : sv v986 = sv v104 + sv v985 := e_add h_v104 h_v985 (of_decide_eq_true rfl)
  have pb_v985_v878 : PB 1 v985 v878 36028797018963968 := pb_sqrt hl h_v878 29 36028797018963968 (of_decide_eq_true rfl)
  clear h_v877 h_v974 h_v975 pb_v974_v877 h_v976 h_v977 pb_v975_v877 h_v979 h_v980 h_v981 h_v982 h_v984
  have h_v987 : R 1 0 4611686017085210624 4647714815446351872 v987 v987 := (r_smx_pb hl 29 h_v985 h_v878 pb_v985_v878 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v987 : sv v987 = sv v985 * sv v878 := e_smx_pb 29 h_v985 h_v878 pb_v985_v878 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v988 : R 1 0 4611686018427387899 4611686018561605632 v988 v988 := (r_srdF hl h_v987 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v988 : sv v988 = sv v987 / 2 ^ 28 := e_srdF h_v987 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v989 : R 1 0 4611686018427387894 4611686018695823360 v989 v989 := (r_sub hl (r_add hl h_v988 h_v988 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v989 : sv v989 = sv v988 + sv v988 := e_add h_v988 h_v988 (of_decide_eq_true rfl)
  have pb_v986_v878 : PB 1 v986 v878 36028797287399439 := pb_sqrt1 hl h_v878 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v990 : R 1 0 4611686017085210619 4647714815714787343 v990 v990 := (r_smx_pb hl 29 h_v986 h_v878 pb_v986_v878 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v990 : sv v990 = sv v986 * sv v878 := e_smx_pb 29 h_v986 h_v878 pb_v986_v878 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v991 : R 1 0 4611686018427387899 4611686018561605634 v991 v991 := (r_srdC hl h_v990 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v991 : sv v991 = -((-sv v990) / 2 ^ 28) := e_srdC h_v990 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v992 : R 1 0 4611686018427387894 4611686018695823364 v992 v992 := (r_sub hl (r_add hl h_v991 h_v991 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v992 : sv v992 = sv v991 + sv v991 := e_add h_v991 h_v991 (of_decide_eq_true rfl)
  have h_v993 : R 1 0 0 1 v993 v993 := (r_plt hl h_v992 h_v33 (of_decide_eq_true rfl))
  have e_v993 : (v993 = 1 ↔ sv v992 < sv v33) := e_plt h_v992 h_v33 (of_decide_eq_true rfl)
  have h_v994 : R 1 0 4611686018427387894 4611686018695823364 v994 v994 := (r_psel hl h_v993 h_v992 h_v33 (of_decide_eq_true rfl))
  have e_v994 : v994 = if v993 = 1 then v992 else v33 := e_psel h_v993 h_v992 h_v33 (of_decide_eq_true rfl)
  have h_v995 : R 1 0 0 1 v995 v995 := (r_plt hl h_v978 h_v989 (of_decide_eq_true rfl))
  have e_v995 : (v995 = 1 ↔ sv v978 < sv v989) := e_plt h_v978 h_v989 (of_decide_eq_true rfl)
  have h_v996 : R 1 0 4611686018427387894 4611686018695823360 v996 v996 := (r_psel hl h_v995 h_v978 h_v989 (of_decide_eq_true rfl))
  have e_v996 : v996 = if v995 = 1 then v978 else v989 := e_psel h_v995 h_v978 h_v989 (of_decide_eq_true rfl)
  have h_v997 : R 1 0 0 1 v997 v997 := (r_plt hl h_v983 h_v994 (of_decide_eq_true rfl))
  have e_v997 : (v997 = 1 ↔ sv v983 < sv v994) := e_plt h_v983 h_v994 (of_decide_eq_true rfl)
  have h_v998 : R 1 0 4611686018427387894 4611686018695823364 v998 v998 := (r_psel hl h_v997 h_v994 h_v983 (of_decide_eq_true rfl))
  have e_v998 : v998 = if v997 = 1 then v994 else v983 := e_psel h_v997 h_v994 h_v983 (of_decide_eq_true rfl)
  clear h_v878 h_v978 h_v983 h_v985 h_v986 pb_v985_v878 h_v987 h_v988 h_v989 pb_v986_v878 h_v990 h_v991 h_v992 h_v993 h_v994 h_v995 h_v997
  have h_v999 : R 1 0 0 1 v999 v999 := (r_plt hl h_v966 h_v902 (of_decide_eq_true rfl))
  have e_v999 : (v999 = 1 ↔ sv v966 < sv v902) := e_plt h_v966 h_v902 (of_decide_eq_true rfl)
  have h_v1000 : R 1 0 0 1 v1000 v1000 := (r_sub hl (r_O hl) h_v999 (of_decide_eq_true rfl))
  have e_v1000 : (v1000 = 1 ↔ ¬v999 = 1) := e_not h_v999 (of_decide_eq_true rfl)
  have h_v1001 : R 1 0 0 1 v1001 v1001 := (r_plt hl h_v896 h_v966 (of_decide_eq_true rfl))
  have e_v1001 : (v1001 = 1 ↔ sv v896 < sv v966) := e_plt h_v896 h_v966 (of_decide_eq_true rfl)
  have h_v1002 : R 1 0 0 1 v1002 v1002 := (r_sub hl (r_O hl) h_v1001 (of_decide_eq_true rfl))
  have e_v1002 : (v1002 = 1 ↔ ¬v1001 = 1) := e_not h_v1001 (of_decide_eq_true rfl)
  have h_v1003 : R 1 0 0 1 v1003 v1003 := (r_land hl h_v1000 h_v1002 (of_decide_eq_true rfl))
  have e_v1003 : (v1003 = 1 ↔ v1000 = 1 ∧ v1002 = 1) := e_land h_v1000 h_v1002 (of_decide_eq_true rfl)
  have h_v1004 : R 1 0 4611686018427387894 4611686018695823364 v1004 v1004 := (r_psel hl h_v1003 h_v33 h_v998 (of_decide_eq_true rfl))
  have e_v1004 : v1004 = if v1003 = 1 then v33 else v998 := e_psel h_v1003 h_v33 h_v998 (of_decide_eq_true rfl)
  have h_v1005 : R 1 0 0 1 v1005 v1005 := (r_plt hl h_v963 h_v9 (of_decide_eq_true rfl))
  have e_v1005 : (v1005 = 1 ↔ sv v963 < sv v9) := e_plt h_v963 h_v9 (of_decide_eq_true rfl)
  have h_v1006 : R 1 0 0 1 v1006 v1006 := (r_sub hl (r_O hl) h_v1005 (of_decide_eq_true rfl))
  have e_v1006 : (v1006 = 1 ↔ ¬v1005 = 1) := e_not h_v1005 (of_decide_eq_true rfl)
  have h_v1007 : R 1 0 0 1 v1007 v1007 := (r_plt hl h_v9 h_v972 (of_decide_eq_true rfl))
  have e_v1007 : (v1007 = 1 ↔ sv v9 < sv v972) := e_plt h_v9 h_v972 (of_decide_eq_true rfl)
  have h_v1008 : R 1 0 0 1 v1008 v1008 := (r_sub hl (r_O hl) h_v1007 (of_decide_eq_true rfl))
  have e_v1008 : (v1008 = 1 ↔ ¬v1007 = 1) := e_not h_v1007 (of_decide_eq_true rfl)
  have h_v1009 : R 1 0 0 1 v1009 v1009 := (r_land hl h_v1005 h_v1008 (of_decide_eq_true rfl))
  have e_v1009 : (v1009 = 1 ↔ v1005 = 1 ∧ v1008 = 1) := e_land h_v1005 h_v1008 (of_decide_eq_true rfl)
  have h_v1010 : R 1 0 0 1 v1010 v1010 := (r_land hl h_v1005 h_v1007 (of_decide_eq_true rfl))
  have e_v1010 : (v1010 = 1 ↔ v1005 = 1 ∧ v1007 = 1) := e_land h_v1005 h_v1007 (of_decide_eq_true rfl)
  have h_v1011 : R 1 0 0 1 v1011 v1011 := (r_plt hl h_v996 h_v9 (of_decide_eq_true rfl))
  clear h_v896 h_v902 h_v998 h_v999 h_v1000 h_v1001 h_v1002 h_v1003 h_v1005 h_v1007 h_v1008
  have e_v1011 : (v1011 = 1 ↔ sv v996 < sv v9) := e_plt h_v996 h_v9 (of_decide_eq_true rfl)
  have h_v1012 : R 1 0 0 1 v1012 v1012 := (r_sub hl (r_O hl) h_v1011 (of_decide_eq_true rfl))
  have e_v1012 : (v1012 = 1 ↔ ¬v1011 = 1) := e_not h_v1011 (of_decide_eq_true rfl)
  have h_v1013 : R 1 0 0 1 v1013 v1013 := (r_plt hl h_v9 h_v1004 (of_decide_eq_true rfl))
  have e_v1013 : (v1013 = 1 ↔ sv v9 < sv v1004) := e_plt h_v9 h_v1004 (of_decide_eq_true rfl)
  have h_v1014 : R 1 0 0 1 v1014 v1014 := (r_sub hl (r_O hl) h_v1013 (of_decide_eq_true rfl))
  have e_v1014 : (v1014 = 1 ↔ ¬v1013 = 1) := e_not h_v1013 (of_decide_eq_true rfl)
  have h_v1015 : R 1 0 0 1 v1015 v1015 := (r_land hl h_v1011 h_v1014 (of_decide_eq_true rfl))
  have e_v1015 : (v1015 = 1 ↔ v1011 = 1 ∧ v1014 = 1) := e_land h_v1011 h_v1014 (of_decide_eq_true rfl)
  have h_v1016 : R 1 0 0 1 v1016 v1016 := (r_land hl h_v1011 h_v1013 (of_decide_eq_true rfl))
  have e_v1016 : (v1016 = 1 ↔ v1011 = 1 ∧ v1013 = 1) := e_land h_v1011 h_v1013 (of_decide_eq_true rfl)
  have h_v1017 : R 1 0 0 1 v1017 v1017 := (r_land hl h_v1010 h_v1016 (of_decide_eq_true rfl))
  have e_v1017 : (v1017 = 1 ↔ v1010 = 1 ∧ v1016 = 1) := e_land h_v1010 h_v1016 (of_decide_eq_true rfl)
  have h_v1018 : R 1 0 0 1 v1018 v1018 := (r_sub hl (r_O hl) h_v1017 (of_decide_eq_true rfl))
  have e_v1018 : (v1018 = 1 ↔ ¬v1017 = 1) := e_not h_v1017 (of_decide_eq_true rfl)
  have h_v1019 : R 1 0 0 1 v1019 v1019 := (r_lor hl h_v822 h_v1018 (of_decide_eq_true rfl))
  have e_v1019 : (v1019 = 1 ↔ v822 = 1 ∨ v1018 = 1) := e_lor h_v822 h_v1018 (of_decide_eq_true rfl)
  have h_v1020 : R 1 0 0 1 v1020 v1020 := (r_land hl h_v1006 h_v1016 (of_decide_eq_true rfl))
  have e_v1020 : (v1020 = 1 ↔ v1006 = 1 ∧ v1016 = 1) := e_land h_v1006 h_v1016 (of_decide_eq_true rfl)
  have h_v1021 : R 1 0 0 1 v1021 v1021 := (r_lor hl h_v1015 h_v1020 (of_decide_eq_true rfl))
  have e_v1021 : (v1021 = 1 ↔ v1015 = 1 ∨ v1020 = 1) := e_lor h_v1015 h_v1020 (of_decide_eq_true rfl)
  have h_v1022 : R 1 0 4611686018427387894 4611686018695823364 v1022 v1022 := (r_psel hl h_v1021 h_v972 h_v963 (of_decide_eq_true rfl))
  have e_v1022 : v1022 = if v1021 = 1 then v972 else v963 := e_psel h_v1021 h_v972 h_v963 (of_decide_eq_true rfl)
  have h_v1023 : R 1 0 0 1 v1023 v1023 := (r_land hl h_v1010 h_v1012 (of_decide_eq_true rfl))
  have e_v1023 : (v1023 = 1 ↔ v1010 = 1 ∧ v1012 = 1) := e_land h_v1010 h_v1012 (of_decide_eq_true rfl)
  clear h_v1006 h_v1011 h_v1012 h_v1013 h_v1014 h_v1017 h_v1018 h_v1020 h_v1021
  have h_v1024 : R 1 0 0 1 v1024 v1024 := (r_lor hl h_v1009 h_v1023 (of_decide_eq_true rfl))
  have e_v1024 : (v1024 = 1 ↔ v1009 = 1 ∨ v1023 = 1) := e_lor h_v1009 h_v1023 (of_decide_eq_true rfl)
  have h_v1025 : R 1 0 4611686018427387894 4611686018695823364 v1025 v1025 := (r_psel hl h_v1024 h_v1004 h_v996 (of_decide_eq_true rfl))
  have e_v1025 : v1025 = if v1024 = 1 then v1004 else v996 := e_psel h_v1024 h_v1004 h_v996 (of_decide_eq_true rfl)
  have h_v1026 : R 1 0 0 1 v1026 v1026 := (r_land hl h_v1009 h_v1016 (of_decide_eq_true rfl))
  have e_v1026 : (v1026 = 1 ↔ v1009 = 1 ∧ v1016 = 1) := e_land h_v1009 h_v1016 (of_decide_eq_true rfl)
  have h_v1027 : R 1 0 0 1 v1027 v1027 := (r_lor hl h_v1015 h_v1026 (of_decide_eq_true rfl))
  have e_v1027 : (v1027 = 1 ↔ v1015 = 1 ∨ v1026 = 1) := e_lor h_v1015 h_v1026 (of_decide_eq_true rfl)
  have h_v1028 : R 1 0 4611686018427387894 4611686018695823364 v1028 v1028 := (r_psel hl h_v1027 h_v963 h_v972 (of_decide_eq_true rfl))
  have e_v1028 : v1028 = if v1027 = 1 then v963 else v972 := e_psel h_v1027 h_v963 h_v972 (of_decide_eq_true rfl)
  have h_v1029 : R 1 0 0 1 v1029 v1029 := (r_land hl h_v1010 h_v1015 (of_decide_eq_true rfl))
  have e_v1029 : (v1029 = 1 ↔ v1010 = 1 ∧ v1015 = 1) := e_land h_v1010 h_v1015 (of_decide_eq_true rfl)
  have h_v1030 : R 1 0 0 1 v1030 v1030 := (r_lor hl h_v1009 h_v1029 (of_decide_eq_true rfl))
  have e_v1030 : (v1030 = 1 ↔ v1009 = 1 ∨ v1029 = 1) := e_lor h_v1009 h_v1029 (of_decide_eq_true rfl)
  have h_v1031 : R 1 0 4611686018427387894 4611686018695823364 v1031 v1031 := (r_psel hl h_v1030 h_v996 h_v1004 (of_decide_eq_true rfl))
  have e_v1031 : v1031 = if v1030 = 1 then v996 else v1004 := e_psel h_v1030 h_v996 h_v1004 (of_decide_eq_true rfl)
  have h_v1032 : R 1 0 4611686015743033304 4683743614612799504 v1032 v1032 := (r_smx hl 29 h_v1025 h_v1022 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1032 : sv v1032 = sv v1025 * sv v1022 := e_smx 29 h_v1025 h_v1022 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1033 : R 1 0 4611686018427387893 4611686018695823368 v1033 v1033 := (r_srdF hl h_v1032 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v1033 : sv v1033 = sv v1032 / 2 ^ 28 := e_srdF h_v1032 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v1034 : R 1 0 4611686015743033304 4683743614612799504 v1034 v1034 := (r_smx hl 29 h_v1031 h_v1028 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1034 : sv v1034 = sv v1031 * sv v1028 := e_smx 29 h_v1031 h_v1028 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1035 : R 1 0 4611686018427387894 4611686018695823369 v1035 v1035 := (r_srdC hl h_v1034 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v1035 : sv v1035 = -((-sv v1034) / 2 ^ 28) := e_srdC h_v1034 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1036 : R 1 0 0 1 v1036 v1036 := (r_plt hl h_v9 h_v1033 (of_decide_eq_true rfl))
  clear h_v963 h_v972 h_v996 h_v1004 h_v1009 h_v1010 h_v1015 h_v1016 h_v1022 h_v1023 h_v1024 h_v1025 h_v1026 h_v1027 h_v1028 h_v1029 h_v1030 h_v1031 h_v1032 h_v1034
  have e_v1036 : (v1036 = 1 ↔ sv v9 < sv v1033) := e_plt h_v9 h_v1033 (of_decide_eq_true rfl)
  have h_v1040 : R 1 0 0 1 v1040 v1040 := (r_plt hl h_v938 h_v9 (of_decide_eq_true rfl))
  have e_v1040 : (v1040 = 1 ↔ sv v938 < sv v9) := e_plt h_v938 h_v9 (of_decide_eq_true rfl)
  have h_v1041 : R 1 0 4611686018427387893 4611686018695823369 v1041 v1041 := (r_psel hl h_v1040 h_v1035 h_v1033 (of_decide_eq_true rfl))
  have e_v1041 : v1041 = if v1040 = 1 then v1035 else v1033 := e_psel h_v1040 h_v1035 h_v1033 (of_decide_eq_true rfl)
  have h_v1042 : R 1 0 4611686018158952439 4611686018427387915 v1042 v1042 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v1041 (of_decide_eq_true rfl))
  have e_v1042 : sv v1042 = sv v9 - sv v1041 := e_sub h_v9 h_v1041 (of_decide_eq_true rfl)
  have h_v1043 : R 1 0 0 1 v1043 v1043 := (r_plt hl h_v938 h_v1042 (of_decide_eq_true rfl))
  have e_v1043 : (v1043 = 1 ↔ sv v938 < sv v1042) := e_plt h_v938 h_v1042 (of_decide_eq_true rfl)
  have h_v1044 : R 1 0 0 1 v1044 v1044 := (r_land hl h_v1036 h_v1043 (of_decide_eq_true rfl))
  have e_v1044 : (v1044 = 1 ↔ v1036 = 1 ∧ v1043 = 1) := e_land h_v1036 h_v1043 (of_decide_eq_true rfl)
  have h_v1053 : R 1 0 4611686018427387904 4683743620518379745 v1053 v1053 := (r_smx_sq hl 29 h_v876 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1053 : sv v1053 = sv v876 * sv v876 := e_smx_sq 29 h_v876 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1054 : R 1 0 4611686018427387904 4611686018695823391 v1054 v1054 := (r_srdC hl h_v1053 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1054 : sv v1054 = -((-sv v1053) / 2 ^ 28) := e_srdC h_v1053 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1055 : R 1 0 4611686018427387904 4611686018964258878 v1055 v1055 := (r_sub hl (r_add hl h_v1054 h_v1054 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1055 : sv v1055 = sv v1054 + sv v1054 := e_add h_v1054 h_v1054 (of_decide_eq_true rfl)
  have h_v1056 : R 1 0 4611686018158952386 4611686018695823360 v1056 v1056 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1055 (of_decide_eq_true rfl))
  have e_v1056 : sv v1056 = sv v33 - sv v1055 := e_sub h_v33 h_v1055 (of_decide_eq_true rfl)
  have h_v1057 : R 1 0 0 1 v1057 v1057 := (r_plt hl h_v1056 h_v94 (of_decide_eq_true rfl))
  have e_v1057 : (v1057 = 1 ↔ sv v1056 < sv v94) := e_plt h_v1056 h_v94 (of_decide_eq_true rfl)
  have h_v1058 : R 1 0 4611686018158952386 4611686018695823360 v1058 v1058 := (r_psel hl h_v1057 h_v94 h_v1056 (of_decide_eq_true rfl))
  have e_v1058 : v1058 = if v1057 = 1 then v94 else v1056 := e_psel h_v1057 h_v94 h_v1056 (of_decide_eq_true rfl)
  have h_v1059 : R 1 0 4611686018427387904 4683743620518379745 v1059 v1059 := (r_smx_sq hl 29 h_v875 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1059 : sv v1059 = sv v875 * sv v875 := e_smx_sq 29 h_v875 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  clear h_v938 h_v1033 h_v1035 h_v1036 h_v1040 h_v1041 h_v1042 h_v1043 h_v1054 h_v1055 h_v1056 h_v1057
  have h_v1060 : R 1 0 4611686018427387904 4611686018695823390 v1060 v1060 := (r_srdF hl h_v1059 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1060 : sv v1060 = sv v1059 / 2 ^ 28 := e_srdF h_v1059 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1061 : R 1 0 4611686018427387904 4611686018964258876 v1061 v1061 := (r_sub hl (r_add hl h_v1060 h_v1060 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1061 : sv v1061 = sv v1060 + sv v1060 := e_add h_v1060 h_v1060 (of_decide_eq_true rfl)
  have h_v1062 : R 1 0 4611686018158952388 4611686018695823360 v1062 v1062 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1061 (of_decide_eq_true rfl))
  have e_v1062 : sv v1062 = sv v33 - sv v1061 := e_sub h_v33 h_v1061 (of_decide_eq_true rfl)
  have h_v1063 : R 1 0 4611686018427387904 4683743620518379745 v1063 v1063 := (r_smx_sq hl 29 h_v880 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1063 : sv v1063 = sv v880 * sv v880 := e_smx_sq 29 h_v880 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1064 : R 1 0 4611686018427387904 4611686018695823391 v1064 v1064 := (r_srdC hl h_v1063 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1064 : sv v1064 = -((-sv v1063) / 2 ^ 28) := e_srdC h_v1063 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1065 : R 1 0 4611686018427387904 4611686018964258878 v1065 v1065 := (r_sub hl (r_add hl h_v1064 h_v1064 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1065 : sv v1065 = sv v1064 + sv v1064 := e_add h_v1064 h_v1064 (of_decide_eq_true rfl)
  have h_v1066 : R 1 0 4611686018158952386 4611686018695823360 v1066 v1066 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1065 (of_decide_eq_true rfl))
  have e_v1066 : sv v1066 = sv v33 - sv v1065 := e_sub h_v33 h_v1065 (of_decide_eq_true rfl)
  have h_v1067 : R 1 0 0 1 v1067 v1067 := (r_plt hl h_v1066 h_v94 (of_decide_eq_true rfl))
  have e_v1067 : (v1067 = 1 ↔ sv v1066 < sv v94) := e_plt h_v1066 h_v94 (of_decide_eq_true rfl)
  have h_v1068 : R 1 0 4611686018158952386 4611686018695823360 v1068 v1068 := (r_psel hl h_v1067 h_v94 h_v1066 (of_decide_eq_true rfl))
  have e_v1068 : v1068 = if v1067 = 1 then v94 else v1066 := e_psel h_v1067 h_v94 h_v1066 (of_decide_eq_true rfl)
  have h_v1069 : R 1 0 4611686018427387904 4683743620518379745 v1069 v1069 := (r_smx_sq hl 29 h_v879 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1069 : sv v1069 = sv v879 * sv v879 := e_smx_sq 29 h_v879 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1070 : R 1 0 4611686018427387904 4611686018695823390 v1070 v1070 := (r_srdF hl h_v1069 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1070 : sv v1070 = sv v1069 / 2 ^ 28 := e_srdF h_v1069 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1071 : R 1 0 4611686018427387904 4611686018964258876 v1071 v1071 := (r_sub hl (r_add hl h_v1070 h_v1070 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1071 : sv v1071 = sv v1070 + sv v1070 := e_add h_v1070 h_v1070 (of_decide_eq_true rfl)
  have h_v1072 : R 1 0 4611686018158952388 4611686018695823360 v1072 v1072 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1071 (of_decide_eq_true rfl))
  clear h_v1060 h_v1061 h_v1064 h_v1065 h_v1066 h_v1067 h_v1070
  have e_v1072 : sv v1072 = sv v33 - sv v1071 := e_sub h_v33 h_v1071 (of_decide_eq_true rfl)
  have h_v1073 : R 1 0 0 1 v1073 v1073 := (r_plt hl h_v1058 h_v9 (of_decide_eq_true rfl))
  have e_v1073 : (v1073 = 1 ↔ sv v1058 < sv v9) := e_plt h_v1058 h_v9 (of_decide_eq_true rfl)
  have h_v1075 : R 1 0 0 1 v1075 v1075 := (r_plt hl h_v9 h_v1062 (of_decide_eq_true rfl))
  have e_v1075 : (v1075 = 1 ↔ sv v9 < sv v1062) := e_plt h_v9 h_v1062 (of_decide_eq_true rfl)
  have h_v1076 : R 1 0 0 1 v1076 v1076 := (r_sub hl (r_O hl) h_v1075 (of_decide_eq_true rfl))
  have e_v1076 : (v1076 = 1 ↔ ¬v1075 = 1) := e_not h_v1075 (of_decide_eq_true rfl)
  have h_v1077 : R 1 0 0 1 v1077 v1077 := (r_land hl h_v1073 h_v1076 (of_decide_eq_true rfl))
  have e_v1077 : (v1077 = 1 ↔ v1073 = 1 ∧ v1076 = 1) := e_land h_v1073 h_v1076 (of_decide_eq_true rfl)
  have h_v1078 : R 1 0 0 1 v1078 v1078 := (r_land hl h_v1073 h_v1075 (of_decide_eq_true rfl))
  have e_v1078 : (v1078 = 1 ↔ v1073 = 1 ∧ v1075 = 1) := e_land h_v1073 h_v1075 (of_decide_eq_true rfl)
  have h_v1079 : R 1 0 0 1 v1079 v1079 := (r_plt hl h_v1068 h_v9 (of_decide_eq_true rfl))
  have e_v1079 : (v1079 = 1 ↔ sv v1068 < sv v9) := e_plt h_v1068 h_v9 (of_decide_eq_true rfl)
  have h_v1081 : R 1 0 0 1 v1081 v1081 := (r_plt hl h_v9 h_v1072 (of_decide_eq_true rfl))
  have e_v1081 : (v1081 = 1 ↔ sv v9 < sv v1072) := e_plt h_v9 h_v1072 (of_decide_eq_true rfl)
  have h_v1082 : R 1 0 0 1 v1082 v1082 := (r_sub hl (r_O hl) h_v1081 (of_decide_eq_true rfl))
  have e_v1082 : (v1082 = 1 ↔ ¬v1081 = 1) := e_not h_v1081 (of_decide_eq_true rfl)
  have h_v1083 : R 1 0 0 1 v1083 v1083 := (r_land hl h_v1079 h_v1082 (of_decide_eq_true rfl))
  have e_v1083 : (v1083 = 1 ↔ v1079 = 1 ∧ v1082 = 1) := e_land h_v1079 h_v1082 (of_decide_eq_true rfl)
  have h_v1084 : R 1 0 0 1 v1084 v1084 := (r_land hl h_v1079 h_v1081 (of_decide_eq_true rfl))
  have e_v1084 : (v1084 = 1 ↔ v1079 = 1 ∧ v1081 = 1) := e_land h_v1079 h_v1081 (of_decide_eq_true rfl)
  have h_v1085 : R 1 0 0 1 v1085 v1085 := (r_land hl h_v1078 h_v1084 (of_decide_eq_true rfl))
  have e_v1085 : (v1085 = 1 ↔ v1078 = 1 ∧ v1084 = 1) := e_land h_v1078 h_v1084 (of_decide_eq_true rfl)
  have h_v1086 : R 1 0 0 1 v1086 v1086 := (r_sub hl (r_O hl) h_v1085 (of_decide_eq_true rfl))
  have e_v1086 : (v1086 = 1 ↔ ¬v1085 = 1) := e_not h_v1085 (of_decide_eq_true rfl)
  clear h_v1071 h_v1073 h_v1075 h_v1076 h_v1079 h_v1081 h_v1082 h_v1085
  have h_v1087 : R 1 0 0 1 v1087 v1087 := (r_lor hl h_v822 h_v1086 (of_decide_eq_true rfl))
  have e_v1087 : (v1087 = 1 ↔ v822 = 1 ∨ v1086 = 1) := e_lor h_v822 h_v1086 (of_decide_eq_true rfl)
  have h_v1094 : R 1 0 0 1 v1094 v1094 := (r_land hl h_v1077 h_v1084 (of_decide_eq_true rfl))
  have e_v1094 : (v1094 = 1 ↔ v1077 = 1 ∧ v1084 = 1) := e_land h_v1077 h_v1084 (of_decide_eq_true rfl)
  have h_v1095 : R 1 0 0 1 v1095 v1095 := (r_lor hl h_v1083 h_v1094 (of_decide_eq_true rfl))
  have e_v1095 : (v1095 = 1 ↔ v1083 = 1 ∨ v1094 = 1) := e_lor h_v1083 h_v1094 (of_decide_eq_true rfl)
  have h_v1096 : R 1 0 4611686018158952386 4611686018695823360 v1096 v1096 := (r_psel hl h_v1095 h_v1058 h_v1062 (of_decide_eq_true rfl))
  have e_v1096 : v1096 = if v1095 = 1 then v1058 else v1062 := e_psel h_v1095 h_v1058 h_v1062 (of_decide_eq_true rfl)
  have h_v1097 : R 1 0 0 1 v1097 v1097 := (r_land hl h_v1078 h_v1083 (of_decide_eq_true rfl))
  have e_v1097 : (v1097 = 1 ↔ v1078 = 1 ∧ v1083 = 1) := e_land h_v1078 h_v1083 (of_decide_eq_true rfl)
  have h_v1098 : R 1 0 0 1 v1098 v1098 := (r_lor hl h_v1077 h_v1097 (of_decide_eq_true rfl))
  have e_v1098 : (v1098 = 1 ↔ v1077 = 1 ∨ v1097 = 1) := e_lor h_v1077 h_v1097 (of_decide_eq_true rfl)
  have h_v1099 : R 1 0 4611686018158952386 4611686018695823360 v1099 v1099 := (r_psel hl h_v1098 h_v1068 h_v1072 (of_decide_eq_true rfl))
  have e_v1099 : v1099 = if v1098 = 1 then v1068 else v1072 := e_psel h_v1098 h_v1068 h_v1072 (of_decide_eq_true rfl)
  have h_v1102 : R 1 0 4539628407746461696 4683743645751316228 v1102 v1102 := (r_smx hl 30 h_v1099 h_v1096 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1102 : sv v1102 = sv v1099 * sv v1096 := e_smx 30 h_v1099 h_v1096 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1103 : R 1 0 4611686018158952386 4611686018695823485 v1103 v1103 := (r_srdC hl h_v1102 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v1103 : sv v1103 = -((-sv v1102) / 2 ^ 28) := e_srdC h_v1102 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v1104 : R 1 0 4611686017890516805 4611686018964258878 v1104 v1104 := (r_sub hl (r_add hl h_v783 h_OFFr (of_decide_eq_true rfl)) h_v1103 (of_decide_eq_true rfl))
  have e_v1104 : sv v1104 = sv v783 - sv v1103 := e_sub h_v783 h_v1103 (of_decide_eq_true rfl)
  have h_v1106 : R 1 0 4611686010374323999 4683743612465315840 v1106 v1106 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v1059 (of_decide_eq_true rfl))
  have e_v1106 : sv v1106 = sv v939 - sv v1059 := e_sub h_v939 h_v1059 (of_decide_eq_true rfl)
  have h_v1107 : R 1 0 4611686018427387904 4611686018695823360 v1107 v1107 := (r_psqrt hl h_v1106 (of_decide_eq_true rfl))
  have e_v1107 : sv v1107 = ((Nat.sqrt (v1106 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1106 (of_decide_eq_true rfl)
  have h_v1108 : R 1 0 4611686018427387905 4611686018695823361 v1108 v1108 := (r_sub hl (r_add hl h_v104 h_v1107 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v783 h_v1058 h_v1062 h_v1068 h_v1072 h_v1077 h_v1078 h_v1083 h_v1084 h_v1086 h_v1094 h_v1095 h_v1096 h_v1097 h_v1098 h_v1099 h_v1102 h_v1103 h_v1106
  have e_v1108 : sv v1108 = sv v104 + sv v1107 := e_add h_v104 h_v1107 (of_decide_eq_true rfl)
  have pb_v1107_v875 : PB 1 v1107 v875 36028797018963968 := pb_sqrt hl h_v875 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1109 : R 1 0 4611686017085210624 4647714815446351872 v1109 v1109 := (r_smx_pb hl 29 h_v1107 h_v875 pb_v1107_v875 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1109 : sv v1109 = sv v1107 * sv v875 := e_smx_pb 29 h_v1107 h_v875 pb_v1107_v875 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1110 : R 1 0 4611686018427387899 4611686018561605632 v1110 v1110 := (r_srdF hl h_v1109 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1110 : sv v1110 = sv v1109 / 2 ^ 28 := e_srdF h_v1109 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1111 : R 1 0 4611686018427387894 4611686018695823360 v1111 v1111 := (r_sub hl (r_add hl h_v1110 h_v1110 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1111 : sv v1111 = sv v1110 + sv v1110 := e_add h_v1110 h_v1110 (of_decide_eq_true rfl)
  have pb_v1108_v875 : PB 1 v1108 v875 36028797287399439 := pb_sqrt1 hl h_v875 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1112 : R 1 0 4611686017085210619 4647714815714787343 v1112 v1112 := (r_smx_pb hl 29 h_v1108 h_v875 pb_v1108_v875 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1112 : sv v1112 = sv v1108 * sv v875 := e_smx_pb 29 h_v1108 h_v875 pb_v1108_v875 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1113 : R 1 0 4611686018427387899 4611686018561605634 v1113 v1113 := (r_srdC hl h_v1112 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1113 : sv v1113 = -((-sv v1112) / 2 ^ 28) := e_srdC h_v1112 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1114 : R 1 0 4611686018427387894 4611686018695823364 v1114 v1114 := (r_sub hl (r_add hl h_v1113 h_v1113 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1114 : sv v1114 = sv v1113 + sv v1113 := e_add h_v1113 h_v1113 (of_decide_eq_true rfl)
  have h_v1115 : R 1 0 0 1 v1115 v1115 := (r_plt hl h_v1114 h_v33 (of_decide_eq_true rfl))
  have e_v1115 : (v1115 = 1 ↔ sv v1114 < sv v33) := e_plt h_v1114 h_v33 (of_decide_eq_true rfl)
  have h_v1116 : R 1 0 4611686018427387894 4611686018695823364 v1116 v1116 := (r_psel hl h_v1115 h_v1114 h_v33 (of_decide_eq_true rfl))
  have e_v1116 : v1116 = if v1115 = 1 then v1114 else v33 := e_psel h_v1115 h_v1114 h_v33 (of_decide_eq_true rfl)
  have h_v1117 : R 1 0 4611686010374323999 4683743612465315840 v1117 v1117 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v1053 (of_decide_eq_true rfl))
  have e_v1117 : sv v1117 = sv v939 - sv v1053 := e_sub h_v939 h_v1053 (of_decide_eq_true rfl)
  have h_v1118 : R 1 0 4611686018427387904 4611686018695823360 v1118 v1118 := (r_psqrt hl h_v1117 (of_decide_eq_true rfl))
  have e_v1118 : sv v1118 = ((Nat.sqrt (v1117 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1117 (of_decide_eq_true rfl)
  have h_v1119 : R 1 0 4611686018427387905 4611686018695823361 v1119 v1119 := (r_sub hl (r_add hl h_v104 h_v1118 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1119 : sv v1119 = sv v104 + sv v1118 := e_add h_v104 h_v1118 (of_decide_eq_true rfl)
  clear h_v875 h_v1107 h_v1108 pb_v1107_v875 h_v1109 h_v1110 pb_v1108_v875 h_v1112 h_v1113 h_v1114 h_v1115 h_v1117
  have pb_v1118_v876 : PB 1 v1118 v876 36028797018963968 := pb_sqrt hl h_v876 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1120 : R 1 0 4611686017085210624 4647714815446351872 v1120 v1120 := (r_smx_pb hl 29 h_v1118 h_v876 pb_v1118_v876 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1120 : sv v1120 = sv v1118 * sv v876 := e_smx_pb 29 h_v1118 h_v876 pb_v1118_v876 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1121 : R 1 0 4611686018427387899 4611686018561605632 v1121 v1121 := (r_srdF hl h_v1120 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1121 : sv v1121 = sv v1120 / 2 ^ 28 := e_srdF h_v1120 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1122 : R 1 0 4611686018427387894 4611686018695823360 v1122 v1122 := (r_sub hl (r_add hl h_v1121 h_v1121 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1122 : sv v1122 = sv v1121 + sv v1121 := e_add h_v1121 h_v1121 (of_decide_eq_true rfl)
  have pb_v1119_v876 : PB 1 v1119 v876 36028797287399439 := pb_sqrt1 hl h_v876 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1123 : R 1 0 4611686017085210619 4647714815714787343 v1123 v1123 := (r_smx_pb hl 29 h_v1119 h_v876 pb_v1119_v876 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1123 : sv v1123 = sv v1119 * sv v876 := e_smx_pb 29 h_v1119 h_v876 pb_v1119_v876 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1124 : R 1 0 4611686018427387899 4611686018561605634 v1124 v1124 := (r_srdC hl h_v1123 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1124 : sv v1124 = -((-sv v1123) / 2 ^ 28) := e_srdC h_v1123 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1125 : R 1 0 4611686018427387894 4611686018695823364 v1125 v1125 := (r_sub hl (r_add hl h_v1124 h_v1124 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1125 : sv v1125 = sv v1124 + sv v1124 := e_add h_v1124 h_v1124 (of_decide_eq_true rfl)
  have h_v1126 : R 1 0 0 1 v1126 v1126 := (r_plt hl h_v1125 h_v33 (of_decide_eq_true rfl))
  have e_v1126 : (v1126 = 1 ↔ sv v1125 < sv v33) := e_plt h_v1125 h_v33 (of_decide_eq_true rfl)
  have h_v1127 : R 1 0 4611686018427387894 4611686018695823364 v1127 v1127 := (r_psel hl h_v1126 h_v1125 h_v33 (of_decide_eq_true rfl))
  have e_v1127 : v1127 = if v1126 = 1 then v1125 else v33 := e_psel h_v1126 h_v1125 h_v33 (of_decide_eq_true rfl)
  have h_v1128 : R 1 0 0 1 v1128 v1128 := (r_plt hl h_v1111 h_v1122 (of_decide_eq_true rfl))
  have e_v1128 : (v1128 = 1 ↔ sv v1111 < sv v1122) := e_plt h_v1111 h_v1122 (of_decide_eq_true rfl)
  have h_v1129 : R 1 0 4611686018427387894 4611686018695823360 v1129 v1129 := (r_psel hl h_v1128 h_v1111 h_v1122 (of_decide_eq_true rfl))
  have e_v1129 : v1129 = if v1128 = 1 then v1111 else v1122 := e_psel h_v1128 h_v1111 h_v1122 (of_decide_eq_true rfl)
  have h_v1130 : R 1 0 0 1 v1130 v1130 := (r_plt hl h_v1116 h_v1127 (of_decide_eq_true rfl))
  have e_v1130 : (v1130 = 1 ↔ sv v1116 < sv v1127) := e_plt h_v1116 h_v1127 (of_decide_eq_true rfl)
  have h_v1131 : R 1 0 4611686018427387894 4611686018695823364 v1131 v1131 := (r_psel hl h_v1130 h_v1127 h_v1116 (of_decide_eq_true rfl))
  clear h_v876 h_v1111 h_v1118 h_v1119 pb_v1118_v876 h_v1120 h_v1121 h_v1122 pb_v1119_v876 h_v1123 h_v1124 h_v1125 h_v1126 h_v1128
  have e_v1131 : v1131 = if v1130 = 1 then v1127 else v1116 := e_psel h_v1130 h_v1127 h_v1116 (of_decide_eq_true rfl)
  have h_v1132 : R 1 0 0 1 v1132 v1132 := (r_plt hl h_v966 h_v1059 (of_decide_eq_true rfl))
  have e_v1132 : (v1132 = 1 ↔ sv v966 < sv v1059) := e_plt h_v966 h_v1059 (of_decide_eq_true rfl)
  have h_v1133 : R 1 0 0 1 v1133 v1133 := (r_sub hl (r_O hl) h_v1132 (of_decide_eq_true rfl))
  have e_v1133 : (v1133 = 1 ↔ ¬v1132 = 1) := e_not h_v1132 (of_decide_eq_true rfl)
  have h_v1134 : R 1 0 0 1 v1134 v1134 := (r_plt hl h_v1053 h_v966 (of_decide_eq_true rfl))
  have e_v1134 : (v1134 = 1 ↔ sv v1053 < sv v966) := e_plt h_v1053 h_v966 (of_decide_eq_true rfl)
  have h_v1135 : R 1 0 0 1 v1135 v1135 := (r_sub hl (r_O hl) h_v1134 (of_decide_eq_true rfl))
  have e_v1135 : (v1135 = 1 ↔ ¬v1134 = 1) := e_not h_v1134 (of_decide_eq_true rfl)
  have h_v1136 : R 1 0 0 1 v1136 v1136 := (r_land hl h_v1133 h_v1135 (of_decide_eq_true rfl))
  have e_v1136 : (v1136 = 1 ↔ v1133 = 1 ∧ v1135 = 1) := e_land h_v1133 h_v1135 (of_decide_eq_true rfl)
  have h_v1137 : R 1 0 4611686018427387894 4611686018695823364 v1137 v1137 := (r_psel hl h_v1136 h_v33 h_v1131 (of_decide_eq_true rfl))
  have e_v1137 : v1137 = if v1136 = 1 then v33 else v1131 := e_psel h_v1136 h_v33 h_v1131 (of_decide_eq_true rfl)
  have h_v1138 : R 1 0 4611686010374323999 4683743612465315840 v1138 v1138 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v1069 (of_decide_eq_true rfl))
  have e_v1138 : sv v1138 = sv v939 - sv v1069 := e_sub h_v939 h_v1069 (of_decide_eq_true rfl)
  have h_v1139 : R 1 0 4611686018427387904 4611686018695823360 v1139 v1139 := (r_psqrt hl h_v1138 (of_decide_eq_true rfl))
  have e_v1139 : sv v1139 = ((Nat.sqrt (v1138 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1138 (of_decide_eq_true rfl)
  have h_v1140 : R 1 0 4611686018427387905 4611686018695823361 v1140 v1140 := (r_sub hl (r_add hl h_v104 h_v1139 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1140 : sv v1140 = sv v104 + sv v1139 := e_add h_v104 h_v1139 (of_decide_eq_true rfl)
  have pb_v1139_v879 : PB 1 v1139 v879 36028797018963968 := pb_sqrt hl h_v879 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1141 : R 1 0 4611686017085210624 4647714815446351872 v1141 v1141 := (r_smx_pb hl 29 h_v1139 h_v879 pb_v1139_v879 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1141 : sv v1141 = sv v1139 * sv v879 := e_smx_pb 29 h_v1139 h_v879 pb_v1139_v879 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1142 : R 1 0 4611686018427387899 4611686018561605632 v1142 v1142 := (r_srdF hl h_v1141 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1142 : sv v1142 = sv v1141 / 2 ^ 28 := e_srdF h_v1141 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1143 : R 1 0 4611686018427387894 4611686018695823360 v1143 v1143 := (r_sub hl (r_add hl h_v1142 h_v1142 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v1053 h_v1059 h_v1116 h_v1127 h_v1130 h_v1131 h_v1132 h_v1133 h_v1134 h_v1135 h_v1136 h_v1138 h_v1139 pb_v1139_v879 h_v1141
  have e_v1143 : sv v1143 = sv v1142 + sv v1142 := e_add h_v1142 h_v1142 (of_decide_eq_true rfl)
  have pb_v1140_v879 : PB 1 v1140 v879 36028797287399439 := pb_sqrt1 hl h_v879 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1144 : R 1 0 4611686017085210619 4647714815714787343 v1144 v1144 := (r_smx_pb hl 29 h_v1140 h_v879 pb_v1140_v879 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1144 : sv v1144 = sv v1140 * sv v879 := e_smx_pb 29 h_v1140 h_v879 pb_v1140_v879 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1145 : R 1 0 4611686018427387899 4611686018561605634 v1145 v1145 := (r_srdC hl h_v1144 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1145 : sv v1145 = -((-sv v1144) / 2 ^ 28) := e_srdC h_v1144 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1146 : R 1 0 4611686018427387894 4611686018695823364 v1146 v1146 := (r_sub hl (r_add hl h_v1145 h_v1145 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1146 : sv v1146 = sv v1145 + sv v1145 := e_add h_v1145 h_v1145 (of_decide_eq_true rfl)
  have h_v1147 : R 1 0 0 1 v1147 v1147 := (r_plt hl h_v1146 h_v33 (of_decide_eq_true rfl))
  have e_v1147 : (v1147 = 1 ↔ sv v1146 < sv v33) := e_plt h_v1146 h_v33 (of_decide_eq_true rfl)
  have h_v1148 : R 1 0 4611686018427387894 4611686018695823364 v1148 v1148 := (r_psel hl h_v1147 h_v1146 h_v33 (of_decide_eq_true rfl))
  have e_v1148 : v1148 = if v1147 = 1 then v1146 else v33 := e_psel h_v1147 h_v1146 h_v33 (of_decide_eq_true rfl)
  have h_v1149 : R 1 0 4611686010374323999 4683743612465315840 v1149 v1149 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v1063 (of_decide_eq_true rfl))
  have e_v1149 : sv v1149 = sv v939 - sv v1063 := e_sub h_v939 h_v1063 (of_decide_eq_true rfl)
  have h_v1150 : R 1 0 4611686018427387904 4611686018695823360 v1150 v1150 := (r_psqrt hl h_v1149 (of_decide_eq_true rfl))
  have e_v1150 : sv v1150 = ((Nat.sqrt (v1149 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1149 (of_decide_eq_true rfl)
  have h_v1151 : R 1 0 4611686018427387905 4611686018695823361 v1151 v1151 := (r_sub hl (r_add hl h_v104 h_v1150 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1151 : sv v1151 = sv v104 + sv v1150 := e_add h_v104 h_v1150 (of_decide_eq_true rfl)
  have pb_v1150_v880 : PB 1 v1150 v880 36028797018963968 := pb_sqrt hl h_v880 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1152 : R 1 0 4611686017085210624 4647714815446351872 v1152 v1152 := (r_smx_pb hl 29 h_v1150 h_v880 pb_v1150_v880 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1152 : sv v1152 = sv v1150 * sv v880 := e_smx_pb 29 h_v1150 h_v880 pb_v1150_v880 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1153 : R 1 0 4611686018427387899 4611686018561605632 v1153 v1153 := (r_srdF hl h_v1152 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1153 : sv v1153 = sv v1152 / 2 ^ 28 := e_srdF h_v1152 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1154 : R 1 0 4611686018427387894 4611686018695823360 v1154 v1154 := (r_sub hl (r_add hl h_v1153 h_v1153 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1154 : sv v1154 = sv v1153 + sv v1153 := e_add h_v1153 h_v1153 (of_decide_eq_true rfl)
  clear h_v104 h_v879 h_v939 h_v1140 h_v1142 pb_v1140_v879 h_v1144 h_v1145 h_v1146 h_v1147 h_v1149 h_v1150 pb_v1150_v880 h_v1152 h_v1153
  have pb_v1151_v880 : PB 1 v1151 v880 36028797287399439 := pb_sqrt1 hl h_v880 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1155 : R 1 0 4611686017085210619 4647714815714787343 v1155 v1155 := (r_smx_pb hl 29 h_v1151 h_v880 pb_v1151_v880 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1155 : sv v1155 = sv v1151 * sv v880 := e_smx_pb 29 h_v1151 h_v880 pb_v1151_v880 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1156 : R 1 0 4611686018427387899 4611686018561605634 v1156 v1156 := (r_srdC hl h_v1155 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1156 : sv v1156 = -((-sv v1155) / 2 ^ 28) := e_srdC h_v1155 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1157 : R 1 0 4611686018427387894 4611686018695823364 v1157 v1157 := (r_sub hl (r_add hl h_v1156 h_v1156 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1157 : sv v1157 = sv v1156 + sv v1156 := e_add h_v1156 h_v1156 (of_decide_eq_true rfl)
  have h_v1158 : R 1 0 0 1 v1158 v1158 := (r_plt hl h_v1157 h_v33 (of_decide_eq_true rfl))
  have e_v1158 : (v1158 = 1 ↔ sv v1157 < sv v33) := e_plt h_v1157 h_v33 (of_decide_eq_true rfl)
  have h_v1159 : R 1 0 4611686018427387894 4611686018695823364 v1159 v1159 := (r_psel hl h_v1158 h_v1157 h_v33 (of_decide_eq_true rfl))
  have e_v1159 : v1159 = if v1158 = 1 then v1157 else v33 := e_psel h_v1158 h_v1157 h_v33 (of_decide_eq_true rfl)
  have h_v1160 : R 1 0 0 1 v1160 v1160 := (r_plt hl h_v1143 h_v1154 (of_decide_eq_true rfl))
  have e_v1160 : (v1160 = 1 ↔ sv v1143 < sv v1154) := e_plt h_v1143 h_v1154 (of_decide_eq_true rfl)
  have h_v1161 : R 1 0 4611686018427387894 4611686018695823360 v1161 v1161 := (r_psel hl h_v1160 h_v1143 h_v1154 (of_decide_eq_true rfl))
  have e_v1161 : v1161 = if v1160 = 1 then v1143 else v1154 := e_psel h_v1160 h_v1143 h_v1154 (of_decide_eq_true rfl)
  have h_v1162 : R 1 0 0 1 v1162 v1162 := (r_plt hl h_v1148 h_v1159 (of_decide_eq_true rfl))
  have e_v1162 : (v1162 = 1 ↔ sv v1148 < sv v1159) := e_plt h_v1148 h_v1159 (of_decide_eq_true rfl)
  have h_v1163 : R 1 0 4611686018427387894 4611686018695823364 v1163 v1163 := (r_psel hl h_v1162 h_v1159 h_v1148 (of_decide_eq_true rfl))
  have e_v1163 : v1163 = if v1162 = 1 then v1159 else v1148 := e_psel h_v1162 h_v1159 h_v1148 (of_decide_eq_true rfl)
  have h_v1164 : R 1 0 0 1 v1164 v1164 := (r_plt hl h_v966 h_v1069 (of_decide_eq_true rfl))
  have e_v1164 : (v1164 = 1 ↔ sv v966 < sv v1069) := e_plt h_v966 h_v1069 (of_decide_eq_true rfl)
  have h_v1165 : R 1 0 0 1 v1165 v1165 := (r_sub hl (r_O hl) h_v1164 (of_decide_eq_true rfl))
  have e_v1165 : (v1165 = 1 ↔ ¬v1164 = 1) := e_not h_v1164 (of_decide_eq_true rfl)
  have h_v1166 : R 1 0 0 1 v1166 v1166 := (r_plt hl h_v1063 h_v966 (of_decide_eq_true rfl))
  have e_v1166 : (v1166 = 1 ↔ sv v1063 < sv v966) := e_plt h_v1063 h_v966 (of_decide_eq_true rfl)
  clear h_v880 h_v966 h_v1063 h_v1069 h_v1143 h_v1148 h_v1151 h_v1154 pb_v1151_v880 h_v1155 h_v1156 h_v1157 h_v1158 h_v1159 h_v1160 h_v1162 h_v1164
  have h_v1167 : R 1 0 0 1 v1167 v1167 := (r_sub hl (r_O hl) h_v1166 (of_decide_eq_true rfl))
  have e_v1167 : (v1167 = 1 ↔ ¬v1166 = 1) := e_not h_v1166 (of_decide_eq_true rfl)
  have h_v1168 : R 1 0 0 1 v1168 v1168 := (r_land hl h_v1165 h_v1167 (of_decide_eq_true rfl))
  have e_v1168 : (v1168 = 1 ↔ v1165 = 1 ∧ v1167 = 1) := e_land h_v1165 h_v1167 (of_decide_eq_true rfl)
  have h_v1169 : R 1 0 4611686018427387894 4611686018695823364 v1169 v1169 := (r_psel hl h_v1168 h_v33 h_v1163 (of_decide_eq_true rfl))
  have e_v1169 : v1169 = if v1168 = 1 then v33 else v1163 := e_psel h_v1168 h_v33 h_v1163 (of_decide_eq_true rfl)
  have h_v1170 : R 1 0 0 1 v1170 v1170 := (r_plt hl h_v1129 h_v9 (of_decide_eq_true rfl))
  have e_v1170 : (v1170 = 1 ↔ sv v1129 < sv v9) := e_plt h_v1129 h_v9 (of_decide_eq_true rfl)
  have h_v1171 : R 1 0 0 1 v1171 v1171 := (r_sub hl (r_O hl) h_v1170 (of_decide_eq_true rfl))
  have e_v1171 : (v1171 = 1 ↔ ¬v1170 = 1) := e_not h_v1170 (of_decide_eq_true rfl)
  have h_v1172 : R 1 0 0 1 v1172 v1172 := (r_plt hl h_v9 h_v1137 (of_decide_eq_true rfl))
  have e_v1172 : (v1172 = 1 ↔ sv v9 < sv v1137) := e_plt h_v9 h_v1137 (of_decide_eq_true rfl)
  have h_v1173 : R 1 0 0 1 v1173 v1173 := (r_sub hl (r_O hl) h_v1172 (of_decide_eq_true rfl))
  have e_v1173 : (v1173 = 1 ↔ ¬v1172 = 1) := e_not h_v1172 (of_decide_eq_true rfl)
  have h_v1174 : R 1 0 0 1 v1174 v1174 := (r_land hl h_v1170 h_v1173 (of_decide_eq_true rfl))
  have e_v1174 : (v1174 = 1 ↔ v1170 = 1 ∧ v1173 = 1) := e_land h_v1170 h_v1173 (of_decide_eq_true rfl)
  have h_v1175 : R 1 0 0 1 v1175 v1175 := (r_land hl h_v1170 h_v1172 (of_decide_eq_true rfl))
  have e_v1175 : (v1175 = 1 ↔ v1170 = 1 ∧ v1172 = 1) := e_land h_v1170 h_v1172 (of_decide_eq_true rfl)
  have h_v1176 : R 1 0 0 1 v1176 v1176 := (r_plt hl h_v1161 h_v9 (of_decide_eq_true rfl))
  have e_v1176 : (v1176 = 1 ↔ sv v1161 < sv v9) := e_plt h_v1161 h_v9 (of_decide_eq_true rfl)
  have h_v1177 : R 1 0 0 1 v1177 v1177 := (r_sub hl (r_O hl) h_v1176 (of_decide_eq_true rfl))
  have e_v1177 : (v1177 = 1 ↔ ¬v1176 = 1) := e_not h_v1176 (of_decide_eq_true rfl)
  have h_v1178 : R 1 0 0 1 v1178 v1178 := (r_plt hl h_v9 h_v1169 (of_decide_eq_true rfl))
  have e_v1178 : (v1178 = 1 ↔ sv v9 < sv v1169) := e_plt h_v9 h_v1169 (of_decide_eq_true rfl)
  have h_v1179 : R 1 0 0 1 v1179 v1179 := (r_sub hl (r_O hl) h_v1178 (of_decide_eq_true rfl))
  clear h_v1163 h_v1165 h_v1166 h_v1167 h_v1168 h_v1170 h_v1172 h_v1173
  have e_v1179 : (v1179 = 1 ↔ ¬v1178 = 1) := e_not h_v1178 (of_decide_eq_true rfl)
  have h_v1180 : R 1 0 0 1 v1180 v1180 := (r_land hl h_v1176 h_v1179 (of_decide_eq_true rfl))
  have e_v1180 : (v1180 = 1 ↔ v1176 = 1 ∧ v1179 = 1) := e_land h_v1176 h_v1179 (of_decide_eq_true rfl)
  have h_v1181 : R 1 0 0 1 v1181 v1181 := (r_land hl h_v1176 h_v1178 (of_decide_eq_true rfl))
  have e_v1181 : (v1181 = 1 ↔ v1176 = 1 ∧ v1178 = 1) := e_land h_v1176 h_v1178 (of_decide_eq_true rfl)
  have h_v1182 : R 1 0 0 1 v1182 v1182 := (r_land hl h_v1175 h_v1181 (of_decide_eq_true rfl))
  have e_v1182 : (v1182 = 1 ↔ v1175 = 1 ∧ v1181 = 1) := e_land h_v1175 h_v1181 (of_decide_eq_true rfl)
  have h_v1183 : R 1 0 0 1 v1183 v1183 := (r_sub hl (r_O hl) h_v1182 (of_decide_eq_true rfl))
  have e_v1183 : (v1183 = 1 ↔ ¬v1182 = 1) := e_not h_v1182 (of_decide_eq_true rfl)
  have h_v1184 : R 1 0 0 1 v1184 v1184 := (r_lor hl h_v822 h_v1183 (of_decide_eq_true rfl))
  have e_v1184 : (v1184 = 1 ↔ v822 = 1 ∨ v1183 = 1) := e_lor h_v822 h_v1183 (of_decide_eq_true rfl)
  have h_v1185 : R 1 0 0 1 v1185 v1185 := (r_land hl h_v1171 h_v1181 (of_decide_eq_true rfl))
  have e_v1185 : (v1185 = 1 ↔ v1171 = 1 ∧ v1181 = 1) := e_land h_v1171 h_v1181 (of_decide_eq_true rfl)
  have h_v1186 : R 1 0 0 1 v1186 v1186 := (r_lor hl h_v1180 h_v1185 (of_decide_eq_true rfl))
  have e_v1186 : (v1186 = 1 ↔ v1180 = 1 ∨ v1185 = 1) := e_lor h_v1180 h_v1185 (of_decide_eq_true rfl)
  have h_v1187 : R 1 0 4611686018427387894 4611686018695823364 v1187 v1187 := (r_psel hl h_v1186 h_v1137 h_v1129 (of_decide_eq_true rfl))
  have e_v1187 : v1187 = if v1186 = 1 then v1137 else v1129 := e_psel h_v1186 h_v1137 h_v1129 (of_decide_eq_true rfl)
  have h_v1188 : R 1 0 0 1 v1188 v1188 := (r_land hl h_v1175 h_v1177 (of_decide_eq_true rfl))
  have e_v1188 : (v1188 = 1 ↔ v1175 = 1 ∧ v1177 = 1) := e_land h_v1175 h_v1177 (of_decide_eq_true rfl)
  have h_v1189 : R 1 0 0 1 v1189 v1189 := (r_lor hl h_v1174 h_v1188 (of_decide_eq_true rfl))
  have e_v1189 : (v1189 = 1 ↔ v1174 = 1 ∨ v1188 = 1) := e_lor h_v1174 h_v1188 (of_decide_eq_true rfl)
  have h_v1190 : R 1 0 4611686018427387894 4611686018695823364 v1190 v1190 := (r_psel hl h_v1189 h_v1169 h_v1161 (of_decide_eq_true rfl))
  have e_v1190 : v1190 = if v1189 = 1 then v1169 else v1161 := e_psel h_v1189 h_v1169 h_v1161 (of_decide_eq_true rfl)
  have h_v1191 : R 1 0 0 1 v1191 v1191 := (r_land hl h_v1174 h_v1181 (of_decide_eq_true rfl))
  have e_v1191 : (v1191 = 1 ↔ v1174 = 1 ∧ v1181 = 1) := e_land h_v1174 h_v1181 (of_decide_eq_true rfl)
  clear h_v822 h_v1171 h_v1176 h_v1177 h_v1178 h_v1179 h_v1181 h_v1182 h_v1183 h_v1185 h_v1186 h_v1188 h_v1189
  have h_v1192 : R 1 0 0 1 v1192 v1192 := (r_lor hl h_v1180 h_v1191 (of_decide_eq_true rfl))
  have e_v1192 : (v1192 = 1 ↔ v1180 = 1 ∨ v1191 = 1) := e_lor h_v1180 h_v1191 (of_decide_eq_true rfl)
  have h_v1193 : R 1 0 4611686018427387894 4611686018695823364 v1193 v1193 := (r_psel hl h_v1192 h_v1129 h_v1137 (of_decide_eq_true rfl))
  have e_v1193 : v1193 = if v1192 = 1 then v1129 else v1137 := e_psel h_v1192 h_v1129 h_v1137 (of_decide_eq_true rfl)
  have h_v1194 : R 1 0 0 1 v1194 v1194 := (r_land hl h_v1175 h_v1180 (of_decide_eq_true rfl))
  have e_v1194 : (v1194 = 1 ↔ v1175 = 1 ∧ v1180 = 1) := e_land h_v1175 h_v1180 (of_decide_eq_true rfl)
  have h_v1195 : R 1 0 0 1 v1195 v1195 := (r_lor hl h_v1174 h_v1194 (of_decide_eq_true rfl))
  have e_v1195 : (v1195 = 1 ↔ v1174 = 1 ∨ v1194 = 1) := e_lor h_v1174 h_v1194 (of_decide_eq_true rfl)
  have h_v1196 : R 1 0 4611686018427387894 4611686018695823364 v1196 v1196 := (r_psel hl h_v1195 h_v1161 h_v1169 (of_decide_eq_true rfl))
  have e_v1196 : v1196 = if v1195 = 1 then v1161 else v1169 := e_psel h_v1195 h_v1161 h_v1169 (of_decide_eq_true rfl)
  have h_v1197 : R 1 0 4611686015743033304 4683743614612799504 v1197 v1197 := (r_smx hl 29 h_v1190 h_v1187 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1197 : sv v1197 = sv v1190 * sv v1187 := e_smx 29 h_v1190 h_v1187 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1198 : R 1 0 4611686018427387893 4611686018695823368 v1198 v1198 := (r_srdF hl h_v1197 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v1198 : sv v1198 = sv v1197 / 2 ^ 28 := e_srdF h_v1197 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v1199 : R 1 0 4611686015743033304 4683743614612799504 v1199 v1199 := (r_smx hl 29 h_v1196 h_v1193 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1199 : sv v1199 = sv v1196 * sv v1193 := e_smx 29 h_v1196 h_v1193 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1200 : R 1 0 4611686018427387894 4611686018695823369 v1200 v1200 := (r_srdC hl h_v1199 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v1200 : sv v1200 = -((-sv v1199) / 2 ^ 28) := e_srdC h_v1199 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1201 : R 1 0 0 1 v1201 v1201 := (r_plt hl h_v9 h_v1198 (of_decide_eq_true rfl))
  have e_v1201 : (v1201 = 1 ↔ sv v9 < sv v1198) := e_plt h_v9 h_v1198 (of_decide_eq_true rfl)
  have h_v1202 : R 1 0 0 1 v1202 v1202 := (r_sub hl (r_O hl) h_v1201 (of_decide_eq_true rfl))
  have e_v1202 : (v1202 = 1 ↔ ¬v1201 = 1) := e_not h_v1201 (of_decide_eq_true rfl)
  have h_v1203 : R 1 0 0 1 v1203 v1203 := (r_plt hl h_v1104 h_v9 (of_decide_eq_true rfl))
  have e_v1203 : (v1203 = 1 ↔ sv v1104 < sv v9) := e_plt h_v1104 h_v9 (of_decide_eq_true rfl)
  have h_v1204 : R 1 0 4611686018427387893 4611686018695823369 v1204 v1204 := (r_psel hl h_v1203 h_v1198 h_v1200 (of_decide_eq_true rfl))
  clear h_v1129 h_v1137 h_v1161 h_v1169 h_v1174 h_v1175 h_v1180 h_v1187 h_v1190 h_v1191 h_v1192 h_v1193 h_v1194 h_v1195 h_v1196 h_v1197 h_v1199
  have e_v1204 : v1204 = if v1203 = 1 then v1198 else v1200 := e_psel h_v1203 h_v1198 h_v1200 (of_decide_eq_true rfl)
  have h_v1207 : R 1 0 0 1 v1207 v1207 := (r_plt hl h_v1204 h_v1104 (of_decide_eq_true rfl))
  have e_v1207 : (v1207 = 1 ↔ sv v1204 < sv v1104) := e_plt h_v1204 h_v1104 (of_decide_eq_true rfl)
  have h_v1208 : R 1 0 0 1 v1208 v1208 := (r_land hl h_v1201 h_v1207 (of_decide_eq_true rfl))
  have e_v1208 : (v1208 = 1 ↔ v1201 = 1 ∧ v1207 = 1) := e_land h_v1201 h_v1207 (of_decide_eq_true rfl)
  have h_v1209 : R 1 0 4611686018158952439 4611686018427387915 v1209 v1209 := (r_sub hl (r_add hl h_v9 h_OFFr (of_decide_eq_true rfl)) h_v1204 (of_decide_eq_true rfl))
  have e_v1209 : sv v1209 = sv v9 - sv v1204 := e_sub h_v9 h_v1204 (of_decide_eq_true rfl)
  have h_v1210 : R 1 0 0 1 v1210 v1210 := (r_plt hl h_v1209 h_v1104 (of_decide_eq_true rfl))
  have e_v1210 : (v1210 = 1 ↔ sv v1209 < sv v1104) := e_plt h_v1209 h_v1104 (of_decide_eq_true rfl)
  have h_v1211 : R 1 0 0 1 v1211 v1211 := (r_sub hl (r_O hl) h_v1210 (of_decide_eq_true rfl))
  have e_v1211 : (v1211 = 1 ↔ ¬v1210 = 1) := e_not h_v1210 (of_decide_eq_true rfl)
  have h_v1212 : R 1 0 0 1 v1212 v1212 := (r_lor hl h_v1202 h_v1211 (of_decide_eq_true rfl))
  have e_v1212 : (v1212 = 1 ↔ v1202 = 1 ∨ v1211 = 1) := e_lor h_v1202 h_v1211 (of_decide_eq_true rfl)
  have h_v1213 : R 1 0 4611686017890516805 4611686018964258878 v1213 v1213 := (r_psel hl h_v1212 h_v94 h_v1104 (of_decide_eq_true rfl))
  have e_v1213 : v1213 = if v1212 = 1 then v94 else v1104 := e_psel h_v1212 h_v94 h_v1104 (of_decide_eq_true rfl)
  have h_v1214 : R 1 0 4611686018427387893 4611686018695823369 v1214 v1214 := (r_psel hl h_v1212 h_v33 h_v1204 (of_decide_eq_true rfl))
  have e_v1214 : v1214 = if v1212 = 1 then v33 else v1204 := e_psel h_v1212 h_v33 h_v1204 (of_decide_eq_true rfl)
  have h_v1215 : R 1 0 0 1 v1215 v1215 := (r_lor hl h_v1044 h_v1208 (of_decide_eq_true rfl))
  have e_v1215 : (v1215 = 1 ↔ v1044 = 1 ∨ v1208 = 1) := e_lor h_v1044 h_v1208 (of_decide_eq_true rfl)
  have h_v1233 : R 1 0 4611686018427387904 4611686019501129727 v1233 v1233 := (r1_hxa hb_H1 0 (of_decide_eq_true rfl))
  have e_v1233 : sv v1233 = ((H1 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H1 0 (of_decide_eq_true rfl)
  have h_v1234 : R 1 0 0 1 v1234 v1234 := (r_plt hl h_v1233 h_v20 (of_decide_eq_true rfl))
  have e_v1234 : (v1234 = 1 ↔ sv v1233 < sv v20) := e_plt h_v1233 h_v20 (of_decide_eq_true rfl)
  have h_v1235 : R 1 0 0 1 v1235 v1235 := (r_sub hl (r_O hl) h_v1234 (of_decide_eq_true rfl))
  have e_v1235 : (v1235 = 1 ↔ ¬v1234 = 1) := e_not h_v1234 (of_decide_eq_true rfl)
  clear h_v94 h_v1104 h_v1198 h_v1200 h_v1201 h_v1202 h_v1203 h_v1204 h_v1207 h_v1208 h_v1209 h_v1210 h_v1211 h_v1212 h_v1234
  have h_t1233_1 : R 1 0 4611686018427387904 4611686018695823363 t1233.1 t1233.1 := r_sc1 hl h_v1233 (of_decide_eq_true rfl)
  have h_t1233_2 : R 1 0 4611686018158952445 4611686018695823363 t1233.2 t1233.2 := r_sc2 hl h_v1233 (of_decide_eq_true rfl)
  have e_t1233_1 : sv t1233.1 = (sc28pS (scArg v1233)).1 := e_sc1 h_v1233 (of_decide_eq_true rfl)
  have e_t1233_2 : sv t1233.2 = (sc28pS (scArg v1233)).2 := e_sc2 h_v1233 (of_decide_eq_true rfl)
  have h_v1237 : R 1 0 4611686018158952449 4611686018695823367 v1237 v1237 := (r_sub hl (r_add hl h_v31 h_t1233_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1237 : sv v1237 = sv v31 + sv t1233.2 := e_add h_v31 h_t1233_2 (of_decide_eq_true rfl)
  have h_v1238 : R 1 0 0 1 v1238 v1238 := (r_plt hl h_v1237 h_v33 (of_decide_eq_true rfl))
  have e_v1238 : (v1238 = 1 ↔ sv v1237 < sv v33) := e_plt h_v1237 h_v33 (of_decide_eq_true rfl)
  have h_v1239 : R 1 0 4611686018158952449 4611686018695823367 v1239 v1239 := (r_psel hl h_v1238 h_v1237 h_v33 (of_decide_eq_true rfl))
  have e_v1239 : v1239 = if v1238 = 1 then v1237 else v33 := e_psel h_v1238 h_v1237 h_v33 (of_decide_eq_true rfl)
  have h_v1240 : R 1 0 4467570780154101760 4755801223146242048 v1240 v1240 := (r_sshl hl h_v1213 4467570780154101760 4755801223146242048 (of_decide_eq_true rfl))
  have e_v1240 : sv v1240 = sv v1213 * 2 ^ 28 := e_sshl h_v1213 4467570780154101760 4755801223146242048 (of_decide_eq_true rfl)
  have h_v1241 : R 1 0 4539628422241976329 4683743616760283199 v1241 v1241 := (r_smx hl 29 h_v1239 h_v1214 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl))
  have e_v1241 : sv v1241 = sv v1239 * sv v1214 := e_smx 29 h_v1239 h_v1214 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl)
  have h_v1242 : R 1 0 0 1 v1242 v1242 := (r_plt hl h_v1240 h_v1241 (of_decide_eq_true rfl))
  have e_v1242 : (v1242 = 1 ↔ sv v1240 < sv v1241) := e_plt h_v1240 h_v1241 (of_decide_eq_true rfl)
  have h_v1243 : R 1 0 0 1 v1243 v1243 := (r_sub hl (r_O hl) h_v1242 (of_decide_eq_true rfl))
  have e_v1243 : (v1243 = 1 ↔ ¬v1242 = 1) := e_not h_v1242 (of_decide_eq_true rfl)
  have h_v1244 : R 1 0 0 1 v1244 v1244 := (r_lor hl h_v1235 h_v1243 (of_decide_eq_true rfl))
  have e_v1244 : (v1244 = 1 ↔ v1235 = 1 ∨ v1243 = 1) := e_lor h_v1235 h_v1243 (of_decide_eq_true rfl)
  have h_v1245 : R 1 0 4611686018427387904 4611686019501129727 v1245 v1245 := (r_psel hl h_v1244 h_v1233 h_v20 (of_decide_eq_true rfl))
  have e_v1245 : v1245 = if v1244 = 1 then v1233 else v20 := e_psel h_v1244 h_v1233 h_v20 (of_decide_eq_true rfl)
  have h_v1247 : R 1 0 4611686018427387904 4611686019501129727 v1247 v1247 := (r_psel hl h_v777 h_v1245 h_v20 (of_decide_eq_true rfl))
  have e_v1247 : v1247 = if v777 = 1 then v1245 else v20 := e_psel h_v777 h_v1245 h_v20 (of_decide_eq_true rfl)
  have h_v1248 : R 1 0 0 1 v1248 v1248 := (r_land hl h_v777 h_v1215 (of_decide_eq_true rfl))
  clear h_v31 h_v33 h_v1213 h_v1214 h_v1233 h_v1235 h_t1233_1 h_t1233_2 e_t1233_1 h_v1237 h_v1238 h_v1239 h_v1240 h_v1241 h_v1242 h_v1243 h_v1244 h_v1245
  have e_v1248 : (v1248 = 1 ↔ v777 = 1 ∧ v1215 = 1) := e_land h_v777 h_v1215 (of_decide_eq_true rfl)
  have h_v1250 : R 1 0 4611686018427387904 4611686019270702761 v1250 v1250 := (r_psel hl h_v1044 h_v20 h_v9 (of_decide_eq_true rfl))
  have e_v1250 : v1250 = if v1044 = 1 then v20 else v9 := e_psel h_v1044 h_v20 h_v9 (of_decide_eq_true rfl)
  have h_v1252 : R 1 0 4611686018427387904 4611686019501129727 v1252 v1252 := (r_psel hl h_v1248 h_v1250 h_v1247 (of_decide_eq_true rfl))
  have e_v1252 : v1252 = if v1248 = 1 then v1250 else v1247 := e_psel h_v1248 h_v1250 h_v1247 (of_decide_eq_true rfl)
  have h_v1254 : R 1 0 4611686017353646081 4611686020574871550 v1254 v1254 := (r_sub hl (r_add hl h_v396 h_v1252 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1254 : sv v1254 = sv v396 + sv v1252 := e_add h_v396 h_v1252 (of_decide_eq_true rfl)
  have h_v1256 : R 1 0 4611686016279904258 4611686021648613373 v1256 v1256 := (r_sub hl (r_add hl h_v721 h_v1254 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1256 : sv v1256 = sv v721 + sv v1254 := e_add h_v721 h_v1254 (of_decide_eq_true rfl)
  have h_v1259 : R 1 0 0 1 v1259 v1259 := (r_plt hl h_v6 h_v1256 (of_decide_eq_true rfl))
  have e_v1259 : (v1259 = 1 ↔ sv v6 < sv v1256) := e_plt h_v6 h_v1256 (of_decide_eq_true rfl)
  have h_v1260 : R 1 0 0 1 v1260 v1260 := (r_sub hl (r_O hl) h_v1259 (of_decide_eq_true rfl))
  have e_v1260 : (v1260 = 1 ↔ ¬v1259 = 1) := e_not h_v1259 (of_decide_eq_true rfl)
  have h_v1261 : R 1 0 0 1 v1261 v1261 := (r_land hl h_v23 h_v47 (of_decide_eq_true rfl))
  have e_v1261 : (v1261 = 1 ↔ v23 = 1 ∧ v47 = 1) := e_land h_v23 h_v47 (of_decide_eq_true rfl)
  have h_v1262 : R 1 0 0 1 v1262 v1262 := (r_land hl h_v74 h_v1261 (of_decide_eq_true rfl))
  have e_v1262 : (v1262 = 1 ↔ v74 = 1 ∧ v1261 = 1) := e_land h_v74 h_v1261 (of_decide_eq_true rfl)
  have h_v1263 : R 1 0 0 1 v1263 v1263 := (r_land hl h_v91 h_v1262 (of_decide_eq_true rfl))
  have e_v1263 : (v1263 = 1 ↔ v91 = 1 ∧ v1262 = 1) := e_land h_v91 h_v1262 (of_decide_eq_true rfl)
  have h_v1264 : R 1 0 0 1 v1264 v1264 := (r_land hl h_v23 h_v1263 (of_decide_eq_true rfl))
  have e_v1264 : (v1264 = 1 ↔ v23 = 1 ∧ v1263 = 1) := e_land h_v23 h_v1263 (of_decide_eq_true rfl)
  have h_v1265 : R 1 0 0 1 v1265 v1265 := (r_land hl h_v109 h_v1264 (of_decide_eq_true rfl))
  have e_v1265 : (v1265 = 1 ↔ v109 = 1 ∧ v1264 = 1) := e_land h_v109 h_v1264 (of_decide_eq_true rfl)
  have h_v1266 : R 1 0 0 1 v1266 v1266 := (r_land hl h_v109 h_v1265 (of_decide_eq_true rfl))
  have e_v1266 : (v1266 = 1 ↔ v109 = 1 ∧ v1265 = 1) := e_land h_v109 h_v1265 (of_decide_eq_true rfl)
  clear h_OFFr h_v6 h_v9 h_v20 h_v47 h_v74 h_v91 h_v109 h_v396 h_v721 h_v777 h_v1044 h_v1215 h_v1247 h_v1248 h_v1250 h_v1252 h_v1254 h_v1256 h_v1259 h_v1261 h_v1262 h_v1263 h_v1264 h_v1265
  have h_v1267 : R 1 0 0 1 v1267 v1267 := (r_land hl h_v146 h_v1266 (of_decide_eq_true rfl))
  have e_v1267 : (v1267 = 1 ↔ v146 = 1 ∧ v1266 = 1) := e_land h_v146 h_v1266 (of_decide_eq_true rfl)
  have h_v1268 : R 1 0 0 1 v1268 v1268 := (r_land hl h_v259 h_v1267 (of_decide_eq_true rfl))
  have e_v1268 : (v1268 = 1 ↔ v259 = 1 ∧ v1267 = 1) := e_land h_v259 h_v1267 (of_decide_eq_true rfl)
  have h_v1269 : R 1 0 0 1 v1269 v1269 := (r_land hl h_v259 h_v1268 (of_decide_eq_true rfl))
  have e_v1269 : (v1269 = 1 ↔ v259 = 1 ∧ v1268 = 1) := e_land h_v259 h_v1268 (of_decide_eq_true rfl)
  have h_v1270 : R 1 0 0 1 v1270 v1270 := (r_land hl h_v290 h_v1269 (of_decide_eq_true rfl))
  have e_v1270 : (v1270 = 1 ↔ v290 = 1 ∧ v1269 = 1) := e_land h_v290 h_v1269 (of_decide_eq_true rfl)
  have h_v1271 : R 1 0 0 1 v1271 v1271 := (r_land hl h_v23 h_v1270 (of_decide_eq_true rfl))
  have e_v1271 : (v1271 = 1 ↔ v23 = 1 ∧ v1270 = 1) := e_land h_v23 h_v1270 (of_decide_eq_true rfl)
  have h_v1272 : R 1 0 0 1 v1272 v1272 := (r_land hl h_v402 h_v1271 (of_decide_eq_true rfl))
  have e_v1272 : (v1272 = 1 ↔ v402 = 1 ∧ v1271 = 1) := e_land h_v402 h_v1271 (of_decide_eq_true rfl)
  have h_v1273 : R 1 0 0 1 v1273 v1273 := (r_land hl h_v423 h_v1272 (of_decide_eq_true rfl))
  have e_v1273 : (v1273 = 1 ↔ v423 = 1 ∧ v1272 = 1) := e_land h_v423 h_v1272 (of_decide_eq_true rfl)
  have h_v1274 : R 1 0 0 1 v1274 v1274 := (r_land hl h_v440 h_v1273 (of_decide_eq_true rfl))
  have e_v1274 : (v1274 = 1 ↔ v440 = 1 ∧ v1273 = 1) := e_land h_v440 h_v1273 (of_decide_eq_true rfl)
  have h_v1275 : R 1 0 0 1 v1275 v1275 := (r_land hl h_v23 h_v1274 (of_decide_eq_true rfl))
  have e_v1275 : (v1275 = 1 ↔ v23 = 1 ∧ v1274 = 1) := e_land h_v23 h_v1274 (of_decide_eq_true rfl)
  have h_v1276 : R 1 0 0 1 v1276 v1276 := (r_land hl h_v443 h_v1275 (of_decide_eq_true rfl))
  have e_v1276 : (v1276 = 1 ↔ v443 = 1 ∧ v1275 = 1) := e_land h_v443 h_v1275 (of_decide_eq_true rfl)
  have h_v1277 : R 1 0 0 1 v1277 v1277 := (r_land hl h_v443 h_v1276 (of_decide_eq_true rfl))
  have e_v1277 : (v1277 = 1 ↔ v443 = 1 ∧ v1276 = 1) := e_land h_v443 h_v1276 (of_decide_eq_true rfl)
  have h_v1278 : R 1 0 0 1 v1278 v1278 := (r_land hl h_v474 h_v1277 (of_decide_eq_true rfl))
  have e_v1278 : (v1278 = 1 ↔ v474 = 1 ∧ v1277 = 1) := e_land h_v474 h_v1277 (of_decide_eq_true rfl)
  have h_v1279 : R 1 0 0 1 v1279 v1279 := (r_land hl h_v584 h_v1278 (of_decide_eq_true rfl))
  clear h_v146 h_v259 h_v290 h_v402 h_v423 h_v440 h_v443 h_v474 h_v1266 h_v1267 h_v1268 h_v1269 h_v1270 h_v1271 h_v1272 h_v1273 h_v1274 h_v1275 h_v1276 h_v1277
  have e_v1279 : (v1279 = 1 ↔ v584 = 1 ∧ v1278 = 1) := e_land h_v584 h_v1278 (of_decide_eq_true rfl)
  have h_v1280 : R 1 0 0 1 v1280 v1280 := (r_land hl h_v584 h_v1279 (of_decide_eq_true rfl))
  have e_v1280 : (v1280 = 1 ↔ v584 = 1 ∧ v1279 = 1) := e_land h_v584 h_v1279 (of_decide_eq_true rfl)
  have h_v1281 : R 1 0 0 1 v1281 v1281 := (r_land hl h_v615 h_v1280 (of_decide_eq_true rfl))
  have e_v1281 : (v1281 = 1 ↔ v615 = 1 ∧ v1280 = 1) := e_land h_v615 h_v1280 (of_decide_eq_true rfl)
  have h_v1282 : R 1 0 0 1 v1282 v1282 := (r_land hl h_v23 h_v1281 (of_decide_eq_true rfl))
  have e_v1282 : (v1282 = 1 ↔ v23 = 1 ∧ v1281 = 1) := e_land h_v23 h_v1281 (of_decide_eq_true rfl)
  have h_v1283 : R 1 0 0 1 v1283 v1283 := (r_land hl h_v728 h_v1282 (of_decide_eq_true rfl))
  have e_v1283 : (v1283 = 1 ↔ v728 = 1 ∧ v1282 = 1) := e_land h_v728 h_v1282 (of_decide_eq_true rfl)
  have h_v1284 : R 1 0 0 1 v1284 v1284 := (r_land hl h_v749 h_v1283 (of_decide_eq_true rfl))
  have e_v1284 : (v1284 = 1 ↔ v749 = 1 ∧ v1283 = 1) := e_land h_v749 h_v1283 (of_decide_eq_true rfl)
  have h_v1285 : R 1 0 0 1 v1285 v1285 := (r_land hl h_v766 h_v1284 (of_decide_eq_true rfl))
  have e_v1285 : (v1285 = 1 ↔ v766 = 1 ∧ v1284 = 1) := e_land h_v766 h_v1284 (of_decide_eq_true rfl)
  have h_v1286 : R 1 0 0 1 v1286 v1286 := (r_land hl h_v823 h_v1285 (of_decide_eq_true rfl))
  have e_v1286 : (v1286 = 1 ↔ v823 = 1 ∧ v1285 = 1) := e_land h_v823 h_v1285 (of_decide_eq_true rfl)
  have h_v1287 : R 1 0 0 1 v1287 v1287 := (r_land hl h_v850 h_v1286 (of_decide_eq_true rfl))
  have e_v1287 : (v1287 = 1 ↔ v850 = 1 ∧ v1286 = 1) := e_land h_v850 h_v1286 (of_decide_eq_true rfl)
  have h_v1288 : R 1 0 0 1 v1288 v1288 := (r_land hl h_v920 h_v1287 (of_decide_eq_true rfl))
  have e_v1288 : (v1288 = 1 ↔ v920 = 1 ∧ v1287 = 1) := e_land h_v920 h_v1287 (of_decide_eq_true rfl)
  have h_v1289 : R 1 0 0 1 v1289 v1289 := (r_land hl h_v1019 h_v1288 (of_decide_eq_true rfl))
  have e_v1289 : (v1289 = 1 ↔ v1019 = 1 ∧ v1288 = 1) := e_land h_v1019 h_v1288 (of_decide_eq_true rfl)
  have h_v1290 : R 1 0 0 1 v1290 v1290 := (r_land hl h_v1087 h_v1289 (of_decide_eq_true rfl))
  have e_v1290 : (v1290 = 1 ↔ v1087 = 1 ∧ v1289 = 1) := e_land h_v1087 h_v1289 (of_decide_eq_true rfl)
  have h_v1291 : R 1 0 0 1 v1291 v1291 := (r_land hl h_v1184 h_v1290 (of_decide_eq_true rfl))
  have e_v1291 : (v1291 = 1 ↔ v1184 = 1 ∧ v1290 = 1) := e_land h_v1184 h_v1290 (of_decide_eq_true rfl)
  clear h_v23 h_v584 h_v615 h_v728 h_v749 h_v766 h_v823 h_v850 h_v920 h_v1019 h_v1087 h_v1184 h_v1278 h_v1279 h_v1280 h_v1281 h_v1282 h_v1283 h_v1284 h_v1285 h_v1286 h_v1287 h_v1288 h_v1289 h_v1290
  have h_v1292 : R 1 0 0 1 v1292 v1292 := (r_land hl h_v1260 h_v1291 (of_decide_eq_true rfl))
  have e_v1292 : (v1292 = 1 ↔ v1260 = 1 ∧ v1291 = 1) := e_land h_v1260 h_v1291 (of_decide_eq_true rfl)
  have k_v1292 : v1292 = 1 := h
  have k_v1260 : v1260 = 1 := ((e_v1292).1 k_v1292).1
  have k_v1291 : v1291 = 1 := ((e_v1292).1 k_v1292).2
  have k_v1184 : v1184 = 1 := ((e_v1291).1 k_v1291).1
  have k_v1290 : v1290 = 1 := ((e_v1291).1 k_v1291).2
  have k_v1087 : v1087 = 1 := ((e_v1290).1 k_v1290).1
  have k_v1289 : v1289 = 1 := ((e_v1290).1 k_v1290).2
  have k_v1019 : v1019 = 1 := ((e_v1289).1 k_v1289).1
  have k_v1288 : v1288 = 1 := ((e_v1289).1 k_v1289).2
  have k_v920 : v920 = 1 := ((e_v1288).1 k_v1288).1
  have k_v1287 : v1287 = 1 := ((e_v1288).1 k_v1288).2
  have k_v850 : v850 = 1 := ((e_v1287).1 k_v1287).1
  have k_v1286 : v1286 = 1 := ((e_v1287).1 k_v1287).2
  have k_v823 : v823 = 1 := ((e_v1286).1 k_v1286).1
  have k_v1285 : v1285 = 1 := ((e_v1286).1 k_v1286).2
  have k_v766 : v766 = 1 := ((e_v1285).1 k_v1285).1
  have k_v1284 : v1284 = 1 := ((e_v1285).1 k_v1285).2
  have k_v749 : v749 = 1 := ((e_v1284).1 k_v1284).1
  have k_v1283 : v1283 = 1 := ((e_v1284).1 k_v1284).2
  have k_v728 : v728 = 1 := ((e_v1283).1 k_v1283).1
  have k_v1282 : v1282 = 1 := ((e_v1283).1 k_v1283).2
  have k_v23 : v23 = 1 := ((e_v1282).1 k_v1282).1
  have k_v1281 : v1281 = 1 := ((e_v1282).1 k_v1282).2
  have k_v615 : v615 = 1 := ((e_v1281).1 k_v1281).1
  have k_v1280 : v1280 = 1 := ((e_v1281).1 k_v1281).2
  have k_v584 : v584 = 1 := ((e_v1280).1 k_v1280).1
  have k_v1279 : v1279 = 1 := ((e_v1280).1 k_v1280).2
  have k_v1278 : v1278 = 1 := ((e_v1279).1 k_v1279).2
  have k_v474 : v474 = 1 := ((e_v1278).1 k_v1278).1
  have k_v1277 : v1277 = 1 := ((e_v1278).1 k_v1278).2
  have k_v443 : v443 = 1 := ((e_v1277).1 k_v1277).1
  have k_v1276 : v1276 = 1 := ((e_v1277).1 k_v1277).2
  have k_v1275 : v1275 = 1 := ((e_v1276).1 k_v1276).2
  have k_v1274 : v1274 = 1 := ((e_v1275).1 k_v1275).2
  have k_v440 : v440 = 1 := ((e_v1274).1 k_v1274).1
  have k_v1273 : v1273 = 1 := ((e_v1274).1 k_v1274).2
  have k_v423 : v423 = 1 := ((e_v1273).1 k_v1273).1
  have k_v1272 : v1272 = 1 := ((e_v1273).1 k_v1273).2
  have k_v402 : v402 = 1 := ((e_v1272).1 k_v1272).1
  have k_v1271 : v1271 = 1 := ((e_v1272).1 k_v1272).2
  have k_v1270 : v1270 = 1 := ((e_v1271).1 k_v1271).2
  have k_v290 : v290 = 1 := ((e_v1270).1 k_v1270).1
  have k_v1269 : v1269 = 1 := ((e_v1270).1 k_v1270).2
  have k_v259 : v259 = 1 := ((e_v1269).1 k_v1269).1
  have k_v1268 : v1268 = 1 := ((e_v1269).1 k_v1269).2
  have k_v1267 : v1267 = 1 := ((e_v1268).1 k_v1268).2
  have k_v146 : v146 = 1 := ((e_v1267).1 k_v1267).1
  have k_v1266 : v1266 = 1 := ((e_v1267).1 k_v1267).2
  have k_v109 : v109 = 1 := ((e_v1266).1 k_v1266).1
  have k_v1265 : v1265 = 1 := ((e_v1266).1 k_v1266).2
  have k_v1264 : v1264 = 1 := ((e_v1265).1 k_v1265).2
  have k_v1263 : v1263 = 1 := ((e_v1264).1 k_v1264).2
  have k_v91 : v91 = 1 := ((e_v1263).1 k_v1263).1
  have k_v1262 : v1262 = 1 := ((e_v1263).1 k_v1263).2
  have k_v74 : v74 = 1 := ((e_v1262).1 k_v1262).1
  have k_v1261 : v1261 = 1 := ((e_v1262).1 k_v1262).2
  have k_v47 : v47 = 1 := ((e_v1261).1 k_v1261).2
  have k_v44 : v44 = 1 := ((e_v47).1 k_v47).1
  have k_v46 : v46 = 1 := ((e_v47).1 k_v47).2
  have k_v108 : v108 = 1 := ((e_v109).1 k_v109).2
  have k_v258 : v258 = 1 := ((e_v259).1 k_v259).2
  have k_v399 : v399 = 1 := ((e_v402).1 k_v402).1
  have k_v401 : v401 = 1 := ((e_v402).1 k_v402).2
  have k_v442 : v442 = 1 := ((e_v443).1 k_v443).2
  have k_v583 : v583 = 1 := ((e_v584).1 k_v584).2
  have k_v19 : v19 = 1 := ((e_v23).1 k_v23).1
  have k_v22 : v22 = 1 := ((e_v23).1 k_v23).2
  have k_v725 : v725 = 1 := ((e_v728).1 k_v728).1
  have k_v727 : v727 = 1 := ((e_v728).1 k_v728).2
  let u10 : ℤ := 1686629712
  let u11 : ℕ := if u10 < (sv v7) then 1 else 0
  let u12 : ℕ := if u11 = 1 then 0 else 1
  let u13 : ℤ := if u12 = 1 then (sv v9) else (sv v7)
  let u17 : ℤ := if v16 = 1 then (sv v7) else (sv v14)
  have f2 := L2.K27_corner_fixed (sv v9) (sv v7) (1 : ℕ) (sv v7) u10 u12 u13 (sv v14) v16 (sv v14) u17 u17 (sv v7) (L2.p_add_0l e_v9) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) rfl e_v14 (L2.p_le e_v15 e_v16) (L2.p_max (L2.p_lt_cc (v := 1) (0) (843314856) e_v9 e_v14 (of_decide_eq_true rfl)) (L2.p_sel_t _ _)) rfl (L2.p_sel_t _ _) (L2.p_sel_t _ _)
  have f23 := L2.K8_in_range True (sv v0) (sv v1) v19 (sv v20) v22 v23 (L2.p_clt (-1) e_v18 e_v19) e_v20 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f22 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v27) (sv v29) (sv v30) (sv v32) (sv v33) (sv v35) v37 v39 v40 (sv v41) f23 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v26 (L2.p_sel e_v27)) (L2.p_addc (-4) e_v29 e_v28) (L2.p_max e_v26 (L2.p_sel e_v30)) (L2.p_addc (4) e_v32 e_v31) e_v33 (L2.p_min e_v34 (L2.p_sel e_v35)) (L2.p_ltc (421657430) e_v36 e_v37) (L2.p_clt (421657427) e_v38 e_v39) e_v40 (L2.p_sel e_v41)
  have f59 := L2.K5_ihalf (sv v2) (sv v3) (sv v42) (sv v43) e_v42 e_v43
  have f63 := L2.K8_in_range True (sv v42) (sv v43) v44 (sv v20) v46 v47 (L2.p_clt (-1) e_v18 e_v44) e_v20 (L2.p_le e_v45 e_v46) e_v47 (L2.X1_top _ k_v47)
  have f62 := L2.K9_isin True (sv v42) (sv v43) (sv t42.1) (sv t43.1) (sv v51) (sv v52) (sv v53) (sv v54) (sv v33) (sv v56) v57 v58 v59 (sv v60) f63 (L2.p_sin e_t42_1) (L2.p_sin e_t43_1) (L2.p_min e_v50 (L2.p_sel e_v51)) (L2.p_addc (-4) (L2.p_add_comm e_v52) e_v28) (L2.p_max e_v50 (L2.p_sel e_v53)) (L2.p_addc (4) (L2.p_add_comm e_v54) e_v31) e_v33 (L2.p_min e_v55 (L2.p_sel e_v56)) (L2.p_ltc (421657430) e_v36 e_v57) (L2.p_clt (421657427) e_v38 e_v58) e_v59 (L2.p_sel e_v60)
  have f99 := L2.K6_imul True (sv v29) (sv v41) (sv v52) (sv v60) (sv v9) v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 (sv v77) v78 v79 (sv v80) v81 v82 (sv v83) v84 v85 (sv v86) (sv v88) (sv v90) e_v9 e_v61 e_v62 e_v63 e_v64 (L2.p_and_comm e_v65) e_v66 e_v67 e_v68 e_v69 e_v70 (L2.p_and_comm e_v71) e_v72 e_v73 e_v74 (L2.X1_top _ k_v74) e_v75 e_v76 (L2.p_sel e_v77) e_v78 e_v79 (L2.p_sel e_v80) e_v81 e_v82 (L2.p_sel e_v83) e_v84 e_v85 (L2.p_sel e_v86) (L2.p_mul (L2.p_mul_comm e_v87) e_v88) (L2.p_mulc (L2.p_mul_comm e_v89) e_v90)
  have f21 := L2.K14_iso_base_a True (sv v2) (sv v3) (sv v0) (sv v1) (sv v29) (sv v41) (sv v42) (sv v43) (sv v52) (sv v60) (sv v88) (sv v90) v91 f22 f59 f62 f99 (L2.p_clt (-1) e_v18 e_v91) (L2.X1_top _ k_v91)
  have f138 := L2.K8_in_range True (sv v0) (sv v1) v19 (sv v20) v22 v23 (L2.p_clt (-1) e_v18 e_v19) e_v20 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f148 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v93) (sv v94) (sv v96) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v93) e_v28) e_v94 (L2.p_max e_v95 (L2.p_sel e_v96))
  have f162 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v101) (sv v33) (sv v103) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v101) e_v31) e_v33 (L2.p_min e_v102 (L2.p_sel e_v103))
  have f137 := L2.K10_icos True (sv v0) (sv v1) (sv v96) (sv v94) v98 (sv v99) (sv v103) (sv v33) v105 (sv v106) f138 f148 e_v94 (L2.p_clt (843314855) e_v97 e_v98) (L2.p_sel e_v99) f162 e_v33 (L2.p_ltc (1) e_v104 e_v105) (L2.p_sel e_v106)
  have f177 := L2.K5_ihalf (sv v3) (sv v3) (sv v107) (sv v43) e_v107 e_v43
  have f181 := L2.K8_in_range True (sv v107) (sv v43) v108 (sv v20) v46 v109 (L2.p_clt (-1) e_v18 e_v108) e_v20 (L2.p_le e_v45 e_v46) (L2.p_and_comm e_v109) (L2.X1_top _ k_v109)
  let u110 : ℤ := L2.cosI (sv v43)
  let u111 : ℤ := (sv v28) + u110
  let u112 : ℕ := if u111 < (sv v94) then 1 else 0
  let u113 : ℤ := if u112 = 1 then (sv v94) else u111
  have f191 := L2.K3_cos_lo (sv v43) u110 u111 (sv v94) u113 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u114 : ℕ := if (sv v97) < (sv v43) then 1 else 0
  let u115 : ℤ := if u114 = 1 then (sv v94) else u113
  let u116 : ℤ := L2.cosI (sv v107)
  let u117 : ℤ := (sv v31) + u116
  let u118 : ℕ := if u117 < (sv v33) then 1 else 0
  let u119 : ℤ := if u118 = 1 then u117 else (sv v33)
  have f205 := L2.K3_cos_hi (sv v107) u116 u117 (sv v33) u119 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u120 : ℕ := if (sv v107) < (sv v104) then 1 else 0
  let u121 : ℤ := if u120 = 1 then (sv v33) else u119
  have f180 := L2.K10_icos True (sv v107) (sv v43) u113 (sv v94) u114 u115 u119 (sv v33) u120 u121 f181 f191 e_v94 (L2.p_clt (843314855) e_v97 (L2.p_ult _ _)) rfl f205 e_v33 (L2.p_ltc (1) e_v104 (L2.p_ult _ _)) rfl
  have f220 := L2.K8_in_range True (sv v107) (sv v43) v108 (sv v20) v46 v109 (L2.p_clt (-1) e_v18 e_v108) e_v20 (L2.p_le e_v45 e_v46) (L2.p_and_comm e_v109) (L2.X1_top _ k_v109)
  have f219 := L2.K9_isin True (sv v107) (sv v43) (sv t107.1) (sv t43.1) (sv v124) (sv v125) (sv v126) (sv v127) (sv v33) (sv v129) v130 v58 v131 (sv v132) f220 (L2.p_sin e_t107_1) (L2.p_sin e_t43_1) (L2.p_min e_v123 (L2.p_sel e_v124)) (L2.p_addc (-4) (L2.p_add_comm e_v125) e_v28) (L2.p_max e_v123 (L2.p_sel e_v126)) (L2.p_addc (4) (L2.p_add_comm e_v127) e_v31) e_v33 (L2.p_min e_v128 (L2.p_sel e_v129)) (L2.p_ltc (421657430) e_v36 e_v130) (L2.p_clt (421657427) e_v38 e_v58) (L2.p_and_comm e_v131) (L2.p_sel e_v132)
  let u140 : ℕ := if v139 = 1 then 0 else 1
  let u142 : ℕ := if v141 = 1 then 0 else 1
  let u143 : ℕ := if v139 = 1 ∧ u142 = 1 then 1 else 0
  let u147 : ℕ := if v134 = 1 ∧ v144 = 1 then 1 else 0
  let u148 : ℕ := if u143 = 1 ∨ u147 = 1 then 1 else 0
  let u149 : ℤ := if u148 = 1 then (sv v106) else (sv v99)
  let u150 : ℕ := if v138 = 1 ∧ u140 = 1 then 1 else 0
  let u151 : ℕ := if v137 = 1 ∨ u150 = 1 then 1 else 0
  let u152 : ℤ := if u151 = 1 then (sv v132) else (sv v125)
  let u153 : ℕ := if v137 = 1 ∧ v144 = 1 then 1 else 0
  let u154 : ℕ := if u143 = 1 ∨ u153 = 1 then 1 else 0
  let u155 : ℤ := if u154 = 1 then (sv v99) else (sv v106)
  let u156 : ℕ := if v138 = 1 ∧ u143 = 1 then 1 else 0
  let u157 : ℕ := if v137 = 1 ∨ u156 = 1 then 1 else 0
  let u158 : ℤ := if u157 = 1 then (sv v125) else (sv v132)
  let u159 : ℤ := u149 * u152
  let u160 : ℤ := u159 / 2 ^ 28
  let u161 : ℤ := u155 * u158
  let u162 : ℤ := -((-u161) / 2 ^ 28)
  have f256 := L2.K6_imul True (sv v99) (sv v106) (sv v125) (sv v132) (sv v9) v133 v134 v135 v136 v137 v138 v139 u140 v141 u142 u143 v144 v145 v146 u147 u148 u149 u150 u151 u152 u153 u154 u155 u156 u157 u158 u160 u162 e_v9 e_v133 e_v134 e_v135 e_v136 (L2.p_and_comm e_v137) e_v138 e_v139 (L2.p_unot _) e_v141 (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) e_v144 e_v145 e_v146 (L2.X1_top _ k_v146) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl)
  let u163 : ℕ := if (sv v9) < u160 then 1 else 0
  let u164 : ℕ := if u163 = 1 then 0 else 1
  let u165 : ℕ := if u115 < (sv v9) then 1 else 0
  let u166 : ℤ := if u165 = 1 then u160 else u162
  let u167 : ℕ := if u121 < (sv v9) then 1 else 0
  let u168 : ℤ := if u167 = 1 then u162 else u160
  have f289 := L2.K11_qdiv u115 u121 u160 u162 u163 u164 (sv v9) u165 u166 u167 u168 (L2.p_clt (0) e_v9 (L2.p_ult _ _)) (L2.p_unot _) e_v9 (L2.p_ult _ _) rfl (L2.p_ult _ _) rfl
  let u169 : ℤ := (sv v9) - u115
  let u170 : ℤ := if u165 = 1 then u169 else u115
  let u171 : ℤ := 0
  let u172 : ℕ := if u165 = 1 then 0 else 1
  let u173 : ℤ := L2.cosI u171
  let u174 : ℤ := (sv v28) + u173
  let u175 : ℕ := if u174 < (sv v94) then 1 else 0
  let u176 : ℤ := if u175 = 1 then (sv v94) else u174
  have f307 := L2.K3_cos_lo u171 u173 u174 (sv v94) u176 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u177 : ℤ := (sv v31) + u173
  let u178 : ℕ := if u177 < (sv v33) then 1 else 0
  let u179 : ℤ := if u178 = 1 then u177 else (sv v33)
  have f316 := L2.K3_cos_hi u171 u173 u177 (sv v33) u179 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u180 : ℤ := L2.sinI u171
  let u181 : ℤ := (sv v31) + u180
  let u182 : ℕ := if u181 < (sv v33) then 1 else 0
  let u183 : ℤ := if u182 = 1 then u181 else (sv v33)
  have f325 := L2.K3_sin_hi u171 u180 u181 (sv v33) u183 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u184 : ℤ := (sv v28) + u180
  have f334 := L2.K3_sin_lo u171 u180 u184 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u185 : ℤ := if u172 = 1 then u176 else u179
  let u186 : ℤ := if u172 = 1 then u183 else u184
  let u187 : ℤ := u166 * u186
  let u188 : ℤ := u170 * u185
  let u189 : ℕ := if u188 < u187 then 1 else 0
  let u190 : ℕ := if u189 = 1 then 0 else 1
  let u191 : ℕ := if u187 < u188 then 1 else 0
  let u192 : ℕ := if u191 = 1 then 0 else 1
  let u193 : ℕ := if (sv v9) < u171 then 1 else 0
  let u194 : ℕ := if u193 = 1 then 0 else 1
  let u196 : ℕ := if (sv v195) < u171 then 1 else 0
  let u197 : ℕ := if u196 = 1 then 0 else 1
  let u198 : ℕ := if (sv v18) < u176 then 1 else 0
  let u199 : ℕ := if u190 = 1 ∧ u198 = 1 then 1 else 0
  let u200 : ℕ := if u197 = 1 ∧ u199 = 1 then 1 else 0
  let u201 : ℕ := if u194 = 1 ∨ u200 = 1 then 1 else 0
  let u203 : ℕ := if u171 < (sv v202) then 1 else 0
  let u204 : ℕ := if u203 = 1 then 0 else 1
  let u205 : ℕ := if u192 = 1 ∨ u204 = 1 then 1 else 0
  let u206 : ℕ := if u172 = 1 ∧ u201 = 1 then 1 else 0
  let u207 : ℕ := if u165 = 1 ∧ u205 = 1 then 1 else 0
  let u208 : ℕ := if u206 = 1 ∨ u207 = 1 then 1 else 0
  let u209 : ℤ := (sv v9) - u171
  let u210 : ℤ := if u165 = 1 then u209 else u171
  let u211 : ℤ := -421657429
  let u212 : ℤ := if u208 = 1 then u210 else u211
  have f300 := L2.K12_atan_lo u115 u166 (sv v9) u165 u169 u170 u171 u172 u176 u179 u183 u184 u185 u186 u187 u188 u190 u192 u193 u194 (sv v195) u197 u198 u199 u200 u201 (sv v202) u204 u205 u206 u165 u207 u208 u209 u210 u211 u212 e_v9 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f307 f316 f325 f334 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v195 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v18 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v202 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  let u213 : ℤ := (sv v9) - u121
  let u214 : ℤ := if u167 = 1 then u213 else u121
  let u215 : ℤ := 0
  let u216 : ℤ := L2.cosI u215
  let u217 : ℤ := (sv v28) + u216
  let u218 : ℕ := if u217 < (sv v94) then 1 else 0
  let u219 : ℤ := if u218 = 1 then (sv v94) else u217
  have f380 := L2.K3_cos_lo u215 u216 u217 (sv v94) u219 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u220 : ℤ := (sv v31) + u216
  let u221 : ℕ := if u220 < (sv v33) then 1 else 0
  let u222 : ℤ := if u221 = 1 then u220 else (sv v33)
  have f389 := L2.K3_cos_hi u215 u216 u220 (sv v33) u222 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u223 : ℤ := L2.sinI u215
  let u224 : ℤ := (sv v31) + u223
  let u225 : ℕ := if u224 < (sv v33) then 1 else 0
  let u226 : ℤ := if u225 = 1 then u224 else (sv v33)
  have f398 := L2.K3_sin_hi u215 u223 u224 (sv v33) u226 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u227 : ℤ := (sv v28) + u223
  have f407 := L2.K3_sin_lo u215 u223 u227 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u228 : ℤ := if u167 = 1 then u219 else u222
  let u229 : ℤ := if u167 = 1 then u226 else u227
  let u230 : ℤ := u168 * u229
  let u231 : ℤ := u214 * u228
  let u232 : ℕ := if u231 < u230 then 1 else 0
  let u233 : ℕ := if u232 = 1 then 0 else 1
  let u234 : ℕ := if u230 < u231 then 1 else 0
  let u235 : ℕ := if u234 = 1 then 0 else 1
  let u236 : ℕ := if (sv v9) < u215 then 1 else 0
  let u237 : ℕ := if u236 = 1 then 0 else 1
  let u238 : ℕ := if (sv v195) < u215 then 1 else 0
  let u239 : ℕ := if u238 = 1 then 0 else 1
  let u240 : ℕ := if (sv v18) < u219 then 1 else 0
  let u241 : ℕ := if u233 = 1 ∧ u240 = 1 then 1 else 0
  let u242 : ℕ := if u239 = 1 ∧ u241 = 1 then 1 else 0
  let u243 : ℕ := if u237 = 1 ∨ u242 = 1 then 1 else 0
  let u244 : ℕ := if u215 < (sv v202) then 1 else 0
  let u245 : ℕ := if u244 = 1 then 0 else 1
  let u246 : ℕ := if u235 = 1 ∨ u245 = 1 then 1 else 0
  let u247 : ℕ := if u167 = 1 ∧ u243 = 1 then 1 else 0
  let u248 : ℕ := if u167 = 1 then 0 else 1
  let u249 : ℕ := if u246 = 1 ∧ u248 = 1 then 1 else 0
  let u250 : ℕ := if u247 = 1 ∨ u249 = 1 then 1 else 0
  let u251 : ℤ := (sv v9) - u215
  let u252 : ℤ := if u167 = 1 then u251 else u215
  let u253 : ℤ := if u250 = 1 then u252 else (sv v202)
  have f374 := L2.K12_atan_hi u121 u168 (sv v9) u167 u213 u214 u215 u219 u222 u226 u227 u228 u229 u230 u231 u233 u235 u236 u237 (sv v195) u239 u240 u241 u242 u243 (sv v202) u245 u246 u247 u248 u249 u250 u251 u252 (sv v202) u253 e_v9 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f380 f389 f398 f407 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v195 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v18 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v202 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v202 rfl
  let u254 : ℤ := if u164 = 1 then u211 else u212
  let u255 : ℤ := if u164 = 1 then (sv v202) else u253
  have f176 := L2.K19_iso_angle_pt True (sv v3) (sv v99) (sv v106) (sv v107) (sv v43) u115 u121 (sv v125) (sv v132) u160 u162 u166 u168 u164 u163 u212 u253 u211 (sv v202) u254 u255 f177 f180 f219 f256 f289 (L2.p_not_not (L2.p_unot _)) f300 f374 rfl e_v202 rfl rfl
  have f452 := L2.K5_ihalf (sv v2) (sv v2) (sv v42) (sv v256) e_v42 e_v256
  have f456 := L2.K8_in_range True (sv v42) (sv v256) v44 (sv v20) v258 v259 (L2.p_clt (-1) e_v18 e_v44) e_v20 (L2.p_le e_v257 e_v258) e_v259 (L2.X1_top _ k_v259)
  let u260 : ℤ := L2.cosI (sv v256)
  let u261 : ℤ := (sv v28) + u260
  let u262 : ℕ := if u261 < (sv v94) then 1 else 0
  let u263 : ℤ := if u262 = 1 then (sv v94) else u261
  have f466 := L2.K3_cos_lo (sv v256) u260 u261 (sv v94) u263 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u264 : ℕ := if (sv v97) < (sv v256) then 1 else 0
  let u265 : ℤ := if u264 = 1 then (sv v94) else u263
  have f480 := L2.K3_cos_hi (sv v42) (sv t42.2) (sv v267) (sv v33) (sv v269) (L2.p_cos e_t42_2) (L2.p_addc (4) (L2.p_add_comm e_v267) e_v31) e_v33 (L2.p_min e_v268 (L2.p_sel e_v269))
  have f455 := L2.K10_icos True (sv v42) (sv v256) u263 (sv v94) u264 u265 (sv v269) (sv v33) v270 (sv v271) f456 f466 e_v94 (L2.p_clt (843314855) e_v97 (L2.p_ult _ _)) rfl f480 e_v33 (L2.p_ltc (1) e_v104 e_v270) (L2.p_sel e_v271)
  have f495 := L2.K8_in_range True (sv v42) (sv v256) v44 (sv v20) v258 v259 (L2.p_clt (-1) e_v18 e_v44) e_v20 (L2.p_le e_v257 e_v258) e_v259 (L2.X1_top _ k_v259)
  have f494 := L2.K9_isin True (sv v42) (sv v256) (sv t42.1) (sv t256.1) (sv v274) (sv v275) (sv v276) (sv v277) (sv v33) (sv v279) v57 v280 v281 (sv v282) f495 (L2.p_sin e_t42_1) (L2.p_sin e_t256_1) (L2.p_min e_v273 (L2.p_sel e_v274)) (L2.p_addc (-4) (L2.p_add_comm e_v275) e_v28) (L2.p_max e_v273 (L2.p_sel e_v276)) (L2.p_addc (4) (L2.p_add_comm e_v277) e_v31) e_v33 (L2.p_min e_v278 (L2.p_sel e_v279)) (L2.p_ltc (421657430) e_v36 e_v57) (L2.p_clt (421657427) e_v38 e_v280) e_v281 (L2.p_sel e_v282)
  have f531 := L2.K6_imul True (sv v99) (sv v106) (sv v275) (sv v282) (sv v9) v133 v134 v135 v136 v137 v138 v283 v284 v285 v286 v287 v288 v289 v290 v291 v292 (sv v293) v294 v295 (sv v296) v297 v298 (sv v299) v300 v301 (sv v302) (sv v304) (sv v306) e_v9 e_v133 e_v134 e_v135 e_v136 (L2.p_and_comm e_v137) e_v138 e_v283 e_v284 e_v285 e_v286 (L2.p_and_comm e_v287) e_v288 e_v289 e_v290 (L2.X1_top _ k_v290) e_v291 e_v292 (L2.p_sel e_v293) e_v294 e_v295 (L2.p_sel e_v296) e_v297 e_v298 (L2.p_sel e_v299) e_v300 e_v301 (L2.p_sel e_v302) (L2.p_mul (L2.p_mul_comm e_v303) e_v304) (L2.p_mulc (L2.p_mul_comm e_v305) e_v306)
  let u309 : ℕ := if u265 < (sv v9) then 1 else 0
  let u310 : ℤ := if u309 = 1 then (sv v304) else (sv v306)
  have f564 := L2.K11_qdiv u265 (sv v271) (sv v304) (sv v306) v307 v308 (sv v9) u309 u310 v311 (sv v312) (L2.p_clt (0) e_v9 e_v307) e_v308 e_v9 (L2.p_ult _ _) rfl e_v311 (L2.p_sel e_v312)
  let u313 : ℤ := (sv v9) - u265
  let u314 : ℤ := if u309 = 1 then u313 else u265
  let u315 : ℤ := 0
  let u316 : ℕ := if u309 = 1 then 0 else 1
  let u317 : ℤ := L2.cosI u315
  let u318 : ℤ := (sv v28) + u317
  let u319 : ℕ := if u318 < (sv v94) then 1 else 0
  let u320 : ℤ := if u319 = 1 then (sv v94) else u318
  have f582 := L2.K3_cos_lo u315 u317 u318 (sv v94) u320 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u321 : ℤ := (sv v31) + u317
  let u322 : ℕ := if u321 < (sv v33) then 1 else 0
  let u323 : ℤ := if u322 = 1 then u321 else (sv v33)
  have f591 := L2.K3_cos_hi u315 u317 u321 (sv v33) u323 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u324 : ℤ := L2.sinI u315
  let u325 : ℤ := (sv v31) + u324
  let u326 : ℕ := if u325 < (sv v33) then 1 else 0
  let u327 : ℤ := if u326 = 1 then u325 else (sv v33)
  have f600 := L2.K3_sin_hi u315 u324 u325 (sv v33) u327 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u328 : ℤ := (sv v28) + u324
  have f609 := L2.K3_sin_lo u315 u324 u328 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u329 : ℤ := if u316 = 1 then u320 else u323
  let u330 : ℤ := if u316 = 1 then u327 else u328
  let u331 : ℤ := u310 * u330
  let u332 : ℤ := u314 * u329
  let u333 : ℕ := if u332 < u331 then 1 else 0
  let u334 : ℕ := if u333 = 1 then 0 else 1
  let u335 : ℕ := if u331 < u332 then 1 else 0
  let u336 : ℕ := if u335 = 1 then 0 else 1
  let u337 : ℕ := if (sv v9) < u315 then 1 else 0
  let u338 : ℕ := if u337 = 1 then 0 else 1
  let u339 : ℕ := if (sv v195) < u315 then 1 else 0
  let u340 : ℕ := if u339 = 1 then 0 else 1
  let u341 : ℕ := if (sv v18) < u320 then 1 else 0
  let u342 : ℕ := if u334 = 1 ∧ u341 = 1 then 1 else 0
  let u343 : ℕ := if u340 = 1 ∧ u342 = 1 then 1 else 0
  let u344 : ℕ := if u338 = 1 ∨ u343 = 1 then 1 else 0
  let u345 : ℕ := if u315 < (sv v202) then 1 else 0
  let u346 : ℕ := if u345 = 1 then 0 else 1
  let u347 : ℕ := if u336 = 1 ∨ u346 = 1 then 1 else 0
  let u348 : ℕ := if u316 = 1 ∧ u344 = 1 then 1 else 0
  let u349 : ℕ := if u309 = 1 ∧ u347 = 1 then 1 else 0
  let u350 : ℕ := if u348 = 1 ∨ u349 = 1 then 1 else 0
  let u351 : ℤ := (sv v9) - u315
  let u352 : ℤ := if u309 = 1 then u351 else u315
  let u353 : ℤ := if u350 = 1 then u352 else u211
  have f575 := L2.K12_atan_lo u265 u310 (sv v9) u309 u313 u314 u315 u316 u320 u323 u327 u328 u329 u330 u331 u332 u334 u336 u337 u338 (sv v195) u340 u341 u342 u343 u344 (sv v202) u346 u347 u348 u309 u349 u350 u351 u352 u211 u353 e_v9 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f582 f591 f600 f609 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v195 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v18 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v202 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  have f655 := L2.K3_cos_lo (sv v356) (sv t356.2) (sv v358) (sv v94) (sv v360) (L2.p_cos e_t356_2) (L2.p_addc (-4) (L2.p_add_comm e_v358) e_v28) e_v94 (L2.p_max e_v359 (L2.p_sel e_v360))
  have f664 := L2.K3_cos_hi (sv v356) (sv t356.2) (sv v361) (sv v33) (sv v363) (L2.p_cos e_t356_2) (L2.p_addc (4) (L2.p_add_comm e_v361) e_v31) e_v33 (L2.p_min e_v362 (L2.p_sel e_v363))
  have f673 := L2.K3_sin_hi (sv v356) (sv t356.1) (sv v365) (sv v33) (sv v367) (L2.p_sin e_t356_1) (L2.p_addc (4) (L2.p_add_comm e_v365) e_v31) e_v33 (L2.p_min e_v366 (L2.p_sel e_v367))
  have f682 := L2.K3_sin_lo (sv v356) (sv t356.1) (sv v368) (L2.p_sin e_t356_1) (L2.p_addc (-4) (L2.p_add_comm e_v368) e_v28)
  have f649 := L2.K12_atan_hi (sv v271) (sv v312) (sv v9) v311 (sv v354) (sv v355) (sv v356) (sv v360) (sv v363) (sv v367) (sv v368) (sv v369) (sv v370) (sv v371) (sv v372) v374 v376 v377 v378 (sv v195) v380 v381 v382 v383 v384 (sv v202) v386 v387 v388 v389 v390 v391 (sv v392) (sv v393) (sv v202) (sv v394) e_v9 e_v311 e_v354 (L2.p_sel e_v355) (L2.p_hint e_v356) f655 f664 f673 f682 (L2.p_sel e_v369) (L2.p_sel e_v370) (L2.p_mul_comm e_v371) (L2.p_mul_comm e_v372) (L2.p_le e_v373 e_v374) (L2.p_le e_v375 e_v376) e_v377 e_v378 e_v195 (L2.p_le e_v379 e_v380) (L2.p_clt (-1) e_v18 e_v381) e_v382 (L2.p_and_comm e_v383) e_v384 e_v202 (L2.p_le e_v385 e_v386) (L2.p_or_comm e_v387) e_v388 e_v389 (L2.p_and_comm e_v390) e_v391 e_v392 (L2.p_sel e_v393) e_v202 (L2.p_sel e_v394)
  let u395 : ℤ := if v308 = 1 then u211 else u353
  have f451 := L2.K19_iso_angle_pt True (sv v2) (sv v99) (sv v106) (sv v42) (sv v256) u265 (sv v271) (sv v275) (sv v282) (sv v304) (sv v306) u310 (sv v312) v308 v307 u353 (sv v394) u211 (sv v202) u395 (sv v396) f452 f455 f494 f531 f564 (L2.p_not_not e_v308) f575 f649 rfl e_v202 rfl (L2.p_sel e_v396)
  have f136 := L2.K20_iso_angle True (sv v2) (sv v3) (sv v0) (sv v1) (sv v99) (sv v106) u254 u255 u164 u395 (sv v396) v308 f137 f176 f451
  have f728 := L2.K8_in_range True (sv v0) (sv v1) v19 (sv v20) v22 v23 (L2.p_clt (-1) e_v18 e_v19) e_v20 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f727 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v27) (sv v29) (sv v30) (sv v32) (sv v33) (sv v35) v37 v39 v40 (sv v41) f728 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v26 (L2.p_sel e_v27)) (L2.p_addc (-4) e_v29 e_v28) (L2.p_max e_v26 (L2.p_sel e_v30)) (L2.p_addc (4) e_v32 e_v31) e_v33 (L2.p_min e_v34 (L2.p_sel e_v35)) (L2.p_ltc (421657430) e_v36 e_v37) (L2.p_clt (421657427) e_v38 e_v39) e_v40 (L2.p_sel e_v41)
  have f764 := L2.K5_ihalf (sv v4) (sv v5) (sv v397) (sv v398) e_v397 e_v398
  have f768 := L2.K8_in_range True (sv v397) (sv v398) v399 (sv v20) v401 v402 (L2.p_clt (-1) e_v18 e_v399) e_v20 (L2.p_le e_v400 e_v401) e_v402 (L2.X1_top _ k_v402)
  have f767 := L2.K9_isin True (sv v397) (sv v398) (sv t397.1) (sv t398.1) (sv v406) (sv v407) (sv v408) (sv v409) (sv v33) (sv v411) v412 v413 v414 (sv v415) f768 (L2.p_sin e_t397_1) (L2.p_sin e_t398_1) (L2.p_min e_v405 (L2.p_sel e_v406)) (L2.p_addc (-4) (L2.p_add_comm e_v407) e_v28) (L2.p_max e_v405 (L2.p_sel e_v408)) (L2.p_addc (4) (L2.p_add_comm e_v409) e_v31) e_v33 (L2.p_min e_v410 (L2.p_sel e_v411)) (L2.p_ltc (421657430) e_v36 e_v412) (L2.p_clt (421657427) e_v38 e_v413) e_v414 (L2.p_sel e_v415)
  have f804 := L2.K6_imul True (sv v29) (sv v41) (sv v407) (sv v415) (sv v9) v61 v62 v63 v64 v65 v66 v416 v417 v418 v419 v420 v421 v422 v423 v424 v425 (sv v426) v427 v428 (sv v429) v430 v431 (sv v432) v433 v434 (sv v435) (sv v437) (sv v439) e_v9 e_v61 e_v62 e_v63 e_v64 (L2.p_and_comm e_v65) e_v66 e_v416 e_v417 e_v418 e_v419 (L2.p_and_comm e_v420) e_v421 e_v422 e_v423 (L2.X1_top _ k_v423) e_v424 e_v425 (L2.p_sel e_v426) e_v427 e_v428 (L2.p_sel e_v429) e_v430 e_v431 (L2.p_sel e_v432) e_v433 e_v434 (L2.p_sel e_v435) (L2.p_mul (L2.p_mul_comm e_v436) e_v437) (L2.p_mulc (L2.p_mul_comm e_v438) e_v439)
  have f726 := L2.K14_iso_base_a True (sv v4) (sv v5) (sv v0) (sv v1) (sv v29) (sv v41) (sv v397) (sv v398) (sv v407) (sv v415) (sv v437) (sv v439) v440 f727 f764 f767 f804 (L2.p_clt (-1) e_v18 e_v440) (L2.X1_top _ k_v440)
  have f843 := L2.K8_in_range True (sv v0) (sv v1) v19 (sv v20) v22 v23 (L2.p_clt (-1) e_v18 e_v19) e_v20 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f853 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v93) (sv v94) (sv v96) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v93) e_v28) e_v94 (L2.p_max e_v95 (L2.p_sel e_v96))
  have f867 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v101) (sv v33) (sv v103) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v101) e_v31) e_v33 (L2.p_min e_v102 (L2.p_sel e_v103))
  have f842 := L2.K10_icos True (sv v0) (sv v1) (sv v96) (sv v94) v98 (sv v99) (sv v103) (sv v33) v105 (sv v106) f843 f853 e_v94 (L2.p_clt (843314855) e_v97 e_v98) (L2.p_sel e_v99) f867 e_v33 (L2.p_ltc (1) e_v104 e_v105) (L2.p_sel e_v106)
  have f882 := L2.K5_ihalf (sv v5) (sv v5) (sv v441) (sv v398) e_v441 e_v398
  have f886 := L2.K8_in_range True (sv v441) (sv v398) v442 (sv v20) v401 v443 (L2.p_clt (-1) e_v18 e_v442) e_v20 (L2.p_le e_v400 e_v401) (L2.p_and_comm e_v443) (L2.X1_top _ k_v443)
  let u444 : ℤ := L2.cosI (sv v398)
  let u445 : ℤ := (sv v28) + u444
  let u446 : ℕ := if u445 < (sv v94) then 1 else 0
  let u447 : ℤ := if u446 = 1 then (sv v94) else u445
  have f896 := L2.K3_cos_lo (sv v398) u444 u445 (sv v94) u447 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u448 : ℕ := if (sv v97) < (sv v398) then 1 else 0
  let u449 : ℤ := if u448 = 1 then (sv v94) else u447
  let u450 : ℤ := L2.cosI (sv v441)
  let u451 : ℤ := (sv v31) + u450
  let u452 : ℕ := if u451 < (sv v33) then 1 else 0
  let u453 : ℤ := if u452 = 1 then u451 else (sv v33)
  have f910 := L2.K3_cos_hi (sv v441) u450 u451 (sv v33) u453 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u454 : ℕ := if (sv v441) < (sv v104) then 1 else 0
  let u455 : ℤ := if u454 = 1 then (sv v33) else u453
  have f885 := L2.K10_icos True (sv v441) (sv v398) u447 (sv v94) u448 u449 u453 (sv v33) u454 u455 f886 f896 e_v94 (L2.p_clt (843314855) e_v97 (L2.p_ult _ _)) rfl f910 e_v33 (L2.p_ltc (1) e_v104 (L2.p_ult _ _)) rfl
  have f925 := L2.K8_in_range True (sv v441) (sv v398) v442 (sv v20) v401 v443 (L2.p_clt (-1) e_v18 e_v442) e_v20 (L2.p_le e_v400 e_v401) (L2.p_and_comm e_v443) (L2.X1_top _ k_v443)
  have f924 := L2.K9_isin True (sv v441) (sv v398) (sv t441.1) (sv t398.1) (sv v458) (sv v459) (sv v460) (sv v461) (sv v33) (sv v463) v464 v413 v465 (sv v466) f925 (L2.p_sin e_t441_1) (L2.p_sin e_t398_1) (L2.p_min e_v457 (L2.p_sel e_v458)) (L2.p_addc (-4) (L2.p_add_comm e_v459) e_v28) (L2.p_max e_v457 (L2.p_sel e_v460)) (L2.p_addc (4) (L2.p_add_comm e_v461) e_v31) e_v33 (L2.p_min e_v462 (L2.p_sel e_v463)) (L2.p_ltc (421657430) e_v36 e_v464) (L2.p_clt (421657427) e_v38 e_v413) (L2.p_and_comm e_v465) (L2.p_sel e_v466)
  let u468 : ℕ := if v467 = 1 then 0 else 1
  let u470 : ℕ := if v469 = 1 then 0 else 1
  let u471 : ℕ := if v467 = 1 ∧ u470 = 1 then 1 else 0
  let u475 : ℕ := if v134 = 1 ∧ v472 = 1 then 1 else 0
  let u476 : ℕ := if u471 = 1 ∨ u475 = 1 then 1 else 0
  let u477 : ℤ := if u476 = 1 then (sv v106) else (sv v99)
  let u478 : ℕ := if v138 = 1 ∧ u468 = 1 then 1 else 0
  let u479 : ℕ := if v137 = 1 ∨ u478 = 1 then 1 else 0
  let u480 : ℤ := if u479 = 1 then (sv v466) else (sv v459)
  let u481 : ℕ := if v137 = 1 ∧ v472 = 1 then 1 else 0
  let u482 : ℕ := if u471 = 1 ∨ u481 = 1 then 1 else 0
  let u483 : ℤ := if u482 = 1 then (sv v99) else (sv v106)
  let u484 : ℕ := if v138 = 1 ∧ u471 = 1 then 1 else 0
  let u485 : ℕ := if v137 = 1 ∨ u484 = 1 then 1 else 0
  let u486 : ℤ := if u485 = 1 then (sv v459) else (sv v466)
  let u487 : ℤ := u477 * u480
  let u488 : ℤ := u487 / 2 ^ 28
  let u489 : ℤ := u483 * u486
  let u490 : ℤ := -((-u489) / 2 ^ 28)
  have f961 := L2.K6_imul True (sv v99) (sv v106) (sv v459) (sv v466) (sv v9) v133 v134 v135 v136 v137 v138 v467 u468 v469 u470 u471 v472 v473 v474 u475 u476 u477 u478 u479 u480 u481 u482 u483 u484 u485 u486 u488 u490 e_v9 e_v133 e_v134 e_v135 e_v136 (L2.p_and_comm e_v137) e_v138 e_v467 (L2.p_unot _) e_v469 (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) e_v472 e_v473 e_v474 (L2.X1_top _ k_v474) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl)
  let u491 : ℕ := if (sv v9) < u488 then 1 else 0
  let u492 : ℕ := if u491 = 1 then 0 else 1
  let u493 : ℕ := if u449 < (sv v9) then 1 else 0
  let u494 : ℤ := if u493 = 1 then u488 else u490
  let u495 : ℕ := if u455 < (sv v9) then 1 else 0
  let u496 : ℤ := if u495 = 1 then u490 else u488
  have f994 := L2.K11_qdiv u449 u455 u488 u490 u491 u492 (sv v9) u493 u494 u495 u496 (L2.p_clt (0) e_v9 (L2.p_ult _ _)) (L2.p_unot _) e_v9 (L2.p_ult _ _) rfl (L2.p_ult _ _) rfl
  let u497 : ℤ := (sv v9) - u449
  let u498 : ℤ := if u493 = 1 then u497 else u449
  let u499 : ℤ := 0
  let u500 : ℕ := if u493 = 1 then 0 else 1
  let u501 : ℤ := L2.cosI u499
  let u502 : ℤ := (sv v28) + u501
  let u503 : ℕ := if u502 < (sv v94) then 1 else 0
  let u504 : ℤ := if u503 = 1 then (sv v94) else u502
  have f1012 := L2.K3_cos_lo u499 u501 u502 (sv v94) u504 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u505 : ℤ := (sv v31) + u501
  let u506 : ℕ := if u505 < (sv v33) then 1 else 0
  let u507 : ℤ := if u506 = 1 then u505 else (sv v33)
  have f1021 := L2.K3_cos_hi u499 u501 u505 (sv v33) u507 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u508 : ℤ := L2.sinI u499
  let u509 : ℤ := (sv v31) + u508
  let u510 : ℕ := if u509 < (sv v33) then 1 else 0
  let u511 : ℤ := if u510 = 1 then u509 else (sv v33)
  have f1030 := L2.K3_sin_hi u499 u508 u509 (sv v33) u511 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u512 : ℤ := (sv v28) + u508
  have f1039 := L2.K3_sin_lo u499 u508 u512 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u513 : ℤ := if u500 = 1 then u504 else u507
  let u514 : ℤ := if u500 = 1 then u511 else u512
  let u515 : ℤ := u494 * u514
  let u516 : ℤ := u498 * u513
  let u517 : ℕ := if u516 < u515 then 1 else 0
  let u518 : ℕ := if u517 = 1 then 0 else 1
  let u519 : ℕ := if u515 < u516 then 1 else 0
  let u520 : ℕ := if u519 = 1 then 0 else 1
  let u521 : ℕ := if (sv v9) < u499 then 1 else 0
  let u522 : ℕ := if u521 = 1 then 0 else 1
  let u523 : ℕ := if (sv v195) < u499 then 1 else 0
  let u524 : ℕ := if u523 = 1 then 0 else 1
  let u525 : ℕ := if (sv v18) < u504 then 1 else 0
  let u526 : ℕ := if u518 = 1 ∧ u525 = 1 then 1 else 0
  let u527 : ℕ := if u524 = 1 ∧ u526 = 1 then 1 else 0
  let u528 : ℕ := if u522 = 1 ∨ u527 = 1 then 1 else 0
  let u529 : ℕ := if u499 < (sv v202) then 1 else 0
  let u530 : ℕ := if u529 = 1 then 0 else 1
  let u531 : ℕ := if u520 = 1 ∨ u530 = 1 then 1 else 0
  let u532 : ℕ := if u500 = 1 ∧ u528 = 1 then 1 else 0
  let u533 : ℕ := if u493 = 1 ∧ u531 = 1 then 1 else 0
  let u534 : ℕ := if u532 = 1 ∨ u533 = 1 then 1 else 0
  let u535 : ℤ := (sv v9) - u499
  let u536 : ℤ := if u493 = 1 then u535 else u499
  let u537 : ℤ := if u534 = 1 then u536 else u211
  have f1005 := L2.K12_atan_lo u449 u494 (sv v9) u493 u497 u498 u499 u500 u504 u507 u511 u512 u513 u514 u515 u516 u518 u520 u521 u522 (sv v195) u524 u525 u526 u527 u528 (sv v202) u530 u531 u532 u493 u533 u534 u535 u536 u211 u537 e_v9 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f1012 f1021 f1030 f1039 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v195 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v18 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v202 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  let u538 : ℤ := (sv v9) - u455
  let u539 : ℤ := if u495 = 1 then u538 else u455
  let u540 : ℤ := 0
  let u541 : ℤ := L2.cosI u540
  let u542 : ℤ := (sv v28) + u541
  let u543 : ℕ := if u542 < (sv v94) then 1 else 0
  let u544 : ℤ := if u543 = 1 then (sv v94) else u542
  have f1085 := L2.K3_cos_lo u540 u541 u542 (sv v94) u544 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u545 : ℤ := (sv v31) + u541
  let u546 : ℕ := if u545 < (sv v33) then 1 else 0
  let u547 : ℤ := if u546 = 1 then u545 else (sv v33)
  have f1094 := L2.K3_cos_hi u540 u541 u545 (sv v33) u547 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u548 : ℤ := L2.sinI u540
  let u549 : ℤ := (sv v31) + u548
  let u550 : ℕ := if u549 < (sv v33) then 1 else 0
  let u551 : ℤ := if u550 = 1 then u549 else (sv v33)
  have f1103 := L2.K3_sin_hi u540 u548 u549 (sv v33) u551 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u552 : ℤ := (sv v28) + u548
  have f1112 := L2.K3_sin_lo u540 u548 u552 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u553 : ℤ := if u495 = 1 then u544 else u547
  let u554 : ℤ := if u495 = 1 then u551 else u552
  let u555 : ℤ := u496 * u554
  let u556 : ℤ := u539 * u553
  let u557 : ℕ := if u556 < u555 then 1 else 0
  let u558 : ℕ := if u557 = 1 then 0 else 1
  let u559 : ℕ := if u555 < u556 then 1 else 0
  let u560 : ℕ := if u559 = 1 then 0 else 1
  let u561 : ℕ := if (sv v9) < u540 then 1 else 0
  let u562 : ℕ := if u561 = 1 then 0 else 1
  let u563 : ℕ := if (sv v195) < u540 then 1 else 0
  let u564 : ℕ := if u563 = 1 then 0 else 1
  let u565 : ℕ := if (sv v18) < u544 then 1 else 0
  let u566 : ℕ := if u558 = 1 ∧ u565 = 1 then 1 else 0
  let u567 : ℕ := if u564 = 1 ∧ u566 = 1 then 1 else 0
  let u568 : ℕ := if u562 = 1 ∨ u567 = 1 then 1 else 0
  let u569 : ℕ := if u540 < (sv v202) then 1 else 0
  let u570 : ℕ := if u569 = 1 then 0 else 1
  let u571 : ℕ := if u560 = 1 ∨ u570 = 1 then 1 else 0
  let u572 : ℕ := if u495 = 1 ∧ u568 = 1 then 1 else 0
  let u573 : ℕ := if u495 = 1 then 0 else 1
  let u574 : ℕ := if u571 = 1 ∧ u573 = 1 then 1 else 0
  let u575 : ℕ := if u572 = 1 ∨ u574 = 1 then 1 else 0
  let u576 : ℤ := (sv v9) - u540
  let u577 : ℤ := if u495 = 1 then u576 else u540
  let u578 : ℤ := if u575 = 1 then u577 else (sv v202)
  have f1079 := L2.K12_atan_hi u455 u496 (sv v9) u495 u538 u539 u540 u544 u547 u551 u552 u553 u554 u555 u556 u558 u560 u561 u562 (sv v195) u564 u565 u566 u567 u568 (sv v202) u570 u571 u572 u573 u574 u575 u576 u577 (sv v202) u578 e_v9 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f1085 f1094 f1103 f1112 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v195 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v18 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v202 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v202 rfl
  let u579 : ℤ := if u492 = 1 then u211 else u537
  let u580 : ℤ := if u492 = 1 then (sv v202) else u578
  have f881 := L2.K19_iso_angle_pt True (sv v5) (sv v99) (sv v106) (sv v441) (sv v398) u449 u455 (sv v459) (sv v466) u488 u490 u494 u496 u492 u491 u537 u578 u211 (sv v202) u579 u580 f882 f885 f924 f961 f994 (L2.p_not_not (L2.p_unot _)) f1005 f1079 rfl e_v202 rfl rfl
  have f1157 := L2.K5_ihalf (sv v4) (sv v4) (sv v397) (sv v581) e_v397 e_v581
  have f1161 := L2.K8_in_range True (sv v397) (sv v581) v399 (sv v20) v583 v584 (L2.p_clt (-1) e_v18 e_v399) e_v20 (L2.p_le e_v582 e_v583) e_v584 (L2.X1_top _ k_v584)
  let u585 : ℤ := L2.cosI (sv v581)
  let u586 : ℤ := (sv v28) + u585
  let u587 : ℕ := if u586 < (sv v94) then 1 else 0
  let u588 : ℤ := if u587 = 1 then (sv v94) else u586
  have f1171 := L2.K3_cos_lo (sv v581) u585 u586 (sv v94) u588 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u589 : ℕ := if (sv v97) < (sv v581) then 1 else 0
  let u590 : ℤ := if u589 = 1 then (sv v94) else u588
  have f1185 := L2.K3_cos_hi (sv v397) (sv t397.2) (sv v592) (sv v33) (sv v594) (L2.p_cos e_t397_2) (L2.p_addc (4) (L2.p_add_comm e_v592) e_v31) e_v33 (L2.p_min e_v593 (L2.p_sel e_v594))
  have f1160 := L2.K10_icos True (sv v397) (sv v581) u588 (sv v94) u589 u590 (sv v594) (sv v33) v595 (sv v596) f1161 f1171 e_v94 (L2.p_clt (843314855) e_v97 (L2.p_ult _ _)) rfl f1185 e_v33 (L2.p_ltc (1) e_v104 e_v595) (L2.p_sel e_v596)
  have f1200 := L2.K8_in_range True (sv v397) (sv v581) v399 (sv v20) v583 v584 (L2.p_clt (-1) e_v18 e_v399) e_v20 (L2.p_le e_v582 e_v583) e_v584 (L2.X1_top _ k_v584)
  have f1199 := L2.K9_isin True (sv v397) (sv v581) (sv t397.1) (sv t581.1) (sv v599) (sv v600) (sv v601) (sv v602) (sv v33) (sv v604) v412 v605 v606 (sv v607) f1200 (L2.p_sin e_t397_1) (L2.p_sin e_t581_1) (L2.p_min e_v598 (L2.p_sel e_v599)) (L2.p_addc (-4) (L2.p_add_comm e_v600) e_v28) (L2.p_max e_v598 (L2.p_sel e_v601)) (L2.p_addc (4) (L2.p_add_comm e_v602) e_v31) e_v33 (L2.p_min e_v603 (L2.p_sel e_v604)) (L2.p_ltc (421657430) e_v36 e_v412) (L2.p_clt (421657427) e_v38 e_v605) e_v606 (L2.p_sel e_v607)
  have f1236 := L2.K6_imul True (sv v99) (sv v106) (sv v600) (sv v607) (sv v9) v133 v134 v135 v136 v137 v138 v608 v609 v610 v611 v612 v613 v614 v615 v616 v617 (sv v618) v619 v620 (sv v621) v622 v623 (sv v624) v625 v626 (sv v627) (sv v629) (sv v631) e_v9 e_v133 e_v134 e_v135 e_v136 (L2.p_and_comm e_v137) e_v138 e_v608 e_v609 e_v610 e_v611 (L2.p_and_comm e_v612) e_v613 e_v614 e_v615 (L2.X1_top _ k_v615) e_v616 e_v617 (L2.p_sel e_v618) e_v619 e_v620 (L2.p_sel e_v621) e_v622 e_v623 (L2.p_sel e_v624) e_v625 e_v626 (L2.p_sel e_v627) (L2.p_mul (L2.p_mul_comm e_v628) e_v629) (L2.p_mulc (L2.p_mul_comm e_v630) e_v631)
  let u634 : ℕ := if u590 < (sv v9) then 1 else 0
  let u635 : ℤ := if u634 = 1 then (sv v629) else (sv v631)
  have f1269 := L2.K11_qdiv u590 (sv v596) (sv v629) (sv v631) v632 v633 (sv v9) u634 u635 v636 (sv v637) (L2.p_clt (0) e_v9 e_v632) e_v633 e_v9 (L2.p_ult _ _) rfl e_v636 (L2.p_sel e_v637)
  let u638 : ℤ := (sv v9) - u590
  let u639 : ℤ := if u634 = 1 then u638 else u590
  let u640 : ℤ := 0
  let u641 : ℕ := if u634 = 1 then 0 else 1
  let u642 : ℤ := L2.cosI u640
  let u643 : ℤ := (sv v28) + u642
  let u644 : ℕ := if u643 < (sv v94) then 1 else 0
  let u645 : ℤ := if u644 = 1 then (sv v94) else u643
  have f1287 := L2.K3_cos_lo u640 u642 u643 (sv v94) u645 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u646 : ℤ := (sv v31) + u642
  let u647 : ℕ := if u646 < (sv v33) then 1 else 0
  let u648 : ℤ := if u647 = 1 then u646 else (sv v33)
  have f1296 := L2.K3_cos_hi u640 u642 u646 (sv v33) u648 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u649 : ℤ := L2.sinI u640
  let u650 : ℤ := (sv v31) + u649
  let u651 : ℕ := if u650 < (sv v33) then 1 else 0
  let u652 : ℤ := if u651 = 1 then u650 else (sv v33)
  have f1305 := L2.K3_sin_hi u640 u649 u650 (sv v33) u652 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v31) e_v33 (L2.p_min (L2.p_ult _ _) rfl)
  let u653 : ℤ := (sv v28) + u649
  have f1314 := L2.K3_sin_lo u640 u649 u653 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28)
  let u654 : ℤ := if u641 = 1 then u645 else u648
  let u655 : ℤ := if u641 = 1 then u652 else u653
  let u656 : ℤ := u635 * u655
  let u657 : ℤ := u639 * u654
  let u658 : ℕ := if u657 < u656 then 1 else 0
  let u659 : ℕ := if u658 = 1 then 0 else 1
  let u660 : ℕ := if u656 < u657 then 1 else 0
  let u661 : ℕ := if u660 = 1 then 0 else 1
  let u662 : ℕ := if (sv v9) < u640 then 1 else 0
  let u663 : ℕ := if u662 = 1 then 0 else 1
  let u664 : ℕ := if (sv v195) < u640 then 1 else 0
  let u665 : ℕ := if u664 = 1 then 0 else 1
  let u666 : ℕ := if (sv v18) < u645 then 1 else 0
  let u667 : ℕ := if u659 = 1 ∧ u666 = 1 then 1 else 0
  let u668 : ℕ := if u665 = 1 ∧ u667 = 1 then 1 else 0
  let u669 : ℕ := if u663 = 1 ∨ u668 = 1 then 1 else 0
  let u670 : ℕ := if u640 < (sv v202) then 1 else 0
  let u671 : ℕ := if u670 = 1 then 0 else 1
  let u672 : ℕ := if u661 = 1 ∨ u671 = 1 then 1 else 0
  let u673 : ℕ := if u641 = 1 ∧ u669 = 1 then 1 else 0
  let u674 : ℕ := if u634 = 1 ∧ u672 = 1 then 1 else 0
  let u675 : ℕ := if u673 = 1 ∨ u674 = 1 then 1 else 0
  let u676 : ℤ := (sv v9) - u640
  let u677 : ℤ := if u634 = 1 then u676 else u640
  let u678 : ℤ := if u675 = 1 then u677 else u211
  have f1280 := L2.K12_atan_lo u590 u635 (sv v9) u634 u638 u639 u640 u641 u645 u648 u652 u653 u654 u655 u656 u657 u659 u661 u662 u663 (sv v195) u665 u666 u667 u668 u669 (sv v202) u671 u672 u673 u634 u674 u675 u676 u677 u211 u678 e_v9 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f1287 f1296 f1305 f1314 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v195 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v18 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v202 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  have f1360 := L2.K3_cos_lo (sv v681) (sv t681.2) (sv v683) (sv v94) (sv v685) (L2.p_cos e_t681_2) (L2.p_addc (-4) (L2.p_add_comm e_v683) e_v28) e_v94 (L2.p_max e_v684 (L2.p_sel e_v685))
  have f1369 := L2.K3_cos_hi (sv v681) (sv t681.2) (sv v686) (sv v33) (sv v688) (L2.p_cos e_t681_2) (L2.p_addc (4) (L2.p_add_comm e_v686) e_v31) e_v33 (L2.p_min e_v687 (L2.p_sel e_v688))
  have f1378 := L2.K3_sin_hi (sv v681) (sv t681.1) (sv v690) (sv v33) (sv v692) (L2.p_sin e_t681_1) (L2.p_addc (4) (L2.p_add_comm e_v690) e_v31) e_v33 (L2.p_min e_v691 (L2.p_sel e_v692))
  have f1387 := L2.K3_sin_lo (sv v681) (sv t681.1) (sv v693) (L2.p_sin e_t681_1) (L2.p_addc (-4) (L2.p_add_comm e_v693) e_v28)
  have f1354 := L2.K12_atan_hi (sv v596) (sv v637) (sv v9) v636 (sv v679) (sv v680) (sv v681) (sv v685) (sv v688) (sv v692) (sv v693) (sv v694) (sv v695) (sv v696) (sv v697) v699 v701 v702 v703 (sv v195) v705 v706 v707 v708 v709 (sv v202) v711 v712 v713 v714 v715 v716 (sv v717) (sv v718) (sv v202) (sv v719) e_v9 e_v636 e_v679 (L2.p_sel e_v680) (L2.p_hint e_v681) f1360 f1369 f1378 f1387 (L2.p_sel e_v694) (L2.p_sel e_v695) (L2.p_mul_comm e_v696) (L2.p_mul_comm e_v697) (L2.p_le e_v698 e_v699) (L2.p_le e_v700 e_v701) e_v702 e_v703 e_v195 (L2.p_le e_v704 e_v705) (L2.p_clt (-1) e_v18 e_v706) e_v707 (L2.p_and_comm e_v708) e_v709 e_v202 (L2.p_le e_v710 e_v711) (L2.p_or_comm e_v712) e_v713 e_v714 (L2.p_and_comm e_v715) e_v716 e_v717 (L2.p_sel e_v718) e_v202 (L2.p_sel e_v719)
  let u720 : ℤ := if v633 = 1 then u211 else u678
  have f1156 := L2.K19_iso_angle_pt True (sv v4) (sv v99) (sv v106) (sv v397) (sv v581) u590 (sv v596) (sv v600) (sv v607) (sv v629) (sv v631) u635 (sv v637) v633 v632 u678 (sv v719) u211 (sv v202) u720 (sv v721) f1157 f1160 f1199 f1236 f1269 (L2.p_not_not e_v633) f1280 f1354 rfl e_v202 rfl (L2.p_sel e_v721)
  have f841 := L2.K20_iso_angle True (sv v4) (sv v5) (sv v0) (sv v1) (sv v99) (sv v106) u579 u580 u492 u720 (sv v721) v633 f842 f881 f1156
  have f1433 := L2.K8_in_range True (sv v0) (sv v1) v19 (sv v20) v22 v23 (L2.p_clt (-1) e_v18 e_v19) e_v20 (L2.p_le e_v21 e_v22) e_v23 (L2.X1_top _ k_v23)
  have f1432 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v27) (sv v29) (sv v30) (sv v32) (sv v33) (sv v35) v37 v39 v40 (sv v41) f1433 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v26 (L2.p_sel e_v27)) (L2.p_addc (-4) e_v29 e_v28) (L2.p_max e_v26 (L2.p_sel e_v30)) (L2.p_addc (4) e_v32 e_v31) e_v33 (L2.p_min e_v34 (L2.p_sel e_v35)) (L2.p_ltc (421657430) e_v36 e_v37) (L2.p_clt (421657427) e_v38 e_v39) e_v40 (L2.p_sel e_v41)
  have f1469 := L2.K5_ihalf u17 (sv v7) (sv v723) (sv v724) (L2.X2_push (fun z : ℤ => z / 2) v16 u17 (sv v7) (sv v14) (sv v722) (sv v195) (sv v723) rfl e_v722 (L2.p_half_cc (421657428) (843314856) e_v195 e_v14 (by norm_num)) (L2.p_sel e_v723)) e_v724
  have f1477 := L2.K8_in_range True (sv v723) (sv v724) v725 (sv v20) v727 v728 (L2.p_clt (-1) e_v18 e_v725) e_v20 (L2.p_le e_v726 e_v727) e_v728 (L2.X1_top _ k_v728)
  have f1476 := L2.K9_isin True (sv v723) (sv v724) (sv t723.1) (sv t724.1) (sv v732) (sv v733) (sv v734) (sv v735) (sv v33) (sv v737) v738 v739 v740 (sv v741) f1477 (L2.p_sin e_t723_1) (L2.p_sin e_t724_1) (L2.p_min e_v731 (L2.p_sel e_v732)) (L2.p_addc (-4) (L2.p_add_comm e_v733) e_v28) (L2.p_max e_v731 (L2.p_sel e_v734)) (L2.p_addc (4) (L2.p_add_comm e_v735) e_v31) e_v33 (L2.p_min e_v736 (L2.p_sel e_v737)) (L2.p_ltc (421657430) e_v36 e_v738) (L2.p_clt (421657427) e_v38 e_v739) e_v740 (L2.p_sel e_v741)
  have f1513 := L2.K6_imul True (sv v29) (sv v41) (sv v733) (sv v741) (sv v9) v61 v62 v63 v64 v65 v66 v742 v743 v744 v745 v746 v747 v748 v749 v750 v751 (sv v752) v753 v754 (sv v755) v756 v757 (sv v758) v759 v760 (sv v761) (sv v763) (sv v765) e_v9 e_v61 e_v62 e_v63 e_v64 (L2.p_and_comm e_v65) e_v66 e_v742 e_v743 e_v744 e_v745 (L2.p_and_comm e_v746) e_v747 e_v748 e_v749 (L2.X1_top _ k_v749) e_v750 e_v751 (L2.p_sel e_v752) e_v753 e_v754 (L2.p_sel e_v755) e_v756 e_v757 (L2.p_sel e_v758) e_v759 e_v760 (L2.p_sel e_v761) (L2.p_mul (L2.p_mul_comm e_v762) e_v763) (L2.p_mulc (L2.p_mul_comm e_v764) e_v765)
  have f1431 := L2.K14_iso_base_a True u17 (sv v7) (sv v0) (sv v1) (sv v29) (sv v41) (sv v723) (sv v724) (sv v733) (sv v741) (sv v763) (sv v765) v766 f1432 f1469 f1476 f1513 (L2.p_clt (-1) e_v18 e_v766) (L2.X1_top _ k_v766)
  have f1552 := L2.K15_a_open (sv v763) (sv v765) v767 v768 v769 (L2.p_clt (0) e_v9 e_v767) (L2.p_ltc (268435456) e_v33 e_v768) e_v769
  have f1560 := L2.K15_a_open (sv v88) (sv v90) v770 v771 v772 (L2.p_clt (0) e_v9 e_v770) (L2.p_ltc (268435456) e_v33 e_v771) e_v772
  have f1568 := L2.K15_a_open (sv v437) (sv v439) v773 v774 v775 (L2.p_clt (0) e_v9 e_v773) (L2.p_ltc (268435456) e_v33 e_v774) e_v775
  have f1578 := L2.K16_a_cos (True ∧ v777 = 1) (sv v763) (sv v765) (sv v33) (sv v779) (sv v780) (sv v781) (sv v94) (sv v783) (sv v785) (sv v786) (sv v787) e_v33 (L2.p_mulc e_v778 e_v779) e_v780 e_v781 e_v94 (L2.p_max e_v782 (L2.p_sel e_v783)) (L2.p_mul e_v784 e_v785) e_v786 e_v787
  have f1592 := L2.K16_a_cos (True ∧ v777 = 1) (sv v437) (sv v439) (sv v33) (sv v789) (sv v790) (sv v791) (sv v94) (sv v793) (sv v795) (sv v796) (sv v797) e_v33 (L2.p_mulc e_v788 e_v789) e_v790 e_v791 e_v94 (L2.p_max e_v792 (L2.p_sel e_v793)) (L2.p_mul e_v794 e_v795) e_v796 e_v797
  have f1606 := L2.K16_a_cos (True ∧ v777 = 1) (sv v88) (sv v90) (sv v33) (sv v799) (sv v800) (sv v801) (sv v94) (sv v803) (sv v805) (sv v806) (sv v807) e_v33 (L2.p_mulc e_v798 e_v799) e_v800 e_v801 e_v94 (L2.p_max e_v802 (L2.p_sel e_v803)) (L2.p_mul e_v804 e_v805) e_v806 e_v807
  have f1620 := L2.K6_imul (True ∧ v777 = 1) (sv v783) (sv v787) (sv v803) (sv v807) (sv v9) v808 v809 v810 v811 v812 v813 v814 v815 v816 v817 v818 v819 v820 v821 v824 v825 (sv v826) v827 v828 (sv v829) v830 v831 (sv v832) v833 v834 (sv v835) (sv v837) (sv v839) e_v9 e_v808 e_v809 e_v810 e_v811 (L2.p_and_comm e_v812) e_v813 e_v814 e_v815 e_v816 e_v817 (L2.p_and_comm e_v818) e_v819 e_v820 e_v821 (L2.X1_step True v777 v822 v821 v823 e_v822 (L2.p_or_comm e_v823) (L2.X1_top _ k_v823)) e_v824 e_v825 (L2.p_sel e_v826) e_v827 e_v828 (L2.p_sel e_v829) e_v830 e_v831 (L2.p_sel e_v832) e_v833 e_v834 (L2.p_sel e_v835) (L2.p_mul (L2.p_mul_comm e_v836) e_v837) (L2.p_mulc (L2.p_mul_comm e_v838) e_v839)
  have f1655 := L2.K4_isub (sv v793) (sv v797) (sv v837) (sv v839) (sv v840) (sv v841) e_v840 e_v841
  have f1658 := L2.K6_imul (True ∧ v777 = 1) (sv v783) (sv v787) (sv v793) (sv v797) (sv v9) v808 v809 v810 v811 v812 v813 v842 v843 v844 v845 v846 v847 v848 v849 v851 v852 (sv v853) v854 v855 (sv v856) v857 v858 (sv v859) v860 v861 (sv v862) (sv v864) (sv v866) e_v9 e_v808 e_v809 e_v810 e_v811 (L2.p_and_comm e_v812) e_v813 e_v842 e_v843 e_v844 e_v845 (L2.p_and_comm e_v846) e_v847 e_v848 e_v849 (L2.X1_step True v777 v822 v849 v850 e_v822 e_v850 (L2.X1_top _ k_v850)) e_v851 e_v852 (L2.p_sel e_v853) e_v854 e_v855 (L2.p_sel e_v856) e_v857 e_v858 (L2.p_sel e_v859) e_v860 e_v861 (L2.p_sel e_v862) (L2.p_mul (L2.p_mul_comm e_v863) e_v864) (L2.p_mulc (L2.p_mul_comm e_v865) e_v866)
  have f1693 := L2.K4_isub (sv v803) (sv v807) (sv v864) (sv v866) (sv v867) (sv v868) e_v867 e_v868
  let u881 : ℤ := -((-(sv v784)) / 2 ^ 28)
  let u882 : ℤ := u881 + u881
  let u883 : ℤ := (sv v33) - u882
  let u884 : ℕ := if u883 < (sv v94) then 1 else 0
  let u885 : ℤ := if u884 = 1 then (sv v94) else u883
  have f1720 := L2.K16_a_cos (True ∧ v777 = 1) (sv v763) (sv v763) (sv v33) u881 u882 u883 (sv v94) u885 (sv v785) (sv v786) (sv v787) e_v33 (L2.p_mulc e_v784 rfl) rfl rfl e_v94 (L2.p_max (L2.p_ult _ _) rfl) (L2.p_mul e_v784 e_v785) e_v786 e_v787
  have f1734 := L2.K16_a_cos (True ∧ v777 = 1) (sv v873) (sv v874) (sv v33) (sv v887) (sv v888) (sv v889) (sv v94) (sv v891) (sv v893) (sv v894) (sv v895) e_v33 (L2.p_mulc e_v886 e_v887) e_v888 e_v889 e_v94 (L2.p_max e_v890 (L2.p_sel e_v891)) (L2.p_mul e_v892 e_v893) e_v894 e_v895
  have f1748 := L2.K16_a_cos (True ∧ v777 = 1) (sv v877) (sv v878) (sv v33) (sv v897) (sv v898) (sv v899) (sv v94) (sv v901) (sv v903) (sv v904) (sv v905) e_v33 (L2.p_mulc e_v896 e_v897) e_v898 e_v899 e_v94 (L2.p_max e_v900 (L2.p_sel e_v901)) (L2.p_mul e_v902 e_v903) e_v904 e_v905
  let u927 : ℕ := if v910 = 1 ∧ v917 = 1 then 1 else 0
  let u928 : ℕ := if v916 = 1 ∨ u927 = 1 then 1 else 0
  let u929 : ℤ := if u928 = 1 then (sv v891) else (sv v895)
  let u930 : ℕ := if v911 = 1 ∧ v916 = 1 then 1 else 0
  let u931 : ℕ := if v910 = 1 ∨ u930 = 1 then 1 else 0
  let u932 : ℤ := if u931 = 1 then (sv v901) else (sv v905)
  let u935 : ℤ := u929 * u932
  let u936 : ℤ := -((-u935) / 2 ^ 28)
  have f1762 := L2.K6_imul (True ∧ v777 = 1) (sv v891) (sv v895) (sv v901) (sv v905) (sv v9) v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 v918 v919 v921 v922 (sv v923) v924 v925 (sv v926) u927 u928 u929 u930 u931 u932 (sv v934) u936 e_v9 e_v906 e_v907 e_v908 e_v909 (L2.p_and_comm e_v910) e_v911 e_v912 e_v913 e_v914 e_v915 (L2.p_and_comm e_v916) e_v917 e_v918 e_v919 (L2.X1_step True v777 v822 v919 v920 e_v822 e_v920 (L2.X1_top _ k_v920)) e_v921 e_v922 (L2.p_sel e_v923) e_v924 e_v925 (L2.p_sel e_v926) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul (L2.p_mul_comm e_v933) e_v934) (L2.p_mulc rfl rfl)
  let u937 : ℤ := u885 - u936
  have f1797 := L2.K4_isub u885 (sv v787) (sv v934) u936 u937 (sv v938) rfl e_v938
  have f1801 := L2.K17_s_end (sv v873) (sv v892) (sv v939) (sv v940) (sv v941) (sv v942) (sv v944) (sv v945) (sv v33) (sv v947) (sv v948) (sv v950) e_v892 e_v939 e_v940 (L2.p_sqrt e_v941) (L2.p_addc (1) (L2.p_add_comm e_v942) e_v104) (L2.p_mul (L2.p_mul_comm e_v943) e_v944) e_v945 e_v33 (L2.p_mulc (L2.p_mul_comm e_v946) e_v947) e_v948 (L2.p_min e_v949 (L2.p_sel e_v950))
  have f1819 := L2.K17_s_end (sv v874) (sv v886) (sv v939) (sv v951) (sv v952) (sv v953) (sv v955) (sv v956) (sv v33) (sv v958) (sv v959) (sv v961) e_v886 e_v939 e_v951 (L2.p_sqrt e_v952) (L2.p_addc (1) (L2.p_add_comm e_v953) e_v104) (L2.p_mul (L2.p_mul_comm e_v954) e_v955) e_v956 e_v33 (L2.p_mulc (L2.p_mul_comm e_v957) e_v958) e_v959 (L2.p_min e_v960 (L2.p_sel e_v961))
  have f1800 := L2.K18_a_sin (True ∧ v777 = 1) (sv v873) (sv v874) (sv v945) (sv v950) (sv v956) (sv v961) (sv v963) (sv v965) (sv v966) (sv v892) (sv v886) v968 v970 v971 (sv v33) (sv v972) f1801 f1819 (L2.p_min e_v962 (L2.p_sel e_v963)) (L2.p_max e_v964 (L2.p_sel e_v965)) e_v966 e_v892 e_v886 (L2.p_le e_v967 e_v968) (L2.p_le e_v969 e_v970) e_v971 e_v33 (L2.p_sel e_v972)
  have f1856 := L2.K17_s_end (sv v877) (sv v902) (sv v939) (sv v973) (sv v974) (sv v975) (sv v977) (sv v978) (sv v33) (sv v980) (sv v981) (sv v983) e_v902 e_v939 e_v973 (L2.p_sqrt e_v974) (L2.p_addc (1) (L2.p_add_comm e_v975) e_v104) (L2.p_mul (L2.p_mul_comm e_v976) e_v977) e_v978 e_v33 (L2.p_mulc (L2.p_mul_comm e_v979) e_v980) e_v981 (L2.p_min e_v982 (L2.p_sel e_v983))
  have f1874 := L2.K17_s_end (sv v878) (sv v896) (sv v939) (sv v984) (sv v985) (sv v986) (sv v988) (sv v989) (sv v33) (sv v991) (sv v992) (sv v994) e_v896 e_v939 e_v984 (L2.p_sqrt e_v985) (L2.p_addc (1) (L2.p_add_comm e_v986) e_v104) (L2.p_mul (L2.p_mul_comm e_v987) e_v988) e_v989 e_v33 (L2.p_mulc (L2.p_mul_comm e_v990) e_v991) e_v992 (L2.p_min e_v993 (L2.p_sel e_v994))
  have f1855 := L2.K18_a_sin (True ∧ v777 = 1) (sv v877) (sv v878) (sv v978) (sv v983) (sv v989) (sv v994) (sv v996) (sv v998) (sv v966) (sv v902) (sv v896) v1000 v1002 v1003 (sv v33) (sv v1004) f1856 f1874 (L2.p_min e_v995 (L2.p_sel e_v996)) (L2.p_max e_v997 (L2.p_sel e_v998)) e_v966 e_v902 e_v896 (L2.p_le e_v999 e_v1000) (L2.p_le e_v1001 e_v1002) e_v1003 e_v33 (L2.p_sel e_v1004)
  have f1910 := L2.K6_imul (True ∧ v777 = 1) (sv v963) (sv v972) (sv v996) (sv v1004) (sv v9) v1005 v1006 v1007 v1008 v1009 v1010 v1011 v1012 v1013 v1014 v1015 v1016 v1017 v1018 v1020 v1021 (sv v1022) v1023 v1024 (sv v1025) v1026 v1027 (sv v1028) v1029 v1030 (sv v1031) (sv v1033) (sv v1035) e_v9 e_v1005 e_v1006 e_v1007 e_v1008 (L2.p_and_comm e_v1009) e_v1010 e_v1011 e_v1012 e_v1013 e_v1014 (L2.p_and_comm e_v1015) e_v1016 e_v1017 e_v1018 (L2.X1_step True v777 v822 v1018 v1019 e_v822 e_v1019 (L2.X1_top _ k_v1019)) e_v1020 e_v1021 (L2.p_sel e_v1022) e_v1023 e_v1024 (L2.p_sel e_v1025) e_v1026 e_v1027 (L2.p_sel e_v1028) e_v1029 e_v1030 (L2.p_sel e_v1031) (L2.p_mul (L2.p_mul_comm e_v1032) e_v1033) (L2.p_mulc (L2.p_mul_comm e_v1034) e_v1035)
  let u1037 : ℕ := if v1036 = 1 then 0 else 1
  let u1038 : ℕ := if u937 < (sv v9) then 1 else 0
  let u1039 : ℤ := if u1038 = 1 then (sv v1033) else (sv v1035)
  have f1945 := L2.K11_qdiv u937 (sv v938) (sv v1033) (sv v1035) v1036 u1037 (sv v9) u1038 u1039 v1040 (sv v1041) (L2.p_clt (0) e_v9 e_v1036) (L2.p_unot _) e_v9 (L2.p_ult _ _) rfl e_v1040 (L2.p_sel e_v1041)
  have f1719 := L2.K23_hn true true true (True ∧ v777 = 1) (sv v763) (sv v763) (sv v873) (sv v874) (sv v877) (sv v878) u885 (sv v787) (sv v891) (sv v895) (sv v901) (sv v905) (sv v934) u936 u937 (sv v938) (sv v963) (sv v972) (sv v996) (sv v1004) (sv v1033) (sv v1035) u1039 (sv v1041) u1037 f1720 f1734 f1748 f1762 f1797 f1800 f1855 f1910 f1945
  let u1045 : ℕ := if (sv v938) < (sv v1041) then 1 else 0
  let u1046 : ℕ := if u1045 = 1 then 0 else 1
  let u1047 : ℕ := if u1037 = 1 ∨ u1046 = 1 then 1 else 0
  let u1048 : ℤ := if u1047 = 1 then (sv v33) else (sv v938)
  let u1049 : ℤ := if u1047 = 1 then (sv v33) else (sv v1041)
  let u1050 : ℤ := (sv v778) / 2 ^ 28
  let u1051 : ℤ := u1050 + u1050
  let u1052 : ℤ := (sv v33) - u1051
  have f1968 := L2.K16_a_cos (True ∧ v777 = 1) (sv v765) (sv v765) (sv v33) (sv v779) (sv v780) (sv v781) (sv v94) (sv v783) u1050 u1051 u1052 e_v33 (L2.p_mulc e_v778 e_v779) e_v780 e_v781 e_v94 (L2.p_max e_v782 (L2.p_sel e_v783)) (L2.p_mul e_v778 rfl) rfl rfl
  have f1982 := L2.K16_a_cos (True ∧ v777 = 1) (sv v875) (sv v876) (sv v33) (sv v1054) (sv v1055) (sv v1056) (sv v94) (sv v1058) (sv v1060) (sv v1061) (sv v1062) e_v33 (L2.p_mulc e_v1053 e_v1054) e_v1055 e_v1056 e_v94 (L2.p_max e_v1057 (L2.p_sel e_v1058)) (L2.p_mul e_v1059 e_v1060) e_v1061 e_v1062
  have f1996 := L2.K16_a_cos (True ∧ v777 = 1) (sv v879) (sv v880) (sv v33) (sv v1064) (sv v1065) (sv v1066) (sv v94) (sv v1068) (sv v1070) (sv v1071) (sv v1072) e_v33 (L2.p_mulc e_v1063 e_v1064) e_v1065 e_v1066 e_v94 (L2.p_max e_v1067 (L2.p_sel e_v1068)) (L2.p_mul e_v1069 e_v1070) e_v1071 e_v1072
  let u1074 : ℕ := if v1073 = 1 then 0 else 1
  let u1080 : ℕ := if v1079 = 1 then 0 else 1
  let u1088 : ℕ := if u1074 = 1 ∧ v1084 = 1 then 1 else 0
  let u1089 : ℕ := if v1083 = 1 ∨ u1088 = 1 then 1 else 0
  let u1090 : ℤ := if u1089 = 1 then (sv v1062) else (sv v1058)
  let u1091 : ℕ := if v1078 = 1 ∧ u1080 = 1 then 1 else 0
  let u1092 : ℕ := if v1077 = 1 ∨ u1091 = 1 then 1 else 0
  let u1093 : ℤ := if u1092 = 1 then (sv v1072) else (sv v1068)
  let u1100 : ℤ := u1090 * u1093
  let u1101 : ℤ := u1100 / 2 ^ 28
  have f2010 := L2.K6_imul (True ∧ v777 = 1) (sv v1058) (sv v1062) (sv v1068) (sv v1072) (sv v9) v1073 u1074 v1075 v1076 v1077 v1078 v1079 u1080 v1081 v1082 v1083 v1084 v1085 v1086 u1088 u1089 u1090 u1091 u1092 u1093 v1094 v1095 (sv v1096) v1097 v1098 (sv v1099) u1101 (sv v1103) e_v9 e_v1073 (L2.p_unot _) e_v1075 e_v1076 (L2.p_and_comm e_v1077) e_v1078 e_v1079 (L2.p_unot _) e_v1081 e_v1082 (L2.p_and_comm e_v1083) e_v1084 e_v1085 e_v1086 (L2.X1_step True v777 v822 v1086 v1087 e_v822 e_v1087 (L2.X1_top _ k_v1087)) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl e_v1094 e_v1095 (L2.p_sel e_v1096) e_v1097 e_v1098 (L2.p_sel e_v1099) (L2.p_mul rfl rfl) (L2.p_mulc (L2.p_mul_comm e_v1102) e_v1103)
  let u1105 : ℤ := u1052 - u1101
  have f2045 := L2.K4_isub (sv v783) u1052 u1101 (sv v1103) (sv v1104) u1105 e_v1104 rfl
  have f2049 := L2.K17_s_end (sv v875) (sv v1059) (sv v939) (sv v1106) (sv v1107) (sv v1108) (sv v1110) (sv v1111) (sv v33) (sv v1113) (sv v1114) (sv v1116) e_v1059 e_v939 e_v1106 (L2.p_sqrt e_v1107) (L2.p_addc (1) (L2.p_add_comm e_v1108) e_v104) (L2.p_mul (L2.p_mul_comm e_v1109) e_v1110) e_v1111 e_v33 (L2.p_mulc (L2.p_mul_comm e_v1112) e_v1113) e_v1114 (L2.p_min e_v1115 (L2.p_sel e_v1116))
  have f2067 := L2.K17_s_end (sv v876) (sv v1053) (sv v939) (sv v1117) (sv v1118) (sv v1119) (sv v1121) (sv v1122) (sv v33) (sv v1124) (sv v1125) (sv v1127) e_v1053 e_v939 e_v1117 (L2.p_sqrt e_v1118) (L2.p_addc (1) (L2.p_add_comm e_v1119) e_v104) (L2.p_mul (L2.p_mul_comm e_v1120) e_v1121) e_v1122 e_v33 (L2.p_mulc (L2.p_mul_comm e_v1123) e_v1124) e_v1125 (L2.p_min e_v1126 (L2.p_sel e_v1127))
  have f2048 := L2.K18_a_sin (True ∧ v777 = 1) (sv v875) (sv v876) (sv v1111) (sv v1116) (sv v1122) (sv v1127) (sv v1129) (sv v1131) (sv v966) (sv v1059) (sv v1053) v1133 v1135 v1136 (sv v33) (sv v1137) f2049 f2067 (L2.p_min e_v1128 (L2.p_sel e_v1129)) (L2.p_max e_v1130 (L2.p_sel e_v1131)) e_v966 e_v1059 e_v1053 (L2.p_le e_v1132 e_v1133) (L2.p_le e_v1134 e_v1135) e_v1136 e_v33 (L2.p_sel e_v1137)
  have f2104 := L2.K17_s_end (sv v879) (sv v1069) (sv v939) (sv v1138) (sv v1139) (sv v1140) (sv v1142) (sv v1143) (sv v33) (sv v1145) (sv v1146) (sv v1148) e_v1069 e_v939 e_v1138 (L2.p_sqrt e_v1139) (L2.p_addc (1) (L2.p_add_comm e_v1140) e_v104) (L2.p_mul (L2.p_mul_comm e_v1141) e_v1142) e_v1143 e_v33 (L2.p_mulc (L2.p_mul_comm e_v1144) e_v1145) e_v1146 (L2.p_min e_v1147 (L2.p_sel e_v1148))
  have f2122 := L2.K17_s_end (sv v880) (sv v1063) (sv v939) (sv v1149) (sv v1150) (sv v1151) (sv v1153) (sv v1154) (sv v33) (sv v1156) (sv v1157) (sv v1159) e_v1063 e_v939 e_v1149 (L2.p_sqrt e_v1150) (L2.p_addc (1) (L2.p_add_comm e_v1151) e_v104) (L2.p_mul (L2.p_mul_comm e_v1152) e_v1153) e_v1154 e_v33 (L2.p_mulc (L2.p_mul_comm e_v1155) e_v1156) e_v1157 (L2.p_min e_v1158 (L2.p_sel e_v1159))
  have f2103 := L2.K18_a_sin (True ∧ v777 = 1) (sv v879) (sv v880) (sv v1143) (sv v1148) (sv v1154) (sv v1159) (sv v1161) (sv v1163) (sv v966) (sv v1069) (sv v1063) v1165 v1167 v1168 (sv v33) (sv v1169) f2104 f2122 (L2.p_min e_v1160 (L2.p_sel e_v1161)) (L2.p_max e_v1162 (L2.p_sel e_v1163)) e_v966 e_v1069 e_v1063 (L2.p_le e_v1164 e_v1165) (L2.p_le e_v1166 e_v1167) e_v1168 e_v33 (L2.p_sel e_v1169)
  have f2158 := L2.K6_imul (True ∧ v777 = 1) (sv v1129) (sv v1137) (sv v1161) (sv v1169) (sv v9) v1170 v1171 v1172 v1173 v1174 v1175 v1176 v1177 v1178 v1179 v1180 v1181 v1182 v1183 v1185 v1186 (sv v1187) v1188 v1189 (sv v1190) v1191 v1192 (sv v1193) v1194 v1195 (sv v1196) (sv v1198) (sv v1200) e_v9 e_v1170 e_v1171 e_v1172 e_v1173 (L2.p_and_comm e_v1174) e_v1175 e_v1176 e_v1177 e_v1178 e_v1179 (L2.p_and_comm e_v1180) e_v1181 e_v1182 e_v1183 (L2.X1_step True v777 v822 v1183 v1184 e_v822 e_v1184 (L2.X1_top _ k_v1184)) e_v1185 e_v1186 (L2.p_sel e_v1187) e_v1188 e_v1189 (L2.p_sel e_v1190) e_v1191 e_v1192 (L2.p_sel e_v1193) e_v1194 e_v1195 (L2.p_sel e_v1196) (L2.p_mul (L2.p_mul_comm e_v1197) e_v1198) (L2.p_mulc (L2.p_mul_comm e_v1199) e_v1200)
  let u1205 : ℕ := if u1105 < (sv v9) then 1 else 0
  let u1206 : ℤ := if u1205 = 1 then (sv v1200) else (sv v1198)
  have f2193 := L2.K11_qdiv (sv v1104) u1105 (sv v1198) (sv v1200) v1201 v1202 (sv v9) v1203 (sv v1204) u1205 u1206 (L2.p_clt (0) e_v9 e_v1201) e_v1202 e_v9 e_v1203 (L2.p_sel e_v1204) (L2.p_ult _ _) rfl
  have f1967 := L2.K23_hn true true true (True ∧ v777 = 1) (sv v765) (sv v765) (sv v875) (sv v876) (sv v879) (sv v880) (sv v783) u1052 (sv v1058) (sv v1062) (sv v1068) (sv v1072) u1101 (sv v1103) (sv v1104) u1105 (sv v1129) (sv v1137) (sv v1161) (sv v1169) (sv v1198) (sv v1200) (sv v1204) u1206 v1202 f1968 f1982 f1996 f2010 f2045 f2048 f2103 f2158 f2193
  let u1216 : ℕ := if v1215 = 1 then 0 else 1
  let u1217 : ℤ := 0
  let u1218 : ℕ := if (sv v9) < u1217 then 1 else 0
  let u1219 : ℕ := if u1218 = 1 then 0 else 1
  let u1220 : ℤ := L2.cosI u1217
  let u1221 : ℤ := (sv v28) + u1220
  let u1222 : ℕ := if u1221 < (sv v94) then 1 else 0
  let u1223 : ℤ := if u1222 = 1 then (sv v94) else u1221
  have f2222 := L2.K3_cos_lo u1217 u1220 u1221 (sv v94) u1223 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v28) e_v94 (L2.p_max (L2.p_ult _ _) rfl)
  let u1224 : ℤ := u1048 * 2 ^ 28
  let u1225 : ℤ := u1049 * u1223
  let u1226 : ℕ := if u1225 < u1224 then 1 else 0
  let u1227 : ℕ := if u1226 = 1 then 0 else 1
  let u1228 : ℕ := if (sv v14) < u1217 then 1 else 0
  let u1229 : ℕ := if u1228 = 1 then 0 else 1
  let u1230 : ℕ := if u1227 = 1 ∧ u1229 = 1 then 1 else 0
  let u1231 : ℕ := if u1219 = 1 ∨ u1230 = 1 then 1 else 0
  let u1232 : ℤ := if u1231 = 1 then u1217 else (sv v9)
  have f2217 := L2.K13_acos_lo u1048 u1049 u1217 (sv v9) u1218 u1219 u1223 u1224 u1225 u1227 (sv v14) u1229 u1230 u1231 u1232 (le_refl (0 : ℤ)) e_v9 (L2.p_ult _ _) (L2.p_unot _) f2222 rfl (L2.p_mul_comm rfl) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) e_v14 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl
  have f2249 := L2.K3_cos_hi (sv v1233) (sv t1233.2) (sv v1237) (sv v33) (sv v1239) (L2.p_cos e_t1233_2) (L2.p_addc (4) (L2.p_add_comm e_v1237) e_v31) e_v33 (L2.p_min e_v1238 (L2.p_sel e_v1239))
  have f2243 := L2.K13_acos_hi (sv v1213) (sv v1214) (sv v1233) (sv v20) v1235 (sv v1239) (sv v1240) (sv v1241) v1243 v1244 (sv v1245) (L2.p_hint e_v1233) e_v20 (L2.p_le e_v1234 e_v1235) f2249 e_v1240 e_v1241 (L2.p_le e_v1242 e_v1243) e_v1244 (L2.p_sel e_v1245)
  let u1246 : ℤ := if v777 = 1 then u1232 else (sv v9)
  let u1249 : ℤ := if v1044 = 1 then (sv v14) else (sv v9)
  have f1716 := L2.K24_tri_tail_x true true true True (sv v763) (sv v765) v777 (sv v873) (sv v874) (sv v877) (sv v878) (sv v875) (sv v876) (sv v879) (sv v880) (sv v33) (sv v94) u937 u1039 (sv v938) (sv v1041) u1037 v1036 (sv v1042) v1043 v1044 u1046 u1047 u1048 u1049 (sv v1104) (sv v1204) u1105 u1206 v1202 v1201 v1207 v1208 (sv v1209) v1211 v1212 (sv v1213) (sv v1214) v1215 u1216 u1232 (sv v1245) (sv v9) (sv v20) (sv v14) u1246 (sv v1247) v1248 u1249 (sv v1250) e_v33 e_v94 f1719 (L2.p_not_not (L2.p_unot _)) (L2.p_neg e_v9 e_v1042) e_v1043 e_v1044 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_uor _ _) rfl rfl f1967 (L2.p_not_not e_v1202) e_v1207 e_v1208 (L2.p_neg e_v9 e_v1209) (L2.p_le e_v1210 e_v1211) e_v1212 (L2.p_sel e_v1213) (L2.p_sel e_v1214) e_v1215 (L2.p_unot _) f2217 f2243 e_v9 e_v20 e_v14 rfl (L2.p_sel e_v1247) e_v1248 rfl (L2.p_sel e_v1250)
  have f1551 := L2.K21_tri_angle_st true true true True (sv v763) (sv v765) (sv v88) (sv v90) (sv v437) (sv v439) v769 v772 v775 v776 v777 (sv v783) (sv v787) (sv v793) (sv v797) (sv v803) (sv v807) (sv v837) (sv v839) (sv v840) (sv v841) (sv v864) (sv v866) (sv v867) (sv v868) v869 v870 v871 v872 (sv v873) (sv v874) (sv v875) (sv v876) (sv v877) (sv v878) (sv v879) (sv v880) u1246 (sv v1247) v1248 u1249 (sv v1250) f1552 f1560 f1568 e_v776 (L2.p_and_comm e_v777) f1578 f1592 f1606 f1620 f1655 f1658 f1693 (L2.p_clt (0) e_v9 e_v869) (L2.p_ltc (0) e_v9 e_v870) (L2.p_clt (0) e_v9 e_v871) (L2.p_ltc (0) e_v9 e_v872) (L2.p_sel e_v873) (L2.p_sel e_v874) (L2.p_sel e_v875) (L2.p_sel e_v876) (L2.p_sel e_v877) (L2.p_sel e_v878) (L2.p_sel e_v879) (L2.p_sel e_v880) f1716
  let u1251 : ℤ := if v1248 = 1 then u1249 else u1246
  have f1550 := L2.K25_tri_angle_c true true true True (sv v763) (sv v765) (sv v88) (sv v90) (sv v437) (sv v439) u1246 (sv v1247) v1248 u1249 (sv v1250) u1251 (sv v1252) f1551 rfl (L2.p_sel e_v1252)
  let u1253 : ℤ := u254 + u1251
  have f2275 := L2.K4_iadd u254 (sv v396) u1251 (sv v1252) u1253 (sv v1254) rfl e_v1254
  let u1255 : ℤ := u579 + u1253
  have f2278 := L2.K4_iadd u1253 (sv v1254) u579 (sv v721) u1255 (sv v1256) (L2.p_add_comm rfl) (L2.p_add_comm e_v1256)
  have f20 := Tammes15.D3Trig.KH_hex_eval True (sv v2) (sv v3) (sv v4) (sv v5) u17 (sv v7) (sv v0) (sv v1) (sv v88) (sv v90) u254 (sv v396) (sv v437) (sv v439) u579 (sv v721) (sv v763) (sv v765) u1251 (sv v1252) u1253 (sv v1254) u1255 (sv v1256) f21 f136 f726 f841 f1431 f1550 f2275 f2278
  let u1257 : ℕ := if u1255 < (sv v6) then 1 else 0
  let u1258 : ℕ := if u1257 = 1 then 0 else 1
  exact Tammes15.D3Trig.THNH F0 F1 F2 F3 hD (sv v0) (sv v1) (sv v2) (sv v3) (sv v4) (sv v5) (sv v6) (sv v7) (1 : ℕ) (sv v9) u17 (sv v7) u1255 (sv v1256) u1258 v1260 v1260 e_v0 e_v1 e_v2 e_v3 e_v4 e_v5 e_v6 e_v7 (of_decide_eq_true rfl) e_v9 f2 f20 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le e_v1259 e_v1260) (L2.p_sel_t _ _) (L2.X1_top _ k_v1260)

end Tammes15.D3Trig
