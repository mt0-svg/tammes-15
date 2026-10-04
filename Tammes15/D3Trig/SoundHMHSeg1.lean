import Tammes15.D3Trig.Prog.HMH
import Tammes15.D3Prog.Sem

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progHMH_seg1 (F0 F1 F2 F3 H0 H1 H2 H3 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (v88 : ℕ) (v90 : ℕ) (v437 : ℕ) (v439 : ℕ) (v763 : ℕ) (v765 : ℕ) (v777 : ℕ) (v783 : ℕ) (v787 : ℕ) (v793 : ℕ) (v797 : ℕ) (v803 : ℕ) (v807 : ℕ) (v809 : ℕ) (v812 : ℕ) (v813 : ℕ) (v815 : ℕ) (v818 : ℕ) (v819 : ℕ) (v822 : ℕ) (v832 : ℕ) (v835 : ℕ) (v837 : ℕ) (h_v88 : R 1 0 4611686018427387899 4611686018695823374 v88 v88) (h_v90 : R 1 0 4611686018427387900 4611686018695823375 v90 v90) (h_v437 : R 1 0 4611686018427387899 4611686018695823374 v437 v437) (h_v439 : R 1 0 4611686018427387900 4611686018695823375 v439 v439) (h_v763 : R 1 0 4611686018427387899 4611686018695823374 v763 v763) (h_v765 : R 1 0 4611686018427387900 4611686018695823375 v765 v765) (h_v777 : R 1 0 0 1 v777 v777) (h_v783 : R 1 0 4611686018158952386 4611686018695823360 v783 v783) (h_v787 : R 1 0 4611686018158952392 4611686018695823360 v787 v787) (h_v793 : R 1 0 4611686018158952386 4611686018695823360 v793 v793) (h_v797 : R 1 0 4611686018158952392 4611686018695823360 v797 v797) (h_v803 : R 1 0 4611686018158952386 4611686018695823360 v803 v803) (h_v807 : R 1 0 4611686018158952392 4611686018695823360 v807 v807) (h_v809 : R 1 0 0 1 v809 v809) (h_v812 : R 1 0 0 1 v812 v812) (h_v813 : R 1 0 0 1 v813 v813) (h_v815 : R 1 0 0 1 v815 v815) (h_v818 : R 1 0 0 1 v818 v818) (h_v819 : R 1 0 0 1 v819 v819) (h_v822 : R 1 0 0 1 v822 v822) (h_v832 : R 1 0 4611686018158952386 4611686018695823360 v832 v832) (h_v835 : R 1 0 4611686018158952386 4611686018695823360 v835 v835) (h_v837 : R 1 0 4611686018158952386 4611686018695823484 v837 v837) :
    let OFFr := Nat.mul 1 4611686018427387904
    let v9 := Nat.mul 1 4611686018427387904
    let v14 := Nat.mul 1 4611686019270702760
    let v20 := Nat.mul 1 4611686019270702761
    let v28 := Nat.mul 1 4611686018427387900
    let v31 := Nat.mul 1 4611686018427387908
    let v33 := Nat.mul 1 4611686018695823360
    let v94 := Nat.mul 1 4611686018158952448
    let v104 := Nat.mul 1 4611686018427387905
    let v838 := smx 30 1 v835 v832
    let v839 := srdC 1 v838
    let v840 := Nat.sub (Nat.add v793 OFFr) v839
    let v841 := Nat.sub (Nat.add v797 OFFr) v837
    let v842 := plt 1 v793 v9
    let v843 := Nat.sub 1 v842
    let v844 := plt 1 v9 v797
    let v845 := Nat.sub 1 v844
    let v846 := Nat.land v842 v845
    let v847 := Nat.land v842 v844
    let v848 := Nat.land v813 v847
    let v849 := Nat.sub 1 v848
    let v850 := Nat.lor v822 v849
    let v851 := Nat.land v809 v847
    let v852 := Nat.lor v846 v851
    let v853 := psel (pmask v852) v787 v783
    let v854 := Nat.land v813 v843
    let v855 := Nat.lor v812 v854
    let v856 := psel (pmask v855) v797 v793
    let v857 := Nat.land v812 v847
    let v858 := Nat.lor v846 v857
    let v859 := psel (pmask v858) v783 v787
    let v860 := Nat.land v813 v846
    let v861 := Nat.lor v812 v860
    let v862 := psel (pmask v861) v793 v797
    let v863 := smx 30 1 v856 v853
    let v864 := srdF 1 v863
    let v865 := smx 30 1 v862 v859
    let v866 := srdC 1 v865
    let v867 := Nat.sub (Nat.add v803 OFFr) v866
    let v868 := Nat.sub (Nat.add v807 OFFr) v864
    let v869 := plt 1 v9 v840
    let v870 := plt 1 v841 v9
    let v871 := plt 1 v9 v867
    let v872 := plt 1 v868 v9
    let v873 := psel (pmask v869) v90 v88
    let v874 := psel (pmask v870) v88 v90
    let v875 := psel (pmask v870) v90 v88
    let v876 := psel (pmask v869) v88 v90
    let v877 := psel (pmask v871) v765 v763
    let v878 := psel (pmask v872) v763 v765
    let v879 := psel (pmask v872) v765 v763
    let v880 := psel (pmask v871) v763 v765
    let v886 := smx 29 1 v874 v874
    let v887 := srdC 1 v886
    let v888 := Nat.sub (Nat.add v887 v887) OFFr
    let v889 := Nat.sub (Nat.add v33 OFFr) v888
    let v890 := plt 1 v889 v94
    let v891 := psel (pmask v890) v94 v889
    let v892 := smx 29 1 v873 v873
    let v893 := srdF 1 v892
    let v894 := Nat.sub (Nat.add v893 v893) OFFr
    let v895 := Nat.sub (Nat.add v33 OFFr) v894
    let v896 := smx 29 1 v878 v878
    let v897 := srdC 1 v896
    let v898 := Nat.sub (Nat.add v897 v897) OFFr
    let v899 := Nat.sub (Nat.add v33 OFFr) v898
    let v900 := plt 1 v899 v94
    let v901 := psel (pmask v900) v94 v899
    let v902 := smx 29 1 v877 v877
    let v903 := srdF 1 v902
    let v904 := Nat.sub (Nat.add v903 v903) OFFr
    let v905 := Nat.sub (Nat.add v33 OFFr) v904
    let v906 := plt 1 v891 v9
    let v907 := Nat.sub 1 v906
    let v908 := plt 1 v9 v895
    let v909 := Nat.sub 1 v908
    let v910 := Nat.land v906 v909
    let v911 := Nat.land v906 v908
    let v912 := plt 1 v901 v9
    let v913 := Nat.sub 1 v912
    let v914 := plt 1 v9 v905
    let v915 := Nat.sub 1 v914
    let v916 := Nat.land v912 v915
    let v917 := Nat.land v912 v914
    let v918 := Nat.land v911 v917
    let v919 := Nat.sub 1 v918
    let v920 := Nat.lor v822 v919
    let v921 := Nat.land v907 v917
    let v922 := Nat.lor v916 v921
    let v923 := psel (pmask v922) v895 v891
    let v924 := Nat.land v911 v913
    let v925 := Nat.lor v910 v924
    let v926 := psel (pmask v925) v905 v901
    let v933 := smx 30 1 v926 v923
    let v934 := srdF 1 v933
    let v938 := Nat.sub (Nat.add v787 OFFr) v934
    let v939 := Nat.mul 1 4683743612465315840
    let v940 := Nat.sub (Nat.add v939 OFFr) v892
    let v941 := psqrt 1 v940
    let v942 := Nat.sub (Nat.add v104 v941) OFFr
    let v943 := smx 29 1 v941 v873
    let v944 := srdF 1 v943
    let v945 := Nat.sub (Nat.add v944 v944) OFFr
    let v946 := smx 29 1 v942 v873
    let v947 := srdC 1 v946
    let v948 := Nat.sub (Nat.add v947 v947) OFFr
    let v949 := plt 1 v948 v33
    let v950 := psel (pmask v949) v948 v33
    let v951 := Nat.sub (Nat.add v939 OFFr) v886
    let v952 := psqrt 1 v951
    let v953 := Nat.sub (Nat.add v104 v952) OFFr
    let v954 := smx 29 1 v952 v874
    let v955 := srdF 1 v954
    let v956 := Nat.sub (Nat.add v955 v955) OFFr
    let v957 := smx 29 1 v953 v874
    let v958 := srdC 1 v957
    let v959 := Nat.sub (Nat.add v958 v958) OFFr
    let v960 := plt 1 v959 v33
    let v961 := psel (pmask v960) v959 v33
    let v962 := plt 1 v945 v956
    let v963 := psel (pmask v962) v945 v956
    let v964 := plt 1 v950 v961
    let v965 := psel (pmask v964) v961 v950
    let v966 := Nat.mul 1 4647714815446351872
    let v967 := plt 1 v966 v892
    let v968 := Nat.sub 1 v967
    let v969 := plt 1 v886 v966
    let v970 := Nat.sub 1 v969
    let v971 := Nat.land v968 v970
    let v972 := psel (pmask v971) v33 v965
    let v973 := Nat.sub (Nat.add v939 OFFr) v902
    let v974 := psqrt 1 v973
    let v975 := Nat.sub (Nat.add v104 v974) OFFr
    let v976 := smx 29 1 v974 v877
    let v977 := srdF 1 v976
    let v978 := Nat.sub (Nat.add v977 v977) OFFr
    let v979 := smx 29 1 v975 v877
    let v980 := srdC 1 v979
    let v981 := Nat.sub (Nat.add v980 v980) OFFr
    let v982 := plt 1 v981 v33
    let v983 := psel (pmask v982) v981 v33
    let v984 := Nat.sub (Nat.add v939 OFFr) v896
    let v985 := psqrt 1 v984
    let v986 := Nat.sub (Nat.add v104 v985) OFFr
    let v987 := smx 29 1 v985 v878
    let v988 := srdF 1 v987
    let v989 := Nat.sub (Nat.add v988 v988) OFFr
    let v990 := smx 29 1 v986 v878
    let v991 := srdC 1 v990
    let v992 := Nat.sub (Nat.add v991 v991) OFFr
    let v993 := plt 1 v992 v33
    let v994 := psel (pmask v993) v992 v33
    let v995 := plt 1 v978 v989
    let v996 := psel (pmask v995) v978 v989
    let v997 := plt 1 v983 v994
    let v998 := psel (pmask v997) v994 v983
    let v999 := plt 1 v966 v902
    let v1000 := Nat.sub 1 v999
    let v1001 := plt 1 v896 v966
    let v1002 := Nat.sub 1 v1001
    let v1003 := Nat.land v1000 v1002
    let v1004 := psel (pmask v1003) v33 v998
    let v1005 := plt 1 v963 v9
    let v1006 := Nat.sub 1 v1005
    let v1007 := plt 1 v9 v972
    let v1008 := Nat.sub 1 v1007
    let v1009 := Nat.land v1005 v1008
    let v1010 := Nat.land v1005 v1007
    let v1011 := plt 1 v996 v9
    let v1012 := Nat.sub 1 v1011
    let v1013 := plt 1 v9 v1004
    let v1014 := Nat.sub 1 v1013
    let v1015 := Nat.land v1011 v1014
    let v1016 := Nat.land v1011 v1013
    let v1017 := Nat.land v1010 v1016
    let v1018 := Nat.sub 1 v1017
    let v1019 := Nat.lor v822 v1018
    let v1020 := Nat.land v1006 v1016
    let v1021 := Nat.lor v1015 v1020
    let v1022 := psel (pmask v1021) v972 v963
    let v1023 := Nat.land v1010 v1012
    let v1024 := Nat.lor v1009 v1023
    let v1025 := psel (pmask v1024) v1004 v996
    let v1026 := Nat.land v1009 v1016
    let v1027 := Nat.lor v1015 v1026
    let v1028 := psel (pmask v1027) v963 v972
    let v1029 := Nat.land v1010 v1015
    let v1030 := Nat.lor v1009 v1029
    let v1031 := psel (pmask v1030) v996 v1004
    let v1032 := smx 29 1 v1025 v1022
    let v1033 := srdF 1 v1032
    let v1034 := smx 29 1 v1031 v1028
    let v1035 := srdC 1 v1034
    let v1036 := plt 1 v9 v1033
    let v1037 := Nat.sub 1 v1036
    let v1040 := plt 1 v938 v9
    let v1041 := psel (pmask v1040) v1035 v1033
    let v1042 := Nat.sub (Nat.add v9 OFFr) v1041
    let v1043 := plt 1 v938 v1042
    let v1044 := Nat.land v1036 v1043
    let v1045 := plt 1 v938 v1041
    let v1046 := Nat.sub 1 v1045
    let v1047 := Nat.lor v1037 v1046
    let v1048 := psel (pmask v1047) v33 v938
    let v1049 := psel (pmask v1047) v33 v1041
    let v1053 := smx 29 1 v876 v876
    let v1054 := srdC 1 v1053
    let v1055 := Nat.sub (Nat.add v1054 v1054) OFFr
    let v1056 := Nat.sub (Nat.add v33 OFFr) v1055
    let v1057 := plt 1 v1056 v94
    let v1058 := psel (pmask v1057) v94 v1056
    let v1059 := smx 29 1 v875 v875
    let v1060 := srdF 1 v1059
    let v1061 := Nat.sub (Nat.add v1060 v1060) OFFr
    let v1062 := Nat.sub (Nat.add v33 OFFr) v1061
    let v1063 := smx 29 1 v880 v880
    let v1064 := srdC 1 v1063
    let v1065 := Nat.sub (Nat.add v1064 v1064) OFFr
    let v1066 := Nat.sub (Nat.add v33 OFFr) v1065
    let v1067 := plt 1 v1066 v94
    let v1068 := psel (pmask v1067) v94 v1066
    let v1069 := smx 29 1 v879 v879
    let v1070 := srdF 1 v1069
    let v1071 := Nat.sub (Nat.add v1070 v1070) OFFr
    let v1072 := Nat.sub (Nat.add v33 OFFr) v1071
    let v1073 := plt 1 v1058 v9
    let v1075 := plt 1 v9 v1062
    let v1076 := Nat.sub 1 v1075
    let v1077 := Nat.land v1073 v1076
    let v1078 := Nat.land v1073 v1075
    let v1079 := plt 1 v1068 v9
    let v1081 := plt 1 v9 v1072
    let v1082 := Nat.sub 1 v1081
    let v1083 := Nat.land v1079 v1082
    let v1084 := Nat.land v1079 v1081
    let v1085 := Nat.land v1078 v1084
    let v1086 := Nat.sub 1 v1085
    let v1087 := Nat.lor v822 v1086
    let v1094 := Nat.land v1077 v1084
    let v1095 := Nat.lor v1083 v1094
    let v1096 := psel (pmask v1095) v1058 v1062
    let v1097 := Nat.land v1078 v1083
    let v1098 := Nat.lor v1077 v1097
    let v1099 := psel (pmask v1098) v1068 v1072
    let v1102 := smx 30 1 v1099 v1096
    let v1103 := srdC 1 v1102
    let v1104 := Nat.sub (Nat.add v783 OFFr) v1103
    let v1106 := Nat.sub (Nat.add v939 OFFr) v1059
    let v1107 := psqrt 1 v1106
    let v1108 := Nat.sub (Nat.add v104 v1107) OFFr
    let v1109 := smx 29 1 v1107 v875
    let v1110 := srdF 1 v1109
    let v1111 := Nat.sub (Nat.add v1110 v1110) OFFr
    let v1112 := smx 29 1 v1108 v875
    let v1113 := srdC 1 v1112
    let v1114 := Nat.sub (Nat.add v1113 v1113) OFFr
    let v1115 := plt 1 v1114 v33
    let v1116 := psel (pmask v1115) v1114 v33
    let v1117 := Nat.sub (Nat.add v939 OFFr) v1053
    let v1118 := psqrt 1 v1117
    let v1119 := Nat.sub (Nat.add v104 v1118) OFFr
    let v1120 := smx 29 1 v1118 v876
    let v1121 := srdF 1 v1120
    let v1122 := Nat.sub (Nat.add v1121 v1121) OFFr
    let v1123 := smx 29 1 v1119 v876
    let v1124 := srdC 1 v1123
    let v1125 := Nat.sub (Nat.add v1124 v1124) OFFr
    let v1126 := plt 1 v1125 v33
    let v1127 := psel (pmask v1126) v1125 v33
    let v1128 := plt 1 v1111 v1122
    let v1129 := psel (pmask v1128) v1111 v1122
    let v1130 := plt 1 v1116 v1127
    let v1131 := psel (pmask v1130) v1127 v1116
    let v1132 := plt 1 v966 v1059
    let v1133 := Nat.sub 1 v1132
    let v1134 := plt 1 v1053 v966
    let v1135 := Nat.sub 1 v1134
    let v1136 := Nat.land v1133 v1135
    let v1137 := psel (pmask v1136) v33 v1131
    let v1138 := Nat.sub (Nat.add v939 OFFr) v1069
    let v1139 := psqrt 1 v1138
    let v1140 := Nat.sub (Nat.add v104 v1139) OFFr
    let v1141 := smx 29 1 v1139 v879
    let v1142 := srdF 1 v1141
    let v1143 := Nat.sub (Nat.add v1142 v1142) OFFr
    let v1144 := smx 29 1 v1140 v879
    let v1145 := srdC 1 v1144
    let v1146 := Nat.sub (Nat.add v1145 v1145) OFFr
    let v1147 := plt 1 v1146 v33
    let v1148 := psel (pmask v1147) v1146 v33
    let v1149 := Nat.sub (Nat.add v939 OFFr) v1063
    let v1150 := psqrt 1 v1149
    let v1151 := Nat.sub (Nat.add v104 v1150) OFFr
    let v1152 := smx 29 1 v1150 v880
    let v1153 := srdF 1 v1152
    let v1154 := Nat.sub (Nat.add v1153 v1153) OFFr
    let v1155 := smx 29 1 v1151 v880
    let v1156 := srdC 1 v1155
    let v1157 := Nat.sub (Nat.add v1156 v1156) OFFr
    let v1158 := plt 1 v1157 v33
    let v1159 := psel (pmask v1158) v1157 v33
    let v1160 := plt 1 v1143 v1154
    let v1161 := psel (pmask v1160) v1143 v1154
    let v1162 := plt 1 v1148 v1159
    let v1163 := psel (pmask v1162) v1159 v1148
    let v1164 := plt 1 v966 v1069
    let v1165 := Nat.sub 1 v1164
    let v1166 := plt 1 v1063 v966
    let v1167 := Nat.sub 1 v1166
    let v1168 := Nat.land v1165 v1167
    let v1169 := psel (pmask v1168) v33 v1163
    let v1170 := plt 1 v1129 v9
    let v1171 := Nat.sub 1 v1170
    let v1172 := plt 1 v9 v1137
    let v1173 := Nat.sub 1 v1172
    let v1174 := Nat.land v1170 v1173
    let v1175 := Nat.land v1170 v1172
    let v1176 := plt 1 v1161 v9
    let v1177 := Nat.sub 1 v1176
    let v1178 := plt 1 v9 v1169
    let v1179 := Nat.sub 1 v1178
    let v1180 := Nat.land v1176 v1179
    let v1181 := Nat.land v1176 v1178
    let v1182 := Nat.land v1175 v1181
    let v1183 := Nat.sub 1 v1182
    let v1184 := Nat.lor v822 v1183
    let v1185 := Nat.land v1171 v1181
    let v1186 := Nat.lor v1180 v1185
    let v1187 := psel (pmask v1186) v1137 v1129
    let v1188 := Nat.land v1175 v1177
    let v1189 := Nat.lor v1174 v1188
    let v1190 := psel (pmask v1189) v1169 v1161
    let v1191 := Nat.land v1174 v1181
    let v1192 := Nat.lor v1180 v1191
    let v1193 := psel (pmask v1192) v1129 v1137
    let v1194 := Nat.land v1175 v1180
    let v1195 := Nat.lor v1174 v1194
    let v1196 := psel (pmask v1195) v1161 v1169
    let v1197 := smx 29 1 v1190 v1187
    let v1198 := srdF 1 v1197
    let v1199 := smx 29 1 v1196 v1193
    let v1200 := srdC 1 v1199
    let v1201 := plt 1 v9 v1198
    let v1202 := Nat.sub 1 v1201
    let v1203 := plt 1 v1104 v9
    let v1204 := psel (pmask v1203) v1198 v1200
    let v1207 := plt 1 v1204 v1104
    let v1208 := Nat.land v1201 v1207
    let v1209 := Nat.sub (Nat.add v9 OFFr) v1204
    let v1210 := plt 1 v1209 v1104
    let v1211 := Nat.sub 1 v1210
    let v1212 := Nat.lor v1202 v1211
    let v1213 := psel (pmask v1212) v94 v1104
    let v1214 := psel (pmask v1212) v33 v1204
    let v1215 := Nat.lor v1044 v1208
    let v1217 := hxa 1 H1 0
    let v1218 := plt 1 v9 v1217
    let v1219 := Nat.sub 1 v1218
    let t1217 := sc28u 1 v1217
    let v1221 := Nat.sub (Nat.add v28 t1217.2) OFFr
    let v1222 := plt 1 v1221 v94
    let v1223 := psel (pmask v1222) v94 v1221
    let v1224 := sshl 1 v1048
    let v1225 := smx 29 1 v1223 v1049
    let v1226 := plt 1 v1225 v1224
    let v1227 := Nat.sub 1 v1226
    let v1228 := plt 1 v14 v1217
    let v1229 := Nat.sub 1 v1228
    let v1230 := Nat.land v1227 v1229
    let v1231 := Nat.lor v1219 v1230
    let v1232 := psel (pmask v1231) v1217 v9
    let v1233 := hxa 1 H1 32
    let v1234 := plt 1 v1233 v20
    let v1235 := Nat.sub 1 v1234
    let t1233 := sc28u 1 v1233
    let v1237 := Nat.sub (Nat.add v31 t1233.2) OFFr
    let v1238 := plt 1 v1237 v33
    let v1239 := psel (pmask v1238) v1237 v33
    let v1240 := sshl 1 v1213
    let v1241 := smx 29 1 v1239 v1214
    let v1242 := plt 1 v1240 v1241
    let v1243 := Nat.sub 1 v1242
    let v1244 := Nat.lor v1235 v1243
    let v1245 := psel (pmask v1244) v1233 v20
    let v1246 := psel (pmask v777) v1232 v9
    let v1247 := psel (pmask v777) v1245 v20
    let v1248 := Nat.land v777 v1215
    let v1251 := Nat.sub 1 v1248
    let v1252 := Nat.land v819 v847
    let v1253 := Nat.sub 1 v1252
    let v1254 := Nat.lor v822 v1253
    let v1255 := Nat.land v815 v847
    let v1256 := Nat.lor v846 v1255
    let v1257 := psel (pmask v1256) v807 v803
    let v1258 := Nat.land v819 v843
    let v1259 := Nat.lor v818 v1258
    let v1260 := psel (pmask v1259) v797 v793
    let v1261 := Nat.land v818 v847
    let v1262 := Nat.lor v846 v1261
    let v1263 := psel (pmask v1262) v803 v807
    let v1264 := Nat.land v819 v846
    let v1265 := Nat.lor v818 v1264
    let v1266 := psel (pmask v1265) v793 v797
    let v1267 := smx 30 1 v1260 v1257
    let v1268 := srdF 1 v1267
    let v1269 := smx 30 1 v1266 v1263
    let v1270 := srdC 1 v1269
    let v1271 := Nat.sub (Nat.add v783 OFFr) v1270
    let v1272 := Nat.sub (Nat.add v787 OFFr) v1268
    let v1273 := plt 1 v9 v1271
    let v1274 := plt 1 v1272 v9
    let v1275 := psel (pmask v869) v439 v437
    let v1276 := psel (pmask v870) v437 v439
    let v1277 := psel (pmask v870) v439 v437
    let v1278 := psel (pmask v869) v437 v439
    let v1279 := psel (pmask v1273) v765 v763
    let v1280 := psel (pmask v1274) v763 v765
    let v1281 := psel (pmask v1274) v765 v763
    let v1282 := psel (pmask v1273) v763 v765
    let v1288 := smx 29 1 v1276 v1276
    let v1289 := srdC 1 v1288
    let v1290 := Nat.sub (Nat.add v1289 v1289) OFFr
    let v1291 := Nat.sub (Nat.add v33 OFFr) v1290
    let v1292 := plt 1 v1291 v94
    let v1293 := psel (pmask v1292) v94 v1291
    let v1294 := smx 29 1 v1275 v1275
    let v1295 := srdF 1 v1294
    let v1296 := Nat.sub (Nat.add v1295 v1295) OFFr
    let v1297 := Nat.sub (Nat.add v33 OFFr) v1296
    let v1298 := smx 29 1 v1280 v1280
    let v1299 := srdC 1 v1298
    let v1300 := Nat.sub (Nat.add v1299 v1299) OFFr
    let v1301 := Nat.sub (Nat.add v33 OFFr) v1300
    let v1302 := plt 1 v1301 v94
    let v1303 := psel (pmask v1302) v94 v1301
    let v1304 := smx 29 1 v1279 v1279
    let v1305 := srdF 1 v1304
    let v1306 := Nat.sub (Nat.add v1305 v1305) OFFr
    let v1307 := Nat.sub (Nat.add v33 OFFr) v1306
    let v1308 := plt 1 v1293 v9
    let v1309 := Nat.sub 1 v1308
    let v1310 := plt 1 v9 v1297
    let v1311 := Nat.sub 1 v1310
    let v1312 := Nat.land v1308 v1311
    let v1313 := Nat.land v1308 v1310
    let v1314 := plt 1 v1303 v9
    let v1315 := Nat.sub 1 v1314
    let v1316 := plt 1 v9 v1307
    let v1317 := Nat.sub 1 v1316
    let v1318 := Nat.land v1314 v1317
    let v1319 := Nat.land v1314 v1316
    let v1320 := Nat.land v1313 v1319
    let v1321 := Nat.sub 1 v1320
    let v1322 := Nat.lor v822 v1321
    let v1323 := Nat.land v1309 v1319
    let v1324 := Nat.lor v1318 v1323
    let v1325 := psel (pmask v1324) v1297 v1293
    let v1326 := Nat.land v1313 v1315
    let v1327 := Nat.lor v1312 v1326
    let v1328 := psel (pmask v1327) v1307 v1303
    let v1335 := smx 30 1 v1328 v1325
    let v1336 := srdF 1 v1335
    let v1340 := Nat.sub (Nat.add v807 OFFr) v1336
    let v1341 := Nat.sub (Nat.add v939 OFFr) v1294
    let v1342 := psqrt 1 v1341
    let v1343 := Nat.sub (Nat.add v104 v1342) OFFr
    let v1344 := smx 29 1 v1342 v1275
    let v1345 := srdF 1 v1344
    let v1346 := Nat.sub (Nat.add v1345 v1345) OFFr
    let v1347 := smx 29 1 v1343 v1275
    let v1348 := srdC 1 v1347
    let v1349 := Nat.sub (Nat.add v1348 v1348) OFFr
    let v1350 := plt 1 v1349 v33
    let v1351 := psel (pmask v1350) v1349 v33
    let v1352 := Nat.sub (Nat.add v939 OFFr) v1288
    let v1353 := psqrt 1 v1352
    let v1354 := Nat.sub (Nat.add v104 v1353) OFFr
    let v1355 := smx 29 1 v1353 v1276
    let v1356 := srdF 1 v1355
    let v1357 := Nat.sub (Nat.add v1356 v1356) OFFr
    let v1358 := smx 29 1 v1354 v1276
    let v1359 := srdC 1 v1358
    let v1360 := Nat.sub (Nat.add v1359 v1359) OFFr
    let v1361 := plt 1 v1360 v33
    let v1362 := psel (pmask v1361) v1360 v33
    let v1363 := plt 1 v1346 v1357
    let v1364 := psel (pmask v1363) v1346 v1357
    let v1365 := plt 1 v1351 v1362
    let v1366 := psel (pmask v1365) v1362 v1351
    let v1367 := plt 1 v966 v1294
    let v1368 := Nat.sub 1 v1367
    let v1369 := plt 1 v1288 v966
    let v1370 := Nat.sub 1 v1369
    let v1371 := Nat.land v1368 v1370
    let v1372 := psel (pmask v1371) v33 v1366
    let v1373 := Nat.sub (Nat.add v939 OFFr) v1304
    let v1374 := psqrt 1 v1373
    let v1375 := Nat.sub (Nat.add v104 v1374) OFFr
    let v1376 := smx 29 1 v1374 v1279
    let v1377 := srdF 1 v1376
    let v1378 := Nat.sub (Nat.add v1377 v1377) OFFr
    let v1379 := smx 29 1 v1375 v1279
    let v1380 := srdC 1 v1379
    let v1381 := Nat.sub (Nat.add v1380 v1380) OFFr
    let v1382 := plt 1 v1381 v33
    let v1383 := psel (pmask v1382) v1381 v33
    let v1384 := Nat.sub (Nat.add v939 OFFr) v1298
    let v1385 := psqrt 1 v1384
    let v1386 := Nat.sub (Nat.add v104 v1385) OFFr
    ∀ (P : Prop), ((sv v838 = sv v835 * sv v832) → (sv v839 = -((-sv v838) / 2 ^ 28)) → (sv v840 = sv v793 - sv v839) → (sv v841 = sv v797 - sv v837) → ((v842 = 1 ↔ sv v793 < sv v9)) → (R 1 0 0 1 v843 v843) → ((v843 = 1 ↔ ¬v842 = 1)) → ((v844 = 1 ↔ sv v9 < sv v797)) → ((v845 = 1 ↔ ¬v844 = 1)) → (R 1 0 0 1 v846 v846) → ((v846 = 1 ↔ v842 = 1 ∧ v845 = 1)) → (R 1 0 0 1 v847 v847) → ((v847 = 1 ↔ v842 = 1 ∧ v844 = 1)) → ((v848 = 1 ↔ v813 = 1 ∧ v847 = 1)) → ((v849 = 1 ↔ ¬v848 = 1)) → (R 1 0 0 1 v850 v850) → ((v850 = 1 ↔ v822 = 1 ∨ v849 = 1)) → ((v851 = 1 ↔ v809 = 1 ∧ v847 = 1)) → ((v852 = 1 ↔ v846 = 1 ∨ v851 = 1)) → (v853 = if v852 = 1 then v787 else v783) → ((v854 = 1 ↔ v813 = 1 ∧ v843 = 1)) → ((v855 = 1 ↔ v812 = 1 ∨ v854 = 1)) → (v856 = if v855 = 1 then v797 else v793) → ((v857 = 1 ↔ v812 = 1 ∧ v847 = 1)) → ((v858 = 1 ↔ v846 = 1 ∨ v857 = 1)) → (v859 = if v858 = 1 then v783 else v787) → ((v860 = 1 ↔ v813 = 1 ∧ v846 = 1)) → ((v861 = 1 ↔ v812 = 1 ∨ v860 = 1)) → (v862 = if v861 = 1 then v793 else v797) → (sv v863 = sv v856 * sv v853) → (sv v864 = sv v863 / 2 ^ 28) → (sv v865 = sv v862 * sv v859) → (sv v866 = -((-sv v865) / 2 ^ 28)) → (sv v867 = sv v803 - sv v866) → (sv v868 = sv v807 - sv v864) → ((v869 = 1 ↔ sv v9 < sv v840)) → ((v870 = 1 ↔ sv v841 < sv v9)) → ((v871 = 1 ↔ sv v9 < sv v867)) → ((v872 = 1 ↔ sv v868 < sv v9)) → (v873 = if v869 = 1 then v90 else v88) → (v874 = if v870 = 1 then v88 else v90) → (v875 = if v870 = 1 then v90 else v88) → (v876 = if v869 = 1 then v88 else v90) → (v877 = if v871 = 1 then v765 else v763) → (v878 = if v872 = 1 then v763 else v765) → (v879 = if v872 = 1 then v765 else v763) → (v880 = if v871 = 1 then v763 else v765) → (sv v886 = sv v874 * sv v874) → (sv v887 = -((-sv v886) / 2 ^ 28)) → (sv v888 = sv v887 + sv v887) → (sv v889 = sv v33 - sv v888) → ((v890 = 1 ↔ sv v889 < sv v94)) → (v891 = if v890 = 1 then v94 else v889) → (sv v892 = sv v873 * sv v873) → (sv v893 = sv v892 / 2 ^ 28) → (sv v894 = sv v893 + sv v893) → (sv v895 = sv v33 - sv v894) → (sv v896 = sv v878 * sv v878) → (sv v897 = -((-sv v896) / 2 ^ 28)) → (sv v898 = sv v897 + sv v897) → (sv v899 = sv v33 - sv v898) → ((v900 = 1 ↔ sv v899 < sv v94)) → (v901 = if v900 = 1 then v94 else v899) → (sv v902 = sv v877 * sv v877) → (sv v903 = sv v902 / 2 ^ 28) → (sv v904 = sv v903 + sv v903) → (sv v905 = sv v33 - sv v904) → ((v906 = 1 ↔ sv v891 < sv v9)) → ((v907 = 1 ↔ ¬v906 = 1)) → ((v908 = 1 ↔ sv v9 < sv v895)) → ((v909 = 1 ↔ ¬v908 = 1)) → ((v910 = 1 ↔ v906 = 1 ∧ v909 = 1)) → ((v911 = 1 ↔ v906 = 1 ∧ v908 = 1)) → ((v912 = 1 ↔ sv v901 < sv v9)) → ((v913 = 1 ↔ ¬v912 = 1)) → ((v914 = 1 ↔ sv v9 < sv v905)) → ((v915 = 1 ↔ ¬v914 = 1)) → ((v916 = 1 ↔ v912 = 1 ∧ v915 = 1)) → ((v917 = 1 ↔ v912 = 1 ∧ v914 = 1)) → ((v918 = 1 ↔ v911 = 1 ∧ v917 = 1)) → ((v919 = 1 ↔ ¬v918 = 1)) → (R 1 0 0 1 v920 v920) → ((v920 = 1 ↔ v822 = 1 ∨ v919 = 1)) → ((v921 = 1 ↔ v907 = 1 ∧ v917 = 1)) → ((v922 = 1 ↔ v916 = 1 ∨ v921 = 1)) → (v923 = if v922 = 1 then v895 else v891) → ((v924 = 1 ↔ v911 = 1 ∧ v913 = 1)) → ((v925 = 1 ↔ v910 = 1 ∨ v924 = 1)) → (v926 = if v925 = 1 then v905 else v901) → (sv v933 = sv v926 * sv v923) → (sv v934 = sv v933 / 2 ^ 28) → (sv v938 = sv v787 - sv v934) → (sv v939 = (72057594037927936)) → (sv v940 = sv v939 - sv v892) → (sv v941 = ((Nat.sqrt (v940 - 4611686018427387904) : ℕ) : ℤ)) → (sv v942 = sv v104 + sv v941) → (sv v943 = sv v941 * sv v873) → (sv v944 = sv v943 / 2 ^ 28) → (sv v945 = sv v944 + sv v944) → (sv v946 = sv v942 * sv v873) → (sv v947 = -((-sv v946) / 2 ^ 28)) → (sv v948 = sv v947 + sv v947) → ((v949 = 1 ↔ sv v948 < sv v33)) → (v950 = if v949 = 1 then v948 else v33) → (sv v951 = sv v939 - sv v886) → (sv v952 = ((Nat.sqrt (v951 - 4611686018427387904) : ℕ) : ℤ)) → (sv v953 = sv v104 + sv v952) → (sv v954 = sv v952 * sv v874) → (sv v955 = sv v954 / 2 ^ 28) → (sv v956 = sv v955 + sv v955) → (sv v957 = sv v953 * sv v874) → (sv v958 = -((-sv v957) / 2 ^ 28)) → (sv v959 = sv v958 + sv v958) → ((v960 = 1 ↔ sv v959 < sv v33)) → (v961 = if v960 = 1 then v959 else v33) → ((v962 = 1 ↔ sv v945 < sv v956)) → (v963 = if v962 = 1 then v945 else v956) → ((v964 = 1 ↔ sv v950 < sv v961)) → (v965 = if v964 = 1 then v961 else v950) → (sv v966 = (36028797018963968)) → ((v967 = 1 ↔ sv v966 < sv v892)) → ((v968 = 1 ↔ ¬v967 = 1)) → ((v969 = 1 ↔ sv v886 < sv v966)) → ((v970 = 1 ↔ ¬v969 = 1)) → ((v971 = 1 ↔ v968 = 1 ∧ v970 = 1)) → (v972 = if v971 = 1 then v33 else v965) → (sv v973 = sv v939 - sv v902) → (sv v974 = ((Nat.sqrt (v973 - 4611686018427387904) : ℕ) : ℤ)) → (sv v975 = sv v104 + sv v974) → (sv v976 = sv v974 * sv v877) → (sv v977 = sv v976 / 2 ^ 28) → (sv v978 = sv v977 + sv v977) → (sv v979 = sv v975 * sv v877) → (sv v980 = -((-sv v979) / 2 ^ 28)) → (sv v981 = sv v980 + sv v980) → ((v982 = 1 ↔ sv v981 < sv v33)) → (v983 = if v982 = 1 then v981 else v33) → (sv v984 = sv v939 - sv v896) → (sv v985 = ((Nat.sqrt (v984 - 4611686018427387904) : ℕ) : ℤ)) → (sv v986 = sv v104 + sv v985) → (sv v987 = sv v985 * sv v878) → (sv v988 = sv v987 / 2 ^ 28) → (sv v989 = sv v988 + sv v988) → (sv v990 = sv v986 * sv v878) → (sv v991 = -((-sv v990) / 2 ^ 28)) → (sv v992 = sv v991 + sv v991) → ((v993 = 1 ↔ sv v992 < sv v33)) → (v994 = if v993 = 1 then v992 else v33) → ((v995 = 1 ↔ sv v978 < sv v989)) → (v996 = if v995 = 1 then v978 else v989) → ((v997 = 1 ↔ sv v983 < sv v994)) → (v998 = if v997 = 1 then v994 else v983) → ((v999 = 1 ↔ sv v966 < sv v902)) → ((v1000 = 1 ↔ ¬v999 = 1)) → ((v1001 = 1 ↔ sv v896 < sv v966)) → ((v1002 = 1 ↔ ¬v1001 = 1)) → ((v1003 = 1 ↔ v1000 = 1 ∧ v1002 = 1)) → (v1004 = if v1003 = 1 then v33 else v998) → ((v1005 = 1 ↔ sv v963 < sv v9)) → ((v1006 = 1 ↔ ¬v1005 = 1)) → ((v1007 = 1 ↔ sv v9 < sv v972)) → ((v1008 = 1 ↔ ¬v1007 = 1)) → ((v1009 = 1 ↔ v1005 = 1 ∧ v1008 = 1)) → ((v1010 = 1 ↔ v1005 = 1 ∧ v1007 = 1)) → ((v1011 = 1 ↔ sv v996 < sv v9)) → ((v1012 = 1 ↔ ¬v1011 = 1)) → ((v1013 = 1 ↔ sv v9 < sv v1004)) → ((v1014 = 1 ↔ ¬v1013 = 1)) → ((v1015 = 1 ↔ v1011 = 1 ∧ v1014 = 1)) → ((v1016 = 1 ↔ v1011 = 1 ∧ v1013 = 1)) → ((v1017 = 1 ↔ v1010 = 1 ∧ v1016 = 1)) → ((v1018 = 1 ↔ ¬v1017 = 1)) → (R 1 0 0 1 v1019 v1019) → ((v1019 = 1 ↔ v822 = 1 ∨ v1018 = 1)) → ((v1020 = 1 ↔ v1006 = 1 ∧ v1016 = 1)) → ((v1021 = 1 ↔ v1015 = 1 ∨ v1020 = 1)) → (v1022 = if v1021 = 1 then v972 else v963) → ((v1023 = 1 ↔ v1010 = 1 ∧ v1012 = 1)) → ((v1024 = 1 ↔ v1009 = 1 ∨ v1023 = 1)) → (v1025 = if v1024 = 1 then v1004 else v996) → ((v1026 = 1 ↔ v1009 = 1 ∧ v1016 = 1)) → ((v1027 = 1 ↔ v1015 = 1 ∨ v1026 = 1)) → (v1028 = if v1027 = 1 then v963 else v972) → ((v1029 = 1 ↔ v1010 = 1 ∧ v1015 = 1)) → ((v1030 = 1 ↔ v1009 = 1 ∨ v1029 = 1)) → (v1031 = if v1030 = 1 then v996 else v1004) → (sv v1032 = sv v1025 * sv v1022) → (sv v1033 = sv v1032 / 2 ^ 28) → (sv v1034 = sv v1031 * sv v1028) → (sv v1035 = -((-sv v1034) / 2 ^ 28)) → ((v1036 = 1 ↔ sv v9 < sv v1033)) → ((v1037 = 1 ↔ ¬v1036 = 1)) → ((v1040 = 1 ↔ sv v938 < sv v9)) → (v1041 = if v1040 = 1 then v1035 else v1033) → (sv v1042 = sv v9 - sv v1041) → ((v1043 = 1 ↔ sv v938 < sv v1042)) → ((v1044 = 1 ↔ v1036 = 1 ∧ v1043 = 1)) → ((v1045 = 1 ↔ sv v938 < sv v1041)) → ((v1046 = 1 ↔ ¬v1045 = 1)) → ((v1047 = 1 ↔ v1037 = 1 ∨ v1046 = 1)) → (v1048 = if v1047 = 1 then v33 else v938) → (v1049 = if v1047 = 1 then v33 else v1041) → (sv v1053 = sv v876 * sv v876) → (sv v1054 = -((-sv v1053) / 2 ^ 28)) → (sv v1055 = sv v1054 + sv v1054) → (sv v1056 = sv v33 - sv v1055) → ((v1057 = 1 ↔ sv v1056 < sv v94)) → (v1058 = if v1057 = 1 then v94 else v1056) → (sv v1059 = sv v875 * sv v875) → (sv v1060 = sv v1059 / 2 ^ 28) → (sv v1061 = sv v1060 + sv v1060) → (sv v1062 = sv v33 - sv v1061) → (sv v1063 = sv v880 * sv v880) → (sv v1064 = -((-sv v1063) / 2 ^ 28)) → (sv v1065 = sv v1064 + sv v1064) → (sv v1066 = sv v33 - sv v1065) → ((v1067 = 1 ↔ sv v1066 < sv v94)) → (v1068 = if v1067 = 1 then v94 else v1066) → (sv v1069 = sv v879 * sv v879) → (sv v1070 = sv v1069 / 2 ^ 28) → (sv v1071 = sv v1070 + sv v1070) → (sv v1072 = sv v33 - sv v1071) → ((v1073 = 1 ↔ sv v1058 < sv v9)) → ((v1075 = 1 ↔ sv v9 < sv v1062)) → ((v1076 = 1 ↔ ¬v1075 = 1)) → ((v1077 = 1 ↔ v1073 = 1 ∧ v1076 = 1)) → ((v1078 = 1 ↔ v1073 = 1 ∧ v1075 = 1)) → ((v1079 = 1 ↔ sv v1068 < sv v9)) → ((v1081 = 1 ↔ sv v9 < sv v1072)) → ((v1082 = 1 ↔ ¬v1081 = 1)) → ((v1083 = 1 ↔ v1079 = 1 ∧ v1082 = 1)) → ((v1084 = 1 ↔ v1079 = 1 ∧ v1081 = 1)) → ((v1085 = 1 ↔ v1078 = 1 ∧ v1084 = 1)) → ((v1086 = 1 ↔ ¬v1085 = 1)) → (R 1 0 0 1 v1087 v1087) → ((v1087 = 1 ↔ v822 = 1 ∨ v1086 = 1)) → ((v1094 = 1 ↔ v1077 = 1 ∧ v1084 = 1)) → ((v1095 = 1 ↔ v1083 = 1 ∨ v1094 = 1)) → (v1096 = if v1095 = 1 then v1058 else v1062) → ((v1097 = 1 ↔ v1078 = 1 ∧ v1083 = 1)) → ((v1098 = 1 ↔ v1077 = 1 ∨ v1097 = 1)) → (v1099 = if v1098 = 1 then v1068 else v1072) → (sv v1102 = sv v1099 * sv v1096) → (sv v1103 = -((-sv v1102) / 2 ^ 28)) → (sv v1104 = sv v783 - sv v1103) → (sv v1106 = sv v939 - sv v1059) → (sv v1107 = ((Nat.sqrt (v1106 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1108 = sv v104 + sv v1107) → (sv v1109 = sv v1107 * sv v875) → (sv v1110 = sv v1109 / 2 ^ 28) → (sv v1111 = sv v1110 + sv v1110) → (sv v1112 = sv v1108 * sv v875) → (sv v1113 = -((-sv v1112) / 2 ^ 28)) → (sv v1114 = sv v1113 + sv v1113) → ((v1115 = 1 ↔ sv v1114 < sv v33)) → (v1116 = if v1115 = 1 then v1114 else v33) → (sv v1117 = sv v939 - sv v1053) → (sv v1118 = ((Nat.sqrt (v1117 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1119 = sv v104 + sv v1118) → (sv v1120 = sv v1118 * sv v876) → (sv v1121 = sv v1120 / 2 ^ 28) → (sv v1122 = sv v1121 + sv v1121) → (sv v1123 = sv v1119 * sv v876) → (sv v1124 = -((-sv v1123) / 2 ^ 28)) → (sv v1125 = sv v1124 + sv v1124) → ((v1126 = 1 ↔ sv v1125 < sv v33)) → (v1127 = if v1126 = 1 then v1125 else v33) → ((v1128 = 1 ↔ sv v1111 < sv v1122)) → (v1129 = if v1128 = 1 then v1111 else v1122) → ((v1130 = 1 ↔ sv v1116 < sv v1127)) → (v1131 = if v1130 = 1 then v1127 else v1116) → ((v1132 = 1 ↔ sv v966 < sv v1059)) → ((v1133 = 1 ↔ ¬v1132 = 1)) → ((v1134 = 1 ↔ sv v1053 < sv v966)) → ((v1135 = 1 ↔ ¬v1134 = 1)) → ((v1136 = 1 ↔ v1133 = 1 ∧ v1135 = 1)) → (v1137 = if v1136 = 1 then v33 else v1131) → (sv v1138 = sv v939 - sv v1069) → (sv v1139 = ((Nat.sqrt (v1138 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1140 = sv v104 + sv v1139) → (sv v1141 = sv v1139 * sv v879) → (sv v1142 = sv v1141 / 2 ^ 28) → (sv v1143 = sv v1142 + sv v1142) → (sv v1144 = sv v1140 * sv v879) → (sv v1145 = -((-sv v1144) / 2 ^ 28)) → (sv v1146 = sv v1145 + sv v1145) → ((v1147 = 1 ↔ sv v1146 < sv v33)) → (v1148 = if v1147 = 1 then v1146 else v33) → (sv v1149 = sv v939 - sv v1063) → (sv v1150 = ((Nat.sqrt (v1149 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1151 = sv v104 + sv v1150) → (sv v1152 = sv v1150 * sv v880) → (sv v1153 = sv v1152 / 2 ^ 28) → (sv v1154 = sv v1153 + sv v1153) → (sv v1155 = sv v1151 * sv v880) → (sv v1156 = -((-sv v1155) / 2 ^ 28)) → (sv v1157 = sv v1156 + sv v1156) → ((v1158 = 1 ↔ sv v1157 < sv v33)) → (v1159 = if v1158 = 1 then v1157 else v33) → ((v1160 = 1 ↔ sv v1143 < sv v1154)) → (v1161 = if v1160 = 1 then v1143 else v1154) → ((v1162 = 1 ↔ sv v1148 < sv v1159)) → (v1163 = if v1162 = 1 then v1159 else v1148) → ((v1164 = 1 ↔ sv v966 < sv v1069)) → ((v1165 = 1 ↔ ¬v1164 = 1)) → ((v1166 = 1 ↔ sv v1063 < sv v966)) → ((v1167 = 1 ↔ ¬v1166 = 1)) → ((v1168 = 1 ↔ v1165 = 1 ∧ v1167 = 1)) → (v1169 = if v1168 = 1 then v33 else v1163) → ((v1170 = 1 ↔ sv v1129 < sv v9)) → ((v1171 = 1 ↔ ¬v1170 = 1)) → ((v1172 = 1 ↔ sv v9 < sv v1137)) → ((v1173 = 1 ↔ ¬v1172 = 1)) → ((v1174 = 1 ↔ v1170 = 1 ∧ v1173 = 1)) → ((v1175 = 1 ↔ v1170 = 1 ∧ v1172 = 1)) → ((v1176 = 1 ↔ sv v1161 < sv v9)) → ((v1177 = 1 ↔ ¬v1176 = 1)) → ((v1178 = 1 ↔ sv v9 < sv v1169)) → ((v1179 = 1 ↔ ¬v1178 = 1)) → ((v1180 = 1 ↔ v1176 = 1 ∧ v1179 = 1)) → ((v1181 = 1 ↔ v1176 = 1 ∧ v1178 = 1)) → ((v1182 = 1 ↔ v1175 = 1 ∧ v1181 = 1)) → ((v1183 = 1 ↔ ¬v1182 = 1)) → (R 1 0 0 1 v1184 v1184) → ((v1184 = 1 ↔ v822 = 1 ∨ v1183 = 1)) → ((v1185 = 1 ↔ v1171 = 1 ∧ v1181 = 1)) → ((v1186 = 1 ↔ v1180 = 1 ∨ v1185 = 1)) → (v1187 = if v1186 = 1 then v1137 else v1129) → ((v1188 = 1 ↔ v1175 = 1 ∧ v1177 = 1)) → ((v1189 = 1 ↔ v1174 = 1 ∨ v1188 = 1)) → (v1190 = if v1189 = 1 then v1169 else v1161) → ((v1191 = 1 ↔ v1174 = 1 ∧ v1181 = 1)) → ((v1192 = 1 ↔ v1180 = 1 ∨ v1191 = 1)) → (v1193 = if v1192 = 1 then v1129 else v1137) → ((v1194 = 1 ↔ v1175 = 1 ∧ v1180 = 1)) → ((v1195 = 1 ↔ v1174 = 1 ∨ v1194 = 1)) → (v1196 = if v1195 = 1 then v1161 else v1169) → (sv v1197 = sv v1190 * sv v1187) → (sv v1198 = sv v1197 / 2 ^ 28) → (sv v1199 = sv v1196 * sv v1193) → (sv v1200 = -((-sv v1199) / 2 ^ 28)) → ((v1201 = 1 ↔ sv v9 < sv v1198)) → ((v1202 = 1 ↔ ¬v1201 = 1)) → ((v1203 = 1 ↔ sv v1104 < sv v9)) → (v1204 = if v1203 = 1 then v1198 else v1200) → ((v1207 = 1 ↔ sv v1204 < sv v1104)) → ((v1208 = 1 ↔ v1201 = 1 ∧ v1207 = 1)) → (sv v1209 = sv v9 - sv v1204) → ((v1210 = 1 ↔ sv v1209 < sv v1104)) → ((v1211 = 1 ↔ ¬v1210 = 1)) → ((v1212 = 1 ↔ v1202 = 1 ∨ v1211 = 1)) → (v1213 = if v1212 = 1 then v94 else v1104) → (v1214 = if v1212 = 1 then v33 else v1204) → ((v1215 = 1 ↔ v1044 = 1 ∨ v1208 = 1)) → (sv v1217 = ((H1 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ)) → ((v1218 = 1 ↔ sv v9 < sv v1217)) → ((v1219 = 1 ↔ ¬v1218 = 1)) → (R 1 0 4611686018427387904 4611686018695823363 t1217.1 t1217.1) → (R 1 0 4611686018158952445 4611686018695823363 t1217.2 t1217.2) → (sv t1217.1 = (sc28pS (scArg v1217)).1) → (sv t1217.2 = (sc28pS (scArg v1217)).2) → (sv v1221 = sv v28 + sv t1217.2) → ((v1222 = 1 ↔ sv v1221 < sv v94)) → (v1223 = if v1222 = 1 then v94 else v1221) → (sv v1224 = sv v1048 * 2 ^ 28) → (sv v1225 = sv v1223 * sv v1049) → ((v1226 = 1 ↔ sv v1225 < sv v1224)) → ((v1227 = 1 ↔ ¬v1226 = 1)) → ((v1228 = 1 ↔ sv v14 < sv v1217)) → ((v1229 = 1 ↔ ¬v1228 = 1)) → ((v1230 = 1 ↔ v1227 = 1 ∧ v1229 = 1)) → (R 1 0 0 1 v1231 v1231) → ((v1231 = 1 ↔ v1219 = 1 ∨ v1230 = 1)) → (v1232 = if v1231 = 1 then v1217 else v9) → (sv v1233 = ((H1 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ)) → ((v1234 = 1 ↔ sv v1233 < sv v20)) → ((v1235 = 1 ↔ ¬v1234 = 1)) → (R 1 0 4611686018427387904 4611686018695823363 t1233.1 t1233.1) → (R 1 0 4611686018158952445 4611686018695823363 t1233.2 t1233.2) → (sv t1233.1 = (sc28pS (scArg v1233)).1) → (sv t1233.2 = (sc28pS (scArg v1233)).2) → (sv v1237 = sv v31 + sv t1233.2) → ((v1238 = 1 ↔ sv v1237 < sv v33)) → (v1239 = if v1238 = 1 then v1237 else v33) → (sv v1240 = sv v1213 * 2 ^ 28) → (sv v1241 = sv v1239 * sv v1214) → ((v1242 = 1 ↔ sv v1240 < sv v1241)) → ((v1243 = 1 ↔ ¬v1242 = 1)) → (R 1 0 0 1 v1244 v1244) → ((v1244 = 1 ↔ v1235 = 1 ∨ v1243 = 1)) → (v1245 = if v1244 = 1 then v1233 else v20) → (R 1 0 4611686018427387904 4611686019501129727 v1246 v1246) → (v1246 = if v777 = 1 then v1232 else v9) → (R 1 0 4611686018427387904 4611686019501129727 v1247 v1247) → (v1247 = if v777 = 1 then v1245 else v20) → ((v1248 = 1 ↔ v777 = 1 ∧ v1215 = 1)) → (R 1 0 0 1 v1251 v1251) → ((v1251 = 1 ↔ ¬v1248 = 1)) → ((v1252 = 1 ↔ v819 = 1 ∧ v847 = 1)) → ((v1253 = 1 ↔ ¬v1252 = 1)) → (R 1 0 0 1 v1254 v1254) → ((v1254 = 1 ↔ v822 = 1 ∨ v1253 = 1)) → ((v1255 = 1 ↔ v815 = 1 ∧ v847 = 1)) → ((v1256 = 1 ↔ v846 = 1 ∨ v1255 = 1)) → (v1257 = if v1256 = 1 then v807 else v803) → ((v1258 = 1 ↔ v819 = 1 ∧ v843 = 1)) → ((v1259 = 1 ↔ v818 = 1 ∨ v1258 = 1)) → (v1260 = if v1259 = 1 then v797 else v793) → ((v1261 = 1 ↔ v818 = 1 ∧ v847 = 1)) → ((v1262 = 1 ↔ v846 = 1 ∨ v1261 = 1)) → (v1263 = if v1262 = 1 then v803 else v807) → ((v1264 = 1 ↔ v819 = 1 ∧ v846 = 1)) → ((v1265 = 1 ↔ v818 = 1 ∨ v1264 = 1)) → (v1266 = if v1265 = 1 then v793 else v797) → (sv v1267 = sv v1260 * sv v1257) → (sv v1268 = sv v1267 / 2 ^ 28) → (sv v1269 = sv v1266 * sv v1263) → (sv v1270 = -((-sv v1269) / 2 ^ 28)) → (sv v1271 = sv v783 - sv v1270) → (sv v1272 = sv v787 - sv v1268) → ((v1273 = 1 ↔ sv v9 < sv v1271)) → ((v1274 = 1 ↔ sv v1272 < sv v9)) → (v1275 = if v869 = 1 then v439 else v437) → (v1276 = if v870 = 1 then v437 else v439) → (R 1 0 4611686018427387899 4611686018695823375 v1277 v1277) → (v1277 = if v870 = 1 then v439 else v437) → (R 1 0 4611686018427387899 4611686018695823375 v1278 v1278) → (v1278 = if v869 = 1 then v437 else v439) → (v1279 = if v1273 = 1 then v765 else v763) → (R 1 0 4611686018427387899 4611686018695823375 v1280 v1280) → (v1280 = if v1274 = 1 then v763 else v765) → (R 1 0 4611686018427387899 4611686018695823375 v1281 v1281) → (v1281 = if v1274 = 1 then v765 else v763) → (R 1 0 4611686018427387899 4611686018695823375 v1282 v1282) → (v1282 = if v1273 = 1 then v763 else v765) → (sv v1288 = sv v1276 * sv v1276) → (sv v1289 = -((-sv v1288) / 2 ^ 28)) → (sv v1290 = sv v1289 + sv v1289) → (sv v1291 = sv v33 - sv v1290) → ((v1292 = 1 ↔ sv v1291 < sv v94)) → (v1293 = if v1292 = 1 then v94 else v1291) → (sv v1294 = sv v1275 * sv v1275) → (sv v1295 = sv v1294 / 2 ^ 28) → (sv v1296 = sv v1295 + sv v1295) → (sv v1297 = sv v33 - sv v1296) → (R 1 0 4611686018427387904 4683743620518379745 v1298 v1298) → (sv v1298 = sv v1280 * sv v1280) → (sv v1299 = -((-sv v1298) / 2 ^ 28)) → (sv v1300 = sv v1299 + sv v1299) → (sv v1301 = sv v33 - sv v1300) → ((v1302 = 1 ↔ sv v1301 < sv v94)) → (v1303 = if v1302 = 1 then v94 else v1301) → (R 1 0 4611686018427387904 4683743620518379745 v1304 v1304) → (sv v1304 = sv v1279 * sv v1279) → (sv v1305 = sv v1304 / 2 ^ 28) → (sv v1306 = sv v1305 + sv v1305) → (sv v1307 = sv v33 - sv v1306) → ((v1308 = 1 ↔ sv v1293 < sv v9)) → ((v1309 = 1 ↔ ¬v1308 = 1)) → ((v1310 = 1 ↔ sv v9 < sv v1297)) → ((v1311 = 1 ↔ ¬v1310 = 1)) → ((v1312 = 1 ↔ v1308 = 1 ∧ v1311 = 1)) → ((v1313 = 1 ↔ v1308 = 1 ∧ v1310 = 1)) → ((v1314 = 1 ↔ sv v1303 < sv v9)) → ((v1315 = 1 ↔ ¬v1314 = 1)) → ((v1316 = 1 ↔ sv v9 < sv v1307)) → ((v1317 = 1 ↔ ¬v1316 = 1)) → ((v1318 = 1 ↔ v1314 = 1 ∧ v1317 = 1)) → ((v1319 = 1 ↔ v1314 = 1 ∧ v1316 = 1)) → ((v1320 = 1 ↔ v1313 = 1 ∧ v1319 = 1)) → ((v1321 = 1 ↔ ¬v1320 = 1)) → (R 1 0 0 1 v1322 v1322) → ((v1322 = 1 ↔ v822 = 1 ∨ v1321 = 1)) → ((v1323 = 1 ↔ v1309 = 1 ∧ v1319 = 1)) → ((v1324 = 1 ↔ v1318 = 1 ∨ v1323 = 1)) → (v1325 = if v1324 = 1 then v1297 else v1293) → ((v1326 = 1 ↔ v1313 = 1 ∧ v1315 = 1)) → ((v1327 = 1 ↔ v1312 = 1 ∨ v1326 = 1)) → (v1328 = if v1327 = 1 then v1307 else v1303) → (sv v1335 = sv v1328 * sv v1325) → (sv v1336 = sv v1335 / 2 ^ 28) → (R 1 0 4611686017890516812 4611686018964258878 v1340 v1340) → (sv v1340 = sv v807 - sv v1336) → (sv v1341 = sv v939 - sv v1294) → (sv v1342 = ((Nat.sqrt (v1341 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1343 = sv v104 + sv v1342) → (sv v1344 = sv v1342 * sv v1275) → (sv v1345 = sv v1344 / 2 ^ 28) → (sv v1346 = sv v1345 + sv v1345) → (sv v1347 = sv v1343 * sv v1275) → (sv v1348 = -((-sv v1347) / 2 ^ 28)) → (sv v1349 = sv v1348 + sv v1348) → ((v1350 = 1 ↔ sv v1349 < sv v33)) → (v1351 = if v1350 = 1 then v1349 else v33) → (sv v1352 = sv v939 - sv v1288) → (sv v1353 = ((Nat.sqrt (v1352 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1354 = sv v104 + sv v1353) → (sv v1355 = sv v1353 * sv v1276) → (sv v1356 = sv v1355 / 2 ^ 28) → (sv v1357 = sv v1356 + sv v1356) → (sv v1358 = sv v1354 * sv v1276) → (sv v1359 = -((-sv v1358) / 2 ^ 28)) → (sv v1360 = sv v1359 + sv v1359) → ((v1361 = 1 ↔ sv v1360 < sv v33)) → (v1362 = if v1361 = 1 then v1360 else v33) → ((v1363 = 1 ↔ sv v1346 < sv v1357)) → (R 1 0 4611686018427387894 4611686018695823360 v1364 v1364) → (v1364 = if v1363 = 1 then v1346 else v1357) → ((v1365 = 1 ↔ sv v1351 < sv v1362)) → (v1366 = if v1365 = 1 then v1362 else v1351) → ((v1367 = 1 ↔ sv v966 < sv v1294)) → ((v1368 = 1 ↔ ¬v1367 = 1)) → ((v1369 = 1 ↔ sv v1288 < sv v966)) → ((v1370 = 1 ↔ ¬v1369 = 1)) → ((v1371 = 1 ↔ v1368 = 1 ∧ v1370 = 1)) → (R 1 0 4611686018427387894 4611686018695823364 v1372 v1372) → (v1372 = if v1371 = 1 then v33 else v1366) → (sv v1373 = sv v939 - sv v1304) → (sv v1374 = ((Nat.sqrt (v1373 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1375 = sv v104 + sv v1374) → (sv v1376 = sv v1374 * sv v1279) → (sv v1377 = sv v1376 / 2 ^ 28) → (R 1 0 4611686018427387894 4611686018695823360 v1378 v1378) → (sv v1378 = sv v1377 + sv v1377) → (sv v1379 = sv v1375 * sv v1279) → (sv v1380 = -((-sv v1379) / 2 ^ 28)) → (sv v1381 = sv v1380 + sv v1380) → ((v1382 = 1 ↔ sv v1381 < sv v33)) → (R 1 0 4611686018427387894 4611686018695823364 v1383 v1383) → (v1383 = if v1382 = 1 then v1381 else v33) → (sv v1384 = sv v939 - sv v1298) → (R 1 0 4611686018427387904 4611686018695823360 v1385 v1385) → (sv v1385 = ((Nat.sqrt (v1384 - 4611686018427387904) : ℕ) : ℤ)) → (R 1 0 4611686018427387905 4611686018695823361 v1386 v1386) → (sv v1386 = sv v104 + sv v1385) → (PB 1 v1385 v1280 36028797018963968) → (PB 1 v1386 v1280 36028797287399439) → P) → P := by
  intro OFFr v9 v14 v20 v28 v31 v33 v94 v104 v838 v839 v840 v841 v842 v843 v844 v845 v846 v847 v848 v849 v850 v851 v852 v853 v854 v855 v856 v857 v858 v859 v860 v861 v862 v863 v864 v865 v866 v867 v868 v869 v870 v871 v872 v873 v874 v875 v876 v877 v878 v879 v880 v886 v887 v888 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 v918 v919 v920 v921 v922 v923 v924 v925 v926 v933 v934 v938 v939 v940 v941 v942 v943 v944 v945 v946 v947 v948 v949 v950 v951 v952 v953 v954 v955 v956 v957 v958 v959 v960 v961 v962 v963 v964 v965 v966 v967 v968 v969 v970 v971 v972 v973 v974 v975 v976 v977 v978 v979 v980 v981 v982 v983 v984 v985 v986 v987 v988 v989 v990 v991 v992 v993 v994 v995 v996 v997 v998 v999 v1000 v1001 v1002 v1003 v1004 v1005 v1006 v1007 v1008 v1009 v1010 v1011 v1012 v1013 v1014 v1015 v1016 v1017 v1018 v1019 v1020 v1021 v1022 v1023 v1024 v1025 v1026 v1027 v1028 v1029 v1030 v1031 v1032 v1033 v1034 v1035 v1036 v1037 v1040 v1041 v1042 v1043 v1044 v1045 v1046 v1047 v1048 v1049 v1053 v1054 v1055 v1056 v1057 v1058 v1059 v1060 v1061 v1062 v1063 v1064 v1065 v1066 v1067 v1068 v1069 v1070 v1071 v1072 v1073 v1075 v1076 v1077 v1078 v1079 v1081 v1082 v1083 v1084 v1085 v1086 v1087 v1094 v1095 v1096 v1097 v1098 v1099 v1102 v1103 v1104 v1106 v1107 v1108 v1109 v1110 v1111 v1112 v1113 v1114 v1115 v1116 v1117 v1118 v1119 v1120 v1121 v1122 v1123 v1124 v1125 v1126 v1127 v1128 v1129 v1130 v1131 v1132 v1133 v1134 v1135 v1136 v1137 v1138 v1139 v1140 v1141 v1142 v1143 v1144 v1145 v1146 v1147 v1148 v1149 v1150 v1151 v1152 v1153 v1154 v1155 v1156 v1157 v1158 v1159 v1160 v1161 v1162 v1163 v1164 v1165 v1166 v1167 v1168 v1169 v1170 v1171 v1172 v1173 v1174 v1175 v1176 v1177 v1178 v1179 v1180 v1181 v1182 v1183 v1184 v1185 v1186 v1187 v1188 v1189 v1190 v1191 v1192 v1193 v1194 v1195 v1196 v1197 v1198 v1199 v1200 v1201 v1202 v1203 v1204 v1207 v1208 v1209 v1210 v1211 v1212 v1213 v1214 v1215 v1217 v1218 v1219 t1217 v1221 v1222 v1223 v1224 v1225 v1226 v1227 v1228 v1229 v1230 v1231 v1232 v1233 v1234 v1235 t1233 v1237 v1238 v1239 v1240 v1241 v1242 v1243 v1244 v1245 v1246 v1247 v1248 v1251 v1252 v1253 v1254 v1255 v1256 v1257 v1258 v1259 v1260 v1261 v1262 v1263 v1264 v1265 v1266 v1267 v1268 v1269 v1270 v1271 v1272 v1273 v1274 v1275 v1276 v1277 v1278 v1279 v1280 v1281 v1282 v1288 v1289 v1290 v1291 v1292 v1293 v1294 v1295 v1296 v1297 v1298 v1299 v1300 v1301 v1302 v1303 v1304 v1305 v1306 v1307 v1308 v1309 v1310 v1311 v1312 v1313 v1314 v1315 v1316 v1317 v1318 v1319 v1320 v1321 v1322 v1323 v1324 v1325 v1326 v1327 v1328 v1335 v1336 v1340 v1341 v1342 v1343 v1344 v1345 v1346 v1347 v1348 v1349 v1350 v1351 v1352 v1353 v1354 v1355 v1356 v1357 v1358 v1359 v1360 v1361 v1362 v1363 v1364 v1365 v1366 v1367 v1368 v1369 v1370 v1371 v1372 v1373 v1374 v1375 v1376 v1377 v1378 v1379 v1380 v1381 v1382 v1383 v1384 v1385 v1386
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v9 : R 1 0 4611686018427387904 4611686018427387904 v9 v9 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v14 : R 1 0 4611686019270702760 4611686019270702760 v14 v14 := (r_c hl 4611686019270702760 (of_decide_eq_true rfl))
  have h_v20 : R 1 0 4611686019270702761 4611686019270702761 v20 v20 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have h_v28 : R 1 0 4611686018427387900 4611686018427387900 v28 v28 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have h_v31 : R 1 0 4611686018427387908 4611686018427387908 v31 v31 := (r_c hl 4611686018427387908 (of_decide_eq_true rfl))
  have h_v33 : R 1 0 4611686018695823360 4611686018695823360 v33 v33 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have h_v94 : R 1 0 4611686018158952448 4611686018158952448 v94 v94 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have h_v104 : R 1 0 4611686018427387905 4611686018427387905 v104 v104 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have h_v838 : R 1 0 4539628407746461696 4683743645751316228 v838 v838 := (r_smx hl 30 h_v835 h_v832 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v838 : sv v838 = sv v835 * sv v832 := e_smx 30 h_v835 h_v832 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
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
  clear h_v838 h_v839
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
  clear h_v842 h_v844 h_v845 h_v848 h_v849 h_v851 h_v852 h_v854 h_v855
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
  clear h_v840 h_v841 h_v853 h_v856 h_v857 h_v858 h_v859 h_v860 h_v861 h_v862 h_v863 h_v864 h_v865 h_v866
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
  have e_v876 : v876 = if v869 = 1 then v88 else v90 := e_psel h_v869 h_v88 h_v90 (of_decide_eq_true rfl)
  have h_v877 : R 1 0 4611686018427387899 4611686018695823375 v877 v877 := (r_psel hl h_v871 h_v765 h_v763 (of_decide_eq_true rfl))
  have e_v877 : v877 = if v871 = 1 then v765 else v763 := e_psel h_v871 h_v765 h_v763 (of_decide_eq_true rfl)
  have h_v878 : R 1 0 4611686018427387899 4611686018695823375 v878 v878 := (r_psel hl h_v872 h_v763 h_v765 (of_decide_eq_true rfl))
  have e_v878 : v878 = if v872 = 1 then v763 else v765 := e_psel h_v872 h_v763 h_v765 (of_decide_eq_true rfl)
  have h_v879 : R 1 0 4611686018427387899 4611686018695823375 v879 v879 := (r_psel hl h_v872 h_v765 h_v763 (of_decide_eq_true rfl))
  have e_v879 : v879 = if v872 = 1 then v765 else v763 := e_psel h_v872 h_v765 h_v763 (of_decide_eq_true rfl)
  have h_v880 : R 1 0 4611686018427387899 4611686018695823375 v880 v880 := (r_psel hl h_v871 h_v763 h_v765 (of_decide_eq_true rfl))
  have e_v880 : v880 = if v871 = 1 then v763 else v765 := e_psel h_v871 h_v763 h_v765 (of_decide_eq_true rfl)
  have h_v886 : R 1 0 4611686018427387904 4683743620518379745 v886 v886 := (r_smx_sq hl 29 h_v874 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v886 : sv v886 = sv v874 * sv v874 := e_smx_sq 29 h_v874 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v887 : R 1 0 4611686018427387904 4611686018695823391 v887 v887 := (r_srdC hl h_v886 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v887 : sv v887 = -((-sv v886) / 2 ^ 28) := e_srdC h_v886 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v888 : R 1 0 4611686018427387904 4611686018964258878 v888 v888 := (r_sub hl (r_add hl h_v887 h_v887 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v867 h_v868 h_v871 h_v872
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
  clear h_v887 h_v888 h_v889 h_v890 h_v893 h_v894 h_v897 h_v898
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
  clear h_v899 h_v900 h_v903 h_v904 h_v906 h_v908 h_v909
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
  clear h_v891 h_v895 h_v907 h_v910 h_v911 h_v912 h_v913 h_v914 h_v915 h_v916 h_v917 h_v918 h_v919 h_v921 h_v922 h_v924
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
  clear h_v901 h_v905 h_v923 h_v925 h_v926 h_v933 h_v934 h_v940 h_v941 pb_v941_v873 h_v943 h_v944
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
  clear h_v873 h_v874 h_v942 pb_v942_v873 h_v946 h_v947 h_v948 h_v949 h_v951 h_v952 h_v953 pb_v952_v874 h_v954 h_v955 pb_v953_v874
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
  clear h_v886 h_v892 h_v945 h_v950 h_v956 h_v957 h_v958 h_v959 h_v960 h_v961 h_v962 h_v964 h_v967
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
  clear h_v877 h_v965 h_v968 h_v969 h_v970 h_v971 h_v973 h_v974 h_v975 pb_v974_v877 h_v976 h_v977 pb_v975_v877 h_v979 h_v980
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
  clear h_v878 h_v981 h_v982 h_v984 h_v985 h_v986 pb_v985_v878 h_v987 h_v988 pb_v986_v878 h_v990 h_v991
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
  clear h_v896 h_v902 h_v978 h_v983 h_v989 h_v992 h_v993 h_v994 h_v995 h_v997 h_v998 h_v999 h_v1000 h_v1001 h_v1002 h_v1003
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
  clear h_v1005 h_v1007 h_v1008 h_v1011 h_v1013 h_v1014
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
  clear h_v963 h_v972 h_v1006 h_v1009 h_v1010 h_v1012 h_v1015 h_v1016 h_v1017 h_v1018 h_v1020 h_v1021 h_v1023 h_v1024 h_v1026 h_v1027 h_v1029
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
  have e_v1036 : (v1036 = 1 ↔ sv v9 < sv v1033) := e_plt h_v9 h_v1033 (of_decide_eq_true rfl)
  have h_v1037 : R 1 0 0 1 v1037 v1037 := (r_sub hl (r_O hl) h_v1036 (of_decide_eq_true rfl))
  have e_v1037 : (v1037 = 1 ↔ ¬v1036 = 1) := e_not h_v1036 (of_decide_eq_true rfl)
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
  have h_v1045 : R 1 0 0 1 v1045 v1045 := (r_plt hl h_v938 h_v1041 (of_decide_eq_true rfl))
  clear h_v996 h_v1004 h_v1022 h_v1025 h_v1028 h_v1030 h_v1031 h_v1032 h_v1033 h_v1034 h_v1035 h_v1036 h_v1040 h_v1042 h_v1043
  have e_v1045 : (v1045 = 1 ↔ sv v938 < sv v1041) := e_plt h_v938 h_v1041 (of_decide_eq_true rfl)
  have h_v1046 : R 1 0 0 1 v1046 v1046 := (r_sub hl (r_O hl) h_v1045 (of_decide_eq_true rfl))
  have e_v1046 : (v1046 = 1 ↔ ¬v1045 = 1) := e_not h_v1045 (of_decide_eq_true rfl)
  have h_v1047 : R 1 0 0 1 v1047 v1047 := (r_lor hl h_v1037 h_v1046 (of_decide_eq_true rfl))
  have e_v1047 : (v1047 = 1 ↔ v1037 = 1 ∨ v1046 = 1) := e_lor h_v1037 h_v1046 (of_decide_eq_true rfl)
  have h_v1048 : R 1 0 4611686017890516812 4611686018964258878 v1048 v1048 := (r_psel hl h_v1047 h_v33 h_v938 (of_decide_eq_true rfl))
  have e_v1048 : v1048 = if v1047 = 1 then v33 else v938 := e_psel h_v1047 h_v33 h_v938 (of_decide_eq_true rfl)
  have h_v1049 : R 1 0 4611686018427387893 4611686018695823369 v1049 v1049 := (r_psel hl h_v1047 h_v33 h_v1041 (of_decide_eq_true rfl))
  have e_v1049 : v1049 = if v1047 = 1 then v33 else v1041 := e_psel h_v1047 h_v33 h_v1041 (of_decide_eq_true rfl)
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
  have h_v1060 : R 1 0 4611686018427387904 4611686018695823390 v1060 v1060 := (r_srdF hl h_v1059 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1060 : sv v1060 = sv v1059 / 2 ^ 28 := e_srdF h_v1059 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  clear h_v938 h_v1037 h_v1041 h_v1045 h_v1046 h_v1047 h_v1054 h_v1055 h_v1056 h_v1057
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
  have e_v1072 : sv v1072 = sv v33 - sv v1071 := e_sub h_v33 h_v1071 (of_decide_eq_true rfl)
  have h_v1073 : R 1 0 0 1 v1073 v1073 := (r_plt hl h_v1058 h_v9 (of_decide_eq_true rfl))
  clear h_v1060 h_v1061 h_v1064 h_v1065 h_v1066 h_v1067 h_v1070 h_v1071
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
  have h_v1087 : R 1 0 0 1 v1087 v1087 := (r_lor hl h_v822 h_v1086 (of_decide_eq_true rfl))
  have e_v1087 : (v1087 = 1 ↔ v822 = 1 ∨ v1086 = 1) := e_lor h_v822 h_v1086 (of_decide_eq_true rfl)
  clear h_v1073 h_v1075 h_v1076 h_v1079 h_v1081 h_v1082 h_v1085 h_v1086
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
  have e_v1108 : sv v1108 = sv v104 + sv v1107 := e_add h_v104 h_v1107 (of_decide_eq_true rfl)
  have pb_v1107_v875 : PB 1 v1107 v875 36028797018963968 := pb_sqrt hl h_v875 29 36028797018963968 (of_decide_eq_true rfl)
  clear h_v1058 h_v1062 h_v1068 h_v1072 h_v1077 h_v1078 h_v1083 h_v1084 h_v1094 h_v1095 h_v1096 h_v1097 h_v1098 h_v1099 h_v1102 h_v1103 h_v1106
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
  have pb_v1118_v876 : PB 1 v1118 v876 36028797018963968 := pb_sqrt hl h_v876 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1120 : R 1 0 4611686017085210624 4647714815446351872 v1120 v1120 := (r_smx_pb hl 29 h_v1118 h_v876 pb_v1118_v876 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  clear h_v875 h_v1107 h_v1108 pb_v1107_v875 h_v1109 h_v1110 pb_v1108_v875 h_v1112 h_v1113 h_v1114 h_v1115 h_v1117
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
  have e_v1131 : v1131 = if v1130 = 1 then v1127 else v1116 := e_psel h_v1130 h_v1127 h_v1116 (of_decide_eq_true rfl)
  have h_v1132 : R 1 0 0 1 v1132 v1132 := (r_plt hl h_v966 h_v1059 (of_decide_eq_true rfl))
  clear h_v876 h_v1111 h_v1116 h_v1118 h_v1119 pb_v1118_v876 h_v1120 h_v1121 h_v1122 pb_v1119_v876 h_v1123 h_v1124 h_v1125 h_v1126 h_v1127 h_v1128 h_v1130
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
  have e_v1143 : sv v1143 = sv v1142 + sv v1142 := e_add h_v1142 h_v1142 (of_decide_eq_true rfl)
  have pb_v1140_v879 : PB 1 v1140 v879 36028797287399439 := pb_sqrt1 hl h_v879 29 36028797287399439 (of_decide_eq_true rfl)
  clear h_v1053 h_v1059 h_v1131 h_v1132 h_v1133 h_v1134 h_v1135 h_v1136 h_v1138 h_v1139 pb_v1139_v879 h_v1141 h_v1142
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
  have pb_v1151_v880 : PB 1 v1151 v880 36028797287399439 := pb_sqrt1 hl h_v880 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1155 : R 1 0 4611686017085210619 4647714815714787343 v1155 v1155 := (r_smx_pb hl 29 h_v1151 h_v880 pb_v1151_v880 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  clear h_v879 h_v1140 pb_v1140_v879 h_v1144 h_v1145 h_v1146 h_v1147 h_v1149 h_v1150 pb_v1150_v880 h_v1152 h_v1153
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
  have h_v1167 : R 1 0 0 1 v1167 v1167 := (r_sub hl (r_O hl) h_v1166 (of_decide_eq_true rfl))
  have e_v1167 : (v1167 = 1 ↔ ¬v1166 = 1) := e_not h_v1166 (of_decide_eq_true rfl)
  clear h_v880 h_v1063 h_v1069 h_v1143 h_v1148 h_v1151 h_v1154 pb_v1151_v880 h_v1155 h_v1156 h_v1157 h_v1158 h_v1159 h_v1160 h_v1162 h_v1164 h_v1166
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
  have e_v1179 : (v1179 = 1 ↔ ¬v1178 = 1) := e_not h_v1178 (of_decide_eq_true rfl)
  have h_v1180 : R 1 0 0 1 v1180 v1180 := (r_land hl h_v1176 h_v1179 (of_decide_eq_true rfl))
  clear h_v1163 h_v1165 h_v1167 h_v1168 h_v1170 h_v1172 h_v1173
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
  have h_v1192 : R 1 0 0 1 v1192 v1192 := (r_lor hl h_v1180 h_v1191 (of_decide_eq_true rfl))
  have e_v1192 : (v1192 = 1 ↔ v1180 = 1 ∨ v1191 = 1) := e_lor h_v1180 h_v1191 (of_decide_eq_true rfl)
  clear h_v1171 h_v1176 h_v1177 h_v1178 h_v1179 h_v1181 h_v1182 h_v1183 h_v1185 h_v1186 h_v1188 h_v1189 h_v1191
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
  have e_v1204 : v1204 = if v1203 = 1 then v1198 else v1200 := e_psel h_v1203 h_v1198 h_v1200 (of_decide_eq_true rfl)
  have h_v1207 : R 1 0 0 1 v1207 v1207 := (r_plt hl h_v1204 h_v1104 (of_decide_eq_true rfl))
  clear h_v1129 h_v1137 h_v1161 h_v1169 h_v1174 h_v1175 h_v1180 h_v1187 h_v1190 h_v1192 h_v1193 h_v1194 h_v1195 h_v1196 h_v1197 h_v1198 h_v1199 h_v1200 h_v1203
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
  have h_v1217 : R 1 0 4611686018427387904 4611686019501129727 v1217 v1217 := (r1_hxa hb_H1 0 (of_decide_eq_true rfl))
  have e_v1217 : sv v1217 = ((H1 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H1 0 (of_decide_eq_true rfl)
  have h_v1218 : R 1 0 0 1 v1218 v1218 := (r_plt hl h_v9 h_v1217 (of_decide_eq_true rfl))
  have e_v1218 : (v1218 = 1 ↔ sv v9 < sv v1217) := e_plt h_v9 h_v1217 (of_decide_eq_true rfl)
  have h_v1219 : R 1 0 0 1 v1219 v1219 := (r_sub hl (r_O hl) h_v1218 (of_decide_eq_true rfl))
  have e_v1219 : (v1219 = 1 ↔ ¬v1218 = 1) := e_not h_v1218 (of_decide_eq_true rfl)
  have h_t1217_1 : R 1 0 4611686018427387904 4611686018695823363 t1217.1 t1217.1 := r_sc1 hl h_v1217 (of_decide_eq_true rfl)
  have h_t1217_2 : R 1 0 4611686018158952445 4611686018695823363 t1217.2 t1217.2 := r_sc2 hl h_v1217 (of_decide_eq_true rfl)
  clear h_v1044 h_v1104 h_v1201 h_v1202 h_v1204 h_v1207 h_v1208 h_v1209 h_v1210 h_v1211 h_v1212 h_v1218
  have e_t1217_1 : sv t1217.1 = (sc28pS (scArg v1217)).1 := e_sc1 h_v1217 (of_decide_eq_true rfl)
  have e_t1217_2 : sv t1217.2 = (sc28pS (scArg v1217)).2 := e_sc2 h_v1217 (of_decide_eq_true rfl)
  have h_v1221 : R 1 0 4611686018158952441 4611686018695823359 v1221 v1221 := (r_sub hl (r_add hl h_v28 h_t1217_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1221 : sv v1221 = sv v28 + sv t1217.2 := e_add h_v28 h_t1217_2 (of_decide_eq_true rfl)
  have h_v1222 : R 1 0 0 1 v1222 v1222 := (r_plt hl h_v1221 h_v94 (of_decide_eq_true rfl))
  have e_v1222 : (v1222 = 1 ↔ sv v1221 < sv v94) := e_plt h_v1221 h_v94 (of_decide_eq_true rfl)
  have h_v1223 : R 1 0 4611686018158952441 4611686018695823359 v1223 v1223 := (r_psel hl h_v1222 h_v94 h_v1221 (of_decide_eq_true rfl))
  have e_v1223 : v1223 = if v1222 = 1 then v94 else v1221 := e_psel h_v1222 h_v94 h_v1221 (of_decide_eq_true rfl)
  have h_v1224 : R 1 0 4467570782033149952 4755801223146242048 v1224 v1224 := (r_sshl hl h_v1048 4467570782033149952 4755801223146242048 (of_decide_eq_true rfl))
  have e_v1224 : sv v1224 = sv v1048 * 2 ^ 28 := e_sshl h_v1048 4467570782033149952 4755801223146242048 (of_decide_eq_true rfl)
  have h_v1225 : R 1 0 4539628420094492609 4683743614612799479 v1225 v1225 := (r_smx hl 29 h_v1223 h_v1049 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl))
  have e_v1225 : sv v1225 = sv v1223 * sv v1049 := e_smx 29 h_v1223 h_v1049 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl)
  have h_v1226 : R 1 0 0 1 v1226 v1226 := (r_plt hl h_v1225 h_v1224 (of_decide_eq_true rfl))
  have e_v1226 : (v1226 = 1 ↔ sv v1225 < sv v1224) := e_plt h_v1225 h_v1224 (of_decide_eq_true rfl)
  have h_v1227 : R 1 0 0 1 v1227 v1227 := (r_sub hl (r_O hl) h_v1226 (of_decide_eq_true rfl))
  have e_v1227 : (v1227 = 1 ↔ ¬v1226 = 1) := e_not h_v1226 (of_decide_eq_true rfl)
  have h_v1228 : R 1 0 0 1 v1228 v1228 := (r_plt hl h_v14 h_v1217 (of_decide_eq_true rfl))
  have e_v1228 : (v1228 = 1 ↔ sv v14 < sv v1217) := e_plt h_v14 h_v1217 (of_decide_eq_true rfl)
  have h_v1229 : R 1 0 0 1 v1229 v1229 := (r_sub hl (r_O hl) h_v1228 (of_decide_eq_true rfl))
  have e_v1229 : (v1229 = 1 ↔ ¬v1228 = 1) := e_not h_v1228 (of_decide_eq_true rfl)
  have h_v1230 : R 1 0 0 1 v1230 v1230 := (r_land hl h_v1227 h_v1229 (of_decide_eq_true rfl))
  have e_v1230 : (v1230 = 1 ↔ v1227 = 1 ∧ v1229 = 1) := e_land h_v1227 h_v1229 (of_decide_eq_true rfl)
  have h_v1231 : R 1 0 0 1 v1231 v1231 := (r_lor hl h_v1219 h_v1230 (of_decide_eq_true rfl))
  have e_v1231 : (v1231 = 1 ↔ v1219 = 1 ∨ v1230 = 1) := e_lor h_v1219 h_v1230 (of_decide_eq_true rfl)
  have h_v1232 : R 1 0 4611686018427387904 4611686019501129727 v1232 v1232 := (r_psel hl h_v1231 h_v1217 h_v9 (of_decide_eq_true rfl))
  clear h_v14 h_v28 h_v1048 h_v1049 h_v1219 h_v1221 h_v1222 h_v1223 h_v1224 h_v1225 h_v1226 h_v1227 h_v1228 h_v1229 h_v1230
  have e_v1232 : v1232 = if v1231 = 1 then v1217 else v9 := e_psel h_v1231 h_v1217 h_v9 (of_decide_eq_true rfl)
  have h_v1233 : R 1 0 4611686018427387904 4611686019501129727 v1233 v1233 := (r1_hxa hb_H1 32 (of_decide_eq_true rfl))
  have e_v1233 : sv v1233 = ((H1 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H1 32 (of_decide_eq_true rfl)
  have h_v1234 : R 1 0 0 1 v1234 v1234 := (r_plt hl h_v1233 h_v20 (of_decide_eq_true rfl))
  have e_v1234 : (v1234 = 1 ↔ sv v1233 < sv v20) := e_plt h_v1233 h_v20 (of_decide_eq_true rfl)
  have h_v1235 : R 1 0 0 1 v1235 v1235 := (r_sub hl (r_O hl) h_v1234 (of_decide_eq_true rfl))
  have e_v1235 : (v1235 = 1 ↔ ¬v1234 = 1) := e_not h_v1234 (of_decide_eq_true rfl)
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
  clear h_v31 h_v1213 h_v1214 h_v1217 h_v1234 h_v1237 h_v1238 h_v1239 h_v1240 h_v1241 h_v1242
  have h_v1244 : R 1 0 0 1 v1244 v1244 := (r_lor hl h_v1235 h_v1243 (of_decide_eq_true rfl))
  have e_v1244 : (v1244 = 1 ↔ v1235 = 1 ∨ v1243 = 1) := e_lor h_v1235 h_v1243 (of_decide_eq_true rfl)
  have h_v1245 : R 1 0 4611686018427387904 4611686019501129727 v1245 v1245 := (r_psel hl h_v1244 h_v1233 h_v20 (of_decide_eq_true rfl))
  have e_v1245 : v1245 = if v1244 = 1 then v1233 else v20 := e_psel h_v1244 h_v1233 h_v20 (of_decide_eq_true rfl)
  have h_v1246 : R 1 0 4611686018427387904 4611686019501129727 v1246 v1246 := (r_psel hl h_v777 h_v1232 h_v9 (of_decide_eq_true rfl))
  have e_v1246 : v1246 = if v777 = 1 then v1232 else v9 := e_psel h_v777 h_v1232 h_v9 (of_decide_eq_true rfl)
  have h_v1247 : R 1 0 4611686018427387904 4611686019501129727 v1247 v1247 := (r_psel hl h_v777 h_v1245 h_v20 (of_decide_eq_true rfl))
  have e_v1247 : v1247 = if v777 = 1 then v1245 else v20 := e_psel h_v777 h_v1245 h_v20 (of_decide_eq_true rfl)
  have h_v1248 : R 1 0 0 1 v1248 v1248 := (r_land hl h_v777 h_v1215 (of_decide_eq_true rfl))
  have e_v1248 : (v1248 = 1 ↔ v777 = 1 ∧ v1215 = 1) := e_land h_v777 h_v1215 (of_decide_eq_true rfl)
  have h_v1251 : R 1 0 0 1 v1251 v1251 := (r_sub hl (r_O hl) h_v1248 (of_decide_eq_true rfl))
  have e_v1251 : (v1251 = 1 ↔ ¬v1248 = 1) := e_not h_v1248 (of_decide_eq_true rfl)
  have h_v1252 : R 1 0 0 1 v1252 v1252 := (r_land hl h_v819 h_v847 (of_decide_eq_true rfl))
  have e_v1252 : (v1252 = 1 ↔ v819 = 1 ∧ v847 = 1) := e_land h_v819 h_v847 (of_decide_eq_true rfl)
  have h_v1253 : R 1 0 0 1 v1253 v1253 := (r_sub hl (r_O hl) h_v1252 (of_decide_eq_true rfl))
  have e_v1253 : (v1253 = 1 ↔ ¬v1252 = 1) := e_not h_v1252 (of_decide_eq_true rfl)
  have h_v1254 : R 1 0 0 1 v1254 v1254 := (r_lor hl h_v822 h_v1253 (of_decide_eq_true rfl))
  have e_v1254 : (v1254 = 1 ↔ v822 = 1 ∨ v1253 = 1) := e_lor h_v822 h_v1253 (of_decide_eq_true rfl)
  have h_v1255 : R 1 0 0 1 v1255 v1255 := (r_land hl h_v815 h_v847 (of_decide_eq_true rfl))
  have e_v1255 : (v1255 = 1 ↔ v815 = 1 ∧ v847 = 1) := e_land h_v815 h_v847 (of_decide_eq_true rfl)
  have h_v1256 : R 1 0 0 1 v1256 v1256 := (r_lor hl h_v846 h_v1255 (of_decide_eq_true rfl))
  have e_v1256 : (v1256 = 1 ↔ v846 = 1 ∨ v1255 = 1) := e_lor h_v846 h_v1255 (of_decide_eq_true rfl)
  have h_v1257 : R 1 0 4611686018158952386 4611686018695823360 v1257 v1257 := (r_psel hl h_v1256 h_v807 h_v803 (of_decide_eq_true rfl))
  have e_v1257 : v1257 = if v1256 = 1 then v807 else v803 := e_psel h_v1256 h_v807 h_v803 (of_decide_eq_true rfl)
  have h_v1258 : R 1 0 0 1 v1258 v1258 := (r_land hl h_v819 h_v843 (of_decide_eq_true rfl))
  clear h_v20 h_v1215 h_v1232 h_v1233 h_v1235 h_v1243 h_v1245 h_v1248 h_v1252 h_v1253 h_v1255 h_v1256
  have e_v1258 : (v1258 = 1 ↔ v819 = 1 ∧ v843 = 1) := e_land h_v819 h_v843 (of_decide_eq_true rfl)
  have h_v1259 : R 1 0 0 1 v1259 v1259 := (r_lor hl h_v818 h_v1258 (of_decide_eq_true rfl))
  have e_v1259 : (v1259 = 1 ↔ v818 = 1 ∨ v1258 = 1) := e_lor h_v818 h_v1258 (of_decide_eq_true rfl)
  have h_v1260 : R 1 0 4611686018158952386 4611686018695823360 v1260 v1260 := (r_psel hl h_v1259 h_v797 h_v793 (of_decide_eq_true rfl))
  have e_v1260 : v1260 = if v1259 = 1 then v797 else v793 := e_psel h_v1259 h_v797 h_v793 (of_decide_eq_true rfl)
  have h_v1261 : R 1 0 0 1 v1261 v1261 := (r_land hl h_v818 h_v847 (of_decide_eq_true rfl))
  have e_v1261 : (v1261 = 1 ↔ v818 = 1 ∧ v847 = 1) := e_land h_v818 h_v847 (of_decide_eq_true rfl)
  have h_v1262 : R 1 0 0 1 v1262 v1262 := (r_lor hl h_v846 h_v1261 (of_decide_eq_true rfl))
  have e_v1262 : (v1262 = 1 ↔ v846 = 1 ∨ v1261 = 1) := e_lor h_v846 h_v1261 (of_decide_eq_true rfl)
  have h_v1263 : R 1 0 4611686018158952386 4611686018695823360 v1263 v1263 := (r_psel hl h_v1262 h_v803 h_v807 (of_decide_eq_true rfl))
  have e_v1263 : v1263 = if v1262 = 1 then v803 else v807 := e_psel h_v1262 h_v803 h_v807 (of_decide_eq_true rfl)
  have h_v1264 : R 1 0 0 1 v1264 v1264 := (r_land hl h_v819 h_v846 (of_decide_eq_true rfl))
  have e_v1264 : (v1264 = 1 ↔ v819 = 1 ∧ v846 = 1) := e_land h_v819 h_v846 (of_decide_eq_true rfl)
  have h_v1265 : R 1 0 0 1 v1265 v1265 := (r_lor hl h_v818 h_v1264 (of_decide_eq_true rfl))
  have e_v1265 : (v1265 = 1 ↔ v818 = 1 ∨ v1264 = 1) := e_lor h_v818 h_v1264 (of_decide_eq_true rfl)
  have h_v1266 : R 1 0 4611686018158952386 4611686018695823360 v1266 v1266 := (r_psel hl h_v1265 h_v793 h_v797 (of_decide_eq_true rfl))
  have e_v1266 : v1266 = if v1265 = 1 then v793 else v797 := e_psel h_v1265 h_v793 h_v797 (of_decide_eq_true rfl)
  have h_v1267 : R 1 0 4539628407746461696 4683743645751316228 v1267 v1267 := (r_smx hl 30 h_v1260 h_v1257 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1267 : sv v1267 = sv v1260 * sv v1257 := e_smx 30 h_v1260 h_v1257 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1268 : R 1 0 4611686018158952386 4611686018695823484 v1268 v1268 := (r_srdF hl h_v1267 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v1268 : sv v1268 = sv v1267 / 2 ^ 28 := e_srdF h_v1267 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v1269 : R 1 0 4539628407746461696 4683743645751316228 v1269 v1269 := (r_smx hl 30 h_v1266 h_v1263 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1269 : sv v1269 = sv v1266 * sv v1263 := e_smx 30 h_v1266 h_v1263 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1270 : R 1 0 4611686018158952386 4611686018695823485 v1270 v1270 := (r_srdC hl h_v1269 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v1270 : sv v1270 = -((-sv v1269) / 2 ^ 28) := e_srdC h_v1269 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  clear h_v1257 h_v1258 h_v1259 h_v1260 h_v1261 h_v1262 h_v1263 h_v1264 h_v1265 h_v1266 h_v1267 h_v1269
  have h_v1271 : R 1 0 4611686017890516805 4611686018964258878 v1271 v1271 := (r_sub hl (r_add hl h_v783 h_OFFr (of_decide_eq_true rfl)) h_v1270 (of_decide_eq_true rfl))
  have e_v1271 : sv v1271 = sv v783 - sv v1270 := e_sub h_v783 h_v1270 (of_decide_eq_true rfl)
  have h_v1272 : R 1 0 4611686017890516812 4611686018964258878 v1272 v1272 := (r_sub hl (r_add hl h_v787 h_OFFr (of_decide_eq_true rfl)) h_v1268 (of_decide_eq_true rfl))
  have e_v1272 : sv v1272 = sv v787 - sv v1268 := e_sub h_v787 h_v1268 (of_decide_eq_true rfl)
  have h_v1273 : R 1 0 0 1 v1273 v1273 := (r_plt hl h_v9 h_v1271 (of_decide_eq_true rfl))
  have e_v1273 : (v1273 = 1 ↔ sv v9 < sv v1271) := e_plt h_v9 h_v1271 (of_decide_eq_true rfl)
  have h_v1274 : R 1 0 0 1 v1274 v1274 := (r_plt hl h_v1272 h_v9 (of_decide_eq_true rfl))
  have e_v1274 : (v1274 = 1 ↔ sv v1272 < sv v9) := e_plt h_v1272 h_v9 (of_decide_eq_true rfl)
  have h_v1275 : R 1 0 4611686018427387899 4611686018695823375 v1275 v1275 := (r_psel hl h_v869 h_v439 h_v437 (of_decide_eq_true rfl))
  have e_v1275 : v1275 = if v869 = 1 then v439 else v437 := e_psel h_v869 h_v439 h_v437 (of_decide_eq_true rfl)
  have h_v1276 : R 1 0 4611686018427387899 4611686018695823375 v1276 v1276 := (r_psel hl h_v870 h_v437 h_v439 (of_decide_eq_true rfl))
  have e_v1276 : v1276 = if v870 = 1 then v437 else v439 := e_psel h_v870 h_v437 h_v439 (of_decide_eq_true rfl)
  have h_v1277 : R 1 0 4611686018427387899 4611686018695823375 v1277 v1277 := (r_psel hl h_v870 h_v439 h_v437 (of_decide_eq_true rfl))
  have e_v1277 : v1277 = if v870 = 1 then v439 else v437 := e_psel h_v870 h_v439 h_v437 (of_decide_eq_true rfl)
  have h_v1278 : R 1 0 4611686018427387899 4611686018695823375 v1278 v1278 := (r_psel hl h_v869 h_v437 h_v439 (of_decide_eq_true rfl))
  have e_v1278 : v1278 = if v869 = 1 then v437 else v439 := e_psel h_v869 h_v437 h_v439 (of_decide_eq_true rfl)
  have h_v1279 : R 1 0 4611686018427387899 4611686018695823375 v1279 v1279 := (r_psel hl h_v1273 h_v765 h_v763 (of_decide_eq_true rfl))
  have e_v1279 : v1279 = if v1273 = 1 then v765 else v763 := e_psel h_v1273 h_v765 h_v763 (of_decide_eq_true rfl)
  have h_v1280 : R 1 0 4611686018427387899 4611686018695823375 v1280 v1280 := (r_psel hl h_v1274 h_v763 h_v765 (of_decide_eq_true rfl))
  have e_v1280 : v1280 = if v1274 = 1 then v763 else v765 := e_psel h_v1274 h_v763 h_v765 (of_decide_eq_true rfl)
  have h_v1281 : R 1 0 4611686018427387899 4611686018695823375 v1281 v1281 := (r_psel hl h_v1274 h_v765 h_v763 (of_decide_eq_true rfl))
  have e_v1281 : v1281 = if v1274 = 1 then v765 else v763 := e_psel h_v1274 h_v765 h_v763 (of_decide_eq_true rfl)
  have h_v1282 : R 1 0 4611686018427387899 4611686018695823375 v1282 v1282 := (r_psel hl h_v1273 h_v763 h_v765 (of_decide_eq_true rfl))
  have e_v1282 : v1282 = if v1273 = 1 then v763 else v765 := e_psel h_v1273 h_v763 h_v765 (of_decide_eq_true rfl)
  have h_v1288 : R 1 0 4611686018427387904 4683743620518379745 v1288 v1288 := (r_smx_sq hl 29 h_v1276 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  clear h_v869 h_v870 h_v1268 h_v1270 h_v1271 h_v1272 h_v1273 h_v1274
  have e_v1288 : sv v1288 = sv v1276 * sv v1276 := e_smx_sq 29 h_v1276 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1289 : R 1 0 4611686018427387904 4611686018695823391 v1289 v1289 := (r_srdC hl h_v1288 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1289 : sv v1289 = -((-sv v1288) / 2 ^ 28) := e_srdC h_v1288 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1290 : R 1 0 4611686018427387904 4611686018964258878 v1290 v1290 := (r_sub hl (r_add hl h_v1289 h_v1289 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1290 : sv v1290 = sv v1289 + sv v1289 := e_add h_v1289 h_v1289 (of_decide_eq_true rfl)
  have h_v1291 : R 1 0 4611686018158952386 4611686018695823360 v1291 v1291 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1290 (of_decide_eq_true rfl))
  have e_v1291 : sv v1291 = sv v33 - sv v1290 := e_sub h_v33 h_v1290 (of_decide_eq_true rfl)
  have h_v1292 : R 1 0 0 1 v1292 v1292 := (r_plt hl h_v1291 h_v94 (of_decide_eq_true rfl))
  have e_v1292 : (v1292 = 1 ↔ sv v1291 < sv v94) := e_plt h_v1291 h_v94 (of_decide_eq_true rfl)
  have h_v1293 : R 1 0 4611686018158952386 4611686018695823360 v1293 v1293 := (r_psel hl h_v1292 h_v94 h_v1291 (of_decide_eq_true rfl))
  have e_v1293 : v1293 = if v1292 = 1 then v94 else v1291 := e_psel h_v1292 h_v94 h_v1291 (of_decide_eq_true rfl)
  have h_v1294 : R 1 0 4611686018427387904 4683743620518379745 v1294 v1294 := (r_smx_sq hl 29 h_v1275 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1294 : sv v1294 = sv v1275 * sv v1275 := e_smx_sq 29 h_v1275 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1295 : R 1 0 4611686018427387904 4611686018695823390 v1295 v1295 := (r_srdF hl h_v1294 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1295 : sv v1295 = sv v1294 / 2 ^ 28 := e_srdF h_v1294 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1296 : R 1 0 4611686018427387904 4611686018964258876 v1296 v1296 := (r_sub hl (r_add hl h_v1295 h_v1295 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1296 : sv v1296 = sv v1295 + sv v1295 := e_add h_v1295 h_v1295 (of_decide_eq_true rfl)
  have h_v1297 : R 1 0 4611686018158952388 4611686018695823360 v1297 v1297 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1296 (of_decide_eq_true rfl))
  have e_v1297 : sv v1297 = sv v33 - sv v1296 := e_sub h_v33 h_v1296 (of_decide_eq_true rfl)
  have h_v1298 : R 1 0 4611686018427387904 4683743620518379745 v1298 v1298 := (r_smx_sq hl 29 h_v1280 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1298 : sv v1298 = sv v1280 * sv v1280 := e_smx_sq 29 h_v1280 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1299 : R 1 0 4611686018427387904 4611686018695823391 v1299 v1299 := (r_srdC hl h_v1298 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1299 : sv v1299 = -((-sv v1298) / 2 ^ 28) := e_srdC h_v1298 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1300 : R 1 0 4611686018427387904 4611686018964258878 v1300 v1300 := (r_sub hl (r_add hl h_v1299 h_v1299 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1300 : sv v1300 = sv v1299 + sv v1299 := e_add h_v1299 h_v1299 (of_decide_eq_true rfl)
  clear h_v1289 h_v1290 h_v1291 h_v1292 h_v1295 h_v1296 h_v1299
  have h_v1301 : R 1 0 4611686018158952386 4611686018695823360 v1301 v1301 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1300 (of_decide_eq_true rfl))
  have e_v1301 : sv v1301 = sv v33 - sv v1300 := e_sub h_v33 h_v1300 (of_decide_eq_true rfl)
  have h_v1302 : R 1 0 0 1 v1302 v1302 := (r_plt hl h_v1301 h_v94 (of_decide_eq_true rfl))
  have e_v1302 : (v1302 = 1 ↔ sv v1301 < sv v94) := e_plt h_v1301 h_v94 (of_decide_eq_true rfl)
  have h_v1303 : R 1 0 4611686018158952386 4611686018695823360 v1303 v1303 := (r_psel hl h_v1302 h_v94 h_v1301 (of_decide_eq_true rfl))
  have e_v1303 : v1303 = if v1302 = 1 then v94 else v1301 := e_psel h_v1302 h_v94 h_v1301 (of_decide_eq_true rfl)
  have h_v1304 : R 1 0 4611686018427387904 4683743620518379745 v1304 v1304 := (r_smx_sq hl 29 h_v1279 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1304 : sv v1304 = sv v1279 * sv v1279 := e_smx_sq 29 h_v1279 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1305 : R 1 0 4611686018427387904 4611686018695823390 v1305 v1305 := (r_srdF hl h_v1304 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v1305 : sv v1305 = sv v1304 / 2 ^ 28 := e_srdF h_v1304 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v1306 : R 1 0 4611686018427387904 4611686018964258876 v1306 v1306 := (r_sub hl (r_add hl h_v1305 h_v1305 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1306 : sv v1306 = sv v1305 + sv v1305 := e_add h_v1305 h_v1305 (of_decide_eq_true rfl)
  have h_v1307 : R 1 0 4611686018158952388 4611686018695823360 v1307 v1307 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1306 (of_decide_eq_true rfl))
  have e_v1307 : sv v1307 = sv v33 - sv v1306 := e_sub h_v33 h_v1306 (of_decide_eq_true rfl)
  have h_v1308 : R 1 0 0 1 v1308 v1308 := (r_plt hl h_v1293 h_v9 (of_decide_eq_true rfl))
  have e_v1308 : (v1308 = 1 ↔ sv v1293 < sv v9) := e_plt h_v1293 h_v9 (of_decide_eq_true rfl)
  have h_v1309 : R 1 0 0 1 v1309 v1309 := (r_sub hl (r_O hl) h_v1308 (of_decide_eq_true rfl))
  have e_v1309 : (v1309 = 1 ↔ ¬v1308 = 1) := e_not h_v1308 (of_decide_eq_true rfl)
  have h_v1310 : R 1 0 0 1 v1310 v1310 := (r_plt hl h_v9 h_v1297 (of_decide_eq_true rfl))
  have e_v1310 : (v1310 = 1 ↔ sv v9 < sv v1297) := e_plt h_v9 h_v1297 (of_decide_eq_true rfl)
  have h_v1311 : R 1 0 0 1 v1311 v1311 := (r_sub hl (r_O hl) h_v1310 (of_decide_eq_true rfl))
  have e_v1311 : (v1311 = 1 ↔ ¬v1310 = 1) := e_not h_v1310 (of_decide_eq_true rfl)
  have h_v1312 : R 1 0 0 1 v1312 v1312 := (r_land hl h_v1308 h_v1311 (of_decide_eq_true rfl))
  have e_v1312 : (v1312 = 1 ↔ v1308 = 1 ∧ v1311 = 1) := e_land h_v1308 h_v1311 (of_decide_eq_true rfl)
  have h_v1313 : R 1 0 0 1 v1313 v1313 := (r_land hl h_v1308 h_v1310 (of_decide_eq_true rfl))
  clear h_v94 h_v1300 h_v1301 h_v1302 h_v1305 h_v1306 h_v1311
  have e_v1313 : (v1313 = 1 ↔ v1308 = 1 ∧ v1310 = 1) := e_land h_v1308 h_v1310 (of_decide_eq_true rfl)
  have h_v1314 : R 1 0 0 1 v1314 v1314 := (r_plt hl h_v1303 h_v9 (of_decide_eq_true rfl))
  have e_v1314 : (v1314 = 1 ↔ sv v1303 < sv v9) := e_plt h_v1303 h_v9 (of_decide_eq_true rfl)
  have h_v1315 : R 1 0 0 1 v1315 v1315 := (r_sub hl (r_O hl) h_v1314 (of_decide_eq_true rfl))
  have e_v1315 : (v1315 = 1 ↔ ¬v1314 = 1) := e_not h_v1314 (of_decide_eq_true rfl)
  have h_v1316 : R 1 0 0 1 v1316 v1316 := (r_plt hl h_v9 h_v1307 (of_decide_eq_true rfl))
  have e_v1316 : (v1316 = 1 ↔ sv v9 < sv v1307) := e_plt h_v9 h_v1307 (of_decide_eq_true rfl)
  have h_v1317 : R 1 0 0 1 v1317 v1317 := (r_sub hl (r_O hl) h_v1316 (of_decide_eq_true rfl))
  have e_v1317 : (v1317 = 1 ↔ ¬v1316 = 1) := e_not h_v1316 (of_decide_eq_true rfl)
  have h_v1318 : R 1 0 0 1 v1318 v1318 := (r_land hl h_v1314 h_v1317 (of_decide_eq_true rfl))
  have e_v1318 : (v1318 = 1 ↔ v1314 = 1 ∧ v1317 = 1) := e_land h_v1314 h_v1317 (of_decide_eq_true rfl)
  have h_v1319 : R 1 0 0 1 v1319 v1319 := (r_land hl h_v1314 h_v1316 (of_decide_eq_true rfl))
  have e_v1319 : (v1319 = 1 ↔ v1314 = 1 ∧ v1316 = 1) := e_land h_v1314 h_v1316 (of_decide_eq_true rfl)
  have h_v1320 : R 1 0 0 1 v1320 v1320 := (r_land hl h_v1313 h_v1319 (of_decide_eq_true rfl))
  have e_v1320 : (v1320 = 1 ↔ v1313 = 1 ∧ v1319 = 1) := e_land h_v1313 h_v1319 (of_decide_eq_true rfl)
  have h_v1321 : R 1 0 0 1 v1321 v1321 := (r_sub hl (r_O hl) h_v1320 (of_decide_eq_true rfl))
  have e_v1321 : (v1321 = 1 ↔ ¬v1320 = 1) := e_not h_v1320 (of_decide_eq_true rfl)
  have h_v1322 : R 1 0 0 1 v1322 v1322 := (r_lor hl h_v822 h_v1321 (of_decide_eq_true rfl))
  have e_v1322 : (v1322 = 1 ↔ v822 = 1 ∨ v1321 = 1) := e_lor h_v822 h_v1321 (of_decide_eq_true rfl)
  have h_v1323 : R 1 0 0 1 v1323 v1323 := (r_land hl h_v1309 h_v1319 (of_decide_eq_true rfl))
  have e_v1323 : (v1323 = 1 ↔ v1309 = 1 ∧ v1319 = 1) := e_land h_v1309 h_v1319 (of_decide_eq_true rfl)
  have h_v1324 : R 1 0 0 1 v1324 v1324 := (r_lor hl h_v1318 h_v1323 (of_decide_eq_true rfl))
  have e_v1324 : (v1324 = 1 ↔ v1318 = 1 ∨ v1323 = 1) := e_lor h_v1318 h_v1323 (of_decide_eq_true rfl)
  have h_v1325 : R 1 0 4611686018158952386 4611686018695823360 v1325 v1325 := (r_psel hl h_v1324 h_v1297 h_v1293 (of_decide_eq_true rfl))
  have e_v1325 : v1325 = if v1324 = 1 then v1297 else v1293 := e_psel h_v1324 h_v1297 h_v1293 (of_decide_eq_true rfl)
  clear h_v9 h_v1293 h_v1297 h_v1308 h_v1309 h_v1310 h_v1314 h_v1316 h_v1317 h_v1318 h_v1319 h_v1320 h_v1321 h_v1323 h_v1324
  have h_v1326 : R 1 0 0 1 v1326 v1326 := (r_land hl h_v1313 h_v1315 (of_decide_eq_true rfl))
  have e_v1326 : (v1326 = 1 ↔ v1313 = 1 ∧ v1315 = 1) := e_land h_v1313 h_v1315 (of_decide_eq_true rfl)
  have h_v1327 : R 1 0 0 1 v1327 v1327 := (r_lor hl h_v1312 h_v1326 (of_decide_eq_true rfl))
  have e_v1327 : (v1327 = 1 ↔ v1312 = 1 ∨ v1326 = 1) := e_lor h_v1312 h_v1326 (of_decide_eq_true rfl)
  have h_v1328 : R 1 0 4611686018158952386 4611686018695823360 v1328 v1328 := (r_psel hl h_v1327 h_v1307 h_v1303 (of_decide_eq_true rfl))
  have e_v1328 : v1328 = if v1327 = 1 then v1307 else v1303 := e_psel h_v1327 h_v1307 h_v1303 (of_decide_eq_true rfl)
  have h_v1335 : R 1 0 4539628407746461696 4683743645751316228 v1335 v1335 := (r_smx hl 30 h_v1328 h_v1325 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1335 : sv v1335 = sv v1328 * sv v1325 := e_smx 30 h_v1328 h_v1325 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1336 : R 1 0 4611686018158952386 4611686018695823484 v1336 v1336 := (r_srdF hl h_v1335 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v1336 : sv v1336 = sv v1335 / 2 ^ 28 := e_srdF h_v1335 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v1340 : R 1 0 4611686017890516812 4611686018964258878 v1340 v1340 := (r_sub hl (r_add hl h_v807 h_OFFr (of_decide_eq_true rfl)) h_v1336 (of_decide_eq_true rfl))
  have e_v1340 : sv v1340 = sv v807 - sv v1336 := e_sub h_v807 h_v1336 (of_decide_eq_true rfl)
  have h_v1341 : R 1 0 4611686010374323999 4683743612465315840 v1341 v1341 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v1294 (of_decide_eq_true rfl))
  have e_v1341 : sv v1341 = sv v939 - sv v1294 := e_sub h_v939 h_v1294 (of_decide_eq_true rfl)
  have h_v1342 : R 1 0 4611686018427387904 4611686018695823360 v1342 v1342 := (r_psqrt hl h_v1341 (of_decide_eq_true rfl))
  have e_v1342 : sv v1342 = ((Nat.sqrt (v1341 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1341 (of_decide_eq_true rfl)
  have h_v1343 : R 1 0 4611686018427387905 4611686018695823361 v1343 v1343 := (r_sub hl (r_add hl h_v104 h_v1342 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1343 : sv v1343 = sv v104 + sv v1342 := e_add h_v104 h_v1342 (of_decide_eq_true rfl)
  have pb_v1342_v1275 : PB 1 v1342 v1275 36028797018963968 := pb_sqrt hl h_v1275 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1344 : R 1 0 4611686017085210624 4647714815446351872 v1344 v1344 := (r_smx_pb hl 29 h_v1342 h_v1275 pb_v1342_v1275 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1344 : sv v1344 = sv v1342 * sv v1275 := e_smx_pb 29 h_v1342 h_v1275 pb_v1342_v1275 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1345 : R 1 0 4611686018427387899 4611686018561605632 v1345 v1345 := (r_srdF hl h_v1344 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1345 : sv v1345 = sv v1344 / 2 ^ 28 := e_srdF h_v1344 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1346 : R 1 0 4611686018427387894 4611686018695823360 v1346 v1346 := (r_sub hl (r_add hl h_v1345 h_v1345 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1346 : sv v1346 = sv v1345 + sv v1345 := e_add h_v1345 h_v1345 (of_decide_eq_true rfl)
  clear h_v1303 h_v1307 h_v1312 h_v1313 h_v1315 h_v1325 h_v1326 h_v1327 h_v1328 h_v1335 h_v1336 h_v1341 h_v1342 pb_v1342_v1275 h_v1344 h_v1345
  have pb_v1343_v1275 : PB 1 v1343 v1275 36028797287399439 := pb_sqrt1 hl h_v1275 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1347 : R 1 0 4611686017085210619 4647714815714787343 v1347 v1347 := (r_smx_pb hl 29 h_v1343 h_v1275 pb_v1343_v1275 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1347 : sv v1347 = sv v1343 * sv v1275 := e_smx_pb 29 h_v1343 h_v1275 pb_v1343_v1275 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1348 : R 1 0 4611686018427387899 4611686018561605634 v1348 v1348 := (r_srdC hl h_v1347 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1348 : sv v1348 = -((-sv v1347) / 2 ^ 28) := e_srdC h_v1347 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1349 : R 1 0 4611686018427387894 4611686018695823364 v1349 v1349 := (r_sub hl (r_add hl h_v1348 h_v1348 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1349 : sv v1349 = sv v1348 + sv v1348 := e_add h_v1348 h_v1348 (of_decide_eq_true rfl)
  have h_v1350 : R 1 0 0 1 v1350 v1350 := (r_plt hl h_v1349 h_v33 (of_decide_eq_true rfl))
  have e_v1350 : (v1350 = 1 ↔ sv v1349 < sv v33) := e_plt h_v1349 h_v33 (of_decide_eq_true rfl)
  have h_v1351 : R 1 0 4611686018427387894 4611686018695823364 v1351 v1351 := (r_psel hl h_v1350 h_v1349 h_v33 (of_decide_eq_true rfl))
  have e_v1351 : v1351 = if v1350 = 1 then v1349 else v33 := e_psel h_v1350 h_v1349 h_v33 (of_decide_eq_true rfl)
  have h_v1352 : R 1 0 4611686010374323999 4683743612465315840 v1352 v1352 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v1288 (of_decide_eq_true rfl))
  have e_v1352 : sv v1352 = sv v939 - sv v1288 := e_sub h_v939 h_v1288 (of_decide_eq_true rfl)
  have h_v1353 : R 1 0 4611686018427387904 4611686018695823360 v1353 v1353 := (r_psqrt hl h_v1352 (of_decide_eq_true rfl))
  have e_v1353 : sv v1353 = ((Nat.sqrt (v1352 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1352 (of_decide_eq_true rfl)
  have h_v1354 : R 1 0 4611686018427387905 4611686018695823361 v1354 v1354 := (r_sub hl (r_add hl h_v104 h_v1353 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1354 : sv v1354 = sv v104 + sv v1353 := e_add h_v104 h_v1353 (of_decide_eq_true rfl)
  have pb_v1353_v1276 : PB 1 v1353 v1276 36028797018963968 := pb_sqrt hl h_v1276 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1355 : R 1 0 4611686017085210624 4647714815446351872 v1355 v1355 := (r_smx_pb hl 29 h_v1353 h_v1276 pb_v1353_v1276 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1355 : sv v1355 = sv v1353 * sv v1276 := e_smx_pb 29 h_v1353 h_v1276 pb_v1353_v1276 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1356 : R 1 0 4611686018427387899 4611686018561605632 v1356 v1356 := (r_srdF hl h_v1355 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1356 : sv v1356 = sv v1355 / 2 ^ 28 := e_srdF h_v1355 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1357 : R 1 0 4611686018427387894 4611686018695823360 v1357 v1357 := (r_sub hl (r_add hl h_v1356 h_v1356 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1357 : sv v1357 = sv v1356 + sv v1356 := e_add h_v1356 h_v1356 (of_decide_eq_true rfl)
  have pb_v1354_v1276 : PB 1 v1354 v1276 36028797287399439 := pb_sqrt1 hl h_v1276 29 36028797287399439 (of_decide_eq_true rfl)
  clear h_v1275 h_v1343 pb_v1343_v1275 h_v1347 h_v1348 h_v1349 h_v1350 h_v1352 h_v1353 pb_v1353_v1276 h_v1355 h_v1356
  have h_v1358 : R 1 0 4611686017085210619 4647714815714787343 v1358 v1358 := (r_smx_pb hl 29 h_v1354 h_v1276 pb_v1354_v1276 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1358 : sv v1358 = sv v1354 * sv v1276 := e_smx_pb 29 h_v1354 h_v1276 pb_v1354_v1276 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1359 : R 1 0 4611686018427387899 4611686018561605634 v1359 v1359 := (r_srdC hl h_v1358 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1359 : sv v1359 = -((-sv v1358) / 2 ^ 28) := e_srdC h_v1358 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1360 : R 1 0 4611686018427387894 4611686018695823364 v1360 v1360 := (r_sub hl (r_add hl h_v1359 h_v1359 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1360 : sv v1360 = sv v1359 + sv v1359 := e_add h_v1359 h_v1359 (of_decide_eq_true rfl)
  have h_v1361 : R 1 0 0 1 v1361 v1361 := (r_plt hl h_v1360 h_v33 (of_decide_eq_true rfl))
  have e_v1361 : (v1361 = 1 ↔ sv v1360 < sv v33) := e_plt h_v1360 h_v33 (of_decide_eq_true rfl)
  have h_v1362 : R 1 0 4611686018427387894 4611686018695823364 v1362 v1362 := (r_psel hl h_v1361 h_v1360 h_v33 (of_decide_eq_true rfl))
  have e_v1362 : v1362 = if v1361 = 1 then v1360 else v33 := e_psel h_v1361 h_v1360 h_v33 (of_decide_eq_true rfl)
  have h_v1363 : R 1 0 0 1 v1363 v1363 := (r_plt hl h_v1346 h_v1357 (of_decide_eq_true rfl))
  have e_v1363 : (v1363 = 1 ↔ sv v1346 < sv v1357) := e_plt h_v1346 h_v1357 (of_decide_eq_true rfl)
  have h_v1364 : R 1 0 4611686018427387894 4611686018695823360 v1364 v1364 := (r_psel hl h_v1363 h_v1346 h_v1357 (of_decide_eq_true rfl))
  have e_v1364 : v1364 = if v1363 = 1 then v1346 else v1357 := e_psel h_v1363 h_v1346 h_v1357 (of_decide_eq_true rfl)
  have h_v1365 : R 1 0 0 1 v1365 v1365 := (r_plt hl h_v1351 h_v1362 (of_decide_eq_true rfl))
  have e_v1365 : (v1365 = 1 ↔ sv v1351 < sv v1362) := e_plt h_v1351 h_v1362 (of_decide_eq_true rfl)
  have h_v1366 : R 1 0 4611686018427387894 4611686018695823364 v1366 v1366 := (r_psel hl h_v1365 h_v1362 h_v1351 (of_decide_eq_true rfl))
  have e_v1366 : v1366 = if v1365 = 1 then v1362 else v1351 := e_psel h_v1365 h_v1362 h_v1351 (of_decide_eq_true rfl)
  have h_v1367 : R 1 0 0 1 v1367 v1367 := (r_plt hl h_v966 h_v1294 (of_decide_eq_true rfl))
  have e_v1367 : (v1367 = 1 ↔ sv v966 < sv v1294) := e_plt h_v966 h_v1294 (of_decide_eq_true rfl)
  have h_v1368 : R 1 0 0 1 v1368 v1368 := (r_sub hl (r_O hl) h_v1367 (of_decide_eq_true rfl))
  have e_v1368 : (v1368 = 1 ↔ ¬v1367 = 1) := e_not h_v1367 (of_decide_eq_true rfl)
  have h_v1369 : R 1 0 0 1 v1369 v1369 := (r_plt hl h_v1288 h_v966 (of_decide_eq_true rfl))
  have e_v1369 : (v1369 = 1 ↔ sv v1288 < sv v966) := e_plt h_v1288 h_v966 (of_decide_eq_true rfl)
  have h_v1370 : R 1 0 0 1 v1370 v1370 := (r_sub hl (r_O hl) h_v1369 (of_decide_eq_true rfl))
  clear h_v966 h_v1276 h_v1288 h_v1294 h_v1346 h_v1351 h_v1354 h_v1357 pb_v1354_v1276 h_v1358 h_v1359 h_v1360 h_v1361 h_v1362 h_v1363 h_v1365 h_v1367
  have e_v1370 : (v1370 = 1 ↔ ¬v1369 = 1) := e_not h_v1369 (of_decide_eq_true rfl)
  have h_v1371 : R 1 0 0 1 v1371 v1371 := (r_land hl h_v1368 h_v1370 (of_decide_eq_true rfl))
  have e_v1371 : (v1371 = 1 ↔ v1368 = 1 ∧ v1370 = 1) := e_land h_v1368 h_v1370 (of_decide_eq_true rfl)
  have h_v1372 : R 1 0 4611686018427387894 4611686018695823364 v1372 v1372 := (r_psel hl h_v1371 h_v33 h_v1366 (of_decide_eq_true rfl))
  have e_v1372 : v1372 = if v1371 = 1 then v33 else v1366 := e_psel h_v1371 h_v33 h_v1366 (of_decide_eq_true rfl)
  have h_v1373 : R 1 0 4611686010374323999 4683743612465315840 v1373 v1373 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v1304 (of_decide_eq_true rfl))
  have e_v1373 : sv v1373 = sv v939 - sv v1304 := e_sub h_v939 h_v1304 (of_decide_eq_true rfl)
  have h_v1374 : R 1 0 4611686018427387904 4611686018695823360 v1374 v1374 := (r_psqrt hl h_v1373 (of_decide_eq_true rfl))
  have e_v1374 : sv v1374 = ((Nat.sqrt (v1373 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1373 (of_decide_eq_true rfl)
  have h_v1375 : R 1 0 4611686018427387905 4611686018695823361 v1375 v1375 := (r_sub hl (r_add hl h_v104 h_v1374 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1375 : sv v1375 = sv v104 + sv v1374 := e_add h_v104 h_v1374 (of_decide_eq_true rfl)
  have pb_v1374_v1279 : PB 1 v1374 v1279 36028797018963968 := pb_sqrt hl h_v1279 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1376 : R 1 0 4611686017085210624 4647714815446351872 v1376 v1376 := (r_smx_pb hl 29 h_v1374 h_v1279 pb_v1374_v1279 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1376 : sv v1376 = sv v1374 * sv v1279 := e_smx_pb 29 h_v1374 h_v1279 pb_v1374_v1279 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1377 : R 1 0 4611686018427387899 4611686018561605632 v1377 v1377 := (r_srdF hl h_v1376 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1377 : sv v1377 = sv v1376 / 2 ^ 28 := e_srdF h_v1376 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1378 : R 1 0 4611686018427387894 4611686018695823360 v1378 v1378 := (r_sub hl (r_add hl h_v1377 h_v1377 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1378 : sv v1378 = sv v1377 + sv v1377 := e_add h_v1377 h_v1377 (of_decide_eq_true rfl)
  have pb_v1375_v1279 : PB 1 v1375 v1279 36028797287399439 := pb_sqrt1 hl h_v1279 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1379 : R 1 0 4611686017085210619 4647714815714787343 v1379 v1379 := (r_smx_pb hl 29 h_v1375 h_v1279 pb_v1375_v1279 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1379 : sv v1379 = sv v1375 * sv v1279 := e_smx_pb 29 h_v1375 h_v1279 pb_v1375_v1279 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1380 : R 1 0 4611686018427387899 4611686018561605634 v1380 v1380 := (r_srdC hl h_v1379 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1380 : sv v1380 = -((-sv v1379) / 2 ^ 28) := e_srdC h_v1379 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1381 : R 1 0 4611686018427387894 4611686018695823364 v1381 v1381 := (r_sub hl (r_add hl h_v1380 h_v1380 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1381 : sv v1381 = sv v1380 + sv v1380 := e_add h_v1380 h_v1380 (of_decide_eq_true rfl)
  clear h_v1279 h_v1366 h_v1368 h_v1369 h_v1370 h_v1371 h_v1373 h_v1374 h_v1375 pb_v1374_v1279 h_v1376 h_v1377 pb_v1375_v1279 h_v1379 h_v1380
  have h_v1382 : R 1 0 0 1 v1382 v1382 := (r_plt hl h_v1381 h_v33 (of_decide_eq_true rfl))
  have e_v1382 : (v1382 = 1 ↔ sv v1381 < sv v33) := e_plt h_v1381 h_v33 (of_decide_eq_true rfl)
  have h_v1383 : R 1 0 4611686018427387894 4611686018695823364 v1383 v1383 := (r_psel hl h_v1382 h_v1381 h_v33 (of_decide_eq_true rfl))
  have e_v1383 : v1383 = if v1382 = 1 then v1381 else v33 := e_psel h_v1382 h_v1381 h_v33 (of_decide_eq_true rfl)
  have h_v1384 : R 1 0 4611686010374323999 4683743612465315840 v1384 v1384 := (r_sub hl (r_add hl h_v939 h_OFFr (of_decide_eq_true rfl)) h_v1298 (of_decide_eq_true rfl))
  have e_v1384 : sv v1384 = sv v939 - sv v1298 := e_sub h_v939 h_v1298 (of_decide_eq_true rfl)
  have h_v1385 : R 1 0 4611686018427387904 4611686018695823360 v1385 v1385 := (r_psqrt hl h_v1384 (of_decide_eq_true rfl))
  have e_v1385 : sv v1385 = ((Nat.sqrt (v1384 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1384 (of_decide_eq_true rfl)
  have h_v1386 : R 1 0 4611686018427387905 4611686018695823361 v1386 v1386 := (r_sub hl (r_add hl h_v104 h_v1385 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1386 : sv v1386 = sv v104 + sv v1385 := e_add h_v104 h_v1385 (of_decide_eq_true rfl)
  have pb_v1385_v1280 : PB 1 v1385 v1280 36028797018963968 := pb_sqrt hl h_v1280 29 36028797018963968 (of_decide_eq_true rfl)
  have pb_v1386_v1280 : PB 1 v1386 v1280 36028797287399439 := pb_sqrt1 hl h_v1280 29 36028797287399439 (of_decide_eq_true rfl)
  exact fun _ k => k e_v838 e_v839 e_v840 e_v841 e_v842 h_v843 e_v843 e_v844 e_v845 h_v846 e_v846 h_v847 e_v847 e_v848 e_v849 h_v850 e_v850 e_v851 e_v852 e_v853 e_v854 e_v855 e_v856 e_v857 e_v858 e_v859 e_v860 e_v861 e_v862 e_v863 e_v864 e_v865 e_v866 e_v867 e_v868 e_v869 e_v870 e_v871 e_v872 e_v873 e_v874 e_v875 e_v876 e_v877 e_v878 e_v879 e_v880 e_v886 e_v887 e_v888 e_v889 e_v890 e_v891 e_v892 e_v893 e_v894 e_v895 e_v896 e_v897 e_v898 e_v899 e_v900 e_v901 e_v902 e_v903 e_v904 e_v905 e_v906 e_v907 e_v908 e_v909 e_v910 e_v911 e_v912 e_v913 e_v914 e_v915 e_v916 e_v917 e_v918 e_v919 h_v920 e_v920 e_v921 e_v922 e_v923 e_v924 e_v925 e_v926 e_v933 e_v934 e_v938 e_v939 e_v940 e_v941 e_v942 e_v943 e_v944 e_v945 e_v946 e_v947 e_v948 e_v949 e_v950 e_v951 e_v952 e_v953 e_v954 e_v955 e_v956 e_v957 e_v958 e_v959 e_v960 e_v961 e_v962 e_v963 e_v964 e_v965 e_v966 e_v967 e_v968 e_v969 e_v970 e_v971 e_v972 e_v973 e_v974 e_v975 e_v976 e_v977 e_v978 e_v979 e_v980 e_v981 e_v982 e_v983 e_v984 e_v985 e_v986 e_v987 e_v988 e_v989 e_v990 e_v991 e_v992 e_v993 e_v994 e_v995 e_v996 e_v997 e_v998 e_v999 e_v1000 e_v1001 e_v1002 e_v1003 e_v1004 e_v1005 e_v1006 e_v1007 e_v1008 e_v1009 e_v1010 e_v1011 e_v1012 e_v1013 e_v1014 e_v1015 e_v1016 e_v1017 e_v1018 h_v1019 e_v1019 e_v1020 e_v1021 e_v1022 e_v1023 e_v1024 e_v1025 e_v1026 e_v1027 e_v1028 e_v1029 e_v1030 e_v1031 e_v1032 e_v1033 e_v1034 e_v1035 e_v1036 e_v1037 e_v1040 e_v1041 e_v1042 e_v1043 e_v1044 e_v1045 e_v1046 e_v1047 e_v1048 e_v1049 e_v1053 e_v1054 e_v1055 e_v1056 e_v1057 e_v1058 e_v1059 e_v1060 e_v1061 e_v1062 e_v1063 e_v1064 e_v1065 e_v1066 e_v1067 e_v1068 e_v1069 e_v1070 e_v1071 e_v1072 e_v1073 e_v1075 e_v1076 e_v1077 e_v1078 e_v1079 e_v1081 e_v1082 e_v1083 e_v1084 e_v1085 e_v1086 h_v1087 e_v1087 e_v1094 e_v1095 e_v1096 e_v1097 e_v1098 e_v1099 e_v1102 e_v1103 e_v1104 e_v1106 e_v1107 e_v1108 e_v1109 e_v1110 e_v1111 e_v1112 e_v1113 e_v1114 e_v1115 e_v1116 e_v1117 e_v1118 e_v1119 e_v1120 e_v1121 e_v1122 e_v1123 e_v1124 e_v1125 e_v1126 e_v1127 e_v1128 e_v1129 e_v1130 e_v1131 e_v1132 e_v1133 e_v1134 e_v1135 e_v1136 e_v1137 e_v1138 e_v1139 e_v1140 e_v1141 e_v1142 e_v1143 e_v1144 e_v1145 e_v1146 e_v1147 e_v1148 e_v1149 e_v1150 e_v1151 e_v1152 e_v1153 e_v1154 e_v1155 e_v1156 e_v1157 e_v1158 e_v1159 e_v1160 e_v1161 e_v1162 e_v1163 e_v1164 e_v1165 e_v1166 e_v1167 e_v1168 e_v1169 e_v1170 e_v1171 e_v1172 e_v1173 e_v1174 e_v1175 e_v1176 e_v1177 e_v1178 e_v1179 e_v1180 e_v1181 e_v1182 e_v1183 h_v1184 e_v1184 e_v1185 e_v1186 e_v1187 e_v1188 e_v1189 e_v1190 e_v1191 e_v1192 e_v1193 e_v1194 e_v1195 e_v1196 e_v1197 e_v1198 e_v1199 e_v1200 e_v1201 e_v1202 e_v1203 e_v1204 e_v1207 e_v1208 e_v1209 e_v1210 e_v1211 e_v1212 e_v1213 e_v1214 e_v1215 e_v1217 e_v1218 e_v1219 h_t1217_1 h_t1217_2 e_t1217_1 e_t1217_2 e_v1221 e_v1222 e_v1223 e_v1224 e_v1225 e_v1226 e_v1227 e_v1228 e_v1229 e_v1230 h_v1231 e_v1231 e_v1232 e_v1233 e_v1234 e_v1235 h_t1233_1 h_t1233_2 e_t1233_1 e_t1233_2 e_v1237 e_v1238 e_v1239 e_v1240 e_v1241 e_v1242 e_v1243 h_v1244 e_v1244 e_v1245 h_v1246 e_v1246 h_v1247 e_v1247 e_v1248 h_v1251 e_v1251 e_v1252 e_v1253 h_v1254 e_v1254 e_v1255 e_v1256 e_v1257 e_v1258 e_v1259 e_v1260 e_v1261 e_v1262 e_v1263 e_v1264 e_v1265 e_v1266 e_v1267 e_v1268 e_v1269 e_v1270 e_v1271 e_v1272 e_v1273 e_v1274 e_v1275 e_v1276 h_v1277 e_v1277 h_v1278 e_v1278 e_v1279 h_v1280 e_v1280 h_v1281 e_v1281 h_v1282 e_v1282 e_v1288 e_v1289 e_v1290 e_v1291 e_v1292 e_v1293 e_v1294 e_v1295 e_v1296 e_v1297 h_v1298 e_v1298 e_v1299 e_v1300 e_v1301 e_v1302 e_v1303 h_v1304 e_v1304 e_v1305 e_v1306 e_v1307 e_v1308 e_v1309 e_v1310 e_v1311 e_v1312 e_v1313 e_v1314 e_v1315 e_v1316 e_v1317 e_v1318 e_v1319 e_v1320 e_v1321 h_v1322 e_v1322 e_v1323 e_v1324 e_v1325 e_v1326 e_v1327 e_v1328 e_v1335 e_v1336 h_v1340 e_v1340 e_v1341 e_v1342 e_v1343 e_v1344 e_v1345 e_v1346 e_v1347 e_v1348 e_v1349 e_v1350 e_v1351 e_v1352 e_v1353 e_v1354 e_v1355 e_v1356 e_v1357 e_v1358 e_v1359 e_v1360 e_v1361 e_v1362 e_v1363 h_v1364 e_v1364 e_v1365 e_v1366 e_v1367 e_v1368 e_v1369 e_v1370 e_v1371 h_v1372 e_v1372 e_v1373 e_v1374 e_v1375 e_v1376 e_v1377 h_v1378 e_v1378 e_v1379 e_v1380 e_v1381 e_v1382 h_v1383 e_v1383 e_v1384 h_v1385 e_v1385 h_v1386 e_v1386 pb_v1385_v1280 pb_v1386_v1280

end Tammes15.D3Trig
