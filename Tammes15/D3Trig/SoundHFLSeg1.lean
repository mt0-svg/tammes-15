import Tammes15.D3Trig.Prog.HFL
import Tammes15.D3Prog.Sem

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progHFL_seg1 (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (hb_H4 : H4 < 2 ^ 64) (v13 : ℕ) (v29 : ℕ) (v41 : ℕ) (v63 : ℕ) (v66 : ℕ) (v67 : ℕ) (v100 : ℕ) (v101 : ℕ) (v110 : ℕ) (v117 : ℕ) (v148 : ℕ) (v149 : ℕ) (v479 : ℕ) (v480 : ℕ) (v647 : ℕ) (v651 : ℕ) (v658 : ℕ) (v663 : ℕ) (v665 : ℕ) (v668 : ℕ) (v672 : ℕ) (v673 : ℕ) (h_v13 : R 1 0 0 1 v13 v13) (h_v29 : R 1 0 4611686018427387900 4611686018695823359 v29 v29) (h_v41 : R 1 0 4611686018427387908 4611686018695823367 v41 v41) (h_v63 : R 1 0 0 1 v63 v63) (h_v66 : R 1 0 0 1 v66 v66) (h_v67 : R 1 0 0 1 v67 v67) (h_v100 : R 1 0 4611686018427387899 4611686018695823374 v100 v100) (h_v101 : R 1 0 4611686018427387900 4611686018695823375 v101 v101) (h_v110 : R 1 0 4611686018158952441 4611686018695823359 v110 v110) (h_v117 : R 1 0 4611686018158952449 4611686018695823367 v117 v117) (h_v148 : R 1 0 0 1 v148 v148) (h_v149 : R 1 0 0 1 v149 v149) (h_v479 : R 1 0 4611686018427387899 4611686018695823374 v479 v479) (h_v480 : R 1 0 4611686018427387900 4611686018695823375 v480 v480) (h_v647 : R 1 0 4611686018158952449 4611686018695823367 v647 v647) (h_v651 : R 1 0 4611686018427387900 4611686018695823359 v651 v651) (h_v658 : R 1 0 4611686018427387908 4611686018695823367 v658 v658) (h_v663 : R 1 0 0 1 v663 v663) (h_v665 : R 1 0 0 1 v665 v665) (h_v668 : R 1 0 4611686018158952441 4611686018695823367 v668 v668) (h_v672 : R 1 0 4611686018427387900 4611686018695823367 v672 v672) (h_v673 : R 1 0 0 1 v673 v673) :
    let OFFr := Nat.mul 1 4611686018427387904
    let H61r := Nat.mul 1 2305843009213693952
    let v7 := ix 1 F3 32
    let v9 := Nat.mul 1 4611686019270702761
    let v19 := Nat.mul 1 4611686018427387903
    let v28 := Nat.mul 1 4611686018427387900
    let v31 := Nat.mul 1 4611686018427387908
    let v33 := Nat.mul 1 4611686018695823360
    let v36 := Nat.mul 1 4611686018849045334
    let v38 := Nat.mul 1 4611686018849045331
    let v61 := Nat.mul 1 4611686018427387904
    let v105 := Nat.mul 1 4611686018158952448
    let v115 := Nat.mul 1 4611686018427387905
    let v216 := Nat.mul 1 4611686018849045332
    let v223 := Nat.mul 1 4611686018849045333
    let v674 := Nat.lor v663 v673
    let v675 := psel (pmask v674) v110 v117
    let v676 := Nat.land v149 v663
    let v677 := Nat.lor v148 v676
    let v678 := psel (pmask v677) v651 v658
    let v679 := smx 29 1 v672 v668
    let v680 := srdF 1 v679
    let v681 := smx 29 1 v678 v675
    let v682 := srdC 1 v681
    let v683 := smx 29 1 v651 v117
    let v684 := srdF 1 v683
    let v685 := smx 29 1 v651 v110
    let v686 := srdC 1 v685
    let v687 := plt 1 v680 v684
    let v688 := psel (pmask v687) v680 v684
    let v689 := plt 1 v682 v686
    let v690 := psel (pmask v689) v686 v682
    let v691 := psel (pmask v665) v688 v680
    let v692 := psel (pmask v665) v690 v682
    let v693 := plt 1 v61 v691
    let v694 := Nat.sub 1 v693
    let v697 := plt 1 v647 v61
    let v698 := psel (pmask v697) v692 v691
    let v740 := Nat.sub (Nat.add v61 OFFr) v647
    let v741 := psel (pmask v697) v740 v647
    let v742 := hxa 1 H1 32
    let t742 := sc28u 1 v742
    let v744 := Nat.sub (Nat.add v28 t742.2) OFFr
    let v745 := plt 1 v744 v105
    let v746 := psel (pmask v745) v105 v744
    let v747 := Nat.sub (Nat.add v31 t742.2) OFFr
    let v748 := plt 1 v747 v33
    let v749 := psel (pmask v748) v747 v33
    let v751 := Nat.sub (Nat.add v31 t742.1) OFFr
    let v752 := plt 1 v751 v33
    let v753 := psel (pmask v752) v751 v33
    let v754 := Nat.sub (Nat.add v28 t742.1) OFFr
    let v755 := psel (pmask v697) v746 v749
    let v756 := psel (pmask v697) v753 v754
    let v757 := smx 29 1 v698 v756
    let v758 := smx 29 1 v755 v741
    let v759 := plt 1 v758 v757
    let v760 := Nat.sub 1 v759
    let v761 := plt 1 v757 v758
    let v762 := Nat.sub 1 v761
    let v763 := plt 1 v61 v742
    let v764 := Nat.sub 1 v763
    let v765 := plt 1 v216 v742
    let v766 := Nat.sub 1 v765
    let v767 := plt 1 v19 v746
    let v768 := Nat.land v760 v767
    let v769 := Nat.land v766 v768
    let v770 := Nat.lor v764 v769
    let v771 := plt 1 v742 v223
    let v772 := Nat.sub 1 v771
    let v773 := Nat.lor v762 v772
    let v774 := Nat.land v697 v770
    let v775 := Nat.sub 1 v697
    let v776 := Nat.land v773 v775
    let v777 := Nat.lor v774 v776
    let v778 := Nat.sub (Nat.add v61 OFFr) v742
    let v779 := psel (pmask v697) v778 v742
    let v780 := psel (pmask v777) v779 v223
    let v782 := psel (pmask v694) v223 v780
    let v783 := Nat.add (pshr1 1 v7) H61r
    let v784 := Nat.add (pshr1 1 (Nat.add v7 1)) H61r
    let v785 := psel (pmask v13) v784 v223
    let v786 := plt 1 v19 v783
    let v787 := plt 1 v9 v785
    let v788 := Nat.sub 1 v787
    let v789 := Nat.land v786 v788
    let t783 := sc28u 1 v783
    let t785 := sc28u 1 v785
    let v792 := plt 1 t783.1 t785.1
    let v793 := psel (pmask v792) t783.1 t785.1
    let v794 := Nat.sub (Nat.add v28 v793) OFFr
    let v795 := psel (pmask v792) t785.1 t783.1
    let v796 := Nat.sub (Nat.add v31 v795) OFFr
    let v797 := plt 1 v796 v33
    let v798 := psel (pmask v797) v796 v33
    let v799 := plt 1 v783 v36
    let v800 := plt 1 v38 v785
    let v801 := Nat.land v799 v800
    let v802 := psel (pmask v801) v33 v798
    let v803 := plt 1 v794 v61
    let v805 := plt 1 v61 v802
    let v806 := Nat.sub 1 v805
    let v807 := Nat.land v803 v806
    let v808 := Nat.land v803 v805
    let v809 := Nat.land v67 v808
    let v810 := Nat.land v63 v808
    let v811 := Nat.lor v807 v810
    let v812 := psel (pmask v811) v41 v29
    let v813 := Nat.sub 1 v807
    let v814 := Nat.land v67 v813
    let v815 := Nat.lor v66 v814
    let v816 := psel (pmask v815) v802 v794
    let v817 := Nat.land v66 v808
    let v818 := Nat.lor v807 v817
    let v819 := psel (pmask v818) v29 v41
    let v820 := Nat.land v67 v807
    let v821 := Nat.lor v66 v820
    let v822 := psel (pmask v821) v794 v802
    let v823 := smx 29 1 v816 v812
    let v824 := srdF 1 v823
    let v825 := smx 29 1 v822 v819
    let v826 := srdC 1 v825
    let v827 := smx 29 1 v794 v41
    let v828 := srdF 1 v827
    let v829 := smx 29 1 v794 v29
    let v830 := srdC 1 v829
    let v831 := plt 1 v824 v828
    let v832 := psel (pmask v831) v824 v828
    let v833 := plt 1 v826 v830
    let v834 := psel (pmask v833) v830 v826
    let v835 := psel (pmask v809) v832 v824
    let v836 := psel (pmask v809) v834 v826
    let v837 := plt 1 v19 v835
    let v838 := plt 1 v61 v479
    let v839 := plt 1 v480 v33
    let v840 := Nat.land v838 v839
    let v841 := plt 1 v61 v100
    let v842 := plt 1 v101 v33
    let v843 := Nat.land v841 v842
    let v844 := plt 1 v61 v835
    let v845 := plt 1 v836 v33
    let v846 := Nat.land v844 v845
    let v847 := Nat.land v840 v843
    let v848 := Nat.land v846 v847
    let v849 := smx 29 1 v480 v480
    let v850 := srdC 1 v849
    let v851 := Nat.sub (Nat.add v850 v850) OFFr
    let v852 := Nat.sub (Nat.add v33 OFFr) v851
    let v853 := plt 1 v852 v105
    let v854 := psel (pmask v853) v105 v852
    let v855 := smx 29 1 v479 v479
    let v856 := srdF 1 v855
    let v857 := Nat.sub (Nat.add v856 v856) OFFr
    let v858 := Nat.sub (Nat.add v33 OFFr) v857
    let v859 := smx 29 1 v836 v836
    let v860 := srdC 1 v859
    let v861 := Nat.sub (Nat.add v860 v860) OFFr
    let v862 := Nat.sub (Nat.add v33 OFFr) v861
    let v863 := plt 1 v862 v105
    let v864 := psel (pmask v863) v105 v862
    let v865 := smx 29 1 v835 v835
    let v866 := srdF 1 v865
    let v867 := Nat.sub (Nat.add v866 v866) OFFr
    let v868 := Nat.sub (Nat.add v33 OFFr) v867
    let v869 := smx 29 1 v101 v101
    let v870 := srdC 1 v869
    let v871 := Nat.sub (Nat.add v870 v870) OFFr
    let v872 := Nat.sub (Nat.add v33 OFFr) v871
    let v873 := plt 1 v872 v105
    let v874 := psel (pmask v873) v105 v872
    let v875 := smx 29 1 v100 v100
    let v876 := srdF 1 v875
    let v877 := Nat.sub (Nat.add v876 v876) OFFr
    let v878 := Nat.sub (Nat.add v33 OFFr) v877
    let v879 := plt 1 v854 v61
    let v880 := Nat.sub 1 v879
    let v881 := plt 1 v61 v858
    let v882 := Nat.sub 1 v881
    let v883 := Nat.land v879 v882
    let v884 := Nat.land v879 v881
    let v885 := plt 1 v874 v61
    let v886 := Nat.sub 1 v885
    let v887 := plt 1 v61 v878
    let v888 := Nat.sub 1 v887
    let v889 := Nat.land v885 v888
    let v890 := Nat.land v885 v887
    let v891 := Nat.land v884 v890
    let v892 := Nat.land v880 v890
    let v893 := Nat.lor v889 v892
    let v894 := psel (pmask v893) v858 v854
    let v895 := Nat.sub 1 v889
    let v896 := Nat.land v884 v895
    let v897 := Nat.lor v883 v896
    let v898 := psel (pmask v897) v878 v874
    let v899 := Nat.land v883 v890
    let v900 := Nat.lor v889 v899
    let v901 := psel (pmask v900) v854 v858
    let v902 := Nat.land v884 v889
    let v903 := Nat.lor v883 v902
    let v904 := psel (pmask v903) v874 v878
    let v905 := smx 30 1 v898 v894
    let v906 := srdF 1 v905
    let v907 := smx 30 1 v904 v901
    let v908 := srdC 1 v907
    let v909 := smx 30 1 v874 v858
    let v910 := srdF 1 v909
    let v911 := smx 30 1 v874 v854
    let v912 := srdC 1 v911
    let v913 := plt 1 v906 v910
    let v914 := psel (pmask v913) v906 v910
    let v915 := plt 1 v908 v912
    let v916 := psel (pmask v915) v912 v908
    let v917 := psel (pmask v891) v914 v906
    let v918 := psel (pmask v891) v916 v908
    let v919 := Nat.sub (Nat.add v864 OFFr) v918
    let v920 := Nat.sub (Nat.add v868 OFFr) v917
    let v921 := plt 1 v864 v61
    let v922 := Nat.sub 1 v921
    let v923 := plt 1 v61 v868
    let v924 := Nat.sub 1 v923
    let v925 := Nat.land v921 v924
    let v926 := Nat.land v921 v923
    let v927 := Nat.land v884 v926
    let v928 := Nat.land v880 v926
    let v929 := Nat.lor v925 v928
    let v930 := psel (pmask v929) v858 v854
    let v931 := Nat.sub 1 v925
    let v932 := Nat.land v884 v931
    let v933 := Nat.lor v883 v932
    let v934 := psel (pmask v933) v868 v864
    let v935 := Nat.land v883 v926
    let v936 := Nat.lor v925 v935
    let v937 := psel (pmask v936) v854 v858
    let v938 := Nat.land v884 v925
    let v939 := Nat.lor v883 v938
    let v940 := psel (pmask v939) v864 v868
    let v941 := smx 30 1 v934 v930
    let v942 := srdF 1 v941
    let v943 := smx 30 1 v940 v937
    let v944 := srdC 1 v943
    let v945 := smx 30 1 v864 v858
    let v946 := srdF 1 v945
    let v947 := smx 30 1 v864 v854
    let v948 := srdC 1 v947
    let v949 := plt 1 v942 v946
    let v950 := psel (pmask v949) v942 v946
    let v951 := plt 1 v944 v948
    let v952 := psel (pmask v951) v948 v944
    let v953 := psel (pmask v927) v950 v942
    let v954 := psel (pmask v927) v952 v944
    let v955 := Nat.sub (Nat.add v874 OFFr) v954
    let v956 := Nat.sub (Nat.add v878 OFFr) v953
    let v957 := plt 1 v61 v919
    let v958 := plt 1 v920 v61
    let v959 := plt 1 v61 v955
    let v960 := plt 1 v956 v61
    let v961 := psel (pmask v957) v101 v100
    let v962 := psel (pmask v958) v100 v101
    let v963 := psel (pmask v958) v101 v100
    let v964 := psel (pmask v957) v100 v101
    let v965 := psel (pmask v959) v836 v835
    let v966 := psel (pmask v960) v835 v836
    let v967 := psel (pmask v960) v836 v835
    let v968 := psel (pmask v959) v835 v836
    let v974 := smx 29 1 v962 v962
    let v975 := srdC 1 v974
    let v976 := Nat.sub (Nat.add v975 v975) OFFr
    let v977 := Nat.sub (Nat.add v33 OFFr) v976
    let v978 := plt 1 v977 v105
    let v979 := psel (pmask v978) v105 v977
    let v980 := smx 29 1 v961 v961
    let v981 := srdF 1 v980
    let v982 := Nat.sub (Nat.add v981 v981) OFFr
    let v983 := Nat.sub (Nat.add v33 OFFr) v982
    let v984 := smx 29 1 v966 v966
    let v985 := srdC 1 v984
    let v986 := Nat.sub (Nat.add v985 v985) OFFr
    let v987 := Nat.sub (Nat.add v33 OFFr) v986
    let v988 := plt 1 v987 v105
    let v989 := psel (pmask v988) v105 v987
    let v990 := smx 29 1 v965 v965
    let v991 := srdF 1 v990
    let v992 := Nat.sub (Nat.add v991 v991) OFFr
    let v993 := Nat.sub (Nat.add v33 OFFr) v992
    let v994 := plt 1 v979 v61
    let v995 := Nat.sub 1 v994
    let v996 := plt 1 v61 v983
    let v997 := Nat.sub 1 v996
    let v998 := Nat.land v994 v997
    let v999 := Nat.land v994 v996
    let v1000 := plt 1 v989 v61
    let v1002 := plt 1 v61 v993
    let v1003 := Nat.sub 1 v1002
    let v1004 := Nat.land v1000 v1003
    let v1005 := Nat.land v1000 v1002
    let v1006 := Nat.land v999 v1005
    let v1007 := Nat.land v995 v1005
    let v1008 := Nat.lor v1004 v1007
    let v1009 := psel (pmask v1008) v983 v979
    let v1010 := Nat.sub 1 v1004
    let v1011 := Nat.land v999 v1010
    let v1012 := Nat.lor v998 v1011
    let v1013 := psel (pmask v1012) v993 v989
    let v1020 := smx 30 1 v1013 v1009
    let v1021 := srdF 1 v1020
    let v1024 := smx 30 1 v989 v983
    let v1025 := srdF 1 v1024
    let v1028 := plt 1 v1021 v1025
    let v1029 := psel (pmask v1028) v1021 v1025
    let v1032 := psel (pmask v1006) v1029 v1021
    let v1035 := Nat.sub (Nat.add v858 OFFr) v1032
    let v1036 := Nat.mul 1 4683743612465315840
    let v1037 := Nat.sub (Nat.add v1036 OFFr) v980
    let v1038 := psqrt 1 v1037
    let v1039 := Nat.sub (Nat.add v115 v1038) OFFr
    let v1040 := smx 29 1 v1038 v961
    let v1041 := srdF 1 v1040
    let v1042 := Nat.sub (Nat.add v1041 v1041) OFFr
    let v1043 := smx 29 1 v1039 v961
    let v1044 := srdC 1 v1043
    let v1045 := Nat.sub (Nat.add v1044 v1044) OFFr
    let v1046 := plt 1 v1045 v33
    let v1047 := psel (pmask v1046) v1045 v33
    let v1048 := Nat.sub (Nat.add v1036 OFFr) v974
    let v1049 := psqrt 1 v1048
    let v1050 := Nat.sub (Nat.add v115 v1049) OFFr
    let v1051 := smx 29 1 v1049 v962
    let v1052 := srdF 1 v1051
    let v1053 := Nat.sub (Nat.add v1052 v1052) OFFr
    let v1054 := smx 29 1 v1050 v962
    let v1055 := srdC 1 v1054
    let v1056 := Nat.sub (Nat.add v1055 v1055) OFFr
    let v1057 := plt 1 v1056 v33
    let v1058 := psel (pmask v1057) v1056 v33
    let v1059 := plt 1 v1042 v1053
    let v1060 := psel (pmask v1059) v1042 v1053
    let v1061 := plt 1 v1047 v1058
    let v1062 := psel (pmask v1061) v1058 v1047
    let v1063 := Nat.mul 1 4647714815446351872
    let v1064 := plt 1 v1063 v980
    let v1065 := Nat.sub 1 v1064
    let v1066 := plt 1 v974 v1063
    let v1067 := Nat.sub 1 v1066
    let v1068 := Nat.land v1065 v1067
    let v1069 := psel (pmask v1068) v33 v1062
    let v1070 := Nat.sub (Nat.add v1036 OFFr) v990
    let v1071 := psqrt 1 v1070
    let v1072 := Nat.sub (Nat.add v115 v1071) OFFr
    let v1073 := smx 29 1 v1071 v965
    let v1074 := srdF 1 v1073
    let v1075 := Nat.sub (Nat.add v1074 v1074) OFFr
    let v1076 := smx 29 1 v1072 v965
    let v1077 := srdC 1 v1076
    let v1078 := Nat.sub (Nat.add v1077 v1077) OFFr
    let v1079 := plt 1 v1078 v33
    let v1080 := psel (pmask v1079) v1078 v33
    let v1081 := Nat.sub (Nat.add v1036 OFFr) v984
    let v1082 := psqrt 1 v1081
    let v1083 := Nat.sub (Nat.add v115 v1082) OFFr
    let v1084 := smx 29 1 v1082 v966
    let v1085 := srdF 1 v1084
    let v1086 := Nat.sub (Nat.add v1085 v1085) OFFr
    let v1087 := smx 29 1 v1083 v966
    let v1088 := srdC 1 v1087
    let v1089 := Nat.sub (Nat.add v1088 v1088) OFFr
    let v1090 := plt 1 v1089 v33
    let v1091 := psel (pmask v1090) v1089 v33
    let v1092 := plt 1 v1075 v1086
    let v1093 := psel (pmask v1092) v1075 v1086
    let v1094 := plt 1 v1080 v1091
    let v1095 := psel (pmask v1094) v1091 v1080
    let v1096 := plt 1 v1063 v990
    let v1097 := Nat.sub 1 v1096
    let v1098 := plt 1 v984 v1063
    let v1099 := Nat.sub 1 v1098
    let v1100 := Nat.land v1097 v1099
    let v1101 := psel (pmask v1100) v33 v1095
    let v1102 := plt 1 v1060 v61
    let v1103 := Nat.sub 1 v1102
    let v1104 := plt 1 v61 v1069
    let v1105 := Nat.sub 1 v1104
    let v1106 := Nat.land v1102 v1105
    let v1107 := Nat.land v1102 v1104
    let v1108 := plt 1 v1093 v61
    let v1110 := plt 1 v61 v1101
    let v1111 := Nat.sub 1 v1110
    let v1112 := Nat.land v1108 v1111
    let v1113 := Nat.land v1108 v1110
    let v1114 := Nat.land v1107 v1113
    let v1115 := Nat.land v1103 v1113
    let v1116 := Nat.lor v1112 v1115
    let v1117 := psel (pmask v1116) v1069 v1060
    let v1118 := Nat.sub 1 v1112
    let v1119 := Nat.land v1107 v1118
    let v1120 := Nat.lor v1106 v1119
    let v1121 := psel (pmask v1120) v1101 v1093
    let v1122 := Nat.land v1106 v1113
    let v1123 := Nat.lor v1112 v1122
    let v1124 := psel (pmask v1123) v1060 v1069
    let v1125 := Nat.land v1107 v1112
    let v1126 := Nat.lor v1106 v1125
    let v1127 := psel (pmask v1126) v1093 v1101
    let v1128 := smx 29 1 v1121 v1117
    let v1129 := srdF 1 v1128
    let v1130 := smx 29 1 v1127 v1124
    let v1131 := srdC 1 v1130
    let v1132 := smx 29 1 v1093 v1069
    let v1133 := srdF 1 v1132
    let v1134 := smx 29 1 v1093 v1060
    let v1135 := srdC 1 v1134
    let v1136 := plt 1 v1129 v1133
    let v1137 := psel (pmask v1136) v1129 v1133
    let v1138 := plt 1 v1131 v1135
    let v1139 := psel (pmask v1138) v1135 v1131
    let v1140 := psel (pmask v1114) v1137 v1129
    let v1141 := psel (pmask v1114) v1139 v1131
    let v1142 := plt 1 v61 v1140
    let v1143 := Nat.sub 1 v1142
    let v1146 := plt 1 v1035 v61
    let v1147 := psel (pmask v1146) v1141 v1140
    let v1148 := Nat.sub (Nat.add v61 OFFr) v1147
    let v1149 := plt 1 v1035 v1148
    let v1150 := Nat.land v1142 v1149
    let v1151 := plt 1 v1035 v1147
    let v1152 := Nat.sub 1 v1151
    let v1153 := Nat.lor v1143 v1152
    let v1154 := psel (pmask v1153) v33 v1035
    let v1155 := psel (pmask v1153) v33 v1147
    ∀ (P : Prop), (((v674 = 1 ↔ v663 = 1 ∨ v673 = 1)) → (v675 = if v674 = 1 then v110 else v117) → ((v676 = 1 ↔ v149 = 1 ∧ v663 = 1)) → ((v677 = 1 ↔ v148 = 1 ∨ v676 = 1)) → (v678 = if v677 = 1 then v651 else v658) → (sv v679 = sv v672 * sv v668) → (sv v680 = sv v679 / 2 ^ 28) → (sv v681 = sv v678 * sv v675) → (sv v682 = -((-sv v681) / 2 ^ 28)) → (sv v683 = sv v651 * sv v117) → (sv v684 = sv v683 / 2 ^ 28) → (sv v685 = sv v651 * sv v110) → (sv v686 = -((-sv v685) / 2 ^ 28)) → ((v687 = 1 ↔ sv v680 < sv v684)) → (v688 = if v687 = 1 then v680 else v684) → ((v689 = 1 ↔ sv v682 < sv v686)) → (v690 = if v689 = 1 then v686 else v682) → (v691 = if v665 = 1 then v688 else v680) → (v692 = if v665 = 1 then v690 else v682) → ((v693 = 1 ↔ sv v61 < sv v691)) → ((v694 = 1 ↔ ¬v693 = 1)) → ((v697 = 1 ↔ sv v647 < sv v61)) → (v698 = if v697 = 1 then v692 else v691) → (sv v740 = sv v61 - sv v647) → (v741 = if v697 = 1 then v740 else v647) → (sv v742 = ((H1 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ)) → (sv t742.1 = (sc28pS (scArg v742)).1) → (sv t742.2 = (sc28pS (scArg v742)).2) → (sv v744 = sv v28 + sv t742.2) → ((v745 = 1 ↔ sv v744 < sv v105)) → (v746 = if v745 = 1 then v105 else v744) → (sv v747 = sv v31 + sv t742.2) → ((v748 = 1 ↔ sv v747 < sv v33)) → (v749 = if v748 = 1 then v747 else v33) → (sv v751 = sv v31 + sv t742.1) → ((v752 = 1 ↔ sv v751 < sv v33)) → (v753 = if v752 = 1 then v751 else v33) → (sv v754 = sv v28 + sv t742.1) → (v755 = if v697 = 1 then v746 else v749) → (v756 = if v697 = 1 then v753 else v754) → (sv v757 = sv v698 * sv v756) → (sv v758 = sv v755 * sv v741) → ((v759 = 1 ↔ sv v758 < sv v757)) → ((v760 = 1 ↔ ¬v759 = 1)) → ((v761 = 1 ↔ sv v757 < sv v758)) → ((v762 = 1 ↔ ¬v761 = 1)) → ((v763 = 1 ↔ sv v61 < sv v742)) → ((v764 = 1 ↔ ¬v763 = 1)) → ((v765 = 1 ↔ sv v216 < sv v742)) → ((v766 = 1 ↔ ¬v765 = 1)) → ((v767 = 1 ↔ sv v19 < sv v746)) → ((v768 = 1 ↔ v760 = 1 ∧ v767 = 1)) → ((v769 = 1 ↔ v766 = 1 ∧ v768 = 1)) → ((v770 = 1 ↔ v764 = 1 ∨ v769 = 1)) → ((v771 = 1 ↔ sv v742 < sv v223)) → ((v772 = 1 ↔ ¬v771 = 1)) → ((v773 = 1 ↔ v762 = 1 ∨ v772 = 1)) → ((v774 = 1 ↔ v697 = 1 ∧ v770 = 1)) → ((v775 = 1 ↔ ¬v697 = 1)) → ((v776 = 1 ↔ v773 = 1 ∧ v775 = 1)) → ((v777 = 1 ↔ v774 = 1 ∨ v776 = 1)) → (sv v778 = sv v61 - sv v742) → (v779 = if v697 = 1 then v778 else v742) → (v780 = if v777 = 1 then v779 else v223) → (R 1 0 4611686017353646081 4611686019501129727 v782 v782) → (v782 = if v694 = 1 then v223 else v780) → (sv v783 = sv v7 / 2) → (sv v784 = (sv v7 + 1) / 2) → (v785 = if v13 = 1 then v784 else v223) → ((v786 = 1 ↔ sv v19 < sv v783)) → ((v787 = 1 ↔ sv v9 < sv v785)) → ((v788 = 1 ↔ ¬v787 = 1)) → (R 1 0 0 1 v789 v789) → ((v789 = 1 ↔ v786 = 1 ∧ v788 = 1)) → (sv t783.1 = (sc28pS (scArg v783)).1) → (sv t785.1 = (sc28pS (scArg v785)).1) → ((v792 = 1 ↔ sv t783.1 < sv t785.1)) → (v793 = if v792 = 1 then t783.1 else t785.1) → (sv v794 = sv v28 + sv v793) → (v795 = if v792 = 1 then t785.1 else t783.1) → (sv v796 = sv v31 + sv v795) → ((v797 = 1 ↔ sv v796 < sv v33)) → (v798 = if v797 = 1 then v796 else v33) → ((v799 = 1 ↔ sv v783 < sv v36)) → ((v800 = 1 ↔ sv v38 < sv v785)) → ((v801 = 1 ↔ v799 = 1 ∧ v800 = 1)) → (v802 = if v801 = 1 then v33 else v798) → ((v803 = 1 ↔ sv v794 < sv v61)) → ((v805 = 1 ↔ sv v61 < sv v802)) → ((v806 = 1 ↔ ¬v805 = 1)) → ((v807 = 1 ↔ v803 = 1 ∧ v806 = 1)) → ((v808 = 1 ↔ v803 = 1 ∧ v805 = 1)) → ((v809 = 1 ↔ v67 = 1 ∧ v808 = 1)) → ((v810 = 1 ↔ v63 = 1 ∧ v808 = 1)) → ((v811 = 1 ↔ v807 = 1 ∨ v810 = 1)) → (v812 = if v811 = 1 then v41 else v29) → ((v813 = 1 ↔ ¬v807 = 1)) → ((v814 = 1 ↔ v67 = 1 ∧ v813 = 1)) → ((v815 = 1 ↔ v66 = 1 ∨ v814 = 1)) → (v816 = if v815 = 1 then v802 else v794) → ((v817 = 1 ↔ v66 = 1 ∧ v808 = 1)) → ((v818 = 1 ↔ v807 = 1 ∨ v817 = 1)) → (v819 = if v818 = 1 then v29 else v41) → ((v820 = 1 ↔ v67 = 1 ∧ v807 = 1)) → ((v821 = 1 ↔ v66 = 1 ∨ v820 = 1)) → (v822 = if v821 = 1 then v794 else v802) → (sv v823 = sv v816 * sv v812) → (sv v824 = sv v823 / 2 ^ 28) → (sv v825 = sv v822 * sv v819) → (sv v826 = -((-sv v825) / 2 ^ 28)) → (sv v827 = sv v794 * sv v41) → (sv v828 = sv v827 / 2 ^ 28) → (sv v829 = sv v794 * sv v29) → (sv v830 = -((-sv v829) / 2 ^ 28)) → ((v831 = 1 ↔ sv v824 < sv v828)) → (v832 = if v831 = 1 then v824 else v828) → ((v833 = 1 ↔ sv v826 < sv v830)) → (v834 = if v833 = 1 then v830 else v826) → (R 1 0 4611686018427387899 4611686018695823374 v835 v835) → (v835 = if v809 = 1 then v832 else v824) → (R 1 0 4611686018427387900 4611686018695823375 v836 v836) → (v836 = if v809 = 1 then v834 else v826) → (R 1 0 0 1 v837 v837) → ((v837 = 1 ↔ sv v19 < sv v835)) → ((v838 = 1 ↔ sv v61 < sv v479)) → ((v839 = 1 ↔ sv v480 < sv v33)) → ((v840 = 1 ↔ v838 = 1 ∧ v839 = 1)) → ((v841 = 1 ↔ sv v61 < sv v100)) → ((v842 = 1 ↔ sv v101 < sv v33)) → ((v843 = 1 ↔ v841 = 1 ∧ v842 = 1)) → ((v844 = 1 ↔ sv v61 < sv v835)) → ((v845 = 1 ↔ sv v836 < sv v33)) → (R 1 0 0 1 v846 v846) → ((v846 = 1 ↔ v844 = 1 ∧ v845 = 1)) → ((v847 = 1 ↔ v840 = 1 ∧ v843 = 1)) → (R 1 0 0 1 v848 v848) → ((v848 = 1 ↔ v846 = 1 ∧ v847 = 1)) → (sv v849 = sv v480 * sv v480) → (sv v850 = -((-sv v849) / 2 ^ 28)) → (sv v851 = sv v850 + sv v850) → (sv v852 = sv v33 - sv v851) → ((v853 = 1 ↔ sv v852 < sv v105)) → (R 1 0 4611686018158952386 4611686018695823360 v854 v854) → (v854 = if v853 = 1 then v105 else v852) → (sv v855 = sv v479 * sv v479) → (sv v856 = sv v855 / 2 ^ 28) → (sv v857 = sv v856 + sv v856) → (R 1 0 4611686018158952392 4611686018695823360 v858 v858) → (sv v858 = sv v33 - sv v857) → (sv v859 = sv v836 * sv v836) → (sv v860 = -((-sv v859) / 2 ^ 28)) → (sv v861 = sv v860 + sv v860) → (sv v862 = sv v33 - sv v861) → ((v863 = 1 ↔ sv v862 < sv v105)) → (R 1 0 4611686018158952386 4611686018695823360 v864 v864) → (v864 = if v863 = 1 then v105 else v862) → (sv v865 = sv v835 * sv v835) → (sv v866 = sv v865 / 2 ^ 28) → (sv v867 = sv v866 + sv v866) → (R 1 0 4611686018158952392 4611686018695823360 v868 v868) → (sv v868 = sv v33 - sv v867) → (sv v869 = sv v101 * sv v101) → (sv v870 = -((-sv v869) / 2 ^ 28)) → (sv v871 = sv v870 + sv v870) → (sv v872 = sv v33 - sv v871) → ((v873 = 1 ↔ sv v872 < sv v105)) → (R 1 0 4611686018158952386 4611686018695823360 v874 v874) → (v874 = if v873 = 1 then v105 else v872) → (sv v875 = sv v100 * sv v100) → (sv v876 = sv v875 / 2 ^ 28) → (sv v877 = sv v876 + sv v876) → (R 1 0 4611686018158952392 4611686018695823360 v878 v878) → (sv v878 = sv v33 - sv v877) → ((v879 = 1 ↔ sv v854 < sv v61)) → ((v880 = 1 ↔ ¬v879 = 1)) → ((v881 = 1 ↔ sv v61 < sv v858)) → ((v882 = 1 ↔ ¬v881 = 1)) → (R 1 0 0 1 v883 v883) → ((v883 = 1 ↔ v879 = 1 ∧ v882 = 1)) → (R 1 0 0 1 v884 v884) → ((v884 = 1 ↔ v879 = 1 ∧ v881 = 1)) → ((v885 = 1 ↔ sv v874 < sv v61)) → (R 1 0 0 1 v886 v886) → ((v886 = 1 ↔ ¬v885 = 1)) → ((v887 = 1 ↔ sv v61 < sv v878)) → ((v888 = 1 ↔ ¬v887 = 1)) → (R 1 0 0 1 v889 v889) → ((v889 = 1 ↔ v885 = 1 ∧ v888 = 1)) → (R 1 0 0 1 v890 v890) → ((v890 = 1 ↔ v885 = 1 ∧ v887 = 1)) → (R 1 0 0 1 v891 v891) → ((v891 = 1 ↔ v884 = 1 ∧ v890 = 1)) → ((v892 = 1 ↔ v880 = 1 ∧ v890 = 1)) → ((v893 = 1 ↔ v889 = 1 ∨ v892 = 1)) → (v894 = if v893 = 1 then v858 else v854) → ((v895 = 1 ↔ ¬v889 = 1)) → ((v896 = 1 ↔ v884 = 1 ∧ v895 = 1)) → ((v897 = 1 ↔ v883 = 1 ∨ v896 = 1)) → (v898 = if v897 = 1 then v878 else v874) → ((v899 = 1 ↔ v883 = 1 ∧ v890 = 1)) → ((v900 = 1 ↔ v889 = 1 ∨ v899 = 1)) → (v901 = if v900 = 1 then v854 else v858) → ((v902 = 1 ↔ v884 = 1 ∧ v889 = 1)) → ((v903 = 1 ↔ v883 = 1 ∨ v902 = 1)) → (v904 = if v903 = 1 then v874 else v878) → (sv v905 = sv v898 * sv v894) → (sv v906 = sv v905 / 2 ^ 28) → (sv v907 = sv v904 * sv v901) → (sv v908 = -((-sv v907) / 2 ^ 28)) → (sv v909 = sv v874 * sv v858) → (sv v910 = sv v909 / 2 ^ 28) → (sv v911 = sv v874 * sv v854) → (sv v912 = -((-sv v911) / 2 ^ 28)) → ((v913 = 1 ↔ sv v906 < sv v910)) → (v914 = if v913 = 1 then v906 else v910) → ((v915 = 1 ↔ sv v908 < sv v912)) → (v916 = if v915 = 1 then v912 else v908) → (v917 = if v891 = 1 then v914 else v906) → (v918 = if v891 = 1 then v916 else v908) → (sv v919 = sv v864 - sv v918) → (sv v920 = sv v868 - sv v917) → ((v921 = 1 ↔ sv v864 < sv v61)) → (R 1 0 0 1 v922 v922) → ((v922 = 1 ↔ ¬v921 = 1)) → ((v923 = 1 ↔ sv v61 < sv v868)) → ((v924 = 1 ↔ ¬v923 = 1)) → (R 1 0 0 1 v925 v925) → ((v925 = 1 ↔ v921 = 1 ∧ v924 = 1)) → (R 1 0 0 1 v926 v926) → ((v926 = 1 ↔ v921 = 1 ∧ v923 = 1)) → ((v927 = 1 ↔ v884 = 1 ∧ v926 = 1)) → ((v928 = 1 ↔ v880 = 1 ∧ v926 = 1)) → ((v929 = 1 ↔ v925 = 1 ∨ v928 = 1)) → (v930 = if v929 = 1 then v858 else v854) → (R 1 0 0 1 v931 v931) → ((v931 = 1 ↔ ¬v925 = 1)) → ((v932 = 1 ↔ v884 = 1 ∧ v931 = 1)) → ((v933 = 1 ↔ v883 = 1 ∨ v932 = 1)) → (v934 = if v933 = 1 then v868 else v864) → ((v935 = 1 ↔ v883 = 1 ∧ v926 = 1)) → ((v936 = 1 ↔ v925 = 1 ∨ v935 = 1)) → (v937 = if v936 = 1 then v854 else v858) → ((v938 = 1 ↔ v884 = 1 ∧ v925 = 1)) → ((v939 = 1 ↔ v883 = 1 ∨ v938 = 1)) → (v940 = if v939 = 1 then v864 else v868) → (sv v941 = sv v934 * sv v930) → (sv v942 = sv v941 / 2 ^ 28) → (sv v943 = sv v940 * sv v937) → (sv v944 = -((-sv v943) / 2 ^ 28)) → (sv v945 = sv v864 * sv v858) → (sv v946 = sv v945 / 2 ^ 28) → (sv v947 = sv v864 * sv v854) → (sv v948 = -((-sv v947) / 2 ^ 28)) → ((v949 = 1 ↔ sv v942 < sv v946)) → (v950 = if v949 = 1 then v942 else v946) → ((v951 = 1 ↔ sv v944 < sv v948)) → (v952 = if v951 = 1 then v948 else v944) → (v953 = if v927 = 1 then v950 else v942) → (v954 = if v927 = 1 then v952 else v944) → (sv v955 = sv v874 - sv v954) → (sv v956 = sv v878 - sv v953) → (R 1 0 0 1 v957 v957) → ((v957 = 1 ↔ sv v61 < sv v919)) → ((v958 = 1 ↔ sv v920 < sv v61)) → ((v959 = 1 ↔ sv v61 < sv v955)) → ((v960 = 1 ↔ sv v956 < sv v61)) → (v961 = if v957 = 1 then v101 else v100) → (v962 = if v958 = 1 then v100 else v101) → (R 1 0 4611686018427387899 4611686018695823375 v963 v963) → (v963 = if v958 = 1 then v101 else v100) → (R 1 0 4611686018427387899 4611686018695823375 v964 v964) → (v964 = if v957 = 1 then v100 else v101) → (v965 = if v959 = 1 then v836 else v835) → (v966 = if v960 = 1 then v835 else v836) → (R 1 0 4611686018427387899 4611686018695823375 v967 v967) → (v967 = if v960 = 1 then v836 else v835) → (R 1 0 4611686018427387899 4611686018695823375 v968 v968) → (v968 = if v959 = 1 then v835 else v836) → (sv v974 = sv v962 * sv v962) → (sv v975 = -((-sv v974) / 2 ^ 28)) → (sv v976 = sv v975 + sv v975) → (sv v977 = sv v33 - sv v976) → ((v978 = 1 ↔ sv v977 < sv v105)) → (v979 = if v978 = 1 then v105 else v977) → (sv v980 = sv v961 * sv v961) → (sv v981 = sv v980 / 2 ^ 28) → (sv v982 = sv v981 + sv v981) → (sv v983 = sv v33 - sv v982) → (sv v984 = sv v966 * sv v966) → (sv v985 = -((-sv v984) / 2 ^ 28)) → (sv v986 = sv v985 + sv v985) → (sv v987 = sv v33 - sv v986) → ((v988 = 1 ↔ sv v987 < sv v105)) → (v989 = if v988 = 1 then v105 else v987) → (sv v990 = sv v965 * sv v965) → (sv v991 = sv v990 / 2 ^ 28) → (sv v992 = sv v991 + sv v991) → (sv v993 = sv v33 - sv v992) → ((v994 = 1 ↔ sv v979 < sv v61)) → ((v995 = 1 ↔ ¬v994 = 1)) → ((v996 = 1 ↔ sv v61 < sv v983)) → ((v997 = 1 ↔ ¬v996 = 1)) → ((v998 = 1 ↔ v994 = 1 ∧ v997 = 1)) → ((v999 = 1 ↔ v994 = 1 ∧ v996 = 1)) → ((v1000 = 1 ↔ sv v989 < sv v61)) → ((v1002 = 1 ↔ sv v61 < sv v993)) → ((v1003 = 1 ↔ ¬v1002 = 1)) → ((v1004 = 1 ↔ v1000 = 1 ∧ v1003 = 1)) → ((v1005 = 1 ↔ v1000 = 1 ∧ v1002 = 1)) → ((v1006 = 1 ↔ v999 = 1 ∧ v1005 = 1)) → ((v1007 = 1 ↔ v995 = 1 ∧ v1005 = 1)) → ((v1008 = 1 ↔ v1004 = 1 ∨ v1007 = 1)) → (v1009 = if v1008 = 1 then v983 else v979) → ((v1010 = 1 ↔ ¬v1004 = 1)) → ((v1011 = 1 ↔ v999 = 1 ∧ v1010 = 1)) → ((v1012 = 1 ↔ v998 = 1 ∨ v1011 = 1)) → (v1013 = if v1012 = 1 then v993 else v989) → (sv v1020 = sv v1013 * sv v1009) → (sv v1021 = sv v1020 / 2 ^ 28) → (sv v1024 = sv v989 * sv v983) → (sv v1025 = sv v1024 / 2 ^ 28) → ((v1028 = 1 ↔ sv v1021 < sv v1025)) → (v1029 = if v1028 = 1 then v1021 else v1025) → (v1032 = if v1006 = 1 then v1029 else v1021) → (sv v1035 = sv v858 - sv v1032) → (sv v1036 = (72057594037927936)) → (sv v1037 = sv v1036 - sv v980) → (sv v1038 = ((Nat.sqrt (v1037 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1039 = sv v115 + sv v1038) → (sv v1040 = sv v1038 * sv v961) → (sv v1041 = sv v1040 / 2 ^ 28) → (sv v1042 = sv v1041 + sv v1041) → (sv v1043 = sv v1039 * sv v961) → (sv v1044 = -((-sv v1043) / 2 ^ 28)) → (sv v1045 = sv v1044 + sv v1044) → ((v1046 = 1 ↔ sv v1045 < sv v33)) → (v1047 = if v1046 = 1 then v1045 else v33) → (sv v1048 = sv v1036 - sv v974) → (sv v1049 = ((Nat.sqrt (v1048 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1050 = sv v115 + sv v1049) → (sv v1051 = sv v1049 * sv v962) → (sv v1052 = sv v1051 / 2 ^ 28) → (sv v1053 = sv v1052 + sv v1052) → (sv v1054 = sv v1050 * sv v962) → (sv v1055 = -((-sv v1054) / 2 ^ 28)) → (sv v1056 = sv v1055 + sv v1055) → ((v1057 = 1 ↔ sv v1056 < sv v33)) → (v1058 = if v1057 = 1 then v1056 else v33) → ((v1059 = 1 ↔ sv v1042 < sv v1053)) → (v1060 = if v1059 = 1 then v1042 else v1053) → ((v1061 = 1 ↔ sv v1047 < sv v1058)) → (v1062 = if v1061 = 1 then v1058 else v1047) → (sv v1063 = (36028797018963968)) → ((v1064 = 1 ↔ sv v1063 < sv v980)) → ((v1065 = 1 ↔ ¬v1064 = 1)) → ((v1066 = 1 ↔ sv v974 < sv v1063)) → ((v1067 = 1 ↔ ¬v1066 = 1)) → ((v1068 = 1 ↔ v1065 = 1 ∧ v1067 = 1)) → (v1069 = if v1068 = 1 then v33 else v1062) → (sv v1070 = sv v1036 - sv v990) → (sv v1071 = ((Nat.sqrt (v1070 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1072 = sv v115 + sv v1071) → (sv v1073 = sv v1071 * sv v965) → (sv v1074 = sv v1073 / 2 ^ 28) → (sv v1075 = sv v1074 + sv v1074) → (sv v1076 = sv v1072 * sv v965) → (sv v1077 = -((-sv v1076) / 2 ^ 28)) → (sv v1078 = sv v1077 + sv v1077) → ((v1079 = 1 ↔ sv v1078 < sv v33)) → (v1080 = if v1079 = 1 then v1078 else v33) → (sv v1081 = sv v1036 - sv v984) → (sv v1082 = ((Nat.sqrt (v1081 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1083 = sv v115 + sv v1082) → (sv v1084 = sv v1082 * sv v966) → (sv v1085 = sv v1084 / 2 ^ 28) → (sv v1086 = sv v1085 + sv v1085) → (sv v1087 = sv v1083 * sv v966) → (sv v1088 = -((-sv v1087) / 2 ^ 28)) → (sv v1089 = sv v1088 + sv v1088) → ((v1090 = 1 ↔ sv v1089 < sv v33)) → (v1091 = if v1090 = 1 then v1089 else v33) → ((v1092 = 1 ↔ sv v1075 < sv v1086)) → (v1093 = if v1092 = 1 then v1075 else v1086) → ((v1094 = 1 ↔ sv v1080 < sv v1091)) → (v1095 = if v1094 = 1 then v1091 else v1080) → ((v1096 = 1 ↔ sv v1063 < sv v990)) → ((v1097 = 1 ↔ ¬v1096 = 1)) → ((v1098 = 1 ↔ sv v984 < sv v1063)) → ((v1099 = 1 ↔ ¬v1098 = 1)) → ((v1100 = 1 ↔ v1097 = 1 ∧ v1099 = 1)) → (v1101 = if v1100 = 1 then v33 else v1095) → ((v1102 = 1 ↔ sv v1060 < sv v61)) → ((v1103 = 1 ↔ ¬v1102 = 1)) → ((v1104 = 1 ↔ sv v61 < sv v1069)) → ((v1105 = 1 ↔ ¬v1104 = 1)) → ((v1106 = 1 ↔ v1102 = 1 ∧ v1105 = 1)) → ((v1107 = 1 ↔ v1102 = 1 ∧ v1104 = 1)) → ((v1108 = 1 ↔ sv v1093 < sv v61)) → ((v1110 = 1 ↔ sv v61 < sv v1101)) → ((v1111 = 1 ↔ ¬v1110 = 1)) → ((v1112 = 1 ↔ v1108 = 1 ∧ v1111 = 1)) → ((v1113 = 1 ↔ v1108 = 1 ∧ v1110 = 1)) → ((v1114 = 1 ↔ v1107 = 1 ∧ v1113 = 1)) → ((v1115 = 1 ↔ v1103 = 1 ∧ v1113 = 1)) → ((v1116 = 1 ↔ v1112 = 1 ∨ v1115 = 1)) → (v1117 = if v1116 = 1 then v1069 else v1060) → ((v1118 = 1 ↔ ¬v1112 = 1)) → ((v1119 = 1 ↔ v1107 = 1 ∧ v1118 = 1)) → ((v1120 = 1 ↔ v1106 = 1 ∨ v1119 = 1)) → (v1121 = if v1120 = 1 then v1101 else v1093) → ((v1122 = 1 ↔ v1106 = 1 ∧ v1113 = 1)) → ((v1123 = 1 ↔ v1112 = 1 ∨ v1122 = 1)) → (v1124 = if v1123 = 1 then v1060 else v1069) → ((v1125 = 1 ↔ v1107 = 1 ∧ v1112 = 1)) → ((v1126 = 1 ↔ v1106 = 1 ∨ v1125 = 1)) → (v1127 = if v1126 = 1 then v1093 else v1101) → (sv v1128 = sv v1121 * sv v1117) → (sv v1129 = sv v1128 / 2 ^ 28) → (sv v1130 = sv v1127 * sv v1124) → (sv v1131 = -((-sv v1130) / 2 ^ 28)) → (sv v1132 = sv v1093 * sv v1069) → (sv v1133 = sv v1132 / 2 ^ 28) → (sv v1134 = sv v1093 * sv v1060) → (sv v1135 = -((-sv v1134) / 2 ^ 28)) → ((v1136 = 1 ↔ sv v1129 < sv v1133)) → (v1137 = if v1136 = 1 then v1129 else v1133) → ((v1138 = 1 ↔ sv v1131 < sv v1135)) → (v1139 = if v1138 = 1 then v1135 else v1131) → (v1140 = if v1114 = 1 then v1137 else v1129) → (v1141 = if v1114 = 1 then v1139 else v1131) → ((v1142 = 1 ↔ sv v61 < sv v1140)) → ((v1143 = 1 ↔ ¬v1142 = 1)) → ((v1146 = 1 ↔ sv v1035 < sv v61)) → (v1147 = if v1146 = 1 then v1141 else v1140) → (sv v1148 = sv v61 - sv v1147) → ((v1149 = 1 ↔ sv v1035 < sv v1148)) → (R 1 0 0 1 v1150 v1150) → ((v1150 = 1 ↔ v1142 = 1 ∧ v1149 = 1)) → ((v1151 = 1 ↔ sv v1035 < sv v1147)) → ((v1152 = 1 ↔ ¬v1151 = 1)) → ((v1153 = 1 ↔ v1143 = 1 ∨ v1152 = 1)) → (R 1 0 4611686017890516812 4611686018964258878 v1154 v1154) → (v1154 = if v1153 = 1 then v33 else v1035) → (R 1 0 4611686018427387893 4611686018695823369 v1155 v1155) → (v1155 = if v1153 = 1 then v33 else v1147) → P) → P := by
  intro OFFr H61r v7 v9 v19 v28 v31 v33 v36 v38 v61 v105 v115 v216 v223 v674 v675 v676 v677 v678 v679 v680 v681 v682 v683 v684 v685 v686 v687 v688 v689 v690 v691 v692 v693 v694 v697 v698 v740 v741 v742 t742 v744 v745 v746 v747 v748 v749 v751 v752 v753 v754 v755 v756 v757 v758 v759 v760 v761 v762 v763 v764 v765 v766 v767 v768 v769 v770 v771 v772 v773 v774 v775 v776 v777 v778 v779 v780 v782 v783 v784 v785 v786 v787 v788 v789 t783 t785 v792 v793 v794 v795 v796 v797 v798 v799 v800 v801 v802 v803 v805 v806 v807 v808 v809 v810 v811 v812 v813 v814 v815 v816 v817 v818 v819 v820 v821 v822 v823 v824 v825 v826 v827 v828 v829 v830 v831 v832 v833 v834 v835 v836 v837 v838 v839 v840 v841 v842 v843 v844 v845 v846 v847 v848 v849 v850 v851 v852 v853 v854 v855 v856 v857 v858 v859 v860 v861 v862 v863 v864 v865 v866 v867 v868 v869 v870 v871 v872 v873 v874 v875 v876 v877 v878 v879 v880 v881 v882 v883 v884 v885 v886 v887 v888 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 v918 v919 v920 v921 v922 v923 v924 v925 v926 v927 v928 v929 v930 v931 v932 v933 v934 v935 v936 v937 v938 v939 v940 v941 v942 v943 v944 v945 v946 v947 v948 v949 v950 v951 v952 v953 v954 v955 v956 v957 v958 v959 v960 v961 v962 v963 v964 v965 v966 v967 v968 v974 v975 v976 v977 v978 v979 v980 v981 v982 v983 v984 v985 v986 v987 v988 v989 v990 v991 v992 v993 v994 v995 v996 v997 v998 v999 v1000 v1002 v1003 v1004 v1005 v1006 v1007 v1008 v1009 v1010 v1011 v1012 v1013 v1020 v1021 v1024 v1025 v1028 v1029 v1032 v1035 v1036 v1037 v1038 v1039 v1040 v1041 v1042 v1043 v1044 v1045 v1046 v1047 v1048 v1049 v1050 v1051 v1052 v1053 v1054 v1055 v1056 v1057 v1058 v1059 v1060 v1061 v1062 v1063 v1064 v1065 v1066 v1067 v1068 v1069 v1070 v1071 v1072 v1073 v1074 v1075 v1076 v1077 v1078 v1079 v1080 v1081 v1082 v1083 v1084 v1085 v1086 v1087 v1088 v1089 v1090 v1091 v1092 v1093 v1094 v1095 v1096 v1097 v1098 v1099 v1100 v1101 v1102 v1103 v1104 v1105 v1106 v1107 v1108 v1110 v1111 v1112 v1113 v1114 v1115 v1116 v1117 v1118 v1119 v1120 v1121 v1122 v1123 v1124 v1125 v1126 v1127 v1128 v1129 v1130 v1131 v1132 v1133 v1134 v1135 v1136 v1137 v1138 v1139 v1140 v1141 v1142 v1143 v1146 v1147 v1148 v1149 v1150 v1151 v1152 v1153 v1154 v1155
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_H61r : R 1 0 2305843009213693952 2305843009213693952 H61r H61r := (r_c hl 2305843009213693952 (of_decide_eq_true rfl))
  have h_v7 : R 1 0 4611686018427387904 4611686087146864624 v7 v7 := (r1_ix hb_F3 32 (of_decide_eq_true rfl))
  have h_v9 : R 1 0 4611686019270702761 4611686019270702761 v9 v9 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have h_v19 : R 1 0 4611686018427387903 4611686018427387903 v19 v19 := (r_c hl 4611686018427387903 (of_decide_eq_true rfl))
  have h_v28 : R 1 0 4611686018427387900 4611686018427387900 v28 v28 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have h_v31 : R 1 0 4611686018427387908 4611686018427387908 v31 v31 := (r_c hl 4611686018427387908 (of_decide_eq_true rfl))
  have h_v33 : R 1 0 4611686018695823360 4611686018695823360 v33 v33 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have h_v36 : R 1 0 4611686018849045334 4611686018849045334 v36 v36 := (r_c hl 4611686018849045334 (of_decide_eq_true rfl))
  have h_v38 : R 1 0 4611686018849045331 4611686018849045331 v38 v38 := (r_c hl 4611686018849045331 (of_decide_eq_true rfl))
  have h_v61 : R 1 0 4611686018427387904 4611686018427387904 v61 v61 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v105 : R 1 0 4611686018158952448 4611686018158952448 v105 v105 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have h_v115 : R 1 0 4611686018427387905 4611686018427387905 v115 v115 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have h_v216 : R 1 0 4611686018849045332 4611686018849045332 v216 v216 := (r_c hl 4611686018849045332 (of_decide_eq_true rfl))
  have h_v223 : R 1 0 4611686018849045333 4611686018849045333 v223 v223 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have h_v674 : R 1 0 0 1 v674 v674 := (r_lor hl h_v663 h_v673 (of_decide_eq_true rfl))
  have e_v674 : (v674 = 1 ↔ v663 = 1 ∨ v673 = 1) := e_lor h_v663 h_v673 (of_decide_eq_true rfl)
  have h_v675 : R 1 0 4611686018158952441 4611686018695823367 v675 v675 := (r_psel hl h_v674 h_v110 h_v117 (of_decide_eq_true rfl))
  have e_v675 : v675 = if v674 = 1 then v110 else v117 := e_psel h_v674 h_v110 h_v117 (of_decide_eq_true rfl)
  have h_v676 : R 1 0 0 1 v676 v676 := (r_land hl h_v149 h_v663 (of_decide_eq_true rfl))
  have e_v676 : (v676 = 1 ↔ v149 = 1 ∧ v663 = 1) := e_land h_v149 h_v663 (of_decide_eq_true rfl)
  have h_v677 : R 1 0 0 1 v677 v677 := (r_lor hl h_v148 h_v676 (of_decide_eq_true rfl))
  have e_v677 : (v677 = 1 ↔ v148 = 1 ∨ v676 = 1) := e_lor h_v148 h_v676 (of_decide_eq_true rfl)
  have h_v678 : R 1 0 4611686018427387900 4611686018695823367 v678 v678 := (r_psel hl h_v677 h_v651 h_v658 (of_decide_eq_true rfl))
  have e_v678 : v678 = if v677 = 1 then v651 else v658 := e_psel h_v677 h_v651 h_v658 (of_decide_eq_true rfl)
  clear h_v674 h_v676 h_v677
  have h_v679 : R 1 0 4539628420631363535 4683743616223412273 v679 v679 := (r_smx hl 29 h_v672 h_v668 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v679 : sv v679 = sv v672 * sv v668 := e_smx 29 h_v672 h_v668 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v680 : R 1 0 4611686018158952433 4611686018695823374 v680 v680 := (r_srdF hl h_v679 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl))
  have e_v680 : sv v680 = sv v679 / 2 ^ 28 := e_srdF h_v679 4611686018158952433 4611686018695823374 (of_decide_eq_true rfl)
  have h_v681 : R 1 0 4539628420631363535 4683743616223412273 v681 v681 := (r_smx hl 29 h_v678 h_v675 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v681 : sv v681 = sv v678 * sv v675 := e_smx 29 h_v678 h_v675 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v682 : R 1 0 4611686018158952434 4611686018695823375 v682 v682 := (r_srdC hl h_v681 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl))
  have e_v682 : sv v682 = -((-sv v681) / 2 ^ 28) := e_srdC h_v681 4611686018158952434 4611686018695823375 (of_decide_eq_true rfl)
  have h_v683 : R 1 0 4539628424926330879 4683743614075928569 v683 v683 := (r_smx hl 29 h_v651 h_v117 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl))
  have e_v683 : sv v683 = sv v651 * sv v117 := e_smx 29 h_v651 h_v117 4539628424926330879 4683743614075928569 (of_decide_eq_true rfl)
  have h_v684 : R 1 0 4611686018158952449 4611686018695823365 v684 v684 := (r_srdF hl h_v683 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl))
  have e_v684 : sv v684 = sv v683 / 2 ^ 28 := e_srdF h_v683 4611686018158952449 4611686018695823365 (of_decide_eq_true rfl)
  have h_v685 : R 1 0 4539628422778847239 4683743611928444929 v685 v685 := (r_smx hl 29 h_v651 h_v110 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl))
  have e_v685 : sv v685 = sv v651 * sv v110 := e_smx 29 h_v651 h_v110 4539628422778847239 4683743611928444929 (of_decide_eq_true rfl)
  have h_v686 : R 1 0 4611686018158952443 4611686018695823359 v686 v686 := (r_srdC hl h_v685 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl))
  have e_v686 : sv v686 = -((-sv v685) / 2 ^ 28) := e_srdC h_v685 4611686018158952443 4611686018695823359 (of_decide_eq_true rfl)
  have h_v687 : R 1 0 0 1 v687 v687 := (r_plt hl h_v680 h_v684 (of_decide_eq_true rfl))
  have e_v687 : (v687 = 1 ↔ sv v680 < sv v684) := e_plt h_v680 h_v684 (of_decide_eq_true rfl)
  have h_v688 : R 1 0 4611686018158952433 4611686018695823374 v688 v688 := (r_psel hl h_v687 h_v680 h_v684 (of_decide_eq_true rfl))
  have e_v688 : v688 = if v687 = 1 then v680 else v684 := e_psel h_v687 h_v680 h_v684 (of_decide_eq_true rfl)
  have h_v689 : R 1 0 0 1 v689 v689 := (r_plt hl h_v682 h_v686 (of_decide_eq_true rfl))
  have e_v689 : (v689 = 1 ↔ sv v682 < sv v686) := e_plt h_v682 h_v686 (of_decide_eq_true rfl)
  have h_v690 : R 1 0 4611686018158952434 4611686018695823375 v690 v690 := (r_psel hl h_v689 h_v686 h_v682 (of_decide_eq_true rfl))
  have e_v690 : v690 = if v689 = 1 then v686 else v682 := e_psel h_v689 h_v686 h_v682 (of_decide_eq_true rfl)
  have h_v691 : R 1 0 4611686018158952433 4611686018695823374 v691 v691 := (r_psel hl h_v665 h_v688 h_v680 (of_decide_eq_true rfl))
  clear h_v675 h_v678 h_v679 h_v681 h_v683 h_v684 h_v685 h_v686 h_v687 h_v689
  have e_v691 : v691 = if v665 = 1 then v688 else v680 := e_psel h_v665 h_v688 h_v680 (of_decide_eq_true rfl)
  have h_v692 : R 1 0 4611686018158952434 4611686018695823375 v692 v692 := (r_psel hl h_v665 h_v690 h_v682 (of_decide_eq_true rfl))
  have e_v692 : v692 = if v665 = 1 then v690 else v682 := e_psel h_v665 h_v690 h_v682 (of_decide_eq_true rfl)
  have h_v693 : R 1 0 0 1 v693 v693 := (r_plt hl h_v61 h_v691 (of_decide_eq_true rfl))
  have e_v693 : (v693 = 1 ↔ sv v61 < sv v691) := e_plt h_v61 h_v691 (of_decide_eq_true rfl)
  have h_v694 : R 1 0 0 1 v694 v694 := (r_sub hl (r_O hl) h_v693 (of_decide_eq_true rfl))
  have e_v694 : (v694 = 1 ↔ ¬v693 = 1) := e_not h_v693 (of_decide_eq_true rfl)
  have h_v697 : R 1 0 0 1 v697 v697 := (r_plt hl h_v647 h_v61 (of_decide_eq_true rfl))
  have e_v697 : (v697 = 1 ↔ sv v647 < sv v61) := e_plt h_v647 h_v61 (of_decide_eq_true rfl)
  have h_v698 : R 1 0 4611686018158952433 4611686018695823375 v698 v698 := (r_psel hl h_v697 h_v692 h_v691 (of_decide_eq_true rfl))
  have e_v698 : v698 = if v697 = 1 then v692 else v691 := e_psel h_v697 h_v692 h_v691 (of_decide_eq_true rfl)
  have h_v740 : R 1 0 4611686018158952441 4611686018695823359 v740 v740 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v647 (of_decide_eq_true rfl))
  have e_v740 : sv v740 = sv v61 - sv v647 := e_sub h_v61 h_v647 (of_decide_eq_true rfl)
  have h_v741 : R 1 0 4611686018158952441 4611686018695823367 v741 v741 := (r_psel hl h_v697 h_v740 h_v647 (of_decide_eq_true rfl))
  have e_v741 : v741 = if v697 = 1 then v740 else v647 := e_psel h_v697 h_v740 h_v647 (of_decide_eq_true rfl)
  have h_v742 : R 1 0 4611686018427387904 4611686019501129727 v742 v742 := (r1_hxa hb_H1 32 (of_decide_eq_true rfl))
  have e_v742 : sv v742 = ((H1 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H1 32 (of_decide_eq_true rfl)
  have h_t742_1 : R 1 0 4611686018427387904 4611686018695823363 t742.1 t742.1 := r_sc1 hl h_v742 (of_decide_eq_true rfl)
  have h_t742_2 : R 1 0 4611686018158952445 4611686018695823363 t742.2 t742.2 := r_sc2 hl h_v742 (of_decide_eq_true rfl)
  have e_t742_1 : sv t742.1 = (sc28pS (scArg v742)).1 := e_sc1 h_v742 (of_decide_eq_true rfl)
  have e_t742_2 : sv t742.2 = (sc28pS (scArg v742)).2 := e_sc2 h_v742 (of_decide_eq_true rfl)
  have h_v744 : R 1 0 4611686018158952441 4611686018695823359 v744 v744 := (r_sub hl (r_add hl h_v28 h_t742_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v744 : sv v744 = sv v28 + sv t742.2 := e_add h_v28 h_t742_2 (of_decide_eq_true rfl)
  have h_v745 : R 1 0 0 1 v745 v745 := (r_plt hl h_v744 h_v105 (of_decide_eq_true rfl))
  have e_v745 : (v745 = 1 ↔ sv v744 < sv v105) := e_plt h_v744 h_v105 (of_decide_eq_true rfl)
  clear h_v680 h_v682 h_v688 h_v690 h_v691 h_v692 h_v693 h_v740
  have h_v746 : R 1 0 4611686018158952441 4611686018695823359 v746 v746 := (r_psel hl h_v745 h_v105 h_v744 (of_decide_eq_true rfl))
  have e_v746 : v746 = if v745 = 1 then v105 else v744 := e_psel h_v745 h_v105 h_v744 (of_decide_eq_true rfl)
  have h_v747 : R 1 0 4611686018158952449 4611686018695823367 v747 v747 := (r_sub hl (r_add hl h_v31 h_t742_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v747 : sv v747 = sv v31 + sv t742.2 := e_add h_v31 h_t742_2 (of_decide_eq_true rfl)
  have h_v748 : R 1 0 0 1 v748 v748 := (r_plt hl h_v747 h_v33 (of_decide_eq_true rfl))
  have e_v748 : (v748 = 1 ↔ sv v747 < sv v33) := e_plt h_v747 h_v33 (of_decide_eq_true rfl)
  have h_v749 : R 1 0 4611686018158952449 4611686018695823367 v749 v749 := (r_psel hl h_v748 h_v747 h_v33 (of_decide_eq_true rfl))
  have e_v749 : v749 = if v748 = 1 then v747 else v33 := e_psel h_v748 h_v747 h_v33 (of_decide_eq_true rfl)
  have h_v751 : R 1 0 4611686018427387908 4611686018695823367 v751 v751 := (r_sub hl (r_add hl h_v31 h_t742_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v751 : sv v751 = sv v31 + sv t742.1 := e_add h_v31 h_t742_1 (of_decide_eq_true rfl)
  have h_v752 : R 1 0 0 1 v752 v752 := (r_plt hl h_v751 h_v33 (of_decide_eq_true rfl))
  have e_v752 : (v752 = 1 ↔ sv v751 < sv v33) := e_plt h_v751 h_v33 (of_decide_eq_true rfl)
  have h_v753 : R 1 0 4611686018427387908 4611686018695823367 v753 v753 := (r_psel hl h_v752 h_v751 h_v33 (of_decide_eq_true rfl))
  have e_v753 : v753 = if v752 = 1 then v751 else v33 := e_psel h_v752 h_v751 h_v33 (of_decide_eq_true rfl)
  have h_v754 : R 1 0 4611686018427387900 4611686018695823359 v754 v754 := (r_sub hl (r_add hl h_v28 h_t742_1 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v754 : sv v754 = sv v28 + sv t742.1 := e_add h_v28 h_t742_1 (of_decide_eq_true rfl)
  have h_v755 : R 1 0 4611686018158952441 4611686018695823367 v755 v755 := (r_psel hl h_v697 h_v746 h_v749 (of_decide_eq_true rfl))
  have e_v755 : v755 = if v697 = 1 then v746 else v749 := e_psel h_v697 h_v746 h_v749 (of_decide_eq_true rfl)
  have h_v756 : R 1 0 4611686018427387900 4611686018695823367 v756 v756 := (r_psel hl h_v697 h_v753 h_v754 (of_decide_eq_true rfl))
  have e_v756 : v756 = if v697 = 1 then v753 else v754 := e_psel h_v697 h_v753 h_v754 (of_decide_eq_true rfl)
  have h_v757 : R 1 0 4539628418483879831 4683743618370895977 v757 v757 := (r_smx hl 29 h_v698 h_v756 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl))
  have e_v757 : sv v757 = sv v698 * sv v756 := e_smx 29 h_v698 h_v756 4539628418483879831 4683743618370895977 (of_decide_eq_true rfl)
  have h_v758 : R 1 0 4539628420631363535 4683743616223412273 v758 v758 := (r_smx hl 29 h_v755 h_v741 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl))
  have e_v758 : sv v758 = sv v755 * sv v741 := e_smx 29 h_v755 h_v741 4539628420631363535 4683743616223412273 (of_decide_eq_true rfl)
  have h_v759 : R 1 0 0 1 v759 v759 := (r_plt hl h_v758 h_v757 (of_decide_eq_true rfl))
  clear h_v698 h_v741 h_t742_1 h_t742_2 h_v744 h_v745 h_v747 h_v748 h_v749 h_v751 h_v752 h_v753 h_v754 h_v755 h_v756
  have e_v759 : (v759 = 1 ↔ sv v758 < sv v757) := e_plt h_v758 h_v757 (of_decide_eq_true rfl)
  have h_v760 : R 1 0 0 1 v760 v760 := (r_sub hl (r_O hl) h_v759 (of_decide_eq_true rfl))
  have e_v760 : (v760 = 1 ↔ ¬v759 = 1) := e_not h_v759 (of_decide_eq_true rfl)
  have h_v761 : R 1 0 0 1 v761 v761 := (r_plt hl h_v757 h_v758 (of_decide_eq_true rfl))
  have e_v761 : (v761 = 1 ↔ sv v757 < sv v758) := e_plt h_v757 h_v758 (of_decide_eq_true rfl)
  have h_v762 : R 1 0 0 1 v762 v762 := (r_sub hl (r_O hl) h_v761 (of_decide_eq_true rfl))
  have e_v762 : (v762 = 1 ↔ ¬v761 = 1) := e_not h_v761 (of_decide_eq_true rfl)
  have h_v763 : R 1 0 0 1 v763 v763 := (r_plt hl h_v61 h_v742 (of_decide_eq_true rfl))
  have e_v763 : (v763 = 1 ↔ sv v61 < sv v742) := e_plt h_v61 h_v742 (of_decide_eq_true rfl)
  have h_v764 : R 1 0 0 1 v764 v764 := (r_sub hl (r_O hl) h_v763 (of_decide_eq_true rfl))
  have e_v764 : (v764 = 1 ↔ ¬v763 = 1) := e_not h_v763 (of_decide_eq_true rfl)
  have h_v765 : R 1 0 0 1 v765 v765 := (r_plt hl h_v216 h_v742 (of_decide_eq_true rfl))
  have e_v765 : (v765 = 1 ↔ sv v216 < sv v742) := e_plt h_v216 h_v742 (of_decide_eq_true rfl)
  have h_v766 : R 1 0 0 1 v766 v766 := (r_sub hl (r_O hl) h_v765 (of_decide_eq_true rfl))
  have e_v766 : (v766 = 1 ↔ ¬v765 = 1) := e_not h_v765 (of_decide_eq_true rfl)
  have h_v767 : R 1 0 0 1 v767 v767 := (r_plt hl h_v19 h_v746 (of_decide_eq_true rfl))
  have e_v767 : (v767 = 1 ↔ sv v19 < sv v746) := e_plt h_v19 h_v746 (of_decide_eq_true rfl)
  have h_v768 : R 1 0 0 1 v768 v768 := (r_land hl h_v760 h_v767 (of_decide_eq_true rfl))
  have e_v768 : (v768 = 1 ↔ v760 = 1 ∧ v767 = 1) := e_land h_v760 h_v767 (of_decide_eq_true rfl)
  have h_v769 : R 1 0 0 1 v769 v769 := (r_land hl h_v766 h_v768 (of_decide_eq_true rfl))
  have e_v769 : (v769 = 1 ↔ v766 = 1 ∧ v768 = 1) := e_land h_v766 h_v768 (of_decide_eq_true rfl)
  have h_v770 : R 1 0 0 1 v770 v770 := (r_lor hl h_v764 h_v769 (of_decide_eq_true rfl))
  have e_v770 : (v770 = 1 ↔ v764 = 1 ∨ v769 = 1) := e_lor h_v764 h_v769 (of_decide_eq_true rfl)
  have h_v771 : R 1 0 0 1 v771 v771 := (r_plt hl h_v742 h_v223 (of_decide_eq_true rfl))
  have e_v771 : (v771 = 1 ↔ sv v742 < sv v223) := e_plt h_v742 h_v223 (of_decide_eq_true rfl)
  clear h_v216 h_v746 h_v757 h_v758 h_v759 h_v760 h_v761 h_v763 h_v764 h_v765 h_v766 h_v767 h_v768 h_v769
  have h_v772 : R 1 0 0 1 v772 v772 := (r_sub hl (r_O hl) h_v771 (of_decide_eq_true rfl))
  have e_v772 : (v772 = 1 ↔ ¬v771 = 1) := e_not h_v771 (of_decide_eq_true rfl)
  have h_v773 : R 1 0 0 1 v773 v773 := (r_lor hl h_v762 h_v772 (of_decide_eq_true rfl))
  have e_v773 : (v773 = 1 ↔ v762 = 1 ∨ v772 = 1) := e_lor h_v762 h_v772 (of_decide_eq_true rfl)
  have h_v774 : R 1 0 0 1 v774 v774 := (r_land hl h_v697 h_v770 (of_decide_eq_true rfl))
  have e_v774 : (v774 = 1 ↔ v697 = 1 ∧ v770 = 1) := e_land h_v697 h_v770 (of_decide_eq_true rfl)
  have h_v775 : R 1 0 0 1 v775 v775 := (r_sub hl (r_O hl) h_v697 (of_decide_eq_true rfl))
  have e_v775 : (v775 = 1 ↔ ¬v697 = 1) := e_not h_v697 (of_decide_eq_true rfl)
  have h_v776 : R 1 0 0 1 v776 v776 := (r_land hl h_v773 h_v775 (of_decide_eq_true rfl))
  have e_v776 : (v776 = 1 ↔ v773 = 1 ∧ v775 = 1) := e_land h_v773 h_v775 (of_decide_eq_true rfl)
  have h_v777 : R 1 0 0 1 v777 v777 := (r_lor hl h_v774 h_v776 (of_decide_eq_true rfl))
  have e_v777 : (v777 = 1 ↔ v774 = 1 ∨ v776 = 1) := e_lor h_v774 h_v776 (of_decide_eq_true rfl)
  have h_v778 : R 1 0 4611686017353646081 4611686018427387904 v778 v778 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v742 (of_decide_eq_true rfl))
  have e_v778 : sv v778 = sv v61 - sv v742 := e_sub h_v61 h_v742 (of_decide_eq_true rfl)
  have h_v779 : R 1 0 4611686017353646081 4611686019501129727 v779 v779 := (r_psel hl h_v697 h_v778 h_v742 (of_decide_eq_true rfl))
  have e_v779 : v779 = if v697 = 1 then v778 else v742 := e_psel h_v697 h_v778 h_v742 (of_decide_eq_true rfl)
  have h_v780 : R 1 0 4611686017353646081 4611686019501129727 v780 v780 := (r_psel hl h_v777 h_v779 h_v223 (of_decide_eq_true rfl))
  have e_v780 : v780 = if v777 = 1 then v779 else v223 := e_psel h_v777 h_v779 h_v223 (of_decide_eq_true rfl)
  have h_v782 : R 1 0 4611686017353646081 4611686019501129727 v782 v782 := (r_psel hl h_v694 h_v223 h_v780 (of_decide_eq_true rfl))
  have e_v782 : v782 = if v694 = 1 then v223 else v780 := e_psel h_v694 h_v223 h_v780 (of_decide_eq_true rfl)
  have h_v783 : R 1 0 4611686018427387904 4611686052787126264 v783 v783 := (r_add hl (r_pshr1 hl h_v7) h_H61r (of_decide_eq_true rfl))
  have e_v783 : sv v783 = sv v7 / 2 := e_halfF h_v7
  have h_v784 : R 1 0 4611686018427387904 4611686052787126264 v784 v784 := (r_add hl (r_pshr1 hl (r_add hl h_v7 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v784 : sv v784 = (sv v7 + 1) / 2 := e_halfC h_v7 (of_decide_eq_true rfl)
  have h_v785 : R 1 0 4611686018427387904 4611686052787126264 v785 v785 := (r_psel hl h_v13 h_v784 h_v223 (of_decide_eq_true rfl))
  clear h_H61r h_v7 h_v694 h_v697 h_v742 h_v762 h_v770 h_v771 h_v772 h_v773 h_v774 h_v775 h_v776 h_v777 h_v778 h_v779 h_v780
  have e_v785 : v785 = if v13 = 1 then v784 else v223 := e_psel h_v13 h_v784 h_v223 (of_decide_eq_true rfl)
  have h_v786 : R 1 0 0 1 v786 v786 := (r_plt hl h_v19 h_v783 (of_decide_eq_true rfl))
  have e_v786 : (v786 = 1 ↔ sv v19 < sv v783) := e_plt h_v19 h_v783 (of_decide_eq_true rfl)
  have h_v787 : R 1 0 0 1 v787 v787 := (r_plt hl h_v9 h_v785 (of_decide_eq_true rfl))
  have e_v787 : (v787 = 1 ↔ sv v9 < sv v785) := e_plt h_v9 h_v785 (of_decide_eq_true rfl)
  have h_v788 : R 1 0 0 1 v788 v788 := (r_sub hl (r_O hl) h_v787 (of_decide_eq_true rfl))
  have e_v788 : (v788 = 1 ↔ ¬v787 = 1) := e_not h_v787 (of_decide_eq_true rfl)
  have h_v789 : R 1 0 0 1 v789 v789 := (r_land hl h_v786 h_v788 (of_decide_eq_true rfl))
  have e_v789 : (v789 = 1 ↔ v786 = 1 ∧ v788 = 1) := e_land h_v786 h_v788 (of_decide_eq_true rfl)
  have h_t783_1 : R 1 0 4611686018427387904 4611686018695823363 t783.1 t783.1 := r_sc1 hl h_v783 (of_decide_eq_true rfl)
  have h_t783_2 : R 1 0 4611686018158952445 4611686018695823363 t783.2 t783.2 := r_sc2 hl h_v783 (of_decide_eq_true rfl)
  have e_t783_1 : sv t783.1 = (sc28pS (scArg v783)).1 := e_sc1 h_v783 (of_decide_eq_true rfl)
  have e_t783_2 : sv t783.2 = (sc28pS (scArg v783)).2 := e_sc2 h_v783 (of_decide_eq_true rfl)
  have h_t785_1 : R 1 0 4611686018427387904 4611686018695823363 t785.1 t785.1 := r_sc1 hl h_v785 (of_decide_eq_true rfl)
  have h_t785_2 : R 1 0 4611686018158952445 4611686018695823363 t785.2 t785.2 := r_sc2 hl h_v785 (of_decide_eq_true rfl)
  have e_t785_1 : sv t785.1 = (sc28pS (scArg v785)).1 := e_sc1 h_v785 (of_decide_eq_true rfl)
  have e_t785_2 : sv t785.2 = (sc28pS (scArg v785)).2 := e_sc2 h_v785 (of_decide_eq_true rfl)
  have h_v792 : R 1 0 0 1 v792 v792 := (r_plt hl h_t783_1 h_t785_1 (of_decide_eq_true rfl))
  have e_v792 : (v792 = 1 ↔ sv t783.1 < sv t785.1) := e_plt h_t783_1 h_t785_1 (of_decide_eq_true rfl)
  have h_v793 : R 1 0 4611686018427387904 4611686018695823363 v793 v793 := (r_psel hl h_v792 h_t783_1 h_t785_1 (of_decide_eq_true rfl))
  have e_v793 : v793 = if v792 = 1 then t783.1 else t785.1 := e_psel h_v792 h_t783_1 h_t785_1 (of_decide_eq_true rfl)
  have h_v794 : R 1 0 4611686018427387900 4611686018695823359 v794 v794 := (r_sub hl (r_add hl h_v28 h_v793 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v794 : sv v794 = sv v28 + sv v793 := e_add h_v28 h_v793 (of_decide_eq_true rfl)
  have h_v795 : R 1 0 4611686018427387904 4611686018695823363 v795 v795 := (r_psel hl h_v792 h_t785_1 h_t783_1 (of_decide_eq_true rfl))
  have e_v795 : v795 = if v792 = 1 then t785.1 else t783.1 := e_psel h_v792 h_t785_1 h_t783_1 (of_decide_eq_true rfl)
  clear h_v9 h_v28 h_v223 h_v784 h_v786 h_v787 h_v788 h_t783_1 h_t783_2 e_t783_2 h_t785_1 h_t785_2 e_t785_2 h_v792 h_v793
  have h_v796 : R 1 0 4611686018427387908 4611686018695823367 v796 v796 := (r_sub hl (r_add hl h_v31 h_v795 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v796 : sv v796 = sv v31 + sv v795 := e_add h_v31 h_v795 (of_decide_eq_true rfl)
  have h_v797 : R 1 0 0 1 v797 v797 := (r_plt hl h_v796 h_v33 (of_decide_eq_true rfl))
  have e_v797 : (v797 = 1 ↔ sv v796 < sv v33) := e_plt h_v796 h_v33 (of_decide_eq_true rfl)
  have h_v798 : R 1 0 4611686018427387908 4611686018695823367 v798 v798 := (r_psel hl h_v797 h_v796 h_v33 (of_decide_eq_true rfl))
  have e_v798 : v798 = if v797 = 1 then v796 else v33 := e_psel h_v797 h_v796 h_v33 (of_decide_eq_true rfl)
  have h_v799 : R 1 0 0 1 v799 v799 := (r_plt hl h_v783 h_v36 (of_decide_eq_true rfl))
  have e_v799 : (v799 = 1 ↔ sv v783 < sv v36) := e_plt h_v783 h_v36 (of_decide_eq_true rfl)
  have h_v800 : R 1 0 0 1 v800 v800 := (r_plt hl h_v38 h_v785 (of_decide_eq_true rfl))
  have e_v800 : (v800 = 1 ↔ sv v38 < sv v785) := e_plt h_v38 h_v785 (of_decide_eq_true rfl)
  have h_v801 : R 1 0 0 1 v801 v801 := (r_land hl h_v799 h_v800 (of_decide_eq_true rfl))
  have e_v801 : (v801 = 1 ↔ v799 = 1 ∧ v800 = 1) := e_land h_v799 h_v800 (of_decide_eq_true rfl)
  have h_v802 : R 1 0 4611686018427387908 4611686018695823367 v802 v802 := (r_psel hl h_v801 h_v33 h_v798 (of_decide_eq_true rfl))
  have e_v802 : v802 = if v801 = 1 then v33 else v798 := e_psel h_v801 h_v33 h_v798 (of_decide_eq_true rfl)
  have h_v803 : R 1 0 0 1 v803 v803 := (r_plt hl h_v794 h_v61 (of_decide_eq_true rfl))
  have e_v803 : (v803 = 1 ↔ sv v794 < sv v61) := e_plt h_v794 h_v61 (of_decide_eq_true rfl)
  have h_v805 : R 1 0 0 1 v805 v805 := (r_plt hl h_v61 h_v802 (of_decide_eq_true rfl))
  have e_v805 : (v805 = 1 ↔ sv v61 < sv v802) := e_plt h_v61 h_v802 (of_decide_eq_true rfl)
  have h_v806 : R 1 0 0 1 v806 v806 := (r_sub hl (r_O hl) h_v805 (of_decide_eq_true rfl))
  have e_v806 : (v806 = 1 ↔ ¬v805 = 1) := e_not h_v805 (of_decide_eq_true rfl)
  have h_v807 : R 1 0 0 1 v807 v807 := (r_land hl h_v803 h_v806 (of_decide_eq_true rfl))
  have e_v807 : (v807 = 1 ↔ v803 = 1 ∧ v806 = 1) := e_land h_v803 h_v806 (of_decide_eq_true rfl)
  have h_v808 : R 1 0 0 1 v808 v808 := (r_land hl h_v803 h_v805 (of_decide_eq_true rfl))
  have e_v808 : (v808 = 1 ↔ v803 = 1 ∧ v805 = 1) := e_land h_v803 h_v805 (of_decide_eq_true rfl)
  have h_v809 : R 1 0 0 1 v809 v809 := (r_land hl h_v67 h_v808 (of_decide_eq_true rfl))
  clear h_v31 h_v36 h_v38 h_v783 h_v785 h_v795 h_v796 h_v797 h_v798 h_v799 h_v800 h_v801 h_v803 h_v805 h_v806
  have e_v809 : (v809 = 1 ↔ v67 = 1 ∧ v808 = 1) := e_land h_v67 h_v808 (of_decide_eq_true rfl)
  have h_v810 : R 1 0 0 1 v810 v810 := (r_land hl h_v63 h_v808 (of_decide_eq_true rfl))
  have e_v810 : (v810 = 1 ↔ v63 = 1 ∧ v808 = 1) := e_land h_v63 h_v808 (of_decide_eq_true rfl)
  have h_v811 : R 1 0 0 1 v811 v811 := (r_lor hl h_v807 h_v810 (of_decide_eq_true rfl))
  have e_v811 : (v811 = 1 ↔ v807 = 1 ∨ v810 = 1) := e_lor h_v807 h_v810 (of_decide_eq_true rfl)
  have h_v812 : R 1 0 4611686018427387900 4611686018695823367 v812 v812 := (r_psel hl h_v811 h_v41 h_v29 (of_decide_eq_true rfl))
  have e_v812 : v812 = if v811 = 1 then v41 else v29 := e_psel h_v811 h_v41 h_v29 (of_decide_eq_true rfl)
  have h_v813 : R 1 0 0 1 v813 v813 := (r_sub hl (r_O hl) h_v807 (of_decide_eq_true rfl))
  have e_v813 : (v813 = 1 ↔ ¬v807 = 1) := e_not h_v807 (of_decide_eq_true rfl)
  have h_v814 : R 1 0 0 1 v814 v814 := (r_land hl h_v67 h_v813 (of_decide_eq_true rfl))
  have e_v814 : (v814 = 1 ↔ v67 = 1 ∧ v813 = 1) := e_land h_v67 h_v813 (of_decide_eq_true rfl)
  have h_v815 : R 1 0 0 1 v815 v815 := (r_lor hl h_v66 h_v814 (of_decide_eq_true rfl))
  have e_v815 : (v815 = 1 ↔ v66 = 1 ∨ v814 = 1) := e_lor h_v66 h_v814 (of_decide_eq_true rfl)
  have h_v816 : R 1 0 4611686018427387900 4611686018695823367 v816 v816 := (r_psel hl h_v815 h_v802 h_v794 (of_decide_eq_true rfl))
  have e_v816 : v816 = if v815 = 1 then v802 else v794 := e_psel h_v815 h_v802 h_v794 (of_decide_eq_true rfl)
  have h_v817 : R 1 0 0 1 v817 v817 := (r_land hl h_v66 h_v808 (of_decide_eq_true rfl))
  have e_v817 : (v817 = 1 ↔ v66 = 1 ∧ v808 = 1) := e_land h_v66 h_v808 (of_decide_eq_true rfl)
  have h_v818 : R 1 0 0 1 v818 v818 := (r_lor hl h_v807 h_v817 (of_decide_eq_true rfl))
  have e_v818 : (v818 = 1 ↔ v807 = 1 ∨ v817 = 1) := e_lor h_v807 h_v817 (of_decide_eq_true rfl)
  have h_v819 : R 1 0 4611686018427387900 4611686018695823367 v819 v819 := (r_psel hl h_v818 h_v29 h_v41 (of_decide_eq_true rfl))
  have e_v819 : v819 = if v818 = 1 then v29 else v41 := e_psel h_v818 h_v29 h_v41 (of_decide_eq_true rfl)
  have h_v820 : R 1 0 0 1 v820 v820 := (r_land hl h_v67 h_v807 (of_decide_eq_true rfl))
  have e_v820 : (v820 = 1 ↔ v67 = 1 ∧ v807 = 1) := e_land h_v67 h_v807 (of_decide_eq_true rfl)
  have h_v821 : R 1 0 0 1 v821 v821 := (r_lor hl h_v66 h_v820 (of_decide_eq_true rfl))
  have e_v821 : (v821 = 1 ↔ v66 = 1 ∨ v820 = 1) := e_lor h_v66 h_v820 (of_decide_eq_true rfl)
  clear h_v807 h_v808 h_v810 h_v811 h_v813 h_v814 h_v815 h_v817 h_v818 h_v820
  have h_v822 : R 1 0 4611686018427387900 4611686018695823367 v822 v822 := (r_psel hl h_v821 h_v794 h_v802 (of_decide_eq_true rfl))
  have e_v822 : v822 = if v821 = 1 then v794 else v802 := e_psel h_v821 h_v794 h_v802 (of_decide_eq_true rfl)
  have h_v823 : R 1 0 4611686017353646052 4683743616223412273 v823 v823 := (r_smx hl 29 h_v816 h_v812 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v823 : sv v823 = sv v816 * sv v812 := e_smx 29 h_v816 h_v812 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v824 : R 1 0 4611686018427387899 4611686018695823374 v824 v824 := (r_srdF hl h_v823 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v824 : sv v824 = sv v823 / 2 ^ 28 := e_srdF h_v823 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v825 : R 1 0 4611686017353646052 4683743616223412273 v825 v825 := (r_smx hl 29 h_v822 h_v819 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v825 : sv v825 = sv v822 * sv v819 := e_smx 29 h_v822 h_v819 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v826 : R 1 0 4611686018427387900 4611686018695823375 v826 v826 := (r_srdC hl h_v825 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v826 : sv v826 = -((-sv v825) / 2 ^ 28) := e_srdC h_v825 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v827 : R 1 0 4611686017353646052 4683743614075928569 v827 v827 := (r_smx hl 29 h_v794 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl))
  have e_v827 : sv v827 = sv v794 * sv v41 := e_smx 29 h_v794 h_v41 4611686017353646052 4683743614075928569 (of_decide_eq_true rfl)
  have h_v828 : R 1 0 4611686018427387899 4611686018695823365 v828 v828 := (r_srdF hl h_v827 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl))
  have e_v828 : sv v828 = sv v827 / 2 ^ 28 := e_srdF h_v827 4611686018427387899 4611686018695823365 (of_decide_eq_true rfl)
  have h_v829 : R 1 0 4611686017353646084 4683743611928444929 v829 v829 := (r_smx hl 29 h_v794 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl))
  have e_v829 : sv v829 = sv v794 * sv v29 := e_smx 29 h_v794 h_v29 4611686017353646084 4683743611928444929 (of_decide_eq_true rfl)
  have h_v830 : R 1 0 4611686018427387901 4611686018695823359 v830 v830 := (r_srdC hl h_v829 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl))
  have e_v830 : sv v830 = -((-sv v829) / 2 ^ 28) := e_srdC h_v829 4611686018427387901 4611686018695823359 (of_decide_eq_true rfl)
  have h_v831 : R 1 0 0 1 v831 v831 := (r_plt hl h_v824 h_v828 (of_decide_eq_true rfl))
  have e_v831 : (v831 = 1 ↔ sv v824 < sv v828) := e_plt h_v824 h_v828 (of_decide_eq_true rfl)
  have h_v832 : R 1 0 4611686018427387899 4611686018695823374 v832 v832 := (r_psel hl h_v831 h_v824 h_v828 (of_decide_eq_true rfl))
  have e_v832 : v832 = if v831 = 1 then v824 else v828 := e_psel h_v831 h_v824 h_v828 (of_decide_eq_true rfl)
  have h_v833 : R 1 0 0 1 v833 v833 := (r_plt hl h_v826 h_v830 (of_decide_eq_true rfl))
  have e_v833 : (v833 = 1 ↔ sv v826 < sv v830) := e_plt h_v826 h_v830 (of_decide_eq_true rfl)
  have h_v834 : R 1 0 4611686018427387900 4611686018695823375 v834 v834 := (r_psel hl h_v833 h_v830 h_v826 (of_decide_eq_true rfl))
  clear h_v794 h_v802 h_v812 h_v816 h_v819 h_v821 h_v822 h_v823 h_v825 h_v827 h_v828 h_v829 h_v831
  have e_v834 : v834 = if v833 = 1 then v830 else v826 := e_psel h_v833 h_v830 h_v826 (of_decide_eq_true rfl)
  have h_v835 : R 1 0 4611686018427387899 4611686018695823374 v835 v835 := (r_psel hl h_v809 h_v832 h_v824 (of_decide_eq_true rfl))
  have e_v835 : v835 = if v809 = 1 then v832 else v824 := e_psel h_v809 h_v832 h_v824 (of_decide_eq_true rfl)
  have h_v836 : R 1 0 4611686018427387900 4611686018695823375 v836 v836 := (r_psel hl h_v809 h_v834 h_v826 (of_decide_eq_true rfl))
  have e_v836 : v836 = if v809 = 1 then v834 else v826 := e_psel h_v809 h_v834 h_v826 (of_decide_eq_true rfl)
  have h_v837 : R 1 0 0 1 v837 v837 := (r_plt hl h_v19 h_v835 (of_decide_eq_true rfl))
  have e_v837 : (v837 = 1 ↔ sv v19 < sv v835) := e_plt h_v19 h_v835 (of_decide_eq_true rfl)
  have h_v838 : R 1 0 0 1 v838 v838 := (r_plt hl h_v61 h_v479 (of_decide_eq_true rfl))
  have e_v838 : (v838 = 1 ↔ sv v61 < sv v479) := e_plt h_v61 h_v479 (of_decide_eq_true rfl)
  have h_v839 : R 1 0 0 1 v839 v839 := (r_plt hl h_v480 h_v33 (of_decide_eq_true rfl))
  have e_v839 : (v839 = 1 ↔ sv v480 < sv v33) := e_plt h_v480 h_v33 (of_decide_eq_true rfl)
  have h_v840 : R 1 0 0 1 v840 v840 := (r_land hl h_v838 h_v839 (of_decide_eq_true rfl))
  have e_v840 : (v840 = 1 ↔ v838 = 1 ∧ v839 = 1) := e_land h_v838 h_v839 (of_decide_eq_true rfl)
  have h_v841 : R 1 0 0 1 v841 v841 := (r_plt hl h_v61 h_v100 (of_decide_eq_true rfl))
  have e_v841 : (v841 = 1 ↔ sv v61 < sv v100) := e_plt h_v61 h_v100 (of_decide_eq_true rfl)
  have h_v842 : R 1 0 0 1 v842 v842 := (r_plt hl h_v101 h_v33 (of_decide_eq_true rfl))
  have e_v842 : (v842 = 1 ↔ sv v101 < sv v33) := e_plt h_v101 h_v33 (of_decide_eq_true rfl)
  have h_v843 : R 1 0 0 1 v843 v843 := (r_land hl h_v841 h_v842 (of_decide_eq_true rfl))
  have e_v843 : (v843 = 1 ↔ v841 = 1 ∧ v842 = 1) := e_land h_v841 h_v842 (of_decide_eq_true rfl)
  have h_v844 : R 1 0 0 1 v844 v844 := (r_plt hl h_v61 h_v835 (of_decide_eq_true rfl))
  have e_v844 : (v844 = 1 ↔ sv v61 < sv v835) := e_plt h_v61 h_v835 (of_decide_eq_true rfl)
  have h_v845 : R 1 0 0 1 v845 v845 := (r_plt hl h_v836 h_v33 (of_decide_eq_true rfl))
  have e_v845 : (v845 = 1 ↔ sv v836 < sv v33) := e_plt h_v836 h_v33 (of_decide_eq_true rfl)
  have h_v846 : R 1 0 0 1 v846 v846 := (r_land hl h_v844 h_v845 (of_decide_eq_true rfl))
  have e_v846 : (v846 = 1 ↔ v844 = 1 ∧ v845 = 1) := e_land h_v844 h_v845 (of_decide_eq_true rfl)
  clear h_v19 h_v809 h_v824 h_v826 h_v830 h_v832 h_v833 h_v834 h_v838 h_v839 h_v841 h_v842 h_v844 h_v845
  have h_v847 : R 1 0 0 1 v847 v847 := (r_land hl h_v840 h_v843 (of_decide_eq_true rfl))
  have e_v847 : (v847 = 1 ↔ v840 = 1 ∧ v843 = 1) := e_land h_v840 h_v843 (of_decide_eq_true rfl)
  have h_v848 : R 1 0 0 1 v848 v848 := (r_land hl h_v846 h_v847 (of_decide_eq_true rfl))
  have e_v848 : (v848 = 1 ↔ v846 = 1 ∧ v847 = 1) := e_land h_v846 h_v847 (of_decide_eq_true rfl)
  have h_v849 : R 1 0 4611686018427387904 4683743620518379745 v849 v849 := (r_smx_sq hl 29 h_v480 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v849 : sv v849 = sv v480 * sv v480 := e_smx_sq 29 h_v480 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v850 : R 1 0 4611686018427387904 4611686018695823391 v850 v850 := (r_srdC hl h_v849 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v850 : sv v850 = -((-sv v849) / 2 ^ 28) := e_srdC h_v849 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v851 : R 1 0 4611686018427387904 4611686018964258878 v851 v851 := (r_sub hl (r_add hl h_v850 h_v850 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v851 : sv v851 = sv v850 + sv v850 := e_add h_v850 h_v850 (of_decide_eq_true rfl)
  have h_v852 : R 1 0 4611686018158952386 4611686018695823360 v852 v852 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v851 (of_decide_eq_true rfl))
  have e_v852 : sv v852 = sv v33 - sv v851 := e_sub h_v33 h_v851 (of_decide_eq_true rfl)
  have h_v853 : R 1 0 0 1 v853 v853 := (r_plt hl h_v852 h_v105 (of_decide_eq_true rfl))
  have e_v853 : (v853 = 1 ↔ sv v852 < sv v105) := e_plt h_v852 h_v105 (of_decide_eq_true rfl)
  have h_v854 : R 1 0 4611686018158952386 4611686018695823360 v854 v854 := (r_psel hl h_v853 h_v105 h_v852 (of_decide_eq_true rfl))
  have e_v854 : v854 = if v853 = 1 then v105 else v852 := e_psel h_v853 h_v105 h_v852 (of_decide_eq_true rfl)
  have h_v855 : R 1 0 4611686018427387904 4683743619981508804 v855 v855 := (r_smx_sq hl 29 h_v479 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v855 : sv v855 = sv v479 * sv v479 := e_smx_sq 29 h_v479 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v856 : R 1 0 4611686018427387904 4611686018695823388 v856 v856 := (r_srdF hl h_v855 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v856 : sv v856 = sv v855 / 2 ^ 28 := e_srdF h_v855 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v857 : R 1 0 4611686018427387904 4611686018964258872 v857 v857 := (r_sub hl (r_add hl h_v856 h_v856 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v857 : sv v857 = sv v856 + sv v856 := e_add h_v856 h_v856 (of_decide_eq_true rfl)
  have h_v858 : R 1 0 4611686018158952392 4611686018695823360 v858 v858 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v857 (of_decide_eq_true rfl))
  have e_v858 : sv v858 = sv v33 - sv v857 := e_sub h_v33 h_v857 (of_decide_eq_true rfl)
  have h_v859 : R 1 0 4611686018427387904 4683743620518379745 v859 v859 := (r_smx_sq hl 29 h_v836 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  clear h_v840 h_v843 h_v847 h_v849 h_v850 h_v851 h_v852 h_v853 h_v855 h_v856 h_v857
  have e_v859 : sv v859 = sv v836 * sv v836 := e_smx_sq 29 h_v836 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v860 : R 1 0 4611686018427387904 4611686018695823391 v860 v860 := (r_srdC hl h_v859 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v860 : sv v860 = -((-sv v859) / 2 ^ 28) := e_srdC h_v859 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v861 : R 1 0 4611686018427387904 4611686018964258878 v861 v861 := (r_sub hl (r_add hl h_v860 h_v860 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v861 : sv v861 = sv v860 + sv v860 := e_add h_v860 h_v860 (of_decide_eq_true rfl)
  have h_v862 : R 1 0 4611686018158952386 4611686018695823360 v862 v862 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v861 (of_decide_eq_true rfl))
  have e_v862 : sv v862 = sv v33 - sv v861 := e_sub h_v33 h_v861 (of_decide_eq_true rfl)
  have h_v863 : R 1 0 0 1 v863 v863 := (r_plt hl h_v862 h_v105 (of_decide_eq_true rfl))
  have e_v863 : (v863 = 1 ↔ sv v862 < sv v105) := e_plt h_v862 h_v105 (of_decide_eq_true rfl)
  have h_v864 : R 1 0 4611686018158952386 4611686018695823360 v864 v864 := (r_psel hl h_v863 h_v105 h_v862 (of_decide_eq_true rfl))
  have e_v864 : v864 = if v863 = 1 then v105 else v862 := e_psel h_v863 h_v105 h_v862 (of_decide_eq_true rfl)
  have h_v865 : R 1 0 4611686018427387904 4683743619981508804 v865 v865 := (r_smx_sq hl 29 h_v835 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v865 : sv v865 = sv v835 * sv v835 := e_smx_sq 29 h_v835 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v866 : R 1 0 4611686018427387904 4611686018695823388 v866 v866 := (r_srdF hl h_v865 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v866 : sv v866 = sv v865 / 2 ^ 28 := e_srdF h_v865 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v867 : R 1 0 4611686018427387904 4611686018964258872 v867 v867 := (r_sub hl (r_add hl h_v866 h_v866 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v867 : sv v867 = sv v866 + sv v866 := e_add h_v866 h_v866 (of_decide_eq_true rfl)
  have h_v868 : R 1 0 4611686018158952392 4611686018695823360 v868 v868 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v867 (of_decide_eq_true rfl))
  have e_v868 : sv v868 = sv v33 - sv v867 := e_sub h_v33 h_v867 (of_decide_eq_true rfl)
  have h_v869 : R 1 0 4611686018427387904 4683743620518379745 v869 v869 := (r_smx_sq hl 29 h_v101 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v869 : sv v869 = sv v101 * sv v101 := e_smx_sq 29 h_v101 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v870 : R 1 0 4611686018427387904 4611686018695823391 v870 v870 := (r_srdC hl h_v869 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v870 : sv v870 = -((-sv v869) / 2 ^ 28) := e_srdC h_v869 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v871 : R 1 0 4611686018427387904 4611686018964258878 v871 v871 := (r_sub hl (r_add hl h_v870 h_v870 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v871 : sv v871 = sv v870 + sv v870 := e_add h_v870 h_v870 (of_decide_eq_true rfl)
  clear h_v859 h_v860 h_v861 h_v862 h_v863 h_v865 h_v866 h_v867 h_v869 h_v870
  have h_v872 : R 1 0 4611686018158952386 4611686018695823360 v872 v872 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v871 (of_decide_eq_true rfl))
  have e_v872 : sv v872 = sv v33 - sv v871 := e_sub h_v33 h_v871 (of_decide_eq_true rfl)
  have h_v873 : R 1 0 0 1 v873 v873 := (r_plt hl h_v872 h_v105 (of_decide_eq_true rfl))
  have e_v873 : (v873 = 1 ↔ sv v872 < sv v105) := e_plt h_v872 h_v105 (of_decide_eq_true rfl)
  have h_v874 : R 1 0 4611686018158952386 4611686018695823360 v874 v874 := (r_psel hl h_v873 h_v105 h_v872 (of_decide_eq_true rfl))
  have e_v874 : v874 = if v873 = 1 then v105 else v872 := e_psel h_v873 h_v105 h_v872 (of_decide_eq_true rfl)
  have h_v875 : R 1 0 4611686018427387904 4683743619981508804 v875 v875 := (r_smx_sq hl 29 h_v100 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v875 : sv v875 = sv v100 * sv v100 := e_smx_sq 29 h_v100 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v876 : R 1 0 4611686018427387904 4611686018695823388 v876 v876 := (r_srdF hl h_v875 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v876 : sv v876 = sv v875 / 2 ^ 28 := e_srdF h_v875 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v877 : R 1 0 4611686018427387904 4611686018964258872 v877 v877 := (r_sub hl (r_add hl h_v876 h_v876 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v877 : sv v877 = sv v876 + sv v876 := e_add h_v876 h_v876 (of_decide_eq_true rfl)
  have h_v878 : R 1 0 4611686018158952392 4611686018695823360 v878 v878 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v877 (of_decide_eq_true rfl))
  have e_v878 : sv v878 = sv v33 - sv v877 := e_sub h_v33 h_v877 (of_decide_eq_true rfl)
  have h_v879 : R 1 0 0 1 v879 v879 := (r_plt hl h_v854 h_v61 (of_decide_eq_true rfl))
  have e_v879 : (v879 = 1 ↔ sv v854 < sv v61) := e_plt h_v854 h_v61 (of_decide_eq_true rfl)
  have h_v880 : R 1 0 0 1 v880 v880 := (r_sub hl (r_O hl) h_v879 (of_decide_eq_true rfl))
  have e_v880 : (v880 = 1 ↔ ¬v879 = 1) := e_not h_v879 (of_decide_eq_true rfl)
  have h_v881 : R 1 0 0 1 v881 v881 := (r_plt hl h_v61 h_v858 (of_decide_eq_true rfl))
  have e_v881 : (v881 = 1 ↔ sv v61 < sv v858) := e_plt h_v61 h_v858 (of_decide_eq_true rfl)
  have h_v882 : R 1 0 0 1 v882 v882 := (r_sub hl (r_O hl) h_v881 (of_decide_eq_true rfl))
  have e_v882 : (v882 = 1 ↔ ¬v881 = 1) := e_not h_v881 (of_decide_eq_true rfl)
  have h_v883 : R 1 0 0 1 v883 v883 := (r_land hl h_v879 h_v882 (of_decide_eq_true rfl))
  have e_v883 : (v883 = 1 ↔ v879 = 1 ∧ v882 = 1) := e_land h_v879 h_v882 (of_decide_eq_true rfl)
  have h_v884 : R 1 0 0 1 v884 v884 := (r_land hl h_v879 h_v881 (of_decide_eq_true rfl))
  clear h_v871 h_v872 h_v873 h_v875 h_v876 h_v877 h_v882
  have e_v884 : (v884 = 1 ↔ v879 = 1 ∧ v881 = 1) := e_land h_v879 h_v881 (of_decide_eq_true rfl)
  have h_v885 : R 1 0 0 1 v885 v885 := (r_plt hl h_v874 h_v61 (of_decide_eq_true rfl))
  have e_v885 : (v885 = 1 ↔ sv v874 < sv v61) := e_plt h_v874 h_v61 (of_decide_eq_true rfl)
  have h_v886 : R 1 0 0 1 v886 v886 := (r_sub hl (r_O hl) h_v885 (of_decide_eq_true rfl))
  have e_v886 : (v886 = 1 ↔ ¬v885 = 1) := e_not h_v885 (of_decide_eq_true rfl)
  have h_v887 : R 1 0 0 1 v887 v887 := (r_plt hl h_v61 h_v878 (of_decide_eq_true rfl))
  have e_v887 : (v887 = 1 ↔ sv v61 < sv v878) := e_plt h_v61 h_v878 (of_decide_eq_true rfl)
  have h_v888 : R 1 0 0 1 v888 v888 := (r_sub hl (r_O hl) h_v887 (of_decide_eq_true rfl))
  have e_v888 : (v888 = 1 ↔ ¬v887 = 1) := e_not h_v887 (of_decide_eq_true rfl)
  have h_v889 : R 1 0 0 1 v889 v889 := (r_land hl h_v885 h_v888 (of_decide_eq_true rfl))
  have e_v889 : (v889 = 1 ↔ v885 = 1 ∧ v888 = 1) := e_land h_v885 h_v888 (of_decide_eq_true rfl)
  have h_v890 : R 1 0 0 1 v890 v890 := (r_land hl h_v885 h_v887 (of_decide_eq_true rfl))
  have e_v890 : (v890 = 1 ↔ v885 = 1 ∧ v887 = 1) := e_land h_v885 h_v887 (of_decide_eq_true rfl)
  have h_v891 : R 1 0 0 1 v891 v891 := (r_land hl h_v884 h_v890 (of_decide_eq_true rfl))
  have e_v891 : (v891 = 1 ↔ v884 = 1 ∧ v890 = 1) := e_land h_v884 h_v890 (of_decide_eq_true rfl)
  have h_v892 : R 1 0 0 1 v892 v892 := (r_land hl h_v880 h_v890 (of_decide_eq_true rfl))
  have e_v892 : (v892 = 1 ↔ v880 = 1 ∧ v890 = 1) := e_land h_v880 h_v890 (of_decide_eq_true rfl)
  have h_v893 : R 1 0 0 1 v893 v893 := (r_lor hl h_v889 h_v892 (of_decide_eq_true rfl))
  have e_v893 : (v893 = 1 ↔ v889 = 1 ∨ v892 = 1) := e_lor h_v889 h_v892 (of_decide_eq_true rfl)
  have h_v894 : R 1 0 4611686018158952386 4611686018695823360 v894 v894 := (r_psel hl h_v893 h_v858 h_v854 (of_decide_eq_true rfl))
  have e_v894 : v894 = if v893 = 1 then v858 else v854 := e_psel h_v893 h_v858 h_v854 (of_decide_eq_true rfl)
  have h_v895 : R 1 0 0 1 v895 v895 := (r_sub hl (r_O hl) h_v889 (of_decide_eq_true rfl))
  have e_v895 : (v895 = 1 ↔ ¬v889 = 1) := e_not h_v889 (of_decide_eq_true rfl)
  have h_v896 : R 1 0 0 1 v896 v896 := (r_land hl h_v884 h_v895 (of_decide_eq_true rfl))
  have e_v896 : (v896 = 1 ↔ v884 = 1 ∧ v895 = 1) := e_land h_v884 h_v895 (of_decide_eq_true rfl)
  clear h_v879 h_v881 h_v885 h_v887 h_v888 h_v892 h_v893 h_v895
  have h_v897 : R 1 0 0 1 v897 v897 := (r_lor hl h_v883 h_v896 (of_decide_eq_true rfl))
  have e_v897 : (v897 = 1 ↔ v883 = 1 ∨ v896 = 1) := e_lor h_v883 h_v896 (of_decide_eq_true rfl)
  have h_v898 : R 1 0 4611686018158952386 4611686018695823360 v898 v898 := (r_psel hl h_v897 h_v878 h_v874 (of_decide_eq_true rfl))
  have e_v898 : v898 = if v897 = 1 then v878 else v874 := e_psel h_v897 h_v878 h_v874 (of_decide_eq_true rfl)
  have h_v899 : R 1 0 0 1 v899 v899 := (r_land hl h_v883 h_v890 (of_decide_eq_true rfl))
  have e_v899 : (v899 = 1 ↔ v883 = 1 ∧ v890 = 1) := e_land h_v883 h_v890 (of_decide_eq_true rfl)
  have h_v900 : R 1 0 0 1 v900 v900 := (r_lor hl h_v889 h_v899 (of_decide_eq_true rfl))
  have e_v900 : (v900 = 1 ↔ v889 = 1 ∨ v899 = 1) := e_lor h_v889 h_v899 (of_decide_eq_true rfl)
  have h_v901 : R 1 0 4611686018158952386 4611686018695823360 v901 v901 := (r_psel hl h_v900 h_v854 h_v858 (of_decide_eq_true rfl))
  have e_v901 : v901 = if v900 = 1 then v854 else v858 := e_psel h_v900 h_v854 h_v858 (of_decide_eq_true rfl)
  have h_v902 : R 1 0 0 1 v902 v902 := (r_land hl h_v884 h_v889 (of_decide_eq_true rfl))
  have e_v902 : (v902 = 1 ↔ v884 = 1 ∧ v889 = 1) := e_land h_v884 h_v889 (of_decide_eq_true rfl)
  have h_v903 : R 1 0 0 1 v903 v903 := (r_lor hl h_v883 h_v902 (of_decide_eq_true rfl))
  have e_v903 : (v903 = 1 ↔ v883 = 1 ∨ v902 = 1) := e_lor h_v883 h_v902 (of_decide_eq_true rfl)
  have h_v904 : R 1 0 4611686018158952386 4611686018695823360 v904 v904 := (r_psel hl h_v903 h_v874 h_v878 (of_decide_eq_true rfl))
  have e_v904 : v904 = if v903 = 1 then v874 else v878 := e_psel h_v903 h_v874 h_v878 (of_decide_eq_true rfl)
  have h_v905 : R 1 0 4539628407746461696 4683743645751316228 v905 v905 := (r_smx hl 30 h_v898 h_v894 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v905 : sv v905 = sv v898 * sv v894 := e_smx 30 h_v898 h_v894 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v906 : R 1 0 4611686018158952386 4611686018695823484 v906 v906 := (r_srdF hl h_v905 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v906 : sv v906 = sv v905 / 2 ^ 28 := e_srdF h_v905 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v907 : R 1 0 4539628407746461696 4683743645751316228 v907 v907 := (r_smx hl 30 h_v904 h_v901 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v907 : sv v907 = sv v904 * sv v901 := e_smx 30 h_v904 h_v901 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v908 : R 1 0 4611686018158952386 4611686018695823485 v908 v908 := (r_srdC hl h_v907 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v908 : sv v908 = -((-sv v907) / 2 ^ 28) := e_srdC h_v907 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v909 : R 1 0 4539628407746461696 4683743644140703120 v909 v909 := (r_smx hl 30 h_v874 h_v858 4539628407746461696 4683743644140703120 (of_decide_eq_true rfl))
  clear h_v894 h_v896 h_v897 h_v898 h_v899 h_v900 h_v901 h_v902 h_v903 h_v904 h_v905 h_v907
  have e_v909 : sv v909 = sv v874 * sv v858 := e_smx 30 h_v874 h_v858 4539628407746461696 4683743644140703120 (of_decide_eq_true rfl)
  have h_v910 : R 1 0 4611686018158952386 4611686018695823478 v910 v910 := (r_srdF hl h_v909 4611686018158952386 4611686018695823478 (of_decide_eq_true rfl))
  have e_v910 : sv v910 = sv v909 / 2 ^ 28 := e_srdF h_v909 4611686018158952386 4611686018695823478 (of_decide_eq_true rfl)
  have h_v911 : R 1 0 4539628407746461696 4683743645751316228 v911 v911 := (r_smx hl 30 h_v874 h_v854 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v911 : sv v911 = sv v874 * sv v854 := e_smx 30 h_v874 h_v854 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v912 : R 1 0 4611686018158952386 4611686018695823485 v912 v912 := (r_srdC hl h_v911 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v912 : sv v912 = -((-sv v911) / 2 ^ 28) := e_srdC h_v911 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v913 : R 1 0 0 1 v913 v913 := (r_plt hl h_v906 h_v910 (of_decide_eq_true rfl))
  have e_v913 : (v913 = 1 ↔ sv v906 < sv v910) := e_plt h_v906 h_v910 (of_decide_eq_true rfl)
  have h_v914 : R 1 0 4611686018158952386 4611686018695823484 v914 v914 := (r_psel hl h_v913 h_v906 h_v910 (of_decide_eq_true rfl))
  have e_v914 : v914 = if v913 = 1 then v906 else v910 := e_psel h_v913 h_v906 h_v910 (of_decide_eq_true rfl)
  have h_v915 : R 1 0 0 1 v915 v915 := (r_plt hl h_v908 h_v912 (of_decide_eq_true rfl))
  have e_v915 : (v915 = 1 ↔ sv v908 < sv v912) := e_plt h_v908 h_v912 (of_decide_eq_true rfl)
  have h_v916 : R 1 0 4611686018158952386 4611686018695823485 v916 v916 := (r_psel hl h_v915 h_v912 h_v908 (of_decide_eq_true rfl))
  have e_v916 : v916 = if v915 = 1 then v912 else v908 := e_psel h_v915 h_v912 h_v908 (of_decide_eq_true rfl)
  have h_v917 : R 1 0 4611686018158952386 4611686018695823484 v917 v917 := (r_psel hl h_v891 h_v914 h_v906 (of_decide_eq_true rfl))
  have e_v917 : v917 = if v891 = 1 then v914 else v906 := e_psel h_v891 h_v914 h_v906 (of_decide_eq_true rfl)
  have h_v918 : R 1 0 4611686018158952386 4611686018695823485 v918 v918 := (r_psel hl h_v891 h_v916 h_v908 (of_decide_eq_true rfl))
  have e_v918 : v918 = if v891 = 1 then v916 else v908 := e_psel h_v891 h_v916 h_v908 (of_decide_eq_true rfl)
  have h_v919 : R 1 0 4611686017890516805 4611686018964258878 v919 v919 := (r_sub hl (r_add hl h_v864 h_OFFr (of_decide_eq_true rfl)) h_v918 (of_decide_eq_true rfl))
  have e_v919 : sv v919 = sv v864 - sv v918 := e_sub h_v864 h_v918 (of_decide_eq_true rfl)
  have h_v920 : R 1 0 4611686017890516812 4611686018964258878 v920 v920 := (r_sub hl (r_add hl h_v868 h_OFFr (of_decide_eq_true rfl)) h_v917 (of_decide_eq_true rfl))
  have e_v920 : sv v920 = sv v868 - sv v917 := e_sub h_v868 h_v917 (of_decide_eq_true rfl)
  have h_v921 : R 1 0 0 1 v921 v921 := (r_plt hl h_v864 h_v61 (of_decide_eq_true rfl))
  have e_v921 : (v921 = 1 ↔ sv v864 < sv v61) := e_plt h_v864 h_v61 (of_decide_eq_true rfl)
  clear h_v906 h_v908 h_v909 h_v910 h_v911 h_v912 h_v913 h_v914 h_v915 h_v916 h_v917 h_v918
  have h_v922 : R 1 0 0 1 v922 v922 := (r_sub hl (r_O hl) h_v921 (of_decide_eq_true rfl))
  have e_v922 : (v922 = 1 ↔ ¬v921 = 1) := e_not h_v921 (of_decide_eq_true rfl)
  have h_v923 : R 1 0 0 1 v923 v923 := (r_plt hl h_v61 h_v868 (of_decide_eq_true rfl))
  have e_v923 : (v923 = 1 ↔ sv v61 < sv v868) := e_plt h_v61 h_v868 (of_decide_eq_true rfl)
  have h_v924 : R 1 0 0 1 v924 v924 := (r_sub hl (r_O hl) h_v923 (of_decide_eq_true rfl))
  have e_v924 : (v924 = 1 ↔ ¬v923 = 1) := e_not h_v923 (of_decide_eq_true rfl)
  have h_v925 : R 1 0 0 1 v925 v925 := (r_land hl h_v921 h_v924 (of_decide_eq_true rfl))
  have e_v925 : (v925 = 1 ↔ v921 = 1 ∧ v924 = 1) := e_land h_v921 h_v924 (of_decide_eq_true rfl)
  have h_v926 : R 1 0 0 1 v926 v926 := (r_land hl h_v921 h_v923 (of_decide_eq_true rfl))
  have e_v926 : (v926 = 1 ↔ v921 = 1 ∧ v923 = 1) := e_land h_v921 h_v923 (of_decide_eq_true rfl)
  have h_v927 : R 1 0 0 1 v927 v927 := (r_land hl h_v884 h_v926 (of_decide_eq_true rfl))
  have e_v927 : (v927 = 1 ↔ v884 = 1 ∧ v926 = 1) := e_land h_v884 h_v926 (of_decide_eq_true rfl)
  have h_v928 : R 1 0 0 1 v928 v928 := (r_land hl h_v880 h_v926 (of_decide_eq_true rfl))
  have e_v928 : (v928 = 1 ↔ v880 = 1 ∧ v926 = 1) := e_land h_v880 h_v926 (of_decide_eq_true rfl)
  have h_v929 : R 1 0 0 1 v929 v929 := (r_lor hl h_v925 h_v928 (of_decide_eq_true rfl))
  have e_v929 : (v929 = 1 ↔ v925 = 1 ∨ v928 = 1) := e_lor h_v925 h_v928 (of_decide_eq_true rfl)
  have h_v930 : R 1 0 4611686018158952386 4611686018695823360 v930 v930 := (r_psel hl h_v929 h_v858 h_v854 (of_decide_eq_true rfl))
  have e_v930 : v930 = if v929 = 1 then v858 else v854 := e_psel h_v929 h_v858 h_v854 (of_decide_eq_true rfl)
  have h_v931 : R 1 0 0 1 v931 v931 := (r_sub hl (r_O hl) h_v925 (of_decide_eq_true rfl))
  have e_v931 : (v931 = 1 ↔ ¬v925 = 1) := e_not h_v925 (of_decide_eq_true rfl)
  have h_v932 : R 1 0 0 1 v932 v932 := (r_land hl h_v884 h_v931 (of_decide_eq_true rfl))
  have e_v932 : (v932 = 1 ↔ v884 = 1 ∧ v931 = 1) := e_land h_v884 h_v931 (of_decide_eq_true rfl)
  have h_v933 : R 1 0 0 1 v933 v933 := (r_lor hl h_v883 h_v932 (of_decide_eq_true rfl))
  have e_v933 : (v933 = 1 ↔ v883 = 1 ∨ v932 = 1) := e_lor h_v883 h_v932 (of_decide_eq_true rfl)
  have h_v934 : R 1 0 4611686018158952386 4611686018695823360 v934 v934 := (r_psel hl h_v933 h_v868 h_v864 (of_decide_eq_true rfl))
  clear h_v880 h_v921 h_v923 h_v924 h_v928 h_v929 h_v932
  have e_v934 : v934 = if v933 = 1 then v868 else v864 := e_psel h_v933 h_v868 h_v864 (of_decide_eq_true rfl)
  have h_v935 : R 1 0 0 1 v935 v935 := (r_land hl h_v883 h_v926 (of_decide_eq_true rfl))
  have e_v935 : (v935 = 1 ↔ v883 = 1 ∧ v926 = 1) := e_land h_v883 h_v926 (of_decide_eq_true rfl)
  have h_v936 : R 1 0 0 1 v936 v936 := (r_lor hl h_v925 h_v935 (of_decide_eq_true rfl))
  have e_v936 : (v936 = 1 ↔ v925 = 1 ∨ v935 = 1) := e_lor h_v925 h_v935 (of_decide_eq_true rfl)
  have h_v937 : R 1 0 4611686018158952386 4611686018695823360 v937 v937 := (r_psel hl h_v936 h_v854 h_v858 (of_decide_eq_true rfl))
  have e_v937 : v937 = if v936 = 1 then v854 else v858 := e_psel h_v936 h_v854 h_v858 (of_decide_eq_true rfl)
  have h_v938 : R 1 0 0 1 v938 v938 := (r_land hl h_v884 h_v925 (of_decide_eq_true rfl))
  have e_v938 : (v938 = 1 ↔ v884 = 1 ∧ v925 = 1) := e_land h_v884 h_v925 (of_decide_eq_true rfl)
  have h_v939 : R 1 0 0 1 v939 v939 := (r_lor hl h_v883 h_v938 (of_decide_eq_true rfl))
  have e_v939 : (v939 = 1 ↔ v883 = 1 ∨ v938 = 1) := e_lor h_v883 h_v938 (of_decide_eq_true rfl)
  have h_v940 : R 1 0 4611686018158952386 4611686018695823360 v940 v940 := (r_psel hl h_v939 h_v864 h_v868 (of_decide_eq_true rfl))
  have e_v940 : v940 = if v939 = 1 then v864 else v868 := e_psel h_v939 h_v864 h_v868 (of_decide_eq_true rfl)
  have h_v941 : R 1 0 4539628407746461696 4683743645751316228 v941 v941 := (r_smx hl 30 h_v934 h_v930 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v941 : sv v941 = sv v934 * sv v930 := e_smx 30 h_v934 h_v930 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v942 : R 1 0 4611686018158952386 4611686018695823484 v942 v942 := (r_srdF hl h_v941 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v942 : sv v942 = sv v941 / 2 ^ 28 := e_srdF h_v941 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v943 : R 1 0 4539628407746461696 4683743645751316228 v943 v943 := (r_smx hl 30 h_v940 h_v937 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v943 : sv v943 = sv v940 * sv v937 := e_smx 30 h_v940 h_v937 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v944 : R 1 0 4611686018158952386 4611686018695823485 v944 v944 := (r_srdC hl h_v943 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v944 : sv v944 = -((-sv v943) / 2 ^ 28) := e_srdC h_v943 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v945 : R 1 0 4539628407746461696 4683743644140703120 v945 v945 := (r_smx hl 30 h_v864 h_v858 4539628407746461696 4683743644140703120 (of_decide_eq_true rfl))
  have e_v945 : sv v945 = sv v864 * sv v858 := e_smx 30 h_v864 h_v858 4539628407746461696 4683743644140703120 (of_decide_eq_true rfl)
  have h_v946 : R 1 0 4611686018158952386 4611686018695823478 v946 v946 := (r_srdF hl h_v945 4611686018158952386 4611686018695823478 (of_decide_eq_true rfl))
  have e_v946 : sv v946 = sv v945 / 2 ^ 28 := e_srdF h_v945 4611686018158952386 4611686018695823478 (of_decide_eq_true rfl)
  clear h_v930 h_v933 h_v934 h_v935 h_v936 h_v937 h_v938 h_v939 h_v940 h_v941 h_v943 h_v945
  have h_v947 : R 1 0 4539628407746461696 4683743645751316228 v947 v947 := (r_smx hl 30 h_v864 h_v854 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v947 : sv v947 = sv v864 * sv v854 := e_smx 30 h_v864 h_v854 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v948 : R 1 0 4611686018158952386 4611686018695823485 v948 v948 := (r_srdC hl h_v947 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v948 : sv v948 = -((-sv v947) / 2 ^ 28) := e_srdC h_v947 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v949 : R 1 0 0 1 v949 v949 := (r_plt hl h_v942 h_v946 (of_decide_eq_true rfl))
  have e_v949 : (v949 = 1 ↔ sv v942 < sv v946) := e_plt h_v942 h_v946 (of_decide_eq_true rfl)
  have h_v950 : R 1 0 4611686018158952386 4611686018695823484 v950 v950 := (r_psel hl h_v949 h_v942 h_v946 (of_decide_eq_true rfl))
  have e_v950 : v950 = if v949 = 1 then v942 else v946 := e_psel h_v949 h_v942 h_v946 (of_decide_eq_true rfl)
  have h_v951 : R 1 0 0 1 v951 v951 := (r_plt hl h_v944 h_v948 (of_decide_eq_true rfl))
  have e_v951 : (v951 = 1 ↔ sv v944 < sv v948) := e_plt h_v944 h_v948 (of_decide_eq_true rfl)
  have h_v952 : R 1 0 4611686018158952386 4611686018695823485 v952 v952 := (r_psel hl h_v951 h_v948 h_v944 (of_decide_eq_true rfl))
  have e_v952 : v952 = if v951 = 1 then v948 else v944 := e_psel h_v951 h_v948 h_v944 (of_decide_eq_true rfl)
  have h_v953 : R 1 0 4611686018158952386 4611686018695823484 v953 v953 := (r_psel hl h_v927 h_v950 h_v942 (of_decide_eq_true rfl))
  have e_v953 : v953 = if v927 = 1 then v950 else v942 := e_psel h_v927 h_v950 h_v942 (of_decide_eq_true rfl)
  have h_v954 : R 1 0 4611686018158952386 4611686018695823485 v954 v954 := (r_psel hl h_v927 h_v952 h_v944 (of_decide_eq_true rfl))
  have e_v954 : v954 = if v927 = 1 then v952 else v944 := e_psel h_v927 h_v952 h_v944 (of_decide_eq_true rfl)
  have h_v955 : R 1 0 4611686017890516805 4611686018964258878 v955 v955 := (r_sub hl (r_add hl h_v874 h_OFFr (of_decide_eq_true rfl)) h_v954 (of_decide_eq_true rfl))
  have e_v955 : sv v955 = sv v874 - sv v954 := e_sub h_v874 h_v954 (of_decide_eq_true rfl)
  have h_v956 : R 1 0 4611686017890516812 4611686018964258878 v956 v956 := (r_sub hl (r_add hl h_v878 h_OFFr (of_decide_eq_true rfl)) h_v953 (of_decide_eq_true rfl))
  have e_v956 : sv v956 = sv v878 - sv v953 := e_sub h_v878 h_v953 (of_decide_eq_true rfl)
  have h_v957 : R 1 0 0 1 v957 v957 := (r_plt hl h_v61 h_v919 (of_decide_eq_true rfl))
  have e_v957 : (v957 = 1 ↔ sv v61 < sv v919) := e_plt h_v61 h_v919 (of_decide_eq_true rfl)
  have h_v958 : R 1 0 0 1 v958 v958 := (r_plt hl h_v920 h_v61 (of_decide_eq_true rfl))
  have e_v958 : (v958 = 1 ↔ sv v920 < sv v61) := e_plt h_v920 h_v61 (of_decide_eq_true rfl)
  have h_v959 : R 1 0 0 1 v959 v959 := (r_plt hl h_v61 h_v955 (of_decide_eq_true rfl))
  clear h_v919 h_v920 h_v927 h_v942 h_v944 h_v946 h_v947 h_v948 h_v949 h_v950 h_v951 h_v952 h_v953 h_v954
  have e_v959 : (v959 = 1 ↔ sv v61 < sv v955) := e_plt h_v61 h_v955 (of_decide_eq_true rfl)
  have h_v960 : R 1 0 0 1 v960 v960 := (r_plt hl h_v956 h_v61 (of_decide_eq_true rfl))
  have e_v960 : (v960 = 1 ↔ sv v956 < sv v61) := e_plt h_v956 h_v61 (of_decide_eq_true rfl)
  have h_v961 : R 1 0 4611686018427387899 4611686018695823375 v961 v961 := (r_psel hl h_v957 h_v101 h_v100 (of_decide_eq_true rfl))
  have e_v961 : v961 = if v957 = 1 then v101 else v100 := e_psel h_v957 h_v101 h_v100 (of_decide_eq_true rfl)
  have h_v962 : R 1 0 4611686018427387899 4611686018695823375 v962 v962 := (r_psel hl h_v958 h_v100 h_v101 (of_decide_eq_true rfl))
  have e_v962 : v962 = if v958 = 1 then v100 else v101 := e_psel h_v958 h_v100 h_v101 (of_decide_eq_true rfl)
  have h_v963 : R 1 0 4611686018427387899 4611686018695823375 v963 v963 := (r_psel hl h_v958 h_v101 h_v100 (of_decide_eq_true rfl))
  have e_v963 : v963 = if v958 = 1 then v101 else v100 := e_psel h_v958 h_v101 h_v100 (of_decide_eq_true rfl)
  have h_v964 : R 1 0 4611686018427387899 4611686018695823375 v964 v964 := (r_psel hl h_v957 h_v100 h_v101 (of_decide_eq_true rfl))
  have e_v964 : v964 = if v957 = 1 then v100 else v101 := e_psel h_v957 h_v100 h_v101 (of_decide_eq_true rfl)
  have h_v965 : R 1 0 4611686018427387899 4611686018695823375 v965 v965 := (r_psel hl h_v959 h_v836 h_v835 (of_decide_eq_true rfl))
  have e_v965 : v965 = if v959 = 1 then v836 else v835 := e_psel h_v959 h_v836 h_v835 (of_decide_eq_true rfl)
  have h_v966 : R 1 0 4611686018427387899 4611686018695823375 v966 v966 := (r_psel hl h_v960 h_v835 h_v836 (of_decide_eq_true rfl))
  have e_v966 : v966 = if v960 = 1 then v835 else v836 := e_psel h_v960 h_v835 h_v836 (of_decide_eq_true rfl)
  have h_v967 : R 1 0 4611686018427387899 4611686018695823375 v967 v967 := (r_psel hl h_v960 h_v836 h_v835 (of_decide_eq_true rfl))
  have e_v967 : v967 = if v960 = 1 then v836 else v835 := e_psel h_v960 h_v836 h_v835 (of_decide_eq_true rfl)
  have h_v968 : R 1 0 4611686018427387899 4611686018695823375 v968 v968 := (r_psel hl h_v959 h_v835 h_v836 (of_decide_eq_true rfl))
  have e_v968 : v968 = if v959 = 1 then v835 else v836 := e_psel h_v959 h_v835 h_v836 (of_decide_eq_true rfl)
  have h_v974 : R 1 0 4611686018427387904 4683743620518379745 v974 v974 := (r_smx_sq hl 29 h_v962 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v974 : sv v974 = sv v962 * sv v962 := e_smx_sq 29 h_v962 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v975 : R 1 0 4611686018427387904 4611686018695823391 v975 v975 := (r_srdC hl h_v974 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v975 : sv v975 = -((-sv v974) / 2 ^ 28) := e_srdC h_v974 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v976 : R 1 0 4611686018427387904 4611686018964258878 v976 v976 := (r_sub hl (r_add hl h_v975 h_v975 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v976 : sv v976 = sv v975 + sv v975 := e_add h_v975 h_v975 (of_decide_eq_true rfl)
  clear h_v955 h_v956 h_v958 h_v959 h_v960 h_v975
  have h_v977 : R 1 0 4611686018158952386 4611686018695823360 v977 v977 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v976 (of_decide_eq_true rfl))
  have e_v977 : sv v977 = sv v33 - sv v976 := e_sub h_v33 h_v976 (of_decide_eq_true rfl)
  have h_v978 : R 1 0 0 1 v978 v978 := (r_plt hl h_v977 h_v105 (of_decide_eq_true rfl))
  have e_v978 : (v978 = 1 ↔ sv v977 < sv v105) := e_plt h_v977 h_v105 (of_decide_eq_true rfl)
  have h_v979 : R 1 0 4611686018158952386 4611686018695823360 v979 v979 := (r_psel hl h_v978 h_v105 h_v977 (of_decide_eq_true rfl))
  have e_v979 : v979 = if v978 = 1 then v105 else v977 := e_psel h_v978 h_v105 h_v977 (of_decide_eq_true rfl)
  have h_v980 : R 1 0 4611686018427387904 4683743620518379745 v980 v980 := (r_smx_sq hl 29 h_v961 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v980 : sv v980 = sv v961 * sv v961 := e_smx_sq 29 h_v961 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v981 : R 1 0 4611686018427387904 4611686018695823390 v981 v981 := (r_srdF hl h_v980 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v981 : sv v981 = sv v980 / 2 ^ 28 := e_srdF h_v980 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v982 : R 1 0 4611686018427387904 4611686018964258876 v982 v982 := (r_sub hl (r_add hl h_v981 h_v981 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v982 : sv v982 = sv v981 + sv v981 := e_add h_v981 h_v981 (of_decide_eq_true rfl)
  have h_v983 : R 1 0 4611686018158952388 4611686018695823360 v983 v983 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v982 (of_decide_eq_true rfl))
  have e_v983 : sv v983 = sv v33 - sv v982 := e_sub h_v33 h_v982 (of_decide_eq_true rfl)
  have h_v984 : R 1 0 4611686018427387904 4683743620518379745 v984 v984 := (r_smx_sq hl 29 h_v966 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v984 : sv v984 = sv v966 * sv v966 := e_smx_sq 29 h_v966 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v985 : R 1 0 4611686018427387904 4611686018695823391 v985 v985 := (r_srdC hl h_v984 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v985 : sv v985 = -((-sv v984) / 2 ^ 28) := e_srdC h_v984 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v986 : R 1 0 4611686018427387904 4611686018964258878 v986 v986 := (r_sub hl (r_add hl h_v985 h_v985 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v986 : sv v986 = sv v985 + sv v985 := e_add h_v985 h_v985 (of_decide_eq_true rfl)
  have h_v987 : R 1 0 4611686018158952386 4611686018695823360 v987 v987 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v986 (of_decide_eq_true rfl))
  have e_v987 : sv v987 = sv v33 - sv v986 := e_sub h_v33 h_v986 (of_decide_eq_true rfl)
  have h_v988 : R 1 0 0 1 v988 v988 := (r_plt hl h_v987 h_v105 (of_decide_eq_true rfl))
  have e_v988 : (v988 = 1 ↔ sv v987 < sv v105) := e_plt h_v987 h_v105 (of_decide_eq_true rfl)
  have h_v989 : R 1 0 4611686018158952386 4611686018695823360 v989 v989 := (r_psel hl h_v988 h_v105 h_v987 (of_decide_eq_true rfl))
  clear h_v976 h_v977 h_v978 h_v981 h_v982 h_v985 h_v986
  have e_v989 : v989 = if v988 = 1 then v105 else v987 := e_psel h_v988 h_v105 h_v987 (of_decide_eq_true rfl)
  have h_v990 : R 1 0 4611686018427387904 4683743620518379745 v990 v990 := (r_smx_sq hl 29 h_v965 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v990 : sv v990 = sv v965 * sv v965 := e_smx_sq 29 h_v965 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v991 : R 1 0 4611686018427387904 4611686018695823390 v991 v991 := (r_srdF hl h_v990 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v991 : sv v991 = sv v990 / 2 ^ 28 := e_srdF h_v990 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v992 : R 1 0 4611686018427387904 4611686018964258876 v992 v992 := (r_sub hl (r_add hl h_v991 h_v991 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v992 : sv v992 = sv v991 + sv v991 := e_add h_v991 h_v991 (of_decide_eq_true rfl)
  have h_v993 : R 1 0 4611686018158952388 4611686018695823360 v993 v993 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v992 (of_decide_eq_true rfl))
  have e_v993 : sv v993 = sv v33 - sv v992 := e_sub h_v33 h_v992 (of_decide_eq_true rfl)
  have h_v994 : R 1 0 0 1 v994 v994 := (r_plt hl h_v979 h_v61 (of_decide_eq_true rfl))
  have e_v994 : (v994 = 1 ↔ sv v979 < sv v61) := e_plt h_v979 h_v61 (of_decide_eq_true rfl)
  have h_v995 : R 1 0 0 1 v995 v995 := (r_sub hl (r_O hl) h_v994 (of_decide_eq_true rfl))
  have e_v995 : (v995 = 1 ↔ ¬v994 = 1) := e_not h_v994 (of_decide_eq_true rfl)
  have h_v996 : R 1 0 0 1 v996 v996 := (r_plt hl h_v61 h_v983 (of_decide_eq_true rfl))
  have e_v996 : (v996 = 1 ↔ sv v61 < sv v983) := e_plt h_v61 h_v983 (of_decide_eq_true rfl)
  have h_v997 : R 1 0 0 1 v997 v997 := (r_sub hl (r_O hl) h_v996 (of_decide_eq_true rfl))
  have e_v997 : (v997 = 1 ↔ ¬v996 = 1) := e_not h_v996 (of_decide_eq_true rfl)
  have h_v998 : R 1 0 0 1 v998 v998 := (r_land hl h_v994 h_v997 (of_decide_eq_true rfl))
  have e_v998 : (v998 = 1 ↔ v994 = 1 ∧ v997 = 1) := e_land h_v994 h_v997 (of_decide_eq_true rfl)
  have h_v999 : R 1 0 0 1 v999 v999 := (r_land hl h_v994 h_v996 (of_decide_eq_true rfl))
  have e_v999 : (v999 = 1 ↔ v994 = 1 ∧ v996 = 1) := e_land h_v994 h_v996 (of_decide_eq_true rfl)
  have h_v1000 : R 1 0 0 1 v1000 v1000 := (r_plt hl h_v989 h_v61 (of_decide_eq_true rfl))
  have e_v1000 : (v1000 = 1 ↔ sv v989 < sv v61) := e_plt h_v989 h_v61 (of_decide_eq_true rfl)
  have h_v1002 : R 1 0 0 1 v1002 v1002 := (r_plt hl h_v61 h_v993 (of_decide_eq_true rfl))
  have e_v1002 : (v1002 = 1 ↔ sv v61 < sv v993) := e_plt h_v61 h_v993 (of_decide_eq_true rfl)
  clear h_v105 h_v987 h_v988 h_v991 h_v992 h_v994 h_v996 h_v997
  have h_v1003 : R 1 0 0 1 v1003 v1003 := (r_sub hl (r_O hl) h_v1002 (of_decide_eq_true rfl))
  have e_v1003 : (v1003 = 1 ↔ ¬v1002 = 1) := e_not h_v1002 (of_decide_eq_true rfl)
  have h_v1004 : R 1 0 0 1 v1004 v1004 := (r_land hl h_v1000 h_v1003 (of_decide_eq_true rfl))
  have e_v1004 : (v1004 = 1 ↔ v1000 = 1 ∧ v1003 = 1) := e_land h_v1000 h_v1003 (of_decide_eq_true rfl)
  have h_v1005 : R 1 0 0 1 v1005 v1005 := (r_land hl h_v1000 h_v1002 (of_decide_eq_true rfl))
  have e_v1005 : (v1005 = 1 ↔ v1000 = 1 ∧ v1002 = 1) := e_land h_v1000 h_v1002 (of_decide_eq_true rfl)
  have h_v1006 : R 1 0 0 1 v1006 v1006 := (r_land hl h_v999 h_v1005 (of_decide_eq_true rfl))
  have e_v1006 : (v1006 = 1 ↔ v999 = 1 ∧ v1005 = 1) := e_land h_v999 h_v1005 (of_decide_eq_true rfl)
  have h_v1007 : R 1 0 0 1 v1007 v1007 := (r_land hl h_v995 h_v1005 (of_decide_eq_true rfl))
  have e_v1007 : (v1007 = 1 ↔ v995 = 1 ∧ v1005 = 1) := e_land h_v995 h_v1005 (of_decide_eq_true rfl)
  have h_v1008 : R 1 0 0 1 v1008 v1008 := (r_lor hl h_v1004 h_v1007 (of_decide_eq_true rfl))
  have e_v1008 : (v1008 = 1 ↔ v1004 = 1 ∨ v1007 = 1) := e_lor h_v1004 h_v1007 (of_decide_eq_true rfl)
  have h_v1009 : R 1 0 4611686018158952386 4611686018695823360 v1009 v1009 := (r_psel hl h_v1008 h_v983 h_v979 (of_decide_eq_true rfl))
  have e_v1009 : v1009 = if v1008 = 1 then v983 else v979 := e_psel h_v1008 h_v983 h_v979 (of_decide_eq_true rfl)
  have h_v1010 : R 1 0 0 1 v1010 v1010 := (r_sub hl (r_O hl) h_v1004 (of_decide_eq_true rfl))
  have e_v1010 : (v1010 = 1 ↔ ¬v1004 = 1) := e_not h_v1004 (of_decide_eq_true rfl)
  have h_v1011 : R 1 0 0 1 v1011 v1011 := (r_land hl h_v999 h_v1010 (of_decide_eq_true rfl))
  have e_v1011 : (v1011 = 1 ↔ v999 = 1 ∧ v1010 = 1) := e_land h_v999 h_v1010 (of_decide_eq_true rfl)
  have h_v1012 : R 1 0 0 1 v1012 v1012 := (r_lor hl h_v998 h_v1011 (of_decide_eq_true rfl))
  have e_v1012 : (v1012 = 1 ↔ v998 = 1 ∨ v1011 = 1) := e_lor h_v998 h_v1011 (of_decide_eq_true rfl)
  have h_v1013 : R 1 0 4611686018158952386 4611686018695823360 v1013 v1013 := (r_psel hl h_v1012 h_v993 h_v989 (of_decide_eq_true rfl))
  have e_v1013 : v1013 = if v1012 = 1 then v993 else v989 := e_psel h_v1012 h_v993 h_v989 (of_decide_eq_true rfl)
  have h_v1020 : R 1 0 4539628407746461696 4683743645751316228 v1020 v1020 := (r_smx hl 30 h_v1013 h_v1009 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v1020 : sv v1020 = sv v1013 * sv v1009 := e_smx 30 h_v1013 h_v1009 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v1021 : R 1 0 4611686018158952386 4611686018695823484 v1021 v1021 := (r_srdF hl h_v1020 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  clear h_v979 h_v993 h_v995 h_v998 h_v999 h_v1000 h_v1002 h_v1003 h_v1004 h_v1005 h_v1007 h_v1008 h_v1009 h_v1010 h_v1011 h_v1012 h_v1013
  have e_v1021 : sv v1021 = sv v1020 / 2 ^ 28 := e_srdF h_v1020 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v1024 : R 1 0 4539628407746461696 4683743645214445192 v1024 v1024 := (r_smx hl 30 h_v989 h_v983 4539628407746461696 4683743645214445192 (of_decide_eq_true rfl))
  have e_v1024 : sv v1024 = sv v989 * sv v983 := e_smx 30 h_v989 h_v983 4539628407746461696 4683743645214445192 (of_decide_eq_true rfl)
  have h_v1025 : R 1 0 4611686018158952386 4611686018695823482 v1025 v1025 := (r_srdF hl h_v1024 4611686018158952386 4611686018695823482 (of_decide_eq_true rfl))
  have e_v1025 : sv v1025 = sv v1024 / 2 ^ 28 := e_srdF h_v1024 4611686018158952386 4611686018695823482 (of_decide_eq_true rfl)
  have h_v1028 : R 1 0 0 1 v1028 v1028 := (r_plt hl h_v1021 h_v1025 (of_decide_eq_true rfl))
  have e_v1028 : (v1028 = 1 ↔ sv v1021 < sv v1025) := e_plt h_v1021 h_v1025 (of_decide_eq_true rfl)
  have h_v1029 : R 1 0 4611686018158952386 4611686018695823484 v1029 v1029 := (r_psel hl h_v1028 h_v1021 h_v1025 (of_decide_eq_true rfl))
  have e_v1029 : v1029 = if v1028 = 1 then v1021 else v1025 := e_psel h_v1028 h_v1021 h_v1025 (of_decide_eq_true rfl)
  have h_v1032 : R 1 0 4611686018158952386 4611686018695823484 v1032 v1032 := (r_psel hl h_v1006 h_v1029 h_v1021 (of_decide_eq_true rfl))
  have e_v1032 : v1032 = if v1006 = 1 then v1029 else v1021 := e_psel h_v1006 h_v1029 h_v1021 (of_decide_eq_true rfl)
  have h_v1035 : R 1 0 4611686017890516812 4611686018964258878 v1035 v1035 := (r_sub hl (r_add hl h_v858 h_OFFr (of_decide_eq_true rfl)) h_v1032 (of_decide_eq_true rfl))
  have e_v1035 : sv v1035 = sv v858 - sv v1032 := e_sub h_v858 h_v1032 (of_decide_eq_true rfl)
  have h_v1036 : R 1 0 4683743612465315840 4683743612465315840 v1036 v1036 := (r_c hl 4683743612465315840 (of_decide_eq_true rfl))
  have e_v1036 : sv v1036 = (72057594037927936) := e_c 4683743612465315840 (72057594037927936) (of_decide_eq_true rfl)
  have h_v1037 : R 1 0 4611686010374323999 4683743612465315840 v1037 v1037 := (r_sub hl (r_add hl h_v1036 h_OFFr (of_decide_eq_true rfl)) h_v980 (of_decide_eq_true rfl))
  have e_v1037 : sv v1037 = sv v1036 - sv v980 := e_sub h_v1036 h_v980 (of_decide_eq_true rfl)
  have h_v1038 : R 1 0 4611686018427387904 4611686018695823360 v1038 v1038 := (r_psqrt hl h_v1037 (of_decide_eq_true rfl))
  have e_v1038 : sv v1038 = ((Nat.sqrt (v1037 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1037 (of_decide_eq_true rfl)
  have h_v1039 : R 1 0 4611686018427387905 4611686018695823361 v1039 v1039 := (r_sub hl (r_add hl h_v115 h_v1038 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1039 : sv v1039 = sv v115 + sv v1038 := e_add h_v115 h_v1038 (of_decide_eq_true rfl)
  have pb_v1038_v961 : PB 1 v1038 v961 36028797018963968 := pb_sqrt hl h_v961 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1040 : R 1 0 4611686017085210624 4647714815446351872 v1040 v1040 := (r_smx_pb hl 29 h_v1038 h_v961 pb_v1038_v961 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1040 : sv v1040 = sv v1038 * sv v961 := e_smx_pb 29 h_v1038 h_v961 pb_v1038_v961 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1041 : R 1 0 4611686018427387899 4611686018561605632 v1041 v1041 := (r_srdF hl h_v1040 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  clear h_v983 h_v989 h_v1006 h_v1020 h_v1021 h_v1024 h_v1025 h_v1028 h_v1029 h_v1032 h_v1037 h_v1038 pb_v1038_v961
  have e_v1041 : sv v1041 = sv v1040 / 2 ^ 28 := e_srdF h_v1040 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1042 : R 1 0 4611686018427387894 4611686018695823360 v1042 v1042 := (r_sub hl (r_add hl h_v1041 h_v1041 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1042 : sv v1042 = sv v1041 + sv v1041 := e_add h_v1041 h_v1041 (of_decide_eq_true rfl)
  have pb_v1039_v961 : PB 1 v1039 v961 36028797287399439 := pb_sqrt1 hl h_v961 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1043 : R 1 0 4611686017085210619 4647714815714787343 v1043 v1043 := (r_smx_pb hl 29 h_v1039 h_v961 pb_v1039_v961 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1043 : sv v1043 = sv v1039 * sv v961 := e_smx_pb 29 h_v1039 h_v961 pb_v1039_v961 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1044 : R 1 0 4611686018427387899 4611686018561605634 v1044 v1044 := (r_srdC hl h_v1043 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1044 : sv v1044 = -((-sv v1043) / 2 ^ 28) := e_srdC h_v1043 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1045 : R 1 0 4611686018427387894 4611686018695823364 v1045 v1045 := (r_sub hl (r_add hl h_v1044 h_v1044 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1045 : sv v1045 = sv v1044 + sv v1044 := e_add h_v1044 h_v1044 (of_decide_eq_true rfl)
  have h_v1046 : R 1 0 0 1 v1046 v1046 := (r_plt hl h_v1045 h_v33 (of_decide_eq_true rfl))
  have e_v1046 : (v1046 = 1 ↔ sv v1045 < sv v33) := e_plt h_v1045 h_v33 (of_decide_eq_true rfl)
  have h_v1047 : R 1 0 4611686018427387894 4611686018695823364 v1047 v1047 := (r_psel hl h_v1046 h_v1045 h_v33 (of_decide_eq_true rfl))
  have e_v1047 : v1047 = if v1046 = 1 then v1045 else v33 := e_psel h_v1046 h_v1045 h_v33 (of_decide_eq_true rfl)
  have h_v1048 : R 1 0 4611686010374323999 4683743612465315840 v1048 v1048 := (r_sub hl (r_add hl h_v1036 h_OFFr (of_decide_eq_true rfl)) h_v974 (of_decide_eq_true rfl))
  have e_v1048 : sv v1048 = sv v1036 - sv v974 := e_sub h_v1036 h_v974 (of_decide_eq_true rfl)
  have h_v1049 : R 1 0 4611686018427387904 4611686018695823360 v1049 v1049 := (r_psqrt hl h_v1048 (of_decide_eq_true rfl))
  have e_v1049 : sv v1049 = ((Nat.sqrt (v1048 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1048 (of_decide_eq_true rfl)
  have h_v1050 : R 1 0 4611686018427387905 4611686018695823361 v1050 v1050 := (r_sub hl (r_add hl h_v115 h_v1049 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1050 : sv v1050 = sv v115 + sv v1049 := e_add h_v115 h_v1049 (of_decide_eq_true rfl)
  have pb_v1049_v962 : PB 1 v1049 v962 36028797018963968 := pb_sqrt hl h_v962 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1051 : R 1 0 4611686017085210624 4647714815446351872 v1051 v1051 := (r_smx_pb hl 29 h_v1049 h_v962 pb_v1049_v962 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1051 : sv v1051 = sv v1049 * sv v962 := e_smx_pb 29 h_v1049 h_v962 pb_v1049_v962 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1052 : R 1 0 4611686018427387899 4611686018561605632 v1052 v1052 := (r_srdF hl h_v1051 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1052 : sv v1052 = sv v1051 / 2 ^ 28 := e_srdF h_v1051 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  clear h_v961 h_v1039 h_v1040 h_v1041 pb_v1039_v961 h_v1043 h_v1044 h_v1045 h_v1046 h_v1048 h_v1049 pb_v1049_v962 h_v1051
  have h_v1053 : R 1 0 4611686018427387894 4611686018695823360 v1053 v1053 := (r_sub hl (r_add hl h_v1052 h_v1052 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1053 : sv v1053 = sv v1052 + sv v1052 := e_add h_v1052 h_v1052 (of_decide_eq_true rfl)
  have pb_v1050_v962 : PB 1 v1050 v962 36028797287399439 := pb_sqrt1 hl h_v962 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1054 : R 1 0 4611686017085210619 4647714815714787343 v1054 v1054 := (r_smx_pb hl 29 h_v1050 h_v962 pb_v1050_v962 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1054 : sv v1054 = sv v1050 * sv v962 := e_smx_pb 29 h_v1050 h_v962 pb_v1050_v962 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1055 : R 1 0 4611686018427387899 4611686018561605634 v1055 v1055 := (r_srdC hl h_v1054 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1055 : sv v1055 = -((-sv v1054) / 2 ^ 28) := e_srdC h_v1054 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1056 : R 1 0 4611686018427387894 4611686018695823364 v1056 v1056 := (r_sub hl (r_add hl h_v1055 h_v1055 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1056 : sv v1056 = sv v1055 + sv v1055 := e_add h_v1055 h_v1055 (of_decide_eq_true rfl)
  have h_v1057 : R 1 0 0 1 v1057 v1057 := (r_plt hl h_v1056 h_v33 (of_decide_eq_true rfl))
  have e_v1057 : (v1057 = 1 ↔ sv v1056 < sv v33) := e_plt h_v1056 h_v33 (of_decide_eq_true rfl)
  have h_v1058 : R 1 0 4611686018427387894 4611686018695823364 v1058 v1058 := (r_psel hl h_v1057 h_v1056 h_v33 (of_decide_eq_true rfl))
  have e_v1058 : v1058 = if v1057 = 1 then v1056 else v33 := e_psel h_v1057 h_v1056 h_v33 (of_decide_eq_true rfl)
  have h_v1059 : R 1 0 0 1 v1059 v1059 := (r_plt hl h_v1042 h_v1053 (of_decide_eq_true rfl))
  have e_v1059 : (v1059 = 1 ↔ sv v1042 < sv v1053) := e_plt h_v1042 h_v1053 (of_decide_eq_true rfl)
  have h_v1060 : R 1 0 4611686018427387894 4611686018695823360 v1060 v1060 := (r_psel hl h_v1059 h_v1042 h_v1053 (of_decide_eq_true rfl))
  have e_v1060 : v1060 = if v1059 = 1 then v1042 else v1053 := e_psel h_v1059 h_v1042 h_v1053 (of_decide_eq_true rfl)
  have h_v1061 : R 1 0 0 1 v1061 v1061 := (r_plt hl h_v1047 h_v1058 (of_decide_eq_true rfl))
  have e_v1061 : (v1061 = 1 ↔ sv v1047 < sv v1058) := e_plt h_v1047 h_v1058 (of_decide_eq_true rfl)
  have h_v1062 : R 1 0 4611686018427387894 4611686018695823364 v1062 v1062 := (r_psel hl h_v1061 h_v1058 h_v1047 (of_decide_eq_true rfl))
  have e_v1062 : v1062 = if v1061 = 1 then v1058 else v1047 := e_psel h_v1061 h_v1058 h_v1047 (of_decide_eq_true rfl)
  have h_v1063 : R 1 0 4647714815446351872 4647714815446351872 v1063 v1063 := (r_c hl 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1063 : sv v1063 = (36028797018963968) := e_c 4647714815446351872 (36028797018963968) (of_decide_eq_true rfl)
  have h_v1064 : R 1 0 0 1 v1064 v1064 := (r_plt hl h_v1063 h_v980 (of_decide_eq_true rfl))
  have e_v1064 : (v1064 = 1 ↔ sv v1063 < sv v980) := e_plt h_v1063 h_v980 (of_decide_eq_true rfl)
  clear h_v962 h_v980 h_v1042 h_v1047 h_v1050 h_v1052 h_v1053 pb_v1050_v962 h_v1054 h_v1055 h_v1056 h_v1057 h_v1058 h_v1059 h_v1061
  have h_v1065 : R 1 0 0 1 v1065 v1065 := (r_sub hl (r_O hl) h_v1064 (of_decide_eq_true rfl))
  have e_v1065 : (v1065 = 1 ↔ ¬v1064 = 1) := e_not h_v1064 (of_decide_eq_true rfl)
  have h_v1066 : R 1 0 0 1 v1066 v1066 := (r_plt hl h_v974 h_v1063 (of_decide_eq_true rfl))
  have e_v1066 : (v1066 = 1 ↔ sv v974 < sv v1063) := e_plt h_v974 h_v1063 (of_decide_eq_true rfl)
  have h_v1067 : R 1 0 0 1 v1067 v1067 := (r_sub hl (r_O hl) h_v1066 (of_decide_eq_true rfl))
  have e_v1067 : (v1067 = 1 ↔ ¬v1066 = 1) := e_not h_v1066 (of_decide_eq_true rfl)
  have h_v1068 : R 1 0 0 1 v1068 v1068 := (r_land hl h_v1065 h_v1067 (of_decide_eq_true rfl))
  have e_v1068 : (v1068 = 1 ↔ v1065 = 1 ∧ v1067 = 1) := e_land h_v1065 h_v1067 (of_decide_eq_true rfl)
  have h_v1069 : R 1 0 4611686018427387894 4611686018695823364 v1069 v1069 := (r_psel hl h_v1068 h_v33 h_v1062 (of_decide_eq_true rfl))
  have e_v1069 : v1069 = if v1068 = 1 then v33 else v1062 := e_psel h_v1068 h_v33 h_v1062 (of_decide_eq_true rfl)
  have h_v1070 : R 1 0 4611686010374323999 4683743612465315840 v1070 v1070 := (r_sub hl (r_add hl h_v1036 h_OFFr (of_decide_eq_true rfl)) h_v990 (of_decide_eq_true rfl))
  have e_v1070 : sv v1070 = sv v1036 - sv v990 := e_sub h_v1036 h_v990 (of_decide_eq_true rfl)
  have h_v1071 : R 1 0 4611686018427387904 4611686018695823360 v1071 v1071 := (r_psqrt hl h_v1070 (of_decide_eq_true rfl))
  have e_v1071 : sv v1071 = ((Nat.sqrt (v1070 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1070 (of_decide_eq_true rfl)
  have h_v1072 : R 1 0 4611686018427387905 4611686018695823361 v1072 v1072 := (r_sub hl (r_add hl h_v115 h_v1071 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1072 : sv v1072 = sv v115 + sv v1071 := e_add h_v115 h_v1071 (of_decide_eq_true rfl)
  have pb_v1071_v965 : PB 1 v1071 v965 36028797018963968 := pb_sqrt hl h_v965 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1073 : R 1 0 4611686017085210624 4647714815446351872 v1073 v1073 := (r_smx_pb hl 29 h_v1071 h_v965 pb_v1071_v965 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1073 : sv v1073 = sv v1071 * sv v965 := e_smx_pb 29 h_v1071 h_v965 pb_v1071_v965 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1074 : R 1 0 4611686018427387899 4611686018561605632 v1074 v1074 := (r_srdF hl h_v1073 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1074 : sv v1074 = sv v1073 / 2 ^ 28 := e_srdF h_v1073 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1075 : R 1 0 4611686018427387894 4611686018695823360 v1075 v1075 := (r_sub hl (r_add hl h_v1074 h_v1074 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1075 : sv v1075 = sv v1074 + sv v1074 := e_add h_v1074 h_v1074 (of_decide_eq_true rfl)
  have pb_v1072_v965 : PB 1 v1072 v965 36028797287399439 := pb_sqrt1 hl h_v965 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1076 : R 1 0 4611686017085210619 4647714815714787343 v1076 v1076 := (r_smx_pb hl 29 h_v1072 h_v965 pb_v1072_v965 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  clear h_v974 h_v1062 h_v1064 h_v1065 h_v1066 h_v1067 h_v1068 h_v1070 h_v1071 pb_v1071_v965 h_v1073 h_v1074
  have e_v1076 : sv v1076 = sv v1072 * sv v965 := e_smx_pb 29 h_v1072 h_v965 pb_v1072_v965 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1077 : R 1 0 4611686018427387899 4611686018561605634 v1077 v1077 := (r_srdC hl h_v1076 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1077 : sv v1077 = -((-sv v1076) / 2 ^ 28) := e_srdC h_v1076 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1078 : R 1 0 4611686018427387894 4611686018695823364 v1078 v1078 := (r_sub hl (r_add hl h_v1077 h_v1077 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1078 : sv v1078 = sv v1077 + sv v1077 := e_add h_v1077 h_v1077 (of_decide_eq_true rfl)
  have h_v1079 : R 1 0 0 1 v1079 v1079 := (r_plt hl h_v1078 h_v33 (of_decide_eq_true rfl))
  have e_v1079 : (v1079 = 1 ↔ sv v1078 < sv v33) := e_plt h_v1078 h_v33 (of_decide_eq_true rfl)
  have h_v1080 : R 1 0 4611686018427387894 4611686018695823364 v1080 v1080 := (r_psel hl h_v1079 h_v1078 h_v33 (of_decide_eq_true rfl))
  have e_v1080 : v1080 = if v1079 = 1 then v1078 else v33 := e_psel h_v1079 h_v1078 h_v33 (of_decide_eq_true rfl)
  have h_v1081 : R 1 0 4611686010374323999 4683743612465315840 v1081 v1081 := (r_sub hl (r_add hl h_v1036 h_OFFr (of_decide_eq_true rfl)) h_v984 (of_decide_eq_true rfl))
  have e_v1081 : sv v1081 = sv v1036 - sv v984 := e_sub h_v1036 h_v984 (of_decide_eq_true rfl)
  have h_v1082 : R 1 0 4611686018427387904 4611686018695823360 v1082 v1082 := (r_psqrt hl h_v1081 (of_decide_eq_true rfl))
  have e_v1082 : sv v1082 = ((Nat.sqrt (v1081 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v1081 (of_decide_eq_true rfl)
  have h_v1083 : R 1 0 4611686018427387905 4611686018695823361 v1083 v1083 := (r_sub hl (r_add hl h_v115 h_v1082 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1083 : sv v1083 = sv v115 + sv v1082 := e_add h_v115 h_v1082 (of_decide_eq_true rfl)
  have pb_v1082_v966 : PB 1 v1082 v966 36028797018963968 := pb_sqrt hl h_v966 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v1084 : R 1 0 4611686017085210624 4647714815446351872 v1084 v1084 := (r_smx_pb hl 29 h_v1082 h_v966 pb_v1082_v966 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v1084 : sv v1084 = sv v1082 * sv v966 := e_smx_pb 29 h_v1082 h_v966 pb_v1082_v966 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v1085 : R 1 0 4611686018427387899 4611686018561605632 v1085 v1085 := (r_srdF hl h_v1084 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v1085 : sv v1085 = sv v1084 / 2 ^ 28 := e_srdF h_v1084 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v1086 : R 1 0 4611686018427387894 4611686018695823360 v1086 v1086 := (r_sub hl (r_add hl h_v1085 h_v1085 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1086 : sv v1086 = sv v1085 + sv v1085 := e_add h_v1085 h_v1085 (of_decide_eq_true rfl)
  have pb_v1083_v966 : PB 1 v1083 v966 36028797287399439 := pb_sqrt1 hl h_v966 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1087 : R 1 0 4611686017085210619 4647714815714787343 v1087 v1087 := (r_smx_pb hl 29 h_v1083 h_v966 pb_v1083_v966 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1087 : sv v1087 = sv v1083 * sv v966 := e_smx_pb 29 h_v1083 h_v966 pb_v1083_v966 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  clear h_v115 h_v965 h_v966 h_v1036 h_v1072 pb_v1072_v965 h_v1076 h_v1077 h_v1078 h_v1079 h_v1081 h_v1082 h_v1083 pb_v1082_v966 h_v1084 h_v1085 pb_v1083_v966
  have h_v1088 : R 1 0 4611686018427387899 4611686018561605634 v1088 v1088 := (r_srdC hl h_v1087 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1088 : sv v1088 = -((-sv v1087) / 2 ^ 28) := e_srdC h_v1087 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1089 : R 1 0 4611686018427387894 4611686018695823364 v1089 v1089 := (r_sub hl (r_add hl h_v1088 h_v1088 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1089 : sv v1089 = sv v1088 + sv v1088 := e_add h_v1088 h_v1088 (of_decide_eq_true rfl)
  have h_v1090 : R 1 0 0 1 v1090 v1090 := (r_plt hl h_v1089 h_v33 (of_decide_eq_true rfl))
  have e_v1090 : (v1090 = 1 ↔ sv v1089 < sv v33) := e_plt h_v1089 h_v33 (of_decide_eq_true rfl)
  have h_v1091 : R 1 0 4611686018427387894 4611686018695823364 v1091 v1091 := (r_psel hl h_v1090 h_v1089 h_v33 (of_decide_eq_true rfl))
  have e_v1091 : v1091 = if v1090 = 1 then v1089 else v33 := e_psel h_v1090 h_v1089 h_v33 (of_decide_eq_true rfl)
  have h_v1092 : R 1 0 0 1 v1092 v1092 := (r_plt hl h_v1075 h_v1086 (of_decide_eq_true rfl))
  have e_v1092 : (v1092 = 1 ↔ sv v1075 < sv v1086) := e_plt h_v1075 h_v1086 (of_decide_eq_true rfl)
  have h_v1093 : R 1 0 4611686018427387894 4611686018695823360 v1093 v1093 := (r_psel hl h_v1092 h_v1075 h_v1086 (of_decide_eq_true rfl))
  have e_v1093 : v1093 = if v1092 = 1 then v1075 else v1086 := e_psel h_v1092 h_v1075 h_v1086 (of_decide_eq_true rfl)
  have h_v1094 : R 1 0 0 1 v1094 v1094 := (r_plt hl h_v1080 h_v1091 (of_decide_eq_true rfl))
  have e_v1094 : (v1094 = 1 ↔ sv v1080 < sv v1091) := e_plt h_v1080 h_v1091 (of_decide_eq_true rfl)
  have h_v1095 : R 1 0 4611686018427387894 4611686018695823364 v1095 v1095 := (r_psel hl h_v1094 h_v1091 h_v1080 (of_decide_eq_true rfl))
  have e_v1095 : v1095 = if v1094 = 1 then v1091 else v1080 := e_psel h_v1094 h_v1091 h_v1080 (of_decide_eq_true rfl)
  have h_v1096 : R 1 0 0 1 v1096 v1096 := (r_plt hl h_v1063 h_v990 (of_decide_eq_true rfl))
  have e_v1096 : (v1096 = 1 ↔ sv v1063 < sv v990) := e_plt h_v1063 h_v990 (of_decide_eq_true rfl)
  have h_v1097 : R 1 0 0 1 v1097 v1097 := (r_sub hl (r_O hl) h_v1096 (of_decide_eq_true rfl))
  have e_v1097 : (v1097 = 1 ↔ ¬v1096 = 1) := e_not h_v1096 (of_decide_eq_true rfl)
  have h_v1098 : R 1 0 0 1 v1098 v1098 := (r_plt hl h_v984 h_v1063 (of_decide_eq_true rfl))
  have e_v1098 : (v1098 = 1 ↔ sv v984 < sv v1063) := e_plt h_v984 h_v1063 (of_decide_eq_true rfl)
  have h_v1099 : R 1 0 0 1 v1099 v1099 := (r_sub hl (r_O hl) h_v1098 (of_decide_eq_true rfl))
  have e_v1099 : (v1099 = 1 ↔ ¬v1098 = 1) := e_not h_v1098 (of_decide_eq_true rfl)
  have h_v1100 : R 1 0 0 1 v1100 v1100 := (r_land hl h_v1097 h_v1099 (of_decide_eq_true rfl))
  clear h_v984 h_v990 h_v1063 h_v1075 h_v1080 h_v1086 h_v1087 h_v1088 h_v1089 h_v1090 h_v1091 h_v1092 h_v1094 h_v1096 h_v1098
  have e_v1100 : (v1100 = 1 ↔ v1097 = 1 ∧ v1099 = 1) := e_land h_v1097 h_v1099 (of_decide_eq_true rfl)
  have h_v1101 : R 1 0 4611686018427387894 4611686018695823364 v1101 v1101 := (r_psel hl h_v1100 h_v33 h_v1095 (of_decide_eq_true rfl))
  have e_v1101 : v1101 = if v1100 = 1 then v33 else v1095 := e_psel h_v1100 h_v33 h_v1095 (of_decide_eq_true rfl)
  have h_v1102 : R 1 0 0 1 v1102 v1102 := (r_plt hl h_v1060 h_v61 (of_decide_eq_true rfl))
  have e_v1102 : (v1102 = 1 ↔ sv v1060 < sv v61) := e_plt h_v1060 h_v61 (of_decide_eq_true rfl)
  have h_v1103 : R 1 0 0 1 v1103 v1103 := (r_sub hl (r_O hl) h_v1102 (of_decide_eq_true rfl))
  have e_v1103 : (v1103 = 1 ↔ ¬v1102 = 1) := e_not h_v1102 (of_decide_eq_true rfl)
  have h_v1104 : R 1 0 0 1 v1104 v1104 := (r_plt hl h_v61 h_v1069 (of_decide_eq_true rfl))
  have e_v1104 : (v1104 = 1 ↔ sv v61 < sv v1069) := e_plt h_v61 h_v1069 (of_decide_eq_true rfl)
  have h_v1105 : R 1 0 0 1 v1105 v1105 := (r_sub hl (r_O hl) h_v1104 (of_decide_eq_true rfl))
  have e_v1105 : (v1105 = 1 ↔ ¬v1104 = 1) := e_not h_v1104 (of_decide_eq_true rfl)
  have h_v1106 : R 1 0 0 1 v1106 v1106 := (r_land hl h_v1102 h_v1105 (of_decide_eq_true rfl))
  have e_v1106 : (v1106 = 1 ↔ v1102 = 1 ∧ v1105 = 1) := e_land h_v1102 h_v1105 (of_decide_eq_true rfl)
  have h_v1107 : R 1 0 0 1 v1107 v1107 := (r_land hl h_v1102 h_v1104 (of_decide_eq_true rfl))
  have e_v1107 : (v1107 = 1 ↔ v1102 = 1 ∧ v1104 = 1) := e_land h_v1102 h_v1104 (of_decide_eq_true rfl)
  have h_v1108 : R 1 0 0 1 v1108 v1108 := (r_plt hl h_v1093 h_v61 (of_decide_eq_true rfl))
  have e_v1108 : (v1108 = 1 ↔ sv v1093 < sv v61) := e_plt h_v1093 h_v61 (of_decide_eq_true rfl)
  have h_v1110 : R 1 0 0 1 v1110 v1110 := (r_plt hl h_v61 h_v1101 (of_decide_eq_true rfl))
  have e_v1110 : (v1110 = 1 ↔ sv v61 < sv v1101) := e_plt h_v61 h_v1101 (of_decide_eq_true rfl)
  have h_v1111 : R 1 0 0 1 v1111 v1111 := (r_sub hl (r_O hl) h_v1110 (of_decide_eq_true rfl))
  have e_v1111 : (v1111 = 1 ↔ ¬v1110 = 1) := e_not h_v1110 (of_decide_eq_true rfl)
  have h_v1112 : R 1 0 0 1 v1112 v1112 := (r_land hl h_v1108 h_v1111 (of_decide_eq_true rfl))
  have e_v1112 : (v1112 = 1 ↔ v1108 = 1 ∧ v1111 = 1) := e_land h_v1108 h_v1111 (of_decide_eq_true rfl)
  have h_v1113 : R 1 0 0 1 v1113 v1113 := (r_land hl h_v1108 h_v1110 (of_decide_eq_true rfl))
  have e_v1113 : (v1113 = 1 ↔ v1108 = 1 ∧ v1110 = 1) := e_land h_v1108 h_v1110 (of_decide_eq_true rfl)
  clear h_v1095 h_v1097 h_v1099 h_v1100 h_v1102 h_v1104 h_v1105 h_v1108 h_v1110 h_v1111
  have h_v1114 : R 1 0 0 1 v1114 v1114 := (r_land hl h_v1107 h_v1113 (of_decide_eq_true rfl))
  have e_v1114 : (v1114 = 1 ↔ v1107 = 1 ∧ v1113 = 1) := e_land h_v1107 h_v1113 (of_decide_eq_true rfl)
  have h_v1115 : R 1 0 0 1 v1115 v1115 := (r_land hl h_v1103 h_v1113 (of_decide_eq_true rfl))
  have e_v1115 : (v1115 = 1 ↔ v1103 = 1 ∧ v1113 = 1) := e_land h_v1103 h_v1113 (of_decide_eq_true rfl)
  have h_v1116 : R 1 0 0 1 v1116 v1116 := (r_lor hl h_v1112 h_v1115 (of_decide_eq_true rfl))
  have e_v1116 : (v1116 = 1 ↔ v1112 = 1 ∨ v1115 = 1) := e_lor h_v1112 h_v1115 (of_decide_eq_true rfl)
  have h_v1117 : R 1 0 4611686018427387894 4611686018695823364 v1117 v1117 := (r_psel hl h_v1116 h_v1069 h_v1060 (of_decide_eq_true rfl))
  have e_v1117 : v1117 = if v1116 = 1 then v1069 else v1060 := e_psel h_v1116 h_v1069 h_v1060 (of_decide_eq_true rfl)
  have h_v1118 : R 1 0 0 1 v1118 v1118 := (r_sub hl (r_O hl) h_v1112 (of_decide_eq_true rfl))
  have e_v1118 : (v1118 = 1 ↔ ¬v1112 = 1) := e_not h_v1112 (of_decide_eq_true rfl)
  have h_v1119 : R 1 0 0 1 v1119 v1119 := (r_land hl h_v1107 h_v1118 (of_decide_eq_true rfl))
  have e_v1119 : (v1119 = 1 ↔ v1107 = 1 ∧ v1118 = 1) := e_land h_v1107 h_v1118 (of_decide_eq_true rfl)
  have h_v1120 : R 1 0 0 1 v1120 v1120 := (r_lor hl h_v1106 h_v1119 (of_decide_eq_true rfl))
  have e_v1120 : (v1120 = 1 ↔ v1106 = 1 ∨ v1119 = 1) := e_lor h_v1106 h_v1119 (of_decide_eq_true rfl)
  have h_v1121 : R 1 0 4611686018427387894 4611686018695823364 v1121 v1121 := (r_psel hl h_v1120 h_v1101 h_v1093 (of_decide_eq_true rfl))
  have e_v1121 : v1121 = if v1120 = 1 then v1101 else v1093 := e_psel h_v1120 h_v1101 h_v1093 (of_decide_eq_true rfl)
  have h_v1122 : R 1 0 0 1 v1122 v1122 := (r_land hl h_v1106 h_v1113 (of_decide_eq_true rfl))
  have e_v1122 : (v1122 = 1 ↔ v1106 = 1 ∧ v1113 = 1) := e_land h_v1106 h_v1113 (of_decide_eq_true rfl)
  have h_v1123 : R 1 0 0 1 v1123 v1123 := (r_lor hl h_v1112 h_v1122 (of_decide_eq_true rfl))
  have e_v1123 : (v1123 = 1 ↔ v1112 = 1 ∨ v1122 = 1) := e_lor h_v1112 h_v1122 (of_decide_eq_true rfl)
  have h_v1124 : R 1 0 4611686018427387894 4611686018695823364 v1124 v1124 := (r_psel hl h_v1123 h_v1060 h_v1069 (of_decide_eq_true rfl))
  have e_v1124 : v1124 = if v1123 = 1 then v1060 else v1069 := e_psel h_v1123 h_v1060 h_v1069 (of_decide_eq_true rfl)
  have h_v1125 : R 1 0 0 1 v1125 v1125 := (r_land hl h_v1107 h_v1112 (of_decide_eq_true rfl))
  have e_v1125 : (v1125 = 1 ↔ v1107 = 1 ∧ v1112 = 1) := e_land h_v1107 h_v1112 (of_decide_eq_true rfl)
  have h_v1126 : R 1 0 0 1 v1126 v1126 := (r_lor hl h_v1106 h_v1125 (of_decide_eq_true rfl))
  clear h_v1103 h_v1107 h_v1112 h_v1113 h_v1115 h_v1116 h_v1118 h_v1119 h_v1120 h_v1122 h_v1123
  have e_v1126 : (v1126 = 1 ↔ v1106 = 1 ∨ v1125 = 1) := e_lor h_v1106 h_v1125 (of_decide_eq_true rfl)
  have h_v1127 : R 1 0 4611686018427387894 4611686018695823364 v1127 v1127 := (r_psel hl h_v1126 h_v1093 h_v1101 (of_decide_eq_true rfl))
  have e_v1127 : v1127 = if v1126 = 1 then v1093 else v1101 := e_psel h_v1126 h_v1093 h_v1101 (of_decide_eq_true rfl)
  have h_v1128 : R 1 0 4611686015743033304 4683743614612799504 v1128 v1128 := (r_smx hl 29 h_v1121 h_v1117 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1128 : sv v1128 = sv v1121 * sv v1117 := e_smx 29 h_v1121 h_v1117 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1129 : R 1 0 4611686018427387893 4611686018695823368 v1129 v1129 := (r_srdF hl h_v1128 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v1129 : sv v1129 = sv v1128 / 2 ^ 28 := e_srdF h_v1128 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v1130 : R 1 0 4611686015743033304 4683743614612799504 v1130 v1130 := (r_smx hl 29 h_v1127 h_v1124 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1130 : sv v1130 = sv v1127 * sv v1124 := e_smx 29 h_v1127 h_v1124 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1131 : R 1 0 4611686018427387894 4611686018695823369 v1131 v1131 := (r_srdC hl h_v1130 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v1131 : sv v1131 = -((-sv v1130) / 2 ^ 28) := e_srdC h_v1130 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1132 : R 1 0 4611686015743033304 4683743613539057664 v1132 v1132 := (r_smx hl 29 h_v1093 h_v1069 4611686015743033304 4683743613539057664 (of_decide_eq_true rfl))
  have e_v1132 : sv v1132 = sv v1093 * sv v1069 := e_smx 29 h_v1093 h_v1069 4611686015743033304 4683743613539057664 (of_decide_eq_true rfl)
  have h_v1133 : R 1 0 4611686018427387893 4611686018695823364 v1133 v1133 := (r_srdF hl h_v1132 4611686018427387893 4611686018695823364 (of_decide_eq_true rfl))
  have e_v1133 : sv v1133 = sv v1132 / 2 ^ 28 := e_srdF h_v1132 4611686018427387893 4611686018695823364 (of_decide_eq_true rfl)
  have h_v1134 : R 1 0 4611686015743033344 4683743612465315840 v1134 v1134 := (r_smx hl 29 h_v1093 h_v1060 4611686015743033344 4683743612465315840 (of_decide_eq_true rfl))
  have e_v1134 : sv v1134 = sv v1093 * sv v1060 := e_smx 29 h_v1093 h_v1060 4611686015743033344 4683743612465315840 (of_decide_eq_true rfl)
  have h_v1135 : R 1 0 4611686018427387894 4611686018695823360 v1135 v1135 := (r_srdC hl h_v1134 4611686018427387894 4611686018695823360 (of_decide_eq_true rfl))
  have e_v1135 : sv v1135 = -((-sv v1134) / 2 ^ 28) := e_srdC h_v1134 4611686018427387894 4611686018695823360 (of_decide_eq_true rfl)
  have h_v1136 : R 1 0 0 1 v1136 v1136 := (r_plt hl h_v1129 h_v1133 (of_decide_eq_true rfl))
  have e_v1136 : (v1136 = 1 ↔ sv v1129 < sv v1133) := e_plt h_v1129 h_v1133 (of_decide_eq_true rfl)
  have h_v1137 : R 1 0 4611686018427387893 4611686018695823368 v1137 v1137 := (r_psel hl h_v1136 h_v1129 h_v1133 (of_decide_eq_true rfl))
  have e_v1137 : v1137 = if v1136 = 1 then v1129 else v1133 := e_psel h_v1136 h_v1129 h_v1133 (of_decide_eq_true rfl)
  have h_v1138 : R 1 0 0 1 v1138 v1138 := (r_plt hl h_v1131 h_v1135 (of_decide_eq_true rfl))
  have e_v1138 : (v1138 = 1 ↔ sv v1131 < sv v1135) := e_plt h_v1131 h_v1135 (of_decide_eq_true rfl)
  clear h_v1060 h_v1069 h_v1093 h_v1101 h_v1106 h_v1117 h_v1121 h_v1124 h_v1125 h_v1126 h_v1127 h_v1128 h_v1130 h_v1132 h_v1133 h_v1134 h_v1136
  have h_v1139 : R 1 0 4611686018427387894 4611686018695823369 v1139 v1139 := (r_psel hl h_v1138 h_v1135 h_v1131 (of_decide_eq_true rfl))
  have e_v1139 : v1139 = if v1138 = 1 then v1135 else v1131 := e_psel h_v1138 h_v1135 h_v1131 (of_decide_eq_true rfl)
  have h_v1140 : R 1 0 4611686018427387893 4611686018695823368 v1140 v1140 := (r_psel hl h_v1114 h_v1137 h_v1129 (of_decide_eq_true rfl))
  have e_v1140 : v1140 = if v1114 = 1 then v1137 else v1129 := e_psel h_v1114 h_v1137 h_v1129 (of_decide_eq_true rfl)
  have h_v1141 : R 1 0 4611686018427387894 4611686018695823369 v1141 v1141 := (r_psel hl h_v1114 h_v1139 h_v1131 (of_decide_eq_true rfl))
  have e_v1141 : v1141 = if v1114 = 1 then v1139 else v1131 := e_psel h_v1114 h_v1139 h_v1131 (of_decide_eq_true rfl)
  have h_v1142 : R 1 0 0 1 v1142 v1142 := (r_plt hl h_v61 h_v1140 (of_decide_eq_true rfl))
  have e_v1142 : (v1142 = 1 ↔ sv v61 < sv v1140) := e_plt h_v61 h_v1140 (of_decide_eq_true rfl)
  have h_v1143 : R 1 0 0 1 v1143 v1143 := (r_sub hl (r_O hl) h_v1142 (of_decide_eq_true rfl))
  have e_v1143 : (v1143 = 1 ↔ ¬v1142 = 1) := e_not h_v1142 (of_decide_eq_true rfl)
  have h_v1146 : R 1 0 0 1 v1146 v1146 := (r_plt hl h_v1035 h_v61 (of_decide_eq_true rfl))
  have e_v1146 : (v1146 = 1 ↔ sv v1035 < sv v61) := e_plt h_v1035 h_v61 (of_decide_eq_true rfl)
  have h_v1147 : R 1 0 4611686018427387893 4611686018695823369 v1147 v1147 := (r_psel hl h_v1146 h_v1141 h_v1140 (of_decide_eq_true rfl))
  have e_v1147 : v1147 = if v1146 = 1 then v1141 else v1140 := e_psel h_v1146 h_v1141 h_v1140 (of_decide_eq_true rfl)
  have h_v1148 : R 1 0 4611686018158952439 4611686018427387915 v1148 v1148 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v1147 (of_decide_eq_true rfl))
  have e_v1148 : sv v1148 = sv v61 - sv v1147 := e_sub h_v61 h_v1147 (of_decide_eq_true rfl)
  have h_v1149 : R 1 0 0 1 v1149 v1149 := (r_plt hl h_v1035 h_v1148 (of_decide_eq_true rfl))
  have e_v1149 : (v1149 = 1 ↔ sv v1035 < sv v1148) := e_plt h_v1035 h_v1148 (of_decide_eq_true rfl)
  have h_v1150 : R 1 0 0 1 v1150 v1150 := (r_land hl h_v1142 h_v1149 (of_decide_eq_true rfl))
  have e_v1150 : (v1150 = 1 ↔ v1142 = 1 ∧ v1149 = 1) := e_land h_v1142 h_v1149 (of_decide_eq_true rfl)
  have h_v1151 : R 1 0 0 1 v1151 v1151 := (r_plt hl h_v1035 h_v1147 (of_decide_eq_true rfl))
  have e_v1151 : (v1151 = 1 ↔ sv v1035 < sv v1147) := e_plt h_v1035 h_v1147 (of_decide_eq_true rfl)
  have h_v1152 : R 1 0 0 1 v1152 v1152 := (r_sub hl (r_O hl) h_v1151 (of_decide_eq_true rfl))
  have e_v1152 : (v1152 = 1 ↔ ¬v1151 = 1) := e_not h_v1151 (of_decide_eq_true rfl)
  have h_v1153 : R 1 0 0 1 v1153 v1153 := (r_lor hl h_v1143 h_v1152 (of_decide_eq_true rfl))
  clear h_OFFr h_v61 h_v1114 h_v1129 h_v1131 h_v1135 h_v1137 h_v1138 h_v1139 h_v1140 h_v1141 h_v1142 h_v1146 h_v1148 h_v1149 h_v1151
  have e_v1153 : (v1153 = 1 ↔ v1143 = 1 ∨ v1152 = 1) := e_lor h_v1143 h_v1152 (of_decide_eq_true rfl)
  have h_v1154 : R 1 0 4611686017890516812 4611686018964258878 v1154 v1154 := (r_psel hl h_v1153 h_v33 h_v1035 (of_decide_eq_true rfl))
  have e_v1154 : v1154 = if v1153 = 1 then v33 else v1035 := e_psel h_v1153 h_v33 h_v1035 (of_decide_eq_true rfl)
  have h_v1155 : R 1 0 4611686018427387893 4611686018695823369 v1155 v1155 := (r_psel hl h_v1153 h_v33 h_v1147 (of_decide_eq_true rfl))
  have e_v1155 : v1155 = if v1153 = 1 then v33 else v1147 := e_psel h_v1153 h_v33 h_v1147 (of_decide_eq_true rfl)
  exact fun _ k => k e_v674 e_v675 e_v676 e_v677 e_v678 e_v679 e_v680 e_v681 e_v682 e_v683 e_v684 e_v685 e_v686 e_v687 e_v688 e_v689 e_v690 e_v691 e_v692 e_v693 e_v694 e_v697 e_v698 e_v740 e_v741 e_v742 e_t742_1 e_t742_2 e_v744 e_v745 e_v746 e_v747 e_v748 e_v749 e_v751 e_v752 e_v753 e_v754 e_v755 e_v756 e_v757 e_v758 e_v759 e_v760 e_v761 e_v762 e_v763 e_v764 e_v765 e_v766 e_v767 e_v768 e_v769 e_v770 e_v771 e_v772 e_v773 e_v774 e_v775 e_v776 e_v777 e_v778 e_v779 e_v780 h_v782 e_v782 e_v783 e_v784 e_v785 e_v786 e_v787 e_v788 h_v789 e_v789 e_t783_1 e_t785_1 e_v792 e_v793 e_v794 e_v795 e_v796 e_v797 e_v798 e_v799 e_v800 e_v801 e_v802 e_v803 e_v805 e_v806 e_v807 e_v808 e_v809 e_v810 e_v811 e_v812 e_v813 e_v814 e_v815 e_v816 e_v817 e_v818 e_v819 e_v820 e_v821 e_v822 e_v823 e_v824 e_v825 e_v826 e_v827 e_v828 e_v829 e_v830 e_v831 e_v832 e_v833 e_v834 h_v835 e_v835 h_v836 e_v836 h_v837 e_v837 e_v838 e_v839 e_v840 e_v841 e_v842 e_v843 e_v844 e_v845 h_v846 e_v846 e_v847 h_v848 e_v848 e_v849 e_v850 e_v851 e_v852 e_v853 h_v854 e_v854 e_v855 e_v856 e_v857 h_v858 e_v858 e_v859 e_v860 e_v861 e_v862 e_v863 h_v864 e_v864 e_v865 e_v866 e_v867 h_v868 e_v868 e_v869 e_v870 e_v871 e_v872 e_v873 h_v874 e_v874 e_v875 e_v876 e_v877 h_v878 e_v878 e_v879 e_v880 e_v881 e_v882 h_v883 e_v883 h_v884 e_v884 e_v885 h_v886 e_v886 e_v887 e_v888 h_v889 e_v889 h_v890 e_v890 h_v891 e_v891 e_v892 e_v893 e_v894 e_v895 e_v896 e_v897 e_v898 e_v899 e_v900 e_v901 e_v902 e_v903 e_v904 e_v905 e_v906 e_v907 e_v908 e_v909 e_v910 e_v911 e_v912 e_v913 e_v914 e_v915 e_v916 e_v917 e_v918 e_v919 e_v920 e_v921 h_v922 e_v922 e_v923 e_v924 h_v925 e_v925 h_v926 e_v926 e_v927 e_v928 e_v929 e_v930 h_v931 e_v931 e_v932 e_v933 e_v934 e_v935 e_v936 e_v937 e_v938 e_v939 e_v940 e_v941 e_v942 e_v943 e_v944 e_v945 e_v946 e_v947 e_v948 e_v949 e_v950 e_v951 e_v952 e_v953 e_v954 e_v955 e_v956 h_v957 e_v957 e_v958 e_v959 e_v960 e_v961 e_v962 h_v963 e_v963 h_v964 e_v964 e_v965 e_v966 h_v967 e_v967 h_v968 e_v968 e_v974 e_v975 e_v976 e_v977 e_v978 e_v979 e_v980 e_v981 e_v982 e_v983 e_v984 e_v985 e_v986 e_v987 e_v988 e_v989 e_v990 e_v991 e_v992 e_v993 e_v994 e_v995 e_v996 e_v997 e_v998 e_v999 e_v1000 e_v1002 e_v1003 e_v1004 e_v1005 e_v1006 e_v1007 e_v1008 e_v1009 e_v1010 e_v1011 e_v1012 e_v1013 e_v1020 e_v1021 e_v1024 e_v1025 e_v1028 e_v1029 e_v1032 e_v1035 e_v1036 e_v1037 e_v1038 e_v1039 e_v1040 e_v1041 e_v1042 e_v1043 e_v1044 e_v1045 e_v1046 e_v1047 e_v1048 e_v1049 e_v1050 e_v1051 e_v1052 e_v1053 e_v1054 e_v1055 e_v1056 e_v1057 e_v1058 e_v1059 e_v1060 e_v1061 e_v1062 e_v1063 e_v1064 e_v1065 e_v1066 e_v1067 e_v1068 e_v1069 e_v1070 e_v1071 e_v1072 e_v1073 e_v1074 e_v1075 e_v1076 e_v1077 e_v1078 e_v1079 e_v1080 e_v1081 e_v1082 e_v1083 e_v1084 e_v1085 e_v1086 e_v1087 e_v1088 e_v1089 e_v1090 e_v1091 e_v1092 e_v1093 e_v1094 e_v1095 e_v1096 e_v1097 e_v1098 e_v1099 e_v1100 e_v1101 e_v1102 e_v1103 e_v1104 e_v1105 e_v1106 e_v1107 e_v1108 e_v1110 e_v1111 e_v1112 e_v1113 e_v1114 e_v1115 e_v1116 e_v1117 e_v1118 e_v1119 e_v1120 e_v1121 e_v1122 e_v1123 e_v1124 e_v1125 e_v1126 e_v1127 e_v1128 e_v1129 e_v1130 e_v1131 e_v1132 e_v1133 e_v1134 e_v1135 e_v1136 e_v1137 e_v1138 e_v1139 e_v1140 e_v1141 e_v1142 e_v1143 e_v1146 e_v1147 e_v1148 e_v1149 h_v1150 e_v1150 e_v1151 e_v1152 e_v1153 h_v1154 e_v1154 h_v1155 e_v1155

end Tammes15.D3Trig
