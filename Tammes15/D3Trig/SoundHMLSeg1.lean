import Tammes15.D3Trig.Prog.HML
import Tammes15.D3Prog.Sem

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progHML_seg1 (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (hb_H4 : H4 < 2 ^ 64) (v13 : ℕ) (v29 : ℕ) (v41 : ℕ) (v63 : ℕ) (v66 : ℕ) (v67 : ℕ) (v89 : ℕ) (v91 : ℕ) (v438 : ℕ) (v440 : ℕ) (v634 : ℕ) (v637 : ℕ) (v702 : ℕ) (v710 : ℕ) (v711 : ℕ) (h_v13 : R 1 0 0 1 v13 v13) (h_v29 : R 1 0 4611686018427387900 4611686018695823359 v29 v29) (h_v41 : R 1 0 4611686018427387908 4611686018695823367 v41 v41) (h_v63 : R 1 0 0 1 v63 v63) (h_v66 : R 1 0 0 1 v66 v66) (h_v67 : R 1 0 0 1 v67 v67) (h_v89 : R 1 0 4611686018427387899 4611686018695823374 v89 v89) (h_v91 : R 1 0 4611686018427387900 4611686018695823375 v91 v91) (h_v438 : R 1 0 4611686018427387899 4611686018695823374 v438 v438) (h_v440 : R 1 0 4611686018427387900 4611686018695823375 v440 v440) (h_v634 : R 1 0 0 1 v634 v634) (h_v637 : R 1 0 0 1 v637 v637) (h_v702 : R 1 0 0 1 v702 v702) (h_v710 : R 1 0 0 1 v710 v710) (h_v711 : R 1 0 0 1 v711 v711) :
    let OFFr := Nat.mul 1 4611686018427387904
    let H61r := Nat.mul 1 2305843009213693952
    let v7 := ix 1 F3 32
    let v9 := Nat.mul 1 4611686019270702761
    let v15 := Nat.mul 1 4611686019270702760
    let v19 := Nat.mul 1 4611686018427387903
    let v28 := Nat.mul 1 4611686018427387900
    let v31 := Nat.mul 1 4611686018427387908
    let v33 := Nat.mul 1 4611686018695823360
    let v36 := Nat.mul 1 4611686018849045334
    let v38 := Nat.mul 1 4611686018849045331
    let v61 := Nat.mul 1 4611686018427387904
    let v95 := Nat.mul 1 4611686018158952448
    let v105 := Nat.mul 1 4611686018427387905
    let v203 := Nat.mul 1 4611686018849045333
    let v682 := hxa 1 H1 32
    let v712 := Nat.sub 1 v711
    let v713 := Nat.lor v702 v712
    let v714 := Nat.land v637 v710
    let v715 := Nat.sub 1 v637
    let v716 := Nat.land v713 v715
    let v717 := Nat.lor v714 v716
    let v718 := Nat.sub (Nat.add v61 OFFr) v682
    let v719 := psel (pmask v637) v718 v682
    let v720 := psel (pmask v717) v719 v203
    let v722 := psel (pmask v634) v203 v720
    let v723 := Nat.add (pshr1 1 v7) H61r
    let v724 := Nat.add (pshr1 1 (Nat.add v7 1)) H61r
    let v725 := psel (pmask v13) v724 v203
    let v726 := plt 1 v19 v723
    let v727 := plt 1 v9 v725
    let v728 := Nat.sub 1 v727
    let v729 := Nat.land v726 v728
    let t723 := sc28u 1 v723
    let t725 := sc28u 1 v725
    let v732 := plt 1 t723.1 t725.1
    let v733 := psel (pmask v732) t723.1 t725.1
    let v734 := Nat.sub (Nat.add v28 v733) OFFr
    let v735 := psel (pmask v732) t725.1 t723.1
    let v736 := Nat.sub (Nat.add v31 v735) OFFr
    let v737 := plt 1 v736 v33
    let v738 := psel (pmask v737) v736 v33
    let v739 := plt 1 v723 v36
    let v740 := plt 1 v38 v725
    let v741 := Nat.land v739 v740
    let v742 := psel (pmask v741) v33 v738
    let v743 := plt 1 v734 v61
    let v744 := Nat.sub 1 v743
    let v745 := plt 1 v61 v742
    let v746 := Nat.sub 1 v745
    let v747 := Nat.land v743 v746
    let v748 := Nat.land v743 v745
    let v749 := Nat.land v67 v748
    let v750 := Nat.sub 1 v749
    let v751 := Nat.land v63 v748
    let v752 := Nat.lor v747 v751
    let v753 := psel (pmask v752) v41 v29
    let v754 := Nat.land v67 v744
    let v755 := Nat.lor v66 v754
    let v756 := psel (pmask v755) v742 v734
    let v757 := Nat.land v66 v748
    let v758 := Nat.lor v747 v757
    let v759 := psel (pmask v758) v29 v41
    let v760 := Nat.land v67 v747
    let v761 := Nat.lor v66 v760
    let v762 := psel (pmask v761) v734 v742
    let v763 := smx 29 1 v756 v753
    let v764 := srdF 1 v763
    let v765 := smx 29 1 v762 v759
    let v766 := srdC 1 v765
    let v767 := plt 1 v19 v764
    let v768 := plt 1 v61 v438
    let v769 := plt 1 v440 v33
    let v770 := Nat.land v768 v769
    let v771 := plt 1 v61 v89
    let v772 := plt 1 v91 v33
    let v773 := Nat.land v771 v772
    let v774 := plt 1 v61 v764
    let v775 := plt 1 v766 v33
    let v776 := Nat.land v774 v775
    let v777 := Nat.land v770 v773
    let v778 := Nat.land v776 v777
    let v779 := smx 29 1 v440 v440
    let v780 := srdC 1 v779
    let v781 := Nat.sub (Nat.add v780 v780) OFFr
    let v782 := Nat.sub (Nat.add v33 OFFr) v781
    let v783 := plt 1 v782 v95
    let v784 := psel (pmask v783) v95 v782
    let v785 := smx 29 1 v438 v438
    let v786 := srdF 1 v785
    let v787 := Nat.sub (Nat.add v786 v786) OFFr
    let v788 := Nat.sub (Nat.add v33 OFFr) v787
    let v789 := smx 29 1 v766 v766
    let v790 := srdC 1 v789
    let v791 := Nat.sub (Nat.add v790 v790) OFFr
    let v792 := Nat.sub (Nat.add v33 OFFr) v791
    let v793 := plt 1 v792 v95
    let v794 := psel (pmask v793) v95 v792
    let v795 := smx 29 1 v764 v764
    let v796 := srdF 1 v795
    let v797 := Nat.sub (Nat.add v796 v796) OFFr
    let v798 := Nat.sub (Nat.add v33 OFFr) v797
    let v799 := smx 29 1 v91 v91
    let v800 := srdC 1 v799
    let v801 := Nat.sub (Nat.add v800 v800) OFFr
    let v802 := Nat.sub (Nat.add v33 OFFr) v801
    let v803 := plt 1 v802 v95
    let v804 := psel (pmask v803) v95 v802
    let v805 := smx 29 1 v89 v89
    let v806 := srdF 1 v805
    let v807 := Nat.sub (Nat.add v806 v806) OFFr
    let v808 := Nat.sub (Nat.add v33 OFFr) v807
    let v809 := plt 1 v784 v61
    let v810 := Nat.sub 1 v809
    let v811 := plt 1 v61 v788
    let v812 := Nat.sub 1 v811
    let v813 := Nat.land v809 v812
    let v814 := Nat.land v809 v811
    let v815 := plt 1 v804 v61
    let v816 := Nat.sub 1 v815
    let v817 := plt 1 v61 v808
    let v818 := Nat.sub 1 v817
    let v819 := Nat.land v815 v818
    let v820 := Nat.land v815 v817
    let v821 := Nat.land v814 v820
    let v822 := Nat.sub 1 v821
    let v823 := Nat.sub 1 v778
    let v824 := Nat.lor v822 v823
    let v825 := Nat.land v810 v820
    let v826 := Nat.lor v819 v825
    let v827 := psel (pmask v826) v788 v784
    let v828 := Nat.land v814 v816
    let v829 := Nat.lor v813 v828
    let v830 := psel (pmask v829) v808 v804
    let v831 := Nat.land v813 v820
    let v832 := Nat.lor v819 v831
    let v833 := psel (pmask v832) v784 v788
    let v834 := Nat.land v814 v819
    let v835 := Nat.lor v813 v834
    let v836 := psel (pmask v835) v804 v808
    let v837 := smx 30 1 v830 v827
    let v838 := srdF 1 v837
    let v839 := smx 30 1 v836 v833
    let v840 := srdC 1 v839
    let v841 := Nat.sub (Nat.add v794 OFFr) v840
    let v842 := Nat.sub (Nat.add v798 OFFr) v838
    let v843 := plt 1 v794 v61
    let v844 := Nat.sub 1 v843
    let v845 := plt 1 v61 v798
    let v846 := Nat.sub 1 v845
    let v847 := Nat.land v843 v846
    let v848 := Nat.land v843 v845
    let v849 := Nat.land v814 v848
    let v850 := Nat.sub 1 v849
    let v851 := Nat.lor v823 v850
    let v852 := Nat.land v810 v848
    let v853 := Nat.lor v847 v852
    let v854 := psel (pmask v853) v788 v784
    let v855 := Nat.land v814 v844
    let v856 := Nat.lor v813 v855
    let v857 := psel (pmask v856) v798 v794
    let v858 := Nat.land v813 v848
    let v859 := Nat.lor v847 v858
    let v860 := psel (pmask v859) v784 v788
    let v861 := Nat.land v814 v847
    let v862 := Nat.lor v813 v861
    let v863 := psel (pmask v862) v794 v798
    let v864 := smx 30 1 v857 v854
    let v865 := srdF 1 v864
    let v866 := smx 30 1 v863 v860
    let v867 := srdC 1 v866
    let v868 := Nat.sub (Nat.add v804 OFFr) v867
    let v869 := Nat.sub (Nat.add v808 OFFr) v865
    let v870 := plt 1 v61 v841
    let v871 := plt 1 v842 v61
    let v872 := plt 1 v61 v868
    let v873 := plt 1 v869 v61
    let v874 := psel (pmask v870) v91 v89
    let v875 := psel (pmask v871) v89 v91
    let v876 := psel (pmask v871) v91 v89
    let v877 := psel (pmask v870) v89 v91
    let v878 := psel (pmask v872) v766 v764
    let v879 := psel (pmask v873) v764 v766
    let v880 := psel (pmask v873) v766 v764
    let v881 := psel (pmask v872) v764 v766
    let v887 := smx 29 1 v875 v875
    let v888 := srdC 1 v887
    let v889 := Nat.sub (Nat.add v888 v888) OFFr
    let v890 := Nat.sub (Nat.add v33 OFFr) v889
    let v891 := plt 1 v890 v95
    let v892 := psel (pmask v891) v95 v890
    let v893 := smx 29 1 v874 v874
    let v894 := srdF 1 v893
    let v895 := Nat.sub (Nat.add v894 v894) OFFr
    let v896 := Nat.sub (Nat.add v33 OFFr) v895
    let v897 := smx 29 1 v879 v879
    let v898 := srdC 1 v897
    let v899 := Nat.sub (Nat.add v898 v898) OFFr
    let v900 := Nat.sub (Nat.add v33 OFFr) v899
    let v901 := plt 1 v900 v95
    let v902 := psel (pmask v901) v95 v900
    let v903 := smx 29 1 v878 v878
    let v904 := srdF 1 v903
    let v905 := Nat.sub (Nat.add v904 v904) OFFr
    let v906 := Nat.sub (Nat.add v33 OFFr) v905
    let v907 := plt 1 v892 v61
    let v908 := Nat.sub 1 v907
    let v909 := plt 1 v61 v896
    let v910 := Nat.sub 1 v909
    let v911 := Nat.land v907 v910
    let v912 := Nat.land v907 v909
    let v913 := plt 1 v902 v61
    let v914 := Nat.sub 1 v913
    let v915 := plt 1 v61 v906
    let v916 := Nat.sub 1 v915
    let v917 := Nat.land v913 v916
    let v918 := Nat.land v913 v915
    let v919 := Nat.land v912 v918
    let v920 := Nat.sub 1 v919
    let v921 := Nat.lor v823 v920
    let v922 := Nat.land v908 v918
    let v923 := Nat.lor v917 v922
    let v924 := psel (pmask v923) v896 v892
    let v925 := Nat.land v912 v914
    let v926 := Nat.lor v911 v925
    let v927 := psel (pmask v926) v906 v902
    let v934 := smx 30 1 v927 v924
    let v935 := srdF 1 v934
    let v939 := Nat.sub (Nat.add v788 OFFr) v935
    let v940 := Nat.mul 1 4683743612465315840
    let v941 := Nat.sub (Nat.add v940 OFFr) v893
    let v942 := psqrt 1 v941
    let v943 := Nat.sub (Nat.add v105 v942) OFFr
    let v944 := smx 29 1 v942 v874
    let v945 := srdF 1 v944
    let v946 := Nat.sub (Nat.add v945 v945) OFFr
    let v947 := smx 29 1 v943 v874
    let v948 := srdC 1 v947
    let v949 := Nat.sub (Nat.add v948 v948) OFFr
    let v950 := plt 1 v949 v33
    let v951 := psel (pmask v950) v949 v33
    let v952 := Nat.sub (Nat.add v940 OFFr) v887
    let v953 := psqrt 1 v952
    let v954 := Nat.sub (Nat.add v105 v953) OFFr
    let v955 := smx 29 1 v953 v875
    let v956 := srdF 1 v955
    let v957 := Nat.sub (Nat.add v956 v956) OFFr
    let v958 := smx 29 1 v954 v875
    let v959 := srdC 1 v958
    let v960 := Nat.sub (Nat.add v959 v959) OFFr
    let v961 := plt 1 v960 v33
    let v962 := psel (pmask v961) v960 v33
    let v963 := plt 1 v946 v957
    let v964 := psel (pmask v963) v946 v957
    let v965 := plt 1 v951 v962
    let v966 := psel (pmask v965) v962 v951
    let v967 := Nat.mul 1 4647714815446351872
    let v968 := plt 1 v967 v893
    let v969 := Nat.sub 1 v968
    let v970 := plt 1 v887 v967
    let v971 := Nat.sub 1 v970
    let v972 := Nat.land v969 v971
    let v973 := psel (pmask v972) v33 v966
    let v974 := Nat.sub (Nat.add v940 OFFr) v903
    let v975 := psqrt 1 v974
    let v976 := Nat.sub (Nat.add v105 v975) OFFr
    let v977 := smx 29 1 v975 v878
    let v978 := srdF 1 v977
    let v979 := Nat.sub (Nat.add v978 v978) OFFr
    let v980 := smx 29 1 v976 v878
    let v981 := srdC 1 v980
    let v982 := Nat.sub (Nat.add v981 v981) OFFr
    let v983 := plt 1 v982 v33
    let v984 := psel (pmask v983) v982 v33
    let v985 := Nat.sub (Nat.add v940 OFFr) v897
    let v986 := psqrt 1 v985
    let v987 := Nat.sub (Nat.add v105 v986) OFFr
    let v988 := smx 29 1 v986 v879
    let v989 := srdF 1 v988
    let v990 := Nat.sub (Nat.add v989 v989) OFFr
    let v991 := smx 29 1 v987 v879
    let v992 := srdC 1 v991
    let v993 := Nat.sub (Nat.add v992 v992) OFFr
    let v994 := plt 1 v993 v33
    let v995 := psel (pmask v994) v993 v33
    let v996 := plt 1 v979 v990
    let v997 := psel (pmask v996) v979 v990
    let v998 := plt 1 v984 v995
    let v999 := psel (pmask v998) v995 v984
    let v1000 := plt 1 v967 v903
    let v1001 := Nat.sub 1 v1000
    let v1002 := plt 1 v897 v967
    let v1003 := Nat.sub 1 v1002
    let v1004 := Nat.land v1001 v1003
    let v1005 := psel (pmask v1004) v33 v999
    let v1006 := plt 1 v964 v61
    let v1007 := Nat.sub 1 v1006
    let v1008 := plt 1 v61 v973
    let v1009 := Nat.sub 1 v1008
    let v1010 := Nat.land v1006 v1009
    let v1011 := Nat.land v1006 v1008
    let v1012 := plt 1 v997 v61
    let v1013 := Nat.sub 1 v1012
    let v1014 := plt 1 v61 v1005
    let v1015 := Nat.sub 1 v1014
    let v1016 := Nat.land v1012 v1015
    let v1017 := Nat.land v1012 v1014
    let v1018 := Nat.land v1011 v1017
    let v1019 := Nat.sub 1 v1018
    let v1020 := Nat.lor v823 v1019
    let v1021 := Nat.land v1007 v1017
    let v1022 := Nat.lor v1016 v1021
    let v1023 := psel (pmask v1022) v973 v964
    let v1024 := Nat.land v1011 v1013
    let v1025 := Nat.lor v1010 v1024
    let v1026 := psel (pmask v1025) v1005 v997
    let v1027 := Nat.land v1010 v1017
    let v1028 := Nat.lor v1016 v1027
    let v1029 := psel (pmask v1028) v964 v973
    let v1030 := Nat.land v1011 v1016
    let v1031 := Nat.lor v1010 v1030
    let v1032 := psel (pmask v1031) v997 v1005
    let v1033 := smx 29 1 v1026 v1023
    let v1034 := srdF 1 v1033
    let v1035 := smx 29 1 v1032 v1029
    let v1036 := srdC 1 v1035
    let v1037 := plt 1 v61 v1034
    let v1038 := Nat.sub 1 v1037
    let v1041 := plt 1 v939 v61
    let v1042 := psel (pmask v1041) v1036 v1034
    let v1043 := Nat.sub (Nat.add v61 OFFr) v1042
    let v1044 := plt 1 v939 v1043
    let v1045 := Nat.land v1037 v1044
    let v1046 := plt 1 v939 v1042
    let v1047 := Nat.sub 1 v1046
    let v1048 := Nat.lor v1038 v1047
    let v1049 := psel (pmask v1048) v33 v939
    let v1050 := psel (pmask v1048) v33 v1042
    let v1054 := smx 29 1 v877 v877
    let v1055 := srdC 1 v1054
    let v1056 := Nat.sub (Nat.add v1055 v1055) OFFr
    let v1057 := Nat.sub (Nat.add v33 OFFr) v1056
    let v1058 := plt 1 v1057 v95
    let v1059 := psel (pmask v1058) v95 v1057
    let v1060 := smx 29 1 v876 v876
    let v1061 := srdF 1 v1060
    let v1062 := Nat.sub (Nat.add v1061 v1061) OFFr
    let v1063 := Nat.sub (Nat.add v33 OFFr) v1062
    let v1064 := smx 29 1 v881 v881
    let v1065 := srdC 1 v1064
    let v1066 := Nat.sub (Nat.add v1065 v1065) OFFr
    let v1067 := Nat.sub (Nat.add v33 OFFr) v1066
    let v1068 := plt 1 v1067 v95
    let v1069 := psel (pmask v1068) v95 v1067
    let v1070 := smx 29 1 v880 v880
    let v1071 := srdF 1 v1070
    let v1072 := Nat.sub (Nat.add v1071 v1071) OFFr
    let v1073 := Nat.sub (Nat.add v33 OFFr) v1072
    let v1074 := plt 1 v1059 v61
    let v1076 := plt 1 v61 v1063
    let v1077 := Nat.sub 1 v1076
    let v1078 := Nat.land v1074 v1077
    let v1079 := Nat.land v1074 v1076
    let v1080 := plt 1 v1069 v61
    let v1082 := plt 1 v61 v1073
    let v1083 := Nat.sub 1 v1082
    let v1084 := Nat.land v1080 v1083
    let v1085 := Nat.land v1080 v1082
    let v1086 := Nat.land v1079 v1085
    let v1087 := Nat.sub 1 v1086
    let v1088 := Nat.lor v823 v1087
    let v1095 := Nat.land v1078 v1085
    let v1096 := Nat.lor v1084 v1095
    let v1097 := psel (pmask v1096) v1059 v1063
    let v1098 := Nat.land v1079 v1084
    let v1099 := Nat.lor v1078 v1098
    let v1100 := psel (pmask v1099) v1069 v1073
    let v1103 := smx 30 1 v1100 v1097
    let v1104 := srdC 1 v1103
    let v1105 := Nat.sub (Nat.add v784 OFFr) v1104
    let v1107 := Nat.sub (Nat.add v940 OFFr) v1060
    let v1108 := psqrt 1 v1107
    let v1109 := Nat.sub (Nat.add v105 v1108) OFFr
    let v1110 := smx 29 1 v1108 v876
    let v1111 := srdF 1 v1110
    let v1112 := Nat.sub (Nat.add v1111 v1111) OFFr
    let v1113 := smx 29 1 v1109 v876
    let v1114 := srdC 1 v1113
    let v1115 := Nat.sub (Nat.add v1114 v1114) OFFr
    let v1116 := plt 1 v1115 v33
    let v1117 := psel (pmask v1116) v1115 v33
    let v1118 := Nat.sub (Nat.add v940 OFFr) v1054
    let v1119 := psqrt 1 v1118
    let v1120 := Nat.sub (Nat.add v105 v1119) OFFr
    let v1121 := smx 29 1 v1119 v877
    let v1122 := srdF 1 v1121
    let v1123 := Nat.sub (Nat.add v1122 v1122) OFFr
    let v1124 := smx 29 1 v1120 v877
    let v1125 := srdC 1 v1124
    let v1126 := Nat.sub (Nat.add v1125 v1125) OFFr
    let v1127 := plt 1 v1126 v33
    let v1128 := psel (pmask v1127) v1126 v33
    let v1129 := plt 1 v1112 v1123
    let v1130 := psel (pmask v1129) v1112 v1123
    let v1131 := plt 1 v1117 v1128
    let v1132 := psel (pmask v1131) v1128 v1117
    let v1133 := plt 1 v967 v1060
    let v1134 := Nat.sub 1 v1133
    let v1135 := plt 1 v1054 v967
    let v1136 := Nat.sub 1 v1135
    let v1137 := Nat.land v1134 v1136
    let v1138 := psel (pmask v1137) v33 v1132
    let v1139 := Nat.sub (Nat.add v940 OFFr) v1070
    let v1140 := psqrt 1 v1139
    let v1141 := Nat.sub (Nat.add v105 v1140) OFFr
    let v1142 := smx 29 1 v1140 v880
    let v1143 := srdF 1 v1142
    let v1144 := Nat.sub (Nat.add v1143 v1143) OFFr
    let v1145 := smx 29 1 v1141 v880
    let v1146 := srdC 1 v1145
    let v1147 := Nat.sub (Nat.add v1146 v1146) OFFr
    let v1148 := plt 1 v1147 v33
    let v1149 := psel (pmask v1148) v1147 v33
    let v1150 := Nat.sub (Nat.add v940 OFFr) v1064
    let v1151 := psqrt 1 v1150
    let v1152 := Nat.sub (Nat.add v105 v1151) OFFr
    let v1153 := smx 29 1 v1151 v881
    let v1154 := srdF 1 v1153
    let v1155 := Nat.sub (Nat.add v1154 v1154) OFFr
    let v1156 := smx 29 1 v1152 v881
    let v1157 := srdC 1 v1156
    let v1158 := Nat.sub (Nat.add v1157 v1157) OFFr
    let v1159 := plt 1 v1158 v33
    let v1160 := psel (pmask v1159) v1158 v33
    let v1161 := plt 1 v1144 v1155
    let v1162 := psel (pmask v1161) v1144 v1155
    let v1163 := plt 1 v1149 v1160
    let v1164 := psel (pmask v1163) v1160 v1149
    let v1165 := plt 1 v967 v1070
    let v1166 := Nat.sub 1 v1165
    let v1167 := plt 1 v1064 v967
    let v1168 := Nat.sub 1 v1167
    let v1169 := Nat.land v1166 v1168
    let v1170 := psel (pmask v1169) v33 v1164
    let v1171 := plt 1 v1130 v61
    let v1172 := Nat.sub 1 v1171
    let v1173 := plt 1 v61 v1138
    let v1174 := Nat.sub 1 v1173
    let v1175 := Nat.land v1171 v1174
    let v1176 := Nat.land v1171 v1173
    let v1177 := plt 1 v1162 v61
    let v1178 := Nat.sub 1 v1177
    let v1179 := plt 1 v61 v1170
    let v1180 := Nat.sub 1 v1179
    let v1181 := Nat.land v1177 v1180
    let v1182 := Nat.land v1177 v1179
    let v1183 := Nat.land v1176 v1182
    let v1184 := Nat.sub 1 v1183
    let v1185 := Nat.lor v823 v1184
    let v1186 := Nat.land v1172 v1182
    let v1187 := Nat.lor v1181 v1186
    let v1188 := psel (pmask v1187) v1138 v1130
    let v1189 := Nat.land v1176 v1178
    let v1190 := Nat.lor v1175 v1189
    let v1191 := psel (pmask v1190) v1170 v1162
    let v1192 := Nat.land v1175 v1182
    let v1193 := Nat.lor v1181 v1192
    let v1194 := psel (pmask v1193) v1130 v1138
    let v1195 := Nat.land v1176 v1181
    let v1196 := Nat.lor v1175 v1195
    let v1197 := psel (pmask v1196) v1162 v1170
    let v1198 := smx 29 1 v1191 v1188
    let v1199 := srdF 1 v1198
    let v1200 := smx 29 1 v1197 v1194
    let v1201 := srdC 1 v1200
    let v1202 := plt 1 v61 v1199
    let v1203 := Nat.sub 1 v1202
    let v1204 := plt 1 v1105 v61
    let v1205 := psel (pmask v1204) v1199 v1201
    let v1208 := plt 1 v1205 v1105
    let v1209 := Nat.land v1202 v1208
    let v1210 := Nat.sub (Nat.add v61 OFFr) v1205
    let v1211 := plt 1 v1210 v1105
    let v1212 := Nat.sub 1 v1211
    let v1213 := Nat.lor v1203 v1212
    let v1214 := psel (pmask v1213) v95 v1105
    let v1215 := psel (pmask v1213) v33 v1205
    let v1216 := Nat.lor v1045 v1209
    let v1218 := hxa 1 H2 0
    let v1219 := plt 1 v61 v1218
    let v1220 := Nat.sub 1 v1219
    let t1218 := sc28u 1 v1218
    let v1222 := Nat.sub (Nat.add v28 t1218.2) OFFr
    let v1223 := plt 1 v1222 v95
    let v1224 := psel (pmask v1223) v95 v1222
    let v1225 := sshl 1 v1049
    let v1226 := smx 29 1 v1224 v1050
    let v1227 := plt 1 v1226 v1225
    let v1228 := Nat.sub 1 v1227
    let v1229 := plt 1 v15 v1218
    let v1230 := Nat.sub 1 v1229
    let v1231 := Nat.land v1228 v1230
    let v1232 := Nat.lor v1220 v1231
    let v1233 := psel (pmask v1232) v1218 v61
    let v1234 := hxa 1 H2 32
    let v1235 := plt 1 v1234 v9
    let v1236 := Nat.sub 1 v1235
    let t1234 := sc28u 1 v1234
    let v1238 := Nat.sub (Nat.add v31 t1234.2) OFFr
    let v1239 := plt 1 v1238 v33
    let v1240 := psel (pmask v1239) v1238 v33
    let v1241 := sshl 1 v1214
    let v1242 := smx 29 1 v1240 v1215
    let v1243 := plt 1 v1241 v1242
    let v1244 := Nat.sub 1 v1243
    let v1245 := Nat.lor v1236 v1244
    ∀ (P : Prop), (((v712 = 1 ↔ ¬v711 = 1)) → ((v713 = 1 ↔ v702 = 1 ∨ v712 = 1)) → ((v714 = 1 ↔ v637 = 1 ∧ v710 = 1)) → ((v715 = 1 ↔ ¬v637 = 1)) → ((v716 = 1 ↔ v713 = 1 ∧ v715 = 1)) → ((v717 = 1 ↔ v714 = 1 ∨ v716 = 1)) → (sv v718 = sv v61 - sv v682) → (v719 = if v637 = 1 then v718 else v682) → (v720 = if v717 = 1 then v719 else v203) → (R 1 0 4611686017353646081 4611686019501129727 v722 v722) → (v722 = if v634 = 1 then v203 else v720) → (sv v723 = sv v7 / 2) → (sv v724 = (sv v7 + 1) / 2) → (v725 = if v13 = 1 then v724 else v203) → ((v726 = 1 ↔ sv v19 < sv v723)) → ((v727 = 1 ↔ sv v9 < sv v725)) → ((v728 = 1 ↔ ¬v727 = 1)) → (R 1 0 0 1 v729 v729) → ((v729 = 1 ↔ v726 = 1 ∧ v728 = 1)) → (sv t723.1 = (sc28pS (scArg v723)).1) → (sv t725.1 = (sc28pS (scArg v725)).1) → ((v732 = 1 ↔ sv t723.1 < sv t725.1)) → (v733 = if v732 = 1 then t723.1 else t725.1) → (sv v734 = sv v28 + sv v733) → (v735 = if v732 = 1 then t725.1 else t723.1) → (sv v736 = sv v31 + sv v735) → ((v737 = 1 ↔ sv v736 < sv v33)) → (v738 = if v737 = 1 then v736 else v33) → ((v739 = 1 ↔ sv v723 < sv v36)) → ((v740 = 1 ↔ sv v38 < sv v725)) → ((v741 = 1 ↔ v739 = 1 ∧ v740 = 1)) → (v742 = if v741 = 1 then v33 else v738) → ((v743 = 1 ↔ sv v734 < sv v61)) → ((v744 = 1 ↔ ¬v743 = 1)) → ((v745 = 1 ↔ sv v61 < sv v742)) → ((v746 = 1 ↔ ¬v745 = 1)) → ((v747 = 1 ↔ v743 = 1 ∧ v746 = 1)) → ((v748 = 1 ↔ v743 = 1 ∧ v745 = 1)) → ((v749 = 1 ↔ v67 = 1 ∧ v748 = 1)) → (R 1 0 0 1 v750 v750) → ((v750 = 1 ↔ ¬v749 = 1)) → ((v751 = 1 ↔ v63 = 1 ∧ v748 = 1)) → ((v752 = 1 ↔ v747 = 1 ∨ v751 = 1)) → (v753 = if v752 = 1 then v41 else v29) → ((v754 = 1 ↔ v67 = 1 ∧ v744 = 1)) → ((v755 = 1 ↔ v66 = 1 ∨ v754 = 1)) → (v756 = if v755 = 1 then v742 else v734) → ((v757 = 1 ↔ v66 = 1 ∧ v748 = 1)) → ((v758 = 1 ↔ v747 = 1 ∨ v757 = 1)) → (v759 = if v758 = 1 then v29 else v41) → ((v760 = 1 ↔ v67 = 1 ∧ v747 = 1)) → ((v761 = 1 ↔ v66 = 1 ∨ v760 = 1)) → (v762 = if v761 = 1 then v734 else v742) → (sv v763 = sv v756 * sv v753) → (R 1 0 4611686018427387899 4611686018695823374 v764 v764) → (sv v764 = sv v763 / 2 ^ 28) → (sv v765 = sv v762 * sv v759) → (R 1 0 4611686018427387900 4611686018695823375 v766 v766) → (sv v766 = -((-sv v765) / 2 ^ 28)) → (R 1 0 0 1 v767 v767) → ((v767 = 1 ↔ sv v19 < sv v764)) → ((v768 = 1 ↔ sv v61 < sv v438)) → ((v769 = 1 ↔ sv v440 < sv v33)) → ((v770 = 1 ↔ v768 = 1 ∧ v769 = 1)) → ((v771 = 1 ↔ sv v61 < sv v89)) → ((v772 = 1 ↔ sv v91 < sv v33)) → ((v773 = 1 ↔ v771 = 1 ∧ v772 = 1)) → ((v774 = 1 ↔ sv v61 < sv v764)) → ((v775 = 1 ↔ sv v766 < sv v33)) → (R 1 0 0 1 v776 v776) → ((v776 = 1 ↔ v774 = 1 ∧ v775 = 1)) → ((v777 = 1 ↔ v770 = 1 ∧ v773 = 1)) → (R 1 0 0 1 v778 v778) → ((v778 = 1 ↔ v776 = 1 ∧ v777 = 1)) → (sv v779 = sv v440 * sv v440) → (sv v780 = -((-sv v779) / 2 ^ 28)) → (sv v781 = sv v780 + sv v780) → (sv v782 = sv v33 - sv v781) → ((v783 = 1 ↔ sv v782 < sv v95)) → (R 1 0 4611686018158952386 4611686018695823360 v784 v784) → (v784 = if v783 = 1 then v95 else v782) → (sv v785 = sv v438 * sv v438) → (sv v786 = sv v785 / 2 ^ 28) → (sv v787 = sv v786 + sv v786) → (R 1 0 4611686018158952392 4611686018695823360 v788 v788) → (sv v788 = sv v33 - sv v787) → (sv v789 = sv v766 * sv v766) → (sv v790 = -((-sv v789) / 2 ^ 28)) → (sv v791 = sv v790 + sv v790) → (sv v792 = sv v33 - sv v791) → ((v793 = 1 ↔ sv v792 < sv v95)) → (R 1 0 4611686018158952386 4611686018695823360 v794 v794) → (v794 = if v793 = 1 then v95 else v792) → (sv v795 = sv v764 * sv v764) → (sv v796 = sv v795 / 2 ^ 28) → (sv v797 = sv v796 + sv v796) → (R 1 0 4611686018158952392 4611686018695823360 v798 v798) → (sv v798 = sv v33 - sv v797) → (sv v799 = sv v91 * sv v91) → (sv v800 = -((-sv v799) / 2 ^ 28)) → (sv v801 = sv v800 + sv v800) → (sv v802 = sv v33 - sv v801) → ((v803 = 1 ↔ sv v802 < sv v95)) → (R 1 0 4611686018158952386 4611686018695823360 v804 v804) → (v804 = if v803 = 1 then v95 else v802) → (sv v805 = sv v89 * sv v89) → (sv v806 = sv v805 / 2 ^ 28) → (sv v807 = sv v806 + sv v806) → (R 1 0 4611686018158952392 4611686018695823360 v808 v808) → (sv v808 = sv v33 - sv v807) → ((v809 = 1 ↔ sv v784 < sv v61)) → ((v810 = 1 ↔ ¬v809 = 1)) → ((v811 = 1 ↔ sv v61 < sv v788)) → ((v812 = 1 ↔ ¬v811 = 1)) → ((v813 = 1 ↔ v809 = 1 ∧ v812 = 1)) → ((v814 = 1 ↔ v809 = 1 ∧ v811 = 1)) → ((v815 = 1 ↔ sv v804 < sv v61)) → (R 1 0 0 1 v816 v816) → ((v816 = 1 ↔ ¬v815 = 1)) → ((v817 = 1 ↔ sv v61 < sv v808)) → ((v818 = 1 ↔ ¬v817 = 1)) → (R 1 0 0 1 v819 v819) → ((v819 = 1 ↔ v815 = 1 ∧ v818 = 1)) → (R 1 0 0 1 v820 v820) → ((v820 = 1 ↔ v815 = 1 ∧ v817 = 1)) → ((v821 = 1 ↔ v814 = 1 ∧ v820 = 1)) → ((v822 = 1 ↔ ¬v821 = 1)) → (R 1 0 0 1 v823 v823) → ((v823 = 1 ↔ ¬v778 = 1)) → (R 1 0 0 1 v824 v824) → ((v824 = 1 ↔ v822 = 1 ∨ v823 = 1)) → ((v825 = 1 ↔ v810 = 1 ∧ v820 = 1)) → ((v826 = 1 ↔ v819 = 1 ∨ v825 = 1)) → (v827 = if v826 = 1 then v788 else v784) → ((v828 = 1 ↔ v814 = 1 ∧ v816 = 1)) → ((v829 = 1 ↔ v813 = 1 ∨ v828 = 1)) → (v830 = if v829 = 1 then v808 else v804) → ((v831 = 1 ↔ v813 = 1 ∧ v820 = 1)) → ((v832 = 1 ↔ v819 = 1 ∨ v831 = 1)) → (v833 = if v832 = 1 then v784 else v788) → ((v834 = 1 ↔ v814 = 1 ∧ v819 = 1)) → ((v835 = 1 ↔ v813 = 1 ∨ v834 = 1)) → (v836 = if v835 = 1 then v804 else v808) → (sv v837 = sv v830 * sv v827) → (sv v838 = sv v837 / 2 ^ 28) → (sv v839 = sv v836 * sv v833) → (sv v840 = -((-sv v839) / 2 ^ 28)) → (sv v841 = sv v794 - sv v840) → (sv v842 = sv v798 - sv v838) → ((v843 = 1 ↔ sv v794 < sv v61)) → (R 1 0 0 1 v844 v844) → ((v844 = 1 ↔ ¬v843 = 1)) → ((v845 = 1 ↔ sv v61 < sv v798)) → ((v846 = 1 ↔ ¬v845 = 1)) → (R 1 0 0 1 v847 v847) → ((v847 = 1 ↔ v843 = 1 ∧ v846 = 1)) → (R 1 0 0 1 v848 v848) → ((v848 = 1 ↔ v843 = 1 ∧ v845 = 1)) → ((v849 = 1 ↔ v814 = 1 ∧ v848 = 1)) → ((v850 = 1 ↔ ¬v849 = 1)) → (R 1 0 0 1 v851 v851) → ((v851 = 1 ↔ v823 = 1 ∨ v850 = 1)) → ((v852 = 1 ↔ v810 = 1 ∧ v848 = 1)) → ((v853 = 1 ↔ v847 = 1 ∨ v852 = 1)) → (v854 = if v853 = 1 then v788 else v784) → ((v855 = 1 ↔ v814 = 1 ∧ v844 = 1)) → ((v856 = 1 ↔ v813 = 1 ∨ v855 = 1)) → (v857 = if v856 = 1 then v798 else v794) → ((v858 = 1 ↔ v813 = 1 ∧ v848 = 1)) → ((v859 = 1 ↔ v847 = 1 ∨ v858 = 1)) → (v860 = if v859 = 1 then v784 else v788) → ((v861 = 1 ↔ v814 = 1 ∧ v847 = 1)) → ((v862 = 1 ↔ v813 = 1 ∨ v861 = 1)) → (v863 = if v862 = 1 then v794 else v798) → (sv v864 = sv v857 * sv v854) → (sv v865 = sv v864 / 2 ^ 28) → (sv v866 = sv v863 * sv v860) → (sv v867 = -((-sv v866) / 2 ^ 28)) → (sv v868 = sv v804 - sv v867) → (sv v869 = sv v808 - sv v865) → (R 1 0 0 1 v870 v870) → ((v870 = 1 ↔ sv v61 < sv v841)) → (R 1 0 0 1 v871 v871) → ((v871 = 1 ↔ sv v842 < sv v61)) → ((v872 = 1 ↔ sv v61 < sv v868)) → ((v873 = 1 ↔ sv v869 < sv v61)) → (v874 = if v870 = 1 then v91 else v89) → (v875 = if v871 = 1 then v89 else v91) → (v876 = if v871 = 1 then v91 else v89) → (v877 = if v870 = 1 then v89 else v91) → (v878 = if v872 = 1 then v766 else v764) → (v879 = if v873 = 1 then v764 else v766) → (v880 = if v873 = 1 then v766 else v764) → (v881 = if v872 = 1 then v764 else v766) → (sv v887 = sv v875 * sv v875) → (sv v888 = -((-sv v887) / 2 ^ 28)) → (sv v889 = sv v888 + sv v888) → (sv v890 = sv v33 - sv v889) → ((v891 = 1 ↔ sv v890 < sv v95)) → (v892 = if v891 = 1 then v95 else v890) → (sv v893 = sv v874 * sv v874) → (sv v894 = sv v893 / 2 ^ 28) → (sv v895 = sv v894 + sv v894) → (sv v896 = sv v33 - sv v895) → (sv v897 = sv v879 * sv v879) → (sv v898 = -((-sv v897) / 2 ^ 28)) → (sv v899 = sv v898 + sv v898) → (sv v900 = sv v33 - sv v899) → ((v901 = 1 ↔ sv v900 < sv v95)) → (v902 = if v901 = 1 then v95 else v900) → (sv v903 = sv v878 * sv v878) → (sv v904 = sv v903 / 2 ^ 28) → (sv v905 = sv v904 + sv v904) → (sv v906 = sv v33 - sv v905) → ((v907 = 1 ↔ sv v892 < sv v61)) → ((v908 = 1 ↔ ¬v907 = 1)) → ((v909 = 1 ↔ sv v61 < sv v896)) → ((v910 = 1 ↔ ¬v909 = 1)) → ((v911 = 1 ↔ v907 = 1 ∧ v910 = 1)) → ((v912 = 1 ↔ v907 = 1 ∧ v909 = 1)) → ((v913 = 1 ↔ sv v902 < sv v61)) → ((v914 = 1 ↔ ¬v913 = 1)) → ((v915 = 1 ↔ sv v61 < sv v906)) → ((v916 = 1 ↔ ¬v915 = 1)) → ((v917 = 1 ↔ v913 = 1 ∧ v916 = 1)) → ((v918 = 1 ↔ v913 = 1 ∧ v915 = 1)) → ((v919 = 1 ↔ v912 = 1 ∧ v918 = 1)) → ((v920 = 1 ↔ ¬v919 = 1)) → (R 1 0 0 1 v921 v921) → ((v921 = 1 ↔ v823 = 1 ∨ v920 = 1)) → ((v922 = 1 ↔ v908 = 1 ∧ v918 = 1)) → ((v923 = 1 ↔ v917 = 1 ∨ v922 = 1)) → (v924 = if v923 = 1 then v896 else v892) → ((v925 = 1 ↔ v912 = 1 ∧ v914 = 1)) → ((v926 = 1 ↔ v911 = 1 ∨ v925 = 1)) → (v927 = if v926 = 1 then v906 else v902) → (sv v934 = sv v927 * sv v924) → (sv v935 = sv v934 / 2 ^ 28) → (sv v939 = sv v788 - sv v935) → (sv v940 = (72057594037927936)) → (sv v941 = sv v940 - sv v893) → (sv v942 = ((Nat.sqrt (v941 - 4611686018427387904) : ℕ) : ℤ)) → (sv v943 = sv v105 + sv v942) → (sv v944 = sv v942 * sv v874) → (sv v945 = sv v944 / 2 ^ 28) → (sv v946 = sv v945 + sv v945) → (sv v947 = sv v943 * sv v874) → (sv v948 = -((-sv v947) / 2 ^ 28)) → (sv v949 = sv v948 + sv v948) → ((v950 = 1 ↔ sv v949 < sv v33)) → (v951 = if v950 = 1 then v949 else v33) → (sv v952 = sv v940 - sv v887) → (sv v953 = ((Nat.sqrt (v952 - 4611686018427387904) : ℕ) : ℤ)) → (sv v954 = sv v105 + sv v953) → (sv v955 = sv v953 * sv v875) → (sv v956 = sv v955 / 2 ^ 28) → (sv v957 = sv v956 + sv v956) → (sv v958 = sv v954 * sv v875) → (sv v959 = -((-sv v958) / 2 ^ 28)) → (sv v960 = sv v959 + sv v959) → ((v961 = 1 ↔ sv v960 < sv v33)) → (v962 = if v961 = 1 then v960 else v33) → ((v963 = 1 ↔ sv v946 < sv v957)) → (v964 = if v963 = 1 then v946 else v957) → ((v965 = 1 ↔ sv v951 < sv v962)) → (v966 = if v965 = 1 then v962 else v951) → (sv v967 = (36028797018963968)) → ((v968 = 1 ↔ sv v967 < sv v893)) → ((v969 = 1 ↔ ¬v968 = 1)) → ((v970 = 1 ↔ sv v887 < sv v967)) → ((v971 = 1 ↔ ¬v970 = 1)) → ((v972 = 1 ↔ v969 = 1 ∧ v971 = 1)) → (v973 = if v972 = 1 then v33 else v966) → (sv v974 = sv v940 - sv v903) → (sv v975 = ((Nat.sqrt (v974 - 4611686018427387904) : ℕ) : ℤ)) → (sv v976 = sv v105 + sv v975) → (sv v977 = sv v975 * sv v878) → (sv v978 = sv v977 / 2 ^ 28) → (sv v979 = sv v978 + sv v978) → (sv v980 = sv v976 * sv v878) → (sv v981 = -((-sv v980) / 2 ^ 28)) → (sv v982 = sv v981 + sv v981) → ((v983 = 1 ↔ sv v982 < sv v33)) → (v984 = if v983 = 1 then v982 else v33) → (sv v985 = sv v940 - sv v897) → (sv v986 = ((Nat.sqrt (v985 - 4611686018427387904) : ℕ) : ℤ)) → (sv v987 = sv v105 + sv v986) → (sv v988 = sv v986 * sv v879) → (sv v989 = sv v988 / 2 ^ 28) → (sv v990 = sv v989 + sv v989) → (sv v991 = sv v987 * sv v879) → (sv v992 = -((-sv v991) / 2 ^ 28)) → (sv v993 = sv v992 + sv v992) → ((v994 = 1 ↔ sv v993 < sv v33)) → (v995 = if v994 = 1 then v993 else v33) → ((v996 = 1 ↔ sv v979 < sv v990)) → (v997 = if v996 = 1 then v979 else v990) → ((v998 = 1 ↔ sv v984 < sv v995)) → (v999 = if v998 = 1 then v995 else v984) → ((v1000 = 1 ↔ sv v967 < sv v903)) → ((v1001 = 1 ↔ ¬v1000 = 1)) → ((v1002 = 1 ↔ sv v897 < sv v967)) → ((v1003 = 1 ↔ ¬v1002 = 1)) → ((v1004 = 1 ↔ v1001 = 1 ∧ v1003 = 1)) → (v1005 = if v1004 = 1 then v33 else v999) → ((v1006 = 1 ↔ sv v964 < sv v61)) → ((v1007 = 1 ↔ ¬v1006 = 1)) → ((v1008 = 1 ↔ sv v61 < sv v973)) → ((v1009 = 1 ↔ ¬v1008 = 1)) → ((v1010 = 1 ↔ v1006 = 1 ∧ v1009 = 1)) → ((v1011 = 1 ↔ v1006 = 1 ∧ v1008 = 1)) → ((v1012 = 1 ↔ sv v997 < sv v61)) → ((v1013 = 1 ↔ ¬v1012 = 1)) → ((v1014 = 1 ↔ sv v61 < sv v1005)) → ((v1015 = 1 ↔ ¬v1014 = 1)) → ((v1016 = 1 ↔ v1012 = 1 ∧ v1015 = 1)) → ((v1017 = 1 ↔ v1012 = 1 ∧ v1014 = 1)) → ((v1018 = 1 ↔ v1011 = 1 ∧ v1017 = 1)) → ((v1019 = 1 ↔ ¬v1018 = 1)) → (R 1 0 0 1 v1020 v1020) → ((v1020 = 1 ↔ v823 = 1 ∨ v1019 = 1)) → ((v1021 = 1 ↔ v1007 = 1 ∧ v1017 = 1)) → ((v1022 = 1 ↔ v1016 = 1 ∨ v1021 = 1)) → (v1023 = if v1022 = 1 then v973 else v964) → ((v1024 = 1 ↔ v1011 = 1 ∧ v1013 = 1)) → ((v1025 = 1 ↔ v1010 = 1 ∨ v1024 = 1)) → (v1026 = if v1025 = 1 then v1005 else v997) → ((v1027 = 1 ↔ v1010 = 1 ∧ v1017 = 1)) → ((v1028 = 1 ↔ v1016 = 1 ∨ v1027 = 1)) → (v1029 = if v1028 = 1 then v964 else v973) → ((v1030 = 1 ↔ v1011 = 1 ∧ v1016 = 1)) → ((v1031 = 1 ↔ v1010 = 1 ∨ v1030 = 1)) → (v1032 = if v1031 = 1 then v997 else v1005) → (sv v1033 = sv v1026 * sv v1023) → (sv v1034 = sv v1033 / 2 ^ 28) → (sv v1035 = sv v1032 * sv v1029) → (sv v1036 = -((-sv v1035) / 2 ^ 28)) → ((v1037 = 1 ↔ sv v61 < sv v1034)) → ((v1038 = 1 ↔ ¬v1037 = 1)) → ((v1041 = 1 ↔ sv v939 < sv v61)) → (v1042 = if v1041 = 1 then v1036 else v1034) → (sv v1043 = sv v61 - sv v1042) → ((v1044 = 1 ↔ sv v939 < sv v1043)) → ((v1045 = 1 ↔ v1037 = 1 ∧ v1044 = 1)) → ((v1046 = 1 ↔ sv v939 < sv v1042)) → ((v1047 = 1 ↔ ¬v1046 = 1)) → ((v1048 = 1 ↔ v1038 = 1 ∨ v1047 = 1)) → (v1049 = if v1048 = 1 then v33 else v939) → (v1050 = if v1048 = 1 then v33 else v1042) → (sv v1054 = sv v877 * sv v877) → (sv v1055 = -((-sv v1054) / 2 ^ 28)) → (sv v1056 = sv v1055 + sv v1055) → (sv v1057 = sv v33 - sv v1056) → ((v1058 = 1 ↔ sv v1057 < sv v95)) → (v1059 = if v1058 = 1 then v95 else v1057) → (sv v1060 = sv v876 * sv v876) → (sv v1061 = sv v1060 / 2 ^ 28) → (sv v1062 = sv v1061 + sv v1061) → (sv v1063 = sv v33 - sv v1062) → (sv v1064 = sv v881 * sv v881) → (sv v1065 = -((-sv v1064) / 2 ^ 28)) → (sv v1066 = sv v1065 + sv v1065) → (sv v1067 = sv v33 - sv v1066) → ((v1068 = 1 ↔ sv v1067 < sv v95)) → (v1069 = if v1068 = 1 then v95 else v1067) → (sv v1070 = sv v880 * sv v880) → (sv v1071 = sv v1070 / 2 ^ 28) → (sv v1072 = sv v1071 + sv v1071) → (sv v1073 = sv v33 - sv v1072) → ((v1074 = 1 ↔ sv v1059 < sv v61)) → ((v1076 = 1 ↔ sv v61 < sv v1063)) → ((v1077 = 1 ↔ ¬v1076 = 1)) → ((v1078 = 1 ↔ v1074 = 1 ∧ v1077 = 1)) → ((v1079 = 1 ↔ v1074 = 1 ∧ v1076 = 1)) → ((v1080 = 1 ↔ sv v1069 < sv v61)) → ((v1082 = 1 ↔ sv v61 < sv v1073)) → ((v1083 = 1 ↔ ¬v1082 = 1)) → ((v1084 = 1 ↔ v1080 = 1 ∧ v1083 = 1)) → ((v1085 = 1 ↔ v1080 = 1 ∧ v1082 = 1)) → ((v1086 = 1 ↔ v1079 = 1 ∧ v1085 = 1)) → ((v1087 = 1 ↔ ¬v1086 = 1)) → (R 1 0 0 1 v1088 v1088) → ((v1088 = 1 ↔ v823 = 1 ∨ v1087 = 1)) → ((v1095 = 1 ↔ v1078 = 1 ∧ v1085 = 1)) → ((v1096 = 1 ↔ v1084 = 1 ∨ v1095 = 1)) → (v1097 = if v1096 = 1 then v1059 else v1063) → ((v1098 = 1 ↔ v1079 = 1 ∧ v1084 = 1)) → ((v1099 = 1 ↔ v1078 = 1 ∨ v1098 = 1)) → (v1100 = if v1099 = 1 then v1069 else v1073) → (sv v1103 = sv v1100 * sv v1097) → (sv v1104 = -((-sv v1103) / 2 ^ 28)) → (sv v1105 = sv v784 - sv v1104) → (sv v1107 = sv v940 - sv v1060) → (sv v1108 = ((Nat.sqrt (v1107 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1109 = sv v105 + sv v1108) → (sv v1110 = sv v1108 * sv v876) → (sv v1111 = sv v1110 / 2 ^ 28) → (sv v1112 = sv v1111 + sv v1111) → (sv v1113 = sv v1109 * sv v876) → (sv v1114 = -((-sv v1113) / 2 ^ 28)) → (sv v1115 = sv v1114 + sv v1114) → ((v1116 = 1 ↔ sv v1115 < sv v33)) → (v1117 = if v1116 = 1 then v1115 else v33) → (sv v1118 = sv v940 - sv v1054) → (sv v1119 = ((Nat.sqrt (v1118 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1120 = sv v105 + sv v1119) → (sv v1121 = sv v1119 * sv v877) → (sv v1122 = sv v1121 / 2 ^ 28) → (sv v1123 = sv v1122 + sv v1122) → (sv v1124 = sv v1120 * sv v877) → (sv v1125 = -((-sv v1124) / 2 ^ 28)) → (sv v1126 = sv v1125 + sv v1125) → ((v1127 = 1 ↔ sv v1126 < sv v33)) → (v1128 = if v1127 = 1 then v1126 else v33) → ((v1129 = 1 ↔ sv v1112 < sv v1123)) → (v1130 = if v1129 = 1 then v1112 else v1123) → ((v1131 = 1 ↔ sv v1117 < sv v1128)) → (v1132 = if v1131 = 1 then v1128 else v1117) → ((v1133 = 1 ↔ sv v967 < sv v1060)) → ((v1134 = 1 ↔ ¬v1133 = 1)) → ((v1135 = 1 ↔ sv v1054 < sv v967)) → ((v1136 = 1 ↔ ¬v1135 = 1)) → ((v1137 = 1 ↔ v1134 = 1 ∧ v1136 = 1)) → (v1138 = if v1137 = 1 then v33 else v1132) → (sv v1139 = sv v940 - sv v1070) → (sv v1140 = ((Nat.sqrt (v1139 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1141 = sv v105 + sv v1140) → (sv v1142 = sv v1140 * sv v880) → (sv v1143 = sv v1142 / 2 ^ 28) → (sv v1144 = sv v1143 + sv v1143) → (sv v1145 = sv v1141 * sv v880) → (sv v1146 = -((-sv v1145) / 2 ^ 28)) → (sv v1147 = sv v1146 + sv v1146) → ((v1148 = 1 ↔ sv v1147 < sv v33)) → (v1149 = if v1148 = 1 then v1147 else v33) → (sv v1150 = sv v940 - sv v1064) → (sv v1151 = ((Nat.sqrt (v1150 - 4611686018427387904) : ℕ) : ℤ)) → (sv v1152 = sv v105 + sv v1151) → (sv v1153 = sv v1151 * sv v881) → (sv v1154 = sv v1153 / 2 ^ 28) → (sv v1155 = sv v1154 + sv v1154) → (sv v1156 = sv v1152 * sv v881) → (sv v1157 = -((-sv v1156) / 2 ^ 28)) → (sv v1158 = sv v1157 + sv v1157) → ((v1159 = 1 ↔ sv v1158 < sv v33)) → (v1160 = if v1159 = 1 then v1158 else v33) → ((v1161 = 1 ↔ sv v1144 < sv v1155)) → (v1162 = if v1161 = 1 then v1144 else v1155) → ((v1163 = 1 ↔ sv v1149 < sv v1160)) → (v1164 = if v1163 = 1 then v1160 else v1149) → ((v1165 = 1 ↔ sv v967 < sv v1070)) → ((v1166 = 1 ↔ ¬v1165 = 1)) → ((v1167 = 1 ↔ sv v1064 < sv v967)) → ((v1168 = 1 ↔ ¬v1167 = 1)) → ((v1169 = 1 ↔ v1166 = 1 ∧ v1168 = 1)) → (v1170 = if v1169 = 1 then v33 else v1164) → ((v1171 = 1 ↔ sv v1130 < sv v61)) → ((v1172 = 1 ↔ ¬v1171 = 1)) → ((v1173 = 1 ↔ sv v61 < sv v1138)) → ((v1174 = 1 ↔ ¬v1173 = 1)) → ((v1175 = 1 ↔ v1171 = 1 ∧ v1174 = 1)) → ((v1176 = 1 ↔ v1171 = 1 ∧ v1173 = 1)) → ((v1177 = 1 ↔ sv v1162 < sv v61)) → ((v1178 = 1 ↔ ¬v1177 = 1)) → ((v1179 = 1 ↔ sv v61 < sv v1170)) → ((v1180 = 1 ↔ ¬v1179 = 1)) → ((v1181 = 1 ↔ v1177 = 1 ∧ v1180 = 1)) → ((v1182 = 1 ↔ v1177 = 1 ∧ v1179 = 1)) → ((v1183 = 1 ↔ v1176 = 1 ∧ v1182 = 1)) → ((v1184 = 1 ↔ ¬v1183 = 1)) → (R 1 0 0 1 v1185 v1185) → ((v1185 = 1 ↔ v823 = 1 ∨ v1184 = 1)) → ((v1186 = 1 ↔ v1172 = 1 ∧ v1182 = 1)) → ((v1187 = 1 ↔ v1181 = 1 ∨ v1186 = 1)) → (v1188 = if v1187 = 1 then v1138 else v1130) → ((v1189 = 1 ↔ v1176 = 1 ∧ v1178 = 1)) → ((v1190 = 1 ↔ v1175 = 1 ∨ v1189 = 1)) → (v1191 = if v1190 = 1 then v1170 else v1162) → ((v1192 = 1 ↔ v1175 = 1 ∧ v1182 = 1)) → ((v1193 = 1 ↔ v1181 = 1 ∨ v1192 = 1)) → (v1194 = if v1193 = 1 then v1130 else v1138) → ((v1195 = 1 ↔ v1176 = 1 ∧ v1181 = 1)) → ((v1196 = 1 ↔ v1175 = 1 ∨ v1195 = 1)) → (v1197 = if v1196 = 1 then v1162 else v1170) → (sv v1198 = sv v1191 * sv v1188) → (sv v1199 = sv v1198 / 2 ^ 28) → (sv v1200 = sv v1197 * sv v1194) → (sv v1201 = -((-sv v1200) / 2 ^ 28)) → ((v1202 = 1 ↔ sv v61 < sv v1199)) → ((v1203 = 1 ↔ ¬v1202 = 1)) → ((v1204 = 1 ↔ sv v1105 < sv v61)) → (v1205 = if v1204 = 1 then v1199 else v1201) → ((v1208 = 1 ↔ sv v1205 < sv v1105)) → ((v1209 = 1 ↔ v1202 = 1 ∧ v1208 = 1)) → (sv v1210 = sv v61 - sv v1205) → ((v1211 = 1 ↔ sv v1210 < sv v1105)) → ((v1212 = 1 ↔ ¬v1211 = 1)) → ((v1213 = 1 ↔ v1203 = 1 ∨ v1212 = 1)) → (v1214 = if v1213 = 1 then v95 else v1105) → (v1215 = if v1213 = 1 then v33 else v1205) → (R 1 0 0 1 v1216 v1216) → ((v1216 = 1 ↔ v1045 = 1 ∨ v1209 = 1)) → (sv v1218 = ((H2 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ)) → ((v1219 = 1 ↔ sv v61 < sv v1218)) → ((v1220 = 1 ↔ ¬v1219 = 1)) → (R 1 0 4611686018427387904 4611686018695823363 t1218.1 t1218.1) → (R 1 0 4611686018158952445 4611686018695823363 t1218.2 t1218.2) → (sv t1218.1 = (sc28pS (scArg v1218)).1) → (sv t1218.2 = (sc28pS (scArg v1218)).2) → (sv v1222 = sv v28 + sv t1218.2) → ((v1223 = 1 ↔ sv v1222 < sv v95)) → (v1224 = if v1223 = 1 then v95 else v1222) → (sv v1225 = sv v1049 * 2 ^ 28) → (sv v1226 = sv v1224 * sv v1050) → ((v1227 = 1 ↔ sv v1226 < sv v1225)) → ((v1228 = 1 ↔ ¬v1227 = 1)) → ((v1229 = 1 ↔ sv v15 < sv v1218)) → ((v1230 = 1 ↔ ¬v1229 = 1)) → ((v1231 = 1 ↔ v1228 = 1 ∧ v1230 = 1)) → (R 1 0 0 1 v1232 v1232) → ((v1232 = 1 ↔ v1220 = 1 ∨ v1231 = 1)) → (R 1 0 4611686018427387904 4611686019501129727 v1233 v1233) → (v1233 = if v1232 = 1 then v1218 else v61) → (sv v1234 = ((H2 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ)) → ((v1235 = 1 ↔ sv v1234 < sv v9)) → ((v1236 = 1 ↔ ¬v1235 = 1)) → (R 1 0 4611686018427387904 4611686018695823363 t1234.1 t1234.1) → (R 1 0 4611686018158952445 4611686018695823363 t1234.2 t1234.2) → (sv t1234.1 = (sc28pS (scArg v1234)).1) → (sv t1234.2 = (sc28pS (scArg v1234)).2) → (sv v1238 = sv v31 + sv t1234.2) → ((v1239 = 1 ↔ sv v1238 < sv v33)) → (v1240 = if v1239 = 1 then v1238 else v33) → (sv v1241 = sv v1214 * 2 ^ 28) → (sv v1242 = sv v1240 * sv v1215) → ((v1243 = 1 ↔ sv v1241 < sv v1242)) → ((v1244 = 1 ↔ ¬v1243 = 1)) → (R 1 0 0 1 v1245 v1245) → ((v1245 = 1 ↔ v1236 = 1 ∨ v1244 = 1)) → P) → P := by
  intro OFFr H61r v7 v9 v15 v19 v28 v31 v33 v36 v38 v61 v95 v105 v203 v682 v712 v713 v714 v715 v716 v717 v718 v719 v720 v722 v723 v724 v725 v726 v727 v728 v729 t723 t725 v732 v733 v734 v735 v736 v737 v738 v739 v740 v741 v742 v743 v744 v745 v746 v747 v748 v749 v750 v751 v752 v753 v754 v755 v756 v757 v758 v759 v760 v761 v762 v763 v764 v765 v766 v767 v768 v769 v770 v771 v772 v773 v774 v775 v776 v777 v778 v779 v780 v781 v782 v783 v784 v785 v786 v787 v788 v789 v790 v791 v792 v793 v794 v795 v796 v797 v798 v799 v800 v801 v802 v803 v804 v805 v806 v807 v808 v809 v810 v811 v812 v813 v814 v815 v816 v817 v818 v819 v820 v821 v822 v823 v824 v825 v826 v827 v828 v829 v830 v831 v832 v833 v834 v835 v836 v837 v838 v839 v840 v841 v842 v843 v844 v845 v846 v847 v848 v849 v850 v851 v852 v853 v854 v855 v856 v857 v858 v859 v860 v861 v862 v863 v864 v865 v866 v867 v868 v869 v870 v871 v872 v873 v874 v875 v876 v877 v878 v879 v880 v881 v887 v888 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 v918 v919 v920 v921 v922 v923 v924 v925 v926 v927 v934 v935 v939 v940 v941 v942 v943 v944 v945 v946 v947 v948 v949 v950 v951 v952 v953 v954 v955 v956 v957 v958 v959 v960 v961 v962 v963 v964 v965 v966 v967 v968 v969 v970 v971 v972 v973 v974 v975 v976 v977 v978 v979 v980 v981 v982 v983 v984 v985 v986 v987 v988 v989 v990 v991 v992 v993 v994 v995 v996 v997 v998 v999 v1000 v1001 v1002 v1003 v1004 v1005 v1006 v1007 v1008 v1009 v1010 v1011 v1012 v1013 v1014 v1015 v1016 v1017 v1018 v1019 v1020 v1021 v1022 v1023 v1024 v1025 v1026 v1027 v1028 v1029 v1030 v1031 v1032 v1033 v1034 v1035 v1036 v1037 v1038 v1041 v1042 v1043 v1044 v1045 v1046 v1047 v1048 v1049 v1050 v1054 v1055 v1056 v1057 v1058 v1059 v1060 v1061 v1062 v1063 v1064 v1065 v1066 v1067 v1068 v1069 v1070 v1071 v1072 v1073 v1074 v1076 v1077 v1078 v1079 v1080 v1082 v1083 v1084 v1085 v1086 v1087 v1088 v1095 v1096 v1097 v1098 v1099 v1100 v1103 v1104 v1105 v1107 v1108 v1109 v1110 v1111 v1112 v1113 v1114 v1115 v1116 v1117 v1118 v1119 v1120 v1121 v1122 v1123 v1124 v1125 v1126 v1127 v1128 v1129 v1130 v1131 v1132 v1133 v1134 v1135 v1136 v1137 v1138 v1139 v1140 v1141 v1142 v1143 v1144 v1145 v1146 v1147 v1148 v1149 v1150 v1151 v1152 v1153 v1154 v1155 v1156 v1157 v1158 v1159 v1160 v1161 v1162 v1163 v1164 v1165 v1166 v1167 v1168 v1169 v1170 v1171 v1172 v1173 v1174 v1175 v1176 v1177 v1178 v1179 v1180 v1181 v1182 v1183 v1184 v1185 v1186 v1187 v1188 v1189 v1190 v1191 v1192 v1193 v1194 v1195 v1196 v1197 v1198 v1199 v1200 v1201 v1202 v1203 v1204 v1205 v1208 v1209 v1210 v1211 v1212 v1213 v1214 v1215 v1216 v1218 v1219 v1220 t1218 v1222 v1223 v1224 v1225 v1226 v1227 v1228 v1229 v1230 v1231 v1232 v1233 v1234 v1235 v1236 t1234 v1238 v1239 v1240 v1241 v1242 v1243 v1244 v1245
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_H61r : R 1 0 2305843009213693952 2305843009213693952 H61r H61r := (r_c hl 2305843009213693952 (of_decide_eq_true rfl))
  have h_v7 : R 1 0 4611686018427387904 4611686087146864624 v7 v7 := (r1_ix hb_F3 32 (of_decide_eq_true rfl))
  have h_v9 : R 1 0 4611686019270702761 4611686019270702761 v9 v9 := (r_c hl 4611686019270702761 (of_decide_eq_true rfl))
  have h_v15 : R 1 0 4611686019270702760 4611686019270702760 v15 v15 := (r_c hl 4611686019270702760 (of_decide_eq_true rfl))
  have h_v19 : R 1 0 4611686018427387903 4611686018427387903 v19 v19 := (r_c hl 4611686018427387903 (of_decide_eq_true rfl))
  have h_v28 : R 1 0 4611686018427387900 4611686018427387900 v28 v28 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have h_v31 : R 1 0 4611686018427387908 4611686018427387908 v31 v31 := (r_c hl 4611686018427387908 (of_decide_eq_true rfl))
  have h_v33 : R 1 0 4611686018695823360 4611686018695823360 v33 v33 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have h_v36 : R 1 0 4611686018849045334 4611686018849045334 v36 v36 := (r_c hl 4611686018849045334 (of_decide_eq_true rfl))
  have h_v38 : R 1 0 4611686018849045331 4611686018849045331 v38 v38 := (r_c hl 4611686018849045331 (of_decide_eq_true rfl))
  have h_v61 : R 1 0 4611686018427387904 4611686018427387904 v61 v61 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v95 : R 1 0 4611686018158952448 4611686018158952448 v95 v95 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have h_v105 : R 1 0 4611686018427387905 4611686018427387905 v105 v105 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have h_v203 : R 1 0 4611686018849045333 4611686018849045333 v203 v203 := (r_c hl 4611686018849045333 (of_decide_eq_true rfl))
  have h_v682 : R 1 0 4611686018427387904 4611686019501129727 v682 v682 := (r1_hxa hb_H1 32 (of_decide_eq_true rfl))
  have h_v712 : R 1 0 0 1 v712 v712 := (r_sub hl (r_O hl) h_v711 (of_decide_eq_true rfl))
  have e_v712 : (v712 = 1 ↔ ¬v711 = 1) := e_not h_v711 (of_decide_eq_true rfl)
  have h_v713 : R 1 0 0 1 v713 v713 := (r_lor hl h_v702 h_v712 (of_decide_eq_true rfl))
  have e_v713 : (v713 = 1 ↔ v702 = 1 ∨ v712 = 1) := e_lor h_v702 h_v712 (of_decide_eq_true rfl)
  have h_v714 : R 1 0 0 1 v714 v714 := (r_land hl h_v637 h_v710 (of_decide_eq_true rfl))
  have e_v714 : (v714 = 1 ↔ v637 = 1 ∧ v710 = 1) := e_land h_v637 h_v710 (of_decide_eq_true rfl)
  have h_v715 : R 1 0 0 1 v715 v715 := (r_sub hl (r_O hl) h_v637 (of_decide_eq_true rfl))
  have e_v715 : (v715 = 1 ↔ ¬v637 = 1) := e_not h_v637 (of_decide_eq_true rfl)
  have h_v716 : R 1 0 0 1 v716 v716 := (r_land hl h_v713 h_v715 (of_decide_eq_true rfl))
  clear h_v712
  have e_v716 : (v716 = 1 ↔ v713 = 1 ∧ v715 = 1) := e_land h_v713 h_v715 (of_decide_eq_true rfl)
  have h_v717 : R 1 0 0 1 v717 v717 := (r_lor hl h_v714 h_v716 (of_decide_eq_true rfl))
  have e_v717 : (v717 = 1 ↔ v714 = 1 ∨ v716 = 1) := e_lor h_v714 h_v716 (of_decide_eq_true rfl)
  have h_v718 : R 1 0 4611686017353646081 4611686018427387904 v718 v718 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v682 (of_decide_eq_true rfl))
  have e_v718 : sv v718 = sv v61 - sv v682 := e_sub h_v61 h_v682 (of_decide_eq_true rfl)
  have h_v719 : R 1 0 4611686017353646081 4611686019501129727 v719 v719 := (r_psel hl h_v637 h_v718 h_v682 (of_decide_eq_true rfl))
  have e_v719 : v719 = if v637 = 1 then v718 else v682 := e_psel h_v637 h_v718 h_v682 (of_decide_eq_true rfl)
  have h_v720 : R 1 0 4611686017353646081 4611686019501129727 v720 v720 := (r_psel hl h_v717 h_v719 h_v203 (of_decide_eq_true rfl))
  have e_v720 : v720 = if v717 = 1 then v719 else v203 := e_psel h_v717 h_v719 h_v203 (of_decide_eq_true rfl)
  have h_v722 : R 1 0 4611686017353646081 4611686019501129727 v722 v722 := (r_psel hl h_v634 h_v203 h_v720 (of_decide_eq_true rfl))
  have e_v722 : v722 = if v634 = 1 then v203 else v720 := e_psel h_v634 h_v203 h_v720 (of_decide_eq_true rfl)
  have h_v723 : R 1 0 4611686018427387904 4611686052787126264 v723 v723 := (r_add hl (r_pshr1 hl h_v7) h_H61r (of_decide_eq_true rfl))
  have e_v723 : sv v723 = sv v7 / 2 := e_halfF h_v7
  have h_v724 : R 1 0 4611686018427387904 4611686052787126264 v724 v724 := (r_add hl (r_pshr1 hl (r_add hl h_v7 (r_O hl) (of_decide_eq_true rfl))) h_H61r (of_decide_eq_true rfl))
  have e_v724 : sv v724 = (sv v7 + 1) / 2 := e_halfC h_v7 (of_decide_eq_true rfl)
  have h_v725 : R 1 0 4611686018427387904 4611686052787126264 v725 v725 := (r_psel hl h_v13 h_v724 h_v203 (of_decide_eq_true rfl))
  have e_v725 : v725 = if v13 = 1 then v724 else v203 := e_psel h_v13 h_v724 h_v203 (of_decide_eq_true rfl)
  have h_v726 : R 1 0 0 1 v726 v726 := (r_plt hl h_v19 h_v723 (of_decide_eq_true rfl))
  have e_v726 : (v726 = 1 ↔ sv v19 < sv v723) := e_plt h_v19 h_v723 (of_decide_eq_true rfl)
  have h_v727 : R 1 0 0 1 v727 v727 := (r_plt hl h_v9 h_v725 (of_decide_eq_true rfl))
  have e_v727 : (v727 = 1 ↔ sv v9 < sv v725) := e_plt h_v9 h_v725 (of_decide_eq_true rfl)
  have h_v728 : R 1 0 0 1 v728 v728 := (r_sub hl (r_O hl) h_v727 (of_decide_eq_true rfl))
  have e_v728 : (v728 = 1 ↔ ¬v727 = 1) := e_not h_v727 (of_decide_eq_true rfl)
  have h_v729 : R 1 0 0 1 v729 v729 := (r_land hl h_v726 h_v728 (of_decide_eq_true rfl))
  have e_v729 : (v729 = 1 ↔ v726 = 1 ∧ v728 = 1) := e_land h_v726 h_v728 (of_decide_eq_true rfl)
  clear h_H61r h_v7 h_v203 h_v682 h_v713 h_v714 h_v715 h_v716 h_v717 h_v718 h_v719 h_v720 h_v724 h_v726 h_v727 h_v728
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
  have h_v737 : R 1 0 0 1 v737 v737 := (r_plt hl h_v736 h_v33 (of_decide_eq_true rfl))
  have e_v737 : (v737 = 1 ↔ sv v736 < sv v33) := e_plt h_v736 h_v33 (of_decide_eq_true rfl)
  have h_v738 : R 1 0 4611686018427387908 4611686018695823367 v738 v738 := (r_psel hl h_v737 h_v736 h_v33 (of_decide_eq_true rfl))
  have e_v738 : v738 = if v737 = 1 then v736 else v33 := e_psel h_v737 h_v736 h_v33 (of_decide_eq_true rfl)
  have h_v739 : R 1 0 0 1 v739 v739 := (r_plt hl h_v723 h_v36 (of_decide_eq_true rfl))
  have e_v739 : (v739 = 1 ↔ sv v723 < sv v36) := e_plt h_v723 h_v36 (of_decide_eq_true rfl)
  have h_v740 : R 1 0 0 1 v740 v740 := (r_plt hl h_v38 h_v725 (of_decide_eq_true rfl))
  clear h_v36 h_v723 h_t723_1 h_t723_2 e_t723_2 h_t725_1 h_t725_2 e_t725_2 h_v732 h_v733 h_v735 h_v736 h_v737
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
  have e_v749 : (v749 = 1 ↔ v67 = 1 ∧ v748 = 1) := e_land h_v67 h_v748 (of_decide_eq_true rfl)
  have h_v750 : R 1 0 0 1 v750 v750 := (r_sub hl (r_O hl) h_v749 (of_decide_eq_true rfl))
  have e_v750 : (v750 = 1 ↔ ¬v749 = 1) := e_not h_v749 (of_decide_eq_true rfl)
  have h_v751 : R 1 0 0 1 v751 v751 := (r_land hl h_v63 h_v748 (of_decide_eq_true rfl))
  have e_v751 : (v751 = 1 ↔ v63 = 1 ∧ v748 = 1) := e_land h_v63 h_v748 (of_decide_eq_true rfl)
  have h_v752 : R 1 0 0 1 v752 v752 := (r_lor hl h_v747 h_v751 (of_decide_eq_true rfl))
  have e_v752 : (v752 = 1 ↔ v747 = 1 ∨ v751 = 1) := e_lor h_v747 h_v751 (of_decide_eq_true rfl)
  clear h_v38 h_v725 h_v738 h_v739 h_v740 h_v741 h_v743 h_v745 h_v746 h_v749 h_v751
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
  have h_v762 : R 1 0 4611686018427387900 4611686018695823367 v762 v762 := (r_psel hl h_v761 h_v734 h_v742 (of_decide_eq_true rfl))
  have e_v762 : v762 = if v761 = 1 then v734 else v742 := e_psel h_v761 h_v734 h_v742 (of_decide_eq_true rfl)
  have h_v763 : R 1 0 4611686017353646052 4683743616223412273 v763 v763 := (r_smx hl 29 h_v756 h_v753 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  have e_v763 : sv v763 = sv v756 * sv v753 := e_smx 29 h_v756 h_v753 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v764 : R 1 0 4611686018427387899 4611686018695823374 v764 v764 := (r_srdF hl h_v763 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl))
  have e_v764 : sv v764 = sv v763 / 2 ^ 28 := e_srdF h_v763 4611686018427387899 4611686018695823374 (of_decide_eq_true rfl)
  have h_v765 : R 1 0 4611686017353646052 4683743616223412273 v765 v765 := (r_smx hl 29 h_v762 h_v759 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl))
  clear h_v734 h_v742 h_v744 h_v747 h_v748 h_v752 h_v753 h_v754 h_v755 h_v756 h_v757 h_v758 h_v760 h_v761 h_v763
  have e_v765 : sv v765 = sv v762 * sv v759 := e_smx 29 h_v762 h_v759 4611686017353646052 4683743616223412273 (of_decide_eq_true rfl)
  have h_v766 : R 1 0 4611686018427387900 4611686018695823375 v766 v766 := (r_srdC hl h_v765 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl))
  have e_v766 : sv v766 = -((-sv v765) / 2 ^ 28) := e_srdC h_v765 4611686018427387900 4611686018695823375 (of_decide_eq_true rfl)
  have h_v767 : R 1 0 0 1 v767 v767 := (r_plt hl h_v19 h_v764 (of_decide_eq_true rfl))
  have e_v767 : (v767 = 1 ↔ sv v19 < sv v764) := e_plt h_v19 h_v764 (of_decide_eq_true rfl)
  have h_v768 : R 1 0 0 1 v768 v768 := (r_plt hl h_v61 h_v438 (of_decide_eq_true rfl))
  have e_v768 : (v768 = 1 ↔ sv v61 < sv v438) := e_plt h_v61 h_v438 (of_decide_eq_true rfl)
  have h_v769 : R 1 0 0 1 v769 v769 := (r_plt hl h_v440 h_v33 (of_decide_eq_true rfl))
  have e_v769 : (v769 = 1 ↔ sv v440 < sv v33) := e_plt h_v440 h_v33 (of_decide_eq_true rfl)
  have h_v770 : R 1 0 0 1 v770 v770 := (r_land hl h_v768 h_v769 (of_decide_eq_true rfl))
  have e_v770 : (v770 = 1 ↔ v768 = 1 ∧ v769 = 1) := e_land h_v768 h_v769 (of_decide_eq_true rfl)
  have h_v771 : R 1 0 0 1 v771 v771 := (r_plt hl h_v61 h_v89 (of_decide_eq_true rfl))
  have e_v771 : (v771 = 1 ↔ sv v61 < sv v89) := e_plt h_v61 h_v89 (of_decide_eq_true rfl)
  have h_v772 : R 1 0 0 1 v772 v772 := (r_plt hl h_v91 h_v33 (of_decide_eq_true rfl))
  have e_v772 : (v772 = 1 ↔ sv v91 < sv v33) := e_plt h_v91 h_v33 (of_decide_eq_true rfl)
  have h_v773 : R 1 0 0 1 v773 v773 := (r_land hl h_v771 h_v772 (of_decide_eq_true rfl))
  have e_v773 : (v773 = 1 ↔ v771 = 1 ∧ v772 = 1) := e_land h_v771 h_v772 (of_decide_eq_true rfl)
  have h_v774 : R 1 0 0 1 v774 v774 := (r_plt hl h_v61 h_v764 (of_decide_eq_true rfl))
  have e_v774 : (v774 = 1 ↔ sv v61 < sv v764) := e_plt h_v61 h_v764 (of_decide_eq_true rfl)
  have h_v775 : R 1 0 0 1 v775 v775 := (r_plt hl h_v766 h_v33 (of_decide_eq_true rfl))
  have e_v775 : (v775 = 1 ↔ sv v766 < sv v33) := e_plt h_v766 h_v33 (of_decide_eq_true rfl)
  have h_v776 : R 1 0 0 1 v776 v776 := (r_land hl h_v774 h_v775 (of_decide_eq_true rfl))
  have e_v776 : (v776 = 1 ↔ v774 = 1 ∧ v775 = 1) := e_land h_v774 h_v775 (of_decide_eq_true rfl)
  have h_v777 : R 1 0 0 1 v777 v777 := (r_land hl h_v770 h_v773 (of_decide_eq_true rfl))
  have e_v777 : (v777 = 1 ↔ v770 = 1 ∧ v773 = 1) := e_land h_v770 h_v773 (of_decide_eq_true rfl)
  clear h_v19 h_v759 h_v762 h_v765 h_v768 h_v769 h_v770 h_v771 h_v772 h_v773 h_v774 h_v775
  have h_v778 : R 1 0 0 1 v778 v778 := (r_land hl h_v776 h_v777 (of_decide_eq_true rfl))
  have e_v778 : (v778 = 1 ↔ v776 = 1 ∧ v777 = 1) := e_land h_v776 h_v777 (of_decide_eq_true rfl)
  have h_v779 : R 1 0 4611686018427387904 4683743620518379745 v779 v779 := (r_smx_sq hl 29 h_v440 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v779 : sv v779 = sv v440 * sv v440 := e_smx_sq 29 h_v440 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
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
  have h_v785 : R 1 0 4611686018427387904 4683743619981508804 v785 v785 := (r_smx_sq hl 29 h_v438 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v785 : sv v785 = sv v438 * sv v438 := e_smx_sq 29 h_v438 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v786 : R 1 0 4611686018427387904 4611686018695823388 v786 v786 := (r_srdF hl h_v785 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v786 : sv v786 = sv v785 / 2 ^ 28 := e_srdF h_v785 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v787 : R 1 0 4611686018427387904 4611686018964258872 v787 v787 := (r_sub hl (r_add hl h_v786 h_v786 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v787 : sv v787 = sv v786 + sv v786 := e_add h_v786 h_v786 (of_decide_eq_true rfl)
  have h_v788 : R 1 0 4611686018158952392 4611686018695823360 v788 v788 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v787 (of_decide_eq_true rfl))
  have e_v788 : sv v788 = sv v33 - sv v787 := e_sub h_v33 h_v787 (of_decide_eq_true rfl)
  have h_v789 : R 1 0 4611686018427387904 4683743620518379745 v789 v789 := (r_smx_sq hl 29 h_v766 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v789 : sv v789 = sv v766 * sv v766 := e_smx_sq 29 h_v766 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v790 : R 1 0 4611686018427387904 4611686018695823391 v790 v790 := (r_srdC hl h_v789 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  clear h_v777 h_v779 h_v780 h_v781 h_v782 h_v783 h_v785 h_v786 h_v787
  have e_v790 : sv v790 = -((-sv v789) / 2 ^ 28) := e_srdC h_v789 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v791 : R 1 0 4611686018427387904 4611686018964258878 v791 v791 := (r_sub hl (r_add hl h_v790 h_v790 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v791 : sv v791 = sv v790 + sv v790 := e_add h_v790 h_v790 (of_decide_eq_true rfl)
  have h_v792 : R 1 0 4611686018158952386 4611686018695823360 v792 v792 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v791 (of_decide_eq_true rfl))
  have e_v792 : sv v792 = sv v33 - sv v791 := e_sub h_v33 h_v791 (of_decide_eq_true rfl)
  have h_v793 : R 1 0 0 1 v793 v793 := (r_plt hl h_v792 h_v95 (of_decide_eq_true rfl))
  have e_v793 : (v793 = 1 ↔ sv v792 < sv v95) := e_plt h_v792 h_v95 (of_decide_eq_true rfl)
  have h_v794 : R 1 0 4611686018158952386 4611686018695823360 v794 v794 := (r_psel hl h_v793 h_v95 h_v792 (of_decide_eq_true rfl))
  have e_v794 : v794 = if v793 = 1 then v95 else v792 := e_psel h_v793 h_v95 h_v792 (of_decide_eq_true rfl)
  have h_v795 : R 1 0 4611686018427387904 4683743619981508804 v795 v795 := (r_smx_sq hl 29 h_v764 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl))
  have e_v795 : sv v795 = sv v764 * sv v764 := e_smx_sq 29 h_v764 4611686018427387904 4683743619981508804 (of_decide_eq_true rfl)
  have h_v796 : R 1 0 4611686018427387904 4611686018695823388 v796 v796 := (r_srdF hl h_v795 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl))
  have e_v796 : sv v796 = sv v795 / 2 ^ 28 := e_srdF h_v795 4611686018427387904 4611686018695823388 (of_decide_eq_true rfl)
  have h_v797 : R 1 0 4611686018427387904 4611686018964258872 v797 v797 := (r_sub hl (r_add hl h_v796 h_v796 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v797 : sv v797 = sv v796 + sv v796 := e_add h_v796 h_v796 (of_decide_eq_true rfl)
  have h_v798 : R 1 0 4611686018158952392 4611686018695823360 v798 v798 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v797 (of_decide_eq_true rfl))
  have e_v798 : sv v798 = sv v33 - sv v797 := e_sub h_v33 h_v797 (of_decide_eq_true rfl)
  have h_v799 : R 1 0 4611686018427387904 4683743620518379745 v799 v799 := (r_smx_sq hl 29 h_v91 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v799 : sv v799 = sv v91 * sv v91 := e_smx_sq 29 h_v91 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v800 : R 1 0 4611686018427387904 4611686018695823391 v800 v800 := (r_srdC hl h_v799 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v800 : sv v800 = -((-sv v799) / 2 ^ 28) := e_srdC h_v799 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v801 : R 1 0 4611686018427387904 4611686018964258878 v801 v801 := (r_sub hl (r_add hl h_v800 h_v800 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v801 : sv v801 = sv v800 + sv v800 := e_add h_v800 h_v800 (of_decide_eq_true rfl)
  have h_v802 : R 1 0 4611686018158952386 4611686018695823360 v802 v802 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v801 (of_decide_eq_true rfl))
  have e_v802 : sv v802 = sv v33 - sv v801 := e_sub h_v33 h_v801 (of_decide_eq_true rfl)
  clear h_v789 h_v790 h_v791 h_v792 h_v793 h_v795 h_v796 h_v797 h_v799 h_v800 h_v801
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
  have h_v812 : R 1 0 0 1 v812 v812 := (r_sub hl (r_O hl) h_v811 (of_decide_eq_true rfl))
  have e_v812 : (v812 = 1 ↔ ¬v811 = 1) := e_not h_v811 (of_decide_eq_true rfl)
  have h_v813 : R 1 0 0 1 v813 v813 := (r_land hl h_v809 h_v812 (of_decide_eq_true rfl))
  have e_v813 : (v813 = 1 ↔ v809 = 1 ∧ v812 = 1) := e_land h_v809 h_v812 (of_decide_eq_true rfl)
  have h_v814 : R 1 0 0 1 v814 v814 := (r_land hl h_v809 h_v811 (of_decide_eq_true rfl))
  have e_v814 : (v814 = 1 ↔ v809 = 1 ∧ v811 = 1) := e_land h_v809 h_v811 (of_decide_eq_true rfl)
  have h_v815 : R 1 0 0 1 v815 v815 := (r_plt hl h_v804 h_v61 (of_decide_eq_true rfl))
  clear h_v802 h_v803 h_v805 h_v806 h_v807 h_v809 h_v811 h_v812
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
  have e_v824 : (v824 = 1 ↔ v822 = 1 ∨ v823 = 1) := e_lor h_v822 h_v823 (of_decide_eq_true rfl)
  have h_v825 : R 1 0 0 1 v825 v825 := (r_land hl h_v810 h_v820 (of_decide_eq_true rfl))
  have e_v825 : (v825 = 1 ↔ v810 = 1 ∧ v820 = 1) := e_land h_v810 h_v820 (of_decide_eq_true rfl)
  have h_v826 : R 1 0 0 1 v826 v826 := (r_lor hl h_v819 h_v825 (of_decide_eq_true rfl))
  have e_v826 : (v826 = 1 ↔ v819 = 1 ∨ v825 = 1) := e_lor h_v819 h_v825 (of_decide_eq_true rfl)
  have h_v827 : R 1 0 4611686018158952386 4611686018695823360 v827 v827 := (r_psel hl h_v826 h_v788 h_v784 (of_decide_eq_true rfl))
  have e_v827 : v827 = if v826 = 1 then v788 else v784 := e_psel h_v826 h_v788 h_v784 (of_decide_eq_true rfl)
  clear h_v815 h_v817 h_v818 h_v821 h_v822 h_v825 h_v826
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
  have h_v837 : R 1 0 4539628407746461696 4683743645751316228 v837 v837 := (r_smx hl 30 h_v830 h_v827 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v837 : sv v837 = sv v830 * sv v827 := e_smx 30 h_v830 h_v827 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v838 : R 1 0 4611686018158952386 4611686018695823484 v838 v838 := (r_srdF hl h_v837 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  have e_v838 : sv v838 = sv v837 / 2 ^ 28 := e_srdF h_v837 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v839 : R 1 0 4539628407746461696 4683743645751316228 v839 v839 := (r_smx hl 30 h_v836 h_v833 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v839 : sv v839 = sv v836 * sv v833 := e_smx 30 h_v836 h_v833 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v840 : R 1 0 4611686018158952386 4611686018695823485 v840 v840 := (r_srdC hl h_v839 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  clear h_v827 h_v828 h_v829 h_v830 h_v831 h_v832 h_v833 h_v834 h_v835 h_v836 h_v837
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
  have e_v849 : (v849 = 1 ↔ v814 = 1 ∧ v848 = 1) := e_land h_v814 h_v848 (of_decide_eq_true rfl)
  have h_v850 : R 1 0 0 1 v850 v850 := (r_sub hl (r_O hl) h_v849 (of_decide_eq_true rfl))
  have e_v850 : (v850 = 1 ↔ ¬v849 = 1) := e_not h_v849 (of_decide_eq_true rfl)
  have h_v851 : R 1 0 0 1 v851 v851 := (r_lor hl h_v823 h_v850 (of_decide_eq_true rfl))
  have e_v851 : (v851 = 1 ↔ v823 = 1 ∨ v850 = 1) := e_lor h_v823 h_v850 (of_decide_eq_true rfl)
  have h_v852 : R 1 0 0 1 v852 v852 := (r_land hl h_v810 h_v848 (of_decide_eq_true rfl))
  have e_v852 : (v852 = 1 ↔ v810 = 1 ∧ v848 = 1) := e_land h_v810 h_v848 (of_decide_eq_true rfl)
  clear h_v810 h_v838 h_v839 h_v840 h_v843 h_v845 h_v846 h_v849 h_v850
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
  have h_v862 : R 1 0 0 1 v862 v862 := (r_lor hl h_v813 h_v861 (of_decide_eq_true rfl))
  have e_v862 : (v862 = 1 ↔ v813 = 1 ∨ v861 = 1) := e_lor h_v813 h_v861 (of_decide_eq_true rfl)
  have h_v863 : R 1 0 4611686018158952386 4611686018695823360 v863 v863 := (r_psel hl h_v862 h_v794 h_v798 (of_decide_eq_true rfl))
  have e_v863 : v863 = if v862 = 1 then v794 else v798 := e_psel h_v862 h_v794 h_v798 (of_decide_eq_true rfl)
  have h_v864 : R 1 0 4539628407746461696 4683743645751316228 v864 v864 := (r_smx hl 30 h_v857 h_v854 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v864 : sv v864 = sv v857 * sv v854 := e_smx 30 h_v857 h_v854 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v865 : R 1 0 4611686018158952386 4611686018695823484 v865 v865 := (r_srdF hl h_v864 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl))
  clear h_v813 h_v814 h_v852 h_v853 h_v854 h_v855 h_v856 h_v857 h_v858 h_v859 h_v861 h_v862
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
  have e_v874 : v874 = if v870 = 1 then v91 else v89 := e_psel h_v870 h_v91 h_v89 (of_decide_eq_true rfl)
  have h_v875 : R 1 0 4611686018427387899 4611686018695823375 v875 v875 := (r_psel hl h_v871 h_v89 h_v91 (of_decide_eq_true rfl))
  have e_v875 : v875 = if v871 = 1 then v89 else v91 := e_psel h_v871 h_v89 h_v91 (of_decide_eq_true rfl)
  have h_v876 : R 1 0 4611686018427387899 4611686018695823375 v876 v876 := (r_psel hl h_v871 h_v91 h_v89 (of_decide_eq_true rfl))
  have e_v876 : v876 = if v871 = 1 then v91 else v89 := e_psel h_v871 h_v91 h_v89 (of_decide_eq_true rfl)
  have h_v877 : R 1 0 4611686018427387899 4611686018695823375 v877 v877 := (r_psel hl h_v870 h_v89 h_v91 (of_decide_eq_true rfl))
  have e_v877 : v877 = if v870 = 1 then v89 else v91 := e_psel h_v870 h_v89 h_v91 (of_decide_eq_true rfl)
  clear h_v841 h_v842 h_v860 h_v863 h_v864 h_v865 h_v866 h_v867 h_v868 h_v869
  have h_v878 : R 1 0 4611686018427387899 4611686018695823375 v878 v878 := (r_psel hl h_v872 h_v766 h_v764 (of_decide_eq_true rfl))
  have e_v878 : v878 = if v872 = 1 then v766 else v764 := e_psel h_v872 h_v766 h_v764 (of_decide_eq_true rfl)
  have h_v879 : R 1 0 4611686018427387899 4611686018695823375 v879 v879 := (r_psel hl h_v873 h_v764 h_v766 (of_decide_eq_true rfl))
  have e_v879 : v879 = if v873 = 1 then v764 else v766 := e_psel h_v873 h_v764 h_v766 (of_decide_eq_true rfl)
  have h_v880 : R 1 0 4611686018427387899 4611686018695823375 v880 v880 := (r_psel hl h_v873 h_v766 h_v764 (of_decide_eq_true rfl))
  have e_v880 : v880 = if v873 = 1 then v766 else v764 := e_psel h_v873 h_v766 h_v764 (of_decide_eq_true rfl)
  have h_v881 : R 1 0 4611686018427387899 4611686018695823375 v881 v881 := (r_psel hl h_v872 h_v764 h_v766 (of_decide_eq_true rfl))
  have e_v881 : v881 = if v872 = 1 then v764 else v766 := e_psel h_v872 h_v764 h_v766 (of_decide_eq_true rfl)
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
  have h_v892 : R 1 0 4611686018158952386 4611686018695823360 v892 v892 := (r_psel hl h_v891 h_v95 h_v890 (of_decide_eq_true rfl))
  have e_v892 : v892 = if v891 = 1 then v95 else v890 := e_psel h_v891 h_v95 h_v890 (of_decide_eq_true rfl)
  have h_v893 : R 1 0 4611686018427387904 4683743620518379745 v893 v893 := (r_smx_sq hl 29 h_v874 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v893 : sv v893 = sv v874 * sv v874 := e_smx_sq 29 h_v874 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v894 : R 1 0 4611686018427387904 4611686018695823390 v894 v894 := (r_srdF hl h_v893 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v894 : sv v894 = sv v893 / 2 ^ 28 := e_srdF h_v893 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v895 : R 1 0 4611686018427387904 4611686018964258876 v895 v895 := (r_sub hl (r_add hl h_v894 h_v894 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v872 h_v873 h_v888 h_v889 h_v890 h_v891
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
  have e_v904 : sv v904 = sv v903 / 2 ^ 28 := e_srdF h_v903 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v905 : R 1 0 4611686018427387904 4611686018964258876 v905 v905 := (r_sub hl (r_add hl h_v904 h_v904 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v905 : sv v905 = sv v904 + sv v904 := e_add h_v904 h_v904 (of_decide_eq_true rfl)
  have h_v906 : R 1 0 4611686018158952388 4611686018695823360 v906 v906 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v905 (of_decide_eq_true rfl))
  have e_v906 : sv v906 = sv v33 - sv v905 := e_sub h_v33 h_v905 (of_decide_eq_true rfl)
  have h_v907 : R 1 0 0 1 v907 v907 := (r_plt hl h_v892 h_v61 (of_decide_eq_true rfl))
  have e_v907 : (v907 = 1 ↔ sv v892 < sv v61) := e_plt h_v892 h_v61 (of_decide_eq_true rfl)
  clear h_v894 h_v895 h_v898 h_v899 h_v900 h_v901 h_v904 h_v905
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
  have h_v917 : R 1 0 0 1 v917 v917 := (r_land hl h_v913 h_v916 (of_decide_eq_true rfl))
  have e_v917 : (v917 = 1 ↔ v913 = 1 ∧ v916 = 1) := e_land h_v913 h_v916 (of_decide_eq_true rfl)
  have h_v918 : R 1 0 0 1 v918 v918 := (r_land hl h_v913 h_v915 (of_decide_eq_true rfl))
  have e_v918 : (v918 = 1 ↔ v913 = 1 ∧ v915 = 1) := e_land h_v913 h_v915 (of_decide_eq_true rfl)
  have h_v919 : R 1 0 0 1 v919 v919 := (r_land hl h_v912 h_v918 (of_decide_eq_true rfl))
  have e_v919 : (v919 = 1 ↔ v912 = 1 ∧ v918 = 1) := e_land h_v912 h_v918 (of_decide_eq_true rfl)
  have h_v920 : R 1 0 0 1 v920 v920 := (r_sub hl (r_O hl) h_v919 (of_decide_eq_true rfl))
  clear h_v907 h_v909 h_v910 h_v913 h_v915 h_v916
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
  have e_v935 : sv v935 = sv v934 / 2 ^ 28 := e_srdF h_v934 4611686018158952386 4611686018695823484 (of_decide_eq_true rfl)
  have h_v939 : R 1 0 4611686017890516812 4611686018964258878 v939 v939 := (r_sub hl (r_add hl h_v788 h_OFFr (of_decide_eq_true rfl)) h_v935 (of_decide_eq_true rfl))
  have e_v939 : sv v939 = sv v788 - sv v935 := e_sub h_v788 h_v935 (of_decide_eq_true rfl)
  have h_v940 : R 1 0 4683743612465315840 4683743612465315840 v940 v940 := (r_c hl 4683743612465315840 (of_decide_eq_true rfl))
  have e_v940 : sv v940 = (72057594037927936) := e_c 4683743612465315840 (72057594037927936) (of_decide_eq_true rfl)
  have h_v941 : R 1 0 4611686010374323999 4683743612465315840 v941 v941 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v893 (of_decide_eq_true rfl))
  have e_v941 : sv v941 = sv v940 - sv v893 := e_sub h_v940 h_v893 (of_decide_eq_true rfl)
  clear h_v892 h_v896 h_v902 h_v906 h_v908 h_v911 h_v912 h_v914 h_v917 h_v918 h_v919 h_v920 h_v922 h_v923 h_v924 h_v925 h_v926 h_v927 h_v934 h_v935
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
  have h_v950 : R 1 0 0 1 v950 v950 := (r_plt hl h_v949 h_v33 (of_decide_eq_true rfl))
  have e_v950 : (v950 = 1 ↔ sv v949 < sv v33) := e_plt h_v949 h_v33 (of_decide_eq_true rfl)
  have h_v951 : R 1 0 4611686018427387894 4611686018695823364 v951 v951 := (r_psel hl h_v950 h_v949 h_v33 (of_decide_eq_true rfl))
  have e_v951 : v951 = if v950 = 1 then v949 else v33 := e_psel h_v950 h_v949 h_v33 (of_decide_eq_true rfl)
  have h_v952 : R 1 0 4611686010374323999 4683743612465315840 v952 v952 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v887 (of_decide_eq_true rfl))
  have e_v952 : sv v952 = sv v940 - sv v887 := e_sub h_v940 h_v887 (of_decide_eq_true rfl)
  have h_v953 : R 1 0 4611686018427387904 4611686018695823360 v953 v953 := (r_psqrt hl h_v952 (of_decide_eq_true rfl))
  clear h_v874 h_v941 h_v942 h_v943 pb_v942_v874 h_v944 h_v945 pb_v943_v874 h_v947 h_v948 h_v949 h_v950
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
  have e_v961 : (v961 = 1 ↔ sv v960 < sv v33) := e_plt h_v960 h_v33 (of_decide_eq_true rfl)
  have h_v962 : R 1 0 4611686018427387894 4611686018695823364 v962 v962 := (r_psel hl h_v961 h_v960 h_v33 (of_decide_eq_true rfl))
  have e_v962 : v962 = if v961 = 1 then v960 else v33 := e_psel h_v961 h_v960 h_v33 (of_decide_eq_true rfl)
  have h_v963 : R 1 0 0 1 v963 v963 := (r_plt hl h_v946 h_v957 (of_decide_eq_true rfl))
  have e_v963 : (v963 = 1 ↔ sv v946 < sv v957) := e_plt h_v946 h_v957 (of_decide_eq_true rfl)
  have h_v964 : R 1 0 4611686018427387894 4611686018695823360 v964 v964 := (r_psel hl h_v963 h_v946 h_v957 (of_decide_eq_true rfl))
  have e_v964 : v964 = if v963 = 1 then v946 else v957 := e_psel h_v963 h_v946 h_v957 (of_decide_eq_true rfl)
  clear h_v875 h_v946 h_v952 h_v953 h_v954 pb_v953_v875 h_v955 h_v956 h_v957 pb_v954_v875 h_v958 h_v959 h_v960 h_v961 h_v963
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
  have h_v974 : R 1 0 4611686010374323999 4683743612465315840 v974 v974 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v903 (of_decide_eq_true rfl))
  have e_v974 : sv v974 = sv v940 - sv v903 := e_sub h_v940 h_v903 (of_decide_eq_true rfl)
  have h_v975 : R 1 0 4611686018427387904 4611686018695823360 v975 v975 := (r_psqrt hl h_v974 (of_decide_eq_true rfl))
  have e_v975 : sv v975 = ((Nat.sqrt (v974 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v974 (of_decide_eq_true rfl)
  have h_v976 : R 1 0 4611686018427387905 4611686018695823361 v976 v976 := (r_sub hl (r_add hl h_v105 h_v975 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v976 : sv v976 = sv v105 + sv v975 := e_add h_v105 h_v975 (of_decide_eq_true rfl)
  have pb_v975_v878 : PB 1 v975 v878 36028797018963968 := pb_sqrt hl h_v878 29 36028797018963968 (of_decide_eq_true rfl)
  clear h_v887 h_v893 h_v951 h_v962 h_v965 h_v966 h_v968 h_v969 h_v970 h_v971 h_v972 h_v974
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
  have e_v985 : sv v985 = sv v940 - sv v897 := e_sub h_v940 h_v897 (of_decide_eq_true rfl)
  have h_v986 : R 1 0 4611686018427387904 4611686018695823360 v986 v986 := (r_psqrt hl h_v985 (of_decide_eq_true rfl))
  have e_v986 : sv v986 = ((Nat.sqrt (v985 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v985 (of_decide_eq_true rfl)
  have h_v987 : R 1 0 4611686018427387905 4611686018695823361 v987 v987 := (r_sub hl (r_add hl h_v105 h_v986 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v987 : sv v987 = sv v105 + sv v986 := e_add h_v105 h_v986 (of_decide_eq_true rfl)
  have pb_v986_v879 : PB 1 v986 v879 36028797018963968 := pb_sqrt hl h_v879 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v988 : R 1 0 4611686017085210624 4647714815446351872 v988 v988 := (r_smx_pb hl 29 h_v986 h_v879 pb_v986_v879 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  clear h_v878 h_v975 h_v976 pb_v975_v878 h_v977 h_v978 pb_v976_v878 h_v980 h_v981 h_v982 h_v983 h_v985
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
  have h_v997 : R 1 0 4611686018427387894 4611686018695823360 v997 v997 := (r_psel hl h_v996 h_v979 h_v990 (of_decide_eq_true rfl))
  have e_v997 : v997 = if v996 = 1 then v979 else v990 := e_psel h_v996 h_v979 h_v990 (of_decide_eq_true rfl)
  have h_v998 : R 1 0 0 1 v998 v998 := (r_plt hl h_v984 h_v995 (of_decide_eq_true rfl))
  have e_v998 : (v998 = 1 ↔ sv v984 < sv v995) := e_plt h_v984 h_v995 (of_decide_eq_true rfl)
  have h_v999 : R 1 0 4611686018427387894 4611686018695823364 v999 v999 := (r_psel hl h_v998 h_v995 h_v984 (of_decide_eq_true rfl))
  have e_v999 : v999 = if v998 = 1 then v995 else v984 := e_psel h_v998 h_v995 h_v984 (of_decide_eq_true rfl)
  have h_v1000 : R 1 0 0 1 v1000 v1000 := (r_plt hl h_v967 h_v903 (of_decide_eq_true rfl))
  clear h_v879 h_v979 h_v984 h_v986 h_v987 pb_v986_v879 h_v988 h_v989 h_v990 pb_v987_v879 h_v991 h_v992 h_v993 h_v994 h_v995 h_v996 h_v998
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
  have e_v1009 : (v1009 = 1 ↔ ¬v1008 = 1) := e_not h_v1008 (of_decide_eq_true rfl)
  have h_v1010 : R 1 0 0 1 v1010 v1010 := (r_land hl h_v1006 h_v1009 (of_decide_eq_true rfl))
  have e_v1010 : (v1010 = 1 ↔ v1006 = 1 ∧ v1009 = 1) := e_land h_v1006 h_v1009 (of_decide_eq_true rfl)
  have h_v1011 : R 1 0 0 1 v1011 v1011 := (r_land hl h_v1006 h_v1008 (of_decide_eq_true rfl))
  have e_v1011 : (v1011 = 1 ↔ v1006 = 1 ∧ v1008 = 1) := e_land h_v1006 h_v1008 (of_decide_eq_true rfl)
  have h_v1012 : R 1 0 0 1 v1012 v1012 := (r_plt hl h_v997 h_v61 (of_decide_eq_true rfl))
  have e_v1012 : (v1012 = 1 ↔ sv v997 < sv v61) := e_plt h_v997 h_v61 (of_decide_eq_true rfl)
  clear h_v897 h_v903 h_v999 h_v1000 h_v1001 h_v1002 h_v1003 h_v1004 h_v1006 h_v1008 h_v1009
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
  have h_v1022 : R 1 0 0 1 v1022 v1022 := (r_lor hl h_v1016 h_v1021 (of_decide_eq_true rfl))
  have e_v1022 : (v1022 = 1 ↔ v1016 = 1 ∨ v1021 = 1) := e_lor h_v1016 h_v1021 (of_decide_eq_true rfl)
  have h_v1023 : R 1 0 4611686018427387894 4611686018695823364 v1023 v1023 := (r_psel hl h_v1022 h_v973 h_v964 (of_decide_eq_true rfl))
  have e_v1023 : v1023 = if v1022 = 1 then v973 else v964 := e_psel h_v1022 h_v973 h_v964 (of_decide_eq_true rfl)
  have h_v1024 : R 1 0 0 1 v1024 v1024 := (r_land hl h_v1011 h_v1013 (of_decide_eq_true rfl))
  have e_v1024 : (v1024 = 1 ↔ v1011 = 1 ∧ v1013 = 1) := e_land h_v1011 h_v1013 (of_decide_eq_true rfl)
  have h_v1025 : R 1 0 0 1 v1025 v1025 := (r_lor hl h_v1010 h_v1024 (of_decide_eq_true rfl))
  clear h_v1007 h_v1012 h_v1013 h_v1014 h_v1015 h_v1018 h_v1019 h_v1021 h_v1022
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
  have e_v1034 : sv v1034 = sv v1033 / 2 ^ 28 := e_srdF h_v1033 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v1035 : R 1 0 4611686015743033304 4683743614612799504 v1035 v1035 := (r_smx hl 29 h_v1032 h_v1029 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1035 : sv v1035 = sv v1032 * sv v1029 := e_smx 29 h_v1032 h_v1029 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1036 : R 1 0 4611686018427387894 4611686018695823369 v1036 v1036 := (r_srdC hl h_v1035 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v1036 : sv v1036 = -((-sv v1035) / 2 ^ 28) := e_srdC h_v1035 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1037 : R 1 0 0 1 v1037 v1037 := (r_plt hl h_v61 h_v1034 (of_decide_eq_true rfl))
  have e_v1037 : (v1037 = 1 ↔ sv v61 < sv v1034) := e_plt h_v61 h_v1034 (of_decide_eq_true rfl)
  clear h_v964 h_v973 h_v997 h_v1005 h_v1010 h_v1011 h_v1016 h_v1017 h_v1023 h_v1024 h_v1025 h_v1026 h_v1027 h_v1028 h_v1029 h_v1030 h_v1031 h_v1032 h_v1033 h_v1035
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
  have h_v1049 : R 1 0 4611686017890516812 4611686018964258878 v1049 v1049 := (r_psel hl h_v1048 h_v33 h_v939 (of_decide_eq_true rfl))
  have e_v1049 : v1049 = if v1048 = 1 then v33 else v939 := e_psel h_v1048 h_v33 h_v939 (of_decide_eq_true rfl)
  have h_v1050 : R 1 0 4611686018427387893 4611686018695823369 v1050 v1050 := (r_psel hl h_v1048 h_v33 h_v1042 (of_decide_eq_true rfl))
  have e_v1050 : v1050 = if v1048 = 1 then v33 else v1042 := e_psel h_v1048 h_v33 h_v1042 (of_decide_eq_true rfl)
  have h_v1054 : R 1 0 4611686018427387904 4683743620518379745 v1054 v1054 := (r_smx_sq hl 29 h_v877 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v1054 : sv v1054 = sv v877 * sv v877 := e_smx_sq 29 h_v877 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1055 : R 1 0 4611686018427387904 4611686018695823391 v1055 v1055 := (r_srdC hl h_v1054 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  clear h_v939 h_v1034 h_v1036 h_v1037 h_v1038 h_v1041 h_v1042 h_v1043 h_v1044 h_v1046 h_v1047 h_v1048
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
  have e_v1064 : sv v1064 = sv v881 * sv v881 := e_smx_sq 29 h_v881 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v1065 : R 1 0 4611686018427387904 4611686018695823391 v1065 v1065 := (r_srdC hl h_v1064 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v1065 : sv v1065 = -((-sv v1064) / 2 ^ 28) := e_srdC h_v1064 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v1066 : R 1 0 4611686018427387904 4611686018964258878 v1066 v1066 := (r_sub hl (r_add hl h_v1065 h_v1065 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1066 : sv v1066 = sv v1065 + sv v1065 := e_add h_v1065 h_v1065 (of_decide_eq_true rfl)
  have h_v1067 : R 1 0 4611686018158952386 4611686018695823360 v1067 v1067 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v1066 (of_decide_eq_true rfl))
  have e_v1067 : sv v1067 = sv v33 - sv v1066 := e_sub h_v33 h_v1066 (of_decide_eq_true rfl)
  clear h_v1055 h_v1056 h_v1057 h_v1058 h_v1061 h_v1062 h_v1065 h_v1066
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
  have h_v1078 : R 1 0 0 1 v1078 v1078 := (r_land hl h_v1074 h_v1077 (of_decide_eq_true rfl))
  have e_v1078 : (v1078 = 1 ↔ v1074 = 1 ∧ v1077 = 1) := e_land h_v1074 h_v1077 (of_decide_eq_true rfl)
  have h_v1079 : R 1 0 0 1 v1079 v1079 := (r_land hl h_v1074 h_v1076 (of_decide_eq_true rfl))
  have e_v1079 : (v1079 = 1 ↔ v1074 = 1 ∧ v1076 = 1) := e_land h_v1074 h_v1076 (of_decide_eq_true rfl)
  have h_v1080 : R 1 0 0 1 v1080 v1080 := (r_plt hl h_v1069 h_v61 (of_decide_eq_true rfl))
  have e_v1080 : (v1080 = 1 ↔ sv v1069 < sv v61) := e_plt h_v1069 h_v61 (of_decide_eq_true rfl)
  have h_v1082 : R 1 0 0 1 v1082 v1082 := (r_plt hl h_v61 h_v1073 (of_decide_eq_true rfl))
  clear h_v1067 h_v1068 h_v1071 h_v1072 h_v1074 h_v1076 h_v1077
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
  have e_v1097 : v1097 = if v1096 = 1 then v1059 else v1063 := e_psel h_v1096 h_v1059 h_v1063 (of_decide_eq_true rfl)
  have h_v1098 : R 1 0 0 1 v1098 v1098 := (r_land hl h_v1079 h_v1084 (of_decide_eq_true rfl))
  have e_v1098 : (v1098 = 1 ↔ v1079 = 1 ∧ v1084 = 1) := e_land h_v1079 h_v1084 (of_decide_eq_true rfl)
  have h_v1099 : R 1 0 0 1 v1099 v1099 := (r_lor hl h_v1078 h_v1098 (of_decide_eq_true rfl))
  have e_v1099 : (v1099 = 1 ↔ v1078 = 1 ∨ v1098 = 1) := e_lor h_v1078 h_v1098 (of_decide_eq_true rfl)
  have h_v1100 : R 1 0 4611686018158952386 4611686018695823360 v1100 v1100 := (r_psel hl h_v1099 h_v1069 h_v1073 (of_decide_eq_true rfl))
  have e_v1100 : v1100 = if v1099 = 1 then v1069 else v1073 := e_psel h_v1099 h_v1069 h_v1073 (of_decide_eq_true rfl)
  clear h_v1059 h_v1063 h_v1069 h_v1073 h_v1078 h_v1079 h_v1080 h_v1082 h_v1083 h_v1084 h_v1085 h_v1086 h_v1087 h_v1095 h_v1096 h_v1098 h_v1099
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
  have e_v1112 : sv v1112 = sv v1111 + sv v1111 := e_add h_v1111 h_v1111 (of_decide_eq_true rfl)
  have pb_v1109_v876 : PB 1 v1109 v876 36028797287399439 := pb_sqrt1 hl h_v876 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1113 : R 1 0 4611686017085210619 4647714815714787343 v1113 v1113 := (r_smx_pb hl 29 h_v1109 h_v876 pb_v1109_v876 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1113 : sv v1113 = sv v1109 * sv v876 := e_smx_pb 29 h_v1109 h_v876 pb_v1109_v876 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1114 : R 1 0 4611686018427387899 4611686018561605634 v1114 v1114 := (r_srdC hl h_v1113 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1114 : sv v1114 = -((-sv v1113) / 2 ^ 28) := e_srdC h_v1113 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1115 : R 1 0 4611686018427387894 4611686018695823364 v1115 v1115 := (r_sub hl (r_add hl h_v1114 h_v1114 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_v876 h_v1097 h_v1100 h_v1103 h_v1104 h_v1107 h_v1108 h_v1109 pb_v1108_v876 h_v1110 h_v1111 pb_v1109_v876 h_v1113
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
  have pb_v1120_v877 : PB 1 v1120 v877 36028797287399439 := pb_sqrt1 hl h_v877 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v1124 : R 1 0 4611686017085210619 4647714815714787343 v1124 v1124 := (r_smx_pb hl 29 h_v1120 h_v877 pb_v1120_v877 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v1124 : sv v1124 = sv v1120 * sv v877 := e_smx_pb 29 h_v1120 h_v877 pb_v1120_v877 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v1125 : R 1 0 4611686018427387899 4611686018561605634 v1125 v1125 := (r_srdC hl h_v1124 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v1125 : sv v1125 = -((-sv v1124) / 2 ^ 28) := e_srdC h_v1124 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v1126 : R 1 0 4611686018427387894 4611686018695823364 v1126 v1126 := (r_sub hl (r_add hl h_v1125 h_v1125 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v1126 : sv v1126 = sv v1125 + sv v1125 := e_add h_v1125 h_v1125 (of_decide_eq_true rfl)
  clear h_v877 h_v1114 h_v1115 h_v1116 h_v1118 h_v1119 h_v1120 pb_v1119_v877 h_v1121 h_v1122 pb_v1120_v877 h_v1124 h_v1125
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
  have h_v1136 : R 1 0 0 1 v1136 v1136 := (r_sub hl (r_O hl) h_v1135 (of_decide_eq_true rfl))
  have e_v1136 : (v1136 = 1 ↔ ¬v1135 = 1) := e_not h_v1135 (of_decide_eq_true rfl)
  have h_v1137 : R 1 0 0 1 v1137 v1137 := (r_land hl h_v1134 h_v1136 (of_decide_eq_true rfl))
  have e_v1137 : (v1137 = 1 ↔ v1134 = 1 ∧ v1136 = 1) := e_land h_v1134 h_v1136 (of_decide_eq_true rfl)
  have h_v1138 : R 1 0 4611686018427387894 4611686018695823364 v1138 v1138 := (r_psel hl h_v1137 h_v33 h_v1132 (of_decide_eq_true rfl))
  have e_v1138 : v1138 = if v1137 = 1 then v33 else v1132 := e_psel h_v1137 h_v33 h_v1132 (of_decide_eq_true rfl)
  have h_v1139 : R 1 0 4611686010374323999 4683743612465315840 v1139 v1139 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1070 (of_decide_eq_true rfl))
  clear h_v1054 h_v1060 h_v1112 h_v1117 h_v1123 h_v1126 h_v1127 h_v1128 h_v1129 h_v1131 h_v1132 h_v1133 h_v1134 h_v1135 h_v1136 h_v1137
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
  have e_v1147 : sv v1147 = sv v1146 + sv v1146 := e_add h_v1146 h_v1146 (of_decide_eq_true rfl)
  have h_v1148 : R 1 0 0 1 v1148 v1148 := (r_plt hl h_v1147 h_v33 (of_decide_eq_true rfl))
  have e_v1148 : (v1148 = 1 ↔ sv v1147 < sv v33) := e_plt h_v1147 h_v33 (of_decide_eq_true rfl)
  have h_v1149 : R 1 0 4611686018427387894 4611686018695823364 v1149 v1149 := (r_psel hl h_v1148 h_v1147 h_v33 (of_decide_eq_true rfl))
  have e_v1149 : v1149 = if v1148 = 1 then v1147 else v33 := e_psel h_v1148 h_v1147 h_v33 (of_decide_eq_true rfl)
  have h_v1150 : R 1 0 4611686010374323999 4683743612465315840 v1150 v1150 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v1064 (of_decide_eq_true rfl))
  have e_v1150 : sv v1150 = sv v940 - sv v1064 := e_sub h_v940 h_v1064 (of_decide_eq_true rfl)
  clear h_v880 h_v940 h_v1139 h_v1140 h_v1141 pb_v1140_v880 h_v1142 h_v1143 pb_v1141_v880 h_v1145 h_v1146 h_v1147 h_v1148
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
  have h_v1159 : R 1 0 0 1 v1159 v1159 := (r_plt hl h_v1158 h_v33 (of_decide_eq_true rfl))
  have e_v1159 : (v1159 = 1 ↔ sv v1158 < sv v33) := e_plt h_v1158 h_v33 (of_decide_eq_true rfl)
  have h_v1160 : R 1 0 4611686018427387894 4611686018695823364 v1160 v1160 := (r_psel hl h_v1159 h_v1158 h_v33 (of_decide_eq_true rfl))
  have e_v1160 : v1160 = if v1159 = 1 then v1158 else v33 := e_psel h_v1159 h_v1158 h_v33 (of_decide_eq_true rfl)
  have h_v1161 : R 1 0 0 1 v1161 v1161 := (r_plt hl h_v1144 h_v1155 (of_decide_eq_true rfl))
  have e_v1161 : (v1161 = 1 ↔ sv v1144 < sv v1155) := e_plt h_v1144 h_v1155 (of_decide_eq_true rfl)
  have h_v1162 : R 1 0 4611686018427387894 4611686018695823360 v1162 v1162 := (r_psel hl h_v1161 h_v1144 h_v1155 (of_decide_eq_true rfl))
  clear h_v105 h_v881 h_v1150 h_v1151 h_v1152 pb_v1151_v881 h_v1153 h_v1154 pb_v1152_v881 h_v1156 h_v1157 h_v1158 h_v1159
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
  have e_v1171 : (v1171 = 1 ↔ sv v1130 < sv v61) := e_plt h_v1130 h_v61 (of_decide_eq_true rfl)
  have h_v1172 : R 1 0 0 1 v1172 v1172 := (r_sub hl (r_O hl) h_v1171 (of_decide_eq_true rfl))
  have e_v1172 : (v1172 = 1 ↔ ¬v1171 = 1) := e_not h_v1171 (of_decide_eq_true rfl)
  have h_v1173 : R 1 0 0 1 v1173 v1173 := (r_plt hl h_v61 h_v1138 (of_decide_eq_true rfl))
  have e_v1173 : (v1173 = 1 ↔ sv v61 < sv v1138) := e_plt h_v61 h_v1138 (of_decide_eq_true rfl)
  have h_v1174 : R 1 0 0 1 v1174 v1174 := (r_sub hl (r_O hl) h_v1173 (of_decide_eq_true rfl))
  have e_v1174 : (v1174 = 1 ↔ ¬v1173 = 1) := e_not h_v1173 (of_decide_eq_true rfl)
  clear h_v967 h_v1064 h_v1070 h_v1144 h_v1149 h_v1155 h_v1160 h_v1161 h_v1163 h_v1164 h_v1165 h_v1166 h_v1167 h_v1168 h_v1169
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
  have h_v1184 : R 1 0 0 1 v1184 v1184 := (r_sub hl (r_O hl) h_v1183 (of_decide_eq_true rfl))
  have e_v1184 : (v1184 = 1 ↔ ¬v1183 = 1) := e_not h_v1183 (of_decide_eq_true rfl)
  have h_v1185 : R 1 0 0 1 v1185 v1185 := (r_lor hl h_v823 h_v1184 (of_decide_eq_true rfl))
  have e_v1185 : (v1185 = 1 ↔ v823 = 1 ∨ v1184 = 1) := e_lor h_v823 h_v1184 (of_decide_eq_true rfl)
  have h_v1186 : R 1 0 0 1 v1186 v1186 := (r_land hl h_v1172 h_v1182 (of_decide_eq_true rfl))
  have e_v1186 : (v1186 = 1 ↔ v1172 = 1 ∧ v1182 = 1) := e_land h_v1172 h_v1182 (of_decide_eq_true rfl)
  have h_v1187 : R 1 0 0 1 v1187 v1187 := (r_lor hl h_v1181 h_v1186 (of_decide_eq_true rfl))
  clear h_v1171 h_v1172 h_v1173 h_v1174 h_v1177 h_v1179 h_v1180 h_v1183 h_v1184
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
  have e_v1196 : (v1196 = 1 ↔ v1175 = 1 ∨ v1195 = 1) := e_lor h_v1175 h_v1195 (of_decide_eq_true rfl)
  have h_v1197 : R 1 0 4611686018427387894 4611686018695823364 v1197 v1197 := (r_psel hl h_v1196 h_v1162 h_v1170 (of_decide_eq_true rfl))
  have e_v1197 : v1197 = if v1196 = 1 then v1162 else v1170 := e_psel h_v1196 h_v1162 h_v1170 (of_decide_eq_true rfl)
  have h_v1198 : R 1 0 4611686015743033304 4683743614612799504 v1198 v1198 := (r_smx hl 29 h_v1191 h_v1188 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1198 : sv v1198 = sv v1191 * sv v1188 := e_smx 29 h_v1191 h_v1188 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1199 : R 1 0 4611686018427387893 4611686018695823368 v1199 v1199 := (r_srdF hl h_v1198 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v1199 : sv v1199 = sv v1198 / 2 ^ 28 := e_srdF h_v1198 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  clear h_v1130 h_v1138 h_v1162 h_v1170 h_v1175 h_v1176 h_v1178 h_v1181 h_v1182 h_v1186 h_v1187 h_v1188 h_v1189 h_v1190 h_v1191 h_v1192 h_v1193 h_v1195 h_v1196 h_v1198
  have h_v1200 : R 1 0 4611686015743033304 4683743614612799504 v1200 v1200 := (r_smx hl 29 h_v1197 h_v1194 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v1200 : sv v1200 = sv v1197 * sv v1194 := e_smx 29 h_v1197 h_v1194 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v1201 : R 1 0 4611686018427387894 4611686018695823369 v1201 v1201 := (r_srdC hl h_v1200 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v1201 : sv v1201 = -((-sv v1200) / 2 ^ 28) := e_srdC h_v1200 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v1202 : R 1 0 0 1 v1202 v1202 := (r_plt hl h_v61 h_v1199 (of_decide_eq_true rfl))
  have e_v1202 : (v1202 = 1 ↔ sv v61 < sv v1199) := e_plt h_v61 h_v1199 (of_decide_eq_true rfl)
  have h_v1203 : R 1 0 0 1 v1203 v1203 := (r_sub hl (r_O hl) h_v1202 (of_decide_eq_true rfl))
  have e_v1203 : (v1203 = 1 ↔ ¬v1202 = 1) := e_not h_v1202 (of_decide_eq_true rfl)
  have h_v1204 : R 1 0 0 1 v1204 v1204 := (r_plt hl h_v1105 h_v61 (of_decide_eq_true rfl))
  have e_v1204 : (v1204 = 1 ↔ sv v1105 < sv v61) := e_plt h_v1105 h_v61 (of_decide_eq_true rfl)
  have h_v1205 : R 1 0 4611686018427387893 4611686018695823369 v1205 v1205 := (r_psel hl h_v1204 h_v1199 h_v1201 (of_decide_eq_true rfl))
  have e_v1205 : v1205 = if v1204 = 1 then v1199 else v1201 := e_psel h_v1204 h_v1199 h_v1201 (of_decide_eq_true rfl)
  have h_v1208 : R 1 0 0 1 v1208 v1208 := (r_plt hl h_v1205 h_v1105 (of_decide_eq_true rfl))
  have e_v1208 : (v1208 = 1 ↔ sv v1205 < sv v1105) := e_plt h_v1205 h_v1105 (of_decide_eq_true rfl)
  have h_v1209 : R 1 0 0 1 v1209 v1209 := (r_land hl h_v1202 h_v1208 (of_decide_eq_true rfl))
  have e_v1209 : (v1209 = 1 ↔ v1202 = 1 ∧ v1208 = 1) := e_land h_v1202 h_v1208 (of_decide_eq_true rfl)
  have h_v1210 : R 1 0 4611686018158952439 4611686018427387915 v1210 v1210 := (r_sub hl (r_add hl h_v61 h_OFFr (of_decide_eq_true rfl)) h_v1205 (of_decide_eq_true rfl))
  have e_v1210 : sv v1210 = sv v61 - sv v1205 := e_sub h_v61 h_v1205 (of_decide_eq_true rfl)
  have h_v1211 : R 1 0 0 1 v1211 v1211 := (r_plt hl h_v1210 h_v1105 (of_decide_eq_true rfl))
  have e_v1211 : (v1211 = 1 ↔ sv v1210 < sv v1105) := e_plt h_v1210 h_v1105 (of_decide_eq_true rfl)
  have h_v1212 : R 1 0 0 1 v1212 v1212 := (r_sub hl (r_O hl) h_v1211 (of_decide_eq_true rfl))
  have e_v1212 : (v1212 = 1 ↔ ¬v1211 = 1) := e_not h_v1211 (of_decide_eq_true rfl)
  have h_v1213 : R 1 0 0 1 v1213 v1213 := (r_lor hl h_v1203 h_v1212 (of_decide_eq_true rfl))
  have e_v1213 : (v1213 = 1 ↔ v1203 = 1 ∨ v1212 = 1) := e_lor h_v1203 h_v1212 (of_decide_eq_true rfl)
  have h_v1214 : R 1 0 4611686017890516805 4611686018964258878 v1214 v1214 := (r_psel hl h_v1213 h_v95 h_v1105 (of_decide_eq_true rfl))
  clear h_v1194 h_v1197 h_v1199 h_v1200 h_v1201 h_v1202 h_v1203 h_v1204 h_v1208 h_v1210 h_v1211 h_v1212
  have e_v1214 : v1214 = if v1213 = 1 then v95 else v1105 := e_psel h_v1213 h_v95 h_v1105 (of_decide_eq_true rfl)
  have h_v1215 : R 1 0 4611686018427387893 4611686018695823369 v1215 v1215 := (r_psel hl h_v1213 h_v33 h_v1205 (of_decide_eq_true rfl))
  have e_v1215 : v1215 = if v1213 = 1 then v33 else v1205 := e_psel h_v1213 h_v33 h_v1205 (of_decide_eq_true rfl)
  have h_v1216 : R 1 0 0 1 v1216 v1216 := (r_lor hl h_v1045 h_v1209 (of_decide_eq_true rfl))
  have e_v1216 : (v1216 = 1 ↔ v1045 = 1 ∨ v1209 = 1) := e_lor h_v1045 h_v1209 (of_decide_eq_true rfl)
  have h_v1218 : R 1 0 4611686018427387904 4611686019501129727 v1218 v1218 := (r1_hxa hb_H2 0 (of_decide_eq_true rfl))
  have e_v1218 : sv v1218 = ((H2 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H2 0 (of_decide_eq_true rfl)
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
  clear h_v28 h_v95 h_v1045 h_v1049 h_v1050 h_v1105 h_v1205 h_v1209 h_v1213 h_v1219 h_v1222 h_v1223 h_v1224
  have h_v1227 : R 1 0 0 1 v1227 v1227 := (r_plt hl h_v1226 h_v1225 (of_decide_eq_true rfl))
  have e_v1227 : (v1227 = 1 ↔ sv v1226 < sv v1225) := e_plt h_v1226 h_v1225 (of_decide_eq_true rfl)
  have h_v1228 : R 1 0 0 1 v1228 v1228 := (r_sub hl (r_O hl) h_v1227 (of_decide_eq_true rfl))
  have e_v1228 : (v1228 = 1 ↔ ¬v1227 = 1) := e_not h_v1227 (of_decide_eq_true rfl)
  have h_v1229 : R 1 0 0 1 v1229 v1229 := (r_plt hl h_v15 h_v1218 (of_decide_eq_true rfl))
  have e_v1229 : (v1229 = 1 ↔ sv v15 < sv v1218) := e_plt h_v15 h_v1218 (of_decide_eq_true rfl)
  have h_v1230 : R 1 0 0 1 v1230 v1230 := (r_sub hl (r_O hl) h_v1229 (of_decide_eq_true rfl))
  have e_v1230 : (v1230 = 1 ↔ ¬v1229 = 1) := e_not h_v1229 (of_decide_eq_true rfl)
  have h_v1231 : R 1 0 0 1 v1231 v1231 := (r_land hl h_v1228 h_v1230 (of_decide_eq_true rfl))
  have e_v1231 : (v1231 = 1 ↔ v1228 = 1 ∧ v1230 = 1) := e_land h_v1228 h_v1230 (of_decide_eq_true rfl)
  have h_v1232 : R 1 0 0 1 v1232 v1232 := (r_lor hl h_v1220 h_v1231 (of_decide_eq_true rfl))
  have e_v1232 : (v1232 = 1 ↔ v1220 = 1 ∨ v1231 = 1) := e_lor h_v1220 h_v1231 (of_decide_eq_true rfl)
  have h_v1233 : R 1 0 4611686018427387904 4611686019501129727 v1233 v1233 := (r_psel hl h_v1232 h_v1218 h_v61 (of_decide_eq_true rfl))
  have e_v1233 : v1233 = if v1232 = 1 then v1218 else v61 := e_psel h_v1232 h_v1218 h_v61 (of_decide_eq_true rfl)
  have h_v1234 : R 1 0 4611686018427387904 4611686019501129727 v1234 v1234 := (r1_hxa hb_H2 32 (of_decide_eq_true rfl))
  have e_v1234 : sv v1234 = ((H2 / 2 ^ 32 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H2 32 (of_decide_eq_true rfl)
  have h_v1235 : R 1 0 0 1 v1235 v1235 := (r_plt hl h_v1234 h_v9 (of_decide_eq_true rfl))
  have e_v1235 : (v1235 = 1 ↔ sv v1234 < sv v9) := e_plt h_v1234 h_v9 (of_decide_eq_true rfl)
  have h_v1236 : R 1 0 0 1 v1236 v1236 := (r_sub hl (r_O hl) h_v1235 (of_decide_eq_true rfl))
  have e_v1236 : (v1236 = 1 ↔ ¬v1235 = 1) := e_not h_v1235 (of_decide_eq_true rfl)
  have h_t1234_1 : R 1 0 4611686018427387904 4611686018695823363 t1234.1 t1234.1 := r_sc1 hl h_v1234 (of_decide_eq_true rfl)
  have h_t1234_2 : R 1 0 4611686018158952445 4611686018695823363 t1234.2 t1234.2 := r_sc2 hl h_v1234 (of_decide_eq_true rfl)
  have e_t1234_1 : sv t1234.1 = (sc28pS (scArg v1234)).1 := e_sc1 h_v1234 (of_decide_eq_true rfl)
  have e_t1234_2 : sv t1234.2 = (sc28pS (scArg v1234)).2 := e_sc2 h_v1234 (of_decide_eq_true rfl)
  have h_v1238 : R 1 0 4611686018158952449 4611686018695823367 v1238 v1238 := (r_sub hl (r_add hl h_v31 h_t1234_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  clear h_OFFr h_v9 h_v15 h_v61 h_v1218 h_v1220 h_v1225 h_v1226 h_v1227 h_v1228 h_v1229 h_v1230 h_v1231 h_v1234 h_v1235
  have e_v1238 : sv v1238 = sv v31 + sv t1234.2 := e_add h_v31 h_t1234_2 (of_decide_eq_true rfl)
  have h_v1239 : R 1 0 0 1 v1239 v1239 := (r_plt hl h_v1238 h_v33 (of_decide_eq_true rfl))
  have e_v1239 : (v1239 = 1 ↔ sv v1238 < sv v33) := e_plt h_v1238 h_v33 (of_decide_eq_true rfl)
  have h_v1240 : R 1 0 4611686018158952449 4611686018695823367 v1240 v1240 := (r_psel hl h_v1239 h_v1238 h_v33 (of_decide_eq_true rfl))
  have e_v1240 : v1240 = if v1239 = 1 then v1238 else v33 := e_psel h_v1239 h_v1238 h_v33 (of_decide_eq_true rfl)
  have h_v1241 : R 1 0 4467570780154101760 4755801223146242048 v1241 v1241 := (r_sshl hl h_v1214 4467570780154101760 4755801223146242048 (of_decide_eq_true rfl))
  have e_v1241 : sv v1241 = sv v1214 * 2 ^ 28 := e_sshl h_v1214 4467570780154101760 4755801223146242048 (of_decide_eq_true rfl)
  have h_v1242 : R 1 0 4539628422241976329 4683743616760283199 v1242 v1242 := (r_smx hl 29 h_v1240 h_v1215 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl))
  have e_v1242 : sv v1242 = sv v1240 * sv v1215 := e_smx 29 h_v1240 h_v1215 4539628422241976329 4683743616760283199 (of_decide_eq_true rfl)
  have h_v1243 : R 1 0 0 1 v1243 v1243 := (r_plt hl h_v1241 h_v1242 (of_decide_eq_true rfl))
  have e_v1243 : (v1243 = 1 ↔ sv v1241 < sv v1242) := e_plt h_v1241 h_v1242 (of_decide_eq_true rfl)
  have h_v1244 : R 1 0 0 1 v1244 v1244 := (r_sub hl (r_O hl) h_v1243 (of_decide_eq_true rfl))
  have e_v1244 : (v1244 = 1 ↔ ¬v1243 = 1) := e_not h_v1243 (of_decide_eq_true rfl)
  have h_v1245 : R 1 0 0 1 v1245 v1245 := (r_lor hl h_v1236 h_v1244 (of_decide_eq_true rfl))
  have e_v1245 : (v1245 = 1 ↔ v1236 = 1 ∨ v1244 = 1) := e_lor h_v1236 h_v1244 (of_decide_eq_true rfl)
  exact fun _ k => k e_v712 e_v713 e_v714 e_v715 e_v716 e_v717 e_v718 e_v719 e_v720 h_v722 e_v722 e_v723 e_v724 e_v725 e_v726 e_v727 e_v728 h_v729 e_v729 e_t723_1 e_t725_1 e_v732 e_v733 e_v734 e_v735 e_v736 e_v737 e_v738 e_v739 e_v740 e_v741 e_v742 e_v743 e_v744 e_v745 e_v746 e_v747 e_v748 e_v749 h_v750 e_v750 e_v751 e_v752 e_v753 e_v754 e_v755 e_v756 e_v757 e_v758 e_v759 e_v760 e_v761 e_v762 e_v763 h_v764 e_v764 e_v765 h_v766 e_v766 h_v767 e_v767 e_v768 e_v769 e_v770 e_v771 e_v772 e_v773 e_v774 e_v775 h_v776 e_v776 e_v777 h_v778 e_v778 e_v779 e_v780 e_v781 e_v782 e_v783 h_v784 e_v784 e_v785 e_v786 e_v787 h_v788 e_v788 e_v789 e_v790 e_v791 e_v792 e_v793 h_v794 e_v794 e_v795 e_v796 e_v797 h_v798 e_v798 e_v799 e_v800 e_v801 e_v802 e_v803 h_v804 e_v804 e_v805 e_v806 e_v807 h_v808 e_v808 e_v809 e_v810 e_v811 e_v812 e_v813 e_v814 e_v815 h_v816 e_v816 e_v817 e_v818 h_v819 e_v819 h_v820 e_v820 e_v821 e_v822 h_v823 e_v823 h_v824 e_v824 e_v825 e_v826 e_v827 e_v828 e_v829 e_v830 e_v831 e_v832 e_v833 e_v834 e_v835 e_v836 e_v837 e_v838 e_v839 e_v840 e_v841 e_v842 e_v843 h_v844 e_v844 e_v845 e_v846 h_v847 e_v847 h_v848 e_v848 e_v849 e_v850 h_v851 e_v851 e_v852 e_v853 e_v854 e_v855 e_v856 e_v857 e_v858 e_v859 e_v860 e_v861 e_v862 e_v863 e_v864 e_v865 e_v866 e_v867 e_v868 e_v869 h_v870 e_v870 h_v871 e_v871 e_v872 e_v873 e_v874 e_v875 e_v876 e_v877 e_v878 e_v879 e_v880 e_v881 e_v887 e_v888 e_v889 e_v890 e_v891 e_v892 e_v893 e_v894 e_v895 e_v896 e_v897 e_v898 e_v899 e_v900 e_v901 e_v902 e_v903 e_v904 e_v905 e_v906 e_v907 e_v908 e_v909 e_v910 e_v911 e_v912 e_v913 e_v914 e_v915 e_v916 e_v917 e_v918 e_v919 e_v920 h_v921 e_v921 e_v922 e_v923 e_v924 e_v925 e_v926 e_v927 e_v934 e_v935 e_v939 e_v940 e_v941 e_v942 e_v943 e_v944 e_v945 e_v946 e_v947 e_v948 e_v949 e_v950 e_v951 e_v952 e_v953 e_v954 e_v955 e_v956 e_v957 e_v958 e_v959 e_v960 e_v961 e_v962 e_v963 e_v964 e_v965 e_v966 e_v967 e_v968 e_v969 e_v970 e_v971 e_v972 e_v973 e_v974 e_v975 e_v976 e_v977 e_v978 e_v979 e_v980 e_v981 e_v982 e_v983 e_v984 e_v985 e_v986 e_v987 e_v988 e_v989 e_v990 e_v991 e_v992 e_v993 e_v994 e_v995 e_v996 e_v997 e_v998 e_v999 e_v1000 e_v1001 e_v1002 e_v1003 e_v1004 e_v1005 e_v1006 e_v1007 e_v1008 e_v1009 e_v1010 e_v1011 e_v1012 e_v1013 e_v1014 e_v1015 e_v1016 e_v1017 e_v1018 e_v1019 h_v1020 e_v1020 e_v1021 e_v1022 e_v1023 e_v1024 e_v1025 e_v1026 e_v1027 e_v1028 e_v1029 e_v1030 e_v1031 e_v1032 e_v1033 e_v1034 e_v1035 e_v1036 e_v1037 e_v1038 e_v1041 e_v1042 e_v1043 e_v1044 e_v1045 e_v1046 e_v1047 e_v1048 e_v1049 e_v1050 e_v1054 e_v1055 e_v1056 e_v1057 e_v1058 e_v1059 e_v1060 e_v1061 e_v1062 e_v1063 e_v1064 e_v1065 e_v1066 e_v1067 e_v1068 e_v1069 e_v1070 e_v1071 e_v1072 e_v1073 e_v1074 e_v1076 e_v1077 e_v1078 e_v1079 e_v1080 e_v1082 e_v1083 e_v1084 e_v1085 e_v1086 e_v1087 h_v1088 e_v1088 e_v1095 e_v1096 e_v1097 e_v1098 e_v1099 e_v1100 e_v1103 e_v1104 e_v1105 e_v1107 e_v1108 e_v1109 e_v1110 e_v1111 e_v1112 e_v1113 e_v1114 e_v1115 e_v1116 e_v1117 e_v1118 e_v1119 e_v1120 e_v1121 e_v1122 e_v1123 e_v1124 e_v1125 e_v1126 e_v1127 e_v1128 e_v1129 e_v1130 e_v1131 e_v1132 e_v1133 e_v1134 e_v1135 e_v1136 e_v1137 e_v1138 e_v1139 e_v1140 e_v1141 e_v1142 e_v1143 e_v1144 e_v1145 e_v1146 e_v1147 e_v1148 e_v1149 e_v1150 e_v1151 e_v1152 e_v1153 e_v1154 e_v1155 e_v1156 e_v1157 e_v1158 e_v1159 e_v1160 e_v1161 e_v1162 e_v1163 e_v1164 e_v1165 e_v1166 e_v1167 e_v1168 e_v1169 e_v1170 e_v1171 e_v1172 e_v1173 e_v1174 e_v1175 e_v1176 e_v1177 e_v1178 e_v1179 e_v1180 e_v1181 e_v1182 e_v1183 e_v1184 h_v1185 e_v1185 e_v1186 e_v1187 e_v1188 e_v1189 e_v1190 e_v1191 e_v1192 e_v1193 e_v1194 e_v1195 e_v1196 e_v1197 e_v1198 e_v1199 e_v1200 e_v1201 e_v1202 e_v1203 e_v1204 e_v1205 e_v1208 e_v1209 e_v1210 e_v1211 e_v1212 e_v1213 e_v1214 e_v1215 h_v1216 e_v1216 e_v1218 e_v1219 e_v1220 h_t1218_1 h_t1218_2 e_t1218_1 e_t1218_2 e_v1222 e_v1223 e_v1224 e_v1225 e_v1226 e_v1227 e_v1228 e_v1229 e_v1230 e_v1231 h_v1232 e_v1232 h_v1233 e_v1233 e_v1234 e_v1235 e_v1236 h_t1234_1 h_t1234_2 e_t1234_1 e_t1234_2 e_v1238 e_v1239 e_v1240 e_v1241 e_v1242 e_v1243 e_v1244 h_v1245 e_v1245

end Tammes15.D3Trig
