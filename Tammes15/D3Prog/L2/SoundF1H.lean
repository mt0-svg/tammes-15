import Tammes15.D3Prog.L2.SoundF1HSeg0
import Tammes15.D3Prog.L2.SoundF1HSeg1
import Tammes15.D3Prog.L2.SoundF1HSeg2
import Tammes15.D3Prog.L2.Kinds
import Tammes15.D3Prog.L2.PLib

namespace D3Prog

open D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progF1H_l2 (F0 F1 F2 F3 H0 H1 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (h : D3Ck2.progF1H 1 F0 F1 F2 F3 H0 H1 = 1) (hD : L2.InDom F0 F1 F2 F3) : L2.LaneClaim 1 true F0 F1 F2 F3 := by
  unfold D3Ck2.progF1H at h
  extract_lets -merge OFFr H61r v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v11 v12 v13 t0 t1 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 t32 t33 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v94 v95 v96 v97 v98 v99 v100 v102 v103 v104 v105 v106 v107 v108 v109 v110 v112 v113 v114 v115 v116 v134 v135 v136 v137 v138 v139 v176 v206 v213 v267 v268 v269 v270 v278 v279 v280 v281 v282 t267 v284 v285 v286 v287 v288 v289 v290 v291 v292 v293 v294 v296 v297 v298 v299 v300 v301 v302 v303 v304 v305 v306 v307 v308 v309 v310 v311 v312 v313 v314 v315 v316 v317 v318 v319 v320 v321 v322 v323 v324 v325 v326 v327 v328 v329 v332 v333 v375 v376 v377 t377 v379 v380 v381 v382 v383 v384 v386 v387 v388 v389 v390 v391 v392 v393 v394 v395 v396 v397 v398 v399 v400 v401 v402 v403 v404 v405 v406 v407 v408 v409 v410 v411 v412 v413 v414 v415 v417 v418 v419 v420 v421 v422 v423 t418 t419 v426 v427 v428 v429 v430 v431 v432 v433 v434 v435 v436 v437 v439 v440 v441 v442 v443 v444 v445 v446 v447 v448 v449 v450 v451 v452 v453 v454 v455 v456 v457 v458 v459 v460 v461 v462 v463 v464 v465 v466 v467 v468 v469 v470 v471 v472 v473 v474 v475 v476 v477 v478 v479 v480 v481 v482 v483 v484 v485 v486 v487 v488 v489 v490 v491 v492 v493 v494 v495 v496 v497 v498 v499 v500 v501 v502 v503 v504 v505 v506 v508 v509 v510 v511 v512 v513 v514 v515 v516 v517 v518 v519 v520 v521 v522 v523 v524 v525 v526 v527 v528 v529 v530 v531 v532 v533 v534 v535 v536 v537 v538 v539 v540 v541 v542 v544 v545 v546 v547 v548 v549 v550 v551 v552 v553 v554 v555 v556 v557 v558 v559 v560 v561 v562 v563 v564 v565 v566 v567 v568 v569 v570 v571 v572 v573 v574 v575 v576 v577 v578 v579 v580 v581 v582 v583 v584 v585 v586 v587 v588 v589 v590 v591 v592 v593 v599 v600 v601 v602 v603 v604 v605 v606 v607 v608 v609 v610 v611 v612 v613 v614 v615 v616 v617 v618 v619 v620 v621 v622 v623 v624 v625 v627 v628 v629 v630 v631 v632 v633 v634 v635 v636 v637 v638 v645 v646 v649 v650 v653 v654 v657 v660 v661 v662 v663 v664 v665 v666 v667 v668 v669 v670 v671 v672 v673 v674 v675 v676 v677 v678 v679 v680 v681 v682 v683 v684 v685 v686 v687 v688 v689 v690 v691 v692 v693 v694 v695 v696 v697 v698 v699 v700 v701 v702 v703 v704 v705 v706 v707 v708 v709 v710 v711 v712 v713 v714 v715 v716 v717 v718 v719 v720 v721 v722 v723 v724 v725 v726 v727 v728 v729 v730 v731 v732 v733 v735 v736 v737 v738 v739 v740 v741 v742 v743 v744 v745 v746 v747 v748 v749 v750 v751 v752 v753 v754 v755 v756 v757 v758 v759 v760 v761 v762 v763 v764 v765 v766 v767 v768 v771 v772 v773 v774 v775 v776 v777 v778 v779 v780 v781 v782 v783 v789 v790 v791 v792 v793 v794 v795 v796 v797 v798 v799 v800 v801 v802 v803 v804 v805 v806 v807 v808 v809 v811 v812 v813 v814 v815 v817 v818 v819 v820 v821 v829 v830 v831 v832 v833 v834 v837 v838 v841 v842 v845 v846 v848 v849 v851 v852 v853 v854 v855 v856 v857 v858 v859 v860 v861 v862 v863 v864 v865 v866 v867 v868 v869 v870 v871 v872 v873 v874 v875 v876 v877 v878 v879 v880 v881 v882 v883 v884 v885 v886 v887 v888 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 v918 v919 v920 v921 v923 v924 v925 v926 v927 v928 v929 v930 v931 v932 v933 v934 v935 v936 v937 v938 v939 v940 v941 v942 v943 v944 v945 v946 v947 v948 v949 v950 v951 v952 v953 v954 v955 v956 v957 v958 v961 v962 v963 v964 v965 v966 v967 v968 v969 v971 v972 v973 t971 v975 v976 v977 v978 v979 v980 v981 v982 v983 v984 v985 v986 v987 v988 v989 t987 v991 v992 v993 v994 v995 v996 v997 v998 v999 v1000 v1001 v1002 v1005 v1007 v1008 v1009 v1010 v1012 v1013 v1014 v1015 v1016 v1017 v1018 v1019 v1020 v1027 v1028 v1031 v1032 v1035 v1036 v1039 v1041 v1042 v1043 v1044 v1045 v1046 v1047 v1048 v1049 v1050 v1051 v1052 v1053 v1054 v1055 v1056 v1057 v1058 v1059 v1061 v1062 v1064 v1065 v1066 v1067 v1068 v1069 v1070 v1071 v1072 v1073 v1074 v1075 v1076 v1077 v1078 v1079 v1080 v1081 v1082 v1083 v1084 v1085 v1086 v1087 v1088 v1089 v1090 v1091 v1092 v1093 v1094 v1095 v1096 v1097 v1098 v1099 v1100 v1101 v1102 v1103 v1104 v1105 v1106 v1107 v1108 v1109 v1110 v1111 v1112 v1113 v1114 v1115 v1116 v1117 v1118 v1130 v1131 v1132 v1135 v1136 v1137 v1138 v1139 v1140 v1141 v1142 v1143 v1144 v1145 v1146 v1147 v1148 v1149 v1150 v1151 v1152 v1154 v1155 v1156 v1157 v1158 v1159 v1160 v1161 v1162 v1163 v1164 v1165 v1166 v1167 v1168 v1169 v1170 v1171 v1172 v1173 v1174 v1175 v1176 v1177 v1178 v1179 v1180 v1181 v1182 v1183 v1184 v1185 v1186 v1187 v1188 v1189 v1190 v1341 v1342 v1343 v1344 v1345 t1343 v1347 v1348 v1349 v1350 v1351 v1352 v1353 v1354 v1355 v1356 v1357 v1359 v1360 v1361 v1362 v1363 v1364 v1365 v1366 v1367 v1368 v1369 v1370 v1371 v1372 v1373 v1374 v1375 v1376 v1377 v1378 v1379 v1380 v1381 v1382 v1383 v1384 v1385 v1386 v1387 v1388 v1389 v1390 v1391 v1392 v1393 v1394 v1395 v1396 v1397 v1398 v1399 v1400 v1401 v1402 v1403 v1404 v1405 v1406 v1407 v1408 v1409 v1410 v1411 v1412 v1413 v1414 v1415 v1416 v1417 v1418 v1419 v1420 v1421 v1422 v1423 v1424 v1425 v1426 v1427 v1428 v1430 v1431 v1432 v1433 v1434 v1435 v1436 v1437 v1438 v1439 v1440 v1441 v1442 v1443 v1444 v1445 v1446 v1447 v1448 v1449 v1450 v1451 v1452 v1453 v1454 v1455 v1456 v1457 v1458 v1459 v1460 v1461 v1462 v1463 v1464 v1465 v1466 v1467 v1468 v1469 v1470 v1471 v1472 v1473 v1474 v1475 v1476 v1477 v1478 v1479 v1480 v1481 v1482 v1483 v1484 v1485 v1486 v1487 v1488 v1489 v1490 v1491 v1492 v1493 v1494 v1495 v1496 v1497 v1498 v1499 v1500 v1501 v1502 v1503 v1504 v1505 v1511 v1512 v1513 v1514 v1515 v1516 v1517 v1518 v1519 v1520 v1521 v1522 v1523 v1524 v1525 v1526 v1527 v1528 v1529 v1530 v1531 v1532 v1533 v1534 v1535 v1536 v1537 v1538 v1539 v1540 v1541 v1542 v1543 v1544 v1546 v1547 v1548 v1549 v1550 v1551 v1552 v1553 v1554 v1555 v1556 v1557 v1564 v1565 v1568 v1569 v1572 v1573 v1576 v1579 v1580 v1581 v1582 v1583 v1584 v1585 v1586 v1587 v1588 v1589 v1590 v1591 v1592 v1593 v1594 v1595 v1596 v1597 v1598 v1599 v1600 v1601 v1602 v1603 v1604 v1605 v1606 v1607 v1608 v1609 v1610 v1611 v1612 v1613 v1614 v1615 v1616 v1617 v1618 v1619 v1620 v1621 v1622 v1623 v1624 v1625 v1626 v1627 v1628 v1629 v1630 v1631 v1633 v1634 v1635 v1636 v1637 v1638 v1639 v1640 v1641 v1642 v1643 v1644 v1645 v1646 v1647 v1648 v1649 v1650 v1651 v1652 v1653 v1654 v1655 v1656 v1657 v1658 v1659 v1660 v1661 v1662 v1663 v1664 v1665 v1669 v1670 v1671 v1672 v1673 v1682 v1683 v1684 v1685 v1686 v1687 v1688 v1689 v1690 v1691 v1692 v1693 v1694 v1695 v1696 v1697 v1698 v1699 v1700 v1701 v1702 v1703 v1704 v1705 v1706 v1707 v1708 v1709 v1711 v1712 v1713 v1714 v1715 v1717 v1718 v1719 v1720 v1721 v1729 v1730 v1731 v1732 v1733 v1734 v1737 v1738 v1741 v1742 v1745 v1746 v1748 v1749 v1751 v1752 v1753 v1754 v1755 v1756 v1757 v1758 v1759 v1760 v1761 v1762 v1763 v1764 v1765 v1766 v1767 v1768 v1769 v1770 v1771 v1772 v1773 v1774 v1775 v1776 v1777 v1778 v1779 v1780 v1781 v1782 v1783 v1784 v1785 v1786 v1787 v1788 v1789 v1790 v1791 v1792 v1793 v1794 v1795 v1796 v1797 v1798 v1799 v1800 v1801 v1802 v1804 v1805 v1806 v1807 v1808 v1809 v1810 v1811 v1812 v1813 v1814 v1815 v1816 v1817 v1818 v1819 v1820 v1821 v1822 v1823 v1824 v1825 v1826 v1827 v1828 v1829 v1830 v1831 v1832 v1833 v1834 v1835 v1836 v1837 v1838 v1839 v1842 v1843 v1844 v1845 v1846 v1847 v1848 v1849 v1850 v1868 v1869 v1870 t1868 v1872 v1873 v1874 v1875 v1876 v1877 v1878 v1879 v1880 v1882 v1883 v1885 v1887 v1889 v1892 v1893 v1894 v1895 v1896 v1897 v1898 v1899 v1900 v1901 v1902 v1903 v1904 v1905 v1906 v1907 v1908 v1909 v1910 v1911 v1912 v1913 v1914 v1915 v1916 v1917 v1918 v1919 v1920 v1921 v1922 v1923 v1924 v1925 v1926 v1927 v1928 v1929 at h
  have hl : 0 < 1 := Nat.one_pos
  have s0 := progF1H_seg0 F0 F1 F2 F3 H0 H1 hb_F0 hb_F1 hb_F2 hb_F3 hb_H0 hb_H1
  extract_lets at s0
  refine s0 _ ?_
  clear s0
  intro e_v0 e_v1 e_v2 e_v3 e_v4 e_v5 e_v6 e_v8 e_v9 e_v10 e_v11 h_v12 e_v12 h_v13 e_v13 h_t0_1 h_t0_2 e_t0_1 e_t0_2 h_t1_1 h_t1_2 e_t1_1 e_t1_2 e_v16 e_v17 e_v18 h_v19 e_v19 e_v20 e_v21 e_v22 e_v23 e_v24 e_v25 e_v26 e_v27 e_v28 e_v29 e_v30 h_v31 e_v31 h_v32 e_v32 h_v33 e_v33 h_v34 e_v34 e_v35 e_v36 h_v37 e_v37 h_t32_1 e_t32_1 e_t32_2 h_t33_1 e_t33_1 e_t33_2 e_v40 e_v41 h_v42 e_v42 e_v43 e_v44 e_v45 e_v46 h_v47 e_v47 e_v48 e_v49 h_v50 e_v50 e_v51 e_v52 h_v53 e_v53 e_v54 e_v55 h_v56 e_v56 h_v57 e_v57 e_v58 e_v60 e_v61 h_v62 e_v62 h_v63 e_v63 e_v64 e_v65 e_v66 e_v67 h_v68 e_v68 e_v69 e_v70 e_v71 e_v72 e_v73 e_v74 e_v75 e_v76 e_v77 e_v78 e_v79 e_v80 e_v81 e_v82 e_v83 e_v84 e_v85 e_v86 e_v87 e_v88 e_v89 e_v90 e_v91 h_v92 e_v92 e_v94 e_v95 e_v96 e_v97 e_v98 e_v99 h_v100 e_v100 e_v102 e_v103 e_v104 e_v105 e_v106 h_v107 e_v107 h_v108 e_v108 e_v109 h_v110 e_v110 e_v112 e_v113 e_v114 e_v115 h_v116 e_v116 e_v134 h_v135 e_v135 e_v136 e_v137 h_v138 e_v138 h_v139 e_v139 h_v176 e_v176 e_v206 e_v213 h_v267 e_v267 e_v268 e_v269 h_v270 e_v270 e_v278 e_v279 e_v280 e_v281 h_v282 e_v282 h_t267_1 e_t267_1 e_v284 e_v285 e_v286 e_v287 e_v288 e_v289 e_v290 e_v291 e_v292 e_v293 e_v294 e_v296 e_v297 e_v298 e_v299 e_v300 e_v301 e_v302 e_v303 e_v304 e_v305 e_v306 e_v307 e_v308 e_v309 e_v310 e_v311 e_v312 e_v313 e_v314 e_v315 e_v316 e_v317 e_v318 e_v319 e_v320 e_v321 e_v322 e_v323 e_v324 e_v325 e_v326 e_v327 e_v328 e_v329 e_v332 e_v333 e_v375 e_v376 e_v377 e_t377_1 e_t377_2 e_v379 e_v380 e_v381 e_v382 e_v383 e_v384 e_v386 e_v387 e_v388 e_v389 e_v390 e_v391 e_v392 e_v393 e_v394 e_v395 e_v396 e_v397 e_v398 e_v399 e_v400 e_v401 e_v402 e_v403 e_v404 e_v405 e_v406 e_v407 e_v408 e_v409 e_v410 e_v411 e_v412 e_v413 e_v414 e_v415 h_v417 e_v417 h_v418 e_v418 e_v419 e_v420 e_v421 h_v422 e_v422 h_v423 e_v423 e_t418_1 h_t419_1 e_t419_1 e_v426 e_v427 e_v428 e_v429 e_v430 e_v431 e_v432 e_v433 h_v434 e_v434 e_v435 e_v436 e_v437 e_v439 e_v440 e_v441 e_v442 e_v443 e_v444 e_v445 e_v446 e_v447 e_v448 e_v449 e_v450 e_v451 e_v452 e_v453 e_v454 e_v455 e_v456 e_v457 e_v458 e_v459 e_v460 e_v461 e_v462 e_v463 e_v464 e_v465 e_v466 e_v467 e_v468 e_v469 e_v470 h_v471 e_v471 e_v472 e_v473 e_v474 h_v475 e_v475 e_v476 e_v477 e_v478 e_v479 e_v480 e_v481 e_v482 h_v483 e_v483 h_v484 e_v484 h_v485 e_v485 e_v486 e_v487 e_v488 e_v489 e_v490 e_v491 e_v492 e_v493 e_v494 e_v495 e_v496 e_v497 e_v498 e_v499 e_v500 e_v501 e_v502 e_v503 e_v504 e_v505 e_v506 e_v508 e_v509 e_v510 e_v511 e_v512 e_v513 e_v514 e_v515 e_v516 e_v517 e_v518 e_v519 e_v520 e_v521 e_v522 e_v523 e_v524 e_v525 e_v526 e_v527 e_v528 e_v529 e_v530 e_v531 e_v532 e_v533 e_v534 e_v535 e_v536 e_v537 e_v538 e_v539 e_v540 e_v541 e_v542 e_v544 e_v545 e_v546 e_v547 e_v548 e_v549 e_v550 e_v551 e_v552 e_v553 e_v554 e_v555 e_v556 e_v557 e_v558 e_v559 e_v560 e_v561 e_v562 e_v563 e_v564 e_v565 e_v566 e_v567 e_v568 e_v569 e_v570 e_v571 e_v572 e_v573 e_v574 e_v575 e_v576 e_v577 e_v578 e_v579 e_v580 e_v581 e_v582 e_v583 h_v584 e_v584 h_v585 e_v585 e_v586 e_v587 h_v588 e_v588 h_v589 e_v589 e_v590 e_v591 e_v592 h_v593 e_v593 e_v599 e_v600 e_v601 e_v602 e_v603 e_v604 e_v605 e_v606 e_v607 e_v608 h_v609 e_v609 e_v610 e_v611 e_v612 e_v613 e_v614 h_v615 e_v615 e_v616 e_v617 e_v618 e_v619 e_v620 e_v621 e_v622 e_v623 e_v624 e_v625 e_v627 e_v628 e_v629 e_v630 e_v631 e_v632 e_v633 e_v634 e_v635 e_v636 e_v637 e_v638 e_v645 e_v646 e_v649 e_v650 e_v653 e_v654 e_v657 h_v660 e_v660 e_v661 e_v662 e_v663 e_v664 e_v665 e_v666 e_v667 e_v668 e_v669 e_v670 e_v671 e_v672 e_v673 e_v674 e_v675 e_v676 e_v677 e_v678 e_v679 e_v680 e_v681 e_v682 e_v683 e_v684 h_v685 e_v685 e_v686 e_v687 e_v688 e_v689 e_v690 e_v691 e_v692 e_v693 h_v694 e_v694 e_v695 e_v696 e_v697 e_v698 e_v699 e_v700 e_v701 e_v702 e_v703 e_v704 h_v705 e_v705 e_v706 e_v707 e_v708 e_v709 e_v710 e_v711 e_v712 e_v713 e_v714 e_v715 h_v716 e_v716 e_v717 h_v718 e_v718 h_v719 e_v719
  have s1 := progF1H_seg1 F0 F1 F2 F3 H0 H1 hb_F0 hb_F1 hb_F2 hb_F3 hb_H0 hb_H1 v12 v13 v19 v31 v32 v33 v34 v37 t32 t33 v42 v47 v50 v53 v56 v57 v62 v63 v68 v100 v107 v108 v116 v135 v138 v139 v176 v267 v282 t267 v417 v418 v422 t419 v434 v475 v483 v484 v584 v585 v588 v589 v609 v615 v660 v685 v694 v705 v716 v718 v719 h_v12 h_v13 h_v19 h_v31 h_v32 h_v33 h_v34 h_v37 h_t32_1 h_t33_1 h_v42 h_v47 h_v50 h_v53 h_v56 h_v57 h_v62 h_v63 h_v68 h_v100 h_v107 h_v108 h_v116 h_v135 h_v138 h_v139 h_v176 h_v267 h_v282 h_t267_1 h_v417 h_v418 h_v422 h_t419_1 h_v434 h_v475 h_v483 h_v484 h_v584 h_v585 h_v588 h_v589 h_v609 h_v615 h_v660 h_v685 h_v694 h_v705 h_v716 h_v718 h_v719
  extract_lets at s1
  refine s1 _ ?_
  clear s1
  intro e_v720 e_v721 e_v722 e_v723 e_v724 e_v725 e_v726 e_v727 e_v728 e_v729 e_v730 e_v731 e_v732 e_v733 e_v735 e_v736 e_v737 e_v738 e_v739 e_v740 e_v741 e_v742 e_v743 e_v744 e_v745 e_v746 e_v747 e_v748 e_v749 e_v750 e_v751 e_v752 e_v753 e_v754 e_v755 e_v756 e_v757 e_v758 e_v759 e_v760 e_v761 e_v762 e_v763 e_v764 e_v765 e_v766 e_v767 e_v768 e_v771 e_v772 e_v773 e_v774 e_v775 e_v776 e_v777 e_v778 e_v779 e_v780 e_v781 e_v782 h_v783 e_v783 e_v789 e_v790 e_v791 e_v792 e_v793 e_v794 e_v795 e_v796 e_v797 e_v798 e_v799 e_v800 e_v801 e_v802 e_v803 e_v804 e_v805 e_v806 e_v807 e_v808 e_v809 e_v811 e_v812 e_v813 e_v814 e_v815 e_v817 e_v818 e_v819 e_v820 e_v821 e_v829 e_v830 e_v831 e_v832 e_v833 e_v834 e_v837 e_v838 e_v841 e_v842 e_v845 e_v846 e_v848 e_v849 e_v851 e_v852 e_v853 e_v854 e_v855 e_v856 e_v857 e_v858 e_v859 e_v860 e_v861 e_v862 e_v863 e_v864 e_v865 e_v866 e_v867 e_v868 e_v869 e_v870 e_v871 e_v872 e_v873 e_v874 e_v875 e_v876 e_v877 e_v878 e_v879 e_v880 e_v881 e_v882 e_v883 e_v884 e_v885 e_v886 e_v887 e_v888 e_v889 e_v890 e_v891 e_v892 e_v893 e_v894 e_v895 e_v896 e_v897 e_v898 e_v899 e_v900 e_v901 e_v902 e_v903 e_v904 e_v905 e_v906 e_v907 e_v908 e_v909 e_v910 e_v911 e_v912 e_v913 e_v914 e_v915 e_v916 e_v917 e_v918 e_v919 e_v920 e_v921 e_v923 e_v924 e_v925 e_v926 e_v927 e_v928 e_v929 e_v930 e_v931 e_v932 e_v933 e_v934 e_v935 e_v936 e_v937 e_v938 e_v939 e_v940 e_v941 e_v942 e_v943 e_v944 e_v945 e_v946 e_v947 e_v948 e_v949 e_v950 e_v951 e_v952 e_v953 e_v954 e_v955 e_v956 e_v957 e_v958 e_v961 e_v962 e_v963 e_v964 e_v965 e_v966 e_v967 e_v968 e_v969 e_v971 e_v972 e_v973 e_t971_1 e_t971_2 e_v975 e_v976 e_v977 e_v978 e_v979 e_v980 e_v981 e_v982 e_v983 e_v984 e_v985 e_v986 e_v987 e_v988 e_v989 e_t987_1 e_t987_2 e_v991 e_v992 e_v993 e_v994 e_v995 e_v996 e_v997 e_v998 e_v999 e_v1000 e_v1001 e_v1002 h_v1005 e_v1005 e_v1007 e_v1008 e_v1009 e_v1010 h_v1012 e_v1012 h_v1013 e_v1013 e_v1014 e_v1015 e_v1016 e_v1017 e_v1018 e_v1019 e_v1020 e_v1027 e_v1028 e_v1031 e_v1032 e_v1035 e_v1036 e_v1039 e_v1041 e_v1042 e_v1043 e_v1044 h_v1045 e_v1045 e_v1046 e_v1047 e_v1048 e_v1049 e_v1050 e_v1051 e_v1052 e_v1053 e_v1054 e_v1055 e_v1056 e_v1057 e_v1058 e_v1059 e_v1061 e_v1062 e_v1064 e_v1065 e_v1066 e_v1067 e_v1068 e_v1069 e_v1070 e_v1071 e_v1072 e_v1073 e_v1074 e_v1075 e_v1076 e_v1077 e_v1078 e_v1079 e_v1080 e_v1081 e_v1082 e_v1083 h_v1084 e_v1084 e_v1085 e_v1086 e_v1087 e_v1088 e_v1089 e_v1090 e_v1091 e_v1092 e_v1093 e_v1094 e_v1095 e_v1096 e_v1097 e_v1098 e_v1099 e_v1100 e_v1101 e_v1102 e_v1103 e_v1104 e_v1105 e_v1106 e_v1107 e_v1108 e_v1109 e_v1110 e_v1111 e_v1112 e_v1113 e_v1114 e_v1115 e_v1116 e_v1117 e_v1118 e_v1130 e_v1131 e_v1132 e_v1135 e_v1136 e_v1137 e_v1138 h_v1139 e_v1139 e_v1140 e_v1141 e_v1142 e_v1143 e_v1144 e_v1145 e_v1146 e_v1147 e_v1148 e_v1149 e_v1150 e_v1151 e_v1152 e_v1154 e_v1155 e_v1156 e_v1157 e_v1158 e_v1159 e_v1160 e_v1161 e_v1162 e_v1163 e_v1164 e_v1165 e_v1166 e_v1167 e_v1168 e_v1169 e_v1170 e_v1171 e_v1172 e_v1173 e_v1174 e_v1175 e_v1176 e_v1177 e_v1178 e_v1179 e_v1180 e_v1181 e_v1182 e_v1183 h_v1184 e_v1184 h_v1185 e_v1185 h_v1186 e_v1186 e_v1187 e_v1188 e_v1189 h_v1190 e_v1190 e_v1341 e_v1342 e_v1343 e_v1344 h_v1345 e_v1345 e_t1343_1 e_v1347 e_v1348 e_v1349 e_v1350 e_v1351 e_v1352 e_v1353 e_v1354 e_v1355 e_v1356 e_v1357 e_v1359 e_v1360 e_v1361 e_v1362 e_v1363 e_v1364 e_v1365 e_v1366 e_v1367 e_v1368 e_v1369 e_v1370 e_v1371 e_v1372 e_v1373 e_v1374 e_v1375 e_v1376 e_v1377 e_v1378 e_v1379 e_v1380 e_v1381 e_v1382 e_v1383 e_v1384 e_v1385 e_v1386 e_v1387 e_v1388 e_v1389 e_v1390 h_v1391 e_v1391 e_v1392 e_v1393 e_v1394 e_v1395 e_v1396 e_v1397 e_v1398 h_v1399 e_v1399 e_v1400 e_v1401 e_v1402 e_v1403 e_v1404 h_v1405 e_v1405 e_v1406 e_v1407 e_v1408 h_v1409 e_v1409 h_v1410 e_v1410 h_v1411 e_v1411 e_v1412 e_v1413 e_v1414 e_v1415 e_v1416 h_v1417 e_v1417 e_v1418 e_v1419 e_v1420 h_v1421 e_v1421 e_v1422 h_v1423 e_v1423 e_v1424 e_v1425 h_v1426 e_v1426 h_v1427 e_v1427 e_v1428 e_v1430 e_v1431 h_v1432 e_v1432 h_v1433 e_v1433
  clear h_v12 h_v19 h_v31 h_v32 h_v33 h_v34 h_t32_1 h_t33_1 h_v42 h_v47 h_v50 h_v53 h_v56 h_v57 h_v62 h_v63 h_v68 h_v108 h_v116 h_v135 h_v176 h_v267 h_v282 h_t267_1 h_v418 h_v422 h_t419_1 h_v434 h_v475 h_v483 h_v484 h_v584 h_v585 h_v588 h_v589 h_v609 h_v615 h_v660 h_v685 h_v694 h_v705 h_v716 h_v718 h_v719
  have s2 := progF1H_seg2 F0 F1 F2 F3 H0 H1 hb_F0 hb_F1 hb_F2 hb_F3 hb_H0 hb_H1 v13 t0 t1 v37 v92 v100 v107 v110 v138 v139 v270 v417 v423 v471 v485 v593 v783 v1005 v1012 v1013 v1045 v1084 v1139 v1184 v1185 v1186 v1190 v1345 v1391 v1399 v1405 v1409 v1410 v1411 v1417 v1421 v1423 v1426 v1427 v1432 v1433 h_v13 h_t0_1 h_t0_2 h_t1_1 h_t1_2 h_v37 h_v92 h_v100 h_v107 h_v110 h_v138 h_v139 h_v270 h_v417 h_v423 h_v471 h_v485 h_v593 h_v783 h_v1005 h_v1012 h_v1013 h_v1045 h_v1084 h_v1139 h_v1184 h_v1185 h_v1186 h_v1190 h_v1345 h_v1391 h_v1399 h_v1405 h_v1409 h_v1410 h_v1411 h_v1417 h_v1421 h_v1423 h_v1426 h_v1427 h_v1432 h_v1433
  extract_lets at s2
  refine s2 _ ?_
  clear s2
  intro e_v1434 e_v1435 e_v1436 e_v1437 e_v1438 e_v1439 e_v1440 e_v1441 e_v1442 e_v1443 e_v1444 e_v1445 e_v1446 e_v1447 e_v1448 e_v1449 e_v1450 e_v1451 e_v1452 e_v1453 e_v1454 e_v1455 e_v1456 e_v1457 e_v1458 e_v1459 e_v1460 e_v1461 e_v1462 e_v1463 e_v1464 e_v1465 e_v1466 e_v1467 e_v1468 e_v1469 e_v1470 e_v1471 e_v1472 e_v1473 e_v1474 e_v1475 e_v1476 e_v1477 e_v1478 e_v1479 e_v1480 e_v1481 e_v1482 e_v1483 e_v1484 e_v1485 e_v1486 e_v1487 e_v1488 e_v1489 e_v1490 e_v1491 e_v1492 e_v1493 e_v1494 e_v1495 e_v1496 e_v1497 e_v1498 e_v1499 e_v1500 e_v1501 e_v1502 e_v1503 e_v1504 e_v1505 e_v1511 e_v1512 e_v1513 e_v1514 e_v1515 e_v1516 e_v1517 e_v1518 e_v1519 e_v1520 e_v1521 e_v1522 e_v1523 e_v1524 e_v1525 e_v1526 e_v1527 e_v1528 e_v1529 e_v1530 e_v1531 e_v1532 e_v1533 e_v1534 e_v1535 e_v1536 e_v1537 e_v1538 e_v1539 e_v1540 e_v1541 e_v1542 e_v1543 e_v1544 e_v1546 e_v1547 e_v1548 e_v1549 e_v1550 e_v1551 e_v1552 e_v1553 e_v1554 e_v1555 e_v1556 e_v1557 e_v1564 e_v1565 e_v1568 e_v1569 e_v1572 e_v1573 e_v1576 e_v1579 e_v1580 e_v1581 e_v1582 e_v1583 e_v1584 e_v1585 e_v1586 e_v1587 e_v1588 e_v1589 e_v1590 e_v1591 e_v1592 e_v1593 e_v1594 e_v1595 e_v1596 e_v1597 e_v1598 e_v1599 e_v1600 e_v1601 e_v1602 e_v1603 e_v1604 e_v1605 e_v1606 e_v1607 e_v1608 e_v1609 e_v1610 e_v1611 e_v1612 e_v1613 e_v1614 e_v1615 e_v1616 e_v1617 e_v1618 e_v1619 e_v1620 e_v1621 e_v1622 e_v1623 e_v1624 e_v1625 e_v1626 e_v1627 e_v1628 e_v1629 e_v1630 e_v1631 e_v1633 e_v1634 e_v1635 e_v1636 e_v1637 e_v1638 e_v1639 e_v1640 e_v1641 e_v1642 e_v1643 e_v1644 e_v1645 e_v1646 e_v1647 e_v1648 e_v1649 e_v1650 e_v1651 e_v1652 e_v1653 e_v1654 e_v1655 e_v1656 e_v1657 e_v1658 e_v1659 e_v1660 e_v1661 e_v1662 e_v1663 e_v1664 e_v1665 e_v1669 e_v1670 e_v1671 e_v1672 e_v1673 e_v1682 e_v1683 e_v1684 e_v1685 e_v1686 e_v1687 e_v1688 e_v1689 e_v1690 e_v1691 e_v1692 e_v1693 e_v1694 e_v1695 e_v1696 e_v1697 e_v1698 e_v1699 e_v1700 e_v1701 e_v1702 e_v1703 e_v1704 e_v1705 e_v1706 e_v1707 e_v1708 e_v1709 e_v1711 e_v1712 e_v1713 e_v1714 e_v1715 e_v1717 e_v1718 e_v1719 e_v1720 e_v1721 e_v1729 e_v1730 e_v1731 e_v1732 e_v1733 e_v1734 e_v1737 e_v1738 e_v1741 e_v1742 e_v1745 e_v1746 e_v1748 e_v1749 e_v1751 e_v1752 e_v1753 e_v1754 e_v1755 e_v1756 e_v1757 e_v1758 e_v1759 e_v1760 e_v1761 e_v1762 e_v1763 e_v1764 e_v1765 e_v1766 e_v1767 e_v1768 e_v1769 e_v1770 e_v1771 e_v1772 e_v1773 e_v1774 e_v1775 e_v1776 e_v1777 e_v1778 e_v1779 e_v1780 e_v1781 e_v1782 e_v1783 e_v1784 e_v1785 e_v1786 e_v1787 e_v1788 e_v1789 e_v1790 e_v1791 e_v1792 e_v1793 e_v1794 e_v1795 e_v1796 e_v1797 e_v1798 e_v1799 e_v1800 e_v1801 e_v1802 e_v1804 e_v1805 e_v1806 e_v1807 e_v1808 e_v1809 e_v1810 e_v1811 e_v1812 e_v1813 e_v1814 e_v1815 e_v1816 e_v1817 e_v1818 e_v1819 e_v1820 e_v1821 e_v1822 e_v1823 e_v1824 e_v1825 e_v1826 e_v1827 e_v1828 e_v1829 e_v1830 e_v1831 e_v1832 e_v1833 e_v1834 e_v1835 e_v1836 e_v1837 e_v1838 e_v1839 e_v1842 e_v1843 e_v1844 e_v1845 e_v1846 e_v1847 e_v1848 e_v1849 e_v1850 e_v1868 e_v1869 e_v1870 e_t1868_2 e_v1872 e_v1873 e_v1874 e_v1875 e_v1876 e_v1877 e_v1878 e_v1879 e_v1880 e_v1882 e_v1883 e_v1885 e_v1887 e_v1889 e_v1892 e_v1893 e_v1894 e_v1895 e_v1896 e_v1897 e_v1898 e_v1899 e_v1900 e_v1901 e_v1902 e_v1903 e_v1904 e_v1905 e_v1906 e_v1907 e_v1908 e_v1909 e_v1910 e_v1911 e_v1912 e_v1913 e_v1914 e_v1915 e_v1916 e_v1917 e_v1918 e_v1919 e_v1920 e_v1921 e_v1922 e_v1923 e_v1924 e_v1925 e_v1926 e_v1927 e_v1928 e_v1929
  clear h_v13 h_t0_1 h_t0_2 h_t1_1 h_t1_2 h_v37 h_v92 h_v100 h_v107 h_v110 h_v138 h_v139 h_v270 h_v417 h_v423 h_v471 h_v485 h_v593 h_v783 h_v1005 h_v1012 h_v1013 h_v1045 h_v1084 h_v1139 h_v1184 h_v1185 h_v1186 h_v1190 h_v1345 h_v1391 h_v1399 h_v1405 h_v1409 h_v1410 h_v1411 h_v1417 h_v1421 h_v1423 h_v1426 h_v1427 h_v1432 h_v1433
  have k_v1929 : v1929 = 1 := h
  have k_v1893 : v1893 = 1 := ((e_v1929).1 k_v1929).1
  have k_v1928 : v1928 = 1 := ((e_v1929).1 k_v1929).2
  have k_v1696 : v1696 = 1 := ((e_v1928).1 k_v1928).1
  have k_v1927 : v1927 = 1 := ((e_v1928).1 k_v1928).2
  have k_v1926 : v1926 = 1 := ((e_v1927).1 k_v1927).2
  have k_v1525 : v1525 = 1 := ((e_v1926).1 k_v1926).1
  have k_v1925 : v1925 = 1 := ((e_v1926).1 k_v1926).2
  have k_v1924 : v1924 = 1 := ((e_v1925).1 k_v1925).2
  have k_v1411 : v1411 = 1 := ((e_v1924).1 k_v1924).1
  have k_v1923 : v1923 = 1 := ((e_v1924).1 k_v1924).2
  have k_v1391 : v1391 = 1 := ((e_v1923).1 k_v1923).1
  have k_v1922 : v1922 = 1 := ((e_v1923).1 k_v1923).2
  have k_v1345 : v1345 = 1 := ((e_v1922).1 k_v1922).1
  have k_v1921 : v1921 = 1 := ((e_v1922).1 k_v1922).2
  have k_v13 : v13 = 1 := ((e_v1921).1 k_v1921).1
  have k_v1920 : v1920 = 1 := ((e_v1921).1 k_v1921).2
  have k_v270 : v270 = 1 := ((e_v1920).1 k_v1920).1
  have k_v1919 : v1919 = 1 := ((e_v1920).1 k_v1920).2
  have k_v1918 : v1918 = 1 := ((e_v1919).1 k_v1919).2
  have k_v1190 : v1190 = 1 := ((e_v1918).1 k_v1918).1
  have k_v1917 : v1917 = 1 := ((e_v1918).1 k_v1918).2
  have k_v1916 : v1916 = 1 := ((e_v1917).1 k_v1917).2
  have k_v1915 : v1915 = 1 := ((e_v1916).1 k_v1916).2
  have k_v1186 : v1186 = 1 := ((e_v1915).1 k_v1915).1
  have k_v1914 : v1914 = 1 := ((e_v1915).1 k_v1915).2
  have k_v1139 : v1139 = 1 := ((e_v1914).1 k_v1914).1
  have k_v1913 : v1913 = 1 := ((e_v1914).1 k_v1914).2
  have k_v1912 : v1912 = 1 := ((e_v1913).1 k_v1913).2
  have k_v1084 : v1084 = 1 := ((e_v1912).1 k_v1912).1
  have k_v1911 : v1911 = 1 := ((e_v1912).1 k_v1912).2
  have k_v1045 : v1045 = 1 := ((e_v1911).1 k_v1911).1
  have k_v1910 : v1910 = 1 := ((e_v1911).1 k_v1911).2
  have k_v1909 : v1909 = 1 := ((e_v1910).1 k_v1910).2
  have k_v1013 : v1013 = 1 := ((e_v1909).1 k_v1909).1
  have k_v1908 : v1908 = 1 := ((e_v1909).1 k_v1909).2
  have k_v1012 : v1012 = 1 := ((e_v1908).1 k_v1908).1
  have k_v1907 : v1907 = 1 := ((e_v1908).1 k_v1908).2
  have k_v1005 : v1005 = 1 := ((e_v1907).1 k_v1907).1
  have k_v1906 : v1906 = 1 := ((e_v1907).1 k_v1907).2
  have k_v783 : v783 = 1 := ((e_v1906).1 k_v1906).1
  have k_v1905 : v1905 = 1 := ((e_v1906).1 k_v1906).2
  have k_v593 : v593 = 1 := ((e_v1905).1 k_v1905).1
  have k_v1904 : v1904 = 1 := ((e_v1905).1 k_v1905).2
  have k_v485 : v485 = 1 := ((e_v1904).1 k_v1904).1
  have k_v1903 : v1903 = 1 := ((e_v1904).1 k_v1904).2
  have k_v471 : v471 = 1 := ((e_v1903).1 k_v1903).1
  have k_v1902 : v1902 = 1 := ((e_v1903).1 k_v1903).2
  have k_v423 : v423 = 1 := ((e_v1902).1 k_v1902).1
  have k_v1901 : v1901 = 1 := ((e_v1902).1 k_v1902).2
  have k_v1900 : v1900 = 1 := ((e_v1901).1 k_v1901).2
  have k_v1899 : v1899 = 1 := ((e_v1900).1 k_v1900).2
  have k_v1898 : v1898 = 1 := ((e_v1899).1 k_v1899).2
  have k_v110 : v110 = 1 := ((e_v1898).1 k_v1898).1
  have k_v1897 : v1897 = 1 := ((e_v1898).1 k_v1898).2
  have k_v1896 : v1896 = 1 := ((e_v1897).1 k_v1897).2
  have k_v1895 : v1895 = 1 := ((e_v1896).1 k_v1896).2
  have k_v92 : v92 = 1 := ((e_v1895).1 k_v1895).1
  have k_v1894 : v1894 = 1 := ((e_v1895).1 k_v1895).2
  have k_v37 : v37 = 1 := ((e_v1894).1 k_v1894).2
  have k_v34 : v34 = 1 := ((e_v37).1 k_v37).1
  have k_v36 : v36 = 1 := ((e_v37).1 k_v37).2
  have k_v109 : v109 = 1 := ((e_v110).1 k_v110).2
  have k_v420 : v420 = 1 := ((e_v423).1 k_v423).1
  have k_v422 : v422 = 1 := ((e_v423).1 k_v423).2
  have k_v1138 : v1138 = 1 := ((e_v1139).1 k_v1139).2
  have k_v1189 : v1189 = 1 := ((e_v1190).1 k_v1190).2
  have k_v269 : v269 = 1 := ((e_v270).1 k_v270).2
  have k_v9 : v9 = 1 := ((e_v13).1 k_v13).1
  have k_v12 : v12 = 1 := ((e_v13).1 k_v13).2
  have k_v1344 : v1344 = 1 := ((e_v1345).1 k_v1345).2
  have f3 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f2 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v17) (sv v19) (sv v20) (sv v22) (sv v23) (sv v25) v27 v29 v30 (sv v31) f3 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v16 (L2.p_sel e_v17)) (L2.p_addc (-4) e_v19 e_v18) (L2.p_max e_v16 (L2.p_sel e_v20)) (L2.p_addc (4) e_v22 e_v21) e_v23 (L2.p_min e_v24 (L2.p_sel e_v25)) (L2.p_ltc (421657430) e_v26 e_v27) (L2.p_clt (421657427) e_v28 e_v29) e_v30 (L2.p_sel e_v31)
  have f39 := L2.K5_ihalf (sv v2) (sv v3) (sv v32) (sv v33) e_v32 e_v33
  have f43 := L2.K8_in_range True (sv v32) (sv v33) v34 (sv v10) v36 v37 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v35 e_v36) e_v37 (L2.X1_top _ k_v37)
  have f42 := L2.K9_isin True (sv v32) (sv v33) (sv t32.1) (sv t33.1) (sv v41) (sv v42) (sv v43) (sv v44) (sv v23) (sv v46) v47 v48 v49 (sv v50) f43 (L2.p_sin e_t32_1) (L2.p_sin e_t33_1) (L2.p_min e_v40 (L2.p_sel e_v41)) (L2.p_addc (-4) (L2.p_add_comm e_v42) e_v18) (L2.p_max e_v40 (L2.p_sel e_v43)) (L2.p_addc (4) (L2.p_add_comm e_v44) e_v21) e_v23 (L2.p_min e_v45 (L2.p_sel e_v46)) (L2.p_ltc (421657430) e_v26 e_v47) (L2.p_clt (421657427) e_v28 e_v48) e_v49 (L2.p_sel e_v50)
  let u59 : ℕ := if v58 = 1 then 0 else 1
  have f79 := L2.K7_imul_full True (sv v19) (sv v31) (sv v42) (sv v50) (sv v51) v52 v53 v54 v55 v56 v57 v58 u59 v60 v61 v62 v63 v64 v65 v66 (sv v67) v68 v69 v70 (sv v71) v72 v73 (sv v74) v75 v76 (sv v77) (sv v79) (sv v81) (sv v83) (sv v85) (sv v87) (sv v89) (sv v90) (sv v91) e_v51 e_v52 e_v53 e_v54 e_v55 (L2.p_and_comm e_v56) e_v57 e_v58 (L2.p_unot _) e_v60 e_v61 (L2.p_and_comm e_v62) e_v63 e_v64 e_v65 e_v66 (L2.p_sel e_v67) e_v68 e_v69 e_v70 (L2.p_sel e_v71) e_v72 e_v73 (L2.p_sel e_v74) e_v75 e_v76 (L2.p_sel e_v77) (L2.p_mul (L2.p_mul_comm e_v78) e_v79) (L2.p_mulc (L2.p_mul_comm e_v80) e_v81) (L2.p_mul (L2.p_mul_comm e_v82) e_v83) (L2.p_mulc (L2.p_mul_comm e_v84) e_v85) (L2.p_min e_v86 (L2.p_sel e_v87)) (L2.p_max e_v88 (L2.p_sel e_v89)) (L2.p_sel e_v90) (L2.p_sel e_v91)
  have f1 := L2.K14_iso_base_a True (sv v2) (sv v3) (sv v0) (sv v1) (sv v19) (sv v31) (sv v32) (sv v33) (sv v42) (sv v50) (sv v90) (sv v91) v92 f2 f39 f42 f79 (L2.p_clt (-1) e_v8 e_v92) (L2.X1_top _ k_v92)
  have f129 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f139 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v94) (sv v95) (sv v97) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v94) e_v18) e_v95 (L2.p_max e_v96 (L2.p_sel e_v97))
  have f153 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v102) (sv v23) (sv v104) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v102) e_v21) e_v23 (L2.p_min e_v103 (L2.p_sel e_v104))
  have f128 := L2.K10_icos True (sv v0) (sv v1) (sv v97) (sv v95) v99 (sv v100) (sv v104) (sv v23) v106 (sv v107) f129 f139 e_v95 (L2.p_clt (843314855) e_v98 e_v99) (L2.p_sel e_v100) f153 e_v23 (L2.p_ltc (1) e_v105 e_v106) (L2.p_sel e_v107)
  have f168 := L2.K5_ihalf (sv v3) (sv v3) (sv v108) (sv v33) e_v108 e_v33
  have f172 := L2.K8_in_range True (sv v108) (sv v33) v109 (sv v10) v36 v110 (L2.p_clt (-1) e_v8 e_v109) e_v10 (L2.p_le e_v35 e_v36) (L2.p_and_comm e_v110) (L2.X1_top _ k_v110)
  have f182 := L2.K3_cos_lo (sv v33) (sv t33.2) (sv v112) (sv v95) (sv v114) (L2.p_cos e_t33_2) (L2.p_addc (-4) (L2.p_add_comm e_v112) e_v18) e_v95 (L2.p_max e_v113 (L2.p_sel e_v114))
  let u117 : ℤ := L2.cosI (sv v108)
  let u118 : ℤ := (sv v21) + u117
  let u119 : ℕ := if u118 < (sv v23) then 1 else 0
  let u120 : ℤ := if u119 = 1 then u118 else (sv v23)
  have f196 := L2.K3_cos_hi (sv v108) u117 u118 (sv v23) u120 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u121 : ℕ := if (sv v108) < (sv v105) then 1 else 0
  let u122 : ℤ := if u121 = 1 then (sv v23) else u120
  have f171 := L2.K10_icos True (sv v108) (sv v33) (sv v114) (sv v95) v115 (sv v116) u120 (sv v23) u121 u122 f172 f182 e_v95 (L2.p_clt (843314855) e_v98 e_v115) (L2.p_sel e_v116) f196 e_v23 (L2.p_ltc (1) e_v105 (L2.p_ult _ _)) rfl
  have f211 := L2.K8_in_range True (sv v108) (sv v33) v109 (sv v10) v36 v110 (L2.p_clt (-1) e_v8 e_v109) e_v10 (L2.p_le e_v35 e_v36) (L2.p_and_comm e_v110) (L2.X1_top _ k_v110)
  let u123 : ℤ := L2.sinI (sv v108)
  let u124 : ℕ := if u123 < (sv t33.1) then 1 else 0
  let u125 : ℤ := if u124 = 1 then u123 else (sv t33.1)
  let u126 : ℤ := (sv v18) + u125
  let u127 : ℤ := if u124 = 1 then (sv t33.1) else u123
  let u128 : ℤ := (sv v21) + u127
  let u129 : ℕ := if u128 < (sv v23) then 1 else 0
  let u130 : ℤ := if u129 = 1 then u128 else (sv v23)
  let u131 : ℕ := if (sv v108) < (sv v26) then 1 else 0
  let u132 : ℕ := if v48 = 1 ∧ u131 = 1 then 1 else 0
  let u133 : ℤ := if u132 = 1 then (sv v23) else u130
  have f210 := L2.K9_isin True (sv v108) (sv v33) u123 (sv t33.1) u125 u126 u127 u128 (sv v23) u130 u131 v48 u132 u133 f211 rfl (L2.p_sin e_t33_1) (L2.p_min (L2.p_ult _ _) rfl) (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) (L2.p_max (L2.p_ult _ _) rfl) (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl) (L2.p_ltc (421657430) e_v26 (L2.p_ult _ _)) (L2.p_clt (421657427) e_v28 e_v48) (L2.p_and_comm (L2.p_uand _ _)) rfl
  let u140 : ℕ := if u126 < (sv v51) then 1 else 0
  let u141 : ℕ := if u140 = 1 then 0 else 1
  let u142 : ℕ := if (sv v51) < u133 then 1 else 0
  let u143 : ℕ := if u142 = 1 then 0 else 1
  let u144 : ℕ := if u140 = 1 ∧ u143 = 1 then 1 else 0
  let u145 : ℕ := if u140 = 1 ∧ u142 = 1 then 1 else 0
  let u146 : ℕ := if v139 = 1 ∧ u145 = 1 then 1 else 0
  let u147 : ℕ := if v135 = 1 ∧ u145 = 1 then 1 else 0
  let u148 : ℕ := if u144 = 1 ∨ u147 = 1 then 1 else 0
  let u149 : ℤ := if u148 = 1 then (sv v107) else (sv v100)
  let u150 : ℕ := if u144 = 1 then 0 else 1
  let u151 : ℕ := if v139 = 1 ∧ u150 = 1 then 1 else 0
  let u152 : ℕ := if v138 = 1 ∨ u151 = 1 then 1 else 0
  let u153 : ℤ := if u152 = 1 then u133 else u126
  let u154 : ℕ := if v138 = 1 ∧ u145 = 1 then 1 else 0
  let u155 : ℕ := if u144 = 1 ∨ u154 = 1 then 1 else 0
  let u156 : ℤ := if u155 = 1 then (sv v100) else (sv v107)
  let u157 : ℕ := if v139 = 1 ∧ u144 = 1 then 1 else 0
  let u158 : ℕ := if v138 = 1 ∨ u157 = 1 then 1 else 0
  let u159 : ℤ := if u158 = 1 then u126 else u133
  let u160 : ℤ := u149 * u153
  let u161 : ℤ := u160 / 2 ^ 28
  let u162 : ℤ := u156 * u159
  let u163 : ℤ := -((-u162) / 2 ^ 28)
  let u164 : ℤ := (sv v107) * u126
  let u165 : ℤ := u164 / 2 ^ 28
  let u166 : ℤ := (sv v100) * u126
  let u167 : ℤ := -((-u166) / 2 ^ 28)
  let u168 : ℕ := if u161 < u165 then 1 else 0
  let u169 : ℤ := if u168 = 1 then u161 else u165
  let u170 : ℕ := if u163 < u167 then 1 else 0
  let u171 : ℤ := if u170 = 1 then u167 else u163
  let u172 : ℤ := if u146 = 1 then u169 else u161
  let u173 : ℤ := if u146 = 1 then u171 else u163
  have f247 := L2.K7_imul_full True (sv v100) (sv v107) u126 u133 (sv v51) v134 v135 v136 v137 v138 v139 u140 u141 u142 u143 u144 u145 u146 u147 u148 u149 u150 u151 u152 u153 u154 u155 u156 u157 u158 u159 u161 u163 u165 u167 u169 u171 u172 u173 e_v51 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 (L2.p_ult _ _) (L2.p_unot _) (L2.p_ult _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uand _ _) (L2.p_uand _ _) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_unot _) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl) (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl) (L2.p_min (L2.p_ult _ _) rfl) (L2.p_max (L2.p_ult _ _) rfl) rfl rfl
  let u174 : ℕ := if (sv v51) < u172 then 1 else 0
  let u175 : ℕ := if u174 = 1 then 0 else 1
  let u177 : ℤ := if v176 = 1 then u172 else u173
  let u178 : ℕ := if u122 < (sv v51) then 1 else 0
  let u179 : ℤ := if u178 = 1 then u173 else u172
  have f291 := L2.K11_qdiv (sv v116) u122 u172 u173 u174 u175 (sv v51) v176 u177 u178 u179 (L2.p_clt (0) e_v51 (L2.p_ult _ _)) (L2.p_unot _) e_v51 e_v176 rfl (L2.p_ult _ _) rfl
  let u180 : ℤ := (sv v51) - (sv v116)
  let u181 : ℤ := if v176 = 1 then u180 else (sv v116)
  let u182 : ℤ := 0
  let u183 : ℕ := if v176 = 1 then 0 else 1
  let u184 : ℤ := L2.cosI u182
  let u185 : ℤ := (sv v18) + u184
  let u186 : ℕ := if u185 < (sv v95) then 1 else 0
  let u187 : ℤ := if u186 = 1 then (sv v95) else u185
  have f309 := L2.K3_cos_lo u182 u184 u185 (sv v95) u187 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u188 : ℤ := (sv v21) + u184
  let u189 : ℕ := if u188 < (sv v23) then 1 else 0
  let u190 : ℤ := if u189 = 1 then u188 else (sv v23)
  have f318 := L2.K3_cos_hi u182 u184 u188 (sv v23) u190 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u191 : ℤ := L2.sinI u182
  let u192 : ℤ := (sv v21) + u191
  let u193 : ℕ := if u192 < (sv v23) then 1 else 0
  let u194 : ℤ := if u193 = 1 then u192 else (sv v23)
  have f327 := L2.K3_sin_hi u182 u191 u192 (sv v23) u194 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u195 : ℤ := (sv v18) + u191
  have f336 := L2.K3_sin_lo u182 u191 u195 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u196 : ℤ := if u183 = 1 then u187 else u190
  let u197 : ℤ := if u183 = 1 then u194 else u195
  let u198 : ℤ := u177 * u197
  let u199 : ℤ := u181 * u196
  let u200 : ℕ := if u199 < u198 then 1 else 0
  let u201 : ℕ := if u200 = 1 then 0 else 1
  let u202 : ℕ := if u198 < u199 then 1 else 0
  let u203 : ℕ := if u202 = 1 then 0 else 1
  let u204 : ℕ := if (sv v51) < u182 then 1 else 0
  let u205 : ℕ := if u204 = 1 then 0 else 1
  let u207 : ℕ := if (sv v206) < u182 then 1 else 0
  let u208 : ℕ := if u207 = 1 then 0 else 1
  let u209 : ℕ := if (sv v8) < u187 then 1 else 0
  let u210 : ℕ := if u201 = 1 ∧ u209 = 1 then 1 else 0
  let u211 : ℕ := if u208 = 1 ∧ u210 = 1 then 1 else 0
  let u212 : ℕ := if u205 = 1 ∨ u211 = 1 then 1 else 0
  let u214 : ℕ := if u182 < (sv v213) then 1 else 0
  let u215 : ℕ := if u214 = 1 then 0 else 1
  let u216 : ℕ := if u203 = 1 ∨ u215 = 1 then 1 else 0
  let u217 : ℕ := if u183 = 1 ∧ u212 = 1 then 1 else 0
  let u218 : ℕ := if v176 = 1 ∧ u216 = 1 then 1 else 0
  let u219 : ℕ := if u217 = 1 ∨ u218 = 1 then 1 else 0
  let u220 : ℤ := (sv v51) - u182
  let u221 : ℤ := if v176 = 1 then u220 else u182
  let u222 : ℤ := -421657429
  let u223 : ℤ := if u219 = 1 then u221 else u222
  have f302 := L2.K12_atan_lo (sv v116) u177 (sv v51) v176 u180 u181 u182 u183 u187 u190 u194 u195 u196 u197 u198 u199 u201 u203 u204 u205 (sv v206) u208 u209 u210 u211 u212 (sv v213) u215 u216 u217 v176 u218 u219 u220 u221 u222 u223 e_v51 e_v176 rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f309 f318 f327 f336 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v206 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v213 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  let u224 : ℤ := (sv v51) - u122
  let u225 : ℤ := if u178 = 1 then u224 else u122
  let u226 : ℤ := 0
  let u227 : ℤ := L2.cosI u226
  let u228 : ℤ := (sv v18) + u227
  let u229 : ℕ := if u228 < (sv v95) then 1 else 0
  let u230 : ℤ := if u229 = 1 then (sv v95) else u228
  have f382 := L2.K3_cos_lo u226 u227 u228 (sv v95) u230 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u231 : ℤ := (sv v21) + u227
  let u232 : ℕ := if u231 < (sv v23) then 1 else 0
  let u233 : ℤ := if u232 = 1 then u231 else (sv v23)
  have f391 := L2.K3_cos_hi u226 u227 u231 (sv v23) u233 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u234 : ℤ := L2.sinI u226
  let u235 : ℤ := (sv v21) + u234
  let u236 : ℕ := if u235 < (sv v23) then 1 else 0
  let u237 : ℤ := if u236 = 1 then u235 else (sv v23)
  have f400 := L2.K3_sin_hi u226 u234 u235 (sv v23) u237 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u238 : ℤ := (sv v18) + u234
  have f409 := L2.K3_sin_lo u226 u234 u238 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u239 : ℤ := if u178 = 1 then u230 else u233
  let u240 : ℤ := if u178 = 1 then u237 else u238
  let u241 : ℤ := u179 * u240
  let u242 : ℤ := u225 * u239
  let u243 : ℕ := if u242 < u241 then 1 else 0
  let u244 : ℕ := if u243 = 1 then 0 else 1
  let u245 : ℕ := if u241 < u242 then 1 else 0
  let u246 : ℕ := if u245 = 1 then 0 else 1
  let u247 : ℕ := if (sv v51) < u226 then 1 else 0
  let u248 : ℕ := if u247 = 1 then 0 else 1
  let u249 : ℕ := if (sv v206) < u226 then 1 else 0
  let u250 : ℕ := if u249 = 1 then 0 else 1
  let u251 : ℕ := if (sv v8) < u230 then 1 else 0
  let u252 : ℕ := if u244 = 1 ∧ u251 = 1 then 1 else 0
  let u253 : ℕ := if u250 = 1 ∧ u252 = 1 then 1 else 0
  let u254 : ℕ := if u248 = 1 ∨ u253 = 1 then 1 else 0
  let u255 : ℕ := if u226 < (sv v213) then 1 else 0
  let u256 : ℕ := if u255 = 1 then 0 else 1
  let u257 : ℕ := if u246 = 1 ∨ u256 = 1 then 1 else 0
  let u258 : ℕ := if u178 = 1 ∧ u254 = 1 then 1 else 0
  let u259 : ℕ := if u178 = 1 then 0 else 1
  let u260 : ℕ := if u257 = 1 ∧ u259 = 1 then 1 else 0
  let u261 : ℕ := if u258 = 1 ∨ u260 = 1 then 1 else 0
  let u262 : ℤ := (sv v51) - u226
  let u263 : ℤ := if u178 = 1 then u262 else u226
  let u264 : ℤ := if u261 = 1 then u263 else (sv v213)
  have f376 := L2.K12_atan_hi u122 u179 (sv v51) u178 u224 u225 u226 u230 u233 u237 u238 u239 u240 u241 u242 u244 u246 u247 u248 (sv v206) u250 u251 u252 u253 u254 (sv v213) u256 u257 u258 u259 u260 u261 u262 u263 (sv v213) u264 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f382 f391 f400 f409 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v206 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v213 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v213 rfl
  let u265 : ℤ := if u175 = 1 then u222 else u223
  let u266 : ℤ := if u175 = 1 then (sv v213) else u264
  have f167 := L2.K19_iso_angle_pt True (sv v3) (sv v100) (sv v107) (sv v108) (sv v33) (sv v116) u122 u126 u133 u172 u173 u177 u179 u175 u174 u223 u264 u222 (sv v213) u265 u266 f168 f171 f210 f247 f291 (L2.p_not_not (L2.p_unot _)) f302 f376 rfl e_v213 rfl rfl
  have f454 := L2.K5_ihalf (sv v2) (sv v2) (sv v32) (sv v267) e_v32 e_v267
  have f458 := L2.K8_in_range True (sv v32) (sv v267) v34 (sv v10) v269 v270 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v268 e_v269) e_v270 (L2.X1_top _ k_v270)
  let u271 : ℤ := L2.cosI (sv v267)
  let u272 : ℤ := (sv v18) + u271
  let u273 : ℕ := if u272 < (sv v95) then 1 else 0
  let u274 : ℤ := if u273 = 1 then (sv v95) else u272
  have f468 := L2.K3_cos_lo (sv v267) u271 u272 (sv v95) u274 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u275 : ℕ := if (sv v98) < (sv v267) then 1 else 0
  let u276 : ℤ := if u275 = 1 then (sv v95) else u274
  have f482 := L2.K3_cos_hi (sv v32) (sv t32.2) (sv v278) (sv v23) (sv v280) (L2.p_cos e_t32_2) (L2.p_addc (4) (L2.p_add_comm e_v278) e_v21) e_v23 (L2.p_min e_v279 (L2.p_sel e_v280))
  have f457 := L2.K10_icos True (sv v32) (sv v267) u274 (sv v95) u275 u276 (sv v280) (sv v23) v281 (sv v282) f458 f468 e_v95 (L2.p_clt (843314855) e_v98 (L2.p_ult _ _)) rfl f482 e_v23 (L2.p_ltc (1) e_v105 e_v281) (L2.p_sel e_v282)
  have f497 := L2.K8_in_range True (sv v32) (sv v267) v34 (sv v10) v269 v270 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v268 e_v269) e_v270 (L2.X1_top _ k_v270)
  have f496 := L2.K9_isin True (sv v32) (sv v267) (sv t32.1) (sv t267.1) (sv v285) (sv v286) (sv v287) (sv v288) (sv v23) (sv v290) v47 v291 v292 (sv v293) f497 (L2.p_sin e_t32_1) (L2.p_sin e_t267_1) (L2.p_min e_v284 (L2.p_sel e_v285)) (L2.p_addc (-4) (L2.p_add_comm e_v286) e_v18) (L2.p_max e_v284 (L2.p_sel e_v287)) (L2.p_addc (4) (L2.p_add_comm e_v288) e_v21) e_v23 (L2.p_min e_v289 (L2.p_sel e_v290)) (L2.p_ltc (421657430) e_v26 e_v47) (L2.p_clt (421657427) e_v28 e_v291) e_v292 (L2.p_sel e_v293)
  let u295 : ℕ := if v294 = 1 then 0 else 1
  have f533 := L2.K7_imul_full True (sv v100) (sv v107) (sv v286) (sv v293) (sv v51) v134 v135 v136 v137 v138 v139 v294 u295 v296 v297 v298 v299 v300 v301 v302 (sv v303) v304 v305 v306 (sv v307) v308 v309 (sv v310) v311 v312 (sv v313) (sv v315) (sv v317) (sv v319) (sv v321) (sv v323) (sv v325) (sv v326) (sv v327) e_v51 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 e_v294 (L2.p_unot _) e_v296 e_v297 (L2.p_and_comm e_v298) e_v299 e_v300 e_v301 e_v302 (L2.p_sel e_v303) e_v304 e_v305 e_v306 (L2.p_sel e_v307) e_v308 e_v309 (L2.p_sel e_v310) e_v311 e_v312 (L2.p_sel e_v313) (L2.p_mul (L2.p_mul_comm e_v314) e_v315) (L2.p_mulc (L2.p_mul_comm e_v316) e_v317) (L2.p_mul (L2.p_mul_comm e_v318) e_v319) (L2.p_mulc (L2.p_mul_comm e_v320) e_v321) (L2.p_min e_v322 (L2.p_sel e_v323)) (L2.p_max e_v324 (L2.p_sel e_v325)) (L2.p_sel e_v326) (L2.p_sel e_v327)
  let u330 : ℕ := if u276 < (sv v51) then 1 else 0
  let u331 : ℤ := if u330 = 1 then (sv v326) else (sv v327)
  have f577 := L2.K11_qdiv u276 (sv v282) (sv v326) (sv v327) v328 v329 (sv v51) u330 u331 v332 (sv v333) (L2.p_clt (0) e_v51 e_v328) e_v329 e_v51 (L2.p_ult _ _) rfl e_v332 (L2.p_sel e_v333)
  let u334 : ℤ := (sv v51) - u276
  let u335 : ℤ := if u330 = 1 then u334 else u276
  let u336 : ℤ := 0
  let u337 : ℕ := if u330 = 1 then 0 else 1
  let u338 : ℤ := L2.cosI u336
  let u339 : ℤ := (sv v18) + u338
  let u340 : ℕ := if u339 < (sv v95) then 1 else 0
  let u341 : ℤ := if u340 = 1 then (sv v95) else u339
  have f595 := L2.K3_cos_lo u336 u338 u339 (sv v95) u341 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u342 : ℤ := (sv v21) + u338
  let u343 : ℕ := if u342 < (sv v23) then 1 else 0
  let u344 : ℤ := if u343 = 1 then u342 else (sv v23)
  have f604 := L2.K3_cos_hi u336 u338 u342 (sv v23) u344 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u345 : ℤ := L2.sinI u336
  let u346 : ℤ := (sv v21) + u345
  let u347 : ℕ := if u346 < (sv v23) then 1 else 0
  let u348 : ℤ := if u347 = 1 then u346 else (sv v23)
  have f613 := L2.K3_sin_hi u336 u345 u346 (sv v23) u348 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u349 : ℤ := (sv v18) + u345
  have f622 := L2.K3_sin_lo u336 u345 u349 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u350 : ℤ := if u337 = 1 then u341 else u344
  let u351 : ℤ := if u337 = 1 then u348 else u349
  let u352 : ℤ := u331 * u351
  let u353 : ℤ := u335 * u350
  let u354 : ℕ := if u353 < u352 then 1 else 0
  let u355 : ℕ := if u354 = 1 then 0 else 1
  let u356 : ℕ := if u352 < u353 then 1 else 0
  let u357 : ℕ := if u356 = 1 then 0 else 1
  let u358 : ℕ := if (sv v51) < u336 then 1 else 0
  let u359 : ℕ := if u358 = 1 then 0 else 1
  let u360 : ℕ := if (sv v206) < u336 then 1 else 0
  let u361 : ℕ := if u360 = 1 then 0 else 1
  let u362 : ℕ := if (sv v8) < u341 then 1 else 0
  let u363 : ℕ := if u355 = 1 ∧ u362 = 1 then 1 else 0
  let u364 : ℕ := if u361 = 1 ∧ u363 = 1 then 1 else 0
  let u365 : ℕ := if u359 = 1 ∨ u364 = 1 then 1 else 0
  let u366 : ℕ := if u336 < (sv v213) then 1 else 0
  let u367 : ℕ := if u366 = 1 then 0 else 1
  let u368 : ℕ := if u357 = 1 ∨ u367 = 1 then 1 else 0
  let u369 : ℕ := if u337 = 1 ∧ u365 = 1 then 1 else 0
  let u370 : ℕ := if u330 = 1 ∧ u368 = 1 then 1 else 0
  let u371 : ℕ := if u369 = 1 ∨ u370 = 1 then 1 else 0
  let u372 : ℤ := (sv v51) - u336
  let u373 : ℤ := if u330 = 1 then u372 else u336
  let u374 : ℤ := if u371 = 1 then u373 else u222
  have f588 := L2.K12_atan_lo u276 u331 (sv v51) u330 u334 u335 u336 u337 u341 u344 u348 u349 u350 u351 u352 u353 u355 u357 u358 u359 (sv v206) u361 u362 u363 u364 u365 (sv v213) u367 u368 u369 u330 u370 u371 u372 u373 u222 u374 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f595 f604 f613 f622 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v206 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v213 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  have f668 := L2.K3_cos_lo (sv v377) (sv t377.2) (sv v379) (sv v95) (sv v381) (L2.p_cos e_t377_2) (L2.p_addc (-4) (L2.p_add_comm e_v379) e_v18) e_v95 (L2.p_max e_v380 (L2.p_sel e_v381))
  have f677 := L2.K3_cos_hi (sv v377) (sv t377.2) (sv v382) (sv v23) (sv v384) (L2.p_cos e_t377_2) (L2.p_addc (4) (L2.p_add_comm e_v382) e_v21) e_v23 (L2.p_min e_v383 (L2.p_sel e_v384))
  have f686 := L2.K3_sin_hi (sv v377) (sv t377.1) (sv v386) (sv v23) (sv v388) (L2.p_sin e_t377_1) (L2.p_addc (4) (L2.p_add_comm e_v386) e_v21) e_v23 (L2.p_min e_v387 (L2.p_sel e_v388))
  have f695 := L2.K3_sin_lo (sv v377) (sv t377.1) (sv v389) (L2.p_sin e_t377_1) (L2.p_addc (-4) (L2.p_add_comm e_v389) e_v18)
  have f662 := L2.K12_atan_hi (sv v282) (sv v333) (sv v51) v332 (sv v375) (sv v376) (sv v377) (sv v381) (sv v384) (sv v388) (sv v389) (sv v390) (sv v391) (sv v392) (sv v393) v395 v397 v398 v399 (sv v206) v401 v402 v403 v404 v405 (sv v213) v407 v408 v409 v410 v411 v412 (sv v413) (sv v414) (sv v213) (sv v415) e_v51 e_v332 e_v375 (L2.p_sel e_v376) (L2.p_hint e_v377) f668 f677 f686 f695 (L2.p_sel e_v390) (L2.p_sel e_v391) (L2.p_mul_comm e_v392) (L2.p_mul_comm e_v393) (L2.p_le e_v394 e_v395) (L2.p_le e_v396 e_v397) e_v398 e_v399 e_v206 (L2.p_le e_v400 e_v401) (L2.p_clt (-1) e_v8 e_v402) e_v403 (L2.p_and_comm e_v404) e_v405 e_v213 (L2.p_le e_v406 e_v407) (L2.p_or_comm e_v408) e_v409 e_v410 (L2.p_and_comm e_v411) e_v412 e_v413 (L2.p_sel e_v414) e_v213 (L2.p_sel e_v415)
  let u416 : ℤ := if v329 = 1 then u222 else u374
  have f453 := L2.K19_iso_angle_pt True (sv v2) (sv v100) (sv v107) (sv v32) (sv v267) u276 (sv v282) (sv v286) (sv v293) (sv v326) (sv v327) u331 (sv v333) v329 v328 u374 (sv v415) u222 (sv v213) u416 (sv v417) f454 f457 f496 f533 f577 (L2.p_not_not e_v329) f588 f662 rfl e_v213 rfl (L2.p_sel e_v417)
  have f127 := L2.K20_iso_angle True (sv v2) (sv v3) (sv v0) (sv v1) (sv v100) (sv v107) u265 u266 u175 u416 (sv v417) v329 f128 f167 f453
  have f741 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f740 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v17) (sv v19) (sv v20) (sv v22) (sv v23) (sv v25) v27 v29 v30 (sv v31) f741 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v16 (L2.p_sel e_v17)) (L2.p_addc (-4) e_v19 e_v18) (L2.p_max e_v16 (L2.p_sel e_v20)) (L2.p_addc (4) e_v22 e_v21) e_v23 (L2.p_min e_v24 (L2.p_sel e_v25)) (L2.p_ltc (421657430) e_v26 e_v27) (L2.p_clt (421657427) e_v28 e_v29) e_v30 (L2.p_sel e_v31)
  have f777 := L2.K5_ihalf (sv v4) (sv v5) (sv v418) (sv v419) e_v418 e_v419
  have f781 := L2.K8_in_range True (sv v418) (sv v419) v420 (sv v10) v422 v423 (L2.p_clt (-1) e_v8 e_v420) e_v10 (L2.p_le e_v421 e_v422) e_v423 (L2.X1_top _ k_v423)
  have f780 := L2.K9_isin True (sv v418) (sv v419) (sv t418.1) (sv t419.1) (sv v427) (sv v428) (sv v429) (sv v430) (sv v23) (sv v432) v433 v434 v435 (sv v436) f781 (L2.p_sin e_t418_1) (L2.p_sin e_t419_1) (L2.p_min e_v426 (L2.p_sel e_v427)) (L2.p_addc (-4) (L2.p_add_comm e_v428) e_v18) (L2.p_max e_v426 (L2.p_sel e_v429)) (L2.p_addc (4) (L2.p_add_comm e_v430) e_v21) e_v23 (L2.p_min e_v431 (L2.p_sel e_v432)) (L2.p_ltc (421657430) e_v26 e_v433) (L2.p_clt (421657427) e_v28 e_v434) e_v435 (L2.p_sel e_v436)
  let u438 : ℕ := if v437 = 1 then 0 else 1
  have f817 := L2.K7_imul_full True (sv v19) (sv v31) (sv v428) (sv v436) (sv v51) v52 v53 v54 v55 v56 v57 v437 u438 v439 v440 v441 v442 v443 v444 v445 (sv v446) v447 v448 v449 (sv v450) v451 v452 (sv v453) v454 v455 (sv v456) (sv v458) (sv v460) (sv v462) (sv v464) (sv v466) (sv v468) (sv v469) (sv v470) e_v51 e_v52 e_v53 e_v54 e_v55 (L2.p_and_comm e_v56) e_v57 e_v437 (L2.p_unot _) e_v439 e_v440 (L2.p_and_comm e_v441) e_v442 e_v443 e_v444 e_v445 (L2.p_sel e_v446) e_v447 e_v448 e_v449 (L2.p_sel e_v450) e_v451 e_v452 (L2.p_sel e_v453) e_v454 e_v455 (L2.p_sel e_v456) (L2.p_mul (L2.p_mul_comm e_v457) e_v458) (L2.p_mulc (L2.p_mul_comm e_v459) e_v460) (L2.p_mul (L2.p_mul_comm e_v461) e_v462) (L2.p_mulc (L2.p_mul_comm e_v463) e_v464) (L2.p_min e_v465 (L2.p_sel e_v466)) (L2.p_max e_v467 (L2.p_sel e_v468)) (L2.p_sel e_v469) (L2.p_sel e_v470)
  have f739 := L2.K14_iso_base_a True (sv v4) (sv v5) (sv v0) (sv v1) (sv v19) (sv v31) (sv v418) (sv v419) (sv v428) (sv v436) (sv v469) (sv v470) v471 f740 f777 f780 f817 (L2.p_clt (-1) e_v8 e_v471) (L2.X1_top _ k_v471)
  have f868 := L2.K15_in_open (sv v0) (sv v1) v472 v474 v475 (L2.p_clt (0) e_v51 e_v472) (L2.p_ltc (843314856) e_v473 e_v474) e_v475
  have f867 := L2.K15_a_open_plain (sv v0) (sv v1) v475 f868
  have f876 := L2.K15_a_open (sv v90) (sv v91) v476 v477 v478 (L2.p_clt (0) e_v51 e_v476) (L2.p_ltc (268435456) e_v23 e_v477) e_v478
  have f884 := L2.K15_a_open (sv v469) (sv v470) v479 v480 v481 (L2.p_clt (0) e_v51 e_v479) (L2.p_ltc (268435456) e_v23 e_v480) e_v481
  have f896 := L2.K8_in_range (True ∧ v483 = 1) (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_step True v483 v484 v13 v485 e_v484 (L2.p_or_comm e_v485) (L2.X1_top _ k_v485))
  have f908 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v94) (sv v95) (sv v97) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v94) e_v18) e_v95 (L2.p_max e_v96 (L2.p_sel e_v97))
  have f922 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v102) (sv v23) (sv v104) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v102) e_v21) e_v23 (L2.p_min e_v103 (L2.p_sel e_v104))
  have f895 := L2.K10_icos (True ∧ v483 = 1) (sv v0) (sv v1) (sv v97) (sv v95) v99 (sv v100) (sv v104) (sv v23) v106 (sv v107) f896 f908 e_v95 (L2.p_clt (843314855) e_v98 e_v99) (L2.p_sel e_v100) f922 e_v23 (L2.p_ltc (1) e_v105 e_v106) (L2.p_sel e_v107)
  have f894 := L2.K16_a_cos_plain (True ∧ v483 = 1) (sv v0) (sv v1) (sv v100) (sv v107) f895
  have f936 := L2.K16_a_cos (True ∧ v483 = 1) (sv v469) (sv v470) (sv v23) (sv v487) (sv v488) (sv v489) (sv v95) (sv v491) (sv v493) (sv v494) (sv v495) e_v23 (L2.p_mulc e_v486 e_v487) e_v488 e_v489 e_v95 (L2.p_max e_v490 (L2.p_sel e_v491)) (L2.p_mul e_v492 e_v493) e_v494 e_v495
  have f950 := L2.K16_a_cos (True ∧ v483 = 1) (sv v90) (sv v91) (sv v23) (sv v497) (sv v498) (sv v499) (sv v95) (sv v501) (sv v503) (sv v504) (sv v505) e_v23 (L2.p_mulc e_v496 e_v497) e_v498 e_v499 e_v95 (L2.p_max e_v500 (L2.p_sel e_v501)) (L2.p_mul e_v502 e_v503) e_v504 e_v505
  let u507 : ℕ := if v506 = 1 then 0 else 1
  have f964 := L2.K7_imul_full (True ∧ v483 = 1) (sv v100) (sv v107) (sv v501) (sv v505) (sv v51) v134 v135 v136 v137 v138 v139 v506 u507 v508 v509 v510 v511 v512 v513 v514 (sv v515) v516 v517 v518 (sv v519) v520 v521 (sv v522) v523 v524 (sv v525) (sv v527) (sv v529) (sv v531) (sv v533) (sv v535) (sv v537) (sv v538) (sv v539) e_v51 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 e_v506 (L2.p_unot _) e_v508 e_v509 (L2.p_and_comm e_v510) e_v511 e_v512 e_v513 e_v514 (L2.p_sel e_v515) e_v516 e_v517 e_v518 (L2.p_sel e_v519) e_v520 e_v521 (L2.p_sel e_v522) e_v523 e_v524 (L2.p_sel e_v525) (L2.p_mul (L2.p_mul_comm e_v526) e_v527) (L2.p_mulc (L2.p_mul_comm e_v528) e_v529) (L2.p_mul (L2.p_mul_comm e_v530) e_v531) (L2.p_mulc (L2.p_mul_comm e_v532) e_v533) (L2.p_min e_v534 (L2.p_sel e_v535)) (L2.p_max e_v536 (L2.p_sel e_v537)) (L2.p_sel e_v538) (L2.p_sel e_v539)
  have f1008 := L2.K4_isub (sv v491) (sv v495) (sv v538) (sv v539) (sv v540) (sv v541) e_v540 e_v541
  let u543 : ℕ := if v542 = 1 then 0 else 1
  have f1011 := L2.K7_imul_full (True ∧ v483 = 1) (sv v100) (sv v107) (sv v491) (sv v495) (sv v51) v134 v135 v136 v137 v138 v139 v542 u543 v544 v545 v546 v547 v548 v549 v550 (sv v551) v552 v553 v554 (sv v555) v556 v557 (sv v558) v559 v560 (sv v561) (sv v563) (sv v565) (sv v567) (sv v569) (sv v571) (sv v573) (sv v574) (sv v575) e_v51 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 e_v542 (L2.p_unot _) e_v544 e_v545 (L2.p_and_comm e_v546) e_v547 e_v548 e_v549 e_v550 (L2.p_sel e_v551) e_v552 e_v553 e_v554 (L2.p_sel e_v555) e_v556 e_v557 (L2.p_sel e_v558) e_v559 e_v560 (L2.p_sel e_v561) (L2.p_mul (L2.p_mul_comm e_v562) e_v563) (L2.p_mulc (L2.p_mul_comm e_v564) e_v565) (L2.p_mul (L2.p_mul_comm e_v566) e_v567) (L2.p_mulc (L2.p_mul_comm e_v568) e_v569) (L2.p_min e_v570 (L2.p_sel e_v571)) (L2.p_max e_v572 (L2.p_sel e_v573)) (L2.p_sel e_v574) (L2.p_sel e_v575)
  have f1055 := L2.K4_isub (sv v501) (sv v505) (sv v574) (sv v575) (sv v576) (sv v577) e_v576 e_v577
  have f1084 := L2.K8_in_range (True ∧ v483 = 1) (sv v0) (sv v0) v9 (sv v10) v591 v592 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v590 e_v591) e_v592 (L2.X1_step True v483 v484 v592 v593 e_v484 e_v593 (L2.X1_top _ k_v593))
  let u594 : ℤ := (sv v18) + (sv t0.2)
  let u595 : ℕ := if u594 < (sv v95) then 1 else 0
  let u596 : ℤ := if u595 = 1 then (sv v95) else u594
  have f1096 := L2.K3_cos_lo (sv v0) (sv t0.2) u594 (sv v95) u596 (L2.p_cos e_t0_2) (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u597 : ℕ := if (sv v98) < (sv v0) then 1 else 0
  let u598 : ℤ := if u597 = 1 then (sv v95) else u596
  have f1110 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v102) (sv v23) (sv v104) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v102) e_v21) e_v23 (L2.p_min e_v103 (L2.p_sel e_v104))
  have f1083 := L2.K10_icos (True ∧ v483 = 1) (sv v0) (sv v0) u596 (sv v95) u597 u598 (sv v104) (sv v23) v106 (sv v107) f1084 f1096 e_v95 (L2.p_clt (843314855) e_v98 (L2.p_ult _ _)) rfl f1110 e_v23 (L2.p_ltc (1) e_v105 e_v106) (L2.p_sel e_v107)
  have f1082 := L2.K16_a_cos_plain (True ∧ v483 = 1) (sv v0) (sv v0) u598 (sv v107) f1083
  have f1124 := L2.K16_a_cos (True ∧ v483 = 1) (sv v582) (sv v583) (sv v23) (sv v600) (sv v601) (sv v602) (sv v95) (sv v604) (sv v606) (sv v607) (sv v608) e_v23 (L2.p_mulc e_v599 e_v600) e_v601 e_v602 e_v95 (L2.p_max e_v603 (L2.p_sel e_v604)) (L2.p_mul e_v605 e_v606) e_v607 e_v608
  have f1138 := L2.K16_a_cos (True ∧ v483 = 1) (sv v586) (sv v587) (sv v23) (sv v610) (sv v611) (sv v612) (sv v95) (sv v614) (sv v616) (sv v617) (sv v618) e_v23 (L2.p_mulc e_v609 e_v610) e_v611 e_v612 e_v95 (L2.p_max e_v613 (L2.p_sel e_v614)) (L2.p_mul e_v615 e_v616) e_v617 e_v618
  let u626 : ℕ := if v625 = 1 then 0 else 1
  let u639 : ℕ := if v623 = 1 ∧ v630 = 1 then 1 else 0
  let u640 : ℕ := if v629 = 1 ∨ u639 = 1 then 1 else 0
  let u641 : ℤ := if u640 = 1 then (sv v604) else (sv v608)
  let u642 : ℕ := if v624 = 1 ∧ v629 = 1 then 1 else 0
  let u643 : ℕ := if v623 = 1 ∨ u642 = 1 then 1 else 0
  let u644 : ℤ := if u643 = 1 then (sv v614) else (sv v618)
  let u647 : ℤ := u641 * u644
  let u648 : ℤ := -((-u647) / 2 ^ 28)
  let u651 : ℤ := (sv v604) * (sv v614)
  let u652 : ℤ := -((-u651) / 2 ^ 28)
  let u655 : ℕ := if u648 < u652 then 1 else 0
  let u656 : ℤ := if u655 = 1 then u652 else u648
  let u658 : ℤ := if v631 = 1 then u656 else u648
  have f1152 := L2.K7_imul_full (True ∧ v483 = 1) (sv v604) (sv v608) (sv v614) (sv v618) (sv v51) v619 v620 v621 v622 v623 v624 v625 u626 v627 v628 v629 v630 v631 v632 v633 (sv v634) v635 v636 v637 (sv v638) u639 u640 u641 u642 u643 u644 (sv v646) u648 (sv v650) u652 (sv v654) u656 (sv v657) u658 e_v51 e_v619 e_v620 e_v621 e_v622 (L2.p_and_comm e_v623) e_v624 e_v625 (L2.p_unot _) e_v627 e_v628 (L2.p_and_comm e_v629) e_v630 e_v631 e_v632 e_v633 (L2.p_sel e_v634) e_v635 e_v636 e_v637 (L2.p_sel e_v638) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul (L2.p_mul_comm e_v645) e_v646) (L2.p_mulc rfl rfl) (L2.p_mul (L2.p_mul_comm e_v649) e_v650) (L2.p_mulc rfl rfl) (L2.p_min e_v653 (L2.p_sel e_v654)) (L2.p_max (L2.p_ult _ _) rfl) (L2.p_sel e_v657) rfl
  let u659 : ℤ := u598 - u658
  have f1196 := L2.K4_isub u598 (sv v107) (sv v657) u658 u659 (sv v660) rfl e_v660
  have f1200 := L2.K17_s_end (sv v582) (sv v605) (sv v661) (sv v662) (sv v663) (sv v664) (sv v666) (sv v667) (sv v23) (sv v669) (sv v670) (sv v672) e_v605 e_v661 e_v662 (L2.p_sqrt e_v663) (L2.p_addc (1) (L2.p_add_comm e_v664) e_v105) (L2.p_mul (L2.p_mul_comm e_v665) e_v666) e_v667 e_v23 (L2.p_mulc (L2.p_mul_comm e_v668) e_v669) e_v670 (L2.p_min e_v671 (L2.p_sel e_v672))
  have f1218 := L2.K17_s_end (sv v583) (sv v599) (sv v661) (sv v673) (sv v674) (sv v675) (sv v677) (sv v678) (sv v23) (sv v680) (sv v681) (sv v683) e_v599 e_v661 e_v673 (L2.p_sqrt e_v674) (L2.p_addc (1) (L2.p_add_comm e_v675) e_v105) (L2.p_mul (L2.p_mul_comm e_v676) e_v677) e_v678 e_v23 (L2.p_mulc (L2.p_mul_comm e_v679) e_v680) e_v681 (L2.p_min e_v682 (L2.p_sel e_v683))
  have f1199 := L2.K18_a_sin (True ∧ v483 = 1) (sv v582) (sv v583) (sv v667) (sv v672) (sv v678) (sv v683) (sv v685) (sv v687) (sv v688) (sv v605) (sv v599) v690 v692 v693 (sv v23) (sv v694) f1200 f1218 (L2.p_min e_v684 (L2.p_sel e_v685)) (L2.p_max e_v686 (L2.p_sel e_v687)) e_v688 e_v605 e_v599 (L2.p_le e_v689 e_v690) (L2.p_le e_v691 e_v692) e_v693 e_v23 (L2.p_sel e_v694)
  have f1255 := L2.K17_s_end (sv v586) (sv v615) (sv v661) (sv v695) (sv v696) (sv v697) (sv v699) (sv v700) (sv v23) (sv v702) (sv v703) (sv v705) e_v615 e_v661 e_v695 (L2.p_sqrt e_v696) (L2.p_addc (1) (L2.p_add_comm e_v697) e_v105) (L2.p_mul (L2.p_mul_comm e_v698) e_v699) e_v700 e_v23 (L2.p_mulc (L2.p_mul_comm e_v701) e_v702) e_v703 (L2.p_min e_v704 (L2.p_sel e_v705))
  have f1273 := L2.K17_s_end (sv v587) (sv v609) (sv v661) (sv v706) (sv v707) (sv v708) (sv v710) (sv v711) (sv v23) (sv v713) (sv v714) (sv v716) e_v609 e_v661 e_v706 (L2.p_sqrt e_v707) (L2.p_addc (1) (L2.p_add_comm e_v708) e_v105) (L2.p_mul (L2.p_mul_comm e_v709) e_v710) e_v711 e_v23 (L2.p_mulc (L2.p_mul_comm e_v712) e_v713) e_v714 (L2.p_min e_v715 (L2.p_sel e_v716))
  have f1254 := L2.K18_a_sin (True ∧ v483 = 1) (sv v586) (sv v587) (sv v700) (sv v705) (sv v711) (sv v716) (sv v718) (sv v720) (sv v688) (sv v615) (sv v609) v722 v724 v725 (sv v23) (sv v726) f1255 f1273 (L2.p_min e_v717 (L2.p_sel e_v718)) (L2.p_max e_v719 (L2.p_sel e_v720)) e_v688 e_v615 e_v609 (L2.p_le e_v721 e_v722) (L2.p_le e_v723 e_v724) e_v725 e_v23 (L2.p_sel e_v726)
  let u734 : ℕ := if v733 = 1 then 0 else 1
  have f1309 := L2.K7_imul_full (True ∧ v483 = 1) (sv v685) (sv v694) (sv v718) (sv v726) (sv v51) v727 v728 v729 v730 v731 v732 v733 u734 v735 v736 v737 v738 v739 v740 v741 (sv v742) v743 v744 v745 (sv v746) v747 v748 (sv v749) v750 v751 (sv v752) (sv v754) (sv v756) (sv v758) (sv v760) (sv v762) (sv v764) (sv v765) (sv v766) e_v51 e_v727 e_v728 e_v729 e_v730 (L2.p_and_comm e_v731) e_v732 e_v733 (L2.p_unot _) e_v735 e_v736 (L2.p_and_comm e_v737) e_v738 e_v739 e_v740 e_v741 (L2.p_sel e_v742) e_v743 e_v744 e_v745 (L2.p_sel e_v746) e_v747 e_v748 (L2.p_sel e_v749) e_v750 e_v751 (L2.p_sel e_v752) (L2.p_mul (L2.p_mul_comm e_v753) e_v754) (L2.p_mulc (L2.p_mul_comm e_v755) e_v756) (L2.p_mul (L2.p_mul_comm e_v757) e_v758) (L2.p_mulc (L2.p_mul_comm e_v759) e_v760) (L2.p_min e_v761 (L2.p_sel e_v762)) (L2.p_max e_v763 (L2.p_sel e_v764)) (L2.p_sel e_v765) (L2.p_sel e_v766)
  let u769 : ℕ := if u659 < (sv v51) then 1 else 0
  let u770 : ℤ := if u769 = 1 then (sv v765) else (sv v766)
  have f1353 := L2.K11_qdiv u659 (sv v660) (sv v765) (sv v766) v767 v768 (sv v51) u769 u770 v771 (sv v772) (L2.p_clt (0) e_v51 e_v767) e_v768 e_v51 (L2.p_ult _ _) rfl e_v771 (L2.p_sel e_v772)
  have f1081 := L2.K23_hn false true true (True ∧ v483 = 1) (sv v0) (sv v0) (sv v582) (sv v583) (sv v586) (sv v587) u598 (sv v107) (sv v604) (sv v608) (sv v614) (sv v618) (sv v657) u658 u659 (sv v660) (sv v685) (sv v694) (sv v718) (sv v726) (sv v765) (sv v766) u770 (sv v772) v768 f1082 f1124 f1138 f1152 f1196 f1199 f1254 f1309 f1353
  have f1378 := L2.K8_in_range (True ∧ v483 = 1) (sv v1) (sv v1) v781 (sv v10) v12 v782 (L2.p_clt (-1) e_v8 e_v781) e_v10 (L2.p_le e_v11 e_v12) (L2.p_and_comm e_v782) (L2.X1_step True v483 v484 v782 v783 e_v484 e_v783 (L2.X1_top _ k_v783))
  have f1390 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v94) (sv v95) (sv v97) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v94) e_v18) e_v95 (L2.p_max e_v96 (L2.p_sel e_v97))
  let u784 : ℤ := (sv v21) + (sv t1.2)
  let u785 : ℕ := if u784 < (sv v23) then 1 else 0
  let u786 : ℤ := if u785 = 1 then u784 else (sv v23)
  have f1404 := L2.K3_cos_hi (sv v1) (sv t1.2) u784 (sv v23) u786 (L2.p_cos e_t1_2) (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u787 : ℕ := if (sv v1) < (sv v105) then 1 else 0
  let u788 : ℤ := if u787 = 1 then (sv v23) else u786
  have f1377 := L2.K10_icos (True ∧ v483 = 1) (sv v1) (sv v1) (sv v97) (sv v95) v99 (sv v100) u786 (sv v23) u787 u788 f1378 f1390 e_v95 (L2.p_clt (843314855) e_v98 e_v99) (L2.p_sel e_v100) f1404 e_v23 (L2.p_ltc (1) e_v105 (L2.p_ult _ _)) rfl
  have f1376 := L2.K16_a_cos_plain (True ∧ v483 = 1) (sv v1) (sv v1) (sv v100) u788 f1377
  have f1418 := L2.K16_a_cos (True ∧ v483 = 1) (sv v584) (sv v585) (sv v23) (sv v790) (sv v791) (sv v792) (sv v95) (sv v794) (sv v796) (sv v797) (sv v798) e_v23 (L2.p_mulc e_v789 e_v790) e_v791 e_v792 e_v95 (L2.p_max e_v793 (L2.p_sel e_v794)) (L2.p_mul e_v795 e_v796) e_v797 e_v798
  have f1432 := L2.K16_a_cos (True ∧ v483 = 1) (sv v588) (sv v589) (sv v23) (sv v800) (sv v801) (sv v802) (sv v95) (sv v804) (sv v806) (sv v807) (sv v808) e_v23 (L2.p_mulc e_v799 e_v800) e_v801 e_v802 e_v95 (L2.p_max e_v803 (L2.p_sel e_v804)) (L2.p_mul e_v805 e_v806) e_v807 e_v808
  let u810 : ℕ := if v809 = 1 then 0 else 1
  let u816 : ℕ := if v815 = 1 then 0 else 1
  let u822 : ℕ := if u810 = 1 ∧ v820 = 1 then 1 else 0
  let u823 : ℕ := if v819 = 1 ∨ u822 = 1 then 1 else 0
  let u824 : ℤ := if u823 = 1 then (sv v798) else (sv v794)
  let u825 : ℕ := if v819 = 1 then 0 else 1
  let u826 : ℕ := if v814 = 1 ∧ u825 = 1 then 1 else 0
  let u827 : ℕ := if v813 = 1 ∨ u826 = 1 then 1 else 0
  let u828 : ℤ := if u827 = 1 then (sv v808) else (sv v804)
  let u835 : ℤ := u824 * u828
  let u836 : ℤ := u835 / 2 ^ 28
  let u839 : ℤ := (sv v798) * (sv v804)
  let u840 : ℤ := u839 / 2 ^ 28
  let u843 : ℕ := if u836 < u840 then 1 else 0
  let u844 : ℤ := if u843 = 1 then u836 else u840
  let u847 : ℤ := if v821 = 1 then u844 else u836
  have f1446 := L2.K7_imul_full (True ∧ v483 = 1) (sv v794) (sv v798) (sv v804) (sv v808) (sv v51) v809 u810 v811 v812 v813 v814 v815 u816 v817 v818 v819 v820 v821 u822 u823 u824 u825 u826 u827 u828 v829 v830 (sv v831) v832 v833 (sv v834) u836 (sv v838) u840 (sv v842) u844 (sv v846) u847 (sv v848) e_v51 e_v809 (L2.p_unot _) e_v811 e_v812 (L2.p_and_comm e_v813) e_v814 e_v815 (L2.p_unot _) e_v817 e_v818 (L2.p_and_comm e_v819) e_v820 e_v821 (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_unot _) (L2.p_uand _ _) (L2.p_uor _ _) rfl e_v829 e_v830 (L2.p_sel e_v831) e_v832 e_v833 (L2.p_sel e_v834) (L2.p_mul rfl rfl) (L2.p_mulc (L2.p_mul_comm e_v837) e_v838) (L2.p_mul rfl rfl) (L2.p_mulc (L2.p_mul_comm e_v841) e_v842) (L2.p_min (L2.p_ult _ _) rfl) (L2.p_max e_v845 (L2.p_sel e_v846)) rfl (L2.p_sel e_v848)
  let u850 : ℤ := u788 - u847
  have f1490 := L2.K4_isub (sv v100) u788 u847 (sv v848) (sv v849) u850 e_v849 rfl
  have f1494 := L2.K17_s_end (sv v584) (sv v795) (sv v661) (sv v851) (sv v852) (sv v853) (sv v855) (sv v856) (sv v23) (sv v858) (sv v859) (sv v861) e_v795 e_v661 e_v851 (L2.p_sqrt e_v852) (L2.p_addc (1) (L2.p_add_comm e_v853) e_v105) (L2.p_mul (L2.p_mul_comm e_v854) e_v855) e_v856 e_v23 (L2.p_mulc (L2.p_mul_comm e_v857) e_v858) e_v859 (L2.p_min e_v860 (L2.p_sel e_v861))
  have f1512 := L2.K17_s_end (sv v585) (sv v789) (sv v661) (sv v862) (sv v863) (sv v864) (sv v866) (sv v867) (sv v23) (sv v869) (sv v870) (sv v872) e_v789 e_v661 e_v862 (L2.p_sqrt e_v863) (L2.p_addc (1) (L2.p_add_comm e_v864) e_v105) (L2.p_mul (L2.p_mul_comm e_v865) e_v866) e_v867 e_v23 (L2.p_mulc (L2.p_mul_comm e_v868) e_v869) e_v870 (L2.p_min e_v871 (L2.p_sel e_v872))
  have f1493 := L2.K18_a_sin (True ∧ v483 = 1) (sv v584) (sv v585) (sv v856) (sv v861) (sv v867) (sv v872) (sv v874) (sv v876) (sv v688) (sv v795) (sv v789) v878 v880 v881 (sv v23) (sv v882) f1494 f1512 (L2.p_min e_v873 (L2.p_sel e_v874)) (L2.p_max e_v875 (L2.p_sel e_v876)) e_v688 e_v795 e_v789 (L2.p_le e_v877 e_v878) (L2.p_le e_v879 e_v880) e_v881 e_v23 (L2.p_sel e_v882)
  have f1549 := L2.K17_s_end (sv v588) (sv v805) (sv v661) (sv v883) (sv v884) (sv v885) (sv v887) (sv v888) (sv v23) (sv v890) (sv v891) (sv v893) e_v805 e_v661 e_v883 (L2.p_sqrt e_v884) (L2.p_addc (1) (L2.p_add_comm e_v885) e_v105) (L2.p_mul (L2.p_mul_comm e_v886) e_v887) e_v888 e_v23 (L2.p_mulc (L2.p_mul_comm e_v889) e_v890) e_v891 (L2.p_min e_v892 (L2.p_sel e_v893))
  have f1567 := L2.K17_s_end (sv v589) (sv v799) (sv v661) (sv v894) (sv v895) (sv v896) (sv v898) (sv v899) (sv v23) (sv v901) (sv v902) (sv v904) e_v799 e_v661 e_v894 (L2.p_sqrt e_v895) (L2.p_addc (1) (L2.p_add_comm e_v896) e_v105) (L2.p_mul (L2.p_mul_comm e_v897) e_v898) e_v899 e_v23 (L2.p_mulc (L2.p_mul_comm e_v900) e_v901) e_v902 (L2.p_min e_v903 (L2.p_sel e_v904))
  have f1548 := L2.K18_a_sin (True ∧ v483 = 1) (sv v588) (sv v589) (sv v888) (sv v893) (sv v899) (sv v904) (sv v906) (sv v908) (sv v688) (sv v805) (sv v799) v910 v912 v913 (sv v23) (sv v914) f1549 f1567 (L2.p_min e_v905 (L2.p_sel e_v906)) (L2.p_max e_v907 (L2.p_sel e_v908)) e_v688 e_v805 e_v799 (L2.p_le e_v909 e_v910) (L2.p_le e_v911 e_v912) e_v913 e_v23 (L2.p_sel e_v914)
  let u922 : ℕ := if v921 = 1 then 0 else 1
  have f1603 := L2.K7_imul_full (True ∧ v483 = 1) (sv v874) (sv v882) (sv v906) (sv v914) (sv v51) v915 v916 v917 v918 v919 v920 v921 u922 v923 v924 v925 v926 v927 v928 v929 (sv v930) v931 v932 v933 (sv v934) v935 v936 (sv v937) v938 v939 (sv v940) (sv v942) (sv v944) (sv v946) (sv v948) (sv v950) (sv v952) (sv v953) (sv v954) e_v51 e_v915 e_v916 e_v917 e_v918 (L2.p_and_comm e_v919) e_v920 e_v921 (L2.p_unot _) e_v923 e_v924 (L2.p_and_comm e_v925) e_v926 e_v927 e_v928 e_v929 (L2.p_sel e_v930) e_v931 e_v932 e_v933 (L2.p_sel e_v934) e_v935 e_v936 (L2.p_sel e_v937) e_v938 e_v939 (L2.p_sel e_v940) (L2.p_mul (L2.p_mul_comm e_v941) e_v942) (L2.p_mulc (L2.p_mul_comm e_v943) e_v944) (L2.p_mul (L2.p_mul_comm e_v945) e_v946) (L2.p_mulc (L2.p_mul_comm e_v947) e_v948) (L2.p_min e_v949 (L2.p_sel e_v950)) (L2.p_max e_v951 (L2.p_sel e_v952)) (L2.p_sel e_v953) (L2.p_sel e_v954)
  let u959 : ℕ := if u850 < (sv v51) then 1 else 0
  let u960 : ℤ := if u959 = 1 then (sv v954) else (sv v953)
  have f1647 := L2.K11_qdiv (sv v849) u850 (sv v953) (sv v954) v955 v956 (sv v51) v957 (sv v958) u959 u960 (L2.p_clt (0) e_v51 e_v955) e_v956 e_v51 e_v957 (L2.p_sel e_v958) (L2.p_ult _ _) rfl
  have f1375 := L2.K23_hn false true true (True ∧ v483 = 1) (sv v1) (sv v1) (sv v584) (sv v585) (sv v588) (sv v589) (sv v100) u788 (sv v794) (sv v798) (sv v804) (sv v808) u847 (sv v848) (sv v849) u850 (sv v874) (sv v882) (sv v906) (sv v914) (sv v953) (sv v954) (sv v958) u960 v956 f1376 f1418 f1432 f1446 f1490 f1493 f1548 f1603 f1647
  let u970 : ℕ := if v969 = 1 then 0 else 1
  have f1676 := L2.K3_cos_lo (sv v971) (sv t971.2) (sv v975) (sv v95) (sv v977) (L2.p_cos e_t971_2) (L2.p_addc (-4) (L2.p_add_comm e_v975) e_v18) e_v95 (L2.p_max e_v976 (L2.p_sel e_v977))
  have f1671 := L2.K13_acos_lo (sv v779) (sv v780) (sv v971) (sv v51) v972 v973 (sv v977) (sv v978) (sv v979) v981 (sv v473) v983 v984 v985 (sv v986) (L2.p_hint e_v971) e_v51 e_v972 e_v973 f1676 e_v978 e_v979 (L2.p_le e_v980 e_v981) e_v473 (L2.p_le e_v982 e_v983) e_v984 e_v985 (L2.p_sel e_v986)
  have f1703 := L2.K3_cos_hi (sv v987) (sv t987.2) (sv v991) (sv v23) (sv v993) (L2.p_cos e_t987_2) (L2.p_addc (4) (L2.p_add_comm e_v991) e_v21) e_v23 (L2.p_min e_v992 (L2.p_sel e_v993))
  have f1697 := L2.K13_acos_hi (sv v967) (sv v968) (sv v987) (sv v10) v989 (sv v993) (sv v994) (sv v995) v997 v998 (sv v999) (L2.p_hint e_v987) e_v10 (L2.p_le e_v988 e_v989) f1703 e_v994 e_v995 (L2.p_le e_v996 e_v997) e_v998 (L2.p_sel e_v999)
  let u1003 : ℤ := if v775 = 1 then (sv v473) else (sv v51)
  let u1004 : ℤ := if v775 = 1 then (sv v10) else (sv v51)
  have f1078 := L2.K24_tri_tail_x false true true True (sv v0) (sv v1) v483 (sv v582) (sv v583) (sv v586) (sv v587) (sv v584) (sv v585) (sv v588) (sv v589) (sv v23) (sv v95) u659 u770 (sv v660) (sv v772) v768 v767 (sv v773) v774 v775 v777 v778 (sv v779) (sv v780) (sv v849) (sv v958) u850 u960 v956 v955 v961 v962 (sv v963) v965 v966 (sv v967) (sv v968) v969 u970 (sv v986) (sv v999) (sv v51) (sv v10) (sv v473) (sv v1000) (sv v1001) v1002 u1003 u1004 e_v23 e_v95 f1081 (L2.p_not_not e_v768) (L2.p_neg e_v51 e_v773) e_v774 e_v775 (L2.p_le e_v776 e_v777) e_v778 (L2.p_sel e_v779) (L2.p_sel e_v780) f1375 (L2.p_not_not e_v956) e_v961 e_v962 (L2.p_neg e_v51 e_v963) (L2.p_le e_v964 e_v965) e_v966 (L2.p_sel e_v967) (L2.p_sel e_v968) e_v969 (L2.p_unot _) f1671 f1697 e_v51 e_v10 e_v473 (L2.p_sel e_v1000) (L2.p_sel e_v1001) e_v1002 rfl rfl
  have f866 := L2.K21_tri_angle_st false true true True (sv v0) (sv v1) (sv v90) (sv v91) (sv v469) (sv v470) v475 v478 v481 v482 v483 (sv v100) (sv v107) (sv v491) (sv v495) (sv v501) (sv v505) (sv v538) (sv v539) (sv v540) (sv v541) (sv v574) (sv v575) (sv v576) (sv v577) v578 v579 v580 v581 (sv v582) (sv v583) (sv v584) (sv v585) (sv v586) (sv v587) (sv v588) (sv v589) (sv v1000) (sv v1001) v1002 u1003 u1004 f867 f876 f884 e_v482 (L2.p_and_comm e_v483) f894 f936 f950 f964 f1008 f1011 f1055 (L2.p_clt (0) e_v51 e_v578) (L2.p_ltc (0) e_v51 e_v579) (L2.p_clt (0) e_v51 e_v580) (L2.p_ltc (0) e_v51 e_v581) (L2.p_sel e_v582) (L2.p_sel e_v583) (L2.p_sel e_v584) (L2.p_sel e_v585) (L2.p_sel e_v586) (L2.p_sel e_v587) (L2.p_sel e_v588) (L2.p_sel e_v589) f1078
  have f865 := L2.K25_tri_angle false true true True (sv v0) (sv v1) (sv v90) (sv v91) (sv v469) (sv v470) (sv v1000) (sv v1001) v1002 u1003 u1004 v1005 f866 e_v1005 (L2.X1_top _ k_v1005)
  let u1006 : ℤ := u265 + (sv v1000)
  have f1729 := L2.K4_iadd u265 (sv v417) (sv v1000) (sv v1001) u1006 (sv v1007) rfl e_v1007
  let u1011 : ℕ := if v1010 = 1 then 0 else 1
  have f1742 := L2.K5_ihalf (sv v2) (sv v3) (sv v32) (sv v33) e_v32 e_v33
  have f1746 := L2.K8_in_range (True ∧ u1011 = 1) (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_step True u1011 v1010 v13 v1012 (L2.p_not_not (L2.p_unot _)) (L2.p_or_comm e_v1012) (L2.X1_top _ k_v1012))
  have f1758 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v94) (sv v95) (sv v97) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v94) e_v18) e_v95 (L2.p_max e_v96 (L2.p_sel e_v97))
  have f1772 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v102) (sv v23) (sv v104) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v102) e_v21) e_v23 (L2.p_min e_v103 (L2.p_sel e_v104))
  have f1745 := L2.K10_icos (True ∧ u1011 = 1) (sv v0) (sv v1) (sv v97) (sv v95) v99 (sv v100) (sv v104) (sv v23) v106 (sv v107) f1746 f1758 e_v95 (L2.p_clt (843314855) e_v98 e_v99) (L2.p_sel e_v100) f1772 e_v23 (L2.p_ltc (1) e_v105 e_v106) (L2.p_sel e_v107)
  have f1787 := L2.K8_in_range (True ∧ u1011 = 1) (sv v32) (sv v33) v34 (sv v10) v36 v37 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v35 e_v36) e_v37 (L2.X1_step True u1011 v1010 v37 v1013 (L2.p_not_not (L2.p_unot _)) (L2.p_or_comm e_v1013) (L2.X1_top _ k_v1013))
  have f1786 := L2.K9_isin (True ∧ u1011 = 1) (sv v32) (sv v33) (sv t32.1) (sv t33.1) (sv v41) (sv v42) (sv v43) (sv v44) (sv v23) (sv v46) v47 v48 v49 (sv v50) f1787 (L2.p_sin e_t32_1) (L2.p_sin e_t33_1) (L2.p_min e_v40 (L2.p_sel e_v41)) (L2.p_addc (-4) (L2.p_add_comm e_v42) e_v18) (L2.p_max e_v40 (L2.p_sel e_v43)) (L2.p_addc (4) (L2.p_add_comm e_v44) e_v21) e_v23 (L2.p_min e_v45 (L2.p_sel e_v46)) (L2.p_ltc (421657430) e_v26 e_v47) (L2.p_clt (421657427) e_v28 e_v48) e_v49 (L2.p_sel e_v50)
  let u1021 : ℕ := if v63 = 1 ∧ v138 = 1 then 1 else 0
  let u1022 : ℕ := if v62 = 1 ∨ u1021 = 1 then 1 else 0
  let u1023 : ℤ := if u1022 = 1 then (sv v100) else (sv v107)
  let u1024 : ℕ := if v62 = 1 ∧ v139 = 1 then 1 else 0
  let u1025 : ℕ := if v138 = 1 ∨ u1024 = 1 then 1 else 0
  let u1026 : ℤ := if u1025 = 1 then (sv v42) else (sv v50)
  let u1029 : ℤ := u1023 * u1026
  let u1030 : ℤ := -((-u1029) / 2 ^ 28)
  let u1033 : ℤ := (sv v42) * (sv v100)
  let u1034 : ℤ := -((-u1033) / 2 ^ 28)
  let u1037 : ℕ := if u1030 < u1034 then 1 else 0
  let u1038 : ℤ := if u1037 = 1 then u1034 else u1030
  let u1040 : ℤ := if v1014 = 1 then u1038 else u1030
  have f1825 := L2.K7_imul_full (True ∧ u1011 = 1) (sv v100) (sv v107) (sv v42) (sv v50) (sv v51) v134 v135 v136 v137 v138 v139 v58 u59 v60 v61 v62 v63 v1014 v1015 v1016 (sv v1017) v68 v1018 v1019 (sv v1020) u1021 u1022 u1023 u1024 u1025 u1026 (sv v1028) u1030 (sv v1032) u1034 (sv v1036) u1038 (sv v1039) u1040 e_v51 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 e_v58 (L2.p_unot _) e_v60 e_v61 (L2.p_and_comm e_v62) e_v63 (L2.p_and_comm e_v1014) (L2.p_and_comm e_v1015) e_v1016 (L2.p_sel e_v1017) e_v68 (L2.p_and_comm e_v1018) e_v1019 (L2.p_sel e_v1020) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl (L2.p_mul (L2.p_mul_comm e_v1027) e_v1028) (L2.p_mulc rfl rfl) (L2.p_mul e_v1031 e_v1032) (L2.p_mulc (L2.p_mul_comm rfl) rfl) (L2.p_min e_v1035 (L2.p_sel e_v1036)) (L2.p_max (L2.p_ult _ _) rfl) (L2.p_sel e_v1039) rfl
  have f1870 := L2.K8_in_range (True ∧ u1011 = 1) (sv v1000) (sv v1001) v1041 (sv v10) v1043 v1044 (L2.p_clt (-1) e_v8 e_v1041) e_v10 (L2.p_le e_v1042 e_v1043) e_v1044 (L2.X1_step True u1011 v1010 v1044 v1045 (L2.p_not_not (L2.p_unot _)) e_v1045 (L2.X1_top _ k_v1045))
  have f1882 := L2.K3_cos_lo (sv v1001) (sv v1047) (sv v1048) (sv v95) (sv v1050) (L2.X2_push L2.cosI v483 (sv v1001) (sv v999) (sv v10) (sv v1046) (sv v95) (sv v1047) (L2.p_sel e_v1001) (L2.X2_push L2.cosI v998 (sv v999) (sv v987) (sv v10) (sv t987.2) (sv v95) (sv v1046) (L2.p_sel e_v999) (L2.p_cos e_t987_2) (L2.p_cos_cc (-268435456) (843314857) e_v95 e_v10 (of_decide_eq_true rfl)) (L2.p_sel e_v1046)) (L2.p_cos_cc (-268435456) (843314857) e_v95 e_v10 (of_decide_eq_true rfl)) (L2.p_sel e_v1047)) (L2.p_addc (-4) (L2.p_add_comm e_v1048) e_v18) e_v95 (L2.p_max e_v1049 (L2.p_sel e_v1050))
  have f1904 := L2.K3_cos_hi (sv v1000) (sv v1054) (sv v1055) (sv v23) (sv v1057) (L2.X2_push L2.cosI v483 (sv v1000) (sv v986) (sv v51) (sv v1053) (sv v23) (sv v1054) (L2.p_sel e_v1000) (L2.X2_push L2.cosI v985 (sv v986) (sv v971) (sv v51) (sv t971.2) (sv v23) (sv v1053) (L2.p_sel e_v986) (L2.p_cos e_t971_2) (L2.p_cos_cc (268435456) (0) e_v23 e_v51 (of_decide_eq_true rfl)) (L2.p_sel e_v1053)) (L2.p_cos_cc (268435456) (0) e_v23 e_v51 (of_decide_eq_true rfl)) (L2.p_sel e_v1054)) (L2.p_addc (4) (L2.p_add_comm e_v1055) e_v21) e_v23 (L2.p_min e_v1056 (L2.p_sel e_v1057))
  have f1869 := L2.K10_icos (True ∧ u1011 = 1) (sv v1000) (sv v1001) (sv v1050) (sv v95) v1051 (sv v1052) (sv v1057) (sv v23) v1058 (sv v1059) f1870 f1882 e_v95 (L2.p_clt (843314855) e_v98 e_v1051) (L2.p_sel e_v1052) f1904 e_v23 (L2.p_ltc (1) e_v105 e_v1058) (L2.p_sel e_v1059)
  have f1927 := L2.K8_in_range (True ∧ u1011 = 1) (sv v1000) (sv v1001) v1041 (sv v10) v1043 v1044 (L2.p_clt (-1) e_v8 e_v1041) e_v10 (L2.p_le e_v1042 e_v1043) e_v1044 (L2.X1_step True u1011 v1010 v1044 v1045 (L2.p_not_not (L2.p_unot _)) e_v1045 (L2.X1_top _ k_v1045))
  have f1926 := L2.K9_isin (True ∧ u1011 = 1) (sv v1000) (sv v1001) (sv v1062) (sv v1065) (sv v1067) (sv v1068) (sv v1069) (sv v1070) (sv v23) (sv v1072) v1073 v1074 v1075 (sv v1076) f1927 (L2.X2_push L2.sinI v483 (sv v1000) (sv v986) (sv v51) (sv v1061) (sv v51) (sv v1062) (L2.p_sel e_v1000) (L2.X2_push L2.sinI v985 (sv v986) (sv v971) (sv v51) (sv t971.1) (sv v51) (sv v1061) (L2.p_sel e_v986) (L2.p_sin e_t971_1) (L2.p_sin_cc (0) (0) e_v51 e_v51 (of_decide_eq_true rfl)) (L2.p_sel e_v1061)) (L2.p_sin_cc (0) (0) e_v51 e_v51 (of_decide_eq_true rfl)) (L2.p_sel e_v1062)) (L2.X2_push L2.sinI v483 (sv v1001) (sv v999) (sv v10) (sv v1064) (sv v51) (sv v1065) (L2.p_sel e_v1001) (L2.X2_push L2.sinI v998 (sv v999) (sv v987) (sv v10) (sv t987.1) (sv v51) (sv v1064) (L2.p_sel e_v999) (L2.p_sin e_t987_1) (L2.p_sin_cc (0) (843314857) e_v51 e_v10 (of_decide_eq_true rfl)) (L2.p_sel e_v1064)) (L2.p_sin_cc (0) (843314857) e_v51 e_v10 (of_decide_eq_true rfl)) (L2.p_sel e_v1065)) (L2.p_min e_v1066 (L2.p_sel e_v1067)) (L2.p_addc (-4) (L2.p_add_comm e_v1068) e_v18) (L2.p_max e_v1066 (L2.p_sel e_v1069)) (L2.p_addc (4) (L2.p_add_comm e_v1070) e_v21) e_v23 (L2.p_min e_v1071 (L2.p_sel e_v1072)) (L2.p_ltc (421657430) e_v26 e_v1073) (L2.p_clt (421657427) e_v28 e_v1074) e_v1075 (L2.p_sel e_v1076)
  have f1981 := L2.K11_qdiv (sv v1052) (sv v1059) (sv v1068) (sv v1076) v1077 v1078 (sv v51) v1079 (sv v1080) v1081 (sv v1082) (L2.p_clt (0) e_v51 e_v1077) e_v1078 e_v51 e_v1079 (L2.p_sel e_v1080) e_v1081 (L2.p_sel e_v1082)
  have f1993 := L2.K8_in_range ((True ∧ u1011 = 1) ∧ v1077 = 1) (sv v32) (sv v33) v34 (sv v10) v36 v37 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v35 e_v36) e_v37 (L2.X1_step (True ∧ u1011 = 1) v1077 v1078 v37 v1083 e_v1078 (L2.p_or_comm e_v1083) (L2.X1_step True u1011 v1010 v1083 v1084 (L2.p_not_not (L2.p_unot _)) e_v1084 (L2.X1_top _ k_v1084)))
  have f2007 := L2.K3_cos_lo (sv v33) (sv t33.2) (sv v112) (sv v95) (sv v114) (L2.p_cos e_t33_2) (L2.p_addc (-4) (L2.p_add_comm e_v112) e_v18) e_v95 (L2.p_max e_v113 (L2.p_sel e_v114))
  have f2021 := L2.K3_cos_hi (sv v32) (sv t32.2) (sv v278) (sv v23) (sv v280) (L2.p_cos e_t32_2) (L2.p_addc (4) (L2.p_add_comm e_v278) e_v21) e_v23 (L2.p_min e_v279 (L2.p_sel e_v280))
  have f1992 := L2.K10_icos ((True ∧ u1011 = 1) ∧ v1077 = 1) (sv v32) (sv v33) (sv v114) (sv v95) v115 (sv v116) (sv v280) (sv v23) v281 (sv v282) f1993 f2007 e_v95 (L2.p_clt (843314855) e_v98 e_v115) (L2.p_sel e_v116) f2021 e_v23 (L2.p_ltc (1) e_v105 e_v281) (L2.p_sel e_v282)
  have f1733 := L2.K26_dec_dir_x_full True (sv v2) (sv v3) u1006 (sv v1007) (sv v1000) (sv v1001) (sv v0) (sv v1) v1008 v1009 v1010 u1011 (sv v32) (sv v33) (sv v100) (sv v107) (sv v42) (sv v50) (sv v1039) u1040 (sv v1052) (sv v1059) (sv v1068) (sv v1076) (sv v1080) (sv v1082) v1078 v1077 (sv v116) (sv v282) (sv v51) v1079 v1085 v1086 v1087 v1088 v1089 v176 u183 v1090 v1091 v1092 v1093 v1094 v1095 v1096 (sv v1097) (sv v1098) v1099 v1100 v1101 (sv v1102) (sv v1103) (sv v1104) (sv v1105) v1106 (sv v1107) (sv v1108) v1109 v1110 v1111 v1112 v1113 v1114 (L2.p_ltc (843314857) e_v10 e_v1008) (L2.p_ltc (843314857) e_v10 e_v1009) e_v1010 (L2.p_unot _) f1742 f1745 f1786 f1825 f1869 f1926 f1981 (L2.p_not_not e_v1078) f1992 e_v51 e_v1079 e_v1085 e_v1086 e_v1087 (L2.p_and_comm e_v1088) e_v1089 e_v176 (L2.p_unot _) e_v1090 e_v1091 (L2.p_and_comm e_v1092) e_v1093 e_v1094 e_v1095 e_v1096 (L2.p_sel e_v1097) (L2.p_sel e_v1098) e_v1099 e_v1100 e_v1101 (L2.p_sel e_v1102) (L2.p_neg e_v51 e_v1103) e_v1104 (L2.p_mul_comm e_v1105) e_v1106 e_v1107 e_v1108 e_v1109 e_v1110 (L2.p_or_comm e_v1111) e_v1112 (L2.p_and_comm e_v1113) e_v1114
  let u1119 : ℤ := if v1118 = 1 then (sv v2) else (sv v3)
  let u1120 : ℕ := if (sv v473) < (sv v3) then 1 else 0
  let u1121 : ℕ := if u1120 = 1 then 0 else 1
  let u1122 : ℕ := if (sv v2) < (sv v473) then 1 else 0
  let u1123 : ℤ := if u1122 = 1 then (sv v473) else (sv v2)
  let u1124 : ℤ := if u1121 = 1 then (sv v3) else u1123
  let u1125 : ℤ := if v1114 = 1 then u1119 else (sv v3)
  have f2071 := L2.K27_corner (sv v2) (sv v3) v1114 (1 : ℕ) (sv v1115) (sv v1116) v1118 u1119 (sv v473) u1121 u1123 u1124 (sv v2) u1119 (sv v2) u1125 e_v1115 e_v1116 (L2.p_le e_v1117 e_v1118) rfl e_v473 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_max (L2.p_ult _ _) rfl) rfl (L2.p_sel_t _ _) (L2.p_sel_t _ _) (L2.p_sel_same _ _) rfl
  let u1126 : ℤ := (sv v4) + (sv v5)
  let u1127 : ℕ := if (sv v1116) < u1126 then 1 else 0
  let u1128 : ℕ := if u1127 = 1 then 0 else 1
  let u1129 : ℤ := if u1128 = 1 then (sv v4) else (sv v5)
  let u1133 : ℤ := if v1132 = 1 then (sv v473) else (sv v4)
  let u1134 : ℤ := if v1131 = 1 then (sv v5) else u1133
  have f2090 := L2.K27_corner_fixed (sv v4) (sv v5) (1 : ℕ) u1126 (sv v1116) u1128 u1129 (sv v473) v1131 u1133 u1134 u1134 (sv v5) rfl e_v1116 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) rfl e_v473 (L2.p_le e_v1130 e_v1131) (L2.p_max e_v1132 rfl) rfl (L2.p_sel_t _ _) (L2.p_sel_t _ _)
  have f2110 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f2109 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v17) (sv v19) (sv v20) (sv v22) (sv v23) (sv v25) v27 v29 v30 (sv v31) f2110 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v16 (L2.p_sel e_v17)) (L2.p_addc (-4) e_v19 e_v18) (L2.p_max e_v16 (L2.p_sel e_v20)) (L2.p_addc (4) e_v22 e_v21) e_v23 (L2.p_min e_v24 (L2.p_sel e_v25)) (L2.p_ltc (421657430) e_v26 e_v27) (L2.p_clt (421657427) e_v28 e_v29) e_v30 (L2.p_sel e_v31)
  have f2146 := L2.K5_ihalf (sv v2) u1125 (sv v32) (sv v1136) e_v32 (L2.X2_push (fun z : ℤ => (z + 1) / 2) v1114 u1125 u1119 (sv v3) (sv v1135) (sv v33) (sv v1136) rfl (L2.X2_push (fun z : ℤ => (z + 1) / 2) v1118 u1119 (sv v2) (sv v3) (sv v267) (sv v33) (sv v1135) rfl e_v267 e_v33 (L2.p_sel e_v1135)) e_v33 (L2.p_sel e_v1136))
  have f2156 := L2.K8_in_range True (sv v32) (sv v1136) v34 (sv v10) v1138 v1139 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v1137 e_v1138) e_v1139 (L2.X1_top _ k_v1139)
  have f2155 := L2.K9_isin True (sv v32) (sv v1136) (sv t32.1) (sv v1141) (sv v1143) (sv v1144) (sv v1145) (sv v1146) (sv v23) (sv v1148) v47 v1149 v1150 (sv v1151) f2156 (L2.p_sin e_t32_1) (L2.X2_push L2.sinI v1114 (sv v1136) (sv v1135) (sv v33) (sv v1140) (sv t33.1) (sv v1141) (L2.p_sel e_v1136) (L2.X2_push L2.sinI v1118 (sv v1135) (sv v267) (sv v33) (sv t267.1) (sv t33.1) (sv v1140) (L2.p_sel e_v1135) (L2.p_sin e_t267_1) (L2.p_sin e_t33_1) (L2.p_sel e_v1140)) (L2.p_sin e_t33_1) (L2.p_sel e_v1141)) (L2.p_min e_v1142 (L2.p_sel e_v1143)) (L2.p_addc (-4) (L2.p_add_comm e_v1144) e_v18) (L2.p_max e_v1142 (L2.p_sel e_v1145)) (L2.p_addc (4) (L2.p_add_comm e_v1146) e_v21) e_v23 (L2.p_min e_v1147 (L2.p_sel e_v1148)) (L2.p_ltc (421657430) e_v26 e_v47) (L2.p_clt (421657427) e_v28 e_v1149) e_v1150 (L2.p_sel e_v1151)
  let u1153 : ℕ := if v1152 = 1 then 0 else 1
  have f2198 := L2.K7_imul_full True (sv v19) (sv v31) (sv v1144) (sv v1151) (sv v51) v52 v53 v54 v55 v56 v57 v1152 u1153 v1154 v1155 v1156 v1157 v1158 v1159 v1160 (sv v1161) v1162 v1163 v1164 (sv v1165) v1166 v1167 (sv v1168) v1169 v1170 (sv v1171) (sv v1173) (sv v1175) (sv v1177) (sv v1179) (sv v1181) (sv v1183) (sv v1184) (sv v1185) e_v51 e_v52 e_v53 e_v54 e_v55 (L2.p_and_comm e_v56) e_v57 e_v1152 (L2.p_unot _) e_v1154 e_v1155 (L2.p_and_comm e_v1156) e_v1157 e_v1158 e_v1159 e_v1160 (L2.p_sel e_v1161) e_v1162 e_v1163 e_v1164 (L2.p_sel e_v1165) e_v1166 e_v1167 (L2.p_sel e_v1168) e_v1169 e_v1170 (L2.p_sel e_v1171) (L2.p_mul (L2.p_mul_comm e_v1172) e_v1173) (L2.p_mulc (L2.p_mul_comm e_v1174) e_v1175) (L2.p_mul (L2.p_mul_comm e_v1176) e_v1177) (L2.p_mulc (L2.p_mul_comm e_v1178) e_v1179) (L2.p_min e_v1180 (L2.p_sel e_v1181)) (L2.p_max e_v1182 (L2.p_sel e_v1183)) (L2.p_sel e_v1184) (L2.p_sel e_v1185)
  have f2108 := L2.K14_iso_base_a True (sv v2) u1125 (sv v0) (sv v1) (sv v19) (sv v31) (sv v32) (sv v1136) (sv v1144) (sv v1151) (sv v1184) (sv v1185) v1186 f2109 f2146 f2155 f2198 (L2.p_clt (-1) e_v8 e_v1186) (L2.X1_top _ k_v1186)
  have f2248 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f2258 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v94) (sv v95) (sv v97) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v94) e_v18) e_v95 (L2.p_max e_v96 (L2.p_sel e_v97))
  have f2272 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v102) (sv v23) (sv v104) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v102) e_v21) e_v23 (L2.p_min e_v103 (L2.p_sel e_v104))
  have f2247 := L2.K10_icos True (sv v0) (sv v1) (sv v97) (sv v95) v99 (sv v100) (sv v104) (sv v23) v106 (sv v107) f2248 f2258 e_v95 (L2.p_clt (843314855) e_v98 e_v99) (L2.p_sel e_v100) f2272 e_v23 (L2.p_ltc (1) e_v105 e_v106) (L2.p_sel e_v107)
  have f2287 := L2.K5_ihalf u1125 u1125 (sv v1188) (sv v1136) (L2.X2_push (fun z : ℤ => z / 2) v1114 u1125 u1119 (sv v3) (sv v1187) (sv v108) (sv v1188) rfl (L2.X2_push (fun z : ℤ => z / 2) v1118 u1119 (sv v2) (sv v3) (sv v32) (sv v108) (sv v1187) rfl e_v32 e_v108 (L2.p_sel e_v1187)) e_v108 (L2.p_sel e_v1188)) (L2.X2_push (fun z : ℤ => (z + 1) / 2) v1114 u1125 u1119 (sv v3) (sv v1135) (sv v33) (sv v1136) rfl (L2.X2_push (fun z : ℤ => (z + 1) / 2) v1118 u1119 (sv v2) (sv v3) (sv v267) (sv v33) (sv v1135) rfl e_v267 e_v33 (L2.p_sel e_v1135)) e_v33 (L2.p_sel e_v1136))
  have f2303 := L2.K8_in_range True (sv v1188) (sv v1136) v1189 (sv v10) v1138 v1190 (L2.p_clt (-1) e_v8 e_v1189) e_v10 (L2.p_le e_v1137 e_v1138) (L2.p_and_comm e_v1190) (L2.X1_top _ k_v1190)
  let u1191 : ℤ := if v1118 = 1 then u271 else (sv t33.2)
  let u1192 : ℤ := if v1114 = 1 then u1191 else (sv t33.2)
  let u1193 : ℤ := (sv v18) + u1192
  let u1194 : ℕ := if u1193 < (sv v95) then 1 else 0
  let u1195 : ℤ := if u1194 = 1 then (sv v95) else u1193
  have f2313 := L2.K3_cos_lo (sv v1136) u1192 u1193 (sv v95) u1195 (L2.X2_push L2.cosI v1114 (sv v1136) (sv v1135) (sv v33) u1191 (sv t33.2) u1192 (L2.p_sel e_v1136) (L2.X2_push L2.cosI v1118 (sv v1135) (sv v267) (sv v33) u271 (sv t33.2) u1191 (L2.p_sel e_v1135) rfl (L2.p_cos e_t33_2) rfl) (L2.p_cos e_t33_2) rfl) (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u1196 : ℕ := if (sv v98) < (sv v1136) then 1 else 0
  let u1197 : ℤ := if u1196 = 1 then (sv v95) else u1195
  let u1198 : ℤ := if v1118 = 1 then (sv t32.2) else u117
  let u1199 : ℤ := if v1114 = 1 then u1198 else u117
  let u1200 : ℤ := (sv v21) + u1199
  let u1201 : ℕ := if u1200 < (sv v23) then 1 else 0
  let u1202 : ℤ := if u1201 = 1 then u1200 else (sv v23)
  have f2333 := L2.K3_cos_hi (sv v1188) u1199 u1200 (sv v23) u1202 (L2.X2_push L2.cosI v1114 (sv v1188) (sv v1187) (sv v108) u1198 u117 u1199 (L2.p_sel e_v1188) (L2.X2_push L2.cosI v1118 (sv v1187) (sv v32) (sv v108) (sv t32.2) u117 u1198 (L2.p_sel e_v1187) (L2.p_cos e_t32_2) rfl rfl) rfl rfl) (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u1203 : ℕ := if (sv v1188) < (sv v105) then 1 else 0
  let u1204 : ℤ := if u1203 = 1 then (sv v23) else u1202
  have f2302 := L2.K10_icos True (sv v1188) (sv v1136) u1195 (sv v95) u1196 u1197 u1202 (sv v23) u1203 u1204 f2303 f2313 e_v95 (L2.p_clt (843314855) e_v98 (L2.p_ult _ _)) rfl f2333 e_v23 (L2.p_ltc (1) e_v105 (L2.p_ult _ _)) rfl
  have f2354 := L2.K8_in_range True (sv v1188) (sv v1136) v1189 (sv v10) v1138 v1190 (L2.p_clt (-1) e_v8 e_v1189) e_v10 (L2.p_le e_v1137 e_v1138) (L2.p_and_comm e_v1190) (L2.X1_top _ k_v1190)
  let u1205 : ℤ := if v1118 = 1 then (sv t32.1) else u123
  let u1206 : ℤ := if v1114 = 1 then u1205 else u123
  let u1207 : ℕ := if u1206 < (sv v1141) then 1 else 0
  let u1208 : ℤ := if u1207 = 1 then u1206 else (sv v1141)
  let u1209 : ℤ := (sv v18) + u1208
  let u1210 : ℤ := if u1207 = 1 then (sv v1141) else u1206
  let u1211 : ℤ := (sv v21) + u1210
  let u1212 : ℕ := if u1211 < (sv v23) then 1 else 0
  let u1213 : ℤ := if u1212 = 1 then u1211 else (sv v23)
  let u1214 : ℕ := if (sv v1188) < (sv v26) then 1 else 0
  let u1215 : ℕ := if v1149 = 1 ∧ u1214 = 1 then 1 else 0
  let u1216 : ℤ := if u1215 = 1 then (sv v23) else u1213
  have f2353 := L2.K9_isin True (sv v1188) (sv v1136) u1206 (sv v1141) u1208 u1209 u1210 u1211 (sv v23) u1213 u1214 v1149 u1215 u1216 f2354 (L2.X2_push L2.sinI v1114 (sv v1188) (sv v1187) (sv v108) u1205 u123 u1206 (L2.p_sel e_v1188) (L2.X2_push L2.sinI v1118 (sv v1187) (sv v32) (sv v108) (sv t32.1) u123 u1205 (L2.p_sel e_v1187) (L2.p_sin e_t32_1) rfl rfl) rfl rfl) (L2.X2_push L2.sinI v1114 (sv v1136) (sv v1135) (sv v33) (sv v1140) (sv t33.1) (sv v1141) (L2.p_sel e_v1136) (L2.X2_push L2.sinI v1118 (sv v1135) (sv v267) (sv v33) (sv t267.1) (sv t33.1) (sv v1140) (L2.p_sel e_v1135) (L2.p_sin e_t267_1) (L2.p_sin e_t33_1) (L2.p_sel e_v1140)) (L2.p_sin e_t33_1) (L2.p_sel e_v1141)) (L2.p_min (L2.p_ult _ _) rfl) (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) (L2.p_max (L2.p_ult _ _) rfl) (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl) (L2.p_ltc (421657430) e_v26 (L2.p_ult _ _)) (L2.p_clt (421657427) e_v28 e_v1149) (L2.p_and_comm (L2.p_uand _ _)) rfl
  let u1217 : ℕ := if u1209 < (sv v51) then 1 else 0
  let u1218 : ℕ := if u1217 = 1 then 0 else 1
  let u1219 : ℕ := if (sv v51) < u1216 then 1 else 0
  let u1220 : ℕ := if u1219 = 1 then 0 else 1
  let u1221 : ℕ := if u1217 = 1 ∧ u1220 = 1 then 1 else 0
  let u1222 : ℕ := if u1217 = 1 ∧ u1219 = 1 then 1 else 0
  let u1223 : ℕ := if v139 = 1 ∧ u1222 = 1 then 1 else 0
  let u1224 : ℕ := if v135 = 1 ∧ u1222 = 1 then 1 else 0
  let u1225 : ℕ := if u1221 = 1 ∨ u1224 = 1 then 1 else 0
  let u1226 : ℤ := if u1225 = 1 then (sv v107) else (sv v100)
  let u1227 : ℕ := if u1221 = 1 then 0 else 1
  let u1228 : ℕ := if v139 = 1 ∧ u1227 = 1 then 1 else 0
  let u1229 : ℕ := if v138 = 1 ∨ u1228 = 1 then 1 else 0
  let u1230 : ℤ := if u1229 = 1 then u1216 else u1209
  let u1231 : ℕ := if v138 = 1 ∧ u1222 = 1 then 1 else 0
  let u1232 : ℕ := if u1221 = 1 ∨ u1231 = 1 then 1 else 0
  let u1233 : ℤ := if u1232 = 1 then (sv v100) else (sv v107)
  let u1234 : ℕ := if v139 = 1 ∧ u1221 = 1 then 1 else 0
  let u1235 : ℕ := if v138 = 1 ∨ u1234 = 1 then 1 else 0
  let u1236 : ℤ := if u1235 = 1 then u1209 else u1216
  let u1237 : ℤ := u1226 * u1230
  let u1238 : ℤ := u1237 / 2 ^ 28
  let u1239 : ℤ := u1233 * u1236
  let u1240 : ℤ := -((-u1239) / 2 ^ 28)
  let u1241 : ℤ := (sv v107) * u1209
  let u1242 : ℤ := u1241 / 2 ^ 28
  let u1243 : ℤ := (sv v100) * u1209
  let u1244 : ℤ := -((-u1243) / 2 ^ 28)
  let u1245 : ℕ := if u1238 < u1242 then 1 else 0
  let u1246 : ℤ := if u1245 = 1 then u1238 else u1242
  let u1247 : ℕ := if u1240 < u1244 then 1 else 0
  let u1248 : ℤ := if u1247 = 1 then u1244 else u1240
  let u1249 : ℤ := if u1223 = 1 then u1246 else u1238
  let u1250 : ℤ := if u1223 = 1 then u1248 else u1240
  have f2402 := L2.K7_imul_full True (sv v100) (sv v107) u1209 u1216 (sv v51) v134 v135 v136 v137 v138 v139 u1217 u1218 u1219 u1220 u1221 u1222 u1223 u1224 u1225 u1226 u1227 u1228 u1229 u1230 u1231 u1232 u1233 u1234 u1235 u1236 u1238 u1240 u1242 u1244 u1246 u1248 u1249 u1250 e_v51 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 (L2.p_ult _ _) (L2.p_unot _) (L2.p_ult _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uand _ _) (L2.p_uand _ _) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_unot _) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl) (L2.p_mul rfl rfl) (L2.p_mulc rfl rfl) (L2.p_min (L2.p_ult _ _) rfl) (L2.p_max (L2.p_ult _ _) rfl) rfl rfl
  let u1251 : ℕ := if (sv v51) < u1249 then 1 else 0
  let u1252 : ℕ := if u1251 = 1 then 0 else 1
  let u1253 : ℕ := if u1197 < (sv v51) then 1 else 0
  let u1254 : ℤ := if u1253 = 1 then u1249 else u1250
  let u1255 : ℕ := if u1204 < (sv v51) then 1 else 0
  let u1256 : ℤ := if u1255 = 1 then u1250 else u1249
  have f2446 := L2.K11_qdiv u1197 u1204 u1249 u1250 u1251 u1252 (sv v51) u1253 u1254 u1255 u1256 (L2.p_clt (0) e_v51 (L2.p_ult _ _)) (L2.p_unot _) e_v51 (L2.p_ult _ _) rfl (L2.p_ult _ _) rfl
  let u1257 : ℤ := (sv v51) - u1197
  let u1258 : ℤ := if u1253 = 1 then u1257 else u1197
  let u1259 : ℤ := 0
  let u1260 : ℕ := if u1253 = 1 then 0 else 1
  let u1261 : ℤ := L2.cosI u1259
  let u1262 : ℤ := (sv v18) + u1261
  let u1263 : ℕ := if u1262 < (sv v95) then 1 else 0
  let u1264 : ℤ := if u1263 = 1 then (sv v95) else u1262
  have f2464 := L2.K3_cos_lo u1259 u1261 u1262 (sv v95) u1264 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u1265 : ℤ := (sv v21) + u1261
  let u1266 : ℕ := if u1265 < (sv v23) then 1 else 0
  let u1267 : ℤ := if u1266 = 1 then u1265 else (sv v23)
  have f2473 := L2.K3_cos_hi u1259 u1261 u1265 (sv v23) u1267 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u1268 : ℤ := L2.sinI u1259
  let u1269 : ℤ := (sv v21) + u1268
  let u1270 : ℕ := if u1269 < (sv v23) then 1 else 0
  let u1271 : ℤ := if u1270 = 1 then u1269 else (sv v23)
  have f2482 := L2.K3_sin_hi u1259 u1268 u1269 (sv v23) u1271 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u1272 : ℤ := (sv v18) + u1268
  have f2491 := L2.K3_sin_lo u1259 u1268 u1272 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u1273 : ℤ := if u1260 = 1 then u1264 else u1267
  let u1274 : ℤ := if u1260 = 1 then u1271 else u1272
  let u1275 : ℤ := u1254 * u1274
  let u1276 : ℤ := u1258 * u1273
  let u1277 : ℕ := if u1276 < u1275 then 1 else 0
  let u1278 : ℕ := if u1277 = 1 then 0 else 1
  let u1279 : ℕ := if u1275 < u1276 then 1 else 0
  let u1280 : ℕ := if u1279 = 1 then 0 else 1
  let u1281 : ℕ := if (sv v51) < u1259 then 1 else 0
  let u1282 : ℕ := if u1281 = 1 then 0 else 1
  let u1283 : ℕ := if (sv v206) < u1259 then 1 else 0
  let u1284 : ℕ := if u1283 = 1 then 0 else 1
  let u1285 : ℕ := if (sv v8) < u1264 then 1 else 0
  let u1286 : ℕ := if u1278 = 1 ∧ u1285 = 1 then 1 else 0
  let u1287 : ℕ := if u1284 = 1 ∧ u1286 = 1 then 1 else 0
  let u1288 : ℕ := if u1282 = 1 ∨ u1287 = 1 then 1 else 0
  let u1289 : ℕ := if u1259 < (sv v213) then 1 else 0
  let u1290 : ℕ := if u1289 = 1 then 0 else 1
  let u1291 : ℕ := if u1280 = 1 ∨ u1290 = 1 then 1 else 0
  let u1292 : ℕ := if u1260 = 1 ∧ u1288 = 1 then 1 else 0
  let u1293 : ℕ := if u1253 = 1 ∧ u1291 = 1 then 1 else 0
  let u1294 : ℕ := if u1292 = 1 ∨ u1293 = 1 then 1 else 0
  let u1295 : ℤ := (sv v51) - u1259
  let u1296 : ℤ := if u1253 = 1 then u1295 else u1259
  let u1297 : ℤ := if u1294 = 1 then u1296 else u222
  have f2457 := L2.K12_atan_lo u1197 u1254 (sv v51) u1253 u1257 u1258 u1259 u1260 u1264 u1267 u1271 u1272 u1273 u1274 u1275 u1276 u1278 u1280 u1281 u1282 (sv v206) u1284 u1285 u1286 u1287 u1288 (sv v213) u1290 u1291 u1292 u1253 u1293 u1294 u1295 u1296 u222 u1297 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f2464 f2473 f2482 f2491 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v206 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v213 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  let u1298 : ℤ := (sv v51) - u1204
  let u1299 : ℤ := if u1255 = 1 then u1298 else u1204
  let u1300 : ℤ := 0
  let u1301 : ℤ := L2.cosI u1300
  let u1302 : ℤ := (sv v18) + u1301
  let u1303 : ℕ := if u1302 < (sv v95) then 1 else 0
  let u1304 : ℤ := if u1303 = 1 then (sv v95) else u1302
  have f2537 := L2.K3_cos_lo u1300 u1301 u1302 (sv v95) u1304 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u1305 : ℤ := (sv v21) + u1301
  let u1306 : ℕ := if u1305 < (sv v23) then 1 else 0
  let u1307 : ℤ := if u1306 = 1 then u1305 else (sv v23)
  have f2546 := L2.K3_cos_hi u1300 u1301 u1305 (sv v23) u1307 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u1308 : ℤ := L2.sinI u1300
  let u1309 : ℤ := (sv v21) + u1308
  let u1310 : ℕ := if u1309 < (sv v23) then 1 else 0
  let u1311 : ℤ := if u1310 = 1 then u1309 else (sv v23)
  have f2555 := L2.K3_sin_hi u1300 u1308 u1309 (sv v23) u1311 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  let u1312 : ℤ := (sv v18) + u1308
  have f2564 := L2.K3_sin_lo u1300 u1308 u1312 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  let u1313 : ℤ := if u1255 = 1 then u1304 else u1307
  let u1314 : ℤ := if u1255 = 1 then u1311 else u1312
  let u1315 : ℤ := u1256 * u1314
  let u1316 : ℤ := u1299 * u1313
  let u1317 : ℕ := if u1316 < u1315 then 1 else 0
  let u1318 : ℕ := if u1317 = 1 then 0 else 1
  let u1319 : ℕ := if u1315 < u1316 then 1 else 0
  let u1320 : ℕ := if u1319 = 1 then 0 else 1
  let u1321 : ℕ := if (sv v51) < u1300 then 1 else 0
  let u1322 : ℕ := if u1321 = 1 then 0 else 1
  let u1323 : ℕ := if (sv v206) < u1300 then 1 else 0
  let u1324 : ℕ := if u1323 = 1 then 0 else 1
  let u1325 : ℕ := if (sv v8) < u1304 then 1 else 0
  let u1326 : ℕ := if u1318 = 1 ∧ u1325 = 1 then 1 else 0
  let u1327 : ℕ := if u1324 = 1 ∧ u1326 = 1 then 1 else 0
  let u1328 : ℕ := if u1322 = 1 ∨ u1327 = 1 then 1 else 0
  let u1329 : ℕ := if u1300 < (sv v213) then 1 else 0
  let u1330 : ℕ := if u1329 = 1 then 0 else 1
  let u1331 : ℕ := if u1320 = 1 ∨ u1330 = 1 then 1 else 0
  let u1332 : ℕ := if u1255 = 1 ∧ u1328 = 1 then 1 else 0
  let u1333 : ℕ := if u1255 = 1 then 0 else 1
  let u1334 : ℕ := if u1331 = 1 ∧ u1333 = 1 then 1 else 0
  let u1335 : ℕ := if u1332 = 1 ∨ u1334 = 1 then 1 else 0
  let u1336 : ℤ := (sv v51) - u1300
  let u1337 : ℤ := if u1255 = 1 then u1336 else u1300
  let u1338 : ℤ := if u1335 = 1 then u1337 else (sv v213)
  have f2531 := L2.K12_atan_hi u1204 u1256 (sv v51) u1255 u1298 u1299 u1300 u1304 u1307 u1311 u1312 u1313 u1314 u1315 u1316 u1318 u1320 u1321 u1322 (sv v206) u1324 u1325 u1326 u1327 u1328 (sv v213) u1330 u1331 u1332 u1333 u1334 u1335 u1336 u1337 (sv v213) u1338 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) f2537 f2546 f2555 f2564 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v206 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v213 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_unot _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) rfl rfl e_v213 rfl
  let u1339 : ℤ := if u1252 = 1 then u222 else u1297
  let u1340 : ℤ := if u1252 = 1 then (sv v213) else u1338
  have f2286 := L2.K19_iso_angle_pt True u1125 (sv v100) (sv v107) (sv v1188) (sv v1136) u1197 u1204 u1209 u1216 u1249 u1250 u1254 u1256 u1252 u1251 u1297 u1338 u222 (sv v213) u1339 u1340 f2287 f2302 f2353 f2402 f2446 (L2.p_not_not (L2.p_unot _)) f2457 f2531 rfl e_v213 rfl rfl
  have f2609 := L2.K5_ihalf (sv v2) (sv v2) (sv v32) (sv v267) e_v32 e_v267
  have f2613 := L2.K8_in_range True (sv v32) (sv v267) v34 (sv v10) v269 v270 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v268 e_v269) e_v270 (L2.X1_top _ k_v270)
  have f2623 := L2.K3_cos_lo (sv v267) u271 u272 (sv v95) u274 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  have f2637 := L2.K3_cos_hi (sv v32) (sv t32.2) (sv v278) (sv v23) (sv v280) (L2.p_cos e_t32_2) (L2.p_addc (4) (L2.p_add_comm e_v278) e_v21) e_v23 (L2.p_min e_v279 (L2.p_sel e_v280))
  have f2612 := L2.K10_icos True (sv v32) (sv v267) u274 (sv v95) u275 u276 (sv v280) (sv v23) v281 (sv v282) f2613 f2623 e_v95 (L2.p_clt (843314855) e_v98 (L2.p_ult _ _)) rfl f2637 e_v23 (L2.p_ltc (1) e_v105 e_v281) (L2.p_sel e_v282)
  have f2652 := L2.K8_in_range True (sv v32) (sv v267) v34 (sv v10) v269 v270 (L2.p_clt (-1) e_v8 e_v34) e_v10 (L2.p_le e_v268 e_v269) e_v270 (L2.X1_top _ k_v270)
  have f2651 := L2.K9_isin True (sv v32) (sv v267) (sv t32.1) (sv t267.1) (sv v285) (sv v286) (sv v287) (sv v288) (sv v23) (sv v290) v47 v291 v292 (sv v293) f2652 (L2.p_sin e_t32_1) (L2.p_sin e_t267_1) (L2.p_min e_v284 (L2.p_sel e_v285)) (L2.p_addc (-4) (L2.p_add_comm e_v286) e_v18) (L2.p_max e_v284 (L2.p_sel e_v287)) (L2.p_addc (4) (L2.p_add_comm e_v288) e_v21) e_v23 (L2.p_min e_v289 (L2.p_sel e_v290)) (L2.p_ltc (421657430) e_v26 e_v47) (L2.p_clt (421657427) e_v28 e_v291) e_v292 (L2.p_sel e_v293)
  have f2688 := L2.K7_imul_full True (sv v100) (sv v107) (sv v286) (sv v293) (sv v51) v134 v135 v136 v137 v138 v139 v294 u295 v296 v297 v298 v299 v300 v301 v302 (sv v303) v304 v305 v306 (sv v307) v308 v309 (sv v310) v311 v312 (sv v313) (sv v315) (sv v317) (sv v319) (sv v321) (sv v323) (sv v325) (sv v326) (sv v327) e_v51 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 e_v294 (L2.p_unot _) e_v296 e_v297 (L2.p_and_comm e_v298) e_v299 e_v300 e_v301 e_v302 (L2.p_sel e_v303) e_v304 e_v305 e_v306 (L2.p_sel e_v307) e_v308 e_v309 (L2.p_sel e_v310) e_v311 e_v312 (L2.p_sel e_v313) (L2.p_mul (L2.p_mul_comm e_v314) e_v315) (L2.p_mulc (L2.p_mul_comm e_v316) e_v317) (L2.p_mul (L2.p_mul_comm e_v318) e_v319) (L2.p_mulc (L2.p_mul_comm e_v320) e_v321) (L2.p_min e_v322 (L2.p_sel e_v323)) (L2.p_max e_v324 (L2.p_sel e_v325)) (L2.p_sel e_v326) (L2.p_sel e_v327)
  have f2732 := L2.K11_qdiv u276 (sv v282) (sv v326) (sv v327) v328 v329 (sv v51) u330 u331 v332 (sv v333) (L2.p_clt (0) e_v51 e_v328) e_v329 e_v51 (L2.p_ult _ _) rfl e_v332 (L2.p_sel e_v333)
  have f2750 := L2.K3_cos_lo u336 u338 u339 (sv v95) u341 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  have f2759 := L2.K3_cos_hi u336 u338 u342 (sv v23) u344 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  have f2768 := L2.K3_sin_hi u336 u345 u346 (sv v23) u348 rfl (L2.p_addc (4) (L2.p_add_comm rfl) e_v21) e_v23 (L2.p_min (L2.p_ult _ _) rfl)
  have f2777 := L2.K3_sin_lo u336 u345 u349 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18)
  have f2743 := L2.K12_atan_lo u276 u331 (sv v51) u330 u334 u335 u336 u337 u341 u344 u348 u349 u350 u351 u352 u353 u355 u357 u358 u359 (sv v206) u361 u362 u363 u364 u365 (sv v213) u367 u368 u369 u330 u370 u371 u372 u373 u222 u374 e_v51 (L2.p_ult _ _) rfl rfl (le_refl (0 : ℤ)) (L2.p_unot _) f2750 f2759 f2768 f2777 rfl rfl (L2.p_mul_comm rfl) rfl (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_ult _ _) (L2.p_unot _) e_v206 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_clt (-1) e_v8 (L2.p_ult _ _)) (L2.p_uand _ _) (L2.p_and_comm (L2.p_uand _ _)) (L2.p_uor _ _) e_v213 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_or_comm (L2.p_uor _ _)) (L2.p_uand _ _) (L2.p_not_not (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl rfl rfl rfl
  have f2823 := L2.K3_cos_lo (sv v377) (sv t377.2) (sv v379) (sv v95) (sv v381) (L2.p_cos e_t377_2) (L2.p_addc (-4) (L2.p_add_comm e_v379) e_v18) e_v95 (L2.p_max e_v380 (L2.p_sel e_v381))
  have f2832 := L2.K3_cos_hi (sv v377) (sv t377.2) (sv v382) (sv v23) (sv v384) (L2.p_cos e_t377_2) (L2.p_addc (4) (L2.p_add_comm e_v382) e_v21) e_v23 (L2.p_min e_v383 (L2.p_sel e_v384))
  have f2841 := L2.K3_sin_hi (sv v377) (sv t377.1) (sv v386) (sv v23) (sv v388) (L2.p_sin e_t377_1) (L2.p_addc (4) (L2.p_add_comm e_v386) e_v21) e_v23 (L2.p_min e_v387 (L2.p_sel e_v388))
  have f2850 := L2.K3_sin_lo (sv v377) (sv t377.1) (sv v389) (L2.p_sin e_t377_1) (L2.p_addc (-4) (L2.p_add_comm e_v389) e_v18)
  have f2817 := L2.K12_atan_hi (sv v282) (sv v333) (sv v51) v332 (sv v375) (sv v376) (sv v377) (sv v381) (sv v384) (sv v388) (sv v389) (sv v390) (sv v391) (sv v392) (sv v393) v395 v397 v398 v399 (sv v206) v401 v402 v403 v404 v405 (sv v213) v407 v408 v409 v410 v411 v412 (sv v413) (sv v414) (sv v213) (sv v415) e_v51 e_v332 e_v375 (L2.p_sel e_v376) (L2.p_hint e_v377) f2823 f2832 f2841 f2850 (L2.p_sel e_v390) (L2.p_sel e_v391) (L2.p_mul_comm e_v392) (L2.p_mul_comm e_v393) (L2.p_le e_v394 e_v395) (L2.p_le e_v396 e_v397) e_v398 e_v399 e_v206 (L2.p_le e_v400 e_v401) (L2.p_clt (-1) e_v8 e_v402) e_v403 (L2.p_and_comm e_v404) e_v405 e_v213 (L2.p_le e_v406 e_v407) (L2.p_or_comm e_v408) e_v409 e_v410 (L2.p_and_comm e_v411) e_v412 e_v413 (L2.p_sel e_v414) e_v213 (L2.p_sel e_v415)
  have f2608 := L2.K19_iso_angle_pt True (sv v2) (sv v100) (sv v107) (sv v32) (sv v267) u276 (sv v282) (sv v286) (sv v293) (sv v326) (sv v327) u331 (sv v333) v329 v328 u374 (sv v415) u222 (sv v213) u416 (sv v417) f2609 f2612 f2651 f2688 f2732 (L2.p_not_not e_v329) f2743 f2817 rfl e_v213 rfl (L2.p_sel e_v417)
  have f2246 := L2.K20_iso_angle True (sv v2) u1125 (sv v0) (sv v1) (sv v100) (sv v107) u1339 u1340 u1252 u416 (sv v417) v329 f2247 f2286 f2608
  have f2896 := L2.K8_in_range True (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_top _ k_v13)
  have f2895 := L2.K9_isin True (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v17) (sv v19) (sv v20) (sv v22) (sv v23) (sv v25) v27 v29 v30 (sv v31) f2896 (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_min e_v16 (L2.p_sel e_v17)) (L2.p_addc (-4) e_v19 e_v18) (L2.p_max e_v16 (L2.p_sel e_v20)) (L2.p_addc (4) e_v22 e_v21) e_v23 (L2.p_min e_v24 (L2.p_sel e_v25)) (L2.p_ltc (421657430) e_v26 e_v27) (L2.p_clt (421657427) e_v28 e_v29) e_v30 (L2.p_sel e_v31)
  have f2932 := L2.K5_ihalf u1134 (sv v5) (sv v1343) (sv v419) (L2.X2_push (fun z : ℤ => z / 2) v1131 u1134 (sv v5) u1133 (sv v1341) (sv v1342) (sv v1343) rfl e_v1341 (L2.X2_push (fun z : ℤ => z / 2) v1132 u1133 (sv v473) (sv v4) (sv v206) (sv v418) (sv v1342) rfl (L2.p_half_cc (421657428) (843314856) e_v206 e_v473 (by norm_num)) e_v418 (L2.p_sel e_v1342)) (L2.p_sel e_v1343)) e_v419
  have f2943 := L2.K8_in_range True (sv v1343) (sv v419) v1344 (sv v10) v422 v1345 (L2.p_clt (-1) e_v8 e_v1344) e_v10 (L2.p_le e_v421 e_v422) (L2.p_and_comm e_v1345) (L2.X1_top _ k_v1345)
  have f2942 := L2.K9_isin True (sv v1343) (sv v419) (sv t1343.1) (sv t419.1) (sv v1348) (sv v1349) (sv v1350) (sv v1351) (sv v23) (sv v1353) v1354 v434 v1355 (sv v1356) f2943 (L2.p_sin e_t1343_1) (L2.p_sin e_t419_1) (L2.p_min e_v1347 (L2.p_sel e_v1348)) (L2.p_addc (-4) (L2.p_add_comm e_v1349) e_v18) (L2.p_max e_v1347 (L2.p_sel e_v1350)) (L2.p_addc (4) (L2.p_add_comm e_v1351) e_v21) e_v23 (L2.p_min e_v1352 (L2.p_sel e_v1353)) (L2.p_ltc (421657430) e_v26 e_v1354) (L2.p_clt (421657427) e_v28 e_v434) (L2.p_and_comm e_v1355) (L2.p_sel e_v1356)
  let u1358 : ℕ := if v1357 = 1 then 0 else 1
  have f2979 := L2.K7_imul_full True (sv v19) (sv v31) (sv v1349) (sv v1356) (sv v51) v52 v53 v54 v55 v56 v57 v1357 u1358 v1359 v1360 v1361 v1362 v1363 v1364 v1365 (sv v1366) v1367 v1368 v1369 (sv v1370) v1371 v1372 (sv v1373) v1374 v1375 (sv v1376) (sv v1378) (sv v1380) (sv v1382) (sv v1384) (sv v1386) (sv v1388) (sv v1389) (sv v1390) e_v51 e_v52 e_v53 e_v54 e_v55 (L2.p_and_comm e_v56) e_v57 e_v1357 (L2.p_unot _) e_v1359 e_v1360 (L2.p_and_comm e_v1361) e_v1362 e_v1363 e_v1364 e_v1365 (L2.p_sel e_v1366) e_v1367 e_v1368 e_v1369 (L2.p_sel e_v1370) e_v1371 e_v1372 (L2.p_sel e_v1373) e_v1374 e_v1375 (L2.p_sel e_v1376) (L2.p_mul (L2.p_mul_comm e_v1377) e_v1378) (L2.p_mulc (L2.p_mul_comm e_v1379) e_v1380) (L2.p_mul (L2.p_mul_comm e_v1381) e_v1382) (L2.p_mulc (L2.p_mul_comm e_v1383) e_v1384) (L2.p_min e_v1385 (L2.p_sel e_v1386)) (L2.p_max e_v1387 (L2.p_sel e_v1388)) (L2.p_sel e_v1389) (L2.p_sel e_v1390)
  have f2894 := L2.K14_iso_base_a True u1134 (sv v5) (sv v0) (sv v1) (sv v19) (sv v31) (sv v1343) (sv v419) (sv v1349) (sv v1356) (sv v1389) (sv v1390) v1391 f2895 f2932 f2942 f2979 (L2.p_clt (-1) e_v8 e_v1391) (L2.X1_top _ k_v1391)
  have f3029 := L2.K15_a_open (sv v1389) (sv v1390) v1392 v1393 v1394 (L2.p_clt (0) e_v51 e_v1392) (L2.p_ltc (268435456) e_v23 e_v1393) e_v1394
  have f3037 := L2.K15_a_open (sv v1184) (sv v1185) v1395 v1396 v1397 (L2.p_clt (0) e_v51 e_v1395) (L2.p_ltc (268435456) e_v23 e_v1396) e_v1397
  have f3046 := L2.K15_in_open (sv v0) (sv v1) v472 v474 v475 (L2.p_clt (0) e_v51 e_v472) (L2.p_ltc (843314856) e_v473 e_v474) e_v475
  have f3045 := L2.K15_a_open_plain (sv v0) (sv v1) v475 f3046
  have f3056 := L2.K16_a_cos (True ∧ v1399 = 1) (sv v1389) (sv v1390) (sv v23) (sv v1401) (sv v1402) (sv v1403) (sv v95) (sv v1405) (sv v1407) (sv v1408) (sv v1409) e_v23 (L2.p_mulc e_v1400 e_v1401) e_v1402 e_v1403 e_v95 (L2.p_max e_v1404 (L2.p_sel e_v1405)) (L2.p_mul e_v1406 e_v1407) e_v1408 e_v1409
  have f3072 := L2.K8_in_range (True ∧ v1399 = 1) (sv v0) (sv v1) v9 (sv v10) v12 v13 (L2.p_clt (-1) e_v8 e_v9) e_v10 (L2.p_le e_v11 e_v12) e_v13 (L2.X1_step True v1399 v1410 v13 v1411 e_v1410 (L2.p_or_comm e_v1411) (L2.X1_top _ k_v1411))
  have f3084 := L2.K3_cos_lo (sv v1) (sv t1.2) (sv v94) (sv v95) (sv v97) (L2.p_cos e_t1_2) (L2.p_addc (-4) (L2.p_add_comm e_v94) e_v18) e_v95 (L2.p_max e_v96 (L2.p_sel e_v97))
  have f3098 := L2.K3_cos_hi (sv v0) (sv t0.2) (sv v102) (sv v23) (sv v104) (L2.p_cos e_t0_2) (L2.p_addc (4) (L2.p_add_comm e_v102) e_v21) e_v23 (L2.p_min e_v103 (L2.p_sel e_v104))
  have f3071 := L2.K10_icos (True ∧ v1399 = 1) (sv v0) (sv v1) (sv v97) (sv v95) v99 (sv v100) (sv v104) (sv v23) v106 (sv v107) f3072 f3084 e_v95 (L2.p_clt (843314855) e_v98 e_v99) (L2.p_sel e_v100) f3098 e_v23 (L2.p_ltc (1) e_v105 e_v106) (L2.p_sel e_v107)
  have f3070 := L2.K16_a_cos_plain (True ∧ v1399 = 1) (sv v0) (sv v1) (sv v100) (sv v107) f3071
  have f3112 := L2.K16_a_cos (True ∧ v1399 = 1) (sv v1184) (sv v1185) (sv v23) (sv v1413) (sv v1414) (sv v1415) (sv v95) (sv v1417) (sv v1419) (sv v1420) (sv v1421) e_v23 (L2.p_mulc e_v1412 e_v1413) e_v1414 e_v1415 e_v95 (L2.p_max e_v1416 (L2.p_sel e_v1417)) (L2.p_mul e_v1418 e_v1419) e_v1420 e_v1421
  let u1429 : ℕ := if v1428 = 1 then 0 else 1
  have f3126 := L2.K7_imul_full (True ∧ v1399 = 1) (sv v1405) (sv v1409) (sv v1417) (sv v1421) (sv v51) v1422 v1423 v1424 v1425 v1426 v1427 v1428 u1429 v1430 v1431 v1432 v1433 v1434 v1435 v1436 (sv v1437) v1438 v1439 v1440 (sv v1441) v1442 v1443 (sv v1444) v1445 v1446 (sv v1447) (sv v1449) (sv v1451) (sv v1453) (sv v1455) (sv v1457) (sv v1459) (sv v1460) (sv v1461) e_v51 e_v1422 e_v1423 e_v1424 e_v1425 (L2.p_and_comm e_v1426) e_v1427 e_v1428 (L2.p_unot _) e_v1430 e_v1431 (L2.p_and_comm e_v1432) e_v1433 e_v1434 e_v1435 e_v1436 (L2.p_sel e_v1437) e_v1438 e_v1439 e_v1440 (L2.p_sel e_v1441) e_v1442 e_v1443 (L2.p_sel e_v1444) e_v1445 e_v1446 (L2.p_sel e_v1447) (L2.p_mul (L2.p_mul_comm e_v1448) e_v1449) (L2.p_mulc (L2.p_mul_comm e_v1450) e_v1451) (L2.p_mul (L2.p_mul_comm e_v1452) e_v1453) (L2.p_mulc (L2.p_mul_comm e_v1454) e_v1455) (L2.p_min e_v1456 (L2.p_sel e_v1457)) (L2.p_max e_v1458 (L2.p_sel e_v1459)) (L2.p_sel e_v1460) (L2.p_sel e_v1461)
  have f3170 := L2.K4_isub (sv v100) (sv v107) (sv v1460) (sv v1461) (sv v1462) (sv v1463) e_v1462 e_v1463
  have f3173 := L2.K7_imul_full (True ∧ v1399 = 1) (sv v1405) (sv v1409) (sv v100) (sv v107) (sv v51) v1422 v1423 v1424 v1425 v1426 v1427 v134 v135 v136 v137 v138 v139 v1464 v1465 v1466 (sv v1467) v1468 v1469 v1470 (sv v1471) v1472 v1473 (sv v1474) v1475 v1476 (sv v1477) (sv v1479) (sv v1481) (sv v1483) (sv v1485) (sv v1487) (sv v1489) (sv v1490) (sv v1491) e_v51 e_v1422 e_v1423 e_v1424 e_v1425 (L2.p_and_comm e_v1426) e_v1427 e_v134 e_v135 e_v136 e_v137 (L2.p_and_comm e_v138) e_v139 (L2.p_and_comm e_v1464) (L2.p_and_comm e_v1465) e_v1466 (L2.p_sel e_v1467) e_v1468 e_v1469 e_v1470 (L2.p_sel e_v1471) (L2.p_and_comm e_v1472) e_v1473 (L2.p_sel e_v1474) (L2.p_and_comm e_v1475) e_v1476 (L2.p_sel e_v1477) (L2.p_mul e_v1478 e_v1479) (L2.p_mulc e_v1480 e_v1481) (L2.p_mul e_v1482 e_v1483) (L2.p_mulc e_v1484 e_v1485) (L2.p_min e_v1486 (L2.p_sel e_v1487)) (L2.p_max e_v1488 (L2.p_sel e_v1489)) (L2.p_sel e_v1490) (L2.p_sel e_v1491)
  have f3217 := L2.K4_isub (sv v1417) (sv v1421) (sv v1490) (sv v1491) (sv v1492) (sv v1493) e_v1492 e_v1493
  let u1506 : ℤ := -((-(sv v1406)) / 2 ^ 28)
  let u1507 : ℤ := u1506 + u1506
  let u1508 : ℤ := (sv v23) - u1507
  let u1509 : ℕ := if u1508 < (sv v95) then 1 else 0
  let u1510 : ℤ := if u1509 = 1 then (sv v95) else u1508
  have f3244 := L2.K16_a_cos (True ∧ v1399 = 1) (sv v1389) (sv v1389) (sv v23) u1506 u1507 u1508 (sv v95) u1510 (sv v1407) (sv v1408) (sv v1409) e_v23 (L2.p_mulc e_v1406 rfl) rfl rfl e_v95 (L2.p_max (L2.p_ult _ _) rfl) (L2.p_mul e_v1406 e_v1407) e_v1408 e_v1409
  have f3258 := L2.K16_a_cos (True ∧ v1399 = 1) (sv v1498) (sv v1499) (sv v23) (sv v1512) (sv v1513) (sv v1514) (sv v95) (sv v1516) (sv v1518) (sv v1519) (sv v1520) e_v23 (L2.p_mulc e_v1511 e_v1512) e_v1513 e_v1514 e_v95 (L2.p_max e_v1515 (L2.p_sel e_v1516)) (L2.p_mul e_v1517 e_v1518) e_v1519 e_v1520
  have f3274 := L2.K8_in_range (True ∧ v1399 = 1) (sv v1502) (sv v1503) v1521 (sv v10) v1523 v1524 (L2.p_clt (-1) e_v8 e_v1521) e_v10 (L2.p_le e_v1522 e_v1523) e_v1524 (L2.X1_step True v1399 v1410 v1524 v1525 e_v1410 e_v1525 (L2.X1_top _ k_v1525))
  have f3286 := L2.K3_cos_lo (sv v1503) (sv v1526) (sv v1527) (sv v95) (sv v1529) (L2.X2_push L2.cosI v1497 (sv v1503) (sv v0) (sv v1) (sv t0.2) (sv t1.2) (sv v1526) (L2.p_sel e_v1503) (L2.p_cos e_t0_2) (L2.p_cos e_t1_2) (L2.p_sel e_v1526)) (L2.p_addc (-4) (L2.p_add_comm e_v1527) e_v18) e_v95 (L2.p_max e_v1528 (L2.p_sel e_v1529))
  have f3303 := L2.K3_cos_hi (sv v1502) (sv v1532) (sv v1533) (sv v23) (sv v1535) (L2.X2_push L2.cosI v1496 (sv v1502) (sv v1) (sv v0) (sv t1.2) (sv t0.2) (sv v1532) (L2.p_sel e_v1502) (L2.p_cos e_t1_2) (L2.p_cos e_t0_2) (L2.p_sel e_v1532)) (L2.p_addc (4) (L2.p_add_comm e_v1533) e_v21) e_v23 (L2.p_min e_v1534 (L2.p_sel e_v1535))
  have f3273 := L2.K10_icos (True ∧ v1399 = 1) (sv v1502) (sv v1503) (sv v1529) (sv v95) v1530 (sv v1531) (sv v1535) (sv v23) v1536 (sv v1537) f3274 f3286 e_v95 (L2.p_clt (843314855) e_v98 e_v1530) (L2.p_sel e_v1531) f3303 e_v23 (L2.p_ltc (1) e_v105 e_v1536) (L2.p_sel e_v1537)
  have f3272 := L2.K16_a_cos_plain (True ∧ v1399 = 1) (sv v1502) (sv v1503) (sv v1531) (sv v1537) f3273
  let u1545 : ℕ := if v1544 = 1 then 0 else 1
  let u1558 : ℕ := if v1542 = 1 ∧ v1549 = 1 then 1 else 0
  let u1559 : ℕ := if v1548 = 1 ∨ u1558 = 1 then 1 else 0
  let u1560 : ℤ := if u1559 = 1 then (sv v1516) else (sv v1520)
  let u1561 : ℕ := if v1543 = 1 ∧ v1548 = 1 then 1 else 0
  let u1562 : ℕ := if v1542 = 1 ∨ u1561 = 1 then 1 else 0
  let u1563 : ℤ := if u1562 = 1 then (sv v1531) else (sv v1537)
  let u1566 : ℤ := u1560 * u1563
  let u1567 : ℤ := -((-u1566) / 2 ^ 28)
  let u1570 : ℤ := (sv v1516) * (sv v1531)
  let u1571 : ℤ := -((-u1570) / 2 ^ 28)
  let u1574 : ℕ := if u1567 < u1571 then 1 else 0
  let u1575 : ℤ := if u1574 = 1 then u1571 else u1567
  let u1577 : ℤ := if v1550 = 1 then u1575 else u1567
  have f3320 := L2.K7_imul_full (True ∧ v1399 = 1) (sv v1516) (sv v1520) (sv v1531) (sv v1537) (sv v51) v1538 v1539 v1540 v1541 v1542 v1543 v1544 u1545 v1546 v1547 v1548 v1549 v1550 v1551 v1552 (sv v1553) v1554 v1555 v1556 (sv v1557) u1558 u1559 u1560 u1561 u1562 u1563 (sv v1565) u1567 (sv v1569) u1571 (sv v1573) u1575 (sv v1576) u1577 e_v51 e_v1538 e_v1539 e_v1540 e_v1541 (L2.p_and_comm e_v1542) e_v1543 e_v1544 (L2.p_unot _) e_v1546 e_v1547 (L2.p_and_comm e_v1548) e_v1549 e_v1550 e_v1551 e_v1552 (L2.p_sel e_v1553) e_v1554 e_v1555 e_v1556 (L2.p_sel e_v1557) (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_mul e_v1564 e_v1565) (L2.p_mulc rfl rfl) (L2.p_mul e_v1568 e_v1569) (L2.p_mulc rfl rfl) (L2.p_min e_v1572 (L2.p_sel e_v1573)) (L2.p_max (L2.p_ult _ _) rfl) (L2.p_sel e_v1576) rfl
  let u1578 : ℤ := u1510 - u1577
  have f3364 := L2.K4_isub u1510 (sv v1409) (sv v1576) u1577 u1578 (sv v1579) rfl e_v1579
  have f3368 := L2.K17_s_end (sv v1498) (sv v1517) (sv v661) (sv v1580) (sv v1581) (sv v1582) (sv v1584) (sv v1585) (sv v23) (sv v1587) (sv v1588) (sv v1590) e_v1517 e_v661 e_v1580 (L2.p_sqrt e_v1581) (L2.p_addc (1) (L2.p_add_comm e_v1582) e_v105) (L2.p_mul (L2.p_mul_comm e_v1583) e_v1584) e_v1585 e_v23 (L2.p_mulc (L2.p_mul_comm e_v1586) e_v1587) e_v1588 (L2.p_min e_v1589 (L2.p_sel e_v1590))
  have f3386 := L2.K17_s_end (sv v1499) (sv v1511) (sv v661) (sv v1591) (sv v1592) (sv v1593) (sv v1595) (sv v1596) (sv v23) (sv v1598) (sv v1599) (sv v1601) e_v1511 e_v661 e_v1591 (L2.p_sqrt e_v1592) (L2.p_addc (1) (L2.p_add_comm e_v1593) e_v105) (L2.p_mul (L2.p_mul_comm e_v1594) e_v1595) e_v1596 e_v23 (L2.p_mulc (L2.p_mul_comm e_v1597) e_v1598) e_v1599 (L2.p_min e_v1600 (L2.p_sel e_v1601))
  have f3367 := L2.K18_a_sin (True ∧ v1399 = 1) (sv v1498) (sv v1499) (sv v1585) (sv v1590) (sv v1596) (sv v1601) (sv v1603) (sv v1605) (sv v688) (sv v1517) (sv v1511) v1607 v1609 v1610 (sv v23) (sv v1611) f3368 f3386 (L2.p_min e_v1602 (L2.p_sel e_v1603)) (L2.p_max e_v1604 (L2.p_sel e_v1605)) e_v688 e_v1517 e_v1511 (L2.p_le e_v1606 e_v1607) (L2.p_le e_v1608 e_v1609) e_v1610 e_v23 (L2.p_sel e_v1611)
  have f3424 := L2.K8_in_range (True ∧ v1399 = 1) (sv v1502) (sv v1503) v1521 (sv v10) v1523 v1524 (L2.p_clt (-1) e_v8 e_v1521) e_v10 (L2.p_le e_v1522 e_v1523) e_v1524 (L2.X1_step True v1399 v1410 v1524 v1525 e_v1410 e_v1525 (L2.X1_top _ k_v1525))
  have f3423 := L2.K9_isin (True ∧ v1399 = 1) (sv v1502) (sv v1503) (sv v1612) (sv v1613) (sv v1615) (sv v1616) (sv v1617) (sv v1618) (sv v23) (sv v1620) v1621 v1622 v1623 (sv v1624) f3424 (L2.X2_push L2.sinI v1496 (sv v1502) (sv v1) (sv v0) (sv t1.1) (sv t0.1) (sv v1612) (L2.p_sel e_v1502) (L2.p_sin e_t1_1) (L2.p_sin e_t0_1) (L2.p_sel e_v1612)) (L2.X2_push L2.sinI v1497 (sv v1503) (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v1613) (L2.p_sel e_v1503) (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_sel e_v1613)) (L2.p_min e_v1614 (L2.p_sel e_v1615)) (L2.p_addc (-4) (L2.p_add_comm e_v1616) e_v18) (L2.p_max e_v1614 (L2.p_sel e_v1617)) (L2.p_addc (4) (L2.p_add_comm e_v1618) e_v21) e_v23 (L2.p_min e_v1619 (L2.p_sel e_v1620)) (L2.p_ltc (421657430) e_v26 e_v1621) (L2.p_clt (421657427) e_v28 e_v1622) e_v1623 (L2.p_sel e_v1624)
  have f3422 := L2.K18_a_sin_plain (True ∧ v1399 = 1) (sv v1502) (sv v1503) (sv v1616) (sv v1624) f3423
  let u1632 : ℕ := if v1631 = 1 then 0 else 1
  have f3468 := L2.K7_imul_full (True ∧ v1399 = 1) (sv v1603) (sv v1611) (sv v1616) (sv v1624) (sv v51) v1625 v1626 v1627 v1628 v1629 v1630 v1631 u1632 v1633 v1634 v1635 v1636 v1637 v1638 v1639 (sv v1640) v1641 v1642 v1643 (sv v1644) v1645 v1646 (sv v1647) v1648 v1649 (sv v1650) (sv v1652) (sv v1654) (sv v1656) (sv v1658) (sv v1660) (sv v1662) (sv v1663) (sv v1664) e_v51 e_v1625 e_v1626 e_v1627 e_v1628 (L2.p_and_comm e_v1629) e_v1630 e_v1631 (L2.p_unot _) e_v1633 e_v1634 (L2.p_and_comm e_v1635) e_v1636 e_v1637 e_v1638 e_v1639 (L2.p_sel e_v1640) e_v1641 e_v1642 e_v1643 (L2.p_sel e_v1644) e_v1645 e_v1646 (L2.p_sel e_v1647) e_v1648 e_v1649 (L2.p_sel e_v1650) (L2.p_mul (L2.p_mul_comm e_v1651) e_v1652) (L2.p_mulc (L2.p_mul_comm e_v1653) e_v1654) (L2.p_mul (L2.p_mul_comm e_v1655) e_v1656) (L2.p_mulc (L2.p_mul_comm e_v1657) e_v1658) (L2.p_min e_v1659 (L2.p_sel e_v1660)) (L2.p_max e_v1661 (L2.p_sel e_v1662)) (L2.p_sel e_v1663) (L2.p_sel e_v1664)
  let u1666 : ℕ := if v1665 = 1 then 0 else 1
  let u1667 : ℕ := if u1578 < (sv v51) then 1 else 0
  let u1668 : ℤ := if u1667 = 1 then (sv v1663) else (sv v1664)
  have f3512 := L2.K11_qdiv u1578 (sv v1579) (sv v1663) (sv v1664) v1665 u1666 (sv v51) u1667 u1668 v1669 (sv v1670) (L2.p_clt (0) e_v51 e_v1665) (L2.p_unot _) e_v51 (L2.p_ult _ _) rfl e_v1669 (L2.p_sel e_v1670)
  have f3243 := L2.K23_hn true true false (True ∧ v1399 = 1) (sv v1389) (sv v1389) (sv v1498) (sv v1499) (sv v1502) (sv v1503) u1510 (sv v1409) (sv v1516) (sv v1520) (sv v1531) (sv v1537) (sv v1576) u1577 u1578 (sv v1579) (sv v1603) (sv v1611) (sv v1616) (sv v1624) (sv v1663) (sv v1664) u1668 (sv v1670) u1666 f3244 f3258 f3272 f3320 f3364 f3367 f3422 f3468 f3512
  let u1674 : ℕ := if (sv v1579) < (sv v1670) then 1 else 0
  let u1675 : ℕ := if u1674 = 1 then 0 else 1
  let u1676 : ℕ := if u1666 = 1 ∨ u1675 = 1 then 1 else 0
  let u1677 : ℤ := if u1676 = 1 then (sv v23) else (sv v1579)
  let u1678 : ℤ := if u1676 = 1 then (sv v23) else (sv v1670)
  let u1679 : ℤ := (sv v1400) / 2 ^ 28
  let u1680 : ℤ := u1679 + u1679
  let u1681 : ℤ := (sv v23) - u1680
  have f3535 := L2.K16_a_cos (True ∧ v1399 = 1) (sv v1390) (sv v1390) (sv v23) (sv v1401) (sv v1402) (sv v1403) (sv v95) (sv v1405) u1679 u1680 u1681 e_v23 (L2.p_mulc e_v1400 e_v1401) e_v1402 e_v1403 e_v95 (L2.p_max e_v1404 (L2.p_sel e_v1405)) (L2.p_mul e_v1400 rfl) rfl rfl
  have f3549 := L2.K16_a_cos (True ∧ v1399 = 1) (sv v1500) (sv v1501) (sv v23) (sv v1683) (sv v1684) (sv v1685) (sv v95) (sv v1687) (sv v1689) (sv v1690) (sv v1691) e_v23 (L2.p_mulc e_v1682 e_v1683) e_v1684 e_v1685 e_v95 (L2.p_max e_v1686 (L2.p_sel e_v1687)) (L2.p_mul e_v1688 e_v1689) e_v1690 e_v1691
  have f3565 := L2.K8_in_range (True ∧ v1399 = 1) (sv v1504) (sv v1505) v1692 (sv v10) v1694 v1695 (L2.p_clt (-1) e_v8 e_v1692) e_v10 (L2.p_le e_v1693 e_v1694) e_v1695 (L2.X1_step True v1399 v1410 v1695 v1696 e_v1410 e_v1696 (L2.X1_top _ k_v1696))
  have f3577 := L2.K3_cos_lo (sv v1505) (sv v1697) (sv v1698) (sv v95) (sv v1700) (L2.X2_push L2.cosI v1496 (sv v1505) (sv v0) (sv v1) (sv t0.2) (sv t1.2) (sv v1697) (L2.p_sel e_v1505) (L2.p_cos e_t0_2) (L2.p_cos e_t1_2) (L2.p_sel e_v1697)) (L2.p_addc (-4) (L2.p_add_comm e_v1698) e_v18) e_v95 (L2.p_max e_v1699 (L2.p_sel e_v1700))
  have f3594 := L2.K3_cos_hi (sv v1504) (sv v1703) (sv v1704) (sv v23) (sv v1706) (L2.X2_push L2.cosI v1497 (sv v1504) (sv v1) (sv v0) (sv t1.2) (sv t0.2) (sv v1703) (L2.p_sel e_v1504) (L2.p_cos e_t1_2) (L2.p_cos e_t0_2) (L2.p_sel e_v1703)) (L2.p_addc (4) (L2.p_add_comm e_v1704) e_v21) e_v23 (L2.p_min e_v1705 (L2.p_sel e_v1706))
  have f3564 := L2.K10_icos (True ∧ v1399 = 1) (sv v1504) (sv v1505) (sv v1700) (sv v95) v1701 (sv v1702) (sv v1706) (sv v23) v1707 (sv v1708) f3565 f3577 e_v95 (L2.p_clt (843314855) e_v98 e_v1701) (L2.p_sel e_v1702) f3594 e_v23 (L2.p_ltc (1) e_v105 e_v1707) (L2.p_sel e_v1708)
  have f3563 := L2.K16_a_cos_plain (True ∧ v1399 = 1) (sv v1504) (sv v1505) (sv v1702) (sv v1708) f3564
  let u1710 : ℕ := if v1709 = 1 then 0 else 1
  let u1716 : ℕ := if v1715 = 1 then 0 else 1
  let u1722 : ℕ := if u1710 = 1 ∧ v1720 = 1 then 1 else 0
  let u1723 : ℕ := if v1719 = 1 ∨ u1722 = 1 then 1 else 0
  let u1724 : ℤ := if u1723 = 1 then (sv v1691) else (sv v1687)
  let u1725 : ℕ := if v1719 = 1 then 0 else 1
  let u1726 : ℕ := if v1714 = 1 ∧ u1725 = 1 then 1 else 0
  let u1727 : ℕ := if v1713 = 1 ∨ u1726 = 1 then 1 else 0
  let u1728 : ℤ := if u1727 = 1 then (sv v1708) else (sv v1702)
  let u1735 : ℤ := u1724 * u1728
  let u1736 : ℤ := u1735 / 2 ^ 28
  let u1739 : ℤ := (sv v1691) * (sv v1702)
  let u1740 : ℤ := u1739 / 2 ^ 28
  let u1743 : ℕ := if u1736 < u1740 then 1 else 0
  let u1744 : ℤ := if u1743 = 1 then u1736 else u1740
  let u1747 : ℤ := if v1721 = 1 then u1744 else u1736
  have f3611 := L2.K7_imul_full (True ∧ v1399 = 1) (sv v1687) (sv v1691) (sv v1702) (sv v1708) (sv v51) v1709 u1710 v1711 v1712 v1713 v1714 v1715 u1716 v1717 v1718 v1719 v1720 v1721 u1722 u1723 u1724 u1725 u1726 u1727 u1728 v1729 v1730 (sv v1731) v1732 v1733 (sv v1734) u1736 (sv v1738) u1740 (sv v1742) u1744 (sv v1746) u1747 (sv v1748) e_v51 e_v1709 (L2.p_unot _) e_v1711 e_v1712 (L2.p_and_comm e_v1713) e_v1714 e_v1715 (L2.p_unot _) e_v1717 e_v1718 (L2.p_and_comm e_v1719) e_v1720 e_v1721 (L2.p_uand _ _) (L2.p_uor _ _) rfl (L2.p_unot _) (L2.p_uand _ _) (L2.p_uor _ _) rfl e_v1729 e_v1730 (L2.p_sel e_v1731) e_v1732 e_v1733 (L2.p_sel e_v1734) (L2.p_mul rfl rfl) (L2.p_mulc e_v1737 e_v1738) (L2.p_mul rfl rfl) (L2.p_mulc e_v1741 e_v1742) (L2.p_min (L2.p_ult _ _) rfl) (L2.p_max e_v1745 (L2.p_sel e_v1746)) rfl (L2.p_sel e_v1748)
  let u1750 : ℤ := u1681 - u1747
  have f3655 := L2.K4_isub (sv v1405) u1681 u1747 (sv v1748) (sv v1749) u1750 e_v1749 rfl
  have f3659 := L2.K17_s_end (sv v1500) (sv v1688) (sv v661) (sv v1751) (sv v1752) (sv v1753) (sv v1755) (sv v1756) (sv v23) (sv v1758) (sv v1759) (sv v1761) e_v1688 e_v661 e_v1751 (L2.p_sqrt e_v1752) (L2.p_addc (1) (L2.p_add_comm e_v1753) e_v105) (L2.p_mul (L2.p_mul_comm e_v1754) e_v1755) e_v1756 e_v23 (L2.p_mulc (L2.p_mul_comm e_v1757) e_v1758) e_v1759 (L2.p_min e_v1760 (L2.p_sel e_v1761))
  have f3677 := L2.K17_s_end (sv v1501) (sv v1682) (sv v661) (sv v1762) (sv v1763) (sv v1764) (sv v1766) (sv v1767) (sv v23) (sv v1769) (sv v1770) (sv v1772) e_v1682 e_v661 e_v1762 (L2.p_sqrt e_v1763) (L2.p_addc (1) (L2.p_add_comm e_v1764) e_v105) (L2.p_mul (L2.p_mul_comm e_v1765) e_v1766) e_v1767 e_v23 (L2.p_mulc (L2.p_mul_comm e_v1768) e_v1769) e_v1770 (L2.p_min e_v1771 (L2.p_sel e_v1772))
  have f3658 := L2.K18_a_sin (True ∧ v1399 = 1) (sv v1500) (sv v1501) (sv v1756) (sv v1761) (sv v1767) (sv v1772) (sv v1774) (sv v1776) (sv v688) (sv v1688) (sv v1682) v1778 v1780 v1781 (sv v23) (sv v1782) f3659 f3677 (L2.p_min e_v1773 (L2.p_sel e_v1774)) (L2.p_max e_v1775 (L2.p_sel e_v1776)) e_v688 e_v1688 e_v1682 (L2.p_le e_v1777 e_v1778) (L2.p_le e_v1779 e_v1780) e_v1781 e_v23 (L2.p_sel e_v1782)
  have f3715 := L2.K8_in_range (True ∧ v1399 = 1) (sv v1504) (sv v1505) v1692 (sv v10) v1694 v1695 (L2.p_clt (-1) e_v8 e_v1692) e_v10 (L2.p_le e_v1693 e_v1694) e_v1695 (L2.X1_step True v1399 v1410 v1695 v1696 e_v1410 e_v1696 (L2.X1_top _ k_v1696))
  have f3714 := L2.K9_isin (True ∧ v1399 = 1) (sv v1504) (sv v1505) (sv v1783) (sv v1784) (sv v1786) (sv v1787) (sv v1788) (sv v1789) (sv v23) (sv v1791) v1792 v1793 v1794 (sv v1795) f3715 (L2.X2_push L2.sinI v1497 (sv v1504) (sv v1) (sv v0) (sv t1.1) (sv t0.1) (sv v1783) (L2.p_sel e_v1504) (L2.p_sin e_t1_1) (L2.p_sin e_t0_1) (L2.p_sel e_v1783)) (L2.X2_push L2.sinI v1496 (sv v1505) (sv v0) (sv v1) (sv t0.1) (sv t1.1) (sv v1784) (L2.p_sel e_v1505) (L2.p_sin e_t0_1) (L2.p_sin e_t1_1) (L2.p_sel e_v1784)) (L2.p_min e_v1785 (L2.p_sel e_v1786)) (L2.p_addc (-4) (L2.p_add_comm e_v1787) e_v18) (L2.p_max e_v1785 (L2.p_sel e_v1788)) (L2.p_addc (4) (L2.p_add_comm e_v1789) e_v21) e_v23 (L2.p_min e_v1790 (L2.p_sel e_v1791)) (L2.p_ltc (421657430) e_v26 e_v1792) (L2.p_clt (421657427) e_v28 e_v1793) e_v1794 (L2.p_sel e_v1795)
  have f3713 := L2.K18_a_sin_plain (True ∧ v1399 = 1) (sv v1504) (sv v1505) (sv v1787) (sv v1795) f3714
  let u1803 : ℕ := if v1802 = 1 then 0 else 1
  have f3759 := L2.K7_imul_full (True ∧ v1399 = 1) (sv v1774) (sv v1782) (sv v1787) (sv v1795) (sv v51) v1796 v1797 v1798 v1799 v1800 v1801 v1802 u1803 v1804 v1805 v1806 v1807 v1808 v1809 v1810 (sv v1811) v1812 v1813 v1814 (sv v1815) v1816 v1817 (sv v1818) v1819 v1820 (sv v1821) (sv v1823) (sv v1825) (sv v1827) (sv v1829) (sv v1831) (sv v1833) (sv v1834) (sv v1835) e_v51 e_v1796 e_v1797 e_v1798 e_v1799 (L2.p_and_comm e_v1800) e_v1801 e_v1802 (L2.p_unot _) e_v1804 e_v1805 (L2.p_and_comm e_v1806) e_v1807 e_v1808 e_v1809 e_v1810 (L2.p_sel e_v1811) e_v1812 e_v1813 e_v1814 (L2.p_sel e_v1815) e_v1816 e_v1817 (L2.p_sel e_v1818) e_v1819 e_v1820 (L2.p_sel e_v1821) (L2.p_mul (L2.p_mul_comm e_v1822) e_v1823) (L2.p_mulc (L2.p_mul_comm e_v1824) e_v1825) (L2.p_mul (L2.p_mul_comm e_v1826) e_v1827) (L2.p_mulc (L2.p_mul_comm e_v1828) e_v1829) (L2.p_min e_v1830 (L2.p_sel e_v1831)) (L2.p_max e_v1832 (L2.p_sel e_v1833)) (L2.p_sel e_v1834) (L2.p_sel e_v1835)
  let u1840 : ℕ := if u1750 < (sv v51) then 1 else 0
  let u1841 : ℤ := if u1840 = 1 then (sv v1835) else (sv v1834)
  have f3803 := L2.K11_qdiv (sv v1749) u1750 (sv v1834) (sv v1835) v1836 v1837 (sv v51) v1838 (sv v1839) u1840 u1841 (L2.p_clt (0) e_v51 e_v1836) e_v1837 e_v51 e_v1838 (L2.p_sel e_v1839) (L2.p_ult _ _) rfl
  have f3534 := L2.K23_hn true true false (True ∧ v1399 = 1) (sv v1390) (sv v1390) (sv v1500) (sv v1501) (sv v1504) (sv v1505) (sv v1405) u1681 (sv v1687) (sv v1691) (sv v1702) (sv v1708) u1747 (sv v1748) (sv v1749) u1750 (sv v1774) (sv v1782) (sv v1787) (sv v1795) (sv v1834) (sv v1835) (sv v1839) u1841 v1837 f3535 f3549 f3563 f3611 f3655 f3658 f3713 f3759 f3803
  let u1851 : ℕ := if v1850 = 1 then 0 else 1
  let u1852 : ℤ := 0
  let u1853 : ℕ := if (sv v51) < u1852 then 1 else 0
  let u1854 : ℕ := if u1853 = 1 then 0 else 1
  let u1855 : ℤ := L2.cosI u1852
  let u1856 : ℤ := (sv v18) + u1855
  let u1857 : ℕ := if u1856 < (sv v95) then 1 else 0
  let u1858 : ℤ := if u1857 = 1 then (sv v95) else u1856
  have f3832 := L2.K3_cos_lo u1852 u1855 u1856 (sv v95) u1858 rfl (L2.p_addc (-4) (L2.p_add_comm rfl) e_v18) e_v95 (L2.p_max (L2.p_ult _ _) rfl)
  let u1859 : ℤ := u1677 * 2 ^ 28
  let u1860 : ℤ := u1678 * u1858
  let u1861 : ℕ := if u1860 < u1859 then 1 else 0
  let u1862 : ℕ := if u1861 = 1 then 0 else 1
  let u1863 : ℕ := if (sv v473) < u1852 then 1 else 0
  let u1864 : ℕ := if u1863 = 1 then 0 else 1
  let u1865 : ℕ := if u1862 = 1 ∧ u1864 = 1 then 1 else 0
  let u1866 : ℕ := if u1854 = 1 ∨ u1865 = 1 then 1 else 0
  let u1867 : ℤ := if u1866 = 1 then u1852 else (sv v51)
  have f3827 := L2.K13_acos_lo u1677 u1678 u1852 (sv v51) u1853 u1854 u1858 u1859 u1860 u1862 (sv v473) u1864 u1865 u1866 u1867 (le_refl (0 : ℤ)) e_v51 (L2.p_ult _ _) (L2.p_unot _) f3832 rfl (L2.p_mul_comm rfl) (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) e_v473 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_uand _ _) (L2.p_uor _ _) rfl
  have f3859 := L2.K3_cos_hi (sv v1868) (sv t1868.2) (sv v1872) (sv v23) (sv v1874) (L2.p_cos e_t1868_2) (L2.p_addc (4) (L2.p_add_comm e_v1872) e_v21) e_v23 (L2.p_min e_v1873 (L2.p_sel e_v1874))
  have f3853 := L2.K13_acos_hi (sv v1848) (sv v1849) (sv v1868) (sv v10) v1870 (sv v1874) (sv v1875) (sv v1876) v1878 v1879 (sv v1880) (L2.p_hint e_v1868) e_v10 (L2.p_le e_v1869 e_v1870) f3859 e_v1875 (L2.p_mul_comm e_v1876) (L2.p_le e_v1877 e_v1878) e_v1879 (L2.p_sel e_v1880)
  let u1881 : ℤ := if v1399 = 1 then u1867 else (sv v51)
  let u1884 : ℤ := if v1673 = 1 then (sv v473) else (sv v51)
  have f3240 := L2.K24_tri_tail_x true true false True (sv v1389) (sv v1390) v1399 (sv v1498) (sv v1499) (sv v1502) (sv v1503) (sv v1500) (sv v1501) (sv v1504) (sv v1505) (sv v23) (sv v95) u1578 u1668 (sv v1579) (sv v1670) u1666 v1665 (sv v1671) v1672 v1673 u1675 u1676 u1677 u1678 (sv v1749) (sv v1839) u1750 u1841 v1837 v1836 v1842 v1843 (sv v1844) v1846 v1847 (sv v1848) (sv v1849) v1850 u1851 u1867 (sv v1880) (sv v51) (sv v10) (sv v473) u1881 (sv v1882) v1883 u1884 (sv v1885) e_v23 e_v95 f3243 (L2.p_not_not (L2.p_unot _)) (L2.p_neg e_v51 e_v1671) e_v1672 e_v1673 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_uor _ _) rfl rfl f3534 (L2.p_not_not e_v1837) e_v1842 e_v1843 (L2.p_neg e_v51 e_v1844) (L2.p_le e_v1845 e_v1846) e_v1847 (L2.p_sel e_v1848) (L2.p_sel e_v1849) e_v1850 (L2.p_unot _) f3827 f3853 e_v51 e_v10 e_v473 rfl (L2.p_sel e_v1882) e_v1883 rfl (L2.p_sel e_v1885)
  have f3028 := L2.K21_tri_angle_st true true false True (sv v1389) (sv v1390) (sv v1184) (sv v1185) (sv v0) (sv v1) v1394 v1397 v475 v1398 v1399 (sv v1405) (sv v1409) (sv v100) (sv v107) (sv v1417) (sv v1421) (sv v1460) (sv v1461) (sv v1462) (sv v1463) (sv v1490) (sv v1491) (sv v1492) (sv v1493) v1494 v1495 v1496 v1497 (sv v1498) (sv v1499) (sv v1500) (sv v1501) (sv v1502) (sv v1503) (sv v1504) (sv v1505) u1881 (sv v1882) v1883 u1884 (sv v1885) f3029 f3037 f3045 e_v1398 (L2.p_and_comm e_v1399) f3056 f3070 f3112 f3126 f3170 f3173 f3217 (L2.p_clt (0) e_v51 e_v1494) (L2.p_ltc (0) e_v51 e_v1495) (L2.p_clt (0) e_v51 e_v1496) (L2.p_ltc (0) e_v51 e_v1497) (L2.p_sel e_v1498) (L2.p_sel e_v1499) (L2.p_sel e_v1500) (L2.p_sel e_v1501) (L2.p_sel e_v1502) (L2.p_sel e_v1503) (L2.p_sel e_v1504) (L2.p_sel e_v1505) f3240
  let u1886 : ℤ := if v1883 = 1 then u1884 else u1881
  have f3027 := L2.K25_tri_angle_c true true false True (sv v1389) (sv v1390) (sv v1184) (sv v1185) (sv v0) (sv v1) u1881 (sv v1882) v1883 u1884 (sv v1885) u1886 (sv v1887) f3028 rfl (L2.p_sel e_v1887)
  let u1888 : ℤ := u1339 + u1886
  have f3885 := L2.K4_iadd u1339 (sv v417) u1886 (sv v1887) u1888 (sv v1889) rfl e_v1889
  have f2107 := L2.K28_pent_eval_1 True (sv v2) u1125 u1134 (sv v5) (sv v0) (sv v1) (sv v1184) (sv v1185) u1339 (sv v417) (sv v1389) (sv v1390) u1886 (sv v1887) u1888 (sv v1889) f2108 f2246 f2894 f3027 f3885
  let u1890 : ℕ := if u1888 < (sv v6) then 1 else 0
  let u1891 : ℕ := if u1890 = 1 then 0 else 1
  exact L2.K31_M1 true F0 F1 F2 F3 hD (sv v0) (sv v1) (sv v2) (sv v3) (sv v4) (sv v5) (sv v6) (1 : ℕ) (sv v90) (sv v91) u265 (sv v417) (sv v469) (sv v470) (sv v1000) (sv v1001) u1006 (sv v1007) v1114 (sv v2) u1125 u1134 (sv v5) u1888 (sv v1889) u1891 v1893 v1893 e_v0 e_v1 e_v2 e_v3 e_v4 e_v5 e_v6 (of_decide_eq_true rfl) f1 f127 f739 f865 f1729 f1733 f2071 f2090 f2107 (L2.p_le (L2.p_ult _ _) (L2.p_unot _)) (L2.p_le e_v1892 e_v1893) (L2.p_sel_t _ _) (L2.X1_top _ k_v1893)

end D3Prog
