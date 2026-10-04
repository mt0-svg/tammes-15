import Tammes15.D3Trig.Prog.HML
import Tammes15.D3Prog.Sem

namespace Tammes15.D3Trig

open D3Prog D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progHML_seg4 (F0 F1 F2 F3 H0 H1 H2 H3 H4 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (hb_H3 : H3 < 2 ^ 64) (hb_H4 : H4 < 2 ^ 64) (v23 : ℕ) (v47 : ℕ) (v75 : ℕ) (v92 : ℕ) (v110 : ℕ) (v147 : ℕ) (v255 : ℕ) (v260 : ℕ) (v291 : ℕ) (v403 : ℕ) (v424 : ℕ) (v441 : ℕ) (v444 : ℕ) (v475 : ℕ) (v580 : ℕ) (v585 : ℕ) (v616 : ℕ) (v729 : ℕ) (v750 : ℕ) (v767 : ℕ) (v794 : ℕ) (v824 : ℕ) (v851 : ℕ) (v921 : ℕ) (v1020 : ℕ) (v1088 : ℕ) (v1185 : ℕ) (v1252 : ℕ) (v1255 : ℕ) (v1323 : ℕ) (v1420 : ℕ) (v1488 : ℕ) (v1585 : ℕ) (v1652 : ℕ) (v1661 : ℕ) (v1662 : ℕ) (v1665 : ℕ) (v1686 : ℕ) (v1725 : ℕ) (v1738 : ℕ) (v1756 : ℕ) (v1757 : ℕ) (v1760 : ℕ) (v1781 : ℕ) (v1820 : ℕ) (v1833 : ℕ) (v1871 : ℕ) (v1892 : ℕ) (v1909 : ℕ) (v1915 : ℕ) (v1952 : ℕ) (v2063 : ℕ) (v2084 : ℕ) (v2101 : ℕ) (v2107 : ℕ) (v2144 : ℕ) (v2258 : ℕ) (v2287 : ℕ) (v2288 : ℕ) (v2315 : ℕ) (v2340 : ℕ) (v2341 : ℕ) (v2344 : ℕ) (v2345 : ℕ) (v2385 : ℕ) (v2482 : ℕ) (v2507 : ℕ) (v2511 : ℕ) (v2512 : ℕ) (h_v23 : R 1 0 0 1 v23 v23) (h_v47 : R 1 0 0 1 v47 v47) (h_v75 : R 1 0 0 1 v75 v75) (h_v92 : R 1 0 0 1 v92 v92) (h_v110 : R 1 0 0 1 v110 v110) (h_v147 : R 1 0 0 1 v147 v147) (h_v255 : R 1 0 4611686017353646081 4611686019501129727 v255 v255) (h_v260 : R 1 0 0 1 v260 v260) (h_v291 : R 1 0 0 1 v291 v291) (h_v403 : R 1 0 0 1 v403 v403) (h_v424 : R 1 0 0 1 v424 v424) (h_v441 : R 1 0 0 1 v441 v441) (h_v444 : R 1 0 0 1 v444 v444) (h_v475 : R 1 0 0 1 v475 v475) (h_v580 : R 1 0 4611686017353646081 4611686019501129727 v580 v580) (h_v585 : R 1 0 0 1 v585 v585) (h_v616 : R 1 0 0 1 v616 v616) (h_v729 : R 1 0 0 1 v729 v729) (h_v750 : R 1 0 0 1 v750 v750) (h_v767 : R 1 0 0 1 v767 v767) (h_v794 : R 1 0 4611686018158952386 4611686018695823360 v794 v794) (h_v824 : R 1 0 0 1 v824 v824) (h_v851 : R 1 0 0 1 v851 v851) (h_v921 : R 1 0 0 1 v921 v921) (h_v1020 : R 1 0 0 1 v1020 v1020) (h_v1088 : R 1 0 0 1 v1088 v1088) (h_v1185 : R 1 0 0 1 v1185 v1185) (h_v1252 : R 1 0 0 1 v1252 v1252) (h_v1255 : R 1 0 0 1 v1255 v1255) (h_v1323 : R 1 0 0 1 v1323 v1323) (h_v1420 : R 1 0 0 1 v1420 v1420) (h_v1488 : R 1 0 0 1 v1488 v1488) (h_v1585 : R 1 0 0 1 v1585 v1585) (h_v1652 : R 1 0 0 1 v1652 v1652) (h_v1661 : R 1 0 0 1 v1661 v1661) (h_v1662 : R 1 0 0 1 v1662 v1662) (h_v1665 : R 1 0 0 1 v1665 v1665) (h_v1686 : R 1 0 0 1 v1686 v1686) (h_v1725 : R 1 0 0 1 v1725 v1725) (h_v1738 : R 1 0 0 1 v1738 v1738) (h_v1756 : R 1 0 0 1 v1756 v1756) (h_v1757 : R 1 0 0 1 v1757 v1757) (h_v1760 : R 1 0 0 1 v1760 v1760) (h_v1781 : R 1 0 0 1 v1781 v1781) (h_v1820 : R 1 0 0 1 v1820 v1820) (h_v1833 : R 1 0 0 1 v1833 v1833) (h_v1871 : R 1 0 0 1 v1871 v1871) (h_v1892 : R 1 0 0 1 v1892 v1892) (h_v1909 : R 1 0 0 1 v1909 v1909) (h_v1915 : R 1 0 0 1 v1915 v1915) (h_v1952 : R 1 0 0 1 v1952 v1952) (h_v2063 : R 1 0 0 1 v2063 v2063) (h_v2084 : R 1 0 0 1 v2084 v2084) (h_v2101 : R 1 0 0 1 v2101 v2101) (h_v2107 : R 1 0 0 1 v2107 v2107) (h_v2144 : R 1 0 0 1 v2144 v2144) (h_v2258 : R 1 0 0 1 v2258 v2258) (h_v2287 : R 1 0 0 1 v2287 v2287) (h_v2288 : R 1 0 0 1 v2288 v2288) (h_v2315 : R 1 0 0 1 v2315 v2315) (h_v2340 : R 1 0 4611686018427387899 4611686018695823375 v2340 v2340) (h_v2341 : R 1 0 4611686018427387899 4611686018695823375 v2341 v2341) (h_v2344 : R 1 0 4611686018427387899 4611686018695823375 v2344 v2344) (h_v2345 : R 1 0 4611686018427387899 4611686018695823375 v2345 v2345) (h_v2385 : R 1 0 0 1 v2385 v2385) (h_v2482 : R 1 0 0 1 v2482 v2482) (h_v2507 : R 1 0 0 1 v2507 v2507) (h_v2511 : R 1 0 4611686017890516812 4611686018964258878 v2511 v2511) (h_v2512 : R 1 0 4611686018427387893 4611686018695823369 v2512 v2512) :
    let OFFr := Nat.mul 1 4611686018427387904
    let v6 := ix 1 F3 0
    let v15 := Nat.mul 1 4611686019270702760
    let v28 := Nat.mul 1 4611686018427387900
    let v33 := Nat.mul 1 4611686018695823360
    let v61 := Nat.mul 1 4611686018427387904
    let v95 := Nat.mul 1 4611686018158952448
    let v105 := Nat.mul 1 4611686018427387905
    let v940 := Nat.mul 1 4683743612465315840
    let v967 := Nat.mul 1 4647714815446351872
    let v2516 := smx 29 1 v2341 v2341
    let v2517 := srdC 1 v2516
    let v2518 := Nat.sub (Nat.add v2517 v2517) OFFr
    let v2519 := Nat.sub (Nat.add v33 OFFr) v2518
    let v2520 := plt 1 v2519 v95
    let v2521 := psel (pmask v2520) v95 v2519
    let v2522 := smx 29 1 v2340 v2340
    let v2523 := srdF 1 v2522
    let v2524 := Nat.sub (Nat.add v2523 v2523) OFFr
    let v2525 := Nat.sub (Nat.add v33 OFFr) v2524
    let v2526 := smx 29 1 v2345 v2345
    let v2527 := srdC 1 v2526
    let v2528 := Nat.sub (Nat.add v2527 v2527) OFFr
    let v2529 := Nat.sub (Nat.add v33 OFFr) v2528
    let v2530 := plt 1 v2529 v95
    let v2531 := psel (pmask v2530) v95 v2529
    let v2532 := smx 29 1 v2344 v2344
    let v2533 := srdF 1 v2532
    let v2534 := Nat.sub (Nat.add v2533 v2533) OFFr
    let v2535 := Nat.sub (Nat.add v33 OFFr) v2534
    let v2536 := plt 1 v2521 v61
    let v2538 := plt 1 v61 v2525
    let v2539 := Nat.sub 1 v2538
    let v2540 := Nat.land v2536 v2539
    let v2541 := Nat.land v2536 v2538
    let v2542 := plt 1 v2531 v61
    let v2544 := plt 1 v61 v2535
    let v2545 := Nat.sub 1 v2544
    let v2546 := Nat.land v2542 v2545
    let v2547 := Nat.land v2542 v2544
    let v2548 := Nat.land v2541 v2547
    let v2549 := Nat.sub 1 v2548
    let v2550 := Nat.lor v2287 v2549
    let v2557 := Nat.land v2540 v2547
    let v2558 := Nat.lor v2546 v2557
    let v2559 := psel (pmask v2558) v2521 v2525
    let v2560 := Nat.land v2541 v2546
    let v2561 := Nat.lor v2540 v2560
    let v2562 := psel (pmask v2561) v2531 v2535
    let v2565 := smx 30 1 v2562 v2559
    let v2566 := srdC 1 v2565
    let v2567 := Nat.sub (Nat.add v794 OFFr) v2566
    let v2569 := Nat.sub (Nat.add v940 OFFr) v2522
    let v2570 := psqrt 1 v2569
    let v2571 := Nat.sub (Nat.add v105 v2570) OFFr
    let v2572 := smx 29 1 v2570 v2340
    let v2573 := srdF 1 v2572
    let v2574 := Nat.sub (Nat.add v2573 v2573) OFFr
    let v2575 := smx 29 1 v2571 v2340
    let v2576 := srdC 1 v2575
    let v2577 := Nat.sub (Nat.add v2576 v2576) OFFr
    let v2578 := plt 1 v2577 v33
    let v2579 := psel (pmask v2578) v2577 v33
    let v2580 := Nat.sub (Nat.add v940 OFFr) v2516
    let v2581 := psqrt 1 v2580
    let v2582 := Nat.sub (Nat.add v105 v2581) OFFr
    let v2583 := smx 29 1 v2581 v2341
    let v2584 := srdF 1 v2583
    let v2585 := Nat.sub (Nat.add v2584 v2584) OFFr
    let v2586 := smx 29 1 v2582 v2341
    let v2587 := srdC 1 v2586
    let v2588 := Nat.sub (Nat.add v2587 v2587) OFFr
    let v2589 := plt 1 v2588 v33
    let v2590 := psel (pmask v2589) v2588 v33
    let v2591 := plt 1 v2574 v2585
    let v2592 := psel (pmask v2591) v2574 v2585
    let v2593 := plt 1 v2579 v2590
    let v2594 := psel (pmask v2593) v2590 v2579
    let v2595 := plt 1 v967 v2522
    let v2596 := Nat.sub 1 v2595
    let v2597 := plt 1 v2516 v967
    let v2598 := Nat.sub 1 v2597
    let v2599 := Nat.land v2596 v2598
    let v2600 := psel (pmask v2599) v33 v2594
    let v2601 := Nat.sub (Nat.add v940 OFFr) v2532
    let v2602 := psqrt 1 v2601
    let v2603 := Nat.sub (Nat.add v105 v2602) OFFr
    let v2604 := smx 29 1 v2602 v2344
    let v2605 := srdF 1 v2604
    let v2606 := Nat.sub (Nat.add v2605 v2605) OFFr
    let v2607 := smx 29 1 v2603 v2344
    let v2608 := srdC 1 v2607
    let v2609 := Nat.sub (Nat.add v2608 v2608) OFFr
    let v2610 := plt 1 v2609 v33
    let v2611 := psel (pmask v2610) v2609 v33
    let v2612 := Nat.sub (Nat.add v940 OFFr) v2526
    let v2613 := psqrt 1 v2612
    let v2614 := Nat.sub (Nat.add v105 v2613) OFFr
    let v2615 := smx 29 1 v2613 v2345
    let v2616 := srdF 1 v2615
    let v2617 := Nat.sub (Nat.add v2616 v2616) OFFr
    let v2618 := smx 29 1 v2614 v2345
    let v2619 := srdC 1 v2618
    let v2620 := Nat.sub (Nat.add v2619 v2619) OFFr
    let v2621 := plt 1 v2620 v33
    let v2622 := psel (pmask v2621) v2620 v33
    let v2623 := plt 1 v2606 v2617
    let v2624 := psel (pmask v2623) v2606 v2617
    let v2625 := plt 1 v2611 v2622
    let v2626 := psel (pmask v2625) v2622 v2611
    let v2627 := plt 1 v967 v2532
    let v2628 := Nat.sub 1 v2627
    let v2629 := plt 1 v2526 v967
    let v2630 := Nat.sub 1 v2629
    let v2631 := Nat.land v2628 v2630
    let v2632 := psel (pmask v2631) v33 v2626
    let v2633 := plt 1 v2592 v61
    let v2634 := Nat.sub 1 v2633
    let v2635 := plt 1 v61 v2600
    let v2636 := Nat.sub 1 v2635
    let v2637 := Nat.land v2633 v2636
    let v2638 := Nat.land v2633 v2635
    let v2639 := plt 1 v2624 v61
    let v2640 := Nat.sub 1 v2639
    let v2641 := plt 1 v61 v2632
    let v2642 := Nat.sub 1 v2641
    let v2643 := Nat.land v2639 v2642
    let v2644 := Nat.land v2639 v2641
    let v2645 := Nat.land v2638 v2644
    let v2646 := Nat.sub 1 v2645
    let v2647 := Nat.lor v2287 v2646
    let v2648 := Nat.land v2634 v2644
    let v2649 := Nat.lor v2643 v2648
    let v2650 := psel (pmask v2649) v2600 v2592
    let v2651 := Nat.land v2638 v2640
    let v2652 := Nat.lor v2637 v2651
    let v2653 := psel (pmask v2652) v2632 v2624
    let v2654 := Nat.land v2637 v2644
    let v2655 := Nat.lor v2643 v2654
    let v2656 := psel (pmask v2655) v2592 v2600
    let v2657 := Nat.land v2638 v2643
    let v2658 := Nat.lor v2637 v2657
    let v2659 := psel (pmask v2658) v2624 v2632
    let v2660 := smx 29 1 v2653 v2650
    let v2661 := srdF 1 v2660
    let v2662 := smx 29 1 v2659 v2656
    let v2663 := srdC 1 v2662
    let v2664 := plt 1 v61 v2661
    let v2666 := plt 1 v2567 v61
    let v2667 := psel (pmask v2666) v2661 v2663
    let v2670 := plt 1 v2667 v2567
    let v2671 := Nat.land v2664 v2670
    let v2678 := Nat.lor v2507 v2671
    let v2680 := hxa 1 H4 0
    let v2681 := plt 1 v61 v2680
    let v2682 := Nat.sub 1 v2681
    let t2680 := sc28u 1 v2680
    let v2684 := Nat.sub (Nat.add v28 t2680.2) OFFr
    let v2685 := plt 1 v2684 v95
    let v2686 := psel (pmask v2685) v95 v2684
    let v2687 := sshl 1 v2511
    let v2688 := smx 29 1 v2686 v2512
    let v2689 := plt 1 v2688 v2687
    let v2690 := Nat.sub 1 v2689
    let v2691 := plt 1 v15 v2680
    let v2692 := Nat.sub 1 v2691
    let v2693 := Nat.land v2690 v2692
    let v2694 := Nat.lor v2682 v2693
    let v2695 := psel (pmask v2694) v2680 v61
    let v2709 := psel (pmask v2258) v2695 v61
    let v2711 := Nat.land v2258 v2678
    let v2712 := psel (pmask v2507) v15 v61
    let v2714 := psel (pmask v2711) v2712 v2709
    let v2716 := Nat.sub (Nat.add v255 v2714) OFFr
    let v2718 := Nat.sub (Nat.add v580 v2716) OFFr
    let v2720 := plt 1 v2718 v6
    let v2721 := Nat.sub 1 v2720
    let v2724 := Nat.land v23 v47
    let v2725 := Nat.land v75 v2724
    let v2726 := Nat.land v92 v2725
    let v2727 := Nat.land v23 v2726
    let v2728 := Nat.land v110 v2727
    let v2729 := Nat.land v110 v2728
    let v2730 := Nat.land v147 v2729
    let v2731 := Nat.land v260 v2730
    let v2732 := Nat.land v260 v2731
    let v2733 := Nat.land v291 v2732
    let v2734 := Nat.land v23 v2733
    let v2735 := Nat.land v403 v2734
    let v2736 := Nat.land v424 v2735
    let v2737 := Nat.land v441 v2736
    let v2738 := Nat.land v23 v2737
    let v2739 := Nat.land v444 v2738
    let v2740 := Nat.land v444 v2739
    let v2741 := Nat.land v475 v2740
    let v2742 := Nat.land v585 v2741
    let v2743 := Nat.land v585 v2742
    let v2744 := Nat.land v616 v2743
    let v2745 := Nat.land v23 v2744
    let v2746 := Nat.land v729 v2745
    let v2747 := Nat.land v750 v2746
    let v2748 := Nat.land v767 v2747
    let v2749 := Nat.land v824 v2748
    let v2750 := Nat.land v851 v2749
    let v2751 := Nat.land v921 v2750
    let v2752 := Nat.land v1020 v2751
    let v2753 := Nat.land v1088 v2752
    let v2754 := Nat.land v1185 v2753
    let v2755 := Nat.land v1252 v2754
    let v2756 := Nat.land v824 v2755
    let v2757 := Nat.land v1255 v2756
    let v2758 := Nat.land v1323 v2757
    let v2759 := Nat.land v1420 v2758
    let v2760 := Nat.land v1488 v2759
    let v2761 := Nat.land v1585 v2760
    let v2762 := Nat.land v1652 v2761
    let v2763 := Nat.land v1661 v2762
    let v2764 := Nat.land v1662 v2763
    let v2765 := Nat.land v1665 v2764
    let v2766 := Nat.land v1686 v2765
    let v2767 := Nat.land v1686 v2766
    let v2768 := Nat.land v1725 v2767
    let v2769 := Nat.land v1738 v2768
    let v2770 := Nat.land v1756 v2769
    let v2771 := Nat.land v1757 v2770
    let v2772 := Nat.land v1760 v2771
    let v2773 := Nat.land v1781 v2772
    let v2774 := Nat.land v1781 v2773
    let v2775 := Nat.land v1820 v2774
    let v2776 := Nat.land v1833 v2775
    let v2777 := Nat.land v23 v2776
    let v2778 := Nat.land v1871 v2777
    let v2779 := Nat.land v1892 v2778
    let v2780 := Nat.land v1909 v2779
    let v2781 := Nat.land v23 v2780
    let v2782 := Nat.land v110 v2781
    let v2783 := Nat.land v110 v2782
    let v2784 := Nat.land v147 v2783
    let v2785 := Nat.land v1915 v2784
    let v2786 := Nat.land v1915 v2785
    let v2787 := Nat.land v1952 v2786
    let v2788 := Nat.land v23 v2787
    let v2789 := Nat.land v2063 v2788
    let v2790 := Nat.land v2084 v2789
    let v2791 := Nat.land v2101 v2790
    let v2792 := Nat.land v23 v2791
    let v2793 := Nat.land v444 v2792
    let v2794 := Nat.land v444 v2793
    let v2795 := Nat.land v475 v2794
    let v2796 := Nat.land v2107 v2795
    let v2797 := Nat.land v2107 v2796
    let v2798 := Nat.land v2144 v2797
    let v2799 := Nat.land v23 v2798
    let v2800 := Nat.land v729 v2799
    let v2801 := Nat.land v750 v2800
    let v2802 := Nat.land v767 v2801
    let v2803 := Nat.land v2288 v2802
    let v2804 := Nat.land v2315 v2803
    let v2805 := Nat.land v2385 v2804
    let v2806 := Nat.land v2482 v2805
    let v2807 := Nat.land v2550 v2806
    let v2808 := Nat.land v2647 v2807
    let v2809 := Nat.land v2721 v2808
    ∀ (P : Prop), ((sv v2516 = sv v2341 * sv v2341) → (sv v2517 = -((-sv v2516) / 2 ^ 28)) → (sv v2518 = sv v2517 + sv v2517) → (sv v2519 = sv v33 - sv v2518) → ((v2520 = 1 ↔ sv v2519 < sv v95)) → (v2521 = if v2520 = 1 then v95 else v2519) → (sv v2522 = sv v2340 * sv v2340) → (sv v2523 = sv v2522 / 2 ^ 28) → (sv v2524 = sv v2523 + sv v2523) → (sv v2525 = sv v33 - sv v2524) → (sv v2526 = sv v2345 * sv v2345) → (sv v2527 = -((-sv v2526) / 2 ^ 28)) → (sv v2528 = sv v2527 + sv v2527) → (sv v2529 = sv v33 - sv v2528) → ((v2530 = 1 ↔ sv v2529 < sv v95)) → (v2531 = if v2530 = 1 then v95 else v2529) → (sv v2532 = sv v2344 * sv v2344) → (sv v2533 = sv v2532 / 2 ^ 28) → (sv v2534 = sv v2533 + sv v2533) → (sv v2535 = sv v33 - sv v2534) → ((v2536 = 1 ↔ sv v2521 < sv v61)) → ((v2538 = 1 ↔ sv v61 < sv v2525)) → ((v2539 = 1 ↔ ¬v2538 = 1)) → ((v2540 = 1 ↔ v2536 = 1 ∧ v2539 = 1)) → ((v2541 = 1 ↔ v2536 = 1 ∧ v2538 = 1)) → ((v2542 = 1 ↔ sv v2531 < sv v61)) → ((v2544 = 1 ↔ sv v61 < sv v2535)) → ((v2545 = 1 ↔ ¬v2544 = 1)) → ((v2546 = 1 ↔ v2542 = 1 ∧ v2545 = 1)) → ((v2547 = 1 ↔ v2542 = 1 ∧ v2544 = 1)) → ((v2548 = 1 ↔ v2541 = 1 ∧ v2547 = 1)) → ((v2549 = 1 ↔ ¬v2548 = 1)) → ((v2550 = 1 ↔ v2287 = 1 ∨ v2549 = 1)) → ((v2557 = 1 ↔ v2540 = 1 ∧ v2547 = 1)) → ((v2558 = 1 ↔ v2546 = 1 ∨ v2557 = 1)) → (v2559 = if v2558 = 1 then v2521 else v2525) → ((v2560 = 1 ↔ v2541 = 1 ∧ v2546 = 1)) → ((v2561 = 1 ↔ v2540 = 1 ∨ v2560 = 1)) → (v2562 = if v2561 = 1 then v2531 else v2535) → (sv v2565 = sv v2562 * sv v2559) → (sv v2566 = -((-sv v2565) / 2 ^ 28)) → (sv v2567 = sv v794 - sv v2566) → (sv v2569 = sv v940 - sv v2522) → (sv v2570 = ((Nat.sqrt (v2569 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2571 = sv v105 + sv v2570) → (sv v2572 = sv v2570 * sv v2340) → (sv v2573 = sv v2572 / 2 ^ 28) → (sv v2574 = sv v2573 + sv v2573) → (sv v2575 = sv v2571 * sv v2340) → (sv v2576 = -((-sv v2575) / 2 ^ 28)) → (sv v2577 = sv v2576 + sv v2576) → ((v2578 = 1 ↔ sv v2577 < sv v33)) → (v2579 = if v2578 = 1 then v2577 else v33) → (sv v2580 = sv v940 - sv v2516) → (sv v2581 = ((Nat.sqrt (v2580 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2582 = sv v105 + sv v2581) → (sv v2583 = sv v2581 * sv v2341) → (sv v2584 = sv v2583 / 2 ^ 28) → (sv v2585 = sv v2584 + sv v2584) → (sv v2586 = sv v2582 * sv v2341) → (sv v2587 = -((-sv v2586) / 2 ^ 28)) → (sv v2588 = sv v2587 + sv v2587) → ((v2589 = 1 ↔ sv v2588 < sv v33)) → (v2590 = if v2589 = 1 then v2588 else v33) → ((v2591 = 1 ↔ sv v2574 < sv v2585)) → (v2592 = if v2591 = 1 then v2574 else v2585) → ((v2593 = 1 ↔ sv v2579 < sv v2590)) → (v2594 = if v2593 = 1 then v2590 else v2579) → ((v2595 = 1 ↔ sv v967 < sv v2522)) → ((v2596 = 1 ↔ ¬v2595 = 1)) → ((v2597 = 1 ↔ sv v2516 < sv v967)) → ((v2598 = 1 ↔ ¬v2597 = 1)) → ((v2599 = 1 ↔ v2596 = 1 ∧ v2598 = 1)) → (v2600 = if v2599 = 1 then v33 else v2594) → (sv v2601 = sv v940 - sv v2532) → (sv v2602 = ((Nat.sqrt (v2601 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2603 = sv v105 + sv v2602) → (sv v2604 = sv v2602 * sv v2344) → (sv v2605 = sv v2604 / 2 ^ 28) → (sv v2606 = sv v2605 + sv v2605) → (sv v2607 = sv v2603 * sv v2344) → (sv v2608 = -((-sv v2607) / 2 ^ 28)) → (sv v2609 = sv v2608 + sv v2608) → ((v2610 = 1 ↔ sv v2609 < sv v33)) → (v2611 = if v2610 = 1 then v2609 else v33) → (sv v2612 = sv v940 - sv v2526) → (sv v2613 = ((Nat.sqrt (v2612 - 4611686018427387904) : ℕ) : ℤ)) → (sv v2614 = sv v105 + sv v2613) → (sv v2615 = sv v2613 * sv v2345) → (sv v2616 = sv v2615 / 2 ^ 28) → (sv v2617 = sv v2616 + sv v2616) → (sv v2618 = sv v2614 * sv v2345) → (sv v2619 = -((-sv v2618) / 2 ^ 28)) → (sv v2620 = sv v2619 + sv v2619) → ((v2621 = 1 ↔ sv v2620 < sv v33)) → (v2622 = if v2621 = 1 then v2620 else v33) → ((v2623 = 1 ↔ sv v2606 < sv v2617)) → (v2624 = if v2623 = 1 then v2606 else v2617) → ((v2625 = 1 ↔ sv v2611 < sv v2622)) → (v2626 = if v2625 = 1 then v2622 else v2611) → ((v2627 = 1 ↔ sv v967 < sv v2532)) → ((v2628 = 1 ↔ ¬v2627 = 1)) → ((v2629 = 1 ↔ sv v2526 < sv v967)) → ((v2630 = 1 ↔ ¬v2629 = 1)) → ((v2631 = 1 ↔ v2628 = 1 ∧ v2630 = 1)) → (v2632 = if v2631 = 1 then v33 else v2626) → ((v2633 = 1 ↔ sv v2592 < sv v61)) → ((v2634 = 1 ↔ ¬v2633 = 1)) → ((v2635 = 1 ↔ sv v61 < sv v2600)) → ((v2636 = 1 ↔ ¬v2635 = 1)) → ((v2637 = 1 ↔ v2633 = 1 ∧ v2636 = 1)) → ((v2638 = 1 ↔ v2633 = 1 ∧ v2635 = 1)) → ((v2639 = 1 ↔ sv v2624 < sv v61)) → ((v2640 = 1 ↔ ¬v2639 = 1)) → ((v2641 = 1 ↔ sv v61 < sv v2632)) → ((v2642 = 1 ↔ ¬v2641 = 1)) → ((v2643 = 1 ↔ v2639 = 1 ∧ v2642 = 1)) → ((v2644 = 1 ↔ v2639 = 1 ∧ v2641 = 1)) → ((v2645 = 1 ↔ v2638 = 1 ∧ v2644 = 1)) → ((v2646 = 1 ↔ ¬v2645 = 1)) → ((v2647 = 1 ↔ v2287 = 1 ∨ v2646 = 1)) → ((v2648 = 1 ↔ v2634 = 1 ∧ v2644 = 1)) → ((v2649 = 1 ↔ v2643 = 1 ∨ v2648 = 1)) → (v2650 = if v2649 = 1 then v2600 else v2592) → ((v2651 = 1 ↔ v2638 = 1 ∧ v2640 = 1)) → ((v2652 = 1 ↔ v2637 = 1 ∨ v2651 = 1)) → (v2653 = if v2652 = 1 then v2632 else v2624) → ((v2654 = 1 ↔ v2637 = 1 ∧ v2644 = 1)) → ((v2655 = 1 ↔ v2643 = 1 ∨ v2654 = 1)) → (v2656 = if v2655 = 1 then v2592 else v2600) → ((v2657 = 1 ↔ v2638 = 1 ∧ v2643 = 1)) → ((v2658 = 1 ↔ v2637 = 1 ∨ v2657 = 1)) → (v2659 = if v2658 = 1 then v2624 else v2632) → (sv v2660 = sv v2653 * sv v2650) → (sv v2661 = sv v2660 / 2 ^ 28) → (sv v2662 = sv v2659 * sv v2656) → (sv v2663 = -((-sv v2662) / 2 ^ 28)) → ((v2664 = 1 ↔ sv v61 < sv v2661)) → ((v2666 = 1 ↔ sv v2567 < sv v61)) → (v2667 = if v2666 = 1 then v2661 else v2663) → ((v2670 = 1 ↔ sv v2667 < sv v2567)) → ((v2671 = 1 ↔ v2664 = 1 ∧ v2670 = 1)) → ((v2678 = 1 ↔ v2507 = 1 ∨ v2671 = 1)) → (sv v2680 = ((H4 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ)) → ((v2681 = 1 ↔ sv v61 < sv v2680)) → ((v2682 = 1 ↔ ¬v2681 = 1)) → (sv t2680.2 = (sc28pS (scArg v2680)).2) → (sv v2684 = sv v28 + sv t2680.2) → ((v2685 = 1 ↔ sv v2684 < sv v95)) → (v2686 = if v2685 = 1 then v95 else v2684) → (sv v2687 = sv v2511 * 2 ^ 28) → (sv v2688 = sv v2686 * sv v2512) → ((v2689 = 1 ↔ sv v2688 < sv v2687)) → ((v2690 = 1 ↔ ¬v2689 = 1)) → ((v2691 = 1 ↔ sv v15 < sv v2680)) → ((v2692 = 1 ↔ ¬v2691 = 1)) → ((v2693 = 1 ↔ v2690 = 1 ∧ v2692 = 1)) → ((v2694 = 1 ↔ v2682 = 1 ∨ v2693 = 1)) → (v2695 = if v2694 = 1 then v2680 else v61) → (v2709 = if v2258 = 1 then v2695 else v61) → ((v2711 = 1 ↔ v2258 = 1 ∧ v2678 = 1)) → (v2712 = if v2507 = 1 then v15 else v61) → (v2714 = if v2711 = 1 then v2712 else v2709) → (sv v2716 = sv v255 + sv v2714) → (sv v2718 = sv v580 + sv v2716) → ((v2720 = 1 ↔ sv v2718 < sv v6)) → ((v2721 = 1 ↔ ¬v2720 = 1)) → ((v2724 = 1 ↔ v23 = 1 ∧ v47 = 1)) → ((v2725 = 1 ↔ v75 = 1 ∧ v2724 = 1)) → ((v2726 = 1 ↔ v92 = 1 ∧ v2725 = 1)) → ((v2727 = 1 ↔ v23 = 1 ∧ v2726 = 1)) → ((v2728 = 1 ↔ v110 = 1 ∧ v2727 = 1)) → ((v2729 = 1 ↔ v110 = 1 ∧ v2728 = 1)) → ((v2730 = 1 ↔ v147 = 1 ∧ v2729 = 1)) → ((v2731 = 1 ↔ v260 = 1 ∧ v2730 = 1)) → ((v2732 = 1 ↔ v260 = 1 ∧ v2731 = 1)) → ((v2733 = 1 ↔ v291 = 1 ∧ v2732 = 1)) → ((v2734 = 1 ↔ v23 = 1 ∧ v2733 = 1)) → ((v2735 = 1 ↔ v403 = 1 ∧ v2734 = 1)) → ((v2736 = 1 ↔ v424 = 1 ∧ v2735 = 1)) → ((v2737 = 1 ↔ v441 = 1 ∧ v2736 = 1)) → ((v2738 = 1 ↔ v23 = 1 ∧ v2737 = 1)) → ((v2739 = 1 ↔ v444 = 1 ∧ v2738 = 1)) → ((v2740 = 1 ↔ v444 = 1 ∧ v2739 = 1)) → ((v2741 = 1 ↔ v475 = 1 ∧ v2740 = 1)) → ((v2742 = 1 ↔ v585 = 1 ∧ v2741 = 1)) → ((v2743 = 1 ↔ v585 = 1 ∧ v2742 = 1)) → ((v2744 = 1 ↔ v616 = 1 ∧ v2743 = 1)) → ((v2745 = 1 ↔ v23 = 1 ∧ v2744 = 1)) → ((v2746 = 1 ↔ v729 = 1 ∧ v2745 = 1)) → ((v2747 = 1 ↔ v750 = 1 ∧ v2746 = 1)) → ((v2748 = 1 ↔ v767 = 1 ∧ v2747 = 1)) → ((v2749 = 1 ↔ v824 = 1 ∧ v2748 = 1)) → ((v2750 = 1 ↔ v851 = 1 ∧ v2749 = 1)) → ((v2751 = 1 ↔ v921 = 1 ∧ v2750 = 1)) → ((v2752 = 1 ↔ v1020 = 1 ∧ v2751 = 1)) → ((v2753 = 1 ↔ v1088 = 1 ∧ v2752 = 1)) → ((v2754 = 1 ↔ v1185 = 1 ∧ v2753 = 1)) → ((v2755 = 1 ↔ v1252 = 1 ∧ v2754 = 1)) → ((v2756 = 1 ↔ v824 = 1 ∧ v2755 = 1)) → ((v2757 = 1 ↔ v1255 = 1 ∧ v2756 = 1)) → ((v2758 = 1 ↔ v1323 = 1 ∧ v2757 = 1)) → ((v2759 = 1 ↔ v1420 = 1 ∧ v2758 = 1)) → ((v2760 = 1 ↔ v1488 = 1 ∧ v2759 = 1)) → ((v2761 = 1 ↔ v1585 = 1 ∧ v2760 = 1)) → ((v2762 = 1 ↔ v1652 = 1 ∧ v2761 = 1)) → ((v2763 = 1 ↔ v1661 = 1 ∧ v2762 = 1)) → ((v2764 = 1 ↔ v1662 = 1 ∧ v2763 = 1)) → ((v2765 = 1 ↔ v1665 = 1 ∧ v2764 = 1)) → ((v2766 = 1 ↔ v1686 = 1 ∧ v2765 = 1)) → ((v2767 = 1 ↔ v1686 = 1 ∧ v2766 = 1)) → ((v2768 = 1 ↔ v1725 = 1 ∧ v2767 = 1)) → ((v2769 = 1 ↔ v1738 = 1 ∧ v2768 = 1)) → ((v2770 = 1 ↔ v1756 = 1 ∧ v2769 = 1)) → ((v2771 = 1 ↔ v1757 = 1 ∧ v2770 = 1)) → ((v2772 = 1 ↔ v1760 = 1 ∧ v2771 = 1)) → ((v2773 = 1 ↔ v1781 = 1 ∧ v2772 = 1)) → ((v2774 = 1 ↔ v1781 = 1 ∧ v2773 = 1)) → ((v2775 = 1 ↔ v1820 = 1 ∧ v2774 = 1)) → ((v2776 = 1 ↔ v1833 = 1 ∧ v2775 = 1)) → ((v2777 = 1 ↔ v23 = 1 ∧ v2776 = 1)) → ((v2778 = 1 ↔ v1871 = 1 ∧ v2777 = 1)) → ((v2779 = 1 ↔ v1892 = 1 ∧ v2778 = 1)) → ((v2780 = 1 ↔ v1909 = 1 ∧ v2779 = 1)) → ((v2781 = 1 ↔ v23 = 1 ∧ v2780 = 1)) → ((v2782 = 1 ↔ v110 = 1 ∧ v2781 = 1)) → ((v2783 = 1 ↔ v110 = 1 ∧ v2782 = 1)) → ((v2784 = 1 ↔ v147 = 1 ∧ v2783 = 1)) → ((v2785 = 1 ↔ v1915 = 1 ∧ v2784 = 1)) → ((v2786 = 1 ↔ v1915 = 1 ∧ v2785 = 1)) → ((v2787 = 1 ↔ v1952 = 1 ∧ v2786 = 1)) → ((v2788 = 1 ↔ v23 = 1 ∧ v2787 = 1)) → ((v2789 = 1 ↔ v2063 = 1 ∧ v2788 = 1)) → ((v2790 = 1 ↔ v2084 = 1 ∧ v2789 = 1)) → ((v2791 = 1 ↔ v2101 = 1 ∧ v2790 = 1)) → ((v2792 = 1 ↔ v23 = 1 ∧ v2791 = 1)) → ((v2793 = 1 ↔ v444 = 1 ∧ v2792 = 1)) → ((v2794 = 1 ↔ v444 = 1 ∧ v2793 = 1)) → ((v2795 = 1 ↔ v475 = 1 ∧ v2794 = 1)) → ((v2796 = 1 ↔ v2107 = 1 ∧ v2795 = 1)) → ((v2797 = 1 ↔ v2107 = 1 ∧ v2796 = 1)) → ((v2798 = 1 ↔ v2144 = 1 ∧ v2797 = 1)) → ((v2799 = 1 ↔ v23 = 1 ∧ v2798 = 1)) → ((v2800 = 1 ↔ v729 = 1 ∧ v2799 = 1)) → ((v2801 = 1 ↔ v750 = 1 ∧ v2800 = 1)) → ((v2802 = 1 ↔ v767 = 1 ∧ v2801 = 1)) → ((v2803 = 1 ↔ v2288 = 1 ∧ v2802 = 1)) → ((v2804 = 1 ↔ v2315 = 1 ∧ v2803 = 1)) → ((v2805 = 1 ↔ v2385 = 1 ∧ v2804 = 1)) → ((v2806 = 1 ↔ v2482 = 1 ∧ v2805 = 1)) → ((v2807 = 1 ↔ v2550 = 1 ∧ v2806 = 1)) → ((v2808 = 1 ↔ v2647 = 1 ∧ v2807 = 1)) → ((v2809 = 1 ↔ v2721 = 1 ∧ v2808 = 1)) → P) → P := by
  intro OFFr v6 v15 v28 v33 v61 v95 v105 v940 v967 v2516 v2517 v2518 v2519 v2520 v2521 v2522 v2523 v2524 v2525 v2526 v2527 v2528 v2529 v2530 v2531 v2532 v2533 v2534 v2535 v2536 v2538 v2539 v2540 v2541 v2542 v2544 v2545 v2546 v2547 v2548 v2549 v2550 v2557 v2558 v2559 v2560 v2561 v2562 v2565 v2566 v2567 v2569 v2570 v2571 v2572 v2573 v2574 v2575 v2576 v2577 v2578 v2579 v2580 v2581 v2582 v2583 v2584 v2585 v2586 v2587 v2588 v2589 v2590 v2591 v2592 v2593 v2594 v2595 v2596 v2597 v2598 v2599 v2600 v2601 v2602 v2603 v2604 v2605 v2606 v2607 v2608 v2609 v2610 v2611 v2612 v2613 v2614 v2615 v2616 v2617 v2618 v2619 v2620 v2621 v2622 v2623 v2624 v2625 v2626 v2627 v2628 v2629 v2630 v2631 v2632 v2633 v2634 v2635 v2636 v2637 v2638 v2639 v2640 v2641 v2642 v2643 v2644 v2645 v2646 v2647 v2648 v2649 v2650 v2651 v2652 v2653 v2654 v2655 v2656 v2657 v2658 v2659 v2660 v2661 v2662 v2663 v2664 v2666 v2667 v2670 v2671 v2678 v2680 v2681 v2682 t2680 v2684 v2685 v2686 v2687 v2688 v2689 v2690 v2691 v2692 v2693 v2694 v2695 v2709 v2711 v2712 v2714 v2716 v2718 v2720 v2721 v2724 v2725 v2726 v2727 v2728 v2729 v2730 v2731 v2732 v2733 v2734 v2735 v2736 v2737 v2738 v2739 v2740 v2741 v2742 v2743 v2744 v2745 v2746 v2747 v2748 v2749 v2750 v2751 v2752 v2753 v2754 v2755 v2756 v2757 v2758 v2759 v2760 v2761 v2762 v2763 v2764 v2765 v2766 v2767 v2768 v2769 v2770 v2771 v2772 v2773 v2774 v2775 v2776 v2777 v2778 v2779 v2780 v2781 v2782 v2783 v2784 v2785 v2786 v2787 v2788 v2789 v2790 v2791 v2792 v2793 v2794 v2795 v2796 v2797 v2798 v2799 v2800 v2801 v2802 v2803 v2804 v2805 v2806 v2807 v2808 v2809
  have hl : 0 < 1 := Nat.one_pos
  have h_OFFr : R 1 0 4611686018427387904 4611686018427387904 OFFr OFFr := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v6 : R 1 0 4611686018427387904 4611686087146864624 v6 v6 := (r1_ix hb_F3 0 (of_decide_eq_true rfl))
  have h_v15 : R 1 0 4611686019270702760 4611686019270702760 v15 v15 := (r_c hl 4611686019270702760 (of_decide_eq_true rfl))
  have h_v28 : R 1 0 4611686018427387900 4611686018427387900 v28 v28 := (r_c hl 4611686018427387900 (of_decide_eq_true rfl))
  have h_v33 : R 1 0 4611686018695823360 4611686018695823360 v33 v33 := (r_c hl 4611686018695823360 (of_decide_eq_true rfl))
  have h_v61 : R 1 0 4611686018427387904 4611686018427387904 v61 v61 := (r_c hl 4611686018427387904 (of_decide_eq_true rfl))
  have h_v95 : R 1 0 4611686018158952448 4611686018158952448 v95 v95 := (r_c hl 4611686018158952448 (of_decide_eq_true rfl))
  have h_v105 : R 1 0 4611686018427387905 4611686018427387905 v105 v105 := (r_c hl 4611686018427387905 (of_decide_eq_true rfl))
  have h_v940 : R 1 0 4683743612465315840 4683743612465315840 v940 v940 := (r_c hl 4683743612465315840 (of_decide_eq_true rfl))
  have h_v967 : R 1 0 4647714815446351872 4647714815446351872 v967 v967 := (r_c hl 4647714815446351872 (of_decide_eq_true rfl))
  have h_v2516 : R 1 0 4611686018427387904 4683743620518379745 v2516 v2516 := (r_smx_sq hl 29 h_v2341 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2516 : sv v2516 = sv v2341 * sv v2341 := e_smx_sq 29 h_v2341 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2517 : R 1 0 4611686018427387904 4611686018695823391 v2517 v2517 := (r_srdC hl h_v2516 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v2517 : sv v2517 = -((-sv v2516) / 2 ^ 28) := e_srdC h_v2516 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v2518 : R 1 0 4611686018427387904 4611686018964258878 v2518 v2518 := (r_sub hl (r_add hl h_v2517 h_v2517 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2518 : sv v2518 = sv v2517 + sv v2517 := e_add h_v2517 h_v2517 (of_decide_eq_true rfl)
  have h_v2519 : R 1 0 4611686018158952386 4611686018695823360 v2519 v2519 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v2518 (of_decide_eq_true rfl))
  have e_v2519 : sv v2519 = sv v33 - sv v2518 := e_sub h_v33 h_v2518 (of_decide_eq_true rfl)
  have h_v2520 : R 1 0 0 1 v2520 v2520 := (r_plt hl h_v2519 h_v95 (of_decide_eq_true rfl))
  have e_v2520 : (v2520 = 1 ↔ sv v2519 < sv v95) := e_plt h_v2519 h_v95 (of_decide_eq_true rfl)
  have h_v2521 : R 1 0 4611686018158952386 4611686018695823360 v2521 v2521 := (r_psel hl h_v2520 h_v95 h_v2519 (of_decide_eq_true rfl))
  have e_v2521 : v2521 = if v2520 = 1 then v95 else v2519 := e_psel h_v2520 h_v95 h_v2519 (of_decide_eq_true rfl)
  have h_v2522 : R 1 0 4611686018427387904 4683743620518379745 v2522 v2522 := (r_smx_sq hl 29 h_v2340 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2522 : sv v2522 = sv v2340 * sv v2340 := e_smx_sq 29 h_v2340 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2523 : R 1 0 4611686018427387904 4611686018695823390 v2523 v2523 := (r_srdF hl h_v2522 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  clear h_v2517 h_v2518 h_v2519 h_v2520
  have e_v2523 : sv v2523 = sv v2522 / 2 ^ 28 := e_srdF h_v2522 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v2524 : R 1 0 4611686018427387904 4611686018964258876 v2524 v2524 := (r_sub hl (r_add hl h_v2523 h_v2523 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2524 : sv v2524 = sv v2523 + sv v2523 := e_add h_v2523 h_v2523 (of_decide_eq_true rfl)
  have h_v2525 : R 1 0 4611686018158952388 4611686018695823360 v2525 v2525 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v2524 (of_decide_eq_true rfl))
  have e_v2525 : sv v2525 = sv v33 - sv v2524 := e_sub h_v33 h_v2524 (of_decide_eq_true rfl)
  have h_v2526 : R 1 0 4611686018427387904 4683743620518379745 v2526 v2526 := (r_smx_sq hl 29 h_v2345 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2526 : sv v2526 = sv v2345 * sv v2345 := e_smx_sq 29 h_v2345 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2527 : R 1 0 4611686018427387904 4611686018695823391 v2527 v2527 := (r_srdC hl h_v2526 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl))
  have e_v2527 : sv v2527 = -((-sv v2526) / 2 ^ 28) := e_srdC h_v2526 4611686018427387904 4611686018695823391 (of_decide_eq_true rfl)
  have h_v2528 : R 1 0 4611686018427387904 4611686018964258878 v2528 v2528 := (r_sub hl (r_add hl h_v2527 h_v2527 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2528 : sv v2528 = sv v2527 + sv v2527 := e_add h_v2527 h_v2527 (of_decide_eq_true rfl)
  have h_v2529 : R 1 0 4611686018158952386 4611686018695823360 v2529 v2529 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v2528 (of_decide_eq_true rfl))
  have e_v2529 : sv v2529 = sv v33 - sv v2528 := e_sub h_v33 h_v2528 (of_decide_eq_true rfl)
  have h_v2530 : R 1 0 0 1 v2530 v2530 := (r_plt hl h_v2529 h_v95 (of_decide_eq_true rfl))
  have e_v2530 : (v2530 = 1 ↔ sv v2529 < sv v95) := e_plt h_v2529 h_v95 (of_decide_eq_true rfl)
  have h_v2531 : R 1 0 4611686018158952386 4611686018695823360 v2531 v2531 := (r_psel hl h_v2530 h_v95 h_v2529 (of_decide_eq_true rfl))
  have e_v2531 : v2531 = if v2530 = 1 then v95 else v2529 := e_psel h_v2530 h_v95 h_v2529 (of_decide_eq_true rfl)
  have h_v2532 : R 1 0 4611686018427387904 4683743620518379745 v2532 v2532 := (r_smx_sq hl 29 h_v2344 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl))
  have e_v2532 : sv v2532 = sv v2344 * sv v2344 := e_smx_sq 29 h_v2344 4611686018427387904 4683743620518379745 (of_decide_eq_true rfl)
  have h_v2533 : R 1 0 4611686018427387904 4611686018695823390 v2533 v2533 := (r_srdF hl h_v2532 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl))
  have e_v2533 : sv v2533 = sv v2532 / 2 ^ 28 := e_srdF h_v2532 4611686018427387904 4611686018695823390 (of_decide_eq_true rfl)
  have h_v2534 : R 1 0 4611686018427387904 4611686018964258876 v2534 v2534 := (r_sub hl (r_add hl h_v2533 h_v2533 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2534 : sv v2534 = sv v2533 + sv v2533 := e_add h_v2533 h_v2533 (of_decide_eq_true rfl)
  have h_v2535 : R 1 0 4611686018158952388 4611686018695823360 v2535 v2535 := (r_sub hl (r_add hl h_v33 h_OFFr (of_decide_eq_true rfl)) h_v2534 (of_decide_eq_true rfl))
  have e_v2535 : sv v2535 = sv v33 - sv v2534 := e_sub h_v33 h_v2534 (of_decide_eq_true rfl)
  clear h_v2523 h_v2524 h_v2527 h_v2528 h_v2529 h_v2530 h_v2533 h_v2534
  have h_v2536 : R 1 0 0 1 v2536 v2536 := (r_plt hl h_v2521 h_v61 (of_decide_eq_true rfl))
  have e_v2536 : (v2536 = 1 ↔ sv v2521 < sv v61) := e_plt h_v2521 h_v61 (of_decide_eq_true rfl)
  have h_v2538 : R 1 0 0 1 v2538 v2538 := (r_plt hl h_v61 h_v2525 (of_decide_eq_true rfl))
  have e_v2538 : (v2538 = 1 ↔ sv v61 < sv v2525) := e_plt h_v61 h_v2525 (of_decide_eq_true rfl)
  have h_v2539 : R 1 0 0 1 v2539 v2539 := (r_sub hl (r_O hl) h_v2538 (of_decide_eq_true rfl))
  have e_v2539 : (v2539 = 1 ↔ ¬v2538 = 1) := e_not h_v2538 (of_decide_eq_true rfl)
  have h_v2540 : R 1 0 0 1 v2540 v2540 := (r_land hl h_v2536 h_v2539 (of_decide_eq_true rfl))
  have e_v2540 : (v2540 = 1 ↔ v2536 = 1 ∧ v2539 = 1) := e_land h_v2536 h_v2539 (of_decide_eq_true rfl)
  have h_v2541 : R 1 0 0 1 v2541 v2541 := (r_land hl h_v2536 h_v2538 (of_decide_eq_true rfl))
  have e_v2541 : (v2541 = 1 ↔ v2536 = 1 ∧ v2538 = 1) := e_land h_v2536 h_v2538 (of_decide_eq_true rfl)
  have h_v2542 : R 1 0 0 1 v2542 v2542 := (r_plt hl h_v2531 h_v61 (of_decide_eq_true rfl))
  have e_v2542 : (v2542 = 1 ↔ sv v2531 < sv v61) := e_plt h_v2531 h_v61 (of_decide_eq_true rfl)
  have h_v2544 : R 1 0 0 1 v2544 v2544 := (r_plt hl h_v61 h_v2535 (of_decide_eq_true rfl))
  have e_v2544 : (v2544 = 1 ↔ sv v61 < sv v2535) := e_plt h_v61 h_v2535 (of_decide_eq_true rfl)
  have h_v2545 : R 1 0 0 1 v2545 v2545 := (r_sub hl (r_O hl) h_v2544 (of_decide_eq_true rfl))
  have e_v2545 : (v2545 = 1 ↔ ¬v2544 = 1) := e_not h_v2544 (of_decide_eq_true rfl)
  have h_v2546 : R 1 0 0 1 v2546 v2546 := (r_land hl h_v2542 h_v2545 (of_decide_eq_true rfl))
  have e_v2546 : (v2546 = 1 ↔ v2542 = 1 ∧ v2545 = 1) := e_land h_v2542 h_v2545 (of_decide_eq_true rfl)
  have h_v2547 : R 1 0 0 1 v2547 v2547 := (r_land hl h_v2542 h_v2544 (of_decide_eq_true rfl))
  have e_v2547 : (v2547 = 1 ↔ v2542 = 1 ∧ v2544 = 1) := e_land h_v2542 h_v2544 (of_decide_eq_true rfl)
  have h_v2548 : R 1 0 0 1 v2548 v2548 := (r_land hl h_v2541 h_v2547 (of_decide_eq_true rfl))
  have e_v2548 : (v2548 = 1 ↔ v2541 = 1 ∧ v2547 = 1) := e_land h_v2541 h_v2547 (of_decide_eq_true rfl)
  have h_v2549 : R 1 0 0 1 v2549 v2549 := (r_sub hl (r_O hl) h_v2548 (of_decide_eq_true rfl))
  have e_v2549 : (v2549 = 1 ↔ ¬v2548 = 1) := e_not h_v2548 (of_decide_eq_true rfl)
  have h_v2550 : R 1 0 0 1 v2550 v2550 := (r_lor hl h_v2287 h_v2549 (of_decide_eq_true rfl))
  clear h_v2536 h_v2538 h_v2539 h_v2542 h_v2544 h_v2545 h_v2548
  have e_v2550 : (v2550 = 1 ↔ v2287 = 1 ∨ v2549 = 1) := e_lor h_v2287 h_v2549 (of_decide_eq_true rfl)
  have h_v2557 : R 1 0 0 1 v2557 v2557 := (r_land hl h_v2540 h_v2547 (of_decide_eq_true rfl))
  have e_v2557 : (v2557 = 1 ↔ v2540 = 1 ∧ v2547 = 1) := e_land h_v2540 h_v2547 (of_decide_eq_true rfl)
  have h_v2558 : R 1 0 0 1 v2558 v2558 := (r_lor hl h_v2546 h_v2557 (of_decide_eq_true rfl))
  have e_v2558 : (v2558 = 1 ↔ v2546 = 1 ∨ v2557 = 1) := e_lor h_v2546 h_v2557 (of_decide_eq_true rfl)
  have h_v2559 : R 1 0 4611686018158952386 4611686018695823360 v2559 v2559 := (r_psel hl h_v2558 h_v2521 h_v2525 (of_decide_eq_true rfl))
  have e_v2559 : v2559 = if v2558 = 1 then v2521 else v2525 := e_psel h_v2558 h_v2521 h_v2525 (of_decide_eq_true rfl)
  have h_v2560 : R 1 0 0 1 v2560 v2560 := (r_land hl h_v2541 h_v2546 (of_decide_eq_true rfl))
  have e_v2560 : (v2560 = 1 ↔ v2541 = 1 ∧ v2546 = 1) := e_land h_v2541 h_v2546 (of_decide_eq_true rfl)
  have h_v2561 : R 1 0 0 1 v2561 v2561 := (r_lor hl h_v2540 h_v2560 (of_decide_eq_true rfl))
  have e_v2561 : (v2561 = 1 ↔ v2540 = 1 ∨ v2560 = 1) := e_lor h_v2540 h_v2560 (of_decide_eq_true rfl)
  have h_v2562 : R 1 0 4611686018158952386 4611686018695823360 v2562 v2562 := (r_psel hl h_v2561 h_v2531 h_v2535 (of_decide_eq_true rfl))
  have e_v2562 : v2562 = if v2561 = 1 then v2531 else v2535 := e_psel h_v2561 h_v2531 h_v2535 (of_decide_eq_true rfl)
  have h_v2565 : R 1 0 4539628407746461696 4683743645751316228 v2565 v2565 := (r_smx hl 30 h_v2562 h_v2559 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl))
  have e_v2565 : sv v2565 = sv v2562 * sv v2559 := e_smx 30 h_v2562 h_v2559 4539628407746461696 4683743645751316228 (of_decide_eq_true rfl)
  have h_v2566 : R 1 0 4611686018158952386 4611686018695823485 v2566 v2566 := (r_srdC hl h_v2565 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl))
  have e_v2566 : sv v2566 = -((-sv v2565) / 2 ^ 28) := e_srdC h_v2565 4611686018158952386 4611686018695823485 (of_decide_eq_true rfl)
  have h_v2567 : R 1 0 4611686017890516805 4611686018964258878 v2567 v2567 := (r_sub hl (r_add hl h_v794 h_OFFr (of_decide_eq_true rfl)) h_v2566 (of_decide_eq_true rfl))
  have e_v2567 : sv v2567 = sv v794 - sv v2566 := e_sub h_v794 h_v2566 (of_decide_eq_true rfl)
  have h_v2569 : R 1 0 4611686010374323999 4683743612465315840 v2569 v2569 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v2522 (of_decide_eq_true rfl))
  have e_v2569 : sv v2569 = sv v940 - sv v2522 := e_sub h_v940 h_v2522 (of_decide_eq_true rfl)
  have h_v2570 : R 1 0 4611686018427387904 4611686018695823360 v2570 v2570 := (r_psqrt hl h_v2569 (of_decide_eq_true rfl))
  have e_v2570 : sv v2570 = ((Nat.sqrt (v2569 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2569 (of_decide_eq_true rfl)
  have h_v2571 : R 1 0 4611686018427387905 4611686018695823361 v2571 v2571 := (r_sub hl (r_add hl h_v105 h_v2570 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2571 : sv v2571 = sv v105 + sv v2570 := e_add h_v105 h_v2570 (of_decide_eq_true rfl)
  clear h_v2521 h_v2525 h_v2531 h_v2535 h_v2540 h_v2541 h_v2546 h_v2547 h_v2549 h_v2557 h_v2558 h_v2559 h_v2560 h_v2561 h_v2562 h_v2565 h_v2566 h_v2569
  have pb_v2570_v2340 : PB 1 v2570 v2340 36028797018963968 := pb_sqrt hl h_v2340 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v2572 : R 1 0 4611686017085210624 4647714815446351872 v2572 v2572 := (r_smx_pb hl 29 h_v2570 h_v2340 pb_v2570_v2340 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2572 : sv v2572 = sv v2570 * sv v2340 := e_smx_pb 29 h_v2570 h_v2340 pb_v2570_v2340 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2573 : R 1 0 4611686018427387899 4611686018561605632 v2573 v2573 := (r_srdF hl h_v2572 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2573 : sv v2573 = sv v2572 / 2 ^ 28 := e_srdF h_v2572 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2574 : R 1 0 4611686018427387894 4611686018695823360 v2574 v2574 := (r_sub hl (r_add hl h_v2573 h_v2573 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2574 : sv v2574 = sv v2573 + sv v2573 := e_add h_v2573 h_v2573 (of_decide_eq_true rfl)
  have pb_v2571_v2340 : PB 1 v2571 v2340 36028797287399439 := pb_sqrt1 hl h_v2340 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2575 : R 1 0 4611686017085210619 4647714815714787343 v2575 v2575 := (r_smx_pb hl 29 h_v2571 h_v2340 pb_v2571_v2340 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2575 : sv v2575 = sv v2571 * sv v2340 := e_smx_pb 29 h_v2571 h_v2340 pb_v2571_v2340 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2576 : R 1 0 4611686018427387899 4611686018561605634 v2576 v2576 := (r_srdC hl h_v2575 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2576 : sv v2576 = -((-sv v2575) / 2 ^ 28) := e_srdC h_v2575 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2577 : R 1 0 4611686018427387894 4611686018695823364 v2577 v2577 := (r_sub hl (r_add hl h_v2576 h_v2576 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2577 : sv v2577 = sv v2576 + sv v2576 := e_add h_v2576 h_v2576 (of_decide_eq_true rfl)
  have h_v2578 : R 1 0 0 1 v2578 v2578 := (r_plt hl h_v2577 h_v33 (of_decide_eq_true rfl))
  have e_v2578 : (v2578 = 1 ↔ sv v2577 < sv v33) := e_plt h_v2577 h_v33 (of_decide_eq_true rfl)
  have h_v2579 : R 1 0 4611686018427387894 4611686018695823364 v2579 v2579 := (r_psel hl h_v2578 h_v2577 h_v33 (of_decide_eq_true rfl))
  have e_v2579 : v2579 = if v2578 = 1 then v2577 else v33 := e_psel h_v2578 h_v2577 h_v33 (of_decide_eq_true rfl)
  have h_v2580 : R 1 0 4611686010374323999 4683743612465315840 v2580 v2580 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v2516 (of_decide_eq_true rfl))
  have e_v2580 : sv v2580 = sv v940 - sv v2516 := e_sub h_v940 h_v2516 (of_decide_eq_true rfl)
  have h_v2581 : R 1 0 4611686018427387904 4611686018695823360 v2581 v2581 := (r_psqrt hl h_v2580 (of_decide_eq_true rfl))
  have e_v2581 : sv v2581 = ((Nat.sqrt (v2580 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2580 (of_decide_eq_true rfl)
  have h_v2582 : R 1 0 4611686018427387905 4611686018695823361 v2582 v2582 := (r_sub hl (r_add hl h_v105 h_v2581 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2582 : sv v2582 = sv v105 + sv v2581 := e_add h_v105 h_v2581 (of_decide_eq_true rfl)
  have pb_v2581_v2341 : PB 1 v2581 v2341 36028797018963968 := pb_sqrt hl h_v2341 29 36028797018963968 (of_decide_eq_true rfl)
  clear h_v2570 h_v2571 pb_v2570_v2340 h_v2572 h_v2573 pb_v2571_v2340 h_v2575 h_v2576 h_v2577 h_v2578 h_v2580
  have h_v2583 : R 1 0 4611686017085210624 4647714815446351872 v2583 v2583 := (r_smx_pb hl 29 h_v2581 h_v2341 pb_v2581_v2341 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2583 : sv v2583 = sv v2581 * sv v2341 := e_smx_pb 29 h_v2581 h_v2341 pb_v2581_v2341 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2584 : R 1 0 4611686018427387899 4611686018561605632 v2584 v2584 := (r_srdF hl h_v2583 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2584 : sv v2584 = sv v2583 / 2 ^ 28 := e_srdF h_v2583 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2585 : R 1 0 4611686018427387894 4611686018695823360 v2585 v2585 := (r_sub hl (r_add hl h_v2584 h_v2584 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2585 : sv v2585 = sv v2584 + sv v2584 := e_add h_v2584 h_v2584 (of_decide_eq_true rfl)
  have pb_v2582_v2341 : PB 1 v2582 v2341 36028797287399439 := pb_sqrt1 hl h_v2341 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2586 : R 1 0 4611686017085210619 4647714815714787343 v2586 v2586 := (r_smx_pb hl 29 h_v2582 h_v2341 pb_v2582_v2341 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2586 : sv v2586 = sv v2582 * sv v2341 := e_smx_pb 29 h_v2582 h_v2341 pb_v2582_v2341 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2587 : R 1 0 4611686018427387899 4611686018561605634 v2587 v2587 := (r_srdC hl h_v2586 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2587 : sv v2587 = -((-sv v2586) / 2 ^ 28) := e_srdC h_v2586 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2588 : R 1 0 4611686018427387894 4611686018695823364 v2588 v2588 := (r_sub hl (r_add hl h_v2587 h_v2587 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2588 : sv v2588 = sv v2587 + sv v2587 := e_add h_v2587 h_v2587 (of_decide_eq_true rfl)
  have h_v2589 : R 1 0 0 1 v2589 v2589 := (r_plt hl h_v2588 h_v33 (of_decide_eq_true rfl))
  have e_v2589 : (v2589 = 1 ↔ sv v2588 < sv v33) := e_plt h_v2588 h_v33 (of_decide_eq_true rfl)
  have h_v2590 : R 1 0 4611686018427387894 4611686018695823364 v2590 v2590 := (r_psel hl h_v2589 h_v2588 h_v33 (of_decide_eq_true rfl))
  have e_v2590 : v2590 = if v2589 = 1 then v2588 else v33 := e_psel h_v2589 h_v2588 h_v33 (of_decide_eq_true rfl)
  have h_v2591 : R 1 0 0 1 v2591 v2591 := (r_plt hl h_v2574 h_v2585 (of_decide_eq_true rfl))
  have e_v2591 : (v2591 = 1 ↔ sv v2574 < sv v2585) := e_plt h_v2574 h_v2585 (of_decide_eq_true rfl)
  have h_v2592 : R 1 0 4611686018427387894 4611686018695823360 v2592 v2592 := (r_psel hl h_v2591 h_v2574 h_v2585 (of_decide_eq_true rfl))
  have e_v2592 : v2592 = if v2591 = 1 then v2574 else v2585 := e_psel h_v2591 h_v2574 h_v2585 (of_decide_eq_true rfl)
  have h_v2593 : R 1 0 0 1 v2593 v2593 := (r_plt hl h_v2579 h_v2590 (of_decide_eq_true rfl))
  have e_v2593 : (v2593 = 1 ↔ sv v2579 < sv v2590) := e_plt h_v2579 h_v2590 (of_decide_eq_true rfl)
  have h_v2594 : R 1 0 4611686018427387894 4611686018695823364 v2594 v2594 := (r_psel hl h_v2593 h_v2590 h_v2579 (of_decide_eq_true rfl))
  have e_v2594 : v2594 = if v2593 = 1 then v2590 else v2579 := e_psel h_v2593 h_v2590 h_v2579 (of_decide_eq_true rfl)
  clear h_v2574 h_v2579 h_v2581 h_v2582 pb_v2581_v2341 h_v2583 h_v2584 h_v2585 pb_v2582_v2341 h_v2586 h_v2587 h_v2588 h_v2589 h_v2590 h_v2591 h_v2593
  have h_v2595 : R 1 0 0 1 v2595 v2595 := (r_plt hl h_v967 h_v2522 (of_decide_eq_true rfl))
  have e_v2595 : (v2595 = 1 ↔ sv v967 < sv v2522) := e_plt h_v967 h_v2522 (of_decide_eq_true rfl)
  have h_v2596 : R 1 0 0 1 v2596 v2596 := (r_sub hl (r_O hl) h_v2595 (of_decide_eq_true rfl))
  have e_v2596 : (v2596 = 1 ↔ ¬v2595 = 1) := e_not h_v2595 (of_decide_eq_true rfl)
  have h_v2597 : R 1 0 0 1 v2597 v2597 := (r_plt hl h_v2516 h_v967 (of_decide_eq_true rfl))
  have e_v2597 : (v2597 = 1 ↔ sv v2516 < sv v967) := e_plt h_v2516 h_v967 (of_decide_eq_true rfl)
  have h_v2598 : R 1 0 0 1 v2598 v2598 := (r_sub hl (r_O hl) h_v2597 (of_decide_eq_true rfl))
  have e_v2598 : (v2598 = 1 ↔ ¬v2597 = 1) := e_not h_v2597 (of_decide_eq_true rfl)
  have h_v2599 : R 1 0 0 1 v2599 v2599 := (r_land hl h_v2596 h_v2598 (of_decide_eq_true rfl))
  have e_v2599 : (v2599 = 1 ↔ v2596 = 1 ∧ v2598 = 1) := e_land h_v2596 h_v2598 (of_decide_eq_true rfl)
  have h_v2600 : R 1 0 4611686018427387894 4611686018695823364 v2600 v2600 := (r_psel hl h_v2599 h_v33 h_v2594 (of_decide_eq_true rfl))
  have e_v2600 : v2600 = if v2599 = 1 then v33 else v2594 := e_psel h_v2599 h_v33 h_v2594 (of_decide_eq_true rfl)
  have h_v2601 : R 1 0 4611686010374323999 4683743612465315840 v2601 v2601 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v2532 (of_decide_eq_true rfl))
  have e_v2601 : sv v2601 = sv v940 - sv v2532 := e_sub h_v940 h_v2532 (of_decide_eq_true rfl)
  have h_v2602 : R 1 0 4611686018427387904 4611686018695823360 v2602 v2602 := (r_psqrt hl h_v2601 (of_decide_eq_true rfl))
  have e_v2602 : sv v2602 = ((Nat.sqrt (v2601 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2601 (of_decide_eq_true rfl)
  have h_v2603 : R 1 0 4611686018427387905 4611686018695823361 v2603 v2603 := (r_sub hl (r_add hl h_v105 h_v2602 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2603 : sv v2603 = sv v105 + sv v2602 := e_add h_v105 h_v2602 (of_decide_eq_true rfl)
  have pb_v2602_v2344 : PB 1 v2602 v2344 36028797018963968 := pb_sqrt hl h_v2344 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v2604 : R 1 0 4611686017085210624 4647714815446351872 v2604 v2604 := (r_smx_pb hl 29 h_v2602 h_v2344 pb_v2602_v2344 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2604 : sv v2604 = sv v2602 * sv v2344 := e_smx_pb 29 h_v2602 h_v2344 pb_v2602_v2344 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2605 : R 1 0 4611686018427387899 4611686018561605632 v2605 v2605 := (r_srdF hl h_v2604 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2605 : sv v2605 = sv v2604 / 2 ^ 28 := e_srdF h_v2604 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2606 : R 1 0 4611686018427387894 4611686018695823360 v2606 v2606 := (r_sub hl (r_add hl h_v2605 h_v2605 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2606 : sv v2606 = sv v2605 + sv v2605 := e_add h_v2605 h_v2605 (of_decide_eq_true rfl)
  clear h_v2516 h_v2522 h_v2594 h_v2595 h_v2596 h_v2597 h_v2598 h_v2599 h_v2601 h_v2602 pb_v2602_v2344 h_v2604 h_v2605
  have pb_v2603_v2344 : PB 1 v2603 v2344 36028797287399439 := pb_sqrt1 hl h_v2344 29 36028797287399439 (of_decide_eq_true rfl)
  have h_v2607 : R 1 0 4611686017085210619 4647714815714787343 v2607 v2607 := (r_smx_pb hl 29 h_v2603 h_v2344 pb_v2603_v2344 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2607 : sv v2607 = sv v2603 * sv v2344 := e_smx_pb 29 h_v2603 h_v2344 pb_v2603_v2344 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2608 : R 1 0 4611686018427387899 4611686018561605634 v2608 v2608 := (r_srdC hl h_v2607 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2608 : sv v2608 = -((-sv v2607) / 2 ^ 28) := e_srdC h_v2607 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2609 : R 1 0 4611686018427387894 4611686018695823364 v2609 v2609 := (r_sub hl (r_add hl h_v2608 h_v2608 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2609 : sv v2609 = sv v2608 + sv v2608 := e_add h_v2608 h_v2608 (of_decide_eq_true rfl)
  have h_v2610 : R 1 0 0 1 v2610 v2610 := (r_plt hl h_v2609 h_v33 (of_decide_eq_true rfl))
  have e_v2610 : (v2610 = 1 ↔ sv v2609 < sv v33) := e_plt h_v2609 h_v33 (of_decide_eq_true rfl)
  have h_v2611 : R 1 0 4611686018427387894 4611686018695823364 v2611 v2611 := (r_psel hl h_v2610 h_v2609 h_v33 (of_decide_eq_true rfl))
  have e_v2611 : v2611 = if v2610 = 1 then v2609 else v33 := e_psel h_v2610 h_v2609 h_v33 (of_decide_eq_true rfl)
  have h_v2612 : R 1 0 4611686010374323999 4683743612465315840 v2612 v2612 := (r_sub hl (r_add hl h_v940 h_OFFr (of_decide_eq_true rfl)) h_v2526 (of_decide_eq_true rfl))
  have e_v2612 : sv v2612 = sv v940 - sv v2526 := e_sub h_v940 h_v2526 (of_decide_eq_true rfl)
  have h_v2613 : R 1 0 4611686018427387904 4611686018695823360 v2613 v2613 := (r_psqrt hl h_v2612 (of_decide_eq_true rfl))
  have e_v2613 : sv v2613 = ((Nat.sqrt (v2612 - 4611686018427387904) : ℕ) : ℤ) := e_psqrt h_v2612 (of_decide_eq_true rfl)
  have h_v2614 : R 1 0 4611686018427387905 4611686018695823361 v2614 v2614 := (r_sub hl (r_add hl h_v105 h_v2613 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2614 : sv v2614 = sv v105 + sv v2613 := e_add h_v105 h_v2613 (of_decide_eq_true rfl)
  have pb_v2613_v2345 : PB 1 v2613 v2345 36028797018963968 := pb_sqrt hl h_v2345 29 36028797018963968 (of_decide_eq_true rfl)
  have h_v2615 : R 1 0 4611686017085210624 4647714815446351872 v2615 v2615 := (r_smx_pb hl 29 h_v2613 h_v2345 pb_v2613_v2345 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl))
  have e_v2615 : sv v2615 = sv v2613 * sv v2345 := e_smx_pb 29 h_v2613 h_v2345 pb_v2613_v2345 4611686017085210624 4647714815446351872 (of_decide_eq_true rfl)
  have h_v2616 : R 1 0 4611686018427387899 4611686018561605632 v2616 v2616 := (r_srdF hl h_v2615 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl))
  have e_v2616 : sv v2616 = sv v2615 / 2 ^ 28 := e_srdF h_v2615 4611686018427387899 4611686018561605632 (of_decide_eq_true rfl)
  have h_v2617 : R 1 0 4611686018427387894 4611686018695823360 v2617 v2617 := (r_sub hl (r_add hl h_v2616 h_v2616 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2617 : sv v2617 = sv v2616 + sv v2616 := e_add h_v2616 h_v2616 (of_decide_eq_true rfl)
  have pb_v2614_v2345 : PB 1 v2614 v2345 36028797287399439 := pb_sqrt1 hl h_v2345 29 36028797287399439 (of_decide_eq_true rfl)
  clear h_v105 h_v940 h_v2603 pb_v2603_v2344 h_v2607 h_v2608 h_v2609 h_v2610 h_v2612 h_v2613 pb_v2613_v2345 h_v2615 h_v2616
  have h_v2618 : R 1 0 4611686017085210619 4647714815714787343 v2618 v2618 := (r_smx_pb hl 29 h_v2614 h_v2345 pb_v2614_v2345 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl))
  have e_v2618 : sv v2618 = sv v2614 * sv v2345 := e_smx_pb 29 h_v2614 h_v2345 pb_v2614_v2345 4611686017085210619 4647714815714787343 (of_decide_eq_true rfl)
  have h_v2619 : R 1 0 4611686018427387899 4611686018561605634 v2619 v2619 := (r_srdC hl h_v2618 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl))
  have e_v2619 : sv v2619 = -((-sv v2618) / 2 ^ 28) := e_srdC h_v2618 4611686018427387899 4611686018561605634 (of_decide_eq_true rfl)
  have h_v2620 : R 1 0 4611686018427387894 4611686018695823364 v2620 v2620 := (r_sub hl (r_add hl h_v2619 h_v2619 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2620 : sv v2620 = sv v2619 + sv v2619 := e_add h_v2619 h_v2619 (of_decide_eq_true rfl)
  have h_v2621 : R 1 0 0 1 v2621 v2621 := (r_plt hl h_v2620 h_v33 (of_decide_eq_true rfl))
  have e_v2621 : (v2621 = 1 ↔ sv v2620 < sv v33) := e_plt h_v2620 h_v33 (of_decide_eq_true rfl)
  have h_v2622 : R 1 0 4611686018427387894 4611686018695823364 v2622 v2622 := (r_psel hl h_v2621 h_v2620 h_v33 (of_decide_eq_true rfl))
  have e_v2622 : v2622 = if v2621 = 1 then v2620 else v33 := e_psel h_v2621 h_v2620 h_v33 (of_decide_eq_true rfl)
  have h_v2623 : R 1 0 0 1 v2623 v2623 := (r_plt hl h_v2606 h_v2617 (of_decide_eq_true rfl))
  have e_v2623 : (v2623 = 1 ↔ sv v2606 < sv v2617) := e_plt h_v2606 h_v2617 (of_decide_eq_true rfl)
  have h_v2624 : R 1 0 4611686018427387894 4611686018695823360 v2624 v2624 := (r_psel hl h_v2623 h_v2606 h_v2617 (of_decide_eq_true rfl))
  have e_v2624 : v2624 = if v2623 = 1 then v2606 else v2617 := e_psel h_v2623 h_v2606 h_v2617 (of_decide_eq_true rfl)
  have h_v2625 : R 1 0 0 1 v2625 v2625 := (r_plt hl h_v2611 h_v2622 (of_decide_eq_true rfl))
  have e_v2625 : (v2625 = 1 ↔ sv v2611 < sv v2622) := e_plt h_v2611 h_v2622 (of_decide_eq_true rfl)
  have h_v2626 : R 1 0 4611686018427387894 4611686018695823364 v2626 v2626 := (r_psel hl h_v2625 h_v2622 h_v2611 (of_decide_eq_true rfl))
  have e_v2626 : v2626 = if v2625 = 1 then v2622 else v2611 := e_psel h_v2625 h_v2622 h_v2611 (of_decide_eq_true rfl)
  have h_v2627 : R 1 0 0 1 v2627 v2627 := (r_plt hl h_v967 h_v2532 (of_decide_eq_true rfl))
  have e_v2627 : (v2627 = 1 ↔ sv v967 < sv v2532) := e_plt h_v967 h_v2532 (of_decide_eq_true rfl)
  have h_v2628 : R 1 0 0 1 v2628 v2628 := (r_sub hl (r_O hl) h_v2627 (of_decide_eq_true rfl))
  have e_v2628 : (v2628 = 1 ↔ ¬v2627 = 1) := e_not h_v2627 (of_decide_eq_true rfl)
  have h_v2629 : R 1 0 0 1 v2629 v2629 := (r_plt hl h_v2526 h_v967 (of_decide_eq_true rfl))
  have e_v2629 : (v2629 = 1 ↔ sv v2526 < sv v967) := e_plt h_v2526 h_v967 (of_decide_eq_true rfl)
  have h_v2630 : R 1 0 0 1 v2630 v2630 := (r_sub hl (r_O hl) h_v2629 (of_decide_eq_true rfl))
  clear h_v967 h_v2526 h_v2532 h_v2606 h_v2611 h_v2614 h_v2617 pb_v2614_v2345 h_v2618 h_v2619 h_v2620 h_v2621 h_v2622 h_v2623 h_v2625 h_v2627
  have e_v2630 : (v2630 = 1 ↔ ¬v2629 = 1) := e_not h_v2629 (of_decide_eq_true rfl)
  have h_v2631 : R 1 0 0 1 v2631 v2631 := (r_land hl h_v2628 h_v2630 (of_decide_eq_true rfl))
  have e_v2631 : (v2631 = 1 ↔ v2628 = 1 ∧ v2630 = 1) := e_land h_v2628 h_v2630 (of_decide_eq_true rfl)
  have h_v2632 : R 1 0 4611686018427387894 4611686018695823364 v2632 v2632 := (r_psel hl h_v2631 h_v33 h_v2626 (of_decide_eq_true rfl))
  have e_v2632 : v2632 = if v2631 = 1 then v33 else v2626 := e_psel h_v2631 h_v33 h_v2626 (of_decide_eq_true rfl)
  have h_v2633 : R 1 0 0 1 v2633 v2633 := (r_plt hl h_v2592 h_v61 (of_decide_eq_true rfl))
  have e_v2633 : (v2633 = 1 ↔ sv v2592 < sv v61) := e_plt h_v2592 h_v61 (of_decide_eq_true rfl)
  have h_v2634 : R 1 0 0 1 v2634 v2634 := (r_sub hl (r_O hl) h_v2633 (of_decide_eq_true rfl))
  have e_v2634 : (v2634 = 1 ↔ ¬v2633 = 1) := e_not h_v2633 (of_decide_eq_true rfl)
  have h_v2635 : R 1 0 0 1 v2635 v2635 := (r_plt hl h_v61 h_v2600 (of_decide_eq_true rfl))
  have e_v2635 : (v2635 = 1 ↔ sv v61 < sv v2600) := e_plt h_v61 h_v2600 (of_decide_eq_true rfl)
  have h_v2636 : R 1 0 0 1 v2636 v2636 := (r_sub hl (r_O hl) h_v2635 (of_decide_eq_true rfl))
  have e_v2636 : (v2636 = 1 ↔ ¬v2635 = 1) := e_not h_v2635 (of_decide_eq_true rfl)
  have h_v2637 : R 1 0 0 1 v2637 v2637 := (r_land hl h_v2633 h_v2636 (of_decide_eq_true rfl))
  have e_v2637 : (v2637 = 1 ↔ v2633 = 1 ∧ v2636 = 1) := e_land h_v2633 h_v2636 (of_decide_eq_true rfl)
  have h_v2638 : R 1 0 0 1 v2638 v2638 := (r_land hl h_v2633 h_v2635 (of_decide_eq_true rfl))
  have e_v2638 : (v2638 = 1 ↔ v2633 = 1 ∧ v2635 = 1) := e_land h_v2633 h_v2635 (of_decide_eq_true rfl)
  have h_v2639 : R 1 0 0 1 v2639 v2639 := (r_plt hl h_v2624 h_v61 (of_decide_eq_true rfl))
  have e_v2639 : (v2639 = 1 ↔ sv v2624 < sv v61) := e_plt h_v2624 h_v61 (of_decide_eq_true rfl)
  have h_v2640 : R 1 0 0 1 v2640 v2640 := (r_sub hl (r_O hl) h_v2639 (of_decide_eq_true rfl))
  have e_v2640 : (v2640 = 1 ↔ ¬v2639 = 1) := e_not h_v2639 (of_decide_eq_true rfl)
  have h_v2641 : R 1 0 0 1 v2641 v2641 := (r_plt hl h_v61 h_v2632 (of_decide_eq_true rfl))
  have e_v2641 : (v2641 = 1 ↔ sv v61 < sv v2632) := e_plt h_v61 h_v2632 (of_decide_eq_true rfl)
  have h_v2642 : R 1 0 0 1 v2642 v2642 := (r_sub hl (r_O hl) h_v2641 (of_decide_eq_true rfl))
  have e_v2642 : (v2642 = 1 ↔ ¬v2641 = 1) := e_not h_v2641 (of_decide_eq_true rfl)
  clear h_v33 h_v2626 h_v2628 h_v2629 h_v2630 h_v2631 h_v2633 h_v2635 h_v2636
  have h_v2643 : R 1 0 0 1 v2643 v2643 := (r_land hl h_v2639 h_v2642 (of_decide_eq_true rfl))
  have e_v2643 : (v2643 = 1 ↔ v2639 = 1 ∧ v2642 = 1) := e_land h_v2639 h_v2642 (of_decide_eq_true rfl)
  have h_v2644 : R 1 0 0 1 v2644 v2644 := (r_land hl h_v2639 h_v2641 (of_decide_eq_true rfl))
  have e_v2644 : (v2644 = 1 ↔ v2639 = 1 ∧ v2641 = 1) := e_land h_v2639 h_v2641 (of_decide_eq_true rfl)
  have h_v2645 : R 1 0 0 1 v2645 v2645 := (r_land hl h_v2638 h_v2644 (of_decide_eq_true rfl))
  have e_v2645 : (v2645 = 1 ↔ v2638 = 1 ∧ v2644 = 1) := e_land h_v2638 h_v2644 (of_decide_eq_true rfl)
  have h_v2646 : R 1 0 0 1 v2646 v2646 := (r_sub hl (r_O hl) h_v2645 (of_decide_eq_true rfl))
  have e_v2646 : (v2646 = 1 ↔ ¬v2645 = 1) := e_not h_v2645 (of_decide_eq_true rfl)
  have h_v2647 : R 1 0 0 1 v2647 v2647 := (r_lor hl h_v2287 h_v2646 (of_decide_eq_true rfl))
  have e_v2647 : (v2647 = 1 ↔ v2287 = 1 ∨ v2646 = 1) := e_lor h_v2287 h_v2646 (of_decide_eq_true rfl)
  have h_v2648 : R 1 0 0 1 v2648 v2648 := (r_land hl h_v2634 h_v2644 (of_decide_eq_true rfl))
  have e_v2648 : (v2648 = 1 ↔ v2634 = 1 ∧ v2644 = 1) := e_land h_v2634 h_v2644 (of_decide_eq_true rfl)
  have h_v2649 : R 1 0 0 1 v2649 v2649 := (r_lor hl h_v2643 h_v2648 (of_decide_eq_true rfl))
  have e_v2649 : (v2649 = 1 ↔ v2643 = 1 ∨ v2648 = 1) := e_lor h_v2643 h_v2648 (of_decide_eq_true rfl)
  have h_v2650 : R 1 0 4611686018427387894 4611686018695823364 v2650 v2650 := (r_psel hl h_v2649 h_v2600 h_v2592 (of_decide_eq_true rfl))
  have e_v2650 : v2650 = if v2649 = 1 then v2600 else v2592 := e_psel h_v2649 h_v2600 h_v2592 (of_decide_eq_true rfl)
  have h_v2651 : R 1 0 0 1 v2651 v2651 := (r_land hl h_v2638 h_v2640 (of_decide_eq_true rfl))
  have e_v2651 : (v2651 = 1 ↔ v2638 = 1 ∧ v2640 = 1) := e_land h_v2638 h_v2640 (of_decide_eq_true rfl)
  have h_v2652 : R 1 0 0 1 v2652 v2652 := (r_lor hl h_v2637 h_v2651 (of_decide_eq_true rfl))
  have e_v2652 : (v2652 = 1 ↔ v2637 = 1 ∨ v2651 = 1) := e_lor h_v2637 h_v2651 (of_decide_eq_true rfl)
  have h_v2653 : R 1 0 4611686018427387894 4611686018695823364 v2653 v2653 := (r_psel hl h_v2652 h_v2632 h_v2624 (of_decide_eq_true rfl))
  have e_v2653 : v2653 = if v2652 = 1 then v2632 else v2624 := e_psel h_v2652 h_v2632 h_v2624 (of_decide_eq_true rfl)
  have h_v2654 : R 1 0 0 1 v2654 v2654 := (r_land hl h_v2637 h_v2644 (of_decide_eq_true rfl))
  have e_v2654 : (v2654 = 1 ↔ v2637 = 1 ∧ v2644 = 1) := e_land h_v2637 h_v2644 (of_decide_eq_true rfl)
  have h_v2655 : R 1 0 0 1 v2655 v2655 := (r_lor hl h_v2643 h_v2654 (of_decide_eq_true rfl))
  clear h_v2634 h_v2639 h_v2640 h_v2641 h_v2642 h_v2644 h_v2645 h_v2646 h_v2648 h_v2649 h_v2651 h_v2652
  have e_v2655 : (v2655 = 1 ↔ v2643 = 1 ∨ v2654 = 1) := e_lor h_v2643 h_v2654 (of_decide_eq_true rfl)
  have h_v2656 : R 1 0 4611686018427387894 4611686018695823364 v2656 v2656 := (r_psel hl h_v2655 h_v2592 h_v2600 (of_decide_eq_true rfl))
  have e_v2656 : v2656 = if v2655 = 1 then v2592 else v2600 := e_psel h_v2655 h_v2592 h_v2600 (of_decide_eq_true rfl)
  have h_v2657 : R 1 0 0 1 v2657 v2657 := (r_land hl h_v2638 h_v2643 (of_decide_eq_true rfl))
  have e_v2657 : (v2657 = 1 ↔ v2638 = 1 ∧ v2643 = 1) := e_land h_v2638 h_v2643 (of_decide_eq_true rfl)
  have h_v2658 : R 1 0 0 1 v2658 v2658 := (r_lor hl h_v2637 h_v2657 (of_decide_eq_true rfl))
  have e_v2658 : (v2658 = 1 ↔ v2637 = 1 ∨ v2657 = 1) := e_lor h_v2637 h_v2657 (of_decide_eq_true rfl)
  have h_v2659 : R 1 0 4611686018427387894 4611686018695823364 v2659 v2659 := (r_psel hl h_v2658 h_v2624 h_v2632 (of_decide_eq_true rfl))
  have e_v2659 : v2659 = if v2658 = 1 then v2624 else v2632 := e_psel h_v2658 h_v2624 h_v2632 (of_decide_eq_true rfl)
  have h_v2660 : R 1 0 4611686015743033304 4683743614612799504 v2660 v2660 := (r_smx hl 29 h_v2653 h_v2650 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v2660 : sv v2660 = sv v2653 * sv v2650 := e_smx 29 h_v2653 h_v2650 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v2661 : R 1 0 4611686018427387893 4611686018695823368 v2661 v2661 := (r_srdF hl h_v2660 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl))
  have e_v2661 : sv v2661 = sv v2660 / 2 ^ 28 := e_srdF h_v2660 4611686018427387893 4611686018695823368 (of_decide_eq_true rfl)
  have h_v2662 : R 1 0 4611686015743033304 4683743614612799504 v2662 v2662 := (r_smx hl 29 h_v2659 h_v2656 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl))
  have e_v2662 : sv v2662 = sv v2659 * sv v2656 := e_smx 29 h_v2659 h_v2656 4611686015743033304 4683743614612799504 (of_decide_eq_true rfl)
  have h_v2663 : R 1 0 4611686018427387894 4611686018695823369 v2663 v2663 := (r_srdC hl h_v2662 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl))
  have e_v2663 : sv v2663 = -((-sv v2662) / 2 ^ 28) := e_srdC h_v2662 4611686018427387894 4611686018695823369 (of_decide_eq_true rfl)
  have h_v2664 : R 1 0 0 1 v2664 v2664 := (r_plt hl h_v61 h_v2661 (of_decide_eq_true rfl))
  have e_v2664 : (v2664 = 1 ↔ sv v61 < sv v2661) := e_plt h_v61 h_v2661 (of_decide_eq_true rfl)
  have h_v2666 : R 1 0 0 1 v2666 v2666 := (r_plt hl h_v2567 h_v61 (of_decide_eq_true rfl))
  have e_v2666 : (v2666 = 1 ↔ sv v2567 < sv v61) := e_plt h_v2567 h_v61 (of_decide_eq_true rfl)
  have h_v2667 : R 1 0 4611686018427387893 4611686018695823369 v2667 v2667 := (r_psel hl h_v2666 h_v2661 h_v2663 (of_decide_eq_true rfl))
  have e_v2667 : v2667 = if v2666 = 1 then v2661 else v2663 := e_psel h_v2666 h_v2661 h_v2663 (of_decide_eq_true rfl)
  have h_v2670 : R 1 0 0 1 v2670 v2670 := (r_plt hl h_v2667 h_v2567 (of_decide_eq_true rfl))
  have e_v2670 : (v2670 = 1 ↔ sv v2667 < sv v2567) := e_plt h_v2667 h_v2567 (of_decide_eq_true rfl)
  clear h_v2567 h_v2592 h_v2600 h_v2624 h_v2632 h_v2637 h_v2638 h_v2643 h_v2650 h_v2653 h_v2654 h_v2655 h_v2656 h_v2657 h_v2658 h_v2659 h_v2660 h_v2661 h_v2662 h_v2663 h_v2666 h_v2667
  have h_v2671 : R 1 0 0 1 v2671 v2671 := (r_land hl h_v2664 h_v2670 (of_decide_eq_true rfl))
  have e_v2671 : (v2671 = 1 ↔ v2664 = 1 ∧ v2670 = 1) := e_land h_v2664 h_v2670 (of_decide_eq_true rfl)
  have h_v2678 : R 1 0 0 1 v2678 v2678 := (r_lor hl h_v2507 h_v2671 (of_decide_eq_true rfl))
  have e_v2678 : (v2678 = 1 ↔ v2507 = 1 ∨ v2671 = 1) := e_lor h_v2507 h_v2671 (of_decide_eq_true rfl)
  have h_v2680 : R 1 0 4611686018427387904 4611686019501129727 v2680 v2680 := (r1_hxa hb_H4 0 (of_decide_eq_true rfl))
  have e_v2680 : sv v2680 = ((H4 / 2 ^ 0 % 2 ^ 30 : ℕ) : ℤ) := e_hxa hb_H4 0 (of_decide_eq_true rfl)
  have h_v2681 : R 1 0 0 1 v2681 v2681 := (r_plt hl h_v61 h_v2680 (of_decide_eq_true rfl))
  have e_v2681 : (v2681 = 1 ↔ sv v61 < sv v2680) := e_plt h_v61 h_v2680 (of_decide_eq_true rfl)
  have h_v2682 : R 1 0 0 1 v2682 v2682 := (r_sub hl (r_O hl) h_v2681 (of_decide_eq_true rfl))
  have e_v2682 : (v2682 = 1 ↔ ¬v2681 = 1) := e_not h_v2681 (of_decide_eq_true rfl)
  have h_t2680_1 : R 1 0 4611686018427387904 4611686018695823363 t2680.1 t2680.1 := r_sc1 hl h_v2680 (of_decide_eq_true rfl)
  have h_t2680_2 : R 1 0 4611686018158952445 4611686018695823363 t2680.2 t2680.2 := r_sc2 hl h_v2680 (of_decide_eq_true rfl)
  have e_t2680_1 : sv t2680.1 = (sc28pS (scArg v2680)).1 := e_sc1 h_v2680 (of_decide_eq_true rfl)
  have e_t2680_2 : sv t2680.2 = (sc28pS (scArg v2680)).2 := e_sc2 h_v2680 (of_decide_eq_true rfl)
  have h_v2684 : R 1 0 4611686018158952441 4611686018695823359 v2684 v2684 := (r_sub hl (r_add hl h_v28 h_t2680_2 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2684 : sv v2684 = sv v28 + sv t2680.2 := e_add h_v28 h_t2680_2 (of_decide_eq_true rfl)
  have h_v2685 : R 1 0 0 1 v2685 v2685 := (r_plt hl h_v2684 h_v95 (of_decide_eq_true rfl))
  have e_v2685 : (v2685 = 1 ↔ sv v2684 < sv v95) := e_plt h_v2684 h_v95 (of_decide_eq_true rfl)
  have h_v2686 : R 1 0 4611686018158952441 4611686018695823359 v2686 v2686 := (r_psel hl h_v2685 h_v95 h_v2684 (of_decide_eq_true rfl))
  have e_v2686 : v2686 = if v2685 = 1 then v95 else v2684 := e_psel h_v2685 h_v95 h_v2684 (of_decide_eq_true rfl)
  have h_v2687 : R 1 0 4467570782033149952 4755801223146242048 v2687 v2687 := (r_sshl hl h_v2511 4467570782033149952 4755801223146242048 (of_decide_eq_true rfl))
  have e_v2687 : sv v2687 = sv v2511 * 2 ^ 28 := e_sshl h_v2511 4467570782033149952 4755801223146242048 (of_decide_eq_true rfl)
  have h_v2688 : R 1 0 4539628420094492609 4683743614612799479 v2688 v2688 := (r_smx hl 29 h_v2686 h_v2512 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl))
  have e_v2688 : sv v2688 = sv v2686 * sv v2512 := e_smx 29 h_v2686 h_v2512 4539628420094492609 4683743614612799479 (of_decide_eq_true rfl)
  have h_v2689 : R 1 0 0 1 v2689 v2689 := (r_plt hl h_v2688 h_v2687 (of_decide_eq_true rfl))
  clear h_v28 h_v95 h_v2664 h_v2670 h_v2671 h_v2681 h_t2680_1 h_t2680_2 e_t2680_1 h_v2684 h_v2685 h_v2686
  have e_v2689 : (v2689 = 1 ↔ sv v2688 < sv v2687) := e_plt h_v2688 h_v2687 (of_decide_eq_true rfl)
  have h_v2690 : R 1 0 0 1 v2690 v2690 := (r_sub hl (r_O hl) h_v2689 (of_decide_eq_true rfl))
  have e_v2690 : (v2690 = 1 ↔ ¬v2689 = 1) := e_not h_v2689 (of_decide_eq_true rfl)
  have h_v2691 : R 1 0 0 1 v2691 v2691 := (r_plt hl h_v15 h_v2680 (of_decide_eq_true rfl))
  have e_v2691 : (v2691 = 1 ↔ sv v15 < sv v2680) := e_plt h_v15 h_v2680 (of_decide_eq_true rfl)
  have h_v2692 : R 1 0 0 1 v2692 v2692 := (r_sub hl (r_O hl) h_v2691 (of_decide_eq_true rfl))
  have e_v2692 : (v2692 = 1 ↔ ¬v2691 = 1) := e_not h_v2691 (of_decide_eq_true rfl)
  have h_v2693 : R 1 0 0 1 v2693 v2693 := (r_land hl h_v2690 h_v2692 (of_decide_eq_true rfl))
  have e_v2693 : (v2693 = 1 ↔ v2690 = 1 ∧ v2692 = 1) := e_land h_v2690 h_v2692 (of_decide_eq_true rfl)
  have h_v2694 : R 1 0 0 1 v2694 v2694 := (r_lor hl h_v2682 h_v2693 (of_decide_eq_true rfl))
  have e_v2694 : (v2694 = 1 ↔ v2682 = 1 ∨ v2693 = 1) := e_lor h_v2682 h_v2693 (of_decide_eq_true rfl)
  have h_v2695 : R 1 0 4611686018427387904 4611686019501129727 v2695 v2695 := (r_psel hl h_v2694 h_v2680 h_v61 (of_decide_eq_true rfl))
  have e_v2695 : v2695 = if v2694 = 1 then v2680 else v61 := e_psel h_v2694 h_v2680 h_v61 (of_decide_eq_true rfl)
  have h_v2709 : R 1 0 4611686018427387904 4611686019501129727 v2709 v2709 := (r_psel hl h_v2258 h_v2695 h_v61 (of_decide_eq_true rfl))
  have e_v2709 : v2709 = if v2258 = 1 then v2695 else v61 := e_psel h_v2258 h_v2695 h_v61 (of_decide_eq_true rfl)
  have h_v2711 : R 1 0 0 1 v2711 v2711 := (r_land hl h_v2258 h_v2678 (of_decide_eq_true rfl))
  have e_v2711 : (v2711 = 1 ↔ v2258 = 1 ∧ v2678 = 1) := e_land h_v2258 h_v2678 (of_decide_eq_true rfl)
  have h_v2712 : R 1 0 4611686018427387904 4611686019270702760 v2712 v2712 := (r_psel hl h_v2507 h_v15 h_v61 (of_decide_eq_true rfl))
  have e_v2712 : v2712 = if v2507 = 1 then v15 else v61 := e_psel h_v2507 h_v15 h_v61 (of_decide_eq_true rfl)
  have h_v2714 : R 1 0 4611686018427387904 4611686019501129727 v2714 v2714 := (r_psel hl h_v2711 h_v2712 h_v2709 (of_decide_eq_true rfl))
  have e_v2714 : v2714 = if v2711 = 1 then v2712 else v2709 := e_psel h_v2711 h_v2712 h_v2709 (of_decide_eq_true rfl)
  have h_v2716 : R 1 0 4611686017353646081 4611686020574871550 v2716 v2716 := (r_sub hl (r_add hl h_v255 h_v2714 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2716 : sv v2716 = sv v255 + sv v2714 := e_add h_v255 h_v2714 (of_decide_eq_true rfl)
  have h_v2718 : R 1 0 4611686016279904258 4611686021648613373 v2718 v2718 := (r_sub hl (r_add hl h_v580 h_v2716 (of_decide_eq_true rfl)) h_OFFr (of_decide_eq_true rfl))
  have e_v2718 : sv v2718 = sv v580 + sv v2716 := e_add h_v580 h_v2716 (of_decide_eq_true rfl)
  clear h_OFFr h_v15 h_v61 h_v2678 h_v2680 h_v2682 h_v2687 h_v2688 h_v2689 h_v2690 h_v2691 h_v2692 h_v2693 h_v2694 h_v2695 h_v2709 h_v2711 h_v2712 h_v2714 h_v2716
  have h_v2720 : R 1 0 0 1 v2720 v2720 := (r_plt hl h_v2718 h_v6 (of_decide_eq_true rfl))
  have e_v2720 : (v2720 = 1 ↔ sv v2718 < sv v6) := e_plt h_v2718 h_v6 (of_decide_eq_true rfl)
  have h_v2721 : R 1 0 0 1 v2721 v2721 := (r_sub hl (r_O hl) h_v2720 (of_decide_eq_true rfl))
  have e_v2721 : (v2721 = 1 ↔ ¬v2720 = 1) := e_not h_v2720 (of_decide_eq_true rfl)
  have h_v2724 : R 1 0 0 1 v2724 v2724 := (r_land hl h_v23 h_v47 (of_decide_eq_true rfl))
  have e_v2724 : (v2724 = 1 ↔ v23 = 1 ∧ v47 = 1) := e_land h_v23 h_v47 (of_decide_eq_true rfl)
  have h_v2725 : R 1 0 0 1 v2725 v2725 := (r_land hl h_v75 h_v2724 (of_decide_eq_true rfl))
  have e_v2725 : (v2725 = 1 ↔ v75 = 1 ∧ v2724 = 1) := e_land h_v75 h_v2724 (of_decide_eq_true rfl)
  have h_v2726 : R 1 0 0 1 v2726 v2726 := (r_land hl h_v92 h_v2725 (of_decide_eq_true rfl))
  have e_v2726 : (v2726 = 1 ↔ v92 = 1 ∧ v2725 = 1) := e_land h_v92 h_v2725 (of_decide_eq_true rfl)
  have h_v2727 : R 1 0 0 1 v2727 v2727 := (r_land hl h_v23 h_v2726 (of_decide_eq_true rfl))
  have e_v2727 : (v2727 = 1 ↔ v23 = 1 ∧ v2726 = 1) := e_land h_v23 h_v2726 (of_decide_eq_true rfl)
  have h_v2728 : R 1 0 0 1 v2728 v2728 := (r_land hl h_v110 h_v2727 (of_decide_eq_true rfl))
  have e_v2728 : (v2728 = 1 ↔ v110 = 1 ∧ v2727 = 1) := e_land h_v110 h_v2727 (of_decide_eq_true rfl)
  have h_v2729 : R 1 0 0 1 v2729 v2729 := (r_land hl h_v110 h_v2728 (of_decide_eq_true rfl))
  have e_v2729 : (v2729 = 1 ↔ v110 = 1 ∧ v2728 = 1) := e_land h_v110 h_v2728 (of_decide_eq_true rfl)
  have h_v2730 : R 1 0 0 1 v2730 v2730 := (r_land hl h_v147 h_v2729 (of_decide_eq_true rfl))
  have e_v2730 : (v2730 = 1 ↔ v147 = 1 ∧ v2729 = 1) := e_land h_v147 h_v2729 (of_decide_eq_true rfl)
  have h_v2731 : R 1 0 0 1 v2731 v2731 := (r_land hl h_v260 h_v2730 (of_decide_eq_true rfl))
  have e_v2731 : (v2731 = 1 ↔ v260 = 1 ∧ v2730 = 1) := e_land h_v260 h_v2730 (of_decide_eq_true rfl)
  have h_v2732 : R 1 0 0 1 v2732 v2732 := (r_land hl h_v260 h_v2731 (of_decide_eq_true rfl))
  have e_v2732 : (v2732 = 1 ↔ v260 = 1 ∧ v2731 = 1) := e_land h_v260 h_v2731 (of_decide_eq_true rfl)
  have h_v2733 : R 1 0 0 1 v2733 v2733 := (r_land hl h_v291 h_v2732 (of_decide_eq_true rfl))
  have e_v2733 : (v2733 = 1 ↔ v291 = 1 ∧ v2732 = 1) := e_land h_v291 h_v2732 (of_decide_eq_true rfl)
  have h_v2734 : R 1 0 0 1 v2734 v2734 := (r_land hl h_v23 h_v2733 (of_decide_eq_true rfl))
  clear h_v6 h_v2718 h_v2720 h_v2724 h_v2725 h_v2726 h_v2727 h_v2728 h_v2729 h_v2730 h_v2731 h_v2732
  have e_v2734 : (v2734 = 1 ↔ v23 = 1 ∧ v2733 = 1) := e_land h_v23 h_v2733 (of_decide_eq_true rfl)
  have h_v2735 : R 1 0 0 1 v2735 v2735 := (r_land hl h_v403 h_v2734 (of_decide_eq_true rfl))
  have e_v2735 : (v2735 = 1 ↔ v403 = 1 ∧ v2734 = 1) := e_land h_v403 h_v2734 (of_decide_eq_true rfl)
  have h_v2736 : R 1 0 0 1 v2736 v2736 := (r_land hl h_v424 h_v2735 (of_decide_eq_true rfl))
  have e_v2736 : (v2736 = 1 ↔ v424 = 1 ∧ v2735 = 1) := e_land h_v424 h_v2735 (of_decide_eq_true rfl)
  have h_v2737 : R 1 0 0 1 v2737 v2737 := (r_land hl h_v441 h_v2736 (of_decide_eq_true rfl))
  have e_v2737 : (v2737 = 1 ↔ v441 = 1 ∧ v2736 = 1) := e_land h_v441 h_v2736 (of_decide_eq_true rfl)
  have h_v2738 : R 1 0 0 1 v2738 v2738 := (r_land hl h_v23 h_v2737 (of_decide_eq_true rfl))
  have e_v2738 : (v2738 = 1 ↔ v23 = 1 ∧ v2737 = 1) := e_land h_v23 h_v2737 (of_decide_eq_true rfl)
  have h_v2739 : R 1 0 0 1 v2739 v2739 := (r_land hl h_v444 h_v2738 (of_decide_eq_true rfl))
  have e_v2739 : (v2739 = 1 ↔ v444 = 1 ∧ v2738 = 1) := e_land h_v444 h_v2738 (of_decide_eq_true rfl)
  have h_v2740 : R 1 0 0 1 v2740 v2740 := (r_land hl h_v444 h_v2739 (of_decide_eq_true rfl))
  have e_v2740 : (v2740 = 1 ↔ v444 = 1 ∧ v2739 = 1) := e_land h_v444 h_v2739 (of_decide_eq_true rfl)
  have h_v2741 : R 1 0 0 1 v2741 v2741 := (r_land hl h_v475 h_v2740 (of_decide_eq_true rfl))
  have e_v2741 : (v2741 = 1 ↔ v475 = 1 ∧ v2740 = 1) := e_land h_v475 h_v2740 (of_decide_eq_true rfl)
  have h_v2742 : R 1 0 0 1 v2742 v2742 := (r_land hl h_v585 h_v2741 (of_decide_eq_true rfl))
  have e_v2742 : (v2742 = 1 ↔ v585 = 1 ∧ v2741 = 1) := e_land h_v585 h_v2741 (of_decide_eq_true rfl)
  have h_v2743 : R 1 0 0 1 v2743 v2743 := (r_land hl h_v585 h_v2742 (of_decide_eq_true rfl))
  have e_v2743 : (v2743 = 1 ↔ v585 = 1 ∧ v2742 = 1) := e_land h_v585 h_v2742 (of_decide_eq_true rfl)
  have h_v2744 : R 1 0 0 1 v2744 v2744 := (r_land hl h_v616 h_v2743 (of_decide_eq_true rfl))
  have e_v2744 : (v2744 = 1 ↔ v616 = 1 ∧ v2743 = 1) := e_land h_v616 h_v2743 (of_decide_eq_true rfl)
  have h_v2745 : R 1 0 0 1 v2745 v2745 := (r_land hl h_v23 h_v2744 (of_decide_eq_true rfl))
  have e_v2745 : (v2745 = 1 ↔ v23 = 1 ∧ v2744 = 1) := e_land h_v23 h_v2744 (of_decide_eq_true rfl)
  have h_v2746 : R 1 0 0 1 v2746 v2746 := (r_land hl h_v729 h_v2745 (of_decide_eq_true rfl))
  have e_v2746 : (v2746 = 1 ↔ v729 = 1 ∧ v2745 = 1) := e_land h_v729 h_v2745 (of_decide_eq_true rfl)
  clear h_v2733 h_v2734 h_v2735 h_v2736 h_v2737 h_v2738 h_v2739 h_v2740 h_v2741 h_v2742 h_v2743 h_v2744 h_v2745
  have h_v2747 : R 1 0 0 1 v2747 v2747 := (r_land hl h_v750 h_v2746 (of_decide_eq_true rfl))
  have e_v2747 : (v2747 = 1 ↔ v750 = 1 ∧ v2746 = 1) := e_land h_v750 h_v2746 (of_decide_eq_true rfl)
  have h_v2748 : R 1 0 0 1 v2748 v2748 := (r_land hl h_v767 h_v2747 (of_decide_eq_true rfl))
  have e_v2748 : (v2748 = 1 ↔ v767 = 1 ∧ v2747 = 1) := e_land h_v767 h_v2747 (of_decide_eq_true rfl)
  have h_v2749 : R 1 0 0 1 v2749 v2749 := (r_land hl h_v824 h_v2748 (of_decide_eq_true rfl))
  have e_v2749 : (v2749 = 1 ↔ v824 = 1 ∧ v2748 = 1) := e_land h_v824 h_v2748 (of_decide_eq_true rfl)
  have h_v2750 : R 1 0 0 1 v2750 v2750 := (r_land hl h_v851 h_v2749 (of_decide_eq_true rfl))
  have e_v2750 : (v2750 = 1 ↔ v851 = 1 ∧ v2749 = 1) := e_land h_v851 h_v2749 (of_decide_eq_true rfl)
  have h_v2751 : R 1 0 0 1 v2751 v2751 := (r_land hl h_v921 h_v2750 (of_decide_eq_true rfl))
  have e_v2751 : (v2751 = 1 ↔ v921 = 1 ∧ v2750 = 1) := e_land h_v921 h_v2750 (of_decide_eq_true rfl)
  have h_v2752 : R 1 0 0 1 v2752 v2752 := (r_land hl h_v1020 h_v2751 (of_decide_eq_true rfl))
  have e_v2752 : (v2752 = 1 ↔ v1020 = 1 ∧ v2751 = 1) := e_land h_v1020 h_v2751 (of_decide_eq_true rfl)
  have h_v2753 : R 1 0 0 1 v2753 v2753 := (r_land hl h_v1088 h_v2752 (of_decide_eq_true rfl))
  have e_v2753 : (v2753 = 1 ↔ v1088 = 1 ∧ v2752 = 1) := e_land h_v1088 h_v2752 (of_decide_eq_true rfl)
  have h_v2754 : R 1 0 0 1 v2754 v2754 := (r_land hl h_v1185 h_v2753 (of_decide_eq_true rfl))
  have e_v2754 : (v2754 = 1 ↔ v1185 = 1 ∧ v2753 = 1) := e_land h_v1185 h_v2753 (of_decide_eq_true rfl)
  have h_v2755 : R 1 0 0 1 v2755 v2755 := (r_land hl h_v1252 h_v2754 (of_decide_eq_true rfl))
  have e_v2755 : (v2755 = 1 ↔ v1252 = 1 ∧ v2754 = 1) := e_land h_v1252 h_v2754 (of_decide_eq_true rfl)
  have h_v2756 : R 1 0 0 1 v2756 v2756 := (r_land hl h_v824 h_v2755 (of_decide_eq_true rfl))
  have e_v2756 : (v2756 = 1 ↔ v824 = 1 ∧ v2755 = 1) := e_land h_v824 h_v2755 (of_decide_eq_true rfl)
  have h_v2757 : R 1 0 0 1 v2757 v2757 := (r_land hl h_v1255 h_v2756 (of_decide_eq_true rfl))
  have e_v2757 : (v2757 = 1 ↔ v1255 = 1 ∧ v2756 = 1) := e_land h_v1255 h_v2756 (of_decide_eq_true rfl)
  have h_v2758 : R 1 0 0 1 v2758 v2758 := (r_land hl h_v1323 h_v2757 (of_decide_eq_true rfl))
  have e_v2758 : (v2758 = 1 ↔ v1323 = 1 ∧ v2757 = 1) := e_land h_v1323 h_v2757 (of_decide_eq_true rfl)
  have h_v2759 : R 1 0 0 1 v2759 v2759 := (r_land hl h_v1420 h_v2758 (of_decide_eq_true rfl))
  clear h_v2746 h_v2747 h_v2748 h_v2749 h_v2750 h_v2751 h_v2752 h_v2753 h_v2754 h_v2755 h_v2756 h_v2757
  have e_v2759 : (v2759 = 1 ↔ v1420 = 1 ∧ v2758 = 1) := e_land h_v1420 h_v2758 (of_decide_eq_true rfl)
  have h_v2760 : R 1 0 0 1 v2760 v2760 := (r_land hl h_v1488 h_v2759 (of_decide_eq_true rfl))
  have e_v2760 : (v2760 = 1 ↔ v1488 = 1 ∧ v2759 = 1) := e_land h_v1488 h_v2759 (of_decide_eq_true rfl)
  have h_v2761 : R 1 0 0 1 v2761 v2761 := (r_land hl h_v1585 h_v2760 (of_decide_eq_true rfl))
  have e_v2761 : (v2761 = 1 ↔ v1585 = 1 ∧ v2760 = 1) := e_land h_v1585 h_v2760 (of_decide_eq_true rfl)
  have h_v2762 : R 1 0 0 1 v2762 v2762 := (r_land hl h_v1652 h_v2761 (of_decide_eq_true rfl))
  have e_v2762 : (v2762 = 1 ↔ v1652 = 1 ∧ v2761 = 1) := e_land h_v1652 h_v2761 (of_decide_eq_true rfl)
  have h_v2763 : R 1 0 0 1 v2763 v2763 := (r_land hl h_v1661 h_v2762 (of_decide_eq_true rfl))
  have e_v2763 : (v2763 = 1 ↔ v1661 = 1 ∧ v2762 = 1) := e_land h_v1661 h_v2762 (of_decide_eq_true rfl)
  have h_v2764 : R 1 0 0 1 v2764 v2764 := (r_land hl h_v1662 h_v2763 (of_decide_eq_true rfl))
  have e_v2764 : (v2764 = 1 ↔ v1662 = 1 ∧ v2763 = 1) := e_land h_v1662 h_v2763 (of_decide_eq_true rfl)
  have h_v2765 : R 1 0 0 1 v2765 v2765 := (r_land hl h_v1665 h_v2764 (of_decide_eq_true rfl))
  have e_v2765 : (v2765 = 1 ↔ v1665 = 1 ∧ v2764 = 1) := e_land h_v1665 h_v2764 (of_decide_eq_true rfl)
  have h_v2766 : R 1 0 0 1 v2766 v2766 := (r_land hl h_v1686 h_v2765 (of_decide_eq_true rfl))
  have e_v2766 : (v2766 = 1 ↔ v1686 = 1 ∧ v2765 = 1) := e_land h_v1686 h_v2765 (of_decide_eq_true rfl)
  have h_v2767 : R 1 0 0 1 v2767 v2767 := (r_land hl h_v1686 h_v2766 (of_decide_eq_true rfl))
  have e_v2767 : (v2767 = 1 ↔ v1686 = 1 ∧ v2766 = 1) := e_land h_v1686 h_v2766 (of_decide_eq_true rfl)
  have h_v2768 : R 1 0 0 1 v2768 v2768 := (r_land hl h_v1725 h_v2767 (of_decide_eq_true rfl))
  have e_v2768 : (v2768 = 1 ↔ v1725 = 1 ∧ v2767 = 1) := e_land h_v1725 h_v2767 (of_decide_eq_true rfl)
  have h_v2769 : R 1 0 0 1 v2769 v2769 := (r_land hl h_v1738 h_v2768 (of_decide_eq_true rfl))
  have e_v2769 : (v2769 = 1 ↔ v1738 = 1 ∧ v2768 = 1) := e_land h_v1738 h_v2768 (of_decide_eq_true rfl)
  have h_v2770 : R 1 0 0 1 v2770 v2770 := (r_land hl h_v1756 h_v2769 (of_decide_eq_true rfl))
  have e_v2770 : (v2770 = 1 ↔ v1756 = 1 ∧ v2769 = 1) := e_land h_v1756 h_v2769 (of_decide_eq_true rfl)
  have h_v2771 : R 1 0 0 1 v2771 v2771 := (r_land hl h_v1757 h_v2770 (of_decide_eq_true rfl))
  have e_v2771 : (v2771 = 1 ↔ v1757 = 1 ∧ v2770 = 1) := e_land h_v1757 h_v2770 (of_decide_eq_true rfl)
  clear h_v2758 h_v2759 h_v2760 h_v2761 h_v2762 h_v2763 h_v2764 h_v2765 h_v2766 h_v2767 h_v2768 h_v2769 h_v2770
  have h_v2772 : R 1 0 0 1 v2772 v2772 := (r_land hl h_v1760 h_v2771 (of_decide_eq_true rfl))
  have e_v2772 : (v2772 = 1 ↔ v1760 = 1 ∧ v2771 = 1) := e_land h_v1760 h_v2771 (of_decide_eq_true rfl)
  have h_v2773 : R 1 0 0 1 v2773 v2773 := (r_land hl h_v1781 h_v2772 (of_decide_eq_true rfl))
  have e_v2773 : (v2773 = 1 ↔ v1781 = 1 ∧ v2772 = 1) := e_land h_v1781 h_v2772 (of_decide_eq_true rfl)
  have h_v2774 : R 1 0 0 1 v2774 v2774 := (r_land hl h_v1781 h_v2773 (of_decide_eq_true rfl))
  have e_v2774 : (v2774 = 1 ↔ v1781 = 1 ∧ v2773 = 1) := e_land h_v1781 h_v2773 (of_decide_eq_true rfl)
  have h_v2775 : R 1 0 0 1 v2775 v2775 := (r_land hl h_v1820 h_v2774 (of_decide_eq_true rfl))
  have e_v2775 : (v2775 = 1 ↔ v1820 = 1 ∧ v2774 = 1) := e_land h_v1820 h_v2774 (of_decide_eq_true rfl)
  have h_v2776 : R 1 0 0 1 v2776 v2776 := (r_land hl h_v1833 h_v2775 (of_decide_eq_true rfl))
  have e_v2776 : (v2776 = 1 ↔ v1833 = 1 ∧ v2775 = 1) := e_land h_v1833 h_v2775 (of_decide_eq_true rfl)
  have h_v2777 : R 1 0 0 1 v2777 v2777 := (r_land hl h_v23 h_v2776 (of_decide_eq_true rfl))
  have e_v2777 : (v2777 = 1 ↔ v23 = 1 ∧ v2776 = 1) := e_land h_v23 h_v2776 (of_decide_eq_true rfl)
  have h_v2778 : R 1 0 0 1 v2778 v2778 := (r_land hl h_v1871 h_v2777 (of_decide_eq_true rfl))
  have e_v2778 : (v2778 = 1 ↔ v1871 = 1 ∧ v2777 = 1) := e_land h_v1871 h_v2777 (of_decide_eq_true rfl)
  have h_v2779 : R 1 0 0 1 v2779 v2779 := (r_land hl h_v1892 h_v2778 (of_decide_eq_true rfl))
  have e_v2779 : (v2779 = 1 ↔ v1892 = 1 ∧ v2778 = 1) := e_land h_v1892 h_v2778 (of_decide_eq_true rfl)
  have h_v2780 : R 1 0 0 1 v2780 v2780 := (r_land hl h_v1909 h_v2779 (of_decide_eq_true rfl))
  have e_v2780 : (v2780 = 1 ↔ v1909 = 1 ∧ v2779 = 1) := e_land h_v1909 h_v2779 (of_decide_eq_true rfl)
  have h_v2781 : R 1 0 0 1 v2781 v2781 := (r_land hl h_v23 h_v2780 (of_decide_eq_true rfl))
  have e_v2781 : (v2781 = 1 ↔ v23 = 1 ∧ v2780 = 1) := e_land h_v23 h_v2780 (of_decide_eq_true rfl)
  have h_v2782 : R 1 0 0 1 v2782 v2782 := (r_land hl h_v110 h_v2781 (of_decide_eq_true rfl))
  have e_v2782 : (v2782 = 1 ↔ v110 = 1 ∧ v2781 = 1) := e_land h_v110 h_v2781 (of_decide_eq_true rfl)
  have h_v2783 : R 1 0 0 1 v2783 v2783 := (r_land hl h_v110 h_v2782 (of_decide_eq_true rfl))
  have e_v2783 : (v2783 = 1 ↔ v110 = 1 ∧ v2782 = 1) := e_land h_v110 h_v2782 (of_decide_eq_true rfl)
  have h_v2784 : R 1 0 0 1 v2784 v2784 := (r_land hl h_v147 h_v2783 (of_decide_eq_true rfl))
  clear h_v2771 h_v2772 h_v2773 h_v2774 h_v2775 h_v2776 h_v2777 h_v2778 h_v2779 h_v2780 h_v2781 h_v2782
  have e_v2784 : (v2784 = 1 ↔ v147 = 1 ∧ v2783 = 1) := e_land h_v147 h_v2783 (of_decide_eq_true rfl)
  have h_v2785 : R 1 0 0 1 v2785 v2785 := (r_land hl h_v1915 h_v2784 (of_decide_eq_true rfl))
  have e_v2785 : (v2785 = 1 ↔ v1915 = 1 ∧ v2784 = 1) := e_land h_v1915 h_v2784 (of_decide_eq_true rfl)
  have h_v2786 : R 1 0 0 1 v2786 v2786 := (r_land hl h_v1915 h_v2785 (of_decide_eq_true rfl))
  have e_v2786 : (v2786 = 1 ↔ v1915 = 1 ∧ v2785 = 1) := e_land h_v1915 h_v2785 (of_decide_eq_true rfl)
  have h_v2787 : R 1 0 0 1 v2787 v2787 := (r_land hl h_v1952 h_v2786 (of_decide_eq_true rfl))
  have e_v2787 : (v2787 = 1 ↔ v1952 = 1 ∧ v2786 = 1) := e_land h_v1952 h_v2786 (of_decide_eq_true rfl)
  have h_v2788 : R 1 0 0 1 v2788 v2788 := (r_land hl h_v23 h_v2787 (of_decide_eq_true rfl))
  have e_v2788 : (v2788 = 1 ↔ v23 = 1 ∧ v2787 = 1) := e_land h_v23 h_v2787 (of_decide_eq_true rfl)
  have h_v2789 : R 1 0 0 1 v2789 v2789 := (r_land hl h_v2063 h_v2788 (of_decide_eq_true rfl))
  have e_v2789 : (v2789 = 1 ↔ v2063 = 1 ∧ v2788 = 1) := e_land h_v2063 h_v2788 (of_decide_eq_true rfl)
  have h_v2790 : R 1 0 0 1 v2790 v2790 := (r_land hl h_v2084 h_v2789 (of_decide_eq_true rfl))
  have e_v2790 : (v2790 = 1 ↔ v2084 = 1 ∧ v2789 = 1) := e_land h_v2084 h_v2789 (of_decide_eq_true rfl)
  have h_v2791 : R 1 0 0 1 v2791 v2791 := (r_land hl h_v2101 h_v2790 (of_decide_eq_true rfl))
  have e_v2791 : (v2791 = 1 ↔ v2101 = 1 ∧ v2790 = 1) := e_land h_v2101 h_v2790 (of_decide_eq_true rfl)
  have h_v2792 : R 1 0 0 1 v2792 v2792 := (r_land hl h_v23 h_v2791 (of_decide_eq_true rfl))
  have e_v2792 : (v2792 = 1 ↔ v23 = 1 ∧ v2791 = 1) := e_land h_v23 h_v2791 (of_decide_eq_true rfl)
  have h_v2793 : R 1 0 0 1 v2793 v2793 := (r_land hl h_v444 h_v2792 (of_decide_eq_true rfl))
  have e_v2793 : (v2793 = 1 ↔ v444 = 1 ∧ v2792 = 1) := e_land h_v444 h_v2792 (of_decide_eq_true rfl)
  have h_v2794 : R 1 0 0 1 v2794 v2794 := (r_land hl h_v444 h_v2793 (of_decide_eq_true rfl))
  have e_v2794 : (v2794 = 1 ↔ v444 = 1 ∧ v2793 = 1) := e_land h_v444 h_v2793 (of_decide_eq_true rfl)
  have h_v2795 : R 1 0 0 1 v2795 v2795 := (r_land hl h_v475 h_v2794 (of_decide_eq_true rfl))
  have e_v2795 : (v2795 = 1 ↔ v475 = 1 ∧ v2794 = 1) := e_land h_v475 h_v2794 (of_decide_eq_true rfl)
  have h_v2796 : R 1 0 0 1 v2796 v2796 := (r_land hl h_v2107 h_v2795 (of_decide_eq_true rfl))
  have e_v2796 : (v2796 = 1 ↔ v2107 = 1 ∧ v2795 = 1) := e_land h_v2107 h_v2795 (of_decide_eq_true rfl)
  clear h_v2783 h_v2784 h_v2785 h_v2786 h_v2787 h_v2788 h_v2789 h_v2790 h_v2791 h_v2792 h_v2793 h_v2794 h_v2795
  have h_v2797 : R 1 0 0 1 v2797 v2797 := (r_land hl h_v2107 h_v2796 (of_decide_eq_true rfl))
  have e_v2797 : (v2797 = 1 ↔ v2107 = 1 ∧ v2796 = 1) := e_land h_v2107 h_v2796 (of_decide_eq_true rfl)
  have h_v2798 : R 1 0 0 1 v2798 v2798 := (r_land hl h_v2144 h_v2797 (of_decide_eq_true rfl))
  have e_v2798 : (v2798 = 1 ↔ v2144 = 1 ∧ v2797 = 1) := e_land h_v2144 h_v2797 (of_decide_eq_true rfl)
  have h_v2799 : R 1 0 0 1 v2799 v2799 := (r_land hl h_v23 h_v2798 (of_decide_eq_true rfl))
  have e_v2799 : (v2799 = 1 ↔ v23 = 1 ∧ v2798 = 1) := e_land h_v23 h_v2798 (of_decide_eq_true rfl)
  have h_v2800 : R 1 0 0 1 v2800 v2800 := (r_land hl h_v729 h_v2799 (of_decide_eq_true rfl))
  have e_v2800 : (v2800 = 1 ↔ v729 = 1 ∧ v2799 = 1) := e_land h_v729 h_v2799 (of_decide_eq_true rfl)
  have h_v2801 : R 1 0 0 1 v2801 v2801 := (r_land hl h_v750 h_v2800 (of_decide_eq_true rfl))
  have e_v2801 : (v2801 = 1 ↔ v750 = 1 ∧ v2800 = 1) := e_land h_v750 h_v2800 (of_decide_eq_true rfl)
  have h_v2802 : R 1 0 0 1 v2802 v2802 := (r_land hl h_v767 h_v2801 (of_decide_eq_true rfl))
  have e_v2802 : (v2802 = 1 ↔ v767 = 1 ∧ v2801 = 1) := e_land h_v767 h_v2801 (of_decide_eq_true rfl)
  have h_v2803 : R 1 0 0 1 v2803 v2803 := (r_land hl h_v2288 h_v2802 (of_decide_eq_true rfl))
  have e_v2803 : (v2803 = 1 ↔ v2288 = 1 ∧ v2802 = 1) := e_land h_v2288 h_v2802 (of_decide_eq_true rfl)
  have h_v2804 : R 1 0 0 1 v2804 v2804 := (r_land hl h_v2315 h_v2803 (of_decide_eq_true rfl))
  have e_v2804 : (v2804 = 1 ↔ v2315 = 1 ∧ v2803 = 1) := e_land h_v2315 h_v2803 (of_decide_eq_true rfl)
  have h_v2805 : R 1 0 0 1 v2805 v2805 := (r_land hl h_v2385 h_v2804 (of_decide_eq_true rfl))
  have e_v2805 : (v2805 = 1 ↔ v2385 = 1 ∧ v2804 = 1) := e_land h_v2385 h_v2804 (of_decide_eq_true rfl)
  have h_v2806 : R 1 0 0 1 v2806 v2806 := (r_land hl h_v2482 h_v2805 (of_decide_eq_true rfl))
  have e_v2806 : (v2806 = 1 ↔ v2482 = 1 ∧ v2805 = 1) := e_land h_v2482 h_v2805 (of_decide_eq_true rfl)
  have h_v2807 : R 1 0 0 1 v2807 v2807 := (r_land hl h_v2550 h_v2806 (of_decide_eq_true rfl))
  have e_v2807 : (v2807 = 1 ↔ v2550 = 1 ∧ v2806 = 1) := e_land h_v2550 h_v2806 (of_decide_eq_true rfl)
  have h_v2808 : R 1 0 0 1 v2808 v2808 := (r_land hl h_v2647 h_v2807 (of_decide_eq_true rfl))
  have e_v2808 : (v2808 = 1 ↔ v2647 = 1 ∧ v2807 = 1) := e_land h_v2647 h_v2807 (of_decide_eq_true rfl)
  have h_v2809 : R 1 0 0 1 v2809 v2809 := (r_land hl h_v2721 h_v2808 (of_decide_eq_true rfl))
  clear h_v2550 h_v2647 h_v2796 h_v2797 h_v2798 h_v2799 h_v2800 h_v2801 h_v2802 h_v2803 h_v2804 h_v2805 h_v2806 h_v2807 h_v2809
  have e_v2809 : (v2809 = 1 ↔ v2721 = 1 ∧ v2808 = 1) := e_land h_v2721 h_v2808 (of_decide_eq_true rfl)
  exact fun _ k => k e_v2516 e_v2517 e_v2518 e_v2519 e_v2520 e_v2521 e_v2522 e_v2523 e_v2524 e_v2525 e_v2526 e_v2527 e_v2528 e_v2529 e_v2530 e_v2531 e_v2532 e_v2533 e_v2534 e_v2535 e_v2536 e_v2538 e_v2539 e_v2540 e_v2541 e_v2542 e_v2544 e_v2545 e_v2546 e_v2547 e_v2548 e_v2549 e_v2550 e_v2557 e_v2558 e_v2559 e_v2560 e_v2561 e_v2562 e_v2565 e_v2566 e_v2567 e_v2569 e_v2570 e_v2571 e_v2572 e_v2573 e_v2574 e_v2575 e_v2576 e_v2577 e_v2578 e_v2579 e_v2580 e_v2581 e_v2582 e_v2583 e_v2584 e_v2585 e_v2586 e_v2587 e_v2588 e_v2589 e_v2590 e_v2591 e_v2592 e_v2593 e_v2594 e_v2595 e_v2596 e_v2597 e_v2598 e_v2599 e_v2600 e_v2601 e_v2602 e_v2603 e_v2604 e_v2605 e_v2606 e_v2607 e_v2608 e_v2609 e_v2610 e_v2611 e_v2612 e_v2613 e_v2614 e_v2615 e_v2616 e_v2617 e_v2618 e_v2619 e_v2620 e_v2621 e_v2622 e_v2623 e_v2624 e_v2625 e_v2626 e_v2627 e_v2628 e_v2629 e_v2630 e_v2631 e_v2632 e_v2633 e_v2634 e_v2635 e_v2636 e_v2637 e_v2638 e_v2639 e_v2640 e_v2641 e_v2642 e_v2643 e_v2644 e_v2645 e_v2646 e_v2647 e_v2648 e_v2649 e_v2650 e_v2651 e_v2652 e_v2653 e_v2654 e_v2655 e_v2656 e_v2657 e_v2658 e_v2659 e_v2660 e_v2661 e_v2662 e_v2663 e_v2664 e_v2666 e_v2667 e_v2670 e_v2671 e_v2678 e_v2680 e_v2681 e_v2682 e_t2680_2 e_v2684 e_v2685 e_v2686 e_v2687 e_v2688 e_v2689 e_v2690 e_v2691 e_v2692 e_v2693 e_v2694 e_v2695 e_v2709 e_v2711 e_v2712 e_v2714 e_v2716 e_v2718 e_v2720 e_v2721 e_v2724 e_v2725 e_v2726 e_v2727 e_v2728 e_v2729 e_v2730 e_v2731 e_v2732 e_v2733 e_v2734 e_v2735 e_v2736 e_v2737 e_v2738 e_v2739 e_v2740 e_v2741 e_v2742 e_v2743 e_v2744 e_v2745 e_v2746 e_v2747 e_v2748 e_v2749 e_v2750 e_v2751 e_v2752 e_v2753 e_v2754 e_v2755 e_v2756 e_v2757 e_v2758 e_v2759 e_v2760 e_v2761 e_v2762 e_v2763 e_v2764 e_v2765 e_v2766 e_v2767 e_v2768 e_v2769 e_v2770 e_v2771 e_v2772 e_v2773 e_v2774 e_v2775 e_v2776 e_v2777 e_v2778 e_v2779 e_v2780 e_v2781 e_v2782 e_v2783 e_v2784 e_v2785 e_v2786 e_v2787 e_v2788 e_v2789 e_v2790 e_v2791 e_v2792 e_v2793 e_v2794 e_v2795 e_v2796 e_v2797 e_v2798 e_v2799 e_v2800 e_v2801 e_v2802 e_v2803 e_v2804 e_v2805 e_v2806 e_v2807 e_v2808 e_v2809

end Tammes15.D3Trig
