import Tammes15.Statement
import Tammes15.Hyps.Reduction
import Tammes15.Local41.Chain
import Tammes15.Vendor.EM8.BestPacking
import Tammes15.Attained.Final
import Tammes15.Params.Checks
import Tammes15.Nonunique.Corollary
import Tammes15.FejesToth.Triangle
import Tammes15.Vendor.EM8.SphericalTriangle
import Tammes15.PaperSteps.MainSearch
import Tammes15.PaperSteps.Optima
import Tammes15.PaperSteps.Isometric
import Tammes15.Contractors.Main
import Tammes15.D2Regions.Statement
import Tammes15.Contractors.DiffTest.Commute

/-! `#print axioms` of the main theorem, of the theorems it takes from each part (the interfaces of
`Draw/Iface.lean` and `Hyps/Interfaces.lean`), of theorems of Sections 4 and 8 of the paper, of the
eight-point theorem of the vendored library, of the bound of Fejes Tóth with 17 theorems of `FejesToth/` and one
of the vendored library behind Lemmas 8.1 and 8.2 and Proposition 8.3, of the main theorem with D1 and D4 proved
and theorems of D1 and D4 (Proposition 2.1, Lemma 4.2), of the inequalities of `Params/`, of Corollary 1.2 with
its parts, of the eight theorems of `PaperSteps/` that `config.json` names, of the main theorem, Corollary 1.2 and
D3 from the search trees the replays accept and the soundness theorems of `Contractors/` behind them (Theorem 7.10,
Proposition 5.6), of the theorems of `D2Draw/` and `D2Regions/` (Lemma 3.20), and of the 31 commutation theorems of
`Contractors/DiffTest/Commute.lean` (Section 10.4). Run by check.sh, step 4. -/

#print axioms Tammes15.reduction
#print axioms Tammes15.upperBound_of_hyps
#print axioms Tammes15.attained_of_hyp
#print axioms Tammes15.relSys_of_realisation
#print axioms Tammes15.realisation_of_structured
#print axioms Tammes15.structure_theorem
#print axioms Tammes15.structured_of_min
#print axioms Tammes15.twoconn_contact
#print axioms Tammes15.faceconvex_contact
#print axioms Tammes15.rattlers_in_hexagons
#print axioms Tammes15.twoconn
#print axioms Tammes15.vertexSum_of_realisation
#print axioms Tammes15.tri_of_realisation
#print axioms Tammes15.rhombus_of_realisation
#print axioms Tammes15.pent_of_realisation
#print axioms Tammes15.hex_of_realisation
#print axioms Tammes15.hexDiag_of_realisation
#print axioms Tammes15.wheel_of_realisation
#print axioms Tammes15.glue_congruent
#print axioms Tammes15.dlo_lt_arccos_root
#print axioms Tammes15.realisation_transport
#print axioms Tammes15.local_optimality
#print axioms Tammes15.kappaBound_orthogonal
#print axioms Tammes15.existsUnique_root
#print axioms Tammes15.conjecture_iff
#print axioms Tammes15.Vendor.EM8.SquareAntiprismVerification.eight_point_best_packing_rigidity
#print axioms Tammes15.fejesToth_bound
#print axioms Tammes15.FejesToth.sphereVertexAngle_eq_arg
#print axioms Tammes15.FejesToth.angle_sum_arg
#print axioms Tammes15.FejesToth.fejesToth_triangle
#print axioms Tammes15.FejesToth.circumcentre_identity
#print axioms Tammes15.FejesToth.tri_sq_le
#print axioms Tammes15.FejesToth.tri_poly
#print axioms Tammes15.FejesToth.tri_mul_le
#print axioms Tammes15.FejesToth.arg_le_arg_of_mul_le
#print axioms Tammes15.FejesToth.N1
#print axioms Tammes15.FejesToth.N2
#print axioms Tammes15.FejesToth.exists_saturated
#print axioms Tammes15.FejesToth.sep_card_bound
#print axioms Tammes15.FejesToth.hB_of_sat
#print axioms Tammes15.FejesToth.facetPolar_norm_lt
#print axioms Tammes15.FejesToth.facet_fan_bound
#print axioms Tammes15.FejesToth.hull_fan_count
#print axioms Tammes15.FejesToth.gram_cross
#print axioms Tammes15.Vendor.EM8.SquareAntiprismVerification.spherical_triangle_excess_positive
#print axioms Tammes15.conjecture_of_enum_killed
#print axioms Tammes15.conjecture_of_frames
#print axioms Tammes15.Attained.attained
#print axioms Tammes15.Attained.frameC1_unit
#print axioms Tammes15.Attained.frameC1_contact
#print axioms Tammes15.Attained.frameC1_sep
#print axioms Tammes15.Attained.frameC3_unit
#print axioms Tammes15.Attained.frameC3_contact
#print axioms Tammes15.Attained.frameC3_sep
#print axioms Tammes15.Attained.uR_spec
#print axioms Tammes15.Attained.bR_spec
#print axioms Tammes15.Attained.nm_0
#print axioms Tammes15.Attained.ct_0_1
#print axioms Tammes15.Attained.sp_8_17
#print axioms Tammes15.Kappa.kappaHyp
#print axioms Tammes15.Kappa.kappa_C1
#print axioms Tammes15.Kappa.kappa_C3
#print axioms Tammes15.Kappa.kappa_frame
#print axioms Tammes15.Kappa.nMat_spec
#print axioms Tammes15.Kappa.cert_of_check
#print axioms Tammes15.Kappa.kappa_of_cert
#print axioms Tammes15.Kappa.C1.checkN
#print axioms Tammes15.Kappa.C3.checkN
#print axioms Tammes15.Kappa.close_C1
#print axioms Tammes15.Kappa.close_C3
#print axioms Tammes15.Params.dlo_file_le
#print axioms Tammes15.Params.dhi_le_file
#print axioms Tammes15.Params.alo_file_le
#print axioms Tammes15.Params.alpha_dhi_le_file
#print axioms Tammes15.Params.smax_dhi_le_file
#print axioms Tammes15.Params.arccos_root_lt
#print axioms Tammes15.Params.fejesToth_value_lt_dhi
#print axioms Tammes15.Params.margin_onehex_P
#print axioms Tammes15.Params.pi_lt_d21
#print axioms Tammes15.alpha_dhi_lt
#print axioms Tammes15.margin_nor_closed
#print axioms Tammes15.margin_perims
#print axioms Tammes15.nonunique_of_enum_killed
#print axioms Tammes15.Nonunique.frames_not_iso
#print axioms Tammes15.Nonunique.frameC1_sep_lt
#print axioms Tammes15.Nonunique.frameC3_sep_lt
#print axioms Tammes15.PaperSteps.killed_of_progKilled
#print axioms Tammes15.conjecture_of_enum_progKilled
#print axioms Tammes15.PaperSteps.progKilled_of_progTrees
#print axioms Tammes15.conjecture_of_enum_progTrees
#print axioms Tammes15.PaperSteps.local_optimality_frame
#print axioms Tammes15.PaperSteps.optima_four
#print axioms Tammes15.PaperSteps.frames_not_isometric
#print axioms Tammes15.PaperSteps.frames_not_distance_preserving
#print axioms Tammes15.conjecture_of_enum_progTreesDom
#print axioms Tammes15.nonunique_of_enum_progTreesDom
#print axioms Tammes15.Contractors.killed_of_progTreesDom
#print axioms Tammes15.Contractors.Impl.onDom_sound
#print axioms Tammes15.Contractors.progTrees_onDom
#print axioms Tammes15.Contractors.Run.sound
#print axioms Tammes15.Contractors.Run.subset
#print axioms Tammes15.Contractors.wheelOut_sound
#print axioms Tammes15.Contractors.primStep_sound
#print axioms Tammes15.Contractors.primStep_subset
#print axioms Tammes15.Contractors.nar_sound
#print axioms Tammes15.Contractors.rowStep_sound
#print axioms Tammes15.Contractors.sysRow_holds
#print axioms Tammes15.Contractors.alphaStep_sound
#print axioms Tammes15.Contractors.alphaInvStep_sound
#print axioms Tammes15.Contractors.rhoStep_sound
#print axioms Tammes15.Contractors.rhoDStep_sound
#print axioms Tammes15.Contractors.pentStep_sound
#print axioms Tammes15.Contractors.hexStep_sound
#print axioms Tammes15.Contractors.diagFwdStep_sound
#print axioms Tammes15.Contractors.diagBwdStep_sound
#print axioms Tammes15.Contractors.wheelStep_sound
#print axioms Tammes15.Contractors.triAngleSt_mem
#print axioms Tammes15.Contractors.side_sound
#print axioms Tammes15.contactDrawn_of_structured
#print axioms Tammes15.contactDrawn_arcs
#print axioms Tammes15.D2Regions.regions_eq_facePolygons
#print axioms Tammes15.D2Regions.planeClass_of_structured
#print axioms Tammes15.Contractors.Q.nar_comm
#print axioms Tammes15.Contractors.Q.isoBase_comm
#print axioms Tammes15.Contractors.Q.isoAngle_comm
#print axioms Tammes15.Contractors.Q.triAngleSt_comm
#print axioms Tammes15.Contractors.Q.triAngle_comm
#print axioms Tammes15.Contractors.Q.triAngleC_comm
#print axioms Tammes15.Contractors.Q.alphaIv_comm
#print axioms Tammes15.Contractors.Q.alphaInvIv_comm
#print axioms Tammes15.Contractors.Q.rhoIv_comm
#print axioms Tammes15.Contractors.Q.rhombusD_comm
#print axioms Tammes15.Contractors.Q.side_comm
#print axioms Tammes15.Contractors.Q.longdiagLb_comm
#print axioms Tammes15.Contractors.Q.cornerEnds_comm
#print axioms Tammes15.Contractors.Q.decDir_comm
#print axioms Tammes15.Contractors.Q.monoBounds_comm
#print axioms Tammes15.Contractors.Q.pentEvalC_comm
#print axioms Tammes15.Contractors.Q.hexEvalC_comm
#print axioms Tammes15.Contractors.Q.cmin_comm
#print axioms Tammes15.Contractors.Q.cmax_comm
#print axioms Tammes15.Contractors.Q.rowUpd_comm
#print axioms Tammes15.Contractors.Q.rowStep_comm
#print axioms Tammes15.Contractors.Q.alphaStep_comm
#print axioms Tammes15.Contractors.Q.alphaInvStep_comm
#print axioms Tammes15.Contractors.Q.rhoStep_comm
#print axioms Tammes15.Contractors.Q.rhoDStep_comm
#print axioms Tammes15.Contractors.Q.pentStep_comm
#print axioms Tammes15.Contractors.Q.hexStep_comm
#print axioms Tammes15.Contractors.Q.diagFwdStep_comm
#print axioms Tammes15.Contractors.Q.diagBwdStep_comm
#print axioms Tammes15.Contractors.Q.wheelTurn_comm
#print axioms Tammes15.Contractors.Q.wheelStep_comm
