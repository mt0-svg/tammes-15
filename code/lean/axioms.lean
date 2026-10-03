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

/-! `#print axioms` of the main theorem, of the theorems it takes from each part (the interfaces of
`Draw/Iface.lean` and `Hyps/Interfaces.lean`), of theorems of the written proof, of the
eight-point theorem of the vendored library, of the bound of Fejes Tóth with 17 theorems of `FejesToth/` and one
of the vendored library behind it, of the main theorem with D1 and D4 proved and theorems of D1 and D4, of the
inequalities of `Params/`, of the non-uniqueness corollary with its parts, of the eight theorems of `PaperSteps/`
that `config.json` names, of the main theorem, the corollary and D3 from the search trees the replays accept and
the soundness theorems of `Contractors/` behind them, and of the theorems of `D2Draw/` and `D2Regions/`. Run by
check.sh, step 4. -/

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
#print axioms Tammes15.Params.pi_lt_d21
#print axioms Tammes15.alpha_dhi_lt
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
