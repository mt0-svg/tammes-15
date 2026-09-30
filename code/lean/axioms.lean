import Tammes15.Statement
import Tammes15.Hyps.Reduction
import Tammes15.Local41.Chain
import Tammes15.Vendor.EM8.BestPacking

/-! `#print axioms` of the main theorem, of the theorems it takes from each part (the interfaces of
`Draw/Iface.lean` and `Hyps/Interfaces.lean`), of theorems of Sections 4 and 8 of the paper, of the
eight-point theorem of the vendored library, and of the bound of Fejes Tóth with the 16 theorems of `FejesToth/`
that Section 8.4 of the paper names. Run by check.sh, step 4. -/

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
