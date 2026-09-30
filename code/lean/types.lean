import Tammes15.Hyps.Interfaces
import Tammes15.Draw.Iface
import Tammes15.Trigrows.Realise
import Tammes15.Fans.Realise
import Tammes15.Glue.Reconstruct
import Tammes15.Geom.T8
import Tammes15.Geom.Hexagons
import Tammes15.TwoConn.Contact
import Tammes15.FaceChain.Contact

/-! Each interface of `Draw/Iface.lean` and `Hyps/Interfaces.lean` that a part of the package proves
under the same statement has the type of that theorem: every `example` below elaborates only if the
two types agree. Run by check.sh, step 5; no output means that every check passes. -/

example : type_of% @Tammes15.tri_of_realisation := @Tammes15.tri_of_realisation_proof
example : type_of% @Tammes15.rhombus_of_realisation := @Tammes15.rhombus_of_realisation_proof
example : type_of% @Tammes15.hexDiag_of_realisation := @Tammes15.hexDiag_of_realisation_proof
example : type_of% @Tammes15.pent_of_realisation := @Tammes15.pent_of_realisation_proof
example : type_of% @Tammes15.hex_of_realisation := @Tammes15.hex_of_realisation_proof
example : type_of% @Tammes15.glue_congruent := @Tammes15.glue_congruent_proof
example : type_of% @Tammes15.wheel_of_realisation := @Tammes15.Geom.wheel_of_realisation_proof
example : type_of% @Tammes15.rattlers_in_hexagons := @Tammes15.Geom.rattlers_in_hexagons_proof
example : type_of% @Tammes15.twoconn_contact := @Tammes15.twoconn_contact_proof
example : type_of% @Tammes15.faceconvex_contact := @Tammes15.FaceChain.faceconvex_contact
