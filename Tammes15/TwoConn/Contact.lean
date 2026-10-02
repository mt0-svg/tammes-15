import Tammes15.TwoConn.Main

/-!
# Corollary twoconn for a contact graph

The interface `twoconn_contact` of the drawing layer (Draw/Iface.lean), from the theorem
`twoconn` (paper, Section 3, Corollary twoconn) and Lemma A (`contact_exposed`):
the contact pairs of a spherical code are exposed pairs of its points. The statement is that of
`twoconn_contact` word for word; the interface file imports this module and proves its statement
by `twoconn_contact_proof`, so elaboration checks that the two agree.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- `twoconn_contact` of Draw/Iface.lean, proved. -/
theorem twoconn_contact_proof [Nonempty V] [DecidableRel G.Adj] (x : V → E3)
    (hx : ∀ v, ‖x v‖ = 1)
    (c : ℝ) (hc : c < 1) (hsep : ∀ a b, a ≠ b → ⟪x a, x b⟫ ≤ c)
    (hG : ∀ a b, G.Adj a b → ⟪x a, x b⟫ = c) (hne : ∀ v, ∃ w, G.Adj v w)
    (R : RotSys G) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π) :
    G.Connected ∧ KConnected G 2 ∧ R.Spherical ∧
      (∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e) ∧
      ∀ e : G.Dart, ∀ m n : ℕ, m < n → n < Function.minimalPeriod R.face e →
        ((R.face ^ m) e).fst ≠ ((R.face ^ n) e).fst := by
  have hinj : Function.Injective x := by
    intro a b hab
    by_contra hne'
    have h1 := hsep a b hne'
    rw [hab, real_inner_self_eq_norm_sq, hx b] at h1
    norm_num at h1
    linarith
  exact twoconn x hx hinj
    (fun a b h => contact_exposed x hx c hc hsep (G.ne_of_adj h) (hG a b h)) hne R hR hcorner

end Tammes15
