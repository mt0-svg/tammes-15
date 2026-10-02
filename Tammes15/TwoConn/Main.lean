import Tammes15.TwoConn.KConn

/-!
# Corollary twoconn by the convex hull

Corollary twoconn (paper, Section 3, in the form of Section 10.7,
for corners in `(0, π)`): a finite injective family of unit vectors and a graph without isolated
vertex whose edges are exposed pairs, with an angular rotation system whose corners all lie in
`(0, π)`. Then the graph is connected and 2-connected, the rotation system is spherical, and every
face walk has length at least 3 and passes through each vertex at most once.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Corollary twoconn by the convex hull. -/
theorem twoconn [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj] (x : V → E3)
    (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hexp : ∀ a b, G.Adj a b → ExposedPair x a b)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (R : RotSys G) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart,
      0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π) :
    G.Connected ∧ KConnected G 2 ∧ R.Spherical ∧
      (∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e) ∧
      ∀ e : G.Dart, ∀ m n : ℕ, m < n → n < Function.minimalPeriod R.face e →
        ((R.face ^ m) e).fst ≠ ((R.face ^ n) e).fst := by
  classical
  have hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫ := fun e he =>
    no_closed_hemisphere G x hx hinj hne
      (fun v t ht ht0 => exists_pos_of_corner_lt_pi R x hx hR hcorner v (hne v) t ht ht0) e he
  obtain ⟨rho, hrho⟩ := exists_angular x hx (hull_distinctDirs x hx hinj hB)
  exact ⟨connected_of_regions G x rho hexp hx hinj hB hrho R hR hcorner hne,
    kconnected_two G x rho hexp hx hinj hB hrho R hR hcorner hne,
    spherical_of_regions G x rho hexp hx hinj hB hrho R hR hcorner hne,
    fun e => face_period_ge_three R x (fun e => (hcorner e).1) e,
    fun e m n hmn hn => face_tails_ne G x rho hexp hx hinj hB hrho R hR hcorner hne e m n hmn hn⟩

end Tammes15
