import Tammes15.D2Regions.Defs
import Tammes15.Geom.Basic

/-!
# Self-contained steps of the graph part of Lemma 4.9 of the paper


* `wedge_not_inside`: the corner wedge in algebraic form. If no neighbour direction `u` of `w`
  lies strictly inside the corner from `w b` to `w p` (`sector_no_neighbor`), no point of the arc
  from `w` to `u` lies strictly inside that corner.
* `eq_empty_of_adj_closed`: in a connected graph, a set of vertices closed under adjacency and
  missing a vertex is empty.
* `card_image_pow_range`: an orbit of a permutation has as many points as its minimal period.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.D2Regions

open Tammes15.Geom

/-- The corner wedge: no point `s w + t u` (`s, t ≥ 0`) is strictly inside the corner at `w` from
`b` to `p` when `u` is not. -/
theorem wedge_not_inside (w b p u : E3) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsec : ¬ (0 < ⟪cross w b, u⟫ ∧ 0 < ⟪cross w u, p⟫)) :
    ¬ (0 < ⟪cross w b, s • w + t • u⟫ ∧ 0 < ⟪cross p w, s • w + t • u⟫) := by
  intro h
  rcases h with ⟨hwb, hpw⟩
  have hwb_eq : ⟪cross w b, s • w + t • u⟫ = t * ⟪cross w b, u⟫ := by
    calc
      ⟪cross w b, s • w + t • u⟫ = ⟪cross w b, s • w⟫ + ⟪cross w b, t • u⟫ := by rw [inner_add_right]
      _ = s * ⟪cross w b, w⟫ + t * ⟪cross w b, u⟫ := by rw [real_inner_smul_right, real_inner_smul_right]
      _ = s * 0 + t * ⟪cross w b, u⟫ := by
        rw [show ⟪cross w b, w⟫ = 0 from by
          simp only [inner_coords, cross_coords]; simp; ring]
      _ = t * ⟪cross w b, u⟫ := by ring
  have hpw_eq : ⟪cross p w, s • w + t • u⟫ = t * ⟪cross p w, u⟫ := by
    calc
      ⟪cross p w, s • w + t • u⟫ = ⟪cross p w, s • w⟫ + ⟪cross p w, t • u⟫ := by rw [inner_add_right]
      _ = s * ⟪cross p w, w⟫ + t * ⟪cross p w, u⟫ := by rw [real_inner_smul_right, real_inner_smul_right]
      _ = s * 0 + t * ⟪cross p w, u⟫ := by
        rw [show ⟪cross p w, w⟫ = 0 from by
          simp only [inner_coords, cross_coords]; simp; ring]
      _ = t * ⟪cross p w, u⟫ := by ring
  rw [hwb_eq] at hwb
  rw [hpw_eq] at hpw
  have h_cross_eq : ⟪cross p w, u⟫ = ⟪cross w u, p⟫ := by rw [triple_cycle]
  rw [h_cross_eq] at hpw
  have ht_pos : 0 < t := by
    by_contra! hle
    have ht0 : t = 0 := by linarith
    rw [ht0] at hwb
    simp at hwb
  have hwb_u_pos : 0 < ⟪cross w b, u⟫ :=
    pos_of_mul_pos_right hwb (by linarith)
  have hwu_p_pos : 0 < ⟪cross w u, p⟫ :=
    pos_of_mul_pos_right hpw (by linarith)
  exact hsec ⟨hwb_u_pos, hwu_p_pos⟩

/-- In a connected graph, a set of vertices closed under adjacency that misses a vertex is
empty. -/
theorem eq_empty_of_adj_closed {W : Type} {H : SimpleGraph W} (hH : H.Connected) (S : Set W)
    (hS : ∀ u v, u ∈ S → H.Adj u v → v ∈ S) (a : W) (ha : a ∉ S) : S = ∅ := by
  by_contra hne
  have hne_nonempty : S.Nonempty := by
    rwa [← Set.not_nonempty_iff_eq_empty, not_not] at hne
  rcases hne_nonempty with ⟨u, hu⟩
  have hreach : H.Reachable u a := hH.preconnected u a
  rcases hreach with ⟨p⟩
  have haS : a ∈ S :=
    SimpleGraph.Walk.rec (motive := λ x y _ => x ∈ S → y ∈ S)
      (by intro x; exact id)
      (by
        intro x y z h p' ih hx
        have hy : y ∈ S := hS x y hx h
        exact ih hy)
      p hu
  exact ha haS

/-- An orbit of a permutation has as many points as its minimal period. -/
theorem card_image_pow_range {α : Type} [DecidableEq α] (F : Equiv.Perm α) (e : α) :
    ((Finset.range (Function.minimalPeriod F e)).image (fun m => (F ^ m) e)).card =
      Function.minimalPeriod F e := by
  have h_inj : Set.InjOn (fun (m : ℕ) => (F ^ m) e) (↑(Finset.range (Function.minimalPeriod F e)) : Set ℕ) := by
    rw [Finset.coe_range]
    simpa [Equiv.Perm.coe_pow] using Function.iterate_injOn_Iio_minimalPeriod (f := (F : α → α)) (x := e)
  rw [Finset.card_image_of_injOn h_inj, Finset.card_range]

end Tammes15.D2Regions
