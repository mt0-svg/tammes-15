import Tammes15.Hyps.Case
import Tammes15.Draw.Angular

/-!
# Row (4) for a realisation

The corners of a realisation (Definition 5.1) at a vertex sum to `2π`: a realisation has distinct
neighbour directions (edges of length `d`, distinct points at distance at least `d`), its rotation
system is angular, and every vertex of a graph of the class has degree at least 3, so the angle
sum `corner_sum` applies. `vertexSum_realisation` is the statement of the interface
`vertexSum_of_realisation` of `Tammes15.Hyps.Interfaces`, without its unused range hypothesis.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

theorem exists_two_adj_of_two_le_degree {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (v : V) (h : 2 ≤ G.degree v) :
    ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  have h_one_lt_degree : 1 < G.degree v := by
    omega
  have h_card : 1 < (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree G v]
    exact h_one_lt_degree
  rcases (Finset.one_lt_card.mp h_card) with ⟨a, ha, b, hb, h_ne⟩
  refine ⟨a, b, h_ne, ?_, ?_⟩
  · rwa [SimpleGraph.mem_neighborFinset] at ha
  · rwa [SimpleGraph.mem_neighborFinset] at hb

/-- Row (4): the corners of a realisation at a vertex sum to `2π`. -/
theorem vertexSum_realisation {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ}
    {x : Pts P k → E3} (hP : InClass P) (hx : Realisation P H d x) (v : Fin P.n) :
    ∑ e ∈ Finset.univ.filter (fun e : P.G.Dart => e.fst = v), (assignOf P H d x).corner e =
      2 * π := by
  have hdpi : 0 < d ∧ d < π := ⟨hx.d_mem.1, by linarith [Real.pi_pos, hx.d_mem.2]⟩
  have hD : DistinctDirs P.G (fun v => x (.inl v)) :=
    distinctDirs_of_sep hdpi (fun v => x (.inl v)) (fun v => hx.unit _)
      (fun a b hab => hx.sep _ _ (fun h => hab (Sum.inl_injective h))) (fun a b h => hx.edge a b h)
  obtain ⟨a, b, hab, ha, hb⟩ :=
    exists_two_adj_of_two_le_degree v (le_trans (by norm_num) (hP.2.1 v).1)
  rw [← corner_sum (fun v => x (.inl v)) (fun v => hx.unit _) hD P.R hx.angular v
    ⟨a, b, hab, ha, hb⟩]
  refine Finset.sum_congr rfl fun e he => ?_
  have hev : e.fst = v := (Finset.mem_filter.mp he).2
  show ocorner (x (.inl e.fst)) _ _ = _
  rw [hev]

end Tammes15
