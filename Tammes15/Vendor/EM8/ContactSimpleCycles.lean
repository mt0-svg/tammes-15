-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/ContactSimpleCycles.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8, hand changes marked below, `Fin 8` generalized to `Fin nPts` (auto-bound); see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.CycleEdgeSeparation

set_option maxHeartbeats 1500000
noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The contact graph with all edges incident to `v` removed. -/
def contactGraphWithout (Y : Fin nPts → ℝ³) (c : ℝ) (v : Fin nPts) : SimpleGraph (Fin nPts) where
  Adj i j := ContactAdj Y c i j ∧ i ≠ v ∧ j ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.1 rfl⟩

lemma contact_walk_without_exists {Y : Fin nPts → ℝ³} {c : ℝ} {v a b : Fin nPts}
    (h : ContactReachableWithout Y c v a b) :
    Nonempty ((contactGraphWithout Y c v).Walk a b) := by
  induction h with
  | refl => exact ⟨.nil⟩
  | tail hpath hstep ih =>
    obtain ⟨p⟩ := ih
    exact ⟨p.concat hstep⟩

lemma contact_walk_without_vertex {Y : Fin nPts → ℝ³} {c : ℝ} {v a b : Fin nPts}
    (p : (contactGraphWithout Y c v).Walk a b) (ha : a ≠ v)
    (k : ℕ) (hk : k ≤ p.length) : p.getVert k ≠ v := by
  by_cases hk0 : k = 0
  · subst k
    simpa using ha
  · have hstep := p.adj_getVert_succ (i := k - 1) (by omega)
    have heq : k - 1 + 1 = k := by omega
    rw [heq] at hstep
    exact hstep.2.2

/-- A simple cyclic list of at least three actual contact vertices. -/
structure SimpleContactCycle (Y : Fin nPts → ℝ³) (c : ℝ) where
  size : ℕ
  size_pos : 0 < size
  vertex : Fin (size + 2) → Fin nPts
  injective : Function.Injective vertex
  adjacent : ∀ i, ContactAdj Y c (vertex i) (vertex (i + 1))

def cycleVertexOfPath {Y : Fin nPts → ℝ³} {c : ℝ} {v a b : Fin nPts}
    (p : (contactGraphWithout Y c v).Walk a b) (i : Fin (p.length + 2)) : Fin nPts :=
  if i.val = 0 then v else p.getVert (i.val - 1)

lemma cycleVertexOfPath_injective {Y : Fin nPts → ℝ³} {c : ℝ} {v a b : Fin nPts}
    (p : (contactGraphWithout Y c v).Walk a b) (hp : p.IsPath) (ha : a ≠ v) :
    Function.Injective (cycleVertexOfPath p) := by
  intro i j heq
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · exact Fin.ext (hi.trans hj.symm)
  · simp only [cycleVertexOfPath, hi, hj, if_true, if_false] at heq
    exact False.elim (contact_walk_without_vertex p ha (j.val - 1) (by omega) heq.symm)
  · simp only [cycleVertexOfPath, hi, hj, if_true, if_false] at heq
    exact False.elim (contact_walk_without_vertex p ha (i.val - 1) (by omega) heq)
  · simp only [cycleVertexOfPath, hi, hj, if_false] at heq
    have hij := hp.getVert_injOn (show i.val - 1 ≤ p.length by omega)
      (show j.val - 1 ≤ p.length by omega) heq
    apply Fin.ext
    omega

lemma cycleVertexOfPath_adjacent {Y : Fin nPts → ℝ³} {c : ℝ} {v a b : Fin nPts}
    (p : (contactGraphWithout Y c v).Walk a b)
    (ha : ContactAdj Y c v a) (hb : ContactAdj Y c v b) :
    ∀ i, ContactAdj Y c (cycleVertexOfPath p i) (cycleVertexOfPath p (i + 1)) := by
  intro i
  have hi : i.val < p.length + 2 := i.isLt
  have hnext : (i + 1).val = (i.val + 1) % (p.length + 2) := by
    simp [Fin.val_add]
  by_cases hi0 : i.val = 0
  · have hs : (i + 1).val = 1 := by rw [hnext, hi0]; simp
    simpa [cycleVertexOfPath, hi0, hs] using ha
  by_cases hilast : i.val = p.length + 1
  · have hs : (i + 1).val = 0 := by rw [hnext, hilast]; simp [Nat.add_assoc]
    simpa [cycleVertexOfPath, hi0, hs, hilast] using hb.symm
  · have hs : (i + 1).val = i.val + 1 := by rw [hnext, Nat.mod_eq_of_lt (by omega)]
    have hstep := (p.adj_getVert_succ (i := i.val - 1) (by omega)).1
    have heq : i.val - 1 + 1 = i.val := by omega
    rw [heq] at hstep
    simpa [cycleVertexOfPath, hi0, hs] using hstep

/-- Two-connectedness produces a simple contact cycle through any prescribed
pair of distinct neighbors, with the prescribed vertex first. -/
theorem simple_contact_cycle_through_neighbors (Y : Fin nPts → ℝ³) (c : ℝ)
    -- tammes-15 port change: the face chain takes the two-connectivity of the contacts (ContactTwoConnected) instead of c ≤ aInf, the only use it made of that bound.
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 < c) (hconn : ContactTwoConnected Y c)
    (hirr : PackingIrreducible c Y) (v a b : Fin nPts)
    (ha : ContactAdj Y c v a) (hb : ContactAdj Y c v b) (hab : a ≠ b) :
    ∃ C : SimpleContactCycle Y c,
      C.vertex 0 = v ∧ C.vertex 1 = a ∧ C.vertex (Fin.last (C.size + 1)) = b := by
  have haC := contactComponent_closed Y c v v a (contactComponent_root Y c v) ha
  have hbC := contactComponent_closed Y c v v b (contactComponent_root Y c v) hb
  -- tammes-15 port change: the two-connectivity comes from ContactTwoConnected instead of irreducible_component_two_connected.
  have hreach := hconn v ⟨a, ha⟩
    v a b haC hbC ha.1.symm hb.1.symm
  obtain ⟨p⟩ := contact_walk_without_exists hreach
  let q := p.toPath
  have hlen : 0 < q.val.length := by
    by_contra hn
    have hz : q.val.length = 0 := by omega
    have hh := q.val.getVert_length
    rw [hz, q.val.getVert_zero] at hh
    exact hab hh
  let C : SimpleContactCycle Y c :=
    ⟨q.val.length, hlen, cycleVertexOfPath q.val,
      cycleVertexOfPath_injective q.val q.property ha.1.symm,
      cycleVertexOfPath_adjacent q.val ha hb⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · simp [C, cycleVertexOfPath]
  · simp [C, cycleVertexOfPath]
  · simp [C, cycleVertexOfPath]

end Tammes15.Vendor.EM8.SquareAntiprismVerification
