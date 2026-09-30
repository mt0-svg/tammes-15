-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/PatchChainSplicing.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8; see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.AngularArcParametrization

noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace PatchArcChain

variable {ι : Type*} {patch : ι → Set ℝ³} {a b c : ℝ³}

def trans (p : PatchArcChain patch a b) (q : PatchArcChain patch b c) :
    PatchArcChain patch a c := by
  induction q with
  | point => exact p
  | @tail y q i z hy hz ih => exact .tail ih i z hy hz

lemma trans_length (p : PatchArcChain patch a b) (q : PatchArcChain patch b c) :
    (p.trans q).length = p.length + q.length := by
  induction q with
  | point => simp [trans, length]
  | tail q i z hy hz ih =>
    change (p.trans q).length + _ = p.length + (q.length + _)
    rw [ih, add_assoc]

def IsShortest (p : PatchArcChain patch a b) : Prop :=
  ∀ q : PatchArcChain patch a b, p.length ≤ q.length

lemma shortest_prefix (p : PatchArcChain patch a b) (q : PatchArcChain patch b c)
    (hmin : (p.trans q).IsShortest) : p.IsShortest := by
  intro r
  have h := hmin (r.trans q)
  rw [trans_length, trans_length] at h
  linarith

lemma shortest_suffix (p : PatchArcChain patch a b) (q : PatchArcChain patch b c)
    (hmin : (p.trans q).IsShortest) : q.IsShortest := by
  intro r
  have h := hmin (p.trans r)
  rw [trans_length, trans_length] at h
  linarith

lemma shortest_of_same_length (p q : PatchArcChain patch a b)
    (hp : p.IsShortest) (heq : q.length = p.length) : q.IsShortest := by
  intro r
  rw [heq]
  exact hp r

/-- Shortening a subchain shortens the whole chain, with no appeal to an
unformalized path-length reparametrization theorem. -/
lemma replace_middle_length {d : ℝ³} (p : PatchArcChain patch a b)
    (q r : PatchArcChain patch b c) (s : PatchArcChain patch c d)
    (hshort : r.length < q.length) :
    ((p.trans r).trans s).length < ((p.trans q).trans s).length := by
  simp only [trans_length]
  linarith

end PatchArcChain
end Tammes15.Vendor.EM8.SquareAntiprismVerification
