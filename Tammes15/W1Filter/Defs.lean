import Tammes15.W1Filter.Core
import Tammes15.Hyps.Computations
import Tammes15.D3lp.Code
import Tammes15.D3lp.W1

namespace Tammes15.W1Filter

open Tammes15 Tammes15.D3lp

def pcBytes (n : ℕ) (nbr : Fin n → List ℕ) : List ℕ :=
  n :: (List.ofFn fun v => nbr v ++ [0]).flatten

structure ListsMatch (P : PlaneGraph) (nbr : Fin P.n → List ℕ) : Prop where
  range : ∀ v, ∀ x ∈ nbr v, 1 ≤ x ∧ x ≤ P.n
  nodup : ∀ v, (nbr v).Nodup
  adj : ∀ v w : Fin P.n, P.G.Adj v w ↔ (w : ℕ) + 1 ∈ nbr v
  rot : ∀ (e : P.G.Dart) (i : ℕ) (hi : i < (nbr e.fst).length),
    (nbr e.fst)[i] = (e.snd : ℕ) + 1 →
      (nbr e.fst)[(i + 1) % (nbr e.fst).length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) =
        ((P.R.rot e).snd : ℕ) + 1

def toBytes (l : List ℕ) : ByteArray := ⟨(l.map Nat.toUInt8).toArray⟩

def toGCode (c : GC) : GCode := ⟨c.D, c.face, c.fst⟩

open scoped Classical in

def EnumCompletePC (S : Set (List ℕ)) : Prop :=
  ∀ n : ℕ, 12 ≤ n → n ≤ 15 → ∀ (G : SimpleGraph (Fin n)) (R : RotSys G),
    KConnected G 3 → (∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5) → D2Regions.PlaneClass G R →
      ∃ P : PlaneGraph, ∃ nbr : Fin P.n → List ℕ, pcBytes P.n nbr ∈ S ∧ ListsMatch P nbr ∧
        P.n = n ∧ R.IsoRefl P.R

def RunW1 (S : Set (List ℕ)) (codes : Set GCode) : Prop :=
  ∀ r ∈ S, ∀ e g fa, filterRec (toBytes r) 0 = some (e, true, g, fa) → toGCode (gcOf g fa) ∈ codes

def LOf (codes : Set GCode) : Set PlaneGraph :=
  {P | ∃ c ∈ codes, ∃ lab : P.G.Dart ≃ Fin c.D, Matches P c lab}

open scoped Classical in

def EnumCompleteW1 (L : Set PlaneGraph) : Prop :=
  ∀ n : ℕ, 12 ≤ n → n ≤ 15 → ∀ (G : SimpleGraph (Fin n)) (R : RotSys G),
    KConnected G 3 → (∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5) → D2Regions.PlaneClass G R →
      W1Graph ⟨n, G, R⟩ → ∃ P ∈ L, P.n = n ∧ R.IsoRefl P.R

end Tammes15.W1Filter
