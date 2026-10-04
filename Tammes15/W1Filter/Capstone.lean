import Tammes15.W1Filter.Record
import Tammes15.W1Filter.Iso
import Tammes15.Attained.Final

namespace Tammes15.W1Filter

open Tammes15 Tammes15.D3lp
open scoped Classical

theorem isoRefl_refl {n : ℕ} {G : SimpleGraph (Fin n)} (R : RotSys G) : R.IsoRefl R :=
  ⟨SimpleGraph.Iso.refl, Or.inl fun e => by ext <;> rfl⟩

theorem enumComplete_union {L : Set PlaneGraph} (h : EnumCompleteW1 L) :
    EnumComplete (L ∪ {P | ¬ W1Graph P}) := by
  intro n h1 h2 G R hc hd hp
  by_cases hw : W1Graph ⟨n, G, R⟩
  · obtain ⟨P, hP, hn, hiso⟩ := h n h1 h2 G R hc hd hp hw
    exact ⟨P, Or.inl hP, hn, hiso⟩
  · exact ⟨⟨n, G, R⟩, Or.inr hw, rfl, isoRefl_refl R⟩

theorem killed_union {L : Set PlaneGraph} {F : Set Frame} (h : Killed L F) :
    Killed (L ∪ {P | ¬ W1Graph P}) F :=
  killed_of_entries fun P hP => hP.elim (fun hL => h P hL) killedEntry_of_not_w1Graph

theorem conjecture_of_enumW1_killed (L : Set PlaneGraph) (h2 : EnumCompleteW1 L)
    (h3 : Killed L {Attained.frameC1, Attained.frameC3}) : Conjecture :=
  conjecture_of_enum_killed _ (enumComplete_union h2) (killed_union h3)

theorem enumCompletePC_iff (S : Set (List ℕ)) :
    EnumCompletePC S ↔ EnumComplete {P | ∃ nbr, pcBytes P.n nbr ∈ S ∧ ListsMatch P nbr} := by
  constructor
  · intro h n h1 h2 G R hc hd hp
    obtain ⟨P, nbr, hS, hm, hn, hiso⟩ := h n h1 h2 G R hc hd hp
    exact ⟨P, ⟨nbr, hS, hm⟩, hn, hiso⟩
  · intro h n h1 h2 G R hc hd hp
    obtain ⟨P, ⟨nbr, hS, hm⟩, hn, hiso⟩ := h n h1 h2 G R hc hd hp
    exact ⟨P, nbr, hS, hm, hn, hiso⟩

theorem enumCompleteW1_of_run {S : Set (List ℕ)} {codes : Set GCode} (h1 : EnumCompletePC S)
    (h2 : RunW1 S codes) : EnumCompleteW1 (LOf codes) := by
  intro n hn1 hn2 G R hc hd hp hw
  obtain ⟨P, nbr, hS, hm, hn, hiso⟩ := h1 n hn1 hn2 G R hc hd hp
  have hwP : W1Graph P := w1Graph_of_isoRefl hiso hw
  obtain ⟨φ, -⟩ := id hiso
  have hdP : ∀ v, 3 ≤ P.G.degree v ∧ P.G.degree v ≤ 5 := by
    intro v
    have hv := hd (φ.symm v)
    have he : P.G.degree (φ (φ.symm v)) = G.degree (φ.symm v) := SimpleGraph.Iso.degree_eq φ _
    rw [φ.apply_symm_apply] at he
    rw [he]
    exact hv
  obtain ⟨b, g, fa, hrun, hb, hlab⟩ := filterRec_pcBytes hm (by omega) (by omega) []
  rw [List.append_nil] at hrun
  have hbt : b = true := hb.mpr ⟨hdP, hwP⟩
  subst hbt
  obtain ⟨lab, hmat⟩ := hlab rfl
  exact ⟨P, ⟨toGCode (gcOf g fa), h2 _ hS _ _ _ hrun, lab, hmat⟩, hn, hiso⟩

theorem conjecture_of_plantri_run_proof (S : Set (List ℕ)) (codes : Set GCode)
    (h1 : EnumCompletePC S) (h2 : RunW1 S codes)
    (h3 : Killed (LOf codes) {Attained.frameC1, Attained.frameC3}) : Conjecture :=
  conjecture_of_enumW1_killed _ (enumCompleteW1_of_run h1 h2) h3

end Tammes15.W1Filter
