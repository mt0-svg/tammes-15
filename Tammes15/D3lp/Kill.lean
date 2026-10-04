import Tammes15.D3lp.Rows
import Tammes15.Hyps.Computations

open Real

namespace Tammes15.D3lp

open Tammes15

def KilledEntry (F : Set Frame) (P : PlaneGraph) : Prop :=
  ∀ k : ℕ, P.n + k = 15 → ∀ (H : HexChoice P k) (A : Assign P k),
    dlo ≤ A.d → A.d ≤ dhi → RelSys P H A →
      ∃ g : GlueData P k, g.Valid ∧ (PairFires P A (glueY H A g) ∨ LocalFires F (glueY H A g))

theorem killed_of_entries {L : Set PlaneGraph} {F : Set Frame} (h : ∀ P ∈ L, KilledEntry F P) :
    Killed L F :=
  h

def RootKilledH (P : PlaneGraph) (k : ℕ) (H : HexChoice P k) (lo hi : ℝ) : Prop :=
  ∀ A : Assign P k, lo ≤ A.d → A.d ≤ hi → ¬ RelSys P H A

def RootKilled (P : PlaneGraph) (lo hi : ℝ) : Prop :=
  ∀ (k : ℕ) (H : HexChoice P k), RootKilledH P k H lo hi

theorem RootKilled.trans {P : PlaneGraph} {a b c : ℝ} (h₁ : RootKilled P a b)
    (h₂ : RootKilled P b c) : RootKilled P a c := by
  intro k H A ha hc
  rcases le_total A.d b with hb | hb
  · exact h₁ k H A ha hb
  · exact h₂ k H A hb hc

theorem killedEntry_of_rootKilled {F : Set Frame} {P : PlaneGraph} (h : RootKilled P dlo dhi) :
    KilledEntry F P :=
  fun k _ H A h₁ h₂ hR => (h k H A h₁ h₂ hR).elim

abbrev Cert := List (ℕ × ℕ)

def buildRows (c : GCode) (p : Params) : Cert → Option (List (ℕ × Row))
  | [] => some []
  | (n, y) :: t =>
    match RowId.decode n with
    | none => none
    | some id =>
      match rowOf c p id with
      | none => none
      | some r =>
        match buildRows c p t with
        | none => none
        | some rows => some ((y, r) :: rows)

def check (B : ℕ) (c : GCode) (p : Params) (cert : Cert) : Bool :=
  match buildRows c p cert with
  | none => false
  | some rows => farkasPacked B rows

def checkE (c : GCode) (p : Params) (cert : Cert) : Bool :=
  match buildRows c p cert with
  | none => false
  | some rows => farkasCheck rows

theorem buildRows_mem {c : GCode} {p : Params} {cert : Cert} {rows : List (ℕ × Row)}
    (h : buildRows c p cert = some rows) : ∀ q ∈ rows, ∃ id, rowOf c p id = some q.2 := by
  induction cert generalizing rows with
  | nil =>
    simp [buildRows] at h
    subst h
    intro q hq
    simp at hq
  | cons q t ih =>
    rcases q with ⟨n, y⟩
    simp [buildRows] at h

    cases hdec : RowId.decode n with
    | none => simp [hdec] at h
    | some id =>
      simp [hdec] at h
      cases hrow : rowOf c p id with
      | none => simp [hrow] at h
      | some r =>
        simp [hrow] at h
        cases hbuild : buildRows c p t with
        | none => simp [hbuild] at h
        | some rows' =>
          simp [hbuild] at h

          rw [← h]

          intro q' hq'
          cases hq' with
          | head =>

            exact ⟨id, hrow⟩
          | tail _ hq'' =>

            exact ih hbuild q' hq''

theorem check_sound {P : PlaneGraph} {c : GCode} {lab : P.G.Dart ≃ Fin c.D} {lo hi : ℝ}
    {p : Params} {B : ℕ} {cert : Cert} (hm : Matches P c lab) (hp : ParamsValid lo hi p)
    (h : check B c p cert = true) : RootKilled P lo hi := by
  intro k H A h1 h2 hR
  unfold check at h
  cases h_build : buildRows c p cert with
  | none => simp [h_build] at h
  | some rows =>
    have h_farkas : farkasPacked B rows = true := by
      simpa [h_build] using h
    have h_rows_mem := Tammes15.D3lp.buildRows_mem h_build
    have hx : ∀ q ∈ rows, q.2.Holds (vars lab A) := by
      intro q hq
      rcases h_rows_mem q hq with ⟨id, hid⟩
      exact rows_of_relsys hm hp ⟨h1, h2⟩ hR id hid
    exact farkasPacked_sound B rows h_farkas (vars lab A) hx

theorem checkE_sound {P : PlaneGraph} {c : GCode} {lab : P.G.Dart ≃ Fin c.D} {lo hi : ℝ}
    {p : Params} {cert : Cert} (hm : Matches P c lab) (hp : ParamsValid lo hi p)
    (h : checkE c p cert = true) : RootKilled P lo hi := by
  unfold checkE at h
  cases hbuild : buildRows c p cert with
  | none =>
    rw [hbuild] at h
    simp at h
  | some rows =>
    rw [hbuild] at h
    have hrows : farkasCheck rows = true := by simpa [hbuild] using h
    intro k H A h1 h2 hR
    have hmem : ∀ q ∈ rows, ∃ id, rowOf c p id = some q.2 := buildRows_mem hbuild
    have hholds : ∀ q ∈ rows, q.2.Holds (vars lab A) := by
      intro q hq
      rcases hmem q hq with ⟨id, hid⟩
      exact rows_of_relsys hm hp ⟨h1, h2⟩ hR id hid
    exact farkasCheck_sound rows hrows (vars lab A) hholds

end Tammes15.D3lp
