import Tammes15.D3Kernel.Cases

open Real

namespace Tammes15.D3Kernel

open Tammes15 Tammes15.D3lp

noncomputable def keyVal (k : ℕ) : ℝ :=
  let b : ℕ := if 2 ^ 63 ≤ k then k - 2 ^ 63 else 2 ^ 64 - 1 - k
  let e : ℕ := b / 2 ^ 52 % 2 ^ 11
  let m : ℕ := b % 2 ^ 52
  let a : ℝ := if e = 0 then (m : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)
    else if e = 2047 then 0 else ((2 ^ 52 + m : ℕ) : ℝ) * (2 : ℝ) ^ ((e : ℤ) - 1075)
  if 2 ^ 63 ≤ k then a else -a

def bits (x o w : ℕ) : ℕ := x / 2 ^ o % 2 ^ w

def bnd (box t : ℕ) : ℕ := bits box (64 * t) 64

def BoxMem (nv box : ℕ) (x : ℕ → ℝ) : Prop :=
  ∀ v < nv, keyVal (bnd box (2 * v)) ≤ x v ∧ x v ≤ keyVal (bnd box (2 * v + 1))

def Active (box : ℕ) : Prop := 2 ^ 8192 ≤ box

def setBnd (box t w : ℕ) : ℕ := box - bnd box t * 2 ^ (64 * t) + w * 2 ^ (64 * t)

def itNew (it : ℕ) : ℕ := bits it 0 64

def itBound (it : ℕ) : ℕ := bits it 64 7

def itKind (it : ℕ) : ℕ := bits it 71 4

def recBox (box it : ℕ) : ℕ := setBnd box (itBound it) (itNew it)

namespace Ctx

def D (g : ℕ) : ℕ := bits g 0 8

def k (g : ℕ) : ℕ := bits g 8 8

def nv (g : ℕ) : ℕ := bits g 16 8

def base (g m : ℕ) : ℕ := bits g (32 + 8 * m) 8

def face (g : ℕ) : ℕ := bits g 64 2048

def fst (g : ℕ) : ℕ := bits g 2112 2048

def code (g : ℕ) : GCode := ⟨D g, face g, fst g⟩

def mean (g v : ℕ) : ℕ := bits g (4160 + 16 * v) 16

noncomputable def val (g : ℕ) {P : PlaneGraph} {k : ℕ} (lab : P.G.Dart ≃ Fin (D g)) (A : Assign P k)
    (v : ℕ) : ℝ :=
  if mean g v = 0 then alpha A.d
  else if mean g v = 1 then A.d
  else if h : mean g v < 258 ∧ mean g v - 2 < D g then A.corner (lab.symm ⟨mean g v - 2, h.2⟩)
  else if h : (mean g v - 258) / 6 < k then
    A.r ⟨(mean g v - 258) / 6, h⟩ ⟨(mean g v - 258) % 6, Nat.mod_lt _ (by norm_num)⟩
  else 0

end Ctx

structure Sol (g : ℕ) where
  P : PlaneGraph
  lab : P.G.Dart ≃ Fin (Ctx.D g)
  hm : Matches P (Ctx.code g) lab
  H : HexChoice P (Ctx.k g)
  hH : ∀ m : Fin (Ctx.k g), ((lab (H.base m) : Fin (Ctx.D g)) : ℕ) = Ctx.base g m
  A : Assign P (Ctx.k g)
  hd : dlo ≤ A.d ∧ A.d ≤ dhi
  hR : RelSys P H A

namespace Sol

variable {g : ℕ}

noncomputable def x (s : Sol g) : ℕ → ℝ := Ctx.val g s.lab s.A

def Fires (s : Sol g) : Prop :=
  ∃ gd : GlueData s.P (Ctx.k g), gd.Valid ∧
    (PairFires s.P s.A (PaperSteps.progGlueY s.H s.A gd) ∨
      PaperSteps.TieFires (PaperSteps.progGlueY s.H s.A gd))

end Sol

def TreeKilled (g box : ℕ) : Prop :=
  ∀ s : Sol g, BoxMem (Ctx.nv g) box s.x → s.Fires

def RecOK (g box it : ℕ) : Prop :=
  ∀ s : Sol g, BoxMem (Ctx.nv g) box s.x → BoxMem (Ctx.nv g) (recBox box it) s.x

def KillOK (g box : ℕ) : Prop := TreeKilled g box

inductive Ev
  | record (g box it : ℕ)
  | kill (g box it : ℕ)

def Ev.it : Ev → ℕ
  | .record _ _ it => it
  | .kill _ _ it => it

def Ev.OK : Ev → Prop
  | .record g box it => RecOK g box it
  | .kill g box _ => KillOK g box

structure Checker where
  σ : Type
  H : Type
  init : σ
  onRec : ℕ → ℕ → ℕ → σ → σ
  onKill : ℕ → ℕ → ℕ → σ → σ
  fin : σ → H → Bool
  frc : σ → (σ → List ℕ) → List ℕ
  frc_eq : ∀ s k, frc s k = k s

namespace Checker

def step (Q : Checker) : Ev → Q.σ → Q.σ
  | .record g b it, s => Q.onRec g b it s
  | .kill g b it, s => Q.onKill g b it s

def run (Q : Checker) (tr : List Ev) : Q.σ :=
  tr.foldl (fun s e => Q.step e s) Q.init

def Sound (Q : Checker) (adm : ℕ → Prop) : Prop :=
  ∀ (tr : List Ev) (h : Q.H), (∀ e ∈ tr, adm e.it) → Q.fin (Q.run tr) h = true → ∀ e ∈ tr, e.OK

def pair (sel : ℕ → Bool) (Q₁ Q₂ : Checker) : Checker where
  σ := Q₁.σ × Q₂.σ
  H := Q₁.H × Q₂.H
  init := (Q₁.init, Q₂.init)
  onRec g b it s := bif sel it then (Q₁.onRec g b it s.1, s.2) else (s.1, Q₂.onRec g b it s.2)
  onKill g b it s := bif sel it then (Q₁.onKill g b it s.1, s.2) else (s.1, Q₂.onKill g b it s.2)
  fin s h := Q₁.fin s.1 h.1 && Q₂.fin s.2 h.2
  frc s k := Q₁.frc s.1 fun a => Q₂.frc s.2 fun b => k (a, b)
  frc_eq s k := by rw [Q₁.frc_eq, Q₂.frc_eq]

def none : Checker where
  σ := Bool
  H := Unit
  init := true
  onRec _ _ _ _ := false
  onKill _ _ _ _ := false
  fin s _ := s
  frc s k := k s
  frc_eq _ _ := rfl

end Checker

def kindIs (κ : ℕ) (it : ℕ) : Prop := itKind it = κ

end Tammes15.D3Kernel
