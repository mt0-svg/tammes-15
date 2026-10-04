import Tammes15.D3Kernel.Iface

namespace Tammes15.D3Kernel.Walk

open Tammes15.D3Kernel

abbrev R := List ℕ

abbrev K (Q : Checker) := ℕ → ℕ → List ℕ → List ℕ → Q.σ → R

def recW (Q : Checker) (g it box : ℕ) (st rs : List ℕ) (q : Q.σ) (k : K Q) : R :=
  let t := Nat.land (Nat.shiftRight it (nat_lit 64)) (nat_lit 127)
  let sh := Nat.shiftLeft t (nat_lit 6)
  let cur := Nat.land box (Nat.shiftLeft (nat_lit 18446744073709551615) sh)
  let w := Nat.shiftLeft (Nat.land it (nat_lit 18446744073709551615)) sh
  @Bool.rec (fun _ => R) []
    (k g (Nat.add (Nat.sub box cur) w) st rs (Q.onRec g box it q))
    (@Bool.rec (fun _ => Bool) (Nat.ble w cur) (Nat.ble cur w)
      (Nat.beq (Nat.land t (nat_lit 1)) (nat_lit 0)))

def splitW (Q : Checker) (g it box : ℕ) (st rs : List ℕ) (q : Q.σ) (k : K Q) : R :=
  let x := Nat.land it (nat_lit 18446744073709551615)
  let slo := Nat.shiftLeft (Nat.land (Nat.shiftRight it (nat_lit 64)) (nat_lit 63)) (nat_lit 7)
  let shi := Nat.add slo (nat_lit 64)
  k g (Nat.add (Nat.sub box (Nat.land box (Nat.shiftLeft (nat_lit 18446744073709551615) shi)))
      (Nat.shiftLeft x shi))
    (Nat.add (Nat.sub box (Nat.land box (Nat.shiftLeft (nat_lit 18446744073709551615) slo)))
      (Nat.shiftLeft x slo) :: st) rs q

def killW (Q : Checker) (g it box : ℕ) (st rs : List ℕ) (q : Q.σ) (k : K Q) : R :=
  @List.rec ℕ (fun _ => R) (k g (nat_lit 0) [] rs (Q.onKill g box it q))
    (fun b st' _ => k g b st' rs (Q.onKill g box it q)) st

def rootW (Q : Checker) (box : ℕ) (st rs : List ℕ) (q : Q.σ) (k : K Q) : R :=
  @Bool.rec (fun _ => R) []
    (@List.rec ℕ (fun _ => R)
      (@List.rec ℕ (fun _ => R) []
        (fun g' rs1 _ => @List.rec ℕ (fun _ => R) []
          (fun r rs2 _ => @Bool.rec (fun _ => R) [] (k g' r [] rs2 q)
            (Nat.ble (Nat.shiftLeft (nat_lit 1) (nat_lit 8192)) r)) rs1) rs)
      (fun _ _ _ => []) st)
    (Nat.beq box (nat_lit 0))

def itemW (Q : Checker) (g it box : ℕ) (st rs : List ℕ) (q : Q.σ) (k : K Q) : R :=
  let tag := Nat.shiftRight it (nat_lit 126)
  @Bool.rec (fun _ => R)
    (@Bool.rec (fun _ => R)
      (@Bool.rec (fun _ => R) (rootW Q box st rs q k) (killW Q g it box st rs q k)
        (Nat.beq tag (nat_lit 3)))
      (splitW Q g it box st rs q k) (Nat.beq tag (nat_lit 2)))
    (recW Q g it box st rs q k) (Nat.beq tag (nat_lit 1))

def chunkW (Q : Checker) (k : K Q) (n : ℕ) : ℕ → K Q :=
  @Nat.rec (fun _ => ℕ → K Q)
    (fun _ g box st rs q => Q.frc q fun q' => k g box st rs q')
    (fun _ ih c g box st rs q =>
      itemW Q g (Nat.land c (nat_lit 340282366920938463463374607431768211455)) box st rs q
        (fun g' b s r q' => ih (Nat.shiftRight c (nat_lit 128)) g' b s r q'))
    n

def walkW (Q : Checker) (fin : K Q) (cs : List ℕ) : K Q :=
  @List.rec ℕ (fun _ => K Q) fin
    (fun c _ ih g box st rs q =>
      chunkW Q ih (Nat.land c (nat_lit 4294967295)) (Nat.shiftRight c (nat_lit 64)) g box st rs q)
    cs

def finW (Q : Checker) (h : Q.H) : K Q :=
  fun g box st rs q =>
    @Bool.rec (fun _ => R) []
      (@List.rec ℕ (fun _ => R) (g :: box :: st) (fun _ _ _ => []) rs) (Q.fin q h)

def lbeq (l₁ l₂ : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => List ℕ → Bool)
    (fun l₂ => @List.rec ℕ (fun _ => Bool) true (fun _ _ _ => false) l₂)
    (fun a _ r l₂ => @List.rec ℕ (fun _ => Bool) false
      (fun b t₂ _ => @Bool.rec (fun _ => Bool) false (r t₂) (Nat.beq a b)) l₂) l₁ l₂

def chk (Q : Checker) (d r : List ℕ) (h : Q.H) (s t : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false
    (fun g s' _ => @List.rec ℕ (fun _ => Bool) false
      (fun box st _ => @List.rec ℕ (fun _ => Bool) false
        (fun _ _ _ => lbeq (walkW Q (finW Q h) d g box st r Q.init) t) t) s') s

inductive Reach (Q : Checker) : List ℕ → List ℕ → List ℕ → Prop
  | refl (s : List ℕ) : Reach Q [] s s
  | step {s t u R : List ℕ} (d r : List ℕ) (h : Q.H) : chk Q d r h s t = true → Reach Q R t u →
      Reach Q (r ++ R) s u

def rootPairs : List ℕ → List (ℕ × ℕ)
  | g :: b :: rs => (g, b) :: rootPairs rs
  | _ => []

def Done (s : List ℕ) : Prop := ∃ g, s = [g, 0]

end Tammes15.D3Kernel.Walk
