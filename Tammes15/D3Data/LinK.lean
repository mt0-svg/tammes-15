import Tammes15.D3Kernel.Kinds.LinSound
import Tammes15.D3Kernel.KLoop

namespace Tammes15.D3Data

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Tammes15.D3Kernel.Kinds Tammes15.D3Kernel.Pent
  Tammes15.D3Kernel.KForm

def fstSortedK (g : ℕ) : Bool :=
  allBelowK (fun i => Nat.ble (laneK (fstK g) i) (laneK (fstK g) (Nat.add i 1))) (Nat.sub (DK g) 1)

def tVarK (Ts q : ℕ) : ℕ := Nat.land (Nat.shiftRight Ts (Nat.mul 10 q)) 63

def tNegK (Ts q : ℕ) : ℕ := Nat.land (Nat.shiftRight Ts (Nat.add (Nat.mul 10 q) 6)) 1

def tMagK (Ts q : ℕ) : ℕ := Nat.land (Nat.shiftRight Ts (Nat.add (Nat.mul 10 q) 7)) 7

def tIsK (Ts q ng mg : ℕ) : Bool := Nat.beq (tNegK Ts q) ng && Nat.beq (tMagK Ts q) mg

def eNtK (E : ℕ) : ℕ := Nat.land E 7

def eCcK (E : ℕ) : ℕ := Nat.land (Nat.shiftRight E 3) 3

def eTsK (E : ℕ) : ℕ := Nat.shiftRight E 8

def eFamK (E : ℕ) : ℕ := Nat.land (Nat.shiftRight E 64) 7

def eXK (E : ℕ) : ℕ := Nat.land (Nat.shiftRight E 67) 255

def eOK (E : ℕ) : ℕ := Nat.land (Nat.shiftRight E 75) 255

def eEK (E : ℕ) : ℕ := Nat.land (Nat.shiftRight E 83) 255

def eTauK (E i : ℕ) : ℕ := Nat.land (Nat.shiftRight E (Nat.add 91 (Nat.mul 3 i))) 7

def dvOKK (g w i : ℕ) : Bool :=
  Nat.blt w (nvK g) && Nat.blt i (DK g) &&
    (Nat.beq (meanK g w) (Nat.add 2 i) ||
      (Nat.beq (meanK g w) 0 && Nat.beq (periodK (faceK g) i) 3) ||
      (Nat.beq (meanK g w) (Nat.add 2 (iterK (faceK g) i 2)) && Nat.beq (periodK (faceK g) i) 4))

def aOKK (g w : ℕ) : Bool := Nat.blt w (nvK g) && Nat.beq (meanK g w) 0

def vertOKK (g E ng : ℕ) : Bool :=
  let v := eXK E
  let o := eOK E
  let e := eEK E
  let Ts := eTsK E
  let nt := eNtK E
  Nat.ble nt 5 && Nat.blt o e && Nat.ble e (DK g) && Nat.ble e (Nat.add o 5) &&
    (Nat.beq o 0 || Nat.blt (laneK (fstK g) (Nat.sub o 1)) v) && (Nat.beq e (DK g) || Nat.blt v (laneK (fstK g) e)) &&
    allBelowK (fun i => Nat.beq (laneK (fstK g) (Nat.add o i)) v && Nat.blt (eTauK E i) nt &&
      dvOKK g (tVarK Ts (eTauK E i)) (Nat.add o i) && Nat.beq (tNegK Ts (eTauK E i)) ng) (Nat.sub e o) &&
    allBelowK (fun q => Nat.blt (tVarK Ts q) (nvK g) &&
      Nat.beq (tMagK Ts q) (countBelowK (fun i => Nat.beq (eTauK E i) q) (Nat.sub e o))) nt

def entOKK (g E : ℕ) : Bool :=
  let i := eXK E
  let Ts := eTsK E
  let f := eFamK E
  @Bool.rec (fun _ => Bool)
    (@Bool.rec (fun _ => Bool)
      (@Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool)
          (@Bool.rec (fun _ => Bool)
            (Nat.beq f 5 && Nat.beq (eCcK E) 2 && vertOKK g E 1)
            (Nat.beq (eCcK E) 1 && vertOKK g E 0) (Nat.beq f 4))
          (Nat.beq (eNtK E) 2 && Nat.beq (eCcK E) 3 && Nat.beq (periodK (faceK g) i) 4 &&
            tIsK Ts 0 0 1 && dvOKK g (tVarK Ts 0) i && tIsK Ts 1 0 1 && dvOKK g (tVarK Ts 1) (laneK (faceK g) i))
          (Nat.beq f 3))
        (Nat.beq (eNtK E) 3 && Nat.beq (eCcK E) 0 && Nat.beq (periodK (faceK g) i) 4 &&
          tIsK Ts 0 0 3 && aOKK g (tVarK Ts 0) && tIsK Ts 1 1 1 && dvOKK g (tVarK Ts 1) i &&
          tIsK Ts 2 1 1 && dvOKK g (tVarK Ts 2) (laneK (faceK g) i))
        (Nat.beq f 2))
      (Nat.beq (eNtK E) 2 && Nat.beq (eCcK E) 0 && Nat.beq (periodK (faceK g) i) 4 &&
        tIsK Ts 0 0 1 && dvOKK g (tVarK Ts 0) i && tIsK Ts 1 1 2 && aOKK g (tVarK Ts 1))
      (Nat.beq f 1))
    (Nat.beq (eNtK E) 2 && Nat.beq (eCcK E) 0 &&
      tIsK Ts 0 0 1 && aOKK g (tVarK Ts 0) && tIsK Ts 1 1 1 && dvOKK g (tVarK Ts 1) i)
    (Nat.beq f 0)

theorem tVarK_eq (Ts q : ℕ) : tVarK Ts q = tVar Ts q := land_shiftRight Ts (10 * q) 6
theorem tNegK_eq (Ts q : ℕ) : tNegK Ts q = tNeg Ts q := land_shiftRight Ts (10 * q + 6) 1
theorem tMagK_eq (Ts q : ℕ) : tMagK Ts q = tMag Ts q := land_shiftRight Ts (10 * q + 7) 3
theorem eCcK_eq (E : ℕ) : eCcK E = eCc E := land_shiftRight E 3 2
theorem eFamK_eq (E : ℕ) : eFamK E = eFam E := land_shiftRight E 64 3
theorem eXK_eq (E : ℕ) : eXK E = eX E := land_shiftRight E 67 8
theorem eOK_eq (E : ℕ) : eOK E = eO E := land_shiftRight E 75 8
theorem eEK_eq (E : ℕ) : eEK E = eE E := land_shiftRight E 83 8
theorem eTauK_eq (E i : ℕ) : eTauK E i = eTau E i := land_shiftRight E (91 + 3 * i) 3

theorem eNtK_eq (E : ℕ) : eNtK E = eNt E := by
  show Nat.land E 7 = bits E 0 3
  exact land_shiftRight E 0 3

theorem eTsK_eq (E : ℕ) : eTsK E = eTs E := by
  unfold eTsK eTs
  exact Nat.shiftRight_eq_div_pow E 8

theorem allBelowK_allBelow (p : ℕ → Bool) (n : ℕ) : allBelowK p n = allBelow p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show @Bool.rec (fun _ => Bool) false (p n) (allBelowK p n) = (allBelow p n && p n)
    rw [ih]
    cases allBelow p n <;> rfl

theorem countBelowK_countBelow (p : ℕ → Bool) (n : ℕ) : countBelowK p n = countBelow p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.add (countBelowK p n) (@Bool.rec (fun _ => ℕ) 0 1 (p n)) = countBelow p n + (if p n then 1 else 0)
    rw [ih]
    cases p n <;> rfl

theorem allBelow_congrL {p q : ℕ → Bool} {n : ℕ} (h : ∀ i < n, p i = q i) : allBelow p n = allBelow q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allBelow]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem fstSortedK_eq (g : ℕ) : fstSortedK g = fstSorted (Ctx.code g) := by
  have hD : Ctx.D g < 256 := bits_lt g 0 8
  unfold fstSortedK fstSorted
  rw [allBelowK_allBelow, DK_eq]
  apply allBelow_congrL
  intro i hi
  have hi' : i < Ctx.D g - 1 := hi
  rw [show Nat.add i 1 = i + 1 from rfl, laneK_fst g i (by omega), laneK_fst g (i + 1) (by omega)]

theorem tIsK_eq (Ts q ng mg : ℕ) : tIsK Ts q ng mg = tIs Ts q ng mg := by
  unfold tIsK tIs
  rw [tNegK_eq, tMagK_eq]

theorem aOKK_eq (g w : ℕ) : aOKK g w = aOK g w := by
  unfold aOKK aOK
  rw [nvK_eq, meanK_eq]

theorem dvOKK_eq (g w i : ℕ) : dvOKK g w i = dvOK g w i := by
  unfold dvOKK dvOK
  have hD : (Ctx.code g).D = Ctx.D g := rfl
  rw [nvK_eq, DK_eq, meanK_eq, hD]
  cases h : Nat.blt i (Ctx.D g)
  · simp
  · have hi : i < 256 := by
      have := bits_lt g 0 8
      rw [Nat.blt_eq] at h
      exact lt_of_lt_of_le h (by unfold Ctx.D; omega)
    have hp : periodK (faceK g) i = (Ctx.code g).period i := periodK_eq g i hi
    have ht : iterK (faceK g) i 2 = (Ctx.code g).faceIter i 2 := iterK_eq g i 2 hi
    rw [hp, ht]
    rfl

theorem vertOKK_eq (g E ng : ℕ) : vertOKK g E ng = vertOK g E ng := by
  have hD : Ctx.D g < 256 := bits_lt g 0 8
  have hr : ∀ x < 256, laneK (fstK g) x = (Ctx.code g).fstAt x := fun x hx => laneK_fst g x hx
  have hcD : (Ctx.code g).D = Ctx.D g := rfl
  simp only [vertOKK, vertOK, eXK_eq, eOK_eq, eEK_eq, eTsK_eq, eNtK_eq, eTauK_eq, tVarK_eq, tNegK_eq, tMagK_eq,
    DK_eq, nvK_eq, allBelowK_allBelow, countBelowK_countBelow, dvOKK_eq, Nat.add_eq, Nat.sub_eq, hcD]
  cases h1 : Nat.blt (eO E) (eE E) <;> cases h2 : Nat.ble (eE E) (Ctx.D g) <;>
    simp only [Bool.and_false, Bool.false_and, Bool.and_true]
  rw [Nat.blt_eq] at h1
  rw [Nat.ble_eq] at h2
  rw [hr (eO E - 1) (by omega), hr (eE E) (by omega)]
  congr 1
  congr 1
  apply allBelow_congrL
  intro i hi
  rw [hr (eO E + i) (by omega)]

theorem entOKK_eq (g E : ℕ) : entOKK g E = entOK g E := by
  have hx : eX E < 256 := bits_lt E 67 8
  have hp : periodK (faceK g) (eX E) = (Ctx.code g).period (eX E) := periodK_eq g _ hx
  have hl : laneK (faceK g) (eX E) = (Ctx.code g).faceAt (eX E) := laneK_face g _ hx
  simp only [entOKK, entOK, eFamK_eq, eXK_eq, eTsK_eq, eNtK_eq, eCcK_eq, tVarK_eq, tIsK_eq, aOKK_eq, dvOKK_eq,
    vertOKK_eq, hp, hl]

end Tammes15.D3Data
