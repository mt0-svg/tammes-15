import Tammes15.D3Kernel.Kinds.Cover
import Tammes15.D3Kernel.KLoop

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Walk Pent KForm

def nVK (c : GCode) : ℕ := @Nat.rec (fun _ => ℕ) 0 (fun i a => maxK a (Nat.add (laneK c.fst i) 1)) c.D

def vertsOKK (c : GCode) (n : ℕ) : Bool :=
  allBelowK (fun i => Nat.blt (laneK c.fst i) n) c.D && anyBelowK (fun i => Nat.beq (Nat.add (laneK c.fst i) 1) n) c.D

def canonK (c : GCode) (i : ℕ) : Bool :=
  Nat.blt i c.D && Nat.beq (iterK c.face i 6) i && allBelowK (fun j => Nat.blt i (iterK c.face i (Nat.add j 1))) 5

def canonListK (c : GCode) : List ℕ := (List.range c.D).filter (canonK c)

def hrepK (c : GCode) (i : ℕ) : ℕ :=
  minK i (minK (iterK c.face i 1) (minK (iterK c.face i 2) (minK (iterK c.face i 3)
    (minK (iterK c.face i 4) (iterK c.face i 5)))))

def repsOfK (c : GCode) (g k : ℕ) : List ℕ := (List.range k).map (fun m => hrepK c (baseK g m))

def varOKK (g box v : ℕ) : Bool :=
  let lo := bk box (Nat.shiftLeft v 1)
  let hi := bk box (Nat.add (Nat.shiftLeft v 1) 1)
  let m := meanK g v
  kgood lo && kgood hi &&
    @Bool.rec (fun _ => Bool)
      (@Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool)
          (Nat.blt (Nat.div (Nat.sub m 258) 6) (kK g) && Nat.ble (kfix lo) cDLO && Nat.ble c3DHI (kfix hi))
          (Nat.blt (Nat.sub m 2) (DK g) && Nat.ble (kfix lo) cALO &&
            (Nat.ble cPI (kfix hi) ||
              (Nat.beq (periodK (Nat.shiftRight g 64) (Nat.sub m 2)) 4 && Nat.ble c2AHI (kfix hi))))
          (Nat.blt m 258))
        (Nat.ble (kfix lo) cDLO && Nat.ble cDHI (kfix hi))
        (Nat.beq m 1))
      (Nat.ble (kfix lo) cALO && Nat.ble cAHI (kfix hi))
      (Nat.beq m 0)

def boxOKK (g box : ℕ) : Bool := allBelowK (varOKK g box) (nvCK g)

def rootOKK (c : GCode) (k g box : ℕ) : Bool :=
  Nat.beq (DK g) c.D && Nat.beq (bitsK g 64 2048) c.face && Nat.beq (bitsK g 2112 2048) c.fst &&
    Nat.beq (kK g) k && allBelowK (fun m => Nat.blt (baseK g m) c.D) k && boxOKK g box

def coverK (c : GCode) (R : List ℕ) : Bool :=
  let n := nVK c
  let k := Nat.sub 15 n
  vertsOKK c n && Nat.ble n 15 && (rootPairs R).all (fun p => rootOKK c k p.1 p.2) &&
    @Bool.rec (fun _ => Bool)
      ((List.sublistsLen k (canonListK c)).all (fun s => (rootPairs R).any (fun p => repsOfK c p.1 k == s)))
      (!(rootPairs R).isEmpty)
      (Nat.beq k 0)

theorem bool_dec {b : Bool} {p : Prop} [Decidable p] (h : b = true ↔ p) : b = decide p :=
  Bool.eq_iff_iff.mpr (h.trans decide_eq_true_iff.symm)

theorem ble_dec (a b : ℕ) : Nat.ble a b = decide (a ≤ b) :=
  bool_dec ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

theorem blt_dec (a b : ℕ) : Nat.blt a b = decide (a < b) :=
  bool_dec ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

theorem beq_dec (a b : ℕ) : Nat.beq a b = decide (a = b) :=
  bool_dec ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem rec_dec {α : Type} (p : Prop) [Decidable p] (x y : α) :
    @Bool.rec (fun _ => α) x y (decide p) = if p then y else x := by
  by_cases hp : p <;> simp [hp]

theorem iterK_code (c : GCode) (i j : ℕ) : iterK c.face i j = c.faceIter i j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show laneK c.face (iterK c.face i j) = c.faceAt (c.faceIter i j)
    rw [ih, laneK_eq]
    rfl

theorem nVK_eq (c : GCode) : nVK c = nV c := by
  unfold nVK nV
  generalize c.D = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ← ih, List.foldl_cons, List.foldl_nil]
    show maxK _ (Nat.add (laneK c.fst n) 1) = _
    rw [maxK_eq, laneK_eq]
    rfl

theorem vertsOKK_eq (c : GCode) (n : ℕ) : vertsOKK c n = vertsOK c n := by
  unfold vertsOKK vertsOK
  simp only [allBelowK_eq, anyBelowK_eq, laneK_eq, blt_dec, beq_dec, Nat.add_eq, Bool.beq_eq_decide_eq]
  rfl

theorem canonK_eq (c : GCode) (i : ℕ) : canonK c i = canon c i := by
  unfold canonK canon
  simp only [iterK_code, blt_dec, beq_dec, allBelowK_eq, Nat.add_eq, Bool.beq_eq_decide_eq]

theorem canonListK_eq (c : GCode) : canonListK c = canonList c := by
  unfold canonListK canonList
  congr
  ext i
  exact canonK_eq c i

theorem hrepK_eq (c : GCode) (i : ℕ) : hrepK c i = hrep c i := by
  unfold hrepK hrep
  simp only [minK_eq, iterK_code]

theorem repsOfK_eq (c : GCode) (g k : ℕ) : repsOfK c g k = repsOf c g k := by
  unfold repsOfK repsOf
  simp only [hrepK_eq, baseK_eq]

theorem varOKK_eq (g box v : ℕ) : varOKK g box v = varOK g box v := by
  have hs : Nat.shiftLeft v 1 = 2 * v := by
    show v <<< 1 = 2 * v
    rw [Nat.shiftLeft_eq]
    ring
  unfold varOKK varOK
  simp only [bk_eq, hs, meanK_eq, DK_eq, kK_eq, Nat.add_eq, Nat.sub_eq, blt_dec, ble_dec, beq_dec, rec_dec,
    Bool.beq_eq_decide_eq]
  split_ifs with h0 h1 h2
  · rfl
  · rfl
  · rw [periodK_eq g _ (by omega)]
  · rfl

theorem boxOKK_eq (g box : ℕ) : boxOKK g box = boxOK g box := by
  unfold boxOKK boxOK
  rw [allBelowK_eq, nvCK_eq]
  congr 1
  funext v
  exact varOKK_eq g box v

theorem rootOKK_eq (c : GCode) (k g box : ℕ) : rootOKK c k g box = rootOK c k g box := by
  unfold rootOKK rootOK
  simp only [DK_eq, bitsK_eq, kK_eq, baseK_eq, beq_dec, blt_dec, allBelowK_eq, boxOKK_eq, Bool.beq_eq_decide_eq]
  rfl

theorem choices_zero (c : GCode) (L : List (ℕ × ℕ)) :
    (List.sublistsLen 0 (canonList c)).all (fun s => L.any (fun p => repsOf c p.1 0 == s)) = !L.isEmpty := by
  simp [List.sublistsLen_zero, repsOf]
  cases L <;> simp

theorem choices_rec (c : GCode) (L : List (ℕ × ℕ)) (k : ℕ) :
    @Bool.rec (fun _ => Bool) ((List.sublistsLen k (canonList c)).all (fun s => L.any (fun p => repsOf c p.1 k == s)))
      (!L.isEmpty) (Nat.beq k 0) =
    (List.sublistsLen k (canonList c)).all (fun s => L.any (fun p => repsOf c p.1 k == s)) := by
  cases hk : Nat.beq k 0
  · rfl
  · rw [Nat.eq_of_beq_eq_true hk]
    exact (choices_zero c L).symm

theorem coverK_eq (c : GCode) (R : List ℕ) : coverK c R = cover c R := by
  unfold coverK cover
  simp only [nVK_eq, vertsOKK_eq, ble_dec, rootOKK_eq, canonListK_eq, repsOfK_eq, Nat.sub_eq]
  rw [choices_rec]

theorem coverK_sound : CoverSound coverK := by
  intro c R h hR
  rw [coverK_eq] at h
  exact cover_sound c R h hR

end Tammes15.D3Kernel.Kinds
