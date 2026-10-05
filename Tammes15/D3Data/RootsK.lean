import Tammes15.D3Data.ChunkX

namespace Tammes15.D3Data

open Tammes15.D3lp Tammes15.D3Kernel Tammes15.D3Kernel.Kinds Tammes15.D3Kernel.Walk

def dropK (n : ℕ) (l : List ℕ) : List ℕ :=
  @Nat.rec (fun _ => List ℕ → List ℕ) (fun l => l)
    (fun _ ih l => @List.rec ℕ (fun _ => List ℕ) [] (fun _ t _ => ih t) l) n l

def takeK (n : ℕ) (l : List ℕ) : List ℕ :=
  @Nat.rec (fun _ => List ℕ → List ℕ) (fun _ => [])
    (fun _ ih l => @List.rec ℕ (fun _ => List ℕ) [] (fun a t _ => a :: ih t) l) n l

def lengthK (l : List ℕ) : ℕ := @List.rec ℕ (fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) l

def rootsAtK (r : List ℕ) (i n : ℕ) : List ℕ := takeK (Nat.mul 2 n) (dropK (Nat.mul 2 i) r)

theorem dropK_eq (n : ℕ) (l : List ℕ) : dropK n l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons a t => exact ih t

theorem takeK_eq (n : ℕ) (l : List ℕ) : takeK n l = l.take n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons a t => exact congrArg (a :: ·) (ih t)

theorem lengthK_eq (l : List ℕ) : lengthK l = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => exact congrArg Nat.succ ih

theorem rootsAtK_eq (r : List ℕ) (i n : ℕ) : rootsAtK r i n = rootsAt r i n := by
  unfold rootsAtK rootsAt
  rw [takeK_eq, dropK_eq]
  rfl

theorem dropK_append_left (k : ℕ) (l m : List ℕ) (h : k ≤ l.length) : dropK k (l ++ m) = dropK k l ++ m := by
  induction' k with k ih generalizing l
  · simp [dropK]
  · cases l
    · simp at h
    · rename_i a t
      have hlen : k ≤ t.length := by
        simpa [List.length_cons] using Nat.le_of_succ_le_succ h
      simpa [dropK] using ih t hlen

theorem takeK_append_left (k : ℕ) (l m : List ℕ) (h : k ≤ l.length) : takeK k (l ++ m) = takeK k l := by
  induction k generalizing l with
  | zero =>
      simp [takeK]
  | succ k ih =>
      cases l with
      | nil =>
          simp at h
      | cons a t =>
          simp [takeK]
          have hk : k ≤ t.length := by
            simpa [List.length_cons] using Nat.le_of_succ_le_succ h
          exact ih t hk

theorem rootsAt_zero (R : List ℕ) (i : ℕ) : rootsAt R i 0 = [] := by
  unfold rootsAt
  simp

theorem length_rootsAt (r : List ℕ) (i n : ℕ) : (rootsAt r i n).length = min (2 * n) (r.length - 2 * i) := by
  unfold rootsAt
  rw [List.length_take, List.length_drop]

theorem length_append_eq {a b : List ℕ} {A B : ℕ} (ha : a.length = A) (hb : b.length = B) :
    (a ++ b).length = Nat.add A B := by
  rw [List.length_append, ha, hb]
  rfl

theorem rootsAt_append_left (r R : List ℕ) (i n : ℕ) (h : 2 * (i + n) ≤ r.length) :
    rootsAt (r ++ R) i n = rootsAt r i n := by
  unfold rootsAt
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem rootsAtK_append_left (r R : List ℕ) (i n : ℕ) (h : 2 * (i + n) ≤ r.length) :
    rootsAtK (r ++ R) i n = rootsAtK r i n := by
  rw [rootsAtK_eq, rootsAtK_eq, rootsAt_append_left r R i n h]

theorem rootsAt_append_right (r R : List ℕ) (L a i n : ℕ) (hL : r.length = L) (ha : Nat.beq L (Nat.mul 2 a) = true) :
    rootsAt (r ++ R) (Nat.add a i) n = rootsAt R i n := by
  have hL_eq : L = 2 * a := Nat.eq_of_beq_eq_true ha
  have hrlen : r.length = 2 * a := by
    rw [hL, hL_eq]
  unfold rootsAt
  have hdrop : (r ++ R).drop (2 * (a + i)) = R.drop (2 * i) := by
    calc
      (r ++ R).drop (2 * (a + i)) = (r ++ R).drop (2 * a + 2 * i) := by
        rw [Nat.mul_add]
      _ = (r ++ R).drop (r.length + 2 * i) := by rw [hrlen]
      _ = r.drop (r.length + 2 * i) ++ R.drop ((r.length + 2 * i) - r.length) := by rw [List.drop_append]
      _ = r.drop (r.length + 2 * i) ++ R.drop (2 * i) := by
        rw [Nat.add_sub_cancel_left]
      _ = [] ++ R.drop (2 * i) := by
        rw [List.drop_of_length_le (by omega : r.length ≤ r.length + 2 * i)]
      _ = R.drop (2 * i) := by simp
  simpa using congrArg (fun l => List.take (2 * n) l) hdrop

theorem rootsAt_of_ble (r R : List ℕ) (L i n : ℕ) (hL : r.length = L)
    (hle : Nat.ble (Nat.mul 2 (Nat.add i n)) L = true) : rootsAt (r ++ R) i n = rootsAtK r i n := by
  have h : 2 * (i + n) ≤ r.length := hL ▸ Nat.le_of_ble_eq_true hle
  rw [rootsAt_append_left r R i n h, rootsAtK_eq]

theorem rootsAt_of_lengthK (r R : List ℕ) (i n : ℕ)
    (h : Nat.beq (lengthK (rootsAtK r i n)) (Nat.mul 2 n) = true) : rootsAt (r ++ R) i n = rootsAtK r i n := by
  rw [rootsAtK_eq] at h ⊢
  rw [lengthK_eq] at h
  have h' := Nat.eq_of_beq_eq_true h
  unfold rootsAt at h' ⊢
  rw [List.length_take, List.length_drop] at h'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hle : 2 * (i + n) ≤ r.length := by
      have : Nat.mul 2 n = 2 * n := rfl
      omega
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem bool_of_ble {f : List ℕ → Bool} {r R : List ℕ} {L i n : ℕ} (hL : r.length = L)
    (hle : Nat.ble (Nat.mul 2 (Nat.add i n)) L = true) (h : f (rootsAtK r i n) = true) :
    f (rootsAt (r ++ R) i n) = true := by
  rw [rootsAt_of_ble r R L i n hL hle]
  exact h

theorem bool_of_lengthK {f : List ℕ → Bool} {r R : List ℕ} {i n : ℕ}
    (h : (Nat.beq (lengthK (rootsAtK r i n)) (Nat.mul 2 n) && f (rootsAtK r i n)) = true) :
    f (rootsAt (r ++ R) i n) = true := by
  rw [Bool.and_eq_true] at h
  rw [rootsAt_of_lengthK r R i n h.1]
  exact h.2

theorem cover_of_coverK_ble {c : GCode} {r R : List ℕ} {L i n : ℕ} (hL : r.length = L)
    (hle : Nat.ble (Nat.mul 2 (Nat.add i n)) L = true) (h : coverK c (rootsAtK r i n) = true) :
    cover c (rootsAt (r ++ R) i n) = true := by
  rw [rootsAt_of_ble r R L i n hL hle, ← coverK_eq]
  exact h

theorem cover_of_coverK_len {c : GCode} {r R : List ℕ} {i n : ℕ}
    (h : (Nat.beq (lengthK (rootsAtK r i n)) (Nat.mul 2 n) && coverK c (rootsAtK r i n)) = true) :
    cover c (rootsAt (r ++ R) i n) = true := by
  rw [Bool.and_eq_true] at h
  rw [rootsAt_of_lengthK r R i n h.1, ← coverK_eq]
  exact h.2

theorem chunkG_appendL {Q : Checker} {a b : List (List ℕ)} (ha : ChunkG Q a) (hb : ChunkG Q b) :
    ChunkG Q (List.append a b) :=
  chunkG_append ha hb

end Tammes15.D3Data
