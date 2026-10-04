import Tammes15.W1Filter.Basic

set_option maxHeartbeats 400000

namespace Tammes15.W1Filter

open Tammes15 Tammes15.D3lp
open scoped Classical

theorem packBytes_lt (a : Array ℕ) : packBytes a < 256 ^ a.size := by
  have h : ∀ l : List ℕ, List.foldr (fun x acc => acc * 256 + x % 256) 0 l < 256 ^ l.length := by
    intro l
    induction' l with x xs ih
    · simp
    · simp [List.foldr]
      have hx : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
      rw [Nat.pow_succ]
      nlinarith
  have hfold : packBytes a = List.foldr (fun x acc => acc * 256 + x % 256) 0 a.toList := by
    rw [packBytes, Array.foldr_toList]
  have hsize : a.size = a.toList.length := by simp
  rw [hfold, hsize]
  exact h a.toList

theorem natBytes_injective {k x y : ℕ} (hx : x < 256 ^ k) (hy : y < 256 ^ k)
    (h : natBytes x k = natBytes y k) : x = y := by
  induction' k with k ih generalizing x y
  ·
    have hx0 : x = 0 := Nat.lt_one_iff.mp (by
      simpa [pow_zero] using hx)
    have hy0 : y = 0 := Nat.lt_one_iff.mp (by
      simpa [pow_zero] using hy)
    rw [hx0, hy0]
  ·

    have hx_unfold : natBytes x (k + 1) = ⟨#[(x % 256).toUInt8]⟩ ++ natBytes (x / 256) k := rfl
    have hy_unfold : natBytes y (k + 1) = ⟨#[(y % 256).toUInt8]⟩ ++ natBytes (y / 256) k := rfl
    rw [hx_unfold, hy_unfold] at h

    have hdata : (⟨#[(x % 256).toUInt8]⟩ ++ natBytes (x / 256) k).data = (⟨#[(y % 256).toUInt8]⟩ ++ natBytes (y / 256) k).data := by rw [h]

    rw [ByteArray.data_append, ByteArray.data_append] at hdata

    simp at hdata

    have h_size : #[(x % 256).toUInt8].size = #[(y % 256).toUInt8].size := by
      simp
    rcases Array.append_inj hdata h_size with ⟨h_first, h_rest⟩

    have h_first_u8 : (x % 256).toUInt8 = (y % 256).toUInt8 := by
      simpa using h_first

    have h_mod_eq : x % 256 = y % 256 := by
      have hx_toNat : ((x % 256).toUInt8).toNat = x % 256 := by
        simp
      have hy_toNat : ((y % 256).toUInt8).toNat = y % 256 := by
        simp
      calc
        x % 256 = ((x % 256).toUInt8).toNat := by symm; exact hx_toNat
        _ = ((y % 256).toUInt8).toNat := by rw [h_first_u8]
        _ = y % 256 := hy_toNat

    have h_rest_ba : natBytes (x / 256) k = natBytes (y / 256) k :=
      ByteArray.ext h_rest

    have hx_div : x / 256 < 256 ^ k := by
      rw [pow_succ] at hx
      have hpos : 0 < 256 := by norm_num
      rw [Nat.div_lt_iff_lt_mul hpos]
      simpa [mul_comm] using hx
    have hy_div : y / 256 < 256 ^ k := by
      rw [pow_succ] at hy
      have hpos : 0 < 256 := by norm_num
      rw [Nat.div_lt_iff_lt_mul hpos]
      simpa [mul_comm] using hy

    have h_div_eq : x / 256 = y / 256 :=
      ih hx_div hy_div h_rest_ba

    calc
      x = 256 * (x / 256) + x % 256 := by rw [Nat.div_add_mod x 256]
      _ = 256 * (y / 256) + y % 256 := by rw [h_div_eq, h_mod_eq]
      _ = y := by rw [Nat.div_add_mod y 256]

theorem degree_eq_length {P : PlaneGraph} {nbr : Fin P.n → List ℕ} (h : ListsMatch P nbr)
    (v : Fin P.n) : P.G.degree v = (nbr v).length := by
  have hcard : (P.G.neighborFinset v).card = (nbr v).toFinset.card := by
    refine Finset.card_nbij (s := P.G.neighborFinset v) (t := (nbr v).toFinset) (fun w => (w : ℕ) + 1) ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw
      rw [Finset.mem_coe]
      have hx := (h.adj v w).mp hw
      simpa using hx
    · intro w1 hw1 w2 hw2 h_eq
      rw [Finset.mem_coe] at hw1 hw2
      rw [SimpleGraph.mem_neighborFinset] at hw1 hw2
      have h_eq' : (w1 : ℕ) + 1 = (w2 : ℕ) + 1 := by simpa using h_eq
      apply Fin.ext
      omega
    · intro x hx
      rw [Finset.mem_coe] at hx
      have hx' : x ∈ nbr v := by
        rwa [List.mem_toFinset] at hx
      rcases h.range v x hx' with ⟨hx1, hx2⟩
      have hxpos : x - 1 < P.n := by
        omega
      let w : Fin P.n := ⟨x - 1, hxpos⟩
      refine ⟨w, ?_, ?_⟩
      · rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
        apply (h.adj v w).mpr
        have : (w : ℕ) + 1 = x := by
          simp [w]
          omega
        rw [this]
        exact hx'
      · simp [w]
        omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree P.G v, hcard, List.toFinset_card_of_nodup (h.nodup v)]

theorem degGo_segment (b : ByteArray) (n fuel i v c : ℕ) (ok : Bool) (l : List ℕ) (hv : v < n)
    (hl : ∀ x ∈ l, 0 < x ∧ x < 256)
    (hb : ∀ j (hj : j < l.length), b.data[i + j]? = some (l[j]'hj).toUInt8)
    (h0 : b.data[i + l.length]? = some 0) :
    degGo b n (fuel + l.length + 1) i v c ok =
      degGo b n fuel (i + l.length + 1) (v + 1) 0 (ok && 3 ≤ c + l.length && c + l.length ≤ 5) := by
  induction l generalizing i c fuel with
  | nil =>
    have h0' : b.data[i]? = some 0 := by simpa using h0
    rcases Array.getElem?_eq_some_iff.mp h0' with ⟨hi_data, hzero_data⟩
    have hi : i < b.size := by
      rw [← ByteArray.size_data]
      exact hi_data
    have hzero : (b[i]'hi).toNat = 0 := by
      rw [ByteArray.getElem_eq_getElem_data]
      simpa [hzero_data] using rfl
    have hnle : ¬ n ≤ v := Nat.not_le.mpr hv
    simp [degGo, hnle, hi, hzero]
  | cons x l' IH =>
    have hx_pos : 0 < x := (hl x (by simp)).1
    have hx_lt_256 : x < 256 := (hl x (by simp)).2
    have hnle : ¬ n ≤ v := Nat.not_le.mpr hv
    have hlen_pos : 0 < (x :: l').length := by simp
    have hi : i < b.size := by
      have hb0 := hb 0 hlen_pos
      have hb0_simp : b.data[i]? = some (x.toUInt8) := by simpa using hb0
      have hne : b.data[i]? ≠ none := by
        rw [hb0_simp]
        simp
      have h_lt : i < b.data.size := by
        by_contra! hge
        have hnone : b.data[i]? = none := (Array.getElem?_eq_none_iff.mpr hge)
        exact hne hnone
      rw [← ByteArray.size_data]
      exact h_lt
    have h_not_zero : (b[i]'hi).toNat ≠ 0 := by
      have hb0 := hb 0 hlen_pos
      have hb0_simp : b.data[i]? = some (x.toUInt8) := by simpa using hb0
      rcases Array.getElem?_eq_some_iff.mp hb0_simp with ⟨_, h_eq⟩
      rw [ByteArray.getElem_eq_getElem_data]
      rw [h_eq]
      have hx_mod : x % 256 = x := Nat.mod_eq_of_lt hx_lt_256
      simp [hx_mod, hx_pos.ne']
    have h_degGo_step : degGo b n (fuel + (x :: l').length + 1) i v c ok =
                        degGo b n (fuel + l'.length + 1) (i + 1) v (c + 1) ok := by
      calc
        degGo b n (fuel + (x :: l').length + 1) i v c ok
            = degGo b n (fuel + (l'.length + 1) + 1) i v c ok := by simp
        _ = degGo b n ((fuel + l'.length + 1) + 1) i v c ok := by ring
        _ = degGo b n (fuel + l'.length + 1) (i + 1) v (c + 1) ok := by
          simp [degGo, hnle, hi, h_not_zero]
    rw [h_degGo_step]
    have hl_tail : ∀ x' ∈ l', 0 < x' ∧ x' < 256 := by
      intro x' hx'
      exact hl x' (by simp [hx'])
    have hb_tail : ∀ j (hj : j < l'.length), b.data[(i + 1) + j]? = some (l'[j]'hj).toUInt8 := by
      intro j hj
      have hj' : j + 1 < (x :: l').length := by
        simp [hj]
      have hbj := hb (j + 1) hj'
      have h_simp1 : i + (j + 1) = (i + 1) + j := by omega
      have h_simp2 : ((x :: l')[j + 1]'(hj')) = l'[j] := by simp
      simpa [h_simp1, h_simp2] using hbj
    have h0_tail : b.data[(i + 1) + l'.length]? = some 0 := by
      have h_simp : i + (x :: l').length = (i + 1) + l'.length := by
        simp; omega
      simpa [add_comm, add_left_comm, add_assoc, h_simp] using h0
    have IH' := IH fuel (i + 1) (c + 1) hl_tail hb_tail h0_tail
    simpa [add_comm, add_left_comm, add_assoc] using IH'

def lbytes (L : List (List ℕ)) : List ℕ := (L.map (· ++ [0])).flatten

def fstOf : ℕ → List (List ℕ) → List ℕ
  | _, [] => []
  | v, l :: L => List.replicate l.length v ++ fstOf (v + 1) L

def sndOf (L : List (List ℕ)) : List ℕ := (L.map fun l => l.map (· - 1)).flatten

def offsOf : ℕ → List (List ℕ) → List ℕ
  | _, [] => []
  | s, l :: L => (s + l.length) :: offsOf (s + l.length) L

theorem degGo_lists (b : ByteArray) (n : ℕ) (L : List (List ℕ)) (fuel i v : ℕ) (ok : Bool)
    (hv : v + L.length ≤ n) (hl : ∀ l ∈ L, ∀ x ∈ l, 0 < x ∧ x < 256)
    (hb : ∀ j (hj : j < (lbytes L).length), b.data[i + j]? = some ((lbytes L)[j]'hj).toUInt8) :
    degGo b n (fuel + (lbytes L).length) i v 0 ok =
      degGo b n fuel (i + (lbytes L).length) (v + L.length) 0
        (ok && L.all fun l => 3 ≤ l.length && l.length ≤ 5) := by
  induction L generalizing fuel i v ok with
  | nil =>
    simp [lbytes]
  | cons l L' ih =>
    have hv_lt : v < n := by
      have hpos : 0 < (l :: L').length := by
        simp
      omega
    have hlen_lbytes : (lbytes (l :: L')).length = l.length + 1 + (lbytes L').length := by
      simp [lbytes, List.length_append]
      omega
    have hLHS_fuel : fuel + (lbytes (l :: L')).length = (fuel + (lbytes L').length) + l.length + 1 := by
      rw [hlen_lbytes]
      omega
    have hb_l : ∀ j (hj : j < l.length), b.data[i + j]? = some (l[j]'hj).toUInt8 := by
      intro j hj
      have hpos : j < (lbytes (l :: L')).length := by
        rw [hlen_lbytes]
        omega
      have h_eq := hb j hpos

      have h_lst : (lbytes (l :: L'))[j] = l[j] := by
        have h' : j < (l ++ ([0] ++ lbytes L')).length := by
          simp
          omega
        have h := List.getElem_append_left (as := l) (bs := [0] ++ lbytes L') (i := j) (h := hj) (h' := h')
        simpa [lbytes] using h
      simpa [h_lst] using h_eq
    have h0 : b.data[i + l.length]? = some 0 := by
      have hpos : l.length < (lbytes (l :: L')).length := by
        rw [hlen_lbytes]
        omega
      have h_eq := hb l.length hpos

      have h_lst : (lbytes (l :: L'))[l.length] = 0 := by
        simp [lbytes]
      simpa [h_lst] using h_eq
    have hl_l : ∀ x ∈ l, 0 < x ∧ x < 256 := by
      intro x hx
      exact hl l (by simp) x hx
    have hseg := degGo_segment b n (fuel + (lbytes L').length) i v 0 ok l hv_lt hl_l hb_l h0
    have hv' : (v + 1) + L'.length ≤ n := by
      simpa [add_comm, add_left_comm, add_assoc] using hv
    have hl' : ∀ l' ∈ L', ∀ x ∈ l', 0 < x ∧ x < 256 := by
      intro l' hl' x hx
      exact hl l' (List.mem_cons_of_mem _ hl') x hx
    have hb' : ∀ j (hj : j < (lbytes L').length), b.data[(i + l.length + 1) + j]? = some ((lbytes L')[j]'hj).toUInt8 := by
      intro j hj
      have hpos : l.length + 1 + j < (lbytes (l :: L')).length := by
        rw [hlen_lbytes]
        omega
      have h_eq := hb (l.length + 1 + j) hpos

      have h_idx : (i + l.length + 1) + j = i + (l.length + 1 + j) := by omega
      rw [h_idx]

      have h_lst : (lbytes (l :: L'))[l.length + 1 + j] = (lbytes L')[j] := by
        have h := List.getElem_append_right (as := l ++ [0]) (bs := lbytes L') (i := l.length + 1 + j)
          (by
            have : (l ++ [0]).length = l.length + 1 := by simp
            rw [this]
            omega)
          (h₂ := by
            have : (lbytes (l :: L')).length = ((l ++ [0]) ++ lbytes L').length := by simp [lbytes]
            rw [← this]
            exact hpos)
        simpa [lbytes] using h

      simpa [h_lst] using h_eq
    have ih_app := ih fuel (i + l.length + 1) (v + 1) (ok && 3 ≤ l.length && l.length ≤ 5) hv' hl' hb'
    calc
      degGo b n (fuel + (lbytes (l :: L')).length) i v 0 ok
          = degGo b n ((fuel + (lbytes L').length) + l.length + 1) i v 0 ok := by
        rw [hlen_lbytes]
        simp [add_comm, add_left_comm, add_assoc]
      _ = degGo b n (fuel + (lbytes L').length) (i + l.length + 1) (v + 1) 0 (ok && 3 ≤ l.length && l.length ≤ 5) := by
        simpa [add_comm, add_left_comm, add_assoc] using hseg
      _ = degGo b n fuel (i + l.length + 1 + (lbytes L').length) (v + 1 + L'.length) 0
            ((ok && 3 ≤ l.length && l.length ≤ 5) && L'.all fun l' => 3 ≤ l'.length && l'.length ≤ 5) := by rw [ih_app]
      _ = degGo b n fuel (i + (lbytes (l :: L')).length) (v + (l :: L').length) 0
            (ok && (l :: L').all fun l' => 3 ≤ l'.length && l'.length ≤ 5) := by
        simp [hlen_lbytes, List.all, add_comm, add_left_comm, add_assoc, Bool.and_assoc]

theorem scan_lists (b : ByteArray) (n : ℕ) (L : List (List ℕ)) (fuel i v : ℕ)
    (fst snd off : Array ℕ) (hv : v + L.length ≤ n) (hl : ∀ l ∈ L, ∀ x ∈ l, 0 < x ∧ x < 256)
    (hb : ∀ j (hj : j < (lbytes L).length), b.data[i + j]? = some ((lbytes L)[j]'hj).toUInt8) :
    scan b n (fuel + (lbytes L).length) i v fst snd off =
      scan b n fuel (i + (lbytes L).length) (v + L.length) (fst ++ (fstOf v L).toArray)
        (snd ++ (sndOf L).toArray) (off ++ (offsOf fst.size L).toArray) := by
  induction L generalizing fuel i v fst snd off with
  | nil =>
    simp [lbytes, fstOf, sndOf, offsOf]
  | cons l L' ih =>
    have hv_lt : v < n := by
      have hpos : 0 < (l :: L').length := by
        simp
      omega
    have hlen_lbytes : (lbytes (l :: L')).length = l.length + 1 + (lbytes L').length := by
      simp [lbytes, List.length_append]
      omega
    have hLHS_fuel : fuel + (lbytes (l :: L')).length = (fuel + (lbytes L').length) + l.length + 1 := by
      rw [hlen_lbytes]
      omega
    have hb_l : ∀ j (hj : j < l.length), b.data[i + j]? = some (l[j]'hj).toUInt8 := by
      intro j hj
      have hpos : j < (lbytes (l :: L')).length := by
        rw [hlen_lbytes]
        omega
      have h_eq := hb j hpos

      have h_lst : (lbytes (l :: L'))[j] = l[j] := by
        have h' : j < (l ++ ([0] ++ lbytes L')).length := by
          simp
          omega
        have h := List.getElem_append_left (as := l) (bs := [0] ++ lbytes L') (i := j) (h := hj) (h' := h')
        simpa [lbytes] using h
      simpa [h_lst] using h_eq
    have h0 : b.data[i + l.length]? = some 0 := by
      have hpos : l.length < (lbytes (l :: L')).length := by
        rw [hlen_lbytes]
        omega
      have h_eq := hb l.length hpos

      have h_lst : (lbytes (l :: L'))[l.length] = 0 := by
        simp [lbytes]
      simpa [h_lst] using h_eq
    have hl_l : ∀ x ∈ l, 0 < x ∧ x < 256 := by
      intro x hx
      exact hl l (by simp) x hx
    have hv' : (v + 1) + L'.length ≤ n := by
      simpa [add_comm, add_left_comm, add_assoc] using hv
    have hl' : ∀ l' ∈ L', ∀ x ∈ l', 0 < x ∧ x < 256 := by
      intro l' hl' x hx
      exact hl l' (List.mem_cons_of_mem _ hl') x hx
    have hb' : ∀ j (hj : j < (lbytes L').length), b.data[(i + l.length + 1) + j]? = some ((lbytes L')[j]'hj).toUInt8 := by
      intro j hj
      have hpos : l.length + 1 + j < (lbytes (l :: L')).length := by
        rw [hlen_lbytes]
        omega
      have h_eq := hb (l.length + 1 + j) hpos

      have h_idx : (i + l.length + 1) + j = i + (l.length + 1 + j) := by omega
      rw [h_idx]

      have h_lst : (lbytes (l :: L'))[l.length + 1 + j] = (lbytes L')[j] := by
        have h := List.getElem_append_right (as := l ++ [0]) (bs := lbytes L') (i := l.length + 1 + j)
          (by
            have : (l ++ [0]).length = l.length + 1 := by simp
            rw [this]
            omega)
          (h₂ := by
            have : (lbytes (l :: L')).length = ((l ++ [0]) ++ lbytes L').length := by simp [lbytes]
            rw [← this]
            exact hpos)
        simpa [lbytes] using h

      simpa [h_lst] using h_eq
    have hseg := scan_segment b n (fuel + (lbytes L').length) i v fst snd off l hv_lt hl_l hb_l h0
    have ih_app := ih fuel (i + l.length + 1) (v + 1) (fst ++ (List.replicate l.length v).toArray)
      (snd ++ (l.map (· - 1)).toArray) (off.push (fst.size + l.length)) hv' hl' hb'
    rw [hLHS_fuel, hseg, ih_app]
    have e1 : i + l.length + 1 + (lbytes L').length = i + (lbytes (l :: L')).length := by
      rw [hlen_lbytes]; omega
    have e2 : v + 1 + L'.length = v + (l :: L').length := by simp; omega
    have e3 : fst ++ (List.replicate l.length v).toArray ++ (fstOf (v + 1) L').toArray =
        fst ++ (fstOf v (l :: L')).toArray := by
      apply Array.toList_inj.mp
      simp [fstOf]
    have e4 : snd ++ (l.map (· - 1)).toArray ++ (sndOf L').toArray =
        snd ++ (sndOf (l :: L')).toArray := by
      apply Array.toList_inj.mp
      simp [sndOf]
    have e5 : off.push (fst.size + l.length) ++
        (offsOf (fst ++ (List.replicate l.length v).toArray).size L').toArray =
        off ++ (offsOf fst.size (l :: L')).toArray := by
      apply Array.toList_inj.mp
      simp [offsOf]
    rw [e1, e2, e3, e4, e5]

structure DecSpec (L : List (List ℕ)) (g : Darts) : Prop where
  off_size : g.off.size = L.length + 1
  off_zero : g.off.getD 0 0 = 0
  off_succ : ∀ v, v < L.length → g.off.getD (v + 1) 0 = g.off.getD v 0 + (L.getD v []).length
  fst_size : g.fst.size = g.off.getD L.length 0
  snd_size : g.snd.size = g.off.getD L.length 0
  fst_at : ∀ v i, v < L.length → i < (L.getD v []).length → g.fst.getD (g.off.getD v 0 + i) 0 = v
  snd_at : ∀ v i, v < L.length → i < (L.getD v []).length →
    g.snd.getD (g.off.getD v 0 + i) 0 = (L.getD v []).getD i 0 - 1

theorem offsOf_length (s : ℕ) (L : List (List ℕ)) : (offsOf s L).length = L.length := by
  induction L generalizing s with
  | nil => rfl
  | cons l L ih => simp [offsOf, ih]

theorem offsOf_getD (L : List (List ℕ)) (s v : ℕ) (hv : v ≤ L.length) :
    (s :: offsOf s L).getD v 0 = s + ((L.take v).map List.length).sum := by
  induction L generalizing s v with
  | nil =>
    obtain rfl : v = 0 := by simpa using hv
    simp
  | cons l L ih =>
    cases v with
    | zero => simp
    | succ v =>
      simp only [offsOf, List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [ih (s + l.length) v (by simpa using hv)]
      omega

theorem fstOf_length (v0 : ℕ) (L : List (List ℕ)) :
    (fstOf v0 L).length = (L.map List.length).sum := by
  induction L generalizing v0 with
  | nil => rfl
  | cons l L ih => simp [fstOf, ih]

theorem sndOf_length (L : List (List ℕ)) : (sndOf L).length = (L.map List.length).sum := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [sndOf, List.map_cons, List.flatten_cons, List.length_append, List.length_map,
      List.sum_cons] at ih ⊢
    rw [ih]

theorem fstOf_getD (L : List (List ℕ)) (v0 v i : ℕ) (hv : v < L.length)
    (hi : i < (L.getD v []).length) :
    (fstOf v0 L).getD (((L.take v).map List.length).sum + i) 0 = v0 + v := by
  induction L generalizing v0 v with
  | nil => simp at hv
  | cons l L ih =>
    cases v with
    | zero =>
      simp only [List.getD_cons_zero] at hi
      simp only [fstOf, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add]
      have hi' : i < (List.replicate l.length v0).length := by simpa using hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
      simp [List.getElem?_replicate, hi]
    | succ v =>
      simp only [List.getD_cons_succ] at hi
      simp only [fstOf, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [show l.length + ((L.take v).map List.length).sum + i =
          (List.replicate l.length v0).length + (((L.take v).map List.length).sum + i) by simp; omega]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD,
        ih (v0 + 1) v (by simpa using hv) hi]
      omega

theorem sndOf_getD (L : List (List ℕ)) (v i : ℕ) (hv : v < L.length)
    (hi : i < (L.getD v []).length) :
    (sndOf L).getD (((L.take v).map List.length).sum + i) 0 = (L.getD v []).getD i 0 - 1 := by
  induction L generalizing v with
  | nil => simp at hv
  | cons l L ih =>
    cases v with
    | zero =>
      simp only [List.getD_cons_zero] at hi ⊢
      simp only [sndOf, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.map_cons,
        List.flatten_cons]
      have hi' : i < (l.map (· - 1)).length := by simpa using hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi', List.getD_eq_getElem _ _ hi]
      simp [hi]
    | succ v =>
      simp only [List.getD_cons_succ] at hi ⊢
      have ih' := ih v (by simpa using hv) hi
      simp only [sndOf] at ih' ⊢
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
      rw [show l.length + ((L.take v).map List.length).sum + i =
          (l.map (· - 1)).length + (((L.take v).map List.length).sum + i) by simp; omega]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD, ih']

theorem toArray_getD (l : List ℕ) (v : ℕ) : l.toArray.getD v 0 = l.getD v 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem decSpec_lists (n : ℕ) (L : List (List ℕ)) :
    DecSpec L ⟨n, (fstOf 0 L).toArray, (sndOf L).toArray, #[0] ++ (offsOf 0 L).toArray⟩ := by
  have hA : (#[0] ++ (offsOf 0 L).toArray) = (0 :: offsOf 0 L).toArray := by
    apply Array.toList_inj.mp
    simp
  have hO : ∀ v, v ≤ L.length →
      (#[0] ++ (offsOf 0 L).toArray).getD v 0 = ((L.take v).map List.length).sum := by
    intro v hv
    rw [hA, toArray_getD, offsOf_getD L 0 v hv, Nat.zero_add]
  have hS : ∀ v, v < L.length → ((L.take (v + 1)).map List.length).sum =
      ((L.take v).map List.length).sum + (L.getD v []).length := by
    intro v hv
    rw [List.take_succ, List.map_append, List.sum_append, List.getElem?_eq_getElem hv,
      List.getD_eq_getElem _ _ hv]
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
  have hD : ((L.take L.length).map List.length).sum = (L.map List.length).sum := by
    rw [List.take_length]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [offsOf_length]
  · rw [hO 0 (Nat.zero_le _)]
    simp
  · intro v hv
    simp only
    rw [hO (v + 1) hv, hO v hv.le, hS v hv]
  · simp only
    rw [hO L.length le_rfl, hD, List.size_toArray, fstOf_length]
  · simp only
    rw [hO L.length le_rfl, hD, List.size_toArray, sndOf_length]
  · intro v i hv hi
    simp only
    rw [hO v hv.le, toArray_getD, fstOf_getD L 0 v i hv hi, Nat.zero_add]
  · intro v i hv hi
    simp only
    rw [hO v hv.le, toArray_getD, sndOf_getD L v i hv hi]

theorem degPass_pcBytes (n : ℕ) (nbr : Fin n → List ℕ) (rest : List ℕ) (hn : 0 < n)
    (hn' : n < 256) (hr : ∀ v, ∀ x ∈ nbr v, 0 < x ∧ x < 256) :
    degPass (toBytes (pcBytes n nbr ++ rest)) 0 =
      some ((pcBytes n nbr).length, decide (∀ v, 3 ≤ (nbr v).length ∧ (nbr v).length ≤ 5)) := by
  set L := List.ofFn nbr
  have hLlen : L.length = n := by
    simpa [L] using List.length_ofFn nbr
  set b := toBytes (pcBytes n nbr ++ rest)
  have hpcBytes : pcBytes n nbr = n :: lbytes L := by
    simp [pcBytes, lbytes, L]
    rfl
  have hblen : b.size = 1 + (lbytes L).length + rest.length := by
    simp [b, toBytes, hpcBytes, ByteArray.size]
    omega
  have hsize_pos : 0 < b.size := by
    rw [hblen]
    omega
  have hb0_val : (b[0]'hsize_pos).toNat = n := by
    dsimp [b, toBytes, hpcBytes]
    have hpos : 0 < ({ data := (List.map Nat.toUInt8 (n :: lbytes L ++ rest)).toArray } : ByteArray).size := by
      simp [ByteArray.size]
    calc
      (({ data := (List.map Nat.toUInt8 (n :: lbytes L ++ rest)).toArray } : ByteArray)[0]'hpos).toNat
          = ((({ data := (List.map Nat.toUInt8 (n :: lbytes L ++ rest)).toArray } : ByteArray).data)[0]'hpos).toNat := by
        rw [ByteArray.getElem_eq_data_getElem]
      _ = (((List.map Nat.toUInt8 (n :: lbytes L ++ rest)).toArray)[0]'hpos).toNat := rfl
      _ = (Nat.toUInt8 n).toNat := by simp
      _ = n := by
        rw [Nat.toUInt8_eq]
        exact (UInt8.toNat_ofNat_of_lt hn')
  have hb0_ne_zero : (b[0]'hsize_pos).toNat ≠ 0 := by
    rw [hb0_val]
    exact Nat.ne_of_gt hn
  have hmem : ∀ (l : List ℕ), l ∈ L → ∀ x ∈ l, 0 < x ∧ x < 256 := by
    intro l hl x hx
    rcases List.mem_ofFn.mp hl with ⟨v, rfl⟩
    exact hr v x hx
  have hb_data : ∀ j (hj : j < (lbytes L).length),
      b.data[1 + j]? = some ((lbytes L)[j]'hj).toUInt8 := by
    intro j hj
    have hpos_data : 1 + j < b.data.size := by
      have : b.data.size = b.size := rfl
      rw [this, hblen]
      omega
    have hpos_list : 1 + j < (n :: lbytes L ++ rest).length := by
      have : (n :: lbytes L ++ rest).length = 1 + (lbytes L).length + rest.length := by
        simp [lbytes, List.length_cons, List.length_append]
        omega
      rw [this]
      omega
    have hpos_append : j < (lbytes L ++ rest).length := by
      have : (lbytes L ++ rest).length = (lbytes L).length + rest.length := by
        simp
      rw [this]
      omega
    have hpos_arr : 1 + j < ((n :: lbytes L ++ rest).map Nat.toUInt8).toArray.size := by
      simpa [b, toBytes, hpcBytes] using hpos_data
    calc
      b.data[1 + j]? = some (b.data[1 + j]'hpos_data) := by
        simp
      _ = some ((((n :: lbytes L ++ rest).map Nat.toUInt8).toArray)[1 + j]'hpos_arr) := by
        simp [b, toBytes, hpcBytes]
      _ = some (Nat.toUInt8 ((n :: lbytes L ++ rest)[1 + j]'hpos_list)) := by
        have hpos_arr' : 1 + j < ((n :: lbytes L ++ rest).map Nat.toUInt8).toArray.size := by
          simpa [List.length_map] using hpos_list
        rw [List.getElem_toArray, List.getElem_map]
      _ = some (Nat.toUInt8 ((lbytes L ++ rest)[j]'hpos_append)) := by
        simpa [add_comm] using congrArg (fun t => some (Nat.toUInt8 t)) (List.getElem_cons_succ _ _ _ hpos_list)
      _ = some (Nat.toUInt8 ((lbytes L)[j]'hj)) := by
        rw [List.getElem_append_left hj]
      _ = some ((lbytes L)[j]'hj).toUInt8 := by simp
  have hdeg := degGo_lists b n L (rest.length + 1) 1 0 true
    (by simpa [add_comm, add_left_comm, add_assoc, hLlen] using le_rfl) hmem hb_data
  have hall : (L.all fun l => decide (3 ≤ l.length) && decide (l.length ≤ 5)) =
      decide (∀ v, 3 ≤ (nbr v).length ∧ (nbr v).length ≤ 5) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
    constructor
    · intro h v
      have := h (nbr v) (List.mem_ofFn.mpr ⟨v, rfl⟩)
      simpa using this
    · intro h l hl
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hl
      simpa using h v
  have hdeg_final : degGo b n b.size 1 0 0 true =
      some (1 + (lbytes L).length, decide (∀ v, 3 ≤ (nbr v).length ∧ (nbr v).length ≤ 5)) := by
    have hbsize_eq : b.size = rest.length + 1 + (lbytes L).length := by
      rw [hblen]
      omega
    rw [hbsize_eq, hdeg, ← hall]
    have h0L : 0 + L.length = n := by omega
    rw [h0L]
    unfold degGo
    simp
  unfold degPass
  have hn0 : ¬ n = 0 := by omega
  simp only [hsize_pos, dite_true, hb0_val, hn0, if_false, Nat.sub_zero, Nat.zero_add, hdeg_final,
    hpcBytes, List.length_cons]
  congr 2
  omega

theorem decode_pcBytes (n : ℕ) (nbr : Fin n → List ℕ) (rest : List ℕ) (hn : 0 < n)
    (hn' : n < 256) (hr : ∀ v, ∀ x ∈ nbr v, 0 < x ∧ x < 256) :
    ∃ g : Darts, decode (toBytes (pcBytes n nbr ++ rest)) 0 = some ((pcBytes n nbr).length, g) ∧
      g.n = n ∧ DecSpec (List.ofFn nbr) g := by
  set L := List.ofFn nbr
  set g : Darts := ⟨n, (fstOf 0 L).toArray, (sndOf L).toArray, #[0] ++ (offsOf 0 L).toArray⟩
  have hg_n : g.n = n := rfl
  have hDspec : DecSpec L g := decSpec_lists n L
  have hLlen : L.length = n := by
    simpa [L] using List.length_ofFn nbr
  set b := toBytes (pcBytes n nbr ++ rest)
  have hpcBytes : pcBytes n nbr = n :: lbytes L := by
    simp [pcBytes, lbytes, L]
    rfl
  have hblen : b.size = 1 + (lbytes L).length + rest.length := by
    simp [b, toBytes, hpcBytes, ByteArray.size]
    omega
  have hsize_pos : 0 < b.size := by
    rw [hblen]
    omega
  have hb0_val : (b[0]'hsize_pos).toNat = n := by
    dsimp [b, toBytes, hpcBytes]
    have hpos : 0 < ({ data := (List.map Nat.toUInt8 (n :: lbytes L ++ rest)).toArray } : ByteArray).size := by
      simp [ByteArray.size]
    calc
      (({ data := (List.map Nat.toUInt8 (n :: lbytes L ++ rest)).toArray } : ByteArray)[0]'hpos).toNat
          = ((({ data := (List.map Nat.toUInt8 (n :: lbytes L ++ rest)).toArray } : ByteArray).data)[0]'hpos).toNat := by
        rw [ByteArray.getElem_eq_data_getElem]
      _ = (((List.map Nat.toUInt8 (n :: lbytes L ++ rest)).toArray)[0]'hpos).toNat := rfl
      _ = (Nat.toUInt8 n).toNat := by simp
      _ = n := by
        rw [Nat.toUInt8_eq]
        exact (UInt8.toNat_ofNat_of_lt hn')
  have hb0_ne_zero : (b[0]'hsize_pos).toNat ≠ 0 := by
    rw [hb0_val]
    exact Nat.ne_of_gt hn
  have hmem : ∀ (l : List ℕ), l ∈ L → ∀ x ∈ l, 0 < x ∧ x < 256 := by
    intro l hl x hx
    rcases List.mem_ofFn.mp hl with ⟨v, rfl⟩
    exact hr v x hx
  have hb_data : ∀ j (hj : j < (lbytes L).length),
      b.data[1 + j]? = some ((lbytes L)[j]'hj).toUInt8 := by
    intro j hj
    have hpos_data : 1 + j < b.data.size := by
      have : b.data.size = b.size := rfl
      rw [this, hblen]
      omega
    have hpos_list : 1 + j < (n :: lbytes L ++ rest).length := by
      have : (n :: lbytes L ++ rest).length = 1 + (lbytes L).length + rest.length := by
        simp [lbytes, List.length_cons, List.length_append]
        omega
      rw [this]
      omega
    have hpos_append : j < (lbytes L ++ rest).length := by
      have : (lbytes L ++ rest).length = (lbytes L).length + rest.length := by
        simp
      rw [this]
      omega
    have hpos_arr : 1 + j < ((n :: lbytes L ++ rest).map Nat.toUInt8).toArray.size := by
      simpa [b, toBytes, hpcBytes] using hpos_data
    calc
      b.data[1 + j]? = some (b.data[1 + j]'hpos_data) := by
        simp
      _ = some ((((n :: lbytes L ++ rest).map Nat.toUInt8).toArray)[1 + j]'hpos_arr) := by
        simp [b, toBytes, hpcBytes]
      _ = some (Nat.toUInt8 ((n :: lbytes L ++ rest)[1 + j]'hpos_list)) := by
        have hpos_arr' : 1 + j < ((n :: lbytes L ++ rest).map Nat.toUInt8).toArray.size := by
          simpa [List.length_map] using hpos_list
        rw [List.getElem_toArray, List.getElem_map]
      _ = some (Nat.toUInt8 ((lbytes L ++ rest)[j]'hpos_append)) := by
        simpa [add_comm] using congrArg (fun t => some (Nat.toUInt8 t)) (List.getElem_cons_succ _ _ _ hpos_list)
      _ = some (Nat.toUInt8 ((lbytes L)[j]'hj)) := by
        rw [List.getElem_append_left hj]
      _ = some ((lbytes L)[j]'hj).toUInt8 := by simp
  have hscan_lists := scan_lists b n L (rest.length + 1) 1 0 #[] #[] #[0]
    (by
      simpa [add_comm, add_left_comm, add_assoc, hLlen] using le_rfl)
    hmem
    hb_data
  have hscan_simp : scan b n (rest.length + 1 + (lbytes L).length) 1 0 #[] #[] #[0] =
      some (1 + (lbytes L).length, (fstOf 0 L).toArray, (sndOf L).toArray, #[0] ++ (offsOf 0 L).toArray) := by
    rw [hscan_lists]
    have h0L : 0 + L.length = n := by
      simpa [hLlen] using rfl
    have hfst : #[] ++ (fstOf 0 L).toArray = (fstOf 0 L).toArray := by simp
    have hsnd : #[] ++ (sndOf L).toArray = (sndOf L).toArray := by simp
    have hoff : #[0] ++ (offsOf (#[] : Array ℕ).size L).toArray = #[0] ++ (offsOf 0 L).toArray := rfl
    unfold scan
    simp [h0L, hfst, hsnd]

  have hbsize_eq : b.size = rest.length + 1 + (lbytes L).length := by
    rw [hblen]
    omega
  have hscan_final : scan b n b.size 1 0 #[] #[] #[0] =
      some (1 + (lbytes L).length, (fstOf 0 L).toArray, (sndOf L).toArray, #[0] ++ (offsOf 0 L).toArray) := by
    rw [hbsize_eq]
    exact hscan_simp
  have hdecode : decode b 0 = some ((pcBytes n nbr).length, g) := by
    unfold decode
    simp [hsize_pos, hb0_val, hscan_final, hpcBytes, g]

    have hn0 : ¬ n = 0 := by omega
    have hlen : 1 + (lbytes L).length = (lbytes L).length + 1 := by omega
    simp [hn0, hlen]
  exact ⟨g, hdecode, hg_n, hDspec⟩

end Tammes15.W1Filter
