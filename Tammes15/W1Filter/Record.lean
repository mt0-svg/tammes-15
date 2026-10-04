import Tammes15.W1Filter.Table

set_option maxHeartbeats 400000

namespace Tammes15.W1Filter

open Tammes15 Tammes15.D3lp
open scoped Classical

theorem ofFn_getD {n : ℕ} (nbr : Fin n → List ℕ) (v : Fin n) :
    (List.ofFn nbr).getD v [] = nbr v := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem idxOf_inj {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (h : l.idxOf a = l.idxOf b) :
    a = b := by
  have h1 : l[l.idxOf a]? = some a := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem ha), List.getElem_idxOf]
  have h2 : l[l.idxOf b]? = some b := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hb), List.getElem_idxOf]
  rw [h, h2] at h1
  exact (Option.some.inj h1).symm

theorem mod_pred_succ {i d : ℕ} (hi : i < d) : ((i + 1) % d + d - 1) % d = i := by
  rcases Nat.lt_or_ge (i + 1) d with h | h
  · rw [Nat.mod_eq_of_lt h]
    have e : i + 1 + d - 1 = i + d := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have e : i + 1 = d := by omega
    rw [e, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
    omega

theorem face_apply {P : PlaneGraph} (e : P.G.Dart) : P.R.face e = P.R.rot.symm e.symm := rfl

theorem rot_symm_fst {P : PlaneGraph} (x : P.G.Dart) : (P.R.rot.symm x).fst = x.fst := by
  simpa using (P.R.rot_fst (P.R.rot.symm x)).symm

section Lab

variable {P : PlaneGraph} {nbr : Fin P.n → List ℕ}

def labOf (nbr : Fin P.n → List ℕ) (g : Darts) (e : P.G.Dart) : ℕ :=
  g.off.getD e.fst 0 + (nbr e.fst).idxOf ((e.snd : ℕ) + 1)

theorem mem_of_dart (h : ListsMatch P nbr) (e : P.G.Dart) : (e.snd : ℕ) + 1 ∈ nbr e.fst :=
  (h.adj _ _).mp e.adj

theorem idxOf_lt_of_dart (h : ListsMatch P nbr) (e : P.G.Dart) :
    (nbr e.fst).idxOf ((e.snd : ℕ) + 1) < (nbr e.fst).length :=
  List.idxOf_lt_length_of_mem (mem_of_dart h e)

theorem lens_succ {g : Darts} (hs : DecSpec (List.ofFn nbr) g) (v : ℕ) (hv : v < P.n) :
    g.off.getD (v + 1) 0 = g.off.getD v 0 + ((List.ofFn nbr).getD v []).length :=
  hs.off_succ v (by simpa using hv)

theorem off_mono {g : Darts} (hs : DecSpec (List.ofFn nbr) g) {v w : ℕ} (hvw : v ≤ w)
    (hw : w ≤ P.n) : g.off.getD v 0 ≤ g.off.getD w 0 := by
  induction w with
  | zero => obtain rfl : v = 0 := by omega
            exact le_rfl
  | succ w ih =>
    rcases Nat.eq_or_lt_of_le hvw with rfl | hlt
    · exact le_rfl
    · rw [lens_succ hs w (by omega)]
      exact le_add_right (ih (by omega) (by omega))

theorem off_le_five {g : Darts} (hs : DecSpec (List.ofFn nbr) g)
    (hd : ∀ v, (nbr v).length ≤ 5) {v : ℕ} (hv : v ≤ P.n) : g.off.getD v 0 ≤ 5 * v := by
  induction v with
  | zero => rw [hs.off_zero]
  | succ v ih =>
    rw [lens_succ hs v (by omega)]
    have := hd ⟨v, by omega⟩
    rw [show (v : ℕ) = ((⟨v, by omega⟩ : Fin P.n) : ℕ) from rfl, ofFn_getD]
    have := ih (by omega)
    simp only at *
    omega

theorem labOf_lt (h : ListsMatch P nbr) {g : Darts} (hs : DecSpec (List.ofFn nbr) g)
    (e : P.G.Dart) : labOf nbr g e < g.off.getD (e.fst + 1) 0 := by
  have h1 := idxOf_lt_of_dart h e
  rw [lens_succ hs e.fst e.fst.2, ofFn_getD]
  unfold labOf
  omega

theorem labOf_lt_D (h : ListsMatch P nbr) {g : Darts} (hs : DecSpec (List.ofFn nbr) g)
    (e : P.G.Dart) : labOf nbr g e < g.D := by
  have h1 := labOf_lt h hs e
  have h2 := off_mono hs (v := e.fst + 1) (w := P.n) e.fst.2 le_rfl
  have h3 := hs.fst_size
  simp only [List.length_ofFn] at h3
  unfold Darts.D
  omega

theorem labOf_injective (h : ListsMatch P nbr) {g : Darts} (hs : DecSpec (List.ofFn nbr) g) :
    Function.Injective (labOf nbr g) := by
  intro e e' he
  have hb := block_unique (fun v => g.off.getD v 0) (fun v => ((List.ofFn nbr).getD v []).length)
    P.n (lens_succ hs) e.fst.2 e'.fst.2
    (by simpa only [ofFn_getD] using idxOf_lt_of_dart h e)
    (by simpa only [ofFn_getD] using idxOf_lt_of_dart h e') he
  rcases e with ⟨⟨v, w⟩, hadj⟩
  rcases e' with ⟨⟨v', w'⟩, hadj'⟩
  simp only at hb
  obtain rfl : v = v' := Fin.ext hb.1
  have hw := idxOf_inj (mem_of_dart h ⟨(v, w), hadj⟩) (mem_of_dart h ⟨(v, w'), hadj'⟩) hb.2
  simp only [add_left_inj] at hw
  obtain rfl : w = w' := Fin.ext hw
  rfl

theorem exists_labOf (h : ListsMatch P nbr) (g : Darts) (v : Fin P.n) (i : ℕ)
    (hi : i < (nbr v).length) : ∃ e : P.G.Dart, e.fst = v ∧ labOf nbr g e = g.off.getD v 0 + i := by
  have hx := h.range v _ (List.getElem_mem hi)
  let w : Fin P.n := ⟨(nbr v)[i] - 1, by omega⟩
  have hw : (w : ℕ) + 1 = (nbr v)[i] := by simp only [w]; omega
  have hadj : P.G.Adj v w := (h.adj v w).mpr (hw ▸ List.getElem_mem hi)
  refine ⟨⟨(v, w), hadj⟩, rfl, ?_⟩
  unfold labOf
  simp only
  rw [hw, List.Nodup.idxOf_getElem (h.nodup v)]

theorem labOf_face (h : ListsMatch P nbr) {g : Darts} (hs : DecSpec (List.ofFn nbr) g)
    {fa : Array ℕ}
    (hfa : ∀ v i, v < (List.ofFn nbr).length → i < ((List.ofFn nbr).getD v []).length →
      fa.getD (g.off.getD v 0 + i) 0 =
        g.off.getD (((List.ofFn nbr).getD v []).getD i 0 - 1) 0 +
          (((List.ofFn nbr).getD (((List.ofFn nbr).getD v []).getD i 0 - 1) []).idxOf (v + 1) +
              ((List.ofFn nbr).getD (((List.ofFn nbr).getD v []).getD i 0 - 1) []).length - 1) %
            ((List.ofFn nbr).getD (((List.ofFn nbr).getD v []).getD i 0 - 1) []).length)
    (e : P.G.Dart) : fa.getD (labOf nbr g e) 0 = labOf nbr g (P.R.face e) := by
  have hi := idxOf_lt_of_dart h e
  have h1 := hfa e.fst ((nbr e.fst).idxOf ((e.snd : ℕ) + 1)) (by simp)
    (by rw [ofFn_getD]; exact hi)
  rw [ofFn_getD, List.getD_eq_getElem _ _ hi, List.getElem_idxOf, Nat.add_sub_cancel,
    ofFn_getD] at h1
  unfold labOf
  rw [h1]

  set e' := P.R.face e with he'
  have hf : e'.fst = e.snd := by rw [he', face_apply, rot_symm_fst]; rfl
  have hrot : P.R.rot e' = e.symm := by rw [he', face_apply, Equiv.apply_symm_apply]
  have hi' := idxOf_lt_of_dart h e'
  have hr := h.rot e' ((nbr e'.fst).idxOf ((e'.snd : ℕ) + 1)) hi' (List.getElem_idxOf hi')
  rw [hrot] at hr
  have hidx : (nbr e'.fst).idxOf ((e.fst : ℕ) + 1) =
      ((nbr e'.fst).idxOf ((e'.snd : ℕ) + 1) + 1) % (nbr e'.fst).length := by
    have := List.Nodup.idxOf_getElem (h.nodup e'.fst)
      (((nbr e'.fst).idxOf ((e'.snd : ℕ) + 1) + 1) % (nbr e'.fst).length)
      (Nat.mod_lt _ (Nat.zero_lt_of_lt hi'))
    rw [hr] at this
    exact this
  rw [hf] at hidx hi'
  rw [hf, hidx, mod_pred_succ hi']

theorem labOf_block (h : ListsMatch P nbr) {g : Darts} (hs : DecSpec (List.ofFn nbr) g)
    (v : Fin P.n) :
    Finset.Ico (g.off.getD v 0) (g.off.getD v 0 + g.deg v) = (darts P v).image (labOf nbr g) := by
  have hdeg : g.deg v = (nbr v).length := by
    unfold Darts.deg
    rw [lens_succ hs v v.2, ofFn_getD]
    omega
  ext k
  simp only [Finset.mem_Ico, Finset.mem_image, darts, Finset.mem_filter, Finset.mem_univ,
    true_and, hdeg]
  constructor
  · rintro ⟨hk1, hk2⟩
    obtain ⟨e, he, hl⟩ := exists_labOf h g v (k - g.off.getD v 0) (by omega)
    exact ⟨e, he, by omega⟩
  · rintro ⟨e, rfl, rfl⟩
    have := idxOf_lt_of_dart h e
    unfold labOf
    omega

end Lab

theorem filterRec_pcBytes {P : PlaneGraph} {nbr : Fin P.n → List ℕ} (h : ListsMatch P nbr)
    (hn : 0 < P.n) (hn' : P.n ≤ 15) (rest : List ℕ) :
    ∃ (b : Bool) (g : Darts) (fa : Array Nat),
      filterRec (toBytes (pcBytes P.n nbr ++ rest)) 0 =
        some ((pcBytes P.n nbr).length, b, g, fa) ∧
      (b = true ↔ (∀ v, 3 ≤ P.G.degree v ∧ P.G.degree v ≤ 5) ∧ W1Graph P) ∧
      (b = true →
        ∃ lab : P.G.Dart ≃ Fin (toGCode (gcOf g fa)).D, Matches P (toGCode (gcOf g fa)) lab) := by
  have hr : ∀ v, ∀ x ∈ nbr v, 0 < x ∧ x < 256 := fun v x hx => by
    have := h.range v x hx
    omega
  have hdeg : ∀ v, P.G.degree v = (nbr v).length := degree_eq_length h
  simp only [hdeg]
  unfold filterRec
  rw [degPass_pcBytes P.n nbr rest hn (by omega) hr]
  by_cases hd : ∀ v, 3 ≤ (nbr v).length ∧ (nbr v).length ≤ 5
  swap
  · rw [decide_eq_false hd]
    refine ⟨false, Darts.none, #[], rfl, ?_, fun hf => absurd hf Bool.false_ne_true⟩
    exact ⟨fun hf => absurd hf Bool.false_ne_true, fun hw => absurd hw.1 hd⟩
  rw [decide_eq_true hd]
  obtain ⟨g, hdec, hgn, hs⟩ := decode_pcBytes P.n nbr rest hn (by omega) hr
  rw [hdec]
  simp only
  set L := List.ofFn nbr with hL
  have hlen : L.length = P.n := List.length_ofFn

  have hr' : ∀ v, v < L.length → ∀ x ∈ L.getD v [], 1 ≤ x ∧ x ≤ L.length := by
    intro v hv x hx
    rw [hlen] at hv ⊢
    rw [show v = ((⟨v, hv⟩ : Fin P.n) : ℕ) from rfl, hL, ofFn_getD] at hx
    exact h.range _ x hx
  have hnd : ∀ v, v < L.length → (L.getD v []).Nodup := by
    intro v hv
    rw [hlen] at hv
    rw [show v = ((⟨v, hv⟩ : Fin P.n) : ℕ) from rfl, hL, ofFn_getD]
    exact h.nodup _
  have hloop : ∀ v, v < L.length → v + 1 ∉ L.getD v [] := by
    intro v hv hx
    rw [hlen] at hv
    rw [show v = ((⟨v, hv⟩ : Fin P.n) : ℕ) from rfl, hL, ofFn_getD] at hx
    exact P.G.loopless.irrefl _ ((h.adj _ _).mpr hx)
  have hsym : ∀ v w, v < L.length → w < L.length → w + 1 ∈ L.getD v [] → v + 1 ∈ L.getD w [] := by
    intro v w hv hw hx
    rw [hlen] at hv hw
    rw [show v = ((⟨v, hv⟩ : Fin P.n) : ℕ) from rfl, hL, ofFn_getD] at hx
    rw [show w = ((⟨w, hw⟩ : Fin P.n) : ℕ) from rfl, hL, ofFn_getD]
    have hadj := (h.adj ⟨v, hv⟩ ⟨w, hw⟩).mpr hx
    exact (h.adj _ _).mp hadj.symm
  obtain ⟨fa, htf, hfas, hfa⟩ := tableFaces_spec L g hs (by rw [hgn, hlen]) hr' hnd hloop hsym
  rw [htf]
  simp only
  have hinj := labOf_injective h hs
  have hface := labOf_face h hs hfa
  have hblock := labOf_block h hs
  refine ⟨g.w1Blocks fa, g, fa, rfl, ?_, ?_⟩
  · rw [w1Blocks_iff P g fa (labOf nbr g) hgn hinj hface hblock]
    exact ⟨fun hw => ⟨hd, hw⟩, fun hw => hw.2⟩
  · intro _
    have hD : g.D = g.off.getD P.n 0 := by
      have := hs.fst_size
      rw [hlen] at this
      exact this
    have hD5 : g.D ≤ 75 := by
      have := off_le_five hs (fun v => (hd v).2) (le_refl P.n)
      omega
    have hsurj : ∀ k, k < g.D → ∃ e, labOf nbr g e = k := by
      intro k hk
      obtain ⟨v, i, hv, hi, rfl⟩ := block_decomp (fun v => g.off.getD v 0)
        (fun v => (L.getD v []).length) P.n hs.off_zero (lens_succ hs) k (hD ▸ hk)
      rw [show v = ((⟨v, hv⟩ : Fin P.n) : ℕ) from rfl, hL, ofFn_getD] at hi
      obtain ⟨e, -, he⟩ := exists_labOf h g ⟨v, hv⟩ i hi
      exact ⟨e, he⟩
    let lab : P.G.Dart ≃ Fin g.D := Equiv.ofBijective (fun e => ⟨labOf nbr g e, labOf_lt_D h hs e⟩)
      ⟨fun e e' he => hinj (Fin.ext_iff.mp he), fun k => by
        obtain ⟨e, he⟩ := hsurj k k.2
        exact ⟨e, Fin.ext he⟩⟩
    have hfa256 : ∀ x ∈ fa, x < 256 := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hx
      obtain ⟨e, rfl⟩ := hsurj k (hfas ▸ hk)
      have h1 := hface e
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk] at h1
      simp only [Option.getD_some] at h1
      have := labOf_lt_D h hs (P.R.face e)
      omega
    have hfst256 : ∀ x ∈ g.fst, x < 256 := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hx
      obtain ⟨v, i, hv, hi, hk'⟩ := block_decomp (fun v => g.off.getD v 0)
        (fun v => (L.getD v []).length) P.n hs.off_zero (lens_succ hs) k
        (by have := hs.fst_size; rw [hlen] at this; omega)
      have h1 := hs.fst_at v i (by rw [hlen]; exact hv) hi
      rw [← hk', Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk] at h1
      simp only [Option.getD_some] at h1
      omega
    refine ⟨lab, ⟨fun e => ?_, fun e => ?_⟩⟩
    · show lane (packBytes fa) (labOf nbr g e) = labOf nbr g (P.R.face e)
      unfold lane
      rw [packBytes_lane fa hfa256, hface]
    · show lane (packBytes g.fst) (labOf nbr g e) = (e.fst : ℕ)
      unfold lane
      rw [packBytes_lane g.fst hfst256]
      have := hs.fst_at e.fst ((nbr e.fst).idxOf ((e.snd : ℕ) + 1)) (by rw [hlen]; exact e.fst.2)
        (by rw [hL, ofFn_getD]; exact idxOf_lt_of_dart h e)
      exact this

end Tammes15.W1Filter
