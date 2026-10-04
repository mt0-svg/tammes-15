import Tammes15.W1Filter.Bytes

set_option maxHeartbeats 400000

namespace Tammes15.W1Filter

open Tammes15 Tammes15.D3lp
open scoped Classical

theorem block_decomp (off len : ℕ → ℕ) (n : ℕ) (h0 : off 0 = 0)
    (hs : ∀ v, v < n → off (v + 1) = off v + len v) (k : ℕ) (hk : k < off n) :
    ∃ v i, v < n ∧ i < len v ∧ k = off v + i := by
  induction n with
  | zero =>
      rw [h0] at hk
      omega
  | succ n ih =>
      have hsn : off (n + 1) = off n + len n := hs n (Nat.lt_succ_self n)
      rw [hsn] at hk
      by_cases h : k < off n
      · rcases ih (fun v hv => hs v (Nat.lt_of_lt_of_le hv (Nat.le_succ n))) h with ⟨v, i, hv, hi, heq⟩
        exact ⟨v, i, Nat.lt_of_lt_of_le hv (Nat.le_succ n), hi, heq⟩
      · have h_lt : k < off n + len n := hk
        refine ⟨n, k - off n, Nat.lt_succ_self n, ?_, ?_⟩
        · omega
        · omega

theorem block_unique (off len : ℕ → ℕ) (n : ℕ) (hs : ∀ v, v < n → off (v + 1) = off v + len v)
    {v v' i i' : ℕ} (hv : v < n) (hv' : v' < n) (hi : i < len v) (hi' : i' < len v')
    (h : off v + i = off v' + i') : v = v' ∧ i = i' := by

  have hmono : ∀ a b, a ≤ b → b ≤ n → off a ≤ off b := by
    intro a b hle hbn
    induction' hle with b hle ih
    · rfl
    · have hb_lt_n : b < n :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hbn
      have hb_le_n : b ≤ n := Nat.le_of_lt hb_lt_n
      have hstep := hs b hb_lt_n

      have hle_step : off b ≤ off (b + 1) := by omega
      exact Nat.le_trans (ih hb_le_n) hle_step

  have hsum : ∀ v w, v < w → w ≤ n → off v + len v ≤ off w := by
    intro v w hlt hwn
    have hv_lt_n : v < n := Nat.lt_of_lt_of_le hlt hwn
    have hstep := hs v hv_lt_n
    have hmono' : off (v + 1) ≤ off w :=
      hmono (v + 1) w (Nat.succ_le_of_lt hlt) hwn
    omega
  by_cases hlt : v < v'
  ·
    have h_ineq : off v + len v ≤ off v' := hsum v v' hlt (Nat.le_of_lt hv')
    have h_lt : off v + i < off v + len v := by omega
    have h_lt' : off v + len v ≤ off v' + i' := by omega
    omega
  ·
    by_cases hlt' : v' < v
    ·
      have h_ineq : off v' + len v' ≤ off v := hsum v' v hlt' (Nat.le_of_lt hv)
      have h_lt : off v' + i' < off v' + len v' := by omega
      have h_lt' : off v' + len v' ≤ off v + i := by omega
      omega
    ·
      have heq : v = v' := by
        apply Nat.le_antisymm
        · exact Nat.le_of_not_gt hlt'
        · exact Nat.le_of_not_gt hlt
      subst heq
      have heq_i : i = i' := by omega
      exact And.intro rfl heq_i

theorem posGo_spec (g : Darts) (len k : ℕ) (t : Array ℕ) (ht : t.size = g.n * g.n)
    (hfst : ∀ j, k ≤ j → j < k + len → g.fst.getD j 0 < g.n)
    (hsnd : ∀ j, k ≤ j → j < k + len → g.snd.getD j 0 < g.n)
    (hne : ∀ j, k ≤ j → j < k + len → g.snd.getD j 0 ≠ g.fst.getD j 0)
    (hinj : ∀ j j', k ≤ j → j < k + len → k ≤ j' → j' < k + len →
      g.fst.getD j 0 = g.fst.getD j' 0 → g.snd.getD j 0 = g.snd.getD j' 0 → j = j')
    (hz : ∀ j, k ≤ j → j < k + len → t.getD (g.fst.getD j 0 * g.n + g.snd.getD j 0) 0 = 0) :
    ∃ t', posGo g len k t = some t' ∧ t'.size = t.size ∧
      (∀ j, k ≤ j → j < k + len → t'.getD (g.fst.getD j 0 * g.n + g.snd.getD j 0) 0 = j + 1) ∧
      ∀ x, (∀ j, k ≤ j → j < k + len → g.fst.getD j 0 * g.n + g.snd.getD j 0 ≠ x) →
        t'.getD x 0 = t.getD x 0 := by
  induction len generalizing k t with
  | zero => exact ⟨t, rfl, rfl, fun j h1 h2 => by omega, fun x _ => rfl⟩
  | succ len ih =>
    have key : ∀ a b c d : ℕ, b < g.n → d < g.n → a * g.n + b = c * g.n + d → a = c ∧ b = d := by
      intro a b c d hb hd h
      have h1 : a = c := by
        by_contra hac
        rcases Nat.lt_or_gt_of_ne hac with hlt | hlt
        · have : (a + 1) * g.n ≤ c * g.n := Nat.mul_le_mul_right g.n hlt
          nlinarith
        · have : (c + 1) * g.n ≤ a * g.n := Nat.mul_le_mul_right g.n hlt
          nlinarith
      subst h1
      omega
    have hk0 : k ≤ k := le_rfl
    have hk1 : k < k + (len + 1) := by omega
    have hpk : g.fst.getD k 0 * g.n + g.snd.getD k 0 < t.size := by
      rw [ht]
      have h1 := hfst k hk0 hk1
      have h2 := hsnd k hk0 hk1
      have : (g.fst.getD k 0 + 1) * g.n ≤ g.n * g.n := Nat.mul_le_mul_right g.n h1
      nlinarith
    have hstep : posGo g (len + 1) k t =
        posGo g len (k + 1) (t.set! (g.fst.getD k 0 * g.n + g.snd.getD k 0) (k + 1)) := by
      simp only [posGo]
      rw [if_pos]
      rw [hz k hk0 hk1]
      have a := hsnd k hk0 hk1
      have b := hne k hk0 hk1
      simp only [Array.getD_eq_getD_getElem?] at a b
      simp [a, b]
    have hne_pair : ∀ j, k + 1 ≤ j → j < k + 1 + len →
        g.fst.getD k 0 * g.n + g.snd.getD k 0 ≠ g.fst.getD j 0 * g.n + g.snd.getD j 0 := by
      intro j h1 h2 he
      obtain ⟨e1, e2⟩ := key _ _ _ _ (hsnd k hk0 hk1) (hsnd j (by omega) (by omega)) he
      have := hinj k j hk0 hk1 (by omega) (by omega) e1 e2
      omega
    obtain ⟨t', h1, h2, h3, h4⟩ :=
      ih (k + 1) (t.set! (g.fst.getD k 0 * g.n + g.snd.getD k 0) (k + 1)) (by simp [ht])
        (fun j a b => hfst j (by omega) (by omega)) (fun j a b => hsnd j (by omega) (by omega))
        (fun j a b => hne j (by omega) (by omega))
        (fun j j' a b c d => hinj j j' (by omega) (by omega) (by omega) (by omega))
        (fun j a b => by
          rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
            Array.getElem?_setIfInBounds_ne (hne_pair j a b)]
          simpa using hz j (by omega) (by omega))
    refine ⟨t', by rw [hstep, h1], by rw [h2]; simp, ?_, ?_⟩
    · intro j hj1 hj2
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
      · rw [h4 _ (fun j' a b => (hne_pair j' a b).symm), Array.set!_eq_setIfInBounds,
          Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hpk]
        rfl
      · exact h3 j (by omega) (by omega)
    · intro x hx
      rw [h4 x (fun j a b => hx j (by omega) (by omega)), Array.set!_eq_setIfInBounds,
        Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (hx k hk0 hk1),
        ← Array.getD_eq_getD_getElem?]

private lemma faceGo_getD_lt (g : Darts) (t : Array ℕ) : ∀ (len k : ℕ) (acc : Array ℕ), ∀ i, i < acc.size →
    (faceGo g t len k acc).getD i 0 = acc.getD i 0 := by
  intro len k acc i hi
  induction len generalizing k acc with
  | zero => rfl
  | succ len ih =>
    unfold faceGo
    have hi' : i < (acc.push (g.off.getD (g.snd.getD k 0) 0 +
      (t.getD (g.snd.getD k 0 * g.n + g.fst.getD k 0) 0 - 1 -
        g.off.getD (g.snd.getD k 0) 0 + g.deg (g.snd.getD k 0) - 1) %
        g.deg (g.snd.getD k 0))).size := by
      rw [Array.size_push]
      omega
    have h_eq := ih (k + 1) (acc.push (g.off.getD (g.snd.getD k 0) 0 +
      (t.getD (g.snd.getD k 0 * g.n + g.fst.getD k 0) 0 - 1 -
        g.off.getD (g.snd.getD k 0) 0 + g.deg (g.snd.getD k 0) - 1) %
        g.deg (g.snd.getD k 0))) hi'
    rw [h_eq]
    have h_not_lt : ¬ acc.size < i := by omega
    simp [Array.getD, hi, h_not_lt, Array.getElem_push_lt hi]

theorem faceGo_spec (g : Darts) (t : Array ℕ) (len k : ℕ) (acc : Array ℕ) :
    (faceGo g t len k acc).size = acc.size + len ∧
      ∀ j, j < len → (faceGo g t len k acc).getD (acc.size + j) 0 =
        g.off.getD (g.snd.getD (k + j) 0) 0 +
          (t.getD (g.snd.getD (k + j) 0 * g.n + g.fst.getD (k + j) 0) 0 - 1 -
              g.off.getD (g.snd.getD (k + j) 0) 0 + g.deg (g.snd.getD (k + j) 0) - 1) %
            g.deg (g.snd.getD (k + j) 0) := by
  induction len generalizing k acc with
  | zero =>
    simp [faceGo]
  | succ len ih =>

    set y := g.off.getD (g.snd.getD k 0) 0 +
      (t.getD (g.snd.getD k 0 * g.n + g.fst.getD k 0) 0 - 1 -
        g.off.getD (g.snd.getD k 0) 0 + g.deg (g.snd.getD k 0) - 1) %
        g.deg (g.snd.getD k 0) with hy_def

    have h_faceGo_succ : faceGo g t (len + 1) k acc = faceGo g t len (k + 1) (acc.push y) := by
      simp [faceGo, y]
    rw [h_faceGo_succ]
    have ih_at_succ := ih (k + 1) (acc.push y)
    rcases ih_at_succ with ⟨ih_size, ih_val⟩
    have h_size_push : (acc.push y).size = acc.size + 1 := Array.size_push y
    have h_size : (faceGo g t len (k + 1) (acc.push y)).size = acc.size + (len + 1) := by
      rw [ih_size, h_size_push]
      omega
    have h_val : ∀ j, j < len + 1 → (faceGo g t len (k + 1) (acc.push y)).getD (acc.size + j) 0 =
      g.off.getD (g.snd.getD (k + j) 0) 0 +
        (t.getD (g.snd.getD (k + j) 0 * g.n + g.fst.getD (k + j) 0) 0 - 1 -
            g.off.getD (g.snd.getD (k + j) 0) 0 + g.deg (g.snd.getD (k + j) 0) - 1) %
          g.deg (g.snd.getD (k + j) 0) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with (rfl | hj_pos)
      ·
        have h_lt : acc.size < (acc.push y).size := by
          rw [h_size_push]
          omega
        have h_get := faceGo_getD_lt g t len (k + 1) (acc.push y) acc.size h_lt

        simpa [add_zero, Array.getD, y] using h_get
      ·
        have h_j' : ∃ j', j = j' + 1 := Nat.exists_eq_succ_of_ne_zero hj_pos.ne'
        rcases h_j' with ⟨j', rfl⟩
        have hj'_lt_len : j' < len := by omega
        have h_idx : acc.size + (j' + 1) = (acc.push y).size + j' := by
          rw [h_size_push]; omega
        rw [h_idx]
        rw [ih_val j' hj'_lt_len]
        ring_nf
    exact And.intro h_size h_val

section TableSpec

variable {L : List (List ℕ)} {g : Darts}

theorem DecSpec.off_mono (hs : DecSpec L g) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ L.length) :
    g.off.getD a 0 ≤ g.off.getD b 0 := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    have h1 := hs.off_succ m (by omega)
    have h2 := ih (by omega)
    omega

theorem DecSpec.D_eq (hs : DecSpec L g) : g.D = g.off.getD L.length 0 := hs.fst_size

theorem DecSpec.lt_D (hs : DecSpec L g) {v i : ℕ} (hv : v < L.length)
    (hi : i < (L.getD v []).length) : g.off.getD v 0 + i < g.D := by
  have h1 := hs.off_succ v hv
  have h2 := hs.off_mono (a := v + 1) (b := L.length) hv le_rfl
  rw [hs.D_eq]
  omega

theorem DecSpec.decomp (hs : DecSpec L g) {k : ℕ} (hk : k < g.D) :
    ∃ v i, v < L.length ∧ i < (L.getD v []).length ∧ k = g.off.getD v 0 + i :=
  block_decomp (fun v => g.off.getD v 0) (fun v => (L.getD v []).length) L.length hs.off_zero
    hs.off_succ k (hs.D_eq ▸ hk)

theorem DecSpec.deg (hs : DecSpec L g) {v : ℕ} (hv : v < L.length) :
    g.deg v = (L.getD v []).length := by
  unfold Darts.deg
  rw [hs.off_succ v hv]
  omega

end TableSpec

theorem entry_mem {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem tableFaces_spec (L : List (List ℕ)) (g : Darts) (hs : DecSpec L g) (hn : g.n = L.length)
    (hr : ∀ v, v < L.length → ∀ x ∈ L.getD v [], 1 ≤ x ∧ x ≤ L.length)
    (hnd : ∀ v, v < L.length → (L.getD v []).Nodup)
    (hloop : ∀ v, v < L.length → v + 1 ∉ L.getD v [])
    (hsym : ∀ v w, v < L.length → w < L.length → w + 1 ∈ L.getD v [] → v + 1 ∈ L.getD w []) :
    ∃ fa, g.tableFaces = some fa ∧ fa.size = g.D ∧
      ∀ v i, v < L.length → i < (L.getD v []).length →
        fa.getD (g.off.getD v 0 + i) 0 =
          g.off.getD ((L.getD v []).getD i 0 - 1) 0 +
            ((L.getD ((L.getD v []).getD i 0 - 1) []).idxOf (v + 1) +
                (L.getD ((L.getD v []).getD i 0 - 1) []).length - 1) %
              (L.getD ((L.getD v []).getD i 0 - 1) []).length := by
  have hD := hs.D_eq
  have hx : ∀ v i, v < L.length → i < (L.getD v []).length →
      1 ≤ (L.getD v []).getD i 0 ∧ (L.getD v []).getD i 0 ≤ L.length :=
    fun v i hv hi => hr v hv _ (entry_mem hi)
  have hmem : ∀ v i, v < L.length → i < (L.getD v []).length →
      (L.getD v []).getD i 0 - 1 + 1 ∈ L.getD v [] := fun v i hv hi => by
    rw [Nat.sub_add_cancel (hx v i hv hi).1]
    exact entry_mem hi
  have hfst : ∀ k, k < g.D → g.fst.getD k 0 < g.n := by
    intro k hk
    obtain ⟨v, i, hv, hi, rfl⟩ := hs.decomp hk
    rw [hs.fst_at v i hv hi, hn]
    exact hv
  have hsnd : ∀ k, k < g.D → g.snd.getD k 0 < g.n := by
    intro k hk
    obtain ⟨v, i, hv, hi, rfl⟩ := hs.decomp hk
    rw [hs.snd_at v i hv hi, hn]
    have := hx v i hv hi
    omega
  have hne : ∀ k, k < g.D → g.snd.getD k 0 ≠ g.fst.getD k 0 := by
    intro k hk
    obtain ⟨v, i, hv, hi, rfl⟩ := hs.decomp hk
    rw [hs.snd_at v i hv hi, hs.fst_at v i hv hi]
    intro h
    have := hmem v i hv hi
    rw [h] at this
    exact hloop v hv this
  have hinj : ∀ j j', j < g.D → j' < g.D → g.fst.getD j 0 = g.fst.getD j' 0 →
      g.snd.getD j 0 = g.snd.getD j' 0 → j = j' := by
    intro j j' hj hj' h1 h2
    obtain ⟨v, i, hv, hi, rfl⟩ := hs.decomp hj
    obtain ⟨v', i', hv', hi', rfl⟩ := hs.decomp hj'
    rw [hs.fst_at v i hv hi, hs.fst_at v' i' hv' hi'] at h1
    subst h1
    rw [hs.snd_at v i hv hi, hs.snd_at v i' hv' hi'] at h2
    have e : (L.getD v []).getD i 0 = (L.getD v []).getD i' 0 := by
      have := hx v i hv hi
      have := hx v i' hv hi'
      omega
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at e
    rw [(hnd v hv).getElem_inj_iff.mp e]
  obtain ⟨t, ht, -, htv, -⟩ := posGo_spec g g.D 0 (Array.replicate (g.n * g.n) 0) (by simp)
    (fun j _ hj => hfst j (by omega)) (fun j _ hj => hsnd j (by omega))
    (fun j _ hj => hne j (by omega)) (fun j j' _ hj _ hj' => hinj j j' (by omega) (by omega))
    (fun j _ _ => by unfold Array.getD; split <;> simp)
  have hrev : ∀ v w, v < L.length → w < L.length → w + 1 ∈ L.getD v [] →
      (L.getD w []).idxOf (v + 1) < (L.getD w []).length ∧
        t.getD (w * g.n + v) 0 = g.off.getD w 0 + (L.getD w []).idxOf (v + 1) + 1 := by
    intro v w hv hw hm
    have hp := List.idxOf_lt_length_of_mem (hsym v w hv hw hm)
    refine ⟨hp, ?_⟩
    have h1 := hs.fst_at w _ hw hp
    have h2 : g.snd.getD (g.off.getD w 0 + (L.getD w []).idxOf (v + 1)) 0 = v := by
      rw [hs.snd_at w _ hw hp, List.getD_eq_getElem _ _ hp, List.getElem_idxOf hp]
      simp
    have h3 := htv (g.off.getD w 0 + (L.getD w []).idxOf (v + 1)) (Nat.zero_le _)
      (by have := hs.lt_D hw hp; omega)
    rw [h1, h2] at h3
    exact h3
  have hvalid : g.validT t = true := by
    have h4 : allFrom (fun k => t.getD (g.snd.getD k 0 * g.n + g.fst.getD k 0) 0 != 0) g.D 0 =
        true := by
      rw [allFrom_iff]
      intro k _ hk
      obtain ⟨v, i, hv, hi, rfl⟩ := hs.decomp (k := k) (by omega)
      rw [hs.snd_at v i hv hi, hs.fst_at v i hv hi]
      have := hx v i hv hi
      rw [(hrev v _ hv (by omega) (hmem v i hv hi)).2]
      simp
    unfold Darts.validT
    rw [h4]
    simp [hs.off_size, hn, hs.snd_size, ← hD]
  have hface := faceGo_spec g t g.D 0 (Array.mkEmpty g.D)
  have h0 : (Array.mkEmpty g.D : Array ℕ).size = 0 := by simp
  refine ⟨faceGo g t g.D 0 (Array.mkEmpty g.D), ?_, ?_, ?_⟩
  · unfold Darts.tableFaces Darts.posTable
    rw [ht]
    simp [hvalid]
  · rw [hface.1, h0, Nat.zero_add]
  · intro v i hv hi
    have := hx v i hv hi
    have hk := hface.2 (g.off.getD v 0 + i) (hs.lt_D hv hi)
    simp only [h0, Nat.zero_add] at hk
    rw [hk, hs.snd_at v i hv hi, hs.fst_at v i hv hi]
    obtain ⟨hp, hr'⟩ := hrev v _ hv (by omega) (hmem v i hv hi)
    rw [hr', hs.deg (by omega)]
    generalize (L.getD ((L.getD v []).getD i 0 - 1) []).idxOf (v + 1) = p at hp ⊢
    generalize g.off.getD ((L.getD v []).getD i 0 - 1) 0 = o
    rw [show o + p + 1 - 1 - o = p by omega]

theorem period_lab (P : PlaneGraph) (fa : Array ℕ) (lab : P.G.Dart → ℕ)
    (hface : ∀ e, fa.getD (lab e) 0 = lab (P.R.face e)) (hinj : Function.Injective lab)
    (e : P.G.Dart) :
    (periodGoA fa (lab e) 6 (lab e) 1 = 3 ↔ fsize P e = 3) ∧
      (periodGoA fa (lab e) 6 (lab e) 1 = 4 ↔ fsize P e = 4) := by
  let f := fun k : ℕ => fa.getD k 0
  let F := P.R.face
  have hf_iter : ∀ t, f^[t] (lab e) = lab (F^[t] e) := by
    intro t
    induction' t with t ih
    · rfl
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      dsimp [f]
      rw [hface (F^[t] e)]
  have hF_per : ∀ x : P.G.Dart, x ∈ Function.periodicPts F := by
    intro x
    exact F.injective.mem_periodicPts x
  have hF_minpos : 0 < Function.minimalPeriod F e :=
    Function.minimalPeriod_pos_of_mem_periodicPts (hF_per e)
  have h_period_eq_iff (m : ℕ) (hm : 0 < m) (hm6 : m ≤ 6) :
      period f (lab e) = m ↔ Function.minimalPeriod F e = m := by
    constructor
    · intro hper
      have hspec := period_spec f (lab e) m hper hm
      rcases hspec with ⟨hret, hfirst⟩
      have hFe : F^[m] e = e := by
        rw [← hinj.eq_iff, ← hf_iter m, hret]
      have hF_first : ∀ t, 0 < t → t < m → F^[t] e ≠ e := by
        intro t ht0 htm
        have hneq : f^[t] (lab e) ≠ lab e := hfirst t ht0 htm
        rw [hf_iter t] at hneq
        intro heq
        apply hneq
        rw [heq]
      have hF_per_m : Function.IsPeriodicPt F m e := by
        rw [Function.IsPeriodicPt, Function.IsFixedPt]
        exact hFe
      have hmin_le : Function.minimalPeriod F e ≤ m :=
        Function.IsPeriodicPt.minimalPeriod_le hm hF_per_m
      have hmin_ge : m ≤ Function.minimalPeriod F e := by
        by_contra! hlt
        have h_contra := hF_first (Function.minimalPeriod F e) hF_minpos hlt
        rw [Function.iterate_minimalPeriod] at h_contra
        exact h_contra rfl
      exact Nat.le_antisymm hmin_le hmin_ge
    · intro hmin
      have hFe : F^[m] e = e := by
        rw [← hmin]
        exact Function.iterate_minimalPeriod (f := F) (x := e)
      have hF_first : ∀ t, 0 < t → t < m → F^[t] e ≠ e := by
        intro t ht0 htm
        have htm' : t < Function.minimalPeriod F e := by
          rw [hmin]
          exact htm
        have h_not_per : ¬ Function.IsPeriodicPt F t e :=
          Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega) htm'
        rw [Function.IsPeriodicPt] at h_not_per
        exact h_not_per
      have hf_ret : f^[m] (lab e) = lab e := by
        rw [hf_iter m, hFe]
      have hf_first : ∀ t, 0 < t → t < m → f^[t] (lab e) ≠ lab e := by
        intro t ht0 htm
        rw [hf_iter t]
        intro heq
        apply hF_first t ht0 htm
        exact hinj heq
      exact period_eq_of_first_return f (lab e) m hm hm6 hf_ret hf_first
  have h3pos : 0 < 3 := by norm_num
  have h4pos : 0 < 4 := by norm_num
  have h3le6 : 3 ≤ 6 := by norm_num
  have h4le6 : 4 ≤ 6 := by norm_num
  have h_eq_period : periodGoA fa (lab e) 6 (lab e) 1 = period f (lab e) := by
    rw [periodGoA_eq, period]
  rw [h_eq_period]
  exact And.intro (h_period_eq_iff 3 h3pos h3le6) (h_period_eq_iff 4 h4pos h4le6)

theorem w1Blocks_iff (P : PlaneGraph) (g : Darts) (fa : Array ℕ) (lab : P.G.Dart → ℕ)
    (hn : g.n = P.n) (hinj : Function.Injective lab)
    (hface : ∀ e, fa.getD (lab e) 0 = lab (P.R.face e))
    (hblock : ∀ v : Fin P.n,
      Finset.Ico (g.off.getD v 0) (g.off.getD v 0 + g.deg v) = (darts P v).image lab) :
    g.w1Blocks fa = true ↔ W1Graph P := by

  have hw1Blocks_def : g.w1Blocks fa = allFrom (fun (v : ℕ) =>
    let (a, q, p) := countBlock fa (g.deg v) (g.off.getD v 0) 0 0 0
    w1Type a q p) g.n 0 := rfl
  rw [hw1Blocks_def]
  rw [allFrom_iff]

  have h0add : (0 : ℕ) + g.n = g.n := by omega
  rw [h0add]

  have h_vertex (v : Fin P.n) : (let (a, q, p) := countBlock fa (g.deg (v : ℕ)) (g.off.getD (v : ℕ) 0) 0 0 0; w1Type a q p) = true ↔ W1Type (triCount P v) (rhoCount P v) (bigCount P v) := by

    have hcount := countBlock_eq fa (g.deg (v : ℕ)) (g.off.getD (v : ℕ) 0) 0 0 0

    have h_simp : (let (a, q, p) := countBlock fa (g.deg (v : ℕ)) (g.off.getD (v : ℕ) 0) 0 0 0; w1Type a q p) =
      w1Type (0 + ((Finset.Ico (g.off.getD (v : ℕ) 0) (g.off.getD (v : ℕ) 0 + g.deg (v : ℕ))).filter (fun j => periodGoA fa j 6 j 1 = 3)).card)
             (0 + ((Finset.Ico (g.off.getD (v : ℕ) 0) (g.off.getD (v : ℕ) 0 + g.deg (v : ℕ))).filter (fun j => periodGoA fa j 6 j 1 = 4)).card)
             (0 + ((Finset.Ico (g.off.getD (v : ℕ) 0) (g.off.getD (v : ℕ) 0 + g.deg (v : ℕ))).filter
                (fun j => periodGoA fa j 6 j 1 ≠ 3 ∧ periodGoA fa j 6 j 1 ≠ 4)).card) := by
      rw [hcount]
    rw [h_simp]

    simp only [Nat.zero_add]

    have hblock_v := hblock v

    have hIco_eq : Finset.Ico (g.off.getD (v : ℕ) 0) (g.off.getD (v : ℕ) 0 + g.deg (v : ℕ)) = (darts P v).image lab := hblock_v

    have hA : ((Finset.Ico (g.off.getD (v : ℕ) 0) (g.off.getD (v : ℕ) 0 + g.deg (v : ℕ))).filter (fun j => periodGoA fa j 6 j 1 = 3)).card =
      ((darts P v).filter (fun e => fsize P e = 3)).card := by
      rw [hIco_eq]
      rw [Finset.filter_image]
      rw [Finset.card_image_of_injective _ hinj]

      refine congrArg Finset.card ?_
      refine Finset.filter_congr ?_
      intro e he
      exact (period_lab P fa lab hface hinj e).1
    have hQ : ((Finset.Ico (g.off.getD (v : ℕ) 0) (g.off.getD (v : ℕ) 0 + g.deg (v : ℕ))).filter (fun j => periodGoA fa j 6 j 1 = 4)).card =
      ((darts P v).filter (fun e => fsize P e = 4)).card := by
      rw [hIco_eq]
      rw [Finset.filter_image]
      rw [Finset.card_image_of_injective _ hinj]
      refine congrArg Finset.card ?_
      refine Finset.filter_congr ?_
      intro e he
      exact (period_lab P fa lab hface hinj e).2
    have hP : ((Finset.Ico (g.off.getD (v : ℕ) 0) (g.off.getD (v : ℕ) 0 + g.deg (v : ℕ))).filter
        (fun j => periodGoA fa j 6 j 1 ≠ 3 ∧ periodGoA fa j 6 j 1 ≠ 4)).card =
      ((darts P v).filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4)).card := by
      rw [hIco_eq]
      rw [Finset.filter_image]
      rw [Finset.card_image_of_injective _ hinj]

      refine congrArg Finset.card ?_
      refine Finset.filter_congr ?_
      intro e he
      have ⟨h3, h4⟩ := period_lab P fa lab hface hinj e
      have hne3 : (periodGoA fa (lab e) 6 (lab e) 1 ≠ 3) ↔ (fsize P e ≠ 3) := not_iff_not.mpr h3
      have hne4 : (periodGoA fa (lab e) 6 (lab e) 1 ≠ 4) ↔ (fsize P e ≠ 4) := not_iff_not.mpr h4
      exact (hne3.and hne4)

    rw [hA, hQ, hP]

    unfold triCount rhoCount bigCount

    rw [w1Type_iff]

  constructor
  ·
    intro hall
    intro v
    have h0le : 0 ≤ (v : ℕ) := Nat.zero_le _
    have hklt : (v : ℕ) < g.n := by rw [hn]; exact v.2
    have htrue := hall (v : ℕ) h0le hklt

    rw [h_vertex v] at htrue
    exact htrue
  ·
    intro hW1
    intro k h0le hklt
    have hkltPn : k < P.n := by rwa [← hn]
    let v : Fin P.n := ⟨k, hkltPn⟩
    have hW1v := hW1 v

    have hgoal := (h_vertex v).mpr hW1v
    simpa [v] using hgoal

end Tammes15.W1Filter
