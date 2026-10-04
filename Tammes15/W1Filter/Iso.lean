import Tammes15.Hyps.Transport
import Tammes15.D3lp.W1

namespace Tammes15.W1Filter

open Tammes15 Tammes15.D3lp
open scoped Classical

set_option maxHeartbeats 400000

theorem w1Graph_of_iso {P Q : PlaneGraph} (φ : P.G ≃g Q.G)
    (hφ : ∀ e, dmap φ (P.R.rot e) = Q.R.rot (dmap φ e)) (hP : W1Graph P) : W1Graph Q := by
  intro w
  let v := φ.symm w
  have hinj : Function.Injective (dmap φ) := dmap_injective φ
  have hφv_eq_w : φ v = w := by
    dsimp [v]
    exact φ.apply_symm_apply w

  have h_darts_map : (darts P v).map ⟨dmap φ, hinj⟩ = darts Q w := by
    apply Finset.ext
    intro e
    constructor
    · intro he
      rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
      unfold darts at he'
      simp at he'
      have he'_fst : e'.fst = v := by
        simpa using he'
      unfold darts
      simp [he'_fst, dmap, hφv_eq_w]
    · intro he
      unfold darts at he
      simp at he
      have he_fst : e.fst = w := he
      let e0 := dmap φ.symm e
      have he0_fst : e0.fst = v := by
        dsimp [e0, v, dmap]
        rw [he_fst]
      have h_dmap_symm : dmap φ e0 = e := by
        dsimp [e0]
        apply SimpleGraph.Dart.ext
        simp [dmap, φ.apply_symm_apply]
      apply Finset.mem_map.mpr
      refine ⟨e0, ?_, h_dmap_symm⟩
      unfold darts
      dsimp [v, e0, dmap]
      simp [he_fst]

  have h_fsize_eq (e : P.G.Dart) : fsize Q (dmap φ e) = fsize P e := by
    unfold fsize
    rw [dmap_minimalPeriod P.R Q.R φ hφ e]

  have h_count_eq (k : ℕ) : ((darts Q w).filter (fun e => fsize Q e = k)).card =
      ((darts P v).filter (fun e => fsize P e = k)).card := by
    have h_filter_eq : ((darts P v).map ⟨dmap φ, hinj⟩).filter (fun e => fsize Q e = k) =
        ((darts P v).filter (fun e => fsize P e = k)).map ⟨dmap φ, hinj⟩ := by
      rw [Finset.filter_map]
      congr
      ext e
      simp [h_fsize_eq e]
    calc
      ((darts Q w).filter (fun e => fsize Q e = k)).card
          = (((darts P v).map ⟨dmap φ, hinj⟩).filter (fun e => fsize Q e = k)).card := by rw [← h_darts_map]
      _ = (((darts P v).filter (fun e => fsize P e = k)).map ⟨dmap φ, hinj⟩).card := by rw [h_filter_eq]
      _ = ((darts P v).filter (fun e => fsize P e = k)).card := by simp
  have htri : triCount Q w = triCount P v := by
    unfold triCount; exact h_count_eq 3
  have hrhou : rhoCount Q w = rhoCount P v := by
    unfold rhoCount; exact h_count_eq 4
  have hbig : bigCount Q w = bigCount P v := by
    unfold bigCount
    have h_filter_eq' : ((darts P v).map ⟨dmap φ, hinj⟩).filter (fun e => fsize Q e ≠ 3 ∧ fsize Q e ≠ 4) =
        ((darts P v).filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4)).map ⟨dmap φ, hinj⟩ := by
      rw [Finset.filter_map]
      congr
      ext e
      simp [h_fsize_eq e]
    calc
      ((darts Q w).filter (fun e => fsize Q e ≠ 3 ∧ fsize Q e ≠ 4)).card
          = (((darts P v).map ⟨dmap φ, hinj⟩).filter (fun e => fsize Q e ≠ 3 ∧ fsize Q e ≠ 4)).card := by rw [← h_darts_map]
      _ = (((darts P v).filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4)).map ⟨dmap φ, hinj⟩).card := by rw [h_filter_eq']
      _ = ((darts P v).filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4)).card := by simp
  rw [htri, hrhou, hbig]
  exact hP v

theorem w1Graph_reverse (P : PlaneGraph) :
    W1Graph ⟨P.n, P.G, P.R.reverse⟩ ↔ W1Graph P := by
  have h_periodic : ∀ (x : P.G.Dart), x ∈ Function.periodicPts (P.R.face) := by
    intro x
    have hinj : Function.Injective (P.R.face) := (Equiv.bijective _).injective
    exact Function.Injective.mem_periodicPts hinj x
  have h_face_symm (e : P.G.Dart) : P.R.face e.symm = P.R.rot.symm e := by
    unfold RotSys.face
    simp [SimpleGraph.Dart.symm_symm]
  have h_reverse_minimalPeriod (e : P.G.Dart) :
      Function.minimalPeriod P.R.reverse.face e = Function.minimalPeriod P.R.face (P.R.rot.symm e) := by
    calc
      Function.minimalPeriod P.R.reverse.face e = Function.minimalPeriod P.R.face e.symm := by
        rw [RotSys.reverse_minimalPeriod]
      _ = Function.minimalPeriod P.R.face (P.R.face e.symm) := by
        rw [Function.minimalPeriod_apply (h_periodic e.symm)]
      _ = Function.minimalPeriod P.R.face (P.R.rot.symm e) := by rw [h_face_symm]
  have h_rot_symm_fst (e : P.G.Dart) : (P.R.rot.symm e).fst = e.fst := by
    have := P.R.rot_fst (P.R.rot.symm e)
    simpa [Equiv.apply_symm_apply] using this.symm
  have h_rot_fst (e : P.G.Dart) : (P.R.rot e).fst = e.fst :=
    P.R.rot_fst e

  have h_fsize_rev_eq (e : P.G.Dart) : fsize ⟨P.n, P.G, P.R.reverse⟩ e = fsize P (P.R.rot.symm e) := by
    unfold fsize
    rw [h_reverse_minimalPeriod e]

  have h_count_eq (v : Fin P.n) (size : ℕ) :
      ((darts P v).filter (fun e => fsize ⟨P.n, P.G, P.R.reverse⟩ e = size)).card =
      ((darts P v).filter (fun e => fsize P e = size)).card := by
    have h_filter_eq : (darts P v).filter (fun e => fsize ⟨P.n, P.G, P.R.reverse⟩ e = size) =
        (darts P v).filter (fun e => fsize P (P.R.rot.symm e) = size) := by
      refine Finset.filter_congr ?_
      intro e _
      simp [h_fsize_rev_eq e]
    rw [h_filter_eq]
    apply Finset.card_bij (fun e _ => P.R.rot.symm e)
    · intro e he
      have he_mem := Finset.mem_filter.mp he
      rcases he_mem with ⟨he_darts, he_size⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · unfold darts at he_darts ⊢
        simp at he_darts ⊢
        rw [h_rot_symm_fst, he_darts]
      · exact he_size
    · intro e₁ he₁ e₂ he₂ h_eq
      exact P.R.rot.symm.injective h_eq
    · intro e' he'
      rcases Finset.mem_filter.mp he' with ⟨he_darts, he_size⟩
      refine ⟨P.R.rot e', Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · unfold darts at he_darts ⊢
        simp at he_darts ⊢
        rw [h_rot_fst, he_darts]
      · simp [he_size]
      · simp

  have h_big_count_eq (v : Fin P.n) :
      ((darts P v).filter (fun e => fsize ⟨P.n, P.G, P.R.reverse⟩ e ≠ 3 ∧ fsize ⟨P.n, P.G, P.R.reverse⟩ e ≠ 4)).card =
      ((darts P v).filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4)).card := by
    apply Finset.card_bij (fun e _ => P.R.rot.symm e)
    · intro e he
      rcases Finset.mem_filter.mp he with ⟨he_darts, ⟨he_ne3, he_ne4⟩⟩
      refine Finset.mem_filter.mpr ⟨?_, ⟨?_, ?_⟩⟩
      · unfold darts at he_darts ⊢
        simp at he_darts ⊢
        rw [h_rot_symm_fst, he_darts]
      ·
        rw [← h_fsize_rev_eq e]
        exact he_ne3
      ·
        rw [← h_fsize_rev_eq e]
        exact he_ne4
    · intro e₁ he₁ e₂ he₂ h_eq
      exact P.R.rot.symm.injective h_eq
    · intro e' he'
      rcases Finset.mem_filter.mp he' with ⟨he_darts, ⟨he_ne3, he_ne4⟩⟩
      refine ⟨P.R.rot e', Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · unfold darts at he_darts ⊢
        simp at he_darts ⊢
        rw [h_rot_fst, he_darts]
      ·
        have h1 : fsize ⟨P.n, P.G, P.R.reverse⟩ (P.R.rot e') = fsize P e' := by
          rw [h_fsize_rev_eq (P.R.rot e'), Equiv.symm_apply_apply]
        rw [h1]
        exact ⟨he_ne3, he_ne4⟩
      · simp
  constructor
  · intro h v
    have h_rev := h v
    unfold triCount rhoCount bigCount at h_rev ⊢

    have h_tri : ((darts ⟨P.n, P.G, P.R.reverse⟩ v).filter (fun e => fsize ⟨P.n, P.G, P.R.reverse⟩ e = 3)).card =
        ((darts ⟨P.n, P.G, P.R.reverse⟩ v).filter (fun e => fsize P e = 3)).card := by
      simpa [darts] using h_count_eq v 3
    have h_rho : ((darts ⟨P.n, P.G, P.R.reverse⟩ v).filter (fun e => fsize ⟨P.n, P.G, P.R.reverse⟩ e = 4)).card =
        ((darts ⟨P.n, P.G, P.R.reverse⟩ v).filter (fun e => fsize P e = 4)).card := by
      simpa [darts] using h_count_eq v 4
    have h_big : ((darts ⟨P.n, P.G, P.R.reverse⟩ v).filter (fun e => fsize ⟨P.n, P.G, P.R.reverse⟩ e ≠ 3 ∧ fsize ⟨P.n, P.G, P.R.reverse⟩ e ≠ 4)).card =
        ((darts ⟨P.n, P.G, P.R.reverse⟩ v).filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4)).card := by
      simpa [darts] using h_big_count_eq v

    rw [h_tri, h_rho, h_big] at h_rev

    simpa [darts] using h_rev
  · intro h v
    have h_orig := h v
    unfold triCount rhoCount bigCount at h_orig ⊢

    have h_tri : ((darts P v).filter (fun e => fsize ⟨P.n, P.G, P.R.reverse⟩ e = 3)).card =
        ((darts P v).filter (fun e => fsize P e = 3)).card := h_count_eq v 3
    have h_rho : ((darts P v).filter (fun e => fsize ⟨P.n, P.G, P.R.reverse⟩ e = 4)).card =
        ((darts P v).filter (fun e => fsize P e = 4)).card := h_count_eq v 4
    have h_big : ((darts P v).filter (fun e => fsize ⟨P.n, P.G, P.R.reverse⟩ e ≠ 3 ∧ fsize ⟨P.n, P.G, P.R.reverse⟩ e ≠ 4)).card =
        ((darts P v).filter (fun e => fsize P e ≠ 3 ∧ fsize P e ≠ 4)).card := h_big_count_eq v
    rw [← h_tri, ← h_rho, ← h_big] at h_orig

    simpa [darts] using h_orig

theorem w1Graph_of_isoRefl {P Q : PlaneGraph} (h : P.R.IsoRefl Q.R)
    (hP : W1Graph P) : W1Graph Q := by
  rcases h with ⟨φ, hφ | hφ⟩
  · exact w1Graph_of_iso φ hφ hP
  · let Q' : PlaneGraph := ⟨Q.n, Q.G, Q.R.reverse⟩
    have hφ' : ∀ e, dmap φ (P.R.rot e) = Q'.R.rot (dmap φ e) := by
      intro e
      simpa [Q', RotSys.reverse] using hφ e
    have hQ' : W1Graph Q' := w1Graph_of_iso φ hφ' hP
    exact (w1Graph_reverse Q).mp hQ'

end Tammes15.W1Filter
