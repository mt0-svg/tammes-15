import Tammes15.Attained.Data

/-!
# Inner products and norms of the frame points

`pt b u k` has coordinates `ptN b u k c / 225008`, so its inner products and norms are read off the
numerators: `inner_pt`, `norm_pt`, and the forms `inner_eq_of_num`, `inner_le_of_num` in which the
generated lemmas `ct_k1_k2` and `sp_k1_k2` are applied. `sep_of_lt` reduces the separation of a
frame to its ordered pairs.
-/

set_option maxHeartbeats 400000

open scoped RealInnerProductSpace

namespace Tammes15.Attained

theorem inner_pt (b u : ℝ) (k1 k2 : Fin 18) :
    ⟪pt b u k1, pt b u k2⟫ = (ptN b u k1 0 * ptN b u k2 0 + ptN b u k1 1 * ptN b u k2 1 +
      ptN b u k1 2 * ptN b u k2 2) / (225008 * 225008) := by
  unfold pt
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem norm_pt (b u : ℝ) (k : Fin 18)
    (h : ptN b u k 0 * ptN b u k 0 + ptN b u k 1 * ptN b u k 1 + ptN b u k 2 * ptN b u k 2 =
      225008 * 225008) : ‖pt b u k‖ = 1 := by
  have h1 : ⟪pt b u k, pt b u k⟫ = 1 := by
    rw [inner_pt, h]
    norm_num
  have h2 : ‖pt b u k‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

theorem inner_eq_of_num (b u : ℝ) (k1 k2 : Fin 18)
    (h : ptN b u k1 0 * ptN b u k2 0 + ptN b u k1 1 * ptN b u k2 1 + ptN b u k1 2 * ptN b u k2 2 =
      (225008 * 225008 : ℝ) * u) : ⟪pt b u k1, pt b u k2⟫ = u := by
  rw [inner_pt, h]
  have hpos : (225008 * 225008 : ℝ) ≠ 0 := by norm_num
  field_simp [hpos]

theorem inner_le_of_num (b u : ℝ) (k1 k2 : Fin 18)
    (h : ptN b u k1 0 * ptN b u k2 0 + ptN b u k1 1 * ptN b u k2 1 + ptN b u k1 2 * ptN b u k2 2 ≤
      (225008 * 225008 : ℝ) * u) : ⟪pt b u k1, pt b u k2⟫ ≤ u := by
  rw [inner_pt, div_le_iff₀ (by norm_num)]
  linarith

theorem sep_of_lt (b u : ℝ) (keep : Fin 15 → Fin 18)
    (h : ∀ i j : Fin 15, i < j → ⟪pt b u (keep i), pt b u (keep j)⟫ ≤ u) :
    ∀ i j : Fin 15, i ≠ j → ⟪pt b u (keep i), pt b u (keep j)⟫ ≤ u := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact h i j h1
  · rw [real_inner_comm]
    exact h j i h1

end Tammes15.Attained
