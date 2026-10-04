import Tammes15.D3Prog.L2.Kinds1

namespace D3Prog.L2

open Real Tammes15 D3Ck2Spec

set_option linter.unusedVariables false

theorem K14_iso_base_a (G : Prop) (UL UH DL DH : ℤ) (SDL SDH HL HH SHL SHH PL PH : ℤ) (ynn : ℕ)
    (hsd : G → (0 ≤ DL ∧ DH ≤ 843314857) ∧ ∀ r : ℝ, Enc DL DH r → Enc SDL SDH (sin r))
    (hh : ∀ r : ℝ, Enc UL UH r → Enc HL HH (r / 2))
    (hsh : G → (0 ≤ HL ∧ HH ≤ 843314857) ∧ ∀ r : ℝ, Enc HL HH r → Enc SHL SHH (sin r))
    (hp : G → ∀ r s : ℝ, Enc SDL SDH r → Enc SHL SHH s → Enc PL PH (r * s)) (hynn : ynn = 1 ↔ -1 < PL)
    (hck : G → ynn = 1) :
    G → ∀ d u : ℝ, Enc DL DH d → Enc UL UH u → AF true PL PH (ebase d u) := by
  intro hG d u hd hu
  have hynn1 : ynn = 1 := hck hG
  have hPL_gt_neg_one : -1 < PL := (hynn.mp hynn1)
  have hPL_nonneg : 0 ≤ PL := by omega
  have hsin_d := (hsd hG).2 d hd
  have hhalf_u := hh u hu
  have hsin_half_u := (hsh hG).2 (u / 2) hhalf_u
  have hx := hp hG (sin d) (sin (u / 2)) hsin_d hsin_half_u
  set x := sin d * sin (u / 2) with hxdef
  have hx_enc : Enc PL PH x := hx
  rcases hx_enc with ⟨hx_lo, hx_hi⟩
  have hx_nonneg : 0 ≤ x := by
    have hPL_nonneg' : (0 : ℝ) ≤ (PL : ℝ) := by exact_mod_cast hPL_nonneg
    have hpos : (0 : ℝ) ≤ 2 ^ 28 * x := by linarith
    have h2pow_pos : (0 : ℝ) < 2 ^ 28 := by norm_num
    nlinarith
  have hx_le_one : x ≤ 1 := by
    have h_abs_d : |sin d| ≤ 1 := Real.abs_sin_le_one d
    have h_abs_half : |sin (u / 2)| ≤ 1 := Real.abs_sin_le_one (u / 2)
    have h_sin_d_le_one : sin d ≤ 1 := by linarith [abs_le.mp h_abs_d]
    have h_sin_d_ge_neg_one : -1 ≤ sin d := by linarith [abs_le.mp h_abs_d]
    have h_sin_half_le_one : sin (u / 2) ≤ 1 := by linarith [abs_le.mp h_abs_half]
    have h_sin_half_ge_neg_one : -1 ≤ sin (u / 2) := by linarith [abs_le.mp h_abs_half]
    by_cases h_sin_d_nonneg : 0 ≤ sin d
    · by_cases h_sin_half_nonneg : 0 ≤ sin (u / 2)
      ·
        nlinarith
      ·
        have h_sin_half_nonpos : sin (u / 2) ≤ 0 := by linarith
        have hx_nonpos : x ≤ 0 := by nlinarith
        nlinarith
    ·
      have h_sin_d_nonpos : sin d ≤ 0 := by linarith
      by_cases h_sin_half_nonneg : 0 ≤ sin (u / 2)
      ·
        have hx_nonpos : x ≤ 0 := by nlinarith
        nlinarith
      ·
        have h_sin_half_nonpos : sin (u / 2) ≤ 0 := by linarith
        nlinarith
  have hx_ge_neg_one : -1 ≤ x := by linarith
  have htheta_nonneg : 0 ≤ 2 * Real.arcsin x := by
    have h_arcsin_nonneg : 0 ≤ Real.arcsin x := (Real.arcsin_nonneg.2 hx_nonneg)
    nlinarith
  have htheta_le_pi : 2 * Real.arcsin x ≤ π := by
    have h_arcsin_le : Real.arcsin x ≤ π / 2 := Real.arcsin_le_pi_div_two x
    nlinarith
  have hsin_half : sin ((2 * Real.arcsin x) / 2) = x := by
    calc
      sin ((2 * Real.arcsin x) / 2) = sin (Real.arcsin x) := by field_simp
      _ = x := Real.sin_arcsin hx_ge_neg_one hx_le_one
  have h_enc_final : Enc PL PH (sin ((2 * Real.arcsin x) / 2)) := by
    rw [hsin_half]
    exact ⟨hx_lo, hx_hi⟩
  have hebase_eq : ebase d u = 2 * Real.arcsin x := by
    dsimp [ebase, x]
  rw [hebase_eq]
  exact ⟨hPL_nonneg, htheta_nonneg, htheta_le_pi, h_enc_final⟩

theorem K15_a_open (XL XH : ℤ) (a b V : ℕ) (ha : a = 1 ↔ 0 < XL) (hb : b = 1 ↔ XH < 268435456)
    (hv : V = 1 ↔ a = 1 ∧ b = 1) : V = 1 → ∀ θ : ℝ, AF true XL XH θ → 0 < θ ∧ θ < π := by
  intro hV θ hAF
  rcases hAF with ⟨hXL, hθ0, hθπ, hEnc⟩
  rcases hEnc with ⟨hEncL, hEncH⟩
  have ha1b1 : a = 1 ∧ b = 1 := (hv.mp hV)
  have hpos : 0 < XL := ha.mp ha1b1.1
  have h_lt : XH < 268435456 := hb.mp ha1b1.2
  have h2pow_eq : (2^28 : ℝ) = (268435456 : ℝ) := by norm_num
  have hθpos : 0 < θ := by
    by_contra! hle
    have hθ0' : θ = 0 := by linarith
    subst hθ0'
    have hsin0 : Real.sin ((0 : ℝ) / 2) = 0 := by norm_num
    have hXL0 : (XL : ℝ) ≤ 0 := by
      calc
        (XL : ℝ) ≤ 2^28 * Real.sin ((0 : ℝ) / 2) := hEncL
        _ = 2^28 * 0 := by rw [hsin0]
        _ = 0 := by ring
    have hXLpos : (0 : ℝ) < (XL : ℝ) := by exact_mod_cast hpos
    linarith
  have hθltπ : θ < π := by
    by_contra! hge
    have hθπ' : θ = π := by linarith
    subst hθπ'
    have hsinπ2 : Real.sin (π / 2) = 1 := Real.sin_pi_div_two
    have hXHbound : (2^28 : ℝ) ≤ (XH : ℝ) := by
      calc
        (2^28 : ℝ) = 2^28 * 1 := by ring
        _ = 2^28 * Real.sin (π / 2) := by rw [hsinπ2]
        _ ≤ (XH : ℝ) := hEncH
    have hXHlt : (XH : ℝ) < (2^28 : ℝ) := by
      rw [h2pow_eq]
      exact_mod_cast h_lt
    linarith
  exact And.intro hθpos hθltπ

theorem K15_in_open (XL XH : ℤ) (a b V : ℕ) (ha : a = 1 ↔ 0 < XL) (hb : b = 1 ↔ XH < 843314856)
    (hv : V = 1 ↔ a = 1 ∧ b = 1) : V = 1 → ∀ θ : ℝ, Enc XL XH θ → 0 < θ ∧ θ < π := by
  intro hV θ hEnc
  rcases hEnc with ⟨hlo, hhi⟩
  have ha1 : a = 1 := (hv.mp hV).left
  have hb1 : b = 1 := (hv.mp hV).right
  have hXLpos : 0 < XL := (ha.mp ha1)
  have hXHlt : XH < 843314856 := (hb.mp hb1)
  have hpos : 0 < θ := by
    have hXLpos' : (0 : ℝ) < (XL : ℝ) := by exact_mod_cast hXLpos
    have hpos_mul : (0 : ℝ) < (2 : ℝ) ^ 28 * θ := by linarith
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ 28 := by norm_num
    exact ((mul_pos_iff_of_pos_left hpowpos).mp hpos_mul)
  have hpi : θ < π := by
    have hXHlt' : (XH : ℝ) < 843314856 := by exact_mod_cast hXHlt
    have hbound : (2 : ℝ) ^ 28 * θ < 843314856 := by linarith
    have hdiv : θ < (843314856 : ℝ) / ((2 : ℝ) ^ 28) := by
      linarith
    have h_approx : (843314856 : ℝ) / ((2 : ℝ) ^ 28) < 3.14159265358979323846 := by
      norm_num
    have h_pi_gt : 3.14159265358979323846 < π := Real.pi_gt_d20
    linarith
  exact And.intro hpos hpi

theorem K15_a_open_plain (XL XH : ℤ) (V : ℕ) (h : V = 1 → ∀ θ : ℝ, Enc XL XH θ → 0 < θ ∧ θ < π) :
    V = 1 → ∀ θ : ℝ, AF false XL XH θ → 0 < θ ∧ θ < π := h

theorem K16_a_cos (G : Prop) (XL XH : ℤ) (one th t2 lo0 m LO tl u2 HI : ℤ) (hone : one = 268435456)
    (hth : th = -(-(XH * XH) / 2 ^ 28)) (ht2 : t2 = th + th) (hlo0 : lo0 = one - t2) (hm : m = -268435456)
    (hlo : LO = max lo0 m) (htl : tl = XL * XL / 2 ^ 28) (hu2 : u2 = tl + tl) (hhi : HI = one - u2) :
    G → ∀ θ : ℝ, AF true XL XH θ → Enc LO HI (cos θ) := by
  intro g θ hAF
  rcases hAF with ⟨hXL0, hθ0, hθπ, hEnc⟩
  rcases hEnc with ⟨hXL_enc, hXH_enc⟩
  have hXL0_real : 0 ≤ (XL : ℝ) := by exact_mod_cast hXL0
  have h28pos : (0 : ℝ) < 2 ^ 28 := by norm_num
  have h28ne0 : (2 ^ 28 : ℤ) ≠ 0 := by norm_num
  set q := (2 ^ 28 : ℝ) * sin (θ / 2) with hq_def
  have hq_nonneg : 0 ≤ q := by
    have : 0 ≤ sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
    nlinarith
  have hq_le_XH : q ≤ (XH : ℝ) := hXH_enc
  have hXL_le_q : (XL : ℝ) ≤ q := hXL_enc
  have hcos_eq : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
    calc
      cos θ = cos (2 * (θ / 2)) := by ring_nf
      _ = 1 - 2 * sin (θ / 2) ^ 2 := by
        rw [Real.cos_two_mul]
        have h := Real.sin_sq_add_cos_sq (θ / 2)
        nlinarith
  have h28cos_eq : (2 ^ 28 : ℝ) * cos θ = (2 ^ 28 : ℝ) - 2 * q ^ 2 / (2 ^ 28 : ℝ) := by
    rw [hcos_eq]
    dsimp [q]
    field_simp

  have hXH_sq_le_th_int : XH * XH ≤ (2 ^ 28 : ℤ) * th := by
    rw [hth]
    have h := Int.ediv_mul_le (-(XH * XH)) h28ne0
    linarith

  have htl_mul_le_XL_sq_int : tl * (2 ^ 28 : ℤ) ≤ XL * XL := by
    rw [htl]
    have h := Int.ediv_mul_le (XL * XL) h28ne0
    simpa [htl] using h

  have hXH_sq_le_th : (XH : ℝ) * (XH : ℝ) ≤ (2 ^ 28 : ℝ) * (th : ℝ) := by
    exact_mod_cast hXH_sq_le_th_int
  have htl_mul_le_XL_sq : (tl : ℝ) * (2 ^ 28 : ℝ) ≤ (XL : ℝ) * (XL : ℝ) := by
    exact_mod_cast htl_mul_le_XL_sq_int

  have hone_real : (one : ℝ) = (2 ^ 28 : ℝ) := by exact_mod_cast hone

  have hlower : (LO : ℝ) ≤ (2 ^ 28 : ℝ) * cos θ := by
    rw [hlo, hlo0, ht2]
    push_cast
    rw [hone, hm]
    norm_num

    constructor
    ·
      have h268435456_real : (268435456 : ℝ) = (2 ^ 28 : ℝ) := by norm_num
      rw [h268435456_real]

      have hgoal : (2 ^ 28 : ℝ) - 2 * (th : ℝ) ≤ (2 ^ 28 : ℝ) * cos θ := by
        rw [h28cos_eq]
        have hq_sq_le_XH_sq : q ^ 2 ≤ (XH : ℝ) * (XH : ℝ) := by
          nlinarith
        have hq_sq_div_le_th : q ^ 2 / (2 ^ 28 : ℝ) ≤ (th : ℝ) := by
          have h1 : q ^ 2 / (2 ^ 28 : ℝ) ≤ (XH : ℝ) * (XH : ℝ) / (2 ^ 28 : ℝ) :=
            div_le_div_of_nonneg_right hq_sq_le_XH_sq (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
          have h2 : (XH : ℝ) * (XH : ℝ) / (2 ^ 28 : ℝ) ≤ (th : ℝ) :=
            (div_le_iff₀' h28pos).mpr hXH_sq_le_th
          nlinarith
        nlinarith
      nlinarith
    ·
      have h268435456_real : (268435456 : ℝ) = (2 ^ 28 : ℝ) := by norm_num
      rw [h268435456_real]
      have hcos_ge_neg_one : -1 ≤ cos θ := Real.neg_one_le_cos θ
      nlinarith

  have hupper : (2 ^ 28 : ℝ) * cos θ ≤ (HI : ℝ) := by

    have h_simple : (2 ^ 28 : ℝ) * cos θ ≤ (2 ^ 28 : ℝ) - 2 * (tl : ℝ) := by
      rw [h28cos_eq]
      have htl_le_q_sq_div : (tl : ℝ) ≤ q ^ 2 / (2 ^ 28 : ℝ) := by
        have hXL_sq_le_q_sq : (XL : ℝ) * (XL : ℝ) ≤ q ^ 2 := by
          nlinarith
        have h : (tl : ℝ) * (2 ^ 28 : ℝ) ≤ q ^ 2 :=
          le_trans htl_mul_le_XL_sq hXL_sq_le_q_sq
        exact (le_div_iff₀ h28pos).mpr h
      nlinarith

    rw [hhi, hu2]
    push_cast

    rw [hone_real]

    simpa [two_mul] using h_simple

  exact And.intro hlower hupper

theorem K16_a_cos_plain (G : Prop) (XL XH LO HI : ℤ)
    (h : G → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc LO HI (cos r)) :
    G → ∀ θ : ℝ, AF false XL XH θ → Enc LO HI (cos θ) :=
  fun hG θ hθ => (h hG).2 θ hθ

theorem K17_s_end (Q : ℤ) (q2 c56 w r rh l LO one h h2 HI : ℤ) (hq2 : q2 = Q * Q) (hc56 : c56 = 72057594037927936)
    (hw : w = c56 - q2) (hr : r = ((Int.toNat w).sqrt : ℤ)) (hrh : rh = r + 1) (hl : l = Q * r / 2 ^ 28)
    (hlo : LO = l + l) (hone : one = 268435456) (hh : h = -(-(Q * rh) / 2 ^ 28)) (hh2 : h2 = h + h)
    (hhi : HI = min h2 one) :
    0 ≤ Q →
      (LO : ℝ) ≤ 2 ^ 28 * (2 * ((Q : ℝ) / 2 ^ 28) * √(1 - ((Q : ℝ) / 2 ^ 28) ^ 2)) ∧
        2 ^ 28 * (2 * ((Q : ℝ) / 2 ^ 28) * √(1 - ((Q : ℝ) / 2 ^ 28) ^ 2)) ≤ HI := by
  intro hQ
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hQ
  subst hq2 hc56 hw hr hrh hl hlo hone hh hh2 hhi
  have p28 : (2 : ℤ) ^ 28 = 268435456 := by norm_num
  have p28n : (2 : ℕ) ^ 28 = 268435456 := by norm_num
  simp only [Int.cast_natCast]
  by_cases hn : n ≤ 2 ^ 28
  · have hs := s_end_sound n hn
    have hnn : n * n ≤ 2 ^ 56 := by
      have := Nat.mul_le_mul hn hn
      norm_num at this ⊢; omega
    have ht : Int.toNat (72057594037927936 - (n : ℤ) * n) = 2 ^ 56 - n * n := by
      have e : (72057594037927936 : ℤ) - (n : ℤ) * n = ((2 ^ 56 - n * n : ℕ) : ℤ) := by
        rw [Nat.cast_sub hnn]; push_cast; ring
      rw [e, Int.toNat_natCast]
    rw [ht]
    set s := Nat.sqrt (2 ^ 56 - n * n) with hs_def
    have hY : ((n * s : ℕ) : ℤ) = (n : ℤ) * (s : ℤ) := by push_cast; ring
    have hX : ((n * (s + 1) : ℕ) : ℤ) = (n : ℤ) * ((s : ℤ) + 1) := by push_cast; ring
    have eLO : (n : ℤ) * s / 2 ^ 28 + (n : ℤ) * s / 2 ^ 28 = ((2 * ((n * s) / 2 ^ 28) : ℕ) : ℤ) := by
      rw [← hY, p28]; generalize n * s = Y; omega
    have eH : -(-((n : ℤ) * ((s : ℤ) + 1)) / 2 ^ 28) + -(-((n : ℤ) * ((s : ℤ) + 1)) / 2 ^ 28) =
        ((2 * ((n * (s + 1) + (2 ^ 28 - 1)) / 2 ^ 28) : ℕ) : ℤ) := by
      rw [← hX, p28, p28n]; generalize n * (s + 1) = Y; omega
    rw [eLO, eH]
    constructor
    · exact_mod_cast hs.1
    · have h2 := hs.2
      rw [Int.cast_min, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat]
      have e : ((268435456 : ℤ) : ℝ) = 2 ^ 28 := by norm_num
      rw [e]; exact h2
  · rw [not_le] at hn
    have hlt : (2 : ℤ) ^ 56 < (n : ℤ) * n := by
      have : (2 : ℕ) ^ 56 < n * n := by
        have := Nat.mul_lt_mul'' hn hn
        norm_num at this ⊢; omega
      exact_mod_cast this
    have ht : Int.toNat (72057594037927936 - (n : ℤ) * n) = 0 := by
      apply Int.toNat_eq_zero.2; norm_num at hlt ⊢; linarith
    rw [ht]
    simp only [Nat.sqrt_zero, Nat.cast_zero, mul_zero, Int.zero_ediv, add_zero, zero_add, Int.cast_zero]
    have hq : 1 < (n : ℝ) / 2 ^ 28 := by
      rw [lt_div_iff₀ (by positivity)]
      have : ((2 : ℕ) ^ 28 : ℝ) < n := by exact_mod_cast hn
      push_cast at this; linarith
    have hsq : √(1 - ((n : ℝ) / 2 ^ 28) ^ 2) = 0 := by
      apply Real.sqrt_eq_zero'.2; nlinarith
    rw [hsq]
    simp only [mul_zero, le_refl, true_and]
    have : (0 : ℤ) ≤ min (-(-((n : ℤ) * (0 + 1)) / 2 ^ 28) + -(-((n : ℤ) * (0 + 1)) / 2 ^ 28)) 268435456 := by
      rw [p28]; omega
    exact_mod_cast this

set_option maxHeartbeats 800000 in

theorem K18_a_sin (G : Prop) (XL XH : ℤ) (l1 h1 l2 h2 LO hi0 half ql2 qh2 : ℤ) (a b m : ℕ) (one HI : ℤ)
    (hs1 : 0 ≤ XL →
      (l1 : ℝ) ≤ 2 ^ 28 * (2 * ((XL : ℝ) / 2 ^ 28) * √(1 - ((XL : ℝ) / 2 ^ 28) ^ 2)) ∧
        2 ^ 28 * (2 * ((XL : ℝ) / 2 ^ 28) * √(1 - ((XL : ℝ) / 2 ^ 28) ^ 2)) ≤ h1)
    (hs2 : 0 ≤ XH →
      (l2 : ℝ) ≤ 2 ^ 28 * (2 * ((XH : ℝ) / 2 ^ 28) * √(1 - ((XH : ℝ) / 2 ^ 28) ^ 2)) ∧
        2 ^ 28 * (2 * ((XH : ℝ) / 2 ^ 28) * √(1 - ((XH : ℝ) / 2 ^ 28) ^ 2)) ≤ h2)
    (hlo : LO = min l1 l2) (hhi0 : hi0 = max h1 h2) (hhalf : half = 36028797018963968) (hql2 : ql2 = XL * XL)
    (hqh2 : qh2 = XH * XH) (ha : a = 1 ↔ ql2 ≤ half) (hb : b = 1 ↔ half ≤ qh2) (hm : m = 1 ↔ a = 1 ∧ b = 1)
    (hone : one = 268435456) (hhi : HI = if m = 1 then one else hi0) :
    G → ∀ θ : ℝ, AF true XL XH θ → Enc LO HI (sin θ) := by
  intro _hG θ hAF
  rcases hAF with ⟨hXL0, hθ0, hθπ, hEnc⟩
  rcases hEnc with ⟨hEncL, hEncH⟩
  set q := sin (θ / 2) with hq_def
  have hq0 : 0 ≤ q := by
    have hθ2_0 : 0 ≤ θ / 2 := by linarith
    have hθ2_π : θ / 2 ≤ π := by linarith
    exact Real.sin_nonneg_of_nonneg_of_le_pi hθ2_0 hθ2_π
  have hq1 : q ≤ 1 := Real.sin_le_one _
  have hcos_eq : cos (θ / 2) = Real.sqrt (1 - q ^ 2) := by
    rw [Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) (by linarith), hq_def]
  have hsinθ : sin θ = 2 * q * Real.sqrt (1 - q ^ 2) := by
    calc
      sin θ = sin (2 * (θ / 2)) := by ring_nf
      _ = 2 * sin (θ / 2) * cos (θ / 2) := by rw [Real.sin_two_mul]
      _ = 2 * q * cos (θ / 2) := by rw [hq_def]
      _ = 2 * q * Real.sqrt (1 - q ^ 2) := by rw [hcos_eq]
  have hXL0' : (0 : ℝ) ≤ (XL : ℝ) := by exact_mod_cast hXL0
  have hXL_le_XH_real : (XL : ℝ) ≤ (XH : ℝ) := by linarith
  have hXH0' : (0 : ℝ) ≤ (XH : ℝ) := by linarith
  have hXH0 : 0 ≤ XH := by exact_mod_cast hXH0'
  set ql := (XL : ℝ) / (2 ^ 28 : ℝ) with hql_def
  set qh := (XH : ℝ) / (2 ^ 28 : ℝ) with hqh_def
  set φ := fun (t : ℝ) => 2 * t * Real.sqrt (1 - t ^ 2) with hφ_def
  have hsinθ_φ : sin θ = φ q := hsinθ

  have hφ_ql_bounds : (l1 : ℝ) ≤ (2 ^ 28 : ℝ) * φ ql ∧ (2 ^ 28 : ℝ) * φ ql ≤ h1 := by
    have h := hs1 hXL0
    simpa [hql_def, hφ_def, mul_comm, mul_left_comm, mul_assoc] using h

  have hφ_qh_bounds : (l2 : ℝ) ≤ (2 ^ 28 : ℝ) * φ qh ∧ (2 ^ 28 : ℝ) * φ qh ≤ h2 := by
    have h := hs2 hXH0
    simpa [hqh_def, hφ_def, mul_comm, mul_left_comm, mul_assoc] using h
  rcases hφ_ql_bounds with ⟨hl1, hqh1⟩
  rcases hφ_qh_bounds with ⟨hl2, hqh2'⟩

  have hpos28 : 0 ≤ (2 ^ 28 : ℝ) := by norm_num
  have hql_le_q : ql ≤ q := by
    rw [hql_def]
    calc
      (XL : ℝ) / (2 ^ 28 : ℝ) ≤ ((2 ^ 28 : ℝ) * q) / (2 ^ 28 : ℝ) :=
        div_le_div_of_nonneg_right hEncL hpos28
      _ = q := by field_simp [show (2 ^ 28 : ℝ) ≠ 0 by norm_num]
  have hq_le_qh : q ≤ qh := by
    rw [hqh_def]
    calc
      q = ((2 ^ 28 : ℝ) * q) / (2 ^ 28 : ℝ) := by field_simp [show (2 ^ 28 : ℝ) ≠ 0 by norm_num]
      _ ≤ (XH : ℝ) / (2 ^ 28 : ℝ) := div_le_div_of_nonneg_right hEncH hpos28

  have hφ_nonneg : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ φ t := by
    intro t ht0 ht1
    dsimp [φ]
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
    nlinarith

  have hφ_zero_of_one_lt : ∀ t, 1 < t → φ t = 0 := by
    intro t ht
    dsimp [φ]
    have h_nonpos : 1 - t ^ 2 ≤ 0 := by nlinarith
    rw [Real.sqrt_eq_zero_of_nonpos h_nonpos]
    ring

  have hφ_le_one : ∀ t, 0 ≤ t → t ≤ 1 → φ t ≤ 1 := by
    intro t ht0 ht1
    have h_sq : (φ t) ^ 2 = 4 * t ^ 2 * (1 - t ^ 2) := by
      dsimp [φ]
      have h_sqrt_sq : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
      calc
        (2 * t * Real.sqrt (1 - t ^ 2)) ^ 2 = 4 * t ^ 2 * (Real.sqrt (1 - t ^ 2)) ^ 2 := by ring
        _ = 4 * t ^ 2 * (1 - t ^ 2) := by rw [h_sqrt_sq]
    have h_nonneg_φ : 0 ≤ φ t := hφ_nonneg t ht0 ht1
    have h_sq_le_one : (φ t) ^ 2 ≤ 1 := by
      rw [h_sq]
      have h_nonneg_sq : 0 ≤ (2 * t ^ 2 - 1) ^ 2 := by positivity
      nlinarith
    nlinarith

  have hφ_sq_sub (a b : ℝ) (ha_sq_le : a ^ 2 ≤ 1) (hb_sq_le : b ^ 2 ≤ 1) :
      (φ b) ^ 2 - (φ a) ^ 2 = 4 * (b ^ 2 - a ^ 2) * (1 - (b ^ 2 + a ^ 2)) := by
    dsimp [φ]
    have h1 : (Real.sqrt (1 - a ^ 2)) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
    have h2 : (Real.sqrt (1 - b ^ 2)) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith)
    calc
      (2 * b * Real.sqrt (1 - b ^ 2)) ^ 2 - (2 * a * Real.sqrt (1 - a ^ 2)) ^ 2
          = 4 * b ^ 2 * (Real.sqrt (1 - b ^ 2)) ^ 2 - 4 * a ^ 2 * (Real.sqrt (1 - a ^ 2)) ^ 2 := by ring
      _ = 4 * b ^ 2 * (1 - b ^ 2) - 4 * a ^ 2 * (1 - a ^ 2) := by rw [h1, h2]
      _ = 4 * (b ^ 2 - a ^ 2) * (1 - (b ^ 2 + a ^ 2)) := by ring

  have h_sq_le_sq {a b : ℝ} (ha0 : 0 ≤ a) (hle : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
    nlinarith

  have hφ_mono_inc (a b : ℝ) (ha0 : 0 ≤ a) (hb_sq_le_half : b ^ 2 ≤ 1 / 2) (hle : a ≤ b) :
      φ a ≤ φ b := by
    have hb1 : b ≤ 1 := by nlinarith
    have ha_sq_le : a ^ 2 ≤ 1 := by nlinarith
    have hb_sq_le : b ^ 2 ≤ 1 := by nlinarith
    have hdiff := hφ_sq_sub a b ha_sq_le hb_sq_le
    have h_sum_le_one : b ^ 2 + a ^ 2 ≤ 1 := by nlinarith
    have h_factor_nonneg : 0 ≤ 4 * (b ^ 2 - a ^ 2) * (1 - (b ^ 2 + a ^ 2)) := by
      have h_sq_diff : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith
      have h_nonneg : 0 ≤ 4 * (b ^ 2 - a ^ 2) := by positivity
      have h_nonneg' : 0 ≤ 1 - (b ^ 2 + a ^ 2) := by linarith
      exact mul_nonneg h_nonneg h_nonneg'
    have h_diff_nonneg : 0 ≤ (φ b) ^ 2 - (φ a) ^ 2 := by linarith
    have hφa_nonneg : 0 ≤ φ a := hφ_nonneg a ha0 (by nlinarith)
    have hφb_nonneg : 0 ≤ φ b := hφ_nonneg b (by linarith) hb1
    nlinarith

  have hφ_mono_dec (a b : ℝ) (ha0 : 0 ≤ a) (ha_sq_ge_half : 1 / 2 ≤ a ^ 2) (hb0 : 0 ≤ b) (hb_sq_le_one : b ^ 2 ≤ 1) (hle : a ≤ b) :
      φ b ≤ φ a := by
    have ha_sq_le : a ^ 2 ≤ 1 := by nlinarith
    have hb_sq_le' : b ^ 2 ≤ 1 := hb_sq_le_one
    have hdiff := hφ_sq_sub a b ha_sq_le hb_sq_le'
    have h_sum_ge_one : 1 ≤ b ^ 2 + a ^ 2 := by nlinarith
    have h_factor_nonpos : 4 * (b ^ 2 - a ^ 2) * (1 - (b ^ 2 + a ^ 2)) ≤ 0 := by
      have h_sq_diff : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith
      have h_nonneg : 0 ≤ 4 * (b ^ 2 - a ^ 2) := by positivity
      have h_nonpos : 1 - (b ^ 2 + a ^ 2) ≤ 0 := by linarith
      nlinarith
    have h_diff_nonpos : (φ b) ^ 2 - (φ a) ^ 2 ≤ 0 := by linarith
    have ha_le_one : a ≤ 1 := by nlinarith
    have hφa_nonneg : 0 ≤ φ a := hφ_nonneg a ha0 ha_le_one
    have hb_le_one : b ≤ 1 := by nlinarith
    have hφb_nonneg : 0 ≤ φ b := hφ_nonneg b hb0 hb_le_one
    nlinarith

  have h_min_le : min (φ ql) (φ qh) ≤ φ q := by
    by_cases hq_sq_le_half : q ^ 2 ≤ 1 / 2
    · have hql_nonneg : 0 ≤ ql := by
        rw [hql_def]
        exact div_nonneg hXL0' (by norm_num)
      have hφ_ql_le_φ_q : φ ql ≤ φ q :=
        hφ_mono_inc ql q hql_nonneg hq_sq_le_half hql_le_q
      have hmin_le_ql : min (φ ql) (φ qh) ≤ φ ql := by simp
      linarith
    · have hq_sq_ge_half : 1 / 2 ≤ q ^ 2 := by linarith
      have hqh_nonneg : 0 ≤ qh := by
        rw [hqh_def]
        exact div_nonneg hXH0' (by norm_num)
      have hφ_qh_le_φ_q : φ qh ≤ φ q := by
        by_cases hqh_le_one : qh ≤ 1
        · have hqh_sq_le_one : qh ^ 2 ≤ 1 := by nlinarith
          exact hφ_mono_dec q qh hq0 hq_sq_ge_half hqh_nonneg hqh_sq_le_one hq_le_qh
        · have hφ_qh_zero : φ qh = 0 := hφ_zero_of_one_lt qh (by linarith)
          have hφ_q_nonneg : 0 ≤ φ q := hφ_nonneg q hq0 hq1
          linarith
      have hmin_le_qh : min (φ ql) (φ qh) ≤ φ qh := by simp
      linarith

  have hLO : (LO : ℝ) = min (l1 : ℝ) (l2 : ℝ) := by
    rw [hlo]
    simp
  have h_lower : (LO : ℝ) ≤ (2 ^ 28 : ℝ) * φ q := by
    calc
      (LO : ℝ) = min (l1 : ℝ) (l2 : ℝ) := hLO
      _ ≤ min ((2 ^ 28 : ℝ) * φ ql) ((2 ^ 28 : ℝ) * φ qh) := by
        have h1 : min (l1 : ℝ) (l2 : ℝ) ≤ (l1 : ℝ) := by simp
        have h2 : min (l1 : ℝ) (l2 : ℝ) ≤ (l2 : ℝ) := by simp
        have hle1 : (l1 : ℝ) ≤ (2 ^ 28 : ℝ) * φ ql := hl1
        have hle2 : (l2 : ℝ) ≤ (2 ^ 28 : ℝ) * φ qh := hl2
        exact le_min (le_trans h1 hle1) (le_trans h2 hle2)
      _ = (2 ^ 28 : ℝ) * min (φ ql) (φ qh) := by
        rw [← mul_min_of_nonneg (φ ql) (φ qh) hpos28]
      _ ≤ (2 ^ 28 : ℝ) * φ q := by nlinarith

  have hone_val : (one : ℝ) = (2 ^ 28 : ℝ) := by
    rw [hone]; norm_num
  have hhalf_val : (half : ℝ) = (2 ^ 55 : ℝ) := by
    rw [hhalf]; norm_num
  have hql2_eq : (ql2 : ℝ) = (XL : ℝ) ^ 2 := by
    rw [hql2]; push_cast; ring
  have hqh2_eq : (qh2 : ℝ) = (XH : ℝ) ^ 2 := by
    rw [hqh2]; push_cast; ring

  by_cases hm1 : m = 1
  ·
    have hHI_val : (HI : ℝ) = (2 ^ 28 : ℝ) := by
      rw [hhi, hm1]; push_cast; rw [hone]; norm_num
    have h_upper : (2 ^ 28 : ℝ) * φ q ≤ (2 ^ 28 : ℝ) := by
      have hφq_le_one : φ q ≤ 1 := hφ_le_one q hq0 hq1
      calc
        (2 ^ 28 : ℝ) * φ q ≤ (2 ^ 28 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hφq_le_one (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
        _ = (2 ^ 28 : ℝ) := by simp
    rw [hsinθ_φ]
    have h_upper' : (2 ^ 28 : ℝ) * φ q ≤ (HI : ℝ) := by rw [hHI_val]; exact h_upper
    exact And.intro h_lower h_upper'
  ·
    have hHI_val : (HI : ℝ) = max (h1 : ℝ) (h2 : ℝ) := by
      rw [hhi, if_neg hm1, hhi0]; push_cast; rfl
    have h_upper : (2 ^ 28 : ℝ) * φ q ≤ max (h1 : ℝ) (h2 : ℝ) := by
      have hm_iff : m = 1 ↔ (a = 1 ∧ b = 1) := hm
      have ha_iff : a = 1 ↔ ql2 ≤ half := ha
      have hb_iff : b = 1 ↔ half ≤ qh2 := hb
      have h_not_m : ¬ (m = 1) := hm1
      rw [hm_iff] at h_not_m
      rw [not_and_or] at h_not_m
      rcases h_not_m with (ha_not1 | hb_not1)
      ·
        have ha_not1' : (ql2 : ℝ) > (half : ℝ) := by
          have : ¬ (ql2 ≤ half) := by
            rw [← ha_iff]
            exact ha_not1
          have : (ql2 : ℤ) > half := by omega
          exact_mod_cast this
        rw [hql2_eq, hhalf_val] at ha_not1'
        have h_XL_sq_gt_half' : (2 ^ 55 : ℝ) < (XL : ℝ) ^ 2 := by linarith
        have hql_nonneg : 0 ≤ ql := by
          rw [hql_def]
          exact div_nonneg hXL0' (by norm_num)
        have hql_sq_gt_half : 1 / 2 < ql ^ 2 := by
          rw [hql_def]
          calc
            1 / 2 = (2 ^ 55 : ℝ) / (2 ^ 56 : ℝ) := by norm_num
            _ < (XL : ℝ) ^ 2 / (2 ^ 56 : ℝ) :=
              div_lt_div_of_pos_right h_XL_sq_gt_half' (by norm_num : 0 < (2 ^ 56 : ℝ))
            _ = ((XL : ℝ) / (2 ^ 28 : ℝ)) ^ 2 := by ring
        have hq_sq_gt_half : 1 / 2 < q ^ 2 := by
          nlinarith [hql_sq_gt_half, hql_le_q, hql_nonneg]
        have hql_sq_le_one : ql ^ 2 ≤ 1 := by
          have hql_le_one : ql ≤ 1 := by
            rw [hql_def]
            have hXL_le : (XL : ℝ) ≤ (2 ^ 28 : ℝ) := by
              have : (XL : ℝ) ≤ 2 ^ 28 * q := hEncL
              have : 2 ^ 28 * q ≤ 2 ^ 28 * 1 := mul_le_mul_of_nonneg_left hq1 (by norm_num)
              linarith
            exact (div_le_one (by norm_num : 0 < (2 ^ 28 : ℝ))).mpr hXL_le
          nlinarith
        have hq_sq_le_one : q ^ 2 ≤ 1 := by
          have : q * q ≤ 1 * 1 := mul_le_mul hq1 hq1 hq0 (by linarith)
          linarith
        have hφ_q_le_φ_ql : φ q ≤ φ ql :=
          hφ_mono_dec ql q hql_nonneg (by linarith) hq0 hq_sq_le_one hql_le_q
        calc
          (2 ^ 28 : ℝ) * φ q ≤ (2 ^ 28 : ℝ) * φ ql :=
            mul_le_mul_of_nonneg_left hφ_q_le_φ_ql (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
          _ ≤ h1 := hqh1
          _ ≤ max (h1 : ℝ) (h2 : ℝ) := by simp
      ·
        have hb_not1' : (half : ℝ) > (qh2 : ℝ) := by
          have : ¬ ((half : ℤ) ≤ qh2) := by
            rw [← hb_iff]
            exact hb_not1
          have : (qh2 : ℤ) < half := by omega
          exact_mod_cast this
        rw [hqh2_eq, hhalf_val] at hb_not1'
        have h_XH_sq_lt_half' : (XH : ℝ) ^ 2 < (2 ^ 55 : ℝ) := by linarith
        have hqh_nonneg : 0 ≤ qh := by
          rw [hqh_def]
          exact div_nonneg hXH0' (by norm_num)
        have hqh_sq_lt_half : qh ^ 2 < 1 / 2 := by
          rw [hqh_def]
          calc
            ((XH : ℝ) / (2 ^ 28 : ℝ)) ^ 2 = (XH : ℝ) ^ 2 / (2 ^ 56 : ℝ) := by ring
            _ < (2 ^ 55 : ℝ) / (2 ^ 56 : ℝ) :=
              div_lt_div_of_pos_right h_XH_sq_lt_half' (by norm_num : 0 < (2 ^ 56 : ℝ))
            _ = 1 / 2 := by norm_num
        have hq_sq_lt_half : q ^ 2 < 1 / 2 := by
          have : q * q ≤ qh * qh := mul_le_mul hq_le_qh hq_le_qh hq0 hqh_nonneg
          linarith
        have hqh_sq_le_half' : qh ^ 2 ≤ 1 / 2 := by linarith
        have hφ_q_le_φ_qh : φ q ≤ φ qh :=
          hφ_mono_inc q qh hq0 hqh_sq_le_half' hq_le_qh
        calc
          (2 ^ 28 : ℝ) * φ q ≤ (2 ^ 28 : ℝ) * φ qh :=
            mul_le_mul_of_nonneg_left hφ_q_le_φ_qh (by norm_num : 0 ≤ (2 ^ 28 : ℝ))
          _ ≤ h2 := hqh2'
          _ ≤ max (h1 : ℝ) (h2 : ℝ) := by simp
    rw [hsinθ_φ]
    have h_upper' : (2 ^ 28 : ℝ) * φ q ≤ (HI : ℝ) := by rw [hHI_val]; exact h_upper
    exact And.intro h_lower h_upper'

theorem K18_a_sin_plain (G : Prop) (XL XH LO HI : ℤ)
    (h : G → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc LO HI (sin r)) :
    G → ∀ θ : ℝ, AF false XL XH θ → Enc LO HI (sin θ) :=
  fun hG θ hθ => (h hG).2 θ hθ

theorem bangle_anti (d u v : ℝ) (hd : 0 < d) (hd' : d < π / 2) (hu : 0 < u) (huv : u ≤ v) (hv : v < 2 * π) :
    bangle d v ≤ bangle d u := by
  set a := u / 2 with ha
  set b := v / 2 with hb
  have ha_pos : 0 < a := by linarith
  have ha_lt_pi : a < π := by
    dsimp [a]
    linarith
  have hb_pos : 0 < b := by linarith
  have hb_lt_pi : b < π := by
    dsimp [b]
    linarith
  have hsin_a_pos : 0 < sin a := Real.sin_pos_of_pos_of_lt_pi ha_pos ha_lt_pi
  have hsin_b_pos : 0 < sin b := Real.sin_pos_of_pos_of_lt_pi hb_pos hb_lt_pi
  have hcos_d_pos : 0 < cos d := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  have hpos_denom_a : 0 < cos d * sin a := mul_pos hcos_d_pos hsin_a_pos
  have hpos_denom_b : 0 < cos d * sin b := mul_pos hcos_d_pos hsin_b_pos
  have h_sin_sub_nonneg : 0 ≤ sin (b - a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by
      dsimp [a, b]
      linarith)
  have h_eq : sin (b - a) = sin b * cos a - cos b * sin a := Real.sin_sub b a
  have h_nonneg' : 0 ≤ cos d * (cos a * sin b - cos b * sin a) := by
    have : 0 ≤ cos a * sin b - cos b * sin a := by linarith
    nlinarith
  have hnum_le : cos b / (cos d * sin b) ≤ cos a / (cos d * sin a) := by
    rw [div_le_div_iff₀ hpos_denom_b hpos_denom_a]
    nlinarith
  dsimp [bangle]
  exact Real.arctan_mono hnum_le

theorem atan_range (q : ℝ) : (-421657429 : ℝ) ≤ 2 ^ 28 * arctan q ∧ 2 ^ 28 * arctan q ≤ 421657429 := by
  have hpos : (0 : ℝ) < 2 ^ 28 := by norm_num
  have h_neg : -(π / 2) < arctan q := Real.neg_pi_div_two_lt_arctan q
  have h_pos' : arctan q < π / 2 := Real.arctan_lt_pi_div_two q
  have h_mul_neg : -(2 ^ 28 * (π / 2)) < 2 ^ 28 * arctan q := by
    nlinarith
  have h_mul_pos : 2 ^ 28 * arctan q < 2 ^ 28 * (π / 2) := by
    nlinarith
  have h_pi_bound : π < 3.14159265358979323847 := Real.pi_lt_d20
  have h_bound : (2 ^ 28 : ℝ) * (π / 2) < (421657429 : ℝ) := by
    nlinarith
  have h_lower : (-421657429 : ℝ) < 2 ^ 28 * arctan q := by
    nlinarith
  have h_upper : 2 ^ 28 * arctan q < (421657429 : ℝ) := by
    nlinarith
  exact And.intro (by linarith) (by linarith)

theorem half_lt_pi (x : ℝ) (h0 : 0 ≤ 2 ^ 28 * (x / 2)) (h1 : 2 ^ 28 * (x / 2) ≤ 843314857)
    (hs : 0 < sin (x / 2)) : 0 < x ∧ x < 2 * π := by
  have h2pow_pos : 0 < (2 ^ 28 : ℝ) := by norm_num
  have hx2_nonneg : 0 ≤ x / 2 := by
    nlinarith
  have hx2_le : x / 2 ≤ 843314857 / (2 ^ 28 : ℝ) := by
    nlinarith
  have h_bound : 843314857 / (2 ^ 28 : ℝ) < (4 : ℝ) := by
    norm_num
  have h_four_lt_two_pi : (4 : ℝ) < 2 * π := by
    nlinarith [Real.pi_gt_three]
  have hx2_lt_two_pi : x / 2 < 2 * π := by
    nlinarith
  have hx2_lt_pi : x / 2 < π := by
    by_contra! hge

    have h_nonneg : 0 ≤ x / 2 - π := by nlinarith
    have h_le_pi : x / 2 - π ≤ π := by nlinarith
    have h_sin_sub_nonneg : 0 ≤ sin (x / 2 - π) :=
      Real.sin_nonneg_of_nonneg_of_le_pi h_nonneg h_le_pi
    have h_sin_eq : sin (x / 2) = -sin (x / 2 - π) := by
      have h := Real.sin_sub_pi (x / 2)
      linarith
    have h_sin_nonpos : sin (x / 2) ≤ 0 := by
      rw [h_sin_eq]
      nlinarith
    nlinarith
  have hx_pos : 0 < x := by
    by_contra! hle

    have hx2_le_zero : x / 2 ≤ 0 := by nlinarith
    have hx2_eq_zero : x / 2 = 0 := by nlinarith
    have h_sin_zero : sin (x / 2) = 0 := by
      rw [hx2_eq_zero]
      exact sin_zero
    nlinarith
  have hx_lt_two_pi : x < 2 * π := by nlinarith
  exact And.intro hx_pos hx_lt_two_pi

noncomputable def ang (p : Bool) (z : ℤ) : ℝ := if p then 2 * arcsin ((z : ℝ) / 2 ^ 28) else (z : ℝ) / 2 ^ 28

theorem ang_mem (p : Bool) (lo hi : ℤ) (θ : ℝ) (h : AF p lo hi θ) : ang p lo ≤ θ ∧ θ ≤ ang p hi := by
  have hpos2_28 : 0 < (2 : ℝ) ^ 28 := by norm_num
  cases p with
  | false =>

      rcases h with ⟨hlo, hhi⟩
      have h_lower : ang false lo ≤ θ := by
        dsimp [ang]

        rw [div_le_iff₀ hpos2_28]

        nlinarith
      have h_upper : θ ≤ ang false hi := by
        dsimp [ang]
        rw [le_div_iff₀ hpos2_28]

        nlinarith
      exact And.intro h_lower h_upper
  | true =>

      rcases h with ⟨hlo_nonneg, hθ_nonneg, hθ_le_pi, hEnc⟩
      rcases hEnc with ⟨hlo_le, hhi_le⟩
      have hlo_div_le_sin : (lo : ℝ) / (2 : ℝ) ^ 28 ≤ sin (θ / 2) := by

        rw [div_le_iff₀ hpos2_28]

        nlinarith
      have hsin_le_hi_div : sin (θ / 2) ≤ (hi : ℝ) / (2 : ℝ) ^ 28 := by
        rw [le_div_iff₀ hpos2_28]

        nlinarith
      have hsin_nonneg : 0 ≤ sin (θ / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hlo_div_nonneg : 0 ≤ (lo : ℝ) / (2 : ℝ) ^ 28 :=
        div_nonneg (by exact_mod_cast hlo_nonneg) (by positivity)
      have hlo_div_le_one : (lo : ℝ) / (2 : ℝ) ^ 28 ≤ 1 := by
        have : sin (θ / 2) ≤ 1 := Real.sin_le_one _
        linarith
      have hθ2_nonneg : 0 ≤ θ / 2 := by linarith
      have hθ2_le_pi2 : θ / 2 ≤ π / 2 := by linarith
      have hlo_div_mem : (lo : ℝ) / (2 : ℝ) ^ 28 ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> linarith
      have hθ2_mem : θ / 2 ∈ Set.Icc (-(π / 2)) (π / 2) := by
        constructor <;> linarith

      have h_arcsin_lo_le : Real.arcsin ((lo : ℝ) / (2 : ℝ) ^ 28) ≤ θ / 2 :=
        ((Real.arcsin_le_iff_le_sin hlo_div_mem hθ2_mem).2 hlo_div_le_sin)
      have h_lower : ang true lo ≤ θ := by
        dsimp [ang]
        linarith

      by_cases hhi_div_ge_one : 1 ≤ (hi : ℝ) / (2 : ℝ) ^ 28
      ·
        have h_arcsin_hi : Real.arcsin ((hi : ℝ) / (2 : ℝ) ^ 28) = π / 2 :=
          Real.arcsin_of_one_le hhi_div_ge_one
        have h_upper : θ ≤ ang true hi := by
          dsimp [ang]
          calc
            θ = 2 * (θ / 2) := by ring
            _ ≤ 2 * (π / 2) := by nlinarith
            _ = 2 * Real.arcsin ((hi : ℝ) / (2 : ℝ) ^ 28) := by rw [h_arcsin_hi]
        exact And.intro h_lower h_upper
      ·
        have hhi_div_nonneg : 0 ≤ (hi : ℝ) / (2 : ℝ) ^ 28 := by

          have hlo_le_hi : (lo : ℝ) ≤ (hi : ℝ) := by

            linarith
          have hhi_nonneg : 0 ≤ (hi : ℝ) := by linarith [hlo_nonneg, hlo_le_hi]
          exact div_nonneg (by exact_mod_cast hhi_nonneg) (by positivity)
        have hhi_div_le_one : (hi : ℝ) / (2 : ℝ) ^ 28 ≤ 1 := by linarith
        have hhi_div_mem : (hi : ℝ) / (2 : ℝ) ^ 28 ∈ Set.Icc (-1 : ℝ) 1 := by
          constructor <;> linarith
        have h_arcsin_hi_ge : θ / 2 ≤ Real.arcsin ((hi : ℝ) / (2 : ℝ) ^ 28) :=
          ((Real.le_arcsin_iff_sin_le hθ2_mem hhi_div_mem).2 hsin_le_hi_div)
        have h_upper : θ ≤ ang true hi := by
          dsimp [ang]
          linarith
        exact And.intro h_lower h_upper

theorem AF_of_ang (p : Bool) (lo hi l h : ℤ) (θ0 : ℝ) (h0 : AF p lo hi θ0)
    (hin : ∀ θ : ℝ, AF p lo hi θ → 0 < θ ∧ θ < π) (hl : l = lo ∨ l = hi) (hh : h = lo ∨ h = hi) (x : ℝ)
    (hx1 : ang p l ≤ x) (hx2 : x ≤ ang p h) : AF p l h x := by
  cases p with
  | false =>
    have hx1' : (l : ℝ) / (2 ^ 28 : ℝ) ≤ x := by simpa [ang] using hx1
    have hx2' : x ≤ (h : ℝ) / (2 ^ 28 : ℝ) := by simpa [ang] using hx2
    have h_enc : Enc l h x := by
      constructor
      · linarith
      · linarith
    simpa [AF] using h_enc
  | true =>
    rcases h0 with ⟨hlo, hθ0, hθ0_le_pi, henc⟩
    rcases henc with ⟨hlo_enc, hhi_enc⟩
    set q := fun (z : ℤ) => (z : ℝ) / (2 ^ 28 : ℝ) with hq_def
    have hpos_ne : (2 ^ 28 : ℝ) ≠ 0 := by norm_num
    have hq_lo_le_sin : q lo ≤ Real.sin (θ0 / 2) := by
      rw [hq_def]
      calc
        (lo : ℝ) / (2 ^ 28 : ℝ) ≤ ((2 ^ 28 : ℝ) * Real.sin (θ0 / 2)) / (2 ^ 28 : ℝ) := by
          gcongr
        _ = Real.sin (θ0 / 2) := by field_simp [hpos_ne]
    have h_sin_le_q_hi : Real.sin (θ0 / 2) ≤ q hi := by
      rw [hq_def]
      calc
        Real.sin (θ0 / 2) = ((2 ^ 28 : ℝ) * Real.sin (θ0 / 2)) / (2 ^ 28 : ℝ) := by
          field_simp [hpos_ne]
        _ ≤ (hi : ℝ) / (2 ^ 28 : ℝ) := by gcongr
    have h_sin_nonneg : 0 ≤ Real.sin (θ0 / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have h_sin_le_one : Real.sin (θ0 / 2) ≤ 1 := Real.sin_le_one _
    have hq_lo_nonneg : 0 ≤ q lo := by
      rw [hq_def]
      exact div_nonneg (by exact_mod_cast hlo) (by positivity)

    have hq_hi_lt_one : q hi < 1 := by
      by_contra! hge
      have hq_lo_le_one : q lo ≤ 1 :=
        le_trans hq_lo_le_sin h_sin_le_one
      have h_af_pi : AF true lo hi π := by
        refine ⟨hlo, by linarith [Real.pi_pos], by linarith, ?_⟩
        rw [Real.sin_pi_div_two]
        constructor
        · have : (lo : ℝ) ≤ (2 ^ 28 : ℝ) := by
            rw [hq_def] at hq_lo_le_one
            linarith
          simpa using this
        · have : (2 ^ 28 : ℝ) ≤ (hi : ℝ) := by
            rw [hq_def] at hge
            linarith
          simpa using this
      rcases hin π h_af_pi with ⟨_, h_lt⟩
      linarith
    have hq_lo_le_q_hi : q lo ≤ q hi :=
      le_trans hq_lo_le_sin h_sin_le_q_hi
    have hneg_pi_div_two_le_zero : -(π / 2) ≤ 0 := by linarith [Real.pi_pos]

    rcases hl with (hl | hl)
    ·
      rw [hl]
      have hq_l_nonneg : 0 ≤ q lo := hq_lo_nonneg
      have hq_l_lt_one : q lo < 1 :=
        lt_of_le_of_lt hq_lo_le_q_hi hq_hi_lt_one
      have h_arcsin_l_nonneg : 0 ≤ Real.arcsin (q lo) := by
        rw [Real.arcsin_nonneg]
        exact hq_l_nonneg
      have h_arcsin_l_lt_pi_div_two : Real.arcsin (q lo) < π / 2 := by
        rw [Real.arcsin_lt_pi_div_two]
        exact hq_l_lt_one
      have h_arcsin_l_le_pi_div_two : Real.arcsin (q lo) ≤ π / 2 := by linarith
      rcases hh with (hh | hh)
      ·
        rw [hh]

        have hx1' : ang true lo ≤ x := by simpa [hl, ang] using hx1
        have hx2' : x ≤ ang true lo := by simpa [hh, ang] using hx2

        have hx_eq : x = 2 * Real.arcsin (q lo) := by
          have h1 : 2 * Real.arcsin (q lo) ≤ x := by
            simpa [ang, hq_def] using hx1'
          have h2 : x ≤ 2 * Real.arcsin (q lo) := by
            simpa [ang, hq_def] using hx2'
          linarith
        have hx_nonneg : 0 ≤ x := by
          rw [hx_eq]
          nlinarith
        have hx_le_pi : x ≤ π := by
          rw [hx_eq]
          nlinarith
        have h_sin_arcsin : Real.sin (Real.arcsin (q lo)) = q lo :=
          Real.sin_arcsin (by linarith) (by linarith)
        have h_enc : Enc lo lo (Real.sin (x / 2)) := by
          rw [hx_eq]
          have : 2 * Real.arcsin (q lo) / 2 = Real.arcsin (q lo) := by ring
          rw [this, h_sin_arcsin, hq_def]
          simp [Enc]
          field_simp [hpos_ne]
          exact ⟨le_rfl, le_rfl⟩
        refine ⟨hlo, hx_nonneg, hx_le_pi, ?_⟩
        simpa [Enc] using h_enc
      ·
        rw [hh]

        have hx1' : ang true lo ≤ x := by simpa [hl, ang] using hx1
        have hx2' : x ≤ ang true hi := by simpa [hh, ang] using hx2
        have hq_h_nonneg : 0 ≤ q hi := by linarith
        have hq_h_lt_one : q hi < 1 := hq_hi_lt_one
        have h_arcsin_h_nonneg : 0 ≤ Real.arcsin (q hi) := by
          rw [Real.arcsin_nonneg]
          exact hq_h_nonneg
        have h_arcsin_h_lt_pi_div_two : Real.arcsin (q hi) < π / 2 := by
          rw [Real.arcsin_lt_pi_div_two]
          exact hq_h_lt_one
        have h_arcsin_h_le_pi_div_two : Real.arcsin (q hi) ≤ π / 2 := by linarith

        have hx_half_lower : Real.arcsin (q lo) ≤ x / 2 := by
          have : 2 * Real.arcsin (q lo) ≤ x := by
            simpa [ang, hq_def] using hx1'
          linarith
        have hx_half_upper : x / 2 ≤ Real.arcsin (q hi) := by
          have : x ≤ 2 * Real.arcsin (q hi) := by
            simpa [ang, hq_def] using hx2'
          linarith
        have hx_nonneg : 0 ≤ x := by
          have : 0 ≤ x / 2 := le_trans h_arcsin_l_nonneg hx_half_lower
          linarith
        have hx_le_pi : x ≤ π := by
          have : x / 2 ≤ π / 2 := le_trans hx_half_upper (by linarith)
          linarith

        have h_sin_lower : q lo ≤ Real.sin (x / 2) := by
          calc
            q lo = Real.sin (Real.arcsin (q lo)) := by
              rw [Real.sin_arcsin (by linarith) (by linarith)]
            _ ≤ Real.sin (x / 2) :=
              Real.sin_le_sin_of_le_of_le_pi_div_two
                (le_trans hneg_pi_div_two_le_zero h_arcsin_l_nonneg)
                (by linarith)
                hx_half_lower
        have h_sin_upper : Real.sin (x / 2) ≤ q hi := by
          calc
            Real.sin (x / 2) ≤ Real.sin (Real.arcsin (q hi)) :=
              Real.sin_le_sin_of_le_of_le_pi_div_two
                (by linarith)
                (by linarith)
                hx_half_upper
            _ = q hi := Real.sin_arcsin (by linarith) (by linarith)
        have h_enc : Enc lo hi (Real.sin (x / 2)) := by
          constructor
          · rw [hq_def] at h_sin_lower; linarith
          · rw [hq_def] at h_sin_upper; linarith
        refine ⟨hlo, hx_nonneg, hx_le_pi, ?_⟩
        simpa [Enc] using h_enc
    ·
      rw [hl]
      have hq_l_nonneg : 0 ≤ q hi := by linarith
      have hq_l_lt_one : q hi < 1 := hq_hi_lt_one
      have h_arcsin_l_nonneg : 0 ≤ Real.arcsin (q hi) := by
        rw [Real.arcsin_nonneg]
        exact hq_l_nonneg
      have h_arcsin_l_lt_pi_div_two : Real.arcsin (q hi) < π / 2 := by
        rw [Real.arcsin_lt_pi_div_two]
        exact hq_l_lt_one
      have h_arcsin_l_le_pi_div_two : Real.arcsin (q hi) ≤ π / 2 := by linarith
      rcases hh with (hh | hh)
      ·
        rw [hh]

        have hx1' : ang true hi ≤ x := by simpa [hl, ang] using hx1
        have hx2' : x ≤ ang true lo := by simpa [hh, ang] using hx2
        have hq_h_nonneg : 0 ≤ q lo := hq_lo_nonneg
        have hq_h_lt_one : q lo < 1 :=
          lt_of_le_of_lt hq_lo_le_q_hi hq_hi_lt_one
        have h_arcsin_h_nonneg : 0 ≤ Real.arcsin (q lo) := by
          rw [Real.arcsin_nonneg]
          exact hq_h_nonneg
        have h_arcsin_h_lt_pi_div_two : Real.arcsin (q lo) < π / 2 := by
          rw [Real.arcsin_lt_pi_div_two]
          exact hq_h_lt_one
        have h_arcsin_h_le_pi_div_two : Real.arcsin (q lo) ≤ π / 2 := by linarith

        have hx_half_lower : Real.arcsin (q hi) ≤ x / 2 := by
          have : 2 * Real.arcsin (q hi) ≤ x := by
            simpa [ang, hq_def] using hx1'
          linarith
        have hx_half_upper : x / 2 ≤ Real.arcsin (q lo) := by
          have : x ≤ 2 * Real.arcsin (q lo) := by
            simpa [ang, hq_def] using hx2'
          linarith
        have hx_nonneg : 0 ≤ x := by
          have : 0 ≤ x / 2 := le_trans h_arcsin_l_nonneg hx_half_lower
          linarith
        have hx_le_pi : x ≤ π := by
          have : x / 2 ≤ π / 2 := le_trans hx_half_upper (by linarith)
          linarith

        have h_sin_lower : q hi ≤ Real.sin (x / 2) := by
          calc
            q hi = Real.sin (Real.arcsin (q hi)) := by
              rw [Real.sin_arcsin (by linarith) (by linarith)]
            _ ≤ Real.sin (x / 2) :=
              Real.sin_le_sin_of_le_of_le_pi_div_two
                (le_trans hneg_pi_div_two_le_zero h_arcsin_l_nonneg)
                (by linarith)
                hx_half_lower
        have h_sin_upper : Real.sin (x / 2) ≤ q lo := by
          calc
            Real.sin (x / 2) ≤ Real.sin (Real.arcsin (q lo)) :=
              Real.sin_le_sin_of_le_of_le_pi_div_two
                (by linarith)
                (by linarith)
                hx_half_upper
            _ = q lo := Real.sin_arcsin (by linarith) (by linarith)
        have h_enc : Enc hi lo (Real.sin (x / 2)) := by
          constructor
          · rw [hq_def] at h_sin_lower; linarith
          · rw [hq_def] at h_sin_upper; linarith

        have hlo_le_hi : lo ≤ hi := by
          rw [hq_def] at hq_lo_le_q_hi
          have h_real : (lo : ℝ) ≤ (hi : ℝ) := by linarith
          exact_mod_cast h_real
        have hhi_nonneg : 0 ≤ hi := by linarith
        refine ⟨hhi_nonneg, hx_nonneg, hx_le_pi, ?_⟩
        simpa [Enc] using h_enc
      ·
        rw [hh]

        have hx1' : ang true hi ≤ x := by simpa [hl, ang] using hx1
        have hx2' : x ≤ ang true hi := by simpa [hh, ang] using hx2

        have hx_eq : x = 2 * Real.arcsin (q hi) := by
          have h1 : 2 * Real.arcsin (q hi) ≤ x := by
            simpa [ang, hq_def] using hx1'
          have h2 : x ≤ 2 * Real.arcsin (q hi) := by
            simpa [ang, hq_def] using hx2'
          linarith
        have hx_nonneg : 0 ≤ x := by
          rw [hx_eq]
          nlinarith
        have hx_le_pi : x ≤ π := by
          rw [hx_eq]
          nlinarith
        have h_sin_arcsin : Real.sin (Real.arcsin (q hi)) = q hi :=
          Real.sin_arcsin (by linarith) (by linarith)
        have h_enc : Enc hi hi (Real.sin (x / 2)) := by
          rw [hx_eq]
          have : 2 * Real.arcsin (q hi) / 2 = Real.arcsin (q hi) := by ring
          rw [this, h_sin_arcsin, hq_def]
          simp [Enc]
          field_simp [hpos_ne]
          exact ⟨le_rfl, le_rfl⟩
        have hhi_nonneg : 0 ≤ hi := by
          have hlo_le_hi : lo ≤ hi := by
            rw [hq_def] at hq_lo_le_q_hi
            have h_real : (lo : ℝ) ≤ (hi : ℝ) := by linarith
            exact_mod_cast h_real
          linarith
        refine ⟨hhi_nonneg, hx_nonneg, hx_le_pi, ?_⟩
        simpa [Enc] using h_enc

theorem eta_anti_g (g1 g2 e f : ℝ) (he : 0 < e ∧ e < π) (hf : 0 < f ∧ f < π) (h0 : 0 ≤ g1) (h12 : g1 ≤ g2)
    (h2 : g2 ≤ π) : eta g2 e f ≤ eta g1 e f := by
  rcases he with ⟨he_pos, he_lt⟩
  rcases hf with ⟨hf_pos, hf_lt⟩
  have hsin_e_pos : 0 < sin e := Real.sin_pos_of_pos_of_lt_pi he_pos he_lt
  have hsin_f_pos : 0 < sin f := Real.sin_pos_of_pos_of_lt_pi hf_pos hf_lt
  have hden_pos : 0 < sin e * sin f := mul_pos hsin_e_pos hsin_f_pos
  have hcos_le : cos g2 ≤ cos g1 :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 h2 h12
  have hnum_le : cos g2 - cos e * cos f ≤ cos g1 - cos e * cos f := by
    linarith
  have hden_nonneg : 0 ≤ sin e * sin f := le_of_lt hden_pos
  exact div_le_div_of_nonneg_right hnum_le hden_nonneg

theorem K19_iso_angle_pt (G : Prop) (X CDL CDH : ℤ) (HL HH CHL CHH SHL SHH DNL DNH DL DH : ℤ) (bad nb : ℕ)
    (AL AH l h LO HI : ℤ)
    (hh : ∀ r : ℝ, Enc X X r → Enc HL HH (r / 2))
    (hch : G → (0 ≤ HL ∧ HH ≤ 843314857) ∧ ∀ r : ℝ, Enc HL HH r → Enc CHL CHH (cos r))
    (hsh : G → (0 ≤ HL ∧ HH ≤ 843314857) ∧ ∀ r : ℝ, Enc HL HH r → Enc SHL SHH (sin r))
    (hdn : G → ∀ r s : ℝ, Enc CDL CDH r → Enc SHL SHH s → Enc DNL DNH (r * s))
    (hq : ¬bad = 1 → ∀ r s : ℝ, Enc CHL CHH r → Enc DNL DNH s →
        0 < s ∧ 0 < DL ∧ 0 < DH ∧ (CHL : ℝ) / DL ≤ r / s ∧ r / s ≤ (CHH : ℝ) / DH)
    (hnb : nb = 1 ↔ ¬bad = 1)
    (hal : 0 < DL → ∀ q : ℝ, (CHL : ℝ) / DL ≤ q → (AL : ℝ) / 2 ^ 28 ≤ arctan q)
    (hah : 0 < DH → ∀ q : ℝ, q ≤ (CHH : ℝ) / DH → arctan q ≤ (AH : ℝ) / 2 ^ 28)
    (hl : l = -421657429) (hh' : h = 421657429) (hlo : LO = if bad = 1 then l else AL)
    (hhi : HI = if bad = 1 then h else AH) :
    G → ∀ d : ℝ, 0 < d → d < π / 2 → Enc CDL CDH (cos d) →
      (∀ u : ℝ, 0 < u → u ≤ (X : ℝ) / 2 ^ 28 → (LO : ℝ) ≤ 2 ^ 28 * bangle d u) ∧
        ∀ u : ℝ, (X : ℝ) / 2 ^ 28 ≤ u → u < 2 * π → 2 ^ 28 * bangle d u ≤ HI := by
  intro hG
  intro d hd0 hd1 hcd
  set x := (X : ℝ) / 2 ^ 28 with hx_def
  have hx_enc : Enc X X x := by
    dsimp [Enc, x]
    have h : 2 ^ 28 * ((X : ℝ) / 2 ^ 28) = (X : ℝ) := by ring
    constructor
    · rw [h]
    · rw [h]
  by_cases hbad1 : bad = 1
  ·
    have hLO : LO = l := by
      rw [hlo, if_pos hbad1]
    have hHI : HI = h := by
      rw [hhi, if_pos hbad1]
    constructor
    · intro u hu0 hu_le_x
      have h := (atan_range (cos (u / 2) / (cos d * sin (u / 2)))).1
      simpa [hLO, hl, bangle] using h
    · intro u hx_le_u hu_lt
      have h := (atan_range (cos (u / 2) / (cos d * sin (u / 2)))).2
      simpa [hHI, hh', bangle] using h
  ·
    have hLO : LO = AL := by
      rw [hlo, if_neg hbad1]
    have hHI : HI = AH := by
      rw [hhi, if_neg hbad1]
    have hh_x := hh x hx_enc
    have hch_x := (hch hG).2 (x / 2) hh_x
    have hsh_x := (hsh hG).2 (x / 2) hh_x
    have hdn_cs := hdn hG (cos d) (sin (x / 2)) hcd hsh_x
    have hq_res := hq hbad1 (cos (x / 2)) (cos d * sin (x / 2)) hch_x hdn_cs
    rcases hq_res with ⟨hs_pos, hDL_pos, hDH_pos, h_le1, h_le2⟩
    have hHL0 : (0 : ℤ) ≤ HL := (hch hG).1.1
    have hHH843314857 : HH ≤ (843314857 : ℤ) := (hch hG).1.2
    have hx_lower : (0 : ℝ) ≤ 2 ^ 28 * (x / 2) := by
      have hHL0' : (0 : ℝ) ≤ (HL : ℝ) := by exact_mod_cast hHL0
      have hh_x_left := hh_x.1
      linarith
    have hx_upper : 2 ^ 28 * (x / 2) ≤ (843314857 : ℝ) := by
      have hHH843314857' : (HH : ℝ) ≤ (843314857 : ℝ) := by exact_mod_cast hHH843314857
      have hh_x_right := hh_x.2
      linarith
    have hcos_d_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, hd1⟩
    have hsin_x2_pos : 0 < sin (x / 2) := by
      rcases mul_pos_iff.mp hs_pos with ⟨hcos, hsin⟩ | ⟨hcos_neg, hsin_neg⟩
      · exact hsin
      · linarith
    have hx_range := half_lt_pi x hx_lower hx_upper hsin_x2_pos
    rcases hx_range with ⟨hx_pos, hx_lt_2pi⟩
    set q := cos (x / 2) / (cos d * sin (x / 2)) with hq_def
    have h_bangle_x_lower : (AL : ℝ) / 2 ^ 28 ≤ bangle d x := by
      have := hal hDL_pos q h_le1
      simpa [bangle, q] using this
    have h_bangle_x_upper : bangle d x ≤ (AH : ℝ) / 2 ^ 28 := by
      have := hah hDH_pos q h_le2
      simpa [bangle, q] using this
    have h2pow_pos : (0 : ℝ) ≤ 2 ^ 28 := by norm_num
    constructor
    · rw [hLO]
      intro u hu_pos hu_le_x
      have h_bangle_anti : bangle d x ≤ bangle d u :=
        bangle_anti d u x hd0 hd1 hu_pos hu_le_x hx_lt_2pi
      have h_AL_le : (AL : ℝ) ≤ 2 ^ 28 * bangle d x := by linarith
      have h_mul : 2 ^ 28 * bangle d x ≤ 2 ^ 28 * bangle d u :=
        mul_le_mul_of_nonneg_left h_bangle_anti h2pow_pos
      linarith
    · rw [hHI]
      intro u hx_le_u hu_lt_2pi
      have h_bangle_anti : bangle d u ≤ bangle d x :=
        bangle_anti d x u hd0 hd1 hx_pos hx_le_u hu_lt_2pi
      have h_bangle_x_upper' : 2 ^ 28 * bangle d x ≤ (AH : ℝ) := by linarith
      have h_mul : 2 ^ 28 * bangle d u ≤ 2 ^ 28 * bangle d x :=
        mul_le_mul_of_nonneg_left h_bangle_anti h2pow_pos
      linarith

theorem K20_iso_angle (G : Prop) (UL UH DL DH : ℤ) (CDL CDH L1 H1 : ℤ) (bad1 : ℕ) (L2 H2 : ℤ) (bad2 : ℕ)
    (hcd : G → (0 ≤ DL ∧ DH ≤ 843314857) ∧ ∀ r : ℝ, Enc DL DH r → Enc CDL CDH (cos r))
    (hf1 : G → ∀ d : ℝ, 0 < d → d < π / 2 → Enc CDL CDH (cos d) →
      (∀ u : ℝ, 0 < u → u ≤ (UH : ℝ) / 2 ^ 28 → (L1 : ℝ) ≤ 2 ^ 28 * bangle d u) ∧
        ∀ u : ℝ, (UH : ℝ) / 2 ^ 28 ≤ u → u < 2 * π → 2 ^ 28 * bangle d u ≤ H1)
    (hf2 : G → ∀ d : ℝ, 0 < d → d < π / 2 → Enc CDL CDH (cos d) →
      (∀ u : ℝ, 0 < u → u ≤ (UL : ℝ) / 2 ^ 28 → (L2 : ℝ) ≤ 2 ^ 28 * bangle d u) ∧
        ∀ u : ℝ, (UL : ℝ) / 2 ^ 28 ≤ u → u < 2 * π → 2 ^ 28 * bangle d u ≤ H2) :
    G → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc DL DH d → Enc UL UH u → 0 < u → u < 2 * π →
      Enc L1 H2 (bangle d u) := by
  intro hG d u hd0 hd1 hd_enc hu_enc hu0 hu2π
  have hcd_G := hcd hG
  rcases hcd_G with ⟨_, hcd'⟩
  have hcos_enc : Enc CDL CDH (cos d) := hcd' d hd_enc
  have hf1_G := hf1 hG d hd0 hd1 hcos_enc
  have hf2_G := hf2 hG d hd0 hd1 hcos_enc
  rcases hf1_G with ⟨hf1_lo, _⟩
  rcases hf2_G with ⟨_, hf2_hi⟩
  rcases hu_enc with ⟨hu_l, hu_u⟩
  have h2pos : (0 : ℝ) < 2 ^ 28 := by norm_num
  have hu_le_UH : u ≤ (UH : ℝ) / 2 ^ 28 := by
    apply (le_div_iff₀ h2pos).2
    simpa [mul_comm] using hu_u
  have hUL_le_u : (UL : ℝ) / 2 ^ 28 ≤ u := by
    apply (div_le_iff₀ h2pos).2
    simpa [mul_comm] using hu_l
  have h_lo : (L1 : ℝ) ≤ 2 ^ 28 * bangle d u := hf1_lo u hu0 hu_le_UH
  have h_hi : 2 ^ 28 * bangle d u ≤ H2 := hf2_hi u hUL_le_u hu2π
  exact And.intro h_lo h_hi

end D3Prog.L2
