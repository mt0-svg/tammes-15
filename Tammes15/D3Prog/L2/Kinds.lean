import Tammes15.D3Prog.L2.Kinds2
import Tammes15.D3Prog.L2B.All

namespace D3Prog.L2

open Real Tammes15 D3Ck2Spec

set_option linter.unusedVariables false

theorem K22_corner (g f a b e : ℝ) (hf : 0 < f ∧ f < π) (ha : 0 < a) (hb : b < π) (he : a ≤ e ∧ e ≤ b)
    (P N : ℕ) (hP : P = 1 → ∀ e' ∈ Set.Icc a b, 0 < cos f - cos g * cos e')
    (hN : N = 1 → ∀ e' ∈ Set.Icc a b, cos f - cos g * cos e' < 0) :
    (∃ e1, (if P = 1 then b else a) ≤ e1 ∧ e1 ≤ (if N = 1 then a else b) ∧ eta g e f ≤ eta g e1 f) ∧
      ∃ e2, (if N = 1 then b else a) ≤ e2 ∧ e2 ≤ (if P = 1 then a else b) ∧ eta g e2 f ≤ eta g e f := by
  rcases hf with ⟨hf_left, hf_right⟩
  rcases he with ⟨he_left, he_right⟩
  have hab : a ≤ b := le_trans he_left he_right
  have he_mem : e ∈ Set.Icc a b := ⟨he_left, he_right⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  by_cases hP1 : P = 1
  · have hPpos : ∀ e' ∈ Set.Icc a b, 0 < cos f - cos g * cos e' := hP hP1
    have hPpos' : ∀ e' ∈ Set.Icc a b, 0 ≤ cos f - cos e' * cos g := by
      intro e' he'
      have h := hPpos e' he'
      have h_eq : cos f - cos g * cos e' = cos f - cos e' * cos g := by ring
      rw [h_eq] at h
      exact le_of_lt h
    have hmono : MonotoneOn (fun e => eta g e f) (Set.Icc a b) :=
      Tammes15.Contractors.eta_monotoneOn_e ⟨hf_left, hf_right⟩ ha hb hPpos'
    by_cases hN1 : N = 1
    · have hNneg_e := hN hN1 e he_mem
      have hPpos_e := hPpos e he_mem
      linarith
    · refine ⟨?_, ?_⟩
      · refine ⟨b, ?_, ?_, ?_⟩
        · simp [hP1]
        · simp [hN1]
        · exact hmono he_mem hb_mem he_right
      · refine ⟨a, ?_, ?_, ?_⟩
        · simp [hN1]
        · simp [hP1]
        · exact hmono ha_mem he_mem he_left
  · by_cases hN1 : N = 1
    · have hNneg : ∀ e' ∈ Set.Icc a b, cos f - cos g * cos e' < 0 := hN hN1
      have hNneg' : ∀ e' ∈ Set.Icc a b, cos f - cos e' * cos g ≤ 0 := by
        intro e' he'
        have h := hNneg e' he'
        have h_eq : cos f - cos g * cos e' = cos f - cos e' * cos g := by ring
        rw [h_eq] at h
        exact le_of_lt h
      have hanti : AntitoneOn (fun e => eta g e f) (Set.Icc a b) :=
        Tammes15.Contractors.eta_antitoneOn_e ⟨hf_left, hf_right⟩ ha hb hNneg'
      refine ⟨?_, ?_⟩
      · refine ⟨a, ?_, ?_, ?_⟩
        · simp [hP1]
        · simp [hN1]
        · exact hanti ha_mem he_mem he_left
      · refine ⟨b, ?_, ?_, ?_⟩
        · simp [hN1]
        · simp [hP1]
        · exact hanti he_mem hb_mem he_right
    · refine ⟨?_, ?_⟩
      · refine ⟨e, ?_, ?_, ?_⟩
        · simp [hP1, he_left]
        · simp [hN1, he_right]
        · rfl
      · refine ⟨e, ?_, ?_, ?_⟩
        · simp [hN1, he_left]
        · simp [hP1, he_right]
        · rfl

theorem K23_hn (pg pe pf : Bool) (G : Prop) (GaL GaH EL EH FL FH : ℤ)
    (CGL CGH C1L C1H C2L C2H PL PH NL NH S1L S1H S2L S2H DNL DNH DL DH : ℤ) (BAD : ℕ)
    (hcg : G → ∀ θ : ℝ, AF pg GaL GaH θ → Enc CGL CGH (cos θ))
    (hc1 : G → ∀ θ : ℝ, AF pe EL EH θ → Enc C1L C1H (cos θ))
    (hc2 : G → ∀ θ : ℝ, AF pf FL FH θ → Enc C2L C2H (cos θ))
    (hp : G → ∀ r s : ℝ, Enc C1L C1H r → Enc C2L C2H s → Enc PL PH (r * s))
    (hnum : ∀ r s : ℝ, Enc CGL CGH r → Enc PL PH s → Enc NL NH (r - s))
    (hs1 : G → ∀ θ : ℝ, AF pe EL EH θ → Enc S1L S1H (sin θ))
    (hs2 : G → ∀ θ : ℝ, AF pf FL FH θ → Enc S2L S2H (sin θ))
    (hden : G → ∀ r s : ℝ, Enc S1L S1H r → Enc S2L S2H s → Enc DNL DNH (r * s))
    (hq : ¬BAD = 1 → ∀ r s : ℝ, Enc NL NH r → Enc DNL DNH s →
        0 < s ∧ 0 < DL ∧ 0 < DH ∧ (NL : ℝ) / DL ≤ r / s ∧ r / s ≤ (NH : ℝ) / DH) :
    G → ¬BAD = 1 →
      ∀ θg θe θf : ℝ, AF pg GaL GaH θg → AF pe EL EH θe → AF pf FL FH θf →
        0 < DL ∧ 0 < DH ∧ (NL : ℝ) / DL ≤ eta θg θe θf ∧ eta θg θe θf ≤ (NH : ℝ) / DH := by
  intro hG hnb θg θe θf hg he hf
  set r := cos θg - cos θe * cos θf with hr
  set s := sin θe * sin θf with hs
  have hr_enc : Enc NL NH r :=
    hnum (cos θg) (cos θe * cos θf) (hcg hG θg hg)
      (hp hG (cos θe) (cos θf) (hc1 hG θe he) (hc2 hG θf hf))
  have hs_enc : Enc DNL DNH s :=
    hden hG (sin θe) (sin θf) (hs1 hG θe he) (hs2 hG θf hf)
  have h := hq hnb r s hr_enc hs_enc
  rcases h with ⟨hs_pos, hDL_pos, hDH_pos, hle1, hle2⟩
  have heta_eq : eta θg θe θf = r / s := by
    dsimp [eta, r, s]
  rw [← heta_eq] at hle1 hle2
  exact ⟨hDL_pos, hDH_pos, hle1, hle2⟩

theorem K24_tri_tail_x (pg pe pf : Bool) (G : Prop) (GaL GaH : ℤ) (guard : ℕ) (E1L E1H F1L F1H E2L E2H F2L F2H : ℤ)
    (one mone : ℤ) (N1L D1L N1 D1 : ℤ) (BAD1 nbad1 : ℕ) (nd1 : ℤ) (lt1 m1 ge1 one1 : ℕ) (y1n y1d : ℤ)
    (N2 D2 N2H D2H : ℤ) (BAD2 nbad2 gt2 m2 : ℕ) (nd2 : ℤ) (le2 mone2 : ℕ) (y2n y2d : ℤ) (er ner : ℕ)
    (LO HI zero pih pil OKL OKH : ℤ) (ERR : ℕ) (EVL EVH : ℤ)
    (hone : one = 268435456) (hmone : mone = -268435456)
    (hh1 : G ∧ guard = 1 → ¬BAD1 = 1 →
      ∀ θg θe θf : ℝ, AF pg GaL GaL θg → AF pe E1L E1H θe → AF pf F1L F1H θf →
        0 < D1L ∧ 0 < D1 ∧ (N1L : ℝ) / D1L ≤ eta θg θe θf ∧ eta θg θe θf ≤ (N1 : ℝ) / D1)
    (hnbad1 : nbad1 = 1 ↔ ¬BAD1 = 1) (hnd1 : nd1 = -D1) (hlt1 : lt1 = 1 ↔ N1 < nd1)
    (hm1 : m1 = 1 ↔ nbad1 = 1 ∧ lt1 = 1) (hge1 : ge1 = 1 ↔ D1 ≤ N1) (hone1 : one1 = 1 ↔ BAD1 = 1 ∨ ge1 = 1)
    (hy1n : y1n = if one1 = 1 then one else N1) (hy1d : y1d = if one1 = 1 then one else D1)
    (hh2 : G ∧ guard = 1 → ¬BAD2 = 1 →
      ∀ θg θe θf : ℝ, AF pg GaH GaH θg → AF pe E2L E2H θe → AF pf F2L F2H θf →
        0 < D2 ∧ 0 < D2H ∧ (N2 : ℝ) / D2 ≤ eta θg θe θf ∧ eta θg θe θf ≤ (N2H : ℝ) / D2H)
    (hnbad2 : nbad2 = 1 ↔ ¬BAD2 = 1) (hgt2 : gt2 = 1 ↔ D2 < N2) (hm2 : m2 = 1 ↔ nbad2 = 1 ∧ gt2 = 1)
    (hnd2 : nd2 = -D2) (hle2 : le2 = 1 ↔ N2 ≤ nd2) (hmone2 : mone2 = 1 ↔ BAD2 = 1 ∨ le2 = 1)
    (hy2n : y2n = if mone2 = 1 then mone else N2) (hy2d : y2d = if mone2 = 1 then one else D2)
    (her : er = 1 ↔ m1 = 1 ∨ m2 = 1) (hner : ner = 1 ↔ ¬er = 1)
    (hlo : 0 < y1d → ∀ y : ℝ, y ≤ (y1n : ℝ) / y1d → -1 ≤ y → (LO : ℝ) / 2 ^ 28 ≤ arccos y)
    (hhi : 0 < y2d → ∀ y : ℝ, (y2n : ℝ) / y2d ≤ y → y ≤ 1 → arccos y ≤ (HI : ℝ) / 2 ^ 28)
    (hzero : zero = 0) (hpih : pih = 843314857) (hpil : pil = 843314856)
    (hokl : OKL = if guard = 1 then LO else zero) (hokh : OKH = if guard = 1 then HI else pih)
    (herr : ERR = 1 ↔ guard = 1 ∧ er = 1) (hevl : EVL = if m1 = 1 then pil else zero)
    (hevh : EVH = if m1 = 1 then pih else zero) :
    G → ∀ y : ℝ,
      (guard = 1 →
        (∃ θg θe θf : ℝ, AF pg GaL GaL θg ∧ AF pe E1L E1H θe ∧ AF pf F1L F1H θf ∧ y ≤ eta θg θe θf) ∧
          ∃ θg θe θf : ℝ, AF pg GaH GaH θg ∧ AF pe E2L E2H θe ∧ AF pf F2L F2H θf ∧ eta θg θe θf ≤ y) →
      (¬ERR = 1 → Enc OKL OKH (arccos y)) ∧ (ERR = 1 → Enc EVL EVH (arccos y)) := by
  exact @L2B.K24_tri_tail_x pg pe pf G GaL GaH guard E1L E1H F1L F1H E2L E2H F2L F2H one mone N1L D1L N1 D1 BAD1 nbad1 nd1 lt1 m1 ge1 one1 y1n y1d N2 D2 N2H D2H BAD2 nbad2 gt2 m2 nd2 le2 mone2 y2n y2d er ner LO HI zero pih pil OKL OKH ERR EVL EVH hone hmone hh1 hnbad1 hnd1 hlt1 hm1 hge1 hone1 hy1n hy1d hh2 hnbad2 hgt2 hm2 hnd2 hle2 hmone2 hy2n hy2d her hner hlo hhi hzero hpih hpil hokl hokh herr hevl hevh

theorem eta_symm (g e f : ℝ) : eta g e f = eta g f e := by
  unfold eta; ring

theorem sub_box (p : Bool) (lo hi l h : ℤ) (θ0 : ℝ) (h0 : AF p lo hi θ0)
    (hin : ∀ θ : ℝ, AF p lo hi θ → 0 < θ ∧ θ < π) (hl : l = lo ∨ l = hi) (hh : h = lo ∨ h = hi) (x : ℝ)
    (hx : AF p l h x) : AF p lo hi x ∧ 0 < x ∧ x < π := by
  have hm := ang_mem p lo hi θ0 h0
  have hx' := ang_mem p l h x hx
  have h1 : ang p lo ≤ x := by
    rcases hl with hl | hl <;> rw [hl] at hx' <;> linarith [hx'.1]
  have h2 : x ≤ ang p hi := by
    rcases hh with hh | hh <;> rw [hh] at hx' <;> linarith [hx'.2]
  have hA := AF_of_ang p lo hi lo hi θ0 h0 hin (Or.inl rfl) (Or.inr rfl) x h1 h2
  exact ⟨hA, hin x hA⟩

theorem ang_ite (p : Bool) (c : Prop) [Decidable c] (a b : ℤ) :
    ang p (if c then a else b) = if c then ang p a else ang p b := by
  split_ifs <;> rfl

theorem ite_mem (c : Prop) [Decidable c] (a b : ℤ) : (if c then a else b) = a ∨ (if c then a else b) = b := by
  split_ifs <;> simp

theorem K21_tri_angle_st (pg pe pf : Bool) (G : Prop) (GaL GaH EL EH FL FH : ℤ) (gg ge gf g1 guard : ℕ)
    (GCL GCH CFL CFH CEL CEH T1L T1H NFL NFH T2L T2H NEL NEH : ℤ) (nfp nfn nep nen : ℕ)
    (E1L E1H E2L E2H F1L F1H F2L F2H OKL OKH : ℤ) (ERR : ℕ) (EVL EVH : ℤ)
    (hgg : gg = 1 → ∀ θ : ℝ, AF pg GaL GaH θ → 0 < θ ∧ θ < π)
    (hge : ge = 1 → ∀ θ : ℝ, AF pe EL EH θ → 0 < θ ∧ θ < π)
    (hgf : gf = 1 → ∀ θ : ℝ, AF pf FL FH θ → 0 < θ ∧ θ < π)
    (hg1 : g1 = 1 ↔ gg = 1 ∧ ge = 1) (hguard : guard = 1 ↔ g1 = 1 ∧ gf = 1)
    (hgc : G ∧ guard = 1 → ∀ θ : ℝ, AF pg GaL GaH θ → Enc GCL GCH (cos θ))
    (hcf : G ∧ guard = 1 → ∀ θ : ℝ, AF pf FL FH θ → Enc CFL CFH (cos θ))
    (hce : G ∧ guard = 1 → ∀ θ : ℝ, AF pe EL EH θ → Enc CEL CEH (cos θ))
    (ht1 : G ∧ guard = 1 → ∀ r s : ℝ, Enc GCL GCH r → Enc CEL CEH s → Enc T1L T1H (r * s))
    (hnf : ∀ r s : ℝ, Enc CFL CFH r → Enc T1L T1H s → Enc NFL NFH (r - s))
    (ht2 : G ∧ guard = 1 → ∀ r s : ℝ, Enc GCL GCH r → Enc CFL CFH s → Enc T2L T2H (r * s))
    (hne : ∀ r s : ℝ, Enc CEL CEH r → Enc T2L T2H s → Enc NEL NEH (r - s))
    (hnfp : nfp = 1 ↔ 0 < NFL) (hnfn : nfn = 1 ↔ NFH < 0) (hnep : nep = 1 ↔ 0 < NEL) (hnen : nen = 1 ↔ NEH < 0)
    (hE1L : E1L = if nfp = 1 then EH else EL) (hE1H : E1H = if nfn = 1 then EL else EH)
    (hE2L : E2L = if nfn = 1 then EH else EL) (hE2H : E2H = if nfp = 1 then EL else EH)
    (hF1L : F1L = if nep = 1 then FH else FL) (hF1H : F1H = if nen = 1 then FL else FH)
    (hF2L : F2L = if nen = 1 then FH else FL) (hF2H : F2H = if nep = 1 then FL else FH)
    (htail : G → ∀ y : ℝ,
      (guard = 1 →
        (∃ θg θe θf : ℝ, AF pg GaL GaL θg ∧ AF pe E1L E1H θe ∧ AF pf F1L F1H θf ∧ y ≤ eta θg θe θf) ∧
          ∃ θg θe θf : ℝ, AF pg GaH GaH θg ∧ AF pe E2L E2H θe ∧ AF pf F2L F2H θf ∧ eta θg θe θf ≤ y) →
      (¬ERR = 1 → Enc OKL OKH (arccos y)) ∧ (ERR = 1 → Enc EVL EVH (arccos y))) :
    G → ∀ θg θe θf : ℝ, AF pg GaL GaH θg → AF pe EL EH θe → AF pf FL FH θf →
      (¬ERR = 1 → Enc OKL OKH (gam θg θe θf)) ∧ (ERR = 1 → Enc EVL EVH (gam θg θe θf)) := by
  intro hG θg θe θf hg he hf
  show (¬ERR = 1 → Enc OKL OKH (arccos (eta θg θe θf))) ∧ (ERR = 1 → Enc EVL EVH (arccos (eta θg θe θf)))
  apply htail hG
  intro hgd
  have hGg : G ∧ guard = 1 := ⟨hG, hgd⟩
  obtain ⟨hg1d, hgfd⟩ := hguard.1 hgd
  obtain ⟨hggd, hged⟩ := hg1.1 hg1d
  have hin_g := hgg hggd
  have hin_e := hge hged
  have hin_f := hgf hgfd
  have hgm := ang_mem pg GaL GaH θg hg
  have hem := ang_mem pe EL EH θe he
  have hfm := ang_mem pf FL FH θf hf
  have boxg : ∀ x, ang pg GaL ≤ x → x ≤ ang pg GaH → AF pg GaL GaH x := fun x h1 h2 =>
    AF_of_ang pg GaL GaH GaL GaH θg hg hin_g (Or.inl rfl) (Or.inr rfl) x h1 h2
  have boxe : ∀ x, ang pe EL ≤ x → x ≤ ang pe EH → AF pe EL EH x := fun x h1 h2 =>
    AF_of_ang pe EL EH EL EH θe he hin_e (Or.inl rfl) (Or.inr rfl) x h1 h2
  have boxf : ∀ x, ang pf FL ≤ x → x ≤ ang pf FH → AF pf FL FH x := fun x h1 h2 =>
    AF_of_ang pf FL FH FL FH θf hf hin_f (Or.inl rfl) (Or.inr rfl) x h1 h2
  have hθg := hin_g θg hg
  have hθe := hin_e θe he
  have hθf := hin_f θf hf
  have hEL := hin_e _ (boxe _ le_rfl (hem.1.trans hem.2))
  have hEH := hin_e _ (boxe _ (hem.1.trans hem.2) le_rfl)
  have hFL := hin_f _ (boxf _ le_rfl (hfm.1.trans hfm.2))
  have hFH := hin_f _ (boxf _ (hfm.1.trans hfm.2) le_rfl)

  have sgnE : ∀ g' f' e', AF pg GaL GaH g' → AF pf FL FH f' → AF pe EL EH e' →
      (nfp = 1 → 0 < cos f' - cos g' * cos e') ∧ (nfn = 1 → cos f' - cos g' * cos e' < 0) := by
    intro g' f' e' hg' hf' he'
    have h1 := hnf _ _ (hcf hGg f' hf') (ht1 hGg _ _ (hgc hGg g' hg') (hce hGg e' he'))
    unfold Enc at h1
    constructor
    · intro h
      have : (0 : ℝ) < NFL := by exact_mod_cast hnfp.1 h
      linarith
    · intro h
      have : (NFH : ℝ) < 0 := by exact_mod_cast hnfn.1 h
      linarith
  have sgnF : ∀ g' e' f', AF pg GaL GaH g' → AF pe EL EH e' → AF pf FL FH f' →
      (nep = 1 → 0 < cos e' - cos g' * cos f') ∧ (nen = 1 → cos e' - cos g' * cos f' < 0) := by
    intro g' e' f' hg' he' hf'
    have h1 := hne _ _ (hce hGg e' he') (ht2 hGg _ _ (hgc hGg g' hg') (hcf hGg f' hf'))
    unfold Enc at h1
    constructor
    · intro h
      have : (0 : ℝ) < NEL := by exact_mod_cast hnep.1 h
      linarith
    · intro h
      have : (NEH : ℝ) < 0 := by exact_mod_cast hnen.1 h
      linarith

  have hgL : AF pg GaL GaH (ang pg GaL) := boxg _ le_rfl (hgm.1.trans hgm.2)
  have hgH : AF pg GaL GaH (ang pg GaH) := boxg _ (hgm.1.trans hgm.2) le_rfl
  have hgL' : AF pg GaL GaL (ang pg GaL) :=
    AF_of_ang pg GaL GaH GaL GaL θg hg hin_g (Or.inl rfl) (Or.inl rfl) _ le_rfl le_rfl
  have hgH' : AF pg GaH GaH (ang pg GaH) :=
    AF_of_ang pg GaL GaH GaH GaH θg hg hin_g (Or.inr rfl) (Or.inr rfl) _ le_rfl le_rfl
  have hgLr := hin_g _ hgL
  have hgHr := hin_g _ hgH
  refine ⟨?_, ?_⟩
  ·
    set g' := ang pg GaL with hg'
    obtain ⟨⟨e1, he1a, he1b, he1η⟩, -⟩ := K22_corner g' θf (ang pe EL) (ang pe EH) θe hθf hEL.1 hEH.2 hem
      nfp nfn (fun h e' he' => (sgnE g' θf e' hgL hf (boxe e' he'.1 he'.2)).1 h)
      (fun h e' he' => (sgnE g' θf e' hgL hf (boxe e' he'.1 he'.2)).2 h)
    have he1 : AF pe E1L E1H e1 := by
      apply AF_of_ang pe EL EH E1L E1H θe he hin_e (by rw [hE1L]; split_ifs <;> simp) (by rw [hE1H]; split_ifs <;> simp)
      · rw [hE1L, ang_ite]; exact he1a
      · rw [hE1H, ang_ite]; exact he1b
    have he1r := sub_box pe EL EH E1L E1H θe he hin_e (by rw [hE1L]; split_ifs <;> simp) (by rw [hE1H]; split_ifs <;> simp) e1 he1
    obtain ⟨⟨f1, hf1a, hf1b, hf1η⟩, -⟩ := K22_corner g' e1 (ang pf FL) (ang pf FH) θf he1r.2 hFL.1 hFH.2 hfm
      nep nen (fun h f' hf' => (sgnF g' e1 f' hgL he1r.1 (boxf f' hf'.1 hf'.2)).1 h)
      (fun h f' hf' => (sgnF g' e1 f' hgL he1r.1 (boxf f' hf'.1 hf'.2)).2 h)
    have hf1 : AF pf F1L F1H f1 := by
      apply AF_of_ang pf FL FH F1L F1H θf hf hin_f (by rw [hF1L]; split_ifs <;> simp) (by rw [hF1H]; split_ifs <;> simp)
      · rw [hF1L, ang_ite]; exact hf1a
      · rw [hF1H, ang_ite]; exact hf1b
    refine ⟨g', e1, f1, hgL', he1, hf1, ?_⟩
    have h1 : eta θg θe θf ≤ eta g' θe θf := eta_anti_g _ _ _ _ hθe hθf hgLr.1.le hgm.1 hθg.2.le
    rw [eta_symm g' θf e1, eta_symm g' f1 e1] at hf1η
    linarith
  ·
    set g' := ang pg GaH with hg'
    obtain ⟨-, ⟨e2, he2a, he2b, he2η⟩⟩ := K22_corner g' θf (ang pe EL) (ang pe EH) θe hθf hEL.1 hEH.2 hem
      nfp nfn (fun h e' he' => (sgnE g' θf e' hgH hf (boxe e' he'.1 he'.2)).1 h)
      (fun h e' he' => (sgnE g' θf e' hgH hf (boxe e' he'.1 he'.2)).2 h)
    have he2 : AF pe E2L E2H e2 := by
      apply AF_of_ang pe EL EH E2L E2H θe he hin_e (by rw [hE2L]; split_ifs <;> simp) (by rw [hE2H]; split_ifs <;> simp)
      · rw [hE2L, ang_ite]; exact he2a
      · rw [hE2H, ang_ite]; exact he2b
    have he2r := sub_box pe EL EH E2L E2H θe he hin_e (by rw [hE2L]; split_ifs <;> simp) (by rw [hE2H]; split_ifs <;> simp) e2 he2
    obtain ⟨-, ⟨f2, hf2a, hf2b, hf2η⟩⟩ := K22_corner g' e2 (ang pf FL) (ang pf FH) θf he2r.2 hFL.1 hFH.2 hfm
      nep nen (fun h f' hf' => (sgnF g' e2 f' hgH he2r.1 (boxf f' hf'.1 hf'.2)).1 h)
      (fun h f' hf' => (sgnF g' e2 f' hgH he2r.1 (boxf f' hf'.1 hf'.2)).2 h)
    have hf2 : AF pf F2L F2H f2 := by
      apply AF_of_ang pf FL FH F2L F2H θf hf hin_f (by rw [hF2L]; split_ifs <;> simp) (by rw [hF2H]; split_ifs <;> simp)
      · rw [hF2L, ang_ite]; exact hf2a
      · rw [hF2H, ang_ite]; exact hf2b
    refine ⟨g', e2, f2, hgH', he2, hf2, ?_⟩
    have h1 : eta g' θe θf ≤ eta θg θe θf := eta_anti_g _ _ _ _ hθe hθf hθg.1.le hgm.2 hgHr.2.le
    rw [eta_symm g' θf e2, eta_symm g' f2 e2] at hf2η
    linarith

theorem K25_tri_angle (pg pe pf : Bool) (G : Prop) (GaL GaH EL EH FL FH : ℤ) (OKL OKH : ℤ) (ERR : ℕ)
    (EVL EVH : ℤ) (ne : ℕ)
    (hst : G → ∀ θg θe θf : ℝ, AF pg GaL GaH θg → AF pe EL EH θe → AF pf FL FH θf →
      (¬ERR = 1 → Enc OKL OKH (gam θg θe θf)) ∧ (ERR = 1 → Enc EVL EVH (gam θg θe θf)))
    (hne : ne = 1 ↔ ¬ERR = 1) (hck : G → ne = 1) :
    G → ∀ θg θe θf : ℝ, AF pg GaL GaH θg → AF pe EL EH θe → AF pf FL FH θf → Enc OKL OKH (gam θg θe θf) := by
  intro hG θg θe θf hpg hpe hpf
  have hne1 : ne = 1 := hck hG
  have hnotERR : ¬ERR = 1 := (hne.mp hne1)
  have hpair := hst hG θg θe θf hpg hpe hpf
  exact hpair.1 hnotERR

theorem K25_tri_angle_c (pg pe pf : Bool) (G : Prop) (GaL GaH EL EH FL FH : ℤ) (OKL OKH : ℤ) (ERR : ℕ)
    (EVL EVH LO HI : ℤ)
    (hst : G → ∀ θg θe θf : ℝ, AF pg GaL GaH θg → AF pe EL EH θe → AF pf FL FH θf →
      (¬ERR = 1 → Enc OKL OKH (gam θg θe θf)) ∧ (ERR = 1 → Enc EVL EVH (gam θg θe θf)))
    (hlo : LO = if ERR = 1 then EVL else OKL) (hhi : HI = if ERR = 1 then EVH else OKH) :
    G → ∀ θg θe θf : ℝ, AF pg GaL GaH θg → AF pe EL EH θe → AF pf FL FH θf → Enc LO HI (gam θg θe θf) := by
  intro hG θg θe θf hpg hpe hpf
  have h := hst hG θg θe θf hpg hpe hpf
  rcases h with ⟨h_not1, h_eq1⟩
  by_cases hERR : ERR = 1
  ·
    have hLO : LO = EVL := by
      simp [hlo, hERR]
    have hHI : HI = EVH := by
      simp [hhi, hERR]
    rw [hLO, hHI]
    exact h_eq1 hERR
  ·
    have hLO : LO = OKL := by
      simp [hlo, hERR]
    have hHI : HI = OKH := by
      simp [hhi, hERR]
    rw [hLO, hHI]
    exact h_not1 hERR

theorem K26_dec_dir_x (G : Prop) (UL UH BXL BXH XL XH DL DH : ℤ) (a b early ne : ℕ)
    (HL HH CDL CDH SHL SHH T1L T1H CXL CXH SXL SXH DLq DHq : ℤ) (bad nb : ℕ) (CHL CHH z : ℤ)
    (al pa ah na0 na za bl pb bh nb0 nbg zb both nboth t m : ℕ) (xn xd : ℤ) (t' m' : ℕ) (ylo k l r : ℤ)
    (r1 r' OUT : ℕ)
    (ha : a = 1 ↔ UH < 843314857) (hb : b = 1 ↔ BXH < 843314857) (hearly : early = 1 ↔ a = 1 ∧ b = 1)
    (hne : ne = 1 ↔ ¬early = 1) (hh : ∀ r : ℝ, Enc UL UH r → Enc HL HH (r / 2))
    (hcd : G ∧ ne = 1 → (0 ≤ DL ∧ DH ≤ 843314857) ∧ ∀ r : ℝ, Enc DL DH r → Enc CDL CDH (cos r))
    (hsh : G ∧ ne = 1 → (0 ≤ HL ∧ HH ≤ 843314857) ∧ ∀ r : ℝ, Enc HL HH r → Enc SHL SHH (sin r))
    (ht1 : G ∧ ne = 1 → ∀ r s : ℝ, Enc CDL CDH r → Enc SHL SHH s → Enc T1L T1H (r * s))
    (hcx : G ∧ ne = 1 → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc CXL CXH (cos r))
    (hsx : G ∧ ne = 1 → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc SXL SXH (sin r))
    (hq : ¬bad = 1 → ∀ r s : ℝ, Enc CXL CXH r → Enc SXL SXH s →
        0 < s ∧ 0 < DLq ∧ 0 < DHq ∧ (CXL : ℝ) / DLq ≤ r / s ∧ r / s ≤ (CXH : ℝ) / DHq)
    (hnb : nb = 1 ↔ ¬bad = 1)
    (hch : (G ∧ ne = 1) ∧ nb = 1 → (0 ≤ HL ∧ HH ≤ 843314857) ∧
      ∀ r : ℝ, Enc HL HH r → Enc CHL CHH (cos r))
    (hz : z = 0) (hal : al = 1 ↔ CXL < z) (hpa : pa = 1 ↔ ¬al = 1) (hah : ah = 1 ↔ z < CXH)
    (hna0 : na0 = 1 ↔ ¬ah = 1) (hna : na = 1 ↔ na0 = 1 ∧ al = 1) (hza : za = 1 ↔ al = 1 ∧ ah = 1)
    (hbl : bl = 1 ↔ CHL < z) (hpb : pb = 1 ↔ ¬bl = 1) (hbh : bh = 1 ↔ z < CHH) (hnb0 : nb0 = 1 ↔ ¬bh = 1)
    (hnbg : nbg = 1 ↔ nb0 = 1 ∧ bl = 1) (hzb : zb = 1 ↔ bl = 1 ∧ bh = 1) (hboth : both = 1 ↔ za = 1 ∧ zb = 1)
    (hnboth : nboth = 1 ↔ ¬both = 1) (hck : (G ∧ ne = 1) ∧ nb = 1 → nboth = 1)
    (ht : t = 1 ↔ pa = 1 ∧ zb = 1) (hm : m = 1 ↔ nbg = 1 ∨ t = 1) (hxn : xn = if m = 1 then CXH else CXL)
    (hxd : xd = if m = 1 then DHq else DLq) (ht' : t' = 1 ↔ za = 1 ∧ pb = 1) (hm' : m' = 1 ↔ na = 1 ∨ t' = 1)
    (hylo : ylo = if m' = 1 then CHH else CHL) (hk : k = -T1L) (hl : l = k * xd) (hr : r = xn * ylo)
    (hr1 : r1 = 1 ↔ l < r) (hr' : r' = 1 ↔ r1 = 1 ∧ nb = 1) (hout : OUT = 1 ↔ early = 1 ∨ r' = 1) :
    G → OUT = 1 → ∀ (d : ℝ) (Y : ℝ → ℝ), Enc DL DH d → 0 < d → d < π / 2 → (0 : ℝ) < UL →
      (∀ u : ℝ, Enc UL UH u → 0 < Y u → Y u < π → Enc XL XH (Y u) ∧ Enc BXL BXH (bangle d u + Y u)) →
      ∀ u ∈ Set.Icc ((UL : ℝ) / 2 ^ 28) (min ((UH : ℝ) / 2 ^ 28) π), 0 < Y u → Y u < π →
        0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
  exact @L2B.K26_dec_dir_x G UL UH BXL BXH XL XH DL DH a b early ne HL HH CDL CDH SHL SHH T1L T1H CXL CXH SXL SXH DLq DHq bad nb CHL CHH z al pa ah na0 na za bl pb bh nb0 nbg zb both nboth t m xn xd t' m' ylo k l r r1 r' OUT ha hb hearly hne hh hcd hsh ht1 hcx hsx hq hnb hch hz hal hpa hah hna0 hna hza hbl hpb hbh hnb0 hnbg hzb hboth hnboth hck ht hm hxn hxd ht' hm' hylo hk hl hr hr1 hr' hout

theorem K26_dec_dir_x_full (G : Prop) (UL UH BXL BXH XL XH DL DH : ℤ) (a b early ne : ℕ)
    (HL HH CDL CDH SHL SHH T1L T1H CXL CXH SXL SXH DLq DHq : ℤ) (bad nb : ℕ) (CHL CHH z : ℤ)
    (al pa ah na0 na za bl pb bh nb0 nbg zb both t m : ℕ) (xn xd : ℤ) (nnb t' m' : ℕ) (ylo k l r : ℤ) (r1 : ℕ)
    (l2 r2 : ℤ) (t2 nbo c2 rr r' OUT : ℕ)
    (ha : a = 1 ↔ UH < 843314857) (hb : b = 1 ↔ BXH < 843314857) (hearly : early = 1 ↔ a = 1 ∧ b = 1)
    (hne : ne = 1 ↔ ¬early = 1) (hh : ∀ r : ℝ, Enc UL UH r → Enc HL HH (r / 2))
    (hcd : G ∧ ne = 1 → (0 ≤ DL ∧ DH ≤ 843314857) ∧ ∀ r : ℝ, Enc DL DH r → Enc CDL CDH (cos r))
    (hsh : G ∧ ne = 1 → (0 ≤ HL ∧ HH ≤ 843314857) ∧ ∀ r : ℝ, Enc HL HH r → Enc SHL SHH (sin r))
    (ht1 : G ∧ ne = 1 → ∀ r s : ℝ, Enc CDL CDH r → Enc SHL SHH s → Enc T1L T1H (r * s))
    (hcx : G ∧ ne = 1 → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc CXL CXH (cos r))
    (hsx : G ∧ ne = 1 → (0 ≤ XL ∧ XH ≤ 843314857) ∧ ∀ r : ℝ, Enc XL XH r → Enc SXL SXH (sin r))
    (hq : ¬bad = 1 → ∀ r s : ℝ, Enc CXL CXH r → Enc SXL SXH s →
        0 < s ∧ 0 < DLq ∧ 0 < DHq ∧ (CXL : ℝ) / DLq ≤ r / s ∧ r / s ≤ (CXH : ℝ) / DHq)
    (hnb : nb = 1 ↔ ¬bad = 1)
    (hch : (G ∧ ne = 1) ∧ nb = 1 → (0 ≤ HL ∧ HH ≤ 843314857) ∧
      ∀ r : ℝ, Enc HL HH r → Enc CHL CHH (cos r))
    (hz : z = 0) (hal : al = 1 ↔ CXL < z) (hpa : pa = 1 ↔ ¬al = 1) (hah : ah = 1 ↔ z < CXH)
    (hna0 : na0 = 1 ↔ ¬ah = 1) (hna : na = 1 ↔ na0 = 1 ∧ al = 1) (hza : za = 1 ↔ al = 1 ∧ ah = 1)
    (hbl : bl = 1 ↔ CHL < z) (hpb : pb = 1 ↔ ¬bl = 1) (hbh : bh = 1 ↔ z < CHH) (hnb0 : nb0 = 1 ↔ ¬bh = 1)
    (hnbg : nbg = 1 ↔ nb0 = 1 ∧ bl = 1) (hzb : zb = 1 ↔ bl = 1 ∧ bh = 1) (hboth : both = 1 ↔ za = 1 ∧ zb = 1)
    (ht : t = 1 ↔ pa = 1 ∧ zb = 1) (hm : m = 1 ↔ nbg = 1 ∨ t = 1) (hxn : xn = if m = 1 then CXH else CXL)
    (hxd : xd = if m = 1 then DHq else DLq) (hnnb : nnb = 1 ↔ ¬nbg = 1) (ht' : t' = 1 ↔ za = 1 ∧ nnb = 1)
    (hm' : m' = 1 ↔ na = 1 ∨ t' = 1) (hylo : ylo = if m' = 1 then CHH else CHL) (hk : k = -T1L)
    (hl : l = k * xd) (hr : r = xn * ylo) (hr1 : r1 = 1 ↔ l < r) (hl2 : l2 = k * DHq) (hr2 : r2 = CXH * CHL)
    (ht2 : t2 = 1 ↔ l2 < r2) (hnbo : nbo = 1 ↔ ¬both = 1) (hc2 : c2 = 1 ↔ nbo = 1 ∨ t2 = 1)
    (hrr : rr = 1 ↔ r1 = 1 ∧ c2 = 1) (hr' : r' = 1 ↔ rr = 1 ∧ nb = 1) (hout : OUT = 1 ↔ early = 1 ∨ r' = 1) :
    G → OUT = 1 → ∀ (d : ℝ) (Y : ℝ → ℝ), Enc DL DH d → 0 < d → d < π / 2 → (0 : ℝ) < UL →
      (∀ u : ℝ, Enc UL UH u → 0 < Y u → Y u < π → Enc XL XH (Y u) ∧ Enc BXL BXH (bangle d u + Y u)) →
      ∀ u ∈ Set.Icc ((UL : ℝ) / 2 ^ 28) (min ((UH : ℝ) / 2 ^ 28) π), 0 < Y u → Y u < π →
        0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
  exact @L2B.K26_dec_dir_x_full G UL UH BXL BXH XL XH DL DH a b early ne HL HH CDL CDH SHL SHH T1L T1H CXL CXH SXL SXH DLq DHq bad nb CHL CHH z al pa ah na0 na za bl pb bh nb0 nbg zb both t m xn xd nnb t' m' ylo k l r r1 l2 r2 t2 nbo c2 rr r' OUT ha hb hearly hne hh hcd hsh ht1 hcx hsx hq hnb hch hz hal hpa hah hna0 hna hza hbl hpb hbh hnb0 hnbg hzb hboth ht hm hxn hxd hnnb ht' hm' hylo hk hl hr hr1 hl2 hr2 ht2 hnbo hc2 hrr hr' hout

theorem K27_corner (UL UH : ℤ) (m side : ℕ) (s tp : ℤ) (lp : ℕ) (LEH pl : ℤ) (hp : ℕ) (mx HEL l h LO HI : ℤ)
    (hs : s = UL + UH) (htp : tp = 1686629712) (hlp : lp = 1 ↔ s ≤ tp) (hleh : LEH = if lp = 1 then UL else UH)
    (hpl : pl = 843314856) (hhp : hp = 1 ↔ UH ≤ pl) (hmx : mx = max UL pl) (hhel : HEL = if hp = 1 then UH else mx)
    (hl : l = if side = 1 then UL else HEL) (hh : h = if side = 1 then LEH else UH)
    (hlo : LO = if m = 1 then l else UL) (hhi : HI = if m = 1 then h else UH) :
    ∀ t : ℝ, Enc UL UH t → t ≤ π → ∃ w : ℝ, Enc LO HI w ∧ (UL : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((UH : ℝ) / 2 ^ 28) π ∧ (m = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬m = 1 → w = t) := by
  exact @L2B.K27_corner UL UH m side s tp lp LEH pl hp mx HEL l h LO HI hs htp hlp hleh hpl hhp hmx hhel hl hh hlo hhi

theorem K27_corner_fixed (UL UH : ℤ) (side : ℕ) (s tp : ℤ) (lp : ℕ) (LEH pl : ℤ) (hp : ℕ) (mx HEL LO HI : ℤ)
    (hs : s = UL + UH) (htp : tp = 1686629712) (hlp : lp = 1 ↔ s ≤ tp) (hleh : LEH = if lp = 1 then UL else UH)
    (hpl : pl = 843314856) (hhp : hp = 1 ↔ UH ≤ pl) (hmx : mx = max UL pl) (hhel : HEL = if hp = 1 then UH else mx)
    (hlo : LO = if side = 1 then HEL else UL) (hhi : HI = if side = 1 then UH else LEH) :
    ∀ t : ℝ, Enc UL UH t → t ≤ π → ∃ w : ℝ, Enc LO HI w ∧ (UL : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((UH : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t) := by
  exact @L2B.K27_corner_fixed UL UH side s tp lp LEH pl hp mx HEL LO HI hs htp hlp hleh hpl hhp hmx hhel hlo hhi

theorem K28_pent_eval_0 (G : Prop) (X0L X0H X1L X1H DL DH : ℤ) (EL EH B1L B1H FL FH B3L B3H GaL GaH TL TH OL OH : ℤ)
    (he : G → ∀ d u : ℝ, Enc DL DH d → Enc X0L X0H u → AF true EL EH (ebase d u))
    (hb1 : G → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc DL DH d → Enc X0L X0H u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : G → ∀ d u : ℝ, Enc DL DH d → Enc X1L X1H u → AF true FL FH (ebase d u))
    (hb3 : G → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc DL DH d → Enc X1L X1H u → 0 < u → u < 2 * π →
      Enc B3L B3H (bangle d u))
    (hg : G → ∀ θg θe θf : ℝ, AF false DL DH θg → AF true EL EH θe → AF true FL FH θf →
      Enc GaL GaH (gam θg θe θf))
    (ht : ∀ r s : ℝ, Enc B1L B1H r → Enc GaL GaH s → Enc TL TH (r + s))
    (ho : ∀ r s : ℝ, Enc TL TH r → Enc B3L B3H s → Enc OL OH (r + s)) :
    G → ∀ d x y : ℝ, Enc DL DH d → Enc X0L X0H x → Enc X1L X1H y → 0 < d → d < π / 2 → 0 < x → x < 2 * π →
      0 < y → y < 2 * π → Enc OL OH (pentOut 0 d x y) := by
  exact @L2B.K28_pent_eval_0 G X0L X0H X1L X1H DL DH EL EH B1L B1H FL FH B3L B3H GaL GaH TL TH OL OH he hb1 hf hb3 hg ht ho

theorem K28_pent_eval_1 (G : Prop) (X0L X0H X1L X1H DL DH : ℤ) (EL EH B1L B1H FL FH GaL GaH OL OH : ℤ)
    (he : G → ∀ d u : ℝ, Enc DL DH d → Enc X0L X0H u → AF true EL EH (ebase d u))
    (hb1 : G → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc DL DH d → Enc X0L X0H u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : G → ∀ d u : ℝ, Enc DL DH d → Enc X1L X1H u → AF true FL FH (ebase d u))
    (hg : G → ∀ θg θe θf : ℝ, AF true FL FH θg → AF true EL EH θe → AF false DL DH θf →
      Enc GaL GaH (gam θg θe θf))
    (ho : ∀ r s : ℝ, Enc B1L B1H r → Enc GaL GaH s → Enc OL OH (r + s)) :
    G → ∀ d x y : ℝ, Enc DL DH d → Enc X0L X0H x → Enc X1L X1H y → 0 < d → d < π / 2 → 0 < x → x < 2 * π →
      0 < y → y < 2 * π → Enc OL OH (pentOut 1 d x y) := by
  exact @L2B.K28_pent_eval_1 G X0L X0H X1L X1H DL DH EL EH B1L B1H FL FH GaL GaH OL OH he hb1 hf hg ho

theorem K29_claim (hi : Bool) (side : ℕ) (C OL OH : ℤ) (lo_ok hi_ok cl : ℕ) (hside : side = 1 ↔ hi = true)
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) : ∀ r : ℝ, Enc OL OH r → Claim hi ((C : ℝ) / 2 ^ 28) r := by
  have hcl1 : cl = 1 := hck trivial
  have hpos : 0 < (2 ^ 28 : ℝ) := by norm_num
  intro r ⟨hlo, hhi⟩
  simp [Claim]
  split_ifs with hhi_eq
  ·
    have hside1 : side = 1 := hside.mpr hhi_eq
    have hcl_eq : cl = hi_ok := by
      rw [hcl, ite_eq_left_of_eq_true _ _ (eq_true hside1)]
    have hhi_ok_val : hi_ok = 1 := by
      rw [← hcl_eq, hcl1]
    have hOH_le_C : OH ≤ C := hhi_ok.mp hhi_ok_val
    have hOH_le_C' : (OH : ℝ) ≤ (C : ℝ) := by exact_mod_cast hOH_le_C
    have h_mul : (2 ^ 28 : ℝ) * r ≤ (C : ℝ) := by simpa using hhi.trans hOH_le_C'
    calc
      r = ((2 ^ 28 : ℝ) * r) / (2 ^ 28 : ℝ) := by field_simp [hpos.ne']
      _ ≤ (C : ℝ) / (2 ^ 28 : ℝ) := div_le_div_of_nonneg_right h_mul hpos.le
  ·
    have hside_ne_one : side ≠ 1 := by
      intro h; apply hhi_eq; exact hside.mp h
    have hcl_eq : cl = lo_ok := by
      rw [hcl, ite_eq_right_of_eq_false _ _ (eq_false hside_ne_one)]
    have hlo_ok_val : lo_ok = 1 := by
      rw [← hcl_eq, hcl1]
    have hC_le_OL : C ≤ OL := hlo_ok.mp hlo_ok_val
    have hC_le_OL' : (C : ℝ) ≤ (OL : ℝ) := by exact_mod_cast hC_le_OL
    have h_mul : (C : ℝ) ≤ (2 ^ 28 : ℝ) * r := by simpa using hC_le_OL'.trans hlo
    calc
      (C : ℝ) / (2 ^ 28 : ℝ) ≤ ((2 ^ 28 : ℝ) * r) / (2 ^ 28 : ℝ) :=
        div_le_div_of_nonneg_right h_mul hpos.le
      _ = r := by field_simp [hpos.ne']

theorem K30_N0 (hi : Bool) (F0 F1 F2 F3 : ℕ) (hD : InDom F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C : ℤ)
    (side : ℕ) (EL EH B1L B1H FL FH B3L B3H GaL GaH TL TH OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hside : side = 1 ↔ hi = true)
    (he : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EL EH (ebase d u))
    (hb1 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true FL FH (ebase d u))
    (hb3 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc Y0 Y1 u → 0 < u → u < 2 * π →
      Enc B3L B3H (bangle d u))
    (hg : True → ∀ θg θe θf : ℝ, AF false D0 D1 θg → AF true EL EH θe → AF true FL FH θf →
      Enc GaL GaH (gam θg θe θf))
    (ht : ∀ r s : ℝ, Enc B1L B1H r → Enc GaL GaH s → Enc TL TH (r + s))
    (ho : ∀ r s : ℝ, Enc TL TH r → Enc B3L B3H s → Enc OL OH (r + s))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaim 0 hi F0 F1 F2 F3 := by
  exact @L2B.K30_N0 hi F0 F1 F2 F3 hD D0 D1 X0 X1 Y0 Y1 C side EL EH B1L B1H FL FH B3L B3H GaL GaH TL TH OL OH lo_ok hi_ok cl hD0 hD1 hX0 hX1 hY0 hY1 hC hside he hb1 hf hb3 hg ht ho hlo_ok hhi_ok hcl hck

theorem K30_N1 (hi : Bool) (F0 F1 F2 F3 : ℕ) (hD : InDom F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C : ℤ)
    (side : ℕ) (EL EH B1L B1H FL FH GaL GaH OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hside : side = 1 ↔ hi = true)
    (he : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EL EH (ebase d u))
    (hb1 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true FL FH (ebase d u))
    (hg : True → ∀ θg θe θf : ℝ, AF true FL FH θg → AF true EL EH θe → AF false D0 D1 θf →
      Enc GaL GaH (gam θg θe θf))
    (ho : ∀ r s : ℝ, Enc B1L B1H r → Enc GaL GaH s → Enc OL OH (r + s))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaim 1 hi F0 F1 F2 F3 := by
  exact @L2B.K30_N1 hi F0 F1 F2 F3 hD D0 D1 X0 X1 Y0 Y1 C side EL EH B1L B1H FL FH GaL GaH OL OH lo_ok hi_ok cl hD0 hD1 hX0 hX1 hY0 hY1 hC hside he hb1 hf hg ho hlo_ok hhi_ok hcl hck

def DirOK (UL UH BXL BXH XL XH DL DH : ℤ) (OUT : ℕ) : Prop :=
  OUT = 1 → ∀ (d : ℝ) (Y : ℝ → ℝ), Enc DL DH d → 0 < d → d < π / 2 → (0 : ℝ) < UL →
    (∀ u : ℝ, Enc UL UH u → 0 < Y u → Y u < π → Enc XL XH (Y u) ∧ Enc BXL BXH (bangle d u + Y u)) →
    ∀ u ∈ Set.Icc ((UL : ℝ) / 2 ^ 28) (min ((UH : ℝ) / 2 ^ 28) π), 0 < Y u → Y u < π →
      0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2)

theorem K31_M0 (hi : Bool) (F0 F1 F2 F3 : ℕ) (hD : InDom F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C : ℤ)
    (side : ℕ) (EL EH B1L B1H FL FH B3L B3H GPL GPH GML GMH BX0L BX0H BX1L BX1H : ℤ) (d0 d1 : ℕ)
    (P0L P0H P1L P1H OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hside : side = 1 ↔ hi = true)
    (he : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EL EH (ebase d u))
    (hb1 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true FL FH (ebase d u))
    (hb3 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc Y0 Y1 u → 0 < u → u < 2 * π →
      Enc B3L B3H (bangle d u))
    (hgp : True → ∀ θg θe θf : ℝ, AF true FL FH θg → AF true EL EH θe → AF false D0 D1 θf →
      Enc GPL GPH (gam θg θe θf))
    (hgm : True → ∀ θg θe θf : ℝ, AF true EL EH θg → AF true FL FH θe → AF false D0 D1 θf →
      Enc GML GMH (gam θg θe θf))
    (hbx0 : ∀ r s : ℝ, Enc B1L B1H r → Enc GPL GPH s → Enc BX0L BX0H (r + s))
    (hbx1 : ∀ r s : ℝ, Enc B3L B3H r → Enc GML GMH s → Enc BX1L BX1H (r + s))
    (hd0 : True → DirOK X0 X1 BX0L BX0H GPL GPH D0 D1 d0)
    (hd1 : True → DirOK Y0 Y1 BX1L BX1H GML GMH D0 D1 d1)
    (hx0 : ∀ t : ℝ, Enc X0 X1 t → t ≤ π → ∃ w : ℝ, Enc P0L P0H w ∧ (X0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((X1 : ℝ) / 2 ^ 28) π ∧ (d0 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d0 = 1 → w = t))
    (hx1 : ∀ t : ℝ, Enc Y0 Y1 t → t ≤ π → ∃ w : ℝ, Enc P1L P1H w ∧ (Y0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((Y1 : ℝ) / 2 ^ 28) π ∧ (d1 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d1 = 1 → w = t))
    (hout : True → ∀ d x y : ℝ, Enc D0 D1 d → Enc P0L P0H x → Enc P1L P1H y → 0 < d → d < π / 2 → 0 < x →
      x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (pentOut 0 d x y))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaim 0 hi F0 F1 F2 F3 := by
  exact @L2B.K31_M0 hi F0 F1 F2 F3 hD D0 D1 X0 X1 Y0 Y1 C side EL EH B1L B1H FL FH B3L B3H GPL GPH GML GMH BX0L BX0H BX1L BX1H d0 d1 P0L P0H P1L P1H OL OH lo_ok hi_ok cl hD0 hD1 hX0 hX1 hY0 hY1 hC hside he hb1 hf hb3 hgp hgm hbx0 hbx1 hd0 hd1 hx0 hx1 hout hlo_ok hhi_ok hcl hck

theorem K31_M1 (hi : Bool) (F0 F1 F2 F3 : ℕ) (hD : InDom F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C : ℤ)
    (side : ℕ) (EL EH B1L B1H FL FH GIL GIH BX0L BX0H : ℤ) (d0 : ℕ) (P0L P0H P1L P1H OL OH : ℤ)
    (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hside : side = 1 ↔ hi = true)
    (he : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EL EH (ebase d u))
    (hb1 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true FL FH (ebase d u))
    (hgi : True → ∀ θg θe θf : ℝ, AF false D0 D1 θg → AF true EL EH θe → AF true FL FH θf →
      Enc GIL GIH (gam θg θe θf))
    (hbx0 : ∀ r s : ℝ, Enc B1L B1H r → Enc GIL GIH s → Enc BX0L BX0H (r + s))
    (hd0 : True → DirOK X0 X1 BX0L BX0H GIL GIH D0 D1 d0)
    (hx0 : ∀ t : ℝ, Enc X0 X1 t → t ≤ π → ∃ w : ℝ, Enc P0L P0H w ∧ (X0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((X1 : ℝ) / 2 ^ 28) π ∧ (d0 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d0 = 1 → w = t))
    (hx1 : ∀ t : ℝ, Enc Y0 Y1 t → t ≤ π → ∃ w : ℝ, Enc P1L P1H w ∧ (Y0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((Y1 : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t))
    (hout : True → ∀ d x y : ℝ, Enc D0 D1 d → Enc P0L P0H x → Enc P1L P1H y → 0 < d → d < π / 2 → 0 < x →
      x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (pentOut 1 d x y))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaim 1 hi F0 F1 F2 F3 := by
  exact @L2B.K31_M1 hi F0 F1 F2 F3 hD D0 D1 X0 X1 Y0 Y1 C side EL EH B1L B1H FL FH GIL GIH BX0L BX0H d0 P0L P0H P1L P1H OL OH lo_ok hi_ok cl hD0 hD1 hX0 hX1 hY0 hY1 hC hside he hb1 hf hgi hbx0 hd0 hx0 hx1 hout hlo_ok hhi_ok hcl hck

theorem X1_top (w : ℕ) (h : w = 1) : True → w = 1 := fun _ => h

theorem X1_step (G : Prop) (g n c w : ℕ) (hn : n = 1 ↔ ¬g = 1) (hw : w = 1 ↔ n = 1 ∨ c = 1) (h : G → w = 1) :
    G ∧ g = 1 → c = 1 := by
  intro hG
  rcases hw.1 (h hG.1) with hn1 | hc
  · exact absurd hG.2 (hn.1 hn1)
  · exact hc

theorem X2_push (φ : ℤ → ℤ) (m : ℕ) (X A B FA FB V : ℤ) (hx : X = if m = 1 then A else B) (ha : FA = φ A)
    (hb : FB = φ B) (hv : V = if m = 1 then FA else FB) : V = φ X := by
  subst hx ha hb hv
  split_ifs <;> rfl

theorem X3_sin (X V : ℤ) (h : sinI X = V) : V = sinI X := h.symm

theorem X3_cos (X V : ℤ) (h : cosI X = V) : V = cosI X := h.symm

end D3Prog.L2
