import Tammes15.Contractors.Encl

/-!
# Soundness of the triangle angle and of the side (the two guards of Section 5.5 of the paper)

`triAngleSt` (deep.rs `tri_angle_st` with its guard) encloses the angle `gam g e f` opposite `g`
for every point of its three input intervals, or reports that no triangle exists there; `side`
encloses the side opposite an angle. Both evaluate a monotone formula at the ends of the box
selected by the signs of its partial derivatives, read from interval enclosures over the whole box
(`etaSel_upper`, `etaSel_lower`, `qSel_upper`, `qSel_lower`).
-/

namespace Tammes15.Contractors

open Real
open scoped Classical
open Tammes15 Tammes15.PaperSteps.Search

theorem eta_swap (g e f : ℝ) : eta g e f = eta g f e := by
  simp only [eta, mul_comm]

theorem etaIv_mem {R : Rnd} (hR : R.Sound) {G E F : Iv} {g e f : ℝ}
    (hg : G.Mem g) (he : E.Mem e) (hf : F.Mem f) (hs : sin e * sin f ≠ 0) :
    (R.div (R.sub (R.cos G) (R.mul (R.cos E) (R.cos F))) (R.mul (R.sin E) (R.sin F))).Mem
      (eta g e f) := by
  dsimp [eta]
  apply hR.div
  · apply hR.sub
    · apply hR.cos G g hg
    · apply hR.mul (R.cos E) (R.cos F)
      · apply hR.cos E e he
      · apply hR.cos F f hf
  · apply hR.mul (R.sin E) (R.sin F)
    · apply hR.sin E e he
    · apply hR.sin F f hf
  · exact hs

theorem inOpen_ends {R : Rnd} (hR : R.Sound) {I : Iv} {x : ℝ}
    (hI : InOpen R I) (hx : I.Mem x) :
    I.lo = .ofReal I.lo.toReal ∧ I.hi = .ofReal I.hi.toReal ∧ 0 < I.lo.toReal ∧
      I.lo.toReal ≤ x ∧ x ≤ I.hi.toReal ∧ I.hi.toReal < π := by
  rcases hI with ⟨hIlo, hIhi⟩
  rcases hx with ⟨hxlo, hxhi⟩
  have hIlo_le : Fl.le (.ofReal 0) I.lo := Fl.le_of_lt hIlo
  have hIhi_le : Fl.le I.hi (.ofReal R.piLo) := Fl.le_of_lt hIhi
  have hlo_eq : I.lo = .ofReal I.lo.toReal := Fl.eq_ofReal_toReal hIlo_le hxlo
  have hhi_eq : I.hi = .ofReal I.hi.toReal := Fl.eq_ofReal_toReal hxhi hIhi_le
  have hlo_toReal_pos : 0 < I.lo.toReal := by
    rw [hlo_eq] at hIlo
    rwa [Fl.ofReal_lt_ofReal] at hIlo
  have hlo_toReal_le_x : I.lo.toReal ≤ x :=
    (Fl.le_ofReal_toReal hIlo_le hxlo).2
  have hx_le_hi_toReal : x ≤ I.hi.toReal :=
    (Fl.le_ofReal_toReal hxhi hIhi_le).1
  have hhi_toReal_lt_pi : I.hi.toReal < π := by
    rw [hhi_eq] at hIhi
    have h := (Fl.ofReal_lt_ofReal.mp hIhi)
    have hRpi : R.piLo ≤ π := hR.piLo
    linarith
  exact ⟨hlo_eq, hhi_eq, hlo_toReal_pos, hlo_toReal_le_x, hx_le_hi_toReal, hhi_toReal_lt_pi⟩

theorem etaSel_upper {R : Rnd} (hR : R.Sound) {G E F E₁ F₁ : Iv}
    {g e f : ℝ} (hg : G.Mem g) (he : E.Mem e) (hf : F.Mem f) (hG : InOpen R G)
    (hE : InOpen R E) (hF : InOpen R F)
    (hE₁ : (Fl.lt (.ofReal 0) (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).lo ∧
        E₁ = Iv.pt E.hi) ∨
      (Fl.lt (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).hi (.ofReal 0) ∧
        E₁ = Iv.pt E.lo) ∨ E₁ = E)
    (hF₁ : (Fl.lt (.ofReal 0) (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).lo ∧
        F₁ = Iv.pt F.hi) ∨
      (Fl.lt (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).hi (.ofReal 0) ∧
        F₁ = Iv.pt F.lo) ∨ F₁ = F) :
    ∃ g' e' f', (Iv.pt G.lo).Mem g' ∧ E₁.Mem e' ∧ F₁.Mem f' ∧ G.Mem g' ∧ E.Mem e' ∧
      F.Mem f' ∧ eta g e f ≤ eta g' e' f' := by
  obtain ⟨hGl, hGh, hg0, hgl, hgh, hg1⟩ := inOpen_ends hR hG hg
  obtain ⟨hEl, hEh, he0, hel, heh, he1⟩ := inOpen_ends hR hE he
  obtain ⟨hFl, hFh, hf0, hfl, hfh, hf1⟩ := inOpen_ends hR hF hf
  set gl := G.lo.toReal
  set gh := G.hi.toReal
  set el := E.lo.toReal
  set eh := E.hi.toReal
  set fl := F.lo.toReal
  set fh := F.hi.toReal
  have memE : ∀ x, el ≤ x → x ≤ eh → E.Mem x := fun x h1 h2 => Iv.mem_of_eq hEl hEh h1 h2
  have memF : ∀ x, fl ≤ x → x ≤ fh → F.Mem x := fun x h1 h2 => Iv.mem_of_eq hFl hFh h1 h2
  have hgG : G.Mem gl := Iv.mem_of_eq hGl hGh le_rfl (hgl.trans hgh)
  have hnf : ∀ x y z, G.Mem x → E.Mem y → F.Mem z →
      (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).Mem (cos z - cos x * cos y) :=
    fun x y z hx hy hz => hR.sub _ _ _ _ (hR.cos _ _ hz) (hR.mul _ _ _ _ (hR.cos _ _ hx) (hR.cos _ _ hy))
  have hne : ∀ x y z, G.Mem x → E.Mem y → F.Mem z →
      (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).Mem (cos y - cos x * cos z) :=
    fun x y z hx hy hz => hR.sub _ _ _ _ (hR.cos _ _ hy) (hR.mul _ _ _ _ (hR.cos _ _ hx) (hR.cos _ _ hz))
  have hfI : 0 < f ∧ f < π := ⟨hf0.trans_le hfl, hfh.trans_lt hf1⟩
  have h1 : eta g e f ≤ eta gl e f :=
    (eta_strictAntiOn_g e f ⟨he0.trans_le hel, heh.trans_lt he1⟩ hfI).antitoneOn
      ⟨hg0.le, ((hgl.trans hgh).trans hg1.le)⟩ ⟨(hg0.trans_le hgl).le, (hgh.trans hg1.le)⟩ hgl
  obtain ⟨e', he'1, he'r, h2⟩ : ∃ e', E₁.Mem e' ∧ (el ≤ e' ∧ e' ≤ eh) ∧
      eta gl e f ≤ eta gl e' f := by
    rcases hE₁ with ⟨hlt, rfl⟩ | ⟨hlt, rfl⟩ | rfl
    · refine ⟨eh, by rw [hEh]; exact Iv.mem_pt, ⟨hel.trans heh, le_rfl⟩, ?_⟩
      refine eta_monotoneOn_e (g := gl) hfI he0 he1 (fun x hx => ?_) ⟨hel, heh⟩
        ⟨hel.trans heh, le_rfl⟩ heh
      have := Iv.pos_of_lt_lo hlt (hnf gl x f hgG (memE x hx.1 hx.2) hf)
      linarith [mul_comm (cos gl) (cos x)]
    · refine ⟨el, by rw [hEl]; exact Iv.mem_pt, ⟨le_rfl, hel.trans heh⟩, ?_⟩
      refine eta_antitoneOn_e (g := gl) hfI he0 he1 (fun x hx => ?_)
        ⟨le_rfl, hel.trans heh⟩ ⟨hel, heh⟩ hel
      have := Iv.neg_of_hi_lt hlt (hnf gl x f hgG (memE x hx.1 hx.2) hf)
      linarith [mul_comm (cos gl) (cos x)]
    · exact ⟨e, he, ⟨hel, heh⟩, le_rfl⟩
  have he'I : 0 < e' ∧ e' < π := ⟨he0.trans_le he'r.1, he'r.2.trans_lt he1⟩
  have he'E := memE e' he'r.1 he'r.2
  obtain ⟨f', hf'1, hf'r, h3⟩ : ∃ f', F₁.Mem f' ∧ (fl ≤ f' ∧ f' ≤ fh) ∧
      eta gl e' f ≤ eta gl e' f' := by
    rw [eta_swap gl e' f]
    rcases hF₁ with ⟨hlt, rfl⟩ | ⟨hlt, rfl⟩ | rfl
    · refine ⟨fh, by rw [hFh]; exact Iv.mem_pt, ⟨hfl.trans hfh, le_rfl⟩, ?_⟩
      rw [eta_swap gl e' fh]
      refine eta_monotoneOn_e (g := gl) he'I hf0 hf1 (fun x hx => ?_) ⟨hfl, hfh⟩
        ⟨hfl.trans hfh, le_rfl⟩ hfh
      have := Iv.pos_of_lt_lo hlt (hne gl e' x hgG he'E (memF x hx.1 hx.2))
      linarith [mul_comm (cos gl) (cos x)]
    · refine ⟨fl, by rw [hFl]; exact Iv.mem_pt, ⟨le_rfl, hfl.trans hfh⟩, ?_⟩
      rw [eta_swap gl e' fl]
      refine eta_antitoneOn_e (g := gl) he'I hf0 hf1 (fun x hx => ?_)
        ⟨le_rfl, hfl.trans hfh⟩ ⟨hfl, hfh⟩ hfl
      have := Iv.neg_of_hi_lt hlt (hne gl e' x hgG he'E (memF x hx.1 hx.2))
      linarith [mul_comm (cos gl) (cos x)]
    · exact ⟨f, hf, ⟨hfl, hfh⟩, by rw [eta_swap gl e' f]⟩
  exact ⟨gl, e', f', by rw [hGl]; exact Iv.mem_pt, he'1, hf'1, hgG, he'E,
    memF f' hf'r.1 hf'r.2, h1.trans (h2.trans h3)⟩

theorem etaSel_lower {R : Rnd} (hR : R.Sound) {G E F E₂ F₂ : Iv}
    {g e f : ℝ} (hg : G.Mem g) (he : E.Mem e) (hf : F.Mem f) (hG : InOpen R G)
    (hE : InOpen R E) (hF : InOpen R F)
    (hE₂ : (Fl.lt (.ofReal 0) (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).lo ∧
        E₂ = Iv.pt E.lo) ∨
      (Fl.lt (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).hi (.ofReal 0) ∧
        E₂ = Iv.pt E.hi) ∨ E₂ = E)
    (hF₂ : (Fl.lt (.ofReal 0) (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).lo ∧
        F₂ = Iv.pt F.lo) ∨
      (Fl.lt (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).hi (.ofReal 0) ∧
        F₂ = Iv.pt F.hi) ∨ F₂ = F) :
    ∃ g' e' f', (Iv.pt G.hi).Mem g' ∧ E₂.Mem e' ∧ F₂.Mem f' ∧ G.Mem g' ∧ E.Mem e' ∧
      F.Mem f' ∧ eta g' e' f' ≤ eta g e f := by
  -- Get the endpoints of G, E, F
  rcases inOpen_ends hR hG hg with ⟨hGlo, hGhi, hG0, hGlo_le_g, hg_le_Ghi, hGhi_lt_pi⟩
  rcases inOpen_ends hR hE he with ⟨hElo, hEhi, hE0, hElo_le_e, he_le_Ehi, hEhi_lt_pi⟩
  rcases inOpen_ends hR hF hf with ⟨hFlo, hFhi, hF0, hFlo_le_f, hf_le_Fhi, hFhi_lt_pi⟩
  set gh := G.hi.toReal with hgh_def
  set el := E.lo.toReal with hel_def
  set eh := E.hi.toReal with heh_def
  set fl := F.lo.toReal with hfl_def
  set fh := F.hi.toReal with hfh_def
  have hg_le_gh : g ≤ gh := hg_le_Ghi
  have hgh_pos : 0 < gh := by linarith
  have hgh_lt_pi : gh < π := hGhi_lt_pi
  have hel_pos : 0 < el := hE0
  have hel_lt_pi : el < π := by linarith
  have heh_pos : 0 < eh := by linarith
  have he_pos : 0 < e := by linarith
  have he_lt_pi : e < π := by linarith
  have he_le_eh : e ≤ eh := he_le_Ehi
  have hfl_pos : 0 < fl := hF0
  have hfl_lt_pi : fl < π := by linarith
  have hf_pos : 0 < f := by linarith
  have hf_lt_pi : f < π := by linarith
  have hf_le_fh : f ≤ fh := hf_le_Fhi
  -- gh is in G
  have hGh_mem : G.Mem gh := by
    rw [Iv.Mem, hGlo, hGhi]
    have h_le : Fl.le (.ofReal (G.lo.toReal)) (.ofReal gh) := by
      rw [Fl.ofReal_le_ofReal]
      linarith
    have h_le' : Fl.le (.ofReal gh) (.ofReal gh) := by
      rw [Fl.ofReal_le_ofReal]
    exact ⟨h_le, h_le'⟩
  -- E.Mem x for any x ∈ [el, eh]
  have hE_mem_of_range (x : ℝ) (hx : el ≤ x ∧ x ≤ eh) : E.Mem x := by
    rcases hx with ⟨hx1, hx2⟩
    simpa [Iv.Mem, hElo, hEhi, Fl.ofReal_le_ofReal] using And.intro hx1 hx2
  -- F.Mem x for any x ∈ [fl, fh]
  have hF_mem_of_range (x : ℝ) (hx : fl ≤ x ∧ x ≤ fh) : F.Mem x := by
    rcases hx with ⟨hx1, hx2⟩
    simpa [Iv.Mem, hFlo, hFhi, Fl.ofReal_le_ofReal] using And.intro hx1 hx2
  -- Helper: if nf contains a value and nf.lo > 0, then the real is positive
  have h_pos_of_nf_contains {a : ℝ} (hnf_pos : Fl.lt (.ofReal 0) (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).lo)
      (h_mem : (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).Mem a) : 0 < a := by
    rcases h_mem with ⟨h_mem_lo, h_mem_hi⟩
    have hlt : Fl.lt (.ofReal 0) (.ofReal a) := Fl.lt_of_lt_of_le hnf_pos h_mem_lo
    rw [Fl.ofReal_lt_ofReal] at hlt
    exact hlt
  -- Helper: if nf contains a value and nf.hi < 0, then the real is negative
  have h_neg_of_nf_contains {a : ℝ} (hnf_neg : Fl.lt (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).hi (.ofReal 0))
      (h_mem : (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).Mem a) : a < 0 := by
    rcases h_mem with ⟨h_mem_lo, h_mem_hi⟩
    have hlt : Fl.lt (.ofReal a) (.ofReal 0) := Fl.lt_of_le_of_lt h_mem_hi hnf_neg
    rw [Fl.ofReal_lt_ofReal] at hlt
    exact hlt
  -- Step 1: eta gh e f ≤ eta g e f using eta_strictAntiOn_g
  have h_step1 : eta gh e f ≤ eta g e f := by
    have h_anti : StrictAntiOn (fun g' => eta g' e f) (Set.Icc (0 : ℝ) π) :=
      eta_strictAntiOn_g e f ⟨he_pos, he_lt_pi⟩ ⟨hf_pos, hf_lt_pi⟩
    have h_anti' : AntitoneOn (fun g' => eta g' e f) (Set.Icc (0 : ℝ) π) :=
      h_anti.antitoneOn
    have hg_mem : g ∈ Set.Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
    have hgh_mem : gh ∈ Set.Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
    exact h_anti' hg_mem hgh_mem hg_le_gh
  -- Helper to get the inequality for the e-move (positive case)
  have h_nf_pos_ineq (hnf_pos : Fl.lt (.ofReal 0) (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).lo)
      (x : ℝ) (hx_lo : el ≤ x) (hx_hi : x ≤ eh) : 0 ≤ cos f - cos x * cos gh := by
    have hx_mem : E.Mem x := hE_mem_of_range x ⟨hx_lo, hx_hi⟩
    have h_cos_f_mem : (R.cos F).Mem (cos f) := hR.cos F f hf
    have h_cos_gh_mem : (R.cos G).Mem (cos gh) := hR.cos G gh hGh_mem
    have h_cos_x_mem : (R.cos E).Mem (cos x) := hR.cos E x hx_mem
    have h_mul_mem : (R.mul (R.cos G) (R.cos E)).Mem (cos gh * cos x) :=
      hR.mul (R.cos G) (R.cos E) (cos gh) (cos x) h_cos_gh_mem h_cos_x_mem
    have h_sub_mem : (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).Mem (cos f - cos gh * cos x) :=
      hR.sub (R.cos F) (R.mul (R.cos G) (R.cos E)) (cos f) (cos gh * cos x) h_cos_f_mem h_mul_mem
    have hpos := h_pos_of_nf_contains hnf_pos h_sub_mem
    linarith
  -- Helper to get the inequality for the e-move (negative case)
  have h_nf_neg_ineq (hnf_neg : Fl.lt (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).hi (.ofReal 0))
      (x : ℝ) (hx_lo : el ≤ x) (hx_hi : x ≤ eh) : cos f - cos x * cos gh ≤ 0 := by
    have hx_mem : E.Mem x := hE_mem_of_range x ⟨hx_lo, hx_hi⟩
    have h_cos_f_mem : (R.cos F).Mem (cos f) := hR.cos F f hf
    have h_cos_gh_mem : (R.cos G).Mem (cos gh) := hR.cos G gh hGh_mem
    have h_cos_x_mem : (R.cos E).Mem (cos x) := hR.cos E x hx_mem
    have h_mul_mem : (R.mul (R.cos G) (R.cos E)).Mem (cos gh * cos x) :=
      hR.mul (R.cos G) (R.cos E) (cos gh) (cos x) h_cos_gh_mem h_cos_x_mem
    have h_sub_mem : (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).Mem (cos f - cos gh * cos x) :=
      hR.sub (R.cos F) (R.mul (R.cos G) (R.cos E)) (cos f) (cos gh * cos x) h_cos_f_mem h_mul_mem
    have hneg := h_neg_of_nf_contains hnf_neg h_sub_mem
    linarith
  -- Helper to get the inequality for the f-move (positive case)
  have h_ne_pos_ineq (hne_pos : Fl.lt (.ofReal 0) (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).lo)
      (e' : ℝ) (he'_mem : E.Mem e') (x : ℝ) (hx_lo : fl ≤ x) (hx_hi : x ≤ fh) : 0 ≤ cos e' - cos x * cos gh := by
    have hx_mem : F.Mem x := hF_mem_of_range x ⟨hx_lo, hx_hi⟩
    have h_cos_e'_mem : (R.cos E).Mem (cos e') := hR.cos E e' he'_mem
    have h_cos_gh_mem : (R.cos G).Mem (cos gh) := hR.cos G gh hGh_mem
    have h_cos_x_mem : (R.cos F).Mem (cos x) := hR.cos F x hx_mem
    have h_mul_mem : (R.mul (R.cos G) (R.cos F)).Mem (cos gh * cos x) :=
      hR.mul (R.cos G) (R.cos F) (cos gh) (cos x) h_cos_gh_mem h_cos_x_mem
    have h_sub_mem : (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).Mem (cos e' - cos gh * cos x) :=
      hR.sub (R.cos E) (R.mul (R.cos G) (R.cos F)) (cos e') (cos gh * cos x) h_cos_e'_mem h_mul_mem
    have hpos : 0 < cos e' - cos x * cos gh := by
      rcases h_sub_mem with ⟨h_mem_lo, h_mem_hi⟩
      have hlt : Fl.lt (.ofReal 0) (.ofReal (cos e' - cos x * cos gh)) :=
        Fl.lt_of_lt_of_le hne_pos (by simpa [mul_comm] using h_mem_lo)
      rw [Fl.ofReal_lt_ofReal] at hlt
      exact hlt
    linarith
  -- Helper to get the inequality for the f-move (negative case)
  have h_ne_neg_ineq (hne_neg : Fl.lt (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).hi (.ofReal 0))
      (e' : ℝ) (he'_mem : E.Mem e') (x : ℝ) (hx_lo : fl ≤ x) (hx_hi : x ≤ fh) : cos e' - cos x * cos gh ≤ 0 := by
    have hx_mem : F.Mem x := hF_mem_of_range x ⟨hx_lo, hx_hi⟩
    have h_cos_e'_mem : (R.cos E).Mem (cos e') := hR.cos E e' he'_mem
    have h_cos_gh_mem : (R.cos G).Mem (cos gh) := hR.cos G gh hGh_mem
    have h_cos_x_mem : (R.cos F).Mem (cos x) := hR.cos F x hx_mem
    have h_mul_mem : (R.mul (R.cos G) (R.cos F)).Mem (cos gh * cos x) :=
      hR.mul (R.cos G) (R.cos F) (cos gh) (cos x) h_cos_gh_mem h_cos_x_mem
    have h_sub_mem : (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).Mem (cos e' - cos gh * cos x) :=
      hR.sub (R.cos E) (R.mul (R.cos G) (R.cos F)) (cos e') (cos gh * cos x) h_cos_e'_mem h_mul_mem
    have hneg : cos e' - cos x * cos gh < 0 := by
      rcases h_sub_mem with ⟨h_mem_lo, h_mem_hi⟩
      have hlt : Fl.lt (.ofReal (cos e' - cos x * cos gh)) (.ofReal 0) :=
        Fl.lt_of_le_of_lt (by simpa [mul_comm] using h_mem_hi) hne_neg
      rw [Fl.ofReal_lt_ofReal] at hlt
      exact hlt
    linarith
  -- Now handle e' based on hE₂
  rcases hE₂ with (⟨hnf_pos, hE₂_eq⟩ | ⟨hnf_neg, hE₂_eq⟩ | hE₂_eq)
  · -- Case: 0 < nf.lo and E₂ = Iv.pt E.lo, set e' := el
    have he'_mem : E.Mem el := hE_mem_of_range el ⟨le_rfl, hElo_le_e.trans he_le_Ehi⟩
    have h_eta_e_step : eta gh el f ≤ eta gh e f := by
      have h_mono : MonotoneOn (fun e' => eta gh e' f) (Set.Icc el eh) :=
        eta_monotoneOn_e ⟨hf_pos, hf_lt_pi⟩ hel_pos hEhi_lt_pi (fun x hx => by
          rcases hx with ⟨hx_lo, hx_hi⟩
          exact h_nf_pos_ineq hnf_pos x hx_lo hx_hi)
      have hel_mem : el ∈ Set.Icc el eh := ⟨le_rfl, hElo_le_e.trans he_le_Ehi⟩
      have he_mem : e ∈ Set.Icc el eh := ⟨hElo_le_e, he_le_Ehi⟩
      exact h_mono hel_mem he_mem hElo_le_e
    -- Now handle f' based on hF₂
    rcases hF₂ with (⟨hne_pos, hF₂_eq⟩ | ⟨hne_neg, hF₂_eq⟩ | hF₂_eq)
    · -- F₂ = Iv.pt F.lo, set f' := fl
      have h_eta_f_step : eta gh el fl ≤ eta gh el f := by
        rw [eta_swap gh el fl, eta_swap gh el f]
        have h_mono : MonotoneOn (fun x => eta gh x el) (Set.Icc fl fh) :=
          eta_monotoneOn_e ⟨hel_pos, hel_lt_pi⟩ hfl_pos hFhi_lt_pi (fun x hx => by
            rcases hx with ⟨hx_lo, hx_hi⟩
            exact h_ne_pos_ineq hne_pos el he'_mem x hx_lo hx_hi)
        have hfl_mem : fl ∈ Set.Icc fl fh := ⟨le_rfl, hFlo_le_f.trans hf_le_fh⟩
        have hf_mem : f ∈ Set.Icc fl fh := ⟨hFlo_le_f, hf_le_fh⟩
        exact h_mono hfl_mem hf_mem hFlo_le_f
      refine ⟨gh, el, fl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hGhi] using Iv.mem_pt (x := gh)
      · rw [hE₂_eq]; simpa [hElo] using Iv.mem_pt (x := el)
      · rw [hF₂_eq]; simpa [hFlo] using Iv.mem_pt (x := fl)
      · exact hGh_mem
      · exact he'_mem
      · exact hF_mem_of_range fl ⟨le_rfl, hFlo_le_f.trans hf_le_fh⟩
      · linarith
    · -- F₂ = Iv.pt F.hi, set f' := fh
      have h_eta_f_step : eta gh el fh ≤ eta gh el f := by
        rw [eta_swap gh el fh, eta_swap gh el f]
        have h_anti : AntitoneOn (fun x => eta gh x el) (Set.Icc fl fh) :=
          eta_antitoneOn_e ⟨hel_pos, hel_lt_pi⟩ hfl_pos hFhi_lt_pi (fun x hx => by
            rcases hx with ⟨hx_lo, hx_hi⟩
            exact h_ne_neg_ineq hne_neg el he'_mem x hx_lo hx_hi)
        have hf_mem : f ∈ Set.Icc fl fh := ⟨hFlo_le_f, hf_le_fh⟩
        have hfh_mem : fh ∈ Set.Icc fl fh := ⟨hFlo_le_f.trans hf_le_fh, le_rfl⟩
        exact h_anti hf_mem hfh_mem hf_le_fh
      refine ⟨gh, el, fh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hGhi] using Iv.mem_pt (x := gh)
      · rw [hE₂_eq]; simpa [hElo] using Iv.mem_pt (x := el)
      · rw [hF₂_eq]; simpa [hFhi] using Iv.mem_pt (x := fh)
      · exact hGh_mem
      · exact he'_mem
      · exact hF_mem_of_range fh ⟨hFlo_le_f.trans hf_le_fh, le_rfl⟩
      · linarith
    · -- F₂ = F, set f' := f
      refine ⟨gh, el, f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hGhi] using Iv.mem_pt (x := gh)
      · rw [hE₂_eq]; simpa [hElo] using Iv.mem_pt (x := el)
      · rw [hF₂_eq]; exact hf
      · exact hGh_mem
      · exact he'_mem
      · exact hf
      · linarith
  · -- Case: nf.hi < 0 and E₂ = Iv.pt E.hi, set e' := eh
    have he'_mem : E.Mem eh := hE_mem_of_range eh ⟨hElo_le_e.trans he_le_Ehi, le_rfl⟩
    have h_eta_e_step : eta gh eh f ≤ eta gh e f := by
      have h_anti : AntitoneOn (fun e' => eta gh e' f) (Set.Icc el eh) :=
        eta_antitoneOn_e ⟨hf_pos, hf_lt_pi⟩ hel_pos hEhi_lt_pi (fun x hx => by
          rcases hx with ⟨hx_lo, hx_hi⟩
          exact h_nf_neg_ineq hnf_neg x hx_lo hx_hi)
      have he_mem : e ∈ Set.Icc el eh := ⟨hElo_le_e, he_le_Ehi⟩
      have heh_mem : eh ∈ Set.Icc el eh := ⟨hElo_le_e.trans he_le_Ehi, le_rfl⟩
      exact h_anti he_mem heh_mem he_le_eh
    -- Now handle f' based on hF₂
    rcases hF₂ with (⟨hne_pos, hF₂_eq⟩ | ⟨hne_neg, hF₂_eq⟩ | hF₂_eq)
    · -- F₂ = Iv.pt F.lo, set f' := fl
      have h_eta_f_step : eta gh eh fl ≤ eta gh eh f := by
        rw [eta_swap gh eh fl, eta_swap gh eh f]
        have h_mono : MonotoneOn (fun x => eta gh x eh) (Set.Icc fl fh) :=
          eta_monotoneOn_e ⟨heh_pos, hEhi_lt_pi⟩ hfl_pos hFhi_lt_pi (fun x hx => by
            rcases hx with ⟨hx_lo, hx_hi⟩
            exact h_ne_pos_ineq hne_pos eh he'_mem x hx_lo hx_hi)
        have hfl_mem : fl ∈ Set.Icc fl fh := ⟨le_rfl, hFlo_le_f.trans hf_le_fh⟩
        have hf_mem : f ∈ Set.Icc fl fh := ⟨hFlo_le_f, hf_le_fh⟩
        exact h_mono hfl_mem hf_mem hFlo_le_f
      refine ⟨gh, eh, fl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hGhi] using Iv.mem_pt (x := gh)
      · rw [hE₂_eq]; simpa [hEhi] using Iv.mem_pt (x := eh)
      · rw [hF₂_eq]; simpa [hFlo] using Iv.mem_pt (x := fl)
      · exact hGh_mem
      · exact he'_mem
      · exact hF_mem_of_range fl ⟨le_rfl, hFlo_le_f.trans hf_le_fh⟩
      · linarith
    · -- F₂ = Iv.pt F.hi, set f' := fh
      have h_eta_f_step : eta gh eh fh ≤ eta gh eh f := by
        rw [eta_swap gh eh fh, eta_swap gh eh f]
        have h_anti : AntitoneOn (fun x => eta gh x eh) (Set.Icc fl fh) :=
          eta_antitoneOn_e ⟨heh_pos, hEhi_lt_pi⟩ hfl_pos hFhi_lt_pi (fun x hx => by
            rcases hx with ⟨hx_lo, hx_hi⟩
            exact h_ne_neg_ineq hne_neg eh he'_mem x hx_lo hx_hi)
        have hf_mem : f ∈ Set.Icc fl fh := ⟨hFlo_le_f, hf_le_fh⟩
        have hfh_mem : fh ∈ Set.Icc fl fh := ⟨hFlo_le_f.trans hf_le_fh, le_rfl⟩
        exact h_anti hf_mem hfh_mem hf_le_fh
      refine ⟨gh, eh, fh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hGhi] using Iv.mem_pt (x := gh)
      · rw [hE₂_eq]; simpa [hEhi] using Iv.mem_pt (x := eh)
      · rw [hF₂_eq]; simpa [hFhi] using Iv.mem_pt (x := fh)
      · exact hGh_mem
      · exact he'_mem
      · exact hF_mem_of_range fh ⟨hFlo_le_f.trans hf_le_fh, le_rfl⟩
      · linarith
    · -- F₂ = F, set f' := f
      refine ⟨gh, eh, f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hGhi] using Iv.mem_pt (x := gh)
      · rw [hE₂_eq]; simpa [hEhi] using Iv.mem_pt (x := eh)
      · rw [hF₂_eq]; exact hf
      · exact hGh_mem
      · exact he'_mem
      · exact hf
      · linarith
  · -- Case: E₂ = E, set e' := e
    have he'_mem : E.Mem e := he
    have h_eta_e_step : eta gh e f ≤ eta gh e f := le_rfl
    -- Now handle f' based on hF₂
    rcases hF₂ with (⟨hne_pos, hF₂_eq⟩ | ⟨hne_neg, hF₂_eq⟩ | hF₂_eq)
    · -- F₂ = Iv.pt F.lo, set f' := fl
      have h_eta_f_step : eta gh e fl ≤ eta gh e f := by
        rw [eta_swap gh e fl, eta_swap gh e f]
        have h_mono : MonotoneOn (fun x => eta gh x e) (Set.Icc fl fh) :=
          eta_monotoneOn_e ⟨he_pos, he_lt_pi⟩ hfl_pos hFhi_lt_pi (fun x hx => by
            rcases hx with ⟨hx_lo, hx_hi⟩
            exact h_ne_pos_ineq hne_pos e he'_mem x hx_lo hx_hi)
        have hfl_mem : fl ∈ Set.Icc fl fh := ⟨le_rfl, hFlo_le_f.trans hf_le_fh⟩
        have hf_mem : f ∈ Set.Icc fl fh := ⟨hFlo_le_f, hf_le_fh⟩
        exact h_mono hfl_mem hf_mem hFlo_le_f
      refine ⟨gh, e, fl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hGhi] using Iv.mem_pt (x := gh)
      · rw [hE₂_eq]; exact he
      · rw [hF₂_eq]; simpa [hFlo] using Iv.mem_pt (x := fl)
      · exact hGh_mem
      · exact he'_mem
      · exact hF_mem_of_range fl ⟨le_rfl, hFlo_le_f.trans hf_le_fh⟩
      · linarith
    · -- F₂ = Iv.pt F.hi, set f' := fh
      have h_eta_f_step : eta gh e fh ≤ eta gh e f := by
        rw [eta_swap gh e fh, eta_swap gh e f]
        have h_anti : AntitoneOn (fun x => eta gh x e) (Set.Icc fl fh) :=
          eta_antitoneOn_e ⟨he_pos, he_lt_pi⟩ hfl_pos hFhi_lt_pi (fun x hx => by
            rcases hx with ⟨hx_lo, hx_hi⟩
            exact h_ne_neg_ineq hne_neg e he'_mem x hx_lo hx_hi)
        have hf_mem : f ∈ Set.Icc fl fh := ⟨hFlo_le_f, hf_le_fh⟩
        have hfh_mem : fh ∈ Set.Icc fl fh := ⟨hFlo_le_f.trans hf_le_fh, le_rfl⟩
        exact h_anti hf_mem hfh_mem hf_le_fh
      refine ⟨gh, e, fh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hGhi] using Iv.mem_pt (x := gh)
      · rw [hE₂_eq]; exact he
      · rw [hF₂_eq]; simpa [hFhi] using Iv.mem_pt (x := fh)
      · exact hGh_mem
      · exact he'_mem
      · exact hF_mem_of_range fh ⟨hFlo_le_f.trans hf_le_fh, le_rfl⟩
      · linarith
    · -- F₂ = F, set f' := f
      refine ⟨gh, e, f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hGhi] using Iv.mem_pt (x := gh)
      · rw [hE₂_eq]; exact he
      · rw [hF₂_eq]; exact hf
      · exact hGh_mem
      · exact he'_mem
      · exact hf
      · linarith

theorem q_antitoneOn {c κ a b : ℝ}
    (hs : ∀ x ∈ Set.Icc a b, 0 ≤ sin x * cos c - cos x * sin c * κ) :
    AntitoneOn (fun x => cos x * cos c + sin x * sin c * κ) (Set.Icc a b) := by
  have hderiv (x : ℝ) : HasDerivAt (fun x => cos x * cos c + sin x * sin c * κ) (-(sin x * cos c - cos x * sin c * κ)) x := by
    have hcos := (Real.hasDerivAt_cos x).mul_const (cos c)
    have hsin := (Real.hasDerivAt_sin x).mul_const (sin c * κ)
    have hsum := hcos.add hsin
    convert hsum using 1
    · ext y; simp [mul_assoc]
    · ring
  have hcont : ContinuousOn (fun x => cos x * cos c + sin x * sin c * κ) (Set.Icc a b) := by
    refine ((Real.continuous_cos.continuousOn.mul continuousOn_const).add ?_)
    exact (Real.continuous_sin.continuousOn.mul continuousOn_const).mul continuousOn_const
  have hdiff : DifferentiableOn ℝ (fun x => cos x * cos c + sin x * sin c * κ) (interior (Set.Icc a b)) := by
    refine DifferentiableOn.add ?_ ?_
    · exact (Real.differentiable_cos.differentiableOn.mul_const (cos c))
    · simpa [mul_assoc] using (Real.differentiable_sin.differentiableOn.mul_const (sin c * κ))
  have hderiv_nonpos : ∀ x ∈ interior (Set.Icc a b), deriv (fun x => cos x * cos c + sin x * sin c * κ) x ≤ 0 := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self (by rwa [interior_Icc] at hx)
    have h_nonneg : 0 ≤ sin x * cos c - cos x * sin c * κ := hs x hx'
    have h_deriv : HasDerivAt (fun x => cos x * cos c + sin x * sin c * κ) (-(sin x * cos c - cos x * sin c * κ)) x := hderiv x
    have h_deriv_eq : deriv (fun x => cos x * cos c + sin x * sin c * κ) x = -(sin x * cos c - cos x * sin c * κ) :=
      h_deriv.deriv
    rw [h_deriv_eq]
    linarith
  exact antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont hdiff hderiv_nonpos

theorem q_monotoneOn {c κ a b : ℝ}
    (hs : ∀ x ∈ Set.Icc a b, sin x * cos c - cos x * sin c * κ ≤ 0) :
    MonotoneOn (fun x => cos x * cos c + sin x * sin c * κ) (Set.Icc a b) := by
  set f := fun x : ℝ => cos x * cos c + sin x * sin c * κ
  have hf_cont : ContinuousOn f (Set.Icc a b) := by
    have hcos : ContinuousOn cos (Set.Icc a b) := Real.continuous_cos.continuousOn
    have hsin : ContinuousOn sin (Set.Icc a b) := Real.continuous_sin.continuousOn
    have hc : ContinuousOn (fun _ : ℝ => cos c) (Set.Icc a b) := continuousOn_const
    have hs' : ContinuousOn (fun _ : ℝ => sin c) (Set.Icc a b) := continuousOn_const
    have hk : ContinuousOn (fun _ : ℝ => κ) (Set.Icc a b) := continuousOn_const
    have h1 : ContinuousOn (fun x : ℝ => cos x * cos c) (Set.Icc a b) := hcos.mul hc
    have h2 : ContinuousOn (fun x : ℝ => sin x * sin c) (Set.Icc a b) := hsin.mul hs'
    have h3 : ContinuousOn (fun x : ℝ => (sin x * sin c) * κ) (Set.Icc a b) := h2.mul hk
    exact h1.add h3
  have hf_diff : DifferentiableOn ℝ f (interior (Set.Icc a b)) := by
    intro x hx
    have hcos : DifferentiableAt ℝ cos x := Real.differentiableAt_cos
    have hsin : DifferentiableAt ℝ sin x := Real.differentiableAt_sin
    have h1 : DifferentiableAt ℝ (fun x : ℝ => cos x * cos c) x :=
      hcos.mul_const (cos c)
    have h2 : DifferentiableAt ℝ (fun x : ℝ => sin x * sin c * κ) x := by
      have h := hsin.mul_const (sin c)
      exact h.mul_const κ
    exact (h1.add h2).differentiableWithinAt
  have hderiv (x : ℝ) : HasDerivAt f (-(sin x * cos c - cos x * sin c * κ)) x := by
    have hcos : HasDerivAt (fun x : ℝ => cos x * cos c) ((-sin x) * cos c) x :=
      (Real.hasDerivAt_cos x).mul_const (cos c)
    have hsin : HasDerivAt (fun x : ℝ => sin x * sin c * κ) (cos x * sin c * κ) x := by
      have h := (Real.hasDerivAt_sin x).mul_const (sin c)
      exact h.mul_const κ
    have hsum : HasDerivAt f ((-sin x) * cos c + cos x * sin c * κ) x :=
      hcos.add hsin
    have hsimpl : (-sin x) * cos c + cos x * sin c * κ = -(sin x * cos c - cos x * sin c * κ) := by ring
    rw [hsimpl] at hsum
    exact hsum
  have hderiv_nonneg : ∀ x ∈ interior (Set.Icc a b), 0 ≤ deriv f x := by
    intro x hx
    rw [(hderiv x).deriv]
    have hx' : x ∈ Set.Icc a b := interior_subset hx
    have h := hs x hx'
    linarith
  exact monotoneOn_of_deriv_nonneg (convex_Icc a b) hf_cont hf_diff hderiv_nonneg

theorem qSel_upper {R : Rnd} (hR : R.Sound) {bl bh cl ch b c κ : ℝ}
    {CA B₁ C₁ : Iv} (hb : bl ≤ b ∧ b ≤ bh) (hc : cl ≤ c ∧ c ≤ ch) (hκ : CA.Mem κ)
    (hB₁ : (Fl.lt (.ofReal 0) (R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
          (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CA)).lo ∧
        B₁ = Iv.pt (.ofReal bl)) ∨
      (Fl.lt (R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
          (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CA)).hi (.ofReal 0) ∧
        B₁ = Iv.pt (.ofReal bh)) ∨ B₁ = Iv.ofReal bl bh)
    (hC₁ : (Fl.lt (.ofReal 0) (R.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
          (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CA)).lo ∧
        C₁ = Iv.pt (.ofReal cl)) ∨
      (Fl.lt (R.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
          (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CA)).hi (.ofReal 0) ∧
        C₁ = Iv.pt (.ofReal ch)) ∨ C₁ = Iv.ofReal cl ch) :
    ∃ b' c', B₁.Mem b' ∧ C₁.Mem c' ∧ (bl ≤ b' ∧ b' ≤ bh) ∧ (cl ≤ c' ∧ c' ≤ ch) ∧
      cos b * cos c + sin b * sin c * κ ≤ cos b' * cos c' + sin b' * sin c' * κ := by
  rcases hb with ⟨hbl, hbh⟩
  rcases hc with ⟨hcl, hch⟩
  rcases hκ with ⟨hκl, hκh⟩
  have hblbh : bl ≤ bh := hbl.trans hbh
  have hclch : cl ≤ ch := hcl.trans hch
  have hb_mem : b ∈ Set.Icc bl bh := ⟨hbl, hbh⟩
  have hc_mem : c ∈ Set.Icc cl ch := ⟨hcl, hch⟩
  set sb := R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
    (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CA) with hsb_def
  set sc := R.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
    (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CA) with hsc_def
  have h_sb_mem (x y : ℝ) (hx : x ∈ Set.Icc bl bh) (hy : y ∈ Set.Icc cl ch) :
      sb.Mem (sin x * cos y - cos x * sin y * κ) := by
    rcases hx with ⟨hxl, hxr⟩
    rcases hy with ⟨hyl, hyr⟩
    have hx_mem : (Iv.ofReal bl bh).Mem x := Iv.mem_ofReal.mpr ⟨hxl, hxr⟩
    have hy_mem : (Iv.ofReal cl ch).Mem y := Iv.mem_ofReal.mpr ⟨hyl, hyr⟩
    have hsinx : (R.sin (Iv.ofReal bl bh)).Mem (sin x) := hR.sin (Iv.ofReal bl bh) x hx_mem
    have hsiny : (R.sin (Iv.ofReal cl ch)).Mem (sin y) := hR.sin (Iv.ofReal cl ch) y hy_mem
    have hcosx : (R.cos (Iv.ofReal bl bh)).Mem (cos x) := hR.cos (Iv.ofReal bl bh) x hx_mem
    have hcosy : (R.cos (Iv.ofReal cl ch)).Mem (cos y) := hR.cos (Iv.ofReal cl ch) y hy_mem
    have h1 : (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch))).Mem (sin x * cos y) :=
      hR.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)) (sin x) (cos y) hsinx hcosy
    have h2 : (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))).Mem (cos x * sin y) :=
      hR.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch)) (cos x) (sin y) hcosx hsiny
    have h3 : (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CA).Mem
        ((cos x * sin y) * κ) :=
      hR.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CA (cos x * sin y) κ h2 ⟨hκl, hκh⟩
    have hmem := hR.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
      (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CA)
      (sin x * cos y) ((cos x * sin y) * κ) h1 h3
    -- hmem : sb.Mem (sin x * cos y - ((cos x * sin y) * κ))
    -- which is syntactically the same as sin x * cos y - cos x * sin y * κ
    simpa [mul_assoc] using hmem
  have h_sc_mem (x y : ℝ) (hx : x ∈ Set.Icc bl bh) (hy : y ∈ Set.Icc cl ch) :
      sc.Mem (sin y * cos x - cos y * sin x * κ) := by
    rcases hx with ⟨hxl, hxr⟩
    rcases hy with ⟨hyl, hyr⟩
    have hx_mem : (Iv.ofReal bl bh).Mem x := Iv.mem_ofReal.mpr ⟨hxl, hxr⟩
    have hy_mem : (Iv.ofReal cl ch).Mem y := Iv.mem_ofReal.mpr ⟨hyl, hyr⟩
    have hsinx : (R.sin (Iv.ofReal cl ch)).Mem (sin y) := hR.sin (Iv.ofReal cl ch) y hy_mem
    have hsiny : (R.sin (Iv.ofReal bl bh)).Mem (sin x) := hR.sin (Iv.ofReal bl bh) x hx_mem
    have hcosx : (R.cos (Iv.ofReal cl ch)).Mem (cos y) := hR.cos (Iv.ofReal cl ch) y hy_mem
    have hcosy : (R.cos (Iv.ofReal bl bh)).Mem (cos x) := hR.cos (Iv.ofReal bl bh) x hx_mem
    have h1 : (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh))).Mem (sin y * cos x) :=
      hR.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)) (sin y) (cos x) hsinx hcosy
    have h2 : (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))).Mem (cos y * sin x) :=
      hR.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh)) (cos y) (sin x) hcosx hsiny
    have h3 : (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CA).Mem
        ((cos y * sin x) * κ) :=
      hR.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CA (cos y * sin x) κ h2 ⟨hκl, hκh⟩
    have hmem := hR.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
      (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CA)
      (sin y * cos x) ((cos y * sin x) * κ) h1 h3
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmem
  have pos_of_flt_lo {I : Iv} {x : ℝ} (hlt : Fl.lt (.ofReal (0 : ℝ)) I.lo) (hmem : I.Mem x) : 0 < x := by
    rcases hmem with ⟨hle1, hle2⟩
    have hlt' : Fl.lt (.ofReal (0 : ℝ)) (Fl.ofReal x) := Fl.lt_of_lt_of_le hlt hle1
    exact (Fl.ofReal_lt_ofReal.mp hlt')
  have neg_of_flt_hi {I : Iv} {x : ℝ} (hlt : Fl.lt I.hi (.ofReal (0 : ℝ))) (hmem : I.Mem x) : x < 0 := by
    rcases hmem with ⟨hle1, hle2⟩
    have hlt' : Fl.lt (Fl.ofReal x) (.ofReal (0 : ℝ)) := Fl.lt_of_le_of_lt hle2 hlt
    exact (Fl.ofReal_lt_ofReal.mp hlt')
  rcases hB₁ with (hB₁ | hB₁ | hB₁)
  · -- case: Fl.lt (.ofReal 0) sb.lo ∧ B₁ = Iv.pt (.ofReal bl)
    rcases hB₁ with ⟨hsb_lt, hB₁_eq⟩
    have hpos : ∀ x ∈ Set.Icc bl bh, 0 ≤ sin x * cos c - cos x * sin c * κ := by
      intro x hx
      have hmem := h_sb_mem x c hx hc_mem
      exact le_of_lt (pos_of_flt_lo hsb_lt hmem)
    have h_anti : AntitoneOn (fun x => cos x * cos c + sin x * sin c * κ) (Set.Icc bl bh) :=
      q_antitoneOn hpos
    have hQb_le_Qbl : cos b * cos c + sin b * sin c * κ ≤ cos bl * cos c + sin bl * sin c * κ :=
      h_anti (Set.left_mem_Icc.mpr hblbh) hb_mem hbl
    rcases hC₁ with (hC₁ | hC₁ | hC₁)
    · -- case: Fl.lt (.ofReal 0) sc.lo ∧ C₁ = Iv.pt (.ofReal cl)
      rcases hC₁ with ⟨hsc_lt, hC₁_eq⟩
      have hpos' : ∀ y ∈ Set.Icc cl ch, 0 ≤ sin y * cos bl - cos y * sin bl * κ := by
        intro y hy
        have hmem := h_sc_mem bl y (Set.left_mem_Icc.mpr hblbh) hy
        -- hmem : sc.Mem (sin y * cos bl - cos y * sin bl * κ)
        -- but wait, h_sc_mem uses x for bl..bh and y for cl..ch
        -- h_sc_mem bl y hb_mem hy gives sc.Mem (sin y * cos bl - cos y * sin bl * κ)
        exact le_of_lt (pos_of_flt_lo hsc_lt hmem)
      have h_anti' : AntitoneOn (fun y => cos y * cos bl + sin y * sin bl * κ) (Set.Icc cl ch) :=
        q_antitoneOn hpos'
      have hQbl_le_Qbcl : cos bl * cos c + sin bl * sin c * κ ≤ cos bl * cos cl + sin bl * sin cl * κ := by
        simpa [mul_comm] using h_anti' (Set.left_mem_Icc.mpr hclch) hc_mem hcl
      refine ⟨bl, cl, ?_, ?_, ⟨le_refl bl, hbl.trans hbh⟩, ⟨le_refl cl, hcl.trans hch⟩, ?_⟩
      · -- B₁.Mem bl
        rw [hB₁_eq]
        exact Iv.mem_pt
      · -- C₁.Mem cl
        rw [hC₁_eq]
        exact Iv.mem_pt
      · -- Q(b,c) ≤ Q(bl,cl)
        linarith
    · -- case: Fl.lt sc.hi (.ofReal 0) ∧ C₁ = Iv.pt (.ofReal ch)
      rcases hC₁ with ⟨hsc_lt, hC₁_eq⟩
      have hneg' : ∀ y ∈ Set.Icc cl ch, sin y * cos bl - cos y * sin bl * κ ≤ 0 := by
        intro y hy
        have hmem := h_sc_mem bl y (Set.left_mem_Icc.mpr hblbh) hy
        exact le_of_lt (neg_of_flt_hi hsc_lt hmem)
      have h_mono' : MonotoneOn (fun y => cos y * cos bl + sin y * sin bl * κ) (Set.Icc cl ch) :=
        q_monotoneOn hneg'
      have hQbl_le_Qbch : cos bl * cos c + sin bl * sin c * κ ≤ cos bl * cos ch + sin bl * sin ch * κ := by
        simpa [mul_comm] using h_mono' hc_mem (Set.right_mem_Icc.mpr hclch) hch
      refine ⟨bl, ch, ?_, ?_, ⟨le_refl bl, hbl.trans hbh⟩, ⟨hcl.trans hch, le_refl ch⟩, ?_⟩
      · rw [hB₁_eq]; exact Iv.mem_pt
      · rw [hC₁_eq]; exact Iv.mem_pt
      · linarith
    · -- case: C₁ = Iv.ofReal cl ch
      have hQbl_le_Qbc : cos bl * cos c + sin bl * sin c * κ ≤ cos bl * cos c + sin bl * sin c * κ :=
        le_refl _
      refine ⟨bl, c, ?_, ?_, ⟨le_refl bl, hbl.trans hbh⟩, ⟨hcl, hch⟩, ?_⟩
      · rw [hB₁_eq]; exact Iv.mem_pt
      · rw [hC₁]
        exact Iv.mem_ofReal.mpr ⟨hcl, hch⟩
      · linarith
  · -- case: Fl.lt sb.hi (.ofReal 0) ∧ B₁ = Iv.pt (.ofReal bh)
    rcases hB₁ with ⟨hsb_lt, hB₁_eq⟩
    have hneg : ∀ x ∈ Set.Icc bl bh, sin x * cos c - cos x * sin c * κ ≤ 0 := by
      intro x hx
      have hmem := h_sb_mem x c hx hc_mem
      exact le_of_lt (neg_of_flt_hi hsb_lt hmem)
    have h_mono : MonotoneOn (fun x => cos x * cos c + sin x * sin c * κ) (Set.Icc bl bh) :=
      q_monotoneOn hneg
    have hQb_le_Qbh : cos b * cos c + sin b * sin c * κ ≤ cos bh * cos c + sin bh * sin c * κ :=
      h_mono hb_mem (Set.right_mem_Icc.mpr hblbh) hbh
    rcases hC₁ with (hC₁ | hC₁ | hC₁)
    · -- case: Fl.lt (.ofReal 0) sc.lo ∧ C₁ = Iv.pt (.ofReal cl)
      rcases hC₁ with ⟨hsc_lt, hC₁_eq⟩
      have hpos' : ∀ y ∈ Set.Icc cl ch, 0 ≤ sin y * cos bh - cos y * sin bh * κ := by
        intro y hy
        have hmem := h_sc_mem bh y (Set.right_mem_Icc.mpr hblbh) hy
        exact le_of_lt (pos_of_flt_lo hsc_lt hmem)
      have h_anti' : AntitoneOn (fun y => cos y * cos bh + sin y * sin bh * κ) (Set.Icc cl ch) :=
        q_antitoneOn hpos'
      have hQbh_le_Qbhcl : cos bh * cos c + sin bh * sin c * κ ≤ cos bh * cos cl + sin bh * sin cl * κ := by
        simpa [mul_comm] using h_anti' (Set.left_mem_Icc.mpr hclch) hc_mem hcl
      refine ⟨bh, cl, ?_, ?_, ⟨hbl.trans hbh, le_refl bh⟩, ⟨le_refl cl, hcl.trans hch⟩, ?_⟩
      · rw [hB₁_eq]; exact Iv.mem_pt
      · rw [hC₁_eq]; exact Iv.mem_pt
      · linarith
    · -- case: Fl.lt sc.hi (.ofReal 0) ∧ C₁ = Iv.pt (.ofReal ch)
      rcases hC₁ with ⟨hsc_lt, hC₁_eq⟩
      have hneg' : ∀ y ∈ Set.Icc cl ch, sin y * cos bh - cos y * sin bh * κ ≤ 0 := by
        intro y hy
        have hmem := h_sc_mem bh y (Set.right_mem_Icc.mpr hblbh) hy
        exact le_of_lt (neg_of_flt_hi hsc_lt hmem)
      have h_mono' : MonotoneOn (fun y => cos y * cos bh + sin y * sin bh * κ) (Set.Icc cl ch) :=
        q_monotoneOn hneg'
      have hQbh_le_Qbhch : cos bh * cos c + sin bh * sin c * κ ≤ cos bh * cos ch + sin bh * sin ch * κ := by
        simpa [mul_comm] using h_mono' hc_mem (Set.right_mem_Icc.mpr hclch) hch
      refine ⟨bh, ch, ?_, ?_, ⟨hbl.trans hbh, le_refl bh⟩, ⟨hcl.trans hch, le_refl ch⟩, ?_⟩
      · rw [hB₁_eq]; exact Iv.mem_pt
      · rw [hC₁_eq]; exact Iv.mem_pt
      · linarith
    · -- case: C₁ = Iv.ofReal cl ch
      have hQbh_le_Qbhc : cos bh * cos c + sin bh * sin c * κ ≤ cos bh * cos c + sin bh * sin c * κ :=
        le_refl _
      refine ⟨bh, c, ?_, ?_, ⟨hbl.trans hbh, le_refl bh⟩, ⟨hcl, hch⟩, ?_⟩
      · rw [hB₁_eq]; exact Iv.mem_pt
      · rw [hC₁]
        exact Iv.mem_ofReal.mpr ⟨hcl, hch⟩
      · linarith
  · -- case: B₁ = Iv.ofReal bl bh
    rcases hB₁ with hB₁_eq
    have hQb_le_Qb : cos b * cos c + sin b * sin c * κ ≤ cos b * cos c + sin b * sin c * κ :=
      le_refl _
    rcases hC₁ with (hC₁ | hC₁ | hC₁)
    · -- case: Fl.lt (.ofReal 0) sc.lo ∧ C₁ = Iv.pt (.ofReal cl)
      rcases hC₁ with ⟨hsc_lt, hC₁_eq⟩
      have hpos' : ∀ y ∈ Set.Icc cl ch, 0 ≤ sin y * cos b - cos y * sin b * κ := by
        intro y hy
        have hmem := h_sc_mem b y hb_mem hy
        exact le_of_lt (pos_of_flt_lo hsc_lt hmem)
      have h_anti' : AntitoneOn (fun y => cos y * cos b + sin y * sin b * κ) (Set.Icc cl ch) :=
        q_antitoneOn hpos'
      have hQb_le_Qbcl : cos b * cos c + sin b * sin c * κ ≤ cos b * cos cl + sin b * sin cl * κ := by
        simpa [mul_comm] using h_anti' (Set.left_mem_Icc.mpr hclch) hc_mem hcl
      refine ⟨b, cl, ?_, ?_, ⟨hbl, hbh⟩, ⟨le_refl cl, hcl.trans hch⟩, ?_⟩
      · rw [hB₁]
        exact Iv.mem_ofReal.mpr ⟨hbl, hbh⟩
      · rw [hC₁_eq]; exact Iv.mem_pt
      · linarith
    · -- case: Fl.lt sc.hi (.ofReal 0) ∧ C₁ = Iv.pt (.ofReal ch)
      rcases hC₁ with ⟨hsc_lt, hC₁_eq⟩
      have hneg' : ∀ y ∈ Set.Icc cl ch, sin y * cos b - cos y * sin b * κ ≤ 0 := by
        intro y hy
        have hmem := h_sc_mem b y hb_mem hy
        exact le_of_lt (neg_of_flt_hi hsc_lt hmem)
      have h_mono' : MonotoneOn (fun y => cos y * cos b + sin y * sin b * κ) (Set.Icc cl ch) :=
        q_monotoneOn hneg'
      have hQb_le_Qbch : cos b * cos c + sin b * sin c * κ ≤ cos b * cos ch + sin b * sin ch * κ := by
        simpa [mul_comm] using h_mono' hc_mem (Set.right_mem_Icc.mpr hclch) hch
      refine ⟨b, ch, ?_, ?_, ⟨hbl, hbh⟩, ⟨hcl.trans hch, le_refl ch⟩, ?_⟩
      · rw [hB₁]
        exact Iv.mem_ofReal.mpr ⟨hbl, hbh⟩
      · rw [hC₁_eq]; exact Iv.mem_pt
      · linarith
    · -- case: C₁ = Iv.ofReal cl ch
      refine ⟨b, c, ?_, ?_, ⟨hbl, hbh⟩, ⟨hcl, hch⟩, ?_⟩
      · rw [hB₁]
        exact Iv.mem_ofReal.mpr ⟨hbl, hbh⟩
      · rw [hC₁]
        exact Iv.mem_ofReal.mpr ⟨hcl, hch⟩
      · rfl

/-- The sign test of deep.rs `side` for the side `b` (with the roles exchanged, for `c`): its
interval holds `sin x cos y - cos x sin y κ` at every point of the box. -/
theorem sideSign_mem {R : Rnd} (hR : R.Sound) {bl bh cl ch κ x y : ℝ} {CA : Iv} (hκ : CA.Mem κ)
    (hx : x ∈ Set.Icc bl bh) (hy : y ∈ Set.Icc cl ch) :
    (R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
      (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CA)).Mem
        (sin x * cos y - cos x * sin y * κ) := by
  have hx' : (Iv.ofReal bl bh).Mem x := Iv.mem_ofReal.mpr hx
  have hy' : (Iv.ofReal cl ch).Mem y := Iv.mem_ofReal.mpr hy
  exact hR.sub _ _ _ _ (hR.mul _ _ _ _ (hR.sin _ _ hx') (hR.cos _ _ hy'))
    (hR.mul _ _ _ _ (hR.mul _ _ _ _ (hR.cos _ _ hx') (hR.sin _ _ hy')) hκ)

theorem qSel_lower {R : Rnd} (hR : R.Sound) {bl bh cl ch b c κ : ℝ}
    {CA B₂ C₂ : Iv} (hb : bl ≤ b ∧ b ≤ bh) (hc : cl ≤ c ∧ c ≤ ch) (hκ : CA.Mem κ)
    (hB₂ : (Fl.lt (.ofReal 0) (R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
          (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CA)).lo ∧
        B₂ = Iv.pt (.ofReal bh)) ∨
      (Fl.lt (R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
          (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CA)).hi (.ofReal 0) ∧
        B₂ = Iv.pt (.ofReal bl)) ∨ B₂ = Iv.ofReal bl bh)
    (hC₂ : (Fl.lt (.ofReal 0) (R.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
          (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CA)).lo ∧
        C₂ = Iv.pt (.ofReal ch)) ∨
      (Fl.lt (R.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
          (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CA)).hi (.ofReal 0) ∧
        C₂ = Iv.pt (.ofReal cl)) ∨ C₂ = Iv.ofReal cl ch) :
    ∃ b' c', B₂.Mem b' ∧ C₂.Mem c' ∧ (bl ≤ b' ∧ b' ≤ bh) ∧ (cl ≤ c' ∧ c' ≤ ch) ∧
      cos b' * cos c' + sin b' * sin c' * κ ≤ cos b * cos c + sin b * sin c * κ := by
  obtain ⟨hbl, hbh⟩ := hb
  obtain ⟨hcl, hch⟩ := hc
  have hb' : b ∈ Set.Icc bl bh := ⟨hbl, hbh⟩
  have hc' : c ∈ Set.Icc cl ch := ⟨hcl, hch⟩
  have hbb : bl ≤ bh := hbl.trans hbh
  have hcc : cl ≤ ch := hcl.trans hch
  obtain ⟨b', hB, hbr, h1⟩ : ∃ b', B₂.Mem b' ∧ (bl ≤ b' ∧ b' ≤ bh) ∧
      cos b' * cos c + sin b' * sin c * κ ≤ cos b * cos c + sin b * sin c * κ := by
    rcases hB₂ with ⟨hlt, rfl⟩ | ⟨hlt, rfl⟩ | rfl
    · refine ⟨bh, Iv.mem_pt, ⟨hbb, le_rfl⟩, ?_⟩
      exact q_antitoneOn (fun x hx => (Iv.pos_of_lt_lo hlt (sideSign_mem hR hκ hx hc')).le)
        hb' ⟨hbb, le_rfl⟩ hbh
    · refine ⟨bl, Iv.mem_pt, ⟨le_rfl, hbb⟩, ?_⟩
      exact q_monotoneOn (fun x hx => (Iv.neg_of_hi_lt hlt (sideSign_mem hR hκ hx hc')).le)
        ⟨le_rfl, hbb⟩ hb' hbl
    · exact ⟨b, Iv.mem_ofReal.mpr ⟨hbl, hbh⟩, ⟨hbl, hbh⟩, le_rfl⟩
  have hb'' : b' ∈ Set.Icc bl bh := hbr
  obtain ⟨c', hC, hcr, h2⟩ : ∃ c', C₂.Mem c' ∧ (cl ≤ c' ∧ c' ≤ ch) ∧
      cos c' * cos b' + sin c' * sin b' * κ ≤ cos c * cos b' + sin c * sin b' * κ := by
    rcases hC₂ with ⟨hlt, rfl⟩ | ⟨hlt, rfl⟩ | rfl
    · refine ⟨ch, Iv.mem_pt, ⟨hcc, le_rfl⟩, ?_⟩
      exact q_antitoneOn (fun y hy => (Iv.pos_of_lt_lo hlt (sideSign_mem hR hκ hy hb'')).le)
        hc' ⟨hcc, le_rfl⟩ hch
    · refine ⟨cl, Iv.mem_pt, ⟨le_rfl, hcc⟩, ?_⟩
      exact q_monotoneOn (fun y hy => (Iv.neg_of_hi_lt hlt (sideSign_mem hR hκ hy hb'')).le)
        ⟨le_rfl, hcc⟩ hc' hcl
    · exact ⟨c, Iv.mem_ofReal.mpr ⟨hcl, hch⟩, ⟨hcl, hch⟩, le_rfl⟩
  refine ⟨b', c', hB, hC, hbr, hcr, ?_⟩
  have e1 : cos b' * cos c' + sin b' * sin c' * κ = cos c' * cos b' + sin c' * sin b' * κ := by
    ring
  have e2 : cos b' * cos c + sin b' * sin c * κ = cos c * cos b' + sin c * sin b' * κ := by ring
  linarith

theorem zeroPi_mem {R : Rnd} (hR : R.Sound) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ π) :
    (⟨.ofReal 0, .ofReal R.piHi⟩ : Iv).Mem s :=
  ⟨Fl.ofReal_le_ofReal.mpr hs0, Fl.ofReal_le_ofReal.mpr (hs1.trans hR.piHi)⟩

/-- The final enclosure of deep.rs `tri_angle_st` and `side`: the arc cosines at the clamped ends
of an interval that holds `y`. -/
theorem acosEnds_mem {R : Rnd} (hR : R.Sound) {U L : Fl} {y : ℝ} (hU : Fl.le (.ofReal y) U)
    (hL : Fl.le L (.ofReal y)) (hU1 : ¬ Fl.lt U (.ofReal (-1))) (hL1 : ¬ Fl.lt (.ofReal 1) L) :
    (⟨Fl.max (R.acos (Iv.pt (Fl.min U (.ofReal 1)))).lo (.ofReal 0),
      (R.acos (Iv.pt (Fl.max L (.ofReal (-1))))).hi⟩ : Iv).Mem (arccos y) := by
  obtain ⟨r, hr, hr1, hr2, hr3⟩ := Fl.min_one_eq hU hU1
  obtain ⟨r', hr', hr1', hr2', hr3'⟩ := Fl.max_neg_one_eq hL hL1
  have ha := hR.acos (Iv.pt (.ofReal r)) r Iv.mem_pt hr1 hr2
  have hb := hR.acos (Iv.pt (.ofReal r')) r' Iv.mem_pt hr1' hr2'
  have e1 : arccos (min y 1) = arccos y := by
    rcases le_total y 1 with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Real.arccos_one, Real.arccos_of_one_le h]
  have e2 : arccos (max y (-1)) = arccos y := by
    rcases le_total y (-1) with h | h
    · rw [max_eq_right h, Real.arccos_neg_one, Real.arccos_of_le_neg_one h]
    · rw [max_eq_left h]
  rw [hr, hr']
  refine ⟨Fl.max_le (Fl.le_trans ha.1 (Fl.ofReal_le_ofReal.mpr ?_))
    (Fl.ofReal_le_ofReal.mpr (Real.arccos_nonneg _)), Fl.le_trans (Fl.ofReal_le_ofReal.mpr ?_) hb.2⟩
  · rw [← e1]; exact Real.arccos_le_arccos hr3
  · rw [← e2]; exact Real.arccos_le_arccos hr3'

theorem qc_mem {R : Rnd} (hR : R.Sound) {B C K : Iv} {x y k : ℝ} (hx : B.Mem x) (hy : C.Mem y)
    (hk : K.Mem k) :
    (R.add (R.mul (R.cos B) (R.cos C)) (R.mul (R.mul (R.sin B) (R.sin C)) K)).Mem
      (cos x * cos y + sin x * sin y * k) :=
  hR.add _ _ _ _ (hR.mul _ _ _ _ (hR.cos _ _ hx) (hR.cos _ _ hy))
    (hR.mul _ _ _ _ (hR.mul _ _ _ _ (hR.sin _ _ hx) (hR.sin _ _ hy)) hk)

theorem ite3_pair {P Q : Prop} [Decidable P] [Decidable Q] (x₁ x₂ y₁ y₂ z : Iv) :
    ((P ∧ (if P then (x₁, x₂) else if Q then (y₁, y₂) else (z, z)).1 = x₁) ∨
        (Q ∧ (if P then (x₁, x₂) else if Q then (y₁, y₂) else (z, z)).1 = y₁) ∨
        (if P then (x₁, x₂) else if Q then (y₁, y₂) else (z, z)).1 = z) ∧
      ((P ∧ (if P then (x₁, x₂) else if Q then (y₁, y₂) else (z, z)).2 = x₂) ∨
        (Q ∧ (if P then (x₁, x₂) else if Q then (y₁, y₂) else (z, z)).2 = y₂) ∨
        (if P then (x₁, x₂) else if Q then (y₁, y₂) else (z, z)).2 = z) := by
  by_cases hP : P
  · simp [hP]
  · by_cases hQ : Q <;> simp [hP, hQ]

theorem side_sound {R : Rnd} (hR : R.Sound) {bl bh cl ch b c A s : ℝ}
    {Ang : Iv} (hb : bl ≤ b ∧ b ≤ bh) (hc : cl ≤ c ∧ c ≤ ch) (hb0 : 0 ≤ bl) (hb1 : bh ≤ π)
    (hc0 : 0 ≤ cl) (hc1 : ch ≤ π) (hA : Ang.Mem A) (hA0 : 0 ≤ A) (hA1 : A ≤ π) (hs0 : 0 ≤ s)
    (hs1 : s ≤ π) (hcos : cos s = cos b * cos c + sin b * sin c * cos A) :
    ∃ I, side R (Iv.ofReal bl bh) (Iv.ofReal cl ch) Ang = some I ∧ I.Mem s := by
  -- the clamped angle
  have haA : (⟨Fl.max Ang.lo (.ofReal 0), Fl.min Ang.hi (.ofReal R.piHi)⟩ : Iv).Mem A :=
    ⟨Fl.max_le hA.1 (Fl.ofReal_le_ofReal.mpr hA0),
      Fl.le_min hA.2 (Fl.ofReal_le_ofReal.mpr (hA1.trans hR.piHi))⟩
  have haA1 : Fl.le (Fl.max Ang.lo (.ofReal 0)) (.ofReal A) := haA.1
  have haA2 : Fl.le (.ofReal A) (Fl.min Ang.hi (.ofReal R.piHi)) := haA.2
  have hale : Fl.le (Fl.max Ang.lo (.ofReal 0)) (Fl.min Ang.hi (.ofReal R.piHi)) :=
    Fl.le_trans haA1 haA2
  have hlo0 : Fl.le (.ofReal 0) (Fl.max Ang.lo (.ofReal 0)) := Fl.le_max_right (by simp [Fl.ofReal])
  obtain ⟨hal0, halA⟩ := Fl.le_ofReal_toReal hlo0 haA1
  have hal := Fl.eq_ofReal_toReal hlo0 haA1
  set al := (Fl.max Ang.lo (.ofReal 0)).toReal
  have hcA : (R.cos ⟨Fl.max Ang.lo (.ofReal 0), Fl.min Ang.hi (.ofReal R.piHi)⟩).Mem (cos A) :=
    hR.cos _ _ haA
  -- the third argument of the lower value
  have hK : ∃ k, (if Fl.le (.ofReal R.piLo) (Fl.min Ang.hi (.ofReal R.piHi)) then
      Iv.pt (.ofReal (-1)) else R.cos (Iv.pt (Fl.min Ang.hi (.ofReal R.piHi)))).Mem k ∧
        k ≤ cos A := by
    split_ifs with h
    · exact ⟨-1, Iv.mem_pt, neg_one_le_cos A⟩
    · have hhi : Fl.le (Fl.min Ang.hi (.ofReal R.piHi)) (.ofReal R.piHi) :=
        Fl.min_le_right (by simp [Fl.ofReal])
      have he := Fl.eq_ofReal_toReal haA2 hhi
      obtain ⟨hAh, -⟩ := Fl.le_ofReal_toReal haA2 hhi
      have hlt : (Fl.min Ang.hi (.ofReal R.piHi)).toReal < R.piLo := by
        by_contra hn
        exact h (by rw [he]; exact Fl.ofReal_le_ofReal.mpr (not_lt.mp hn))
      refine ⟨cos (Fl.min Ang.hi (.ofReal R.piHi)).toReal, ?_, ?_⟩
      · rw [he]; exact hR.cos _ _ Iv.mem_pt
      · exact Real.cos_le_cos_of_nonneg_of_le_pi hA0 (hlt.le.trans hR.piLo) hAh
  have hpi1 : Fl.le (.ofReal (-1)) (.ofReal (cos s)) := Fl.ofReal_le_ofReal.mpr (neg_one_le_cos s)
  have hpi2 : Fl.le (.ofReal (cos s)) (.ofReal 1) := Fl.ofReal_le_ofReal.mpr (cos_le_one s)
  have hal' : (Iv.pt (Fl.max Ang.lo (.ofReal 0))).Mem al := by rw [hal]; exact Iv.mem_pt
  unfold side
  dsimp only
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not.mpr hale))]
  set CAa := R.cos (⟨Fl.max Ang.lo (.ofReal 0), Fl.min Ang.hi (.ofReal R.piHi)⟩ : Iv) with hCAa
  obtain ⟨hB1, hB2⟩ := ite3_pair
    (P := Fl.lt (.ofReal 0) (R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
      (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CAa)).lo)
    (Q := Fl.lt (R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
      (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CAa)).hi (.ofReal 0))
    (Iv.pt (Iv.ofReal bl bh).lo) (Iv.pt (Iv.ofReal bl bh).hi) (Iv.pt (Iv.ofReal bl bh).hi)
    (Iv.pt (Iv.ofReal bl bh).lo) (Iv.ofReal bl bh)
  obtain ⟨hC1, hC2⟩ := ite3_pair
    (P := Fl.lt (.ofReal 0) (R.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
      (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CAa)).lo)
    (Q := Fl.lt (R.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
      (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CAa)).hi (.ofReal 0))
    (Iv.pt (Iv.ofReal cl ch).lo) (Iv.pt (Iv.ofReal cl ch).hi) (Iv.pt (Iv.ofReal cl ch).hi)
    (Iv.pt (Iv.ofReal cl ch).lo) (Iv.ofReal cl ch)
  generalize (if Fl.lt (.ofReal 0) (R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
      (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CAa)).lo then
      (Iv.pt (Iv.ofReal bl bh).lo, Iv.pt (Iv.ofReal bl bh).hi)
    else if Fl.lt (R.sub (R.mul (R.sin (Iv.ofReal bl bh)) (R.cos (Iv.ofReal cl ch)))
      (R.mul (R.mul (R.cos (Iv.ofReal bl bh)) (R.sin (Iv.ofReal cl ch))) CAa)).hi (.ofReal 0) then
      (Iv.pt (Iv.ofReal bl bh).hi, Iv.pt (Iv.ofReal bl bh).lo)
    else (Iv.ofReal bl bh, Iv.ofReal bl bh)) = bb at hB1 hB2 ⊢
  generalize (if Fl.lt (.ofReal 0) (R.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
      (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CAa)).lo then
      (Iv.pt (Iv.ofReal cl ch).lo, Iv.pt (Iv.ofReal cl ch).hi)
    else if Fl.lt (R.sub (R.mul (R.sin (Iv.ofReal cl ch)) (R.cos (Iv.ofReal bl bh)))
      (R.mul (R.mul (R.cos (Iv.ofReal cl ch)) (R.sin (Iv.ofReal bl bh))) CAa)).hi (.ofReal 0) then
      (Iv.pt (Iv.ofReal cl ch).hi, Iv.pt (Iv.ofReal cl ch).lo)
    else (Iv.ofReal cl ch, Iv.ofReal cl ch)) = cc at hC1 hC2 ⊢
  obtain ⟨k, hk, hkA⟩ := hK
  generalize (if Fl.le (.ofReal R.piLo) (Fl.min Ang.hi (.ofReal R.piHi)) then
      Iv.pt (.ofReal (-1)) else R.cos (Iv.pt (Fl.min Ang.hi (.ofReal R.piHi)))) = K at hk ⊢
  -- upper value
  obtain ⟨b₁, c₁, hb₁, hc₁, hb₁r, hc₁r, hQ₁⟩ := qSel_upper hR hb hc hcA hB1 hC1
  have hq₁ := qc_mem hR hb₁ hc₁ (hR.cos _ _ hal')
  have hU : Fl.le (.ofReal (cos s))
      (R.add (R.mul (R.cos bb.1) (R.cos cc.1))
        (R.mul (R.mul (R.sin bb.1) (R.sin cc.1)) (R.cos (Iv.pt (Fl.max Ang.lo (.ofReal 0)))))).hi := by
    refine Fl.le_trans (Fl.ofReal_le_ofReal.mpr ?_) hq₁.2
    have h1 : 0 ≤ sin b₁ * sin c₁ :=
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (hb0.trans hb₁r.1) (hb₁r.2.trans hb1))
        (Real.sin_nonneg_of_nonneg_of_le_pi (hc0.trans hc₁r.1) (hc₁r.2.trans hc1))
    have h2 : cos A ≤ cos al := Real.cos_le_cos_of_nonneg_of_le_pi hal0 hA1 halA
    rw [hcos]
    nlinarith [mul_le_mul_of_nonneg_left h2 h1]
  -- lower value
  obtain ⟨b₂, c₂, hb₂, hc₂, hb₂r, hc₂r, hQ₂⟩ := qSel_lower hR hb hc hcA hB2 hC2
  have hq₂ := qc_mem hR hb₂ hc₂ hk
  have hL : Fl.le (R.add (R.mul (R.cos bb.2) (R.cos cc.2))
        (R.mul (R.mul (R.sin bb.2) (R.sin cc.2)) K)).lo (.ofReal (cos s)) := by
    refine Fl.le_trans hq₂.1 (Fl.ofReal_le_ofReal.mpr ?_)
    have h1 : 0 ≤ sin b₂ * sin c₂ :=
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (hb0.trans hb₂r.1) (hb₂r.2.trans hb1))
        (Real.sin_nonneg_of_nonneg_of_le_pi (hc0.trans hc₂r.1) (hc₂r.2.trans hc1))
    rw [hcos]
    nlinarith [mul_le_mul_of_nonneg_left hkA h1]
  split_ifs
  · exact ⟨_, rfl, zeroPi_mem hR hs0 hs1⟩
  · refine ⟨_, rfl, ?_⟩
    rw [← Real.arccos_cos hs0 hs1]
    exact acosEnds_mem hR hU hL (Fl.not_lt_of_le (Fl.le_trans hpi1 hU))
      (Fl.not_lt_of_le (Fl.le_trans hL hpi2))

theorem triAngleSt_mem {R : Rnd} (hR : R.Sound) {G E F : Iv}
    {g e f : ℝ} (hg : G.Mem g) (he : E.Mem e) (hf : F.Mem f) :
    (∃ I, triAngleSt R G E F = .ok I ∧ I.Mem (gam g e f)) ∨
      (∃ I, triAngleSt R G E F = .error I ∧ I.Mem (gam g e f) ∧
        (eta g e f < -1 ∨ 1 < eta g e f)) := by
  have hgam : 0 ≤ gam g e f ∧ gam g e f ≤ π := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  by_cases hin : InOpen R G ∧ InOpen R E ∧ InOpen R F
  swap
  · left
    refine ⟨_, ?_, zeroPi_mem hR hgam.1 hgam.2⟩
    unfold triAngleSt
    simp only [hin, not_false_eq_true, ↓reduceIte]
  obtain ⟨hG, hE, hF⟩ := hin
  unfold triAngleSt
  dsimp only
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not.mpr ⟨hG, hE, hF⟩))]
  obtain ⟨hE1, hE2⟩ := ite3_pair
    (P := Fl.lt (.ofReal 0) (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).lo)
    (Q := Fl.lt (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).hi (.ofReal 0))
    (Iv.pt E.hi) (Iv.pt E.lo) (Iv.pt E.lo) (Iv.pt E.hi) E
  obtain ⟨hF1, hF2⟩ := ite3_pair
    (P := Fl.lt (.ofReal 0) (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).lo)
    (Q := Fl.lt (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).hi (.ofReal 0))
    (Iv.pt F.hi) (Iv.pt F.lo) (Iv.pt F.lo) (Iv.pt F.hi) F
  generalize (if Fl.lt (.ofReal 0) (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).lo then
      (Iv.pt E.hi, Iv.pt E.lo)
    else if Fl.lt (R.sub (R.cos F) (R.mul (R.cos G) (R.cos E))).hi (.ofReal 0) then
      (Iv.pt E.lo, Iv.pt E.hi)
    else (E, E)) = ee at hE1 hE2 ⊢
  generalize (if Fl.lt (.ofReal 0) (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).lo then
      (Iv.pt F.hi, Iv.pt F.lo)
    else if Fl.lt (R.sub (R.cos E) (R.mul (R.cos G) (R.cos F))).hi (.ofReal 0) then
      (Iv.pt F.lo, Iv.pt F.hi)
    else (F, F)) = ff at hF1 hF2 ⊢
  obtain ⟨g₁, e₁, f₁, hg₁, he₁, hf₁, -, he₁E, hf₁F, hle₁⟩ :=
    etaSel_upper hR hg he hf hG hE hF hE1 hF1
  obtain ⟨g₂, e₂, f₂, hg₂, he₂, hf₂, -, he₂E, hf₂F, hle₂⟩ :=
    etaSel_lower hR hg he hf hG hE hF hE2 hF2
  have hsin : ∀ {x y : ℝ}, E.Mem x → F.Mem y → sin x * sin y ≠ 0 := by
    intro x y hx hy
    obtain ⟨-, -, hx0, hxl, hxh, hx1⟩ := inOpen_ends hR hE hx
    obtain ⟨-, -, hy0, hyl, hyh, hy1⟩ := inOpen_ends hR hF hy
    exact (mul_pos (Real.sin_pos_of_pos_of_lt_pi (hx0.trans_le hxl) (hxh.trans_lt hx1))
      (Real.sin_pos_of_pos_of_lt_pi (hy0.trans_le hyl) (hyh.trans_lt hy1))).ne'
  have hU := Fl.le_trans (Fl.ofReal_le_ofReal.mpr hle₁) (etaIv_mem hR hg₁ he₁ hf₁ (hsin he₁E hf₁F)).2
  have hL := Fl.le_trans (etaIv_mem hR hg₂ he₂ hf₂ (hsin he₂E hf₂F)).1 (Fl.ofReal_le_ofReal.mpr hle₂)
  split_ifs with c1 c2 c3
  · exact Or.inl ⟨_, rfl, zeroPi_mem hR hgam.1 hgam.2⟩
  · have h : eta g e f < -1 := Fl.ofReal_lt_ofReal.mp (Fl.lt_of_le_of_lt hU c2)
    refine Or.inr ⟨_, rfl, ?_, Or.inl h⟩
    rw [gam, Real.arccos_of_le_neg_one h.le]
    exact ⟨Fl.ofReal_le_ofReal.mpr hR.piLo, Fl.ofReal_le_ofReal.mpr hR.piHi⟩
  · have h : 1 < eta g e f := Fl.ofReal_lt_ofReal.mp (Fl.lt_of_lt_of_le c3 hL)
    refine Or.inr ⟨_, rfl, ?_, Or.inr h⟩
    rw [gam, Real.arccos_of_one_le h.le]
    exact Iv.mem_pt
  · exact Or.inl ⟨_, rfl, acosEnds_mem hR hU hL c2 c3⟩

end Tammes15.Contractors
