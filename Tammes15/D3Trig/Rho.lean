import Tammes15.D3Trig.RhoSpec

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel Tammes15.D3Kernel.Pent Tammes15.D3Kernel.KForm

def jR (s : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 1 3 (Nat.beq (Nat.land s 2) 2)

def okR (k : Fin 2) (hi : Bool) (g box it : ℕ) : Bool :=
  let c := Ctx.code g
  let e := fk it 75 127
  let s := fk it 82 7
  let t := fk it 64 127
  let o := Nat.shiftRight t 1
  let xv := fk it 85 63
  let yv := fk it 91 63
  let dv := fk it 97 63
  let nv := Ctx.nv g
  let my := 2 + c.faceIter e (jR s)
  Nat.blt e c.D && Nat.beq (c.period e) 4 && Nat.ble s 3 &&
  Nat.beq (k : ℕ) (Nat.land s 1) &&
  Nat.beq (Nat.land t 1) (@Bool.rec (fun _ => ℕ) 0 1 hi) &&
  Nat.blt dv nv && Nat.blt xv nv && Nat.blt yv nv && Nat.blt o nv &&
  Nat.beq (Ctx.mean g dv) 1 &&
  Nat.beq (Ctx.mean g xv) (2 + c.faceIter e 0) &&
  Nat.beq (Ctx.mean g yv) my &&
  Nat.beq (Ctx.mean g o) (@Bool.rec (fun _ => ℕ) my 1 (Nat.beq (k : ℕ) 1)) &&
  kok (bk box (2 * dv)) && kok (bk box (2 * dv + 1)) && kok (bk box (2 * xv)) && kok (bk box (2 * xv + 1)) &&
  kok (bk box (2 * yv)) && kok (bk box (2 * yv + 1)) && kok (Nat.land it 18446744073709551615) &&
  inDomB (lf box dv) (lf box xv) (lf box yv) (claim it)

def okRK (k : Fin 2) (hi : Bool) (g box it : ℕ) : Bool :=
  let face := Nat.shiftRight g 64
  let e := fk it 75 127
  let s := fk it 82 7
  let t := fk it 64 127
  let o := Nat.shiftRight t 1
  let xv := fk it 85 63
  let yv := fk it 91 63
  let dv := fk it 97 63
  let nv := nvCK g
  let my := Nat.add 2 (iterK face e (jR s))
  Nat.blt e (DK g) && Nat.beq (periodK face e) 4 && Nat.ble s 3 &&
  Nat.beq (k : ℕ) (Nat.land s 1) &&
  Nat.beq (Nat.land t 1) (@Bool.rec (fun _ => ℕ) 0 1 hi) &&
  Nat.blt dv nv && Nat.blt xv nv && Nat.blt yv nv && Nat.blt o nv &&
  Nat.beq (meanK g dv) 1 &&
  Nat.beq (meanK g xv) (Nat.add 2 (iterK face e 0)) &&
  Nat.beq (meanK g yv) my &&
  Nat.beq (meanK g o) (@Bool.rec (fun _ => ℕ) my 1 (Nat.beq (k : ℕ) 1)) &&
  kokK (bk box (Nat.shiftLeft dv 1)) && kokK (bk box (Nat.add (Nat.shiftLeft dv 1) 1)) &&
  kokK (bk box (Nat.shiftLeft xv 1)) && kokK (bk box (Nat.add (Nat.shiftLeft xv 1) 1)) &&
  kokK (bk box (Nat.shiftLeft yv 1)) && kokK (bk box (Nat.add (Nat.shiftLeft yv 1) 1)) &&
  kokK (Nat.land it 18446744073709551615) &&
  inDomBK (lf box dv) (lf box xv) (lf box yv) (claim it)

theorem okRK_eq (k : Fin 2) (hi : Bool) (g box it : ℕ) : okRK k hi g box it = okR k hi g box it := by
  have he : fk it 75 127 < 256 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hs : ∀ v, Nat.shiftLeft v 1 = 2 * v := fun v => by
    show v <<< 1 = 2 * v
    rw [Nat.shiftLeft_eq]; ring
  have hD : (Ctx.code g).D = Ctx.D g := rfl
  unfold okRK okR
  simp only [nvCK_eq, DK_eq, meanK_eq, periodK_eq g _ he, iterK_eq g _ _ he, inDomBK_eq, kokK_eq, hs, hD,
    Nat.add_eq]

def ProgOKR (k : Fin 2) (hi : Bool) (prog : Prog) : Prop :=
  ∀ (n F0 F1 F2 F3 : ℕ) (hs : List ℕ) (v : ℕ),
    (∀ i < n, InDom (lane F0 i) (lane F1 i) (lane F2 i) (lane F3 i)) →
      Nat.beq (prog (oN n) F0 F1 F2 F3 hs) v = true → ∀ l < n, lane v l = 1 →
        LaneClaimR k hi (lane F0 l) (lane F1 l) (lane F2 l) (lane F3 l)

def progCheckerR (k : Fin 2) (hi : Bool) (prog : Prog) : Checker where
  σ := ℕ × ℕ × ℕ × ℕ × ℕ × Bool
  H := List ℕ
  init := (0, 0, 0, 0, 0, true)
  onRec g box it s :=
    let sh := Nat.shiftLeft s.1 (nat_lit 6)
    (Nat.add s.1 1,
      Nat.add s.2.1 (Nat.shiftLeft (lf box (fk it 97 63)) sh),
      Nat.add s.2.2.1 (Nat.shiftLeft (lf box (fk it 85 63)) sh),
      Nat.add s.2.2.2.1 (Nat.shiftLeft (lf box (fk it 91 63)) sh),
      Nat.add s.2.2.2.2.1 (Nat.shiftLeft (claim it) sh),
      s.2.2.2.2.2 && okRK k hi g box it)
  onKill _ _ _ s := (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, false)
  fin s hs := s.2.2.2.2.2 && Nat.beq (prog (oN s.1) s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 hs) (oN s.1)
  frc s k := @Bool.rec (fun _ => List ℕ) (k s) (k s)
    (Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0)
  frc_eq s k := by
    cases Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0 <;> rfl

def rIdx (it : ℕ) : ℕ := Nat.add (Nat.shiftLeft (Nat.land (fk it 82 7) 1) 1) (fk it 64 1)

def rhoChecker (progs : ℕ → Prog) : Checker :=
  btree (fun i => if i < 4 then progCheckerR (kOf i) (hiOf i) (progs i) else Checker.none) rIdx 2 0

theorem jR_cases (s : ℕ) : jR s = 1 ∨ jR s = 3 := by
  unfold jR
  cases Nat.beq (Nat.land s 2) 2 <;> simp

theorem recOK_of_rho {k : Fin 2} {hi : Bool} {g box it : ℕ} (hok : okR k hi g box it = true)
    (hc : LaneClaimR k hi (lf box (fk it 97 63)) (lf box (fk it 85 63)) (lf box (fk it 91 63)) (claim it)) :
    RecOK g box it := by
  have hok' := hok
  simp only [okR, fk_bits7, fk_bits6, fk_bits3, bk_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq,
    and_assoc] at hok'
  obtain ⟨he, hper, -, -, hside, hdv, hxv, hyv, -, mdv, mxv, myv, mo, k1, k2, k3, k4, k5, k6, knew, -⟩ := hok'
  rw [fk_bits6, fk_bits6, fk_bits6] at hc
  have hoe : Nat.shiftRight (bits it 64 7) 1 = bits it 64 7 / 2 := Nat.shiftRight_eq_div_pow _ _
  rw [hoe] at mo
  intro S hS

  set e' : S.P.G.Dart := S.lab.symm ⟨bits it 75 7, he⟩ with he'
  have hlab : (S.lab e' : ℕ) = bits it 75 7 := by simp [he']
  have hfs : fsize S.P e' = 4 :=
    D3lp.fsize_of_period S.hm e' ((congrArg (Ctx.code g).period hlab).trans hper) (by norm_num)
  have hiter : ∀ j, (Ctx.code g).faceIter (bits it 75 7) j = S.lab ((S.P.R.face ^ j) e') := by
    intro j; rw [← hlab]; exact D3lp.faceIter_lab S.hm e' j
  have hcorner : ∀ v j, Ctx.mean g v = 2 + (Ctx.code g).faceIter (bits it 75 7) j → S.x v = S.A.fc e' j := by
    intro v j hm
    rw [hiter] at hm
    exact val_corner S.lab S.A _ hm
  have hd : fld (lf box (bits it 97 6)) 0 ≤ S.A.d ∧ S.A.d ≤ fld (lf box (bits it 97 6)) 32 := by
    rw [← val_d S.lab S.A mdv]; exact lf_bounds k1 k2 (hS _ hdv)
  have hX := lf_bounds k3 k4 (hS _ hxv)
  have hY := lf_bounds k5 k6 (hS _ hyv)

  have hx0 : S.x (bits it 85 6) = S.A.fc e' 0 := hcorner _ 0 mxv
  have hy0 : S.x (bits it 91 6) = S.A.fc e' (jR (bits it 82 3)) := hcorner _ _ myv
  have hR := rhombus_fc S.hR hfs
  have hyrel : S.x (bits it 91 6) = rho S.A.d (S.x (bits it 85 6)) := by
    rw [hy0, hx0]
    rcases jR_cases (bits it 82 3) with h | h <;> rw [h]
    · exact hR.1
    · exact hR.2
  have hxpi : S.x (bits it 85 6) < Real.pi := by rw [hx0]; exact (S.hR.corner_mem _).2
  have hL := hc S.A.d (S.x (bits it 85 6)) (S.x (bits it 91 6)) hd.1 hd.2 hX.1 hX.2 hY.1 hY.2 hxpi hyrel

  have hcl : Claim hi (fld (claim it) 0) (S.x (bits it 64 7 / 2)) := by
    obtain ⟨kk, hkk⟩ := k
    obtain rfl | rfl : kk = 0 ∨ kk = 1 := by omega
    · change Ctx.mean g (bits it 64 7 / 2) = 2 + (Ctx.code g).faceIter (bits it 75 7) (jR (bits it 82 3)) at mo
      rw [hcorner _ _ mo, ← hy0]
      exact hL
    · change Ctx.mean g (bits it 64 7 / 2) = 1 at mo
      have hv : S.x (bits it 64 7 / 2) = S.A.d := val_d S.lab S.A mo
      rw [hv]
      exact hL

  have hb1 : bits it 64 1 = bits it 64 7 % 2 := by
    unfold bits; rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 7)]; rfl
  have hside' : bits it 64 7 % 2 = @Bool.rec (fun _ => ℕ) 0 1 hi := by
    rw [← hside]; exact (Nat.and_one_is_mod _).symm
  rw [Walk.kf_new] at knew
  refine boxMem_set (bits_lt it 0 64) hS (fun h0 => ?_) (fun h1 => ?_)
  · have h0' : bits it 64 7 % 2 = 0 := h0
    cases hi
    · have hlt : claim it < 2 ^ 32 := by
        rw [claim_lo (hb1.trans h0')]; exact lt_trans (kce_lt knew).1 (by norm_num)
      have hcl' : (claim it : ℝ) / 2 ^ 24 ≤ S.x (bits it 64 7 / 2) := by
        rw [← fld0_of_lt hlt]; exact hcl
      rw [claim_lo (hb1.trans h0')] at hcl'
      exact (le_kce knew).trans hcl'
    · have h1' : bits it 64 7 % 2 = 1 := hside'
      omega
  · have h1' : bits it 64 7 % 2 = 1 := h1
    cases hi
    · have h0' : bits it 64 7 % 2 = 0 := hside'
      omega
    · have hlt : claim it < 2 ^ 32 := by
        rw [claim_hi (hb1.trans h1')]; exact lt_trans (kce_lt knew).2 (by norm_num)
      have hcl' : S.x (bits it 64 7 / 2) ≤ (claim it : ℝ) / 2 ^ 24 := by
        rw [← fld0_of_lt hlt]; exact hcl
      rw [claim_hi (hb1.trans h1')] at hcl'
      exact hcl'.trans (kfl_le knew)

def PInvR (k : Fin 2) (hi : Bool) (s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool) (tr : List Ev) : Prop :=
  s.2.2.2.2.2 = true →
    s.2.1 < 2 ^ (64 * s.1) ∧ s.2.2.1 < 2 ^ (64 * s.1) ∧ s.2.2.2.1 < 2 ^ (64 * s.1) ∧
      s.2.2.2.2.1 < 2 ^ (64 * s.1) ∧
      (∀ l < s.1, InDom (lane s.2.1 l) (lane s.2.2.1 l) (lane s.2.2.2.1 l) (lane s.2.2.2.2.1 l)) ∧
      ∀ e ∈ tr, ∃ g box it, e = .record g box it ∧ okR k hi g box it = true ∧
        ∃ l < s.1, lane s.2.1 l = lf box (fk it 97 63) ∧ lane s.2.2.1 l = lf box (fk it 85 63) ∧
          lane s.2.2.2.1 l = lf box (fk it 91 63) ∧ lane s.2.2.2.2.1 l = claim it

theorem okR_inDomB {k : Fin 2} {hi : Bool} {g box it : ℕ} (h : okR k hi g box it = true) :
    inDomB (lf box (fk it 97 63)) (lf box (fk it 85 63)) (lf box (fk it 91 63)) (claim it) = true := by
  unfold okR at h
  exact ((Bool.and_eq_true _ _).mp h).2

theorem progR_step_rec (k : Fin 2) (hi : Bool) (prog : Prog) (n F0 F1 F2 F3 : ℕ) (ok : Bool) (g box it : ℕ) :
    (progCheckerR k hi prog).step (.record g box it) (n, F0, F1, F2, F3, ok) =
      (n + 1, F0 + lf box (fk it 97 63) * 2 ^ (64 * n), F1 + lf box (fk it 85 63) * 2 ^ (64 * n),
        F2 + lf box (fk it 91 63) * 2 ^ (64 * n), F3 + claim it * 2 ^ (64 * n), ok && okR k hi g box it) := by
  show (Nat.add n 1, Nat.add F0 (Nat.shiftLeft (lf box (fk it 97 63)) (Nat.shiftLeft n 6)),
    Nat.add F1 (Nat.shiftLeft (lf box (fk it 85 63)) (Nat.shiftLeft n 6)),
    Nat.add F2 (Nat.shiftLeft (lf box (fk it 91 63)) (Nat.shiftLeft n 6)),
    Nat.add F3 (Nat.shiftLeft (claim it) (Nat.shiftLeft n 6)), ok && okRK k hi g box it) = _
  rw [Walk.shl6, okRK_eq]
  simp only [shl_eq]
  rfl

theorem pinvR_record {k : Fin 2} {hi : Bool} {n F0 F1 F2 F3 : ℕ} {tr : List Ev} {g box it : ℕ}
    (h : PInvR k hi (n, F0, F1, F2, F3, true) tr) (hok : okR k hi g box it = true) :
    PInvR k hi (n + 1, F0 + lf box (fk it 97 63) * 2 ^ (64 * n), F1 + lf box (fk it 85 63) * 2 ^ (64 * n),
      F2 + lf box (fk it 91 63) * 2 ^ (64 * n), F3 + claim it * 2 ^ (64 * n), true) (tr ++ [.record g box it]) := by
  unfold PInvR at h ⊢
  dsimp only at h ⊢
  intro _
  obtain ⟨b0, b1, b2, b3, hdom, hev⟩ := h rfl
  have hD := inDomB_sound (okR_inDomB hok)
  have f0 := hD.1
  have f1 := hD.2.1
  have f2 := hD.2.2.1
  have f3 : claim it < 2 ^ 64 := lt_trans hD.2.2.2.1 (by norm_num)
  refine ⟨append_lt _ _ _ b0 f0, append_lt _ _ _ b1 f1, append_lt _ _ _ b2 f2, append_lt _ _ _ b3 f3, ?_, ?_⟩
  · intro l hl
    rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2, lane_append _ _ _ _ b3 f3]
    by_cases hln : l < n
    · simp only [hln, ite_true]
      exact hdom l hln
    · have hle : l = n := by omega
      simp [hle]
      exact hD
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨g', box', it', rfl, hok', l, hl, h0, h1, h2, h3⟩ := hev e he
      refine ⟨g', box', it', rfl, hok', l, by omega, ?_⟩
      rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2,
        lane_append _ _ _ _ b3 f3]
      simp only [hl, ite_true]
      exact ⟨h0, h1, h2, h3⟩
    · rw [List.mem_singleton] at he
      subst he
      refine ⟨g, box, it, rfl, hok, n, by omega, ?_⟩
      rw [lane_append _ _ _ _ b0 f0, lane_append _ _ _ _ b1 f1, lane_append _ _ _ _ b2 f2,
        lane_append _ _ _ _ b3 f3]
      simp

theorem pinvR_step {k : Fin 2} {hi : Bool} {prog : Prog} {s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool} {tr : List Ev}
    (h : PInvR k hi s tr) (e : Ev) : PInvR k hi ((progCheckerR k hi prog).step e s) (tr ++ [e]) := by
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := s
  cases e with
  | kill g box it =>
    intro hf
    have h' : false = true := hf
    cases h'
  | record g box it =>
    rw [progR_step_rec]
    unfold PInvR
    dsimp only
    intro hf
    rw [Bool.and_eq_true] at hf
    obtain ⟨rfl, hok⟩ := hf
    have := pinvR_record h hok
    unfold PInvR at this
    dsimp only at this
    exact this rfl

theorem pinvR_fold {k : Fin 2} {hi : Bool} {prog : Prog} (tr : List Ev) :
    ∀ (s : ℕ × ℕ × ℕ × ℕ × ℕ × Bool) (tr0 : List Ev), PInvR k hi s tr0 →
      PInvR k hi (tr.foldl (fun s e => (progCheckerR k hi prog).step e s) s) (tr0 ++ tr) := by
  induction tr with
  | nil => intro s tr0 h; rw [List.append_nil]; exact h
  | cons e tr ih =>
    intro s tr0 h
    have := ih _ _ (pinvR_step (prog := prog) h e)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

theorem progCheckerR_sound {k : Fin 2} {hi : Bool} {prog : Prog} (hp : ProgOKR k hi prog) :
    (progCheckerR k hi prog).Sound fun _ => True := by
  intro tr hs _ hfin e he
  have hinv : PInvR k hi ((progCheckerR k hi prog).run tr) tr := by
    have h0 : PInvR k hi (0, 0, 0, 0, 0, true) [] := by
      intro _
      refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun l hl => absurd hl (Nat.not_lt_zero _),
        fun e he => absurd he (by simp)⟩
    have := pinvR_fold (prog := prog) tr _ _ h0
    rw [List.nil_append] at this
    exact this
  generalize (progCheckerR k hi prog).run tr = S at hinv hfin
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := S
  have hf : (ok && Nat.beq (prog (oN n) F0 F1 F2 F3 hs) (oN n)) = true := hfin
  rw [Bool.and_eq_true] at hf
  obtain ⟨rfl, hv⟩ := hf
  unfold PInvR at hinv
  dsimp only at hinv
  obtain ⟨-, -, -, -, hdom, hev⟩ := hinv rfl
  obtain ⟨g, box, it, rfl, hok, l, hl, h0, h1, h2, h3⟩ := hev e he
  have hc := hp n F0 F1 F2 F3 hs (oN n) hdom hv l hl (lane_oN n l hl)
  rw [h0, h1, h2, h3] at hc
  exact recOK_of_rho hok hc

theorem rhoChecker_sound (progs : ℕ → Prog) (hp : ∀ i < 4, ProgOKR (kOf i) (hiOf i) (progs i)) :
    (rhoChecker progs).Sound (kindIs 2) := by
  refine btree_sound _ rIdx (fun i => ?_) 2 0 _
  split_ifs with h
  · exact progCheckerR_sound (hp i h)
  · exact Checker.none_sound _

noncomputable def rhoProgs (i : ℕ) : Prog :=
  match i with
  | 0 => fun O F0 F1 F2 F3 hs => progRL O F0 F1 F2 F3 (hs.getD 0 0)
  | 1 => fun O F0 F1 F2 F3 hs => progRH O F0 F1 F2 F3 (hs.getD 0 0)
  | 2 => fun O F0 F1 F2 F3 hs => progDL O F0 F1 F2 F3 (hs.getD 0 0)
  | 3 => fun O F0 F1 F2 F3 hs => progDH O F0 F1 F2 F3 (hs.getD 0 0)
  | _ => fun _ _ _ _ _ _ => 0

theorem rhoProgs_ok : ∀ i < 4, ProgOKR (kOf i) (hiOf i) (rhoProgs i) := by
  intro i hi
  interval_cases i
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [rhoProgs] at hv
    exact progRL_decl n F0 F1 F2 F3 (hs.getD 0 0) v hD hv l hl h1
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [rhoProgs] at hv
    exact progRH_decl n F0 F1 F2 F3 (hs.getD 0 0) v hD hv l hl h1
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [rhoProgs] at hv
    exact progDL_decl n F0 F1 F2 F3 (hs.getD 0 0) v hD hv l hl h1
  · intro n F0 F1 F2 F3 hs v hD hv l hl h1
    simp only [rhoProgs] at hv
    exact progDH_decl n F0 F1 F2 F3 (hs.getD 0 0) v hD hv l hl h1

noncomputable def rhoQ : Checker := rhoChecker rhoProgs

theorem rhoQ_sound : rhoQ.Sound (kindIs 2) := rhoChecker_sound rhoProgs rhoProgs_ok

end Tammes15.D3Trig
