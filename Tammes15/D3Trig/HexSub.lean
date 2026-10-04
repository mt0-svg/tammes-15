import Tammes15.D3Trig.SliceKinds

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel Tammes15.D3Kernel.Pent Tammes15.D3Kernel.KForm

def hKx (it : ℕ) : ℕ := fk it 108 7

def hKy (it : ℕ) : ℕ := fk it 111 7

def addH (s : WSt) (a b c F3 : ℕ) : WSt :=
  let sh := Nat.shiftLeft s.1 (nat_lit 6)
  (Nat.add s.1 1, Nat.add s.2.1 (Nat.shiftLeft a sh), Nat.add s.2.2.1 (Nat.shiftLeft b sh),
    Nat.add s.2.2.2.1 (Nat.shiftLeft c sh), Nat.add s.2.2.2.2.1 (Nat.shiftLeft F3 sh),
    s.2.2.2.2.2 && inDomBHK a b c F3)

def progCheckerHS (hi : Bool) (prog : Prog) : Checker where
  σ := WSt
  H := List ℕ
  init := (0, 0, 0, 0, 0, true)
  onRec g box it s :=
    (subsW (hKy it) (hKx it) (lf box (fk it 82 63)) (lf box (fk it 88 63))).foldl
      (fun s x => addH s (lf box (fk it 100 63)) x.1 x.2 (claimH hi box (fk it 94 63) it))
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2 && okHK hi g box it)
  onKill _ _ _ s := (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, false)
  fin s hs := s.2.2.2.2.2 && Nat.beq (prog (oN s.1) s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 hs) (oN s.1)
  frc s k := @Bool.rec (fun _ => List ℕ) (k s) (k s)
    (Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0)
  frc_eq s k := by
    cases Nat.beq (Nat.add (Nat.add s.1 s.2.1) (Nat.add (Nat.add s.2.2.1 s.2.2.2.1) s.2.2.2.2.1)) 0 <;> rfl

def hexCheckerS (progs : ℕ → Prog) : Checker :=
  btree (fun i => if i < 6 then progCheckerHS (hiOf i) (progs i) else Checker.none) hIdx 3 0

theorem lo32_lt (F : ℕ) : lo32 F < 2 ^ 32 := by
  have : lo32 F = Nat.land F 4294967295 := rfl
  rw [this, Nat.land_eq]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem hi32_lt (F : ℕ) : hi32 F < 2 ^ 32 := by
  have : hi32 F = Nat.land (Nat.shiftRight F 32) 4294967295 := rfl
  rw [this, Nat.land_eq]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem laneClaimH_of_subs (hi : Bool) (ky kx F0 F1 F2 F3 : ℕ)
    (h : ∀ x ∈ subsW ky kx F1 F2, LaneClaimH hi F0 x.1 x.2 F3) : LaneClaimH hi F0 F1 F2 F3 := by
  intro d x y z hd0 hd32 hx0 hx32 hy0 hy32 hxpi hypi hzpi hz
  obtain ⟨hF1_0, hF1_32⟩ := fld_lo32 F1
  obtain ⟨hF2_0, hF2_32⟩ := fld_lo32 F2
  rw [hF1_0] at hx0
  rw [hF1_32] at hx32
  rw [hF2_0] at hy0
  rw [hF2_32] at hy32
  obtain ⟨px, hpx, hpx0, hpx32⟩ := cutW_cover kx (lo32 F1) (hi32 F1) (lo32_lt F1) (hi32_lt F1) x hx0 hx32
  obtain ⟨py, hpy, hpy0, hpy32⟩ := cutW_cover ky (lo32 F2) (hi32 F2) (lo32_lt F2) (hi32_lt F2) y hy0 hy32
  have hmem : (px, py) ∈ subsW ky kx F1 F2 := by
    unfold subsW
    exact List.mem_flatMap.mpr ⟨py, hpy, List.mem_map.mpr ⟨px, hpx, rfl⟩⟩
  exact h (px, py) hmem d x y z hd0 hd32 hpx0 hpx32 hpy0 hpy32 hxpi hypi hzpi hz

theorem addH_eq (n F0 F1 F2 F3 : ℕ) (ok : Bool) (a b c d : ℕ) :
    addH (n, F0, F1, F2, F3, ok) a b c d =
      (n + 1, F0 + a * 2 ^ (64 * n), F1 + b * 2 ^ (64 * n), F2 + c * 2 ^ (64 * n), F3 + d * 2 ^ (64 * n),
        ok && inDomBH a b c d) := by
  show (Nat.add n 1, Nat.add F0 (Nat.shiftLeft a (Nat.shiftLeft n 6)), Nat.add F1 (Nat.shiftLeft b (Nat.shiftLeft n 6)),
    Nat.add F2 (Nat.shiftLeft c (Nat.shiftLeft n 6)), Nat.add F3 (Nat.shiftLeft d (Nat.shiftLeft n 6)),
    ok && inDomBHK a b c d) = _
  rw [Walk.shl6, inDomBHK_eq]
  simp only [shl_eq]
  rfl

theorem addH_step (a b c d : ℕ) (s : WSt) :
    (addH s a b c d).2.2.2.2.2 = true → s.2.2.2.2.2 = true ∧
      (LanesOK InDomH s → LanesOK InDomH (addH s a b c d) ∧ HasLane (addH s a b c d) (a, b, c, d) ∧
        ∀ q, HasLane s q → HasLane (addH s a b c d) q) := by
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := s
  rw [addH_eq]
  intro h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, fun hs => lanes_append (fun hq => ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩) hs (inDomBH_sound h.2)⟩

def PInvHS (hi : Bool) (s : WSt) (tr : List Ev) : Prop :=
  s.2.2.2.2.2 = true → LanesOK InDomH s ∧ ∀ e ∈ tr, ∃ g box it, e = .record g box it ∧ okH hi g box it = true ∧
    ∀ x ∈ subsW (hKy it) (hKx it) (lf box (fk it 82 63)) (lf box (fk it 88 63)),
      HasLane s (lf box (fk it 100 63), x.1, x.2, claimH hi box (fk it 94 63) it)

theorem pinvHS_step {hi : Bool} {prog : Prog} {s : WSt} {tr : List Ev}
    (h : PInvHS hi s tr) (e : Ev) : PInvHS hi ((progCheckerHS hi prog).step e s) (tr ++ [e]) := by
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := s
  cases e with
  | kill g box it =>
    intro hf
    have h' : false = true := hf
    cases h'
  | record g box it =>
    show PInvHS hi (List.foldl
        (fun (s : WSt) (x : ℕ × ℕ) => addH s (lf box (fk it 100 63)) x.1 x.2 (claimH hi box (fk it 94 63) it))
        (n, F0, F1, F2, F3, ok && okHK hi g box it)
        (subsW (hKy it) (hKx it) (lf box (fk it 82 63)) (lf box (fk it 88 63)))) (tr ++ [Ev.record g box it])
    rw [okHK_eq]
    intro hf
    have hf' : (List.foldl
        (fun (s : WSt) (x : ℕ × ℕ) => addH s (lf box (fk it 100 63)) x.1 x.2 (claimH hi box (fk it 94 63) it))
        (n, F0, F1, F2, F3, ok && okH hi g box it)
        (subsW (hKy it) (hKx it) (lf box (fk it 82 63)) (lf box (fk it 88 63)))).2.2.2.2.2 = true := hf
    obtain ⟨hok0, hrest⟩ := fold_lanes (D := InDomH)
      (fun (s : WSt) (x : ℕ × ℕ) => addH s (lf box (fk it 100 63)) x.1 x.2 (claimH hi box (fk it 94 63) it))
      (fun x => (lf box (fk it 100 63), x.1, x.2, claimH hi box (fk it 94 63) it)) (fun s x => addH_step _ _ _ _ s)
      (subsW (hKy it) (hKx it) (lf box (fk it 82 63)) (lf box (fk it 88 63)))
      (n, F0, F1, F2, F3, ok && okH hi g box it) hf'
    have hok1 : (ok && okH hi g box it) = true := hok0
    rw [Bool.and_eq_true] at hok1
    obtain ⟨rfl, hok⟩ := hok1
    obtain ⟨hlanes, hev⟩ := h rfl
    obtain ⟨l1, l2, l3⟩ := hrest hlanes
    refine ⟨l1, fun e' he' => ?_⟩
    rcases List.mem_append.mp he' with he' | he'
    · obtain ⟨g', box', it', rfl, hok', hs⟩ := hev e' he'
      exact ⟨g', box', it', rfl, hok', fun x hx => l3 _ (hs x hx)⟩
    · rw [List.mem_singleton] at he'
      subst he'
      exact ⟨g, box, it, rfl, hok, fun x hx => l2 x hx⟩

theorem pinvHS_fold {hi : Bool} {prog : Prog} (tr : List Ev) :
    ∀ (s : WSt) (tr0 : List Ev), PInvHS hi s tr0 →
      PInvHS hi (tr.foldl (fun s e => (progCheckerHS hi prog).step e s) s) (tr0 ++ tr) := by
  induction tr with
  | nil => intro s tr0 h; rw [List.append_nil]; exact h
  | cons e tr ih =>
    intro s tr0 h
    have := ih _ _ (pinvHS_step (prog := prog) h e)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

theorem progCheckerHS_sound {hi : Bool} {prog : Prog} (hp : ProgOKH hi prog) :
    (progCheckerHS hi prog).Sound fun _ => True := by
  intro tr hs _ hfin e he
  have hinv : PInvHS hi ((progCheckerHS hi prog).run tr) tr := by
    have h0 : PInvHS hi (0, 0, 0, 0, 0, true) [] := by
      intro _
      exact ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, fun l hl => absurd hl (Nat.not_lt_zero _)⟩,
        fun e he => absurd he (by simp)⟩
    have := pinvHS_fold (prog := prog) tr _ _ h0
    rw [List.nil_append] at this
    exact this
  generalize (progCheckerHS hi prog).run tr = S at hinv hfin
  obtain ⟨n, F0, F1, F2, F3, ok⟩ := S
  have hf : (ok && Nat.beq (prog (oN n) F0 F1 F2 F3 hs) (oN n)) = true := hfin
  rw [Bool.and_eq_true] at hf
  obtain ⟨rfl, hv⟩ := hf
  obtain ⟨⟨-, -, -, -, hdom⟩, hev⟩ := hinv rfl
  obtain ⟨g, box, it, rfl, hok, hsub⟩ := hev e he
  refine recOK_of_hex hok (laneClaimH_of_subs hi (hKy it) (hKx it) _ _ _ _ fun x hx => ?_)
  obtain ⟨l, hl, h0, h1, h2, h3⟩ := hsub x hx
  have hc := hp n F0 F1 F2 F3 hs (oN n) hdom hv l hl (lane_oN n l hl)
  simp only at h0 h1 h2 h3
  rw [h0, h1, h2, h3] at hc
  exact hc

theorem hexCheckerS_sound (progs : ℕ → Prog) (hp : ∀ i < 6, ProgOKH (hiOf i) (progs i)) :
    (hexCheckerS progs).Sound (kindIs 4) := by
  refine btree_sound _ hIdx (fun i => ?_) 3 0 _
  split_ifs with h
  · exact progCheckerHS_sound (hp i h)
  · exact Checker.none_sound _

noncomputable def hexQS : Checker := hexCheckerS hexProgs

theorem hexQS_sound : hexQS.Sound (kindIs 4) := hexCheckerS_sound hexProgs hexProgs_ok

theorem hexSliceS_sound (tH : ℕ → BT) (Dt : ℕ → ℕ)
    (ht : ∀ i < 6, (tH i).All (BatchClaims (LaneClaimH (hiOf i)))) :
    (hexCheckerS fun i => sliceProg (tH i) (Dt i)).Sound (kindIs 4) :=
  hexCheckerS_sound _ fun i hi => sliceProg_ok (Dom := InDomH) (Dt i) (ht i hi)

end Tammes15.D3Trig
