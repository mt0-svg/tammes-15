import Tammes15.D3Data.QX
import Tammes15.D3Data.LinK

namespace Tammes15.D3Data

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Tammes15.D3Kernel.Kinds Tammes15.D3Kernel.Pent
  Tammes15.D3Kernel.Walk

def ctxOKR (g last : ℕ) : Bool := @Bool.rec (fun _ => Bool) (fstSortedK g) true (Nat.beq (Nat.succ g) last)

def rowOK (g it : ℕ) : Bool := entOKK g (entK g (fk it 75 127))

def rowSeen (bm j : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight bm j) 1) 1

def bmOf (g last bm : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 0 bm (Nat.beq (Nat.succ g) last)

def rowOKM (g it last bm : ℕ) : Bool := rowSeen (bmOf g last bm) (fk it 75 127) || rowOK g it

def linCheckerR : Checker where
  σ := Bool × ℕ × ℕ
  H := Unit
  init := (true, 0, 0)
  onRec g box it s := (s.1 && ctxOKR g s.2.1 && rowOKM g it s.2.1 s.2.2 && linRec g box it, Nat.succ g,
    Nat.lor (bmOf g s.2.1 s.2.2) (Nat.shiftLeft 1 (fk it 75 127)))
  onKill g box it s := (s.1 && ctxOKR g s.2.1 && rowOKM g it s.2.1 s.2.2 && linKill g box it, Nat.succ g,
    Nat.lor (bmOf g s.2.1 s.2.2) (Nat.shiftLeft 1 (fk it 75 127)))
  fin s _ := s.1
  frc s k := @Bool.rec (fun _ => List ℕ) (k (false, s.2)) (k (true, s.2)) s.1
  frc_eq s k := by obtain ⟨b, n⟩ := s; cases b <;> rfl

theorem rowSeen_eq (bm j : ℕ) : rowSeen bm j = Nat.testBit bm j := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 : Nat.land (Nat.shiftRight bm j) 1 = bm / 2 ^ j % 2 := by
    show (bm >>> j) &&& 1 = bm / 2 ^ j % 2
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold rowSeen
  rw [h1]
  cases h : decide (bm / 2 ^ j % 2 = 1)
  · simp only [decide_eq_false_iff_not] at h
    cases hb : Nat.beq (bm / 2 ^ j % 2) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h
  · simp only [decide_eq_true_eq] at h
    simp [h]

theorem rowSeen_zero (j : ℕ) : rowSeen 0 j = false := by
  rw [rowSeen_eq]
  simp

theorem rowSeen_lor {bm j j' : ℕ} (h : rowSeen (Nat.lor bm (Nat.shiftLeft 1 j)) j' = true) :
    rowSeen bm j' = true ∨ j' = j := by
  rw [rowSeen_eq] at h ⊢
  have h2 : Nat.lor bm (Nat.shiftLeft 1 j) = bm ||| 2 ^ j := by
    show bm ||| (1 <<< j) = bm ||| 2 ^ j
    rw [Nat.one_shiftLeft]
  rw [h2, Nat.testBit_or, Nat.testBit_two_pow] at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (of_decide_eq_true h).symm

theorem rowValid_of_rowOK {g it : ℕ} (hs : fstSorted (Ctx.code g) = true) (h : rowOK g it = true) :
    RowValid g (ent g (bits it 75 7)) := by
  unfold rowOK at h
  rw [entOKK_eq, fk_bits7, entK_eq] at h
  exact rowValid_of_entOK hs h

theorem recOK_of_rowValid {g box it : ℕ} (hE : RowValid g (ent g (bits it 75 7))) (h : linRec g box it = true) :
    RecOK g box it := by
  obtain ⟨-, hr⟩ := linRec_spec h
  intro s hS
  rcases hr with ⟨hn, hacc⟩ | hacc
  · obtain ⟨cp, cn, P, Q, hk, hle⟩ :=
      linAcc_row s.x (fun q hq => hS _ (hE.1 q hq)) hacc
    have hfin := recFin_sound _ _ _ cp cn P Q _ _ hle (hE.2 s) hk
    rw [← keyVal_kgood hn] at hfin
    exact boxMem_set (bits_lt it 0 64) hS (fun h0 => hfin.2 (by omega)) (fun h1 => hfin.1 h1)
  · exact (empty_of hE s hS hacc).elim

theorem killOK_of_rowValid {g box it : ℕ} (hE : RowValid g (ent g (bits it 75 7))) (h : linKill g box it = true) :
    KillOK g box := by
  obtain ⟨-, hacc⟩ := linKill_spec h
  intro s hS
  exact (empty_of hE s hS hacc).elim

theorem ctxOKR_sorted {g last : ℕ} (hl : last = 0 ∨ fstSorted (Ctx.code (last - 1)) = true)
    (h : ctxOKR g last = true) : fstSorted (Ctx.code g) = true := by
  unfold ctxOKR at h
  cases hb : Nat.beq (Nat.succ g) last
  · rw [hb, fstSortedK_eq] at h
    exact h
  · rw [Nat.beq_eq] at hb
    rcases hl with hl | hl
    · omega
    · rw [← hb] at hl
      simpa using hl

def LinInv (s : Bool × ℕ × ℕ) : Prop :=
  s.1 = true → s.2.1 = 0 ∨ (fstSorted (Ctx.code (s.2.1 - 1)) = true ∧
    ∀ j, rowSeen s.2.2 j = true → RowValid (s.2.1 - 1) (ent (s.2.1 - 1) j))

theorem rowOKM_valid {g it : ℕ} {s : Bool × ℕ × ℕ} (hs : LinInv s) (h1 : s.1 = true)
    (hfs : fstSorted (Ctx.code g) = true) (h : rowOKM g it s.2.1 s.2.2 = true) :
    RowValid g (ent g (bits it 75 7)) ∧ ∀ j, rowSeen (Nat.lor (bmOf g s.2.1 s.2.2) (Nat.shiftLeft 1 (fk it 75 127))) j = true →
      RowValid g (ent g j) := by

  have hbm : ∀ j, rowSeen (bmOf g s.2.1 s.2.2) j = true → RowValid g (ent g j) := by
    intro j hj
    unfold bmOf at hj
    cases hb : Nat.beq (Nat.succ g) s.2.1
    · rw [hb, rowSeen_zero] at hj
      exact absurd hj (by simp)
    · rw [hb] at hj
      rw [Nat.beq_eq] at hb
      rcases hs h1 with h0 | ⟨-, hall⟩
      · omega
      · have hg : s.2.1 - 1 = g := by omega
        rw [← hg]
        exact hall j hj
  have hE : RowValid g (ent g (bits it 75 7)) := by
    unfold rowOKM at h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · rw [fk_bits7] at h
      exact hbm _ h
    · exact rowValid_of_rowOK hfs h
  refine ⟨hE, fun j hj => ?_⟩
  rcases rowSeen_lor hj with hj | hj
  · exact hbm j hj
  · rw [hj, fk_bits7]
    exact hE

theorem linR_step {ev : Ev} {s : Bool × ℕ × ℕ} (hs : LinInv s) (h : (linCheckerR.step ev s).1 = true) :
    s.1 = true ∧ ev.OK ∧ LinInv (linCheckerR.step ev s) := by
  have hl : s.1 = true → s.2.1 = 0 ∨ fstSorted (Ctx.code (s.2.1 - 1)) = true :=
    fun h1 => (hs h1).imp_right And.left
  cases ev with
  | record g box it =>
    change (s.1 && ctxOKR g s.2.1 && rowOKM g it s.2.1 s.2.2 && linRec g box it) = true at h
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, hc⟩, hrow⟩, hr⟩ := h
    have hfs := ctxOKR_sorted (hl h1) hc
    obtain ⟨hE, hnext⟩ := rowOKM_valid hs h1 hfs hrow
    refine ⟨h1, recOK_of_rowValid hE hr, fun _ => Or.inr ⟨?_, ?_⟩⟩
    · change fstSorted (Ctx.code (Nat.succ g - 1)) = true
      simpa using hfs
    · change ∀ j, rowSeen (Nat.lor (bmOf g s.2.1 s.2.2) (Nat.shiftLeft 1 (fk it 75 127))) j = true →
        RowValid (Nat.succ g - 1) (ent (Nat.succ g - 1) j)
      simpa using hnext
  | kill g box it =>
    change (s.1 && ctxOKR g s.2.1 && rowOKM g it s.2.1 s.2.2 && linKill g box it) = true at h
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, hc⟩, hrow⟩, hr⟩ := h
    have hfs := ctxOKR_sorted (hl h1) hc
    obtain ⟨hE, hnext⟩ := rowOKM_valid hs h1 hfs hrow
    refine ⟨h1, killOK_of_rowValid hE hr, fun _ => Or.inr ⟨?_, ?_⟩⟩
    · change fstSorted (Ctx.code (Nat.succ g - 1)) = true
      simpa using hfs
    · change ∀ j, rowSeen (Nat.lor (bmOf g s.2.1 s.2.2) (Nat.shiftLeft 1 (fk it 75 127))) j = true →
        RowValid (Nat.succ g - 1) (ent (Nat.succ g - 1) j)
      simpa using hnext

theorem linR_fold : ∀ (l : List Ev) (s : Bool × ℕ × ℕ), LinInv s →
    (l.foldl (fun s e => linCheckerR.step e s) s).1 = true → s.1 = true ∧ ∀ e ∈ l, e.OK := by
  intro l
  induction l with
  | nil => exact fun s _ h => ⟨h, fun e he => by simp at he⟩
  | cons ev l ih =>
    intro s hs h
    change (List.foldl (fun s e => linCheckerR.step e s) (linCheckerR.step ev s) l).1 = true at h
    have hinv : LinInv (linCheckerR.step ev s) := fun h1 => (linR_step hs h1).2.2 h1
    obtain ⟨h1, hl⟩ := ih _ hinv h
    obtain ⟨hs1, hev, -⟩ := linR_step hs h1
    refine ⟨hs1, fun e he => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact hev
    · exact hl e he

theorem linCheckerR_sound : linCheckerR.Sound (kindIs 0) := by
  intro tr _ _ hfin
  exact (linR_fold tr linCheckerR.init (fun _ => Or.inl rfl) hfin).2

noncomputable def QXRs : List (ℕ × Checker) := (0, linCheckerR) :: QXs.tail

theorem QXRs_sound : ∀ p ∈ QXRs, p.2.Sound (kindIs p.1) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact linCheckerR_sound
  · exact QXs_sound p (List.mem_of_mem_tail hp)

noncomputable def QXR : Checker := byKind ((3, pentChecker progsZ) :: QXRs)

theorem QXR_sound : QXR.Sound fun _ => True := by
  refine byKind_sound _ ?_
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact pentChecker_sound progsZ progsZ_ok
  · exact QXRs_sound p hp

end Tammes15.D3Data
