import Tammes15.D3Kernel.Walk
import Tammes15.D3Kernel.Bits

namespace Tammes15.D3Kernel.Walk

open Tammes15.D3Kernel

structure Cfg where
  g : ℕ
  box : ℕ
  st : List ℕ
  rs : List ℕ

inductive Step : Cfg → List Ev → Cfg → Prop
  | record (g box it : ℕ) (st rs : List ℕ) :
      Step ⟨g, box, st, rs⟩ [.record g box it] ⟨g, recBox box it, st, rs⟩
  | split (g box j x : ℕ) (st rs : List ℕ) (hj : j < 64) (hx : x < 2 ^ 64) :
      Step ⟨g, box, st, rs⟩ [] ⟨g, setBnd box (2 * j + 1) x, setBnd box (2 * j) x :: st, rs⟩
  | kill (g box it b : ℕ) (st rs : List ℕ) :
      Step ⟨g, box, b :: st, rs⟩ [.kill g box it] ⟨g, b, st, rs⟩
  | kill0 (g box it : ℕ) (rs : List ℕ) :
      Step ⟨g, box, [], rs⟩ [.kill g box it] ⟨g, 0, [], rs⟩
  | root (g g' r : ℕ) (rs : List ℕ) (hr : Active r) :
      Step ⟨g, 0, [], g' :: r :: rs⟩ [] ⟨g', r, [], rs⟩

inductive Steps : Cfg → List Ev → Cfg → Prop
  | refl (c : Cfg) : Steps c [] c
  | head {c c' c'' : Cfg} {tr tr' : List Ev} : Step c tr c' → Steps c' tr' c'' → Steps c (tr ++ tr') c''

theorem Steps.trans {c c' c'' : Cfg} {tr tr' : List Ev} (h : Steps c tr c') (h' : Steps c' tr' c'') :
    Steps c (tr ++ tr') c'' := by
  induction h with
  | refl => simpa using h'
  | head hs _ ih => rw [List.append_assoc]; exact .head hs (ih h')

def adv (Q : Checker) (q : Q.σ) (tr : List Ev) : Q.σ := tr.foldl (fun s e => Q.step e s) q

theorem adv_append (Q : Checker) (q : Q.σ) (tr tr' : List Ev) : adv Q q (tr ++ tr') = adv Q (adv Q q tr) tr' :=
  List.foldl_append ..

theorem run_eq_adv (Q : Checker) (tr : List Ev) : Q.run tr = adv Q Q.init tr := rfl

theorem kf_bound (it : ℕ) : Nat.land (Nat.shiftRight it 64) 127 = itBound it :=
  land_shiftRight it 64 7

theorem kf_var (it : ℕ) : Nat.land (Nat.shiftRight it 64) 63 = bits it 64 6 :=
  land_shiftRight it 64 6

theorem kf_new (it : ℕ) : Nat.land it 18446744073709551615 = itNew it :=
  land_shiftRight it 0 64

theorem shl6 (t : ℕ) : Nat.shiftLeft t 6 = 64 * t := by
  rw [shl_eq]; ring

theorem bool_rec_ne {α : Type} {x : List α} {b : Bool} (h : @Bool.rec (fun _ => List α) [] x b ≠ []) :
    @Bool.rec (fun _ => List α) [] x b = x ∧ b = true := by
  cases b
  · exact absurd rfl h
  · exact ⟨rfl, rfl⟩

theorem recW_spec {Q : Checker} {g it box : ℕ} {st rs : List ℕ} {q : Q.σ} {k : K Q}
    (h : recW Q g it box st rs q k ≠ []) :
    recW Q g it box st rs q k = k g (recBox box it) st rs (Q.onRec g box it q) := by
  unfold recW at h ⊢
  dsimp only at h ⊢
  rw [(bool_rec_ne h).1]
  congr 1
  show Nat.add (Nat.sub box (Nat.land box (Nat.shiftLeft 18446744073709551615
      (Nat.shiftLeft (Nat.land (Nat.shiftRight it 64) 127) 6))))
      (Nat.shiftLeft (Nat.land it 18446744073709551615) (Nat.shiftLeft (Nat.land (Nat.shiftRight it 64) 127) 6)) = _
  rw [kf_bound, kf_new, shl6, setBnd_kernel]
  rfl

theorem splitW_eq (Q : Checker) (g it box : ℕ) (st rs : List ℕ) (q : Q.σ) (k : K Q) :
    splitW Q g it box st rs q k =
      k g (setBnd box (2 * bits it 64 6 + 1) (itNew it)) (setBnd box (2 * bits it 64 6) (itNew it) :: st) rs q := by
  have h1 : Nat.shiftLeft (Nat.land (Nat.shiftRight it 64) 63) 7 = 64 * (2 * bits it 64 6) := by
    rw [kf_var, shl_eq]; ring
  have h2 : Nat.add (64 * (2 * bits it 64 6)) 64 = 64 * (2 * bits it 64 6 + 1) := by
    show 64 * (2 * bits it 64 6) + 64 = _; ring
  show k g (Nat.add (Nat.sub box (Nat.land box (Nat.shiftLeft 18446744073709551615
      (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight it 64) 63) 7) 64))))
      (Nat.shiftLeft (Nat.land it 18446744073709551615) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight it 64) 63) 7) 64)))
    (Nat.add (Nat.sub box (Nat.land box (Nat.shiftLeft 18446744073709551615
      (Nat.shiftLeft (Nat.land (Nat.shiftRight it 64) 63) 7))))
      (Nat.shiftLeft (Nat.land it 18446744073709551615) (Nat.shiftLeft (Nat.land (Nat.shiftRight it 64) 63) 7)) :: st)
    rs q = _
  rw [h1, h2, kf_new, setBnd_kernel, setBnd_kernel]

theorem rootW_spec {Q : Checker} {box : ℕ} {st rs : List ℕ} {q : Q.σ} {k : K Q}
    (h : rootW Q box st rs q k ≠ []) :
    ∃ g' r rs', box = 0 ∧ st = [] ∧ rs = g' :: r :: rs' ∧ Active r ∧ rootW Q box st rs q k = k g' r [] rs' q := by
  unfold rootW at h ⊢
  obtain ⟨h1, hb⟩ := bool_rec_ne h
  rw [h1] at h ⊢
  have hbox : box = 0 := Nat.eq_of_beq_eq_true hb
  cases st with
  | cons _ _ => exact (h rfl).elim
  | nil =>
    cases rs with
    | nil => exact (h rfl).elim
    | cons g' rs1 =>
      cases rs1 with
      | nil => exact (h rfl).elim
      | cons r rs2 =>
        obtain ⟨h2, hr⟩ := bool_rec_ne h
        refine ⟨g', r, rs2, hbox, rfl, rfl, ?_, h2⟩
        have h3 : Nat.shiftLeft 1 8192 ≤ r := Nat.le_of_ble_eq_true hr
        have h4 : (2 : ℕ) ^ 8192 = Nat.shiftLeft 1 8192 := by rw [shl_eq, one_mul]
        show 2 ^ 8192 ≤ r
        rw [h4]; exact h3

theorem itemW_spec {Q : Checker} {g it box : ℕ} {st rs : List ℕ} {q : Q.σ} {k : K Q}
    (h : itemW Q g it box st rs q k ≠ []) :
    ∃ c' tr, Step ⟨g, box, st, rs⟩ tr c' ∧ itemW Q g it box st rs q k = k c'.g c'.box c'.st c'.rs (adv Q q tr) := by
  unfold itemW at h ⊢
  dsimp only at h ⊢
  revert h
  cases Nat.beq (Nat.shiftRight it (nat_lit 126)) (nat_lit 1)
  · dsimp only
    cases Nat.beq (Nat.shiftRight it (nat_lit 126)) (nat_lit 2)
    · dsimp only
      cases Nat.beq (Nat.shiftRight it (nat_lit 126)) (nat_lit 3)
      · dsimp only
        intro h
        obtain ⟨g', r, rs', rfl, rfl, rfl, hr, he⟩ := rootW_spec h
        exact ⟨⟨g', r, [], rs'⟩, [], .root g g' r rs' hr, he⟩
      · dsimp only
        intro _
        cases st with
        | nil => exact ⟨⟨g, 0, [], rs⟩, [.kill g box it], .kill0 g box it rs, rfl⟩
        | cons b st' => exact ⟨⟨g, b, st', rs⟩, [.kill g box it], .kill g box it b st' rs, rfl⟩
    · dsimp only
      intro _
      refine ⟨⟨g, setBnd box (2 * bits it 64 6 + 1) (itNew it), setBnd box (2 * bits it 64 6) (itNew it) :: st, rs⟩,
        [], .split g box _ _ st rs (bits_lt it 64 6) (bits_lt it 0 64), ?_⟩
      exact splitW_eq Q g it box st rs q k
  · dsimp only
    intro h
    exact ⟨⟨g, recBox box it, st, rs⟩, [.record g box it], .record g box it st rs, recW_spec h⟩

theorem chunkW_spec (Q : Checker) (k : K Q) (n : ℕ) :
    ∀ (c g box : ℕ) (st rs : List ℕ) (q : Q.σ), chunkW Q k n c g box st rs q ≠ [] →
      ∃ c' tr, Steps ⟨g, box, st, rs⟩ tr c' ∧ chunkW Q k n c g box st rs q = k c'.g c'.box c'.st c'.rs (adv Q q tr) := by
  induction n with
  | zero =>
    intro c g box st rs q _
    refine ⟨⟨g, box, st, rs⟩, [], .refl _, ?_⟩
    show Q.frc q (fun q' => k g box st rs q') = _
    rw [Q.frc_eq]
    rfl
  | succ n ih =>
    intro c g box st rs q h
    have e : chunkW Q k (n + 1) c g box st rs q =
        itemW Q g (Nat.land c 340282366920938463463374607431768211455) box st rs q
          (fun g' b s r q' => chunkW Q k n (Nat.shiftRight c 128) g' b s r q') := rfl
    rw [e] at h ⊢
    obtain ⟨c1, tr1, hs1, he1⟩ := itemW_spec h
    rw [he1] at h ⊢
    obtain ⟨c2, tr2, hs2, he2⟩ := ih _ _ _ _ _ _ h
    exact ⟨c2, tr1 ++ tr2, .head hs1 hs2, by rw [he2, adv_append]⟩

theorem walkW_spec (Q : Checker) (fin : K Q) (cs : List ℕ) :
    ∀ (g box : ℕ) (st rs : List ℕ) (q : Q.σ), walkW Q fin cs g box st rs q ≠ [] →
      ∃ c' tr, Steps ⟨g, box, st, rs⟩ tr c' ∧ walkW Q fin cs g box st rs q = fin c'.g c'.box c'.st c'.rs (adv Q q tr) := by
  induction cs with
  | nil =>
    intro g box st rs q _
    exact ⟨⟨g, box, st, rs⟩, [], .refl _, rfl⟩
  | cons c cs ih =>
    intro g box st rs q h
    have e : walkW Q fin (c :: cs) g box st rs q =
        chunkW Q (walkW Q fin cs) (Nat.land c 4294967295) (Nat.shiftRight c 64) g box st rs q := rfl
    rw [e] at h ⊢
    obtain ⟨c1, tr1, hs1, he1⟩ := chunkW_spec Q _ _ _ _ _ _ _ _ h
    rw [he1] at h ⊢
    obtain ⟨c2, tr2, hs2, he2⟩ := ih _ _ _ _ _ h
    exact ⟨c2, tr1 ++ tr2, hs1.trans hs2, by rw [he2, adv_append]⟩

theorem finW_spec {Q : Checker} {h : Q.H} {g box : ℕ} {st rs : List ℕ} {q : Q.σ}
    (hne : finW Q h g box st rs q ≠ []) :
    Q.fin q h = true ∧ rs = [] ∧ finW Q h g box st rs q = g :: box :: st := by
  unfold finW at hne ⊢
  obtain ⟨h1, hf⟩ := bool_rec_ne hne
  rw [h1] at hne ⊢
  cases rs with
  | nil => exact ⟨hf, rfl, rfl⟩
  | cons _ _ => exact absurd rfl hne

theorem lbeq_eq (l₁ : List ℕ) : ∀ l₂ : List ℕ, lbeq l₁ l₂ = true → l₁ = l₂ := by
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons b t => have h' : false = true := h; cases h'
  | cons a t₁ ih =>
    intro l₂ h
    cases l₂ with
    | nil => have h' : false = true := h; cases h'
    | cons b t₂ =>
      have h' : @Bool.rec (fun _ => Bool) false (lbeq t₁ t₂) (Nat.beq a b) = true := h
      cases hab : Nat.beq a b
      · rw [hab] at h'; have h'' : false = true := h'; cases h''
      · rw [hab] at h'
        rw [Nat.eq_of_beq_eq_true hab, ih t₂ h']

theorem chk_spec {Q : Checker} {d r : List ℕ} {h : Q.H} {s t : List ℕ} (hc : chk Q d r h s t = true) :
    ∃ g box st c' tr, s = g :: box :: st ∧ Steps ⟨g, box, st, r⟩ tr c' ∧ Q.fin (Q.run tr) h = true ∧ c'.rs = [] ∧
      t = c'.g :: c'.box :: c'.st := by
  rcases s with _ | ⟨g, _ | ⟨box, st⟩⟩
  · have h' : false = true := hc; cases h'
  · have h' : false = true := hc; cases h'
  rcases t with _ | ⟨t₀, t₁⟩
  · have h' : false = true := hc; cases h'
  have hl : lbeq (walkW Q (finW Q h) d g box st r Q.init) (t₀ :: t₁) = true := hc
  have he := lbeq_eq _ _ hl
  have hne : walkW Q (finW Q h) d g box st r Q.init ≠ [] := by rw [he]; exact List.cons_ne_nil _ _
  obtain ⟨c', tr, hs, hw⟩ := walkW_spec Q _ d g box st r Q.init hne
  rw [hw] at hne he
  obtain ⟨hf, hrs, hfe⟩ := finW_spec hne
  exact ⟨g, box, st, c', tr, rfl, hs, hf, hrs, he.symm.trans hfe⟩

abbrev Inv (g box : ℕ) (st : List ℕ) : Prop :=
  (Active box → TreeKilled g box) ∧ ∀ b ∈ st, Active b → TreeKilled g b

abbrev Good (c : Cfg) : Prop :=
  Inv c.g c.box c.st ∧ (∀ p ∈ rootPairs c.rs, TreeKilled p.1 p.2) ∧ c.rs.length % 2 = 0

theorem not_active_zero : ¬ Active 0 := by
  unfold Active; exact Nat.not_le.mpr (by positivity)

theorem boxMem_split {g box j x : ℕ} (hx : x < 2 ^ 64) {y : ℕ → ℝ} (hy : BoxMem (Ctx.nv g) box y) :
    BoxMem (Ctx.nv g) (setBnd box (2 * j + 1) x) y ∨ BoxMem (Ctx.nv g) (setBnd box (2 * j) x) y := by
  rcases le_total (y j) (keyVal x) with hle | hle
  · left
    intro v hv
    rw [bnd_setBnd_ne box (2 * j + 1) (2 * v) x hx (by omega)]
    by_cases hvj : v = j
    · rw [hvj] at hv ⊢
      rw [bnd_setBnd_self box (2 * j + 1) x hx]
      exact ⟨(hy j hv).1, hle⟩
    · rw [bnd_setBnd_ne box (2 * j + 1) (2 * v + 1) x hx (by omega)]
      exact hy v hv
  · right
    intro v hv
    rw [bnd_setBnd_ne box (2 * j) (2 * v + 1) x hx (by omega)]
    by_cases hvj : v = j
    · rw [hvj] at hv ⊢
      rw [bnd_setBnd_self box (2 * j) x hx]
      exact ⟨hle, (hy j hv).2⟩
    · rw [bnd_setBnd_ne box (2 * j) (2 * v) x hx (by omega)]
      exact hy v hv

theorem step_back {c c' : Cfg} {tr : List Ev} (h : Step c tr c') (hok : ∀ e ∈ tr, e.OK) (hg : Good c') :
    Good c := by
  obtain ⟨⟨hb, hst⟩, hroots, hpar⟩ := hg
  cases h with
  | record g box it st rs =>
    have hrec : RecOK g box it := hok _ (List.mem_singleton_self _)
    refine ⟨⟨fun ha s hs => hb ?_ s (hrec s hs), hst⟩, hroots, hpar⟩
    exact active_setBnd _ _ _ (bits_lt it 64 7) (bits_lt it 0 64) ha
  | split g box j x st rs hj hx =>
    refine ⟨⟨fun ha s hs => ?_, fun b hbm => hst b (List.mem_cons_of_mem _ hbm)⟩, hroots, hpar⟩
    rcases boxMem_split hx hs with h1 | h2
    · exact hb (active_setBnd _ _ _ (by omega) hx ha) s h1
    · exact hst _ (by simp) (active_setBnd _ _ _ (by omega) hx ha) s h2
  | kill g box it b st rs =>
    have hk : KillOK g box := hok _ (List.mem_singleton_self _)
    refine ⟨⟨fun _ => hk, fun b' hb' => ?_⟩, hroots, hpar⟩
    rcases List.mem_cons.mp hb' with rfl | hm
    · exact hb
    · exact hst b' hm
  | kill0 g box it rs =>
    have hk : KillOK g box := hok _ (List.mem_singleton_self _)
    exact ⟨⟨fun _ => hk, fun _ hm => by simp at hm⟩, hroots, hpar⟩
  | root g g' r rs hr =>
    refine ⟨⟨fun ha => absurd ha not_active_zero, fun _ hm => by simp at hm⟩, ?_, ?_⟩
    · intro p hp
      simp only [rootPairs, List.mem_cons] at hp
      rcases hp with rfl | hm
      · exact hb hr
      · exact hroots p hm
    · simp only [List.length_cons] at hpar ⊢; omega

theorem steps_back {c c' : Cfg} {tr : List Ev} (h : Steps c tr c') (hok : ∀ e ∈ tr, e.OK) (hg : Good c') :
    Good c := by
  induction h with
  | refl => exact hg
  | head hs _ ih =>
    exact step_back hs (fun e he => hok e (List.mem_append_left _ he))
      (ih (fun e he => hok e (List.mem_append_right _ he)) hg)

theorem rootPairs_append : ∀ (r R : List ℕ), r.length % 2 = 0 → rootPairs (r ++ R) = rootPairs r ++ rootPairs R
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | g :: b :: r, R, h => by
    simp only [List.cons_append, rootPairs, List.length_cons] at h ⊢
    rw [rootPairs_append r R (by omega)]

end Tammes15.D3Kernel.Walk
