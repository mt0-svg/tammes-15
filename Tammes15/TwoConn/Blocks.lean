import Tammes15.TwoConn.Excess

/-!
# Blocks: the rotation of the graph inside the rotation of the hull

Lemmas G1 and G2 of the proof of Corollary twoconn by the convex hull (paper, Section 3,
Lemma hull and Corollary twoconn), in the form used by the count of regions. Along an angular
rotation with positive corners the corner from a dart to its `j`-th iterate is the sum of the
first `j` corners (`ocorner_rot_pow`). For a graph `G` whose edges are hull edges, with an angular
rotation `R` whose corners lie in `(0, π)`, the successor `R.rot e` of a dart of `G` is the first
dart of `G` counterclockwise from `e` in the hull rotation `rho`, and the corner of `R` at `e` is
the sum of the corners of `rho` over the hull darts in between (`block`).
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

/-! ## Iterates of a rotation -/

section Angular

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem rot_pow_succ_apply (R : RotSys G) (e : G.Dart) (k : ℕ) :
    R.rot ((R.rot ^ k) e) = (R.rot ^ (k + 1)) e := by
  rw [pow_succ', Equiv.Perm.mul_apply]

/-- The darts at a vertex are the iterates of the rotation over one period. -/
theorem rot_pow_surj (R : RotSys G) (e f : G.Dart) (hf : f.fst = e.fst) :
    ∃ j < Function.minimalPeriod R.rot e, (R.rot ^ j) e = f := by
  have hcycle : R.rot.SameCycle e f := R.rot_cycle e f hf.symm
  have h_exists := hcycle.exists_nat_pow_eq
  rcases h_exists with ⟨n, hn⟩
  have h_order_pos : 0 < orderOf R.rot := by
    apply orderOf_pos
  have h_periodic : Function.IsPeriodicPt R.rot (orderOf R.rot) e := by
    have h_pow : (R.rot ^ orderOf R.rot) = 1 := pow_orderOf_eq_one R.rot
    have h_iter : R.rot^[orderOf R.rot] e = e := by
      calc
        R.rot^[orderOf R.rot] e = (R.rot ^ orderOf R.rot) e := by
          simpa using congrFun (Equiv.Perm.iterate_eq_pow R.rot (orderOf R.rot)) e
        _ = (1 : Equiv.Perm G.Dart) e := by rw [h_pow]
        _ = e := rfl
    exact h_iter
  have h_minimal_pos : 0 < Function.minimalPeriod R.rot e :=
    Function.IsPeriodicPt.minimalPeriod_pos (orderOf_pos R.rot) h_periodic
  set P := Function.minimalPeriod R.rot e with hPdef
  use n % P
  constructor
  · exact Nat.mod_lt n h_minimal_pos
  · calc
      (R.rot ^ (n % P)) e = R.rot^[n % P] e := by
        simpa using congrFun (Equiv.Perm.coe_pow R.rot (n % P)) e
      _ = R.rot^[n] e := by rw [Function.iterate_mod_minimalPeriod_eq]
      _ = (R.rot ^ n) e := by
        simpa using congrFun (Equiv.Perm.iterate_eq_pow R.rot n) e
      _ = f := hn

theorem rot_pow_ne_self (R : RotSys G) (e : G.Dart) {j : ℕ} (hj0 : 0 < j)
    (hj : j < Function.minimalPeriod R.rot e) : (R.rot ^ j) e ≠ e := by
  intro h_eq
  have h_periodic : Function.IsPeriodicPt R.rot j e := by
    calc
      (⇑R.rot)^[j] e = ⇑(R.rot ^ j) e := by rw [Equiv.Perm.coe_pow]
      _ = e := h_eq
  have h_le : Function.minimalPeriod R.rot e ≤ j :=
    Function.IsPeriodicPt.minimalPeriod_le hj0 h_periodic
  have : j < j := Nat.lt_of_lt_of_le hj h_le
  exact Nat.lt_irrefl _ this

/-- A sum over the darts at a vertex as a sum along the rotation. -/
theorem sum_darts_at_eq_sum_rot (R : RotSys G) (e : G.Dart) (φ : G.Dart → ℝ) :
    ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = e.fst), φ d =
      ∑ i ∈ Finset.range (Function.minimalPeriod R.rot e), φ ((R.rot ^ i) e) := by
  set P := Function.minimalPeriod R.rot e
  have h_inj : Set.InjOn (fun i : ℕ => (R.rot ^ i) e) (Set.Iio P) :=
    Function.iterate_injOn_Iio_minimalPeriod
  have h_range_eq : (Finset.range P : Set ℕ) = Set.Iio P := by
    ext x; simp
  -- Use Finset.sum_nbij from range P to filter, then symm
  have hsum := Finset.sum_nbij (s := Finset.range P) (t := Finset.univ.filter (fun d : G.Dart => d.fst = e.fst))
    (f := fun i => φ ((R.rot ^ i) e)) (g := φ)
    (i := fun (i : ℕ) => (R.rot ^ i) e) ?hi ?i_inj ?i_surj ?h
  · exact hsum.symm
  · -- hi
    intro i hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rot_pow_fst R e i⟩
  · -- i_inj: Set.InjOn (fun i => (R.rot ^ i) e) (range P)
    rw [h_range_eq]
    exact h_inj
  · -- i_surj
    intro d hd
    rw [Finset.mem_coe, Finset.mem_filter] at hd
    rcases hd with ⟨_, hd_fst⟩
    rcases rot_pow_surj R e d hd_fst with ⟨j, hj, h⟩
    refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    exact h
  · -- h: f a = g (i a)
    intro i hi
    rfl

/-- Along an angular rotation with positive corners, the corner from `e` to its `j`-th iterate
is the sum of the first `j` corners. -/
theorem ocorner_rot_pow (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hD : DistinctDirs G x)
    (R : RotSys G) (hR : IsAngular R x)
    (hpos : ∀ d : G.Dart, 0 < ocorner (x d.fst) (x d.snd) (x (R.rot d).snd)) (e : G.Dart)
    (hv : ∃ a b, a ≠ b ∧ G.Adj e.fst a ∧ G.Adj e.fst b) (j : ℕ)
    (hj : j < Function.minimalPeriod R.rot e) :
    ocorner (x e.fst) (x e.snd) (x ((R.rot ^ j) e).snd) =
      ∑ i ∈ Finset.range j,
        ocorner (x e.fst) (x ((R.rot ^ i) e).snd) (x ((R.rot ^ (i + 1)) e).snd) := by
  let v := e.fst
  let P := Function.minimalPeriod R.rot e
  have hx_v : ‖x v‖ = 1 := hx v
  have h_adj_e : G.Adj v e.snd := by
    exact e.adj
  -- Each iterate of rot stays at vertex v
  have h_rot_fst : ∀ i, ((R.rot ^ i) e).fst = v := by
    intro i; simpa [v] using rot_pow_fst R e i
  -- Adjacency of iterated darts
  have h_adj_rot : ∀ i, G.Adj v ((R.rot ^ i) e).snd := by
    intro i
    have h_adj_dart : G.Adj ((R.rot ^ i) e).fst ((R.rot ^ i) e).snd := ((R.rot ^ i) e).adj
    rw [h_rot_fst i] at h_adj_dart
    exact h_adj_dart
  -- Nonzero tdirs for iterated darts
  have h_tdir_ne_zero : ∀ i, tdir (x v) (x ((R.rot ^ i) e).snd) ≠ 0 := by
    intro i
    apply hD.1 v ((R.rot ^ i) e).snd
    exact h_adj_rot i
  -- Define c_i for convenience
  let c : ℕ → ℝ := fun i =>
    ocorner (x v) (x ((R.rot ^ i) e).snd) (x ((R.rot ^ (i + 1)) e).snd)
  -- Each c_i is positive
  have hc_pos : ∀ i, 0 < c i := by
    intro i
    dsimp [c]
    have h := hpos ((R.rot ^ i) e)
    have h_fst_eq : ((R.rot ^ i) e).fst = v := h_rot_fst i
    have h_rot_eq : R.rot ((R.rot ^ i) e) = (R.rot ^ (i + 1)) e := by
      simpa [add_comm] using rot_pow_succ_apply R e i
    simpa [h_fst_eq, h_rot_eq] using h
  -- The sum over one period is 2π
  have hsum_period : ∑ i ∈ Finset.range P, c i = 2 * π := by
    let φ : G.Dart → ℝ := fun d =>
      ocorner (x v) (x d.snd) (x (R.rot d).snd)
    have hφ_eq : ∀ i, φ ((R.rot ^ i) e) = c i := by
      intro i
      dsimp [φ, c]
      have h_rot_eq : R.rot ((R.rot ^ i) e) = (R.rot ^ (i + 1)) e := by
        simpa [add_comm] using rot_pow_succ_apply R e i
      simp [h_rot_eq]
    calc
      ∑ i ∈ Finset.range P, c i = ∑ i ∈ Finset.range P, φ ((R.rot ^ i) e) := by
        simp [hφ_eq]
      _ = ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), φ d :=
        (sum_darts_at_eq_sum_rot R e φ).symm
      _ = ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v),
          ocorner (x v) (x d.snd) (x (R.rot d).snd) := rfl
      _ = 2 * π := corner_sum x hx hD R hR v hv
  -- For any k < P, the partial sum is < 2π
  have hsum_range_lt : ∀ k, k < P → ∑ i ∈ Finset.range k, c i < 2 * π := by
    intro k hk
    have h_sub : Finset.range k ⊆ Finset.range P := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      exact lt_of_lt_of_le hx (Nat.le_of_lt hk)
    have h_sdiff_pos : 0 < ∑ i ∈ (Finset.range P) \ (Finset.range k), c i := by
      have hk_mem : k ∈ (Finset.range P) \ (Finset.range k) := by
        refine Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hk, ?_⟩
        simp [Finset.mem_range]
      have h_nonneg : ∀ i, 0 ≤ c i := fun i => le_of_lt (hc_pos i)
      have h_pos_all : ∀ i ∈ (Finset.range P) \ (Finset.range k), 0 < c i := by
        intro i hi; exact hc_pos i
      have h_nonempty : ((Finset.range P) \ (Finset.range k)).Nonempty :=
        ⟨k, hk_mem⟩
      exact Finset.sum_pos h_pos_all h_nonempty
    have h_eq := Finset.sum_sdiff h_sub (f := c)
    -- h_eq : ∑ i ∈ (range P) \ (range k), c i + ∑ i ∈ range k, c i = ∑ i ∈ range P, c i
    have h_sum_pos : ∑ i ∈ Finset.range k, c i < ∑ i ∈ Finset.range P, c i := by
      linarith
    rw [hsum_period] at h_sum_pos
    exact h_sum_pos
  -- For any k, the partial sum is ≥ 0
  have hsum_nonneg : ∀ k, 0 ≤ ∑ i ∈ Finset.range k, c i := by
    intro k
    have h_nonneg : ∀ i, 0 ≤ c i := fun i => le_of_lt (hc_pos i)
    exact Finset.sum_nonneg (fun i _ => h_nonneg i)
  -- Main induction on j
  induction' j with j ih
  · -- base case j = 0
    simp [ocorner_self]
  · -- inductive step: prove for j.succ
    have hj_lt_P : j.succ < P := hj
    have hj_lt_P' : j < P := Nat.lt_of_succ_lt hj
    -- Use rot_pow_succ_apply to relate iterates
    have h_rot_succ_eq : (R.rot ^ j.succ) e = R.rot ((R.rot ^ j) e) := by
      simpa using (rot_pow_succ_apply R e j).symm
    -- Apply ocorner_add
    have h_add := ocorner_add (x v) (x e.snd) (x ((R.rot ^ j) e).snd)
      (x (R.rot ((R.rot ^ j) e)).snd)
      hx_v
      (h_tdir_ne_zero 0)
      (h_tdir_ne_zero j)
      (by
        -- need tdir (x v) (x (R.rot ((R.rot ^ j) e)).snd) ≠ 0
        -- we have h_tdir_ne_zero (j+1) which gives tdir (x v) (x ((R.rot ^ (j+1)) e).snd) ≠ 0
        -- but we need it for R.rot ((R.rot ^ j) e), which equals (R.rot ^ (j+1)) e
        have h_rot_eq : R.rot ((R.rot ^ j) e) = (R.rot ^ (j + 1)) e := by
          simpa [add_comm] using rot_pow_succ_apply R e j
        rw [h_rot_eq]
        exact h_tdir_ne_zero (j + 1))
    -- Simplify R.rot ((R.rot ^ j) e) = (R.rot ^ (j+1)) e in h_add
    have h_rot_eq : R.rot ((R.rot ^ j) e) = (R.rot ^ (j + 1)) e := by
      simpa [add_comm] using rot_pow_succ_apply R e j
    rw [h_rot_eq] at h_add
    -- h_add: ocorre (x v) (x e.snd) (x ((R.rot ^ (j+1)) e).snd) =
    --   toIcoMod two_pi_pos 0 (ocorner (x v) (x e.snd) (x ((R.rot ^ j) e).snd) + c j)
    -- By IH: ocorre (x v) (x e.snd) (x ((R.rot ^ j) e).snd) = ∑ i ∈ range j, c i
    rw [ih hj_lt_P'] at h_add
    -- h_add: ... = toIcoMod two_pi_pos 0 ((∑ i ∈ range j, c i) + c j)
    have h_sum_eq : (∑ i ∈ Finset.range j, c i) + c j = ∑ i ∈ Finset.range j.succ, c i := by
      simp [Finset.sum_range_succ]
    rw [h_sum_eq] at h_add
    -- Now h_add: ocorre (x v) (x e.snd) (x ((R.rot ^ (j+1)) e).snd) =
    --   toIcoMod two_pi_pos 0 (∑ i ∈ range j.succ, c i)
    -- Need to show that ∑ i ∈ range j.succ, c i ∈ Set.Ico (0 : ℝ) (0 + 2 * π)
    have h_mem_Ico : (∑ i ∈ Finset.range j.succ, c i) ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by
      have h_left : (0 : ℝ) ≤ ∑ i ∈ Finset.range j.succ, c i := hsum_nonneg j.succ
      have h_right : ∑ i ∈ Finset.range j.succ, c i < 0 + 2 * π := by
        simpa [zero_add] using hsum_range_lt j.succ hj_lt_P
      exact ⟨h_left, h_right⟩
    -- Apply toIcoMod_eq_self
    have h_toIco_eq := (toIcoMod_eq_self Real.two_pi_pos).mpr h_mem_Ico
    -- h_toIco_eq : toIcoMod two_pi_pos 0 (∑ i ∈ range j.succ, c i) = ∑ i ∈ range j.succ, c i
    rw [h_toIco_eq] at h_add
    -- Now h_add: ocorre (x v) (x e.snd) (x ((R.rot ^ (j+1)) e).snd) = ∑ i ∈ range j.succ, c i
    -- This is exactly what we need
    simpa [v, c] using h_add

/-- The corner function strictly increases along the rotation within one period. -/
theorem ocorner_rot_pow_lt (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hD : DistinctDirs G x)
    (R : RotSys G) (hR : IsAngular R x)
    (hpos : ∀ d : G.Dart, 0 < ocorner (x d.fst) (x d.snd) (x (R.rot d).snd)) (e : G.Dart)
    (hv : ∃ a b, a ≠ b ∧ G.Adj e.fst a ∧ G.Adj e.fst b) {i j : ℕ} (hij : i < j)
    (hj : j < Function.minimalPeriod R.rot e) :
    ocorner (x e.fst) (x e.snd) (x ((R.rot ^ i) e).snd) <
      ocorner (x e.fst) (x e.snd) (x ((R.rot ^ j) e).snd) := by
  rw [ocorner_rot_pow x hx hD R hR hpos e hv i (hij.trans hj),
    ocorner_rot_pow x hx hD R hR hpos e hv j hj]
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun k => ocorner (x e.fst) (x ((R.rot ^ k) e).snd) (x ((R.rot ^ (k + 1)) e).snd)) hij.le
  rw [← hsplit, lt_add_iff_pos_right]
  refine Finset.sum_pos (fun k _ => ?_) ⟨i, Finset.mem_Ico.mpr ⟨le_rfl, hij⟩⟩
  have h := hpos ((R.rot ^ k) e)
  rwa [rot_pow_fst, rot_pow_succ_apply] at h

end Angular

/-! ## The graph inside the hull -/

section Block

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A dart of `G` as a dart of the hull graph. -/
def hdart (x : V → E3) (hexp : ∀ a b, G.Adj a b → ExposedPair x a b) (e : G.Dart) :
    (hullGraph x).Dart :=
  ⟨e.toProd, hexp _ _ e.adj⟩

omit [Fintype V] [DecidableEq V] in
theorem hdart_toProd (x : V → E3) (hexp : ∀ a b, G.Adj a b → ExposedPair x a b) (e : G.Dart) :
    (hdart x hexp e).toProd = e.toProd := rfl

omit [Fintype V] [DecidableEq V] in
theorem hdart_injective (x : V → E3) (hexp : ∀ a b, G.Adj a b → ExposedPair x a b) :
    Function.Injective (hdart x hexp) := by
  intro e f h
  have h' := congrArg (fun d : (hullGraph x).Dart => d.toProd) h
  exact SimpleGraph.Dart.ext _ _ h'

/-- A dart of the hull whose ends are adjacent in `G`, as a dart of `G`. -/
def gdart (x : V → E3) (d : (hullGraph x).Dart) (h : G.Adj d.fst d.snd) : G.Dart :=
  ⟨d.toProd, h⟩

omit [Fintype V] [DecidableEq V] in
theorem hdart_gdart (x : V → E3) (hexp : ∀ a b, G.Adj a b → ExposedPair x a b)
    (d : (hullGraph x).Dart) (h : G.Adj d.fst d.snd) : hdart x hexp (gdart x d h) = d := rfl

/-- Positive corners give distinct directions (item K1). -/
theorem distinctDirs_of_corner (x : V → E3) (_hx : ∀ v, ‖x v‖ = 1) (R : RotSys G)
    (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π) :
    DistinctDirs G x := by
  refine ⟨fun v w hvw h => ?_, fun v a b ha hb hab h => ?_⟩
  · have h' := (hcorner ⟨(v, w), hvw⟩).1
    rw [ocorner_of_tdir_eq_zero _ _ _ h] at h'
    exact lt_irrefl _ h'
  · let ea : G.Dart := ⟨(v, a), ha⟩
    let eb : G.Dart := ⟨(v, b), hb⟩
    have hne : eb ≠ ea := fun h' => hab (congrArg (fun d : G.Dart => d.snd) h').symm
    have hle := hR ea eb rfl hne
    have hpos := (hcorner ea).1
    have h0 : ocorner (x ea.fst) (x ea.snd) (x eb.snd) = 0 := h
    linarith

/-- G1 and G2: the successor of a dart `e` of `G` is the first dart of `G` counterclockwise from
`e` in the hull rotation, and the corner at `e` is the sum of the hull corners in between. -/
theorem block (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (rho : RotSys (hullGraph x))
    (hrho : IsAngular rho x) (hexp : ∀ a b, G.Adj a b → ExposedPair x a b) (R : RotSys G)
    (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (e : G.Dart) :
    ∃ k, 0 < k ∧ (rho.rot ^ k) (hdart x hexp e) = hdart x hexp (R.rot e) ∧
      (∀ i, 0 < i → i < k → ¬ G.Adj e.fst ((rho.rot ^ i) (hdart x hexp e)).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) =
        ∑ i ∈ Finset.range k, rcorner x rho ((rho.rot ^ i) (hdart x hexp e)) := by
  have hD := hull_distinctDirs x hx hinj hB
  have hpos : ∀ d : (hullGraph x).Dart, 0 < ocorner (x d.fst) (x d.snd) (x (rho.rot d).snd) :=
    hull_rot_pos x hx hinj hB rho hrho
  set d0 := hdart x hexp e with hd0
  have h2 : ∃ a b, a ≠ b ∧ (hullGraph x).Adj d0.fst a ∧ (hullGraph x).Adj d0.fst b :=
    hull_two_nbrs x hx hinj hB d0.fst
  have hf_ne : R.rot e ≠ e := by
    intro h
    have h' := (hcorner e).1
    rw [h, ocorner_self] at h'
    exact lt_irrefl _ h'
  obtain ⟨k, hkP, hk⟩ := rot_pow_surj rho d0 (hdart x hexp (R.rot e)) (R.rot_fst e)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [pow_zero, Equiv.Perm.one_apply] at hk
      exact absurd (hdart_injective x hexp hk).symm hf_ne
    · exact h
  refine ⟨k, hk0, hk, fun i hi hik hadj => ?_, ?_⟩
  · set g : G.Dart := ⟨(e.fst, ((rho.rot ^ i) d0).snd), hadj⟩ with hg
    have hg_ne : g ≠ e := by
      intro h
      have hsnd : ((rho.rot ^ i) d0).snd = e.snd := congrArg (fun d : G.Dart => d.snd) h
      have hfst : ((rho.rot ^ i) d0).fst = e.fst := rot_pow_fst rho d0 i
      have h' : (rho.rot ^ i) d0 = d0 := SimpleGraph.Dart.ext _ _ (Prod.ext hfst hsnd)
      exact rot_pow_ne_self rho d0 hi (hik.trans hkP) h'
    have hle := hR e g rfl hg_ne
    have hlt := ocorner_rot_pow_lt x hx hD rho hrho hpos d0 h2 hik hkP
    rw [hk] at hlt
    exact absurd hle (not_le.mpr hlt)
  · have hθk := ocorner_rot_pow x hx hD rho hrho hpos d0 h2 k hkP
    rw [hk] at hθk
    refine hθk.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [rcorner, rot_pow_fst, rot_pow_succ_apply]

end Block

end Tammes15
