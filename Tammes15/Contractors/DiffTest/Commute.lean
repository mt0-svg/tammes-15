import Tammes15.Contractors.Prims
import Tammes15.Contractors.DiffTest.PrimsQ

/-!
# The computable copy runs Prims.lean (the differential test, Section 10.4 of the paper)

The embeddings `embF : FlQ → Fl`, `embI : IvQ → Iv`, `embB : BoxQ ι → Box ι` and `embRow` read a
rational as a real. They are injective, so an arithmetic `R : RndQ` lifts to `lift R : Rnd`, whose
operations agree with those of `R` on embedded arguments. Each definition of PrimsQ.lean commutes
with the embeddings: `embI (Q.side R b c a) = side (lift R) (embI b) (embI c) (embI a)`, and so on.
So the value of a definition of PrimsQ.lean, computed by Lean, is the value of the definition
of Prims.lean at the arithmetic `lift R`, read back through the embedding.

The steps on a box are stated for any index type (`pentStepG` and the others: the bodies of Prims.lean
with the variables `fv e j` and `.d` replaced by indices `v j` and `jd`); each step of Prims.lean is its
generic copy at `v = fv e`, `jd = .d`, by `rfl`.
-/

namespace Tammes15.Contractors.Q

open Real
open Tammes15 Tammes15.PaperSteps Tammes15.PaperSteps.Search

/-! ## The embeddings -/

/-- A rational float as a float of `Fl`. -/
noncomputable def embF : FlQ → Fl
  | .fin q => Fl.ofReal (q : ℝ)
  | .top => Fl.inf
  | .bot => Fl.ninf
  | .nan => Fl.nan

/-- An interval of rational floats as an interval of `Iv`. -/
noncomputable def embI (I : IvQ) : Iv := ⟨embF I.lo, embF I.hi⟩

/-- A box with rational ends as a box with real ends. -/
def embB {ι : Type} (B : BoxQ ι) : Box ι := ⟨fun i => (B.lo i : ℝ), fun i => (B.hi i : ℝ)⟩

/-- A row with rational coefficients as a row of `Prims`. -/
noncomputable def embRow {ι : Type} (r : RowQ ι) : Row ι :=
  ⟨r.terms.map fun t => (t.1, (t.2 : ℝ)), embF r.lo, embF r.hi⟩

theorem embF_injective : Function.Injective embF := by
  intro a b h
  cases a <;> cases b <;> simp_all [embF, Fl.ofReal, Fl.inf, Fl.ninf]

theorem embI_injective : Function.Injective embI := by
  intro I J h
  simp only [embI, Iv.mk.injEq] at h
  cases I; cases J
  simp only [IvQ.mk.injEq]
  exact ⟨embF_injective h.1, embF_injective h.2⟩

@[simp] theorem embI_lo (I : IvQ) : (embI I).lo = embF I.lo := rfl
@[simp] theorem embI_hi (I : IvQ) : (embI I).hi = embF I.hi := rfl
theorem embI_mk (a b : FlQ) : embI ⟨a, b⟩ = ⟨embF a, embF b⟩ := rfl

/-- Push an interval written by its ends back into `embI`. -/
@[simp] theorem mk_embF (a b : FlQ) : (⟨embF a, embF b⟩ : Iv) = embI ⟨a, b⟩ := rfl

@[simp] theorem pt_embF (x : FlQ) : Iv.pt (embF x) = embI (IvQ.pt x) := rfl

@[simp] theorem ofReal_ratCast (q : ℚ) : Fl.ofReal (q : ℝ) = embF (.fin q) := rfl
@[simp] theorem inf_eq : Fl.inf = embF .top := rfl
@[simp] theorem ninf_eq : Fl.ninf = embF .bot := rfl
@[simp] theorem ofReal_zero : Fl.ofReal 0 = embF (.fin 0) := by simp [embF]
@[simp] theorem ofReal_one : Fl.ofReal 1 = embF (.fin 1) := by simp [embF]
@[simp] theorem ofReal_neg_one : Fl.ofReal (-1) = embF (.fin (-1)) := by simp [embF]
theorem ofReal_two_mul (q : ℚ) : Fl.ofReal (2 * (q : ℝ)) = embF (.fin (2 * q)) := by simp [embF]

@[simp] theorem embF_le_iff (a b : FlQ) : Fl.le (embF a) (embF b) ↔ FlQ.le a b := by
  cases a <;> cases b <;>
    simp [embF, Fl.le, FlQ.le, FlQ.ble, Fl.ofReal, Fl.inf, Fl.ninf, EReal.coe_le_coe_iff]

@[simp] theorem embF_lt_iff (a b : FlQ) : Fl.lt (embF a) (embF b) ↔ FlQ.lt a b := by
  cases a <;> cases b <;>
    simp [embF, Fl.lt, FlQ.lt, FlQ.blt, Fl.ofReal, Fl.inf, Fl.ninf, EReal.coe_lt_coe_iff]

@[simp] theorem embF_max (a b : FlQ) : Fl.max (embF a) (embF b) = embF (FlQ.max a b) := by
  cases a <;> cases b <;>
    simp [embF, Fl.max, FlQ.max, FlQ.ble, Fl.ofReal, Fl.inf, Fl.ninf, max_def] <;>
    split_ifs <;> simp_all [Fl.ofReal]

@[simp] theorem embF_min (a b : FlQ) : Fl.min (embF a) (embF b) = embF (FlQ.min a b) := by
  cases a <;> cases b <;>
    simp [embF, Fl.min, FlQ.min, FlQ.ble, Fl.ofReal, Fl.inf, Fl.ninf, min_def] <;>
    split_ifs <;> simp_all [Fl.ofReal]

@[simp] theorem embF_isFinite (a : FlQ) : (embF a).IsFinite ↔ a.IsFinite := by
  cases a <;> simp [embF, Fl.IsFinite, FlQ.IsFinite, FlQ.isFin, Fl.ofReal, Fl.inf, Fl.ninf]

@[simp] theorem embF_toReal (a : FlQ) : (embF a).toReal = (a.toQ : ℝ) := by
  cases a <;> simp [embF, Fl.toReal, FlQ.toQ, Fl.ofReal, Fl.inf, Fl.ninf]

@[simp] theorem usable_embI (I : IvQ) : (embI I).Usable ↔ I.Usable := by
  simp [Iv.Usable, IvQ.Usable]

@[simp] theorem meet_embI (I J : IvQ) : (embI I).meet (embI J) = embI (I.meet J) := by
  simp only [Iv.meet, IvQ.meet, embI_lo, embI_hi, embF_max, embF_min]; rfl

@[simp] theorem ivOf_embB {ι : Type} (B : BoxQ ι) (j : ι) :
    Contractors.ivOf (embB B) j = embI (ivOf B j) := rfl

theorem embB_injective {ι : Type} : Function.Injective (embB (ι := ι)) := by
  intro B C h
  cases B; cases C
  simp only [embB, Box.mk.injEq] at h
  simp only [BoxQ.mk.injEq]
  constructor
  · funext i; exact_mod_cast congrFun h.1 i
  · funext i; exact_mod_cast congrFun h.2 i

/-- An update of rational ends, read as reals. -/
theorem embB_upd {ι : Type} [DecidableEq ι] (B : BoxQ ι) (j : ι) (a b : ℚ) :
    embB (⟨updQ B.lo j a, updQ B.hi j b⟩ : BoxQ ι) =
      ⟨Function.update (fun i => (B.lo i : ℝ)) j (a : ℝ),
        Function.update (fun i => (B.hi i : ℝ)) j (b : ℝ)⟩ := by
  simp only [embB, Box.mk.injEq]
  constructor <;> funext i <;> by_cases h : i = j <;> simp [updQ, Function.update, h]

/-! ## The lifted arithmetic -/

/-- A preimage under `embF` (any value off the image). -/
noncomputable def preF : Fl → FlQ := Function.invFun embF

/-- A preimage under `embI`. -/
noncomputable def preI : Iv → IvQ := Function.invFun embI

@[simp] theorem preF_embF (a : FlQ) : preF (embF a) = a :=
  Function.leftInverse_invFun embF_injective a

@[simp] theorem preI_embI (I : IvQ) : preI (embI I) = I :=
  Function.leftInverse_invFun embI_injective I

/-- The arithmetic `R`, read on `Fl`: each operation on embedded arguments is the embedding of the
operation of `R`. -/
noncomputable def lift (R : RndQ) : Rnd where
  add I J := embI (R.add (preI I) (preI J))
  sub I J := embI (R.sub (preI I) (preI J))
  mul I J := embI (R.mul (preI I) (preI J))
  div I J := embI (R.div (preI I) (preI J))
  cos I := embI (R.cos (preI I))
  sin I := embI (R.sin (preI I))
  acos I := embI (R.acos (preI I))
  asin I := embI (R.asin (preI I))
  atan I := embI (R.atan (preI I))
  tan I := embI (R.tan (preI I))
  addDn a b := embF (R.addDn (preF a) (preF b))
  addUp a b := embF (R.addUp (preF a) (preF b))
  subDn a b := embF (R.subDn (preF a) (preF b))
  subUp a b := embF (R.subUp (preF a) (preF b))
  mulDn a b := embF (R.mulDn (preF a) (preF b))
  mulUp a b := embF (R.mulUp (preF a) (preF b))
  divDn a b := embF (R.divDn (preF a) (preF b))
  divUp a b := embF (R.divUp (preF a) (preF b))
  piLo := R.piLo
  piHi := R.piHi
  twoPiLo := R.twoPiLo
  twoPiHi := R.twoPiHi

section Lift

variable (R : RndQ) (I J : IvQ) (a b : FlQ)

@[simp] theorem lift_add : (lift R).add (embI I) (embI J) = embI (R.add I J) := by simp [lift]
@[simp] theorem lift_sub : (lift R).sub (embI I) (embI J) = embI (R.sub I J) := by simp [lift]
@[simp] theorem lift_mul : (lift R).mul (embI I) (embI J) = embI (R.mul I J) := by simp [lift]
@[simp] theorem lift_div : (lift R).div (embI I) (embI J) = embI (R.div I J) := by simp [lift]
@[simp] theorem lift_cos : (lift R).cos (embI I) = embI (R.cos I) := by simp [lift]
@[simp] theorem lift_sin : (lift R).sin (embI I) = embI (R.sin I) := by simp [lift]
@[simp] theorem lift_acos : (lift R).acos (embI I) = embI (R.acos I) := by simp [lift]
@[simp] theorem lift_asin : (lift R).asin (embI I) = embI (R.asin I) := by simp [lift]
@[simp] theorem lift_atan : (lift R).atan (embI I) = embI (R.atan I) := by simp [lift]
@[simp] theorem lift_tan : (lift R).tan (embI I) = embI (R.tan I) := by simp [lift]
@[simp] theorem lift_addDn : (lift R).addDn (embF a) (embF b) = embF (R.addDn a b) := by simp [lift]
@[simp] theorem lift_addUp : (lift R).addUp (embF a) (embF b) = embF (R.addUp a b) := by simp [lift]
@[simp] theorem lift_subDn : (lift R).subDn (embF a) (embF b) = embF (R.subDn a b) := by simp [lift]
@[simp] theorem lift_subUp : (lift R).subUp (embF a) (embF b) = embF (R.subUp a b) := by simp [lift]
@[simp] theorem lift_mulDn : (lift R).mulDn (embF a) (embF b) = embF (R.mulDn a b) := by simp [lift]
@[simp] theorem lift_mulUp : (lift R).mulUp (embF a) (embF b) = embF (R.mulUp a b) := by simp [lift]
@[simp] theorem lift_divDn : (lift R).divDn (embF a) (embF b) = embF (R.divDn a b) := by simp [lift]
@[simp] theorem lift_divUp : (lift R).divUp (embF a) (embF b) = embF (R.divUp a b) := by simp [lift]
@[simp] theorem lift_piLo : (lift R).piLo = (R.piLo : ℝ) := rfl
@[simp] theorem lift_piHi : (lift R).piHi = (R.piHi : ℝ) := rfl
@[simp] theorem lift_twoPiLo : (lift R).twoPiLo = (R.twoPiLo : ℝ) := rfl
@[simp] theorem lift_twoPiHi : (lift R).twoPiHi = (R.twoPiHi : ℝ) := rfl

@[simp] theorem lift_scale (c : ℚ) : (lift R).scale (embI I) (c : ℝ) = embI (R.scale I c) := by
  simp [Rnd.scale, RndQ.scale]

theorem lift_scale_half : (lift R).scale (embI I) 0.5 = embI (R.scale I (1 / 2)) := by
  rw [← lift_scale]; norm_num

theorem lift_scale_two : (lift R).scale (embI I) 2 = embI (R.scale I 2) := by
  rw [← lift_scale]; norm_num

theorem lift_scale_three : (lift R).scale (embI I) 3 = embI (R.scale I 3) := by
  rw [← lift_scale]; norm_num

end Lift

/-- The embedding of the two outcomes of `triAngleSt`. -/
noncomputable def embE : Except IvQ IvQ → Except Iv Iv
  | .ok v => .ok (embI v)
  | .error v => .error (embI v)

@[simp] theorem embE_ok (v : IvQ) : embE (.ok v) = .ok (embI v) := rfl
@[simp] theorem embE_error (v : IvQ) : embE (.error v) = .error (embI v) := rfl

/-! Moving the embeddings out of a branch, whatever the decision procedure of the branch (the
definitions of Prims.lean decide classically, the copies by computation). -/

theorem fst_ite' {α β : Type} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).1 = if c then x.1 else y.1 := by split_ifs <;> rfl

theorem snd_ite' {α β : Type} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).2 = if c then x.2 else y.2 := by split_ifs <;> rfl

theorem ite_embI {c : Prop} [Decidable c] (a b : IvQ) :
    (if c then embI a else embI b) = embI (if c then a else b) := by split_ifs <;> rfl

theorem ite_embF {c : Prop} [Decidable c] (a b : FlQ) :
    (if c then embF a else embF b) = embF (if c then a else b) := by split_ifs <;> rfl

theorem embE_ite {c : Prop} [Decidable c] (x y : Except IvQ IvQ) :
    embE (if c then x else y) = if c then embE x else embE y := by split_ifs <;> rfl

theorem map_ite' {α β : Type} (f : α → β) {c : Prop} [Decidable c] (x y : Option α) :
    (if c then x else y).map f = if c then x.map f else y.map f := by split_ifs <;> rfl

/-- The rewriting of a definition of Prims.lean at `lift R` on embedded arguments into the embedding of
the copy (used with `open scoped Classical`, so that every intermediate branch condition is
decidable). -/
macro "comm_simp" : tactic => `(tactic| simp only [lift_add, lift_sub, lift_mul, lift_div,
  lift_cos, lift_sin, lift_acos, lift_asin, lift_atan, lift_tan, lift_addDn, lift_addUp,
  lift_subDn, lift_subUp, lift_mulDn, lift_mulUp, lift_divDn, lift_divUp, lift_scale_half,
  lift_scale_two, lift_scale_three, lift_piLo, lift_piHi, lift_twoPiLo, lift_twoPiHi, pt_embF,
  mk_embF, embI_lo, embI_hi, embF_max, embF_min, embF_le_iff, embF_lt_iff, usable_embI,
  embF_isFinite, embF_toReal, ofReal_ratCast, ofReal_zero, ofReal_one, ofReal_neg_one, inf_eq,
  ninf_eq, ofReal_two_mul, meet_embI, ivOf_embB, Rat.cast_nonneg, Rat.cast_pos, Rat.cast_eq_zero, Rat.cast_lt,
  Rat.cast_le, fst_ite', snd_ite', ite_embI, ite_embF, embE_ite, embE_ok, embE_error, map_ite',
  Option.map_some, Option.map_none])

/-! ## The primitives on intervals -/

section Prims

open scoped Classical

variable (R : RndQ)

theorem nar_comm {ι : Type} [DecidableEq ι] (B : BoxQ ι) (j : ι) (n : IvQ) :
    (nar B j n).map embB = Contractors.nar (embB B) j (embI n) := by
  unfold nar Contractors.nar
  have hl : ∀ i, (embB B).lo i = (B.lo i : ℝ) := fun _ => rfl
  have hh : ∀ i, (embB B).hi i = (B.hi i : ℝ) := fun _ => rfl
  simp only [hl, hh, ofReal_ratCast, embI_lo, embI_hi, embF_min, embF_max, embF_lt_iff,
    usable_embI, embF_toReal]
  split_ifs <;> simp [embB_upd] <;> constructor <;> funext i <;> by_cases h : i = j <;>
    simp [h, embB, Function.update_apply]

theorem isoBase_comm (u d : IvQ) :
    embI (isoBase R u d) = Contractors.isoBase (lift R) (embI u) (embI d) := by
  simp only [isoBase, Contractors.isoBase, lift_scale_half, lift_sin, lift_mul, lift_asin,
    lift_scale_two]

theorem isoAngle_comm (u d : IvQ) :
    embI (isoAngle R u d) = Contractors.isoAngle (lift R) (embI u) (embI d) := by
  unfold isoAngle Contractors.isoAngle; comm_simp

theorem inOpen_iff (I : IvQ) : Contractors.InOpen (lift R) (embI I) ↔ InOpen R I := by
  unfold InOpen Contractors.InOpen; comm_simp

theorem triAngleSt_comm (g e f : IvQ) :
    embE (triAngleSt R g e f) =
      Contractors.triAngleSt (lift R) (embI g) (embI e) (embI f) := by
  unfold triAngleSt Contractors.triAngleSt Contractors.InOpen; comm_simp

theorem triAngle_comm (g e f : IvQ) :
    (triAngle R g e f).map embI = Contractors.triAngle (lift R) (embI g) (embI e) (embI f) := by
  unfold triAngle Contractors.triAngle; rw [← triAngleSt_comm]
  cases triAngleSt R g e f <;> rfl

theorem triAngleC_comm (g e f : IvQ) :
    embI (triAngleC R g e f) = Contractors.triAngleC (lift R) (embI g) (embI e) (embI f) := by
  unfold triAngleC Contractors.triAngleC; rw [← triAngleSt_comm]
  cases triAngleSt R g e f <;> rfl

theorem alphaIv_comm (d : IvQ) : embI (alphaIv R d) = Contractors.alphaIv (lift R) (embI d) := by
  unfold alphaIv Contractors.alphaIv; comm_simp

theorem alphaInvIv_comm (a : IvQ) :
    embI (alphaInvIv R a) = Contractors.alphaInvIv (lift R) (embI a) := by
  unfold alphaInvIv Contractors.alphaInvIv; comm_simp

theorem rhoIv_comm (x d : IvQ) :
    embI (rhoIv R x d) = Contractors.rhoIv (lift R) (embI x) (embI d) := by
  unfold rhoIv Contractors.rhoIv; comm_simp

theorem rhombusD_comm (x y : IvQ) :
    (rhombusD R x y).map embI = Contractors.rhombusD (lift R) (embI x) (embI y) := by
  unfold rhombusD Contractors.rhombusD; comm_simp

theorem side_comm (b c ang : IvQ) :
    (side R b c ang).map embI = Contractors.side (lift R) (embI b) (embI c) (embI ang) := by
  unfold side Contractors.side; comm_simp

theorem longdiagLb_comm (u d : IvQ) :
    embF (longdiagLb R u d) = Contractors.longdiagLb (lift R) (embI u) (embI d) := by
  unfold longdiagLb Contractors.longdiagLb
  comm_simp; rw [← isoBase_comm, ← isoAngle_comm]; comm_simp

theorem cornerEnds_comm (u : IvQ) :
    ((embI (cornerEnds R u).1, embI (cornerEnds R u).2) : Iv × Iv) =
      Contractors.cornerEnds (lift R) (embI u) := by
  unfold cornerEnds Contractors.cornerEnds; comm_simp

theorem decDir_comm (u bx x d : IvQ) :
    decDir R u bx x d = Contractors.decDir (lift R) (embI u) (embI bx) (embI x) (embI d) := by
  unfold decDir Contractors.decDir; comm_simp

theorem monoBounds_comm {K : ℕ} (inp : Fin K → IvQ) (ends : Fin K → IvQ × IvQ)
    (dirs : Fin 3 → Fin K → ℤ) (evalQ : (Fin K → IvQ) → Fin 3 → IvQ)
    (eval : (Fin K → Iv) → Fin 3 → Iv)
    (hev : ∀ x k, embI (evalQ x k) = eval (fun j => embI (x j)) k) (k : Fin 3) :
    embI (monoBounds inp ends dirs evalQ k) =
      Contractors.monoBounds (fun j => embI (inp j)) (fun j => (embI (ends j).1, embI (ends j).2))
        dirs eval k := by
  simp only [Q.monoBounds, Contractors.monoBounds, embI_mk]
  simp only [Iv.mk.injEq, ← embI_lo, ← embI_hi, hev]
  refine ⟨?_, ?_⟩
  · simp [ite_embI]
  · simp [ite_embI]

theorem vec2_eq {α : Type} (a b : α) : vec2 a b = ![a, b] := by
  funext k; fin_cases k <;> rfl

theorem vec3_eq {α : Type} (a b c : α) : vec3 a b c = ![a, b, c] := by
  funext k; fin_cases k <;> rfl

theorem pentEvalC_comm (d : IvQ) (x : Fin 2 → IvQ) (k : Fin 3) :
    embI (pentEvalC R d x k) =
      Contractors.pentEvalC (lift R) (embI d) (fun j => embI (x j)) k := by
  simp only [Q.pentEvalC, Contractors.pentEvalC, vec3_eq]
  fin_cases k <;> simp [← lift_add, ← isoBase_comm, ← isoAngle_comm, ← triAngleC_comm]

theorem hexEvalC_comm (d : IvQ) (x : Fin 3 → IvQ) (k : Fin 3) :
    embI (hexEvalC R d x k) =
      Contractors.hexEvalC (lift R) (embI d) (fun j => embI (x j)) k := by
  unfold Q.hexEvalC Contractors.hexEvalC
  rw [vec3_eq]
  fin_cases k <;>
    simp [Matrix.cons_val, ← isoBase_comm, ← isoAngle_comm,
      ← triAngleC_comm, ← lift_add]

/-- `monoBounds_comm` at the inputs of `pentStep`, written as the step of Prims.lean writes them. -/
theorem monoBounds2_comm (a b : IvQ) (dirs : Fin 3 → Fin 2 → ℤ)
    (evalQ : (Fin 2 → IvQ) → Fin 3 → IvQ) (eval : (Fin 2 → Iv) → Fin 3 → Iv)
    (hev : ∀ x k, embI (evalQ x k) = eval (fun j => embI (x j)) k) (k : Fin 3) :
    Contractors.monoBounds ![embI a, embI b]
        ![Contractors.cornerEnds (lift R) (embI a), Contractors.cornerEnds (lift R) (embI b)]
        dirs eval k =
      embI (monoBounds ![a, b] ![cornerEnds R a, cornerEnds R b] dirs evalQ k) := by
  rw [monoBounds_comm _ _ dirs evalQ eval hev k]
  congr 1
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> simp [← cornerEnds_comm]

/-- `monoBounds_comm` at the inputs of `hexStep`, written as the step of Prims.lean writes them. -/
theorem monoBounds3_comm (a b c : IvQ) (dirs : Fin 3 → Fin 3 → ℤ)
    (evalQ : (Fin 3 → IvQ) → Fin 3 → IvQ) (eval : (Fin 3 → Iv) → Fin 3 → Iv)
    (hev : ∀ x k, embI (evalQ x k) = eval (fun j => embI (x j)) k) (k : Fin 3) :
    Contractors.monoBounds ![embI a, embI b, embI c]
        ![Contractors.cornerEnds (lift R) (embI a), Contractors.cornerEnds (lift R) (embI b),
          Contractors.cornerEnds (lift R) (embI c)]
        dirs eval k =
      embI (monoBounds ![a, b, c] ![cornerEnds R a, cornerEnds R b, cornerEnds R c] dirs evalQ
        k) := by
  rw [monoBounds_comm _ _ dirs evalQ eval hev k]
  congr 1
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> simp [← cornerEnds_comm]

theorem cmin_comm (c l u : ℚ) :
    embF (cmin R c l u) = Contractors.cmin (lift R) c l u := by
  unfold cmin Contractors.cmin; comm_simp

theorem cmax_comm (c l u : ℚ) :
    embF (cmax R c l u) = Contractors.cmax (lift R) c l u := by
  unfold cmax Contractors.cmax; comm_simp

theorem ite_cast {c : Prop} {_ : Decidable c} (a b : ℚ) :
    (if c then (a : ℝ) else (b : ℝ)) = ((if c then a else b : ℚ) : ℝ) := by split_ifs <;> rfl

@[simp] theorem embRow_lo {ι : Type} (r : RowQ ι) : (embRow r).lo = embF r.lo := rfl
@[simp] theorem embRow_hi {ι : Type} (r : RowQ ι) : (embRow r).hi = embF r.hi := rfl

theorem rowUpd_comm {ι : Type} [DecidableEq ι] (r : RowQ ι) (smin smax : FlQ)
    (l : List ((ι × ℚ) × FlQ × FlQ)) (B : BoxQ ι) :
    (rowUpd R r smin smax l B).map embB =
      Contractors.rowUpd (lift R) (embRow r) (embF smin) (embF smax)
        (l.map fun t => ((t.1.1, (t.1.2 : ℝ)), embF t.2.1, embF t.2.2)) (embB B) := by
  induction l generalizing B with
  | nil => rfl
  | cons t l ih =>
    obtain ⟨⟨v, c⟩, mn, mx⟩ := t
    simp only [List.map_cons, rowUpd, Contractors.rowUpd]
    by_cases hc : c = 0
    · simp [hc, ih]
    · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      simp only [hc, hc', ite_false, embRow_lo, embRow_hi]
      have hl : (embB B).lo v = (B.lo v : ℝ) := rfl
      have hh : (embB B).hi v = (B.hi v : ℝ) := rfl
      have hl' : (embB B).lo = fun i => (B.lo i : ℝ) := rfl
      have hh' : (embB B).hi = fun i => (B.hi i : ℝ) := rfl
      simp only [hl, hh]
      comm_simp
      simp only [ite_cast, Rat.cast_lt]
      rw [hl', hh']
      congr 1
      rw [ih, embB_upd]
      congr <;> exact Subsingleton.elim _ _

theorem zip3_map {α β γ α' β' γ' : Type} (f : α → α') (g : β → β') (h : γ → γ')
    (a : List α) (b : List β) (c : List γ) :
    (a.map f).zip ((b.map g).zip (c.map h)) =
      (a.zip (b.zip c)).map fun t => (f t.1, g t.2.1, h t.2.2) := by
  induction a generalizing b c with
  | nil => rfl
  | cons x a ih =>
    cases b with
    | nil => rfl
    | cons y b =>
      cases c with
      | nil => rfl
      | cons z c => simp only [List.map_cons, List.zip_cons_cons, ih]

@[simp] theorem embRow_terms {ι : Type} (r : RowQ ι) :
    (embRow r).terms = r.terms.map fun t => (t.1, (t.2 : ℝ)) := rfl

theorem foldl_dn_comm (l : List FlQ) (z : FlQ) :
    (l.map embF).foldl (lift R).addDn (embF z) = embF (l.foldl R.addDn z) := by
  induction l generalizing z with
  | nil => rfl
  | cons t l ih => simp only [List.foldl_cons, List.map_cons, lift_addDn, ih]

theorem foldl_up_comm (l : List FlQ) (z : FlQ) :
    (l.map embF).foldl (lift R).addUp (embF z) = embF (l.foldl R.addUp z) := by
  induction l generalizing z with
  | nil => rfl
  | cons t l ih => simp only [List.foldl_cons, List.map_cons, lift_addUp, ih]

theorem rowStep_comm {ι : Type} [DecidableEq ι] (r : RowQ ι) (B : BoxQ ι) :
    (rowStep R r B).map embB = Contractors.rowStep (lift R) (embRow r) (embB B) := by
  have hmn : ((embRow r).terms.map fun t =>
      Contractors.cmin (lift R) t.2 ((embB B).lo t.1) ((embB B).hi t.1)) =
      (r.terms.map fun t => cmin R t.2 (B.lo t.1) (B.hi t.1)).map embF := by
    simp only [embRow, List.map_map]
    congr 1; funext t; exact (cmin_comm R _ _ _).symm
  have hmx : ((embRow r).terms.map fun t =>
      Contractors.cmax (lift R) t.2 ((embB B).lo t.1) ((embB B).hi t.1)) =
      (r.terms.map fun t => cmax R t.2 (B.lo t.1) (B.hi t.1)).map embF := by
    simp only [embRow, List.map_map]
    congr 1; funext t; exact (cmax_comm R _ _ _).symm
  unfold rowStep Contractors.rowStep
  simp only []
  rw [hmn, hmx, ofReal_zero, foldl_dn_comm, foldl_up_comm]
  simp only [embRow_lo, embRow_hi, embF_lt_iff, map_ite', Option.map_none]
  congr 1
  rw [rowUpd_comm]
  congr 1
  rw [embRow_terms, zip3_map]

end Prims

/-! ## The steps on a box over any index type -/

section G

open scoped Classical

variable (R : Rnd) {ι : Type}

/-- `alphaStep` with the variables `a`, `d` at the indices `ja`, `jd`. -/
noncomputable def alphaStepG (B : Box ι) (ja jd : ι) : Option (Box ι) :=
  Contractors.nar B ja (Contractors.alphaIv R (Contractors.ivOf B jd))

/-- `alphaInvStep` over indices. -/
noncomputable def alphaInvStepG (B : Box ι) (ja jd : ι) : Option (Box ι) :=
  Contractors.nar B jd (Contractors.alphaInvIv R (Contractors.ivOf B ja))

/-- `rhoStep` with the corner `j` steps along the face at the index `v j`. -/
noncomputable def rhoStepG (B : Box ι) (v : ℕ → ι) (jd : ι) : Option (Box ι) :=
  Contractors.nar B (v 1) (Contractors.rhoIv R (Contractors.ivOf B (v 0)) (Contractors.ivOf B jd))

/-- `rhoDStep` over indices. -/
noncomputable def rhoDStepG (B : Box ι) (v : ℕ → ι) (jd : ι) : Option (Box ι) :=
  (Contractors.rhombusD R (Contractors.ivOf B (v 0)) (Contractors.ivOf B (v 1))).bind
    (Contractors.nar B jd)

/-- `pentStep` over indices. -/
noncomputable def pentStepG (B : Box ι) (v : ℕ → ι) (jd : ι) : Option (Box ι) :=
  let d := Contractors.ivOf B jd
  let up := Contractors.ivOf B (v 1)
  let um := Contractors.ivOf B (v 4)
  let ee := Contractors.isoBase R up d
  let b1 := Contractors.isoAngle R up d
  let ff := Contractors.isoBase R um d
  let b3 := Contractors.isoAngle R um d
  match Contractors.triAngle R d ee ff, Contractors.triAngle R ff ee d,
    Contractors.triAngle R ee ff d with
  | some gi, some gp, some gm =>
    let nat := ![R.add (R.add b1 gi) b3, R.add b1 gp, R.add b3 gm]
    let dirs : Fin 3 → Fin 2 → ℤ :=
      ![![Contractors.decDir R up (nat 1) gp d, Contractors.decDir R um (nat 2) gm d],
        ![Contractors.decDir R up (R.add b1 gi) gi d, 1],
        ![1, Contractors.decDir R um (R.add b3 gi) gi d]]
    let mo := Contractors.monoBounds ![up, um]
      ![Contractors.cornerEnds R up, Contractors.cornerEnds R um] dirs (Contractors.pentEvalC R d)
    (Contractors.nar B (v 0) ((nat 0).meet (mo 0))).bind fun B₁ =>
      (Contractors.nar B₁ (v 2) ((nat 1).meet (mo 1))).bind fun B₂ =>
        Contractors.nar B₂ (v 3) ((nat 2).meet (mo 2))
  | _, _, _ => none

/-- `hexStep` over indices. -/
noncomputable def hexStepG (B : Box ι) (v : ℕ → ι) (jd : ι) : Option (Box ι) :=
  let d := Contractors.ivOf B jd
  let u1 := Contractors.ivOf B (v 1)
  let u3 := Contractors.ivOf B (v 3)
  let u5 := Contractors.ivOf B (v 5)
  let e1 := Contractors.isoBase R u1 d
  let b1 := Contractors.isoAngle R u1 d
  let e3 := Contractors.isoBase R u3 d
  let b3 := Contractors.isoAngle R u3 d
  let e5 := Contractors.isoBase R u5 d
  let b5 := Contractors.isoAngle R u5 d
  match Contractors.triAngle R e3 e1 e5, Contractors.triAngle R e5 e1 e3,
    Contractors.triAngle R e1 e3 e5 with
  | some g0, some g2, some g4 =>
    let nat := ![R.add (R.add b5 g0) b1, R.add (R.add b1 g2) b3, R.add (R.add b3 g4) b5]
    let dirs : Fin 3 → Fin 3 → ℤ :=
      ![![Contractors.decDir R u1 (R.add b1 g2) g2 d, 1,
          Contractors.decDir R u5 (R.add b5 g4) g4 d],
        ![Contractors.decDir R u1 (R.add b1 g0) g0 d,
          Contractors.decDir R u3 (R.add b3 g4) g4 d, 1],
        ![1, Contractors.decDir R u3 (R.add b3 g2) g2 d,
          Contractors.decDir R u5 (R.add b5 g0) g0 d]]
    let mo := Contractors.monoBounds ![u1, u3, u5]
      ![Contractors.cornerEnds R u1, Contractors.cornerEnds R u3, Contractors.cornerEnds R u5] dirs
      (Contractors.hexEvalC R d)
    (Contractors.nar B (v 0) ((nat 0).meet (mo 0))).bind fun B₁ =>
      (Contractors.nar B₁ (v 2) ((nat 1).meet (mo 1))).bind fun B₂ =>
        Contractors.nar B₂ (v 4) ((nat 2).meet (mo 2))
  | _, _, _ => none

/-- `diagFwdStep` over indices. -/
noncomputable def diagFwdStepG (B : Box ι) (v : ℕ → ι) (jd : ι) : Option (Box ι) :=
  Contractors.nar B (v 1)
    ⟨Contractors.longdiagLb R (Contractors.ivOf B (v 0)) (Contractors.ivOf B jd), Fl.inf⟩

/-- `diagBwdStep` over indices. -/
noncomputable def diagBwdStepG (B : Box ι) (v : ℕ → ι) (jd : ι) : Option (Box ι) :=
  Contractors.nar B (v 0)
    ⟨Contractors.longdiagLb R (Contractors.ivOf B (v 1)) (Contractors.ivOf B jd), Fl.inf⟩

/-- `wheelTurn` over indices: `v j` the corner `j` steps along the hexagon, `r i` the variable
`r m i`. -/
noncomputable def wheelTurnG (v : ℕ → ι) (r : Fin 6 → ι) (d : Iv) (B : Box ι) (i : Fin 6) :
    Option (Box ι) :=
  let u : ι := v i
  let ri := Contractors.ivOf B (r i)
  (Contractors.triAngle R (Contractors.ivOf B (r (i + 1))) ri d).bind fun a1 =>
  (Contractors.triAngle R (Contractors.ivOf B (r (i - 1))) ri d).bind fun a2 =>
  (Contractors.nar B u (R.add a1 a2)).bind fun B₂ =>
  (Contractors.side R ri d (R.sub (Contractors.ivOf B₂ u) a2)).bind fun rp =>
  (Contractors.nar B₂ (r (i + 1)) rp).bind fun B₃ =>
  (Contractors.side R ri d (R.sub (Contractors.ivOf B₃ u) a1)).bind fun rm =>
  Contractors.nar B₃ (r (i - 1)) rm

/-- `wheelStep` over indices. -/
noncomputable def wheelStepG (v : ℕ → ι) (r : Fin 6 → ι) (jd : ι) (B : Box ι) :
    Option (Box ι) :=
  let d := Contractors.ivOf B jd
  ((List.finRange 6).foldlM (fun B' i => Contractors.nar B' (r i) ⟨d.lo, (R.scale d 3).hi⟩)
    B).bind fun B₁ =>
  ((List.finRange 6).mapM fun i =>
    Contractors.triAngle R d (Contractors.ivOf B₁ (r i)) (Contractors.ivOf B₁ (r (i + 1)))).bind
    fun th =>
  let s := th.foldl R.add (Iv.pt (.ofReal 0))
  if Fl.lt s.hi (.ofReal R.twoPiLo) ∨ Fl.lt (.ofReal R.twoPiHi) s.lo then none
  else (List.finRange 6).foldlM (wheelTurnG R v r d) B₁

variable {P : PlaneGraph} {k : ℕ} (B : Box (PVar P k)) (e : P.G.Dart)

theorem alphaStep_eq : Contractors.alphaStep R B = alphaStepG R B .a .d := rfl
theorem alphaInvStep_eq : Contractors.alphaInvStep R B = alphaInvStepG R B .a .d := rfl
theorem rhoStep_eq : Contractors.rhoStep R B e = rhoStepG R B (fun j => fv e j) .d := rfl
theorem rhoDStep_eq : Contractors.rhoDStep R B e = rhoDStepG R B (fun j => fv e j) .d := rfl
theorem pentStep_eq : Contractors.pentStep R B e = pentStepG R B (fun j => fv e j) .d := rfl
theorem hexStep_eq : Contractors.hexStep R B e = hexStepG R B (fun j => fv e j) .d := rfl
theorem diagFwdStep_eq :
    Contractors.diagFwdStep R B e = diagFwdStepG R B (fun j => fv e j) .d := rfl
theorem diagBwdStep_eq :
    Contractors.diagBwdStep R B e = diagBwdStepG R B (fun j => fv e j) .d := rfl
theorem wheelTurn_eq (H : HexChoice P k) (m : Fin k) (d : Iv) (i : Fin 6) :
    Contractors.wheelTurn R H m d B i =
      wheelTurnG R (fun j => fv (H.base m) j) (fun i => .r m i) d B i := rfl
theorem wheelStep_eq (H : HexChoice P k) (m : Fin k) :
    Contractors.wheelStep R H m B =
      wheelStepG R (fun j => fv (H.base m) j) (fun i => .r m i) .d B := rfl

end G

/-! ## The steps commute -/

section Steps

open scoped Classical

variable (R : RndQ) {ι : Type} [DecidableEq ι] (B : BoxQ ι) (v : ℕ → ι) (jd : ι)

theorem bind_map_comm {α α' β β' : Type} (o : Option α) (f : α → Option β)
    (g : α' → Option β') (e : α → α') (e₂ : β → β') (h : ∀ a, (f a).map e₂ = g (e a)) :
    (o.bind f).map e₂ = (o.map e).bind g := by
  cases o <;> simp [h]

theorem foldlM_map_comm {α β γ : Type} (e : α → β) (f : α → γ → Option α)
    (g : β → γ → Option β) (h : ∀ a c, (f a c).map e = g (e a) c) (l : List γ) (a : α) :
    (l.foldlM f a).map e = l.foldlM g (e a) := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih =>
    simp only [List.foldlM_cons]
    rw [← h]
    cases f a c with
    | none => rfl
    | some a' => exact ih a'

theorem mapM_map_comm {α β γ : Type} (e : α → β) (f : γ → Option α) (g : γ → Option β)
    (h : ∀ c, (f c).map e = g c) (l : List γ) :
    (l.mapM f).map (List.map e) = l.mapM g := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.mapM_cons]
    rw [← h, ← ih]
    cases f c <;> cases List.mapM f l <;> rfl

theorem foldl_add_comm (th : List IvQ) (z : IvQ) :
    embI (th.foldl R.add z) = (th.map embI).foldl (lift R).add (embI z) := by
  induction th generalizing z with
  | nil => rfl
  | cons t th ih => simp only [List.foldl_cons, List.map_cons, ih, lift_add]

/-- The three narrowings that end `pentStep` and `hexStep`. -/
theorem narChain_comm (j0 j1 j2 : ι) (I0 I1 I2 : IvQ) :
    ((nar B j0 I0).bind fun B₁ => (nar B₁ j1 I1).bind fun B₂ => nar B₂ j2 I2).map embB =
      (Contractors.nar (embB B) j0 (embI I0)).bind fun B₁ =>
        (Contractors.nar B₁ j1 (embI I1)).bind fun B₂ => Contractors.nar B₂ j2 (embI I2) := by
  rw [← nar_comm]
  cases nar B j0 I0 with
  | none => rfl
  | some B₁ =>
    simp only [Option.bind_some, Option.map_some]
    rw [← nar_comm]
    cases nar B₁ j1 I1 with
    | none => rfl
    | some B₂ => simp only [Option.bind_some, Option.map_some, nar_comm]

theorem alphaStep_comm (ja : ι) :
    (alphaStep R B ja jd).map embB = alphaStepG (lift R) (embB B) ja jd := by
  simp only [alphaStep, alphaStepG, ivOf_embB, ← alphaIv_comm, ← nar_comm]

theorem alphaInvStep_comm (ja : ι) :
    (alphaInvStep R B ja jd).map embB = alphaInvStepG (lift R) (embB B) ja jd := by
  simp only [alphaInvStep, alphaInvStepG, ivOf_embB, ← alphaInvIv_comm, ← nar_comm]

theorem rhoStep_comm : (rhoStep R B v jd).map embB = rhoStepG (lift R) (embB B) v jd := by
  simp only [rhoStep, rhoStepG, ivOf_embB, ← rhoIv_comm, ← nar_comm]

theorem rhoDStep_comm : (rhoDStep R B v jd).map embB = rhoDStepG (lift R) (embB B) v jd := by
  simp only [rhoDStep, rhoDStepG, ivOf_embB, ← rhombusD_comm]
  cases rhombusD R (ivOf B (v 0)) (ivOf B (v 1)) <;> simp [nar_comm]

theorem pentStep_comm : (pentStep R B v jd).map embB = pentStepG (lift R) (embB B) v jd := by
  simp only [pentStep, pentStepG, ivOf_embB, ← isoBase_comm, ← isoAngle_comm, ← triAngle_comm]
  generalize triAngle R (ivOf B jd) (isoBase R (ivOf B (v 1)) (ivOf B jd))
    (isoBase R (ivOf B (v 4)) (ivOf B jd)) = t1
  generalize triAngle R (isoBase R (ivOf B (v 4)) (ivOf B jd))
    (isoBase R (ivOf B (v 1)) (ivOf B jd)) (ivOf B jd) = t2
  generalize triAngle R (isoBase R (ivOf B (v 1)) (ivOf B jd))
    (isoBase R (ivOf B (v 4)) (ivOf B jd)) (ivOf B jd) = t3
  rcases t1 with _ | gi <;> rcases t2 with _ | gp <;> rcases t3 with _ | gm <;>
    simp only [Option.map_none, Option.map_some]
  simp only [vec2_eq, vec3_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, lift_add, ← decDir_comm]
  rw [monoBounds2_comm R _ _ _ _ _ (pentEvalC_comm R _),
    monoBounds2_comm R _ _ _ _ _ (pentEvalC_comm R _),
    monoBounds2_comm R _ _ _ _ _ (pentEvalC_comm R _), meet_embI, meet_embI, meet_embI,
    ← narChain_comm]

theorem hexStep_comm : (hexStep R B v jd).map embB = hexStepG (lift R) (embB B) v jd := by
  simp only [hexStep, hexStepG, ivOf_embB, ← isoBase_comm, ← isoAngle_comm, ← triAngle_comm]
  generalize triAngle R (isoBase R (ivOf B (v 3)) (ivOf B jd))
    (isoBase R (ivOf B (v 1)) (ivOf B jd)) (isoBase R (ivOf B (v 5)) (ivOf B jd)) = t1
  generalize triAngle R (isoBase R (ivOf B (v 5)) (ivOf B jd))
    (isoBase R (ivOf B (v 1)) (ivOf B jd)) (isoBase R (ivOf B (v 3)) (ivOf B jd)) = t2
  generalize triAngle R (isoBase R (ivOf B (v 1)) (ivOf B jd))
    (isoBase R (ivOf B (v 3)) (ivOf B jd)) (isoBase R (ivOf B (v 5)) (ivOf B jd)) = t3
  rcases t1 with _ | g0 <;> rcases t2 with _ | g2 <;> rcases t3 with _ | g4 <;>
    simp only [Option.map_none, Option.map_some]
  simp only [vec3_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, lift_add, ← decDir_comm]
  rw [monoBounds3_comm R _ _ _ _ _ _ (hexEvalC_comm R _),
    monoBounds3_comm R _ _ _ _ _ _ (hexEvalC_comm R _),
    monoBounds3_comm R _ _ _ _ _ _ (hexEvalC_comm R _), meet_embI, meet_embI, meet_embI,
    ← narChain_comm]

theorem diagFwdStep_comm :
    (diagFwdStep R B v jd).map embB = diagFwdStepG (lift R) (embB B) v jd := by
  simp only [diagFwdStep, diagFwdStepG, ivOf_embB, ← longdiagLb_comm, inf_eq, mk_embF,
    ← nar_comm]

theorem diagBwdStep_comm :
    (diagBwdStep R B v jd).map embB = diagBwdStepG (lift R) (embB B) v jd := by
  simp only [diagBwdStep, diagBwdStepG, ivOf_embB, ← longdiagLb_comm, inf_eq, mk_embF,
    ← nar_comm]

theorem wheelTurn_comm (r : Fin 6 → ι) (d : IvQ) (i : Fin 6) :
    (wheelTurn R v r d B i).map embB = wheelTurnG (lift R) v r (embI d) (embB B) i := by
  unfold Q.wheelTurn wheelTurnG
  simp only [ivOf_embB, ← triAngle_comm]
  cases h1 : triAngle R (ivOf B (r (i + 1))) (ivOf B (r i)) d
  · simp
  · rename_i a1
    simp
    cases h2 : triAngle R (ivOf B (r (i - 1))) (ivOf B (r i)) d
    · simp
    · rename_i a2
      simp
      cases h3 : nar B (v i) (R.add a1 a2)
      · simp [h3, ← nar_comm]
      · rename_i B₂
        simp [h3, ← nar_comm]
        cases h4 : side R (ivOf B (r i)) d (R.sub (ivOf B₂ (v i)) a2)
        · simp [h4, ← side_comm]
        · rename_i rp
          simp [h4, ← side_comm]
          cases h5 : nar B₂ (r (i + 1)) rp
          · simp [h5, ← nar_comm]
          · rename_i B₃
            simp [h5, ← nar_comm]
            cases h6 : side R (ivOf B (r i)) d (R.sub (ivOf B₃ (v i)) a1)
            · simp [h6, ← side_comm]
            · rename_i rm
              simp [h6, ← side_comm, ← nar_comm]

theorem wheelStep_comm (r : Fin 6 → ι) :
    (wheelStep R v r jd B).map embB = wheelStepG (lift R) v r jd (embB B) := by
  unfold wheelStep wheelStepG
  simp only [ivOf_embB]
  rw [bind_map_comm _ _ _ embB embB, foldlM_map_comm embB]
  · intro B' i
    rw [nar_comm, lift_scale_three]
    rfl
  · intro B₁
    simp only [ivOf_embB]
    rw [bind_map_comm _ _ _ (List.map embI) embB, mapM_map_comm embI]
    · intro i; exact triAngle_comm R _ _ _
    · intro th
      rw [ofReal_zero, pt_embF, ← foldl_add_comm, lift_twoPiLo, lift_twoPiHi, ofReal_ratCast,
        ofReal_ratCast, embI_hi, embI_lo, embF_lt_iff, embF_lt_iff]
      split_ifs
      · rfl
      · exact foldlM_map_comm embB _ _ (fun B' i => wheelTurn_comm R B' v r _ i) _ _

end Steps

end Tammes15.Contractors.Q
