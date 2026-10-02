import Tammes15.Hyps.Computations

/-!
# D1 for `F = {frameC1, frameC3}`: the objects of the certificate

The objects of the certificate of D1 (paper, proof of Lemma 4.2); the data of the
kernel checker are in Kappa/C1.lean and Kappa/C3.lean.

The certificate, found by linear programming in SageMath. For a frame `p`
with contacts `e = (i, j)`, `s_e = w - Lmap p t e`, and the LP multipliers `λ_e ≥ 0`, `μ_ef ≥ 0`:
`F(w, t) = Rc² w² - ∑ ‖t i‖² - ∑ λ_e w s_e - ∑ μ_ef s_e s_f` satisfies, at the frame rounded to
`2^-100` (`q`), `F = ∑_k g_k(t) m_k(w, t) + zᵀ N z` with `z = (w, t) ∈ ℝ⁴⁶`, the 18 TPerp forms `g_k`,
rational linear forms `m_k`, and a matrix `N` with `(∑ |N_ab + N_ba|) / 2 ≤ B / 2^265`. The kernel
computes `N` from integer data (`checkV`, `checkW`, `checkN` of Tammes15.Kappa.C1 and C3). With
`w = κ₀ |t|` and every `Lmap p t e < κ₀ |t|` all `s_e > 0`, so `|t|² ≤ (Rc² + η) κ₀² |t|² + η |t|²`, and
`(Rc² + η) κ₀² + η < 1` forces `t = 0`: that is `KappaBound p S κ₀` (`kappa_of_cert`).
-/

open scoped RealInnerProductSpace

namespace Tammes15.Kappa


/-! ## 1. Coordinates and quadratic forms -/

/-- The index `1 + 3 i + m` of `Fin 46`: the coordinate `m` of the point `i` in `z = (w, t)`. -/
def ix (i : Fin 15) (m : Fin 3) : Fin 46 := ⟨1 + 3 * i.val + m.val, by omega⟩

/-- `z = (w, t)`: `z 0 = w`, `z (1 + 3k + m) = t k m`. -/
noncomputable def zv (w : ℝ) (t : Fin 15 → E3) (a : Fin 46) : ℝ :=
  if a.val = 0 then w else
    t ⟨(a.val - 1) / 3, by have := a.isLt; omega⟩ ⟨(a.val - 1) % 3, by omega⟩

/-- The quadratic form of a matrix. -/
def quad (N : Fin 46 → Fin 46 → ℝ) (z : Fin 46 → ℝ) : ℝ := ∑ a, ∑ b, N a b * z a * z b

/-! ## 2. The certificate form, generic in the frame -/

/-- `v_e`, with `∑ a, vr p e a * zv w t a = w - Lmap p t e`. -/
noncomputable def vr (p : Fin 15 → E3) (e : Fin 15 × Fin 15) (a : Fin 46) : ℝ :=
  if a.val = 0 then 1 else
    (if (a.val - 1) / 3 = (e.2 : ℕ) then -(p e.1 ⟨(a.val - 1) % 3, by omega⟩) else 0) +
      (if (a.val - 1) / 3 = (e.1 : ℕ) then -(p e.2 ⟨(a.val - 1) % 3, by omega⟩) else 0)

/-- The 18 TPerp forms: `⟪p k, t k⟫` for `k < 15`, `(∑ i, cross (p i) (t i)) c` for `k = 15 + c`. -/
noncomputable def gr (p : Fin 15 → E3) (k : Fin 18) (a : Fin 46) : ℝ :=
  if a.val = 0 then 0 else
    if k.val < 15 then
      (if (a.val - 1) / 3 = k.val then p ⟨k.val % 15, by omega⟩ ⟨(a.val - 1) % 3, by omega⟩ else 0)
    else
      if (a.val - 1) % 3 = (k.val - 15 + 2) % 3 then
        p ⟨(a.val - 1) / 3, by have := a.isLt; omega⟩ ⟨(k.val - 15 + 1) % 3, by omega⟩
      else if (a.val - 1) % 3 = (k.val - 15 + 1) % 3 then
        -(p ⟨(a.val - 1) / 3, by have := a.isLt; omega⟩ ⟨(k.val - 15 + 2) % 3, by omega⟩)
      else 0

/-- `F(w, t) = Rc² w² - |t|² - ∑ λ_e w s_e - ∑ μ_ef s_e s_f`, `s_e = w - Lmap p t (Sl e)`. -/
noncomputable def Fform (p : Fin 15 → E3) (Sl : Fin 30 → Fin 15 × Fin 15) (lam : Fin 30 → ℝ)
    (mu : Fin 30 → Fin 30 → ℝ) (Rc2 w : ℝ) (t : Fin 15 → E3) : ℝ :=
  Rc2 * w ^ 2 - ∑ i, ‖t i‖ ^ 2 - ∑ e, lam e * w * (w - Lmap p t (Sl e)) -
    ∑ e, ∑ f, mu e f * (w - Lmap p t (Sl e)) * (w - Lmap p t (Sl f))

/-- The matrix of `F - ∑_k g_k m_k`. -/
noncomputable def Nr (p : Fin 15 → E3) (Sl : Fin 30 → Fin 15 × Fin 15) (lam : Fin 30 → ℝ)
    (mu : Fin 30 → Fin 30 → ℝ) (Rc2 : ℝ) (mk : Fin 18 → Fin 46 → ℝ) (a b : Fin 46) : ℝ :=
  (if a.val = 0 ∧ b.val = 0 then Rc2 else if a = b then -1 else 0) -
    (if a.val = 0 then ∑ e, lam e * vr p (Sl e) b else 0) -
    ∑ e, ∑ f, mu e f * vr p (Sl e) a * vr p (Sl f) b - ∑ k, gr p k a * mk k b

/-! ## 3. Perturbation from the rounded frame `q` to the frame `p` -/

/-- The constant of `Fform_perturb`: `|Δ s_e| ≤ 4δ|t|` and `|s_e| ≤ |w| + 2|t|` for any pair `e` (also `i = j`). -/
def Cpert (δ L M : ℝ) : ℝ := 2 * δ * L + 4 * δ * (5 + 4 * δ) * M


def dI (o n : Nat) : Int := (n : Int) - (o : Int)
def dL (o : Nat) (l : List Nat) : List Int := l.map (dI o)
def dLL (o : Nat) (l : List (List Nat)) : List (List Int) := l.map (dL o)
def nL (l : List Nat) : List Int := l.map Int.ofNat
def oP : Nat := 2 ^ 101
def oW : Nat := 2 ^ 180
def oM : Nat := 2 ^ 80

def getP (P : List (List Int)) (k m : Nat) : Int := (P.getD k []).getD m 0

/-- `2^100 · vr`, from the rounded frame `P` (scale `2^100`). -/
def vEntry (P : List (List Int)) (e : Nat × Nat) (a : Nat) : Int :=
  if a = 0 then 2 ^ 100 else
    (if (a - 1) / 3 = e.2 then -getP P e.1 ((a - 1) % 3) else 0) +
    (if (a - 1) / 3 = e.1 then -getP P e.2 ((a - 1) % 3) else 0)

def mkV (P : List (List Int)) (S : List (Nat × Nat)) : List (List Int) :=
  S.map fun e => (List.range 46).map fun a => vEntry P e a

/-- `2^100 · gr`. -/
def gEntry (P : List (List Int)) (k a : Nat) : Int :=
  if a = 0 then 0 else
    let kk := (a - 1) / 3
    let m := (a - 1) % 3
    if k < 15 then (if kk = k then getP P k m else 0) else
      let c := k - 15
      if m = (c + 2) % 3 then getP P kk ((c + 1) % 3) else
        if m = (c + 1) % 3 then -getP P kk ((c + 2) % 3) else 0

def mkGt (P : List (List Int)) : List (List Int) :=
  (List.range 46).map fun a => (List.range 18).map fun k => gEntry P k a

def smulAdd (c : Int) (v acc : List Int) : List Int := List.zipWith (fun x y => c * x + y) v acc

def lin : List Int → List (List Int) → List Int → List Int
  | c :: cs, r :: rs, acc => lin cs rs (smulAdd c r acc)
  | _, _, acc => acc

def zeros (n : Nat) : List Int := List.replicate n 0

def mkW (Mu V : List (List Int)) : List (List Int) := Mu.map fun row => lin row V (zeros 46)

/-- Row `a` of `2^264 · Nr`. -/
def nRow (RC : Int) (Lam : List Int) (V W Mk : List (List Int)) (a : Nat) (vt gt : List Int) :
    List Int :=
  let base := (List.range 46).map fun b =>
    if a = 0 ∧ b = 0 then RC * 2 ^ 200 else if a = b then -(2 ^ 264) else 0
  let r0 := if a = 0 then lin (Lam.map fun l => -(l * 2 ^ 100)) V base else base
  let r1 := lin (vt.map fun x => -x) W r0
  lin (gt.map fun x => -(x * 2 ^ 100)) Mk r1

def absSum (rows : List (List Int)) : Nat :=
  rows.foldl (fun s r => r.foldl (fun s x => s + x.natAbs) s) 0

def nMat (RC : Int) (Lam : List Int) (V W Mk Vt Gt : List (List Int)) : List (List Int) :=
  ((List.range 46).zip (Vt.zip Gt)).map fun (a, vt, gt) => nRow RC Lam V W Mk a vt gt

def tr (rows : List (List Int)) : List (List Int) :=
  rows.foldr (fun r acc => List.zipWith List.cons r acc) (List.replicate 46 [])

def symm (N : List (List Int)) : List (List Int) := List.zipWith (List.zipWith (· + ·)) N (tr N)

/-- The shapes the specification of the checker needs. -/
def Shape (P : List (List Int)) (S : List (Nat × Nat)) (Lam : List Nat) (Mu : List (List Nat))
    (Mk : List (List Int)) : Prop :=
  P.length = 15 ∧ (∀ r ∈ P, r.length = 3) ∧ S.length = 30 ∧ (∀ e ∈ S, e.1 < 15 ∧ e.2 < 15) ∧
    Lam.length = 30 ∧ Mu.length = 30 ∧ (∀ r ∈ Mu, r.length = 30) ∧ Mk.length = 18 ∧
    (∀ r ∈ Mk, r.length = 46)

/-- The rounded frame as points. -/
noncomputable def qOf (P : List (List Int)) (i : Fin 15) : E3 :=
  !₂[((P.getD i []).getD 0 0 : ℝ) / 2 ^ 100, ((P.getD i []).getD 1 0 : ℝ) / 2 ^ 100,
    ((P.getD i []).getD 2 0 : ℝ) / 2 ^ 100]

/-- The contacts as a function. -/
def SlOf (S : List (Nat × Nat)) (e : Fin 30) : Fin 15 × Fin 15 :=
  (⟨(S.getD e (0, 0)).1 % 15, Nat.mod_lt _ (by norm_num)⟩,
    ⟨(S.getD e (0, 0)).2 % 15, Nat.mod_lt _ (by norm_num)⟩)

noncomputable def lamOf (Lam : List Nat) (e : Fin 30) : ℝ := (Lam.getD e 0 : ℝ) / 2 ^ 64

noncomputable def muOf (Mu : List (List Nat)) (e f : Fin 30) : ℝ :=
  ((Mu.getD e []).getD f 0 : ℝ) / 2 ^ 64

noncomputable def mkOf (Mk : List (List Int)) (k : Fin 18) (b : Fin 46) : ℝ :=
  ((Mk.getD k []).getD b 0 : ℝ) / 2 ^ 64


end Tammes15.Kappa
