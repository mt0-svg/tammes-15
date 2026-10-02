# Run from the repository root: OUT=DIR sage code/lean-data/d4_cut.sage (DIR receives the two generated files)
# D4 (AttainedHyp) for F = {C1, C3}: the frame coordinates in Q(u, b) and the lemmas of Tammes15/Attained/.
# Writes $OUT/D4Cut.lean (every lemma stated, proofs `sorry`) and
# $OUT/D4CutProofs.lean (the same generated lemmas, the identities proved by
# `linear_combination` with Groebner cofactors, the separations by `dyadic_interval`).
# Checks first, against data/bk15_exact.txt: the 18 points evaluated at (u, b)
# agree with the recorded coordinates, and the pairs at inner product exactly u are the recorded
# contact lists of C1 and C3.
import ast, os
R.<b,u> = PolynomialRing(QQ, order="lex")
P = 13*u^5 - u^4 + 6*u^3 + 2*u^2 - 3*u - 1
Q4 = 9*(4*u^2-u-1)*(3*u+1)^2*b^4 + 2*u*(62*u^4-155*u^3-37*u^2+51*u+15)*b^2 + u^2*(4*u^2-u-1)*(5*u-1)^2
I = R.ideal([P, Q4]); G = I.groebner_basis()
def nf(f): return I.reduce(f)
def inv(f):
    co = R(1).lift(R.ideal([f] + list(G))); return nf(co[0])
c = nf(b*(27*b^2*u^2+18*b^2*u+29*u^3+3*b^2-18*u^2-11*u) * inv((3*u+1)*(9*b^2*u+3*b^2-5*u^2+u)))
a = nf((u - b*c) * inv(b + c))
iu1 = inv(u + 1); iu2 = nf(iu1^2)
dd = nf(((2*a-b+2*c)*u-b)*iu1); ee = nf(((2*a+2*b-c)*u-c)*iu1); ff = nf(((-a+2*b+2*c)*u-a)*iu1)
r = nf(((6*a-2*c+3*b)*u^2+2*(a-b-c)*u-b)*iu2)
s = nf(((6*b-2*a+3*c)*u^2+2*(b-c-a)*u-c)*iu2)
t = nf(((6*c-2*b+3*a)*u^2+2*(c-a-b)*u-a)*iu2)
base = [("aN", a), ("bN", b), ("cN", c), ("dN", dd), ("eN", ee), ("fN", ff), ("rN", r), ("sN", s), ("tN", t)]
DD = lcm([q.denominator() for _, f in base for q in f.coefficients()])
print("common denominator DD =", DD)
# the 18 points, in the order of bk15_exact.txt (V1 V2 V3 V12 V23 V31 P I A Q J B W12 W23 W31 W1 W2 W3)
Fp = [[a,b,c],[c,a,b],[b,c,a],[dd,ee,ff],[ff,dd,ee],[ee,ff,dd],[r,s,t],[t,r,s],[s,t,r],
      [-t,-s,-r],[-r,-t,-s],[-s,-r,-t],[-ff,-ee,-dd],[-ee,-dd,-ff],[-dd,-ff,-ee],[-c,-b,-a],[-b,-a,-c],[-a,-c,-b]]
names = ["V1","V2","V3","V12","V23","V31","P","I","A","Q","J","B","W12","W23","W31","W1","W2","W3"]
RF = RealField(200)
x = polygen(RF)
uv = [z for z in (13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1).roots(multiplicities=False) if 0.5 < z < 0.7][0]
bv = [z for z in Q4.subs(u=uv).univariate_polynomial().change_ring(RF).roots(multiplicities=False) if abs(z - 0.1714903098) < 1e-6][0]
def ev(f): return RF(R(f).subs(b=bv, u=uv))
lines = open("data/bk15_exact.txt").read().splitlines()
rec = {}; keep = {}; cont = {}
for ln in lines:
    w = ln.split()
    if len(w) == 7 and w[0] in names: rec[w[0]] = [RF(w[1]), RF(w[3]), RF(w[5])]
    w2 = ln.split(None, 2)
    if len(w2) == 3 and w2[1] == "keep": keep[w2[0]] = ast.literal_eval(w2[2])
    if len(w2) == 3 and w2[1] == "contacts": cont[w2[0]] = ast.literal_eval(w2[2])
dev = max(abs(ev(Fp[k][m]) - rec[names[k]][m]) for k in range(18) for m in range(3))
print("max deviation of the 18 points from bk15_exact.txt: %.3e" % dev)
assert dev < 1e-25
# contact pairs from exact normal forms, compared with the recorded lists
def ip(k1, k2): return sum(Fp[k1][m]*Fp[k2][m] for m in range(3))
CP = set(); NP = set()
for nm in ["C1", "C3"]:
    kp = [k - 1 for k in keep[nm]]
    exact = sorted((i, j) for i in range(15) for j in range(i+1, 15) if nf(ip(kp[i], kp[j])) == u)
    assert exact == sorted(cont[nm]), nm
    for i in range(15):
        for j in range(i+1, 15):
            (CP if (i, j) in exact else NP).add((kp[i], kp[j]))
    print(nm, "keep", keep[nm], "contacts", len(exact), "= recorded list")
assert not (CP & NP)
print("point pairs: contacts", len(CP), "non-contacts", len(NP))
gaps = sorted((ev(ip(k1, k2)) - uv, (k1, k2)) for (k1, k2) in NP)
print("largest non-contact inner product minus u: %.10f at point pair %s" % (gaps[-1][0], gaps[-1][1]))
# decimal enclosures: u of width 1e-40, b of width 1e-30
den = 10**30; denu = 10**40   # u much tighter than b, so that Q4(bl, u) and Q4(bh, u) keep their signs over the u enclosure
ul = floor(uv*denu)/denu; uh = ul + 1/denu; bl = floor(bv*den)/den; bh = bl + 1/den
def dec(q, n=41):
    sq = str(floor(q * 10**n)); return "0." + sq.rjust(n, "0")
Pq = lambda z: 13*z^5 - z^4 + 6*z^3 + 2*z^2 - 3*z - 1
print("sign of the quintic at ul, uh:", sign(Pq(ul)), sign(Pq(uh)))
assert Pq(ul) < 0 < Pq(uh)
# Q4(b, u) at b = bl, bh for u in [ul, uh]: sign by 200-bit interval evaluation
RIF200 = RealIntervalField(200)
Ui = RIF200(ul, uh)
q4l = Q4.subs(b=bl).univariate_polynomial()(Ui) if Q4.subs(b=bl).degree(u) > 0 else RIF200(Q4.subs(b=bl))
q4h = Q4.subs(b=bh).univariate_polynomial()(Ui)
print("Q4(bl, [ul, uh]) = %.6e .. %.6e   Q4(bh, [ul, uh]) = %.6e .. %.6e" % (q4l.lower(), q4l.upper(), q4h.lower(), q4h.upper()))
sgl = 1 if q4l > 0 else -1; sgh = 1 if q4h > 0 else -1
assert sgl * sgh < 0
# Lean text
def prod_form(f, scale):
    terms = []
    for (eb, eu), q in sorted((f*scale).dict().items(), reverse=True):
        assert q.denominator() == 1
        terms.append("(%s : ℝ)%s" % (q, "".join(" * " + v for v in ["b"]*eb + ["u"]*eu)))
    return " + ".join(terms) if terms else "0"
def pow_form(f):
    terms = []
    for (eb, eu), q in sorted(f.dict().items(), reverse=True):
        mon = (["b ^ %d" % eb] if eb else []) + (["u ^ %d" % eu] if eu else [])
        terms.append("(%s : ℝ)%s" % (q, "".join(" * " + m for m in mon)))
    return " + ".join(terms)
bname = {str(f): nm for nm, f in base}
def coordN(z):
    if str(z) in bname: return "%s b u" % bname[str(z)]
    return "(-(%s b u))" % bname[str(-z)]
def expr_ip(k1, k2): return " + ".join("%s * %s" % (coordN(Fp[k1][m]), coordN(Fp[k2][m])) for m in range(3))
defs_names = ", ".join(nm for nm, _ in base)
def cof(f):
    co = f.lift(R.ideal([P, Q4])); assert co[0]*P + co[1]*Q4 == f; return co
hdr = r"""import Tammes15.Hyps.Computations

/-!
# D4 `AttainedHyp` for `F = {frameC1, frameC3}`, cut into self-contained lemmas

Generated by code/lean-data/d4_cut.sage from data/bk15_exact.txt (the script
checks that the 18 points below evaluate to the recorded coordinates and that the pairs at inner
product exactly `u` are the recorded contact lists). %s

Data. `u` is the root of `quintic` in `[ul, uh]` and `b` the root of `Q4 b u` in `[bl, bh]` (decimal
enclosures of width 1e-40 and 1e-30). The frame coordinates lie in `ℚ(u, b)`, of degree 20; each one is
`xN b u / 225008` with `xN` a polynomial with integer coefficients written with products (no `^`, so
that `dyadic_interval` accepts it). The 18 points `pt b u k` are signed cyclic permutations of the
triples `(aN, bN, cN)`, `(dN, eN, fN)`, `(rN, sN, tN)`; `frameC1` and `frameC3` keep 15 of them.

How the lemmas compose.
1. `u_root`, `b_root` (IVT from the sign lemmas `quintic_lo`, `quintic_hi`, `Q4_lo`, `Q4_hi`) give
   `uR`, `bR` with `quintic uR = 0` and `Q4 bR uR = 0`.
2. `nm_k` (18 lemmas): the squared norm numerator of point `k` is `225008²` whenever
   `quintic u = 0` and `Q4 b u = 0`; with `norm_pt` it gives `‖pt bR uR k‖ = 1`.
3. `ct_k1_k2` (one per contact point pair): the inner product numerator is `225008² · u`; with
   `inner_pt` it gives `⟪pt bR uR k1, pt bR uR k2⟫ = uR`.
4. `sp_k1_k2` (one per non-contact point pair): for `u, b` in the enclosures the inner product
   numerator is at most `225008² · u`; with `inner_pt` it gives `⟪pt bR uR k1, pt bR uR k2⟫ ≤ uR`.
5. `frameC1_unit`, `frameC1_contact`, `frameC1_sep` (and C3) assemble 2 to 4 over the 15 kept
   indices (`fin_cases`; `keepC1` and `keepC3` are increasing, the point pairs are ordered);
   `attained : AttainedHyp {frameC1, frameC3}` follows with `1/2 < uR < 7/10` from `uR_mem`.

D1 for the same frames is stated at the end (`kappa_C1`, `kappa_C3`, `kappaHyp`); it is not part of
this cut. By `LocalFires` (isometries and bijections) the two frames stand for all eight.
-/

set_option maxHeartbeats 0

open scoped RealInnerProductSpace

namespace Tammes15.D4Cut

"""
def lean_defs():
    out = ""
    for nm, f in base:
        out += "/-- Numerator of a frame coordinate: the coordinate is `%s b u / 225008`. -/\ndef %s (b %s : ℝ) : ℝ :=\n  %s\n\n" % (nm, nm, "_u" if nm == "bN" else "u", prod_form(f, DD))
    out += "/-- The quartic whose root `b` generates `ℚ(u, b)` over `ℚ(u)`, written with products. -/\ndef Q4 (b u : ℝ) : ℝ :=\n  %s\n\n" % prod_form(Q4, 1)
    rows = []
    for k in range(18):
        rows.append("![%s]" % ", ".join(coordN(Fp[k][m]) for m in range(3)))
    out += "/-- Numerators of the 18 frame points (order of bk15_exact.txt: V1 V2 V3 V12 V23 V31 P I A Q J B\nW12 W23 W31 W1 W2 W3). -/\ndef ptN (b u : ℝ) : Fin 18 → Fin 3 → ℝ :=\n  ![%s]\n\n" % ",\n    ".join(rows)
    out += "/-- The 18 frame points. -/\nnoncomputable def pt (b u : ℝ) (k : Fin 18) : E3 :=\n  !₂[ptN b u k 0 / 225008, ptN b u k 1 / 225008, ptN b u k 2 / 225008]\n\n"
    out += "/-- Enclosure of `u`. -/\ndef ul : ℝ := %s\n/-- Enclosure of `u`. -/\ndef uh : ℝ := %s\n/-- Enclosure of `b`. -/\ndef bl : ℝ := %s\n/-- Enclosure of `b`. -/\ndef bh : ℝ := %s\n\n" % (dec(ul), dec(uh), dec(bl), dec(bh))
    return out
def stmt_nm(k):
    e = " + ".join("%s * %s" % (coordN(Fp[k][m]), coordN(Fp[k][m])) for m in range(3))
    return "theorem nm_%d (b u : ℝ) (hP : quintic u = 0) (hQ : Q4 b u = 0) :\n    %s = (225008 * 225008 : ℝ)" % (k, e), (sum(Fp[k][m]^2 for m in range(3)) - 1)
def stmt_ct(k1, k2):
    return "theorem ct_%d_%d (b u : ℝ) (hP : quintic u = 0) (hQ : Q4 b u = 0) :\n    %s = (225008 * 225008 : ℝ) * u" % (k1, k2, expr_ip(k1, k2)), (ip(k1, k2) - u)
def stmt_sp(k1, k2):
    return "theorem sp_%d_%d (b u : ℝ) (hu : u ∈ Set.Icc ul uh) (hb : b ∈ Set.Icc bl bh) :\n    %s ≤ (225008 * 225008 : ℝ) * u" % (k1, k2, expr_ip(k1, k2))
def proof_ident(f):
    co = cof(f * DD^2)
    return " := by\n  simp only [%s, Q4, quintic] at *\n  linear_combination (%s) * hP + (%s) * hQ\n\n" % (defs_names, pow_form(co[0]) or "0", pow_form(co[1]) or "0")
proof_sp = " := by\n  simp only [ul, uh, bl, bh] at hu hb\n  simp only [%s]\n  dyadic_interval [prec := 60]\n\n" % defs_names
sorry_ = " := by\n  sorry\n\n"
kp1 = [k - 1 for k in keep["C1"]]; kp3 = [k - 1 for k in keep["C3"]]
struct = r"""/-! ## Roots -/

theorem quintic_lo : quintic ul < 0 := by
  sorry

theorem quintic_hi : 0 < quintic uh := by
  sorry

theorem Q4_lo (u : ℝ) (hu : u ∈ Set.Icc ul uh) : %s := by
  sorry

theorem Q4_hi (u : ℝ) (hu : u ∈ Set.Icc ul uh) : %s := by
  sorry

theorem u_root : ∃ u ∈ Set.Icc ul uh, quintic u = 0 := by
  sorry

theorem b_root (u : ℝ) (hu : u ∈ Set.Icc ul uh) : ∃ b ∈ Set.Icc bl bh, Q4 b u = 0 := by
  sorry

/-- The contact cosine `u`, root of the quintic in `[ul, uh]`. -/
noncomputable def uR : ℝ := u_root.choose

theorem uR_mem : uR ∈ Set.Icc ul uh := u_root.choose_spec.1

theorem uR_root : quintic uR = 0 := u_root.choose_spec.2

/-- The generator `b` of `ℚ(u, b)`, root of `Q4 · uR` in `[bl, bh]`. -/
noncomputable def bR : ℝ := (b_root uR uR_mem).choose

theorem bR_mem : bR ∈ Set.Icc bl bh := (b_root uR uR_mem).choose_spec.1

theorem bR_root : Q4 bR uR = 0 := (b_root uR uR_mem).choose_spec.2

theorem uR_bounds : 1 / 2 < uR ∧ uR < 7 / 10 := by
  sorry

/-! ## Inner products of the points -/

theorem inner_pt (b u : ℝ) (k1 k2 : Fin 18) :
    ⟪pt b u k1, pt b u k2⟫ = (ptN b u k1 0 * ptN b u k2 0 + ptN b u k1 1 * ptN b u k2 1 +
      ptN b u k1 2 * ptN b u k2 2) / (225008 * 225008) := by
  sorry

theorem norm_pt (b u : ℝ) (k : Fin 18)
    (h : ptN b u k 0 * ptN b u k 0 + ptN b u k 1 * ptN b u k 1 + ptN b u k 2 * ptN b u k 2 =
      225008 * 225008) : ‖pt b u k‖ = 1 := by
  sorry

""" % (("Q4 bl u < 0" if sgl < 0 else "0 < Q4 bl u"), ("0 < Q4 bh u" if sgh > 0 else "Q4 bh u < 0"))
def frame_block(nm, kp):
    S = ", ".join("(%d, %d)" % ij for ij in cont[nm])
    return r"""/-! ## Frame %(nm)s -/

/-- The 15 points of %(nm)s among the 18 (bk15_exact.txt, `%(nm)s keep`, minus one). -/
def keep%(nm)s : Fin 15 → Fin 18 := ![%(kp)s]

/-- The frame %(nm)s with its 30 contacts (bk15_exact.txt, `%(nm)s contacts`). -/
noncomputable def frame%(nm)s : Frame where
  p i := pt bR uR (keep%(nm)s i)
  S := {%(S)s}

theorem frame%(nm)s_unit : ∀ i, ‖frame%(nm)s.p i‖ = 1 := by
  sorry

theorem frame%(nm)s_contact : ∀ ij ∈ frame%(nm)s.S,
    ij.1 ≠ ij.2 ∧ ⟪frame%(nm)s.p ij.1, frame%(nm)s.p ij.2⟫ = uR := by
  sorry

theorem frame%(nm)s_sep : ∀ i j, i ≠ j → ⟪frame%(nm)s.p i, frame%(nm)s.p j⟫ ≤ uR := by
  sorry

""" % {"nm": nm, "kp": ", ".join(str(k) for k in kp), "S": S}
tail = r"""/-! ## Assembly -/

theorem attained : AttainedHyp {frameC1, frameC3} := by
  sorry

/-! ## D1 for the same frames (not part of this cut) -/

theorem kappa_C1 : KappaBound frameC1.p frameC1.S kappa0 := by
  sorry

theorem kappa_C3 : KappaBound frameC3.p frameC3.S kappa0 := by
  sorry

theorem kappaHyp : KappaHyp {frameC1, frameC3} := by
  sorry

end Tammes15.D4Cut
"""
CPs = sorted(CP); NPs = sorted(NP)
note_cut = "Here every proof is `sorry`; D4CutProofs.lean has the generated proofs of the lemmas `nm_k`, `ct_k1_k2`, `sp_k1_k2`."
note_prf = "Here the lemmas `nm_k`, `ct_k1_k2`, `sp_k1_k2` carry their generated proofs; the rest is in D4Cut.lean."
for fname, mode in [(os.environ["OUT"] + "/D4Cut.lean", "cut"), (os.environ["OUT"] + "/D4CutProofs.lean", "proofs")]:
    L = open(fname, "w")
    L.write(hdr % (note_cut if mode == "cut" else note_prf))
    if mode == "proofs": L.write("set_option linter.unusedSimpArgs false\n\n")
    L.write(lean_defs())
    L.write("/-! ## Unit norms -/\n\n")
    for k in range(18):
        st, f = stmt_nm(k); L.write(st + (sorry_ if mode == "cut" else proof_ident(f)))
    L.write("/-! ## Contacts -/\n\n")
    for (k1, k2) in CPs:
        st, f = stmt_ct(k1, k2); L.write(st + (sorry_ if mode == "cut" else proof_ident(f)))
    L.write("/-! ## Separations -/\n\n")
    for (k1, k2) in NPs:
        L.write(stmt_sp(k1, k2) + (sorry_ if mode == "cut" else proof_sp))
    if mode == "cut":
        L.write(struct); L.write(frame_block("C1", kp1)); L.write(frame_block("C3", kp3)); L.write(tail)
    else:
        # the four sign lemmas of the roots, proved here as a check of the enclosures
        L.write("/-! ## Signs at the ends of the enclosures -/\n\n")
        L.write("theorem quintic_lo : quintic ul < 0 := by\n  norm_num [quintic, ul]\n\n")
        L.write("theorem quintic_hi : 0 < quintic uh := by\n  norm_num [quintic, uh]\n\n")
        L.write("theorem Q4_lo (u : ℝ) (hu : u ∈ Set.Icc ul uh) : %s := by\n  simp only [ul, uh] at hu\n  simp only [Q4, bl]\n  dyadic_interval [prec := 256]\n\n" % ("Q4 bl u < 0" if sgl < 0 else "0 < Q4 bl u"))
        L.write("theorem Q4_hi (u : ℝ) (hu : u ∈ Set.Icc ul uh) : %s := by\n  simp only [ul, uh] at hu\n  simp only [Q4, bh]\n  dyadic_interval [prec := 256]\n\n" % ("0 < Q4 bh u" if sgh > 0 else "Q4 bh u < 0"))
        L.write("end Tammes15.D4Cut\n")
    L.close()
print("lemmas: 18 norms, %d contacts, %d separations, plus 21 structural" % (len(CPs), len(NPs)))
