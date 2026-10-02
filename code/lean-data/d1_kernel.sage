# Run from the repository root: OUT=DIR sage code/lean-data/d1_kernel.sage (reads the certificates code/lean-data/d1_lp_cert_C1.txt, C3.txt of d1_lp.sage)
# D1: the integer data of Tammes15/Kappa/C1.lean and C3.lean from the LP certificate of d1_lp.sage, in the
# coordinates of the Lean statement. Writes $OUT/D1Kernel_<frame>.lean (core Lean,
# no Mathlib), whose three `decide +kernel` theorems check, from integer data:
#   V  = the 30 vectors v_e with v_e . z = w - Lmap p t e (from the rounded frame P and the contacts),
#   Gt = the 18 TPerp forms (15 inner products <p_k, t_k>, 3 components of sum_k p_k x t_k),
#   W  = Mu V,
#   absSum (N + N^T) <= B, N the integer matrix of
#     F(z) - sum_k g_k(z) m_k(z),  F(w, t) = Rc^2 w^2 - |t|^2 - sum_e lam_e w s_e - sum_{e<=f} mu_ef s_e s_f,
#     s_e = w - Lmap p t e, at the frame rounded to 2^-100 and the multipliers rounded to 2^-64,
#   all scaled by 2^264, so that every entry is an integer.
# The same integers are computed here exactly; B is the absolute sum of N + N^T, eta = B / 2^265
# bounds |z^T N z| / |z|^2.
import ast, os
lines = open("data/bk15_exact.txt").read().splitlines()
RF = RealField(200)
names = ["V1","V2","V3","V12","V23","V31","P","I","A","Q","J","B","W12","W23","W31","W1","W2","W3"]
pts = {}; keep = {}; cont = {}
for ln in lines:
    w = ln.split()
    if len(w) == 7 and w[0] in names: pts[w[0]] = [RF(w[1]), RF(w[3]), RF(w[5])]
    w2 = ln.split(None, 2)
    if len(w2) == 3 and w2[1] == "keep": keep[w2[0]] = ast.literal_eval(w2[2])
    if len(w2) == 3 and w2[1] == "contacts": cont[w2[0]] = ast.literal_eval(w2[2])
OFFS = {"P": 2^101, "V": 2^101, "W": 2^180, "M": 2^80}
kappa0 = QQ(6498) / 10^6
def enc(x, t):
    x = ZZ(x); assert abs(x) < OFFS[t]; return str(x + OFFS[t])
def lst(v): return "[" + ", ".join(v) + "]"
for nm in ["C1", "C3"]:
    X = [pts[names[k-1]] for k in keep[nm]]; S = cont[nm]
    P = [[ZZ(round(X[k][m] * 2^100)) for m in range(3)] for k in range(15)]
    cert = [RF(v) for ln in open("code/lean-data/d1_lp_cert_%s.txt" % nm).read().splitlines() if not ln.startswith("#") for v in ln.split()]
    # Lean units: t unscaled, so multiply the x-unit certificate by 150^2
    R2 = cert[0] * 22500; lam = [max(v, 0) * 22500 for v in cert[1:31]]; mu = [max(v, 0) * 22500 for v in cert[31:]]
    pairs = [(i, j) for i in range(30) for j in range(i, 30)]
    RC = ZZ(ceil(R2 * 2^64))
    Lam = [ZZ(round(v * 2^64)) for v in lam]
    Mu = [[0]*30 for _ in range(30)]
    for k, (e, f) in enumerate(pairs): Mu[e][f] = ZZ(round(mu[k] * 2^64))
    # V (30 x 46, scale 2^100), G (18 x 46, scale 2^100), exactly as the Lean functions compute them
    def vEntry(e, a):
        if a == 0: return 2^100
        k, m = (a - 1) // 3, (a - 1) % 3
        i, j = S[e]
        return (-P[i][m] if k == j else 0) + (-P[j][m] if k == i else 0)
    V = [[vEntry(e, a) for a in range(46)] for e in range(30)]
    def gEntry(k, a):
        if a == 0: return 0
        kk, m = (a - 1) // 3, (a - 1) % 3
        if k < 15: return P[k][m] if kk == k else 0
        c = k - 15   # (p x t)_c = p_{c+1} t_{c+2} - p_{c+2} t_{c+1}
        if m == (c + 2) % 3: return P[kk][(c + 1) % 3]
        if m == (c + 1) % 3: return -P[kk][(c + 2) % 3]
        return 0
    G = [[gEntry(k, a) for a in range(46)] for k in range(18)]
    W = [[sum(Mu[e][f] * V[f][a] for f in range(30)) for a in range(46)] for e in range(30)]
    # A = matrix of F at the rounded data, scale 2^264 (non-symmetric form: z^T A z = F(z))
    A = matrix(ZZ, 46, 46)
    A[0, 0] = RC * 2^200
    for a in range(1, 46): A[a, a] = -2^264
    for e in range(30):
        for b in range(46): A[0, b] -= Lam[e] * 2^100 * V[e][b]
    Vm = matrix(ZZ, V); Wm = matrix(ZZ, W)
    A -= Vm.transpose() * Wm
    # multipliers m_k from the projection onto W = ker G (200-bit), rounded to 2^-64
    Ar = A.change_ring(RF) / RF(2)^264; As = (Ar + Ar.transpose()) / 2
    Gr = matrix(RF, G) / RF(2)^100
    Cp = Gr.transpose() * (Gr * Gr.transpose()).inverse()
    Pi = identity_matrix(RF, 46) - Cp * Gr
    Mr = 2 * Cp.transpose() * As * Pi + Cp.transpose() * As * Cp * Gr   # F(z) = (Gz)^T Mr z + small
    Mk = [[ZZ(round(Mr[k, b] * 2^64)) for b in range(46)] for k in range(18)]
    N = A - matrix(ZZ, G).transpose() * matrix(ZZ, Mk) * 2^100
    Ns = N + N.transpose()   # only the symmetric part of N matters: z^T N z = z^T (N + N^T) z / 2
    B = sum(abs(x) for x in Ns.list())
    eta = RF(B) / RF(2)^265
    Rc2 = RF(RC) / RF(2)^64
    marg = 1 - (Rc2 + eta) * RF(kappa0)^2 - eta
    print(nm, "Rc^2 = %.9f (Rc = %.7f), eta = absSum(N + N^T) / 2^265 = %.3e, 1 - (Rc^2 + eta) kappa0^2 - eta = %.3e" % (Rc2, sqrt(Rc2), eta, marg))
    assert marg > 0
    sizes = {"P": max(abs(x) for r in P for x in r).nbits(), "Lam": max(Lam).nbits(), "Mu": max(max(r) for r in Mu).nbits(),
             "W": max(abs(x) for r in W for x in r).nbits(), "Mk": max(abs(x) for r in Mk for x in r).nbits(), "N": max(abs(x) for x in Ns.list()).nbits()}
    print(nm, "bit sizes", sizes)
    print(nm, "sums: lam %.6f, mu %.6f, |Mk| %.6f (real units)" % (RF(sum(Lam)) / 2^64, RF(sum(sum(r) for r in Mu)) / 2^64, RF(sum(abs(x) for r in Mk for x in r)) / 2^64))
    print(nm, "RCn", RC, "Bn", B)
    Vt = [[V[e][a] for e in range(30)] for a in range(46)]
    Gt = [[G[k][a] for k in range(18)] for a in range(46)]
    L = open(os.environ["OUT"] + "/D1Kernel_%s.lean" % nm, "w")
    L.write("""set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! D1: kernel check of the LP certificate of frame %s, generated by
code/lean-data/d1_kernel.sage. Signed integers are stored as `Nat` plus an offset (2^101 for P and V, 2^180 for W, 2^80 for Mk) and decoded in the kernel. -/

namespace D1Kernel

def dI (o n : Nat) : Int := (n : Int) - (o : Int)
def dL (o : Nat) (l : List Nat) : List Int := l.map (dI o)
def dLL (o : Nat) (l : List (List Nat)) : List (List Int) := l.map (dL o)
def nL (l : List Nat) : List Int := l.map Int.ofNat

""" % nm)
    L.write("def Pn : List (List Nat) := %s\n\n" % lst([lst([enc(x, "P") for x in r]) for r in P]))
    L.write("def Sn : List (Nat × Nat) := %s\n\n" % lst(["(%d, %d)" % e for e in S]))
    L.write("def Lamn : List Nat := %s\n\n" % lst([str(x) for x in Lam]))
    L.write("def Mun : List (List Nat) := %s\n\n" % lst([lst([str(x) for x in r]) for r in Mu]))
    L.write("def Vn : List (List Nat) := %s\n\n" % lst([lst([enc(x, "V") for x in r]) for r in V]))
    L.write("def Wn : List (List Nat) := %s\n\n" % lst([lst([enc(x, "W") for x in r]) for r in W]))
    L.write("def Mkn : List (List Nat) := %s\n\n" % lst([lst([enc(x, "M") for x in r]) for r in Mk]))
    L.write("def RCn : Nat := %s\n\ndef Bn : Nat := %s\n\n" % (RC, B))
    L.write(r"""def getP (P : List (List Int)) (k m : Nat) : Int := (P.getD k []).getD m 0

/-- `v_e`, scale 2^100: `v_e . (w, t) = w - (<p_i, t_j> + <p_j, t_i>)` for `e = (i, j)`. -/
def vEntry (P : List (List Int)) (e : Nat × Nat) (a : Nat) : Int :=
  if a = 0 then 2 ^ 100 else
    (if (a - 1) / 3 = e.2 then -getP P e.1 ((a - 1) % 3) else 0) +
    (if (a - 1) / 3 = e.1 then -getP P e.2 ((a - 1) % 3) else 0)

def mkV (P : List (List Int)) (S : List (Nat × Nat)) : List (List Int) :=
  S.map fun e => (List.range 46).map fun a => vEntry P e a

def mkVt (P : List (List Int)) (S : List (Nat × Nat)) : List (List Int) :=
  (List.range 46).map fun a => S.map fun e => vEntry P e a

/-- The TPerp forms, scale 2^100: `<p_k, t_k>` for `k < 15`, `(sum_k p_k x t_k)_c` for `k = 15 + c`. -/
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

/-- Row `a` of `N`, scale 2^264. -/
def nRow (RC : Int) (Lam : List Int) (V W Mk : List (List Int)) (a : Nat) (vt gt : List Int) :
    List Int :=
  let base := (List.range 46).map fun b =>
    if a = 0 ∧ b = 0 then RC * 2 ^ 200 else if a = b then -(2 ^ 264) else 0
  let r0 := if a = 0 then lin (Lam.map fun l => -(l * 2 ^ 100)) V base else base
  let r1 := lin (vt.map fun x => -x) W r0
  lin (gt.map fun x => -(x * 2 ^ 100)) Mk r1

def absSum (rows : List (List Int)) : Nat := rows.foldl (fun s r => r.foldl (fun s x => s + x.natAbs) s) 0

def nMat (RC : Int) (Lam : List Int) (V W Mk Vt Gt : List (List Int)) : List (List Int) :=
  ((List.range 46).zip (Vt.zip Gt)).map fun (a, vt, gt) => nRow RC Lam V W Mk a vt gt

def oP : Nat := 2 ^ 101
def oW : Nat := 2 ^ 180
def oM : Nat := 2 ^ 80

theorem checkV : mkV (dLL oP Pn) Sn = dLL oP Vn := by decide +kernel

theorem checkW : mkW (Mun.map nL) (dLL oP Vn) = dLL oW Wn := by decide +kernel

def tr (rows : List (List Int)) : List (List Int) :=
  rows.foldr (fun r acc => List.zipWith List.cons r acc) (List.replicate 46 [])

def symm (N : List (List Int)) : List (List Int) := List.zipWith (List.zipWith (· + ·)) N (tr N)

theorem checkN : absSum (symm (nMat (RCn : Int) (nL Lamn) (dLL oP Vn) (dLL oW Wn) (dLL oM Mkn)
    (tr (dLL oP Vn)) (mkGt (dLL oP Pn)))) ≤ Bn := by
  decide +kernel

end D1Kernel
""")
    L.close()
    print(nm, "wrote D1Kernel_%s.lean" % nm)
