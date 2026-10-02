# Ball-arithmetic re-check of the constants used by the proof (Sage RealBallField, 256 bits).
# (1) params15ft.txt: dlo, dhi, alo, ahi, shi read as exact decimal rationals and compared with
#     balls of 53.65785 deg, 56.6716 deg, alpha(d) = acos(cos d / (1 + cos d)) and
#     smax(d) = 4 atan(1 / sqrt(cos d)) (code/gp/consts.gp);
# (2) the d range: 53.65785 deg < psi* (u from the exact construction, data/bk15_exact.txt ball) and
#     56.6716 deg >= the Fejes Toth bound for N = 15, arccos((cot^2(N pi / (6 (N - 2))) - 1) / 2);
# (3) the numerical margins of Section 4.3 of the paper: [3.1], [3.2],
#     [3.3] at the ends of the range (monotonicity proved in Section 4) and [3.4] on 40
#     subintervals, all as certified signs of balls.
# Usage: sage code/sage/params_check.sage   (from the repository root)
RBF256 = RealBallField(256)
R = RBF256
pi_ = R.pi()
dg = pi_ / 180
def dec(s):
    # exact rational value of a decimal string
    neg = s.startswith("-")
    s = s.lstrip("+-")
    ip_, _, fp = s.partition(".")
    q = QQ(Integer(ip_ + fp)) / 10**len(fp)
    return -q if neg else q
vals = {}
for l in open("data/params15ft.txt"):
    w = l.split()
    if len(w) == 2 and w[0] in ("dlo", "dhi", "alo", "ahi", "shi"):
        vals[w[0]] = dec(w[1])
Dlo = R(dec("53.65785")) * dg
Dhi = R(dec("56.6716")) * dg
def alpha(d): return (d.cos() / (1 + d.cos())).arccos()
def smax(d): return 4 * (1 / d.cos().sqrt()).arctan()
def hh(d): return (d.cos() / (d / 2).cos()).arccos()
def ok(b): return "OK" if b else "FAIL"
def sci(q, up, n=8):
    # the positive rational q rounded to n significant digits toward +infinity (up) or -infinity
    n = int(n); e = int(floor(RR(q).log10()))
    while floor(q / QQ(10)**(e - n + 1)) >= 10**n: e += 1
    while floor(q / QQ(10)**(e - n + 1)) < 10**(n - 1): e -= 1
    m = int(ceil(q / QQ(10)**(e - n + 1)) if up else floor(q / QQ(10)**(e - n + 1)))
    if m == 10**n: m, e = m // 10, e + 1
    return "%d.%0*de%+03d" % (m // 10**(n - 1), int(n - 1), m % 10**(n - 1), e)
def fix(x, up, n):
    # x (rational, real ball endpoint or real algebraic) rounded to n decimals toward +infinity (up) or -infinity
    n = int(n); m = int((x * 10**n).ceil() if up else (x * 10**n).floor())
    return "%s%d.%0*d" % ("-" if m < 0 else "", abs(m) // int(10)**n, n, abs(m) % int(10)**n)
checks = []
def chk(name, ball_pos):
    # ball_pos must be a ball certified > 0; its lower end, rounded down, is printed
    good = ball_pos > 0
    checks.append(good)
    print("%-58s %s  (margin >= %s)" % (name, ok(good), sci(ball_pos.lower().exact_rational(), False) if good else ball_pos))
chk("dlo_file <= 53.65785 deg", Dlo - R(vals["dlo"]))
chk("dhi_file >= 56.6716 deg", R(vals["dhi"]) - Dhi)
chk("alo_file <= alpha(53.65785 deg)", alpha(Dlo) - R(vals["alo"]))
chk("ahi_file >= alpha(56.6716 deg)", R(vals["ahi"]) - alpha(Dhi))
chk("shi_file >= smax(56.6716 deg)", R(vals["shi"]) - smax(Dhi))
# psi*: u is the root of 13x^5 - x^4 + 6x^3 + 2x^2 - 3x - 1 in (0.5, 0.7), isolated here
x = polygen(QQ)
pu = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1
rts = [r for r in pu.roots(RealIntervalField(256), multiplicities=False) if r > RealIntervalField(256)(0.5) and r < RealIntervalField(256)(0.7)]
assert len(rts) == 1
u = R(rts[0])
psi = u.arccos()
chk("psi* - 53.65785 deg (u root of 13x^5 - ... in (0.5, 0.7))", psi - Dlo)
chk("53.6578502 deg - psi* (main range starts above psi*)", R(dec("53.6578502")) * dg - psi)
N = 15
om = N * pi_ / (6 * (N - 2))
ft = (((1 / om.tan())**2 - 1) / 2).arccos()
ftd = ft / dg
print("Fejes Toth bound for N = 15 in [%s, %s] deg" % (fix(ftd.lower().exact_rational(), False, 9), fix(ftd.upper().exact_rational(), True, 9)))
chk("56.6716 deg - Fejes Toth bound", Dhi - ft)
chk("[3.1] 2 pi - 5 alpha(dhi)", 2 * pi_ - 5 * alpha(Dhi))
chk("[3.2] pi (1 + sin h(dlo)) - 5 dhi", pi_ * (1 + hh(Dlo).sin()) - 5 * Dhi)
chk("[3.3] pi - 2 h(dhi) - dhi", pi_ - 2 * hh(Dhi) - Dhi)
def Pform(l, h):
    return 2 * ((l.cos() - h.sin()**2) / h.cos()**2).arccos() + 2 * h.sin() * (pi_ - 2 * (h.tan() * (l / 2).tan()).arcsin())
K = 40
worst = None
for i in range(K):
    a = Dlo + i * (Dhi - Dlo) / K
    b = Dlo + (i + 1) * (Dhi - Dlo) / K
    m = Pform(a, hh(a)) - 6 * b
    if worst is None or m.lower() < worst.lower():
        worst = m
chk("[3.4] min over 40 subintervals of P(a, h(a)) - 6 b", worst)
print("ALL OK" if all(checks) else "SOME CHECK FAILED")
