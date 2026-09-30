# The join of code/impl1/coverage_join.sh (read that file first). POSIX awk (mawk or gawk).
# Variables: W (work directory with recs, jobs, certg, skip), R (replay directory), TLO, THI (the d
# range tdeep reads from data/params15ft.txt, radians, as printed by pcrec --drange), SELFTEST.

function fail(msg) {
    nfail++
    if (nfail <= 100) print "FAIL: " msg
}

function binom(n, r,   i, v) {
    if (r < 0 || r > n) return 0
    v = 1
    for (i = 1; i <= r; i++) v = v * (n - r + i) / i
    return v
}

# class k of a level-2 input file, from its name
function kof(f) {
    if (f ~ /^in_k0_[0-9]+\.pc$/) return 0
    if (f ~ /^in9_k1_[0-9]+\.pc$/ || f == "b_k1.pc") return 1
    if (f == "b_k2.pc") return 2
    if (f ~ /^stageA_k[0-3]\.pc$/) return substr(f, 9, 1) + 0
    return -1
}

# a value printed by tdeep with {:.17e} (18 significant digits, exponent without padding); it must
# read back to a double that prints the same, so the comparisons below are exact comparisons of the
# doubles tdeep used
function exact(s,   x, a, b) {
    x = s + 0
    split(s, a, "e"); split(sprintf("%.17e", x), b, "e")
    if (a[1] != b[1] || a[2] + 0 != b[2] + 0) fail("the value " s " does not read back exactly")
    return x
}

function deg(x) { return sprintf("%.10f", x * 180 / PI) }

# x as tdeep prints it with {:.17e}: 18 significant digits, exponent without sign padding
function fmt17(x,   s, a) {
    s = sprintf("%.17e", x + 0)
    split(s, a, "e")
    return a[1] "e" (a[2] + 0)
}

function base(p,   n, a) {
    n = split(p, a, "/")
    return a[n]
}

# options with every path reduced to its file name
function cleanopts(o,   n, a, i, s) {
    n = split(o, a, " ")
    s = ""
    for (i = 1; i <= n; i++) s = s (i > 1 ? " " : "") (a[i] ~ /\// ? base(a[i]) : a[i])
    return s
}

# Cover test. Intervals lo_[1..m], hi_[1..m] (doubles) against [t0, t1]: sorts them by lower end,
# sweeps, and returns the gaps as "a b;" pairs (empty string: covered). Sets COVFULL (one interval
# contains [t0, t1]) and COVOV (smallest overlap at a junction of two slices, -1 if none).
function cover(m, t0, t1,   a, b, x, y, z, reach, g) {
    for (a = 2; a <= m; a++) {
        x = lo_[a]; y = hi_[a]; z = jb_[a]
        for (b = a - 1; b >= 1 && lo_[b] > x; b--) { lo_[b + 1] = lo_[b]; hi_[b + 1] = hi_[b]; jb_[b + 1] = jb_[b] }
        lo_[b + 1] = x; hi_[b + 1] = y; jb_[b + 1] = z
    }
    COVFULL = 0; COVOV = -1
    reach = t0; g = ""
    for (a = 1; a <= m; a++) {
        if (lo_[a] <= t0 && hi_[a] >= t1) COVFULL = 1
        if (lo_[a] > reach) g = g reach " " lo_[a] ";"
        else if (lo_[a] > t0 && hi_[a] > reach && (COVOV < 0 || reach - lo_[a] < COVOV)) COVOV = reach - lo_[a]
        if (hi_[a] > reach) reach = hi_[a]
    }
    if (reach < t1) g = g reach " " t1 ";"
    return g
}

function selftest(name, spec, want,   n, s, a, e, got) {
    n = split(spec, s, ";")
    for (a = 1; a <= n; a++) { split(s[a], e, " "); lo_[a] = e[1] + 0; hi_[a] = e[2] + 0; jb_[a] = a }
    got = cover(n, 0, 10)
    ntest++
    if (got == want) { print "selftest " name ": " (got == "" ? "covered" : "gaps " got) ", as expected"; npass++ }
    else print "selftest " name ": FAILED, got \"" got "\", expected \"" want "\""
}

BEGIN {
    PI = atan2(0, -1)
    CONVFMT = "%.17g"   # numbers turned into strings (the gaps of cover) keep every digit
    if (SELFTEST) {
        # known answers of the cover test on [0, 10]
        selftest("one interval", "0 10", "")
        selftest("wider interval", "-1 11", "")
        selftest("touching slices", "0 4;4 10", "")
        selftest("overlapping slices, unsorted", "3.5 10;0 4", "")
        selftest("nested and duplicate", "0 10;2 3;2 3", "")
        selftest("gap inside", "0 4;4.5 10", "4 4.5;")
        selftest("lower end missing", "0.5 10", "0 0.5;")
        selftest("upper end missing", "0 9.5", "9.5 10;")
        selftest("two gaps", "1 3;4 9", "0 1;3 4;9 10;")
        selftest("gap hidden by order", "6 10;0 2;1 5", "5 6;")
        print "selftest: " npass " of " ntest " as expected"
        exit (npass == ntest ? 0 : 1)
    }
    if (PREFAIL) fail("section 1, the stage-A survivor files")
    tlo = exact(TLO); thi = exact(THI)

    # 1. The records of the stage-A survivor files (they come first in recs), then of the level-2
    # inputs; each input record is identified with a survivor by its bytes, or else by its canonical
    # code.
    while ((getline < (W "/recs")) > 0) {
        f = $1; i = $2 + 0; k = kof(f)
        if (k < 0) { fail(f ": not a level-2 input"); continue }
        if (i != nrec[f]) fail(f ": record " i " out of order")
        nrec[f]++
        if (!(f in seenf)) { seenf[f] = 1; nfiles++; files[nfiles] = f }
        fc[f, i] = $5 " " $6 " " $7 " " $8
        if (f ~ /^stageA_k/) {
            sid = k " " i
            nsurv[k]++
            if ($11 in byraw) { rr[k]++; fail(f " #" i ": same bytes as survivor " byraw[$11]) }
            if ($12 in bycan) { rc[k]++; fail(f " #" i ": same canonical code as survivor " bycan[$12]) }
            byraw[$11] = sid; bycan[$12] = sid
            if ($10 > 5) { bd[k]++; fail("survivor " sid ": degree " $10) }
            if ($9 != 0) { bf[k]++; fail("survivor " sid ": a face of size other than 3 to 6") }
            if ($8 < k) { bh[k]++; fail("survivor " sid ": " $8 " hexagons, fewer than k") }
            nch[sid] = (k == 0) ? 1 : binom($8, k)
            nchk[k] += nch[sid]
            id[f, i] = sid; how = "bytes"
        } else if ($11 in byraw) {
            sid = byraw[$11]; how = "bytes"
        } else if ($12 in bycan) {
            sid = bycan[$12]; how = "canonical code"
        } else {
            fail(f " #" i ": neither the bytes nor the canonical code of a stage-A survivor")
            continue
        }
        split(sid, sk_, " ")
        if (sk_[1] != k) fail(f " #" i ": survivor " sid " of another class")
        id[f, i] = sid; nhow[f, how]++
        if ((f, sid) in inf) { nrep2[f]++; fail(f ": survivor " sid " twice") }
        inf[f, sid] = 1; where[sid] = where[sid] " " f "#" i
        if (f ~ /^in_k0_/ || f ~ /^in9_k1_/) occ[sid]++
    }
    close(W "/recs")

    print "== 2. The stage-A survivors (inputs/stageA_k<k>.pc) and their choices of H"
    for (k = 0; k <= 3; k++)
        printf "k = %d: %d survivors; repeated records %d, repeated canonical codes %d; degree above 5: %d, a face of size other than 3 to 6: %d, fewer than k hexagons: %d; %d choices of H in all\n", k, nsurv[k], rr[k], rc[k], bd[k], bf[k], bh[k], nchk[k]
    print ""
    print "== 3. The level-2 inputs, record by record"
    for (a = 1; a <= nfiles; a++) {
        f = files[a]
        if (f ~ /^stageA_k/) continue
        printf "%s: %d records, class k = %d; %d byte-identical to a survivor, %d identified by canonical code, %d unidentified, %d repeated\n", f, nrec[f], kof(f), nhow[f, "bytes"], nhow[f, "canonical code"], nrec[f] - nhow[f, "bytes"] - nhow[f, "canonical code"], nrep2[f] + 0
    }
    # order: in_k0_j record i is stageA_k0 record 3 i + j; in9_k1_j record i is stageA_k1 record 9 i + j
    for (a = 1; a <= nfiles; a++) {
        f = files[a]
        if (f ~ /^in_k0_/) { m = 3; j = substr(f, 7) + 0; k = 0 }
        else if (f ~ /^in9_k1_/) { m = 9; j = substr(f, 8) + 0; k = 1 }
        else continue
        bad = 0
        for (i = 0; i < nrec[f]; i++) if (id[f, i] != k " " (m * i + j)) bad++
        if (bad) fail(f ": " bad " records not at their round-robin place")
        else printf "%s record i = stageA_k%d.pc record %d i + %d, byte for byte, for every i\n", f, k, m, j
    }
    for (k = 0; k <= 1; k++) {
        bad = 0
        for (i = 0; i < nsurv[k]; i++) if (occ[k " " i] != 1) bad++
        if (bad) fail("k = " k ": " bad " survivors not exactly once in the level-2 input files")
        else printf "k = %d: every survivor is in exactly one of the %s files\n", k, (k == 0 ? "in_k0_*" : "in9_k1_*")
    }
    # the graphs set aside from the first pass: skip lists of records/first/full
    t = 0; bad = 0
    for (r = 0; r <= 8; r++) {
        sk = W "/skip/b_k1_" r ".idx"
        while ((getline s < sk) > 0) {
            ee = id["in9_k1_" r ".pc", s + 0]
            if (id["b_k1.pc", t] != ee) bad++
            aside[ee] = "k1_" t; t++
        }
        close(sk)
    }
    if (bad || t != nrec["b_k1.pc"]) fail("b_k1.pc is not the concatenation of the in9_k1 records at the skip lists")
    else printf "b_k1.pc = the records of in9_k1_0..8.pc at the indices of b_k1_0..8.idx, in order, byte for byte (%d records)\n", t
    n = 0; bad = 0
    while ((getline s < (W "/skip/skip_k2.idx")) > 0) { ee = "2 " (s + 0); want2[ee] = 1; n++ }
    close(W "/skip/skip_k2.idx")
    for (i = 0; i < nrec["b_k2.pc"]; i++) { if (!(id["b_k2.pc", i] in want2)) bad++; aside[id["b_k2.pc", i]] = "k2_" i }
    if (bad || n != nrec["b_k2.pc"]) fail("b_k2.pc is not the set of stageA_k2 records at skip_k2.idx")
    else printf "b_k2.pc = the records of stageA_k2.pc at the %d indices of skip_k2.idx, as a set (%d byte-identical, %d by canonical code)\n", n, nhow["b_k2.pc", "bytes"], nhow["b_k2.pc", "canonical code"]
    n = 0; sk3 = ""
    while ((getline s < (W "/skip/skip_k3.idx")) > 0) { aside["3 " (s + 0)] = "k3_" (s + 0); n++; sk3 = sk3 " " s }
    close(W "/skip/skip_k3.idx")
    printf "k = 3: the jobs read stageA_k3.pc itself; set aside: indices%s\n", sk3
    naside = 0
    for (ee in aside) naside++
    printf "set aside from the first pass: %d graphs\n", naside
    print ""

    # 2. The jobs. Certificate headers "G idx choice" of every job's certificate file.
    while ((getline < (W "/certg")) > 0) cg[$1, $2, $3] = 1
    close(W "/certg")
    print "== 4. The replay jobs (job list of code/impl1/replay_all.sh, logs and per-graph lines of the replay)"
    print "job | input | options | d range of the log (rad) = (deg) | lines: VERIFIED, NO_CERTIFICATE"
    nj = 0
    while ((getline line < (W "/jobs")) > 0) {
        split(line, J, "|")
        name = J[1]; cert = J[2]; f = base(J[3]); opts = J[4]
        nj++; jobk[name] = kof(f); isjob[name] = 1
        if (!(f in nrec)) { fail(name ": input " f " unknown"); continue }
        k = kof(f)
        # options of the command line
        no = split(opts, o, " "); iso = -1; odlo = ""; odhi = ""
        for (a = 1; a <= no; a++) {
            if (o[a] == "--iso") iso = o[a + 1] + 0
            if (o[a] == "--dlo") odlo = o[a + 1]
            if (o[a] == "--dhi") odhi = o[a + 1]
        }
        if (iso != k) fail(name ": --iso " iso " on an input of class " k)
        # the log: the replay summary and the d range line of tdeep
        lg = R "/" name ".log"; hs = 0; hd = 0
        while ((getline l < lg) > 0) {
            nl = split(l, w, " ")
            if (l ~ /^replay: verified [0-9]+ failed [0-9]+ missing certificates [0-9]+ \(trig [a-z]+\)$/) {
                hs++; V = w[3] + 0; F = w[5] + 0; M = w[8] + 0; tr1 = w[10]; sub(/\)$/, "", tr1)
            } else if (l ~ /^d in \[/) {
                hd++; slo = w[3]; shi = w[4]; gsub(/[\[,]/, "", slo); gsub(/\]/, "", shi)
                glo = w[7]; ghi = w[8]; gsub(/[\[,]/, "", glo); gsub(/\]/, "", ghi)
                tot = w[11] + 0; tr2 = w[nl]
            } else fail(name ": unexpected line in the log: " l)
        }
        close(lg)
        if (hs != 1 || hd != 1) { fail(name ": log without its summary and d range lines"); continue }
        if (F != 0) fail(name ": " F " replays failed")
        if (tr1 != "rig" || tr2 != "rig") fail(name ": trig backend " tr1 "/" tr2 ", not rig")
        if (tot != nrec[f]) fail(name ": " tot " graphs read, " f " has " nrec[f])
        lo = exact(slo); hi = exact(shi)
        # the d range of the log against the command line
        if (odlo == "") { if (slo != TLO) fail(name ": lower end " slo " without --dlo") }
        else if (sprintf("%.10f", odlo) != glo) fail(name ": --dlo " odlo " but the log reads " glo)
        if (odhi == "") { if (shi != THI) fail(name ": upper end " shi " without --dhi") }
        else if (sprintf("%.10f", odhi) != ghi) fail(name ": --dhi " odhi " but the log reads " ghi)
        if (lo >= hi) fail(name ": empty d range")
        # the per-graph lines
        tx = R "/" name ".txt"; nv = 0; nm = 0; split("", seen)
        while ((getline l < tx) > 0) {
            nl = split(l, w, " ")
            i = w[1]
            if (i !~ /^[0-9]+$/ || i + 0 >= nrec[f]) { fail(name ": bad line: " l); continue }
            i = i + 0
            if (i in seen) fail(name ": graph " i " twice")
            seen[i] = 1
            fs = w[2] " " w[3] " " w[4] " " w[5]; gsub(/faces=\[|,|\]/, "", fs)
            if (fs != fc[f, i]) fail(name ": graph " i ": faces " fs ", the record has " fc[f, i])
            v = w[6]
            if (v == "VERIFIED") {
                nv++; sid = id[f, i]; nodes = w[7]; sub(/^nodes=/, "", nodes)
                for (c = 0; c < nch[sid]; c++) if (!((cert, i, c) in cg)) fail(name ": graph " i " VERIFIED without a tree for choice " c)
                if (nodes + 0 < nch[sid]) fail(name ": graph " i ": " nodes " leaves for " nch[sid] " choices")
                nvc += nch[sid]; nvl++
                cov[sid] = cov[sid] slo " " shi " " name ";"
                if (name ~ /^full_/) infull[sid] = 1
                if (name !~ /^full_/) other[sid] = 1
                if (name ~ /^pb_/) inpb[sid] = 1
            } else if (v == "NO_CERTIFICATE") nm++
            else fail(name ": graph " i ": " v)
        }
        close(tx)
        if (nv != V || nm != M) fail(name ": " nv " VERIFIED and " nm " NO_CERTIFICATE lines, the log says " V " and " M)
        printf "%s | %s | %s | [%s, %s] = [%s, %s] | %d, %d\n", name, f, cleanopts(opts), slo, shi, glo, ghi, nv, nm
        jv[name] = nv
    }
    close(W "/jobs")
    # every log of the replay directory belongs to a job of the list
    while ((getline l < (W "/logs")) > 0) if (!(l in isjob)) fail("log " l ".log of no job of the list")
    close(W "/logs")
    printf "%d jobs; %d VERIFIED lines, each with a tree for every one of its choices of H (%d trees)\n", nj, nvl, nvc
    print ""

    # 3. Coverage of [TLO, THI] for every survivor
    print "== 5. Coverage: the d ranges of the VERIFIED replays of every survivor against the d range of data/params15ft.txt"
    printf "d range: [%s, %s] rad = [%s, %s] deg\n", TLO, THI, deg(tlo), deg(thi)
    print "graphs with a replay outside the first pass, with their replays (slice [lo, hi] in degrees, job):"
    for (k = 0; k <= 3; k++) {
        nfull1[k] = 0; nsl[k] = 0; nun[k] = 0; nrep[k] = 0
        for (i = 0; i < nsurv[k]; i++) {
            sid = k " " i
            m = split(cov[sid], L, ";") - 1
            nrep[k] += m
            for (a = 1; a <= m; a++) { split(L[a], e, " "); lo_[a] = e[1] + 0; hi_[a] = e[2] + 0; jb_[a] = e[3] }
            g = cover(m, tlo, thi)
            if (g != "") {
                nun[k]++
                ng = split(g, G, ";") - 1
                for (a = 1; a <= ng; a++) { split(G[a], e, " "); fail("survivor k" k " #" i " (" substr(where[sid], 2) "): no VERIFIED replay on [" fmt17(e[1]) ", " fmt17(e[2]) "] rad = [" deg(e[1]) ", " deg(e[2]) "] deg") }
            } else if (COVFULL) nfull1[k]++
            else nsl[k]++
            if (sid in other || g != "" || !COVFULL) {
                s = ""
                for (a = 1; a <= m; a++) s = s (a > 1 ? ", " : "") "[" deg(lo_[a]) ", " deg(hi_[a]) "] " jb_[a]
                printf "  k%d #%d (%s%s): %s: %s\n", k, i, substr(where[sid], 2), (sid in aside ? ", set aside as " aside[sid] : ""), (m ? s : "none"), (g != "" ? "NOT COVERED" : (COVFULL ? "one replay of the whole range" : sprintf("slices, smallest overlap %.2e rad", COVOV)))
            }
        }
    }
    print ""
    print "== 6. Counts"
    for (k = 0; k <= 3; k++) {
        nf = 0; na = 0; nb = 0; nfa = 0; npb = 0
        for (i = 0; i < nsurv[k]; i++) {
            sid = k " " i
            if (sid in infull) nf++
            if (sid in aside) { na++; if (sid in infull) nfa++ }
            else if (!(sid in infull)) { nb++; if (sid in inpb) npb++ }
        }
        printf "k = %d: %d survivors, %d VERIFIED replays; VERIFIED in the first pass %d; set aside %d (of them VERIFIED in the first pass %d); the other %d VERIFIED in the second pass %d; covered by one replay of the whole range %d, by a union of slices only %d, not covered %d\n", k, nsurv[k], nrep[k], nf, na, nfa, nb, npb, nfull1[k], nsl[k], nun[k]
        S += nsurv[k]; RP += nrep[k]; UN += nun[k]
    }
    printf "total: %d survivors, %d VERIFIED replays, %d not covered, %d failures\n", S, RP, UN, nfail
    if (nfail) { print "coverage join: FAIL"; exit 1 }
    print "coverage join: PASS"
}
