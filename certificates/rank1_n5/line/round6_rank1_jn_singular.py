#!/usr/bin/env python3
"""ROUND 6-AU (registry R6.113): the deflation (Krylov-determinant) ideal J_n of the rank-one stratum, built with
Singular's polynomial arithmetic over GF(p) (or Q) — sympy is far too slow for n >= 6 — and decided by msolve.
Same family as round6_rank1_n5.py: R = [x, e_1 + y_1 x, ..., e_{n-1} + y_{n-1} x] ((n-1) x n), and for every column j
and ordering tau of the other n-1 columns D_{j,tau} = det[c_j, M c_j, ..., M^{n-2} c_j] with M = [c_tau(1) ... c_tau(n-1)].
J_n = (all n (n-1)! determinants) unit over GF(p) ==> the rank-one stratum of 16.95 at n holds in characteristic p
(Lean cyclic_standardBasis_of_principalBlock, general n).  Singular is used ONLY for determinants (no Groebner bases);
it runs under a 1-second RSS/wall watchdog; msolve runs one at a time under a wall cap; swap gate < 9 GB.
Usage: round6_rank1_jn_singular.py <n> <p> [--out DIR] [--wall-build 900] [--wall-msolve 1800] [--rss-mb 1500] [--build-only]"""
import sys, os, re, time, itertools, subprocess
sys.stdout.reconfigure(line_buffering=True)
SING = os.path.expanduser("~/.local/bin/Singular"); MS = os.path.expanduser("~/.local/bin/msolve")
ENV = dict(os.environ, DYLD_LIBRARY_PATH=os.path.expanduser("~/.local/lib"))
argv = sys.argv[1:]; wall_b = 900; wall_m = 1800; rss_mb = 1500; build_only = False
if "--build-only" in argv: build_only = True; argv.remove("--build-only")
out = None
if "--out" in argv:
    k = argv.index("--out"); out = argv[k + 1]; argv = argv[:k] + argv[k + 2:]
for flag in ("--wall-build", "--wall-msolve", "--rss-mb"):
    if flag in argv:
        k = argv.index(flag); val = int(argv[k + 1]); argv = argv[:k] + argv[k + 2:]
        if flag == "--wall-build": wall_b = val
        elif flag == "--wall-msolve": wall_m = val
        else: rss_mb = val
n = int(argv[0]); p = int(argv[1]); m = n - 1
OUT = out or os.path.dirname(os.path.abspath(__file__)); os.makedirs(OUT, exist_ok=True)
xs = ["x%d" % i for i in range(1, m + 1)]; ys = ["y%d" % i for i in range(1, m + 1)]
VARS = ys + xs
ms_path = OUT + "/J%d_p%d.ms" % (n, p)
def watched(cmd, wall, tag, stdin_path=None):
    # Singular is fed its script on STDIN (with a file argument it stayed interactive after the script and hung)
    # stdout goes to a FILE: with a pipe, Singular's warnings filled the 64 KB pipe buffer and deadlocked (n = 6 hang, 12:2x)
    t0 = time.time(); peak = 0; reason = None
    outp = OUT + "/%s_n%d_p%d.out" % (tag, n, p); fh = open(outp, "w")
    proc = subprocess.Popen(cmd, stdin=open(stdin_path) if stdin_path else None, stdout=fh, stderr=subprocess.STDOUT, text=True, env=ENV)
    while proc.poll() is None:
        time.sleep(1)
        try: rss = int(subprocess.run(["ps", "-o", "rss=", "-p", str(proc.pid)], capture_output=True, text=True).stdout.strip() or 0) // 1024
        except ValueError: rss = 0
        peak = max(peak, rss)
        if rss > rss_mb: reason = "rss-cap %dMB" % rss
        elif time.time() - t0 > wall: reason = "timeout %ds" % wall
        if reason: proc.kill(); proc.wait(); break
    fh.close(); out = open(outp).read()
    return reason, out, time.time() - t0, peak
def swap_mb():
    mm = re.search(r"used = ([\d.]+)M", subprocess.run(["sysctl", "vm.swapusage"], capture_output=True, text=True).stdout)
    return float(mm.group(1)) if mm else 0.0
# ---- build the determinants with Singular (polynomial arithmetic only) ----
lines = ["ring R_ = %d,(%s),dp;" % (p, ",".join(VARS))]
# columns of R: c0 = x; ck = e_k + y_k x
for k in range(n):
    entries = []
    for r in range(m):
        if k == 0: entries.append(xs[r])
        else: entries.append(("1+" if r == k - 1 else "") + "%s*%s" % (ys[k - 1], xs[r]))
    lines.append("matrix c%d[%d][1] = %s;" % (k, m, ",".join(entries)))
lines.append("ideal J; int cnt = 0; poly D; int rr;")
for j in range(n):
    others = [k for k in range(n) if k != j]
    for tau in itertools.permutations(others):
        lines.append("matrix M%s[%d][%d] = %s;" % ("", m, m, ",".join("c%d[%d,1]" % (tau[c], r + 1) for r in range(m) for c in range(m))))
        lines.append("matrix K[%d][%d]; matrix v = c%d; int q;" % (m, m, j))
        lines.append("for (q = 1; q <= %d; q = q + 1) { for (rr = 1; rr <= %d; rr = rr + 1) { K[rr, q] = v[rr, 1]; } v = M * v; }" % (m, m))
        lines.append("D = det(K); if (D != 0) { cnt = cnt + 1; J[cnt] = D; }")
        lines.append("kill M; kill K; kill v; kill q;")
lines.append('print("NONZERO " + string(cnt) + " MAXDEG " + string(deg(J[1])));')
lines.append('int i; int md = 0; for (i = 1; i <= size(J); i = i + 1) { if (deg(J[i]) > md) { md = deg(J[i]); } } print("MAXDEG " + string(md));')
lines.append('link l = ":w %s"; write(l, "%s"); write(l, "%d");' % (ms_path, ",".join(VARS), p))
lines.append('for (i = 1; i <= size(J); i = i + 1) { if (i < size(J)) { write(l, string(J[i]) + ","); } else { write(l, string(J[i])); } }')
lines.append("close(l); exit;")
sing_path = OUT + "/build_J%d_p%d.sing" % (n, p); open(sing_path, "w").write("\n".join(lines) + "\n")
T0 = time.time()
reason, out, s, peak = watched([SING, "-q"], wall_b, "build", stdin_path=sing_path)
mm = re.search(r"NONZERO (\d+)", out); md = re.findall(r"MAXDEG (\d+)", out)
print("build n=%d p=%d: %s nonzero=%s maxdeg=%s %.0fs peak=%dMB %s" % (n, p, "FAIL " + reason if reason else "ok", mm.group(1) if mm else "?", md[-1] if md else "?", s, peak, out.strip().replace("\n", " | ")[-200:] if reason else ""))
if reason or not os.path.exists(ms_path): sys.exit(1)
if build_only: sys.exit(0)
# ---- decide with msolve ----
while swap_mb() > 9000: print("  swap %.0f MB > 9000, waiting" % swap_mb()); time.sleep(30)
o = ms_path + ".gb"
if os.path.exists(o): os.remove(o)
reason, out, s, peak = watched([MS, "-g", "2", "-v", "0", "-t", "1", "-f", ms_path, "-o", o], wall_m, "msolve")
if reason or not os.path.exists(o): print("J_%d over %s: NORESULT %s (%.0fs, peak %dMB)" % (n, "Q" if p == 0 else "GF(%d)" % p, reason, s, peak)); sys.exit(2)
body = "".join(l for l in open(o) if not l.startswith("#")).replace("\n", "").replace(" ", "")
print("J_%d over %s: %s  (%.0fs, peak %dMB)  [total %.0fs]" % (n, "Q" if p == 0 else "GF(%d)" % p, "UNIT [1]" if body.startswith("[1]") else "NOT unit (basis %d chars: %s...)" % (len(body), body[:60]), s, peak, time.time() - T0))
