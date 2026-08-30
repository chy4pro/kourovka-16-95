#!/usr/bin/env python3
"""ZLIFT worker v2 (registry R6.110): exact integer content of one characteristic-zero msolve terminal.
Order of attempts (the caller runs this inside a systemd scope with a real MemoryMax):
  1. Singular strong Groebner basis over the integers (ring "integer"): the constant of the basis is the
     contraction generator d = generator of I cap Z  ->  "<name> ZSTD d=<int> size=<k> seconds=<s>"
     (d = 1: unit in every characteristic; the primes of d are exactly the failing characteristics).
  2. Fallback: Nullstellensatz certificate over Q by lift(I, ideal(1)); the product D of the coefficient
     denominators is a multiple of d  ->  "<name> LIFT D=<int> terms=<k> seconds=<s>".
  3. "<name> FAIL reason" when both are out of wall.
Usage: zlift_one_v2.py <terminal.ms> <outdir> <wall_seconds_zstd> [<wall_seconds_lift>]"""
import sys, os, subprocess, time, re
ms, outdir, wall = sys.argv[1], sys.argv[2], int(sys.argv[3])
wall_lift = int(sys.argv[4]) if len(sys.argv) > 4 else wall
name = os.path.basename(ms)[:-3]
lines = open(ms).read().splitlines()
variables = lines[0].strip(); assert lines[1].strip() == "0", "characteristic-zero input expected"
body = "\n".join(lines[2:]).strip().rstrip(",")
gens = [g.strip() for g in body.split(",\n") if g.strip()]
ideal_txt = ",\n".join(gens)
def run_singular(script, secs, tag):
    p = os.path.join(outdir, name + "." + tag + ".sing"); open(p, "w").write(script)
    t0 = time.time()
    try:
        r = subprocess.run(["timeout", "-s", "KILL", str(secs), "Singular", "-q", p], capture_output=True, text=True, timeout=secs + 30)
        out = r.stdout
    except subprocess.TimeoutExpired:
        out = ""
    try: os.remove(p)
    except OSError: pass
    return out, time.time() - t0
# ring named R_ (not r): some ideals use a variable called r, which would shadow the ring name in Singular
z_script = f"""ring R_ = integer,({variables}),dp;
ideal I =
{ideal_txt};
ideal G = std(I);
int i; bigint d = 0;
for (i = 1; i <= size(G); i = i + 1) {{ if (deg(G[i]) == 0) {{ d = bigint(leadcoef(G[i])); }} }}
print("ZSTD_D " + string(d) + " SIZE " + string(size(G)));
exit;
"""
out, s = run_singular(z_script, wall, "zstd")
m = re.search(r"ZSTD_D (-?\d+) SIZE (\d+)", out)
res = None
if m and m.group(1) != "0":
    res = f"{name} ZSTD d={abs(int(m.group(1)))} size={m.group(2)} seconds={s:.0f}"
elif m:
    res = f"{name} FAIL zstd-no-constant size={m.group(2)} seconds={s:.0f}"
else:
    lift_script = f"""option(redSB);
ring R_ = 0,({variables}),dp;
ideal I =
{ideal_txt};
ideal G = std(I);
if (size(G) != 1 or G[1] != 1) {{ print("NOTUNIT"); exit; }}
matrix C = lift(I, ideal(1));
poly chk = 0; int i; int k = 0; bigint D = 1;
for (i = 1; i <= nrows(C); i = i + 1) {{
  chk = chk + I[i] * C[i,1];
  poly q = C[i,1];
  while (q != 0) {{ k = k + 1; number cf = leadcoef(q); D = D * bigint(denominator(cf)); q = q - lead(q); }}
}}
if (chk != 1) {{ print("BADCERT"); exit; }}
print("LIFT_D " + string(D) + " TERMS " + string(k));
exit;
"""
    out2, s2 = run_singular(lift_script, wall_lift, "lift")
    m2 = re.search(r"LIFT_D (\d+) TERMS (\d+)", out2)
    if m2: res = f"{name} LIFT D={m2.group(1)} terms={m2.group(2)} seconds={s + s2:.0f} zstd_wall={s:.0f}"
    elif "NOTUNIT" in out2: res = f"{name} FAIL not-unit-over-Q seconds={s + s2:.0f}"
    elif "BADCERT" in out2: res = f"{name} FAIL bad-certificate seconds={s + s2:.0f}"
    else: res = f"{name} FAIL timeout zstd={s:.0f}s lift={s2:.0f}s"
open(os.path.join(outdir, name + ".result"), "w").write(res + "\n")
print(res)
