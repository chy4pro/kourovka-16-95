#!/usr/bin/env python3
"""ZSTD worker v3 (registry R6.112): exact integer content of one characteristic-zero msolve terminal.
Each Singular call runs in ITS OWN transient systemd scope (MemoryMax from $MEMMAX, via $SR) so that a memory
kill removes only that Singular and this worker survives to run the next attempt (v2 lost the lift fallback when
the whole scope was killed).  Attempts, each with its own wall:
  1. strong Groebner basis over the integers (ring "integer"): constant = contraction generator d
       -> "<name> ZSTD d=<int> size=<k> seconds=<s>"
  2. Nullstellensatz certificate over Q by lift(I, ideal(1)); D = product of coefficient denominators, d | D
       -> "<name> LIFT D=<int> terms=<k> seconds=<s> zstd=<outcome>"
  3. "<name> FAIL zstd=<outcome> lift=<outcome>"
Usage: zlift_one_v3.py <terminal.ms> <outdir> <workdir> <wall_zstd> <wall_lift>"""
import sys, os, subprocess, time, re, shlex
ms, outdir, workdir, wall_z, wall_l = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
name = os.path.basename(ms)[:-3]
SR = os.environ.get("SR", ""); MEMMAX = os.environ.get("MEMMAX", "14G")
lines = open(ms).read().splitlines()
variables = lines[0].strip(); assert lines[1].strip() == "0", "characteristic-zero input expected"
body = "\n".join(lines[2:]).strip().rstrip(",")
gens = [g.strip() for g in body.split(",\n") if g.strip()]
ideal_txt = ",\n".join(gens)
def run_singular(script, secs, tag):
    p = os.path.join(workdir, name + "." + tag + ".sing"); open(p, "w").write(script)
    cmd = ["timeout", "-s", "KILL", str(secs), "Singular", "-q", p]
    if SR: cmd = shlex.split(SR) + ["-p", "MemoryMax=" + MEMMAX, "--"] + cmd
    t0 = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=secs + 60)
        out, rc = r.stdout, r.returncode
    except subprocess.TimeoutExpired:
        out, rc = "", -1
    try: os.remove(p)
    except OSError: pass
    return out, rc, time.time() - t0
z_script = f"""ring R_ = integer,({variables}),dp;
ideal I =
{ideal_txt};
ideal G = std(I);
int i; bigint d = 0;
for (i = 1; i <= size(G); i = i + 1) {{ if (deg(G[i]) == 0) {{ d = bigint(leadcoef(G[i])); }} }}
print("ZSTD_D " + string(d) + " SIZE " + string(size(G)));
exit;
"""
out, rc, s = run_singular(z_script, wall_z, "zstd")
m = re.search(r"ZSTD_D (-?\d+) SIZE (\d+)", out)
res = None; zout = "ok"
if m and m.group(1) != "0":
    res = f"{name} ZSTD d={abs(int(m.group(1)))} size={m.group(2)} seconds={s:.0f}"
elif m:
    res = f"{name} FAIL zstd-no-constant size={m.group(2)} seconds={s:.0f}"
else:
    zout = "timeout" if s >= wall_z - 1 else f"killed-rc{rc}"
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
    out2, rc2, s2 = run_singular(lift_script, wall_l, "lift")
    m2 = re.search(r"LIFT_D (\d+) TERMS (\d+)", out2)
    if m2: res = f"{name} LIFT D={m2.group(1)} terms={m2.group(2)} seconds={s + s2:.0f} zstd={zout}"
    elif "NOTUNIT" in out2: res = f"{name} FAIL not-unit-over-Q seconds={s + s2:.0f}"
    elif "BADCERT" in out2: res = f"{name} FAIL bad-certificate seconds={s + s2:.0f}"
    else:
        lout = "timeout" if s2 >= wall_l - 1 else f"killed-rc{rc2}"
        res = f"{name} FAIL zstd={zout} lift={lout} seconds={s + s2:.0f}"
open(os.path.join(outdir, name + ".result"), "w").write(res + "\n")
print(res)
