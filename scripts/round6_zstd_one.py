#!/usr/bin/env python3
"""ROUND 6-AT: exact contraction generator d_S of a characteristic-zero msolve terminal via a strong Groebner
basis over the integers (Singular, ring "integer").  (d_S) = I_S cap Z; the primes dividing d_S are EXACTLY the
characteristics in which the terminal ideal fails to be the unit ideal.
Self-capped (registry R6.110 incident): Singular runs as a direct child under a 1-second watchdog that SIGKILLs it
when its resident size exceeds --rss-mb (default 2000) or the --wall (default 120 s) elapses.  macOS compresses
memory, so RSS under-reports the footprint: keep --rss-mb conservative and never run more than one at a time.
Prints "<name> ZSTD d=<int> size=<k> seconds=<s>" or "<name> FAIL <reason>".
Usage: round6_zstd_one.py <terminal.ms> [--scratch DIR] [--wall SECONDS] [--rss-mb MB]"""
import sys, os, re, subprocess, time, signal
sys.stdout.reconfigure(line_buffering=True)
SING = os.path.expanduser("~/.local/bin/Singular")
argv = sys.argv[1:]; scratch = "/tmp"; wall = 120; rss_mb = 2000
for flag in ("--scratch", "--wall", "--rss-mb"):
    if flag in argv:
        k = argv.index(flag); val = argv[k + 1]; argv = argv[:k] + argv[k + 2:]
        if flag == "--scratch": scratch = val
        elif flag == "--wall": wall = int(val)
        else: rss_mb = int(val)
ms = argv[0]; name = os.path.basename(ms)[:-3]
lines = open(ms).read().splitlines()
variables = lines[0].strip(); assert lines[1].strip() == "0", "characteristic-zero input expected"
body = "\n".join(lines[2:]).strip().rstrip(",")
gens = [g.strip() for g in body.split(",\n") if g.strip()]
script = "ring R_ = integer,(%s),dp;\nideal I =\n%s;\nideal G = std(I);\nint i; bigint d = 0;\nfor (i = 1; i <= size(G); i = i + 1) { if (deg(G[i]) == 0) { d = bigint(leadcoef(G[i])); } }\nprint(\"ZSTD_D \" + string(d) + \" SIZE \" + string(size(G)));\nexit;\n" % (variables, ",\n".join(gens))
p = os.path.join(scratch, name + ".zstd.sing"); open(p, "w").write(script)
outp = os.path.join(scratch, name + ".zstd.out")
t0 = time.time(); peak = 0; reason = None
with open(outp, "w") as fh:
    proc = subprocess.Popen([SING, "-q", p], stdout=fh, stderr=subprocess.STDOUT)
    while proc.poll() is None:
        time.sleep(1)
        try:
            rss = int(subprocess.run(["ps", "-o", "rss=", "-p", str(proc.pid)], capture_output=True, text=True).stdout.strip() or 0) // 1024
        except ValueError:
            rss = 0
        peak = max(peak, rss)
        if rss > rss_mb: reason = "rss-cap %dMB" % rss
        elif time.time() - t0 > wall: reason = "timeout %ds" % wall
        if reason:
            proc.kill(); proc.wait(); break
secs = time.time() - t0
out = open(outp).read()
try: os.remove(outp)
except OSError: pass
if reason:
    print("%s FAIL %s peak_rss=%dMB seconds=%.0f" % (name, reason, peak, secs)); sys.exit(0)
m = re.search(r"ZSTD_D (-?\d+) SIZE (\d+)", out)
if m and m.group(1) not in ("0",):
    print("%s ZSTD d=%s size=%s seconds=%.0f peak_rss=%dMB" % (name, abs(int(m.group(1))), m.group(2), secs, peak))
elif m:
    print("%s FAIL zstd-no-constant size=%s seconds=%.0f" % (name, m.group(2), secs))
else:
    print("%s FAIL singular rc=%s %s" % (name, proc.returncode, out.strip().replace("\n", " ")[:200]))
