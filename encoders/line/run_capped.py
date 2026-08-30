#!/usr/bin/env python3
"""Run one command under a wall-clock cap and a process-tree resident-memory cap (own watchdog for the
swap-bound local box).  Writes START/CAP/COMMAND header, the child's stdout+stderr, and a final line
'UNRESOLVED cap=...' (killed by this watchdog) or 'EXIT code=...' (child ended on its own) to --log.
Usage: run_capped.py --wall SECONDS --mem KIB --log FILE -- CMD ARGS..."""
from __future__ import annotations
import argparse, os, signal, subprocess, time
from pathlib import Path


def tree_rss_kib(root_pid: int) -> int:
    out = subprocess.check_output(["/bin/ps", "-axo", "pid=,ppid=,rss="], text=True)
    rows = [tuple(map(int, l.split())) for l in out.splitlines() if l.split()]
    wanted = {root_pid}; changed = True
    while changed:
        changed = False
        for pid, ppid, _ in rows:
            if ppid in wanted and pid not in wanted:
                wanted.add(pid); changed = True
    return sum(rss for pid, _, rss in rows if pid in wanted)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--wall", type=int, required=True)
    ap.add_argument("--mem", type=int, required=True, help="resident memory cap for the process tree, KiB")
    ap.add_argument("--log", required=True)
    ap.add_argument("command", nargs=argparse.REMAINDER)
    a = ap.parse_args()
    cmd = a.command[1:] if a.command[:1] == ["--"] else a.command
    if not cmd: ap.error("missing command")
    log = Path(a.log); log.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    header = f"START {time.strftime('%Y-%m-%dT%H:%M:%S')}\nCAP wall={a.wall}s resident_memory={a.mem}KiB\nCOMMAND {' '.join(cmd)}\n"
    with log.open("w") as stream:
        stream.write(header); stream.flush()
        proc = subprocess.Popen(cmd, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True,
                                env=os.environ | {"PYTHONUNBUFFERED": "1"}, text=True)
        peak = 0; cap = None
        while proc.poll() is None:
            elapsed = time.monotonic() - start
            try: peak = max(peak, tree_rss_kib(proc.pid))
            except (OSError, subprocess.SubprocessError): pass
            if elapsed >= a.wall: cap = f"wall-{a.wall}s"
            elif peak >= a.mem: cap = f"resident-memory-{a.mem}KiB"
            if cap:
                os.killpg(proc.pid, signal.SIGKILL); break
            time.sleep(0.5)
        proc.wait()
        elapsed = time.monotonic() - start
        status = (f"UNRESOLVED cap={cap}" if cap else f"EXIT code={proc.returncode}") + f" seconds={elapsed:.1f} peak_rss_kib={peak}\n"
        stream.write(status)
    print(status, end="")


if __name__ == "__main__":
    main()
