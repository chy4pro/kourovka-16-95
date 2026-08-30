#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TARGET=${1:-quick}
ASSET=${2:-}
MSOLVE_BIN=${MSOLVE:-msolve}
if ! command -v "$MSOLVE_BIN" >/dev/null 2>&1 && test -x "$HOME/.local/bin/msolve"; then
  MSOLVE_BIN="$HOME/.local/bin/msolve"
fi

pass() { printf 'PASS %s\n' "$1"; }
fail() { printf 'FAIL %s\n' "$1" >&2; exit 1; }

check_manifest() {
  (cd "$ROOT" && shasum -a 256 -c MANIFEST.sha256 >/dev/null) || fail manifest
  pass manifest
}

check_lean_record() {
  test "$(find "$ROOT/lean/K1695" -name '*.lean' | wc -l | tr -d ' ')" = 11 || fail lean-source-count
  ! grep -R -n -E '(^|[^A-Za-z])(sorry|admit)([^A-Za-z]|$)' "$ROOT/lean/K1695" >/dev/null || fail lean-placeholders
  for log in "$ROOT"/lean/recorded_checks/*.log; do grep -q 'EXIT code=0' "$log" || fail lean-recorded-exit; done
  grep -q 'minpoly_eq_charpoly_of_rank_ge.*propext, Classical.choice, Quot.sound' "$ROOT/lean/recorded_checks/round6_lean10_axioms.log" || fail lean-axioms
  grep -q 'goodCount3.*propext, Classical.choice, Quot.sound' "$ROOT/lean/recorded_checks/round6_gc3lean_check.log" || fail lean-axioms
  pass 'C1-C3 recorded Lean kernel audits'
}

check_bases() {
  count=$(find "$ROOT/certificates" -name '*.gb' | wc -l | tr -d ' ')
  test "$count" = 55216 || fail basis-count
  for family in k1695_r6_r2split k1695_r6_r2split357 k1695_r6_r2splitq k1695_r6_r2split1113 k1695_r6_r2split1723 r2split_check r2split_odd rank1; do
    sample=$(find "$ROOT/certificates/$family" -name '*.gb' | head -n 1)
    test -n "$sample" || fail "basis-family-$family"
    test -s "$sample" || fail "basis-empty-$family"
  done
  pass "C4-C5 recorded bases ($count files)"
}

check_msolve() {
  command -v "$MSOLVE_BIN" >/dev/null 2>&1 || fail msolve-not-found
  tmp=$(mktemp -d "${TMPDIR:-/tmp}/k1695-quick.XXXXXX")
  trap 'rm -rf "$tmp"' EXIT INT TERM
  family="$ROOT/certificates/rank1_n5/independent"
  input="$family/p3.ms"
  expected="$family/p3.gb"
  output="$tmp/p3.gb"
  log="$tmp/p3.log"
  python3 "$ROOT/encoders/line/run_capped.py" --wall 600 --mem 2500000 --log "$log" -- \
    "$MSOLVE_BIN" -g 2 -v 1 -t 1 -f "$input" -o "$output" >/dev/null || fail "p3-wrapper"
  grep -q 'EXIT code=0' "$log" || fail "p3-msolve-exit"
  ! grep -q 'UNRESOLVED cap=' "$log" || fail "p3-UNRESOLVED-due-to-load"
  body=$(grep -v '^#' "$output" | tr -d '[:space:]')
  expected_body=$(grep -v '^#' "$expected" | tr -d '[:space:]')
  test "$body" = "$expected_body" || fail "p3-basis-mismatch"
  pass 'C8 independent-family p=3 capped msolve rerun'
  rm -rf "$tmp"; trap - EXIT INT TERM
}

check_rank1_n5() {
  family="$ROOT/certificates/rank1_n5/independent"
  test "$(find "$family" -maxdepth 1 -name '*.ms' | wc -l | tr -d ' ')" = 304 || fail n5-ms-count
  test "$(find "$family" -maxdepth 1 -name '*.gb' | wc -l | tr -d ' ')" = 304 || fail n5-gb-count
  python3 - "$family" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
state = json.loads((root / "prime_results.json").read_text())
audit = json.loads((root / "finite_audit.json").read_text())
assert len(state["results"]) == 304 and state["exhaustive"] and state["all_unit"]
assert [(row["characteristic"], row["rank_one_invertible_matrices"], row["failed"])
        for row in audit["audits"]] == [(2, 465, 0), (3, 19481, 0)]
PY
  grep -qx PASS "$family/GRADE.md" || fail n5-gate
  pass 'C8 certificate inventory, finite audits, and gate'
}

check_rank1_families() {
  family="$ROOT/scripts/rank1_families"
  (cd "$family" && shasum -a 256 -c SHA256SUMS >/dev/null) || fail rank1-families-checksums
  tmp=$(mktemp -d "${TMPDIR:-/tmp}/k1695-r1alln.XXXXXX")
  trap 'rm -r "$tmp"' EXIT INT TERM
  cc -O2 "$family/round6_r1alln_exhaust.c" -o "$tmp/round6_r1alln_exhaust" || fail r1alln-compile
  "$tmp/round6_r1alln_exhaust" 2 4 >"$tmp/run.log" || fail r1alln-run
  grep -q 'p=2 m=4 points=256 all_witnessed=1 bad=0' "$tmp/run.log" || fail r1alln-result
  pass 'C9-C10 every-n families and p=2 m=4 exhaustion spot check'
  rm -r "$tmp"; trap - EXIT INT TERM
}

check_data() {
  python3 "$ROOT/data/refutations/verify_refutations.py"
  pass C7
}

lean_build() {
  (cd "$ROOT/lean" && lake build)
  (cd "$ROOT/lean" && for f in K1695/*.lean; do lake env lean "$f"; done)
  pass 'C1-C3 Lean rebuild'
}

rank_target() {
  case "$1" in
    rank1) test -d "$ROOT/certificates/rank1" || fail rank1 ;;
    rank2-*) p=${1#rank2-}; grep -q '"'"$p"'"' "$ROOT/data/SUMMARY.json" || fail "$1" ;;
  esac
  check_bases
}

full_replay() {
  test -n "$ASSET" && test -d "$ASSET/certificates" || fail asset-path
  find "$ASSET/certificates" -name '*.ms' -print0 | while IFS= read -r -d '' input; do
    output="$input.replay.gb"
    log="$input.replay.log"
    python3 "$ROOT/encoders/line/run_capped.py" --wall 600 --mem 2500000 --log "$log" -- \
      "$MSOLVE_BIN" -g 2 -t 1 -f "$input" -o "$output" >/dev/null || fail "replay-$input"
    grep -q 'EXIT code=0' "$log" || fail "replay-exit-$input"
    ! grep -q 'UNRESOLVED cap=' "$log" || fail "replay-cap-$input"
  done
  pass 'full raw-input replay'
}

case "$TARGET" in
  quick) check_manifest; check_lean_record; check_bases; check_rank1_n5; check_rank1_families; check_data ;;
  lean) check_lean_record ;;
  lean-build) lean_build ;;
  data) check_data ;;
  rank1|rank2-*) rank_target "$TARGET" ;;
  full) check_manifest; check_lean_record; check_bases; check_data; full_replay ;;
  *) fail "unknown-target-$TARGET" ;;
esac
