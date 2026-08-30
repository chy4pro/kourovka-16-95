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
  test "$count" = 54727 || fail basis-count
  for family in k1695_r6_r2split k1695_r6_r2split357 k1695_r6_r2splitq k1695_r6_r2split1113 r2split_check r2split_odd rank1; do
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
  printf 'x\n2\nx,\nx+1\n' > "$tmp/unit.ms"
  "$MSOLVE_BIN" -g 2 -t 1 -f "$tmp/unit.ms" -o "$tmp/unit.gb" >/dev/null 2>&1 || fail msolve-exit
  body=$(grep -v '^#' "$tmp/unit.gb" | tr -d '[:space:]')
  case "$body" in '[1]:'|'[1]') pass 'msolve 0.10.1 tiny unit basis' ;; *) fail msolve-unit-basis ;; esac
  rm -rf "$tmp"; trap - EXIT INT TERM
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
    "$MSOLVE_BIN" -g 2 -t 1 -f "$input" -o "$output" >/dev/null 2>&1 || fail "replay-$input"
  done
  pass 'full raw-input replay'
}

case "$TARGET" in
  quick) check_manifest; check_lean_record; check_bases; check_msolve; check_data ;;
  lean) check_lean_record ;;
  lean-build) lean_build ;;
  data) check_data ;;
  rank1|rank2-*) rank_target "$TARGET" ;;
  full) check_manifest; check_lean_record; check_bases; check_data; full_replay ;;
  *) fail "unknown-target-$TARGET" ;;
esac
