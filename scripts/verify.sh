#!/usr/bin/env bash
# Verify the formal proof end to end and print a status table.
#
#   1. lake build                (all default targets; fails on any error)
#   2. no `sorry` / `axiom` / `native_decide` in the proof sources
#   3. `MatrixIneq.mainTheorem : Statement.MainTheorem` and its axioms
#   4. leanchecker               (kernel replay of every project module; skipped if not available)
#   5. nanoda                    (independent Rust checker on a lean4export dump; skipped if not available)
#   6. lake comparator --paranoid (challenge/solution comparison in a sandbox, all bundled checkers)
#
# Tools for 4-6 are looked up in PATH and next to the active `lean` binary. Override with
#   LEANCHECKER=... LEANEXPORT=... NANODA=... ; COMPARATOR_FLAGS='' drops --paranoid
# Output goes to ./verify-out/. Exit code is 0 iff no step FAILED (skipped steps do not fail the run).
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
OUT=verify-out; mkdir -p "$OUT"
declare -a NAMES=() STATES=() NOTES=()
record() { NAMES+=("$1"); STATES+=("$2"); NOTES+=("$3"); }
PREFIX="$(lean --print-prefix 2>/dev/null)/bin"
find_tool() { # $1 = override value, $2... = candidate names
  local o="$1"; shift
  if [ -n "$o" ] && [ -x "$o" ]; then echo "$o"; return; fi
  for n in "$@"; do
    if command -v "$n" >/dev/null 2>&1; then command -v "$n"; return; fi
    if [ -x "$PREFIX/$n" ]; then echo "$PREFIX/$n"; return; fi
  done
}
AXIOMS_OK='[propext, Classical.choice, Quot.sound]'

# 1. build
if lake build > "$OUT/build.log" 2>&1; then record "lake build" PASS "$(tail -1 "$OUT/build.log")"
else record "lake build" FAIL "see $OUT/build.log"; fi

# 2. source scan (the Comparator challenge file contains the one intended `sorry`)
if grep -rnE '\bsorry\b|^\s*axiom\b|native_decide|implemented_by|^\s*unsafe\b' Statement.lean MatrixIneq.lean MatrixIneq Short.lean > "$OUT/scan.log"; then
  record "source scan" FAIL "forbidden token found, see $OUT/scan.log"
else record "source scan" PASS "no sorry / axiom / native_decide in Statement.lean, MatrixIneq/, Short.lean"; fi

# 3. statement and axioms
cat > "$OUT/Axioms.lean" <<'LEAN'
import MatrixIneq
import Short
#check (MatrixIneq.mainTheorem : Statement.MainTheorem)
#check (Short.main : Statement.MainTheorem)
#print axioms MatrixIneq.mainTheorem
#print axioms Short.main
LEAN
if lake env lean "$OUT/Axioms.lean" > "$OUT/axioms.log" 2>&1 && [ "$(grep -cF "depends on axioms: $AXIOMS_OK" "$OUT/axioms.log")" -eq 2 ]; then
  record "statement + axioms" PASS "mainTheorem and Short.main: $AXIOMS_OK"
else record "statement + axioms" FAIL "see $OUT/axioms.log"; fi

# 4. leanchecker
LC="$(find_tool "${LEANCHECKER:-}" leanchecker lean4checker)"
if [ -z "$LC" ]; then record "leanchecker" SKIP "tool not found"
else
  ( ulimit -s unlimited 2>/dev/null
    fail=0
    for m in Statement Short $(find MatrixIneq -name '*.lean' | sort | sed 's#/#.#g; s#\.lean$##'); do
      if lake env "$LC" "$m" >> "$OUT/leanchecker.log" 2>&1; then echo "ok   $m"; else echo "FAIL $m"; fail=1; fi
    done > "$OUT/leanchecker.summary"; exit $fail )
  if [ $? -eq 0 ]; then record "leanchecker" PASS "$(wc -l < "$OUT/leanchecker.summary") modules replayed"
  else record "leanchecker" FAIL "see $OUT/leanchecker.summary"; fi
fi

# 5. nanoda
LE="$(find_tool "${LEANEXPORT:-}" leanexport lean4export)"; ND="$(find_tool "${NANODA:-}" nanoda_bin nanoda)"
if [ -z "$LE" ] || [ -z "$ND" ]; then record "nanoda" SKIP "leanexport or nanoda_bin not found"
else
  if lake env "$LE" MatrixIneq -- MatrixIneq.mainTheorem > "$OUT/main.ndjson" 2> "$OUT/export.log"; then
    cat > "$OUT/nanoda.json" <<JSON
{"export_file_path": "$PWD/$OUT/main.ndjson", "use_stdin": false,
 "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
 "unpermitted_axiom_hard_error": false, "nat_extension": true, "string_extension": true,
 "pp_declars": ["MatrixIneq.mainTheorem", "Statement.MainTheorem"], "pp_to_stdout": true, "print_success_message": true}
JSON
    if "$ND" "$OUT/nanoda.json" > "$OUT/nanoda.log" 2>&1 && grep -q 'with no errors' "$OUT/nanoda.log"; then
      record "nanoda" PASS "$(grep 'with no errors' "$OUT/nanoda.log")"
    else record "nanoda" FAIL "see $OUT/nanoda.log"; fi
    rm -f "$OUT/main.ndjson"
  else record "nanoda" FAIL "export failed, see $OUT/export.log"; fi
fi

# 6. comparator (built into Lake since Lean v4.35; needs bubblewrap). --paranoid also runs every external
#    checker bundled with Lean (leanchecker-paranoid, lean4lean, nanoda, ...).
if ! lake comparator --help >/dev/null 2>&1; then record "comparator" SKIP "this Lake has no 'comparator' command"
elif ! command -v bwrap >/dev/null 2>&1; then record "comparator" SKIP "bubblewrap (bwrap) not installed"
else
  for c in comparator comparator-short; do
    if lake comparator --config "$c.json" ${COMPARATOR_FLAGS---paranoid} > "$OUT/$c.log" 2>&1; then
      record "$c" PASS "$(tail -1 "$OUT/$c.log")"
    else record "$c" FAIL "see $OUT/$c.log"; fi
  done
fi

echo
echo "== Verification status ($(cat lean-toolchain)) =="
rc=0
for i in "${!NAMES[@]}"; do
  printf '  %-20s %-5s %s\n' "${NAMES[$i]}" "${STATES[$i]}" "${NOTES[$i]}"
  [ "${STATES[$i]}" = FAIL ] && rc=1
done
echo
sed -n '1,2p' "$OUT/axioms.log" 2>/dev/null
exit $rc
