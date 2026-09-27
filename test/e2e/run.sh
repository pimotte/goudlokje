#!/bin/sh
# End-to-end tests, on copies of the worksheets in this directory (libraries `E2EWorksheets` and
# `E2EFixtures` in the test package's lakefile). Run from anywhere: `test/e2e/run.sh`.
#
# 1. `goudlokje check` and `goudlokje update` on `Sheet.lean`.
# 2. Regression test of all findings: `update --all` on the fixtures in `fixtures/` must produce
#    exactly the `.test.json` files in `fixtures/expected/` (none for fixtures without findings),
#    and `check` must then report exactly the errors in `fixtures/expected/errors.txt` (raw Lean
#    tactics, which cannot be recorded as expected). After an intended change of behaviour,
#    regenerate these files with `e2e/run.sh --regenerate`.
set -eu
cd "$(dirname "$0")/.."
regenerate=false
[ "${1:-}" = "--regenerate" ] && regenerate=true
work=e2e/work/Worksheets
out=e2e/work/out.txt
fail() { echo "FAIL: $*"; cat "$out"; exit 1; }
goudlokje() { ../.lake/build/bin/goudlokje "$@" > "$out" 2>&1; }
olean=.lake/build/lib/lean/Worksheets/Sheet.olean

lake build goudlokje
rm -rf e2e/work
mkdir -p "$work"
cp e2e/Sheet.lean "$work/Sheet.lean"

echo "check fails on unexpected findings"
goudlokje check "$work" && fail "check passed"
grep -q '`decide` closes the goal at step 1 of exercise "shortcut"' "$out" || fail "no shortcut"
grep -q '`sorry` at step 1 of exercise "true or false"' "$out" || fail "no sorry"

echo "update --all records them"
goudlokje update --all "$work" || fail "update failed"
diff -u e2e/Sheet.expected.json "$work/Sheet.test.json" || fail "unexpected .test.json"

echo "check passes, rebuilding the worksheet since its last build failed"
goudlokje check "$work" || fail "check failed"

echo "check notices stale expectations after only .test.json changed, without rebuilding"
touch -d '2000-01-01' "$olean"
cp e2e/Sheet.stale.json "$work/Sheet.test.json"
goudlokje check "$work" || fail "check failed"
grep -q 'stale expectation: Remove the stale expected shortcut `simp` at step 2 of "shortcut"' "$out" ||
  fail "no stale warning"
[ "$(date -r "$olean" +%Y)" = 2000 ] || fail "the worksheet was rebuilt"

echo "check fails on findings that .test.json no longer expects, without rebuilding"
cp e2e/Sheet.expected.json "$work/Sheet.test.json"
sed -i '/"tactic":"decide"/d' "$work/Sheet.test.json"
goudlokje check "$work" && fail "check passed"
grep -q '`decide` closes the goal at step 1 of exercise "shortcut"' "$out" || fail "no shortcut"
[ "$(date -r "$olean" +%Y)" = 2000 ] || fail "the worksheet was rebuilt"

echo "update works without results files, without rebuilding"
rm -rf .lake/goudlokje
goudlokje update --all "$work" || fail "update failed"
diff -u e2e/Sheet.expected.json "$work/Sheet.test.json" || fail "unexpected .test.json"
[ "$(date -r "$olean" +%Y)" = 2000 ] || fail "the worksheet was rebuilt"

echo "update --all removes stale expectations and removed exercises"
cp e2e/Sheet.stale.json "$work/Sheet.test.json"
grep -v 'Fix n : ℕ' e2e/Sheet.lean | sed 's/Exercise "annotation"/Exercise "renamed"/' > "$work/Sheet.lean"
goudlokje update --all "$work" || fail "update failed"
diff -u e2e/Sheet.updated.json "$work/Sheet.test.json" || fail "unexpected .test.json"

echo "fixtures produce exactly the expected findings"
fixtures=e2e/work/Fixtures
mkdir -p "$fixtures"
cp e2e/fixtures/*.lean "$fixtures/"
goudlokje update --all "$fixtures" || fail "update failed"
if $regenerate; then
  rm -rf e2e/fixtures/expected
  mkdir -p e2e/fixtures/expected
  cp "$fixtures"/*.test.json e2e/fixtures/expected/ 2>/dev/null || true
fi
for f in e2e/fixtures/*.lean; do
  name=$(basename "$f" .lean)
  expected="e2e/fixtures/expected/$name.test.json"
  actual="$fixtures/$name.test.json"
  if [ -f "$expected" ]; then
    diff -u "$expected" "$actual" > "$out" 2>&1 || fail "findings of $name changed"
  elif [ -f "$actual" ]; then
    cp "$actual" "$out"; fail "$name has unexpected findings"
  fi
done
goudlokje check "$fixtures" && fail "check of the fixtures passed despite raw Lean tactics"
errors=e2e/work/errors.txt
grep "^error: $fixtures/" "$out" | sed "s|^error: $fixtures/||" | sort > "$errors"
$regenerate && cp "$errors" e2e/fixtures/expected/errors.txt
diff -u e2e/fixtures/expected/errors.txt "$errors" > "$out" 2>&1 || fail "errors of the fixtures changed"

echo "PASS"
