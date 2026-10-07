#!/bin/bash
# Integrated supplement checks for r65. Run from anywhere; needs the pinned
# toolchain and dependencies of the archive (lean-toolchain, lake-manifest.json).
# On a 2-core machine the whole script takes about a quarter of an hour once Mathlib is built.
#
# Every step stops the script if it fails. At the end the summary lines of all steps are
# compared with audit-claude/expected-summary.txt, so that the numbers quoted in
# AUDIT_CLAUDE.md are checked and not only printed.
#
#   bash audit-claude/check.sh            run all checks and compare the summary
#   bash audit-claude/check.sh --record   run all checks and overwrite expected-summary.txt
#                                         (after a deliberate, reviewed change).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
summary="$tmp/summary.txt"
: > "$summary"
supplement="R56Audit.lean $(ls R56Audit/*.lean)"
nsupp=$(echo $supplement | wc -w | tr -d '[:space:]')
lean="lake env lean -DautoImplicit=false -DwarningAsError=true"

echo "== pinned integrated supplement sources"
if command -v sha256sum > /dev/null; then sha="sha256sum"; else sha="shasum -a 256"; fi
$sha -c audit-claude/supplement.sha256 > "$tmp/sha.out" 2>&1 \
  || { cat "$tmp/sha.out"; exit 1; }

echo "== source scan (library and supplement must be clean; scripts contain meta code)"
python3 -I audit-claude/scan.py . | tee "$tmp/scan.out"
grep -E "^(== supplement:|SCAN)" "$tmp/scan.out" >> "$summary"

echo "== the statement gates are the statements of the sources"
python3 -I audit-claude/mkgates.py audit-claude/Gates.template R56Audit "$tmp/Gates.lean" | sed 's# to .*##' | tee -a "$summary"
cmp "$tmp/Gates.lean" audit-claude/Gates.lean
echo "audit-claude/Gates.lean is up to date"

echo "== build: archive (58 modules) and supplement ($nsupp modules)"
lake build Oscillation R56Audit | tail -1

echo "== supplement: every module again, with the strict options; no message allowed"
for f in $supplement; do
  lake env lean -DautoImplicit=false -Dlinter.unusedSectionVars=true \
    -Dlinter.unusedVariables=true -Dlinter.unusedSimpArgs=true "$f" > "$tmp/strict.out" 2>&1 \
    || { cat "$tmp/strict.out"; echo "FAILED: $f"; exit 1; }
  if [ -s "$tmp/strict.out" ]; then cat "$tmp/strict.out"; echo "MESSAGES: $f"; exit 1; fi
done
echo "STRICT $nsupp modules, no error, no warning" | tee -a "$summary"

echo "== supplement: what the compiled modules add to Lean (read as data, not imported)"
$lean audit-claude/OleanCheck.lean | tee -a "$summary"

echo "== supplement: kinds, axioms by walking the terms, attributes, names, name clashes"
$lean audit-claude/SupplementAudit.lean | tee -a "$summary"

echo "== archive: kinds of constants, axioms of every constant, reading lists"
lake env lean -DautoImplicit=false audit-claude/ArchiveAudit.lean > "$tmp/archive.out"
grep -E "^(KIND|BAD|SUMMARY|READING|CLOSURE)" "$tmp/archive.out"
# the one flagged constant is the unsafe auxiliary that the compiler generates for the
# recursive definition `Riesz.Moments.SampleSpace`; no constant refers to it
if [ "$(grep '^BAD' "$tmp/archive.out")" != "BAD partial Riesz.Moments.SampleSpace._unsafe_rec" ]; then
  echo "unexpected BAD lines"; exit 1
fi

echo "== archive: what the archive's main theorem depends on"
lake env lean -DautoImplicit=false audit-claude/MainTheoremClosure.lean

echo "== supplement: what its results use of the archive"
$lean audit-claude/Closure.lean | tee "$tmp/closure.out"
grep -E "^(MODULES|ROOT)" "$tmp/closure.out" >> "$summary"

echo "== supplement: statement gates, axioms, route of the proof, reading list"
$lean audit-claude/Gates.lean | tee -a "$summary"
echo "GATES all examples accepted" | tee -a "$summary"

echo "== supplement: the gates reject changed statements"
python3 -I audit-claude/mutants.py write audit-claude/Gates.lean "$tmp/Mutants.lean"
lake env lean -DautoImplicit=false "$tmp/Mutants.lean" > "$tmp/mutants.log" 2>&1 || true
python3 -I audit-claude/mutants.py check "$tmp/Mutants.lean" "$tmp/mutants.log" | tee -a "$summary"

echo "== supplement: kernel replay"
# One module at a time. (The root module `R56Audit` declares nothing; passing its name would
# replay every module below it in parallel, which needs several gigabytes of memory.)
count=0
for f in R56Audit/*.lean; do
  m="$(echo "${f%.lean}" | tr / .)"
  lake env leanchecker "$m"
  echo "replayed $m"
  count=$((count + 1))
done
echo "REPLAY $count modules" | tee -a "$summary"

echo "== the summary lines are the expected ones"
if [ "${1:-}" = "--record" ]; then
  cp "$summary" audit-claude/expected-summary.txt
  echo "recorded audit-claude/expected-summary.txt"
else
  diff "$summary" audit-claude/expected-summary.txt
  echo "$(wc -l < "$summary") summary lines agree with audit-claude/expected-summary.txt"
fi
echo "ALL CHECKS PASSED"
