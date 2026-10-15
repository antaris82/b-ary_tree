#!/usr/bin/env bash
# Release verification.  Every step is mandatory; the script stops with a nonzero exit status
# at the first failing step (set -e), so a successful exit certifies all steps.
#
#   1. record toolchain, manifest and source fingerprint
#   2. build the two mathematical libraries
#   3. source-level fail-closed check            (scripts/source_check.py)
#   4. kernel-level fail-closed audit             (ReleaseAudit/Run.lean: #fail_closed_audit,
#                                                   #require_decls), built AND re-run directly
#   5. informational axiom report                 (ReleaseAudit/Report.lean)
#   6. negative fixtures must fail, positive control must pass (scripts/negative_fixtures.sh)
#   7. leanchecker (the toolchain's lean4checker) replay, if the binary is available
set -euo pipefail
cd "$(dirname "$0")/.."
step() { echo; echo "=== $* ==="; }

step "1. toolchain, manifest, fingerprint"
echo "lean-toolchain: $(cat lean-toolchain)"
lean --version
lake --version
echo "lake-manifest.json:"; cat lake-manifest.json
echo "git commit: $(git rev-parse HEAD 2>/dev/null || echo n/a)"
SRC=$( (ls TreeFoundations.lean TreeAnalysis.lean lakefile.toml lean-toolchain lake-manifest.json; \
        find PrimitiveTree TreeNumbers TreeFoundation DimensionFoundation TreeAnalysis \
             BoundaryTopology ReleaseAudit scripts -type f \( -name '*.lean' -o -name '*.py' -o -name '*.sh' \)) | LC_ALL=C sort)
echo "source files: $(echo "$SRC" | wc -l)"
echo "source fingerprint (sha256 of sorted per-file sha256 list): $(echo "$SRC" | xargs sha256sum | sha256sum | cut -d' ' -f1)"

step "2. build mathematical libraries"
lake build TreeFoundations TreeAnalysis 2>&1 | tail -n 3

step "3. source-level check"
python3 scripts/source_check.py

step "4. kernel-level fail-closed audit"
lake build ReleaseAudit 2>&1 | tail -n 3
lake env lean ReleaseAudit/Run.lean

step "5. axiom report (informational)"
lake env lean ReleaseAudit/Report.lean

step "6. negative fixtures"
./scripts/negative_fixtures.sh

step "7. leanchecker"
LC="$(command -v leanchecker || true)"
if [ -z "$LC" ]; then
  TC="$(dirname "$(command -v lean)")"
  for c in "$TC/leanchecker" "$HOME/.elan/toolchains/"*"/bin/leanchecker"; do
    [ -x "$c" ] && LC="$c" && break
  done
fi
if [ -n "$LC" ] && [ -x "$LC" ]; then
  echo "using $LC"
  for m in TreeFoundations TreeAnalysis; do
    echo "leanchecker --fresh $m"; lake env "$LC" --fresh "$m"; echo "  ok (exit $?)"
  done
  for p in PrimitiveTree TreeNumbers TreeFoundation DimensionFoundation TreeAnalysis BoundaryTopology ReleaseAudit; do
    echo "leanchecker $p (replay every module with this prefix)"; lake env "$LC" "$p"; echo "  ok (exit $?)"
  done
else
  echo "leanchecker NOT AVAILABLE: step skipped (no passing check is claimed)"
fi

echo; echo "RELEASE VERIFICATION PASSED"
