#!/usr/bin/env bash
# Controlled negative fixtures for the fail-closed audit.
#
# The fixtures are generated in a temporary directory OUTSIDE the repository, so no forbidden
# axiom, `sorry`, classical constant or `Nat` declaration is ever added to the released source
# tree.  Each negative fixture must make the audit FAIL (nonzero exit status); the positive
# control must PASS.  This script itself exits nonzero if any expectation is violated.
set -u
cd "$(dirname "$0")/.."
lake build ReleaseAudit.Command >/dev/null || { echo "cannot build ReleaseAudit.Command"; exit 2; }
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
status=0

expect() {  # expect <pass|fail> <name> <file>
  local want="$1" name="$2" file="$3"
  local out rc
  out="$(lake env lean "$file" 2>&1)"; rc=$?
  if [ "$want" = fail ] && [ $rc -ne 0 ]; then
    echo "OK   (fails as required, exit $rc): $name"
    echo "$out" | grep -m3 "FAIL-CLOSED\|forbidden\|missing\|mentions\|axiom declaration" | sed 's/^/       /'
  elif [ "$want" = pass ] && [ $rc -eq 0 ]; then
    echo "OK   (passes as required, exit 0): $name"
  else
    echo "BAD  (expected $want, got exit $rc): $name"; echo "$out" | sed 's/^/       /'
    status=1
  fi
}

hdr='import ReleaseAudit.Command'

printf '%s\naxiom fixtureBogus : False\ntheorem fixtureUsesBogus : False := fixtureBogus\n#fail_closed_audit_local\n' "$hdr" > "$TMP/NegAxiom.lean"
printf '%s\ntheorem fixtureEm (p : Prop) : p ∨ ¬ p := Classical.em p\n#fail_closed_audit_local\n' "$hdr" > "$TMP/NegClassical.lean"
printf '%s\ntheorem fixtureSorry : False := sorry\n#fail_closed_audit_local\n' "$hdr" > "$TMP/NegSorry.lean"
printf '%s\ndef fixtureNatCarrier (n : Nat) : Nat := n + 1\n#fail_closed_audit_local\n' "$hdr" > "$TMP/NegNat.lean"
printf '%s\ntheorem fixtureNative : True ∧ True := by\n  have h : (2 : Nat) + 2 = 4 := by native_decide\n  exact ⟨True.intro, True.intro⟩\n#fail_closed_audit_local\n' "$hdr" > "$TMP/NegNative.lean"
printf '%s\nopaque fixtureOpaque : Prop\n#fail_closed_audit_local\n' "$hdr" > "$TMP/NegOpaque.lean"
printf '%s\n#require_decls Nonexistent.declaration\n' "$hdr" > "$TMP/NegMissing.lean"
printf '%s\n#fail_closed_audit\n' "$hdr" > "$TMP/NegCoverage.lean"
printf '%s\ninductive FixtureUnit : Type where\n  | only : FixtureUnit\ntheorem fixtureOk (x : FixtureUnit) : x = FixtureUnit.only := by\n  cases x\n  rfl\n#fail_closed_audit_local\n' "$hdr" > "$TMP/PosControl.lean"

expect fail "user axiom"                       "$TMP/NegAxiom.lean"
expect fail "Classical.em (Classical.choice)"  "$TMP/NegClassical.lean"
expect fail "sorry (sorryAx)"                  "$TMP/NegSorry.lean"
expect fail "built-in Nat carrier"             "$TMP/NegNat.lean"
expect fail "native_decide (trust axiom)"      "$TMP/NegNative.lean"
expect fail "opaque constant"                  "$TMP/NegOpaque.lean"
expect fail "missing required declaration"     "$TMP/NegMissing.lean"
expect fail "release audit without the libraries loaded" "$TMP/NegCoverage.lean"
expect pass "positive control (inductive type + structural proof)" "$TMP/PosControl.lean"

# Source-level fixture: a temporary copy of the root files plus one bad module.
mkdir -p "$TMP/tree/PrimitiveTree"
printf 'module\n' > "$TMP/tree/TreeAnalysis.lean"
printf 'module\npublic import PrimitiveTree.Bad\n' > "$TMP/tree/TreeFoundations.lean"
printf 'module\nimport Lean\ndef bad : Nat := 3\ntheorem t : bad = bad := by simp\n' > "$TMP/tree/PrimitiveTree/Bad.lean"
out="$(python3 scripts/source_check.py "$TMP/tree" 2>&1)"; rc=$?
if [ $rc -ne 0 ]; then echo "OK   (fails as required, exit $rc): source-level fixture"; echo "$out" | sed 's/^/       /'
else echo "BAD  (source-level fixture passed)"; echo "$out"; status=1; fi

if [ $status -eq 0 ]; then echo "NEGATIVE FIXTURES: all expectations met"; else echo "NEGATIVE FIXTURES: FAILED"; fi
exit $status
