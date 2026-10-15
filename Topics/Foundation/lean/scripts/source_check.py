#!/usr/bin/env python3
"""Fail-closed source-level check of the handwritten mathematical Lean sources.

Scope: every `.lean` file of the two mathematical libraries
  TreeFoundations.lean, TreeAnalysis.lean and the directories
  PrimitiveTree/ TreeNumbers/ TreeFoundation/ DimensionFoundation/ TreeAnalysis/ BoundaryTopology/.
(The audit tooling in `ReleaseAudit/` and the historical reporting files in `Audit/` are not
mathematical sources and are not scanned; `ReleaseAudit/` necessarily uses `import Lean`.)

After removing comments (nested `/- ... -/` blocks and `--` line comments) and string literals,
the check fails (exit status 1) on:
  * any forbidden identifier, keyword or tactic (word-boundary match, see FORBIDDEN);
  * any decimal numeric literal;
  * any `import` that is not a project module (no Lean, Std, Mathlib, ...);
  * any mathematical source file not reachable from the two library roots by imports
    (so that the kernel-level audit, which loads the roots, sees every file).
It prints every violation with file and line number.  Exit status 0 means no violation.
Usage: `python3 scripts/source_check.py [ROOT]` (ROOT defaults to the repository; the negative
fixture script passes a temporary tree).
"""
import os
import re
import sys

ROOT = (os.path.abspath(sys.argv[1]) if len(sys.argv) > 1
        else os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DIRS = ["PrimitiveTree", "TreeNumbers", "TreeFoundation", "DimensionFoundation",
        "TreeAnalysis", "BoundaryTopology"]
ROOTS = ["TreeFoundations.lean", "TreeAnalysis.lean"]
PROJECT_PREFIXES = tuple(d + "." for d in DIRS)

FORBIDDEN = [
    # number carriers
    "Nat", "Int", "Rat", "Fin", "PNat", "UInt8", "UInt16", "UInt32", "UInt64", "USize",
    "BitVec", "Real", "Float", "OfNat", "OfScientific",
    # list numeric APIs
    "List.length", "List.range", "List.replicate", "List.get", "length", "replicate",
    # classical logic and escape hatches
    "Classical", "classical", "noncomputable", "sorry", "admit", "axiom", "unsafe",
    "partial", "native_decide", "implemented_by", "opaque", "Mathlib", "mathlib",
    # forbidden tactics / automation (`decide` is *not* listed: the project uses the term
    # `decide` = `Decidable.decide` on its own constructive decision procedures, e.g.
    # `TreeAnalysis.ApartnessStrength.gapTest`; the kernel audit checks the result)
    "simp", "simpa", "simp_all", "dsimp", "omega", "norm_num", "ring", "ring_nf",
    "linarith", "nlinarith", "aesop", "positivity", "grind", "bv_decide",
]


def strip(src: str) -> str:
    """Remove nested block comments, line comments and string literals, keeping newlines."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith('"', i):
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append("".join("\n" if c == "\n" else " " for c in src[i:j + 1]))
            i = j + 1
        elif src.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def module_of(path: str) -> str:
    return os.path.relpath(path, ROOT)[:-len(".lean")].replace(os.sep, ".")


def main() -> int:
    files = [os.path.join(ROOT, r) for r in ROOTS]
    for d in DIRS:
        for dp, _, fs in os.walk(os.path.join(ROOT, d)):
            files += [os.path.join(dp, f) for f in fs if f.endswith(".lean")]
    files = sorted(set(files))
    violations = []
    imports = {}
    word = re.compile(r"(?<![\w'!?])(" + "|".join(re.escape(w) for w in
                      sorted(FORBIDDEN, key=len, reverse=True)) + r")(?![\w'!?])")
    numlit = re.compile(r"(?<![\w'.])[0-9]+(?![\w'])")
    for f in files:
        code = strip(open(f, encoding="utf-8").read())
        mod = module_of(f)
        imports[mod] = []
        for ln, line in enumerate(code.split("\n"), 1):
            m = re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)", line)
            if m:
                imp = m.group(1)
                imports[mod].append(imp)
                if not imp.startswith(PROJECT_PREFIXES):
                    violations.append(f"{mod}:{ln}: non-project import `{imp}`")
                continue
            for w in word.finditer(line):
                violations.append(f"{mod}:{ln}: forbidden token `{w.group(1)}`")
            for w in numlit.finditer(line):
                violations.append(f"{mod}:{ln}: numeric literal `{w.group(0)}`")
    # coverage: every file reachable from the roots
    seen, todo = set(), [module_of(os.path.join(ROOT, r)) for r in ROOTS]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        todo += [i for i in imports.get(m, []) if i in imports]
    for m in sorted(imports):
        if m not in seen:
            violations.append(f"{m}: not imported (transitively) by the library roots")
    print(f"source check: {len(files)} mathematical source files scanned, "
          f"{len(seen)} reachable from the roots")
    if violations:
        print(f"SOURCE CHECK FAILED: {len(violations)} violation(s)")
        for v in violations:
            print("  " + v)
        return 1
    print("source check passed: no forbidden token, numeric literal or foreign import")
    return 0


if __name__ == "__main__":
    sys.exit(main())
