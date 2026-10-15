# OFFLINE HANDOFF — READ THIS FIRST (English)

## What is in this archive?
This is a fixed Git source snapshot of `antaris82/b-ary_tree`. It includes **both**:
- `Topics/Foundation/` — the complete, existing mathematical Foundation, **read-only**.
- `Topics/Local_Star/` — the new topic scaffold, current Task 01, mathematics notes and tests, **the only editable topic**.

The parent archive directory is a GitHub-generated snapshot name. Relative paths below refer to the directory containing `Topics/`.

## Highest-priority source boundary
**Never alter `Topics/Foundation/`, not even to fix a build.** No edits, new files, reorganizations, rebuilt documentation, changes in imports, toolchains, validators, tests, or dependency version. All hand-authored changes must be confined to `Topics/Local_Star/`. The existing one-way source dependency is `Foundation → Local_Star`; imports from Foundation are allowed.

No previous `FloatingStar` Lean code is included or allowed. Historical mathematical outcomes in `Local_Star/docs` are goals/checks, **not reusable source** or newly verified theorems.

## Required mathematics
Use only Foundation's existing intrinsic numerical carriers:
`TreeN` (N_T), `TreeZ` (Z_T), and `QStar = TreeQOmega` (Q_T) for all scalar computations. Reuse its finite-child arithmetic and sums; no `Nat`, `Int`, `Rat`, `Fin`, foreign numerals, Mathlib or `Classical` in new mathematical Lean sources.

The Task 01 requirements are authoritative:
`Topics/Local_Star/_formalization/ARISTOTLE_TASK_01.md`

For the research roadmap see:
`Topics/Local_Star/_formalization/MASTER_PLAN.md`

For positivity, semidefinite energy, and the resistance Gram identity:
`Topics/Local_Star/docs/METRIC_FORMS_AND_POSITIVITY.md`

## Local build
Use the existing local package configuration in `Topics/Local_Star/lean/lakefile.toml`, which points to `../../Foundation/lean`. With Lean 4.28.0 installed:

```sh
cd Topics/Local_Star/lean
lake build LocalStar
```

Do not report successful builds or kernel checks without actual command output. If the dependency itself fails, document the error and keep Foundation untouched.

## Required return
Deliver all created and changed **Local_Star** source files, a precise completed/failed goal inventory, theorem signatures, relevant `#print axioms`, actual build/source-check logs, and a verification that the supplied Foundation files were not edited. No network access is needed.
