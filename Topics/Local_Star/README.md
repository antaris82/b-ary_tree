# Local_Star — local star networks and effective resistance geometry

**Status:** Initial repository scaffold for mathematical formalization. No new mathematical theorems are claimed as Lean-verified.
**Upstream:** [Foundation](../Foundation/README.md), unchanged. The permitted dependency is `Foundation → Local_Star` only.
**Toolchain:** Lean 4.28.0 (the exact Foundation toolchain).

## Scope
Construct outward local stars of the infinite rooted finite-word tree using the existing Foundation carriers, global word addresses, path sums, and rational arithmetic. Study their node overlaps, unit-conductance network law, electrical measurement of primitive unit resistance, local Dirichlet-to-Neumann (DtN) families, precise positive-semidefinite and positive-definite forms, the **identity resistance Gram matrix**, simplex geometry, composition of overlapping blocks, and controlled finite-depth boundary limits.

Unit *path count* already belongs to Foundation; **unit electrical conductance is an explicit new constitutive definition**. A measured unit two-terminal resistance is then a proof obligation, not an assumption about physical Ohms.

## Research limits
This topic contains geometrical rank classifications and mathematically qualified candidate arity-selection principles, but no Clifford/spin/quaternion/Lorentz analyses or independent number systems. Never identify native infinite ray ends with resistance-metric completion without a proof.

## Navigation
- [Mathematical scope](docs/MATHEMATICAL_SCOPE.md)
- [PSD, PD and identity metric](docs/METRIC_FORMS_AND_POSITIVITY.md)
- [Boundary census](docs/DTN_CENSUS.md)
- [Composition and infinite boundaries](docs/COMPOSITION_AND_BOUNDARY.md)
- [Foundation contracts](docs/FOUNDATION_INTERFACES.md)
- [Formalization master plan](_formalization/MASTER_PLAN.md)
- [Aristotle task 01](_formalization/ARISTOTLE_TASK_01.md)
- [Open questions](docs/OPEN_QUESTIONS.md)

## Implementation
All new mathematical Lean sources must be written from scratch, using **only Foundation's existing source definitions as imports**. Historical `FloatingStar` sources and archive are read-only mathematical evidence, never reusable source. The import-only Lean entry point is not a theorem claim. A build and `#print axioms` audit are required before any formal-result status is assigned.
