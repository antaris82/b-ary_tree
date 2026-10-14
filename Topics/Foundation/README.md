# Foundation — rooted trees, path arithmetic, and algebraic child-coordinate spaces

This directory is reserved for the mathematically complete Task-5 foundation and the preparation of a mathematical paper. It is **not** itself a finished paper.

## Mathematical scope

Finite words and rooted trees (finite and countably infinite arity); unit-edge path sums; natural-number path counts and equal-depth quotients; signed differences and rational triple-path classes; ordered-field comparisons; finite child-coordinate spaces with a rank-one uniform subspace, a rank-(b−1) zero-sum subspace, and explicit direct-sum projections; countably infinite finite-support transverse modules; infinite rays, cylinder topology, and rooted-tree automorphisms; rational Cauchy quotients and the exact constructive scope of their properties.

## Planned layout

- `lean/`: frozen Lean 4.28.0 source snapshot (to import from the final Task-5/Q14-repaired archive).
- `docs/PAPER_OUTLINE_AND_SOURCE_MAP.md`: complete mathematical contents, primary sources, and theorem-level provenance.
- `docs/PROJECT_CHAT_HANDOFF.md`: instructions for the future paper-drafting project.
- `docs/references.bib`: verified bibliography before submission.
- `docs/SOURCE_MANIFEST_SHA256.txt`: source inventory and checksums.

**Current repository status:** organizational directory initialized. The unpacked source and complete documentation have been prepared in a separate downloadable project package, but are **not yet committed here**. Do not treat the planned paths as existing files until import is complete.

## Interpretation boundaries

The transverse dimension b−1 is an algebraic rank of a child-coordinate module, not the topological dimension of the tree or its boundary. The native ray boundary is not proved canonically identical to the Cauchy quotient. The constructed Cauchy quotient has unconditional ring and constructive order/apartness properties; full classical field and completeness claims require exactly stated additional premises.

Frozen Aristotle project: https://aristotle.harmonic.fun/projects/db97653b-b468-41a1-97fd-7eb835c2087d

The paper is to be a **mathematical exposition with proofs**, not a Lean review or development log.