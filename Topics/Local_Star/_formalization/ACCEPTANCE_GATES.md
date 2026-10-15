# Integration gates for each completed phase

1. Exact statement inventory, including all implicit parameters, typeclass hypotheses and carrier identities.
2. Original mathematical definitions/proofs in new files; no code transfer from historical archives.
3. One-way dependency check: only `Foundation → LocalStar`, no modules imported backward.
4. Actual `lake build LocalStar` on the recorded Lean 4.28.0 toolchain; report actual command and output, not an assumed build.
5. Source policy audit (same effective mathematical-source restrictions as Foundation).
6. `#print axioms` for every new theorem designated principal; distinguish `Quot.sound`, `propext`, `Classical.choice`, new axioms, `sorryAx`.
7. Exact-rational independent small instance controls (b=1,2,3,4 where applicable): positivity, 31/27, singleton zero, Gram identity and 5-port coefficient 1/5.
8. Build on recorded immutable upstream Foundation SHA, inventory of changed paths; minimal targeted regressions.
9. Document limitations and formally unresolved items, including finite-versus-infinite boundaries and the unresolved canonical global geometry.

Do not require final release audit during every exploratory attempt. Before paper claims or integration, all relevant gates must be checked and evidence preserved. No history rewriting.
