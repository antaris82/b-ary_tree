# Verification and scope status

- Existing Foundation: available on GitHub with its own reported release verification; its frozen source was developed on Lean 4.28.0. Upstream sources remain untouched.
- Local_Star GitHub scaffold: package metadata, documentation and import-only `LocalStar.lean`; **no new mathematical theorem declarations**.
- The described 31/27 exact arithmetic and resistance-Gram checks are independent Python diagnostics, **not** Lean kernel proofs.
- Positive-semidefinite DtN, positive-definite grounded energy, and unit resistance Gram: established mathematical targets, not yet new-topic formal results.
- Compositions and boundary limits: mathematical program, proof gaps remain.
- `lake build LocalStar`, source policy check of new formal code, `#print axioms`: **not executed in this upload step**. Do not label the new package green without running them.

See `../_formalization/ACCEPTANCE_GATES.md`.
