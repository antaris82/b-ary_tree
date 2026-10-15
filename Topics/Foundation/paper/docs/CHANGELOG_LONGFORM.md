> **Historical document:** This file describes an earlier editorial stage, not the current 18-section PDF. The 89 mathematical treatments are now inline, and Appendix B now denotes formal verification. Use the current `main.tex`, `paper/README.md`, and automatically regenerated navigation in `docs/scope_89.csv` for the released state.

# Long-form mathematical revision — change log

## What was requested
Expand the 26-page revised Task--06 manuscript into a self-contained mathematical long form, completing the formerly abbreviated auxiliary proof discussions, and cover all 89 subsections of the original mathematical outline without upgrading any statement beyond its Lean prerequisites.

## What changed in the mathematical exposition

The original 17-section theorem-led main body remains intact. The newly included Appendix B provides 89 individually labeled mathematical treatments. The most substantial new proofs and calculations are:

- Complete finite-word edge-cut acyclicity and unique path details; finite child-index enumeration.
- Auxiliary induction proofs for unary recursion, multiplication and order cancellation, including congruence for equal-depth quotient operations.
- Explicit arithmetic of normalized signed pairs, equivalence of raw fractions and representative independence of their operations.
- The two-letter triple witness and the reason unary triples omit both zero and minus one (the latter clearly not described as a newly kernel-checked theorem).
- The coordinate basis and transverse free basis, finite-dimensional direct sum, Task--06 bilinearity, complete complementary projection algebra, and orthogonal splitting.
- The finitely supported countable basis, padded inclusions and the precise failure of uniform-line compatibility.
- Prefix cylinders, connectedness, non-isolated points, countable noncompactness, and precise conditions of chart obstructions.
- Ray-transitive levelwise automorphisms and the subtree-supported counterexample to the levelwise completeness conjecture.
- Modulated Cauchy equivalence, quotient operations, positivity and apartness, the *source-exact tail resampling* for inversion with modulus `j+2k`.
- The *source-exact single rational sequence* `ApproxData` and its modulus `max(ν(k+2),M(k+2))`; completeness equivalence using one representative of a single limit.
- The two-stage `ChoiceNN` selection of dyadic numerator pairs; explicit dyadic cuts establishing LPO/WLPO lower bounds.
- The actual hypotheses behind constructive suprema and tracked uniformly continuous extensions.

## Verification boundary

No Lean source changed. No Lean kernel binary is installed in this documentation environment. The unchanged Task--06 release transcript and user-provided independent reviewer report remain the evidence for kernel verification. PDF compilation and all 89 topic navigation links were independently checked here. The extension introduces explanatory derived arguments, not extra named Lean declarations. No independence or general impossibility theorem is inferred from unproved stronger claims.
