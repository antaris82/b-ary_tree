# Mathematical scope: proved, conditional, refuted, and open — Task--06

**Frozen Lean source:** `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`; Lean 4.28.0. This is a scope register, not a claim of metatheoretic independence.

## Proven under their stated hypotheses

- Constructed unary natural semiring and order; normalized signed integers; positive-denominator fraction field; the **transported** rational structure on admissible triple classes under `[TwoLetters α]` and the fraction comparison.
- Explicit finite zero-sum bases, line and transverse ranks, direct sum for **positive arity**, BilinearForm and ProjectionLaws (complementary idempotents, images, kernels, bilinear splitting); countable finite-support transverse basis.
- Specific zero-padding obstruction for the finite uniform vectors, and `RayOmega.union_proper` for finite-arity ray subboundaries.
- Clopen cylinders, prefix separation under exact hypotheses, no isolated rays for nontrivial arity, and failure of cylinder compactness / local compactness in the omega boundary's implemented predicates.
- Ray transitivity under levelwise-permutation automorphisms; invariant maps under this action are constant.
- The modulated Cauchy quotient ring, rational embedding, apartness-based inversion, rational density, tracked convergence, given-data least upper bounds, and exact logical equivalences with the principles defined in the source.

## Conditional theorems, not unconditional principles

- `TreeR.UnrestrictedCompleteness K ↔ TreeR.CauchyApprox K` for real sequences **with a given Cauchy modulus**; completeness follows from extra `ChoiceNN` in the proved direction. `ChoiceNN` is a proposition, not a kernel axiom used unconditionally.
- `TreeR.ModulusFreeCompleteness` under additional assumptions, especially choice/modulus selection; no unconditional modulus-free theorem.
- An ordinary inverse for every real `x ≠ 0` is equivalent to the Boolean form of MP in the source; apartness-based inversion is already unconditional under the declared `[TOField K]`.
- Real trichotomy and zero-or-apartness are equivalent to LPO; decidable zero to WLPO; these logical principles are not proved unconditionally.
- `no_chart_into_real` assumes `TreeR.IntervalsConnected K`; no unconditional general positive-dimensional manifold exclusion is inferred.

## Formally refuted (in the precise formulation)

- Every rooted-tree automorphism is globally levelwise: refuted by a subtree-supported automorphism (`levelwise_converse_false`).
- Universal continuity of the finite uniform lines along zero-padding: the claimed compatibility fails for the specific inclusion (`padSucc_u_not_inL`), and the all-ones vector is not finitely supported (`allOnes_not_finSupp`). Do not globalize this obstruction to arbitrary ambient spaces.
- Raw prefix path-count observations produce a non-Cauchy sequence independent of the ray; this does not rule out different ray encodings.

## Open / not formalized without extra hypotheses

- Unconditional general Cauchy completeness and arbitrary modulus selection; ordinary nonzero inversion without MP; trichotomy without LPO; unrestricted least-upper-bound principle for all inhabited bounded subsets; general bounded monotone convergence. The source establishes some one-way lower bounds, not their converses or independence.
- Universal properties beyond the proved specialized fraction and extension maps; finite-alphabet boundary compactness in the implemented predicate; general manifold-chart classification; classification of the entire tree automorphism group.
- A canonical boundary–numerical completion homeomorphism or compatible identification; an alternative longitudinal omega ambient space with precisely stated injections, topology and limit notion.
- Positivity of the finite bilinear form as a general `TField` theorem, or any claim of geometric/topological/physical dimension equal to `b-1`.

## Informal mathematical consequence not separately Lean-formalized

For a unary alphabet, the admissible triples represent neither `0` nor `-1`, because pairwise distinct unary words have distinct lengths and would violate `P₁≠P₂` or `P₁≠P₃` respectively. The `0` case is a named Lean theorem; the `-1` case is derived in the manuscript. The **exact image characterization** as all fractions except `0` and `-1` is not claimed as a formal theorem. See `LEAN_PROOF_REQUIREMENTS.md`.

## Exposition, reproducibility, and literature boundaries

- All 25 main manuscript claims are crosswalked. The historical 45-item and 252-reference registers are distinct supplement layers; neither supersedes the current main manuscript.
- The originally uploaded source archive and release log are included in `evidence/`. Task--05 per-declaration logs are supplemental historical data, not newly executed Task--06 checks.
- A reviewer reports a locally reproduced Kernel check; the paper authoring environment performed a source/hash audit but not a Lean kernel rebuild. These are separate evidence levels.
- Some auxiliary calculations in the 89-subsection source map remain compressed in the compact main manuscript. A paper is not an independent peer review or a blanket proof of stronger classical real axioms.
