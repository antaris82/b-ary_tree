# Systematic mathematical proof-expansion audit — Task 06

## Frozen source and deliverable

- Task--06 source fingerprint: `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`.
- Lean version in the frozen archive: 4.28.0.
- Mathematical manuscript: `main.tex` including `extended_proof_details.tex`.
- All **89** numbered topics of the original scope have one distinct Appendix B subsection, with labels `supp:1-1` through `supp:17-2`; see the generated `scope_89.md` and `scope_89.csv` for names, original code paths and actual PDF page numbers.
- The appendix is arranged by mathematical dependence, not Task chronology. Definitions, limitations and open problems are not presented as proof obligations.

## Explicit mathematical proof obligations addressed

| Area | Strengthened arguments | Important condition retained |
|---|---|---|
| Rooted words | List-constructor uniqueness, directed root paths, edge-cut proof of undirected acyclicity, finite arity enumeration and its injections | Infinite depth needs an inhabitant of the alphabet |
| Path sums and naturals | Actual edge-fold concatenation, structural induction and recursion, order cancellation, quotient congruence | Depth quotient isomorphic to unary naturals only for inhabited alphabets |
| Normalized integers | Pair-equivalence transitivity, uniqueness of normal forms, polynomial operations, signs and zero-divisor reasoning | Integer carrier is a normal-form structure, not the host quotient type |
| Rational values | Positive-denominator transitivity, both-variable congruence, witness construction, order invariance, operation transport | `TwoLetters` for full triple representation; unary value -1 is an *informal* deduction |
| Finite dimension | Coordinate basis, sum kernel, transverse basis, characteristic-zero coefficient, full projector identities, symmetric bilinear splitting | `b>0`; no topological-dimensional inference |
| Countable dimension | Finite-support sums, explicit countable algebraic basis, padding preservation, uniform-line incompatibility | Only the specified embeddings and finite-support ambient module |
| Prefix topology | Clopen cylinder arguments, separation with explicit disagreement, connectedness, noncompactness cover and local-compactness deduction | Conditional interval-connectedness for real-line chart obstruction |
| Automorphisms | Explicit levelwise inverses, transitive action, invariant constancy, address-dependent subtree involution | The full automorphism group remains unclassified |
| Constructive completion | Modulus and regularization, quotient congruence, nonnegativity quantifiers, dyadic cotransitivity, explicit inverse modulus `j+2k`, product tail equivalence | `TOField` includes decidable rational order and explicit Archimedean bound |
| Completeness | Exact one-sequence `ApproxData` theorem with rational modulus `max(ν(k+2), M(k+2))`, limit threshold `max(λ(k+1),M(k+1))`, inversion of UC to CA using one limit representative | Modulated ≠ modulus-free; no automatic representative selection |
| Choice and logics | Explicit dyadic numerator-pair selection via two `ChoiceNN` applications, Boolean gap test, numerical 1/4–1/2–1/8 cuts for WLPO/LPO lower bounds | MP/LPO/WLPO/ChoiceNN are not assumed unconditionally |
| Suprema | SupData construction, regular bounds, upper and least properties, finite and tracked-monotone cases | No unconditional supremum for arbitrary bounded inhabited predicates |

## Proof-versus-claim mapping rules

1. Every named principal result remains supported by the prior Task--06 declaration correspondence and the supplied successful release audit. This document does **not** assert that the new manuscript prose was separately Lean-kernel checked.
2. Routine arithmetic re-associations (for example regrouping three finite sums) are abbreviated where they follow directly from already established ring laws. Nontrivial choices, witnesses, diagonal schedules and dyadic bounds are explicitly displayed.
3. Explanatory consequences not established as separate kernel declarations are not represented as named Lean theorems: e.g. the unary exclusion of -1, mathematical iteration of successor alphabet inclusions and elementary corollaries of the projection identities.
4. Formal sources do not prove all conceivable stronger principles. For claims such as unconditional general Cauchy completeness, bare-nonzero inversion, unrestricted LUB or a universal boundary--real identification the manuscript explicitly leaves the corresponding conditions open.
5. The original archive has not been edited. New auxiliary mathematical exposition may contain human-readable derivations that are not executable Lean code; it has been checked against relevant source definitions, but a full independent external referee audit remains outstanding.

## What is and is not closed

**Closed as exposition:** all 89 planned mathematical topics have individual, referenceable treatment (not 89 independent Lean theorems), including proof steps for the previously sketched topics, and the substantial constructive error estimates are spelled out. The original 26-page compact version is retained as the principal text; the long-form mathematical appendix is added without erasing its original theorem statements.

**Not a new theorem:** this writing expansion does not add or change any Lean proof. A line-by-line restatement of every definitional rewrite made by the Lean tactics is neither claimed nor needed for a mathematical paper when the arithmetic steps are explicitly reconstructible.

**Formal proof gap decision:** no new Lean theorem is required for the principal claims at their existing qualified scope. Optional declarative upgrades appear in `LEAN_PROOF_REQUIREMENTS.md`, and none has been compiled here.
