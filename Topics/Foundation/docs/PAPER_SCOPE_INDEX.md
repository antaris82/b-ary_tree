# Mathematical paper — scope index (preparation only)

**This is a contents index, not the full outline or a paper draft.** The detailed 18-section, 89-subsection outline with checked source paths and literature references is supplied in the associated `TREE_FOUNDATION_PROJECT_CHAT_HANDOFF.zip` preparation package. Import that package into this directory before drafting a manuscript.

## Intended paper sections

0. Front matter — mathematical abstract, hypotheses and carefully qualified results.
1. Introduction — established frameworks, the exact constructions, and main mathematical claims.
2. Finite words and rooted trees — root, parent/child edges, unique paths, connectedness, no cycles, finite arity, countable arity, arity embeddings.
3. Primitive unit-edge sums — finite root edge lists, path-sum/depth theorem, ray-prefix count limitations.
4. Unary path counting — natural semiring, operations/induction/order, equal-depth quotients over arbitrary nonempty alphabets.
5. Oriented path-count differences — normalized integers, ordered integral-domain properties, natural embedding.
6. Rational triple-path equivalence classes — valid triples, cross multiplication, witnesses, complete field laws, order and internal fraction-field characterization.
7. Arity-independent rational arithmetic — isomorphisms, compatibility and the exact contribution of distinct path addresses.
8. Finite child-coordinate modules — coordinate-sum map, uniform line, zero-sum kernel, symmetric bilinear form, explicit transverse bases, rank-(b−1), orthogonality and direct-sum projections.
9. Countably infinite child-coordinate limit — finite support, the countably generated zero-sum submodule, basis, compatible embeddings, and failure of the all-ones vector under standard padding.
10. Ray boundaries and prefix topology — compatible prefixes, noncommutation with arity union, clopen cylinders, connectedness, isolated points, local compactness, precise chart conditions and noncanonical numerical encodings.
11. Rooted-tree automorphisms — levelwise permutations, ray transitivity, invariant-map constancy and formally refuted levelwise classification.
12. Constructive rational Cauchy quotient — modulated sequences, equivalence, regularization, quotient ring, constructive order, apartness and separated inversion.
13. Constructive convergence and completeness scope — rational density, diagonal limits with tracking data, finite algebraic-expression closure, conditional choice and supremum theorems.
14. Logical strength — Markov principle, LPO, WLPO and precisely qualified implications for stronger inverse/order/completeness claims.
15. Structural comparisons and nonidentifications — algebraic rank versus arity-independent numbers, prefix counts versus ray identity, native boundary versus Cauchy quotient.
16. Open mathematical problems — universal properties, unrestricted completeness, classical order/inverse/supremum principles, ambient-space compatibility, topological conditions.
17. Conclusion — actual proved statements and remaining conditions, without extrapolation.

## Principal mathematical references

- Serre, *Trees*: https://doi.org/10.1007/978-3-642-61856-7
- Lyons–Peres, *Probability on Trees and Networks*: https://rdlyons.pages.iu.edu/prbtree/prbtree.html
- Kechris, *Classical Descriptive Set Theory*: https://doi.org/10.1007/978-1-4612-4190-4
- Axler, *Linear Algebra Done Right*, 4th ed.: https://doi.org/10.1007/978-3-031-41026-0
- Bass et al., *Cyclic Renormalization and Automorphism Groups of Rooted Trees*: https://doi.org/10.1007/BFb0096321
- Bishop–Bridges, *Constructive Analysis*: https://doi.org/10.1007/978-3-642-61667-9
- Bridges–Richman, *Varieties of Constructive Mathematics*: https://doi.org/10.1017/CBO9780511565663
- Lubarsky, *On the Cauchy completeness of the constructive Cauchy reals*: https://doi.org/10.1002/malq.200710007
- Gilbert, *Formalising Real Numbers in Homotopy Type Theory*: https://arxiv.org/abs/1610.05072

## Lean module families (after importing the frozen snapshot)

`PrimitiveTree/`, `TreeFoundation/`, `TreeNumbers/`, `DimensionFoundation/`, `BoundaryTopology/`, `TreeAnalysis/`.

**Important:** Do not produce a code-review narrative. Write a standard mathematical paper with independently intelligible definitions and proofs. State extra hypotheses directly in theorem statements. Lean name/signature correspondence belongs in supplementary verification materials. The final Task-5 source in the package uses Lean 4.28.0; the Aristotle project page is https://aristotle.harmonic.fun/projects/db97653b-b468-41a1-97fd-7eb835c2087d .