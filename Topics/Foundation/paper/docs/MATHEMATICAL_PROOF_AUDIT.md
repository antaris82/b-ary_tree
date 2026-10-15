# Task--6 mathematical paper: critical auxiliary-proof audit

**Primary source:** frozen `output-final_aristotle` with SHA-256 source fingerprint `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e` (Lean 4.28.0). **Review date:** 15 October 2026.

## Scope and evidence status

- The source archive and manuscript were inspected directly in this review. The supplied Task--6 release transcript **reports** a successful 67-job build, 64 mathematical modules, 3,014 audited constants and permitted transitive axioms confined to `Quot.sound` and `propext`.
- A new Lean 4.28.0 kernel run was **not** performed in this writing environment. The new text edits and derived mathematical arguments were checked by hand against the source definitions, not kernel-checked as new Lean propositions.
- The source contains proofs of all 45 previously selected central claims and the newly added Task--6 bilinear/projection laws under their stated assumptions. Nothing here claims that the manuscript's thousands of prose-level inferences have each separately been proven in Lean.

## Claim-by-claim mathematical spot audit

| No. | Paper claim / proof obligation | Primary Lean source | Review finding |
|---:|---|---|---|
| 1 | Uniqueness of directed root-edge path, not arbitrary walks | `PrimitiveTree/FiniteWords.lean` | Induction on the unique immediate parent; exact scope retained. |
| 2 | Sum of unit edges equals depth | `PrimitiveTree/RootEdges.lean` | Structural recursion on edge list; no primitive vertex label substituted. |
| 3 | Natural semiring from unary words and additive order | `TreeNumbers/PathNaturals.lean`, `PathOrder.lean` | Constructed via list recursion; prior detailed paper still compresses some routine inductions. |
| 4 | Integer pair equivalence, normal form, no zero divisors | `TreeNumbers/PathIntegers.lean` | Source law checked; normal-form proof uses unary cancellation, not subtraction in naturals. |
| 5 | Fraction relation equivalence and cancellation | `TreeNumbers/PathFractions.lean` | Explicit cross-product cancellation and positivity maintained. |
| 6 | Fraction addition/product two-variable congruence | `TreeNumbers/PathFractions.lean` | Algebraic identities expanded; additional proof details in manuscript appendix. |
| 7 | Triple representation using two letters | `TreeNumbers/PathTriples.lean` | Word patterns preserve pairwise distinctness and target numerator/denominator; unary obstruction limited to specified triples. |
| 8 | Ordered-field isomorphism and arity independence | `TreeAnalysis/FractionCharacterization.lean`, `TreeNumbers/RationalArityIndependence.lean` | Composites of explicit quotient maps; no identification of individual tree words claimed. |
| 9 | Finite rank `1`, `b-1` and direct sum | `DimensionFoundation/TransverseBasis.lean` | Explicit independent/spanning coordinates; `b>0`, `[TField K]`. |
| 10 | Bilinearity, complements, kernels and images | `DimensionFoundation/BilinearForm.lean`, `ProjectionLaws.lean` | Task--6 theorems already proved; no `InnerProductSpace` claim. |
| 11 | Countable basis and uniform obstruction | `DimensionFoundation/OmegaFiniteSupport.lean`, `BoundaryLongitudinal.lean` | Only finite-support, zero-padding setting; no universal no-go theorem. |
| 12 | Clopen prefix cylinders, noncompactness | `BoundaryTopology/PrefixTopology.lean`, `TopologicalObstructions.lean` | Explicit next-letter cover checked. Local compactness argument expanded using `compact_cyl_of_sub`. |
| 13 | Ray transitivity, invariant constants, subtree counterexample | `TreeFoundation/RayAutomorphism.lean`, `AutomorphismCounterexample.lean` | Assumptions distinguished; levelwise classification **refuted**. |
| 14 | Modulated sequence equivalence and regularization | `TreeAnalysis/CauchyData.lean` | Dyadic `k+1` transitivity and nondecreasing resampling schedule checked. |
| 15 | Cauchy product modulus and quotient congruence | `TreeAnalysis/CauchyOps.lean`, `RealQuotient.lean` | Shifted-modulus calculation now recorded explicitly in Appendix A; bounding tails required. |
| 16 | Approximate nonnegativity and apartness tightness | `TreeAnalysis/SeqOrder.lean`, `RealOrderApartness.lean` | Definition and representative transfer expanded. Uses established negated-strict ↔ approximate-nonnegative lemma; no trichotomy. |
| 17 | Strict cotransitivity | `TreeAnalysis/RealOrderApartness.lean`, `lt_cotrans` | Reconstructed rational dichotomy at common precision `k+3`, gap `ε_(k+2)` in either branch; included in main proof. |
| 18 | Rational density | `TreeAnalysis/RealOrderApartness.lean`, `exists_rat_between` | Explicit witness `a(n0)+ε_(k+1)` at precision `k+2` now included. |
| 19 | Inversion only under apartness | `TreeAnalysis/RealOrderApartness.lean`, `ApartnessStrength.lean` | Reciprocal modulus and delayed sampling checked; ordinary non-equality is **not** substituted. |
| 20 | Tracked diagonal theorem | `TreeAnalysis/CompletenessStrength.lean` | `λ(k)=max(ν(k+2),M(k+2))` and three-error bound checked; no arbitrary representative selection. |
| 21 | Modulated completeness ↔ Cauchy approximation | `TreeAnalysis/LiftingPrinciples.lean` | Both implications mapped, explicit `RCauchyMod`; neither side asserted unconditionally. |
| 22 | SupData LUB, finite / monotone cases | `TreeAnalysis/SupremumScope.lean` | Verified upper/near-attainment definition, regular `u_k`, conditional monotone data. No blanket LUB. |
| 23 | Uniformly continuous extension | `TreeAnalysis/CompletionCharacterization.lean` | Requires `UCMod`; uniqueness relative to `RatSeqContinuous`, not arbitrary metric-space universal property. |
| 24 | MP, LPO, WLPO and one-way lower bounds | `TreeAnalysis/ApartnessStrength.lean`, `FoundationsClosure.lean`, `SupremumScope.lean` | All are explicit equivalences/implications with `[TOField K]`; no unconditional constructive proof of principles. |

## Source-preserving corrections made

1. In the order section the meaning of `SeqPos` and `SeqNonneg` is now defined by precise quantifiers, with explicit representative-transfer errors.
2. The cotransitivity proof has a specified rational decision index and exact dyadic margin, as in `TreeR.lt_cotrans`.
3. The strict rational-density claim has an explicit source-matched rational witness `a_{n0}+ε_(k+1)`.
4. Local noncompactness now contains the finite-open-cover argument that transfers compactness from a containing neighborhood to a clopen cylinder.
5. Product congruence, reciprocal tail bounds, diagonal approximation and SupData regularity are spelled out in an auxiliary appendix.
6. The Lyons–Peres bibliography now includes its author-supplied DOI.

## Residual limitations — not hidden

- The paper is still a relatively concise research manuscript; many elementary inductions and finite-sum rearrangements are compressed, as is standard in mathematical publishing. A full 89-subsection, lemma-by-lemma textbook treatment would be a substantially larger work and is **not** represented as completed by this audit.
- Some steps appeal to already-proved repository lemmas for technical order closure, Cauchy lifting and constructive decidability. Their signatures exist and were checked via the frozen source; an independent full-length prose derivation of every such supporting lemma would require further pages.
- Primary literature for several restricted-access books has been checked at publisher chapter level, not via a full independent examination of their internal proof text. No paper theorem cites such a text as its proof.
- Exact author, external peer-review approval, and journal formatting are not supplied and are not invented.

## Addendum — responses to the merged reviews (15 October 2026)

The revised `main.tex` now correctly presents `TreeZ` as a normalized-pair structure, and separately presents `TreeQ` as quotient classes equipped with the field structure **transported** from the internal fraction field via `TreeQ.lift1`/`lift2`. The `TOField` base explicitly includes decidable `Nonneg` and the `archBound` function with `arch_spec`. The unary discussion states the additional `-1` exclusion as an *informal consequence*, not an archived Lean theorem, and does not assert an exact-image theorem. The `RNonneg` quantifiers are `∃ representative ∀ precision ∃ tail`. Undirected cycle freedom and openness of cylinder complements are now discussed at their actually proved strength.

The previous 24-topic table is a targeted review, not an autonomous formal derivation of every helper lemma. Revised formulas in the main paper are connected to the exact source correspondences; intermediate checks are in `revision_acceptance.md` and the separate correspondence file. No new Lean kernel test was performed for the edited manuscript.
