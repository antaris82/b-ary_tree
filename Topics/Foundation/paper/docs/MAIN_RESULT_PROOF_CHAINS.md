# Detailed proof chains for the 25 named main results

Each entry is a human-readable dependency outline, not a substitute for the full theorem proof in `main.tex` (including the integrated detailed arguments), or the exact Lean signature in `proof_correspondence.md`.

## 1. Unique finite root path (proposition, main.tex:187)

1. Structural induction supplies existence of root paths.
2. Unique immediate predecessor forces every step in a root path.
3. Induction on depth identifies the edge list and proves uniqueness.

## 2. Path sum equals depth (proposition, main.tex:224)

1. Root-edge list is defined recursively.
2. The unit-edge sum is folded along that list.
3. Induction appends exactly one edge, so the sum equals word depth.

## 3. Natural semiring (proposition, main.tex:258)

1. Unary words are recursively defined.
2. Concatenation and repeated concatenation satisfy structural recursion.
3. Induction proves the semiring laws and uniqueness of recursion.

## 4. Transitivity and positive-denominator cancellation (lemma, main.tex:367)

1. Fractions use the cross-product relation with positive denominators.
2. Transitivity multiplies by a strictly positive common factor.
3. Integral-domain cancellation yields the required cross-product equality.

## 5. Fraction-field algebra (proposition, main.tex:398)

1. The raw arithmetic formulas preserve equivalence classes.
2. Normal-form sign decomposition constructs inverses and excludes zero divisors.
3. Integral-domain cancellation, the positive-denominator condition and the quotient congruences furnish the field laws; the rational order is established separately.

## 6. Ordered-field comparison (theorem, main.tex:474)

1. Each fraction has a valid two-letter triple witness.
2. The quotient relation gives mutually inverse maps Φ and Ψ.
3. Transported operations and cross-product order yield an ordered-field isomorphism.

## 7. Arity independence (corollary, main.tex:494)

1. Both alphabets have two distinguished different letters.
2. The two representations are transported through the shared Frac(Z).
3. Composition and TreeQ.transfer_le yield ordered-field compatibility.

## 8. Symmetric bilinearity of the finite coordinate form (proposition, main.tex:533)

1. Define B(x,y) as a finite sum of coordinate products.
2. Distribute addition and scalar multiplication through finite sums.
3. Commutativity gives symmetry; no positivity is inferred.

## 9. Explicit bases and ranks (theorem, main.tex:576)

1. The vector u spans the uniform line.
2. The coordinate differences e_j−e_0 lie in the zero-sum kernel.
3. Their nonzero coordinates prove independence; zero-sum gives spanning.

## 10. Finite decomposition (theorem, main.tex:613)

1. Define projections by averaging coordinates and subtraction.
2. Their summands have the required membership for positive b.
3. The line and kernel intersect only at zero, proving uniqueness.

## 11. Complementary projection operators (theorem, main.tex:629)

1. Linearity follows from linearity of the coordinate sum.
2. Apply decomposition uniqueness to obtain idempotence and annihilation.
3. Image and kernel characterizations follow from the fixed-point identities.

## 12. Algebraic orthogonal splitting (theorem, main.tex:671)

1. B(u,s)=sum_i s_i=0 for s in S.
2. Extend by linearity to L×S, then symmetry to S×L.
3. Expand B(P_Lx+P_Sx,P_Ly+P_Sy) and remove mixed terms.

## 13. Countable transverse basis (theorem, main.tex:720)

1. Each difference vector has finite support and sum zero.
2. Coordinates >0 force coefficients to vanish in any finite linear relation.
3. Finite support and sum zero supply a finite expansion of every vector.

## 14. Longitudinal incompatibility for zero-padding (theorem, main.tex:742)

1. Pad a finite uniform vector by zero at the new coordinate.
2. Coordinate zero forces the candidate uniform scalar to be one.
3. The new coordinate forces it to be zero, contradicting nontriviality.

## 15. Separated rays (proposition, main.tex:791)

1. An explicitly differing index gives incompatible length-(n+1) prefixes.
2. Corresponding cylinders are disjoint by coordinate evaluation.
3. Cylinder complements are open by prefix agreement; double-negated differences are not witnesses.

## 16. Noncompact countable cylinders (proposition, main.tex:818)

1. The next-letter cylinders cover an ω-ary cylinder.
2. A finite subfamily omits some next-letter index.
3. Extending by that index defeats finite subcovers and hence compact neighborhoods.

## 17. Ray transitivity and invariant maps (proposition, main.tex:856)

1. Levelwise bijections induce inverse word/ray actions.
2. Coordinatewise swaps map any prescribed ray to another.
3. Transitivity makes every invariant map constant.

## 18. Product estimate and modulus (lemma, main.tex:953)

1. Obtain eventual bounds for each modulated factor.
2. Split the product difference into two summands.
3. Choose shifted precision indices so their errors sum to ε_k.

## 19. Constructive Cauchy ring (proposition, main.tex:978)

1. Sequence congruence proves addition/multiplication well-defined.
2. Pointwise ring equalities descend to the quotient.
3. Archimedean smallness makes constant-sequence embedding injective.

## 20. Order and tight apartness (proposition, main.tex:1016)

1. RNonneg requires a single representative witnessing all precisions.
2. Transfer and tail error budgets establish order properties.
3. Apartness tightness follows without assuming a decidable real order.

## 21. Separated inversion (theorem, main.tex:1063)

1. A positive apartness witness supplies a rational tail gap.
2. Resample into that tail and use modulus shifted by twice its gap index.
3. Unshifted product is equivalent to one by the separate Cauchy-tail estimate.

## 22. Modulated completeness characterization (theorem, main.tex:1177)

1. Modulated completeness quantifies over sequences supplied with moduli.
2. Tracked diagonal data yield a rational limit class.
3. Conversely, a modulated real limit yields rational approximation data; no modulus-free choice is hidden.

## 23. Suprema from data (theorem, main.tex:1217)

1. SupData supplies rational upper estimates and close witnesses.
2. The estimates form a modulated rational Cauchy class.
3. Upper-bound and approximate attainment inequalities establish the least property.

## 24. Logical equivalences; conditional form (theorem, main.tex:1288)

1. Encode Boolean streams as rational Cauchy data with known modulus.
2. Use the constructive gap test to translate inversion/zero decisions.
3. The project proves equivalences with MP, LPO, WLPO and real trichotomy, not the principles themselves.

## 25. One-way logical lower bounds (proposition, main.tex:1319)

1. Assume an unrestricted LUB / monotone convergence principle.
2. Build the specific Boolean-coded set or monotone sequence.
3. The derived real decision yields WLPO / LPO respectively; no converse is claimed.

