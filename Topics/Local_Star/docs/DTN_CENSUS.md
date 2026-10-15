# Complete local DtN family — target theorem inventory

For an outward star with b children there are `2^(b+1)-1` nonempty terminal subsets. Each defines an effective map by harmonic elimination (or an equivalent Schur complement). The retained-center form for children A is `Σ_{i∈A}(e_i-e_r)(e_i-e_r)ᵀ`. If the center is eliminated and `A` nonempty with k children, the map is `I_A - (1/k)J_A`.

After zero-extension to the common original star carrier the only collisions are between the b+1 single-terminal zero responses; hence there are `2^(b+1)-b-1` distinct matrices. For b=4: 31 boundary choices, 27 distinct matrices, 5 collapsed singleton choices. This count refers to a common labeled carrier and must not be confused with classification up to permutation.

For retained center and k≥1: rank k, eigenvalues 0, 1 (multiplicity k−1), k+1 (multiplicity 1) on the retained carrier. For eliminated center and k≥1: rank k−1, eigenvalues 0 (one) and 1 (multiplicity k−1). In each case justify empty and singleton cases.

Mandatory proofs: total normal forms, invertible interior blocks, exact response equivalence relation, symmetry, zero row sum, positivity, kernel, rank, spectra, group-action invariance and case b=4 exhaustive regression. **Mathematical targets only; not yet Lean-verified.**
