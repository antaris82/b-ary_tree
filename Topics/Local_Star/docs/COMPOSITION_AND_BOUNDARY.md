# Overlapping blocks and boundary regimes

## Primitive edges and composition
For center v, outward `S_b(v)` has edges v→c::v. Adjacent outward stars intersect in exactly one **vertex**, share no **primitive edge**, and each ambient edge is owned by exactly one outgoing star. With global address embeddings ι_v and full finite prefix T_n, the Laplacian satisfies `L_T=Σ_v ι_v L_v ι_vᵀ`. This is a **goal to prove** in new Lean.

A shared interface has one potential value and Kirchhoff-balanced currents. You cannot sum arbitrary independently reduced local DtN matrices; retain all needed interface terminals until their common elimination. Prove exact direct-versus-stepwise Kron equivalence with explicit invertibility hypotheses.

## Full neighborhood differs from outward star
At nonroot center v there are b children **and an incoming parent edge**. Eliminating this degree-(b+1) interior node with all its neighbors retained gives a complete effective graph on b+1 ports with per-edge conductance 1/(b+1). For b=4, this is K₅ with 1/5, not the outward star's K₄ with 1/4. The effective graph's cycles do not change the primitive tree's unique paths.

## Effective resistance preservation
For any two retained vertices in a connected finite unit tree, two-terminal resistance equals the number of primitive edges on their unique path, provided all other ports have zero net injection. For the resistance Gram realization, use global edge-address characteristic vectors p_v: `||p_u-p_v||²=R_eff(u,v)`. A larger composite block can have higher affine rank than a child facet; no global dimension-three theorem follows from b=4.

## Distinct infinite regimes
(1) Individual ray prefixes `v_n`: `R(o,v_n)=n` diverges.
(2) The ordinary resistance-metric completion of finite **vertices** adds no ray ends: distances between distinct nodes ≥1.
(3) At finite depth n, if **all depth-n nodes are shorted into one terminal**, `R_n=Σ_{k=1}^n b^{-k}`. For b≥2, limit 1/(b−1); for b=1, unbounded.
(4) Native `RayFinite b` with prefix topology is a separate Foundation object. Any `Λ_∞` requires explicitly compatible carriers/inter-level maps and a named convergence relation.

A shorted boundary is an added boundary condition, not a Schur reduction. Neither finite resistance to the collective end nor effective loops imply finite ray-path distance.
