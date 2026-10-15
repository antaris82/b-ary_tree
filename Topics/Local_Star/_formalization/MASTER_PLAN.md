# MASTER PLAN — Formalization of Local_Star (S1–S8)

**Mathematical question.** Given Foundation's rooted finite-word trees, path-count arithmetic, fields and finite child-coordinate spaces, construct and classify finite outward stars and their response/resistance geometries, then study compatible block composition and limited infinite boundary questions.

**Immutable dependency rule.** Existing `Foundation` is reusable without modification. Historical `FloatingStar` is read-only mathematical inspiration, never source to import/port/copy. No external number carriers, Mathlib, classical choices, unproved new axioms, or prohibited Foundation-source tokens. Use Lean 4.28.0 and a shallow import DAG.

## S1 — Embedded outward stars (covered by expanded Aristotle Task 01)
Carrier for local vertices and edges at any `v : Word (Child b)`; preserve global word addresses. `S_b(v)` has center v, children c::v and b outgoing edges; its incoming parent edge is excluded even if v is not the global root. Prove address injectivity, incidence, the one-vertex overlap with immediately adjacent outward stars, disjoint local edge sets, unique ownership of any ambient parent-child edge. Test b=1 and root/nonroot. **Task 01 now continues into the elementary local part of S2**; consult its full current objective, not the historical short scaffold.

## S2 — Unit electric model and measurement (local part in Task 01)
Define **new** conductance c(e)=1 (not an automatic consequence of path count), `I_e=U(child)-U(parent)` with consistent signed Kirchhoff divergence; define energy `E=Σ (ΔU)^2`, Laplacian as incidence sum. Prove symmetry, row-sum zero, PSD and exact constant kernel. **Task 01 covers the complete local-star model**, center-grounded unit-current injection at a child, opposite child-port injections, resistance 1 and 2, grounded PD, and the identity resistance Gram. Its scalar computations use exclusively Foundation `TreeN`, `TreeZ`, `QStar` (the established `TreeQOmega`) including at arity one. The **remaining global path extension** (grounding the actual global root and injecting at arbitrary depth w, proving `R(root,w)=pathSum(w)=depth(w)` and all finite-tree unique-path resistances) must be a later targeted task requiring finite assembled-tree interfaces; do not assume it in Task 01.

## S3 — Exact finite local DtN
For every **nonempty** terminal subset B of the star, eliminate interior I. Prove harmonic extension and block invertibility from explicit constructors, then match energy-minimizing DtN and Schur form. If center retained with selected children A: `Λ_R=Σ_{i∈A}(e_i-e_r)(e_i-e_r)^T`. If center eliminated and A nonempty with k children: `Λ_P=I_A−J_A/k`. Establish zero rows, symmetry, PSD, and the precisely stated constant kernel and grounded PD.

## S4 — Boundary classification
Prove count `2^(b+1)−1` of nonempty boundary choices, and `2^(b+1)−b−1` distinct **zero-extended** matrices: exactly b+1 singleton choices collapse. Rank/spectrum/permutation classification with carrier and multiplicities explicit. b=4 mandatory: 31 terminal subsets, 27 matrices, complete census. Distinguish labels, equivalence, matrix equality and conjugacy classes.

## S5 — Effective resistance and metric forms
Build on Task 01's **locally measured** resistance 1/2, grounded PD and resistance Gram identity, without recoding the electrical model. Extend to Dirichlet-energy minimization, general DtN reductions and composite-block resistance invariance; prove the appropriate constrained energy minimum and resistance inverse only after positivity. Realize `p_root=0,p_i=e_i` and show squared Euclidean distances equal effective resistances. Distinguish identity `G_res=I` from PSD `Λ`, grounded PD and the ambient coordinate Gram `G_coord=I+J`; coordinate/resistance forms agree only on zero-sum transverse coefficients. Prove simplexes/faces and retain boundary labels for singleton null responses.

## S6 — Dimension census and conditional b=4 criteria
Record algebraic child rank b, longitudinal 1, transverse b−1, relative outgoing-star b, effective boundary rank |B|−1, and affine dimensions. The outward star is a b-simplex, the pure child facet is regular (b−1)-simplex. If transverse rank 3 is a desired criterion, b=4. Separately `d(d−1)/2=d` with d≥0 selects d=0 or 3; for nonzero transverse dimension, b=4. These criteria neither derive orientation nor imply a global 3-manifold or any new algebra.

## S7 — Composition of overlapping stars
For finite tree prefixes, prove `L_T=Σ_v ι_v L_{S(v)} ι_v^T` from unique primitive edge ownership. Potentials coincide and currents balance at shared addressed vertices. Prove direct-vs-compatible-stepwise Kron reductions with explicit surviving interface terminals and pivot hypotheses; never add arbitrary unrelated reduced matrices. For a nonroot full-neighbor elimination, degree b+1 yields complete graph K_(b+1) with conductance 1/(b+1); b=4 => K5 conductance 1/5, while outward-star elimination => K4 conductance 1/4. Prove retained-terminal effective resistance preserved; global edge-characteristic vectors yield `||p_u-p_v||²=R(u,v)`. Investigate dimensional growth under gluing and prevent global dimension extrapolation.

## S8 — Infinite boundary and limiting response scope
Use Foundation `Ray.prefixAt`. Individual ray prefix resistance to root is n and diverges. Node resistance metric has minimum separation 1; ordinary vertex Cauchy completion adds no ray points. A **different** experiment shorts all depth-n vertices to one counterelectrode: `R_0=0`, `R_(n+1)=(1+R_n)/b`, `R_n=Σ_{k=1}^n b^{-k}`. b=1 divergent; b≥2 converges to 1/(b−1) with explicit rational error `b^(−n)/(b−1)` and constructive modulus. Native prefix-ray topology is a different object. No canonical infinite DtN `Λ_∞` without interlevel carriers, maps and a named convergence theorem. Unproved forms and geometric identifications remain OPEN.

## Proof architecture and integration
One precise Aristotle task at a time. Add only files with proved mathematical purpose; keep directed imports broad and shallow. Foundation's numerical carrier and operations must be reused, not redeveloped. Use minimally sufficient finite functional matrix primitives in LocalStar; no ambitious standalone matrix library. Every accepted theorem needs exact elaborated signature, minimal hypotheses, documented SHA, kernel build, source-policy check, transitive axiom audit, and a relevant regression test. Tests are **not** universal proofs. Maintain strict statuses: IDEA / CONJECTURE / EXACT TEST / INFORMAL PROOF / KERNEL CHECKED / OPEN / REFUTED.

## Priorities and exclusions
Prioritize actual local star construction, electric normalization, DtN, resistance geometry and composition *before* any general algebra. Do not create Clifford, spin, quaternion, octonion, Lorentz, physical spacetime, independent numbers or physical dynamics in this topic. The foundational paper remains separately citable.
