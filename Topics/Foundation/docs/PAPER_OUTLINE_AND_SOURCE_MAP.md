# Full mathematical paper outline and source map — Rooted trees, path arithmetic, child-coordinate modules, and constructive completion

**Status:** Planning document for a future mathematical paper; **not** a manuscript.  
**Primary formal source:** frozen Task-5 Q14-repaired repository, Lean 4.28.0.  
**Scope:** all substantive proved mathematics, all important explicitly conditional results, and all central unresolved assertions.  
**Language of eventual paper:** English.  
**Writing priority:** standard mathematical definitions, propositions, theorems, and proofs; Lean names only in this planning document and a separate provenance appendix.

## Proposed working title

**Arithmetic and Algebraic Child-Space Decompositions of Rooted Trees: Constructive Number Systems, Infinite Branching, and Boundary Structures**

Alternative shorter title: *Rooted Trees, Path Arithmetic, and Algebraic Decompositions*. Do not claim a topological dimension of the tree equal to `b−1`, a full classical real field, a geometric embedding, or mathematical novelty without further evidence.

## Essential editorial rules

1. Present mathematics and its hypotheses directly. Never narrate task numbers, programming effort, or the chronology of Aristotle runs as mathematics.
2. Distinguish **definition**, **proved theorem**, **proved conditional theorem**, **counterexample**, and **open claim**. The strength of the LaTeX theorem must be no greater than that of its elaborated Lean signature.
3. A source citation supplies historical and conceptual context; **the project's original proof** supplies the actual claim. Do not cite a textbook as though it proves the project's specific nonstandard formulation.
4. The coefficient field for finite-dimensional statements is the internally constructed rational field (or the exact `TField K` hypothesis where the theorem is generic). The direct-sum decomposition does **not** require the completion.
5. For the Cauchy quotient use **constructive Cauchy ring with an apartness-based inversion theorem**, not “complete ordered field” without conditions.
6. The native ray boundary, the coordinate module, and the Cauchy quotient are distinct objects. No canonical identification has been constructed.
7. Full mathematical proofs in the eventual paper; reserve Lean paths, precise signatures, audit summaries, and reproduction instructions for a *supplementary correspondence file*.
8. References are to authentic works by their authors (or original publishers). Check any specific theorem/page citation against its actual chapter before submission.

## 0. Front matter

**Title; authors and affiliations (supplied by author, not invented); abstract; keywords; MSC 2020 classifications (to validate).** The abstract must mention rooted infinite-depth trees of finite and countably infinite arity, unary path arithmetic, the signed and fractional quotients, the `b−1` transverse-rank theorem, and the scope of constructive Cauchy completion. Do not claim that all statements are unconditionally classically complete.

## 1. Introduction

### 1.1. Mathematical objects and construction order
Define the question as the systematic study of elementary number structures and child-coordinate modules associated with finite words and rooted parent–child relations. State the actual dependency order: unary path counts → signed differences → positive-denominator triple fractions → finite child-coordinate modules and a separate modulated Cauchy quotient. Differentiate the existence of representations from the universality of standard numbers.

### 1.2. Related established mathematical frameworks
Locally finite and countably branching rooted trees; word monoids and path lengths; quotient semirings and fraction fields; free modules and kernels of coordinate sums; ends and cylinder topologies; constructive analysis. Avoid a misleading single “new theory” claim. **Literature:** [S], [LP], [K], [A], [BB], [BR].

### 1.3. Main theorems and their scope
Short, mathematical statement of the depth-class semiring representation; integer ring and rational ordered-field construction; arity-independence of the rational body; local `1+(b−1)` basis decomposition; algebraic omega limit; native boundary results; Cauchy quotient algebra, tracked convergence, and conditional completeness; logical equivalences. Each named item must be covered in the paper with its hypotheses.

### 1.4. Logical framework and interpretative scope
Constructive proof policy; primitive inductive words and quotients; explain that quotient formation uses underlying logic rather than preexisting numerical fields. In the paper proper, keep this to a paragraph and refer the reader to the supplement. **Literature:** [L], [BR].

## 2. Finite words and rooted trees

### 2.1. Alphabets, finite words, root, and directed edges
For alphabet `A`, define `A^{<ω}`, the empty root `ε`, and `(w,w⌢a)` for each `a∈A`. Distinguish word-length from graph-embedding coordinates. **Lean:** `PrimitiveTree/FiniteWords.lean`: `Word` L22; `root` L29; `depth` L32; `IsParent` L37; `Edge` L40; `ChildOf` L103. **Literature:** [S] (trees), [K] (trees as finite sequences).

### 2.2. Unique parent and unique finite root path
Prove uniqueness of immediate predecessor, root-path existence and uniqueness. Define ordered edge list explicitly. **Lean:** `PrimitiveTree/FiniteWords.lean`: `root_no_parent` L69; `nonroot_has_parent` L72; `parent_unique` L75; `rootEdges` L133; `dpath_root_unique` L142.

### 2.3. Connectedness, absence of cycles, and infinite depth
Specify graph-theoretic assumptions; use the code's *precise* connectedness and cycle predicates rather than claiming a stronger equivalence of graph categories. **Lean:** `PrimitiveTree/FiniteWords.lean`: `connected` L187; `no_cycle` L261; `unbounded_depth` L288.

### 2.4. Finite arity as a derived indexing object
Once unary counts are defined, `Child b={i : TreeN | i<b}` supplies `b` child symbols. Explain that the general finite-arity family is **parametrized using the previously defined unary natural structure**. This is not circular because §5 makes that construction explicit. **Lean:** `PrimitiveTree/FiniteChild.lean`: `Child` L18; `inclSucc` L76; `enum` L111; `nodup_enum` L144; `TreeNumbers/PathNaturals.lean` L17–37.

### 2.5. The countably branching tree
Use count-indexed finite words, not a fictitious finite “arity infinity.” Child bijection with the self-built unary counts; infinitely many children; unbounded depth. **Lean:** `TreeFoundation/OmegaTree.lean`: `WordOmega` L18; `childOfIndex` L23; `children_distinct` L33; `infinitely_many_children` L37; `unbounded_depth` L52. **Literature:** [LP], [K].

### 2.6. Inclusions and the directed arity union
Prove finite-arity alphabet/word/edge embeddings; every finite word and finite edge in the countably branching tree appears at a sufficiently large finite arity. **Lean:** `TreeFoundation/ArityEmbeddings.lean`: `mapWord_injective` L36; `mapWord_isParent` L55; `wordOmega_wordSucc` L105; `vertex_union` L147; `edge_union` L153. Carefully state the positivity of a bounding arity for the root. **Literature:** [K].

## 3. Primitive unit-edge path sums

### 3.1. Unit contribution and literal finite edge sum
Assign unit contribution to each primitive parent–child edge; define the path sum as a fold over the actual root-edge list, **not** as a primitive vertex label. **Lean:** `PrimitiveTree/RootEdges.lean`: `edgeFold` L22; `unitSum` L27; `pathSum` L30.

### 3.2. Equality of unit-edge sum and depth
Prove `pathSum(w)=depth(w)` by edge-list recursion. Explain the consequence that path sums are invariant under alphabet-symbol replacements. **Lean:** `PrimitiveTree/RootEdges.lean`: `unitSum_rootEdges` L68; `pathSum_eq_depth` L75; `pathSum_cons` L77.

### 3.3. The unbounded path-count sequence along each ray
For a ray `ξ`, show `pathSum(prefix_n ξ)=n` and therefore no finite Cauchy limit arises from the **unmodified** prefix-count sequence. Do not infer any no-go for all possible ray encodings. **Lean:** `TreeFoundation/InfiniteRays.lean`: `pathSum_prefixAt` L44; `TreeAnalysis/PrimitiveDataScope.lean`: `prefixCount_eq` L51; `prefixCount_not_isCauchy` L62; `prefixCount_indep` L77.

## 4. Unary path counts and the natural-number semiring

### 4.1. Unary paths as natural-count carrier
Use the one-letter type `U`; `N_T=U^{<ω}` and empty path/single-edge/successor. Explicitly state that this is a construction of a carrier isomorphic to standard naturals, not a foundational reconstruction of Lean's inductive kernel. **Lean:** `PrimitiveTree/UnaryPaths.lean`: `UnaryPath` L16; `extend` L27; `concat` L30; `iterate` L35; `TreeNumbers/PathNaturals.lean`: `TreeN` L17.

### 4.2. Addition and multiplication from word operations
Concatenation and repeated concatenation, with associativity, commutativity, units, zero, and distributivity derived by structural induction. **Lean:** `TreeNumbers/PathNaturals.lean`: `add` L34; `mul` L37; `add_comm` L79; `mul_comm` L117; `right_distrib` L126; `mul_assoc` L136; `instCSR` L156.

### 4.3. Induction, recursion, order, and cancellation
Induction/recursion over unary words; order by prefix/suffix additive comparison; totality, antisymmetry and compatibility. **Lean:** `TreeNumbers/FoundationsLedger.lean`: `induction` L32; `recN` L42; `recN_unique` L51; `TreeNumbers/PathOrder.lean`: `le_antisymm` L141; `lt_or_eq_or_gt` L167; `le_iff_exists_add` (see `FoundationsLedger.lean` L83).

### 4.4. Equal-depth quotient for arbitrary nonempty alphabets
Define `w~v` iff equal primitive path sums, quotient `D(A)`; construct its semiring and prove an ordered-semiring isomorphism `D(A)≅N_T` when a letter is supplied. Distinguish representative dependence from class invariance, and note the empty-alphabet obstruction. **Lean:** `TreeNumbers/DepthQuotient.lean`: `DepthRel` L40; `DepthClass` L62; `repeatW` L119; `OrderedSemiringIso` L281; `depthIso` L294; `depthIso_letter_indep` L307; `no_positive_count_of_noLetter` L331.

## 5. Signed differences and the integers

### 5.1. Oriented pairs of nonnegative path counts
Construct the pair relation `(m,n)~(p,q)` iff `m+q=p+n`. Negative signs are **not** primitive edge values. **Lean:** `TreeNumbers/PathIntegers.lean`: `PairEq` L23; `pairEq_refl` L25; `pairEq_symm` L27; `pairEq_trans` L29.

### 5.2. Normal forms and equivalence classes
Define canonical normalized representatives by cancellation of simultaneous successor edges. Prove exactness and uniqueness of normal form. **Lean:** `TreeNumbers/PathIntegers.lean`: `normPair` L37; `normal_unique` L64; `TreeZ` L92; `mkZ_sound` L113; `mkZ_exact` L119.

### 5.3. Ring laws and absence of zero divisors
Addition, negation, multiplication on normalized pairs; check distributivity, additive inverses, nontriviality, no zero divisors, cancellation. **Lean:** `TreeNumbers/PathIntegers.lean`: `instCRing` L256; `mul_eq_zero` L319; `mul_left_cancel` L330; `mul_ne_zero` L342.

### 5.4. Order and canonical embedding of natural counts
Order, decidability (for this carrier), preservation/reflection by `N_T→Z_T`. **Lean:** `TreeNumbers/PathOrder.lean` and `TreeNumbers/FoundationsLedger.lean`: `ofN_lt_ofN` L124; `lt_trichotomy` L140; `TreeNumbers/PathIntegers.lean`: `ofN` L351; `ofN_injective` L366. Validate precise order theorem signatures before final prose.

## 6. Rational numbers as classes of three finite paths

### 6.1. Valid configurations and the positive gap
Triples `(P1,P2,P3)` of pairwise distinct paths with `len(P2)>len(P3)`. Set `A=len(P1)-len(P2)∈Z_T`, `D=len(P2)-len(P3)>0`. **Lean:** `TreeNumbers/PathTriples.lean`: `TriplePath` (locate in final source); `numer`, `denom`; `denom_pos` (locate in final source).

### 6.2. Equivalence by cross multiplication
`(A,D)~(A',D')` iff `AD'=A'D`. Prove reflexivity, symmetry, transitivity and compatibility with each operation. **Lean:** `TreeNumbers/PathTriples.lean`: `Rel`; `TreeNumbers/PathFractions.lean`: `Eqv` L41, `eqv_trans` L49, `add_resp` L101, `mul_resp` L113.

### 6.3. Universal representatives using two distinct child symbols
Explicit distinct-word witnesses for every signed numerator and positive denominator; trace where `[TwoLetters α]` enters. **Lean:** `TreeNumbers/PathTriples.lean`: `universal_witness` L194; `TreeNumbers/FoundationsLedger.lean`: `unary_numer_ne_zero` L208; `unary_no_universal_witness` L216.

### 6.4. Field operations and all field laws
Classes `Q_T(α)`, total inverse convention `0⁻¹=0`, nonzero inverse, nontriviality, characteristic zero. Present actual group/ring/field proofs, not only a certificate listing their conclusions. **Lean:** `TreeNumbers/PathRationalField.lean`; `TreeNumbers/PathFractions.lean`: `mul_inv_cancel` L243; `TreeAnalysis/FractionCharacterization.lean`: `FracQ.instTField` L240.

### 6.5. Ordering and Archimedean structure
Order by positive-denominator cross multiplication, order compatibility and characteristic-zero embedding of unary counts. Dyadic bounds later used for Cauchy moduli. **Lean:** `TreeAnalysis/RationalOrder.lean`: `NonnegQ` L123; `archQ` L282; `instTOField` L299; `TreeAnalysis/DyadicPrecision.lean`: `eps` L73, `exists_eps_lt` L173.

### 6.6. Identification with internally defined fractions
Independently define positive-denominator fractions from `Z_T` and prove the ordered-field isomorphism `Q_T(α)≅FracQ`; demonstrate addition, multiplication, inverse and order preservation/reflection. **Lean:** `TreeAnalysis/FractionCharacterization.lean`: `FracQ` L74; `ofFracQ_toFracQ` L281; `toFracQ_ofFracQ` L285; `orderedFieldIsoFracQ` L347.

### 6.7. What branching contributes to this representation
A formal theorem/remark: arithmetic values depend only on path sums, while distinct child symbols guarantee *existence of the chosen triple representatives*. Do not claim all rational arithmetic intrinsically requires branching. **Lean:** `TreeAnalysis/FractionCharacterization.lean`: `mk_eq_of_depth_eq` L61; `TreeNumbers/FoundationsLedger.lean`: `unary_numer_ne_zero` L208.

## 7. Independence of the number structures from arity

### 7.1. Canonical algebraic comparisons across finite arities
State the family of ordered-field isomorphisms `Q_T(b)≅Q_T(c)` for `b,c≥2`; identify explicit assumptions. **Lean:** `TreeNumbers/RationalArityIndependence.lean`; `TreeNumbers/FoundationsLedger.lean`: `arityIso_comp` L284.

### 7.2. Compatibility and uniqueness
Prove identity, composition and natural-count embedding compatibility where present; do not mistake an isomorphism for a canonical identification of all individual words. **Lean:** `TreeAnalysis/Canonicity.lean`; `TreeNumbers/FoundationsLedger.lean`: `transfer_comp` L272, `transfer_natCast` L277.

### 7.3. Representation versus primitive structure
Mathematical distinction between the intrinsic arithmetic quotient and the full address-bearing tree. Later child-coordinate ranks *do* depend on arity. Present this as a precise comparison, not a causal claim about a “dimension of a tree.”

## 8. Finite child-coordinate spaces over the constructed rational field

### 8.1. Coordinate module and algebraic operations
For `b≥1` and `K=Q_T(α)` define `F_b=K^{Child(b)}`, zero, addition, scalar multiplication and canonical coordinate vectors `e_i`. **Lean:** `DimensionFoundation/FiniteChildModule.lean`: `F` L27; `addV` L30; `smul` L32; `e` L74. **Literature:** [A] Chapters 1–3.

### 8.2. Coordinate sum and canonical bilinear form
`σ_b(x)=Σ_i x_i`, `B_b(x,y)=Σ_i x_i y_i`. Call it a **symmetric bilinear form**; over ordered rationals it also has positivity, but do not assert unproved norm/Hilbert/completion properties. **Lean:** `DimensionFoundation/FiniteChildModule.lean`: `coordSum` L59; `dot` L71; `dot_comm` L114; `DimensionFoundation/FiniteSums.lean`: `sumC` L66. **Literature:** [A] Ch. 6.

### 8.3. Uniform line and zero-sum submodule
`u_b=(1,…,1)`, `L_b=K u_b`, `S_b=ker σ_b`. These are *defined* as longitudinal and transverse directions in the finite child-coordinate module; their identification does not arise solely from the abstract undirected graph. **Lean:** `DimensionFoundation/FiniteChildModule.lean`: `u` L62; `InL` L65; `InS` L68.

### 8.4. Orthogonality relative to the chosen bilinear form
`B_b(u_b,x)=0` for `x∈S_b`; the explicit difference basis need not be pairwise orthogonal. **Lean:** `DimensionFoundation/FiniteChildModule.lean`: `dot_u_of_inS` L110; `dot_comm` L114.

### 8.5. Explicit basis of the uniform line
Constructive basis of `L_b` consisting of `u_b`; rank one for `b≥1`. **Lean:** `DimensionFoundation/TransverseBasis.lean`: `IsBasisOf` L47; `longitudinal_basis` L65; `DimensionFoundation/Instances.lean`: `longitudinal_basis_treeQ` L24.

### 8.6. Basis of the zero-sum submodule
For `b=c::b'`, basis vectors `e_{j+1}-e_0` indexed by `Child(b')`. Prove spanning and linear independence and the rank `b−1`. **Lean:** `DimensionFoundation/TransverseBasis.lean`: `tv` L85; `tv_indep` L134; `tv_span` L141; `transverse_basis` L155; `transverse_index_bijection` L164. **Literature:** [A] Ch. 2.

### 8.7. Explicit projection and direct-sum theorem
`P_L(x)=(σ_b(x)/b)u_b`, `P_S(x)=x−P_L(x)`; prove `F_b=L_b⊕S_b`, uniqueness and trivial intersection. Restrict to positive finite arity, rational characteristic zero and invertibility of its numeral. **Lean:** `DimensionFoundation/TransverseBasis.lean`: `projL` L173; `projS` L176; `decomposition` L181; `decomposition_unique` L194; `inL_inS_zero` L211; `DimensionFoundation/Instances.lean`: `direct_sum_treeQ` L29.

### 8.8. Exceptional unary case and permutation invariance
`b=1` gives `S_1={0}`. Child permutations preserve line, zero-sum subspace and bilinear form. **Lean:** `DimensionFoundation/TransverseBasis.lean`: `transverse_one_zero` L218; `dot_perm` L231; `inS_perm` L237; `inL_perm` L244.

### 8.9. Interpretation of `b−1`
A theorem about free rank / vector-space dimension **of a local coordinate space**. Not the covering/topological/Hausdorff dimension of the tree, its boundary, or a manifold.

## 9. Countably infinite child-coordinate limit

### 9.1. Finite-support sequences and the zero-sum condition
Define the algebraic direct sum `K^{(N_T)}` and `S_ω={x: finite support, Σ x_i=0}` using explicit support bounds and finite sums. **Lean:** `DimensionFoundation/OmegaFiniteSupport.lean`: `FO` L26; `FinSupp` L38; `InSO` L41.

### 9.2. A countable explicit basis
Construct vectors `e_{i+1}−e_0`; show finite linear independence and algebraic spanning of `S_ω`. Distinguish algebraic spanning from any infinite-series convergence. **Lean:** `DimensionFoundation/OmegaFiniteSupport.lean`: `tvO` L113; `tvO_indep` L160; `tvO_span` L170; `DimensionFoundation/Instances.lean`: `omega_indep` L43 and `omega_span` L48.

### 9.3. Canonical compatible inclusions
Zero-padding `S_b→S_{b+1}→S_ω`; compatibility with addition and scalar multiplication, and the basis elements. **Lean:** `DimensionFoundation/OmegaFiniteSupport.lean`: `pad` L217; `pad_injective` L236; `pad_inSO` L249; `pad_tv` L266; `padSucc` L283; `padSucc_inS` L294; `padSucc_tv` L304.

### 9.4. Failure of the uniform line under zero-padding
The all-ones sequence does not have finite support. Zero-padding does not carry `L_b` into `L_{b+1}` as the corresponding uniform line. Hence the finite direct-sum decompositions do not form a compatible global decomposition under these inclusions. **Lean:** `DimensionFoundation/BoundaryLongitudinal.lean`: `allOnes_not_finSupp` L35; `no_finSupp_uniform_limit` L40; `padSucc_u_not_inL` L50.

### 9.5. Precise scope of the omega result
No unique limiting “longitudinal line,” no limiting tangent vector, and no disappearance of such a direction has been established without an added identification/transport or ambient space. State the proved *particular embedding obstruction*, not a universal impossibility.

## 10. Infinite rays and native boundary topology

### 10.1. Rays as infinite sequences and coherent prefixes
`∂T_A=A^{N_T}`; finite prefixes, unique directed paths and unbounded prefix depth; distinguish ends from vertices. **Lean:** `TreeFoundation/InfiniteRays.lean`: `Ray` L19; `prefixAt` L30; `prefixAt_succ` L34; `eq_of_prefixAt` L65; `depth_unbounded` L83. **Literature:** [LP] Ch. 1; [K] pp. 5–12.

### 10.2. Boundary and arity union do not commute
Finite-arity rays inject into countable-arity rays, but `ξ(n)=n` is not in any single finite-arity subboundary. **Lean:** `TreeFoundation/InfiniteRays.lean`: `ofFinite` L93; `identityRay_not_finite` L108; `union_proper` L116.

### 10.3. Cylinders and prefix incidence
Define `C(w)={ξ : w is a prefix of ξ}`. Prefix agreement and properties of cylinders derived from finite words. **Lean:** `BoundaryTopology/Cylinders.lean`: `Agree` L53; `Cyl` L56; `cyl_prefixAt` L124. **Literature:** [LP], [K] pp. 5–12.

### 10.4. Clopen cylinder basis and point separation
Establish the prefix topology with clopen cylinders. For alphabets with decidable equality, distinct rays are separated by a finite disagreement. Carefully distinguish negated equality from a constructive witness of disagreement. **Lean:** `BoundaryTopology/PrefixTopology.lean`: `PrefixOpen` L39; `prefixTopology` L42; `cyl_open` L58; `cyl_compl_open` L62; `separate_of_diff` L83; `not_not_diff_of_ne` L102. **Literature:** [K] pp. 5–12 and 35–40.

### 10.5. Connected subsets and isolated points
Under the actual assumptions in code: connected subsets are subsingletons; with two children there are no isolated points. State the constructive assumptions, avoid smuggling in classical point-set topology. **Lean:** `BoundaryTopology/TopologicalObstructions.lean`: `no_isolated` L81; `connected_subsingleton` L133; `boundary_disconnected` L119.

### 10.6. Countable arity and local compactness
Prove failure of cylinder compactness and local compactness in the implemented topological predicate; do **not** claim finite-alphabet boundary compactness was proven if it was not. **Lean:** `BoundaryTopology/TopologicalObstructions.lean`: `cyl_not_compact` L162; `not_locallyCompactAt` L219. **Literature:** [K] pp. 18–30; [LP].

### 10.7. Exact status of manifold statements
For the chosen chart predicate, zero-dimensional nonunary charts are excluded; unary boundary admits a trivial zero-dimensional chart. The no-chart result into a real model carries `IntervalsConnected K` as an explicit additional assumption. No general `R^d` model (`d≥2`) or positive manifold structure is established. **Lean:** `BoundaryTopology/ManifoldConditions.lean`: `Chart` L41; `no_zero_dim_chart` L117; `unaryChart` L127; `IntervalsConnected` L208; `no_chart_into_real` L227; `RealLineManifold.lean`: `realIdChart` L81. **Literature:** [K], [A] only for conventional concepts; not as sources for the project-specific conditional theorem.

### 10.8. Optional numerical encodings are noncanonical
Present encoding as a separate example, not an identification of every ray with a unique real number. Distinct rays can have equal encoded values, and letter-choice dependence must be recorded. **Lean:** `BoundaryTopology/BinaryEncoding.lean`: `encode` L103; `encode_not_injective` L176; `TreeAnalysis/PrimitiveDataScope.lean`: `encode_letter_choice_dependence` L144.

## 11. Automorphisms and invariance of ray observations

### 11.1. Levelwise child permutations and induced tree automorphisms
Define root-, depth-, edge-preserving maps and level-dependent (globally at that level) permutations; prove compatibility with finite words and rays. **Lean:** `TreeFoundation/RayAutomorphism.lean`: `LevelPerm` L33; `TreeAut` L101; `treeAut` L111; `rayAct` L123. **Literature:** [B].

### 11.2. Explicit transitive action on rays
Swap at each level the symbols of a given source/target ray. Prove any two rays can be related by the constructed automorphism. **Lean:** `TreeFoundation/RayAutomorphism.lean`: `swapPerm` L190; `rayAct_swapPerm` L197; `invariant_const` L209.

### 11.3. Invariant ray maps are constant
For any codomain, a map invariant under all these levelwise automorphisms is constant on the ray boundary. This does **not** forbid noninvariant encodings or imply an equivalence of the different mathematical carriers. **Lean:** `TreeFoundation/RayAutomorphism.lean`: `invariant_const` L209; `swapInvariant_const` L214.

### 11.4. General automorphisms are more numerous
An explicit subtree-supported involution preserving incidence cannot be described by a single permutation applied uniformly at each level; Q14 counterexample. **Lean:** `TreeFoundation/AutomorphismCounterexample.lean`: `subtreeSwapAut` L105; `subtreeSwapAut_not_levelwise` L189; `levelwise_converse_false` L204. Do not assert full classification of the automorphism group. **Literature:** [B].

## 12. Constructive Cauchy quotient of the rational field

### 12.1. Choice of base field and internally derived precision
Take `K=Q_T(α)` with the proved `TOField` interface and dyadic tolerances `ε_k`; enumerate the necessary Archimedean smallness, monotonicity and triangle estimates actually proved. **Lean:** `TreeAnalysis/OrderedField.lean`: interface; `TreeAnalysis/DyadicPrecision.lean`: `eps` L73; `eps_succ_add` L94; `three_eps_le` L141; `exists_eps_lt` L173. **Literature:** [BB] pp. 14–66; [BR].

### 12.2. Rational Cauchy sequences with explicit modulus
Pair `s:N_T→K`, `μ:N_T→N_T` satisfying a quantified tail inequality. Explain why existence of a modulus and a bare Cauchy predicate are distinct in constructive logic. **Lean:** `TreeAnalysis/CauchyData.lean`: `CSeq`, `IsModulus`, `SeqEquiv` (check exact source line). **Literature:** [BB], [L], [G].

### 12.3. Equivalence relation, regularization and quotient carrier
Define eventual closeness, regularization and `R(K)=C(K)/∼`; construct well-definedness of operations by congruence. **Lean:** `TreeAnalysis/CauchyData.lean`: `isRegular_reg` L130; `seqEquiv_trans` L162; `reg_equiv` L144; `TreeAnalysis/RealQuotient.lean`: `TreeR` L42, `mkR` L51.

### 12.4. Commutative ring laws and rational embedding
Prove nontrivial commutative ring and injective ring homomorphism `K→R(K)`. **Lean:** `TreeAnalysis/RealQuotient.lean`: `instCRing` L161; `ofQ_injective` L195; `zero_ne_one` L204. Do not replace “ring” by “field” here.

### 12.5. Positive cone, weak order, strict order and apartness
Define `<`, `≤`, `#`, show required order laws (including cotransitivity where proved) and “tightness” of apartness. **Lean:** `TreeAnalysis/RealOrderApartness.lean`: `RLt` L69; `RLe` L71; `RApart` L77; `lt_trans` L172; `le_antisymm` L187; `eq_of_not_apart` L292. **Literature:** [BB], [BR].

### 12.6. Separated inversion versus ordinary non-equality
When `x # 0`, construct reciprocal, and distinguish this from `x≠0`. Cancellation under `x≠0` remains provable. **Lean:** `TreeAnalysis/RealOrderApartness.lean`: `rinv` L330, `mul_rinv` L335, `exists_inv_of_apart` (near L375); `TreeAnalysis/ApartnessStrength.lean`: `mul_left_cancel_of_ne` L64.

### 12.7. Density, Archimedean control, arity transfer
Quantitative rational approximation within `ε_k`, compatible isomorphisms of completions for qualifying alphabets, and the exact archimedean propositions from the code. **Lean:** `TreeAnalysis/CompletenessScope.lean`: `rat_dense` L127; `TreeAnalysis/ArityCompletionTransfer.lean`; `TreeAnalysis/FoundationsClosure.lean`: `realArityIso_comp` L146.

## 13. Convergence and constructive completeness scope

### 13.1. Convergence of embedded rational Cauchy sequences
A modulated rational sequence, embedded termwise, converges to its own quotient class; uniqueness of limits. **Lean:** `TreeAnalysis/CompletenessScope.lean`: `limit_unique` L89, `ofQ_seq_converges` (find exact source declaration).

### 13.2. Tracked real Cauchy sequences and the diagonal theorem
Define tracked data (real Cauchy modulus plus rational approximants and precision schedule); construct limit via diagonal rational sequence and prove convergence. **Lean:** `TreeAnalysis/CompletenessStrength.lean`: `ApproxData` and `limit_of_approx` L306; `TreeAnalysis/CompletenessScope.lean`: `tower_limit` L271.

### 13.3. Closure of tracked families under finite expressions
The class of tracked sequences is closed under constants, negation, sums and products given adequate bounds; limits commute with such finite algebraic expressions. **Lean:** `TreeAnalysis/ApproxClosure.lean`: `Tracked.converges` L262; `TreeAnalysis/TrackedExpressions.lean`: `lim_tracked` L66; `converges_evalSeq` L85.

### 13.4. Unrestricted modulated completeness and Cauchy approximation
State the precise equivalence `(UnrestrictedCompleteness K)↔(CauchyApprox K)` for *sequences with a supplied Cauchy modulus*; avoid “unrestricted” in prose without the qualification. **Lean:** `TreeAnalysis/LiftingPrinciples.lean`: `complete_iff_cauchyApprox` L124.

### 13.5. Choice principles and modulus-free completeness
Specify and display `ChoiceNN`; resulting conditional modulated and modulus-free completeness. No necessity or converse to choice was proved. **Lean:** `TreeAnalysis/LiftingPrinciples.lean`: `complete_of_choice` L245; `modulusFreeComplete_of_choice` L249. **Literature:** [L], [G].

### 13.6. Least upper bounds with explicit approximation data
Define `SupData`; prove least upper bound for data-bearing sets, singleton/finite-set cases and conditional monotone families. Do not generalize to *every* bounded inhabited set. **Lean:** `TreeAnalysis/SupremumScope.lean`: `isLUB` L65; `ofList_isLUB` L152; `tower_monotone_lub` L182.

### 13.7. Continuation of uniformly continuous maps
For rational self-maps with supplied modulus, extend to quotient representatives; check representative independence, composition and uniqueness under the stated continuity predicate. Avoid a false general universal mapping property of all completions. **Lean:** `TreeAnalysis/CompletionCharacterization.lean`: `UCMod` L39; `extendR` L53; `extendR_unique` L94; `extendR_comp` L111.

## 14. Logical strength of additional properties

### 14.1. Markov principle and inverse existence
Precisely state the equivalence between inversion for all `x≠0` and the project's Boolean-sequence form of Markov's principle. Explicitly name the base `TOField K` hypothesis. **Lean:** `TreeAnalysis/ApartnessStrength.lean`: `inv_iff_markov` L349. **Literature:** [BR], [L].

### 14.2. LPO and real trichotomy / zero-versus-apartness
Correctly distinguish `ZeroOrApart`, trichotomy, and `LPO`; state only precisely proved bi-implications. **Lean:** `TreeAnalysis/ApartnessStrength.lean`: `zeroOrApart_iff_lpo` L369; `TreeAnalysis/FoundationsClosure.lean`: `trichotomy_iff_lpo` L230.

### 14.3. WLPO and decidable zero
`DecidableZero ↔ WLPO` in the project's definitions. **Lean:** `TreeAnalysis/FoundationsClosure.lean`: `decidableZero_iff_wlpo` L199.

### 14.4. Logical lower bounds for global Suprema and monotone convergence
`UnrestrictedLUB⇒WLPO`, `BoundedMonotoneConvergence⇒LPO`; neither converse nor independence is part of the project's conclusions. **Lean:** `TreeAnalysis/SupremumScope.lean`: `wlpo_of_unrestrictedLUB` L257; `lpo_of_bmc` L312. **Literature:** [BR], [L].

### 14.5. What “constructive” establishes and does not establish
Differentiate absence of `Classical.choice` in the archived theorem closures from metatheoretic independence; built-in `Quot.sound`, `propext`, and structural recursion are allowed. **Literature:** [L], [BR].

## 15. Relationships and nonidentifications among the structures

### 15.1. Same arithmetic field, different finite child-space ranks
For `b,c≥2`, rational fields are isomorphic; the attached coordinate modules have ranks `b` and `c` and transverse ranks `b−1` and `c−1`. These statements concern **different invariants**.

### 15.2. Primitive path counts do not distinguish rays
A single prefix-count sequence is `n` for every ray and is not Cauchy. Consequently this primitive observation alone cannot label ray ends by distinct real limits. This is not a universal no-go for all additional encodings.

### 15.3. Boundary, algebraic direct limit, and numerical completion
Formally disjoint constructions with different operations and topologies; no isomorphism, quotient map, metric identification, smooth atlas or transport of longitudinal vectors follows automatically.

### 15.4. Root and endpoint levels
The root has **graph depth 0**. In the archived code `vertexLevel(root)=finite 0`, while `rayLevel(ξ)=posInfinity` is a conventional marker. The originally discussed `negInfinity` label for the root is **not** the implemented label. Explain the exact present theorem, do not retroactively claim the stronger convention. **Lean:** `TreeFoundation/ExtendedLevels.lean`: `vertexLevel` L50; `rayLevel` L54; `root_level` L57; `first_edge_unit` L60.

## 16. Scope limitations and open questions

### 16.1. Algebraic universal properties
A general universal property of the free natural semiring, integer Grothendieck completion, fraction field, or Cauchy completion is not established by the specific proved isomorphisms. **Code ledger:** `FINAL_OPEN_QUESTIONS.md`, `FINAL_AXIOM_AND_LAW_MATRIX.md`.

### 16.2. Cauchy completeness without supplied representatives/moduli
Differentiate modulated and modulus-free completeness, selection of representatives, choice assumptions and the exact equivalence proved. No blanket unprovability claim. **Literature:** [L], [G].

### 16.3. Strong classical real-field and order axioms
Conventional nonzero inversion requires MP in the proved characterization; trichotomy requires LPO; full LUB and Dedekind completeness remain unproved. A constructive Cauchy ring is not automatically a conventional complete ordered field.

### 16.4. Infinite-line compatibility obstruction
No nonzero all-ones finite-support vector; no compatible zero-padding family of finite uniform lines. A different ambient space/identification could lead to other questions but is **outside** proved premises.

### 16.5. Boundary-topological limits and missing conditions
Finite-arity boundary compactness is not established by the code; positive-dimensional manifold obstruction is conditional on the precise interval-connectedness predicate; native boundary does not come with a canonical numerical coordinate map.

### 16.6. Full automorphism classification
Levelwise-permutation completeness is **refuted**, not open. Characterizing the full automorphism group is an independent unaddressed question.

### 16.7. Systematic separation of statuses
A concise claims table may be included in a supplemental appendix, but the main paper should state the hypotheses directly in theorem statements. Never describe an unfinished proof attempt as a no-go theorem.

## 17. Conclusion

### 17.1. Statements established under the exact hypotheses
Succinctly recapitulate the **actual mathematical results**: path-count ordered semiring, normalized integers, triple-path ordered field, explicit finite-rank decomposition, infinite transverse direct limit and compatibility obstruction, native ray boundary topology, and quotient-based constructive Cauchy algebra with tracked convergence.

### 17.2. Delineation of open properties
Explicitly mention global completeness, classical inversion and order principles, unrestricted supremum and noncanonical identifications. Avoid predictions and prospective physical interpretations.

## Supplementary material (not in the main mathematical narrative)

- **S1. Theorem-to-Lean correspondence.** Every important mathematical theorem in §§2–16 maps to a source path, fully qualified declaration name, *exact elaborated signature*, prerequisites and transitive axioms; include dimensions and topology this time.
- **S2. Verification manifest.** Source archive SHA-256, Lean 4.28.0, compiler options, full build command, fail-closed axiom audit, independent checker status and any nonreproduced claims.
- **S3. Property ledger.** Four statuses: unconditionally proved; conditionally proved; formally refuted; currently open/not formalized; distinguish “not investigated” from “not derivable.”
- **S4. Optional illustrations.** Definitions and finite-arity examples; no figure may imply a metric embedding, a spacetime dimension or an existing manifold structure.
- **S5. Bibliography with links and checked chapter-level topical relevance.**

## Primary-source and authorial reference registry

**[S]** Jean-Pierre Serre, *Trees*, Springer, English edition; chapter “Trees and Amalgams,” pp. 1–68. https://doi.org/10.1007/978-3-642-61856-7 . **Use for:** conventional tree structure and groups acting on trees; not the specific typed Lean implementation.

**[LP]** Russell Lyons and Yuval Peres, *Probability on Trees and Networks*, Cambridge University Press, 2016; author-hosted complete text and errata: https://rdlyons.pages.iu.edu/prbtree/prbtree.html . **Use for:** rooted trees, rays/ends, network terminology. Read chapters relevant to rooted trees before citing a named theorem.

**[K]** Alexander S. Kechris, *Classical Descriptive Set Theory*, Springer 1995; “Trees” pp. 5–12, “Compact Metrizable Spaces” pp. 18–28, “Locally Compact Spaces” pp. 29–30, “Zero-dimensional Spaces” pp. 35–40. https://doi.org/10.1007/978-1-4612-4190-4 . **Use for:** Cantor/Baire spaces, product/prefix topologies, zero-dimensionality, compactness; do not silently import classical arguments into Lean results.

**[A]** Sheldon Axler, *Linear Algebra Done Right*, 4th ed., Springer open access (2024), DOI https://doi.org/10.1007/978-3-031-41026-0 ; author's updated free PDF: https://www.linear.axler.net/ . Chapters 1–3 (vector spaces, bases, dimensions), 6 (inner products). **Use for:** standard module/vector-space terminology and finite direct sums, not a proof of a claim specific to tree labels.

**[B]** Hyman Bass, María Victoria Otero-Espinar, Daniel Rockmore, Charles Tresser, *Cyclic Renormalization and Automorphism Groups of Rooted Trees*, Springer Lecture Notes in Mathematics (1996); section “Spherically transitive automorphisms of rooted trees,” pp. 103–133. https://doi.org/10.1007/BFb0096321 . **Use for:** automorphisms of rooted trees and proper distinction of classes of actions.

**[BB]** Errett Bishop and Douglas Bridges, *Constructive Analysis*, Springer 1985; Chapter 2 “Calculus and the Real Numbers” pp. 14–66, Chapter 4 “Metric Spaces” pp. 81–127. https://doi.org/10.1007/978-3-642-61667-9 . **Use for:** regular/Cauchy reals, moduli, constructive order and completeness.

**[BR]** Douglas Bridges and Fred Richman, *Varieties of Constructive Mathematics*, Cambridge University Press 1987; Ch. 1 (foundations, choice) and Ch. 2 (constructive analysis); https://doi.org/10.1017/CBO9780511565663 . **Use for:** intuitionistic logic, LPO, constructive logical distinctions. Verify exact proposition/page before associating a published result with a code-specific equivalence.

**[L]** Robert S. Lubarsky, “On the Cauchy completeness of the constructive Cauchy reals,” *Mathematical Logic Quarterly* **53** (2007), 396–414; https://doi.org/10.1002/malq.200710007 ; author page https://www.math.fau.edu/people/faculty/lubarsky/publications.php . **Use for:** constructive Cauchy-reals completeness without Countable Choice; **not** a formal independence theorem about this particular Lean development.

**[G]** Gaëtan Gilbert, “Formalising Real Numbers in Homotopy Type Theory,” arXiv:1610.05072 (2016); published CPP 2017, DOI 10.1145/3018610.3018614, https://arxiv.org/abs/1610.05072 . **Use for:** carefully scoped formal constructive completion, representative selection and choice issues; verify full title and latest publication metadata before final bibliography.

**[LEAN]** Lean official Language Reference, https://lean-lang.org/doc/reference/latest/ ; axioms and proof validation https://lean-lang.org/doc/reference/latest/ValidatingProofs/ . **Use for:** `Quot.sound`, `propext`, elaborated theorem signatures and kernel-audit methodology; this is supplementary technical documentation, not a mathematical source of the main theorems.

**Reference policy:** Cite the original author/publisher and section when known. Do **not** attribute a formally proved project-specific result directly to these general sources; the own proofs must appear in the paper. Do not cite any source merely because it mentions similar terminology.

## Project-chat execution instructions

1. Use this outline as the **scope contract**, not as a skeleton for a code walkthrough. First validate every referenced Lean name against the *frozen* source, especially where the map says “locate.”
2. Read all `PrimitiveTree`, `TreeFoundation`, `TreeNumbers`, `DimensionFoundation`, `BoundaryTopology`, and pertinent `TreeAnalysis` modules. Avoid relying exclusively on audit reports or the previous arithmetic-only draft.
3. For each subsection, draft its definitions and theorems in standard mathematical language, then write independent human-readable proofs with explicit assumptions. The code correspondence is a separate table produced alongside the paper.
4. Research/cite the primary sources above as actual context. Bibliographic entries must be verified; distinguish classical background theorems from constructive project theorems.
5. Identify coverage gaps *before* drafting: every substantive result in the frozen mathematical source should have a home in the outline or an explicit justified exclusion. Especially `DimensionFoundation` and `BoundaryTopology` must not disappear.
6. Do not modify the mathematics or assume additional axioms to force a desired result. If an asserted paper theorem lacks a Lean proof, weaken the prose to the exact proved signature or mark it open.
7. Draft only when the user subsequently requests the manuscript; this package is for preparation and organization.
