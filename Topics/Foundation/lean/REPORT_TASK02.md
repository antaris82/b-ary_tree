# Task 02 — Constructive Cauchy completion, real-number properties, tree-boundary topology

All new code lives in `TreeAnalysis/*.lean` and `BoundaryTopology/*.lean`, collected by the root
module `TreeAnalysis.lean` (library `TreeAnalysis` in `lakefile.toml`, now a default target).
The Task 01 sources (`PrimitiveTree`, `TreeNumbers`, `TreeFoundation`, `DimensionFoundation`)
were **not modified**; the only change to existing files is the new `TreeAnalysis` library entry
in `lakefile.toml`.  All new modules import and use the Task 01 `TreeN`, `TreeZ`, `Frac`,
`TriplePath`, `TreeQ`, `Ray`.

Build evidence: `lake build TreeAnalysis` → `Build completed successfully (39 jobs)`.
Axiom audit: `Audit/AxiomAuditTask02.lean`, output saved verbatim in `Audit/axioms_task02.txt`.

## Design decisions

* **Rational base `Q★ := TreeQOmega`** (`QStar` in `TreeAnalysis/RationalOrder.lean`), the
  quotient of valid triples of omega-branching root paths.  Everything analytic is developed
  generically over an interface `TOField K` (`TreeAnalysis/OrderedField.lean`), whose **only
  instance** is `TreeQ.instTOField : TOField (TreeQ α)` for every `α` with two letters, built
  from the triple-path quotient.  `TOField` packages: a decidable nonnegativity predicate,
  closure under `+`/`·`, totality, antisymmetry, and an explicit Archimedean bound *function*
  `archBound` (data, not an existential).
* **Precision scale** `twoPow : TreeN → TreeN` (structural doubling, no exponentiation) and
  `eps n := (natCast (twoPow n))⁻¹`.
* **Real carrier** `TreeR K := Quot CRel` over `CSeq K` (sequence `TreeN → K` + modulus
  `TreeN → TreeN` + proof of the modulus property).  Representatives are sequences of Task 01
  triple-path rational **classes**.  `TreeRStar := TreeR QStar`.
* Order on `TreeR`: `x < y :↔ RPos (y - x)` where `RPos` asks for a representative with an
  eventual **positive rational lower bound `eps k`**; `x ≤ y :↔ RNonneg (y - x)` (eventually
  `≥ -eps k` for every `k`); `RApart x y := x < y ∨ y < x`.

## Theorem list per checkpoint (all build-proved unless marked otherwise)

### Checkpoint A (`OrderedField`, `RationalOrder`, `DyadicPrecision`, `PathMax`)
* `TreeQ.instTOField` — the triple-path rationals form a decidable linearly ordered field
  (order derived from `TreeZ` cross products via `Frac.LEF`, invariance `Frac.lef_resp_left/right`,
  `TreeQ.nonnegQ_add/mul/total/antisymm`, explicit Archimedean bound `TreeQ.archQ_spec`).
* `TreeQ.le_ofF_of_lef`, `TreeQ.lef_of_le_ofF` — the quotient order agrees with the fraction
  cross-product order; `TreeQ.ofZ_le`, `TreeQ.le_of_ofZ_le`, `TreeQ.ofZ_add/mul/injective` —
  agreement with the `TreeZ` order and embedding; `TreeQ.pathLE_of_natCast_le` for `TreeN`.
* Order laws (`TOField.le_refl/le_trans/le_antisymm/le_total/decLE/decLT`, `add_le_add_left`,
  `mul_le_mul_of_nonneg_left`, `mul_pos`, …).
* Absolute value/distance: `abs_nonneg`, `eq_zero_of_abs_eq_zero`, `abs_zero`, `abs_neg`,
  `abs_add` (triangle), `abs_mul`, `dist_nonneg`, `dist_self`, `eq_of_dist_eq_zero`,
  `dist_comm`, `dist_triangle`.
* Precision: `eps_pos`, `eps_le_eps` (monotone), `eps_succ_add : eps (n+1) + eps (n+1) = eps n`,
  `eps_add` (shift law), `eps_three`, `three_eps_le`,
  `exists_eps_lt : 𝟘 < δ → ∃ n : TreeN, eps n < δ` (with explicit index `epsIndex`,
  `eps_epsIndex_lt`), `le_of_forall_le_add_eps`.

### Checkpoint B (`CauchyData`, `RealQuotient`)
* Three separate notions: `IsCauchy s` (∀ δ>0 ∃ N …, in `Prop`), `IsModulus s μ`
  (`∀ k m n, μ k ≤ m → μ k ≤ n → |s m - s n| ≤ eps k`), `IsRegular s`
  (`∀ m n, |s m - s n| ≤ eps m + eps n`).
* `isCauchy_of_isRegular`, `isModulus_of_isRegular`, `isCauchy_of_isModulus`.
* Regularization with explicit modulus: `reg : CSeq K → (TreeN → K)` (monotone resampling
  schedule `rho`), `isRegular_reg`, `reg_equiv : SeqEquiv (reg c) c.seq`, `reg_resp`.
* `exists_modulus_of_choice` — from a bare `IsCauchy` predicate a modulus is obtained **only
  under** the explicit premise `∀ P, (∀ k, ∃ N, P k N) → ∃ f, ∀ k, P k (f k)` (choice for
  `TreeN → TreeN`).  No modulus is extracted without it.
* `SeqEquiv` (difference tends to zero) with `seqEquiv_refl/symm/trans`; agreement with the fixed
  error formulation on regular sequences: `seqEquiv_iff_bishop`
  (`SeqEquiv s t ↔ ∀ n, |s n - t n| ≤ 2·eps n`).
* `TreeR`, `mkR_sound`, `mkR_exact`, `mkR_eq_iff : mkR a = mkR b ↔ SeqEquiv a.seq b.seq`.
* `ofQ`, `ofQ_injective`.

### Checkpoint C (`CauchyOps`, `RealQuotient`, `RealOrderApartness`, `Instances`)
* `addSeq` (modulus `k ↦ max (μ(k+1)) (ν(k+1))`), `negSeq`, `mulSeq` with explicit bound `bnd`
  (`abs_le_bnd`) and shifted modulus `mulMod` (`mulMod_isMod`) — the pointwise product is
  re-moduled, not assumed regular; `add_resp`, `neg_resp`, `mulSeq_resp`.
* `TreeR.instCRing : CRing (TreeR K)` (all commutative-ring laws), `TreeR.zero_ne_one`.
* `ofQ_add/neg/mul/zero/one`; `natR_injective/add/mul/one`; `ofZR_injective/add/mul`;
  `treeN_embedding_injective` (chain `TreeN → TreeZ → Q★ → TreeR`).
* Inverse under apartness: `ApartW x` (data-carrying witness), `rinv x h`,
  `mul_rinv : x * rinv x h = 𝟙`, `rinv_indep` (independent of witness), `inv_unique`,
  `exists_inv_of_apart : RApart x 𝟘 → ∃ y, x * y = 𝟙`, and the converse
  `apart_of_mul_eq_one : x * y = 𝟙 → RApart x 𝟘`.
* `NeImpliesApart K := ∀ x, x ≠ 𝟘 → RApart x 𝟘`; `exists_inv_of_ne_of_markov` and
  `markov_of_inv`: the conventional field axiom `x ≠ 0 → ∃ y, x·y = 1` is **equivalent** to
  `NeImpliesApart` (a Markov-type principle).  Unconditionally only
  `not_not_apart_of_ne : x ≠ y → ¬¬ RApart x y` is proved.

### Checkpoint D (`SeqOrder`, `RealOrderApartness`, `CompletenessScope`)
* Order: `lt_irrefl`, `lt_trans`, `le_refl`, `le_trans`, `le_antisymm`, `le_of_lt`,
  `lt_of_lt_of_le`, `lt_of_le_of_lt`, `not_lt_of_le`, `le_of_not_lt` (`¬ y < x → x ≤ y`),
  `le_iff_not_lt`, `add_lt_add_right`, `add_le_add`, `mul_le_mul_of_nonneg_left`,
  `mul_lt_mul_of_pos_left`, `mul_pos`, `zero_lt_one`, `ofQ_lt_ofQ`, `lt_of_ofQ_lt`.
* Apartness: `apart_irrefl`, `apart_symm`, `eq_of_not_apart` (tightness), `ne_of_apart`,
  `lt_cotrans : x < y → x < z ∨ z < y` (locatedness), `apart_cotrans`.  Trichotomy is **not**
  claimed.
* `archimedean : ∃ n : TreeN, x < natR n`, `archimedean_abs`,
  `exists_rat_between : x < y → ∃ q, x < ofQ q ∧ ofQ q < y`.
* D3(a): `ofQ_seq_converges c : ConvergesTo (fun n => ofQ (c.seq n)) (mkR c)`,
  `rat_dense`, `limit_unique`.
* D3(b): `TrackedCauchyTower K` (specified representatives `r : TreeN → CSeq K` and specified
  real modulus `ν`), diagonal sequence `diagSeq`, `tower_converges`,
  `tower_limit : ∃ L, ConvergesTo (fun i => mkR (T.r i)) L`.
* D3(c): `UnrestrictedCompleteness K` (stated, **not proved**), `SequenceLifting K`
  (every `TreeN → TreeR K` lifts to representatives), `complete_of_lifting :
  SequenceLifting K → UnrestrictedCompleteness K`, `complete_of_lifting_choice` (also from a
  bare `RCauchy` predicate, with additionally `ChoiceNN`).
* D4: `SupData S` (inhabited, upper rational bounds `u k`, approximating members `s k`) with
  `SupData.sup`, `le_sup`, `sup_approx`.

### Checkpoint E (`ArityCompletionTransfer`)
* `OFieldHom` (order-preserving field maps), `TreeQ.transferHom α β`, `transfer_le`,
  `transfer_abs`, `transfer_eps`, `mapSeq_resp`, `mapR`, `mapR_add/mul/neg/zero/one/lt/ofQ`.
* `realArityIso α β : RealIso (TreeR (TreeQ α)) (TreeR (TreeQ β))` (bijection preserving
  `0,1,+,·,-,<` in both directions), `finiteRealIso b c` for `b,c ≥ 2`,
  `finiteOmegaRealIso b`, `realArityIso_ofQ`.

### Checkpoint F (`Cylinders`, `PrefixTopology`, `TopologicalObstructions`)
* `Agree n r r'` (prefix agreement), `Cyl w`, `decCyl`; `Topology` structure (opens closed under
  finite intersection and arbitrary `Type`-indexed unions); `prefixTopology α` with
  `PrefixOpen U := ∀ r ∈ U, ∃ n, ∀ r', Agree n r' r → r' ∈ U`.
* `cyl_open`, `cyl_compl_open` (cylinders clopen), `isOpen_iff_cylinders` (basis).
* `separate_of_diff` (a supplied differing position gives disjoint cylinders),
  `exists_diff_of_separated` (conversely, separation yields a differing position),
  `not_not_diff_of_ne : r ≠ r' → ¬¬ ∃ n, r n ≠ r' n` (only the double negation from mere `≠`).
* Prefix uniformity: `agree_entourage_mono`, `agree_all_iff`; prefix-coherent completion:
  `PrefixCoherent`, `coherentLimit`, `coherentLimit_agree`.
* Unary: `unary_singleton`, `unary_isolated`.  Two letters (finite `b ≥ 2`, omega):
  `no_isolated`, `not_isolated`, `boundary_disconnected`, `open_not_connected` (no inhabited
  open set is connected), `connected_subsingleton`.  Omega: `cyl_not_compact`,
  `not_locallyCompactAt`.

### Checkpoint G (`ManifoldConditions`, `BinaryEncoding`, `RealLineManifold`)
* `Chart TX TY` (homeomorphism between open subsets, continuity via `ContinuousOn`),
  `chart_connected_transport`.
* `no_zero_dim_chart` (two letters: no chart into the one-point space at any point),
  `unaryChart`, `unary_zero_manifold` (unary boundary is a 0-manifold).
* `no_chart_of_connectedPairs` — no chart from an inhabited open set of the boundary into any
  space with `HasConnectedPairs`; `realTopology K`, `IntervalsConnected K`,
  `no_chart_into_real (hI : IntervalsConnected K) …` — **conditional** dimension-1 no-go.
* Extra construction (labelled extension): `Ray.encode : Ray α → TreeR K` (binary expansion,
  digits from two chosen letters), `encode_le_of_agree` (quantitative continuity),
  `encode_not_injective` (rays `0111…`, `1000…` with a supplied differing position have equal
  encodings).
* Positive control on the line itself: `ofQ_eps_lt_of_pos`, `lt_open_left`, `lt_open_right`,
  `separate_of_lt` (Hausdorff separation under a positive witness), `realIdChart`
  (global identity chart: `TreeR K` is a one-chart 1-manifold modelled on itself).

## Completion-status matrix

| # | Item | Status | Identifier(s) | Hypotheses | Reason |
|---|------|--------|---------------|------------|--------|
| 1 | Rational order from triple-path classes | PROVED | `TreeQ.instTOField`, `TreeQ.le_ofF_of_lef`, `TreeQ.lef_of_le_ofF`, `TreeQ.ofZ_le` | `[TwoLetters α]` | order from `TreeZ` cross products, invariance under fraction/triple equivalence, decidable via Bool lift |
| 2 | Abs value; `eps n → 0` | PROVED | `TOField.abs_add`, `abs_mul`, `eq_zero_of_abs_eq_zero`, `dist_triangle`, `exists_eps_lt` | `𝟘 < δ` | explicit Archimedean bound function `archBound` from path representatives |
| 3 | Ordinary rational Cauchy predicate | PROVED (definition + relations) | `IsCauchy`, `isCauchy_of_isRegular`, `isCauchy_of_isModulus` | — | — |
| 4 | Explicit-modulus regularization | PROVED | `reg`, `isRegular_reg`, `reg_equiv`, `reg_resp`; `exists_modulus_of_choice` CONDITIONAL | modulus data `CSeq`; for bare `IsCauchy` the choice premise | a modulus is a function; extracting it from `∀k∃N` in `Prop` is exactly choice `TreeN → TreeN` |
| 5 | Cauchy equivalence, quotient exactness | PROVED | `seqEquiv_trans`, `seqEquiv_iff_bishop`, `mkR_eq_iff` | regularity for the Bishop form | exactness via `Quot.lift` into `Prop` (uses `propext`) |
| 6 | Injective rational embedding | PROVED | `ofQ_injective`, `ofQ_add/mul/zero/one`, `treeN_embedding_injective` | — | — |
| 7 | `+`, `·`, commutative ring | PROVED | `TreeR.instCRing`, `zero_ne_one`, `mulSeq_resp` | — | explicit re-moduled product |
| 8 | Apartness and inverse | PROVED | `mul_rinv`, `rinv_indep`, `exists_inv_of_apart`, `apart_of_mul_eq_one` | `ApartW x` / `RApart x 𝟘` | inverse sequence with modulus from the positive witness |
| 9 | Inverse under only `x ≠ 0` | CONDITIONAL | `exists_inv_of_ne_of_markov`, `markov_of_inv`, `not_not_apart_of_ne` | `NeImpliesApart K` | the conventional axiom is *equivalent* to this Markov-type principle; not provable here, not refuted |
| 10 | Order laws, density, Archimedean | PROVED | `lt_trans`, `le_antisymm`, `le_of_not_lt`, `eq_of_not_apart`, `lt_cotrans`, `archimedean`, `exists_rat_between` | strict `<` with rational witness | trichotomy not claimed |
| 11 | Rational Cauchy convergence in `TreeR` | PROVED | `ofQ_seq_converges`, `rat_dense`, `limit_unique` | — | — |
| 12 | Tracked Cauchy towers | PROVED | `tower_limit`, `tower_converges` | `TrackedCauchyTower K` | diagonal of specified representatives |
| 13 | Unrestricted Cauchy completeness | CONDITIONAL (OPEN unconditionally) | `UnrestrictedCompleteness K`; `complete_of_lifting`, `complete_of_lifting_choice` | `SequenceLifting K` (+ `ChoiceNN` without modulus) | blocked step: choosing a representative of each `f i` (countable choice for a quotient); background literature (Lubarsky) shows independence over IZF-type theories — not an internal Lean theorem |
| 14 | LUB and stronger principles | sup with data: PROVED UNDER EXPLICIT CONDITIONS (`SupData.sup`, `le_sup`, `sup_approx`); unrestricted LUB, monotone convergence, IVT: NOT PROVED | — | `SupData S` | locatedness data supplied; arbitrary subsets give no approximants |
| 15 | Arity independence of completions | PROVED | `realArityIso`, `finiteRealIso`, `finiteOmegaRealIso`, `transfer_le`, `transfer_abs` | `[TwoLetters α] [TwoLetters β]`, `AtLeastTwo b` | Task 01 isomorphisms preserve order, abs, `eps`, Cauchy data |
| 16 | Prefix topology, separation | PROVED | `prefixTopology`, `cyl_open`, `cyl_compl_open`, `isOpen_iff_cylinders`, `separate_of_diff`, `exists_diff_of_separated`, `not_not_diff_of_ne` | separation needs a supplied differing position | equality of rays is not decidable |
| 17 | Classification unary / `b ≥ 2` / omega | PROVED (stated invariants) | `unary_singleton`, `unary_isolated`, `no_isolated`, `boundary_disconnected`, `open_not_connected`, `cyl_not_compact`, `not_locallyCompactAt` | `TwoLetters α`; omega for compactness results | compactness of finite-arity boundary NOT PROVED (would need a fan-theorem-type principle); "Cantor/Baire space" names not claimed beyond these invariants |
| 18 | Manifold / no-go under natural topology | dim 0, `b ≥ 2`/omega: FORMAL NO-GO (`no_zero_dim_chart`); unary: PROVED 0-manifold (`unaryChart`); dim 1 into `TreeR`: CONDITIONAL (`no_chart_into_real`); general: `no_chart_of_connectedPairs` | `IntervalsConnected K` for dim 1 | connectedness of real intervals not proved constructively here; higher `d`: `TreeR^d` not formalized (OPEN, would follow from `HasConnectedPairs` of the model) |
| 19 | Extra map / quotient | PROVED properties of a labelled extension | `encode`, `encode_le_of_agree`, `encode_not_injective`; `realIdChart`, `separate_of_lt` | choice of two letters as digits | encoding continuous but not injective; no manifold structure on the boundary is produced; the line `TreeR` itself has the identity chart |
| 20 | Dependency / axiom audit | DONE | `Audit/AxiomAuditTask02.lean`, `Audit/axioms_task02.txt` | — | see below |

## Axiom audit (from `Audit/axioms_task02.txt`)

Every audited declaration depends on a subset of `[propext, Quot.sound]`; many depend on no
axiom at all (e.g. `TOField.exists_eps_lt`, `TOField.reg_equiv`, `Ray.cyl_open`,
`Ray.no_isolated`, `Ray.not_locallyCompactAt`, `Ray.no_zero_dim_chart`).  Examples:

* `TreeQ.instTOField`: `[Quot.sound]`; `TreeR.instCRing`: `[Quot.sound]`;
  `TreeR.mul_rinv`: `[Quot.sound]`; `TreeR.archimedean`: `[Quot.sound]`;
* `TreeR.mkR_exact`: `[propext]`; `TreeR.ofQ_injective`: `[propext]`;
* `TreeR.exists_rat_between`, `TreeR.lt_cotrans`, `TreeR.tower_limit`,
  `TreeR.complete_of_lifting`, `TreeR.SupData.le_sup`, `no_chart_into_real`:
  `[propext, Quot.sound]`;
* `realArityIso`, `finiteRealIso`, `finiteOmegaRealIso`: `[Quot.sound]`.

`propext` enters only through quotient **exactness** (`mkR_exact`: lifting the relation
`CRel a` to a `Prop`-valued function on the quotient requires identifying equivalent
propositions) and through Core lemmas about `Prop`-valued rewriting; it is not used as a
classical principle.  No `Classical.choice` appears anywhere.

## Source firewall audit

`grep -w` over `TreeAnalysis.lean`, `TreeAnalysis/*.lean`, `BoundaryTopology/*.lean` for
`Nat Int Rat Fin PNat UInt* USize BitVec Real Classical classical noncomputable omega norm_num
ring linarith simp simpa sorry admit axiom unsafe partial implemented_by native_decide aesop
decide length replicate range` and for numeric literals: all matches are in comments/docstrings
(English words such as "ring", "omega branching", "axiom audit", and `b ≥ 2` in prose).  No
code use.  All indices, moduli and bounds are `TreeN`.

## Remaining gaps (exact)

* `UnrestrictedCompleteness K` unconditionally (needs `SequenceLifting K`, a countable-choice
  principle for the quotient).
* Total inverse from `x ≠ 0` (equivalent to `NeImpliesApart K`).
* Unrestricted least-upper-bound property, monotone convergence for arbitrary bounded
  sequences, intermediate value theorem: not attempted beyond `SupData`.
* Universal property of the completion (D5): not formalized (no category of constructive metric
  spaces was built).
* `IntervalsConnected K` (connectedness of `TreeR` intervals): not proved, so the dimension-1
  boundary no-go is conditional; `TreeR^d` for `d ≥ 2` is not formalized.
* Compactness of finite-arity boundaries: not proved.
