# Summary of changes for run bce2b6c2-1d8d-47f6-8ea1-bdb61067db09
Task 06 is finished: all three requirements are proved in Lean, and I found no mathematical obstacle. No existing definition or theorem changed. The new modules add no carriers, structures, instances, axioms or classical reasoning, and no `sorry` remains. `./scripts/verify_release.sh` ran once on the final sources and passed (exit 0).

**Requirement 1: `dot` is bilinear** (`DimensionFoundation/BilinearForm.lean`). This uses only the existing `ChildModule.dot`, the finite-sum lemmas (`FinSum.sumC_add`, `sumC_mul_left`, `sumC_congr`) and the internal field laws.
- The four identities are `dot_addV_left`, `dot_addV_right`, `dot_smul_left` and `dot_smul_right`.
- `dot_bilinear_symmetric` combines them with the existing `dot_comm`.
- There are also small identities for the zero vector and negation.
- None of these depends on any axiom. I proved only that the form is symmetric and bilinear; nothing about positivity, so it is not called an inner product.

**Requirement 2: projection laws** (`DimensionFoundation/ProjectionLaws.lean`). Every result assumes a positive arity, `hb : TreeN.PathLT TreeN.zero b`.
- **Identity actions:** `proj_of_inL` gives `projL x = x` and `projS x = 0` on `InL`. `proj_of_inS` gives `projL x = 0` and `projS x = x` on `InS`. Both come directly from the existing `decomposition_unique`.
- **Idempotent and complementary:** `projL_idem`, `projS_idem`, `projL_projS`, `projS_projL` and `projL_addV_projS` follow from these. `projections_idempotent_complementary` states them together.

**Requirement 3: optional extras, all proved.**
- **Linearity:** `projL_addV`, `projL_smul`, `projS_addV`, `projS_smul`. These need no positivity assumption.
- **Images:** `range_projL` (the image of `projL` is exactly `InL`) and `range_projS` (the image of `projS` is exactly `InS`).
- **Kernels:** `inS_iff_projL_eq_zero` (the kernel of `projL` is exactly `InS`) and `inL_iff_projS_eq_zero` (the kernel of `projS` is exactly `InL`).
- **Orthogonality:** `dot_inL_inS`, `dot_projL_projS` and `dot_projS_projL`.
- **Splitting:** `dot_split` shows \(\langle x,y\rangle = \langle P_Lx,P_Ly\rangle + \langle P_Sx,P_Sy\rangle\).

The projection results depend only on `Quot.sound`, which comes from function extensionality, used to prove two vectors equal. The existing `decomposition` theorems depend on it in the same way. Arity zero needs no separate treatment: `Child zero` is empty, so the space has one element and every identity holds trivially.

**Other files changed:**
- `TreeFoundations.lean`: two new import lines.
- `ReleaseAudit/Run.lean`: 13 more required declarations, 60 in total.
- `scripts/gen_matrix.py`: three appended rows. `FINAL_AXIOM_AND_LAW_MATRIX.md` was regenerated and now has 159 rows, 132 proved.
- `release/`: verification output, declaration signatures, inventory and module graph refreshed.
- `VERIFICATION_LOG.md`: new §6.
- New report `TASK06_BILINEAR_PROJECTION_REPORT.md`, with exact signatures, assumptions, line locations, `#print axioms` results and the proof-correspondence addendum for the dimension section.

**Verification run:**
- The starting fingerprint `44a6935b…2075` matched before I edited anything.
- New fingerprint `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`, over 75 files, commit `2897ec5`.
- Build: 67 jobs, successful.
- Source check: passed on 64 files.
- Fail-closed audit: passed on 3014 constants, with nothing outside `propext` and `Quot.sound`, and all 60 required declarations present.
- All negative fixtures behaved as expected.
- The bundled `leanchecker` passed on both libraries and every module group. It replays proofs with the same Lean kernel, so it is not a fully independent checker.

The scripts had lost their executable bit again, so the first attempt to run the release script stopped with `Permission denied` before any step ran. I restored the bit, this time recorded in git, with contents unchanged; the passing run above is the only one that executed. The four new results are in the Properties table, marked proved.

# Summary of changes for run ca064ed7-52d8-41b0-8982-c27c3783f36a
Q14 is repaired. The old converse ("every root- and incidence-preserving tree automorphism is levelwise") is false whenever the alphabet has two distinct letters, and Lean now checks a counterexample for it. The new results use no axioms at all, and `./scripts/verify_release.sh` ran once on the final source tree and passed (exit 0).

**The counterexample** is in the new module `TreeFoundation/AutomorphismCounterexample.lean`. It needs only decidable equality of the alphabet.
- **The map:** `RayAutomorphism.subtreeSwapAut a b : TreeAut α` swaps the two child subtrees rooted at `a :: [a]` and `b :: [a]`, including every descendant (`subtreeSwap_append_aa`, `subtreeSwap_append_ba`). It fixes all first-level vertices and every other subtree (`subtreeSwap_append_fixed`).
- **Automorphism:** the map is its own explicit inverse, preserves the root, and preserves and reflects parent–child links.
- `subtreeSwapAut_not_levelwise (a b) (hab : a ≠ b) (P : LevelPerm α) : (treeAut P).toFun ≠ (subtreeSwapAut a b).toFun`.
  - A levelwise permutation gives `a :: [a]` and `a :: [b]` the same new letter `P.perm one a`, because both parents have depth one. The level-zero permutation only moves the parent letters.
  - The swap instead gives the new letters `b` and `a`, which would force `a = b`.
- `levelwise_converse_false (a b) (hab : a ≠ b) : ¬ ∀ T : TreeAut α, ∃ P : LevelPerm α, (treeAut P).toFun = T.toFun`.
- Instances: `binary_levelwise_converse_false` for `Child two`, using the existing letters `Child.first` and `Child.second`, and `omega_levelwise_converse_false` for `TreeN`.

The existing `RayAutomorphism.treeAut`, `invariant_const` and `swapInvariant_const` are unchanged and still valid.

**Other changes:**
- `TreeFoundations.lean` gains one import line.
- `ReleaseAudit/Run.lean` now requires four more declarations, 47 in total.
- `scripts/gen_matrix.py` has one appended row. The regenerated `FINAL_AXIOM_AND_LAW_MATRIX.md` has row 156 (PROVED, no axioms) and now counts 129 proved; `release/declaration_signatures.txt` was regenerated with it.
- Q14 in `FINAL_OPEN_QUESTIONS.md` now reads "counterexample proved", with the corrected statement.
- `VERIFICATION_LOG.md` has a corrected §2 and a new §4a for the final run.
- `release/verification_output.txt`, `source_inventory.txt` and `module_dag.txt` were refreshed from the final files.
- New report: `TASK05_Q14_REPAIR_REPORT.md`.
- I did not change `FINAL_OPEN_PROBLEMS.md` or `FINAL_FOUNDATIONS_REPORT.md`: neither states the false converse, and the log already treats them as historical records. All qualifications on `TreeR` are unchanged (completeness, apartness, Markov, LPO, WLPO, choice).

**Verification:**
- The new module built on its own: `Build completed successfully (18 jobs)`.
- **Release run:** fingerprint `44a6935b4ecb8de9a4215976eddd31da05f18f5a6b400c56ae7efbb7f2b52075`, commit `87b8348`, 73 source files, full rebuild (65 jobs).
  - Source check passed on 62 files.
  - The fail-closed audit passed on 62 modules and 2975 constants, with no axiom outside `propext` and `Quot.sound`, and all 47 required declarations present.
  - All negative tests behaved as expected.
  - The bundled kernel checker passed on both libraries and on every module group.
  - Final line: `RELEASE VERIFICATION PASSED`.
- The scripts had lost their executable bit, so my first attempt to run the release script stopped at `Permission denied` before any step ran. I restored the bit (contents unchanged); the passing run above is the only one that executed.

**Remaining gaps:**
- Nothing remains open for Q14 itself. As instructed, I did not try to classify the full automorphism group.
- `scripts/inventory.py` cannot run in this checkout, because the baseline commit it compares against is not in the git history. I regenerated the inventory with the same logic and kept the recorded provenance labels.
- The informational axiom report `ReleaseAudit/Report.lean` does not list the new declarations; the enforcing audit does cover them.

# Summary of changes for run 30309698-ee7b-4d80-899f-86a6402e4e27
Task 05 is done on top of the Task 04 repository. All carriers, relations, operations and existing theorem statements are unchanged: the received files I touched differ only in comments, plus new import lines in the two library roots. After a clean rebuild, `./scripts/verify_release.sh` ran to completion with exit 0 in about 4 minutes. No `sorry` remains, and every project constant depends on at most `propext` and `Quot.sound`.

**The four reviewer files (`ReviewProbes.lean`, `ComputeProbe.lean`, `ClassicalProbe.lean`, `FullAxiomScan.lean`) were not in the repository or anywhere in the environment.** None of them was replayed. Each objection in your brief was checked against the actual declarations instead (`REVIEW_DISPOSITION.md`).

**New results:**
- **Depth quotient of `TreeN`** (§2, `TreeNumbers/DepthQuotient.lean`)
  - For any alphabet, words with the same unit-edge sum are identified; `cls_eq_iff` shows a class depends only on that sum.
  - Given a letter, `DepthQuotient.depthIso` is an explicit ordered-semiring isomorphism with `TreeN`. Grafting gives `+`, repetition gives `·`, and `≤` is preserved and reflected.
  - The class does not depend on the letter, but the representative word does.
  - An alphabet with no letters represents no positive count; over the one-letter alphabet the quotient identifies nothing.
- **`TreeQ α` versus fractions** (§3, `TreeAnalysis/FractionCharacterization.lean`)
  - Two triples with equal path sums have the same class (`TreeQ.mk_eq_of_pathSum_eq`).
  - The fraction quotient `FracQ` is built only from `TreeZ` and positive `TreeN`, and is itself a field.
  - `TreeQ.orderedFieldIsoFracQ` is an ordered-field isomorphism, including `inv 0 = 0`. It does not depend on the choice of witness letters, and it is compatible with the arity maps and their uniqueness theorems.
  - The one-letter obstruction is confined to the triple presentation (`TriplePath.unary_obstruction_scope`).
- **Ray automorphisms** (§4, `TreeFoundation/RayAutomorphism.lean`)
  - A levelwise permutation of child symbols gives a tree automorphism with explicit inverse that preserves the root and parent–child links.
  - Explicit levelwise swaps send any ray to any other, so every automorphism-invariant function on rays is constant.
  - Only decidable equality of the alphabet is needed, so `b ≥ 2` is not required. The converse (every automorphism is levelwise) is not proved.
- **Tracked expressions** (§5, `TreeAnalysis/TrackedExpressions.lean`): finite expression trees built from tracked families have explicit limits, equal to the expression evaluated at the atoms' limits. This was the only extra result the existing lemmas gave; no completeness statement changed.

**Fail-closed audit (§7):**
- **Kernel-level check:** `ReleaseAudit/Run.lean` checks all 2938 project constants. It raises an error on any axiom other than `propext`/`Quot.sound`, on `Classical`, on `opaque`/`unsafe`/`implemented_by`, and on built-in number constants in handwritten declarations. Constants Lean generates for inductive types and for the `𝟘`/`𝟙` notation are exempt from the number check only; the exemptions are listed in the output. It also fails if any of 43 central declarations is missing.
- **Source-level check:** `scripts/source_check.py` scans comment-stripped sources for forbidden tokens, numeric literals and foreign imports, and fails if any file is not reachable from the library roots.
- **Negative fixtures:** `scripts/negative_fixtures.sh` generates its test files outside the repository. Each of 8 deliberate violations exits 1 (user axiom, classical, `sorry`, `Nat`, `native_decide`, `opaque`, missing declaration, empty environment), the positive control exits 0, and a bad source file makes the source check fail.
- **`leanchecker`:** the toolchain's bundled lean4checker passes with `--fresh` on both libraries and on all module prefixes. It re-checks with the same kernel, so it is not an independent verifier.

**Documentation (§6, §8):** misleading comments corrected (the interface classes do contain law fields; two nonexistent theorem names fixed; trivial lemmas flagged as sanity checks). Duplicate helpers are recorded but not merged: `pickD` and `ifD` are identical, but merging them would mean refactoring four received modules for no mathematical gain. Delivered files:
- `FINAL_PROVENANCE.md`
- `FINAL_AXIOM_AND_LAW_MATRIX.md`: 155 rows; 128 proved, 9 conditional, 6 obstructions, 11 open, 1 definition. Axioms are computed by Lean and match the Task 04 matrix on every carried-over row; types are in `release/declaration_signatures.txt`.
- `FINAL_OPEN_QUESTIONS.md`, `REVIEW_DISPOSITION.md`, `VERIFICATION_LOG.md` (baseline, discrepancy table, commands, fingerprint, limitations), `README.md`, and `release/` (inventory, import graph, full run output).

`TreeR` is not claimed to be a conventional field, an ordered field, or complete. Conventional inverses are equivalent to Markov's principle, trichotomy to LPO, deciding zero to WLPO, and completeness follows only from `ChoiceNN`; the unconditional versions remain open, with no independence claimed. I added 8 entries to the Properties table and marked the 6 properties proved.

# Summary of changes for run 49737920-41ab-4677-8eec-d96777e44fce
I finished Task 04 on top of the Task 03 repository. Every defining axiom of the semiring, ring, integral-domain and field structures claimed for `TreeN`, `TreeZ` and `TreeQ` is now a checked theorem. `TreeR` is classified as a constructive ordered ring, not a field or a complete ordered field. `lake build TreeFoundations TreeAnalysis Audit` succeeds with no errors or warnings, and no `sorry` remains.

No existing declaration, carrier, relation or operation was changed. The only edits to existing files are new import lines in `TreeFoundations.lean` and `TreeAnalysis.lean`.

**New results (five new modules):**
- **`TreeN` (`TreeNumbers/FoundationsLedger.lean`):**
  - induction, and recursion together with a proof that it is unique;
  - `zero ≠ one` and a total order.
- **`TreeZ` (same file):**
  - a strict order with trichotomy;
  - the order on `TreeN` is preserved and reflected when it is embedded in `TreeZ`;
  - sign rules.
- **Why two letters are needed (same file):** with a one-letter alphabet, no triple configuration has numerator zero, so the field construction fails there (`unary_no_universal_witness`).
- **Uniqueness of the arity isomorphisms (`TreeAnalysis/Canonicity.lean`):**
  - every field isomorphism between two rational fields `TreeQ α ≅ TreeQ β` is the existing comparison map (`fieldIso_unique`);
  - every order-preserving ring isomorphism between the completions equals `realArityIso` (`realIso_unique`);
  - the comparison maps compose correctly and commute with all embeddings;
  - they do not depend on which two letters are chosen, although the individual witness triples do.
- **Two new equivalences (`TreeAnalysis/FoundationsClosure.lean`):**
  - deciding whether a real is `0` is equivalent to WLPO (`decidableZero_iff_wlpo`);
  - trichotomy of the real order is equivalent to LPO (`trichotomy_iff_lpo`).
- **Approximation closure (E2, `TreeAnalysis/ApproxClosure.lean`):**
  - families of reals that come with a modulus and rational approximants are closed under `+`, `−`, `·` and scaling, with explicit output data;
  - their limits commute with these operations and do not depend on the data chosen;
  - with no data at all, convergent sequences are closed under `+`, `−` and `·`.
- **Certificates (`TreeAnalysis/Task04Summary.lean`):** one theorem per carrier lists its axioms. The conditional `TreeR` certificate keeps each extra principle visible in its statement.

**Status of `TreeR`:**
- **Proved:** it is a commutative ring with `0 ≠ 1`, with a tight, cotransitive strict order, Archimedean, with the rationals dense. Elements apart from `0` have inverses, and nonzero elements can be cancelled.
- **Conditional:** the usual inverse law `x ≠ 0 → ∃ y, x·y = 1` is equivalent to Markov's principle. Completeness follows from `ChoiceNN`. Unrestricted least upper bounds would imply WLPO, and bounded monotone convergence would imply LPO; both are one-way only.
- **Still open:** completeness without a hypothesis, the usual inverse law, LPO, WLPO and Markov's principle themselves, unrestricted least upper bounds, bounded monotone convergence, totality of `≤`, and a choice-free numerical value for rays. These are recorded in `FINAL_OPEN_PROBLEMS.md` (O1–O14). No independence or unprovability is claimed for any of them.

**Audit:** `#print axioms` was run on 403 declarations (all 141 new ones plus every earlier one cited in the matrix). Each depends on nothing, on `Quot.sound`, on `propext`, or on both; `Classical.choice` never appears. A full dependency trace of 22 central results finds no `Classical` constant. Built-in `Nat` appears only through helpers Lean generates automatically for every inductive type. A comment-stripped scan of the new modules finds no banned identifier or tactic and no numeric literal.

**Files:** `TASK04_BASELINE.md` (starting state, including seven places where earlier reports and the code disagree), `FINAL_PROPERTY_MATRIX.md` (131 rows: 109 proved unconditionally, 10 conditionally, 4 obstructions, 7 open, 1 definition), `FINAL_OPEN_PROBLEMS.md`, `FINAL_FOUNDATIONS_REPORT.md` (recommends RELEASE with the scope above), `Audit/AxiomAuditTask04.lean` and `Audit/axioms_task04.txt`. I did not attempt the optional tree-automorphism subsection.

I added 14 entries to the Properties table; the 13 properties are marked proved and the new definition stays in progress.

# Summary of changes for run 86e162c4-be88-4f65-8068-174be8007003
I extended the Task 02 repository with six new modules (Checkpoints A–F), a summary module and audit files. Unconditional sequential completeness is still not proved; it is open, and I claim no impossibility result. The rest of the work below is done and checked.

**Build and audit:** `lake build TreeAnalysis Audit` succeeds with no errors or warnings, and no `sorry` remains. No existing declaration was changed, and `TreeR K := Quot (CRel (K := K))` is untouched; the only edit to an existing file is seven new import lines in `TreeAnalysis.lean`. `#print axioms` was run on all 181 new declarations: each depends on nothing, on `Quot.sound`, on `propext`, or on both, and none uses `Classical.choice`. The raw output is in `Audit/axioms_task03.txt`. For 16 central results I also traced every constant they depend on (`Audit/closure_task03.txt`). No constant from `Classical` appears. Built-in `Nat` constants appear only through helpers Lean generates automatically for every inductive type, as in Tasks 01 and 02. `TASK03_BASELINE.md` records the starting inventory and six places where the Task 02 prose and the code disagree. For example, `NeImpliesApart` lives in the root namespace rather than `TreeR`, and `sup_of_supData` is named in a docstring but does not exist.

**Results (full statements and status labels in `REPORT_TASK03.md`):**
- **A — Cauchy notions:**
  - The two-sided real Cauchy inequality follows from the one-sided one by exchanging indices.
  - Rational and real Cauchy notions correspond exactly: `IsModulus` ⇔ `RCauchyMod`, and `IsCauchy` ⇔ `RCauchy`.
  - A regular representative approximates its real within `eps n` at every index `n` (`regular_close`).
  - Sharpened diagonal argument (`limit_of_approx`): a real Cauchy sequence with a modulus converges once you supply one rational per index with an explicit error schedule. No representatives are needed, and tracked towers supply such rationals.
- **B — completeness:**
  - `complete_iff_cauchyApprox` (both directions): completeness with a modulus is exactly equivalent to having rational approximation data for every Cauchy sequence with a modulus.
  - The weaker premise `CauchySequenceLifting K` suffices.
  - `ChoiceNN` alone (choice of `TreeN` values) gives completeness both with a modulus (`complete_of_choice`) and without one (`modulusFreeComplete_of_choice`). It is applied only to path-count numerators of dyadic approximants, never to quotient representatives. This is weaker than the Task 02 premise.
  - Still open: completeness with no hypothesis, and whether any of these principles is necessary.
- **C — inverses and algebra:**
  - `NeImpliesApart K` is equivalent to Markov's principle for Boolean tests on `TreeN`, so the usual inverse law `x ≠ 0 → ∃ y, x·y = 1` is too (`inv_iff_markov`).
  - Deciding `x = 0 ∨ RApart x 0` for every real is equivalent to LPO.
  - Without any extra principle: if `x ≠ 0` and `x·y = 0` then `y = 0`, nonzero reals can be cancelled, and equality is stable under double negation.
- **D — suprema:**
  - `SupData.isLUB`: `D.sup` is a genuine least upper bound, and least upper bounds are unique.
  - `SupData` is constructed for nonempty finite lists of explicit Cauchy data (by unions) and for monotone sequences given a modulus and approximants.
  - The unrestricted least-upper-bound property would imply WLPO, and bounded monotone convergence would imply LPO. Both remain open.
- **E — primitive data:**
  - For every ray, the raw prefix-count sequence `pathSum (prefixAt r n)` is **not** Cauchy in the project's own sense (tolerance 1, unit-edge increment).
  - That sequence is the same for every ray, so it cannot tell rays apart.
  - The Task 02 binary encoding depends on which letter is chosen as digit 1: swapping the letters changes the encoded value from 0 to 1.
- **F — extension:** a map `K → K` with a function-valued uniform-continuity modulus extends to `TreeR K`. The extension does not depend on representatives, agrees with the map on rationals, and is the unique extension continuous along rational approximants. This is not claimed as a universal property of the completion.

I added 16 entries to the Properties table and updated the comments on two Task 02 entries. Fourteen of the new properties are marked proved; the open one (unconditional completeness) and the new definition stay in progress.

# Summary of changes for run 2969d9b9-9217-40cb-acbd-f149c25c8d44
I built the Task 02 constructive completion on top of the Task 01 repository, which is unchanged except for one new library entry in `lakefile.toml`. Everything is in new `TreeAnalysis/*.lean` and `BoundaryTopology/*.lean` modules, gathered in `TreeAnalysis.lean`. `lake build` succeeds and no `sorry` remains. Every audited result depends only on a subset of `[propext, Quot.sound]` (`Audit/AxiomAuditTask02.lean`, raw output in `Audit/axioms_task02.txt`). `propext` comes from quotient exactness; `Classical.choice` is never used. The search for forbidden identifiers and tactics in the new files found matches only in comments. The full report, with the 20-row status matrix, exact theorem names and hypotheses, is in `REPORT_TASK02.md`.

**Proved:**
- **Rational order (A):** a decidable linearly ordered field structure on the triple-path rationals `TreeQ` (`TreeQ.instTOField`). The order comes from `TreeZ` cross products, does not depend on the representative, and agrees with the fraction and `TreeZ` orders. Absolute value, distance and the triangle inequality are proved. The scale \(\varepsilon_n = 1/2^n\), built by structural doubling in `TreeN`, eventually drops below any positive rational, with an explicitly computed index (`exists_eps_lt`).
- **Cauchy data (B):** three separate notions: `IsCauchy`, `IsModulus` and `IsRegular`. Any sequence with an explicit modulus can be resampled into an equivalent regular one (`reg`, `isRegular_reg`, `reg_equiv`). Two forms of Cauchy equivalence are shown to agree on regular sequences (`seqEquiv_iff_bishop`).
- **The quotient `TreeR` (B, C):** a quotient of Task 01 rational-class sequences with explicit modulus. Equality holds exactly when representatives are Cauchy-equivalent (`mkR_eq_iff`). The rational embedding is injective. `TreeR` is a commutative ring with \(0 \neq 1\); products get an explicitly shifted modulus rather than a reused one. The embedding chain `TreeN → TreeZ → Q★ → TreeR` is injective.
- **Inverses (C):** with an apartness witness, `mul_rinv` gives an inverse that does not depend on the witness, and its converse holds too.
- **Order (D):** transitivity, antisymmetry, tightness, cotransitivity, the Archimedean bound and rational density between positively separated reals (`exists_rat_between`). Trichotomy is not claimed.
- **Completeness:** rational approximants converge to their class. Tracked Cauchy towers have limits (`tower_limit`). Suprema exist when explicit approximation data is supplied (`SupData`).
- **Arity independence (E):** the completed lines for any two arities with at least two letters are isomorphic, preserving \(0, 1, +, \cdot, -, <\) (`realArityIso`, `finiteRealIso`, `finiteOmegaRealIso`).
- **Boundary topology (F):** the prefix topology has clopen cylinders as a basis. Distinct rays are separated when a differing position is supplied; from mere \(\neq\) only its double negation is proved. The unary boundary is a single point. With two or more letters there are no isolated points and no inhabited open set is connected. The omega boundary is nowhere locally compact.
- **Manifold questions (G):**
  - With two or more letters, no open set of the boundary has a chart into a point (`no_zero_dim_chart`).
  - The unary boundary is a 0-manifold.
  - `TreeR` with its interval topology has a global identity chart, and separation holds under a positive witness. This is a statement about the line itself, not the boundary.
  - An extra binary encoding of rays into `TreeR` is continuous but not injective (`encode_not_injective`).

**Conditional only:**
- **Inverse from \(x \neq 0\) alone:** holds exactly under the Markov-type premise `NeImpliesApart K`; the two are proved equivalent.
- **Unrestricted Cauchy completeness:** follows from `SequenceLifting K` (picking a representative for each term of a sequence of reals, a countable-choice principle). Without it, it is open. Lubarsky's independence result is cited as background only, not proved in Lean.
- **Extracting a modulus from a bare Cauchy predicate:** needs an explicit choice premise.
- **No chart into the line `TreeR`:** proved only assuming open intervals of `TreeR` are connected (`IntervalsConnected`), which is not proved.

**Not proved:** the unrestricted least-upper-bound property, monotone convergence, the intermediate value theorem, the universal property of the completion, compactness of finite-arity boundaries, and anything about \(\mathrm{TreeR}^d\) for \(d \geq 2\).

The Properties table now includes the main Task 02 results and the `TreeR` definition.

# Summary of changes for run 5a96bc3c-b0ca-47df-b53c-13129eed69c7
I built a standalone Lean 4 project that covers Checkpoints I–IV completely. Both targets (`TreeFoundations` and `Audit`) build with no errors or warnings, and no source file contains `sorry`, `admit` or `axiom`. The full theorem list for each checkpoint, the two audits and the design notes are in `REPORT.md`.

I removed the Mathlib dependency from `lakefile.toml` and `lake-manifest.json`, so the project uses only Lean's core logic: inductive types, `List` as a plain data structure, and `Quot`.

**What is built**
- **Checkpoint I — tree and `TreeN`.** `TreeN` is literally the type of lists of unit child steps. Addition is concatenation and multiplication is repeated concatenation, and every semiring law is proved by induction on paths. Strict order is an inductive relation, with a constructive comparison, decision procedures, cancellation (including by a positive factor) and a path-difference operation. Child alphabets are `Child b` (an index path with a proof that it is below `b`). The tree results are all proved: unique parent, unique root path, connectedness, no cycles, the child family at each vertex, and unbounded depth. The unit-edge sum is a fold over the actual root edges, and `unitSum_rootEdges` proves it equals depth.
- **Checkpoint II — `TreeZ`.** Integers are pairs of paths, made canonical by an explicitly proved normalization (one of the two options the spec allows). I proved the commutative-ring laws, `0 ≠ 1`, no zero divisors, cancellation by a nonzero factor, sign classification, absolute value and a total order.
- **Checkpoint III — `TreeQ`.** `TreeQ α` is the kernel quotient of valid triple-path configurations, with the relation `A·D' = A'·D` in `TreeZ`. The universal witness uses the addresses `0^m`, `1^n`, `0·1^(k−1)`, with the predecessor of `k` given explicitly. Operations build new triple-path witnesses and are lifted with compatibility proofs. `TreeQ` is proved to be a field of characteristic zero, with `inv 0 = 0` proved, for every arity `b ≥ 2` and for omega. Any two of these fields are proved isomorphic (`arityIso`).
- **Checkpoint IV — limits and dimensions.** The omega tree is proved to be the directed union of the finite-arity trees, for vertices and for edges. This is a union statement, not a proof of a categorical colimit. Other results proved here:
  - Rays are indexed by `TreeN`, and the identity ray shows that the union of finite-arity rays is proper.
  - `L_b` has rank one, and `S_b` has rank `b−1` with the explicit basis `e_{j+1}−e_0` (independence and spanning are proved directly).
  - The decomposition `F_b = L_b ⊕ S_b` exists and is unique; `S_one` is zero; child permutations preserve `dot`, `L_b` and `S_b`.
  - In the omega finite-support space the analogous basis is independent and spanning, and it is compatible with zero padding.
  - The all-ones function is not finitely supported, and zero padding does not preserve `L_b`. No canonical omega longitudinal line is claimed.

**Audits**
- **Text scan:** every forbidden identifier appears only in comments ("omega" also names the countably branching tree). There are no numeric literals in code.
- **Scan of the compiled declarations:** none of the 1271 project declarations references `Nat`, `Int`, `Fin`, `OfNat`, `Classical`, `propext` or the banned list functions. The exceptions are helper declarations Lean generates automatically for every inductive type (for example the ones behind `injection` and `cases`); in Lean 4.28 these use built-in `Nat` constructor indices internally. `REPORT.md` says this explicitly.
- **`#print axioms`** on 95 central results: every one depends on no axioms or only on `Quot.sound` (from the `TreeQ` quotient and from function extensionality). None uses `propext` or `Classical.choice`.

**Formulation choices you should know about**
- Words store the most recent step at the head of the list, so the edge from `w` along `c` goes to `c :: w`.
- Sections 6–7 are proved for any field built by the project, then restated for `TreeQ(b)` and `TreeQOmega` in `DimensionFoundation/Instances.lean`. This is because `TreeQ(one)` is not a field: a one-letter alphabet cannot support the field operations. The case `b = one` therefore uses `TreeQOmega`, which is proved isomorphic to every `TreeQ(b)`.
- "No undirected cycles" is stated as: there is no closed walk of positive length whose edges are all distinct.

No required objective is left open. I recorded 15 entries (14 properties and one definition) in the Properties table; all 14 properties are marked proved.