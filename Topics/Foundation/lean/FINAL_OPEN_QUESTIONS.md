# FINAL OPEN QUESTIONS

Exact statements that are **not** proved in this repository, with the proved implications that
surround them. `K` ranges over `{K : Type} [TOField K]`; the concrete case is `K = QStar`
(`TreeRStar = TreeR QStar`). Every principle below is a `def … : Prop` in the sources; none is an
axiom, an instance or a hypothesis of a released theorem other than the conditional theorems that
name it explicitly.

**No independence, necessity or unprovability result is formalized for any item.** A one-way
implication `P → LPO` (say) is a lower bound on the logical strength of `P`; it is neither a proof
that `P` is unprovable nor a converse. Results about other foundational systems are not imported.
The Task 04 register `FINAL_OPEN_PROBLEMS.md` (O1–O14) gives the longer discussion of each item;
this file supersedes it where they differ (only Q13 changed in substance).

| id | exact statement (Lean names) | proved around it | sufficient named premise |
|---|---|---|---|
| Q1 | `UnrestrictedCompleteness K := ∀ (f : TreeN → TreeR K) (ν : TreeN → TreeN), RCauchyMod f ν → ∃ L, ConvergesTo f L` (Cauchy sequences **supplied with a modulus**) | `complete_iff_cauchyApprox` (⇔ `CauchyApprox K`); holds for every family with approximation data (`limit_of_approx`), every `Tracked` family and every finite expression in tracked families (`TExpr.lim_tracked`), every rational-valued sequence with a real modulus | `ChoiceNN` (`complete_of_choice`); `SequenceLifting K`, `CauchySequenceLifting K` |
| Q2 | `ModulusFreeCompleteness K := ∀ f, RCauchy f → ∃ L, ConvergesTo f L` | `modulusFreeComplete_of_choice`; `complete_of_modulusFree : ModulusFreeCompleteness K → UnrestrictedCompleteness K` | `ChoiceNN` |
| Q3 | `ModulusSelection K := ∀ f, RCauchy f → ∃ ν, RCauchyMod f ν`; `RatModulusSelection K` | `modulusSelection_of_choice`, `ratModulusSelection_of_choice` | `ChoiceNN` |
| Q4 | reverse lifting arrows, e.g. `UnrestrictedCompleteness K → ChoiceNN`, `ChoiceNN → SequenceLifting K`, `ModulusFreeCompleteness K → ModulusSelection K` | only the forward arrows (see `REPORT_TASK03.md` §3) | — |
| Q5 | conventional inverses `∀ x : TreeR K, x ≠ 𝟘 → ∃ y, x * y = 𝟙` | `inv_iff_markov` (⇔ `MarkovPrinciple`); unconditional: `exists_inv_of_apart`, `not_not_exists_inv`, `mul_left_cancel_of_ne`, `eq_zero_of_mul_eq_zero_of_ne` | `MarkovPrinciple` (equivalent) |
| Q6 | `MarkovPrinciple := ∀ p : TreeN → Bool, ¬¬(∃ n, p n = true) → ∃ n, p n = true` | `markov_of_lpo`; ⇔ Q5 ⇔ `NeImpliesApart K` | `LPO` |
| Q7 | `LPO := ∀ p : TreeN → Bool, (∃ n, p n = true) ∨ (∀ n, p n = false)` | ⇔ `ZeroOrApart K` (`zeroOrApart_iff_lpo`) ⇔ `Trichotomy K` (`trichotomy_iff_lpo`); `lpo_of_bmc : BoundedMonotoneConvergence K → LPO` | — |
| Q8 | `WLPO := ∀ p : TreeN → Bool, (∀ n, p n = false) ∨ ¬(∀ n, p n = false)` | ⇔ `DecidableZero K` (`decidableZero_iff_wlpo`); `wlpo_of_lpo`; `wlpo_of_unrestrictedLUB` | `LPO` |
| Q9 | `UnrestrictedLUB K := ∀ S, (∃ x, S x) → (∃ b, IsUpperBound S b) → ∃ y, IsLUB S y` | `wlpo_of_unrestrictedLUB` (one way); with explicit data `SupData.isLUB` (the supremum is **data-dependent**: it is built from the supplied approximations), `SupData.ofList_isLUB`, `SupData.ofMonotone` | none known |
| Q10 | `BoundedMonotoneConvergence K := ∀ f, Monotone f → (∃ b, ∀ i, f i ≤ b) → ∃ L, ConvergesTo f L` | `lpo_of_bmc` (one way); with data `tower_monotone_lub`; under `ChoiceNN` for Cauchy monotone sequences `monotone_lub_of_choice` | none known |
| Q11 | `ZeroProductDisjunction K := ∀ x y, x * y = 𝟘 → x = 𝟘 ∨ y = 𝟘` and totality `∀ x y : TreeR K, x ≤ y ∨ y ≤ x` | `zeroProduct_of_zeroOrApart` (so from `LPO`); for totality nothing | `LPO` (zero product); none formalized (totality) |
| Q12 | a conventional `TField (TreeR K)` instance (total `inv`, `x ≠ 𝟘 → x * inv x = 𝟙`, `inv 𝟘 = 𝟘`) | Q5 and Q8 | `MarkovPrinciple` + `WLPO` (both from `LPO`); **not constructed** by design |
| Q13 | a non-constant map `Ray α → TreeR K` defined from primitive tree data without a distinguished letter choice | **Task 05:** every function on rays that is invariant under the tree automorphisms induced by levelwise permutations is constant (`RayAutomorphism.invariant_const`; swap invariance suffices, `swapInvariant_const`); earlier: prefix counts coincide for all rays and are not Cauchy (`prefixCount_indep`, `prefixCount_not_isCauchy`); the binary encoding depends on the letter choice (`encode_letter_choice_dependence`) | a letter choice (`TwoLetters`) gives the non-constant, non-invariant `encode` |
| Q14 | **Corrected (Task 05 Q14 repair).** The former entry — "every root- and incidence-preserving automorphism of the full tree is induced by a levelwise permutation (`RayAutomorphism.LevelPerm`)" — is **false** for every alphabet with two distinct letters, so it is no longer an open question. Correct statement: `RayAutomorphism.levelwise_converse_false (a b : α) (hab : a ≠ b) : ¬ ∀ T : TreeAut α, ∃ P : LevelPerm α, (treeAut P).toFun = T.toFun` (with `[DecidableEq α]`). **Status: counterexample proved** (kernel-checked, no axioms). Witness `RayAutomorphism.subtreeSwapAut a b`: swaps the child subtrees rooted at `a :: [a]` and `b :: [a]` (descendants included, `subtreeSwap_append`), fixes all first-level vertices and all other subtrees; it is its own explicit inverse and preserves/reflects parent incidence. `subtreeSwapAut_not_levelwise`: it changes the new letter of `a :: [a]` (to `b`) but not that of `a :: [b]`, whereas any `treeAut P` gives both the same new letter `P.perm one a` (both parents have depth `one`; the level-zero action `P.perm zero` only moves the parent letters). Instances: `binary_levelwise_converse_false` (`Child two`), `omega_levelwise_converse_false` (`TreeN`). | `RayAutomorphism.treeAut` (levelwise ⇒ automorphism), `invariant_const`, `swapInvariant_const` remain valid and unchanged. Not attempted: a classification of the full automorphism group (e.g. by vertex-dependent child permutations); no such statement is claimed. | — (refuted, not open) |
| Q15 | universal property of `TreeZ` (group completion of `(TreeN,+)`), of `FracQ`/`TreeQ α` (field of fractions), and of `TreeR K` (completion) w.r.t. arbitrary structures | only concrete facts: `fieldIso_unique`, `realIso_unique`, `extendR_unique` (uniformly continuous maps `K → K`) | — (no generic interface for these universal properties) |
| Q16 | Dedekind completeness of `TreeR K` | not formulated; Q9 is the closest formulated statement | — |

## Clarifications (to prevent misreading)

* **Not open:** all field axioms of `TreeQ α` for alphabets with two letters
  (`Task04.treeQ_certificate`); the ordered-field isomorphism `TreeQ α ≅ FracQ`
  (`TreeQ.orderedFieldIsoFracQ`); the commutative-ring laws of `TreeZ` and `TreeR K`; the
  integral-domain disjunction for `TreeZ`; the ordered-semiring isomorphism
  `TreeN ≅ DepthClass α` given a letter (`DepthQuotient.depthIso`).
* **Obstructions (proved, specific):** the one-letter alphabet admits no valid triple with zero
  numerator, so the pairwise-distinct *triple presentation* fails there
  (`unary_no_universal_witness`, `unary_toFracQ_ne_zero`); this is **not** a statement that no
  rational field can be built from unary-path counts — `FracQ.instTField` is such a field. An
  alphabet without letters represents no positive count in the depth quotient
  (`DepthQuotient.no_positive_count_of_noLetter`).
* The classical observation that each of `MarkovPrinciple`, `LPO`, `WLPO`, `ChoiceNN` follows
  from excluded middle / choice is **not** used and not formalized in the release (the reviewer's
  `ClassicalProbe.lean` was not supplied and is in any case excluded from the release). Merely as
  a logical remark: the conditional theorems above show that, in a classical metatheory, `TreeR`
  would satisfy Q1, Q2, Q5–Q8, Q11 (zero product) and Q12 — this is not a theorem of this
  project.
