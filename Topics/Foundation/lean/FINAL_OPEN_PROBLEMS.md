# FINAL OPEN PROBLEMS — permanent register for the number-foundation phase

Every item lists six fields:
(1) the proposition and its quantifier scope;
(2) what is already proved (proved implications only);
(3) the exact missing construction or step;
(4) whether a negative result exists for the same formulation;
(5) the minimum explicitly named assumption known to suffice;
(6) whether necessity, independence or unprovability has been proved.

`K` ranges over `{K : Type} [TOField K]`. The concrete instance of interest is `K = QStar`, so
`TreeR QStar = TreeRStar`. All principles are `def … : Prop` in the repository. None is an
axiom or an instance.

Common answer to field (6) for **every** item below: **no** necessity, independence or
unprovability result is formalized in this repository. A failure to find a proof is not a proof
of underivability. Results about other foundational systems are not imported and are not
claimed to apply.

---

## O1. Unconditional sequential completeness with modulus

1. `∀ K, UnrestrictedCompleteness K`, i.e. `∀ (f : TreeN → TreeR K) (ν : TreeN → TreeN), RCauchyMod f ν → ∃ L, ConvergesTo f L`.
2. `complete_iff_cauchyApprox` (it is equivalent to `CauchyApprox K`).
   `complete_of_choice : ChoiceNN → UnrestrictedCompleteness K`.
   `complete_of_lifting`, `complete_of_cauchyLifting`, `complete_of_seqApprox`.
   It holds unconditionally on these classes of inputs:
   * every family with approximation data (`limit_of_approx`);
   * every `Tracked` family, and the class of tracked families is closed under `+`, `-`, `·`
     and scaling (`Tracked.add/neg/mul/smulQ/smulRep`);
   * every tracked tower (`tower_converges`);
   * every rational-valued sequence `ofQ ∘ s` with a real modulus
     (`Task04.treeR_convergence_certificate`, last conjunct).
3. The missing step is a selection function. From `∀ i, ∃ q, RClose (f i) (ofQ q) (eps i)`
   (`exists_rat_close`, obtained by `Quot.ind` into `Prop`) one must produce
   `∃ q : TreeN → K, ∃ M, ApproxData f q M`. `Quot.lift` cannot do this: it would need a function
   on sequences of representatives, and the quotient of single reals does not provide one.
4. None.
5. `ChoiceNN` (selection of `TreeN`-valued indices for `TreeN`-indexed families). Also
   `SequenceLifting K`, `CauchySequenceLifting K`, `SequenceApprox K` or `CauchyApprox K`
   (the last is equivalent to the target).
6. Not proved (see the common answer).

**E3 stopping-rule record.** Task 04 tested whether an unused proved property strengthens this.
* The new `converges_mul` and the `Tracked` closure enlarge the class of inputs that are known
  to converge.
* Rational-valued sequences need no extra data, because `isModulus_of_rcauchyMod_ofQ` turns the
  real modulus into a rational one.
* For general real-valued sequences, the only input-dependent data are Prop-level existence
  statements.
No term was found that turns `∀ i, ∃ q` into `∃ q, ∀ i`. As required, the search stopped there
and the item stays OPEN.

## O2. Modulus-free completeness

1. `∀ K, ModulusFreeCompleteness K`, i.e. `∀ f, RCauchy f → ∃ L, ConvergesTo f L`.
2. `modulusFreeComplete_of_choice : ChoiceNN → ModulusFreeCompleteness K`.
   `complete_of_modulusFree : ModulusFreeCompleteness K → UnrestrictedCompleteness K`.
   `modulusFree_of_modulusSelection : ModulusSelection K → UnrestrictedCompleteness K → ModulusFreeCompleteness K`.
3. A modulus function `ν` must be selected from `∀ k, ∃ N, …` (O3), together with the selection
   of O1.
4. None.
5. `ChoiceNN`.
6. Not proved.

## O3. Modulus selection

1. `ModulusSelection K := ∀ f, RCauchy f → ∃ ν, RCauchyMod f ν` and
   `RatModulusSelection K := ∀ s, IsCauchy s → ∃ μ, IsModulus s μ`.
2. `modulusSelection_of_choice`, `ratModulusSelection_of_choice` (both from `ChoiceNN`).
   `ratModulusSelection_of_modulusSelection`.
3. A function `k ↦ N k` must be produced from `∀ k, ∃ N, P k N`. `P k N` is in general not
   decidable: real `≤` is not decidable, and rational Cauchy conditions quantify over all larger
   indices. So the structural search `findFirst` does not apply.
4. None.
5. `ChoiceNN`.
6. Not proved.

## O4. Reverse lifting implications

1. Each of the following arrows:
   * `UnrestrictedCompleteness K → CauchySequenceLifting K`;
   * `UnrestrictedCompleteness K → SequenceApprox K`;
   * `UnrestrictedCompleteness K → SequenceLifting K`;
   * `UnrestrictedCompleteness K → ChoiceNN`;
   * `ChoiceNN → SequenceLifting K`;
   * `ModulusFreeCompleteness K → ModulusSelection K`.
2. Only the forward arrows (`SequenceLifting → CauchySequenceLifting → CauchyApprox ⇔ UnrestrictedCompleteness`, `ChoiceNN → SequenceApprox`, `ChoiceNN → ModulusSelection`, and the others listed in `REPORT_TASK03.md` §3).
3. Each arrow needs a construction that recovers selection data from convergence alone. No such
   construction is known.
4. None.
5. Not applicable (these are implications between principles).
6. Not proved.

## O5. Conventional inverses (unconditional)

1. `∀ x : TreeR K, x ≠ 𝟘 → ∃ y, x * y = 𝟙`.
2. `inv_iff_markov` (equivalent to `MarkovPrinciple`), `inv_iff_neImpliesApart`.
   Unconditionally:
   * `exists_inv_of_apart` (under apartness);
   * `not_not_exists_inv` (`x ≠ 𝟘 → ¬¬ ∃ y, …`);
   * `eq_zero_of_mul_eq_zero_of_ne`;
   * `mul_left_cancel_of_ne`.
3. `x ≠ 𝟘 → RApart x 𝟘`. This needs Markov's principle applied to the decidable gap test
   `gapTest s` of a regular representative.
4. None.
5. `MarkovPrinciple` (exactly equivalent).
6. Not proved. Because of the proved equivalence, this item is exactly as open as O6.

## O6. `MarkovPrinciple`

1. `∀ p : TreeN → Bool, ¬¬(∃ n, p n = true) → ∃ n, p n = true`.
2. `markov_of_lpo : LPO → MarkovPrinciple`. It is equivalent to O5 and to `NeImpliesApart K`.
3. A proof by structural recursion would need a bound on the search, and none is available.
4. None.
5. `LPO`.
6. Not proved.

## O7. `LPO`

1. `∀ p : TreeN → Bool, (∃ n, p n = true) ∨ (∀ n, p n = false)`.
2. Equivalent, for every `K`, to `ZeroOrApart K` (`zeroOrApart_iff_lpo`) and to `Trichotomy K`
   (`trichotomy_iff_lpo`, new). It implies `MarkovPrinciple`, `WLPO` and `DecidableZero K`.
   It is implied by `BoundedMonotoneConvergence K` (`lpo_of_bmc`).
3. A decision over infinitely many `TreeN` indices.
4. None.
5. None weaker than itself is known within the repository. `BoundedMonotoneConvergence K`
   suffices, but that is itself open (O10).
6. Not proved.

## O8. `WLPO`

1. `∀ p : TreeN → Bool, (∀ n, p n = false) ∨ ¬(∀ n, p n = false)`.
2. Equivalent to `DecidableZero K := ∀ x : TreeR K, x = 𝟘 ∨ x ≠ 𝟘` (`decidableZero_iff_wlpo`,
   new). Implied by `LPO` and by `UnrestrictedLUB K`.
3. Same as O7.
4. None.
5. `LPO`.
6. Not proved.

## O9. Unrestricted least-upper-bound property

1. `UnrestrictedLUB K := ∀ S : TreeR K → Prop, (∃ x, S x) → (∃ b, IsUpperBound S b) → ∃ y, IsLUB S y`.
2. `wlpo_of_unrestrictedLUB : UnrestrictedLUB K → WLPO` (one way only).
   Unconditional for inputs with `SupData`:
   * `SupData.isLUB`;
   * finite nonempty lists (`SupData.ofList_isLUB`);
   * monotone sequences with a modulus and approximants (`SupData.ofMonotone`);
   * monotone tracked towers.
3. For an arbitrary predicate, a *function* `u : TreeN → K` of rational upper approximations
   must be constructed from `Prop`-level information.
4. None. The implication to `WLPO` is a lower bound on strength, not a disproof.
5. No named premise in the repository is proved to suffice.
6. Not proved.

## O10. Bounded monotone convergence

1. `BoundedMonotoneConvergence K := ∀ f, Monotone f → (∃ b, ∀ i, f i ≤ b) → ∃ L, ConvergesTo f L`.
2. `lpo_of_bmc : BoundedMonotoneConvergence K → LPO` (one way only).
   With data: `tower_monotone_lub`, `SupData.ofMonotone`.
   Under `ChoiceNN`: `monotone_lub_of_choice`, for monotone sequences that are Cauchy.
3. A Cauchy modulus for a bounded monotone sequence. No such modulus can be computed from the
   bound alone.
4. None (the implication to `LPO` is a lower bound only).
5. No named premise in the repository is proved to suffice.
6. Not proved.

## O11. Zero-product disjunction and order totality on `TreeR`

1. `ZeroProductDisjunction K := ∀ x y, x * y = 𝟘 → x = 𝟘 ∨ y = 𝟘`. Also
   `∀ x y : TreeR K, x ≤ y ∨ y ≤ x`.
2. `zeroProduct_of_zeroOrApart` (hence from `LPO`). For totality of `≤`, nothing is proved.
   Unconditionally, only the non-disjunctive forms hold: `eq_zero_of_mul_eq_zero_of_ne`, and
   `le_iff_not_lt`.
3. A disjunction must be decided from real data. For totality, a reduction to a named principle
   is also missing.
4. None.
5. `LPO` suffices for the zero-product disjunction. For totality no named premise is
   formalized.
6. Not proved.

## O12. A conventional field structure on `TreeR`

1. An instance `TField (TreeR K)`. It needs a total `inv` with `x ≠ 𝟘 → x * inv x = 𝟙` and
   `inv 𝟘 = 𝟘`.
2. The inverse law is equivalent to `MarkovPrinciple` (O5). A total `inv` defined by cases also
   needs `DecidableZero K`, which is equivalent to `WLPO` (O8).
3. Both O5 and O8.
4. None.
5. `MarkovPrinciple` together with `WLPO` (both follow from `LPO`) suffice mathematically. The
   instance itself is **not** constructed: by design, Task 04 creates no instance from an open
   premise.
6. Not proved.

## O13. Numerical value of a ray without an explicit symbol choice

1. A non-constant map `Ray α → TreeR K` defined from primitive tree data alone, without a
   distinguished letter or digit choice.
2. Two results limit what such a map can be:
   * the literal prefix counts are the same for all rays and are not Cauchy
     (`prefixCount_indep`, `prefixCount_not_isCauchy`);
   * the binary encoding depends on the letter choice (`encode_letter_choice_dependence`).
3. A construction, or an invariance theorem showing that none exists. The optional automorphism
   programme of Task 04 §8 was **not** carried out.
4. No proof that every choice-free map is constant. The two results in (2) cover only the
   specific maps named there.
5. An explicit letter choice (`TwoLetters`) suffices for a non-constant map (`encode`).
6. Not proved.

## O14. Structural statements not formulated in the repository

* **Universal property of `TreeZ`** as the group completion of `(TreeN, +)`. There is no generic
  group interface in the repository. Nothing in the ledger depends on it.
* **Universal property of the completion `TreeR K`** with respect to arbitrary complete ordered
  structures. Only the extension of uniformly continuous maps `K → K` is proved
  (`extendR_unique`).
* **Letter-choice independence at the real level.** The carrier `TreeR (TreeQ β)` is itself
  built from the `TwoLetters β` instance, so two letter choices give two types that are equal
  only propositionally. A pointwise statement is therefore ill-typed, and the matter is settled
  at the rational level instead (`transfer_letter_indep`, `fieldIso_unique`, `realIso_unique`).

For each of these, fields (4)–(6): none; none; not proved.

---

## Items that are **not** open (to prevent misreading)

* The field axioms of `TreeQ α` (for alphabets with two letters) are all proved
  (`Task04.treeQ_certificate`).
* The commutative-ring axioms of `TreeZ` and `TreeR K`, the integral-domain property of `TreeZ`,
  and the semiring axioms of `TreeN` are all proved.
* The isomorphisms between arities are **unique**, both for the rationals (`fieldIso_unique`)
  and for the completions (`realIso_unique`).
* The one-letter alphabet is excluded for a proved reason: no triple configuration has
  numerator zero (`unary_no_universal_witness`). This is a proved obstruction, not a gap.
