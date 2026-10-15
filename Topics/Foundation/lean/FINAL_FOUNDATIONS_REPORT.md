# FINAL FOUNDATIONS REPORT — Task 04 (closure of the number-foundation phase)

Companion files:
* `TASK04_BASELINE.md`: exact starting state and prose/code mismatches.
* `FINAL_PROPERTY_MATRIX.md`: 131 rows, one per specific property, with status, premises and
  axioms.
* `FINAL_OPEN_PROBLEMS.md`: the permanent register of open items.
* `Audit/AxiomAuditTask04.lean` and `Audit/axioms_task04.txt`: the audit source and its raw
  output.

## 0. What changed

* **No existing declaration was modified, renamed or removed.** No carrier, relation, precision
  scale or operation changed. No defect was found that needed repair.
* **Edited existing files:** two root import lists only.
  * `TreeFoundations.lean`: `+ public import TreeNumbers.FoundationsLedger`.
  * `TreeAnalysis.lean`: `+ FoundationsClosure`, `+ ApproxClosure`, `+ Canonicity`,
    `+ Task04Summary`.
* **New modules:**

| Module | Content |
|---|---|
| `TreeNumbers/FoundationsLedger.lean` | `TreeN` induction, recursion and **uniqueness of recursion**, `zero ≠ one`, totality, right monotonicity of `·`; `TreeZ` strict order, order reflection by `ofN`, sign rules; the one-letter obstruction; letter-choice independence and coherence of `transfer` |
| `TreeAnalysis/FoundationsClosure.lean` | embedding chain for every alphabet, coherence of `realArityIso`, strict monotonicity of `·` in ordered fields, `DecidableZero ↔ WLPO`, `Trichotomy ↔ LPO` |
| `TreeAnalysis/ApproxClosure.lean` | E2: sign-free real product estimate, convergence algebra, `Tracked` families closed under `+`, `-`, `·` and scaling, with explicit output data |
| `TreeAnalysis/Canonicity.lean` | **uniqueness** of the field isomorphism `TreeQ α ≅ TreeQ β` and of the completion isomorphism `TreeR (TreeQ α) ≅ TreeR (TreeQ β)` |
| `TreeAnalysis/Task04Summary.lean` | axiom-by-axiom certificates for the four concrete carriers |
| `Audit/AxiomAuditTask04.lean` | `#print axioms` for all 141 new declarations and all 262 earlier declarations cited in the matrix; dependency-closure audit of 22 central results |

## 1. Construction diagram (actual modules)

```text
UnitChild (PrimitiveTree/UnitChild)                    one child symbol
  └─ UnaryPath := List UnitChild (PrimitiveTree/UnaryPaths)    finite root paths
       ├─ Word α, Edge, rootEdges, unitSum, pathSum (PrimitiveTree/FiniteWords, RootEdges)
       │      unitSum (rootEdges w) = depth w            [Word.unitSum_rootEdges]
       └─ TreeN := UnaryPath (TreeNumbers/PathNaturals, PathOrder, FoundationsLedger)
            commutative semiring, cancellation, decidable total order, recursion + uniqueness
            └─ TreeZ := normalized pairs (pos, neg) (TreeNumbers/PathIntegers)
                 PairEq m n p q :⇔ m+q = p+n ;  mkZ m n = mkZ p q ⇔ PairEq   [mkZ_sound/exact]
                 commutative ring, integral domain, decidable total order
                 └─ TriplePath α (TreeNumbers/PathTriples)      three distinct root paths
                      numer = [pathSum P1, pathSum P2], denom = gap(P3,P2) > 0
                      └─ TreeQ α := Quot TriplePath.Rel (TreeNumbers/PathRationalField,
                         TreeAnalysis/RationalOrder)            [TwoLetters α]
                           Archimedean, decidably ordered field of characteristic zero
                           └─ CSeq (TreeAnalysis/CauchyData, CauchyOps)  sequence + modulus
                                └─ TreeR K := Quot CRel (TreeAnalysis/RealQuotient,
                                   RealOrderApartness, …)            K = QStar = TreeQ TreeN
                                     commutative ring, constructive ordered ring with apartness
```

Embeddings: `TreeZ.ofN : TreeN → TreeZ`, `TreeQ.ofZ : TreeZ → TreeQ α`,
`TreeR.ofQ : K → TreeR K`, `natR`, `ofZRα`. They commute: `natR n = ofZRα (ofN n)`
(`natR_eq_ofZRα`) and `natCast n = ofZ (ofN n)` (`natCast_eq_ofZ`).

## 2. Strongest exact structure proved for each carrier

| Carrier | Strongest structure proved (unconditional) | Certificate |
|---|---|---|
| `TreeN` | Commutative semiring with additive cancellation and cancellation by positive factors, no zero divisors, an injective never-zero successor, `zero ≠ one`, structural induction, and recursion with **uniqueness** (initiality of `(TreeN, zero, succ)`). Its order is decidable, total, antisymmetric, compatible with `+` and `·`, and equal to the path-extension order. | `Task04.treeN_certificate` |
| `TreeZ` | Commutative ring and **integral domain**, with the zero-product *disjunction* proved. Equality is decidable. The order is decidable and total, compatible with `+` and with multiplication by nonnegatives, and satisfies trichotomy. `TreeN → TreeZ` is an injective semiring embedding that preserves and reflects `≤` and `<`. | `Task04.treeZ_certificate` |
| `TreeQ α` (`[TwoLetters α]`) | **Archimedean, decidably and totally ordered field of characteristic zero**, built from path triples. Equality is decidable. The arity isomorphisms exist and are **unique**. | `Task04.treeQ_certificate`, `TreeQ.fieldIso_unique` |
| `TreeR K`, in particular `TreeRStar` | Commutative ring with `0 ≠ 1`. The strict order is irreflexive, transitive and cotransitive. Apartness is tight. Both are compatible with `+` and `·`. Archimedean, rationally dense. Every element apart from `0` is invertible, and every element `≠ 0` is cancellable. This is a **constructive ordered ring with tight apartness, in which apart elements are invertible** (and invertible elements are apart, `apart_of_mul_eq_one`). It is **not** proved to be a conventional field, a discrete field, or a totally ordered field. | `Task04.treeR_unconditional_certificate` |

Conditional: `TreeR K` satisfies the conventional inverse law **exactly** under
`MarkovPrinciple` (`inv_iff_markov`). The statement keeps the premise
(`Task04.treeR_conditional_certificate`).

## 3. Axiom-by-axiom accounting

**Semiring (TreeN):**
* `+`: associativity, commutativity and identity.
* `·`: associativity, commutativity, identity and absorption by zero.
* both distributive laws.

All proved (`TreeN.add_assoc` … `TreeN.right_distrib`; instance `TreeN.instCSR`).

**Ring (TreeZ, TreeQ α, TreeR K):** the additive inverse `neg_add_cancel'` in addition to the
semiring laws. All proved for all three (`TreeZ.instCRing`, `TreeQ.instCRing`,
`TreeR.instCRing`). `0 ≠ 1` is proved for all three.

**Integral domain:**

| Law | `TreeZ` | `TreeQ α` | `TreeR K` |
|---|---|---|---|
| `x·y = 0 → x = 0 ∨ y = 0` | proved (`TreeZ.mul_eq_zero`) | via the field | **only under `ZeroOrApart K` (⇔ `LPO`)** |
| `x ≠ 0 → x·y = 0 → y = 0` | proved | proved | proved (`eq_zero_of_mul_eq_zero_of_ne`) |
| cancellation by `x ≠ 0` | proved | proved | proved (`mul_left_cancel_of_ne`) |

So `TreeR` is cancellative, but not proved to be an integral domain in the disjunctive sense.

**Field:**

| Law | `TreeQ α` | `TreeR K` |
|---|---|---|
| inverses | proved for all `x ≠ 0` (`mul_inv_cancel''`), with `inv 0 = 0` proved (`inv_zero'`) | only for apart `x` (`exists_inv_of_apart`, `mul_rinv`); the conventional form is **equivalent to `MarkovPrinciple`** |
| `TField` instance | concrete (`TreeQ.instTField`) | **none** |

**Ordered field:**
* `TreeQ α`: all axioms proved (`TreeQ.instTOField`), including decidability of `≤` and an
  explicit Archimedean bound function.
* `TreeR K`: the *constructive* ordered-ring axioms hold, namely irreflexivity, transitivity,
  cotransitivity, tightness, `x ≤ y ⇔ ¬ y < x`, compatibility with `+` and `·`, the Archimedean
  property and density.
* `TreeR K`: these laws are **not** proved:
  * trichotomy (equivalent to `LPO`);
  * decidability of `x = 0` (equivalent to `WLPO`);
  * totality of `≤` (open, not reduced to a named principle).

**Constructive reals:** `TreeR K` has all of the following.
* quotient of Cauchy data with explicit moduli, with soundness and exactness;
* well-defined ring operations with explicit output moduli;
* tight apartness, and inversion of apart elements;
* Archimedean, with rationals dense;
* limits of Cauchy sequences that carry explicit data;
* uniqueness of limits.

This is the content that justifies the name "constructive Cauchy reals". The classical complete
ordered field is **not** claimed (§4).

## 4. Rational field axioms versus real Cauchy completeness

These are different notions. The field axioms for `TreeQ` are **complete**: every defining
axiom is a concrete theorem (§3).

Cauchy completeness of `TreeR`:

| Statement | Status |
|---|---|
| `limit_of_approx`: modulus `ν` plus approximation data give a limit | unconditional |
| tracked towers converge (`tower_converges`) | unconditional |
| `Tracked` families converge; the class is closed under `+`, `-`, `·`, scaling, and limits commute (new) | unconditional |
| rational-valued sequences with a real modulus converge (new corollary) | unconditional |
| `UnrestrictedCompleteness K` (every real Cauchy sequence *with modulus* converges) | **OPEN**; equivalent to `CauchyApprox K`; follows from `ChoiceNN` |
| `ModulusFreeCompleteness K` | **OPEN**; follows from `ChoiceNN` |
| modulus selection | **OPEN**; follows from `ChoiceNN` |

`UnrestrictedCompleteness K` covers only sequences supplied with a modulus function. It is
not a statement about every form of completeness.

## 5. Best unconditional and conditional theorems

**Sequential convergence**
* Unconditional:
  * `limit_of_approx`;
  * `Tracked.converges`, with `Tracked.add/neg/mul` and `lim_add/lim_neg/lim_mul`;
  * `converges_add/neg/mul` (Prop-level, no data);
  * `limit_unique`;
  * `ofQ_seq_converges`.
* Conditional: `complete_of_choice : ChoiceNN → UnrestrictedCompleteness K` and
  `modulusFreeComplete_of_choice : ChoiceNN → ModulusFreeCompleteness K`.

**Supremum**
* Unconditional:
  * `SupData.isLUB : IsLUB S D.sup` for every `D : SupData S`;
  * `lub_unique`;
  * `SupData.ofList_isLUB` (nonempty finite lists);
  * `SupData.ofMonotone`, `tower_monotone_lub`.
* Conditional: `monotone_lub_of_choice` (needs `ChoiceNN`).
* Lower bounds on logical strength:
  * `wlpo_of_unrestrictedLUB : UnrestrictedLUB K → WLPO`;
  * `lpo_of_bmc : BoundedMonotoneConvergence K → LPO`.

  These are one-way implications only. They are not disproofs.

**Inversion** (D2, as separate theorems)
1. `exists_inv_of_apart : RApart x 0 → ∃ y, x*y = 1`.
2. `eq_zero_of_mul_eq_zero_of_ne : x ≠ 0 → x*y = 0 → y = 0`.
3. `mul_left_cancel_of_ne : x ≠ 0 → x*y = x*z → y = z`.
4. `inv_iff_markov : (∀ x, x ≠ 0 → ∃ y, x*y = 1) ↔ MarkovPrinciple`. The inverse law itself is
   open.
5. Decisions:
   * `zeroProduct_of_zeroOrApart`;
   * `zeroOrApart_iff_lpo`;
   * `decidableZero_iff_wlpo` (new);
   * `trichotomy_iff_lpo` (new).

Only `x ≠ 0 → ¬¬ ∃ y, x*y = 1` (`not_not_exists_inv`) is unconditional. That is not a
constructed inverse.

**Rechecked signatures**:
* `inv_iff_markov` and `zeroOrApart_iff_lpo` are genuine `↔`.
* `wlpo_of_unrestrictedLUB` and `lpo_of_bmc` are one-way `→`. No converse is asserted anywhere.

## 6. Remaining OPEN questions

Full register: `FINAL_OPEN_PROBLEMS.md`, items O1–O14.
* Unconditional completeness with modulus.
* Modulus-free completeness.
* Modulus selection.
* Reverse lifting implications.
* The conventional inverse law.
* `MarkovPrinciple`, `LPO` and `WLPO` themselves.
* The unrestricted least-upper-bound property.
* Bounded monotone convergence.
* Zero-product disjunction and totality of `≤` on `TreeR`.
* A conventional `TField (TreeR K)` instance.
* A choice-free numerical value for rays.
* Three structural statements that are not formulated (universal properties of `TreeZ` and of
  the completion; letter independence at the real level, which is ill-typed).

No necessity, independence or unprovability result is claimed for any of them.

## 7. New closure, coherence and canonicity results, with their hypotheses

* **E2 closure** (`ApproxClosure.lean`). For `T : Tracked f` and `S : Tracked g`:
  * `T.add S`, `T.neg`, `T.mul S`, `T.smulQ c` and `T.smulRep c` carry explicit approximants,
    schedules and moduli;
  * the product uses the **derived** bound `mulShift T S = succ (2^(bnd T.cseq) + 2^(bnd S.cseq))`,
    not the input moduli;
  * the limit commutes with each operation;
  * `lim_indep`: the limit does not depend on the data;
  * `approx_seqEquiv`: two approximant sequences of one family are Cauchy-equivalent.

  The core estimate `rclose_mul_zero` (`|w| ≤ B`, `|u| ≤ e` ⟹ `|wu| ≤ Be`) needs no sign
  decision. It uses the identity `(B−w)(e+u) + (B+w)(e−u) = 2(Be − wu)` and halving.
* **Convergence algebra without data:** `converges_add`, `converges_neg`, `converges_mul`.
* **Coherence:**
  * `transfer_self`, `transfer_comp`, `arityIso_comp`;
  * `realArityIso_self`, `realArityIso_comp`;
  * commutation with every embedding: `transfer_ofZ`, `transfer_natCast`, `realArityIso_ofZRα`,
    `realArityIso_natR`.
* **Canonicity:**
  * `TreeQ.fieldIso_unique`: every `FieldIso (TreeQ α) (TreeQ β)` is `transfer α β`;
  * `TreeR.realIso_unique`: every `RealIso (TreeR (TreeQ α)) (TreeR (TreeQ β))` is
    `realArityIso α β`;
  * `ofF_letter_indep` and `transfer_letter_indep`: the classes and the comparison maps do not
    depend on the letter choice.

  The raw witness *triples* do depend on the letter choice (`ofFrac_letter_dependent`).
  Existence of witnesses needs two letters, and this need is proved
  (`unary_no_universal_witness`).
* **Initiality of `TreeN`:** `recN_unique`.
* **Integer order:** `TreeZ.le_of_ofN_le`, `ofN_lt_ofN`, `lt_of_ofN_lt`, `lt_trichotomy` and the
  sign rules.
* **Reverified Task 03 scope results** on the literal unit-edge sum: `prefixCount_eq`,
  `prefixCount_indep`, `prefixCount_not_isCauchy`.

## 8. Kernel audit and firewall

**`#print axioms`** (raw: `Audit/axioms_task04.txt`). The file has 403 entries: all 141 new
declarations, plus 262 earlier declarations cited in the matrix.

| Axioms | Count |
|---|---|
| none | 176 |
| `[Quot.sound]` | 122 |
| `[propext, Quot.sound]` | 102 |
| `[propext]` | 3 (`TreeR.mkR_exact`, `TreeR.ofQ_injective`, `TreeR.natR_injective`) |

**`Classical.choice` occurs in no entry.** Neither does any other axiom.
* `Quot.sound` comes from the kernel quotients `TreeQ` and `TreeR`, and from function
  extensionality (`funext`, which is derived from `Quot.sound`).
* `propext` comes from quotient exactness. `TreeR.mkR_exact` lifts the relation into `Prop`
  through `relTo`, which uses `propext`. It imports no numerical law.

Representative lines:

```text
'TreeN.instCSR' does not depend on any axioms
'TreeZ.instCRing' does not depend on any axioms
'TreeQ.instTField' depends on axioms: [Quot.sound]
'TreeQ.instTOField' depends on axioms: [Quot.sound]
'TreeR.instCRing' depends on axioms: [Quot.sound]
'Task04.treeN_certificate' does not depend on any axioms
'Task04.treeZ_certificate' does not depend on any axioms
'Task04.treeQ_certificate' depends on axioms: [Quot.sound]
'Task04.treeR_unconditional_certificate' depends on axioms: [propext, Quot.sound]
'Task04.treeR_conditional_certificate' depends on axioms: [propext, Quot.sound]
'Task04.treeR_convergence_certificate' depends on axioms: [propext, Quot.sound]
'TreeR.inv_iff_markov' depends on axioms: [propext, Quot.sound]
'TreeR.zeroOrApart_iff_lpo' depends on axioms: [propext, Quot.sound]
'TreeR.decidableZero_iff_wlpo' depends on axioms: [propext, Quot.sound]
'TreeR.trichotomy_iff_lpo' depends on axioms: [propext, Quot.sound]
'TreeR.complete_iff_cauchyApprox' depends on axioms: [propext, Quot.sound]
'TreeR.complete_of_choice' depends on axioms: [propext, Quot.sound]
'TreeR.Tracked.mul' depends on axioms: [propext, Quot.sound]
'TreeR.converges_mul' depends on axioms: [propext, Quot.sound]
'TreeQ.fieldIso_unique' depends on axioms: [Quot.sound]
'TreeR.realIso_unique' depends on axioms: [propext, Quot.sound]
'TreeR.SupData.isLUB' depends on axioms: [propext, Quot.sound]
'TreeR.wlpo_of_unrestrictedLUB' depends on axioms: [propext, Quot.sound]
'TreeR.lpo_of_bmc' depends on axioms: [propext, Quot.sound]
'TreeN.recN_unique' does not depend on any axioms
'TriplePath.unary_no_universal_witness' does not depend on any axioms
'PrimitiveScope.prefixCount_not_isCauchy' does not depend on any axioms
```

**Transitive dependency closure** (`#closure_audit4`). It covers 22 central results: the five
concrete instances, the six certificates, the four equivalences, the E2 product, the two
canonicity theorems, and others.
* No closure contains a constant with a `Classical` component.
* The axioms found are `Quot.sound` and `propext` only.
* Built-in `Nat` constants occur (10 per closure, none for `TreeN.instCSR`) **only** through
  helpers that Lean generates automatically for every inductive type: `List.ctorIdx`,
  `Bool.ctorIdx`, `noConfusion_of_Nat` and its private auxiliaries. Lean 4.28 uses them for
  `injection`, `cases` and `nomatch`. They belong to the compiler and kernel, not to the
  project's source, and no project declaration mentions them. This matches the Task 01–03
  audits.

**Source firewall** (new modules). After stripping comments, a scan for the following
identifiers finds **no match**: `Nat`, `Int`, `Rat`, `Fin`, `PNat`, `UInt*`, `USize`, `BitVec`,
`Real`, `Classical`, `classical`, `noncomputable`, `omega`, `norm_num`, `ring`, `linarith`,
`simp`, `simpa`, `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `implemented_by`,
`native_decide`, `aesop`, `decide`, `Mathlib`, `length`, `replicate`, `range`.
* There are no numeric literals. The only digit-like characters are the notations `𝟘` and `𝟙`,
  which stand for `CSR.zero` and `CSR.one` of the concrete instances.
* No mathlib import. `lake-manifest.json` is unchanged and has no packages.
* All new principles (`DecidableZero K`, `Trichotomy K`) are `def … : Prop` used only as
  hypotheses or in `↔` statements.
* No new instance encodes an open property.
* The audit file uses Lean's metaprogramming API, imports nothing into the mathematics, and has
  no `partial`.

## 9. Build commands and results

| Command | Result |
|---|---|
| `lake build TreeNumbers.FoundationsLedger` | success |
| `lake build TreeAnalysis.FoundationsClosure` | success |
| `lake build TreeAnalysis.ApproxClosure` | success |
| `lake build TreeAnalysis.Canonicity` | success |
| `lake build TreeAnalysis.Task04Summary` | success |
| `lake build TreeFoundations TreeAnalysis Audit` (final integration) | success (66 jobs, 0 warnings, 0 errors) |
| `lake env lean Audit/AxiomAuditTask04.lean > Audit/axioms_task04.txt` | exit 0, 0 errors |

No `sorry` occurs in any source file.

## 10. Recommendation

**RELEASE** the current foundations phase. Its scope is exactly the following:
* `TreeN`, `TreeZ` and `TreeQ` are fully closed at the level of their defining axioms, with
  every law kernel-checked from primitive path data and no classical axiom.
* `TreeQ α` is a genuinely proved Archimedean ordered field built from path triples.
* `TreeR` is released **as a constructive ordered ring with tight apartness and inverses for
  apart elements**, together with the conditional statements above. It is **not** released as a
  conventional field or as a complete ordered field.

The open items O1–O14 stay in the permanent register. None of them is a defect in the defining
axioms of the structures claimed in §2, so none blocks the release. They mark where further
strength would need an additional principle (`ChoiceNN`, `MarkovPrinciple`, `WLPO`, `LPO`) or a
new construction.
