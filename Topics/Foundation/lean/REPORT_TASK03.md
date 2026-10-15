# REPORT — Task 03: constructive completeness, logical strength and exact scope

## 1. Base and changed files

* **Base:** the Task 02 repository as supplied, git commit `940609d` ("Initial commit").
  Baseline inventory: `TASK03_BASELINE.md`.
* **No existing declaration was modified, renamed or removed.** `TreeR K := Quot (CRel (K := K))`
  is unchanged. No foundational file was refactored.
* **Added modules** (all in the existing `TreeAnalysis` library):
  * `TreeAnalysis/CompletenessStrength.lean`: Checkpoint A
  * `TreeAnalysis/LiftingPrinciples.lean`: Checkpoint B
  * `TreeAnalysis/ApartnessStrength.lean`: Checkpoint C
  * `TreeAnalysis/SupremumScope.lean`: Checkpoint D
  * `TreeAnalysis/PrimitiveDataScope.lean`: Checkpoint E
  * `TreeAnalysis/CompletionCharacterization.lean`: Checkpoint F
  * `TreeAnalysis/Task03Summary.lean`: headline results restated for `TreeRStar = TreeR Q★`
  * `Audit/AxiomAuditTask03.lean` and `Audit/axioms_task03.txt`: `#print axioms` for all 181 new
    declarations
  * `Audit/ClosureAuditTask03.lean` and `Audit/closure_task03.txt`: audit of the effective
    dependency closure
* **Modified:** `TreeAnalysis.lean`, which gained seven new `public import` lines and nothing else.

Notation used below: `K` is an implicit `{K : Type} [TOField K]`, and every theorem holds for
every triple-path rational base, in particular for `QStar`. `eps k = 1/2^k`, with `k : TreeN`.
`RClose x y e` means `x ≤ y + ofQ e ∧ y ≤ x + ofQ e`.

## 2. New kernel-checked theorems

### Checkpoint A: Cauchy notions and the limiting step (`CompletenessStrength.lean`)

| Status | Name | Statement |
|---|---|---|
| PROVED UNCONDITIONALLY | `rcauchyMod_iff_close` | `RCauchyMod f ν` ⇔ `∀ k i j, ν k ≤ i → ν k ≤ j → RClose (f i) (f j) (eps k)` |
| PROVED UNCONDITIONALLY | `rcauchy_iff_close` | the same equivalence for `RCauchy` (with `Prop`-level `N`) |
| PROVED UNCONDITIONALLY | `rcauchy_of_rcauchyMod` | `RCauchyMod f ν → RCauchy f` |
| PROVED UNCONDITIONALLY | `rcauchy_of_converges` | `ConvergesTo f L → RCauchy f` |
| PROVED UNCONDITIONALLY | `rcauchyMod_of_converges_mod` | a convergence modulus *function* `μ` gives `RCauchyMod f (μ ∘ succ)` |
| PROVED UNCONDITIONALLY | `rcauchyMod_ofQ`, `isModulus_of_rcauchyMod_ofQ` | `IsModulus s μ ⇔ RCauchyMod (ofQ ∘ s) μ` (one theorem for each direction) |
| PROVED UNCONDITIONALLY | `isCauchy_of_rcauchy_ofQ`, `rcauchy_ofQ_of_isCauchy` | `IsCauchy s ⇔ RCauchy (ofQ ∘ s)` |
| PROVED UNCONDITIONALLY | `mkR_close_seq` | `c.mod k ≤ n → RClose (ofQ (c.seq n)) (mkR c) (eps k)`, with an explicit index |
| PROVED UNCONDITIONALLY | `mkR_reg` | `mkR (CSeq.ofRegular (reg c) _) = mkR c` |
| PROVED UNCONDITIONALLY | `regular_close` | for `IsRegular s`: `RClose (ofQ (s n)) (mkR (ofRegular s)) (eps n)` for **every** `n` |
| PROVED UNCONDITIONALLY | `regular_rep_bishop` | two regular representatives of one real satisfy `abs (s n - t n) ≤ eps n + eps n` |
| PROVED UNCONDITIONALLY | `exists_regular_rep` | `∀ x, ∃ s hs, mkR (ofRegular s hs) = x` (`Prop`-level; nothing is selected) |
| PROVED UNCONDITIONALLY | `exists_rat_close` | `∀ x i, ∃ q, RClose x (ofQ q) (eps i)` (`Prop`-level) |
| PROVED UNCONDITIONALLY | `limit_of_approx` | `RCauchyMod f ν → ApproxData f q M → ∃ L, ConvergesTo f L` |
| PROVED UNCONDITIONALLY | `approxSeq_converges` | the same, with the limit `mkR (approxSeq …)` and an explicit convergence schedule |
| PROVED UNCONDITIONALLY | `close_of_cauchy_of_converges` | `RCauchyMod f ν → ConvergesTo f L → ν k ≤ i → RClose (f i) L (eps k)` |
| PROVED UNCONDITIONALLY | `TrackedCauchyTower.approx`, `tower_limit_via_approx`, `tower_limit_eq_approx_limit` | a tower supplies `ApproxData` with `q i := (r i).seq ((r i).mod i)` and `M = id`; the limit obtained this way equals `T.limit` |

Here `ApproxData f q M := ∀ k i, M k ≤ i → RClose (f i) (ofQ (q i)) (eps k)`.

**A3, diagnosis of the diagonal.** `diag_isMod` and `tower_converges` use the representatives
`r i` only through the single rationals `(r (I m)).seq ((r (I m)).mod m)`, together with the
real-level modulus `ν`. The sharpened theorem `limit_of_approx` keeps exactly that information:
one rational per index with an explicit error schedule `M`, plus `ν`. It needs no representative
of any `f i`. The modulus `ν` is still used, to build the rational modulus `approxMod ν M` of the
approximants. Without `ν`, the approximants form only a `Prop`-level Cauchy sequence, and turning
that into data is the modulus-selection problem (B3).

**Which real Cauchy families are known to converge (unconditionally):** every family with a
modulus `ν` **and** approximation data `(q, M)`. This includes every `TrackedCauchyTower`, every
sequence of classes of explicit Cauchy data, and every sequence `ofQ ∘ s` with `IsModulus s μ`.

### Checkpoint B: lifting principles and sequential completeness (`LiftingPrinciples.lean`)

The new principles are **propositions** used only as hypotheses:
`CauchySequenceLifting K`, `SequenceApprox K` (`∀ f, ∃ q, ∀ i, RClose (f i) (ofQ (q i)) (eps i)`),
`CauchyApprox K` (`∀ f ν, RCauchyMod f ν → ∃ q M, ApproxData f q M`), `ModulusSelection K`
(`∀ f, RCauchy f → ∃ ν, RCauchyMod f ν`), `RatModulusSelection K`
(`∀ s, IsCauchy s → ∃ μ, IsModulus s μ`) and `ModulusFreeCompleteness K`
(`∀ f, RCauchy f → ∃ L, ConvergesTo f L`).

| Status | Name | Statement |
|---|---|---|
| PROVED UNDER EXPLICIT HYPOTHESES | `cauchyLifting_of_lifting` | `SequenceLifting K → CauchySequenceLifting K` |
| PROVED UNDER EXPLICIT HYPOTHESES | `complete_of_cauchyLifting` | `CauchySequenceLifting K → UnrestrictedCompleteness K` |
| PROVED UNDER EXPLICIT HYPOTHESES | `seqApprox_of_lifting` | `SequenceLifting K → SequenceApprox K` |
| PROVED UNDER EXPLICIT HYPOTHESES | `cauchyApprox_of_cauchyLifting`, `cauchyApprox_of_seqApprox` | `CauchySequenceLifting K → CauchyApprox K`, `SequenceApprox K → CauchyApprox K` |
| **PROVED (both directions)** | `complete_iff_cauchyApprox` | `(UnrestrictedCompleteness K → CauchyApprox K) ∧ (CauchyApprox K → UnrestrictedCompleteness K)` |
| PROVED UNDER EXPLICIT HYPOTHESES | `modulusSelection_of_choice` | `ChoiceNN → ModulusSelection K` |
| PROVED UNDER EXPLICIT HYPOTHESES | `ratModulusSelection_of_modulusSelection` | `ModulusSelection K → RatModulusSelection K` |
| PROVED UNDER EXPLICIT HYPOTHESES | `ratModulusSelection_of_choice` | `ChoiceNN → RatModulusSelection K` |
| PROVED UNDER EXPLICIT HYPOTHESES | `modulusFree_of_modulusSelection` | `ModulusSelection K → UnrestrictedCompleteness K → ModulusFreeCompleteness K` |
| PROVED UNDER EXPLICIT HYPOTHESES | `complete_of_modulusFree` | `ModulusFreeCompleteness K → UnrestrictedCompleteness K` |
| PROVED UNCONDITIONALLY | `exists_floor` | `∀ y : K, ∃ a b : TreeN, abs (natCast a - natCast b - y) ≤ 1` |
| PROVED UNCONDITIONALLY | `exists_dyad_close` | `∀ x i, ∃ a b : TreeN, RClose x (ofQ ((natCast a - natCast b)·eps (i+1))) (eps i)` |
| PROVED UNDER EXPLICIT HYPOTHESES | `choice_pair` | `ChoiceNN → (∀ i, ∃ a b, P i a b) → ∃ fa fb, ∀ i, P i (fa i) (fb i)` |
| PROVED UNDER EXPLICIT HYPOTHESES | `seqApprox_of_choice` | `ChoiceNN → SequenceApprox K` |
| PROVED UNDER EXPLICIT HYPOTHESES | **`complete_of_choice`** | `ChoiceNN → UnrestrictedCompleteness K` |
| PROVED UNDER EXPLICIT HYPOTHESES | **`modulusFreeComplete_of_choice`** | `ChoiceNN → ModulusFreeCompleteness K` |

**Weakening of the Task 02 premise.** Task 02 used `SequenceLifting K`, which selects
*representatives*: functions with moduli, so elements of a quotient of a function space. Task 03
shows that `ChoiceNN` suffices for both completeness statements. `ChoiceNN` selects
`TreeN`-valued indices only. It is applied, twice, to the two path-count numerators `a, b` of a
dyadic approximant `(a − b)/2^(i+1)`. It is never applied to quotient representatives.

**B2, the step that remains open.** Every real `f i` has, *for each* `i`, a rational approximant
(`exists_rat_close`). This is a `∀ i, ∃ q` statement, obtained by `Quot.ind` into `Prop`.
`complete_iff_cauchyApprox` shows that unconditional completeness is **exactly** the passage to
`∃ q M, ∀ k i, …` for Cauchy sequences with modulus. No term producing such a family was found.
`Quot.ind` only proves propositions, and `Quot.lift` would require a function on the space of
*sequences of representatives*, which the quotient of single reals does not provide. The
unconditional statement is therefore **OPEN**. No impossibility is claimed.

### Checkpoint C: apartness, inversion and algebraic strength (`ApartnessStrength.lean`)

New named propositions:
* `MarkovPrinciple := ∀ p : TreeN → Bool, ¬¬(∃ n, p n = true) → ∃ n, p n = true`;
* `LPO := ∀ p : TreeN → Bool, (∃ n, p n = true) ∨ (∀ n, p n = false)`;
* `ZeroOrApart K := ∀ x, x = 0 ∨ RApart x 0`;
* `ZeroProductDisjunction K := ∀ x y, x·y = 0 → x = 0 ∨ y = 0`.

| Status | Name | Statement |
|---|---|---|
| PROVED (both directions) | `inv_iff_neImpliesApart` | `(∀ x, x ≠ 0 → ∃ y, x·y = 1) ↔ NeImpliesApart K` |
| **PROVED (both directions)** | `neImpliesApart_iff_markov` | `NeImpliesApart K ↔ MarkovPrinciple` |
| PROVED (both directions) | `inv_iff_markov` | `(∀ x, x ≠ 0 → ∃ y, x·y = 1) ↔ MarkovPrinciple` |
| **PROVED (both directions)** | `zeroOrApart_iff_lpo` | `ZeroOrApart K ↔ LPO` |
| PROVED UNDER EXPLICIT HYPOTHESES | `zeroProduct_of_zeroOrApart`, `neImpliesApart_of_zeroOrApart`, `markov_of_lpo` | `ZeroOrApart K → ZeroProductDisjunction K`, `ZeroOrApart K → NeImpliesApart K`, `LPO → MarkovPrinciple` |

The reductions are explicit. `MarkovPrinciple → NeImpliesApart` applies Markov's principle to the
decidable gap test `gapTest s n := decide (3·eps n < abs (s n))` on a regular representative.
`NeImpliesApart → MarkovPrinciple` uses the real `markovReal K p`, whose representative at stage
`m` is `eps` of the first success of `p` up to `m` (computed by the existing structural search
`TreeQ.findFirst`), or `0` if there is none yet.

### Algebraic laws: unconditional versus conditional

**Unconditional, from positive evidence of apartness:** `exists_inv_of_apart`, `mul_rinv`,
`eq_zero_of_mul_eq_zero_of_apart` (`RApart x 0 → x·y = 0 → y = 0`), `mul_left_cancel_of_apart`,
`apart_mul` (`RApart x 0 → RApart y 0 → RApart (x·y) 0`), `apart_of_apart_mul_left` and
`apart_of_apart_mul_right`.

**Unconditional, from mere inequality `x ≠ 0`:**
* `eq_of_not_not_eq`: equality of reals is `¬¬`-stable;
* `eq_zero_of_mul_eq_zero_of_ne`: `x ≠ 0 → x·y = 0 → y = 0`;
* `mul_left_cancel_of_ne`: `x ≠ 0 → x·y = x·z → y = z`;
* `mul_ne_zero'`: `x ≠ 0 → y ≠ 0 → x·y ≠ 0`;
* `not_not_exists_inv`: `x ≠ 0 → ¬¬ ∃ y, x·y = 1`;
* from Task 02: `x ≠ 0 → ¬¬ RApart x 0`.

**Only under an additional principle:**
* the conventional inverse law, which is *equivalent* to `MarkovPrinciple`;
* the disjunctive zero-product law, which follows from `ZeroOrApart K`, itself equivalent to
  `LPO`. Whether the zero-product law follows from something weaker is OPEN.

`TreeR K` is therefore proved to be a commutative ring with `0 ≠ 1` in which apart elements are
invertible and nonzero elements are cancellable. It is a conventional field
(`x ≠ 0 → ∃ y, x·y = 1`) **exactly** under `MarkovPrinciple`.

### Checkpoint D: suprema (`SupremumScope.lean`)

Three separate notions:

| Notion | Status | Names |
|---|---|---|
| **Approximated supremum** | PROVED UNCONDITIONALLY (Task 02) | `SupData.sup`, `SupData.le_sup`, `SupData.sup_approx` |
| **Genuine least upper bound under `SupData`** | **PROVED UNCONDITIONALLY** (given `D : SupData S`) | `SupData.sup_least` (`IsUpperBound S y → D.sup ≤ y`), `SupData.isLUB` (`IsLUB S D.sup`), `lub_unique`, `SupData.eq_sup_of_isLUB`, `SupData.sup_eq` |
| **Unrestricted least upper bound** `UnrestrictedLUB K` | OPEN. Proved implication: `wlpo_of_unrestrictedLUB : UnrestrictedLUB K → WLPO` | `UnrestrictedLUB K := ∀ S, (∃ x, S x) → (∃ b, IsUpperBound S b) → ∃ y, IsLUB S y` |

`IsLUB S y := (∀ x, S x → x ≤ y) ∧ ∀ z, (∀ x, S x → x ≤ z) → y ≤ z`, and
`WLPO := ∀ p : TreeN → Bool, (∀ n, p n = false) ∨ ¬(∀ n, p n = false)`.

**D2, constructive supply of `SupData`** (all unconditional, given the displayed data):
* `SupData.singleton c` for `{mkR c}`;
* `SupData.union D E` for `S ∪ T`, chosen by the decidable comparison of the rational upper
  approximations;
* `SupData.ofList c l` for every nonempty finite list of explicit Cauchy data, with
  `ofList_isLUB`: such a list has a least upper bound;
* `SupData.ofMonotone hm hc hq` for the range of a monotone real sequence with a Cauchy modulus
  `ν` and approximation data `(q, M)`.

Whether every inhabited, bounded predicate admits `SupData` is not claimed. `SupData` requires a
*function* `u : TreeN → K` of rational upper bounds. For an arbitrary predicate `S`, no
construction of such a function from `Prop`-level information was found. By
`wlpo_of_unrestrictedLUB`, a uniform solution would yield `WLPO`.

**D3, monotone sequences:**
* `lub_of_monotone_converges` (unconditional): the limit of a monotone convergent sequence is the
  least upper bound of its range;
* `tower_monotone_lub` (unconditional, for monotone tracked towers);
* `monotone_lub_of_choice` (conditional on `ChoiceNN`, with no modulus required);
* `lpo_of_bmc`: ordinary bounded monotone convergence implies `LPO`. Bounded monotone
  convergence itself is OPEN and is not claimed.

### Checkpoint E: primitive path data and canonicity (`PrimitiveDataScope.lean`)

| Status | Name | Statement |
|---|---|---|
| PROVED UNCONDITIONALLY | `PrimitiveScope.provenance_chain` | `natR (pathSum w) = ofZR (TreeZ.ofN (depth w)) ∧ pathSum w = unitSum (rootEdges w) ∧ unitSum (rootEdges w) = depth w` |
| PROVED UNCONDITIONALLY | `prefixCount_eq`, `prefixCount_succ` | `prefixCount r n := natCast (pathSum (prefixAt r n)) = natCast n`; each further edge adds exactly `1` |
| **PROVED OBSTRUCTION** | `prefixCount_not_isCauchy` | `¬ IsCauchy (prefixCount r)`, for every ray `r` and every base `K` |
| PROVED OBSTRUCTION | `prefixCount_not_rcauchy` | `¬ RCauchy (ofQ ∘ prefixCount r)` |
| PROVED UNCONDITIONALLY | `prefixCount_indep`, `prefixCount_indep_alphabet`, `prefixCount_observation_indep` | `prefixCount r = prefixCount r'` for any two rays, even over different alphabets; hence `F (prefixCount r) = F (prefixCount r')` for every `F` |
| PROVED UNCONDITIONALLY | `Ray.encode_distinguishes` | with the extra letter choice, `encode (const l0) ≠ encode (const l1)` |
| **PROVED COUNTEREXAMPLE** | `Ray.encode_letter_choice_dependence` | `encode (const T.l0) = 0` under `T`, while it equals `1` under the swapped letters, so the two encodings differ |

**E2, result.** The unmodified prefix-count sequence is the image of `n ↦ n`. In the project's own
sense it is **not Cauchy**: with tolerance `1`, consecutive terms differ by exactly the unit edge.
The proof uses only `prefixCount_succ`. The sequence is the same for every ray, so these
observations cannot distinguish any two rays. This does **not** show that every map from rays to
numbers is constant: `encode_distinguishes` gives a non-constant map, but that map uses extra
choices.

**Table: source data versus choices**

| Map | Classification | Evidence |
|---|---|---|
| `rootEdges`, `unitSum`, `pathSum`, `depth` | derived from primitive data | `unitSum_rootEdges`, `pathSum_eq_depth` |
| `TreeN` arithmetic and order | derived from primitive data | Task 01 |
| `TreeN → TreeZ` (`ofN`), `TreeZ → TreeQ` (`ofZ`), `natR`, `ofZR` | derived; no choice | `natR_eq_ofZR`, `provenance_chain` |
| the universal triple-path witness for a fraction | derived after an explicit choice of the two letters `l0, l1` (`TwoLetters`) | Task 01, `PathTriples` |
| comparison between arities | derived after an explicit choice of letters; the field isomorphism is proved | `arityIso`, `realArityIso` |
| precision scale `eps k = 1/2^k` | derived after an explicit design choice (the dyadic scale) | `DyadicPrecision` |
| a real from a sequence of reals (limit) | requires selected data: moduli and approximants (`ApproxData`), or `ChoiceNN` | `limit_of_approx`, `complete_of_choice` |
| `encode : Ray → TreeR` | derived after explicit choices (`l1` digit, weights `eps (i+1)`); **not** invariant under swapping the letters | `encode_letter_choice_dependence` |
| raw prefix counts `pathSum (prefixAt r n)` as a real number for a ray | unsupported: not Cauchy | `prefixCount_not_isCauchy` |
| a canonical numerical value of a ray | unsupported / OPEN: no construction from primitive data alone was found | `prefixCount_indep` shows the raw counts carry no ray information |

### Checkpoint F: extension of uniformly continuous maps (`CompletionCharacterization.lean`)

| Status | Name | Statement |
|---|---|---|
| PROVED UNCONDITIONALLY | `mapSeqUC`, `mapSeqUC_resp` | for `UCMod f ω := ∀ k x y, abs (x - y) ≤ eps (ω k) → abs (f x - f y) ≤ eps k`, termwise application gives `CSeq` data with modulus `k ↦ c.mod (ω k)`; it respects `SeqEquiv` |
| PROVED UNCONDITIONALLY | `extendR`, `extendR_indep` | induced map `TreeR K → TreeR K`; independent of the representative |
| PROVED UNCONDITIONALLY | `extendR_ofQ` | `extendR f ω h (ofQ q) = ofQ (f q)` |
| PROVED UNCONDITIONALLY | `extendR_ratSeqContinuous` | `RatSeqContinuous (extendR f ω h)`, where `RatSeqContinuous F := ∀ c, ConvergesTo (fun n => F (ofQ (c.seq n))) (F (mkR c))` |
| PROVED UNCONDITIONALLY | `eq_of_ratSeqContinuous`, **`extendR_unique`** | two `RatSeqContinuous` maps agreeing on `ofQ` are equal; so `extendR f ω h` is the unique such extension of `f` |
| PROVED UNCONDITIONALLY | `extendR_modulus_indep`, `extendR_comp`, `extendR_neg` | independence of the modulus; compatibility with composition; the extension of rational negation is real negation |

This is an extension-and-uniqueness theorem for maps `K → K` only. No universal property of the
completion with respect to arbitrary complete spaces is claimed.

## 3. Implication diagram (proved arrows only)

```text
SequenceLifting K ──► CauchySequenceLifting K ──► CauchyApprox K ◄══► UnrestrictedCompleteness K
        │                                            ▲                       ▲
        └──────────► SequenceApprox K ──────────────┘                       │
                          ▲                                                  │
ChoiceNN ─────────────────┘                                                  │
ChoiceNN ──► ModulusSelection K ──► RatModulusSelection K                    │
ChoiceNN ──► RatModulusSelection K                                           │
ModulusSelection K ∧ UnrestrictedCompleteness K ──► ModulusFreeCompleteness K ┘ (and back: ModulusFree ⇒ Unrestricted)
ChoiceNN ──► UnrestrictedCompleteness K,   ChoiceNN ──► ModulusFreeCompleteness K

IsModulus s μ ◄══► RCauchyMod (ofQ∘s) μ ;  IsCauchy s ◄══► RCauchy (ofQ∘s)
IsRegular s ──► IsModulus s succ ──► IsCauchy s ;  RCauchyMod f ν ──► RCauchy f
ConvergesTo f L ──► RCauchy f ;  RCauchyMod f ν ∧ ConvergesTo f L ──► (convergence with modulus ν)
RCauchyMod f ν ∧ ApproxData f q M ──► ∃ L, ConvergesTo f L      (unconditional)

(∀ x ≠ 0, ∃ y, x·y = 1) ◄══► NeImpliesApart K ◄══► MarkovPrinciple
ZeroOrApart K ◄══► LPO ;  LPO ──► MarkovPrinciple ;  LPO ──► WLPO
ZeroOrApart K ──► ZeroProductDisjunction K ;  ZeroOrApart K ──► NeImpliesApart K
UnrestrictedLUB K ──► WLPO ;  BoundedMonotoneConvergence K ──► LPO
```

### Open arrows (unsolved implications; none is claimed false)

| Arrow | Status |
|---|---|
| (no hypothesis) → `UnrestrictedCompleteness K` (equivalently → `CauchyApprox K`) | OPEN |
| (no hypothesis) → `ModulusFreeCompleteness K`, `ModulusSelection K`, `RatModulusSelection K` | OPEN |
| `UnrestrictedCompleteness K` → `CauchySequenceLifting K` / `SequenceApprox K` / `SequenceLifting K` | OPEN |
| `ChoiceNN` → `SequenceLifting K` | OPEN |
| `UnrestrictedCompleteness K` → `ChoiceNN` (or any choice fragment) | OPEN |
| `ModulusFreeCompleteness K` → `ModulusSelection K` | OPEN |
| `MarkovPrinciple` → `LPO`, `WLPO` → `LPO`, `WLPO` → `UnrestrictedLUB K`, `LPO` → `BoundedMonotoneConvergence K` | OPEN (not attempted in Lean; no claim) |
| (no hypothesis) → `MarkovPrinciple`, `LPO`, `WLPO` | OPEN in this development; no independence claimed |
| `ZeroProductDisjunction K` → `ZeroOrApart K` (or → `LPO`) | OPEN |
| every inhabited bounded predicate has `SupData` | OPEN; it would imply `UnrestrictedLUB K`, hence `WLPO` |

## 4–7. Summary of results by checkpoint

* **Algebra:** see the separation of unconditional and conditional laws in Checkpoint C.
* **Least upper bound:** `SupData.isLUB` is a genuine least-upper-bound theorem *for sets
  equipped with `SupData`*. It is not an unrestricted order-completeness theorem.
* **Primitive prefix counts:** not Cauchy, and independent of the ray. See the source-data table
  in Checkpoint E.
* **Extension and uniqueness (F):** proved, as stated in Checkpoint F.

## 8. OPEN questions

1. `UnrestrictedCompleteness K` with no hypothesis. By `complete_iff_cauchyApprox` this is
   equivalent to producing approximation data `∃ q M` from the available `∀ i, ∃ q`.
2. Modulus-free completeness, and modulus selection without `ChoiceNN`.
3. Whether `UnrestrictedCompleteness K` implies `ChoiceNN`, `SequenceApprox K` or any lifting
   principle.
4. `MarkovPrinciple`, `LPO` and `WLPO` themselves: neither proved nor refuted here. External
   results about other foundations are background only.
5. The unrestricted least-upper-bound property, and bounded monotone convergence. Only the
   implications to `WLPO` and to `LPO`, respectively, are proved.
6. A canonical, choice-free numerical value for a ray.

None of these is reported as impossible. The absence of a proof is not a proof of
non-derivability.

## 9. Build evidence and axioms

* Targeted builds of each new module:
  * `lake build TreeAnalysis.CompletenessStrength`
  * `lake build TreeAnalysis.LiftingPrinciples`
  * `lake build TreeAnalysis.ApartnessStrength`
  * `lake build TreeAnalysis.SupremumScope`
  * `lake build TreeAnalysis.PrimitiveDataScope`
  * `lake build TreeAnalysis.CompletionCharacterization`

  Every one succeeded with no errors and no warnings.
* Final integration build: `lake build TreeAnalysis Audit` (59 jobs, which includes both Task 03
  audit files) succeeded with no errors. The raw audit outputs were produced with
  `lake env lean Audit/AxiomAuditTask03.lean` and `lake env lean Audit/ClosureAuditTask03.lean`.
* `#print axioms`, from `Audit/axioms_task03.txt` (181 declarations):
  * 46 depend on no axioms;
  * 61 depend on `[Quot.sound]`;
  * 1 depends on `[propext]` (`regular_rep_bishop`);
  * 73 depend on `[propext, Quot.sound]`.

  No declaration depends on `Classical.choice` or on any other axiom. `propext` enters only
  through the existing exactness lemma `mkR_exact` (`relTo` lifts `SeqEquiv` into `Prop`).
  `Quot.sound` enters through the quotients and function extensionality.

  Representative entries:
  ```text
  'TreeR.complete_of_choice' depends on axioms: [propext, Quot.sound]
  'TreeR.complete_iff_cauchyApprox' depends on axioms: [propext, Quot.sound]
  'TreeR.neImpliesApart_iff_markov' depends on axioms: [propext, Quot.sound]
  'TreeR.zeroOrApart_iff_lpo' depends on axioms: [propext, Quot.sound]
  'TreeR.SupData.isLUB' depends on axioms: [propext, Quot.sound]
  'TreeR.wlpo_of_unrestrictedLUB' depends on axioms: [propext, Quot.sound]
  'TreeR.lpo_of_bmc' depends on axioms: [propext, Quot.sound]
  'PrimitiveScope.prefixCount_not_isCauchy' does not depend on any axioms
  'Ray.encode_letter_choice_dependence' depends on axioms: [propext, Quot.sound]
  'TreeR.extendR_unique' depends on axioms: [propext, Quot.sound]
  'TreeR.exists_floor' does not depend on any axioms
  ```
* **Effective closure audit** (`Audit/closure_task03.txt`). For 16 central results, the full
  transitive closure of constants was traversed. In every case:
  * the closure contains **no constant with a `Classical` component**;
  * the only axioms are `propext` and `Quot.sound`.

  Built-in number constants occur only through Lean's automatically generated
  constructor-index helpers: `List.ctorIdx`, `Bool.ctorIdx` and `noConfusion_of_Nat`, together
  with the `Nat.*` constants they mention. Lean 4.28 uses these for `injection`, `cases` and
  `nomatch` on every inductive type. No project declaration mentions them. This matches the
  Task 01 and Task 02 audits.

## 10. Firewall confirmation

* There is no mathlib and no external package (`lake-manifest.json` is unchanged).
* A search of the new mathematical modules for `Nat`, `Int`, `Rat`, `Fin`, `PNat`, `UInt*`,
  `USize`, `BitVec`, `Real`, `Classical`, `classical`, `noncomputable`, `omega`, `norm_num`,
  `ring`, `linarith`, `simp`, `simpa`, `sorry`, `admit`, `axiom`, `unsafe`, `partial`,
  `implemented_by`, `native_decide` and `aesop` finds matches only in comments. Examples are the
  words "Real closeness", "omega ray" and "no global instance or axiom".
* The only remaining match is the core function `decide` in `gapTest`. It is the Boolean
  projection of the project's own decidability instance `TOField.decLT`, not the `decide`
  tactic, and it imports no arithmetic.
* All indices, bounds and precisions are `TreeN`. All rationals are elements of a `TOField`
  populated only by `TreeQ`.
* Additional principles (`ChoiceNN`, `MarkovPrinciple`, `LPO`, `WLPO`, `SequenceLifting K` and
  the other new principles) appear only as `def … : Prop` and as explicit hypotheses. There is
  no new `axiom`, no global instance, and no use of `Classical`.
* The audit meta-programs in `Audit/` use Lean's metaprogramming API, which is outside the
  mathematical source. They contain no `partial` and are not imported by any mathematical
  module.
