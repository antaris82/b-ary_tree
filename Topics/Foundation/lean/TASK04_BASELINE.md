# TASK 04 — Baseline (state of the Task 03 repository before any Task 04 change)

The baseline is the repository as supplied (git commit `d4368be`, "Initial commit"). It was
established by reading the Lean sources and signatures, not only `REPORT_TASK03.md`. It was not
rebuilt from scratch: one ordinary `lake build TreeFoundations TreeAnalysis Audit` confirmed that
the supplied tree compiles (60 jobs, no errors).

Notation: `K` is an implicit `{K : Type} [TOField K]`. `α` is an alphabet, with `[TwoLetters α]`
wherever the field structure is needed. `eps k = inv (natCast (twoPow k))`, with `k : TreeN`.

## 1. Carriers, operations and equality at each level

| Level | Carrier (exact Lean) | Equality / identification | Operations (source) |
|---|---|---|---|
| unit child | `inductive UnitChild \| only` (`PrimitiveTree/UnitChild.lean`) | Lean equality | — |
| unary path | `abbrev UnaryPath := List UnitChild` (`PrimitiveTree/UnaryPaths.lean`) | Lean equality of lists | `zeroPath := []`, `onePath := [only]`, `extend p := only :: p`, `concat`, `iterate` |
| `TreeN` | `abbrev TreeN := UnaryPath` (`TreeNumbers/PathNaturals.lean`) | Lean equality (decidable: `TreeN.decEq`) | `zero`, `one`, `succ := extend`, `add := concat`, `mul` (repeated concatenation: `[] * n = []`, `(c :: m) * n = n + m * n`) |
| order on `TreeN` | `inductive PathLT`, `inductive PathLE` (`TreeNumbers/PathOrder.lean`) | — | `compare : Trichotomy m n` (data), `decLT`, `decLE`, `diff` (truncated path difference) |
| unit-edge sums | `Word.edgeFold`, `unitSum`, `pathSum w := unitSum (rootEdges w)` (`PrimitiveTree/RootEdges.lean`) | — | fold over the actual edge list, increment `one` |
| `TreeZ` | `structure TreeZ where pos neg : TreeN; normal : pos = zero ∨ neg = zero` (`TreeNumbers/PathIntegers.lean`) | Lean equality of **normalized** pairs; raw relation `PairEq m n p q := m + q = p + n` | `mkZ m n` (normalization by `normPair`), `add`, `negate` (swap), `mul` (`(pp'+nn', pn'+np')`), `ofN n := mkZ n zero`, `NonNeg x := x.neg = zero`, `LE x y := NonNeg (y + -x)`, `sign`, `absN` |
| fraction data | `structure Frac where num : TreeZ; den : TreeN; pos : PathLT zero den` (`TreeNumbers/PathFractions.lean`) | `Eqv f g := f.num * ofN g.den = g.num * ofN f.den` | `add`, `neg`, `mul`, `inv` (by the constructive `sign` of the numerator, `inv` of zero is zero) |
| triple paths | `structure TriplePath α where p1 p2 p3 : Word α; ne12 ne13 ne23; gt : PathLT (pathSum p3) (pathSum p2)` (`TreeNumbers/PathTriples.lean`) | `Rel t t' := numer t * ofN (denom t') = numer t' * ofN (denom t)` with `numer t := mkZ (pathSum p1) (pathSum p2)`, `denom t := diff (pathSum p3) (pathSum p2)` | witness `witness p q D hD` with addresses `l0^m`, `l1^n`, `l0·l1^(k−1)` |
| `TreeQ` | `def TreeQ α := Quot (TriplePath.Rel (α := α))` (`TreeNumbers/PathRationalField.lean`) | kernel quotient; `TreeQ.sound`, `TreeQ.exact` | `ofF f := mk (ofFrac f)`, `addQ`, `mulQ`, `negQ`, `invQ` lifted from `Frac` by `lift1`/`lift2` with explicit compatibility |
| order on `TreeQ` | `NonnegQ`, from the `TreeZ` sign of the numerator (`TreeAnalysis/RationalOrder.lean`) | — | `archQ` (explicit Archimedean bound, computed by the structural search `findFirst`) |
| `QStar` | `abbrev QStar := TreeQOmega = TreeQ ChildOmega` with `ChildOmega := TreeN` | — | — |
| Cauchy data | `structure CSeq K where seq : TreeN → K; mod : TreeN → TreeN; isMod : IsModulus seq mod` (`TreeAnalysis/CauchyData.lean`) | `SeqEquiv s t := ∀ k, ∃ N, ∀ n, N ≤ n → abs (s n - t n) ≤ eps k` | `constSeq`, `addSeq`, `negSeq`, `mulSeq` (modulus `mulMod` from the derived bound `bnd`), `invSeq` under a positivity witness |
| `TreeR` | `def TreeR K := Quot (CRel (K := K))`, `CRel a b := SeqEquiv a.seq b.seq` (`TreeAnalysis/RealQuotient.lean`) | kernel quotient; `mkR_sound`, `mkR_exact` | `ofQ`, `addR`, `negR`, `mulR`; order `RPos`, `RNonneg`, `<`, `≤`, `RApart` (`TreeAnalysis/RealOrderApartness.lean`) |
| `TreeRStar` | `abbrev TreeRStar := TreeR QStar` (`TreeAnalysis/Instances.lean`) | — | `ofZR z := ofQ (ofZ z)` |

## 2. Class instances and their direct proof dependencies

| Instance | Concrete proofs supplying the fields |
|---|---|
| `TreeN.instCSR : CSR TreeN` | `TreeN.add_assoc`, `add_comm`, `zero_add`, `mul_assoc`, `mul_comm`, `one_mul`, `zero_mul`, `left_distrib` (all by list induction in `PathNaturals.lean`) |
| `TreeZ.instCRing : CRing TreeZ` | `TreeZ.add_assoc'`, `add_comm'`, `zero_add'`, `mul_assoc'`, `mul_comm'`, `one_mul'`, `zero_mul'`, `left_distrib'`, `neg_add_cancel'` (all via `mkZ_sound` and `TreeN` laws) |
| `TreeQ.instCRing : CRing (TreeQ α)` | `TreeQ.add_assoc'` … `neg_add_cancel'` (via `ind_ofF`, `ofF_sound` and `Frac` laws) |
| `TreeQ.instTField : TField (TreeQ α)` | `invQ`, `zero_ne_one'`, `mul_inv_cancel''`, `inv_zero'`, `charZero'` |
| `TreeQ.instTOField : TOField (TreeQ α)` | `NonnegQ`, `decNonnegQ`, `nonnegQ_add`, `nonnegQ_mul`, `nonnegQ_total`, `nonnegQ_antisymm`, `archQ`, `archQ_spec` |
| `TreeR.instCRing : CRing (TreeR K)` | `TreeR.add_assoc'` … `neg_add_cancel'` (via `ind_mkR`, `mkR_sound` and the `TOField` laws of `K`) |

No other instances of `CSR`, `CRing`, `TField` or `TOField` exist. In particular there is **no**
`TField (TreeR K)` instance.

## 3. Existing theorems (full propositions and hypotheses)

The complete list of Task 01–03 names, each with its proposition and hypotheses, is in
`REPORT.md` (Task 01), `REPORT_TASK02.md` and `REPORT_TASK03.md`. Those statements were checked
against the source. The ones the Task 04 ledger depends on are restated verbatim, with status,
in `FINAL_PROPERTY_MATRIX.md`. Key examples:

* `Word.unitSum_rootEdges (w : Word α) : unitSum (rootEdges w) = depth w`
* `TreeN.mul_left_cancel {k m n} (hk : PathLT zero k) (h : k * m = k * n) : m = n`
* `TreeZ.mkZ_sound (h : PairEq m n p q) : mkZ m n = mkZ p q`; `TreeZ.mkZ_exact` (converse)
* `TreeZ.mul_eq_zero {x y : TreeZ} (h : x * y = 𝟘) : x = 𝟘 ∨ y = 𝟘` (a genuine disjunction)
* `TriplePath.universal_witness [TwoLetters α] (A : TreeZ) (D : TreeN) (hD : PathLT zero D) : ∃ t : TriplePath α, numer t = A ∧ denom t = D`
* `TreeQ.exact {t t' : TriplePath α} (h : mk t = mk t') : Rel t t'`
* `TreeQ.mul_inv_cancel'' (x : TreeQ α) (hx : x ≠ zeroQ) : x * invQ x = oneQ`
* `TreeR.mkR_eq_iff (a b : CSeq K) : (mkR a = mkR b → SeqEquiv a.seq b.seq) ∧ (SeqEquiv a.seq b.seq → mkR a = mkR b)`
* `TreeR.exists_inv_of_apart {x : TreeR K} (h : RApart x 𝟘) : ∃ y, x * y = 𝟙`
* `TreeR.inv_iff_markov : (∀ x : TreeR K, x ≠ 𝟘 → ∃ y, x * y = 𝟙) ↔ MarkovPrinciple`
* `TreeR.zeroOrApart_iff_lpo : ZeroOrApart K ↔ LPO`
* `TreeR.wlpo_of_unrestrictedLUB (h : UnrestrictedLUB K) : WLPO` (one way only)
* `TreeR.lpo_of_bmc (h : BoundedMonotoneConvergence K) : LPO` (one way only)
* `TreeR.complete_iff_cauchyApprox : (UnrestrictedCompleteness K → CauchyApprox K) ∧ (CauchyApprox K → UnrestrictedCompleteness K)`
* `TreeR.complete_of_choice (hc : ChoiceNN) : UnrestrictedCompleteness K`
* `TreeR.modulusFreeComplete_of_choice (hc : ChoiceNN) : ModulusFreeCompleteness K`
* `TreeR.SupData.isLUB (D : SupData S) : IsLUB S D.sup`
* `PrimitiveScope.prefixCount_not_isCauchy (r : Ray α) : ¬ IsCauchy (prefixCount (K := K) r)`

The named principles, all `def … : Prop`, never axioms or instances:
`ChoiceNN := ∀ P : TreeN → TreeN → Prop, (∀ k, ∃ N, P k N) → ∃ f, ∀ k, P k (f k)`;
`MarkovPrinciple := ∀ p : TreeN → Bool, ¬¬(∃ n, p n = true) → ∃ n, p n = true`;
`LPO := ∀ p, (∃ n, p n = true) ∨ (∀ n, p n = false)`;
`WLPO := ∀ p, (∀ n, p n = false) ∨ ¬(∀ n, p n = false)`;
`NeImpliesApart K := ∀ x : TreeR K, x ≠ 𝟘 → RApart x 𝟘`;
`SequenceLifting K`, `CauchySequenceLifting K`, `SequenceApprox K`, `CauchyApprox K`,
`ModulusSelection K`, `RatModulusSelection K`, `ModulusFreeCompleteness K`,
`UnrestrictedCompleteness K`, `UnrestrictedLUB K`, `BoundedMonotoneConvergence K`,
`ZeroOrApart K`, `ZeroProductDisjunction K`.

## 4. Definitions and interfaces, as distinct from proofs

* `CSR`, `CRing`, `TField`, `TOField`, `FieldIso`, `OFieldHom` and `RealIso` are **interfaces**
  (structures or classes). An interface theorem counts as a fact about a carrier only through
  one of the concrete instances in §2.
* `TOField` stores an Archimedean **bound function** `archBound` (data) together with its
  specification.
* Every named principle in §3 is a definition only. None is asserted.
* `Tracked`, `SupData` and `TrackedCauchyTower` are records of explicit data. Results about
  them hold only for inputs that come with that data.

## 5. Mismatches between the Task 03 prose and the Lean declarations

1. The module docstring of `TreeAnalysis/CompletenessStrength.lean` lists `rcauchyMod_symm`. No
   declaration of that name exists; the two-sided form is `rcauchyMod_close` / `rcauchyMod_iff_close`.
2. `complete_iff_cauchyApprox`, `mkR_eq_iff`, `TreeQ.mk_eq_mk_iff` and `TreeQ.ofF_eq_ofF_iff` are
   stated as **conjunctions of two implications**, not with `↔`. The content is the same; the
   report's word "iff" refers to this conjunction.
3. `NeImpliesApart`, `exists_inv_of_ne_of_markov` and `markov_of_inv` are in the root namespace
   (`TreeAnalysis/Instances.lean`). This was already noted in `TASK03_BASELINE.md`.
4. The `CompletenessScope.lean` docstring names `sup_of_supData`, which does not exist (already
   noted in Task 03).
5. `UnrestrictedCompleteness K` covers only Cauchy sequences **given with a modulus function**.
   The name could suggest more.
6. Task 02 states the embedding chain `TreeN → TreeZ → TreeQ → TreeR` only over `QStar`
   (`ofZR`, `natR_eq_ofZR`). For a general alphabet it was not stated. Task 04 adds it
   (`TreeR.ofZRα`, `natR_eq_ofZRα`).
7. `TreeZ` had no strict order. Reflection of the order by `TreeN → TreeZ` was not proved. Task
   04 adds both (`TreeZ.LT`, `TreeZ.le_of_ofN_le`).

## 6. Already-known OPEN items that a title might suggest are solved

* "Completeness" (`UnrestrictedCompleteness`, `CompletenessScope.lean`) is **not** proved
  unconditionally. Only `ChoiceNN → …` and the equivalence with `CauchyApprox K` are proved.
* "Inverse" (`mul_rinv`) needs an apartness **witness**. The conventional inverse law is
  equivalent to `MarkovPrinciple`, which is not proved.
* "Supremum" (`SupData.sup`) needs explicit `SupData`. The unrestricted least-upper-bound
  property is open; only `UnrestrictedLUB K → WLPO` is proved.
* "Arity independence" of `TreeR` is an isomorphism built from the letter-based witness map.
  No canonical, choice-free identification of rays with reals is claimed.
