# Task 03 — baseline inventory (reconstructed from the Task 02 source code)

Base: the Task 02 repository as supplied (git commit `940609d`, "Initial commit"), built with
`lake build TreeAnalysis` before any Task 03 change (39 jobs, no errors, no warnings).

All statements below were read from the source files, not from report labels.
`K` is always an implicit `{K : Type} [TOField K]` (a decidable, Archimedean ordered field
interface, populated in this project only by the triple-path rationals `TreeQ α`; the fixed base
is `QStar`, and `TreeRStar := TreeR QStar`). Precisions are `eps k = 1/2^k`, with `k : TreeN`.

## (i) Exact proved statements and (ii) their assumptions

| Name (actual) | File | Exact statement (transcribed) | Assumptions |
|---|---|---|---|
| `TOField.IsCauchy s` | CauchyData | `∀ δ, 0 < δ → ∃ N, ∀ m n, N ≤ m → N ≤ n → abs (s m - s n) < δ` (a `Prop`) | definition |
| `TOField.IsModulus s μ` | CauchyData | `∀ k m n, μ k ≤ m → μ k ≤ n → abs (s m - s n) ≤ eps k` | definition |
| `TOField.IsRegular s` | CauchyData | `∀ m n, abs (s m - s n) ≤ eps m + eps n` | definition |
| `TOField.CSeq K` | CauchyData | structure `seq : TreeN → K`, `mod : TreeN → TreeN`, `isMod : IsModulus seq mod` | definition |
| `TOField.SeqEquiv s t` | CauchyData | `∀ k, ∃ N, ∀ n, N ≤ n → abs (s n - t n) ≤ eps k` | definition |
| `TOField.reg c` | CauchyData | `fun n => c.seq (rho c.mod n)` | definition |
| `TOField.isRegular_reg c` | CauchyData | `IsRegular (reg c)` | none |
| `TOField.reg_equiv c` | CauchyData | `SeqEquiv (reg c) c.seq` | none |
| `TOField.seqEquiv_iff_bishop` | CauchyData | for `IsRegular s`, `IsRegular t`: `(SeqEquiv s t → ∀ n, abs (s n - t n) ≤ eps n + eps n) ∧ (converse)` | regularity of both |
| `TOField.exists_modulus_of_choice` | CauchyData | `IsCauchy s → ∃ μ, IsModulus s μ` | explicit choice premise `∀ P, (∀ k ∃ N, P k N) → ∃ f, ∀ k, P k (f k)` |
| `TreeR K` | RealQuotient | `Quot (CRel (K := K))`, `CRel a b := SeqEquiv a.seq b.seq` | definition |
| `TreeR.mkR_exact` | RealQuotient | `mkR a = mkR b → SeqEquiv a.seq b.seq` | none (uses `propext` via `Quot.lift` into `Prop`) |
| `TreeR.ofQ_injective` | RealQuotient | `ofQ p = ofQ q → p = q` | none |
| `TreeR.ConvergesTo f L` | CompletenessScope | `∀ k, ∃ N, ∀ n, N ≤ n → f n ≤ L + ofQ (eps k) ∧ L ≤ f n + ofQ (eps k)` (`Prop`-level `N`) | definition |
| `TreeR.limit_unique` | CompletenessScope | `ConvergesTo f L → ConvergesTo f L' → L = L'` | none |
| `TreeR.ofQ_seq_converges c` | CompletenessScope | `ConvergesTo (fun n => ofQ (c.seq n)) (mkR c)` | none |
| `TreeR.rat_dense x k` | CompletenessScope | `∃ q, ofQ q ≤ x + ofQ (eps k) ∧ x ≤ ofQ q + ofQ (eps k)` | none |
| `TreeR.RCauchyMod f ν` | CompletenessScope | `∀ k i j, ν k ≤ i → ν k ≤ j → f i ≤ f j + ofQ (eps k)` (one-sided) | definition |
| `TreeR.RCauchy f` | CompletenessScope | `∀ k, ∃ N, ∀ i j, N ≤ i → N ≤ j → f i ≤ f j + ofQ (eps k)` | definition |
| `TreeR.UnrestrictedCompleteness K` | CompletenessScope | `∀ f ν, RCauchyMod f ν → ∃ L, ConvergesTo f L` | definition (**with** a modulus `ν`, despite the name) |
| `TreeR.SequenceLifting K` | CompletenessScope | `∀ f : TreeN → TreeR K, ∃ g : TreeN → CSeq K, ∀ i, mkR (g i) = f i` | definition |
| `TreeR.ChoiceNN` | CompletenessScope | `∀ P : TreeN → TreeN → Prop, (∀ k, ∃ N, P k N) → ∃ f, ∀ k, P k (f k)` | definition |
| `TreeR.TrackedCauchyTower K` | CompletenessScope | structure `r : TreeN → CSeq K`, `ν`, `cauchy : ∀ k i j, ν k ≤ i → ν k ≤ j → mkR (r i) ≤ mkR (r j) + ofQ (eps k)` | definition |
| `TreeR.tower_limit T` | CompletenessScope | `∃ L, ConvergesTo (fun i => mkR (T.r i)) L` | none |
| `TreeR.complete_of_lifting` | CompletenessScope | `SequenceLifting K → UnrestrictedCompleteness K` | premise as displayed |
| `TreeR.complete_of_lifting_choice` | CompletenessScope | `SequenceLifting K → ChoiceNN → RCauchy f → ∃ L, ConvergesTo f L` | premises as displayed |
| `TreeR.SupData S` | CompletenessScope | structure `u : TreeN → K`, `s : TreeN → TreeR K`, `mem : ∀ k, S (s k)`, `upper : ∀ k x, S x → x ≤ ofQ (u k)`, `approx : ∀ k, ofQ (u k) ≤ s k + ofQ (eps k)` | definition |
| `TreeR.SupData.sup` | CompletenessScope | `mkR (CSeq.ofRegular D.u _)` | definition |
| `TreeR.SupData.le_sup` | CompletenessScope | `S x → x ≤ D.sup` | none |
| `TreeR.SupData.sup_approx` | CompletenessScope | `D.sup ≤ D.s (k+2) + ofQ (eps k)` | none |
| `NeImpliesApart K` | Instances (**root namespace**) | `∀ x : TreeR K, x ≠ 0 → RApart x 0` | definition |
| `exists_inv_of_ne_of_markov` | Instances (root) | `NeImpliesApart K → x ≠ 0 → ∃ y, x * y = 1` | premise as displayed |
| `markov_of_inv` | Instances (root) | `(∀ x, x ≠ 0 → ∃ y, x * y = 1) → NeImpliesApart K` | premise as displayed |
| `TreeR.exists_inv_of_apart` | RealOrderApartness | `RApart x 0 → ∃ y, x * y = 1` | none |
| `TreeR.apart_of_mul_eq_one` | RealOrderApartness | `x * y = 1 → RApart x 0` | none |
| `TreeR.lt_cotrans z` | RealOrderApartness | `x < y → x < z ∨ z < y` | none |
| `Ray.pathSum_prefixAt r n` | TreeFoundation/InfiniteRays | `pathSum (prefixAt r n) = n` | none |
| `Word.unitSum_rootEdges w` | PrimitiveTree/RootEdges | `unitSum (rootEdges w) = depth w` | none |

## (iii) Status of the named open goals at the start of Task 03

| Goal | Status at baseline |
|---|---|
| `UnrestrictedCompleteness K` without hypotheses | OPEN (only `SequenceLifting K → …` proved) |
| modulus-free completeness | proved only from `SequenceLifting K` **and** `ChoiceNN` |
| conventional inverse `x ≠ 0 → ∃ y, x·y = 1` | equivalent to `NeImpliesApart K`; relation to Markov's principle **not** proved |
| `SupData.sup` is the *least* upper bound | **not** stated (only `le_sup`, `sup_approx`) |
| unrestricted least upper bound, bounded monotone convergence | not stated |
| extension of uniformly continuous maps | not present |

## (iv) Minimal dependency map

```text
PrimitiveTree.RootEdges (rootEdges, unitSum, pathSum, depth)
  -> TreeNumbers.PathNaturals/PathOrder (TreeN = List UnitChild, order, maxN)
  -> TreeNumbers.PathIntegers (TreeZ) -> PathTriples/PathRationalField (TreeQ α, QStar)
  -> TreeAnalysis.OrderedField (TOField interface) -> RationalOrder (TreeQ is a TOField)
  -> DyadicPrecision (eps) -> CauchyData (IsCauchy, IsModulus, IsRegular, CSeq, reg)
  -> CauchyOps -> SeqOrder -> RealQuotient (TreeR := Quot CRel, ring)
  -> RealOrderApartness (order, apartness, inverses, density, cotransitivity)
  -> CompletenessScope (ConvergesTo, towers, SequenceLifting, SupData)
  -> ArityCompletionTransfer -> Instances (TreeRStar, NeImpliesApart)
TreeFoundation.InfiniteRays (Ray, prefixAt) -> BoundaryTopology.* -> BinaryEncoding (encode)
```

## (v) Mismatches between prose and signatures

1. `NeImpliesApart`, `exists_inv_of_ne_of_markov`, `markov_of_inv` live in the **root namespace**
   (file `TreeAnalysis/Instances.lean`), not in `TreeR` as the Task 03 navigation list says.
2. The module docstring of `CompletenessScope.lean` names `sup_of_supData`; no declaration of that
   name exists. The supremum results are `SupData.sup`, `SupData.le_sup`, `SupData.sup_approx`.
3. `UnrestrictedCompleteness K` quantifies only over Cauchy sequences **with a modulus function**
   `ν`; it is not the modulus-free statement its name might suggest.
4. "Markov-type" for `NeImpliesApart K` was descriptive only: Task 02 proves no reduction to or
   from a standard Markov principle. (Task 03 now proves the two-way reduction, see the report.)
5. The Task 02 report says unconditional completeness "needs `SequenceLifting K`". The code
   proves only sufficiency; necessity was never proved. (Task 03 shows that the weaker `ChoiceNN`
   already suffices; necessity of either principle remains unproved.)
6. `RCauchyMod` and `RCauchy` are stated one-sidedly (`f i ≤ f j + eps k`); the two-sided form
   follows by exchanging `i` and `j` (made explicit in Task 03 as `rcauchyMod_iff_close`).
