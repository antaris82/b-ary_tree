# FINAL PROVENANCE — `TreeN`, `TreeZ`, `TreeQ α`, `TreeR K`

This document states, from the actual Lean definitions, where each number structure comes from,
which data are primitive, and what role the branching of the trees plays. Every claim names the
declaration that supports it; status and axioms of each are in `FINAL_AXIOM_AND_LAW_MATRIX.md`.

## 1. `TreeN`: the vertices of the unary tree `T₁`

**Definition (unchanged since Task 01).**

```
inductive UnitChild | only                         -- PrimitiveTree/UnitChild.lean
abbrev UnaryPath := List UnitChild                 -- PrimitiveTree/UnaryPaths.lean
abbrev TreeN := UnaryPath                          -- TreeNumbers/PathNaturals.lean
zero := [] ; one := [only] ; succ n := only :: n
add := concatenation ; mul: [] * n = [], (c :: m) * n = n + m * n
```

So `TreeN` *is* the vertex set `Word UnitChild` of the full unary tree `T₁`: the root is `zero`
and the one-edge extension is `succ`. It is **not** defined from an arbitrary `b`-ary tree; the
arity `b` of `Child b` is itself an element of `TreeN` (`Child b := {idx : TreeN // PathLT idx b}`),
so the finite-arity trees are built *after* `TreeN`.

Facts linking `TreeN` with unit-edge sums of actual root paths:

* `Word.unitSum_rootEdges : unitSum (rootEdges w) = depth w` — the unit-edge sum is a fold over
  the list of actual parent–child edges, *not* defined as depth; equality is a theorem.
* `UnaryTree.pathSum_self : pathSum p = p` for `p : Word UnitChild` — in `T₁` the unit-edge sum
  of a vertex is that very vertex; `UnaryTree.count_realized`, `UnaryTree.count_unique`.
* All semiring, cancellation and order laws are proved by list induction
  (`TreeN.instCSR`, `Task04.treeN_certificate`; matrix rows 1–25).

### 1.1 Derived comparison: the depth quotient of an arbitrary tree (Task 05)

`TreeNumbers/DepthQuotient.lean` adds — without changing any carrier — a second presentation of
the same counting structure for any alphabet `α`:

```
DepthRel w v :⇔ Word.pathSum w = Word.pathSum v       DepthClass α := Quot DepthRel
count : DepthClass α → TreeN        (induced by pathSum; letter-free)
realize a : TreeN → DepthClass α    (n ↦ class of the explicit word Word.rep a n)
```

Proved:

| statement | declaration |
|---|---|
| the relation is an equivalence; it can be phrased through `depth` | `depthRel_refl/symm/trans`, `depthRel_iff_depth` |
| a class depends only on the unit-edge sum (both directions) | `cls_eq_iff`, `count_injective` |
| `count (realize a n) = n`, `realize a (count x) = x` | `count_realize`, `realize_count` |
| class-level letter independence; representative words differ | `realize_letter_indep`, `oneD_letter_indep`, `rep_letter_dependent` |
| letter-free operations: grafting (`appL`) induces `+`, repetition induces `·`; root class is `0` | `addD`, `mulD`, `zeroD`, `count_add`, `count_mul`, `count_zero` |
| explicit isomorphism of ordered commutative semirings `TreeN ≅ DepthClass α` (bijection, `0`, `1`, `+`, `·`, `≤` both ways) | `DepthQuotient.depthIso`, `DepthQuotient.csr` |
| the transferred order is "extension by grafting" | `led_iff_graft` |
| no letter ⇒ no positive count is represented; the quotient is the single root class | `no_positive_count_of_noLetter`, `eq_zeroD_of_noLetter`, `empty_no_one` |
| over `UnitChild` the relation identifies nothing (`T₁` is its own depth quotient) | `unary_cls_eq_iff`, `unary_count_cls` |

Interpretation, kept to what is proved: for every alphabet with a letter, collapsing the full
tree by depth yields a structure isomorphic (as an ordered commutative semiring, by an explicit
map) to `TreeN`; the empty alphabet yields only the root (the "singleton root" tree, which does
**not** represent `TreeN`). This compares two representations of one internally derived counting
structure. It does **not** say that branching data are needed for the arithmetic of `TreeN`, and
it does not provide a canonical representative word of a class (only the class is
letter-independent).

## 2. `TreeZ`: normalized oriented differences of unary-path counts

```
structure TreeZ where pos neg : TreeN ; normal : pos = zero ∨ neg = zero   -- PathIntegers.lean
PairEq (m,n) (p,q) :⇔ m + q = p + n ;  mkZ m n := normalization of (m,n)
```

The canonical normalization is proved equivalent to the pair-difference relation
(`TreeN.normPair_pairEq`, `TreeN.normal_unique`, `TreeZ.mkZ_sound`, `TreeZ.mkZ_exact`).
Operations are the path-pair formulas (`TreeZ.add_mk`, `neg_mk`, `mul_mk`). Ring laws, `0 ≠ 1`,
zero-product **disjunction** (`TreeZ.mul_eq_zero : x * y = 𝟘 → x = 𝟘 ∨ y = 𝟘`), cancellation,
decidable total order and the faithful order-preserving/reflecting embedding `ofN : TreeN → TreeZ`
are proved (`Task04.treeZ_certificate`; rows 26–44). No branching is involved.

## 3. `TreeQ α`: classes of valid triples of pairwise distinct root paths

```
structure TriplePath α where p1 p2 p3 : Word α ; ne12 ne13 ne23 ; gt : PathLT (pathSum p3) (pathSum p2)
numer t := mkZ (pathSum p1) (pathSum p2)          -- a TreeZ
denom t := diff (pathSum p3) (pathSum p2)         -- positive TreeN, with denom_spec, denom_pos
Rel t t' :⇔ numer t * ofN (denom t') = numer t' * ofN (denom t)
TreeQ α := Quot (TriplePath.Rel)                  -- PathRationalField.lean (unchanged)
```

**What depends on what.**

* `numer` and `denom` depend **only on the three unit-edge sums** (equivalently depths) of the
  addresses. Hence two valid triples with corresponding equal path sums have the same class
  (`TreeQ.mk_eq_of_pathSum_eq`, `TreeQ.mk_eq_of_depth_eq`), although the triples as addresses
  may differ.
* The branching hypothesis `[TwoLetters α]` (two distinct letters `l0 ≠ l1`) is used only to
  **realize** every signed numerator and every positive denominator by a valid pairwise-distinct
  triple: `TriplePath.witness` uses the addresses `l0^m`, `l1^n`, `l0·l1^(k−1)`
  (`TriplePath.universal_witness`). The operations of `TreeQ α` are lifted from the fraction
  operations through these witnesses (`TreeQ.ofF`, `lift1`, `lift2`).
* Over the one-letter alphabet the pairwise-distinct triple presentation cannot represent the
  zero numerator (`TriplePath.unary_numer_ne_zero`, `unary_no_universal_witness`,
  `unary_toFracQ_ne_zero`). This is an obstruction for **this presentation**, not for fraction
  fields over unary counts: see §3.1.

### 3.1 Comparison with the internal fraction quotient (Task 05)

`TreeAnalysis/FractionCharacterization.lean` defines the auxiliary quotient

```
Frac := {num : TreeZ, den : TreeN, pos : PathLT zero den}     (existing, PathFractions.lean)
FracQ := Quot Frac.Eqv                                        (new, derived)
```

built only from `TreeZ` and positive `TreeN` (no standard rationals), with operations lifted from
the existing `Frac` operations and their proved compatibility.

| statement | declaration |
|---|---|
| `FracQ` is a field of characteristic zero (`inv 0 = 0`), with no alphabet involved | `FracQ.instTField` |
| `toFracQ : TreeQ α → FracQ` (from `TriplePath.toFrac`, letter-free) and `ofFracQ : FracQ → TreeQ α` (from the witness construction) are mutually inverse | `TreeQ.ofFracQ_toFracQ`, `TreeQ.toFracQ_ofFracQ` |
| they preserve `0, 1, +, -, ·, inv` (incl. `inv 0 = 0`) and preserve/reflect `≤` and `<` | `TreeQ.orderedFieldIsoFracQ`, `TreeQ.lt_iff_toFracQ`, `TreeQ.toFracQ_inv_zero` |
| `ofFracQ` is independent of the two witness letters (class level); the representative triple is not | `TreeQ.ofFracQ_letter_indep`, `TreeQ.ofFrac_letter_dependent` |
| coherence: `toFracQ ∘ transfer = toFracQ`, every field iso is compatible, `transfer = ofFracQ ∘ toFracQ`, `arityIso` is the identity on fraction classes, completions act as identity on fraction classes | `TreeQ.toFracQ_transfer`, `toFracQ_fieldIso`, `transfer_eq_ofFracQ_toFracQ`, `arityIso_fracQ`, `TreeR.realArityIso_ofFracQ`, `TreeR.realIso_ofFracQ` |
| scope of the unary obstruction | `TriplePath.unary_obstruction_scope` |

**Result, stated directly.** The arithmetic and order of `TreeQ α` are exactly those of the
fraction classes of signed path-count differences over positive path counts with
cross-multiplication; the triple carrier is an ordered-field-isomorphic presentation of `FracQ`.
The branching condition supplies witness configurations; it does not change any operation. No
branching-dependent operation was added. `TreeQ α` remains the official carrier (an actual
quotient of valid triples); `FracQ` is a derived comparison object.

## 4. `TreeR K`: quotient of explicitly modulated rational Cauchy data

```
structure CSeq K where seq : TreeN → K ; mod : TreeN → TreeN ; isMod : IsModulus seq mod
TreeR K := Quot CRel,  CRel a b := SeqEquiv a.seq b.seq          -- RealQuotient.lean (unchanged)
TreeRStar := TreeR QStar,  QStar := TreeQ ChildOmega
```

Indices, moduli and the precision scale `eps k = inv (natCast (twoPow k))` all live in `TreeN`.
The proved and conditional properties are listed in `README.md` and the matrix (rows 72–126,
151–155); `TreeR` is **not** claimed to be a conventional field, a linearly ordered field, an
unrestricted Cauchy-complete or a Dedekind-complete system.

## 5. Interface laws versus concrete proofs

The classes `CSR`, `CRing`, `TField`, `TOField` are typeclass specifications whose fields include
the algebraic laws. They are not kernel axioms: a field is discharged only by an instance, and
every instance of the project proves each field by a named theorem about the concrete carrier.
Generic lemmas such as `CSR.add_zero` hold for an arbitrary type only under the assumption that
it is an instance. The names are conventional, but no agreement with an external library is
claimed or used; the table below gives the explicit formula of each field.

| field (class) | explicit formula | `TreeN.instCSR` | `TreeZ.instCRing` | `TreeQ.instTField` / `instCRing` | `FracQ.instTField` | `TreeR.instCRing` |
|---|---|---|---|---|---|---|
| `add_assoc` (CSR) | `∀ a b c, a + b + c = a + (b + c)` | `TreeN.add_assoc` | `TreeZ.add_assoc'` | `TreeQ.add_assoc'` | `FracQ.add_assoc'` | `TreeR.add_assoc'` |
| `add_comm` (CSR) | `∀ a b, a + b = b + a` | `TreeN.add_comm` | `TreeZ.add_comm'` | `TreeQ.add_comm'` | `FracQ.add_comm'` | `TreeR.add_comm'` |
| `zero_add` (CSR) | `∀ a, zero + a = a` | `TreeN.zero_add` | `TreeZ.zero_add'` | `TreeQ.zero_add'` | `FracQ.zero_add'` | `TreeR.zero_add'` |
| `mul_assoc` (CSR) | `∀ a b c, a * b * c = a * (b * c)` | `TreeN.mul_assoc` | `TreeZ.mul_assoc'` | `TreeQ.mul_assoc'` | `FracQ.mul_assoc'` | `TreeR.mul_assoc'` |
| `mul_comm` (CSR) | `∀ a b, a * b = b * a` | `TreeN.mul_comm` | `TreeZ.mul_comm'` | `TreeQ.mul_comm'` | `FracQ.mul_comm'` | `TreeR.mul_comm'` |
| `one_mul` (CSR) | `∀ a, one * a = a` | `TreeN.one_mul` | `TreeZ.one_mul'` | `TreeQ.one_mul'` | `FracQ.one_mul'` | `TreeR.one_mul'` |
| `zero_mul` (CSR) | `∀ a, zero * a = zero` | `TreeN.zero_mul` | `TreeZ.zero_mul'` | `TreeQ.zero_mul'` | `FracQ.zero_mul'` | `TreeR.zero_mul'` |
| `left_distrib` (CSR) | `∀ a b c, a * (b + c) = a * b + a * c` | `TreeN.left_distrib` | `TreeZ.left_distrib'` | `TreeQ.left_distrib'` | `FracQ.left_distrib'` | `TreeR.left_distrib'` |
| `neg_add_cancel` (CRing) | `∀ a, -a + a = zero` | — | `TreeZ.neg_add_cancel'` | `TreeQ.neg_add_cancel'` | `FracQ.neg_add_cancel'` | `TreeR.neg_add_cancel'` |
| `zero_ne_one` (TField) | `zero ≠ one` | (`TreeN.zero_ne_one`) | (`TreeZ.zero_ne_one`) | `TreeQ.zero_ne_one'` | `FracQ.zero_ne_one'` | (`TreeR.zero_ne_one`, no `TField`) |
| `mul_inv_cancel` (TField) | `∀ a, a ≠ zero → a * inv a = one` | — | — | `TreeQ.mul_inv_cancel''` | `FracQ.mul_inv_cancel''` | **not** a field: ⇔ `MarkovPrinciple` (`TreeR.inv_iff_markov`) |
| `inv_zero` (TField) | `inv zero = zero` | — | — | `TreeQ.inv_zero'` | `FracQ.inv_zero'` | — |
| `charZero` (TField) | `∀ n, natCast (succ n) ≠ zero` | — | — | `TreeQ.charZero'` | `FracQ.charZero'` | — |
| `Nonneg`, `decNonneg`, `nonneg_add`, `nonneg_mul`, `nonneg_total`, `nonneg_antisymm` (TOField) | decidable positive cone, closed under `+`, `·`, total, antisymmetric | — | (`TreeZ.NonNeg`, separate lemmas) | `TreeQ.NonnegQ`, `decNonnegQ`, `nonnegQ_add`, `nonnegQ_mul`, `nonnegQ_total`, `nonnegQ_antisymm` | — (order `FracQ.LEF`, transported) | — |
| `archBound`, `arch_spec` (TOField) | `∀ x, Nonneg (natCast (archBound x) - x)` (explicit bound) | — | — | `TreeQ.archQ`, `archQ_spec` | — | `TreeR.archimedean` (Prop-level, no `TOField`) |

Entries in parentheses are proved theorems of the carrier that are not fields of an instance.
