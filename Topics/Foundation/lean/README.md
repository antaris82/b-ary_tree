This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Tree-path number foundations (Lean 4 core, no Mathlib)

Natural numbers, integers, rationals and a constructive completion, built from finite root paths
of rooted trees, with every law proved in Lean 4.28.0 core (no Mathlib, no `Classical`, no `sorry`,
no added axioms). Every project constant depends at most on the kernel axioms `propext` and
`Quot.sound`; this is enforced by a fail-closed audit (below).

## Entry points

* Libraries: `TreeFoundations` (trees, `TreeN`, `TreeZ`, `TreeQ α`, child-direction algebra) and
  `TreeAnalysis` (orders, `TreeR K`, boundary topology). Roots: `TreeFoundations.lean`,
  `TreeAnalysis.lean`.
* `FINAL_PROVENANCE.md` — where each number structure comes from (role of the unary tree `T₁`,
  role of branching, comparison with fraction classes).
* `FINAL_AXIOM_AND_LAW_MATRIX.md` — one row per claim with exact Lean declaration, hypotheses,
  status and axioms (generated mechanically; signatures in `release/declaration_signatures.txt`).
* `FINAL_OPEN_QUESTIONS.md`, `REVIEW_DISPOSITION.md`, `VERIFICATION_LOG.md`.
* Per-carrier certificates (one conjunction of all laws each): `Task04.treeN_certificate`,
  `Task04.treeZ_certificate`, `Task04.treeQ_certificate`, `Task04.treeR_unconditional_certificate`,
  `Task04.treeR_conditional_certificate`, `Task04.treeR_convergence_certificate`
  (module `TreeAnalysis/Task04Summary.lean`; the module name is historical).

## Strongest unconditional structures (proved)

* `TreeN := List UnitChild` (vertices of `T₁`): commutative semiring with additive cancellation,
  cancellation by positive factors, no zero divisors, decidable total order compatible with `+`
  and `·`, induction and unique structural recursion. For any alphabet with a letter, the depth
  quotient of the full tree is an isomorphic ordered semiring (`DepthQuotient.depthIso`).
* `TreeZ` (normalized oriented differences of path counts): commutative ring, `0 ≠ 1`,
  zero-product disjunction, cancellation, decidable total order, faithful order embedding of
  `TreeN`.
* `TreeQ α` (classes of valid triples of pairwise distinct root paths, `[TwoLetters α]`):
  Archimedean field of characteristic zero with a decidable total order compatible with the
  operations; ordered-field isomorphic to the internal fraction quotient `FracQ`
  (`TreeQ.orderedFieldIsoFracQ`); the isomorphisms between alphabets are unique.
* `TreeR K` (quotient of explicitly modulated rational Cauchy data): commutative ring with
  `0 ≠ 1`; strict order irreflexive, transitive, cotransitive, tight, compatible with `+` and `·`;
  Archimedean; rationals dense; inverse for every element **apart** from zero; cancellation and
  zero-product implication under `≠`; limits unique; explicit limits for tracked data, closed under
  `+`, `-`, `·` and finite expressions; every rational-valued sequence with a modulus converges.

## Major conditional or open properties of `TreeR` (not proved unconditionally)

* Inverse for every `x ≠ 0` ⇔ `MarkovPrinciple` (so no conventional field instance is installed).
* `ZeroOrApart K` ⇔ `LPO`; `Trichotomy K` ⇔ `LPO`; `DecidableZero K` ⇔ `WLPO`.
* `UnrestrictedCompleteness K` (Cauchy sequences **with a modulus**) ⇔ `CauchyApprox K`; it follows
  from `ChoiceNN`. `ModulusFreeCompleteness K` follows from `ChoiceNN`; both are open
  unconditionally.
* Least upper bounds exist for sets with explicit `SupData` (data-dependent); the unrestricted
  least-upper-bound property and bounded monotone convergence are open (they would imply `WLPO`,
  resp. `LPO` — one-way lower bounds, not independence results).
* Totality of `≤` and the zero-product disjunction are not proved (the latter follows from `LPO`).

`TreeR` is therefore **not** claimed to be a conventional field, a linearly ordered field, an
unrestricted Cauchy-complete or a Dedekind-complete system.

## Verification

```
./scripts/verify_release.sh
```

runs, failing at the first error: the library build; `scripts/source_check.py` (forbidden tokens,
numeric literals, foreign imports, coverage); the kernel-level audit `ReleaseAudit/Run.lean`
(`#fail_closed_audit` over all project constants, `#require_decls`); the axiom report;
`scripts/negative_fixtures.sh` (controlled violations generated outside the repository must make
the audit fail); and `leanchecker` replays. See `VERIFICATION_LOG.md` for the recorded run.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
