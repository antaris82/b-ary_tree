# TASK 06 — Finite Bilinear and Projection Laws

Baseline: final Q14-repaired Task 5, Lean 4.28.0, source fingerprint
`44a6935b4ecb8de9a4215976eddd31da05f18f5a6b400c56ae7efbb7f2b52075` (recomputed and matched before
any edit).

**Result: every requirement (1–3) is formally proved. No mathematical blocker was found.**

## Changes

| file | change |
|---|---|
| `DimensionFoundation/BilinearForm.lean` | **new**: bilinearity of `ChildModule.dot` |
| `DimensionFoundation/ProjectionLaws.lean` | **new**: projection laws for `projL`, `projS` |
| `TreeFoundations.lean` | two new `public import` lines (nothing else) |
| `ReleaseAudit/Run.lean` | 13 more names in `#require_decls` (47 → 60 required declarations) |
| `scripts/gen_matrix.py` | three appended rows (157–159); matrix and `release/declaration_signatures.txt` regenerated |
| `release/*` | verification output, inventory and module DAG refreshed |

No existing definition or theorem was changed. The new modules introduce no carrier, structure,
class, instance or axiom. They use only `ChildModule.{F, addV, negV, smul, zeroV, coordSum, u, InL,
InS, dot, projL, projS}` and existing lemmas: `FinSum.sumC_add`, `sumC_mul_left`, `sumC_neg`,
`sumC_congr`, `sumC_zero`, the `CSR`/`CRing` field laws, `dot_comm`, `dot_u_of_inS`,
`coordSum_addV`, `coordSum_smul`, `add_smul`, `mul_smul`, `zero_addV`, `inS_zero`, `projL_inL`,
`projS_inS`, `decomposition` and `decomposition_unique`.

## Exact theorem signatures

Common context: `{K : Type} [TField K] {b : TreeN}`, with `F K b = Child b → K`.
`hb : TreeN.PathLT TreeN.zero b` means the arity is positive. Every result holds for every
internally constructed field `K` (`TreeQb b` for `b ≥ two`, and `TreeQOmega`). In the axiom
column, `[]` means the result depends on no axiom.

### `DimensionFoundation/BilinearForm.lean` (requirement 1)

| line | declaration | statement | axioms |
|---|---|---|---|
| 27 | `dot_addV_left` | `(x y z : F K b) : dot (addV x y) z = dot x z + dot y z` | `[]` |
| 33 | `dot_addV_right` | `(x y z : F K b) : dot x (addV y z) = dot x y + dot x z` | `[]` |
| 39 | `dot_smul_left` | `(a : K) (x y : F K b) : dot (smul a x) y = a * dot x y` | `[]` |
| 45 | `dot_smul_right` | `(a : K) (x y : F K b) : dot x (smul a y) = a * dot x y` | `[]` |
| 51 | `dot_bilinear_symmetric` | conjunction of the four identities and `dot x y = dot y x` | `[]` |
| 61–74 | `dot_zeroV_left/right`, `dot_negV_left/right` | `dot 0 y = 0`, `dot x 0 = 0`, `dot (−x) y = −dot x y`, `dot x (−y) = −dot x y` | `[]` |

### `DimensionFoundation/ProjectionLaws.lean` (requirements 2 and 3)

| line | declaration | hypotheses | statement | axioms |
|---|---|---|---|---|
| 38 | `proj_of_inL` | `hb`, `InL x` | `projL x = x ∧ projS x = zeroV` | `Quot.sound` |
| 45 | `proj_of_inS` | `hb`, `InS x` | `projL x = zeroV ∧ projS x = x` | `Quot.sound` |
| 51–62 | `projL_of_inL`, `projS_of_inL`, `projL_of_inS`, `projS_of_inS` | as above | the four components separately | `Quot.sound` |
| 67 | `projL_idem` | `hb` | `projL (projL x) = projL x` | `Quot.sound` |
| 70 | `projS_idem` | `hb` | `projS (projS x) = projS x` | `Quot.sound` |
| 73 | `projL_projS` | `hb` | `projL (projS x) = zeroV` | `Quot.sound` |
| 76 | `projS_projL` | `hb` | `projS (projL x) = zeroV` | `Quot.sound` |
| 79 | `projL_addV_projS` | none | `addV (projL x) (projS x) = x` | `Quot.sound` |
| 82 | `projections_idempotent_complementary` | `hb` | conjunction of lines 67–79 | `Quot.sound` |
| 92 | `projL_addV` | none | `projL (addV x y) = addV (projL x) (projL y)` | `Quot.sound` |
| 96 | `projL_smul` | none | `projL (smul a x) = smul a (projL x)` | `Quot.sound` |
| 100 | `projS_addV` | none | `projS (addV x y) = addV (projS x) (projS y)` | `Quot.sound` |
| 107 | `projS_smul` | none | `projS (smul a x) = smul a (projS x)` | `Quot.sound` |
| 116 | `inL_iff_projL_eq` | `hb` | `InL x ↔ projL x = x` | `Quot.sound` |
| 120 | `inS_iff_projS_eq` | `hb` | `InS x ↔ projS x = x` | `Quot.sound` |
| 125 | `range_projL` | `hb` | `(∃ y, x = projL y) ↔ InL x` | `Quot.sound` |
| 130 | `range_projS` | `hb` | `(∃ y, x = projS y) ↔ InS x` | `Quot.sound` |
| 135 | `inS_iff_projL_eq_zero` | `hb` | `InS x ↔ projL x = zeroV` (kernel of `projL`) | `Quot.sound` |
| 144 | `inL_iff_projS_eq_zero` | `hb` | `InL x ↔ projS x = zeroV` (kernel of `projS`) | `Quot.sound` |
| 155 | `dot_inL_inS` | `InL x`, `InS y` | `dot x y = 𝟘` | `[]` |
| 160 | `dot_projL_projS` | `hb` | `dot (projL x) (projS y) = 𝟘` | `[]` |
| 164 | `dot_projS_projL` | `hb` | `dot (projS x) (projL y) = 𝟘` | `[]` |
| 171 | `dot_split` | `hb` | `dot x y = dot (projL x) (projL y) + dot (projS x) (projS y)` | `Quot.sound` |

`Quot.sound` enters only through function extensionality (`funext`), which is how equality of
vectors in `F K b = Child b → K` is proved. This is the same source as in the existing
`decomposition` and `decomposition_unique`. No result uses `propext` or `Classical.choice`.

**Hypotheses.**
- The positivity hypothesis `hb` is used exactly where `projS_inS` or `decomposition_unique` need
  `natCast b ≠ 0`.
- Linearity and `projL_addV_projS` hold for every `b`, including `b = zero`.
- For `b = zero`, `Child zero` is empty, so `F K zero` has exactly one element and every identity
  above holds trivially there. The hypothesis `hb` is kept so that the statements match the existing
  `projS_inS` and `decomposition_unique`, and so that the proofs can use them directly.

## Proof-correspondence addendum (dimension section)

| mathematical statement | Lean |
|---|---|
| \(\langle x+y, z\rangle = \langle x,z\rangle + \langle y,z\rangle\), and similarly in the second argument | `dot_addV_left`, `dot_addV_right`: distribute pointwise, then `sumC_add` |
| \(\langle a x, y\rangle = a\langle x,y\rangle = \langle x, a y\rangle\) | `dot_smul_left`, `dot_smul_right`: pointwise associativity and commutativity, then `sumC_mul_left` |
| symmetry | existing `dot_comm` |
| \(P_L x = x\) for \(x\in L_b\), \(P_S x = 0\) | `proj_of_inL`: \(P_L x + P_S x = x = x + 0\) with \(P_L x\in L\), \(P_S x\in S\), \(0\in S\), so `decomposition_unique` gives \(P_L x = x\) and \(P_S x = 0\) |
| \(P_S x = x\) for \(x\in S_b\), \(P_L x = 0\) | `proj_of_inS`: same argument with \(x = 0 + x\) and \(0 \in L\) (`zeroV_inL`) |
| \(P_L^2 = P_L\), \(P_S^2 = P_S\), \(P_L P_S = P_S P_L = 0\), \(P_L + P_S = \mathrm{id}\) | apply the identity and annihilation actions to \(P_L x \in L\) and \(P_S x \in S\) (`projL_inL`, `projS_inS`), plus `decomposition` |
| linearity of \(P_L\) | \(P_L x = (b^{-1}\textstyle\sum_i x_i)\,u\): `coordSum_addV`, `coordSum_smul`, distributivity, `add_smul`, `mul_smul` |
| linearity of \(P_S = \mathrm{id} - P_L\) | pointwise from the linearity of \(P_L\) |
| \(\operatorname{im} P_L = L_b = \ker P_S\), \(\operatorname{im} P_S = S_b = \ker P_L\) | `range_projL`, `inL_iff_projS_eq_zero`, `range_projS`, `inS_iff_projL_eq_zero` |
| \(L_b \perp S_b\) for `dot` | `dot_inL_inS`: \(\langle c u, s\rangle = c\langle u,s\rangle = c\cdot 0\) by `dot_smul_left` and the existing `dot_u_of_inS` |
| \(\langle x,y\rangle = \langle P_Lx,P_Ly\rangle + \langle P_Sx,P_Sy\rangle\) | `dot_split`: expand bilinearly, then the cross terms vanish |

**Scope.**
- `dot` is proved to be a **symmetric bilinear form** only. Positivity and definiteness are not
  claimed, and `dot` is not called an inner product. The orthogonality results are statements about
  this bilinear form, not about any metric.
- The meaning of algebraic dimension (bases `longitudinal_basis` and `transverse_basis`) is
  unchanged.
- None of the excluded topics (completeness, Markov's principle, LPO, WLPO, connectedness,
  compactness, longitudinal limits, identification of rays with reals) is touched.

## Verification (`./scripts/verify_release.sh`, exit 0; full output in `release/verification_output.txt`)

- **Fingerprint.** New source fingerprint:
  **`7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`**, computed over 75 source
  files at commit `2897ec5`.
- **Build.** `lake build TreeFoundations TreeAnalysis`: `Build completed successfully (67 jobs)`.
- **Source check.** 64 mathematical source files scanned, all reachable from the roots. No
  forbidden token (`simp`, `omega`, `Nat`, `Classical`, `sorry`, …), numeric literal or foreign
  import.
- **Fail-closed kernel audit.** Passed on 64 modules and 3014 constants, with no axiom outside
  `propext` and `Quot.sound`. All **60** required declarations are present.
- **Negative fixtures.** All expectations were met: the user-axiom, `Classical.em`, `sorry`, `Nat`,
  `native_decide`, `opaque`, missing-declaration and empty-environment fixtures each fail; the
  positive control passes; the bad source file fails the source check.
- **`leanchecker`.** Passed with `--fresh` on both libraries and on every module prefix. This is
  the toolchain's bundled checker: it replays the declarations with the same kernel, so it is not a
  fully independent verifier.
- **Matrix.** `FINAL_AXIOM_AND_LAW_MATRIX.md` now has 159 rows (132 proved). Rows 157–159 are the
  new results.

**Note on the scripts.** The scripts had lost their executable bit, so the first attempt to run the
release script stopped with `Permission denied` before any step ran. I restored the bit in git
(`git update-index --chmod=+x`); the contents are unchanged. The fingerprint hashes file contents
only, so this has no effect on it.
