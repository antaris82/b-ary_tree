**Historical review acceptance record. Current mathematical arguments have since been integrated into the main text; see `INTEGRATION_89.md`.**

# Final review-resolution and acceptance report — Task--06

The source revision remains fixed to fingerprint `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`. Only **documentation** has been edited; no new Lean declaration is asserted. Original reviewers and the manuscript-authoring environment are distinguished in `verification_report.md`.

| ID | Resolution | Documentary evidence |
|---|---|---|
| M01 | **Resolved** | §5: normalized-pair carrier; TreeZ.mkZ_sound/exact |
| M02 | **Resolved** | Abstract, §6 and §7: Φ/Ψ transport equations and structural interpretation |
| M03 | **Resolved** | §12: explicit TOField.decNonneg, Nonneg, archBound, arch_spec |
| M04 | **Resolved within stated scope** | §6: unary 0 and −1 omitted (−1 only informally proved); no exact-image theorem |
| M05 | **Resolved** | §2: undirected cut-edge acyclicity proof |
| M06 | **Resolved** | §4: graft, repeatW, comparison via path sums |
| M07 | **Resolved** | §12: one representative for every precision; transfer argument |
| M08 | **Resolved** | §7: order preservation via TreeQ.transfer_le and inverse |
| M09 | **Resolved** | §8: decomposition identity without hb vs direct-sum conclusions with hb |
| M10 | **Resolved** | §10: openness of complement without DecidableEq |
| M11 | **Resolved in prose** | §2: arity b≤c as finite iteration, not independent Lean theorem |
| M12 | **Resolved** | §2: undirected graph theorem no_cycle |
| M13 | **Resolved** | Appendix A: congruence calculation explicitly expanded |
| M14 | **Resolved** | LaTeX syntax, typeset references.tex DOI and Gilbert diacritic |
| M15 | **Resolved** | RClose / Ray.compact_cyl_of_sub / TreeR.apart_of_mul_eq_one namespace clarification |
| M16 | **Resolved for delivered package** | Task06 source archive, release logs and Task05 historical logs included; reproduction helper documents chmod |
| M17 | **Resolved** | verification_report: three distinct evidence levels, 463 vs 159 |
| M18 | **Partially resolved; transparent limit** | Expanded long-form Appendix B treats all 89 plan topics individually, with nontrivial auxiliary derivations. Routine algebraic rewrites remain abbreviated; no new Lean evidence supplied |
| M19 | **Resolved** | Single open_questions.md register with disjoint statuses and task06 hash |
| M20 | **Resolved** | §2 and §10: correct strength, without imported Cantor/Baire identities |

## Evidence and quality gates

1. **Source integrity:** independently recomputed Task--06 hash over 75 files using the archive's documented `sha256sum` procedure; exact match. Independently reran `python3 scripts/source_check.py`: all 64 mathematical files reachable, no violations.
2. **Kernel:** the archived release transcript records a passing Task--06 kernel audit and permitted axiom closure; the Claude-attributed independent reproduction is *reported*, not executed by the documentation author in this turn. No new formal theorem was introduced.
3. **Manuscript:** `main.tex` is the mathematical narrative, `references.tex` the actually typeset bibliography; supporting correspondence and historical logs are in this package.
4. **Remaining presentation limits:** M18 is resolved as a **topic-coverage and nontrivial-proof-exposition requirement**: Appendix B explicitly treats all 89 original topics. This does not mean 89 separately kernel-checked theorems or a line-by-line recitation of every routine Lean rewrite. A future referee may request additional details. The optional exact unary-image statement still requires its own Lean formalization if presented as kernel-proved.
5. **Do not infer:** classic complete ordered-field status for `TreeR`, a topological dimension `b−1`, a canonical boundary-to-Cauchy homeomorphism, or independence of MP/LPO from the established conditional equivalences.

## Additional source evidence

- The embedded `evidence/task06_frozen_source.tar.gz` is the unmodified Task--06 code, including release scripts. The reproduced SHA-256 source fingerprint is stated above; the review's shell permission workaround is documented separately and does not change this frozen archive.
- `evidence/task05_historical/logs/` and `evidence/projS_inS_check.log` close prior *supplementary* provenance links but must not be presented as a new Task--06 kernel run.

## Second-review resolution (15 October 2026)

See `SECOND_REVIEW_RESOLUTION.md` for the six mathematical precision fixes and nine documentary fixes. The preceding M01–M20 table records the **first** review cycle and is not itself evidence for a new Lean run.

## Third-review editorial addendum (15 October 2026)

- R1: The main-body subsection map explicitly records plans 6.7, 8.9, 13.3, 14.5 and 16.7 as shared thematic coverage, without inventing new theorem anchors; introduction/conclusion plan topics remain section-level.
- R2: `scope_89.csv` and `.md` classify Plan 13.4 as **Proved equivalence; principle not asserted**.
- R3: The fifth main proof chain no longer treats integer order as necessary for abstract field laws.
- R4: `README.md` states that `build_scope.py` requires `main.aux` generated by a prior LaTeX run.
- R5: Jan Seeck is named as **editor** in the PDF. Authorship/affiliation remain explicitly unprovided, and must not be inferred from the editor name.
- The requested intrinsic word-tree versus Stern--Brocot and general address-labelled graph comparison is mathematical context, with original-source references and no stronger Lean claim.
- Main sections, appendices, references and table of contents begin on new pages. Current PDF: **56 pages** (previous long-form second-review version: 46 pages).
- The conclusion acknowledges AI assistance, including Aristotle.
- External opinion deferred until repository publication and documentation integration.
