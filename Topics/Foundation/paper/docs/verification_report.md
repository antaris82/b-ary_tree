# Verification and reproducibility — Task--06 manuscript revision

**Source:** Lean 4.28.0, Lake project `TreeFoundations`, no external packages in `lake-manifest.json`. **Frozen source fingerprint:** `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`. The exact uploaded source archive is provided at `evidence/task06_frozen_source.tar.gz`. The archived release report is `evidence/verification_output.txt`; individual declaration printouts are available in `evidence/declaration_signatures.txt`.

## Evidence levels

| Origin | Actually run | Result / status |
|---|---|---|
| Task--06 release transcript included in the archive | `lake build TreeFoundations TreeAnalysis`, source check, fail-closed audit, negative fixtures and `leanchecker` | Reports 67 successful build jobs; 64 reachable mathematical modules; 3,014 audited constants; 60 mandatory declarations present; only `propext` and `Quot.sound` in the reported transitive closures |
| Manuscript-authoring environment (current revision) | Recomputed source fingerprint over the 75 identified files and reran `python3 scripts/source_check.py` in this documentation revision | **PASS:** fingerprint exactly matches `7e126414…b0b7e`; **64/64** mathematical modules reachable, no source-policy violations; **Lean kernel was not rerun here** |
| Separate Claude-attributed reviewer (user-provided report) | Reports its own Lean 4.28.0 build and all release stages, with affected shell script stages invoked manually | Reports matching 67 jobs, 3,014 constants, 64 modules, 60 declarations, 10 fixtures and 9 checker runs; see `reviews/CLAUDE_REVIEW.md`. Those are **independently reported results, not a build executed here** |
| This documentation revision | Compared actual extracted Lean definitions against reviews; rebuilt the LaTeX manuscript | No new Lean proof compiled; PDF built and visually inspected; see `revision_acceptance.md` and `compile.log` |

The release output reports 2,162 axiom-free constants, 245 mentioning `propext` and 817 mentioning `Quot.sound`. **The latter two counts overlap**; they are not disjoint categories. No `Classical.choice`, `sorryAx`, user axioms or compiler-trust axioms were reported in the audited mathematical closure. `Quot.sound` and `propext` are permitted built-in assumptions in the project, not evidence of metamathematical independence.

## Reproducibility defect and workaround

The source archive does not preserve executable bits on `scripts/*.sh`. As a result the unmodified `scripts/verify_release.sh` may fail (exit 126) when it directly invokes `./scripts/negative_fixtures.sh`, even if Lean succeeds. **Do not change the frozen source fingerprint silently.** Instead, after extracting the frozen archive, give its scripts executable permissions (`chmod +x scripts/*.sh`) before running `bash scripts/verify_release.sh` (or invoke the negative-fixtures script with `bash` explicitly in a derivative reproduction tree). A helper is included as `REPRODUCE_RELEASE.sh`; it does not automatically assert that Lean was run for this revision.

## Signature evidence and limits

- `evidence/declaration_signatures.txt` contains **463 entries**; the similarly named `FINAL_AXIOM_AND_LAW_MATRIX.md` contains **159 rows** and is a different document.
- `proof_correspondence.md` has 289 source pointers, including the 37 added Task--06 theorem declarations. The earlier set of 252 pointers addresses unchanged Task--05 mathematical files. Source-declared signatures are distinguished from archival elaborated types.
- `evidence/task05_historical/logs/` holds **21 Task--05 audit batches** for earlier declarations, and `evidence/projS_inS_check.log` holds a separate historical check. These are **not Task--06 elaboration logs**. Do not claim a new batch of 603 Task--06 individual checks.
- The 25 mathematical assertions stated explicitly in the manuscript are crosswalked in `25_MAIN_RESULTS_CROSSWALK.md`. Its entries are editorial correspondence, **not themselves independently elaborated Lean declarations**.
- Formal kernel verification certifies the precise Lean types, not stronger prose claims. Source classes `[TField K]`, `[TOField K]`, `[TwoLetters α]`, positivity, tracking/modulus and choice assumptions are recorded in the manuscript; the new unary `-1` observation is **informal**, not a newly checked Lean declaration.

## Manuscript and primary-source status

- The main paper was revised for the integer normalized-pair type; fraction transport; explicit `TOField` data; unary `-1`; undirected acyclicity; depth quotient; quantifier order; projection scope; arity order transfer; bibliography and namespace corrections.
- `main.tex` and the actually typeset `references.tex` are the authoritative typesetting inputs; `references.bib` is a structured migration copy.
- Author/publisher original sources provide context rather than formal verification. Axler §9A and the Lyons–Peres DOI are checked against original author/publisher pages; references to restricted monographs do not imply full-text line-by-line examination.
- No new Lean kernel build was performed for this manuscript revision. No external peer review is claimed.


## Long-form mathematical exposition: 15 October 2026

The manuscript has been extended with `extended_proof_details.tex`, a mathematical appendix with **89 individually labeled** discussions that correspond one-to-one with the original 89 planned subsections (`scope_89.md`). The principal prior theorem statements and source type claims are unchanged; the paper now includes explicit auxiliary proofs for the formerly abbreviated sections. The revised build was performed locally in this document-authoring environment with `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` and succeeded; the resulting PDF contains **46 pages** and the LaTeX log contains no undefined-reference or overfull-box errors. The generated scope mapping and PDF pages were programmatically cross-checked (89/89 labels, 89/89 valid PDF page locations). These are **LaTeX/exposition checks**, not a new Lean build.

One important fidelity correction made during source comparison: `TreeR.ApproxData` stores **one** rational sequence `q : TreeN → K` and the schedule `M`, not a two-index choice array. The long-form proof now gives the actual rational modulus `max (ν (k+2)) (M (k+2))` and the final convergence threshold. The apartness inverse discussion uses the source's shifted tail sequence and explicit modulus `j + 2k` rather than an ungrounded generic reciprocal argument.

The source archive and its hash are unchanged. Reported third-party Lean verification remains the same. Some routine algebraic rewrites are still abbreviated in the standard manner; no independent external refereeing is claimed.

## Second-review documentary revision (15 October 2026)

Two user-provided reviews were reconciled and the mathematics/documentation repaired; see `SECOND_REVIEW_RESOLUTION.md`. The reviewer reports of a successful independent Task-06 build with Lean 4.28.0 remain **reported** results. In this revision the documentation author actually reran (a) the 75-file SHA-256 fingerprint calculation, obtaining exactly `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`, (b) the static source check, which passed for 64 modules, and (c) `latexmk -pdf` for the amended manuscript. A new Lean kernel or `leanchecker` run was **not** executed here.

The definitive PDF and TeX are in this *second-review-revised* delivery. `compile.log` is the actual compilation transcript for this delivery. `evidence/projS_inS_check.log` is the historical user's independent check (SHA-256 `84e41297347b032be619bc51f01d695499ca1f8bef3b64940c1ebcc3296b9dae`), not a new Task-06 run. The full 25-result start-line correspondence is regenerated; `scope_89.csv` gives the exact 89 Appendix B PDF page references, and `MAIN_TEXT_SUBSECTION_MAP.md` disambiguates 62 main-text subsections from the four Appendix A supplementary subsections. The release ZIP carries its own newly generated SHA-256 artifact manifest.

## Third-review editorial revision (15 October 2026)

The third ChatGPT and Claude reviews were supplied by the user. They report no new erroneous theorem in the 25 named mathematical statements, with remaining minor editorial repairs. This edition implements the editor credit, a literature-grounded distinction between intrinsic word-tree incidence and rationally labelled Stern--Brocot models, an AI/Aristotle acknowledgement in the conclusion, and new-page starts for the contents and all 21 top-level sections/appendices. It does not change the frozen Task--06 Lean source or claim an additional kernel build.

The TeX was recompiled after the editorial changes with `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`. The **current** PDF has **56 pages**, not the 46 pages of the preceding second-review long-form PDF. All 25 main theorem lines and all 89 Appendix-B PDF page references were regenerated against the current build. The supplementary `build_scope.py` requires `main.aux` and must be run **after** a successful LaTeX build. The layout rules are manuscript-only and do not affect the semantic correspondence.

The title-page editor is **Jan Seeck** at `jan.seeck1@gmail.com` (confirmed by the editor on 15 October 2026). No author identity or affiliation has been supplied; the current title block intentionally contains no author or affiliation placeholder, and Jan Seeck is credited as Editor. Any independent external review is deferred until the repository is published and the corresponding documentation is integrated, as requested.
