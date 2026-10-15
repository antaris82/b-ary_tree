# Reconstructing Arithmetic from Finite Words: A Formal Study of Methods and Limits

**Editor:** Jan Seeck — jan.seeck1@gmail.com. **Date:** 15 October 2026.
**Formally checked source:** archivally audited Task-06 Lean 4.28.0; source fingerprint `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`.

This paper is a formal reconstruction of familiar arithmetic, not a new mathematical foundation. Its internally constructed numerical carriers are also intended as reusable, auditable infrastructure for future formalizations that begin from the same word and unit-edge data. This is a design objective, not a claim that arbitrary later numerical computations are already verified. The persistent numerical source is finite words and path counts; recursion, normalization, quotient construction, and operation transport remain distinct methods. The manuscript treats rooted word-tree incidence, unary arithmetic, normalized integers, transported rational fraction structures, finite child-coordinate decomposition, countably supported transverse bases, native ray topology and automorphisms, and constructive Cauchy quotients with explicitly limited completeness and order claims. It carefully distinguishes this intrinsic word-tree construction from rationally labelled Stern--Brocot trees.

## Read the paper

- [`main.pdf`](main.pdf): freshly compiled PDF for the motivation/title revision of 15 October 2026 (GitHub Actions (see workflow history)).
- [`main.tex`](main.tex): current LaTeX manuscript, now including an expanded introduction, a motivation section, and targeted clarifications of rational structure transport and real-number scope, alongside the **89 inline supporting treatments**.
- [`references.tex`](references.tex) is the typeset bibliography; [`references.bib`](references.bib) supplies structured metadata.
- [`scope_89.md`](docs/scope_89.md) and [`scope_89.csv`](docs/scope_89.csv): 89 mathematical topics matched to their real inline LaTeX anchors and PDF pages.
- [`proof_correspondence.md`](docs/proof_correspondence.md): independent Lean theorem correspondence, assumptions and archival verification status.
- [`MAIN_RESULT_PROOF_CHAINS.md`](docs/MAIN_RESULT_PROOF_CHAINS.md): main theorem dependencies; [`INTEGRATION_89.md`](docs/INTEGRATION_89.md): integration methodology and acceptance checks.

## Document structure

Sections 1–18 contain definitions, statements, mathematical proofs and **all 89 previously separate explanations** in context. The unnumbered third-level headings improve scanning without expanding the numbered table of contents. For introduction/conclusion topics without dedicated main-text subsections, details occur in the containing main *section*. The remaining appendices cover focused technical estimates and formal verification/source declarations; they do not duplicate the 89-topic proof catalogue.

## Rebuilding

Run `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`, then `python3 build/rebuild_navigation.py`. The latter requires the generated `main.aux` and updates `scope_89.csv` page numbers. Source-level proof verifications are archival, not freshly rerun by this manuscript editing operation.

## Scope and submission

Additional logical principles (`ChoiceNN`, MP, LPO, WLPO) are never assumed globally. All statements about inversion from mere non-equality, unrestricted modulated or modulus-free completeness, general suprema, boundary-to-reals identifications and positive-dimensional charts remain conditional or open exactly as in the frozen source. Aristotle and other AI assistance are acknowledged; AI review does not replace independent expert peer review. External review may follow the publication of the integrated repository, not precede it.

## 15 October 2026 motivation revision

The title and explanatory framing were revised to distinguish the primitive construction, the resulting tree properties, the internal derivation of arithmetic, transported rational operations, and the limits of constructive completion. No mathematical Lean declarations or theorem proofs were modified. **The LaTeX compilation was successful in GitHub Actions run 38723389434; a fresh Lean build was not performed.** The checked Task-06 fingerprint and historical verification logs continue to refer to the unchanged frozen Lean sources. No discussion-thread material or participant references were introduced into the manuscript.
