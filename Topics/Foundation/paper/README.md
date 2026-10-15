# Foundation — Mathematical Theme Paper

**Title:** *Path Arithmetic, Child-Coordinate Decompositions, and Constructive Cauchy Structures on Rooted Word Trees*  
**Editor:** Jan Seeck — jan.seeck1@gmail.com  
**Status:** Task-06 third-review documentation draft; external review pending until the repository and documentation are integrated.  
**Lean:** 4.28.0, frozen Task-06 fingerprint `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`.

## Read the paper

- [PDF](main.pdf) (56 pages; typeset manuscript)
- [LaTeX source](main.tex)
- [Extended proofs](extended_proof_details.tex)
- [Literature](references.bib) and [typeset references](references.tex)

## Supplements and source

- [Proof correspondence](docs/proof_correspondence.md)
- [25 principal results](docs/25_MAIN_RESULTS_CROSSWALK.md)
- [89-topic scope](docs/scope_89.md) and [main-text map](docs/MAIN_TEXT_SUBSECTION_MAP.md)
- [Verification report](docs/verification_report.md) and [open questions](docs/open_questions.md)
- [Third-review resolution](docs/THIRD_REVIEW_RESOLUTION.md)
- [Source code for the frozen Lean development](../lean/)
- [Reproducibility script](build/REPRODUCE_RELEASE.sh), [archived compile log](build/compile.log), and [review records](reviews/)

The complete Task-06 source archive has been unpacked into `../lean/` without modifying its mathematical source text. Corresponding logs, release reports and historical provenance remain under `evidence/`. Shell entrypoints have executable Git file mode set where appropriate; the archived release scripts themselves retain their original source text. For a complete clean verification run, see [the verification report](docs/verification_report.md).

## Mathematical scope and editorial status

The work studies word-rooted trees and associated path-count arithmetic, normalized integer differences, transported rational fraction operations, finite coordinate-space decompositions, the countably branching algebraic limit, the ray boundary and prefix topology, and constructive Cauchy-ring constructions. Algebraic rank `b−1` is **not** a topological or physical dimension. This is **not** a Stern–Brocot labeling of a pre-existing rational tree: the primitive tree and number structures are constructed in a single dependency-based development.

The manuscript was prepared with AI assistance, including Aristotle for parts of the formalization; this is distinct from independent mathematical peer review. No externally reviewed acceptance is claimed. Repository publication and documentation integration precede requesting an independent expert assessment.

**Note on archive manifests:** `docs/ORIGINAL_DELIVERY_MANIFEST_SHA256.txt` describes the *prior ZIP layout*, not these relocated GitHub paths. The current unpacked GitHub paths are covered by [this repository manifest](docs/REPO_FILE_MANIFEST_SHA256.txt).
