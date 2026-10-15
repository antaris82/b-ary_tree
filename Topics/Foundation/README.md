# Foundation — arithmetic reconstruction from finite words

The Task-06 mathematical theme paper and frozen Lean 4.28.0 source are stored **unpacked** in this directory. The folder name **Foundation** identifies a project topic, not a claim to introduce new foundations of mathematics. The paper emphasizes the shared finite-word and path-count representations of familiar arithmetic while distinguishing the different operations required at each step.

## Start here

- **[Paper overview](paper/README.md)** and **[current PDF](paper/main.pdf)**
- [LaTeX manuscript with integrated mathematical proofs](paper/main.tex), [bibliography](paper/references.bib)
- [Proof correspondence](paper/docs/proof_correspondence.md), [verification report](paper/docs/verification_report.md), [open questions](paper/docs/open_questions.md)
- [89 inline proof locations](paper/docs/scope_89.md) and [historical mathematical outline](docs/PAPER_OUTLINE_AND_SOURCE_MAP.md)
- [Reviews and revisions](paper/reviews/), [validation evidence](paper/evidence/), [reproducibility helpers](paper/build/)
- **[Frozen Task-06 Lean source tree](lean/)** with its original release files and scripts

## Formal reference state

- Lean: **4.28.0**
- Frozen Task-06 source fingerprint: `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`
- [Aristotle formalization project](https://aristotle.harmonic.fun/projects/db97653b-b468-41a1-97fd-7eb835c2087d)
- Paper editor: **Jan Seeck** · jan.seeck1@gmail.com

## Mathematical scope and limitations

The development begins with rooted word trees and unit-edge path sums, then constructs natural-count arithmetic, normalized integer differences, rational fractions with **operations transported** from the previously constructed fraction structure, and separately the finite child-coordinate decomposition, countably branching algebraic limit, native ray boundary/prefix topology, and constructive Cauchy structures.

The algebraic transverse rank `b−1` is not a topological or physical dimension. This is **not** a Stern–Brocot address labeling of an already given rational tree. Nor are the native ray boundary and numerical completion canonically identified in the proved scope.

The manuscript was prepared with AI assistance, including Aristotle-assisted formalization. Internal AI reviews are not external peer review. An external expert assessment will be requested **after** the repository and documentation are published and integrated.

This folder includes archived audit logs and reviews as evidence, not as replacements for the Lean code and its elaborated theorem signatures. Check the [verification report](paper/docs/verification_report.md) for the precise distinction between reproduced checks and reported kernel runs.
