# Handoff for the mathematical-paper project chat

## Goal
Prepare a **standard mathematical journal paper** representing the entire frozen Task-5 mathematical content, not just path arithmetic or the Cauchy quotient. **Do not draft the paper until explicitly requested.** The initial output is the verified content plan in `PAPER_OUTLINE_AND_SOURCE_MAP.md`.

## Required source reading
Read the complete `lean/PrimitiveTree`, `lean/TreeFoundation`, `lean/TreeNumbers`, `lean/DimensionFoundation`, `lean/BoundaryTopology`, and mathematical `lean/TreeAnalysis` modules, plus the property/open-question ledgers and release audit. The published formal source and the human-readable proof text are separate layers. Exact Lean line references in the outline are *navigation targets*, not evidence that all code-dependent statements have been independently kernel-checked.

## Narrative (pure mathematics)
Definitions of words and trees; finite path-count arithmetic; quotient and fraction constructions; finite algebraic child-coordinate modules and bases; countable-arity algebraic limit; infinite rays and cylinder topology; constructive Cauchy quotient and its proven limitations; structural comparisons and open questions. Exposition must be discursive and mathematical, with complete proof arguments and exact hypotheses. Lean statements are cited in a technical supplement, never described in place of mathematics.

## Theorem inventory acceptance
For **every** main theorem in the outline, transcribe its exact fully elaborated Lean type, identify all typeclasses, distinguish definitions from theorems, audit axioms and source provenance, and then provide a paper version no stronger than its Lean type. If any item cannot be matched, mark it `UNVERIFIED / NOT FORMALIZED` rather than inventing a proof. Never label a conditional theorem unconditional.

## Literature policy
Use and inspect original author editions or publishers' original texts: Serre (trees), Lyons–Peres (network/tree boundaries), Kechris (Cantor/Baire spaces), Axler (finite dimensional algebra), Bass–Otero-Espinar–Rockmore–Tresser (rooted-tree automorphisms), Bishop–Bridges and Bridges–Richman (constructive analysis), Lubarsky (Cauchy completeness). The outline has links. Page references must be checked in cited editions.

## Do not conflate
Do not identify native boundary with the numerical completion. Do not call the rank `b−1` the topological dimension. Do not present `R(K)` as a classical complete ordered field. Do not promise arbitrary-choice-free modulus selection. Do not assume root `−∞` conventional marking was implemented: actual `vertexLevel root = finite 0`.

## Publishing outputs, when requested later
A complete `main.tex` with all mathematical sections; bibliography; mathematical theorem correspondence; verification report; exact scope/open-problem register; reproducible build evidence. Consider separate papers only after covering all existing mathematics in a *complete* scope map.

## Submission criterion
Review the full mathematical table of contents against all mathematical modules. Each major result must appear in the paper or be omitted for a stated reason. The previous 12-page arithmetic-focused draft was incomplete as a complete project paper; do not make the same omission again.
