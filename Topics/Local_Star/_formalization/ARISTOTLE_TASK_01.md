# TASK 01 — Embedded outward local stars

## OBJECTIVE
Construct, in new Lean source under `Topics/Local_Star/lean/LocalStar/`, the outward finite local star centered at an arbitrary vertex of the already established rooted word tree. Prove the exact embedding and overlap properties; no electrical structure yet.

## CONTEXT
For `b : TreeN`, the ambient vertices are `Word (Child b)`. At center `v`, the local vertex set is `{v} ∪ {c::v | c : Child b}` and its primitive edge set contains exactly `Word.edgeTo v c`. A nonroot center's incoming parent edge is not a local-star edge. For adjacent centers `v` and `c::v`, the two local stars share that single vertex and no primitive edge.

## INTERFACES
Inspect exact source and elaborated signatures of `PrimitiveTree.FiniteWords`, `PrimitiveTree.FiniteChild`, `PrimitiveTree.RootEdges`; reuse `Word`, `Word.Edge`, `Word.edgeTo`, `Word.IsParent`, `Child b`. Use only further Foundation imports that prove strictly necessary.

## CONSTRAINTS
No Foundation modifications. All new Lean sources from scratch. Historical `FloatingStar` is a read-only idea source and cannot be imported/copied. No Mathlib, external number carriers, `Classical`, new axioms, `sorry`, `admit`, `noncomputable`, forbidden numerals or tactics, as established by the Foundation source policy. Match Lean 4.28.0. Small independent theorem modules, no deep import chains.

## DELIVERABLES
Define local star vertex/edge carrier and canonical global-address embeddings. Prove injectivity, incidence, child-parent adjacent-star vertex intersection, edge-set disjointness, and uniqueness of the owner of every primitive parent-child edge. Verify global-root and nonroot-center cases and b=1; state b=0 boundary correctly if considered. Update `LocalStar.lean` imports and a compact implementation note.

## ACCEPTANCE
Actual `lake build LocalStar` with the existing Foundation dependency, source restriction check, elaborated signatures and transitive `#print axioms`; relevant small constructive regression examples. Disclose any checks not run. Do **not** yet define Laplacian, currents, energy, DtN, resistance, Gram, simplex, or other algebras.
