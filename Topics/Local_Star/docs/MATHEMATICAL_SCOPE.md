# Exact mathematical scope

## Starting objects
Use Foundation `Word (Child b)`, `Word.edgeTo`, `Word.IsParent`, `TreeN`, `TreeQ`, `TField`, `TOField`, `ChildModule.F` and proved child-coordinate projections. Rooted tree edges, global addresses and path sums are **not** redeveloped. For center `v`, the outward star has vertices `{v} ∪ {c::v}` and edges `{(v,c::v)}`. A nonroot center's incoming edge is part of the ambient tree, not of its outward star.

## Work to be established
1. Canonical embedding, neighbor overlap exactly at their shared vertex, edge disjointness, unique outgoing-star edge ownership.
2. Explicit unit conductance, edge current, Kirchhoff balance and energy, then ground-root/unit-injection resistance measurement.
3. Exact finite Laplacian and DtN reductions for every nonempty subset of star vertices; retained-center and eliminated-center normal forms.
4. For arity four: five vertices, four primitive edges, 31 nonempty terminal choices and 27 distinct zero-extended response matrices.
5. Positive-semidefinite DtN forms; positive-definite grounded relative forms; resistance Gram identity and distinct coordinate Gram.
6. Resistance-derived simplices, their faces and dimensions; conditional arity-four criteria without a global-dimension claim.
7. Assembly of overlapping star Laplacians using shared *addresses*, compatible interface reduction and preservation of two-terminal resistances.
8. Distinguish native rays, vertex resistance metric, shorted-depth boundary and any newly defined energy-form limit.

## Boundaries and countercontrols
The finite DtN terminal subset is not the tree's infinite end boundary. A graph's simple path metric on its vertices is not the Euclidean distance of the Gram realization; resistance corresponds to **squared Euclidean distance** in that realization. Effective edges created by eliminating centers are not primitive tree edges. A local transverse rank `b-1` does not imply a global manifold of that dimension.

## Formal status
Every item after the existing Foundation interfaces is an unproved new-topic objective until a real Lean kernel build validates its exact statement.
