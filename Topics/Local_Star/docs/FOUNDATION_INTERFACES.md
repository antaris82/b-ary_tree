# Foundation interface contract (checked against GitHub main, 2026-10-15)

- `PrimitiveTree.FiniteWords`: `Word α := List α`; `Word.root`; `Word.IsParent`; `Word.Edge`, `Word.edgeTo`, `Word.child_injective`, `Word.parent_unique`.
- `PrimitiveTree.FiniteChild`: `Child b` with child index and proof; `Child.decEq`, `Child.enum`, uniqueness of children.
- `PrimitiveTree.RootEdges`: `Word.unitSum`, `Word.pathSum`, `Word.pathSum_eq_depth`, `Word.unitSum_single`, `Word.pathSum_cons`.
- `TreeNumbers.FieldInterface`: `TField`, `TField.natCast`; intrinsic `TreeN`, `TreeQ` from `TreeNumbers.PathRationalField`.
- `TreeAnalysis.OrderedField`: `TOField`; `TreeAnalysis.RationalOrder` proves the rational instances.
- `DimensionFoundation.FiniteChildModule`: `ChildModule.F K b`, `coordSum`, `InL`, `InS`, `dot`.
- `DimensionFoundation.TransverseBasis`: `longitudinal_basis`, `transverse_basis`, `projL`, `projS`.
- `DimensionFoundation.ProjectionLaws`: projection and orthogonality laws.
- `TreeFoundation.InfiniteRays`: `Ray.prefixAt`, `Ray.pathSum_prefixAt`, `Ray.depth_unbounded`.
- `TreeFoundation.ExtendedLevels`: `vertexLevel root = finite zero`, `rayLevel = posInfinity`; negative-infinity is a convention, **not** an identified root node.

Exact elaborated signatures, implicit parameters and axioms must be rechecked against the immutable Foundation SHA at each formal integration. Lean source is more authoritative than this interface map.

Upstream: https://github.com/antaris82/b-ary_tree/tree/main/Topics/Foundation
