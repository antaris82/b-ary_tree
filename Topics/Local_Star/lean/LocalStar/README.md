# Lean source directory

Task 01 is an actual constructive formalization, not a placeholder. Build, from existing Foundation carriers, three tightly scoped results:

1. `Primitive.lean`: globally addressed outward star, vertices/edges, neighboring block overlap and unique edge ownership.
2. `Electrical.lean`: explicitly normalized intrinsic `QStar` conductance, Kirchhoff/Laplacian operator, energy, PSD, constant kernel and grounded positive definiteness.
3. `PortMeasurements.lean`: explicit `+1/-1` port-current solutions, measured resistances `1` (center–child) and `2` (distinct children), and the identity resistance Gram.

Use numerical carriers **only from Foundation**: `TreeN`, `TreeZ`, `QStar = TreeQOmega`. The `b=1` case uses `QStar`, never a field incorrectly instantiated on the one-letter child alphabet. Actual implementation may choose fewer modules if that gives shorter imports.

Do not create empty proof files, import historical `FloatingStar`, recreate arithmetic, or assert desired theorems as abstract law fields. Update the `LocalStar.lean` entry point after new modules are proved.

See the full assignment: [Aristotle Task 01](../../_formalization/ARISTOTLE_TASK_01.md).
