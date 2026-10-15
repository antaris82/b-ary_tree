module

public import TreeFoundation.InfiniteRays

@[expose] public section

/-!
# Conventional extended longitudinal labels

`ExtLevel` is an explicitly **conventional** label type with `negInfinity`, `finite n`
(`n : TreeN`) and `posInfinity`.  The actual root keeps graph depth `zero`, and the first
root-child edge has unit length.

Nothing here infers a geometric end at the root, a bi-infinite geodesic, a preferred
geometric midpoint or a boundary hypersurface: the infinite labels are bookkeeping symbols
only.  `posInfinity` is the conventional label attached to rays (their depths are unbounded,
`Ray.depth_unbounded`); `negInfinity` is attached to nothing in this project.
-/

open TreeN Word

/-- Conventional extended longitudinal labels. -/
inductive ExtLevel : Type
  | negInfinity : ExtLevel
  | finite (n : TreeN) : ExtLevel
  | posInfinity : ExtLevel

namespace ExtLevel

/-- Strict order of labels (conventional). -/
inductive Lt : ExtLevel → ExtLevel → Prop
  | neg_finite (n : TreeN) : Lt negInfinity (finite n)
  | neg_pos : Lt negInfinity posInfinity
  | finite_pos (n : TreeN) : Lt (finite n) posInfinity
  | finite_finite {m n : TreeN} : PathLT m n → Lt (finite m) (finite n)

theorem finite_injective {m n : TreeN} (h : finite m = finite n) : m = n := by
  injection h

theorem finite_ne_neg (n : TreeN) : finite n ≠ negInfinity := fun h => nomatch h
theorem finite_ne_pos (n : TreeN) : finite n ≠ posInfinity := fun h => nomatch h
theorem neg_ne_pos : negInfinity ≠ posInfinity := fun h => nomatch h

theorem lt_irrefl (x : ExtLevel) : ¬ Lt x x := by
  intro h
  cases h with
  | finite_finite h' => exact TreeN.lt_irrefl _ h'

/-- The label of a vertex: its graph depth. -/
def vertexLevel {α : Type} (w : Word α) : ExtLevel := finite (depth w)

/-- The conventional label of a ray.  **Definitional sanity check:** this is the constant
label `posInfinity` for every ray (by definition); it carries no information about the ray. -/
def rayLevel {α : Type} (_r : Ray α) : ExtLevel := posInfinity

/-- The actual root keeps graph depth `zero`. -/
theorem root_level (α : Type) : vertexLevel (root : Word α) = finite TreeN.zero := rfl

/-- The first root-child edge has unit length. -/
theorem first_edge_unit {α : Type} (c : α) : pathSum [c] = TreeN.one := rfl

/-- Every vertex label lies strictly below the conventional ray label. -/
theorem vertex_lt_ray {α : Type} (w : Word α) (r : Ray α) : Lt (vertexLevel w) (rayLevel r) :=
  Lt.finite_pos _

/-- Along a ray, vertex labels increase strictly and exceed every finite label. -/
theorem ray_levels_unbounded {α : Type} (r : Ray α) (n : TreeN) :
    ∃ m, Lt (finite n) (vertexLevel (Ray.prefixAt r m)) := by
  obtain ⟨m, hm⟩ := Ray.depth_unbounded r n
  exact ⟨m, Lt.finite_finite hm⟩

end ExtLevel
end
