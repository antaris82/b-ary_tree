module

public import PrimitiveTree.FiniteWords

@[expose] public section

/-!
# Unit-edge sums along root paths

The only primitive quantity is one unit edge.  The unit-edge sum of a list of edges is a
left fold whose accumulator lies in `TreeN` and whose increment for every edge is the
one-edge unary path.  It is *not* defined as depth; equality with depth is a theorem.
-/

open TreeN ListOps

namespace Word

variable {α : Type}

/-- Left fold over edges: each edge adds the one-edge unary path to the accumulator. -/
def edgeFold (acc : TreeN) : List (Edge α) → TreeN
  | [] => acc
  | _ :: es => edgeFold (acc + TreeN.one) es

/-- The finite unit-edge sum of a list of edges. -/
def unitSum (es : List (Edge α)) : TreeN := edgeFold TreeN.zero es

/-- The primitive path length of a vertex: the unit-edge sum along its root edges. -/
def pathSum (w : Word α) : TreeN := unitSum (rootEdges w)

theorem edgeFold_acc (acc : TreeN) (es : List (Edge α)) :
    edgeFold acc es = acc + edgeFold TreeN.zero es := by
  induction es generalizing acc with
  | nil => exact (add_zero acc).symm
  | cons e es ih =>
    show edgeFold (acc + TreeN.one) es = acc + edgeFold (TreeN.zero + TreeN.one) es
    rw [ih, ih (TreeN.zero + TreeN.one), add_assoc]
    rfl

theorem edgeFold_appL (acc : TreeN) (es fs : List (Edge α)) :
    edgeFold acc (appL es fs) = edgeFold (edgeFold acc es) fs := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih => exact ih _

/-- The root path has zero primitive length. -/
theorem unitSum_nil : unitSum ([] : List (Edge α)) = TreeN.zero := rfl

/-- Each primitive edge contributes one. -/
theorem unitSum_single (e : Edge α) : unitSum [e] = TreeN.one := rfl

/-- Adjoining an edge increases the sum by exactly the unary successor. -/
theorem unitSum_snoc (es : List (Edge α)) (e : Edge α) :
    unitSum (appL es [e]) = succ (unitSum es) := by
  unfold unitSum
  rw [edgeFold_appL]
  exact add_one _

theorem unitSum_cons (e : Edge α) (es : List (Edge α)) :
    unitSum (e :: es) = succ (unitSum es) := by
  unfold unitSum
  show edgeFold (TreeN.zero + TreeN.one) es = _
  rw [edgeFold_acc]
  rfl

/-- **Unit-edge sum equals depth.** -/
theorem unitSum_rootEdges (w : Word α) : unitSum (rootEdges w) = depth w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    show unitSum (appL (rootEdges w) [edgeTo w c]) = succ (depth w)
    rw [unitSum_snoc, ih]

theorem pathSum_eq_depth (w : Word α) : pathSum w = depth w := unitSum_rootEdges w

theorem pathSum_cons (c : α) (w : Word α) : pathSum (c :: w) = succ (pathSum w) := by
  rw [pathSum_eq_depth, pathSum_eq_depth]
  rfl

theorem pathSum_rep (a : α) (n : TreeN) : pathSum (rep a n) = n := by
  rw [pathSum_eq_depth]
  exact depth_rep a n

end Word

/-! ## The unary tree: its root paths are exactly the unary paths -/

namespace UnaryTree

open Word

/-- In the unary tree the vertices are exactly the unary paths, and the primitive path
length of a vertex is that very path. -/
theorem pathSum_self (p : UnaryPath) : pathSum (α := UnitChild) p = p := by
  rw [pathSum_eq_depth]
  induction p with
  | nil => rfl
  | cons c p ih =>
    show succ (depth p) = c :: p
    rw [ih, UnaryPath.cons_eq_extend]

/-- Each unary-tree vertex has exactly one child. -/
theorem unique_child (v w : Word UnitChild) (h : IsParent v w) : w = UnaryPath.extend v := by
  obtain ⟨c, hc⟩ := h
  rw [hc, UnaryPath.cons_eq_extend]

/-- Every path count is realized by a unique unary-tree vertex: different unary paths
represent different counts. -/
theorem count_realized (n : TreeN) : ∃ v : Word UnitChild, pathSum v = n := ⟨n, pathSum_self n⟩

theorem count_unique {v w : Word UnitChild} (h : pathSum v = pathSum w) : v = w := by
  rw [pathSum_self, pathSum_self] at h
  exact h

end UnaryTree
end
