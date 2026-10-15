module

public import TreeFoundation.ArityEmbeddings
public import TreeNumbers.PathTriples

@[expose] public section

/-!
# The countably branching (omega) tree

Child symbols are the tree-derived unary paths `ChildOmega := TreeN`; vertices are
`WordOmega := Word TreeN`.
-/

open TreeN ListOps Word ArityEmbedding

/-- Vertices of the omega tree. -/
abbrev WordOmega : Type := Word ChildOmega

namespace OmegaTree

/-- Children of an omega vertex ↔ `TreeN`, explicitly (both composites are identities). -/
def childOfIndex (v : WordOmega) (n : TreeN) : ChildOf v := symToChild v n
def indexOfChild {v : WordOmega} (w : ChildOf v) : TreeN := childToSym w

theorem indexOfChild_childOfIndex (v : WordOmega) (n : TreeN) :
    indexOfChild (childOfIndex v n) = n := rfl

theorem childOfIndex_indexOfChild {v : WordOmega} (w : ChildOf v) :
    childOfIndex v (indexOfChild w) = w := symToChild_childToSym w

/-- Distinct child symbols give distinct children. -/
theorem children_distinct (v : WordOmega) {m n : TreeN} (h : m ≠ n) : m :: v ≠ n :: v :=
  fun e => h (child_injective e)

/-- Infinitely many pairwise distinct child symbols: no finite list exhausts them. -/
theorem infinitely_many_children (L : List TreeN) : ∃ n : TreeN, ¬ InL n L :=
  ⟨bound L, fun h => lt_irrefl _ (lt_bound h)⟩

/-- The first symbol of a word (root ↦ `zero`). -/
def headSym : WordOmega → TreeN
  | [] => TreeN.zero
  | m :: _ => m

/-- Every vertex has a child outside any given finite list of vertices. -/
theorem child_outside (v : WordOmega) (L : List WordOmega) :
    ∃ n : TreeN, ¬ InL (n :: v) L := by
  obtain ⟨n, hn⟩ := infinitely_many_children (mapL headSym L)
  exact ⟨n, fun h => hn (inL_mapL headSym h)⟩

/-- Unbounded depth in the omega tree. -/
theorem unbounded_depth (n : TreeN) : ∃ w : WordOmega, depth w = n :=
  Word.unbounded_depth TreeN.zero n

end OmegaTree
end
