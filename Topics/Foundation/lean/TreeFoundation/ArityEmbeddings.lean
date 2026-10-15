module

public import PrimitiveTree.RootEdges

@[expose] public section

/-!
# Arity embeddings: letters, words, edges; directed union into the omega tree

* letters:  `Child b ↪ Child (succ b)` (same intrinsic index) and `Child b ↪ TreeN`;
* words and edges are mapped letterwise;
* every omega vertex and every omega edge comes from some finite arity.

The last two statements express the omega tree as the *directed union* of the finite-arity
trees (vertices and edges).  No abstract category-theoretic universal property is
formalized here: this is a constructive union statement, not a proof of a colimit in an
arbitrary category.
-/

open TreeN ListOps Word

namespace ArityEmbedding

variable {α β γ : Type}

/-- Letterwise map of words. -/
def mapWord (f : α → β) (w : Word α) : Word β := mapL f w

/-- Letterwise map of edge records. -/
def mapEdge (f : α → β) (e : Edge α) : Edge β :=
  ⟨mapWord f e.parent, f e.sym, mapWord f e.child, by rw [e.incid]; rfl⟩

theorem mapWord_cons (f : α → β) (c : α) (w : Word α) :
    mapWord f (c :: w) = f c :: mapWord f w := rfl

theorem mapWord_injective {f : α → β} (hf : ∀ a a', f a = f a' → a = a') :
    ∀ {w w' : Word α}, mapWord f w = mapWord f w' → w = w'
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | c :: w, c' :: w', h => by
    injection h with h1 h2
    rw [hf c c' h1, mapWord_injective hf h2]

theorem depth_mapWord (f : α → β) (w : Word α) : depth (mapWord f w) = depth w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    show succ (depth (mapWord f w)) = succ (depth w)
    rw [ih]

theorem pathSum_mapWord (f : α → β) (w : Word α) : pathSum (mapWord f w) = pathSum w := by
  rw [pathSum_eq_depth, pathSum_eq_depth, depth_mapWord]

theorem mapWord_isParent (f : α → β) {p v : Word α} (h : IsParent p v) :
    IsParent (mapWord f p) (mapWord f v) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨f c, by rw [hc]; rfl⟩

theorem mapWord_comp (f : α → β) (g : β → γ) (w : Word α) :
    mapWord g (mapWord f w) = mapWord (fun a => g (f a)) w := by
  induction w with
  | nil => rfl
  | cons c w ih => exact congrArg (List.cons (g (f c))) ih

/-- Root edges are mapped to root edges. -/
theorem mapEdge_rootEdges (f : α → β) (w : Word α) :
    mapL (mapEdge f) (rootEdges w) = rootEdges (mapWord f w) := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    show mapL (mapEdge f) (appL (rootEdges w) [edgeTo w c]) =
      appL (rootEdges (mapWord f w)) [edgeTo (mapWord f w) (f c)]
    rw [mapL_appL, ih]
    rfl

/-! ## Finite arity to its successor and into omega -/

/-- Letter inclusion `Child b ↪ Child (succ b)`. -/
def letterSucc {b : TreeN} : Child b → Child (succ b) := Child.inclSucc

/-- Letter inclusion `Child b ↪ TreeN = ChildOmega`. -/
def letterOmega {b : TreeN} : Child b → TreeN := Child.idx

theorem letterSucc_injective {b : TreeN} (x y : Child b) (h : letterSucc x = letterSucc y) :
    x = y := Child.incl_injective h

theorem letterOmega_injective {b : TreeN} (x y : Child b) (h : letterOmega x = letterOmega y) :
    x = y := Child.ext h

/-- Compatibility: including into `succ b` and then into omega is the inclusion into omega. -/
theorem letterOmega_letterSucc {b : TreeN} (x : Child b) :
    letterOmega (letterSucc x) = letterOmega x := rfl

/-- Word inclusion from arity `b` into arity `succ b`. -/
def wordSucc {b : TreeN} : Word (Child b) → Word (Child (succ b)) := mapWord letterSucc

/-- Word inclusion from arity `b` into the omega tree. -/
def wordOmega {b : TreeN} : Word (Child b) → Word TreeN := mapWord letterOmega

/-- Edge inclusions. -/
def edgeSucc {b : TreeN} : Edge (Child b) → Edge (Child (succ b)) := mapEdge letterSucc
def edgeOmega {b : TreeN} : Edge (Child b) → Edge TreeN := mapEdge letterOmega

theorem wordOmega_wordSucc {b : TreeN} (w : Word (Child b)) :
    wordOmega (wordSucc w) = wordOmega w := by
  unfold wordOmega wordSucc
  rw [mapWord_comp]
  rfl

theorem wordSucc_injective {b : TreeN} {w w' : Word (Child b)} (h : wordSucc w = wordSucc w') :
    w = w' := mapWord_injective letterSucc_injective h

theorem wordOmega_injective {b : TreeN} {w w' : Word (Child b)}
    (h : wordOmega w = wordOmega w') : w = w' := mapWord_injective letterOmega_injective h

/-! ## Directed union: vertices and edges -/

/-- A bound on the symbols of an omega word: the sum of their successors. -/
def bound : List TreeN → TreeN
  | [] => TreeN.zero
  | n :: w => succ n + bound w

theorem lt_bound {n : TreeN} : {w : List TreeN} → InL n w → PathLT n (bound w)
  | [], h => h.elim
  | m :: w, h => by
    cases h with
    | inl e =>
      rw [e]
      exact lt_of_lt_of_le (lt_succ_self m) (le_add (succ m) (bound w))
    | inr h =>
      have h1 := lt_bound h
      exact lt_of_lt_of_le h1 (show PathLE (bound w) (succ m + bound w) by rw [add_comm]; exact le_add _ _)

/-- Lift an omega word whose symbols are all below `b` to the arity-`b` tree. -/
def liftWord (b : TreeN) : (w : List TreeN) → (∀ n, InL n w → PathLT n b) → Word (Child b)
  | [], _ => []
  | n :: w, h => ⟨n, h n (Or.inl rfl)⟩ :: liftWord b w (fun m hm => h m (Or.inr hm))

theorem wordOmega_liftWord (b : TreeN) :
    (w : List TreeN) → (h : ∀ n, InL n w → PathLT n b) → wordOmega (liftWord b w h) = w
  | [], _ => rfl
  | n :: w, _ => congrArg (List.cons n) (wordOmega_liftWord b w _)

/-- **Vertex union**: every omega vertex uses symbols bounded by some `b : TreeN` and is the
image of a vertex of the arity-`b` tree. -/
theorem vertex_union (w : Word TreeN) :
    ∃ b : TreeN, (∀ n, InL n w → PathLT n b) ∧ ∃ w' : Word (Child b), wordOmega w' = w :=
  ⟨bound w, fun _ h => lt_bound h, liftWord _ w (fun _ h => lt_bound h),
    wordOmega_liftWord _ w _⟩

/-- **Edge union**: every omega edge arises from some finite-arity edge. -/
theorem edge_union (e : Edge TreeN) : ∃ b : TreeN, ∃ e' : Edge (Child b), edgeOmega e' = e := by
  have hb : ∀ n, InL n e.child → PathLT n (bound e.child) := fun _ h => lt_bound h
  have hs : InL e.sym e.child := by rw [e.incid]; exact Or.inl rfl
  have hp : ∀ n, InL n e.parent → PathLT n (bound e.child) := by
    intro n h
    apply hb
    rw [e.incid]
    exact Or.inr h
  refine ⟨bound e.child, edgeTo (liftWord _ e.parent hp) ⟨e.sym, hb _ hs⟩, ?_⟩
  apply Edge.ext
  · exact wordOmega_liftWord _ e.parent hp
  · rfl

end ArityEmbedding
end
