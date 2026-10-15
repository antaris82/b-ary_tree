module

public import PrimitiveTree.FiniteChild

@[expose] public section

/-!
# Full rooted trees over a child alphabet

For any child alphabet `α` the vertices are the finite words `List α`; the root is the empty
word.  A word is stored with its **most recent step at the head**: the edge from a parent
`w` to its child along symbol `c` is `w ⟶ c :: w`.  (So the list `c₀ :: c₁ :: … ` is read
from the deepest step back to the root.)  There is no primitive metric.

* finite arity `b`:  `Word (Child b)`;
* countable arity:   `Word TreeN` (`ChildOmega := TreeN`).
-/

open TreeN ListOps

/-- Vertices of the full tree over alphabet `α`. -/
abbrev Word (α : Type) : Type := List α

namespace Word

variable {α : Type}

/-- The root vertex. -/
def root : Word α := []

/-- Depth of a vertex, by structural recursion, with values in `TreeN`. -/
def depth : Word α → TreeN
  | [] => TreeN.zero
  | _ :: w => succ (depth w)

/-- Parent–child incidence: `v` is obtained from `p` by one child step. -/
def IsParent (p v : Word α) : Prop := ∃ c : α, v = c :: p

/-- An edge record: explicit endpoints, the child symbol, and the incidence proof. -/
structure Edge (α : Type) where
  parent : Word α
  sym : α
  child : Word α
  incid : child = sym :: parent

theorem Edge.ext {e f : Edge α} (h1 : e.parent = f.parent) (h2 : e.sym = f.sym) : e = f := by
  cases e with
  | mk p s c i =>
    cases f with
    | mk p' s' c' i' =>
      cases h1
      cases h2
      cases i
      cases i'
      rfl

/-- Two edges with the same child endpoint coincide. -/
theorem Edge.eq_of_child {e f : Edge α} (h : e.child = f.child) : e = f := by
  have h' : e.sym :: e.parent = f.sym :: f.parent := by rw [← e.incid, ← f.incid, h]
  injection h' with h1 h2
  exact Edge.ext h2 h1

theorem Edge.isParent (e : Edge α) : IsParent e.parent e.child := ⟨e.sym, e.incid⟩

/-- The edge from `w` along the child symbol `c`. -/
def edgeTo (w : Word α) (c : α) : Edge α := ⟨w, c, c :: w, rfl⟩

/-- The root has no parent. -/
theorem root_no_parent (p : Word α) : ¬ IsParent p root := fun ⟨_, h⟩ => nomatch h

/-- Every nonroot vertex has a parent. -/
theorem nonroot_has_parent (c : α) (w : Word α) : IsParent w (c :: w) := ⟨c, rfl⟩

/-- Unique parent of a nonroot vertex. -/
theorem parent_unique {p q v : Word α} (hp : IsParent p v) (hq : IsParent q v) : p = q := by
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  rw [hc] at hd
  injection hd

/-- Exactly the prescribed child family: the children of `v` are the words `c :: v`. -/
theorem children_eq (v w : Word α) : IsParent v w ↔ ∃ c : α, w = c :: v := Iff.rfl

/-- Distinct child symbols give distinct children. -/
theorem child_injective {v : Word α} {c d : α} (h : c :: v = d :: v) : c = d := by
  injection h

/-- The child symbol of a child of `v`. -/
def childSym {v : Word α} : (w : Word α) → IsParent v w → α
  | [], h => False.elim (root_no_parent v h)
  | c :: _, _ => c

theorem childSym_spec {v : Word α} (w : Word α) (h : IsParent v w) : w = childSym w h :: v := by
  cases w with
  | nil => exact (root_no_parent v h).elim
  | cons c w' =>
    obtain ⟨d, hd⟩ := h
    injection hd with h1 h2
    show c :: w' = c :: v
    rw [h2]

/-- The children of a vertex, as a type. -/
structure ChildOf (v : Word α) where
  word : Word α
  isChild : IsParent v word

/-- Explicit bijection between the alphabet and the children of every vertex. -/
def symToChild (v : Word α) (c : α) : ChildOf v := ⟨c :: v, ⟨c, rfl⟩⟩

def childToSym {v : Word α} (w : ChildOf v) : α := childSym w.word w.isChild

theorem childToSym_symToChild (v : Word α) (c : α) : childToSym (symToChild v c) = c := rfl

theorem ChildOf.ext {v : Word α} {x y : ChildOf v} (h : x.word = y.word) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem symToChild_childToSym {v : Word α} (w : ChildOf v) : symToChild v (childToSym w) = w :=
  ChildOf.ext (childSym_spec w.word w.isChild).symm

/-! ## Directed root paths -/

/-- Directed edge paths, built by appending one edge at the far end. -/
inductive DPath : Word α → Word α → List (Edge α) → Prop
  | nil (u : Word α) : DPath u u []
  | snoc {u : Word α} {es : List (Edge α)} (e : Edge α) :
      DPath u e.parent es → DPath u e.child (appL es [e])

/-- The list of actual consecutive parent–child edges from the root to `w`, in root-first
order. -/
def rootEdges : Word α → List (Edge α)
  | [] => []
  | c :: w => appL (rootEdges w) [edgeTo w c]

theorem rootEdges_dpath : (w : Word α) → DPath root w (rootEdges w)
  | [] => DPath.nil _
  | c :: w => DPath.snoc (edgeTo w c) (rootEdges_dpath w)

/-- Uniqueness of the directed root path to each vertex. -/
theorem dpath_root_unique {w : Word α} {es : List (Edge α)} (h : DPath root w es) :
    es = rootEdges w := by
  have key : ∀ (u v : Word α) (es : List (Edge α)), DPath u v es → u = root → es = rootEdges v := by
    intro u v es h
    induction h with
    | nil => intro hu; rw [hu]; rfl
    | snoc e _ ih =>
      intro hu
      cases e with
      | mk p s c i =>
        cases i
        rw [ih hu]
        rfl
  exact key _ _ _ h rfl

/-! ## Undirected walks: connectedness and absence of cycles -/

/-- Undirected walks, recording the traversed edge records. -/
inductive Walk : Word α → Word α → List (Edge α) → Prop
  | nil (u : Word α) : Walk u u []
  | up {w : Word α} {es : List (Edge α)} (e : Edge α) :
      Walk e.child w es → Walk e.parent w (e :: es)
  | down {w : Word α} {es : List (Edge α)} (e : Edge α) :
      Walk e.parent w es → Walk e.child w (e :: es)

theorem Walk.append {u v w : Word α} {es fs : List (Edge α)} (h1 : Walk u v es)
    (h2 : Walk v w fs) : Walk u w (appL es fs) := by
  induction h1 with
  | nil => exact h2
  | up e _ ih => exact Walk.up e (ih h2)
  | down e _ ih => exact Walk.down e (ih h2)

theorem walk_to_root : (w : Word α) → ∃ es, Walk w root es
  | [] => ⟨[], Walk.nil _⟩
  | c :: w =>
    match walk_to_root w with
    | ⟨es, h⟩ => ⟨edgeTo w c :: es, Walk.down (edgeTo w c) h⟩

theorem walk_from_root : (w : Word α) → ∃ es, Walk root w es
  | [] => ⟨[], Walk.nil _⟩
  | c :: w =>
    match walk_from_root w with
    | ⟨es, h⟩ => ⟨appL es [edgeTo w c], Walk.append h (Walk.up (edgeTo w c) (Walk.nil _))⟩

/-- Connectedness. -/
theorem connected (u v : Word α) : ∃ es, Walk u v es := by
  obtain ⟨es, h1⟩ := walk_to_root u
  obtain ⟨fs, h2⟩ := walk_from_root v
  exact ⟨appL es fs, Walk.append h1 h2⟩

/-- `v` lies in the subtree below `x`. -/
def IsDesc (x v : Word α) : Prop := ∃ l : List α, v = appL l x

theorem isDesc_refl (x : Word α) : IsDesc x x := ⟨[], rfl⟩

theorem isDesc_cons {x v : Word α} (c : α) (h : IsDesc x v) : IsDesc x (c :: v) := by
  obtain ⟨l, hl⟩ := h
  exact ⟨c :: l, by rw [hl]; rfl⟩

/-- A parent is never below its own child. -/
theorem not_isDesc_parent (e : Edge α) : ¬ IsDesc e.child e.parent := by
  intro ⟨l, hl⟩
  rw [e.incid] at hl
  exact appL_cons_ne l e.sym e.parent hl.symm

/-- Leaving the subtree below `e.child` forces traversing `e`. -/
theorem bridge_out (e : Edge α) {v w : Word α} {es : List (Edge α)} (h : Walk v w es) :
    IsDesc e.child v → IsDesc e.child w ∨ InL e es := by
  induction h with
  | nil u => exact fun hv => Or.inl hv
  | up e' _ ih =>
    intro hv
    have hc : IsDesc e.child e'.child := by
      rw [e'.incid]
      exact isDesc_cons _ hv
    cases ih hc with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (Or.inr h)
  | down e' _ ih =>
    intro hv
    obtain ⟨l, hl⟩ := hv
    cases l with
    | nil => exact Or.inr (Or.inl (Edge.eq_of_child hl).symm)
    | cons a l =>
      have hp : IsDesc e.child e'.parent := by
        rw [e'.incid] at hl
        injection hl with _ h2
        exact ⟨l, h2⟩
      cases ih hp with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inr h)

/-- Entering the subtree below `e.child` forces traversing `e`. -/
theorem bridge_in (e : Edge α) {v w : Word α} {es : List (Edge α)} (h : Walk v w es) :
    IsDesc e.child w → IsDesc e.child v ∨ InL e es := by
  induction h with
  | nil u => exact fun hv => Or.inl hv
  | up e' _ ih =>
    intro hw
    cases ih hw with
    | inr h => exact Or.inr (Or.inr h)
    | inl hc =>
      obtain ⟨l, hl⟩ := hc
      cases l with
      | nil => exact Or.inr (Or.inl (Edge.eq_of_child hl).symm)
      | cons a l =>
        rw [e'.incid] at hl
        injection hl with _ h2
        exact Or.inl ⟨l, h2⟩
  | down e' _ ih =>
    intro hw
    cases ih hw with
    | inr h => exact Or.inr (Or.inr h)
    | inl hc =>
      rw [e'.incid]
      exact Or.inl (isDesc_cons _ hc)

/-- **Absence of undirected cycles**: there is no closed walk of positive length whose
traversed edges are pairwise distinct. -/
theorem no_cycle {u : Word α} {e : Edge α} {es : List (Edge α)} (h : Walk u u (e :: es))
    (hnd : NodupL (e :: es)) : False := by
  cases h with
  | up _ rest =>
    cases bridge_out e rest (isDesc_refl _) with
    | inl h => exact not_isDesc_parent e h
    | inr h => exact hnd.1 h
  | down _ rest =>
    cases bridge_in e rest (isDesc_refl _) with
    | inl h => exact not_isDesc_parent e h
    | inr h => exact hnd.1 h

/-! ## Unbounded depth -/

/-- Repeated-word constructor: the word `a^n`, with exponent a unary path. -/
def rep (a : α) : TreeN → Word α
  | [] => []
  | _ :: n => a :: rep a n

theorem depth_rep (a : α) (n : TreeN) : depth (rep a n) = n := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    show succ (depth (rep a n)) = c :: n
    rw [ih, UnaryPath.cons_eq_extend]

/-- Unbounded finite depth for any inhabited alphabet. -/
theorem unbounded_depth (a : α) (n : TreeN) : ∃ w : Word α, depth w = n :=
  ⟨rep a n, depth_rep a n⟩

end Word
end
