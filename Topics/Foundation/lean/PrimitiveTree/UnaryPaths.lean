module

public import PrimitiveTree.UnitChild

@[expose] public section

/-!
# Unary root paths

A finite unary root path is literally a finite list of successive unit child steps.
No number type is involved: the list constructors *are* the root and the one-step
extension of the unary tree.
-/

/-- A finite unary root path: a finite list of unit child steps. -/
abbrev UnaryPath : Type := List UnitChild

namespace UnaryPath

/-- The empty (root) path. -/
def zeroPath : UnaryPath := []

/-- The one-edge path. -/
def onePath : UnaryPath := [UnitChild.only]

/-- One-step extension of a path by one more unit child step. -/
def extend (p : UnaryPath) : UnaryPath := UnitChild.only :: p

/-- Concatenation of unary paths, by structural recursion on the first path. -/
def concat : UnaryPath → UnaryPath → UnaryPath
  | [], q => q
  | c :: p, q => c :: concat p q

/-- Iteration of an endofunction along a unary path (structural recursion). -/
def iterate {α : Type} (f : α → α) : UnaryPath → α → α
  | [], a => a
  | _ :: p, a => f (iterate f p a)

/-- Every list cell of a unary path is an `extend` step. -/
theorem cons_eq_extend (c : UnitChild) (p : UnaryPath) : c :: p = extend p := by
  cases c
  rfl

/-- Root and extensions are distinct. -/
theorem extend_ne_zero (p : UnaryPath) : extend p ≠ zeroPath := fun h => nomatch h

/-- Extension is injective (uniqueness of the parent path). -/
theorem extend_injective {p q : UnaryPath} (h : extend p = extend q) : p = q := by
  injection h

/-- Every unary path is either the root or the extension of a unique path. -/
theorem zero_or_extend (p : UnaryPath) : p = zeroPath ∨ ∃ q, p = extend q := by
  cases p with
  | nil => exact Or.inl rfl
  | cons c q => exact Or.inr ⟨q, cons_eq_extend c q⟩

/-- Every unary path is obtained from the root by iterating extension along itself. -/
theorem iterate_extend_zero (p : UnaryPath) : iterate extend p zeroPath = p := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    show extend (iterate extend p zeroPath) = c :: p
    rw [ih, cons_eq_extend]

/-- A path is never equal to a proper extension of itself. -/
theorem ne_cons_self (c : UnitChild) (p : UnaryPath) : c :: p ≠ p := by
  induction p generalizing c with
  | nil => exact fun h => nomatch h
  | cons d p ih =>
    intro h
    injection h with _ h2
    exact ih d h2

end UnaryPath
end
