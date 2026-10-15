module

public import TreeNumbers.PathRationalField

@[expose] public section

/-!
# Independence of the finite arity

For any two alphabets with two distinct letters (finite arities `b, b' ≥ 2`, or omega), the
triple-path rational fields are isomorphic.  The comparison map sends the class of a
configuration over `α` to the class of the witness configuration over `β` with the same
numerator/denominator data.  Only internally constructed fields are involved.

Note: a triple class represents a numerical value; the addresses (vertices) themselves carry
no numerical value — nothing assigns a rational number to a vertex.
-/

open TreeZ CSR CRing TriplePath

/-- Field isomorphism between two field-interface instances. -/
structure FieldIso (K L : Type) [TField K] [TField L] where
  toFun : K → L
  invFun : L → K
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_zero : toFun 𝟘 = 𝟘
  map_one : toFun 𝟙 = 𝟙
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  map_neg : ∀ x, toFun (-x) = -toFun x
  map_inv : ∀ x, toFun (TField.inv x) = TField.inv (toFun x)

namespace TreeQ

/-- The comparison map between triple-path rationals over two alphabets. -/
def transfer (α β : Type) [TwoLetters β] : TreeQ α → TreeQ β :=
  Quot.lift (fun t => ofF (toFrac t)) (fun _ _ h => ofF_sound h)

variable {α β : Type} [TwoLetters α] [TwoLetters β]

theorem transfer_ofF (f : Frac) : transfer α β (ofF f) = ofF f := by
  show ofF (toFrac (ofFrac (α := α) f)) = ofF f
  rw [toFrac_ofFrac]

theorem transfer_add (x y : TreeQ α) : transfer α β (x + y) = transfer α β x + transfer α β y := by
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  rw [add_ofF, transfer_ofF, transfer_ofF, transfer_ofF, add_ofF]

theorem transfer_mul (x y : TreeQ α) : transfer α β (x * y) = transfer α β x * transfer α β y := by
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  rw [mul_ofF, transfer_ofF, transfer_ofF, transfer_ofF, mul_ofF]

theorem transfer_neg (x : TreeQ α) : transfer α β (-x) = -transfer α β x := by
  induction x using ind_ofF with | h f => ?_
  rw [neg_ofF, transfer_ofF, transfer_ofF, neg_ofF]

theorem transfer_inv (x : TreeQ α) :
    transfer α β (TField.inv x) = TField.inv (transfer α β x) := by
  induction x using ind_ofF with | h f => ?_
  show transfer α β (invQ (ofF f)) = invQ (transfer α β (ofF f))
  rw [inv_ofF, transfer_ofF, transfer_ofF, inv_ofF]

theorem transfer_zero : transfer α β 𝟘 = 𝟘 := transfer_ofF Frac.zero

theorem transfer_one : transfer α β 𝟙 = 𝟙 := transfer_ofF Frac.one

theorem transfer_transfer (x : TreeQ α) : transfer β α (transfer α β x) = x := by
  induction x using ind_ofF with | h f => ?_
  rw [transfer_ofF, transfer_ofF]

/-- **Arity independence**: the triple-path rational fields over any two alphabets with two
distinct letters are isomorphic. -/
def arityIso (α β : Type) [TwoLetters α] [TwoLetters β] : FieldIso (TreeQ α) (TreeQ β) where
  toFun := transfer α β
  invFun := transfer β α
  left_inv := transfer_transfer
  right_inv := transfer_transfer
  map_zero := transfer_zero
  map_one := transfer_one
  map_add := transfer_add
  map_mul := transfer_mul
  map_neg := transfer_neg
  map_inv := transfer_inv

end TreeQ

/-- Isomorphism between two finite arities with at least two children. -/
def finiteArityIso (b b' : TreeN) [AtLeastTwo b] [AtLeastTwo b'] :
    FieldIso (TreeQb b) (TreeQb b') :=
  TreeQ.arityIso (Child b) (Child b')

/-- Isomorphism between a finite arity with at least two children and omega branching. -/
def finiteOmegaIso (b : TreeN) [AtLeastTwo b] : FieldIso (TreeQb b) TreeQOmega :=
  TreeQ.arityIso (Child b) ChildOmega

end
