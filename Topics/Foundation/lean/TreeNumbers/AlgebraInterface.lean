module

@[expose] public section

/-!
# Algebraic interfaces (typeclass specifications with law fields)

`CSR` and `CRing` are typeclass **specifications**: besides the operations they contain
*law fields* (associativity, commutativity, distributivity, …) stating the algebraic axioms.
They contain no numbers and import no outside arithmetic.  The law fields are **not** kernel
`axiom` declarations; a law field is only ever discharged by a concrete instance, and the
project's only instances are the internally built carriers (`TreeN.instCSR`,
`TreeZ.instCRing`, `TreeQ.instCRing`, `TreeR.instCRing`, …), each of which proves every field
from the concrete definitions.  The generic lemmas below (e.g. `CSR.add_zero`) are derived from
the law fields, so for an *arbitrary* type they hold only under the assumption that it is an
instance; for the project's carriers that assumption is the proved instance.
-/

/-- Commutative semiring specification: operations plus law fields; instances must prove every
law (populated only by the project's constructions). -/
class CSR (α : Type) extends Add α, Mul α where
  zero : α
  one : α
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, zero + a = a
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul : ∀ a : α, one * a = a
  zero_mul : ∀ a : α, zero * a = zero
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c

notation "𝟘" => CSR.zero
notation "𝟙" => CSR.one

namespace CSR

variable {α : Type} [CSR α]

theorem add_zero (a : α) : a + 𝟘 = a := by
  rw [add_comm]
  exact zero_add a

theorem mul_one (a : α) : a * 𝟙 = a := by
  rw [mul_comm]
  exact one_mul a

theorem mul_zero (a : α) : a * 𝟘 = 𝟘 := by
  rw [mul_comm]
  exact zero_mul a

theorem right_distrib (a b c : α) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem add_left_comm (a b c : α) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem add_right_comm (a b c : α) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]

theorem add_add_add_comm (a b c d : α) : a + b + (c + d) = a + c + (b + d) := by
  rw [add_assoc, add_left_comm b c d, ← add_assoc]

theorem mul_left_comm (a b c : α) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

theorem mul_right_comm (a b c : α) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm b c, ← mul_assoc]

theorem mul_mul_mul_comm (a b c d : α) : a * b * (c * d) = a * c * (b * d) := by
  rw [mul_assoc, mul_left_comm b c d, ← mul_assoc]

end CSR

/-- Commutative ring interface. -/
class CRing (α : Type) extends CSR α, Neg α where
  neg_add_cancel : ∀ a : α, -a + a = zero

namespace CRing

open CSR

variable {α : Type} [CRing α]

theorem add_neg_cancel (a : α) : a + -a = 𝟘 := by
  rw [add_comm]
  exact neg_add_cancel a

theorem add_left_cancel {a b c : α} (h : a + b = a + c) : b = c := by
  have h2 : -a + (a + b) = -a + (a + c) := by rw [h]
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at h2
  exact h2

theorem add_right_cancel {a b c : α} (h : a + c = b + c) : a = b := by
  rw [add_comm a c, add_comm b c] at h
  exact add_left_cancel h

theorem neg_eq_of_add_eq_zero {a b : α} (h : a + b = 𝟘) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

theorem neg_neg (a : α) : - -a = a :=
  neg_eq_of_add_eq_zero (neg_add_cancel a)

theorem neg_zero : -(𝟘 : α) = 𝟘 :=
  neg_eq_of_add_eq_zero (zero_add 𝟘)

theorem neg_add (a b : α) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  rw [add_add_add_comm, add_neg_cancel, add_neg_cancel, zero_add]

theorem eq_of_add_neg_eq_zero {a b : α} (h : a + -b = 𝟘) : a = b := by
  have h2 : -a = -b := neg_eq_of_add_eq_zero h
  rw [← neg_neg a, h2, neg_neg]

theorem neg_mul (a b : α) : -a * b = -(a * b) := by
  apply Eq.symm
  apply neg_eq_of_add_eq_zero
  rw [← right_distrib, add_neg_cancel, zero_mul]

theorem mul_neg (a b : α) : a * -b = -(a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_mul_neg (a b : α) : -a * -b = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem add_eq_zero_iff_eq_neg {a b : α} (h : a + b = 𝟘) : a = -b := by
  apply eq_of_add_neg_eq_zero
  rw [neg_neg]
  exact h

end CRing
end
