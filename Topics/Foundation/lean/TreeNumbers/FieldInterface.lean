module

public import TreeNumbers.PathOrder

@[expose] public section

/-!
# Field interface (typeclass specification with law fields)

A typeclass specification of a field of characteristic zero: operations plus law fields
(`zero_ne_one`, `mul_inv_cancel`, `inv_zero`, `charZero`, and the `CRing` laws).  The law fields
are not kernel axioms; they are proved by each concrete instance.  In this project the instances
are the triple-path rational fields `TreeQ α` (`TreeQ.instTField`) and the auxiliary fraction
quotient `FracQ` (`FracQ.instTField`); generic lemmas below hold for an arbitrary type only under
the assumption that it is an instance.  The image of path counts is given by an explicit
structural recursion `natCastWith` on unary paths.
-/

/-- Image of a unary path count under `zero`, `one`, `add`: structural recursion. -/
def natCastWith {K : Type} (z o : K) (add : K → K → K) : TreeN → K
  | [] => z
  | _ :: n => add o (natCastWith z o add n)

/-- Field specification with characteristic zero: law fields to be proved by every instance
(populated only by the project's constructions). -/
class TField (K : Type) extends CRing K where
  inv : K → K
  zero_ne_one : (zero : K) ≠ one
  mul_inv_cancel : ∀ a : K, a ≠ zero → a * inv a = one
  inv_zero : inv zero = zero
  charZero : ∀ n : TreeN, natCastWith zero one (fun x y => x + y) (TreeN.succ n) ≠ zero

namespace TField

open CSR CRing

variable {K : Type} [TField K]

/-- The image of a unary path count in the field. -/
def natCast (n : TreeN) : K := natCastWith 𝟘 𝟙 (fun x y => x + y) n

theorem natCast_nil : natCast (K := K) [] = 𝟘 := rfl

theorem natCast_cons (c : UnitChild) (n : TreeN) :
    natCast (K := K) (c :: n) = 𝟙 + natCast n := rfl

theorem natCast_succ_ne_zero (n : TreeN) : natCast (K := K) (TreeN.succ n) ≠ 𝟘 := charZero n

theorem natCast_ne_zero_of_pos {n : TreeN} (h : TreeN.PathLT TreeN.zero n) :
    natCast (K := K) n ≠ 𝟘 := by
  cases h with
  | zero_lt c m =>
    cases c
    exact charZero m

theorem mul_inv_cancel' {a : K} (h : a ≠ 𝟘) : a * inv a = 𝟙 := mul_inv_cancel a h

theorem inv_mul_cancel' {a : K} (h : a ≠ 𝟘) : inv a * a = 𝟙 := by
  rw [mul_comm]
  exact mul_inv_cancel a h

theorem mul_left_cancel' {a b c : K} (ha : a ≠ 𝟘) (h : a * b = a * c) : b = c := by
  have h2 : inv a * (a * b) = inv a * (a * c) := by rw [h]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel' ha, one_mul, one_mul] at h2
  exact h2

theorem eq_zero_of_mul_eq_zero_left {a b : K} (ha : a ≠ 𝟘) (h : a * b = 𝟘) : b = 𝟘 := by
  apply mul_left_cancel' ha
  rw [h, mul_zero]

theorem mul_ne_zero' {a b : K} (ha : a ≠ 𝟘) (hb : b ≠ 𝟘) : a * b ≠ 𝟘 :=
  fun h => hb (eq_zero_of_mul_eq_zero_left ha h)

end TField
end
