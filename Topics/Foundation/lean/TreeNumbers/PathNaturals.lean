module

public import PrimitiveTree.UnaryPaths
public import TreeNumbers.AlgebraInterface

@[expose] public section

/-!
# `TreeN`: natural numbers as unary root paths

The carrier of the intrinsic natural numbers is the type of unary root paths itself.
Addition is concatenation of paths, multiplication is repeated concatenation.  All laws are
proved by structural induction on paths.
-/

/-- The intrinsic natural numbers: unary root paths. -/
abbrev TreeN : Type := UnaryPath

namespace TreeN

/-- Zero: the empty (root) path. -/
abbrev zero : TreeN := UnaryPath.zeroPath

/-- One: the one-edge path. -/
abbrev one : TreeN := UnaryPath.onePath

/-- Successor: adjoin one primitive unit edge. -/
abbrev succ (n : TreeN) : TreeN := UnaryPath.extend n

/-- Two: `one + one`, written as two successive unit edges. -/
abbrev two : TreeN := succ one

/-- Addition: concatenation of unary paths. -/
def add (m n : TreeN) : TreeN := UnaryPath.concat m n

/-- Multiplication: repeated concatenation, by structural recursion on the first path. -/
def mul : TreeN → TreeN → TreeN
  | [], _ => []
  | _ :: m, n => add n (mul m n)

instance : Add TreeN := ⟨add⟩
instance : Mul TreeN := ⟨mul⟩

theorem nil_add (n : TreeN) : ([] : TreeN) + n = n := rfl

theorem cons_add (c : UnitChild) (m n : TreeN) : (c :: m) + n = c :: (m + n) := rfl

theorem succ_add (m n : TreeN) : succ m + n = succ (m + n) := rfl

theorem nil_mul (n : TreeN) : ([] : TreeN) * n = [] := rfl

theorem cons_mul (c : UnitChild) (m n : TreeN) : (c :: m) * n = n + m * n := rfl

theorem succ_mul (m n : TreeN) : succ m * n = n + m * n := rfl

theorem add_zero (m : TreeN) : m + zero = m := by
  induction m with
  | nil => rfl
  | cons c m ih =>
    show c :: (m + zero) = c :: m
    rw [ih]

theorem add_assoc (a b c : TreeN) : a + b + c = a + (b + c) := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    show x :: (a + b + c) = x :: (a + (b + c))
    rw [ih]

theorem add_succ (m n : TreeN) : m + succ n = succ (m + n) := by
  induction m with
  | nil => rfl
  | cons c m ih =>
    show c :: (m + succ n) = succ (c :: (m + n))
    rw [ih]
    cases c
    rfl

theorem add_comm (m n : TreeN) : m + n = n + m := by
  induction m with
  | nil =>
    show n = n + zero
    rw [add_zero]
  | cons c m ih =>
    show c :: (m + n) = n + c :: m
    rw [UnaryPath.cons_eq_extend, UnaryPath.cons_eq_extend, add_succ, ih]

theorem add_left_cancel {k m n : TreeN} (h : k + m = k + n) : m = n := by
  induction k with
  | nil => exact h
  | cons c k ih =>
    apply ih
    injection h

theorem add_right_cancel {k m n : TreeN} (h : m + k = n + k) : m = n := by
  rw [add_comm m k, add_comm n k] at h
  exact add_left_cancel h

theorem add_left_comm (a b c : TreeN) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem mul_zero (m : TreeN) : m * zero = zero := by
  induction m with
  | nil => rfl
  | cons c m ih =>
    show zero + m * zero = zero
    rw [ih]
    rfl

theorem mul_succ (m n : TreeN) : m * succ n = m + m * n := by
  induction m with
  | nil => rfl
  | cons c m ih =>
    show succ n + m * succ n = c :: m + (n + m * n)
    rw [ih, succ_add, cons_add, UnaryPath.cons_eq_extend, add_left_comm]

theorem mul_comm (m n : TreeN) : m * n = n * m := by
  induction m with
  | nil =>
    show zero = n * zero
    rw [mul_zero]
  | cons c m ih =>
    show n + m * n = n * (c :: m)
    rw [UnaryPath.cons_eq_extend, mul_succ, ih]

theorem right_distrib (a b c : TreeN) : (a + b) * c = a * c + b * c := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    show c + (a + b) * c = c + a * c + b * c
    rw [ih, add_assoc]

theorem left_distrib (a b c : TreeN) : a * (b + c) = a * b + a * c := by
  rw [mul_comm, right_distrib, mul_comm b a, mul_comm c a]

theorem mul_assoc (a b c : TreeN) : a * b * c = a * (b * c) := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    show (b + a * b) * c = b * c + a * (b * c)
    rw [right_distrib, ih]

theorem one_mul (n : TreeN) : one * n = n := by
  show n + zero = n
  exact add_zero n

theorem mul_one (n : TreeN) : n * one = n := by
  rw [mul_comm]
  exact one_mul n

theorem zero_mul (n : TreeN) : zero * n = zero := rfl

theorem zero_add (n : TreeN) : zero + n = n := rfl

/-- `TreeN` populates the commutative-semiring interface. -/
instance instCSR : CSR TreeN where
  zero := zero
  one := one
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  zero_mul := zero_mul
  left_distrib := left_distrib

theorem csr_zero : (𝟘 : TreeN) = zero := rfl
theorem csr_one : (𝟙 : TreeN) = one := rfl

theorem one_add (n : TreeN) : one + n = succ n := rfl

theorem add_one (n : TreeN) : n + one = succ n := by
  rw [add_comm]
  rfl

theorem succ_ne_zero (n : TreeN) : succ n ≠ zero := fun h => nomatch h

theorem succ_injective {m n : TreeN} (h : succ m = succ n) : m = n := by
  injection h

/-- Sum is zero only if both summands are zero. -/
theorem eq_zero_of_add_eq_zero_left {m n : TreeN} (h : m + n = zero) : m = zero := by
  cases m with
  | nil => rfl
  | cons c m => exact nomatch h

theorem eq_zero_of_add_eq_zero_right {m n : TreeN} (h : m + n = zero) : n = zero := by
  rw [add_comm] at h
  exact eq_zero_of_add_eq_zero_left h

/-- `m + n = m` forces `n = zero`. -/
theorem eq_zero_of_add_eq_self {m n : TreeN} (h : m + n = m) : n = zero := by
  apply add_left_cancel (k := m)
  rw [h, add_zero]

/-- No zero divisors among path counts. -/
theorem mul_eq_zero {m n : TreeN} (h : m * n = zero) : m = zero ∨ n = zero := by
  cases m with
  | nil => exact Or.inl rfl
  | cons c m => exact Or.inr (eq_zero_of_add_eq_zero_left h)

/-- Decidable equality of unary paths, by structural recursion. -/
def decEq : (m n : TreeN) → Decidable (m = n)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => nomatch h)
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | c :: m, d :: n =>
    match decEq m n with
    | isTrue h => isTrue (by rw [h, UnitChild.eq c d])
    | isFalse h => isFalse (fun e => h (by injection e))

instance : DecidableEq TreeN := decEq

end TreeN
end
