module

public import TreeNumbers.RationalArityIndependence

@[expose] public section

/-!
# Task 04 — gap closures for `TreeN`, `TreeZ` and the algebra of `TreeQ`

Small, explicit additions requested by the Task 04 property ledger.  Nothing here changes an
existing carrier, relation or operation.

* `TreeN`: an explicit induction principle, structural recursion with its defining equations and
  **uniqueness** (initiality of `(TreeN, zero, succ)` among all `(β, b, f)`), `zero ≠ one`,
  totality of `PathLE`, right monotonicity of multiplication, and the successor characterisation
  of the strict order.
* `TreeZ`: reflection of the order by `TreeN → TreeZ`, preservation of strict order, the sign
  rules for products, squares are nonnegative, `0 ≤ 1`, negation reverses the order, additive
  order cancellation.
* `TreeQ`: identity and composition coherence of the comparison maps `transfer`, and
  **independence of the class `ofF f` from the choice of the two distinguished letters**,
  together with the fact that the raw witness *triple* does depend on that choice.
-/

open CSR CRing

namespace TreeN

/-! ## A1. Induction, recursion and initiality -/

/-- Structural induction on unary root paths (zero and successor cases are exhaustive). -/
theorem induction {P : TreeN → Prop} (h0 : P zero) (hs : ∀ n, P n → P (succ n)) :
    ∀ n, P n := by
  intro n
  induction n with
  | nil => exact h0
  | cons c n ih =>
    rw [UnaryPath.cons_eq_extend]
    exact hs n ih

/-- Structural recursion on unary root paths: iterate `f` along the path, starting from `b`. -/
def recN {β : Type} (b : β) (f : β → β) (n : TreeN) : β := UnaryPath.iterate f n b

theorem recN_zero {β : Type} (b : β) (f : β → β) : recN b f zero = b := rfl

theorem recN_succ {β : Type} (b : β) (f : β → β) (n : TreeN) :
    recN b f (succ n) = f (recN b f n) := rfl

/-- **Initiality / uniqueness of recursion**: any function satisfying the two recursion
equations agrees with `recN b f` everywhere. -/
theorem recN_unique {β : Type} (b : β) (f : β → β) (h : TreeN → β) (h0 : h zero = b)
    (hs : ∀ n, h (succ n) = f (h n)) : ∀ n, h n = recN b f n := by
  apply induction
  · exact h0
  · intro n ih
    rw [hs n, ih]
    rfl

/-- Zero (the root path) is distinct from one (the one-edge path). -/
theorem zero_ne_one : zero ≠ one := fun h => nomatch h

/-! ## A2. Order: totality and multiplicative compatibility -/

theorem le_total (m n : TreeN) : PathLE m n ∨ PathLE n m := by
  cases le_or_lt m n with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (le_of_lt h)

theorem mul_le_mul_right (k : TreeN) {m n : TreeN} (h : PathLE m n) : PathLE (m * k) (n * k) := by
  rw [mul_comm m k, mul_comm n k]
  exact mul_le_mul_left k h

theorem mul_le_mul' {a b c d : TreeN} (h1 : PathLE a b) (h2 : PathLE c d) :
    PathLE (a * c) (b * d) :=
  le_trans (mul_le_mul_right c h1) (mul_le_mul_left b h2)

/-- The strict order is the successor-shifted non-strict order (both directions). -/
theorem lt_iff_succ_le (m n : TreeN) : (PathLT m n → PathLE (succ m) n) ∧
    (PathLE (succ m) n → PathLT m n) :=
  ⟨succ_le_of_lt, lt_of_succ_le⟩

/-- The non-strict order is the prefix / extension order of unary paths (both directions). -/
theorem le_iff_exists_add (m n : TreeN) : (PathLE m n → ∃ k, n = m + k) ∧
    ((∃ k, n = m + k) → PathLE m n) :=
  ⟨exists_of_le, fun ⟨k, hk⟩ => by rw [hk]; exact le_add m k⟩

end TreeN

namespace TreeZ

open TreeN (PathLE PathLT)

/-! ## B. Order and sign on `TreeZ` -/

theorem ofN_pos' (k : TreeN) : (ofN k).pos = k := by
  cases k with
  | nil => rfl
  | cons c k => rfl

theorem not_nonNeg_neg_ofN_succ (k : TreeN) : ¬ NonNeg (-ofN (TreeN.succ k)) := by
  intro h
  have e : (-ofN (TreeN.succ k)).neg = (ofN (TreeN.succ k)).pos := rfl
  unfold NonNeg at h
  rw [e, ofN_pos'] at h
  exact TreeN.succ_ne_zero k h

/-- `TreeN → TreeZ` reflects the order. -/
theorem le_of_ofN_le {m n : TreeN} (h : LE (ofN m) (ofN n)) : PathLE m n := by
  cases TreeN.le_or_lt m n with
  | inl h' => exact h'
  | inr h' =>
    exfalso
    obtain ⟨k, hk⟩ := TreeN.exists_of_lt h'
    unfold LE at h
    rw [hk, ofN_add, neg_add, ← add_assoc, add_neg_cancel, zero_add] at h
    exact not_nonNeg_neg_ofN_succ k h

/-- Strict order on `TreeZ`: `x < y` iff `y ≤ x` fails.  Decidable, since `LE` is. -/
def LT (x y : TreeZ) : Prop := ¬ LE y x

instance (x y : TreeZ) : Decidable (LT x y) := instDecidableNot

/-- `TreeN → TreeZ` preserves strict order. -/
theorem ofN_lt_ofN {m n : TreeN} (h : PathLT m n) : LT (ofN m) (ofN n) := fun h' =>
  TreeN.not_lt_of_le (le_of_ofN_le h') h

/-- `TreeN → TreeZ` reflects strict order. -/
theorem lt_of_ofN_lt {m n : TreeN} (h : LT (ofN m) (ofN n)) : PathLT m n := by
  cases TreeN.le_or_lt n m with
  | inl h' => exact absurd (ofN_le_ofN h') h
  | inr h' => exact h'

theorem lt_irrefl (x : TreeZ) : ¬ LT x x := fun h => h (le_refl x)

theorem le_of_lt {x y : TreeZ} (h : LT x y) : LE x y := by
  cases le_total x y with
  | inl h' => exact h'
  | inr h' => exact absurd h' h

theorem lt_trichotomy (x y : TreeZ) : LT x y ∨ x = y ∨ LT y x := by
  cases decEq x y with
  | isTrue e => exact Or.inr (Or.inl e)
  | isFalse ne =>
    cases le_total x y with
    | inl h => exact Or.inl (fun h' => ne (le_antisymm h h'))
    | inr h => exact Or.inr (Or.inr (fun h' => ne (le_antisymm h' h)))

theorem zero_le_one : LE 𝟘 𝟙 := by
  rw [← ofN_zero, ← ofN_one]
  exact ofN_le_ofN (TreeN.zero_le _)

theorem zero_lt_one : LT 𝟘 𝟙 := by
  rw [← ofN_zero, ← ofN_one]
  exact ofN_lt_ofN (TreeN.zero_lt_succ _)

theorem le_of_add_le_add_left {x y z : TreeZ} (h : LE (z + x) (z + y)) : LE x y := by
  have h2 := add_le_add_left (-z) h
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at h2
  exact h2

theorem add_le_add_right {x y : TreeZ} (z : TreeZ) (h : LE x y) : LE (x + z) (y + z) := by
  rw [add_comm x z, add_comm y z]
  exact add_le_add_left z h

theorem neg_le_neg {x y : TreeZ} (h : LE x y) : LE (-y) (-x) := by
  unfold LE at *
  rw [neg_neg, add_comm]
  exact h

/-- Sign rule: the product of two nonpositive integers is nonnegative. -/
theorem nonNeg_mul_of_nonpos {x y : TreeZ} (hx : NonNeg (-x)) (hy : NonNeg (-y)) :
    NonNeg (x * y) := by
  rw [← neg_mul_neg]
  exact nonNeg_mul hx hy

/-- Sign rule: nonnegative times nonpositive is nonpositive. -/
theorem nonpos_mul_of_nonNeg_of_nonpos {x y : TreeZ} (hx : NonNeg x) (hy : NonNeg (-y)) :
    NonNeg (-(x * y)) := by
  rw [← mul_neg]
  exact nonNeg_mul hx hy

/-- Squares are nonnegative. -/
theorem nonNeg_mul_self (x : TreeZ) : NonNeg (x * x) := by
  cases nonNeg_or_neg_nonNeg x with
  | inl h => exact nonNeg_mul h h
  | inr h => exact nonNeg_mul_of_nonpos h h

/-- Multiplication by a strictly positive integer reflects the order. -/
theorem le_of_mul_le_mul_pos {x y : TreeZ} {d : TreeN} (hd : PathLT TreeN.zero d)
    (h : LE (ofN d * x) (ofN d * y)) : LE x y := by
  cases le_total x y with
  | inl h' => exact h'
  | inr h' =>
    have h2 := mul_le_mul_of_nonneg (nonNeg_ofN d) h'
    have e := le_antisymm h h2
    rw [mul_left_cancel (ofN_ne_zero hd) e]
    exact le_refl y

end TreeZ

/-! ## C1. Where the two-letter hypothesis is needed -/

namespace TriplePath

/-- Over the **one-letter** alphabet no triple configuration has numerator zero: distinct unary
paths have distinct unit-edge sums.  Hence the universal witness property fails there, which is
exactly why every rational-field statement assumes `[TwoLetters α]`. -/
theorem unary_numer_ne_zero (t : TriplePath UnitChild) : numer t ≠ 𝟘 := by
  intro h
  apply t.ne12
  have e := TreeZ.mkZ_eq_zero h
  rw [UnaryTree.pathSum_self, UnaryTree.pathSum_self] at e
  exact e

/-- The universal witness property is false for the one-letter alphabet. -/
theorem unary_no_universal_witness :
    ¬ ∀ (A : TreeZ) (D : TreeN), TreeN.PathLT TreeN.zero D →
      ∃ t : TriplePath UnitChild, numer t = A ∧ denom t = D := by
  intro h
  obtain ⟨t, ht, _⟩ := h 𝟘 TreeN.one (TreeN.zero_lt_succ TreeN.zero)
  exact unary_numer_ne_zero t ht

end TriplePath

/-! ## C3. Coherence and letter-choice independence of the rational comparison maps -/

namespace TreeQ

open TriplePath

variable {α β γ : Type}

/-- The class `ofF f` does **not** depend on which two distinguished letters are used to build
the witness triple: two letter choices `I`, `J` on the same alphabet give the same class. -/
theorem ofF_letter_indep (I J : TwoLetters α) (f : Frac) :
    @ofF α I f = @ofF α J f := by
  apply sound
  show Frac.Eqv (toFrac (@ofFrac α I f)) (toFrac (@ofFrac α J f))
  rw [@toFrac_ofFrac α I, @toFrac_ofFrac α J]
  exact Frac.eqv_refl f

/-- The letter-swapped choice. -/
def swapLetters (I : TwoLetters α) : TwoLetters α := ⟨I.l1, I.l0, fun h => I.ne h.symm⟩

/-- In contrast, the raw witness **triple** does depend on the letter choice: swapping the two
letters changes its first path.  Only its class is choice-independent. -/
theorem ofFrac_letter_dependent (I : TwoLetters α) (f : Frac) :
    (@ofFrac α I f).p1 ≠ (@ofFrac α (swapLetters I) f).p1 := by
  intro h
  have e1 : (@ofFrac α I f).p1 = I.l0 :: I.l0 :: Word.rep I.l0 (f.num.pos + f.den) :=
    @wP1_eq α I _ _
  have e2 : (@ofFrac α (swapLetters I) f).p1 =
      I.l1 :: I.l1 :: Word.rep I.l1 (f.num.pos + f.den) := @wP1_eq α (swapLetters I) _ _
  rw [e1, e2] at h
  injection h with h1 _
  exact I.ne h1

/-- `transfer` itself does not depend on the letter choice of the target alphabet. -/
theorem transfer_letter_indep (I J : TwoLetters β) (x : TreeQ α) :
    @transfer α β I x = @transfer α β J x := by
  induction x using ind_mk with
  | h t => exact ofF_letter_indep I J (toFrac t)

variable [TwoLetters α] [TwoLetters β] [TwoLetters γ]

/-- Identity coherence: the comparison map of an alphabet with itself is the identity. -/
theorem transfer_self (x : TreeQ α) : transfer α α x = x := by
  induction x using ind_ofF with
  | h f => exact transfer_ofF f

/-- Composition coherence: comparing `α → β → γ` equals comparing `α → γ` directly. -/
theorem transfer_comp (x : TreeQ α) : transfer β γ (transfer α β x) = transfer α γ x := by
  induction x using ind_ofF with
  | h f => rw [transfer_ofF, transfer_ofF, transfer_ofF]

/-- The comparison maps preserve the image of every internal fraction datum. -/
theorem transfer_natCast (n : TreeN) :
    transfer α β (TField.natCast n) = TField.natCast n := by
  show transfer α β (natCastWith zeroQ oneQ (fun x y => x + y) n) =
    natCastWith zeroQ oneQ (fun x y => x + y) n
  rw [natCast_eq, natCast_eq, transfer_ofF]

/-- The arity isomorphisms compose coherently. -/
theorem arityIso_comp (x : TreeQ α) :
    (arityIso β γ).toFun ((arityIso α β).toFun x) = (arityIso α γ).toFun x :=
  transfer_comp x

end TreeQ

end
