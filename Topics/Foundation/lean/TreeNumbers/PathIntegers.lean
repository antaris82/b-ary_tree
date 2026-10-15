module

public import TreeNumbers.PathOrder

@[expose] public section

/-!
# `TreeZ`: integers as oriented differences of two unary root paths

A raw integer is a pair of unary root paths `(m, n)`, read as the oriented difference
"`m` minus `n`".  Two pairs are identified when `m + q = p + n` (path addition).

Instead of a kernel quotient we use an *explicitly proved canonical normalization*:
`normPair` strips common unit steps from both paths, so every class has a unique
representative in which one of the two paths is the root path.  `TreeZ` is the type of such
normalized path pairs; it is proved (`mkZ_sound`, `mkZ_exact`) that two raw pairs have equal
normal forms exactly when they are related by `PairEq`.
-/

namespace TreeN

/-- The defining relation of oriented path differences. -/
def PairEq (m n p q : TreeN) : Prop := m + q = p + n

theorem pairEq_refl (m n : TreeN) : PairEq m n m n := rfl

theorem pairEq_symm {m n p q : TreeN} (h : PairEq m n p q) : PairEq p q m n := h.symm

theorem pairEq_trans {a b c d e f : TreeN} (h1 : PairEq a b c d) (h2 : PairEq c d e f) :
    PairEq a b e f := by
  unfold PairEq at *
  apply add_right_cancel (k := d)
  rw [add_assoc, add_comm f d, ← add_assoc, h1, add_assoc, add_comm b f, ← add_assoc, h2,
    add_assoc, add_comm d b, ← add_assoc]

/-- Canonical normalization: strip common unit steps. -/
def normPair : TreeN → TreeN → TreeN × TreeN
  | [], n => ([], n)
  | c :: m, [] => (c :: m, [])
  | _ :: m, _ :: n => normPair m n

theorem normPair_normal (m n : TreeN) :
    (normPair m n).1 = zero ∨ (normPair m n).2 = zero := by
  induction m generalizing n with
  | nil => exact Or.inl rfl
  | cons c m ih =>
    cases n with
    | nil => exact Or.inr rfl
    | cons d n => exact ih n

theorem normPair_pairEq (m n : TreeN) : PairEq (normPair m n).1 (normPair m n).2 m n := by
  induction m generalizing n with
  | nil => rfl
  | cons c m ih =>
    cases n with
    | nil => rfl
    | cons d n =>
      have h := ih n
      unfold PairEq at *
      show (normPair m n).1 + d :: n = c :: m + (normPair m n).2
      rw [UnaryPath.cons_eq_extend d, UnaryPath.cons_eq_extend c, add_succ, succ_add, h]

/-- Uniqueness of normal forms. -/
theorem normal_unique {a b c d : TreeN} (h1 : a = zero ∨ b = zero) (h2 : c = zero ∨ d = zero)
    (h : a + d = c + b) : a = c ∧ b = d := by
  cases h1 with
  | inl ha =>
    cases h2 with
    | inl hc =>
      rw [ha, hc] at h
      exact ⟨by rw [ha, hc], h.symm⟩
    | inr hd =>
      rw [ha, hd] at h
      have h' : c + b = zero := h.symm
      exact ⟨by rw [ha, eq_zero_of_add_eq_zero_left h'],
        by rw [hd, eq_zero_of_add_eq_zero_right h']⟩
  | inr hb =>
    cases h2 with
    | inl hc =>
      rw [hb, hc, add_zero] at h
      exact ⟨by rw [hc, eq_zero_of_add_eq_zero_left h],
        by rw [hb, eq_zero_of_add_eq_zero_right h]⟩
    | inr hd =>
      rw [hb, hd, add_zero, add_zero] at h
      exact ⟨h, by rw [hb, hd]⟩

end TreeN

open TreeN

/-- The tree integers: normalized oriented differences of two unary root paths. -/
structure TreeZ where
  pos : TreeN
  neg : TreeN
  normal : pos = TreeN.zero ∨ neg = TreeN.zero

namespace TreeZ

theorem ext {x y : TreeZ} (h1 : x.pos = y.pos) (h2 : x.neg = y.neg) : x = y := by
  cases x
  cases y
  cases h1
  cases h2
  rfl

/-- The class of the raw path pair `(m, n)`. -/
def mkZ (m n : TreeN) : TreeZ := ⟨(normPair m n).1, (normPair m n).2, normPair_normal m n⟩

theorem mkZ_pairEq (m n : TreeN) : PairEq (mkZ m n).pos (mkZ m n).neg m n :=
  normPair_pairEq m n

/-- Related raw pairs have the same class. -/
theorem mkZ_sound {m n p q : TreeN} (h : PairEq m n p q) : mkZ m n = mkZ p q := by
  have h1 := pairEq_trans (pairEq_trans (mkZ_pairEq m n) h) (pairEq_symm (mkZ_pairEq p q))
  have h2 := normal_unique (mkZ m n).normal (mkZ p q).normal h1
  exact ext h2.1 h2.2

/-- Equal classes come from related raw pairs. -/
theorem mkZ_exact {m n p q : TreeN} (h : mkZ m n = mkZ p q) : PairEq m n p q := by
  have h1 := mkZ_pairEq m n
  rw [h] at h1
  exact pairEq_trans (pairEq_symm h1) (mkZ_pairEq p q)

theorem mkZ_self (x : TreeZ) : mkZ x.pos x.neg = x := by
  have h := normal_unique (mkZ x.pos x.neg).normal x.normal (mkZ_pairEq x.pos x.neg)
  exact ext h.1 h.2

/-- Induction principle: every tree integer is the class of a raw path pair. -/
theorem ind_mk {P : TreeZ → Prop} (h : ∀ m n, P (mkZ m n)) (x : TreeZ) : P x := by
  rw [← mkZ_self x]
  exact h _ _

/-! ## Operations -/

def zeroZ : TreeZ := mkZ TreeN.zero TreeN.zero
def oneZ : TreeZ := mkZ TreeN.one TreeN.zero

def add (x y : TreeZ) : TreeZ := mkZ (x.pos + y.pos) (x.neg + y.neg)

/-- Negation exchanges the two paths. -/
def negate (x : TreeZ) : TreeZ := ⟨x.neg, x.pos, Or.symm x.normal⟩

def mul (x y : TreeZ) : TreeZ :=
  mkZ (x.pos * y.pos + x.neg * y.neg) (x.pos * y.neg + x.neg * y.pos)

instance : Add TreeZ := ⟨add⟩
instance : Neg TreeZ := ⟨negate⟩
instance : Mul TreeZ := ⟨mul⟩

/-! ## Compatibility of the raw operations with `PairEq` -/

theorem add_mk (a b c d : TreeN) : mkZ a b + mkZ c d = mkZ (a + c) (b + d) := by
  apply mkZ_sound
  have h1 := mkZ_pairEq a b
  have h2 := mkZ_pairEq c d
  unfold PairEq at *
  rw [CSR.add_add_add_comm, h1, h2, CSR.add_add_add_comm]

theorem neg_mk (a b : TreeN) : -(mkZ a b) = mkZ b a := by
  rw [← mkZ_self (-(mkZ a b))]
  apply mkZ_sound
  have h1 := mkZ_pairEq a b
  unfold PairEq at *
  show (mkZ a b).neg + a = b + (mkZ a b).pos
  rw [add_comm, ← h1, add_comm]

/-- Raw multiplication respects `PairEq` in its first argument. -/
theorem rawMul_resp_left {a b a' b' : TreeN} (c d : TreeN) (h : a + b' = a' + b) :
    PairEq (a * c + b * d) (a * d + b * c) (a' * c + b' * d) (a' * d + b' * c) := by
  unfold PairEq
  have e1 : a * c + b * d + (a' * d + b' * c) = (a + b') * c + (b + a') * d := by
    rw [right_distrib, right_distrib, add_comm (a' * d) (b' * c), CSR.add_add_add_comm]
  have e2 : a' * c + b' * d + (a * d + b * c) = (a' + b) * c + (b' + a) * d := by
    rw [right_distrib, right_distrib, add_comm (a * d) (b * c), CSR.add_add_add_comm]
  rw [e1, e2, h, add_comm b a', add_comm b' a, h]

theorem rawMul_resp_right (a b : TreeN) {c d c' d' : TreeN} (h : c + d' = c' + d) :
    PairEq (a * c + b * d) (a * d + b * c) (a * c' + b * d') (a * d' + b * c') := by
  have h' := rawMul_resp_left a b h
  unfold PairEq at *
  rw [mul_comm c a, mul_comm d b, mul_comm d a, mul_comm c b, mul_comm c' a, mul_comm d' b,
    mul_comm d' a, mul_comm c' b, add_comm (b * c) (a * d), add_comm (b * c') (a * d')] at h'
  exact h'

theorem mul_mk (a b c d : TreeN) :
    mkZ a b * mkZ c d = mkZ (a * c + b * d) (a * d + b * c) := by
  show mkZ ((mkZ a b).pos * (mkZ c d).pos + (mkZ a b).neg * (mkZ c d).neg)
      ((mkZ a b).pos * (mkZ c d).neg + (mkZ a b).neg * (mkZ c d).pos) = _
  rw [mkZ_sound (rawMul_resp_left (mkZ c d).pos (mkZ c d).neg (mkZ_pairEq a b)),
    mkZ_sound (rawMul_resp_right a b (mkZ_pairEq c d))]

/-! ## Commutative ring laws -/

theorem add_comm' (x y : TreeZ) : x + y = y + x := by
  induction x using ind_mk with | h a b => ?_
  induction y using ind_mk with | h c d => ?_
  rw [add_mk, add_mk, add_comm a c, add_comm b d]

theorem add_assoc' (x y z : TreeZ) : x + y + z = x + (y + z) := by
  induction x using ind_mk with | h a b => ?_
  induction y using ind_mk with | h c d => ?_
  induction z using ind_mk with | h e f => ?_
  rw [add_mk, add_mk, add_mk, add_mk, add_assoc, add_assoc]

theorem zero_add' (x : TreeZ) : zeroZ + x = x := by
  induction x using ind_mk with | h a b => ?_
  exact add_mk TreeN.zero TreeN.zero a b

theorem neg_add_cancel' (x : TreeZ) : -x + x = zeroZ := by
  induction x using ind_mk with | h a b => ?_
  rw [neg_mk, add_mk]
  apply mkZ_sound
  show b + a + zero = zero + (a + b)
  rw [add_zero, add_comm]
  rfl

theorem mul_comm' (x y : TreeZ) : x * y = y * x := by
  induction x using ind_mk with | h a b => ?_
  induction y using ind_mk with | h c d => ?_
  rw [mul_mk, mul_mk, mul_comm a c, mul_comm b d, mul_comm a d, mul_comm b c, add_comm (d * a)]

theorem mul_assoc' (x y z : TreeZ) : x * y * z = x * (y * z) := by
  induction x using ind_mk with | h a b => ?_
  induction y using ind_mk with | h c d => ?_
  induction z using ind_mk with | h e f => ?_
  rw [mul_mk, mul_mk, mul_mk, mul_mk]
  have e1 : (a * c + b * d) * e + (a * d + b * c) * f
      = a * (c * e + d * f) + b * (c * f + d * e) := by
    rw [right_distrib, right_distrib, left_distrib, left_distrib, mul_assoc, mul_assoc,
      mul_assoc, mul_assoc, CSR.add_add_add_comm (a * (c * e)), add_comm (b * (d * e))]
  have e2 : (a * c + b * d) * f + (a * d + b * c) * e
      = a * (c * f + d * e) + b * (c * e + d * f) := by
    rw [right_distrib, right_distrib, left_distrib, left_distrib, mul_assoc, mul_assoc,
      mul_assoc, mul_assoc, CSR.add_add_add_comm (a * (c * f)), add_comm (b * (d * f))]
  rw [e1, e2]

theorem one_mul' (x : TreeZ) : oneZ * x = x := by
  induction x using ind_mk with | h a b => ?_
  show mkZ TreeN.one TreeN.zero * mkZ a b = mkZ a b
  rw [mul_mk, one_mul, one_mul, TreeN.zero_mul, TreeN.zero_mul, add_zero, add_zero]

theorem zero_mul' (x : TreeZ) : zeroZ * x = zeroZ := by
  induction x using ind_mk with | h a b => ?_
  show mkZ TreeN.zero TreeN.zero * mkZ a b = mkZ TreeN.zero TreeN.zero
  rw [mul_mk]
  rfl

theorem left_distrib' (x y z : TreeZ) : x * (y + z) = x * y + x * z := by
  induction x using ind_mk with | h a b => ?_
  induction y using ind_mk with | h c d => ?_
  induction z using ind_mk with | h e f => ?_
  rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk, left_distrib, left_distrib, left_distrib,
    left_distrib, CSR.add_add_add_comm, CSR.add_add_add_comm (a * d)]

/-- `TreeZ` populates the commutative-ring interface. -/
instance instCRing : CRing TreeZ where
  zero := zeroZ
  one := oneZ
  add_assoc := add_assoc'
  add_comm := add_comm'
  zero_add := zero_add'
  mul_assoc := mul_assoc'
  mul_comm := mul_comm'
  one_mul := one_mul'
  zero_mul := zero_mul'
  left_distrib := left_distrib'
  neg_add_cancel := neg_add_cancel'

theorem csr_zero : (𝟘 : TreeZ) = mkZ TreeN.zero TreeN.zero := rfl
theorem csr_one : (𝟙 : TreeZ) = mkZ TreeN.one TreeN.zero := rfl

/-! ## Zero detection, decidable equality -/

theorem mkZ_eq_zero {a b : TreeN} (h : mkZ a b = 𝟘) : a = b := by
  have h' := mkZ_exact h
  unfold PairEq at h'
  rw [add_zero] at h'
  exact h'

theorem mkZ_eq_zero_of {a b : TreeN} (h : a = b) : mkZ a b = 𝟘 := by
  apply mkZ_sound
  show a + zero = zero + b
  rw [add_zero, h]
  rfl

theorem zero_ne_one : (𝟘 : TreeZ) ≠ 𝟙 := by
  intro h
  have h' := mkZ_exact h
  exact nomatch h'

/-- Decidable equality of tree integers (componentwise on normal forms). -/
def decEq (x y : TreeZ) : Decidable (x = y) :=
  match TreeN.decEq x.pos y.pos, TreeN.decEq x.neg y.neg with
  | isTrue h1, isTrue h2 => isTrue (ext h1 h2)
  | isFalse h1, _ => isFalse (fun e => h1 (by rw [e]))
  | _, isFalse h2 => isFalse (fun e => h2 (by rw [e]))

instance : DecidableEq TreeZ := decEq

/-! ## No zero divisors and cancellation -/

/-- Raw form of the absence of zero divisors. -/
theorem raw_no_zero_divisors {a b c d : TreeN} (h : a * c + b * d = a * d + b * c) :
    a = b ∨ c = d :=
  match compare a b with
  | Trichotomy.eq e => Or.inl e
  | Trichotomy.lt hl => by
    obtain ⟨k, hk⟩ := exists_of_lt hl
    rw [hk, right_distrib, right_distrib, ← add_assoc, ← add_assoc, add_comm (a * c) (a * d)] at h
    have h2 := add_left_cancel h
    exact Or.inr (mul_left_cancel (zero_lt_succ k) h2).symm
  | Trichotomy.gt hg => by
    obtain ⟨k, hk⟩ := exists_of_lt hg
    rw [hk, right_distrib, right_distrib, CSR.add_right_comm (b * c),
      CSR.add_right_comm (b * d), add_comm (b * d) (b * c), add_assoc, add_assoc] at h
    exact Or.inr (mul_left_cancel (zero_lt_succ k) (add_left_cancel (add_left_cancel h)))

/-- `TreeZ` has no zero divisors. -/
theorem mul_eq_zero {x y : TreeZ} (h : x * y = 𝟘) : x = 𝟘 ∨ y = 𝟘 := by
  revert h
  induction x using ind_mk with | h a b => ?_
  induction y using ind_mk with | h c d => ?_
  intro h
  rw [mul_mk] at h
  cases raw_no_zero_divisors (mkZ_eq_zero h) with
  | inl e => exact Or.inl (mkZ_eq_zero_of e)
  | inr e => exact Or.inr (mkZ_eq_zero_of e)

/-- Multiplication by a nonzero tree integer is cancellative. -/
theorem mul_left_cancel {x y z : TreeZ} (hx : x ≠ 𝟘) (h : x * y = x * z) : y = z := by
  apply CRing.eq_of_add_neg_eq_zero
  have h2 : x * (y + -z) = 𝟘 := by
    rw [CSR.left_distrib, CRing.mul_neg, h, CRing.add_neg_cancel]
  cases mul_eq_zero h2 with
  | inl e => exact absurd e hx
  | inr e => exact e

theorem mul_right_cancel {x y z : TreeZ} (hx : x ≠ 𝟘) (h : y * x = z * x) : y = z := by
  rw [CSR.mul_comm y x, CSR.mul_comm z x] at h
  exact mul_left_cancel hx h

theorem mul_ne_zero {x y : TreeZ} (hx : x ≠ 𝟘) (hy : y ≠ 𝟘) : x * y ≠ 𝟘 := by
  intro h
  cases mul_eq_zero h with
  | inl e => exact hx e
  | inr e => exact hy e

/-! ## The canonical embedding `TreeN → TreeZ` -/

/-- Embedding of path counts: `n ↦ [n, root]`. -/
def ofN (n : TreeN) : TreeZ := mkZ n TreeN.zero

theorem ofN_zero : ofN TreeN.zero = 𝟘 := rfl
theorem ofN_one : ofN TreeN.one = 𝟙 := rfl

theorem ofN_add (m n : TreeN) : ofN (m + n) = ofN m + ofN n := by
  show mkZ (m + n) zero = mkZ m zero + mkZ n zero
  rw [add_mk]
  rfl

theorem ofN_mul (m n : TreeN) : ofN (m * n) = ofN m * ofN n := by
  show mkZ (m * n) zero = mkZ m zero * mkZ n zero
  rw [mul_mk, TreeN.mul_zero, TreeN.mul_zero, add_zero]
  rfl

theorem ofN_injective {m n : TreeN} (h : ofN m = ofN n) : m = n := by
  have h' := mkZ_exact h
  unfold PairEq at h'
  rw [add_zero, add_zero] at h'
  exact h'

theorem ofN_ne_zero {n : TreeN} (h : PathLT TreeN.zero n) : ofN n ≠ 𝟘 := by
  intro e
  exact ne_zero_of_pos h (ofN_injective e)

theorem mkZ_eq_sub (m n : TreeN) : mkZ m n = ofN m + -ofN n := by
  show mkZ m n = mkZ m zero + -mkZ n zero
  rw [neg_mk, add_mk, add_zero]
  rfl

/-! ## Sign classification, absolute value and order -/

/-- Constructive sign classification of a tree integer. -/
inductive Sign (x : TreeZ) : Type
  | zero : x = 𝟘 → Sign x
  | pos (n : TreeN) : x = ofN (succ n) → Sign x
  | neg (n : TreeN) : x = -ofN (succ n) → Sign x

/-- The sign decision procedure, by pattern matching on the normal form. -/
def sign : (x : TreeZ) → Sign x
  | ⟨[], [], _⟩ => Sign.zero rfl
  | ⟨c :: m, [], _⟩ => Sign.pos m (ext (by cases c; rfl) rfl)
  | ⟨[], c :: m, _⟩ => Sign.neg m (ext rfl (by cases c; rfl))
  | ⟨_ :: _, _ :: _, h⟩ => False.elim (by cases h with
      | inl h => exact nomatch h
      | inr h => exact nomatch h)

/-- Absolute value as a path count. -/
def absN (x : TreeZ) : TreeN := x.pos + x.neg

theorem absN_ofN (n : TreeN) : absN (ofN n) = n := by
  cases n with
  | nil => rfl
  | cons c n => exact add_zero _

theorem absN_neg (x : TreeZ) : absN (-x) = absN x := add_comm x.neg x.pos

theorem absN_pos {x : TreeZ} (h : x ≠ 𝟘) : PathLT TreeN.zero (absN x) :=
  match sign x with
  | Sign.zero e => absurd e h
  | Sign.pos n e => by rw [e, absN_ofN]; exact zero_lt_succ n
  | Sign.neg n e => by rw [e, absN_neg, absN_ofN]; exact zero_lt_succ n

/-- Nonnegativity: the negative path of the normal form is the root. -/
def NonNeg (x : TreeZ) : Prop := x.neg = TreeN.zero

/-- Order on tree integers. -/
def LE (x y : TreeZ) : Prop := NonNeg (y + -x)

instance (x : TreeZ) : Decidable (NonNeg x) := TreeN.decEq x.neg TreeN.zero
instance (x y : TreeZ) : Decidable (LE x y) := TreeN.decEq (y + -x).neg TreeN.zero

theorem mkZ_zero_neg (m : TreeN) : (mkZ m TreeN.zero).neg = TreeN.zero := by
  cases m with
  | nil => rfl
  | cons c m => rfl

theorem nonNeg_eq {x : TreeZ} (h : NonNeg x) : x = ofN x.pos := by
  have e : mkZ x.pos x.neg = x := mkZ_self x
  unfold NonNeg at h
  rw [h] at e
  exact e.symm

theorem nonNeg_ofN (n : TreeN) : NonNeg (ofN n) := mkZ_zero_neg n

theorem nonNeg_add {x y : TreeZ} (hx : NonNeg x) (hy : NonNeg y) : NonNeg (x + y) := by
  rw [nonNeg_eq hx, nonNeg_eq hy, ← ofN_add]
  exact nonNeg_ofN _

theorem nonNeg_mul {x y : TreeZ} (hx : NonNeg x) (hy : NonNeg y) : NonNeg (x * y) := by
  rw [nonNeg_eq hx, nonNeg_eq hy, ← ofN_mul]
  exact nonNeg_ofN _

theorem nonNeg_or_neg_nonNeg (x : TreeZ) : NonNeg x ∨ NonNeg (-x) := by
  cases x.normal with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

theorem eq_zero_of_nonNeg_of_nonNeg_neg {x : TreeZ} (h1 : NonNeg x) (h2 : NonNeg (-x)) :
    x = 𝟘 :=
  ext h2 h1

theorem le_refl (x : TreeZ) : LE x x := by
  unfold LE
  rw [CRing.add_neg_cancel]
  rfl

theorem le_trans {x y z : TreeZ} (h1 : LE x y) (h2 : LE y z) : LE x z := by
  unfold LE at *
  have e : z + -x = (z + -y) + (y + -x) := by
    rw [CSR.add_assoc, ← CSR.add_assoc (-y), CRing.neg_add_cancel, CSR.zero_add]
  rw [e]
  exact nonNeg_add h2 h1

theorem neg_sub (x y : TreeZ) : -(y + -x) = x + -y := by
  rw [CRing.neg_add, CRing.neg_neg, CSR.add_comm]

theorem le_antisymm {x y : TreeZ} (h1 : LE x y) (h2 : LE y x) : x = y := by
  unfold LE at *
  rw [← neg_sub] at h2
  have e := eq_zero_of_nonNeg_of_nonNeg_neg h1 h2
  exact (CRing.eq_of_add_neg_eq_zero e).symm

theorem le_total (x y : TreeZ) : LE x y ∨ LE y x := by
  unfold LE
  cases nonNeg_or_neg_nonNeg (y + -x) with
  | inl h => exact Or.inl h
  | inr h =>
    rw [neg_sub] at h
    exact Or.inr h

theorem add_le_add_left {x y : TreeZ} (z : TreeZ) (h : LE x y) : LE (z + x) (z + y) := by
  unfold LE at *
  rw [CRing.neg_add, CSR.add_add_add_comm, CRing.add_neg_cancel, CSR.zero_add]
  exact h

theorem mul_le_mul_of_nonneg {x y z : TreeZ} (hz : NonNeg z) (h : LE x y) :
    LE (z * x) (z * y) := by
  unfold LE at *
  rw [← CRing.mul_neg, ← CSR.left_distrib]
  exact nonNeg_mul hz h

theorem ofN_le_ofN {m n : TreeN} (h : PathLE m n) : LE (ofN m) (ofN n) := by
  obtain ⟨k, hk⟩ := exists_of_le h
  unfold LE
  rw [hk, ofN_add, CSR.add_comm (ofN m), CSR.add_assoc, CRing.add_neg_cancel, CSR.add_zero]
  exact nonNeg_ofN k

end TreeZ
end
