module

public import TreeNumbers.FoundationsLedger

@[expose] public section

/-!
# Provenance of `TreeN`: a derived depth-quotient characterization

`TreeN` is *defined* as the type of finite unary root paths `List UnitChild`, i.e. as the
vertex set of the unary tree `T₁` (see `PrimitiveTree/UnaryPaths`, `UnaryTree.pathSum_self`).
This module does **not** change that definition.  It adds an *auxiliary, derived* comparison:
for any alphabet `α`, the words of the full tree over `α` modulo "same unit-edge sum"

    w ~ v  :⇔  Word.pathSum w = Word.pathSum v,     DepthClass α := Quot (~)

form a second presentation of the same counting structure, provided a letter `a : α` is
supplied to realize every count by the explicit word `Word.rep a n`.

* `count : DepthClass α → TreeN` is induced by `pathSum` (no letter needed);
* `realize a : TreeN → DepthClass α` is induced by `Word.rep a`, and is inverse to `count`;
* the class `realize a n` does not depend on `a` (only the representative word does);
* word concatenation and word "repetition" are letter-free operations that descend to the
  quotient and correspond to `+` and `*` of `TreeN`; zero is the root class and `≤` is
  transferred along `count` (and coincides with the existence of a word extension);
* for the empty alphabet the quotient has exactly one element (the root class), so no positive
  count is represented; for the one-letter alphabet the quotient identifies nothing.

All of this is a comparison of two representations of one internally derived counting
structure; it is **not** a claim that branching data are needed for the arithmetic of `TreeN`.
-/

open TreeN ListOps Word

namespace DepthQuotient

variable {α : Type}

/-- Two words are related when their finite unit-edge sums agree. -/
def DepthRel (w v : Word α) : Prop := pathSum w = pathSum v

theorem depthRel_refl (w : Word α) : DepthRel w w := rfl

theorem depthRel_symm {w v : Word α} (h : DepthRel w v) : DepthRel v w := Eq.symm h

theorem depthRel_trans {w v u : Word α} (h1 : DepthRel w v) (h2 : DepthRel v u) :
    DepthRel w u := Eq.trans h1 h2

/-- The relation can equally be phrased through depth (`pathSum_eq_depth`). -/
theorem depthRel_iff_depth (w v : Word α) :
    (DepthRel w v → depth w = depth v) ∧ (depth w = depth v → DepthRel w v) := by
  constructor
  · intro h
    rw [← pathSum_eq_depth, ← pathSum_eq_depth]
    exact h
  · intro h
    show pathSum w = pathSum v
    rw [pathSum_eq_depth, pathSum_eq_depth]
    exact h

/-- The depth quotient of the full tree over `α`. -/
def DepthClass (α : Type) : Type := Quot (DepthRel (α := α))

/-- The class of a word. -/
def cls (w : Word α) : DepthClass α := Quot.mk _ w

theorem cls_sound {w v : Word α} (h : pathSum w = pathSum v) : cls w = cls v := Quot.sound h

theorem ind_cls {motive : DepthClass α → Prop} (h : ∀ w, motive (cls w)) (x : DepthClass α) :
    motive x := Quot.ind h x

/-- The count of a class, induced by the unit-edge sum (well defined by construction). -/
def count : DepthClass α → TreeN := Quot.lift pathSum (fun _ _ h => h)

theorem count_cls (w : Word α) : count (cls w) = pathSum w := rfl

/-- Classes with the same count are equal. -/
theorem count_injective {x y : DepthClass α} (h : count x = count y) : x = y := by
  revert h
  induction x using ind_cls with | h w => ?_
  induction y using ind_cls with | h v => ?_
  intro h
  exact cls_sound h

/-- Exactness: the class of a word depends **only** on its finite unit-edge sum. -/
theorem cls_eq_iff (w v : Word α) :
    (cls w = cls v → pathSum w = pathSum v) ∧ (pathSum w = pathSum v → cls w = cls v) :=
  ⟨fun h => by rw [← count_cls, ← count_cls, h], cls_sound⟩

/-- Realization of a count by the explicit word `a^n`. -/
def realize (a : α) (n : TreeN) : DepthClass α := cls (rep a n)

theorem count_realize (a : α) (n : TreeN) : count (realize a n) = n := pathSum_rep a n

theorem realize_count (a : α) (x : DepthClass α) : realize a (count x) = x :=
  count_injective (count_realize a (count x))

/-- Independence of the witnessing letter **at the level of classes**. -/
theorem realize_letter_indep (a b : α) (n : TreeN) : realize a n = realize b n :=
  count_injective (by rw [count_realize, count_realize])

/-- The representative words, by contrast, do depend on the letter. -/
theorem rep_letter_dependent {a b : α} (hab : a ≠ b) (n : TreeN) :
    rep a (succ n) ≠ rep b (succ n) := by
  intro h
  injection h with h1 _
  exact hab h1

/-- `count` is surjective (given a letter) and injective: a bijection with `TreeN`. -/
theorem count_surjective (a : α) (n : TreeN) : ∃ x : DepthClass α, count x = n :=
  ⟨realize a n, count_realize a n⟩

/-! ## Letter-free word operations and their descent to the quotient -/

/-- Grafting: concatenation of words (letter-free). -/
def graft (w v : Word α) : Word α := appL w v

/-- Repetition: one copy of `v` for every step of `w` (letter-free). -/
def repeatW : Word α → Word α → Word α
  | [], _ => []
  | _ :: w, v => appL v (repeatW w v)

theorem depth_appL (w v : Word α) : depth (appL w v) = depth w + depth v := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    show succ (depth (appL w v)) = succ (depth w) + depth v
    rw [ih]
    rfl

theorem pathSum_graft (w v : Word α) : pathSum (graft w v) = pathSum w + pathSum v := by
  rw [pathSum_eq_depth, pathSum_eq_depth, pathSum_eq_depth]
  exact depth_appL w v

theorem depth_repeatW (w v : Word α) : depth (repeatW w v) = depth w * depth v := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    show depth (appL v (repeatW w v)) = succ (depth w) * depth v
    rw [depth_appL, ih]
    rfl

theorem pathSum_repeatW (w v : Word α) : pathSum (repeatW w v) = pathSum w * pathSum v := by
  rw [pathSum_eq_depth, pathSum_eq_depth, pathSum_eq_depth]
  exact depth_repeatW w v

/-- Addition of classes, induced by grafting. -/
def addD : DepthClass α → DepthClass α → DepthClass α :=
  Quot.lift (fun w => Quot.lift (fun v => cls (graft w v))
      (fun v v' (h : pathSum v = pathSum v') => cls_sound (by
        rw [pathSum_graft, pathSum_graft, h])))
    (fun w w' (h : pathSum w = pathSum w') => funext (fun y => by
      induction y using ind_cls with
      | h v => exact cls_sound (by rw [pathSum_graft, pathSum_graft, h])))

/-- Multiplication of classes, induced by repetition. -/
def mulD : DepthClass α → DepthClass α → DepthClass α :=
  Quot.lift (fun w => Quot.lift (fun v => cls (repeatW w v))
      (fun v v' (h : pathSum v = pathSum v') => cls_sound (by
        rw [pathSum_repeatW, pathSum_repeatW, h])))
    (fun w w' (h : pathSum w = pathSum w') => funext (fun y => by
      induction y using ind_cls with
      | h v => exact cls_sound (by rw [pathSum_repeatW, pathSum_repeatW, h])))

/-- Zero: the class of the root (letter-free). -/
def zeroD : DepthClass α := cls []

/-- One: the class of a one-edge word (needs a letter; independent of it as a class). -/
def oneD (a : α) : DepthClass α := cls [a]

/-- Order transferred along `count`. -/
def LED (x y : DepthClass α) : Prop := PathLE (count x) (count y)

instance : Add (DepthClass α) := ⟨addD⟩
instance : Mul (DepthClass α) := ⟨mulD⟩

theorem cls_add (w v : Word α) : cls w + cls v = cls (graft w v) := rfl
theorem cls_mul (w v : Word α) : cls w * cls v = cls (repeatW w v) := rfl

/-! ### `count` is structure preserving -/

theorem count_zero : count (zeroD : DepthClass α) = zero := rfl

theorem count_one (a : α) : count (oneD a) = one := pathSum_rep a one

theorem count_add (x y : DepthClass α) : count (x + y) = count x + count y := by
  induction x using ind_cls with | h w => ?_
  induction y using ind_cls with | h v => ?_
  exact pathSum_graft w v

theorem count_mul (x y : DepthClass α) : count (x * y) = count x * count y := by
  induction x using ind_cls with | h w => ?_
  induction y using ind_cls with | h v => ?_
  exact pathSum_repeatW w v

theorem oneD_letter_indep (a b : α) : oneD a = oneD b :=
  count_injective (by rw [count_one, count_one])

/-! ### `realize` is structure preserving -/

theorem realize_zero (a : α) : realize a zero = zeroD := rfl

theorem realize_one (a : α) : realize a one = oneD a := rfl

theorem realize_add (a : α) (m n : TreeN) : realize a (m + n) = realize a m + realize a n :=
  count_injective (by rw [count_add, count_realize, count_realize, count_realize])

theorem realize_mul (a : α) (m n : TreeN) : realize a (m * n) = realize a m * realize a n :=
  count_injective (by rw [count_mul, count_realize, count_realize, count_realize])

theorem realize_le (a : α) (m n : TreeN) :
    (PathLE m n → LED (realize a m) (realize a n)) ∧
    (LED (realize a m) (realize a n) → PathLE m n) := by
  constructor
  · intro h
    show PathLE (count (realize a m)) (count (realize a n))
    rw [count_realize, count_realize]
    exact h
  · intro h
    have h' : PathLE (count (realize a m)) (count (realize a n)) := h
    rw [count_realize, count_realize] at h'
    exact h'

/-- The transferred order coincides with the intrinsic tree order "some word of the second class
extends some word of the first class by grafting". -/
theorem led_iff_graft (a : α) (x y : DepthClass α) :
    (LED x y → ∃ z, y = x + z) ∧ ((∃ z, y = x + z) → LED x y) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_of_le h
    exact ⟨realize a k, count_injective (by rw [count_add, count_realize, hk])⟩
  · intro ⟨z, hz⟩
    show PathLE (count x) (count y)
    rw [hz, count_add]
    exact le_add _ _

/-! ### Semiring laws on the quotient (transferred through `count`) -/

theorem add_assocD (x y z : DepthClass α) : x + y + z = x + (y + z) :=
  count_injective (by rw [count_add, count_add, count_add, count_add, add_assoc])

theorem add_commD (x y : DepthClass α) : x + y = y + x :=
  count_injective (by rw [count_add, count_add, add_comm])

theorem zero_addD (x : DepthClass α) : zeroD + x = x :=
  count_injective (by rw [count_add, count_zero]; rfl)

theorem mul_assocD (x y z : DepthClass α) : x * y * z = x * (y * z) :=
  count_injective (by rw [count_mul, count_mul, count_mul, count_mul, mul_assoc])

theorem mul_commD (x y : DepthClass α) : x * y = y * x :=
  count_injective (by rw [count_mul, count_mul, mul_comm])

theorem one_mulD (a : α) (x : DepthClass α) : oneD a * x = x :=
  count_injective (by rw [count_mul, count_one, one_mul])

theorem zero_mulD (x : DepthClass α) : zeroD * x = zeroD :=
  count_injective (by rw [count_mul, count_zero]; rfl)

theorem left_distribD (x y z : DepthClass α) : x * (y + z) = x * y + x * z :=
  count_injective (by rw [count_mul, count_add, count_add, count_mul, count_mul, left_distrib])

theorem add_left_cancelD {x y z : DepthClass α} (h : x + y = x + z) : y = z :=
  count_injective (TreeN.add_left_cancel (by rw [← count_add, ← count_add, h]))

/-- The commutative-semiring interface on the depth quotient, given a letter `a`. -/
def csr (a : α) : CSR (DepthClass α) where
  zero := zeroD
  one := oneD a
  add_assoc := add_assocD
  add_comm := add_commD
  zero_add := zero_addD
  mul_assoc := mul_assocD
  mul_comm := mul_commD
  one_mul := one_mulD a
  zero_mul := zero_mulD
  left_distrib := left_distribD

/-- An explicit isomorphism of ordered commutative semirings between `TreeN` and the depth
quotient over an alphabet with a supplied letter. -/
structure OrderedSemiringIso (α : Type) (a : α) where
  toFun : TreeN → DepthClass α
  invFun : DepthClass α → TreeN
  left_inv : ∀ n, invFun (toFun n) = n
  right_inv : ∀ x, toFun (invFun x) = x
  map_zero : toFun zero = zeroD
  map_one : toFun one = oneD a
  map_add : ∀ m n, toFun (m + n) = toFun m + toFun n
  map_mul : ∀ m n, toFun (m * n) = toFun m * toFun n
  map_le : ∀ m n, PathLE m n → LED (toFun m) (toFun n)
  reflect_le : ∀ m n, LED (toFun m) (toFun n) → PathLE m n

/-- **The depth quotient presentation of `TreeN`.** -/
def depthIso (a : α) : OrderedSemiringIso α a where
  toFun := realize a
  invFun := count
  left_inv := count_realize a
  right_inv := realize_count a
  map_zero := realize_zero a
  map_one := realize_one a
  map_add := realize_add a
  map_mul := realize_mul a
  map_le := fun m n => (realize_le a m n).1
  reflect_le := fun m n => (realize_le a m n).2

/-- Two letters give the same underlying map on counts (class-level letter independence). -/
theorem depthIso_letter_indep (a b : α) (n : TreeN) :
    (depthIso a).toFun n = (depthIso b).toFun n := realize_letter_indep a b n

/-! ## Degenerate alphabets -/

/-- Over the empty alphabet the only word is the root. -/
theorem empty_word_eq_root (w : Word Empty) : w = [] := by
  cases w with
  | nil => rfl
  | cons c _ => exact nomatch c

/-- More generally, over an alphabet without letters every word is the root. -/
theorem word_eq_root_of_noLetter (hα : α → False) (w : Word α) : w = [] := by
  cases w with
  | nil => rfl
  | cons c _ => exact (hα c).elim

/-- Over an alphabet without letters, every class has count zero ... -/
theorem count_eq_zero_of_noLetter (hα : α → False) (x : DepthClass α) : count x = zero := by
  induction x using ind_cls with | h w => ?_
  rw [word_eq_root_of_noLetter hα w]
  rfl

/-- ... so no positive path count is represented ... -/
theorem no_positive_count_of_noLetter (hα : α → False) (n : TreeN) :
    ¬ ∃ x : DepthClass α, count x = succ n := by
  intro ⟨x, hx⟩
  rw [count_eq_zero_of_noLetter hα x] at hx
  exact succ_ne_zero n hx.symm

/-- ... and the quotient is the single root class (the "singleton root" tree). -/
theorem eq_zeroD_of_noLetter (hα : α → False) (x : DepthClass α) : x = zeroD :=
  count_injective (count_eq_zero_of_noLetter hα x)

theorem empty_no_one : ¬ ∃ x : DepthClass Empty, count x = one :=
  no_positive_count_of_noLetter (fun c => nomatch c) zero

/-- Over the one-letter alphabet the relation identifies nothing: the depth quotient of `T₁`
is `T₁` itself (two unary words are related exactly when they are equal). -/
theorem unary_cls_eq_iff (w v : Word UnitChild) :
    (cls w = cls v → w = v) ∧ (w = v → cls w = cls v) := by
  constructor
  · intro h
    exact UnaryTree.count_unique ((cls_eq_iff w v).1 h)
  · intro h
    rw [h]

/-- On `T₁`, `count` of the class of a unary path is that very path. -/
theorem unary_count_cls (p : TreeN) : count (cls (α := UnitChild) p) = p :=
  UnaryTree.pathSum_self p

end DepthQuotient

end
