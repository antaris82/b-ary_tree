module

public import TreeNumbers.PathTriples
public import TreeNumbers.FieldInterface

@[expose] public section

/-!
# `TreeQ`: the rational field as a quotient of triple-path configurations

`TreeQ α` is the kernel quotient of the type `TriplePath α` of valid triple-path
configurations by the cross-multiplication relation `A·D' = A'·D`.

* `TreeQ (Child b)` for every finite arity `b` with at least two children;
* `TreeQOmega := TreeQ ChildOmega` for countable branching.

Operations are defined by constructing new triple-path witnesses (`TriplePath.ofFrac`) from
the derived cross-formulas and lifting to classes with explicit compatibility proofs.
-/

open TreeN (PathLT zero_lt_succ succ)
open TreeZ CSR CRing TriplePath

/-- The tree rationals over alphabet `α`: classes of triple-path configurations. -/
def TreeQ (α : Type) : Type := Quot (TriplePath.Rel (α := α))

/-- The tree rationals of the countably branching tree. -/
abbrev TreeQOmega : Type := TreeQ ChildOmega

namespace TreeQ

variable {α : Type}

/-- The class of a triple-path configuration. -/
def mk (t : TriplePath α) : TreeQ α := Quot.mk _ t

theorem sound {t t' : TriplePath α} (h : Rel t t') : mk t = mk t' := Quot.sound h

theorem ind_mk {motive : TreeQ α → Prop} (h : ∀ t, motive (mk t)) (x : TreeQ α) : motive x :=
  Quot.ind h x

/-! ## Exactness (without propositional extensionality), via a Boolean lift -/

/-- Boolean reflection of a locally constructed decision. -/
def boolOf {p : Prop} : Decidable p → Bool
  | isTrue _ => true
  | isFalse _ => false

theorem boolOf_congr {p q : Prop} (dp : Decidable p) (dq : Decidable q) (h1 : p → q)
    (h2 : q → p) : boolOf dp = boolOf dq := by
  cases dp with
  | isTrue hp =>
    cases dq with
    | isTrue _ => rfl
    | isFalse hq => exact absurd (h1 hp) hq
  | isFalse hp =>
    cases dq with
    | isTrue hq => exact absurd (h2 hq) hp
    | isFalse _ => rfl

theorem of_boolOf_true {p : Prop} (dp : Decidable p) (h : boolOf dp = true) : p := by
  cases dp with
  | isTrue hp => exact hp
  | isFalse _ => exact nomatch h

theorem boolOf_true_of {p : Prop} (dp : Decidable p) (h : p) : boolOf dp = true := by
  cases dp with
  | isTrue _ => rfl
  | isFalse hp => exact absurd h hp

/-- Boolean test "is related to `t`", lifted to classes. -/
def relTo (t : TriplePath α) : TreeQ α → Bool :=
  Quot.lift (fun s => boolOf (TreeZ.decEq (numer t * TreeZ.ofN (denom s))
      (numer s * TreeZ.ofN (denom t)))) (fun _ _ h =>
    boolOf_congr _ _ (fun h1 => rel_trans h1 h) (fun h1 => rel_trans h1 (rel_symm h)))

/-- Equal classes come from related configurations. -/
theorem exact {t t' : TriplePath α} (h : mk t = mk t') : Rel t t' := by
  have e : relTo t (mk t) = relTo t (mk t') := by rw [h]
  have e1 : relTo t (mk t) = true := boolOf_true_of _ (rel_refl t)
  rw [e1] at e
  exact of_boolOf_true _ e.symm

section Ops

variable [TwoLetters α]

/-- The class of the witness configuration of a fraction datum. -/
def ofF (f : Frac) : TreeQ α := mk (ofFrac f)

theorem ofF_sound {f g : Frac} (h : Frac.Eqv f g) : ofF (α := α) f = ofF g := by
  apply sound
  show Frac.Eqv (toFrac (ofFrac (α := α) f)) (toFrac (ofFrac (α := α) g))
  rw [toFrac_ofFrac, toFrac_ofFrac]
  exact h

theorem ofF_exact {f g : Frac} (h : ofF (α := α) f = ofF g) : Frac.Eqv f g := by
  have e : Frac.Eqv (toFrac (ofFrac (α := α) f)) (toFrac (ofFrac (α := α) g)) := exact h
  rw [toFrac_ofFrac, toFrac_ofFrac] at e
  exact e

theorem mk_eq_ofF (t : TriplePath α) : mk t = ofF (toFrac t) := by
  apply sound
  show Frac.Eqv (toFrac t) (toFrac (ofFrac (α := α) (toFrac t)))
  rw [toFrac_ofFrac]
  exact Frac.eqv_refl _

/-- Every class is the class of a witness configuration. -/
theorem ind_ofF {motive : TreeQ α → Prop} (h : ∀ f, motive (ofF f)) (x : TreeQ α) :
    motive x := by
  induction x using ind_mk with
  | h t =>
    rw [mk_eq_ofF]
    exact h _

/-- Lifting a compatible unary operation on fraction data. -/
def lift1 (g : Frac → Frac) (hg : ∀ f f', Frac.Eqv f f' → Frac.Eqv (g f) (g f')) :
    TreeQ α → TreeQ α :=
  Quot.lift (fun t => ofF (g (toFrac t))) (fun _ _ h => ofF_sound (hg _ _ h))

theorem lift1_ofF (g : Frac → Frac) (hg : ∀ f f', Frac.Eqv f f' → Frac.Eqv (g f) (g f'))
    (f : Frac) : lift1 (α := α) g hg (ofF f) = ofF (g f) := by
  show ofF (g (toFrac (ofFrac (α := α) f))) = ofF (g f)
  rw [toFrac_ofFrac]

/-- Lifting a compatible binary operation on fraction data. -/
def lift2 (g : Frac → Frac → Frac)
    (hg : ∀ f f' h h', Frac.Eqv f f' → Frac.Eqv h h' → Frac.Eqv (g f h) (g f' h')) :
    TreeQ α → TreeQ α → TreeQ α :=
  Quot.lift (fun t => lift1 (g (toFrac t)) (fun _ _ e => hg _ _ _ _ (Frac.eqv_refl _) e))
    (fun _ _ e => funext (fun y => by
      induction y using ind_mk with
      | h s => exact ofF_sound (hg _ _ _ _ e (Frac.eqv_refl _))))

theorem lift2_ofF (g : Frac → Frac → Frac)
    (hg : ∀ f f' h h', Frac.Eqv f f' → Frac.Eqv h h' → Frac.Eqv (g f h) (g f' h'))
    (f h : Frac) : lift2 (α := α) g hg (ofF f) (ofF h) = ofF (g f h) := by
  show ofF (g (toFrac (ofFrac (α := α) f)) (toFrac (ofFrac (α := α) h))) = ofF (g f h)
  rw [toFrac_ofFrac, toFrac_ofFrac]

def zeroQ : TreeQ α := ofF Frac.zero
def oneQ : TreeQ α := ofF Frac.one
def addQ : TreeQ α → TreeQ α → TreeQ α :=
  lift2 Frac.add (fun _ _ _ _ h1 h2 => Frac.add_resp h1 h2)
def mulQ : TreeQ α → TreeQ α → TreeQ α :=
  lift2 Frac.mul (fun _ _ _ _ h1 h2 => Frac.mul_resp h1 h2)
def negQ : TreeQ α → TreeQ α := lift1 Frac.neg (fun _ _ h => Frac.neg_resp h)
/-- Total inverse, with `inv 0 = 0`. -/
def invQ : TreeQ α → TreeQ α := lift1 Frac.inv (fun _ _ h => Frac.inv_resp h)

instance : Add (TreeQ α) := ⟨addQ⟩
instance : Mul (TreeQ α) := ⟨mulQ⟩
instance : Neg (TreeQ α) := ⟨negQ⟩

theorem add_ofF (f g : Frac) : ofF (α := α) f + ofF g = ofF (Frac.add f g) :=
  lift2_ofF Frac.add (fun _ _ _ _ h1 h2 => Frac.add_resp h1 h2) f g
theorem mul_ofF (f g : Frac) : ofF (α := α) f * ofF g = ofF (Frac.mul f g) :=
  lift2_ofF Frac.mul (fun _ _ _ _ h1 h2 => Frac.mul_resp h1 h2) f g
theorem neg_ofF (f : Frac) : -ofF (α := α) f = ofF (Frac.neg f) :=
  lift1_ofF Frac.neg (fun _ _ h => Frac.neg_resp h) f
theorem inv_ofF (f : Frac) : invQ (ofF (α := α) f) = ofF (Frac.inv f) :=
  lift1_ofF Frac.inv (fun _ _ h => Frac.inv_resp h) f

theorem add_comm' (x y : TreeQ α) : x + y = y + x := by
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  rw [add_ofF, add_ofF, Frac.add_comm]

theorem add_assoc' (x y z : TreeQ α) : x + y + z = x + (y + z) := by
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  induction z using ind_ofF with | h h => ?_
  rw [add_ofF, add_ofF, add_ofF, add_ofF, Frac.add_assoc]

theorem zero_add' (x : TreeQ α) : zeroQ + x = x := by
  induction x using ind_ofF with | h f => ?_
  show ofF Frac.zero + ofF f = ofF f
  rw [add_ofF, Frac.zero_add]

theorem neg_add_cancel' (x : TreeQ α) : -x + x = zeroQ := by
  induction x using ind_ofF with | h f => ?_
  rw [neg_ofF, add_ofF]
  exact ofF_sound (Frac.neg_add_cancel f)

theorem mul_comm' (x y : TreeQ α) : x * y = y * x := by
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  rw [mul_ofF, mul_ofF, Frac.mul_comm]

theorem mul_assoc' (x y z : TreeQ α) : x * y * z = x * (y * z) := by
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  induction z using ind_ofF with | h h => ?_
  rw [mul_ofF, mul_ofF, mul_ofF, mul_ofF, Frac.mul_assoc']

theorem one_mul' (x : TreeQ α) : oneQ * x = x := by
  induction x using ind_ofF with | h f => ?_
  show ofF Frac.one * ofF f = ofF f
  rw [mul_ofF, Frac.one_mul]

theorem zero_mul' (x : TreeQ α) : zeroQ * x = zeroQ := by
  induction x using ind_ofF with | h f => ?_
  show ofF Frac.zero * ofF f = ofF Frac.zero
  rw [mul_ofF]
  apply ofF_sound
  apply Frac.eqv_zero_of_num_eq_zero
  exact CSR.zero_mul _

theorem left_distrib' (x y z : TreeQ α) : x * (y + z) = x * y + x * z := by
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  induction z using ind_ofF with | h h => ?_
  rw [add_ofF, mul_ofF, mul_ofF, mul_ofF, add_ofF]
  exact ofF_sound (Frac.left_distrib f g h)

theorem zero_ne_one' : (zeroQ : TreeQ α) ≠ oneQ := fun h => Frac.zero_ne_one (ofF_exact h)

theorem num_ne_zero_of_ne {f : Frac} (h : ofF (α := α) f ≠ zeroQ) : f.num ≠ 𝟘 :=
  fun e => h (ofF_sound (Frac.eqv_zero_of_num_eq_zero e))

theorem mul_inv_cancel'' (x : TreeQ α) (hx : x ≠ zeroQ) : x * invQ x = oneQ := by
  revert hx
  induction x using ind_ofF with | h f => ?_
  intro hx
  rw [inv_ofF, mul_ofF]
  exact ofF_sound (Frac.mul_inv_cancel (num_ne_zero_of_ne hx))

/-- The convention `inv 0 = 0`, proved. -/
theorem inv_zero' : invQ (zeroQ : TreeQ α) = zeroQ := by
  show invQ (ofF Frac.zero) = ofF Frac.zero
  rw [inv_ofF, Frac.inv_of_num_zero rfl]

/-- `TreeQ α` populates the commutative-ring interface. -/
instance instCRing : CRing (TreeQ α) where
  zero := zeroQ
  one := oneQ
  add_assoc := add_assoc'
  add_comm := add_comm'
  zero_add := zero_add'
  mul_assoc := mul_assoc'
  mul_comm := mul_comm'
  one_mul := one_mul'
  zero_mul := zero_mul'
  left_distrib := left_distrib'
  neg_add_cancel := neg_add_cancel'

theorem natCast_eq (n : TreeN) :
    natCastWith (zeroQ : TreeQ α) oneQ (fun x y => x + y) n = ofF (Frac.ofTreeN n) := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    show oneQ + natCastWith zeroQ oneQ (fun x y => x + y) n = ofF (Frac.ofTreeN (c :: n))
    rw [ih]
    show ofF Frac.one + ofF (Frac.ofTreeN n) = ofF (Frac.ofTreeN (c :: n))
    rw [add_ofF]
    apply ofF_sound
    apply Frac.eqv_symm
    have e : c :: n = TreeN.one + n := by cases c; rfl
    rw [e]
    exact Frac.ofTreeN_add TreeN.one n

theorem charZero' (n : TreeN) :
    natCastWith (zeroQ : TreeQ α) oneQ (fun x y => x + y) (succ n) ≠ zeroQ := by
  rw [natCast_eq]
  exact fun h => Frac.ofTreeN_succ_ne_zero n (ofF_exact h)

/-- **`TreeQ α` is a field** (for every alphabet with two distinct letters). -/
instance instTField : TField (TreeQ α) where
  inv := invQ
  zero_ne_one := zero_ne_one'
  mul_inv_cancel := mul_inv_cancel''
  inv_zero := inv_zero'
  charZero := charZero'

/-! ## Correspondence between triple classes and fraction classes -/

omit [TwoLetters α] in
theorem mk_eq_mk_iff (t t' : TriplePath α) :
    (mk t = mk t' → Frac.Eqv (toFrac t) (toFrac t')) ∧
    (Frac.Eqv (toFrac t) (toFrac t') → mk t = mk t') :=
  ⟨exact, sound⟩

theorem ofF_eq_ofF_iff (f g : Frac) :
    (ofF (α := α) f = ofF g → Frac.Eqv f g) ∧ (Frac.Eqv f g → ofF (α := α) f = ofF g) :=
  ⟨ofF_exact, ofF_sound⟩

theorem exists_ofF (x : TreeQ α) : ∃ f : Frac, x = ofF f := by
  induction x using ind_ofF with
  | h f => exact ⟨f, rfl⟩

end Ops

end TreeQ

/-! ## The required instances -/

/-- The finite-arity tree rationals `TreeQ(b)`, for `b` with at least two children. -/
abbrev TreeQb (b : TreeN) : Type := TreeQ (Child b)

example (b : TreeN) [AtLeastTwo b] : TField (TreeQb b) := inferInstance
example : TField TreeQOmega := inferInstance

end
