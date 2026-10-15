module

public import TreeAnalysis.Canonicity

@[expose] public section

/-!
# `TreeQ α` versus the internal fraction quotient `FracQ`

`TreeQ α` is, and remains, the quotient of valid triples of pairwise distinct root paths.  The
numerator and denominator of a triple (`TriplePath.numer`, `TriplePath.denom`) are computed from
the three unit-edge sums only.  This module makes the consequence explicit:

* `mk_eq_of_pathSum_eq`: two triples with corresponding equal path sums have the same class
  (the triples themselves, as addresses, may differ);
* `FracQ := Quot Frac.Eqv` is the *auxiliary* fraction quotient built only from `TreeZ` and
  positive `TreeN` (no standard rationals); it carries its own operations, lifted from the
  existing `Frac` operations, and its own field laws (`FracQ.instTField`) — so a field is
  obtained from unary-path counts by the general fraction construction;
* `toFracQ : TreeQ α → FracQ` (induced by `TriplePath.toFrac`) and `ofFracQ : FracQ → TreeQ α`
  (induced by the witness construction `TreeQ.ofF`) are mutually inverse and preserve `0, 1,
  +, -, ·, inv` (with `inv 0 = 0` on both sides) and the order in both directions
  (`orderedFieldIsoFracQ`);
* `ofFracQ` does not depend on the choice of the two witness letters (class level), whereas the
  representative triple does (`TreeQ.ofFrac_letter_dependent`);
* coherence with `transfer`, `arityIso`, `fieldIso_unique` and `realArityIso`.

The branching hypothesis `[TwoLetters α]` is used only for the **existence** of witness
configurations; the arithmetic is determined by signed path-count differences and
cross-multiplication.
-/

open CSR CRing TreeZ TOField TField TriplePath TreeQ

/-! ## Classes depend only on the three path sums -/

namespace TreeQ

variable {α : Type}

theorem numer_eq_of_pathSum_eq {t t' : TriplePath α} (h1 : Word.pathSum t.p1 = Word.pathSum t'.p1)
    (h2 : Word.pathSum t.p2 = Word.pathSum t'.p2) : numer t = numer t' := by
  unfold numer
  rw [h1, h2]

theorem denom_eq_of_pathSum_eq {t t' : TriplePath α} (h2 : Word.pathSum t.p2 = Word.pathSum t'.p2)
    (h3 : Word.pathSum t.p3 = Word.pathSum t'.p3) : denom t = denom t' := by
  unfold denom
  rw [h2, h3]

/-- **Two valid triples with corresponding equal path sums have equal classes.**  This is a
statement about classes, not about the addresses. -/
theorem mk_eq_of_pathSum_eq {t t' : TriplePath α} (h1 : Word.pathSum t.p1 = Word.pathSum t'.p1)
    (h2 : Word.pathSum t.p2 = Word.pathSum t'.p2) (h3 : Word.pathSum t.p3 = Word.pathSum t'.p3) :
    mk t = mk t' := by
  apply sound
  show numer t * ofN (denom t') = numer t' * ofN (denom t)
  rw [numer_eq_of_pathSum_eq h1 h2, denom_eq_of_pathSum_eq h2 h3]

/-- The same statement phrased through depths. -/
theorem mk_eq_of_depth_eq {t t' : TriplePath α} (h1 : Word.depth t.p1 = Word.depth t'.p1)
    (h2 : Word.depth t.p2 = Word.depth t'.p2) (h3 : Word.depth t.p3 = Word.depth t'.p3) :
    mk t = mk t' := by
  apply mk_eq_of_pathSum_eq
  · rw [Word.pathSum_eq_depth, Word.pathSum_eq_depth, h1]
  · rw [Word.pathSum_eq_depth, Word.pathSum_eq_depth, h2]
  · rw [Word.pathSum_eq_depth, Word.pathSum_eq_depth, h3]

end TreeQ

/-! ## The auxiliary fraction quotient -/

/-- The internal fraction quotient: classes of `(TreeZ, positive TreeN)` data. -/
def FracQ : Type := Quot Frac.Eqv

namespace FracQ

def mk (f : Frac) : FracQ := Quot.mk _ f

theorem sound {f g : Frac} (h : Frac.Eqv f g) : mk f = mk g := Quot.sound h

theorem ind_mk {motive : FracQ → Prop} (h : ∀ f, motive (mk f)) (x : FracQ) : motive x :=
  Quot.ind h x

/-- Boolean test "related to `f`", lifted to classes (used for exactness without `propext`). -/
def relTo (f : Frac) : FracQ → Bool :=
  Quot.lift (fun g => boolOf (TreeZ.decEq (f.num * g.dz) (g.num * f.dz)))
    (fun _ _ h => boolOf_congr _ _ (fun h1 => Frac.eqv_trans h1 h)
      (fun h1 => Frac.eqv_trans h1 (Frac.eqv_symm h)))

theorem exact {f g : Frac} (h : mk f = mk g) : Frac.Eqv f g := by
  have e : relTo f (mk f) = relTo f (mk g) := by rw [h]
  have e1 : relTo f (mk f) = true := boolOf_true_of _ (Frac.eqv_refl f)
  rw [e1] at e
  exact of_boolOf_true _ e.symm

def lift1 (g : Frac → Frac) (hg : ∀ f f', Frac.Eqv f f' → Frac.Eqv (g f) (g f')) :
    FracQ → FracQ :=
  Quot.lift (fun f => mk (g f)) (fun _ _ h => sound (hg _ _ h))

def lift2 (g : Frac → Frac → Frac)
    (hg : ∀ f f' h h', Frac.Eqv f f' → Frac.Eqv h h' → Frac.Eqv (g f h) (g f' h')) :
    FracQ → FracQ → FracQ :=
  Quot.lift (fun f => lift1 (g f) (fun _ _ e => hg _ _ _ _ (Frac.eqv_refl _) e))
    (fun _ _ e => funext (fun y => by
      induction y using ind_mk with
      | h s => exact sound (hg _ _ _ _ e (Frac.eqv_refl _))))

def zeroF : FracQ := mk Frac.zero
def oneF : FracQ := mk Frac.one
def addF : FracQ → FracQ → FracQ := lift2 Frac.add (fun _ _ _ _ h1 h2 => Frac.add_resp h1 h2)
def mulF : FracQ → FracQ → FracQ := lift2 Frac.mul (fun _ _ _ _ h1 h2 => Frac.mul_resp h1 h2)
def negF : FracQ → FracQ := lift1 Frac.neg (fun _ _ h => Frac.neg_resp h)
/-- Total inverse with `inv 0 = 0`, lifted from `Frac.inv`. -/
def invF : FracQ → FracQ := lift1 Frac.inv (fun _ _ h => Frac.inv_resp h)

instance : Add FracQ := ⟨addF⟩
instance : Mul FracQ := ⟨mulF⟩
instance : Neg FracQ := ⟨negF⟩

theorem add_mk (f g : Frac) : mk f + mk g = mk (Frac.add f g) := rfl
theorem mul_mk (f g : Frac) : mk f * mk g = mk (Frac.mul f g) := rfl
theorem neg_mk (f : Frac) : -mk f = mk (Frac.neg f) := rfl
theorem inv_mk (f : Frac) : invF (mk f) = mk (Frac.inv f) := rfl

/-- The order on fraction classes: some representatives satisfy the cross-product comparison. -/
def LEF (x y : FracQ) : Prop := ∃ f g, x = mk f ∧ y = mk g ∧ Frac.LEF f g

theorem lef_mk_iff (f g : Frac) : (LEF (mk f) (mk g) → Frac.LEF f g) ∧
    (Frac.LEF f g → LEF (mk f) (mk g)) := by
  constructor
  · intro ⟨f', g', hf, hg, h⟩
    exact Frac.lef_resp_right (Frac.eqv_symm (exact hg))
      (Frac.lef_resp_left (Frac.eqv_symm (exact hf)) h)
  · intro h
    exact ⟨f, g, rfl, rfl, h⟩

/-! ### Field laws of `FracQ` (proved directly from the `Frac` laws) -/

theorem add_comm' (x y : FracQ) : x + y = y + x := by
  induction x using ind_mk with | h f => ?_
  induction y using ind_mk with | h g => ?_
  rw [add_mk, add_mk, Frac.add_comm]

theorem add_assoc' (x y z : FracQ) : x + y + z = x + (y + z) := by
  induction x using ind_mk with | h f => ?_
  induction y using ind_mk with | h g => ?_
  induction z using ind_mk with | h h => ?_
  rw [add_mk, add_mk, add_mk, add_mk, Frac.add_assoc]

theorem zero_add' (x : FracQ) : zeroF + x = x := by
  induction x using ind_mk with | h f => ?_
  show mk Frac.zero + mk f = mk f
  rw [add_mk, Frac.zero_add]

theorem neg_add_cancel' (x : FracQ) : -x + x = zeroF := by
  induction x using ind_mk with | h f => ?_
  rw [neg_mk, add_mk]
  exact sound (Frac.neg_add_cancel f)

theorem mul_comm' (x y : FracQ) : x * y = y * x := by
  induction x using ind_mk with | h f => ?_
  induction y using ind_mk with | h g => ?_
  rw [mul_mk, mul_mk, Frac.mul_comm]

theorem mul_assoc' (x y z : FracQ) : x * y * z = x * (y * z) := by
  induction x using ind_mk with | h f => ?_
  induction y using ind_mk with | h g => ?_
  induction z using ind_mk with | h h => ?_
  rw [mul_mk, mul_mk, mul_mk, mul_mk, Frac.mul_assoc']

theorem one_mul' (x : FracQ) : oneF * x = x := by
  induction x using ind_mk with | h f => ?_
  show mk Frac.one * mk f = mk f
  rw [mul_mk, Frac.one_mul]

theorem zero_mul' (x : FracQ) : zeroF * x = zeroF := by
  induction x using ind_mk with | h f => ?_
  show mk Frac.zero * mk f = mk Frac.zero
  rw [mul_mk]
  apply sound
  apply Frac.eqv_zero_of_num_eq_zero
  exact CSR.zero_mul _

theorem left_distrib' (x y z : FracQ) : x * (y + z) = x * y + x * z := by
  induction x using ind_mk with | h f => ?_
  induction y using ind_mk with | h g => ?_
  induction z using ind_mk with | h h => ?_
  rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk]
  exact sound (Frac.left_distrib f g h)

theorem zero_ne_one' : zeroF ≠ oneF := fun h => Frac.zero_ne_one (exact h)

theorem mul_inv_cancel'' (x : FracQ) (hx : x ≠ zeroF) : x * invF x = oneF := by
  revert hx
  induction x using ind_mk with | h f => ?_
  intro hx
  rw [inv_mk, mul_mk]
  exact sound (Frac.mul_inv_cancel (fun e => hx (sound (Frac.eqv_zero_of_num_eq_zero e))))

theorem inv_zero' : invF zeroF = zeroF := by
  show mk (Frac.inv Frac.zero) = mk Frac.zero
  rw [Frac.inv_of_num_zero rfl]

instance instCRing : CRing FracQ where
  zero := zeroF
  one := oneF
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
    natCastWith zeroF oneF (fun x y => x + y) n = mk (Frac.ofTreeN n) := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    show oneF + natCastWith zeroF oneF (fun x y => x + y) n = mk (Frac.ofTreeN (c :: n))
    rw [ih]
    show mk Frac.one + mk (Frac.ofTreeN n) = mk (Frac.ofTreeN (c :: n))
    rw [add_mk]
    apply sound
    apply Frac.eqv_symm
    have e : c :: n = TreeN.one + n := by cases c; rfl
    rw [e]
    exact Frac.ofTreeN_add TreeN.one n

theorem charZero' (n : TreeN) :
    natCastWith zeroF oneF (fun x y => x + y) (TreeN.succ n) ≠ zeroF := by
  rw [natCast_eq]
  exact fun h => Frac.ofTreeN_succ_ne_zero n (exact h)

/-- **The fraction construction over unary-path counts is a field** (characteristic zero, with
`inv 0 = 0`).  No alphabet and no triple of addresses is involved. -/
instance instTField : TField FracQ where
  inv := invF
  zero_ne_one := zero_ne_one'
  mul_inv_cancel := mul_inv_cancel''
  inv_zero := inv_zero'
  charZero := charZero'

end FracQ

/-! ## The comparison maps `TreeQ α ⇄ FracQ` -/

namespace TreeQ

variable {α β : Type}

/-- Fraction class of a triple-path class (no letters needed). -/
def toFracQ : TreeQ α → FracQ := Quot.lift (fun t => FracQ.mk (toFrac t)) (fun _ _ h => FracQ.sound h)

theorem toFracQ_mk (t : TriplePath α) : toFracQ (mk t) = FracQ.mk (toFrac t) := rfl

/-- The fraction class only sees path sums: the map is injective on classes. -/
theorem toFracQ_injective {x y : TreeQ α} (h : toFracQ x = toFracQ y) : x = y := by
  revert h
  induction x using ind_mk with | h t => ?_
  induction y using ind_mk with | h s => ?_
  intro h
  exact sound (FracQ.exact h)

section Letters

variable [TwoLetters α]

/-- Triple-path class of a fraction class, through the universal witness construction. -/
def ofFracQ : FracQ → TreeQ α := Quot.lift ofF (fun _ _ h => ofF_sound h)

theorem ofFracQ_mk (f : Frac) : ofFracQ (α := α) (FracQ.mk f) = ofF f := rfl

theorem toFracQ_ofF (f : Frac) : toFracQ (ofF (α := α) f) = FracQ.mk f := by
  show FracQ.mk (toFrac (ofFrac (α := α) f)) = FracQ.mk f
  rw [toFrac_ofFrac]

theorem ofFracQ_toFracQ (x : TreeQ α) : ofFracQ (toFracQ x) = x := by
  induction x using ind_mk with
  | h t => exact (mk_eq_ofF t).symm

theorem toFracQ_ofFracQ (y : FracQ) : toFracQ (ofFracQ (α := α) y) = y := by
  induction y using FracQ.ind_mk with
  | h f => exact toFracQ_ofF f

theorem toFracQ_zero : toFracQ (𝟘 : TreeQ α) = 𝟘 := toFracQ_ofF Frac.zero

theorem toFracQ_one : toFracQ (𝟙 : TreeQ α) = 𝟙 := toFracQ_ofF Frac.one

theorem toFracQ_add (x y : TreeQ α) : toFracQ (x + y) = toFracQ x + toFracQ y := by
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  rw [add_ofF, toFracQ_ofF, toFracQ_ofF, toFracQ_ofF]
  rfl

theorem toFracQ_mul (x y : TreeQ α) : toFracQ (x * y) = toFracQ x * toFracQ y := by
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  rw [mul_ofF, toFracQ_ofF, toFracQ_ofF, toFracQ_ofF]
  rfl

theorem toFracQ_neg (x : TreeQ α) : toFracQ (-x) = -toFracQ x := by
  induction x using ind_ofF with | h f => ?_
  rw [neg_ofF, toFracQ_ofF, toFracQ_ofF]
  rfl

/-- Inversion is preserved, including the convention `inv 0 = 0` on both sides. -/
theorem toFracQ_inv (x : TreeQ α) : toFracQ (TField.inv x) = TField.inv (toFracQ x) := by
  induction x using ind_ofF with | h f => ?_
  show toFracQ (invQ (ofF f)) = FracQ.invF (toFracQ (ofF f))
  rw [inv_ofF, toFracQ_ofF, toFracQ_ofF]
  rfl

theorem toFracQ_inv_zero : toFracQ (TField.inv (𝟘 : TreeQ α)) = 𝟘 := by
  rw [toFracQ_inv, toFracQ_zero]
  exact FracQ.inv_zero'

/-- The order is preserved ... -/
theorem toFracQ_le {x y : TreeQ α} (h : x ≤ y) : FracQ.LEF (toFracQ x) (toFracQ y) := by
  revert h
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  intro h
  rw [toFracQ_ofF, toFracQ_ofF]
  exact (FracQ.lef_mk_iff f g).2 (lef_of_le_ofF h)

/-- ... and reflected. -/
theorem le_of_toFracQ_le {x y : TreeQ α} (h : FracQ.LEF (toFracQ x) (toFracQ y)) : x ≤ y := by
  revert h
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  intro h
  rw [toFracQ_ofF, toFracQ_ofF] at h
  exact le_ofF_of_lef ((FracQ.lef_mk_iff f g).1 h)

/-- An isomorphism of ordered fields between two field-interface instances, with the order on the
target given by an explicit relation. -/
structure OrderedFieldIso (K L : Type) [TOField K] [TField L] (LEL : L → L → Prop) where
  toFieldIso : FieldIso K L
  map_le : ∀ x y : K, x ≤ y → LEL (toFieldIso.toFun x) (toFieldIso.toFun y)
  reflect_le : ∀ x y : K, LEL (toFieldIso.toFun x) (toFieldIso.toFun y) → x ≤ y

/-- **Ordered-field isomorphism `TreeQ α ≅ FracQ`.** -/
def orderedFieldIsoFracQ (α : Type) [TwoLetters α] :
    OrderedFieldIso (TreeQ α) FracQ FracQ.LEF where
  toFieldIso :=
    { toFun := toFracQ
      invFun := ofFracQ
      left_inv := ofFracQ_toFracQ
      right_inv := toFracQ_ofFracQ
      map_zero := toFracQ_zero
      map_one := toFracQ_one
      map_add := toFracQ_add
      map_mul := toFracQ_mul
      map_neg := toFracQ_neg
      map_inv := toFracQ_inv }
  map_le := fun _ _ h => toFracQ_le h
  reflect_le := fun _ _ h => le_of_toFracQ_le h

/-- The strict order is preserved and reflected as well (`<` is `¬ ≥` on both sides). -/
theorem lt_iff_toFracQ (x y : TreeQ α) :
    (x < y → ¬ FracQ.LEF (toFracQ y) (toFracQ x)) ∧
    (¬ FracQ.LEF (toFracQ y) (toFracQ x) → x < y) :=
  ⟨fun h h' => h (le_of_toFracQ_le h'), fun h h' => h (toFracQ_le h')⟩

end Letters

/-! ### Letter independence and coherence -/

/-- `ofFracQ` does not depend on the two chosen witness letters (class level). -/
theorem ofFracQ_letter_indep (I J : TwoLetters α) (y : FracQ) :
    @ofFracQ α I y = @ofFracQ α J y := by
  induction y using FracQ.ind_mk with
  | h f => exact ofF_letter_indep I J f

/-- `toFracQ` commutes with the arity comparison maps. -/
theorem toFracQ_transfer [TwoLetters β] (x : TreeQ α) : toFracQ (transfer α β x) = toFracQ x := by
  induction x using ind_mk with
  | h t => exact toFracQ_ofF (toFrac t)

/-- Every field isomorphism `TreeQ α ≅ TreeQ β` is compatible with the fraction presentation. -/
theorem toFracQ_fieldIso [TwoLetters α] [TwoLetters β] (φ : FieldIso (TreeQ α) (TreeQ β))
    (x : TreeQ α) : toFracQ (φ.toFun x) = toFracQ x := by
  rw [fieldIso_unique φ, toFracQ_transfer]

/-- The comparison map factors through `FracQ`. -/
theorem transfer_eq_ofFracQ_toFracQ [TwoLetters β] (x : TreeQ α) :
    transfer α β x = ofFracQ (toFracQ x) := by
  induction x using ind_mk with
  | h t => rfl

/-- `arityIso` corresponds, under the fraction presentation, to the identity of `FracQ`. -/
theorem arityIso_fracQ [TwoLetters α] [TwoLetters β] (y : FracQ) :
    (arityIso α β).toFun (ofFracQ y) = ofFracQ y := by
  induction y using FracQ.ind_mk with
  | h f => exact transfer_ofF f

end TreeQ

namespace TreeR

open TreeQ

variable {α β : Type} [TwoLetters α] [TwoLetters β]

/-- Coherence with the completions: `realArityIso` sends the image of a fraction class to the image
of the same fraction class. -/
theorem realArityIso_ofFracQ (y : FracQ) :
    (realArityIso α β).toFun (ofQ (ofFracQ (α := α) y)) = ofQ (ofFracQ (α := β) y) := by
  rw [realArityIso_ofQ, transfer_eq_ofFracQ_toFracQ, toFracQ_ofFracQ]

/-- Every order-preserving ring isomorphism of the completions acts as the identity on fraction
classes. -/
theorem realIso_ofFracQ (φ : RealIso (TreeR (TreeQ α)) (TreeR (TreeQ β))) (y : FracQ) :
    φ.toFun (ofQ (ofFracQ (α := α) y)) = ofQ (ofFracQ (α := β) y) := by
  rw [realIso_unique φ, realArityIso_ofFracQ]

end TreeR

/-! ## Correct scope of the unary obstruction -/

namespace TriplePath

/-- Over the one-letter alphabet the **pairwise-distinct triple presentation** cannot represent
the zero numerator, so `toFracQ` is not surjective there ... -/
theorem unary_toFracQ_ne_zero (x : TreeQ UnitChild) : toFracQ x ≠ (𝟘 : FracQ) := by
  induction x using TreeQ.ind_mk with | h t => ?_
  intro h
  apply unary_numer_ne_zero t
  exact Frac.num_eq_zero_of_eqv_zero (FracQ.exact h)

/-- ... while the general fraction construction over the same unary-path counts is a field: the
obstruction concerns the triple presentation, not fraction fields over unary counts. -/
theorem unary_obstruction_scope :
    (∀ x : TreeQ UnitChild, toFracQ x ≠ (𝟘 : FracQ)) ∧ (𝟘 : FracQ) ≠ 𝟙 ∧
    (∀ y : FracQ, y ≠ 𝟘 → y * TField.inv y = 𝟙) :=
  ⟨unary_toFracQ_ne_zero, TField.zero_ne_one, TField.mul_inv_cancel⟩

end TriplePath

end
