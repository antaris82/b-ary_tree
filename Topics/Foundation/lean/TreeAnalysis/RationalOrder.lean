module

public import TreeNumbers.RationalArityIndependence
public import TreeAnalysis.OrderedField

@[expose] public section

/-!
# Checkpoint A1 — the derived order of the triple-path rational fields

On auxiliary fraction data `f = (a,d)`, `g = (c,e)` (positive path-count denominators) the
comparison is `a·e ≤ c·d` in the already constructed order of `TreeZ`.  It is invariant under
the cross-multiplication relation, hence descends to the quotient `TreeQ α` of valid
triple-path configurations.  The descent uses a Boolean reflection of the locally constructed
decision procedure (no propositional extensionality).

The result populates the ordered-field interface `TOField (TreeQ α)`, including an explicit
Archimedean bound function `archQ`, computed as the least path count above the class (a
canonical value, hence independent of the chosen triple).
-/

open TreeN (PathLT PathLE zero_lt_succ succ)
open TreeZ CSR CRing TriplePath TreeQ

namespace TreeZ

theorem ofN_pos_eq (k : TreeN) : (ofN k).pos = k := by
  cases k with
  | nil => rfl
  | cons c k => rfl

theorem not_nonNeg_neg_ofN {k : TreeN} (hk : PathLT TreeN.zero k) : ¬ NonNeg (-ofN k) := by
  intro h
  have h' : (ofN k).pos = TreeN.zero := h
  rw [ofN_pos_eq] at h'
  exact TreeN.ne_zero_of_pos hk h'

/-- Nonnegativity is detected after multiplication by a positive path count. -/
theorem nonNeg_of_mul_pos {x : TreeZ} {d : TreeN} (hd : PathLT TreeN.zero d)
    (h : NonNeg (x * ofN d)) : NonNeg x :=
  match sign x with
  | Sign.zero e => by rw [e]; rfl
  | Sign.pos n e => by rw [e]; exact nonNeg_ofN _
  | Sign.neg n e => by
    rw [e, neg_mul, ← ofN_mul] at h
    exact absurd h (not_nonNeg_neg_ofN (TreeN.mul_pos (zero_lt_succ n) hd))

theorem nonNeg_mul_pos {x : TreeZ} {d : TreeN} (h : NonNeg x) : NonNeg (x * ofN d) :=
  nonNeg_mul h (nonNeg_ofN d)

def decNonNeg (x : TreeZ) : Decidable (NonNeg x) := TreeN.decEq x.neg TreeN.zero

end TreeZ

namespace Frac

/-- Nonnegativity of fraction data: the numerator is nonnegative in `TreeZ`. -/
def NonNegF (f : Frac) : Prop := NonNeg f.num

/-- Comparison of fraction data by cross products in `TreeZ`: `a·e ≤ c·d`. -/
def LEF (f g : Frac) : Prop := TreeZ.LE (f.num * g.dz) (g.num * f.dz)

/-- Invariance of nonnegativity under the cross-multiplication relation. -/
theorem nonNegF_of_eqv {f g : Frac} (h : Eqv f g) (hf : NonNegF f) : NonNegF g := by
  unfold Eqv at h
  have h1 : NonNeg (f.num * g.dz) := nonNeg_mul_pos hf
  rw [h] at h1
  exact nonNeg_of_mul_pos f.pos h1

/-- Invariance of the cross-product comparison under the relation (first argument). -/
theorem lef_resp_left {f f' g : Frac} (h : Eqv f f') (hl : LEF f g) : LEF f' g := by
  unfold LEF TreeZ.LE at *
  apply nonNeg_of_mul_pos f.pos
  unfold Eqv at h
  have e : (g.num * f'.dz + -(f'.num * g.dz)) * f.dz
      = (g.num * f.dz + -(f.num * g.dz)) * f'.dz := by
    rw [CRing.sub_mul, CRing.sub_mul, mul_right_comm g.num f'.dz f.dz,
      mul_right_comm f'.num g.dz f.dz, ← h, mul_right_comm f.num f'.dz g.dz]
  rw [e]
  exact nonNeg_mul_pos hl

theorem lef_resp_right {f g g' : Frac} (h : Eqv g g') (hl : LEF f g) : LEF f g' := by
  unfold LEF TreeZ.LE at *
  apply nonNeg_of_mul_pos g.pos
  unfold Eqv at h
  have e : (g'.num * f.dz + -(f.num * g'.dz)) * g.dz
      = (g.num * f.dz + -(f.num * g.dz)) * g'.dz := by
    rw [CRing.sub_mul, CRing.sub_mul, mul_right_comm g'.num f.dz g.dz, ← h,
      mul_right_comm g.num g'.dz f.dz, mul_right_comm f.num g'.dz g.dz]
  rw [e]
  exact nonNeg_mul_pos hl

theorem nonNegF_iff_lef (f : Frac) : (NonNegF f → LEF zero f) ∧ (LEF zero f → NonNegF f) := by
  have e : f.num * zero.dz + -(zero.num * f.dz) = f.num := by
    show f.num * ofN TreeN.one + -(𝟘 * f.dz) = f.num
    rw [ofN_one, mul_one, zero_mul, neg_zero, add_zero]
  constructor
  · intro h
    show NonNeg (f.num * zero.dz + -(zero.num * f.dz))
    rw [e]
    exact h
  · intro h
    have h' : NonNeg (f.num * zero.dz + -(zero.num * f.dz)) := h
    rw [e] at h'
    exact h'

end Frac

namespace TreeQ

variable {α : Type}

/-! ## Nonnegativity on triple-path classes -/

/-- Boolean nonnegativity test, lifted to classes of triple-path configurations. -/
def nonnegB : TreeQ α → Bool :=
  Quot.lift (fun t => boolOf (TreeZ.decNonNeg (numer t)))
    (fun t t' h => boolOf_congr _ _
      (fun h1 => Frac.nonNegF_of_eqv (f := toFrac t) (g := toFrac t') h h1)
      (fun h1 => Frac.nonNegF_of_eqv (f := toFrac t') (g := toFrac t) (Frac.eqv_symm h) h1))

/-- Nonnegativity of a tree rational. -/
def NonnegQ (x : TreeQ α) : Prop := nonnegB x = true

def decNonnegQ (x : TreeQ α) : Decidable (NonnegQ x) := instDecidableEqBool _ _

/-- Raw invariance: related triples have the same sign behaviour. -/
theorem nonNeg_numer_of_rel {t t' : TriplePath α} (h : Rel t t') (ht : NonNeg (numer t)) :
    NonNeg (numer t') := Frac.nonNegF_of_eqv (f := toFrac t) (g := toFrac t') h ht

theorem nonnegQ_mk {t : TriplePath α} (h : NonNeg (numer t)) : NonnegQ (mk t) :=
  boolOf_true_of _ h

theorem nonNeg_of_nonnegQ_mk {t : TriplePath α} (h : NonnegQ (mk t)) : NonNeg (numer t) :=
  of_boolOf_true _ h

section Ops

variable [TwoLetters α]

theorem numer_ofFrac (f : Frac) : numer (ofFrac (α := α) f) = f.num := by
  have e := toFrac_ofFrac (α := α) f
  exact congrArg Frac.num e

theorem nonnegQ_ofF {f : Frac} (h : Frac.NonNegF f) : NonnegQ (ofF (α := α) f) := by
  apply nonnegQ_mk
  rw [numer_ofFrac]
  exact h

theorem nonNegF_of_nonnegQ {f : Frac} (h : NonnegQ (ofF (α := α) f)) : Frac.NonNegF f := by
  have h' := nonNeg_of_nonnegQ_mk h
  rw [numer_ofFrac] at h'
  exact h'

theorem nonnegQ_add (x y : TreeQ α) (hx : NonnegQ x) (hy : NonnegQ y) : NonnegQ (x + y) := by
  revert hx hy
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  intro hx hy
  rw [add_ofF]
  apply nonnegQ_ofF
  have hf := nonNegF_of_nonnegQ hx
  have hg := nonNegF_of_nonnegQ hy
  exact nonNeg_add (nonNeg_mul_pos hf) (nonNeg_mul_pos hg)

theorem nonnegQ_mul (x y : TreeQ α) (hx : NonnegQ x) (hy : NonnegQ y) : NonnegQ (x * y) := by
  revert hx hy
  induction x using ind_ofF with | h f => ?_
  induction y using ind_ofF with | h g => ?_
  intro hx hy
  rw [mul_ofF]
  apply nonnegQ_ofF
  exact nonNeg_mul (nonNegF_of_nonnegQ hx) (nonNegF_of_nonnegQ hy)

theorem nonnegQ_total (x : TreeQ α) : NonnegQ x ∨ NonnegQ (-x) := by
  induction x using ind_ofF with | h f => ?_
  rw [neg_ofF]
  cases nonNeg_or_neg_nonNeg f.num with
  | inl h => exact Or.inl (nonnegQ_ofF h)
  | inr h => exact Or.inr (nonnegQ_ofF (f := Frac.neg f) h)

theorem nonnegQ_antisymm (x : TreeQ α) (h1 : NonnegQ x) (h2 : NonnegQ (-x)) : x = zeroQ := by
  revert h1 h2
  induction x using ind_ofF with | h f => ?_
  intro h1 h2
  rw [neg_ofF] at h2
  have e := eq_zero_of_nonNeg_of_nonNeg_neg (nonNegF_of_nonnegQ h1)
    (nonNegF_of_nonnegQ (f := Frac.neg f) h2)
  exact ofF_sound (Frac.eqv_zero_of_num_eq_zero e)

/-! ## The Archimedean bound: least path count above a class -/

/-- First position (below a fuel bound) where a Boolean test succeeds; structural recursion. -/
def findFirst (p : TreeN → Bool) : TreeN → TreeN
  | [] => []
  | c :: f => cond (p (findFirst p f)) (findFirst p f) (c :: f)

theorem findFirst_spec (p : TreeN → Bool) (f : TreeN) :
    (∀ m, PathLT m (findFirst p f) → p m = false) ∧
    (p (findFirst p f) = true ∨ findFirst p f = f) := by
  induction f with
  | nil => exact ⟨fun m h => absurd h (TreeN.not_lt_zero m), Or.inr rfl⟩
  | cons c f ih =>
    show (∀ m, PathLT m (cond (p (findFirst p f)) (findFirst p f) (c :: f)) → p m = false) ∧
      (p (cond (p (findFirst p f)) (findFirst p f) (c :: f)) = true ∨
        cond (p (findFirst p f)) (findFirst p f) (c :: f) = c :: f)
    cases hp : p (findFirst p f) with
    | true => exact ⟨ih.1, Or.inl hp⟩
    | false =>
      refine ⟨fun m hm => ?_, Or.inr rfl⟩
      have hm' : PathLE m f := by
        cases c
        exact TreeN.le_of_lt_succ hm
      cases ih.2 with
      | inl ht => rw [hp] at ht; exact nomatch ht
      | inr he =>
        cases TreeN.eq_or_lt_of_le hm' with
        | inl e => rw [e, ← he]; exact hp
        | inr hl => exact ih.1 m (by rw [he]; exact hl)

theorem findFirst_true {p : TreeN → Bool} {f : TreeN} (h : p f = true) :
    p (findFirst p f) = true := by
  cases (findFirst_spec p f).2 with
  | inl h' => exact h'
  | inr e => rw [e]; exact h

/-- The least successful position does not depend on the fuel bound. -/
theorem findFirst_eq {p : TreeN → Bool} {f f' : TreeN} (h : p f = true) (h' : p f' = true) :
    findFirst p f = findFirst p f' := by
  have a := findFirst_true h
  have a' := findFirst_true h'
  match TreeN.compare (findFirst p f) (findFirst p f') with
  | TreeN.Trichotomy.eq e => exact e
  | TreeN.Trichotomy.lt hl =>
    have := (findFirst_spec p f').1 _ hl
    rw [a] at this
    exact nomatch this
  | TreeN.Trichotomy.gt hg =>
    have := (findFirst_spec p f).1 _ hg
    rw [a'] at this
    exact nomatch this

/-- Image of a path count in `TreeQ α`. -/
def natQ (n : TreeN) : TreeQ α := natCastWith zeroQ oneQ (fun a b => a + b) n

/-- The test "`x ≤ n`". -/
def archTest (x : TreeQ α) (n : TreeN) : Bool := nonnegB (natQ n + -x)

theorem natQ_eq (n : TreeN) : natQ (α := α) n = ofF (Frac.ofTreeN n) := natCast_eq n

theorem arch_aux (x : TreeZ) (d' : TreeN) :
    ofN x.pos * ofN (succ d') + -x * ofN TreeN.one = ofN (x.pos * d' + x.neg) := by
  have e1 : x = ofN x.pos + -ofN x.neg := by rw [← mkZ_eq_sub, mkZ_self]
  have e3 : -x = -ofN x.pos + ofN x.neg :=
    (congrArg Neg.neg e1).trans (by rw [neg_add, neg_neg])
  rw [ofN_one, mul_one, e3, ← ofN_mul, TreeN.mul_succ, ofN_add, ofN_add,
    add_comm (ofN x.pos) (ofN (x.pos * d')), add_assoc, ← add_assoc (ofN x.pos) (-ofN x.pos),
    add_neg_cancel, zero_add]

/-- Every fraction lies below the positive part of its numerator. -/
theorem archTest_fuel (f : Frac) : archTest (ofF (α := α) f) f.num.pos = true := by
  show NonnegQ (natQ f.num.pos + -ofF f)
  rw [natQ_eq, neg_ofF, add_ofF]
  apply nonnegQ_ofF
  · show NonNeg ((Frac.add (Frac.ofTreeN f.num.pos) (Frac.neg f)).num)
    show NonNeg (ofN f.num.pos * ofN f.den + -f.num * ofN TreeN.one)
    obtain ⟨d', hd⟩ := TreeN.pos_iff_succ f.pos
    rw [hd]
    have e2 := arch_aux f.num d'
    rw [e2]
    exact nonNeg_ofN _

/-- The Archimedean bound of a raw configuration. -/
def archRaw (t : TriplePath α) : TreeN := findFirst (archTest (mk t)) (numer t).pos

theorem archTest_raw (t : TriplePath α) : archTest (mk t) (numer t).pos = true := by
  have h := archTest_fuel (α := α) (toFrac t)
  rw [← mk_eq_ofF] at h
  exact h

/-- The Archimedean bound on classes: the least path count `n` with `x ≤ n`. -/
def archQ : TreeQ α → TreeN :=
  Quot.lift archRaw (fun t t' h => by
    have e : mk t = mk t' := sound h
    unfold archRaw
    rw [e]
    have h1 := archTest_raw t
    rw [e] at h1
    exact findFirst_eq h1 (archTest_raw t'))

theorem archQ_spec (x : TreeQ α) : NonnegQ (natQ (archQ x) + -x) := by
  induction x using ind_mk with | h t => ?_
  exact findFirst_true (archTest_raw t)

/-! ## The ordered-field instance -/

/-- **`TreeQ α` is an ordered field** (Archimedean, with decidable order), for every alphabet
with two distinct letters. -/
instance instTOField : TOField (TreeQ α) where
  toTField := instTField
  Nonneg := NonnegQ
  decNonneg := decNonnegQ
  nonneg_add := nonnegQ_add
  nonneg_mul := nonnegQ_mul
  nonneg_total := nonnegQ_total
  nonneg_antisymm := nonnegQ_antisymm
  archBound := archQ
  arch_spec := archQ_spec

/-! ## Agreement with the cross-product comparison and the embeddings -/

open TOField TField

/-- The derived order on classes is the cross-product comparison `a·e ≤ c·d` of `TreeZ`. -/
theorem le_ofF_of_lef {f g : Frac} (h : Frac.LEF f g) : ofF (α := α) f ≤ ofF g := by
  show NonnegQ (ofF g + -ofF f)
  rw [neg_ofF, add_ofF]
  apply nonnegQ_ofF
  show NonNeg (g.num * f.dz + -f.num * g.dz)
  rw [neg_mul]
  exact h

theorem lef_of_le_ofF {f g : Frac} (h : ofF (α := α) f ≤ ofF g) : Frac.LEF f g := by
  have h' : NonnegQ (ofF (α := α) g + -ofF f) := h
  rw [neg_ofF, add_ofF] at h'
  have h2 : NonNeg (g.num * f.dz + -f.num * g.dz) := nonNegF_of_nonnegQ h'
  rw [neg_mul] at h2
  exact h2

/-- Embedding of tree integers into `TreeQ α` (denominator one). -/
def ofZ (z : TreeZ) : TreeQ α := ofF ⟨z, TreeN.one, zero_lt_succ TreeN.zero⟩

theorem ofZ_le {z z' : TreeZ} (h : TreeZ.LE z z') : ofZ (α := α) z ≤ ofZ z' := by
  apply le_ofF_of_lef
  show TreeZ.LE (z * ofN TreeN.one) (z' * ofN TreeN.one)
  rw [ofN_one, mul_one, mul_one]
  exact h

theorem le_of_ofZ_le {z z' : TreeZ} (h : ofZ (α := α) z ≤ ofZ z') : TreeZ.LE z z' := by
  have h' := lef_of_le_ofF h
  have h'' : TreeZ.LE (z * ofN TreeN.one) (z' * ofN TreeN.one) := h'
  rw [ofN_one, mul_one, mul_one] at h''
  exact h''

theorem ofZ_add (z z' : TreeZ) : ofZ (α := α) (z + z') = ofZ z + ofZ z' := by
  unfold ofZ
  rw [add_ofF]
  apply ofF_sound
  show (z + z') * ofN (TreeN.one * TreeN.one) = (z * ofN TreeN.one + z' * ofN TreeN.one) * ofN TreeN.one
  rw [ofN_one, TreeN.one_mul, ofN_one, mul_one, mul_one, mul_one, mul_one]

theorem ofZ_mul (z z' : TreeZ) : ofZ (α := α) (z * z') = ofZ z * ofZ z' := by
  unfold ofZ
  rw [mul_ofF]
  apply ofF_sound
  show z * z' * ofN (TreeN.one * TreeN.one) = z * z' * ofN TreeN.one
  rw [TreeN.one_mul]

theorem ofZ_injective {z z' : TreeZ} (h : ofZ (α := α) z = ofZ z') : z = z' := by
  have h' := ofF_exact h
  have h'' : z * ofN TreeN.one = z' * ofN TreeN.one := h'
  rw [ofN_one, mul_one, mul_one] at h''
  exact h''

/-- The image of path counts in `TreeQ α` is `ofZ ∘ ofN`. -/
theorem natCast_eq_ofZ (n : TreeN) : natCast (K := TreeQ α) n = ofZ (ofN n) := natCast_eq n

/-- Agreement with the order of `TreeN`. -/
theorem pathLE_of_natCast_le {m n : TreeN} (h : natCast (K := TreeQ α) m ≤ natCast n) :
    PathLE m n := by
  cases TreeN.le_or_lt m n with
  | inl h' => exact h'
  | inr h' => exact absurd h (natCast_lt h')

end Ops

end TreeQ

/-- The fixed rational base carrier `Q★` of the completion: the omega-branching tree rationals. -/
abbrev QStar : Type := TreeQOmega

example : TOField QStar := inferInstance

end
