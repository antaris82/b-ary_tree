module

public import TreeNumbers.FieldInterface

@[expose] public section

/-!
# Ordered-field interface and its derived laws

`TOField K` is a typeclass *specification* with law fields (not kernel axioms; every instance
must prove them): a field in the sense of the project's
`TField`, together with a nonnegativity predicate that is **decidable by a supplied
procedure**, closed under addition and multiplication, total and antisymmetric, and an
explicit Archimedean bound function with values in the tree-path counts `TreeN`.

In this project the interface is populated only by the triple-path rational fields `TreeQ`
(see `TreeAnalysis/RationalOrder`).  Everything below is derived from the interface laws by
explicit rewriting; no outside ordered-field theory is used.

* `x ≤ y` is `Nonneg (y - x)`;  `x < y` is `¬ (y ≤ x)` (a decidable, total order);
* `abs`, the triangle inequality, multiplicativity of `abs`, positivity of inverses,
  monotonicity of the image of path counts.
-/

open CSR CRing

/-- Ordered field interface (populated only by the project's rational fields). -/
class TOField (K : Type) extends TField K where
  Nonneg : K → Prop
  decNonneg : (x : K) → Decidable (Nonneg x)
  nonneg_add : ∀ x y : K, Nonneg x → Nonneg y → Nonneg (x + y)
  nonneg_mul : ∀ x y : K, Nonneg x → Nonneg y → Nonneg (x * y)
  nonneg_total : ∀ x : K, Nonneg x ∨ Nonneg (-x)
  nonneg_antisymm : ∀ x : K, Nonneg x → Nonneg (-x) → x = zero
  /-- An explicit Archimedean bound (data, not a mere existence statement). -/
  archBound : K → TreeN
  arch_spec : ∀ x : K, Nonneg (natCastWith zero one (fun a b => a + b) (archBound x) + -x)

namespace CRing

variable {α : Type} [CRing α]

theorem neg_sub' (x y : α) : -(y + -x) = x + -y := by
  rw [neg_add, neg_neg, add_comm]

theorem sub_add_sub (x y z : α) : (x + -y) + (y + -z) = x + -z := by
  rw [add_assoc, ← add_assoc (-y), neg_add_cancel, zero_add]

theorem add_sub_cancel_right (x y : α) : x + y + -y = x := by
  rw [add_assoc, add_neg_cancel, add_zero]

theorem sub_self (x : α) : x + -x = 𝟘 := add_neg_cancel x

theorem eq_add_of_sub_eq {x y z : α} (h : x + -y = z) : x = z + y := by
  rw [← h, add_sub_cancel_right' ]
where
  add_sub_cancel_right' : x + -y + y = x := by
    rw [add_assoc, neg_add_cancel, add_zero]

theorem sub_sub_sub_cancel (a b c : α) : (a + -c) + -(b + -c) = a + -b := by
  rw [neg_add, neg_neg, add_add_add_comm, neg_add_cancel, add_zero]

theorem mul_sub (a b c : α) : a * (b + -c) = a * b + -(a * c) := by
  rw [left_distrib, mul_neg]

theorem sub_mul (a b c : α) : (a + -b) * c = a * c + -(b * c) := by
  rw [right_distrib, neg_mul]

end CRing

namespace TOField

open TField

variable {K : Type} [TOField K]

instance : LE K := ⟨fun x y => Nonneg (y + -x)⟩
instance : LT K := ⟨fun x y => ¬ (y ≤ x)⟩

instance decLE (x y : K) : Decidable (x ≤ y) := decNonneg (y + -x)
instance decLT (x y : K) : Decidable (x < y) := instDecidableNot

theorem le_def (x y : K) : (x ≤ y) = Nonneg (y + -x) := rfl
theorem lt_def (x y : K) : (x < y) = ¬ (y ≤ x) := rfl

theorem nonneg_zero : Nonneg (𝟘 : K) := by
  cases nonneg_total (𝟘 : K) with
  | inl h => exact h
  | inr h =>
    rw [neg_zero] at h
    exact h

theorem zero_le_of_nonneg {x : K} (h : Nonneg x) : 𝟘 ≤ x := by
  show Nonneg (x + -𝟘)
  rw [neg_zero, add_zero]
  exact h

theorem nonneg_of_zero_le {x : K} (h : 𝟘 ≤ x) : Nonneg x := by
  have h' : Nonneg (x + -𝟘) := h
  rw [neg_zero, add_zero] at h'
  exact h'

theorem le_refl (x : K) : x ≤ x := by
  show Nonneg (x + -x)
  rw [add_neg_cancel]
  exact nonneg_zero

theorem le_of_eq {x y : K} (h : x = y) : x ≤ y := by
  rw [h]
  exact le_refl y

theorem le_trans {x y z : K} (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  show Nonneg (z + -x)
  rw [← sub_add_sub z y x]
  exact nonneg_add _ _ h2 h1

theorem le_antisymm {x y : K} (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  have h2' : Nonneg (-(y + -x)) := by
    rw [neg_sub']
    exact h2
  have e := nonneg_antisymm _ h1 h2'
  exact (eq_of_add_neg_eq_zero e).symm

theorem le_total (x y : K) : x ≤ y ∨ y ≤ x := by
  cases nonneg_total (y + -x) with
  | inl h => exact Or.inl h
  | inr h =>
    rw [neg_sub'] at h
    exact Or.inr h

/-- Constructive comparison: `x < y` or `y ≤ x`, decided by the supplied procedure. -/
theorem lt_or_le (x y : K) : x < y ∨ y ≤ x :=
  match decNonneg (x + -y) with
  | isTrue h => Or.inr h
  | isFalse h => Or.inl h

theorem le_or_lt (x y : K) : x ≤ y ∨ y < x :=
  match lt_or_le y x with
  | Or.inl h => Or.inr h
  | Or.inr h => Or.inl h

theorem le_of_lt {x y : K} (h : x < y) : x ≤ y := by
  cases le_total x y with
  | inl h' => exact h'
  | inr h' => exact absurd h' h

theorem lt_irrefl (x : K) : ¬ x < x := fun h => h (le_refl x)

theorem not_lt_of_le {x y : K} (h : x ≤ y) : ¬ y < x := fun h' => h' h

theorem le_of_not_lt {x y : K} (h : ¬ y < x) : x ≤ y := by
  cases lt_or_le y x with
  | inl h' => exact absurd h' h
  | inr h' => exact h'

theorem lt_of_lt_of_le {x y z : K} (h1 : x < y) (h2 : y ≤ z) : x < z :=
  fun h => h1 (le_trans h2 h)

theorem lt_of_le_of_lt {x y z : K} (h1 : x ≤ y) (h2 : y < z) : x < z :=
  fun h => h2 (le_trans h h1)

theorem lt_trans {x y z : K} (h1 : x < y) (h2 : y < z) : x < z :=
  lt_of_lt_of_le h1 (le_of_lt h2)

theorem ne_of_lt {x y : K} (h : x < y) : x ≠ y := fun e => h (by rw [e]; exact le_refl y)

theorem lt_of_le_of_ne {x y : K} (h1 : x ≤ y) (h2 : x ≠ y) : x < y :=
  fun h => h2 (le_antisymm h1 h)

/-! ## Compatibility with addition -/

theorem add_le_add_left {x y : K} (z : K) (h : x ≤ y) : z + x ≤ z + y := by
  show Nonneg (z + y + -(z + x))
  rw [neg_add, add_add_add_comm, add_neg_cancel, zero_add]
  exact h

theorem add_le_add_right {x y : K} (z : K) (h : x ≤ y) : x + z ≤ y + z := by
  rw [add_comm x, add_comm y]
  exact add_le_add_left z h

theorem add_le_add {a b c d : K} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right c h1) (add_le_add_left b h2)

theorem le_of_add_le_add_left {x y z : K} (h : z + x ≤ z + y) : x ≤ y := by
  have h2 := add_le_add_left (-z) h
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at h2
  exact h2

theorem le_of_add_le_add_right {x y z : K} (h : x + z ≤ y + z) : x ≤ y := by
  rw [add_comm x, add_comm y] at h
  exact le_of_add_le_add_left h

theorem add_lt_add_left {x y : K} (z : K) (h : x < y) : z + x < z + y :=
  fun h' => h (le_of_add_le_add_left h')

theorem add_lt_add_right {x y : K} (z : K) (h : x < y) : x + z < y + z :=
  fun h' => h (le_of_add_le_add_right h')

theorem add_lt_add_of_lt_of_le {a b c d : K} (h1 : a < b) (h2 : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right c h1) (add_le_add_left b h2)

theorem add_lt_add_of_le_of_lt {a b c d : K} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right c h1) (add_lt_add_left b h2)

theorem neg_le_neg {x y : K} (h : x ≤ y) : -y ≤ -x := by
  show Nonneg (-x + - -y)
  rw [neg_neg, add_comm]
  exact h

theorem neg_lt_neg {x y : K} (h : x < y) : -y < -x := by
  intro h'
  apply h
  have h2 := neg_le_neg h'
  rw [neg_neg, neg_neg] at h2
  exact h2

theorem sub_nonneg_of_le {x y : K} (h : x ≤ y) : 𝟘 ≤ y + -x := zero_le_of_nonneg h

theorem le_of_sub_nonneg {x y : K} (h : 𝟘 ≤ y + -x) : x ≤ y := nonneg_of_zero_le h

theorem le_add_of_nonneg_right {x y : K} (h : 𝟘 ≤ y) : x ≤ x + y := by
  have h2 := add_le_add_left x h
  rw [add_zero] at h2
  exact h2

theorem lt_add_of_pos_right {x y : K} (h : 𝟘 < y) : x < x + y := by
  have h2 := add_lt_add_left x h
  rw [add_zero] at h2
  exact h2

theorem le_sub_iff_add_le {x y z : K} (h : x + z ≤ y) : x ≤ y + -z := by
  have h2 := add_le_add_right (-z) h
  rw [add_sub_cancel_right] at h2
  exact h2

theorem add_le_of_le_sub {x y z : K} (h : x ≤ y + -z) : x + z ≤ y := by
  have h2 := add_le_add_right z h
  rw [add_assoc, neg_add_cancel, add_zero] at h2
  exact h2

/-! ## Compatibility with multiplication -/

theorem mul_nonneg {a b : K} (ha : 𝟘 ≤ a) (hb : 𝟘 ≤ b) : 𝟘 ≤ a * b :=
  zero_le_of_nonneg (nonneg_mul _ _ (nonneg_of_zero_le ha) (nonneg_of_zero_le hb))

theorem mul_le_mul_of_nonneg_left {x y z : K} (hz : 𝟘 ≤ z) (h : x ≤ y) : z * x ≤ z * y := by
  show Nonneg (z * y + -(z * x))
  rw [← mul_neg, ← left_distrib]
  exact nonneg_mul _ _ (nonneg_of_zero_le hz) h

theorem mul_le_mul_of_nonneg_right {x y z : K} (hz : 𝟘 ≤ z) (h : x ≤ y) : x * z ≤ y * z := by
  rw [mul_comm x, mul_comm y]
  exact mul_le_mul_of_nonneg_left hz h

theorem mul_le_mul {a b c d : K} (ha : 𝟘 ≤ a) (hab : a ≤ b) (hc : 𝟘 ≤ c) (hcd : c ≤ d) :
    a * c ≤ b * d :=
  le_trans (mul_le_mul_of_nonneg_left ha hcd)
    (mul_le_mul_of_nonneg_right (le_trans hc hcd) hab)

theorem mul_pos {a b : K} (ha : 𝟘 < a) (hb : 𝟘 < b) : 𝟘 < a * b :=
  lt_of_le_of_ne (mul_nonneg (le_of_lt ha) (le_of_lt hb))
    (fun e => mul_ne_zero' (fun x => ne_of_lt ha x.symm) (fun x => ne_of_lt hb x.symm) e.symm)

theorem zero_le_one : (𝟘 : K) ≤ 𝟙 := by
  apply zero_le_of_nonneg
  cases nonneg_total (𝟙 : K) with
  | inl h => exact h
  | inr h =>
    have h2 := nonneg_mul _ _ h h
    rw [neg_mul_neg, one_mul] at h2
    exact h2

theorem zero_lt_one : (𝟘 : K) < 𝟙 := lt_of_le_of_ne zero_le_one zero_ne_one

/-! ## Image of path counts -/

theorem natCast_nonneg (n : TreeN) : 𝟘 ≤ natCast (K := K) n := by
  induction n with
  | nil => exact le_refl _
  | cons c n ih =>
    rw [natCast_cons]
    have h := add_le_add zero_le_one ih
    rw [add_zero] at h
    exact h

theorem natCast_add (m n : TreeN) : natCast (K := K) (m + n) = natCast m + natCast n := by
  induction m with
  | nil =>
    show natCast (K := K) n = 𝟘 + natCast n
    rw [zero_add]
  | cons c m ih =>
    show natCast (K := K) (c :: (m + n)) = natCast (c :: m) + natCast n
    rw [natCast_cons, natCast_cons, ih, add_assoc]

theorem natCast_mul (m n : TreeN) : natCast (K := K) (m * n) = natCast m * natCast n := by
  induction m with
  | nil =>
    show natCast (K := K) TreeN.zero = 𝟘 * natCast n
    rw [zero_mul]
    rfl
  | cons c m ih =>
    show natCast (K := K) (n + m * n) = natCast (c :: m) * natCast n
    rw [natCast_add, ih, natCast_cons, right_distrib, one_mul]

theorem natCast_one : natCast (K := K) TreeN.one = 𝟙 := by
  show 𝟙 + 𝟘 = 𝟙
  rw [add_zero]

theorem natCast_le {m n : TreeN} (h : TreeN.PathLE m n) : natCast (K := K) m ≤ natCast n := by
  obtain ⟨k, hk⟩ := TreeN.exists_of_le h
  rw [hk, natCast_add]
  exact le_add_of_nonneg_right (natCast_nonneg k)

theorem natCast_pos {n : TreeN} (h : TreeN.PathLT TreeN.zero n) : 𝟘 < natCast (K := K) n :=
  lt_of_le_of_ne (natCast_nonneg n) (fun e => natCast_ne_zero_of_pos h e.symm)

theorem natCast_lt {m n : TreeN} (h : TreeN.PathLT m n) : natCast (K := K) m < natCast n := by
  obtain ⟨k, hk⟩ := TreeN.exists_of_lt h
  rw [hk, natCast_add]
  exact lt_add_of_pos_right (natCast_pos (TreeN.zero_lt_succ k))

theorem natCast_injective {m n : TreeN} (h : natCast (K := K) m = natCast n) : m = n :=
  match TreeN.compare m n with
  | TreeN.Trichotomy.eq e => e
  | TreeN.Trichotomy.lt hl => absurd h (ne_of_lt (natCast_lt hl))
  | TreeN.Trichotomy.gt hg => absurd h.symm (ne_of_lt (natCast_lt hg))

/-- The Archimedean bound, restated with `natCast`. -/
theorem le_archBound (x : K) : x ≤ natCast (archBound x) := arch_spec x

/-! ## Inverses -/

theorem inv_ne_zero {a : K} (ha : a ≠ 𝟘) : inv a ≠ 𝟘 := by
  intro e
  have h := mul_inv_cancel' ha
  rw [e, mul_zero] at h
  exact zero_ne_one h

theorem inv_pos {a : K} (ha : 𝟘 < a) : 𝟘 < inv a := by
  have ha0 : a ≠ 𝟘 := fun e => ne_of_lt ha e.symm
  apply lt_of_le_of_ne _ (fun e => inv_ne_zero ha0 e.symm)
  apply zero_le_of_nonneg
  cases nonneg_total (inv a) with
  | inl h => exact h
  | inr h =>
    have h2 := nonneg_mul _ _ (nonneg_of_zero_le (le_of_lt ha)) h
    rw [mul_neg, mul_inv_cancel' ha0] at h2
    exact absurd (nonneg_antisymm _ (nonneg_of_zero_le zero_le_one) h2).symm zero_ne_one

theorem inv_mul_distrib {a b : K} (ha : a ≠ 𝟘) (hb : b ≠ 𝟘) : inv (a * b) = inv a * inv b := by
  apply mul_left_cancel' (mul_ne_zero' ha hb)
  rw [mul_inv_cancel' (mul_ne_zero' ha hb), mul_mul_mul_comm, mul_inv_cancel' ha,
    mul_inv_cancel' hb, one_mul]

theorem inv_one : inv (𝟙 : K) = 𝟙 := by
  apply mul_left_cancel' (fun e => zero_ne_one e.symm)
  rw [mul_inv_cancel' (fun e => zero_ne_one e.symm), one_mul]

theorem inv_le_inv {a b : K} (ha : 𝟘 < a) (h : a ≤ b) : inv b ≤ inv a := by
  have ha0 : a ≠ 𝟘 := fun e => ne_of_lt ha e.symm
  have hb : 𝟘 < b := lt_of_lt_of_le ha h
  have hb0 : b ≠ 𝟘 := fun e => ne_of_lt hb e.symm
  show Nonneg (inv a + -inv b)
  have e : inv a * inv b * (b + -a) = inv a + -inv b := by
    rw [left_distrib, mul_neg, mul_assoc, inv_mul_cancel' hb0, mul_one, mul_right_comm,
      inv_mul_cancel' ha0, one_mul]
  rw [← e]
  exact nonneg_mul _ _ (nonneg_of_zero_le (mul_nonneg (le_of_lt (inv_pos ha))
    (le_of_lt (inv_pos hb)))) h

/-- From `a * c ≤ b` with `c > 0` infer `a ≤ b * inv c`. -/
theorem le_mul_inv_of_mul_le {a b c : K} (hc : 𝟘 < c) (h : a * c ≤ b) : a ≤ b * inv c := by
  have hc0 : c ≠ 𝟘 := fun e => ne_of_lt hc e.symm
  have h2 := mul_le_mul_of_nonneg_right (le_of_lt (inv_pos hc)) h
  rw [mul_assoc, mul_inv_cancel' hc0, mul_one] at h2
  exact h2

/-! ## Absolute value -/

/-- Absolute value relative to a decision of nonnegativity. -/
def absD (x : K) : Decidable (Nonneg x) → K
  | isTrue _ => x
  | isFalse _ => -x

/-- Absolute value, by the supplied decision procedure for nonnegativity. -/
def abs (x : K) : K := absD x (decNonneg x)

theorem absD_of_nonneg {x : K} (h : Nonneg x) : ∀ d, absD x d = x
  | isTrue _ => rfl
  | isFalse h' => absurd h h'

theorem absD_of_not_nonneg {x : K} (h : ¬ Nonneg x) : ∀ d, absD x d = -x
  | isTrue h' => absurd h' h
  | isFalse _ => rfl

theorem abs_of_nonneg {x : K} (h : Nonneg x) : abs x = x := absD_of_nonneg h _

theorem abs_of_zero_le {x : K} (h : 𝟘 ≤ x) : abs x = x := abs_of_nonneg (nonneg_of_zero_le h)

theorem abs_of_nonpos {x : K} (h : Nonneg (-x)) : abs x = -x := by
  unfold abs
  cases decNonneg x with
  | isTrue hx =>
    show x = -x
    rw [nonneg_antisymm x hx h, neg_zero]
  | isFalse _ => rfl

theorem abs_nonneg' (x : K) : Nonneg (abs x) := by
  unfold abs
  cases decNonneg x with
  | isTrue hx => exact hx
  | isFalse hx =>
    cases nonneg_total x with
    | inl h => exact absurd h hx
    | inr h => exact h

theorem abs_nonneg (x : K) : 𝟘 ≤ abs x := zero_le_of_nonneg (abs_nonneg' x)

theorem abs_zero : abs (𝟘 : K) = 𝟘 := abs_of_nonneg nonneg_zero

theorem abs_neg (x : K) : abs (-x) = abs x := by
  cases nonneg_total x with
  | inl h =>
    rw [abs_of_nonneg h, abs_of_nonpos (by rw [neg_neg]; exact h), neg_neg]
  | inr h =>
    rw [abs_of_nonneg h, abs_of_nonpos h]

theorem le_abs_self (x : K) : x ≤ abs x := by
  cases nonneg_total x with
  | inl h =>
    rw [abs_of_nonneg h]
    exact le_refl x
  | inr h =>
    rw [abs_of_nonpos h]
    exact le_trans (y := 𝟘) (le_of_sub_nonneg' h) (zero_le_of_nonneg h)
where
  le_of_sub_nonneg' {x : K} (h : Nonneg (-x)) : x ≤ 𝟘 := by
    show Nonneg (𝟘 + -x)
    rw [zero_add]
    exact h

theorem neg_le_abs (x : K) : -x ≤ abs x := by
  have h := le_abs_self (-x)
  rw [abs_neg] at h
  exact h

theorem abs_le_of {x e : K} (h1 : -e ≤ x) (h2 : x ≤ e) : abs x ≤ e := by
  cases nonneg_total x with
  | inl h =>
    rw [abs_of_nonneg h]
    exact h2
  | inr h =>
    rw [abs_of_nonpos h]
    have h3 := neg_le_neg h1
    rw [neg_neg] at h3
    exact h3

theorem le_of_abs_le {x e : K} (h : abs x ≤ e) : x ≤ e := le_trans (le_abs_self x) h

theorem neg_le_of_abs_le {x e : K} (h : abs x ≤ e) : -e ≤ x := by
  have h2 := neg_le_neg (le_trans (neg_le_abs x) h)
  rw [neg_neg] at h2
  exact h2

theorem abs_add (x y : K) : abs (x + y) ≤ abs x + abs y := by
  apply abs_le_of
  · rw [neg_add]
    have h1 := neg_le_neg (le_abs_self x)
    have h2 := neg_le_neg (le_abs_self y)
    have h1' := le_trans (neg_le_neg (neg_le_abs x)) (le_of_eq (neg_neg x))
    have h2' := le_trans (neg_le_neg (neg_le_abs y)) (le_of_eq (neg_neg y))
    exact add_le_add h1' h2'
  · exact add_le_add (le_abs_self x) (le_abs_self y)

theorem abs_sub_comm (x y : K) : abs (x + -y) = abs (y + -x) := by
  rw [← abs_neg, neg_sub']

/-- Triangle inequality for the rational distance `|x - z|`. -/
theorem abs_sub_le (x y z : K) : abs (x + -z) ≤ abs (x + -y) + abs (y + -z) := by
  rw [← sub_add_sub x y z]
  exact abs_add _ _

theorem abs_mul (x y : K) : abs (x * y) = abs x * abs y := by
  cases nonneg_total x with
  | inl hx =>
    cases nonneg_total y with
    | inl hy =>
      rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (nonneg_mul _ _ hx hy)]
    | inr hy =>
      have h : Nonneg (-(x * y)) := by rw [← mul_neg]; exact nonneg_mul _ _ hx hy
      rw [abs_of_nonneg hx, abs_of_nonpos hy, abs_of_nonpos h, mul_neg]
  | inr hx =>
    cases nonneg_total y with
    | inl hy =>
      have h : Nonneg (-(x * y)) := by rw [← neg_mul]; exact nonneg_mul _ _ hx hy
      rw [abs_of_nonpos hx, abs_of_nonneg hy, abs_of_nonpos h, neg_mul]
    | inr hy =>
      have h : Nonneg (x * y) := by rw [← neg_mul_neg]; exact nonneg_mul _ _ hx hy
      rw [abs_of_nonpos hx, abs_of_nonpos hy, abs_of_nonneg h, neg_mul_neg]

theorem eq_zero_of_abs_eq_zero {x : K} (h : abs x = 𝟘) : x = 𝟘 := by
  cases nonneg_total x with
  | inl hx =>
    rw [abs_of_nonneg hx] at h
    exact h
  | inr hx =>
    rw [abs_of_nonpos hx] at h
    rw [← neg_neg x, h, neg_zero]

theorem eq_of_abs_sub_eq_zero {x y : K} (h : abs (x + -y) = 𝟘) : x = y :=
  eq_of_add_neg_eq_zero (eq_zero_of_abs_eq_zero h)

theorem abs_of_pos {x : K} (h : 𝟘 < x) : abs x = x := abs_of_zero_le (le_of_lt h)

theorem abs_pos_of_ne {x : K} (h : x ≠ 𝟘) : 𝟘 < abs x :=
  lt_of_le_of_ne (abs_nonneg x) (fun e => h (eq_zero_of_abs_eq_zero e.symm))

theorem abs_abs (x : K) : abs (abs x) = abs x := abs_of_nonneg (abs_nonneg' x)

/-- Reverse triangle inequality (one side). -/
theorem abs_le_abs_add_abs_sub (x y : K) : abs x ≤ abs y + abs (x + -y) := by
  have h := abs_add y (x + -y)
  have e : y + (x + -y) = x := by rw [add_comm x, ← add_assoc, add_neg_cancel, zero_add]
  rw [e] at h
  exact h

/-! ## Distance -/

/-- The rational distance `d(p,q) := |p - q|`. -/
def dist (p q : K) : K := abs (p + -q)

theorem dist_nonneg (p q : K) : 𝟘 ≤ dist p q := abs_nonneg _

theorem dist_self (p : K) : dist p p = 𝟘 := by
  unfold dist
  rw [add_neg_cancel, abs_zero]

theorem eq_of_dist_eq_zero {p q : K} (h : dist p q = 𝟘) : p = q := eq_of_abs_sub_eq_zero h

theorem dist_comm (p q : K) : dist p q = dist q p := abs_sub_comm p q

theorem dist_triangle (p q r : K) : dist p r ≤ dist p q + dist q r := abs_sub_le p q r

end TOField
end
