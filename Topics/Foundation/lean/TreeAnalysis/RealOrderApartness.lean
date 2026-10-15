module

public import TreeAnalysis.RealQuotient
public import TreeAnalysis.SeqOrder

@[expose] public section

/-!
# Checkpoints C (inverse) and D1, D2 — constructive order, apartness, inverse, density

* `RPos x`: some representative is eventually above a fixed positive precision;
  `x < y := RPos (y - x)`;  `x ≤ y := RNonneg (y - x)`;  `RApart x y := x < y ∨ y < x`.
* Proved order laws: irreflexivity and transitivity of `<`; reflexivity, transitivity and
  antisymmetry of `≤`; `x ≤ y ↔ ¬ y < x` (both directions constructive); compatibility with
  addition and with multiplication by nonnegative/positive elements; tightness
  `¬ RApart x y → x = y`; hence `x ≠ y → ¬¬ RApart x y`.
* **Trichotomy is not asserted** for arbitrary elements.
* Inverse: `RPosW x` and `ApartW x` are *data* (a representative with an explicit separation
  witness).  `rinv x h` satisfies `x * rinv x h = 1` and does not depend on `h`.  The
  propositional `RApart x 0` is equivalent to `Nonempty (ApartW x)`; it yields the
  propositional statement `∃ y, x * y = 1`.
* Archimedean property `x < natR n`, and rational density between separated reals.
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace CRing

variable {α : Type} [CRing α]

theorem add_sub_add_right (x y z : α) : y + z + -(x + z) = y + -x := by
  rw [neg_add, add_add_add_comm, add_neg_cancel, add_zero]

theorem add_sub_add_left (x y z : α) : z + y + -(z + x) = y + -x := by
  rw [add_comm z y, add_comm z x, add_sub_add_right]

theorem sub_zero' (x : α) : x + -𝟘 = x := by rw [neg_zero, add_zero]

end CRing

namespace TreeR

open TField TOField

variable {K : Type} [TOField K]

/-! ## Positivity and nonnegativity of reals -/

/-- Positivity: some representative is eventually above a fixed positive precision. -/
def RPos (x : TreeR K) : Prop := ∃ c : CSeq K, mkR c = x ∧ SeqPos c.seq

/-- Nonnegativity: some representative is eventually above `-eps k`, for every `k`. -/
def RNonneg (x : TreeR K) : Prop := ∃ c : CSeq K, mkR c = x ∧ SeqNonneg c.seq

theorem rpos_mk {c : CSeq K} (h : SeqPos c.seq) : RPos (mkR c) := ⟨c, rfl, h⟩

theorem seqPos_of_rpos {c : CSeq K} (h : RPos (mkR c)) : SeqPos c.seq := by
  obtain ⟨d, e, hd⟩ := h
  exact seqPos_resp (mkR_exact e) hd

theorem rnonneg_mk {c : CSeq K} (h : SeqNonneg c.seq) : RNonneg (mkR c) := ⟨c, rfl, h⟩

theorem seqNonneg_of_rnonneg {c : CSeq K} (h : RNonneg (mkR c)) : SeqNonneg c.seq := by
  obtain ⟨d, e, hd⟩ := h
  exact seqNonneg_resp (mkR_exact e) hd

/-- Strict order: positive separation. -/
def RLt (x y : TreeR K) : Prop := RPos (y + -x)
/-- Non-strict order. -/
def RLe (x y : TreeR K) : Prop := RNonneg (y + -x)

instance : LT (TreeR K) := ⟨RLt⟩
instance : LE (TreeR K) := ⟨RLe⟩

/-- Apartness: positive separation in one of the two directions. -/
def RApart (x y : TreeR K) : Prop := x < y ∨ y < x

theorem lt_def (x y : TreeR K) : (x < y) = RPos (y + -x) := rfl
theorem le_def (x y : TreeR K) : (x ≤ y) = RNonneg (y + -x) := rfl

theorem pos_iff (x : TreeR K) : ((𝟘 : TreeR K) < x → RPos x) ∧ (RPos x → (𝟘 : TreeR K) < x) := by
  constructor
  · intro h
    have h' : RPos (x + -𝟘) := h
    rw [sub_zero'] at h'
    exact h'
  · intro h
    show RPos (x + -𝟘)
    rw [sub_zero']
    exact h

theorem nonneg_iff (x : TreeR K) :
    ((𝟘 : TreeR K) ≤ x → RNonneg x) ∧ (RNonneg x → (𝟘 : TreeR K) ≤ x) := by
  constructor
  · intro h
    have h' : RNonneg (x + -𝟘) := h
    rw [sub_zero'] at h'
    exact h'
  · intro h
    show RNonneg (x + -𝟘)
    rw [sub_zero']
    exact h

theorem not_rpos_zero : ¬ RPos (𝟘 : TreeR K) := fun h => not_seqPos_zero (seqPos_of_rpos h)

theorem rnonneg_zero : RNonneg (𝟘 : TreeR K) := rnonneg_mk (seqNonneg_const (le_refl _))

theorem rpos_add_nonneg {x y : TreeR K} (hx : RPos x) (hy : RNonneg y) : RPos (x + y) := by
  revert hx hy
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  intro hx hy
  exact rpos_mk (c := addSeq a b) (seqPos_add_nonneg (seqPos_of_rpos hx) (seqNonneg_of_rnonneg hy))

theorem rnonneg_of_rpos {x : TreeR K} (h : RPos x) : RNonneg x := by
  obtain ⟨c, e, hc⟩ := h
  exact ⟨c, e, seqNonneg_of_seqPos hc⟩

theorem rpos_add {x y : TreeR K} (hx : RPos x) (hy : RPos y) : RPos (x + y) :=
  rpos_add_nonneg hx (rnonneg_of_rpos hy)

theorem rnonneg_add {x y : TreeR K} (hx : RNonneg x) (hy : RNonneg y) : RNonneg (x + y) := by
  revert hx hy
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  intro hx hy
  exact rnonneg_mk (c := addSeq a b) (seqNonneg_add (seqNonneg_of_rnonneg hx)
    (seqNonneg_of_rnonneg hy))

theorem rpos_mul {x y : TreeR K} (hx : RPos x) (hy : RPos y) : RPos (x * y) := by
  revert hx hy
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  intro hx hy
  exact rpos_mk (c := mulSeq a b) (seqPos_mul (seqPos_of_rpos hx) (seqPos_of_rpos hy))

theorem rnonneg_mul {x y : TreeR K} (hx : RNonneg x) (hy : RNonneg y) : RNonneg (x * y) := by
  revert hx hy
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  intro hx hy
  exact rnonneg_mk (seqNonneg_mul a b (seqNonneg_of_rnonneg hx) (seqNonneg_of_rnonneg hy))

theorem rnonneg_antisymm {x : TreeR K} (h1 : RNonneg x) (h2 : RNonneg (-x)) : x = 𝟘 := by
  revert h1 h2
  induction x using ind_mkR with | h a => ?_
  intro h1 h2
  exact mkR_sound (seqEquiv_zero_of_nonneg_nonneg (seqNonneg_of_rnonneg h1)
    (seqNonneg_of_rnonneg (c := negSeq a) h2))

theorem not_rpos_neg_of_rnonneg {x : TreeR K} (h1 : RNonneg x) (h2 : RPos (-x)) : False := by
  revert h1 h2
  induction x using ind_mkR with | h a => ?_
  intro h1 h2
  exact not_seqPos_neg_of_seqNonneg (seqNonneg_of_rnonneg h1) (seqPos_of_rpos (c := negSeq a) h2)

theorem rnonneg_of_not_rpos_neg {x : TreeR K} (h : ¬ RPos (-x)) : RNonneg x := by
  revert h
  induction x using ind_mkR with | h a => ?_
  intro h
  exact rnonneg_mk (seqNonneg_of_not_seqPos_neg a (fun hp => h (rpos_mk (c := negSeq a) hp)))

/-! ## Order laws -/

theorem lt_irrefl (x : TreeR K) : ¬ x < x := by
  intro h
  have h' : RPos (x + -x) := h
  rw [add_neg_cancel] at h'
  exact not_rpos_zero h'

theorem lt_trans {x y z : TreeR K} (h1 : x < y) (h2 : y < z) : x < z := by
  show RPos (z + -x)
  rw [← sub_add_sub z y x]
  exact rpos_add h2 h1

theorem le_refl (x : TreeR K) : x ≤ x := by
  show RNonneg (x + -x)
  rw [add_neg_cancel]
  exact rnonneg_zero

theorem le_trans {x y z : TreeR K} (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  show RNonneg (z + -x)
  rw [← sub_add_sub z y x]
  exact rnonneg_add h2 h1

theorem le_antisymm {x y : TreeR K} (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  have h2' : RNonneg (-(y + -x)) := by
    rw [neg_sub']
    exact h2
  exact (eq_of_add_neg_eq_zero (rnonneg_antisymm h1 h2')).symm

theorem le_of_lt {x y : TreeR K} (h : x < y) : x ≤ y := rnonneg_of_rpos h

theorem lt_of_lt_of_le {x y z : TreeR K} (h1 : x < y) (h2 : y ≤ z) : x < z := by
  show RPos (z + -x)
  rw [← sub_add_sub z y x, add_comm]
  exact rpos_add_nonneg h1 h2

theorem lt_of_le_of_lt {x y z : TreeR K} (h1 : x ≤ y) (h2 : y < z) : x < z := by
  show RPos (z + -x)
  rw [← sub_add_sub z y x]
  exact rpos_add_nonneg h2 h1

/-- `x ≤ y` excludes `y < x`. -/
theorem not_lt_of_le {x y : TreeR K} (h : x ≤ y) : ¬ y < x := by
  intro h'
  have h'' : RPos (-(y + -x)) := by
    rw [neg_sub']
    exact h'
  exact not_rpos_neg_of_rnonneg h h''

/-- **Constructive**: `¬ (y < x)` implies `x ≤ y`. -/
theorem le_of_not_lt {x y : TreeR K} (h : ¬ y < x) : x ≤ y := by
  apply rnonneg_of_not_rpos_neg
  intro h'
  apply h
  show RPos (x + -y)
  rw [← neg_sub']
  exact h'

theorem add_lt_add_right {x y : TreeR K} (z : TreeR K) (h : x < y) : x + z < y + z := by
  show RPos (y + z + -(x + z))
  rw [add_sub_add_right]
  exact h

theorem add_le_add_right {x y : TreeR K} (z : TreeR K) (h : x ≤ y) : x + z ≤ y + z := by
  show RNonneg (y + z + -(x + z))
  rw [add_sub_add_right]
  exact h

theorem add_le_add_left {x y : TreeR K} (z : TreeR K) (h : x ≤ y) : z + x ≤ z + y := by
  show RNonneg (z + y + -(z + x))
  rw [add_sub_add_left]
  exact h

theorem add_le_add {a b c d : TreeR K} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right c h1) (add_le_add_left b h2)

theorem mul_le_mul_of_nonneg_left {x y z : TreeR K} (hz : 𝟘 ≤ z) (h : x ≤ y) :
    z * x ≤ z * y := by
  show RNonneg (z * y + -(z * x))
  rw [← mul_neg, ← left_distrib]
  exact rnonneg_mul ((nonneg_iff z).1 hz) h

theorem mul_lt_mul_of_pos_left {x y z : TreeR K} (hz : 𝟘 < z) (h : x < y) : z * x < z * y := by
  show RPos (z * y + -(z * x))
  rw [← mul_neg, ← left_distrib]
  exact rpos_mul ((pos_iff z).1 hz) h

theorem mul_pos {x y : TreeR K} (hx : 𝟘 < x) (hy : 𝟘 < y) : 𝟘 < x * y :=
  (pos_iff _).2 (rpos_mul ((pos_iff x).1 hx) ((pos_iff y).1 hy))

theorem zero_lt_one : (𝟘 : TreeR K) < 𝟙 :=
  (pos_iff _).2 (rpos_mk (seqPos_const TOField.zero_lt_one))

/-! ## Rational embedding and order -/

theorem ofQ_lt_ofQ {p q : K} (h : p < q) : ofQ p < ofQ q := by
  show RPos (ofQ q + -ofQ p)
  rw [← ofQ_neg, ← ofQ_add]
  apply rpos_mk
  apply seqPos_const
  have h2 := TOField.add_lt_add_right (-p) h
  rw [add_neg_cancel] at h2
  exact h2

theorem ofQ_le_ofQ {p q : K} (h : p ≤ q) : ofQ p ≤ ofQ q := by
  show RNonneg (ofQ q + -ofQ p)
  rw [← ofQ_neg, ← ofQ_add]
  exact rnonneg_mk (seqNonneg_const (sub_nonneg_of_le h))

theorem le_of_ofQ_le {p q : K} (h : ofQ p ≤ ofQ q) : p ≤ q := by
  apply TOField.le_of_not_lt
  intro h'
  exact not_lt_of_le h (ofQ_lt_ofQ h')

theorem lt_of_ofQ_lt {p q : K} (h : ofQ p < ofQ q) : p < q := by
  intro h'
  exact not_lt_of_le (ofQ_le_ofQ h') h

/-! ## Apartness and tightness -/

theorem apart_irrefl (x : TreeR K) : ¬ RApart x x := fun h =>
  match h with
  | Or.inl h => lt_irrefl x h
  | Or.inr h => lt_irrefl x h

theorem apart_symm {x y : TreeR K} (h : RApart x y) : RApart y x := Or.symm h

/-- **Tightness**: not apart implies equal. -/
theorem eq_of_not_apart {x y : TreeR K} (h : ¬ RApart x y) : x = y :=
  le_antisymm (le_of_not_lt (fun h' => h (Or.inr h'))) (le_of_not_lt (fun h' => h (Or.inl h')))

theorem ne_of_apart {x y : TreeR K} (h : RApart x y) : x ≠ y := by
  intro e
  rw [e] at h
  exact apart_irrefl y h

/-- From mere inequality only the double negation of apartness follows constructively. -/
theorem not_not_apart_of_ne {x y : TreeR K} (h : x ≠ y) : ¬¬ RApart x y :=
  fun h' => h (eq_of_not_apart h')

/-- `x ≤ y` is equivalent to `¬ y < x` (both directions proved constructively). -/
theorem le_iff_not_lt (x y : TreeR K) : (x ≤ y → ¬ y < x) ∧ (¬ y < x → x ≤ y) :=
  ⟨not_lt_of_le, le_of_not_lt⟩

/-! ## Inverse under a positive separation witness -/

/-- Data: a representative of `x` with an explicit positive separation witness. -/
structure RPosW (x : TreeR K) : Type where
  rep : CSeq K
  eq : mkR rep = x
  wit : PosWit rep.seq

/-- Data: an explicit apartness-from-zero witness. -/
inductive ApartW (x : TreeR K) : Type
  | pos : RPosW x → ApartW x
  | neg : RPosW (-x) → ApartW x

/-- Inverse of a positively separated real. -/
def rinvPos (x : TreeR K) (h : RPosW x) : TreeR K := mkR (invSeq h.rep h.wit)

theorem mul_rinvPos (x : TreeR K) (h : RPosW x) : x * rinvPos x h = 𝟙 := by
  obtain ⟨c, e, w⟩ := h
  subst e
  exact mkR_sound (mul_invSeq_equiv c w)

/-- Inverse under an apartness witness. -/
def rinv (x : TreeR K) : ApartW x → TreeR K
  | ApartW.pos h => rinvPos x h
  | ApartW.neg h => -rinvPos (-x) h

/-- **Inverse law** under a positive separation witness. -/
theorem mul_rinv (x : TreeR K) (h : ApartW x) : x * rinv x h = 𝟙 := by
  cases h with
  | pos h => exact mul_rinvPos x h
  | neg h =>
    show x * -rinvPos (-x) h = 𝟙
    rw [mul_neg, ← neg_mul]
    exact mul_rinvPos (-x) h

theorem inv_unique {x y y' : TreeR K} (h : x * y = 𝟙) (h' : x * y' = 𝟙) : y = y' := by
  rw [← mul_one y, ← h', ← mul_assoc, mul_comm y x, h, one_mul]

/-- The inverse does not depend on the chosen witness. -/
theorem rinv_indep (x : TreeR K) (h h' : ApartW x) : rinv x h = rinv x h' :=
  inv_unique (mul_rinv x h) (mul_rinv x h')

theorem rpos_of_rposW {x : TreeR K} (h : RPosW x) : RPos x := ⟨h.rep, h.eq, seqPos_of_posWit h.wit⟩

/-- The propositional shadow of a witness. -/
theorem apart_of_apartW {x : TreeR K} (h : ApartW x) : RApart x 𝟘 := by
  cases h with
  | pos h => exact Or.inr ((pos_iff x).2 (rpos_of_rposW h))
  | neg h =>
    apply Or.inl
    show RPos (𝟘 + -x)
    rw [zero_add]
    exact rpos_of_rposW h

/-- Propositional apartness is the mere existence of a witness. -/
theorem nonempty_apartW_of_apart {x : TreeR K} (h : RApart x 𝟘) : Nonempty (ApartW x) := by
  cases h with
  | inl h =>
    have h' : RPos (𝟘 + -x) := h
    rw [zero_add] at h'
    obtain ⟨c, e, k, N, hN⟩ := h'
    exact ⟨ApartW.neg ⟨c, e, ⟨k, N, hN⟩⟩⟩
  | inr h =>
    obtain ⟨c, e, k, N, hN⟩ := (pos_iff x).1 h
    exact ⟨ApartW.pos ⟨c, e, ⟨k, N, hN⟩⟩⟩

/-- Propositional inverse under propositional apartness. -/
theorem exists_inv_of_apart {x : TreeR K} (h : RApart x 𝟘) : ∃ y, x * y = 𝟙 := by
  obtain ⟨w⟩ := nonempty_apartW_of_apart h
  exact ⟨rinv x w, mul_rinv x w⟩

/-- Conversely, an invertible real is apart from zero. -/
theorem apart_of_mul_eq_one {x y : TreeR K} (h : x * y = 𝟙) : RApart x 𝟘 := by
  revert h
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  intro h
  have hE := mkR_exact h
  obtain ⟨N, hN⟩ := hE (succ TreeN.zero)
  let P := succ (succ TreeN.zero) + bnd b
  let n0 := maxN (maxN N (b.mod TreeN.zero)) (a.mod (succ P))
  have hn0N : PathLE N n0 := TreeN.le_of_maxN_le_left (TreeN.le_maxN_left _ _)
  have hb0 : PathLE (b.mod TreeN.zero) n0 := TreeN.le_of_maxN_le_right (TreeN.le_maxN_left _ _)
  have hmod : ∀ n, PathLE n0 n → abs (a.seq n + -a.seq n0) ≤ eps (succ P) := fun n hn =>
    a.isMod _ n n0 (TreeN.le_trans (TreeN.le_maxN_right _ _) hn) (TreeN.le_maxN_right _ _)
  cases TOField.le_or_lt (eps P) (a.seq n0) with
  | inl hpos =>
    apply Or.inr
    apply (pos_iff _).2
    apply rpos_mk
    refine ⟨succ P, n0, fun n hn => ?_⟩
    have h2 := TOField.le_trans hpos (upper_of_abs (hmod n hn))
    rw [← eps_succ_add] at h2
    exact le_of_add_le_add_left h2
  | inr hlt =>
    cases TOField.le_or_lt (a.seq n0) (-eps P) with
    | inl hneg =>
      apply Or.inl
      show RPos (𝟘 + -mkR a)
      rw [zero_add]
      apply rpos_mk (c := negSeq a)
      refine ⟨succ P, n0, fun n hn => ?_⟩
      show eps (succ P) ≤ -a.seq n
      have h2 := TOField.le_trans (lower_of_abs (hmod n hn)) (TOField.add_le_add_left _ hneg)
      have h3 := neg_le_neg h2
      rw [neg_add, neg_neg, ← eps_succ_add P, ← add_assoc, neg_add_cancel, zero_add] at h3
      exact h3
    | inr hneg2 =>
      apply False.elim
      have habs : abs (a.seq n0) ≤ eps P := abs_le_of (TOField.le_of_lt hneg2) (TOField.le_of_lt hlt)
      have hprod := abs_mul_le habs (abs_le_bnd b hb0)
      rw [mul_comm (eps _) (natCast _), natCast_twoPow_mul_eps_add] at hprod
      have hc : abs (a.seq n0 * b.seq n0 + -𝟙) ≤ eps (succ TreeN.zero) := hN n0 hn0N
      have h1 : 𝟙 ≤ abs (a.seq n0 * b.seq n0) + eps (succ TreeN.zero) := by
        have := abs_le_abs_add_abs_sub (𝟙 : K) (a.seq n0 * b.seq n0)
        rw [abs_of_pos TOField.zero_lt_one, abs_sub_comm] at this
        exact TOField.le_trans this (TOField.add_le_add_left _ hc)
      have h2 := TOField.le_trans h1 (TOField.add_le_add_right _ hprod)
      have h3 := TOField.add_lt_add_right (eps (succ TreeN.zero)) (eps_succ_lt (K := K) (succ TreeN.zero))
      rw [eps_succ_add, eps_zero] at h3
      exact TOField.lt_irrefl _ (TOField.lt_of_le_of_lt h2 h3)

/-! ## Archimedean property and density -/

/-- **Archimedean property**: every real lies below the image of an intrinsic path count. -/
theorem archimedean (x : TreeR K) : ∃ n : TreeN, x < natR n := by
  induction x using ind_mkR with | h c => ?_
  refine ⟨twoPow (bnd c) + TreeN.one, ?_⟩
  apply rpos_mk (c := addSeq (constSeq (natCast (twoPow (bnd c) + TreeN.one))) (negSeq c))
  refine ⟨TreeN.zero, c.mod TreeN.zero, fun n hn => ?_⟩
  show eps TreeN.zero ≤ natCast (twoPow (bnd c) + TreeN.one) + -c.seq n
  rw [eps_zero, natCast_add, natCast_one]
  apply le_sub_iff_add_le
  rw [add_comm]
  exact TOField.add_le_add_right _ (TOField.le_trans (le_abs_self _) (abs_le_bnd c hn))

/-- Upper and lower Archimedean bound by path counts. -/
theorem archimedean_abs (x : TreeR K) : ∃ n : TreeN, x < natR n ∧ -natR n < x := by
  obtain ⟨n, hn⟩ := archimedean x
  obtain ⟨m, hm⟩ := archimedean (-x)
  refine ⟨n + m, lt_of_lt_of_le hn ?_, ?_⟩
  · rw [natR_add]
    have h := add_le_add_left (natR n) (ofQ_le_ofQ (natCast_nonneg (K := K) m))
    rw [ofQ_zero, add_zero] at h
    exact h
  · have h1 : -natR (n + m) ≤ -natR (K := K) m := by
      show RNonneg (-natR m + - -natR (n + m))
      rw [neg_neg, natR_add, add_comm, add_assoc, add_neg_cancel, add_zero]
      exact (nonneg_iff _).1 (ofQ_le_ofQ (natCast_nonneg n))
    apply lt_of_le_of_lt h1
    show RPos (x + - -natR m)
    rw [neg_neg]
    have hm' : RPos (natR m + - -x) := hm
    rw [neg_neg, add_comm] at hm'
    exact hm'

/-- Small rational precisions below every positive rational. -/
theorem exists_eps_lt_rat {δ : K} (h : 𝟘 < δ) : ∃ n : TreeN, eps n < δ := exists_eps_lt h

/-- **Rational density** between positively separated reals. -/
theorem exists_rat_between {x y : TreeR K} (h : x < y) : ∃ q : K, x < ofQ q ∧ ofQ q < y := by
  revert h
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  intro h
  obtain ⟨k, N, hN⟩ := seqPos_of_rpos (c := addSeq b (negSeq a)) h
  let k2 := succ (succ k)
  let n0 := maxN N (maxN (a.mod k2) (b.mod k2))
  have hn0N : PathLE N n0 := TreeN.le_maxN_left _ _
  have hn0a : PathLE (a.mod k2) n0 := TreeN.le_of_maxN_le_left (TreeN.le_maxN_right _ _)
  have hn0b : PathLE (b.mod k2) n0 := TreeN.le_of_maxN_le_right (TreeN.le_maxN_right _ _)
  refine ⟨a.seq n0 + eps (succ k), ?_, ?_⟩
  · apply rpos_mk (c := addSeq (constSeq (a.seq n0 + eps (succ k))) (negSeq a))
    refine ⟨k2, a.mod k2, fun n hn => ?_⟩
    show eps k2 ≤ a.seq n0 + eps (succ k) + -a.seq n
    apply le_sub_iff_add_le
    have h1 := lower_of_abs (a.isMod k2 n n0 hn hn0a)
    have h2 := TOField.add_le_add_left (eps k2) h1
    rw [← add_assoc, eps_succ_add] at h2
    rw [add_comm (a.seq n0)]
    exact h2
  · apply rpos_mk (c := addSeq b (negSeq (constSeq (a.seq n0 + eps (succ k)))))
    refine ⟨k2, n0, fun n hn => ?_⟩
    show eps k2 ≤ b.seq n + -(a.seq n0 + eps (succ k))
    apply le_sub_iff_add_le
    have h1 : eps k + a.seq n0 ≤ b.seq n0 := add_le_of_le_sub (hN n0 hn0N)
    have h2 := upper_of_abs (b.isMod k2 n n0 (TreeN.le_trans hn0b hn) hn0b)
    have h3 := TOField.le_trans h1 h2
    rw [← eps_three k, add_assoc, add_assoc, add_comm (eps k2), add_assoc] at h3
    have h4 := le_of_add_le_add_left h3
    rw [add_comm (eps k2), add_comm (a.seq n0)]
    exact h4

/-! ## Cotransitivity (locatedness of the strict order) -/

/-- **Cotransitivity**: `x < y → x < z ∨ z < y`, decided at one explicitly chosen rational
index; no excluded middle about real numbers is used. -/
theorem lt_cotrans {x y : TreeR K} (z : TreeR K) (h : x < y) : x < z ∨ z < y := by
  revert h
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  induction z using ind_mkR with | h c => ?_
  intro h
  obtain ⟨k, N, hN⟩ := seqPos_of_rpos (c := addSeq b (negSeq a)) h
  let q := succ (succ (succ k))
  let n0 := maxN N (maxN (a.mod q) (maxN (b.mod q) (c.mod q)))
  have hN0 : PathLE N n0 := TreeN.le_maxN_left _ _
  have ha0 : PathLE (a.mod q) n0 := TreeN.le_of_maxN_le_left (TreeN.le_maxN_right _ _)
  have hb0 : PathLE (b.mod q) n0 :=
    TreeN.le_of_maxN_le_left (TreeN.le_of_maxN_le_right (TreeN.le_maxN_right _ _))
  have hc0 : PathLE (c.mod q) n0 :=
    TreeN.le_of_maxN_le_right (TreeN.le_of_maxN_le_right (TreeN.le_maxN_right _ _))
  cases TOField.le_or_lt (eps (succ k) + a.seq n0) (c.seq n0) with
  | inl hA =>
    apply Or.inl
    apply rpos_mk (c := addSeq c (negSeq a))
    refine ⟨succ (succ k), n0, fun n hn => ?_⟩
    show eps (succ (succ k)) ≤ c.seq n + -a.seq n
    have h1 : eps (succ k) + a.seq n0 ≤ eps q + c.seq n :=
      TOField.le_trans hA (lower_of_abs (c.isMod q n0 n hc0 (TreeN.le_trans hc0 hn)))
    have h2 : a.seq n ≤ eps q + a.seq n0 := lower_of_abs (a.isMod q n n0 (TreeN.le_trans ha0 hn) ha0)
    have eqA : eps (succ (succ k)) + (eps q + a.seq n0) + eps q = eps (succ k) + a.seq n0 := by
      rw [add_assoc, add_right_comm (eps q) (a.seq n0) (eps q), eps_succ_add, ← add_assoc,
        eps_succ_add]
    have h3 := TOField.add_le_add_right (eps q) (TOField.add_le_add_left (eps (succ (succ k))) h2)
    rw [eqA] at h3
    have h4 := TOField.le_trans h3 h1
    rw [add_comm (eps q) (c.seq n)] at h4
    exact le_sub_iff_add_le (le_of_add_le_add_right h4)
  | inr hB =>
    apply Or.inr
    apply rpos_mk (c := addSeq b (negSeq c))
    refine ⟨succ (succ k), n0, fun n hn => ?_⟩
    show eps (succ (succ k)) ≤ b.seq n + -c.seq n
    have h0 : eps k + a.seq n0 ≤ b.seq n0 := add_le_of_le_sub (hN n0 hN0)
    have h1 : b.seq n0 ≤ eps q + b.seq n := lower_of_abs (b.isMod q n0 n hb0 (TreeN.le_trans hb0 hn))
    have h2 : c.seq n ≤ eps q + c.seq n0 := lower_of_abs (c.isMod q n n0 (TreeN.le_trans hc0 hn) hc0)
    have eqB : eps (succ (succ k)) + (eps q + (eps (succ k) + a.seq n0)) + eps q
        = eps k + a.seq n0 := by
      rw [add_assoc, add_right_comm (eps q) (eps (succ k) + a.seq n0) (eps q), eps_succ_add,
        ← add_assoc, eps_succ_add, ← add_assoc, eps_succ_add]
    have h3 := TOField.add_le_add_right (eps q) (TOField.add_le_add_left (eps (succ (succ k)))
      (TOField.le_trans h2 (TOField.add_le_add_left (eps q) (TOField.le_of_lt hB))))
    rw [eqB] at h3
    have h4 := TOField.le_trans h3 (TOField.le_trans h0 h1)
    rw [add_comm (eps q) (b.seq n)] at h4
    exact le_sub_iff_add_le (le_of_add_le_add_right h4)

/-- Apartness is cotransitive. -/
theorem apart_cotrans {x y : TreeR K} (z : TreeR K) (h : RApart x y) : RApart x z ∨ RApart z y := by
  cases h with
  | inl h =>
    cases lt_cotrans z h with
    | inl h1 => exact Or.inl (Or.inl h1)
    | inr h1 => exact Or.inr (Or.inl h1)
  | inr h =>
    cases lt_cotrans z h with
    | inl h1 => exact Or.inr (Or.inr h1)
    | inr h1 => exact Or.inl (Or.inr h1)

end TreeR
end
