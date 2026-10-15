module

public import TreeAnalysis.CompletenessStrength

@[expose] public section

/-!
# Task 03, Checkpoint C — apartness, inversion and exact algebraic strength

Unconditional results (no additional principle):
* `eq_of_not_not_eq`: equality of reals is `¬¬`-stable (from tightness);
* `eq_zero_of_mul_eq_zero_of_apart` / `..._of_ne`: `x·y = 0` forces `y = 0` both when `x` is
  apart from `0` **and** when merely `x ≠ 0`;
* `mul_left_cancel_of_ne`: cancellation by any `x ≠ 0`;
* `mul_ne_zero'`: a product of two nonzero reals is nonzero;
* `apart_mul`, `apart_of_apart_mul_left`: apartness from `0` is multiplicative;
* `not_not_exists_inv`: every `x ≠ 0` has an inverse *up to double negation*.

Exact logical strength (named propositions, both directions proved):
* `inv_iff_neImpliesApart`: the conventional inverse law `x ≠ 0 → ∃ y, x·y = 1` is
  equivalent to `NeImpliesApart K`;
* `neImpliesApart_iff_markov`: **`NeImpliesApart K` is equivalent to Markov's principle for
  Boolean tests on tree-path counts** (`MarkovPrinciple`);
* `zeroOrApart_iff_lpo`: the decision `x = 0 ∨ RApart x 0` for all reals is equivalent to the
  limited principle of omniscience for Boolean tests on path counts (`LPO`).

The reductions use two explicit constructions: the gap test `gapTest s` on a regular
representative, and the real `markovReal p` built from a Boolean test with `findFirst`.
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TreeR

open TField TOField

variable {K : Type} [TOField K]

/-! ## C1: the conventional inverse law -/

/-- **C1**: the conventional inverse law is equivalent to `NeImpliesApart K`. -/
theorem inv_iff_neImpliesApart :
    (∀ x : TreeR K, x ≠ 𝟘 → ∃ y, x * y = 𝟙) ↔ NeImpliesApart K :=
  ⟨markov_of_inv, fun hM _ hx => exists_inv_of_ne_of_markov hM hx⟩

/-! ## C2: unconditional algebraic laws -/

/-- Equality of reals is stable under double negation (tightness of apartness). -/
theorem eq_of_not_not_eq {x y : TreeR K} (h : ¬¬ (x = y)) : x = y :=
  eq_of_not_apart (fun ha => h (ne_of_apart ha))

theorem eq_zero_of_mul_eq_zero_of_apart {x y : TreeR K} (hx : RApart x 𝟘) (h : x * y = 𝟘) :
    y = 𝟘 := by
  obtain ⟨w, hw⟩ := exists_inv_of_apart hx
  rw [← one_mul y, ← hw, mul_comm x w, mul_assoc, h, mul_zero]

/-- **Zero-product law under mere inequality** (unconditional). -/
theorem eq_zero_of_mul_eq_zero_of_ne {x y : TreeR K} (hx : x ≠ 𝟘) (h : x * y = 𝟘) : y = 𝟘 :=
  eq_of_not_not_eq (fun hy => not_not_apart_of_ne hx
    (fun ha => hy (eq_zero_of_mul_eq_zero_of_apart ha h)))

/-- **Cancellation by any nonzero real** (unconditional). -/
theorem mul_left_cancel_of_ne {x y z : TreeR K} (hx : x ≠ 𝟘) (h : x * y = x * z) : y = z := by
  apply eq_of_add_neg_eq_zero
  apply eq_zero_of_mul_eq_zero_of_ne hx
  rw [left_distrib, mul_neg, h, add_neg_cancel]

theorem mul_left_cancel_of_apart {x y z : TreeR K} (hx : RApart x 𝟘) (h : x * y = x * z) :
    y = z := by
  apply eq_of_add_neg_eq_zero
  apply eq_zero_of_mul_eq_zero_of_apart hx
  rw [left_distrib, mul_neg, h, add_neg_cancel]

/-- A product of nonzero reals is nonzero (unconditional). -/
theorem mul_ne_zero' {x y : TreeR K} (hx : x ≠ 𝟘) (hy : y ≠ 𝟘) : x * y ≠ 𝟘 :=
  fun h => hy (eq_zero_of_mul_eq_zero_of_ne hx h)

/-- Apartness from zero is closed under products. -/
theorem apart_mul {x y : TreeR K} (hx : RApart x 𝟘) (hy : RApart y 𝟘) : RApart (x * y) 𝟘 := by
  obtain ⟨w, hw⟩ := exists_inv_of_apart hx
  obtain ⟨v, hv⟩ := exists_inv_of_apart hy
  apply apart_of_mul_eq_one (y := w * v)
  rw [mul_assoc, mul_left_comm y w v, hv, mul_one, hw]

/-- Apartness of a product from zero gives apartness of each factor. -/
theorem apart_of_apart_mul_left {x y : TreeR K} (h : RApart (x * y) 𝟘) : RApart x 𝟘 := by
  obtain ⟨z, hz⟩ := exists_inv_of_apart h
  apply apart_of_mul_eq_one (y := y * z)
  rw [← mul_assoc]
  exact hz

theorem apart_of_apart_mul_right {x y : TreeR K} (h : RApart (x * y) 𝟘) : RApart y 𝟘 := by
  rw [mul_comm] at h
  exact apart_of_apart_mul_left h

/-- Every nonzero real has an inverse up to double negation (unconditional). -/
theorem not_not_exists_inv {x : TreeR K} (hx : x ≠ 𝟘) : ¬¬ ∃ y, x * y = 𝟙 :=
  fun h => not_not_apart_of_ne hx (fun ha => h (exists_inv_of_apart ha))

/-! ## C3: named logical principles -/

/-- Markov's principle for Boolean tests on tree-path counts. -/
def MarkovPrinciple : Prop :=
  ∀ p : TreeN → Bool, ¬¬ (∃ n, p n = true) → ∃ n, p n = true

/-- The limited principle of omniscience for Boolean tests on tree-path counts. -/
def LPO : Prop := ∀ p : TreeN → Bool, (∃ n, p n = true) ∨ (∀ n, p n = false)

/-- Decision of zero versus apartness for all reals. -/
def ZeroOrApart (K : Type) [TOField K] : Prop := ∀ x : TreeR K, x = 𝟘 ∨ RApart x 𝟘

/-- The disjunctive zero-product law. -/
def ZeroProductDisjunction (K : Type) [TOField K] : Prop :=
  ∀ x y : TreeR K, x * y = 𝟘 → x = 𝟘 ∨ y = 𝟘

theorem bool_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

theorem markov_of_lpo (h : LPO) : MarkovPrinciple := fun p hp =>
  match h p with
  | Or.inl e => e
  | Or.inr hn => False.elim (hp (fun ⟨n, hn'⟩ => by rw [hn n] at hn'; exact nomatch hn'))

/-! ### The gap test on a regular representative -/

/-- Decidable gap test: `3·eps n < |s n|`. -/
def gapTest (s : TreeN → K) (n : TreeN) : Bool := decide (eps n + eps n + eps n < abs (s n))

theorem regular_neg {s : TreeN → K} (hs : IsRegular s) : IsRegular (fun n => -s n) := by
  intro m n
  show abs (-s m + - -s n) ≤ eps m + eps n
  rw [← neg_add, abs_neg]
  exact hs m n

theorem lower_of_gap {s : TreeN → K} (hs : IsRegular s) {n : TreeN}
    (h : eps n + eps n + eps n ≤ s n) {m : TreeN} (hm : PathLE n m) : eps n ≤ s m := by
  have h1 := lower_of_abs (TOField.le_trans (hs n m)
    (TOField.add_le_add_left (eps n) (eps_le_eps (K := K) hm)))
  exact le_of_add_le_add_left (TOField.le_trans h h1)

theorem apart_of_gap {s : TreeN → K} (hs : IsRegular s) {n : TreeN} (h : gapTest s n = true) :
    RApart (mkR (CSeq.ofRegular s hs)) 𝟘 := by
  have hg : eps n + eps n + eps n < abs (s n) := of_decide_eq_true h
  cases TOField.le_or_lt (𝟘 : K) (s n) with
  | inl hp =>
    rw [abs_of_zero_le hp] at hg
    apply Or.inr
    apply (pos_iff _).2
    exact rpos_mk ⟨n, n, fun m hm => lower_of_gap hs (TOField.le_of_lt hg) hm⟩
  | inr hn =>
    rw [abs_of_nonpos (nonneg_of_zero_le (by
      have := TOField.neg_le_neg (TOField.le_of_lt hn)
      rw [neg_zero] at this
      exact this))] at hg
    apply Or.inl
    show RPos (𝟘 + -mkR (CSeq.ofRegular s hs))
    rw [zero_add]
    exact rpos_mk (c := negSeq (CSeq.ofRegular s hs))
      ⟨n, n, fun m hm => lower_of_gap (regular_neg hs) (TOField.le_of_lt hg) hm⟩

theorem eq_zero_of_no_gap {s : TreeN → K} (hs : IsRegular s) (h : ∀ n, gapTest s n = false) :
    mkR (CSeq.ofRegular s hs) = 𝟘 := by
  apply mkR_sound
  intro k
  refine ⟨succ (succ k), fun n hn => ?_⟩
  have h1 : abs (s n) ≤ eps n + eps n + eps n :=
    TOField.le_of_not_lt (fun h' => by
      have := h n
      unfold gapTest at this
      rw [decide_eq_true h'] at this
      exact nomatch this)
  show abs (s n + -𝟘) ≤ eps k
  rw [neg_zero, add_zero]
  have hle := eps_le_eps (K := K) hn
  exact TOField.le_trans h1 (TOField.le_trans
    (TOField.add_le_add (TOField.add_le_add hle hle) hle) (three_eps_le k))

/-! ### The real attached to a Boolean test -/

/-- `eps` of the first success of `p` up to `m`, or `0` if there is none yet. -/
def markovSeq (p : TreeN → Bool) (m : TreeN) : K :=
  cond (p (TreeQ.findFirst p m)) (eps (TreeQ.findFirst p m)) 𝟘

theorem false_below_of_not_found {p : TreeN → Bool} {n : TreeN}
    (h : p (TreeQ.findFirst p n) = false) {j : TreeN} (hj : PathLE j n) : p j = false := by
  have hs := TreeQ.findFirst_spec p n
  have he : TreeQ.findFirst p n = n := by
    cases hs.2 with
    | inl ht => rw [h] at ht; exact nomatch ht
    | inr e => exact e
  cases TreeN.eq_or_lt_of_le hj with
  | inl e => rw [e, ← he]; exact h
  | inr hl => exact hs.1 j (by rw [he]; exact hl)

theorem findFirst_le_of_true {p : TreeN → Bool} {n : TreeN} (m : TreeN) (hp : p n = true) :
    PathLE (TreeQ.findFirst p m) n :=
  TreeN.le_of_not_lt (fun hl => by
    have := (TreeQ.findFirst_spec p m).1 n hl
    rw [hp] at this
    exact nomatch this)

theorem found_of_true {p : TreeN → Bool} {n m : TreeN} (hp : p n = true) (hnm : PathLE n m) :
    p (TreeQ.findFirst p m) = true := by
  cases hq : p (TreeQ.findFirst p m) with
  | true => rfl
  | false =>
    have := false_below_of_not_found hq hnm
    rw [hp] at this
    exact nomatch this

theorem findFirst_eq_of_found {p : TreeN → Bool} {m n : TreeN}
    (hm : p (TreeQ.findFirst p m) = true) (hn : p (TreeQ.findFirst p n) = true) :
    TreeQ.findFirst p m = TreeQ.findFirst p n :=
  match TreeN.compare (TreeQ.findFirst p m) (TreeQ.findFirst p n) with
  | TreeN.Trichotomy.eq e => e
  | TreeN.Trichotomy.lt hl => by
    have := (TreeQ.findFirst_spec p n).1 _ hl
    rw [hm] at this
    exact nomatch this
  | TreeN.Trichotomy.gt hg => by
    have := (TreeQ.findFirst_spec p m).1 _ hg
    rw [hn] at this
    exact nomatch this

theorem markovSeq_nonneg (p : TreeN → Bool) (m : TreeN) : 𝟘 ≤ markovSeq (K := K) p m := by
  unfold markovSeq
  cases p (TreeQ.findFirst p m) with
  | true => exact eps_nonneg _
  | false => exact TOField.le_refl _

theorem markovSeq_isMod (p : TreeN → Bool) : IsModulus (markovSeq (K := K) p) (fun k => k) := by
  have mixed : ∀ k m n : TreeN, PathLE k n → p (TreeQ.findFirst p m) = true →
      p (TreeQ.findFirst p n) = false → abs (markovSeq (K := K) p m + -markovSeq p n) ≤ eps k := by
    intro k m n hn hm hn'
    unfold markovSeq
    rw [hm, hn']
    show abs (eps (TreeQ.findFirst p m) + -𝟘) ≤ eps k
    rw [neg_zero, add_zero, abs_of_pos (eps_pos _)]
    apply eps_le_eps
    apply TreeN.le_trans hn
    cases TreeN.le_or_lt (TreeQ.findFirst p m) n with
    | inl hle =>
      have := false_below_of_not_found hn' hle
      rw [hm] at this
      exact nomatch this
    | inr hl => exact TreeN.le_of_lt hl
  intro k m n hm hn
  cases hpm : p (TreeQ.findFirst p m) with
  | true =>
    cases hpn : p (TreeQ.findFirst p n) with
    | true =>
      have e := findFirst_eq_of_found hpm hpn
      unfold markovSeq
      rw [hpm, hpn]
      show abs (eps (TreeQ.findFirst p m) + -eps (TreeQ.findFirst p n)) ≤ eps k
      rw [e, add_neg_cancel, abs_zero]
      exact eps_nonneg k
    | false => exact mixed k m n hn hpm hpn
  | false =>
    cases hpn : p (TreeQ.findFirst p n) with
    | true =>
      rw [abs_sub_comm]
      exact mixed k n m hm hpn hpm
    | false =>
      unfold markovSeq
      rw [hpm, hpn]
      show abs ((𝟘 : K) + -𝟘) ≤ eps k
      rw [add_neg_cancel, abs_zero]
      exact eps_nonneg k

/-- The real attached to a Boolean test. -/
def markovReal (K : Type) [TOField K] (p : TreeN → Bool) : TreeR K :=
  mkR ⟨markovSeq p, fun k => k, markovSeq_isMod p⟩

theorem markovReal_eq_zero_of_none {p : TreeN → Bool} (h : ∀ n, p n = false) :
    markovReal K p = 𝟘 := by
  apply mkR_sound
  apply seqEquiv_of_eq
  intro n
  show markovSeq p n = 𝟘
  unfold markovSeq
  rw [h (TreeQ.findFirst p n)]
  rfl

theorem none_of_markovReal_eq_zero {p : TreeN → Bool} (h : markovReal K p = 𝟘) (n : TreeN) :
    p n = false := by
  apply bool_false_of_ne_true
  intro hp
  obtain ⟨N, hN⟩ := mkR_exact h (succ n)
  let m := maxN N n
  have hfound := found_of_true hp (TreeN.le_maxN_right N n)
  have h1 : abs (markovSeq (K := K) p m + -𝟘) ≤ eps (succ n) := hN m (TreeN.le_maxN_left _ _)
  unfold markovSeq at h1
  rw [hfound, neg_zero, add_zero] at h1
  have h2 : abs (eps (K := K) (TreeQ.findFirst p m)) ≤ eps (succ n) := h1
  rw [abs_of_pos (eps_pos _)] at h2
  have h3 := eps_le_eps (K := K) (findFirst_le_of_true m hp)
  exact TOField.lt_irrefl _ (TOField.lt_of_le_of_lt (TOField.le_trans h3 h2) (eps_succ_lt n))

theorem exists_true_of_markovReal_apart {p : TreeN → Bool} (h : RApart (markovReal K p) 𝟘) :
    ∃ n, p n = true := by
  cases h with
  | inl hneg =>
    apply False.elim
    have h1 : RPos (𝟘 + -markovReal K p) := hneg
    rw [zero_add] at h1
    obtain ⟨k, N, hN⟩ := seqPos_of_rpos (c := negSeq ⟨markovSeq p, fun k => k, markovSeq_isMod p⟩) h1
    have h2 : eps k ≤ -markovSeq (K := K) p N := hN N (TreeN.le_refl N)
    have h3 := TOField.neg_le_neg (markovSeq_nonneg (K := K) p N)
    rw [neg_zero] at h3
    exact TOField.lt_irrefl _ (TOField.lt_of_lt_of_le (eps_pos (K := K) k) (TOField.le_trans h2 h3))
  | inr hpos =>
    obtain ⟨k, N, hN⟩ := seqPos_of_rpos (c := ⟨markovSeq p, fun k => k, markovSeq_isMod p⟩)
      ((pos_iff _).1 hpos)
    have h2 : eps k ≤ markovSeq (K := K) p N := hN N (TreeN.le_refl N)
    cases hq : p (TreeQ.findFirst p N) with
    | true => exact ⟨_, hq⟩
    | false =>
      apply False.elim
      unfold markovSeq at h2
      rw [hq] at h2
      exact TOField.lt_irrefl _ (TOField.lt_of_lt_of_le (eps_pos (K := K) k) h2)

/-! ### The equivalences -/

theorem neImpliesApart_of_markov (hM : MarkovPrinciple) : NeImpliesApart K := by
  intro x hx
  obtain ⟨s, hs, e⟩ := exists_regular_rep x
  subst e
  obtain ⟨n, hn⟩ := hM (gapTest s) (fun hno => hx (eq_zero_of_no_gap hs
    (fun n => bool_false_of_ne_true (fun ht => hno ⟨n, ht⟩))))
  exact apart_of_gap hs hn

theorem markov_of_neImpliesApart (h : NeImpliesApart K) : MarkovPrinciple := by
  intro p hp
  apply exists_true_of_markovReal_apart (K := K)
  apply h
  intro h0
  exact hp (fun ⟨n, hn⟩ => by rw [none_of_markovReal_eq_zero h0 n] at hn; exact nomatch hn)

/-- **C1/C3: `NeImpliesApart K` is equivalent to Markov's principle** (for any rational base). -/
theorem neImpliesApart_iff_markov : NeImpliesApart K ↔ MarkovPrinciple :=
  ⟨markov_of_neImpliesApart, neImpliesApart_of_markov⟩

/-- Hence the conventional inverse law is equivalent to Markov's principle. -/
theorem inv_iff_markov : (∀ x : TreeR K, x ≠ 𝟘 → ∃ y, x * y = 𝟙) ↔ MarkovPrinciple :=
  Iff.trans inv_iff_neImpliesApart neImpliesApart_iff_markov

theorem zeroOrApart_of_lpo (h : LPO) : ZeroOrApart K := by
  intro x
  obtain ⟨s, hs, e⟩ := exists_regular_rep x
  subst e
  cases h (gapTest s) with
  | inl he =>
    obtain ⟨n, hn⟩ := he
    exact Or.inr (apart_of_gap hs hn)
  | inr hn => exact Or.inl (eq_zero_of_no_gap hs hn)

theorem lpo_of_zeroOrApart (h : ZeroOrApart K) : LPO := by
  intro p
  cases h (markovReal K p) with
  | inl h0 => exact Or.inr (none_of_markovReal_eq_zero h0)
  | inr ha => exact Or.inl (exists_true_of_markovReal_apart ha)

/-- **C3: deciding `x = 0 ∨ RApart x 0` for all reals is equivalent to `LPO`.** -/
theorem zeroOrApart_iff_lpo : ZeroOrApart K ↔ LPO :=
  ⟨lpo_of_zeroOrApart, zeroOrApart_of_lpo⟩

theorem zeroProduct_of_zeroOrApart (h : ZeroOrApart K) : ZeroProductDisjunction K := by
  intro x y hxy
  cases h x with
  | inl hx => exact Or.inl hx
  | inr hx => exact Or.inr (eq_zero_of_mul_eq_zero_of_apart hx hxy)

theorem neImpliesApart_of_zeroOrApart (h : ZeroOrApart K) : NeImpliesApart K := fun x hx =>
  match h x with
  | Or.inl e => absurd e hx
  | Or.inr ha => ha

end TreeR
end
