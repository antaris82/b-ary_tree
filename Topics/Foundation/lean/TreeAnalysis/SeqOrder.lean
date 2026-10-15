module

public import TreeAnalysis.CauchyOps

@[expose] public section

/-!
# Order of rational Cauchy data (representative level)

Positivity (`SeqPos`: eventually above a fixed positive precision) and nonnegativity
(`SeqNonneg`: eventually above `-eps k`, for every `k`) of representatives, their closure
properties, and the constructive link between them:

* `seqNonneg_of_not_seqPos_neg`: if `-s` is *not* positive then `s` is nonnegative.  The proof
  uses only the decidable order of the rationals at one explicitly chosen index and the explicit
  Archimedean index function; no excluded middle about real numbers is used.
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TOField

open TField

variable {K : Type} [TOField K]

theorem eps_sub_succ (k : TreeN) : eps (K := K) k + -eps (succ k) = eps (succ k) := by
  rw [← eps_succ_add, add_sub_cancel_right]

theorem neg_eps_succ_add (k : TreeN) :
    -eps (K := K) (succ k) + -eps (succ k) = -eps k := by
  rw [← neg_add, eps_succ_add]

theorem neg_eps_le_zero (k : TreeN) : -eps (K := K) k ≤ 𝟘 := by
  have h := neg_le_neg (eps_nonneg (K := K) k)
  rw [neg_zero] at h
  exact h

theorem seqNonneg_of_eventually_nonneg {s : TreeN → K} (N : TreeN)
    (h : ∀ n, PathLE N n → 𝟘 ≤ s n) : SeqNonneg s := fun k =>
  ⟨N, fun n hn => le_trans (neg_eps_le_zero k) (h n hn)⟩

theorem seqPos_add_nonneg {s t : TreeN → K} (hs : SeqPos s) (ht : SeqNonneg t) :
    SeqPos (fun n => s n + t n) := by
  obtain ⟨k, N, hN⟩ := hs
  obtain ⟨N', hN'⟩ := ht (succ k)
  refine ⟨succ k, maxN N N', fun n hn => ?_⟩
  have h := add_le_add (hN n (TreeN.le_of_maxN_le_left hn)) (hN' n (TreeN.le_of_maxN_le_right hn))
  rw [eps_sub_succ] at h
  exact h

theorem seqPos_add {s t : TreeN → K} (hs : SeqPos s) (ht : SeqPos t) :
    SeqPos (fun n => s n + t n) := seqPos_add_nonneg hs (seqNonneg_of_seqPos ht)

theorem seqNonneg_add {s t : TreeN → K} (hs : SeqNonneg s) (ht : SeqNonneg t) :
    SeqNonneg (fun n => s n + t n) := fun k => by
  obtain ⟨N, hN⟩ := hs (succ k)
  obtain ⟨N', hN'⟩ := ht (succ k)
  refine ⟨maxN N N', fun n hn => ?_⟩
  have h := add_le_add (hN n (TreeN.le_of_maxN_le_left hn)) (hN' n (TreeN.le_of_maxN_le_right hn))
  rw [neg_eps_succ_add] at h
  exact h

theorem seqPos_mul {s t : TreeN → K} (hs : SeqPos s) (ht : SeqPos t) :
    SeqPos (fun n => s n * t n) := by
  obtain ⟨k, N, hN⟩ := hs
  obtain ⟨k', N', hN'⟩ := ht
  refine ⟨k + k', maxN N N', fun n hn => ?_⟩
  rw [eps_add]
  exact mul_le_mul (eps_nonneg k) (hN n (TreeN.le_of_maxN_le_left hn)) (eps_nonneg k')
    (hN' n (TreeN.le_of_maxN_le_right hn))

theorem seqPos_const {q : K} (h : 𝟘 < q) : SeqPos (fun _ => q) :=
  ⟨epsIndex q, TreeN.zero, fun _ _ => le_of_lt (eps_epsIndex_lt h)⟩

theorem not_seqPos_zero : ¬ SeqPos (fun _ => (𝟘 : K)) := by
  intro h
  obtain ⟨k, N, hN⟩ := h
  exact lt_irrefl _ (lt_of_lt_of_le (eps_pos k) (hN N (TreeN.le_refl N)))

theorem seqNonneg_const {q : K} (h : 𝟘 ≤ q) : SeqNonneg (fun _ => q) :=
  seqNonneg_of_eventually_nonneg TreeN.zero (fun _ _ => h)

/-- A nonnegative sequence whose negation is nonnegative is equivalent to `0`. -/
theorem seqEquiv_zero_of_nonneg_nonneg {s : TreeN → K} (h1 : SeqNonneg s)
    (h2 : SeqNonneg (fun n => -s n)) : SeqEquiv s (fun _ => 𝟘) := fun k => by
  obtain ⟨N, hN⟩ := h1 k
  obtain ⟨N', hN'⟩ := h2 k
  refine ⟨maxN N N', fun n hn => ?_⟩
  show abs (s n + -𝟘) ≤ eps k
  rw [neg_zero, add_zero]
  apply abs_le_of (hN n (TreeN.le_of_maxN_le_left hn))
  have h := neg_le_neg (hN' n (TreeN.le_of_maxN_le_right hn))
  rw [neg_neg, neg_neg] at h
  exact h

theorem not_seqPos_neg_of_seqNonneg {s : TreeN → K} (h1 : SeqNonneg s)
    (h2 : SeqPos (fun n => -s n)) : False := by
  obtain ⟨k, N, hN⟩ := h2
  obtain ⟨N', hN'⟩ := h1 (succ k)
  have hn := TreeN.le_maxN_left N N'
  have hn' := TreeN.le_maxN_right N N'
  have a := hN _ hn
  have b := neg_le_neg (hN' _ hn')
  rw [neg_neg] at b
  exact lt_irrefl _ (lt_of_le_of_lt (le_trans a b) (eps_succ_lt k))

/-- **Constructive dichotomy at one index.**  If the negation of a modulated sequence is not
positive, the sequence is nonnegative. -/
theorem seqNonneg_of_not_seqPos_neg (c : CSeq K) (h : ¬ SeqPos (fun n => -c.seq n)) :
    SeqNonneg c.seq := by
  intro k
  let n0 := c.mod (succ k)
  cases le_or_lt (-eps (succ k)) (c.seq n0) with
  | inl h1 =>
    refine ⟨n0, fun n hn => ?_⟩
    have h2 := lower_of_abs (c.isMod (succ k) n0 n (TreeN.le_refl _) hn)
    have h3 := add_le_add_left (-eps (succ k)) (le_trans h1 h2)
    rw [← add_assoc, neg_add_cancel, zero_add, neg_eps_succ_add] at h3
    exact h3
  | inr h1 =>
    apply False.elim
    apply h
    have hδ : 𝟘 < -eps (succ k) + -c.seq n0 := by
      have := add_lt_add_right (-c.seq n0) h1
      rw [add_neg_cancel] at this
      exact this
    refine ⟨epsIndex (-eps (succ k) + -c.seq n0), n0, fun n hn => ?_⟩
    have h2 := lower_of_abs (c.isMod (succ k) n n0 hn (TreeN.le_refl _))
    have h3 := neg_le_neg h2
    rw [neg_add] at h3
    exact le_trans (le_of_lt (eps_epsIndex_lt hδ)) h3

/-! ## Products of nonnegative and positive data -/

theorem nonneg_mul_lower {a b T e : K} (ha : 𝟘 ≤ a) (haT : a ≤ T) (hb : -e ≤ b) (he : 𝟘 ≤ e) :
    -(T * e) ≤ a * b := by
  have h1 := mul_le_mul_of_nonneg_left ha hb
  rw [mul_neg] at h1
  exact le_trans (neg_le_neg (mul_le_mul_of_nonneg_right he haT)) h1

theorem mul_lower {a b T e : K} (haT : abs a ≤ T) (hbT : abs b ≤ T) (ha : -e ≤ a) (hb : -e ≤ b)
    (he : 𝟘 ≤ e) : -(T * e) ≤ a * b := by
  have hT : 𝟘 ≤ T := le_trans (abs_nonneg a) haT
  have hTe : -(T * e) ≤ 𝟘 := by
    have h := neg_le_neg (mul_nonneg hT he)
    rw [neg_zero] at h
    exact h
  cases le_or_lt 𝟘 a with
  | inl ha0 =>
    cases le_or_lt 𝟘 b with
    | inl hb0 => exact le_trans hTe (mul_nonneg ha0 hb0)
    | inr _ => exact nonneg_mul_lower ha0 (le_trans (le_abs_self a) haT) hb he
  | inr ha0 =>
    cases le_or_lt 𝟘 b with
    | inl hb0 =>
      rw [mul_comm a b]
      exact nonneg_mul_lower hb0 (le_trans (le_abs_self b) hbT) ha he
    | inr hb0 =>
      apply le_trans hTe
      rw [← neg_mul_neg]
      have na : 𝟘 ≤ -a := by
        have := neg_le_neg (le_of_lt ha0)
        rw [neg_zero] at this
        exact this
      have nb : 𝟘 ≤ -b := by
        have := neg_le_neg (le_of_lt hb0)
        rw [neg_zero] at this
        exact this
      exact mul_nonneg na nb

theorem abs_le_bnd_add (c d : CSeq K) {n : TreeN} (hn : PathLE (c.mod TreeN.zero) n) :
    abs (c.seq n) ≤ natCast (twoPow (bnd c + bnd d)) :=
  le_trans (abs_le_bnd c hn) (natCast_le (twoPow_le (TreeN.le_add_right _ _)))

theorem seqNonneg_mul (c d : CSeq K) (hc : SeqNonneg c.seq) (hd : SeqNonneg d.seq) :
    SeqNonneg (mulSeq c d).seq := by
  intro k
  let B := bnd c + bnd d
  obtain ⟨N, hN⟩ := hc (k + B)
  obtain ⟨N', hN'⟩ := hd (k + B)
  refine ⟨maxN (maxN N N') (maxN (c.mod TreeN.zero) (d.mod TreeN.zero)), fun n hn => ?_⟩
  have hn1 := TreeN.le_of_maxN_le_left hn
  have hn2 := TreeN.le_of_maxN_le_right hn
  have hcB := abs_le_bnd_add c d (TreeN.le_of_maxN_le_left hn2)
  have hdB : abs (d.seq n) ≤ natCast (twoPow B) := by
    have h := abs_le_bnd_add d c (TreeN.le_of_maxN_le_right hn2)
    rw [TreeN.add_comm] at h
    exact h
  have h := mul_lower hcB hdB (hN n (TreeN.le_of_maxN_le_left hn1))
    (hN' n (TreeN.le_of_maxN_le_right hn1)) (eps_nonneg _)
  rw [mul_comm (natCast _) (eps _), mul_comm (eps _) (natCast _), natCast_twoPow_mul_eps_add] at h
  exact h

end TOField
end
