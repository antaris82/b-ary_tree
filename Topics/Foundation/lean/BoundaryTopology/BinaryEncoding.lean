module

public import BoundaryTopology.ManifoldConditions

@[expose] public section

/-!
# Checkpoint G3 — an explicitly labelled *extra* construction: binary encoding of rays

This is an **extension of the primitive structure**, not part of it: it uses two chosen letters
`l0, l1` and assigns the digit `1` to `l1` and `0` to every other letter.

`encode r := lim_n S r n` with `S r n = Σ_{i<n} digit(r i) · eps (i+1)` (explicit modulus
`k ↦ k`).  Proved:

* `encode_le_of_agree`: rays agreeing up to length `k` have encodings within `eps k`
  (continuity for the prefix topology, in a quantitative form);
* `encode_not_injective`: two rays with an explicitly supplied differing position (`0 1 1 1 …`
  and `1 0 0 0 …`) have the same encoding.

So the encoding is not a homeomorphism onto its image; turning it into a bijection would require
an additional quotient (identification of the two expansions of dyadic values).  Surjectivity
onto an interval is **not** claimed (constructing binary expansions of arbitrary reals would need
decisions of real comparisons that are not available).
-/

open TreeN ListOps Word CSR CRing TOField TreeR

namespace Ray

variable {α K : Type} [DecidableEq α] [TwoLetters α] [TOField K]

/-- The digit of a letter (an explicit labelling choice). -/
def digit (a : α) : K := pickD (decEq a TwoLetters.l1) 𝟙 𝟘

theorem digit_nonneg (a : α) : 𝟘 ≤ digit (K := K) a := by
  unfold digit
  cases decEq a TwoLetters.l1 with
  | isTrue _ => exact TOField.zero_le_one
  | isFalse _ => exact TOField.le_refl _

theorem digit_le_one (a : α) : digit (K := K) a ≤ 𝟙 := by
  unfold digit
  cases decEq a TwoLetters.l1 with
  | isTrue _ => exact TOField.le_refl _
  | isFalse _ => exact TOField.zero_le_one

/-- Partial sums of the binary expansion. -/
def psum (r : Ray α) : TreeN → K
  | [] => 𝟘
  | _ :: n => psum r n + digit (r n) * eps (succ n)

theorem psum_succ (r : Ray α) (n : TreeN) :
    psum (K := K) r (succ n) = psum r n + digit (r n) * eps (succ n) := rfl

theorem digit_mul_eps_nonneg (a : α) (n : TreeN) : 𝟘 ≤ digit (K := K) a * eps n :=
  mul_nonneg (digit_nonneg a) (eps_nonneg n)

theorem digit_mul_eps_le (a : α) (n : TreeN) : digit (K := K) a * eps n ≤ eps n := by
  have h := mul_le_mul_of_nonneg_right (eps_nonneg (K := K) n) (digit_le_one (K := K) a)
  rw [CSR.one_mul] at h
  exact h

/-- Increments: `0 ≤ S(n+d) - S n ≤ eps n - eps (n+d)`. -/
theorem psum_incr (r : Ray α) (n : TreeN) : ∀ d : TreeN,
    psum (K := K) r n ≤ psum r (n + d) ∧ psum (K := K) r (n + d) + eps (n + d) ≤ psum r n + eps n
  | [] => by
    rw [show n + [] = n from TreeN.add_zero n]
    exact ⟨TOField.le_refl _, TOField.le_refl _⟩
  | c :: d => by
    have e : n + c :: d = succ (n + d) := by rw [UnaryPath.cons_eq_extend, add_succ]
    rw [e, psum_succ]
    obtain ⟨h1, h2⟩ := psum_incr r n d
    refine ⟨TOField.le_trans h1 (le_add_of_nonneg_right (digit_mul_eps_nonneg _ _)), ?_⟩
    have h3 := TOField.add_le_add_right (eps (K := K) (succ (n + d)))
      (TOField.add_le_add_left (psum (K := K) r (n + d)) (digit_mul_eps_le (K := K) (r (n + d)) (succ (n + d))))
    rw [CSR.add_assoc (psum (K := K) r (n + d)) (eps _) (eps _), eps_succ_add] at h3
    exact TOField.le_trans h3 h2

theorem psum_close (r : Ray α) {k m n : TreeN} (hm : PathLE k m) (hn : PathLE k n) :
    abs (psum (K := K) r m + -psum r n) ≤ eps k := by
  have key : ∀ {a b : TreeN}, PathLE k a → PathLE a b →
      abs (psum (K := K) r b + -psum r a) ≤ eps k := by
    intro a b ha hab
    obtain ⟨d, hd⟩ := exists_of_le hab
    rw [hd]
    obtain ⟨h1, h2⟩ := psum_incr (K := K) r a d
    rw [abs_of_zero_le (sub_nonneg_of_le h1)]
    apply sub_le_of_le_add
    have h3 := TOField.le_trans (le_add_of_nonneg_right (eps_nonneg (a + d))) h2
    rw [CSR.add_comm (psum r a)] at h3
    exact TOField.le_trans h3 (TOField.add_le_add_right _ (eps_le_eps ha))
  cases le_or_lt m n with
  | inl h =>
    rw [abs_sub_comm]
    exact key hm h
  | inr h => exact key hn (le_of_lt h)

/-- The Cauchy data of the encoding. -/
def encodeSeq (r : Ray α) : CSeq K := ⟨psum r, fun k => k, fun _ _ _ hm hn => psum_close r hm hn⟩

/-- **The binary encoding** of a ray into the completion. -/
def encode (r : Ray α) : TreeR K := mkR (encodeSeq r)

theorem psum_agree {r r' : Ray α} {n : TreeN} (h : Agree n r r') : psum (K := K) r n = psum r' n := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    have h' : r n :: prefixAt r n = r' n :: prefixAt r' n := h
    injection h' with h1 h2
    show psum r n + digit (r n) * eps (succ n) = psum r' n + digit (r' n) * eps (succ n)
    rw [ih h2, h1]

/-- **Continuity** (quantitative): rays agreeing up to length `k` have encodings within
`eps k`. -/
theorem encode_le_of_agree {r r' : Ray α} {k : TreeN} (h : Agree k r r') :
    encode (K := K) r ≤ encode r' + ofQ (eps k) := by
  apply rnonneg_mk (c := addSeq (addSeq (encodeSeq r') (constSeq (eps k))) (negSeq (encodeSeq r)))
  apply seqNonneg_of_eventually_nonneg k
  intro n hn
  show 𝟘 ≤ psum r' n + eps k + -psum r n
  apply sub_nonneg_of_le
  obtain ⟨d, hd⟩ := exists_of_le hn
  rw [hd]
  obtain ⟨h1, h2⟩ := psum_incr (K := K) r k d
  obtain ⟨h1', _⟩ := psum_incr (K := K) r' k d
  have h3 := TOField.le_trans (le_add_of_nonneg_right (eps_nonneg (k + d))) h2
  rw [psum_agree h] at h3
  exact TOField.le_trans h3 (TOField.add_le_add_right _ h1')

/-- The two expansions `0 1 1 1 …` and `1 0 0 0 …`. -/
def rayA : Ray α := modify (const TwoLetters.l1) TreeN.zero TwoLetters.l0
def rayB : Ray α := modify (const TwoLetters.l0) TreeN.zero TwoLetters.l1

theorem digit_l0 : digit (K := K) (TwoLetters.l0 : α) = 𝟘 := pickD_neg TwoLetters.ne _
theorem digit_l1 : digit (K := K) (TwoLetters.l1 : α) = 𝟙 := pickD_pos rfl _

omit [DecidableEq α] in
theorem rayA_zero : rayA (α := α) TreeN.zero = TwoLetters.l0 := modify_at _ _ _
omit [DecidableEq α] in
theorem rayB_zero : rayB (α := α) TreeN.zero = TwoLetters.l1 := modify_at _ _ _
omit [DecidableEq α] in
theorem rayA_succ (n : TreeN) : rayA (α := α) (succ n) = TwoLetters.l1 := by
  unfold rayA modify
  exact pickD_neg (fun e => succ_ne_zero n e) _
omit [DecidableEq α] in
theorem rayB_succ (n : TreeN) : rayB (α := α) (succ n) = TwoLetters.l0 := by
  unfold rayB modify
  exact pickD_neg (fun e => succ_ne_zero n e) _

theorem psum_rayB (n : TreeN) : psum (K := K) (rayB (α := α)) (succ n) = eps (succ TreeN.zero) := by
  induction n with
  | nil =>
    show psum (K := K) (rayB (α := α)) TreeN.zero + digit (rayB (α := α) TreeN.zero) * eps (succ TreeN.zero)
      = eps (succ TreeN.zero)
    rw [rayB_zero, digit_l1, CSR.one_mul]
    exact CSR.zero_add _
  | cons c n ih =>
    have e : c :: n = succ n := UnaryPath.cons_eq_extend c n
    rw [e, psum_succ, ih, rayB_succ, digit_l0, CSR.zero_mul, CSR.add_zero]

theorem psum_rayA (n : TreeN) :
    psum (K := K) (rayA (α := α)) (succ n) + eps (succ n) = eps (succ TreeN.zero) := by
  induction n with
  | nil =>
    show psum (K := K) (rayA (α := α)) TreeN.zero + digit (rayA (α := α) TreeN.zero) * eps (succ TreeN.zero)
      + eps (succ TreeN.zero) = eps (succ TreeN.zero)
    rw [rayA_zero, digit_l0, CSR.zero_mul, CSR.add_zero]
    exact CSR.zero_add _
  | cons c n ih =>
    have e : c :: n = succ n := UnaryPath.cons_eq_extend c n
    rw [e, psum_succ, rayA_succ, digit_l1, CSR.one_mul, CSR.add_assoc, eps_succ_add, ih]

/-- **Non-injectivity**: two rays differing at the explicitly given position `0` have the same
encoding. -/
theorem encode_not_injective :
    rayA (α := α) TreeN.zero ≠ rayB (α := α) TreeN.zero ∧
      encode (K := K) (rayA (α := α)) = encode (rayB (α := α)) := by
  refine ⟨by rw [rayA_zero, rayB_zero]; exact TwoLetters.ne, mkR_sound ?_⟩
  intro k
  refine ⟨succ k, fun n hn => ?_⟩
  obtain ⟨m, hm⟩ := pos_iff_succ (lt_of_lt_of_le (zero_lt_succ k) hn)
  show abs (psum (K := K) (rayA (α := α)) n + -psum (rayB (α := α)) n) ≤ eps k
  rw [hm, psum_rayB (K := K) (α := α), ← psum_rayA (K := K) (α := α) m, add_sub_cancel_right', abs_neg, abs_of_zero_le (eps_nonneg _)]
  rw [hm] at hn
  exact TOField.le_trans (eps_le_eps hn) (eps_succ_le k)
where
  add_sub_cancel_right' (a b : K) : a + -(a + b) = -b := by
    rw [neg_add, ← CSR.add_assoc, add_neg_cancel, CSR.zero_add]

end Ray
end
