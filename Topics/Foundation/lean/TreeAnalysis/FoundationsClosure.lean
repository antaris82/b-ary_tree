module

public import TreeAnalysis.Task03Summary
public import TreeNumbers.FoundationsLedger

@[expose] public section

/-!
# Task 04 — embeddings, coherence, and two further exact logical equivalences

* **C3/F. Embedding chain** `TreeN → TreeZ → TreeQ α → TreeR (TreeQ α)` for *every* alphabet with
  two letters (Task 02 only stated it over `Q★`): preservation of `0, 1, +, ·, -`, of the order
  and of the strict order, reflection of the order, injectivity, and agreement of the direct map
  `natR` with the composite.
* **Coherence of the arity isomorphisms of the completions** (identity and composition laws),
  and their compatibility with every embedding.  (Letter-choice independence is proved at the
  rational level, `TreeQ.transfer_letter_indep`; at the real level the carrier
  `TreeR (TreeQ β)` is itself built from the instance, so no such statement is made.)
* **Ordered field `TreeQ α`:** strict monotonicity of multiplication by a positive element.
* **Two new exact equivalences** (both directions proved, named propositions only):
  * `decidableZero_iff_wlpo`: `∀ x : TreeR K, x = 0 ∨ x ≠ 0` is equivalent to `WLPO`;
  * `trichotomy_iff_lpo`: `∀ x y, x < y ∨ x = y ∨ y < x` is equivalent to `LPO`.
-/

open CSR CRing TreeZ TOField TField TreeR TreeQ
open TreeN (PathLE PathLT succ maxN)

/-! ## Ordered-field facts used in the ledger -/

namespace TOField

variable {K : Type} [TOField K]

/-- Multiplication by a strictly positive element is strictly monotone. -/
theorem mul_lt_mul_of_pos_left {x y z : K} (hz : 𝟘 < z) (h : x < y) : z * x < z * y := by
  have hd : 𝟘 < y + -x := by
    apply lt_of_le_of_ne (sub_nonneg_of_le (le_of_lt h))
    intro e
    apply ne_of_lt h
    exact (eq_of_add_neg_eq_zero e.symm).symm
  have hp := mul_pos hz hd
  rw [mul_sub] at hp
  apply lt_of_le_of_ne (le_of_sub_nonneg (le_of_lt hp))
  intro e
  apply ne_of_lt hp
  rw [e, add_neg_cancel]

theorem mul_lt_mul_of_pos_right {x y z : K} (hz : 𝟘 < z) (h : x < y) : x * z < y * z := by
  rw [mul_comm x z, mul_comm y z]
  exact mul_lt_mul_of_pos_left hz h

end TOField

namespace TreeQ

variable {α β γ : Type} [TwoLetters α] [TwoLetters β] [TwoLetters γ]

/-! ## `TreeZ → TreeQ α` -/

theorem ofZ_zero : ofZ (α := α) 𝟘 = 𝟘 := rfl

theorem ofZ_one : ofZ (α := α) 𝟙 = 𝟙 := rfl

theorem ofZ_neg (z : TreeZ) : ofZ (α := α) (-z) = -ofZ z := by
  apply CRing.add_left_cancel (a := ofZ z)
  rw [← ofZ_add, add_neg_cancel, add_neg_cancel]
  rfl

theorem ofZ_lt {z z' : TreeZ} (h : TreeZ.LT z z') : ofZ (α := α) z < ofZ z' := fun h' =>
  h (le_of_ofZ_le h')

theorem lt_of_ofZ_lt {z z' : TreeZ} (h : ofZ (α := α) z < ofZ z') : TreeZ.LT z z' := fun h' =>
  h (ofZ_le h')

/-- The comparison maps fix the image of every tree integer. -/
theorem transfer_ofZ (z : TreeZ) : transfer α β (ofZ z) = ofZ z := transfer_ofF _

end TreeQ

namespace TreeR

variable {α β γ : Type} [TwoLetters α] [TwoLetters β] [TwoLetters γ]

/-! ## `TreeZ → TreeR (TreeQ α)` for every alphabet -/

/-- Embedding of tree integers into the completion over any alphabet with two letters. -/
def ofZRα (z : TreeZ) : TreeR (TreeQ α) := ofQ (ofZ z)

theorem ofZRα_injective {z z' : TreeZ} (h : ofZRα (α := α) z = ofZRα z') : z = z' :=
  ofZ_injective (ofQ_injective h)

theorem ofZRα_zero : ofZRα (α := α) 𝟘 = 𝟘 := rfl

theorem ofZRα_one : ofZRα (α := α) 𝟙 = 𝟙 := rfl

theorem ofZRα_add (z z' : TreeZ) : ofZRα (α := α) (z + z') = ofZRα z + ofZRα z' := by
  unfold ofZRα
  rw [ofZ_add, ofQ_add]

theorem ofZRα_mul (z z' : TreeZ) : ofZRα (α := α) (z * z') = ofZRα z * ofZRα z' := by
  unfold ofZRα
  rw [ofZ_mul, ofQ_mul]

theorem ofZRα_neg (z : TreeZ) : ofZRα (α := α) (-z) = -ofZRα z := by
  unfold ofZRα
  rw [ofZ_neg, ofQ_neg]

theorem ofZRα_le {z z' : TreeZ} (h : TreeZ.LE z z') : ofZRα (α := α) z ≤ ofZRα z' :=
  ofQ_le_ofQ (ofZ_le h)

theorem le_of_ofZRα_le {z z' : TreeZ} (h : ofZRα (α := α) z ≤ ofZRα z') : TreeZ.LE z z' :=
  le_of_ofZ_le (le_of_ofQ_le h)

theorem ofZRα_lt {z z' : TreeZ} (h : TreeZ.LT z z') : ofZRα (α := α) z < ofZRα z' :=
  ofQ_lt_ofQ (ofZ_lt h)

/-- The direct embedding `natR` of path counts agrees with the composite
`TreeN → TreeZ → TreeQ α → TreeR`. -/
theorem natR_eq_ofZRα (n : TreeN) : natR (K := TreeQ α) n = ofZRα (ofN n) := by
  unfold natR ofZRα
  rw [natCast_eq_ofZ]

/-- `natR` preserves and reflects the order of path counts. -/
theorem natR_le_iff (m n : TreeN) : (PathLE m n → natR (K := TreeQ α) m ≤ natR n) ∧
    (natR (K := TreeQ α) m ≤ natR n → PathLE m n) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [natR_eq_ofZRα, natR_eq_ofZRα]
    exact ofZRα_le (ofN_le_ofN h)
  · rw [natR_eq_ofZRα, natR_eq_ofZRα] at h
    exact TreeZ.le_of_ofN_le (le_of_ofZRα_le h)

theorem natR_zero : natR (K := TreeQ α) TreeN.zero = 𝟘 := rfl

/-! ## Coherence of the arity isomorphisms of the completions -/

theorem mapR_congr {K L : Type} [TOField K] [TOField L] {φ ψ : OFieldHom K L}
    (h : ∀ q, φ.toFun q = ψ.toFun q) (x : TreeR K) : mapR φ x = mapR ψ x := by
  induction x using ind_mkR with
  | h a => exact mkR_sound (seqEquiv_of_eq (fun n => h (a.seq n)))

/-- Identity coherence. -/
theorem realArityIso_self (x : TreeR (TreeQ α)) : (realArityIso α α).toFun x = x :=
  mapR_id_of (fun q => transfer_self q) x

/-- Composition coherence. -/
theorem realArityIso_comp (x : TreeR (TreeQ α)) :
    (realArityIso β γ).toFun ((realArityIso α β).toFun x) = (realArityIso α γ).toFun x := by
  show mapR (transferHom β γ) (mapR (transferHom α β) x) = mapR (transferHom α γ) x
  rw [mapR_comp]
  exact mapR_congr (fun q => transfer_comp q) x

/-- The arity isomorphisms commute with the integer embeddings. -/
theorem realArityIso_ofZRα (z : TreeZ) :
    (realArityIso α β).toFun (ofZRα z) = ofZRα z := by
  show ofQ (transfer α β (ofZ z)) = ofQ (ofZ z)
  rw [transfer_ofZ]

/-- The arity isomorphisms commute with the path-count embeddings. -/
theorem realArityIso_natR (n : TreeN) :
    (realArityIso α β).toFun (natR n) = natR n := by
  rw [natR_eq_ofZRα, natR_eq_ofZRα, realArityIso_ofZRα]

end TreeR

/-! ## Two further exact logical equivalences -/

namespace TreeR

variable {K : Type} [TOField K]

/-- Decidability of equality with zero for every real (a named proposition, not assumed). -/
def DecidableZero (K : Type) [TOField K] : Prop := ∀ x : TreeR K, x = 𝟘 ∨ x ≠ 𝟘

/-- Trichotomy of the strict order (a named proposition, not assumed). -/
def Trichotomy (K : Type) [TOField K] : Prop := ∀ x y : TreeR K, x < y ∨ x = y ∨ y < x

theorem wlpo_of_decidableZero (h : DecidableZero K) : WLPO := by
  intro p
  cases h (markovReal K p) with
  | inl h0 => exact Or.inl (none_of_markovReal_eq_zero h0)
  | inr hne => exact Or.inr (fun hall => hne (markovReal_eq_zero_of_none hall))

theorem decidableZero_of_wlpo (h : WLPO) : DecidableZero K := by
  intro x
  obtain ⟨s, hs, e⟩ := exists_regular_rep x
  subst e
  cases h (gapTest s) with
  | inl hall => exact Or.inl (eq_zero_of_no_gap hs hall)
  | inr hnot =>
    apply Or.inr
    intro h0
    apply hnot
    intro n
    apply bool_false_of_ne_true
    intro hn
    exact ne_of_apart (apart_of_gap hs hn) h0

/-- **Deciding `x = 0 ∨ x ≠ 0` for all reals is equivalent to `WLPO`.** -/
theorem decidableZero_iff_wlpo : DecidableZero K ↔ WLPO :=
  ⟨wlpo_of_decidableZero, decidableZero_of_wlpo⟩

theorem zeroOrApart_of_trichotomy (h : Trichotomy K) : ZeroOrApart K := by
  intro x
  cases h x 𝟘 with
  | inl hl => exact Or.inr (Or.inl hl)
  | inr h2 =>
    cases h2 with
    | inl e => exact Or.inl e
    | inr hg => exact Or.inr (Or.inr hg)

theorem trichotomy_of_zeroOrApart (h : ZeroOrApart K) : Trichotomy K := by
  intro x y
  cases h (y + -x) with
  | inl e => exact Or.inr (Or.inl (eq_of_add_neg_eq_zero e).symm)
  | inr ha =>
    cases ha with
    | inl hneg =>
      apply Or.inr
      apply Or.inr
      have h1 : RPos (𝟘 + -(y + -x)) := hneg
      rw [zero_add, neg_sub'] at h1
      exact h1
    | inr hpos =>
      apply Or.inl
      have h1 : RPos (y + -x + -𝟘) := hpos
      rw [sub_zero'] at h1
      exact h1

/-- **Trichotomy of the real order is equivalent to `LPO`.** -/
theorem trichotomy_iff_lpo : Trichotomy K ↔ LPO :=
  ⟨fun h => lpo_of_zeroOrApart (zeroOrApart_of_trichotomy h),
   fun h => trichotomy_of_zeroOrApart (zeroOrApart_of_lpo h)⟩

/-- `LPO` implies the decidability of zero (via `WLPO`). -/
theorem decidableZero_of_lpo (h : LPO) : DecidableZero K := decidableZero_of_wlpo (wlpo_of_lpo h)

end TreeR

end
