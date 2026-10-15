module

public import TreeAnalysis.CompletenessStrength

@[expose] public section

/-!
# Task 03, Checkpoint B — minimal lifting principles and sequential completeness

All principles below are **propositions** (`def ... : Prop`).  They are used only as explicit
hypotheses of theorems; none is asserted, and no global instance or axiom is added.

Principles about *quotient representatives*:
* `SequenceLifting K` (Task 02): every sequence of reals has a sequence of representatives;
* `CauchySequenceLifting K`: the same, restricted to Cauchy sequences with a modulus.

Principles about *rational approximants* (no representative of any real is selected):
* `SequenceApprox K`: every sequence of reals has pointwise rational approximants
  `|f i - q i| ≤ eps i`;
* `CauchyApprox K`: every real Cauchy sequence with modulus has approximation data
  (`ApproxData`, with an explicit error schedule).

Principles about *moduli*:
* `ModulusSelection K`: every `RCauchy` sequence of reals has a modulus function;
* `RatModulusSelection K`: every `IsCauchy` rational sequence has a modulus function.

Completeness statements:
* `UnrestrictedCompleteness K` (Task 02): Cauchy sequences **with modulus** converge;
* `ModulusFreeCompleteness K`: `RCauchy` sequences converge.

Main results:
* `complete_iff_cauchyApprox`: **`UnrestrictedCompleteness K` is equivalent to
  `CauchyApprox K`** (both directions proved);
* `complete_of_choice`, `modulusFreeComplete_of_choice`: the countable-choice principle
  `ChoiceNN` (for `TreeN`-valued choices only) suffices for both completeness statements, for every
  rational base `K`.  It is applied to the **numerators of dyadic approximants**, never to
  quotient representatives.
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TreeR

open TField TOField

variable {K : Type} [TOField K]

/-! ## The principles -/

/-- Representative lifting restricted to real Cauchy sequences with a modulus. -/
def CauchySequenceLifting (K : Type) [TOField K] : Prop :=
  ∀ (f : TreeN → TreeR K) (ν : TreeN → TreeN), RCauchyMod f ν →
    ∃ g : TreeN → CSeq K, ∀ i, mkR (g i) = f i

/-- Pointwise rational approximants for every sequence of reals. -/
def SequenceApprox (K : Type) [TOField K] : Prop :=
  ∀ f : TreeN → TreeR K, ∃ q : TreeN → K, ∀ i, RClose (f i) (ofQ (q i)) (eps i)

/-- Approximation data for every real Cauchy sequence with a modulus. -/
def CauchyApprox (K : Type) [TOField K] : Prop :=
  ∀ (f : TreeN → TreeR K) (ν : TreeN → TreeN), RCauchyMod f ν →
    ∃ q : TreeN → K, ∃ M : TreeN → TreeN, ApproxData f q M

/-- Modulus selection for real Cauchy sequences. -/
def ModulusSelection (K : Type) [TOField K] : Prop :=
  ∀ f : TreeN → TreeR K, RCauchy f → ∃ ν : TreeN → TreeN, RCauchyMod f ν

/-- Modulus selection for rational Cauchy sequences. -/
def RatModulusSelection (K : Type) [TOField K] : Prop :=
  ∀ s : TreeN → K, IsCauchy s → ∃ μ : TreeN → TreeN, IsModulus s μ

/-- Sequential completeness for Cauchy sequences without a supplied modulus. -/
def ModulusFreeCompleteness (K : Type) [TOField K] : Prop :=
  ∀ f : TreeN → TreeR K, RCauchy f → ∃ L, ConvergesTo f L

/-! ## Representative lifting -/

theorem cauchyLifting_of_lifting (h : SequenceLifting K) : CauchySequenceLifting K :=
  fun f _ _ => h f

theorem seqApprox_of_lifting (h : SequenceLifting K) : SequenceApprox K := by
  intro f
  obtain ⟨g, hg⟩ := h f
  refine ⟨fun i => approxAt (g i) i, fun i => ?_⟩
  have h1 := approxAt_close (g i) i
  rw [hg i] at h1
  exact h1

theorem cauchyApprox_of_cauchyLifting (h : CauchySequenceLifting K) : CauchyApprox K := by
  intro f ν hc
  obtain ⟨g, hg⟩ := h f ν hc
  refine ⟨fun i => approxAt (g i) i, fun k => k, approxData_of_pointwise (fun i => ?_)⟩
  have h1 := approxAt_close (g i) i
  rw [hg i] at h1
  exact h1

theorem cauchyApprox_of_seqApprox (h : SequenceApprox K) : CauchyApprox K := by
  intro f _ _
  obtain ⟨q, hq⟩ := h f
  exact ⟨q, fun k => k, approxData_of_pointwise hq⟩

/-! ## Completeness is exactly `CauchyApprox` -/

theorem complete_of_cauchyApprox (h : CauchyApprox K) : UnrestrictedCompleteness K := by
  intro f ν hc
  obtain ⟨q, M, hq⟩ := h f ν hc
  exact limit_of_approx hc hq

theorem cauchyApprox_of_complete (h : UnrestrictedCompleteness K) : CauchyApprox K := by
  intro f ν hc
  obtain ⟨L, hL⟩ := h f ν hc
  obtain ⟨c, hcL⟩ := exists_rep L
  refine ⟨fun i => approxAt c i, fun k => maxN (ν (succ k)) (succ k), fun k i hi => ?_⟩
  have h1 := close_of_cauchy_of_converges hc hL (k := succ k) (TreeN.le_of_maxN_le_left hi)
  have h2 := approxAt_close c i
  rw [hcL] at h2
  have h3 := rclose_trans h1 (rclose_mono h2 (eps_le_eps (TreeN.le_of_maxN_le_right hi)))
  rw [eps_succ_add] at h3
  exact h3

/-- **B4: exact characterization.** Sequential completeness (with modulus) holds iff every real
Cauchy sequence with a modulus admits rational approximation data. -/
theorem complete_iff_cauchyApprox :
    (UnrestrictedCompleteness K → CauchyApprox K) ∧ (CauchyApprox K → UnrestrictedCompleteness K) :=
  ⟨cauchyApprox_of_complete, complete_of_cauchyApprox⟩

/-- **B1**: the restricted lifting premise suffices. -/
theorem complete_of_cauchyLifting (h : CauchySequenceLifting K) : UnrestrictedCompleteness K :=
  complete_of_cauchyApprox (cauchyApprox_of_cauchyLifting h)

theorem complete_of_seqApprox (h : SequenceApprox K) : UnrestrictedCompleteness K :=
  complete_of_cauchyApprox (cauchyApprox_of_seqApprox h)

/-! ## Moduli -/

theorem modulusSelection_of_choice (hc : ChoiceNN) : ModulusSelection K := fun f hf => by
  obtain ⟨ν, hν⟩ := hc _ hf
  exact ⟨ν, fun k i j hi hj => hν k i j hi hj⟩

theorem ratModulusSelection_of_modulusSelection (h : ModulusSelection K) :
    RatModulusSelection K := by
  intro s hs
  obtain ⟨ν, hν⟩ := h _ (rcauchy_ofQ_of_isCauchy hs)
  exact ⟨ν, isModulus_of_rcauchyMod_ofQ hν⟩

theorem ratModulusSelection_of_choice (hc : ChoiceNN) : RatModulusSelection K :=
  fun _ hs => exists_modulus_of_choice hc hs

theorem modulusFree_of_modulusSelection (hm : ModulusSelection K)
    (hc : UnrestrictedCompleteness K) : ModulusFreeCompleteness K := by
  intro f hf
  obtain ⟨ν, hν⟩ := hm f hf
  exact hc f ν hν

theorem complete_of_modulusFree (h : ModulusFreeCompleteness K) : UnrestrictedCompleteness K :=
  fun f _ hc => h f (rcauchy_of_rcauchyMod hc)

/-! ## Dyadic approximants and `ChoiceNN` -/

/-- The dyadic rational `(a - b) · eps i` with tree-path numerator data `a, b`. -/
def dyad (i a b : TreeN) : K := (natCast a + -natCast b) * eps i

theorem floor_aux (M : TreeN) : ∀ t : K, 𝟘 ≤ t → t ≤ natCast M →
    ∃ a : TreeN, natCast a ≤ t ∧ t ≤ natCast a + 𝟙 := by
  induction M with
  | nil =>
    intro t h0 h1
    refine ⟨[], h0, TOField.le_trans h1 ?_⟩
    show (𝟘 : K) ≤ 𝟘 + 𝟙
    rw [zero_add]
    exact TOField.zero_le_one
  | cons c M ih =>
    intro t h0 h1
    cases TOField.le_or_lt t (natCast M) with
    | inl h => exact ih t h0 h
    | inr h =>
      refine ⟨M, TOField.le_of_lt h, ?_⟩
      have e : natCast (K := K) (c :: M) = 𝟙 + natCast M := rfl
      rw [e, add_comm] at h1
      exact h1

/-- Every rational lies within `1` of a difference of two path counts (`Prop`-level). -/
theorem exists_floor (y : K) : ∃ a b : TreeN, abs (natCast a + -natCast b + -y) ≤ 𝟙 := by
  let B := archBound (abs y)
  have hB : abs y ≤ natCast B := le_archBound (abs y)
  have hnegy : -y ≤ natCast B := TOField.le_trans (neg_le_abs y) hB
  have h0 : 𝟘 ≤ y + natCast B := by
    have := sub_nonneg_of_le hnegy
    rw [neg_neg, add_comm] at this
    exact this
  have h1 : y + natCast B ≤ natCast (B + B) := by
    rw [natCast_add]
    exact TOField.add_le_add_right _ (TOField.le_trans (le_abs_self y) hB)
  obtain ⟨a, ha1, ha2⟩ := floor_aux (B + B) (y + natCast B) h0 h1
  refine ⟨a, B, ?_⟩
  have e : natCast (K := K) a + -natCast B + -y = natCast a + -(y + natCast B) := by
    rw [neg_add, add_comm (-y), add_assoc]
  rw [e]
  apply abs_le_of
  · have h2 : y + natCast B ≤ 𝟙 + natCast a := by rw [add_comm (𝟙 : K)]; exact ha2
    have h3 := TOField.neg_le_neg (sub_le_of_le_add h2)
    rw [neg_sub'] at h3
    exact h3
  · have h2 : natCast (K := K) a ≤ 𝟘 + (y + natCast B) := by rw [zero_add]; exact ha1
    exact TOField.le_trans (sub_le_of_le_add h2) TOField.zero_le_one

/-- Every real is within `eps i` of a dyadic rational with tree-path numerator data. -/
theorem exists_dyad_close (x : TreeR K) (i : TreeN) :
    ∃ a b : TreeN, RClose x (ofQ (dyad (succ i) a b)) (eps i) := by
  obtain ⟨q, hq⟩ := exists_rat_close x (succ i)
  obtain ⟨a, b, hab⟩ := exists_floor (q * natCast (twoPow (succ i)))
  refine ⟨a, b, ?_⟩
  have hq' : q * natCast (twoPow (succ i)) * eps (succ i) = q := by
    rw [mul_assoc, natCast_twoPow_mul_eps, mul_one]
  have e : dyad (succ i) a b + -q =
      (natCast a + -natCast b + -(q * natCast (twoPow (succ i)))) * eps (succ i) := by
    unfold dyad
    rw [CRing.sub_mul (natCast a + -natCast b) (q * natCast (twoPow (succ i))) (eps (succ i)), hq']
  have hd : abs (dyad (succ i) a b + -q) ≤ eps (K := K) (succ i) := by
    rw [e, abs_mul, abs_of_pos (eps_pos _)]
    have := TOField.mul_le_mul_of_nonneg_right (eps_nonneg (K := K) (succ i)) hab
    rw [one_mul] at this
    exact this
  have h := rclose_trans hq (rclose_symm (rclose_ofQ hd))
  rw [eps_succ_add] at h
  exact h

/-- `ChoiceNN` yields choice for pairs of path counts (two successive applications). -/
theorem choice_pair (hc : ChoiceNN) (P : TreeN → TreeN → TreeN → Prop)
    (h : ∀ i, ∃ a b, P i a b) : ∃ fa fb : TreeN → TreeN, ∀ i, P i (fa i) (fb i) := by
  obtain ⟨fa, hfa⟩ := hc (fun i a => ∃ b, P i a b) h
  obtain ⟨fb, hfb⟩ := hc (fun i b => P i (fa i) b) hfa
  exact ⟨fa, fb, hfb⟩

/-- **`ChoiceNN` gives pointwise rational approximants** for every sequence of reals. -/
theorem seqApprox_of_choice (hc : ChoiceNN) : SequenceApprox K := by
  intro f
  obtain ⟨fa, fb, h⟩ := choice_pair hc
    (fun i a b => RClose (f i) (ofQ (dyad (K := K) (succ i) a b)) (eps i))
    (fun i => exists_dyad_close (f i) i)
  exact ⟨fun i => dyad (succ i) (fa i) (fb i), h⟩

/-- **B1/B3: `ChoiceNN` suffices for sequential completeness (with modulus).** -/
theorem complete_of_choice (hc : ChoiceNN) : UnrestrictedCompleteness K :=
  complete_of_seqApprox (seqApprox_of_choice hc)

/-- **B3: `ChoiceNN` suffices for modulus-free sequential completeness.** -/
theorem modulusFreeComplete_of_choice (hc : ChoiceNN) : ModulusFreeCompleteness K :=
  modulusFree_of_modulusSelection (modulusSelection_of_choice hc) (complete_of_choice hc)

end TreeR
end
