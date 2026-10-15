module

public import TreeAnalysis.FoundationsClosure

@[expose] public section

/-!
# Task 04, C3/F — canonicity of the arity isomorphisms

Arity independence was proved in Tasks 01/02 by explicit comparison maps (`transfer`,
`realArityIso`). Here these maps are shown to be the **only** isomorphisms of their kind:

* `TreeQ.fieldIso_unique`: every field isomorphism `TreeQ α → TreeQ β` (preserving `0, 1, +, ·,
  -, inv`) equals `transfer α β`.  The proof uses only `map_zero`, `map_one`, `map_add`,
  `map_neg` and `map_mul`: such a map fixes path counts, hence integers, hence every fraction.
* `TreeR.realIso_unique`: every isomorphism of the completions preserving `0, 1, +, ·, -` and the
  strict order in both directions (`RealIso`) equals `realArityIso α β`.  The proof fixes the
  rationals as above and then uses rational density and tightness (`eq_of_not_apart`).

Together with `TreeQ.transfer_letter_indep`, this shows that the comparison does not depend on any
letter choice.  Existence of the witness *triples* still uses two distinguished letters
(`TreeQ.ofFrac_letter_dependent`).
-/

open CSR CRing TreeZ TOField TField TreeR TreeQ TriplePath


namespace TreeQ
variable {α β : Type} [TwoLetters α] [TwoLetters β]
/-- Clearing the denominator of a fraction class. -/
theorem ofZ_den_mul_ofF (f : Frac) : ofZ (α := α) (ofN f.den) * ofF f = ofZ f.num := by
  unfold ofZ
  rw [mul_ofF]
  apply ofF_sound
  show ofN f.den * f.num * ofN TreeN.one = f.num * ofN (TreeN.one * f.den)
  rw [ofN_one, mul_one, TreeN.one_mul, mul_comm]
theorem ofZ_ofN_ne_zero {d : TreeN} (h : TreeN.PathLT TreeN.zero d) : ofZ (α := α) (ofN d) ≠ 𝟘 := by
  intro e
  rw [← ofZ_zero] at e
  exact ofN_ne_zero h (ofZ_injective e)
end TreeQ

namespace TreeQ
variable {α β : Type} [TwoLetters α] [TwoLetters β]

theorem fieldIso_natCast (φ : FieldIso (TreeQ α) (TreeQ β)) (n : TreeN) :
    φ.toFun (natCast n) = natCast n := by
  induction n with
  | nil => exact φ.map_zero
  | cons c n ih => rw [natCast_cons, natCast_cons, φ.map_add, φ.map_one, ih]

theorem fieldIso_ofZ (φ : FieldIso (TreeQ α) (TreeQ β)) (z : TreeZ) :
    φ.toFun (ofZ z) = ofZ z := by
  rw [← mkZ_self z, mkZ_eq_sub, ofZ_add, ofZ_add, ofZ_neg, ofZ_neg, φ.map_add, φ.map_neg,
    ← natCast_eq_ofZ, ← natCast_eq_ofZ, fieldIso_natCast, fieldIso_natCast, natCast_eq_ofZ,
    natCast_eq_ofZ]

/-- **Canonicity**: every field isomorphism between two triple-path rational fields equals the
comparison map `transfer`. -/
theorem fieldIso_unique (φ : FieldIso (TreeQ α) (TreeQ β)) (x : TreeQ α) :
    φ.toFun x = transfer α β x := by
  induction x using ind_ofF with
  | h f =>
    rw [transfer_ofF]
    apply mul_left_cancel' (ofZ_ofN_ne_zero (α := β) f.pos)
    have h1 := congrArg φ.toFun (ofZ_den_mul_ofF (α := α) f)
    rw [φ.map_mul, fieldIso_ofZ, fieldIso_ofZ] at h1
    rw [h1, ofZ_den_mul_ofF]

/-- In particular any two field isomorphisms agree. -/
theorem fieldIso_ext (φ ψ : FieldIso (TreeQ α) (TreeQ β)) (x : TreeQ α) : φ.toFun x = ψ.toFun x := by
  rw [fieldIso_unique φ, fieldIso_unique ψ]
end TreeQ

namespace TreeR
variable {α β : Type} [TwoLetters α] [TwoLetters β]

theorem natR_cons (c : UnitChild) (n : TreeN) : natR (K := TreeQ α) (c :: n) = 𝟙 + natR n := by
  unfold natR
  rw [natCast_cons, ofQ_add]
  rfl

theorem realIso_natR (φ : RealIso (TreeR (TreeQ α)) (TreeR (TreeQ β))) (n : TreeN) :
    φ.toFun (natR n) = natR n := by
  induction n with
  | nil => exact φ.map_zero
  | cons c n ih => rw [natR_cons, natR_cons, φ.map_add, φ.map_one, ih]

theorem realIso_ofZRα (φ : RealIso (TreeR (TreeQ α)) (TreeR (TreeQ β))) (z : TreeZ) :
    φ.toFun (ofZRα z) = ofZRα z := by
  rw [← mkZ_self z, mkZ_eq_sub, ofZRα_add, ofZRα_add, ofZRα_neg, ofZRα_neg, φ.map_add, φ.map_neg,
    ← natR_eq_ofZRα, ← natR_eq_ofZRα, realIso_natR, realIso_natR, natR_eq_ofZRα, natR_eq_ofZRα]

theorem realIso_ofQ (φ : RealIso (TreeR (TreeQ α)) (TreeR (TreeQ β))) (q : TreeQ α) :
    φ.toFun (ofQ q) = ofQ (transfer α β q) := by
  induction q using ind_ofF with
  | h f =>
    rw [transfer_ofF]
    have hne : ofZRα (α := β) (ofN f.den) ≠ 𝟘 := fun e =>
      TreeQ.ofZ_ofN_ne_zero (α := β) f.pos (ofQ_injective e)
    apply mul_left_cancel_of_ne hne
    have h1 : ofZRα (α := α) (ofN f.den) * ofQ (ofF f) = ofZRα f.num := by
      unfold ofZRα
      rw [← ofQ_mul, TreeQ.ofZ_den_mul_ofF]
    have h2 := congrArg φ.toFun h1
    rw [φ.map_mul, realIso_ofZRα, realIso_ofZRα] at h2
    rw [h2]
    unfold ofZRα
    rw [← ofQ_mul, TreeQ.ofZ_den_mul_ofF]

/-- **Canonicity of the arity isomorphism of the completions**: every isomorphism of completed
ordered rings (preserving `0, 1, +, ·, -` and `<` in both directions) equals `realArityIso`. -/
theorem realIso_unique (φ : RealIso (TreeR (TreeQ α)) (TreeR (TreeQ β))) (x : TreeR (TreeQ α)) :
    φ.toFun x = (realArityIso α β).toFun x := by
  have hinvQ : ∀ q : TreeQ β, φ.invFun (ofQ q) = ofQ (transfer β α q) := by
    intro q
    have e := φ.left_inv (ofQ (transfer β α q))
    rw [realIso_ofQ, transfer_transfer] at e
    exact e
  apply eq_of_not_apart
  intro ha
  cases ha with
  | inl hlt =>
    obtain ⟨q, hq1, hq2⟩ := exists_rat_between hlt
    have h3 := φ.inv_map_lt _ _ hq1
    rw [φ.left_inv, hinvQ] at h3
    have h4 := (realArityIso α β).map_lt _ _ h3
    rw [realArityIso_ofQ, transfer_transfer] at h4
    exact TreeR.lt_irrefl _ (TreeR.lt_trans h4 hq2)
  | inr hlt =>
    obtain ⟨q, hq1, hq2⟩ := exists_rat_between hlt
    have h3 := φ.inv_map_lt _ _ hq2
    rw [φ.left_inv, hinvQ] at h3
    have h4 := (realArityIso α β).map_lt _ _ h3
    rw [realArityIso_ofQ, transfer_transfer] at h4
    exact TreeR.lt_irrefl _ (TreeR.lt_trans hq1 h4)
end TreeR

end
