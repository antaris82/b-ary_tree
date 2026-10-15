module

public import TreeAnalysis.LiftingPrinciples
public import TreeAnalysis.ApartnessStrength
public import TreeAnalysis.SupremumScope
public import TreeAnalysis.PrimitiveDataScope
public import TreeAnalysis.CompletionCharacterization

@[expose] public section

/-!
# Task 03 — headline results specialized to `TreeRStar = TreeR Q★`

Each statement is a direct instance of the generic theorem named in its proof.
-/

open CSR CRing TreeR

namespace Task03

/-- `TreeRStar` is sequentially complete (with modulus) iff `CauchyApprox Q★` holds. -/
theorem star_complete_iff_cauchyApprox :
    (UnrestrictedCompleteness QStar → CauchyApprox QStar) ∧
    (CauchyApprox QStar → UnrestrictedCompleteness QStar) :=
  complete_iff_cauchyApprox

/-- Under `ChoiceNN`, every `RCauchy` sequence in `TreeRStar` converges. -/
theorem star_modulusFreeComplete_of_choice (hc : ChoiceNN) : ModulusFreeCompleteness QStar :=
  modulusFreeComplete_of_choice hc

/-- In `TreeRStar`, the conventional inverse law is equivalent to Markov's principle. -/
theorem star_inv_iff_markov :
    (∀ x : TreeRStar, x ≠ 𝟘 → ∃ y, x * y = 𝟙) ↔ MarkovPrinciple :=
  inv_iff_markov

/-- In `TreeRStar`, deciding `x = 0 ∨ RApart x 0` for all `x` is equivalent to `LPO`. -/
theorem star_zeroOrApart_iff_lpo : ZeroOrApart QStar ↔ LPO := zeroOrApart_iff_lpo

/-- In `TreeRStar`, `SupData.sup` is the least upper bound. -/
theorem star_supData_isLUB {S : TreeRStar → Prop} (D : SupData S) : IsLUB S D.sup := D.isLUB

/-- Unrestricted least upper bounds in `TreeRStar` would give `WLPO`; bounded monotone
convergence would give `LPO`. -/
theorem star_order_completeness_strength :
    (UnrestrictedLUB QStar → WLPO) ∧ (BoundedMonotoneConvergence QStar → LPO) :=
  ⟨wlpo_of_unrestrictedLUB, lpo_of_bmc⟩

/-- The raw primitive prefix-count sequence of any omega ray is not Cauchy in `Q★`. -/
theorem star_prefixCount_not_isCauchy (r : RayOmega) :
    ¬ TOField.IsCauchy (PrimitiveScope.prefixCount (K := QStar) r) :=
  PrimitiveScope.prefixCount_not_isCauchy r

end Task03
end
