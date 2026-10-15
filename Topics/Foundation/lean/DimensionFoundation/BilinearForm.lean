module

public import DimensionFoundation.FiniteChildModule

@[expose] public section

/-!
# Bilinearity of the finite coordinate form `ChildModule.dot`

`dot x y = sumC b (fun i => x i * y i)` is the symmetric finite coordinate form on
`F_b = Child b → K`.  This module proves the four bilinearity identities (additivity and
homogeneity in each argument) directly from the finite-sum lemmas `FinSum.sumC_add`,
`FinSum.sumC_mul_left`, `FinSum.sumC_congr` and the internal field laws, together with the
derived identities for `zeroV` and `negV`.

Only bilinearity and symmetry are claimed.  No positivity or definiteness is asserted, so the
form is **not** promoted to an inner product here.
-/

open CSR CRing TField FinSum

namespace ChildModule

variable {K : Type} [TField K] {b : TreeN}

/-- Bilinearity (1): additivity in the left argument. -/
theorem dot_addV_left (x y z : F K b) : dot (addV x y) z = dot x z + dot y z := by
  unfold dot
  rw [← sumC_add]
  exact sumC_congr fun i => right_distrib (x i) (y i) (z i)

/-- Bilinearity (2): additivity in the right argument. -/
theorem dot_addV_right (x y z : F K b) : dot x (addV y z) = dot x y + dot x z := by
  unfold dot
  rw [← sumC_add]
  exact sumC_congr fun i => left_distrib (x i) (y i) (z i)

/-- Bilinearity (3): homogeneity in the left argument. -/
theorem dot_smul_left (a : K) (x y : F K b) : dot (smul a x) y = a * dot x y := by
  unfold dot
  rw [← sumC_mul_left]
  exact sumC_congr fun i => mul_assoc a (x i) (y i)

/-- Bilinearity (4): homogeneity in the right argument. -/
theorem dot_smul_right (a : K) (x y : F K b) : dot x (smul a y) = a * dot x y := by
  unfold dot
  rw [← sumC_mul_left]
  exact sumC_congr fun i => mul_left_comm (x i) a (y i)

/-- All four bilinearity identities together with symmetry, in one statement. -/
theorem dot_bilinear_symmetric :
    (∀ x y z : F K b, dot (addV x y) z = dot x z + dot y z) ∧
    (∀ x y z : F K b, dot x (addV y z) = dot x y + dot x z) ∧
    (∀ (a : K) (x y : F K b), dot (smul a x) y = a * dot x y) ∧
    (∀ (a : K) (x y : F K b), dot x (smul a y) = a * dot x y) ∧
    (∀ x y : F K b, dot x y = dot y x) :=
  ⟨dot_addV_left, dot_addV_right, dot_smul_left, dot_smul_right, dot_comm⟩

/-! ## Derived identities -/

theorem dot_zeroV_left (y : F K b) : dot zeroV y = 𝟘 := by
  unfold dot
  exact (sumC_congr (b := b) (g := fun _ => 𝟘) fun i => zero_mul (y i)).trans (sumC_zero b)

theorem dot_zeroV_right (x : F K b) : dot x zeroV = 𝟘 := by
  rw [dot_comm]
  exact dot_zeroV_left x

theorem dot_negV_left (x y : F K b) : dot (negV x) y = -dot x y := by
  unfold dot
  rw [← sumC_neg]
  exact sumC_congr fun i => neg_mul (x i) (y i)

theorem dot_negV_right (x y : F K b) : dot x (negV y) = -dot x y := by
  unfold dot
  rw [← sumC_neg]
  exact sumC_congr fun i => mul_neg (x i) (y i)

end ChildModule
end
