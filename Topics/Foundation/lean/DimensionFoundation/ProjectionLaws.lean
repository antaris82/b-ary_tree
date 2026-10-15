module

public import DimensionFoundation.TransverseBasis
public import DimensionFoundation.BilinearForm

@[expose] public section

/-!
# Projection laws for the decomposition `F_b = L_b ⊕ S_b`

`ChildModule.projL` and `ChildModule.projS` are the projections of `TransverseBasis`.  For every
positive finite arity (`hb : PathLT zero b`) this module proves:

* identity actions: `projL x = x` on `InL`, `projS x = x` on `InS`, derived from the existing
  `decomposition_unique`;
* annihilation: `projL x = 0` on `InS`, `projS x = 0` on `InL` (also from `decomposition_unique`);
* idempotence and complementarity: `projL ∘ projL = projL`, `projS ∘ projS = projS`,
  `projL ∘ projS = 0`, `projS ∘ projL = 0`, `projL x + projS x = x`;
* linearity of both projections (additivity and homogeneity; this part needs no positivity);
* images and kernels: `InL x ↔ projL x = x ↔ ∃ y, x = projL y`, `InS x ↔ projS x = x ↔
  ∃ y, x = projS y`, `InS x ↔ projL x = 0`, `InL x ↔ projS x = 0`;
* orthogonality of the projected components for the coordinate form `dot`.
-/

open CSR CRing TField FinSum ChildModule

namespace ChildModule

variable {K : Type} [TField K] {b : TreeN}

theorem zeroV_inL : InL (zeroV : F K b) := ⟨𝟘, funext fun _ => (zero_mul _).symm⟩

theorem addV_zeroV (x : F K b) : addV x zeroV = x := funext fun i => add_zero (x i)

/-! ## Identity and annihilation actions, from `decomposition_unique` -/

/-- The longitudinal and transverse components of a longitudinal vector `x` are `x` and `0`. -/
theorem proj_of_inL (hb : TreeN.PathLT TreeN.zero b) {x : F K b} (hx : InL x) :
    projL x = x ∧ projS x = zeroV := by
  have h : addV (projL x) (projS x) = addV x zeroV := by
    rw [← decomposition x, addV_zeroV]
  exact decomposition_unique hb (projL_inL x) (projS_inS hb x) hx inS_zero h

/-- The longitudinal and transverse components of a transverse vector `x` are `0` and `x`. -/
theorem proj_of_inS (hb : TreeN.PathLT TreeN.zero b) {x : F K b} (hx : InS x) :
    projL x = zeroV ∧ projS x = x := by
  have h : addV (projL x) (projS x) = addV zeroV x := by
    rw [← decomposition x, zero_addV]
  exact decomposition_unique hb (projL_inL x) (projS_inS hb x) zeroV_inL hx h

theorem projL_of_inL (hb : TreeN.PathLT TreeN.zero b) {x : F K b} (hx : InL x) : projL x = x :=
  (proj_of_inL hb hx).1

theorem projS_of_inL (hb : TreeN.PathLT TreeN.zero b) {x : F K b} (hx : InL x) :
    projS x = zeroV :=
  (proj_of_inL hb hx).2

theorem projL_of_inS (hb : TreeN.PathLT TreeN.zero b) {x : F K b} (hx : InS x) :
    projL x = zeroV :=
  (proj_of_inS hb hx).1

theorem projS_of_inS (hb : TreeN.PathLT TreeN.zero b) {x : F K b} (hx : InS x) : projS x = x :=
  (proj_of_inS hb hx).2

/-! ## Idempotence and complementarity -/

theorem projL_idem (hb : TreeN.PathLT TreeN.zero b) (x : F K b) : projL (projL x) = projL x :=
  projL_of_inL hb (projL_inL x)

theorem projS_idem (hb : TreeN.PathLT TreeN.zero b) (x : F K b) : projS (projS x) = projS x :=
  projS_of_inS hb (projS_inS hb x)

theorem projL_projS (hb : TreeN.PathLT TreeN.zero b) (x : F K b) : projL (projS x) = zeroV :=
  projL_of_inS hb (projS_inS hb x)

theorem projS_projL (hb : TreeN.PathLT TreeN.zero b) (x : F K b) : projS (projL x) = zeroV :=
  projS_of_inL hb (projL_inL x)

theorem projL_addV_projS (x : F K b) : addV (projL x) (projS x) = x := (decomposition x).symm

/-- Summary: for positive arity `projL`, `projS` are complementary idempotents. -/
theorem projections_idempotent_complementary (hb : TreeN.PathLT TreeN.zero b) :
    (∀ x : F K b, projL (projL x) = projL x) ∧
    (∀ x : F K b, projS (projS x) = projS x) ∧
    (∀ x : F K b, projL (projS x) = zeroV) ∧
    (∀ x : F K b, projS (projL x) = zeroV) ∧
    (∀ x : F K b, addV (projL x) (projS x) = x) :=
  ⟨projL_idem hb, projS_idem hb, projL_projS hb, projS_projL hb, projL_addV_projS⟩

/-! ## Linearity -/

theorem projL_addV (x y : F K b) : projL (addV x y) = addV (projL x) (projL y) := by
  unfold projL
  rw [coordSum_addV, left_distrib, add_smul]

theorem projL_smul (a : K) (x : F K b) : projL (smul a x) = smul a (projL x) := by
  unfold projL
  rw [coordSum_smul, mul_left_comm, mul_smul]

theorem projS_addV (x y : F K b) : projS (addV x y) = addV (projS x) (projS y) := by
  unfold projS
  rw [projL_addV]
  funext i
  show x i + y i + -(projL x i + projL y i) = x i + -projL x i + (y i + -projL y i)
  rw [neg_add, add_add_add_comm]

theorem projS_smul (a : K) (x : F K b) : projS (smul a x) = smul a (projS x) := by
  unfold projS
  rw [projL_smul]
  funext i
  show a * x i + -(a * projL x i) = a * (x i + -projL x i)
  rw [left_distrib, mul_neg]

/-! ## Images and kernels -/

theorem inL_iff_projL_eq (hb : TreeN.PathLT TreeN.zero b) (x : F K b) :
    InL x ↔ projL x = x :=
  ⟨projL_of_inL hb, fun h => h ▸ projL_inL x⟩

theorem inS_iff_projS_eq (hb : TreeN.PathLT TreeN.zero b) (x : F K b) :
    InS x ↔ projS x = x :=
  ⟨projS_of_inS hb, fun h => h ▸ projS_inS hb x⟩

/-- The image of `projL` is exactly `L_b`. -/
theorem range_projL (hb : TreeN.PathLT TreeN.zero b) (x : F K b) :
    (∃ y, x = projL y) ↔ InL x :=
  ⟨fun ⟨y, hy⟩ => hy ▸ projL_inL y, fun h => ⟨x, (projL_of_inL hb h).symm⟩⟩

/-- The image of `projS` is exactly `S_b`. -/
theorem range_projS (hb : TreeN.PathLT TreeN.zero b) (x : F K b) :
    (∃ y, x = projS y) ↔ InS x :=
  ⟨fun ⟨y, hy⟩ => hy ▸ projS_inS hb y, fun h => ⟨x, (projS_of_inS hb h).symm⟩⟩

/-- The kernel of `projL` is exactly `S_b`. -/
theorem inS_iff_projL_eq_zero (hb : TreeN.PathLT TreeN.zero b) (x : F K b) :
    InS x ↔ projL x = zeroV := by
  refine ⟨projL_of_inS hb, fun h => ?_⟩
  have e := decomposition x
  rw [h, zero_addV] at e
  rw [e]
  exact projS_inS hb x

/-- The kernel of `projS` is exactly `L_b`. -/
theorem inL_iff_projS_eq_zero (hb : TreeN.PathLT TreeN.zero b) (x : F K b) :
    InL x ↔ projS x = zeroV := by
  refine ⟨projS_of_inL hb, fun h => ?_⟩
  have e : x = projL x := by
    rw [← addV_zeroV (projL x), ← h, ← decomposition x]
  rw [e]
  exact projL_inL x

/-! ## Orthogonality of the projected components -/

/-- Longitudinal vectors are `dot`-orthogonal to transverse vectors. -/
theorem dot_inL_inS {x y : F K b} (hx : InL x) (hy : InS y) : dot x y = 𝟘 := by
  obtain ⟨a, ha⟩ := hx
  rw [ha, dot_smul_left, dot_u_of_inS hy, mul_zero]

/-- For positive arity, the projected components of any two vectors are `dot`-orthogonal. -/
theorem dot_projL_projS (hb : TreeN.PathLT TreeN.zero b) (x y : F K b) :
    dot (projL x) (projS y) = 𝟘 :=
  dot_inL_inS (projL_inL x) (projS_inS hb y)

theorem dot_projS_projL (hb : TreeN.PathLT TreeN.zero b) (x y : F K b) :
    dot (projS x) (projL y) = 𝟘 := by
  rw [dot_comm]
  exact dot_projL_projS hb y x

/-- The coordinate form splits along the decomposition (Pythagorean-type identity; this is an
algebraic identity for the bilinear form, not a positivity statement). -/
theorem dot_split (hb : TreeN.PathLT TreeN.zero b) (x y : F K b) :
    dot x y = dot (projL x) (projL y) + dot (projS x) (projS y) := by
  calc dot x y = dot (addV (projL x) (projS x)) (addV (projL y) (projS y)) := by
        rw [← decomposition x, ← decomposition y]
    _ = dot (projL x) (projL y) + dot (projS x) (projS y) := by
        rw [dot_addV_left, dot_addV_right, dot_addV_right, dot_projL_projS hb,
          dot_projS_projL hb, add_zero, zero_add]

end ChildModule
end
