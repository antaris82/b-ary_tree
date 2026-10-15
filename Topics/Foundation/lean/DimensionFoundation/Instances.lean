module

public import DimensionFoundation.BoundaryLongitudinal
public import TreeNumbers.RationalArityIndependence

@[expose] public section

/-!
# The dimension results over the concrete tree-rational fields

Specializations of the generic statements to `K := TreeQb b` (finite arity `b ≥ 2`, so
`F_b = Child b → TreeQ(b)`) and to `K := TreeQOmega` (any positive arity, including `b = one`,
and the omega transverse space).
-/

open ChildModule OmegaModule

/-- `S_b ⊆ Child b → TreeQ(b)` is free of rank `b − 1` (here `b = c :: bp`, `b ≥ 2`). -/
theorem transverse_basis_treeQ (c : UnitChild) (bp : TreeN) [AtLeastTwo (c :: bp)] :
    IsBasisOf (K := TreeQb (c :: bp)) InS (tv c bp) :=
  transverse_basis c bp

/-- `L_b ⊆ Child b → TreeQ(b)` is free of rank one. -/
theorem longitudinal_basis_treeQ (c : UnitChild) (bp : TreeN) [AtLeastTwo (c :: bp)] :
    IsBasisOf (K := TreeQb (c :: bp)) (n := TreeN.one) InL (fun _ => u (TreeQb (c :: bp)) (c :: bp)) :=
  longitudinal_basis c bp

/-- `F_b = L_b ⊕ S_b` over `TreeQ(b)`: existence and uniqueness of the decomposition. -/
theorem direct_sum_treeQ (c : UnitChild) (bp : TreeN) [AtLeastTwo (c :: bp)]
    (x : F (TreeQb (c :: bp)) (c :: bp)) :
    (x = addV (projL x) (projS x) ∧ InL (projL x) ∧ InS (projS x)) ∧
    ∀ l s l' s' : F (TreeQb (c :: bp)) (c :: bp), InL l → InS s → InL l' → InS s' →
      addV l s = addV l' s' → l = l' ∧ s = s' :=
  ⟨⟨decomposition x, projL_inL x, projS_inS (TreeN.PathLT.zero_lt c bp) x⟩,
    fun _ _ _ _ hl hs hl' hs' h =>
      decomposition_unique (TreeN.PathLT.zero_lt c bp) hl hs hl' hs' h⟩

/-- Arity one over `TreeQOmega`: the transverse space is zero. -/
theorem transverse_one_zero_omega (x : F TreeQOmega TreeN.one) (hx : InS x) : x = zeroV :=
  transverse_one_zero x hx

/-- The omega transverse family over `TreeQOmega` is linearly independent. -/
theorem omega_indep (coef : FO TreeQOmega) (B : TreeN) (hc : BoundedSupp coef B)
    (h : lincombO coef B = fun _ => CSR.zero) (j : TreeN) : coef j = CSR.zero :=
  tvO_indep coef B hc h j

/-- The omega transverse family over `TreeQOmega` spans `S_omega`. -/
theorem omega_span (f : FO TreeQOmega) (hf : InSO f) :
    ∃ coef : FO TreeQOmega, ∃ B, BoundedSupp coef B ∧ f = lincombO coef B :=
  tvO_span f hf

end
