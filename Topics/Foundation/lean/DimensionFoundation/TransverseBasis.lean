module

public import DimensionFoundation.FiniteChildModule

@[expose] public section

/-!
# Explicit bases: the longitudinal line and the transverse space

For a positive arity written `b = c :: bp` (so `bp` is the predecessor unary path of `b`):

* `L_b` has the basis `{u_b}` indexed by `Child one` (free of rank one);
* `S_b` has the basis `e_{j+1} − e_0`, `j : Child bp` (free of rank `bp = b − 1`);
* `F_b = L_b ⊕ S_b`, with the projection built from the inverse of the image of `b`.

Linear independence and spanning are proved directly (no counting arguments).  These are
statements about the explicitly constructed algebraic child-coordinate space; they are not
topological dimensions of the graph.  The choice of `u_b` as "longitudinal" is an explicit
algebraic choice.
-/

open CSR CRing TField FinSum ChildModule

namespace TreeN

/-- Predecessor unary path (root ↦ root). -/
def pred : TreeN → TreeN
  | [] => []
  | _ :: n => n

theorem succ_pred {b : TreeN} (h : PathLT zero b) : succ (pred b) = b := by
  cases h with
  | zero_lt c n => cases c; rfl

end TreeN

namespace ChildModule

variable {K : Type} [TField K]

/-- Linear combination, with coefficients indexed by the alphabet `Child n`. -/
def lincomb {n b : TreeN} (coef : Child n → K) (v : Child n → F K b) : F K b :=
  fun i => sumC n (fun j => coef j * v j i)

/-- `v` is a basis of the subspace `P`, indexed by `Child n`: members, closure of linear
combinations, linear independence, and spanning. -/
structure IsBasisOf {n b : TreeN} (P : F K b → Prop) (v : Child n → F K b) : Prop where
  mem : ∀ j, P (v j)
  closed : ∀ coef, P (lincomb coef v)
  indep : ∀ coef, lincomb coef v = zeroV → ∀ j, coef j = 𝟘
  span : ∀ x, P x → ∃ coef, x = lincomb coef v

/-! ## The longitudinal line: free of rank one -/

theorem sumC_arity_one (f : Child TreeN.one → K) : sumC TreeN.one f = f (Child.zeroC _ []) :=
  zero_add _

theorem lincomb_one {b : TreeN} (coef : Child TreeN.one → K) (v : Child TreeN.one → F K b) :
    lincomb coef v = smul (coef (Child.zeroC _ [])) (v (Child.zeroC _ [])) := by
  funext i
  show sumC TreeN.one (fun j => coef j * v j i) = coef (Child.zeroC _ []) * v (Child.zeroC _ []) i
  exact sumC_arity_one _

/-- `L_b` is free of rank one, with basis `u_b` (indexed by the one-letter alphabet). -/
theorem longitudinal_basis (c : UnitChild) (bp : TreeN) :
    IsBasisOf (K := K) (n := TreeN.one) InL (fun _ => u K (c :: bp)) where
  mem := fun _ => inL_u
  closed := fun coef => by
    rw [lincomb_one]
    exact inL_smul _ inL_u
  indep := fun coef h j => by
    rw [lincomb_one] at h
    have e := congrFun h (Child.zeroC c bp)
    have e' : coef (Child.zeroC _ []) * 𝟙 = 𝟘 := e
    rw [mul_one] at e'
    rw [Child.one_unique j]
    exact e'
  span := fun x hx => by
    obtain ⟨a, ha⟩ := hx
    exact ⟨fun _ => a, by rw [lincomb_one]; exact ha⟩

/-! ## The transverse basis `e_{j+1} − e_0` -/

/-- The transverse vector `e_{j+1} − e_0`. -/
def tv (c : UnitChild) (bp : TreeN) (j : Child bp) : F K (c :: bp) :=
  addV (e (Child.shift c j)) (negV (e (Child.zeroC c bp)))

theorem tv_at_shift {c : UnitChild} {bp : TreeN} (j k : Child bp) :
    tv (K := K) c bp j (Child.shift c k) = delta k 𝟙 j := by
  show delta (Child.shift c j) 𝟙 (Child.shift c k) + -delta (Child.zeroC c bp) 𝟙 (Child.shift c k)
    = delta k 𝟙 j
  rw [delta_ne 𝟙 (Child.shift_ne_zeroC c k), neg_zero, add_zero]
  apply delta_cases (Child.shift c j) (Child.shift c k)
    (fun v => v = delta k 𝟙 j) 𝟙
  · intro h
    rw [Child.shift_injective h, delta_self]
  · intro h
    exact (delta_ne 𝟙 (fun e => h (by rw [e]))).symm

theorem tv_at_zero {c : UnitChild} {bp : TreeN} (j : Child bp) :
    tv (K := K) c bp j (Child.zeroC c bp) = -𝟙 := by
  show delta (Child.shift c j) 𝟙 (Child.zeroC c bp) + -delta (Child.zeroC c bp) 𝟙 (Child.zeroC c bp)
    = -𝟙
  rw [delta_ne 𝟙 (fun e => Child.shift_ne_zeroC c j e.symm), delta_self, zero_add]

theorem tv_inS (c : UnitChild) (bp : TreeN) (j : Child bp) : InS (tv (K := K) c bp j) := by
  unfold InS tv
  rw [coordSum_addV, coordSum_negV, coordSum_e, coordSum_e, add_neg_cancel]

theorem lincomb_inS {n b : TreeN} (coef : Child n → K) {v : Child n → F K b}
    (hv : ∀ j, InS (v j)) : InS (lincomb coef v) := by
  unfold InS coordSum lincomb
  rw [sumC_swap]
  have e : ∀ j, sumC b (fun i => coef j * v j i) = 𝟘 := by
    intro j
    rw [sumC_mul_left]
    have h := hv j
    unfold InS coordSum at h
    rw [h, mul_zero]
  rw [sumC_congr e, sumC_zero]

theorem lincomb_tv_at_shift {c : UnitChild} {bp : TreeN} (coef : Child bp → K) (k : Child bp) :
    lincomb coef (tv (K := K) c bp) (Child.shift c k) = coef k := by
  show sumC bp (fun j => coef j * tv c bp j (Child.shift c k)) = coef k
  rw [sumC_congr (fun j => by rw [tv_at_shift]), sumC_congr (fun j => mul_delta coef k j)]
  exact sumC_delta bp k (coef k)

theorem lincomb_tv_at_zero {c : UnitChild} {bp : TreeN} (coef : Child bp → K) :
    lincomb coef (tv (K := K) c bp) (Child.zeroC c bp) = -sumC bp coef := by
  show sumC bp (fun j => coef j * tv c bp j (Child.zeroC c bp)) = -sumC bp coef
  rw [sumC_congr (fun j => by rw [tv_at_zero, mul_neg, mul_one]), sumC_neg]

/-- Linear independence of the transverse family. -/
theorem tv_indep {c : UnitChild} {bp : TreeN} (coef : Child bp → K)
    (h : lincomb coef (tv (K := K) c bp) = zeroV) (j : Child bp) : coef j = 𝟘 := by
  have e := congrFun h (Child.shift c j)
  rw [lincomb_tv_at_shift] at e
  exact e

/-- The transverse family spans `S_b`, with coefficients `x(j+1)`. -/
theorem tv_span {c : UnitChild} {bp : TreeN} (x : F K (c :: bp)) (hx : InS x) :
    x = lincomb (fun j => x (Child.shift c j)) (tv (K := K) c bp) := by
  funext i
  match Child.zeroOrShift c i with
  | Child.ZeroOrShift.zero e =>
    rw [e, lincomb_tv_at_zero]
    unfold InS coordSum at hx
    rw [sumC_first] at hx
    exact add_eq_zero_iff_eq_neg hx
  | Child.ZeroOrShift.shifted k e =>
    rw [e, lincomb_tv_at_shift]

/-- **`S_b` is free of rank `b − 1`**: for `b = c :: bp`, the family `e_{j+1} − e_0` indexed by
`Child bp` (`bp` the predecessor unary path of `b`) is a basis of `S_b`. -/
theorem transverse_basis (c : UnitChild) (bp : TreeN) :
    IsBasisOf (K := K) InS (tv c bp) where
  mem := tv_inS c bp
  closed := fun coef => lincomb_inS coef (tv_inS c bp)
  indep := fun coef h => tv_indep coef h
  span := fun x hx => ⟨_, tv_span x hx⟩

/-- The transverse family is exactly `e_i − e_0` over the nonzero children `i`: the shift is
injective, avoids `0`, and hits every nonzero child. -/
theorem transverse_index_bijection (c : UnitChild) (bp : TreeN) :
    (∀ j j' : Child bp, Child.shift c j = Child.shift c j' → j = j') ∧
    (∀ j : Child bp, Child.shift c j ≠ Child.zeroC c bp) ∧
    (∀ i : Child (c :: bp), i ≠ Child.zeroC c bp → ∃ j, i = Child.shift c j) :=
  ⟨fun _ _ h => Child.shift_injective h, Child.shift_ne_zeroC c, Child.nonzero_is_shift⟩

/-! ## The direct sum decomposition `F_b = L_b ⊕ S_b` -/

/-- Longitudinal projection: `x ↦ (b⁻¹ · Σ_i x(i)) · u_b`. -/
def projL {b : TreeN} (x : F K b) : F K b := smul (inv (natCast b) * coordSum x) (u K b)

/-- Transverse projection: `x ↦ x − projL x`. -/
def projS {b : TreeN} (x : F K b) : F K b := addV x (negV (projL x))

theorem coordSum_smul_u {b : TreeN} (a : K) : coordSum (smul a (u K b)) = a * natCast b := by
  rw [coordSum_smul, coordSum_u]

theorem decomposition {b : TreeN} (x : F K b) : x = addV (projL x) (projS x) := by
  funext i
  show x i = projL x i + (x i + -projL x i)
  rw [add_left_comm, add_neg_cancel, add_zero]

theorem projL_inL {b : TreeN} (x : F K b) : InL (projL x) := ⟨_, rfl⟩

theorem projS_inS {b : TreeN} (hb : TreeN.PathLT TreeN.zero b) (x : F K b) : InS (projS x) := by
  unfold InS projS projL
  rw [coordSum_addV, coordSum_negV, coordSum_smul_u, mul_assoc, mul_comm (coordSum x),
    ← mul_assoc, inv_mul_cancel' (natCast_ne_zero_of_pos hb), one_mul, add_neg_cancel]

/-- Uniqueness of the decomposition, for positive arity. -/
theorem decomposition_unique {b : TreeN} (hb : TreeN.PathLT TreeN.zero b) {l s l' s' : F K b}
    (hl : InL l) (hs : InS s) (hl' : InL l') (hs' : InS s')
    (h : addV l s = addV l' s') : l = l' ∧ s = s' := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨a', ha'⟩ := hl'
  have e := congrArg coordSum h
  rw [coordSum_addV, coordSum_addV, hs, hs', add_zero, add_zero, ha, ha', coordSum_smul_u,
    coordSum_smul_u, mul_comm a, mul_comm a'] at e
  have eaa : a = a' := mul_left_cancel' (natCast_ne_zero_of_pos hb) e
  have ell : l = l' := by rw [ha, ha', eaa]
  refine ⟨ell, ?_⟩
  funext i
  have e2 := congrFun h i
  rw [ell] at e2
  exact add_left_cancel e2

/-- `L_b ∩ S_b = 0` for positive arity. -/
theorem inL_inS_zero {b : TreeN} (hb : TreeN.PathLT TreeN.zero b) {x : F K b} (hl : InL x)
    (hs : InS x) : x = zeroV := by
  have h : addV x zeroV = addV zeroV x := addV_comm _ _
  exact (decomposition_unique hb hl inS_zero ⟨𝟘, funext fun i => (zero_mul _).symm⟩ hs h).1

/-! ## Arity one: the transverse space is zero -/

theorem transverse_one_zero (x : F K TreeN.one) (hx : InS x) : x = zeroV := by
  funext i
  unfold InS coordSum at hx
  rw [sumC_arity_one] at hx
  rw [Child.one_unique i]
  exact hx

/-- For `b = one` the transverse basis is indexed by the empty alphabet `Child zero`. -/
theorem transverse_one_index_empty (j : Child TreeN.zero) : False := Child.zero_empty j

/-! ## Child permutations -/

/-- Child permutations preserve the dot product. -/
theorem dot_perm {b : TreeN} (σ τ : Child b → Child b) (h1 : ∀ i, σ (τ i) = i)
    (h2 : ∀ i, τ (σ i) = i) (x y : F K b) :
    dot (fun i => x (σ i)) (fun i => y (σ i)) = dot x y :=
  sumC_perm σ τ h1 h2 (fun i => x i * y i)

/-- Child permutations preserve `S_b`. -/
theorem inS_perm {b : TreeN} (σ τ : Child b → Child b) (h1 : ∀ i, σ (τ i) = i)
    (h2 : ∀ i, τ (σ i) = i) {x : F K b} (hx : InS x) : InS (fun i => x (σ i)) := by
  unfold InS coordSum at *
  rw [sumC_perm σ τ h1 h2 x]
  exact hx

/-- Child permutations preserve `L_b` (indeed fix `u_b`). -/
theorem inL_perm {b : TreeN} (σ : Child b → Child b) {x : F K b} (hx : InL x) :
    InL (fun i => x (σ i)) := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, by rw [ha]; rfl⟩

end ChildModule
end
