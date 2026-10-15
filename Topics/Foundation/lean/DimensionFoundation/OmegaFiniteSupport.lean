module

public import DimensionFoundation.TransverseBasis

@[expose] public section

/-!
# The omega transverse space of finitely supported functions

At omega arity, `S_omega` consists of functions `TreeN → K` with finite support (a unary-path
bound `B` beyond which all values vanish) whose finite coefficient sum is zero.  Sums are the
structural recursive sums below `B` (independent of the chosen bound).  We prove that the
family `e_{j+1} − e_0` (indexed through `j ↦ succ j` by the positive unary paths) is linearly
independent and spans `S_omega`, and that it is compatible with zero padding from finite
arities.  `K` is any internally constructed rational field (e.g. `TreeQOmega`).
-/

open CSR CRing TField FinSum ChildModule
open TreeN (PathLT PathLE succ)

namespace OmegaModule

variable {K : Type} [TField K]

/-- Functions on the omega child alphabet. -/
abbrev FO (K : Type) : Type := TreeN → K

/-- Sum of `f i` over all `i` below the unary path `B`. -/
def sumUpTo (f : FO K) (B : TreeN) : K := sumC B (fun i => f i.idx)

theorem sumUpTo_cons (f : FO K) (c : UnitChild) (B : TreeN) :
    sumUpTo f (c :: B) = sumUpTo f B + f B := rfl

/-- Support bounded by `B`. -/
def BoundedSupp (f : FO K) (B : TreeN) : Prop := ∀ i, PathLE B i → f i = 𝟘

/-- Finite support. -/
def FinSupp (f : FO K) : Prop := ∃ B, BoundedSupp f B

/-- The omega transverse space: finitely supported, coefficient sum zero. -/
def InSO (f : FO K) : Prop := ∃ B, BoundedSupp f B ∧ sumUpTo f B = 𝟘

theorem sumUpTo_extend {f : FO K} {B : TreeN} (h : BoundedSupp f B) (k : TreeN) :
    sumUpTo f (B + k) = sumUpTo f B := by
  induction k with
  | nil => rw [show B + [] = B from TreeN.add_zero B]
  | cons c k ih =>
    have e : B + c :: k = c :: (B + k) := by cases c; exact TreeN.add_succ B k
    rw [e, sumUpTo_cons, ih, h (B + k) (TreeN.le_add B k), add_zero]

/-- The finite sum does not depend on the chosen support bound. -/
theorem sumUpTo_indep {f : FO K} {B B' : TreeN} (h : BoundedSupp f B) (h' : BoundedSupp f B') :
    sumUpTo f B = sumUpTo f B' := by
  cases TreeN.le_or_lt B B' with
  | inl hle =>
    obtain ⟨k, hk⟩ := TreeN.exists_of_le hle
    rw [hk, sumUpTo_extend h]
  | inr hlt =>
    obtain ⟨k, hk⟩ := TreeN.exists_of_le (TreeN.le_of_lt hlt)
    rw [hk, sumUpTo_extend h']

theorem sumUpTo_first (f : FO K) (B : TreeN) :
    sumUpTo f (succ B) = f TreeN.zero + sumUpTo (fun j => f (succ j)) B :=
  sumC_first B UnitChild.only (fun i => f i.idx)

/-! ## Delta functions on `TreeN` -/

def deltaN (j : TreeN) (a : K) (k : TreeN) : K :=
  match TreeN.decEq k j with
  | isTrue _ => a
  | isFalse _ => 𝟘

theorem deltaN_cases (j k : TreeN) (P : K → Prop) (a : K) (h1 : k = j → P a)
    (h2 : k ≠ j → P 𝟘) : P (deltaN j a k) := by
  unfold deltaN
  cases TreeN.decEq k j with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

theorem deltaN_eq {j k : TreeN} (a : K) (h : k = j) : deltaN j a k = a :=
  deltaN_cases j k (fun v => v = a) a (fun _ => rfl) (fun h' => absurd h h')

theorem deltaN_ne {j k : TreeN} (a : K) (h : k ≠ j) : deltaN j a k = 𝟘 :=
  deltaN_cases j k (fun v => v = 𝟘) a (fun h' => absurd h' h) (fun _ => rfl)

/-- Delta functions on `TreeN` restrict to delta functions on `Child b`. -/
theorem deltaN_idx {b : TreeN} (j i : Child b) (a : K) : deltaN j.idx a i.idx = delta j a i := by
  apply delta_cases j i (fun v => deltaN j.idx a i.idx = v) a
  · intro e
    rw [e]
    exact deltaN_eq a rfl
  · intro ne
    exact deltaN_ne a (fun e => ne (Child.ext e))

theorem sumUpTo_deltaN_lt {j B : TreeN} (a : K) (h : PathLT j B) :
    sumUpTo (deltaN j a) B = a := by
  unfold sumUpTo
  rw [sumC_congr (fun i => deltaN_idx ⟨j, h⟩ i a)]
  exact sumC_delta B ⟨j, h⟩ a

theorem sumUpTo_deltaN_ge {j B : TreeN} (a : K) (h : PathLE B j) :
    sumUpTo (deltaN j a) B = 𝟘 := by
  unfold sumUpTo
  rw [sumC_congr (fun i => deltaN_ne a (fun e => TreeN.not_lt_of_le h (by rw [← e]; exact i.lt)))]
  exact sumC_zero B

/-! ## The omega transverse family -/

/-- Unit vectors `e_i` on `TreeN`. -/
def eO (i : TreeN) : FO K := deltaN i 𝟙

/-- The omega transverse vector `e_{j+1} − e_0`. -/
def tvO (j : TreeN) : FO K := fun k => eO (succ j) k + -eO TreeN.zero k

/-- The index map `j ↦ succ j` is a bijection onto the positive unary paths. -/
theorem positive_index (i : TreeN) (h : PathLT TreeN.zero i) : ∃ j, i = succ j :=
  TreeN.pos_iff_succ h

theorem tvO_at_succ (j k : TreeN) : tvO (K := K) j (succ k) = deltaN k 𝟙 j := by
  show deltaN (succ j) 𝟙 (succ k) + -deltaN TreeN.zero 𝟙 (succ k) = deltaN k 𝟙 j
  rw [deltaN_ne 𝟙 (TreeN.succ_ne_zero k), neg_zero, add_zero]
  apply deltaN_cases (succ j) (succ k) (fun v => v = deltaN k 𝟙 j) 𝟙
  · intro e
    exact (deltaN_eq 𝟙 (TreeN.succ_injective e).symm).symm
  · intro ne
    exact (deltaN_ne 𝟙 (fun e => ne (by rw [e]))).symm

theorem tvO_at_zero (j : TreeN) : tvO (K := K) j TreeN.zero = -𝟙 := by
  show deltaN (succ j) 𝟙 TreeN.zero + -deltaN TreeN.zero 𝟙 TreeN.zero = -𝟙
  rw [deltaN_ne 𝟙 (fun e => TreeN.succ_ne_zero j e.symm), deltaN_eq 𝟙 rfl, zero_add]

/-- Finite linear combinations with coefficients supported below `B`. -/
def lincombO (coef : FO K) (B : TreeN) : FO K := fun k => sumUpTo (fun j => coef j * tvO j k) B

theorem mul_deltaN (coef : FO K) (k j : TreeN) : coef j * deltaN k 𝟙 j = deltaN k (coef k) j := by
  apply deltaN_cases k j (fun v => coef j * v = deltaN k (coef k) j) 𝟙
  · intro e
    rw [e, mul_one, deltaN_eq _ rfl]
  · intro ne
    rw [mul_zero, deltaN_ne _ ne]

theorem lincombO_at_succ (coef : FO K) (B k : TreeN) :
    lincombO coef B (succ k) = sumUpTo (deltaN k (coef k)) B := by
  unfold lincombO sumUpTo
  apply sumC_congr
  intro i
  show coef i.idx * tvO i.idx (succ k) = deltaN k (coef k) i.idx
  rw [tvO_at_succ, mul_deltaN]

theorem lincombO_at_zero (coef : FO K) (B : TreeN) :
    lincombO coef B TreeN.zero = -sumUpTo coef B := by
  unfold lincombO sumUpTo
  rw [← sumC_neg]
  apply sumC_congr
  intro i
  show coef i.idx * tvO i.idx TreeN.zero = -coef i.idx
  rw [tvO_at_zero, mul_neg, mul_one]

/-- **Linear independence** of the omega transverse family. -/
theorem tvO_indep (coef : FO K) (B : TreeN) (hc : BoundedSupp coef B)
    (h : lincombO coef B = fun _ => 𝟘) (j : TreeN) : coef j = 𝟘 := by
  cases TreeN.le_or_lt B j with
  | inl hle => exact hc j hle
  | inr hlt =>
    have e := congrFun h (succ j)
    rw [lincombO_at_succ, sumUpTo_deltaN_lt _ hlt] at e
    exact e

/-- **Spanning**: every element of `S_omega` is a finite combination of `e_{j+1} − e_0`. -/
theorem tvO_span (f : FO K) (hf : InSO f) :
    ∃ coef : FO K, ∃ B, BoundedSupp coef B ∧ f = lincombO coef B := by
  obtain ⟨B, hB, hs⟩ := hf
  refine ⟨fun j => f (succ j), B, ?_, ?_⟩
  · intro j hj
    exact hB (succ j) (TreeN.le_trans hj (TreeN.le_of_lt (TreeN.lt_succ_self j)))
  · funext k
    cases k with
    | nil =>
      show f TreeN.zero = lincombO _ B TreeN.zero
      rw [lincombO_at_zero]
      have e := sumUpTo_first f B
      rw [show succ B = UnitChild.only :: B from rfl, sumUpTo_cons, hs, hB B (TreeN.le_refl B),
        add_zero] at e
      exact add_eq_zero_iff_eq_neg e.symm
    | cons c k =>
      rw [show c :: k = succ k by cases c; rfl, lincombO_at_succ]
      cases TreeN.le_or_lt B k with
      | inl hle =>
        rw [sumUpTo_deltaN_ge _ hle]
        exact hB (succ k) (TreeN.le_trans hle (TreeN.le_of_lt (TreeN.lt_succ_self k)))
      | inr hlt =>
        rw [sumUpTo_deltaN_lt _ hlt]

/-- Finite combinations of the family lie in `S_omega`. -/
theorem lincombO_inSO (coef : FO K) (B : TreeN) : InSO (lincombO coef B) := by
  refine ⟨succ B, ?_, ?_⟩
  · intro k hk
    cases k with
    | nil => exact absurd hk (fun h => nomatch h)
    | cons c k =>
      rw [show c :: k = succ k by cases c; rfl, lincombO_at_succ]
      apply sumUpTo_deltaN_ge
      cases hk with
      | succ_le _ _ h => exact h
  · rw [sumUpTo_first, lincombO_at_zero]
    have e : sumUpTo (fun j => lincombO coef B (succ j)) B = sumUpTo coef B := by
      unfold sumUpTo
      apply sumC_congr
      intro i
      show lincombO coef B (succ i.idx) = coef i.idx
      rw [lincombO_at_succ, sumUpTo_deltaN_lt _ i.lt]
    rw [e, neg_add_cancel]

/-! ## Compatibility with zero padding from finite arities -/

/-- Zero padding of a finite-arity coordinate vector to an omega function. -/
def pad {b : TreeN} (x : F K b) : FO K := fun k =>
  match TreeN.decLT k b with
  | isTrue h => x ⟨k, h⟩
  | isFalse _ => 𝟘

theorem pad_lt {b : TreeN} (x : F K b) {k : TreeN} (h : PathLT k b) : pad x k = x ⟨k, h⟩ := by
  unfold pad
  cases TreeN.decLT k b with
  | isTrue _ => rfl
  | isFalse h' => exact absurd h h'

theorem pad_ge {b : TreeN} (x : F K b) {k : TreeN} (h : ¬ PathLT k b) : pad x k = 𝟘 := by
  unfold pad
  cases TreeN.decLT k b with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl

theorem pad_idx {b : TreeN} (x : F K b) (i : Child b) : pad x i.idx = x i := pad_lt x i.lt

theorem pad_injective {b : TreeN} {x y : F K b} (h : pad x = pad y) : x = y := by
  funext i
  rw [← pad_idx x i, ← pad_idx y i, h]

theorem pad_bounded {b : TreeN} (x : F K b) : BoundedSupp (pad x) b :=
  fun _ hk => pad_ge x (TreeN.not_lt_of_le hk)

theorem pad_finSupp {b : TreeN} (x : F K b) : FinSupp (pad x) := ⟨b, pad_bounded x⟩

theorem sumUpTo_pad {b : TreeN} (x : F K b) : sumUpTo (pad x) b = coordSum x :=
  sumC_congr (fun i => pad_idx x i)

/-- Zero padding maps `S_b` into `S_omega`. -/
theorem pad_inSO {b : TreeN} {x : F K b} (hx : InS x) : InSO (pad x) :=
  ⟨b, pad_bounded x, by rw [sumUpTo_pad]; exact hx⟩

theorem pad_addV {b : TreeN} (x y : F K b) : pad (addV x y) = fun k => pad x k + pad y k := by
  funext k
  cases TreeN.decLT k b with
  | isTrue h => rw [pad_lt _ h, pad_lt _ h, pad_lt _ h]; rfl
  | isFalse h => rw [pad_ge _ h, pad_ge _ h, pad_ge _ h, add_zero]

theorem pad_smul {b : TreeN} (a : K) (x : F K b) : pad (smul a x) = fun k => a * pad x k := by
  funext k
  cases TreeN.decLT k b with
  | isTrue h => rw [pad_lt _ h, pad_lt _ h]; rfl
  | isFalse h => rw [pad_ge _ h, pad_ge _ h, mul_zero]

/-- Zero padding sends the finite transverse basis vector `e_{j+1} − e_0` to the omega
transverse basis vector with the same intrinsic index. -/
theorem pad_tv (c : UnitChild) (bp : TreeN) (j : Child bp) :
    pad (tv (K := K) c bp j) = tvO j.idx := by
  funext k
  cases TreeN.decLT k (c :: bp) with
  | isTrue h =>
    rw [pad_lt _ h]
    show delta (Child.shift c j) 𝟙 ⟨k, h⟩ + -delta (Child.zeroC c bp) 𝟙 ⟨k, h⟩
      = deltaN (succ j.idx) 𝟙 k + -deltaN TreeN.zero 𝟙 k
    rw [← deltaN_idx, ← deltaN_idx]
    rfl
  | isFalse h =>
    rw [pad_ge _ h]
    show 𝟘 = deltaN (succ j.idx) 𝟙 k + -deltaN TreeN.zero 𝟙 k
    rw [deltaN_ne 𝟙 (fun e => h (by rw [e]; exact (Child.shift c j).lt)),
      deltaN_ne 𝟙 (fun e => h (by rw [e]; exact (Child.zeroC c bp).lt)), neg_zero, add_zero]

/-- The zero-padding inclusion `F_b → F_{succ b}`. -/
def padSucc {b : TreeN} (x : F K b) : F K (succ b) := fun i => pad x i.idx

/-- Padding is compatible with the finite-arity zero-padding inclusions. -/
theorem pad_padSucc {b : TreeN} (x : F K b) : pad (padSucc x) = pad x := by
  funext k
  cases TreeN.decLT k (succ b) with
  | isTrue h => rw [pad_lt _ h]; rfl
  | isFalse h =>
    rw [pad_ge _ h, pad_ge x (fun h' => h (TreeN.lt_trans h' (TreeN.lt_succ_self b)))]

/-- The zero-padding inclusion maps `S_b` into `S_{succ b}`. -/
theorem padSucc_inS {b : TreeN} {x : F K b} (hx : InS x) : InS (padSucc x) := by
  unfold InS coordSum at *
  show sumC (UnitChild.only :: b) (padSucc x) = 𝟘
  rw [sumC_cons]
  have e1 : ∀ i, padSucc x (Child.incl UnitChild.only i) = x i := fun i => pad_idx x i
  rw [sumC_congr e1, hx, zero_add]
  exact pad_ge x (TreeN.lt_irrefl b)

/-- The zero-padding inclusion maps the transverse basis of arity `c :: bp` to the
corresponding transverse basis vectors of arity `succ (c :: bp)`. -/
theorem padSucc_tv (c : UnitChild) (bp : TreeN) (j : Child bp) :
    padSucc (tv (K := K) c bp j) = tv UnitChild.only (c :: bp) (Child.incl c j) := by
  apply pad_injective
  rw [pad_padSucc, pad_tv, pad_tv]
  rfl

end OmegaModule
end
