module

public import TreeNumbers.FieldInterface
public import PrimitiveTree.FiniteChild

@[expose] public section

/-!
# Finite sums over the constructed finite alphabets

`sumBelow B g` sums `g i` over all unary-path indices `i` below `B`, by structural recursion
on the unary path `B` (an explicit enumeration of the alphabet in index order).
`sumC b f` is the resulting sum over `Child b`.  It is shown to agree with the fold over the
explicit list enumeration `Child.enum b` (`sumC_eq_fold`).  No `Fin`, no numeric indices.
-/

open CSR CRing TField ListOps

namespace Child

/-- The child `0` of a positive arity `c :: bp`. -/
def zeroC (c : UnitChild) (bp : TreeN) : Child (c :: bp) := ⟨TreeN.zero, TreeN.PathLT.zero_lt c bp⟩

/-- Shift `j ↦ j+1` from `Child bp` to the nonzero children of `Child (c :: bp)`. -/
def shift {bp : TreeN} (c : UnitChild) (j : Child bp) : Child (c :: bp) :=
  ⟨TreeN.succ j.idx, TreeN.PathLT.succ_lt _ c j.lt⟩

theorem shift_ne_zeroC {bp : TreeN} (c : UnitChild) (j : Child bp) : shift c j ≠ zeroC c bp :=
  fun e => nomatch congrArg Child.idx e

theorem shift_injective {bp : TreeN} {c : UnitChild} {j j' : Child bp}
    (h : shift c j = shift c j') : j = j' := by
  have e := congrArg Child.idx h
  exact ext (TreeN.succ_injective e)

/-- Every child of `c :: bp` is `0` or a shifted child. -/
inductive ZeroOrShift {bp : TreeN} (c : UnitChild) (i : Child (c :: bp)) : Type
  | zero : i = zeroC c bp → ZeroOrShift c i
  | shifted (j : Child bp) : i = shift c j → ZeroOrShift c i

def zeroOrShift {bp : TreeN} (c : UnitChild) : (i : Child (c :: bp)) → ZeroOrShift c i
  | ⟨[], _⟩ => ZeroOrShift.zero rfl
  | ⟨d :: k, h⟩ => ZeroOrShift.shifted ⟨k, by cases h with | succ_lt _ _ h' => exact h'⟩
      (ext (by cases d; rfl))

/-- The shift is a bijection onto the nonzero children. -/
theorem nonzero_is_shift {bp : TreeN} {c : UnitChild} (i : Child (c :: bp))
    (h : i ≠ zeroC c bp) : ∃ j, i = shift c j :=
  match zeroOrShift c i with
  | ZeroOrShift.zero e => absurd e h
  | ZeroOrShift.shifted j e => ⟨j, e⟩

end Child

namespace FinSum

variable {K : Type} [TField K]

/-- Sum over all unary-path indices below `B`, by structural recursion on `B`. -/
def sumBelow : (B : TreeN) → ((i : TreeN) → TreeN.PathLT i B → K) → K
  | [], _ => 𝟘
  | c :: B, g => sumBelow B (fun i h => g i (TreeN.lt_trans h (TreeN.lt_cons_self c B))) +
      g B (TreeN.lt_cons_self c B)

/-- Sum over the finite alphabet `Child b`. -/
def sumC (b : TreeN) (f : Child b → K) : K := sumBelow b (fun i h => f ⟨i, h⟩)

theorem sumC_nil (f : Child [] → K) : sumC [] f = 𝟘 := rfl

theorem sumC_cons (c : UnitChild) (b : TreeN) (f : Child (c :: b) → K) :
    sumC (c :: b) f = sumC b (fun i => f (Child.incl c i)) + f (Child.last c b) := rfl

theorem sumC_congr {b : TreeN} {f g : Child b → K} (h : ∀ i, f i = g i) :
    sumC b f = sumC b g := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    rw [sumC_cons, sumC_cons, ih (fun i => h (Child.incl c i)), h]

theorem sumC_zero (b : TreeN) : sumC b (fun _ => (𝟘 : K)) = 𝟘 := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    rw [sumC_cons, ih, add_zero]

theorem sumC_add (b : TreeN) (f g : Child b → K) :
    sumC b (fun i => f i + g i) = sumC b f + sumC b g := by
  induction b with
  | nil => exact (add_zero 𝟘).symm
  | cons c b ih =>
    rw [sumC_cons, sumC_cons, sumC_cons, ih, add_add_add_comm]

theorem sumC_mul_left (b : TreeN) (a : K) (f : Child b → K) :
    sumC b (fun i => a * f i) = a * sumC b f := by
  induction b with
  | nil => exact (mul_zero a).symm
  | cons c b ih =>
    rw [sumC_cons, sumC_cons, ih, left_distrib]

theorem sumC_neg (b : TreeN) (f : Child b → K) : sumC b (fun i => -f i) = -sumC b f := by
  induction b with
  | nil => exact neg_zero.symm
  | cons c b ih =>
    rw [sumC_cons, sumC_cons, ih, neg_add]

/-- The sum of the constant `1` over `Child b` is the image of the path count `b`. -/
theorem sumC_one (b : TreeN) : sumC b (fun _ => (𝟙 : K)) = natCast b := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    rw [sumC_cons, ih, natCast_cons, add_comm]

/-! ## Delta functions -/

/-- The function with value `a` at `j` and `0` elsewhere (decidable equality of children). -/
def delta {b : TreeN} (j : Child b) (a : K) (i : Child b) : K :=
  match Child.decEq i j with
  | isTrue _ => a
  | isFalse _ => 𝟘

theorem delta_eq {b : TreeN} {j i : Child b} (a : K) (h : i = j) : delta j a i = a := by
  unfold delta
  cases Child.decEq i j with
  | isTrue _ => rfl
  | isFalse h' => exact absurd h h'

theorem delta_ne {b : TreeN} {j i : Child b} (a : K) (h : i ≠ j) : delta j a i = 𝟘 := by
  unfold delta
  cases Child.decEq i j with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl

theorem delta_self {b : TreeN} (j : Child b) (a : K) : delta j a j = a := delta_eq a rfl

/-- Pointwise case split for delta functions. -/
theorem delta_cases {b : TreeN} (j i : Child b) (P : K → Prop) (a : K)
    (h1 : i = j → P a) (h2 : i ≠ j → P 𝟘) : P (delta j a i) := by
  unfold delta
  cases Child.decEq i j with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

/-- **Sifting**: the sum of a delta function is its value. -/
theorem sumC_delta : (b : TreeN) → (j : Child b) → (a : K) → sumC b (delta j a) = a
  | [], j, _ => (Child.zero_empty j).elim
  | c :: b, j, a =>
    match Child.decomp c j with
    | Child.Decomp.old y e => by
      subst e
      rw [sumC_cons, delta_ne a (Child.last_ne_incl c y), add_zero]
      have h : ∀ i, delta (Child.incl c y) a (Child.incl c i) = delta y a i := by
        intro i
        apply delta_cases y i (fun v => delta (Child.incl c y) a (Child.incl c i) = v)
        · intro e
          rw [e]
          exact delta_self _ a
        · intro ne
          exact delta_ne a (fun e => ne (Child.incl_injective e))
      rw [sumC_congr h]
      exact sumC_delta b y a
    | Child.Decomp.new e => by
      subst e
      rw [sumC_cons, delta_self]
      have h : ∀ i, delta (Child.last c b) a (Child.incl c i) = 𝟘 :=
        fun i => delta_ne a (fun e => Child.last_ne_incl c i e.symm)
      rw [sumC_congr h, sumC_zero, zero_add]

theorem delta_symm {b : TreeN} (f : Child b → K) (j k : Child b) :
    delta j (f j) k = delta k (f k) j := by
  apply delta_cases j k (fun v => v = delta k (f k) j) (f j)
  · intro e
    rw [e, delta_self]
  · intro ne
    exact (delta_ne _ (fun e => ne e.symm)).symm

/-- Sifting over the index of the delta function. -/
theorem sumC_delta' (b : TreeN) (f : Child b → K) (k : Child b) :
    sumC b (fun j => delta j (f j) k) = f k := by
  rw [sumC_congr (fun j => delta_symm f j k)]
  exact sumC_delta b k (f k)

/-- `f i · δ_j(i) = δ_j(f j)(i)`. -/
theorem mul_delta {b : TreeN} (f : Child b → K) (j i : Child b) :
    f i * delta j 𝟙 i = delta j (f j) i := by
  apply delta_cases j i (fun v => f i * v = delta j (f j) i) 𝟙
  · intro e
    rw [e, mul_one, delta_self]
  · intro ne
    rw [mul_zero, delta_ne _ ne]

/-! ## Splitting off the zeroth child -/

theorem sumC_first : (bp : TreeN) → (c : UnitChild) → (f : Child (c :: bp) → K) →
    sumC (c :: bp) f = f (Child.zeroC c bp) + sumC bp (fun j => f (Child.shift c j))
  | [], c, f => by
    rw [sumC_cons, sumC_nil, sumC_nil, zero_add, add_zero]
    rfl
  | d :: bp, c, f => by
    rw [sumC_cons, sumC_first bp d (fun i => f (Child.incl c i)), sumC_cons, add_assoc]
    have e1 : Child.incl c (Child.zeroC d bp) = Child.zeroC c (d :: bp) := Child.ext rfl
    have e2 : Child.last c (d :: bp) = Child.shift c (Child.last d bp) :=
      Child.ext (by cases d; rfl)
    rw [e1, e2]
    rfl

/-! ## Interchange of finite sums and invariance under permutations -/

theorem sumC_swap (b b' : TreeN) (g : Child b → Child b' → K) :
    sumC b (fun i => sumC b' (fun j => g i j)) = sumC b' (fun j => sumC b (fun i => g i j)) := by
  induction b with
  | nil => exact (sumC_zero b').symm
  | cons c b ih =>
    rw [sumC_cons, ih (fun i j => g (Child.incl c i) j), ← sumC_add]
    rfl

/-- Finite sums are invariant under child permutations. -/
theorem sumC_perm {b : TreeN} (σ τ : Child b → Child b) (h1 : ∀ i, σ (τ i) = i)
    (h2 : ∀ i, τ (σ i) = i) (f : Child b → K) : sumC b (fun i => f (σ i)) = sumC b f := by
  have e1 : ∀ i, f (σ i) = sumC b (fun j => delta j (f j) (σ i)) :=
    fun i => (sumC_delta' b f (σ i)).symm
  rw [sumC_congr e1, sumC_swap]
  have e2 : ∀ j, sumC b (fun i => delta j (f j) (σ i)) = f j := by
    intro j
    have e3 : ∀ i, delta j (f j) (σ i) = delta (τ j) (f j) i := by
      intro i
      apply delta_cases j (σ i) (fun v => v = delta (τ j) (f j) i) (f j)
      · intro e
        rw [← e, h2, delta_self]
      · intro ne
        exact (delta_ne _ (fun e => ne (by rw [e, h1]))).symm
    rw [sumC_congr e3]
    exact sumC_delta b (τ j) (f j)
  exact sumC_congr e2

/-! ## Agreement with the fold over the explicit enumeration list -/

/-- Fold of a list of field elements. -/
def sumList : List K → K
  | [] => 𝟘
  | x :: l => x + sumList l

theorem sumList_appL (l m : List K) : sumList (appL l m) = sumList l + sumList m := by
  induction l with
  | nil => exact (zero_add _).symm
  | cons x l ih =>
    show x + sumList (appL l m) = x + sumList l + sumList m
    rw [ih, add_assoc]

theorem mapL_mapL {α β γ : Type} (f : β → γ) (g : α → β) (l : List α) :
    mapL f (mapL g l) = mapL (fun a => f (g a)) l := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (List.cons (f (g x))) ih

/-- The recursive sum equals the fold over the enumeration `Child.enum b`. -/
theorem sumC_eq_fold (b : TreeN) (f : Child b → K) : sumC b f = sumList (mapL f (Child.enum b)) := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    show sumC (c :: b) f = sumList (mapL f (appL (mapL (Child.incl c) (Child.enum b)) [Child.last c b]))
    rw [mapL_appL, sumList_appL, mapL_mapL, sumC_cons, ih]
    show _ = _ + (f (Child.last c b) + 𝟘)
    rw [add_zero]

end FinSum
end
