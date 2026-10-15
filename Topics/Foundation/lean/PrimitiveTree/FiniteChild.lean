module

public import TreeNumbers.PathOrder
public import PrimitiveTree.ListOps

@[expose] public section

/-!
# Finite arity without `Nat` or `Fin`

A finite branching count `b` is itself a unary root path.  The child alphabet `Child b`
consists of unary-path indices `i` together with a proof of `PathLT i b`.
-/

open TreeN ListOps

/-- The child alphabet of arity `b`: a tree-path index strictly below `b`. -/
structure Child (b : TreeN) where
  idx : TreeN
  lt : PathLT idx b

namespace Child

theorem ext {b : TreeN} {x y : Child b} (h : x.idx = y.idx) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Decidable equality of child symbols (through their tree-path indices). -/
def decEq {b : TreeN} (x y : Child b) : Decidable (x = y) :=
  match TreeN.decEq x.idx y.idx with
  | isTrue h => isTrue (ext h)
  | isFalse h => isFalse (fun e => h (by rw [e]))

instance {b : TreeN} : DecidableEq (Child b) := decEq

/-- Arity zero has no children. -/
theorem zero_empty (x : Child zero) : False := not_lt_zero x.idx x.lt

/-- The first child symbol `0` of a positive arity. -/
def first {b : TreeN} (h : PathLT zero b) : Child b := ⟨zero, h⟩

/-- The second child symbol `1` of an arity with at least two children. -/
def second {b : TreeN} (h : PathLT one b) : Child b := ⟨one, h⟩

theorem first_ne_second {b : TreeN} (h0 : PathLT zero b) (h1 : PathLT one b) :
    first h0 ≠ second h1 := fun e => nomatch congrArg Child.idx e

/-- Arity one has exactly one child symbol. -/
theorem one_unique (x : Child one) : x = first (zero_lt_succ zero) := by
  apply ext
  cases x with
  | mk i h =>
    cases h with
    | zero_lt => rfl
    | succ_lt _ _ h' => exact absurd h' (not_lt_zero _)

/-- Arity two has exactly the two child symbols `0` and `1`. -/
theorem two_cases (x : Child two) :
    x = first (zero_lt_succ one) ∨ x = second (lt_succ_self one) := by
  cases x with
  | mk i h =>
    cases h with
    | zero_lt => exact Or.inl rfl
    | succ_lt c _ h' =>
      cases h' with
      | zero_lt => exact Or.inr (ext (by cases c; rfl))
      | succ_lt _ _ h'' => exact absurd h'' (not_lt_zero _)

/-- Canonical inclusion `Child b ↪ Child (c :: b)`, retaining the same index. -/
def incl {b : TreeN} (c : UnitChild) (x : Child b) : Child (c :: b) :=
  ⟨x.idx, lt_trans x.lt (lt_cons_self c b)⟩

/-- Canonical inclusion `Child b ↪ Child (succ b)`. -/
def inclSucc {b : TreeN} (x : Child b) : Child (succ b) := incl UnitChild.only x

theorem incl_idx {b : TreeN} (c : UnitChild) (x : Child b) : (incl c x).idx = x.idx := rfl

theorem incl_injective {b : TreeN} {c : UnitChild} {x y : Child b} (h : incl c x = incl c y) :
    x = y := by
  have e := congrArg Child.idx h
  exact ext e

/-- The new (last) child of arity `c :: b`, with index `b`. -/
def last (c : UnitChild) (b : TreeN) : Child (c :: b) := ⟨b, lt_cons_self c b⟩

theorem last_ne_incl {b : TreeN} (c : UnitChild) (x : Child b) : last c b ≠ incl c x := by
  intro e
  have e' : b = x.idx := congrArg Child.idx e
  have h := x.lt
  rw [← e'] at h
  exact lt_irrefl b h

/-- Constructive decomposition of `Child (c :: b)`: old children and the new last child. -/
inductive Decomp {b : TreeN} (c : UnitChild) (x : Child (c :: b)) : Type
  | old (y : Child b) : x = incl c y → Decomp c x
  | new : x = last c b → Decomp c x

def decomp {b : TreeN} (c : UnitChild) (x : Child (c :: b)) : Decomp c x :=
  match decLT x.idx b with
  | isTrue h => Decomp.old ⟨x.idx, h⟩ (ext rfl)
  | isFalse h =>
    have h2 : PathLT x.idx (succ b) := by
      have h3 := x.lt
      cases c
      exact h3
    Decomp.new (ext (show x.idx = b from le_antisymm (le_of_lt_succ h2) (le_of_not_lt h)))

/-- Explicit recursive enumeration of the finite alphabet `Child b`. -/
def enum : (b : TreeN) → List (Child b)
  | [] => []
  | c :: b => appL (mapL (incl c) (enum b)) [last c b]

/-- Every child symbol occurs in the enumeration. -/
theorem mem_enum : (b : TreeN) → (x : Child b) → InL x (enum b)
  | [], x => (zero_empty x).elim
  | c :: b, x =>
    match decomp c x with
    | Decomp.old y e => by
      rw [e]
      exact inL_appL_left _ (inL_mapL (incl c) (mem_enum b y))
    | Decomp.new e => by
      rw [e]
      exact inL_appL_right _ (Or.inl rfl)

theorem not_mem_incl_list {b : TreeN} (c : UnitChild) (y : Child b) :
    (l : List (Child b)) → ¬ InL y l → ¬ InL (incl c y) (appL (mapL (incl c) l) [last c b])
  | [], _, h => by
    cases h with
    | inl e => exact last_ne_incl c y e.symm
    | inr e => exact e
  | z :: l, hy, h => by
    cases h with
    | inl e => exact hy (Or.inl (incl_injective e))
    | inr e => exact not_mem_incl_list c y l (fun h' => hy (Or.inr h')) e

theorem nodup_incl_list {b : TreeN} (c : UnitChild) :
    (l : List (Child b)) → NodupL l → NodupL (appL (mapL (incl c) l) [last c b])
  | [], _ => ⟨fun h => h, trivial⟩
  | y :: l, hb => ⟨not_mem_incl_list c y l hb.1, nodup_incl_list c l hb.2⟩

/-- The enumeration has no repetitions. -/
theorem nodup_enum : (b : TreeN) → NodupL (enum b)
  | [] => trivial
  | c :: b => nodup_incl_list c (enum b) (nodup_enum b)

end Child
end
