module

public import TreeNumbers.PathNaturals

@[expose] public section

/-!
# Constructive order on `TreeN`

Strict and non-strict comparison of unary paths are defined *inductively* from the list
constructors.  Decidability and trichotomy are given by explicit structural recursion.
-/

namespace TreeN

/-- Strict comparison of unary paths, defined inductively from the path constructors. -/
inductive PathLT : TreeN → TreeN → Prop
  | zero_lt (c : UnitChild) (n : TreeN) : PathLT [] (c :: n)
  | succ_lt {m n : TreeN} (c d : UnitChild) : PathLT m n → PathLT (c :: m) (d :: n)

/-- Non-strict comparison of unary paths, defined inductively. -/
inductive PathLE : TreeN → TreeN → Prop
  | zero_le (n : TreeN) : PathLE [] n
  | succ_le {m n : TreeN} (c d : UnitChild) : PathLE m n → PathLE (c :: m) (d :: n)

theorem lt_irrefl (n : TreeN) : ¬ PathLT n n := by
  induction n with
  | nil => intro h; cases h
  | cons c n ih =>
    intro h
    cases h with
    | succ_lt _ _ h' => exact ih h'

theorem not_lt_zero (n : TreeN) : ¬ PathLT n zero := by
  intro h
  cases h

theorem lt_trans {a b c : TreeN} (h1 : PathLT a b) (h2 : PathLT b c) : PathLT a c := by
  induction h1 generalizing c with
  | zero_lt x n =>
    cases h2 with
    | succ_lt _ y _ => exact PathLT.zero_lt y _
  | succ_lt x y _ ih =>
    cases h2 with
    | succ_lt _ z h2' => exact PathLT.succ_lt x z (ih h2')

theorem le_refl (n : TreeN) : PathLE n n := by
  induction n with
  | nil => exact PathLE.zero_le _
  | cons c n ih => exact PathLE.succ_le c c ih

theorem le_trans {a b c : TreeN} (h1 : PathLE a b) (h2 : PathLE b c) : PathLE a c := by
  induction h1 generalizing c with
  | zero_le n => exact PathLE.zero_le _
  | succ_le x y _ ih =>
    cases h2 with
    | succ_le _ z h2' => exact PathLE.succ_le x z (ih h2')

theorem le_of_lt {m n : TreeN} (h : PathLT m n) : PathLE m n := by
  induction h with
  | zero_lt c n => exact PathLE.zero_le _
  | succ_lt c d _ ih => exact PathLE.succ_le c d ih

theorem lt_cons_self (c : UnitChild) (n : TreeN) : PathLT n (c :: n) := by
  induction n generalizing c with
  | nil => exact PathLT.zero_lt c []
  | cons d n ih => exact PathLT.succ_lt d c (ih d)

theorem lt_succ_self (n : TreeN) : PathLT n (succ n) := lt_cons_self _ n

theorem zero_lt_succ (n : TreeN) : PathLT zero (succ n) := PathLT.zero_lt _ n

theorem zero_le (n : TreeN) : PathLE zero n := PathLE.zero_le n

/-- `m < m + succ k`. -/
theorem lt_add_succ (m k : TreeN) : PathLT m (m + succ k) := by
  induction m with
  | nil => exact PathLT.zero_lt _ k
  | cons c m ih => exact PathLT.succ_lt c c ih

/-- Strict comparison is witnessed by a positive path difference. -/
theorem exists_of_lt {m n : TreeN} (h : PathLT m n) : ∃ k, n = m + succ k := by
  induction h with
  | zero_lt c n => exact ⟨n, by rw [UnaryPath.cons_eq_extend]; rfl⟩
  | succ_lt c d _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k, by rw [hk, cons_add, UnitChild.eq c d]⟩

theorem le_add (m k : TreeN) : PathLE m (m + k) := by
  induction m with
  | nil => exact PathLE.zero_le _
  | cons c m ih => exact PathLE.succ_le c c ih

theorem exists_of_le {m n : TreeN} (h : PathLE m n) : ∃ k, n = m + k := by
  induction h with
  | zero_le n => exact ⟨n, rfl⟩
  | succ_le c d _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k, by rw [hk, cons_add, UnitChild.eq c d]⟩

theorem lt_of_lt_of_le {a b c : TreeN} (h1 : PathLT a b) (h2 : PathLE b c) : PathLT a c := by
  induction h1 generalizing c with
  | zero_lt x n =>
    cases h2 with
    | succ_le _ y _ => exact PathLT.zero_lt y _
  | succ_lt x y _ ih =>
    cases h2 with
    | succ_le _ z h2' => exact PathLT.succ_lt x z (ih h2')

theorem lt_of_le_of_lt {a b c : TreeN} (h1 : PathLE a b) (h2 : PathLT b c) : PathLT a c := by
  induction h1 generalizing c with
  | zero_le n =>
    cases h2 with
    | zero_lt y _ => exact PathLT.zero_lt y _
    | succ_lt _ y _ => exact PathLT.zero_lt y _
  | succ_le x y _ ih =>
    cases h2 with
    | succ_lt _ z h2' => exact PathLT.succ_lt x z (ih h2')

theorem lt_succ_of_le {m n : TreeN} (h : PathLE m n) : PathLT m (succ n) :=
  lt_of_le_of_lt h (lt_succ_self n)

theorem le_of_lt_succ {m n : TreeN} (h : PathLT m (succ n)) : PathLE m n := by
  induction m generalizing n with
  | nil => exact PathLE.zero_le _
  | cons c m ih =>
    cases h with
    | succ_lt _ _ h' =>
      cases n with
      | nil => exact absurd h' (not_lt_zero m)
      | cons d n => exact PathLE.succ_le c d (ih h')

theorem succ_le_of_lt {m n : TreeN} (h : PathLT m n) : PathLE (succ m) n := by
  induction h with
  | zero_lt c n => exact PathLE.succ_le _ c (PathLE.zero_le n)
  | succ_lt c d _ ih => exact PathLE.succ_le _ d ih

theorem lt_of_succ_le {m n : TreeN} (h : PathLE (succ m) n) : PathLT m n :=
  lt_of_lt_of_le (lt_succ_self m) h

theorem le_antisymm {m n : TreeN} (h1 : PathLE m n) (h2 : PathLE n m) : m = n := by
  induction h1 with
  | zero_le n =>
    cases h2 with
    | zero_le => rfl
  | succ_le c d _ ih =>
    cases h2 with
    | succ_le _ _ h2' => rw [ih h2', UnitChild.eq c d]

/-- Constructive trichotomy data. -/
inductive Trichotomy (m n : TreeN) : Type
  | lt : PathLT m n → Trichotomy m n
  | eq : m = n → Trichotomy m n
  | gt : PathLT n m → Trichotomy m n

/-- Constructive comparison of unary paths by structural recursion. -/
def compare : (m n : TreeN) → Trichotomy m n
  | [], [] => Trichotomy.eq rfl
  | [], d :: n => Trichotomy.lt (PathLT.zero_lt d n)
  | c :: m, [] => Trichotomy.gt (PathLT.zero_lt c m)
  | c :: m, d :: n =>
    match compare m n with
    | Trichotomy.lt h => Trichotomy.lt (PathLT.succ_lt c d h)
    | Trichotomy.eq h => Trichotomy.eq (by rw [h, UnitChild.eq c d])
    | Trichotomy.gt h => Trichotomy.gt (PathLT.succ_lt d c h)

theorem lt_or_eq_or_gt (m n : TreeN) : PathLT m n ∨ m = n ∨ PathLT n m :=
  match compare m n with
  | Trichotomy.lt h => Or.inl h
  | Trichotomy.eq h => Or.inr (Or.inl h)
  | Trichotomy.gt h => Or.inr (Or.inr h)

theorem le_of_not_lt {m n : TreeN} (h : ¬ PathLT n m) : PathLE m n :=
  match compare m n with
  | Trichotomy.lt h' => le_of_lt h'
  | Trichotomy.eq h' => by rw [h']; exact le_refl n
  | Trichotomy.gt h' => absurd h' h

theorem not_lt_of_le {m n : TreeN} (h : PathLE m n) : ¬ PathLT n m :=
  fun h' => lt_irrefl m (lt_of_le_of_lt h h')

theorem ne_of_lt {m n : TreeN} (h : PathLT m n) : m ≠ n := by
  intro e
  rw [e] at h
  exact lt_irrefl n h

theorem le_or_lt (m n : TreeN) : PathLE m n ∨ PathLT n m :=
  match compare m n with
  | Trichotomy.lt h => Or.inl (le_of_lt h)
  | Trichotomy.eq h => Or.inl (by rw [h]; exact le_refl n)
  | Trichotomy.gt h => Or.inr h

theorem eq_or_lt_of_le {m n : TreeN} (h : PathLE m n) : m = n ∨ PathLT m n :=
  match compare m n with
  | Trichotomy.lt h' => Or.inr h'
  | Trichotomy.eq h' => Or.inl h'
  | Trichotomy.gt h' => absurd h' (not_lt_of_le h)

/-- Decidability of strict comparison, by structural recursion. -/
def decLT : (m n : TreeN) → Decidable (PathLT m n)
  | [], [] => isFalse (lt_irrefl [])
  | [], d :: n => isTrue (PathLT.zero_lt d n)
  | _ :: m, [] => isFalse (not_lt_zero _)
  | c :: m, d :: n =>
    match decLT m n with
    | isTrue h => isTrue (PathLT.succ_lt c d h)
    | isFalse h => isFalse (fun h' => by cases h' with | succ_lt _ _ h'' => exact h h'')

instance (m n : TreeN) : Decidable (PathLT m n) := decLT m n

/-- Decidability of non-strict comparison, by structural recursion. -/
def decLE : (m n : TreeN) → Decidable (PathLE m n)
  | [], n => isTrue (PathLE.zero_le n)
  | _ :: m, [] => isFalse (fun h => nomatch h)
  | c :: m, d :: n =>
    match decLE m n with
    | isTrue h => isTrue (PathLE.succ_le c d h)
    | isFalse h => isFalse (fun h' => by cases h' with | succ_le _ _ h'' => exact h h'')

instance (m n : TreeN) : Decidable (PathLE m n) := decLE m n

/-! ## Positivity -/

theorem pos_iff_succ {n : TreeN} (h : PathLT zero n) : ∃ m, n = succ m := by
  cases h with
  | zero_lt c m => exact ⟨m, UnaryPath.cons_eq_extend c m⟩

theorem pos_of_ne_zero {n : TreeN} (h : n ≠ zero) : PathLT zero n := by
  cases n with
  | nil => exact absurd rfl h
  | cons c n => exact PathLT.zero_lt c n

theorem ne_zero_of_pos {n : TreeN} (h : PathLT zero n) : n ≠ zero :=
  fun e => by rw [e] at h; exact lt_irrefl zero h

/-! ## Compatibility with addition -/

theorem add_lt_add_left {m n : TreeN} (k : TreeN) (h : PathLT m n) : PathLT (k + m) (k + n) := by
  induction k with
  | nil => exact h
  | cons c k ih => exact PathLT.succ_lt c c ih

theorem lt_of_add_lt_add_left {k m n : TreeN} (h : PathLT (k + m) (k + n)) : PathLT m n := by
  induction k with
  | nil => exact h
  | cons c k ih =>
    cases h with
    | succ_lt _ _ h' => exact ih h'

theorem add_lt_add_right {m n : TreeN} (k : TreeN) (h : PathLT m n) : PathLT (m + k) (n + k) := by
  rw [add_comm m k, add_comm n k]
  exact add_lt_add_left k h

theorem add_le_add_left {m n : TreeN} (k : TreeN) (h : PathLE m n) : PathLE (k + m) (k + n) := by
  induction k with
  | nil => exact h
  | cons c k ih => exact PathLE.succ_le c c ih

theorem le_of_add_le_add_left {k m n : TreeN} (h : PathLE (k + m) (k + n)) : PathLE m n := by
  induction k with
  | nil => exact h
  | cons c k ih =>
    cases h with
    | succ_le _ _ h' => exact ih h'

theorem add_le_add_right {m n : TreeN} (k : TreeN) (h : PathLE m n) : PathLE (m + k) (n + k) := by
  rw [add_comm m k, add_comm n k]
  exact add_le_add_left k h

theorem lt_add_of_pos {m k : TreeN} (h : PathLT zero k) : PathLT m (m + k) := by
  obtain ⟨j, hj⟩ := pos_iff_succ h
  rw [hj]
  exact lt_add_succ m j

theorem add_pos_left {m : TreeN} (n : TreeN) (h : PathLT zero m) : PathLT zero (m + n) :=
  lt_of_lt_of_le h (le_add m n)

/-! ## Compatibility with multiplication -/

theorem mul_pos {m n : TreeN} (hm : PathLT zero m) (hn : PathLT zero n) : PathLT zero (m * n) := by
  obtain ⟨m', hm'⟩ := pos_iff_succ hm
  rw [hm', succ_mul]
  exact add_pos_left _ hn

theorem mul_lt_mul_left {k m n : TreeN} (hk : PathLT zero k) (h : PathLT m n) :
    PathLT (k * m) (k * n) := by
  obtain ⟨j, hj⟩ := exists_of_lt h
  rw [hj, left_distrib]
  exact lt_add_of_pos (mul_pos hk (zero_lt_succ j))

theorem mul_le_mul_left (k : TreeN) {m n : TreeN} (h : PathLE m n) : PathLE (k * m) (k * n) := by
  obtain ⟨j, hj⟩ := exists_of_le h
  rw [hj, left_distrib]
  exact le_add _ _

/-- Multiplicative cancellation by a positive path count. -/
theorem mul_left_cancel {k m n : TreeN} (hk : PathLT zero k) (h : k * m = k * n) : m = n :=
  match compare m n with
  | Trichotomy.lt h' => absurd h (ne_of_lt (mul_lt_mul_left hk h'))
  | Trichotomy.eq h' => h'
  | Trichotomy.gt h' => absurd h.symm (ne_of_lt (mul_lt_mul_left hk h'))

theorem mul_right_cancel {k m n : TreeN} (hk : PathLT zero k) (h : m * k = n * k) : m = n := by
  rw [mul_comm m k, mul_comm n k] at h
  exact mul_left_cancel hk h

theorem lt_of_mul_lt_mul_left {k m n : TreeN} (h : PathLT (k * m) (k * n)) : PathLT m n :=
  match le_or_lt n m with
  | Or.inl h' => absurd h (not_lt_of_le (mul_le_mul_left k h'))
  | Or.inr h' => h'

/-! ## Truncated path difference -/

/-- Path difference by pattern matching: removes common steps; `diff m n` is the part of
`n` beyond `m` (and the root path if `n` is not longer than `m`). -/
def diff : TreeN → TreeN → TreeN
  | [], n => n
  | _ :: _, [] => []
  | _ :: m, _ :: n => diff m n

theorem add_diff {m n : TreeN} (h : PathLE m n) : m + diff m n = n := by
  induction h with
  | zero_le n => rfl
  | succ_le c d _ ih =>
    rw [UnitChild.eq c d]
    exact congrArg (List.cons d) ih

theorem diff_add (m k : TreeN) : diff m (m + k) = k := by
  induction m with
  | nil => rfl
  | cons c m ih => exact ih

/-- The positive path gap between `m` and a strictly longer `n`. -/
theorem diff_pos {m n : TreeN} (h : PathLT m n) : PathLT zero (diff m n) := by
  induction h with
  | zero_lt c n => exact PathLT.zero_lt c n
  | succ_lt c d _ ih => exact ih

end TreeN
end
