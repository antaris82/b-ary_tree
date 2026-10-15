module

public import PrimitiveTree.UnitChild

@[expose] public section

/-!
# Structural list operations

Local, purely structural list operations (append, map, membership, duplicate-freeness),
defined by structural recursion so that no library list API is used.
-/

namespace ListOps

variable {α β : Type}

/-- Append, by structural recursion on the first list. -/
def appL : List α → List α → List α
  | [], l => l
  | a :: l, m => a :: appL l m

/-- Map, by structural recursion. -/
def mapL (f : α → β) : List α → List β
  | [] => []
  | a :: l => f a :: mapL f l

/-- Membership, by structural recursion. -/
def InL (a : α) : List α → Prop
  | [] => False
  | x :: l => a = x ∨ InL a l

/-- Duplicate-freeness, by structural recursion. -/
def NodupL : List α → Prop
  | [] => True
  | x :: l => ¬ InL x l ∧ NodupL l

theorem appL_nil (l : List α) : appL l [] = l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (List.cons a) ih

theorem appL_assoc (l m n : List α) : appL (appL l m) n = appL l (appL m n) := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (List.cons a) ih

theorem mapL_appL (f : α → β) (l m : List α) : mapL f (appL l m) = appL (mapL f l) (mapL f m) := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (List.cons (f a)) ih

theorem inL_appL_left {a : α} {l : List α} (m : List α) (h : InL a l) : InL a (appL l m) := by
  induction l with
  | nil => exact h.elim
  | cons x l ih =>
    cases h with
    | inl e => exact Or.inl e
    | inr h => exact Or.inr (ih h)

theorem inL_appL_right {a : α} (l : List α) {m : List α} (h : InL a m) : InL a (appL l m) := by
  induction l with
  | nil => exact h
  | cons x l ih => exact Or.inr ih

theorem inL_mapL {a : α} {l : List α} (f : α → β) (h : InL a l) : InL (f a) (mapL f l) := by
  induction l with
  | nil => exact h.elim
  | cons x l ih =>
    cases h with
    | inl e => exact Or.inl (congrArg f e)
    | inr h => exact Or.inr (ih h)

theorem inL_mapL_inv {b : β} {l : List α} {f : α → β} (h : InL b (mapL f l)) :
    ∃ a, InL a l ∧ b = f a := by
  induction l with
  | nil => exact h.elim
  | cons x l ih =>
    cases h with
    | inl e => exact ⟨x, Or.inl rfl, e⟩
    | inr h =>
      obtain ⟨a, ha, e⟩ := ih h
      exact ⟨a, Or.inr ha, e⟩

/-- A list never equals a list obtained by putting a nonempty list in front of it. -/
theorem appL_cons_ne (l : List α) (a : α) (m : List α) : appL l (a :: m) ≠ m := by
  induction m generalizing l a with
  | nil =>
    cases l with
    | nil => exact fun h => nomatch h
    | cons x l => exact fun h => nomatch h
  | cons b m ih =>
    intro h
    cases l with
    | nil =>
      injection h with h1 h2
      exact ih [] b h2
    | cons x l =>
      injection h with h1 h2
      have e : appL l (a :: b :: m) = appL (appL l [a]) (b :: m) := by
        rw [appL_assoc]
        rfl
      rw [e] at h2
      exact ih _ b h2

end ListOps
end
