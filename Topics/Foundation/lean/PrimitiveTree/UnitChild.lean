module

@[expose] public section

/-- The one-element child-symbol type. -/
inductive UnitChild : Type where
  | only : UnitChild

namespace UnitChild

theorem eq_only (c : UnitChild) : c = UnitChild.only := by
  cases c
  rfl

theorem eq (c d : UnitChild) : c = d := by
  cases c
  cases d
  rfl

end UnitChild
end
