module

public import TreeNumbers.PathOrder

@[expose] public section

/-!
# Maximum of two unary paths

`TreeN.maxN` by structural recursion on the two unary paths, with its order laws.  Used for
moduli of convergence and for prefix lengths.
-/

namespace TreeN

/-- Maximum of two unary paths, by structural recursion. -/
def maxN : TreeN → TreeN → TreeN
  | [], n => n
  | c :: m, [] => c :: m
  | c :: m, _ :: n => c :: maxN m n

theorem le_maxN_left (m n : TreeN) : PathLE m (maxN m n) := by
  induction m generalizing n with
  | nil => exact PathLE.zero_le _
  | cons c m ih =>
    cases n with
    | nil => exact le_refl _
    | cons d n => exact PathLE.succ_le c c (ih n)

theorem le_maxN_right (m n : TreeN) : PathLE n (maxN m n) := by
  induction m generalizing n with
  | nil => exact le_refl _
  | cons c m ih =>
    cases n with
    | nil => exact PathLE.zero_le _
    | cons d n => exact PathLE.succ_le d c (ih n)

theorem maxN_le {m n k : TreeN} (h1 : PathLE m k) (h2 : PathLE n k) : PathLE (maxN m n) k := by
  induction h1 generalizing n with
  | zero_le k => exact h2
  | succ_le c d h ih =>
    cases h2 with
    | zero_le _ => exact PathLE.succ_le c d h
    | succ_le e _ h2' => exact PathLE.succ_le c d (ih h2')

theorem le_of_maxN_le_left {m n k : TreeN} (h : PathLE (maxN m n) k) : PathLE m k :=
  le_trans (le_maxN_left m n) h

theorem le_of_maxN_le_right {m n k : TreeN} (h : PathLE (maxN m n) k) : PathLE n k :=
  le_trans (le_maxN_right m n) h

theorem le_succ (n : TreeN) : PathLE n (succ n) := le_of_lt (lt_succ_self n)

theorem le_add_right (m k : TreeN) : PathLE m (m + k) := le_add m k

theorem le_add_left (m k : TreeN) : PathLE m (k + m) := by
  rw [add_comm]
  exact le_add m k

end TreeN
end
