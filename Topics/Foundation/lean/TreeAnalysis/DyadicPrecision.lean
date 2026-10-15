module

public import TreeAnalysis.OrderedField
public import TreeAnalysis.PathMax

@[expose] public section

/-!
# Checkpoint A3 — the internal precision scale

* `twoPow n`: positive powers of the internal value `two`, by structural recursion on `n`
  (`twoPow (n+1) = twoPow n + twoPow n`); no numerical exponentiation is used;
* `eps n := inv (twoPow n)`: the positive rational precisions.

Proved: positivity, halving `eps (n+1) + eps (n+1) = eps n`, the shift law
`eps (m+n) = eps m · eps n`, antitonicity, and the shrinking statement
`∀ δ > 0, ∃ n, eps n < δ` (with an explicit index function `epsIndex`), from the explicit
Archimedean bound of the ordered-field interface.
-/

open CSR CRing


open TreeN (PathLE PathLT succ maxN)

/-- Powers of two in `TreeN`: `twoPow 0 = 1`, `twoPow (n+1) = twoPow n + twoPow n`. -/
def twoPow : TreeN → TreeN
  | [] => TreeN.one
  | _ :: n => twoPow n + twoPow n

theorem twoPow_succ (n : TreeN) : twoPow (succ n) = twoPow n + twoPow n := rfl

theorem twoPow_pos (n : TreeN) : PathLT TreeN.zero (twoPow n) := by
  induction n with
  | nil => exact TreeN.zero_lt_succ _
  | cons c n ih => exact TreeN.add_pos_left _ ih

theorem one_le_twoPow (n : TreeN) : PathLE TreeN.one (twoPow n) :=
  TreeN.succ_le_of_lt (twoPow_pos n)

/-- `n < 2^n`, by internal induction. -/
theorem lt_twoPow (n : TreeN) : PathLT n (twoPow n) := by
  induction n with
  | nil => exact TreeN.zero_lt_succ _
  | cons c n ih =>
    have e : c :: n = succ n := UnaryPath.cons_eq_extend c n
    rw [e]
    exact TreeN.lt_of_le_of_lt (TreeN.succ_le_of_lt ih) (TreeN.lt_add_of_pos (twoPow_pos n))

theorem twoPow_add (m n : TreeN) : twoPow (m + n) = twoPow m * twoPow n := by
  induction m with
  | nil =>
    show twoPow n = TreeN.one * twoPow n
    rw [TreeN.one_mul]
  | cons c m ih =>
    show twoPow (m + n) + twoPow (m + n) = (twoPow m + twoPow m) * twoPow n
    rw [ih, TreeN.right_distrib]

theorem twoPow_le {m n : TreeN} (h : PathLE m n) : PathLE (twoPow m) (twoPow n) := by
  obtain ⟨k, hk⟩ := TreeN.exists_of_le h
  rw [hk, twoPow_add]
  have h2 := TreeN.mul_le_mul_left (twoPow m) (one_le_twoPow k)
  rw [TreeN.mul_one] at h2
  exact h2

namespace TOField

open TField

variable {K : Type} [TOField K]

/-- The positive rational precisions `eps n := 1 / 2^n`. -/
def eps (n : TreeN) : K := inv (natCast (twoPow n))

theorem natCast_twoPow_pos (n : TreeN) : 𝟘 < natCast (K := K) (twoPow n) :=
  natCast_pos (twoPow_pos n)

theorem natCast_twoPow_ne (n : TreeN) : natCast (K := K) (twoPow n) ≠ 𝟘 :=
  fun e => ne_of_lt (natCast_twoPow_pos n) e.symm

theorem eps_pos (n : TreeN) : 𝟘 < eps (K := K) n := inv_pos (natCast_twoPow_pos n)

theorem eps_nonneg (n : TreeN) : 𝟘 ≤ eps (K := K) n := le_of_lt (eps_pos n)

theorem eps_zero : eps (K := K) TreeN.zero = 𝟙 := by
  unfold eps
  show inv (natCast (K := K) TreeN.one) = 𝟙
  rw [natCast_one, inv_one]

theorem natCast_twoPow_mul_eps (n : TreeN) : natCast (K := K) (twoPow n) * eps n = 𝟙 :=
  mul_inv_cancel' (natCast_twoPow_ne n)

/-- Halving: `eps (n+1) + eps (n+1) = eps n`. -/
theorem eps_succ_add (n : TreeN) : eps (K := K) (succ n) + eps (succ n) = eps n := by
  unfold eps
  rw [twoPow_succ, natCast_add]
  have hT := natCast_twoPow_ne (K := K) n
  have hTT : natCast (K := K) (twoPow n) + natCast (twoPow n) ≠ 𝟘 := by
    have h := natCast_twoPow_ne (K := K) (succ n)
    rw [twoPow_succ, natCast_add] at h
    exact h
  apply mul_left_cancel' hTT
  rw [left_distrib, mul_inv_cancel' hTT, right_distrib, mul_inv_cancel' hT]

/-- Shift law: `eps (m+n) = eps m · eps n`. -/
theorem eps_add (m n : TreeN) : eps (K := K) (m + n) = eps m * eps n := by
  unfold eps
  rw [twoPow_add, natCast_mul, inv_mul_distrib (natCast_twoPow_ne m) (natCast_twoPow_ne n)]

theorem eps_le_one (n : TreeN) : eps (K := K) n ≤ 𝟙 := by
  have h1 := natCast_le (K := K) (one_le_twoPow n)
  rw [natCast_one] at h1
  have h := inv_le_inv (zero_lt_one (K := K)) h1
  rw [inv_one] at h
  exact h

/-- Antitonicity of the scale. -/
theorem eps_le_eps {m n : TreeN} (h : PathLE m n) : eps (K := K) n ≤ eps m := by
  unfold eps
  exact inv_le_inv (natCast_twoPow_pos m) (natCast_le (twoPow_le h))

theorem eps_succ_le (n : TreeN) : eps (K := K) (succ n) ≤ eps n :=
  eps_le_eps (TreeN.le_succ n)

theorem eps_succ_lt (n : TreeN) : eps (K := K) (succ n) < eps n := by
  have h := lt_add_of_pos_right (x := eps (K := K) (succ n)) (eps_pos (succ n))
  rw [eps_succ_add] at h
  exact h

/-- Rescaling: `2^c · eps (j + c) = eps j`. -/
theorem natCast_twoPow_mul_eps_add (j c : TreeN) :
    natCast (K := K) (twoPow c) * eps (j + c) = eps j := by
  rw [eps_add, mul_left_comm, natCast_twoPow_mul_eps, mul_one]

/-- `eps (n+2) + eps (n+2) + eps (n+1) = eps n`. -/
theorem eps_three (n : TreeN) :
    eps (K := K) (succ (succ n)) + eps (succ (succ n)) + eps (succ n) = eps n := by
  rw [eps_succ_add, eps_succ_add]

/-- Three terms at precision `n+2` stay below precision `n`. -/
theorem three_eps_le (n : TreeN) :
    eps (K := K) (succ (succ n)) + eps (succ (succ n)) + eps (succ (succ n)) ≤ eps n := by
  have h := add_le_add_left (eps (K := K) (succ (succ n)) + eps (succ (succ n)))
    (le_trans (eps_succ_le (succ n)) (le_refl (eps (K := K) (succ n))))
  rw [eps_three] at h
  exact h

theorem inv_inv' {a : K} (ha : a ≠ 𝟘) : inv (inv a) = a := by
  apply mul_left_cancel' (inv_ne_zero ha)
  rw [mul_inv_cancel' (inv_ne_zero ha), inv_mul_cancel' ha]

theorem inv_lt_inv {a b : K} (ha : 𝟘 < a) (h : a < b) : inv b < inv a := by
  have hb : 𝟘 < b := lt_trans ha h
  apply lt_of_le_of_ne (inv_le_inv ha (le_of_lt h))
  intro e
  have e2 : inv (inv b) = inv (inv a) := by rw [e]
  rw [inv_inv' (fun x => ne_of_lt hb x.symm), inv_inv' (fun x => ne_of_lt ha x.symm)] at e2
  exact ne_of_lt h e2.symm

/-- Explicit index function for the shrinking statement. -/
def epsIndex (δ : K) : TreeN := archBound (inv δ)

/-- **The scale tends to zero**: `eps (epsIndex δ) < δ` for every `δ > 0`. -/
theorem eps_epsIndex_lt {δ : K} (hδ : 𝟘 < δ) : eps (epsIndex δ) < δ := by
  have hδ0 : δ ≠ 𝟘 := fun e => ne_of_lt hδ e.symm
  have h1 : inv δ ≤ natCast (archBound (inv δ)) := le_archBound (inv δ)
  have h2 : natCast (K := K) (archBound (inv δ)) < natCast (twoPow (archBound (inv δ))) :=
    natCast_lt (lt_twoPow _)
  have h3 := inv_lt_inv (inv_pos hδ) (lt_of_le_of_lt h1 h2)
  rw [inv_inv' hδ0] at h3
  exact h3

theorem exists_eps_lt {δ : K} (hδ : 𝟘 < δ) : ∃ n : TreeN, eps n < δ :=
  ⟨epsIndex δ, eps_epsIndex_lt hδ⟩

/-- Approximation principle: if `a ≤ b + eps k` for every `k`, then `a ≤ b`. -/
theorem le_of_forall_le_add_eps {a b : K} (h : ∀ k : TreeN, a ≤ b + eps k) : a ≤ b := by
  cases le_or_lt a b with
  | inl h' => exact h'
  | inr h' =>
    have hpos : 𝟘 < a + -b := by
      have := add_lt_add_right (-b) h'
      rw [add_neg_cancel] at this
      exact this
    have h2 := eps_epsIndex_lt hpos
    have h3 := h (epsIndex (a + -b))
    have h4 : a + -b ≤ eps (epsIndex (a + -b)) := by
      have := add_le_add_right (-b) h3
      rw [add_comm b, add_sub_cancel_right] at this
      exact this
    exact absurd h4 h2

theorem eps_lt_of_lt {m n : TreeN} (h : PathLT m n) : eps (K := K) n < eps m :=
  lt_of_le_of_lt (eps_le_eps (TreeN.succ_le_of_lt h)) (eps_succ_lt m)

end TOField
end
