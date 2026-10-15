module

public import TreeFoundation.InfiniteRays
public import TreeNumbers.PathTriples

@[expose] public section

/-!
# Checkpoint F1 — cylinders and prefix agreement on the ray boundary

For an alphabet `α` (`Child b` or `TreeN`), rays are the Task 01 functions `Ray α = TreeN → α`.

* `Agree n r r'`: the prefixes of length `n` coincide (a relation, no numerical distance);
* `Cyl w`: the cylinder of rays passing through the finite vertex `w`;
* `rayOf t w`: an explicit ray through `w` (followed by the tail `t`);
* `modify r n a`: the ray `r` with the letter at position `n` replaced by `a`.

Equality of letters is decided by the supplied procedure (`DecidableEq α`, populated by the
constructive `Child.decEq`, `TreeN.decEq`); equality of infinite rays is **not** assumed decidable.
-/

open TreeN ListOps Word

/-- Selection by a decision. -/
def pickD {p : Prop} {β : Type} : Decidable p → β → β → β
  | isTrue _, a, _ => a
  | isFalse _, _, b => b

theorem pickD_pos {p : Prop} {β : Type} {a b : β} (h : p) : ∀ d : Decidable p, pickD d a b = a
  | isTrue _ => rfl
  | isFalse h' => absurd h h'

theorem pickD_neg {p : Prop} {β : Type} {a b : β} (h : ¬ p) : ∀ d : Decidable p, pickD d a b = b
  | isTrue h' => absurd h' h
  | isFalse _ => rfl

namespace Ray

variable {α : Type}

/-- Decidable equality of finite words, by structural recursion. -/
def wordDecEq [DecidableEq α] : (v w : Word α) → Decidable (v = w)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => nomatch h)
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | a :: v, b :: w =>
    match decEq a b, wordDecEq v w with
    | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
    | isFalse h1, _ => isFalse (fun e => h1 (by injection e))
    | _, isFalse h2 => isFalse (fun e => h2 (by injection e))

/-- Prefix agreement up to length `n`. -/
def Agree (n : TreeN) (r r' : Ray α) : Prop := prefixAt r n = prefixAt r' n

/-- The cylinder of rays through the vertex `w`. -/
def Cyl (w : Word α) (r : Ray α) : Prop := prefixAt r (depth w) = w

def decAgree [DecidableEq α] (n : TreeN) (r r' : Ray α) : Decidable (Agree n r r') :=
  wordDecEq _ _

def decCyl [DecidableEq α] (w : Word α) (r : Ray α) : Decidable (Cyl w r) := wordDecEq _ _

theorem agree_refl (n : TreeN) (r : Ray α) : Agree n r r := rfl

theorem agree_symm {n : TreeN} {r r' : Ray α} (h : Agree n r r') : Agree n r' r := h.symm

theorem agree_trans {n : TreeN} {r r' r'' : Ray α} (h1 : Agree n r r') (h2 : Agree n r' r'') :
    Agree n r r'' := h1.trans h2

theorem lt_cons_cases {i n : TreeN} {c : UnitChild} (h : PathLT i (c :: n)) : i = n ∨ PathLT i n := by
  cases c
  exact eq_or_lt_of_le (le_of_lt_succ h)

theorem agree_of_pointwise {n : TreeN} {r r' : Ray α} (h : ∀ i, PathLT i n → r i = r' i) :
    Agree n r r' := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    show r n :: prefixAt r n = r' n :: prefixAt r' n
    rw [h n (lt_cons_self c n), ih (fun i hi => h i (lt_trans hi (lt_cons_self c n)))]

theorem pointwise_of_agree {n : TreeN} {r r' : Ray α} (h : Agree n r r') :
    ∀ i, PathLT i n → r i = r' i := by
  induction n with
  | nil => intro i hi; exact absurd hi (not_lt_zero i)
  | cons c n ih =>
    intro i hi
    have h' : r n :: prefixAt r n = r' n :: prefixAt r' n := h
    injection h' with h1 h2
    cases lt_cons_cases hi with
    | inl e => rw [e]; exact h1
    | inr hl => exact ih h2 i hl

theorem agree_mono {m n : TreeN} {r r' : Ray α} (hmn : PathLE m n) (h : Agree n r r') :
    Agree m r r' :=
  agree_of_pointwise (fun i hi => pointwise_of_agree h i (lt_of_lt_of_le hi hmn))

theorem agree_succ {n : TreeN} {r r' : Ray α} (h : Agree (succ n) r r') : r n = r' n :=
  pointwise_of_agree h n (lt_succ_self n)

/-- Agreement at every length gives equality of rays (function extensionality). -/
theorem eq_of_agree_all {r r' : Ray α} (h : ∀ n, Agree n r r') : r = r' :=
  funext (fun n => agree_succ (h (succ n)))

/-- If two rays do not agree up to `n`, a first difference below `n` is found by a bounded
search with the supplied decision procedure for letters. -/
theorem exists_diff_of_not_agree [DecidableEq α] {n : TreeN} {r r' : Ray α}
    (h : ¬ Agree n r r') : ∃ i, PathLT i n ∧ r i ≠ r' i := by
  induction n with
  | nil => exact absurd rfl h
  | cons c n ih =>
    match decEq (r n) (r' n) with
    | isFalse hne => exact ⟨n, lt_cons_self c n, hne⟩
    | isTrue he =>
      have h2 : ¬ Agree n r r' := by
        intro ha
        apply h
        show r n :: prefixAt r n = r' n :: prefixAt r' n
        rw [he]
        exact congrArg (List.cons (r' n)) ha
      obtain ⟨i, hi, hne⟩ := ih h2
      exact ⟨i, lt_trans hi (lt_cons_self c n), hne⟩

theorem cyl_prefixAt (r : Ray α) (n : TreeN) : Cyl (prefixAt r n) r := by
  unfold Cyl
  rw [depth_prefixAt]

theorem agree_of_cyl_prefixAt {r r' : Ray α} {n : TreeN} (h : Cyl (prefixAt r n) r') :
    Agree n r' r := by
  unfold Cyl at h
  rw [depth_prefixAt] at h
  exact h

theorem cyl_prefixAt_of_agree {r r' : Ray α} {n : TreeN} (h : Agree n r' r) :
    Cyl (prefixAt r n) r' := by
  unfold Cyl
  rw [depth_prefixAt]
  exact h

/-! ## Explicit rays -/

/-- The ray through `w`, continued by the tail `t` (positions at or beyond `depth w`). -/
def rayOf (t : Ray α) : Word α → Ray α
  | [], i => t i
  | c :: w, i => pickD (TreeN.decEq i (depth w)) c (rayOf t w i)

theorem rayOf_tail (t : Ray α) (w : Word α) {i : TreeN} (h : PathLE (depth w) i) :
    rayOf t w i = t i := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    have hlt : PathLT (depth w) i := lt_of_lt_of_le (lt_succ_self _) h
    show pickD (TreeN.decEq i (depth w)) c (rayOf t w i) = t i
    rw [pickD_neg (fun e => lt_irrefl i (by rw [e] at hlt ⊢; exact hlt))]
    exact ih (le_of_lt hlt)

theorem rayOf_cyl (t : Ray α) (w : Word α) : Cyl w (rayOf t w) := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    show prefixAt (rayOf t (c :: w)) (succ (depth w)) = c :: w
    rw [prefixAt_succ]
    have e1 : rayOf t (c :: w) (depth w) = c := pickD_pos rfl _
    have e2 : prefixAt (rayOf t (c :: w)) (depth w) = prefixAt (rayOf t w) (depth w) :=
      agree_of_pointwise (fun i hi => pickD_neg (fun e => lt_irrefl i (by rw [e] at hi ⊢; exact hi)) _)
    rw [e1, e2]
    exact congrArg (List.cons c) ih

/-- Replace the letter at position `n`. -/
def modify (r : Ray α) (n : TreeN) (a : α) : Ray α := fun i => pickD (TreeN.decEq i n) a (r i)

theorem modify_at (r : Ray α) (n : TreeN) (a : α) : modify r n a n = a := pickD_pos rfl _

theorem agree_modify (r : Ray α) (n : TreeN) (a : α) : Agree n (modify r n a) r :=
  agree_of_pointwise (fun i hi => pickD_neg (fun e => lt_irrefl i (by rw [e] at hi ⊢; exact hi)) _)

/-- A letter different from a given one (two distinct letters are available). -/
def other [DecidableEq α] [TwoLetters α] (a : α) : α :=
  pickD (decEq a TwoLetters.l0) TwoLetters.l1 TwoLetters.l0

theorem other_ne [DecidableEq α] [TwoLetters α] (a : α) : other a ≠ a := by
  unfold other
  cases decEq a TwoLetters.l0 with
  | isTrue h =>
    show TwoLetters.l1 ≠ a
    rw [h]
    exact fun e => TwoLetters.ne e.symm
  | isFalse h =>
    show TwoLetters.l0 ≠ a
    exact fun e => h e.symm

/-- Constant ray. -/
def const (a : α) : Ray α := fun _ => a

end Ray
end
