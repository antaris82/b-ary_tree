module

public import TreeFoundation.RayAutomorphism

@[expose] public section

/-!
# A tree automorphism that is not levelwise (Q14 counterexample)

`RayAutomorphism.treeAut` turns a *levelwise* permutation `P : LevelPerm α` into a root- and
incidence-preserving automorphism of the full rooted tree `Word α`: the same permutation
`P.perm n` acts on the new letter of *every* vertex of depth `n + 1`, whatever its parent.

A general rooted-tree automorphism may permute the children of different vertices of the same
depth differently.  For two distinct letters `a ≠ b` (decidable equality only) we construct
`subtreeSwap a b`: under the first-level vertex `[a]` it swaps the two child subtrees rooted at
`a :: [a]` and `b :: [a]` (children are written `c :: parent`), acting on every descendant;
all first-level vertices and all other subtrees are fixed.  Concretely, on a word whose last
(= root-level) letter is `y` and whose second-to-last (= level-one) letter is `x`, the level-one
letter is replaced by `swap a b x` when `y = a`, and left alone otherwise.

* `subtreeSwapAut a b : TreeAut α` is an involutive, root-preserving tree automorphism with
  explicit inverse (itself) and parent–child incidence preserved and reflected;
* `subtreeSwapAut_not_levelwise`: for `a ≠ b` it is not `treeAut P` for any levelwise `P`
  (the `toFun` maps already differ): it changes the new letter of `a :: [a]` but not that of
  `a :: [b]`, although both parents `[a]` and `[b]` have depth one;
* `levelwise_converse_false`: hence the converse "every tree automorphism is levelwise" fails
  for every alphabet with two distinct letters; instances for `Child two` and for the omega
  alphabet `TreeN`.
-/

open TreeN Word

namespace RayAutomorphism

variable {α : Type} [DecidableEq α]

/-- Level-one action, depending on the root-level letter `y` of the parent: under the parent
`[a]` swap `a` and `b`, under every other first-level vertex do nothing. -/
def condSwap (a b y x : α) : α :=
  match decEq y a with
  | isTrue _ => swap a b x
  | isFalse _ => x

theorem condSwap_condSwap (a b y x : α) : condSwap a b y (condSwap a b y x) = x := by
  unfold condSwap
  cases decEq y a with
  | isTrue _ => exact swap_swap a b x
  | isFalse _ => rfl

theorem condSwap_of_eq {a b y : α} (h : y = a) (x : α) : condSwap a b y x = swap a b x := by
  unfold condSwap
  cases decEq y a with
  | isTrue _ => rfl
  | isFalse h' => exact absurd h h'

theorem condSwap_of_ne {a b y : α} (h : y ≠ a) (x : α) : condSwap a b y x = x := by
  unfold condSwap
  cases decEq y a with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl

/-- The vertex-dependent automorphism swapping the subtrees rooted at `a :: [a]` and
`b :: [a]`.  Only the level-one letter (second from the end of the word) is touched, and only
when the root-level letter is `a`; letters at all other levels are copied. -/
def subtreeSwap (a b : α) : Word α → Word α
  | [] => []
  | [y] => [y]
  | [x, y] => [condSwap a b y x, y]
  | c :: d :: e :: w => c :: subtreeSwap a b (d :: e :: w)

theorem subtreeSwap_subtreeSwap (a b : α) : (w : Word α) → subtreeSwap a b (subtreeSwap a b w) = w
  | [] => rfl
  | [_] => rfl
  | [x, y] => by
    show [condSwap a b y (condSwap a b y x), y] = [x, y]
    rw [condSwap_condSwap]
  | c :: d :: e :: w => by
    show subtreeSwap a b (c :: subtreeSwap a b (d :: e :: w)) = c :: d :: e :: w
    have ih := subtreeSwap_subtreeSwap a b (d :: e :: w)
    revert ih
    generalize subtreeSwap a b (d :: e :: w) = u
    intro ih
    match u, ih with
    | d' :: e' :: w', ih => exact congrArg (List.cons c) ih
    | [], ih => exact nomatch ih
    | [_], ih => exact nomatch ih

/-- One step down the tree: the image of a child `c :: p` is a child of the image of `p`. -/
theorem subtreeSwap_cons (a b c : α) : (p : Word α) →
    ∃ c' : α, subtreeSwap a b (c :: p) = c' :: subtreeSwap a b p
  | [] => ⟨c, rfl⟩
  | [y] => ⟨condSwap a b y c, rfl⟩
  | _ :: _ :: _ => ⟨c, rfl⟩

theorem subtreeSwap_isParent (a b : α) {p v : Word α} (h : IsParent p v) :
    IsParent (subtreeSwap a b p) (subtreeSwap a b v) := by
  obtain ⟨c, hc⟩ := h
  rw [hc]
  obtain ⟨c', hc'⟩ := subtreeSwap_cons a b c p
  exact ⟨c', hc'⟩

/-- **The subtree swap is a root- and incidence-preserving tree automorphism**, with explicit
inverse (itself). -/
def subtreeSwapAut (a b : α) : TreeAut α where
  toFun := subtreeSwap a b
  invFun := subtreeSwap a b
  left_inv := subtreeSwap_subtreeSwap a b
  right_inv := subtreeSwap_subtreeSwap a b
  map_root := rfl
  map_parent := fun _ _ h => subtreeSwap_isParent a b h
  reflect_parent := fun p v h => by
    have h' := subtreeSwap_isParent a b h
    rw [subtreeSwap_subtreeSwap, subtreeSwap_subtreeSwap] at h'
    exact h'

theorem subtreeSwapAut_root (a b : α) : (subtreeSwapAut a b).toFun root = root := rfl

/-- First-level vertices are fixed. -/
theorem subtreeSwap_level_one (a b y : α) : subtreeSwap a b [y] = [y] := rfl

/-- The vertex `a :: [a]` is sent to `b :: [a]` (its new letter changes) ... -/
theorem subtreeSwap_aa (a b : α) : subtreeSwap a b [a, a] = [b, a] := by
  show [condSwap a b a a, a] = [b, a]
  rw [condSwap_of_eq rfl, swap_left]

/-- ... and `b :: [a]` is sent to `a :: [a]` ... -/
theorem subtreeSwap_ba (a b : α) (hab : a ≠ b) : subtreeSwap a b [b, a] = [a, a] := by
  show [condSwap a b a b, a] = [a, a]
  rw [condSwap_of_eq rfl, swap_of_eq_right (fun e => hab e.symm) rfl]

/-- ... while `a :: [b]` is fixed (parent `[b]` is not `[a]`). -/
theorem subtreeSwap_ab (a b : α) (hab : a ≠ b) : subtreeSwap a b [a, b] = [a, b] := by
  show [condSwap a b b a, b] = [a, b]
  rw [condSwap_of_ne (fun e => hab e.symm)]

/-- **Action on every descendant.** A vertex `w ++ [x, y]` lies in the subtree rooted at the
level-two vertex `x :: [y]`; it is sent to `w ++ [condSwap a b y x, y]`, i.e. the descendant
path `w` is copied verbatim into the image subtree. -/
theorem subtreeSwap_append (a b x y : α) : (w : Word α) →
    subtreeSwap a b (w ++ [x, y]) = w ++ [condSwap a b y x, y]
  | [] => rfl
  | c :: w => by
    show subtreeSwap a b (c :: (w ++ [x, y])) = c :: (w ++ [condSwap a b y x, y])
    have ih := subtreeSwap_append a b x y w
    match w, ih with
    | [], ih => exact congrArg (List.cons c) ih
    | d :: w', ih =>
      show subtreeSwap a b (c :: d :: (w' ++ [x, y])) = c :: (d :: w' ++ [condSwap a b y x, y])
      have hne : ∃ e r, w' ++ [x, y] = e :: r := by
        cases w' with
        | nil => exact ⟨x, [y], rfl⟩
        | cons e r => exact ⟨e, r ++ [x, y], rfl⟩
      obtain ⟨e, r, her⟩ := hne
      have ih' : subtreeSwap a b (d :: e :: r) = d :: w' ++ [condSwap a b y x, y] := by
        rw [← her]; exact ih
      rw [her]
      exact congrArg (List.cons c) ih'

/-- The whole subtree below `a :: [a]` is carried onto the subtree below `b :: [a]` ... -/
theorem subtreeSwap_append_aa (a b : α) (w : Word α) :
    subtreeSwap a b (w ++ [a, a]) = w ++ [b, a] := by
  rw [subtreeSwap_append, condSwap_of_eq rfl, swap_left]

/-- ... the subtree below `b :: [a]` onto the subtree below `a :: [a]` ... -/
theorem subtreeSwap_append_ba (a b : α) (hab : a ≠ b) (w : Word α) :
    subtreeSwap a b (w ++ [b, a]) = w ++ [a, a] := by
  rw [subtreeSwap_append, condSwap_of_eq rfl, swap_of_eq_right (fun e => hab e.symm) rfl]

/-- ... and every subtree below a level-two vertex `x :: [y]` with `y ≠ a`, or with `y = a`
and `x ∉ {a, b}`, is fixed pointwise. -/
theorem subtreeSwap_append_fixed (a b x y : α) (h : y ≠ a ∨ (x ≠ a ∧ x ≠ b)) (w : Word α) :
    subtreeSwap a b (w ++ [x, y]) = w ++ [x, y] := by
  rw [subtreeSwap_append]
  cases h with
  | inl hy => rw [condSwap_of_ne hy]
  | inr hx =>
    cases decEq y a with
    | isTrue hy => rw [condSwap_of_eq hy, swap_of_ne hx.1 hx.2]
    | isFalse hy => rw [condSwap_of_ne hy]

/-- **Q14 counterexample.** For distinct letters `a ≠ b`, the subtree swap is not induced by
any levelwise permutation: `(treeAut P).toFun ≠ (subtreeSwapAut a b).toFun` for all `P`.

Proof: `treeAut P` sends `a :: [a]` to `P.perm one a :: [P.perm zero a]` and `a :: [b]` to
`P.perm one a :: [P.perm zero b]` — the level-zero action only changes the parent letters, and
the new letter is `P.perm one a` in both cases because both parents have depth `one`.  The
subtree swap gives new letters `b` and `a` respectively, forcing `a = b`. -/
theorem subtreeSwapAut_not_levelwise (a b : α) (hab : a ≠ b) (P : LevelPerm α) :
    (treeAut P).toFun ≠ (subtreeSwapAut a b).toFun := by
  intro h
  have h1 : wordAct P [a, a] = subtreeSwap a b [a, a] := congrFun h [a, a]
  have h2 : wordAct P [a, b] = subtreeSwap a b [a, b] := congrFun h [a, b]
  rw [subtreeSwap_aa] at h1
  rw [subtreeSwap_ab a b hab] at h2
  have e1 : P.perm (depth [a]) a = b := List.head_eq_of_cons_eq h1
  have e2 : P.perm (depth [b]) a = a := List.head_eq_of_cons_eq h2
  have e3 : depth [b] = depth [a] := rfl
  rw [e3, e1] at e2
  exact hab e2.symm

/-- **The levelwise converse is false** for every alphabet with two distinct letters: not every
root- and incidence-preserving tree automorphism is induced by a levelwise permutation. -/
theorem levelwise_converse_false (a b : α) (hab : a ≠ b) :
    ¬ ∀ T : TreeAut α, ∃ P : LevelPerm α, (treeAut P).toFun = T.toFun := fun hall =>
  match hall (subtreeSwapAut a b) with
  | ⟨P, hP⟩ => subtreeSwapAut_not_levelwise a b hab P hP

end RayAutomorphism

/-- Binary finite-arity instance (`Child two`, letters `0` and `1`). -/
theorem binary_levelwise_converse_false :
    ¬ ∀ T : RayAutomorphism.TreeAut (Child two),
      ∃ P : RayAutomorphism.LevelPerm (Child two), (RayAutomorphism.treeAut P).toFun = T.toFun :=
  RayAutomorphism.levelwise_converse_false _ _
    (Child.first_ne_second (zero_lt_succ one) (lt_succ_self one))

/-- Omega instance (alphabet `TreeN`, letters `zero` and `one`). -/
theorem omega_levelwise_converse_false :
    ¬ ∀ T : RayAutomorphism.TreeAut TreeN,
      ∃ P : RayAutomorphism.LevelPerm TreeN, (RayAutomorphism.treeAut P).toFun = T.toFun :=
  RayAutomorphism.levelwise_converse_false zero one (fun e => nomatch e)

end
