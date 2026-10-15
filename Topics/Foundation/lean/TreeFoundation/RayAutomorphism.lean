module

public import TreeFoundation.InfiniteRays

@[expose] public section

/-!
# Levelwise permutations, tree automorphisms, and homogeneity of rays

For an alphabet `α` a *levelwise permutation* is a family, indexed by the levels `n : TreeN`, of
mutually inverse maps `α → α`.  It acts on words level by level: the letter that sits at level
`n` (i.e. on top of a word of depth `n`) is moved by the permutation of level `n`.

* `wordAct P` preserves the root, depth and parent–child incidence in both directions, and has
  the explicit inverse `wordAct P.symm`: it is a root-preserving tree automorphism;
* `rayAct P` is the induced action on rays, compatible with finite prefixes;
* for any two rays `ξ, η` the explicit levelwise swaps `swapPerm ξ η` (each level swaps the two
  indicated symbols, using decidable equality of the alphabet) send `ξ` to `η`;
* hence every function on rays invariant under all these automorphisms is constant.

Only decidable equality of the alphabet is used (no selection principle); in particular the
statement holds for every finite arity `Child b` (any `b`, including `b ≥ two`) and for the omega
alphabet `TreeN`.  Nothing here assigns a numerical value to rays.
-/

open TreeN Word Ray

namespace RayAutomorphism

variable {α : Type}

/-- A levelwise permutation of the child symbols, with explicit inverse. -/
structure LevelPerm (α : Type) where
  perm : TreeN → α → α
  inv : TreeN → α → α
  inv_perm : ∀ n a, inv n (perm n a) = a
  perm_inv : ∀ n a, perm n (inv n a) = a

/-- The inverse levelwise permutation. -/
def LevelPerm.symm (P : LevelPerm α) : LevelPerm α :=
  ⟨P.inv, P.perm, P.perm_inv, P.inv_perm⟩

/-- Action on words: the letter on top of a word of depth `n` is moved by `perm n`. -/
def wordAct (P : LevelPerm α) : Word α → Word α
  | [] => []
  | c :: w => P.perm (depth w) c :: wordAct P w

theorem wordAct_root (P : LevelPerm α) : wordAct P root = root := rfl

theorem wordAct_cons (P : LevelPerm α) (c : α) (w : Word α) :
    wordAct P (c :: w) = P.perm (depth w) c :: wordAct P w := rfl

/-- The action preserves finite levels (depth). -/
theorem depth_wordAct (P : LevelPerm α) (w : Word α) : depth (wordAct P w) = depth w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    show succ (depth (wordAct P w)) = succ (depth w)
    rw [ih]

theorem pathSum_wordAct (P : LevelPerm α) (w : Word α) : pathSum (wordAct P w) = pathSum w := by
  rw [pathSum_eq_depth, pathSum_eq_depth, depth_wordAct]

/-- The inverse action undoes the action. -/
theorem wordAct_symm_wordAct (P : LevelPerm α) (w : Word α) :
    wordAct P.symm (wordAct P w) = w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    show P.inv (depth (wordAct P w)) (P.perm (depth w) c) :: wordAct P.symm (wordAct P w) = c :: w
    rw [depth_wordAct, P.inv_perm, ih]

theorem wordAct_wordAct_symm (P : LevelPerm α) (w : Word α) :
    wordAct P (wordAct P.symm w) = w :=
  wordAct_symm_wordAct P.symm w

theorem wordAct_injective (P : LevelPerm α) {w v : Word α} (h : wordAct P w = wordAct P v) :
    w = v := by
  rw [← wordAct_symm_wordAct P w, h, wordAct_symm_wordAct]

/-- Parent–child incidence is preserved ... -/
theorem wordAct_isParent (P : LevelPerm α) {p v : Word α} (h : IsParent p v) :
    IsParent (wordAct P p) (wordAct P v) := by
  obtain ⟨c, hc⟩ := h
  rw [hc]
  exact ⟨P.perm (depth p) c, rfl⟩

/-- ... and reflected. -/
theorem isParent_of_wordAct (P : LevelPerm α) {p v : Word α}
    (h : IsParent (wordAct P p) (wordAct P v)) : IsParent p v := by
  have h' := wordAct_isParent P.symm h
  rw [wordAct_symm_wordAct, wordAct_symm_wordAct] at h'
  exact h'

/-- The action on edge records. -/
def edgeAct (P : LevelPerm α) (e : Edge α) : Edge α :=
  ⟨wordAct P e.parent, P.perm (depth e.parent) e.sym, wordAct P e.child, by
    rw [e.incid]; rfl⟩

/-- A root- and incidence-preserving tree automorphism, with explicit inverse. -/
structure TreeAut (α : Type) where
  toFun : Word α → Word α
  invFun : Word α → Word α
  left_inv : ∀ w, invFun (toFun w) = w
  right_inv : ∀ w, toFun (invFun w) = w
  map_root : toFun root = root
  map_parent : ∀ p v, IsParent p v → IsParent (toFun p) (toFun v)
  reflect_parent : ∀ p v, IsParent (toFun p) (toFun v) → IsParent p v

/-- The tree automorphism induced by a levelwise permutation. -/
def treeAut (P : LevelPerm α) : TreeAut α where
  toFun := wordAct P
  invFun := wordAct P.symm
  left_inv := wordAct_symm_wordAct P
  right_inv := wordAct_wordAct_symm P
  map_root := rfl
  map_parent := fun _ _ h => wordAct_isParent P h
  reflect_parent := fun _ _ h => isParent_of_wordAct P h

/-! ## Action on rays -/

/-- The induced action on rays. -/
def rayAct (P : LevelPerm α) (r : Ray α) : Ray α := fun n => P.perm n (r n)

/-- Compatibility with finite prefixes: the action on rays is the levelwise limit of the tree
automorphism. -/
theorem prefixAt_rayAct (P : LevelPerm α) (r : Ray α) (n : TreeN) :
    prefixAt (rayAct P r) n = wordAct P (prefixAt r n) := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    show P.perm n (r n) :: prefixAt (rayAct P r) n = wordAct P (r n :: prefixAt r n)
    rw [wordAct_cons, depth_prefixAt, ih]

theorem rayAct_symm_rayAct (P : LevelPerm α) (r : Ray α) : rayAct P.symm (rayAct P r) = r :=
  funext (fun n => P.inv_perm n (r n))

/-! ## Explicit swaps -/

variable [DecidableEq α]

/-- The transposition of `a` and `b` (decidable equality only). -/
def swap (a b : α) (x : α) : α :=
  match decEq x a with
  | isTrue _ => b
  | isFalse _ =>
    match decEq x b with
    | isTrue _ => a
    | isFalse _ => x

theorem swap_of_eq_left {a b x : α} (h : x = a) : swap a b x = b := by
  unfold swap
  cases decEq x a with
  | isTrue _ => rfl
  | isFalse h' => exact absurd h h'

theorem swap_of_eq_right {a b x : α} (h1 : x ≠ a) (h2 : x = b) : swap a b x = a := by
  unfold swap
  cases decEq x a with
  | isTrue h' => exact absurd h' h1
  | isFalse _ =>
    cases decEq x b with
    | isTrue _ => rfl
    | isFalse h' => exact absurd h2 h'

theorem swap_of_ne {a b x : α} (h1 : x ≠ a) (h2 : x ≠ b) : swap a b x = x := by
  unfold swap
  cases decEq x a with
  | isTrue h' => exact absurd h' h1
  | isFalse _ =>
    cases decEq x b with
    | isTrue h' => exact absurd h' h2
    | isFalse _ => rfl

theorem swap_left (a b : α) : swap a b a = b := swap_of_eq_left rfl

theorem swap_swap (a b x : α) : swap a b (swap a b x) = x := by
  cases decEq x a with
  | isTrue h1 =>
    rw [swap_of_eq_left h1]
    cases decEq b a with
    | isTrue h2 => rw [swap_of_eq_left h2, h1, h2]
    | isFalse h2 => rw [swap_of_eq_right h2 rfl, h1]
  | isFalse h1 =>
    cases decEq x b with
    | isTrue h2 => rw [swap_of_eq_right h1 h2, swap_left, h2]
    | isFalse h2 => rw [swap_of_ne h1 h2, swap_of_ne h1 h2]

/-- The levelwise swaps sending the symbols of `ξ` to those of `η`. -/
def swapPerm (ξ η : Ray α) : LevelPerm α where
  perm := fun n => swap (ξ n) (η n)
  inv := fun n => swap (ξ n) (η n)
  inv_perm := fun _ a => swap_swap _ _ a
  perm_inv := fun _ a => swap_swap _ _ a

/-- **Ray homogeneity**: the explicit levelwise swaps send `ξ` to `η`. -/
theorem rayAct_swapPerm (ξ η : Ray α) : rayAct (swapPerm ξ η) ξ = η :=
  funext (fun n => swap_left (ξ n) (η n))

/-- Prefix form: the induced tree automorphism maps every finite prefix of `ξ` to the prefix of
`η` of the same length. -/
theorem treeAut_swapPerm_prefix (ξ η : Ray α) (n : TreeN) :
    (treeAut (swapPerm ξ η)).toFun (prefixAt ξ n) = prefixAt η n := by
  show wordAct (swapPerm ξ η) (prefixAt ξ n) = prefixAt η n
  rw [← prefixAt_rayAct, rayAct_swapPerm]

/-- **Every function on rays invariant under the levelwise-permutation automorphisms is
constant.** -/
theorem invariant_const {β : Type} (F : Ray α → β)
    (hF : ∀ (P : LevelPerm α) (r : Ray α), F (rayAct P r) = F r) (ξ η : Ray α) : F ξ = F η := by
  rw [← rayAct_swapPerm ξ η, hF]

/-- Invariance under the swap automorphisms alone already suffices. -/
theorem swapInvariant_const {β : Type} (F : Ray α → β)
    (hF : ∀ ξ η r : Ray α, F (rayAct (swapPerm ξ η) r) = F r) (ξ η : Ray α) : F ξ = F η := by
  rw [← rayAct_swapPerm ξ η, hF]

end RayAutomorphism

/-- Instance for finite arity (decidable equality of `Child b` is constructive).  The statement
holds for every `b`; the hypothesis `b ≥ two` mentioned in the task is not needed (for `b ≤ one`
there is at most one ray, so the statement is then trivial in content). -/
theorem finiteRay_homogeneous (b : TreeN) (ξ η : RayFinite b) :
    RayAutomorphism.rayAct (RayAutomorphism.swapPerm ξ η) ξ = η :=
  RayAutomorphism.rayAct_swapPerm ξ η

/-- Instance for the omega alphabet. -/
theorem omegaRay_homogeneous (ξ η : RayOmega) :
    RayAutomorphism.rayAct (RayAutomorphism.swapPerm ξ η) ξ = η :=
  RayAutomorphism.rayAct_swapPerm ξ η

end
