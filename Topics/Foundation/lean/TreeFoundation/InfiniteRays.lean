module

public import TreeFoundation.OmegaTree

@[expose] public section

/-!
# Infinite rays

All sequence positions and truncation lengths are unary paths (`TreeN`).

* `Ray α := TreeN → α` (for `α = Child b` or `α = TreeN`);
* `prefixAt r n` is the finite vertex reached after the steps at positions below `n`.
-/

open TreeN ListOps Word ArityEmbedding

/-- Infinite rays over an alphabet. -/
abbrev Ray (α : Type) : Type := TreeN → α

/-- Finite-arity rays and omega rays. -/
abbrev RayFinite (b : TreeN) : Type := Ray (Child b)
abbrev RayOmega : Type := Ray TreeN

namespace Ray

variable {α : Type}

/-- The finite prefix of length `n` (structural recursion on the unary path `n`). -/
def prefixAt (r : Ray α) : TreeN → Word α
  | [] => []
  | _ :: n => r n :: prefixAt r n

theorem prefixAt_succ (r : Ray α) (n : TreeN) : prefixAt r (succ n) = r n :: prefixAt r n := rfl

/-- The prefix of length `n` has depth (and primitive path length) `n`. -/
theorem depth_prefixAt (r : Ray α) (n : TreeN) : depth (prefixAt r n) = n := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    show succ (depth (prefixAt r n)) = c :: n
    rw [ih, UnaryPath.cons_eq_extend]

theorem pathSum_prefixAt (r : Ray α) (n : TreeN) : pathSum (prefixAt r n) = n := by
  rw [pathSum_eq_depth, depth_prefixAt]

/-- Consecutive prefixes are joined by an edge. -/
theorem prefixAt_isParent (r : Ray α) (n : TreeN) :
    IsParent (prefixAt r n) (prefixAt r (succ n)) := ⟨r n, rfl⟩

/-- Prefix characterization: shorter prefixes lie on the root path of longer ones. -/
theorem prefixAt_isDesc (r : Ray α) {m n : TreeN} (h : PathLE m n) :
    IsDesc (prefixAt r m) (prefixAt r n) := by
  obtain ⟨k, hk⟩ := exists_of_le h
  rw [hk]
  clear hk h
  induction k with
  | nil => rw [show m + [] = m from add_zero m]; exact isDesc_refl _
  | cons c k ih =>
    have e : m + c :: k = succ (m + k) := by rw [UnaryPath.cons_eq_extend, add_succ]
    rw [e, prefixAt_succ]
    exact isDesc_cons _ ih

/-- The prefixes determine the ray. -/
theorem eq_of_prefixAt {r r' : Ray α} (h : ∀ n, prefixAt r n = prefixAt r' n) (n : TreeN) :
    r n = r' n := by
  have e := h (succ n)
  rw [prefixAt_succ, prefixAt_succ] at e
  injection e

/-- Each finite prefix has a unique directed root path. -/
theorem prefixAt_root_path_unique (r : Ray α) (n : TreeN) {es : List (Edge α)}
    (h : DPath root (prefixAt r n) es) : es = rootEdges (prefixAt r n) :=
  dpath_root_unique h

/-- Strictly increasing intrinsic depths. -/
theorem depth_strictMono (r : Ray α) {m n : TreeN} (h : PathLT m n) :
    PathLT (depth (prefixAt r m)) (depth (prefixAt r n)) := by
  rw [depth_prefixAt, depth_prefixAt]
  exact h

/-- Unbounded intrinsic depths. -/
theorem depth_unbounded (r : Ray α) (n : TreeN) : ∃ m, PathLT n (depth (prefixAt r m)) :=
  ⟨succ n, by rw [depth_prefixAt]; exact lt_succ_self n⟩

end Ray

namespace RayOmega

open Ray

/-- Inclusion of finite-arity rays into omega rays (same intrinsic indices). -/
def ofFinite {b : TreeN} (r : RayFinite b) : RayOmega := fun n => (r n).idx

theorem prefixAt_ofFinite {b : TreeN} (r : RayFinite b) (n : TreeN) :
    prefixAt (ofFinite r) n = wordOmega (prefixAt r n) := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    show (r n).idx :: prefixAt (ofFinite r) n = (r n).idx :: wordOmega (prefixAt r n)
    rw [ih]

/-- The identity (unbounded) ray `ξ(n) := n`. -/
def identityRay : RayOmega := fun n => n

/-- **Properness**: for every finite arity `b`, the identity ray is not the inclusion of any
arity-`b` ray; the contradiction comes from the index bound at position `b`. -/
theorem identityRay_not_finite (b : TreeN) (r : RayFinite b) : ¬ (∀ n, ofFinite r n = identityRay n) := by
  intro h
  have e : (r b).idx = b := h b
  have hl := (r b).lt
  rw [e] at hl
  exact lt_irrefl b hl

/-- The union of finite-arity rays included into omega rays is proper. -/
theorem union_proper : ∃ ξ : RayOmega, ∀ b : TreeN, ∀ r : RayFinite b, ¬ (∀ n, ofFinite r n = ξ n) :=
  ⟨identityRay, identityRay_not_finite⟩

end RayOmega
end
