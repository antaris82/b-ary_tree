module

public import BoundaryTopology.PrefixTopology

@[expose] public section

/-!
# Checkpoint F2 — topological structure of the three kinds of boundary

General notions (for a `Topology X`): `Connected`, `Compact` (open covers indexed by an
arbitrary type, finite subcovers given by explicit lists), `IsNbhd`, `LocallyCompactAt`,
`IsolatedPoint`.

* **Unary branching** (`b = one`): there is exactly one ray; it is an isolated point.
* **At least two letters** (finite `b ≥ 2` or omega): no isolated points (`no_isolated`,
  `not_isolated`), the whole boundary is disconnected by the nontrivial clopen cylinder `[l0]`,
  no inhabited open set is connected, and every connected subset is a subsingleton
  (total disconnectedness — proved constructively).  Together with the clopen cylinder basis
  (`isOpen_iff_cylinders`) this is zero-dimensionality in the clopen-basis sense.
* **Omega branching**: no cylinder is compact (`cyl_not_compact`: its child cylinders form an
  open cover with no finite subcover) and no point has a compact neighbourhood
  (`not_locallyCompactAt`).

Compactness of the finite-arity boundary (`b ≥ 2`) is **not proved**: in the present
choice-free constructive setting it would require a fan-theorem-type principle.
-/

open TreeN ListOps Word

namespace Topology

variable {X : Type} (T : Topology X)

/-- Connectedness of a subset: no separation by two open sets. -/
def Connected (S : X → Prop) : Prop :=
  ∀ U V : X → Prop, T.IsOpen U → T.IsOpen V → (∀ x, S x → U x ∨ V x) →
    (∀ x, S x → U x → V x → False) → (∃ x, S x ∧ U x) → (∃ x, S x ∧ V x) → False

/-- Compactness of a subset: every open cover has an explicitly listed finite subcover. -/
def Compact (S : X → Prop) : Prop :=
  ∀ (ι : Type) (F : ι → X → Prop), (∀ i, T.IsOpen (F i)) → (∀ x, S x → ∃ i, F i x) →
    ∃ l : List ι, ∀ x, S x → ∃ i, InL i l ∧ F i x

/-- Neighbourhoods. -/
def IsNbhd (N : X → Prop) (x : X) : Prop := ∃ U, T.IsOpen U ∧ U x ∧ ∀ y, U y → N y

/-- Local compactness at a point. -/
def LocallyCompactAt (x : X) : Prop := ∃ N, T.IsNbhd N x ∧ T.Compact N

/-- Isolated points. -/
def IsolatedPoint (x : X) : Prop := T.IsOpen (fun y => y = x)

end Topology

namespace Ray

variable {α : Type}

/-! ## Unary branching -/

theorem unary_ray_unique (r r' : Ray (Child TreeN.one)) : r = r' :=
  funext (fun n => (Child.one_unique (r n)).trans (Child.one_unique (r' n)).symm)

/-- The unary boundary is a singleton. -/
theorem unary_singleton : ∃ r : Ray (Child TreeN.one), ∀ r', r' = r :=
  ⟨const (Child.first (zero_lt_succ TreeN.zero)), fun _ => unary_ray_unique _ _⟩

/-- Its point is isolated. -/
theorem unary_isolated (r : Ray (Child TreeN.one)) :
    (prefixTopology (Child TreeN.one)).IsolatedPoint r :=
  fun _ _ => ⟨TreeN.zero, fun r' _ => unary_ray_unique r' r⟩

/-! ## At least two letters -/

section Two

variable [DecidableEq α] [TwoLetters α]

/-- **No isolated points**: every open neighbourhood of `r` contains a ray differing from `r`
at an explicitly given position. -/
theorem no_isolated {U : Ray α → Prop} (hU : PrefixOpen U) {r : Ray α} (hr : U r) :
    ∃ r' n, U r' ∧ r' n ≠ r n := by
  obtain ⟨n, hn⟩ := hU r hr
  refine ⟨modify r n (other (r n)), n, hn _ (agree_modify r n _), ?_⟩
  rw [modify_at]
  exact other_ne (r n)

theorem not_isolated (r : Ray α) : ¬ (prefixTopology α).IsolatedPoint r := by
  intro h
  obtain ⟨r', n, e, hne⟩ := no_isolated h rfl
  rw [e] at hne
  exact hne rfl

omit [DecidableEq α] in
/-- The nontrivial clopen cylinder `[l0]`. -/
theorem cyl_l0_nontrivial :
    Cyl [TwoLetters.l0] (const (TwoLetters.l0 : α)) ∧ ¬ Cyl [TwoLetters.l0] (const (TwoLetters.l1 : α)) :=
  ⟨rfl, fun h => by
    have h' : [(TwoLetters.l1 : α)] = [TwoLetters.l0] := h
    injection h' with h1
    exact TwoLetters.ne h1.symm⟩

omit [TwoLetters α] in
/-- Separation of a subset by a cylinder and its complement. -/
theorem not_connected_of_cyl {S : Ray α → Prop} (w : Word α) {x y : Ray α} (hx : S x) (hy : S y)
    (hxw : Cyl w x) (hyw : ¬ Cyl w y) : ¬ (prefixTopology α).Connected S := by
  intro hc
  apply hc (Cyl w) (fun r => ¬ Cyl w r) (cyl_open w) (cyl_compl_open w)
  · intro z _
    match decCyl w z with
    | isTrue h => exact Or.inl h
    | isFalse h => exact Or.inr h
  · intro z _ h1 h2
    exact h2 h1
  · exact ⟨x, hx, hxw⟩
  · exact ⟨y, hy, hyw⟩

/-- The boundary is disconnected. -/
theorem boundary_disconnected : ¬ (prefixTopology α).Connected (fun _ => True) :=
  not_connected_of_cyl [TwoLetters.l0] True.intro True.intro cyl_l0_nontrivial.1
    cyl_l0_nontrivial.2

/-- No inhabited open set is connected. -/
theorem open_not_connected {S : Ray α → Prop} (hS : PrefixOpen S) {r : Ray α} (hr : S r) :
    ¬ (prefixTopology α).Connected S := by
  obtain ⟨r', n, hr', hne⟩ := no_isolated hS hr
  have sep := separate_of_diff (fun e => hne e.symm)
  exact not_connected_of_cyl _ hr hr' sep.1 sep.2.2.2

omit [TwoLetters α] in
/-- **Total disconnectedness**: connected subsets are subsingletons (any alphabet with
decidable letter equality). -/
theorem connected_subsingleton {S : Ray α → Prop} (hc : (prefixTopology α).Connected S)
    {x y : Ray α} (hx : S x) (hy : S y) : x = y := by
  apply eq_of_not_diff
  intro ⟨n, hne⟩
  have sep := separate_of_diff hne
  exact not_connected_of_cyl _ hx hy sep.1 sep.2.2.2 hc

end Two

/-! ## Omega branching: failure of (local) compactness -/

/-- Maximum of a finite list of path counts. -/
def foldMax : List TreeN → TreeN
  | [] => TreeN.zero
  | n :: l => maxN n (foldMax l)

theorem le_foldMax {n : TreeN} : ∀ {l : List TreeN}, InL n l → PathLE n (foldMax l)
  | [], h => False.elim h
  | m :: l, h => by
    cases h with
    | inl e => rw [e]; exact le_maxN_left _ _
    | inr h' => exact le_trans (le_foldMax h') (le_maxN_right _ _)

theorem cyl_child_cover (w : Word TreeN) (x : Ray TreeN) (hx : Cyl w x) : Cyl (x (depth w) :: w) x := by
  show prefixAt x (succ (depth w)) = x (depth w) :: w
  rw [prefixAt_succ]
  exact congrArg (List.cons (x (depth w))) hx

/-- **No cylinder of the omega boundary is compact.** -/
theorem cyl_not_compact (w : Word TreeN) : ¬ (prefixTopology TreeN).Compact (Cyl w) := by
  intro hc
  obtain ⟨l, hl⟩ := hc TreeN (fun m => Cyl (m :: w)) (fun m => cyl_open _)
    (fun x hx => ⟨x (depth w), cyl_child_cover w x hx⟩)
  let m := succ (foldMax l)
  let x := rayOf (const m) w
  obtain ⟨i, hi, hxi⟩ := hl x (rayOf_cyl _ w)
  have h1 : prefixAt x (succ (depth w)) = i :: w := hxi
  rw [prefixAt_succ] at h1
  injection h1 with h2 _
  have h3 : x (depth w) = m := rayOf_tail _ w (le_refl _)
  rw [h3] at h2
  have h4 := le_foldMax hi
  rw [← h2] at h4
  exact lt_irrefl _ (lt_of_le_of_lt h4 (lt_succ_self _))

/-- Dropping the `none` entries of a list of options. -/
def dropNone {ι : Type} : List (Option ι) → List ι
  | [] => []
  | none :: l => dropNone l
  | some i :: l => i :: dropNone l

theorem inL_dropNone {ι : Type} {i : ι} : ∀ {l : List (Option ι)}, InL (some i) l → InL i (dropNone l)
  | [], h => False.elim h
  | none :: l, h => by
    cases h with
    | inl e => exact nomatch e
    | inr h' => exact inL_dropNone (l := l) h'
  | some j :: l, h => by
    cases h with
    | inl e =>
      injection e with e'
      exact Or.inl e'
    | inr h' => exact Or.inr (inL_dropNone h')

/-- A cylinder contained in a compact set is compact. -/
theorem compact_cyl_of_sub [DecidableEq α] {N : Ray α → Prop} (w : Word α)
    (hN : (prefixTopology α).Compact N) (hsub : ∀ x, Cyl w x → N x) :
    (prefixTopology α).Compact (Cyl w) := by
  intro ι F hF hcov
  obtain ⟨l, hl⟩ := hN (Option ι)
    (fun o x => match o with
      | none => ¬ Cyl w x
      | some i => F i x)
    (fun o => match o with
      | none => cyl_compl_open w
      | some i => hF i)
    (fun x _ => match decCyl w x with
      | isTrue h => (hcov x h).elim (fun i hi => ⟨some i, hi⟩)
      | isFalse h => ⟨none, h⟩)
  refine ⟨dropNone l, fun x hx => ?_⟩
  obtain ⟨o, ho, hxo⟩ := hl x (hsub x hx)
  cases o with
  | none => exact absurd hx hxo
  | some i => exact ⟨i, inL_dropNone ho, hxo⟩

/-- **The omega boundary is not locally compact at any point.** -/
theorem not_locallyCompactAt (r : Ray TreeN) : ¬ (prefixTopology TreeN).LocallyCompactAt r := by
  intro ⟨N, ⟨U, hU, hrU, hUN⟩, hc⟩
  obtain ⟨n, hn⟩ := hU r hrU
  exact cyl_not_compact (prefixAt r n) (compact_cyl_of_sub (prefixAt r n) hc
    (fun x hx => hUN x (hn x (agree_of_cyl_prefixAt hx))))

end Ray
end
