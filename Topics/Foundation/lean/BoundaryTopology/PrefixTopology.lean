module

public import BoundaryTopology.Cylinders
public import TreeAnalysis.PathMax

@[expose] public section

/-!
# Checkpoints F1, F3 — the prefix/cylinder topology

* `Topology X`: a topology given by its open predicates (whole space, binary intersections,
  unions indexed by an arbitrary type).  No library topology is used.
* `PrefixOpen U`: every point of `U` has a prefix length beyond which agreeing rays stay in `U`.
  `prefixTopology α` is the resulting topology on `Ray α`.
* Cylinders are open, their complements are open (clopen), membership is decidable, and the
  cylinders form a basis (`isOpen_iff_cylinders`).
* Separation: rays with a **supplied** differing position have disjoint clopen neighbourhoods;
  conversely an open set containing one ray and not the other yields such a position
  (`exists_diff_of_separated`).  From `r ≠ r'` alone only `¬¬ ∃ n, r n ≠ r' n` is derived.
* Prefix uniformity: the relations `Agree n` are equivalence relations, decreasing in `n`, with
  intersection the equality of rays; prefix-coherent sequences of rays have a limit ray
  (completeness of the prefix uniformity, a problem distinct from completing `TreeR`).
-/

open TreeN ListOps Word

/-- A topology, given by its open predicates. -/
structure Topology (X : Type) where
  IsOpen : (X → Prop) → Prop
  isOpen_univ : IsOpen (fun _ => True)
  isOpen_inter : ∀ U V, IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)
  isOpen_union : ∀ (ι : Type) (F : ι → X → Prop), (∀ i, IsOpen (F i)) → IsOpen (fun x => ∃ i, F i x)

namespace Ray

variable {α : Type}

/-- Openness for the prefix topology. -/
def PrefixOpen (U : Ray α → Prop) : Prop := ∀ r, U r → ∃ n : TreeN, ∀ r', Agree n r' r → U r'

/-- **The prefix (cylinder) topology** on rays. -/
def prefixTopology (α : Type) : Topology (Ray α) where
  IsOpen := PrefixOpen
  isOpen_univ := fun _ _ => ⟨TreeN.zero, fun _ _ => True.intro⟩
  isOpen_inter := fun U V hU hV r h => by
    obtain ⟨n1, h1⟩ := hU r h.1
    obtain ⟨n2, h2⟩ := hV r h.2
    exact ⟨maxN n1 n2, fun r' hr => ⟨h1 r' (agree_mono (le_maxN_left _ _) hr),
      h2 r' (agree_mono (le_maxN_right _ _) hr)⟩⟩
  isOpen_union := fun _ F hF r h => by
    obtain ⟨i, hi⟩ := h
    obtain ⟨n, hn⟩ := hF i r hi
    exact ⟨n, fun r' hr => ⟨i, hn r' hr⟩⟩

theorem isOpen_empty : PrefixOpen (fun _ : Ray α => False) := fun _ h => False.elim h

/-- Cylinders are open. -/
theorem cyl_open (w : Word α) : PrefixOpen (Cyl w) := fun _ hr =>
  ⟨depth w, fun _ h => h.trans hr⟩

/-- Complements of cylinders are open: cylinders are clopen. -/
theorem cyl_compl_open (w : Word α) : PrefixOpen (fun r => ¬ Cyl w r) := fun _ hr =>
  ⟨depth w, fun _ h hc => hr (h.symm.trans hc)⟩

/-- Membership in a cylinder is decidable. -/
def cyl_decidable [DecidableEq α] (w : Word α) (r : Ray α) : Decidable (Cyl w r) := decCyl w r

/-- **Cylinder basis**: every open set is the union of the cylinders it contains. -/
theorem isOpen_iff_cylinders (U : Ray α → Prop) :
    (PrefixOpen U → ∀ r, U r → ∃ w, Cyl w r ∧ ∀ r', Cyl w r' → U r') ∧
    ((∀ r, U r → ∃ w, Cyl w r ∧ ∀ r', Cyl w r' → U r') → PrefixOpen U) := by
  constructor
  · intro hU r hr
    obtain ⟨n, hn⟩ := hU r hr
    exact ⟨prefixAt r n, cyl_prefixAt r n, fun r' h => hn r' (agree_of_cyl_prefixAt h)⟩
  · intro h r hr
    obtain ⟨w, hw, hsub⟩ := h r hr
    exact ⟨depth w, fun r' ha => hsub r' (ha.trans hw)⟩

/-! ## Separation -/

/-- Rays with a supplied differing position have disjoint clopen neighbourhoods. -/
theorem separate_of_diff {r r' : Ray α} {n : TreeN} (h : r n ≠ r' n) :
    Cyl (prefixAt r (succ n)) r ∧ Cyl (prefixAt r' (succ n)) r' ∧
    (∀ x, Cyl (prefixAt r (succ n)) x → Cyl (prefixAt r' (succ n)) x → False) ∧
    ¬ Cyl (prefixAt r (succ n)) r' := by
  refine ⟨cyl_prefixAt r _, cyl_prefixAt r' _, fun x h1 h2 => ?_, fun h1 => ?_⟩
  · have a := agree_succ (agree_of_cyl_prefixAt h1)
    have b := agree_succ (agree_of_cyl_prefixAt h2)
    exact h (a.symm.trans b)
  · exact h (agree_succ (agree_of_cyl_prefixAt h1)).symm

/-- Conversely, an open set containing `r` but not `r'` yields a differing position. -/
theorem exists_diff_of_separated [DecidableEq α] {r r' : Ray α} {U : Ray α → Prop}
    (hU : PrefixOpen U) (hr : U r) (hr' : ¬ U r') : ∃ n, r n ≠ r' n := by
  obtain ⟨n, hn⟩ := hU r hr
  have h : ¬ Agree n r' r := fun ha => hr' (hn r' ha)
  obtain ⟨i, _, hi⟩ := exists_diff_of_not_agree h
  exact ⟨i, fun e => hi e.symm⟩

/-- From mere inequality of rays, only the double negation of a differing position follows. -/
theorem not_not_diff_of_ne [DecidableEq α] {r r' : Ray α} (h : r ≠ r') :
    ¬¬ ∃ n, r n ≠ r' n := by
  intro hn
  apply h
  funext n
  match decEq (r n) (r' n) with
  | isTrue e => exact e
  | isFalse ne => exact absurd ⟨n, ne⟩ hn

/-- Rays are equal as soon as no position can differ. -/
theorem eq_of_not_diff [DecidableEq α] {r r' : Ray α} (h : ¬ ∃ n, r n ≠ r' n) : r = r' := by
  funext n
  match decEq (r n) (r' n) with
  | isTrue e => exact e
  | isFalse ne => exact absurd ⟨n, ne⟩ h

/-! ## Prefix uniformity and prefix-coherent completeness -/

/-- The prefix entourages shrink with the length. -/
theorem agree_entourage_mono {m n : TreeN} (h : PathLE m n) {r r' : Ray α} :
    Agree n r r' → Agree m r r' := agree_mono h

/-- The intersection of the prefix entourages is the equality of rays. -/
theorem agree_all_iff (r r' : Ray α) : ((∀ n, Agree n r r') → r = r') ∧ (r = r' → ∀ n, Agree n r r') :=
  ⟨eq_of_agree_all, fun e n => by rw [e]; exact agree_refl n r'⟩

/-- A prefix-coherent sequence of rays: the `k`-th and `(k+1)`-st agree up to length `k`. -/
def PrefixCoherent (s : TreeN → Ray α) : Prop := ∀ k, Agree k (s k) (s (succ k))

/-- The limit ray of a prefix-coherent sequence. -/
def coherentLimit (s : TreeN → Ray α) : Ray α := fun i => s (succ i) i

theorem coherent_agree_le {s : TreeN → Ray α} (h : PrefixCoherent s) (k : TreeN) :
    ∀ d, Agree k (s k) (s (k + d)) := by
  intro d
  induction d with
  | nil =>
    rw [show k + [] = k from add_zero k]
    exact agree_refl _ _
  | cons c d ih =>
    have e : k + c :: d = succ (k + d) := by rw [UnaryPath.cons_eq_extend, add_succ]
    rw [e]
    exact agree_trans ih (agree_mono (le_add_right k d) (h (k + d)))

/-- **Completeness of the prefix uniformity**: a prefix-coherent sequence converges to its
limit ray in the sense of prefixes. -/
theorem coherentLimit_agree {s : TreeN → Ray α} (h : PrefixCoherent s) (k : TreeN) :
    Agree k (coherentLimit s) (s k) := by
  apply agree_of_pointwise
  intro i hi
  show s (succ i) i = s k i
  obtain ⟨d, hd⟩ := exists_of_le (succ_le_of_lt hi)
  have h1 := coherent_agree_le h (succ i) d
  rw [← hd] at h1
  exact pointwise_of_agree h1 i (lt_succ_self i)

end Ray
end
