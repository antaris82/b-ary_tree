module

public import TreeNumbers.PathFractions
public import PrimitiveTree.RootEdges

@[expose] public section

/-!
# Triple-path configurations

A triple-path configuration over an alphabet `α` is an ordered triple of pairwise distinct
actual finite root paths `(P1, P2, P3)` with `pathSum P2 > pathSum P3`.  It determines

* the numerator `A := [pathSum P1, pathSum P2] : TreeZ`;
* the denominator `D : TreeN`, the strictly positive path-length gap between `P2` and `P3`,
  produced together with its witnessing equation `pathSum P3 + D = pathSum P2`.

The universal witness construction (`witness`) uses two distinct child letters `l0`, `l1` and
the addresses `0^m`, `1^n`, `0·1^(k-1)` (with the predecessor of `k` given explicitly).
-/

open TreeN (PathLT PathLE zero_lt_succ succ diff add_diff diff_add diff_pos lt_add_of_pos)
open TreeZ CSR CRing Word ListOps

/-- Two distinct child letters, supplied constructively. -/
class TwoLetters (α : Type) where
  l0 : α
  l1 : α
  ne : l0 ≠ l1

/-- An ordered triple of pairwise distinct root paths with `pathSum P2 > pathSum P3`. -/
structure TriplePath (α : Type) where
  p1 : Word α
  p2 : Word α
  p3 : Word α
  ne12 : p1 ≠ p2
  ne13 : p1 ≠ p3
  ne23 : p2 ≠ p3
  gt : PathLT (pathSum p3) (pathSum p2)

namespace TriplePath

variable {α : Type}

/-- Numerator `A := [pathSum P1, pathSum P2]`. -/
def numer (t : TriplePath α) : TreeZ := mkZ (pathSum t.p1) (pathSum t.p2)

/-- Denominator: the path-length gap between `P2` and `P3`. -/
def denom (t : TriplePath α) : TreeN := diff (pathSum t.p3) (pathSum t.p2)

/-- The equation witnessing the gap. -/
theorem denom_spec (t : TriplePath α) : pathSum t.p3 + denom t = pathSum t.p2 :=
  add_diff (TreeN.le_of_lt t.gt)

/-- The gap is nonzero (strictly positive). -/
theorem denom_pos (t : TriplePath α) : PathLT TreeN.zero (denom t) := diff_pos t.gt

theorem denom_unique (t : TriplePath α) {D : TreeN} (h : pathSum t.p3 + D = pathSum t.p2) :
    D = denom t := by
  apply TreeN.add_left_cancel (k := pathSum t.p3)
  rw [h, denom_spec]

/-- Primary equivalence of triples: `A·D' = A'·D` in `TreeZ`. -/
def Rel (t t' : TriplePath α) : Prop := numer t * ofN (denom t') = numer t' * ofN (denom t)

/-- The auxiliary fraction data of a triple. -/
def toFrac (t : TriplePath α) : Frac := ⟨numer t, denom t, denom_pos t⟩

theorem rel_iff_eqv (t t' : TriplePath α) : Rel t t' = Frac.Eqv (toFrac t) (toFrac t') := rfl

theorem rel_refl (t : TriplePath α) : Rel t t := rfl

theorem rel_symm {t t' : TriplePath α} (h : Rel t t') : Rel t' t := h.symm

theorem rel_trans {t t' t'' : TriplePath α} (h1 : Rel t t') (h2 : Rel t' t'') : Rel t t'' :=
  Frac.eqv_trans (f := toFrac t) (g := toFrac t') (h := toFrac t'') h1 h2

/-! ## Universal path witnesses -/

theorem rep_succ (a : α) (n : TreeN) : rep a (succ n) = a :: rep a n := rfl

section Witness

variable [TwoLetters α]

open TwoLetters

/-- Witness path lengths, from a raw pair `(p, q)` and a positive denominator `D`:
`k := q + two`, `n := k + D`, `m := p + two + D`; the explicit predecessor of `k` is
`k' := q + one`. -/
def wk' (q : TreeN) : TreeN := q + TreeN.one
def wk (q : TreeN) : TreeN := q + TreeN.two
def wn (q D : TreeN) : TreeN := wk q + D
def wm (p D : TreeN) : TreeN := p + TreeN.two + D

theorem wk_eq (q : TreeN) : wk q = succ (wk' q) := TreeN.add_succ q TreeN.one

theorem wk'_eq (q : TreeN) : wk' q = succ q := TreeN.add_one q

theorem wn_eq (q D : TreeN) : wn q D = succ (wk' q + D) := by
  unfold wn
  rw [wk_eq]
  rfl

theorem wm_eq (p D : TreeN) : wm p D = succ (succ (p + D)) := by
  unfold wm
  rw [TreeN.add_succ, TreeN.add_one, TreeN.succ_add, TreeN.succ_add]

/-- The three addresses `0^m`, `1^n`, `0·1^(k-1)`. -/
def wP1 (p D : TreeN) : Word α := rep l0 (wm p D)
def wP2 (q D : TreeN) : Word α := rep l1 (wn q D)
def wP3 (q : TreeN) : Word α := l0 :: rep l1 (wk' q)

theorem wP1_eq (p D : TreeN) : wP1 (α := α) p D = l0 :: l0 :: rep l0 (p + D) := by
  unfold wP1
  rw [wm_eq]
  rfl

theorem wP2_eq (q D : TreeN) : wP2 (α := α) q D = l1 :: rep l1 (wk' q + D) := by
  unfold wP2
  rw [wn_eq]
  rfl

theorem wP3_eq (q : TreeN) : wP3 (α := α) q = l0 :: l1 :: rep l1 q := by
  unfold wP3
  rw [wk'_eq]
  rfl

theorem pathSum_wP1 (p D : TreeN) : pathSum (wP1 (α := α) p D) = wm p D := pathSum_rep _ _
theorem pathSum_wP2 (q D : TreeN) : pathSum (wP2 (α := α) q D) = wn q D := pathSum_rep _ _
theorem pathSum_wP3 (q : TreeN) : pathSum (wP3 (α := α) q) = wk q := by
  unfold wP3
  rw [pathSum_cons, pathSum_rep, wk_eq]

theorem w_ne12 (p q D : TreeN) : wP1 (α := α) p D ≠ wP2 q D := by
  rw [wP1_eq, wP2_eq]
  intro h
  injection h with h1 _
  exact ne h1

theorem w_ne13 (p q D : TreeN) : wP1 (α := α) p D ≠ wP3 q := by
  rw [wP1_eq, wP3_eq]
  intro h
  injection h with _ h2
  injection h2 with h3 _
  exact ne h3

theorem w_ne23 (q D : TreeN) : wP2 (α := α) q D ≠ wP3 q := by
  rw [wP2_eq, wP3_eq]
  intro h
  injection h with h1 _
  exact ne h1.symm

theorem w_gt (q D : TreeN) (hD : PathLT TreeN.zero D) :
    PathLT (pathSum (wP3 (α := α) q)) (pathSum (wP2 (α := α) q D)) := by
  rw [pathSum_wP3, pathSum_wP2]
  exact lt_add_of_pos hD

/-- The universal triple-path witness for the raw pair `(p, q)` and positive `D`. -/
def witness (p q D : TreeN) (hD : PathLT TreeN.zero D) : TriplePath α :=
  ⟨wP1 p D, wP2 q D, wP3 q, w_ne12 p q D, w_ne13 p q D, w_ne23 q D, w_gt q D hD⟩

/-- `m − n` represents the class `(p, q)`. -/
theorem witness_numer (p q D : TreeN) (hD : PathLT TreeN.zero D) :
    numer (witness (α := α) p q D hD) = mkZ p q := by
  unfold numer witness
  show mkZ (pathSum (wP1 (α := α) p D)) (pathSum (wP2 (α := α) q D)) = mkZ p q
  rw [pathSum_wP1, pathSum_wP2]
  apply mkZ_sound
  show p + TreeN.two + D + q = p + (q + TreeN.two + D)
  rw [TreeN.add_assoc, TreeN.add_assoc, TreeN.add_comm D q, ← TreeN.add_assoc TreeN.two q D,
    TreeN.add_comm TreeN.two q]

/-- `n − k = D`. -/
theorem witness_denom (p q D : TreeN) (hD : PathLT TreeN.zero D) :
    denom (witness (α := α) p q D hD) = D := by
  apply Eq.symm
  apply denom_unique
  show pathSum (wP3 (α := α) q) + D = pathSum (wP2 (α := α) q D)
  rw [pathSum_wP3, pathSum_wP2]
  rfl

/-- The triple-path witness of a fraction datum. -/
def ofFrac (f : Frac) : TriplePath α := witness f.num.pos f.num.neg f.den f.pos

theorem toFrac_ofFrac (f : Frac) : toFrac (ofFrac (α := α) f) = f := by
  apply Frac.ext
  · show numer (witness (α := α) f.num.pos f.num.neg f.den f.pos) = f.num
    rw [witness_numer, mkZ_self]
  · exact witness_denom _ _ _ _

/-- **Universal witnesses**: every numerator `A : TreeZ` and every strictly positive
`D : TreeN` are realized by a valid triple-path configuration. -/
theorem universal_witness (A : TreeZ) (D : TreeN) (hD : PathLT TreeN.zero D) :
    ∃ t : TriplePath α, numer t = A ∧ denom t = D :=
  ⟨witness A.pos A.neg D hD, by rw [witness_numer, mkZ_self], witness_denom _ _ _ _⟩

end Witness

end TriplePath

/-! ## Two letters for finite arity `b ≥ 2` and for omega branching -/

/-- The arity `b` has at least two children. -/
class AtLeastTwo (b : TreeN) : Prop where
  lt : PathLT TreeN.one b

instance (b : TreeN) [h : AtLeastTwo b] : TwoLetters (Child b) where
  l0 := Child.first (TreeN.lt_trans (TreeN.zero_lt_succ TreeN.zero) h.lt)
  l1 := Child.second h.lt
  ne := Child.first_ne_second _ _

instance (b : TreeN) : AtLeastTwo (succ (succ b)) where
  lt := TreeN.PathLT.succ_lt _ _ (TreeN.zero_lt_succ b)

/-- The child alphabet of the countably branching tree. -/
abbrev ChildOmega : Type := TreeN

instance : TwoLetters ChildOmega where
  l0 := TreeN.zero
  l1 := TreeN.one
  ne := fun h => nomatch h

end
