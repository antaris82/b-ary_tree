module

public import TreeAnalysis.CauchyOps

@[expose] public section

/-!
# Checkpoints B4, B5, C — the completion `TreeR` and its ring structure

`TreeR K := Quot CRel` is the kernel quotient of rational Cauchy data `CSeq K` (sequences of
elements of `K`, with explicit moduli) by Cauchy equivalence.  For `K = Q★ = TreeQOmega`, the
sequence entries are classes of valid triple-path configurations.

* `mkR_sound`, `mkR_exact`: `mkR s = mkR t` iff `SeqEquiv s t` (exactness uses `propext`,
  which is reported in the axiom audit; it is not a classical principle);
* the operations are lifted from `constSeq`, `addSeq`, `negSeq`, `mulSeq` with the
  compatibility proofs of `CauchyOps`;
* `TreeR K` populates the commutative-ring interface `CRing`, with `0 ≠ 1`;
* `ofQ : K → TreeR K` (constant sequences) preserves `0, 1, +, -, ·` and is injective.

No representative of a quotient element is ever selected: all statements about arbitrary
elements are proved by quotient induction.
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TOField

open TField

variable {K : Type} [TOField K]

/-- Cauchy equivalence of Cauchy data. -/
def CRel (a b : CSeq K) : Prop := SeqEquiv a.seq b.seq

end TOField

open TOField

/-- **The completion**: classes of rational Cauchy data under Cauchy equivalence. -/
def TreeR (K : Type) [TOField K] : Type := Quot (CRel (K := K))

namespace TreeR

open TField

variable {K : Type} [TOField K]

/-- The class of Cauchy data. -/
def mkR (c : CSeq K) : TreeR K := Quot.mk _ c

theorem mkR_sound {a b : CSeq K} (h : SeqEquiv a.seq b.seq) : mkR a = mkR b := Quot.sound h

theorem ind_mkR {motive : TreeR K → Prop} (h : ∀ c, motive (mkR c)) (x : TreeR K) : motive x :=
  Quot.ind h x

/-- "Is equivalent to `a`", lifted to classes (uses `propext`). -/
def relTo (a : CSeq K) : TreeR K → Prop :=
  Quot.lift (fun c => SeqEquiv a.seq c.seq) (fun _ _ h =>
    propext ⟨fun h1 => seqEquiv_trans h1 h, fun h1 => seqEquiv_trans h1 (seqEquiv_symm h)⟩)

/-- **Exactness**: equal classes have Cauchy-equivalent representatives. -/
theorem mkR_exact {a b : CSeq K} (h : mkR a = mkR b) : SeqEquiv a.seq b.seq := by
  have e : relTo a (mkR a) = relTo a (mkR b) := by rw [h]
  have h1 : relTo a (mkR a) := seqEquiv_refl a.seq
  rw [e] at h1
  exact h1

theorem mkR_eq_iff (a b : CSeq K) :
    (mkR a = mkR b → SeqEquiv a.seq b.seq) ∧ (SeqEquiv a.seq b.seq → mkR a = mkR b) :=
  ⟨mkR_exact, mkR_sound⟩

/-- Every element is the class of some Cauchy data (as a proposition; no selection). -/
theorem exists_rep (x : TreeR K) : ∃ c : CSeq K, mkR c = x := by
  induction x using ind_mkR with
  | h c => exact ⟨c, rfl⟩

/-! ## Lifting operations -/

def lift1 (g : CSeq K → CSeq K) (hg : ∀ a b, SeqEquiv a.seq b.seq → SeqEquiv (g a).seq (g b).seq) :
    TreeR K → TreeR K :=
  Quot.lift (fun c => mkR (g c)) (fun a b h => mkR_sound (hg a b h))

def lift2 (g : CSeq K → CSeq K → CSeq K)
    (hg : ∀ a a' b b', SeqEquiv a.seq a'.seq → SeqEquiv b.seq b'.seq →
      SeqEquiv (g a b).seq (g a' b').seq) : TreeR K → TreeR K → TreeR K :=
  Quot.lift (fun a => Quot.lift (fun b => mkR (g a b))
      (fun b b' h => mkR_sound (hg a a b b' (seqEquiv_refl _) h)))
    (fun a a' h => funext (fun y => by
      induction y using ind_mkR with
      | h b => exact mkR_sound (hg a a' b b h (seqEquiv_refl _))))

/-- Embedding of rationals as constant sequences. -/
def ofQ (q : K) : TreeR K := mkR (constSeq q)

def zeroR : TreeR K := ofQ 𝟘
def oneR : TreeR K := ofQ 𝟙

def addR : TreeR K → TreeR K → TreeR K :=
  lift2 addSeq (fun _ _ _ _ h1 h2 => add_resp h1 h2)
def negR : TreeR K → TreeR K := lift1 negSeq (fun _ _ h => neg_resp h)
def mulR : TreeR K → TreeR K → TreeR K :=
  lift2 mulSeq (fun _ _ _ _ h1 h2 => mulSeq_resp h1 h2)

instance : Add (TreeR K) := ⟨addR⟩
instance : Neg (TreeR K) := ⟨negR⟩
instance : Mul (TreeR K) := ⟨mulR⟩

theorem add_mk (a b : CSeq K) : mkR a + mkR b = mkR (addSeq a b) := rfl
theorem neg_mk (a : CSeq K) : -mkR a = mkR (negSeq a) := rfl
theorem mul_mk (a b : CSeq K) : mkR a * mkR b = mkR (mulSeq a b) := rfl

/-! ## Commutative-ring laws -/

theorem add_comm' (x y : TreeR K) : x + y = y + x := by
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => add_comm (a.seq n) (b.seq n)))

theorem add_assoc' (x y z : TreeR K) : x + y + z = x + (y + z) := by
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  induction z using ind_mkR with | h c => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => add_assoc (a.seq n) (b.seq n) (c.seq n)))

theorem zero_add' (x : TreeR K) : zeroR + x = x := by
  induction x using ind_mkR with | h a => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => zero_add (a.seq n)))

theorem neg_add_cancel' (x : TreeR K) : -x + x = zeroR := by
  induction x using ind_mkR with | h a => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => neg_add_cancel (a.seq n)))

theorem mul_comm' (x y : TreeR K) : x * y = y * x := by
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => mul_comm (a.seq n) (b.seq n)))

theorem mul_assoc' (x y z : TreeR K) : x * y * z = x * (y * z) := by
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  induction z using ind_mkR with | h c => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => mul_assoc (a.seq n) (b.seq n) (c.seq n)))

theorem one_mul' (x : TreeR K) : oneR * x = x := by
  induction x using ind_mkR with | h a => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => one_mul (a.seq n)))

theorem zero_mul' (x : TreeR K) : zeroR * x = zeroR := by
  induction x using ind_mkR with | h a => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => zero_mul (a.seq n)))

theorem left_distrib' (x y z : TreeR K) : x * (y + z) = x * y + x * z := by
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  induction z using ind_mkR with | h c => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => left_distrib (a.seq n) (b.seq n) (c.seq n)))

/-- **`TreeR K` is a commutative ring.** -/
instance instCRing : CRing (TreeR K) where
  zero := zeroR
  one := oneR
  add_assoc := add_assoc'
  add_comm := add_comm'
  zero_add := zero_add'
  mul_assoc := mul_assoc'
  mul_comm := mul_comm'
  one_mul := one_mul'
  zero_mul := zero_mul'
  left_distrib := left_distrib'
  neg_add_cancel := neg_add_cancel'

theorem zero_def : (𝟘 : TreeR K) = ofQ 𝟘 := rfl
theorem one_def : (𝟙 : TreeR K) = ofQ 𝟙 := rfl

/-! ## The rational embedding -/

theorem ofQ_add (p q : K) : ofQ (p + q) = ofQ p + ofQ q := mkR_sound (seqEquiv_refl _)
theorem ofQ_neg (p : K) : ofQ (-p) = -ofQ p := mkR_sound (seqEquiv_refl _)
theorem ofQ_mul (p q : K) : ofQ (p * q) = ofQ p * ofQ q := mkR_sound (seqEquiv_refl _)
theorem ofQ_zero : ofQ (𝟘 : K) = 𝟘 := rfl
theorem ofQ_one : ofQ (𝟙 : K) = 𝟙 := rfl

/-- If `|a| ≤ eps k` for every `k`, then `a = 0`. -/
theorem eq_zero_of_abs_le_eps {a : K} (h : ∀ k, abs a ≤ eps k) : a = 𝟘 := by
  apply eq_zero_of_abs_eq_zero
  apply le_antisymm _ (abs_nonneg a)
  apply le_of_forall_le_add_eps
  intro k
  rw [zero_add]
  exact h k

/-- **Injectivity of the rational embedding.** -/
theorem ofQ_injective {p q : K} (h : ofQ p = ofQ q) : p = q := by
  have h' := mkR_exact h
  apply eq_of_add_neg_eq_zero
  apply eq_zero_of_abs_le_eps
  intro k
  obtain ⟨N, hN⟩ := h' k
  exact hN N (TreeN.le_refl N)

/-- `0 ≠ 1` in the completion. -/
theorem zero_ne_one : (𝟘 : TreeR K) ≠ 𝟙 := fun h => TField.zero_ne_one (ofQ_injective h)

/-- Image of a path count in the completion. -/
def natR (n : TreeN) : TreeR K := ofQ (natCast n)

theorem natR_injective {m n : TreeN} (h : natR (K := K) m = natR n) : m = n :=
  natCast_injective (ofQ_injective h)

theorem natR_add (m n : TreeN) : natR (K := K) (m + n) = natR m + natR n := by
  unfold natR
  rw [natCast_add, ofQ_add]

theorem natR_mul (m n : TreeN) : natR (K := K) (m * n) = natR m * natR n := by
  unfold natR
  rw [natCast_mul, ofQ_mul]

theorem natR_one : natR (K := K) TreeN.one = 𝟙 := by
  unfold natR
  rw [natCast_one]
  rfl

end TreeR
end
