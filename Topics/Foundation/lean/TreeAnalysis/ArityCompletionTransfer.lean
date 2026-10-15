module

public import TreeAnalysis.CompletenessScope
public import TreeAnalysis.RationalOrder

@[expose] public section

/-!
# Checkpoint E — independence of the arity

An *ordered-field homomorphism* `φ : K → L` (field operations, inverse, and nonnegativity are
preserved) preserves the derived order, absolute value, the precisions `eps n`, hence rational
Cauchy data and Cauchy equivalence.  It therefore induces `mapR φ : TreeR K → TreeR L`,
compatible with the rational embedding, the ring operations and the strict order.

The Task 01 comparison maps `TreeQ.transfer α β` between the triple-path rational fields of any
two alphabets with two distinct letters preserve the derived order, so they lift to mutually
inverse maps between the completions:

* `realArityIso α β : RealIso (TreeR (TreeQ α)) (TreeR (TreeQ β))`;
* in particular `TreeR_b ≃ TreeR_c` for finite `b, c ≥ 2` and `TreeR_b ≃ TreeR_omega`.

So the one-dimensional ordered completion does not depend on the arity.
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TOField

open TField

/-- Ordered-field homomorphism. -/
structure OFieldHom (K L : Type) [TOField K] [TOField L] where
  toFun : K → L
  map_zero : toFun 𝟘 = 𝟘
  map_one : toFun 𝟙 = 𝟙
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  map_neg : ∀ x, toFun (-x) = -toFun x
  map_inv : ∀ x, toFun (inv x) = inv (toFun x)
  map_nonneg : ∀ x, Nonneg x → Nonneg (toFun x)

namespace OFieldHom

variable {K L : Type} [TOField K] [TOField L] (φ : OFieldHom K L)

theorem map_sub (x y : K) : φ.toFun (x + -y) = φ.toFun x + -φ.toFun y := by
  rw [φ.map_add, φ.map_neg]

theorem map_natCast (n : TreeN) : φ.toFun (natCast n) = natCast n := by
  induction n with
  | nil => exact φ.map_zero
  | cons c n ih =>
    rw [natCast_cons, natCast_cons, φ.map_add, φ.map_one, ih]

theorem map_eps (n : TreeN) : φ.toFun (eps n) = eps n := by
  unfold eps
  rw [φ.map_inv, map_natCast]

theorem map_le {x y : K} (h : x ≤ y) : φ.toFun x ≤ φ.toFun y := by
  show Nonneg (φ.toFun y + -φ.toFun x)
  rw [← map_sub]
  exact φ.map_nonneg _ h

theorem map_abs (x : K) : φ.toFun (abs x) = abs (φ.toFun x) := by
  cases nonneg_total x with
  | inl h => rw [abs_of_nonneg h, abs_of_nonneg (φ.map_nonneg _ h)]
  | inr h =>
    have h' : Nonneg (-φ.toFun x) := by rw [← φ.map_neg]; exact φ.map_nonneg _ h
    rw [abs_of_nonpos h, abs_of_nonpos h', φ.map_neg]

theorem map_abs_sub_le {a b e : K} (h : abs (a + -b) ≤ e) :
    abs (φ.toFun a + -φ.toFun b) ≤ φ.toFun e := by
  rw [← map_sub, ← map_abs]
  exact φ.map_le h

/-- Image of rational Cauchy data (same modulus). -/
def mapSeq (c : CSeq K) : CSeq L :=
  ⟨fun n => φ.toFun (c.seq n), c.mod, fun k m n hm hn => by
    have h := φ.map_abs_sub_le (c.isMod k m n hm hn)
    rw [map_eps] at h
    exact h⟩

theorem mapSeq_resp {c d : CSeq K} (h : SeqEquiv c.seq d.seq) :
    SeqEquiv (φ.mapSeq c).seq (φ.mapSeq d).seq := fun k => by
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  have h2 := φ.map_abs_sub_le (hN n hn)
  rw [map_eps] at h2
  exact h2

/-- Composition of ordered-field homomorphisms. -/
def comp {M : Type} [TOField M] (ψ : OFieldHom L M) : OFieldHom K M where
  toFun := fun x => ψ.toFun (φ.toFun x)
  map_zero := by rw [φ.map_zero, ψ.map_zero]
  map_one := by rw [φ.map_one, ψ.map_one]
  map_add := fun x y => by rw [φ.map_add, ψ.map_add]
  map_mul := fun x y => by rw [φ.map_mul, ψ.map_mul]
  map_neg := fun x => by rw [φ.map_neg, ψ.map_neg]
  map_inv := fun x => by rw [φ.map_inv, ψ.map_inv]
  map_nonneg := fun x h => ψ.map_nonneg _ (φ.map_nonneg _ h)

end OFieldHom

end TOField

namespace TreeR

open TField TOField

variable {K L : Type} [TOField K] [TOField L]

/-- The map of completions induced by an ordered-field homomorphism. -/
def mapR (φ : OFieldHom K L) : TreeR K → TreeR L :=
  Quot.lift (fun c => mkR (φ.mapSeq c)) (fun _ _ h => mkR_sound (φ.mapSeq_resp h))

variable (φ : OFieldHom K L)

theorem mapR_mk (c : CSeq K) : mapR φ (mkR c) = mkR (φ.mapSeq c) := rfl

theorem mapR_ofQ (q : K) : mapR φ (ofQ q) = ofQ (φ.toFun q) := rfl

theorem mapR_add (x y : TreeR K) : mapR φ (x + y) = mapR φ x + mapR φ y := by
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => φ.map_add (a.seq n) (b.seq n)))

theorem mapR_mul (x y : TreeR K) : mapR φ (x * y) = mapR φ x * mapR φ y := by
  induction x using ind_mkR with | h a => ?_
  induction y using ind_mkR with | h b => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => φ.map_mul (a.seq n) (b.seq n)))

theorem mapR_neg (x : TreeR K) : mapR φ (-x) = -mapR φ x := by
  induction x using ind_mkR with | h a => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => φ.map_neg (a.seq n)))

theorem mapR_zero : mapR φ (𝟘 : TreeR K) = 𝟘 := by
  show ofQ (φ.toFun 𝟘) = ofQ 𝟘
  rw [φ.map_zero]

theorem mapR_one : mapR φ (𝟙 : TreeR K) = 𝟙 := by
  show ofQ (φ.toFun 𝟙) = ofQ 𝟙
  rw [φ.map_one]

theorem mapR_rpos {x : TreeR K} (h : RPos x) : RPos (mapR φ x) := by
  obtain ⟨c, e, k, N, hN⟩ := h
  rw [← e]
  refine rpos_mk (c := φ.mapSeq c) ⟨k, N, fun n hn => ?_⟩
  have h2 := φ.map_le (hN n hn)
  rw [OFieldHom.map_eps] at h2
  exact h2

theorem mapR_lt {x y : TreeR K} (h : x < y) : mapR φ x < mapR φ y := by
  show RPos (mapR φ y + -mapR φ x)
  rw [← mapR_neg, ← mapR_add]
  exact mapR_rpos φ h

theorem mapR_comp {M : Type} [TOField M] (ψ : OFieldHom L M) (x : TreeR K) :
    mapR ψ (mapR φ x) = mapR (φ.comp ψ) x := by
  induction x using ind_mkR with | h a => ?_
  rfl

theorem mapR_id_of {ψ : OFieldHom K K} (h : ∀ q, ψ.toFun q = q) (x : TreeR K) : mapR ψ x = x := by
  induction x using ind_mkR with | h a => ?_
  exact mkR_sound (seqEquiv_of_eq (fun n => h (a.seq n)))

end TreeR

/-- Isomorphism of completed ordered rings (ring operations, rational-free order). -/
structure RealIso (A B : Type) [CRing A] [CRing B] [LT A] [LT B] where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_zero : toFun 𝟘 = 𝟘
  map_one : toFun 𝟙 = 𝟙
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  map_neg : ∀ x, toFun (-x) = -toFun x
  map_lt : ∀ x y, x < y → toFun x < toFun y
  inv_map_lt : ∀ x y, x < y → invFun x < invFun y

namespace TreeQ

open TOField TField

variable {α β : Type} [TwoLetters α] [TwoLetters β]

theorem transfer_nonneg (x : TreeQ α) (h : Nonneg x) : Nonneg (transfer α β x) := by
  revert h
  induction x using ind_ofF with | h f => ?_
  intro h
  show NonnegQ (transfer α β (ofF f))
  rw [transfer_ofF]
  exact nonnegQ_ofF (nonNegF_of_nonnegQ h)

/-- The Task 01 comparison map is an ordered-field homomorphism. -/
def transferHom (α β : Type) [TwoLetters α] [TwoLetters β] : OFieldHom (TreeQ α) (TreeQ β) where
  toFun := transfer α β
  map_zero := transfer_zero
  map_one := transfer_one
  map_add := transfer_add
  map_mul := transfer_mul
  map_neg := transfer_neg
  map_inv := transfer_inv
  map_nonneg := transfer_nonneg

/-- The comparison maps preserve the derived order. -/
theorem transfer_le {x y : TreeQ α} (h : x ≤ y) : transfer α β x ≤ transfer α β y :=
  (transferHom α β).map_le h

/-- The comparison maps preserve the absolute value. -/
theorem transfer_abs (x : TreeQ α) : transfer α β (abs x) = abs (transfer α β x) :=
  (transferHom α β).map_abs x

/-- The comparison maps preserve the precisions. -/
theorem transfer_eps (n : TreeN) : transfer α β (eps n) = eps n := (transferHom α β).map_eps n

end TreeQ

open TreeR TreeQ

/-- **Arity independence of the completion.** -/
def realArityIso (α β : Type) [TwoLetters α] [TwoLetters β] :
    RealIso (TreeR (TreeQ α)) (TreeR (TreeQ β)) where
  toFun := mapR (transferHom α β)
  invFun := mapR (transferHom β α)
  left_inv := fun x => by
    rw [mapR_comp]
    exact mapR_id_of (fun q => transfer_transfer q) x
  right_inv := fun y => by
    rw [mapR_comp]
    exact mapR_id_of (fun q => transfer_transfer q) y
  map_zero := mapR_zero _
  map_one := mapR_one _
  map_add := mapR_add _
  map_mul := mapR_mul _
  map_neg := mapR_neg _
  map_lt := fun _ _ h => mapR_lt _ h
  inv_map_lt := fun _ _ h => mapR_lt _ h

/-- The completions of finite arities `b, c ≥ 2`. -/
def finiteRealIso (b c : TreeN) [AtLeastTwo b] [AtLeastTwo c] :
    RealIso (TreeR (TreeQb b)) (TreeR (TreeQb c)) :=
  realArityIso (Child b) (Child c)

/-- Finite arity `b ≥ 2` versus omega branching. -/
def finiteOmegaRealIso (b : TreeN) [AtLeastTwo b] :
    RealIso (TreeR (TreeQb b)) (TreeR TreeQOmega) :=
  realArityIso (Child b) ChildOmega

/-- The isomorphism extends the rational comparison map. -/
theorem realArityIso_ofQ (α β : Type) [TwoLetters α] [TwoLetters β] (q : TreeQ α) :
    (realArityIso α β).toFun (ofQ q) = ofQ (transfer α β q) := rfl

end
