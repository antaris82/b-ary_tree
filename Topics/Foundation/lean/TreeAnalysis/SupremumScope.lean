module

public import TreeAnalysis.LiftingPrinciples
public import TreeAnalysis.ApartnessStrength

@[expose] public section

/-!
# Task 03, Checkpoint D — suprema and the limits of order completeness

Three separately named notions:
* **approximated supremum** — `SupData.sup` with `le_sup` and `sup_approx` (Task 02);
* **genuine least upper bound under `SupData`** — `SupData.isLUB` (this file): `D.sup` is an
  upper bound and lies below every upper bound; least upper bounds are unique (`lub_unique`);
* **unrestricted least upper bound** — `UnrestrictedLUB K` (a named proposition, **not** proved).
  We prove that it implies the weak limited principle of omniscience `WLPO`
  (`wlpo_of_unrestrictedLUB`).  Similarly, ordinary bounded monotone convergence
  `BoundedMonotoneConvergence K` (not proved) implies `LPO` (`lpo_of_bmc`).

Constructive supply of `SupData` (D2):
* `SupData.singleton c` for the class of explicit Cauchy data;
* `SupData.union D E` for the union of two sets with `SupData` (decided by rational comparison);
* `SupData.ofList c l` for every nonempty finite list of explicit Cauchy data;
* `SupData.ofMonotone` for monotone real sequences with a Cauchy modulus and approximation data.

Monotone sequences: `lub_of_monotone_converges` (the limit of a monotone convergent sequence is
the least upper bound of its range), with unconditional instances for tracked towers and
conditional instances under `ChoiceNN`.
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TreeR

open TField TOField

variable {K : Type} [TOField K]

/-- Upper bounds. -/
def IsUpperBound (S : TreeR K → Prop) (y : TreeR K) : Prop := ∀ x, S x → x ≤ y

/-- Least upper bounds. -/
def IsLUB (S : TreeR K → Prop) (y : TreeR K) : Prop :=
  IsUpperBound S y ∧ ∀ z, IsUpperBound S z → y ≤ z

/-- Least upper bounds are unique. -/
theorem lub_unique {S : TreeR K → Prop} {y y' : TreeR K} (h : IsLUB S y) (h' : IsLUB S y') :
    y = y' :=
  le_antisymm (h.2 y' h'.1) (h'.2 y h.1)

/-! ## D1: `SupData.sup` is the least upper bound -/

namespace SupData

variable {S : TreeR K → Prop} (D : SupData S)

/-- `D.sup` lies below every upper bound. -/
theorem sup_least {y : TreeR K} (hy : IsUpperBound S y) : D.sup ≤ y := by
  apply le_of_forall_le_add_eps
  intro k
  exact le_trans (D.sup_approx k) (add_le_add_right _ (hy _ (D.mem _)))

/-- **D1: `D.sup` is the least upper bound of `S`.** -/
theorem isLUB : IsLUB S D.sup := ⟨fun _ hx => D.le_sup hx, fun _ hy => D.sup_least hy⟩

/-- Any least upper bound of a set with `SupData` equals `D.sup`. -/
theorem eq_sup_of_isLUB {y : TreeR K} (h : IsLUB S y) : y = D.sup := lub_unique h D.isLUB

/-- Two `SupData` for the same set give the same supremum. -/
theorem sup_eq (E : SupData S) : D.sup = E.sup := lub_unique D.isLUB E.isLUB

end SupData

/-! ## D2: constructive supply of `SupData` -/

/-- Selection by a decidable proposition. -/
def ifD {p : Prop} {β : Type} : Decidable p → β → β → β
  | isTrue _, a, _ => a
  | isFalse _, _, b => b

theorem ifD_pos {p : Prop} {β : Type} {a b : β} (h : p) : ∀ d : Decidable p, ifD d a b = a
  | isTrue _ => rfl
  | isFalse h' => absurd h h'

theorem ifD_neg {p : Prop} {β : Type} {a b : β} (h : ¬ p) : ∀ d : Decidable p, ifD d a b = b
  | isTrue h' => absurd h' h
  | isFalse _ => rfl

namespace SupData

/-- `SupData` for the singleton of the class of explicit Cauchy data. -/
def singleton (c : CSeq K) : SupData (fun x => x = mkR c) where
  u := fun k => approxAt c (succ k) + eps (succ k)
  s := fun _ => mkR c
  mem := fun _ => rfl
  upper := fun k x hx => by
    rw [hx, ofQ_add]
    exact (approxAt_close c (succ k)).1
  approx := fun k => by
    have h := (approxAt_close c (succ k)).2
    have e : mkR c + ofQ (eps (succ k)) + ofQ (eps (succ k)) = mkR c + ofQ (eps k) := by
      rw [add_assoc, ← ofQ_add, eps_succ_add]
    rw [ofQ_add, ← e]
    exact add_le_add_right _ h

/-- `SupData` for a union, decided by comparing the rational upper approximations. -/
def union {S T : TreeR K → Prop} (D : SupData S) (E : SupData T) :
    SupData (fun x => S x ∨ T x) where
  u := fun k => ifD (decLE (D.u k) (E.u k)) (E.u k) (D.u k)
  s := fun k => ifD (decLE (D.u k) (E.u k)) (E.s k) (D.s k)
  mem := fun k => by
    cases TOField.le_or_lt (D.u k) (E.u k) with
    | inl h =>
      rw [ifD_pos h]
      exact Or.inr (E.mem k)
    | inr h =>
      rw [ifD_neg h]
      exact Or.inl (D.mem k)
  upper := fun k x hx => by
    cases TOField.le_or_lt (D.u k) (E.u k) with
    | inl h =>
      rw [ifD_pos h]
      cases hx with
      | inl hS => exact le_trans (D.upper k x hS) (ofQ_le_ofQ h)
      | inr hT => exact E.upper k x hT
    | inr h =>
      rw [ifD_neg h]
      cases hx with
      | inl hS => exact D.upper k x hS
      | inr hT => exact le_trans (E.upper k x hT) (ofQ_le_ofQ (TOField.le_of_lt h))
  approx := fun k => by
    cases TOField.le_or_lt (D.u k) (E.u k) with
    | inl h =>
      rw [ifD_pos h, ifD_pos h]
      exact E.approx k
    | inr h =>
      rw [ifD_neg h, ifD_neg h]
      exact D.approx k

/-- The set of classes of a nonempty finite list of explicit Cauchy data. -/
def ListSet : CSeq K → List (CSeq K) → TreeR K → Prop
  | c, [] => fun x => x = mkR c
  | c, d :: l => fun x => x = mkR c ∨ ListSet d l x

/-- `SupData` for every nonempty finite list of explicit Cauchy data. -/
def ofList : (c : CSeq K) → (l : List (CSeq K)) → SupData (ListSet c l)
  | c, [] => singleton c
  | c, d :: l => union (singleton c) (ofList d l)

/-- **Finite suprema**: the least upper bound of a nonempty finite list of classes. -/
theorem ofList_isLUB (c : CSeq K) (l : List (CSeq K)) : IsLUB (ListSet c l) (ofList c l).sup :=
  (ofList c l).isLUB

end SupData

/-! ## Monotone sequences -/

/-- Monotone sequences of reals. -/
def Monotone (f : TreeN → TreeR K) : Prop := ∀ i j, PathLE i j → f i ≤ f j

/-- The range of a sequence. -/
def Range (f : TreeN → TreeR K) : TreeR K → Prop := fun x => ∃ i, x = f i

/-- **The limit of a monotone convergent sequence is the least upper bound of its range.** -/
theorem lub_of_monotone_converges {f : TreeN → TreeR K} (hm : Monotone f) {L : TreeR K}
    (hL : ConvergesTo f L) : IsLUB (Range f) L := by
  constructor
  · intro x ⟨i, hi⟩
    rw [hi]
    apply le_of_forall_le_add_eps
    intro k
    obtain ⟨N, hN⟩ := hL k
    exact le_trans (hm i (maxN N i) (TreeN.le_maxN_right _ _)) (hN _ (TreeN.le_maxN_left _ _)).1
  · intro z hz
    apply le_of_forall_le_add_eps
    intro k
    obtain ⟨N, hN⟩ := hL k
    exact le_trans (hN N (TreeN.le_refl N)).2 (add_le_add_right _ (hz _ ⟨N, rfl⟩))

/-- Monotone tracked towers: the range has a least upper bound (unconditional). -/
theorem tower_monotone_lub (T : TrackedCauchyTower K) (hm : Monotone (fun i => mkR (T.r i))) :
    IsLUB (Range (fun i => mkR (T.r i))) T.limit :=
  lub_of_monotone_converges hm T.tower_converges

/-- Under `ChoiceNN`: monotone Cauchy sequences (even without a modulus) have a least upper
bound of their range. -/
theorem monotone_lub_of_choice (hc : ChoiceNN) {f : TreeN → TreeR K} (hm : Monotone f)
    (hf : RCauchy f) : ∃ L, IsLUB (Range f) L := by
  obtain ⟨L, hL⟩ := modulusFreeComplete_of_choice hc f hf
  exact ⟨L, lub_of_monotone_converges hm hL⟩

namespace SupData

/-- The sampling index used for monotone sequences. -/
def monoIdx (ν M : TreeN → TreeN) (k : TreeN) : TreeN := maxN (ν (succ k)) (M (succ (succ k)))

/-- `SupData` for the range of a monotone real sequence with a Cauchy modulus and approximation
data (all inputs explicit). -/
def ofMonotone {f : TreeN → TreeR K} (hm : Monotone f) {ν : TreeN → TreeN}
    (hc : RCauchyMod f ν) {q : TreeN → K} {M : TreeN → TreeN} (hq : ApproxData f q M) :
    SupData (Range f) where
  u := fun k => q (monoIdx ν M k) + eps (succ (succ k)) + eps (succ k)
  s := fun k => f (monoIdx ν M k)
  mem := fun k => ⟨_, rfl⟩
  upper := fun k x hx => by
    obtain ⟨i, hi⟩ := hx
    rw [hi]
    have h1 : f i ≤ f (monoIdx ν M k) + ofQ (eps (succ k)) := by
      cases TreeN.le_or_lt i (monoIdx ν M k) with
      | inl h =>
        apply le_trans (hm i _ h)
        exact (rclose_self (f (monoIdx ν M k)) (eps (succ k)) (eps_nonneg _)).1
      | inr h =>
        exact hc (succ k) i _ (TreeN.le_trans (TreeN.le_maxN_left _ _) (TreeN.le_of_lt h))
          (TreeN.le_maxN_left _ _)
    have h2 := (hq (succ (succ k)) (monoIdx ν M k) (TreeN.le_maxN_right _ _)).1
    have h3 := le_trans h1 (add_le_add_right (ofQ (eps (succ k))) h2)
    rw [ofQ_add, ofQ_add]
    exact h3
  approx := fun k => by
    have h2 := (hq (succ (succ k)) (monoIdx ν M k) (TreeN.le_maxN_right _ _)).2
    have e : f (monoIdx ν M k) + ofQ (eps (succ (succ k))) +
        ofQ (eps (succ (succ k)) + eps (succ k)) = f (monoIdx ν M k) + ofQ (eps k) := by
      rw [add_assoc, ← ofQ_add, ← add_assoc, eps_three]
    rw [add_assoc, ofQ_add, ← e]
    exact add_le_add_right _ h2

end SupData

/-! ## D3: unrestricted order-completeness principles (named, not proved) -/

/-- The unrestricted least-upper-bound property for inhabited, bounded-above predicates. -/
def UnrestrictedLUB (K : Type) [TOField K] : Prop :=
  ∀ S : TreeR K → Prop, (∃ x, S x) → (∃ b, IsUpperBound S b) → ∃ y, IsLUB S y

/-- Ordinary bounded monotone convergence. -/
def BoundedMonotoneConvergence (K : Type) [TOField K] : Prop :=
  ∀ f : TreeN → TreeR K, Monotone f → (∃ b, ∀ i, f i ≤ b) → ∃ L, ConvergesTo f L

/-- The weak limited principle of omniscience for Boolean tests on tree-path counts. -/
def WLPO : Prop := ∀ p : TreeN → Bool, (∀ n, p n = false) ∨ ¬ (∀ n, p n = false)

theorem wlpo_of_lpo (h : LPO) : WLPO := fun p =>
  match h p with
  | Or.inl ⟨n, hn⟩ => Or.inr (fun ha => by rw [ha n] at hn; exact nomatch hn)
  | Or.inr ha => Or.inl ha

theorem zero_lt_ofQ_eps (k : TreeN) : (𝟘 : TreeR K) < ofQ (eps k) := by
  rw [← ofQ_zero]
  exact ofQ_lt_ofQ (eps_pos k)

theorem ofQ_eps_succ_lt (k : TreeN) : ofQ (eps (K := K) (succ k)) < ofQ (eps k) :=
  ofQ_lt_ofQ (eps_succ_lt k)

/-- **The unrestricted least-upper-bound property implies `WLPO`.** -/
theorem wlpo_of_unrestrictedLUB (h : UnrestrictedLUB K) : WLPO := by
  intro p
  let S : TreeR K → Prop := fun x => x = 𝟘 ∨ (x = 𝟙 ∧ ∃ n, p n = true)
  have hbound : IsUpperBound S 𝟙 := fun x hx => by
    cases hx with
    | inl h0 => rw [h0]; exact le_of_lt zero_lt_one
    | inr h1 => rw [h1.1]; exact le_refl _
  obtain ⟨y, hy⟩ := h S ⟨𝟘, Or.inl rfl⟩ ⟨𝟙, hbound⟩
  cases lt_cotrans y (ofQ_eps_succ_lt (K := K) (succ TreeN.zero)) with
  | inl hlow =>
    apply Or.inr
    intro hall
    have h0 : IsUpperBound S 𝟘 := fun x hx => by
      cases hx with
      | inl h0 => rw [h0]; exact le_refl _
      | inr h1 =>
        obtain ⟨n, hn⟩ := h1.2
        rw [hall n] at hn
        exact nomatch hn
    have hy0 := hy.2 𝟘 h0
    exact lt_irrefl _ (lt_trans (zero_lt_ofQ_eps _) (lt_of_lt_of_le hlow hy0))
  | inr hhigh =>
    apply Or.inl
    intro n
    apply bool_false_of_ne_true
    intro hn
    have h1 : (𝟙 : TreeR K) ≤ y := hy.1 𝟙 (Or.inr ⟨rfl, n, hn⟩)
    have h2 := lt_of_le_of_lt h1 hhigh
    rw [← ofQ_one] at h2
    exact TOField.not_lt_of_le (eps_le_one (K := K) (succ TreeN.zero)) (lt_of_ofQ_lt h2)

theorem findFirst_le_self (p : TreeN → Bool) : ∀ n : TreeN, PathLE (TreeQ.findFirst p n) n
  | [] => TreeN.le_refl _
  | c :: n => by
    show PathLE (cond (p (TreeQ.findFirst p n)) (TreeQ.findFirst p n) (c :: n)) (c :: n)
    cases p (TreeQ.findFirst p n) with
    | true => exact TreeN.le_trans (findFirst_le_self p n) (TreeN.le_of_lt (TreeN.lt_cons_self c n))
    | false => exact TreeN.le_refl _

/-- The `{0,1}`-valued indicator of "a success of `p` has been found by stage `n`". -/
def foundInd (p : TreeN → Bool) (n : TreeN) : K := cond (p (TreeQ.findFirst p n)) 𝟙 𝟘

theorem foundInd_mono (p : TreeN → Bool) {i j : TreeN} (h : PathLE i j) :
    foundInd (K := K) p i ≤ foundInd p j := by
  unfold foundInd
  cases hi : p (TreeQ.findFirst p i) with
  | true =>
    rw [found_of_true hi (TreeN.le_trans (findFirst_le_self p i) h)]
    exact TOField.le_refl _
  | false =>
    cases p (TreeQ.findFirst p j) with
    | true => exact TOField.zero_le_one
    | false => exact TOField.le_refl _

/-- **Bounded monotone convergence implies `LPO`.** -/
theorem lpo_of_bmc (h : BoundedMonotoneConvergence K) : LPO := by
  intro p
  let f : TreeN → TreeR K := fun n => ofQ (foundInd p n)
  have hm : Monotone f := fun i j hij => ofQ_le_ofQ (foundInd_mono p hij)
  have hb : ∀ i, f i ≤ 𝟙 := fun i => by
    show ofQ (foundInd p i) ≤ ofQ 𝟙
    apply ofQ_le_ofQ
    unfold foundInd
    cases p (TreeQ.findFirst p i) with
    | true => exact TOField.le_refl _
    | false => exact TOField.zero_le_one
  obtain ⟨L, hL⟩ := h f hm ⟨𝟙, hb⟩
  let e1 : K := eps (succ TreeN.zero)
  let e2 : K := eps (succ (succ TreeN.zero))
  cases lt_cotrans L (ofQ_eps_succ_lt (K := K) (succ TreeN.zero)) with
  | inl hlow =>
    apply Or.inl
    obtain ⟨N, hN⟩ := hL (succ (succ (succ TreeN.zero)))
    have h1 : L ≤ f N + ofQ (eps (succ (succ (succ TreeN.zero)))) := (hN N (TreeN.le_refl N)).2
    cases hq : p (TreeQ.findFirst p N) with
    | true => exact ⟨_, hq⟩
    | false =>
      apply False.elim
      have hf : f N = 𝟘 := by
        show ofQ (foundInd p N) = ofQ 𝟘
        unfold foundInd
        rw [hq]
        rfl
      rw [hf, zero_add] at h1
      exact lt_irrefl _ (lt_trans (lt_of_lt_of_le hlow h1) (ofQ_eps_succ_lt _))
  | inr hhigh =>
    apply Or.inr
    intro n
    apply bool_false_of_ne_true
    intro hn
    obtain ⟨N, hN⟩ := hL (succ (succ TreeN.zero))
    let m := maxN N n
    have h1 : f m ≤ L + ofQ e2 := (hN m (TreeN.le_maxN_left _ _)).1
    have hf : f m = 𝟙 := by
      show ofQ (foundInd p m) = ofQ 𝟙
      unfold foundInd
      rw [found_of_true hn (TreeN.le_maxN_right N n)]
      rfl
    rw [hf] at h1
    have h2 := lt_of_le_of_lt h1 (add_lt_add_right (ofQ e2) hhigh)
    rw [← ofQ_add, ← ofQ_one] at h2
    have h3 := lt_of_ofQ_lt h2
    have h4 : e1 + e2 ≤ (𝟙 : K) := by
      have := TOField.add_le_add_left e1 (eps_succ_le (K := K) (succ TreeN.zero))
      rw [eps_succ_add, eps_zero] at this
      exact this
    exact TOField.not_lt_of_le h4 h3

end TreeR
end
