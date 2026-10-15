module

public import TreeAnalysis.Instances

@[expose] public section

/-!
# Task 03, Checkpoint A — Cauchy notions and the exact limiting step

* `RClose x y e` : the two-sided real estimate `x ≤ y + e ∧ y ≤ x + e` (for rational `e`).
* `rcauchyMod_close`, `rcauchy_of_rcauchyMod`, `rcauchyMod_iff_close`: the one-sided real Cauchy
  inequality yields the two-sided one by exchanging indices.
* `mkR_close_seq`: explicit (not merely existential) rational approximation of a class by the
  terms of any representative beyond its own modulus.
* `regular_close`: a *regular* representative approximates its class at **every** index with
  error `eps n`, and two regular representatives of one real satisfy Bishop's pointwise bound
  (`regular_rep_bishop`).  Every real has a regular representative (`exists_regular_rep`, a
  `Prop`-level statement; no selection).
* `limit_of_approx` (**A3, sharpened diagonal**): a real Cauchy sequence with modulus converges as
  soon as *one rational per index* is supplied with an explicit error schedule.  No
  representative of any `f i` is needed.  `TrackedCauchyTower` supplies such rationals
  (`TrackedCauchyTower.approx`), so `tower_limit` is recovered as `tower_limit_via_approx`.
* `close_of_cauchy_of_converges`: a limit of a Cauchy sequence with modulus `ν` is reached with
  the same modulus `ν` (no new data needed).
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TreeR

open TField TOField

variable {K : Type} [TOField K]

/-- Two-sided closeness of reals within a rational tolerance. -/
def RClose (x y : TreeR K) (e : K) : Prop := x ≤ y + ofQ e ∧ y ≤ x + ofQ e

theorem rclose_symm {x y : TreeR K} {e : K} (h : RClose x y e) : RClose y x e := ⟨h.2, h.1⟩

theorem rclose_mono {x y : TreeR K} {e e' : K} (h : RClose x y e) (he : e ≤ e') :
    RClose x y e' :=
  ⟨le_trans h.1 (add_le_add_left y (ofQ_le_ofQ he)),
   le_trans h.2 (add_le_add_left x (ofQ_le_ofQ he))⟩

theorem le_add_add {x y z : TreeR K} {e1 e2 : K} (h1 : x ≤ y + ofQ e1) (h2 : y ≤ z + ofQ e2) :
    x ≤ z + ofQ (e1 + e2) := by
  have h := le_trans h1 (add_le_add_right (ofQ e1) h2)
  rw [add_assoc, ← ofQ_add, add_comm e2 e1] at h
  exact h

theorem rclose_trans {x y z : TreeR K} {e1 e2 : K} (h1 : RClose x y e1) (h2 : RClose y z e2) :
    RClose x z (e1 + e2) := by
  refine ⟨le_add_add h1.1 h2.1, ?_⟩
  have h := le_add_add h2.2 h1.2
  rw [add_comm e2 e1] at h
  exact h

theorem rclose_self (x : TreeR K) (e : K) (he : 𝟘 ≤ e) : RClose x x e := by
  have h : x ≤ x + ofQ e := by
    have h1 := add_le_add_left x (ofQ_le_ofQ he)
    rw [ofQ_zero, add_zero] at h1
    exact h1
  exact ⟨h, h⟩

/-- `ConvergesTo` is pointwise `RClose` (definitional unfolding). -/
theorem convergesTo_iff (f : TreeN → TreeR K) (L : TreeR K) :
    (ConvergesTo f L → ∀ k, ∃ N, ∀ n, PathLE N n → RClose (f n) L (eps k)) ∧
    ((∀ k, ∃ N, ∀ n, PathLE N n → RClose (f n) L (eps k)) → ConvergesTo f L) :=
  ⟨fun h => h, fun h => h⟩

/-! ## A1: the real Cauchy notions -/

/-- The one-sided real Cauchy inequality gives the two-sided one by exchanging indices. -/
theorem rcauchyMod_close {f : TreeN → TreeR K} {ν : TreeN → TreeN} (h : RCauchyMod f ν)
    {k i j : TreeN} (hi : PathLE (ν k) i) (hj : PathLE (ν k) j) : RClose (f i) (f j) (eps k) :=
  ⟨h k i j hi hj, h k j i hj hi⟩

/-- `RCauchyMod` is equivalent to its two-sided form. -/
theorem rcauchyMod_iff_close (f : TreeN → TreeR K) (ν : TreeN → TreeN) :
    (RCauchyMod f ν → ∀ k i j, PathLE (ν k) i → PathLE (ν k) j → RClose (f i) (f j) (eps k)) ∧
    ((∀ k i j, PathLE (ν k) i → PathLE (ν k) j → RClose (f i) (f j) (eps k)) → RCauchyMod f ν) :=
  ⟨fun h _ _ _ hi hj => rcauchyMod_close h hi hj, fun h k i j hi hj => (h k i j hi hj).1⟩

/-- The same for the modulus-free predicate. -/
theorem rcauchy_iff_close (f : TreeN → TreeR K) :
    (RCauchy f → ∀ k, ∃ N, ∀ i j, PathLE N i → PathLE N j → RClose (f i) (f j) (eps k)) ∧
    ((∀ k, ∃ N, ∀ i j, PathLE N i → PathLE N j → RClose (f i) (f j) (eps k)) → RCauchy f) := by
  constructor
  · intro h k
    obtain ⟨N, hN⟩ := h k
    exact ⟨N, fun i j hi hj => ⟨hN i j hi hj, hN j i hj hi⟩⟩
  · intro h k
    obtain ⟨N, hN⟩ := h k
    exact ⟨N, fun i j hi hj => (hN i j hi hj).1⟩

/-- A modulus function yields the `Prop`-level Cauchy predicate. -/
theorem rcauchy_of_rcauchyMod {f : TreeN → TreeR K} {ν : TreeN → TreeN} (h : RCauchyMod f ν) :
    RCauchy f := fun k => ⟨ν k, h k⟩

/-- Convergent sequences are Cauchy (`Prop`-level; the limit carries no modulus function). -/
theorem rcauchy_of_converges {f : TreeN → TreeR K} {L : TreeR K} (h : ConvergesTo f L) :
    RCauchy f := by
  intro k
  obtain ⟨N, hN⟩ := h (succ k)
  refine ⟨N, fun i j hi hj => ?_⟩
  have h1 := le_add_add (hN i hi).1 (hN j hj).2
  rw [eps_succ_add] at h1
  exact h1

/-- A convergence modulus function yields a Cauchy modulus. -/
theorem rcauchyMod_of_converges_mod {f : TreeN → TreeR K} {L : TreeR K} {μ : TreeN → TreeN}
    (h : ∀ k n, PathLE (μ k) n → RClose (f n) L (eps k)) :
    RCauchyMod f (fun k => μ (succ k)) := by
  intro k i j hi hj
  have h1 := le_add_add (h _ i hi).1 (h _ j hj).2
  rw [eps_succ_add] at h1
  exact h1

/-- Rational closeness gives real closeness. -/
theorem rclose_ofQ {p q e : K} (h : abs (p + -q) ≤ e) : RClose (ofQ p) (ofQ q) e := by
  constructor
  · rw [← ofQ_add]
    apply ofQ_le_ofQ
    have h1 := lower_of_abs h
    rw [add_comm] at h1
    exact h1
  · rw [← ofQ_add]
    apply ofQ_le_ofQ
    have h1 := upper_of_abs h
    rw [add_comm] at h1
    exact h1

/-- Real closeness of rationals gives rational closeness. -/
theorem abs_le_of_rclose_ofQ {p q e : K} (h : RClose (ofQ p) (ofQ q) e) : abs (p + -q) ≤ e := by
  have h1 : p ≤ q + e := by
    apply le_of_ofQ_le
    rw [ofQ_add]
    exact h.1
  have h2 : q ≤ p + e := by
    apply le_of_ofQ_le
    rw [ofQ_add]
    exact h.2
  have h2' : q ≤ e + p := by rw [add_comm]; exact h2
  have h1' : p ≤ e + q := by rw [add_comm]; exact h1
  apply abs_le_of
  · have h3 := TOField.neg_le_neg (sub_le_of_le_add h2')
    rw [neg_sub'] at h3
    exact h3
  · exact sub_le_of_le_add h1'

/-- Rational Cauchy notions embed: `IsModulus s μ` gives `RCauchyMod (ofQ ∘ s) μ`. -/
theorem rcauchyMod_ofQ {s : TreeN → K} {μ : TreeN → TreeN} (h : IsModulus s μ) :
    RCauchyMod (fun n => ofQ (s n)) μ :=
  fun k i j hi hj => (rclose_ofQ (h k i j hi hj)).1

/-- Conversely, a real modulus for `ofQ ∘ s` is a rational modulus for `s`. -/
theorem isModulus_of_rcauchyMod_ofQ {s : TreeN → K} {μ : TreeN → TreeN}
    (h : RCauchyMod (fun n => ofQ (s n)) μ) : IsModulus s μ :=
  fun _ _ _ hm hn => abs_le_of_rclose_ofQ (rcauchyMod_close h hm hn)

/-- The same correspondence for the modulus-free predicates. -/
theorem isCauchy_of_rcauchy_ofQ {s : TreeN → K} (h : RCauchy (fun n => ofQ (s n))) :
    IsCauchy s := by
  intro δ hδ
  obtain ⟨N, hN⟩ := h (succ (epsIndex δ))
  refine ⟨N, fun m n hm hn => ?_⟩
  have key : abs (s m + -s n) ≤ eps (succ (epsIndex δ)) :=
    abs_le_of_rclose_ofQ ⟨hN m n hm hn, hN n m hn hm⟩
  exact TOField.lt_of_le_of_lt key
    (TOField.lt_of_le_of_lt (eps_succ_le _) (eps_epsIndex_lt hδ))

theorem rcauchy_ofQ_of_isCauchy {s : TreeN → K} (h : IsCauchy s) :
    RCauchy (fun n => ofQ (s n)) := by
  intro k
  obtain ⟨N, hN⟩ := isCauchy_tail h k
  exact ⟨N, fun i j hi hj => (rclose_ofQ (hN i j hi hj)).1⟩

/-! ## Explicit rational approximation of a class -/

/-- **Explicit approximation**: beyond its modulus, every term of a representative is
`eps k`-close to the class (the index is the representative's own `c.mod k`). -/
theorem mkR_close_seq (c : CSeq K) {k n : TreeN} (hn : PathLE (c.mod k) n) :
    RClose (ofQ (c.seq n)) (mkR c) (eps k) := by
  constructor
  · apply rnonneg_mk (c := addSeq (addSeq c (constSeq (eps k))) (negSeq (constSeq (c.seq n))))
    apply seqNonneg_of_eventually_nonneg (c.mod k)
    intro m hm
    show 𝟘 ≤ c.seq m + eps k + -c.seq n
    apply sub_nonneg_of_le
    rw [add_comm (c.seq m)]
    exact lower_of_abs (c.isMod k n m hn hm)
  · apply rnonneg_mk (c := addSeq (addSeq (constSeq (c.seq n)) (constSeq (eps k))) (negSeq c))
    apply seqNonneg_of_eventually_nonneg (c.mod k)
    intro m hm
    show 𝟘 ≤ c.seq n + eps k + -c.seq m
    apply sub_nonneg_of_le
    rw [add_comm (c.seq n)]
    exact lower_of_abs (c.isMod k m n hm hn)

/-- The canonical approximant of Cauchy data at precision `i`. -/
def approxAt (c : CSeq K) (i : TreeN) : K := c.seq (c.mod i)

theorem approxAt_close (c : CSeq K) (i : TreeN) : RClose (mkR c) (ofQ (approxAt c i)) (eps i) :=
  rclose_symm (mkR_close_seq c (TreeN.le_refl _))

/-! ## A2: strength of regularization -/

/-- The regularized data have the same class as the input. -/
theorem mkR_reg (c : CSeq K) : mkR (CSeq.ofRegular (reg c) (isRegular_reg c)) = mkR c :=
  mkR_sound (reg_equiv c)

/-- Closeness up to every extra `eps j` gives closeness. -/
theorem rclose_of_forall_add_eps {x y : TreeR K} {e : K} (h : ∀ j, RClose x y (e + eps j)) :
    RClose x y e := by
  constructor
  · apply le_of_forall_le_add_eps
    intro j
    have h1 := (h j).1
    rw [ofQ_add, ← add_assoc] at h1
    exact h1
  · apply le_of_forall_le_add_eps
    intro j
    have h1 := (h j).2
    rw [ofQ_add, ← add_assoc] at h1
    exact h1

/-- A regular representative approximates its class at **every** index with error `eps n`. -/
theorem regular_close {s : TreeN → K} (hs : IsRegular s) (n : TreeN) :
    RClose (ofQ (s n)) (mkR (CSeq.ofRegular s hs)) (eps n) := by
  apply rclose_of_forall_add_eps
  intro j
  let m := maxN (succ (succ j)) n
  have hm : PathLE (succ (succ j)) m := TreeN.le_maxN_left _ _
  have h1 : abs (s n + -s m) ≤ eps n + eps (succ j) :=
    TOField.le_trans (hs n m) (TOField.add_le_add_left _
      (TOField.le_trans (eps_le_eps hm) (eps_succ_le _)))
  have h2 := mkR_close_seq (CSeq.ofRegular s hs) (k := succ j) (n := m) hm
  have h3 := rclose_trans (rclose_ofQ h1) h2
  rw [add_assoc, eps_succ_add] at h3
  exact h3

/-- Two regular representatives of the same real satisfy Bishop's pointwise bound. -/
theorem regular_rep_bishop {s t : TreeN → K} (hs : IsRegular s) (ht : IsRegular t)
    (h : mkR (CSeq.ofRegular s hs) = mkR (CSeq.ofRegular t ht)) (n : TreeN) :
    abs (s n + -t n) ≤ eps n + eps n :=
  bishop_of_seqEquiv hs ht (mkR_exact h) n

/-- Every real has a regular representative (a `Prop`-level statement; no selection). -/
theorem exists_regular_rep (x : TreeR K) :
    ∃ s : TreeN → K, ∃ hs : IsRegular s, mkR (CSeq.ofRegular s hs) = x := by
  induction x using ind_mkR with
  | h c => exact ⟨reg c, isRegular_reg c, mkR_reg c⟩

/-- Every real is, for each fixed precision, within `eps i` of a rational (`Prop`-level). -/
theorem exists_rat_close (x : TreeR K) (i : TreeN) : ∃ q : K, RClose x (ofQ q) (eps i) := by
  induction x using ind_mkR with
  | h c => exact ⟨approxAt c i, approxAt_close c i⟩

/-! ## A3: the diagonal step needs only one rational per index -/

/-- Approximation data for a sequence of reals: one rational `q i` per index, with an explicit
error schedule `M` (beyond `M k`, the error is at most `eps k`). -/
def ApproxData (f : TreeN → TreeR K) (q : TreeN → K) (M : TreeN → TreeN) : Prop :=
  ∀ k i, PathLE (M k) i → RClose (f i) (ofQ (q i)) (eps k)

/-- Pointwise approximation `|f i - q i| ≤ eps i` is approximation data with `M = id`. -/
theorem approxData_of_pointwise {f : TreeN → TreeR K} {q : TreeN → K}
    (h : ∀ i, RClose (f i) (ofQ (q i)) (eps i)) : ApproxData f q (fun k => k) :=
  fun _ i hi => rclose_mono (h i) (eps_le_eps hi)

/-- The rational modulus of approximants of a real Cauchy sequence. -/
def approxMod (ν M : TreeN → TreeN) (k : TreeN) : TreeN :=
  maxN (ν (succ (succ k))) (M (succ (succ k)))

theorem approx_isModulus {f : TreeN → TreeR K} {ν : TreeN → TreeN} (hc : RCauchyMod f ν)
    {q : TreeN → K} {M : TreeN → TreeN} (hq : ApproxData f q M) :
    IsModulus q (approxMod ν M) := by
  intro k m n hm hn
  have hmν := TreeN.le_of_maxN_le_left hm
  have hmM := TreeN.le_of_maxN_le_right hm
  have hnν := TreeN.le_of_maxN_le_left hn
  have hnM := TreeN.le_of_maxN_le_right hn
  have h1 := rclose_trans (rclose_trans (rclose_symm (hq _ m hmM)) (rcauchyMod_close hc hmν hnν))
    (hq _ n hnM)
  exact TOField.le_trans (abs_le_of_rclose_ofQ h1) (three_eps_le k)

/-- The rational Cauchy data formed by the approximants. -/
def approxSeq {f : TreeN → TreeR K} {ν : TreeN → TreeN} (hc : RCauchyMod f ν)
    {q : TreeN → K} {M : TreeN → TreeN} (hq : ApproxData f q M) : CSeq K :=
  ⟨q, approxMod ν M, approx_isModulus hc hq⟩

/-- **A3 (sharpened diagonal)**: the class of the approximants is a limit, reached with the
explicit schedule `k ↦ max (approxMod ν M (k+1)) (M (k+1))`. -/
theorem approxSeq_converges {f : TreeN → TreeR K} {ν : TreeN → TreeN} (hc : RCauchyMod f ν)
    {q : TreeN → K} {M : TreeN → TreeN} (hq : ApproxData f q M) (k i : TreeN)
    (hi : PathLE (maxN (approxMod ν M (succ k)) (M (succ k))) i) :
    RClose (f i) (mkR (approxSeq hc hq)) (eps k) := by
  have h1 := hq (succ k) i (TreeN.le_of_maxN_le_right hi)
  have h2 := mkR_close_seq (approxSeq hc hq) (k := succ k) (n := i) (TreeN.le_of_maxN_le_left hi)
  have h3 := rclose_trans h1 h2
  rw [eps_succ_add] at h3
  exact h3

/-- **A3**: a real Cauchy sequence with a modulus and approximation data converges. -/
theorem limit_of_approx {f : TreeN → TreeR K} {ν : TreeN → TreeN} (hc : RCauchyMod f ν)
    {q : TreeN → K} {M : TreeN → TreeN} (hq : ApproxData f q M) : ∃ L, ConvergesTo f L :=
  ⟨mkR (approxSeq hc hq), fun k => ⟨_, fun i hi => approxSeq_converges hc hq k i hi⟩⟩

/-- A limit of a Cauchy sequence with modulus `ν` is reached with the same modulus `ν`. -/
theorem close_of_cauchy_of_converges {f : TreeN → TreeR K} {ν : TreeN → TreeN}
    (hc : RCauchyMod f ν) {L : TreeR K} (hL : ConvergesTo f L) {k i : TreeN}
    (hi : PathLE (ν k) i) : RClose (f i) L (eps k) := by
  apply rclose_of_forall_add_eps
  intro m
  obtain ⟨N, hN⟩ := hL m
  let j := maxN N (ν k)
  have h1 := rclose_trans (rcauchyMod_close hc hi (TreeN.le_maxN_right N (ν k)))
    (hN j (TreeN.le_maxN_left _ _))
  exact h1

/-- A tracked tower supplies pointwise approximants: the only information its diagonal uses. -/
theorem TrackedCauchyTower.approx (T : TrackedCauchyTower K) :
    ApproxData (fun i => mkR (T.r i)) (fun i => approxAt (T.r i) i) (fun k => k) :=
  approxData_of_pointwise (fun i => approxAt_close (T.r i) i)

/-- `tower_limit`, recovered from approximation data only. -/
theorem tower_limit_via_approx (T : TrackedCauchyTower K) :
    ∃ L, ConvergesTo (fun i => mkR (T.r i)) L :=
  limit_of_approx (f := fun i => mkR (T.r i)) T.cauchy T.approx

/-- The two limits agree (uniqueness of limits). -/
theorem tower_limit_eq_approx_limit (T : TrackedCauchyTower K) :
    T.limit = mkR (approxSeq (f := fun i => mkR (T.r i)) T.cauchy T.approx) :=
  limit_unique T.tower_converges
    (fun k => ⟨_, fun i hi => approxSeq_converges (f := fun i => mkR (T.r i)) T.cauchy T.approx
      k i hi⟩)

end TreeR
end
