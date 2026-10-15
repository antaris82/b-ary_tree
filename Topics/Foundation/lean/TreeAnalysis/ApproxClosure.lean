module

public import TreeAnalysis.FoundationsClosure

@[expose] public section

/-!
# Task 04, Checkpoint E2 — closure of explicitly controlled approximations

A `Tracked f` is a small record of data that is **already** used by Task 03's
`limit_of_approx`: a real Cauchy modulus `ν` for `f`, and approximation data `(q, M)`.  It is not
a new primitive sequence kind and does not assume any closure property.

Proved here (all unconditional, with explicit output data):

* real estimates: `rclose_add`, `rclose_neg`, `rclose_sub_iff`, and the product estimate
  `rclose_mul_zero` (`|w| ≤ B`, `|u| ≤ e` ⟹ `|w·u| ≤ B·e`), proved without any sign decision by
  the identity `(B-w)(e+u) + (B+w)(e-u) = 2(Be - wu)` and halving;
* `Tracked.add`, `Tracked.neg`, `Tracked.mul`, `Tracked.smulQ` (scaling by a rational),
  `Tracked.smulRep` (scaling by the class of explicit Cauchy data): closure with explicit output
  moduli and approximation schedules.  The product uses the **derived** bound
  `2^(bnd)` of the approximant sequences, not the input moduli;
* `Tracked.lim_add`, `lim_neg`, `lim_mul`, `lim_smulQ`: the limit commutes with the operations;
* `Tracked.lim_indep`: the limit does not depend on the tracking data, and two approximant
  sequences for one family are Cauchy-equivalent (`approx_seqEquiv`);
* general convergence algebra without any data: `converges_add`, `converges_neg`,
  `converges_mul` (Prop-level `ConvergesTo` is closed under `+`, `-`, `·`).
-/

open CSR CRing TOField TField TreeR
open TreeN (PathLE PathLT succ maxN)

namespace TreeR

variable {K : Type} [TOField K]

/-! ## Algebraic identities -/

theorem cring_four {α : Type} [CRing α] (a b c d : α) :
    (a + b + c + d) + (a + -b + -c + d) = (a + d) + (a + d) := by
  have e1 : a + b + c + d = (a + d) + (b + c) := by
    rw [add_right_comm, add_assoc, add_assoc, add_assoc, add_left_comm b d c]
  have e2 : a + -b + -c + d = (a + d) + -(b + c) := by
    rw [neg_add, add_right_comm, add_assoc, add_assoc, add_assoc, add_left_comm (-b) d (-c)]
  rw [e1, e2, add_add_add_comm, add_neg_cancel, add_zero]

/-- The identity `(B-w)(e+u) + (B+w)(e-u) = 2(Be - wu)` behind the sign-free product estimate. -/
theorem cring_trick {α : Type} [CRing α] (B w e u : α) :
    (B + -w) * (e + u) + (B + w) * (e + -u) = (B * e + -(w * u)) + (B * e + -(w * u)) := by
  have e1 : (B + -w) * (e + u) = B * e + B * u + -(w * e) + -(w * u) := by
    rw [right_distrib, left_distrib, left_distrib, neg_mul, neg_mul, ← add_assoc]
  have e2 : (B + w) * (e + -u) = B * e + -(B * u) + - -(w * e) + -(w * u) := by
    rw [right_distrib, left_distrib, left_distrib, mul_neg, mul_neg, neg_neg, ← add_assoc]
  rw [e1, e2, cring_four]

theorem cring_two_terms {α : Type} [CRing α] (f g a b : α) :
    f * g + -(a * b) = f * (g + -b) + (f + -a) * b := by
  rw [mul_sub, sub_mul, add_assoc, ← add_assoc (-(f * b)), neg_add_cancel, zero_add]

/-! ## Real estimates -/

theorem rnonneg_half {z : TreeR K} (h : RNonneg (z + z)) : RNonneg z := by
  have hh : RNonneg (ofQ (eps (K := K) (succ TreeN.zero))) :=
    (nonneg_iff _).1 (ofQ_le_ofQ (eps_nonneg _))
  have e : ofQ (eps (K := K) (succ TreeN.zero)) * (z + z) = z := by
    rw [left_distrib, ← right_distrib, ← ofQ_add, eps_succ_add, eps_zero]
    exact one_mul z
  rw [← e]
  exact rnonneg_mul hh h

theorem rclose_zero_iff (x : TreeR K) (e : K) :
    (RClose x 𝟘 e → RNonneg (ofQ e + -x) ∧ RNonneg (x + ofQ e)) ∧
    (RNonneg (ofQ e + -x) ∧ RNonneg (x + ofQ e) → RClose x 𝟘 e) := by
  constructor
  · intro h
    have h1 : RNonneg (𝟘 + ofQ e + -x) := h.1
    have h2 : RNonneg (x + ofQ e + -𝟘) := h.2
    rw [zero_add] at h1
    rw [sub_zero'] at h2
    exact ⟨h1, h2⟩
  · intro h
    constructor
    · show RNonneg (𝟘 + ofQ e + -x)
      rw [zero_add]
      exact h.1
    · show RNonneg (x + ofQ e + -𝟘)
      rw [sub_zero']
      exact h.2

/-- **Product estimate**: `|w| ≤ B` and `|u| ≤ e` give `|w·u| ≤ B·e`, with no sign decision. -/
theorem rclose_mul_zero {w u : TreeR K} {B e : K} (hw : RClose w 𝟘 B) (hu : RClose u 𝟘 e) :
    RClose (w * u) 𝟘 (B * e) := by
  obtain ⟨hw1, hw2⟩ := (rclose_zero_iff w B).1 hw
  obtain ⟨hu1, hu2⟩ := (rclose_zero_iff u e).1 hu
  rw [add_comm] at hw2 hu2
  apply (rclose_zero_iff _ _).2
  constructor
  · apply rnonneg_half
    rw [ofQ_mul, ← cring_trick]
    exact rnonneg_add (rnonneg_mul hw1 hu2) (rnonneg_mul hw2 hu1)
  · apply rnonneg_half
    have e1 := cring_trick (ofQ B) w (ofQ e) (-u)
    rw [neg_neg, mul_neg, neg_neg] at e1
    rw [ofQ_mul, add_comm (w * u)]
    rw [← e1]
    exact rnonneg_add (rnonneg_mul hw1 hu1) (rnonneg_mul hw2 hu2)

theorem rclose_sub_iff (x y : TreeR K) (e : K) :
    (RClose x y e → RClose (x + -y) 𝟘 e) ∧ (RClose (x + -y) 𝟘 e → RClose x y e) := by
  have e1 : ofQ e + -(x + -y) = y + ofQ e + -x := by
    rw [neg_add, neg_neg, add_comm (-x), ← add_assoc, add_comm (ofQ e)]
  have e2 : x + -y + ofQ e = x + ofQ e + -y := add_right_comm _ _ _
  constructor
  · intro h
    apply (rclose_zero_iff _ _).2
    rw [e1, e2]
    exact ⟨h.1, h.2⟩
  · intro h
    obtain ⟨h1, h2⟩ := (rclose_zero_iff _ _).1 h
    rw [e1] at h1
    rw [e2] at h2
    exact ⟨h1, h2⟩

theorem rclose_add {x x' y y' : TreeR K} {e e' : K} (h1 : RClose x x' e) (h2 : RClose y y' e') :
    RClose (x + y) (x' + y') (e + e') := by
  have r : ∀ a b : TreeR K, a + ofQ e + (b + ofQ e') = a + b + ofQ (e + e') := by
    intro a b
    rw [ofQ_add, add_add_add_comm]
  constructor
  · have h := add_le_add h1.1 h2.1
    rw [r] at h
    exact h
  · have h := add_le_add h1.2 h2.2
    rw [r] at h
    exact h

theorem rclose_neg {x y : TreeR K} {e : K} (h : RClose x y e) : RClose (-x) (-y) e := by
  have r : ∀ a b : TreeR K, -b + ofQ e + - -a = a + ofQ e + -b := by
    intro a b
    rw [neg_neg, add_comm (-b), add_assoc, add_comm (-b), ← add_assoc, add_comm (ofQ e)]
  constructor
  · show RNonneg (-y + ofQ e + - -x)
    rw [r]
    exact h.2
  · show RNonneg (-x + ofQ e + - -y)
    rw [r]
    exact h.1

theorem rclose_zero_of_abs {p B : K} (h : abs p ≤ B) : RClose (ofQ p) 𝟘 B := by
  have h' : abs (p + -𝟘) ≤ B := by rw [neg_zero, add_zero]; exact h
  exact rclose_ofQ h'

/-- The product estimate in its two-term form: if `f ≈ a`, `g ≈ b` with `|f| ≤ D`, `|b| ≤ D`
and both errors `≤ e`, then `f·g ≈ a·b` within `D·e + D·e`. -/
theorem rclose_mul {f g a b : TreeR K} {D e : K} (hf : RClose f 𝟘 D) (hb : RClose b 𝟘 D)
    (hfa : RClose f a e) (hgb : RClose g b e) : RClose (f * g) (a * b) (D * e + D * e) := by
  apply (rclose_sub_iff _ _ _).2
  rw [cring_two_terms]
  have t1 := rclose_mul_zero hf ((rclose_sub_iff _ _ _).1 hgb)
  have t2 := rclose_mul_zero hb ((rclose_sub_iff _ _ _).1 hfa)
  rw [mul_comm b] at t2
  have t := rclose_add t1 t2
  rw [zero_add] at t
  exact t


/-! ## Precision bookkeeping -/

theorem twoPow_mul_eps_shift (k T : TreeN) :
    natCast (K := K) (twoPow T) * eps (succ k + T) = eps (succ k) := by
  rw [eps_add, mul_left_comm, natCast_twoPow_mul_eps, mul_one]

theorem double_shift (k T : TreeN) :
    natCast (K := K) (twoPow T) * eps (succ k + T) + natCast (twoPow T) * eps (succ k + T) =
      eps k := by
  rw [twoPow_mul_eps_shift, eps_succ_add]

theorem natCast_le_twoPow_of_le {m T : TreeN} (h : PathLE m T) :
    natCast (K := K) m ≤ natCast (twoPow T) :=
  natCast_le (TreeN.le_trans h (TreeN.le_of_lt (lt_twoPow T)))

/-- Bounds `-n < x < n` by a path count give `|x| ≤ n`. -/
theorem rclose_zero_of_bounds {x : TreeR K} {n : TreeN} (h1 : x < natR n) (h2 : -natR n < x) :
    RClose x 𝟘 (natCast n) := by
  apply (rclose_zero_iff _ _).2
  constructor
  · exact le_of_lt h1
  · have h := le_of_lt h2
    have h' : RNonneg (x + - -natR n) := h
    rw [neg_neg] at h'
    exact h'

/-! ## Convergence algebra (no data needed) -/

theorem converges_add {f g : TreeN → TreeR K} {L L' : TreeR K} (hf : ConvergesTo f L)
    (hg : ConvergesTo g L') : ConvergesTo (fun i => f i + g i) (L + L') := by
  intro k
  obtain ⟨N1, h1⟩ := hf (succ k)
  obtain ⟨N2, h2⟩ := hg (succ k)
  refine ⟨maxN N1 N2, fun n hn => ?_⟩
  have h := rclose_add (h1 n (TreeN.le_of_maxN_le_left hn)) (h2 n (TreeN.le_of_maxN_le_right hn))
  rw [eps_succ_add] at h
  exact h

theorem converges_neg {f : TreeN → TreeR K} {L : TreeR K} (hf : ConvergesTo f L) :
    ConvergesTo (fun i => -f i) (-L) := by
  intro k
  obtain ⟨N, h⟩ := hf k
  exact ⟨N, fun n hn => rclose_neg (h n hn)⟩

/-- **Products of convergent sequences converge to the product of the limits** (no tracking
data needed; the bounds come from the Archimedean property at the `Prop` level). -/
theorem converges_mul {f g : TreeN → TreeR K} {L L' : TreeR K} (hf : ConvergesTo f L)
    (hg : ConvergesTo g L') : ConvergesTo (fun i => f i * g i) (L * L') := by
  intro k
  obtain ⟨n, hn1, hn2⟩ := archimedean_abs L
  obtain ⟨n', hn1', hn2'⟩ := archimedean_abs L'
  have hL := rclose_zero_of_bounds hn1 hn2
  have hL' := rclose_zero_of_bounds hn1' hn2'
  let T := succ (n + n')
  obtain ⟨N0, h0⟩ := hf TreeN.zero
  obtain ⟨N1, h1⟩ := hf (succ k + T)
  obtain ⟨N2, h2⟩ := hg (succ k + T)
  refine ⟨maxN N0 (maxN N1 N2), fun i hi => ?_⟩
  have hi0 := TreeN.le_of_maxN_le_left hi
  have hi1 := TreeN.le_of_maxN_le_left (TreeN.le_of_maxN_le_right hi)
  have hi2 := TreeN.le_of_maxN_le_right (TreeN.le_of_maxN_le_right hi)
  have hfi : RClose (f i) 𝟘 (natCast (twoPow T)) := by
    have h := rclose_trans (h0 i hi0) hL
    rw [eps_zero] at h
    apply rclose_mono h
    show natCast (K := K) (succ n) ≤ natCast (twoPow T)
    exact natCast_le_twoPow_of_le (TreeN.PathLE.succ_le _ _ (TreeN.le_add n n'))
  have hb : RClose L' 𝟘 (natCast (twoPow T)) := by
    apply rclose_mono hL'
    exact natCast_le_twoPow_of_le (TreeN.le_of_lt (TreeN.lt_succ_of_le (TreeN.le_add_left n' n)))
  have h := rclose_mul hfi hb (h1 i hi1) (h2 i hi2)
  rw [double_shift] at h
  exact h

/-! ## Tracked families -/

/-- **Tracked family**: a real sequence with a real Cauchy modulus and rational approximation
data — exactly the inputs of `limit_of_approx`.  A derived record, not a new sequence kind. -/
structure Tracked (f : TreeN → TreeR K) : Type where
  ν : TreeN → TreeN
  cauchy : RCauchyMod f ν
  q : TreeN → K
  M : TreeN → TreeN
  approx : ApproxData f q M

namespace Tracked

variable {f g : TreeN → TreeR K}

/-- The rational Cauchy data of the approximants. -/
def cseq (T : Tracked f) : CSeq K := approxSeq T.cauchy T.approx

/-- The limit of a tracked family. -/
def lim (T : Tracked f) : TreeR K := mkR T.cseq

theorem converges (T : Tracked f) : ConvergesTo f T.lim :=
  fun k => ⟨_, fun i hi => approxSeq_converges T.cauchy T.approx k i hi⟩

theorem lim_eq_of_converges (T : Tracked f) {L : TreeR K} (h : ConvergesTo f L) : T.lim = L :=
  limit_unique T.converges h

/-- **Independence of the limit from the tracking data** (modulus and approximants). -/
theorem lim_indep (T T' : Tracked f) : T.lim = T'.lim := lim_eq_of_converges T T'.converges

/-- Two approximant sequences of one family are Cauchy-equivalent. -/
theorem approx_seqEquiv (T T' : Tracked f) : SeqEquiv T.q T'.q := mkR_exact (lim_indep T T')

/-- A real Cauchy modulus derived from approximation data and a rational modulus of the
approximants (so the output modulus of every closure operation is explicit). -/
theorem rcauchyMod_of_approx {q : TreeN → K} {M μ : TreeN → TreeN} (h : ApproxData f q M)
    (hμ : IsModulus q μ) : RCauchyMod f (fun k => maxN (M (succ (succ k))) (μ (succ k))) := by
  intro k i j hi hj
  have h1 := h (succ (succ k)) i (TreeN.le_of_maxN_le_left hi)
  have h2 := rclose_ofQ (hμ (succ k) i j (TreeN.le_of_maxN_le_right hi)
    (TreeN.le_of_maxN_le_right hj))
  have h3 := rclose_symm (h (succ (succ k)) j (TreeN.le_of_maxN_le_left hj))
  have h4 := rclose_trans (rclose_trans h1 h2) h3
  rw [add_right_comm, eps_succ_add, eps_succ_add] at h4
  exact h4.1

/-- Build tracking data from approximants with a rational modulus. -/
def ofApproxMod (q : TreeN → K) (M μ : TreeN → TreeN) (h : ApproxData f q M)
    (hμ : IsModulus q μ) : Tracked f :=
  ⟨fun k => maxN (M (succ (succ k))) (μ (succ k)), rcauchyMod_of_approx h hμ, q, M, h⟩

/-- Constant rational family. -/
def constQ (c : K) : Tracked (fun _ => ofQ c) :=
  ⟨fun _ => TreeN.zero, fun k _ _ _ _ => (rclose_self (ofQ c) (eps k) (eps_nonneg k)).1,
   fun _ => c, fun _ => TreeN.zero, fun k _ _ => rclose_self (ofQ c) (eps k) (eps_nonneg k)⟩

/-- Constant family at the class of explicit Cauchy data. -/
def ofCSeq (c : CSeq K) : Tracked (fun _ => mkR c) :=
  ⟨fun _ => TreeN.zero, fun k _ _ _ _ => (rclose_self (mkR c) (eps k) (eps_nonneg k)).1,
   fun i => approxAt c i, fun k => k, approxData_of_pointwise (fun i => approxAt_close c i)⟩

/-- Embedded rational Cauchy data. -/
def ofRat (c : CSeq K) : Tracked (fun i => ofQ (c.seq i)) :=
  ⟨c.mod, rcauchyMod_ofQ c.isMod, c.seq, fun _ => TreeN.zero,
   fun k i _ => rclose_self (ofQ (c.seq i)) (eps k) (eps_nonneg k)⟩

/-- Every tracked Cauchy tower is tracked. -/
def ofTower (T : TrackedCauchyTower K) : Tracked (fun i => mkR (T.r i)) :=
  ⟨T.ν, T.cauchy, fun i => approxAt (T.r i) i, fun k => k, T.approx⟩

theorem lim_constQ (c : K) : (constQ c).lim = ofQ c :=
  lim_eq_of_converges _ (fun k => ⟨TreeN.zero, fun _ _ => rclose_self (ofQ c) (eps k) (eps_nonneg k)⟩)

theorem lim_ofCSeq (c : CSeq K) : (ofCSeq c).lim = mkR c :=
  lim_eq_of_converges _ (fun k => ⟨TreeN.zero, fun _ _ => rclose_self (mkR c) (eps k) (eps_nonneg k)⟩)

theorem lim_ofRat (c : CSeq K) : (ofRat c).lim = mkR c :=
  lim_eq_of_converges _ (ofQ_seq_converges c)

/-! ### Closure under the ring operations, with explicit output data -/

/-- **Sum**: approximants `q + r`, schedule `k ↦ max (M (k+1)) (M' (k+1))`, rational modulus
that of `addSeq`. -/
def add (T : Tracked f) (S : Tracked g) : Tracked (fun i => f i + g i) :=
  ofApproxMod (fun i => T.q i + S.q i) (fun k => maxN (T.M (succ k)) (S.M (succ k)))
    (addSeq T.cseq S.cseq).mod
    (fun k i hi => by
      have h := rclose_add (T.approx (succ k) i (TreeN.le_of_maxN_le_left hi))
        (S.approx (succ k) i (TreeN.le_of_maxN_le_right hi))
      rw [eps_succ_add, ← ofQ_add] at h
      exact h)
    (addSeq T.cseq S.cseq).isMod

/-- **Negation**: approximants `-q`, same schedule and modulus. -/
def neg (T : Tracked f) : Tracked (fun i => -f i) :=
  ofApproxMod (fun i => -T.q i) T.M (negSeq T.cseq).mod
    (fun k i hi => by
      have h := rclose_neg (T.approx k i hi)
      rw [← ofQ_neg] at h
      exact h)
    (negSeq T.cseq).isMod

/-- The derived bound index of the product: `2^T` dominates `1 + 2^(bnd)` of both approximant
sequences. -/
def mulShift (T : Tracked f) (S : Tracked g) : TreeN :=
  succ (twoPow (bnd T.cseq) + twoPow (bnd S.cseq))

/-- The approximation schedule of the product. -/
def mulM (T : Tracked f) (S : Tracked g) (k : TreeN) : TreeN :=
  maxN (maxN (T.cseq.mod TreeN.zero) (S.cseq.mod TreeN.zero))
    (maxN (T.M (succ k + mulShift T S)) (S.M (succ k + mulShift T S)))

theorem mul_approx (T : Tracked f) (S : Tracked g) :
    ApproxData (fun i => f i * g i) (fun i => T.q i * S.q i) (mulM T S) := by
  intro k i hi
  have hb0 := TreeN.le_of_maxN_le_left hi
  have hiT := TreeN.le_of_maxN_le_left (TreeN.le_of_maxN_le_right hi)
  have hiS := TreeN.le_of_maxN_le_right (TreeN.le_of_maxN_le_right hi)
  have hqT : abs (T.q i) ≤ natCast (twoPow (bnd T.cseq)) :=
    abs_le_bnd T.cseq (TreeN.le_of_maxN_le_left hb0)
  have hqS : abs (S.q i) ≤ natCast (twoPow (bnd S.cseq)) :=
    abs_le_bnd S.cseq (TreeN.le_of_maxN_le_right hb0)
  have hfa := T.approx _ i hiT
  have hgb := S.approx _ i hiS
  have hf : RClose (f i) 𝟘 (natCast (twoPow (mulShift T S))) := by
    have h := rclose_trans hfa (rclose_zero_of_abs hqT)
    apply rclose_mono h
    apply TOField.le_trans (TOField.add_le_add_right _ (eps_le_one _))
    show natCast (K := K) (succ (twoPow (bnd T.cseq))) ≤ natCast (twoPow (mulShift T S))
    exact natCast_le_twoPow_of_le (TreeN.PathLE.succ_le _ _ (TreeN.le_add _ _))
  have hb : RClose (ofQ (S.q i)) 𝟘 (natCast (twoPow (mulShift T S))) := by
    apply rclose_mono (rclose_zero_of_abs hqS)
    exact natCast_le_twoPow_of_le (TreeN.le_of_lt (TreeN.lt_succ_of_le (TreeN.le_add_left _ _)))
  have h := rclose_mul hf hb hfa hgb
  rw [double_shift, ← ofQ_mul] at h
  exact h

/-- **Product**: approximants `q·r`, the derived schedule `mulM`, and the rational modulus of
`mulSeq` (which is computed from the derived bounds `bnd`, not from the input moduli). -/
def mul (T : Tracked f) (S : Tracked g) : Tracked (fun i => f i * g i) :=
  ofApproxMod (fun i => T.q i * S.q i) (mulM T S) (mulSeq T.cseq S.cseq).mod (mul_approx T S)
    (mulSeq T.cseq S.cseq).isMod

/-- Scaling by a fixed rational. -/
def smulQ (c : K) (T : Tracked f) : Tracked (fun i => ofQ c * f i) := (constQ c).mul T

/-- Scaling by the class of fixed explicit Cauchy data. -/
def smulRep (c : CSeq K) (T : Tracked f) : Tracked (fun i => mkR c * f i) := (ofCSeq c).mul T

/-! ### The limit commutes with the operations -/

theorem lim_add (T : Tracked f) (S : Tracked g) : (T.add S).lim = T.lim + S.lim :=
  mkR_sound (seqEquiv_of_eq (fun _ => rfl))

theorem lim_neg (T : Tracked f) : T.neg.lim = -T.lim :=
  mkR_sound (seqEquiv_of_eq (fun _ => rfl))

theorem lim_mul (T : Tracked f) (S : Tracked g) : (T.mul S).lim = T.lim * S.lim :=
  mkR_sound (seqEquiv_of_eq (fun _ => rfl))

theorem lim_smulQ (c : K) (T : Tracked f) : (T.smulQ c).lim = ofQ c * T.lim := by
  unfold smulQ
  rw [lim_mul, lim_constQ]

theorem lim_smulRep (c : CSeq K) (T : Tracked f) : (T.smulRep c).lim = mkR c * T.lim := by
  unfold smulRep
  rw [lim_mul, lim_ofCSeq]

/-- Scaling by an arbitrary fixed real: tracking data for the scaled family exist (the real's
representative is obtained inside a proposition only, so no selection is claimed). -/
theorem exists_tracked_smul (x : TreeR K) (T : Tracked f) :
    ∃ S : Tracked (fun i => x * f i), S.lim = x * T.lim := by
  induction x using ind_mkR with
  | h c => exact ⟨T.smulRep c, lim_smulRep c T⟩

end Tracked

end TreeR

end
