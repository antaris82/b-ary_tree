module

public import TreeAnalysis.CauchyData

@[expose] public section

/-!
# Operations on rational Cauchy data

Closure of the modulated representation `CSeq K` under the arithmetic operations, each with an
**explicitly constructed new modulus**:

* constants: modulus `0`;
* sum: `k ↦ max (μ (k+1)) (ν (k+1))`;
* product: a constructive bound `|s n| ≤ 2^(B s)` beyond `μ 0` (`B s` from the explicit
  Archimedean bound of `|s (μ 0)| + 1`), and the shifted modulus
  `k ↦ max (max (μ 0) (ν 0)) (max (μ (k+1+B t)) (ν (k+1+B s)))`.  A pointwise product is
  *not* given the input moduli: the shift by the bounds is part of the construction;
* inverse of a sequence with a positive separation witness `(k, N)`: the resampled sequence
  `n ↦ 1 / s (N + n)` with modulus `j ↦ μ (j + (k + k))`.

Compatibility of all operations with Cauchy equivalence is proved here; positivity and
nonnegativity of representatives are defined and proved representative-independent.
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TOField

open TField

variable {K : Type} [TOField K]

theorem le_add_of_sub_le {x y e : K} (h : x + -y ≤ e) : x ≤ e + y := by
  have h2 := add_le_add_right y h
  rw [add_assoc, neg_add_cancel, add_zero] at h2
  exact h2

theorem sub_le_of_le_add {x y e : K} (h : x ≤ e + y) : x + -y ≤ e := by
  have h2 := add_le_add_right (-y) h
  rw [add_sub_cancel_right] at h2
  exact h2

theorem add_sub_add (a b c d : K) : a + b + -(c + d) = (a + -c) + (b + -d) := by
  rw [neg_add, add_add_add_comm]

theorem mul_sub_mul (a b c d : K) : a * b + -(c * d) = a * (b + -d) + (a + -c) * d := by
  rw [CRing.mul_sub, CRing.sub_mul, CRing.sub_add_sub]

theorem abs_mul_le {a b A B : K} (ha : abs a ≤ A) (hb : abs b ≤ B) : abs (a * b) ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul (abs_nonneg a) ha (abs_nonneg b) hb

/-! ## Constructive bounds -/

/-- The bound index of Cauchy data: `|s n| ≤ 2^(bnd c)` for `n ≥ μ 0`. -/
def bnd (c : CSeq K) : TreeN := archBound (abs (c.seq (c.mod TreeN.zero)) + 𝟙)

theorem abs_le_bnd (c : CSeq K) {n : TreeN} (hn : PathLE (c.mod TreeN.zero) n) :
    abs (c.seq n) ≤ natCast (twoPow (bnd c)) := by
  have h1 := abs_le_abs_add_abs_sub (c.seq n) (c.seq (c.mod TreeN.zero))
  have h2 := c.isMod TreeN.zero n _ hn (TreeN.le_refl _)
  rw [eps_zero] at h2
  have h3 := le_trans h1 (add_le_add_left _ h2)
  exact le_trans h3 (le_trans (le_archBound _) (natCast_le (TreeN.le_of_lt (lt_twoPow _))))

/-! ## Operations on Cauchy data -/

/-- Constant Cauchy data. -/
def constSeq (q : K) : CSeq K :=
  ⟨fun _ => q, fun _ => TreeN.zero, fun k _ _ _ _ => by
    show abs (q + -q) ≤ eps k
    rw [add_neg_cancel, abs_zero]
    exact eps_nonneg k⟩

/-- Sum of Cauchy data. -/
def addSeq (c d : CSeq K) : CSeq K :=
  ⟨fun n => c.seq n + d.seq n, fun k => maxN (c.mod (succ k)) (d.mod (succ k)), fun k m n hm hn => by
    show abs (c.seq m + d.seq m + -(c.seq n + d.seq n)) ≤ eps k
    rw [add_sub_add, ← eps_succ_add]
    exact le_trans (abs_add _ _) (add_le_add
      (c.isMod _ m n (TreeN.le_of_maxN_le_left hm) (TreeN.le_of_maxN_le_left hn))
      (d.isMod _ m n (TreeN.le_of_maxN_le_right hm) (TreeN.le_of_maxN_le_right hn)))⟩

/-- Negation of Cauchy data. -/
def negSeq (c : CSeq K) : CSeq K :=
  ⟨fun n => -c.seq n, c.mod, fun k m n hm hn => by
    show abs (-c.seq m + - -c.seq n) ≤ eps k
    rw [← neg_add, abs_neg]
    exact c.isMod k m n hm hn⟩

/-- Modulus of the product. -/
def mulMod (c d : CSeq K) (k : TreeN) : TreeN :=
  maxN (maxN (c.mod TreeN.zero) (d.mod TreeN.zero))
    (maxN (c.mod (succ k + bnd d)) (d.mod (succ k + bnd c)))

theorem mulMod_isMod (c d : CSeq K) : IsModulus (fun n => c.seq n * d.seq n) (mulMod c d) := by
  intro k m n hm hn
  show abs (c.seq m * d.seq m + -(c.seq n * d.seq n)) ≤ eps k
  have hm1 := TreeN.le_of_maxN_le_left hm
  have hm2 := TreeN.le_of_maxN_le_right hm
  have hn1 := TreeN.le_of_maxN_le_left hn
  have hn2 := TreeN.le_of_maxN_le_right hn
  rw [mul_sub_mul, ← eps_succ_add]
  apply le_trans (abs_add _ _)
  apply add_le_add
  · have h := abs_mul_le (abs_le_bnd c (TreeN.le_of_maxN_le_left hm1))
      (d.isMod _ m n (TreeN.le_of_maxN_le_right hm2) (TreeN.le_of_maxN_le_right hn2))
    rw [natCast_twoPow_mul_eps_add] at h
    exact h
  · have h := abs_mul_le
      (c.isMod _ m n (TreeN.le_of_maxN_le_left hm2) (TreeN.le_of_maxN_le_left hn2))
      (abs_le_bnd d (TreeN.le_of_maxN_le_right hn1))
    rw [mul_comm (eps _) (natCast _), natCast_twoPow_mul_eps_add] at h
    exact h

/-- Product of Cauchy data, with the shifted modulus `mulMod`. -/
def mulSeq (c d : CSeq K) : CSeq K := ⟨fun n => c.seq n * d.seq n, mulMod c d, mulMod_isMod c d⟩

/-! ## Compatibility with Cauchy equivalence -/

theorem add_resp {s s' t t' : TreeN → K} (h1 : SeqEquiv s s') (h2 : SeqEquiv t t') :
    SeqEquiv (fun n => s n + t n) (fun n => s' n + t' n) := fun k => by
  obtain ⟨N1, hN1⟩ := h1 (succ k)
  obtain ⟨N2, hN2⟩ := h2 (succ k)
  refine ⟨maxN N1 N2, fun n hn => ?_⟩
  show abs (s n + t n + -(s' n + t' n)) ≤ eps k
  rw [add_sub_add, ← eps_succ_add]
  exact le_trans (abs_add _ _)
    (add_le_add (hN1 n (TreeN.le_of_maxN_le_left hn)) (hN2 n (TreeN.le_of_maxN_le_right hn)))

theorem neg_resp {s s' : TreeN → K} (h : SeqEquiv s s') :
    SeqEquiv (fun n => -s n) (fun n => -s' n) := fun k => by
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  show abs (-s n + - -s' n) ≤ eps k
  rw [← neg_add, abs_neg]
  exact hN n hn

/-- Multiplication by an eventually bounded sequence respects equivalence. -/
theorem mul_resp_bounded {s s' t : TreeN → K} (B N0 : TreeN)
    (hb : ∀ n, PathLE N0 n → abs (t n) ≤ natCast (twoPow B)) (h : SeqEquiv s s') :
    SeqEquiv (fun n => s n * t n) (fun n => s' n * t n) := fun k => by
  obtain ⟨N, hN⟩ := h (k + B)
  refine ⟨maxN N N0, fun n hn => ?_⟩
  show abs (s n * t n + -(s' n * t n)) ≤ eps k
  rw [← neg_mul, ← right_distrib]
  have h2 := abs_mul_le (hN n (TreeN.le_of_maxN_le_left hn)) (hb n (TreeN.le_of_maxN_le_right hn))
  rw [mul_comm (eps _) (natCast _), natCast_twoPow_mul_eps_add] at h2
  exact h2

theorem mulSeq_resp {c c' d d' : CSeq K} (h1 : SeqEquiv c.seq c'.seq) (h2 : SeqEquiv d.seq d'.seq) :
    SeqEquiv (mulSeq c d).seq (mulSeq c' d').seq := by
  apply seqEquiv_trans (t := fun n => c'.seq n * d.seq n)
  · exact mul_resp_bounded (bnd d) (d.mod TreeN.zero) (fun n hn => abs_le_bnd d hn) h1
  · have h3 := mul_resp_bounded (t := c'.seq) (bnd c') (c'.mod TreeN.zero)
      (fun n hn => abs_le_bnd c' hn) h2
    intro k
    obtain ⟨N, hN⟩ := h3 k
    refine ⟨N, fun n hn => ?_⟩
    show abs (c'.seq n * d.seq n + -(c'.seq n * d'.seq n)) ≤ eps k
    rw [mul_comm (c'.seq n) (d.seq n), mul_comm (c'.seq n) (d'.seq n)]
    exact hN n hn

/-! ## Positivity and nonnegativity of representatives -/

/-- A positive separation witness: beyond `N`, all terms are at least `eps k`. -/
structure PosWit (s : TreeN → K) : Type where
  k : TreeN
  N : TreeN
  spec : ∀ n, PathLE N n → eps k ≤ s n

/-- Positivity of a representative (propositional form). -/
def SeqPos (s : TreeN → K) : Prop := ∃ k N : TreeN, ∀ n, PathLE N n → eps k ≤ s n

/-- Nonnegativity of a representative: eventually above `-eps k`, for every `k`. -/
def SeqNonneg (s : TreeN → K) : Prop := ∀ k, ∃ N : TreeN, ∀ n, PathLE N n → -eps k ≤ s n

theorem seqPos_of_posWit {s : TreeN → K} (w : PosWit s) : SeqPos s := ⟨w.k, w.N, w.spec⟩

theorem lower_of_abs {a b e : K} (h : abs (a + -b) ≤ e) : a ≤ e + b :=
  le_add_of_sub_le (le_of_abs_le h)

theorem upper_of_abs {a b e : K} (h : abs (a + -b) ≤ e) : b ≤ e + a := by
  rw [abs_sub_comm] at h
  exact lower_of_abs h

theorem seqPos_resp {s t : TreeN → K} (h : SeqEquiv s t) (hp : SeqPos s) : SeqPos t := by
  obtain ⟨k, N, hN⟩ := hp
  obtain ⟨N', hN'⟩ := h (succ k)
  refine ⟨succ k, maxN N N', fun n hn => ?_⟩
  have h1 := le_trans (hN n (TreeN.le_of_maxN_le_left hn))
    (lower_of_abs (hN' n (TreeN.le_of_maxN_le_right hn)))
  rw [← eps_succ_add] at h1
  exact le_of_add_le_add_left h1

theorem seqNonneg_resp {s t : TreeN → K} (h : SeqEquiv s t) (hp : SeqNonneg s) : SeqNonneg t := by
  intro k
  obtain ⟨N, hN⟩ := hp (succ k)
  obtain ⟨N', hN'⟩ := h (succ k)
  refine ⟨maxN N N', fun n hn => ?_⟩
  have h1 := le_trans (hN n (TreeN.le_of_maxN_le_left hn))
    (lower_of_abs (hN' n (TreeN.le_of_maxN_le_right hn)))
  have h2 := add_le_add_left (-eps (succ k)) h1
  rw [← add_assoc, neg_add_cancel, zero_add, ← neg_add, eps_succ_add] at h2
  exact h2

theorem seqNonneg_of_seqPos {s : TreeN → K} (h : SeqPos s) : SeqNonneg s := by
  obtain ⟨k, N, hN⟩ := h
  intro j
  refine ⟨N, fun n hn => le_trans ?_ (hN n hn)⟩
  have h1 := neg_le_neg (eps_nonneg (K := K) j)
  rw [neg_zero] at h1
  exact le_trans h1 (eps_nonneg k)

/-! ## Inverse of a positively separated representative -/

/-- Inverse sequence, resampled along the separation witness. -/
def invSeqFun (c : CSeq K) (w : PosWit c.seq) : TreeN → K := fun n => inv (c.seq (w.N + n))

theorem pos_of_wit (c : CSeq K) (w : PosWit c.seq) (n : TreeN) : 𝟘 < c.seq (w.N + n) :=
  lt_of_lt_of_le (eps_pos w.k) (w.spec _ (TreeN.le_add_right _ _))

theorem inv_le_twoPow (c : CSeq K) (w : PosWit c.seq) (n : TreeN) :
    inv (c.seq (w.N + n)) ≤ natCast (twoPow w.k) := by
  have h := inv_le_inv (eps_pos w.k) (w.spec (w.N + n) (TreeN.le_add_right w.N n))
  unfold eps at h
  rw [inv_inv' (natCast_twoPow_ne w.k)] at h
  exact h

theorem inv_sub_inv {a b : K} (ha : a ≠ 𝟘) (hb : b ≠ 𝟘) :
    inv a + -inv b = (b + -a) * (inv a * inv b) := by
  rw [CRing.sub_mul, mul_left_comm, mul_inv_cancel' hb, mul_one, ← mul_assoc,
    mul_inv_cancel' ha, one_mul]

theorem invSeq_isMod (c : CSeq K) (w : PosWit c.seq) :
    IsModulus (invSeqFun c w) (fun j => c.mod (j + (w.k + w.k))) := by
  intro j m n hm hn
  show abs (inv (c.seq (w.N + m)) + -inv (c.seq (w.N + n))) ≤ eps j
  have ha := pos_of_wit c w m
  have hb := pos_of_wit c w n
  rw [inv_sub_inv (fun e => ne_of_lt ha e.symm) (fun e => ne_of_lt hb e.symm)]
  have h1 := c.isMod _ (w.N + n) (w.N + m) (TreeN.le_trans hn (TreeN.le_add_left _ _))
    (TreeN.le_trans hm (TreeN.le_add_left _ _))
  have h2 : abs (inv (c.seq (w.N + m)) * inv (c.seq (w.N + n)))
      ≤ natCast (twoPow w.k) * natCast (twoPow w.k) := by
    rw [abs_of_pos (mul_pos (inv_pos ha) (inv_pos hb))]
    exact mul_le_mul (le_of_lt (inv_pos ha)) (inv_le_twoPow c w m) (le_of_lt (inv_pos hb))
      (inv_le_twoPow c w n)
  have h3 := abs_mul_le h1 h2
  have e : eps (K := K) (j + (w.k + w.k)) * (natCast (twoPow w.k) * natCast (twoPow w.k))
      = eps j := by
    rw [eps_add, eps_add, mul_assoc, mul_mul_mul_comm (eps w.k) (eps w.k),
      mul_comm (eps w.k) (natCast (twoPow w.k)), natCast_twoPow_mul_eps, one_mul, mul_one]
  rw [e] at h3
  exact h3

/-- The inverse Cauchy data of a positively separated representative. -/
def invSeq (c : CSeq K) (w : PosWit c.seq) : CSeq K :=
  ⟨invSeqFun c w, fun j => c.mod (j + (w.k + w.k)), invSeq_isMod c w⟩

/-- `s · (1/s) ~ 1`. -/
theorem mul_invSeq_equiv (c : CSeq K) (w : PosWit c.seq) :
    SeqEquiv (mulSeq c (invSeq c w)).seq (constSeq 𝟙).seq := by
  intro j
  refine ⟨c.mod (j + w.k), fun n hn => ?_⟩
  show abs (c.seq n * inv (c.seq (w.N + n)) + -𝟙) ≤ eps j
  have hb := pos_of_wit c w n
  have hb0 : c.seq (w.N + n) ≠ 𝟘 := fun e => ne_of_lt hb e.symm
  have e : c.seq n * inv (c.seq (w.N + n)) + -𝟙
      = (c.seq n + -c.seq (w.N + n)) * inv (c.seq (w.N + n)) := by
    rw [CRing.sub_mul, mul_inv_cancel' hb0]
  rw [e]
  have h1 := c.isMod _ n (w.N + n) hn (TreeN.le_trans hn (TreeN.le_add_left _ _))
  have h2 : abs (inv (c.seq (w.N + n))) ≤ natCast (twoPow w.k) := by
    rw [abs_of_pos (inv_pos hb)]
    exact inv_le_twoPow c w n
  have h3 := abs_mul_le h1 h2
  rw [mul_comm (eps _) (natCast _), natCast_twoPow_mul_eps_add] at h3
  exact h3

end TOField
end
