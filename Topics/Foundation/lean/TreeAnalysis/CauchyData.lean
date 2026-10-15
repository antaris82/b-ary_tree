module

public import TreeAnalysis.DyadicPrecision

@[expose] public section

/-!
# Checkpoint B1–B3 — three Cauchy notions, regularization, equivalence

All indices are tree-path counts `TreeN`; the precisions are `eps k = 1/2^k`.

* `IsCauchy s`  — the *ordinary* Cauchy predicate: for every positive rational `δ` there is an
  index beyond which all terms are `δ`-close (a `Prop`, no modulus is supplied);
* `IsModulus s μ` — `μ : TreeN → TreeN` is an *explicit modulus*: beyond `μ k` all terms are
  `eps k`-close;
* `IsRegular s` — the *regular* (Bishop-style) error discipline
  `|s m - s n| ≤ eps m + eps n` (a design option, not a property of arbitrary sequences).

`CSeq K` (sequence together with an explicit modulus) is the representation used for the
completion.  Regularization (`reg`) resamples a modulated sequence along the constructed
monotone schedule `rho μ` and is proved regular and equivalent to the input.

`SeqEquiv s t` — the difference tends to zero, with explicit quantified tail estimates.
For regular sequences it agrees with Bishop's indexwise formulation
`|s n - t n| ≤ eps n + eps n` (`seqEquiv_iff_bishop`).
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TOField

variable {K : Type} [TOField K]

/-- The ordinary rational Cauchy predicate (no modulus data). -/
def IsCauchy (s : TreeN → K) : Prop :=
  ∀ δ : K, 𝟘 < δ → ∃ N : TreeN, ∀ m n, PathLE N m → PathLE N n → abs (s m + -s n) < δ

/-- An explicit Cauchy modulus at the precisions `eps k`. -/
def IsModulus (s : TreeN → K) (μ : TreeN → TreeN) : Prop :=
  ∀ k m n, PathLE (μ k) m → PathLE (μ k) n → abs (s m + -s n) ≤ eps k

/-- Regular (fast) Cauchy sequences: `|s m - s n| ≤ eps m + eps n`. -/
def IsRegular (s : TreeN → K) : Prop := ∀ m n, abs (s m + -s n) ≤ eps m + eps n

/-- Rational Cauchy data: a sequence of rationals with an explicit modulus. -/
structure CSeq (K : Type) [TOField K] where
  seq : TreeN → K
  mod : TreeN → TreeN
  isMod : IsModulus seq mod

/-- Cauchy equivalence: the difference tends to zero (explicit tail estimates). -/
def SeqEquiv (s t : TreeN → K) : Prop :=
  ∀ k, ∃ N : TreeN, ∀ n, PathLE N n → abs (s n + -t n) ≤ eps k

/-! ## Relations between the three notions -/

/-- A sequence with an explicit modulus is an ordinary Cauchy sequence. -/
theorem isCauchy_of_isModulus {s : TreeN → K} {μ : TreeN → TreeN} (h : IsModulus s μ) :
    IsCauchy s := fun δ hδ =>
  ⟨μ (epsIndex δ), fun m n hm hn => lt_of_le_of_lt (h _ m n hm hn) (eps_epsIndex_lt hδ)⟩

theorem eps_add_eps_le_of_le {m n k : TreeN} (hm : PathLE (succ k) m) (hn : PathLE (succ k) n) :
    eps (K := K) m + eps n ≤ eps k := by
  have h := add_le_add (eps_le_eps (K := K) hm) (eps_le_eps (K := K) hn)
  rw [eps_succ_add] at h
  exact h

/-- A regular sequence has the explicit modulus `k ↦ k+1`. -/
theorem isModulus_of_isRegular {s : TreeN → K} (h : IsRegular s) : IsModulus s succ :=
  fun _ m n hm hn => le_trans (h m n) (eps_add_eps_le_of_le hm hn)

/-- Every regular representation is an ordinary Cauchy sequence. -/
theorem isCauchy_of_isRegular {s : TreeN → K} (h : IsRegular s) : IsCauchy s :=
  isCauchy_of_isModulus (isModulus_of_isRegular h)

/-- The ordinary predicate yields, for each precision, a `Prop`-level tail index. -/
theorem isCauchy_tail {s : TreeN → K} (h : IsCauchy s) (k : TreeN) :
    ∃ N, ∀ m n, PathLE N m → PathLE N n → abs (s m + -s n) ≤ eps k := by
  obtain ⟨N, hN⟩ := h (eps k) (eps_pos k)
  exact ⟨N, fun m n hm hn => le_of_lt (hN m n hm hn)⟩

/-- **Conditional extraction of a modulus.**  A modulus *function* can be obtained from the
ordinary (`Prop`-level) Cauchy predicate under the choice principle `∀ k ∃ N, P k N → ∃ f, ∀ k,
P k (f k)` for `TreeN`-indexed families; this principle is an explicit premise here (it is not
used anywhere else in the project). -/
theorem exists_modulus_of_choice
    (choice : ∀ P : TreeN → TreeN → Prop, (∀ k, ∃ N, P k N) → ∃ f : TreeN → TreeN, ∀ k, P k (f k))
    {s : TreeN → K} (h : IsCauchy s) : ∃ μ, IsModulus s μ := by
  obtain ⟨f, hf⟩ := choice _ (isCauchy_tail h)
  exact ⟨f, fun k m n hm hn => hf k m n hm hn⟩

/-! ## Regularization along a constructed monotone schedule -/

/-- The monotone resampling schedule `rho μ n = max_{i ≤ n} μ (i+1)`. -/
def rho (μ : TreeN → TreeN) : TreeN → TreeN
  | [] => μ (succ TreeN.zero)
  | c :: n => maxN (rho μ n) (μ (succ (c :: n)))

theorem rho_le_succ (μ : TreeN → TreeN) (n : TreeN) : PathLE (rho μ n) (rho μ (succ n)) :=
  TreeN.le_maxN_left _ _

theorem rho_mono (μ : TreeN → TreeN) {m n : TreeN} (h : PathLE m n) :
    PathLE (rho μ m) (rho μ n) := by
  obtain ⟨k, hk⟩ := TreeN.exists_of_le h
  rw [hk]
  clear hk h
  induction k with
  | nil =>
    rw [show m + [] = m from TreeN.add_zero m]
    exact TreeN.le_refl _
  | cons c k ih =>
    have e : m + c :: k = succ (m + k) := by rw [UnaryPath.cons_eq_extend, TreeN.add_succ]
    rw [e]
    exact TreeN.le_trans ih (rho_le_succ μ _)

theorem mod_le_rho_self (μ : TreeN → TreeN) (n : TreeN) : PathLE (μ (succ n)) (rho μ n) := by
  cases n with
  | nil => exact TreeN.le_refl _
  | cons c n => exact TreeN.le_maxN_right _ _

theorem mod_le_rho (μ : TreeN → TreeN) {i n : TreeN} (h : PathLE i n) :
    PathLE (μ (succ i)) (rho μ n) :=
  TreeN.le_trans (mod_le_rho_self μ i) (rho_mono μ h)

/-- The regularized sequence `n ↦ s (rho μ n)`. -/
def reg (c : CSeq K) : TreeN → K := fun n => c.seq (rho c.mod n)

/-- The regularized sequence is regular. -/
theorem isRegular_reg (c : CSeq K) : IsRegular (reg c) := by
  intro m n
  cases TreeN.le_or_lt m n with
  | inl h =>
    have h1 := c.isMod (succ m) _ _ (mod_le_rho c.mod (TreeN.le_refl m)) (mod_le_rho c.mod h)
    exact le_trans h1 (le_trans (eps_succ_le m) (le_add_of_nonneg_right (eps_nonneg n)))
  | inr h =>
    have h1 := c.isMod (succ n) _ _ (mod_le_rho c.mod (TreeN.le_of_lt h))
      (mod_le_rho c.mod (TreeN.le_refl n))
    have h2 := le_trans (eps_succ_le (K := K) n) (le_add_of_nonneg_right (x := eps n) (eps_nonneg m))
    rw [add_comm] at h2
    exact le_trans h1 h2

/-- The regularization is Cauchy-equivalent to the original sequence. -/
theorem reg_equiv (c : CSeq K) : SeqEquiv (reg c) c.seq := by
  intro k
  refine ⟨maxN k (c.mod (succ k)), fun n hn => ?_⟩
  have h1 : PathLE (c.mod (succ k)) (rho c.mod n) := mod_le_rho c.mod (TreeN.le_of_maxN_le_left hn)
  exact le_trans (c.isMod (succ k) _ _ h1 (TreeN.le_of_maxN_le_right hn)) (eps_succ_le k)

/-- Every regular sequence, packaged with its modulus `k ↦ k+1`. -/
def CSeq.ofRegular (s : TreeN → K) (h : IsRegular s) : CSeq K := ⟨s, succ, isModulus_of_isRegular h⟩

/-! ## Cauchy equivalence -/

theorem seqEquiv_refl (s : TreeN → K) : SeqEquiv s s := fun k =>
  ⟨TreeN.zero, fun n _ => by rw [add_neg_cancel, abs_zero]; exact eps_nonneg k⟩

theorem seqEquiv_symm {s t : TreeN → K} (h : SeqEquiv s t) : SeqEquiv t s := fun k => by
  obtain ⟨N, hN⟩ := h k
  exact ⟨N, fun n hn => by rw [abs_sub_comm]; exact hN n hn⟩

theorem seqEquiv_trans {s t u : TreeN → K} (h1 : SeqEquiv s t) (h2 : SeqEquiv t u) :
    SeqEquiv s u := fun k => by
  obtain ⟨N1, hN1⟩ := h1 (succ k)
  obtain ⟨N2, hN2⟩ := h2 (succ k)
  refine ⟨maxN N1 N2, fun n hn => ?_⟩
  have h := le_trans (abs_sub_le (s n) (t n) (u n))
    (add_le_add (hN1 n (TreeN.le_of_maxN_le_left hn)) (hN2 n (TreeN.le_of_maxN_le_right hn)))
  rw [eps_succ_add] at h
  exact h

/-- Pointwise-equal tails are equivalent. -/
theorem seqEquiv_of_eventually_eq {s t : TreeN → K} (N : TreeN)
    (h : ∀ n, PathLE N n → s n = t n) : SeqEquiv s t := fun k =>
  ⟨N, fun n hn => by rw [h n hn, add_neg_cancel, abs_zero]; exact eps_nonneg k⟩

theorem seqEquiv_of_eq {s t : TreeN → K} (h : ∀ n, s n = t n) : SeqEquiv s t :=
  seqEquiv_of_eventually_eq TreeN.zero (fun n _ => h n)

/-- Equivalence is preserved by the regularization (on both sides). -/
theorem reg_resp {c d : CSeq K} (h : SeqEquiv c.seq d.seq) : SeqEquiv (reg c) (reg d) :=
  seqEquiv_trans (reg_equiv c) (seqEquiv_trans h (seqEquiv_symm (reg_equiv d)))

/-! ## Agreement with Bishop's indexwise formulation for regular sequences -/

theorem rearrange4 {α : Type} [CSR α] (a b c : α) : a + b + c + (b + a) = a + a + (b + b + c) := by
  rw [add_comm b a, add_right_comm a b c, add_add_add_comm (a + c) b a b, add_right_comm a c a,
    add_assoc (a + a) c (b + b), add_comm c (b + b)]

theorem seqEquiv_of_bishop {s t : TreeN → K} (h : ∀ n, abs (s n + -t n) ≤ eps n + eps n) :
    SeqEquiv s t := fun k =>
  ⟨succ k, fun n hn => le_trans (h n) (eps_add_eps_le_of_le hn hn)⟩

theorem bishop_of_seqEquiv {s t : TreeN → K} (hs : IsRegular s) (ht : IsRegular t)
    (h : SeqEquiv s t) (n : TreeN) : abs (s n + -t n) ≤ eps n + eps n := by
  apply le_of_forall_le_add_eps
  intro j
  obtain ⟨N, hN⟩ := h (succ (succ j))
  let m := maxN N (succ (succ j))
  have hmN : PathLE N m := TreeN.le_maxN_left _ _
  have hmj : PathLE (succ (succ j)) m := TreeN.le_maxN_right _ _
  have h1 : abs (s n + -t n) ≤ abs (s n + -s m) + abs (s m + -t m) + abs (t m + -t n) :=
    le_trans (abs_sub_le (s n) (s m) (t n))
      (add_le_add_left _ (abs_sub_le (s m) (t m) (t n))) |> fun x => by
        rw [← add_assoc] at x; exact x
  have h2 := add_le_add (add_le_add (hs n m) (hN m hmN)) (ht m n)
  rw [rearrange4] at h2
  have hm := eps_le_eps (K := K) hmj
  have h3 : eps m + eps m + eps (succ (succ j)) ≤ eps (K := K) j :=
    le_trans (add_le_add_right _ (add_le_add hm hm)) (three_eps_le j)
  exact le_trans h1 (le_trans h2 (add_le_add_left _ h3))

/-- For regular sequences the tail formulation and Bishop's formulation agree. -/
theorem seqEquiv_iff_bishop {s t : TreeN → K} (hs : IsRegular s) (ht : IsRegular t) :
    (SeqEquiv s t → ∀ n, abs (s n + -t n) ≤ eps n + eps n) ∧
    ((∀ n, abs (s n + -t n) ≤ eps n + eps n) → SeqEquiv s t) :=
  ⟨bishop_of_seqEquiv hs ht, seqEquiv_of_bishop⟩

end TOField
end
