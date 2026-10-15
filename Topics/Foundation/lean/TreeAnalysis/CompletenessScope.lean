module

public import TreeAnalysis.RealOrderApartness

@[expose] public section

/-!
# Checkpoint D3, D4 — completeness: three distinct claims

* **D3(a)** `ofQ_seq_converges`: the rational approximants of every representative converge
  to its class; `rat_dense`: `Q★` is dense in `TreeR`.
* **D3(b)** `tower_limit`: a `TrackedCauchyTower` — a sequence of *specified* rational Cauchy
  data `r i` (each with its own modulus) together with a *specified* modulus `ν` for the
  real-level Cauchy condition — has a limit, namely the class of the explicit diagonal sequence
  `m ↦ (r (I m)).seq ((r (I m)).mod m)` with the monotone schedule `I = rho ν`.
* **D3(c)** `complete_of_lifting`: unrestricted completeness for sequences `TreeN → TreeR K`
  is proved **only under the explicit premise** `SequenceLifting K` (every sequence of classes
  has a sequence of representatives — an instance of countable choice for this quotient).  The
  unconditional statement `UnrestrictedCompleteness K` is **not proved** here.
* **D4** `SupData` (structure; its least-upper-bound property is `TreeR.SupData.isLUB` in
  `TreeAnalysis/SupremumScope`): suprema exist for subsets equipped with explicit approximation data
  (rational upper bounds `u k` and members `s k` with `u k ≤ s k + eps k`).

`ConvergesTo f L` is the explicit convergence criterion; limits are unique (`limit_unique`).
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TOField

variable {K : Type} [TOField K]

/-- Combining three one-sided estimates. -/
theorem chain3 {a b c d e1 e2 e3 e4 : K} (h1 : a ≤ e1 + b) (h2 : b ≤ c + e2 + e4)
    (h3 : c ≤ e3 + d) : a ≤ d + (e1 + e3 + e2) + e4 := by
  have h := le_trans h1 (add_le_add_left e1 (le_trans h2
    (add_le_add_right e4 (add_le_add_right e2 h3))))
  have e : e1 + (e3 + d + e2 + e4) = d + (e1 + e3 + e2) + e4 := by
    rw [add_comm e3 d, ← add_assoc e1 (d + e3 + e2) e4, add_assoc d e3 e2,
      add_left_comm e1 d (e3 + e2), ← add_assoc e1 e3 e2]
  rw [e] at h
  exact h

theorem le_add_eps_of_neg_le {x y : K} (e : K) (h : -e ≤ y + -x) : x ≤ y + e := by
  have h2 := add_le_add_right (x + e) h
  rw [add_comm x e, ← add_assoc, neg_add_cancel, zero_add, add_assoc, add_left_comm (-x),
    neg_add_cancel, add_zero] at h2
  exact h2

end TOField

namespace TreeR

open TField TOField

variable {K : Type} [TOField K]

/-! ## Convergence and uniqueness of limits -/

/-- Explicit convergence criterion for sequences of reals. -/
def ConvergesTo (f : TreeN → TreeR K) (L : TreeR K) : Prop :=
  ∀ k, ∃ N : TreeN, ∀ n, PathLE N n → f n ≤ L + ofQ (eps k) ∧ L ≤ f n + ofQ (eps k)

theorem rnonneg_of_forall_add_eps {z : TreeR K} (h : ∀ k, RNonneg (z + ofQ (eps k))) :
    RNonneg z := by
  revert h
  induction z using ind_mkR with | h c => ?_
  intro h
  apply rnonneg_mk
  intro j
  obtain ⟨N, hN⟩ := seqNonneg_of_rnonneg (c := addSeq c (constSeq (eps (succ j)))) (h (succ j)) (succ j)
  refine ⟨N, fun n hn => ?_⟩
  have h0 : -eps (succ j) ≤ c.seq n + eps (succ j) := hN n hn
  have h1 := TOField.add_le_add_right (-eps (succ j)) h0
  rw [add_sub_cancel_right, neg_eps_succ_add] at h1
  exact h1

/-- If `x ≤ y + eps k` for all `k`, then `x ≤ y`. -/
theorem le_of_forall_le_add_eps {x y : TreeR K} (h : ∀ k, x ≤ y + ofQ (eps k)) : x ≤ y := by
  show RNonneg (y + -x)
  apply rnonneg_of_forall_add_eps
  intro k
  have h1 : RNonneg (y + ofQ (eps k) + -x) := h k
  rw [add_right_comm] at h1
  exact h1

/-- **Uniqueness of limits.** -/
theorem limit_unique {f : TreeN → TreeR K} {L L' : TreeR K} (h : ConvergesTo f L)
    (h' : ConvergesTo f L') : L = L' := by
  have key : ∀ {A B : TreeR K}, ConvergesTo f A → ConvergesTo f B → A ≤ B := by
    intro A B hA hB
    apply le_of_forall_le_add_eps
    intro k
    obtain ⟨N1, hN1⟩ := hA (succ k)
    obtain ⟨N2, hN2⟩ := hB (succ k)
    let n := maxN N1 N2
    have a := (hN1 n (TreeN.le_maxN_left _ _)).2
    have b := (hN2 n (TreeN.le_maxN_right _ _)).1
    have c := le_trans a (add_le_add_right (ofQ (eps (succ k))) b)
    rw [add_assoc, ← ofQ_add, eps_succ_add] at c
    exact c
  exact le_antisymm (key h h') (key h' h)

/-! ## D3(a): rational approximation -/

/-- **D3(a)**: the rational approximants of a representative converge to its class. -/
theorem ofQ_seq_converges (c : CSeq K) : ConvergesTo (fun n => ofQ (c.seq n)) (mkR c) := by
  intro k
  refine ⟨c.mod k, fun n hn => ⟨?_, ?_⟩⟩
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

/-- **Density of the rationals** in the completion (quantitative form). -/
theorem rat_dense (x : TreeR K) (k : TreeN) :
    ∃ q : K, ofQ q ≤ x + ofQ (eps k) ∧ x ≤ ofQ q + ofQ (eps k) := by
  induction x using ind_mkR with | h c => ?_
  obtain ⟨N, hN⟩ := ofQ_seq_converges c k
  exact ⟨c.seq N, hN N (TreeN.le_refl N)⟩

/-! ## D3(b): explicitly tracked Cauchy towers -/

/-- From a real-level estimate to a representative-level eventual estimate. -/
theorem close_of_le {a b : CSeq K} {e : K} (h : mkR a ≤ mkR b + ofQ e) (j : TreeN) :
    ∃ N, ∀ n, PathLE N n → a.seq n ≤ b.seq n + e + eps j := by
  obtain ⟨N, hN⟩ := seqNonneg_of_rnonneg (c := addSeq (addSeq b (constSeq e)) (negSeq a)) h j
  exact ⟨N, fun n hn => le_add_eps_of_neg_le _ (hN n hn)⟩

/-- A Cauchy sequence of reals whose terms come with *specified* rational Cauchy data and whose
real-level Cauchy condition comes with a *specified* modulus `ν`. -/
structure TrackedCauchyTower (K : Type) [TOField K] where
  r : TreeN → CSeq K
  ν : TreeN → TreeN
  cauchy : ∀ k i j, PathLE (ν k) i → PathLE (ν k) j → mkR (r i) ≤ mkR (r j) + ofQ (eps k)

namespace TrackedCauchyTower

variable (T : TrackedCauchyTower K)

/-- Monotone index schedule. -/
def I (m : TreeN) : TreeN := rho T.ν m

/-- The diagonal rational sequence. -/
def diag (m : TreeN) : K := (T.r (T.I m)).seq ((T.r (T.I m)).mod m)

theorem I_ge {k m : TreeN} (h : PathLE k m) : PathLE (T.ν (succ k)) (T.I m) := mod_le_rho T.ν h

theorem diag_le {k m m' : TreeN} (hm : PathLE (succ (succ k)) m) (hm' : PathLE (succ (succ k)) m') :
    T.diag m ≤ T.diag m' + eps k := by
  apply TOField.le_of_forall_le_add_eps
  intro j
  have hkm : PathLE k m := TreeN.le_trans (TreeN.le_trans (TreeN.le_succ _) (TreeN.le_succ _)) hm
  have hkm' : PathLE k m' := TreeN.le_trans (TreeN.le_trans (TreeN.le_succ _) (TreeN.le_succ _)) hm'
  obtain ⟨N, hN⟩ := close_of_le (T.cauchy (succ k) (T.I m) (T.I m') (T.I_ge hkm) (T.I_ge hkm')) j
  let a := T.r (T.I m)
  let b := T.r (T.I m')
  let n := maxN N (maxN (a.mod m) (b.mod m'))
  have hnN : PathLE N n := TreeN.le_maxN_left _ _
  have hna : PathLE (a.mod m) n := TreeN.le_of_maxN_le_left (TreeN.le_maxN_right _ _)
  have hnb : PathLE (b.mod m') n := TreeN.le_of_maxN_le_right (TreeN.le_maxN_right _ _)
  have h1 : T.diag m ≤ eps m + a.seq n := lower_of_abs (a.isMod m _ n (TreeN.le_refl _) hna)
  have h2 : a.seq n ≤ b.seq n + eps (succ k) + eps j := hN n hnN
  have h3 : b.seq n ≤ eps m' + T.diag m' := lower_of_abs (b.isMod m' n _ hnb (TreeN.le_refl _))
  have h := chain3 h1 h2 h3
  have hb : eps m + eps m' + eps (succ k) ≤ eps (K := K) k := by
    have := TOField.add_le_add_right (eps (K := K) (succ k)) (eps_add_eps_le_of_le hm hm')
    rw [eps_succ_add] at this
    exact this
  exact TOField.le_trans h (TOField.add_le_add_right _ (TOField.add_le_add_left _ hb))

theorem diag_isMod : IsModulus T.diag (fun k => succ (succ k)) := by
  intro k m n hm hn
  apply abs_le_of
  · have h1 := T.diag_le hn hm
    rw [add_comm] at h1
    have h := TOField.neg_le_neg (sub_le_of_le_add h1)
    rw [neg_sub'] at h
    exact h
  · have h1 := T.diag_le hm hn
    rw [add_comm] at h1
    exact sub_le_of_le_add h1

/-- The diagonal Cauchy data. -/
def diagSeq : CSeq K := ⟨T.diag, fun k => succ (succ k), T.diag_isMod⟩

/-- The limit of the tower. -/
def limit : TreeR K := mkR T.diagSeq

theorem upper {k i n : TreeN} (hi : PathLE (T.I (succ k)) i)
    (hn : PathLE (maxN (succ (succ k)) ((T.r i).mod (succ (succ k)))) n) :
    (T.r i).seq n ≤ T.diag n + eps k := by
  let q := succ (succ k)
  have hnq : PathLE q n := TreeN.le_of_maxN_le_left hn
  have hnm : PathLE ((T.r i).mod q) n := TreeN.le_of_maxN_le_right hn
  have hsk : PathLE (succ k) n := TreeN.le_trans (TreeN.le_succ _) hnq
  have hi' : PathLE (T.ν q) i := TreeN.le_trans (T.I_ge (TreeN.le_refl _)) hi
  have hIn : PathLE (T.ν q) (T.I n) := T.I_ge hsk
  apply TOField.le_of_forall_le_add_eps
  intro j
  obtain ⟨N, hN⟩ := close_of_le (T.cauchy q i (T.I n) hi' hIn) j
  let a := T.r i
  let b := T.r (T.I n)
  let n' := maxN N (maxN (a.mod q) (b.mod n))
  have hn'N : PathLE N n' := TreeN.le_maxN_left _ _
  have hn'a : PathLE (a.mod q) n' := TreeN.le_of_maxN_le_left (TreeN.le_maxN_right _ _)
  have hn'b : PathLE (b.mod n) n' := TreeN.le_of_maxN_le_right (TreeN.le_maxN_right _ _)
  have h1 : a.seq n ≤ eps q + a.seq n' := lower_of_abs (a.isMod q n n' hnm hn'a)
  have h2 : a.seq n' ≤ b.seq n' + eps q + eps j := hN n' hn'N
  have h3 : b.seq n' ≤ eps n + T.diag n := lower_of_abs (b.isMod n n' _ hn'b (TreeN.le_refl _))
  have h := chain3 h1 h2 h3
  have hb : eps q + eps n + eps q ≤ eps (K := K) k :=
    TOField.le_trans (TOField.add_le_add_right _ (TOField.add_le_add_left _ (eps_le_eps hnq)))
      (three_eps_le k)
  exact TOField.le_trans h (TOField.add_le_add_right _ (TOField.add_le_add_left _ hb))

theorem lower {k i n : TreeN} (hi : PathLE (T.I (succ k)) i)
    (hn : PathLE (maxN (succ (succ k)) ((T.r i).mod (succ (succ k)))) n) :
    T.diag n ≤ (T.r i).seq n + eps k := by
  let q := succ (succ k)
  have hnq : PathLE q n := TreeN.le_of_maxN_le_left hn
  have hnm : PathLE ((T.r i).mod q) n := TreeN.le_of_maxN_le_right hn
  have hsk : PathLE (succ k) n := TreeN.le_trans (TreeN.le_succ _) hnq
  have hi' : PathLE (T.ν q) i := TreeN.le_trans (T.I_ge (TreeN.le_refl _)) hi
  have hIn : PathLE (T.ν q) (T.I n) := T.I_ge hsk
  apply TOField.le_of_forall_le_add_eps
  intro j
  obtain ⟨N, hN⟩ := close_of_le (T.cauchy q (T.I n) i hIn hi') j
  let a := T.r i
  let b := T.r (T.I n)
  let n' := maxN N (maxN (a.mod q) (b.mod n))
  have hn'N : PathLE N n' := TreeN.le_maxN_left _ _
  have hn'a : PathLE (a.mod q) n' := TreeN.le_of_maxN_le_left (TreeN.le_maxN_right _ _)
  have hn'b : PathLE (b.mod n) n' := TreeN.le_of_maxN_le_right (TreeN.le_maxN_right _ _)
  have h1 : T.diag n ≤ eps n + b.seq n' := lower_of_abs (b.isMod n _ n' (TreeN.le_refl _) hn'b)
  have h2 : b.seq n' ≤ a.seq n' + eps q + eps j := hN n' hn'N
  have h3 : a.seq n' ≤ eps q + a.seq n := lower_of_abs (a.isMod q n' n hn'a hnm)
  have h := chain3 h1 h2 h3
  have hb : eps n + eps q + eps q ≤ eps (K := K) k :=
    TOField.le_trans (TOField.add_le_add_right _ (TOField.add_le_add_right _ (eps_le_eps hnq)))
      (three_eps_le k)
  exact TOField.le_trans h (TOField.add_le_add_right _ (TOField.add_le_add_left _ hb))

/-- **D3(b): every explicitly tracked Cauchy tower converges** (to its diagonal limit). -/
theorem tower_converges : ConvergesTo (fun i => mkR (T.r i)) T.limit := by
  intro k
  refine ⟨T.I (succ k), fun i hi => ⟨?_, ?_⟩⟩
  · apply rnonneg_mk (c := addSeq (addSeq T.diagSeq (constSeq (eps k))) (negSeq (T.r i)))
    apply seqNonneg_of_eventually_nonneg _
    intro n hn
    exact sub_nonneg_of_le (T.upper hi hn)
  · apply rnonneg_mk (c := addSeq (addSeq (T.r i) (constSeq (eps k))) (negSeq T.diagSeq))
    apply seqNonneg_of_eventually_nonneg _
    intro n hn
    exact sub_nonneg_of_le (T.lower hi hn)

end TrackedCauchyTower

/-- **D3(b)**, existence form. -/
theorem tower_limit (T : TrackedCauchyTower K) :
    ∃ L : TreeR K, ConvergesTo (fun i => mkR (T.r i)) L := ⟨T.limit, T.tower_converges⟩

/-! ## D3(c): unrestricted completeness — scope -/

/-- Real-level Cauchy condition with a specified modulus. -/
def RCauchyMod (f : TreeN → TreeR K) (ν : TreeN → TreeN) : Prop :=
  ∀ k i j, PathLE (ν k) i → PathLE (ν k) j → f i ≤ f j + ofQ (eps k)

/-- Real-level Cauchy condition without a modulus function. -/
def RCauchy (f : TreeN → TreeR K) : Prop :=
  ∀ k, ∃ N : TreeN, ∀ i j, PathLE N i → PathLE N j → f i ≤ f j + ofQ (eps k)

/-- The **unproved** statement of unrestricted sequential completeness (with modulus). -/
def UnrestrictedCompleteness (K : Type) [TOField K] : Prop :=
  ∀ (f : TreeN → TreeR K) (ν : TreeN → TreeN), RCauchyMod f ν → ∃ L, ConvergesTo f L

/-- The missing principle: a sequence of classes has a sequence of representatives
(countable choice for this quotient). -/
def SequenceLifting (K : Type) [TOField K] : Prop :=
  ∀ f : TreeN → TreeR K, ∃ g : TreeN → CSeq K, ∀ i, mkR (g i) = f i

/-- Countable choice for `TreeN`-indexed families of `TreeN`-valued choices. -/
def ChoiceNN : Prop :=
  ∀ P : TreeN → TreeN → Prop, (∀ k, ∃ N, P k N) → ∃ f : TreeN → TreeN, ∀ k, P k (f k)

/-- **D3(c), conditional**: under `SequenceLifting K`, every real Cauchy sequence with a
modulus converges. -/
theorem complete_of_lifting (hl : SequenceLifting K) : UnrestrictedCompleteness K := by
  intro f ν hc
  obtain ⟨g, hg⟩ := hl f
  have hc' : ∀ k i j, PathLE (ν k) i → PathLE (ν k) j → mkR (g i) ≤ mkR (g j) + ofQ (eps k) := by
    intro k i j hi hj
    rw [hg i, hg j]
    exact hc k i j hi hj
  obtain ⟨L, hL⟩ := tower_limit ⟨g, ν, hc'⟩
  refine ⟨L, fun k => ?_⟩
  obtain ⟨N, hN⟩ := hL k
  refine ⟨N, fun n hn => ?_⟩
  have h : mkR (g n) ≤ L + ofQ (eps k) ∧ L ≤ mkR (g n) + ofQ (eps k) := hN n hn
  rw [hg n] at h
  exact h

/-- **D3(c), conditional, modulus-free form**: under `SequenceLifting K` and `ChoiceNN`. -/
theorem complete_of_lifting_choice (hl : SequenceLifting K) (hc : ChoiceNN)
    (f : TreeN → TreeR K) (hf : RCauchy f) : ∃ L, ConvergesTo f L := by
  obtain ⟨ν, hν⟩ := hc _ hf
  exact complete_of_lifting hl f ν (fun k i j hi hj => hν k i j hi hj)

/-! ## D4: suprema with explicit approximation data -/

/-- Explicit approximation data for the supremum of a subset `S`. -/
structure SupData (S : TreeR K → Prop) where
  u : TreeN → K
  s : TreeN → TreeR K
  mem : ∀ k, S (s k)
  upper : ∀ k x, S x → x ≤ ofQ (u k)
  approx : ∀ k, ofQ (u k) ≤ s k + ofQ (eps k)

namespace SupData

variable {S : TreeR K → Prop} (D : SupData S)

theorem u_le (k m : TreeN) : D.u m ≤ D.u k + eps m := by
  apply le_of_ofQ_le
  rw [ofQ_add]
  exact le_trans (D.approx m) (add_le_add_right _ (D.upper k _ (D.mem m)))

theorem isRegular_u : IsRegular D.u := by
  intro m n
  apply abs_le_of
  · have h := D.u_le m n
    rw [add_comm] at h
    have h2 := TOField.neg_le_neg (sub_le_of_le_add h)
    rw [neg_sub'] at h2
    have h3 : eps (K := K) n ≤ eps m + eps n := by
      rw [add_comm]
      exact le_add_of_nonneg_right (eps_nonneg m)
    exact TOField.le_trans (TOField.neg_le_neg h3) h2
  · have h := D.u_le n m
    rw [add_comm] at h
    exact TOField.le_trans (sub_le_of_le_add h) (le_add_of_nonneg_right (eps_nonneg n))

/-- The supremum. -/
def sup : TreeR K := mkR (CSeq.ofRegular D.u D.isRegular_u)

/-- The supremum is an upper bound. -/
theorem le_sup {x : TreeR K} (hx : S x) : x ≤ D.sup := by
  apply le_of_forall_le_add_eps
  intro k
  obtain ⟨N, hN⟩ := ofQ_seq_converges (CSeq.ofRegular D.u D.isRegular_u) k
  exact le_trans (D.upper (maxN N (succ k)) x hx) (hN _ (TreeN.le_maxN_left _ _)).1

/-- The supremum is approximated from below by members of `S`. -/
theorem sup_approx (k : TreeN) : D.sup ≤ D.s (succ (succ k)) + ofQ (eps k) := by
  let k2 := succ (succ k)
  obtain ⟨N, hN⟩ := ofQ_seq_converges (CSeq.ofRegular D.u D.isRegular_u) (succ k)
  let n := maxN N k2
  have h1 := (hN n (TreeN.le_maxN_left _ _)).2
  have h2 : ofQ (D.u n) ≤ D.s k2 + ofQ (eps k2 + eps k2) := by
    have a : ofQ (D.u n) ≤ ofQ (D.u k2) + ofQ (eps k2) := by
      rw [← ofQ_add]
      exact ofQ_le_ofQ (TOField.le_trans (D.u_le k2 n)
        (TOField.add_le_add_left _ (eps_le_eps (TreeN.le_maxN_right _ _))))
    have b := add_le_add_right (ofQ (eps k2)) (D.approx k2)
    rw [add_assoc, ← ofQ_add] at b
    exact le_trans a b
  have h3 := le_trans h1 (add_le_add_right (ofQ (eps (succ k))) h2)
  rw [add_assoc, ← ofQ_add, eps_three] at h3
  exact h3

end SupData

end TreeR
end
