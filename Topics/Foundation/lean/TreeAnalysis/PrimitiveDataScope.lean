module

public import TreeAnalysis.CompletenessStrength
public import BoundaryTopology.BinaryEncoding

@[expose] public section

/-!
# Task 03, Checkpoint E — dependence on primitive path data and canonicity

E1 (provenance): `provenance_chain` composes the existing definitional links
`rootEdges → unitSum → pathSum = depth → TreeN → TreeZ → Q★ → TreeR`.

E2 (raw prefix counts): for a ray `r`, `prefixCount r n` is the image in the rational base of
the **unmodified** primitive edge count `pathSum (prefixAt r n)`.
* `prefixCount_eq`: it equals the image of `n` (by `Ray.pathSum_prefixAt`);
* `prefixCount_not_isCauchy`: it is **not** Cauchy in the project's own sense (`IsCauchy`), with
  the explicit tolerance `1` and the unit-edge increment `prefixCount_succ`;
* `prefixCount_indep`: the prefix-count sequences of **any two rays coincide**, so no
  observation of these sequences distinguishes rays (`prefixCount_observation_indep`).
  This does **not** say that every map from rays to numbers is constant:
  `encode_distinguishes` exhibits a map (using an extra letter choice) separating two rays.

E3 (the optional binary encoding of Task 02 uses extra choices): `Ray.encode` depends on the
chosen letter `l1` (`TwoLetters` instance) — `encode_letter_choice_dependence` proves that
swapping the roles of the two letters changes the value on the constant ray at `l0` from `0`
to `1`.
-/

open CSR CRing TField TOField TreeR Word
open TreeN (PathLE PathLT succ maxN)

namespace PrimitiveScope

variable {α K : Type} [TOField K]

/-! ## E1: provenance -/

/-- The path count of a vertex enters the completion through `TreeZ` and `Q★`, and equals the
image of its depth. -/
theorem provenance_chain (w : Word α) :
    natR (K := QStar) (pathSum w) = ofZR (TreeZ.ofN (depth w)) ∧
    pathSum w = unitSum (rootEdges w) ∧ unitSum (rootEdges w) = depth w :=
  ⟨by rw [pathSum_eq_depth, natR_eq_ofZR], rfl, unitSum_rootEdges w⟩

/-! ## E2: the raw prefix-count sequence -/

/-- The image in `K` of the primitive edge count of the length-`n` prefix of `r`. -/
def prefixCount (r : Ray α) (n : TreeN) : K := natCast (pathSum (Ray.prefixAt r n))

theorem prefixCount_eq (r : Ray α) (n : TreeN) : prefixCount (K := K) r n = natCast n := by
  unfold prefixCount
  rw [Ray.pathSum_prefixAt]

/-- Each further unit edge adds exactly `1`. -/
theorem prefixCount_succ (r : Ray α) (n : TreeN) :
    prefixCount (K := K) r (succ n) = 𝟙 + prefixCount r n := by
  rw [prefixCount_eq, prefixCount_eq]
  rfl

/-- **The raw prefix-count sequence is not Cauchy** (tolerance `1`). -/
theorem prefixCount_not_isCauchy (r : Ray α) : ¬ IsCauchy (prefixCount (K := K) r) := by
  intro h
  obtain ⟨N, hN⟩ := h 𝟙 TOField.zero_lt_one
  have h1 := hN (succ N) N (TreeN.le_of_lt (TreeN.lt_succ_self N)) (TreeN.le_refl N)
  rw [prefixCount_succ, add_sub_cancel_right, abs_of_pos TOField.zero_lt_one] at h1
  exact TOField.lt_irrefl _ h1

/-- Nor is its image in the completion Cauchy. -/
theorem prefixCount_not_rcauchy (r : Ray α) :
    ¬ RCauchy (fun n => ofQ (prefixCount (K := K) r n)) :=
  fun h => prefixCount_not_isCauchy r (isCauchy_of_rcauchy_ofQ h)

/-- **Prefix counts do not depend on the ray.**  Immediate lemma: every prefix of length `n`
has path sum `n` by construction (`Ray.pathSum_prefixAt`), so this is a direct consequence of the
fixed-length prefixes, not an independent substantive theorem. -/
theorem prefixCount_indep (r r' : Ray α) : prefixCount (K := K) r = prefixCount r' :=
  funext (fun n => by rw [prefixCount_eq, prefixCount_eq])

/-- Hence no observation of the prefix-count sequence separates two rays. -/
theorem prefixCount_observation_indep {β : Type} (F : (TreeN → K) → β) (r r' : Ray α) :
    F (prefixCount r) = F (prefixCount r') := by
  rw [prefixCount_indep r r']

/-- The same holds for rays over different alphabets. -/
theorem prefixCount_indep_alphabet {β : Type} (r : Ray α) (r' : Ray β) :
    prefixCount (K := K) r = prefixCount r' :=
  funext (fun n => by rw [prefixCount_eq, prefixCount_eq])

end PrimitiveScope

/-! ## E3: the binary encoding depends on the letter choice -/

namespace Ray

variable {α K : Type} [DecidableEq α] [TOField K]

/-- The two letters with their roles exchanged. -/
def swappedLetters (T : TwoLetters α) : TwoLetters α := ⟨T.l1, T.l0, fun h => T.ne h.symm⟩

variable [TwoLetters α]

theorem psum_all_l0 (n : TreeN) : psum (K := K) (fun _ => (TwoLetters.l0 : α)) n = 𝟘 := by
  induction n with
  | nil => rfl
  | cons c n ih =>
    rw [UnaryPath.cons_eq_extend c n, psum_succ, ih, digit_l0, CSR.zero_mul, CSR.add_zero]

theorem psum_all_l1 (n : TreeN) :
    psum (K := K) (fun _ => (TwoLetters.l1 : α)) n + eps n = 𝟙 := by
  induction n with
  | nil => exact Eq.trans (CSR.zero_add _) eps_zero
  | cons c n ih =>
    rw [UnaryPath.cons_eq_extend c n, psum_succ, digit_l1, CSR.one_mul, CSR.add_assoc,
      eps_succ_add, ih]

theorem encode_all_l0 : encode (K := K) (fun _ => (TwoLetters.l0 : α)) = 𝟘 :=
  mkR_sound (seqEquiv_of_eq (fun n => psum_all_l0 n))

theorem encode_all_l1 : encode (K := K) (fun _ => (TwoLetters.l1 : α)) = 𝟙 := by
  apply mkR_sound
  intro k
  refine ⟨k, fun n hn => ?_⟩
  show abs (psum (K := K) (fun _ => (TwoLetters.l1 : α)) n + -𝟙) ≤ eps k
  rw [← psum_all_l1 (K := K) (α := α) n, neg_add, ← CSR.add_assoc, add_neg_cancel, CSR.zero_add,
    abs_neg, abs_of_pos (eps_pos n)]
  exact eps_le_eps hn

/-- The encoding separates the two constant rays (so maps from rays to numbers built with extra
choices need not be constant). -/
theorem encode_distinguishes :
    encode (K := K) (fun _ => (TwoLetters.l0 : α)) ≠ encode (fun _ => (TwoLetters.l1 : α)) := by
  rw [encode_all_l0, encode_all_l1]
  exact TreeR.zero_ne_one

end Ray

namespace Ray

variable {α K : Type} [DecidableEq α] [TOField K]

/-- **E3: the encoding is not invariant under the choice of the designated letter.** With the
letters exchanged, the constant ray at `l0` is encoded by `1` instead of `0`. -/
theorem encode_letter_choice_dependence (T : TwoLetters α) :
    @encode α K _ T _ (fun _ => T.l0) = 𝟘 ∧
    @encode α K _ (swappedLetters T) _ (fun _ => T.l0) = 𝟙 ∧
    @encode α K _ T _ (fun _ => T.l0) ≠ @encode α K _ (swappedLetters T) _ (fun _ => T.l0) := by
  have h0 : @encode α K _ T _ (fun _ => T.l0) = 𝟘 := @encode_all_l0 α K _ _ T
  have h1 : @encode α K _ (swappedLetters T) _ (fun _ => T.l0) = 𝟙 :=
    @encode_all_l1 α K _ _ (swappedLetters T)
  refine ⟨h0, h1, ?_⟩
  rw [h0, h1]
  exact TreeR.zero_ne_one

end Ray
end
