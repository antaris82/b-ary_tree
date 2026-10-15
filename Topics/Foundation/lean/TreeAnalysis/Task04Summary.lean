module

public import TreeAnalysis.ApproxClosure
public import TreeAnalysis.Canonicity

@[expose] public section

/-!
# Task 04 — axiom-by-axiom certificates for the four concrete carriers

Each theorem below states, for the **concrete** carrier, the full list of defining axioms of the
structure it is claimed to carry, and proves every item from the concrete theorems of the
project (not from an interface field taken on trust).  Conditional statements keep their
premise in the statement.

* `treeN_certificate`: `TreeN` is a commutative semiring with additive cancellation,
  cancellation by a positive factor, injective never-zero successor, and a decidable total order
  compatible with `+` and `·`;
* `treeZ_certificate`: `TreeZ` is a commutative ring, an integral domain (zero-product
  *disjunction*), with decidable total order compatible with `+` and with `·` by nonnegatives,
  and `TreeN → TreeZ` is an injective, order-preserving and -reflecting semiring embedding;
* `treeQ_certificate`: every `TreeQ α` (two letters) is an Archimedean, decidably and totally
  ordered field of characteristic zero;
* `treeR_unconditional_certificate`: `TreeRStar` is a commutative ring with `0 ≠ 1`, with a
  strict order that is irreflexive, transitive, cotransitive, tight, compatible with `+` and
  `·`, Archimedean and rationally dense, with inverses for apart elements and cancellation for
  nonzero elements;
* `treeR_conditional_certificate`: the conventional field law and three decision principles,
  each **equivalent** to a named omniscience/Markov principle, plus the proved one-way
  implications for completeness and order-completeness.
-/

open CSR CRing TOField TField TreeR TreeQ
open TreeN (PathLE PathLT succ)

namespace Task04

/-- Boolean-free decision from a `Decidable` instance (constructive). -/
theorem em_of_dec {p : Prop} (d : Decidable p) : p ∨ ¬ p :=
  match d with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr h

/-- **`TreeN` certificate** (unconditional). -/
theorem treeN_certificate :
    (∀ a b c : TreeN, a + b + c = a + (b + c)) ∧ (∀ a b : TreeN, a + b = b + a) ∧
    (∀ a : TreeN, TreeN.zero + a = a) ∧ (∀ a : TreeN, a + TreeN.zero = a) ∧
    (∀ a b c : TreeN, a * b * c = a * (b * c)) ∧ (∀ a b : TreeN, a * b = b * a) ∧
    (∀ a : TreeN, TreeN.one * a = a) ∧ (∀ a : TreeN, a * TreeN.one = a) ∧
    (∀ a : TreeN, TreeN.zero * a = TreeN.zero) ∧ (∀ a : TreeN, a * TreeN.zero = TreeN.zero) ∧
    (∀ a b c : TreeN, a * (b + c) = a * b + a * c) ∧
    (∀ a b c : TreeN, (a + b) * c = a * c + b * c) ∧
    (∀ a b c : TreeN, a + b = a + c → b = c) ∧
    (∀ k m n : TreeN, PathLT TreeN.zero k → k * m = k * n → m = n) ∧
    (∀ n : TreeN, succ n ≠ TreeN.zero) ∧ (∀ m n : TreeN, succ m = succ n → m = n) ∧
    TreeN.zero ≠ TreeN.one ∧
    (∀ n : TreeN, PathLE n n) ∧ (∀ a b c : TreeN, PathLE a b → PathLE b c → PathLE a c) ∧
    (∀ a b : TreeN, PathLE a b → PathLE b a → a = b) ∧ (∀ a b : TreeN, PathLE a b ∨ PathLE b a) ∧
    (∀ a b : TreeN, a = b ∨ ¬ a = b) ∧ (∀ a b : TreeN, PathLE a b ∨ ¬ PathLE a b) ∧
    (∀ a b : TreeN, PathLT a b ∨ ¬ PathLT a b) ∧
    (∀ k a b : TreeN, PathLE a b → PathLE (k + a) (k + b)) ∧
    (∀ k a b : TreeN, PathLE a b → PathLE (k * a) (k * b)) :=
  ⟨TreeN.add_assoc, TreeN.add_comm, TreeN.zero_add, TreeN.add_zero, TreeN.mul_assoc,
   TreeN.mul_comm, TreeN.one_mul, TreeN.mul_one, TreeN.zero_mul, TreeN.mul_zero,
   TreeN.left_distrib, TreeN.right_distrib, fun _ _ _ h => TreeN.add_left_cancel h,
   fun _ _ _ hk h => TreeN.mul_left_cancel hk h, TreeN.succ_ne_zero,
   fun _ _ h => TreeN.succ_injective h, TreeN.zero_ne_one, TreeN.le_refl,
   fun _ _ _ h1 h2 => TreeN.le_trans h1 h2, fun _ _ h1 h2 => TreeN.le_antisymm h1 h2,
   TreeN.le_total, fun a b => em_of_dec (TreeN.decEq a b), fun a b => em_of_dec (TreeN.decLE a b),
   fun a b => em_of_dec (TreeN.decLT a b), fun k _ _ h => TreeN.add_le_add_left k h,
   fun k _ _ h => TreeN.mul_le_mul_left k h⟩

/-- **`TreeZ` certificate** (unconditional). -/
theorem treeZ_certificate :
    (∀ a b c : TreeZ, a + b + c = a + (b + c)) ∧ (∀ a b : TreeZ, a + b = b + a) ∧
    (∀ a : TreeZ, 𝟘 + a = a) ∧ (∀ a : TreeZ, -a + a = 𝟘) ∧
    (∀ a b c : TreeZ, a * b * c = a * (b * c)) ∧ (∀ a b : TreeZ, a * b = b * a) ∧
    (∀ a : TreeZ, 𝟙 * a = a) ∧ (∀ a b c : TreeZ, a * (b + c) = a * b + a * c) ∧
    (𝟘 : TreeZ) ≠ 𝟙 ∧
    (∀ a b : TreeZ, a * b = 𝟘 → a = 𝟘 ∨ b = 𝟘) ∧
    (∀ a b c : TreeZ, a ≠ 𝟘 → a * b = a * c → b = c) ∧
    (∀ a b : TreeZ, a = b ∨ ¬ a = b) ∧
    (∀ a : TreeZ, TreeZ.LE a a) ∧
    (∀ a b c : TreeZ, TreeZ.LE a b → TreeZ.LE b c → TreeZ.LE a c) ∧
    (∀ a b : TreeZ, TreeZ.LE a b → TreeZ.LE b a → a = b) ∧
    (∀ a b : TreeZ, TreeZ.LE a b ∨ TreeZ.LE b a) ∧
    (∀ a b : TreeZ, TreeZ.LE a b ∨ ¬ TreeZ.LE a b) ∧
    (∀ a b c : TreeZ, TreeZ.LE a b → TreeZ.LE (c + a) (c + b)) ∧
    (∀ a b c : TreeZ, TreeZ.NonNeg c → TreeZ.LE a b → TreeZ.LE (c * a) (c * b)) ∧
    TreeZ.LT 𝟘 𝟙 ∧
    (∀ m n : TreeN, TreeZ.ofN m = TreeZ.ofN n → m = n) ∧
    (∀ m n : TreeN, TreeZ.ofN (m + n) = TreeZ.ofN m + TreeZ.ofN n) ∧
    (∀ m n : TreeN, TreeZ.ofN (m * n) = TreeZ.ofN m * TreeZ.ofN n) ∧
    TreeZ.ofN TreeN.zero = 𝟘 ∧ TreeZ.ofN TreeN.one = 𝟙 ∧
    (∀ m n : TreeN, PathLE m n → TreeZ.LE (TreeZ.ofN m) (TreeZ.ofN n)) ∧
    (∀ m n : TreeN, TreeZ.LE (TreeZ.ofN m) (TreeZ.ofN n) → PathLE m n) :=
  ⟨TreeZ.add_assoc', TreeZ.add_comm', TreeZ.zero_add', TreeZ.neg_add_cancel', TreeZ.mul_assoc',
   TreeZ.mul_comm', TreeZ.one_mul', TreeZ.left_distrib', TreeZ.zero_ne_one,
   fun _ _ h => TreeZ.mul_eq_zero h, fun _ _ _ hx h => TreeZ.mul_left_cancel hx h,
   fun a b => em_of_dec (TreeZ.decEq a b), TreeZ.le_refl, fun _ _ _ h1 h2 => TreeZ.le_trans h1 h2,
   fun _ _ h1 h2 => TreeZ.le_antisymm h1 h2, TreeZ.le_total,
   fun a b => em_of_dec (inferInstance : Decidable (TreeZ.LE a b)),
   fun _ _ c h => TreeZ.add_le_add_left c h, fun _ _ _ hc h => TreeZ.mul_le_mul_of_nonneg hc h,
   TreeZ.zero_lt_one, fun _ _ h => TreeZ.ofN_injective h, TreeZ.ofN_add, TreeZ.ofN_mul,
   TreeZ.ofN_zero, TreeZ.ofN_one, fun _ _ h => TreeZ.ofN_le_ofN h,
   fun _ _ h => TreeZ.le_of_ofN_le h⟩

/-- **`TreeQ α` certificate** (unconditional, for every alphabet with two letters): an
Archimedean, decidably and totally ordered field of characteristic zero. -/
theorem treeQ_certificate (α : Type) [TwoLetters α] :
    (∀ a b c : TreeQ α, a + b + c = a + (b + c)) ∧ (∀ a b : TreeQ α, a + b = b + a) ∧
    (∀ a : TreeQ α, 𝟘 + a = a) ∧ (∀ a : TreeQ α, -a + a = 𝟘) ∧
    (∀ a b c : TreeQ α, a * b * c = a * (b * c)) ∧ (∀ a b : TreeQ α, a * b = b * a) ∧
    (∀ a : TreeQ α, 𝟙 * a = a) ∧ (∀ a b c : TreeQ α, a * (b + c) = a * b + a * c) ∧
    (𝟘 : TreeQ α) ≠ 𝟙 ∧
    (∀ a : TreeQ α, a ≠ 𝟘 → a * inv a = 𝟙) ∧ inv (𝟘 : TreeQ α) = 𝟘 ∧
    (∀ n : TreeN, natCast (K := TreeQ α) (succ n) ≠ 𝟘) ∧
    (∀ a b : TreeQ α, a = b ∨ ¬ a = b) ∧
    (∀ a : TreeQ α, a ≤ a) ∧ (∀ a b c : TreeQ α, a ≤ b → b ≤ c → a ≤ c) ∧
    (∀ a b : TreeQ α, a ≤ b → b ≤ a → a = b) ∧ (∀ a b : TreeQ α, a ≤ b ∨ b ≤ a) ∧
    (∀ a b : TreeQ α, a ≤ b ∨ ¬ a ≤ b) ∧
    (∀ a b c : TreeQ α, a ≤ b → c + a ≤ c + b) ∧
    (∀ a b : TreeQ α, 𝟘 ≤ a → 𝟘 ≤ b → 𝟘 ≤ a * b) ∧
    (∀ a b c : TreeQ α, 𝟘 < c → a < b → c * a < c * b) ∧
    (∀ a : TreeQ α, a ≤ natCast (archBound a)) := by
  refine ⟨add_assoc', add_comm', zero_add', neg_add_cancel', mul_assoc', mul_comm', one_mul',
    left_distrib', zero_ne_one', mul_inv_cancel'', inv_zero', charZero', ?_, TOField.le_refl,
    fun _ _ _ h1 h2 => TOField.le_trans h1 h2, fun _ _ h1 h2 => TOField.le_antisymm h1 h2,
    TOField.le_total, fun a b => em_of_dec (TOField.decLE a b),
    fun _ _ c h => TOField.add_le_add_left c h, fun _ _ ha hb => TOField.mul_nonneg ha hb,
    fun _ _ _ hc h => TOField.mul_lt_mul_of_pos_left hc h, le_archBound⟩
  intro a b
  cases TOField.le_total a b with
  | inl h1 =>
    cases em_of_dec (TOField.decLE b a) with
    | inl h2 => exact Or.inl (TOField.le_antisymm h1 h2)
    | inr h2 => exact Or.inr (fun e => h2 (by rw [e]; exact TOField.le_refl b))
  | inr h1 =>
    cases em_of_dec (TOField.decLE a b) with
    | inl h2 => exact Or.inl (TOField.le_antisymm h2 h1)
    | inr h2 => exact Or.inr (fun e => h2 (by rw [e]; exact TOField.le_refl b))

/-- **`TreeRStar` unconditional certificate**: commutative ring with `0 ≠ 1`, constructive
strict order (irreflexive, transitive, cotransitive, tight), compatible with `+` and `·`,
Archimedean, rationally dense; inverses under apartness; cancellation under `≠`. -/
theorem treeR_unconditional_certificate :
    (∀ a b c : TreeRStar, a + b + c = a + (b + c)) ∧ (∀ a b : TreeRStar, a + b = b + a) ∧
    (∀ a : TreeRStar, 𝟘 + a = a) ∧ (∀ a : TreeRStar, -a + a = 𝟘) ∧
    (∀ a b c : TreeRStar, a * b * c = a * (b * c)) ∧ (∀ a b : TreeRStar, a * b = b * a) ∧
    (∀ a : TreeRStar, 𝟙 * a = a) ∧ (∀ a b c : TreeRStar, a * (b + c) = a * b + a * c) ∧
    (𝟘 : TreeRStar) ≠ 𝟙 ∧
    (∀ a : TreeRStar, ¬ a < a) ∧ (∀ a b c : TreeRStar, a < b → b < c → a < c) ∧
    (∀ a b c : TreeRStar, a < b → a < c ∨ c < b) ∧
    (∀ a b : TreeRStar, ¬ RApart a b → a = b) ∧
    (∀ a b : TreeRStar, (a ≤ b → ¬ b < a) ∧ (¬ b < a → a ≤ b)) ∧
    (∀ a b c : TreeRStar, a < b → a + c < b + c) ∧
    (∀ a b : TreeRStar, 𝟘 < a → 𝟘 < b → 𝟘 < a * b) ∧ (𝟘 : TreeRStar) < 𝟙 ∧
    (∀ a : TreeRStar, ∃ n : TreeN, a < natR n) ∧
    (∀ a b : TreeRStar, a < b → ∃ q : QStar, a < ofQ q ∧ ofQ q < b) ∧
    (∀ a : TreeRStar, RApart a 𝟘 → ∃ b, a * b = 𝟙) ∧
    (∀ a b : TreeRStar, a * b = 𝟙 → RApart a 𝟘) ∧
    (∀ a b c : TreeRStar, a ≠ 𝟘 → a * b = a * c → b = c) ∧
    (∀ a b : TreeRStar, a ≠ 𝟘 → a * b = 𝟘 → b = 𝟘) ∧
    (∀ a : TreeRStar, a ≠ 𝟘 → ¬¬ ∃ b, a * b = 𝟙) :=
  ⟨add_assoc', add_comm', zero_add', neg_add_cancel', mul_assoc', mul_comm', one_mul',
   left_distrib', TreeR.zero_ne_one, TreeR.lt_irrefl, fun _ _ _ h1 h2 => TreeR.lt_trans h1 h2,
   fun _ _ c h => lt_cotrans c h, fun _ _ h => eq_of_not_apart h, le_iff_not_lt,
   fun _ _ c h => TreeR.add_lt_add_right c h, fun _ _ ha hb => TreeR.mul_pos ha hb,
   TreeR.zero_lt_one, archimedean, fun _ _ h => exists_rat_between h,
   fun _ h => exists_inv_of_apart h, fun _ _ h => apart_of_mul_eq_one h,
   fun _ _ _ hx h => mul_left_cancel_of_ne hx h, fun _ _ hx h => eq_zero_of_mul_eq_zero_of_ne hx h,
   fun _ hx => not_not_exists_inv hx⟩

/-- **`TreeRStar` conditional certificate**: every textbook law that is not proved
unconditionally appears here with its exact logical strength. -/
theorem treeR_conditional_certificate :
    ((∀ x : TreeRStar, x ≠ 𝟘 → ∃ y, x * y = 𝟙) ↔ MarkovPrinciple) ∧
    (ZeroOrApart QStar ↔ LPO) ∧ (DecidableZero QStar ↔ WLPO) ∧ (Trichotomy QStar ↔ LPO) ∧
    (ZeroOrApart QStar → ZeroProductDisjunction QStar) ∧
    (UnrestrictedCompleteness QStar ↔ CauchyApprox QStar) ∧
    (ChoiceNN → UnrestrictedCompleteness QStar) ∧ (ChoiceNN → ModulusFreeCompleteness QStar) ∧
    (UnrestrictedLUB QStar → WLPO) ∧ (BoundedMonotoneConvergence QStar → LPO) :=
  ⟨inv_iff_markov, zeroOrApart_iff_lpo, decidableZero_iff_wlpo, trichotomy_iff_lpo,
   zeroProduct_of_zeroOrApart, ⟨cauchyApprox_of_complete, complete_of_cauchyApprox⟩,
   complete_of_choice, modulusFreeComplete_of_choice, wlpo_of_unrestrictedLUB, lpo_of_bmc⟩

/-- **Unconditional convergence results** for `TreeRStar`: the rational embedding is dense in the
sense that every class is the limit of its rational terms; limits are unique; tracked families
(modulus + approximants) converge and are closed under `+`, `-`, `·`; convergence is closed
under `+`, `-`, `·`; real Cauchy sequences of rationals with a modulus converge. -/
theorem treeR_convergence_certificate :
    (∀ c : CSeq QStar, ConvergesTo (fun n => ofQ (c.seq n)) (mkR c)) ∧
    (∀ (f : TreeN → TreeRStar) (L L' : TreeRStar), ConvergesTo f L → ConvergesTo f L' → L = L') ∧
    (∀ (f : TreeN → TreeRStar) (T : Tracked f), ConvergesTo f T.lim) ∧
    (∀ (f g : TreeN → TreeRStar) (L L' : TreeRStar), ConvergesTo f L → ConvergesTo g L' →
      ConvergesTo (fun i => f i * g i) (L * L')) ∧
    (∀ (f g : TreeN → TreeRStar) (T : Tracked f) (S : Tracked g),
      (T.mul S).lim = T.lim * S.lim ∧ (T.add S).lim = T.lim + S.lim ∧ T.neg.lim = -T.lim) ∧
    (∀ (s : TreeN → QStar) (ν : TreeN → TreeN), RCauchyMod (fun i => ofQ (s i)) ν →
      ∃ L, ConvergesTo (fun i => ofQ (s i)) L) :=
  ⟨ofQ_seq_converges, fun _ _ _ h h' => limit_unique h h', fun _ T => T.converges,
   fun _ _ _ _ hf hg => converges_mul hf hg,
   fun _ _ T S => ⟨Tracked.lim_mul T S, Tracked.lim_add T S, Tracked.lim_neg T⟩,
   fun s ν h => ⟨_, ofQ_seq_converges ⟨s, ν, isModulus_of_rcauchyMod_ofQ h⟩⟩⟩

end Task04

end
