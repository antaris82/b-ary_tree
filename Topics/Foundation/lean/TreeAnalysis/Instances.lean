module

public import TreeAnalysis.ArityCompletionTransfer

@[expose] public section

/-!
# The completion over the fixed base `Q★ = TreeQOmega`, embeddings, and field status

* `TreeRStar := TreeR QStar`: the completion of the omega-branching triple-path rationals.
* Embedding chain `TreeN → TreeZ → Q★ → TreeR`, each map injective and compatible with the
  operations (`ofZR_injective`, `ofZR_add`, `ofZR_mul`, `natR_injective`, ...).
* Field status: inverses exist for **apartness witnesses** (`TreeR.mul_rinv`); the conventional
  form `x ≠ 0 → ∃ y, x·y = 1` is proved **only under** the explicit Markov-type premise
  `NeImpliesApart K` (`exists_inv_of_ne_of_markov`).  Without it, only `x ≠ 0 → ¬¬ RApart x 0`
  is proved.
-/

open CSR CRing TreeZ TOField TreeR TreeQ

/-- The completion over `Q★`. -/
abbrev TreeRStar : Type := TreeR QStar

example : CRing TreeRStar := inferInstance

/-- Embedding of tree integers into the completion. -/
def ofZR (z : TreeZ) : TreeRStar := ofQ (ofZ z)

theorem ofZR_injective {z z' : TreeZ} (h : ofZR z = ofZR z') : z = z' :=
  ofZ_injective (ofQ_injective h)

theorem ofZR_add (z z' : TreeZ) : ofZR (z + z') = ofZR z + ofZR z' := by
  unfold ofZR
  rw [ofZ_add, ofQ_add]

theorem ofZR_mul (z z' : TreeZ) : ofZR (z * z') = ofZR z * ofZR z' := by
  unfold ofZR
  rw [ofZ_mul, ofQ_mul]

/-- The path counts enter through `TreeZ`: `natR n = ofZR (ofN n)`. -/
theorem natR_eq_ofZR (n : TreeN) : natR (K := QStar) n = ofZR (ofN n) := by
  unfold natR ofZR
  rw [natCast_eq_ofZ]

/-- The composite `TreeN → TreeZ → Q★ → TreeR` is injective. -/
theorem treeN_embedding_injective {m n : TreeN} (h : ofZR (ofN m) = ofZR (ofN n)) : m = n :=
  ofN_injective (ofZR_injective h)

/-- Mere inequality to zero together with the Markov-type principle below. -/
def NeImpliesApart (K : Type) [TOField K] : Prop := ∀ x : TreeR K, x ≠ 𝟘 → RApart x 𝟘

/-- **Conditional conventional inverse**: under `NeImpliesApart K`. -/
theorem exists_inv_of_ne_of_markov {K : Type} [TOField K] (hM : NeImpliesApart K)
    {x : TreeR K} (hx : x ≠ 𝟘) : ∃ y, x * y = 𝟙 :=
  exists_inv_of_apart (hM x hx)

/-- Conversely, the conventional inverse property implies `NeImpliesApart K`; so the two are
equivalent and the conventional field axiom is exactly as strong as this principle. -/
theorem markov_of_inv {K : Type} [TOField K]
    (h : ∀ x : TreeR K, x ≠ 𝟘 → ∃ y, x * y = 𝟙) : NeImpliesApart K := fun x hx => by
  obtain ⟨y, hy⟩ := h x hx
  exact apart_of_mul_eq_one hy

end
