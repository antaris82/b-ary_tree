module

public import TreeAnalysis.CompletenessStrength

@[expose] public section

/-!
# Task 03, Checkpoint F — extension of uniformly continuous rational maps

* `UCMod f ω`: `ω : TreeN → TreeN` is a **function-valued** precision modulus of uniform
  continuity for `f : K → K` (`|x - y| ≤ eps (ω k) → |f x - f y| ≤ eps k`);
* `mapSeqUC`: termwise application to Cauchy data, with the explicit modulus `k ↦ c.mod (ω k)`;
* `mapSeqUC_resp`: Cauchy-equivalent inputs give Cauchy-equivalent outputs;
* `extendR`: the induced map on `TreeR K` (lifted through the quotient; independent of
  representatives by construction);
* `extendR_ofQ`: compatibility with the constant-sequence embedding;
* `RatSeqContinuous F`: `F` maps the rational approximants of every representative to a
  sequence converging to `F` of its class;
* `extendR_ratSeqContinuous` and `extendR_unique`: `extendR f` is the **unique**
  `RatSeqContinuous` map extending `f` along `ofQ` (uniqueness uses rational density in the form
  `ofQ_seq_converges` and uniqueness of limits);
* `extendR_comp`: extensions compose; `extendR_neg`: the extension of rational negation is real
  negation.

This is a uniqueness/extension statement for maps `K → K` only; no universal property of the
completion with respect to arbitrary complete spaces is claimed.
-/

open CSR CRing
open TreeN (PathLE PathLT succ maxN)

namespace TreeR

open TField TOField

variable {K : Type} [TOField K]

/-- `ω` is a uniform-continuity modulus for `f` at the precisions `eps k`. -/
def UCMod (f : K → K) (ω : TreeN → TreeN) : Prop :=
  ∀ k x y, abs (x + -y) ≤ eps (ω k) → abs (f x + -f y) ≤ eps k

/-- Termwise application of a uniformly continuous map to Cauchy data. -/
def mapSeqUC (f : K → K) (ω : TreeN → TreeN) (h : UCMod f ω) (c : CSeq K) : CSeq K :=
  ⟨fun n => f (c.seq n), fun k => c.mod (ω k), fun k m n hm hn => h k _ _ (c.isMod (ω k) m n hm hn)⟩

theorem mapSeqUC_resp (f : K → K) (ω : TreeN → TreeN) (h : UCMod f ω) {c d : CSeq K}
    (hcd : SeqEquiv c.seq d.seq) : SeqEquiv (mapSeqUC f ω h c).seq (mapSeqUC f ω h d).seq := by
  intro k
  obtain ⟨N, hN⟩ := hcd (ω k)
  exact ⟨N, fun n hn => h k _ _ (hN n hn)⟩

/-- The induced map on the completion. -/
def extendR (f : K → K) (ω : TreeN → TreeN) (h : UCMod f ω) : TreeR K → TreeR K :=
  lift1 (mapSeqUC f ω h) (fun _ _ hcd => mapSeqUC_resp f ω h hcd)

theorem extendR_mk (f : K → K) (ω : TreeN → TreeN) (h : UCMod f ω) (c : CSeq K) :
    extendR f ω h (mkR c) = mkR (mapSeqUC f ω h c) := rfl

/-- Independence of representatives, stated explicitly. -/
theorem extendR_indep (f : K → K) (ω : TreeN → TreeN) (h : UCMod f ω) {c d : CSeq K}
    (hcd : mkR c = mkR d) : mkR (mapSeqUC f ω h c) = mkR (mapSeqUC f ω h d) := by
  rw [← extendR_mk, ← extendR_mk, hcd]

/-- Compatibility with the rational embedding. -/
theorem extendR_ofQ (f : K → K) (ω : TreeN → TreeN) (h : UCMod f ω) (q : K) :
    extendR f ω h (ofQ q) = ofQ (f q) :=
  mkR_sound (seqEquiv_of_eq (fun _ => rfl))

/-- Continuity along rational approximants of representatives. -/
def RatSeqContinuous (F : TreeR K → TreeR K) : Prop :=
  ∀ c : CSeq K, ConvergesTo (fun n => F (ofQ (c.seq n))) (F (mkR c))

theorem extendR_ratSeqContinuous (f : K → K) (ω : TreeN → TreeN) (h : UCMod f ω) :
    RatSeqContinuous (extendR f ω h) := by
  intro c
  have e : (fun n => extendR f ω h (ofQ (c.seq n))) = fun n => ofQ ((mapSeqUC f ω h c).seq n) :=
    funext (fun n => extendR_ofQ f ω h (c.seq n))
  rw [e, extendR_mk]
  exact ofQ_seq_converges _

/-- Two `RatSeqContinuous` maps agreeing on the rationals agree everywhere. -/
theorem eq_of_ratSeqContinuous {F G : TreeR K → TreeR K} (hF : RatSeqContinuous F)
    (hG : RatSeqContinuous G) (h : ∀ q, F (ofQ q) = G (ofQ q)) : F = G := by
  funext x
  induction x using ind_mkR with
  | h c =>
    have e : (fun n => F (ofQ (c.seq n))) = fun n => G (ofQ (c.seq n)) :=
      funext (fun n => h (c.seq n))
    have hF' := hF c
    rw [e] at hF'
    exact limit_unique hF' (hG c)

/-- **Uniqueness of the extension.** -/
theorem extendR_unique (f : K → K) (ω : TreeN → TreeN) (h : UCMod f ω)
    {F : TreeR K → TreeR K} (hF : RatSeqContinuous F) (hext : ∀ q, F (ofQ q) = ofQ (f q)) :
    F = extendR f ω h :=
  eq_of_ratSeqContinuous hF (extendR_ratSeqContinuous f ω h)
    (fun q => by rw [hext, extendR_ofQ])

/-- The extension does not depend on the chosen modulus. -/
theorem extendR_modulus_indep (f : K → K) (ω ω' : TreeN → TreeN) (h : UCMod f ω)
    (h' : UCMod f ω') : extendR f ω h = extendR f ω' h' :=
  extendR_unique f ω' h' (extendR_ratSeqContinuous f ω h) (extendR_ofQ f ω h)

/-- Composition of uniformly continuous maps. -/
theorem ucMod_comp {f g : K → K} {ω ω' : TreeN → TreeN} (hf : UCMod f ω) (hg : UCMod g ω') :
    UCMod (fun x => g (f x)) (fun k => ω (ω' k)) :=
  fun k x y hxy => hg k _ _ (hf (ω' k) x y hxy)

/-- Extensions compose. -/
theorem extendR_comp {f g : K → K} {ω ω' : TreeN → TreeN} (hf : UCMod f ω) (hg : UCMod g ω')
    (x : TreeR K) :
    extendR (fun y => g (f y)) (fun k => ω (ω' k)) (ucMod_comp hf hg) x =
      extendR g ω' hg (extendR f ω hf x) := by
  induction x using ind_mkR with
  | h c => rfl

/-- Rational negation has the modulus `id`. -/
theorem ucMod_neg : UCMod (fun x : K => -x) (fun k => k) := fun k x y hxy => by
  show abs (-x + - -y) ≤ eps k
  rw [← neg_add, abs_neg]
  exact hxy

/-- The extension of rational negation is real negation. -/
theorem extendR_neg (x : TreeR K) : extendR (fun y : K => -y) (fun k => k) ucMod_neg x = -x := by
  induction x using ind_mkR with
  | h c => rfl

end TreeR
end
