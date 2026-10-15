module

public import DimensionFoundation.OmegaFiniteSupport

@[expose] public section

/-!
# Longitudinal limitations at omega arity

What is proved here:

* the infinite all-ones function `TreeN → K` does **not** have finite support;
* no finitely supported omega function restricts to the uniform vector `u_b` on every finite
  arity;
* the finite uniform lines `L_b` are **not** preserved by the zero-padding inclusion
  `F_b → F_{succ b}`: the padding of `u_b` is never in `L_{succ b}` (for positive `b`).

What is *not* claimed: there is no canonical omega-dimensional longitudinal line in the
finitely supported space and no limiting longitudinal vector along rays; producing one would
require an additional transport/limit structure, which is not part of this project (a
possible extension only).
-/

open CSR CRing TField FinSum ChildModule OmegaModule
open TreeN (PathLT PathLE succ)

namespace Longitudinal

variable {K : Type} [TField K]

/-- The infinite all-ones function. -/
def allOnes : FO K := fun _ => 𝟙

/-- The all-ones function has no finite support. -/
theorem allOnes_not_finSupp : ¬ FinSupp (allOnes (K := K)) := by
  intro ⟨B, hB⟩
  exact zero_ne_one (hB B (TreeN.le_refl B)).symm

/-- No finitely supported omega function restricts to `u_b` on every finite arity. -/
theorem no_finSupp_uniform_limit :
    ¬ ∃ f : FO K, FinSupp f ∧ ∀ b k : TreeN, PathLT k b → f k = 𝟙 := by
  intro ⟨f, ⟨B, hB⟩, hu⟩
  have e1 := hB B (TreeN.le_refl B)
  have e2 := hu (succ B) B (TreeN.lt_succ_self B)
  rw [e1] at e2
  exact zero_ne_one e2

/-- Zero padding does not preserve the uniform lines: for positive `b`, the zero padding of
`u_b` is not in `L_{succ b}`. -/
theorem padSucc_u_not_inL {b : TreeN} (hb : PathLT TreeN.zero b) :
    ¬ ChildModule.InL (padSucc (u K b)) := by
  intro ⟨a, ha⟩
  have e0 := congrFun ha ⟨TreeN.zero, TreeN.lt_trans hb (TreeN.lt_succ_self b)⟩
  have eb := congrFun ha ⟨b, TreeN.lt_succ_self b⟩
  have h0 : padSucc (u K b) ⟨TreeN.zero, TreeN.lt_trans hb (TreeN.lt_succ_self b)⟩ = 𝟙 :=
    pad_lt (u K b) hb
  have hb' : padSucc (u K b) ⟨b, TreeN.lt_succ_self b⟩ = 𝟘 :=
    pad_ge (u K b) (TreeN.lt_irrefl b)
  rw [h0] at e0
  rw [hb'] at eb
  have ea : a = 𝟙 := by
    have : 𝟙 = a * 𝟙 := e0
    rw [mul_one] at this
    exact this.symm
  have ez : a = 𝟘 := by
    have : 𝟘 = a * 𝟙 := eb
    rw [mul_one] at this
    exact this.symm
  exact zero_ne_one (ez.symm.trans ea)

end Longitudinal
end
