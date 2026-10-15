module

public import DimensionFoundation.FiniteSums

@[expose] public section

/-!
# The finite child-direction module `F_b := Child b → K`

`K` is any of the internally constructed rational fields (`TreeQb b` for `b ≥ 2`, or
`TreeQOmega`, which by `finiteOmegaIso` is isomorphic to every `TreeQb b`).  Allowing
`TreeQOmega` covers the arity `b = one`, where triple paths over a one-letter alphabet do
not support the field operations.  The field interface is populated only by `TreeQ`.

Zero, addition, negation and scalar multiplication are pointwise; the module laws follow
from the internal field laws.  Equality of vectors uses function extensionality (derived in
Lean's kernel from quotient soundness).
-/

open CSR CRing TField FinSum

namespace ChildModule

variable {K : Type} [TField K] {b : TreeN}

/-- The finite child-direction module. -/
abbrev F (K : Type) (b : TreeN) : Type := Child b → K

def zeroV : F K b := fun _ => 𝟘
def addV (x y : F K b) : F K b := fun i => x i + y i
def negV (x : F K b) : F K b := fun i => -x i
def smul (a : K) (x : F K b) : F K b := fun i => a * x i

/-! ## Module laws -/

theorem addV_assoc (x y z : F K b) : addV (addV x y) z = addV x (addV y z) :=
  funext fun i => add_assoc (x i) (y i) (z i)

theorem addV_comm (x y : F K b) : addV x y = addV y x := funext fun i => add_comm (x i) (y i)

theorem zero_addV (x : F K b) : addV zeroV x = x := funext fun i => zero_add (x i)

theorem negV_addV (x : F K b) : addV (negV x) x = zeroV := funext fun i => neg_add_cancel (x i)

theorem smul_addV (a : K) (x y : F K b) : smul a (addV x y) = addV (smul a x) (smul a y) :=
  funext fun i => left_distrib a (x i) (y i)

theorem add_smul (a c : K) (x : F K b) : smul (a + c) x = addV (smul a x) (smul c x) :=
  funext fun i => right_distrib a c (x i)

theorem mul_smul (a c : K) (x : F K b) : smul (a * c) x = smul a (smul c x) :=
  funext fun i => mul_assoc a c (x i)

theorem one_smul (x : F K b) : smul 𝟙 x = x := funext fun i => one_mul (x i)

/-! ## Coordinate sum, uniform vector, longitudinal line, transverse space, dot product -/

/-- Sum of all coordinates (explicit recursive enumeration of `Child b`). -/
def coordSum (x : F K b) : K := sumC b x

/-- The uniform child vector `u_b(i) := 1`. -/
def u (K : Type) [TField K] (b : TreeN) : F K b := fun _ => 𝟙

/-- The longitudinal line `L_b := {c · u_b}`. -/
def InL (x : F K b) : Prop := ∃ c : K, x = smul c (u K b)

/-- The transverse space `S_b := {x | Σ_i x(i) = 0}`. -/
def InS (x : F K b) : Prop := coordSum x = 𝟘

/-- The dot product `dot(x, y) := Σ_i x(i)·y(i)`. -/
def dot (x y : F K b) : K := sumC b (fun i => x i * y i)

/-- Unit coordinate vectors `e_j`. -/
def e (j : Child b) : F K b := delta j 𝟙

theorem coordSum_addV (x y : F K b) : coordSum (addV x y) = coordSum x + coordSum y :=
  sumC_add b x y

theorem coordSum_smul (a : K) (x : F K b) : coordSum (smul a x) = a * coordSum x :=
  sumC_mul_left b a x

theorem coordSum_negV (x : F K b) : coordSum (negV x) = -coordSum x := sumC_neg b x

theorem coordSum_u : coordSum (u K b) = natCast b := sumC_one b

theorem coordSum_e (j : Child b) : coordSum (e (K := K) j) = 𝟙 := sumC_delta b j 𝟙

theorem inS_zero : InS (zeroV : F K b) := sumC_zero b

theorem inS_addV {x y : F K b} (hx : InS x) (hy : InS y) : InS (addV x y) := by
  unfold InS at *
  rw [coordSum_addV, hx, hy, add_zero]

theorem inS_smul (a : K) {x : F K b} (hx : InS x) : InS (smul a x) := by
  unfold InS at *
  rw [coordSum_smul, hx, mul_zero]

theorem inL_u : InL (u K b) := ⟨𝟙, (one_smul _).symm⟩

theorem inL_smul (a : K) {x : F K b} (hx : InL x) : InL (smul a x) := by
  obtain ⟨c, hc⟩ := hx
  exact ⟨a * c, by rw [hc, mul_smul]⟩

theorem inL_addV {x y : F K b} (hx : InL x) (hy : InL y) : InL (addV x y) := by
  obtain ⟨c, hc⟩ := hx
  obtain ⟨d, hd⟩ := hy
  exact ⟨c + d, by rw [hc, hd, add_smul]⟩

/-- `dot(u_b, x) = 0` for every transverse `x`. -/
theorem dot_u_of_inS {x : F K b} (hx : InS x) : dot (u K b) x = 𝟘 := by
  unfold dot
  exact (sumC_congr (fun i => one_mul (x i))).trans hx

theorem dot_comm (x y : F K b) : dot x y = dot y x := sumC_congr fun i => mul_comm (x i) (y i)

end ChildModule
end
