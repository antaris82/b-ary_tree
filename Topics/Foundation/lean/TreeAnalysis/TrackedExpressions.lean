module

public import TreeAnalysis.ApproxClosure

@[expose] public section

/-!
# Recursively composed tracked approximations (bounded continuation of Task 04, E2)

The closure operations `Tracked.add`, `Tracked.neg`, `Tracked.mul` and `Tracked.constQ` are
combined along an arbitrary finite expression tree.  An expression over atoms indexed by any
type `ι` is built from rational constants, atoms, `+`, `-` and `·`.  Given, for every atom `j`,
a real sequence `fs j` **together with** tracking data `Ts j : Tracked (fs j)`, the composite
sequence receives explicit tracking data by structural recursion on the expression, and its limit
is the same expression evaluated at the limits of the atoms.

This is the only additional statement obtained from the existing closure lemmas; it uses no
choice principle (all tracking data are supplied), and it is a routine structural consequence of
`Tracked.lim_add`, `lim_neg`, `lim_mul`, `lim_constQ`, not a new completeness property.
-/

open CSR CRing TOField TField

namespace TreeR

variable {K : Type} [TOField K]

/-- Finite expressions over atoms of type `ι` and rational constants. -/
inductive TExpr (K : Type) (ι : Type) : Type where
  | const : K → TExpr K ι
  | atom : ι → TExpr K ι
  | add : TExpr K ι → TExpr K ι → TExpr K ι
  | neg : TExpr K ι → TExpr K ι
  | mul : TExpr K ι → TExpr K ι → TExpr K ι

namespace TExpr

variable {ι : Type}

/-- Evaluation of an expression on real values of the atoms. -/
def eval (v : ι → TreeR K) : TExpr K ι → TreeR K
  | const c => ofQ c
  | atom j => v j
  | add a b => eval v a + eval v b
  | neg a => -eval v a
  | mul a b => eval v a * eval v b

/-- Termwise evaluation on real sequences of the atoms. -/
def evalSeq (fs : ι → TreeN → TreeR K) : TExpr K ι → TreeN → TreeR K
  | const c => fun _ => ofQ c
  | atom j => fs j
  | add a b => fun i => evalSeq fs a i + evalSeq fs b i
  | neg a => fun i => -evalSeq fs a i
  | mul a b => fun i => evalSeq fs a i * evalSeq fs b i

/-- Explicit tracking data for the composite sequence, by structural recursion. -/
def tracked (fs : ι → TreeN → TreeR K) (Ts : ∀ j, Tracked (fs j)) :
    (e : TExpr K ι) → Tracked (evalSeq fs e)
  | const c => Tracked.constQ c
  | atom j => Ts j
  | add a b => (tracked fs Ts a).add (tracked fs Ts b)
  | neg a => (tracked fs Ts a).neg
  | mul a b => (tracked fs Ts a).mul (tracked fs Ts b)

/-- **The limit of a recursively composed tracked family is the composite of the limits.** -/
theorem lim_tracked (fs : ι → TreeN → TreeR K) (Ts : ∀ j, Tracked (fs j)) (e : TExpr K ι) :
    (tracked fs Ts e).lim = eval (fun j => (Ts j).lim) e := by
  induction e with
  | const c => exact Tracked.lim_constQ c
  | atom j => rfl
  | add a b iha ihb =>
    show ((tracked fs Ts a).add (tracked fs Ts b)).lim = _
    rw [Tracked.lim_add, iha, ihb]
    rfl
  | neg a iha =>
    show (tracked fs Ts a).neg.lim = _
    rw [Tracked.lim_neg, iha]
    rfl
  | mul a b iha ihb =>
    show ((tracked fs Ts a).mul (tracked fs Ts b)).lim = _
    rw [Tracked.lim_mul, iha, ihb]
    rfl

/-- Consequently the composite sequence converges to the composite of the limits. -/
theorem converges_evalSeq (fs : ι → TreeN → TreeR K) (Ts : ∀ j, Tracked (fs j))
    (e : TExpr K ι) : ConvergesTo (evalSeq fs e) (eval (fun j => (Ts j).lim) e) := by
  rw [← lim_tracked fs Ts e]
  exact (tracked fs Ts e).converges

end TExpr

end TreeR

end
