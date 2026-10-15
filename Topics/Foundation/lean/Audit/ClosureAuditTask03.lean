import Lean
import TreeAnalysis

/-! Task 03 effective-closure audit.

For each central Task 03 result, the transitive closure of all constants occurring in the types
and values of its dependencies is computed.  The audit reports
* every constant of the closure whose name contains a `Classical` component,
* every axiom of the closure,
* every closure constant whose root namespace is a built-in number type
  (`Nat`, `Int`, `Rat`, `Fin`, `UInt8/16/32/64`, `USize`, `BitVec`, `Real`, `PNat`).
The only direct users of built-in number constants found are Lean's automatically generated
constructor-index helpers (`List.ctorIdx`, `Bool.ctorIdx`, `noConfusion_of_Nat`), which the kernel-level
`injection`/`cases`/`nomatch` machinery uses for every inductive type in Lean 4.28; no project
declaration mentions them.
Raw output: `Audit/closure_task03.txt`. -/

open Lean Elab Command

def closureOf (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let cs := ci.type.getUsedConstants ++ (match ci.value? with
          | some v => v.getUsedConstants
          | none => #[])
        for c in cs do
          if !seen.contains c then todo := c :: todo
  return seen

def numRoots : List Name :=
  [`Nat, `Int, `Rat, `Fin, `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec, `Real, `PNat]

elab "#closure_audit " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    let n := id.getId
    let cl := closureOf env [n]
    let classical := cl.toList.filter (fun c => c.components.any (· == `Classical))
    let axs := cl.toList.filter (fun c => match env.find? c with
      | some (ConstantInfo.axiomInfo _) => true
      | _ => false)
    let nums := cl.toList.filter (fun c => numRoots.contains c.getRoot)
    let users := cl.toList.filter (fun c => !numRoots.contains c.getRoot && (match env.find? c with
      | some ci => (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])).any
          (fun d => numRoots.contains d.getRoot)
      | none => false))
    logInfo m!"{n}: closure size {cl.size}; Classical constants: {classical}; axioms: {axs}; \
      built-in number constants: {nums.length} {nums}; \
      closure constants outside those namespaces that mention them directly: {users}"

#closure_audit TreeR.complete_iff_cauchyApprox TreeR.complete_of_choice
  TreeR.modulusFreeComplete_of_choice TreeR.limit_of_approx TreeR.regular_close
  TreeR.neImpliesApart_iff_markov TreeR.zeroOrApart_iff_lpo TreeR.eq_zero_of_mul_eq_zero_of_ne
  TreeR.SupData.isLUB TreeR.SupData.ofList_isLUB TreeR.wlpo_of_unrestrictedLUB TreeR.lpo_of_bmc
  PrimitiveScope.prefixCount_not_isCauchy PrimitiveScope.prefixCount_indep
  Ray.encode_letter_choice_dependence TreeR.extendR_unique
