import Lean

/-!
# Fail-closed audit command

`#fail_closed_audit` inspects **every** constant of the environment that belongs to the project,
i.e. every constant whose defining module has one of the project roots below as its first name
component, together with every constant declared in the file that invokes the command (this
makes negative fixtures auditable).  It raises an elaboration **error** (so `lean`/`lake` exit
with a nonzero status) if any of the following holds:

1. **Axioms.** The transitive kernel-axiom closure (`Lean.collectAxioms`) of a constant contains
   anything other than `propext` and `Quot.sound` (e.g. `Classical.choice`, `sorryAx`,
   `Lean.ofReduceBool`, `Lean.trustCompiler`, or any user axiom).
2. **Declaration kinds.** A project constant is itself an `axiom`, is `unsafe`, is an `opaque`
   constant (this is how `partial` definitions are compiled), or carries `@[implemented_by]`.
3. **Classical constants.** A project constant directly mentions a constant with a `Classical`
   name component in its type or value.
4. **Number carriers.** A *handwritten* project constant directly mentions a constant of a
   built-in number namespace (`Nat`, `Int`, `Rat`, `Fin`, `UInt*`, `USize`, `BitVec`, `Real`,
   `PNat`, `Float`) or the numeric literal classes `OfNat`/`OfScientific`, in its type or value.
5. **Coverage.** Fewer than `minProjectModules` project modules are loaded (guards against an
   audit that silently imports nothing).

**Generated constants.** Lean 4.28 generates, for every inductive type and structure, auxiliary
constants (`ctorIdx`, `noConfusionType`, `noConfusion`, `_sizeOf_*`, `sizeOf_spec`, `SizeOf`
instances, `injEq`, …).  Some of them mention the built-in `Nat` because the kernel's constructor
index and `SizeOf` machinery is stated in `Nat`.  These constants are still subject to checks 1–3,
but are exempt from check 4.  A constant counts as generated when it is recognized by Lean as an
auxiliary recursor or no-confusion constant, or when its last name component is one of the fixed
list `genSuffixes` or starts with `_sizeOf`/`instSizeOf`.
Likewise, `notation`/`syntax` declarations compile to parser descriptions, macro rules and
unexpanders (types `Lean.ParserDescr`, `Lean.Macro`, `Lean.PrettyPrinter.Unexpander`) that use
`Nat` literals for precedences; they are exempt from check 4 only.  Abstracted proofs
(`_proof_n`) and matchers (`match_n`) of handwritten declarations are **not** exempt.
Every exemption is counted and reported in the success message.

The metaprogram itself uses Lean's `Nat`, `String`, `Array` etc. as bookkeeping; this never enters
the audited declarations (the audit files declare no mathematical constants).
-/

open Lean Elab Command

namespace ReleaseAudit

/-- First name components of the project's mathematical modules. -/
def projectRoots : List Name :=
  [`PrimitiveTree, `TreeNumbers, `TreeFoundation, `DimensionFoundation, `TreeFoundations,
   `TreeAnalysis, `BoundaryTopology]

/-- The only permitted kernel axioms. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound]

/-- Built-in number namespaces and numeric-literal classes. -/
def numberRoots : List Name :=
  [`Nat, `Int, `Rat, `Fin, `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec, `Real, `PNat,
   `Float, `OfNat, `OfScientific]

/-- Last name components of constants generated automatically for inductive types. -/
def genSuffixes : List String :=
  ["ctorIdx", "toCtorIdx", "noConfusionType", "noConfusion", "sizeOf_spec", "injEq", "inj",
   "below", "brecOn", "binductionOn", "ibelow", "casesOn", "recOn", "rec", "ctorElim",
   "ctorElimType", "noConfusion_of_Nat"]

def isProjectModule (m : Name) : Bool := projectRoots.contains m.getRoot

def sizeOfLike (s : String) : Bool := s.startsWith "_sizeOf" || s.startsWith "instSizeOf"

def isGenerated (env : Environment) (n : Name) : Bool :=
  isAuxRecursor env n || isNoConfusion env n ||
  (match n with
   | .str _ s => genSuffixes.contains s || sizeOfLike s
   | _ => false)

/-- Syntax declarations (`notation`, `syntax`) compile to parser descriptions, macro rules and
unexpanders whose precedence levels and syntax positions are built-in `Nat` literals; they are
metaprogram data, not mathematical constants. -/
def isSyntaxDecl (ci : ConstantInfo) : Bool :=
  ci.type.isConstOf ``Lean.ParserDescr || ci.type.isConstOf ``Lean.TrailingParserDescr ||
  ci.type.isConstOf ``Lean.Macro || ci.type.isConstOf ``Lean.PrettyPrinter.Unexpander

def usedConstants (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[])

/-- Is `n` subject to the audit? -/
def inScope (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => isProjectModule m
    | none => false
  | none => true  -- declared in the invoking file

/-- Minimum number of loaded project modules for the release audit (`#fail_closed_audit`). -/
def minProjectModules : Nat := 60

def runAudit (minModules : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let mods := env.header.moduleNames.filter isProjectModule
  let mut failures : Array MessageData := #[]
  if mods.size < minModules then
    failures := failures.push
      m!"only {mods.size} project modules loaded; expected at least {minModules}"
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if inScope env n then names := names.push n
  let mut generated : Nat := 0
  let mut syntaxDecls : Array Name := #[]
  let mut withPropext : Nat := 0
  let mut withQuot : Nat := 0
  let mut axiomFree : Nat := 0
  for n in names do
    let some ci := env.find? n | continue
    -- 1. axiom closure
    let axs ← liftCoreM (collectAxioms n)
    let bad := axs.filter (fun a => !allowedAxioms.contains a)
    if !bad.isEmpty then
      failures := failures.push m!"{n}: forbidden axioms {bad}"
    if axs.isEmpty then axiomFree := axiomFree + 1
    if axs.contains ``propext then withPropext := withPropext + 1
    if axs.contains ``Quot.sound then withQuot := withQuot + 1
    -- 2. declaration kinds
    match ci with
    | .axiomInfo _ => failures := failures.push m!"{n}: is an axiom declaration"
    | .opaqueInfo _ => failures := failures.push m!"{n}: is an opaque (e.g. partial) constant"
    | _ => pure ()
    if ci.isUnsafe then failures := failures.push m!"{n}: is unsafe"
    if (Compiler.implementedByAttr.getParam? env n).isSome then
      failures := failures.push m!"{n}: carries @[implemented_by]"
    -- 3. classical constants
    let used := usedConstants ci
    let cls := used.filter (fun c => c.components.contains `Classical)
    if !cls.isEmpty then
      failures := failures.push m!"{n}: mentions classical constants {cls}"
    -- 4. number carriers (handwritten constants only)
    if isGenerated env n then
      generated := generated + 1
    else if isSyntaxDecl ci then
      syntaxDecls := syntaxDecls.push n
    else
      let nums := used.filter (fun c => numberRoots.contains c.getRoot)
      if !nums.isEmpty then
        failures := failures.push m!"{n}: mentions built-in number constants {nums}"
  if !failures.isEmpty then
    throwError (m!"FAIL-CLOSED AUDIT FAILED: {failures.size} violation(s)\n" ++
      MessageData.joinSep failures.toList "\n")
  logInfo m!"fail-closed audit passed: {mods.size} project modules, {names.size} constants \
    audited ({generated} generated constants and {syntaxDecls.size} syntax declarations {syntaxDecls} \
    exempt from the number-carrier check only); \
    axiom-free: {axiomFree}, using propext: {withPropext}, using Quot.sound: {withQuot}; \
    no axiom outside [propext, Quot.sound]"

/-- The release audit: all project modules must be loaded. -/
elab "#fail_closed_audit" : command => runAudit minProjectModules

/-- The same checks without the module-coverage requirement (used by negative fixtures, which
audit only their own declarations). -/
elab "#fail_closed_audit_local" : command => runAudit 0

/-- Fail unless every listed constant exists (guards the release against silent deletion or
renaming of the central results).  Names are taken literally, without namespace resolution. -/
elab "#require_decls " ids:ident* : command => do
  let env ← getEnv
  let missing := ids.filter (fun id => !env.contains id.getId)
  if !missing.isEmpty then
    throwError m!"FAIL-CLOSED AUDIT FAILED: missing required declarations {missing.map (·.getId)}"
  logInfo m!"all {ids.size} required declarations present"

/-- Reporting helper (not a check): print the kernel-axiom closure of each listed constant, one
line per constant.  Enforcement is done by `#fail_closed_audit`, not by this command. -/
elab "#axiom_report " ids:ident* : command => do
  let mut lines : Array MessageData := #[]
  for id in ids do
    let n := id.getId
    unless (← getEnv).contains n do
      throwError m!"unknown declaration {n}"
    let axs ← liftCoreM (collectAxioms n)
    lines := lines.push m!"{n}: {axs}"
  logInfo (MessageData.joinSep lines.toList "\n")

end ReleaseAudit
