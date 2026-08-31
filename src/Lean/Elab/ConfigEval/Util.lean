/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.Elab.Command

public section

namespace Lean.Elab.ConfigEval

open Meta Term Command

/--
Creates a decision tree to implement `match discr with $cases* | _ => onFail`,
where `discr : String`.
-/
partial def makeStringMatcher (discr : Ident) (cases : Array (String × Term)) (onFail : Term) :
    TermElabM Term := do
  let cases := Array.qsort cases (fun c c' => c.1 < c'.1)
  build 0 cases.size cases
where
  build (start stop : Nat) (cases : Array (String × Term)) : TermElabM Term := do
    if stop - start ≤ 5 then
      -- Switch to if/else chains once we get to a small number of options.
      cases[start:stop].foldrM (init := onFail) fun (s, body) res =>
        `(if $discr == $(quote s) then $body else $res)
    else
      let mid := (start + stop) / 2
      let (s, _) := cases[mid]!
      let low ← build start mid cases
      let high ← build mid stop cases
      `(if $discr < $(quote s) then $low else $high)

/--
Returns a list of types that are are missing `cls` instances such that
implementing them would ensure a `cls type` instance. If there are no conditional
instances to support this, returns `#[type]`. If there's already a `cls type` instance,
returns `#[]`.

Only supports one-parameter classes.

For example, `planDerivation C t` where `t` is `Array t₁ × Option t₂` might return `#[t₁, t₂]`
if there are instances for `Array`, `Option`, and `Prod`, but not for `t₁` and `t₂`.

The `extraDeps` function is called whenever a type cannot be satisfied by existing instances.
It should return an array of types that need an instance to be implemented for the implementation
of the instance to succeed. For example, a `structure` might report the list of the types of all
its fields.
-/
private partial def planDerivation (className : Name) (type : Expr)
    (extraDeps : Expr → TermElabM (Array Expr)) :
    TermElabM (Array Expr) := do
  withTraceNode `Elab.ConfigEval
      (fun r => return m!"derivation plan `{.ofConstName className}` for `{type}`: "
        ++ match r with | .ok types => m!"{types}" | .error ex => ex.toMessageData) do
    go #[] {type} type
where
  go (plan : Array Expr) (processing : ExprSet) (type : Expr) : TermElabM (Array Expr) := withIncRecDepth do
    trace[Elab.ConfigEval] "plan: {plan}, processing: {processing.toList}, type: {type}"
    if plan.contains type then
      return plan
    else
      let cls ← mkAppM className #[type]
      let insts ← SynthInstance.getInstances cls
      trace[Elab.ConfigEval] "num insts for `{cls}`: {insts.size}"
      for inst in insts do
        try
          return ← tryInst plan processing cls inst
        catch _ => pure ()
      let depTypes ← extraDeps type
      trace[Elab.ConfigEval] "extra deps for `{type}`: {depTypes}"
      let plan ← useDepTypes plan processing depTypes
      return plan.push type
  tryInst (plan : Array Expr) (processing : ExprSet) (cls : Expr) (inst : SynthInstance.Instance) :
      TermElabM (Array Expr) := do
    trace[Elab.ConfigEval] "tryInst {cls}"
    let (xs, bis, cls') ← forallMetaTelescopeReducing (← inferType inst.val)
    trace[Elab.ConfigEval] "inst: {xs}, {cls'}"
    guard <| ← isDefEq cls cls'
    let mut depTypes := #[] -- types that need instances of the class
    -- Analyze instance arguments; fail if instances not of the class can't be synthesized
    for i in inst.synthOrder do
      let x := xs[i]!
      let depCls ← instantiateMVars (← whnf (← inferType x))
      if depCls.isAppOfArity className 1 then -- foralls not supported
        let depType := depCls.appArg!
        depTypes := depTypes.push depType
      else
        guard <| ← synthesizeInstMVarCore x.mvarId!
    -- Ensure everything's been solved for but the instances
    for h : i in [0:xs.size] do
      unless inst.synthOrder.contains i do
        let x ← instantiateMVars xs[i]
        guard <| !x.hasMVar
    trace[Elab.ConfigEval] "inst for `{cls}` deps: {depTypes}"
    useDepTypes plan processing depTypes
  useDepTypes (plan : Array Expr) (processing : ExprSet) (depTypes : Array Expr) : TermElabM (Array Expr) := do
    let depTypes ← depTypes.mapM instantiateMVars
    if let some depType := depTypes.find? (·.hasMVar) then
      throwError "dependency has metavariables: {depType}"
    -- Filter out those instances that are part of the derivation plan
    let depTypes := depTypes.filter (!plan.contains ·)
    -- If any are currently being processed, then we have a cyclic dependency.
    if let some depType := depTypes.find? processing.contains then
      throwError "cyclic dependency on {depType}"
    let mut plan := plan
    for depType in depTypes do
      plan ← go plan (processing.insert depType) depType
    return plan

/--
Helper for deriving instances along with all dependencies.
Given a one-parameter class `className` and a type `type`,
uses pre-existing conditional instances to figure out which types would
suffice to be implemented, then runs `mkCmd` on each type with fresh macro scopes.

The commands are generated and elaborated one at a time.
-/
def withClassInstDeps (className : Name) (type : Expr)
    (extraDeps : Expr → TermElabM (Array Expr))
    (mkCmd : Expr → TermElabM Command) :
    CommandElabM Unit := do
  let types ← liftTermElabM <| planDerivation className type extraDeps
  let env ← getEnv
  for type' in types do
    let cmd ← liftTermElabM do
      try
        withFreshMacroScope (mkCmd type')
      catch ex =>
        trace[Elab.ConfigEval] m!"failure deriving instance for `{type'}`: {ex.toMessageData}"
        setEnv env
        throw ex
    elabCommand cmd
    trace[Elab.ConfigEval] m!"added instance of {.ofConstName className} for  `{type'}`"

builtin_initialize
  registerTraceClass `Elab.ConfigEval

end Lean.Elab.ConfigEval
