/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.ForEachExprWhere
import Lean.Elab.Deriving.Basic

namespace Lean.Elab
open Command Meta Parser Term

private abbrev IndexSet := RBTree Nat compare
private abbrev LocalInst2Index := FVarIdMap Nat

private def implicitBinderF := Parser.Term.implicitBinder
private def instBinderF     := Parser.Term.instBinder

private def mkInhabitedInstanceUsing (inductiveTypeName : Name) (ctorName : Name) (addHypotheses : Bool) : CommandElabM Bool := do
  match (← liftTermElabM mkInstanceCmd?) with
  | some cmd =>
    elabCommand cmd
    return true
  | none =>
    return false
where
  addLocalInstancesForParamsAux {α} (k : LocalInst2Index → TermElabM α) : List Expr → Nat → LocalInst2Index → TermElabM α
    | [], _, map    => k map
    | x::xs, i, map =>
      try
        let instType ← mkAppM `Inhabited #[x]
        if (← isTypeCorrect instType) then
          withLocalDeclD (← mkFreshUserName `inst) instType fun inst => do
            trace[Elab.Deriving.inhabited] "adding local instance {instType}"
            addLocalInstancesForParamsAux k xs (i+1) (map.insert inst.fvarId! i)
        else
          addLocalInstancesForParamsAux k xs (i+1) map
      catch _ =>
        addLocalInstancesForParamsAux k xs (i+1) map

  addLocalInstancesForParams {α} (xs : Array Expr) (k : LocalInst2Index → TermElabM α) : TermElabM α := do
    if addHypotheses then
      addLocalInstancesForParamsAux k xs.toList 0 {}
    else
      k {}

  collectUsedLocalsInsts (usedInstIdxs : IndexSet) (localInst2Index : LocalInst2Index) (e : Expr) : IndexSet :=
    if localInst2Index.isEmpty then
      usedInstIdxs
    else
      let visit {ω} : StateRefT IndexSet (ST ω) Unit :=
        e.forEachWhere Expr.isFVar fun e =>
          let fvarId := e.fvarId!
          match localInst2Index.find? fvarId with
          | some idx => modify (·.insert idx)
          | none => pure ()
      runST (fun _ => visit |>.run usedInstIdxs) |>.2

  /-- Create an `instance` command using the constructor `ctorName` with a hypothesis `Inhabited α` when `α` is one of the inductive type parameters
     at position `i` and `i ∈ assumingParamIdxs`. -/
  mkInstanceCmdWith (assumingParamIdxs : IndexSet) : TermElabM Syntax := do
    let indVal ← getConstInfoInduct inductiveTypeName
    let ctorVal ← getConstInfoCtor ctorName
    let mut indArgs := #[]
    let mut binders := #[]
    for i in [:indVal.numParams + indVal.numIndices] do
      let arg := mkIdent (← mkFreshUserName `a)
      indArgs := indArgs.push arg
      let binder ← `(bracketedBinderF| { $arg:ident })
      binders := binders.push binder
      if assumingParamIdxs.contains i then
        let binder ← `(bracketedBinderF| [Inhabited $arg:ident ])
        binders := binders.push binder
    let type ← `(Inhabited (@$(mkIdent inductiveTypeName):ident $indArgs:ident*))
    let mut ctorArgs := #[]
    for _ in [:ctorVal.numParams] do
      ctorArgs := ctorArgs.push (← `(_))
    for _ in [:ctorVal.numFields] do
      ctorArgs := ctorArgs.push (← ``(Inhabited.default))
    let val ← `(⟨@$(mkIdent ctorName):ident $ctorArgs*⟩)
    `(instance $binders:bracketedBinder* : $type := $val)

  mkInstanceCmd? : TermElabM (Option Syntax) := do
    let ctorVal ← getConstInfoCtor ctorName
    forallTelescopeReducing ctorVal.type fun xs _ =>
      addLocalInstancesForParams xs[:ctorVal.numParams] fun localInst2Index => do
        let mut usedInstIdxs := {}
        let mut ok := true
        for h : i in [ctorVal.numParams:xs.size] do
          let x := xs[i]
          let instType ← mkAppM `Inhabited #[(← inferType x)]
          trace[Elab.Deriving.inhabited] "checking {instType} for '{ctorName}'"
          match (← trySynthInstance instType) with
          | LOption.some e =>
            usedInstIdxs := collectUsedLocalsInsts usedInstIdxs localInst2Index e
          | _ =>
            trace[Elab.Deriving.inhabited] "failed to generate instance using '{ctorName}' {if addHypotheses then "(assuming parameters are inhabited)" else ""} because of field with type{indentExpr (← inferType x)}"
            ok := false
            break
        if !ok then
          return none
        else
          trace[Elab.Deriving.inhabited] "inhabited instance using '{ctorName}' {if addHypotheses then "(assuming parameters are inhabited)" else ""} {usedInstIdxs.toList}"
          let cmd ← mkInstanceCmdWith usedInstIdxs
          trace[Elab.Deriving.inhabited] "\n{cmd}"
          return some cmd

private def mkInhabitedInstance (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  let doIt (addHypotheses : Bool) : CommandElabM Bool := do
    for ctorName in indVal.ctors do
      if (← mkInhabitedInstanceUsing declName ctorName addHypotheses) then
        return true
    return false
  unless (← doIt false <||> doIt true) do
    throwError "failed to generate 'Inhabited' instance for '{declName}'"

def mkInhabitedInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    declNames.forM mkInhabitedInstance
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler `Inhabited mkInhabitedInstanceHandler
  registerTraceClass `Elab.Deriving.inhabited

end Lean.Elab
