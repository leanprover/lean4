/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural
import Lean.Elab.PreDefinition.WF
namespace Lean.Elab
open Meta
open Term

private def addAndCompilePartial (preDefs : Array PreDefinition) : TermElabM Unit := do
  for preDef in preDefs do
    trace[Elab.definition] "processing {preDef.declName}"
    forallTelescope preDef.type fun xs type => do
      let inh ← liftM $ mkInhabitantFor preDef.declName xs type
      trace[Elab.definition] "inhabitant for {preDef.declName}"
      addNonRec { preDef with
        kind  := DefKind.«opaque»,
        value := inh
      }
  addAndCompilePartialRec preDefs

private def isNonRecursive (preDef : PreDefinition) : Bool :=
  Option.isNone $ preDef.value.find? fun
    | Expr.const declName _ _ => preDef.declName == declName
    | _ => false

private def partitionPreDefs (preDefs : Array PreDefinition) : Array (Array PreDefinition) :=
  let getPreDef    := fun declName => (preDefs.find? fun preDef => preDef.declName == declName).get!
  let vertices     := preDefs.toList.map (·.declName)
  let successorsOf := fun declName => (getPreDef declName).value.foldConsts [] fun declName successors =>
    if preDefs.any fun preDef => preDef.declName == declName then
      declName :: successors
    else
      successors
  let sccs := SCC.scc vertices successorsOf
  sccs.toArray.map fun scc => scc.toArray.map getPreDef

private def collectMVarsAtPreDef (preDef : PreDefinition) : StateRefT CollectMVars.State MetaM Unit := do
  collectMVars preDef.value
  collectMVars preDef.type

private def getMVarsAtPreDef (preDef : PreDefinition) : MetaM (Array MVarId) := do
  let (_, s) ← (collectMVarsAtPreDef preDef).run {}
  pure s.result

private def ensureNoUnassignedMVarsAtPreDef (preDef : PreDefinition) : TermElabM PreDefinition := do
  let pendingMVarIds ← getMVarsAtPreDef preDef
  if (← logUnassignedUsingErrorInfos pendingMVarIds) then
    let preDef := { preDef with value := (← mkSorry preDef.type (synthetic := true)) }
    if (← getMVarsAtPreDef preDef).isEmpty then
      return preDef
    else
      throwAbortCommand
  else
    return preDef

def addPreDefinitions (preDefs : Array PreDefinition) : TermElabM Unit := do
  for preDef in preDefs do
    trace[Elab.definition.body] "{preDef.declName} : {preDef.type} :=\n{preDef.value}"
  let preDefs ← preDefs.mapM ensureNoUnassignedMVarsAtPreDef
  for preDefs in partitionPreDefs preDefs do
    trace[Elab.definition.scc] "{preDefs.map (·.declName)}"
    if preDefs.size == 1 && isNonRecursive preDefs[0] then
      let preDef := preDefs[0]
      if preDef.modifiers.isNoncomputable then
        addNonRec preDef
      else
        addAndCompileNonRec preDef
    else if preDefs.any (·.modifiers.isUnsafe) then
      addAndCompileUnsafe preDefs
    else if preDefs.any (·.modifiers.isPartial) then
      addAndCompilePartial preDefs
    else withRef (preDefs[0].ref) do
      mapError
        (orelseMergeErrors
          (structuralRecursion preDefs)
          (WFRecursion preDefs))
        (fun msg =>
          let preDefMsgs := preDefs.toList.map (MessageData.ofExpr $ mkConst ·.declName)
          m!"fail to show termination for{indentD (MessageData.joinSep preDefMsgs Format.line)}\nwith errors\n{msg}")

builtin_initialize
  registerTraceClass `Elab.definition.body
  registerTraceClass `Elab.definition.scc

end Lean.Elab
