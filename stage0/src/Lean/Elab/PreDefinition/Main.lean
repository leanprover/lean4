/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural
import Lean.Elab.PreDefinition.WF

namespace Lean
namespace Elab
open Meta
open Term

private def addAndCompilePartial (preDefs : Array PreDefinition) : TermElabM Unit := do
preDefs.forM fun preDef =>
  forallTelescope preDef.type fun xs type => do
    inh ← liftM $ mkInhabitantFor preDef.declName xs type;
    addNonRec { preDef with
      kind  := DefKind.«opaque»,
      value := inh };
addAndCompileUnsafeRec preDefs

private def isNonRecursive (preDef : PreDefinition) : Bool :=
Option.isNone $ preDef.value.find? fun c => match c with
  | Expr.const declName _ _ => preDef.declName == declName
  | _ => false

private def partitionPreDefs (preDefs : Array PreDefinition) : Array (Array PreDefinition) :=
let getPreDef    := fun declName => (preDefs.find? fun preDef => preDef.declName == declName).get!;
let vertices     := preDefs.toList.map fun preDef => preDef.declName;
let successorsOf := fun declName => (getPreDef declName).value.foldConsts [] fun declName successors =>
  if preDefs.any fun preDef => preDef.declName == declName then
    declName :: successors
  else
    successors;
let sccs := SCC.scc vertices successorsOf;
sccs.toArray.map fun scc => scc.toArray.map getPreDef

private def collectMVarsAtPreDef (preDef : PreDefinition) : StateRefT CollectMVars.State MetaM Unit := do
collectMVars preDef.value;
collectMVars preDef.type

private def getMVarsAtPreDef (preDef : PreDefinition) : MetaM (Array MVarId) := do
(_, s) ← (collectMVarsAtPreDef preDef).run {};
pure s.result

private def ensureNoUnassignedMVarsAtPreDef (preDef : PreDefinition) : TermElabM Unit := do
pendingMVarIds ← liftMetaM $ getMVarsAtPreDef preDef;
foundError ← logUnassignedUsingErrorInfos pendingMVarIds;
when foundError throwAbort

def addPreDefinitions (preDefs : Array PreDefinition) : TermElabM Unit := do
preDefs.forM fun preDef => trace `Elab.definition.body fun _ => preDef.declName ++ " : " ++ preDef.type ++ " :=" ++ Format.line ++ preDef.value;
preDefs.forM ensureNoUnassignedMVarsAtPreDef;
(partitionPreDefs preDefs).forM fun preDefs => do
  if preDefs.size == 1 && isNonRecursive (preDefs.get! 0) then
    let preDef := preDefs.get! 0;
    if preDef.modifiers.isNoncomputable then
      addNonRec preDef
    else
      addAndCompileNonRec preDef
  else if preDefs.any fun preDef => preDef.modifiers.isUnsafe then
    addAndCompileUnsafe preDefs
  else if preDefs.any fun preDef => preDef.modifiers.isPartial then
    addAndCompilePartial preDefs
  else
    mapError
      (orelseMergeErrors
        (structuralRecursion preDefs)
        (WFRecursion preDefs))
      (fun msg =>
        let preDefMsgs := preDefs.toList.map fun preDef => MessageData.ofExpr $ mkConst preDef.declName;
        "fail to show termination for" ++ indentD (MessageData.joinSep preDefMsgs Format.line)
        ++ Format.line ++ "with errors" ++ Format.line ++ msg)
end Elab
end Lean
