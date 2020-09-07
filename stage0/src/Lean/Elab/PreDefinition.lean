/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.SCC
import Lean.Elab.MkInhabitant
import Lean.Elab.Term
import Lean.Elab.DefView

namespace Lean
namespace Elab
open Meta
open Term

/-
A (potentially recursive) definition.
The elaborator converts it into Kernel definitions using many different strategies.
-/
structure PreDefinition :=
(kind      : DefKind)
(lparams   : List Name)
(modifiers : Modifiers)
(declName  : Name)
(type      : Expr)
(value     : Expr)

instance PreDefinition.inhabited : Inhabited PreDefinition :=
⟨⟨DefKind.«def», [], {}, arbitrary _, arbitrary _, arbitrary _⟩⟩

def instantiateMVarsAtPreDecls (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) :=
preDefs.mapM fun preDef => do
  type  ← instantiateMVars preDef.type;
  value ← instantiateMVars preDef.value;
  pure { preDef with type := type, value := value }

private def levelMVarToParamExpr (e : Expr) : StateRefT Nat TermElabM Expr := do
nextIdx ← get;
(e, nextIdx) ← liftM $ levelMVarToParam e nextIdx;
set nextIdx;
pure e

private def levelMVarToParamPreDeclsAux (preDefs : Array PreDefinition) : StateRefT Nat TermElabM (Array PreDefinition) :=
preDefs.mapM fun preDef => do
  type  ← levelMVarToParamExpr preDef.type;
  value ← levelMVarToParamExpr preDef.value;
  pure { preDef with type := type, value := value }

def levelMVarToParamPreDecls (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) :=
(levelMVarToParamPreDeclsAux preDefs).run' 1

private def collectLevelParamsExpr (e : Expr) : StateM CollectLevelParams.State Unit := do
modify fun s => collectLevelParams s e

private def getLevelParamsPreDecls (preDefs : Array PreDefinition) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (List Name) :=
let (_, s) := StateT.run
  (preDefs.forM fun preDef => do {
    collectLevelParamsExpr preDef.type;
    collectLevelParamsExpr preDef.value })
  {};
match sortDeclLevelParams scopeLevelNames allUserLevelNames s.params with
| Except.error msg      => throwError msg
| Except.ok levelParams => pure levelParams

private def shareCommon (preDefs : Array PreDefinition) : Array PreDefinition :=
let result : Std.ShareCommonM (Array PreDefinition) :=
  preDefs.mapM fun preDef => do {
    type  ← Std.withShareCommon preDef.type;
    value ← Std.withShareCommon preDef.value;
    pure { preDef with type := type, value := value }
  };
result.run

def fixLevelParams (preDefs : Array PreDefinition) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (Array PreDefinition) := do
let preDefs := shareCommon preDefs;
lparams ← getLevelParamsPreDecls preDefs scopeLevelNames allUserLevelNames;
let us := lparams.map mkLevelParam;
let fixExpr (e : Expr) : Expr :=
  e.replace fun c => match c with
    | Expr.const declName _ _ => if preDefs.any fun preDef => preDef.declName == declName then some $ Lean.mkConst declName us else none
    | _ => none;
pure $ preDefs.map fun preDef =>
  { preDef with
    type    := fixExpr preDef.type,
    value   := fixExpr preDef.value,
    lparams := lparams }

private def applyAttributesOf (preDefs : Array PreDefinition) (applicationTime : AttributeApplicationTime) : TermElabM Unit := do
preDefs.forM fun preDef => applyAttributes preDef.declName preDef.modifiers.attrs applicationTime

private def addNonRecAux (preDef : PreDefinition) (compile : Bool) : TermElabM Unit := do
env ← getEnv;
let decl :=
  match preDef.kind with
  | DefKind.«example» => unreachable!
  | DefKind.«theorem» =>
    Declaration.thmDecl { name := preDef.declName, lparams := preDef.lparams, type := preDef.type, value := preDef.value }
  | DefKind.«opaque»  =>
    Declaration.opaqueDecl { name := preDef.declName, lparams := preDef.lparams, type := preDef.type, value := preDef.value,
                             isUnsafe := preDef.modifiers.isUnsafe }
  | DefKind.«abbrev»  =>
    Declaration.defnDecl { name := preDef.declName, lparams := preDef.lparams, type := preDef.type, value := preDef.value,
                           hints := ReducibilityHints.«abbrev», isUnsafe := preDef.modifiers.isUnsafe }
  | DefKind.«def»  =>
    Declaration.defnDecl { name := preDef.declName, lparams := preDef.lparams, type := preDef.type, value := preDef.value,
                           hints := ReducibilityHints.regular (getMaxHeight env preDef.value + 1),
                           isUnsafe := preDef.modifiers.isUnsafe };
ensureNoUnassignedMVars decl;
addDecl decl;
applyAttributesOf #[preDef] AttributeApplicationTime.afterTypeChecking;
when compile $
  compileDecl decl;
applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation;
pure ()

private def addAndCompileNonRec (preDef : PreDefinition) : TermElabM Unit := do
addNonRecAux preDef true

private def addNonRec (preDef : PreDefinition) : TermElabM Unit := do
addNonRecAux preDef false

private def addAndCompileUnsafe (preDefs : Array PreDefinition) : TermElabM Unit := do
let decl := Declaration.mutualDefnDecl $ preDefs.toList.map fun preDef => {
    name     := preDef.declName,
    lparams  := preDef.lparams,
    type     := preDef.type,
    value    := preDef.value,
    isUnsafe := true,
    hints    := ReducibilityHints.opaque
  };
ensureNoUnassignedMVars decl;
addDecl decl;
applyAttributesOf preDefs AttributeApplicationTime.afterTypeChecking;
compileDecl decl;
applyAttributesOf preDefs AttributeApplicationTime.afterCompilation;
pure ()

private def addAndCompileUnsafeRec (preDefs : Array PreDefinition) : TermElabM Unit := do
addAndCompileUnsafe $ preDefs.map fun preDef =>
  { preDef with
    declName  := Compiler.mkUnsafeRecName preDef.declName,
    value     := preDef.value.replace fun e => match e with
      | Expr.const declName us _ =>
        if preDefs.any fun preDef => preDef.declName == declName then
          some $ mkConst (Compiler.mkUnsafeRecName declName) us
        else
          none
      | _ => none,
    modifiers := {} }

private def addAndCompilePartial (preDefs : Array PreDefinition) : TermElabM Unit := do
preDefs.forM fun preDef =>
  forallTelescopeReducing preDef.type fun xs type => do
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

private def tryStructuralRecursion? (preDef : PreDefinition) : TermElabM (Option PreDefinition) := do
trace `Elab.definition fun _ => preDef.declName ++ ":=\n" ++ preDef.value;
throwError "WIP"

def addPreDefinitions (preDefs : Array PreDefinition) : TermElabM Unit := do
preDefs.forM fun preDef => trace `Elab.definition.body fun _ => preDef.declName ++ " : " ++ preDef.type ++ " :=" ++ Format.line ++ preDef.value;
(partitionPreDefs preDefs).forM fun preDefs => do
  if preDefs.size == 1 && isNonRecursive (preDefs.get! 0) then
    addAndCompileNonRec (preDefs.get! 0)
  else if preDefs.any fun preDef => preDef.modifiers.isUnsafe then
    addAndCompileUnsafe preDefs
  else if preDefs.any fun preDef => preDef.modifiers.isPartial then
    addAndCompilePartial preDefs
  else if preDefs.size == 1 then do
    tryStructuralRecursion? (preDefs.get! 0);
    pure ()
  else
    -- TODO
    throwError "WIP"

end Elab
end Lean
