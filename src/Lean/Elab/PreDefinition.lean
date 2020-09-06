/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
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

def instantiateMVarsAtPreDecls (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) :=
preDefs.mapM fun preDecl => do
  type  ← instantiateMVars preDecl.type;
  value ← instantiateMVars preDecl.value;
  pure { preDecl with type := type, value := value }

private def levelMVarToParamExpr (e : Expr) : StateRefT Nat TermElabM Expr := do
nextIdx ← get;
(e, nextIdx) ← liftM $ levelMVarToParam e nextIdx;
set nextIdx;
pure e

private def levelMVarToParamPreDeclsAux (preDefs : Array PreDefinition) : StateRefT Nat TermElabM (Array PreDefinition) :=
preDefs.mapM fun preDecl => do
  type  ← levelMVarToParamExpr preDecl.type;
  value ← levelMVarToParamExpr preDecl.value;
  pure { preDecl with type := type, value := value }

def levelMVarToParamPreDecls (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) :=
(levelMVarToParamPreDeclsAux preDefs).run' 1

private def collectLevelParamsExpr (e : Expr) : StateM CollectLevelParams.State Unit := do
modify fun s => collectLevelParams s e

private def getLevelParamsPreDecls (preDefs : Array PreDefinition) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (List Name) :=
let (_, s) := StateT.run
  (preDefs.forM fun preDecl => do {
    collectLevelParamsExpr preDecl.type;
    collectLevelParamsExpr preDecl.value })
  {};
match sortDeclLevelParams scopeLevelNames allUserLevelNames s.params with
| Except.error msg      => throwError msg
| Except.ok levelParams => pure levelParams

private def shareCommon (preDefs : Array PreDefinition) : Array PreDefinition :=
let result : Std.ShareCommonM (Array PreDefinition) :=
  preDefs.mapM fun preDecl => do {
    type  ← Std.withShareCommon preDecl.type;
    value ← Std.withShareCommon preDecl.value;
    pure { preDecl with type := type, value := value }
  };
result.run

def fixLevelParams (preDefs : Array PreDefinition) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (Array PreDefinition) := do
let preDefs := shareCommon preDefs;
lparams ← getLevelParamsPreDecls preDefs scopeLevelNames allUserLevelNames;
let us := lparams.map mkLevelParam;
let fixExpr (e : Expr) : Expr :=
  e.replace fun c => match c with
    | Expr.const declName _ _ => if preDefs.any fun preDecl => preDecl.declName == declName then some $ Lean.mkConst declName us else none
    | _ => none;
pure $ preDefs.map fun preDecl =>
  { preDecl with
    type    := fixExpr preDecl.type,
    value   := fixExpr preDecl.value,
    lparams := lparams }

private def applyAttributesOf (preDefs : Array PreDefinition) (applicationTime : AttributeApplicationTime) : TermElabM Unit := do
preDefs.forM fun preDecl => applyAttributes preDecl.declName preDecl.modifiers.attrs applicationTime

private def addAndCompileNonRec (preDecl : PreDefinition) : TermElabM Unit := do
env ← getEnv;
let decl :=
  match preDecl.kind with
  | DefKind.«example» => unreachable!
  | DefKind.«theorem» =>
    Declaration.thmDecl { name := preDecl.declName, lparams := preDecl.lparams, type := preDecl.type, value := preDecl.value }
  | DefKind.«opaque»  =>
    Declaration.opaqueDecl { name := preDecl.declName, lparams := preDecl.lparams, type := preDecl.type, value := preDecl.value,
                             isUnsafe := preDecl.modifiers.isUnsafe }
  | DefKind.«abbrev»  =>
    Declaration.defnDecl { name := preDecl.declName, lparams := preDecl.lparams, type := preDecl.type, value := preDecl.value,
                           hints := ReducibilityHints.«abbrev», isUnsafe := preDecl.modifiers.isUnsafe }
  | DefKind.«def»  =>
    Declaration.defnDecl { name := preDecl.declName, lparams := preDecl.lparams, type := preDecl.type, value := preDecl.value,
                           hints := ReducibilityHints.regular (getMaxHeight env preDecl.value + 1),
                           isUnsafe := preDecl.modifiers.isUnsafe };
ensureNoUnassignedMVars decl;
addDecl decl;
applyAttributesOf #[preDecl] AttributeApplicationTime.afterTypeChecking;
compileDecl decl;
applyAttributesOf #[preDecl] AttributeApplicationTime.afterCompilation;
pure ()

private def addAndCompileAsUnsafe (preDefs : Array PreDefinition) : TermElabM Unit := do
let decl := Declaration.mutualDefnDecl $ preDefs.toList.map fun preDecl => {
    name     := preDecl.declName,
    lparams  := preDecl.lparams,
    type     := preDecl.type,
    value    := preDecl.value,
    isUnsafe := true,
    hints    := ReducibilityHints.opaque
  };
ensureNoUnassignedMVars decl;
addDecl decl;
applyAttributesOf preDefs AttributeApplicationTime.afterTypeChecking;
compileDecl decl;
applyAttributesOf preDefs AttributeApplicationTime.afterCompilation;
pure ()

private def partitionNonRec (preDefs : Array PreDefinition) : Array PreDefinition × Array PreDefinition :=
preDefs.partition fun predDecl =>
  Option.isNone $ predDecl.value.find? fun c => match c with
    | Expr.const declName _ _ => preDefs.any fun preDecl => preDecl.declName == declName
    | _ => false

def addPreDefinitions (preDefs : Array PreDefinition) : TermElabM Unit := do
preDefs.forM fun preDecl => trace `Elab.definition.body fun _ => preDecl.declName ++ " : " ++ preDecl.type ++ " :=" ++ Format.line ++ preDecl.value;
let (preDefsNonRec, preDefs) := partitionNonRec preDefs;
preDefsNonRec.forM addAndCompileNonRec;
-- TODO
addAndCompileAsUnsafe preDefs

end Elab
end Lean
