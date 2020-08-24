/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Std.ShareCommon
import Lean.Util.CollectLevelParams
import Lean.Util.FoldConsts
import Lean.Elab.CollectFVars
import Lean.Elab.DeclModifiers
import Lean.Elab.Binders

namespace Lean
namespace Elab
namespace Command

inductive DefKind
| «def» | «theorem» | «example» | «opaque» | «abbrev»

def DefKind.isTheorem : DefKind → Bool
| DefKind.theorem => true
| _               => false

def DefKind.isDefOrAbbrevOrOpaque : DefKind → Bool
| DefKind.def    => true
| DefKind.opaque => true
| DefKind.abbrev => true
| _              => false

def DefKind.isExample : DefKind → Bool
| DefKind.example => true
| _               => false

structure DefView :=
(kind          : DefKind)
(ref           : Syntax)
(modifiers     : Modifiers)
(declId        : Syntax)
(binders       : Syntax)
(type?         : Option Syntax)
(val           : Syntax)

private def removeUnused (vars : Array Expr) (xs : Array Expr) (e : Expr) (eType : Expr)
    : TermElabM (LocalContext × LocalInstances × Array Expr) := do
let used : CollectFVars.State := {};
used ← Term.collectUsedFVars used eType;
used ← Term.collectUsedFVars used e;
used ← Term.collectUsedFVarsAtFVars used xs;
Term.removeUnused vars used

private def withUsedWhen {α} (vars : Array Expr) (xs : Array Expr) (e : Expr) (eType : Expr) (cond : Bool) (k : Array Expr → TermElabM α) : TermElabM α :=
if cond then do
 (lctx, localInsts, vars) ← removeUnused vars xs e eType;
 Term.withLCtx lctx localInsts $ k vars
else
 k vars

private def withUsedWhen' {α} (vars : Array Expr) (xs : Array Expr) (e : Expr) (cond : Bool) (k : Array Expr → TermElabM α) : TermElabM α :=
let dummyExpr := mkSort levelOne;
withUsedWhen vars xs e dummyExpr cond k

def mkDef (view : DefView) (declName : Name) (scopeLevelNames allUserLevelNames : List Name) (vars : Array Expr) (xs : Array Expr) (type : Expr) (val : Expr)
    : TermElabM (Option Declaration) := do
withRef view.ref do
Term.synthesizeSyntheticMVars;
val     ← withRef view.val $ Term.ensureHasType type val;
Term.synthesizeSyntheticMVars false;
type    ← instantiateMVars type;
val     ← instantiateMVars val;
if view.kind.isExample then pure none
else withUsedWhen vars xs val type view.kind.isDefOrAbbrevOrOpaque $ fun vars => do
  type ← mkForallFVars xs type;
  type ← mkForallFVars vars type;
  val  ← mkLambdaFVars xs val;
  val  ← mkLambdaFVars vars val;
  (type, nextParamIdx) ← Term.levelMVarToParam type;
  (val,  _) ← Term.levelMVarToParam val nextParamIdx;
  type ← instantiateMVars type;
  val  ← instantiateMVars val;
  let shareCommonTypeVal : Std.ShareCommonM (Expr × Expr) := do {
    type ← Std.withShareCommon type;
    val  ← Std.withShareCommon val;
    pure (type, val)
  };
  let (type, val) := shareCommonTypeVal.run;
  Term.trace `Elab.definition.body fun _ => declName ++ " : " ++ type ++ " :=" ++ Format.line ++ val;
  let usedParams : CollectLevelParams.State := {};
  let usedParams  := collectLevelParams usedParams type;
  let usedParams  := collectLevelParams usedParams val;
  match sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams.params with
  | Except.error msg      => throwError msg
  | Except.ok levelParams =>
    match view.kind with
    | DefKind.theorem =>
      -- TODO theorem elaboration in parallel
      pure $ some $ Declaration.thmDecl { name := declName, lparams := levelParams, type := type, value := Task.pure val }
    | DefKind.opaque  =>
      pure $ some $ Declaration.opaqueDecl { name := declName, lparams := levelParams, type := type, value := val, isUnsafe := view.modifiers.isUnsafe }
    | DefKind.abbrev =>
      pure $ some $ Declaration.defnDecl {
        name := declName, lparams := levelParams, type := type, value := val,
        hints := ReducibilityHints.abbrev,
        isUnsafe := view.modifiers.isUnsafe }
    | DefKind.def => do
      env ← getEnv;
      pure $ some $ Declaration.defnDecl {
        name := declName, lparams := levelParams, type := type, value := val,
        hints := ReducibilityHints.regular (getMaxHeight env val + 1),
        isUnsafe := view.modifiers.isUnsafe }
    | _ => unreachable!

def elabDefVal (defVal : Syntax) (expectedType : Expr) : TermElabM Expr := do
let kind := defVal.getKind;
if kind == `Lean.Parser.Command.declValSimple then
  -- parser! " := " >> termParser
  Term.elabTerm (defVal.getArg 1) expectedType
else if kind == `Lean.Parser.Command.declValEqns then
  throwErrorAt defVal "equations have not been implemented yet"
else
  throwUnsupportedSyntax

def elabDefLike (view : DefView) : CommandElabM Unit :=
withRef view.ref do
scopeLevelNames ← getLevelNames;
withDeclId view.declId $ fun name => do
  declName          ← withRef view.declId $ mkDeclName view.modifiers name;
  applyAttributes declName view.modifiers.attrs AttributeApplicationTime.beforeElaboration;
  allUserLevelNames ← getLevelNames;
  decl? ← runTermElabM declName $ fun vars => Term.elabBinders view.binders.getArgs $ fun xs =>
    match view.type? with
    | some typeStx => do
      type ← Term.elabType typeStx;
      Term.synthesizeSyntheticMVars false;
      type ← instantiateMVars type;
      withUsedWhen' vars xs type view.kind.isTheorem $ fun vars => do
        val  ← elabDefVal view.val type;
        mkDef view declName scopeLevelNames allUserLevelNames vars xs type val
    | none => do {
      type ← withRef view.binders $ Term.mkFreshTypeMVar;
      val  ← elabDefVal view.val type;
      mkDef view declName scopeLevelNames allUserLevelNames vars xs type val
    };
  match decl? with
  | none      => pure ()
  | some decl => do
    addDecl decl;
    applyAttributes declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking;
    compileDecl decl;
    applyAttributes declName view.modifiers.attrs AttributeApplicationTime.afterCompilation

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.definition;
pure ()

end Command
end Elab
end Lean
