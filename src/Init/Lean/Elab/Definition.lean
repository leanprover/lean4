/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Util.CollectLevelParams
import Init.Lean.Util.CollectFVars
import Init.Lean.Elab.DeclModifiers
import Init.Lean.Elab.TermBinders

namespace Lean
namespace Elab
namespace Command

inductive DefKind
| «def» | «theorem» | «example» | «opaque»

def DefKind.isTheorem : DefKind → Bool
| DefKind.theorem => true
| _               => false

def DefKind.isDefOrOpaque : DefKind → Bool
| DefKind.def    => true
| DefKind.opaque => true
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

def collectUsedFVars (ref : Syntax) (used : CollectFVars.State) (e : Expr) : TermElabM CollectFVars.State := do
e ← Term.instantiateMVars ref e;
pure $ collectFVars used e

def collectUsedFVarsAtFVars (ref : Syntax) (used : CollectFVars.State) (fvars : Array Expr) : TermElabM CollectFVars.State :=
fvars.foldlM
  (fun used fvar => do
    fvarType ← Term.inferType ref fvar;
    collectUsedFVars ref used fvarType)
  used

def removeUnused (ref : Syntax) (vars : Array Expr) (xs : Array Expr) (e : Expr) (eType : Expr)
    : TermElabM (LocalContext × LocalInstances × Array Expr) := do
let used : CollectFVars.State := {};
used ← collectUsedFVars ref used eType;
used ← collectUsedFVars ref used e;
used ← collectUsedFVarsAtFVars ref used xs;
localInsts ← Term.getLocalInsts;
lctx ← Term.getLCtx;
(lctx, localInsts, newVars, _) ← vars.foldrM
  (fun var (result : LocalContext × LocalInstances × Array Expr × CollectFVars.State) =>
    let (lctx, localInsts, newVars, used) := result;
    if used.fvarSet.contains var.fvarId! then do
      varType ← Term.inferType ref var;
      used ← collectUsedFVars ref used varType;
      pure (lctx, localInsts, newVars.push var, used)
    else
      pure (lctx.erase var.fvarId!, localInsts.erase var.fvarId!, newVars, used))
  (lctx, localInsts, #[], used);
pure (lctx, localInsts, newVars.reverse)

def withUsedWhen {α} (ref : Syntax) (vars : Array Expr) (xs : Array Expr) (e : Expr) (eType : Expr) (cond : Bool) (k : Array Expr → TermElabM α) : TermElabM α :=
if cond then do
 (lctx, localInsts, vars) ← removeUnused ref vars xs e eType;
 Term.withLCtx lctx localInsts $ k vars
else
 k vars

def withUsedWhen' {α} (ref : Syntax) (vars : Array Expr) (xs : Array Expr) (e : Expr) (cond : Bool) (k : Array Expr → TermElabM α) : TermElabM α :=
let dummyExpr := mkSort levelOne;
withUsedWhen ref vars xs e dummyExpr cond k

def mkDef (view : DefView) (declName : Name) (explictLevelNames : List Name) (vars : Array Expr) (xs : Array Expr) (type : Expr) (val : Expr)
    : TermElabM (Option Declaration) := do
let ref := view.ref;
val     ← Term.ensureHasType ref type val;
Term.synthesizeSyntheticMVars false;
type    ← Term.instantiateMVars ref type;
val     ← Term.instantiateMVars view.val val;
if view.kind.isExample then pure none
else withUsedWhen ref vars xs val type view.kind.isDefOrOpaque $ fun vars => do
  type ← Term.mkForall ref xs type;
  type ← Term.mkForall ref vars type;
  val  ← Term.mkLambda ref xs val;
  val  ← Term.mkLambda ref vars val;
  type ← Term.levelMVarToParam type;
  val  ← Term.levelMVarToParam val;
  type ← Term.instantiateMVars ref type;
  val  ← Term.instantiateMVars view.val val;
  Term.trace `Elab.definition.body ref $ fun _ => val;
  let usedParams : CollectLevelParams.State := {};
  let usedParams  := collectLevelParams usedParams type;
  let usedParams  := collectLevelParams usedParams val;
  let levelParams := sortDeclLevelParams explictLevelNames usedParams.params;
  match view.kind with
  | DefKind.theorem =>
    -- TODO theorem elaboration in parallel
    pure $ some $ Declaration.thmDecl { name := declName, lparams := levelParams, type := type, value := Task.pure val }
  | DefKind.opaque  =>
    pure $ some $ Declaration.opaqueDecl { name := declName, lparams := levelParams, type := type, value := val, isUnsafe := view.modifiers.isUnsafe }
  | DefKind.def =>
    pure $ some $ Declaration.defnDecl {
      name := declName, lparams := levelParams, type := type, value := val,
      hints := ReducibilityHints.regular 0, -- TODO
      isUnsafe := view.modifiers.isUnsafe }
  | _ => unreachable!

def elabDefVal (defVal : Syntax) (expectedType : Expr) : TermElabM Expr := do
let kind := defVal.getKind;
if kind == `Lean.Parser.Command.declValSimple then
  -- parser! " := " >> termParser
  Term.elabTerm (defVal.getArg 1) expectedType
else if kind == `Lean.Parser.Command.declValEqns then
  Term.throwError defVal "equations have not been implemented yet"
else
  Term.throwUnsupportedSyntax

def elabDefLike (view : DefView) : CommandElabM Unit :=
let ref := view.ref;
withDeclId view.declId $ fun name => do
  declName          ← mkDeclName view.modifiers name;
  applyAttributes ref declName view.modifiers.attrs AttributeApplicationTime.beforeElaboration;
  explictLevelNames ← getLevelNames;
  decl? ← runTermElabM declName $ fun vars => Term.elabBinders view.binders.getArgs $ fun xs =>
    match view.type? with
    | some typeStx => do
      type ← Term.elabType typeStx;
      Term.synthesizeSyntheticMVars false;
      type ← Term.instantiateMVars typeStx type;
      withUsedWhen' ref vars xs type view.kind.isTheorem $ fun vars => do
        val  ← elabDefVal view.val type;
        mkDef view declName explictLevelNames vars xs type val
    | none => do {
      type ← Term.mkFreshTypeMVar view.binders;
      val  ← elabDefVal view.val type;
      mkDef view declName explictLevelNames vars xs type val
    };
  match decl? with
  | none      => pure ()
  | some decl => do
    addDecl ref decl;
    applyAttributes ref declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking;
    compileDecl ref decl;
    applyAttributes ref declName view.modifiers.attrs AttributeApplicationTime.afterCompilation

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.definition;
pure ()

end Command
end Elab
end Lean
