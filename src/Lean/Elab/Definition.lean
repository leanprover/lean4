/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Std.ShareCommon
import Lean.Util.CollectLevelParams
import Lean.Util.FoldConsts
import Lean.Elab.CollectFVars
import Lean.Elab.Command
import Lean.Elab.SyntheticMVars
import Lean.Elab.Binders
import Lean.Elab.DeclUtil

namespace Lean
namespace Elab
namespace Command

open Meta

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

def mkDefViewOfAbbrev (modifiers : Modifiers) (stx : Syntax) : DefView :=
-- parser! "abbrev " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `inline };
let modifiers       := modifiers.addAttribute { name := `reducible };
{ ref := stx, kind := DefKind.abbrev, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := type, val := stx.getArg 3 }

def mkDefViewOfDef (modifiers : Modifiers) (stx : Syntax) : DefView :=
-- parser! "def " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
{ ref := stx, kind := DefKind.def, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := type, val := stx.getArg 3 }

def mkDefViewOfTheorem (modifiers : Modifiers) (stx : Syntax) : DefView :=
-- parser! "theorem " >> declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
{ ref := stx, kind := DefKind.theorem, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := some type, val := stx.getArg 3 }

def mkFreshInstanceName : CommandElabM Name := do
s ← get;
let idx := s.nextInstIdx;
modify fun s => { s with nextInstIdx := s.nextInstIdx + 1 };
pure $ Lean.Elab.mkFreshInstanceName s.env idx

def mkDefViewOfConstant (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
-- parser! "constant " >> declId >> declSig >> optional declValSimple
let (binders, type) := expandDeclSig (stx.getArg 2);
val ← match (stx.getArg 3).getOptional? with
  | some val => pure val
  | none     => do {
    val ← `(arbitrary _);
    pure $ Syntax.node `Lean.Parser.Command.declValSimple #[ mkAtomFrom stx ":=", val ]
  };
pure {
  ref := stx, kind := DefKind.opaque, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := some type, val := val
}

def mkDefViewOfInstance (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
-- parser! "instance " >> optional declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `instance };
declId ← match (stx.getArg 1).getOptional? with
  | some declId => pure declId
  | none        => do {
    id ← mkFreshInstanceName;
    pure $ Syntax.node `Lean.Parser.Command.declId #[mkIdentFrom stx id, mkNullNode]
  };
pure {
  ref := stx, kind := DefKind.def, modifiers := modifiers,
  declId := declId, binders := binders, type? := type, val := stx.getArg 3
}

def mkDefViewOfExample (modifiers : Modifiers) (stx : Syntax) : DefView :=
-- parser! "example " >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 1);
let id              := mkIdentFrom stx `_example;
let declId          := Syntax.node `Lean.Parser.Command.declId #[id, mkNullNode];
{ ref := stx, kind := DefKind.example, modifiers := modifiers,
  declId := declId, binders := binders, type? := some type, val := stx.getArg 2 }

def isDefLike (stx : Syntax) : Bool :=
let declKind := stx.getKind;
declKind == `Lean.Parser.Command.«abbrev» ||
declKind == `Lean.Parser.Command.«def» ||
declKind == `Lean.Parser.Command.«theorem» ||
declKind == `Lean.Parser.Command.«constant» ||
declKind == `Lean.Parser.Command.«instance» ||
declKind == `Lean.Parser.Command.«example»

def mkDefView (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView :=
let declKind := stx.getKind;
if declKind == `Lean.Parser.Command.«abbrev» then
  pure $ mkDefViewOfAbbrev modifiers stx
else if declKind == `Lean.Parser.Command.«def» then
  pure $ mkDefViewOfDef modifiers stx
else if declKind == `Lean.Parser.Command.«theorem» then
  pure $ mkDefViewOfTheorem modifiers stx
else if declKind == `Lean.Parser.Command.«constant» then
  mkDefViewOfConstant modifiers stx
else if declKind == `Lean.Parser.Command.«instance» then
  mkDefViewOfInstance modifiers stx
else if declKind == `Lean.Parser.Command.«example» then
  pure $ mkDefViewOfExample modifiers stx
else
  throwError "unexpected kind of definition"

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
 withLCtx lctx localInsts $ k vars
else
 k vars

private def withUsedWhen' {α} (vars : Array Expr) (xs : Array Expr) (e : Expr) (cond : Bool) (k : Array Expr → TermElabM α) : TermElabM α :=
let dummyExpr := mkSort levelOne;
withUsedWhen vars xs e dummyExpr cond k

def mkDef? (view : DefView) (declName : Name) (scopeLevelNames allUserLevelNames : List Name) (vars : Array Expr) (xs : Array Expr) (type : Expr) (val : Expr)
    : TermElabM (Option Declaration) := do
withRef view.ref do
Term.synthesizeSyntheticMVars;
val     ← withRef view.val $ Term.ensureHasType type val;
Term.synthesizeSyntheticMVarsNoPostponing;
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
  trace `Elab.definition.body fun _ => declName ++ " : " ++ type ++ " :=" ++ Format.line ++ val;
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
⟨name, declName, allUserLevelNames⟩ ← expandDeclId view.declId view.modifiers;
runTermElabM declName $ fun vars => Term.withLevelNames allUserLevelNames $ Term.elabBinders view.binders.getArgs fun xs => do
  applyAttributes declName view.modifiers.attrs AttributeApplicationTime.beforeElaboration;
  decl? ← match view.type? with
    | some typeStx => do
      type ← Term.elabType typeStx;
      Term.synthesizeSyntheticMVarsNoPostponing;
      type ← instantiateMVars type;
      withUsedWhen' vars xs type view.kind.isTheorem $ fun vars => do
        val  ← elabDefVal view.val type;
        mkDef? view declName scopeLevelNames allUserLevelNames vars xs type val
    | none => do {
        type ← withRef view.binders $ mkFreshTypeMVar;
        val  ← elabDefVal view.val type;
        mkDef? view declName scopeLevelNames allUserLevelNames vars xs type val
      };
  match decl? with
  | none      => pure ()
  | some decl => do
    Term.ensureNoUnassignedMVars decl;
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
