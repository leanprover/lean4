/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Elab.Definition

namespace Lean
namespace Elab

/- DefView after elaborating the header. -/
structure DefViewElabHeader :=
(ref           : Syntax)
(modifiers     : Modifiers)
(kind          : DefKind)
(shortDeclName : Name)
(declName      : Name)
(levelNames    : List Name)
(numParams     : Nat)
(type          : Expr) -- including the parameters
(declVal       : Syntax)

namespace Term

open Meta

private def checkModifiers (m₁ m₂ : Modifiers) : TermElabM Unit := do
unless (m₁.isUnsafe == m₂.isUnsafe) $
  throwError "cannot mix unsafe and safe definitions";
unless (m₁.isNoncomputable == m₂.isNoncomputable) $
  throwError "cannot mix computable and non-computable definitions";
unless (m₁.isPartial == m₂.isPartial) $
  throwError "cannot mix partial and non-partial definitions";
pure ()

private def checkKinds (k₁ k₂ : DefKind) : TermElabM Unit := do
unless (k₁.isExample == k₂.isExample) $
  throwError "cannot mix examples and definitions"; -- Reason: we should discard examples
unless (k₁.isTheorem == k₂.isTheorem) $
  throwError "cannot mix theorems and definitions"; -- Reason: we will eventually elaborate theorems in `Task`s.
pure ()

private def check (prevHeaders : Array DefViewElabHeader) (newHeader : DefViewElabHeader) : TermElabM Unit := do
when (newHeader.kind.isTheorem && newHeader.modifiers.isUnsafe) $
  throwError "unsafe theorems are not allowed";
if h : 0 < prevHeaders.size then
  let firstHeader := prevHeaders.get ⟨0, h⟩;
  catch
   (do
     unless (newHeader.levelNames == firstHeader.levelNames) $
       throwError "universe parameters mismatch";
     checkModifiers newHeader.modifiers firstHeader.modifiers;
     checkKinds newHeader.kind firstHeader.kind)
   (fun ex => match ex with
     | Exception.error ref msg => throw (Exception.error ref ("invalid mutually recursive definitions, " ++ msg))
     | _ => throw ex)
else
  pure ()

private def elabFunType (xs : Array Expr) (view : DefView) : TermElabM Expr :=
match view.type? with
| some typeStx => do
  type ← elabType typeStx;
  synthesizeSyntheticMVarsNoPostponing;
  type ← instantiateMVars type;
  mkForallFVars xs type
| none => do
  type ← withRef view.binders $ mkFreshTypeMVar;
  mkForallFVars xs type

private def elabHeaders (views : Array DefView) : TermElabM (Array DefViewElabHeader) :=
views.foldlM
  (fun (headers : Array DefViewElabHeader) (view : DefView) => withRef view.ref do
    currNamespace ← getCurrNamespace;
    currLevelNames ← getLevelNames;
    ⟨shortDeclName, declName, levelNames⟩ ← expandDeclId currNamespace currLevelNames view.declId view.modifiers;
    applyAttributes declName view.modifiers.attrs AttributeApplicationTime.beforeElaboration;
    withLevelNames levelNames $ elabBinders view.binders.getArgs fun xs => do
      type ← elabFunType xs view;
      let newHeader : DefViewElabHeader := {
        ref           := view.ref,
        modifiers     := view.modifiers,
        kind          := view.kind,
        shortDeclName := shortDeclName,
        declName      := declName,
        levelNames    := levelNames,
        numParams     := xs.size,
        type          := type,
        declVal       := view.val
      };
      check headers newHeader;
      pure $ headers.push newHeader)
  #[]

private partial def withFunLocalDeclsAux {α} (headers : Array DefViewElabHeader) (k : Array Expr → TermElabM α) : Nat → Array Expr → TermElabM α
| i, fvars =>
  if h : i < headers.size then do
    let header := headers.get ⟨i, h⟩;
    withLocalDeclD header.shortDeclName header.type fun fvar => withFunLocalDeclsAux (i+1) (fvars.push fvar)
  else
    k fvars

private def withFunLocalDecls {α} (headers : Array DefViewElabHeader) (k : Array Expr → TermElabM α) : TermElabM α :=
withFunLocalDeclsAux headers k 0 #[]

/-
Recall that
```
def matchAlts (optionalFirstBar := true) : Parser :=
withPosition $ fun pos =>
  (if optionalFirstBar then optional "| " else "| ") >>
  sepBy1 matchAlt (checkColGe pos.column "alternatives must be indented" >> "|")
def declValSimple    := parser! " := " >> termParser
def declValEqns      := parser! Term.matchAlts false
def declVal          := declValSimple <|> declValEqns
```
-/
private def declValToTerm (declVal : Syntax) : MacroM Syntax :=
if declVal.isOfKind `Lean.Parser.Command.declValSimple then
  pure $ declVal.getArg 1
else if declVal.isOfKind `Lean.Parser.Command.declValEqns then
  expandMatchAltsIntoMatch declVal (declVal.getArg 1)
else
  Macro.throwError declVal "unexpected definition value"

private def elabFunValues (headers : Array DefViewElabHeader) : TermElabM (Array Expr) :=
headers.mapM fun header => withDeclName header.declName $ withLevelNames header.levelNames do
  valStx ← liftMacroM $ declValToTerm header.declVal;
  forallBoundedTelescope header.type header.numParams fun xs type => do
    val ← elabTermEnsuringType valStx type;
    mkLambdaFVars xs val

private def collectUsed (headers : Array DefViewElabHeader) (values : Array Expr) (toLift : List LetRecToLift)
    : StateRefT CollectFVars.State TermElabM Unit := do
headers.forM fun header => collectUsedFVars header.type;
values.forM collectUsedFVars;
toLift.forM fun letRecToLift => do {
  collectUsedFVars letRecToLift.type;
  collectUsedFVars letRecToLift.val
}

private def removeUnusedVars (vars : Array Expr) (headers : Array DefViewElabHeader) (values : Array Expr) (toLift : List LetRecToLift)
    : TermElabM (LocalContext × LocalInstances × Array Expr) := do
(_, used) ← (collectUsed headers values toLift).run {};
removeUnused vars used

private def withUsedWhen {α} (vars : Array Expr) (headers : Array DefViewElabHeader) (values : Array Expr) (toLift : List LetRecToLift)
    (cond : Bool) (k : Array Expr → TermElabM α) : TermElabM α :=
if cond then do
 (lctx, localInsts, vars) ← removeUnusedVars vars headers values toLift;
 withLCtx lctx localInsts $ k vars
else
 k vars

private def isExample (views : Array DefView) : Bool :=
views.any fun view => view.kind.isExample

private def isTheorem (views : Array DefView) : Bool :=
views.any fun view => view.kind.isTheorem

private def instantiateMVarsAtHeader (header : DefViewElabHeader) : TermElabM DefViewElabHeader := do
type ← instantiateMVars header.type;
pure { header with type := type }

private def instantiateMVarsAtLetRecToLift (toLift : LetRecToLift) : TermElabM LetRecToLift := do
type ← instantiateMVars toLift.type;
val ← instantiateMVars toLift.val;
pure { toLift with type := type, val := val }

private def typeHasRecFun (type : Expr) (funFVars : Array Expr) (letRecsToLift : List LetRecToLift) : Option FVarId :=
let occ? := type.find? fun e => match e with
  | Expr.fvar fvarId _ => funFVars.contains e || letRecsToLift.any fun toLift => toLift.fvarId == fvarId
  | _ => false;
match occ? with
| some (Expr.fvar fvarId _) => some fvarId
| _ => none

private def getFunName (fvarId : FVarId) (letRecsToLift : List LetRecToLift) : TermElabM Name := do
decl? ← findLocalDecl? fvarId;
match decl? with
| some decl => pure decl.userName
| none =>
  /- Recall that the FVarId of nested let-recs are not in the current local context. -/
  match letRecsToLift.findSome? fun (toLift : LetRecToLift) => if toLift.fvarId == fvarId then some toLift.shortDeclName else none with
  | none   => throwError "unknown function"
  | some n => pure n

/-
Ensures that the of let-rec definitions do not contain functions being defined.
In principle, this test can be improved. We could perform it after we separate the set of functions is strongly connected components.
However, this extra complication doesn't seem worth it.
-/
private def checkLetRecsToLiftTypes (funVars : Array Expr) (letRecsToLift : List LetRecToLift) : TermElabM Unit :=
letRecsToLift.forM fun toLift => do
  match typeHasRecFun toLift.type funVars letRecsToLift with
  | none        => pure ()
  | some fvarId => do
    fnName ← getFunName fvarId letRecsToLift;
    throwErrorAt toLift.ref ("invalid type in 'let rec', it uses '" ++ fnName ++ "' which is being defined simultaneously")

private def replaceFunFVarsWithConsts (headers : Array DefViewElabHeader) (funFVars : Array Expr) (vars : Array Expr) (e : Expr) : Expr :=
e.replace fun x => match x with
  | Expr.fvar fvarId _ =>
    match funFVars.indexOf x with
    | some idx => match headers.get? idx.val with
      | some header => some $ mkAppN (Lean.mkConst header.declName) vars -- Remark: we add the universe levels later
      | none        => none
    | none     => none
  | _ => none

/- A mapping from -/
abbrev Closures := NameMap NameSet

namespace LetRecClosure

structure State :=
(closures : Closures    := {})
(modified : Bool        := false)

abbrev M := ReaderT (List FVarId) $ StateM State

private def isModified : M Bool := do
s ← get; pure s.modified

private def resetModified : M Unit :=
modify fun s => { s with modified := false }

private def markModified : M Unit :=
modify fun s => { s with modified := true }

private def getClosures : M Closures :=
do s ← get; pure s.closures

private def modifyClosures (f : Closures → Closures) : M Unit :=
modify fun s => { s with closures := f s.closures }

-- merge s₂ into s₁
private def merge (s₁ s₂ : NameSet) : M NameSet :=
s₂.foldM
  (fun (s₁ : NameSet) k =>
    if s₁.contains k then
      pure s₁
    else do
      markModified;
      pure $ s₁.insert k)
  s₁

private def updateClosureOf (fvarId : FVarId) : M Unit := do
closures ← getClosures;
match closures.find? fvarId with
| none         => pure ()
| some closure => do
  closureNew ← closure.foldM
    (fun (closureNew : NameSet) (fvarId' : FVarId) =>
      if fvarId == fvarId' then
        pure closureNew
      else
        match closures.find? fvarId' with
        | none => pure closureNew
        -- We are being sloppy here `otherClosure` may contain free variables that are not in the context of the let-rec associated with fvarId.
        -- We filter these out-of-context free variables later.
        | some otherClosure => merge closureNew otherClosure)
    closure;
  modifyClosures fun closures => closures.insert fvarId closureNew

private partial def closureFixpoint : Unit → M Unit
| _ => do
  resetModified;
  letRecFVarIds ← read;
  letRecFVarIds.forM updateClosureOf;
  whenM isModified $ closureFixpoint ()

private def mkInitialClosures (letRecsToLift : List LetRecToLift) : Closures :=
letRecsToLift.foldl
  (fun (closures : Closures) toLift =>
    let state := Lean.collectFVars {} toLift.val;
    let state := Lean.collectFVars state toLift.type;
    closures.insert toLift.fvarId state.fvarSet)
  {}

private def mkClosures (letRecsToLift : List LetRecToLift) : Closures :=
let letRecFVarIds := letRecsToLift.map fun toLift => toLift.fvarId;
let closures      := mkInitialClosures letRecsToLift;
let (_, s)        := ((closureFixpoint ()).run letRecFVarIds).run { closures := closures };
s.closures

private def nameSetToFVars (s : NameSet) (lctx : LocalContext) (letRecFVarIds : List FVarId) : Array FVarId :=
let fvarIds := s.fold
  (fun (fvarIds : Array FVarId) (fvarId : FVarId) =>
    if lctx.contains fvarId && !letRecFVarIds.contains fvarId then
      fvarIds.push fvarId
    else
      fvarIds)
  #[];
fvarIds.qsort fun fvarId₁ fvarId₂ => (lctx.get! fvarId₁).index < (lctx.get! fvarId₂).index

def main (letRecsToLift : List LetRecToLift) : TermElabM (List LetRecToLift) := do
let letRecFVarIds := letRecsToLift.map fun toLift => toLift.fvarId;
let closures := mkClosures letRecsToLift;
-- Assign metavariables associated with each let-rec
ps ← letRecsToLift.mapM fun toLift => do {
  let s    := (closures.find? toLift.fvarId).get!;
  let lctx := toLift.lctx;
  let xs   := (nameSetToFVars s lctx letRecFVarIds).map mkFVar;
  assignExprMVar toLift.mvarId (mkAppN (Lean.mkConst toLift.declName) xs);
  pure (xs, toLift)
};
ps.mapM fun (p : Array Expr × LetRecToLift) => do
  let (xs, toLift) := p;
  type ← instantiateMVars toLift.type;
  val  ← instantiateMVars toLift.val;
  let lctx := toLift.lctx;
  -- Val may contain outer let-recs, we must replace them with constants
  let val := val.replace fun x => match x with
    | Expr.fvar fvarId _ => match ps.find? fun (p : Array Expr × LetRecToLift) => p.2.fvarId == fvarId with
      | some p => some (mkAppN (Lean.mkConst p.2.declName) p.1)
      | none => none
    | _ => none;
  withLCtx lctx toLift.localInstances do
    -- Apply closure
    type ← mkForallFVars xs type;
    val  ← mkLambdaFVars xs val;
    pure { toLift with type := type, val := val }

end LetRecClosure

def elabMutualDef (vars : Array Expr) (views : Array DefView) : TermElabM Unit := do
scopeLevelNames ← getLevelNames;
headers ← elabHeaders views;
withFunLocalDecls headers fun funFVars => do
  values ← elabFunValues headers;
  Term.synthesizeSyntheticMVarsNoPostponing;
  if isExample views then pure ()
  else do
    values ← values.mapM instantiateMVars;
    headers ← headers.mapM instantiateMVarsAtHeader;
    letRecsToLift ← getLetRecsToLift;
    letRecsToLift ← letRecsToLift.mapM instantiateMVarsAtLetRecToLift;
    checkLetRecsToLiftTypes funFVars letRecsToLift;
    withUsedWhen vars headers values letRecsToLift (not $ isTheorem views) fun vars => do
      let values        := values.map $ replaceFunFVarsWithConsts headers funFVars vars;
      let letRecsToLift := letRecsToLift.map fun toLift => { toLift with val := replaceFunFVarsWithConsts headers funFVars vars toLift.val };
      values  ← values.mapM $ mkLambdaFVars vars;
      headers ← headers.mapM fun header => do { type ← mkForallFVars vars header.type; pure { header with type := type } };
      letRecsToLift ← LetRecClosure.main letRecsToLift;
      values ← values.mapM instantiateMVars;
      -- TODO
      values.forM fun val => IO.println (toString val);
      letRecsToLift.forM fun toLift => IO.println (toString toLift.declName ++ " := " ++ toString toLift.val);
      throwError "WIP mutual def"

end Term

namespace Command

def elabMutualDef (ds : Array Syntax) : CommandElabM Unit := do
views ← ds.mapM fun d => do {
  modifiers ← elabModifiers (d.getArg 0);
  mkDefView modifiers (d.getArg 1)
};
runTermElabM none fun vars => Term.elabMutualDef vars views

end Command
end Elab
end Lean
