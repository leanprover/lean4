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

def elabMutualDef (vars : Array Expr) (views : Array DefView) : TermElabM Unit := do
scopeLevelNames ← getLevelNames;
headers ← elabHeaders views;
withFunLocalDecls headers fun funFVars => do
  values ← elabFunValues headers;
  Term.synthesizeSyntheticMVarsNoPostponing;
  if isExample views then pure ()
  else do
    letRecsToLift ← getLetRecsToLift;
    withUsedWhen vars headers values letRecsToLift (not $ isTheorem views) fun vars => do

      values.forM fun val => IO.println (toString val);
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
