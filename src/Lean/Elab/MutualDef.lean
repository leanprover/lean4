/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Closure
import Lean.Meta.Check
import Lean.Elab.Command
import Lean.Elab.DefView

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
(valueStx      : Syntax)

instance DefViewElabHeader.inhabited : Inhabited DefViewElabHeader :=
⟨⟨arbitrary _, {}, DefKind.«def», arbitrary _, arbitrary _, [], 0, arbitrary _, arbitrary _⟩⟩

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
        valueStx      := view.value
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
  valStx ← liftMacroM $ declValToTerm header.valueStx;
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
Ensures that the of let-rec definition types do not contain functions being defined.
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

structure PreDeclaration :=
(kind      : DefKind)
(lparams   : List Name)
(modifiers : Modifiers)
(declName  : Name)
(type      : Expr)
(value     : Expr)

namespace MutualClosure

/- A mapping from FVarId to Set of FVarIds. -/
abbrev UsedFVarsMap := NameMap NameSet

/-
Create the `UsedFVarsMap` mapping that takes the variable id for the mutually recursive functions being defined to the set of
free variables in its definition.

For `mainFVars`, this is just the set of section variables `sectionVars` used.
For nested let-rec functions, we collect their free variables.

Recall that a `let rec` expressions are encoded as follows in the elaborator.
```lean
let rec
  f : A := t,
  g : B := s;
body
```
is encoded as
```lean
let f : A := ?m₁;
let g : B := ?m₂;
body
```
where `?m₁` and `?m₂` are synthetic opaque metavariables. That are assigned by this module.
We may have nested `let rec`s.
```lean
let rec f : A :=
    let rec g : B := t;
    s;
body
```
is encoded as
```lean
let f : A := ?m₁;
body
```
and the body of `f` is stored the field `val` of a `LetRecToLift`. For the example above,
we would have a `LetRecToLift` containing:
```
{
  mvarId := m₁,
  val    := `(let g : B := ?m₂; body)
  ...
}
```
Note that `g` is not a free variable at `(let g : B := ?m₂; body)`. We recover the fact that
`f` depends on `g` because it contains `m₂`
-/
private def mkInitialUsedFVarsMap (mctx : MetavarContext) (sectionVars : Array Expr) (mainFVarIds : Array FVarId) (letRecsToLift : List LetRecToLift)
    : UsedFVarsMap :=
let sectionVarSet := sectionVars.foldl (fun (s : NameSet) (var : Expr) => s.insert var.fvarId!) {};
let usedFVarMap := mainFVarIds.foldl
  (fun (usedFVarMap : UsedFVarsMap) mainFVarId =>
    usedFVarMap.insert mainFVarId sectionVarSet)
  {};
letRecsToLift.foldl
  (fun (usedFVarMap : UsedFVarsMap) toLift =>
    let state := Lean.collectFVars {} toLift.val;
    let state := Lean.collectFVars state toLift.type;
    let set   := state.fvarSet;
    /- toLift.val may contain metavariables that are placeholders for nested let-recs. We should collect the fvarId
       for the associated let-rec because we need this information to compute the fixpoint later. -/
    let mvarIds := (toLift.val.collectMVars {}).result;
    let set     := mvarIds.foldl
      (fun (set : NameSet) (mvarId : MVarId) =>
        match letRecsToLift.findSome? fun (toLift : LetRecToLift) => if toLift.mvarId == mctx.getDelayedRoot mvarId then some toLift.fvarId else none with
        | some fvarId => set.insert fvarId
        | none        => set)
      set;
    usedFVarMap.insert toLift.fvarId set)
  usedFVarMap

/-
The let-recs may invoke each other. Example:
```
let rec
  f (x : Nat) := g x + y
  g : Nat → Nat
    | 0   => 1
    | x+1 => f x + z
```
`y` is free variable in `f`, and `z` is a free variable in `g`.
To close `f` and `g`, `y` and `z` must be in the closure of both.
That is, we need to generate the top-level definitions.
```
def f (y z x : Nat) := g y z x + y
def g (y z : Nat) : Nat → Nat
  | 0 => 1
  | x+1 => f y z x + z
```
-/
namespace FixPoint

structure State :=
(usedFVarsMap : UsedFVarsMap := {})
(modified     : Bool         := false)

abbrev M := ReaderT (List FVarId) $ StateM State

private def isModified : M Bool := do s ← get; pure s.modified
private def resetModified : M Unit := modify fun s => { s with modified := false }
private def markModified : M Unit := modify fun s => { s with modified := true }
private def getUsedFVarsMap : M UsedFVarsMap := do s ← get; pure s.usedFVarsMap
private def modifyUsedFVars (f : UsedFVarsMap → UsedFVarsMap) : M Unit := modify fun s => { s with usedFVarsMap := f s.usedFVarsMap }

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

private def updateUsedVarsOf (fvarId : FVarId) : M Unit := do
usedFVarsMap ← getUsedFVarsMap;
match usedFVarsMap.find? fvarId with
| none         => pure ()
| some fvarIds => do
  fvarIdsNew ← fvarIds.foldM
    (fun (fvarIdsNew : NameSet) (fvarId' : FVarId) =>
      if fvarId == fvarId' then
        pure fvarIdsNew
      else
        match usedFVarsMap.find? fvarId' with
        | none => pure fvarIdsNew
          /- We are being sloppy here `otherFVarIds` may contain free variables that are
             not in the context of the let-rec associated with fvarId.
             We filter these out-of-context free variables later. -/
        | some otherFVarIds => merge fvarIdsNew otherFVarIds)
    fvarIds;
  modifyUsedFVars fun usedFVars => usedFVars.insert fvarId fvarIdsNew

private partial def fixpoint : Unit → M Unit
| _ => do
  resetModified;
  letRecFVarIds ← read;
  letRecFVarIds.forM updateUsedVarsOf;
  whenM isModified $ fixpoint ()

def run (letRecFVarIds : List FVarId) (usedFVarsMap : UsedFVarsMap) : UsedFVarsMap :=
let (_, s) := ((fixpoint ()).run letRecFVarIds).run { usedFVarsMap := usedFVarsMap };
s.usedFVarsMap

end FixPoint

abbrev FreeVarMap := NameMap (Array FVarId)

private def mkFreeVarMap
    (mctx : MetavarContext) (sectionVars : Array Expr) (mainFVarIds : Array FVarId)
    (recFVarIds : Array FVarId) (letRecsToLift : List LetRecToLift) : FreeVarMap :=
let usedFVarsMap  := mkInitialUsedFVarsMap mctx sectionVars mainFVarIds letRecsToLift;
let letRecFVarIds := letRecsToLift.map fun toLift => toLift.fvarId;
let usedFVarsMap  := FixPoint.run letRecFVarIds usedFVarsMap;
letRecsToLift.foldl
  (fun (freeVarMap : FreeVarMap) toLift =>
    let lctx       := toLift.lctx;
    let fvarIdsSet := (usedFVarsMap.find? toLift.fvarId).get!;
    let fvarIds    := fvarIdsSet.fold
      (fun (fvarIds : Array FVarId) (fvarId : FVarId) =>
        if lctx.contains fvarId && !recFVarIds.contains fvarId then
          fvarIds.push fvarId
        else
          fvarIds)
      #[];
    freeVarMap.insert toLift.fvarId fvarIds)
  {}

structure ClosureState :=
(newLocalDecls : Array LocalDecl := #[])
(localDecls    : Array LocalDecl := #[])
(newLetDecls   : Array LocalDecl := #[])
(exprArgs      : Array Expr      := #[])

private def pickMaxFVar? (lctx : LocalContext) (fvarIds : Array FVarId) : Option FVarId :=
fvarIds.getMax? fun fvarId₁ fvarId₂ => (lctx.get! fvarId₁).index < (lctx.get! fvarId₂).index

private def preprocess (e : Expr) : TermElabM Expr := do
e ← instantiateMVars e;
-- which let-decls are dependent. We say a let-decl is dependent if its lambda abstraction is type incorrect.
liftM $ check e;
pure e

/- Push free variables in `s` to `toProcess` if they are not already there. -/
private def pushNewVars (toProcess : Array FVarId) (s : CollectFVars.State) : Array FVarId :=
s.fvarSet.fold
  (fun (toProcess : Array FVarId) fvarId => if toProcess.contains fvarId then toProcess else toProcess.push fvarId)
  toProcess

private def pushLocalDecl (toProcess : Array FVarId) (fvarId : FVarId) (userName : Name) (type : Expr) (bi := BinderInfo.default)
    : StateRefT ClosureState TermElabM (Array FVarId) := do
type ← liftM $ preprocess type;
modify fun s => { s with
  newLocalDecls := s.newLocalDecls.push $ LocalDecl.cdecl (arbitrary _) fvarId userName type bi,
  exprArgs      := s.exprArgs.push (mkFVar fvarId)
};
pure $ pushNewVars toProcess (collectFVars {} type)

private partial def mkClosureForAux : Array FVarId → StateRefT ClosureState TermElabM Unit
| toProcess => do
  lctx ← getLCtx;
  match pickMaxFVar? lctx toProcess with
  | none        => pure ()
  | some fvarId => do
    let toProcess := toProcess.erase fvarId;
    localDecl ← getLocalDecl fvarId;
    match localDecl with
    | LocalDecl.cdecl _ _ userName type bi => do
      toProcess ← pushLocalDecl toProcess fvarId userName type bi;
      mkClosureForAux toProcess
    | LocalDecl.ldecl _ _ userName type val _ => do
      zetaFVarIds ← getZetaFVarIds;
      if !zetaFVarIds.contains fvarId then do
        /- Non-dependent let-decl. See comment at src/Lean/Meta/Closure.lean -/
        toProcess ← pushLocalDecl toProcess fvarId userName type;
        mkClosureForAux toProcess
      else do
        /- Dependent let-decl. -/
        type ← liftM $ preprocess type;
        val  ← liftM $ preprocess val;
        modify fun s => { s with
          newLetDecls   := s.newLetDecls.push $ LocalDecl.ldecl (arbitrary _) fvarId userName type val false,
          /- We don't want to interleave let and lambda declarations in our closure. So, we expand any occurrences of fvarId
             at `newLocalDecls` and `localDecls` -/
          newLocalDecls := s.newLocalDecls.map (replaceFVarIdAtLocalDecl fvarId val),
          localDecls := s.localDecls.map (replaceFVarIdAtLocalDecl fvarId val)
        };
        mkClosureForAux (pushNewVars toProcess (collectFVars (collectFVars {} type) val))

structure LetRecClosure :=
(localDecls : Array LocalDecl)
(closed     : Expr) -- expression used to replace occurrences of the let-rec FVarId
(toLift     : LetRecToLift)

private def mkLetRecClosureFor (toLift : LetRecToLift) (freeVars : Array FVarId) : TermElabM LetRecClosure := do
let lctx := toLift.lctx;
withLCtx lctx toLift.localInstances do
lambdaTelescope toLift.val fun xs val => do
  type ← instantiateForall toLift.type xs;
  lctx ← getLCtx;
  (_, s) ← (mkClosureForAux freeVars).run { localDecls := xs.map fun x => lctx.get! x.fvarId! };
  let type := Closure.mkForall s.localDecls $ Closure.mkForall s.newLetDecls type;
  let val  := Closure.mkLambda s.localDecls $ Closure.mkLambda s.newLetDecls val;
  let c    := mkAppN (Lean.mkConst toLift.declName) s.exprArgs;
  assignExprMVar toLift.mvarId c;
  pure ⟨s.newLocalDecls, c, { toLift with val := val, type := type }⟩

private def mkLetRecClosures (letRecsToLift : List LetRecToLift) (freeVarMap : FreeVarMap) : TermElabM (List LetRecClosure) :=
letRecsToLift.mapM fun toLift => mkLetRecClosureFor toLift (freeVarMap.find? toLift.fvarId).get!

/- Mapping from FVarId of mutually recursive functions being defined to "closure" expression. -/
abbrev Replacement := NameMap Expr

def insertReplacementForMainFns (r : Replacement) (sectionVars : Array Expr) (mainHeaders : Array DefViewElabHeader) (mainFVars : Array Expr) : Replacement :=
mainFVars.size.fold
  (fun i (r : Replacement) =>
    r.insert (mainFVars.get! i).fvarId! (mkAppN (Lean.mkConst (mainHeaders.get! i).declName) sectionVars))
  r

def insertReplacementForLetRecs (r : Replacement) (letRecClosures : List LetRecClosure) : Replacement :=
letRecClosures.foldl (fun (r : Replacement) c => r.insert c.toLift.fvarId c.closed) r

def Replacement.apply (r : Replacement) (e : Expr) : Expr :=
e.replace fun e => match e with
  | Expr.fvar fvarId _ => match r.find? fvarId with
    | some c => some c
    | _      => none
  | _ => none

def pushMain (preDecls : Array PreDeclaration) (sectionVars : Array Expr) (mainHeaders : Array DefViewElabHeader) (mainVals : Array Expr)
    : TermElabM (Array PreDeclaration) :=
mainHeaders.size.foldM
  (fun i (preDecls : Array PreDeclaration) => do
    let header := mainHeaders.get! i;
    val  ← mkLambdaFVars sectionVars (mainVals.get! i);
    type ← mkForallFVars sectionVars header.type;
    pure $ preDecls.push {
      kind      := header.kind,
      declName  := header.declName,
      lparams   := [], -- we set it later
      modifiers := header.modifiers,
      type      := type,
      value     := val
    })
  preDecls

def pushLetRecs (preDecls : Array PreDeclaration) (letRecClosures : List LetRecClosure) (kind : DefKind) (modifiers : Modifiers) : Array PreDeclaration :=
letRecClosures.foldl
  (fun (preDecls : Array PreDeclaration) (c : LetRecClosure) =>
    let type := Closure.mkForall c.localDecls c.toLift.type;
    let val  := Closure.mkLambda c.localDecls c.toLift.val;
    preDecls.push {
      kind      := kind,
      declName  := c.toLift.declName,
      lparams   := [], -- we set it later
      modifiers := { modifiers with attrs := c.toLift.attrs },
      type      := type,
      value     := val
    })
  preDecls

def getKindForLetRecs (mainHeaders : Array DefViewElabHeader) : DefKind :=
if mainHeaders.any fun h => h.kind.isTheorem then DefKind.«theorem»
else DefKind.«def»

def getModifiersForLetRecs (mainHeaders : Array DefViewElabHeader) : Modifiers :=
{ isNoncomputable := mainHeaders.any fun h => h.modifiers.isNoncomputable,
  isPartial       := mainHeaders.any fun h => h.modifiers.isPartial,
  isUnsafe        := mainHeaders.any fun h => h.modifiers.isUnsafe }

/-
- `sectionVars`:   The section variables used in the `mutual` block.
- `mainHeaders`:   The elaborated header of the top-level definitions being defined by the mutual block.
- `mainFVars`:     The auxiliary variables used to represent the top-level definitions being defined by the mutual block.
- `mainVals`:      The elaborated value for the top-level definitions
- `letRecsToLift`: The let-rec's definitions that need to be lifted
-/
def main (sectionVars : Array Expr) (mainHeaders : Array DefViewElabHeader) (mainFVars : Array Expr) (mainVals : Array Expr) (letRecsToLift : List LetRecToLift)
    : TermElabM (Array PreDeclaration) := do
-- Store in recFVarIds the fvarId of every function being defined by the mutual block.
let mainFVarIds := mainFVars.map Expr.fvarId!;
let recFVarIds  := (letRecsToLift.toArray.map fun toLift => toLift.fvarId) ++ mainFVarIds;
-- Compute the set of free variables (excluding `recFVarIds`) for each let-rec.
mctx ← getMCtx;
let freeVarMap := mkFreeVarMap mctx sectionVars mainFVarIds recFVarIds letRecsToLift;
resetZetaFVarIds;
withTrackingZeta do
-- By checking `toLift.type` and `toLift.val` we populate `zetaFVarIds`. See comments at `src/Lean/Meta/Closure.lean`.
letRecsToLift.forM fun toLift => withLCtx toLift.lctx toLift.localInstances do { liftM $ check toLift.type; liftM $ check toLift.val };
letRecClosures ← mkLetRecClosures letRecsToLift freeVarMap;
-- mkLetRecClosures assign metavariables that were placeholders for the lifted declarations.
mainVals    ← mainVals.mapM instantiateMVars;
mainHeaders ← mainHeaders.mapM instantiateMVarsAtHeader;
letRecClosures ← letRecClosures.mapM fun closure => do { toLift ← instantiateMVarsAtLetRecToLift closure.toLift; pure { closure with toLift := toLift } };
-- Replace fvarIds for functions being defined with closed terms
let r              := insertReplacementForMainFns {} sectionVars mainHeaders mainFVars;
let r              := insertReplacementForLetRecs r letRecClosures;
let mainVals       := mainVals.map r.apply;
let mainHeaders    := mainHeaders.map fun h => { h with type := r.apply h.type };
let letRecClosures := letRecClosures.map fun c => { c with toLift := { c.toLift with type := r.apply c.toLift.type, val := r.apply c.toLift.val } };
let letRecKind     := getKindForLetRecs mainHeaders;
let letRecMods     := getModifiersForLetRecs mainHeaders;
pushMain (pushLetRecs #[] letRecClosures letRecKind letRecMods) sectionVars mainHeaders mainVals

end MutualClosure

private def getAllUserLevelNames (headers : Array DefViewElabHeader) : List Name :=
if h : 0 < headers.size then
  -- Recall that all top-level functions must have the same levels. See `check` method above
  (headers.get ⟨0, h⟩).levelNames
else
  []

private def instantiateMVarsAtPreDecls (preDecls : Array PreDeclaration) : TermElabM (Array PreDeclaration) :=
preDecls.mapM fun preDecl => do
  type  ← instantiateMVars preDecl.type;
  value ← instantiateMVars preDecl.value;
  pure { preDecl with type := type, value := value }

private def levelMVarToParamExpr (e : Expr) : StateRefT Nat TermElabM Expr := do
nextIdx ← get;
(e, nextIdx) ← liftM $ levelMVarToParam e nextIdx;
set nextIdx;
pure e

private def levelMVarToParamPreDeclsAux (preDecls : Array PreDeclaration) : StateRefT Nat TermElabM (Array PreDeclaration) :=
preDecls.mapM fun preDecl => do
  type  ← levelMVarToParamExpr preDecl.type;
  value ← levelMVarToParamExpr preDecl.value;
  pure { preDecl with type := type, value := value }

private def levelMVarToParamPreDecls (preDecls : Array PreDeclaration) : TermElabM (Array PreDeclaration) :=
(levelMVarToParamPreDeclsAux preDecls).run' 1

private def collectLevelParamsExpr (e : Expr) : StateM CollectLevelParams.State Unit := do
modify fun s => collectLevelParams s e

private def getLevelParamsPreDecls (preDecls : Array PreDeclaration) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (List Name) :=
let (_, s) := StateT.run
  (preDecls.forM fun preDecl => do {
    collectLevelParamsExpr preDecl.type;
    collectLevelParamsExpr preDecl.value })
  {};
match sortDeclLevelParams scopeLevelNames allUserLevelNames s.params with
| Except.error msg      => throwError msg
| Except.ok levelParams => pure levelParams

private def shareCommon (preDecls : Array PreDeclaration) : Array PreDeclaration :=
let result : Std.ShareCommonM (Array PreDeclaration) :=
  preDecls.mapM fun preDecl => do {
    type  ← Std.withShareCommon preDecl.type;
    value ← Std.withShareCommon preDecl.value;
    pure { preDecl with type := type, value := value }
  };
result.run

private def fixLevelParams (preDecls : Array PreDeclaration) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (Array PreDeclaration) := do
let preDecls := shareCommon preDecls;
lparams ← getLevelParamsPreDecls preDecls scopeLevelNames allUserLevelNames;
let us := lparams.map mkLevelParam;
let fixExpr (e : Expr) : Expr :=
  e.replace fun c => match c with
    | Expr.const declName _ _ => if preDecls.any fun preDecl => preDecl.declName == declName then some $ Lean.mkConst declName us else none
    | _ => none;
pure $ preDecls.map fun preDecl =>
  { preDecl with
    type    := fixExpr preDecl.type,
    value   := fixExpr preDecl.value,
    lparams := lparams }

private def applyAttributesOf (preDecls : Array PreDeclaration) (applicationTime : AttributeApplicationTime) : TermElabM Unit := do
preDecls.forM fun preDecl => applyAttributes preDecl.declName preDecl.modifiers.attrs applicationTime

private def addAndCompileNonRec (preDecl : PreDeclaration) : TermElabM Unit := do
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

private def addAndCompileAsUnsafe (preDecls : Array PreDeclaration) : TermElabM Unit := do
let decl := Declaration.mutualDefnDecl $ preDecls.toList.map fun preDecl => {
    name     := preDecl.declName,
    lparams  := preDecl.lparams,
    type     := preDecl.type,
    value    := preDecl.value,
    isUnsafe := true,
    hints    := ReducibilityHints.opaque
  };
ensureNoUnassignedMVars decl;
addDecl decl;
applyAttributesOf preDecls AttributeApplicationTime.afterTypeChecking;
compileDecl decl;
applyAttributesOf preDecls AttributeApplicationTime.afterCompilation;
pure ()

private def partitionNonRec (preDecls : Array PreDeclaration) : Array PreDeclaration × Array PreDeclaration :=
preDecls.partition fun predDecl =>
  Option.isNone $ predDecl.value.find? fun c => match c with
    | Expr.const declName _ _ => preDecls.any fun preDecl => preDecl.declName == declName
    | _ => false

def elabMutualDef (vars : Array Expr) (views : Array DefView) : TermElabM Unit := do
scopeLevelNames ← getLevelNames;
headers ← elabHeaders views;
let allUserLevelNames := getAllUserLevelNames headers;
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
      preDecls ← MutualClosure.main vars headers funFVars values letRecsToLift;
      preDecls ← levelMVarToParamPreDecls preDecls;
      preDecls ← instantiateMVarsAtPreDecls preDecls;
      preDecls ← fixLevelParams preDecls scopeLevelNames allUserLevelNames;
      preDecls.forM fun preDecl => trace `Elab.definition.body fun _ => preDecl.declName ++ " : " ++ preDecl.type ++ " :=" ++ Format.line ++ preDecl.value;
      let (preDeclsNonRec, preDecls) := partitionNonRec preDecls;
      preDeclsNonRec.forM addAndCompileNonRec;
      -- TODO
      addAndCompileAsUnsafe preDecls

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
