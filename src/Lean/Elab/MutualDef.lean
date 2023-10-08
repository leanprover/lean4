/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term
import Lean.Meta.Closure
import Lean.Meta.Check
import Lean.Meta.Transform
import Lean.PrettyPrinter.Delaborator.Options
import Lean.Elab.Command
import Lean.Elab.Match
import Lean.Elab.DefView
import Lean.Elab.Deriving.Basic
import Lean.Elab.PreDefinition.Main
import Lean.Elab.DeclarationRange

namespace Lean.Elab
open Lean.Parser.Term

/-- `DefView` after elaborating the header. -/
structure DefViewElabHeader where
  ref           : Syntax
  modifiers     : Modifiers
  /-- Stores whether this is the header of a definition, theorem, ... -/
  kind          : DefKind
  /--
    Short name. Recall that all declarations in Lean 4 are potentially recursive. We use `shortDeclName` to refer
    to them at `valueStx`, and other declarations in the same mutual block. -/
  shortDeclName : Name
  /-- Full name for this declaration. This is the name that will be added to the `Environment`. -/
  declName      : Name
  /-- Universe level parameter names explicitly provided by the user. -/
  levelNames    : List Name
  /-- Syntax objects for the binders occurring before `:`, we use them to populate the `InfoTree` when elaborating `valueStx`. -/
  binderIds     : Array Syntax
  /-- Number of parameters before `:`, it also includes auto-implicit parameters automatically added by Lean. -/
  numParams     : Nat
  /-- Type including parameters. -/
  type          : Expr
  /-- `Syntax` object the body/value of the definition. -/
  valueStx      : Syntax
  deriving Inhabited

namespace Term
open Meta

private def checkModifiers (m₁ m₂ : Modifiers) : TermElabM Unit := do
  unless m₁.isUnsafe == m₂.isUnsafe do
    throwError "cannot mix unsafe and safe definitions"
  unless m₁.isNoncomputable == m₂.isNoncomputable do
    throwError "cannot mix computable and non-computable definitions"
  unless m₁.isPartial == m₂.isPartial do
    throwError "cannot mix partial and non-partial definitions"

private def checkKinds (k₁ k₂ : DefKind) : TermElabM Unit := do
  unless k₁.isExample == k₂.isExample do
    throwError "cannot mix examples and definitions" -- Reason: we should discard examples
  unless k₁.isTheorem == k₂.isTheorem do
    throwError "cannot mix theorems and definitions" -- Reason: we will eventually elaborate theorems in `Task`s.

private def check (prevHeaders : Array DefViewElabHeader) (newHeader : DefViewElabHeader) : TermElabM Unit := do
  if newHeader.kind.isTheorem && newHeader.modifiers.isUnsafe then
    throwError "'unsafe' theorems are not allowed"
  if newHeader.kind.isTheorem && newHeader.modifiers.isPartial then
    throwError "'partial' theorems are not allowed, 'partial' is a code generation directive"
  if newHeader.kind.isTheorem && newHeader.modifiers.isNoncomputable then
    throwError "'theorem' subsumes 'noncomputable', code is not generated for theorems"
  if newHeader.modifiers.isNoncomputable && newHeader.modifiers.isUnsafe then
    throwError "'noncomputable unsafe' is not allowed"
  if newHeader.modifiers.isNoncomputable && newHeader.modifiers.isPartial then
    throwError "'noncomputable partial' is not allowed"
  if newHeader.modifiers.isPartial && newHeader.modifiers.isUnsafe then
    throwError "'unsafe' subsumes 'partial'"
  if h : 0 < prevHeaders.size then
    let firstHeader := prevHeaders.get ⟨0, h⟩
    try
      unless newHeader.levelNames == firstHeader.levelNames do
        throwError "universe parameters mismatch"
      checkModifiers newHeader.modifiers firstHeader.modifiers
      checkKinds newHeader.kind firstHeader.kind
    catch
       | .error ref msg => throw (.error ref m!"invalid mutually recursive definitions, {msg}")
       | ex => throw ex
  else
    pure ()

private def registerFailedToInferDefTypeInfo (type : Expr) (ref : Syntax) : TermElabM Unit :=
  registerCustomErrorIfMVar type ref "failed to infer definition type"

/--
  Return `some [b, c]` if the given `views` are representing a declaration of the form
  ```
  opaque a b c : Nat
  ```  -/
private def isMultiConstant? (views : Array DefView) : Option (List Name) :=
  if views.size == 1 &&
     views[0]!.kind == .opaque &&
     views[0]!.binders.getArgs.size > 0 &&
     views[0]!.binders.getArgs.all (·.isIdent) then
    some (views[0]!.binders.getArgs.toList.map (·.getId))
  else
    none

private def getPendindMVarErrorMessage (views : Array DefView) : String :=
  match isMultiConstant? views with
  | some ids =>
    let idsStr := ", ".intercalate <| ids.map fun id => s!"`{id}`"
    let paramsStr := ", ".intercalate <| ids.map fun id => s!"`({id} : _)`"
    s!"\nrecall that you cannot declare multiple constants in a single declaration. The identifier(s) {idsStr} are being interpreted as parameters {paramsStr}"
  | none =>
    "\nwhen the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed"

/--
Convert terms of the form `OfNat <type> (OfNat.ofNat Nat <num> ..)` into `OfNat <type> <num>`.
We use this method on instance declaration types.
The motivation is to address a recurrent mistake when users forget to use `nat_lit` when declaring `OfNat` instances.
See issues #1389 and #875
-/
private def cleanupOfNat (type : Expr) : MetaM Expr := do
  Meta.transform type fun e => do
    if !e.isAppOfArity ``OfNat 2 then return .continue
    let arg ← instantiateMVars e.appArg!
    if !arg.isAppOfArity ``OfNat.ofNat 3 then return .continue
    let argArgs := arg.getAppArgs
    if !argArgs[0]!.isConstOf ``Nat then return .continue
    let eNew := mkApp e.appFn! argArgs[1]!
    return .done eNew

/-- Elaborate only the declaration headers. We have to elaborate the headers first because we support mutually recursive declarations in Lean 4. -/
private def elabHeaders (views : Array DefView) : TermElabM (Array DefViewElabHeader) := do
  let expandedDeclIds ← views.mapM fun view => withRef view.ref do
    Term.expandDeclId (← getCurrNamespace) (← getLevelNames) view.declId view.modifiers
  withAutoBoundImplicitForbiddenPred (fun n => expandedDeclIds.any (·.shortName == n)) do
    let mut headers := #[]
    for view in views, ⟨shortDeclName, declName, levelNames⟩ in expandedDeclIds do
      let newHeader ← withRef view.ref do
        addDeclarationRanges declName view.ref
        applyAttributesAt declName view.modifiers.attrs .beforeElaboration
        withDeclName declName <| withAutoBoundImplicit <| withLevelNames levelNames <|
          elabBindersEx view.binders.getArgs fun xs => do
            let refForElabFunType := view.value
            let mut type ← match view.type? with
              | some typeStx =>
                let type ← elabType typeStx
                registerFailedToInferDefTypeInfo type typeStx
                pure type
              | none =>
                let hole := mkHole refForElabFunType
                let type ← elabType hole
                trace[Elab.definition] ">> type: {type}\n{type.mvarId!}"
                registerFailedToInferDefTypeInfo type refForElabFunType
                pure type
            Term.synthesizeSyntheticMVarsNoPostponing
            if view.isInstance then
              type ← cleanupOfNat type
            let (binderIds, xs) := xs.unzip
            -- TODO: add forbidden predicate using `shortDeclName` from `views`
            let xs ← addAutoBoundImplicits xs
            type ← mkForallFVars' xs type
            type ← instantiateMVars type
            let levelNames ← getLevelNames
            if view.type?.isSome then
              let pendingMVarIds ← getMVars type
              discard <| logUnassignedUsingErrorInfos pendingMVarIds <|
                getPendindMVarErrorMessage views
            let newHeader := {
              ref           := view.ref
              modifiers     := view.modifiers
              kind          := view.kind
              shortDeclName := shortDeclName
              declName, type, levelNames, binderIds
              numParams     := xs.size
              valueStx      := view.value : DefViewElabHeader }
            check headers newHeader
            return newHeader
      headers := headers.push newHeader
    return headers

/--
  Create auxiliary local declarations `fs` for the given hearders using their `shortDeclName` and `type`, given hearders, and execute `k fs`.
  The new free variables are tagged as `auxDecl`.
  Remark: `fs.size = headers.size`.
-/
private partial def withFunLocalDecls {α} (headers : Array DefViewElabHeader) (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec loop (i : Nat) (fvars : Array Expr) := do
    if h : i < headers.size then
      let header := headers.get ⟨i, h⟩
      if header.modifiers.isNonrec then
        loop (i+1) fvars
      else
        withAuxDecl header.shortDeclName header.type header.declName fun fvar => loop (i+1) (fvars.push fvar)
    else
      k fvars
  loop 0 #[]

private def expandWhereStructInst : Macro
  | `(Parser.Command.whereStructInst|where $[$decls:letDecl];* $[$whereDecls?:whereDecls]?) => do
    let letIdDecls ← decls.mapM fun stx => match stx with
      | `(letDecl|$_decl:letPatDecl) => Macro.throwErrorAt stx "patterns are not allowed here"
      | `(letDecl|$decl:letEqnsDecl) => expandLetEqnsDecl decl (useExplicit := false)
      | `(letDecl|$decl:letIdDecl)   => pure decl
      | _                            => Macro.throwUnsupported
    let structInstFields ← letIdDecls.mapM fun
      | stx@`(letIdDecl|$id:ident $binders* $[: $ty?]? := $val) => withRef stx do
        let mut val := val
        if let some ty := ty? then
          val ← `(($val : $ty))
        -- HACK: this produces invalid syntax, but the fun elaborator supports letIdBinders as well
        have : Coe (TSyntax ``letIdBinder) (TSyntax ``funBinder) := ⟨(⟨·⟩)⟩
        val ← if binders.size > 0 then `(fun $binders* => $val) else pure val
        `(structInstField|$id:ident := $val)
      | stx@`(letIdDecl|_ $_* $[: $_]? := $_) => Macro.throwErrorAt stx "'_' is not allowed here"
      | _ => Macro.throwUnsupported
    let body ← `({ $structInstFields,* })
    match whereDecls? with
    | some whereDecls => expandWhereDecls whereDecls body
    | none => return body
  | _ => Macro.throwUnsupported

/-
Recall that
```
def declValSimple    := leading_parser " :=\n" >> termParser >> optional Term.whereDecls
def declValEqns      := leading_parser Term.matchAltsWhereDecls
def declVal          := declValSimple <|> declValEqns <|> Term.whereDecls
```
-/
private def declValToTerm (declVal : Syntax) : MacroM Syntax := withRef declVal do
  if declVal.isOfKind ``Parser.Command.declValSimple then
    expandWhereDeclsOpt declVal[2] declVal[1]
  else if declVal.isOfKind ``Parser.Command.declValEqns then
    expandMatchAltsWhereDecls declVal[0]
  else if declVal.isOfKind ``Parser.Command.whereStructInst then
    expandWhereStructInst declVal
  else if declVal.isMissing then
    Macro.throwErrorAt declVal "declaration body is missing"
  else
    Macro.throwErrorAt declVal "unexpected declaration body"

private def elabFunValues (headers : Array DefViewElabHeader) : TermElabM (Array Expr) :=
  headers.mapM fun header => withDeclName header.declName <| withLevelNames header.levelNames do
    let valStx ← liftMacroM <| declValToTerm header.valueStx
    forallBoundedTelescope header.type header.numParams fun xs type => do
      -- Add new info nodes for new fvars. The server will detect all fvars of a binder by the binder's source location.
      for i in [0:header.binderIds.size] do
        -- skip auto-bound prefix in `xs`
        addLocalVarInfo header.binderIds[i]! xs[header.numParams - header.binderIds.size + i]!
      let val ← elabTermEnsuringType valStx type
      mkLambdaFVars xs val

private def collectUsed (headers : Array DefViewElabHeader) (values : Array Expr) (toLift : List LetRecToLift)
    : StateRefT CollectFVars.State MetaM Unit := do
  headers.forM fun header => header.type.collectFVars
  values.forM fun val => val.collectFVars
  toLift.forM fun letRecToLift => do
    letRecToLift.type.collectFVars
    letRecToLift.val.collectFVars

private def removeUnusedVars (vars : Array Expr) (headers : Array DefViewElabHeader) (values : Array Expr) (toLift : List LetRecToLift)
    : TermElabM (LocalContext × LocalInstances × Array Expr) := do
  let (_, used) ← (collectUsed headers values toLift).run {}
  removeUnused vars used

private def withUsed {α} (vars : Array Expr) (headers : Array DefViewElabHeader) (values : Array Expr) (toLift : List LetRecToLift)
    (k : Array Expr → TermElabM α) : TermElabM α := do
  let (lctx, localInsts, vars) ← removeUnusedVars vars headers values toLift
  withLCtx lctx localInsts <| k vars

private def isExample (views : Array DefView) : Bool :=
  views.any (·.kind.isExample)

private def isTheorem (views : Array DefView) : Bool :=
  views.any (·.kind.isTheorem)

private def instantiateMVarsAtHeader (header : DefViewElabHeader) : TermElabM DefViewElabHeader := do
  let type ← instantiateMVars header.type
  pure { header with type := type }

private def instantiateMVarsAtLetRecToLift (toLift : LetRecToLift) : TermElabM LetRecToLift := do
  let type ← instantiateMVars toLift.type
  let val ← instantiateMVars toLift.val
  pure { toLift with type, val }

private def typeHasRecFun (type : Expr) (funFVars : Array Expr) (letRecsToLift : List LetRecToLift) : Option FVarId :=
  let occ? := type.find? fun e => match e with
    | Expr.fvar fvarId => funFVars.contains e || letRecsToLift.any fun toLift => toLift.fvarId == fvarId
    | _ => false
  match occ? with
  | some (Expr.fvar fvarId) => some fvarId
  | _ => none

private def getFunName (fvarId : FVarId) (letRecsToLift : List LetRecToLift) : TermElabM Name := do
  match (← fvarId.findDecl?) with
  | some decl => return decl.userName
  | none =>
    /- Recall that the FVarId of nested let-recs are not in the current local context. -/
    match letRecsToLift.findSome? fun toLift => if toLift.fvarId == fvarId then some toLift.shortDeclName else none with
    | none   => throwError "unknown function"
    | some n => return n

/--
Ensures that the of let-rec definition types do not contain functions being defined.
In principle, this test can be improved. We could perform it after we separate the set of functions is strongly connected components.
However, this extra complication doesn't seem worth it.
-/
private def checkLetRecsToLiftTypes (funVars : Array Expr) (letRecsToLift : List LetRecToLift) : TermElabM Unit :=
  letRecsToLift.forM fun toLift =>
    match typeHasRecFun toLift.type funVars letRecsToLift with
    | none        => pure ()
    | some fvarId => do
      let fnName ← getFunName fvarId letRecsToLift
      throwErrorAt toLift.ref "invalid type in 'let rec', it uses '{fnName}' which is being defined simultaneously"

namespace MutualClosure

/-- A mapping from FVarId to Set of FVarIds. -/
abbrev UsedFVarsMap := FVarIdMap FVarIdSet

/--
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
private def mkInitialUsedFVarsMap [Monad m] [MonadMCtx m] (sectionVars : Array Expr) (mainFVarIds : Array FVarId) (letRecsToLift : Array LetRecToLift)
    : m UsedFVarsMap := do
  let mut sectionVarSet := {}
  for var in sectionVars do
    sectionVarSet := sectionVarSet.insert var.fvarId!
  let mut usedFVarMap := {}
  for mainFVarId in mainFVarIds do
    usedFVarMap := usedFVarMap.insert mainFVarId sectionVarSet
  for toLift in letRecsToLift do
    let state := Lean.collectFVars {} toLift.val
    let state := Lean.collectFVars state toLift.type
    let mut set := state.fvarSet
    /- toLift.val may contain metavariables that are placeholders for nested let-recs. We should collect the fvarId
       for the associated let-rec because we need this information to compute the fixpoint later. -/
    let mvarIds := (toLift.val.collectMVars {}).result
    for mvarId in mvarIds do
      match (← letRecsToLift.findSomeM? fun (toLift : LetRecToLift) => return if toLift.mvarId == (← getDelayedMVarRoot mvarId) then some toLift.fvarId else none) with
      | some fvarId => set := set.insert fvarId
      | none        => pure ()
    usedFVarMap := usedFVarMap.insert toLift.fvarId set
  return usedFVarMap

/-!
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

structure State where
  usedFVarsMap : UsedFVarsMap := {}
  modified     : Bool         := false

abbrev M := ReaderT (Array FVarId) $ StateM State

private def isModified : M Bool := do pure (← get).modified
private def resetModified : M Unit := modify fun s => { s with modified := false }
private def markModified : M Unit := modify fun s => { s with modified := true }
private def getUsedFVarsMap : M UsedFVarsMap := do pure (← get).usedFVarsMap
private def modifyUsedFVars (f : UsedFVarsMap → UsedFVarsMap) : M Unit := modify fun s => { s with usedFVarsMap := f s.usedFVarsMap }

-- merge s₂ into s₁
private def merge (s₁ s₂ : FVarIdSet) : M FVarIdSet :=
  s₂.foldM (init := s₁) fun s₁ k => do
    if s₁.contains k then
      return s₁
    else
      markModified
      return s₁.insert k

private def updateUsedVarsOf (fvarId : FVarId) : M Unit := do
  let usedFVarsMap ← getUsedFVarsMap
  match usedFVarsMap.find? fvarId with
  | none         => return ()
  | some fvarIds =>
    let fvarIdsNew ← fvarIds.foldM (init := fvarIds) fun fvarIdsNew fvarId' => do
      if fvarId == fvarId' then
        return fvarIdsNew
      else
        match usedFVarsMap.find? fvarId' with
        | none => return fvarIdsNew
          /- We are being sloppy here `otherFVarIds` may contain free variables that are
             not in the context of the let-rec associated with fvarId.
             We filter these out-of-context free variables later. -/
        | some otherFVarIds => merge fvarIdsNew otherFVarIds
    modifyUsedFVars fun usedFVars => usedFVars.insert fvarId fvarIdsNew

private partial def fixpoint : Unit → M Unit
  | _ => do
    resetModified
    let letRecFVarIds ← read
    letRecFVarIds.forM updateUsedVarsOf
    if (← isModified) then
      fixpoint ()

def run (letRecFVarIds : Array FVarId) (usedFVarsMap : UsedFVarsMap) : UsedFVarsMap :=
  let (_, s) := fixpoint () |>.run letRecFVarIds |>.run { usedFVarsMap := usedFVarsMap }
  s.usedFVarsMap

end FixPoint

abbrev FreeVarMap := FVarIdMap (Array FVarId)

private def mkFreeVarMap [Monad m] [MonadMCtx m]
    (sectionVars : Array Expr) (mainFVarIds : Array FVarId)
    (recFVarIds : Array FVarId) (letRecsToLift : Array LetRecToLift) : m FreeVarMap := do
  let usedFVarsMap   ← mkInitialUsedFVarsMap sectionVars mainFVarIds letRecsToLift
  let letRecFVarIds  := letRecsToLift.map fun toLift => toLift.fvarId
  let usedFVarsMap   := FixPoint.run letRecFVarIds usedFVarsMap
  let mut freeVarMap := {}
  for toLift in letRecsToLift do
    let lctx       := toLift.lctx
    let fvarIdsSet := usedFVarsMap.find? toLift.fvarId |>.get!
    let fvarIds    := fvarIdsSet.fold (init := #[]) fun fvarIds fvarId =>
      if lctx.contains fvarId && !recFVarIds.contains fvarId then
        fvarIds.push fvarId
      else
        fvarIds
    freeVarMap := freeVarMap.insert toLift.fvarId fvarIds
  return freeVarMap

structure ClosureState where
  newLocalDecls : Array LocalDecl := #[]
  localDecls    : Array LocalDecl := #[]
  newLetDecls   : Array LocalDecl := #[]
  exprArgs      : Array Expr      := #[]

private def pickMaxFVar? (lctx : LocalContext) (fvarIds : Array FVarId) : Option FVarId :=
  fvarIds.getMax? fun fvarId₁ fvarId₂ => (lctx.get! fvarId₁).index < (lctx.get! fvarId₂).index

private def preprocess (e : Expr) : TermElabM Expr := do
  let e ← instantiateMVars e
  -- which let-decls are dependent. We say a let-decl is dependent if its lambda abstraction is type incorrect.
  Meta.check e
  pure e

/-- Push free variables in `s` to `toProcess` if they are not already there. -/
private def pushNewVars (toProcess : Array FVarId) (s : CollectFVars.State) : Array FVarId :=
  s.fvarSet.fold (init := toProcess) fun toProcess fvarId =>
    if toProcess.contains fvarId then toProcess else toProcess.push fvarId

private def pushLocalDecl (toProcess : Array FVarId) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo) (kind : LocalDeclKind)
    : StateRefT ClosureState TermElabM (Array FVarId) := do
  let type ← preprocess type
  modify fun s => { s with
    newLocalDecls := s.newLocalDecls.push <| LocalDecl.cdecl default fvarId userName type bi kind
    exprArgs      := s.exprArgs.push (mkFVar fvarId)
  }
  return pushNewVars toProcess (collectFVars {} type)

private partial def mkClosureForAux (toProcess : Array FVarId) : StateRefT ClosureState TermElabM Unit := do
  let lctx ← getLCtx
  match pickMaxFVar? lctx toProcess with
  | none        => return ()
  | some fvarId =>
    trace[Elab.definition.mkClosure] "toProcess: {toProcess.map mkFVar}, maxVar: {mkFVar fvarId}"
    let toProcess := toProcess.erase fvarId
    let localDecl ← fvarId.getDecl
    match localDecl with
    | .cdecl _ _ userName type bi k =>
      let toProcess ← pushLocalDecl toProcess fvarId userName type bi k
      mkClosureForAux toProcess
    | .ldecl _ _ userName type val _ k =>
      let zetaFVarIds ← getZetaFVarIds
      if !zetaFVarIds.contains fvarId then
        /- Non-dependent let-decl. See comment at src/Lean/Meta/Closure.lean -/
        let toProcess ← pushLocalDecl toProcess fvarId userName type .default k
        mkClosureForAux toProcess
      else
        /- Dependent let-decl. -/
        let type ← preprocess type
        let val  ← preprocess val
        modify fun s => { s with
          newLetDecls   := s.newLetDecls.push <| .ldecl default fvarId userName type val false k,
          /- We don't want to interleave let and lambda declarations in our closure. So, we expand any occurrences of fvarId
             at `newLocalDecls` and `localDecls` -/
          newLocalDecls := s.newLocalDecls.map (·.replaceFVarId fvarId val)
          localDecls := s.localDecls.map (·.replaceFVarId fvarId val)
        }
        mkClosureForAux (pushNewVars toProcess (collectFVars (collectFVars {} type) val))

private partial def mkClosureFor (freeVars : Array FVarId) (localDecls : Array LocalDecl) : TermElabM ClosureState := do
  let (_, s) ← mkClosureForAux freeVars |>.run { localDecls := localDecls }
  return { s with
    newLocalDecls := s.newLocalDecls.reverse
    newLetDecls   := s.newLetDecls.reverse
    exprArgs      := s.exprArgs.reverse
  }

structure LetRecClosure where
  ref        : Syntax
  localDecls : Array LocalDecl
  /-- Expression used to replace occurrences of the let-rec `FVarId`. -/
  closed     : Expr
  toLift     : LetRecToLift

private def mkLetRecClosureFor (toLift : LetRecToLift) (freeVars : Array FVarId) : TermElabM LetRecClosure := do
  let lctx := toLift.lctx
  withLCtx lctx toLift.localInstances do
  lambdaTelescope toLift.val fun xs val => do
    /-
      Recall that `toLift.type` and `toLift.value` may have different binder annotations.
      See issue #1377 for an example.
    -/
    let userNameAndBinderInfos ← forallBoundedTelescope toLift.type xs.size fun xs _ =>
      xs.mapM fun x => do
        let localDecl ← x.fvarId!.getDecl
        return (localDecl.userName, localDecl.binderInfo)
    /- Auxiliary map for preserving binder user-facing names and `BinderInfo` for types. -/
    let mut userNameBinderInfoMap : FVarIdMap (Name × BinderInfo) := {}
    for x in xs, (userName, bi) in userNameAndBinderInfos do
      userNameBinderInfoMap := userNameBinderInfoMap.insert x.fvarId! (userName, bi)
    let type ← instantiateForall toLift.type xs
    let lctx ← getLCtx
    let s ← mkClosureFor freeVars <| xs.map fun x => lctx.get! x.fvarId!
    /- Apply original type binder info and user-facing names to local declarations. -/
    let typeLocalDecls := s.localDecls.map fun localDecl =>
      if let some (userName, bi) := userNameBinderInfoMap.find? localDecl.fvarId then
        localDecl.setBinderInfo bi |>.setUserName userName
      else
        localDecl
    let type := Closure.mkForall typeLocalDecls <| Closure.mkForall s.newLetDecls type
    let val  := Closure.mkLambda s.localDecls <| Closure.mkLambda s.newLetDecls val
    let c    := mkAppN (Lean.mkConst toLift.declName) s.exprArgs
    toLift.mvarId.assign c
    return {
      ref        := toLift.ref
      localDecls := s.newLocalDecls
      closed     := c
      toLift     := { toLift with val, type }
    }

private def mkLetRecClosures (sectionVars : Array Expr) (mainFVarIds : Array FVarId) (recFVarIds : Array FVarId) (letRecsToLift : Array LetRecToLift) : TermElabM (List LetRecClosure) := do
  -- Compute the set of free variables (excluding `recFVarIds`) for each let-rec.
  let mut letRecsToLift := letRecsToLift
  let mut freeVarMap    ← mkFreeVarMap sectionVars mainFVarIds recFVarIds letRecsToLift
  let mut result := #[]
  for i in [:letRecsToLift.size] do
    if letRecsToLift[i]!.val.hasExprMVar then
      -- This can happen when this particular let-rec has nested let-rec that have been resolved in previous iterations.
      -- This code relies on the fact that nested let-recs occur before the outer most let-recs at `letRecsToLift`.
      -- Unresolved nested let-recs appear as metavariables before they are resolved. See `assignExprMVar` at `mkLetRecClosureFor`
      let valNew ← instantiateMVars letRecsToLift[i]!.val
      letRecsToLift := letRecsToLift.modify i fun t => { t with val := valNew }
      -- We have to recompute the `freeVarMap` in this case. This overhead should not be an issue in practice.
      freeVarMap ← mkFreeVarMap sectionVars mainFVarIds recFVarIds letRecsToLift
    let toLift := letRecsToLift[i]!
    result := result.push (← mkLetRecClosureFor toLift (freeVarMap.find? toLift.fvarId).get!)
  return result.toList

/-- Mapping from FVarId of mutually recursive functions being defined to "closure" expression. -/
abbrev Replacement := FVarIdMap Expr

def insertReplacementForMainFns (r : Replacement) (sectionVars : Array Expr) (mainHeaders : Array DefViewElabHeader) (mainFVars : Array Expr) : Replacement :=
  mainFVars.size.fold (init := r) fun i r =>
    r.insert mainFVars[i]!.fvarId! (mkAppN (Lean.mkConst mainHeaders[i]!.declName) sectionVars)


def insertReplacementForLetRecs (r : Replacement) (letRecClosures : List LetRecClosure) : Replacement :=
  letRecClosures.foldl (init := r) fun r c =>
    r.insert c.toLift.fvarId c.closed

def Replacement.apply (r : Replacement) (e : Expr) : Expr :=
  e.replace fun e => match e with
    | .fvar fvarId => match r.find? fvarId with
      | some c => some c
      | _      => none
    | _ => none

def pushMain (preDefs : Array PreDefinition) (sectionVars : Array Expr) (mainHeaders : Array DefViewElabHeader) (mainVals : Array Expr)
    : TermElabM (Array PreDefinition) :=
  mainHeaders.size.foldM (init := preDefs) fun i preDefs => do
    let header := mainHeaders[i]!
    let value ← mkLambdaFVars sectionVars mainVals[i]!
    let type ← mkForallFVars sectionVars header.type
    return preDefs.push {
      ref         := getDeclarationSelectionRef header.ref
      kind        := header.kind
      declName    := header.declName
      levelParams := [], -- we set it later
      modifiers   := header.modifiers
      type, value
    }

def pushLetRecs (preDefs : Array PreDefinition) (letRecClosures : List LetRecClosure) (kind : DefKind) (modifiers : Modifiers) : MetaM (Array PreDefinition) :=
  letRecClosures.foldlM (init := preDefs) fun preDefs c => do
    let type  := Closure.mkForall c.localDecls c.toLift.type
    let value := Closure.mkLambda c.localDecls c.toLift.val
    -- Convert any proof let recs inside a `def` to `theorem` kind
    let kind ← if kind.isDefOrAbbrevOrOpaque then
      withLCtx c.toLift.lctx c.toLift.localInstances do
        return if (← inferType c.toLift.type).isProp then .theorem else kind
    else
      pure kind
    return preDefs.push {
      ref         := c.ref
      declName    := c.toLift.declName
      levelParams := [] -- we set it later
      modifiers   := { modifiers with attrs := c.toLift.attrs }
      kind, type, value
    }

def getKindForLetRecs (mainHeaders : Array DefViewElabHeader) : DefKind :=
  if mainHeaders.any fun h => h.kind.isTheorem then DefKind.«theorem»
  else DefKind.«def»

def getModifiersForLetRecs (mainHeaders : Array DefViewElabHeader) : Modifiers := {
  isNoncomputable := mainHeaders.any fun h => h.modifiers.isNoncomputable
  recKind         := if mainHeaders.any fun h => h.modifiers.isPartial then RecKind.partial else RecKind.default
  isUnsafe        := mainHeaders.any fun h => h.modifiers.isUnsafe
}

/--
- `sectionVars`:   The section variables used in the `mutual` block.
- `mainHeaders`:   The elaborated header of the top-level definitions being defined by the mutual block.
- `mainFVars`:     The auxiliary variables used to represent the top-level definitions being defined by the mutual block.
- `mainVals`:      The elaborated value for the top-level definitions
- `letRecsToLift`: The let-rec's definitions that need to be lifted
-/
def main (sectionVars : Array Expr) (mainHeaders : Array DefViewElabHeader) (mainFVars : Array Expr) (mainVals : Array Expr) (letRecsToLift : List LetRecToLift)
    : TermElabM (Array PreDefinition) := do
  -- Store in recFVarIds the fvarId of every function being defined by the mutual block.
  let letRecsToLift := letRecsToLift.toArray
  let mainFVarIds := mainFVars.map Expr.fvarId!
  let recFVarIds  := (letRecsToLift.map fun toLift => toLift.fvarId) ++ mainFVarIds
  resetZetaFVarIds
  withTrackingZeta do
    -- By checking `toLift.type` and `toLift.val` we populate `zetaFVarIds`. See comments at `src/Lean/Meta/Closure.lean`.
    let letRecsToLift ← letRecsToLift.mapM fun toLift => withLCtx toLift.lctx toLift.localInstances do
      Meta.check toLift.type
      Meta.check toLift.val
      return { toLift with val := (← instantiateMVars toLift.val), type := (← instantiateMVars toLift.type) }
    let letRecClosures ← mkLetRecClosures sectionVars mainFVarIds recFVarIds letRecsToLift
    -- mkLetRecClosures assign metavariables that were placeholders for the lifted declarations.
    let mainVals    ← mainVals.mapM (instantiateMVars ·)
    let mainHeaders ← mainHeaders.mapM instantiateMVarsAtHeader
    let letRecClosures ← letRecClosures.mapM fun closure => do pure { closure with toLift := (← instantiateMVarsAtLetRecToLift closure.toLift) }
    -- Replace fvarIds for functions being defined with closed terms
    let r              := insertReplacementForMainFns {} sectionVars mainHeaders mainFVars
    let r              := insertReplacementForLetRecs r letRecClosures
    let mainVals       := mainVals.map r.apply
    let mainHeaders    := mainHeaders.map fun h => { h with type := r.apply h.type }
    let letRecClosures := letRecClosures.map fun c => { c with toLift := { c.toLift with type := r.apply c.toLift.type, val := r.apply c.toLift.val } }
    let letRecKind     := getKindForLetRecs mainHeaders
    let letRecMods     := getModifiersForLetRecs mainHeaders
    pushMain (← pushLetRecs #[] letRecClosures letRecKind letRecMods) sectionVars mainHeaders mainVals

end MutualClosure

private def getAllUserLevelNames (headers : Array DefViewElabHeader) : List Name :=
  if h : 0 < headers.size then
    -- Recall that all top-level functions must have the same levels. See `check` method above
    (headers.get ⟨0, h⟩).levelNames
  else
    []

/-- Eagerly convert universe metavariables occurring in theorem headers to universe parameters. -/
private def levelMVarToParamHeaders (views : Array DefView) (headers : Array DefViewElabHeader) : TermElabM (Array DefViewElabHeader) := do
  let rec process : StateRefT Nat TermElabM (Array DefViewElabHeader) := do
    let mut newHeaders := #[]
    for view in views, header in headers do
      if view.kind.isTheorem then
        newHeaders ←
          withLevelNames header.levelNames do
            return newHeaders.push { header with type := (← levelMVarToParam header.type), levelNames := (← getLevelNames) }
      else
        newHeaders := newHeaders.push header
    return newHeaders
  let newHeaders ← (process).run' 1
  newHeaders.mapM fun header => return { header with type := (← instantiateMVars header.type) }

partial def checkForHiddenUnivLevels (allUserLevelNames : List Name) (preDefs : Array PreDefinition) : TermElabM Unit :=
  unless (← MonadLog.hasErrors) do
    -- We do not report this kind of error if the declaration already contains errors
    let mut sTypes : CollectLevelParams.State := {}
    let mut sValues : CollectLevelParams.State := {}
    for preDef in preDefs do
      sTypes  := collectLevelParams sTypes preDef.type
      sValues := collectLevelParams sValues preDef.value
    if sValues.params.all fun u => sTypes.params.contains u || allUserLevelNames.contains u then
      -- If all universe level occurring in values also occur in types or explicitly provided universes, then everything is fine
      -- and we just return
      return ()
    let checkPreDef (preDef : PreDefinition) : TermElabM Unit :=
      -- Otherwise, we try to produce an error message containing the expression with the offending universe
      let rec visitLevel (u : Level) : ReaderT Expr TermElabM Unit := do
        match u with
        | .succ u => visitLevel u
        | .imax u v | .max u v => visitLevel u; visitLevel v
        | .param n =>
          unless sTypes.visitedLevel.contains u || allUserLevelNames.contains n do
            let parent ← withOptions (fun o => pp.universes.set o true) do addMessageContext m!"{indentExpr (← read)}"
            let body ← withOptions (fun o => pp.letVarTypes.setIfNotSet (pp.funBinderTypes.setIfNotSet o true) true) do addMessageContext m!"{indentExpr preDef.value}"
            throwError "invalid occurrence of universe level '{u}' at '{preDef.declName}', it does not occur at the declaration type, nor it is explicit universe level provided by the user, occurring at expression{parent}\nat declaration body{body}"
        | _ => pure ()
      let rec visit (e : Expr) : ReaderT Expr (MonadCacheT ExprStructEq Unit TermElabM) Unit := do
        checkCache { val := e : ExprStructEq } fun _ => do
          match e with
          | .forallE n d b c | .lam n d b c => visit d e; withLocalDecl n c d fun x => visit (b.instantiate1 x) e
          | .letE n t v b _  => visit t e; visit v e; withLetDecl n t v fun x => visit (b.instantiate1 x) e
          | .app ..        => e.withApp fun f args => do visit f e; args.forM fun arg => visit arg e
          | .mdata _ b     => visit b e
          | .proj _ _ b    => visit b e
          | .sort u        => visitLevel u (← read)
          | .const _ us    => us.forM (visitLevel · (← read))
          | _              => pure ()
      visit preDef.value preDef.value |>.run {}
    for preDef in preDefs do
      checkPreDef preDef

def elabMutualDef (vars : Array Expr) (views : Array DefView) (hints : TerminationHints) : TermElabM Unit :=
  if isExample views then
    withoutModifyingEnv do
      -- save correct environment in info tree
      withSaveInfoContext do
        go
  else
    go
where
  go := do
    let scopeLevelNames ← getLevelNames
    let headers ← elabHeaders views
    let headers ← levelMVarToParamHeaders views headers
    let allUserLevelNames := getAllUserLevelNames headers
    withFunLocalDecls headers fun funFVars => do
      for view in views, funFVar in funFVars do
        addLocalVarInfo view.declId funFVar
      let values ←
        try
          let values ← elabFunValues headers
          Term.synthesizeSyntheticMVarsNoPostponing
          values.mapM (instantiateMVars ·)
        catch ex =>
          logException ex
          headers.mapM fun header => mkSorry header.type (synthetic := true)
      let headers ← headers.mapM instantiateMVarsAtHeader
      let letRecsToLift ← getLetRecsToLift
      let letRecsToLift ← letRecsToLift.mapM instantiateMVarsAtLetRecToLift
      checkLetRecsToLiftTypes funFVars letRecsToLift
      withUsed vars headers values letRecsToLift fun vars => do
        let preDefs ← MutualClosure.main vars headers funFVars values letRecsToLift
        for preDef in preDefs do
          trace[Elab.definition] "{preDef.declName} : {preDef.type} :=\n{preDef.value}"
        let preDefs ← withLevelNames allUserLevelNames <| levelMVarToParamPreDecls preDefs
        let preDefs ← instantiateMVarsAtPreDecls preDefs
        let preDefs ← fixLevelParams preDefs scopeLevelNames allUserLevelNames
        for preDef in preDefs do
          trace[Elab.definition] "after eraseAuxDiscr, {preDef.declName} : {preDef.type} :=\n{preDef.value}"
        checkForHiddenUnivLevels allUserLevelNames preDefs
        addPreDefinitions preDefs hints
        processDeriving headers

  processDeriving (headers : Array DefViewElabHeader) := do
    for header in headers, view in views do
      if let some classNamesStx := view.deriving? then
        for classNameStx in classNamesStx do
          let className ← resolveGlobalConstNoOverload classNameStx
          withRef classNameStx do
            unless (← processDefDeriving className header.declName) do
              throwError "failed to synthesize instance '{className}' for '{header.declName}'"

end Term
namespace Command

def elabMutualDef (ds : Array Syntax) (hints : TerminationHints) : CommandElabM Unit := do
  let views ← ds.mapM fun d => do
    let modifiers ← elabModifiers d[0]
    if ds.size > 1 && modifiers.isNonrec then
      throwErrorAt d "invalid use of 'nonrec' modifier in 'mutual' block"
    mkDefView modifiers d[1]
  runTermElabM fun vars => Term.elabMutualDef vars views hints

end Command
end Lean.Elab
