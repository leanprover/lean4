/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
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
import Lean.Elab.PreDefinition.TerminationHint
import Lean.Elab.DeclarationRange

namespace Lean.Elab
open Lean.Parser.Term

open Language

builtin_initialize
  registerTraceClass `Meta.instantiateMVars

def instantiateMVarsProfiling (e : Expr) : MetaM Expr := do
  profileitM Exception s!"instantiate metavars" (← getOptions) do
  withTraceNode `Meta.instantiateMVars (fun _ => pure e) do
    instantiateMVars e

/-- `DefView` plus header elaboration data and snapshot. -/
structure DefViewElabHeader extends DefView, DefViewElabHeaderData where
  /--
  Snapshot for incremental processing of top-level tactic block, if any.

  Invariant: if the bundle's `old?` is set, then the state *up to the start* of the tactic block is
  unchanged, i.e. reuse is possible.
  -/
  tacSnap? : Option (Language.SnapshotBundle Tactic.TacticParsedSnapshot)
  /--
  Snapshot for incremental processing of definition body.

  Invariant: if the bundle's `old?` is set, then elaboration of the body is guaranteed to result in
  the same elaboration result and state, i.e. reuse is possible.
  -/
  bodySnap? : Option (Language.SnapshotBundle (Option BodyProcessedSnapshot))
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
  if newHeader.modifiers.isNoncomputable && newHeader.modifiers.isPartial then
    throwError "'noncomputable partial' is not allowed"
  if newHeader.modifiers.isPartial && newHeader.modifiers.isUnsafe then
    throwError "'unsafe' subsumes 'partial'"
  if h : 0 < prevHeaders.size then
    let firstHeader := prevHeaders[0]
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

private def getPendingMVarErrorMessage (views : Array DefView) : String :=
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
    let arg ← instantiateMVarsProfiling e.appArg!
    if !arg.isAppOfArity ``OfNat.ofNat 3 then return .continue
    let argArgs := arg.getAppArgs
    if !argArgs[0]!.isConstOf ``Nat then return .continue
    let eNew := mkApp e.appFn! argArgs[1]!
    return .done eNew

/--
Elaborates only the declaration view headers. We have to elaborate the headers first because we
support mutually recursive declarations in Lean 4.
-/
private def elabHeaders (views : Array DefView) (expandedDeclIds : Array ExpandDeclIdResult)
    (bodyPromises : Array (IO.Promise (Option BodyProcessedSnapshot)))
    (tacPromises : Array (IO.Promise Tactic.TacticParsedSnapshot)) :
    TermElabM (Array DefViewElabHeader) := do
  withAutoBoundImplicitForbiddenPred (fun n => expandedDeclIds.any (·.shortName == n)) do
    let mut headers := #[]
    -- Can we reuse the result for a body? For starters, all headers (even those below the body)
    -- must be reusable
    let mut reuseBody := views.all (·.headerSnap?.any (·.old?.isSome))
    for view in views, ⟨shortDeclName, declName, levelNames⟩ in expandedDeclIds,
        tacPromise in tacPromises, bodyPromise in bodyPromises do
      let mut reusableResult? := none
      let mut oldBodySnap? := none
      let mut oldTacSnap? := none
      if let some snap := view.headerSnap? then
        -- by the `DefView.headerSnap?` invariant, safe to reuse results at this point, so let's
        -- wait for them!
        if let some old := snap.old?.bind (·.val.get) then
          -- Transition from `DefView.snap?` to `DefViewElabHeader.tacSnap?` invariant: if all
          -- headers and all previous bodies could be reused, then the state at the *start* of the
          -- top-level tactic block (if any) is unchanged
          let reuseTac := reuseBody
          -- Transition from `DefView.snap?` to `DefViewElabHeader.bodySnap?` invariant: if all
          -- headers and all previous bodies could be reused and this body syntax is unchanged, then
          -- we can reuse the result
          reuseBody := reuseBody &&
            view.value.eqWithInfoAndTraceReuse (← getOptions) old.bodyStx
          -- no syntax guard to store, we already did the necessary checks
          oldBodySnap? := guard reuseBody *> pure ⟨.missing, old.bodySnap⟩
          if oldBodySnap?.isNone then
            old.bodySnap.cancelRec
          oldTacSnap? := do
              guard reuseTac
              some ⟨(← old.tacStx?), (← old.tacSnap?)⟩
          let newHeader : DefViewElabHeader := { view, old.view with
            bodySnap? := none, tacSnap? := none }  -- filled below
          reusableResult? := some (newHeader, old.state)
        else
          reuseBody := false

      let mut (newHeader, newState) ←
        withTraceNode `Elab.definition.header (fun _ => pure declName) do
        withRestoreOrSaveFull reusableResult? none do
        withReuseContext view.headerRef do
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
            let xs ← addAutoBoundImplicits xs (view.declId.getTailPos? (canonicalOnly := true))
            type ← mkForallFVars' xs type
            type ← instantiateMVarsProfiling type
            let levelNames ← getLevelNames
            if view.type?.isSome then
              let pendingMVarIds ← getMVars type
              discard <| logUnassignedUsingErrorInfos pendingMVarIds <|
                getPendingMVarErrorMessage views
            let newHeader : DefViewElabHeaderData := {
              declName, shortDeclName, type, levelNames, binderIds
              numParams := xs.size
            }
            let newHeader : DefViewElabHeader := { view, newHeader with
              bodySnap? := none, tacSnap? := none }
            check headers newHeader
            return newHeader
      if let some snap := view.headerSnap? then
        let (tacStx?, newTacTask?) ← mkTacTask view.value tacPromise
        let bodySnap := {
          stx? := view.value
          reportingRange? :=
            if newTacTask?.isSome then
              -- Only use first line of body as range when we have incremental tactics as otherwise we
              -- would cover their progress
              view.ref.getPos?.map fun pos => ⟨pos, pos⟩
            else
              getBodyTerm? view.value |>.getD view.value |>.getRange?
          task := bodyPromise.resultD default
        }
        snap.new.resolve <| some {
          diagnostics :=
            (← Language.Snapshot.Diagnostics.ofMessageLog (← Core.getAndEmptyMessageLog))
          moreSnaps := (← Core.getAndEmptySnapshotTasks)
          view := newHeader.toDefViewElabHeaderData
          state := newState
          tacStx?
          tacSnap? := newTacTask?
          bodyStx := view.value
          bodySnap
        }
        newHeader := { newHeader with
          -- We should only forward the promise if we are actually waiting on the
          -- corresponding task; otherwise, diagnostics assigned to it will be lost
          tacSnap? := guard newTacTask?.isSome *> some { old? := oldTacSnap?, new := tacPromise }
          bodySnap? := some { old? := oldBodySnap?, new := bodyPromise }
        }
      headers := headers.push newHeader
    return headers
where
  getBodyTerm? (stx : Syntax) : Option Syntax := do
    -- TODO: does not work with partial syntax
    --| `(Parser.Command.declVal| := $body $_suffix:suffix) => body
    guard (stx.isOfKind ``Parser.Command.declValSimple)
    let body := stx[1]
    let whereDeclsOpt := stx[3]
    -- We currently disable incrementality in presence of `where` as we would have to handle the
    -- generated leading `let rec` specially
    guard whereDeclsOpt.isNone
    return body

  /--
  If `body` allows for incremental tactic reporting and reuse, creates a snapshot task out of the
  passed promise with appropriate range, otherwise immediately resolves the promise to a dummy
  value.
  -/
  mkTacTask (body : Syntax) (tacPromise : IO.Promise Tactic.TacticParsedSnapshot) :
      TermElabM (Option Syntax × Option (Language.SnapshotTask Tactic.TacticParsedSnapshot))
   := do
    if let some e := getBodyTerm? body then
      if let `(by $tacs*) := e then
        return (e, some { stx? := mkNullNode tacs, task := tacPromise.resultD default })
    tacPromise.resolve default
    return (none, none)

/--
  Create auxiliary local declarations `fs` for the given headers using their `shortDeclName` and `type`, given headers, and execute `k fs`.
  The new free variables are tagged as `auxDecl`.
  Remark: `fs.size = headers.size`.
-/
private partial def withFunLocalDecls {α} (headers : Array DefViewElabHeader) (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec loop (i : Nat) (fvars : Array Expr) := do
    if h : i < headers.size then
      let header := headers[i]
      if header.modifiers.isNonrec then
        loop (i+1) fvars
      else
        withAuxDecl header.shortDeclName header.type header.declName fun fvar => loop (i+1) (fvars.push fvar)
    else
      k fvars
  loop 0 #[]

private def expandWhereStructInst : Macro := fun whereStx => do
  let `(Parser.Command.whereStructInst| where%$whereTk $[$structInstFields];* $[$whereDecls?:whereDecls]?) := whereStx
    | Macro.throwUnsupported

  let startOfStructureTkInfo : SourceInfo :=
    match whereTk.getPos? with
    | some pos => .synthetic pos ⟨pos.byteIdx + 1⟩ true
    | none => .none
  -- Position the closing `}` at the end of the trailing whitespace of `where $[$_:letDecl];*`.
  -- We need an accurate range of the generated structure instance in the generated `TermInfo`
  -- so that we can determine the expected type in structure field completion.
  let structureStxTailInfo :=
    whereStx[1].getTailInfo?
    <|> whereStx[0].getTailInfo?
  let endOfStructureTkInfo : SourceInfo :=
    match structureStxTailInfo with
    | some (SourceInfo.original _ _ trailing _) =>
      let tokenPos := trailing.str.prev trailing.stopPos
      let tokenEndPos := trailing.stopPos
      .synthetic tokenPos tokenEndPos true
    | _ => .none

  let body ← `(structInst| { $structInstFields,* })
  let body := body.raw.setInfo <|
    match startOfStructureTkInfo.getPos?, endOfStructureTkInfo.getTailPos? with
    | some startPos, some endPos => .synthetic startPos endPos true
    | _, _ => .none
  match whereDecls? with
  | some whereDecls => expandWhereDecls whereDecls body
  | none => return body

/-
Recall that
```
def declValSimple    := leading_parser " :=\n" >> termParser >> Termination.suffix >> optional Term.whereDecls
def declValEqns      := leading_parser Term.matchAltsWhereDecls
def declVal          := declValSimple <|> declValEqns <|> Term.whereDecls
```

The `Termination.suffix` is ignored here, and extracted in `declValToTerminationHint`.
-/
private def declValToTerm (declVal : Syntax) : MacroM Syntax := withRef declVal do
  if declVal.isOfKind ``Parser.Command.declValSimple then
    expandWhereDeclsOpt declVal[3] declVal[1]
  else if declVal.isOfKind ``Parser.Command.declValEqns then
    expandMatchAltsWhereDecls declVal[0]
  else if declVal.isOfKind ``Parser.Command.whereStructInst then
    expandWhereStructInst declVal
  else if declVal.isMissing then
    Macro.throwErrorAt declVal "declaration body is missing"
  else
    Macro.throwErrorAt declVal "unexpected declaration body"

/-- Elaborates the termination hints in a `declVal` syntax. -/
private def declValToTerminationHint (declVal : Syntax) : TermElabM TerminationHints :=
  if declVal.isOfKind ``Parser.Command.declValSimple then
    elabTerminationHints ⟨declVal[2]⟩
  else if declVal.isOfKind ``Parser.Command.declValEqns then
    elabTerminationHints ⟨declVal[0][1]⟩
  else
    return .none

/--
Runs `k` with a restricted local context where only section variables from `vars` are included that
* are directly referenced in any `headers`,
* are included in `sc.includedVars` (via the `include` command),
* are directly referenced in any variable included by these rules, OR
* are instance-implicit variables that only reference section variables included by these rules AND
  are not listed in `sc.omittedVars` (via `omit`; note that `omit` also subtracts from
  `sc.includedVars`).
-/
private def withHeaderSecVars {α} (vars : Array Expr) (sc : Command.Scope) (headers : Array DefViewElabHeader)
    (k : Array Expr → TermElabM α) : TermElabM α := do
  let mut revSectionFVars : Std.HashMap FVarId Name := {}
  for (uid, var) in (← read).sectionFVars do
    revSectionFVars := revSectionFVars.insert var.fvarId! uid
  let (_, used) ← collectUsed revSectionFVars |>.run {}
  let (lctx, localInsts, vars) ← removeUnused vars used
  withLCtx lctx localInsts <| k vars
where
  collectUsed revSectionFVars : StateRefT CollectFVars.State MetaM Unit := do
    -- directly referenced in headers
    headers.forM (·.type.collectFVars)
    -- included by `include`
    for var in vars do
      if let some uid := revSectionFVars[var.fvarId!]? then
        if sc.includedVars.contains uid then
          modify (·.add var.fvarId!)
    -- transitively referenced
    get >>= (·.addDependencies) >>= set
    for var in (← get).fvarIds do
      if let some uid := revSectionFVars[var]? then
        if sc.omittedVars.contains uid then
          throwError "cannot omit referenced section variable '{Expr.fvar var}'"
    -- instances (`addDependencies` unnecessary as by definition they may only reference variables
    -- already included)
    for var in vars do
      let ldecl ← getFVarLocalDecl var
      if let some uid := revSectionFVars[var.fvarId!]? then
        if sc.omittedVars.contains uid then
          continue
      let st ← get
      if ldecl.binderInfo.isInstImplicit && (← getFVars ldecl.type).all st.fvarSet.contains then
        modify (·.add ldecl.fvarId)
  getFVars (e : Expr) : MetaM (Array FVarId) :=
    (·.2.fvarIds) <$> e.collectFVars.run {}

register_builtin_option deprecated.oldSectionVars : Bool := {
  defValue := false
  descr    := "re-enable deprecated behavior of including exactly the section variables used in a declaration"
}

register_builtin_option linter.unusedSectionVars : Bool := {
  defValue := true
  descr := "enable the 'unused section variables in theorem body' linter"
}

register_builtin_option debug.proofAsSorry : Bool := {
  defValue := false
  group    := "debug"
  descr    := "replace the bodies (proofs) of theorems with `sorry`"
}

/-- Returns true if `k` is a theorem, option `debug.proofAsSorry` is set to true, and the environment contains the axiom `sorryAx`. -/
private def useProofAsSorry (k : DefKind) : CoreM Bool := do
  if k.isTheorem then
    if debug.proofAsSorry.get (← getOptions) then
      if (← getEnv).contains ``sorryAx then
        return true
  return false

private def elabFunValues (headers : Array DefViewElabHeader) (vars : Array Expr) (sc : Command.Scope) : TermElabM (Array Expr) :=
  headers.mapM fun header => do
    let mut reusableResult? := none
    if let some snap := header.bodySnap? then
      if let some old := snap.old? then
        -- guaranteed reusable as by the `bodySnap?` invariant, so let's wait on the previous
        -- elaboration
        if let some old := old.val.get then
          snap.new.resolve <| some old
          reusableResult? := some (old.value, old.state)
        else
          -- NOTE: this will eagerly cancel async tasks not associated with an inner snapshot, most
          -- importantly kernel checking and compilation of the top-level declaration
          old.val.cancelRec

    let (val, state) ← withRestoreOrSaveFull reusableResult? header.tacSnap? do
      withReuseContext header.value do
      withTraceNode `Elab.definition.value (fun _ => pure header.declName) do
      withDeclName header.declName <| withLevelNames header.levelNames do
      let valStx ← liftMacroM <| declValToTerm header.value
      (if header.kind.isTheorem && !deprecated.oldSectionVars.get (← getOptions) then withHeaderSecVars vars sc #[header] else fun x => x #[]) fun vars => do
      forallBoundedTelescope header.type header.numParams fun xs type => do
        -- Add new info nodes for new fvars. The server will detect all fvars of a binder by the binder's source location.
        for h : i in [0:header.binderIds.size] do
          -- skip auto-bound prefix in `xs`
          addLocalVarInfo header.binderIds[i] xs[header.numParams - header.binderIds.size + i]!
        let val ← if (← useProofAsSorry header.kind) then
          mkSorry type false
        else withReader ({ · with tacSnap? := header.tacSnap? }) do
          -- Store instantiated body in info tree for the benefit of the unused variables linter
          -- and other metaprograms that may want to inspect it without paying for the instantiation
          -- again
          withInfoContext' valStx
            (mkInfo := (pure <| .inl <| mkBodyInfo valStx ·))
            (mkInfoOnError := (pure <| mkBodyInfo valStx none))
            do
              -- synthesize mvars here to force the top-level tactic block (if any) to run
              let val ← elabTermEnsuringType valStx type <* synthesizeSyntheticMVarsNoPostponing
              -- NOTE: without this `instantiatedMVars`, `mkLambdaFVars` may leave around a redex that
              -- leads to more section variables being included than necessary
              instantiateMVarsProfiling val
        let val ← mkLambdaFVars xs val
        if linter.unusedSectionVars.get (← getOptions) && !header.type.hasSorry && !val.hasSorry then
          let unusedVars ← vars.filterMapM fun var => do
            let varDecl ← var.fvarId!.getDecl
            return if sc.includedVars.contains varDecl.userName ||
                header.type.containsFVar var.fvarId! || val.containsFVar var.fvarId! ||
                (← vars.anyM (fun v => return (← v.fvarId!.getType).containsFVar var.fvarId!)) then
              none
            else
              if varDecl.userName.hasMacroScopes && varDecl.binderInfo.isInstImplicit then
                some m!"[{varDecl.type}]"
              else
                some m!"{var}"
          if unusedVars.size > 0 then
            Linter.logLint linter.unusedSectionVars header.ref
              m!"automatically included section variable(s) unused in theorem '{header.declName}':\
              \n  {MessageData.joinSep unusedVars.toList "\n  "}\
              \nconsider restructuring your `variable` declarations so that the variables are not \
                in scope or explicitly omit them:\
              \n  omit {MessageData.joinSep unusedVars.toList " "} in theorem ..."
        return val
    if let some snap := header.bodySnap? then
      snap.new.resolve <| some {
        diagnostics :=
          (← Language.Snapshot.Diagnostics.ofMessageLog (← Core.getAndEmptyMessageLog))
        moreSnaps := (← Core.getAndEmptySnapshotTasks)
        state
        value := val
      }
    return val

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
  let type ← instantiateMVarsProfiling header.type
  pure { header with type := type }

private def instantiateMVarsAtLetRecToLift (toLift : LetRecToLift) : TermElabM LetRecToLift := do
  let type ← instantiateMVarsProfiling toLift.type
  let val ← instantiateMVarsProfiling toLift.val
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
    let mut state := Lean.collectFVars {} toLift.val
    state := Lean.collectFVars state toLift.type
    let mut set := {}
    /- toLift.val may contain metavariables that are placeholders for nested let-recs. We should collect the fvarId
       for the associated let-rec because we need this information to compute the fixpoint later. -/
    let mvarIds := (toLift.val.collectMVars {}).result
    for mvarId in mvarIds do
      let root ← getDelayedMVarRoot mvarId
      match letRecsToLift.findSome? fun (toLift : LetRecToLift) => if toLift.mvarId == root then some toLift.fvarId else none with
      | some fvarId => set := set.insert fvarId
      | none        =>
        /- If the metavariable is not a nested let-rec, it may contribute additional free-variable
           dependencies not caught in the fixed-point routine. In particular, delayed assignments
           due to `match` expressions or tactic blocks induce fvar dependencies that we need to
           account for (see #6927) but cannot ascertain through instantiation if those expressions
           contain still-unassigned metavariable placeholders for other let-recs. See Note
           [Delayed-Assigned Metavariables in Free Variable Collection] for more information. -/
        let some rootAssignment ← getExprMVarAssignment? root | continue
        state := Lean.collectFVars state rootAssignment
    set := state.fvarSet.union set
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
  let e ← instantiateMVarsProfiling e
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
      let zetaDeltaFVarIds ← getZetaDeltaFVarIds
      if !zetaDeltaFVarIds.contains fvarId then
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
      let valNew ← instantiateMVarsProfiling letRecsToLift[i]!.val
      letRecsToLift := letRecsToLift.modify i fun t => { t with val := valNew }
      -- We have to recompute the `freeVarMap` in this case. This overhead should not be an issue in practice.
      freeVarMap ← mkFreeVarMap sectionVars mainFVarIds recFVarIds letRecsToLift
    let toLift := letRecsToLift[i]!
    result := result.push (← mkLetRecClosureFor toLift (freeVarMap.find? toLift.fvarId).get!)
  return result.toList

/-- Mapping from FVarId of mutually recursive functions being defined to "closure" expression. -/
abbrev Replacement := FVarIdMap Expr

def insertReplacementForMainFns (r : Replacement) (sectionVars : Array Expr) (mainHeaders : Array DefViewElabHeader) (mainFVars : Array Expr) : Replacement :=
  mainFVars.size.fold (init := r) fun i _ r =>
    r.insert mainFVars[i].fvarId! (mkAppN (Lean.mkConst mainHeaders[i]!.declName) sectionVars)


def insertReplacementForLetRecs (r : Replacement) (letRecClosures : List LetRecClosure) : Replacement :=
  letRecClosures.foldl (init := r) fun r c =>
    r.insert c.toLift.fvarId c.closed

def isApplicable (r : Replacement) (e : Expr) : Bool :=
  Option.isSome <| e.findExt? fun e =>
    if e.hasFVar then
      match e with
      | .fvar fvarId => if r.contains fvarId then .found else .done
      | _ => .visit
    else
      .done

def Replacement.apply (r : Replacement) (e : Expr) : Expr :=
  -- Remark: if `r` is not a singlenton, then declaration is using `mutual` or `let rec`,
  -- and there is a big chance `isApplicable r e` is true.
  if r.isSingleton && !isApplicable r e then
    e
  else
    e.replace fun e => match e with
      | .fvar fvarId => match r.find? fvarId with
        | some c => some c
        | _      => none
      | _ => none

def pushMain (preDefs : Array PreDefinition) (sectionVars : Array Expr) (mainHeaders : Array DefViewElabHeader) (mainVals : Array Expr)
    : TermElabM (Array PreDefinition) :=
  mainHeaders.size.foldM (init := preDefs) fun i _ preDefs => do
    let header := mainHeaders[i]
    let termination ← declValToTerminationHint header.value
    let termination := termination.rememberExtraParams header.numParams mainVals[i]!
    let value ← mkLambdaFVars sectionVars mainVals[i]!
    let type ← mkForallFVars sectionVars header.type
    if header.kind.isTheorem then
      unless (← isProp type) do
        throwErrorAt header.ref "type of theorem '{header.declName}' is not a proposition{indentExpr type}"
    return preDefs.push {
      ref         := getDeclarationSelectionRef header.ref
      kind        := header.kind
      declName    := header.declName
      levelParams := [], -- we set it later
      modifiers   := header.modifiers
      type, value, termination
    }

def pushLetRecs (preDefs : Array PreDefinition) (letRecClosures : List LetRecClosure) (kind : DefKind) (modifiers : Modifiers) : MetaM (Array PreDefinition) :=
  letRecClosures.foldlM (init := preDefs) fun preDefs c => do
    let type  := Closure.mkForall c.localDecls c.toLift.type
    let value := Closure.mkLambda c.localDecls c.toLift.val
    let kind ← if kind matches .def | .instance | .opaque | .abbrev then
      -- Convert any proof let recs inside a `def` to `theorem` kind
      withLCtx c.toLift.lctx c.toLift.localInstances do
        return if (← inferType c.toLift.type).isProp then .theorem else kind
    else if kind.isTheorem then
      -- Convert any non-proof let recs inside a `theorem` to `def` kind
      withLCtx c.toLift.lctx c.toLift.localInstances do
        return if (← inferType c.toLift.type).isProp then .theorem else .def
    else
      pure kind
    return preDefs.push {
      ref         := c.ref
      declName    := c.toLift.declName
      levelParams := [] -- we set it later
      modifiers   := { modifiers with attrs := c.toLift.attrs }
      kind, type, value,
      termination := c.toLift.termination
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
  resetZetaDeltaFVarIds
  withTrackingZetaDelta do
    -- By checking `toLift.type` and `toLift.val` we populate `zetaFVarIds`. See comments at `src/Lean/Meta/Closure.lean`.
    let letRecsToLift ← letRecsToLift.mapM fun toLift => withLCtx toLift.lctx toLift.localInstances do
      Meta.check toLift.type
      Meta.check toLift.val
      return { toLift with val := (← instantiateMVarsProfiling toLift.val), type := (← instantiateMVarsProfiling toLift.type) }
    let letRecClosures ← mkLetRecClosures sectionVars mainFVarIds recFVarIds letRecsToLift
    -- mkLetRecClosures assign metavariables that were placeholders for the lifted declarations.
    let mainVals    ← mainVals.mapM (instantiateMVarsProfiling ·)
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
    headers[0].levelNames
  else
    []

/-- Eagerly convert universe metavariables occurring in theorem headers to universe parameters. -/
private def levelMVarToParamHeaders (views : Array DefView) (headers : Array DefViewElabHeader) : TermElabM (Array DefViewElabHeader) := do
  let rec process : StateRefT Nat TermElabM (Array DefViewElabHeader) := do
    let mut newHeaders := #[]
    for view in views, header in headers do
      if ← pure view.kind.isTheorem <||> isProp header.type then
        newHeaders ←
          withLevelNames header.levelNames do
            return newHeaders.push { header with type := (← levelMVarToParam header.type), levelNames := (← getLevelNames) }
      else
        newHeaders := newHeaders.push header
    return newHeaders
  let newHeaders ← (process).run' 1
  newHeaders.mapM fun header => return { header with type := (← instantiateMVarsProfiling header.type) }

/--
Ensures that all declarations given by `preDefs` have distinct names.
Remark: we wait to perform this check until the pre-definition phase because we must account for
auxiliary declarations introduced by `where` and `let rec`.
-/
private def checkAllDeclNamesDistinct (preDefs : Array PreDefinition) : TermElabM Unit := do
  let mut names : Std.HashMap Name Syntax := {}
  for preDef in preDefs do
    let userName := privateToUserName preDef.declName
    if let some dupStx := names[userName]? then
      let errorMsg := m!"'mutual' block contains two declarations of the same name '{userName}'"
      Lean.logErrorAt dupStx errorMsg
      throwErrorAt preDef.ref errorMsg
    names := names.insert userName preDef.ref

structure AsyncBodyInfo where
deriving TypeName

def elabMutualDef (vars : Array Expr) (sc : Command.Scope) (views : Array DefView) : TermElabM Unit :=
  if isExample views then
    withoutModifyingEnv do
      -- save correct environment in info tree
      withSaveInfoContext do
        go
  else
    go
where
  go := do
    let bodyPromises ← views.mapM fun _ => IO.Promise.new
    let tacPromises ← views.mapM fun _ => IO.Promise.new
    let expandedDeclIds ← views.mapM fun view => withRef view.headerRef do
      Term.expandDeclId (← getCurrNamespace) (← getLevelNames) view.declId view.modifiers
    let headers ← elabHeaders views expandedDeclIds bodyPromises tacPromises
    let headers ← levelMVarToParamHeaders views headers
    -- elaborate body in parallel when all stars align
    if let (#[view], #[declId]) := (views, expandedDeclIds) then
      if Elab.async.get (← getOptions) && view.kind.isTheorem &&
          !deprecated.oldSectionVars.get (← getOptions) &&
          -- holes in theorem types is not a fatal error, but it does make parallelism impossible
          !headers[0]!.type.hasMVar then
        elabAsync headers[0]! view declId
      else elabSync headers
    else elabSync headers
    for view in views, declId in expandedDeclIds do
      -- NOTE: this should be the full `ref`, and thus needs to be done after any snapshotting
      -- that depends only on a part of the ref
      addDeclarationRangesForBuiltin declId.declName view.modifiers.stx view.ref
  elabSync headers := do
    finishElab headers
    processDeriving headers
  elabAsync header view declId := do
    let env ← getEnv
    let async ← env.addConstAsync declId.declName .thm
    setEnv async.mainEnv

    -- TODO: parallelize header elaboration as well? Would have to refactor auto implicits catch,
    -- makes `@[simp]` etc harder?

    -- commit signature; take level params from type only
    withHeaderSecVars vars sc #[header] fun vars => do
      let type ← mkForallFVars vars header.type
      let allUserLevelNames := getAllUserLevelNames #[header]
      let type ← withLevelNames allUserLevelNames <| levelMVarToParam type
      -- NOTE: instantiation must happen after `levelMVarToParam`, otherwise there can be
      -- normalization differences to the corresponding code in `finishElab`
      let type ← instantiateMVars type

      -- in the case of theorems, the decl level params are those of the header
      let mut s : CollectLevelParams.State := {}
      s := collectLevelParams s type
      let scopeLevelNames ← getLevelNames
      let levelParams ← IO.ofExcept <| sortDeclLevelParams scopeLevelNames allUserLevelNames s.params
      async.commitSignature { name := header.declName, levelParams, type }

    -- attributes should be applied on the main thread; see below
    let header := { header with modifiers.attrs := #[] }

    -- insert a hole for the proof info trees in the main info tree
    let infoHole ← mkFreshMVarId
    let infoPromise ← IO.Promise.new
    modifyInfoState fun s => { s with
      trees := s.trees.push <| .hole infoHole
      lazyAssignment := s.lazyAssignment.insert infoHole <| infoPromise.resultD default
    }

    -- now start new thread for body elaboration, then nested thread for kernel checking
    let cancelTk ← IO.CancelToken.new
    let act ← wrapAsyncAsSnapshot (desc := s!"elaborating proof of {declId.declName}")
        (cancelTk? := cancelTk) fun _ => do profileitM Exception "elaboration" (← getOptions) do
      setEnv async.asyncEnv
      try
        finishElab #[header]
      finally
        reportDiag
        -- must introduce node to fill `infoHole` with multiple info trees
        let info := .ofCustomInfo { stx := header.value, value := .mk (α := AsyncBodyInfo) {} }
        let ctx ← CommandContextInfo.save
        infoPromise.resolve <| .context (.commandCtx ctx) <| .node info (← getInfoTrees)
      async.commitConst (← getEnv)
      let cancelTk ← IO.CancelToken.new
      let checkAct ← wrapAsyncAsSnapshot (desc := s!"finishing proof of {declId.declName}")
          (cancelTk? := cancelTk) fun _ => do profileitM Exception "elaboration" (← getOptions) do
        processDeriving #[header]
        async.commitCheckEnv (← getEnv)
      let checkTask ← BaseIO.mapTask (t := (← getEnv).checked) checkAct
      Core.logSnapshotTask { stx? := none, task := checkTask, cancelTk? := cancelTk }
    Core.logSnapshotTask { stx? := none, task := (← BaseIO.asTask (act ())), cancelTk? := cancelTk }
    applyAttributesAt declId.declName view.modifiers.attrs .afterTypeChecking
    applyAttributesAt declId.declName view.modifiers.attrs .afterCompilation
  finishElab headers := withFunLocalDecls headers fun funFVars => do
    for view in views, funFVar in funFVars do
      addLocalVarInfo view.declId funFVar
    let values ← try
      let values ← elabFunValues headers vars sc
      Term.synthesizeSyntheticMVarsNoPostponing
      values.mapM (instantiateMVarsProfiling ·)
    catch ex =>
      logException ex
      headers.mapM fun header => withRef header.declId <| mkLabeledSorry header.type (synthetic := true) (unique := true)
    let headers ← headers.mapM instantiateMVarsAtHeader
    let letRecsToLift ← getLetRecsToLift
    let letRecsToLift ← letRecsToLift.mapM instantiateMVarsAtLetRecToLift
    checkLetRecsToLiftTypes funFVars letRecsToLift
    (if headers.all (·.kind.isTheorem) && !deprecated.oldSectionVars.get (← getOptions) then withHeaderSecVars vars sc headers else withUsed vars headers values letRecsToLift) fun vars => do
      let preDefs ← MutualClosure.main vars headers funFVars values letRecsToLift
      checkAllDeclNamesDistinct preDefs
      for preDef in preDefs do
        trace[Elab.definition] "{preDef.declName} : {preDef.type} :=\n{preDef.value}"
      let allUserLevelNames := getAllUserLevelNames headers
      let preDefs ← withLevelNames allUserLevelNames <| levelMVarToParamTypesPreDecls preDefs
      let preDefs ← instantiateMVarsAtPreDecls preDefs
      let preDefs ← shareCommonPreDefs preDefs
      let scopeLevelNames ← getLevelNames
      let preDefs ← fixLevelParams preDefs scopeLevelNames allUserLevelNames
      for preDef in preDefs do
        trace[Elab.definition] "after eraseAuxDiscr, {preDef.declName} : {preDef.type} :=\n{preDef.value}"
      addPreDefinitions preDefs
  processDeriving (headers : Array DefViewElabHeader) := do
    for header in headers, view in views do
      if let some classNamesStx := view.deriving? then
        for classNameStx in classNamesStx do
          let className ← realizeGlobalConstNoOverload classNameStx
          withRef classNameStx do
            unless (← processDefDeriving className header.declName) do
              throwError "failed to synthesize instance '{className}' for '{header.declName}'"

/--
Logs a snapshot task that waits for the entire snapshot tree in `defsParsedSnap` and then logs a
`goalsAccomplished` silent message for theorems and `Prop`-typed examples if the entire mutual block
is error-free and contains no syntactical `sorry`s.
-/
private def logGoalsAccomplishedSnapshotTask (views : Array DefView)
    (defsParsedSnap : DefsParsedSnapshot) : TermElabM Unit := do
  if Lean.internal.cmdlineSnapshots.get (← getOptions) then
    -- Skip 'goals accomplished' task if we are on the command line.
    -- These messages are only used in the language server.
    return
  let currentLog ← Core.getMessageLog
  let snaps := #[SnapshotTask.finished none (toSnapshotTree defsParsedSnap)] ++
    (← getThe Core.State).snapshotTasks
  let tree := SnapshotTree.mk { diagnostics := .empty } snaps
  let logGoalsAccomplishedAct ← Term.wrapAsyncAsSnapshot (cancelTk? := none) fun () => do
    -- NOTE: `waitAll` below ensures `getAll` will not block here
    let logs := tree.getAll.map (·.diagnostics.msgLog) |>.push currentLog
    let hasErrorOrSorry := logs.any fun log =>
      log.reportedPlusUnreported.any fun msg =>
        msg.severity matches .error || msg.data.hasTag (· == `hasSorry)
    if hasErrorOrSorry then
      return
    for d in defsParsedSnap.defs, view in views do
      let logGoalsAccomplished :=
        let msgData := .tagged `goalsAccomplished m!"Goals accomplished!"
        logAt view.ref msgData (severity := .information) (isSilent := true)
      match view.kind with
      | .theorem =>
        logGoalsAccomplished
      | .example =>
        let some processedSnap := d.headerProcessedSnap.get
          | continue
        if ! (← isProp processedSnap.view.type) then
          continue
        logGoalsAccomplished
      | _ => continue
  let logGoalsAccomplishedTask ← BaseIO.mapTask (t := ← tree.waitAll) logGoalsAccomplishedAct
  Core.logSnapshotTask {
    stx? := none
    -- Use first line of the mutual block to avoid covering the progress of the whole mutual block
    reportingRange? := (← getRef).getPos?.map fun pos => ⟨pos, pos⟩
    task := logGoalsAccomplishedTask
  }

end Term
namespace Command

def elabMutualDef (ds : Array Syntax) : CommandElabM Unit := do
  let opts ← getOptions
  let headerPromises ← ds.mapM fun _ => IO.Promise.new
  let snap? := (← read).snap?
  let mut views := #[]
  let mut defs := #[]
  let mut reusedAllHeaders := true
  for h : i in [0:ds.size], headerPromise in headerPromises do
    let d := ds[i]
    let modifiers ← elabModifiers ⟨d[0]⟩
    if ds.size > 1 && modifiers.isNonrec then
      throwErrorAt d "invalid use of 'nonrec' modifier in 'mutual' block"
    let mut view ← mkDefView modifiers d[1]
    let fullHeaderRef := mkNullNode #[d[0], view.headerRef]
    if let some snap := snap? then
      view := { view with headerSnap? := some {
        old? := do
          -- transitioning from `Context.snap?` to `DefView.headerSnap?` invariant: if the
          -- elaboration context and state are unchanged, and the syntax of this as well as all
          -- previous headers is unchanged, then the elaboration result for this header (which
          -- includes state from elaboration of previous headers!) should be unchanged.
          guard reusedAllHeaders
          let old ← snap.old?
          -- blocking wait, `HeadersParsedSnapshot` (and hopefully others) should be quick
          let old ← old.val.get.toTyped? DefsParsedSnapshot
          let oldParsed ← old.defs[i]?
          guard <| fullHeaderRef.eqWithInfoAndTraceReuse opts oldParsed.fullHeaderRef
          -- no syntax guard to store, we already did the necessary checks
          return ⟨.missing, oldParsed.headerProcessedSnap⟩
        new := headerPromise
      } }
      if snap.old?.isSome && (view.headerSnap?.bind (·.old?)).isNone then
        snap.old?.forM (·.val.cancelRec)
      defs := defs.push {
        fullHeaderRef
        headerProcessedSnap := { stx? := d, task := headerPromise.resultD default }
      }
      reusedAllHeaders := reusedAllHeaders && view.headerSnap?.any (·.old?.isSome)
    views := views.push view
  let defsParsedSnap := { defs, diagnostics := .empty : DefsParsedSnapshot }
  if let some snap := snap? then
    -- no non-fatal diagnostics at this point
    snap.new.resolve <| .ofTyped defsParsedSnap
  let sc ← getScope
  runTermElabM fun vars => do
    Term.elabMutualDef vars sc views
    Term.logGoalsAccomplishedSnapshotTask views defsParsedSnap

builtin_initialize
  registerTraceClass `Elab.definition.mkClosure
  registerTraceClass `Elab.definition.header
  registerTraceClass `Elab.definition.value

end Command
end Lean.Elab

/-!
# Note [Delayed-Assigned Metavariables in Free Variable Collection]

Nested declarations using `let rec` should compile correctly even when nested within expressions
that are elaborated using delayed metavariable assignments, such as `match` expressions and tactic
blocks. Previously, declaring a `let rec` within such an expression in the following fashion
```lean
def f x :=
  let rec g :=
    match ... with
    | pat =>
      let rec h := ... g ...
      ... x ...
```
where `g` depends on some free variable bound by `f` (like `x` above) would cause `MutualClosure` to
fail to detect that transitive fvar dependency of `h` (which must pass it as an argument to `g`),
leading to an unbound fvar in the body of `h` that was ultimately fed to the kernel. This occurred
because `MutualClosure` processes let-recs from most to least nested. Initially, the body of `g` is
an application of the delayed-assigned metavariable generated by `match` elaboration; the root
metavariable of that delayed assignment is, in turn, assigned to an expression that refers to the
mvar that will eventually be assigned to `g` once we process that declaration. Therefore, when we
initially process the most-nested declaration `h` (before `g`), we cannot instantiate the
`match`-expression mvar's delayed assignment (since the metavariable that will eventually be
assigned to the yet-unprocessed `g` remains unassigned). Thus, we do not detect any of the fvar
dependencies of `g` in the `match` body -- namely, that corresponding to `x`, which `h` should
therefore also take as a parameter. This also caused a knock-on effect in certain situations,
wherein `h` would compile as an `axiom` rather than as `opaque`, rendering `f` erroneously
noncomputable.
-/
