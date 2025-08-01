/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Util.SCC
public import Lean.Elab.PreDefinition.Basic
public import Lean.Elab.PreDefinition.Structural
public import Lean.Elab.PreDefinition.WF.Main
public import Lean.Elab.PreDefinition.MkInhabitant
public import Lean.Elab.PreDefinition.PartialFixpoint

public section

namespace Lean.Elab
open Meta
open Term

private def addAndCompilePartial (preDefs : Array PreDefinition) (useSorry := false) : TermElabM Unit := do
  for preDef in preDefs do
    trace[Elab.definition] "processing {preDef.declName}"
    let all := preDefs.toList.map (·.declName)
    forallTelescope preDef.type fun xs type => do
      let value ← if useSorry then
        mkLambdaFVars xs (← withRef preDef.ref <| mkLabeledSorry type (synthetic := true) (unique := true))
      else
        let msg := m!"failed to compile 'partial' definition '{preDef.declName}'"
        liftM <| mkInhabitantFor msg xs type
      addNonRec { preDef with
        kind  := DefKind.«opaque»
        value
      } (all := all)
  addAndCompilePartialRec preDefs

private def isNonRecursive (preDef : PreDefinition) : Bool :=
  Option.isNone $ preDef.value.find? fun
    | Expr.const declName _ => preDef.declName == declName
    | _ => false

private def partitionPreDefs (preDefs : Array PreDefinition) : Array (Array PreDefinition) :=
  let getPreDef    := fun declName => (preDefs.find? fun preDef => preDef.declName == declName).get!
  let vertices     := preDefs.toList.map (·.declName)
  let successorsOf := fun declName => (getPreDef declName).value.foldConsts [] fun declName successors =>
    if preDefs.any fun preDef => preDef.declName == declName then
      declName :: successors
    else
      successors
  let sccs := SCC.scc vertices successorsOf
  sccs.toArray.map fun scc => scc.toArray.map getPreDef

private def collectMVarsAtPreDef (preDef : PreDefinition) : StateRefT CollectMVars.State MetaM Unit := do
  collectMVars preDef.value
  collectMVars preDef.type

private def getMVarsAtPreDef (preDef : PreDefinition) : MetaM (Array MVarId) := do
  let (_, s) ← (collectMVarsAtPreDef preDef).run {}
  pure s.result

/--
Set any lingering level mvars to `.zero`, for error recovery.
-/
private def setLevelMVarsAtPreDef (preDef : PreDefinition) : PreDefinition :=
  if preDef.value.hasLevelMVar then
    let value' :=
      preDef.value.replaceLevel fun l =>
        match l with
        | .mvar _ => levelZero
        | _       => none
    { preDef with value := value' }
  else
    preDef

private partial def ensureNoUnassignedLevelMVarsAtPreDef (preDef : PreDefinition) : TermElabM PreDefinition := do
  if !preDef.value.hasLevelMVar then
    return preDef
  else
    let pendingLevelMVars := (collectLevelMVars {} (← instantiateMVars preDef.value)).result
    if (← logUnassignedLevelMVarsUsingErrorInfos pendingLevelMVars) then
      return setLevelMVarsAtPreDef preDef
    else if !(← MonadLog.hasErrors) then
      -- This is a fallback in case we don't have an error info available for the universe level metavariables.
      -- We try to produce an error message containing an expression with one of the universe level metavariables.
      let rec visitLevel (u : Level) (e : Expr) : TermElabM Unit := do
        if u.hasMVar then
          let e' ← exposeLevelMVars e
          throwError "\
            declaration '{preDef.declName}' contains universe level metavariables at the expression\
            {indentExpr e'}\n\
            in the declaration body{indentExpr <| ← exposeLevelMVars preDef.value}"
      let withExpr (e : Expr) (m : ReaderT Expr (MonadCacheT ExprStructEq Unit TermElabM) Unit) :=
        withReader (fun _ => e) m
      let rec visit (e : Expr) (head := false) : ReaderT Expr (MonadCacheT ExprStructEq Unit TermElabM) Unit := do
        if e.hasLevelMVar then
          checkCache { val := e : ExprStructEq } fun _ => do
            match e with
            | .forallE n d b c | .lam n d b c => withExpr e do visit d; withLocalDecl n c d fun x => visit (b.instantiate1 x)
            | .letE n t v b nondep => withExpr e do visit t; visit v; withLetDecl n t v (nondep := nondep) fun x => visit (b.instantiate1 x)
            | .mdata _ b     => withExpr e do visit b
            | .proj _ _ b    => withExpr e do visit b
            | .sort u        => visitLevel u (← read)
            | .const _ us    => (if head then id else withExpr e) <| us.forM (visitLevel · (← read))
            | .app ..        => withExpr e do e.withApp fun f args => do visit f true; args.forM visit
            | _              => pure ()
      try
        visit preDef.value |>.run preDef.value |>.run {}
      catch e =>
        logException e
        return setLevelMVarsAtPreDef preDef
      throwAbortCommand
    else
      return setLevelMVarsAtPreDef preDef

private def ensureNoUnassignedMVarsAtPreDef (preDef : PreDefinition) : TermElabM PreDefinition := do
  let pendingMVarIds ← getMVarsAtPreDef preDef
  if (← logUnassignedUsingErrorInfos pendingMVarIds) then
    let preDef := { preDef with value := (← withRef preDef.ref <| mkLabeledSorry preDef.type (synthetic := true) (unique := true)) }
    if (← getMVarsAtPreDef preDef).isEmpty then
      return preDef
    else
      throwAbortCommand
  else
    ensureNoUnassignedLevelMVarsAtPreDef preDef

/--
  Letrec declarations produce terms of the form `(fun .. => ..) d` where `d` is a (partial) application of an auxiliary declaration for a letrec declaration.
  This method beta-reduces them to make sure they can be eliminated by the well-founded recursion module. -/
private def betaReduceLetRecApps (preDefs : Array PreDefinition) : MetaM (Array PreDefinition) :=
  preDefs.mapM fun preDef => do
    if preDef.value.find? (fun e => e.isConst && preDefs.any fun preDef => preDef.declName == e.constName!) |>.isSome then
      let value ← Core.transform preDef.value fun e => do
        if e.isApp && e.getAppFn.isLambda && e.getAppArgs.all fun arg => arg.getAppFn.isConst && preDefs.any fun preDef => preDef.declName == arg.getAppFn.constName! then
          return .visit e.headBeta
        else
          return .continue
      return { preDef with value }
    else
      return preDef

private def addSorried (preDefs : Array PreDefinition) : TermElabM Unit := do
  for preDef in preDefs do
    unless (← hasConst preDef.declName) do
      let value ← mkSorry (synthetic := true) preDef.type
      let decl := if preDef.kind.isTheorem then
        Declaration.thmDecl {
          name        := preDef.declName,
          levelParams := preDef.levelParams,
          type        := preDef.type,
          value
        }
      else
        Declaration.defnDecl {
          name        := preDef.declName,
          levelParams := preDef.levelParams,
          type        := preDef.type,
          hints       := .abbrev
          safety      := .safe
          value
        }
      addDecl decl
      withSaveInfoContext do  -- save new env
        addTermInfo' preDef.ref (← mkConstWithLevelParams preDef.declName) (isBinder := true)
      applyAttributesOf #[preDef] AttributeApplicationTime.afterTypeChecking
      applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

def ensureFunIndReservedNamesAvailable (preDefs : Array PreDefinition) : MetaM Unit := do
  preDefs.forM fun preDef =>
    withRef preDef.ref <| ensureReservedNameAvailable preDef.declName "induct"
  withRef preDefs[0]!.ref <| ensureReservedNameAvailable preDefs[0]!.declName "mutual_induct"


/--
Checks consistency of a clique of TerminationHints:

* If not all have a hint, the hints are ignored (log error)
* None have both `termination_by` and `partial_fixpoint` (throw error)
* If one has `structural` or `partial_fixpoint`, check that all have it (else throw error)
* A `structural` should not have a `decreasing_by` (else log error)

-/
def checkTerminationByHints (preDefs : Array PreDefinition) : CoreM Unit := do
  let some preDefWith := preDefs.find? (·.termination.isNotNone) | return
  let preDefsWithout := preDefs.filter (·.termination.terminationBy?.isNone)
  let structural :=
    preDefWith.termination.terminationBy? matches some {structural := true, ..}
  -- Information whether the current one is partial, inductive or coinductive
  let partialFixpoint := preDefWith.termination.partialFixpoint?.any fun x => isPartialFixpoint x.fixpointType
  let inductiveFixpoint := preDefWith.termination.partialFixpoint?.any fun x => isInductiveFixpoint x.fixpointType
  let coinductiveFixpoint := preDefWith.termination.partialFixpoint?.any fun x => isCoinductiveFixpoint x.fixpointType
  for preDef in preDefs do
    -- if some has at termination by clause
    if let .some termBy := preDef.termination.terminationBy? then
      -- but something in the clique is partial/inductive/coinductive, then we report error
      if let .some partialFixpointStx := preDef.termination.partialFixpoint? then
        match partialFixpointStx.fixpointType with
        | .partialFixpoint => throwErrorAt partialFixpointStx.ref m!"conflicting annotations: this function cannot \
          be both terminating and a partial fixpoint"
        | .inductiveFixpoint => throwErrorAt partialFixpointStx.ref m!"conflicting annotations: this function cannot \
          be both terminating and an inductive fixpoint"
        | .coinductiveFixpoint => throwErrorAt partialFixpointStx.ref m!"conflicting annotations: this function cannot \
          be both terminating and a coinductive fixpoint"

      -- if has no annotations
      if !structural && !partialFixpoint && !inductiveFixpoint && !coinductiveFixpoint && !preDefsWithout.isEmpty then
        let m := MessageData.andList (preDefsWithout.toList.map (m!"{·.declName}"))
        let doOrDoes := if preDefsWithout.size = 1 then "does" else "do"
        logErrorAt termBy.ref m!"incomplete set of termination hints:\n\
          This function is mutually recursive with {m}, which {doOrDoes} not have \
          a termination hint.\n\
          The present clause is ignored."

      if structural && !termBy.structural then
        throwErrorAt termBy.ref m!"Incompatible termination hint; this function is mutually \
          recursive with {preDefWith.declName}, which is marked as `termination_by \
          structural` so this one also needs to be marked `structural`."
      if !structural && termBy.structural then
        throwErrorAt termBy.ref m!"Incompatible termination hint; this function is mutually \
          recursive with {preDefWith.declName}, which is not marked as `structural` \
         so this one cannot be `structural` either."
      if termBy.structural then
        if let .some decr := preDef.termination.decreasingBy? then
          logErrorAt decr.ref m!"Incompatible termination hint; this function is marked as \
            structurally recursive, so no explicit termination proof is needed."

    -- If one is partial, but others are not
    if partialFixpoint && !preDef.termination.partialFixpoint?.any fun x => isPartialFixpoint x.fixpointType then
      throwErrorAt preDef.ref m!"Incompatible termination hint; this function is mutually \
        recursive with {preDefWith.declName}, which is marked as \
        `partial_fixpoint` so this one also needs to be marked \
        `partial_fixpoint`."

    -- If one is least, but others are not
    if inductiveFixpoint && !preDef.termination.partialFixpoint?.any fun x => isLatticeTheoretic x.fixpointType then
      throwErrorAt preDef.ref m!"Incompatible termination hint; this function is mutually \
        recursive with {preDefWith.declName}, which is marked as
        `inductive_fixpoint` so this one also needs to be marked \
        `inductive_fixpoint` or `coinductive_fixpoint`."

    -- If one is greatest, but others are not
    if coinductiveFixpoint && !preDef.termination.partialFixpoint?.any fun x => isLatticeTheoretic x.fixpointType then
      throwErrorAt preDef.ref m!"Incompatible termination hint; this function is mutually \
        recursive with {preDefWith.declName}, which is marked as \
        `coinductive_fixpoint` so this one also needs to be marked \
        `inductive_fixpoint` or `coinductive_fixpoint`."

    -- checking for unnecessary `decreasing_by` clause
    if preDef.termination.partialFixpoint?.any fun x => isPartialFixpoint x.fixpointType then
        if let .some decr := preDef.termination.decreasingBy? then
          logErrorAt decr.ref m!"Invalid `decreasing_by`; this function is marked as \
            partial_fixpoint, so no explicit termination proof is needed."

    if preDef.termination.partialFixpoint?.any fun x => isInductiveFixpoint x.fixpointType then
      if let .some decr := preDef.termination.decreasingBy? then
        logErrorAt decr.ref m!"Invalid `decreasing_by`; this function is marked as \
          inductive_fixpoint, so no explicit termination proof is needed."

    if preDef.termination.partialFixpoint?.any fun x => isInductiveFixpoint x.fixpointType then
      if let .some decr := preDef.termination.decreasingBy? then
        logErrorAt decr.ref m!"Invalid `decreasing_by`; this function is marked as \
          coinductive_fixpoint, so no explicit termination proof is needed."

    -- if the selected one is not marked as partial fixpoint
    if !partialFixpoint then
      if let some stx := preDef.termination.partialFixpoint? then
        if isPartialFixpoint stx.fixpointType then
          throwErrorAt stx.ref m!"Incompatible termination hint; this function is mutually \
            recursive with {preDefWith.declName}, which is not also marked as \
            `partial_fixpoint`, so this one cannot be either."

    -- if the selected one is not marked as partial fixpoint
    unless inductiveFixpoint || coinductiveFixpoint do
      if let some stx := preDef.termination.partialFixpoint? then
        if isLatticeTheoretic stx.fixpointType then
          throwErrorAt stx.ref m!"Incompatible termination hint; this function is mutually \
            recursive with {preDefWith.declName}, which is not also marked as \
            `inductive_fixpoint` or `coinductive_fixpoint`, so this one cannot be either."

/--
Elaborates the `TerminationHint` in the clique to `TerminationMeasures`
-/
def elabTerminationByHints (preDefs : Array PreDefinition) : TermElabM (Array (Option TerminationMeasure)) := do
  preDefs.mapM fun preDef => do
    let arity ← lambdaTelescope preDef.value fun xs _ => pure xs.size
    let hints := preDef.termination
    hints.terminationBy?.mapM
      (TerminationMeasure.elab preDef.declName preDef.type arity hints.extraParams ·)

def shouldUseStructural (preDefs : Array PreDefinition) : Bool :=
  preDefs.any fun preDef =>
    preDef.termination.terminationBy? matches some {structural := true, ..}

def shouldUsePartialFixpoint (preDefs : Array PreDefinition) : Bool :=
  preDefs.any fun preDef =>
    preDef.termination.partialFixpoint?.isSome

def shouldUseWF (preDefs : Array PreDefinition) : Bool :=
  preDefs.any fun preDef =>
    preDef.termination.terminationBy? matches some {structural := false, ..} ||
    preDef.termination.decreasingBy?.isSome


def addPreDefinitions (preDefs : Array PreDefinition) : TermElabM Unit := withLCtx {} {} do
  profileitM Exception "process pre-definitions" (← getOptions) do
    withTraceNode `Elab.def.processPreDef (fun _ => return m!"process pre-definitions") do
      for preDef in preDefs do
        trace[Elab.definition.body] "{preDef.declName} : {preDef.type} :=\n{preDef.value}"
      let preDefs ← preDefs.mapM ensureNoUnassignedMVarsAtPreDef
      let preDefs ← betaReduceLetRecApps preDefs
      let cliques := partitionPreDefs preDefs
      for preDefs in cliques do
        trace[Elab.definition.scc] "{preDefs.map (·.declName)}"
        if preDefs.size == 1 && isNonRecursive preDefs[0]! then
          /-
          We must erase `recApp` annotations even when `preDef` is not recursive
          because it may use another recursive declaration in the same mutual block.
          See issue #2321
          -/
          let preDef ← eraseRecAppSyntax preDefs[0]!
          ensureEqnReservedNamesAvailable preDef.declName
          if preDef.modifiers.isNoncomputable then
            addNonRec preDef (cleanupValue := true)
          else
            addAndCompileNonRec preDef (cleanupValue := true)
          preDef.termination.ensureNone "not recursive"
        else if preDefs.any (·.modifiers.isUnsafe) then
          addAndCompileUnsafe preDefs
          preDefs.forM (·.termination.ensureNone "unsafe")
        else
          if preDefs.any (·.modifiers.isInferredPartial) then
            let mut isPartial := true
            for preDef in preDefs do
              if !(← whnfD preDef.type).isForall then
                if preDef.modifiers.isPartial then
                  withRef preDef.ref <| throwError "invalid use of 'partial', '{preDef.declName}' is not a function{indentExpr preDef.type}"
                else
                  -- `meta` should not imply `partial` in this case
                  isPartial := false

            if isPartial then
              addAndCompilePartial preDefs
              preDefs.forM (·.termination.ensureNone "partial")
              continue

          ensureFunIndReservedNamesAvailable preDefs
          try
            checkCodomainsLevel preDefs
            checkTerminationByHints preDefs
            let termMeasures?s ← elabTerminationByHints preDefs
            if shouldUseStructural preDefs then
              structuralRecursion preDefs termMeasures?s
            else if shouldUsePartialFixpoint preDefs then
              partialFixpoint preDefs
            else if shouldUseWF preDefs then
              wfRecursion preDefs termMeasures?s
            else
              withRef (preDefs[0]!.ref) <| mapError
                (orelseMergeErrors
                  (structuralRecursion preDefs termMeasures?s)
                  (wfRecursion preDefs termMeasures?s))
                (fun msg =>
                  let preDefMsgs := preDefs.toList.map (MessageData.ofExpr $ mkConst ·.declName)
                  m!"fail to show termination for{indentD (MessageData.joinSep preDefMsgs Format.line)}\nwith errors\n{msg}")
          catch ex =>
            logException ex
            let s ← saveState
            try
              if preDefs.all fun preDef => (preDef.kind matches DefKind.def | DefKind.instance) || preDefs.all fun preDef => preDef.kind == DefKind.abbrev then
                -- try to add as partial definition
                withOptions (Elab.async.set · false) do
                  try
                    addAndCompilePartial preDefs (useSorry := true)
                  catch _ =>
                    -- Compilation failed try again just as axiom
                    s.restore
                    addSorried preDefs
              else if preDefs.all fun preDef => preDef.kind == DefKind.theorem then
                addSorried preDefs
            catch _ => s.restore

builtin_initialize
  registerTraceClass `Elab.definition.body
  registerTraceClass `Elab.definition.scc

end Lean.Elab
