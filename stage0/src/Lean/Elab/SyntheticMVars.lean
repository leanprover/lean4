/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.ForEachExpr
import Lean.Elab.Term
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Term
open Tactic (TacticM evalTactic getUnsolvedGoals withTacticInfoContext)
open Meta

/-- Auxiliary function used to implement `synthesizeSyntheticMVars`. -/
private def resumeElabTerm (stx : Syntax) (expectedType? : Option Expr) (errToSorry := true) : TermElabM Expr :=
  -- Remark: if `ctx.errToSorry` is already false, then we don't enable it. Recall tactics disable `errToSorry`
  withReader (fun ctx => { ctx with errToSorry := ctx.errToSorry && errToSorry }) do
    elabTerm stx expectedType? false

/--
  Try to elaborate `stx` that was postponed by an elaboration method using `Expection.postpone`.
  It returns `true` if it succeeded, and `false` otherwise.
  It is used to implement `synthesizeSyntheticMVars`. -/
private def resumePostponed (savedContext : SavedContext) (stx : Syntax) (mvarId : MVarId) (postponeOnError : Bool) : TermElabM Bool :=
  withRef stx <| withMVarContext mvarId do
    let s ← get
    try
      withSavedContext savedContext do
        let mvarDecl     ← getMVarDecl mvarId
        let expectedType ← instantiateMVars mvarDecl.type
        withInfoHole mvarId do
          let result ← resumeElabTerm stx expectedType (!postponeOnError)
          /- We must ensure `result` has the expected type because it is the one expected by the method that postponed stx.
            That is, the method does not have an opportunity to check whether `result` has the expected type or not. -/
          let result ← withRef stx <| ensureHasType expectedType result
          /- We must perform `occursCheck` here since `result` may contain `mvarId` when it has synthetic `sorry`s. -/
          if (← occursCheck mvarId result) then
            assignExprMVar mvarId result
            return true
          else
            return false
    catch
     | ex@(Exception.internal id _) =>
       if id == postponeExceptionId then
         set s
         return false
       else
         throw ex
     | ex@(Exception.error _ _) =>
       if postponeOnError then
         set s
         return false
       else
         logException ex
         return true

/--
  Similar to `synthesizeInstMVarCore`, but makes sure that `instMVar` local context and instances
  are used. It also logs any error message produced. -/
private def synthesizePendingInstMVar (instMVar : MVarId) : TermElabM Bool :=
  withMVarContext instMVar do
    try
      synthesizeInstMVarCore instMVar
    catch
      | ex@(Exception.error _ _) => logException ex; return true
      | _                        => unreachable!

/--
  Similar to `synthesizePendingInstMVar`, but generates type mismatch error message.
  Remark: `eNew` is of the form `@coe ... mvar`, where `mvar` is the metavariable for the `CoeT ...` instance.
  If `mvar` can be synthesized, then assign `auxMVarId := (expandCoe eNew)`.
-/
private def synthesizePendingCoeInstMVar
    (auxMVarId : MVarId) (errorMsgHeader? : Option String) (eNew : Expr) (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr) : TermElabM Bool := do
  let instMVarId := eNew.appArg!.mvarId!
  withMVarContext instMVarId do
    if (← isDefEq expectedType eType) then
      /- This case may seem counterintuitive since we created the coercion
         because the `isDefEq expectedType eType` test failed before.
         However, it may succeed here because we have more information, for example, metavariables
         occurring at `expectedType` and `eType` may have been assigned. -/
      if (← occursCheck auxMVarId e) then
        assignExprMVar auxMVarId e
        return true
      else
        return false
    try
      if (← synthesizeCoeInstMVarCore instMVarId) then
        let eNew ← expandCoe eNew
        if (← occursCheck auxMVarId eNew) then
          assignExprMVar auxMVarId eNew
          return true
      return false
    catch
      | Exception.error _ msg => throwTypeMismatchError errorMsgHeader? expectedType eType e f? msg
      | _                     => unreachable!

/--
  Try to synthesize a value for `mvarId` using the given default instance.
  Return `some (val, mvarDecls)` if successful, where `val` is the value assigned to `mvarId`, and `mvarDecls` is a list of new type class instances that need to be synthesized.
-/
private def tryToSynthesizeUsingDefaultInstance (mvarId : MVarId) (defaultInstance : Name) : TermElabM (Option (Expr × List SyntheticMVarDecl)) :=
  commitWhenSome? do
    let candidate ← mkConstWithFreshMVarLevels defaultInstance
    let (mvars, bis, _) ← forallMetaTelescopeReducing (← inferType candidate)
    let candidate := mkAppN candidate mvars
    trace[Elab.resume] "trying default instance for {mkMVar mvarId} := {candidate}"
    if (← isDefEqGuarded (mkMVar mvarId) candidate) then
      -- Succeeded. Collect new TC problems
      let mut result := []
      for i in [:bis.size] do
        if bis[i] == BinderInfo.instImplicit then
           result := { mvarId := mvars[i].mvarId!, stx := (← getRef), kind := SyntheticMVarKind.typeClass } :: result
      trace[Elab.resume] "worked"
      return some (candidate, result)
    else
      return none

private def tryToSynthesizeUsingDefaultInstances (mvarId : MVarId) (prio : Nat) : TermElabM (Option (Expr × List SyntheticMVarDecl)) :=
  withMVarContext mvarId do
    let mvarType := (← Meta.getMVarDecl mvarId).type
    match (← isClass? mvarType) with
    | none => return none
    | some className =>
      match (← getDefaultInstances className) with
      | [] => return none
      | defaultInstances =>
        for (defaultInstance, instPrio) in defaultInstances do
          if instPrio == prio then
            match (← tryToSynthesizeUsingDefaultInstance mvarId defaultInstance) with
            | some result => return some result
            | none => continue
        return none

/- Used to implement `synthesizeUsingDefault`. This method only consider default instances with the given priority. -/
private def synthesizeUsingDefaultPrio (prio : Nat) : TermElabM Bool := do
  let rec visit (syntheticMVars : List SyntheticMVarDecl) (syntheticMVarsNew : List SyntheticMVarDecl) : TermElabM Bool := do
    match syntheticMVars with
    | [] => return false
    | mvarDecl :: mvarDecls =>
      match mvarDecl.kind with
      | SyntheticMVarKind.typeClass =>
        match (← withRef mvarDecl.stx <| tryToSynthesizeUsingDefaultInstances mvarDecl.mvarId prio) with
        | none => visit mvarDecls (mvarDecl :: syntheticMVarsNew)
        | some (val, newMVarDecls) =>
          for newMVarDecl in newMVarDecls do
            -- Register that `newMVarDecl.mvarId`s are implicit arguments of the value assigned to `mvarDecl.mvarId`
            registerMVarErrorImplicitArgInfo newMVarDecl.mvarId (← getRef) val
          let syntheticMVarsNew := newMVarDecls ++ syntheticMVarsNew
          let syntheticMVarsNew := mvarDecls.reverse ++ syntheticMVarsNew
          modify fun s => { s with syntheticMVars := syntheticMVarsNew }
          return true
      | _ => visit mvarDecls (mvarDecl :: syntheticMVarsNew)
  /- Recall that s.syntheticMVars is essentially a stack. The first metavariable was the last one created.
     We want to apply the default instance in reverse creation order. Otherwise,
     `toString 0` will produce a `OfNat String _` cannot be synthesized error. -/
  visit (← get).syntheticMVars.reverse []

/--
  Apply default value to any pending synthetic metavariable of kind `SyntheticMVarKind.withDefault`
  Return true if something was synthesized. -/
private def synthesizeUsingDefault : TermElabM Bool := do
  let prioSet ← getDefaultInstancesPriorities
  /- Recall that `prioSet` is stored in descending order -/
  for prio in prioSet do
    if (← synthesizeUsingDefaultPrio prio) then
      return true
  return false

/--
  Report an error for each synthetic metavariable that could not be resolved.
  Remark: we set `ignoreStuckTC := true` when elaborating `simp` arguments.
-/
private def reportStuckSyntheticMVars (ignoreStuckTC := false) : TermElabM Unit := do
  let syntheticMVars ← modifyGet fun s => (s.syntheticMVars, { s with syntheticMVars := [] })
  for mvarSyntheticDecl in syntheticMVars do
    withRef mvarSyntheticDecl.stx do
    match mvarSyntheticDecl.kind with
    | SyntheticMVarKind.typeClass =>
      unless ignoreStuckTC do
        withMVarContext mvarSyntheticDecl.mvarId do
          let mvarDecl ← getMVarDecl mvarSyntheticDecl.mvarId
          unless (← get).messages.hasErrors do
            throwError "typeclass instance problem is stuck, it is often due to metavariables{indentExpr mvarDecl.type}"
    | SyntheticMVarKind.coe header eNew expectedType eType e f? =>
      let mvarId := eNew.appArg!.mvarId!
      withMVarContext mvarId do
        let mvarDecl ← getMVarDecl mvarId
        throwTypeMismatchError header expectedType eType e f? (some ("failed to create type class instance for " ++ indentExpr mvarDecl.type))
    | _ => unreachable! -- TODO handle other cases.

private def getSomeSynthethicMVarsRef : TermElabM Syntax := do
  let s ← get
  match s.syntheticMVars.find? fun (mvarDecl : SyntheticMVarDecl) => !mvarDecl.stx.getPos?.isNone with
  | some mvarDecl => return mvarDecl.stx
  | none          => return Syntax.missing

mutual

  partial def runTactic (mvarId : MVarId) (tacticCode : Syntax) : TermElabM Unit := do
    /- Recall, `tacticCode` is the whole `by ...` expression. -/
    let byTk := tacticCode[0]
    let code := tacticCode[1]
    modifyThe Meta.State fun s => { s with mctx := s.mctx.instantiateMVarDeclMVars mvarId }
    let remainingGoals ← withInfoHole mvarId <| Tactic.run mvarId do
       withTacticInfoContext tacticCode (evalTactic code)
       synthesizeSyntheticMVars (mayPostpone := false)
    unless remainingGoals.isEmpty do
      reportUnsolvedGoals remainingGoals

  /-- Try to synthesize the given pending synthetic metavariable. -/
  private partial def synthesizeSyntheticMVar (mvarSyntheticDecl : SyntheticMVarDecl) (postponeOnError : Bool) (runTactics : Bool) : TermElabM Bool :=
    withRef mvarSyntheticDecl.stx do
    match mvarSyntheticDecl.kind with
    | SyntheticMVarKind.typeClass => synthesizePendingInstMVar mvarSyntheticDecl.mvarId
    | SyntheticMVarKind.coe header? eNew expectedType eType e f? => synthesizePendingCoeInstMVar mvarSyntheticDecl.mvarId header? eNew expectedType eType e f?
    -- NOTE: actual processing at `synthesizeSyntheticMVarsAux`
    | SyntheticMVarKind.postponed savedContext => resumePostponed savedContext mvarSyntheticDecl.stx mvarSyntheticDecl.mvarId postponeOnError
    | SyntheticMVarKind.tactic tacticCode savedContext =>
      withSavedContext savedContext do
        if runTactics then
          runTactic mvarSyntheticDecl.mvarId tacticCode
          return true
        else
          return false
  /--
    Try to synthesize the current list of pending synthetic metavariables.
    Return `true` if at least one of them was synthesized. -/
  private partial def synthesizeSyntheticMVarsStep (postponeOnError : Bool) (runTactics : Bool) : TermElabM Bool := do
    let ctx ← read
    traceAtCmdPos `Elab.resuming fun _ =>
      m!"resuming synthetic metavariables, mayPostpone: {ctx.mayPostpone}, postponeOnError: {postponeOnError}"
    let syntheticMVars    := (← get).syntheticMVars
    let numSyntheticMVars := syntheticMVars.length
    -- We reset `syntheticMVars` because new synthetic metavariables may be created by `synthesizeSyntheticMVar`.
    modify fun s => { s with syntheticMVars := [] }
    -- Recall that `syntheticMVars` is a list where head is the most recent pending synthetic metavariable.
    -- We use `filterRevM` instead of `filterM` to make sure we process the synthetic metavariables using the order they were created.
    -- It would not be incorrect to use `filterM`.
    let remainingSyntheticMVars ← syntheticMVars.filterRevM fun mvarDecl => do
       -- We use `traceM` because we want to make sure the metavar local context is used to trace the message
       traceM `Elab.postpone (withMVarContext mvarDecl.mvarId do addMessageContext m!"resuming {mkMVar mvarDecl.mvarId}")
       let succeeded ← synthesizeSyntheticMVar mvarDecl postponeOnError runTactics
       trace[Elab.postpone] if succeeded then format "succeeded" else format "not ready yet"
       pure !succeeded
    -- Merge new synthetic metavariables with `remainingSyntheticMVars`, i.e., metavariables that still couldn't be synthesized
    modify fun s => { s with syntheticMVars := s.syntheticMVars ++ remainingSyntheticMVars }
    return numSyntheticMVars != remainingSyntheticMVars.length

  /--
    Try to process pending synthetic metavariables. If `mayPostpone == false`,
    then `syntheticMVars` is `[]` after executing this method.

    It keeps executing `synthesizeSyntheticMVarsStep` while progress is being made.
    If `mayPostpone == false`, then it applies default instances to `SyntheticMVarKind.typeClass` (if available)
    metavariables that are still unresolved, and then tries to resolve metavariables
    with `mayPostpone == false`. That is, we force them to produce error messages and/or commit to
    a "best option". If, after that, we still haven't made progress, we report "stuck" errors.

    Remark: we set `ignoreStuckTC := true` when elaborating `simp` arguments. Then,
    pending TC problems become implicit parameters for the simp theorem.
  -/
  partial def synthesizeSyntheticMVars (mayPostpone := true) (ignoreStuckTC := false) : TermElabM Unit :=
    let rec loop (u : Unit) : TermElabM Unit := do
      withRef (← getSomeSynthethicMVarsRef) <| withIncRecDepth do
        unless (← get).syntheticMVars.isEmpty do
          if ← synthesizeSyntheticMVarsStep (postponeOnError := false) (runTactics := false) then
            loop ()
          else if !mayPostpone then
            /- Resume pending metavariables with "elaboration postponement" disabled.
               We postpone elaboration errors in this step by setting `postponeOnError := true`.
               Example:
               ```
               #check let x := ⟨1, 2⟩; Prod.fst x
               ```
               The term `⟨1, 2⟩` can't be elaborated because the expected type is not know.
               The `x` at `Prod.fst x` is not elaborated because the type of `x` is not known.
               When we execute the following step with "elaboration postponement" disabled,
               the elaborator fails at `⟨1, 2⟩` and postpones it, and succeeds at `x` and learns
               that its type must be of the form `Prod ?α ?β`.

               Recall that we postponed `x` at `Prod.fst x` because its type it is not known.
               We the type of `x` may learn later its type and it may contain implicit and/or auto arguments.
               By disabling postponement, we are essentially giving up the opportunity of learning `x`s type
               and assume it does not have implict and/or auto arguments. -/
            if ← withoutPostponing <| synthesizeSyntheticMVarsStep (postponeOnError := true) (runTactics := false) then
              loop ()
            else if ← synthesizeUsingDefault then
              loop ()
            else if ← withoutPostponing <| synthesizeSyntheticMVarsStep (postponeOnError := false) (runTactics := false) then
              loop ()
            else if ← synthesizeSyntheticMVarsStep (postponeOnError := false) (runTactics := true) then
              loop ()
            else
              reportStuckSyntheticMVars ignoreStuckTC
    loop ()
end

def synthesizeSyntheticMVarsNoPostponing : TermElabM Unit :=
  synthesizeSyntheticMVars (mayPostpone := false)

/- Keep invoking `synthesizeUsingDefault` until it returns false. -/
private partial def synthesizeUsingDefaultLoop : TermElabM Unit := do
  if (← synthesizeUsingDefault) then
    synthesizeSyntheticMVars (mayPostpone := true)
    synthesizeUsingDefaultLoop

def synthesizeSyntheticMVarsUsingDefault : TermElabM Unit := do
  synthesizeSyntheticMVars (mayPostpone := true)
  synthesizeUsingDefaultLoop

private partial def withSynthesizeImp {α} (k : TermElabM α) (mayPostpone : Bool) (synthesizeDefault : Bool) : TermElabM α := do
  let syntheticMVarsSaved := (← get).syntheticMVars
  modify fun s => { s with syntheticMVars := [] }
  try
    let a ← k
    synthesizeSyntheticMVars mayPostpone
    if mayPostpone && synthesizeDefault then
      synthesizeUsingDefaultLoop
    return a
  finally
    modify fun s => { s with syntheticMVars := s.syntheticMVars ++ syntheticMVarsSaved }

/--
  Execute `k`, and synthesize pending synthetic metavariables created while executing `k` are solved.
  If `mayPostpone == false`, then all of them must be synthesized.
  Remark: even if `mayPostpone == true`, the method still uses `synthesizeUsingDefault` -/
@[inline] def withSynthesize [MonadFunctorT TermElabM m] [Monad m] (k : m α) (mayPostpone := false) : m α :=
  monadMap (m := TermElabM) (withSynthesizeImp . mayPostpone (synthesizeDefault := true)) k

/-- Similar to `withSynthesize`, but sets `mayPostpone` to `true`, and do not use `synthesizeUsingDefault` -/
@[inline] def withSynthesizeLight [MonadFunctorT TermElabM m] [Monad m] (k : m α) : m α :=
  monadMap (m := TermElabM) (withSynthesizeImp . (mayPostpone := true) (synthesizeDefault := false)) k

/-- Elaborate `stx`, and make sure all pending synthetic metavariables created while elaborating `stx` are solved. -/
def elabTermAndSynthesize (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
  withRef stx do
    instantiateMVars (← withSynthesize <| elabTerm stx expectedType?)

end Lean.Elab.Term
