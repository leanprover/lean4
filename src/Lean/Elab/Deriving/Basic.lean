/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Wojciech Nawrocki
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Elab.DeclarationRange
public meta import Lean.Parser.Command

public section

namespace Lean.Elab
open Command

namespace Term
open Meta

/-- Result for `mkInst` -/
private structure MkInstResult where
  instType   : Expr
  instVal    : Expr

private def throwDeltaDeriveFailure (className declName : Name) (msg? : Option MessageData) (suffix : MessageData := "") : MetaM α :=
  let suffix := if let some msg := msg? then m!", {msg}{suffix}" else m!".{suffix}"
  throwError "Failed to delta derive `{.ofConstName className}` instance for `{.ofConstName declName}`{suffix}"

/--
Constructs an instance of the class `className` by figuring out the correct position to insert `val`
to create a type `className ... val ...` such that there is already an instance for it.
The `declVal` argument is the value to use in place of `val` when creating the new instance.

Heuristics:
- `val` must not be an outParam.
- `val` should be an explicit parameter.
- If there are multiple explicit parameters, we try each possibility.
- If this all fails and `val` is a constant application, we try unfolding it once and try again.

For example, when deriving `MonadReader (ρ : outParam (Type u)) (m : Type u → Type v)`,
we will skip `ρ` and try using `m`.

Note that we try synthesizing instances even if there are still metavariables in the type.
If that succeeds, then we can abstract the metavariables and create a parameterized instance.
The result might still have universe level metavariables, though it is unlikely.
-/
private partial def mkInst (className declName : Name) (declVal val : Expr) : MetaM MkInstResult := do
  let cls ← mkConstWithFreshMVarLevels className
  let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType cls)
  let instType := mkAppN cls xs
  unless (← isClass? instType).isSome do
    throwDeltaDeriveFailure className declName m!"`{.ofConstName className}` is not a class."
  let inst ← mkFreshExprMVar instType
  let rec go (val : Expr) : MetaM MkInstResult := do
    let val ← whnfCore val
    trace[Elab.Deriving] "Looking for arguments to `{instType}` that can be used for the value{indentExpr val}"
    -- Save the metacontext so that we can try each option in turn
    let mctx ← getMCtx
    let valTy ← inferType val
    let mut failures : Array MessageData := #[]
    for x in xs, bi in bis, i in 0...xs.size do
      setMCtx mctx
      unless bi.isExplicit do
        continue
      let decl ← x.mvarId!.getDecl
      if decl.type.isOutParam then
        continue
      unless ← isDefEqGuarded decl.type valTy <&&> isDefEqGuarded x val do
        continue
      trace[Elab.Deriving] "Argument {i} gives option{indentExpr instType}"
      try
        synthAppInstances `deriving inst.mvarId! (xs.push inst) (bis.push .instImplicit) (synthAssignedInstances := true) (allowSynthFailures := false)
      catch ex =>
        trace[Elab.Deriving] "Option for argument {i} failed"
        if !(← inst.mvarId!.isAssigned) then
          failures := failures.push <| ← addMessageContext m!"Failed to synthesize instance\n{inst.mvarId!}"
        else
          failures := failures.push <| ← addMessageContext m!"Failed to synthesize{indentExpr instType}\nError:{ex.toMessageData}"
        continue
      -- Success
      trace[Elab.Deriving] "Argument {i} option succeeded{indentExpr instType}"
      -- Create the type for the declaration itself.
      let xs' := xs.set! i declVal
      let declInstType := mkAppN cls xs'
      -- If there are metavariables, we can abstract them to make a parameterized instance.
      let (xs, bis) ← Array.unzip <$> (xs.zip bis).filterM fun (x, _) => not <$> x.mvarId!.isAssigned
      let instType ← mkForallFVars xs declInstType
      let instType := instType.updateForallBinderInfos (bis.toList.map some)
      let instVal ← mkLambdaFVars xs inst
      return { instType, instVal }
    setMCtx mctx
    try
      if let some val' ← unfoldDefinition? val then
        return ← withTraceNode `Elab.Deriving (fun _ => return m!"Unfolded value to {val'}") <| go val'
    catch ex =>
      if failures.isEmpty then
        throw ex
    if failures.isEmpty then
      throwDeltaDeriveFailure className declName (m!"the class has no explicit non-out-param parameters where\
        {indentExpr declVal}\n\
        can be inserted.")
    else
      throwDeltaDeriveFailure className declName none
        (m!"\n\n"
          ++ MessageData.joinSep (failures.toList) m!"\n\n"
          ++ .note m!"Delta deriving tries the following strategies: \
              (1) inserting the definition into each explicit non-out-param parameter of a class and \
              (2) further unfolding of definitions.")
  go val

def processDefDeriving (className declName : Name) : TermElabM Unit := do
  let ConstantInfo.defnInfo info ← getConstInfo declName
    | throwDeltaDeriveFailure className declName m!"declaration is not a definition."
  -- Assumption: users intend delta deriving to apply to the body of a definition, even if in the source code
  -- the function is written as a lambda expression.
  let result : MkInstResult ← lambdaTelescope info.value fun xs value => do
    let declVal := mkAppN (.const declName (info.levelParams.map .param)) xs
    let result ← mkInst className declName declVal value
    pure { instType := ← mkForallFVars xs result.instType
           instVal := ← mkLambdaFVars xs result.instVal }
  let r := (← getMCtx).levelMVarToParam info.levelParams.contains (fun _ => false) (← instantiateMVars result.instType)
  setMCtx r.mctx
  let instType ← instantiateMVars r.expr
  let instValue ← instantiateMVars result.instVal
  Meta.check instType
  -- Note: if declName is private then this name is private as well.
  let instName ← liftMacroM <| mkUnusedBaseName (declName.appendBefore "inst" |>.appendAfter className.getString!)
  addAndCompile <| Declaration.defnDecl {
    name        := instName
    levelParams := info.levelParams ++ r.newParamNames.toList
    type        := instType
    value       := instValue
    hints       := info.hints
    safety      := info.safety
  }
  trace[Elab.Deriving] "Derived instance `{.ofConstName instName}`"
  addInstance instName AttributeKind.global (eval_prio default)
  addDeclarationRangesFromSyntax instName (← getRef)

end Term

@[expose] def DerivingHandler := (typeNames : Array Name) → CommandElabM Bool

builtin_initialize derivingHandlersRef : IO.Ref (NameMap (List DerivingHandler)) ← IO.mkRef {}

/--
Registers a deriving handler for a class. This function should be called in an `initialize` block.

A `DerivingHandler` is called on the fully qualified names of all types it is running for. For
example, `deriving instance Foo for Bar, Baz` invokes ``fooHandler #[`Bar, `Baz]``.
-/
def registerDerivingHandler (className : Name) (handler : DerivingHandler) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register deriving handler, it can only be registered during initialization")
  derivingHandlersRef.modify fun m => match m.find? className with
    | some handlers => m.insert className (handler :: handlers)
    | none => m.insert className [handler]

def applyDerivingHandlers (className : Name) (typeNames : Array Name) : CommandElabM Unit := do
  withTraceNode `Elab.Deriving (fun _ => return m!"running deriving handlers for `{.ofConstName className}`") do
    match (← derivingHandlersRef.get).find? className with
    | some handlers =>
      for handler in handlers do
        if (← handler typeNames) then
          return ()
      throwError "None of the deriving handlers for class `{.ofConstName className}` applied to the types \
        {.andList <| typeNames.toList.map (m!"`{.ofConstName ·}`")}"
    | none => throwError "No deriving handlers have been implemented for class `{.ofConstName className}`"

private def applyDefHandler (className : Name) (declName : Name) : CommandElabM Unit :=
  withTraceNode `Elab.Deriving (fun _ => return m!"running delta deriving handler for `{.ofConstName className}` and definition `{.ofConstName declName}`") do
    liftTermElabM do Term.processDefDeriving className declName

@[builtin_command_elab «deriving»] def elabDeriving : CommandElab
  | `(deriving instance $[$classIdents],* for $[$declIdents],*) => do
    let classNames ← liftCoreM <| classIdents.mapM realizeGlobalConstNoOverloadWithInfo
    let declNames ← liftCoreM <| declIdents.mapM realizeGlobalConstNoOverloadWithInfo
    -- When any of the types are private, the deriving handler will need access to the private scope
    -- (and should also make sure to put its outputs in the private scope).
    withoutExporting (when := declNames.any isPrivateName) do
      -- If any of the declarations are definitions, then we commit to delta deriving.
      let infos ← declNames.mapM getConstInfo
      if infos.any (·.isDefinition) then
        -- When delta deriving, we require that all of the declarations be definitions
        for info in infos, ref in declIdents, declName in declNames do
          unless info.isDefinition do
            throwErrorAt ref (m!"Declaration `{.ofConstName declName}` is not a definition."
              ++ .note m!"When any declaration is a definition, this command goes into delta deriving mode, \
                    which applies only to definitions. \
                    Delta deriving unfolds definitions and infers pre-existing instances.")
          for className in classNames do
            for declName in declNames, declIdent in declIdents do
              withRef declIdent <| withLogging <| applyDefHandler className declName
      else
        for className in classNames, classIdent in classIdents do
          withRef classIdent <| withLogging <| applyDerivingHandlers className declNames
  | _ => throwUnsupportedSyntax

structure DerivingClassView where
  ref : Syntax
  className : Name

def getOptDerivingClasses (optDeriving : Syntax) : CoreM (Array DerivingClassView) := do
  match optDeriving with
  | `(Parser.Command.optDeriving| deriving $[$classes],*) =>
    let mut ret := #[]
    for cls in classes do
      let className ← realizeGlobalConstNoOverloadWithInfo cls
      ret := ret.push { ref := cls, className := className }
    return ret
  | _ => return #[]

def DerivingClassView.applyHandlers (view : DerivingClassView) (declNames : Array Name) : CommandElabM Unit :=
  withRef view.ref do applyDerivingHandlers view.className declNames

builtin_initialize
  registerTraceClass `Elab.Deriving

end Lean.Elab
