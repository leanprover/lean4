/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Wojciech Nawrocki
-/
module

prelude
public import Lean.Elab.App
public import Lean.Elab.Command
public import Lean.Elab.DeclarationRange
public import Lean.Elab.DeclNameGen
public meta import Lean.Parser.Command

public section

namespace Lean.Elab
open Command

structure DerivingClassView where
  ref : Syntax
  hasExpose : Bool
  cls : Term

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
Constructs an instance of the class `classExpr` by figuring out the correct position to insert `val`
to create a type `className ... val ...` such that there is already an instance for it.
The `declVal` argument is the value to use in place of `val` when creating the new instance.

Heuristics:
- `val` must not use an outParam.
- `val` should use an explicit parameter, or a parameter that has already been given a value.
- If there are multiple explicit parameters, we try each possibility.
- If the class has instance arguments, we require that they be synthesizable while synthesizing this instance.
  While we could allow synthesis failure and abstract such instances,
  we leave such conditional instances to be defined by users.
- If this all fails and `val` is a constant application, we try unfolding it once and try again.

For example, when deriving `MonadReader (ρ : outParam (Type u)) (m : Type u → Type v)`,
we will skip `ρ` and try using `m`.

Note that we try synthesizing instances even if there are still metavariables in the type.
If that succeeds, then one can abstract those metavariables and create a parameterized instance.
The abstraction is not done by this function.

Expects to be run with an empty message log.
-/
private partial def mkInst (classExpr : Expr) (declName : Name) (declVal val : Expr) : TermElabM MkInstResult := do
  let classExpr ← whnfCore classExpr
  let cls := classExpr.getAppFn
  let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType cls)
  for x in xs, y in classExpr.getAppArgs do
    x.mvarId!.assign y
  let classExpr := mkAppN cls xs
  let some className ← isClass? classExpr
    | throwError "Failed to delta derive instance for `{.ofConstName declName}`, not a class:{indentExpr classExpr}"
  let mut instMVars := #[]
  for x in xs, bi in bis do
    if !(← x.mvarId!.isAssigned) then
      -- Assumption: assigned inst implicits are already either solved or registered as synthetic
      if bi.isInstImplicit then
        x.mvarId!.setKind .synthetic
        instMVars := instMVars.push x.mvarId!
  let instVal ← mkFreshExprMVar classExpr (kind := .synthetic)
  instMVars := instMVars.push instVal.mvarId!
  let rec go (val : Expr) : TermElabM MkInstResult := do
    let val ← whnfCore val
    trace[Elab.Deriving] "Looking for arguments to `{classExpr}` that can be used for the value{indentExpr val}"
    -- Save the metacontext so that we can try each option in turn
    let state ← saveState
    let valTy ← inferType val
    let mut anyDefEqSuccess := false
    let mut messages : MessageLog := {}
    for x in xs, bi in bis, i in 0...xs.size do
      unless bi.isExplicit do
        continue
      let decl ← x.mvarId!.getDecl
      if decl.type.isOutParam then
        continue
      unless ← isMVarApp x do
        /-
        This is an argument supplied by the user, and it's not a `_`.
        This is to avoid counterintuitive behavior, like in the following example.
        Because `MyNat` unifies with `Nat`, it would otherwise generate an `HAdd MyNat Nat Nat` instance.
        Instead it generates an `HAdd Nat MyNat Nat` instance.
        ```
        def MyNat := Nat
        deriving instance HAdd Nat for MyNat
        ```
        Likely neither of these is the intended result, but the second is more justifiable.
        It's possible to have it return `MyNat` using `deriving instance HAdd Nat _ MyNat for MyNat`.
        -/
        continue
      unless ← isDefEqGuarded decl.type valTy <&&> isDefEqGuarded x val do
        restoreState state
        continue
      anyDefEqSuccess := true
      trace[Elab.Deriving] "Argument {i} gives option{indentExpr classExpr}"
      try
        -- Finish elaboration
        synthesizeAppInstMVars instMVars classExpr
        Term.synthesizeSyntheticMVarsNoPostponing
      catch ex =>
        trace[Elab.Deriving] "Option for argument {i} failed"
        logException ex
        messages := messages ++ (← Core.getMessageLog)
        restoreState state
        continue
      if (← MonadLog.hasErrors) then
        -- Sometimes elaboration only logs errors
        trace[Elab.Deriving] "Option for argument {i} failed, logged errors"
        messages := messages ++ (← Core.getMessageLog)
        restoreState state
        continue
      -- Success
      trace[Elab.Deriving] "Argument {i} option succeeded{indentExpr classExpr}"
      -- Create the type for the declaration itself.
      let xs' := xs.set! i declVal
      let instType := mkAppN cls xs'
      return { instType, instVal }
    try
      if let some val' ← unfoldDefinition? val then
        return ← withTraceNode `Elab.Deriving (fun _ => return m!"Unfolded value to {val'}") <| go val'
    catch ex =>
      if !messages.hasErrors then
        throw ex
      Core.resetMessageLog
    if !anyDefEqSuccess then
      throwDeltaDeriveFailure className declName (m!"the class has no explicit non-out-param parameters where\
        {indentExpr declVal}\n\
        can be inserted.")
    else
      Core.setMessageLog (messages ++ (← Core.getMessageLog))
      throwDeltaDeriveFailure className declName none
        (.note m!"Delta deriving tries the following strategies: \
            (1) inserting the definition into each explicit non-out-param parameter of a class and \
            (2) unfolding definitions further.")
  go val

/--
Delta deriving handler. Creates an instance of class `classStx` for `decl`.
The elaborated class expression may be underapplied (e.g. `Decidable` instead of `Decidable _`),
and may be `decl`.
If unfolding `decl` results in an underapplied lambda, then this enters the body of the lambda.
We prevent `classStx` from referring to these local variables; instead it's expected that one uses section variables.

This function can handle being run from within a nontrivial local context,
and it uses `mkValueTypeClosure` to construct the final instance.
-/
def processDefDeriving (view : DerivingClassView) (decl : Expr) : TermElabM Unit := do
  let { cls := classStx, hasExpose := _ /- todo? -/, .. } := view
  let decl ← whnfCore decl
  let .const declName _ := decl.getAppFn
    | throwError "Failed to delta derive instance, expecting a term of the form `C ...` where `C` is a constant, given{indentExpr decl}"
  -- When the definition is private, the deriving handler will need access to the private scope,
  -- and we make sure to put the instance in the private scope.
  withoutExporting (when := isPrivateName declName) do
  let ConstantInfo.defnInfo info ← getConstInfo declName
    | throwError "Failed to delta derive instance, `{.ofConstName declName}` is not a definition."
  let value := info.value.beta decl.getAppArgs
  let result : Closure.MkValueTypeClosureResult ←
    -- Assumption: users intend delta deriving to apply to the body of a definition, even if in the source code
    -- the function is written as a lambda expression.
    -- Furthermore, we don't use `forallTelescope` because users want to derive instances for monads.
    lambdaTelescope value fun xs value => withoutErrToSorry do
      let decl := mkAppN decl xs
      -- Make these local variables inaccessible.
      let lctx ← xs.foldlM (init := ← getLCtx) fun lctx x => do
        pure <| lctx.setUserName x.fvarId! (← mkFreshUserName <| (lctx.find? x.fvarId!).get!.userName)
      withLCtx' lctx do
        let msgLog ← Core.getMessageLog
        Core.resetMessageLog
        try
          -- We need to elaborate the class within this context to ensure metavariables can unify with `xs`.
          let classExpr ← elabTerm classStx none
          synthesizeSyntheticMVars (postpone := .partial)
          if (← MonadLog.hasErrors) then
            throwAbortTerm
          -- We allow `classExpr` to be a pi type, to support giving more hypotheses to the derived instance.
          -- (Possibly `classExpr` is not a type due to being underapplied, but `forallTelescopeReducing` tolerates this.)
          -- We don't reduce because of abbreviations such as `DecidableEq`
          forallTelescope classExpr fun _ classExpr => do
            let result ← mkInst classExpr declName decl value
            Closure.mkValueTypeClosure result.instType result.instVal (zetaDelta := true)
        finally
          Core.setMessageLog (msgLog ++ (← Core.getMessageLog))
  let env ← getEnv
  let mut instName := (← getCurrNamespace) ++ (← NameGen.mkBaseNameWithSuffix "inst" result.type)
  -- We don't have a facility to let users override derived names, so make an unused name if needed.
  instName ← liftMacroM <| mkUnusedBaseName instName
  -- Make the instance private if the declaration is private.
  if isPrivateName declName then
    instName := mkPrivateName env instName
  let hints := ReducibilityHints.regular (getMaxHeight env result.value + 1)
  let decl ← mkDefinitionValInferringUnsafe instName result.levelParams.toList result.type result.value hints
  addAndCompile (logCompileErrors := !(← read).isNoncomputableSection) <| Declaration.defnDecl decl
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

def applyDerivingHandlers (className : Name) (typeNames : Array Name) (setExpose := false) : CommandElabM Unit := do
  withScope (fun sc => { sc with
    attrs := if setExpose then Unhygienic.run `(Parser.Term.attrInstance| expose) :: sc.attrs else sc.attrs
    -- Deactivate some linting options that only make writing deriving handlers more painful.
    opts := sc.opts.setBool `warn.exposeOnPrivate false
    -- When any of the types are private, the deriving handler will need access to the private scope
    -- and should create private instances.
    isPublic := !typeNames.any isPrivateName }) do
  withTraceNode `Elab.Deriving (fun _ => return m!"running deriving handlers for `{.ofConstName className}`") do
    match (← derivingHandlersRef.get).find? className with
    | some handlers =>
      for handler in handlers do
        if (← handler typeNames) then
          return ()
      throwError "None of the deriving handlers for class `{.ofConstName className}` applied to \
        {.andList <| typeNames.toList.map (m!"`{.ofConstName ·}`")}"
    | none => throwError "No deriving handlers have been implemented for class `{.ofConstName className}`"

open Parser.Command

def DerivingClassView.getClassName (view : DerivingClassView) : CoreM Name :=
  realizeGlobalConstNoOverloadWithInfo view.cls

def DerivingClassView.ofSyntax : TSyntax ``derivingClass → CoreM DerivingClassView
  | `(Parser.Command.derivingClass| $[@[expose%$expTk?]]? $cls:term) => do
    return { ref := cls, cls, hasExpose := expTk?.isSome }
  | _ => throwUnsupportedSyntax

def getOptDerivingClasses (optDeriving : Syntax) : CoreM (Array DerivingClassView) := do
  match optDeriving with
  | `(Parser.Command.optDeriving| deriving $[$classes],*) => classes.mapM DerivingClassView.ofSyntax
  | _ => return #[]

def DerivingClassView.applyHandlers (view : DerivingClassView) (declNames : Array Name) : CommandElabM Unit :=
  withRef view.ref do
    applyDerivingHandlers (setExpose := view.hasExpose) (← liftCoreM <| view.getClassName) declNames

private def elabDefDeriving (classes : Array DerivingClassView) (decls : Array Syntax) :
    CommandElabM Unit := runTermElabM fun _ => do
  for decl in decls do
    withRef decl <| withLogging do
      let declExpr ←
        if decl.isIdent then
          let declName ← realizeGlobalConstNoOverload decl
          let info ← getConstInfo declName
          unless info.isDefinition do
            throwError (m!"Declaration `{.ofConstName declName}` is not a definition."
              ++ .note m!"When any declaration is a definition, this command goes into delta deriving mode, \
                    which applies only to definitions. \
                    Delta deriving unfolds definitions and infers pre-existing instances.")
          -- Use the declaration's level parameters, to ensure the instance is fully universe polymorphic
          mkConstWithLevelParams declName
        else
          Term.elabTermAndSynthesize decl none
      for cls in classes do
        withLogging do
        withTraceNode `Elab.Deriving (fun _ => return m!"running delta deriving handler for `{cls.cls}` and definition `{declExpr}`") do
          Term.processDefDeriving cls declExpr


@[builtin_command_elab «deriving»] def elabDeriving : CommandElab
  | `(deriving instance $[$classes],* for $[$decls],*) => do
    let classes ← liftCoreM <| classes.mapM DerivingClassView.ofSyntax
    let decls : Array Syntax := decls
    if decls.all Syntax.isIdent then
      let declNames ← liftCoreM <| decls.mapM (realizeGlobalConstNoOverloadWithInfo ·)
      -- If any of the declarations are definitions, then we commit to delta deriving.
      let infos ← declNames.mapM getConstInfo
      if infos.any (·.isDefinition) then
        elabDefDeriving classes decls
      else
        -- Otherwise, we commit to using deriving handlers.
        for cls in classes do
          cls.applyHandlers declNames
    else
      elabDefDeriving classes decls
  | _ => throwUnsupportedSyntax

builtin_initialize
  registerTraceClass `Elab.Deriving

end Lean.Elab
