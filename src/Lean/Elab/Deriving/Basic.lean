/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Wojciech Nawrocki
-/
prelude
import Lean.Elab.Command
import Lean.Elab.DeclarationRange

namespace Lean.Elab
open Command

namespace Term
open Meta

/-- Result for `mkInst?` -/
structure MkInstResult where
  instVal   : Expr
  instType  : Expr
  outParams : Array Expr := #[]

/--
  Construct an instance for `className out₁ ... outₙ type`.
  The method support classes with a prefix of `outParam`s (e.g. `MonadReader`). -/
private partial def mkInst? (className : Name) (type : Expr) : MetaM (Option MkInstResult) := do
  let rec go? (instType instTypeType : Expr) (outParams : Array Expr) : MetaM (Option MkInstResult) := do
    let instTypeType ← whnfD instTypeType
    unless instTypeType.isForall do
      return none
    let d := instTypeType.bindingDomain!
    if d.isOutParam then
      let mvar ← mkFreshExprMVar d
      go? (mkApp instType mvar) (instTypeType.bindingBody!.instantiate1 mvar) (outParams.push mvar)
    else
      unless (← isDefEqGuarded (← inferType type) d) do
        return none
      let instType ← instantiateMVars (mkApp instType type)
      let instVal ← synthInstance instType
      return some { instVal, instType, outParams }
  let instType ← mkConstWithFreshMVarLevels className
  go? instType (← inferType instType) #[]

def processDefDeriving (className : Name) (declName : Name) : TermElabM Bool := do
  try
    let ConstantInfo.defnInfo info ← getConstInfo declName | return false
    let some result ← mkInst? className info.value | return false
    let instTypeNew := mkApp result.instType.appFn! (Lean.mkConst declName (info.levelParams.map mkLevelParam))
    Meta.check instTypeNew
    let instName ← liftMacroM <| mkUnusedBaseName (declName.appendBefore "inst" |>.appendAfter className.getString!)
    addAndCompile <| Declaration.defnDecl {
      name        := instName
      levelParams := info.levelParams
      type        := (← instantiateMVars instTypeNew)
      value       := (← instantiateMVars result.instVal)
      hints       := info.hints
      safety      := info.safety
    }
    addInstance instName AttributeKind.global (eval_prio default)
    addDeclarationRangesFromSyntax instName (← getRef)
    return true
  catch _ =>
    return false

end Term

def DerivingHandler := (typeNames : Array Name) → CommandElabM Bool

/-- Deprecated - `DerivingHandler` no longer assumes arguments -/
@[deprecated DerivingHandler (since := "2024-09-09")]
def DerivingHandlerNoArgs := (typeNames : Array Name) → CommandElabM Bool

builtin_initialize derivingHandlersRef : IO.Ref (NameMap (List DerivingHandler)) ← IO.mkRef {}

/-- A `DerivingHandler` is called on the fully qualified names of all types it is running for
as well as the syntax of a `with` argument, if present.

For example, `deriving instance Foo with fooArgs for Bar, Baz` invokes
``fooHandler #[`Bar, `Baz] `(fooArgs)``. -/
def registerDerivingHandler (className : Name) (handler : DerivingHandler) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register deriving handler, it can only be registered during initialization")
  derivingHandlersRef.modify fun m => match m.find? className with
    | some handlers => m.insert className (handler :: handlers)
    | none => m.insert className [handler]

def defaultHandler (className : Name) (typeNames : Array Name) : CommandElabM Unit := do
  throwError "default handlers have not been implemented yet, class: '{className}' types: {typeNames}"

def applyDerivingHandlers (className : Name) (typeNames : Array Name) : CommandElabM Unit := do
  withTraceNode `Elab.Deriving (fun _ => return m!"running deriving handlers for '{className}'") do
    match (← derivingHandlersRef.get).find? className with
    | some handlers =>
      for handler in handlers do
        if (← handler typeNames) then
          return ()
      defaultHandler className typeNames
    | none => defaultHandler className typeNames

private def tryApplyDefHandler (className : Name) (declName : Name) : CommandElabM Bool :=
  liftTermElabM do
    Term.processDefDeriving className declName

@[builtin_command_elab «deriving»] def elabDeriving : CommandElab
  | `(deriving instance $[$classes],* for $[$declNames],*) => do
     let declNames ← liftCoreM <| declNames.mapM realizeGlobalConstNoOverloadWithInfo
     for cls in classes do
       try
         let className ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo cls
         withRef cls do
           if declNames.size == 1 then
             if (← tryApplyDefHandler className declNames[0]!) then
               return ()
           applyDerivingHandlers className declNames
       catch ex =>
         logException ex
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
