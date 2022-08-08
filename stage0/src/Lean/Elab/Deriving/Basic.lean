/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Wojciech Nawrocki
-/
import Lean.Elab.Command
import Lean.Elab.MutualDef

namespace Lean.Elab
open Command

def DerivingHandler := (typeNames : Array Name) → (args? : Option (TSyntax ``Parser.Term.structInst)) → CommandElabM Bool
def DerivingHandlerNoArgs := (typeNames : Array Name) → CommandElabM Bool

builtin_initialize derivingHandlersRef : IO.Ref (NameMap (List DerivingHandler)) ← IO.mkRef {}

/-- A `DerivingHandler` is called on the fully qualified names of all types it is running for
as well as the syntax of a `with` argument, if present.

For example, `deriving instance Foo with fooArgs for Bar, Baz` invokes
``fooHandler #[`Bar, `Baz] `(fooArgs)``. -/
def registerDerivingHandlerWithArgs (className : Name) (handler : DerivingHandler) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register deriving handler, it can only be registered during initialization")
  derivingHandlersRef.modify fun m => match m.find? className with
    | some handlers => m.insert className (handler :: handlers)
    | none => m.insert className [handler]

/-- Like `registerBuiltinDerivingHandlerWithArgs` but ignoring any `with` argument. -/
def registerDerivingHandler (className : Name) (handler : DerivingHandlerNoArgs) : IO Unit := do
  registerDerivingHandlerWithArgs className fun typeNames _ => handler typeNames

def defaultHandler (className : Name) (typeNames : Array Name) : CommandElabM Unit := do
  throwError "default handlers have not been implemented yet, class: '{className}' types: {typeNames}"

def applyDerivingHandlers (className : Name) (typeNames : Array Name) (args? : Option (TSyntax ``Parser.Term.structInst)) : CommandElabM Unit := do
  match (← derivingHandlersRef.get).find? className with
  | some handlers =>
    for handler in handlers do
      if (← handler typeNames args?) then
        return ()
    defaultHandler className typeNames
  | none => defaultHandler className typeNames

private def tryApplyDefHandler (className : Name) (declName : Name) : CommandElabM Bool :=
  liftTermElabM do
    Term.processDefDeriving className declName

@[builtinCommandElab «deriving»] def elabDeriving : CommandElab
  | `(deriving instance $[$classes $[with $argss?]?],* for $[$declNames],*) => do
     let declNames ← declNames.mapM resolveGlobalConstNoOverloadWithInfo
     for cls in classes, args? in argss? do
       try
         let className ← resolveGlobalConstNoOverloadWithInfo cls
         withRef cls do
           if declNames.size == 1 && args?.isNone then
             if (← tryApplyDefHandler className declNames[0]!) then
               return ()
           applyDerivingHandlers className declNames args?
       catch ex =>
         logException ex
  | _ => throwUnsupportedSyntax

structure DerivingClassView where
  ref : Syntax
  className : Name
  args? : Option (TSyntax ``Parser.Term.structInst)

def getOptDerivingClasses [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] [MonadInfoTree m] (optDeriving : Syntax) : m (Array DerivingClassView) := do
  match optDeriving with
  | `(Parser.Command.optDeriving| deriving $[$classes $[with $argss?]?],*) =>
    let mut ret := #[]
    for cls in classes, args? in argss? do
      let className ← resolveGlobalConstNoOverloadWithInfo cls
      ret := ret.push { ref := cls, className := className, args? }
    return ret
  | _ => return #[]

def DerivingClassView.applyHandlers (view : DerivingClassView) (declNames : Array Name) : CommandElabM Unit :=
  withRef view.ref do applyDerivingHandlers view.className declNames view.args?

builtin_initialize
  registerTraceClass `Elab.Deriving

end Lean.Elab
