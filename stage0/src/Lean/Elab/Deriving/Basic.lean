/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Wojciech Nawrocki
-/
import Lean.Elab.Command
import Lean.Elab.MutualDef

namespace Lean.Elab
open Command

def DerivingHandler := (typeNames : Array Name) → (args? : Option Syntax) → CommandElabM Bool
def DerivingHandlerNoArgs := (typeNames : Array Name) → CommandElabM Bool

builtin_initialize derivingHandlersRef : IO.Ref (NameMap DerivingHandler) ← IO.mkRef {}

def registerBuiltinDerivingHandlerWithArgs (className : Name) (handler : DerivingHandler) : IO Unit := do
  let initializing ← IO.initializing
  unless initializing do
    throw (IO.userError "failed to register deriving handler, it can only be registered during initialization")
  if (← derivingHandlersRef.get).contains className then
    throw (IO.userError s!"failed to register deriving handler, a handler has already been registered for '{className}'")
  derivingHandlersRef.modify fun m => m.insert className handler

def registerBuiltinDerivingHandler (className : Name) (handler : DerivingHandlerNoArgs) : IO Unit := do
  registerBuiltinDerivingHandlerWithArgs className fun typeNames _ => handler typeNames

def defaultHandler (className : Name) (typeNames : Array Name) : CommandElabM Unit := do
  throwError "default handlers have not been implemented yet, class: '{className}' types: {typeNames}"

def applyDerivingHandlers (className : Name) (typeNames : Array Name) (args? : Option Syntax) : CommandElabM Unit := do
  match (← derivingHandlersRef.get).find? className with
  | some handler =>
    unless (← handler typeNames args?) do
      defaultHandler className typeNames
  | none => defaultHandler className typeNames

private def tryApplyDefHandler (className : Name) (declName : Name) : CommandElabM Bool :=
  liftTermElabM none do
    Term.processDefDeriving className declName

@[builtinCommandElab «deriving»] def elabDeriving : CommandElab
  | `(deriving instance $[$classes $[with $argss?]?],* for $[$declNames],*) => do
     let declNames ← declNames.mapM resolveGlobalConstNoOverloadWithInfo
     for cls in classes, args? in argss? do
       try
         let className ← resolveGlobalConstNoOverloadWithInfo cls
         withRef cls do
           if declNames.size == 1 && args?.isNone then
             if (← tryApplyDefHandler className declNames[0]) then
               return ()
           applyDerivingHandlers className declNames args?
       catch ex =>
         logException ex
  | _ => throwUnsupportedSyntax

structure DerivingClassView where
  ref : Syntax
  className : Name
  args? : Option Syntax

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
