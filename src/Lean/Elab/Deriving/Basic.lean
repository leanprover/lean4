/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command

namespace Lean.Elab
open Command

def DerivingHandler := (typeNames : Array Name) → CommandElabM Bool

builtin_initialize derivingHandlersRef : IO.Ref (NameMap DerivingHandler) ← IO.mkRef {}

def registerBuiltinDerivingHandler (className : Name) (handler : DerivingHandler) : IO Unit := do
  let initializing ← IO.initializing
  unless initializing do
    throw (IO.userError "failed to register deriving handler, it can only be registered during initialization")
  if (← derivingHandlersRef.get).contains className then
    throw (IO.userError s!"failed to register deriving handler, a handler has already been registered for '{className}'")
  derivingHandlersRef.modify fun m => m.insert className handler

def defaultHandler (className : Name) (typeNames : Array Name) : CommandElabM Unit := do
  throwError "default handlers have not been implemented yet, class: '{className}' types: {typeNames}"

def applyDerivingHandlers (className : Name) (typeNames : Array Name) : CommandElabM Unit := do
  match (← derivingHandlersRef.get).find? className with
  | some handler =>
    unless (← handler typeNames) do
      defaultHandler className typeNames
  | none => defaultHandler className typeNames

@[builtinCommandElab «deriving»] def elabDeriving : CommandElab
  | `(deriving instance $[$classes],* for $[$declNames],*) => do
     let classes ← classes.mapM (resolveGlobalConstNoOverload ·.getId)
     let declNames ← declNames.mapM (resolveGlobalConstNoOverload ·.getId)
     for cls in classes do
       try
         applyDerivingHandlers cls declNames
       catch ex =>
         logException ex
  | _ => throwUnsupportedSyntax

structure DerivingClassView where
  ref : Syntax
  className : Name

/- leading_parser optional (atomic ("deriving " >> notSymbol "instance") >> sepBy1 ident ", ") -/
def getOptDerivingClasses [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] (optDeriving : Syntax) : m (Array DerivingClassView) := do
  if optDeriving.isNone then
    return #[]
  else
    optDeriving[0][1].getSepArgs.mapM fun ident => do
      let className ← resolveGlobalConstNoOverload ident.getId
      return { ref := ident, className := className }

def DerivingClassView.applyHandlers (view : DerivingClassView) (declNames : Array Name) : CommandElabM Unit :=
  withRef view.ref do applyDerivingHandlers view.className declNames

builtin_initialize
  registerTraceClass `Elab.Deriving

end Lean.Elab
