/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Lean.Util.Trace

public section

open Lean

namespace Lean.SimpLC

abbrev NamePair := Name × Name

initialize simpLCAllowExt : SimplePersistentEnvExtension NamePair (Array NamePair) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.flatMap id
  }

def isCriticalPairAllowed {m : Type → Type} [Monad m] [MonadEnv m] (pair : NamePair) : m Bool := do
  let pair := match pair with | (x,y) => if y.quickLt x then (y,x) else (x,y)
  return simpLCAllowExt.getState (← getEnv) |>.contains pair


initialize simpLCIgnoreExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.flatMap id
  }

def ignoreName {m : Type → Type} [Monad m] [MonadEnv m] (n : Name) : m Unit := do
  modifyEnv (simpLCIgnoreExt.addEntry · n)

def isIgnoredName {m : Type → Type} [Monad m] [MonadEnv m] (n : Name) : m Bool := do
  return simpLCIgnoreExt.getState (← getEnv) |>.contains n

initialize
  Lean.registerTraceClass `simplc

register_option simplc.stderr : Bool := {
  defValue := false
  descr := "Print steps to stderr (useful when it crashes)"
}

register_option simplc.checkAllow : Bool := {
  defValue := true
  descr := "`simp_lc allow` to warn if the pair is actually ok"
}

end Lean.SimpLC

end -- public section
