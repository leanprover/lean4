/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.System.IO
namespace Lean

/-- Internal exception identifier -/
structure InternalExceptionId where
  idx : Nat := 0
  deriving Inhabited, BEq

/-- Internal exceptions registered in the system. -/
builtin_initialize internalExceptionsRef : IO.Ref (Array Name) ← IO.mkRef #[]

/--
Register a new internal exception in the system.
Each internal exception has a unique index.
Throw an exception if the given name is not unique.
This method is usually invoked using the `initialize` command.
-/
def registerInternalExceptionId (name : Name) : IO InternalExceptionId := do
  let exs ← internalExceptionsRef.get
  if exs.contains name then throw <| IO.userError s!"invalid internal exception id, '{name}' has already been used"
  let nextIdx := exs.size
  internalExceptionsRef.modify fun a => a.push name
  pure { idx := nextIdx }

/-- Convert internal exception id into the message "internal exception #<idx>"-/
def InternalExceptionId.toString (id : InternalExceptionId) : String :=
  s!"internal exception #{id.idx}"

/-- Retrieve the name used to register the internal exception. -/
def InternalExceptionId.getName (id : InternalExceptionId) : IO Name :=  do
  let exs ← internalExceptionsRef.get
  let i := id.idx;
  if h : i < exs.size then
    return exs[i]
  else
    throw <| IO.userError "invalid internal exception id"

end Lean
