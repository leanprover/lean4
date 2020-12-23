/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Lean

structure InternalExceptionId where
  idx : Nat := 0
  deriving Inhabited, BEq

builtin_initialize internalExceptionsRef : IO.Ref (Array Name) ← IO.mkRef #[]

def registerInternalExceptionId (name : Name) : IO InternalExceptionId := do
  let exs ← internalExceptionsRef.get
  if exs.contains name then throw $ IO.userError s!"invalid internal exception id, '{name}' has already been used"
  let nextIdx := exs.size
  internalExceptionsRef.modify fun a => a.push name
  pure { idx := nextIdx }

def InternalExceptionId.toString (id : InternalExceptionId) : String :=
  s!"internal exception #{id.idx}"

def InternalExceptionId.getName (id : InternalExceptionId) : IO Name :=  do
  let exs ← internalExceptionsRef.get
  let i := id.idx;
  if h : i < exs.size then
    pure $ exs.get ⟨i, h⟩
  else
    throw $ IO.userError "invalid internal exception id"

end Lean
