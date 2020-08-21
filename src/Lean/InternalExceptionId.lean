/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Lean

structure InternalExceptionId :=
(id : Nat)

def mkInternalExceptionsRef : IO (IO.Ref (Array Name)) :=
IO.mkRef #[]

@[init mkInternalExceptionsRef] constant internalExceptionsRef : IO.Ref (Array Name) := arbitrary _

def registerInternalExceptionId (name : Name) : IO InternalExceptionId := do
exs ← internalExceptionsRef.get;
when (exs.contains name) $ throw $ IO.userError ("invalid internal exception id, '" ++ toString name ++ "' has already been used");
let nextId := exs.size;
internalExceptionsRef.modify fun a => a.push name;
pure { id := nextId }

def InternalExceptionId.toString (id : InternalExceptionId) : IO Name :=  do
exs ← internalExceptionsRef.get;
pure $ exs.get! id.id

end Lean
