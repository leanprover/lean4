/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.ToString.Basic
import Init.Ptr

universe u v

/-! # Debugging helper functions -/

set_option linter.unusedVariables.funArgs false in
@[never_extract, extern "lean_dbg_trace"]
def dbgTrace {α : Type u} (s : String) (f : Unit → α) : α := f ()

def dbgTraceVal {α : Type u} [ToString α] (a : α) : α :=
  dbgTrace (toString a) (fun _ => a)

set_option linter.unusedVariables.funArgs false in
/-- Display the given message if `a` is shared, that is, RC(a) > 1 -/
@[never_extract, extern "lean_dbg_trace_if_shared"]
def dbgTraceIfShared {α : Type u} (s : String) (a : α) : α := a

/-- Print stack trace to stderr before evaluating given closure. Currently supported on Linux only. -/
@[never_extract, extern "lean_dbg_stack_trace"]
def dbgStackTrace {α : Type u} (f : Unit → α) : α := f ()

@[extern "lean_dbg_sleep"]
def dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α := f ()

@[noinline] private def mkPanicMessage (modName : String) (line col : Nat) (msg : String) : String :=
  "PANIC at " ++ modName ++ ":" ++ toString line ++ ":" ++ toString col ++ ": " ++ msg

@[never_extract, inline] def panicWithPos {α : Sort u} [Inhabited α] (modName : String) (line col : Nat) (msg : String) : α :=
  panic (mkPanicMessage modName line col msg)

@[noinline] private def mkPanicMessageWithDecl (modName : String) (declName : String) (line col : Nat) (msg : String) : String :=
  "PANIC at " ++ declName ++ " " ++ modName ++ ":" ++ toString line ++ ":" ++ toString col ++ ": " ++ msg

@[never_extract, inline] def panicWithPosWithDecl {α : Sort u} [Inhabited α] (modName : String) (declName : String) (line col : Nat) (msg : String) : α :=
  panic (mkPanicMessageWithDecl modName declName line col msg)
