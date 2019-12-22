/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.ToString

universes u v
/- debugging helper functions -/
@[neverExtract, extern "lean_dbg_trace"]
def dbgTrace {α : Type u} (s : String) (f : Unit → α) : α :=
f ()

/- Display the given message if `a` is shared, that is, RC(a) > 1 -/
@[neverExtract, extern "lean_dbg_trace_if_shared"]
def dbgTraceIfShared {α : Type u} (s : String) (a : α) : α :=
a

@[extern "lean_dbg_sleep"]
def dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α :=
f ()

@[extern c inline "#4"]
unsafe def unsafeCast {α : Type u} {β : Type v} [inh : @& Inhabited β] (a : α) : β := arbitrary _

@[neverExtract, extern "lean_panic_fn"]
constant panic {α : Type u} [Inhabited α] (msg : String) : α := arbitrary _

@[noinline] private def mkPanicMessage (modName : String) (line col : Nat) (msg : String) : String :=
"PANIC at " ++ modName ++ ":" ++ toString line ++ ":" ++ toString col ++ ": " ++ msg

@[neverExtract, inline] def panicWithPos {α : Type u} [Inhabited α] (modName : String) (line col : Nat) (msg : String) : α :=
panic (mkPanicMessage modName line col msg)

-- TODO: should be a macro
@[neverExtract, noinline, nospecialize] def unreachable! {α : Type u} [Inhabited α] : α :=
panic! "unreachable"
