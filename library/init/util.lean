/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.format
universes u

/-- This function has a native implementation that tracks time. -/
def timeit {α : Type u} (s : string) (f : thunk α) : α :=
f ()

/-- This function has a native implementation that displays the given string in the regular output stream. -/
def trace {α : Type u} (s : string) (f : thunk α) : α :=
f ()

meta def trace_val {α : Type u} [has_to_format α] (f : α) : α :=
trace (to_fmt f).to_string f

/-- This function has a native implementation that shows the VM call stack. -/
def trace_call_stack {α : Type u} (f : thunk α) : α :=
f ()

/-- This function has a native implementation that displays in the given position all trace messages used in f.
   The arguments line and col are filled by the elaborator. -/
def scope_trace {α : Type u} {line col: nat} (f : thunk α) : α :=
f ()

/--
  This function has a native implementation where
  the thunk is interrupted if it takes more than 'max' "heartbeats" to compute it.
  The heartbeat is approx. the maximum number of memory allocations (in thousands) performed by 'f ()'.
  This is a deterministic way of interrupting long running tasks. -/
meta def try_for {α : Type u} (max : nat) (f : thunk α) : option α :=
some (f ())

meta constant undefined_core {α : Sort u} (message : string) : α

meta def undefined {α : Sort u} : α := undefined_core "undefined"

meta def unchecked_cast {α : Sort u} {β : Sort u} : α → β :=
cast undefined
