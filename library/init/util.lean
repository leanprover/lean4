/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.string.basic
universe variables u

/- This function has a native implementation that tracks time. -/
def timeit {α : Type u} (s : string) (f : thunk α) : α :=
f ()

/- This function has a native implementation that displays the given string in the regular output stream. -/
def trace {α : Type u} (s : string) (f : thunk α) : α :=
f ()

/- This function has a native implementation that shows the VM call stack. -/
def trace_call_stack {α : Type u} (f : thunk α) : α :=
f ()

/- This function has a native implementation that displays in the given position all trace messages used in f.
   The arguments line and col are filled by the elaborator. -/
def scope_trace {α : Type u} {line col: nat} (f : thunk α) : α :=
f ()

meta constant undefined_core {α : Type u} (message : string) : α

meta def undefined {α : Type u} : α := undefined_core "undefined"
