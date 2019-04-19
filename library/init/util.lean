/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.string.basic

universes u
/- debugging helper functions -/
@[extern cpp inline "lean::dbg_trace(#2, #3)"]
def dbgTrace {α : Type u} (s : String) (f : Unit → α) : α :=
f ()

/- Display the given message if `a` is shared, that is, RC(a) > 1 -/
@[extern cpp inline "lean::dbg_trace_if_shared(#2, #3)"]
def dbgTraceIfShared {α : Type u} (s : String) (a : α) : α :=
a

@[extern cpp inline "lean::dbg_sleep(#2, #3)"]
def dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α :=
f ()
