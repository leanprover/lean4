/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.string.basic

universes u
/- debugging helper functions -/
@[extern cpp inline "lean::dbgTrace(#2, #3)"]
def dbgTrace {α : Type u} (s : string) (f : unit → α) : α :=
f ()

@[extern cpp inline "lean::dbgSleep(#2, #3)"]
def dbgSleep {α : Type u} (ms : uint32) (f : unit → α) : α :=
f ()
