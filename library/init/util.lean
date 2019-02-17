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
def dbg_trace {α : Type u} (s : string) (f : unit → α) : α :=
f ()

@[extern cpp inline "lean::dbg_sleep(#2, #3)"]
def dbg_sleep {α : Type u} (ms : uint32) (f : unit → α) : α :=
f ()
