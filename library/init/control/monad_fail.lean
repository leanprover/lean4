/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.lift init.data.string.basic

universes u v

class monadFail (m : Type u → Type v) :=
(fail {} : Π {a}, string → m a)

def matchFailed {α : Type u} {m : Type u → Type v} [monadFail m] : m α :=
monadFail.fail "match failed"

instance monadFailLift (m n : Type u → Type v) [hasMonadLift m n] [monadFail m] [monad n] : monadFail n :=
{ fail := λ α s, monadLift (monadFail.fail s : m α) }
