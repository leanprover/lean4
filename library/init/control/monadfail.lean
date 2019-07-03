/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.lift init.data.string.basic

universes u v

class MonadFail (m : Type u → Type v) :=
(fail {} : ∀ {a}, String → m a)

def matchFailed {α : Type u} {m : Type u → Type v} [MonadFail m] : m α :=
MonadFail.fail "match failed"

instance monadFailLift (m n : Type u → Type v) [HasMonadLift m n] [MonadFail m] [Monad n] : MonadFail n :=
{ fail := fun α s => monadLift (MonadFail.fail s : m α) }
