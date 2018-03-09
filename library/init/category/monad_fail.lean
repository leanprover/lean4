/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.category.lift init.data.string.basic

universes u v

class monad_fail (m : Type u → Type v) :=
(fail {} : Π {a}, string → m a)

def match_failed {α : Type u} {m : Type u → Type v} [monad_fail m] : m α :=
monad_fail.fail "match failed"

instance monad_fail_lift (m n : Type u → Type v) [has_monad_lift m n] [monad_fail m] [monad n] : monad_fail n :=
{ fail := λ α s, monad_lift (monad_fail.fail s : m α) }
