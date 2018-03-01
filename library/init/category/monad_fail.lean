/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.category.transformers init.data.string.basic

universes u v

class monad_fail (m : Type u → Type v) extends monad m :=
(fail : Π {a}, string → m a)

-- deriving monad from monad_fail should happen only as a last resort
attribute [instance, priority 1] monad_fail.to_monad

def match_failed {α : Type u} {m : Type u → Type v} [monad_fail m] : m α :=
monad_fail.fail m "match failed"

-- TODO(Sebastian): Could take `has_monad_lift_t`, except that the refl instances will make it loop
instance monad_fail_lift (m n : Type u → Type v) [has_monad_lift m n] [monad_fail m] [monad_n : monad n] : monad_fail n :=
{ fail := λ α s, monad_lift (monad_fail.fail m s : m α), ..monad_n }
