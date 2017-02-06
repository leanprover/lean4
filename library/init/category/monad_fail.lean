/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.category.monad init.data.string.basic

universe variables u v

class monad_fail (m : Type u → Type v) extends monad m :=
(fail : Π {a}, string → m a)

def match_failed {α : Type u} {m : Type u → Type v} [monad_fail m] : m α :=
monad_fail.fail m "match failed"
