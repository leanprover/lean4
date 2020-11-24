/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The identity Monad.
-/
prelude
import Init.Core

universe u

def Id (type : Type u) : Type u := type

namespace Id

instance : Monad Id := {
  pure := fun x => x
  bind := fun x f => f x
  map  := fun f x => f x
}

@[inline] protected def run (x : Id α) : α := x

instance [OfNat α] : OfNat (Id α) :=
  inferInstanceAs (OfNat α)

end Id
