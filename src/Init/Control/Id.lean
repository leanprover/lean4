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

@[always_inline]
instance : Monad Id where
  pure x := x
  bind x f := f x
  map f x := f x

def hasBind : Bind Id :=
  inferInstance

@[always_inline, inline]
protected def run (x : Id α) : α := x

instance [OfNat α n] : OfNat (Id α) n :=
  inferInstanceAs (OfNat α n)

end Id
