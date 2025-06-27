/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Combinators.Monadic.ULift

namespace Std.Iterators

universe v u v' u'

variable {α : Type u} {β : Type u}

@[always_inline, inline]
def Iter.uLift (it : Iter (α := α) β) :
    Iter (α := Types.ULiftIterator.{v} α Id Id β (fun _ => monadLift)) (ULift β) :=
  (it.toIterM.uLift Id).toIter

end Std.Iterators
