/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.ULift

public section

namespace Std
open Std.Iterators Std.Iterators.Types

universe v u v' u'

variable {α : Type u} {β : Type u}

/--
Transforms a step of the base iterator into a step of the `uLift` iterator.
-/
@[always_inline, inline]
def Iterators.Types.ULiftIterator.modifyStep (step : IterStep (Iter (α := α) β) β) :
    IterStep (Iter (α := ULiftIterator.{v} α Id Id β (fun _ => monadLift)) (ULift.{v} β))
      (ULift.{v} β) :=
  (ULiftIterator.Monadic.modifyStep (step.mapIterator Iter.toIterM)).mapIterator IterM.toIter

/--
Transforms an iterator with values in `β` into one with values in `ULift β`.

Most other combinators like `map` cannot switch between universe levels. This combinators
makes it possible to transition to a higher universe.

**Marble diagram:**

```
it            ---a    ----b    ---c    --d    ---⊥
it.uLift n    ---.up a----.up b---.up c--.up d---⊥
```

**Termination properties:**

* `Finite`: only if the original iterator is finite
* `Productive`: only if the original iterator is productive
-/
@[always_inline, inline, expose]
def Iter.uLift (it : Iter (α := α) β) :
    Iter (α := Types.ULiftIterator.{v} α Id Id β (fun _ => monadLift)) (ULift β) :=
  (it.toIterM.uLift Id).toIter

end Std
