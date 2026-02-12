/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/
module

prelude
public import Init.Data.List.Basic
public import Init.Control.Id

public section

namespace List

/-- Tail-recursive helper function for `scanlM` and `scanrM` -/
@[inline]
private def scanAuxM [Monad m] (f : β → α → m β) (init : β) (l : List α) : m (List β) :=
  go l init []
where
  /-- Auxiliary for `scanAuxM` -/
  @[specialize] go : List α → β → List β → m (List β)
    | [], last, acc => pure <| last :: acc
    | x :: xs, last, acc => do go xs (← f last x) (last :: acc)

/--
Folds a monadic function over a list from the left, accumulating partial results starting with
`init`. The accumulated values are combined with the each element of the list in order, using `f`.
-/
@[inline]
def scanlM [Monad m] (f : β → α → m β) (init : β) (l : List α) : m (List β) :=
  List.reverse <$> scanAuxM f init l

/--
Folds a monadic function over a list from the right, accumulating partial results starting with
`init`. The accumulated values are combined with the each element of the list in order, using `f`.
-/
@[inline]
def scanrM [Monad m] (f : α → β → m β) (init : β) (xs : List α) : m (List β) :=
  scanAuxM (flip f) init xs.reverse

/--
Fold a function `f` over the list from the left, returning the list of partial results.
```
scanl (+) 0 [1, 2, 3] = [0, 1, 3, 6]
```
-/
@[inline]
def scanl (f : β → α → β) (init : β) (as : List α) : List β :=
  Id.run <| as.scanlM (pure <| f · ·) init

/--
Fold a function `f` over the list from the right, returning the list of partial results.
```
scanr (+) 0 [1, 2, 3] = [6, 5, 3, 0]
```
-/
@[inline]
def scanr (f : α → β → β) (init : β) (as : List α) : List β :=
  Id.run <| as.scanrM (pure <| f · ·) init

end List
