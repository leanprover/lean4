/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian
-/

prelude
import Init.Data.Int
import Init.Data.String

inductive Ordering
| LT | EQ | GT

class Ord (α : Type u) where
  compare : α → α → Ordering

def cmp [inst : Ord α] := inst.compare

def compareOfLessAndEq {α} (x y : α) [HasLess α] [Decidable (x < y)] [DecidableEq α] :=
    if x < y then Ordering.LT
    else if x = y then Ordering.EQ
    else Ordering.GT

instance : Ord Nat where
  compare x y := compareOfLessAndEq x y

instance : Ord Int where
  compare x y := compareOfLessAndEq x y

instance : Ord Int where
  compare x y := compareOfLessAndEq x y

instance : Ord String where
  compare x y := compareOfLessAndEq x y
