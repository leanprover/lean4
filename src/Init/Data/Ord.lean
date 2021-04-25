/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian
-/

prelude
import Init.Data.Int
import Init.Data.String

inductive Ordering where
  | lt | eq | gt
deriving Inhabited, BEq


class Ord (α : Type u) where
  compare : α → α → Ordering

export Ord (compare)

def compareOfLessAndEq {α} (x y : α) [LT α] [Decidable (x < y)] [DecidableEq α] : Ordering :=
  if x < y then Ordering.lt
  else if x = y then Ordering.eq
  else Ordering.gt

instance : Ord Nat where
  compare x y := compareOfLessAndEq x y

instance : Ord Int where
  compare x y := compareOfLessAndEq x y

instance : Ord Bool where
  compare
  | false, true => Ordering.lt
  | true, false => Ordering.gt
  | _, _ => Ordering.eq

instance : Ord String where
  compare x y := compareOfLessAndEq x y

instance (n : Nat) : Ord (Fin n) where
  compare x y := compare x.val y.val

def USize.cmp (a b : USize) : Ordering := compare a.val b.val

instance : Ord USize where
  compare x y := compare x.val y.val

instance : Ord Char where 
  compare x y := compareOfLessAndEq x y