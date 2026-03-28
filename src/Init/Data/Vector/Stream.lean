/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, François G. Dorais, Kim Morrison
-/
module

prelude
public import Init.Data.Stream
public import Init.Data.Vector.Basic
import Init.Data.Slice.Array.Basic

namespace Vector

/-! ### ToStream instance -/

@[no_expose]
public instance : Std.ToStream (Vector α n) (Subarray α) where
  toStream xs := xs.toArray[*...*]

end Vector
