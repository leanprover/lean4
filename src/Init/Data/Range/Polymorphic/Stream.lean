/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Stream

public section

open Std.Iterators

namespace Std.PRange

instance {sl su α} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α] :
    ToStream (PRange ⟨sl, su⟩ α) (Iter (α := RangeIterator su α) α) where
  toStream r := Internal.iter r

end Std.PRange
