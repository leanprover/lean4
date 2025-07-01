/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import all Init.Data.Array.Subarray
public import all Init.Data.Slice.Array.Basic
public import all Init.Data.Slice.Array.Iterator
public import all Init.Data.Slice.Operations
public import all Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Range.Polymorphic.Lemmas
public import Init.Data.Slice.Lemmas
public import Init.Data.Iterators.Lemmas

public section

open Std.Iterators Std.PRange

namespace Std.Slice.Array

theorem internalIter_eq {α : Type u} {s : Subarray α} :
    Internal.iter s = (PRange.Internal.iter (s.start...<s.stop)
      |>.attachWith (· < s.array.size)
        (fun out h => h
            |> PRange.Internal.isPlausibleIndirectOutput_iter_iff.mp
            |> PRange.lt_upper_of_mem
            |> (Nat.lt_of_lt_of_le · s.stop_le_array_size))
      |>.uLift
      |>.map fun | .up i => s.array[i.1]) := by
  simp [Internal.iter, ToIterator.iter_eq, Subarray.start, Subarray.stop, Subarray.array]

theorem toList_internalIter {α : Type u} {s : Subarray α} :
    (Internal.iter s).toList =
      ((s.start...s.stop).toList
        |>.attachWith (· < s.array.size)
          (fun out h => h
              |> PRange.mem_toList_iff_mem.mp
              |> PRange.lt_upper_of_mem
              |> (Nat.lt_of_lt_of_le · s.stop_le_array_size))
        |>.map fun i => s.array[i.1]) := by
  rw [internalIter_eq, Iter.toList_map, Iter.toList_uLift, Iter.toList_attachWith]
  simp [PRange.toList]

end Std.Slice.Array
