module

prelude
import Init.Core
import Init.Data.Range.Polymorphic.Basic
import Init.Data.Range.Polymorphic.Nat
import all Init.Data.Range.Polymorphic.Basic
import Init.Data.Slice.Basic
import Init.Data.Iterators.Combinators.Attach
import Init.Data.Iterators.Combinators.FilterMap

open Std.Slice Std.PRange

instance {shape} {α : Type u} : Sliceable shape (Array α) Nat α where

instance : SliceIter ⟨.closed, .open⟩ (Array α) :=
  .of _ fun s =>
    Internal.iter s.range
      |>.attachWith (· < s.carrier.size) sorry
      |>.map fun i => s.carrier[i.1]
