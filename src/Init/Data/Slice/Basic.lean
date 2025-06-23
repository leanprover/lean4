module

prelude
import Init.Data.Range.Polymorphic

open Std.PRange

class Sliceable (shape : RangeShape) (α : Type u) where
  collection : α
  range: Std.PRange shape α
