module

prelude
import Init.Data.Range.Polymorphic

open Std.PRange
open Std.Iterators

namespace Std.Slice

class Sliceable (shape : RangeShape) (α : Type u) (β : outParam (Type v)) where

structure _root_.Std.Slice (shape : RangeShape) (α : Type u) {β : Type v}
    [Sliceable shape α β] where
  carrier : α
  range : PRange shape β

class SliceIter (shape : RangeShape) (α : Type u) {β : Type v}
    [Sliceable shape α β] where
  State : Type u
  iter (slice : Slice shape α) : Iter (α := State) α

@[always_inline, inline, expose]
def SliceIter.of [Sliceable shape α β] (State : Type u)
    (iter : Slice shape α → Iter (α := State) α) :
    SliceIter shape α where
  State := State
  iter := iter

instance {shape : RangeShape} {α : Type u} {β : Type v} [Sliceable shape α β]
    {State : Type u} {iter} [Iterator (α := State) Id α] :
    letI i : SliceIter shape α := .of State iter
    Iterator (α := i.State) Id α :=
  inferInstanceAs <| Iterator (α := State) Id α

instance {shape : RangeShape} {α : Type u} {β : Type v} [Sliceable shape α β]
    {State : Type u} {iter} [Iterator (α := State) Id α] [Finite (α := State) Id] :
    letI i : SliceIter shape α := .of State iter
    Finite (α := i.State) Id :=
  inferInstanceAs <| Finite (α := State) Id
