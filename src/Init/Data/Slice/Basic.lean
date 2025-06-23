module

prelude
import Init.Data.Range.Polymorphic

open Std.PRange
open Std.Iterators

namespace Std.Slice

class Sliceable (shape : RangeShape) (α : Type u) (β : outParam (Type v))
    (γ : outParam (Type w)) where

structure _root_.Std.Slice (shape : RangeShape) (α : Type u) {β : Type v}
    {γ : Type w} [Sliceable shape α β γ] where
  carrier : α
  range : PRange shape β

class SliceIter (shape : RangeShape) (α : Type u) {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] where
  State : Type w
  iter (slice : Slice shape α) : Iter (α := State) γ

@[always_inline, inline, expose]
def SliceIter.of [Sliceable shape α β γ] (State : Type u)
    (iter : Slice shape α → Iter (α := State) γ) :
    SliceIter shape α where
  State := State
  iter := iter

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] {State : Type w} {iter} [Iterator (α := State) Id γ] :
    letI i : SliceIter shape α := .of State iter
    Iterator (α := i.State) Id γ :=
  inferInstanceAs <| Iterator (α := State) Id γ

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] {State : Type w} {iter} [Iterator (α := State) Id γ]
    [Finite (α := State) Id] :
    letI i : SliceIter shape α := .of State iter
    Finite (α := i.State) Id :=
  inferInstanceAs <| Finite (α := State) Id
