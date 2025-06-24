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
  State : Slice shape α → Type w
  iter (slice : Slice shape α) : Iter (α := State slice) γ

@[always_inline, inline, expose]
def SliceIter.of [Sliceable shape α β γ] (State : Slice shape α → Type u)
    (iter : (slice : Slice shape α) → Iter (α := State slice) γ) :
    SliceIter shape α where
  State := State
  iter := iter

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] {slice : Slice shape α} {State : Slice shape α → Type w} {iter}
    [Iterator (α := State slice) Id γ] :
    letI i : SliceIter shape α := .of State iter
    Iterator (α := i.State slice) Id γ :=
  inferInstanceAs <| Iterator (α := State slice) Id γ

instance {shape : RangeShape} {α : Type u} {β : Type v} {γ : Type w}
    [Sliceable shape α β γ] {slice : Slice shape α} {State : Slice shape α → Type w} {iter}
    [Iterator (α := State slice) Id γ] [Finite (α := State slice) Id] :
    letI i : SliceIter shape α := .of State iter
    Finite (α := i.State slice) Id :=
  inferInstanceAs <| Finite (α := State slice) Id
