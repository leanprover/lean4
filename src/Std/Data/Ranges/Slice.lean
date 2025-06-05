prelude
import Std.Data.Ranges.Basic

open Std.Iterators

class Sliceable (shape : RangeShape) (ρ : Type v) (α : Type u) (β : outParam (Type w)) where

structure Slice (shape : RangeShape) (ρ : Type v) (α : Type u) where
  collection : ρ
  range : PRange shape α

def makeSlice [Sliceable shape ρ α β] (x : ρ) (r : PRange shape α) : Slice shape ρ α :=
  ⟨x, r⟩

syntax:max term noWs "[[" term "]]" : term

macro_rules
  | `($x[[$r]]) => `(makeSlice $x $r)

class SliceIter (shape : RangeShape) (ρ α) {β} [Sliceable shape ρ α β] where
  State : Type u
  iter : Slice shape ρ α → Iter (α := State) β

@[always_inline, inline]
def SliceIter.of [Sliceable shape ρ α β] {State} (iter : Slice shape ρ α → Iter (α := State) β) : SliceIter shape ρ α where
  State := State
  iter := iter

@[always_inline, inline]
def Slice.iter [Sliceable shape ρ α β] [SliceIter shape ρ α] (s : Slice shape ρ α) :
    Iter (α := SliceIter.State shape ρ α β) β :=
  SliceIter.iter s

instance [Iterator State Id α] [Sliceable shape ρ α β]
    {iter : Slice shape ρ α → Iter (α := State) β} :
    letI : SliceIter shape ρ α := SliceIter.of iter
    Iterator (SliceIter.State shape ρ α β) Id α :=
  inferInstanceAs <| Iterator State Id α

instance [Iterator State Id α] [Sliceable shape ρ α β]
    [Finite State Id]
    {iter : Slice shape ρ α → Iter (α := State) β} :
    letI : SliceIter shape ρ α := SliceIter.of iter
    Finite (SliceIter.State shape ρ α β) Id :=
  inferInstanceAs <| Finite State Id

instance [Iterator State Id α] [Sliceable shape ρ α β]
    [IteratorCollect State Id m]
    {iter : Slice shape ρ α → Iter (α := State) β} :
    letI : SliceIter shape ρ α := SliceIter.of iter
    IteratorCollect (SliceIter.State shape ρ α β) Id m :=
  inferInstanceAs <| IteratorCollect State Id m
