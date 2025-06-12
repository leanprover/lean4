prelude
-- import Std.Data.Ranges.Basic

-- open Std.Iterators

-- class Sliceable (shape : RangeShape) (ρ : Type v) (α : Type u) (β : outParam (Type w)) where

-- structure Slice (shape : RangeShape) (ρ : Type v) (α : Type u) where
--   collection : ρ
--   range : PRange shape α

-- def makeSlice [Sliceable shape ρ α β] (x : ρ) (r : PRange shape α) : Slice shape ρ α :=
--   ⟨x, r⟩

-- syntax:max term noWs "[[" term "]]" : term

-- macro_rules
--   | `($x[[$r]]) => `(makeSlice $x $r)

-- class SliceIter (shape : RangeShape) (ρ α) {β} [Sliceable shape ρ α β] where
--   State : Slice shape ρ α → Type u
--   iter : (s : Slice shape ρ α) → Iter (α := State s) β

-- @[always_inline, inline]
-- def SliceIter.of [Sliceable shape ρ α β] {State : Slice shape ρ α → _}
--     (iter : (s : Slice shape ρ α) → Iter (α := State s) β) : SliceIter shape ρ α where
--   State := State
--   iter := iter

-- @[always_inline, inline]
-- def Slice.iter [Sliceable shape ρ α β] [SliceIter shape ρ α]
--     (s : Slice shape ρ α) :
--     Iter (α := SliceIter.State (shape := shape) (ρ := ρ) (α := α) (β := β) s) β :=
--   SliceIter.iter s

-- instance {State : Slice shape ρ α → _} [Iterator (State s) Id α] [Sliceable shape ρ α β]
--     {iter : (s : Slice shape ρ α) → Iter (α := State s) β} :
--     letI : SliceIter shape ρ α := SliceIter.of iter
--     Iterator (SliceIter.State (shape := shape) (ρ := ρ) (α := α) β s) Id α :=
--   inferInstanceAs <| Iterator (State s) Id α

-- instance {State : Slice shape ρ α → _} [Iterator (State s) Id α]
--     [Sliceable shape ρ α β]
--     [Finite (State s) Id]
--     {iter : (s : Slice shape ρ α) → Iter (α := State s) β} :
--     letI : SliceIter shape ρ α := SliceIter.of iter
--     Finite (SliceIter.State (shape := shape) (ρ := ρ) (α := α) β s) Id :=
--   inferInstanceAs <| Finite (State s) Id

-- instance {State : Slice shape ρ α → _} [Iterator (State s) Id α] [Sliceable shape ρ α β]
--     [IteratorCollect (State s) Id m]
--     {iter : (s : Slice shape ρ α) → Iter (α := State s) β} :
--     letI : SliceIter shape ρ α := SliceIter.of iter
--     IteratorCollect (SliceIter.State (shape := shape) (ρ := ρ) (α := α) β s) Id m :=
--   inferInstanceAs <| IteratorCollect (State s) Id m
