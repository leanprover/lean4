import Std.Data.HashMap

open Std

/--
error: (kernel) application type mismatch
  DHashMap.Raw.WF inner
argument has type
  _nested.Std.DHashMap.Raw_3
but function has type
  (DHashMap.Raw String fun x => Maze) → Prop
-/
#guard_msgs in
structure Maze where
  description : String
  passages : HashMap String Maze

structure TestThingy (α : Type u) where
  data : List α
  invariant : data ≠ []

/--
error: In argument #2 of constructor Maze'.mk:
  Invalid occurrence of inductive type `Maze'`, parameter #1 of `TestThingy` is not positive.
  ⏎
  Note: That parameter is not positive:
    Non-positive occurrence of parameter `α` in type of TestThingy.mk
-/
#guard_msgs in
structure Maze' where
  description : String
  passages : TestThingy Maze'
