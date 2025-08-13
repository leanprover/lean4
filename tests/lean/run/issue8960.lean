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
error: (kernel) application type mismatch
  data ≠ []
argument has type
  List Maze'
but function has type
  _nested.List_2 → Prop
-/
#guard_msgs in
structure Maze' where
  description : String
  passages : TestThingy Maze'
