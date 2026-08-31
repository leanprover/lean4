import Lean
open Lean

def encodeDecode [ToJson α] [FromJson α] (x : α) : Except String α := do
  let json := toJson x
  fromJson? json

/-- info: `5 -/
#guard_msgs in
#eval IO.ofExcept <| encodeDecode (Name.mkNum Name.anonymous 5)

/-- info: `bla.«foo.boo» -/
#guard_msgs in
#eval IO.ofExcept <| encodeDecode (Name.mkStr `bla "foo.boo")
