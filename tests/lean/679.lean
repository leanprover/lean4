import Lean
open Lean

def encodeDecode [ToJson α] [FromJson α] (x : α) : Except String α := do
  let json ← toJson x
  fromJson? json

#eval encodeDecode Name.anonymous
