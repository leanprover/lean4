import Std.Tactic.BVDecide.LRAT.Parser

open Std.Tactic.BVDecide.LRAT

-- This is a nonsensical LRAT proof, merely used for testing.
def actions : Array IntAction := #[
  .del #[1, 2, 3, 4],
  .addRup 10000 #[111111111, -6] #[7, 8],
  .addRat 10001 #[234234, 13] (234234, true) #[5, 9] #[(500, #[120, 170, 42])],
  .addEmpty 10002 #[10000, 10001, 42]
]

/-- info: true -/
#guard_msgs in
#eval show IO _ from do
  match Parser.parseActions.run (lratProofToString actions).toUTF8 with
  | .ok parsed => return parsed == actions
  | .error e => throw <| IO.userError e

/-- info: true -/
#guard_msgs in
#eval show IO _ from do
  match Parser.parseActions.run (lratProofToBinary actions) with
  | .ok parsed => return parsed == actions
  | .error e => throw <| IO.userError e
