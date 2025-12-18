import Lean

open Lean

/-- info: Lean.mkNullNode (args : Array Syntax := #[]) : Syntax -/
#guard_msgs in
#check mkNullNode

/-- info: mkNullNode #[] : Syntax -/
#guard_msgs in
#check mkNullNode #[]

/-- info: @mkNullNode : optParam (Array Syntax) #[] → Syntax -/
#guard_msgs in
#check @mkNullNode

/--
info: let f := @mkNullNode;
f #[] : Syntax
-/
#guard_msgs in
#check
 let f : Array Syntax → Syntax := @mkNullNode;
 f #[]

/--
info: let f := @mkNullNode;
f #[] : Syntax
-/
#guard_msgs in
#check let f := @mkNullNode; f #[]
