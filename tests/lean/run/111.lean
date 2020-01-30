import Init.Lean
new_frontend
open Lean
#check mkNullNode  -- Lean.Syntax
#check mkNullNode #[]  -- Lean.Syntax
#check @mkNullNode
#check
 let f : Array Syntax → Syntax := @mkNullNode;
 f #[]

#check let f := @mkNullNode; f #[]
