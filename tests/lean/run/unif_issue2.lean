import Lean



open Lean

#check @StateT.run Nat Id Nat (let f := fun (x : Unit) => pure 0; f ()) 0

#check Id.run $ StateT.run (let x := fun _ => pure 0; x ()) 0

#check @StateT.run Nat Id (List Nat) (let x := fun _ => pure [0]; x ()) 0

#check @Unhygienic.run Syntax $ let x := fun _ => pure Syntax.missing; x ()
