/-!
This file tests errors in the case of uninstantiated universe levels
-/

example : Nat :=
  let x := #[]
  let y := []
  4

example : Nat :=
  let x : Array.{_} _ := #[]
  let y : List.{_+1} _ := []
  4

example : Nat :=
  let x : Array _ := id { data := [] }
  4
