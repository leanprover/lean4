module

def a (_ : Unit) : Nat :=
  match some 0 with
  | some _ => 2
  | _ => 2
