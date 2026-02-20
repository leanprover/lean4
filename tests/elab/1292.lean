def test : Nat :=
  let inp : Array (Option Nat × Nat) := #[(some 0, 0), (none, 0)]
  let fvars : Array Nat := inp.filterMap fun
    | (some _, _) => none
    | (none, fv)  => fv
  fvars.size

#eval test

def test2 : Nat :=
  let inp : Array (Option Nat × Nat) := #[(some 0, 0)]
  let fvars : Array Nat := inp.filterMap fun
    | (some _, _) => none
    | (none, fv)  => fv
  fvars.size

#eval test2
