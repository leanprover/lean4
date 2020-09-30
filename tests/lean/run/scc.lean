import Lean.Util.SCC
new_frontend
open Lean.SCC

def checkSCC (expected : List (List Nat)) (vertices : List Nat) (successorsOf : Nat → List Nat) : IO Unit := do
let r := scc vertices successorsOf
IO.println r
«unless» (expected == r) $
  throw $ IO.userError ("expected result " ++ toString expected)

#eval checkSCC [[2], [1, 3], [4]] [1, 2, 3, 4] fun x => match x with
  | 1 => [2, 3]
  | 3 => [1]
  | 4 => [1, 2]
  | _ => []

#eval checkSCC [[1], [2], [3], [4]] [1, 2, 3, 4] fun x => match x with
  | _ => []

#eval checkSCC [[1, 2, 3, 4]] [1, 2, 3, 4] fun x => match x with
  | 1 => [2]
  | 2 => [3]
  | 3 => [4]
  | 4 => [1]
  | _ => []

#eval checkSCC [[1, 2, 4], [3]] [1, 2, 3, 4] fun x => match x with
  | 1 => [2]
  | 2 => [4]
  | 3 => [4]
  | 4 => [1]
  | _ => []
