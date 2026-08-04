import Lean

open Lean Elab Command

elab "#guard_list_lit " t:term : command => do
  let e ← liftTermElabM do
    Term.elabTerm t none
  let some (_, elems) := e.listLit?
    | throwError "not recognized as a list literal"
  unless elems.length == 33 do
    throwError "expected 33 elements, got {elems.length}"

#guard_list_lit [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
  11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
  21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
  31, 32
]
