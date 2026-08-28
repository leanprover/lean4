/-!
Test that `for` loops with `mut` variables of sort-polymorphic type (e.g. `PProd`) work correctly.
`PProd Nat True : Sort (max 1 0)` has a `Prop` component, so `getDecLevel` must see the fully
instantiated and normalized level `1` rather than `max ?u ?v` with unresolved metavariables.
-/

def foo : Unit := Id.run do
  let mut x : PProd Nat True := ⟨0, trivial⟩
  for _ in [true] do
    x := ⟨0, trivial⟩
    break
