
-- Refines the free variable `n` and the result type of the `do` block:
example (x : Nat) (n : Fin (x + 1)) : Id (Fin (x + 1)) := do
  match (dependent := true) x with
  | 42 => pure 40
  | _ => pure n

-- Just refines the free variable `n`:
example (x : Nat) (n : Fin x) : Id Bool := do
  match (dependent := true) x with
  | 0 => n.elim0
  | _ => pure true

/--
error: Dependent match is not supported when the result type of the `do` block ⏎
  Bool
 is different to the result type of the `match` ⏎
  Fin (x + 1)
-/
#guard_msgs (error) in
example (x : Nat) (n : Fin (x + 1)) : Id Bool := do
  let y : Fin (x + 1) ←
    match (dependent := true) x with
    | 42 => pure 40
    | _ => pure 0
  return y % 2 == 0

/--
error: Dependent match is not supported when the result type of the `do` block ⏎
  Bool
 is different to the result type of the `match` ⏎
  ?m.7
-/
#guard_msgs (error) in
example (x : Nat) (n : Fin (x + 1)) : Id Bool := do
  let y ←
    match (dependent := true) x with
    | 42 => pure 40
    | _ => pure 0
  return y % 2 == 0

-- A bare `return` in a dependent branch targets the refined branch type.
example (n : Nat) : Id (Fin (n + 1)) := do
  match (dependent := true) n with
  | 0 => return 0
  | _k + 1 => return 1

-- The same holds through a nested `do`.
example (n : Nat) : Id (Fin (n + 1)) := do
  match (dependent := true) n with
  | 0 => do return 0
  | _k + 1 => do return 1

-- And through a parenthesized `do` block.
example (n : Nat) : Id (Fin (n + 1)) := do
  match (dependent := true) n with
  | 0 => (do return 0)
  | _k + 1 => (do return 1)

-- The refinement holds under further control flow inside the branch.
example (n : Nat) : Id (Fin (n + 1)) := do
  match (dependent := true) n with
  | 0 => if true then return 0 else return 0
  | _k + 1 => return 1
