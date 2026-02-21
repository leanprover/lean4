set_option backward.do.legacy false

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
