def f1 (x : Nat) (p : Nat × Nat) : IO Unit := do
  match x with
  | 0 => let (y, _) ← pure p
  | _ => pure ()


def f2 (x : Nat) (p : Nat × Nat) : IO Unit := do
  let mut y := 0
  match x with
  | 0 => (y, _) ← pure p
  | _ => pure ()
