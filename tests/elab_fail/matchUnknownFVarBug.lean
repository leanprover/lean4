example (n? : Option Nat) : False := by
  match h:n?, h':n? with
  | some 0, _ => {}
