example : ∀(x : Nat){h : x = x}, Nat := by
  intro x
  match x with
  | 0 => _
  | n + 1 => _

example (x : Nat) : ∀{h : x = x}, Nat := by
  match x with
  | 0 => _
  | n + 1 => _
