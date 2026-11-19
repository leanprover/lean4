example (a : α) (f : α → Option α) : Bool := by
  match h:f a with
  | some _ => exact true
