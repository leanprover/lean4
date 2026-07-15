theorem ex : True ∧ (match True with | _ => True) := by
  constructor; exact trivial
  split; trivial
