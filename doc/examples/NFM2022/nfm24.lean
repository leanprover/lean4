/- induction tactic -/

example (as : List α) (a : α) : (as.concat a).length = as.length + 1 := by
  induction as with
  | nil => rfl
  | cons x xs ih => simp [List.concat, ih]

example (as : List α) (a : α) : (as.concat a).length = as.length + 1 := by
  induction as <;> simp! [*]
