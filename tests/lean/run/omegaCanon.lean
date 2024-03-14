def filter (p : α → Prop) [inst : DecidablePred p] (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' =>
    if p x then
      -- Trying to confuse `omega` by creating subterms that are structurally different
      -- but definitionally equal.
      x :: @filter α p (fun x => inst x) xs'
    else
      filter p xs'

def filter_length (p : α → Prop) [DecidablePred p] : (filter p xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    simp only [filter]
    split <;> simp only [List.length] <;> omega
