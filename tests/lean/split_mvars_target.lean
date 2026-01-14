/-!
Tests that `split` works when there are metavariables in the target.
-/
theorem split_subgoals {x : Option Nat × Nat} :
  match x.fst with
  | some _ => True
  | none => True
  := by
  have h {P : Prop} {x'} : (x' = 4 ∧ P) → P := by simp
  apply h
  split
  rotate_right
  · exact 4
  · trivial
  · trivial
