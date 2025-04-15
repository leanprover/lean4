/-!
# Make sure `injection` tactic can handle `0 = n + 1`
https://github.com/leanprover/lean4/issues/5064
-/

/-!
Motivating example from #5064.
This failed when generating the splitter theorem for `thingy`.
-/

def thingy : List (Nat ⊕ Nat) → List Bool
  | Sum.inr (_n + 2) :: l => thingy l
  | _ => []
  termination_by l => l.length

/-- info: ⊢ [] = [] -/
#guard_msgs in
theorem thingy_empty : thingy [] = [] := by
  unfold thingy
  trace_state
  rfl

/-!
Test using `injection` directly.
-/
example (n : Nat) (h : 0 = n + 1) : False := by
  with_reducible injection h
