def copy (curr : Nat) (input : Array Nat) (output : Array Nat) : Array Nat :=
  if hcurr:curr < input.size then
    copy (curr + 1) input (output.push (input[curr]'hcurr))
  else
    output
termination_by input.size - curr

/--
info: Try this:
  termination_by input.size - curr
-/
#guard_msgs(drop warning, info) in
theorem foo (curr : Nat) (input : Array Nat) (output : Array Nat)
    : ∀ (idx : Nat) (hidx1 : idx < curr),
        (copy curr input output)[idx]'sorry
          =
        output[idx]'sorry := by
  intro idx hidx
  unfold copy
  split
  . rw [foo]
    . rw [Array.getElem_push_lt]
    . omega
  . rfl
termination_by?
