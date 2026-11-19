module

/-!
The termination error should be reported at the second recursive call, not the first.
The two calls `f heapsize (lCh i)` are structurally identical syntax; without recording
the source position in the `_recApp` mdata, hashconsing/simplification merged them and
the error was attributed to the wrong call.
-/

def lCh := (· * 2 + 1)

/--
@ +7:6...24
error: failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
heapsize i : Nat
h✝¹ : i < heapsize
h✝ : ¬i = 0
⊢ heapsize - lCh i < heapsize - i
-/
#guard_msgs (positions := true) in
def f (heapsize i : Nat) : Nat :=
  if i < heapsize then
    if i = 0 then
      have : i < lCh i := by simp [lCh]; omega
      f heapsize (lCh i)
    else
      f heapsize (lCh i)
  else 0
termination_by heapsize - i
